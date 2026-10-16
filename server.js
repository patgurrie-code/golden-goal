'use strict';
// Golden Goal: online club football for you and the boys.
// One Node process serves the game page and runs every match on the server,
// so everyone sees the same ball. Empty spots are filled with bots.

const http = require('http');
const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;

// ===========================================================================
// Shared physics. This exact function also runs in the browser (served as
// /shared.js), so the game predicts your movement with the same maths.
// ===========================================================================
function SHARED() {
  const S = {};
  S.TICK = 30;
  S.DT = 1 / 30;
  S.G = 9.81;
  S.BR = 0.11;
  S.PR = 0.4;
  S.ND = 1.8; // net depth
  S.FIELDS = {
    5: { W: 36, L: 56, gw: 5, gh: 2.0, boxW: 18, boxD: 9, sixW: 9, sixD: 3, circle: 5, spot: 7.5 },
    7: { W: 46, L: 72, gw: 6, gh: 2.2, boxW: 26, boxD: 12, sixW: 12, sixD: 4, circle: 6.5, spot: 9 },
    11: { W: 66, L: 102, gw: 7.32, gh: 2.44, boxW: 40.3, boxD: 16.5, sixW: 18.3, sixD: 5.5, circle: 9.15, spot: 11 }
  };
  S.field = n => S.FIELDS[n] || S.FIELDS[11];
  S.clamp = (v, a, b) => (v < a ? a : v > b ? b : v);
  S.wrap = a => { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; };
  S.derive = a => ({
    jog: 5.3 + a.pac * 0.007,
    spr: 6.8 + a.pac * 0.025,
    acc: 18 + a.pac * 0.06,
    accB: 10 + a.dri * 0.07,
    drib: 0.86 + a.dri * 0.0012,
    turnB: 6 + a.dri * 0.065,
    drain: 11 - a.phy * 0.06,
    ctrl: 0.62 + a.dri * 0.003
  });
  S.ballOffset = sp => 0.52 + sp * 0.045;

  // Player states
  S.NORMAL = 0; S.SLIDE = 1; S.STUN = 2; S.DIVE = 3; S.CELEB = 4; S.LOCK = 5; S.HOLD = 6;

  // Moves one player for one tick. p: {x,y,vx,vy,face,sta,st}
  S.stepMove = function (p, mx, my, spr, aim, dt, F, hasBall, D) {
    if (p.st === 5) { p.vx = 0; p.vy = 0; if (aim !== null) p.face = aim; return; }
    let len = Math.hypot(mx, my);
    if (len > 1) { mx /= len; my /= len; len = 1; }
    const sprinting = spr && len > 0.3 && p.sta > 1;
    let max = sprinting ? D.spr * (p.sta < 30 ? 0.82 + p.sta * 0.006 : 1) : D.jog;
    if (hasBall) max *= D.drib;
    if (p.st === 6) max = Math.min(max, 3.5);
    const tvx = mx * max, tvy = my * max;
    let dvx = tvx - p.vx, dvy = tvy - p.vy;
    const dv = Math.hypot(dvx, dvy);
    let acc = hasBall ? D.accB : D.acc;
    if (len < 0.15) acc *= 1.5;
    const lim = acc * dt;
    if (dv > lim) { dvx *= lim / dv; dvy *= lim / dv; }
    p.vx += dvx; p.vy += dvy;
    p.x += p.vx * dt; p.y += p.vy * dt;
    const sp = Math.hypot(p.vx, p.vy);
    if (sprinting && sp > D.jog * 0.85) p.sta = Math.max(0, p.sta - D.drain * dt);
    else p.sta = Math.min(100, p.sta + (sp < 1.5 ? 9 : 4.5) * dt);
    let tgt = null;
    if (sp > 0.8) tgt = Math.atan2(p.vy, p.vx); else if (aim !== null) tgt = aim;
    if (tgt !== null) {
      const d = S.wrap(tgt - p.face), r = (hasBall ? D.turnB : 14) * dt;
      p.face = S.wrap(p.face + (d > r ? r : d < -r ? -r : d));
    }
    const bx = F.W / 2 + 3.5, by = F.L / 2 + 3.5;
    if (p.x < -bx) { p.x = -bx; if (p.vx < 0) p.vx = 0; } else if (p.x > bx) { p.x = bx; if (p.vx > 0) p.vx = 0; }
    if (p.y < -by) { p.y = -by; if (p.vy < 0) p.vy = 0; } else if (p.y > by) { p.y = by; if (p.vy > 0) p.vy = 0; }
  };

  // Moves the ball for one tick. b: {x,y,z,vx,vy,vz,sp,net}. Returns 1 if it hit the frame.
  S.stepBall = function (b, dt, F) {
    const n = 4, h = dt / n, hl = F.L / 2, gw = F.gw / 2, gh = F.gh, R = S.BR, PR = 0.06, ND = S.ND;
    let ev = 0;
    for (let i = 0; i < n; i++) {
      const px = b.x, py = b.y, pz = b.z;
      if (b.z > 0.002 || b.vz > 0.01) {
        b.vz -= S.G * h;
        const sp = Math.hypot(b.vx, b.vy, b.vz), k = 0.0125 * sp * h;
        b.vx -= b.vx * k; b.vy -= b.vy * k; b.vz -= b.vz * k;
        if (b.sp) { const c = b.sp * h, vx = b.vx; b.vx -= b.vy * c; b.vy += vx * c; b.sp *= Math.exp(-0.6 * h); }
        b.x += b.vx * h; b.y += b.vy * h; b.z += b.vz * h;
        if (b.z < 0) {
          b.z = 0;
          if (b.vz < -1.6) { b.vz = -b.vz * 0.5; b.vx *= 0.86; b.vy *= 0.86; b.sp *= 0.4; } else b.vz = 0;
        }
      } else {
        b.z = 0; b.vz = 0;
        const sp = Math.hypot(b.vx, b.vy);
        if (sp > 0) {
          const ns = Math.max(0, sp - (2.4 + 0.05 * sp) * h);
          b.vx *= ns / sp; b.vy *= ns / sp;
          if (b.sp) { const c = b.sp * h * 0.4, vx = b.vx; b.vx -= b.vy * c; b.vy += vx * c; }
        }
        b.sp *= Math.exp(-3 * h);
        b.x += b.vx * h; b.y += b.vy * h;
      }
      // Posts and crossbars at both ends
      for (let e = -1; e <= 1; e += 2) {
        const ly = e * hl;
        if (Math.abs(b.y - ly) > 1) continue;
        for (let s = -1; s <= 1; s += 2) {
          const dx = b.x - s * gw, dy = b.y - ly, d = Math.hypot(dx, dy);
          if (d < R + PR && b.z < gh + R && d > 1e-6) {
            const nx = dx / d, ny = dy / d, vn = b.vx * nx + b.vy * ny;
            if (vn < 0) { b.vx -= 1.6 * vn * nx; b.vy -= 1.6 * vn * ny; ev = 1; }
            b.x = s * gw + nx * (R + PR); b.y = ly + ny * (R + PR);
          }
        }
        if (Math.abs(b.x) < gw) {
          const dy = b.y - ly, dz = b.z - gh, d = Math.hypot(dy, dz);
          if (d < R + PR && d > 1e-6) {
            const ny = dy / d, nz = dz / d, vn = b.vy * ny + b.vz * nz;
            if (vn < 0) { b.vy -= 1.6 * vn * ny; b.vz -= 1.6 * vn * nz; ev = 1; }
            b.y = ly + ny * (R + PR); b.z = gh + nz * (R + PR);
          }
        }
      }
      // Goals and nets
      if (!b.net) {
        const ay = Math.abs(b.y), apy = Math.abs(py);
        if (ay > hl + R && apy <= hl + R) {
          const t = (hl + R - apy) / Math.max(1e-6, ay - apy);
          const cx = px + (b.x - px) * t, cz = pz + (b.z - pz) * t;
          if (Math.abs(cx) < gw - R * 0.5 && cz < gh - R * 0.3) b.net = b.y > 0 ? 2 : 1;
        }
        if (!b.net && ay > hl && ay < hl + ND + R && Math.abs(b.x) < gw + R && b.z < gh + R) {
          if (Math.abs(px) >= gw + R) { b.x = px; b.vx *= -0.25; }
          else if (pz >= gh + R) { b.z = pz; b.vz = Math.abs(b.vz) * 0.25; }
          else if (apy >= hl + ND + R) { b.y = py; b.vy *= -0.25; }
        }
      }
      if (b.net) {
        const e = b.net === 2 ? 1 : -1;
        if (e * b.y > hl + ND - R) { b.y = e * (hl + ND - R); b.vy *= -0.15; b.vx *= 0.6; b.vz *= 0.6; }
        if (e * b.y < hl + R) { b.y = e * (hl + R); b.vy = e * Math.abs(b.vy) * 0.2; }
        if (Math.abs(b.x) > gw - R) { b.x = Math.sign(b.x) * (gw - R); b.vx *= -0.2; }
        if (b.z > gh - R) { b.z = gh - R; b.vz = -Math.abs(b.vz) * 0.2; }
      }
    }
    return ev;
  };

  // Ground pass: launch speed that arrives at distance d with speed vf.
  const RA = 2.4, RB = 0.05;
  const rollF = s => s / RB - (RA / (RB * RB)) * Math.log(RA + RB * s);
  S.passSpeed = (d, vf) => {
    let lo = vf, hi = 45;
    const want = d + rollF(vf);
    for (let i = 0; i < 30; i++) { const m = (lo + hi) / 2; if (rollF(m) < want) lo = m; else hi = m; }
    return (lo + hi) / 2;
  };
  // Lofted ball: horizontal and vertical launch speed to land at distance d after about T seconds.
  S.flightDist = (vh, vz, z0) => {
    let x = 0, z = z0, vx = vh, v2 = vz;
    const h = 1 / 120;
    for (let i = 0; i < 1200; i++) {
      v2 -= S.G * h;
      const sp = Math.hypot(vx, v2), k = 0.0125 * sp * h;
      vx -= vx * k; v2 -= v2 * k; x += vx * h; z += v2 * h;
      if (z <= 0 && v2 < 0) return x;
    }
    return x;
  };
  S.loft = (d, T, z0) => {
    const vz = S.G * T * 0.5 * 1.04;
    let lo = 0.2, hi = 60;
    for (let i = 0; i < 22; i++) { const m = (lo + hi) / 2; if (S.flightDist(m, vz, z0 || 0) < d) lo = m; else hi = m; }
    return { vh: (lo + hi) / 2, vz };
  };
  // Shot: vertical speed so the ball reaches height h after travelling d at speed v.
  S.shotVz = (d, v, h, z0) => {
    const k = 0.0125;
    const t = (Math.exp(k * d) - 1) / (k * Math.max(5, v));
    return (h - (z0 || 0) + 0.5 * S.G * t * t) / t;
  };
  // Picks the teammate a pass is aimed at. mates: [{i,x,y,vx,vy}]
  S.pickReceiver = (from, aimA, aimX, aimY, mates, wide) => {
    let best = null, bs = 1e9;
    const cone = wide ? 0.95 : 0.8;
    for (const m of mates) {
      const dx = m.x - from.x, dy = m.y - from.y, d = Math.hypot(dx, dy);
      if (d < 2 || d > 60) continue;
      const ang = Math.abs(S.wrap(Math.atan2(dy, dx) - aimA));
      const near = Math.hypot(m.x - aimX, m.y - aimY);
      if (ang > cone && near > 5) continue;
      const sc = ang * 22 + d * 0.35 + (near < 5 ? -12 + near * 1.5 : 0);
      if (sc < bs) { bs = sc; best = m; }
    }
    return best;
  };
  return S;
}

const S = SHARED();
const SHARED_JS = 'window.SH=(' + SHARED.toString() + ')();';

// ===========================================================================
// Game data
// ===========================================================================
const ROLE_CAT = { GK: 'GK', CB: 'DEF', LB: 'DEF', RB: 'DEF', CDM: 'MID', CM: 'MID', CAM: 'MID', LM: 'MID', RM: 'MID', LW: 'ATT', RW: 'ATT', ST: 'ATT' };
const ROLES = Object.keys(ROLE_CAT);
// Formations: [role, x across (-1 left .. 1 right), y along (-1 own goal .. 1 their goal)]
const FORMS = {
  11: [['GK', 0, -0.94], ['LB', -0.68, -0.6], ['CB', -0.24, -0.68], ['CB', 0.24, -0.68], ['RB', 0.68, -0.6],
    ['CDM', 0, -0.44], ['CM', -0.36, -0.26], ['CM', 0.36, -0.26], ['LW', -0.66, 0], ['ST', 0, 0.06], ['RW', 0.66, 0]],
  7: [['GK', 0, -0.93], ['CB', -0.34, -0.62], ['CB', 0.34, -0.62], ['LM', -0.62, -0.2], ['CM', 0, -0.32], ['RM', 0.62, -0.2], ['ST', 0, 0.04]],
  5: [['GK', 0, -0.92], ['CB', 0, -0.58], ['LM', -0.55, -0.22], ['RM', 0.55, -0.22], ['ST', 0, 0.02]]
};
const PROFILES = {
  GK: { pac: -16, sho: -34, pas: -6, dri: -16, def: -20, phy: 2, gk: 6 },
  CB: { pac: -6, sho: -26, pas: -4, dri: -12, def: 8, phy: 8 },
  LB: { pac: 5, sho: -16, pas: 0, dri: -2, def: 2, phy: 0 },
  RB: { pac: 5, sho: -16, pas: 0, dri: -2, def: 2, phy: 0 },
  CDM: { pac: -4, sho: -8, pas: 4, dri: -2, def: 6, phy: 6 },
  CM: { pac: 0, sho: -2, pas: 6, dri: 4, def: -2, phy: 2 },
  CAM: { pac: 2, sho: 4, pas: 8, dri: 8, def: -16, phy: -4 },
  LM: { pac: 6, sho: -2, pas: 4, dri: 6, def: -8, phy: -2 },
  RM: { pac: 6, sho: -2, pas: 4, dri: 6, def: -8, phy: -2 },
  LW: { pac: 8, sho: 4, pas: 2, dri: 8, def: -22, phy: -4 },
  RW: { pac: 8, sho: 4, pas: 2, dri: 8, def: -22, phy: -4 },
  ST: { pac: 4, sho: 10, pas: -4, dri: 4, def: -26, phy: 6 }
};
const DIFF = [
  { name: 'Amateur', base: 57, react: 0.5, tackle: 0.05, err: 1.6, noise: 0.5, keep: 0.82 },
  { name: 'Semi-pro', base: 65, react: 0.36, tackle: 0.08, err: 1.25, noise: 0.35, keep: 0.9 },
  { name: 'Pro', base: 73, react: 0.25, tackle: 0.11, err: 1.0, noise: 0.25, keep: 0.97 },
  { name: 'World class', base: 82, react: 0.16, tackle: 0.15, err: 0.8, noise: 0.15, keep: 1.03 }
];
const SURNAMES = ['Silva', 'Okafor', 'Rossi', 'Mueller', 'Kovac', 'Haddad', 'Nakamura', 'Mensah', 'Fernandes', 'Novak', 'Kelly', 'Moreno', 'Petrov', 'Diallo', 'Jensen', 'Costa', 'Ward', 'Ito', 'Santos', 'Murphy',
  'Bakker', 'Adeyemi', 'Lund', 'Garcia', 'Reyes', 'Walsh', 'Ahmadi', 'Park', 'Dubois', 'Romero', 'Nilsen', 'Barros', 'Osei', 'Brennan', 'Vidal', 'Kim', 'Laurent', 'Hughes', 'Sato', 'Popescu',
  'Ferreira', 'Mitchell', 'Varga', 'Torres', 'Boateng', 'Lindqvist', 'Castro', 'Quinn', 'Yilmaz', 'Duarte', 'Nwosu', 'Holm', 'Ortega', 'Byrne', 'Rahman', 'Vos', 'Mendes', 'Tanaka', 'Fischer', 'Ruiz'];
const BOT_CLUBS = [
  { name: 'Harbour City', abbr: 'HAR', c1: '#1d4fb8', c2: '#f4f4f0', pattern: 'plain', crest: { shape: 'shield', icon: 'star' } },
  { name: 'Northside United', abbr: 'NOR', c1: '#c8202f', c2: '#141414', pattern: 'stripes', crest: { shape: 'round', icon: 'bolt' } },
  { name: 'Westgate Athletic', abbr: 'WES', c1: '#1f7a43', c2: '#f4f4f0', pattern: 'hoops', crest: { shape: 'shield', icon: 'crown' } },
  { name: 'Bayside Rovers', abbr: 'BAY', c1: '#7cc3ee', c2: '#14254a', pattern: 'plain', crest: { shape: 'round', icon: 'wave' } },
  { name: 'Kingsway Wanderers', abbr: 'KIN', c1: '#f2b705', c2: '#151515', pattern: 'plain', crest: { shape: 'diamond', icon: 'crown' } },
  { name: 'Old Boys AFC', abbr: 'OLD', c1: '#7a1f3d', c2: '#8fd0f0', pattern: 'halves', crest: { shape: 'shield', icon: 'ball' } },
  { name: 'Riverside Town', abbr: 'RIV', c1: '#f26a1b', c2: '#151515', pattern: 'plain', crest: { shape: 'round', icon: 'flame' } },
  { name: 'Southbank Albion', abbr: 'SOU', c1: '#13235b', c2: '#f5d33b', pattern: 'sash', crest: { shape: 'shield', icon: 'moon' } },
  { name: 'Eastfield Rangers', abbr: 'EAS', c1: '#f4f4f0', c2: '#c8202f', pattern: 'sash', crest: { shape: 'diamond', icon: 'star' } },
  { name: 'Highgate Celtic', abbr: 'HIG', c1: '#138a4a', c2: '#f4f4f0', pattern: 'hoops', crest: { shape: 'round', icon: 'chevron' } },
  { name: 'Dockside FC', abbr: 'DOC', c1: '#141414', c2: '#f4f4f0', pattern: 'stripes', crest: { shape: 'shield', icon: 'bolt' } },
  { name: 'Ironbark FC', abbr: 'IRO', c1: '#5b6470', c2: '#e23d3d', pattern: 'plain', crest: { shape: 'diamond', icon: 'chevron' } }
];
const SHAPES = ['shield', 'round', 'diamond'];
const ICONS = ['star', 'bolt', 'crown', 'ball', 'wave', 'flame', 'moon', 'chevron'];
const PATTERNS = ['plain', 'stripes', 'hoops', 'halves', 'sash'];
const SKINS = 6, HAIRS = ['bald', 'buzz', 'short', 'afro', 'long', 'mohawk', 'bun'];

const rnd = (a, b) => a + Math.random() * (b - a);
const pick = a => a[Math.floor(Math.random() * a.length)];
const gauss = () => { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };
const hyp = Math.hypot;
const clamp = S.clamp;
const segDist = (px, py, ax, ay, bx, by) => {
  const dx = bx - ax, dy = by - ay, l2 = dx * dx + dy * dy;
  let t = l2 ? ((px - ax) * dx + (py - ay) * dy) / l2 : 0;
  t = t < 0 ? 0 : t > 1 ? 1 : t;
  return { d: hyp(px - (ax + dx * t), py - (ay + dy * t)), t };
};
const r2 = v => Math.round(v * 100) / 100;
const r1 = v => Math.round(v * 10) / 10;

// ---------------------------------------------------------------------------
// Sanitising what browsers send
// ---------------------------------------------------------------------------
const cleanText = (s, max) => String(s == null ? '' : s).replace(/[\u0000-\u001f<>"`]/g, '').replace(/\s+/g, ' ').trim().slice(0, max);
const cleanColor = (c, d) => (typeof c === 'string' && /^#[0-9a-f]{6}$/i.test(c) ? c.toLowerCase() : d);
const num = (v, a, b, d) => { v = Number(v); return Number.isFinite(v) ? clamp(v, a, b) : d; };
function cleanClub(c) {
  if (!c || typeof c !== 'object') return null;
  const id = cleanText(c.id, 12).replace(/[^a-z0-9]/gi, '');
  if (id.length < 4) return null;
  const name = cleanText(c.name, 24) || 'My Club';
  const abbr = (cleanText(c.abbr, 3).toUpperCase().replace(/[^A-Z0-9]/g, '') || name.slice(0, 3).toUpperCase()).padEnd(3, 'X');
  const cr = c.crest || {};
  return {
    id, name, abbr,
    c1: cleanColor(c.c1, '#1d4fb8'), c2: cleanColor(c.c2, '#f4f4f0'),
    pattern: PATTERNS.includes(c.pattern) ? c.pattern : 'plain',
    crest: { shape: SHAPES.includes(cr.shape) ? cr.shape : 'shield', icon: ICONS.includes(cr.icon) ? cr.icon : 'star' },
    ver: num(c.ver, 0, 1e13, 0)
  };
}
function cleanProfile(p) {
  p = p && typeof p === 'object' ? p : {};
  const a = p.attrs || {};
  const at = k => Math.round(num(a[k], 25, 99, 60));
  const look = p.look || {};
  return {
    name: cleanText(p.name, 16) || 'Player',
    num: Math.round(num(p.num, 1, 99, 10)),
    pos: ROLES.includes(p.pos) ? p.pos : 'ST',
    attrs: { pac: at('pac'), sho: at('sho'), pas: at('pas'), dri: at('dri'), def: at('def'), phy: at('phy'), gk: at('gk') },
    look: {
      skin: Math.round(num(look.skin, 0, SKINS - 1, 2)),
      hair: HAIRS.includes(look.hair) ? look.hair : 'short',
      hairC: cleanColor(look.hairC, '#2a1c14'),
      boots: cleanColor(look.boots, '#f2f2f2'),
      h: num(look.h, 1.65, 1.98, 1.8),
      sleeves: look.sleeves === 'long' ? 'long' : 'short'
    },
    celeb: ['slide', 'plane', 'leap', 'calm'].includes(p.celeb) ? p.celeb : 'slide',
    club: cleanClub(p.club),
    level: Math.round(num(p.level, 1, 99, 1))
  };
}

// ---------------------------------------------------------------------------
// Kits
// ---------------------------------------------------------------------------
const rgb = h => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];
const cdist = (a, b) => { const x = rgb(a), y = rgb(b); const rm = (x[0] + y[0]) / 2; return Math.sqrt((2 + rm / 256) * (x[0] - y[0]) ** 2 + 4 * (x[1] - y[1]) ** 2 + (2 + (255 - rm) / 256) * (x[2] - y[2]) ** 2); };
const lum = h => { const c = rgb(h); return (0.299 * c[0] + 0.587 * c[1] + 0.114 * c[2]) / 255; };
function kitFrom(id, flip) {
  const shirt = flip ? id.c2 : id.c1, trim = flip ? id.c1 : id.c2;
  return { shirt, trim, pattern: flip ? 'plain' : id.pattern, shorts: lum(shirt) > 0.72 ? '#1b1f27' : (id.pattern === 'plain' || flip ? trim : '#f2f2ee'), socks: shirt };
}
function makeKits(home, away) {
  const h = kitFrom(home, false);
  let a = kitFrom(away, false);
  if (cdist(a.shirt, h.shirt) < 160) a = kitFrom(away, true);
  if (cdist(a.shirt, h.shirt) < 160) a = { shirt: lum(h.shirt) > 0.6 ? '#20242c' : '#f4f4f0', trim: lum(h.shirt) > 0.6 ? '#f4f4f0' : '#20242c', pattern: 'plain', shorts: lum(h.shirt) > 0.6 ? '#20242c' : '#f4f4f0', socks: lum(h.shirt) > 0.6 ? '#20242c' : '#f4f4f0' };
  const gkOpts = ['#c6f432', '#ff8a1f', '#9b5cff', '#ff4fa3', '#21d4c4'];
  const gks = [];
  for (const k of [h, a]) {
    let g = gkOpts.find(c => cdist(c, h.shirt) > 180 && cdist(c, a.shirt) > 180 && !gks.includes(c)) || '#ff8a1f';
    gks.push(g);
  }
  return [h, a].map((k, i) => ({ ...k, gk: { shirt: gks[i], trim: '#1b1f27', pattern: 'plain', shorts: '#1b1f27', socks: gks[i] } }));
}

// ===========================================================================
// Rooms
// ===========================================================================
const rooms = new Map();
const clients = new Map();
let nextClientId = 1;
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
function makeCode() {
  for (;;) {
    let c = '';
    for (let i = 0; i < 5; i++) c += CODE_CHARS[Math.floor(Math.random() * CODE_CHARS.length)];
    if (!rooms.has(c)) return c;
  }
}
const PH = { warmup: 0, play: 1, set: 2, goal: 3, half: 4, full: 5 };

class Room {
  constructor(o, hostClient) {
    this.code = makeCode();
    this.name = cleanText(o.name, 28) || ((hostClient && hostClient.profile ? hostClient.profile.name : 'Player') + "'s match");
    this.pub = o.pub !== false;
    this.size = [5, 7, 11].includes(Number(o.size)) ? Number(o.size) : 11;
    this.len = [3, 4, 6, 8, 10, 12].includes(Number(o.len)) ? Number(o.len) : 6;
    this.diff = Math.round(num(o.diff, 0, 3, 2));
    this.bots = o.bots !== false;
    this.golden = o.golden !== false;
    this.warmLen = [0, 15, 30, 60, 90].includes(Number(o.warm)) ? Number(o.warm) : 30;
    this.quick = !!o.quick;
    this.F = S.field(this.size);
    this.created = Date.now();
    this.members = new Map(); // client id -> client
    this.hostId = hostClient ? hostClient.id : 0;
    this.tick = 0; this.time = 0;
    this.phase = 'warmup'; this.phaseT = this.warmLen > 0 ? this.warmLen : 3; this.firstMatch = true;
    this.clock = 0; this.half = 1; this.score = [0, 0]; this.extra = false;
    this.ball = { x: 0, y: 0, z: 0, vx: 0, vy: 0, vz: 0, sp: 0, net: 0 };
    this.owner = -1;
    this.set = null;
    this.evq = [];
    this.touches = [];
    this.pendingPass = null; this.pendingShot = null;
    this.kickoffTeam = 0;
    this.rosterVer = 0;
    this.emptySince = Date.now();
    this.idents = [null, null];
    this.matchNo = 0;
    this.buildTeams();
    this.pickIdents();
    this.resetStats();
    this.placeFormation(false);
  }

  // ---- roster -------------------------------------------------------------
  buildTeams() {
    const form = FORMS[this.size];
    this.players = [];
    for (let t = 0; t < 2; t++) {
      form.forEach((f, s) => {
        const p = {
          i: this.players.length, team: t, slot: s, role: f[0], ax: f[1], ay: f[2],
          x: 0, y: 0, vx: 0, vy: 0, face: 0, sta: 100, st: 0, stT: 0,
          cid: 0, afk: false, active: this.bots, name: '', num: 0, attrs: null, D: null, look: null, celeb: 'slide',
          inp: { mx: 0, my: 0, spr: 0, ax: 0, ay: 0 }, q: [], acts: [], ack: 0,
          kcd: 0, tcd: 0, buf: null, call: -10, slideHit: false, holdT: 0, diveZ: 0,
          ai: { next: 0, tx: 0, ty: 0, spr: false, dir: null, mode: '', act: null, actAt: 0, held: 0, runT: 0 },
          stats: null
        };
        this.makeBot(p);
        this.players.push(p);
      });
    }
  }
  makeBot(p) {
    const d = DIFF[this.diff], prof = PROFILES[p.role];
    const a = {};
    for (const k of ['pac', 'sho', 'pas', 'dri', 'def', 'phy']) a[k] = Math.round(clamp(d.base + (prof[k] || 0) + rnd(-4, 4), 30, 96));
    a.gk = p.role === 'GK' ? Math.round(clamp(d.base + 6 + rnd(-3, 3), 40, 96)) : 20;
    p.attrs = a; p.D = S.derive(a);
    p.cid = 0; p.afk = false;
    p.name = String.fromCharCode(65 + Math.floor(Math.random() * 26)) + '. ' + pick(SURNAMES);
    p.num = p.role === 'GK' ? 1 : [2, 3, 4, 5, 6, 8, 7, 10, 11, 9, 14, 15, 17][p.slot] || (p.slot + 2);
    p.look = { skin: Math.floor(Math.random() * SKINS), hair: pick(HAIRS), hairC: pick(['#1a120c', '#2a1c14', '#4a3020', '#7a5230', '#c9a25a', '#141414']), boots: pick(['#f2f2f2', '#141414', '#e8333a', '#2f6bff', '#f5d33b', '#21d4c4', '#ff8a1f']), h: rnd(1.7, 1.92), sleeves: Math.random() < 0.2 ? 'long' : 'short' };
    p.celeb = pick(['slide', 'plane', 'leap', 'calm']);
    p.active = this.bots;
  }
  pickIdents() {
    // Each side takes the club of its first human; otherwise it's a bot club.
    const used = new Set();
    for (let t = 0; t < 2; t++) {
      let club = null;
      const humans = this.players.filter(p => p.team === t && p.cid).map(p => this.members.get(p.cid)).filter(Boolean).sort((a, b) => a.joinedAt - b.joinedAt);
      for (const c of humans) if (c.profile.club) { club = c.profile.club; break; }
      if (club && used.has(club.id)) {
        club = { ...club, id: club.id + 'r', name: club.name.slice(0, 15) + ' Reserves', bot: false, reserves: true };
      }
      if (!club) {
        const keep = this.idents[t] && this.idents[t].bot ? this.idents[t] : null;
        if (keep && !used.has(keep.id)) club = keep;
        else {
          const opts = BOT_CLUBS.filter(b => !used.has('bot' + b.abbr) && !(this.idents[1 - t] && this.idents[1 - t].abbr === b.abbr));
          const b = pick(opts.length ? opts : BOT_CLUBS);
          club = { ...b, id: 'bot' + b.abbr, bot: true };
        }
      }
      used.add(club.id);
      this.idents[t] = club;
    }
    this.kits = makeKits(this.idents[0], this.idents[1]);
  }
  humansOn(t) { return this.players.filter(p => p.team === t && p.cid).length; }
  bestSlot(team, pos) {
    const free = this.players.filter(p => p.team === team && !p.cid);
    if (!free.length) return null;
    const cat = ROLE_CAT[pos];
    let best = free.find(p => p.role === pos) || free.find(p => ROLE_CAT[p.role] === cat && p.role !== 'GK');
    if (!best && cat === 'GK') best = free.find(p => p.role === 'GK');
    if (!best) {
      const order = { GK: 0, DEF: 1, MID: 2, ATT: 3 };
      const want = order[cat];
      best = free.filter(p => p.role !== 'GK').sort((a, b) => Math.abs(order[ROLE_CAT[a.role]] - want) - Math.abs(order[ROLE_CAT[b.role]] - want))[0] || free[0];
    }
    return best;
  }
  addClient(c) {
    if (this.members.size >= this.size * 2) return 'full';
    c.joinedAt = Date.now();
    this.members.set(c.id, c);
    c.room = this;
    if (!this.hostId || !this.members.has(this.hostId)) this.hostId = c.id;
    // Join the side that has your club, otherwise the side with fewer people.
    let team;
    const club = c.profile.club;
    const tClub = [0, 1].find(t => club && this.idents[t] && this.idents[t].id === club.id && this.humansOn(t) > 0);
    if (tClub !== undefined && this.humansOn(tClub) < this.size) team = tClub;
    else team = this.humansOn(0) <= this.humansOn(1) ? 0 : 1;
    if (this.humansOn(team) >= this.size) team = 1 - team;
    const slot = this.bestSlot(team, c.profile.pos);
    if (slot) this.takeSlot(c, slot);
    this.emptySince = 0;
    return null;
  }
  takeSlot(c, p) {
    const old = this.players.find(q => q.cid === c.id);
    if (old === p) return;
    if (old) this.freeSlot(old);
    const prof = c.profile;
    p.cid = c.id; p.afk = false; p.active = true;
    p.name = prof.name; p.num = prof.num; p.look = prof.look; p.celeb = prof.celeb;
    const a = { ...prof.attrs };
    if (p.role !== 'GK') a.gk = Math.min(a.gk, 45);
    p.attrs = a; p.D = S.derive(a);
    p.q = []; p.acts = []; p.inp = { mx: 0, my: 0, spr: 0, ax: p.x, ay: p.y };
    p.call = -10; p.buf = null;
    if (!p.stats) p.stats = this.blankStats();
    c.slot = p.i;
    if (this.phase === 'warmup') this.pickIdents();
    this.rosterVer++;
  }
  freeSlot(p) {
    if (this.owner === p.i && p.st === S.HOLD) p.st = 0;
    p.q = []; p.acts = []; p.ack = 0;
    this.makeBot(p);
    if (!this.bots) { p.active = false; if (this.owner === p.i) this.owner = -1; }
    if (p.st === S.LOCK && (!this.set || this.set.taker !== p.i)) p.st = 0;
    if (this.phase === 'warmup') this.pickIdents();
    this.rosterVer++;
  }
  removeClient(c) {
    const p = this.players.find(q => q.cid === c.id);
    if (p) this.freeSlot(p);
    this.members.delete(c.id);
    c.room = null; c.slot = -1;
    if (this.hostId === c.id) {
      const next = [...this.members.values()].sort((a, b) => a.joinedAt - b.joinedAt)[0];
      this.hostId = next ? next.id : 0;
    }
    if (!this.members.size) this.emptySince = Date.now();
    this.rosterVer++;
  }
  rosterMsg(c) {
    return {
      t: 'roster',
      ver: this.rosterVer,
      you: c.slot != null ? c.slot : -1,
      host: this.hostId === c.id,
      teams: this.idents.map((id, t) => ({ name: id.name, abbr: id.abbr, c1: id.c1, c2: id.c2, pattern: id.pattern, crest: id.crest, club: id.bot ? null : id.id, kit: this.kits[t] })),
      players: this.players.map(p => ({ i: p.i, team: p.team, slot: p.slot, role: p.role, name: p.name, num: p.num, bot: !p.cid, act: p.active, look: p.look, celeb: p.celeb, ovr: ovr(p.attrs, p.role) }))
    };
  }
  infoMsg() {
    return { t: 'room', code: this.code, name: this.name, pub: this.pub, size: this.size, len: this.len, diff: this.diff, bots: this.bots, golden: this.golden, warm: this.warmLen, F: this.F };
  }
  listing() {
    return {
      code: this.code, name: this.name, size: this.size, len: this.len, diff: this.diff, bots: this.bots, golden: this.golden,
      humans: this.members.size, max: this.size * 2, phase: this.phase, clock: Math.floor(this.clock), score: this.score,
      teams: this.idents.map(id => ({ name: id.name, abbr: id.abbr, c1: id.c1, c2: id.c2, crest: id.crest }))
    };
  }

  // ---- stats ---------------------------------------------------------------
  blankStats() { return { g: 0, a: 0, sh: 0, sot: 0, pa: 0, pc: 0, tk: 0, int: 0, sv: 0, lost: 0, fo: 0, mins: 0 }; }
  resetStats() {
    for (const p of this.players) p.stats = this.blankStats();
    this.tstats = [0, 1].map(() => ({ poss: 0, sh: 0, sot: 0, pa: 0, pc: 0, tk: 0, fo: 0, co: 0 }));
    this.goals = [];
  }

  // ---- geometry helpers ----------------------------------------------------
  sgn(t) { return t === 0 ? 1 : -1; }
  toWorld(t, lx, ly) { const s = this.sgn(t); return { x: s * lx * this.F.W / 2, y: s * ly * this.F.L / 2 }; }
  local(t, x, y) { const s = this.sgn(t); return { lx: s * x / (this.F.W / 2), ly: s * y / (this.F.L / 2) }; }
  oppGoal(t) { return { x: 0, y: this.sgn(t) * this.F.L / 2 }; }
  ownGoal(t) { return { x: 0, y: -this.sgn(t) * this.F.L / 2 }; }
  inOwnBox(p, margin) {
    const F = this.F, m = margin || 0, ey = -this.sgn(p.team) * F.L / 2;
    return Math.abs(p.x) < F.boxW / 2 + m && Math.abs(p.y - ey) < F.boxD + m && Math.sign(p.y) === Math.sign(ey);
  }
  inBoxOf(t, x, y) { // inside team t's own box
    const F = this.F, ey = -this.sgn(t) * F.L / 2;
    return Math.abs(x) < F.boxW / 2 && Math.abs(y - ey) < F.boxD && Math.sign(y) === Math.sign(ey);
  }
  placeFormation(kickoffTeam) {
    for (const p of this.players) {
      let w = this.toWorld(p.team, p.ax * 0.9, p.ay * 0.88 - 0.02);
      if (p.role !== 'GK') w.y = this.sgn(p.team) * Math.min(this.sgn(p.team) * w.y, -1.5);
      p.x = w.x; p.y = w.y; p.vx = 0; p.vy = 0; p.face = p.team === 0 ? Math.PI / 2 : -Math.PI / 2;
      p.st = 0; p.stT = 0; p.buf = null; p.kcd = 0; p.tcd = 0;
    }
    if (kickoffTeam !== false) {
      // Kicking team's two most forward players stand on the centre spot
      const fw = this.players.filter(p => p.team === kickoffTeam && p.active && p.role !== 'GK').sort((a, b) => b.ay - a.ay);
      if (fw[0]) { fw[0].x = 0; fw[0].y = -this.sgn(kickoffTeam) * 0.6; }
      if (fw[1]) { fw[1].x = (fw[1].ax < 0 ? -1 : 1) * 4; fw[1].y = -this.sgn(kickoffTeam) * 1.5; }
      // Defending team stays outside the circle
      for (const p of this.players) if (p.team !== kickoffTeam) {
        const d = hyp(p.x, p.y);
        if (d < this.F.circle + 1) { const k = (this.F.circle + 1) / Math.max(0.1, d); p.x *= k; p.y = p.y === 0 ? -this.sgn(p.team) * (this.F.circle + 1) : p.y * k; }
      }
    }
  }
  resetBall(x, y, z) { Object.assign(this.ball, { x: x || 0, y: y || 0, z: z || 0, vx: 0, vy: 0, vz: 0, sp: 0, net: 0, passTo: -1, passT: 0, kickT: 0 }); this.owner = -1; }

  // ---- events --------------------------------------------------------------
  ev(e) { this.evq.push(e); }
  touch(p, kind) {
    this.touches.push({ i: p.i, team: p.team, t: this.time, kind });
    if (this.touches.length > 12) this.touches.shift();
    if (this.pendingPass && kind !== 'pass-start') {
      const pp = this.pendingPass;
      if (p.i !== pp.i) {
        if (p.team === pp.team) { this.players[pp.i].stats.pc++; this.tstats[pp.team].pc++; }
        else if (this.isPlaying()) p.stats.int++;
        this.pendingPass = null;
      }
    }
  }
  isPlaying() { return this.phase === 'play' || this.phase === 'set'; }

  // ---- input ---------------------------------------------------------------
  consumeInput(p) {
    if (p.q.length > 7) { while (p.q.length > 3) { const x = p.q.shift(); if (x[6]) p.acts.push([x[6], x[7]]); p.ack = x[0]; } }
    const x = p.q.shift();
    if (!x) return;
    p.ack = x[0];
    p.inp.mx = clamp(x[1] / 100, -1, 1); p.inp.my = clamp(x[2] / 100, -1, 1); p.inp.spr = x[3] ? 1 : 0;
    p.inp.ax = clamp(x[4] / 100, -80, 80); p.inp.ay = clamp(x[5] / 100, -80, 80);
    if (x[6]) p.acts.push([x[6], x[7]]);
  }
  aimAngle(p) {
    if (p.cid && !p.afk) {
      const dx = p.inp.ax - p.x, dy = p.inp.ay - p.y;
      return Math.hypot(dx, dy) > 0.3 ? Math.atan2(dy, dx) : p.face;
    }
    return p.ai.look != null ? p.ai.look : null;
  }

  // ---- main tick -------------------------------------------------------------
  step() {
    const dt = S.DT;
    this.tick++; this.time += dt;
    const P = this.players;
    for (const p of P) {
      if (!p.active) continue;
      if (p.cid && !p.afk) this.consumeInput(p);
      if (p.kcd > 0) p.kcd -= dt;
      if (p.tcd > 0) p.tcd -= dt;
      if (p.buf && this.time > p.buf.until) p.buf = null;
    }
    if (this.tick % 3 === 0) this.think();
    for (const p of P) if (p.active && (!p.cid || p.afk)) this.steer(p);
    for (const p of P) if (p.active && p.acts.length) { const acts = p.acts; p.acts = []; for (const a of acts) this.action(p, a[0], a[1]); }
    for (const p of P) if (p.active) this.movePlayer(p, dt);
    this.collide();
    this.updateBall(dt);
    this.rules(dt);
  }

  movePlayer(p, dt) {
    const hasBall = this.owner === p.i;
    if (p.st === 0 || p.st === S.HOLD || p.st === S.LOCK) {
      const inp = p.inp;
      S.stepMove(p, inp.mx, inp.my, inp.spr, this.aimAngle(p), dt, this.F, hasBall, p.D);
      if (p.st === S.HOLD && !this.inOwnBox(p, -0.3)) {
        // A keeper carrying the ball can't leave the box
        const F = this.F, ey = -this.sgn(p.team) * F.L / 2;
        p.x = clamp(p.x, -F.boxW / 2 + 0.3, F.boxW / 2 - 0.3);
        const lo = Math.min(ey, ey + this.sgn(p.team) * (F.boxD - 0.3)), hi = Math.max(ey, ey + this.sgn(p.team) * (F.boxD - 0.3));
        p.y = clamp(p.y, lo, hi);
      }
      if (this.phase === 'set' && this.set && this.set.type === 'kickoff' && p.st !== S.LOCK) {
        // Stay in your own half until kick-off
        const s = this.sgn(p.team);
        if (s * p.y > -0.3) { p.y = -s * 0.3; p.vy = 0; }
      }
      return;
    }
    p.stT -= dt;
    if (p.st === S.SLIDE) {
      const k = Math.exp(-1.7 * dt); p.vx *= k; p.vy *= k;
      p.x += p.vx * dt; p.y += p.vy * dt;
      this.slideContact(p);
      if (p.stT <= 0) { p.st = S.STUN; p.stT = 0.4; }
    } else if (p.st === S.DIVE) {
      const k = Math.exp(-2.6 * dt); p.vx *= k; p.vy *= k;
      p.x += p.vx * dt; p.y += p.vy * dt;
      if (p.stT <= 0) { p.st = S.STUN; p.stT = 0.45; }
    } else if (p.st === S.STUN) {
      const k = Math.exp(-7 * dt); p.vx *= k; p.vy *= k;
      p.x += p.vx * dt; p.y += p.vy * dt;
      if (p.stT <= 0) p.st = 0;
    } else if (p.st === S.CELEB) {
      const t = p.celebTo;
      if (t) {
        const dx = t.x - p.x, dy = t.y - p.y, d = hyp(dx, dy);
        const run = p.stT > 0 && d > 1.5;
        S.stepMove(p, run ? dx / d : 0, run ? dy / d : 0, run ? 1 : 0, null, dt, this.F, false, p.D);
        p.sta = 100;
      }
    }
  }

  collide() {
    const P = this.players;
    for (let i = 0; i < P.length; i++) {
      const a = P[i];
      if (!a.active) continue;
      for (let j = i + 1; j < P.length; j++) {
        const b = P[j];
        if (!b.active) continue;
        const dx = b.x - a.x, dy = b.y - a.y;
        if (dx > 0.8 || dx < -0.8 || dy > 0.8 || dy < -0.8) continue;
        const d = hyp(dx, dy);
        if (d >= 0.8 || d < 1e-5) continue;
        let wa = b.attrs.phy + (this.owner === b.i ? 15 : 0), wb = a.attrs.phy + (this.owner === a.i ? 15 : 0);
        const s = wa + wb;
        const push = (0.8 - d), nx = dx / d, ny = dy / d;
        a.x -= nx * push * wa / s; a.y -= ny * push * wa / s;
        b.x += nx * push * wb / s; b.y += ny * push * wb / s;
        // Bumping into the dribbler can knock it loose
        if (this.isPlaying() || this.phase === 'warmup') {
          for (const [o, q] of [[a, b], [b, a]]) {
            if (this.owner === o.i && q.team !== o.team && q.st === 0 && o.st === 0 && q.tcd <= 0) {
              const db = hyp(this.ball.x - q.x, this.ball.y - q.y);
              const faceB = Math.cos(S.wrap(Math.atan2(this.ball.y - q.y, this.ball.x - q.x) - q.face));
              if (db < 0.7 && faceB > 0.3 && Math.random() < 0.012 * (q.attrs.def / Math.max(30, o.attrs.dri)) * (q.cid ? 1.6 : 1)) {
                this.owner = -1;
                const ang = Math.atan2(q.y - o.y, q.x - o.x) + rnd(-0.8, 0.8);
                Object.assign(this.ball, { vx: o.vx * 0.5 + Math.cos(ang) * 3, vy: o.vy * 0.5 + Math.sin(ang) * 3, vz: 0 });
                o.kcd = 0.35; q.tcd = 0.5;
                q.stats.tk++; this.tstats[q.team].tk++; o.stats.lost++;
                this.touch(q, 'tackle');
                this.ev({ k: 'tk', i: q.i });
              }
            }
          }
        }
      }
    }
  }

  // ---- ball -------------------------------------------------------------------
  updateBall(dt) {
    const b = this.ball;
    if (this.owner >= 0) {
      const o = this.players[this.owner];
      if (!o.active || (o.st !== 0 && o.st !== S.HOLD && o.st !== S.LOCK)) { this.owner = -1; }
      else {
        if (o.st === S.HOLD) {
          b.x = o.x + Math.cos(o.face) * 0.32; b.y = o.y + Math.sin(o.face) * 0.32; b.z = 1.05;
          b.vx = o.vx; b.vy = o.vy; b.vz = 0;
          o.holdT += dt;
        } else {
          const sp = hyp(o.vx, o.vy), off = S.ballOffset(sp);
          b.x = o.x + Math.cos(o.face) * off; b.y = o.y + Math.sin(o.face) * off; b.z = 0;
          b.vx = o.vx; b.vy = o.vy; b.vz = 0;
        }
        b.sp = 0;
        if (this.isPlaying()) this.tstats[o.team].poss++;
        return;
      }
    }
    const hit = S.stepBall(b, dt, this.F);
    if (hit && this.isPlaying()) { this.ev({ k: 'post' }); if (this.pendingShot) this.pendingShot.post = true; }
    if (this.phase === 'warmup' || this.phase === 'full') {
      const bx = this.F.W / 2 + 4, by = this.F.L / 2 + 4;
      if (Math.abs(b.x) > bx) { b.x = Math.sign(b.x) * bx; b.vx *= -0.5; }
      if (Math.abs(b.y) > by && !b.net) { b.y = Math.sign(b.y) * by; b.vy *= -0.5; }
    }
    if (b.net) return;
    this.ballContacts();
  }

  ballContacts() {
    const b = this.ball, P = this.players, F = this.F;
    const bs = hyp(b.vx, b.vy, b.vz);
    let best = null, bd = 1e9, gkBest = null, gkD = 1e9;
    for (const p of P) {
      if (!p.active || p.kcd > 0) continue;
      if (p.st !== 0 && p.st !== S.DIVE && p.st !== S.LOCK) continue;
      const dx = b.x - p.x, dy = b.y - p.y;
      if (dx > 2 || dx < -2 || dy > 2 || dy < -2) continue;
      const d = hyp(dx, dy);
      // Keeper hands
      if (p.role === 'GK' && this.inOwnBox(p, 0.2) && this.phase !== 'warmup' || (p.role === 'GK' && this.phase === 'warmup' && this.inOwnBox(p, 0.2))) {
        const reach = (p.st === S.DIVE ? 1.05 : 0.75) + p.attrs.gk * 0.003;
        const top = p.st === S.DIVE ? 1.6 + p.diveZ * 0.5 : 2.55;
        if (d < reach && b.z < top && d < gkD) {
          // Don't catch your own team's back passes from close range
          const last = this.touches[this.touches.length - 1];
          const own = last && last.team === p.team && last.i !== p.i && this.time - last.t < 1.2;
          if (!own || bs > 14) { gkBest = p; gkD = d; }
        }
      }
      if (p.st === S.DIVE) continue;
      // Pass meant for someone else on your team: let it run
      if (b.passTo >= 0 && b.passTo !== p.i && this.time - b.passT < 1.4) {
        const r = P[b.passTo];
        if (r && r.team === p.team && !p.cid && r.active) continue;
      }
      if (b.z < 0.95) {
        const R = p.D.ctrl + (p.cid ? 0.08 : 0);
        if (d < R && d < bd) {
          // A fast ball flashing past isn't automatically yours: one try per kick
          const rel = hyp(b.vx - p.vx, b.vy - p.vy);
          if (rel > 9 && b.passTo !== p.i && d > 0.38 && !p.buf) {
            if (p.tryK === b.kickT) continue;
            p.tryK = b.kickT;
            const since = this.time - (b.kickT || 0);
            const ch = clamp(0.2 + p.attrs.def * 0.0035 + (1 - d / R) * 0.45 - (since < 0.25 ? 0.25 : 0) + (p.cid ? 0.15 : 0) - (rel - 9) * 0.02, 0.05, 0.9);
            if (Math.random() > ch) continue;
          }
          best = p; bd = d;
        }
      } else if (b.z < 2.45 && d < 0.75 && d < bd) {
        best = p; bd = d;
      }
    }
    if (gkBest) { this.keeperContact(gkBest, bs); return; }
    if (!best) return;
    const p = best;
    const rvx = b.vx - p.vx, rvy = b.vy - p.vy, rel = hyp(rvx, rvy, b.vz);
    // One-touch actions (first-time passes, volleys, headers)
    if (p.buf) {
      const a = p.buf; p.buf = null;
      this.owner = p.i;
      this.touch(p, 'touch');
      b.z = Math.min(b.z, 2.3);
      this.kick(p, a.act, a.pow, true);
      return;
    }
    if (b.z >= 0.95) {
      // Ball hits head or chest: knock it down or away
      if (!p.cid && p.team != null && this.botHeader(p)) return;
      const ang = Math.atan2(rvy, rvx) + Math.PI + rnd(-0.6, 0.6);
      const sp = Math.min(6, rel * 0.3);
      Object.assign(b, { vx: p.vx + Math.cos(ang) * sp, vy: p.vy + Math.sin(ang) * sp, vz: 1 + rnd(0, 1.5) });
      this.touch(p, 'touch');
      p.kcd = 0.15;
      return;
    }
    const trap = 13 + p.attrs.dri * 0.13 + (p.cid ? 3 : 0) + (p.role === 'GK' ? 4 : 0);
    if (rel > trap && Math.random() < 0.85) {
      // Too hot to control: deflects off the player
      const nx = (b.x - p.x) / Math.max(0.05, bd), ny = (b.y - p.y) / Math.max(0.05, bd);
      const vn = rvx * nx + rvy * ny;
      let vx = rvx - 1.4 * vn * nx, vy = rvy - 1.4 * vn * ny;
      const k = 0.35 + rnd(0, 0.15);
      Object.assign(b, { vx: p.vx + vx * k + rnd(-1.5, 1.5), vy: p.vy + vy * k + rnd(-1.5, 1.5), vz: Math.abs(b.vz) * 0.3 + rnd(0, 1.5) });
      p.kcd = 0.2;
      this.touch(p, 'block');
      if (this.pendingShot && this.pendingShot.team !== p.team) this.ev({ k: 'block', i: p.i });
      return;
    }
    this.gainBall(p);
  }
  gainBall(p) {
    const b = this.ball;
    const prev = this.owner;
    this.owner = p.i;
    b.passTo = -1;
    p.ai.held = 0; p.ai.next = this.time + DIFF[this.diff].react * (0.6 + Math.random() * 0.8);
    if (this.pendingShot && this.pendingShot.team !== p.team) this.pendingShot = null;
    this.touch(p, 'touch');
    if (prev !== p.i) this.ev({ k: 'own', i: p.i });
  }
  keeperContact(p, bs) {
    const b = this.ball;
    const catchSp = 11 + p.attrs.gk * 0.16;
    const shot = this.pendingShot && this.pendingShot.team !== p.team;
    const handling = clamp(0.35 + p.attrs.gk * 0.006, 0.4, 0.95);
    if (bs < catchSp || (bs < catchSp + 8 && Math.random() < handling)) {
      this.owner = p.i;
      p.st = S.HOLD; p.holdT = 0; p.vx *= 0.3; p.vy *= 0.3;
      b.passTo = -1;
      if (shot) { p.stats.sv++; const s = this.players[this.pendingShot.i]; if (s) { s.stats.sot++; this.tstats[s.team].sot++; } this.ev({ k: 'save', i: p.i, c: 1 }); }
      this.pendingShot = null;
      this.touch(p, 'catch');
      p.ai.next = this.time + 1.2;
    } else {
      // Parry away from goal
      const away = this.sgn(p.team);
      const ang = Math.atan2(away * 0.6, Math.sign(b.x - p.x || rnd(-1, 1)) * 1) + rnd(-0.5, 0.5);
      const sp = bs * rnd(0.25, 0.4);
      Object.assign(b, { vx: Math.cos(ang) * sp, vy: Math.sin(ang) * sp, vz: rnd(1, 4) });
      p.kcd = 0.3;
      if (shot) { p.stats.sv++; const s = this.players[this.pendingShot.i]; if (s) { s.stats.sot++; this.tstats[s.team].sot++; } this.ev({ k: 'save', i: p.i, c: 0 }); }
      this.pendingShot = null;
      this.touch(p, 'parry');
    }
  }
  slideContact(p) {
    const b = this.ball;
    const fx = p.x + Math.cos(p.face) * 0.55, fy = p.y + Math.sin(p.face) * 0.55;
    const ownerP = this.owner >= 0 ? this.players[this.owner] : null;
    if ((this.owner < 0 || (ownerP && ownerP.team !== p.team && ownerP.st !== S.HOLD)) && b.z < 0.6 && hyp(b.x - fx, b.y - fy) < 0.95) {
      if (ownerP) { ownerP.stats.lost++; ownerP.kcd = 0.4; p.stats.tk++; this.tstats[p.team].tk++; this.ev({ k: 'tk', i: p.i }); }
      this.owner = -1;
      const sp = 7 + rnd(0, 3);
      Object.assign(b, { vx: Math.cos(p.face) * sp + rnd(-2, 2), vy: Math.sin(p.face) * sp + rnd(-2, 2), vz: rnd(0, 1.5) });
      p.slideHit = true;
      this.touch(p, 'tackle');
      return;
    }
    if (p.slideHit || !this.isPlaying() || this.phase === 'set') return;
    for (const q of this.players) {
      if (!q.active || q.team === p.team || q.st === S.STUN || q.st === S.DIVE) continue;
      if (hyp(q.x - fx, q.y - fy) < 0.8) {
        const near = this.owner === q.i || hyp(q.x - b.x, q.y - b.y) < 2.5;
        q.st = S.STUN; q.stT = 0.9; q.vx *= 0.3; q.vy *= 0.3;
        if (this.owner === q.i) this.owner = -1;
        if (near) { this.foul(p, q); return; }
      }
    }
  }
  foul(p, q) {
    p.stats.fo++; this.tstats[p.team].fo++;
    this.ev({ k: 'foul', i: p.i, v: q.i });
    const pen = this.inBoxOf(p.team, q.x, q.y);
    if (pen) this.startSet('penalty', q.team, 0, this.sgn(q.team) * (this.F.L / 2 - this.F.spot));
    else this.startSet('free', q.team, clamp(q.x, -this.F.W / 2 + 0.5, this.F.W / 2 - 0.5), clamp(q.y, -this.F.L / 2 + 0.5, this.F.L / 2 - 0.5));
  }

  // ---- actions -------------------------------------------------------------------
  // act: 1 pass, 2 shoot, 3 through, 4 lob/cross, 5 knock-on, 6 call for pass
  action(p, act, pow) {
    pow = clamp(Number(pow) || 0, 0, 100) / 100;
    if (act === 6) { p.call = this.time; this.ev({ k: 'call', i: p.i }); return; }
    if (this.phase === 'goal' || this.phase === 'half') return;
    if (this.phase === 'set' && this.set) {
      if (this.set.taker === p.i && this.set.t > 0.35) this.takeSet(p, act, pow);
      else if (p.role === 'GK' && act === 2 && this.set.type === 'penalty' && this.set.kicked) this.dive(p);
      return;
    }
    if (p.st === S.LOCK) return;
    if (this.owner === p.i && (p.st === 0 || p.st === S.HOLD)) { this.kick(p, act, pow, false); return; }
    if (p.st !== 0) return;
    const b = this.ball;
    const d = hyp(b.x - p.x, b.y - p.y);
    if (this.owner < 0 && act <= 4) {
      // Ball incoming: queue a first-time touch
      const rvx = b.vx - p.vx, rvy = b.vy - p.vy;
      const closing = -((b.x - p.x) * rvx + (b.y - p.y) * rvy) / Math.max(0.1, d);
      if (d < 3.2 || (closing > 2 && d / closing < 0.7)) { p.buf = { act, pow, until: this.time + 0.45 }; return; }
    }
    if (p.role === 'GK' && act === 2 && this.inOwnBox(p, 0)) { this.dive(p); return; }
    const o = this.owner >= 0 ? this.players[this.owner] : null;
    if (act === 1 && p.tcd <= 0) {
      if (o && o.team !== p.team && o.st !== S.HOLD) this.standTackle(p, o);
      else if (this.owner < 0 && d < 2.6) p.buf = { act, pow, until: this.time + 0.45 };
    } else if (act === 2 && p.tcd <= 0 && (o ? o.team !== p.team && o.st !== S.HOLD : true) && d < 8) {
      this.slide(p);
    }
  }
  standTackle(p, o) {
    p.tcd = 0.8;
    const b = this.ball;
    const db = hyp(b.x - p.x, b.y - p.y);
    this.ev({ k: 'stk', i: p.i });
    if (db > 1.9) { p.st = S.STUN; p.stT = 0.22; return; }
    const facing = Math.cos(S.wrap(Math.atan2(b.y - p.y, b.x - p.x) - p.face));
    let ch = 0.42 + (p.attrs.def - o.attrs.dri) * 0.009 + facing * 0.12 - (db > 1.3 ? 0.15 : 0) + (p.cid ? 0.1 : 0);
    ch = clamp(ch, 0.12, 0.9);
    if (Math.random() < ch) {
      o.stats.lost++; o.kcd = 0.45; p.stats.tk++; this.tstats[p.team].tk++;
      this.ev({ k: 'tk', i: p.i });
      if (Math.random() < 0.55) { this.owner = p.i; this.touch(p, 'tackle'); p.ai.held = 0; this.ball.passTo = -1; }
      else {
        this.owner = -1;
        const ang = Math.atan2(p.y - o.y, p.x - o.x) + rnd(-1, 1);
        Object.assign(b, { vx: Math.cos(ang) * rnd(3, 6), vy: Math.sin(ang) * rnd(3, 6), vz: 0 });
        this.touch(p, 'tackle');
      }
    } else { p.st = S.STUN; p.stT = 0.3; }
  }
  slide(p) {
    p.tcd = 1.2;
    const a = p.cid && !p.afk ? this.aimAngle(p) : (p.ai.look != null ? p.ai.look : p.face);
    p.face = a;
    const sp = 9 + p.attrs.pac * 0.025;
    p.vx = Math.cos(a) * sp; p.vy = Math.sin(a) * sp;
    p.st = S.SLIDE; p.stT = 0.55; p.slideHit = false;
    if (this.owner === p.i) this.owner = -1;
    this.ev({ k: 'slide', i: p.i });
  }
  dive(p) {
    if (p.st !== 0 && p.st !== S.LOCK) return;
    const ax = p.cid && !p.afk ? p.inp.ax : p.ai.diveX, ay = p.cid && !p.afk ? p.inp.ay : p.ai.diveY;
    let dx = ax - p.x, dy = ay - p.y;
    const d = hyp(dx, dy) || 1;
    dx /= d; dy /= d;
    const sp = 3.4 + p.attrs.gk * 0.022;
    p.vx = dx * sp; p.vy = dy * sp;
    p.face = Math.atan2(this.sgn(p.team), 0);
    p.diveDir = Math.sign(dx * this.sgn(p.team)) || 1;
    p.st = S.DIVE; p.stT = 0.65; p.diveZ = clamp(p.cid ? 0.6 : p.ai.diveZ || 0.5, 0, 1.6);
    this.ev({ k: 'dive', i: p.i, d: p.diveDir });
  }

  // Executes a kick for the ball owner. act: 1 pass 2 shot 3 through 4 lob 5 knock-on
  kick(p, act, pow, firstTime) {
    const b = this.ball, F = this.F;
    if (this.owner !== p.i) return;
    const hands = p.st === S.HOLD;
    const human = p.cid && !p.afk;
    const aimA = human ? this.aimAngle(p) : (p.ai.look != null ? p.ai.look : p.face);
    const ax = human ? p.inp.ax : (p.ai.kx != null ? p.ai.kx : p.x + Math.cos(aimA) * 15);
    const ay = human ? p.inp.ay : (p.ai.ky != null ? p.ai.ky : p.y + Math.sin(aimA) * 15);
    const a = p.attrs;
    const errM = (p.cid ? 1 : DIFF[this.diff].err) * (firstTime ? 1.3 : 1);
    const sp = hyp(p.vx, p.vy);
    const z0 = hands ? 1.0 : Math.max(0.05, b.z);
    const mates = this.players.filter(q => q.active && q.team === p.team && q.i !== p.i && q.st !== S.CELEB);
    let vx = 0, vy = 0, vz = 0, spin = 0, kind = 'pass', target = -1;
    if (hands && act === 2) act = 4;
    if (b.z > 0.95 && !hands) {
      // Header
      const toGoal = this.oppGoal(p.team);
      if (act === 2) {
        const dir = Math.atan2(ay - p.y, ax - p.x) + gauss() * (0.06 + (100 - a.sho) * 0.0014) * errM;
        const s = 13 + a.sho * 0.06 + pow * 4;
        vx = Math.cos(dir) * s; vy = Math.sin(dir) * s; vz = -1.5 + rnd(-1, 1.5);
        kind = 'shot';
      } else {
        const r = S.pickReceiver(p, aimA, ax, ay, mates, true);
        const tx = r ? r.x + r.vx * 0.6 : p.x + Math.cos(aimA) * 12, ty = r ? r.y + r.vy * 0.6 : p.y + Math.sin(aimA) * 12;
        const d = hyp(tx - p.x, ty - p.y), dir = Math.atan2(ty - p.y, tx - p.x) + gauss() * 0.12 * errM;
        const s = clamp(d * 0.75, 6, 15);
        vx = Math.cos(dir) * s; vy = Math.sin(dir) * s; vz = 2.5;
        target = r ? r.i : -1;
      }
      void toGoal;
    } else if (act === 5) {
      // Knock the ball ahead and chase it
      const dir = p.face, s = Math.max(sp, 4) + 4.5;
      vx = Math.cos(dir) * s; vy = Math.sin(dir) * s; vz = 0;
      kind = 'knock';
      p.kcd = 0.25;
    } else if (act === 2) {
      // Shot
      const goalY = this.sgn(p.team) * F.L / 2;
      const toGoalA = Math.atan2(goalY - p.y, 0 - p.x);
      let tx = ax, ty = ay, h = 0.3 + pow * pow * 2.5;
      const dGoal = hyp(goalY - p.y, p.x);
      if (Math.abs(S.wrap(aimA - toGoalA)) < 0.75 && dGoal < 45 && Math.sign(goalY - p.y) === Math.sign(goalY)) {
        // Aim assist: place it inside the posts where the cursor points
        let cx;
        if (Math.abs(Math.sin(aimA)) > 0.05) cx = p.x + Math.cos(aimA) * (goalY - p.y) / Math.sin(aimA);
        else cx = p.x;
        const lim = F.gw / 2 - 0.3;
        tx = clamp(cx, -lim, lim); ty = goalY;
        if (!human) tx = p.ai.kx != null ? clamp(p.ai.kx, -lim, lim) : tx;
      }
      const s = (15 + pow * 19) * (0.78 + a.sho * 0.0028) * (firstTime ? 0.95 : 1);
      const err = (0.02 + (100 - a.sho) * 0.0011 + Math.min(1, sp / 9) * 0.02 + (pow > 0.88 ? 0.03 : 0) + (b.z > 0.3 ? 0.03 : 0)) * errM;
      const dir = Math.atan2(ty - p.y, tx - p.x) + gauss() * err;
      const d = hyp(tx - p.x, ty - p.y);
      h += gauss() * (0.15 + (100 - a.sho) * 0.008) * errM;
      if (!human && p.ai.kh != null) h = p.ai.kh + gauss() * 0.25 * errM;
      vz = S.shotVz(d, s, clamp(h, 0.1, 4), z0);
      vx = Math.cos(dir) * s; vy = Math.sin(dir) * s;
      spin = gauss() * 0.15;
      kind = 'shot';
    } else {
      // Passing
      const through = act === 3, lob = act === 4 || hands && act === 4;
      let r = S.pickReceiver(p, aimA, ax, ay, mates, through);
      if (!human && p.ai.passTo != null && this.players[p.ai.passTo]) r = this.players[p.ai.passTo];
      let tx, ty;
      const dist = r ? hyp(r.x - p.x, r.y - p.y) : 0;
      if (r) {
        const lead = clamp(dist / 16, 0.25, 1.6);
        tx = r.x + r.vx * lead; ty = r.y + r.vy * lead;
        if (through) {
          const s = this.sgn(p.team);
          const rsp = hyp(r.vx, r.vy);
          const dx = rsp > 2 ? r.vx / rsp : 0, dy = rsp > 2 ? r.vy / rsp : s;
          const extra = human ? 5 + pow * 6 : (p.ai.lead || 6);
          tx = r.x + (dx * 0.6) * extra + r.vx * lead * 0.5; ty = r.y + (dy * 0.6 + s * 0.6) * extra + r.vy * lead * 0.5;
        }
        target = r.i;
      } else {
        const want = clamp(hyp(ax - p.x, ay - p.y), 6, lob ? 55 : 40);
        tx = p.x + Math.cos(aimA) * want; ty = p.y + Math.sin(aimA) * want;
      }
      if (!human && p.ai.kx != null && p.ai.passTo == null) { tx = p.ai.kx; ty = p.ai.ky; }
      tx = clamp(tx, -F.W / 2 + 1.5, F.W / 2 - 1.5); ty = clamp(ty, -F.L / 2 + 1, F.L / 2 - 1);
      let d = hyp(tx - p.x, ty - p.y);
      const pe = (0.012 + (100 - a.pas) * 0.0011) * errM * (1 + Math.min(1, sp / 9) * 0.5);
      const dir = Math.atan2(ty - p.y, tx - p.x) + gauss() * pe;
      d *= 1 + gauss() * pe * 0.8;
      if (lob) {
        const T = clamp(0.7 + d / 22, 0.8, 2.3);
        const L = S.loft(Math.max(3, d), T, z0);
        vx = Math.cos(dir) * L.vh; vy = Math.sin(dir) * L.vh; vz = L.vz;
        kind = hands && p.st === S.HOLD ? 'punt' : 'lob';
      } else if (hands) {
        const s = clamp(S.passSpeed(Math.min(d, 30), 7) * 1.05, 8, 19);
        vx = Math.cos(dir) * s; vy = Math.sin(dir) * s; vz = 1.2;
        kind = 'throw';
      } else {
        const vf = through ? 8 + d * 0.12 : 6.5 + d * 0.18;
        let s = S.passSpeed(Math.max(2, d), vf);
        s = Math.min(s, 30) * (firstTime ? 1.05 : 1);
        vx = Math.cos(dir) * s; vy = Math.sin(dir) * s; vz = b.z > 0.3 ? 0.5 : 0;
      }
      if (kind !== 'knock') {
        p.stats.pa++; this.tstats[p.team].pa++;
        this.pendingPass = { i: p.i, team: p.team };
      }
    }
    // Release
    this.owner = -1;
    if (hands) { p.st = 0; b.z = 1.0; }
    b.vx = vx; b.vy = vy; b.vz = vz; b.sp = spin;
    if (b.z < 0.02 && vz > 0) b.z = 0.03;
    b.passTo = target; b.passT = this.time; b.kickT = this.time;
    if (kind !== 'knock') p.kcd = 0.3;
    p.ai.passTo = null; p.ai.kx = null; p.ai.ky = null; p.ai.kh = null;
    if (kind !== 'knock') this.touch(p, kind === 'shot' ? 'shot' : 'pass-start');
    if (kind === 'shot') {
      p.stats.sh++; this.tstats[p.team].sh++;
      this.pendingShot = { i: p.i, team: p.team, t: this.time };
    }
    this.ev({ k: 'kick', i: p.i, s: r1(hyp(vx, vy, vz)), y: kind });
  }

  // ---- set pieces -------------------------------------------------------------------
  startSet(type, team, x, y) {
    const F = this.F, b = this.ball;
    this.phase = 'set';
    if (this.owner >= 0) { const o = this.players[this.owner]; if (o.st === S.HOLD) o.st = 0; }
    this.resetBall(x, y, 0);
    this.pendingShot = null; this.pendingPass = null;
    for (const p of this.players) { if (p.st === S.LOCK) p.st = 0; p.buf = null; }
    const cands = this.players.filter(p => p.team === team && p.active && (type === 'goalkick' ? true : p.role !== 'GK' || type === 'free' && false));
    let taker = null;
    if (type === 'goalkick') taker = cands.find(p => p.role === 'GK' && p.active) || cands[0];
    else if (type === 'kickoff') {
      const hum = cands.filter(p => p.cid && !p.afk && p.role !== 'GK').sort((a, c) => hyp(a.x, a.y) - hyp(c.x, c.y))[0];
      taker = hum && hyp(hum.x, hum.y) < 12 ? hum : cands.filter(p => p.role !== 'GK').sort((a, c) => hyp(a.x, a.y) - hyp(c.x, c.y))[0];
    } else if (type === 'penalty') {
      const hum = cands.filter(p => p.cid && !p.afk && p.role !== 'GK').sort((a, c) => c.attrs.sho - a.attrs.sho)[0];
      taker = hum || cands.filter(p => p.role !== 'GK').sort((a, c) => c.attrs.sho - a.attrs.sho)[0];
    } else {
      const out = cands.filter(p => p.role !== 'GK');
      const hum = out.filter(p => p.cid && !p.afk).sort((a, c) => hyp(a.x - x, a.y - y) - hyp(c.x - x, c.y - y))[0];
      const near = out.sort((a, c) => hyp(a.x - x, a.y - y) - hyp(c.x - x, c.y - y))[0];
      taker = hum && hyp(hum.x - x, hum.y - y) < (type === 'corner' ? 45 : 28) ? hum : near;
    }
    if (!taker) taker = this.players.find(p => p.team === team && p.active);
    if (!taker) { this.phase = 'play'; return; }
    const s = this.sgn(team);
    let aimA = Math.atan2(s, 0);
    if (type === 'throw') aimA = Math.atan2(0, -Math.sign(x)) * 0.5 + (s > 0 ? Math.PI / 4 : -Math.PI / 4) * Math.sign(-x) * 0 + Math.atan2(s * 0.5, -Math.sign(x));
    if (type === 'corner') aimA = Math.atan2(-Math.sign(y) * 0.3, -Math.sign(x)) ;
    if (type === 'corner') aimA = Math.atan2(s * 0 - Math.sign(y) * 1, -Math.sign(x) * 1);
    const back = type === 'throw' ? 0.45 : 0.55;
    taker.x = x - Math.cos(aimA) * back; taker.y = y - Math.sin(aimA) * back;
    if (type === 'throw') { taker.x = x + Math.sign(x) * 0.45; taker.y = y; }
    taker.vx = 0; taker.vy = 0; taker.face = aimA; taker.st = S.LOCK; taker.stT = 0;
    if (taker.cid) { taker.inp.ax = x + Math.cos(aimA) * 15; taker.inp.ay = y + Math.sin(aimA) * 15; }
    this.set = { type, team, x, y, taker: taker.i, t: 0, kicked: false, aimA };
    if (type === 'kickoff') this.placeFormation(team);
    if (type === 'kickoff') { taker.x = 0; taker.y = -s * 0.5; taker.face = Math.atan2(s, 0) + 0.0; }
    if (type === 'penalty') {
      const keeper = this.players.find(p => p.team !== team && p.role === 'GK' && p.active);
      const gy = s * F.L / 2;
      for (const p of this.players) {
        if (!p.active || p === taker || p === keeper) continue;
        // everyone else waits outside the box behind the ball
        const by = s * (F.L / 2 - F.boxD - 2.5);
        if (s * p.y > s * by) p.y = by - s * rnd(0, 6);
        if (Math.abs(p.x) < F.boxW / 2 + 1 && s * p.y > s * by) p.x = clamp(p.x, -F.boxW / 2, F.boxW / 2);
      }
      if (keeper) { keeper.x = 0; keeper.y = gy - s * 0.3; keeper.face = Math.atan2(-s, 0); keeper.vx = 0; keeper.vy = 0; keeper.st = 0; }
      taker.x = x; taker.y = y - s * 2.2; taker.face = Math.atan2(s, 0);
    }
    if (type === 'free') {
      // Defensive wall when in shooting range
      const g = this.oppGoal(team), dg = hyp(g.x - x, g.y - y);
      const defs = this.players.filter(p => p.active && p.team !== team && p.role !== 'GK' && !p.cid).sort((a, c) => hyp(a.x - x, a.y - y) - hyp(c.x - x, c.y - y));
      if (dg < F.L * 0.3) {
        const n = dg < F.L * 0.22 ? 3 : 2, wd = Math.min(9.15, F.circle);
        const ang = Math.atan2(g.y - y, g.x - x);
        for (let k = 0; k < n && k < defs.length; k++) {
          const off = (k - (n - 1) / 2) * 0.75 + 0.4;
          defs[k].x = x + Math.cos(ang) * wd - Math.sin(ang) * off; defs[k].y = y + Math.sin(ang) * wd + Math.cos(ang) * off;
          defs[k].vx = 0; defs[k].vy = 0; defs[k].face = ang + Math.PI; defs[k].ai.wall = this.time + 3;
        }
      }
    }
    if (type === 'corner') this.tstats[team].co++;
    this.ev({ k: 'set', y: type, team, i: taker.i, x: r2(x), yy: r2(y) });
    if (type !== 'kickoff') this.ev({ k: 'whistle', n: type === 'penalty' || type === 'free' ? 2 : 0 });
  }
  takeSet(p, act, pow) {
    const st = this.set;
    if (!st || st.kicked) return;
    const type = st.type;
    if (type === 'throw') { if (act === 2 || act === 3) act = 4; if (act === 5) act = 1; }
    if (type === 'penalty') { act = 2; }
    if (type === 'goalkick' && act === 5) act = 1;
    if (act === 5) act = 1;
    st.kicked = true;
    p.st = 0;
    this.owner = p.i;
    if (type === 'throw') {
      // Thrown from above the head; can't go too far
      const b = this.ball; b.z = 1.9;
      const aimA = p.cid && !p.afk ? this.aimAngle(p) : (p.ai.look != null ? p.ai.look : p.face);
      const ax = p.cid && !p.afk ? p.inp.ax : p.ai.kx, ay = p.cid && !p.afk ? p.inp.ay : p.ai.ky;
      const mates = this.players.filter(q => q.active && q.team === p.team && q.i !== p.i);
      let r = !p.cid && p.ai.passTo != null ? this.players[p.ai.passTo] : S.pickReceiver(p, aimA, ax, ay, mates, false);
      let tx, ty;
      if (r) { tx = r.x + r.vx * 0.5; ty = r.y + r.vy * 0.5; } else { const d0 = clamp(hyp(ax - p.x, ay - p.y), 5, 22); tx = p.x + Math.cos(aimA) * d0; ty = p.y + Math.sin(aimA) * d0; }
      tx = clamp(tx, -this.F.W / 2 + 3, this.F.W / 2 - 3);
      const d = clamp(hyp(tx - p.x, ty - p.y), 3, act === 4 ? 26 : 18);
      const dir = Math.atan2(ty - p.y, tx - p.x) + gauss() * 0.05;
      const T = act === 4 ? clamp(0.6 + d / 25, 0.7, 1.5) : clamp(0.35 + d / 30, 0.4, 0.9);
      const L = S.loft(d, T, 1.9);
      this.owner = -1;
      Object.assign(b, { vx: Math.cos(dir) * L.vh, vy: Math.sin(dir) * L.vh, vz: L.vz, sp: 0, passTo: r ? r.i : -1, passT: this.time, kickT: this.time });
      p.kcd = 0.6;
      p.stats.pa++; this.tstats[p.team].pa++; this.pendingPass = { i: p.i, team: p.team };
      this.touch(p, 'pass-start');
      this.ev({ k: 'kick', i: p.i, s: 10, y: 'throw' });
    } else {
      if (type === 'penalty') pow = clamp(pow || 0.65, 0.3, 1);
      this.kick(p, act, pow, false);
      p.kcd = 0.5;
    }
    this.phase = 'play';
    if (type === 'kickoff') this.ev({ k: 'whistle', n: 1 });
    if (type === 'penalty') {
      st.kicked = true;
      this.penaltyT = this.time;
      const keeper = this.players.find(q => q.team !== p.team && q.role === 'GK' && q.active);
      if (keeper && (!keeper.cid || keeper.afk)) {
        // Bot keeper guesses
        const b = this.ball, s = this.sgn(p.team), gy = s * this.F.L / 2;
        const tToLine = (gy - b.y) / (b.vy || 1);
        const realX = b.x + b.vx * tToLine;
        const guessRight = Math.random() < 0.38 + keeper.attrs.gk * 0.003 ? realX : (Math.random() < 0.5 ? -1 : 1) * this.F.gw * 0.3;
        keeper.ai.diveX = guessRight; keeper.ai.diveY = keeper.y; keeper.ai.diveZ = 0.6;
        keeper.ai.diveAt = this.time + 0.1;
      }
    }
    this.set = null;
  }

  // ---- rules & phases -------------------------------------------------------------
  rules(dt) {
    const b = this.ball, F = this.F;
    this.phaseT -= dt;
    if (this.phase === 'warmup') {
      if (b.net) {
        if (!this.warmGoalT) { this.warmGoalT = this.time; this.ev({ k: 'wgoal' }); }
        if (this.time - this.warmGoalT > 1.6) { this.resetBall(0, 0, 0); this.warmGoalT = 0; }
      }
      if (this.phaseT <= 0 && this.members.size > 0) this.startMatch();
      if (!this.members.size) this.phaseT = Math.max(this.phaseT, 5);
      return;
    }
    if (this.phase === 'full') {
      if (this.phaseT <= 0) { this.phase = 'warmup'; this.phaseT = 15; this.resetBall(0, 0, 0); for (const p of this.players) { if (p.st === S.CELEB || p.st === S.LOCK) p.st = 0; } this.pickIdents(); this.rosterVer++; }
      return;
    }
    if (this.phase === 'goal') {
      if (this.phaseT <= 0) {
        if (this.endAfterGoal) { this.fullTime(); return; }
        this.startSet('kickoff', this.kickoffTeam, 0, 0);
      }
      return;
    }
    if (this.phase === 'half') {
      if (this.phaseT <= 0) { this.half = 2; this.clock = 45; this.kickoffTeam = 1; for (const p of this.players) p.sta = Math.min(100, p.sta + 50); this.startSet('kickoff', 1, 0, 0); }
      return;
    }
    // play or set
    if (this.phase === 'set' && ((this.half === 1 && this.clock >= 46) || (this.half === 2 && !this.extra && this.clock >= 91) || (this.extra && this.clock >= 105))) {
      if (this.set) { const tk = this.players[this.set.taker]; if (tk && tk.st === S.LOCK) tk.st = 0; }
      this.set = null; this.phase = 'play';
    }
    const rate = 90 / (this.len * 60);
    this.clock += dt * rate;
    for (const p of this.players) if (p.active && p.stats) p.stats.mins += dt * rate;
    if (this.phase === 'set' && this.set) {
      const st = this.set;
      st.t += dt;
      const tk = this.players[st.taker];
      // Keep opponents back
      const rad = st.type === 'kickoff' ? F.circle : st.type === 'throw' ? 2.5 : st.type === 'penalty' ? 0 : Math.min(9.15, F.circle);
      if (rad > 0) for (const p of this.players) {
        if (!p.active || p.team === st.team || (p.ai.wall && p.ai.wall > this.time)) continue;
        const dx = p.x - st.x, dy = p.y - st.y, d = hyp(dx, dy);
        if (d < rad) { const k = rad / Math.max(0.1, d); p.x = st.x + dx * k; p.y = st.y + (d < 0.1 ? -this.sgn(p.team) * rad : dy * k); }
      }
      if (st.type === 'penalty') {
        const s = this.sgn(st.team), by = s * (F.L / 2 - F.boxD - 0.5);
        for (const p of this.players) {
          if (!p.active || p.i === st.taker || (p.role === 'GK' && p.team !== st.team)) continue;
          if (s * p.y > s * by) p.y = by;
        }
        const keeper = this.players.find(p => p.team !== st.team && p.role === 'GK' && p.active);
        if (keeper) { keeper.y = s * (F.L / 2 - 0.3); keeper.x = clamp(keeper.x, -F.gw / 2, F.gw / 2); }
      }
      if (!tk || !tk.active) { this.set = null; this.phase = 'play'; return; }
      tk.st = S.LOCK;
      // Bot takers, or humans who wait too long
      const humanT = tk.cid && !tk.afk;
      const wait = st.type === 'kickoff' ? 1.1 : st.type === 'penalty' ? 2.2 : 1.7;
      if ((!humanT && st.t > wait) || (humanT && st.t > (st.type === 'penalty' ? 12 : 9))) {
        if (humanT) { tk.ai.look = this.aimAngle(tk); }
        this.botSetPiece(tk, st);
      }
      if (this.phase === 'set') return;
    }
    // Penalty keeper dives
    for (const p of this.players) {
      if (p.ai.diveAt && this.time >= p.ai.diveAt) { p.ai.diveAt = 0; if (p.st === 0 || p.st === S.LOCK) { p.st = 0; this.dive(p); } }
    }
    // Goal?
    if (b.net) { this.goalScored(b.net === 2 ? 0 : 1); return; }
    // Out of play?
    const R = S.BR;
    if (Math.abs(b.x) > F.W / 2 + R && this.owner < 0 || (this.owner >= 0 && Math.abs(b.x) > F.W / 2 + R)) {
      const last = this.touches[this.touches.length - 1];
      const team = last ? 1 - last.team : 0;
      this.outOfPlay();
      this.startSet('throw', team, Math.sign(b.x) * (F.W / 2 - 0.12), clamp(b.y, -F.L / 2 + 1, F.L / 2 - 1));
      return;
    }
    if (Math.abs(b.y) > F.L / 2 + R) {
      const last = this.touches[this.touches.length - 1];
      const lastTeam = last ? last.team : 0;
      const defending = b.y > 0 ? 1 : 0; // team defending this end
      this.outOfPlay();
      if (lastTeam === defending) this.startSet('corner', 1 - defending, Math.sign(b.x || 1) * (F.W / 2 - 0.4), Math.sign(b.y) * (F.L / 2 - 0.4));
      else this.startSet('goalkick', defending, Math.sign(b.x || 1) * F.sixW * 0.3, Math.sign(b.y) * (F.L / 2 - F.sixD));
      return;
    }
    // Keepers can't hold forever
    if (this.owner >= 0) {
      const o = this.players[this.owner];
      if (o.st === S.HOLD && o.holdT > (o.cid && !o.afk ? 6 : 3.5)) { o.ai.look = Math.atan2(this.sgn(o.team), 0); this.botDistribute(o, true); }
    }
    // Clock
    if (this.half === 1 && this.clock >= 45 && this.phase === 'play') {
      this.phase = 'half'; this.phaseT = 8;
      this.ev({ k: 'whistle', n: 2 });
      this.ev({ k: 'half', sum: this.summary(false) });
      this.resetBall(0, 0, 0);
      this.placeFormation(false);
      return;
    }
    if (this.half === 2 && this.clock >= 90 && this.phase === 'play') {
      if (this.score[0] === this.score[1] && this.golden && !this.extra) {
        this.extra = true;
        this.ev({ k: 'golden' });
      } else if (!this.extra || this.clock >= 90 + 15) {
        this.fullTime();
      }
    }
  }
  outOfPlay() {
    if (this.pendingShot) { this.ev({ k: 'miss', i: this.pendingShot.i }); this.pendingShot = null; }
    this.pendingPass = null;
  }
  goalScored(team) {
    const F = this.F;
    this.score[team]++;
    // Work out scorer and assist
    let scorer = null, og = false, assist = null;
    const ts = this.touches;
    const last = ts[ts.length - 1];
    if (last && last.team === team) scorer = last;
    else {
      // last touch by defender: credit attacker if they shot just before, else own goal
      const prev = [...ts].reverse().find(t => t.team === team);
      if (prev && this.time - prev.t < 2.5 && (prev.kind === 'shot')) scorer = prev;
      else { scorer = last; og = true; }
    }
    if (scorer && !og) {
      for (let k = ts.length - 1; k >= 0; k--) {
        const t = ts[k];
        if (t.team !== team) break;
        if (t.i !== scorer.i && scorer.t - t.t < 14) { assist = t; break; }
      }
    }
    const sp = scorer ? this.players[scorer.i] : null;
    if (sp && !og) {
      sp.stats.g++; sp.stats.sot++; this.tstats[team].sot++;
      if (scorer.kind !== 'shot') { sp.stats.sh++; this.tstats[team].sh++; }
    }
    if (this.pendingShot && this.pendingShot.i !== (sp && sp.i)) { /* deflected */ }
    this.pendingShot = null; this.pendingPass = null;
    const ap = assist ? this.players[assist.i] : null;
    if (ap) ap.stats.a++;
    const min = Math.min(this.half === 1 ? 45 : this.extra ? 120 : 90, Math.floor(this.clock) + 1);
    const g = { team, i: sp ? sp.i : -1, name: sp ? sp.name : '', og, a: ap ? ap.i : -1, an: ap ? ap.name : '', min, extra: this.extra, score: [...this.score] };
    this.goals.push(g);
    this.ev({ k: 'goal', ...g });
    this.phase = 'goal'; this.phaseT = 5;
    this.kickoffTeam = 1 - team;
    this.endAfterGoal = this.extra && this.golden;
    if (this.owner >= 0) { const o = this.players[this.owner]; if (o.st === S.HOLD) o.st = 0; this.owner = -1; }
    if (sp && !og) {
      sp.st = S.CELEB; sp.stT = 2.6;
      const s = this.sgn(team);
      sp.celebTo = { x: Math.sign(sp.x || 1) * (F.W / 2 - 3), y: s * (F.L / 2 - 6) };
      if (Math.abs(sp.x) < 6) sp.celebTo = { x: Math.sign(sp.x || 1) * 10, y: s * (F.L / 2 - 14) };
    }
    for (const p of this.players) { p.buf = null; if (p.st === S.LOCK) p.st = 0; }
  }
  fullTime() {
    this.phase = 'full'; this.phaseT = 22;
    this.ev({ k: 'whistle', n: 3 });
    this.ev({ k: 'full', sum: this.summary(true) });
    for (const p of this.players) if (p.st !== S.CELEB) { p.st = 0; }
    if (this.owner >= 0) { const o = this.players[this.owner]; if (o.st === S.HOLD) o.st = 0; this.owner = -1; }
    this.set = null;
    this.matchNo++;
  }
  startMatch() {
    this.resetStats();
    this.score = [0, 0]; this.clock = 0; this.half = 1; this.extra = false; this.endAfterGoal = false;
    this.touches = []; this.pendingPass = null; this.pendingShot = null;
    this.pickIdents(); this.rosterVer++;
    for (const p of this.players) { p.sta = 100; p.st = 0; p.call = -10; }
    this.kickoffTeam = 0;
    this.ev({ k: 'start' });
    this.startSet('kickoff', 0, 0, 0);
    this.firstMatch = false;
  }
  summary(final) {
    const tot = this.tstats[0].poss + this.tstats[1].poss || 1;
    const res = this.score[0] === this.score[1] ? [0, 0] : this.score[0] > this.score[1] ? [1, -1] : [-1, 1];
    const ratings = this.players.map(p => {
      if (!p.active && !p.stats) return null;
      const s = p.stats || this.blankStats();
      if (s.mins < 1 && !p.active) return null;
      let r = 6.0 + s.g * 1.1 + s.a * 0.75 + s.sot * 0.15 - (s.sh - s.sot) * 0.04 + s.pc * 0.025 - (s.pa - s.pc) * 0.07 + s.tk * 0.2 + s.int * 0.12 + s.sv * 0.4 - s.lost * 0.04 - s.fo * 0.1;
      if (final) r += res[p.team] > 0 ? 0.35 : res[p.team] === 0 ? 0.1 : -0.25;
      const conc = this.score[1 - p.team];
      const cat = ROLE_CAT[p.role];
      if (cat === 'GK') r += conc === 0 ? 0.8 : -conc * 0.2;
      else if (cat === 'DEF') r += conc === 0 ? 0.5 : -conc * 0.08;
      r = Math.round(clamp(r, 3, 10) * 10) / 10;
      return { i: p.i, team: p.team, name: p.name, role: p.role, bot: !p.cid, cid: p.cid, r, ...s, mins: Math.round(s.mins) };
    }).filter(Boolean);
    let motm = null;
    for (const r of ratings) if (!motm || r.r > motm.r || (r.r === motm.r && r.g > motm.g)) motm = r;
    return {
      score: [...this.score], final, extra: this.extra,
      teams: this.tstats.map(t => ({ ...t, possPct: Math.round(t.poss / tot * 100) })),
      goals: this.goals, ratings, motm: motm ? motm.i : -1
    };
  }

  // ===========================================================================
  // Bot brains
  // ===========================================================================
  think() {
    const b = this.ball, F = this.F, P = this.players, now = this.time;
    if (this.phase === 'goal' || this.phase === 'half' || this.phase === 'full') {
      for (const p of P) {
        if (!p.active || p.st === S.CELEB || (p.cid && !p.afk)) continue;
        const w = this.toWorld(p.team, p.ax * 0.9, p.ay * 0.8);
        p.ai.tx = w.x; p.ai.ty = w.y; p.ai.spr = false; p.ai.dir = null; p.ai.look = Math.atan2(b.y - p.y, b.x - p.x);
      }
      return;
    }
    // Predict the loose ball's path
    const path = [];
    if (this.owner < 0) {
      const c = { ...b };
      for (let k = 1; k <= 24; k++) { S.stepBall(c, 0.1, F); path.push({ x: c.x, y: c.y, z: c.z, t: k * 0.1 }); }
    }
    this.path = path;
    const ownerP = this.owner >= 0 ? P[this.owner] : null;
    for (let t = 0; t < 2; t++) {
      const mates = P.filter(p => p.team === t && p.active);
      const bots = mates.filter(p => (!p.cid || p.afk) && p.st !== S.CELEB);
      const opps = P.filter(p => p.team !== t && p.active);
      const mode = ownerP ? (ownerP.team === t ? 'att' : 'def') : 'loose';
      // Who goes for the ball
      let chaser = null, chaser2 = null;
      if (mode !== 'att') {
        const times = mates.filter(p => p.role !== 'GK' || this.inOwnBox(p, 0)).map(p => ({ p, t: this.timeToBall(p, path, ownerP) })).sort((a, c) => a.t - c.t);
        const humBest = times.find(x => x.p.cid && !x.p.afk);
        const botTimes = times.filter(x => !x.p.cid || x.p.afk);
        if (botTimes[0]) {
          const pass = b.passTo >= 0 && P[b.passTo] && P[b.passTo].team === t && now - b.passT < 1.6 && mode === 'loose';
          if (pass) {
            const r = P[b.passTo];
            if (!r.cid || r.afk) chaser = r;
          } else if (!humBest || botTimes[0].t < humBest.t - 0.25 || mode === 'def') {
            chaser = botTimes[0].p;
          }
          if (botTimes[1] && mode === 'def') chaser2 = botTimes[1].p !== chaser ? botTimes[1].p : botTimes[2] && botTimes[2].p;
          if (mode === 'def' && humBest && humBest.t < botTimes[0].t - 0.4 && humBest.p.team === t) { chaser2 = chaser; chaser = null; if (chaser2 === null) chaser2 = botTimes[0].p; }
        }
      }
      const bl = this.local(t, b.x, b.y);
      for (const p of bots) {
        if (p.st !== 0 && p.st !== S.HOLD && p.st !== S.LOCK) continue;
        if (p.st === S.LOCK) { p.ai.tx = p.x; p.ai.ty = p.y; continue; }
        if (p.ai.wall && p.ai.wall > now) { p.ai.tx = p.x; p.ai.ty = p.y; p.ai.dir = null; p.ai.spr = false; continue; }
        if (p.role === 'GK') { this.thinkKeeper(p, path, mode, ownerP); continue; }
        if (this.owner === p.i) { this.thinkOwner(p, mates, opps); continue; }
        p.ai.dir = null;
        p.ai.look = Math.atan2(b.y - p.y, b.x - p.x);
        if (p === chaser) {
          const ip = this.interceptPoint(p, path, ownerP);
          p.ai.tx = ip.x; p.ai.ty = ip.y; p.ai.spr = hyp(ip.x - p.x, ip.y - p.y) > 2.5;
          if (mode === 'def' && ownerP) this.pressAndTackle(p, ownerP);
          if (mode === 'loose' && this.phase !== 'set') this.maybeHeader(p, path);
          continue;
        }
        if (p === chaser2 && ownerP) {
          // Cover: goal side of the ball
          const g = this.ownGoal(t);
          const dx = g.x - ownerP.x, dy = g.y - ownerP.y, d = hyp(dx, dy) || 1;
          const k = Math.min(6, d * 0.4);
          p.ai.tx = ownerP.x + dx / d * k; p.ai.ty = ownerP.y + dy / d * k; p.ai.spr = hyp(p.ai.tx - p.x, p.ai.ty - p.y) > 5;
          if (hyp(ownerP.x - p.x, ownerP.y - p.y) < 1.6) this.pressAndTackle(p, ownerP);
          continue;
        }
        this.position(p, mode, bl, ownerP, mates, opps);
      }
    }
  }
  timeToBall(p, path, ownerP) {
    const sp = p.D.spr * 0.92;
    if (ownerP) return hyp(ownerP.x - p.x, ownerP.y - p.y) / sp;
    const b = this.ball;
    const d0 = hyp(b.x - p.x, b.y - p.y);
    if (d0 < 1) return 0;
    for (const q of path) {
      if (q.z > 2.2) continue;
      if (hyp(q.x - p.x, q.y - p.y) - 0.6 <= sp * q.t + 0.15) return q.t;
    }
    const last = path[path.length - 1] || b;
    return 2.4 + hyp(last.x - p.x, last.y - p.y) / sp;
  }
  interceptPoint(p, path, ownerP) {
    const b = this.ball;
    if (ownerP) {
      // aim slightly ahead of the dribbler, goal side
      const g = this.ownGoal(p.team);
      const ahead = { x: b.x + ownerP.vx * 0.35, y: b.y + ownerP.vy * 0.35 };
      const dx = g.x - ahead.x, dy = g.y - ahead.y, d = hyp(dx, dy) || 1;
      const dd = hyp(ahead.x - p.x, ahead.y - p.y);
      const k = dd > 3 ? 0.8 : 0.2;
      return { x: ahead.x + dx / d * k, y: ahead.y + dy / d * k };
    }
    const sp = p.D.spr * 0.92;
    for (const q of path) {
      if (q.z > 2.2) continue;
      if (hyp(q.x - p.x, q.y - p.y) - 0.6 <= sp * q.t + 0.15) return { x: q.x, y: q.y };
    }
    const last = path[path.length - 1] || b;
    return { x: last.x, y: last.y };
  }
  pressAndTackle(p, o) {
    const d = hyp(this.ball.x - p.x, this.ball.y - p.y);
    if (p.tcd > 0 || o.st === S.HOLD || this.phase !== 'play') return;
    const dd = DIFF[this.diff];
    if (d < 1.5 && Math.random() < dd.tackle) p.acts.push([1, 0]);
    else if (d < 3.2 && d > 1.4 && Math.random() < dd.tackle * 0.25) {
      // Slide if the ball is moving away and we're roughly behind it
      p.ai.look = Math.atan2(this.ball.y + o.vy * 0.25 - p.y, this.ball.x + o.vx * 0.25 - p.x);
      p.acts.push([2, 0]);
    }
  }
  maybeHeader(p, path) {
    const b = this.ball;
    if (b.z < 0.95 || p.buf) return;
    const d = hyp(b.x - p.x, b.y - p.y);
    if (d > 3.5) return;
    const g = this.oppGoal(p.team);
    const dg = hyp(g.x - p.x, g.y - p.y);
    if (dg < this.F.boxD + 4) {
      p.ai.look = Math.atan2(g.y - p.y, (g.x + rnd(-this.F.gw * 0.35, this.F.gw * 0.35)) - p.x);
      p.ai.kx = null;
      p.buf = { act: 2, pow: 0.6, until: this.time + 0.5 };
    } else {
      // Head it forward or away from danger
      p.ai.look = Math.atan2(this.sgn(p.team), rnd(-0.6, 0.6));
      p.buf = { act: 1, pow: 0.5, until: this.time + 0.5 };
    }
  }
  botHeader(p) { return false; }
  position(p, mode, bl, ownerP, mates, opps) {
    const F = this.F, t = p.team, s = this.sgn(t), now = this.time;
    const att = mode === 'att' || (mode === 'loose' && this.touches.length && this.touches[this.touches.length - 1].team === t);
    const shift = att ? clamp(bl.ly * 0.55 + 0.22, -0.2, 0.55) : clamp(bl.ly * 0.5 - 0.06, -0.38, 0.32);
    const spread = att ? 1.12 : 0.82;
    let ly = p.ay * (att ? 1.0 : 0.9) + shift;
    let lx = p.ax * spread + bl.lx * (att ? 0.22 : 0.32);
    const cat = ROLE_CAT[p.role];
    if (att && cat === 'ATT') {
      // Forwards run in behind when a teammate has it in midfield
      if (p.ai.runT > now) ly += 0.16;
      else if (Math.random() < 0.02 && bl.ly > -0.3) p.ai.runT = now + 2.5;
    }
    // Stay roughly onside: not beyond the last defender + 1 m
    const defLine = this.lastDefender(t);
    if (att) ly = Math.min(ly, defLine + 1 / (F.L / 2));
    ly = clamp(ly, -0.92, 0.9);
    lx = clamp(lx, -0.94, 0.94);
    let w = this.toWorld(t, lx, ly);
    if (!att) {
      // Mark the nearest attacker in my zone
      let best = null, bd = 9;
      for (const o of opps) {
        if (o.role === 'GK') continue;
        const d = hyp(o.x - w.x, o.y - w.y);
        if (d < bd) { bd = d; best = o; }
      }
      if (best && (cat === 'DEF' || p.role === 'CDM')) {
        const g = this.ownGoal(t);
        const dx = g.x - best.x, dy = g.y - best.y, d = hyp(dx, dy) || 1;
        const k = 2.8, bx = this.ball.x - best.x, by = this.ball.y - best.y, bd2 = hyp(bx, by) || 1;
        w = { x: best.x + dx / d * k + bx / bd2 * 1.2, y: best.y + dy / d * k + by / bd2 * 1.2 };
      }
    } else if (ownerP && ownerP.team === t) {
      // Offer an angle: drift away from teammates crowding the same space
      for (const m of mates) {
        if (m === p) continue;
        const d = hyp(m.x - w.x, m.y - w.y);
        if (d < 6 && d > 0.01) { w.x -= (m.x - w.x) / d * (6 - d) * 0.5; w.y -= (m.y - w.y) / d * (6 - d) * 0.3; }
      }
    }
    // Throw-ins: two nearest teammates come short to offer
    if (this.phase === 'set' && this.set && this.set.type === 'throw' && this.set.team === t) {
      const st = this.set;
      const near2 = mates.filter(m => m.i !== st.taker && m.role !== 'GK' && (!m.cid || m.afk)).sort((a, c) => hyp(a.x - st.x, a.y - st.y) - hyp(c.x - st.x, c.y - st.y)).slice(0, 2);
      const k = near2.indexOf(p);
      if (k >= 0) {
        const inX = st.x - Math.sign(st.x) * (k === 0 ? 7 : 12);
        w = { x: inX, y: clamp(st.y + (k === 0 ? s * 5 : -s * 4), -F.L / 2 + 3, F.L / 2 - 3) };
      }
    }
    // Corner and wide free kicks: crowd the box
    if (this.phase === 'set' && this.set && (this.set.type === 'corner' || (this.set.type === 'free' && Math.abs(this.set.y) > F.L * 0.25))) {
      const st = this.set, gEnd = Math.sign(st.y) * F.L / 2;
      const attacking = st.team === t;
      if (attacking && cat !== 'DEF' || attacking && p.role === 'CB' && p.slot % 2 === 0) {
        const spots = [[-0.25, 0.35], [0.25, 0.4], [0, 0.6], [-0.4, 0.7], [0.4, 0.75], [0, 0.95]];
        const sp = spots[p.slot % spots.length];
        w = { x: sp[0] * F.boxW, y: gEnd - Math.sign(gEnd) * sp[1] * F.boxD };
      } else if (!attacking && (cat === 'DEF' || cat === 'MID')) {
        const sp = [[-0.2, 0.3], [0.2, 0.3], [0, 0.5], [-0.35, 0.55], [0.35, 0.55], [0, 0.8], [0.15, 0.15]][p.slot % 7];
        w = { x: sp[0] * F.boxW, y: gEnd - Math.sign(gEnd) * sp[1] * F.boxD };
      }
    }
    p.ai.tx = w.x; p.ai.ty = w.y;
    const far = hyp(w.x - p.x, w.y - p.y);
    p.ai.spr = far > 7 || (att && p.ai.runT > now && far > 3);
    void s;
  }
  lastDefender(t) {
    // Returns local y of the opponents' deepest outfield player (in team t's view)
    let m = -1;
    for (const o of this.players) {
      if (!o.active || o.team === t || o.role === 'GK') continue;
      const l = this.local(t, o.x, o.y).ly;
      if (l > m) m = l;
    }
    const bl = this.local(t, this.ball.x, this.ball.y).ly;
    return Math.max(m, bl, 0);
  }
  thinkKeeper(p, path, mode, ownerP) {
    const F = this.F, b = this.ball, s = this.sgn(p.team), gy = -s * F.L / 2, now = this.time;
    if (p.st === S.HOLD) {
      p.ai.tx = p.x; p.ai.ty = p.y + s * 0.5; p.ai.spr = false; p.ai.dir = null;
      if (p.holdT > 1.3) this.botDistribute(p, false);
      return;
    }
    if (this.owner === p.i) { this.thinkOwner(p, this.players.filter(q => q.team === p.team && q.active), this.players.filter(q => q.team !== p.team && q.active)); return; }
    p.ai.look = Math.atan2(b.y - p.y, b.x - p.x);
    // Shot coming?
    if (this.owner < 0 && s * b.vy < -6 && p.st === 0) {
      const ty = p.y;
      const tt = (ty - b.y) / (b.vy || -1e-3);
      if (tt > 0 && tt < 1.2) {
        const px = b.x + b.vx * tt;
        const pz = b.z + b.vz * tt - 0.5 * S.G * tt * tt;
        if (Math.abs(px) < F.gw / 2 + 1.2 && pz < F.gh + 0.6) {
          const dx = px - p.x;
          const react = DIFF[this.diff].react * 0.8;
          if (Math.abs(dx) > 0.6 && now - (b.kickT || 0) > react && tt < 0.42) {
            const err = gauss() * (1.1 - p.attrs.gk * 0.008);
            p.ai.diveX = px + err; p.ai.diveY = p.y; p.ai.diveZ = clamp(pz, 0, 2);
            this.dive(p);
            return;
          }
          // Shuffle across (keepers can't sprint sideways)
          p.ai.tx = p.x + clamp(px - p.x, -0.9, 0.9); p.ai.ty = p.y; p.ai.spr = false; p.ai.shuffle = true;
          return;
        }
      }
    }
    // Loose ball in my box that I can get first: come and claim it
    if (mode === 'loose' && this.inBoxOf(p.team, b.x, b.y)) {
      const mine = this.timeToBall(p, path, null);
      let theirs = 9;
      for (const o of this.players) if (o.active && o.team !== p.team) theirs = Math.min(theirs, this.timeToBall(o, path, null));
      if (mine < theirs + 0.15) { const ip = this.interceptPoint(p, path, null); p.ai.tx = ip.x; p.ai.ty = ip.y; p.ai.spr = true; return; }
    }
    // 1v1: rush out
    if (ownerP && ownerP.team !== p.team && this.inBoxOf(p.team, ownerP.x, ownerP.y)) {
      const d = hyp(ownerP.x - p.x, ownerP.y - p.y);
      const dg = hyp(ownerP.x, ownerP.y - gy);
      if (dg < F.boxD * 0.8) {
        p.ai.tx = ownerP.x * 0.6; p.ai.ty = gy + s * Math.min(dg * 0.45, 5); p.ai.spr = true;
        if (d < 1.6 && p.tcd <= 0 && Math.random() < 0.3) p.acts.push([1, 0]);
        return;
      }
    }
    // Default: on the line between ball and goal centre
    const dx = b.x - 0, dy = b.y - gy, d = hyp(dx, dy) || 1;
    const depth = clamp(d * 0.06, 0.6, d > F.L * 0.5 ? 6 : 2.6);
    p.ai.tx = clamp(dx / d * depth, -F.gw / 2 + 0.3, F.gw / 2 - 0.3);
    p.ai.ty = gy + s * Math.max(0.5, Math.abs(dy / d) * depth);
    p.ai.spr = hyp(p.ai.tx - p.x, p.ai.ty - p.y) > 3;
    p.ai.dir = null;
  }
  botDistribute(p, forced) {
    const mates = this.players.filter(q => q.active && q.team === p.team && q.i !== p.i);
    const opps = this.players.filter(q => q.active && q.team !== p.team);
    let best = null, bs = -1e9;
    for (const m of mates) {
      const d = hyp(m.x - p.x, m.y - p.y);
      if (d > 45) continue;
      let open = 99;
      for (const o of opps) open = Math.min(open, hyp(o.x - m.x, o.y - m.y));
      let lane = 99;
      for (const o of opps) { const r = segDist(o.x, o.y, p.x, p.y, m.x, m.y); if (r.t > 0.05 && r.t < 0.95) lane = Math.min(lane, r.d); }
      const sc = Math.min(open, 10) * 0.3 + Math.min(lane, 5) * 0.4 - d * 0.03 + (m.cid ? 0.8 : 0) + (this.time - m.call < 2 ? 3 : 0);
      if (sc > bs) { bs = sc; best = m; }
    }
    if (!best) { p.ai.kx = p.x; p.ai.ky = p.y + this.sgn(p.team) * 40; p.ai.passTo = null; p.ai.look = Math.atan2(this.sgn(p.team), 0); this.kick(p, 4, 0.8, false); return; }
    const d = hyp(best.x - p.x, best.y - p.y);
    p.ai.passTo = best.i; p.ai.look = Math.atan2(best.y - p.y, best.x - p.x);
    this.kick(p, d > 26 ? 4 : 1, 0.6, false);
    void forced;
  }
  thinkOwner(p, mates, opps) {
    const F = this.F, now = this.time, b = this.ball, dd = DIFF[this.diff];
    const t = p.team, s = this.sgn(t);
    const g = this.oppGoal(t);
    p.ai.held += 0.1;
    // Dribble direction: toward goal, away from pressure
    const loc = this.local(t, p.x, p.y);
    let dx = (g.x - p.x) * 0.25, dy = g.y - p.y;
    const wide = Math.abs(loc.lx) > 0.45 && ['LW', 'RW', 'LM', 'RM', 'LB', 'RB'].includes(p.role);
    if (wide && loc.ly < 0.6) { dx = 0; dy = s; }
    else if (wide) { dx = -Math.sign(p.x) * 0.9; dy = s * 0.45; }
    let dl = hyp(dx, dy) || 1; dx /= dl; dy /= dl;
    let near = 99;
    for (const o of opps) {
      const ox = o.x - p.x, oy = o.y - p.y, d = hyp(ox, oy);
      if (d < near) near = d;
      if (d < 7 && d > 0.01) {
        const ahead = (ox * dx + oy * dy) / d;
        if (ahead > -0.2) { const w = (7 - d) / 7 * 1.3; dx -= ox / d * w; dy -= oy / d * w; }
      }
    }
    // keep inside the pitch
    if (Math.abs(p.x) > F.W / 2 - 3) dx -= Math.sign(p.x) * 1.5;
    if (s * p.y > F.L / 2 - 2) dy -= s * 1.5;
    dl = hyp(dx, dy) || 1;
    p.ai.dir = { x: dx / dl, y: dy / dl };
    p.ai.spr = near > 3.2 && p.sta > 25;
    p.ai.look = Math.atan2(p.ai.dir.y, p.ai.dir.x);
    if (now < p.ai.next) return;
    p.ai.next = now + dd.react * (0.5 + Math.random() * 0.6);
    if (this.phase !== 'play' && this.phase !== 'warmup') return;
    // Options
    const dGoal = hyp(g.x - p.x, g.y - p.y);
    const range = F.L * (0.19 + p.attrs.sho * 0.0007);
    const lp0 = this.local(t, p.x, p.y);
    // Space ahead in the dribbling direction
    let space = 20;
    for (const o of opps) {
      const ox = o.x - p.x, oy = o.y - p.y, d = hyp(ox, oy);
      if (d < 0.01) continue;
      const fwd = (ox * p.ai.dir.x + oy * p.ai.dir.y) / d;
      if (fwd > 0.55) space = Math.min(space, d);
    }
    const cat = ROLE_CAT[p.role];
    let bestScore = 0.35 + Math.min(space, 12) * 0.06 - (near < 1.6 ? 0.55 : 0) - Math.max(0, p.ai.held - 2.5) * 0.4
      + (cat === 'ATT' ? 0.15 : cat === 'DEF' ? -0.25 : 0) + (lp0.ly > 0.3 && lp0.ly < 0.62 && space > 4 ? 0.35 : 0);
    let choice = null;
    if (dGoal < range && s * (g.y - p.y) > 2) {
      const angleW = Math.abs(Math.atan2(F.gw / 2 - p.x, Math.abs(g.y - p.y)) - Math.atan2(-F.gw / 2 - p.x, Math.abs(g.y - p.y)));
      let blockers = 0;
      for (const o of opps) { const r = segDist(o.x, o.y, p.x, p.y, g.x, g.y); if (r.d < 1.2 && r.t > 0.05 && r.t < 0.97 && o.role !== 'GK') blockers++; }
      const q = 0.3 + (1 - dGoal / range) * 1.6 + angleW * 1.2 - blockers * 0.35 + (this.inBoxOf(1 - t, p.x, p.y) ? 0.4 : 0) + gauss() * dd.noise * 0.3;
      if (q > bestScore || (q > 1.4 && Math.random() < 0.75)) {
        bestScore = Math.max(q, bestScore) + 5;
        // Aim away from the keeper
        const k = this.players.find(o => o.team !== t && o.role === 'GK' && o.active);
        let side = Math.random() < 0.5 ? -1 : 1;
        if (k) side = k.x > 0 ? -1 : 1;
        if (Math.random() < 0.25) side = -side;
        choice = { act: 2, kx: side * (F.gw / 2 - rnd(0.35, 1.2)), ky: g.y, kh: rnd(0.2, 1.9), pow: clamp(0.45 + dGoal / range * 0.4 + rnd(-0.1, 0.1), 0.35, 0.92) };
      }
    }
    for (const m of mates) {
      if (m.role === 'GK' && lp0.ly > -0.4) continue;
      const d = hyp(m.x - p.x, m.y - p.y);
      if (d < 4 || d > 42) continue;
      let open = 99, lane = 99;
      for (const o of opps) {
        open = Math.min(open, hyp(o.x - m.x, o.y - m.y));
        const r = segDist(o.x, o.y, p.x, p.y, m.x + m.vx * 0.5, m.y + m.vy * 0.5);
        if (r.t > 0.08) lane = Math.min(lane, r.d - r.t * d * 0.045);
      }
      if (lane < 1.2) continue;
      const prog = s * (m.y - p.y);
      const human = m.cid && !m.afk;
      const called = human && now - m.call < 2;
      let sc = 0.15 + prog * 0.035 + Math.min(open, 8) * 0.05 + Math.min(lane, 4) * 0.08 - d * 0.006 + (human ? 0.3 : 0) + (called ? 2.2 : 0) - (open < 2 ? 0.4 : 0)
        + (this.inBoxOf(1 - t, m.x, m.y) && open > 2.5 ? 0.45 : 0);
      if (prog < -3 && near > 2.5) sc -= 0.25;
      if (lp0.ly > 0.4 && prog < 2 && !this.inBoxOf(1 - t, m.x, m.y)) sc -= 0.3;
      if (near < 2.2) sc += 0.35;
      sc += gauss() * dd.noise * 0.3;
      if (sc > bestScore) {
        bestScore = sc;
        const mloc = this.local(t, m.x, m.y);
        const lob = d > 30 || (wide && mloc.ly > 0.6 && Math.abs(mloc.lx) < 0.4 && lp0.ly > 0.6);
        // Through ball for runners
        const runner = ROLE_CAT[m.role] === 'ATT' && s * m.vy > 3 && mloc.ly > lp0.ly - 0.1;
        choice = { act: lob ? 4 : runner && Math.random() < 0.6 ? 3 : 1, passTo: m.i, pow: 0.5, lead: 5 + Math.random() * 3 };
      }
    }
    // Cross from wide areas near the byline
    const lp = this.local(t, p.x, p.y);
    if (wide && lp.ly > 0.6) {
      const inBox = mates.filter(m => this.inBoxOf(1 - t, m.x, m.y) && m !== p);
      if (inBox.length) {
        const tgt = pick(inBox);
        const sc = 1.3 + (lp.ly - 0.6) * 4 + rnd(-0.2, 0.2);
        if (sc > bestScore) { bestScore = sc; choice = { act: 4, kx: tgt.x + rnd(-1.5, 1.5), ky: tgt.y + rnd(-1, 1.5), pow: 0.6 }; }
      }
    }
    // Clear danger
    if (ROLE_CAT[p.role] === 'DEF' && lp.ly < -0.55 && near < 2.5 && (!choice || bestScore < 0.6)) {
      choice = { act: 4, kx: clamp(p.x + rnd(-15, 15), -F.W / 2 + 3, F.W / 2 - 3), ky: p.y + s * rnd(30, 45), pow: 0.8 };
    }
    if (p.ai.held > 5 && !choice) {
      const m = mates.filter(q => q.role !== 'GK' && q !== p).sort((a, c) => hyp(a.x - p.x, a.y - p.y) - hyp(c.x - p.x, c.y - p.y))[0];
      if (m) choice = { act: 1, passTo: m.i, pow: 0.5 };
    }
    if (!choice) return;
    p.ai.passTo = choice.passTo != null ? choice.passTo : null;
    p.ai.kx = choice.kx != null ? choice.kx : null; p.ai.ky = choice.ky != null ? choice.ky : null; p.ai.kh = choice.kh != null ? choice.kh : null;
    p.ai.lead = choice.lead;
    if (choice.passTo != null) { const m = this.players[choice.passTo]; p.ai.look = Math.atan2(m.y - p.y, m.x - p.x); }
    else if (choice.kx != null) p.ai.look = Math.atan2(choice.ky - p.y, choice.kx - p.x);
    this.kick(p, choice.act, choice.pow, false);
  }
  botSetPiece(p, st) {
    const F = this.F, s = this.sgn(p.team), now = this.time;
    const mates = this.players.filter(q => q.active && q.team === p.team && q.i !== p.i);
    const opps = this.players.filter(q => q.active && q.team !== p.team);
    const g = this.oppGoal(p.team);
    const openness = m => { let o = 99; for (const q of opps) o = Math.min(o, hyp(q.x - m.x, q.y - m.y)); return o; };
    let act = 1, pow = 0.5;
    p.ai.passTo = null; p.ai.kx = null; p.ai.ky = null; p.ai.kh = null;
    if (st.type === 'penalty') {
      const side = Math.random() < 0.5 ? -1 : 1;
      p.ai.kx = side * (F.gw / 2 - rnd(0.4, 1.0)); p.ai.ky = g.y; p.ai.kh = rnd(0.2, 1.6);
      p.ai.look = Math.atan2(g.y - p.y, p.ai.kx - p.x);
      act = 2; pow = rnd(0.5, 0.75);
    } else if (st.type === 'corner') {
      const inBox = mates.filter(m => this.inBoxOf(1 - p.team, m.x, m.y));
      if (inBox.length && Math.random() < 0.8) {
        const tgt = inBox.sort((a, c) => openness(c) - openness(a))[0];
        p.ai.kx = tgt.x; p.ai.ky = tgt.y; act = 4;
      } else {
        const m = mates.sort((a, c) => hyp(a.x - p.x, a.y - p.y) - hyp(c.x - p.x, c.y - p.y))[0];
        if (m) p.ai.passTo = m.i;
      }
    } else if (st.type === 'free' && hyp(g.x - st.x, g.y - st.y) < F.L * 0.27 && Math.random() < 0.6) {
      const side = Math.random() < 0.5 ? -1 : 1;
      p.ai.kx = side * (F.gw / 2 - rnd(0.4, 1.0)); p.ai.ky = g.y; p.ai.kh = rnd(1.2, 2.1);
      p.ai.look = Math.atan2(g.y - p.y, p.ai.kx - p.x);
      act = 2; pow = rnd(0.55, 0.8);
    } else {
      // Pick the most open teammate, prefer short for kick-offs and throw-ins
      let best = null, bs = -1e9;
      for (const m of mates) {
        if (m.role === 'GK' && st.type !== 'goalkick') continue;
        const d = hyp(m.x - p.x, m.y - p.y);
        const maxD = st.type === 'throw' ? 18 : st.type === 'kickoff' ? 20 : 45;
        if (d < 3 || d > maxD) continue;
        const humanCalled = m.cid && now - m.call < 3;
        const sc = Math.min(openness(m), 9) * 0.3 - d * 0.03 + (m.cid ? 0.6 : 0) + (humanCalled ? 3 : 0) + s * (m.y - p.y) * 0.01;
        if (sc > bs) { bs = sc; best = m; }
      }
      if (best) {
        p.ai.passTo = best.i;
        const d = hyp(best.x - p.x, best.y - p.y);
        act = st.type === 'goalkick' && d > 28 ? 4 : st.type === 'throw' && d > 12 ? 4 : 1;
      } else if (st.type === 'throw') {
        p.ai.kx = p.x - Math.sign(p.x) * rnd(8, 14); p.ai.ky = p.y + s * rnd(4, 12); act = 4;
      } else {
        p.ai.kx = clamp(p.x + rnd(-8, 8), -F.W / 2 + 4, F.W / 2 - 4); p.ai.ky = p.y + s * 25; act = 4;
      }
    }
    if (p.ai.passTo != null) { const m = this.players[p.ai.passTo]; p.ai.look = Math.atan2(m.y - p.y, m.x - p.x); }
    else if (p.ai.kx != null) p.ai.look = Math.atan2(p.ai.ky - p.y, p.ai.kx - p.x);
    p.face = p.ai.look;
    if (p.cid && !p.afk) {
      // Human ran out of time: hand it to the bot logic but aim where they were aiming
      p.ai.look = this.aimAngle(p);
      if (p.ai.passTo == null && p.ai.kx == null) { p.ai.kx = p.inp.ax; p.ai.ky = p.inp.ay; }
      const wasHuman = p.cid; p.cid = 0;
      this.takeSet(p, act, pow);
      p.cid = wasHuman;
      return;
    }
    this.takeSet(p, act, pow);
  }
  // Turns AI targets into movement input
  steer(p) {
    const ai = p.ai;
    if (p.st === S.LOCK) { p.inp.mx = 0; p.inp.my = 0; return; }
    if (ai.dir) {
      p.inp.mx = ai.dir.x; p.inp.my = ai.dir.y; p.inp.spr = ai.spr ? 1 : 0;
      return;
    }
    const dx = ai.tx - p.x, dy = ai.ty - p.y, d = hyp(dx, dy);
    if (d < 0.35) { p.inp.mx = 0; p.inp.my = 0; p.inp.spr = 0; }
    else { const m = Math.min(ai.shuffle ? 0.55 : 1, d / 2.2); p.inp.mx = dx / d * m; p.inp.my = dy / d * m; p.inp.spr = ai.spr ? 1 : 0; }
    ai.shuffle = false;
  }

  // ---- networking ---------------------------------------------------------------
  snapshot() {
    const b = this.ball;
    const parts = [this.tick, PH[this.phase], r2(this.clock), this.score[0], this.score[1], this.owner, this.set ? this.set.taker : -1, r1(Math.max(0, this.phaseT)), this.extra ? 1 : 0,
      r2(b.x), r2(b.y), r2(b.z), r1(b.vx), r1(b.vy), r1(b.vz), r2(b.sp || 0)];
    for (const p of this.players) {
      if (!p.active) { parts.push(0, 0, 0, 0, 0, -1); continue; }
      const spr = p.inp.spr && hyp(p.vx, p.vy) > p.D.jog * 0.9 ? 1 : 0;
      parts.push(r2(p.x), r2(p.y), r1(p.vx), r1(p.vy), r2(p.face), p.st * 2 + spr);
    }
    return parts.join(',');
  }
  broadcast() {
    if (!this.members.size) { this.evq = []; return; }
    const common = this.snapshot();
    const evs = this.evq.length ? JSON.stringify({ t: 'ev', e: this.evq }) : null;
    this.evq = [];
    for (const c of this.members.values()) {
      if (c.ws.readyState !== 1) continue;
      if (c.rosterVer !== this.rosterVer) { c.rosterVer = this.rosterVer; send(c.ws, this.rosterMsg(c)); }
      if (evs) c.ws.send(evs);
      const p = c.slot >= 0 ? this.players[c.slot] : null;
      const mine = p ? [p.ack, r1(p.sta), r2(Math.max(0, p.stT))] : [0, 0, 0];
      if (c.ws.bufferedAmount < 256 * 1024) c.ws.send('["s",' + mine.join(',') + ',' + common + ']');
    }
  }
}

function ovr(a, role) {
  if (!a) return 50;
  const w = {
    GK: { gk: 0.85, pas: 0.05, phy: 0.1 },
    CB: { def: 0.45, phy: 0.25, pac: 0.12, pas: 0.12, dri: 0.06 },
    LB: { def: 0.32, pac: 0.28, pas: 0.18, dri: 0.12, phy: 0.1 },
    RB: { def: 0.32, pac: 0.28, pas: 0.18, dri: 0.12, phy: 0.1 },
    CDM: { def: 0.34, pas: 0.26, phy: 0.2, dri: 0.1, pac: 0.1 },
    CM: { pas: 0.34, dri: 0.22, def: 0.14, phy: 0.12, sho: 0.1, pac: 0.08 },
    CAM: { pas: 0.32, dri: 0.3, sho: 0.22, pac: 0.12, phy: 0.04 },
    LM: { pac: 0.26, dri: 0.28, pas: 0.26, sho: 0.14, phy: 0.06 },
    RM: { pac: 0.26, dri: 0.28, pas: 0.26, sho: 0.14, phy: 0.06 },
    LW: { pac: 0.3, dri: 0.32, sho: 0.2, pas: 0.14, phy: 0.04 },
    RW: { pac: 0.3, dri: 0.32, sho: 0.2, pas: 0.14, phy: 0.04 },
    ST: { sho: 0.42, pac: 0.22, dri: 0.16, phy: 0.14, pas: 0.06 }
  }[role] || { pac: 1 / 6, sho: 1 / 6, pas: 1 / 6, dri: 1 / 6, def: 1 / 6, phy: 1 / 6 };
  let s = 0;
  for (const k in w) s += (a[k] || 50) * w[k];
  return Math.round(s);
}

// ===========================================================================
// HTTP: serves the game page, the shared physics and three.js
// ===========================================================================
const files = {};
function loadFile(name, candidates, type, cache) {
  for (const f of candidates) {
    try {
      const data = fs.readFileSync(f);
      files[name] = { data, gz: zlib.gzipSync(data), type, cache, mtime: fs.statSync(f).mtimeMs, path: f };
      return true;
    } catch (e) { /* try next */ }
  }
  return false;
}
function indexFile() {
  const cands = [path.join(__dirname, 'public', 'index.html'), path.join(__dirname, 'index.html')];
  const cur = files['/'];
  if (cur) { try { if (fs.statSync(cur.path).mtimeMs === cur.mtime) return cur; } catch (e) { /* reload */ } }
  loadFile('/', cands, 'text/html; charset=utf-8', 'no-cache');
  return files['/'];
}
loadFile('/three.js', [path.join(__dirname, 'node_modules', 'three', 'build', 'three.module.min.js')], 'text/javascript; charset=utf-8', 'public, max-age=604800');
{
  const data = Buffer.from(SHARED_JS);
  files['/shared.js'] = { data, gz: zlib.gzipSync(data), type: 'text/javascript; charset=utf-8', cache: 'no-cache' };
}

const server = http.createServer((req, res) => {
  const url = (req.url || '/').split('?')[0];
  if (url === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); res.end('ok'); return; }
  let f = null;
  if (url === '/' || url === '/index.html') f = indexFile();
  else if (url === '/three.js' || url === '/shared.js') f = files[url];
  if (!f) {
    res.writeHead(url === '/' ? 500 : 404, { 'Content-Type': 'text/plain' });
    res.end(url === '/' ? 'Game file missing: upload index.html into the public folder' : 'Not found');
    return;
  }
  const gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  res.writeHead(200, { 'Content-Type': f.type, 'Cache-Control': f.cache, ...(gz ? { 'Content-Encoding': 'gzip' } : {}), 'Vary': 'Accept-Encoding' });
  res.end(gz ? f.gz : f.data);
});

// ===========================================================================
// WebSocket lobby and match traffic
// ===========================================================================
const wss = new WebSocketServer({ server, path: '/ws', maxPayload: 16 * 1024 });
function send(ws, obj) { if (ws.readyState === 1) ws.send(JSON.stringify(obj)); }
function roomList() {
  const list = [];
  for (const r of rooms.values()) if (r.pub) list.push(r.listing());
  list.sort((a, b) => b.humans - a.humans);
  return list;
}
function sendJoined(c, r) {
  send(c.ws, r.infoMsg());
  c.rosterVer = r.rosterVer;
  send(c.ws, r.rosterMsg(c));
}
function createRoom(c, opts) {
  if (rooms.size >= 40) { send(c.ws, { t: 'error', m: 'The server is full right now. Try joining a match instead.' }); return null; }
  const r = new Room(opts || {}, c);
  rooms.set(r.code, r);
  return r;
}
function joinRoom(c, r) {
  if (c.room) leaveRoom(c);
  const err = r.addClient(c);
  if (err) { send(c.ws, { t: 'error', m: err === 'full' ? 'That match is full.' : 'Could not join that match.' }); return; }
  sendJoined(c, r);
}
function leaveRoom(c) {
  if (!c.room) return;
  c.room.removeClient(c);
}
function clubOnline(clubId) {
  const out = [];
  for (const c of clients.values()) if (c.profile && c.profile.club && c.profile.club.id === clubId) out.push({ name: c.profile.name, pos: c.profile.pos, room: c.room ? c.room.name : null, code: c.room && c.room.pub ? c.room.code : null });
  return out;
}
const clubCache = new Map();

wss.on('connection', ws => {
  const c = { id: nextClientId++, ws, profile: cleanProfile({}), room: null, slot: -1, rosterVer: -1, joinedAt: Date.now(), msgs: 0, msgT: Date.now() };
  clients.set(c.id, c);
  ws.isAlive = true;
  ws.on('pong', () => { ws.isAlive = true; });
  ws.on('message', raw => {
    const now = Date.now();
    if (now - c.msgT > 1000) { c.msgT = now; c.msgs = 0; }
    if (++c.msgs > 200) return;
    let m;
    try { m = JSON.parse(raw); } catch (e) { return; }
    if (Array.isArray(m)) {
      if (m[0] === 'i' && c.room && c.slot >= 0) {
        const p = c.room.players[c.slot];
        if (!p || p.cid !== c.id) return;
        const x = [m[1] | 0, m[2] | 0, m[3] | 0, m[4] ? 1 : 0, m[5] | 0, m[6] | 0, (m[7] | 0) >= 1 && (m[7] | 0) <= 6 ? m[7] | 0 : 0, clamp(m[8] | 0, 0, 100)];
        if (p.q.length < 40) p.q.push(x);
      } else if (m[0] === 'ping') {
        ws.send(JSON.stringify(['pong', m[1]]));
      }
      return;
    }
    if (!m || typeof m !== 'object') return;
    switch (m.t) {
      case 'hello': {
        c.profile = cleanProfile(m.profile);
        const cl = c.profile.club;
        if (cl) {
          const known = clubCache.get(cl.id);
          if (known && known.ver > cl.ver) send(ws, { t: 'clubUpdate', club: known });
          else clubCache.set(cl.id, cl);
        }
        send(ws, { t: 'hello', id: c.id, online: clients.size });
        if (c.room) {
          const p = c.room.players.find(q => q.cid === c.id);
          if (p && c.room.phase === 'warmup') { c.room.takeSlot(c, p); c.room.rosterVer++; }
        }
        break;
      }
      case 'list': send(ws, { t: 'rooms', rooms: roomList(), online: clients.size }); break;
      case 'quick': {
        const opts = [...rooms.values()].filter(r => r.pub && r.members.size < r.size * 2 && r.phase !== 'full').sort((a, b) => b.members.size - a.members.size);
        let r = opts[0];
        if (!r) r = createRoom(c, { name: 'Quick match', pub: true, size: 11, len: 6, diff: 2, bots: true, golden: true, warm: 15, quick: true });
        if (r) joinRoom(c, r);
        break;
      }
      case 'create': {
        const r = createRoom(c, m.opts || {});
        if (r) joinRoom(c, r);
        break;
      }
      case 'join': {
        const code = cleanText(m.code, 8).toUpperCase();
        const r = rooms.get(code);
        if (!r) { send(ws, { t: 'error', m: 'No match with code ' + code + '. It may have ended.' }); break; }
        joinRoom(c, r);
        break;
      }
      case 'leave': leaveRoom(c); send(ws, { t: 'left' }); break;
      case 'slot': {
        const r = c.room;
        if (!r) break;
        const p = r.players[m.i | 0];
        if (!p || p.cid) break;
        r.takeSlot(c, p);
        if (r.phase === 'warmup' || r.phase === 'full') { const w = r.toWorld(p.team, p.ax * 0.9, p.ay * 0.8); p.x = w.x; p.y = w.y; p.vx = 0; p.vy = 0; }
        break;
      }
      case 'afk': {
        const r = c.room;
        if (!r || c.slot < 0) break;
        const p = r.players[c.slot];
        if (p && p.cid === c.id) { p.afk = !!m.on; p.q = []; p.inp.mx = 0; p.inp.my = 0; p.inp.spr = 0; }
        break;
      }
      case 'start': {
        const r = c.room;
        if (r && r.hostId === c.id && r.phase === 'warmup') r.phaseT = 0;
        break;
      }
      case 'chat': {
        const r = c.room;
        if (!r) break;
        const id = m.m | 0;
        if (id >= 0 && id < 8 && c.slot >= 0) r.ev({ k: 'chat', i: c.slot, m: id });
        break;
      }
      case 'club': {
        const cl = cleanClub(m.club);
        if (!cl) break;
        if (m.update) { clubCache.set(cl.id, cl); for (const o of clients.values()) if (o !== c && o.profile.club && o.profile.club.id === cl.id) { o.profile.club = cl; send(o.ws, { t: 'clubUpdate', club: cl }); } }
        send(ws, { t: 'clubOnline', id: cl.id, list: clubOnline(cl.id) });
        break;
      }
    }
  });
  ws.on('close', () => { leaveRoom(c); clients.delete(c.id); });
  ws.on('error', () => {});
});

// Drop connections that stop answering
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    try { ws.ping(); } catch (e) { /* ignore */ }
  }
}, 25000);

// ===========================================================================
// Game loop: 30 ticks a second for every room
// ===========================================================================
let last = process.hrtime.bigint(), acc = 0;
setInterval(() => {
  const now = process.hrtime.bigint();
  acc += Number(now - last) / 1e9;
  last = now;
  if (acc > 0.25) acc = 0.25;
  let steps = 0;
  while (acc >= S.DT && steps < 5) {
    acc -= S.DT; steps++;
    for (const r of rooms.values()) {
      try { r.step(); } catch (e) { console.error('Room ' + r.code + ' error:', e); }
    }
  }
  if (steps) for (const r of rooms.values()) { try { r.broadcast(); } catch (e) { console.error(e); } }
  // Close rooms nobody is in
  const t = Date.now();
  for (const [code, r] of rooms) if (!r.members.size && r.emptySince && t - r.emptySince > 20000) rooms.delete(code);
}, 1000 / 60);

if (require.main === module) {
  server.listen(PORT, () => console.log('Golden Goal running on port ' + PORT));
}
module.exports = { SHARED, Room, rooms, server, S, cleanProfile, ovr };
