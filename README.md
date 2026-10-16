# Golden Goal

Online club football for you and the boys. Make a pro, start a club, and play full matches (5v5, 7v7 or 11v11) with bots filling every empty spot.

## Put it online (same as Rooftop Rumble)

### 1. GitHub
1. Make a new repository called `golden-goal` (Public).
2. Click **uploading an existing file**.
3. Unzip `golden-goal.zip`, open the folder, and drag in everything inside it: `package.json`, `server.js`, `README.md` and the `public` folder.
4. Check that `public/index.html` shows with `public/` in front of it. If the folder won't drag in, drag `index.html` in by itself; the game works either way.
5. Click **Commit changes**.

### 2. Render
1. Click **New**, then **Web Service**, and pick the `golden-goal` repo.
2. Settings:
   - **Language:** Node
   - **Build command:** `npm install` (this matters: it downloads the 3D engine)
   - **Start command:** `npm start`
   - **Instance type:** Free
   - **Region:** Singapore
3. Click **Create Web Service** and wait until it says **Live**.

### 3. Play
1. Open your Render link and create your pro.
2. **My club** → Create a club → **Copy club invite link** → send it to the boys so you share the badge and kit.
3. **Create a match** (or **Play now**) → **Copy invite link** → send it. They land straight in your match.
4. Pick positions in the warm-up, then the host hits **Start now**.

## Controls
| Key | Action |
| --- | --- |
| W A S D / arrows | Move |
| Shift | Sprint |
| Mouse | Aim passes and shots |
| Left click | Pass to the mate you aim at · standing tackle |
| Right click (hold) | Shoot with power · slide tackle · keeper dive |
| E | Through ball |
| Q | Lob, cross or long ball |
| Space | Knock the ball ahead |
| F | Call for the ball (bots pass to you) |
| 1–8 | Quick chat |
| C | Switch camera |
| M | Change position |
| Esc | Pause (a bot plays for you) |

## Good to know
- **First load can be slow.** The free server sleeps after 15 minutes with nobody on it and takes up to a minute to wake.
- **Your pro, level, XP and club are saved in your browser.** Same browser, same pro.
- **Updating:** upload the new `server.js` to the main folder and the new `index.html` into `public`. Render redeploys by itself, then everyone refreshes.
- **Best on a computer** with a keyboard and mouse.
