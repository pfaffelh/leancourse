#!/usr/bin/env bash
# Open a deck for recording: slides in a bare Chrome window (no tabs,
# no address bar) at a fixed size in the bottom left corner, so OBS can
# capture exactly that window. Bottom rather than top keeps it clear of
# GNOME's notification banners, which drop in from the top. Press `s`
# in it for the speaker view, which opens as a second window that OBS
# does not see.
#
#   scripts/lecture_slides.sh 1-1-nat          deck by its URL name
#   scripts/lecture_slides.sh 1-1-nat 1600x900 other window size
#
# Needs the decks built:  lake exe slides _out/html-multi/slides
# The decks are served over http rather than opened as file://, because
# the speaker view talks to the slide window with postMessage.
# A separate Chrome profile makes --app and --window-size take effect
# even when Chrome is already running on the desktop.
set -euo pipefail

cd "$(dirname "$0")/.."
deck=${1:?usage: $0 <deck> [WIDTHxHEIGHT]}
size=${2:-1920x1080}
root=_out/html-multi
port=8897

[ -f "$root/slides/$deck/index.html" ] \
  || { echo "No deck $root/slides/$deck -- run lake exe slides first." >&2; exit 1; }

chrome=$(command -v google-chrome || command -v chromium || command -v chromium-browser) \
  || { echo "No Chrome or Chromium found." >&2; exit 1; }

profile="${XDG_CACHE_HOME:-$HOME/.cache}/leancourse-lecture-chrome"
mkdir -p "$profile"

python3 -m http.server "$port" --directory "$root" >/dev/null 2>&1 &
server=$!
trap 'kill $server 2>/dev/null' EXIT
for _ in $(seq 20); do
  curl -sf -o /dev/null "http://localhost:$port/" && break
  sleep 0.5
done

screen_h=$(xwininfo -root | awk '/^  Height:/{print $2}')
# --window-position places the content, not the title bar (measured on
# GNOME), so this puts the content's lower edge on the screen's.
y=$(( screen_h - ${size#*x} ))

echo "Slides: http://localhost:$port/slides/$deck/  (close the window to stop)"
"$chrome" --user-data-dir="$profile" --no-first-run --no-default-browser-check \
  --app="http://localhost:$port/slides/$deck/" \
  --window-position=0,$y --window-size="${size/x/,}" >/dev/null 2>&1
