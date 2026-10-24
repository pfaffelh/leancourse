#!/usr/bin/env bash
# Export the slide decks as PDF, one file per deck, into _slides/pdf/.
#
#   scripts/slides_pdf.sh              all decks
#   scripts/slides_pdf.sh 1-1-nat      one deck, by its URL name
#
# Needs the decks built:  lake build slides && lake exe slides _out/html-multi/slides
# Uses reveal.js print-pdf mode and Chrome's headless printer. The old
# headless mode is required: the new one prints before reveal has laid
# the slides out and yields a single blank page. Each run gets its own
# --user-data-dir, otherwise a Chrome already running on the desktop
# takes over the request and the PDF comes out blank as well.
set -euo pipefail

cd "$(dirname "$0")/.."
root=_out/html-multi
out=_slides/pdf
port=8899

[ -d "$root/slides" ] || { echo "No decks in $root/slides -- run lake exe slides first." >&2; exit 1; }

chrome=$(command -v google-chrome || command -v chromium || command -v chromium-browser) \
  || { echo "No Chrome or Chromium found." >&2; exit 1; }

mkdir -p "$out"
profile=$(mktemp -d)
python3 -m http.server "$port" --directory "$root" >/dev/null 2>&1 &
server=$!
trap 'kill $server 2>/dev/null; rm -rf "$profile"' EXIT
for _ in $(seq 20); do
  curl -sf -o /dev/null "http://localhost:$port/" && break
  sleep 0.5
done

status=0
decks=("$@")
if [ ${#decks[@]} -eq 0 ]; then
  decks=()
  for d in "$root"/slides/*/; do decks+=("$(basename "$d")"); done
fi

for deck in "${decks[@]}"; do
  [ -f "$root/slides/$deck/index.html" ] || { echo "skip $deck -- not built"; continue; }
  # Chrome occasionally prints before reveal has split the deck into
  # pages and returns a single blank one. Retry in that case.
  for attempt in 1 2 3; do
    rm -rf "$profile/$deck"
    "$chrome" --headless=old --disable-gpu --no-sandbox --no-pdf-header-footer \
      --user-data-dir="$profile/$deck" \
      --run-all-compositor-stages-before-draw --virtual-time-budget=60000 \
      --print-to-pdf="$out/$deck.pdf" \
      "http://localhost:$port/slides/$deck/?print-pdf" >/dev/null 2>&1
    pages=$(pdfinfo "$out/$deck.pdf" 2>/dev/null | awk '/^Pages:/{print $2}')
    [ "${pages:-0}" -gt 1 ] && break
  done
  if [ "${pages:-0}" -le 1 ]; then
    echo "$out/$deck.pdf  FAILED after 3 attempts (${pages:-?} pages)" >&2
    status=1
  else
    echo "$out/$deck.pdf  ($pages pages)"
  fi
done

exit $status
