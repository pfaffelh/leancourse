#!/usr/bin/env bash
# Export the slide decks as PDF, one file per deck, into _slides/pdf/.
#
#   scripts/slides_pdf.sh              all decks
#   scripts/slides_pdf.sh 1-1-nat      one deck, by its URL name
#
# Needs the decks built:  lake build slides && lake exe slides _out/html-multi/slides
# Uses reveal.js print-pdf mode and Chrome's headless printer. The old
# headless mode is required: the new one prints before reveal has laid
# the slides out and yields a single blank page.
set -euo pipefail

cd "$(dirname "$0")/.."
root=_out/html-multi
out=_slides/pdf
port=8899

[ -d "$root/slides" ] || { echo "No decks in $root/slides -- run lake exe slides first." >&2; exit 1; }

chrome=$(command -v google-chrome || command -v chromium || command -v chromium-browser) \
  || { echo "No Chrome or Chromium found." >&2; exit 1; }

mkdir -p "$out"
python3 -m http.server "$port" --directory "$root" >/dev/null 2>&1 &
server=$!
trap 'kill $server 2>/dev/null' EXIT
sleep 1

decks=("$@")
if [ ${#decks[@]} -eq 0 ]; then
  decks=()
  for d in "$root"/slides/*/; do decks+=("$(basename "$d")"); done
fi

for deck in "${decks[@]}"; do
  [ -f "$root/slides/$deck/index.html" ] || { echo "skip $deck -- not built"; continue; }
  "$chrome" --headless=old --disable-gpu --no-sandbox --no-pdf-header-footer \
    --run-all-compositor-stages-before-draw --virtual-time-budget=60000 \
    --print-to-pdf="$out/$deck.pdf" \
    "http://localhost:$port/slides/$deck/?print-pdf" >/dev/null 2>&1
  pages=$(pdfinfo "$out/$deck.pdf" 2>/dev/null | awk '/^Pages:/{print $2}')
  echo "$out/$deck.pdf  (${pages:-?} pages)"
done
