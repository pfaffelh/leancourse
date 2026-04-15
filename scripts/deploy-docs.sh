#!/usr/bin/env bash
# Rebuild the Verso manual and publish docs/ for GitHub Pages.
# Pages serves pfaffelh.github.io/leancourse from main:/docs.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

echo "==> lake build"
lake build

echo "==> lake exe leancourse --output _out/"
lake exe leancourse --output _out/

echo "==> refreshing docs/ from _out/html-multi"
rm -rf docs
cp -r _out/html-multi docs

if git diff --quiet --cached docs && git diff --quiet docs; then
  echo "==> docs/ unchanged; nothing to push"
  exit 0
fi

git add docs
msg="${1:-Rebuild docs}"
git commit -m "$msg"
git push origin "$(git rev-parse --abbrev-ref HEAD)"
echo "==> pushed. Pages will refresh in ~1 minute."
