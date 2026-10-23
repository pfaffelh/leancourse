#!/usr/bin/env bash
#
# Verify that every solvability witness in Leancourse/Checks/ still
# compiles with no errors and no `sorry`.
#
# Usage:
#   scripts/check_solvable.sh [FILE_OR_DIR ...]
#
# With no argument, the whole Leancourse/Checks/ tree is checked.
# Arguments may be files or directories (relative to the repository
# root or absolute), e.g.
#
#   scripts/check_solvable.sh Leancourse/Checks/0-Logic
#
# Unlike the pre-export check in export_exercises.sh, a `sorry`
# warning is a FAILURE here: the point of a witness is that the
# exercise can be finished.
#
# Exit status: 0 if every file passes, 1 otherwise.

set -uo pipefail

ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
CHECKS="$ROOT/Leancourse/Checks"

# --- collect the files to check -------------------------------------
FILES=()
if [ "$#" -eq 0 ]; then
  mapfile -t FILES < <(find "$CHECKS" -name '*.lean' | sort)
else
  for arg in "$@"; do
    case "$arg" in
      /*) p="$arg" ;;
      *)  p="$ROOT/$arg" ;;
    esac
    if [ -d "$p" ]; then
      mapfile -t -O "${#FILES[@]}" FILES < <(find "$p" -name '*.lean' | sort)
    elif [ -f "$p" ]; then
      FILES+=("$p")
    else
      echo "no such file or directory: $arg" >&2
      exit 1
    fi
  done
fi

if [ "${#FILES[@]}" -eq 0 ]; then
  echo "No .lean files to check." >&2
  exit 1
fi

# --- check one file -------------------------------------------------
# A sheet may deliberately contain statements that are NOT provable --
# 01-a asks the student to work out which of three implications hold.
# Such a witness declares how many `sorry`s are expected with a line
#
#   -- CHECK: expect N sorry
#
# anywhere in the file.  Anything other than exactly N is a failure,
# so an unexpected `sorry` is caught and a disappearing one (the
# statement was fixed, the marker was not) is caught too.
#
# Printed to stdout as "<status>\t<relative path>\t<detail>".
check_one() {
  local f="$1" rel out want got
  rel="${f#"$ROOT"/}"
  want="$(sed -n 's/^--[[:space:]]*CHECK:[[:space:]]*expect[[:space:]]\+\([0-9]\+\)[[:space:]]\+sorry.*/\1/p' "$f" | head -1)"
  want="${want:-0}"
  out="$(cd "$ROOT" && lake env lean "$f" 2>&1)"
  got="$(printf '%s' "$out" | grep -c 'declaration uses .sorry')"
  if printf '%s' "$out" | grep -q ': error'; then
    printf 'ERROR\t%s\t%s\n' "$rel" \
      "$(printf '%s' "$out" | grep -c ': error') error(s)"
  elif [ "$got" -ne "$want" ]; then
    printf 'SORRY\t%s\t%s\n' "$rel" "$got sorry, expected $want"
  elif [ "$want" -gt 0 ]; then
    printf 'OK\t%s\t%s\n' "$rel" "$want expected sorry"
  else
    printf 'OK\t%s\t\n' "$rel"
  fi
}
export -f check_one
export ROOT

echo "Checking ${#FILES[@]} witness file(s) in Leancourse/Checks/ ..."
echo

RESULTS="$(printf '%s\n' "${FILES[@]}" \
  | xargs -P 4 -I {} bash -c 'check_one "$@"' _ {} | sort -k2)"

printf '%s\n' "$RESULTS" | while IFS=$'\t' read -r status rel detail; do
  case "$status" in
    OK)    if [ -n "$detail" ]; then printf '  ok     %s  (%s)\n' "$rel" "$detail"
           else                      printf '  ok     %s\n'       "$rel"; fi ;;
    SORRY) printf '  SORRY  %s  (%s)\n'  "$rel" "$detail" ;;
    ERROR) printf '  ERROR  %s  (%s)\n'  "$rel" "$detail" ;;
  esac
done

FAILED="$(printf '%s\n' "$RESULTS" | grep -cE '^(ERROR|SORRY)')"
TOTAL="${#FILES[@]}"

echo
if [ "$FAILED" -eq 0 ]; then
  echo "All $TOTAL witness file(s) compile cleanly and are sorry-free."
  exit 0
fi

echo "$FAILED of $TOTAL witness file(s) failed."
echo
echo "A failure means one of two things:"
echo "  * the witness has rotted and needs fixing, or"
echo "  * the exercise sheet it belongs to is genuinely broken."
echo "Check the sheet in Leancourse/Exercises/ before touching the witness."
exit 1
