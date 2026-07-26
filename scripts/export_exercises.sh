#!/usr/bin/env bash
#
# Export the student exercises into a standalone repository.
#
# Usage:
#   scripts/export_exercises.sh [TARGET_DIR] [--with-solutions]
#
# TARGET_DIR defaults to ../leancourse_exercises (a sibling of this
# repository).  The script is idempotent: run it again after editing
# exercises here, then commit and push inside TARGET_DIR.
#
# What it does:
#   * copies Leancourse/Exercises/ -> TARGET_DIR/Exercises/
#     (Solutions/ is skipped unless --with-solutions is given)
#   * writes lean-toolchain, lakefile.lean, and a lake-manifest.json
#     pinned to the exact Mathlib revision this repository uses, so
#     `lake exe cache get` finds a prebuilt cache
#   * writes README.md and .gitignore on first export only (so local
#     edits in the exercises repo are not clobbered)

set -euo pipefail

ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
TARGET="${1:-$ROOT/../leancourse_exercises}"
WITH_SOLUTIONS=0
for arg in "$@"; do
  [ "$arg" = "--with-solutions" ] && WITH_SOLUTIONS=1
done

mkdir -p "$TARGET"

# --- exercises ------------------------------------------------------
RSYNC_ARGS=(-a --delete --exclude 'MyExercises')
if [ "$WITH_SOLUTIONS" -eq 0 ]; then
  RSYNC_ARGS+=(--exclude 'Solutions')
fi
rsync "${RSYNC_ARGS[@]}" "$ROOT/Leancourse/Exercises/" "$TARGET/Exercises/"

# --- toolchain ------------------------------------------------------
cp "$ROOT/lean-toolchain" "$TARGET/lean-toolchain"

# --- lakefile -------------------------------------------------------
# Pin Mathlib to the same revision as the course repository.
MATHLIB_REV="$(grep -oP 'mathlib4"@"\K[^"]+' "$ROOT/lakefile.lean")"
cat > "$TARGET/lakefile.lean" <<EOF
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"$MATHLIB_REV"

package «leancourse_exercises» where
  moreLeancArgs := #["-O0"]

@[default_target]
lean_lib «LeancourseExercises» where
EOF

# Stub library root: the exercise files themselves are opened
# directly in the editor and are not lake build targets (their
# names, e.g. 01-a-Propositions, are not valid module names).
if [ ! -f "$TARGET/LeancourseExercises.lean" ]; then
  cat > "$TARGET/LeancourseExercises.lean" <<'EOF'
-- The exercises live under `Exercises/`; open them directly in
-- VS Code.  This root module only exists so that `lake build`
-- has a (trivial) target.
EOF
fi

# --- manifest -------------------------------------------------------
# Restrict the course manifest to Mathlib and its dependencies, so
# every package is pinned to a revision covered by the Mathlib cache.
jq --arg name "leancourse_exercises" '
  .name = $name |
  .packages |= map(select(.name as $n |
    ["mathlib", "batteries", "aesop", "Qq", "proofwidgets",
     "importGraph", "LeanSearchClient", "plausible", "Cli"]
    | index($n)))
' "$ROOT/lake-manifest.json" > "$TARGET/lake-manifest.json"

# --- one-time files -------------------------------------------------
if [ ! -f "$TARGET/.gitignore" ]; then
  cat > "$TARGET/.gitignore" <<'EOF'
/.lake
/MyExercises
EOF
fi

if [ ! -f "$TARGET/README.md" ]; then
  cat > "$TARGET/README.md" <<'EOF'
# Leancourse exercises

Exercise sheets for the course *Interactive Theorem Proving using
Lean* (University of Freiburg, winter semester 2026/27).  The course
notes are at <https://pfaffelh.github.io/leancourse/>.

## Setup

1. Install [VS Code](https://code.visualstudio.com/) and, inside VS
   Code, the *Lean 4 language extension* (which installs Lean itself
   on first use).
2. Clone this repository and fetch the precompiled Mathlib cache:

   ```
   git clone https://github.com/pfaffelh/leancourse_exercises
   cd leancourse_exercises
   lake exe cache get
   code .
   ```

3. Open a file under `Exercises/` (start with
   `Exercises/01-Logic/01-a-Propositions.lean`).  Once the orange
   bars disappear you are ready: replace the `sorry`s.

## Working on the sheets

Copy the `Exercises` folder to `MyExercises` and work there --
`MyExercises` is ignored by git, so updating the course material via

```
git pull
```

will never overwrite your own solutions.

## Troubleshooting

* Lean needs a fair amount of RAM; if your machine struggles, use
  the course compute server or GitHub Codespaces (see the course
  notes for instructions).
* If `lake exe cache get` fails, make sure you are inside the
  repository directory and try again; a partial download resumes.
EOF
fi

echo "Exported exercises to: $TARGET"
if [ "$WITH_SOLUTIONS" -eq 1 ]; then
  echo "  (including Solutions/)"
fi
echo "Next steps: cd \"$TARGET\" && git add -A && git commit && git push"
