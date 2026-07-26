# leancourse

Source repository for the course notes of *Interactive Theorem
Proving using Lean* (University of Freiburg, winter semester
2026/27). The notes are a [Verso](https://github.com/leanprover/verso)
manual; the rendered version is published at
<https://pfaffelh.github.io/leancourse/> via GitHub Actions on every
push to `main`.

**Students do not need this repository.** The exercise sheets live in
their own repository,
[pfaffelh/leancourse_exercises](https://github.com/pfaffelh/leancourse_exercises),
which is all you need to clone for the course. Setup instructions
(local machine or compute server) are in that repository's README and
in the introduction of the course notes.

## Layout

- `Leancourse/Coursenotes/` — the Verso chapters (built by Lean).
- `Leancourse/Exercises/` — the *source of truth* for the exercise
  sheets. They are exported to the student repository with
  `scripts/export_exercises.sh` (add `--with-solutions` to publish
  `Solutions/`); after an export, commit and push inside
  `../leancourse_exercises`.
- `.github/workflows/deploy.yml` — builds and deploys the site.

## Building the notes locally

```
lake exe cache get
lake build
lake exe leancourse --output _out/
```

To view the result, serve the multi-page HTML locally, e.g.:

```
python3 -m http.server 8800 --directory _out/html-multi/
```

(One-liner while authoring:
`pkill python3; lake build; lake exe leancourse --output _out --verbose --depth 2; python3 -m http.server 8800 --directory _out/html-multi/`)

## Authoring notes (Verso)

Docstrings are included with

```
{docstring Lean.Parser.Tactic.apply}
```

Lean examples take the form

````
```lean (name := twoplustwo)
example : 2 + 2 = 4 :=
  by rfl
```
````

Informative output, such as the result of `#eval`, is shown with

````
```leanOutput twoplustwo (severity := information)

```
````

and then wait for the bulb...

New paragraphs start with `:::paragraph`.

## TODO

- change "All goals completed" to "No goals"
- Make `exact` instead of exact etc.
