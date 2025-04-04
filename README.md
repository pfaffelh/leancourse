To build the example website and place the results in _out/examples/demosite, run:

lake build
lake exe leancourse --output _out/
To view the output, a local server will be needed. One way to get such a server is to use the one from the Python standard library, e.g.

pkill python3; lake build; lake exe leancourse --output _out --verbose --depth 2; python3 -m http.server 8800 --directory _out/html-multi/

https://pfaffelh.github.io/leancourse/
shows 


This is how to include docstrings

{docstring Lean.Parser.Tactic.apply}


Lean examples take the form

```lean (name := twoplustwo)
example : 2 + 2 = 4 :=
  by rfl
```

LeanOutput is 
```leanOutput twoplustwo (severity := information)

```
and then wait for the bulb...




New paragraphs start with

:::paragraph


change "All goals completed" to "No goals"

Make `exact` instead of exact etc.

