To build the example website and place the results in _out/examples/demosite, run:

lake build
lake exe leancourse --output _out/
To view the output, a local server will be needed. One way to get such a server is to use the one from the Python standard library, e.g.

python3 -m http.server 8800 --directory _out/html-single/ &
after which http://localhost:8800/ will show the generated site.

pkill python3; lake build; lake exe leancourse --output _out/; python3 -m http.server 8800 --directory _out/html-single/

https://pfaffelh.github.io/leancourse/
shows 