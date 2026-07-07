# leancourse

## Using a compute server (for the course)

For our course, you can use a compute server, which you might need if your
computer does not have enough RAM. (Usually, Lean does not work well with less
than 32 GB.) Please contact the advisors for a login. Once you have it, follow
these instructions:

1. Connect your computer to the university network via VPN.
2. Create an SSH key and copy it to the remote machine
   (`ssh-keygen`, then `ssh-copy-id <user>@<host>`).
3. Install the **Remote - SSH** extension for VS Code on your machine.
4. Connect to the remote host (command palette → *Remote-SSH: Connect to
   Host…*). From here on you work inside VS Code, but everything runs on the
   server.
5. **Install Lean on the remote host.** Lean is managed by `elan`, which
   downloads the exact version each project needs. Open a terminal on the
   remote (*Terminal → New Terminal*) and run
   ```
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```
   Accept the offered `PATH` change, then open a fresh terminal (or run
   `source ~/.elan/env`) so that `lean` and `lake` are available.
6. **Get the course materials onto the remote host** by cloning the
   repository:
   ```
   git clone https://github.com/pfaffelh/leancourse.git
   cd leancourse
   ```
   (If the advisors point you to a different repository — e.g. one containing
   the exercises — clone that one instead.)
7. **Fetch the prebuilt Mathlib cache and build.** The course depends on
   Mathlib; compiling it from source would take hours and a lot of memory, so
   download the precompiled files instead:
   ```
   lake exe cache get
   lake build
   ```
   On the first `lake` call, `elan` installs the Lean version pinned in
   `lean-toolchain` automatically. `lake exe cache get` then downloads
   Mathlib's compiled `.olean` files, and `lake build` compiles only the
   course's own files.
8. **Open the folder and start Lean.** Still connected to the remote, choose
   *File → Open Folder…* and open the `leancourse` folder on the server. In the
   Extensions panel install the **Lean 4** extension *on the remote host*
   (VS Code lists a separate "SSH: …" section there — install it in that
   section, not only locally). Open any `.lean` file: after a moment the goal
   window (*InfoView*) appears, and from now on all of Lean's checking runs on
   the compute server rather than on your laptop.

You now edit and navigate files in VS Code exactly as you would locally; only
the heavy computation happens remotely.

**No root/`sudo` is required.** Everything above installs into your home
directory — `elan` into `~/.elan`, the Mathlib cache into the project's
`.lake/` and `~/.cache`, and the VS Code server and Lean extension into
`~/.vscode-server`. Checking `.lean` files needs no compiler either (`elan`
ships prebuilt `lean`/`lake` binaries and `lake exe cache get` fetches
precompiled Mathlib). The advisors only need to ensure that `curl` and `git`
are available on the server (they normally are); a C compiler is needed solely
if you build native executables, not for the exercises.

## Building and authoring (development notes)

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

Informative output, such as the result of {keywordOf Lean.Parser.Command.eval}`#eval`, is shown like this:
```leanOutput output (severity := information)
"The answer is 4"
```

LeanOutput is 
```leanOutput twoplustwo (severity := information)

```
and then wait for the bulb...




New paragraphs start with

:::paragraph


change "All goals completed" to "No goals"

Make `exact` instead of exact etc.

