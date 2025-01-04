import VersoManual

import Leancourse

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/leanprover/verso",
  issueLink := some "https://github.com/leanprover/verso/issues"
}

def main := manualMain (%doc Leancourse.Basic) (config := config)
