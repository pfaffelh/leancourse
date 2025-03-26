import VersoManual

import Leancourse

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/pfaffelh/leancourse",
  issueLink := some "https://github.com/pfaffelh/leancourse/issues"
}

def main := manualMain (%doc Leancourse.Coursenotes) (config := config)
