import VersoSlides
import Slides.Introduction
import Slides.Filters

open VersoSlides

def deckConfig (dir : String) : Config := {
  outputDir := dir
  theme := "white"
  slideNumber := true
  transition := "slide" }

/--
Generates the slide decks.  The argument is the *base* directory; each
deck is written to a subdirectory of it named after the deck, so that
adding a deck needs no change to the deploy workflow.  The base
defaults to `_slides`; the workflow passes `_out/html-multi/slides`
so the decks end up next to the rendered manual.
-/
def main (args : List String) : IO UInt32 := do
  let base := args.head?.getD "_slides"
  let decks : List (String × (String → IO UInt32)) :=
    [ ("introduction", fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Introduction)),
      ("filters",      fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Filters)) ]
  let mut code : UInt32 := 0
  for (name, run) in decks do
    IO.println s!"slides: {name}"
    let c ← run s!"{base}/{name}"
    if c != 0 then code := c
  return code
