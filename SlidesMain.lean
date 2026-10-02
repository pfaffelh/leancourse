import VersoSlides
import Slides.Filters

open VersoSlides

/--
Generates the slide decks.  The output directory can be given as the
first argument; it defaults to `_slides`.  The deploy workflow passes
`_out/html-multi/slides/filters` so that the deck ends up next to the
rendered manual.
-/
def main (args : List String) : IO UInt32 :=
  slidesMain
    (config := {
      outputDir := args.head?.getD "_slides"
      theme := "white"
      slideNumber := true
      transition := "slide" })
    (doc := %doc Slides.Filters)
