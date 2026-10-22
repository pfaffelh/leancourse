import VersoSlides
import Slides.Introduction
import Slides.Filters
import Slides.Nat
import Slides.Types
import Slides.Terms
import Slides.Typeclasses
import Slides.CurryHoward
import Slides.DependentTypes
import Slides.Notation

open VersoSlides

/--
Styling for the back-link that every deck carries in its upper right
corner.  The link sits on `body`, outside `.reveal`, so `reveal.js`
neither scales it with the slide nor moves it between slides; it is
faint until hovered and is dropped from the PDF export.
-/
def backLinkCss : String := "
.course-back {
  position: fixed;
  top: 0.8rem;
  right: 1.1rem;
  z-index: 40;
  display: inline-flex;
  align-items: center;
  gap: 0.35em;
  padding: 0.25em 0.7em;
  border: 1px solid #34499a;
  border-radius: 999px;
  background: rgba(255, 255, 255, 0.9);
  color: #34499a;
  font-family: inherit;
  font-size: 0.75rem;
  line-height: 1.5;
  text-decoration: none;
  opacity: 0.45;
  transition: opacity 0.15s ease;
}
.course-back:hover, .course-back:focus {
  opacity: 1;
}
@media print {
  .course-back { display: none; }
}
"

/--
Adds the back-link to the page.  The target is relative: a deck is
written to `<site>/slides/<deck>/`, so two levels up is the site root
and `Lecture-slides` is the chapter listing the decks.  Building the
decks on their own (`lake exe slides`) puts them outside the manual,
and the link then has nothing to point at.
-/
def backLinkJs : String := "
document.addEventListener('DOMContentLoaded', function () {
  var a = document.createElement('a');
  a.className = 'course-back';
  a.href = '../../Lecture-slides/';
  a.title = 'Back to the course notes';
  a.textContent = '\\u2190 Course notes';
  document.body.appendChild(a);
});
"

open Verso.Output.Html in
/-- Tab icon and back-link, added to the `head` of every deck. -/
def deckHead : Array Verso.Output.Html := #[
  {{ <link rel="icon" type="image/svg+xml" href="../../static/favicon.svg" /> }},
  {{ <link rel="icon" type="image/png" sizes="32x32" href="../../static/favicon-32.png" /> }},
  {{ <style>{{Verso.Output.Html.text false backLinkCss}}</style> }},
  {{ <script>{{Verso.Output.Html.text false backLinkJs}}</script> }}
]

def deckConfig (dir : String) : Config := {
  outputDir := dir
  theme := "white"
  slideNumber := true
  transition := "slide"
  extraHead := deckHead }

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
      ("filters",      fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Filters)),
      ("nat",             fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Nat)),
      ("types",           fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Types)),
      ("terms",           fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Terms)),
      ("typeclasses",     fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Typeclasses)),
      ("curry-howard",    fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.CurryHoward)),
      ("dependent-types", fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.DependentTypes)),
      ("notation",        fun d => slidesMain (config := deckConfig d) (doc := %doc Slides.Notation)) ]
  let mut code : UInt32 := 0
  for (name, run) in decks do
    IO.println s!"slides: {name}"
    let c ← run s!"{base}/{name}"
    if c != 0 then code := c
  return code
