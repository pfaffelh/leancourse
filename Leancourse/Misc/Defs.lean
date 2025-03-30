import VersoManual

open Verso.Genre Manual

-- The following defines the possibility to get a newline within a table.

def Inline.br : Manual.Inline where
  name := `br

def br (_ : Array (Verso.Doc.Inline Manual)) : Verso.Doc.Inline Manual :=
  .other Inline.br #[]

open Verso.Output.Html in
@[inline_extension br]
def br.descr : InlineDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ =>
    pure {{<br/>}}
  toTeX := none
