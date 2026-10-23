import VersoManual

open Lean Verso.Genre Manual
open Verso.Doc.Elab

-- The `{br}` role: a line break inside a Verso table cell. Verso has
-- no inline break of its own, so the notes define one here.  Imported
-- by every page of the tactic appendix.

def Inline.br : Manual.Inline where
  name := `MyDef.br

@[role_expander MyDef.br]
def MyDef.br : RoleExpander
  | #[], #[] => do
    pure #[← `(Verso.Doc.Inline.other Inline.br #[])]
  | _, _ => throwError "`br` takes no arguments"

open Verso.Output.Html in
@[inline_extension MyDef.br]
def MyDef.br.descr : InlineDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ =>
    pure {{<br/>}}
  toTeX := none

open MyDef
