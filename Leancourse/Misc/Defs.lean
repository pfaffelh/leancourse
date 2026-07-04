import VersoManual
import Verso.Doc.Elab

open Verso.Genre Manual
open Lean

-- The following defines the possibility to get a newline within a table.

def Inline.br : Manual.Inline where
  name := `MyDef.br

def MyDef.br (_ : Array (Verso.Doc.Inline Manual)) : Verso.Doc.Inline Manual :=
  .other Inline.br #[]

open Verso.Output.Html in
@[inline_extension MyDef.br]
def MyDef.br.descr : InlineDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ _ =>
    pure {{<br/>}}
  toTeX := none

open MyDef

-- A collapsible `<details>` block: content the reader may skip, but
-- that stays available on demand behind a summary line.

def MyDef.collapsible (summary : String) : Manual.Block where
  name := `MyDef.collapsible
  data := toJson summary

open Verso.Output.Html in
@[block_extension MyDef.collapsible]
def MyDef.collapsible.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id info content => do
    let summary := info.getStr?.toOption.getD ""
    let inner ← content.mapM goB
    pure {{
      <details>
        <summary>{{summary}}</summary>
        {{inner}}
      </details>
    }}
  toTeX := none

open Verso.ArgParse Verso.Doc.Elab in
@[directive_expander collapsedDetails]
def collapsedDetails : DirectiveExpander
  | args, contents => do
    let parser : Verso.ArgParse _ String := .positional `summary .string
    let summary ← parser.run args
    let blocks ← contents.mapM elabBlock
    return #[← ``(Verso.Doc.Block.other
      (MyDef.collapsible $(quote summary)) #[$blocks,*])]
