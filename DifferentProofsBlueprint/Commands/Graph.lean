import VersoBlueprint.Commands.Graph
import DifferentProofsBlueprint.ProofColor

namespace DifferentProofsBlueprint.Commands.Graph

open Lean
open Verso Doc Elab

private def hexNibble? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then
    some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then
    some (c.toNat - 'A'.toNat + 10)
  else
    none

private def parseHexByte? (high low : Char) : Option Nat := do
  return 16 * (← hexNibble? high) + (← hexNibble? low)

private def parseHexColor? (color : String) : Option (Nat × Nat × Nat) := do
  match color.toList with
  | '#' :: r₁ :: r₂ :: g₁ :: g₂ :: b₁ :: b₂ :: [] =>
      return (← parseHexByte? r₁ r₂, ← parseHexByte? g₁ g₂, ← parseHexByte? b₁ b₂)
  | _ => none

private def fontColorForFill (fillColor : String) : String :=
  match parseHexColor? fillColor with
  | some (r, g, b) =>
      if 299 * r + 587 * g + 114 * b < 140000 then "#f8fafc" else "#0f172a"
  | none => "#0f172a"

private def withTooltip (node : Informal.Graph.NodeData) (message : String) :
    Informal.Graph.NodeData :=
  let tooltip? := some <|
    match node.visual.tooltip? with
    | some tooltip => tooltip ++ " | " ++ message
    | none => message
  { node with visual := { node.visual with tooltip? } }

private def applyProofColors (env : Environment) (graphModel : Informal.Graph.GraphModel) :
    Informal.Graph.GraphModel :=
  let colors := DifferentProofsBlueprint.ProofColor.all env
  {
    graphModel with
      nodes := graphModel.nodes.map fun node =>
        match colors.get? node.label with
        | none => node
        | some color =>
            match node.proofStatus with
            | .formalizedWithAncestors =>
                withTooltip
                  {
                    node with
                      visual := {
                        node.visual with
                          fillcolor := color
                          fontcolor := fontColorForFill color
                      }
                  }
                  s!"Proof-complete custom color: {color}"
            | _ =>
                withTooltip node s!"Custom color {color} pending a complete, sorry-free proof"
  }

open Verso Doc Elab Syntax PartElabM in
private def mkGraphPart (stx : Syntax) (endPos : String.Pos.Raw)
    (options : Informal.Graph.GraphOptions)
    (previewMode : Informal.HoverRender.PreviewMode := .pinned)
    (previewPlacement : Informal.HoverRender.PreviewPlacement := .docked) :
    PartElabM FinishedPart := do
  let titlePreview := "Dependency Graph"
  let titleInlines ← `(inline | "Dependency Graph")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let graphModel ← Informal.Commands.buildAll
  let graphModel := applyProofColors (← getEnv) graphModel
  let graphData : Informal.Commands.GraphBlockData := {
    graphModel, options, previewMode, previewPlacement
  }
  let block ← ``(Verso.Doc.Block.other
    (Informal.Commands.Block.graph $(quote graphData)) #[])
  pure <| FinishedPart.mk stx stx expandedTitle titlePreview metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Syntax.command]
public meta def depGraphWithProofColors : PartCommand
  | stx@`(block|command{blueprint_graph $args*}) => do
    let cfg ← Verso.ArgParse.parseThe Informal.Commands.BlueprintGraphConfig (← parseArgs args)
    let options ← Informal.Commands.parseGraphOptions cfg
    let previewMode ← Informal.Commands.parseGraphPreviewMode cfg
    let previewPlacement ← Informal.Commands.parseGraphPreviewPlacement cfg
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkGraphPart stx endPos options previewMode previewPlacement)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end DifferentProofsBlueprint.Commands.Graph
