import VersoBlueprint.Commands.Graph
import DifferentProofsBlueprint.ProofColor

namespace DifferentProofsBlueprint.Commands.Graph

open Lean
open Verso Doc Elab

private def withTooltip (node : Informal.Commands.GraphNode) (message : String) :
    Informal.Commands.GraphNode :=
  {
    node with
      tooltip? := some <|
        match node.tooltip? with
        | some tooltip => tooltip ++ " | " ++ message
        | none => message
  }

private def applyProofColors (env : Environment) (graph : Informal.Commands.Graph) :
    Informal.Commands.Graph :=
  let colors := DifferentProofsBlueprint.ProofColor.all env
  let state := Informal.Environment.informalExt.getState env
  graph.map fun node =>
    match colors.get? node.label with
    | none => node
    | some color =>
        let proofStatus? := state.data.get? node.label |>.map fun data =>
          Informal.Graph.proofStatus {} state node.label data
        match proofStatus? with
        | some .formalizedWithAncestors =>
            withTooltip
              {
                node with
                  fillcolor := color
                  fontcolor := Informal.Commands.fontColorForFill color
              }
              s!"Proof-complete custom color: {color}"
        | _ =>
            withTooltip node s!"Custom color {color} pending a complete, sorry-free proof"

open Verso Doc Elab Syntax PartElabM in
private def mkGraphPart (stx : Syntax) (endPos : String.Pos.Raw)
    (options : Informal.Commands.GraphOptions) : PartElabM FinishedPart := do
  let titlePreview := "Dependency Graph"
  let titleInlines ← `(inline | "Dependency Graph")
  let expandedTitle ← #[titleInlines].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let (graph, groupTitles) ← Informal.Commands.buildAll
  let graph := applyProofColors (← getEnv) graph
  let graphData : Informal.Commands.GraphBlockData := { graph, options, groupTitles }
  let block ← ``(Verso.Doc.Block.other
    (Informal.Commands.Block.graph $(quote graphData)) #[])
  pure <| FinishedPart.mk stx expandedTitle titlePreview metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Syntax.command]
public meta def depGraphWithProofColors : PartCommand
  | stx@`(block|command{blueprint_graph $args*}) => do
    let cfg ← Verso.ArgParse.parseThe Informal.Commands.BlueprintGraphConfig (← parseArgs args)
    let options ← Informal.Commands.parseGraphOptions cfg
    let endPos := stx.getTailPos?.get!
    closePartsUntil 1 endPos
    addPart (← mkGraphPart stx endPos options)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end DifferentProofsBlueprint.Commands.Graph
