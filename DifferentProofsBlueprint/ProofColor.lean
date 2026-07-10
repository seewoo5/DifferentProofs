import VersoBlueprint

namespace DifferentProofsBlueprint.ProofColor

open Lean
open Verso Doc Elab
open Lean.Doc.Syntax

abbrev State := Lean.NameMap String

initialize proofColorExt : PersistentEnvExtension (Name × String) (Name × String) State ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun imported =>
      pure <| imported.foldl (init := ({} : State)) fun colors entries =>
        entries.foldl (init := colors) fun colors (label, color) =>
          colors.insert label color
    addEntryFn := fun colors (label, color) => colors.insert label color
    exportEntriesFn := fun colors => colors.toArray
  }

def all (env : Environment) : State :=
  proofColorExt.getState env

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def isHexColor (color : String) : Bool :=
  match color.toList with
  | '#' :: digits => digits.length == 6 && digits.all isHexDigit
  | _ => false

private def extractProofColor (args : Array Verso.Doc.Arg) :
    DocElabM (Option String × Array Verso.Doc.Arg) := do
  let mut proofColor? := none
  let mut remaining := #[]
  for arg in args do
    match arg with
    | .named stx name value =>
        if name.getId.eraseMacroScopes == `proofColor then
          if proofColor?.isSome then
            throwErrorAt stx "The `proofColor` option may only be specified once"
          let color ←
            match value with
            | .str color => pure color.getString.trimAscii.toString
            | _ => throwErrorAt value.syntax "Expected `proofColor` to be a string"
          unless isHexColor color do
            throwErrorAt value.syntax
              m!"Invalid proof color '{color}'; expected a six-digit hex color such as #ddd6fe"
          proofColor? := some color
        else
          remaining := remaining.push arg
    | _ => remaining := remaining.push arg
  pure (proofColor?, remaining)

private def register (label : Name) (color : String) : DocElabM Unit := do
  let colors := all (← getEnv)
  if let some previous := colors.get? label then
    unless previous == color do
      throwError
        m!"Blueprint node '{label}' already has proof color '{previous}', cannot assign '{color}'"
  modifyEnv fun env => proofColorExt.addEntry env (label, color)

private def expandTheoremLike (name : Name) (cfg : Informal.Config)
    (blocks : TSyntaxArray `block) : DocElabM Term :=
  if name == ``Informal.proposition then
    Informal.proposition cfg blocks
  else if name == ``Informal.lemma_ then
    Informal.lemma_ cfg blocks
  else if name == ``Informal.theorem then
    Informal.theorem cfg blocks
  else if name == ``Informal.corollary then
    Informal.corollary cfg blocks
  else
    Lean.Elab.throwUnsupportedSyntax

@[block_expander Lean.Doc.Syntax.directive]
public meta def expandProofColorDirective : BlockExpander
  | `(block| ::: $nameStx:ident $argsStx* { $blocks:block* } ) => do
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    let args ← parseArgs argsStx
    let (proofColor?, args) ← extractProofColor args
    let some color := proofColor?
      | Lean.Elab.throwUnsupportedSyntax
    let cfg ← Verso.ArgParse.parseThe Informal.Config args
    let term ← expandTheoremLike name cfg blocks
    register cfg.label color
    pure term
  | _ => Lean.Elab.throwUnsupportedSyntax

end DifferentProofsBlueprint.ProofColor
