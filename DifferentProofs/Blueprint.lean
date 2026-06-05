import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import DifferentProofs.FermatLittleTheorem.Blueprint
import DifferentProofs.InfinitudeOfPrimes.Blueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false
set_option verso.blueprint.foldProofBlocks true
set_option verso.blueprint.graph.defaultPack true

#doc (Manual) "Different Proofs" =>

This blueprint tracks formalizations of multiple proofs of the same theorem.
The Lean declarations live in the `DifferentProofs` library, while this Verso
document records the informal statements, proof sketches, and dependency graph.

{include 0 DifferentProofs.FermatLittleTheorem.Blueprint}
{include 0 DifferentProofs.InfinitudeOfPrimes.Blueprint}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
