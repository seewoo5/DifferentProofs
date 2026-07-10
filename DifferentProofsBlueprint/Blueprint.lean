import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Summary
import DifferentProofsBlueprint.Commands.Graph
import DifferentProofsBlueprint.Chapters.CombinatorialIdentities
import DifferentProofsBlueprint.Chapters.FermatLittleTheorem
import DifferentProofsBlueprint.Chapters.InfinitudeOfPrimes
import DifferentProofsBlueprint.Chapters.IrrationalSqrtTwo
import DifferentProofsBlueprint.Chapters.BaselProblem

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

Matching custom backgrounds in the graph identify sorry-free theorems with
exactly the same mathematical statement, even when their blueprint and Lean
names differ. The configured color appears only after the theorem and all its
recorded dependencies are complete; otherwise the normal proof-status fill is
kept.

{include 0 DifferentProofsBlueprint.Chapters.FermatLittleTheorem}
{include 0 DifferentProofsBlueprint.Chapters.InfinitudeOfPrimes}
{include 0 DifferentProofsBlueprint.Chapters.IrrationalSqrtTwo}
{include 0 DifferentProofsBlueprint.Chapters.BaselProblem}
{include 0 DifferentProofsBlueprint.Chapters.CombinatorialIdentities}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
