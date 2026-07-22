import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Summary
import DifferentProofsBlueprint.Commands.Graph
import DifferentProofsBlueprint.Chapters.CombinatorialIdentities
import DifferentProofsBlueprint.Chapters.FermatLittleTheorem
import DifferentProofsBlueprint.Chapters.InfinitudeOfPrimes
import DifferentProofsBlueprint.Chapters.IntegerRectangle
import DifferentProofsBlueprint.Chapters.IrrationalSqrtTwo
import DifferentProofsBlueprint.Chapters.SumOfTwoSquares
import DifferentProofsBlueprint.Chapters.BaselProblem

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false
set_option verso.blueprint.foldProofBlocks true
set_option verso.blueprint.graph.defaultPack true

#doc (Manual) "Different Proofs" =>

Each theorem deserves many proofs.

{include 0 DifferentProofsBlueprint.Chapters.FermatLittleTheorem}
{include 0 DifferentProofsBlueprint.Chapters.InfinitudeOfPrimes}
{include 0 DifferentProofsBlueprint.Chapters.IrrationalSqrtTwo}
{include 0 DifferentProofsBlueprint.Chapters.SumOfTwoSquares}
{include 0 DifferentProofsBlueprint.Chapters.BaselProblem}
{include 0 DifferentProofsBlueprint.Chapters.CombinatorialIdentities}
{include 0 DifferentProofsBlueprint.Chapters.IntegerRectangle}

{blueprint_graph (direction := LR) (pack := true)}
{blueprint_summary}
