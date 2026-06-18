module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Real

/-- The **Basel problem**: `∑ 1/n² = π²/6`, where the `n = 0` term is `1 / 0 = 0` by convention. -/
def BaselProblem : Prop := ∑' n : ℕ, (1 : ℝ) / n ^ 2 = π ^ 2 / 6
