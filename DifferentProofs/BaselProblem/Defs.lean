module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Real

-- 1 / 0 = 0
def BaselProblem : Prop := ∑' n : ℕ, (1 : ℝ) / n ^ 2 = π ^ 2 / 6
