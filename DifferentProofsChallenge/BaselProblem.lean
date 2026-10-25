module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Comparator challenge: the Basel problem

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.BaselProblem.*` is required to prove. See `README.md` for what the Comparator check
guarantees and how to run it.
-/

@[expose] public section

open Real

/-- The **Basel problem**: `∑ 1/n² = π²/6`, where the `n = 0` term is `1 / 0 = 0` by convention. -/
def BaselProblem : Prop := ∑' n : ℕ, (1 : ℝ) / n ^ 2 = π ^ 2 / 6

theorem BaselProblem_Cauchy : BaselProblem := sorry

theorem BaselProblem_Parseval : BaselProblem := sorry

theorem BaselProblem_Ramanujan : BaselProblem := sorry

theorem BaselProblem_RamanujanUnnormalized : BaselProblem := sorry
