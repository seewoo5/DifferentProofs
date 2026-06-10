module

public import DifferentProofs.IrrationalSqrtTwo.Defs
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.Tactic.LinearCombination

@[expose] public section

theorem IrrationalSqrtTwo_FermatLastTheorem : IrrationalSqrtTwo := by
  rintro ⟨r, hr⟩
  have hr2 : r ^ 2 = 2 := by
    exact_mod_cast show (r : ℝ) ^ 2 = 2 by rw [hr, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hx : (18 : ℚ) + 17 * r ≠ 0 := fun h => by
    rw [show r = -(18 / 17) by linear_combination h / 17] at hr2
    norm_num at hr2
  have hy : (18 : ℚ) - 17 * r ≠ 0 := fun h => by
    rw [show r = 18 / 17 by linear_combination -h / 17] at hr2
    norm_num at hr2
  exact fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree _ _ _ hx hy
    (by norm_num : (42 : ℚ) ≠ 0) (by linear_combination (31212 : ℚ) * hr2)
