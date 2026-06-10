module

public import DifferentProofs.IrrationalSqrtTwo.Defs
public import Mathlib.Tactic.FieldSimp

@[expose] public section

theorem IrrationalSqrtTwoNat_impl_IrrationalSqrtTwo :
    IrrationalSqrtTwoNat → IrrationalSqrtTwo := by
  rintro h ⟨r, hr⟩
  have hr2 : r ^ 2 = 2 := by
    exact_mod_cast show (r : ℝ) ^ 2 = 2 by rw [hr, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hz : r.num ^ 2 = (r.den : ℤ) ^ 2 * 2 := by
    rw [← Rat.num_div_den r] at hr2
    field_simp at hr2
    exact_mod_cast hr2
  have hn : r.num.natAbs ^ 2 = 2 * r.den ^ 2 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow, mul_comm] using congrArg Int.natAbs hz
  exact r.den_nz (h _ _ hn)
