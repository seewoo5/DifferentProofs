module

public import DifferentProofs.IrrationalSqrtTwo.Basic
public import Mathlib.Tactic.Ring

/-!
# Irrationality of `√2` by infinite descent

If `p ^ 2 = 2 * q ^ 2` with `q` positive, then `p` is even, because the square of an odd number is
odd. Writing `p = 2 * r` gives `q ^ 2 = 2 * r ^ 2`, a solution with a smaller first component.

The natural-number form `IrrationalSqrtTwoNat_Descent` depends only on `propext`, which its
statement already forces, so no proof of it can use fewer axioms. Keeping it there rules out `lia`,
`omega` and mathlib's `Nat.Prime.dvd_of_dvd_pow`, which reach `Classical.choice` or `Quot.sound`.
The `#guard_msgs` at the end of this file fail the build otherwise. `IrrationalSqrtTwo_Descent`
depends on `Classical.choice`, because the statement `IrrationalSqrtTwo` does.
-/

@[expose] public section

namespace IrrationalSqrtTwo.Descent

/-- If `p ^ 2 = 2 * q ^ 2`, then `p` is even, because the square of an odd number is odd. -/
theorem exists_eq_two_mul_of_sq_eq {p q : ℕ} (h : p ^ 2 = 2 * q ^ 2) : ∃ r, p = 2 * r := by
  rcases Nat.mod_two_eq_zero_or_one p with hp | hp
  · exact ⟨p / 2, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hp)).symm⟩
  · have hk : 2 * (p / 2) + 1 = p := hp ▸ Nat.div_add_mod p 2
    generalize p / 2 = k at hk
    subst hk
    have e : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have h1 := congrArg (· % 2) (e.symm.trans h)
    simp only [Nat.mul_add_mod, Nat.mul_mod_right] at h1
    exact absurd h1 (by decide)

end IrrationalSqrtTwo.Descent

open IrrationalSqrtTwo.Descent in
lemma IrrationalSqrtTwoNat_Descent : IrrationalSqrtTwoNat := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro q hpq
    rcases Nat.eq_zero_or_pos q with hq | hq
    · exact hq
    obtain ⟨r, rfl⟩ := exists_eq_two_mul_of_sq_eq hpq
    have hq2 : 0 < q ^ 2 := Nat.pow_pos hq
    have h2 : (2 * r) ^ 2 = 2 * (2 * r ^ 2) := by ring
    have hqr : q ^ 2 = 2 * r ^ 2 :=
      (Nat.eq_of_mul_eq_mul_left Nat.two_pos (h2.symm.trans hpq)).symm
    have hlt : q < 2 * r := Nat.lt_of_not_ge fun hge => by
      have h1 : (2 * r) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hge 2
      rw [h2, ← hqr, Nat.two_mul] at h1
      exact Nat.not_le_of_gt hq2 (Nat.le_of_add_le_add_left (Nat.add_zero _ ▸ h1))
    rw [ih q hlt r hqr] at hqr
    rw [hqr] at hq2
    exact absurd hq2 (by decide)

theorem IrrationalSqrtTwo_Descent : IrrationalSqrtTwo :=
  IrrationalSqrtTwoNat_impl_IrrationalSqrtTwo IrrationalSqrtTwoNat_Descent

/-- info: 'IrrationalSqrtTwoNat_Descent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms IrrationalSqrtTwoNat_Descent
