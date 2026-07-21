module

public import DifferentProofs.SumOfTwoSquares.Defs
public import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Sum of two squares via Jacobi sums (Alpoge's proof)

Alpoge's one-line proof: let `χ₄ : (ZMod p)ˣ → ℂˣ` be a character of order `4` (available because
`4 ∣ p - 1`), extended by `χ₄ 0 = 0`. The Jacobi sum

```
J = ∑ x, χ₄ x · χ₄ (1 - x)
```

lies in `ℤ[i]` because `χ₄` takes values in the fourth roots of unity, and
`jacobiSum_mul_jacobiSum_inv` gives `J · conj J = p`, i.e. `|J|² = p`. Writing `J = a + b·i`
with `a, b ∈ ℤ` yields `a² + b² = p`.
-/

@[expose] public section

open Complex

namespace SumOfTwoSquares.Jacobi

/-- Every element of `ℤ[i] = Algebra.adjoin ℤ {I}` has integer real and imaginary parts. -/
private lemma exists_int_coeffs {z : ℂ} (hz : z ∈ Algebra.adjoin ℤ ({I} : Set ℂ)) :
    ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * I := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simp [Set.eq_of_mem_singleton hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a₁, b₁, rfl⟩ := ihx
    obtain ⟨a₂, b₂, rfl⟩ := ihy
    exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a₁, b₁, rfl⟩ := ihx
    obtain ⟨a₂, b₂, rfl⟩ := ihy
    exact ⟨a₁ * a₂ - b₁ * b₂, a₁ * b₂ + a₂ * b₁, by
      push_cast; linear_combination (b₁ * b₂ : ℂ) * I_sq⟩

/-- `I` is a primitive fourth root of unity. -/
private lemma isPrimitiveRoot_I : IsPrimitiveRoot I 4 :=
  IsPrimitiveRoot.mk_of_lt I four_pos I_pow_four fun l hl0 hl4 => by
    interval_cases l <;> norm_num [Complex.ext_iff, I_sq, I_pow_three]

/-- Fermat's theorem on sums of two squares, via Jacobi sums: the Jacobi sum of a quartic
character on `ZMod p` is a Gaussian integer of norm `p` (Alpoge's proof). -/
theorem FermatSumOfTwoSquares_Jacobi : FermatSumOfTwoSquares := by
  intro p hp hp4
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ, hord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) (R := ℂ) (n := 4)
    (by rw [ZMod.card]; omega) isPrimitiveRoot_I
  have hχ4 : χ ^ 4 = 1 := hord ▸ pow_orderOf_eq_one χ
  have hχ1 : χ ≠ 1 := fun h => by simp [h, orderOf_one] at hord
  have hχχ : χ * χ ≠ 1 := fun h => by
    have h2 := orderOf_dvd_of_pow_eq_one (show χ ^ 2 = 1 by rwa [pow_two])
    rw [hord] at h2
    omega
  have hrc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]
    exact hp.pos.ne
  have hmul := jacobiSum_mul_jacobiSum_inv hrc hχ1 hχ1 hχχ
  have hconj : χ⁻¹ = χ.ringHomComp (starRingEnd ℂ) := (MulChar.star_eq_inv χ).symm
  rw [ZMod.card, hconj, jacobiSum_ringHomComp, mul_conj] at hmul
  obtain ⟨a, b, hab⟩ := exists_int_coeffs
    (jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ4 hχ4 isPrimitiveRoot_I)
  rw [hab, ← ofReal_intCast a, ← ofReal_intCast b, normSq_add_mul_I] at hmul
  exact ⟨a.natAbs, b.natAbs, by zify [sq_abs]; exact_mod_cast hmul⟩

end SumOfTwoSquares.Jacobi
