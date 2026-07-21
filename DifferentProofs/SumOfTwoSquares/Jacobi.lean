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
private lemma exists_int_coeffs {z : ℂ} (hz : z ∈ Algebra.adjoin ℤ ({Complex.I} : Set ℂ)) :
    ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * Complex.I := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a₁, b₁, rfl⟩ := ihx
      obtain ⟨a₂, b₂, rfl⟩ := ihy
      exact ⟨a₁ + a₂, b₁ + b₂, by push_cast; ring⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨a₁, b₁, rfl⟩ := ihx
      obtain ⟨a₂, b₂, rfl⟩ := ihy
      exact ⟨a₁ * a₂ - b₁ * b₂, a₁ * b₂ + a₂ * b₁, by
        push_cast; linear_combination (b₁ * b₂ : ℂ) * Complex.I_sq⟩

/-- `I` is a primitive fourth root of unity. -/
private lemma isPrimitiveRoot_I : IsPrimitiveRoot (Complex.I) 4 := by
  refine ⟨Complex.I_pow_four, fun l hl => ?_⟩
  rw [Complex.I_pow_eq_pow_mod] at hl
  have hlt : l % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : l % 4
  · exact Nat.dvd_of_mod_eq_zero h
  · rw [pow_one] at hl; simp [Complex.ext_iff] at hl
  · rw [Complex.I_sq] at hl; norm_num at hl
  · rw [Complex.I_pow_three] at hl; simp [Complex.ext_iff] at hl

theorem FermatSumOfTwoSquares_Jacobi : FermatSumOfTwoSquares := by
  intro p hp hp4
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- A multiplicative character `χ` of order 4 on `ZMod p`, valued in `ℂ`.
  obtain ⟨χ, hord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) (R := ℂ) (n := 4)
    (by rw [ZMod.card]; omega) isPrimitiveRoot_I
  have hχ4 : χ ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one χ
  have hχ1 : χ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; norm_num at hord
  have hχχ : χ * χ ≠ 1 := by
    intro h
    have h2 : χ ^ 2 = 1 := by rw [pow_two]; exact h
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hd; norm_num at hd
  have hrc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]; exact fun h => hp.pos.ne' h.symm
  -- The Jacobi sum `J = ∑ₓ χ(x)χ(1-x)` satisfies `J · conj J = p`.
  have hmul := jacobiSum_mul_jacobiSum_inv hrc hχ1 hχ1 hχχ
  rw [ZMod.card] at hmul
  -- `χ⁻¹` is the conjugate character, since `χ` takes values in the unit circle.
  have hconj : χ⁻¹ = χ.ringHomComp (starRingEnd ℂ) := by
    ext a
    rw [MulChar.inv_apply_eq_inv', MulChar.ringHomComp_apply]
    have hpow : χ (a : ZMod p) ^ 4 = 1 := by
      rw [← MulChar.pow_apply_coe χ 4 a, hχ4, MulChar.one_apply_coe]
    have hne : χ (a : ZMod p) ≠ 0 := by
      intro h; rw [h] at hpow; norm_num at hpow
    have hnorm : Complex.normSq (χ (a : ZMod p)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one hpow (by norm_num)]
      norm_num
    refine mul_left_cancel₀ hne ?_
    rw [mul_inv_cancel₀ hne, Complex.mul_conj, hnorm]; norm_num
  rw [hconj, jacobiSum_ringHomComp, Complex.mul_conj] at hmul
  -- Extract integer coordinates of `J` from `J ∈ ℤ[i]`.
  obtain ⟨a, b, hab⟩ := exists_int_coeffs
    (jacobiSum_mem_algebraAdjoin_of_pow_eq_one hχ4 hχ4 isPrimitiveRoot_I)
  rw [hab, ← Complex.ofReal_intCast a, ← Complex.ofReal_intCast b, Complex.normSq_add_mul_I] at hmul
  have hpint : a ^ 2 + b ^ 2 = (p : ℤ) := by
    have : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) = (p : ℝ) := by exact_mod_cast hmul
    exact_mod_cast this
  refine ⟨a.natAbs, b.natAbs, ?_⟩
  have hnat : ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℤ) = (p : ℤ) := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs,
      sq_abs, sq_abs]
    exact hpint
  exact_mod_cast hnat

end SumOfTwoSquares.Jacobi
