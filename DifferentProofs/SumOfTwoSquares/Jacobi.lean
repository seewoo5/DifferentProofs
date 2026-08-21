module

public import DifferentProofs.SumOfTwoSquares.Defs
public import DifferentProofsForMathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

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

/-- The values of a character `χ` with `χ ^ 4 = 1` are Gaussian integers: every nonzero value
is a fourth root of unity, hence a power of `I`. -/
private lemma apply_mem_gaussianInt {p : ℕ} {χ : MulChar (ZMod p) ℂ} (hχ4 : χ ^ 4 = 1)
    (a : ZMod p) : χ a ∈ GaussianInt.toComplex.range := by
  by_cases hu : IsUnit a
  · have hpow : χ a ^ 4 = 1 := by
      rw [← χ.pow_apply' (by norm_num) a, hχ4, ← hu.unit_spec, MulChar.one_apply_coe]
    obtain ⟨i, -, hi⟩ := isPrimitiveRoot_I.eq_pow_of_pow_eq_one hpow
    exact hi ▸ pow_mem (RingHom.mem_range.mpr ⟨⟨0, 1⟩, by simp [GaussianInt.toComplex_def']⟩) i
  · exact χ.map_nonunit hu ▸ zero_mem _

end SumOfTwoSquares.Jacobi

open SumOfTwoSquares.Jacobi in
/-- Fermat's theorem on sums of two squares, via Jacobi sums: the Jacobi sum of a quartic
character on `ZMod p` is a Gaussian integer of norm `p` (Alpoge's proof). -/
theorem FermatSumOfTwoSquares_Jacobi : FermatSumOfTwoSquares := by
  intro p hp hp4
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ, hord⟩ := MulChar.exists_mulChar_orderOf (ZMod p) (R := ℂ) (n := 4)
    (by rw [ZMod.card]; lia) isPrimitiveRoot_I
  have hχ4 : χ ^ 4 = 1 := hord ▸ pow_orderOf_eq_one χ
  have hχ1 : χ ≠ 1 := fun h ↦ by simp [h, orderOf_one] at hord
  have hχχ : χ * χ ≠ 1 := fun h ↦ by
    have h2 := orderOf_dvd_of_pow_eq_one (show χ ^ 2 = 1 by rwa [pow_two])
    rw [hord] at h2
    lia
  have hrc : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq_zero]
    exact hp.pos.ne
  have hmul := jacobiSum_mul_jacobiSum_inv hrc hχ1 hχ1 hχχ
  have hconj : χ⁻¹ = χ.ringHomComp (starRingEnd ℂ) := (MulChar.star_eq_inv χ).symm
  rw [ZMod.card, hconj, jacobiSum_ringHomComp, mul_conj] at hmul
  have hJ : jacobiSum χ χ ∈ GaussianInt.toComplex.range :=
    Subring.sum_mem _ fun x _ ↦
      mul_mem (apply_mem_gaussianInt hχ4 x) (apply_mem_gaussianInt hχ4 (1 - x))
  obtain ⟨g, hg⟩ := RingHom.mem_range.mp hJ
  rw [← hg, ← GaussianInt.intCast_complex_norm] at hmul
  have hnorm : g.norm = (p : ℤ) := by exact_mod_cast hmul
  exact ⟨g.re.natAbs, g.im.natAbs, by
    simpa [GaussianInt.natAbs_norm_eq, sq] using congrArg Int.natAbs hnorm⟩
