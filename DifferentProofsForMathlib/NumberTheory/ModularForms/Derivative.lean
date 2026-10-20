/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.Derivative

/-!
# The normalized derivative of a `q`-series

Since `D qᵐ = (m / h) qᵐ` for `q = exp (2πiτ / h)` and the normalized derivative
`D = (2πi)⁻¹ d/dτ`, a function `f τ = ∑ cₘ qᵐ` given by a convergent `q`-series has
`D f τ = ∑ (m / h) cₘ qᵐ`: a convergent power series may be differentiated term by term.

This is intended for `Mathlib/NumberTheory/ModularForms/Derivative.lean`.
-/

@[expose] public section

open UpperHalfPlane hiding I
open Complex Filter Function
open scoped Real Topology Manifold

namespace Derivative

variable {f : ℍ → ℂ} {h : ℝ} {c : ℕ → ℂ}

local notation "𝕢" => Periodic.qParam

/-- The `q`-series of `D f` is obtained by differentiating the `q`-series of `f` term by term:
`D (∑ cₘ qᵐ) = ∑ (m / h) cₘ qᵐ`. -/
theorem hasSum_normalizedDerivOfComplex_of_hasSum (hh : 0 < h)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (m / h * c m) • 𝕢 h τ ^ m) (D f τ) := by
  set p := FormalMultilinearSeries.ofScalars ℂ c
  have hq : ‖𝕢 h τ‖ₑ < p.radius := (ofReal_norm (𝕢 h τ) ▸ ENNReal.ofReal_lt_one.2
    (Periodic.norm_qParam_lt_one hh τ.im_pos)).trans_le (one_le_radius_of_hasSum_qExpansion hh hf)
  rw [← hasSum_nat_add_iff' 1, Finset.sum_range_one, Nat.cast_zero, zero_div, zero_mul, zero_smul,
    sub_zero, normalizedDerivOfComplex, HasDerivAt.deriv (((p.hasFDerivAt_sum hq).hasDerivAt.comp _
    (Periodic.hasDerivAt_qParam h τ)).congr_of_eventuallyEq <|
    eventually_of_mem (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos) fun z hz ↦
      (comp_ofComplex_of_im_pos f z hz).trans (eq_sum_ofScalars_of_hasSum_qExpansion hf ⟨z, hz⟩))]
  refine ((((ContinuousLinearMap.apply ℂ ℂ 1).hasSum (p.derivSeries.hasSum (mem_eball_zero_iff.2
    (hq.trans_le p.radius_le_radius_derivSeries)))).mul_right _).mul_left _).congr_fun fun n ↦ ?_
  simp only [p, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_apply,
    ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul, smul_eq_mul, pow_succ]
  field_simp

end Derivative
