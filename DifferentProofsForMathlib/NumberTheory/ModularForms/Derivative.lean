/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
  have hrad := one_le_radius_of_hasSum_qExpansion hh hf
  have hw : ‖𝕢 h τ‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  obtain ⟨r, hwr, hr1⟩ := exists_between hw
  -- Differentiate `∑ cₘ wᵐ` term by term on the disc of radius `r`.
  have hderiv := hasSum_deriv_of_summable_norm (F := fun m v ↦ c m * v ^ m)
    (U := Metric.ball 0 r)
    (summable_norm_mul_pow_of_hasSum_qExpansion hh hf ((norm_nonneg _).trans hwr.le) hr1)
    (fun m ↦ (by fun_prop : Differentiable ℂ _).differentiableOn) Metric.isOpen_ball
    (fun m v hv ↦ by
      rw [norm_mul, norm_pow]
      gcongr
      exact (mem_ball_zero_iff.mp hv).le)
    (mem_ball_zero_iff.mpr hwr)
  have hsum : (fun v ↦ ∑' m, c m * v ^ m) = p.sum := by
    ext v
    exact (FormalMultilinearSeries.ofScalars_sum_eq c v).symm
  rw [hsum] at hderiv
  -- The chain rule for `f = p.sum ∘ q` gives `D f τ = (q / h) · p.sum' q`.
  have hpd : DifferentiableAt ℂ p.sum (𝕢 h τ) := by
    refine (p.hasFPowerSeriesOnBall (zero_lt_one.trans_le hrad)).differentiableOn.differentiableAt
      (Metric.isOpen_eball.mem_nhds (Metric.mem_eball.mpr (lt_of_lt_of_le ?_ hrad)))
    simpa only [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one] using hw
  have hD : D f τ = 𝕢 h τ / h * deriv p.sum (𝕢 h τ) := by
    have hcomp : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] p.sum ∘ 𝕢 h := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      simpa only [comp_apply, ofComplex_apply_of_im_pos hz] using
        eq_sum_ofScalars_of_hasSum_qExpansion hf ⟨z, hz⟩
    rw [normalizedDerivOfComplex, hcomp.deriv_eq,
      (hpd.hasDerivAt.comp (τ : ℂ) (Periodic.hasDerivAt_qParam h τ)).deriv]
    have := two_pi_I_ne_zero
    field_simp
  rw [hD]
  convert hderiv.mul_left (𝕢 h τ / h) using 2 with m
  rw [((hasDerivAt_pow m _).const_mul (c m)).deriv]
  rcases m with _ | m
  · simp only [CharP.cast_eq_zero, zero_div, zero_mul, pow_zero, smul_eq_mul, mul_one, zero_tsub,
      mul_zero]
  · simp only [smul_eq_mul, add_tsub_cancel_right]
    push_cast
    ring

end Derivative
