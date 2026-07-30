module

public import DifferentProofs.IntegerRectangle.Basic
public import DifferentProofsForMathlib.MeasureTheory.Measure.Stieltjes

/-!
# The integer-rectangle theorem via step functions

The step-function entry in Wagon's list, his thirteenth proof, credited there to Hochster and Maté.
The oscillating integrand of the first three proofs is replaced by the sawtooth `{x} = x - ⌊x⌋` —
the identity minus a step function — and integration by a count of integer points. To a rectangle
`S = [a, b] × [c, d]` the proof attaches the number

```
Φ(S) = ({b} - {a}) · ({d} - {c}).
```

The factor `{b} - {a}` vanishes exactly when `b - a ∈ ℤ`, so `Φ(S) = 0` says precisely that `S` has
an integer side. This criterion is sharper than the checkerboard proof's triangle wave, which is
why no "standard position" hypothesis appears here. Granting that `Φ` is *additive* over a tiling,
every tile contributes `0`, hence `Φ(R) = 0` and `R` has an integer side.

Additivity is what the step function buys. Both `x` and `⌊x⌋` are monotone and right-continuous,
hence Stieltjes functions (`StieltjesFunction.id` and `StieltjesFunction.floor`), whose measures are
Lebesgue measure and the counting measure of the integers. So `{b} - {a}` is the *signed* mass
`λ (a, b] - #(ℤ ∩ (a, b])`, and expanding the product `Φ(S)` turns it into a combination of four
honest plane measures of the half-open cell of `S`. Each of those is additive over a tiling by
`IsTiling.measure_toSetIoc`, and `dichotomy` assembles them.

This is the discrete counterpart of the integral engine of `Basic.lean`, and it is stated for an
arbitrary difference of two Stieltjes functions. No integration and no null sets are involved: the
whole proof rides on the exact partition of a tiling into half-open cells.
-/

@[expose] public section

open MeasureTheory Set

namespace IntegerRectangle.StepFunction

variable {ι : Type*} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- The increment of `f - g` across `(a, b]`, for `f` and `g` Stieltjes functions: the signed mass
that `(a, b]` receives from the difference of the two associated measures. -/
noncomputable def incr (f g : StieltjesFunction ℝ) (a b : ℝ) : ℝ := (f b - g b) - (f a - g a)

/-- The increment is the difference of the two Stieltjes masses of `(a, b]`; both are finite. -/
private lemma incr_eq_toReal (f g : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    incr f g a b = (f.measure (Ioc a b)).toReal - (g.measure (Ioc a b)).toReal := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.2 (f.mono hab)),
    ENNReal.toReal_ofReal (sub_nonneg.2 (g.mono hab))]
  exact sub_sub_sub_comm ..

/-- **Real-valued additivity over a tiling** of the mass coming from a product of two Stieltjes
measures: `IsTiling.measure_toSetIoc` together with finiteness of that mass on a cell. -/
private lemma sum_toReal_prod (hT : IsTiling R T) (f g : StieltjesFunction ℝ) :
    ((f.measure.prod g.measure) R.toSetIoc).toReal =
      ∑ i, ((f.measure.prod g.measure) (T i).toSetIoc).toReal := by
  have hfin (S : Rectangle) : (f.measure.prod g.measure) S.toSetIoc ≠ ⊤ := by
    rw [Rectangle.toSetIoc, Measure.prod_prod, StieltjesFunction.measure_Ioc,
      StieltjesFunction.measure_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [hT.measure_toSetIoc _, ENNReal.toReal_sum fun i _ ↦ hfin (T i)]

/-- **The product of a rectangle's two increments is a combination of four plane measures** of its
half-open cell, obtained by expanding `(λ - #ℤ) ⊗ (λ - #ℤ)`. This is what makes the product
additive over a tiling. -/
private lemma incr_mul_incr (f g : StieltjesFunction ℝ) (S : Rectangle) :
    incr f g S.x₀ S.x₁ * incr f g S.y₀ S.y₁ =
      ((f.measure.prod f.measure) S.toSetIoc).toReal
        - ((f.measure.prod g.measure) S.toSetIoc).toReal
        - ((g.measure.prod f.measure) S.toSetIoc).toReal
        + ((g.measure.prod g.measure) S.toSetIoc).toReal := by
  simp only [incr_eq_toReal f g S.hx, incr_eq_toReal f g S.hy, Rectangle.toSetIoc,
    Measure.prod_prod, ENNReal.toReal_mul]
  ring

/-- **The product of a rectangle's two increments is additive over a tiling.** Each of the four
plane measures it expands into is additive by `sum_toReal_prod`. -/
private lemma sum_incr_mul (hT : IsTiling R T) (f g : StieltjesFunction ℝ) :
    incr f g R.x₀ R.x₁ * incr f g R.y₀ R.y₁ =
      ∑ i, incr f g (T i).x₀ (T i).x₁ * incr f g (T i).y₀ (T i).y₁ := by
  simp only [incr_mul_incr, sum_toReal_prod hT, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- **The step-function engine.** Let `f` and `g` be Stieltjes functions, so that `f - g` is a
right-continuous function of bounded variation. If `T` tiles `R` and every tile has vanishing
increment of `f - g` across its width or across its height, then so does `R`. This is the
discrete counterpart of `IsTiling.prod_integral_dichotomy`. -/
theorem dichotomy (hT : IsTiling R T) (f g : StieltjesFunction ℝ)
    (htile : ∀ i, incr f g (T i).x₀ (T i).x₁ = 0 ∨ incr f g (T i).y₀ (T i).y₁ = 0) :
    incr f g R.x₀ R.x₁ = 0 ∨ incr f g R.y₀ R.y₁ = 0 :=
  mul_eq_zero.mp <| (sum_incr_mul hT f g).trans <|
    Finset.sum_eq_zero fun i _ ↦ mul_eq_zero.mpr (htile i)

/-- The sawtooth is the difference of the identity and the floor Stieltjes functions, so its
increment across `(a, b]` is `{b} - {a}`. -/
private lemma incr_id_floor (a b : ℝ) :
    incr StieltjesFunction.id StieltjesFunction.floor a b = Int.fract b - Int.fract a := by
  simp only [incr, StieltjesFunction.id_apply, StieltjesFunction.floor_apply, id_eq,
    Int.self_sub_floor]

/-- **The one-dimensional criterion.** The sawtooth increment across `(a, b]` vanishes exactly when
`b - a` is an integer. Unlike the checkerboard's triangle wave this needs no alignment of `a`. -/
private lemma incr_id_floor_eq_zero_iff {a b : ℝ} :
    incr StieltjesFunction.id StieltjesFunction.floor a b = 0 ↔ ∃ n : ℤ, b - a = n := by
  rw [incr_id_floor, sub_eq_zero, Int.fract_eq_fract]

/-- **Step-function proof** (Hochster–Maté) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_StepFunction : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  exact (dichotomy hT StieltjesFunction.id StieltjesFunction.floor fun i ↦ (hsides i).imp
      incr_id_floor_eq_zero_iff.mpr incr_id_floor_eq_zero_iff.mpr).imp
    incr_id_floor_eq_zero_iff.mp incr_id_floor_eq_zero_iff.mp

end IntegerRectangle.StepFunction
