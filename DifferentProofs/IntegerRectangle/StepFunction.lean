module

public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem via step functions

The step-function entry in Wagon's list, his thirteenth proof, credited there to Hochster and
Maté. To a rectangle `S = [a, b] × [c, d]` the proof attaches the number

```
Φ(S) = ({b} - {a}) · ({d} - {c}),      {x} = x - ⌊x⌋,
```

the fg-area of `S` (`IntegerRectangle.fgArea`) for the sawtooth `Int.fract` — the identity minus a
step function — in both coordinates. The sawtooth increment `{b} - {a}` vanishes exactly when
`b - a ∈ ℤ`, so `Φ(S) = 0` says precisely that `S` has an integer side. The fg-area of an
arbitrary pair of functions is additive over a tiling (`IsTiling.sum_fgArea`: refine the tiling
along the graph formed by the tile edges into a grid and telescope, following Wagon). Every tile
contributes `0`, hence `Φ(R) = 0` and `R` has an integer side.

The sawtooth criterion is sharper than the checkerboard proof's triangle wave — it detects
integer differences exactly — which is why no "standard position" hypothesis appears here. The
sawtooth increment also reads as the signed mass `λ (a, b] - #(ℤ ∩ (a, b])` of the difference of
two Stieltjes measures, Lebesgue measure minus the counting measure of the integers; that reading
gives an alternative, measure-theoretic proof of the additivity, but the grid refinement is
Wagon's own argument and needs no measure theory.
-/

@[expose] public section

namespace IntegerRectangle.StepFunction

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **The step-function engine**: the fg-area dichotomy, for arbitrary `f, g : ℝ → ℝ`. If `T`
tiles `R` and every tile has vanishing increment of `f` across its width or of `g` across its
height, then the same dichotomy holds for `R`. This is the discrete counterpart of
`IsTiling.prod_integral_dichotomy`. -/
theorem dichotomy (hT : IsTiling R T) (f g : ℝ → ℝ)
    (htile : ∀ i, f (T i).x₁ - f (T i).x₀ = 0 ∨ g (T i).y₁ - g (T i).y₀ = 0) :
    f R.x₁ - f R.x₀ = 0 ∨ g R.y₁ - g R.y₀ = 0 :=
  mul_eq_zero.mp <| (hT.sum_fgArea f g).symm.trans <|
    Finset.sum_eq_zero fun i _ ↦ mul_eq_zero.mpr (htile i)

/-- **The one-dimensional criterion.** The sawtooth increment across `[a, b]` vanishes exactly
when `b - a` is an integer. Unlike the checkerboard's triangle wave this needs no alignment of
`a`. -/
private lemma fract_sub_eq_zero_iff {a b : ℝ} :
    Int.fract b - Int.fract a = 0 ↔ ∃ n : ℤ, b - a = n := by
  rw [sub_eq_zero, Int.fract_eq_fract]

/-- **Step-function proof** (Hochster–Maté) of the integer-rectangle tiling theorem: the fg-area
dichotomy for the sawtooth `Int.fract` in both coordinates. -/
theorem IntegerRectangleTheorem_StepFunction : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  exact (dichotomy hT Int.fract Int.fract fun i ↦ (hsides i).imp
      fract_sub_eq_zero_iff.mpr fract_sub_eq_zero_iff.mpr).imp
    fract_sub_eq_zero_iff.mp fract_sub_eq_zero_iff.mp

end IntegerRectangle.StepFunction
