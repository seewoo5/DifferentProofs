module

public import DifferentProofs.IrrationalSqrtTwo.Defs
public import DifferentProofsForMathlib.NumberTheory.CongruentNumber

/-!
# Irrationality of `√2` from Fermat's theorem that `1` is not a congruent number

A positive rational number is a congruent number if it is the area of a right triangle with
rational sides, and Fermat proved that `1` is not one (`not_isCongruentNumber_one`). If `√2` were
rational, then `√2`, `√2` and `2` would be the sides of a rational right triangle with area `1`.

This is the remark after Theorem 2.1 of Keith Conrad's notes *The congruent number problem*
(<https://kconrad.math.uconn.edu/blurbs/ugradnumthy/congnumber.pdf>), recalled in Markus
Scheuer's answer <https://math.stackexchange.com/a/1332960>.
-/

@[expose] public section

/-- **The irrationality of `√2`**, from Fermat's theorem that `1` is not a congruent number: the
isosceles right triangle with legs `√2` would have rational sides and area `1`. -/
theorem IrrationalSqrtTwo_CongruentNumber : IrrationalSqrtTwo := by
  rintro ⟨q, hq⟩
  have hq2 : q ^ 2 = 2 := by
    exact_mod_cast show (q : ℝ) ^ 2 = 2 by rw [hq, Real.sq_sqrt zero_le_two]
  have hq0 : 0 < q := by exact_mod_cast hq ▸ Real.sqrt_pos.mpr two_pos
  exact not_isCongruentNumber_one
    ⟨q, q, 2, hq0, hq0, two_pos, by linear_combination 2 * hq2, by linear_combination hq2 / 2⟩
