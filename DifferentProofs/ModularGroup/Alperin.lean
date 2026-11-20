module

public import DifferentProofs.ModularGroup.Defs
public import DifferentProofsForMathlib.GroupTheory.Coprod.CoprodI
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The modular group is a free product: Alperin's ping-pong proof

We prove that `PSL(2, ℤ) = SL(2, ℤ) / {±1}` is isomorphic to the free product `C₂ ∗ C₃` of a
cyclic group of order two and a cyclic group of order three, following R. C. Alperin,
*PSL₂(ℤ) = ℤ₂ ∗ ℤ₃*, Amer. Math. Monthly 100 (1993), no. 4, 385–386, as presented in the blog
post [An elementary application of ping-pong lemma](https://chiasme.wordpress.com/2015/03/08/an-elementary-application-of-ping-pong-lemma/).

Instead of the action of `PSL(2, ℤ)` on the hyperbolic plane, Alperin uses its action on the
irrational numbers by the Möbius transformations `x ↦ (a x + b) / (c x + d)`. Here it acts on
`OnePoint ℝ = ℝ ∪ {∞}` through mathlib's action of `GL(2, ℝ)`. Take the generators

* `B = S = !![0, -1; 1, 0]`, which acts by `x ↦ -1 / x` and has order two, and
* `C = T S = !![1, -1; 1, 0]`, which acts by `x ↦ 1 - 1 / x` and has order three, so that `C⁻¹`
  acts by `x ↦ 1 / (1 - x)`,

and let `P` and `N` be the sets of positive and of negative irrational numbers. Then `B • P ⊆ N`
and `C • N ⊆ P`, `C⁻¹ • N ⊆ P`, so the ping-pong lemma
(`Monoid.CoprodI.lift_injective_of_ping_pong`) shows that the homomorphism from `C₂ ∗ C₃` sending
the two generators to `B` and `C` is injective. It is surjective, because `S` and `T` generate
`SL(2, ℤ)` (`SpecialLinearGroup.SL2Z_generators`) and `T = C B` in `PSL(2, ℤ)`.

Mathlib's ping-pong lemma is stated for the free product `Monoid.CoprodI` of a family of groups,
here indexed by `Bool`; `Monoid.CoprodI.boolEquivCoprod` identifies it with the binary free
product `C₂ ∗ C₃` of the statement.

The blog post proves the ping-pong step directly: an alternating word of odd length maps `P` into
`N` or `N` into `P`, and one of even length, after conjugation by `B` if necessary, maps `P` into
the irrationals greater than `1` or into those less than `1`. Mathlib's ping-pong lemma, used
here, instead turns a word of even length into one of odd length by conjugating it with an element
of the factor of order three.
-/

@[expose] public section

open Matrix SpecialLinearGroup OnePoint Monoid.CoprodI
open scoped MatrixGroups Pointwise Monoid.Coprod

namespace ModularGroup.Alperin

/-! ### The generators `B` and `C` -/

/-- The image of `S = !![0, -1; 1, 0]` in `PSL(2, ℤ)`. -/
abbrev B : PSL(2, ℤ) := S

/-- The image of `T S = !![1, -1; 1, 0]` in `PSL(2, ℤ)`. -/
abbrev C : PSL(2, ℤ) := ↑(T * S)

lemma coe_neg_one : ((-1 : SL(2, ℤ)) : PSL(2, ℤ)) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr <| Subgroup.mem_center_iff.mpr fun _ ↦ by
    rw [mul_neg_one, neg_one_mul]

lemma B_sq : B ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, show S ^ 2 = -1 by decide, coe_neg_one]

lemma C_pow_three : C ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, show (T * S) ^ 3 = -1 by decide, coe_neg_one]

lemma C_mul_B : C * B = T := by
  rw [← QuotientGroup.mk_mul, show T * S * S = -1 * T by decide, QuotientGroup.mk_mul, coe_neg_one,
    one_mul]

/-! ### The action on `ℝ ∪ {∞}` by Möbius transformations -/

/-- `PSL(2, ℤ)` acts on `ℝ ∪ {∞}` by the Möbius transformations of `GL(2, ℝ)`; the central
elements of `SL(2, ℤ)` are scalar matrices, so they act trivially. -/
noncomputable scoped instance : MulAction PSL(2, ℤ) (OnePoint ℝ) :=
  .compHom _ <| QuotientGroup.lift _
    ((MulAction.toPermHom (GL (Fin 2) ℝ) (OnePoint ℝ)).comp (mapGL ℝ)) fun z hz ↦ by
      obtain ⟨r, hr, hz⟩ := mem_center_iff.mp hz
      have hr0 : (r : ℝ) ≠ 0 := by rintro h; simp_all
      ext x
      cases x <;> simp [smul_infty_eq_ite, smul_some_eq_ite, ← hz, hr0, intCast_apply]

/-- The matrix `!![a, b; c, d]` sends `x` to `(a x + b) / (c x + d)`, or to `∞` if the
denominator vanishes. -/
lemma smul_coe_eq_ite (g : SL(2, ℤ)) (x : ℝ) : (g : PSL(2, ℤ)) • (x : OnePoint ℝ) =
    if (g 1 0 : ℝ) * x + g 1 1 = 0 then ∞ else ↑((g 0 0 * x + g 0 1) / (g 1 0 * x + g 1 1)) :=
  smul_some_eq_ite

lemma B_smul {x : ℝ} (hx : x ≠ 0) : B • (x : OnePoint ℝ) = ↑(-1 / x) := by
  rw [smul_coe_eq_ite, coe_S]
  simp [hx]

lemma C_smul {x : ℝ} (hx : x ≠ 0) : C • (x : OnePoint ℝ) = ↑(1 - 1 / x) := by
  rw [smul_coe_eq_ite, show ↑(T * S) = !![1, -1; 1, 0] by decide]
  simp [hx, add_div, neg_div, sub_eq_add_neg]

lemma C_inv_smul {x : ℝ} (hx : x ≠ 1) : C⁻¹ • (x : OnePoint ℝ) = ↑(1 / (1 - x)) := by
  rw [inv_smul_eq_iff, C_smul (one_div_ne_zero (sub_ne_zero.mpr hx.symm)), one_div_one_div,
    sub_sub_cancel]

/-! ### The ping-pong sets -/

/-- The positive irrational numbers. -/
def P : Set (OnePoint ℝ) := (↑) '' {x : ℝ | Irrational x ∧ 0 < x}

/-- The negative irrational numbers. -/
def N : Set (OnePoint ℝ) := (↑) '' {x : ℝ | Irrational x ∧ x < 0}

lemma disjoint_P_N : Disjoint P N :=
  (Set.disjoint_image_iff coe_injective).mpr <| Set.disjoint_left.mpr fun _ hx hy ↦ by
    linarith [hx.2, hy.2]

lemma B_smul_P : B • P ⊆ N := by
  rintro _ ⟨_, ⟨x, ⟨hx, hx0⟩, rfl⟩, rfl⟩
  exact ⟨_, ⟨by simpa only [neg_div, one_div] using hx.inv.neg,
    div_neg_of_neg_of_pos (by norm_num) hx0⟩, (B_smul hx0.ne').symm⟩

lemma C_smul_N : C • N ⊆ P := by
  rintro _ ⟨_, ⟨x, ⟨hx, hx0⟩, rfl⟩, rfl⟩
  exact ⟨_, ⟨by simpa only [one_div, Int.cast_one] using hx.inv.intCast_sub 1,
    by linarith [one_div_neg.mpr hx0]⟩, (C_smul hx0.ne).symm⟩

lemma C_inv_smul_N : C⁻¹ • N ⊆ P := by
  rintro _ ⟨_, ⟨x, ⟨hx, hx0⟩, rfl⟩, rfl⟩
  exact ⟨_, ⟨by simpa only [one_div, Int.cast_one] using (hx.intCast_sub 1).inv,
    one_div_pos.mpr (by linarith)⟩, (C_inv_smul (by linarith)).symm⟩

/-! ### The free product -/

/-- The homomorphism `Multiplicative (ZMod n) →* G` sending `ofAdd 1` to an element `g` with
`g ^ n = 1`. -/
noncomputable def cycHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft <| ZMod.lift n
    ⟨zmultiplesHom _ (Additive.ofMul g), congrArg Additive.ofMul ((zpow_natCast g n).trans hg)⟩

lemma cycHom_ofAdd_intCast {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) (k : ℤ) :
    cycHom n g hg (.ofAdd k) = g ^ k :=
  congrArg Additive.toMul (ZMod.lift_coe _ _ _)

/-- The two factors of the free product, `C₂` at `false` and `C₃` at `true`. -/
abbrev Cyc : Bool → Type
  | false => Multiplicative (ZMod 2)
  | true => Multiplicative (ZMod 3)

instance (i : Bool) : Group (Cyc i) := by cases i <;> infer_instance

/-- The generator of `C₂` goes to `B`, and that of `C₃` to `C`. -/
noncomputable def toPSL : ∀ i, Cyc i →* PSL(2, ℤ)
  | false => cycHom 2 B B_sq
  | true => cycHom 3 C C_pow_three

/-- The ping-pong sets: `N` for `C₂`, whose nontrivial element maps `P` into `N`, and `P` for
`C₃`, whose nontrivial elements map `N` into `P`. -/
def pingPongSet : Bool → Set (OnePoint ℝ)
  | false => N
  | true => P

lemma toPSL_false_one : toPSL false (.ofAdd 1) = B :=
  (cycHom_ofAdd_intCast 2 B B_sq 1).trans (zpow_one B)

lemma toPSL_true_one : toPSL true (.ofAdd 1) = C :=
  (cycHom_ofAdd_intCast 3 C C_pow_three 1).trans (zpow_one C)

lemma toPSL_true_two : toPSL true (.ofAdd 2) = C⁻¹ := by
  rw [show (2 : ZMod 3) = ((-1 : ℤ) : ZMod 3) by decide]
  exact (cycHom_ofAdd_intCast 3 C C_pow_three (-1)).trans (zpow_neg_one C)

/-- **Ping-pong**: the homomorphism `C₂ ∗ C₃ →* PSL(2, ℤ)` is injective. -/
theorem lift_toPSL_injective : Function.Injective (lift toPSL) := by
  refine lift_injective_of_ping_pong toPSL (.inr ⟨true, by simp⟩) pingPongSet ?_ ?_ ?_
  · rintro (_ | _)
    exacts [⟨_, -√2, ⟨irrational_sqrt_two.neg, neg_neg_of_pos (by positivity)⟩, rfl⟩,
      ⟨_, √2, ⟨irrational_sqrt_two, by positivity⟩, rfl⟩]
  · rintro (_ | _) (_ | _) hij
    exacts [absurd rfl hij, disjoint_P_N.symm, disjoint_P_N, absurd rfl hij]
  · rintro (_ | _) (_ | _) hij h hh
    · exact absurd rfl hij
    · obtain rfl : h = .ofAdd 1 := by revert h; decide
      exact toPSL_false_one ▸ B_smul_P
    · obtain rfl | rfl : h = .ofAdd 1 ∨ h = .ofAdd 2 := by revert h; decide
      exacts [toPSL_true_one ▸ C_smul_N, toPSL_true_two ▸ C_inv_smul_N]
    · exact absurd rfl hij

/-- The homomorphism `C₂ ∗ C₃ →* PSL(2, ℤ)` is surjective, because `S` and `T = C B` generate
`SL(2, ℤ)`. -/
theorem lift_toPSL_surjective : Function.Surjective (lift toPSL) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℤ))),
    ← SL2Z_generators, MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
  have hB : B ∈ (lift toPSL).range := ⟨of (i := false) (.ofAdd 1),
    (lift_of _ _).trans toPSL_false_one⟩
  rintro _ (rfl | rfl)
  · exact hB
  · rw [QuotientGroup.mk'_apply, ← C_mul_B]
    exact mul_mem ⟨of (i := true) (.ofAdd 1), (lift_of _ _).trans toPSL_true_one⟩ hB

/-- `PSL(2, ℤ) ≃* C₂ ∗ C₃`. -/
noncomputable def mulEquiv : PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3) :=
  (MulEquiv.ofBijective _ ⟨lift_toPSL_injective, lift_toPSL_surjective⟩).symm.trans
    boolEquivCoprod

end ModularGroup.Alperin

/-- **Alperin's proof** that the modular group is the free product `C₂ ∗ C₃`. -/
theorem ModularGroupFreeProduct_Alperin : ModularGroupFreeProduct :=
  ⟨ModularGroup.Alperin.mulEquiv⟩
