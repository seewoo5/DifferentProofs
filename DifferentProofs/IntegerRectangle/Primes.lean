module

public import DifferentProofs.IntegerRectangle.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Nat.Prime.Infinite

/-!
# The integer-rectangle theorem via prime numbers

Wagon's sixth proof (Raphael Robinson). For a prime `p`, count the points of the lattice
`(1/p)ℤ × (1/p)ℤ` inside the *half-open* cell of a rectangle: the count factors as
`(⌊p·x₁⌋ - ⌊p·x₀⌋) · (⌊p·y₁⌋ - ⌊p·y₀⌋)`, one floor difference per side. Because the half-open
cells of a tiling partition the half-open cell of the tiled rectangle exactly
(`IsTiling.iUnion_toSetIoc`), the count is additive over the tiling — Wagon's "scale by `p` and
round the corners" happens here inside the counting, with no auxiliary re-tiling to verify.

A side of integer length `n` contributes the factor `⌊p·x₀ + p·n⌋ - ⌊p·x₀⌋ = p·n`, so each tile
with an integer side has count divisible by `p`. Hence `p` divides the count of `R`, which is a
product of two factors; primality forces `p` to divide one of them, and a side whose floor
difference is `p·m` has length within `1/p` of `m`. So for every prime `p`, some side of `R` is
within `1/p` of an integer; since there are infinitely many primes and a non-integer keeps a fixed
positive distance from `ℤ`, one side of `R` must be an integer.
-/

@[expose] public section

open Finset Set

namespace IntegerRectangle.Primes

/-- The points of the lattice `(1/p)ℤ × (1/p)ℤ` lying in the half-open cell of `S`, recorded by
their integer numerators: the pair `(a, b)` stands for the lattice point `(a/p, b/p)`. -/
noncomputable def latticePoints (p : ℕ) (S : Rectangle) : Finset (ℤ × ℤ) :=
  Finset.Ioc ⌊S.x₀ * p⌋ ⌊S.x₁ * p⌋ ×ˢ Finset.Ioc ⌊S.y₀ * p⌋ ⌊S.y₁ * p⌋

/-- Membership in `latticePoints` is membership of the lattice point in the half-open cell. -/
private lemma mem_latticePoints {p : ℕ} (hp : 0 < p) {S : Rectangle} {ab : ℤ × ℤ} :
    ab ∈ latticePoints p S ↔ ((ab.1 / p : ℝ), (ab.2 / p : ℝ)) ∈ S.toSetIoc := by
  have hp' : (0 : ℝ) < p := by positivity
  simp only [latticePoints, Finset.mem_product, Finset.mem_Ioc, Rectangle.mem_toSetIoc,
    Int.floor_lt, Int.le_floor, lt_div_iff₀ hp', div_le_iff₀ hp']

/-- The lattice count of a rectangle is the product of the floor differences of its sides. -/
private lemma card_latticePoints (p : ℕ) (S : Rectangle) :
    ((latticePoints p S).card : ℤ)
      = (⌊S.x₁ * p⌋ - ⌊S.x₀ * p⌋) * (⌊S.y₁ * p⌋ - ⌊S.y₀ * p⌋) := by
  have hx := Int.floor_mono (mul_le_mul_of_nonneg_right S.hx p.cast_nonneg)
  have hy := Int.floor_mono (mul_le_mul_of_nonneg_right S.hy p.cast_nonneg)
  simp [latticePoints, Int.card_Ioc, hx, hy]

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- **Additivity of the lattice count over a tiling.** The half-open cells of the tiles partition
the half-open cell of `R` (`IsTiling.iUnion_toSetIoc`, `IsTiling.pairwiseDisjoint_toSetIoc`), and
counting lattice points respects exact partitions. This is where Wagon's "scale by `p` and round
all corners" is replaced by counting, with no auxiliary re-tiling. -/
theorem card_latticePoints_eq_sum (hT : IsTiling R T) {p : ℕ} (hp : 0 < p) :
    (latticePoints p R).card = ∑ i, (latticePoints p (T i)).card := by
  classical
  rw [show latticePoints p R = Finset.univ.biUnion (fun i ↦ latticePoints p (T i)) from
      Finset.ext fun ab ↦ by
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_latticePoints hp,
          ← Set.mem_iUnion, hT.iUnion_toSetIoc],
    Finset.card_biUnion fun i _ j _ hij ↦ Finset.disjoint_left.mpr fun ab hai haj ↦
      Set.disjoint_left.mp (hT.pairwiseDisjoint_toSetIoc hij)
        ((mem_latticePoints hp).mp hai) ((mem_latticePoints hp).mp haj)]

/-- The one-dimensional core: a side of integer length `n`, scaled by `p`, ends at an integer
shift `n·p` of its start, and the shift passes through `⌊·⌋`, leaving floor difference `p·n`. -/
private lemma floor_sub_floor_of_int {p : ℕ} {a b : ℝ} {n : ℤ} (h : b - a = n) :
    ⌊b * p⌋ - ⌊a * p⌋ = p * n := by
  have hb : b * (p : ℝ) = a * p + ((p * n : ℤ) : ℝ) := by
    push_cast
    linear_combination (p : ℝ) * h
  rw [hb, Int.floor_add_intCast, add_sub_cancel_left]

/-- A tile with an integer side has lattice count divisible by `p`: an integer side of length `n`
contributes the floor-difference factor `⌊x·p + n·p⌋ - ⌊x·p⌋ = n·p`. -/
private lemma dvd_card_latticePoints {p : ℕ} (S : Rectangle) (h : S.HasIntegerSide) :
    (p : ℤ) ∣ ((latticePoints p S).card : ℤ) := by
  rw [card_latticePoints]
  obtain ⟨n, hn⟩ | ⟨n, hn⟩ := h
  · exact Dvd.dvd.mul_right ⟨n, floor_sub_floor_of_int hn⟩ _
  · exact Dvd.dvd.mul_left ⟨n, floor_sub_floor_of_int hn⟩ _

/-- A side whose floor-difference factor is `p·m` has length within `1/p` of `m`: scaled by `p`,
the difference is a difference of two floor remainders, each in `[0, 1)`. -/
private lemma abs_sub_lt_of_floor_sub_floor {x₀ x₁ : ℝ} {p : ℕ} (hp : 0 < p) {m : ℤ}
    (h : ⌊x₁ * p⌋ - ⌊x₀ * p⌋ = p * m) : |x₁ - x₀ - m| < 1 / p := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have h' : (⌊x₁ * p⌋ : ℝ) - ⌊x₀ * p⌋ = p * m := by exact_mod_cast h
  rw [lt_div_iff₀ hp', ← abs_of_pos hp', ← abs_mul, abs_lt]
  constructor <;>
    nlinarith [Int.floor_le (x₁ * (p : ℝ)), Int.lt_floor_add_one (x₁ * (p : ℝ)),
      Int.floor_le (x₀ * (p : ℝ)), Int.lt_floor_add_one (x₀ * (p : ℝ))]

/-- **Wagon's claim.** For every prime `p`, some side of the tiled rectangle is within `1/p` of an
integer. -/
theorem exists_side_near_int (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) {p : ℕ}
    (hp : p.Prime) :
    (∃ n : ℤ, |R.width - n| < 1 / p) ∨ (∃ n : ℤ, |R.height - n| < 1 / p) := by
  have hdvd : (p : ℤ) ∣ ((latticePoints p R).card : ℤ) := by
    rw [card_latticePoints_eq_sum hT hp.pos]
    push_cast
    exact Finset.dvd_sum fun i _ ↦ dvd_card_latticePoints (T i) (hsides i)
  rw [card_latticePoints] at hdvd
  exact ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp hdvd).imp
    (fun ⟨m, hm⟩ ↦ ⟨m, abs_sub_lt_of_floor_sub_floor hp.pos hm⟩)
    fun ⟨m, hm⟩ ↦ ⟨m, abs_sub_lt_of_floor_sub_floor hp.pos hm⟩

/-- A real number that is not an integer keeps a fixed positive distance from every integer. -/
private lemma exists_forall_le_abs_sub {x : ℝ} (h : ¬∃ n : ℤ, x = n) :
    ∃ δ > 0, ∀ n : ℤ, δ ≤ |x - n| :=
  ⟨|x - round x|, abs_sub_pos.mpr fun heq ↦ h ⟨round x, heq⟩, round_le x⟩

/-- **Prime-numbers proof** (Robinson) of the integer-rectangle tiling theorem. -/
theorem IntegerRectangleTheorem_Primes : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  by_contra hcon
  rw [Rectangle.HasIntegerSide, not_or] at hcon
  obtain ⟨δw, hδw, hw⟩ := exists_forall_le_abs_sub hcon.1
  obtain ⟨δh, hδh, hh⟩ := exists_forall_le_abs_sub hcon.2
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max ⌈1 / δw⌉₊ ⌈1 / δh⌉₊ + 1)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have key : ∀ δ : ℝ, 0 < δ → ⌈1 / δ⌉₊ < p → 1 / (p : ℝ) < δ := fun δ hδ h₀ ↦ by
    have h₁ : 1 / δ < p := (Nat.le_ceil _).trans_lt (by exact_mod_cast h₀)
    rw [div_lt_iff₀ hδ] at h₁
    rw [div_lt_iff₀ hp']
    linarith [mul_comm (p : ℝ) δ]
  have hpw := key δw hδw (lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hple)
  have hph := key δh hδh (lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hple)
  rcases exists_side_near_int hT hsides hp with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact absurd hn (not_lt.mpr (hpw.le.trans (hw n)))
  · exact absurd hn (not_lt.mpr (hph.le.trans (hh n)))

end IntegerRectangle.Primes
