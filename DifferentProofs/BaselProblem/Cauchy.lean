module

public import DifferentProofs.BaselProblem.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Real Complex Finset Polynomial Filter Topology

namespace BaselProblem.Cauchy

private lemma I_pow_two_mul (m : ℕ) : (I : ℂ) ^ (2 * m) = (-1) ^ m := by
  rw [pow_mul, I_sq]

private lemma I_pow_two_mul_add_one (j : ℕ) : (I : ℂ) ^ (2 * j + 1) = (-1) ^ j * I := by
  rw [pow_succ, I_pow_two_mul]

/-- De Moivre expansion of `sin ((2n+1)θ)` as an odd polynomial in `sin θ` and `cos θ`. -/
lemma sin_two_mul_add_one (n : ℕ) (θ : ℝ) :
    Real.sin ((2 * n + 1) * θ) =
      ∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * Nat.choose (2 * n + 1) (2 * j + 1)
        * Real.cos θ ^ (2 * (n - j)) * Real.sin θ ^ (2 * j + 1) := by
  have hL : Real.sin ((2 * n + 1) * θ)
      = ((Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * I) ^ (2 * n + 1)).im := by
    rw [← Complex.exp_mul_I, ← Complex.exp_nat_mul,
      show ((2 * n + 1 : ℕ) : ℂ) * ((θ : ℂ) * I) = (((2 * n + 1 : ℕ) * θ : ℝ) : ℂ) * I by
        push_cast; ring,
      Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, Complex.I_im, Complex.I_re, mul_zero, mul_one, add_zero, zero_add]
    push_cast
    ring_nf
  rw [hL, ← Complex.ofReal_cos, ← Complex.ofReal_sin, add_pow, Complex.im_sum]
  refine (Finset.sum_of_injOn (fun j ↦ 2 * (n - j)) ?_ ?_ ?_ ?_).symm
  · intro a ha b hb hab
    grind
  · intro j hj
    grind
  · intro i hi hni
    rw [mem_range] at hi
    have hodd : Odd i := by
      rw [← Nat.not_even_iff_odd]
      rintro ⟨m, rfl⟩
      exact hni ⟨n - m, by simp only [coe_range, Set.mem_Iio]; lia, by simp only []; lia⟩
    obtain ⟨m, rfl⟩ := hodd
    rw [show 2 * n + 1 - (2 * m + 1) = 2 * (n - m) by lia, mul_pow, ← Complex.ofReal_pow,
      I_pow_two_mul, show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_mul, add_zero]
  · intro j hj
    rw [mem_range] at hj
    have hsymm : Nat.choose (2 * n + 1) (2 * (n - j)) = Nat.choose (2 * n + 1) (2 * j + 1) := by
      rw [← Nat.choose_symm (by lia)]
      congr 1
      lia
    rw [show 2 * n + 1 - 2 * (n - j) = 2 * j + 1 by lia, mul_pow, ← Complex.ofReal_pow,
      I_pow_two_mul_add_one, show ((-1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num, hsymm]
    simp only [← Complex.ofReal_pow, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]
    ring

/-- The degree-`n` polynomial whose roots are `(cot (kπ/(2n+1)))²` for `k = 1, …, n`. -/
noncomputable def cotPoly (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C ((-1 : ℝ) ^ j * Nat.choose (2 * n + 1) (2 * j + 1)) * X ^ (n - j)

/-- Evaluating `cotPoly` at `(cot θ)²` recovers `sin ((2n+1)θ) / sin θ ^ (2n+1)`. -/
lemma cotPoly_eval (n : ℕ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    (cotPoly n).eval (Real.cot θ ^ 2) * Real.sin θ ^ (2 * n + 1) = Real.sin ((2 * n + 1) * θ) := by
  rw [Real.cot_eq_cos_div_sin, sin_two_mul_add_one, cotPoly, eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [mem_range] at hj
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [← pow_mul, div_pow, show 2 * n + 1 = 2 * (n - j) + (2 * j + 1) by lia, pow_add]
  field_simp

lemma cotPoly_coeff (n d : ℕ) (hd : d ≤ n) :
    (cotPoly n).coeff d = (-1 : ℝ) ^ (n - d) * Nat.choose (2 * n + 1) (2 * (n - d) + 1) := by
  rw [cotPoly, finsetSum_coeff, Finset.sum_eq_single (n - d)]
  · rw [coeff_C_mul, coeff_X_pow, if_pos (by lia), mul_one]
  · intro j hj hjd
    rw [mem_range] at hj
    rw [coeff_C_mul, coeff_X_pow, if_neg (by lia), mul_zero]
  · intro h; exact absurd (mem_range.mpr (by lia)) h

lemma cotPoly_coeff_eq_zero (n d : ℕ) (hd : n < d) : (cotPoly n).coeff d = 0 := by
  rw [cotPoly, finsetSum_coeff, Finset.sum_eq_zero]
  intro j hj
  rw [mem_range] at hj
  rw [coeff_C_mul, coeff_X_pow, if_neg (by lia), mul_zero]

lemma cotPoly_natDegree (n : ℕ) : (cotPoly n).natDegree = n := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun d hd ↦ cotPoly_coeff_eq_zero n d hd)
    (le_natDegree_of_ne_zero ?_)
  rw [cotPoly_coeff n n le_rfl]
  simp only [Nat.sub_self, pow_zero, one_mul, mul_zero, zero_add, Nat.choose_one_right]
  exact Nat.cast_ne_zero.mpr (by lia)

lemma cotPoly_leadingCoeff (n : ℕ) : (cotPoly n).leadingCoeff = (2 * n + 1 : ℝ) := by
  rw [leadingCoeff, cotPoly_natDegree, cotPoly_coeff n n le_rfl]
  simp [Nat.choose_one_right]

lemma cotPoly_ne_zero (n : ℕ) : cotPoly n ≠ 0 := by
  rw [← leadingCoeff_ne_zero, cotPoly_leadingCoeff]
  positivity

/-- The angle `kπ/(2n+1)` lies in `(0, π/2)` for `1 ≤ k ≤ n`. -/
lemma theta_mem (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) :
    0 < (k : ℝ) * π / (2 * n + 1) ∧ (k : ℝ) * π / (2 * n + 1) < π / 2 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk2
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pi_pos]

/-- `(cot (kπ/(2n+1)))²` is a root of `cotPoly n` for `1 ≤ k ≤ n`. -/
lemma cotPoly_eval_eq_zero (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) :
    (cotPoly n).eval (Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2) = 0 := by
  obtain ⟨hpos, hlt⟩ := theta_mem n k hk1 hk2
  have hsin : Real.sin ((k : ℝ) * π / (2 * n + 1)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hpos (hlt.trans (by linarith [pi_pos]))).ne'
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have key := cotPoly_eval n ((k : ℝ) * π / (2 * n + 1)) hsin
  rw [show (2 * (n : ℝ) + 1) * ((k : ℝ) * π / (2 * n + 1)) = (k : ℝ) * π by field_simp,
    Real.sin_nat_mul_pi] at key
  exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ hsin)

/-- Distinctness of the roots: `k ↦ (cot (kπ/(2n+1)))²` is injective on `{1, …, n}`. -/
lemma cotSq_injOn (n : ℕ) :
    Set.InjOn (fun k : ℕ ↦ Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2) ↑(Finset.Icc 1 n) := by
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  obtain ⟨ha0, hapos⟩ := theta_mem n a ha.1 ha.2
  obtain ⟨hb0, hbpos⟩ := theta_mem n b hb.1 hb.2
  set α := (a : ℝ) * π / (2 * n + 1) with hα
  set β := (b : ℝ) * π / (2 * n + 1) with hβ
  have hca : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hapos⟩
  have hcb : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hbpos⟩
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi ha0 (by linarith [pi_pos])
  have hsb : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hb0 (by linarith [pi_pos])
  simp only [Real.cot_eq_cos_div_sin] at hab
  have hbase : Real.cos α / Real.sin α = Real.cos β / Real.sin β := by
    rw [← Real.sqrt_sq (div_pos hca hsa).le, ← Real.sqrt_sq (div_pos hcb hsb).le, hab]
  have htan : Real.tan α = Real.tan β := by
    have h : (Real.tan α)⁻¹ = (Real.tan β)⁻¹ := by
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, inv_div, inv_div]; exact hbase
    exact inv_injective h
  have hαβ : α = β :=
    Real.strictMonoOn_tan.injOn ⟨by linarith [pi_pos], hapos⟩ ⟨by linarith [pi_pos], hbpos⟩ htan
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  rw [hα, hβ] at hαβ
  field_simp at hαβ
  exact_mod_cast hαβ

/-- **Cauchy's identity.** The sum of `(cot (kπ/(2n+1)))²` over `k = 1, …, n` equals `n(2n-1)/3`,
obtained from Vieta's formula applied to `cotPoly n`. -/
lemma cotSq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2 = n * (2 * n - 1) / 3 := by
  classical
  set f : ℕ → ℝ := fun k ↦
    Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2 with hf
  set S : Finset ℝ := (Finset.Icc 1 n).image f with hS
  have hScard : S.card = n := by
    rw [hS, Finset.card_image_of_injOn (cotSq_injOn n), Nat.card_Icc]; lia
  have hle : S.val ≤ (cotPoly n).roots := by
    rw [Multiset.le_iff_count]
    intro x
    by_cases hx : x ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup hx, Multiset.one_le_count_iff_mem,
        mem_roots (cotPoly_ne_zero n)]
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_Icc] at hk
      exact cotPoly_eval_eq_zero n k hk.1 hk.2
    · rw [Multiset.count_eq_zero.mpr (by simpa using hx)]; exact Nat.zero_le _
  have hcard : (cotPoly n).roots.card ≤ S.val.card := by
    rw [show S.val.card = n from hScard]
    exact (card_roots' _).trans_eq (cotPoly_natDegree n)
  have hroots : S.val = (cotPoly n).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hsplit : Splits (cotPoly n) := by
    rw [splits_iff_card_roots, ← hroots, cotPoly_natDegree]; exact hScard
  have hvieta := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [cotPoly_leadingCoeff, ← hroots] at hvieta
  have hnext : (cotPoly n).nextCoeff = -(Nat.choose (2 * n + 1) 3 : ℝ) := by
    rw [nextCoeff, if_neg (by rw [cotPoly_natDegree]; lia), cotPoly_natDegree,
      cotPoly_coeff n (n - 1) (by lia), show n - (n - 1) = 1 by lia]
    norm_num
  rw [hnext] at hvieta
  have hsumeq : S.val.sum = ∑ k ∈ Finset.Icc 1 n, f k := by
    rw [hS, Finset.image_val_of_injOn (cotSq_injOn n)]; rfl
  have hchoose : (6 : ℝ) * (Nat.choose (2 * n + 1) 3 : ℝ)
      = (2 * (n : ℝ) - 1) * (2 * n) * (2 * n + 1) := by
    have hnat : 6 * Nat.choose (2 * n + 1) 3 = (2 * n - 1) * (2 * n) * (2 * n + 1) := by
      have h := Nat.descFactorial_eq_factorial_mul_choose (2 * n + 1) 3
      have hval : Nat.descFactorial (2 * n + 1) 3 = (2 * n - 1) * (2 * n) * (2 * n + 1) := by
        simp only [Nat.descFactorial, Nat.sub_zero, Nat.mul_one,
          show 2 * n + 1 - 2 = 2 * n - 1 by lia, show 2 * n + 1 - 1 = 2 * n by lia]
        ring
      rw [hval] at h
      simp only [Nat.factorial] at h
      lia
    have := congrArg (Nat.cast (R := ℝ)) hnat
    push_cast [Nat.cast_sub (by lia : 1 ≤ 2 * n)] at this
    linarith [this]
  have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hv : (Nat.choose (2 * n + 1) 3 : ℝ) = (2 * (n : ℝ) + 1) * S.val.sum := by linarith [hvieta]
  have h6s : 6 * S.val.sum = (2 * (n : ℝ) - 1) * (2 * n) :=
    mul_left_cancel₀ h2n (by linear_combination (-6 : ℝ) * hv + hchoose)
  rw [← hsumeq]
  linear_combination h6s / 6

/-- For `x ∈ (0, π/2)`, `cot²x < 1/x²`. -/
lemma cotSq_lt_inv_sq (x : ℝ) (hx0 : 0 < x) (hx : x < π / 2) : Real.cot x ^ 2 < 1 / x ^ 2 := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hx⟩
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
  have htan : x < Real.tan x := Real.lt_tan hx0 hx
  rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at htan
  have h1 : Real.cos x / Real.sin x < 1 / x := by rw [div_lt_div_iff₀ hsin hx0]; nlinarith [htan]
  rw [Real.cot_eq_cos_div_sin, ← one_div_pow]
  exact pow_lt_pow_left₀ h1 (div_pos hcos hsin).le two_ne_zero

/-- For `x ∈ (0, π/2)`, `1/x² < 1 + cot²x` (right half of the squeeze; `csc² = 1 + cot²`). -/
lemma inv_sq_lt_one_add_cotSq (x : ℝ) (hx0 : 0 < x) (hx : x < π / 2) :
    1 / x ^ 2 < 1 + Real.cot x ^ 2 := by
  have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [pi_pos])
  have hsinlt : Real.sin x < x := Real.sin_lt hx0
  have hcsc : 1 + Real.cot x ^ 2 = 1 / Real.sin x ^ 2 := by
    rw [Real.cot_eq_cos_div_sin, div_pow]
    field_simp
    linarith [Real.sin_sq_add_cos_sq x]
  rw [hcsc]
  exact one_div_lt_one_div_of_lt (by positivity) (pow_lt_pow_left₀ hsinlt hsin.le two_ne_zero)

/-- A linear-over-linear ratio with matching leading coefficients tends to `1`. -/
private lemma tendsto_lin_ratio (a : ℝ) :
    Tendsto (fun n : ℕ ↦ (a + 2 * (n : ℝ)) / (1 + 2 * (n : ℝ))) atTop (𝓝 1) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have := tendsto_add_mul_div_add_mul_atTop_nhds a 1 2 h2
  rwa [div_self h2] at this

/-- Each squeeze bound `π² · (n(2n-1)/3 + c·n) / (2n+1)²` converges to `π²/6`. -/
private lemma tendsto_basel_bound (c : ℝ) :
    Tendsto (fun n : ℕ ↦ π ^ 2 * ((n : ℝ) * (2 * n - 1) / 3 + c * n) / (2 * n + 1) ^ 2)
      atTop (𝓝 (π ^ 2 / 6)) := by
  have key : Tendsto (fun n : ℕ ↦
      π ^ 2 / 6 * ((0 + 2 * (n : ℝ)) / (1 + 2 * n)) * (((3 * c - 1) + 2 * (n : ℝ)) / (1 + 2 * n)))
      atTop (𝓝 (π ^ 2 / 6)) := by
    have := ((tendsto_const_nhds (x := π ^ 2 / 6)).mul (tendsto_lin_ratio 0)).mul
      (tendsto_lin_ratio (3 * c - 1))
    simpa using this
  refine key.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (1 : ℝ) + 2 * (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem BaselProblem_Cauchy : BaselProblem := by
  have hsummable := summable_one_div_nat_pow.mpr one_lt_two
  set L := ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ 2 with hLdef
  set D : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ^ 2 with hDdef
  have hD_eq : ∀ n, D n = ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 := fun n ↦ by
    have hins : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      lia
    rw [hDdef, hins, Finset.sum_insert (by simp)]; simp
  have hDL : Tendsto D atTop (𝓝 L) := by
    have hpart : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, (1 : ℝ) / (k : ℝ) ^ 2)
        atTop (𝓝 L) := hsummable.hasSum.tendsto_sum_nat
    have hshift := hpart.comp (tendsto_add_atTop_nat 1)
    exact hshift.congr fun n ↦ (hD_eq n).symm
  have hrel : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) * π / (2 * n + 1)) ^ 2
      = (2 * (n : ℝ) + 1) ^ 2 / π ^ 2 * D n := by
    intro n
    rw [hDdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_Icc] at hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have h2n : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [pi_ne_zero]
  set g : ℕ → ℝ := fun n ↦ π ^ 2 * ((n : ℝ) * (2 * n - 1) / 3) / (2 * n + 1) ^ 2 with hgdef
  set h : ℕ → ℝ := fun n ↦ π ^ 2 * ((n : ℝ) * (2 * n - 1) / 3 + n) / (2 * n + 1) ^ 2 with hhdef
  have hgD : ∀ n, g n ≤ D n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hgdef, hDdef]
    have hne : (Finset.Icc 1 n).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
    have hlt : ∑ k ∈ Finset.Icc 1 n,
        Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2
        < ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) * π / (2 * n + 1)) ^ 2 := by
      refine Finset.sum_lt_sum_of_nonempty hne fun k hk ↦ ?_
      rw [Finset.mem_Icc] at hk
      obtain ⟨h0, h2⟩ := theta_mem n k hk.1 hk.2
      exact cotSq_lt_inv_sq _ h0 h2
    rw [cotSq_sum n hn, hrel n] at hlt
    rw [hgdef, div_le_iff₀ (by positivity : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ 2)]
    have hπ2 : (0 : ℝ) < π ^ 2 := by positivity
    have key := mul_lt_mul_of_pos_left hlt hπ2
    rw [show π ^ 2 * ((2 * (n : ℝ) + 1) ^ 2 / π ^ 2 * D n) = (2 * (n : ℝ) + 1) ^ 2 * D n by
      field_simp] at key
    nlinarith [key]
  have hDh : ∀ n, D n ≤ h n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hhdef, hDdef]
    have hne : (Finset.Icc 1 n).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hn⟩⟩
    have hlt : ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℝ) * π / (2 * n + 1)) ^ 2 < ∑ k ∈ Finset.Icc 1 n,
        (1 + Real.cot ((k : ℝ) * π / (2 * n + 1)) ^ 2) := by
      refine Finset.sum_lt_sum_of_nonempty hne fun k hk ↦ ?_
      rw [Finset.mem_Icc] at hk
      obtain ⟨h0, h2⟩ := theta_mem n k hk.1 hk.2
      exact inv_sq_lt_one_add_cotSq _ h0 h2
    rw [hrel n, Finset.sum_add_distrib, Finset.sum_const, cotSq_sum n hn, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at hlt
    rw [hhdef, le_div_iff₀ (by positivity : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ 2)]
    have hπ2 : (0 : ℝ) < π ^ 2 := by positivity
    have key := mul_lt_mul_of_pos_left hlt hπ2
    rw [show π ^ 2 * ((2 * (n : ℝ) + 1) ^ 2 / π ^ 2 * D n) = (2 * (n : ℝ) + 1) ^ 2 * D n by
      field_simp] at key
    nlinarith [key]
  have hgπ : Tendsto g atTop (𝓝 (π ^ 2 / 6)) := by grind [tendsto_basel_bound 0]
  have hhπ : Tendsto h atTop (𝓝 (π ^ 2 / 6)) := by grind [tendsto_basel_bound 1]
  have hDπ : Tendsto D atTop (𝓝 (π ^ 2 / 6)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hgπ hhπ hgD hDh
  change L = π ^ 2 / 6
  exact tendsto_nhds_unique hDL hDπ

end BaselProblem.Cauchy
