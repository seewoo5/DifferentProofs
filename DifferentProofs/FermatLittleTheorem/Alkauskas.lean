module

import Architect
public import DifferentProofs.FermatLittleTheorem.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic

/-!
# Fermat's Little Theorem via Alkauskas' formal product expansion

This is a faithful formalization of G. Alkauskas, *A curious proof of Fermat's little theorem*
(arXiv:0801.0805). Notably it uses **no** binomial theorem, group theory, or Frobenius
endomorphism — only the unique expansion of an integer power series into a formal product and a
logarithmic-derivative coefficient comparison.

## The argument

Fix `d` and work in `ℤ⟦X⟧`. Consider the rational power series
$$ f(x) = \frac{1-(d+1)x}{1-dx} = 1 - x - \sum_{n\ge 1} d^n x^{n+1}. $$
Because `f` has constant term `1` it is a unit of `ℤ⟦X⟧`, so its inverse `invOfUnit f 1` is again an
*integer* power series. Therefore `f` expands uniquely as a formal product
$$ f(x) = \prod_{n\ge 1}(1 - a_n x^n), \qquad a_n \in \mathbb{Z}, $$
where the integers `a_n` are produced by an inductive coefficient-matching algorithm using only
integer arithmetic (`exists_intExpansion`). This integrality is the entire content of the proof.

Define the negated logarithmic derivative `W g := -(x · g'/g)`, which stays in `ℤ⟦X⟧` because `g` is
a unit. It is additive on products (`W_mul`, `W_prod`) and odd on inverses (`W_invOfUnit`). Direct
computation gives the coefficient of `xᴺ`:
* from `f`: `(d+1)ᴺ - dᴺ` (`coeff_W_f`);
* from a single factor `1 - c·xⁿ`: `n · c^{N/n}` when `n ∣ N` (`coeff_W_oneSubMonomial`).

For a prime `p`, summing the factor contributions over the divisors `{1, p}` of `p` gives the
coefficient `1 + p·a_p` from the product side (`coeff_W_partialProduct`). Since `f` and the partial
product agree up to degree `p` they share the `xᵖ`-coefficient (`coeff_W_congr`), whence
$$ (d+1)^p - d^p = 1 + p\,a_p, \qquad a_p \in \mathbb{Z}, $$
so `p ∣ (d+1)^p - d^p - 1` (`alkauskas_step`). Telescoping over `d` yields `aᵖ ≡ a (mod p)`.
-/

@[expose] public section

open PowerSeries

namespace FermatLittleTheorem.Alkauskas

/-- The negated formal logarithmic derivative `W g = -(X · g' · g⁻¹)`.
Defined for every `g`; the lemmas below assume `constantCoeff g = 1`, which makes `invOfUnit g 1`
the genuine inverse and keeps everything inside `ℤ⟦X⟧`. -/
private noncomputable def W (g : ℤ⟦X⟧) : ℤ⟦X⟧ := -(X * (d⁄dX ℤ g * invOfUnit g 1))

/-- Alkauskas' series `f_d(x) = (1-(d+1)x)/(1-dx)`, written as a product of two units of `ℤ⟦X⟧`. -/
private noncomputable def f (d : ℤ) : ℤ⟦X⟧ := (1 - C (d + 1) * X) * invOfUnit (1 - C d * X) 1

/-! ### Constant-coefficient bookkeeping (units of `ℤ⟦X⟧`) -/

/-- A factor `1 - c·Xⁿ` with `n ≥ 1` has constant term `1`. -/
private lemma constantCoeff_oneSubMonomial (c : ℤ) {n : ℕ} (hn : 0 < n) :
    constantCoeff (1 - C c * X ^ n : ℤ⟦X⟧) = 1 := by simp [hn.ne']

/-- `f d` has constant term `1`. -/
private lemma constantCoeff_f (d : ℤ) : constantCoeff (f d) = 1 := by simp [f]

/-- The partial product is a unit (constant term `1`). -/
private lemma constantCoeff_partialProduct (a : ℕ → ℤ) (N : ℕ) :
    constantCoeff (∏ n ∈ Finset.Icc 1 N, (1 - C (a n) * X ^ n) : ℤ⟦X⟧) = 1 := by
  rw [map_prod]
  exact Finset.prod_eq_one fun n hn => constantCoeff_oneSubMonomial (a n) (Finset.mem_Icc.mp hn).1

/-! ### Algebraic properties of `W` -/

/-- `W` is additive on products of units: `W (g*h) = W g + W h`. -/
private lemma W_mul {g h : ℤ⟦X⟧} (hg : constantCoeff g = 1) (hh : constantCoeff h = 1) :
    W (g * h) = W g + W h := by
  have egh : constantCoeff (g * h) = ((1 : ℤˣ) : ℤ) := by simp [hg, hh]
  have hg1 : g * invOfUnit g 1 = 1 := mul_invOfUnit g 1 (by simp [hg])
  have hh1 : h * invOfUnit h 1 = 1 := mul_invOfUnit h 1 (by simp [hh])
  have hne : (g * h : ℤ⟦X⟧) ≠ 0 := fun h0 => by simp [h0] at egh
  have invprod : invOfUnit (g * h) 1 = invOfUnit g 1 * invOfUnit h 1 :=
    mul_left_cancel₀ hne <| by
      rw [mul_invOfUnit (g * h) 1 egh, mul_mul_mul_comm, hg1, hh1, one_mul]
  have key : (g * d⁄dX ℤ h + h * d⁄dX ℤ g) * (invOfUnit g 1 * invOfUnit h 1)
      = d⁄dX ℤ g * invOfUnit g 1 + d⁄dX ℤ h * invOfUnit h 1 := by
    linear_combination (d⁄dX ℤ h * invOfUnit h 1) * hg1 + (d⁄dX ℤ g * invOfUnit g 1) * hh1
  simp only [W, (d⁄dX ℤ).leibniz, smul_eq_mul, invprod, key, mul_add, neg_add]

/-- `W 1 = 0`, since the derivative of `1` vanishes. -/
private lemma W_one : W (1 : ℤ⟦X⟧) = 0 := by simp [W]

/-- `W` turns the inverse of a unit into a negation: `W (invOfUnit g 1) = - W g`. -/
private lemma W_invOfUnit {g : ℤ⟦X⟧} (hg : constantCoeff g = 1) :
    W (invOfUnit g 1) = - W g := by
  have hci : constantCoeff (invOfUnit g 1) = 1 := by simp [constantCoeff_invOfUnit]
  have hmul := W_mul hg hci
  rw [mul_invOfUnit g 1 (by rw [Units.val_one]; exact hg), W_one] at hmul
  linear_combination -hmul

/-- `W` is additive on finite products of units: `W (∏ gᵢ) = ∑ W gᵢ`. -/
private lemma W_prod {ι : Type*} (s : Finset ι) (g : ι → ℤ⟦X⟧)
    (hg : ∀ i ∈ s, constantCoeff (g i) = 1) :
    W (∏ i ∈ s, g i) = ∑ i ∈ s, W (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W_one]
  | @insert a s ha ih =>
      have hcs : ∀ i ∈ s, constantCoeff (g i) = 1 :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
          W_mul (hg a (Finset.mem_insert_self a s))
            (by rw [map_prod]; exact Finset.prod_eq_one hcs), ih hcs]

/-! ### Coefficient computations -/

/-- The inverse of `1 - c·Xⁿ` is the geometric series `∑ c^j X^{nj}`. -/
private lemma invOfUnit_oneSubMonomial (c : ℤ) {n : ℕ} (hn : 0 < n) :
    invOfUnit (1 - C c * X ^ n) 1 = mk (fun k => if n ∣ k then c ^ (k / n) else 0) := by
  set G : ℤ⟦X⟧ := mk (fun k => if n ∣ k then c ^ (k / n) else 0) with hG
  set u : ℤ⟦X⟧ := 1 - C c * X ^ n with hu
  have hcu : constantCoeff u = ((1 : ℤˣ) : ℤ) := by simp [hu, hn.ne']
  have hune : u ≠ 0 := fun h0 => by simp [h0] at hcu
  have huG : u * G = 1 := by
    ext N
    have hsplit : u * G = G - C c * (X ^ n * G) := by rw [hu]; ring
    rw [hsplit, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_one]
    simp only [hG, coeff_mk]
    by_cases hN0 : N = 0
    · subst hN0; simp [hn.ne']
    · rw [if_neg hN0]
      by_cases hdvd : n ∣ N
      · obtain ⟨q, rfl⟩ := hdvd
        have hqpos : 0 < q := Nat.pos_of_ne_zero fun h => hN0 (by rw [h, mul_zero])
        have hsub : n * q - n = n * (q - 1) := (Nat.mul_sub_one n q).symm
        rw [if_pos ⟨q, rfl⟩, if_pos (Nat.le_mul_of_pos_right n hqpos),
            if_pos (hsub ▸ Dvd.intro _ rfl), Nat.mul_div_cancel_left q hn, hsub,
            Nat.mul_div_cancel_left _ hn, ← pow_succ', Nat.sub_add_cancel hqpos, sub_self]
      · rw [if_neg hdvd]
        by_cases hle : n ≤ N
        · rw [if_pos hle, if_neg fun h => hdvd (Nat.sub_add_cancel hle ▸ dvd_add h dvd_rfl),
              mul_zero, sub_zero]
        · rw [if_neg hle, mul_zero, sub_zero]
  exact mul_left_cancel₀ hune ((mul_invOfUnit u 1 hcu).trans huG.symm)

/-- The coefficient of `Xᴺ` in `W (1 - c·Xⁿ)` is `n·c^{N/n}` exactly when `n ∣ N` and `N > 0`. -/
private lemma coeff_W_oneSubMonomial (c : ℤ) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    coeff N (W (1 - C c * X ^ n)) =
      if n ∣ N ∧ 0 < N then (n : ℤ) * c ^ (N / n) else 0 := by
  have hXd : X * d⁄dX ℤ (1 - C c * X ^ n) = -(C (c * (n : ℤ)) * X ^ n) := by
    ext k
    cases k with
    | zero => simp [hn.ne']
    | succ m =>
        rw [coeff_succ_X_mul, coeff_derivative]
        simp only [map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_one,
          Nat.succ_ne_zero, if_false, zero_sub]
        by_cases h : m + 1 = n
        · subst h; simp
        · simp [h]
  have hWu : W (1 - C c * X ^ n) =
      C (c * (n : ℤ)) * X ^ n * mk (fun k => if n ∣ k then c ^ (k / n) else 0) := by
    simp only [W, invOfUnit_oneSubMonomial c hn]
    rw [← mul_assoc, hXd]; ring
  rw [hWu, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_mk]
  by_cases hcond : n ∣ N ∧ 0 < N
  · obtain ⟨⟨q, rfl⟩, hNpos⟩ := hcond
    have hqpos : 0 < q := Nat.pos_of_ne_zero fun h => by simp [h] at hNpos
    have hsub : n * q - n = n * (q - 1) := (Nat.mul_sub_one n q).symm
    rw [if_pos (Nat.le_mul_of_pos_right n hqpos), if_pos ⟨q - 1, hsub⟩,
        if_pos ⟨⟨q, rfl⟩, hNpos⟩, Nat.mul_div_cancel_left q hn, hsub,
        Nat.mul_div_cancel_left _ hn,
        show c ^ q = c * c ^ (q - 1) by rw [← pow_succ', Nat.sub_add_cancel hqpos]]
    ring
  · rw [if_neg hcond]
    have hinner : (if n ≤ N then (if n ∣ (N - n) then c ^ ((N - n) / n) else 0) else 0)
        = (0 : ℤ) := by
      split_ifs with hle hd
      · exact absurd ⟨Nat.sub_add_cancel hle ▸ dvd_add hd dvd_rfl, by omega⟩ hcond
      all_goals rfl
    rw [hinner, mul_zero]

/-- The coefficient of `Xᴺ` (for `N > 0`) in `W (f d)` is `(d+1)ᴺ - dᴺ`. -/
private lemma coeff_W_f (d : ℤ) {N : ℕ} (hN : 0 < N) :
    coeff N (W (f d)) = (d + 1) ^ N - d ^ N := by
  have hlin : ∀ c : ℤ, coeff N (W (1 - C c * X)) = c ^ N := fun c => by
    rw [← pow_one (X : ℤ⟦X⟧), coeff_W_oneSubMonomial c Nat.one_pos N,
        if_pos ⟨one_dvd N, hN⟩, Nat.cast_one, Nat.div_one, one_mul]
  rw [f, W_mul (by simp) (by simp [constantCoeff_invOfUnit]),
      W_invOfUnit (by simp), map_add, map_neg, hlin, hlin, ← sub_eq_add_neg]

private lemma coeff_W_partialProduct {p : ℕ} (hp : p.Prime) (a : ℕ → ℤ) (ha1 : a 1 = 1) :
    coeff p (W (∏ n ∈ Finset.Icc 1 p, (1 - C (a n) * X ^ n))) = 1 + (p : ℤ) * a p := by
  rw [W_prod _ _ (fun n hn => constantCoeff_oneSubMonomial (a n) (Finset.mem_Icc.mp hn).1), map_sum,
      Finset.sum_congr rfl (fun n hn => coeff_W_oneSubMonomial (a n) (Finset.mem_Icc.mp hn).1 p),
      ← Finset.sum_subset (s₁ := {1, p}) (by simp [Finset.insert_subset_iff, hp.one_le])
        (fun x _ hxni => if_neg fun ⟨hxdvd, _⟩ => hxni <| by
          rcases hp.eq_one_or_self_of_dvd x hxdvd with rfl | rfl <;> simp),
      Finset.sum_pair hp.one_lt.ne, if_pos ⟨one_dvd p, hp.pos⟩, if_pos ⟨dvd_refl p, hp.pos⟩,
      ha1, Nat.div_one, Nat.div_self hp.pos, Nat.cast_one, one_pow, mul_one, pow_one]

/-- If `g` and `h` agree up to degree `m`, so do their inverses (strong induction on the
`coeff_invOfUnit` recursion). -/
private lemma coeff_invOfUnit_congr {g h : ℤ⟦X⟧} :
    ∀ m : ℕ, (∀ k ≤ m, coeff k g = coeff k h) →
      coeff m (invOfUnit g 1) = coeff m (invOfUnit h 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro H
    rw [coeff_invOfUnit, coeff_invOfUnit]
    by_cases hm : m = 0
    · simp [hm]
    · rw [if_neg hm, if_neg hm]
      refine congr_arg _ (Finset.sum_congr rfl fun x hx => ?_)
      rw [Finset.mem_antidiagonal] at hx
      split_ifs with hlt
      · rw [H x.1 (by omega), ih x.2 hlt fun k hk => H k (by omega)]
      · rfl

/-- Two unit series agreeing up to degree `p` share the `Xᵖ`-coefficient of their `W`. -/
private lemma coeff_W_congr {g h : ℤ⟦X⟧}
    {p : ℕ} (hp : 0 < p) (H : ∀ k ≤ p, coeff k g = coeff k h) :
    coeff p (W g) = coeff p (W h) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simp only [W, map_neg, coeff_succ_X_mul]
  rw [coeff_mul, coeff_mul]
  refine congr_arg _ (Finset.sum_congr rfl fun x hx => ?_)
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_derivative, coeff_derivative, H (x.1 + 1) (by omega),
      coeff_invOfUnit_congr x.2 fun k hk => H k (by omega)]

/-- The degree-`1` coefficient of `f d` is `-1` (matching `f = 1 - x - ∑ dⁿ xⁿ⁺¹`). -/
private lemma coeff_one_f (d : ℤ) : coeff 1 (f d) = -1 := by
  have hinv : invOfUnit (1 - C d * X) 1 = mk (fun k => d ^ k) := by
    rw [show (1 - C d * X : ℤ⟦X⟧) = 1 - C d * X ^ 1 by rw [pow_one],
        invOfUnit_oneSubMonomial d Nat.one_pos]
    ext k; simp
  rw [f, hinv, show (1 - C (d + 1) * X) * mk (fun k => d ^ k)
        = mk (fun k => d ^ k) - C (d + 1) * (X * mk (fun k => d ^ k)) by ring,
      map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_mk, coeff_mk]
  ring

/-! ### The integer product expansion (heart of the proof) -/

@[blueprint
  "lem:flt-alkauskas-expansion"
  (statement := /-- Let $g \in \mathbb{Z}[[x]]$ be any integer power series of the form
    $g(x) = 1 - x - d x^2 + \sum_{k \ge 3} b_k x^k$ (equivalently, $[x^0] g = 1$ and
    $[x^1] g = -1$). Then for every $N \ge 0$ there is a sequence of integers $(a_n)_{n \ge 1}$
    with $a_1 = 1$ such that $g$ agrees with the partial product
    $\prod_{n=1}^{N}(1 - a_n x^n)$ in every coefficient of degree $k \le N$. -/)
  (hasProof := true)
  (proof := /-- Induct on $N$. For $N = 0$ the empty product is $1$ and $g$ has constant term $1$.
    Suppose integers $a_1, \dots, a_N$ have been chosen so that the partial product $P_N$ matches
    $g$ in all degrees $\le N$. Since $P_N$ has constant term $1$, multiplying by a new factor
    $1 - a_{N+1} x^{N+1}$ leaves every coefficient of degree $\le N$ unchanged and decreases the
    coefficient of $x^{N+1}$ by $a_{N+1}$. Choosing the integer
    $a_{N+1} := [x^{N+1}] P_N - [x^{N+1}] g$ therefore matches degree $N+1$ as well. Every step uses
    only integer arithmetic, so all $a_n$ are integers; this integrality is the entire content of
    the proof. (The value $a_1 = 1$ is forced, since $[x^1] g = -1$.) -/)
  (title := "Integer formal product expansion of $1 - x - dx^2 + \\cdots$")
  (latexEnv := "lemma")]
private lemma exists_intExpansion {g : ℤ⟦X⟧} (hg0 : constantCoeff g = 1)
    (hg1 : coeff 1 g = -1) (N : ℕ) :
    ∃ a : ℕ → ℤ, a 1 = 1 ∧
      ∀ k ≤ N, coeff k g = coeff k (∏ n ∈ Finset.Icc 1 N, (1 - C (a n) * X ^ n)) := by
  induction N with
  | zero =>
    refine ⟨fun _ => 1, rfl, fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    simp [hg0]
  | succ N ih =>
    obtain ⟨a, ha1, hmatch⟩ := ih
    set P : ℤ⟦X⟧ := ∏ n ∈ Finset.Icc 1 N, (1 - C (a n) * X ^ n) with hP
    set c : ℤ := coeff (N + 1) P - coeff (N + 1) g with hc
    have hP0 : coeff 0 P = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, hP]; exact constantCoeff_partialProduct a N
    refine ⟨Function.update a (N + 1) c, ?_, ?_⟩
    · by_cases hN0 : N = 0
      · subst hN0; simp [hc, hP, hg1]
      · rw [Function.update_of_ne (by omega : (1 : ℕ) ≠ N + 1)]; exact ha1
    · intro k hk
      have hQ : (∏ n ∈ Finset.Icc 1 (N + 1), (1 - C (Function.update a (N + 1) c n) * X ^ n))
          = P * (1 - C c * X ^ (N + 1)) := by
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N + 1), Function.update_self, hP]
        refine congr_arg (· * _) (Finset.prod_congr rfl fun n hn => ?_)
        rw [Function.update_of_ne (by have := (Finset.mem_Icc.mp hn).2; omega)]
      rw [hQ, show P * (1 - C c * X ^ (N + 1)) = P - C c * (P * X ^ (N + 1)) by ring,
          map_sub, coeff_C_mul, coeff_mul_X_pow']
      rcases Nat.lt_or_ge k (N + 1) with hlt | hge
      · rw [if_neg (by omega), mul_zero, sub_zero]
        exact hmatch k (by omega)
      · obtain rfl : k = N + 1 := by omega
        rw [if_pos le_rfl, Nat.sub_self, hP0, hc]
        ring

/-! ### Assembling the proof -/

/-- Alkauskas' congruence: `p ∣ (d+1)^p - d^p - 1` for any integer `d` and prime `p`, proved via
the integer product expansion (no binomial theorem / Frobenius). -/
private lemma alkauskas_step (d : ℤ) {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ (d + 1) ^ p - d ^ p - 1 := by
  obtain ⟨a, ha1, hmatch⟩ := exists_intExpansion (constantCoeff_f d) (coeff_one_f d) p
  have key := coeff_W_congr hp.pos hmatch
  rw [coeff_W_f d hp.pos, coeff_W_partialProduct hp a ha1] at key
  exact ⟨a p, by linarith [key]⟩

@[blueprint
  "thm:flt-alkauskas"
  (statement := /-- For any prime $p$ and integer $a$, we have $a^p \equiv a \pmod{p}$. -/)
  (hasProof := true)
  (proof := /-- Working in $\mathbb{Z}[[x]]$, the rational series
    $f(x) = \frac{1-(d+1)x}{1-dx}$ has constant term $1$, hence is a unit, so it expands uniquely
    as a formal product $\prod_{n \ge 1}(1-a_nx^n)$ with \emph{integer} coefficients $a_n$ (the
    coefficients are produced by an inductive integer coefficient-matching algorithm; this
    integrality is the whole point). Taking the formal logarithmic derivative and comparing the
    coefficient of $x^p$ on the rational side, $(d+1)^p - d^p$, with the product side, $1 + p a_p$,
    gives $p \mid (d+1)^p-d^p-1$. Telescoping these consecutive congruences over $d$ yields
    $a^p \equiv a \pmod p$, and the standard reduction gives the integer form. -/)
  (title := "Fermat's Little Theorem using Alkauskas' product expansion")
  (latexEnv := "theorem")]
theorem FermatLittleTheorem_Alkauskas : FermatLittleTheorem := by
  apply FermatLittleTheoremNat_impl_FermatLittleTheorem
  intro p a hp
  induction a with
  | zero => simpa [Nat.zero_pow hp.pos] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD p])
  | succ d ih =>
      refine Nat.ModEq.trans ?_ (Nat.ModEq.add_right 1 ih)
      rw [Nat.modEq_iff_dvd, show (((d ^ p + 1 : ℕ) : ℤ) - ((d + 1) ^ p : ℕ)) =
          -(((d : ℤ) + 1) ^ p - (d : ℤ) ^ p - 1) by push_cast; ring]
      exact (alkauskas_step (d : ℤ) hp).neg_right

end FermatLittleTheorem.Alkauskas
