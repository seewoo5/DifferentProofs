module

public import DifferentProofs.FermatLittleTheorem.Basic
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.UnitInterval
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open scoped unitInterval

noncomputable def T (n : ℕ) (x : I) : I :=
  if x = 1 then 1 else ⟨Int.fract (n * (x : ℝ)), unitInterval.fract_mem _⟩

@[simp] lemma T_one (n : ℕ) : T n 1 = 1 := by simp [T]

private lemma T_val_of_ne {n : ℕ} {x : I} (hx : x ≠ 1) :
    (T n x : ℝ) = Int.fract ((n : ℝ) * (x : ℝ)) := by simp [T, hx]

private lemma T_ne_one {n : ℕ} {x : I} (hx : x ≠ 1) : T n x ≠ 1 := fun h => by
  have hv : (T n x : ℝ) = 1 := by rw [h]; rfl
  rw [T_val_of_ne hx] at hv
  linarith [Int.fract_lt_one ((n : ℝ) * (x : ℝ))]

lemma T_comp_eq_mul (m n : ℕ) : T m ∘ T n = T (m * n) := by
  funext x
  apply Subtype.ext
  change (T m (T n x) : ℝ) = (T (m * n) x : ℝ)
  by_cases hx : x = 1
  · subst hx; simp
  · rw [T_val_of_ne (T_ne_one hx), T_val_of_ne hx, T_val_of_ne hx]
    have h1 : (m : ℝ) * Int.fract ((n : ℝ) * (x : ℝ)) =
              ((m * n : ℕ) : ℝ) * (x : ℝ) -
              (((m : ℤ) * ⌊(n : ℝ) * (x : ℝ)⌋ : ℤ) : ℝ) := by
      rw [Int.fract]; push_cast; ring
    rw [h1, Int.fract_sub_intCast]

lemma T_num_fp_eq (n : ℕ) (hn : 2 ≤ n) : Nat.card {x : I | T n x = x} = n := by
  have hn1_le : (1 : ℕ) ≤ n := by lia
  have hn1_lt : (1 : ℝ) < n := by exact_mod_cast (by lia : 1 < n)
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn1_ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1_pos
  have hn1_eq : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1_le, Nat.cast_one]
  let toI : Fin n → I := fun j => ⟨(j : ℝ) / ((n : ℝ) - 1), by
    refine ⟨div_nonneg (by positivity) hn1_pos.le, ?_⟩
    rw [div_le_one hn1_pos]
    have h1 : (j : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt j.is_lt
    have h2 : ((j : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    rwa [hn1_eq] at h2⟩
  have hinj : Function.Injective toI := by
    intro j k hjk
    have h1 : (j : ℝ) / ((n : ℝ) - 1) = (k : ℝ) / ((n : ℝ) - 1) := congr_arg Subtype.val hjk
    have h2 : (j : ℝ) = (k : ℝ) := by field_simp at h1; exact h1
    exact Fin.ext (by exact_mod_cast h2)
  have hmaps : ∀ j : Fin n, T n (toI j) = toI j := by
    intro j
    by_cases hj_eq : (j : ℕ) = n - 1
    · have htoI_one : toI j = 1 := by
        apply Subtype.ext
        change (j : ℝ) / ((n : ℝ) - 1) = 1
        rw [show ((j : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) by exact_mod_cast hj_eq, hn1_eq,
            div_self hn1_ne]
      rw [htoI_one, T_one]
    · have hj_lt : (j : ℕ) < n - 1 := lt_of_le_of_ne (Nat.le_sub_one_of_lt j.is_lt) hj_eq
      have hj_lt_real : (j : ℝ) < (n : ℝ) - 1 := by
        have : ((j : ℕ) : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hj_lt
        rwa [hn1_eq] at this
      have htoI_lt_one : ((toI j : I) : ℝ) < 1 := by
        change (j : ℝ) / ((n : ℝ) - 1) < 1
        rw [div_lt_one hn1_pos]; exact hj_lt_real
      have htoI_ne : toI j ≠ 1 := fun h => by
        have hh : ((toI j : I) : ℝ) = 1 := by rw [h]; rfl
        linarith
      apply Subtype.ext
      change (T n (toI j) : ℝ) = ((toI j : I) : ℝ)
      rw [T_val_of_ne htoI_ne]
      change Int.fract ((n : ℝ) * ((j : ℝ) / ((n : ℝ) - 1))) = (j : ℝ) / ((n : ℝ) - 1)
      have key : (n : ℝ) * ((j : ℝ) / ((n : ℝ) - 1)) =
                 ((j : ℕ) : ℝ) + (j : ℝ) / ((n : ℝ) - 1) := by
        field_simp; ring
      rw [key, Int.fract_natCast_add]
      apply Int.fract_eq_self.mpr
      refine ⟨div_nonneg (by positivity) hn1_pos.le, ?_⟩
      rw [div_lt_one hn1_pos]; exact hj_lt_real
  have hsurj : ∀ x : I, T n x = x → ∃ j : Fin n, toI j = x := by
    intro x hx
    by_cases hx1 : x = 1
    · refine ⟨⟨n - 1, by lia⟩, ?_⟩
      apply Subtype.ext
      change ((n - 1 : ℕ) : ℝ) / ((n : ℝ) - 1) = (x : ℝ)
      rw [hn1_eq, div_self hn1_ne]
      exact (congr_arg Subtype.val hx1).symm
    · have hxv_lt : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 (fun h => hx1 (Subtype.ext h))
      have hxv_nn : 0 ≤ (x : ℝ) := x.2.1
      have heq : Int.fract ((n : ℝ) * (x : ℝ)) = (x : ℝ) := by
        have := congr_arg Subtype.val hx
        rw [T_val_of_ne hx1] at this
        exact this
      set k : ℤ := ⌊(n : ℝ) * (x : ℝ)⌋ with hk_def
      have hkx : ((n : ℝ) - 1) * (x : ℝ) = (k : ℝ) := by
        have hf : Int.fract ((n : ℝ) * (x : ℝ)) = (n : ℝ) * (x : ℝ) - (k : ℝ) := rfl
        linarith [heq, hf]
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := by rw [← hkx]; positivity
      have hk_lt : (k : ℝ) < (n : ℝ) - 1 := by
        have hxlt1 : ((n : ℝ) - 1) * (x : ℝ) < (n : ℝ) - 1 := by
          have := mul_lt_mul_of_pos_left hxv_lt hn1_pos
          linarith
        linarith [hkx]
      have hk_int_nn : 0 ≤ k := by exact_mod_cast hk_nn
      have hk_int_lt : k < ((n - 1 : ℕ) : ℤ) := by
        have h1 : (k : ℝ) < ((n - 1 : ℕ) : ℝ) := by rw [hn1_eq]; exact hk_lt
        exact_mod_cast h1
      have hk_toNat_lt : k.toNat < n - 1 := by
        have h := Int.toNat_of_nonneg hk_int_nn
        lia
      refine ⟨⟨k.toNat, by lia⟩, ?_⟩
      apply Subtype.ext
      change ((k.toNat : ℕ) : ℝ) / ((n : ℝ) - 1) = (x : ℝ)
      have hk_toNat_eq : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        rw [show ((k.toNat : ℕ) : ℝ) = (((k.toNat : ℕ) : ℤ) : ℝ) by push_cast; rfl,
            Int.toNat_of_nonneg hk_int_nn]
      rw [hk_toNat_eq, div_eq_iff hn1_ne]
      linarith [hkx]
  let e : Fin n ≃ {x : I | T n x = x} := Equiv.ofBijective
    (fun j => ⟨toI j, hmaps j⟩)
    ⟨fun j k hjk => hinj (congr_arg Subtype.val hjk),
     fun ⟨x, hx⟩ => by
       obtain ⟨j, hj⟩ := hsurj x hx
       exact ⟨j, Subtype.ext hj⟩⟩
  have hcard : Nat.card {x : I | T n x = x} = Nat.card (Fin n) := (Nat.card_congr e).symm
  rw [hcard, Nat.card_fin]

/-- $T_a$ iterated $k$ times equals $T_{a^k}$ (for $k \ge 1$). -/
private lemma T_iterate (a : ℕ) {k : ℕ} (hk : 0 < k) : (T a)^[k] = T (a^k) := by
  induction k with
  | zero => lia
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Function.iterate_succ', ih hm, pow_succ, Nat.mul_comm]
      exact T_comp_eq_mul a (a^m)

private def fixedDiff (a p : ℕ) : Set I := {x | T (a ^ p) x = x} \ {x | T a x = x}

/-- If `x` is fixed by `T_{a^p}` but not by `T_a`, then `T_a x` has the same property. -/
private lemma T_mem_fixed_diff {a p : ℕ} (hp : p.Prime) {x : I}
    (hx_period : T (a ^ p) x = x) (hx_not_fixed : T a x ≠ x) : T a x ∈ fixedDiff a p := by
  rw [fixedDiff]
  constructor
  · calc
      T (a ^ p) (T a x) = (T (a ^ p) ∘ T a) x := rfl
      _ = (T a ∘ T (a ^ p)) x := by rw [T_comp_eq_mul, Nat.mul_comm, T_comp_eq_mul]
      _ = T a x := by
        change T a (T (a ^ p) x) = T a x
        rw [hx_period]
  · intro hy_fixed
    have hy_iter_fixed : T a (T a x) = T a x := by simpa using hy_fixed
    have hxperiod_iter : (T a)^[p] x = x := by
      rw [T_iterate a hp.pos]
      exact hx_period
    have hxeventual : (T a)^[p] x = T a x := by
      rw [← Nat.succ_pred_eq_of_pos hp.pos, Function.iterate_succ_apply]
      exact Function.iterate_fixed hy_iter_fixed (p - 1)
    exact hx_not_fixed (hxeventual.symm.trans hxperiod_iter)

private lemma T_fixed_set_finite {n : ℕ} (hn : 2 ≤ n) :
    ({x : I | T n x = x} : Set I).Finite := by
  rw [← Set.finite_coe_iff]
  exact Nat.finite_of_card_ne_zero (by
    rw [T_num_fp_eq n hn]
    lia)

private lemma fixedDiff_finite {a p : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    (fixedDiff a p).Finite := by
  rw [fixedDiff]
  exact T_fixed_set_finite (ha.trans <| le_self_pow (by lia : 1 ≤ a) hp.ne_zero) |>.diff

private lemma fixedDiff_card {a p : ℕ} (hp : p.Prime) (ha : 2 ≤ a) :
    Nat.card (fixedDiff a p) = a ^ p - a := by
  have hBA : {x : I | T a x = x} ⊆ {x : I | T (a ^ p) x = x} := by
    intro x hx
    have hiter : (T a)^[p] x = x := Function.iterate_fixed hx p
    rwa [T_iterate a hp.pos] at hiter
  rw [Nat.card_coe_set_eq, fixedDiff, Set.ncard_diff hBA (T_fixed_set_finite ha),
      ← Nat.card_coe_set_eq {x : I | T (a ^ p) x = x},
      ← Nat.card_coe_set_eq {x : I | T a x = x},
      T_num_fp_eq (a ^ p) (ha.trans <| le_self_pow (by lia : 1 ≤ a) hp.ne_zero),
      T_num_fp_eq a ha]

private noncomputable def fixedDiffStep (a p : ℕ) (hp : p.Prime) :
    fixedDiff a p → fixedDiff a p := fun x =>
  ⟨T a (x : I), T_mem_fixed_diff hp (by simpa [fixedDiff] using x.2.1)
    (by simpa [fixedDiff] using x.2.2)⟩

private lemma fixedDiffStep_iter_val {a p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, ∀ x : fixedDiff a p,
      (((fixedDiffStep a p hp)^[n] x : fixedDiff a p) : I) = (T a)^[n] (x : I) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (fixedDiffStep a p hp x)]
      rfl

private lemma fixedDiffStep_pow {a p : ℕ} (hp : p.Prime) :
    (fixedDiffStep a p hp)^[p] = id := by
  funext x
  apply Subtype.ext
  calc
    _ = (T a)^[p] (x : I) := fixedDiffStep_iter_val hp p x
    _ = T (a ^ p) (x : I) := by rw [T_iterate a hp.pos]
    _ = (x : I) := by simpa [fixedDiff] using x.2.1

private lemma fixedDiffStep_fixedpointfree {a p : ℕ} (hp : p.Prime) :
    ∀ x : fixedDiff a p, fixedDiffStep a p hp x ≠ x := by
  intro x hx
  exact x.2.2 (by
    simpa [fixedDiff, fixedDiffStep] using
      congr_arg (fun y : fixedDiff a p => (y : I)) hx)

/-- A fixed-point-free permutation whose `p`th power is the identity has cardinality divisible by
`p`, for prime `p`. -/
private lemma prime_dvd_card_of_fixedpointfree_periodic
    {α : Type*} [Finite α] {p : ℕ} (hp : p.Prime) (f : Equiv.Perm α)
    (hpow : f ^ p = 1) (hfix : ∀ x : α, f x ≠ x) :
    p ∣ Nat.card α := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let fZ : ℤ →+ Additive (Equiv.Perm α) := {
    toFun n := Additive.ofMul (f ^ n)
    map_zero' := by simp
    map_add' m n := by
      apply Additive.toMul.injective
      rw [zpow_add]
      rfl }
  have hfZ_p : fZ (p : ℤ) = 0 := by
    apply Additive.toMul.injective
    change f ^ ((p : ℕ) : ℤ) = 1
    simpa using hpow
  let φ : ZMod p →+ Additive (Equiv.Perm α) := ZMod.lift p ⟨fZ, hfZ_p⟩
  letI : AddAction (ZMod p) α := AddAction.compHom α φ
  letI : MulAction (Multiplicative (ZMod p)) α := inferInstance
  have hgen (x : α) : (Multiplicative.ofAdd (1 : ZMod p)) • x = f x := by
    change φ (1 : ZMod p) +ᵥ x = f x
    have hφ_one : φ (1 : ZMod p) = Additive.ofMul f := by
      dsimp [φ]
      simpa [fZ] using (ZMod.lift_coe (n := p) (f := ⟨fZ, hfZ_p⟩) (1 : ℤ))
    rw [hφ_one]
    rfl
  have hfixed_card : Nat.card (MulAction.fixedPoints (Multiplicative (ZMod p)) α) = 0 := by
    rw [Finite.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    exact hfix x.1 ((hgen x.1).symm.trans (x.2 (Multiplicative.ofAdd (1 : ZMod p))))
  have hG : IsPGroup p (Multiplicative (ZMod p)) := IsPGroup.of_card (n := 1) (by simp)
  exact Nat.modEq_zero_iff_dvd.mp <| by
    simpa [hfixed_card] using hG.card_modEq_card_fixedPoints α

private lemma prime_dvd_card_of_fixedpointfree_periodic_map
    {α : Type*} [Finite α] {p : ℕ} (hp : p.Prime) (f : α → α)
    (hpow : f^[p] = id) (hfix : ∀ x : α, f x ≠ x) : p ∣ Nat.card α := by
  have hsucc : (p - 1).succ = p := Nat.succ_pred_eq_of_pos hp.pos
  let fPerm : Equiv.Perm α := ⟨f, f^[p - 1],
    fun x => by rw [← Function.iterate_succ_apply f (p - 1), hsucc]; exact congr_fun hpow x,
    fun x => by rw [← Function.iterate_succ_apply' f (p - 1), hsucc]; exact congr_fun hpow x⟩
  refine prime_dvd_card_of_fixedpointfree_periodic hp fPerm ?_ hfix
  ext x
  rw [← Equiv.Perm.iterate_eq_pow]
  exact congr_fun hpow x

theorem FermatLittleTheorem_Dynamical : FermatLittleTheorem := by
  apply FermatLittleTheoremNat_impl_FermatLittleTheorem
  intro p a hp
  rcases Nat.lt_or_ge a 2 with ha | ha
  · have ha_cases : a = 0 ∨ a = 1 := by lia
    rcases ha_cases with rfl | rfl
    · simpa [Nat.zero_pow hp.pos] using (Nat.ModEq.refl 0 : 0 ≡ 0 [MOD p])
    · simpa using (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD p])
  · classical
    have : Finite (fixedDiff a p) := Set.finite_coe_iff.mpr (fixedDiff_finite hp ha)
    have hcard_dvd : p ∣ Nat.card (fixedDiff a p) :=
      prime_dvd_card_of_fixedpointfree_periodic_map hp (fixedDiffStep a p hp)
        (fixedDiffStep_pow hp) (fixedDiffStep_fixedpointfree hp)
    exact ((Nat.modEq_iff_dvd' (le_self_pow (by lia : 1 ≤ a) hp.ne_zero)).mpr
      (by simpa [fixedDiff_card hp ha] using hcard_dvd)).symm
