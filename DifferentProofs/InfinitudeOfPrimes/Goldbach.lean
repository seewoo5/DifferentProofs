module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section


def Fermat (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1

lemma Fermat_gt_two (n : ℕ) : Fermat n ≥ 2 := by
  have : 1 ≤ 2 ^ (2 ^ n) := Nat.one_le_two_pow
  unfold Fermat; lia

lemma Fermat_odd (n : ℕ) : Odd (Fermat n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos n).ne'
  exact ⟨2 ^ k, by unfold Fermat; rw [hk, pow_succ]; ring⟩

lemma Fermat_recurrence (n : ℕ) :
    Fermat (n + 1) = ∏ k ∈ Finset.range (n + 1), Fermat k + 2 := by
  have hprod : ∀ m, ∏ k ∈ Finset.range m, Fermat k = Fermat m - 2 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, Fermat, Fermat, mul_comm,
          (show 2 ^ 2 ^ m + 1 - 2 = 2 ^ 2 ^ m - 1 by lia), ← Nat.sq_sub_sq]
      ring_nf
      lia
  rw [hprod, Nat.sub_add_cancel (Fermat_gt_two _)]

lemma Fermat_coprime (n : ℕ) :
    (Fermat (n + 1)).Coprime (∏ k ∈ Finset.range (n + 1), Fermat k) := by
  rw [Fermat_recurrence n, add_comm, Nat.coprime_add_self_left, Nat.coprime_two_left]
  exact Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
    (fun k _ => Fermat_odd k)

lemma Fermat_pairwise_coprime : Pairwise (fun m n => (Fermat m).Coprime (Fermat n)) := by
  intro m n hmn
  wlog h : m < n with H
  · exact (H hmn.symm (by lia)).symm
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by lia⟩
  exact (Fermat_coprime k).symm.coprime_dvd_left
    (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by lia)))

theorem InfinitudeOfPrimes_Goldbach : InfinitudeOfPrimes := by
  apply Set.infinite_of_injective_forall_mem (f := fun n => (Fermat n).minFac)
  · intro m n (h : (Fermat m).minFac = (Fermat n).minFac)
    by_contra hmn
    have hp : (Fermat m).minFac.Prime :=
      Nat.minFac_prime (by have := Fermat_gt_two m; lia)
    exact hp.not_dvd_one <| Fermat_pairwise_coprime hmn ▸
      Nat.dvd_gcd (Nat.minFac_dvd _) (h.symm ▸ Nat.minFac_dvd _)
  · exact fun n => Nat.minFac_prime (by have := Fermat_gt_two n; lia)
