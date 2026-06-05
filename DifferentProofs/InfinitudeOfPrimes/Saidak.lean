module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Tactic.Ring
public import DifferentProofs.InfinitudeOfPrimes.Defs

@[expose] public section


def a : ℕ → ℕ
  | 0 => 2
  | n + 1 => a n * (a n + 1)

lemma a_ge_two : ∀ n, 2 ≤ a n
  | 0 => le_rfl
  | n + 1 => (Nat.mul_le_mul (a_ge_two n) (by lia : 1 ≤ a n + 1)).trans_eq' rfl

lemma a_primeFactors_card_ge (n : ℕ) : n + 1 ≤ (a n).primeFactors.card := by
  induction n with
  | zero => simp [a, Nat.Prime.primeFactors Nat.prime_two]
  | succ n ih =>
    have h2 := a_ge_two n
    have hpos : 1 ≤ (a n + 1).primeFactors.card :=
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr (by lia))
    have hco : Nat.Coprime (a n) (a n + 1) := by simp [Nat.Coprime]
    rw [show a (n + 1) = a n * (a n + 1) from rfl, Nat.primeFactors_mul (by lia) (by lia),
      Finset.card_union_of_disjoint hco.disjoint_primeFactors]
    lia

theorem InfinitudeOfPrimes_Saidak : InfinitudeOfPrimes := fun hfin => by
  have h1 : (a hfin.toFinset.card).primeFactors.card ≤ hfin.toFinset.card :=
    Finset.card_le_card fun _ hp => hfin.mem_toFinset.mpr (Nat.prime_of_mem_primeFactors hp)
  have h2 := a_primeFactors_card_ge hfin.toFinset.card
  lia
