module

public import DifferentProofs.CombinatorialIdentities.Defs

@[expose] public section

open Finset

namespace CombinatorialIdentities.DoubleCounting

/-- The largest element of a nonempty finite set of naturals is one of its elements. -/
private lemma sup_id_mem {S : Finset ℕ} (hS : S.Nonempty) : S.sup id ∈ S := by
  simpa using Finset.sup_mem_of_nonempty (f := id) hS

/-- A `(k + 1)`-element set of naturals has largest element at least `k`, since it is contained
in `{0, 1, …, S.sup id}`. -/
private lemma le_sup_id {S : Finset ℕ} {k : ℕ} (hcard : #S = k + 1) : k ≤ S.sup id := by
  have hsub : S ⊆ range (S.sup id + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
  simpa [hcard] using Finset.card_le_card hsub

/-- Deleting the largest element is a bijection from the `(k + 1)`-element subsets of
`{0, 1, …, n + k}` whose largest element is `m` onto the `k`-element subsets of `{0, 1, …, m - 1}`;
reinserting `m` is its inverse. Hence there are `m.choose k` of the former. -/
private lemma card_fiber (n k m : ℕ) (hm : m ≤ n + k) :
    #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} = m.choose k := by
  rw [show m.choose k = #((range m).powersetCard k) by simp]
  refine Finset.card_nbij' (fun S => S.erase m) (fun T => insert m T) ?_ ?_ ?_ ?_ <;>
    simp only [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_powersetCard, and_imp]
  · rintro S - hcard hsup
    have hmS : m ∈ S := hsup ▸ sup_id_mem (Finset.card_pos.mp (by omega))
    refine ⟨fun x hx => ?_, by simp [Finset.card_erase_of_mem hmS, hcard]⟩
    have hxm : x ≤ m := hsup ▸ Finset.le_sup (f := id) (Finset.mem_of_mem_erase hx)
    exact Finset.mem_range.mpr (lt_of_le_of_ne hxm (Finset.ne_of_mem_erase hx))
  · rintro T hsub hcard
    have hmT : m ∉ T := fun h => absurd (Finset.mem_range.mp (hsub h)) (lt_irrefl m)
    refine ⟨⟨Finset.insert_subset (Finset.mem_range.mpr (by omega)) fun x hx => ?_, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hsub hx); omega)
    · rw [Finset.card_insert_of_notMem hmT, hcard]
    · rw [Finset.sup_insert]
      exact sup_eq_left.mpr (Finset.sup_le fun x hx => (Finset.mem_range.mp (hsub hx)).le)
  · rintro S - hcard hsup
    exact Finset.insert_erase (hsup ▸ sup_id_mem (Finset.card_pos.mp (by omega)))
  · rintro T hsub -
    exact Finset.erase_insert fun h => absurd (Finset.mem_range.mp (hsub h)) (lt_irrefl m)

/-- Sorting the `(k + 1)`-element subsets of `{0, 1, …, n + k}` by their largest element. -/
private lemma card_eq_sum_fibers (n k : ℕ) :
    #((range (n + k + 1)).powersetCard (k + 1))
      = ∑ m ∈ Icc k (n + k), #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} := by
  refine Finset.card_eq_sum_card_fiberwise fun S hS => ?_
  simp only [Finset.mem_coe, Finset.mem_powersetCard] at hS
  exact Finset.mem_Icc.mpr ⟨le_sup_id hS.2, Finset.sup_le fun x hx =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS.1 hx))⟩

end CombinatorialIdentities.DoubleCounting

open CombinatorialIdentities.DoubleCounting in
/-- **Hockey-stick identity**, by counting the `(k + 1)`-element subsets of `{0, 1, …, n + k}`
in two ways: directly, and after partitioning them according to their largest element `m`,
which ranges over `k, k + 1, …, n + k`. -/
theorem HockeyStickIdentity_doubleCounting : HockeyStickIdentity := by
  rw [HockeyStickIdentity]
  intro n k
  have hIcc : Icc k (n + k) = Ico k (n + k + 1) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  calc ∑ i ∈ range (n + 1), (i + k).choose k
      = ∑ m ∈ Icc k (n + k), m.choose k := by
        rw [hIcc, Finset.sum_Ico_eq_sum_range]
        simp [show n + k + 1 - k = n + 1 from by omega, Nat.add_comm]
    _ = ∑ m ∈ Icc k (n + k), #{S ∈ (range (n + k + 1)).powersetCard (k + 1) | S.sup id = m} :=
        Finset.sum_congr rfl fun m hm => (card_fiber n k m (Finset.mem_Icc.mp hm).2).symm
    _ = #((range (n + k + 1)).powersetCard (k + 1)) := (card_eq_sum_fibers n k).symm
    _ = (n + k + 1).choose (k + 1) := by simp
