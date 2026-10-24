/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Data.Set.Card

/-!
# Bipartite multigraphs

A multigraph is *bipartite* with parts `s` and `t` when they are disjoint and every edge joins a
vertex of `s` to a vertex of `t` (`Graph.IsBipartiteWith`). Its edges can then be counted from
either side: the numbers of edges at the vertices of `s` add up to the number of edges, and so do
the numbers of edges at the vertices of `t` (`Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq`).
This is the multigraph counterpart of `SimpleGraph.isBipartiteWith_sum_degrees_eq`. Mathlib's
multigraphs have no degrees yet, so the edges at a vertex are counted through its incidence set,
in which a loop would count once; a bipartite multigraph has no loops.

This file is intended for `Mathlib/Combinatorics/Graph/Bipartite.lean`.
-/

@[expose] public section

open Finset

namespace Graph

variable {α β : Type*} {G : Graph α β} {s t : Set α}

/-- A multigraph is **bipartite** with parts `s` and `t` when they are disjoint and every edge
joins a vertex of `s` to a vertex of `t`. -/
structure IsBipartiteWith (G : Graph α β) (s t : Set α) : Prop where
  /-- The two parts are disjoint. -/
  disjoint : Disjoint s t
  /-- Every edge joins a vertex of `s` to a vertex of `t`. -/
  mem_or_mem_of_isLink ⦃e : β⦄ ⦃x y : α⦄ : G.IsLink e x y → x ∈ s ∧ y ∈ t ∨ x ∈ t ∧ y ∈ s

lemma IsBipartiteWith.symm (h : G.IsBipartiteWith s t) : G.IsBipartiteWith t s :=
  ⟨h.disjoint.symm, fun _ _ _ he ↦ (h.mem_or_mem_of_isLink he).symm⟩

/-- **Counting the edges of a bipartite multigraph from one side.** If the multigraph has finitely
many edges, the numbers of edges at the vertices of `s` add up to the number of edges, since every
edge has exactly one end in `s`. -/
theorem IsBipartiteWith.sum_ncard_incidenceSet {s : Finset α} (h : G.IsBipartiteWith s t)
    (hE : E(G).Finite) : ∑ x ∈ s, (G.incidenceSet x).ncard = E(G).ncard := by
  classical
  have hinc (x : α) :
      G.incidenceSet x = ↑(hE.toFinset.bipartiteAbove (fun x e ↦ G.Inc e x) x) :=
    Set.ext fun e ↦ by simpa using fun he : G.Inc e x ↦ he.edge_mem
  simp_rw [hinc, Set.ncard_coe_finset, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow,
    Set.ncard_eq_toFinset_card _ hE]
  refine (sum_congr rfl fun e he ↦ card_eq_one.mpr ?_).trans (card_eq_sum_ones _).symm
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (hE.mem_toFinset.mp he)
  have key {x y : α} (hxy : G.IsLink e x y) (hx : x ∈ s) (hy : y ∉ s) :
      s.bipartiteBelow (fun x e ↦ G.Inc e x) e = {x} :=
    ext fun z ↦ by
      simp only [mem_bipartiteBelow, mem_singleton]
      refine ⟨fun ⟨hz, hzi⟩ ↦ (hzi.eq_or_eq_of_isLink hxy).resolve_right ?_, ?_⟩
      · rintro rfl
        exact hy hz
      · rintro rfl
        exact ⟨hx, hxy.inc_left⟩
  rcases h.mem_or_mem_of_isLink hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨x, key hxy hx (Set.disjoint_right.mp h.disjoint hy)⟩
  · exact ⟨y, key hxy.symm hy (Set.disjoint_right.mp h.disjoint hx)⟩

/-- **Counting the edges of a bipartite multigraph from either side.** The numbers of edges at the
vertices of `s` and at the vertices of `t` have the same sum, the number of edges. -/
theorem IsBipartiteWith.sum_ncard_incidenceSet_eq {s t : Finset α} (h : G.IsBipartiteWith s t)
    (hE : E(G).Finite) :
    ∑ x ∈ s, (G.incidenceSet x).ncard = ∑ y ∈ t, (G.incidenceSet y).ncard :=
  (h.sum_ncard_incidenceSet hE).trans (h.symm.sum_ncard_incidenceSet hE).symm

end Graph
