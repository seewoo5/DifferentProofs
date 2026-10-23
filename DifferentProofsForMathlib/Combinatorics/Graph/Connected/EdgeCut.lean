/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Combinatorics.Graph.Connected.EdgeCut
import all Mathlib.Combinatorics.Graph.Connected.EdgeCut

/-!
# Minimal separating edge sets are bonds

In a multigraph, let `S` be a set of edges that is minimal among those whose deletion leaves no
chain of edges from a vertex `s` to a vertex `t`, the two being joined beforehand. Then `S` is a
bond, a minimal nonempty edge cut (`Graph.isBond_of_minimal`).

`Relation.ReflTransGen (G.deleteEdges S).Adj` stands in for reachability, since mathlib's
multigraphs have no walks yet. This file is intended for
`Mathlib/Combinatorics/Graph/Connected/EdgeCut.lean`. The edge cuts there are not exposed to
other modules and come without an introduction rule, so this file imports that module in full to
add one, `Graph.isEdgeCut_edgeCut`, which would sit next to `Graph.IsEdgeCut` upstream.
-/

@[expose] public section

open Set

namespace Graph

variable {α β : Type*} {G : Graph α β} {s t : α} {S : Set β}

/-- The edge cut along a set of vertices is an edge cut. -/
lemma isEdgeCut_edgeCut (G : Graph α β) (X : Set α) : G.IsEdgeCut (G.edgeCut X) := ⟨X, rfl⟩

/-- A set closed under a relation contains everything reachable from its members. -/
private lemma mem_of_reflTransGen {r : α → α → Prop} {P : Set α} {x y : α}
    (hP : ∀ ⦃a b⦄, a ∈ P → r a b → b ∈ P) (hx : x ∈ P) (h : Relation.ReflTransGen r x y) :
    y ∈ P := by
  induction h with
  | refl => exact hx
  | tail _ hab ih => exact hP ih hab

/-- Reachability after deleting edges is symmetric. -/
private lemma reflTransGen_deleteEdges_symm {x y : α}
    (h : Relation.ReflTransGen (G.deleteEdges S).Adj x y) :
    Relation.ReflTransGen (G.deleteEdges S).Adj y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact .head hab.symm ih

/-- **A minimal separating set of edges is a bond.** Let `s` and `t` be joined by a chain of
edges, and let `S` be minimal among the sets of edges whose deletion leaves no chain from `s` to
`t`. Then `S` consists of the edges between the vertices still reachable from `s` and the rest,
and no smaller nonempty edge cut lies inside it. -/
theorem isBond_of_minimal (hst : Relation.ReflTransGen G.Adj s t)
    (hS : Minimal (fun S ↦ ¬ Relation.ReflTransGen (G.deleteEdges S).Adj s t) S) :
    G.IsBond S := by
  set X : Set α := {x | Relation.ReflTransGen (G.deleteEdges S).Adj s x} with hX
  have htX : t ∉ X := hS.prop
  -- Deleting one edge fewer reconnects `s` to `t`.
  have hless : ∀ e ∈ S, Relation.ReflTransGen (G.deleteEdges (S \ {e})).Adj s t := by
    intro e he
    by_contra hcon
    exact (hS.2 hcon sdiff_subset he).2 rfl
  -- Every edge of `S` joins a vertex of `X` to a vertex reachable from `t`.
  have hlink : ∀ e ∈ S, ∃ u w, G.IsLink e u w ∧ u ∈ X ∧
      Relation.ReflTransGen (G.deleteEdges S).Adj t w := by
    intro e he
    have hcut : e ∈ G.edgeCut X := by
      by_contra hcut
      refine htX (mem_of_reflTransGen (fun a b ha ⟨f, hfab, hf⟩ ↦ ?_) Relation.ReflTransGen.refl
        (hless e he))
      by_cases hfS : f ∈ S
      · obtain rfl : f = e := by simpa [hfS] using hf
        by_contra hb
        exact hcut ⟨a, b, hfab, ha, hb⟩
      · exact ha.tail ⟨f, hfab, hfS⟩
    obtain ⟨u, w, huw, hu, hw⟩ := hcut
    refine ⟨u, w, huw, hu, ?_⟩
    have hP : t ∈ X ∪ {x | Relation.ReflTransGen (G.deleteEdges S).Adj w x} := by
      refine mem_of_reflTransGen (fun a b ha ⟨f, hfab, hf⟩ ↦ ?_) (.inl Relation.ReflTransGen.refl)
        (hless e he)
      by_cases hfS : f ∈ S
      · obtain rfl : f = e := by simpa [hfS] using hf
        rcases huw.eq_and_eq_or_eq_and_eq hfab with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · exact .inr Relation.ReflTransGen.refl
        · exact .inl hu
      · exact ha.imp (fun ha ↦ ha.tail ⟨f, hfab, hfS⟩) fun ha ↦ ha.tail ⟨f, hfab, hfS⟩
    exact reflTransGen_deleteEdges_symm (hP.resolve_left htX)
  have hcutX : G.edgeCut X = S := by
    refine Subset.antisymm (fun e ⟨u, w, huw, hu, hw⟩ ↦ ?_) fun e he ↦ ?_
    · by_contra he
      exact hw (hu.tail ⟨e, huw, he⟩)
    · obtain ⟨u, w, huw, hu, hw⟩ := hlink e he
      exact ⟨u, w, huw, hu, fun hwX ↦ htX (hwX.trans (reflTransGen_deleteEdges_symm hw))⟩
  refine ⟨⟨hcutX ▸ G.isEdgeCut_edgeCut X, ?_⟩, ?_⟩
  · rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hS.prop (by rwa [deleteEdges_empty])
  · rintro C ⟨⟨Y, rfl⟩, e₀, he₀⟩ hCS e he
    -- Steps avoiding `S` never cross the cut `edgeCut Y ⊆ S`.
    have hstep : ∀ ⦃a b⦄, (G.deleteEdges S).Adj a b → (a ∈ Y ↔ b ∈ Y) := by
      rintro a b ⟨f, hfab, hf⟩
      by_contra hab
      exact hf (hCS ((hfab.mem_edgeCut_iff).mpr (by tauto)))
    have hreach : ∀ ⦃a b⦄, Relation.ReflTransGen (G.deleteEdges S).Adj a b →
        (a ∈ Y ↔ b ∈ Y) := by
      intro a b h
      induction h with
      | refl => exact Iff.rfl
      | tail _ hbc ih => exact ih.trans (hstep hbc)
    have hside : ∀ f ∈ S, f ∈ G.edgeCut Y ↔ ¬ (s ∈ Y ↔ t ∈ Y) := by
      intro f hf
      obtain ⟨u, w, huw, hu, hw⟩ := hlink f hf
      rw [huw.mem_edgeCut_iff, ← hreach hu, ← hreach hw]
      tauto
    exact (hside e he).mpr ((hside e₀ (hCS he₀)).mp he₀)

end Graph
