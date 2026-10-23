/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import DifferentProofsForMathlib.Combinatorics.Graph.Connected.Basic
public import DifferentProofsForMathlib.Combinatorics.Graph.Connected.EdgeCut
public import DifferentProofsForMathlib.Combinatorics.Graph.Cycle
public import DifferentProofsForMathlib.Combinatorics.Graph.DartPairing
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Combinatorial maps and planar duality

A **combinatorial map** describes a multigraph embedded in a closed orientable surface through its
darts, or half-edges. An involution `edgePerm` exchanges the two darts of each edge, and a
permutation `vertexPerm` turns each dart to the next one counterclockwise around its vertex. The
vertices, edges and faces of the embedding are the orbits of `vertexPerm`, of `edgePerm` and of
`facePerm = vertexPerm * edgePerm`: following a dart to the other end of its edge and turning there
walks along the boundary of a face. `CombinatorialMap V E F D` names the vertices, edges and faces
by the types `V`, `E` and `F`, through labelings of the darts whose fibres are exactly the orbits.

The **graph** of a map has the vertices and edges of the map, and its **dual graph** has the faces
as vertices, the edge of a dart joining the faces of its two darts: both are graphs of the
underlying `DartPairing`, for the labelings of the darts by vertices and by faces
(`DartPairing.labelGraph`). A map is **planar**, an embedding in the sphere, when its graph is
connected and its Euler characteristic `#V - #E + #F` is `2`; by the classification of surfaces
this is the usual combinatorial definition of planarity.

## Main results

* `CombinatorialMap.IsPlanar.isCycle_of_isBond`: in a planar map, the edges of a bond of the graph,
  a minimal nonempty edge cut, form a cycle of the dual graph.
* `CombinatorialMap.isPlanar_of_forall_isEdgeCut`: a map with a connected graph is planar as soon
  as every edge set meeting each face evenly is an edge cut of the graph.

## Proof

Over `ZMod 2`, the edge cuts of the graph form the image of its coboundary `ℤ₂^V → ℤ₂^E`, and the
edge sets meeting every face evenly form the kernel of the boundary `ℤ₂^E → ℤ₂^F` of the dual
graph; both maps come from incidence matrices. In any map the image lies in the kernel
(`CombinatorialMap.isEven_of_isEdgeCut`): walking round a face crosses an edge cut an even number
of times. For a connected map they have dimensions `#V - 1` and `#E - #F + 1`, so Euler's formula
makes them equal. A bond is then a minimal nonempty edge set meeting every face evenly, and such a
set is a cycle of the dual graph (`CombinatorialMap.isCycle_of_minimal`): the rest of it joins the
two ends of any of its edges, by the handshake lemma
(`DartPairing.even_card_of_forall_adj_restrict`), and a shortest path between them closes up with
the edge to a cycle that, being even, is all of it.

This file is intended for `Mathlib/Combinatorics/Graph/CombinatorialMap.lean`.

## References

* B. Mohar and C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press, 2001.
-/

@[expose] public section

open Finset Matrix

/-- A **combinatorial map** with vertices `V`, edges `E` and faces `F` on the darts `D`: the
rotation `vertexPerm` around the vertices and the fixed-point-free involution `edgePerm` pairing
the two darts of each edge, together with labelings `vert`, `edge` and `face` of the darts whose
fibres are the orbits of `vertexPerm`, of `edgePerm` and of `vertexPerm * edgePerm`. The
involution and the edge labeling form the underlying `DartPairing`. -/
structure CombinatorialMap (V E F D : Type*) extends DartPairing E D where
  /-- The rotation, turning each dart to the next one around its vertex. -/
  vertexPerm : Equiv.Perm D
  /-- The vertex of a dart. -/
  vert : D → V
  /-- The face of a dart. -/
  face : D → F
  vert_eq_vert_iff (d d' : D) : vert d = vert d' ↔ vertexPerm.SameCycle d d'
  face_eq_face_iff (d d' : D) : face d = face d' ↔ (vertexPerm * edgePerm).SameCycle d d'
  vert_surjective : Function.Surjective vert
  face_surjective : Function.Surjective face

namespace CombinatorialMap

variable {V E F D W : Type*} (M : CombinatorialMap V E F D)

/-- The face permutation `vertexPerm * edgePerm`: its orbits are the faces. -/
def facePerm : Equiv.Perm D := M.vertexPerm * M.edgePerm

lemma facePerm_apply (d : D) : M.facePerm d = M.vertexPerm (M.edgePerm d) := rfl

lemma vert_vertexPerm (d : D) : M.vert (M.vertexPerm d) = M.vert d :=
  (M.vert_eq_vert_iff _ _).mpr (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))

lemma face_facePerm (d : D) : M.face (M.facePerm d) = M.face d :=
  (M.face_eq_face_iff _ _).mpr (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))

lemma vert_facePerm (d : D) : M.vert (M.facePerm d) = M.vert (M.edgePerm d) :=
  M.vert_vertexPerm _

/-! ### The graph and the dual graph -/

/-- The graph of the map: the darts labeled by their vertices. -/
def graph : Graph V E := M.labelGraph M.vert

/-- The dual graph of the map: its vertices are the faces, and the edge of a dart joins the faces
of its two darts. -/
def dualGraph : Graph F E := M.labelGraph M.face

lemma graph_isLink_dart (d : D) : M.graph.IsLink (M.edge d) (M.vert d) (M.vert (M.edgePerm d)) :=
  M.labelGraph_isLink_dart M.vert d

lemma dualGraph_isLink_dart (d : D) :
    M.dualGraph.IsLink (M.edge d) (M.face d) (M.face (M.edgePerm d)) :=
  M.labelGraph_isLink_dart M.face d

/-- A map is **planar** when its graph is connected and its Euler characteristic is `2`. -/
def IsPlanar : Prop :=
  M.graph.Connected ∧ (Nat.card V : ℤ) - Nat.card E + Nat.card F = 2

/-- An edge set `C` is **even** for the labeling `lab` when each label is carried by an even
number of darts of edges of `C`: for `lab = face`, every vertex of the dual graph has even degree
in `C`, loops counting twice. -/
def IsEven (lab : D → W) (C : Set E) : Prop :=
  ∀ w, Even (Nat.card {d : D // lab d = w ∧ M.edge d ∈ C})

/-! ### Darts and edges -/

section Darts

variable [Fintype D]

lemma filter_edge_eq [DecidableEq D] [DecidableEq E] (d : D) :
    ({d' | M.edge d' = M.edge d} : Finset D) = {d, M.edgePerm d} := by
  ext d'
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  exact eq_comm.trans (M.edge_eq_edge_iff d d')

/-- The two darts of an edge. -/
lemma sum_edge_eq {R : Type*} [AddCommMonoid R] [DecidableEq E] (f : D → R) (d : D) :
    ∑ d' with M.edge d' = M.edge d, f d' = f d + f (M.edgePerm d) := by
  classical
  rw [M.filter_edge_eq, sum_pair (M.edgePerm_ne d).symm]

/-- Evenness as a parity of sums in `ZMod 2`. -/
lemma isEven_iff [DecidableEq W] (lab : D → W) (C : Set E) :
    M.IsEven lab C ↔ ∀ w, ∑ d with lab d = w, C.indicator (1 : E → ZMod 2) (M.edge d) = 0 := by
  classical
  refine forall_congr' fun w ↦ ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← ZMod.natCast_eq_zero_iff_even,
    card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter, sum_filter]
  refine Iff.of_eq (congrArg (· = (0 : ZMod 2)) (sum_congr rfl fun d _ ↦ ?_))
  by_cases hw : lab d = w <;> by_cases hC : M.edge d ∈ C <;> simp [hw, hC]

end Darts

/-! ### The incidence matrices -/

section Incidence

variable [Fintype D]

open scoped Classical in
/-- The incidence matrix of `labelGraph lab` over `ZMod 2`: the number of darts of each edge
carrying each label, mod 2. -/
noncomputable def incMatrix (lab : D → W) : Matrix E W (ZMod 2) :=
  fun e w ↦ #{d | M.edge d = e ∧ lab d = w}

open scoped Classical in
lemma incMatrix_mulVec [Fintype W] (lab : D → W) (χ : W → ZMod 2) (e : E) :
    (M.incMatrix lab *ᵥ χ) e = ∑ d with M.edge d = e, χ (lab d) := by
  simp only [mulVec, dotProduct, incMatrix]
  rw [← sum_fiberwise (s := ({d | M.edge d = e} : Finset D)) (g := lab)
    (f := fun d ↦ χ (lab d))]
  refine sum_congr rfl fun w _ ↦ ?_
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul, filter_filter]
  refine sum_congr rfl fun d hd ↦ ?_
  rw [(mem_filter.mp hd).2.2, one_mul]

open scoped Classical in
lemma incMatrix_transpose_mulVec [Fintype E] (lab : D → W) (g : E → ZMod 2) (w : W) :
    ((M.incMatrix lab)ᵀ *ᵥ g) w = ∑ d with lab d = w, g (M.edge d) := by
  simp only [mulVec, dotProduct, transpose_apply, incMatrix]
  rw [← sum_fiberwise (s := ({d | lab d = w} : Finset D)) (g := M.edge)
    (f := fun d ↦ g (M.edge d))]
  refine sum_congr rfl fun e _ ↦ ?_
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul, filter_filter]
  refine sum_congr (by ext; simp [and_comm]) fun d hd ↦ ?_
  rw [(mem_filter.mp hd).2.2, one_mul]

/-- A function on labels has zero coboundary when it agrees on the two darts of every edge. -/
lemma incMatrix_mulVec_eq_zero_iff [Fintype W] (lab : D → W) (χ : W → ZMod 2) :
    M.incMatrix lab *ᵥ χ = 0 ↔ ∀ d, χ (lab d) = χ (lab (M.edgePerm d)) := by
  classical
  have h2 : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  constructor
  · intro h d
    have := congrFun h (M.edge d)
    rwa [incMatrix_mulVec, M.sum_edge_eq (fun d ↦ χ (lab d)), Pi.zero_apply, h2] at this
  · intro h
    funext e
    obtain ⟨d, rfl⟩ := M.edge_surjective e
    rw [incMatrix_mulVec, M.sum_edge_eq (fun d ↦ χ (lab d)), Pi.zero_apply, h2]
    exact h d

/-- **The kernel of the coboundary of a connected graph** consists of the constant functions. -/
lemma finrank_ker_incMatrix [Fintype W] (lab : D → W) (h : (M.labelGraph lab).Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker (M.incMatrix lab).mulVecLin) = 1 := by
  obtain ⟨w₀, -⟩ := h.1
  have hker : LinearMap.ker (M.incMatrix lab).mulVecLin = (ZMod 2) ∙ (fun _ ↦ (1 : ZMod 2)) := by
    ext χ
    rw [LinearMap.mem_ker, mulVecLin_apply, Submodule.mem_span_singleton,
      M.incMatrix_mulVec_eq_zero_iff]
    constructor
    · intro hχ
      refine ⟨χ w₀, funext fun x ↦ ?_⟩
      have hconst : ∀ ⦃y z⦄, Relation.ReflTransGen (M.labelGraph lab).Adj y z → χ y = χ z := by
        intro y z hyz
        induction hyz with
        | refl => rfl
        | tail _ hab ih =>
          obtain ⟨e, d, -, rfl, rfl⟩ := hab
          exact ih.trans (hχ d)
      simpa using hconst (h.2 (Set.mem_univ w₀) (Set.mem_univ x))
    · rintro ⟨c, rfl⟩ d
      rfl
  rw [hker]
  exact finrank_span_singleton fun h1 ↦ one_ne_zero (congrFun h1 w₀)

/-- **The dimension of the cut space** of a connected graph: the image of its coboundary has
dimension one less than the number of vertices. -/
lemma finrank_range_incMatrix [Fintype W] (lab : D → W) (h : (M.labelGraph lab).Connected) :
    Module.finrank (ZMod 2) (LinearMap.range (M.incMatrix lab).mulVecLin) + 1 =
      Fintype.card W := by
  rw [← M.finrank_ker_incMatrix lab h, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

/-- **The dimension of the cycle space** of a connected graph: the kernel of its boundary has
dimension `#E - #W + 1`. -/
lemma finrank_ker_incMatrix_transpose [Fintype W] [Fintype E] (lab : D → W)
    (h : (M.labelGraph lab).Connected) :
    Module.finrank (ZMod 2) (LinearMap.ker (M.incMatrix lab)ᵀ.mulVecLin) + Fintype.card W =
      Fintype.card E + 1 := by
  have h₁ := LinearMap.finrank_range_add_finrank_ker (M.incMatrix lab)ᵀ.mulVecLin
  have h₂ := M.finrank_range_incMatrix lab h
  have h₃ : (M.incMatrix lab)ᵀ.rank = (M.incMatrix lab).rank := rank_transpose _
  rw [Matrix.rank, Matrix.rank] at h₃
  rw [Module.finrank_fintype_fun_eq_card] at h₁
  lia

end Incidence

/-! ### Edge cuts are even in the dual -/

section Cuts

variable [Fintype D] [Fintype V]

/-- The indicator of an edge cut is the coboundary of the indicator of its side. -/
lemma indicator_edgeCut (X : Set V) :
    (M.graph.edgeCut X).indicator 1 = M.incMatrix M.vert *ᵥ X.indicator (1 : V → ZMod 2) := by
  classical
  funext e
  obtain ⟨d, rfl⟩ := M.edge_surjective e
  rw [incMatrix_mulVec, M.sum_edge_eq (fun d ↦ X.indicator (1 : V → ZMod 2) (M.vert d)),
    Set.indicator_apply, (M.graph_isLink_dart d).mem_edgeCut_iff]
  by_cases h₁ : M.vert d ∈ X <;> by_cases h₂ : M.vert (M.edgePerm d) ∈ X <;>
    simp [h₁, h₂, CharTwo.add_self_eq_zero]

/-- Every element of the image of the coboundary is the indicator of an edge cut. -/
lemma isEdgeCut_of_indicator_mem_range {C : Set E}
    (h : C.indicator 1 ∈ LinearMap.range (M.incMatrix M.vert).mulVecLin) :
    M.graph.IsEdgeCut C := by
  obtain ⟨χ, hχ⟩ := h
  have hχX : χ = {x | χ x = 1}.indicator 1 := by
    funext x
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (χ x) with h | h <;> simp [h]
  have hC : (M.graph.edgeCut {x | χ x = 1}).indicator (1 : E → ZMod 2) = C.indicator 1 := by
    rw [M.indicator_edgeCut, ← hχX]
    exact hχ
  rw [← Set.indicator_one_inj (ZMod 2) hC]
  exact M.graph.isEdgeCut_edgeCut _

/-- **Walking round a face crosses an edge cut an even number of times**: the boundary of the dual
graph kills the coboundary of the graph. Around a face, the dart after `d` is `facePerm d`, which
shares the vertex of `edgePerm d`, so over the darts of the face the vertices of the two darts of
each edge are counted equally often. -/
lemma transpose_mulVec_mulVec [Fintype E] (χ : V → ZMod 2) :
    (M.incMatrix M.face)ᵀ *ᵥ (M.incMatrix M.vert *ᵥ χ) = 0 := by
  classical
  funext f
  rw [incMatrix_transpose_mulVec, Pi.zero_apply]
  simp_rw [incMatrix_mulVec, M.sum_edge_eq (fun d ↦ χ (M.vert d))]
  rw [sum_add_distrib]
  have hperm : ∑ d with M.face d = f, χ (M.vert (M.edgePerm d)) =
      ∑ d with M.face d = f, χ (M.vert d) := by
    refine sum_equiv M.facePerm (fun d ↦ by simp [M.face_facePerm]) fun d _ ↦ ?_
    rw [M.vert_facePerm]
  rw [hperm]
  exact CharTwo.add_self_eq_zero _

omit [Fintype V] in
/-- An edge set is even in the dual graph exactly when its indicator is killed by the boundary of
the dual graph. -/
lemma isEven_iff_mem_ker [Fintype E] (C : Set E) :
    M.IsEven M.face C ↔ C.indicator 1 ∈ LinearMap.ker (M.incMatrix M.face)ᵀ.mulVecLin := by
  classical
  rw [isEven_iff, LinearMap.mem_ker, mulVecLin_apply, funext_iff]
  simp only [incMatrix_transpose_mulVec, Pi.zero_apply]

end Cuts

/-- **Edge cuts of the graph are even in the dual graph.** -/
lemma isEven_of_isEdgeCut [Finite D] {C : Set E} (h : M.graph.IsEdgeCut C) :
    M.IsEven M.face C := by
  have : Fintype D := Fintype.ofFinite D
  have : Finite V := Finite.of_surjective _ M.vert_surjective
  have : Finite E := Finite.of_surjective _ M.edge_surjective
  have : Fintype V := Fintype.ofFinite V
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨X, -, rfl⟩ := h.exists_edgeCut
  rw [isEven_iff_mem_ker, LinearMap.mem_ker, mulVecLin_apply, M.indicator_edgeCut]
  exact M.transpose_mulVec_mulVec _

/-! ### Connectivity of the dual -/

/-- **The dual of a connected map is connected**: the darts whose faces are reachable from a given
one in the dual graph are closed under the rotation, which is an edge step followed by a face
step, and so they reach every vertex of the connected graph. -/
theorem dualGraph_connected (h : M.graph.Connected) : M.dualGraph.Connected := by
  obtain ⟨⟨v₀, -⟩, hconn⟩ := h
  obtain ⟨d₀, rfl⟩ := M.vert_surjective v₀
  refine ⟨⟨M.face d₀, Set.mem_univ _⟩, ?_⟩
  -- `R d`: the face of `d` is reachable from that of `d₀` in the dual graph.
  set R : D → Prop := fun d ↦ Relation.ReflTransGen M.dualGraph.Adj (M.face d₀) (M.face d)
  have hedge : ∀ d, R d → R (M.edgePerm d) := fun d hd ↦
    hd.tail ⟨M.edge d, M.labelGraph_isLink_dart M.face d⟩
  have hedge' : ∀ d, R (M.edgePerm d) → R d := fun d hd ↦ by
    have := hedge _ hd
    rwa [M.edgePerm_edgePerm] at this
  have hface : ∀ d, M.face (M.vertexPerm d) = M.face (M.edgePerm d) := fun d ↦ by
    rw [← M.face_facePerm (M.edgePerm d), facePerm_apply, M.edgePerm_edgePerm]
  have hrot : ∀ d, R d → R (M.vertexPerm d) := fun d hd ↦ by
    change Relation.ReflTransGen _ _ _
    rw [hface]
    exact hedge d hd
  have hrot' : ∀ d, R (M.vertexPerm d) → R d := fun d hd ↦ by
    refine hedge' d ?_
    change Relation.ReflTransGen _ _ _
    rw [← hface]
    exact hd
  have hcycle : ∀ d d', M.vertexPerm.SameCycle d d' → R d → R d' := by
    rintro d d' ⟨k, rfl⟩ hd
    induction k using Int.induction_on with
    | zero => simpa using hd
    | succ k ih =>
      rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      exact hrot _ ih
    | pred k ih =>
      refine hrot' _ ?_
      rw [← Equiv.Perm.mul_apply, ← zpow_one_add, add_sub_cancel]
      exact ih
  -- Every dart is reached, going along the connected graph.
  have hall : ∀ d, R d := by
    intro d
    suffices ∀ x, Relation.ReflTransGen M.graph.Adj (M.vert d₀) x → ∀ d', M.vert d' = x → R d' from
      this _ (hconn (Set.mem_univ _) (Set.mem_univ _)) d rfl
    intro x hx
    induction hx with
    | refl =>
      intro d' hd'
      exact hcycle d₀ d' ((M.vert_eq_vert_iff _ _).mp hd'.symm) Relation.ReflTransGen.refl
    | tail _ hxy ih =>
      obtain ⟨e, d₁, -, hd₁, rfl⟩ := hxy
      intro d' hd'
      exact hcycle _ d' ((M.vert_eq_vert_iff _ _).mp hd'.symm) (hedge d₁ (ih d₁ hd₁))
  have hsymm : ∀ ⦃f g⦄, Relation.ReflTransGen M.dualGraph.Adj f g →
      Relation.ReflTransGen M.dualGraph.Adj g f := by
    intro f g hfg
    induction hfg with
    | refl => exact .refl
    | tail _ hab ih => exact .head hab.symm ih
  intro f _ g _
  obtain ⟨d, rfl⟩ := M.face_surjective f
  obtain ⟨d', rfl⟩ := M.face_surjective g
  exact (hsymm (hall d)).trans (hall d')

/-! ### Minimal even edge sets are cycles -/

section Cycles

variable [Finite D]

/-- **The edge set of a cycle is even**: each vertex of the cycle meets exactly two darts of
cycle edges, those of the edges before and after it. -/
lemma isEven_range_of_isLink (lab : D → W) {n : ℕ} {v : Fin (n + 1) → W} {e : Fin (n + 1) → E}
    (he : Function.Injective e) (hl : ∀ k, (M.labelGraph lab).IsLink (e k) (v k) (v (k + 1))) :
    M.IsEven lab (Set.range e) := by
  classical
  have : Fintype D := Fintype.ofFinite D
  rw [isEven_iff]
  intro x
  have hl' : ∀ k, ∃ d, M.edge d = e k ∧ lab d = v k ∧ lab (M.edgePerm d) = v (k + 1) := hl
  choose d hd hdv hdv' using hl'
  have hind : ∀ d', (Set.range e).indicator (1 : E → ZMod 2) (M.edge d') =
      ∑ k, if M.edge d' = e k then 1 else 0 := by
    intro d'
    by_cases hmem : M.edge d' ∈ Set.range e
    · obtain ⟨k₀, hk₀⟩ := hmem
      rw [Set.indicator_of_mem (show M.edge d' ∈ Set.range e from ⟨k₀, hk₀⟩),
        Fintype.sum_eq_single k₀ fun k hk ↦ ite_eq_right fun h ↦
          hk (he (h.symm.trans hk₀.symm)), ite_eq_left hk₀.symm, Pi.one_apply]
    · rw [Set.indicator_of_notMem hmem]
      exact (sum_eq_zero fun k _ ↦ ite_eq_right fun h ↦ hmem ⟨k, h.symm⟩).symm
  simp_rw [hind]
  rw [sum_comm]
  have hterm : ∀ k, ∑ d' with lab d' = x, (if M.edge d' = e k then (1 : ZMod 2) else 0) =
      (if v k = x then 1 else 0) + if v (k + 1) = x then 1 else 0 := by
    intro k
    rw [← hdv k, ← hdv' k, ← M.sum_edge_eq (fun d' ↦ if lab d' = x then (1 : ZMod 2) else 0),
      sum_filter, sum_filter]
    refine sum_congr rfl fun d' _ ↦ ?_
    rw [hd k]
    by_cases h₁ : lab d' = x <;> by_cases h₂ : M.edge d' = e k <;> simp [h₁, h₂]
  simp_rw [hterm]
  rw [sum_add_distrib, Fintype.sum_equiv (Equiv.addRight 1)
    (fun k ↦ if v (k + 1) = x then (1 : ZMod 2) else 0) (fun k ↦ if v k = x then 1 else 0)
    fun k ↦ rfl]
  exact CharTwo.add_self_eq_zero _

/-- **A minimal nonempty even edge set is a cycle.** Take an edge of it. If the edge is a loop it
is the whole set. Otherwise the rest of the set joins its two ends, by a parity count over the
labels reachable from one of them, and a shortest path between them closes up with the edge to a
cycle inside the set, which, being even and nonempty, is the whole set. -/
theorem isCycle_of_minimal (lab : D → W) {C : Set E}
    (hC : Minimal (fun C : Set E ↦ C.Nonempty ∧ M.IsEven lab C) C) :
    (M.labelGraph lab).IsCycle C := by
  classical
  have : Fintype D := Fintype.ofFinite D
  obtain ⟨⟨e₀, he₀⟩, heven⟩ := hC.prop
  rw [isEven_iff] at heven
  obtain ⟨d₀, rfl⟩ := M.edge_surjective e₀
  -- A cycle inside `C` is all of it.
  have of_cycle : ∀ (n : ℕ) (v : Fin (n + 1) → W) (e : Fin (n + 1) → E), Function.Injective v →
      Function.Injective e → (∀ k, (M.labelGraph lab).IsLink (e k) (v k) (v (k + 1))) →
      Set.range e ⊆ C → (M.labelGraph lab).IsCycle C := by
    intro n v e hv he hl hsub
    exact ⟨n, v, e, hv, he, hl,
      hsub.antisymm (hC.2 ⟨⟨e 0, 0, rfl⟩, M.isEven_range_of_isLink lab he hl⟩ hsub)⟩
  by_cases hloop : lab d₀ = lab (M.edgePerm d₀)
  · have hfin : ∀ a b : Fin (0 + 1), a = b := fun a b ↦ Fin.ext (by lia)
    refine of_cycle 0 (fun _ ↦ lab d₀) (fun _ ↦ M.edge d₀) (fun a b _ ↦ hfin a b)
      (fun a b _ ↦ hfin a b) (fun _ ↦ ⟨d₀, rfl, rfl, hloop.symm⟩) ?_
    rintro _ ⟨_, rfl⟩
    exact he₀
  -- The rest of `C` joins the two ends of the edge `M.edge d₀`.
  set C' : Set E := C \ {M.edge d₀} with hC'
  set r : W → W → Prop := fun x y ↦ ∃ e ∈ C', (M.labelGraph lab).IsLink e x y with hr
  have hrsymm : ∀ ⦃x y⦄, r x y → r y x := fun x y ⟨e, he, hxy⟩ ↦ ⟨e, he, hxy.symm⟩
  have hreach : Relation.ReflTransGen r (lab d₀) (lab (M.edgePerm d₀)) := by
    by_contra hw
    set K : Set W := {x | Relation.ReflTransGen r (lab d₀) x}
    have hK₀ : lab d₀ ∈ K := Relation.ReflTransGen.refl
    -- By the handshake lemma, the darts of `C'` carrying labels in `K` are evenly many...
    have hpair : Even (#{d | lab d ∈ K ∧ M.edge d ∈ C'}) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact M.even_card_of_forall_adj_restrict lab C' fun _ _ hx hxy ↦
        Relation.ReflTransGen.tail hx hxy
    -- ...yet, counted through the labels, there is an odd number of them.
    have hsplit : ∀ d, C'.indicator (1 : E → ZMod 2) (M.edge d) =
        C.indicator 1 (M.edge d) - ({M.edge d₀} : Set E).indicator 1 (M.edge d) := by
      intro d
      by_cases h₁ : M.edge d ∈ C <;> by_cases h₂ : M.edge d = M.edge d₀ <;>
        simp_all [Set.indicator_apply]
    have hzero : ∑ d with lab d ∈ K, C.indicator (1 : E → ZMod 2) (M.edge d) = 0 := by
      rw [← sum_fiberwise_of_maps_to (g := lab) (t := ({d | lab d ∈ K} : Finset D).image lab)
        (fun d hd ↦ mem_image_of_mem lab hd)]
      refine sum_eq_zero fun x hx ↦ ?_
      obtain ⟨d', hd', rfl⟩ := mem_image.mp hx
      rw [← heven (lab d'), filter_filter]
      refine sum_congr (filter_congr fun d _ ↦ ?_) fun _ _ ↦ rfl
      exact and_iff_right_of_imp fun h ↦ h ▸ (mem_filter.mp hd').2
    have hone : ∑ d with lab d ∈ K, ({M.edge d₀} : Set E).indicator (1 : E → ZMod 2)
        (M.edge d) = 1 := by
      have := M.sum_edge_eq (fun d ↦ if lab d ∈ K then (1 : ZMod 2) else 0) d₀
      rw [ite_eq_left hK₀, ite_eq_right (show lab (M.edgePerm d₀) ∉ K from hw), add_zero,
        sum_filter] at this
      rw [sum_filter, ← this]
      refine sum_congr rfl fun d _ ↦ ?_
      by_cases h₁ : lab d ∈ K <;> by_cases h₂ : M.edge d = M.edge d₀ <;>
        simp [h₁, h₂]
    have hcount : ∑ d with lab d ∈ K, C'.indicator (1 : E → ZMod 2) (M.edge d) = 1 := by
      simp_rw [hsplit]
      rw [sum_sub_distrib, hzero, hone]
      decide
    have hcard : (#{d | lab d ∈ K ∧ M.edge d ∈ C'} : ZMod 2) = 1 := by
      rw [← hcount, sum_filter, ← filter_filter, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
        sum_filter, sum_filter]
      refine sum_congr rfl fun d _ ↦ ?_
      by_cases h₁ : lab d ∈ K <;> by_cases h₂ : M.edge d ∈ C' <;> simp [h₁, h₂]
    rw [(ZMod.natCast_eq_zero_iff_even).mpr hpair] at hcard
    exact zero_ne_one hcard
  -- A shortest path from one end to the other, closed up by the edge, is a cycle inside `C`.
  set G' : SimpleGraph W := SimpleGraph.fromRel r
  have hG'reach : G'.Reachable (lab d₀) (lab (M.edgePerm d₀)) := by
    rw [SimpleGraph.reachable_iff_reflTransGen]
    have key : ∀ y, Relation.ReflTransGen r (lab d₀) y →
        Relation.ReflTransGen G'.Adj (lab d₀) y := by
      intro y hy
      induction hy with
      | refl => exact .refl
      | @tail x y _ hxy ih =>
        by_cases hxy' : x = y
        · exact hxy' ▸ ih
        · exact ih.tail ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hxy', .inl hxy⟩)
    exact key _ hreach
  obtain ⟨p, hp⟩ := hG'reach.exists_isPath
  have hstep : ∀ i < p.length, ∃ e ∈ C',
      (M.labelGraph lab).IsLink e (p.getVert i) (p.getVert (i + 1)) := by
    intro i hi
    obtain ⟨-, h | h⟩ := (SimpleGraph.fromRel_adj _ _ _).mp (p.adj_getVert_succ hi)
    · exact h
    · exact hrsymm h
  have : Nonempty E := ⟨M.edge d₀⟩
  choose! ep hepC hepl using hstep
  have hinj : ∀ i j : ℕ, i ≤ p.length → j ≤ p.length → p.getVert i = p.getVert j → i = j :=
    fun i j hi hj h ↦ hp.getVert_injOn hi hj h
  refine of_cycle p.length (fun k ↦ p.getVert k)
    (fun k ↦ if (k : ℕ) < p.length then ep k else M.edge d₀) ?_ ?_ ?_ ?_
  · intro a b hab
    exact Fin.ext (hinj _ _ (Nat.lt_succ_iff.mp a.2) (Nat.lt_succ_iff.mp b.2) hab)
  · intro a b hab
    simp only at hab
    split_ifs at hab with ha hb hb
    · have hla := hepl a ha
      rw [hab] at hla
      rcases (hepl b hb).eq_and_eq_or_eq_and_eq hla with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
      · exact Fin.ext (hinj _ _ hb.le ha.le h₁).symm
      · have := hinj _ _ hb.le (Nat.succ_le_of_lt ha) h₁
        have := hinj _ _ (Nat.succ_le_of_lt hb) ha.le h₂
        lia
    · exact absurd (hepC a ha) (by rw [hab]; exact fun h ↦ h.2 rfl)
    · exact absurd (hepC b hb) (by rw [← hab]; exact fun h ↦ h.2 rfl)
    · exact Fin.ext (by lia)
  · intro k
    split_ifs with hk
    · rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr fun h ↦ by
        rw [h, Fin.val_last] at hk; exact lt_irrefl _ hk)]
      exact hepl k hk
    · have hkm : k = Fin.last p.length := Fin.ext (by have := k.2; simp at hk ⊢; lia)
      rw [hkm, Fin.last_add_one, Fin.val_last, Fin.val_zero, p.getVert_length, p.getVert_zero]
      exact ⟨M.edgePerm d₀, M.edge_edgePerm d₀, rfl, by rw [M.edgePerm_edgePerm]⟩
  · rintro _ ⟨k, rfl⟩
    dsimp only
    split_ifs with hk
    · exact (hepC k hk).1
    · exact he₀

end Cycles

/-! ### Planar duality -/

section Planar

variable {M} [Finite D]

/-- In a planar map, the edge cuts of the graph are exactly the edge sets meeting every face
evenly: both form a space of dimension `#V - 1 = #E - #F + 1` over `ZMod 2`, and the first lies
in the second. -/
theorem IsPlanar.isEdgeCut_of_isEven (hM : M.IsPlanar) {C : Set E} (hC : M.IsEven M.face C) :
    M.graph.IsEdgeCut C := by
  have : Fintype D := Fintype.ofFinite D
  have : Finite V := Finite.of_surjective _ M.vert_surjective
  have : Finite E := Finite.of_surjective _ M.edge_surjective
  have : Finite F := Finite.of_surjective _ M.face_surjective
  have : Fintype V := Fintype.ofFinite V
  have : Fintype E := Fintype.ofFinite E
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨hconn, heuler⟩ := hM
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at heuler
  have hle : LinearMap.range (M.incMatrix M.vert).mulVecLin ≤
      LinearMap.ker (M.incMatrix M.face)ᵀ.mulVecLin := by
    rintro _ ⟨χ, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply]
    exact M.transpose_mulVec_mulVec χ
  have hrange := M.finrank_range_incMatrix M.vert hconn
  have hker := M.finrank_ker_incMatrix_transpose M.face (M.dualGraph_connected hconn)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by lia)
  rw [isEven_iff_mem_ker, ← heq] at hC
  exact M.isEdgeCut_of_indicator_mem_range hC

/-- **Planar duality for bonds**: in a planar map, the edges of a bond of the graph, a minimal
nonempty edge cut, form a cycle of the dual graph. A bond is even in the dual graph, and so is
any smaller nonempty edge set meeting every face evenly, which by planarity is an edge cut; so a
bond is a minimal nonempty even edge set of the dual graph, that is, a cycle of it. -/
theorem IsPlanar.isCycle_of_isBond (hM : M.IsPlanar) {B : Set E} (hB : M.graph.IsBond B) :
    M.dualGraph.IsCycle B := by
  have : Fintype D := Fintype.ofFinite D
  have : Finite V := Finite.of_surjective _ M.vert_surjective
  have : Finite E := Finite.of_surjective _ M.edge_surjective
  have : Finite F := Finite.of_surjective _ M.face_surjective
  have : Fintype V := Fintype.ofFinite V
  have : Fintype E := Fintype.ofFinite E
  have : Fintype F := Fintype.ofFinite F
  refine M.isCycle_of_minimal M.face ⟨⟨hB.nonempty, M.isEven_of_isEdgeCut hB.isEdgeCut⟩, ?_⟩
  rintro C ⟨hCne, hCeven⟩ hCB
  exact hB.2 ⟨hM.isEdgeCut_of_isEven hCeven, hCne⟩ hCB

/-- A map with a connected graph is **planar** as soon as every edge set meeting each face evenly
is an edge cut of the graph: the cut space and the cycle space of the dual are then equal, and
comparing their dimensions `#V - 1` and `#E - #F + 1` is Euler's formula. -/
theorem isPlanar_of_forall_isEdgeCut (hconn : M.graph.Connected)
    (h : ∀ C : Set E, M.IsEven M.face C → M.graph.IsEdgeCut C) : M.IsPlanar := by
  have : Fintype D := Fintype.ofFinite D
  have : Finite V := Finite.of_surjective _ M.vert_surjective
  have : Finite E := Finite.of_surjective _ M.edge_surjective
  have : Finite F := Finite.of_surjective _ M.face_surjective
  have : Fintype V := Fintype.ofFinite V
  have : Fintype E := Fintype.ofFinite E
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hconn, ?_⟩
  have heq : LinearMap.range (M.incMatrix M.vert).mulVecLin =
      LinearMap.ker (M.incMatrix M.face)ᵀ.mulVecLin := by
    refine le_antisymm ?_ fun g hg ↦ ?_
    · rintro _ ⟨χ, rfl⟩
      rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply]
      exact M.transpose_mulVec_mulVec χ
    · have hgC : g = {e | g e = 1}.indicator 1 := by
        funext e
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (g e) with h | h <;> simp [h]
      rw [hgC] at hg ⊢
      obtain ⟨X, -, hX⟩ := (h _ ((M.isEven_iff_mem_ker _).mpr hg)).exists_edgeCut
      rw [← hX, M.indicator_edgeCut]
      exact ⟨_, rfl⟩
  have hrange := M.finrank_range_incMatrix M.vert hconn
  have hker := M.finrank_ker_incMatrix_transpose M.face (M.dualGraph_connected hconn)
  rw [heq] at hrange
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  lia

end Planar

end CombinatorialMap
