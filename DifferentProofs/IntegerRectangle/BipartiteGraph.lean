module

public import DifferentProofs.IntegerRectangle.Tiling.CornerCount
public import DifferentProofsForMathlib.Combinatorics.Graph.Bipartite

/-!
# The integer-rectangle theorem via a bipartite graph

Wagon's eighth proof, his variation on Paterson's Eulerian-path proof. Place `R` in standard
position, let `S` be the set of corners of tiles having both coordinates integers, and let `T` be
the set of tiles. Form a bipartite graph on `S ∪ T` by joining each point of `S` to all the tiles
of which it is a corner. There is an even number of edges, since a tile with an integer side has
`0`, `2` or `4` corners in `S`. But each point of `S` that is not a corner of `R` lies on `2` or `4`
tiles, while the lower-left corner of `R`, which is in `S`, lies on only one; so another point of
`S` lies on an odd number of tiles. That can only be another corner of `R`, and then the width or
the height of `R` is an integer.

The graph is `bipartiteGraph`, a mathlib multigraph. Its vertices are the points of `S`, as
`Sum.inl`, and the tiles, as `Sum.inr`, and its edges are the incidences of the tiles with their
corners: the edge `(i, b)` joins the tile `T i` to its corner `b`, and is an edge of the graph when
that corner is in `S`. The edges at a vertex form its incidence set, and the count of all the
edges from either side is `Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq`. That a point lies on
exactly one tile at a corner of `R`, and on none, two or four tiles anywhere else, is the local
picture of `IsTiling.sum_cornerCount_eq`.

Instead of moving `R` into standard position, `S` is cut out by the lattice through the lower-left
corner of `R` (`OnLattice`).

## Main result

- `IntegerRectangleTheorem_BipartiteGraph`: the bipartite-graph proof of the integer-rectangle
  theorem.
-/

@[expose] public section

open Finset

namespace IntegerRectangle.BipartiteGraph

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-! ### The bipartite graph -/

/-- A point is *on the lattice* of `R` when both of its coordinates differ from those of the
lower-left corner of `R` by integers. Measuring from that corner replaces Wagon's "place `R` in
standard position". -/
def OnLattice (R : Rectangle) (z : ℝ × ℝ) : Prop :=
  (∃ m : ℤ, z.1 - R.x₀ = m) ∧ ∃ n : ℤ, z.2 - R.y₀ = n

open scoped Classical in
/-- Wagon's set `S`: the corners of the tiles lying on the lattice. -/
noncomputable def latticeCorners (R : Rectangle) (T : ι → Rectangle) : Finset (ℝ × ℝ) :=
  {z ∈ univ.image fun d : ι × Bool × Bool ↦ (T d.1).corner d.2 | OnLattice R z}

open scoped Classical in
/-- The points of `S` are on the lattice. -/
lemma onLattice_of_mem {z : ℝ × ℝ} (hz : z ∈ latticeCorners R T) : OnLattice R z :=
  (mem_filter.mp hz).2

open scoped Classical in
/-- A corner of a tile on the lattice is in `S`. -/
lemma corner_mem_latticeCorners {d : ι × Bool × Bool} (h : OnLattice R ((T d.1).corner d.2)) :
    (T d.1).corner d.2 ∈ latticeCorners R T :=
  mem_filter.mpr ⟨mem_image_of_mem _ (mem_univ d), h⟩

/-- **Wagon's bipartite graph** on `S ∪ T`. The edge `(i, b)` joins the corner `b` of the tile
`T i` to the tile, when that corner is on the lattice. -/
def bipartiteGraph (R : Rectangle) (T : ι → Rectangle) :
    Graph ((ℝ × ℝ) ⊕ ι) (ι × Bool × Bool) where
  vertexSet := Sum.inl '' ↑(latticeCorners R T) ∪ Set.range Sum.inr
  IsLink d x y := OnLattice R ((T d.1).corner d.2) ∧
    (x = .inl ((T d.1).corner d.2) ∧ y = .inr d.1 ∨ x = .inr d.1 ∧ y = .inl ((T d.1).corner d.2))
  edgeSet := {d | OnLattice R ((T d.1).corner d.2)}
  isLink_symm _ _ := ⟨fun _ _ ↦ by grind⟩
  eq_or_eq_of_isLink_of_isLink := by grind
  edge_mem_iff_exists_isLink d := ⟨fun h ↦ ⟨_, _, h, .inl ⟨rfl, rfl⟩⟩, fun ⟨_, _, h, _⟩ ↦ h⟩
  left_mem_of_isLink d x y := by
    rintro ⟨h, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact .inl ⟨_, corner_mem_latticeCorners h, rfl⟩
    · exact .inr ⟨_, rfl⟩

/-- The bipartite graph is bipartite, with the points of `S` on one side and the tiles on the
other. -/
lemma isBipartiteWith :
    (bipartiteGraph R T).IsBipartiteWith
      ↑((latticeCorners R T).map (.inl : ℝ × ℝ ↪ (ℝ × ℝ) ⊕ ι))
      ↑((univ : Finset ι).map (.inr : ι ↪ (ℝ × ℝ) ⊕ ι)) := by
  refine ⟨?_, fun d x y ⟨h, hxy⟩ ↦ ?_⟩
  · simp [Set.disjoint_left]
  · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [corner_mem_latticeCorners h]

/-! ### Counting the edges at a tile -/

/-- The edges at a tile are its corners on the lattice. -/
lemma ncard_incidenceSet_inr [DecidablePred (OnLattice R)] (i : ι) :
    ((bipartiteGraph R T).incidenceSet (.inr i)).ncard = #{b | OnLattice R ((T i).corner b)} := by
  have : (bipartiteGraph R T).incidenceSet (.inr i) =
      (fun b ↦ (i, b)) '' {b | OnLattice R ((T i).corner b)} := by
    ext ⟨j, b⟩
    simp only [Graph.incidenceSet, Graph.Inc, bipartiteGraph, Set.mem_ofPred_eq, Set.mem_image,
      Prod.mk.injEq]
    grind
  rw [this, Set.ncard_image_of_injective _ (Prod.mk_right_injective i),
    Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]

/-- A side of integer length has both of its endpoints on the lattice or neither. -/
private lemma onLattice_iff {S : Rectangle} (h : S.HasIntegerSide) :
    (∀ y, OnLattice R (S.x₀, y) ↔ OnLattice R (S.x₁, y)) ∨
      ∀ x, OnLattice R (x, S.y₀) ↔ OnLattice R (x, S.y₁) := by
  refine h.imp (fun ⟨n, hn⟩ y ↦ ?_) fun ⟨n, hn⟩ x ↦ ?_ <;>
    simp only [OnLattice, Rectangle.width, Rectangle.height] at hn ⊢
  · exact and_congr_left' ⟨fun ⟨m, hm⟩ ↦ ⟨m + n, by push_cast; linarith⟩,
      fun ⟨m, hm⟩ ↦ ⟨m - n, by push_cast; linarith⟩⟩
  · exact and_congr_right' ⟨fun ⟨m, hm⟩ ↦ ⟨m + n, by push_cast; linarith⟩,
      fun ⟨m, hm⟩ ↦ ⟨m - n, by push_cast; linarith⟩⟩

/-- **A tile with an integer side has `0`, `2` or `4` corners on the lattice**, so evenly many
edges: the two ends of a side of integer length are on the lattice together or not at all. -/
theorem even_ncard_incidenceSet_inr {i : ι} (h : (T i).HasIntegerSide) :
    Even ((bipartiteGraph R T).incidenceSet (.inr i)).ncard := by
  classical
  rw [ncard_incidenceSet_inr, card_filter, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  simp only [Rectangle.corner, ↓reduceIte, Bool.false_eq_true]
  rcases onLattice_iff (R := R) h with h | h <;> simp only [h] <;> split_ifs <;> decide

/-! ### Counting the edges at a point -/

/-- The edges at a point of `S` are the incidences of the tiles with it, so their number is the
number of corners the tiles have there. -/
theorem ncard_incidenceSet_inl {z : ℝ × ℝ} (hz : z ∈ latticeCorners R T) :
    ((bipartiteGraph R T).incidenceSet (.inl z)).ncard = ∑ i, cornerCount (T i) z.1 z.2 := by
  classical
  have : (bipartiteGraph R T).incidenceSet (.inl z) = {d | (T d.1).corner d.2 = z} := by
    ext d
    simp only [Graph.incidenceSet, Graph.Inc, bipartiteGraph, Set.mem_ofPred_eq]
    grind [onLattice_of_mem hz]
  rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, card_filter, Fintype.sum_prod_type]
  exact sum_congr rfl fun i _ ↦ (card_filter _ _).symm.trans (card_corner_eq (T i) z.1 z.2)

/-- **The lower-left corner of `R` lies on exactly one tile**, and is therefore in `S`. -/
theorem corner_mem (hT : IsTiling R T) :
    (R.x₀, R.y₀) ∈ latticeCorners R T ∧ ∑ i, cornerCount (T i) R.x₀ R.y₀ = 1 := by
  classical
  have hR : cornerCount R R.x₀ R.y₀ = 1 := by
    simp [cornerCount, xCount, yCount, hT.x₀_lt_x₁.ne', hT.y₀_lt_y₁.ne']
  have hsum : ∑ i, cornerCount (T i) R.x₀ R.y₀ = 1 := by
    rcases hT.sum_cornerCount_eq R.x₀ R.y₀ with h | ⟨h, -⟩
    · exact h.trans hR
    · exact absurd (h.symm.trans hR) zero_ne_one
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero (s := univ) (hsum ▸ one_ne_zero)
  obtain ⟨b, hb⟩ : ∃ b, (T i).corner b = (R.x₀, R.y₀) := by
    by_contra! hb
    rw [← card_corner_eq, card_eq_zero.mpr (filter_eq_empty_iff.mpr fun b _ ↦ hb b)] at hi
    exact hi rfl
  exact ⟨hb ▸ corner_mem_latticeCorners (d := (i, b)) (hb ▸ ⟨⟨0, by simp⟩, 0, by simp⟩), hsum⟩

/-! ### The proof -/

/-- **Another point of `S` lies on an odd number of tiles.** Counted from the side of the tiles,
the edges of the bipartite graph are evenly many. Counted from the side of `S` they are the
numbers of tiles the points of `S` lie on, and the lower-left corner of `R` lies on only one. -/
theorem exists_odd (hT : IsTiling R T) (hsides : ∀ i, (T i).HasIntegerSide) :
    ∃ z ∈ latticeCorners R T, z ≠ (R.x₀, R.y₀) ∧ Odd (∑ i, cornerCount (T i) z.1 z.2) := by
  classical
  have hcount := Graph.IsBipartiteWith.sum_ncard_incidenceSet_eq isBipartiteWith
    (Set.toFinite (bipartiteGraph R T).edgeSet)
  simp only [sum_map, Function.Embedding.inl_apply, Function.Embedding.inr_apply] at hcount
  rw [sum_congr rfl fun z hz ↦ ncard_incidenceSet_inl hz] at hcount
  obtain ⟨hmem, hone⟩ := corner_mem hT
  have heven : Even (∑ z ∈ latticeCorners R T, ∑ i, cornerCount (T i) z.1 z.2) :=
    hcount ▸ even_sum _ fun i _ ↦ even_ncard_incidenceSet_inr (hsides i)
  rw [← add_sum_erase _ _ hmem, hone] at heven
  by_contra! h
  refine Nat.not_even_one ((Nat.even_add.mp heven).mpr (even_sum _ fun z hz ↦ ?_))
  exact Nat.not_odd_iff_even.mp (h z (mem_of_mem_erase hz) (ne_of_mem_erase hz))

end IntegerRectangle.BipartiteGraph

open IntegerRectangle IntegerRectangle.BipartiteGraph in
/-- **Bipartite-graph proof** (Wagon's variation on Paterson's Eulerian-path proof) of the
integer-rectangle tiling theorem. Another point of `S` lies on an odd number of tiles
(`exists_odd`); a point that is not a corner of `R` lies on none, two or four, so it is another
corner of `R`, and being on the lattice it makes a side of `R` an integer. -/
theorem IntegerRectangleTheorem_BipartiteGraph : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  classical
  obtain ⟨z, hz, hzo, hodd⟩ := exists_odd hT hsides
  have hc : cornerCount R z.1 z.2 ≠ 0 := fun h₀ ↦ by
    rcases hT.sum_cornerCount_eq z.1 z.2 with h | ⟨-, h | h⟩ <;> rw [h] at hodd
    · exact Nat.not_odd_zero (h₀ ▸ hodd)
    · exact absurd hodd (by decide)
    · exact absurd hodd (by decide)
  obtain ⟨⟨m, hm⟩, n, hn⟩ := onLattice_of_mem hz
  have hx : R.x₀ = z.1 ∨ R.x₁ = z.1 := by
    by_contra! h
    simp [cornerCount, xCount, h.1, h.2] at hc
  have hy : R.y₀ = z.2 ∨ R.y₁ = z.2 := by
    by_contra! h
    simp [cornerCount, yCount, h.1, h.2] at hc
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact absurd (Prod.ext hx.symm hy.symm) hzo
    · exact .inr ⟨n, by rw [Rectangle.height, hy, hn]⟩
  · exact .inl ⟨m, by rw [Rectangle.width, hx, hm]⟩
