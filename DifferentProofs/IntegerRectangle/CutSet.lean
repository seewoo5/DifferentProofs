module

public import DifferentProofs.IntegerRectangle.ReducibleLink
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic

/-!
# The integer-rectangle theorem by a minimal cut-set

Wagon's eleventh proof, due to Paul Seymour. Form a graph `Γ`: its vertices are the horizontal
segments of the tiling — the maximal stretches of horizontal tile edges — and its edges are the
tiles, each tile joining the segment carrying its bottom edge to the segment carrying its top
edge, together with one exterior edge running around the outside of `R` from its bottom edge to
its top edge. Call a tile a *V-tile* when its height is an integer — by the hypothesis of the
theorem the others are *H-tiles*, of integer width — and let `S` be the set of edges of `Γ`
coming from H-tiles, together with the exterior edge.

If deleting `S` leaves the bottom of `R` connected to its top, a path of V-tiles climbs from the
bottom edge to the top edge, each step changing the height by the integer height of the tile
crossed, and the height of `R` is an integer (`CutSet.Reach`, `CutSet.int_sub_y₀_of_mem_reach`).

Otherwise `S` is a cut, and Wagon takes a minimal cut `S' ⊆ S` and invokes planar duality: the
tiling embeds `Γ` in the plane; the faces of the embedding are the V-links of the tiling — "in
the terminology of the preceding proof", so this file imports them from
`DifferentProofs.IntegerRectangle.ReducibleLink` — together with the two outer faces on either
side of the exterior edge; and the duals of the edges of a minimal cut form a cycle in the dual
graph `Γ*`. The cycle must use the dual of the exterior edge, since that edge alone joins bottom
to top, and deleting it leaves a dual path from the left outer face to the right outer face all
of whose steps cross H-tiles: the abscissa travels from `R.x₀` to `R.x₁` in integer steps, and
the width of `R` is an integer.

Mathlib has no planarity, so the duality is proved directly for this graph, in the concrete form
Wagon reads it off the embedding: the faces are constructed geometrically (`CutSet.Face`,
`CutSet.leftFace`, `CutSet.rightFace`), and the statement "around a face, a cut is crossed
evenly" is a telescope along the tiles abutting a V-link (`CutSet.cutDeg_link`).

## Deviations from the paper, and why

* The vertices of `Γ` are handled as the points of the plane lying on horizontal tile edges,
  two points representing the same vertex when a segment move (`CutSet.SegStep`) joins them,
  rather than as maximal segments; a path in `Γ` is a `Relation.ReflTransGen` chain of segment
  moves and V-tile crossings. This is the same graph with its vertices kept as representatives
  instead of equivalence classes.

* In place of the minimal cut `S' ⊆ S` and the cited theorem that the duals of a minimal cut's
  edges form a cycle (Wagon's reference [7, Thm 15C]), the formalization takes the cut around
  the *reachable region* — the tiles with exactly one horizontal edge reachable from the bottom
  (`CutSet.Cut`) — and proves the parity form of the same planar duality: around every V-link
  face the cut crosses an even number of tiles (`CutSet.cutDeg_link`), and around each of the
  two outer faces an odd number (`CutSet.cutDeg_left`, `CutSet.cutDeg_right`), the exterior
  edge, which every bottom–top cut contains, being their shared odd crossing. The dual path
  then falls out by a handshake count in `ZMod 2` (`CutSet.reflTransGen_dualStep`) — the same
  path Wagon extracts from his cycle by deleting the exterior dual edge. The parity statement
  is the geometric content of the cycle theorem here; extracting a literal cycle would add
  trail bookkeeping and no geometry.

The parity around a face is a telescope: the tiles abutting a V-link on one side partition it
(`ReducibleLink.Link.exists_left`), so the reachability indicators of their horizontal edges
telescope in `ZMod 2` to the two ends of the link (`CutSet.sum_partition`), and the two sides of
the link see the same two ends and cancel. Around an outer face the telescope runs up the left
or right edge of `R` instead, and its ends are two corners of `R`, of which the bottom one is
reachable and the top one is not — the odd crossing that the exterior edge contributes.
-/

@[expose] public section

open Set

namespace IntegerRectangle

open ReducibleLink

namespace CutSet

variable {ι : Type} {R : Rectangle} {T : ι → Rectangle} {i : ι} {p q : ℝ × ℝ}

/-! ### Seymour's graph, its cut-set deleted -/

/-- The point `p` lies on the bottom edge of the rectangle `S`. -/
def MemBot (S : Rectangle) (p : ℝ × ℝ) : Prop := p.2 = S.y₀ ∧ S.x₀ ≤ p.1 ∧ p.1 ≤ S.x₁

/-- The point `p` lies on the top edge of the rectangle `S`. -/
def MemTop (S : Rectangle) (p : ℝ × ℝ) : Prop := p.2 = S.y₁ ∧ S.x₀ ≤ p.1 ∧ p.1 ≤ S.x₁

/-- The point `p` lies on a horizontal edge of the tiling. The vertices of Seymour's graph are
the maximal horizontal segments of the tiling; this file keeps their points as representatives
and never forms the segments themselves. -/
def OnEdge (T : ι → Rectangle) (p : ℝ × ℝ) : Prop := ∃ i, MemBot (T i) p ∨ MemTop (T i) p

/-- A move along a horizontal segment: two points at the same height, every point between them
on a horizontal edge, represent the same vertex of Seymour's graph. -/
def SegStep (T : ι → Rectangle) (p q : ℝ × ℝ) : Prop :=
  p.2 = q.2 ∧ ∀ x ∈ uIcc p.1 q.1, OnEdge T (x, p.2)

/-- A crossing of a V-tile — a tile of integer height — from its bottom edge to its top edge or
back: the edges of Seymour's graph that survive when the cut-set `S` is deleted. -/
def CrossStep (T : ι → Rectangle) (p q : ℝ × ℝ) : Prop :=
  ∃ i, (∃ m : ℤ, (T i).height = m) ∧
    (MemBot (T i) p ∧ MemTop (T i) q ∨ MemBot (T i) q ∧ MemTop (T i) p)

/-- A step in Seymour's graph with the cut-set deleted: a segment move or a V-tile crossing. -/
def Step (T : ι → Rectangle) (p q : ℝ × ℝ) : Prop := SegStep T p q ∨ CrossStep T p q

/-- The vertices reachable from the bottom of `R` after the cut-set is deleted, seeded at the
bottom-left corner. -/
def Reach (R : Rectangle) (T : ι → Rectangle) : Set (ℝ × ℝ) :=
  {p | Relation.ReflTransGen (Step T) (R.x₀, R.y₀) p}

/-- Segment moves are symmetric. -/
lemma SegStep.symm (h : SegStep T p q) : SegStep T q p :=
  ⟨h.1.symm, fun x hx ↦ h.1 ▸ h.2 x (uIcc_comm q.1 p.1 ▸ hx)⟩

/-- Steps are symmetric, so reachability is closed under steps in both directions. -/
lemma Step.symm (h : Step T p q) : Step T q p :=
  h.imp SegStep.symm fun ⟨i, hint, hc⟩ ↦ ⟨i, hint, hc.symm⟩

/-- The two ends of a step are reachable together. -/
lemma step_mem_reach_iff (h : Step T p q) : p ∈ Reach R T ↔ q ∈ Reach R T :=
  ⟨fun hp ↦ hp.tail h, fun hq ↦ hq.tail h.symm⟩

/-- **Reachability climbs by integer steps**: every reachable vertex sits an integer distance
above the bottom of `R`, since a segment move keeps the height and a crossing changes it by the
integer height of a V-tile. If the cut-set fails to cut, this is the first alternative of the
theorem: a vertex on the top edge of `R` is reachable, and the height of `R` is an integer. -/
lemma int_sub_y₀_of_mem_reach (h : p ∈ Reach R T) : ∃ m : ℤ, p.2 - R.y₀ = m := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm⟩ := ih
    rcases hstep with ⟨hy, -⟩ | ⟨j, ⟨n, hn⟩, ⟨⟨hb, -⟩, ht, -⟩ | ⟨⟨hb, -⟩, ht, -⟩⟩
    · exact ⟨m, hy ▸ hm⟩
    · rw [Rectangle.height] at hn
      exact ⟨m + n, by push_cast; linarith⟩
    · rw [Rectangle.height] at hn
      exact ⟨m - n, by push_cast; linarith⟩

/-- Two points of one bottom edge are joined by a segment move: the edge is its own witness. -/
lemma segStep_of_memBot (hp : MemBot (T i) p) (hq : MemBot (T i) q) : SegStep T p q := by
  refine ⟨hp.1.trans hq.1.symm, fun x hx ↦ ⟨i, .inl ⟨hp.1, ?_⟩⟩⟩
  rcases mem_uIcc.mp hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨hp.2.1.trans h₁, h₂.trans hq.2.2⟩
  · exact ⟨hq.2.1.trans h₁, h₂.trans hp.2.2⟩

/-- Two points of one top edge are joined by a segment move. -/
lemma segStep_of_memTop (hp : MemTop (T i) p) (hq : MemTop (T i) q) : SegStep T p q := by
  refine ⟨hp.1.trans hq.1.symm, fun x hx ↦ ⟨i, .inr ⟨hp.1, ?_⟩⟩⟩
  rcases mem_uIcc.mp hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨hp.2.1.trans h₁, h₂.trans hq.2.2⟩
  · exact ⟨hq.2.1.trans h₁, h₂.trans hp.2.2⟩

/-- All points of a tile's bottom edge are reachable together: whether "the vertex below the
tile" is reachable does not depend on the representing point. -/
lemma memBot_mem_reach_iff (hp : MemBot (T i) p) (hq : MemBot (T i) q) :
    p ∈ Reach R T ↔ q ∈ Reach R T :=
  step_mem_reach_iff (.inl (segStep_of_memBot hp hq))

/-- All points of a tile's top edge are reachable together. -/
lemma memTop_mem_reach_iff (hp : MemTop (T i) p) (hq : MemTop (T i) q) :
    p ∈ Reach R T ↔ q ∈ Reach R T :=
  step_mem_reach_iff (.inl (segStep_of_memTop hp hq))

/-! ### The cut -/

/-- The **cut** around the reachable region: the edges of Seymour's graph with exactly one end
reachable, recorded at each tile's lower-left and upper-left corners. Since reachability is
closed under V-tile crossings, all cut edges come from H-tiles (`intWidth_of_cut`), and together
with the exterior edge — whose ends, the bottom and top of `R`, are likewise reachable and
unreachable — they form a bottom–top cut inside Wagon's `S`. -/
def Cut (R : Rectangle) (T : ι → Rectangle) (i : ι) : Prop :=
  ¬((((T i).x₀, (T i).y₀) : ℝ × ℝ) ∈ Reach R T ↔ (((T i).x₀, (T i).y₁) : ℝ × ℝ) ∈ Reach R T)

/-- A cut tile cannot have integer height — its two edges would be reachable together — so by
the hypothesis of the theorem it has integer width: **cut edges are H-tile edges**. -/
lemma intWidth_of_cut (hsides : ∀ i, (T i).HasIntegerSide) (hcut : Cut R T i) :
    ∃ m : ℤ, (T i).width = m :=
  (hsides i).resolve_right fun hh ↦ hcut (step_mem_reach_iff (.inr ⟨i, hh,
    .inl ⟨⟨rfl, le_rfl, (T i).hx⟩, rfl, le_rfl, (T i).hx⟩⟩))

variable [Fintype ι]

/-- Every point of the bottom edge of `R` lies on the bottom edge of a tile. -/
lemma exists_memBot_of_bot (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    {z : ℝ} (h₀ : R.x₀ ≤ z) (h₁ : z ≤ R.x₁) : ∃ i, MemBot (T i) ((z, R.y₀) : ℝ × ℝ) := by
  rcases h₁.lt_or_eq with hlt | rfl
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell false false
      (Rectangle.mem_cell_ff.mpr ⟨⟨h₀, hlt⟩, le_rfl, hy⟩)
    rcases Rectangle.mem_cell_ff.mp hi with ⟨⟨hx₀, hx₁⟩, hy₀, -⟩
    exact ⟨i, le_antisymm (hT.le_tile_y₀ i) hy₀, hx₀, hx₁.le⟩
  · obtain ⟨i, hi, -⟩ := hT.existsUnique_cell true false
      (Rectangle.mem_cell_tf.mpr ⟨⟨hx, le_rfl⟩, le_rfl, hy⟩)
    rcases Rectangle.mem_cell_tf.mp hi with ⟨⟨hx₀, hx₁⟩, hy₀, -⟩
    exact ⟨i, le_antisymm (hT.le_tile_y₀ i) hy₀, hx₀.le, hx₁⟩

/-- **The bottom edge of `R` is one vertex of Seymour's graph**: it is covered by the bottom
edges of the bottom row of tiles, so all its points are reachable in one segment move. -/
lemma mem_reach_of_bot (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) {z : ℝ}
    (h₀ : R.x₀ ≤ z) (h₁ : z ≤ R.x₁) : ((z, R.y₀) : ℝ × ℝ) ∈ Reach R T := by
  refine Relation.ReflTransGen.single (.inl ⟨rfl, fun x hx' ↦ ?_⟩)
  have hx'' : R.x₀ ≤ x ∧ x ≤ R.x₁ := by
    rcases mem_uIcc.mp hx' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨ha, hb.trans h₁⟩
    · exact ⟨h₀.trans ha, hb.trans hx.le⟩
  obtain ⟨i, hi⟩ := exists_memBot_of_bot hT hx hy hx''.1 hx''.2
  exact ⟨i, .inl hi⟩

/-! ### The telescope around a face -/

open scoped Classical in
/-- **The boundary telescope.** A family of intervals `[a i, b i]` partitioning `[lo, hi]` —
half-open covering plus uniqueness — telescopes any `ZMod 2` weight: the endpoint weights of the
members collapse to the weights of the two ends. Consecutive members share an endpoint, so this
is the discrete form of "walking around a face": instantiated below with the reachability
indicator along the two sides of a V-link, or along a boundary column of `R`, it computes the
parity of the cut around a face. -/
private lemma sum_partition {P : ι → Prop} {a b : ι → ℝ} {lo hi : ℝ} (χ : ℝ → ZMod 2)
    (hlohi : lo ≤ hi) (hab : ∀ i, P i → a i < b i) (hmem : ∀ i, P i → lo ≤ a i ∧ b i ≤ hi)
    (hcover : ∀ y, lo < y → y ≤ hi → ∃ i, P i ∧ a i < y ∧ y ≤ b i)
    (huniq : ∀ i j, P i → P j → ∀ y, a i < y → y ≤ b i → a j < y → y ≤ b j → i = j) :
    ∑ i ∈ Finset.univ.filter P, (χ (a i) + χ (b i)) = χ lo + χ hi := by
  have hself : ∀ v : ZMod 2, v + v = 0 := by decide
  have key : ∀ n (t : ℝ), lo ≤ t → t ≤ hi → (t = lo ∨ ∃ u, P u ∧ b u = t) →
      (Finset.univ.filter fun i ↦ P i ∧ b i ≤ t).card ≤ n →
      ∑ i ∈ Finset.univ.filter fun i ↦ P i ∧ b i ≤ t, (χ (a i) + χ (b i)) = χ lo + χ t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t hlot hthi hal hcard
      rcases hal with rfl | ⟨u, hu, hbu⟩
      · rw [Finset.filter_false_of_mem, Finset.sum_empty]
        · exact (hself _).symm
        · rintro i - ⟨hPi, hble⟩
          exact absurd ((hmem i hPi).1.trans_lt (hab i hPi)) (not_lt.mpr hble)
      · have hau_lo : lo ≤ a u := (hmem u hu).1
        have hau_hi : a u ≤ hi := (hab u hu).le.trans (hmem u hu).2
        have hal' : a u = lo ∨ ∃ v, P v ∧ b v = a u := by
          rcases hau_lo.lt_or_eq with hlt | heq
          · obtain ⟨v, hv, hav, hbv⟩ := hcover (a u) hlt hau_hi
            refine .inr ⟨v, hv, (hbv.eq_or_lt.resolve_right fun hlt' ↦ ?_).symm⟩
            have hy : a u < min (b v) (b u) := lt_min hlt' (hab u hu)
            have hvu := huniq v u hv hu (min (b v) (b u)) (hav.trans hy) (min_le_left _ _)
              hy (min_le_right _ _)
            exact absurd (hvu ▸ hav) (lt_irrefl _)
          · exact .inl heq.symm
        have hsplit : (Finset.univ.filter fun i ↦ P i ∧ b i ≤ t) =
            insert u (Finset.univ.filter fun i ↦ P i ∧ b i ≤ a u) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hPj, hbj⟩
            rcases eq_or_ne j u with rfl | hne
            · exact .inl rfl
            · refine .inr ⟨hPj, ?_⟩
              by_contra hcon
              push Not at hcon
              have haj : a j < b u := by
                by_contra hcon'
                push Not at hcon'
                exact absurd (hbu ▸ hcon'.trans_lt (hab j hPj)) (not_lt.mpr hbj)
              exact hne (huniq j u hPj hu (min (b j) (b u)) (lt_min (hab j hPj) haj)
                (min_le_left _ _) (lt_min hcon (hab u hu)) (min_le_right _ _))
          · rintro (rfl | ⟨hPj, hbj⟩)
            · exact ⟨hu, hbu.le⟩
            · exact ⟨hPj, hbj.trans ((hab u hu).le.trans hbu.le)⟩
        have hcard' : (Finset.univ.filter fun i ↦ P i ∧ b i ≤ a u).card < n := by
          refine lt_of_lt_of_le (Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hcon ↦ ?_⟩) hcard
          · rw [Finset.mem_filter] at hj ⊢
            exact ⟨hj.1, hj.2.1, hj.2.2.trans ((hab u hu).le.trans hbu.le)⟩
          · have hmem' := hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu, hbu.le⟩)
            exact absurd (Finset.mem_filter.mp hmem').2.2 (not_le.mpr (hab u hu))
        rw [hsplit, Finset.sum_insert fun hcon ↦
            absurd (Finset.mem_filter.mp hcon).2.2 (not_le.mpr (hab u hu)),
          ih _ hcard' (a u) hau_lo hau_hi hal' le_rfl, ← hbu]
        linear_combination hself (χ (a u))
  have hfil : Finset.univ.filter P = Finset.univ.filter fun i ↦ P i ∧ b i ≤ hi :=
    Finset.filter_congr fun i _ ↦ (and_iff_left_of_imp fun h ↦ (hmem i h).2).symm
  rw [hfil]
  rcases hlohi.lt_or_eq with hlt | rfl
  · obtain ⟨u, hu, -, hbu⟩ := hcover hi hlt le_rfl
    exact key _ hi hlohi le_rfl (.inr ⟨u, hu, le_antisymm (hmem u hu).2 hbu⟩) le_rfl
  · exact key _ lo le_rfl le_rfl (.inl rfl) le_rfl

/-! ### The faces of the embedding -/

/-- The tiles on the right of a link meet it in disjoint stretches, the mirror image of
`ReducibleLink.isLeft_unique`. -/
lemma isRight_unique (hT : IsTiling R T) (hp : Proper T) {l : Link R T} {i j : ι} {y : ℝ}
    (hi : IsRight l i) (hj : IsRight l j) (hyi : (T i).y₀ < y ∧ y ≤ (T i).y₁)
    (hyj : (T j).y₀ < y ∧ y ≤ (T j).y₁) : i = j :=
  hT.eq_of_mem_cell (sx := false) (sy := true) (x := l.c) (y := y)
    ⟨⟨hi.1.le, hi.1 ▸ (hp i).1⟩, hyi⟩ ⟨⟨hj.1.le, hj.1 ▸ (hp j).1⟩, hyj⟩

variable (R T) in
/-- A **face** of the planar embedding of Seymour's graph: a V-link of the tiling, or one of the
two outer faces into which the exterior edge divides the outside of `R`. -/
inductive Face : Type where
  /-- The outer face along the left edge of `R`. -/
  | left : Face
  /-- The outer face along the right edge of `R`. -/
  | right : Face
  /-- The face along a V-link of the tiling. -/
  | link (l : Link R T) : Face

/-- The abscissa of a face: the common abscissa of the vertical stretch it runs along. -/
def Face.c : Face R T → ℝ
  | .left => R.x₀
  | .right => R.x₁
  | .link l => l.c

/-- The face along the left edge of a tile: the left outer face when the tile reaches the left
edge of `R`, and otherwise the V-link its left edge lies on (`ReducibleLink.exists_link_left`). -/
noncomputable def leftFace (hT : IsTiling R T) (hp : Proper T) (i : ι) : Face R T :=
  if h : (T i).x₀ = R.x₀ then .left
  else .link (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose

/-- The face along the right edge of a tile. -/
noncomputable def rightFace (hT : IsTiling R T) (hp : Proper T) (i : ι) : Face R T :=
  if h : (T i).x₁ = R.x₁ then .right
  else .link (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne h)).choose

/-- The left face of a tile lies at the abscissa of its left edge. -/
lemma c_leftFace (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    (leftFace hT hp i).c = (T i).x₀ := by
  by_cases h : (T i).x₀ = R.x₀
  · simp only [leftFace, dif_pos h]
    exact h.symm
  · simp only [leftFace, dif_neg h]
    exact (exists_link_left hT hp ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose_spec.1

/-- The right face of a tile lies at the abscissa of its right edge. -/
lemma c_rightFace (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    (rightFace hT hp i).c = (T i).x₁ := by
  by_cases h : (T i).x₁ = R.x₁
  · simp only [rightFace, dif_pos h]
    exact h.symm
  · simp only [rightFace, dif_neg h]
    exact (exists_link_right hT hp ((hT.tile_x₁_le i).lt_of_ne h)).choose_spec.1

/-- The left face of a tile is the left outer face exactly when the tile reaches the left edge
of `R`. -/
lemma leftFace_eq_left_iff (hT : IsTiling R T) (hp : Proper T) :
    leftFace hT hp i = .left ↔ (T i).x₀ = R.x₀ := by
  unfold leftFace
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false nofun h

/-- The right face of a tile is the right outer face exactly when the tile reaches the right
edge of `R`. -/
lemma rightFace_eq_right_iff (hT : IsTiling R T) (hp : Proper T) :
    rightFace hT hp i = .right ↔ (T i).x₁ = R.x₁ := by
  unfold rightFace
  split
  · next h => exact iff_of_true rfl h
  · next h => exact iff_of_false nofun h

/-- The left face of a tile is never the right outer face. -/
lemma leftFace_ne_right (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    leftFace hT hp i ≠ .right := by
  unfold leftFace
  split <;> exact nofun

/-- The right face of a tile is never the left outer face. -/
lemma rightFace_ne_left (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    rightFace hT hp i ≠ .left := by
  unfold rightFace
  split <;> exact nofun

/-- **The left face of a tile is the V-link carrying its left edge**: `leftFace` lands on a link
exactly when the tile abuts it on its right side. Uniqueness is `Link.eq_of_overlap`. -/
lemma leftFace_eq_link_iff (hT : IsTiling R T) (hp : Proper T) {l : Link R T} :
    leftFace hT hp i = .link l ↔ IsRight l i := by
  by_cases h : (T i).x₀ = R.x₀
  · simp only [leftFace, dif_pos h]
    exact iff_of_false nofun fun hcon ↦
      absurd l.x₀_lt (by rw [← hcon.1, h]; exact lt_irrefl _)
  · simp only [leftFace, dif_neg h]
    obtain ⟨hc, hlo, hhi⟩ := (exists_link_left hT hp
      ((hT.le_tile_x₀ i).lt_of_ne fun h' ↦ h h'.symm)).choose_spec
    rw [Face.link.injEq]
    constructor
    · rintro rfl
      exact ⟨hc.symm, hlo, hhi⟩
    · rintro ⟨hc', hlo', hhi'⟩
      exact Link.eq_of_overlap (hc.trans hc') (hp i).2 hlo hhi hlo' hhi'

/-- **The right face of a tile is the V-link carrying its right edge**: `rightFace` lands on a
link exactly when the tile abuts it on its left side. -/
lemma rightFace_eq_link_iff (hT : IsTiling R T) (hp : Proper T) {l : Link R T} :
    rightFace hT hp i = .link l ↔ IsLeft l i := by
  by_cases h : (T i).x₁ = R.x₁
  · simp only [rightFace, dif_pos h]
    exact iff_of_false nofun fun hcon ↦
      absurd l.lt_x₁ (by rw [← hcon.1, h]; exact lt_irrefl _)
  · simp only [rightFace, dif_neg h]
    obtain ⟨hc, hlo, hhi⟩ := (exists_link_right hT hp
      ((hT.tile_x₁_le i).lt_of_ne h)).choose_spec
    rw [Face.link.injEq]
    constructor
    · rintro rfl
      exact ⟨hc.symm, hlo, hhi⟩
    · rintro ⟨hc', hlo', hhi'⟩
      exact Link.eq_of_overlap (hc.trans hc') (hp i).2 hlo hhi hlo' hhi'

/-! ### The parity of the cut around each face -/

open scoped Classical in
/-- The reachability indicator: the `ZMod 2` weight that the boundary telescopes count. -/
private noncomputable def reachInd (R : Rectangle) (T : ι → Rectangle) (p : ℝ × ℝ) : ZMod 2 :=
  if p ∈ Reach R T then 1 else 0

open scoped Classical in
/-- The number of cut tiles running along a face, modulo 2: the degree of the face in the dual
of the cut, the exterior edge not counted. -/
noncomputable def cutDeg (hT : IsTiling R T) (hp : Proper T) (F : Face R T) : ZMod 2 :=
  ∑ i ∈ Finset.univ.filter (Cut R T), ((if leftFace hT hp i = F then 1 else 0) +
    (if rightFace hT hp i = F then 1 else 0))

omit [Fintype ι] in
open scoped Classical in
/-- The reachability indicators of a bottom point and a top point of one tile sum to its cut
indicator. -/
private lemma reachInd_add_reachInd (hb : MemBot (T i) p) (ht : MemTop (T i) q) :
    reachInd R T p + reachInd R T q = if Cut R T i then 1 else 0 := by
  rw [reachInd, reachInd,
    if_congr (memBot_mem_reach_iff (q := (((T i).x₀, (T i).y₀) : ℝ × ℝ)) hb
      ⟨rfl, le_rfl, (T i).hx⟩) rfl rfl,
    if_congr (memTop_mem_reach_iff (q := (((T i).x₀, (T i).y₁) : ℝ × ℝ)) ht
      ⟨rfl, le_rfl, (T i).hx⟩) rfl rfl]
  simp only [Cut]
  by_cases h₁ : (((T i).x₀, (T i).y₀) : ℝ × ℝ) ∈ Reach R T <;>
    by_cases h₂ : (((T i).x₀, (T i).y₁) : ℝ × ℝ) ∈ Reach R T
  · rw [if_pos h₁, if_pos h₂, if_neg (not_not_intro (iff_of_true h₁ h₂))]
    exact CharTwo.add_self_eq_zero 1
  · rw [if_pos h₁, if_neg h₂, if_pos fun h ↦ h₂ (h.mp h₁), add_zero]
  · rw [if_neg h₁, if_pos h₂, if_pos fun h ↦ h₁ (h.mpr h₂), zero_add]
  · rw [if_neg h₁, if_neg h₂, if_neg (not_not_intro (iff_of_false h₁ h₂)), add_zero]

open scoped Classical in
/-- The cut count of a family of tiles carrying the points `(c, y₀ i)` and `(c, y₁ i)` on their
horizontal edges, rewritten as the sum their reachability indicators telescope. -/
private lemma sum_cut_eq_sum_reachInd {P : ι → Prop} {c : ℝ}
    (hbt : ∀ i, P i →
      MemBot (T i) ((c, (T i).y₀) : ℝ × ℝ) ∧ MemTop (T i) ((c, (T i).y₁) : ℝ × ℝ)) :
    ∑ i ∈ Finset.univ.filter (Cut R T), (if P i then (1 : ZMod 2) else 0) =
      ∑ i ∈ Finset.univ.filter P,
        (reachInd R T (c, (T i).y₀) + reachInd R T (c, (T i).y₁)) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hPi : P i
  · simp only [hPi, if_true]
    exact (reachInd_add_reachInd (hbt i hPi).1 (hbt i hPi).2).symm
  · simp only [hPi, if_false, ite_self]

/-- **The cut crosses every V-link face evenly** — the planar-duality parity at an inner face.
The tiles abutting the link on either side partition it, so on each side the cut count
telescopes to the reachability of the two ends of the link, and the two sides cancel. -/
theorem cutDeg_link (hT : IsTiling R T) (hp : Proper T) (l : Link R T) :
    cutDeg hT hp (.link l) = 0 := by
  classical
  have hleft : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if leftFace hT hp i = Face.link l then (1 : ZMod 2) else 0) =
      reachInd R T (l.c, l.lo) + reachInd R T (l.c, l.hi) := by
    rw [Finset.sum_congr rfl fun i _ ↦ if_congr (leftFace_eq_link_iff hT hp) rfl rfl,
      sum_cut_eq_sum_reachInd fun i hi ↦
        ⟨⟨rfl, hi.1.le, hi.1.symm.trans_le (T i).hx⟩,
          rfl, hi.1.le, hi.1.symm.trans_le (T i).hx⟩]
    exact sum_partition (fun y ↦ reachInd R T (l.c, y)) l.lo_lt_hi.le (fun i _ ↦ (hp i).2)
      (fun i hi ↦ ⟨hi.2.1, hi.2.2⟩) (fun y hy₀ hy₁ ↦ exists_isRight hT hp l hy₀ hy₁)
      fun i j hi hj y h₁ h₂ h₃ h₄ ↦ isRight_unique hT hp hi hj ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  have hright : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if rightFace hT hp i = Face.link l then (1 : ZMod 2) else 0) =
      reachInd R T (l.c, l.lo) + reachInd R T (l.c, l.hi) := by
    rw [Finset.sum_congr rfl fun i _ ↦ if_congr (rightFace_eq_link_iff hT hp) rfl rfl,
      sum_cut_eq_sum_reachInd fun i hi ↦
        ⟨⟨rfl, (T i).hx.trans hi.1.le, hi.1.ge⟩, rfl, (T i).hx.trans hi.1.le, hi.1.ge⟩]
    exact sum_partition (fun y ↦ reachInd R T (l.c, y)) l.lo_lt_hi.le (fun i _ ↦ (hp i).2)
      (fun i hi ↦ ⟨hi.2.1, hi.2.2⟩) (fun y hy₀ hy₁ ↦ exists_isLeft hT hp l hy₀ hy₁)
      fun i j hi hj y h₁ h₂ h₃ h₄ ↦ isLeft_unique hT hp hi hj ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  rw [cutDeg, Finset.sum_add_distrib, hleft, hright]
  exact CharTwo.add_self_eq_zero _

/-- **The cut crosses the left outer face oddly.** The tiles along the left edge of `R`
partition it, the telescope runs between the two left corners of `R`, and the bottom corner is
reachable while the top one is not: the exterior edge is the odd crossing that closes the
boundary of the outer face. -/
theorem cutDeg_left (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (htop : ∀ x : ℝ, ((x, R.y₁) : ℝ × ℝ) ∉ Reach R T) : cutDeg hT hp .left = 1 := by
  classical
  have hright : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if rightFace hT hp i = Face.left then (1 : ZMod 2) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ if_neg (rightFace_ne_left hT hp i)
  have hleft : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if leftFace hT hp i = Face.left then (1 : ZMod 2) else 0) =
      reachInd R T (R.x₀, R.y₀) + reachInd R T (R.x₀, R.y₁) := by
    rw [Finset.sum_congr rfl fun i _ ↦ if_congr (leftFace_eq_left_iff hT hp) rfl rfl,
      sum_cut_eq_sum_reachInd fun i hi ↦
        ⟨⟨rfl, hi.le, hi.symm.trans_le (T i).hx⟩, rfl, hi.le, hi.symm.trans_le (T i).hx⟩]
    refine sum_partition (fun y ↦ reachInd R T (R.x₀, y)) hy.le (fun i _ ↦ (hp i).2)
      (fun i _ ↦ ⟨hT.le_tile_y₀ i, hT.tile_y₁_le i⟩) (fun y hy₀ hy₁ ↦ ?_)
      fun i j hi hj y h₁ h₂ h₃ h₄ ↦ hT.eq_of_mem_cell (sx := false) (sy := true)
        (x := R.x₀) (y := y) ⟨⟨hi.le, hi ▸ (hp i).1⟩, h₁, h₂⟩ ⟨⟨hj.le, hj ▸ (hp j).1⟩, h₃, h₄⟩
    obtain ⟨j, hj, -⟩ := hT.existsUnique_cell false true
      (Rectangle.mem_cell_ft.mpr ⟨⟨le_rfl, hx⟩, hy₀, hy₁⟩)
    rcases Rectangle.mem_cell_ft.mp hj with ⟨⟨hx₀, -⟩, hyj⟩
    exact ⟨j, le_antisymm hx₀ (hT.le_tile_x₀ j), hyj⟩
  rw [cutDeg, Finset.sum_add_distrib, hleft, hright, add_zero, reachInd, reachInd,
    if_pos (show ((R.x₀, R.y₀) : ℝ × ℝ) ∈ Reach R T from Relation.ReflTransGen.refl),
    if_neg (htop R.x₀), add_zero]

/-- **The cut crosses the right outer face oddly**, the mirror image of `cutDeg_left`. -/
theorem cutDeg_right (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (htop : ∀ x : ℝ, ((x, R.y₁) : ℝ × ℝ) ∉ Reach R T) : cutDeg hT hp .right = 1 := by
  classical
  have hleft : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if leftFace hT hp i = Face.right then (1 : ZMod 2) else 0) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ if_neg (leftFace_ne_right hT hp i)
  have hright : ∑ i ∈ Finset.univ.filter (Cut R T),
      (if rightFace hT hp i = Face.right then (1 : ZMod 2) else 0) =
      reachInd R T (R.x₁, R.y₀) + reachInd R T (R.x₁, R.y₁) := by
    rw [Finset.sum_congr rfl fun i _ ↦ if_congr (rightFace_eq_right_iff hT hp) rfl rfl,
      sum_cut_eq_sum_reachInd fun i hi ↦
        ⟨⟨rfl, (T i).hx.trans hi.le, hi.ge⟩, rfl, (T i).hx.trans hi.le, hi.ge⟩]
    refine sum_partition (fun y ↦ reachInd R T (R.x₁, y)) hy.le (fun i _ ↦ (hp i).2)
      (fun i _ ↦ ⟨hT.le_tile_y₀ i, hT.tile_y₁_le i⟩) (fun y hy₀ hy₁ ↦ ?_)
      fun i j hi hj y h₁ h₂ h₃ h₄ ↦ hT.eq_of_mem_cell (sx := true) (sy := true)
        (x := R.x₁) (y := y) ⟨⟨(hp i).1.trans_le hi.le, hi.ge⟩, h₁, h₂⟩
        ⟨⟨(hp j).1.trans_le hj.le, hj.ge⟩, h₃, h₄⟩
    obtain ⟨j, hj, -⟩ := hT.existsUnique_cell true true
      (Rectangle.mem_cell_tt.mpr ⟨⟨hx, le_rfl⟩, hy₀, hy₁⟩)
    rcases Rectangle.mem_cell_tt.mp hj with ⟨⟨-, hx₁⟩, hyj⟩
    exact ⟨j, le_antisymm (hT.tile_x₁_le j) hx₁, hyj⟩
  rw [cutDeg, Finset.sum_add_distrib, hleft, hright, zero_add, reachInd, reachInd,
    if_pos (mem_reach_of_bot hT hx hy hx.le le_rfl), if_neg (htop R.x₁), add_zero]

/-! ### The dual path -/

/-- A step of the dual path: a cut tile joins the faces along its two vertical edges — the dual
edge of a cut edge of Seymour's graph. -/
def DualStep (hT : IsTiling R T) (hp : Proper T) (f g : Face R T) : Prop :=
  ∃ i, Cut R T i ∧ (leftFace hT hp i = f ∧ rightFace hT hp i = g ∨
    leftFace hT hp i = g ∧ rightFace hT hp i = f)

/-- **The dual path exists**: when no vertex at the top of `R` is reachable, the right outer
face is joined to the left outer face through cut tiles — the path Wagon obtains from the dual
cycle of a minimal cut by deleting the dual of the exterior edge. Here it falls out of the
parities by a handshake in `ZMod 2`: the faces joined to the left outer face are closed under
crossing cut tiles, so the cut degrees they see sum to zero — yet they include `Face.left`, of
odd degree, so they must also include the only other face of odd degree, `Face.right`. -/
theorem reflTransGen_dualStep (hT : IsTiling R T) (hp : Proper T) (hx : R.x₀ < R.x₁)
    (hy : R.y₀ < R.y₁) (htop : ∀ x : ℝ, ((x, R.y₁) : ℝ × ℝ) ∉ Reach R T) :
    Relation.ReflTransGen (DualStep hT hp) .left .right := by
  classical
  by_contra hcon
  set D : Set (Face R T) := {f | Relation.ReflTransGen (DualStep hT hp) .left f} with hD
  set s : Finset (Face R T) := insert .left (insert .right
    ((Finset.univ.filter (Cut R T)).image (leftFace hT hp) ∪
      (Finset.univ.filter (Cut R T)).image (rightFace hT hp))) with hs
  have hstep : ∀ i, Cut R T i →
      D.indicator (fun _ ↦ (1 : ZMod 2)) (leftFace hT hp i) +
        D.indicator (fun _ ↦ (1 : ZMod 2)) (rightFace hT hp i) = 0 := by
    intro i hcut
    by_cases hm : leftFace hT hp i ∈ D
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show rightFace hT hp i ∈ D from
        Relation.ReflTransGen.tail hm ⟨i, hcut, .inl ⟨rfl, rfl⟩⟩)]
      decide
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem
        (show rightFace hT hp i ∉ D from
          fun h ↦ hm (Relation.ReflTransGen.tail h ⟨i, hcut, .inr ⟨rfl, rfl⟩⟩)), add_zero]
  have hA : ∑ F ∈ s, D.indicator (fun _ ↦ (1 : ZMod 2)) F * cutDeg hT hp F = 1 := by
    have hzero : ∀ F ∈ s, F ≠ Face.left →
        D.indicator (fun _ ↦ (1 : ZMod 2)) F * cutDeg hT hp F = 0 := by
      intro F hF hne
      rcases F with _ | _ | l
      · exact absurd rfl hne
      · rw [Set.indicator_of_notMem (show (Face.right : Face R T) ∉ D from hcon), zero_mul]
      · rw [cutDeg_link hT hp l, mul_zero]
    rw [Finset.sum_eq_single_of_mem Face.left (Finset.mem_insert_self _ _) hzero,
      Set.indicator_of_mem (show (Face.left : Face R T) ∈ D from Relation.ReflTransGen.refl),
      one_mul, cutDeg_left hT hp hx hy htop]
  have hB : ∑ F ∈ s, D.indicator (fun _ ↦ (1 : ZMod 2)) F * cutDeg hT hp F = 0 := by
    simp only [cutDeg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hcut := (Finset.mem_filter.mp hi).2
    have hmeml : leftFace hT hp i ∈ s :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)))
    have hmemr : rightFace hT hp i ∈ s :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi)))
    rw [Finset.sum_congr rfl fun F _ ↦ by
        rw [mul_add, mul_ite, mul_one, mul_zero, mul_ite, mul_one, mul_zero],
      Finset.sum_add_distrib, Finset.sum_ite_eq s (leftFace hT hp i) _,
      Finset.sum_ite_eq s (rightFace hT hp i) _, if_pos hmeml, if_pos hmemr]
    exact hstep i hcut
  rw [hA] at hB
  exact one_ne_zero hB

/-- **The dual path moves by integer steps**: each of its steps crosses a cut tile, of integer
width, so every face joined to the left outer face sits an integer distance to the right of the
left edge of `R`. -/
lemma int_c_sub_x₀_of_reflTransGen (hT : IsTiling R T) (hp : Proper T)
    (hsides : ∀ i, (T i).HasIntegerSide) {F : Face R T}
    (h : Relation.ReflTransGen (DualStep hT hp) .left F) : ∃ m : ℤ, F.c - R.x₀ = m := by
  induction h with
  | refl => exact ⟨0, by simp only [Face.c, sub_self, Int.cast_zero]⟩
  | tail _ hstep ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨i, hcut, hcase⟩ := hstep
    obtain ⟨n, hn⟩ := intWidth_of_cut hsides hcut
    rw [Rectangle.width] at hn
    rcases hcase with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [← hl, c_leftFace] at hm
      exact ⟨m + n, by rw [← hr, c_rightFace]; push_cast; linarith⟩
    · rw [← hr, c_rightFace] at hm
      exact ⟨m - n, by rw [← hl, c_leftFace]; push_cast; linarith⟩

/-- **The second alternative of the dichotomy**: when no vertex at the top of `R` is reachable,
the width of `R` is an integer, read off the dual path. -/
theorem intWidth_of_not_reach_top (hT : IsTiling R T) (hp : Proper T)
    (hsides : ∀ i, (T i).HasIntegerSide) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁)
    (htop : ∀ x : ℝ, ((x, R.y₁) : ℝ × ℝ) ∉ Reach R T) : ∃ m : ℤ, R.width = m :=
  int_c_sub_x₀_of_reflTransGen hT hp hsides (reflTransGen_dualStep hT hp hx hy htop)

end CutSet

end IntegerRectangle

open IntegerRectangle IntegerRectangle.CutSet in
/-- **Minimal cut-set proof** (Seymour) of the integer-rectangle tiling theorem. Delete the
H-tile edges and the exterior edge from Seymour's graph of horizontal segments: either the top
of `R` stays reachable from the bottom — across V-tiles, so the height of `R` is an integer —
or the cut around the reachable region dualizes, by the planar duality of the tiling graph read
on its concrete faces, to a path of H-tiles from the left edge of `R` to its right edge, and
the width of `R` is an integer. -/
theorem IntegerRectangleTheorem_CutSet : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  classical
  rcases eq_or_lt_of_le R.hx with hx | hx
  · exact .inl ⟨0, by simp [Rectangle.width, ← hx]⟩
  rcases eq_or_lt_of_le R.hy with hy | hy
  · exact .inr ⟨0, by simp [Rectangle.height, ← hy]⟩
  by_cases hcase : ∃ x : ℝ, ((x, R.y₁) : ℝ × ℝ) ∈ Reach R (properTiles T)
  · obtain ⟨x, hmem⟩ := hcase
    exact .inr (int_sub_y₀_of_mem_reach hmem)
  · push Not at hcase
    exact .inl (intWidth_of_not_reach_top (hT.proper hx hy) (proper_properTiles T)
      (fun j ↦ hsides j.1) hx hy hcase)
