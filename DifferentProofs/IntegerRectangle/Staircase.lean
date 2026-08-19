module

public import DifferentProofs.IntegerRectangle.Walks
public import DifferentProofsForMathlib.Algebra.Order.Floor.Ring
public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem by induction on the number of H-tiles

Robinson's ninth proof. Call a tile an *H-tile* if it is designated by its integer width and a
*V-tile* if it is designated by its integer height. Splitting each tile along its designated side
normalizes the tiling: every H-tile then has width exactly `1` and every V-tile height exactly `1`
(`Normalized`, `IsTiling.normalized`). Robinson's induction runs on the number of H-tiles of a
normalized tiling. If there are none, every tile has integer height and so does `R`. Otherwise
pick an H-tile and grow a vertical strip of width `1` from it, upwards and downwards: the strip
runs straight up through V-tiles until an H-tile blocks it, at which point it steps sideways onto
that H-tile and continues. Deleting the strip and sliding what is to its right one unit leftwards
tiles a rectangle one unit narrower with fewer H-tiles, and the induction applies to it.
-/

@[expose] public section

namespace IntegerRectangle.Staircase

variable {ι : Type} [Fintype ι] {R S : Rectangle} {T : ι → Rectangle} {H : ι → Prop}

/-! ### Normalized tilings -/

/-- A tiling is *normalized*, with `H` designating its H-tiles, when it is proper, every H-tile
has width exactly `1`, and every other tile — every V-tile — has height exactly `1`. -/
structure Normalized (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop) : Prop where
  /-- The tiles tile `R`. -/
  tiling : IsTiling R T
  /-- No tile is degenerate. -/
  proper : Proper T
  /-- H-tiles are one unit wide. -/
  width_one : ∀ i, H i → (T i).width = 1
  /-- V-tiles are one unit tall. -/
  height_one : ∀ i, ¬ H i → (T i).height = 1

/-- An H-tile is one unit wide. -/
lemma x₁_eq_of_H (hn : Normalized R T H) {k : ι} (hk : H k) : (T k).x₁ = (T k).x₀ + 1 := by
  simpa [Rectangle.width, sub_eq_iff_eq_add'] using hn.width_one k hk

/-- A V-tile is one unit tall. -/
lemma y₁_eq_of_not_H (hn : Normalized R T H) {j : ι} (hj : ¬ H j) : (T j).y₁ = (T j).y₀ + 1 := by
  simpa [Rectangle.height, sub_eq_iff_eq_add'] using hn.height_one j hj

/-- A tiled rectangle is nondegenerate horizontally, since its tiles are. -/
lemma Normalized.pos_width (hn : Normalized R T H) : R.x₀ < R.x₁ :=
  have ⟨i⟩ := hn.tiling.nonempty_index
  lt_of_le_of_lt (hn.tiling.le_tile_x₀ i) ((hn.proper i).1.trans_le (hn.tiling.tile_x₁_le i))

/-- A tiled rectangle is nondegenerate vertically, since its tiles are. -/
lemma Normalized.pos_height (hn : Normalized R T H) : R.y₀ < R.y₁ :=
  have ⟨i⟩ := hn.tiling.nonempty_index
  lt_of_le_of_lt (hn.tiling.le_tile_y₀ i) ((hn.proper i).2.trans_le (hn.tiling.tile_y₁_le i))

/-- A tile is cut along its width when that is an integer, and along its height otherwise. -/
def CutsWidth (S : Rectangle) : Prop := ∃ m : ℤ, S.width = m

open scoped Classical in
/-- The number of unit pieces a tile is cut into: its width if that is an integer, and its height
otherwise. -/
noncomputable def pieceCount (S : Rectangle) : ℕ :=
  if CutsWidth S then ⌊S.width⌋₊ else ⌊S.height⌋₊

open scoped Classical in
/-- The `j`-th unit piece of a tile, counted from its lower left corner along the side it is cut
along. -/
noncomputable def piece (S : Rectangle) (j : ℕ) : Rectangle :=
  if CutsWidth S then
    { x₀ := S.x₀ + j, x₁ := S.x₀ + j + 1, y₀ := S.y₀, y₁ := S.y₁, hx := by linarith, hy := S.hy }
  else
    { x₀ := S.x₀, x₁ := S.x₁, y₀ := S.y₀ + j, y₁ := S.y₀ + j + 1, hx := S.hx, hy := by linarith }

/-- An interval whose length is a whole number is exhausted by that many unit steps. -/
private lemma add_floor_sub {a b : ℝ} (hab : a < b) (h : ∃ m : ℤ, b - a = m) :
    a + ⌊b - a⌋₊ = b := by
  obtain ⟨m, hm⟩ := h
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast hm ▸ sub_nonneg.mpr hab.le
  rw [hm, Nat.floor_intCast, ← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  linarith

/-- The pieces of a tile cut along its width exhaust that width. -/
private lemma add_pieceCount_width (h : CutsWidth S) (hx : S.x₀ < S.x₁) :
    S.x₀ + pieceCount S = S.x₁ := by
  classical
  rw [pieceCount, if_pos h]
  exact add_floor_sub hx h

/-- The pieces of a tile cut along its height exhaust that height. -/
private lemma add_pieceCount_height (hS : S.HasIntegerSide) (h : ¬ CutsWidth S) (hy : S.y₀ < S.y₁) :
    S.y₀ + pieceCount S = S.y₁ := by
  classical
  rw [pieceCount, if_neg h]
  exact add_floor_sub hy (hS.resolve_left h)

private lemma piece_width_of_cutsWidth (h : CutsWidth S) (j : ℕ) : (piece S j).width = 1 := by
  simp only [piece, if_pos h, Rectangle.width]
  ring

private lemma piece_height_of_not_cutsWidth (h : ¬ CutsWidth S) (j : ℕ) :
    (piece S j).height = 1 := by
  simp only [piece, if_neg h, Rectangle.height]
  ring

/-- Each piece is proper: it is one unit long along the side it is cut from, and keeps the other
side of the tile it comes from. -/
private lemma piece_nondegenerate (hnd : S.Nondegenerate) (j : ℕ) :
    (piece S j).Nondegenerate := by
  classical
  rw [Rectangle.Nondegenerate, piece]
  split_ifs
  exacts [⟨by simp, hnd.2⟩, ⟨hnd.1, by simp⟩]

/-- A piece with a legitimate index sits inside the tile it comes from. -/
private lemma piece_le (hS : S.HasIntegerSide) (hnd : S.Nondegenerate) {j : ℕ}
    (hj : j < pieceCount S) :
    S.x₀ ≤ (piece S j).x₀ ∧ (piece S j).x₁ ≤ S.x₁ ∧ S.y₀ ≤ (piece S j).y₀ ∧
      (piece S j).y₁ ≤ S.y₁ := by
  classical
  have hj' : (j : ℝ) + 1 ≤ pieceCount S := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [piece]
  split_ifs with h
  · have := add_pieceCount_width h hnd.1
    exact ⟨by linarith, by linarith, le_rfl, le_rfl⟩
  · have := add_pieceCount_height hS h hnd.2
    exact ⟨le_rfl, le_rfl, by linarith, by linarith⟩

private lemma piece_subset (hS : S.HasIntegerSide) (hnd : S.Nondegenerate) {j : ℕ}
    (hj : j < pieceCount S) : (piece S j).toSet ⊆ S.toSet := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := piece_le hS hnd hj
  rintro ⟨a, b⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private lemma piece_subset_toSetIoc (hS : S.HasIntegerSide) (hnd : S.Nondegenerate) {j : ℕ}
    (hj : j < pieceCount S) : (piece S j).toSetIoc ⊆ S.toSetIoc := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := piece_le hS hnd hj
  rintro ⟨a, b⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The index of the piece containing a point: the ceiling of its distance from the cut side. -/
private lemma exists_index {a b t : ℝ} (hat : a < t) (htb : t ≤ b) {n : ℕ} (hn : a + n = b) :
    ∃ j : ℕ, j < n ∧ a + j < t ∧ t ≤ a + j + 1 := by
  have h1 : 1 ≤ ⌈t - a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcast : ((⌈t - a⌉₊ - 1 : ℕ) : ℝ) = (⌈t - a⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  refine ⟨⌈t - a⌉₊ - 1, ?_, ?_, ?_⟩
  · have : ⌈t - a⌉₊ ≤ n := Nat.ceil_le.mpr (by linarith)
    lia
  · rw [hcast]
    linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t - a by linarith)]
  · rw [hcast]
    linarith [Nat.le_ceil (t - a)]

/-- Every point of a tile lies in the half-open cell of one of its pieces. -/
private lemma exists_mem_piece (hS : S.HasIntegerSide) (hnd : S.Nondegenerate) {x y : ℝ}
    (hz : (x, y) ∈ S.toSetIoc) :
    ∃ j : ℕ, j < pieceCount S ∧ (x, y) ∈ (piece S j).toSetIoc := by
  classical
  obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hz
  by_cases h : CutsWidth S
  · obtain ⟨j, hj, hj₁, hj₂⟩ := exists_index h₁ h₂ (add_pieceCount_width h hnd.1)
    exact ⟨j, hj, by rw [Rectangle.mem_toSetIoc', piece, if_pos h]; exact ⟨⟨hj₁, hj₂⟩, h₃, h₄⟩⟩
  · obtain ⟨j, hj, hj₁, hj₂⟩ := exists_index h₃ h₄ (add_pieceCount_height hS h hnd.2)
    exact ⟨j, hj, by rw [Rectangle.mem_toSetIoc', piece, if_neg h]; exact ⟨⟨h₁, h₂⟩, hj₁, hj₂⟩⟩

/-- Distinct pieces of a tile have disjoint half-open cells. -/
private lemma piece_disjoint {j j' : ℕ} (hjj : j ≠ j') :
    Disjoint (piece S j).toSetIoc (piece S j').toSetIoc := by
  classical
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hj hj'
  have hne : ∀ {a b : ℕ}, a < b → (a : ℝ) + 1 ≤ b := fun h ↦ by exact_mod_cast h
  rw [piece] at hj hj'
  split_ifs at hj hj' with h <;> simp only [Rectangle.mem_toSetIoc] at hj hj' <;>
    rcases lt_or_gt_of_ne hjj with hlt | hlt
  · linarith [hj.1.2, hj'.1.1, hne hlt]
  · linarith [hj'.1.2, hj.1.1, hne hlt]
  · linarith [hj.2.2, hj'.2.1, hne hlt]
  · linarith [hj'.2.2, hj.2.1, hne hlt]

/-- The index type of the normalized tiling attached to `T`: one index per unit piece of each
nondegenerate tile. -/
abbrev PieceIndex (T : ι → Rectangle) : Type :=
  Σ i : {i : ι // (T i).Nondegenerate}, Fin (pieceCount (properTiles T i))

/-- **The normalized tiling attached to a tiling by tiles with an integer side**: drop the
degenerate tiles and cut each of the others into unit pieces along a side of integer length. -/
noncomputable def pieceTiles (T : ι → Rectangle) (p : PieceIndex T) : Rectangle :=
  piece (properTiles T p.1) p.2

/-- The H-tiles of the normalized tiling: the pieces of the tiles cut along their width. -/
def PieceCutsWidth (T : ι → Rectangle) (p : PieceIndex T) : Prop :=
  CutsWidth (properTiles T p.1)

/-- **Cutting each tile into unit pieces normalizes a tiling.** Every tile has a side of integer
length, at least one unit long since the tile is nondegenerate, and the half-open cells of the
pieces of a tile partition its own. -/
theorem _root_.IntegerRectangle.IsTiling.normalized (hT : IsTiling R T) (hx : R.x₀ < R.x₁)
    (hy : R.y₀ < R.y₁)
    (hsides : ∀ i, (T i).HasIntegerSide) :
    Normalized R (pieceTiles T) (PieceCutsWidth T) := by
  classical
  have hT₁ : IsTiling R (properTiles T) := hT.proper hx hy
  have hs : ∀ i : {i : ι // (T i).Nondegenerate}, (properTiles T i).HasIntegerSide :=
    fun i ↦ hsides i.1
  refine ⟨?_, fun p ↦ piece_nondegenerate p.1.2 p.2, fun p hp ↦ piece_width_of_cutsWidth hp p.2,
    fun p hp ↦ piece_height_of_not_cutsWidth hp p.2⟩
  refine isTiling_of_toSetIoc hx hy
    (fun p ↦ (piece_subset (hs p.1) p.1.2 p.2.2).trans (hT₁.tile_subset p.1))
    (fun p q hpq ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨p₁, p₂⟩ := p
    obtain ⟨q₁, q₂⟩ := q
    rw [Function.onFun]
    rcases eq_or_ne p₁ q₁ with heq | hne
    · subst heq
      exact piece_disjoint fun hcon ↦ hpq (congrArg _ (Fin.val_injective hcon))
    · exact (hT₁.pairwiseDisjoint_toSetIoc hne).mono
        (piece_subset_toSetIoc (hs p₁) p₁.2 p₂.2) (piece_subset_toSetIoc (hs q₁) q₁.2 q₂.2)
  · obtain ⟨x, y⟩ := z
    obtain ⟨i, hi, -⟩ := hT₁.existsUnique_toSetIoc hz
    obtain ⟨j, hj, hmem⟩ := exists_mem_piece (hs i) i.2 hi
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨j, hj⟩⟩, hmem⟩

/-! ### Cutting a tiling along a staircase strip -/

/-- The part of a tile to the left of the strip of width `1` with left edge at `c`. It is
degenerate exactly when the tile does not reach past `c`. -/
def cutLeft (S : Rectangle) (c : ℝ) : Rectangle where
  x₀ := min S.x₀ c
  x₁ := min S.x₁ c
  y₀ := S.y₀
  y₁ := S.y₁
  hx := min_le_min S.hx le_rfl
  hy := S.hy

/-- The part of a tile to the right of the strip of width `1` with left edge at `c`, slid one unit
leftwards. It is degenerate exactly when the tile does not reach past `c + 1`. -/
def cutRight (S : Rectangle) (c : ℝ) : Rectangle where
  x₀ := max S.x₀ (c + 1) - 1
  x₁ := max S.x₁ (c + 1) - 1
  y₀ := S.y₀
  y₁ := S.y₁
  hx := by have := max_le_max S.hx (le_refl (c + 1)); linarith
  hy := S.hy

/-- The two pieces a tile is cut into by the strip of width `1` with left edge at `c`. A tile
lying inside the strip is cut into two degenerate pieces, and so disappears. -/
def cutPiece (S : Rectangle) (c : ℝ) : Bool → Rectangle
  | false => cutLeft S c
  | true => cutRight S c

@[simp] lemma cutPiece_y₀ (S : Rectangle) (c : ℝ) (b : Bool) : (cutPiece S c b).y₀ = S.y₀ := by
  cases b <;> rfl

@[simp] lemma cutPiece_y₁ (S : Rectangle) (c : ℝ) (b : Bool) : (cutPiece S c b).y₁ = S.y₁ := by
  cases b <;> rfl

/-- The rectangle left over when a strip of width `1` is cut out of `R`. -/
def cutRect (R : Rectangle) (h : R.x₀ + 1 ≤ R.x₁) : Rectangle where
  x₀ := R.x₀
  x₁ := R.x₁ - 1
  y₀ := R.y₀
  y₁ := R.y₁
  hx := by linarith
  hy := R.hy

private lemma mem_cutLeft {S : Rectangle} {c x y : ℝ}
    (h : (x, y) ∈ (cutLeft S c).toSetIoc) :
    (x, y) ∈ S.toSetIoc ∧ x ≤ c := by
  simp only [Rectangle.mem_toSetIoc', cutLeft] at h ⊢
  grind

private lemma mem_cutRight {S : Rectangle} {c x y : ℝ}
    (h : (x, y) ∈ (cutRight S c).toSetIoc) :
    (x + 1, y) ∈ S.toSetIoc ∧ c < x := by
  simp only [Rectangle.mem_toSetIoc', cutRight] at h ⊢
  grind

private lemma mem_cutLeft_of_le {S : Rectangle} {c x y : ℝ} (h : (x, y) ∈ S.toSetIoc)
    (hc : x ≤ c) :
    (x, y) ∈ (cutLeft S c).toSetIoc := by
  simp only [Rectangle.mem_toSetIoc', cutLeft] at h ⊢
  grind

private lemma mem_cutRight_of_lt {S : Rectangle} {c x y : ℝ} (h : (x + 1, y) ∈ S.toSetIoc)
    (hc : c < x) : (x, y) ∈ (cutRight S c).toSetIoc := by
  simp only [Rectangle.mem_toSetIoc', cutRight] at h ⊢
  grind

/-- A *staircase strip* for a tiling, running across the heights `(a, b]`.

The strip is one unit wide but it does not stand straight: it is a staircase, so which vertical
line carries its left edge depends on how high one looks. That is what `c : ℝ → ℝ` records — at
height `y` the strip is `[c y, c y + 1] × {y}`. It is a step function, constant along each
*column* of the staircase and jumping at the finitely many heights where the staircase steps
sideways, but only the following three properties of it are ever used, so it is taken as an
arbitrary function of the height.

Each tile lies to the left of the strip at each of its heights, or to its right, or inside it; a
tile inside the strip meets no other column of the staircase, and if it is an H-tile it fills the
strip exactly. And no tile lies to the left of the strip at one of its heights and to the right of
it at another: the staircase is a wall. -/
structure Strip (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop) (a b : ℝ) (c : ℝ → ℝ) :
    Prop where
  /-- The strip stays inside `R`. -/
  mem : ∀ y, a < y → y ≤ b → R.x₀ ≤ c y ∧ c y + 1 ≤ R.x₁
  /-- At each of its heights a tile is left of, right of, or inside the strip. -/
  side : ∀ (j : ι) (y : ℝ), a < y → y ≤ b → (T j).y₀ < y → y ≤ (T j).y₁ →
      (T j).x₁ ≤ c y ∨ c y + 1 ≤ (T j).x₀ ∨
        (a ≤ (T j).y₀ ∧ (T j).y₁ ≤ b ∧ (∀ t, (T j).y₀ < t → t ≤ (T j).y₁ → c t = c y) ∧
          (H j → (T j).x₀ = c y ∧ (T j).x₁ = c y + 1))
  /-- No tile is left of the strip at one height and right of it at another. -/
  consistent : ∀ (j : ι) (y y' : ℝ), a < y → y ≤ b → a < y' → y' ≤ b → (T j).y₀ < y →
      y ≤ (T j).y₁ → (T j).y₀ < y' → y' ≤ (T j).y₁ → (T j).x₁ ≤ c y → c y' + 1 ≤ (T j).x₀ → False

open scoped Classical in
/-- The abscissa at which the strip cuts a tile: its right edge if the tile is left of the strip,
its left edge less one if it is right of the strip, and the left edge of the strip if the tile
lies inside it. -/
noncomputable def cutAt (T : ι → Rectangle) (c : ℝ → ℝ) (j : ι) : ℝ :=
  if (T j).x₁ ≤ c (T j).y₁ then (T j).x₁
  else if c (T j).y₁ + 1 ≤ (T j).x₀ then (T j).x₀ - 1 else c (T j).y₁

variable {c : ℝ → ℝ}

/-- **A tile is cut at the same abscissa at every one of its heights.** The three cases are the
three alternatives of `Strip.side`, and it is consistency of the strip that keeps a tile in the
same case throughout. -/
private lemma cutAt_spec (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) (j : ι) {y : ℝ}
    (h₀ : (T j).y₀ < y) (h₁ : y ≤ (T j).y₁) :
    (cutAt T c j = (T j).x₁ ∧ (T j).x₁ ≤ c y) ∨
      (cutAt T c j = (T j).x₀ - 1 ∧ c y + 1 ≤ (T j).x₀) ∨
      (cutAt T c j = c y ∧ (H j → (T j).x₀ = c y ∧ (T j).x₁ = c y + 1)) := by
  classical
  have hjy : (T j).y₀ < (T j).y₁ := (hn.proper j).2
  have hY₀ : R.y₀ < (T j).y₁ := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) hjy
  have hY₁ : (T j).y₁ ≤ R.y₁ := hn.tiling.tile_y₁_le j
  have hy₀ : R.y₀ < y := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) h₀
  have hy₁ : y ≤ R.y₁ := h₁.trans hY₁
  -- the strip has the same abscissa at `y` as at the top edge of the tile in the third case
  have hside := hs.side j y hy₀ hy₁ h₀ h₁
  by_cases hL : (T j).x₁ ≤ c (T j).y₁
  · refine Or.inl ⟨by rw [cutAt, if_pos hL], ?_⟩
    rcases hside with h | h | ⟨-, -, hconst, -⟩
    · exact h
    · exact (hs.consistent j (T j).y₁ y hY₀ hY₁ hy₀ hy₁ hjy le_rfl h₀ h₁ hL h).elim
    · rw [hconst (T j).y₁ hjy le_rfl] at hL
      exact hL
  by_cases hR : c (T j).y₁ + 1 ≤ (T j).x₀
  · refine Or.inr (Or.inl ⟨by rw [cutAt, if_neg hL, if_pos hR], ?_⟩)
    rcases hside with h | h | ⟨-, -, hconst, -⟩
    · exact (hs.consistent j y (T j).y₁ hy₀ hy₁ hY₀ hY₁ h₀ h₁ hjy le_rfl h hR).elim
    · exact h
    · rw [hconst (T j).y₁ hjy le_rfl] at hR
      exact hR
  · -- the tile meets the strip at its top edge, so it lies inside it and follows it
    refine Or.inr (Or.inr ?_)
    rw [cutAt, if_neg hL, if_neg hR]
    rcases hs.side j (T j).y₁ hY₀ hY₁ hjy le_rfl with h | h | ⟨-, -, hconst, halign⟩
    · exact absurd h hL
    · exact absurd h hR
    · refine ⟨(hconst y h₀ h₁).symm, fun hj ↦ ?_⟩
      rw [hconst y h₀ h₁]
      exact halign hj

/-- The cut abscissa of a tile stays inside the horizontal extent of the shrunken rectangle. -/
private lemma cutAt_mem (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) (j : ι) :
    R.x₀ ≤ cutAt T c j ∧ cutAt T c j ≤ R.x₁ - 1 := by
  have hjy : (T j).y₀ < (T j).y₁ := (hn.proper j).2
  have hy₀ : R.y₀ < (T j).y₁ := lt_of_le_of_lt (hn.tiling.le_tile_y₀ j) hjy
  have hy₁ : (T j).y₁ ≤ R.y₁ := hn.tiling.tile_y₁_le j
  obtain ⟨hm₀, hm₁⟩ := hs.mem (T j).y₁ hy₀ hy₁
  have hx₀ := hn.tiling.le_tile_x₀ j
  have hx₁ := hn.tiling.tile_x₁_le j
  rcases cutAt_spec hn hs j hjy le_rfl with ⟨he, hle⟩ | ⟨he, hle⟩ | ⟨he, -⟩ <;> rw [he] <;>
    constructor <;> linarith [(hn.proper j).1]

/-- The left piece of a tile lies in the tile, to the left of the strip. -/
private lemma mem_cutPiece_left (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι}
    {u v : ℝ} (h : (u, v) ∈ (cutPiece (T j) (cutAt T c j) false).toSetIoc) :
    (u, v) ∈ (T j).toSetIoc ∧ u ≤ c v := by
  obtain ⟨hmem, hle⟩ := mem_cutLeft h
  refine ⟨hmem, ?_⟩
  rcases cutAt_spec hn hs j hmem.2.1 hmem.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he] at hle
  · linarith
  · linarith [hmem.1.1]
  · linarith

/-- The right piece of a tile lies, once slid back, in the tile, to the right of the strip. -/
private lemma mem_cutPiece_right (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι}
    {u v : ℝ} (h : (u, v) ∈ (cutPiece (T j) (cutAt T c j) true).toSetIoc) :
    (u + 1, v) ∈ (T j).toSetIoc ∧ c v < u := by
  obtain ⟨hmem, hlt⟩ := mem_cutRight h
  refine ⟨hmem, ?_⟩
  rcases cutAt_spec hn hs j hmem.2.1 hmem.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he] at hlt
  · linarith [hmem.1.2]
  · linarith
  · linarith

/-- A point of a tile to the left of the strip lies in the left piece of the tile. -/
private lemma mem_cutPiece_left_of_le (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι}
    {u v : ℝ} (h : (u, v) ∈ (T j).toSetIoc) (hc : u ≤ c v) :
    (u, v) ∈ (cutPiece (T j) (cutAt T c j) false).toSetIoc := by
  refine mem_cutLeft_of_le h ?_
  rcases cutAt_spec hn hs j h.2.1 h.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he]
  · linarith [h.1.2]
  · linarith [h.1.1]
  · linarith

/-- A point whose translate lies in a tile to the right of the strip lies in the right piece of
that tile. -/
private lemma mem_cutPiece_right_of_lt (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c)
    {j : ι} {u v : ℝ} (h : (u + 1, v) ∈ (T j).toSetIoc) (hc : c v < u) :
    (u, v) ∈ (cutPiece (T j) (cutAt T c j) true).toSetIoc := by
  refine mem_cutRight_of_lt h ?_
  rcases cutAt_spec hn hs j h.2.1 h.2.2 with ⟨he, hx⟩ | ⟨he, hx⟩ | ⟨he, -⟩ <;> rw [he]
  · linarith
  · linarith [h.1.1]
  · linarith

/-- **Cutting a tiling along a staircase strip tiles the rectangle one unit narrower.** The strip
of width `1` that is deleted is exactly the gap that closes when everything to its right slides
one unit leftwards, so the half-open cells still partition the shrunken rectangle. -/
theorem isTiling_cut (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c)
    (hRx : R.x₀ + 1 < R.x₁) :
    IsTiling (cutRect R hRx.le) fun p : ι × Bool ↦ cutPiece (T p.1) (cutAt T c p.1) p.2 := by
  have hRy := hn.pos_height
  refine isTiling_of_toSetIoc (by simp only [cutRect]; linarith) (by simpa only [cutRect] using hRy)
    (fun p ↦ ?_) (fun p q hpq ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨j, b⟩ := p
    obtain ⟨hκ₀, hκ₁⟩ := cutAt_mem hn hs j
    have hx₀ := hn.tiling.le_tile_x₀ j
    have hx₁ := hn.tiling.tile_x₁_le j
    have hy₀ := hn.tiling.le_tile_y₀ j
    have hy₁ := hn.tiling.tile_y₁_le j
    rintro ⟨u, v⟩ ⟨⟨k₁, k₂⟩, k₃, k₄⟩
    cases b <;> simp only [cutPiece, cutLeft, cutRight, cutRect] at k₁ k₂ k₃ k₄ ⊢
    · exact ⟨⟨(le_min hx₀ hκ₀).trans k₁, k₂.trans ((min_le_right _ _).trans hκ₁)⟩,
        hy₀.trans k₃, k₄.trans hy₁⟩
    · refine ⟨⟨by linarith [le_max_right (T j).x₀ (cutAt T c j + 1)], ?_⟩, hy₀.trans k₃,
        k₄.trans hy₁⟩
      linarith [max_le hx₁ (show cutAt T c j + 1 ≤ R.x₁ by linarith)]
  · obtain ⟨j, b⟩ := p
    obtain ⟨j', b'⟩ := q
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨u, v⟩ hmem hmem'
    cases b <;> cases b'
    · obtain ⟨h, -⟩ := mem_cutPiece_left hn hs hmem
      obtain ⟨h', -⟩ := mem_cutPiece_left hn hs hmem'
      exact hpq (Prod.ext (hn.tiling.eq_of_mem_cell (sx := true) (sy := true) h h') rfl)
    · obtain ⟨-, h⟩ := mem_cutPiece_left hn hs hmem
      obtain ⟨-, h'⟩ := mem_cutPiece_right hn hs hmem'
      linarith
    · obtain ⟨-, h⟩ := mem_cutPiece_right hn hs hmem
      obtain ⟨-, h'⟩ := mem_cutPiece_left hn hs hmem'
      linarith
    · obtain ⟨h, -⟩ := mem_cutPiece_right hn hs hmem
      obtain ⟨h', -⟩ := mem_cutPiece_right hn hs hmem'
      exact hpq (Prod.ext (hn.tiling.eq_of_mem_cell (sx := true) (sy := true) h h') rfl)
  · obtain ⟨u, v⟩ := z
    obtain ⟨⟨hu₀, hu₁⟩, hv₀, hv₁⟩ := hz
    simp only [cutRect] at hu₀ hu₁ hv₀ hv₁
    by_cases hc : u ≤ c v
    · obtain ⟨j, hj, -⟩ := hn.tiling.existsUnique_toSetIoc
        (show (u, v) ∈ R.toSetIoc from ⟨⟨hu₀, by linarith⟩, hv₀, hv₁⟩)
      exact Set.mem_iUnion.mpr ⟨(j, false), mem_cutPiece_left_of_le hn hs hj hc⟩
    · push Not at hc
      obtain ⟨j, hj, -⟩ := hn.tiling.existsUnique_toSetIoc
        (show (u + 1, v) ∈ R.toSetIoc from ⟨⟨by linarith, by linarith⟩, hv₀, hv₁⟩)
      exact Set.mem_iUnion.mpr ⟨(j, true), mem_cutPiece_right_of_lt hn hs hj hc⟩

/-! ### One step of the induction -/

/-- **An H-tile survives the cut in one piece, or not at all.** It is one unit wide, so the strip
either misses it, and it is carried over whole in one of the two pieces, or the strip covers it
exactly and both pieces are empty. -/
private lemma width_cutPiece_of_H (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c) {j : ι}
    (hj : H j) :
    ((cutPiece (T j) (cutAt T c j) false).width = 1 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 0) ∨
      ((cutPiece (T j) (cutAt T c j) false).width = 0 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 1) ∨
      ((cutPiece (T j) (cutAt T c j) false).width = 0 ∧
        (cutPiece (T j) (cutAt T c j) true).width = 0) := by
  have hw : (T j).x₁ = (T j).x₀ + 1 := x₁_eq_of_H hn hj
  rcases cutAt_spec hn hs j (hn.proper j).2 le_rfl with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, halign⟩
  · exact Or.inl (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, min_def, max_def] <;>
      split_ifs <;> linarith)
  · exact Or.inr (Or.inl (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, min_def, max_def] <;>
      split_ifs <;> linarith))
  · obtain ⟨h₀, h₁⟩ := halign hj
    exact Or.inr (Or.inr (by constructor <;>
      simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, h₀, h₁, min_def, max_def] <;>
      split_ifs <;> linarith))

/-- A tile that fills the strip at its own height leaves nothing behind. -/
private lemma width_cutPiece_of_mem_strip (hn : Normalized R T H) {k : ι} (hk : H k)
    (hkc : (T k).x₀ = c (T k).y₁) (b : Bool) : (cutPiece (T k) (cutAt T c k) b).width = 0 := by
  classical
  have hw : (T k).x₁ = (T k).x₀ + 1 := x₁_eq_of_H hn hk
  have he : cutAt T c k = c (T k).y₁ := by
    rw [cutAt, if_neg (by rw [hw, hkc]; linarith), if_neg (by rw [hkc]; linarith)]
  cases b <;>
    simp only [cutPiece, cutLeft, cutRight, Rectangle.width, he, ← hkc, hw, min_def, max_def] <;>
    split_ifs <;> linarith

/-- A piece is nondegenerate exactly when it has positive width. -/
private lemma width_ne_zero_iff {S : Rectangle} : S.x₀ < S.x₁ ↔ S.width ≠ 0 := by
  simp only [Rectangle.width, sub_ne_zero]
  exact ⟨fun h ↦ h.ne', fun h ↦ lt_of_le_of_ne S.hx (Ne.symm h)⟩

/-- **One step of Robinson's induction.** Cutting a normalized tiling along a staircase strip
grown from an H-tile leaves a normalized tiling of a rectangle one unit narrower: heights never
change, so V-tiles stay V-tiles, and an H-tile is either carried over whole or swallowed by the
strip — and the H-tile the strip is grown from is swallowed. -/
theorem exists_normalized_cut (hn : Normalized R T H) (hs : Strip R T H R.y₀ R.y₁ c)
    (hRx : R.x₀ + 1 < R.x₁) {k : ι} (hk : H k) (hkc : (T k).x₀ = c (T k).y₁) :
    ∃ (ι' : Type) (_ : Fintype ι') (T' : ι' → Rectangle) (H' : ι' → Prop),
      Normalized (cutRect R hRx.le) T' H' ∧ Nat.card {p // H' p} < Nat.card {i // H i} := by
  classical
  have hcut : IsTiling (cutRect R hRx.le) fun p : ι × Bool ↦ cutPiece (T p.1) (cutAt T c p.1) p.2 :=
    isTiling_cut hn hs hRx
  refine ⟨{p : ι × Bool // (cutPiece (T p.1) (cutAt T c p.1) p.2).Nondegenerate}, inferInstance,
    properTiles fun p : ι × Bool ↦ cutPiece (T p.1) (cutAt T c p.1) p.2, fun p ↦ H p.1.1,
    ⟨hcut.proper (by simp only [cutRect]; linarith) hn.pos_height, proper_properTiles _, ?_, ?_⟩,
    ?_⟩
  · rintro ⟨⟨j, b⟩, hprop⟩ hj
    have hne := width_ne_zero_iff.mp hprop.1
    rcases width_cutPiece_of_H hn hs hj with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> cases b <;>
      first
        | exact h₀
        | exact h₁
        | exact absurd h₀ hne
        | exact absurd h₁ hne
  · rintro ⟨⟨j, b⟩, hprop⟩ hj
    simpa only [Rectangle.height, properTiles, cutPiece_y₀, cutPiece_y₁] using
      hn.height_one j hj
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_of_notMem
      (fun p ↦ (⟨p.1.1.1, p.2⟩ : {i // H i})) (fun p q hpq ↦ ?_) (b := ⟨k, hk⟩) ?_
    · obtain ⟨⟨⟨j, b⟩, hprop⟩, hH⟩ := p
      obtain ⟨⟨⟨j', b'⟩, hprop'⟩, hH'⟩ := q
      have hjj : j = j' := congrArg Subtype.val hpq
      subst hjj
      have hne := width_ne_zero_iff.mp hprop.1
      have hne' := width_ne_zero_iff.mp hprop'.1
      have hbb : b = b' := by
        rcases width_cutPiece_of_H hn hs hH with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;>
          cases b <;> cases b' <;>
          first
            | rfl
            | exact absurd h₀ hne
            | exact absurd h₁ hne
            | exact absurd h₀ hne'
            | exact absurd h₁ hne'
      subst hbb
      rfl
    · rintro ⟨⟨⟨⟨j, b⟩, hprop⟩, hH⟩, hmem⟩
      have hjk : j = k := congrArg Subtype.val hmem
      subst hjk
      exact absurd (width_cutPiece_of_mem_strip hn hH hkc b) (width_ne_zero_iff.mp hprop.1)

/-! ### Growing the strip upwards from an H-tile -/

/-- The strip of width `1` grown upwards from the H-tile `k` is *blocked* at height `t` when an
H-tile starts there and meets the strip: that is where the staircase steps sideways. -/
def BlockedAt (T : ι → Rectangle) (H : ι → Prop) (k : ι) (t : ℝ) : Prop :=
  ∃ j, H j ∧ (T j).y₀ = t ∧ (T j).x₀ < (T k).x₀ + 1 ∧ (T k).x₀ < (T j).x₁

/-- The strip grown upwards from `k` *stops* `n` units above it when it reaches the top of `R`
there or is blocked there. -/
def StopsAbove (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop) (k : ι) (n : ℕ) : Prop :=
  (T k).y₁ + n = R.y₁ ∨ BlockedAt T H k ((T k).y₁ + n)

/-- The strip grown upwards from the H-tile `k` is *clear* at height `t` when no tile of the
tiling crosses that height inside it — every tile below `t` there ends exactly at `t`, so `t` is a
clean horizontal cut across the strip.

Spelled out: for every abscissa `x` strictly inside the column `((T k).x₀, (T k).x₀ + 1)` of the
strip, the tile whose half-open cell contains `(x, t)` — the tile immediately below and to the
left of that point, of which there is exactly one — has its top edge at `t` rather than reaching
past it. This is the invariant that the strip carries up one unit level at a time: it holds at the
top edge of `k` (`clear_top`), and survives a level as long as no H-tile blocks the strip there
(`clear_succ`). -/
def Clear (T : ι → Rectangle) (k : ι) (t : ℝ) : Prop :=
  ∀ x, (T k).x₀ < x → x < (T k).x₀ + 1 → ∀ j : ι,
    (x, t) ∈ (T j).toSetIoc → (T j).y₁ = t

/-- The strip is clear at the top edge of the H-tile it is grown from: the only tile below that
edge inside the strip is the H-tile itself. -/
private lemma clear_top (hn : Normalized R T H) {k : ι} (hk : H k) : Clear T k (T k).y₁ := by
  intro x hx₀ hx₁ j hmem
  rw [hn.tiling.eq_of_mem_cell (sx := true) (sy := true) hmem
    ⟨⟨hx₀, by rw [x₁_eq_of_H hn hk]; linarith⟩, (hn.proper k).2, le_rfl⟩]

/-- **One level of the strip.** Where the strip is clear and unblocked, the tiles just above are
V-tiles resting on that height, and each spans the whole unit level above it. -/
private lemma exists_level_tile (hn : Normalized R T H) {k : ι} (hk : H k) {t : ℝ}
    (hclear : Clear T k t) (hle : R.y₀ ≤ t) (hlt : t < R.y₁) (hnb : ¬ BlockedAt T H k t) {x : ℝ}
    (hx₀ : (T k).x₀ < x) (hx₁ : x < (T k).x₀ + 1) :
    ∃ j, ¬ H j ∧ (T j).x₀ < x ∧ x ≤ (T j).x₁ ∧ (T j).y₀ = t ∧ (T j).y₁ = t + 1 := by
  have hkx₀ : R.x₀ ≤ (T k).x₀ := hn.tiling.le_tile_x₀ k
  have hkx₁ : (T k).x₁ ≤ R.x₁ := hn.tiling.tile_x₁_le k
  have hkw : (T k).x₁ = (T k).x₀ + 1 := x₁_eq_of_H hn hk
  obtain ⟨j, hj, -⟩ := hn.tiling.existsUnique_cell true false
    (show (x, t) ∈ R.cell true false from ⟨⟨by linarith, by linarith⟩, hle, hlt⟩)
  obtain ⟨⟨hjx₀, hjx₁⟩, hjy₀, hjy₁⟩ := hj
  have hy₀ : (T j).y₀ = t := by
    refine le_antisymm hjy₀ (not_lt.mp fun hcon ↦ ?_)
    have := hclear x hx₀ hx₁ j ⟨⟨hjx₀, hjx₁⟩, hcon, hjy₁.le⟩
    linarith
  have hH : ¬ H j := fun hjH ↦ hnb ⟨j, hjH, hy₀, by linarith, by linarith⟩
  exact ⟨j, hH, hjx₀, hjx₁, hy₀, by rw [y₁_eq_of_not_H hn hH, hy₀]⟩

/-- The strip stays clear one level higher, and stays inside `R`. -/
private lemma clear_succ (hn : Normalized R T H) {k : ι} (hk : H k) {t : ℝ} (hclear : Clear T k t)
    (hle : R.y₀ ≤ t) (hlt : t < R.y₁) (hnb : ¬ BlockedAt T H k t) :
    t + 1 ≤ R.y₁ ∧ Clear T k (t + 1) := by
  refine ⟨?_, fun x hx₀ hx₁ j' hmem ↦ ?_⟩
  · obtain ⟨j, -, -, -, -, hy₁⟩ := exists_level_tile hn hk hclear hle hlt hnb
      (by linarith : (T k).x₀ < (T k).x₀ + 1 / 2) (by linarith)
    rw [← hy₁]
    exact hn.tiling.tile_y₁_le j
  · obtain ⟨j, -, hjx₀, hjx₁, hy₀, hy₁⟩ := exists_level_tile hn hk hclear hle hlt hnb hx₀ hx₁
    rw [hn.tiling.eq_of_mem_cell (sx := true) (sy := true) hmem
      ⟨⟨hjx₀, hjx₁⟩, by rw [hy₀]; linarith, by rw [hy₁]⟩, hy₁]

/-- **The strip runs straight up until it stops.** Below the first stop the strip is clear at
every unit height above the H-tile it is grown from, and stays inside `R`. -/
private lemma level (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∀ n : ℕ, (∀ m : ℕ, m < n → ¬ StopsAbove R T H k m) →
      (T k).y₁ + n ≤ R.y₁ ∧ Clear T k ((T k).y₁ + n) := by
  have hR₀ : R.y₀ ≤ (T k).y₁ :=
    (hn.tiling.le_tile_y₀ k).trans (hn.proper k).2.le
  intro n
  induction n with
  | zero => exact fun _ ↦ ⟨by simpa using hn.tiling.tile_y₁_le k, by simpa using clear_top hn hk⟩
  | succ n ih =>
    intro hstop
    obtain ⟨hle, hclear⟩ := ih fun m hm ↦ hstop m (by lia)
    have hnb : ¬ BlockedAt T H k ((T k).y₁ + n) := fun h ↦ hstop n (by lia) (Or.inr h)
    have hlt : (T k).y₁ + n < R.y₁ :=
      lt_of_le_of_ne hle fun h ↦ hstop n (by lia) (Or.inl h)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨h₁, h₂⟩ := clear_succ hn hk hclear (by linarith) hlt hnb
    exact ⟨by push_cast; linarith, by push_cast [← add_assoc]; exact h₂⟩

/-- **The strip always stops.** It rises by one unit at each level, so it must reach the top of
`R` or be blocked. -/
private lemma exists_stopsAbove (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ n : ℕ, StopsAbove R T H k n ∧ ∀ m : ℕ, m < n → ¬ StopsAbove R T H k m := by
  classical
  have hex : ∃ n : ℕ, StopsAbove R T H k n := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hgt⟩ := exists_nat_gt (R.y₁ - (T k).y₁)
    exact absurd (level hn hk n fun m _ ↦ hcon m).1 (by linarith)
  exact ⟨Nat.find hex, Nat.find_spec hex, fun m hm ↦ Nat.find_min hex hm⟩

/-- **The column of the staircase above an H-tile.** The strip runs from the bottom of the H-tile
up to the height `hi` where it stops. Every tile meeting the strip along the way lies inside the
column, and is a V-tile unless it is the H-tile itself; and at `hi` either the strip has reached
the top of `R` or an H-tile carries it on. -/
theorem exists_column (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ hi : ℝ, (T k).y₁ ≤ hi ∧ hi ≤ R.y₁ ∧
      (∀ (j : ι) (y : ℝ), (T j).y₀ < y → y ≤ (T j).y₁ → (T k).y₀ < y → y ≤ hi →
        (T j).x₁ ≤ (T k).x₀ ∨ (T k).x₀ + 1 ≤ (T j).x₀ ∨ ((T k).y₀ ≤ (T j).y₀ ∧ (T j).y₁ ≤ hi ∧
          (H j → (T j).x₀ = (T k).x₀ ∧ (T j).x₁ = (T k).x₀ + 1))) ∧
      (hi = R.y₁ ∨
        ∃ k', H k' ∧ (T k').y₀ = hi ∧ (T k').x₀ < (T k).x₀ + 1 ∧ (T k).x₀ < (T k').x₁) := by
  obtain ⟨N, hN, hNmin⟩ := exists_stopsAbove hn hk
  obtain ⟨hle, -⟩ := level hn hk N hNmin
  have hkw : (T k).x₁ = (T k).x₀ + 1 := x₁_eq_of_H hn hk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨(T k).y₁ + N, by linarith, hle, fun j y hjy₀ hjy₁ hky₀ hyhi ↦ ?_, ?_⟩
  · by_cases hleft : (T j).x₁ ≤ (T k).x₀
    · exact Or.inl hleft
    by_cases hright : (T k).x₀ + 1 ≤ (T j).x₀
    · exact Or.inr (Or.inl hright)
    push Not at hleft hright
    -- the tile meets the strip, so it lies in the column: take a point of the overlap
    refine Or.inr (Or.inr ?_)
    obtain ⟨x, hxj₀, hxj₁, hxk₀, hxk₁⟩ : ∃ x, (T j).x₀ < x ∧ x ≤ (T j).x₁ ∧ (T k).x₀ < x ∧
        x < (T k).x₀ + 1 := by
      refine ⟨(max (T j).x₀ (T k).x₀ + min (T j).x₁ ((T k).x₀ + 1)) / 2, ?_, ?_, ?_, ?_⟩ <;>
        linarith [le_max_left (T j).x₀ (T k).x₀, le_max_right (T j).x₀ (T k).x₀,
          min_le_left (T j).x₁ ((T k).x₀ + 1), min_le_right (T j).x₁ ((T k).x₀ + 1),
          max_lt (lt_min (hn.proper j).1 hright) (lt_min hleft (by linarith :
            (T k).x₀ < (T k).x₀ + 1))]
    have hmem : (x, y) ∈ (T j).toSetIoc := ⟨⟨hxj₀, hxj₁⟩, hjy₀, hjy₁⟩
    rcases le_or_gt y (T k).y₁ with hy | hy
    · -- inside the H-tile itself
      have hjk : j = k := hn.tiling.eq_of_mem_cell (sx := true) (sy := true) hmem
        ⟨⟨hxk₀, by rw [hkw]; linarith⟩, hky₀, hy⟩
      subst hjk
      exact ⟨le_rfl, by linarith, fun _ ↦ ⟨rfl, hkw⟩⟩
    · -- above it, in one of the unit levels of the run
      obtain ⟨m, hmN, hm₀, hm₁⟩ := exists_index hy hyhi (a := (T k).y₁) (n := N) rfl
      obtain ⟨hlem, hclearm⟩ := level hn hk m fun m' hm' ↦ hNmin m' (by lia)
      have hlt : (T k).y₁ + m < R.y₁ := by
        linarith [hjy₁.trans (hn.tiling.tile_y₁_le j), hyhi.trans hle]
      have hR₀ : R.y₀ ≤ (T k).y₁ + m := by
        linarith [hn.tiling.le_tile_y₀ k, (hn.proper k).2, Nat.cast_nonneg (α := ℝ) m]
      obtain ⟨j₀, hH₀, hj₀x₀, hj₀x₁, hy₀, hy₁⟩ := exists_level_tile hn hk hclearm hR₀ hlt
        (fun h ↦ hNmin m hmN (Or.inr h)) hxk₀ hxk₁
      have hjj : j = j₀ := hn.tiling.eq_of_mem_cell (sx := true) (sy := true) hmem
        ⟨⟨hj₀x₀, hj₀x₁⟩, by rw [hy₀]; exact hm₀, by rw [hy₁]; exact hm₁⟩
      subst hjj
      have hmN' : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
      exact ⟨by rw [hy₀]; linarith [(hn.proper k).2, Nat.cast_nonneg (α := ℝ) m],
        by rw [hy₁]; linarith, fun h ↦ absurd h hH₀⟩
  · exact hN

/-! ### The staircase above an H-tile -/

/-- **Gluing a column below a staircase.** Below the height `m` the strip is the single column at
abscissa `v`, above it the given staircase, whose own first column is at `v'`; the two overlap
horizontally, so the glued strip is again a wall: a tile to the left of the staircase at one
height and to its right at another would have to fit between two overlapping columns. -/
private lemma strip_glue (hn : Normalized R T H) {a m mcap m' v v' : ℝ} {c' : ℝ → ℝ}
    (hup : Strip R T H m R.y₁ c') (ham : a ≤ m) (hv₀ : R.x₀ ≤ v) (hv₁ : v + 1 ≤ R.x₁)
    (hm' : m < m') (hnext : ∀ y, m < y → y ≤ m' → c' y = v')
    (hcap : ∀ y, m < y → y ≤ mcap → c' y = v) (hjun : v < v' + 1) (hjun' : v' < v + 1)
    (hcol : ∀ (j : ι) (y : ℝ), (T j).y₀ < y → y ≤ (T j).y₁ → a < y → y ≤ m →
      (T j).x₁ ≤ v ∨ v + 1 ≤ (T j).x₀ ∨
        (a ≤ (T j).y₀ ∧ (T j).y₁ ≤ mcap ∧ (H j → (T j).x₀ = v ∧ (T j).x₁ = v + 1))) :
    Strip R T H a R.y₁ fun y ↦ if y ≤ m then v else c' y where
  mem y _ hy₁ := by
    by_cases hy : y ≤ m
    · rw [if_pos hy]
      exact ⟨hv₀, hv₁⟩
    · rw [if_neg hy]
      exact hup.mem y (not_le.mp hy) hy₁
  side j y hy₀ hy₁ hjy₀ hjy₁ := by
    by_cases hy : y ≤ m
    · rw [if_pos hy]
      rcases hcol j y hjy₀ hjy₁ hy₀ hy with h | h | ⟨h₀, h₁, h₂⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ⟨h₀, hn.tiling.tile_y₁_le j, fun t _ ht₁ ↦ ?_, h₂⟩)
        by_cases ht : t ≤ m
        · rw [if_pos ht]
        · rw [if_neg ht]
          exact hcap t (not_le.mp ht) (ht₁.trans h₁)
    · rw [if_neg hy]
      rcases hup.side j y (not_le.mp hy) hy₁ hjy₀ hjy₁ with h | h | ⟨h₀, h₁, h₂, h₃⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨ham.trans h₀, h₁,
          fun t ht₀ ht₁ ↦ by rw [if_neg (by linarith : ¬ t ≤ m)]; exact h₂ t ht₀ ht₁, h₃⟩)
  consistent j y y' _ hy₁ _ hy'₁ hjy₀ hjy₁ hjy'₀ hjy'₁ hleft hright := by
    by_cases hy : y ≤ m <;> by_cases hy' : y' ≤ m
    · rw [if_pos hy] at hleft
      rw [if_pos hy'] at hright
      linarith [(T j).hx]
    · rw [if_pos hy] at hleft
      rw [if_neg hy'] at hright
      push Not at hy'
      have ht₀ : m < min y' m' := lt_min hy' hm'
      have ht₁ : min y' m' ≤ (T j).y₁ := (min_le_left _ _).trans hjy'₁
      have ht₂ : (T j).y₀ < min y' m' := by linarith
      have htR : min y' m' ≤ R.y₁ := (min_le_left _ _).trans hy'₁
      rcases hup.side j _ ht₀ htR ht₂ ht₁ with h | h | ⟨h₀, -, -, -⟩
      · exact hup.consistent j _ y' ht₀ htR hy' hy'₁ ht₂ ht₁ hjy'₀ hjy'₁ h hright
      · rw [hnext _ ht₀ (min_le_right _ _)] at h
        linarith [(T j).hx]
      · linarith
    · rw [if_neg hy] at hleft
      rw [if_pos hy'] at hright
      push Not at hy
      have ht₀ : m < min y m' := lt_min hy hm'
      have ht₁ : min y m' ≤ (T j).y₁ := (min_le_left _ _).trans hjy₁
      have ht₂ : (T j).y₀ < min y m' := by linarith
      have htR : min y m' ≤ R.y₁ := (min_le_left _ _).trans hy₁
      rcases hup.side j _ ht₀ htR ht₂ ht₁ with h | h | ⟨h₀, -, -, -⟩
      · rw [hnext _ ht₀ (min_le_right _ _)] at h
        linarith [(T j).hx]
      · exact hup.consistent j y _ hy hy₁ ht₀ htR hjy₀ hjy₁ ht₂ ht₁ hleft h
      · linarith
    · rw [if_neg hy] at hleft
      rw [if_neg hy'] at hright
      push Not at hy hy'
      exact hup.consistent j y y' hy hy₁ hy' hy'₁ hjy₀ hjy₁ hjy'₀ hjy'₁ hleft hright

/-- **The staircase strip above an H-tile.** Starting from the H-tile `k`, the strip runs up its
column and then steps sideways onto the H-tile blocking it, and so on until it reaches the top of
`R`. The walk terminates because each step raises the top edge to a strictly higher one of the
finitely many edge heights of the tiling. -/
private theorem strip_above_aux (hn : Normalized R T H) :
    ∀ n : ℕ, ∀ k : ι, H k →
      ((edgeHeights R T).filter fun a ↦ (T k).y₁ < a ∧ a ≤ R.y₁).card ≤ n →
      ∃ c : ℝ → ℝ, Strip R T H (T k).y₀ R.y₁ c ∧
        ∀ y, (T k).y₀ < y → y ≤ (T k).y₁ → c y = (T k).x₀ := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hcard
    obtain ⟨hi, hhi₀, hhi₁, hcol, hend⟩ := exists_column hn hk
    have hkw : (T k).x₁ = (T k).x₀ + 1 := x₁_eq_of_H hn hk
    have hkx₀ : R.x₀ ≤ (T k).x₀ := hn.tiling.le_tile_x₀ k
    have hkx₁ : (T k).x₀ + 1 ≤ R.x₁ := hkw ▸ hn.tiling.tile_x₁_le k
    rcases hend with htop | ⟨k', hk', hk'y, hk'x₀, hk'x₁⟩
    · -- the column reaches the top of `R`, and the strip is that single column
      refine ⟨fun _ ↦ (T k).x₀, ⟨fun y _ _ ↦ ⟨hkx₀, hkx₁⟩, fun j y hy₀ hy₁ hjy₀ hjy₁ ↦ ?_,
        fun j y y' _ _ _ _ _ _ _ _ hleft hright ↦ by linarith [(T j).hx]⟩, fun y _ _ ↦ rfl⟩
      rcases hcol j y hjy₀ hjy₁ hy₀ (htop ▸ hy₁) with h | h | ⟨h₀, h₁, h₂⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h₀, htop ▸ h₁, fun _ _ _ ↦ rfl, h₂⟩)
    -- the column is blocked, and the staircase steps sideways onto the H-tile `k'`
    have hk'w : (T k').x₁ = (T k').x₀ + 1 := x₁_eq_of_H hn hk'
    have hk'y₁ : hi < (T k').y₁ := hk'y ▸ (hn.proper k').2
    have hlt : (T k).y₁ < (T k').y₁ := lt_of_le_of_lt hhi₀ hk'y₁
    have hdrop : ((edgeHeights R T).filter fun a ↦ (T k').y₁ < a ∧ a ≤ R.y₁).card <
        ((edgeHeights R T).filter fun a ↦ (T k).y₁ < a ∧ a ≤ R.y₁).card :=
      Finset.card_lt_card ⟨fun a ha ↦ by
        obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨h₁, hlt.trans h₂, h₃⟩, fun hcon ↦
        absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
          ⟨y₁_mem_edgeHeights k', hlt, hn.tiling.tile_y₁_le k'⟩))).2.1 (lt_irrefl _)⟩
    obtain ⟨c', hc', hc'k⟩ := ih _ (hdrop.trans_le hcard) k' hk' le_rfl
    rw [hk'y] at hc' hc'k
    exact ⟨_, strip_glue hn hc' ((hn.proper k).2.le.trans hhi₀) hkx₀ hkx₁ hk'y₁ hc'k
      (fun y h₁ h₂ ↦ absurd h₁ (not_lt.mpr h₂)) (by rw [hk'w] at hk'x₁; linarith) hk'x₀ hcol,
      fun y _ hy ↦ if_pos (hy.trans hhi₀)⟩

/-- **The staircase strip above an H-tile.** -/
theorem exists_strip_above (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ c : ℝ → ℝ, Strip R T H (T k).y₀ R.y₁ c ∧
      ∀ y, (T k).y₀ < y → y ≤ (T k).y₁ → c y = (T k).x₀ :=
  strip_above_aux hn _ k hk le_rfl

/-! ### The staircase all the way down to the bottom of `R` -/

/-- Reflecting the plane in the horizontal axis carries a normalized tiling to a normalized one,
with the same tiles designated: widths are unchanged and so are heights. -/
lemma Normalized.reflectY (hn : Normalized R T H) :
    Normalized R.reflectY (fun i ↦ (T i).reflectY) H where
  tiling := hn.tiling.reflectY
  proper := properReflectY hn.proper
  width_one i hi := by simpa using hn.width_one i hi
  height_one i hi := by simpa using hn.height_one i hi

/-- **The column of the staircase below an H-tile**, the mirror image of `exists_column`. It is
read off the reflected tiling; only the half-open convention needs care, and a column is settled
by an argument at any interior height, since its abscissa is the same throughout. -/
theorem exists_column_below (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ lo : ℝ, lo ≤ (T k).y₀ ∧ R.y₀ ≤ lo ∧
      (∀ (j : ι) (y : ℝ), (T j).y₀ < y → y ≤ (T j).y₁ → lo < y → y ≤ (T k).y₁ →
        (T j).x₁ ≤ (T k).x₀ ∨ (T k).x₀ + 1 ≤ (T j).x₀ ∨ (lo ≤ (T j).y₀ ∧ (T j).y₁ ≤ (T k).y₁ ∧
          (H j → (T j).x₀ = (T k).x₀ ∧ (T j).x₁ = (T k).x₀ + 1))) ∧
      (lo = R.y₀ ∨
        ∃ k', H k' ∧ (T k').y₁ = lo ∧ (T k').x₀ < (T k).x₀ + 1 ∧ (T k).x₀ < (T k').x₁) := by
  obtain ⟨hi, h₁, h₂, hcol, hend⟩ := exists_column hn.reflectY hk
  simp only [Rectangle.reflectY] at h₁ h₂ hcol hend
  refine ⟨-hi, by linarith, by linarith, fun j y hjy₀ hjy₁ hlo hhi ↦ ?_, ?_⟩
  · -- the reflected column applies just below `y`, and its conclusion does not depend on the
    -- height at which it is read
    obtain ⟨e, he₀, he₁, he₂⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ y - (T j).y₀ ∧ e ≤ y + hi :=
      ⟨min (y - (T j).y₀) (y + hi), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    rcases hcol j (-(y - e)) (by linarith) (by linarith) (by linarith) (by linarith) with
      h | h | ⟨h₃, h₄, h₅⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith, h₅⟩)
  · rcases hend with h | ⟨k', hk', hy, hx₀, hx₁⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨k', hk', by linarith, hx₀, hx₁⟩

/-- **The staircase can be started at the bottom of `R`.** Walking down along the staircase from
any H-tile reaches an H-tile whose column runs down to the bottom edge of `R`; each step lands on
a strictly lower tile, so the walk stops. -/
theorem exists_column_bottom (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ k₀, H k₀ ∧ ∀ (j : ι) (y : ℝ), (T j).y₀ < y → y ≤ (T j).y₁ → R.y₀ < y → y ≤ (T k₀).y₁ →
      (T j).x₁ ≤ (T k₀).x₀ ∨ (T k₀).x₀ + 1 ≤ (T j).x₀ ∨ (R.y₀ ≤ (T j).y₀ ∧ (T j).y₁ ≤ (T k₀).y₁ ∧
        (H j → (T j).x₀ = (T k₀).x₀ ∧ (T j).x₁ = (T k₀).x₀ + 1)) := by
  classical
  refine walk_down_until (R := R) (T := T) (P := H) (fun s hs hgoal ↦ ?_) _ k hk le_rfl
  obtain ⟨lo, hlo₀, hlo₁, hcol, hend⟩ := exists_column_below hn hs
  rcases hend with rfl | ⟨k', hk', hy, -, -⟩
  · exact absurd hcol hgoal
  · exact ⟨k', hk', lt_of_lt_of_le (hy ▸ (hn.proper k').2) hlo₀⟩

/-- **The staircase strip of a normalized tiling.** Grown upwards from an H-tile whose column
reaches the bottom of `R`, the staircase runs from the bottom edge of `R` to its top edge, and the
H-tile it starts from lies inside it. -/
theorem exists_strip (hn : Normalized R T H) {k : ι} (hk : H k) :
    ∃ (c : ℝ → ℝ) (k₀ : ι), Strip R T H R.y₀ R.y₁ c ∧ H k₀ ∧ (T k₀).x₀ = c (T k₀).y₁ := by
  obtain ⟨k₀, hk₀, hbot⟩ := exists_column_bottom hn hk
  obtain ⟨c₀, hc₀, hc₀k⟩ := exists_strip_above hn hk₀
  have hk₀y : (T k₀).y₀ < (T k₀).y₁ := (hn.proper k₀).2
  have hk₀w : (T k₀).x₁ = (T k₀).x₀ + 1 := x₁_eq_of_H hn hk₀
  refine ⟨_, k₀, strip_glue hn hc₀ (hn.tiling.le_tile_y₀ k₀) (hn.tiling.le_tile_x₀ k₀)
    (hk₀w ▸ hn.tiling.tile_x₁_le k₀) hk₀y hc₀k hc₀k (by linarith) (by linarith)
    (fun j y hjy₀ hjy₁ hy₀ hy ↦ hbot j y hjy₀ hjy₁ hy₀ (hy.trans hk₀y.le)), hk₀, ?_⟩
  rw [if_neg (by linarith : ¬ (T k₀).y₁ ≤ (T k₀).y₀), hc₀k _ hk₀y le_rfl]

/-! ### The induction -/

/-- The induction motive: the integer-rectangle theorem for normalized tilings with at most `n`
H-tiles, the index type quantified away so that cutting the staircase out can shrink it. -/
private def IH (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (R : Rectangle) (T : ι → Rectangle) (H : ι → Prop),
    Nat.card {i // H i} ≤ n → Normalized R T H → R.HasIntegerSide

/-- **A normalized tiling tiles a rectangle with an integer side**, by induction on the number of
H-tiles. With no H-tile every tile has integer height and so does `R`. Otherwise grow the
staircase strip from an H-tile: either `R` is too narrow to hold anything but the strip, and is
one unit wide, or cutting the strip out leaves a normalized tiling of a rectangle one unit
narrower with fewer H-tiles, whose integer side is one of `R`'s. -/
private theorem hasIntegerSide_of_normalized : ∀ n : ℕ, IH n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ R T H hcard hn
    classical
    by_cases hH : ∀ i, ¬ H i
    · exact Or.inr (intHeight_of_forall hn.tiling hn.pos_width fun i ↦
        ⟨1, by simpa using hn.height_one i (hH i)⟩)
    push Not at hH
    obtain ⟨k, hk⟩ := hH
    rcases lt_or_ge (R.x₀ + 1) R.x₁ with hRx | hRx
    · obtain ⟨c, k₀, hs, hk₀, hk₀c⟩ := exists_strip hn hk
      obtain ⟨ι', _, T', H', hn', hlt⟩ := exists_normalized_cut hn hs hRx hk₀ hk₀c
      rcases ih _ (hlt.trans_le hcard) ι' _ T' H' le_rfl hn' with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact Or.inl ⟨m + 1, by
          simp only [Rectangle.width, cutRect] at hm ⊢
          push_cast
          linarith⟩
      · exact Or.inr ⟨m, by simpa only [Rectangle.height, cutRect] using hm⟩
    · -- `R` is only wide enough for the H-tile itself, so it is one unit wide
      refine Or.inl ⟨1, ?_⟩
      have h₀ := hn.tiling.le_tile_x₀ k
      have h₁ := hn.tiling.tile_x₁_le k
      rw [x₁_eq_of_H hn hk] at h₁
      simp only [Rectangle.width, Int.cast_one]
      linarith

/-- **Robinson's proof** of the integer-rectangle tiling theorem, by induction on the number of
H-tiles. Cutting every tile into unit pieces along its integer side normalizes the tiling, and
the induction then runs on normalized tilings. -/
theorem IntegerRectangleTheorem_Staircase : IntegerRectangleTheorem := by
  intro ι _ R T hT hsides
  rcases eq_or_lt_of_le R.hx with hRx | hRx
  · exact Or.inl ⟨0, by simp [Rectangle.width, ← hRx]⟩
  rcases eq_or_lt_of_le R.hy with hRy | hRy
  · exact Or.inr ⟨0, by simp [Rectangle.height, ← hRy]⟩
  exact hasIntegerSide_of_normalized _ _ R (pieceTiles T) (PieceCutsWidth T) le_rfl
    (hT.normalized hRx hRy hsides)

end IntegerRectangle.Staircase
