module

public import DifferentProofs.IntegerRectangle.Cells
public import DifferentProofs.IntegerRectangle.GridRefinement

/-!
# The integer-rectangle theorem by induction on reducible links

Wagon's tenth proof, the variation on Robinson's induction due to Richard Bishop and Wagon. Call a
tile an *H-tile* if it is designated by its integer width and a *V-tile* if it is designated by
its integer height. A *V-link* is a maximal vertical segment of the tiling whose interior is
crossed by no horizontal segment, and an *H-link* is its horizontal counterpart. A link is
*reducible* if it is a V-link with only H-tiles along one of its sides, or an H-link with only
V-tiles along one of its sides. Given a reducible V-link with only H-tiles on its right, let `w`
be the width of the narrowest of them and push the tiles on its left `w` units rightwards: heights
never change, so V-tiles stay V-tiles, and widths change by the integer `w`, so H-tiles stay
H-tiles — while the narrowest tile on the right is squeezed away and the tiling loses a tile.
Induction on the number of tiles then reduces everything to the claim that a reducible link always
exists, and if none did there would be a chain of H-tiles running from the bottom of `R` to its
top and a chain of V-tiles running from its left to its right, and those two chains would have to
cross.

Only one of each symmetric pair is developed here and the rest are read off it. H-links are the
V-links of the transposed tiling (`IsTiling.transpose`), so nothing horizontal is defined
separately; and the right-hand side of a vertical line is the left-hand side of the reflected
tiling (`IsTiling.reflectX`, `Link.reflectX`, `Link.ofReflectX`), so `Link.exists_right` and
`exists_link_left` are corollaries of `Link.exists_left` and `exists_link_right`. This is also why
the four ways a link can be reducible cost a single proof: `step_of_reducible_right` treats a
V-link with only H-tiles on its right, and `step_of_reducible_left`, `step_of_reducible_above`
and `step_of_reducible_below` read it in `T.reflectX`, `T.transpose` and `T.transpose.reflectX`.

Two unrelated senses of "left" meet in those names. `Link.exists_left` is about the tiles abutting
a link *on its left*, whereas `exists_link_left` is about the link carried by the *left edge* of a
given tile.
-/

@[expose] public section

open Set

namespace IntegerRectangle.ReducibleLink

variable {ι : Type} [Fintype ι] {R : Rectangle} {T : ι → Rectangle}

/-- A family of rectangles is *proper* when each of its members has positive width and positive
height. Degenerate tiles are harmless but carry no information, and every tiling can be pruned
down to a proper one (`isTiling_proper`). -/
def Proper (T : ι → Rectangle) : Prop := ∀ i, (T i).x₀ < (T i).x₁ ∧ (T i).y₀ < (T i).y₁

/-- The height `y` is *blocked* on the vertical line `x = c` when that line is not a free stretch
of the tiling there: either a tile crosses the line at height `y`, or a horizontal edge of the
tiling arrives at the line at height `y` from both sides. The unblocked heights are those
interior to a V-link. -/
def Blocked (T : ι → Rectangle) (c y : ℝ) : Prop :=
  (∃ i, (T i).x₀ < c ∧ c < (T i).x₁ ∧ (T i).y₀ ≤ y ∧ y ≤ (T i).y₁) ∨
    ((∃ i, (T i).x₀ < c ∧ c ≤ (T i).x₁ ∧ ((T i).y₀ = y ∨ (T i).y₁ = y)) ∧
      ∃ i, (T i).x₀ ≤ c ∧ c < (T i).x₁ ∧ ((T i).y₀ = y ∨ (T i).y₁ = y))

/-- A **V-link** of a tiling: a stretch `{c} × [lo, hi]` of a vertical line, interior to the tiled
rectangle in the horizontal direction, whose interior heights are unblocked and whose two ends are
blocked or on the boundary of `R`. Wagon's H-links are the V-links of the transposed tiling. -/
structure Link (R : Rectangle) (T : ι → Rectangle) where
  /-- The abscissa of the vertical line carrying the link. -/
  c : ℝ
  /-- The height of the lower end of the link. -/
  lo : ℝ
  /-- The height of the upper end of the link. -/
  hi : ℝ
  /-- The link is to the right of the left edge of `R`. -/
  x₀_lt : R.x₀ < c
  /-- The link is to the left of the right edge of `R`. -/
  lt_x₁ : c < R.x₁
  /-- The link is not a single point. -/
  lo_lt_hi : lo < hi
  /-- The link starts inside `R`. -/
  y₀_le : R.y₀ ≤ lo
  /-- The link ends inside `R`. -/
  le_y₁ : hi ≤ R.y₁
  /-- No interior height of the link is blocked. -/
  free : ∀ y, lo < y → y < hi → ¬ Blocked T c y
  /-- The link is maximal downwards. -/
  bot : lo = R.y₀ ∨ Blocked T c lo
  /-- The link is maximal upwards. -/
  top : hi = R.y₁ ∨ Blocked T c hi

/-- Two tiles whose lower-left cells contain a common point are equal — the form in which
uniqueness of the tile in a quadrant is used below. -/
private lemma eq_of_cell (hT : IsTiling R T) {c t : ℝ} {i j : ι}
    (hi : ((T i).x₀ < c ∧ c ≤ (T i).x₁) ∧ (T i).y₀ < t ∧ t ≤ (T i).y₁)
    (hj : ((T j).x₀ < c ∧ c ≤ (T j).x₁) ∧ (T j).y₀ < t ∧ t ≤ (T j).y₁) : i = j :=
  hT.eq_of_mem_cell (sx := true) (sy := true) (x := c) (y := t) hi hj

/-- A tile whose right edge lies on a vertical line does not cross a blocked height of that line:
whatever blocks the line there — a tile crossing it, or a horizontal edge arriving at it from the
left — would share a point with the tile. -/
private lemma not_blocked_of_cross (hT : IsTiling R T) (hp : Proper T) {c e : ℝ} {i : ι}
    (hx₀ : (T i).x₀ < c) (hx₁ : (T i).x₁ = c) (h₀ : (T i).y₀ < e) (h₁ : e < (T i).y₁) :
    ¬ Blocked T c e := by
  rintro (⟨j, hj₀, hj₁, hj₂, hj₃⟩ | ⟨⟨j, hj₀, hj₁, hj₂⟩, -⟩)
  · have ha₁ : (T i).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_left _ _
    have ha₂ : (T j).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_right _ _
    have hb₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
    have hb₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
    have hab : max (T i).y₀ (T j).y₀ < min (T i).y₁ (T j).y₁ := by
      simp only [max_lt_iff, lt_min_iff]
      exact ⟨⟨h₀.trans h₁, hj₂.trans_lt h₁⟩, h₀.trans_le hj₃, (hp j).2⟩
    have hij := eq_of_cell hT (c := c)
      (t := (max (T i).y₀ (T j).y₀ + min (T i).y₁ (T j).y₁) / 2)
      ⟨⟨hx₀, hx₁.ge⟩, by linarith, by linarith⟩ ⟨⟨hj₀, hj₁.le⟩, by linarith, by linarith⟩
    rw [hij] at hx₁
    linarith
  · have hjy := (hp j).2
    rcases hj₂ with heq | heq
    · have hm₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
      have hm₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
      have hlt : e < min (T i).y₁ (T j).y₁ := lt_min h₁ (heq ▸ hjy)
      have hij := eq_of_cell hT (c := c) (t := (e + min (T i).y₁ (T j).y₁) / 2)
        ⟨⟨hx₀, hx₁.ge⟩, by linarith, by linarith⟩
        ⟨⟨hj₀, hj₁⟩, by rw [heq]; linarith, by linarith⟩
      rw [← hij] at heq
      linarith
    · have hij := eq_of_cell hT (c := c) (t := e) ⟨⟨hx₀, hx₁.ge⟩, h₀, h₁.le⟩
        ⟨⟨hj₀, hj₁⟩, heq ▸ hjy, heq.ge⟩
      rw [← hij] at heq
      linarith

omit [Fintype ι] in
/-- A tile crossing the line of a link whose height range overlaps the link blocks an interior
height of the link, which is impossible. -/
private lemma Link.not_straddle (l : Link R T) {j : ι} (h₀ : (T j).x₀ < l.c) (h₁ : l.c < (T j).x₁)
    (h : max (T j).y₀ l.lo < min (T j).y₁ l.hi) : False := by
  have ha₁ : (T j).y₀ ≤ max (T j).y₀ l.lo := le_max_left _ _
  have ha₂ : l.lo ≤ max (T j).y₀ l.lo := le_max_right _ _
  have hb₁ : min (T j).y₁ l.hi ≤ (T j).y₁ := min_le_left _ _
  have hb₂ : min (T j).y₁ l.hi ≤ l.hi := min_le_right _ _
  exact l.free ((max (T j).y₀ l.lo + min (T j).y₁ l.hi) / 2) (by linarith) (by linarith)
    (Or.inl ⟨j, h₀, h₁, by linarith, by linarith⟩)

/-- **The tile abutting a V-link on the left at a given height.** At every height of the link
there is a tile whose right edge lies on the link, and it sticks out past neither end of the
link: those tiles cut the link into consecutive pieces. -/
theorem Link.exists_left (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) :
    ∃ i, (T i).x₀ < l.c ∧ (T i).x₁ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi ∧
      (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, ⟨⟨hx₀, hx₁⟩, hb, ht⟩, -⟩ := hT.existsUnique_cell true true (x := l.c) (y := y)
    ⟨⟨l.x₀_lt, l.lt_x₁.le⟩, l.y₀_le.trans_lt hy₀, hy₁.trans l.le_y₁⟩
  have hmin : y ≤ min (T i).y₁ l.hi := le_min ht hy₁
  have hxeq : (T i).x₁ = l.c :=
    (hx₁.eq_or_lt.resolve_right fun h ↦
      l.not_straddle hx₀ h (max_lt (hb.trans_le hmin) (hy₀.trans_le hmin))).symm
  have hup : (T i).y₁ ≤ l.hi := by
    refine not_lt.mp fun h ↦ ?_
    obtain heq | hbl := l.top
    · exact absurd (hT.tile_y₁_le i) (by rw [← heq]; exact not_le.mpr h)
    · exact not_blocked_of_cross hT hp hx₀ hxeq (hb.trans_le hy₁) h hbl
  have hdn : l.lo ≤ (T i).y₀ := by
    refine not_lt.mp fun h ↦ ?_
    obtain heq | hbl := l.bot
    · exact absurd (hT.le_tile_y₀ i) (by rw [← heq]; exact not_le.mpr h)
    · exact not_blocked_of_cross hT hp hx₀ hxeq h (hy₀.trans_le ht) hbl
  exact ⟨i, hxeq ▸ (hp i).1, hxeq, hdn, hup, hb, ht⟩

/-! ### The two sides of a link -/

omit [Fintype ι] in
/-- Reflecting the plane in the vertical axis exchanges the two sides of a vertical line, so it
preserves being blocked. -/
lemma blocked_reflectX (T : ι → Rectangle) (c y : ℝ) :
    Blocked (fun i ↦ (T i).reflectX) (-c) y ↔ Blocked T c y := by
  simp only [Blocked, Rectangle.reflectX, neg_lt_neg_iff, neg_le_neg_iff]
  grind

/-- Reflecting the plane in the vertical axis carries a V-link to a V-link. -/
def Link.reflectX (l : Link R T) : Link R.reflectX fun i ↦ (T i).reflectX where
  c := -l.c
  lo := l.lo
  hi := l.hi
  x₀_lt := by simpa [Rectangle.reflectX] using l.lt_x₁
  lt_x₁ := by simpa [Rectangle.reflectX] using l.x₀_lt
  lo_lt_hi := l.lo_lt_hi
  y₀_le := l.y₀_le
  le_y₁ := l.le_y₁
  free y h₁ h₂ := (blocked_reflectX T l.c y).not.mpr (l.free y h₁ h₂)
  bot := l.bot.imp id (blocked_reflectX T l.c l.lo).mpr
  top := l.top.imp id (blocked_reflectX T l.c l.hi).mpr

/-- **The tile abutting a V-link on the right at a given height**, the mirror image of
`Link.exists_left`. -/
theorem Link.exists_right (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) :
    ∃ i, l.c < (T i).x₁ ∧ (T i).x₀ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi ∧
      (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, h₁, h₂, h₃, h₄, h₅, h₆⟩ := Link.exists_left hT.reflectX
    (fun i ↦ ⟨by simpa [Rectangle.reflectX] using (hp i).1, (hp i).2⟩) l.reflectX hy₀ hy₁
  simp only [Rectangle.reflectX, Link.reflectX] at h₁ h₂
  exact ⟨i, by linarith, by linarith, h₃, h₄, h₅, h₆⟩

/-- Tile `i` abuts the link on the left: its right edge lies on the link. -/
def IsLeft (l : Link R T) (i : ι) : Prop := (T i).x₁ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi

/-- Tile `i` abuts the link on the right: its left edge lies on the link. -/
def IsRight (l : Link R T) (i : ι) : Prop := (T i).x₀ = l.c ∧ l.lo ≤ (T i).y₀ ∧ (T i).y₁ ≤ l.hi

omit [Fintype ι] in
lemma not_isLeft_isRight (hp : Proper T) {l : Link R T} {i : ι} (h : IsLeft l i)
    (h' : IsRight l i) : False :=
  lt_irrefl _ (h.1 ▸ h'.1 ▸ (hp i).1)

/-- **The tiles on the left of a link cover it.** -/
theorem exists_isLeft (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) : ∃ i, IsLeft l i ∧ (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, -, h₁, h₂, h₃, h₄, h₅⟩ := l.exists_left hT hp hy₀ hy₁
  exact ⟨i, ⟨h₁, h₂, h₃⟩, h₄, h₅⟩

/-- **The tiles on the right of a link cover it.** -/
theorem exists_isRight (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {y : ℝ}
    (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) : ∃ i, IsRight l i ∧ (T i).y₀ < y ∧ y ≤ (T i).y₁ := by
  obtain ⟨i, -, h₁, h₂, h₃, h₄, h₅⟩ := l.exists_right hT hp hy₀ hy₁
  exact ⟨i, ⟨h₁, h₂, h₃⟩, h₄, h₅⟩

/-- **The tiles on the left of a link meet it in disjoint stretches.** -/
theorem isLeft_unique (hT : IsTiling R T) (hp : Proper T) {l : Link R T} {i j : ι} {y : ℝ}
    (hi : IsLeft l i) (hj : IsLeft l j) (hyi : (T i).y₀ < y ∧ y ≤ (T i).y₁)
    (hyj : (T j).y₀ < y ∧ y ≤ (T j).y₁) : i = j :=
  eq_of_cell hT (c := l.c) ⟨⟨by have := (hp i).1; rw [hi.1] at this; exact this, hi.1.ge⟩, hyi⟩
    ⟨⟨by have := (hp j).1; rw [hj.1] at this; exact this, hj.1.ge⟩, hyj⟩

/-! ### Pushing the tiles on the left of a link rightwards -/

open scoped Classical in
/-- The family obtained from `T` by pushing every tile on the left of the link `w` units
rightwards and paring every tile on its right back by the same amount. -/
noncomputable def push (l : Link R T) (w : ℝ) (hw : 0 ≤ w)
    (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) (i : ι) : Rectangle :=
  if h : IsLeft l i then
    { x₀ := (T i).x₀, x₁ := l.c + w, y₀ := (T i).y₀, y₁ := (T i).y₁
      hx := by
        have h₁ := (T i).hx
        rw [h.1] at h₁
        linarith
      hy := (T i).hy }
  else if h' : IsRight l i then
    { x₀ := l.c + w, x₁ := (T i).x₁, y₀ := (T i).y₀, y₁ := (T i).y₁
      hx := hR i h'
      hy := (T i).hy }
  else T i

variable {l : Link R T} {w : ℝ} {hw : 0 ≤ w} {hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁}

omit [Fintype ι] in
@[simp] lemma push_y₀ (i : ι) : (push l w hw hR i).y₀ = (T i).y₀ := by
  unfold push; split_ifs <;> rfl

omit [Fintype ι] in
@[simp] lemma push_y₁ (i : ι) : (push l w hw hR i).y₁ = (T i).y₁ := by
  unfold push; split_ifs <;> rfl

omit [Fintype ι] in
lemma push_x₀_of_isLeft {i : ι} (h : IsLeft l i) : (push l w hw hR i).x₀ = (T i).x₀ := by
  unfold push; rw [dif_pos h]

omit [Fintype ι] in
lemma push_x₁_of_isLeft {i : ι} (h : IsLeft l i) : (push l w hw hR i).x₁ = l.c + w := by
  unfold push; rw [dif_pos h]

omit [Fintype ι] in
lemma push_x₀_of_isRight (hp : Proper T) {i : ι} (h : IsRight l i) :
    (push l w hw hR i).x₀ = l.c + w := by
  unfold push; rw [dif_neg fun h' ↦ not_isLeft_isRight hp h' h, dif_pos h]

omit [Fintype ι] in
lemma push_x₁_of_isRight (hp : Proper T) {i : ι} (h : IsRight l i) :
    (push l w hw hR i).x₁ = (T i).x₁ := by
  unfold push; rw [dif_neg fun h' ↦ not_isLeft_isRight hp h' h, dif_pos h]

omit [Fintype ι] in
lemma push_of_not {i : ι} (h : ¬ IsLeft l i) (h' : ¬ IsRight l i) : push l w hw hR i = T i := by
  unfold push; rw [dif_neg h, dif_neg h']

private lemma mem_toSetIoc' {S : Rectangle} {x y : ℝ} :
    ((x, y) : ℝ × ℝ) ∈ S.toSetIoc ↔ (S.x₀ < x ∧ x ≤ S.x₁) ∧ S.y₀ < y ∧ y ≤ S.y₁ := Iff.rfl

/-- Since some tile on the right of the link is at least `w` wide, the pushed edge stays inside
`R`. -/
private lemma add_le_x₁ (hT : IsTiling R T) (hp : Proper T)
    (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) : l.c + w ≤ R.x₁ := by
  obtain ⟨k, hk, -, -⟩ := exists_isRight hT hp l l.lo_lt_hi le_rfl
  exact (hR k hk).trans (hT.tile_x₁_le k)

/-- Every point of the strip swept by the push lies in the cell of a tile on the right of the
link. -/
private lemma exists_isRight_of_mem_strip (hT : IsTiling R T) (hp : Proper T)
    (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) {x y : ℝ} (h₁ : l.c < x) (h₂ : x ≤ l.c + w)
    (h₃ : l.lo < y) (h₄ : y ≤ l.hi) :
    ∃ k, IsRight l k ∧ ((x, y) : ℝ × ℝ) ∈ (T k).toSetIoc := by
  obtain ⟨k, hk, hy₀, hy₁⟩ := exists_isRight hT hp l h₃ h₄
  exact ⟨k, hk, ⟨by rw [hk.1]; exact h₁, h₂.trans (hR k hk)⟩, hy₀, hy₁⟩

omit [Fintype ι] in
/-- A pushed cell either stays inside the old cell or reaches into the swept strip. -/
private lemma mem_toSetIoc_or_mem_strip (hp : Proper T) (i : ι) {x y : ℝ}
    (hmem : ((x, y) : ℝ × ℝ) ∈ (push l w hw hR i).toSetIoc) :
    ((x, y) : ℝ × ℝ) ∈ (T i).toSetIoc ∨ ((l.c < x ∧ x ≤ l.c + w) ∧ l.lo < y ∧ y ≤ l.hi) := by
  by_cases hL : IsLeft l i
  · simp only [mem_toSetIoc', push_x₀_of_isLeft hL, push_x₁_of_isLeft hL, push_y₀,
      push_y₁] at hmem
    rcases le_or_gt x l.c with h | h
    · exact Or.inl ⟨⟨hmem.1.1, by rw [hL.1]; exact h⟩, hmem.2⟩
    · exact Or.inr ⟨⟨h, hmem.1.2⟩, hL.2.1.trans_lt hmem.2.1, hmem.2.2.trans hL.2.2⟩
  by_cases hRi : IsRight l i
  · simp only [mem_toSetIoc', push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi, push_y₀,
      push_y₁] at hmem
    exact Or.inl ⟨⟨by rw [hRi.1]; linarith [hmem.1.1], hmem.1.2⟩, hmem.2⟩
  · rw [push_of_not hL hRi] at hmem
    exact Or.inl hmem

/-- Only a tile on the left of the link reaches into the swept strip. -/
private lemma isLeft_of_mem_strip (hT : IsTiling R T) (hp : Proper T) (i : ι) {x y : ℝ}
    (hmem : ((x, y) : ℝ × ℝ) ∈ (push l w hw hR i).toSetIoc) (h₁ : l.c < x) (h₂ : x ≤ l.c + w)
    (h₃ : l.lo < y) (h₄ : y ≤ l.hi) : IsLeft l i := by
  by_cases hL : IsLeft l i
  · exact hL
  by_cases hRi : IsRight l i
  · rw [mem_toSetIoc', push_x₀_of_isRight hp hRi] at hmem
    exact absurd hmem.1.1 (not_lt.mpr h₂)
  · rw [push_of_not hL hRi] at hmem
    obtain ⟨k, hk, hkmem⟩ := exists_isRight_of_mem_strip hT hp hR h₁ h₂ h₃ h₄
    have : i = k := hT.eq_of_mem_cell (sx := true) (sy := true) hmem hkmem
    subst this
    exact absurd hk hRi

/-- A pushed tile stays within the horizontal extent of `R`. -/
private lemma push_mem_Icc (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    R.x₀ ≤ (push l w hw hR i).x₀ ∧ (push l w hw hR i).x₁ ≤ R.x₁ := by
  by_cases hL : IsLeft l i
  · rw [push_x₀_of_isLeft hL, push_x₁_of_isLeft hL]
    exact ⟨hT.le_tile_x₀ i, add_le_x₁ hT hp hR⟩
  by_cases hRi : IsRight l i
  · rw [push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi]
    exact ⟨by have := l.x₀_lt; linarith, hT.tile_x₁_le i⟩
  · rw [push_of_not hL hRi]
    exact ⟨hT.le_tile_x₀ i, hT.tile_x₁_le i⟩

/-- A pushed tile stays inside `R`. -/
private lemma push_toSet_subset (hT : IsTiling R T) (hp : Proper T) (i : ι) :
    (push l w hw hR i).toSet ⊆ R.toSet := by
  rintro ⟨a, b⟩ ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  obtain ⟨hb₁, hb₂⟩ := push_mem_Icc hT hp i
  rw [push_y₀] at h₃
  rw [push_y₁] at h₄
  exact ⟨⟨by linarith, by linarith⟩, by linarith [hT.le_tile_y₀ i], by linarith [hT.tile_y₁_le i]⟩

/-- The pushed cells are still pairwise disjoint: two of them meeting inside the swept strip
belong to tiles on the left of the link at a common height, and two meeting outside it already
met as cells of `T`. -/
private lemma push_pairwiseDisjoint (hT : IsTiling R T) (hp : Proper T) :
    Pairwise (Function.onFun Disjoint fun i ↦ (push l w hw hR i).toSetIoc) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro ⟨x, y⟩ hi hj
  by_cases hs : (l.c < x ∧ x ≤ l.c + w) ∧ l.lo < y ∧ y ≤ l.hi
  · have hLi := isLeft_of_mem_strip hT hp i hi hs.1.1 hs.1.2 hs.2.1 hs.2.2
    have hLj := isLeft_of_mem_strip hT hp j hj hs.1.1 hs.1.2 hs.2.1 hs.2.2
    simp only [mem_toSetIoc', push_y₀, push_y₁] at hi hj
    exact hij (isLeft_unique hT hp hLi hLj hi.2 hj.2)
  · rcases mem_toSetIoc_or_mem_strip hp i hi with hi' | hi'
    · rcases mem_toSetIoc_or_mem_strip hp j hj with hj' | hj'
      · exact hij (hT.eq_of_mem_cell (sx := true) (sy := true) hi' hj')
      · exact hs hj'
    · exact hs hi'

/-- The pushed cells still cover `R`: the strip the tiles on the right vacate is picked up by the
tiles on the left. -/
private lemma subset_iUnion_push (hT : IsTiling R T) (hp : Proper T) :
    R.toSetIoc ⊆ ⋃ i, (push l w hw hR i).toSetIoc := by
  rintro ⟨x, y⟩ hz
  obtain ⟨i, hi, -⟩ := hT.existsUnique_toSetIoc hz
  rw [mem_toSetIoc'] at hi
  by_cases hRi : IsRight l i
  · rcases le_or_gt x (l.c + w) with hx | hx
    · obtain ⟨j, hLj, hj₀, hj₁⟩ := exists_isLeft hT hp l (hRi.2.1.trans_lt hi.2.1)
        (hi.2.2.trans hRi.2.2)
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      simp only [mem_toSetIoc', push_x₀_of_isLeft hLj, push_x₁_of_isLeft hLj, push_y₀, push_y₁]
      refine ⟨⟨?_, hx⟩, hj₀, hj₁⟩
      have h₁ := (hp j).1
      rw [hLj.1] at h₁
      rw [hRi.1] at hi
      linarith [hi.1.1]
    · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [mem_toSetIoc', push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi, push_y₀,
        push_y₁]
      exact ⟨⟨hx, hi.1.2⟩, hi.2⟩
  · by_cases hL : IsLeft l i
    · refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simp only [mem_toSetIoc', push_x₀_of_isLeft hL, push_x₁_of_isLeft hL, push_y₀, push_y₁]
      rw [hL.1] at hi
      exact ⟨⟨hi.1.1, by linarith [hi.1.2]⟩, hi.2⟩
    · exact Set.mem_iUnion.mpr ⟨i, by rw [push_of_not hL hRi, mem_toSetIoc']; exact hi⟩

/-- **Pushing the tiles on the left of a link rightwards again tiles the same rectangle.** The
strip `(c, c + w] × (lo, hi]` that the tiles on the left sweep out is exactly the strip that the
tiles on the right vacate, so the cells still partition `R`. -/
theorem isTiling_push (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁) (hRy : R.y₀ < R.y₁)
    {l : Link R T} {w : ℝ} (hw0 : 0 < w) (hR : ∀ i, IsRight l i → l.c + w ≤ (T i).x₁) :
    IsTiling R (push l w hw0.le hR) :=
  isTiling_of_toSetIoc hRx hRy (push_toSet_subset hT hp) (push_pairwiseDisjoint hT hp)
    (subset_iUnion_push hT hp)

/-! ### Every interior vertical tile edge lies on a link -/

open scoped Classical in
/-- The heights at which a tile, or the tiled rectangle, has a horizontal edge. The ends of a link
are among them. -/
noncomputable def edgeHeights (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.y₀ (insert R.y₁ ((Finset.univ.image fun i ↦ (T i).y₀) ∪
    Finset.univ.image fun i ↦ (T i).y₁))

lemma y₀_mem_edgeHeights (i : ι) : (T i).y₀ ∈ edgeHeights R T := by simp [edgeHeights]

lemma y₁_mem_edgeHeights (i : ι) : (T i).y₁ ∈ edgeHeights R T := by simp [edgeHeights]

/-- A height carrying a horizontal tile edge is an edge height. -/
private lemma mem_edgeHeights_of_eq {j : ι} {y : ℝ} (h : (T j).y₀ = y ∨ (T j).y₁ = y) :
    y ∈ edgeHeights R T :=
  h.elim (· ▸ y₀_mem_edgeHeights j) (· ▸ y₁_mem_edgeHeights j)

/-- The greatest blocked height of the line `x = c` at or below `b`, or else the bottom of `R`:
the lower end of the link through `b`. -/
private lemma exists_lower_end (c : ℝ) {b : ℝ} (hb : R.y₀ ≤ b) :
    ∃ lo, lo ≤ b ∧ R.y₀ ≤ lo ∧ (lo = R.y₀ ∨ Blocked T c lo) ∧
      ∀ a ∈ edgeHeights R T, a ≤ b → Blocked T c a → a ≤ lo := by
  classical
  set S := insert R.y₀ ((edgeHeights R T).filter fun a ↦ a ≤ b ∧ Blocked T c a) with hS
  have hne : S.Nonempty := ⟨R.y₀, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hne, ?_, S.le_max' _ (Finset.mem_insert_self _ _),
    (Finset.mem_insert.mp (S.max'_mem hne)).imp id fun h ↦ (Finset.mem_filter.mp h).2.2,
    fun a h₁ h₂ h₃ ↦ S.le_max' a (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h₁, h₂, h₃⟩))⟩
  exact (Finset.mem_insert.mp (S.max'_mem hne)).elim (·.trans_le hb)
    fun h ↦ (Finset.mem_filter.mp h).2.1

/-- The least blocked height of the line `x = c` at or above `b`, or else the top of `R`: the
upper end of the link through `b`. -/
private lemma exists_upper_end (c : ℝ) {b : ℝ} (hb : b ≤ R.y₁) :
    ∃ hi, b ≤ hi ∧ hi ≤ R.y₁ ∧ (hi = R.y₁ ∨ Blocked T c hi) ∧
      ∀ a ∈ edgeHeights R T, b ≤ a → Blocked T c a → hi ≤ a := by
  classical
  set S := insert R.y₁ ((edgeHeights R T).filter fun a ↦ b ≤ a ∧ Blocked T c a) with hS
  have hne : S.Nonempty := ⟨R.y₁, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hne, ?_, S.min'_le _ (Finset.mem_insert_self _ _),
    (Finset.mem_insert.mp (S.min'_mem hne)).imp id fun h ↦ (Finset.mem_filter.mp h).2.2,
    fun a h₁ h₂ h₃ ↦ S.min'_le a (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h₁, h₂, h₃⟩))⟩
  exact (Finset.mem_insert.mp (S.min'_mem hne)).elim (hb.trans ·.ge)
    fun h ↦ (Finset.mem_filter.mp h).2.1

/-- **The right edge of a tile, when interior to `R`, lies on a V-link straddling it**: the link
starts at or below the tile's bottom and ends at or above its top. Here "right" is the edge of the
tile the link runs along, not the side of the link a tile sits on, as in `Link.exists_right`. -/
theorem exists_link_right (hT : IsTiling R T) (hp : Proper T) {k : ι} (hlt : (T k).x₁ < R.x₁) :
    ∃ l : Link R T, l.c = (T k).x₁ ∧ l.lo ≤ (T k).y₀ ∧ (T k).y₁ ≤ l.hi := by
  classical
  set c := (T k).x₁ with hc
  have hkx : (T k).x₀ < c := (hp k).1
  have hky : (T k).y₀ < (T k).y₁ := (hp k).2
  have hconf : ∀ j : ι, (T j).x₀ < c → c < (T j).x₁ →
      max (T j).y₀ (T k).y₀ < min (T j).y₁ (T k).y₁ → False := by
    intro j h₁ h₂ h₃
    have ha₁ : (T j).y₀ ≤ max (T j).y₀ (T k).y₀ := le_max_left _ _
    have ha₂ : (T k).y₀ ≤ max (T j).y₀ (T k).y₀ := le_max_right _ _
    have hb₁ : min (T j).y₁ (T k).y₁ ≤ (T j).y₁ := min_le_left _ _
    have hb₂ : min (T j).y₁ (T k).y₁ ≤ (T k).y₁ := min_le_right _ _
    have hjk : j = k := hT.eq_of_mem_cell (sx := true) (sy := true) (x := c)
      (y := (max (T j).y₀ (T k).y₀ + min (T j).y₁ (T k).y₁) / 2)
      ⟨⟨h₁, h₂.le⟩, by linarith, by linarith⟩ ⟨⟨hkx, le_rfl⟩, by linarith, by linarith⟩
    rw [hjk] at h₂
    exact absurd h₂ (lt_irrefl _)
  have hfree : ∀ y, (T k).y₀ < y → y < (T k).y₁ → ¬ Blocked T c y :=
    fun y h₁ h₂ ↦ not_blocked_of_cross hT hp hkx hc.symm h₁ h₂
  obtain ⟨lo, hlo_le, hlo_ge, hlo_spec, hlo_max⟩ := exists_lower_end (T := T) c (hT.le_tile_y₀ k)
  obtain ⟨hi, hhi_ge, hhi_le, hhi_spec, hhi_min⟩ := exists_upper_end (T := T) c (hT.tile_y₁_le k)
  refine ⟨⟨c, lo, hi, (hT.le_tile_x₀ k).trans_lt hkx, hlt, by linarith, hlo_ge, hhi_le,
    fun y h₁ h₂ hb ↦ ?_, hlo_spec, hhi_spec⟩, rfl, hlo_le, hhi_ge⟩
  by_cases hA : y ≤ (T k).y₀
  · have hb' := hb
    rcases hb with ⟨j, hj₁, hj₂, hj₃, hj₄⟩ | ⟨⟨j, hj₁, hj₂, hj₃⟩, -⟩
    · by_cases hj : (T j).y₁ ≤ (T k).y₀
      · have := hlo_max _ (y₁_mem_edgeHeights j) hj (Or.inl ⟨j, hj₁, hj₂, (hp j).2.le, le_rfl⟩)
        linarith
      · refine hconf j hj₁ hj₂ ?_
        rw [max_eq_right (by linarith : (T j).y₀ ≤ (T k).y₀)]
        exact lt_min (not_le.mp hj) hky
    · linarith [hlo_max y (mem_edgeHeights_of_eq hj₃) hA hb']
  by_cases hB : (T k).y₁ ≤ y
  · have hb' := hb
    rcases hb with ⟨j, hj₁, hj₂, hj₃, hj₄⟩ | ⟨⟨j, hj₁, hj₂, hj₃⟩, -⟩
    · by_cases hj : (T k).y₁ ≤ (T j).y₀
      · have := hhi_min _ (y₀_mem_edgeHeights j) hj (Or.inl ⟨j, hj₁, hj₂, le_rfl, (hp j).2.le⟩)
        linarith
      · refine hconf j hj₁ hj₂ ?_
        rw [min_eq_right (by linarith : (T k).y₁ ≤ (T j).y₁)]
        exact max_lt (not_le.mp hj) hky
    · linarith [hhi_min y (mem_edgeHeights_of_eq hj₃) hB hb']
  · exact hfree y (not_le.mp hA) (not_le.mp hB) hb

/-! ### Pruning the degenerate tiles, and the two extreme cases -/

/-- **Degenerate tiles may be discarded.** The half-open cell of a degenerate rectangle is empty,
so it contributes nothing to the partition and deleting it leaves a tiling. -/
theorem isTiling_proper (hT : IsTiling R T) (hx : R.x₀ < R.x₁) (hy : R.y₀ < R.y₁) :
    IsTiling R fun i : {i : ι // (T i).x₀ < (T i).x₁ ∧ (T i).y₀ < (T i).y₁} ↦ T i.1 := by
  refine isTiling_of_toSetIoc hx hy (fun i ↦ hT.tile_subset i.1)
    (fun i j hij ↦ hT.pairwiseDisjoint_toSetIoc (Subtype.coe_ne_coe.mpr hij)) fun z hz ↦ ?_
  obtain ⟨i, hi, -⟩ := hT.existsUnique_toSetIoc hz
  exact Set.mem_iUnion.mpr ⟨⟨i, hi.1.1.trans_le hi.1.2, hi.2.1.trans_le hi.2.2⟩, hi⟩

/-- **A tiling all of whose tiles have integer width tiles a rectangle of integer width.** The
fg-area for the fractional part horizontally and the identity vertically vanishes on every tile,
hence on `R`. -/
theorem intWidth_of_forall (hT : IsTiling R T) (hy : R.y₀ < R.y₁)
    (h : ∀ i, ∃ m : ℤ, (T i).width = m) : ∃ m : ℤ, R.width = m := by
  have key := hT.sum_fgArea Int.fract id
  rw [Finset.sum_eq_zero fun i _ ↦ ?_] at key
  · rw [fgArea] at key
    exact Int.fract_eq_fract.mp (by
      have : Int.fract R.x₁ - Int.fract R.x₀ = 0 := by
        rcases mul_eq_zero.mp key.symm with h' | h'
        · exact h'
        · simp only [id] at h'; linarith
      linarith)
  · obtain ⟨m, hm⟩ := h i
    rw [fgArea, Int.fract_eq_fract.mpr ⟨m, by simpa [Rectangle.width] using hm⟩, sub_self,
      zero_mul]

/-- **A tiling all of whose tiles have integer height tiles a rectangle of integer height.** -/
theorem intHeight_of_forall (hT : IsTiling R T) (hx : R.x₀ < R.x₁)
    (h : ∀ i, ∃ m : ℤ, (T i).height = m) : ∃ m : ℤ, R.height = m :=
  intWidth_of_forall hT.transpose hx h

/-! ### Links on the left-hand edge of a tile -/

/-- A V-link of the reflected tiling is a V-link of the original one. -/
def Link.ofReflectX (l : Link R.reflectX fun i ↦ (T i).reflectX) : Link R T where
  c := -l.c
  lo := l.lo
  hi := l.hi
  x₀_lt := by have := l.lt_x₁; simp only [Rectangle.reflectX] at this; linarith
  lt_x₁ := by have := l.x₀_lt; simp only [Rectangle.reflectX] at this; linarith
  lo_lt_hi := l.lo_lt_hi
  y₀_le := l.y₀_le
  le_y₁ := l.le_y₁
  free y h₁ h₂ hb := l.free y h₁ h₂ (by simpa using (blocked_reflectX T (-l.c) y).mpr hb)
  bot := l.bot.imp id fun h ↦ (blocked_reflectX T (-l.c) l.lo).mp (by simpa using h)
  top := l.top.imp id fun h ↦ (blocked_reflectX T (-l.c) l.hi).mp (by simpa using h)

omit [Fintype ι] in
lemma properReflectX (hp : Proper T) : Proper fun i ↦ (T i).reflectX := fun i ↦
  ⟨by simpa [Rectangle.reflectX] using (hp i).1, (hp i).2⟩

/-- **The left edge of a tile, when interior to `R`, lies on a V-link straddling it**, the mirror
image of `exists_link_right` under reflection in the vertical axis. -/
theorem exists_link_left (hT : IsTiling R T) (hp : Proper T) {k : ι} (hgt : R.x₀ < (T k).x₀) :
    ∃ l : Link R T, l.c = (T k).x₀ ∧ l.lo ≤ (T k).y₀ ∧ (T k).y₁ ≤ l.hi := by
  obtain ⟨l, hc, hlo, hhi⟩ := exists_link_right hT.reflectX (properReflectX hp) (k := k)
    (by simpa [Rectangle.reflectX] using hgt)
  simp only [Rectangle.reflectX] at hc hlo hhi
  exact ⟨l.ofReflectX, by change -l.c = (T k).x₀; rw [hc, neg_neg], hlo, hhi⟩

/-! ### Walking along a chain of tiles -/

open scoped Classical in
/-- The abscissae at which a tile, or the tiled rectangle, has a vertical edge. -/
noncomputable def edgeAbscissae (R : Rectangle) (T : ι → Rectangle) : Finset ℝ :=
  insert R.x₀ (insert R.x₁ ((Finset.univ.image fun i ↦ (T i).x₀) ∪
    Finset.univ.image fun i ↦ (T i).x₁))

lemma x₀_mem_edgeAbscissae (i : ι) : (T i).x₀ ∈ edgeAbscissae R T := by simp [edgeAbscissae]

lemma x₁_mem_edgeAbscissae (i : ι) : (T i).x₁ ∈ edgeAbscissae R T := by simp [edgeAbscissae]

/-- **Walking up a stack of tiles.** If from every tile of the family `P` whose top edge is below
`top` one can step to a tile of `P` sitting directly on it, then every height up to `top` above a
tile of `P` is met by a tile of `P`. The walk terminates because each step raises the top edge to
a strictly higher one of the finitely many edge heights. -/
private theorem walk_up {P : ι → Prop} {top : ℝ}
    (hstep : ∀ s, P s → (T s).y₁ < top →
      ∃ s', P s' ∧ (T s').y₀ = (T s).y₁ ∧ (T s).y₁ < (T s').y₁) :
    ∀ n : ℕ, ∀ s, P s → ((edgeHeights R T).filter fun a ↦ (T s).y₁ < a ∧ a ≤ top).card ≤ n →
      ∀ y, (T s).y₀ < y → y ≤ top → ∃ s', P s' ∧ (T s').y₀ < y ∧ y ≤ (T s').y₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard y hy₀ hy₁
    by_cases hcase : y ≤ (T s).y₁
    · exact ⟨s, hs, hy₀, hcase⟩
    push Not at hcase
    obtain ⟨s', hs', hy, hgt⟩ := hstep s hs (hcase.trans_le hy₁)
    by_cases hover : top < (T s').y₁
    · exact ⟨s', hs', by rw [hy]; exact hcase, hy₁.trans hover.le⟩
    push Not at hover
    refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) s' hs'
      le_rfl y (by rw [hy]; exact hcase) hy₁
    · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h₁, hgt.trans h₂, h₃⟩
    · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
        ⟨y₁_mem_edgeHeights s', hgt, hover⟩))).2.1 (lt_irrefl _)

/-- **Walking down a stack of tiles**, the mirror image of `walk_up`. -/
private theorem walk_down {P : ι → Prop} {bot : ℝ}
    (hstep : ∀ s, P s → bot < (T s).y₀ →
      ∃ s', P s' ∧ (T s').y₁ = (T s).y₀ ∧ (T s').y₀ < (T s).y₀) :
    ∀ n : ℕ, ∀ s, P s → ((edgeHeights R T).filter fun a ↦ bot ≤ a ∧ a < (T s).y₀).card ≤ n →
      ∀ y, bot < y → y ≤ (T s).y₁ → ∃ s', P s' ∧ (T s').y₀ < y ∧ y ≤ (T s').y₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard y hy₀ hy₁
    by_cases hcase : (T s).y₀ < y
    · exact ⟨s, hs, hcase, hy₁⟩
    push Not at hcase
    obtain ⟨s', hs', hy, hlt⟩ := hstep s hs (hy₀.trans_le hcase)
    by_cases hunder : (T s').y₀ < bot
    · exact ⟨s', hs', hunder.trans hy₀, by rw [hy]; exact hcase⟩
    push Not at hunder
    refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) s' hs'
      le_rfl y hy₀ (by rw [hy]; exact hcase)
    · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨h₁, h₂, h₃.trans hlt⟩
    · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
        ⟨y₀_mem_edgeHeights s', hunder, hlt⟩))).2.2 (lt_irrefl _)

/-- **Walking rightwards to the right-hand edge.** If from every tile of the family `P` not
reaching the right edge of `R` one can step to a tile of `P` reaching further right, then some
tile of `P` has its right edge on that of `R`. -/
private theorem walk_right (hT : IsTiling R T) {P : ι → Prop}
    (hstep : ∀ i, P i → (T i).x₁ < R.x₁ → ∃ j, P j ∧ (T i).x₁ < (T j).x₁) :
    ∀ n : ℕ, ∀ i, P i → ((edgeAbscissae R T).filter fun a ↦ (T i).x₁ < a ∧ a ≤ R.x₁).card ≤ n →
      ∃ u, P u ∧ (T u).x₁ = R.x₁ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hcard
    rcases (hT.tile_x₁_le i).lt_or_eq with hlt | heq
    · obtain ⟨j, hj, hgt⟩ := hstep i hi hlt
      refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) j hj
        le_rfl
      · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨h₁, hgt.trans h₂, h₃⟩
      · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
          ⟨x₁_mem_edgeAbscissae j, hgt, hT.tile_x₁_le j⟩))).2.1 (lt_irrefl _)
    · exact ⟨i, hi, heq⟩

/-- **Walking leftwards to the left-hand edge**, the mirror image of `walk_right`. -/
private theorem walk_left (hT : IsTiling R T) {P : ι → Prop}
    (hstep : ∀ i, P i → R.x₀ < (T i).x₀ → ∃ j, P j ∧ (T j).x₀ < (T i).x₀) :
    ∀ n : ℕ, ∀ i, P i → ((edgeAbscissae R T).filter fun a ↦ R.x₀ ≤ a ∧ a < (T i).x₀).card ≤ n →
      ∃ u, P u ∧ (T u).x₀ = R.x₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hcard
    rcases (hT.le_tile_x₀ i).lt_or_eq with hlt | heq
    · obtain ⟨j, hj, hlt'⟩ := hstep i hi hlt
      refine ih _ (lt_of_lt_of_le (Finset.card_lt_card ⟨fun a ha ↦ ?_, fun hcon ↦ ?_⟩) hcard) j hj
        le_rfl
      · obtain ⟨h₁, h₂, h₃⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨h₁, h₂, h₃.trans hlt'⟩
      · exact absurd (Finset.mem_filter.mp (hcon (Finset.mem_filter.mpr
          ⟨x₀_mem_edgeAbscissae j, hT.le_tile_x₀ j, hlt'⟩))).2.2 (lt_irrefl _)
    · exact ⟨i, hi, heq.symm⟩

/-! ### The crossing argument -/

omit [Fintype ι] in
lemma properTranspose (hp : Proper T) : Proper fun i ↦ (T i).transpose :=
  fun i ↦ ⟨(hp i).2, (hp i).1⟩

/-- A finite set of reals leaves a gap above any point. -/
private lemma exists_gap_above (s : Finset ℝ) (e : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, e < a → e + δ ≤ a := by
  classical
  rcases (s.filter fun a ↦ e < a).eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun a ha hlt ↦ absurd (Finset.mem_filter.mpr ⟨ha, hlt⟩) (by simp [h])⟩
  · refine ⟨(s.filter fun a ↦ e < a).min' h - e, ?_, fun a ha hlt ↦ ?_⟩
    · have := (Finset.mem_filter.mp ((s.filter fun a ↦ e < a).min'_mem h)).2
      linarith
    · have := (s.filter fun a ↦ e < a).min'_le a (Finset.mem_filter.mpr ⟨ha, hlt⟩)
      linarith

/-- **A V-link blocks every transverse link it meets.** At a height interior to a V-link there is
a vertical edge of the tiling on the link's line both just below and just above, so the line
blocks the H-link at that height — which is exactly why the two chains of Wagon's argument cannot
cross. -/
theorem blocked_transpose (hT : IsTiling R T) (hp : Proper T) (l : Link R T) {e : ℝ}
    (h₁ : l.lo < e) (h₂ : e < l.hi) : Blocked (fun i ↦ (T i).transpose) e l.c := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_above (edgeHeights R T) e
  obtain ⟨P, -, hP₁, -, -, hP₂, hP₃⟩ := l.exists_left hT hp h₁ h₂.le
  have hmin₁ : min δ (l.hi - e) ≤ δ := min_le_left _ _
  have hmin₂ : min δ (l.hi - e) ≤ l.hi - e := min_le_right _ _
  have hd : 0 < min δ (l.hi - e) := lt_min hδ (by linarith)
  obtain ⟨Q, -, hQ₁, -, -, hQ₂, hQ₃⟩ := l.exists_left hT hp (y := e + min δ (l.hi - e))
    (by linarith) (by linarith)
  have hQ₀ : (T Q).y₀ ≤ e := by
    by_contra hcon
    have := hgap _ (y₀_mem_edgeHeights Q) (not_le.mp hcon)
    linarith
  have hQ₄ : e < (T Q).y₁ := by linarith
  exact Or.inr ⟨⟨P, hP₂, hP₃, Or.inr hP₁⟩, Q, hQ₀, hQ₄, Or.inr hQ₁⟩

variable {H : ι → Prop}

/-- One step upwards along the chain of H-tiles on the left of a V-link. -/
private theorem step_up_left (hT : IsTiling R T) (hp : Proper T)
    (hC : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsRight l' i ∧ H i)
    (l : Link R T) {s : ι} (hleft : (T s).x₁ ≤ l.c) (hlo : l.lo < (T s).y₁)
    (hhi : (T s).y₁ < l.hi) :
    ∃ s', H s' ∧ (T s').x₁ ≤ l.c ∧ (T s').y₀ = (T s).y₁ ∧ (T s).y₁ < (T s').y₁ := by
  obtain ⟨l', hc, hlo', hhi'⟩ := exists_link_right hT.transpose (properTranspose hp) (k := s)
    (show ((T s).transpose).x₁ < R.transpose.x₁ from hhi.trans_le l.le_y₁)
  obtain ⟨s', hR', hH'⟩ := hC l'
  have hy₀ : (T s').y₀ = (T s).y₁ := hR'.1.trans hc
  have hhile : l'.hi ≤ l.c := by
    refine not_lt.mp fun hcon ↦ l'.free l.c (lt_of_le_of_lt hlo' ((hp s).1.trans_le hleft)) hcon ?_
    rw [hc]
    exact blocked_transpose hT hp l hlo hhi
  exact ⟨s', hH', hR'.2.2.trans hhile, hy₀, hy₀ ▸ (hp s').2⟩

/-- One step downwards along the chain of H-tiles on the left of a V-link. -/
private theorem step_down_left (hT : IsTiling R T) (hp : Proper T)
    (hD : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsLeft l' i ∧ H i)
    (l : Link R T) {s : ι} (hleft : (T s).x₁ ≤ l.c) (hlo : l.lo < (T s).y₀)
    (hhi : (T s).y₀ < l.hi) :
    ∃ s', H s' ∧ (T s').x₁ ≤ l.c ∧ (T s').y₁ = (T s).y₀ ∧ (T s').y₀ < (T s).y₀ := by
  obtain ⟨l', hc, hlo', hhi'⟩ := exists_link_left hT.transpose (properTranspose hp) (k := s)
    (show R.transpose.x₀ < ((T s).transpose).x₀ from l.y₀_le.trans_lt hlo)
  obtain ⟨s', hL', hH'⟩ := hD l'
  have hy₁ : (T s').y₁ = (T s).y₀ := hL'.1.trans hc
  have hhile : l'.hi ≤ l.c := by
    refine not_lt.mp fun hcon ↦ l'.free l.c (lt_of_le_of_lt hlo' ((hp s).1.trans_le hleft)) hcon ?_
    rw [hc]
    exact blocked_transpose hT hp l hlo hhi
  exact ⟨s', hH', hL'.2.2.trans hhile, hy₁, hy₁ ▸ (hp s').2⟩

/-- Two tiles that overlap in height and are distinct lie one strictly to the left of the
other. -/
private lemma dichotomy (hT : IsTiling R T) (hp : Proper T) {i j : ι} (hij : i ≠ j)
    (h : max (T i).y₀ (T j).y₀ < min (T i).y₁ (T j).y₁) :
    (T i).x₁ ≤ (T j).x₀ ∨ (T j).x₁ ≤ (T i).x₀ := by
  by_contra hcon
  push Not at hcon
  have ha₁ : (T i).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_left _ _
  have ha₂ : (T j).y₀ ≤ max (T i).y₀ (T j).y₀ := le_max_right _ _
  have hb₁ : min (T i).y₁ (T j).y₁ ≤ (T i).y₁ := min_le_left _ _
  have hb₂ : min (T i).y₁ (T j).y₁ ≤ (T j).y₁ := min_le_right _ _
  have hc₁ : min (T i).x₁ (T j).x₁ ≤ (T i).x₁ := min_le_left _ _
  have hc₂ : min (T i).x₁ (T j).x₁ ≤ (T j).x₁ := min_le_right _ _
  exact hij (hT.eq_of_mem_cell (sx := true) (sy := true)
    (x := min (T i).x₁ (T j).x₁) (y := min (T i).y₁ (T j).y₁)
    ⟨⟨lt_min (hp i).1 hcon.2, hc₁⟩, by linarith, hb₁⟩
    ⟨⟨lt_min hcon.1 (hp j).1, hc₂⟩, by linarith, hb₂⟩)

/-- One step upwards along a chain of H-tiles, across an H-link. -/
private theorem step_up_plain (hT : IsTiling R T) (hp : Proper T)
    (hC : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsRight l' i ∧ H i) {s : ι}
    (hlt : (T s).y₁ < R.y₁) : ∃ s', H s' ∧ (T s').y₀ = (T s).y₁ ∧ (T s).y₁ < (T s').y₁ := by
  obtain ⟨l', hc, -, -⟩ := exists_link_right hT.transpose (properTranspose hp) (k := s)
    (show ((T s).transpose).x₁ < R.transpose.x₁ from hlt)
  obtain ⟨s', hR', hH'⟩ := hC l'
  have hy : (T s').y₀ = (T s).y₁ := hR'.1.trans hc
  exact ⟨s', hH', hy, hy ▸ (hp s').2⟩

/-- One step downwards along a chain of H-tiles, across an H-link. -/
private theorem step_down_plain (hT : IsTiling R T) (hp : Proper T)
    (hD : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsLeft l' i ∧ H i) {s : ι}
    (hlt : R.y₀ < (T s).y₀) : ∃ s', H s' ∧ (T s').y₁ = (T s).y₀ ∧ (T s').y₀ < (T s).y₀ := by
  obtain ⟨l', hc, -, -⟩ := exists_link_left hT.transpose (properTranspose hp) (k := s)
    (show R.transpose.x₀ < ((T s).transpose).x₀ from hlt)
  obtain ⟨s', hL', hH'⟩ := hD l'
  have hy : (T s').y₁ = (T s).y₀ := hL'.1.trans hc
  exact ⟨s', hH', hy, hy ▸ (hp s').2⟩

/-- If no H-link is reducible, the H-tiles reach every height of the tiled rectangle. -/
private theorem exists_H_of_height (hT : IsTiling R T) (hp : Proper T)
    (hC : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsRight l' i ∧ H i)
    (hD : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsLeft l' i ∧ H i)
    {a : ι} (ha : H a) : ∀ y, R.y₀ < y → y ≤ R.y₁ → ∃ s, H s ∧ (T s).y₀ < y ∧ y ≤ (T s).y₁ := by
  intro y hy₀ hy₁
  rcases lt_or_ge (T a).y₀ y with h | h
  · exact walk_up (R := R) (fun _ hs h' ↦ step_up_plain hT hp hC h') _ a ha le_rfl y h hy₁
  · exact walk_down (R := R) (fun _ hs h' ↦ step_down_plain hT hp hD h') _ a ha le_rfl y hy₀
      (h.trans (T a).hy)

/-- The invariant carried rightwards along the V-tiles in Wagon's crossing argument: `i` is a
V-tile, and every H-tile overlapping it in height lies to its right. -/
private def RightOfAll (T : ι → Rectangle) (H : ι → Prop) (i : ι) : Prop :=
  ¬ H i ∧ ∀ s, H s → max (T i).y₀ (T s).y₀ < min (T i).y₁ (T s).y₁ → (T i).x₁ ≤ (T s).x₀

/-- If no V-link is reducible on its left, then to the left of any tile whose left edge is
interior to `R` there is a V-tile reaching further left. -/
private theorem exists_lt_x₀ (hT : IsTiling R T) (hp : Proper T)
    (hB : ∀ l : Link R T, ∃ i, IsLeft l i ∧ ¬ H i) {i : ι} (hlt : R.x₀ < (T i).x₀) :
    ∃ j, ¬ H j ∧ (T j).x₀ < (T i).x₀ := by
  obtain ⟨l, hc, -, -⟩ := exists_link_left hT hp hlt
  obtain ⟨j, hLj, hHj⟩ := hB l
  have h₁ : (T j).x₁ = (T i).x₀ := hLj.1.trans hc
  have h₂ := (hp j).1
  exact ⟨j, hHj, by linarith⟩

/-- **The H-tiles on the left of a V-link cover its heights.** Starting from one of them, walk up
and down along H-links: each step stays on the left of the V-link, because the V-link blocks every
H-link it meets and the tiles bordering an H-link do not reach past its ends. -/
private theorem exists_isH_left (hT : IsTiling R T) (hp : Proper T)
    (hC : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsRight l' i ∧ H i)
    (hD : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsLeft l' i ∧ H i) (l : Link R T)
    {s : ι} (hs : H s) (hsx : (T s).x₁ ≤ l.c) (hs₁ : l.lo < (T s).y₁) (hs₀ : (T s).y₀ < l.hi)
    {y : ℝ} (hy₀ : l.lo < y) (hy₁ : y ≤ l.hi) :
    ∃ t, H t ∧ (T t).x₁ ≤ l.c ∧ (T t).y₀ < y ∧ y ≤ (T t).y₁ := by
  have hup : ∀ t, (H t ∧ (T t).x₁ ≤ l.c ∧ l.lo < (T t).y₁ ∧ (T t).y₀ < l.hi) → (T t).y₁ < l.hi →
      ∃ t', (H t' ∧ (T t').x₁ ≤ l.c ∧ l.lo < (T t').y₁ ∧ (T t').y₀ < l.hi) ∧
        (T t').y₀ = (T t).y₁ ∧ (T t).y₁ < (T t').y₁ := by
    intro t ht hlt
    obtain ⟨t', hH', hx', hy', hgt'⟩ := step_up_left hT hp hC l ht.2.1 ht.2.2.1 hlt
    have := ht.2.2.1
    exact ⟨t', ⟨hH', hx', by linarith, by rw [hy']; exact hlt⟩, hy', hgt'⟩
  have hdown : ∀ t, (H t ∧ (T t).x₁ ≤ l.c ∧ l.lo < (T t).y₁ ∧ (T t).y₀ < l.hi) → l.lo < (T t).y₀ →
      ∃ t', (H t' ∧ (T t').x₁ ≤ l.c ∧ l.lo < (T t').y₁ ∧ (T t').y₀ < l.hi) ∧
        (T t').y₁ = (T t).y₀ ∧ (T t').y₀ < (T t).y₀ := by
    intro t ht hlt
    obtain ⟨t', hH', hx', hy', hlt'⟩ := step_down_left hT hp hD l ht.2.1 hlt ht.2.2.2
    have := ht.2.2.2
    exact ⟨t', ⟨hH', hx', by rw [hy']; exact hlt, by linarith⟩, hy', hlt'⟩
  rcases lt_or_ge (T s).y₀ y with hcase | hcase
  · obtain ⟨t, ht, h₀, h₁⟩ := walk_up (R := R) hup _ s ⟨hs, hsx, hs₁, hs₀⟩ le_rfl y hcase hy₁
    exact ⟨t, ht.1, ht.2.1, h₀, h₁⟩
  · obtain ⟨t, ht, h₀, h₁⟩ := walk_down (R := R) hdown _ s ⟨hs, hsx, hs₁, hs₀⟩ le_rfl y hy₀
      (hcase.trans (T s).hy)
    exact ⟨t, ht.1, ht.2.1, h₀, h₁⟩

/-- **The invariant survives a step rightwards.** An H-tile lying on the left of the V-link just
crossed can be walked to the height of the previous V-tile, staying on the left throughout, which
the invariant for that tile forbids. -/
private theorem rightOfAll_step (hT : IsTiling R T) (hp : Proper T)
    (hA : ∀ l : Link R T, ∃ i, IsRight l i ∧ ¬ H i)
    (hC : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsRight l' i ∧ H i)
    (hD : ∀ l' : Link R.transpose fun i ↦ (T i).transpose, ∃ i, IsLeft l' i ∧ H i) {i : ι}
    (hi : RightOfAll T H i) (hlt : (T i).x₁ < R.x₁) :
    ∃ j, RightOfAll T H j ∧ (T i).x₁ < (T j).x₁ := by
  obtain ⟨l, hc, hlo, hhi⟩ := exists_link_right hT hp hlt
  obtain ⟨j, hRj, hHj⟩ := hA l
  have hjx : (T j).x₀ = (T i).x₁ := hRj.1.trans hc
  refine ⟨j, ⟨hHj, fun s hs hov ↦ ?_⟩, by have := (hp j).1; linarith⟩
  rcases dichotomy hT hp (fun h ↦ hHj (by rw [h]; exact hs)) hov with h | h
  · exact h
  exfalso
  rw [hRj.1] at h
  have hiy := (hp i).2
  obtain ⟨t, ht, htx, h₀, h₁⟩ := exists_isH_left hT hp hC hD l hs h
    (hRj.2.1.trans_lt (((le_max_left _ _).trans_lt hov).trans_le (min_le_right _ _)))
    ((((le_max_right _ _).trans_lt hov).trans_le (min_le_left _ _)).trans_le hRj.2.2)
    (y := ((T i).y₀ + (T i).y₁) / 2) (by linarith) (by linarith)
  have h₂ := hi.2 t ht ((max_lt (by linarith) h₀).trans_le (le_min (by linarith) h₁))
  have h₃ := (hp t).1
  linarith

/-- **Wagon's crossing argument: some link is reducible.** In a tiling with a tile satisfying `H`
and a tile not satisfying it, some V-link has only `H`-tiles along one of its sides, or some
H-link — a V-link of the transposed tiling — has only non-`H`-tiles along one of its sides. For
suppose not: every V-link has a non-`H`-tile on each side and every H-link an `H`-tile below and
above. Walking along links, the `H`-tiles then reach every height of `R`, and the non-`H`-tiles
reach from the left edge to the right one; the invariant `RightOfAll` holds at the left edge and
survives every step rightwards, which is absurd once the right edge of `R` is reached. -/
theorem exists_reducible (hT : IsTiling R T) (hp : Proper T) {a b : ι} (ha : H a) (hb : ¬ H b) :
    (∃ l : Link R T, ∀ i, IsRight l i → H i) ∨ (∃ l : Link R T, ∀ i, IsLeft l i → H i) ∨
      (∃ l : Link R.transpose fun i ↦ (T i).transpose, ∀ i, IsRight l i → ¬ H i) ∨
      ∃ l : Link R.transpose fun i ↦ (T i).transpose, ∀ i, IsLeft l i → ¬ H i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB, hC, hD⟩ := hcon
  obtain ⟨b₀, hb₀, hb₀x⟩ :=
    walk_left hT (fun _ _ hlt ↦ exists_lt_x₀ hT hp hB hlt) _ b hb le_rfl
  obtain ⟨u, hQu, hux⟩ := walk_right hT (fun i hi hlt ↦ rightOfAll_step hT hp hA hC hD hi hlt) _ b₀
    ⟨hb₀, fun s hs hov ↦ by
      rcases dichotomy hT hp (fun h ↦ hb₀ (by rw [h]; exact hs)) hov with h | h
      · exact h
      · exfalso
        have h₁ := hT.le_tile_x₀ s
        have h₂ := (hp s).1
        rw [hb₀x] at h
        linarith⟩ le_rfl
  have huy := (hp u).2
  obtain ⟨s, hs, hs₀, hs₁⟩ := exists_H_of_height hT hp hC hD ha (((T u).y₀ + (T u).y₁) / 2)
    (by have := hT.le_tile_y₀ u; linarith) (by have := hT.tile_y₁_le u; linarith)
  have h₁ := hQu.2 s hs ((max_lt (by linarith) hs₀).trans_le (le_min (by linarith) hs₁))
  have h₂ := hT.tile_x₁_le s
  have h₃ := (hp s).1
  rw [hux] at h₁
  linarith

/-! ### The induction -/

@[simp] lemma reflectX_width (S : Rectangle) : S.reflectX.width = S.width := by
  simp only [Rectangle.width, Rectangle.reflectX]
  ring

@[simp] lemma reflectX_height (S : Rectangle) : S.reflectX.height = S.height := rfl

@[simp] lemma transpose_width (S : Rectangle) : S.transpose.width = S.height := rfl

@[simp] lemma transpose_height (S : Rectangle) : S.transpose.height = S.width := rfl

lemma hasIntegerSide_reflectX {S : Rectangle} :
    S.reflectX.HasIntegerSide ↔ S.HasIntegerSide := by simp [Rectangle.HasIntegerSide]

lemma hasIntegerSide_transpose {S : Rectangle} :
    S.transpose.HasIntegerSide ↔ S.HasIntegerSide := by
  simp [Rectangle.HasIntegerSide, or_comm]

omit [Fintype ι] in
lemma isRight_reflectX {l : Link R T} {i : ι} : IsRight l.reflectX i ↔ IsLeft l i := by
  simp only [IsLeft, IsRight, Link.reflectX, Rectangle.reflectX, neg_inj]

omit [Fintype ι] in
/-- Pushing preserves having an integer side: heights never change, and widths change by the
integer `w`, so V-tiles stay V-tiles and H-tiles stay H-tiles. -/
private lemma hasIntegerSide_push (hp : Proper T) (hsides : ∀ i, (T i).HasIntegerSide)
    (hred : ∀ i, IsRight l i → ∃ m : ℤ, (T i).width = m) {wm : ℤ} (hwm : w = wm) (i : ι) :
    (push l w hw hR i).HasIntegerSide := by
  have hy : (push l w hw hR i).height = (T i).height := by
    simp only [Rectangle.height, push_y₀, push_y₁]
  by_cases hL : IsLeft l i
  · have hx : (push l w hw hR i).width = (T i).width + w := by
      simp only [Rectangle.width, push_x₀_of_isLeft hL, push_x₁_of_isLeft hL, ← hL.1]
      ring
    rcases hsides i with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact Or.inl ⟨m + wm, by rw [hx, hm, hwm]; push_cast; ring⟩
    · exact Or.inr ⟨m, by rw [hy, hm]⟩
  by_cases hRi : IsRight l i
  · have hx : (push l w hw hR i).width = (T i).width - w := by
      simp only [Rectangle.width, push_x₀_of_isRight hp hRi, push_x₁_of_isRight hp hRi, ← hRi.1]
      ring
    obtain ⟨m, hm⟩ := hred i hRi
    exact Or.inl ⟨m - wm, by rw [hx, hm, hwm]; push_cast; ring⟩
  · rw [push_of_not hL hRi]
    exact hsides i

/-- The induction motive: the integer-rectangle theorem for tilings by at most `n` tiles, the
index type quantified away so that discarding a tile can shrink it. -/
private def IH (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (R : Rectangle) (T : ι → Rectangle),
    Fintype.card ι ≤ n → IsTiling R T → (∀ i, (T i).HasIntegerSide) → R.HasIntegerSide

/-- **One step of the induction.** A tiling with a V-link all of whose tiles on the right have
integer width has an integer side, provided every tiling with fewer tiles does: push the tiles on
the left of the link rightwards by the width `w` of the narrowest tile on its right. Heights never
change and widths change by the integer `w`, so every tile keeps an integer side, while the
narrowest tile on the right is squeezed to nothing — discarding it, the new tiling has fewer
tiles and the induction hypothesis applies. -/
private theorem step_of_reducible_right {n : ℕ} (ih : ∀ m, m < n → IH m)
    (hcard : Fintype.card ι ≤ n) (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁)
    (hRy : R.y₀ < R.y₁) (hsides : ∀ i, (T i).HasIntegerSide) (l : Link R T)
    (hred : ∀ i, IsRight l i → ∃ m : ℤ, (T i).width = m) : R.HasIntegerSide := by
  classical
  obtain ⟨k, hk, -, -⟩ := exists_isRight hT hp l l.lo_lt_hi le_rfl
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i ↦ IsRight l i)
    (fun i ↦ (T i).width) ⟨k, by simpa using hk⟩
  have hi₀R : IsRight l i₀ := by simpa using hi₀
  have hw0 : 0 < (T i₀).width := sub_pos.mpr (hp i₀).1
  have hR : ∀ i, IsRight l i → l.c + (T i₀).width ≤ (T i).x₁ := by
    intro i hi
    have h₁ := hmin i (by simpa using hi)
    have h₂ : (T i).x₁ - (T i).x₀ = (T i).width := rfl
    rw [hi.1] at h₂
    linarith
  obtain ⟨wm, hwm⟩ := hred i₀ hi₀R
  set T' := push l (T i₀).width hw0.le hR with hT'def
  have hT' : IsTiling R T' := isTiling_push hT hp hRx hRy hw0 hR
  have hdeg : ¬((T' i₀).x₀ < (T' i₀).x₁ ∧ (T' i₀).y₀ < (T' i₀).y₁) := by
    rw [hT'def, push_x₀_of_isRight hp hi₀R, push_x₁_of_isRight hp hi₀R]
    have : (T i₀).x₁ - (T i₀).x₀ = (T i₀).width := rfl
    rw [hi₀R.1] at this
    rintro ⟨h, -⟩
    linarith
  have hlt := Fintype.card_subtype_lt
    (p := fun i ↦ (T' i).x₀ < (T' i).x₁ ∧ (T' i).y₀ < (T' i).y₁) hdeg
  refine ih _ (hlt.trans_le hcard) _ R _ le_rfl
    (isTiling_proper hT' hRx hRy) fun i ↦ hasIntegerSide_push hp hsides hred hwm i.1

/-- `step_of_reducible_right` for a V-link with only H-tiles on its left, transported along the
reflection in the vertical axis. -/
private theorem step_of_reducible_left {n : ℕ} (ih : ∀ m, m < n → IH m)
    (hcard : Fintype.card ι ≤ n) (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁)
    (hRy : R.y₀ < R.y₁) (hsides : ∀ i, (T i).HasIntegerSide) (l : Link R T)
    (hred : ∀ i, IsLeft l i → ∃ m : ℤ, (T i).width = m) : R.HasIntegerSide := by
  refine hasIntegerSide_reflectX.mp (step_of_reducible_right ih hcard hT.reflectX
    (properReflectX hp) ?_ hRy (fun i ↦ hasIntegerSide_reflectX.mpr (hsides i)) l.reflectX
    fun i hi ↦ ?_)
  · simpa [Rectangle.reflectX] using hRx
  · simpa using hred i (isRight_reflectX.mp hi)

/-- `step_of_reducible_right` for an H-link with only V-tiles above it, transported along the
transposition: a tile with no integer width has integer height, an integer width transposed. -/
private theorem step_of_reducible_above {n : ℕ} (ih : ∀ m, m < n → IH m)
    (hcard : Fintype.card ι ≤ n) (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁)
    (hRy : R.y₀ < R.y₁) (hsides : ∀ i, (T i).HasIntegerSide)
    (l : Link R.transpose fun i ↦ (T i).transpose)
    (hred : ∀ i, IsRight l i → ¬ ∃ m : ℤ, (T i).width = m) : R.HasIntegerSide := by
  refine hasIntegerSide_transpose.mp (step_of_reducible_right ih hcard hT.transpose
    (properTranspose hp) hRy hRx (fun i ↦ hasIntegerSide_transpose.mpr (hsides i)) l
    fun i hi ↦ ?_)
  simpa using (hsides i).resolve_left (hred i hi)

/-- `step_of_reducible_left` transposed: an H-link with only V-tiles below it. -/
private theorem step_of_reducible_below {n : ℕ} (ih : ∀ m, m < n → IH m)
    (hcard : Fintype.card ι ≤ n) (hT : IsTiling R T) (hp : Proper T) (hRx : R.x₀ < R.x₁)
    (hRy : R.y₀ < R.y₁) (hsides : ∀ i, (T i).HasIntegerSide)
    (l : Link R.transpose fun i ↦ (T i).transpose)
    (hred : ∀ i, IsLeft l i → ¬ ∃ m : ℤ, (T i).width = m) : R.HasIntegerSide := by
  refine hasIntegerSide_transpose.mp (step_of_reducible_left ih hcard hT.transpose
    (properTranspose hp) hRy hRx (fun i ↦ hasIntegerSide_transpose.mpr (hsides i)) l
    fun i hi ↦ ?_)
  simpa using (hsides i).resolve_left (hred i hi)

/-- **Reducible-link proof** (Bishop–Wagon) of the integer-rectangle tiling theorem, by strong
induction on the number of tiles. A degenerate `R` has a zero side; a tiling that is not proper
loses a degenerate tile; if every tile has integer width, or every tile integer height, the
fg-area settles the matter at once; and otherwise some link is reducible (`exists_reducible`) and
the matching one of the four `step_of_reducible` lemmas loses a tile. -/
theorem IntegerRectangleTheorem_ReducibleLink : IntegerRectangleTheorem := by
  have main : ∀ n, IH n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro ι _ R T hcard hT hsides
      classical
      rcases eq_or_lt_of_le R.hx with hRx | hRx
      · exact Or.inl ⟨0, by simp [Rectangle.width, ← hRx]⟩
      rcases eq_or_lt_of_le R.hy with hRy | hRy
      · exact Or.inr ⟨0, by simp [Rectangle.height, ← hRy]⟩
      by_cases hp : Proper T
      case neg =>
        obtain ⟨i₀, hi₀⟩ := not_forall.mp hp
        have hlt := Fintype.card_subtype_lt
          (p := fun i ↦ (T i).x₀ < (T i).x₁ ∧ (T i).y₀ < (T i).y₁) hi₀
        exact ih _ (hlt.trans_le hcard) _ R _ le_rfl (isTiling_proper hT hRx hRy)
          fun i ↦ hsides i.1
      by_cases hH : ∀ i, ∃ m : ℤ, (T i).width = m
      · exact Or.inl (intWidth_of_forall hT hRy hH)
      by_cases hV : ∀ i, ¬ ∃ m : ℤ, (T i).width = m
      · exact Or.inr (intHeight_of_forall hT hRx fun i ↦ (hsides i).resolve_left (hV i))
      obtain ⟨b, hb⟩ := not_forall.mp hH
      obtain ⟨a, ha⟩ := not_forall.mp hV
      obtain ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨l, hl⟩ | ⟨l, hl⟩ :=
        exists_reducible (H := fun i ↦ ∃ m : ℤ, (T i).width = m) hT hp (not_not.mp ha) hb
      · exact step_of_reducible_right ih hcard hT hp hRx hRy hsides l hl
      · exact step_of_reducible_left ih hcard hT hp hRx hRy hsides l hl
      · exact step_of_reducible_above ih hcard hT hp hRx hRy hsides l hl
      · exact step_of_reducible_below ih hcard hT hp hRx hRy hsides l hl
  intro ι _ R T hT hsides
  exact main (Fintype.card ι) ι R T le_rfl hT hsides

end IntegerRectangle.ReducibleLink
