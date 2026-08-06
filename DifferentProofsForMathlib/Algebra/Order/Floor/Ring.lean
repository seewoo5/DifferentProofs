/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Ceiling equals floor exactly at the integers

`Int.ceil_eq_floor_add_one_iff_notMem` says that the ceiling of a non-integer exceeds its floor by
one. `Int.ceil_eq_floor_iff_mem` below is the complementary statement — ceiling and floor agree
exactly at the integers — completing the pair, alongside the existing `Int.floor_eq_self_iff_mem`
and `Int.ceil_eq_self_iff_mem`.

This is intended for `Mathlib/Algebra/Order/Floor/Ring.lean`, next to
`Int.ceil_eq_floor_add_one_iff_notMem`.
-/

@[expose] public section

namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

lemma ceil_eq_floor_iff_mem (a : R) : ⌈a⌉ = ⌊a⌋ ↔ a ∈ Set.range Int.cast := by
  rw [← not_iff_not, ← ceil_eq_floor_add_one_iff_notMem]
  have := floor_le_ceil a
  have := ceil_le_floor_add_one a
  lia

end Int
