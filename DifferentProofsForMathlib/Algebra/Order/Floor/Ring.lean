/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Complements on `Int.floor`, `Int.ceil` and `Int.fract`

## Ceiling equals floor exactly at the integers

`Int.ceil_eq_floor_add_one_iff_notMem` says that the ceiling of a non-integer exceeds its floor by
one. `Int.ceil_eq_floor_iff_mem` below is the complementary statement — ceiling and floor agree
exactly at the integers — completing the pair, alongside the existing `Int.floor_eq_self_iff_mem`
and `Int.ceil_eq_self_iff_mem`.

## Two reals have the same fractional part exactly when they are congruent mod one

`Int.fract_eq_fract` reads `Int.fract a = Int.fract b ↔ ∃ z : ℤ, a - b = z`; that is congruence
modulo `1`, which mathlib expresses as `a ≡ b [PMOD (1 : R)]`. The identification is
`Int.fract_eq_fract_iff_modEq` below, and it is missing: nothing currently connects `Int.fract` to
`AddCommGroup.ModEq`. The `Int.fract` section of `Mathlib/Algebra/Order/ToIntervalMod.lean` stops
at `toIcoMod_zero_one`, from which the identification also follows for a linear ordered field,
whereas below it holds in any `FloorRing`.

The `[PMOD]` API states the difference the other way round —
`AddCommGroup.modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p`, and likewise
`AddCommGroup.modEq_iff_eq_add_zsmul` and `toIcoMod_eq_toIcoMod` — so `Int.fract_eq_fract` is the
odd one out among its neighbours. `Int.fract_eq_fract'` records that orientation, which is the one
wanted whenever `b` is reached from `a` by adding an integer.

Both are intended for `Mathlib/Algebra/Order/Floor/Ring.lean`, the first next to
`Int.ceil_eq_floor_add_one_iff_notMem` and the other two next to `Int.fract_eq_fract`. That file
does not yet import `Mathlib/Algebra/Group/ModEq.lean`, which is a cheap import: it needs only
`Mathlib/Algebra/Group/Hom/Defs.lean` and `Mathlib/Algebra/Group/Torsion.lean`.
-/

@[expose] public section

namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R] {a b : R}

lemma ceil_eq_floor_iff_mem (a : R) : ⌈a⌉ = ⌊a⌋ ↔ a ∈ Set.range Int.cast := by
  rw [← not_iff_not, ← ceil_eq_floor_add_one_iff_notMem]
  have := floor_le_ceil a
  have := ceil_le_floor_add_one a
  lia

/-- **Two elements have the same fractional part exactly when they are congruent modulo one.** -/
theorem fract_eq_fract_iff_modEq : fract a = fract b ↔ a ≡ b [PMOD (1 : R)] := by
  rw [fract_eq_fract, AddCommGroup.modEq_iff_zsmul']
  simp only [zsmul_eq_mul, mul_one]
  constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨-z, by rw [Int.cast_neg, ← hz, neg_sub]⟩

/-- `Int.fract_eq_fract` with the difference taken in the direction used by the `[PMOD]` API. -/
theorem fract_eq_fract' : fract a = fract b ↔ ∃ n : ℤ, b - a = n := by
  simp [fract_eq_fract_iff_modEq, AddCommGroup.modEq_iff_zsmul']

end Int
