/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Complements on `Int.ceil` and `Int.fract`

`Int.ceil_eq_floor_iff_mem` completes the pair begun by
`Int.ceil_eq_floor_add_one_iff_notMem`: ceiling and floor agree exactly at the integers.

`Int.fract_eq_fract` reads `Int.fract a = Int.fract b ↔ ∃ z : ℤ, a - b = z`, which is congruence
modulo `1`. `Int.fract_eq_fract_iff_modEq` says so in mathlib's own notation, `a ≡ b [PMOD 1]` —
a connection between `Int.fract` and `AddCommGroup.ModEq` that is currently missing. That API
subtracts the other way round (`AddCommGroup.modEq_iff_zsmul'`, `toIcoMod_eq_toIcoMod`), and
`Int.fract_eq_fract'` records the orientation.

All three are intended for `Mathlib/Algebra/Order/Floor/Ring.lean`.
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
