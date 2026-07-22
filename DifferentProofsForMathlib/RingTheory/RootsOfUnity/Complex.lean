/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.IntervalCases

/-!
# `Complex.I` is a primitive fourth root of unity

This complements `Complex.isPrimitiveRoot_exp` and is intended for
`Mathlib/RingTheory/RootsOfUnity/Complex.lean`.
-/

public section

namespace Complex

/-- `Complex.I` is a primitive fourth root of unity. -/
theorem isPrimitiveRoot_I : IsPrimitiveRoot I 4 :=
  IsPrimitiveRoot.mk_of_lt I (by norm_num) I_pow_four fun l hl0 hl4 ↦ by
    interval_cases l <;> norm_num [Complex.ext_iff, I_sq, I_pow_three]

end Complex
