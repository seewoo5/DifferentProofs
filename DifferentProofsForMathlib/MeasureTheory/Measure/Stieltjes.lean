/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.Algebra.Order.Floor

/-!
# The floor function as a Stieltjes function

`⌊·⌋` is monotone, and right-continuous because it is constant on `[x, ⌊x⌋ + 1)`, so it is a
Stieltjes function. The measure it induces gives an interval `(a, b]` the mass `⌊b⌋ - ⌊a⌋`, the
number of integers it contains: it is the counting measure of the integer points of the line.

This complements `StieltjesFunction.id`, whose measure is Lebesgue measure, and is intended for
`Mathlib/MeasureTheory/Measure/Stieltjes.lean`.
-/

@[expose] public section

namespace StieltjesFunction

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
  [TopologicalSpace R] [OrderClosedTopology R]

/-- The floor function `⌊·⌋` as a Stieltjes function. The associated measure gives an interval
`(a, b]` the mass `⌊b⌋ - ⌊a⌋`, so it is the counting measure of the integers. -/
@[simps]
protected def floor : StieltjesFunction R where
  toFun x := ⌊x⌋
  mono' _ _ h := Int.cast_le.2 (Int.floor_mono h)
  right_continuous' x := (tendsto_pure_nhds _ _).comp (tendsto_floor_right_pure_floor x)

end StieltjesFunction
