module

public import DifferentProofs.IntegerRectangle.Defs

/-!
# Comparator challenge: tiling a rectangle

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.IntegerRectangle.*` is required to prove. See `comparator/README.md`.

Listed in the order of Stan Wagon's *Fourteen Proofs of a Result About Tiling a Rectangle*.

`IntegerRectangleTheorem` quantifies over `Type*`, so these theorems carry a universe
parameter, and Comparator compares signatures syntactically — universe parameter *names*
included. The names are therefore written out here instead of being auto-bound. They are not
uniform: a proof file whose headline theorem is preceded by a `variable {ι : Type*}` line has
already spent `u_1` on that variable, so its theorem auto-binds `u_2`. If one of these stops
matching, check whether such a `variable` line was added to or removed from the proof file.
-/

@[expose] public section

namespace IntegerRectangle

theorem ComplexIntegral.IntegerRectangleTheorem_ComplexIntegral.{u_1} :
    IntegerRectangleTheorem.{u_1} := sorry

theorem RealIntegral.IntegerRectangleTheorem_RealIntegral.{u_1} :
    IntegerRectangleTheorem.{u_1} := sorry

theorem Checkerboard.IntegerRectangleTheorem_Checkerboard.{u_1} :
    IntegerRectangleTheorem.{u_1} := sorry

theorem CountingSquares.IntegerRectangleTheorem_CountingSquares.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

theorem Polynomials.IntegerRectangleTheorem_Polynomials.{u_1} :
    IntegerRectangleTheorem.{u_1} := sorry

theorem Primes.IntegerRectangleTheorem_Primes.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

theorem EulerianPath.IntegerRectangleTheorem_EulerianPath.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

theorem BipartiteGraph.IntegerRectangleTheorem_BipartiteGraph.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

theorem SweepLine.IntegerRectangleTheorem_SweepLine.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

theorem StepFunction.IntegerRectangleTheorem_StepFunction.{u_2} :
    IntegerRectangleTheorem.{u_2} := sorry

end IntegerRectangle
