module

public import DifferentProofs.IntegerRectangle.Defs

/-!
# Comparator challenge: tiling a rectangle

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.IntegerRectangle.*` is required to prove. See `comparator/README.md`.

Listed in the order of Stan Wagon's *Fourteen Proofs of a Result About Tiling a Rectangle*.

`IntegerRectangleTheorem` quantifies over `Type*`, so these theorems carry a universe parameter.
Comparator compares signatures syntactically, universe parameter names included, so the proof
files name it explicitly too rather than letting it be auto-bound.
-/

@[expose] public section

namespace IntegerRectangle

theorem ComplexIntegral.IntegerRectangleTheorem_ComplexIntegral.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem RealIntegral.IntegerRectangleTheorem_RealIntegral.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem Checkerboard.IntegerRectangleTheorem_Checkerboard.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem CountingSquares.IntegerRectangleTheorem_CountingSquares.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem Polynomials.IntegerRectangleTheorem_Polynomials.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem Primes.IntegerRectangleTheorem_Primes.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem EulerianPath.IntegerRectangleTheorem_EulerianPath.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem BipartiteGraph.IntegerRectangleTheorem_BipartiteGraph.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem SweepLine.IntegerRectangleTheorem_SweepLine.{u} :
    IntegerRectangleTheorem.{u} := sorry

theorem StepFunction.IntegerRectangleTheorem_StepFunction.{u} :
    IntegerRectangleTheorem.{u} := sorry

end IntegerRectangle
