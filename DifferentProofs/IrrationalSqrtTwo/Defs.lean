module

public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

def IrrationalSqrtTwo : Prop := Irrational (Real.sqrt 2)

def IrrationalSqrtTwoNat : Prop := ∀ p q : ℕ, p ^ 2 = 2 * q ^ 2 → q = 0
