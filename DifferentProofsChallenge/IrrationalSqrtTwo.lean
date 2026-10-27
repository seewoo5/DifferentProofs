module

public import Mathlib.NumberTheory.Real.Irrational

/-!
# Comparator challenge: irrationality of `√2`

Each theorem below records the statement that the correspondingly named declaration in
`DifferentProofs.IrrationalSqrtTwo.*` is required to prove. See `README.md` for what the Comparator
check guarantees and how to run it.
-/

@[expose] public section

def IrrationalSqrtTwo : Prop := Irrational (Real.sqrt 2)

def IrrationalSqrtTwoNat : Prop := ∀ p q : ℕ, p ^ 2 = 2 * q ^ 2 → q = 0

theorem IrrationalSqrtTwo_Descent : IrrationalSqrtTwo := sorry

theorem IrrationalSqrtTwoNat_Descent : IrrationalSqrtTwoNat := sorry

theorem IrrationalSqrtTwo_Valuation : IrrationalSqrtTwo := sorry

theorem IrrationalSqrtTwoNat_Valuation : IrrationalSqrtTwoNat := sorry

theorem IrrationalSqrtTwo_FermatLastTheorem : IrrationalSqrtTwo := sorry

theorem IrrationalSqrtTwo_CongruentNumber : IrrationalSqrtTwo := sorry
