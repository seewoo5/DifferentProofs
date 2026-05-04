module

import Architect
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

@[blueprint
  "def:flt"
  (statement := /-- Fermat's Little Theorem: for any prime $p$ and integer $a$,
    $a^p \equiv a \pmod{p}$. -/)
  (title := "Fermat's Little Theorem (statement, integer form)")
  (latexEnv := "definition")]
def FermatLittleTheorem : Prop := ∀ p : ℕ, ∀ a : ℤ, p.Prime → a ^ p ≡ a [ZMOD p]

@[blueprint
  "def:flt-nat"
  (statement := /-- Fermat's Little Theorem (natural-number form): for any prime $p$ and
    natural number $a$, $a^p \equiv a \pmod{p}$. -/)
  (title := "Fermat's Little Theorem (statement, natural-number form)")
  (latexEnv := "definition")]
def FermatLittleTheoremNat : Prop := ∀ p : ℕ, ∀ a : ℕ, p.Prime → a ^ p ≡ a [MOD p]
