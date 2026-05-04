module

import Architect
public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic

@[expose] public section

@[blueprint
  "thm:flt-binomial"
  (statement := /-- For any prime $p$ and integer $a$, we have $a^p \equiv a \pmod{p}$.-/)
  (hasProof := true)
  (proof := /--Use Freshmen's dream: $(a + b)^p = a^p + b^p$ in characteristic $p$.
    Then $(a + 1)^p \equiv a^p + 1 \pmod{p}$, and the result follows by induction on $a$. -/)
  (title := "Fermat's Little Theorem using the Binomial Theorem")
  (latexEnv := "theorem")]
theorem FermatLittleTheorem_Binomial : FermatLittleTheorem := by
  intro p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod p)]
  induction (a : ZMod p).val with
  | zero => simp [zero_pow hp.ne_zero]
  | succ k ih => rw [Nat.cast_succ, add_pow_expChar, ih, one_pow]
