module

import Architect
public import DifferentProofs.FermatLittleTheorem.Defs
public import Mathlib.Data.ZMod.Basic

@[expose] public section

@[blueprint
  "thm:flt-nat-impl-flt"
  (statement := /-- The natural-number form of Fermat's Little Theorem implies the integer form;
    that is, \cref{def:flt-nat} implies \cref{def:flt}. -/)
  (hasProof := true)
  (proof := /-- Working in $\mathbb{Z}/p\mathbb{Z}$, every element is the cast of its
    natural-number representative $b := (a \bmod p).val \in \mathbb{N}$. Applying the
    natural-number form to $b$ gives $b^p \equiv b \pmod p$, which lifts back through the
    canonical map to $a^p \equiv a \pmod p$. -/)
  (title := "Reduction of FLT to the natural-number case")
  (latexEnv := "theorem")]
theorem FermatLittleTheoremNat_impl_FermatLittleTheorem :
    FermatLittleTheoremNat → FermatLittleTheorem := by
  intro hN p a hp
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod p), ← Nat.cast_pow]
  exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN p _ hp)
