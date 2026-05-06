---
name: different-proofs-add
description: Add a new formalization to the DifferentProofs repo (e.g. another proof of infinitude of primes or Fermat's little theorem). Use when finishing a `sorry`-skeleton file or porting an informal proof.
---

# Adding a new proof to DifferentProofs

The repo collects several Lean 4 proofs of the same theorem. Each new proof goes in its own file under `DifferentProofs/<TheoremName>/<ProofName>.lean`. The recipe below covers the *scaffolding* — the proof itself is your job.

## Five-step recipe

1. **Formalize** the body of the target lemmas/theorem in `<file>.lean`. Replace every `sorry`. Keep the existing header (`module`, `import Architect`, `public import …`, `@[expose] public section`) and the `@[blueprint …]` attribute blocks unchanged unless you are adding new declarations.
2. **Golf** with the project's `lean4:proof-golfer` agent (or `/cleanup` if available). Aim for ~30% reduction; don't sacrifice readability.
3. **Update README.md and the blueprint section file** under `blueprint/src/sections/<theorem>.tex`. README gets a bullet `- [<Name>'s proof](DifferentProofs/<Theorem>/<Name>.lean)`. The blueprint section gets `\section{<Name>'s proof}` followed by `\inputleanmodule{DifferentProofs.<Theorem>.<Name>}`.
4. **Update the root module**: `lake exe mk_all --module` regenerates `DifferentProofs.lean`.
5. **Build** in this order and check each step is clean:
   - `lake build DifferentProofs.<Theorem>.<Name>` — Lean compiles.
   - `lake build :blueprint` — blueprint artifacts generate.
   - `leanblueprint all` — web (`blueprint/web/index.html`) and PDF (`blueprint/print/print.pdf`) build.

## Gotchas (learned the hard way)

- **`decide` on primality of 4-digit numbers blows the recursion limit.** Import `Mathlib.Tactic.NormNum.Prime` and use `by norm_num` instead.
- **`nlinarith` is not in scope.** Use `lia` for linear arithmetic over `ℕ`/`ℤ`. For nonlinear goals, find a structured proof or use `ring_nf; lia`.
- **`Finset.sum_le_sum` etc. need `Mathlib.Algebra.Order.BigOperators.Group.Finset`.** Not transitively imported via the typical Saidak/Goldbach header — add it explicitly.
- **The `show` tactic triggers a style linter** when it changes the goal (i.e. unfolds a definition). Use `change` instead.
- **Blueprint prose must be valid LaTeX.** Anything with `_` (subscripts) needs `$...$` math mode. A bare `\{p_1 = 2, p_2, \ldots\}` inside a `(proof := /-- ... -/)` block will pass `lake build :blueprint` but make `leanblueprint all` fail with "Missing $ inserted". Wrap subscripted text in `$ … $`.
- **`leanblueprint all` returning errors but a PDF appears anyway** usually means unresolved `\cref`s on the first pdflatex pass; rerun once and they should resolve. If they don't, you likely have a real LaTeX syntax error — check `blueprint/print/print.log`.
- **The `@[blueprint …]` attribute keys**: `(statement := /-- … -/)`, `(hasProof := true)`, `(proof := /-- … -/)`, `(title := "…")`, `(latexEnv := "definition" | "lemma" | "theorem")`. Labels are referenced from other proofs by their key string (e.g. `"lem:saidak-ge-two"`), and `\uses{…}` lines in the generated `.tex` are auto-derived from the Lean dependencies.

## House style

- Term-mode proofs preferred when shorter.
- Don't introduce `set` bindings just to rename — only when the alias is reused enough to pay for itself.
- Prove `≥ 1` cardinality bounds via `Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr …)`.
- Use `Finset.card_eq_sum_ones` to convert `s.card ≤ ∑ x ∈ s, f x` problems into `Finset.sum_le_sum`.
- For pairwise-disjoint prime-factor unions, the closing chain is `← Finset.card_biUnion hpwd; Finset.card_le_card hbU`.
- Reference files for style: `DifferentProofs/InfinitudeOfPrimes/{Goldbach,Saidak,Wunderlich}.lean`.

## Final commit + PR

After everything builds, the typical pattern is one branch per proof, one commit titled `<Name>'s proof of <theorem>`, body listing the new file + README/blueprint/root-module updates. Push and `gh pr create`.
