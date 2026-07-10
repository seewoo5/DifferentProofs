# Contributing

Different Proofs is a Lean project collecting formalizations of different
proofs of the same mathematical results, together with a blueprint explaining
the arguments.

## New theorems and proofs

Contributions of new theorem families and new proofs of existing theorem
families are welcome.

Before starting substantial formalization work, please open an issue describing
the theorem or proof you want to add. This helps check that the statement fits
the scope of the project, avoids duplicated work, and gives maintainers a chance
to discuss the intended mathematical statement and proof strategy.

When adding a new proof, please make the Lean statement match the intended
mathematics carefully, add the relevant imports, and update the project index
and blueprint where appropriate.

## Formalizations that may belong in mathlib

Sometimes a proof may require a useful fact that is not yet available in
mathlib, but is general enough that it could eventually be upstreamed. There
are no such formalizations in this project at the moment.

When such material appears, put it under a new `DifferentProofsForMathlib/`
directory instead of burying it inside a theorem-specific folder. This directory
is for reusable supporting results that are useful beyond this project, not for
lemmas whose statements are tailored only to one proof here.

The directory structure should mirror the corresponding mathlib location as
closely as possible. For example, material that would ideally live in
`Mathlib/AAA/BBB/CCC.lean` should go in
`DifferentProofsForMathlib/AAA/BBB/CCC.lean`, with module names arranged so that
the project-local import can later be replaced mechanically. Ideally, once the
result is upstreamed, code importing `ForMathlib.AAA.BBB.CCC` should only need
to switch to `Mathlib.AAA.BBB.CCC`.

For this kind of contribution:

- First check that the result is not already in mathlib, possibly under a
  different name or in a more general form.
- State the result in a mathlib-friendly form, with appropriate generality and
  namespacing.
- Follow mathlib's directory structure for the file's expected final home, so
  later upstreaming does not require moving unrelated project code around.
- Keep imports as small and natural as possible.
- Prefer names, theorem statements, and proof style that would make sense in a
  future mathlib pull request.
- Add comments only when they clarify why the result is placed here or where it
  might eventually belong upstream.
- When the directory is first introduced, also add the corresponding root module
  and build configuration needed for `lake build` to check it.

If a result from `DifferentProofsForMathlib/` is later accepted into mathlib,
remove the local copy and update this project to use the mathlib version.

## Blueprint contributions

The blueprint is written as a Verso manual using `VersoBlueprint`. It records
the informal statements, proof sketches, and dependency graph for the Lean
formalizations.

Blueprint files live under `DifferentProofsBlueprint/`:

- `DifferentProofsBlueprint/Blueprint.lean` is the top-level document. It
  imports the chapter modules and includes them in the rendered blueprint.
- `DifferentProofsBlueprint/Chapters/*.lean` contains the topic chapters.
- `DifferentProofsBlueprintMain.lean` is used to render the static site.

When adding a new theorem family, usually add a new chapter file under
`DifferentProofsBlueprint/Chapters/`, import it from
`DifferentProofsBlueprint/Blueprint.lean`, and add an `{include ...}` line in
the desired order. When adding a new proof to an existing theorem family, update
the corresponding chapter.

Follow the existing chapter style:

- Start with the usual Verso and blueprint imports, then import the Lean files
  that contain the formal declarations being discussed.
- Use a `:::group` block for a theorem family.
- Use `:::definition`, `:::theorem`, or `:::lemma_` blocks for the main
  mathematical objects and claims.
- Give each block a stable, unique blueprint id such as `grp:...`, `def:...`,
  `thm:...`, or `lem:...`.
- Add `(parent := "...")` so the graph is organized under the relevant group.
- Add `(lean := "...")` when a block corresponds to a Lean declaration.
- Use `:::proof "..."` blocks for proof sketches, where the string matches the
  theorem or lemma id.
- Use `{uses "..."}[]` links to record important dependencies between blueprint
  items.

### Proof-complete dependency-graph colors

The project extends theorem-like blueprint directives with a `proofColor`
option. Put the option beside each theorem in its topic chapter, using the same
color for nodes that have exactly the same mathematical statement. A chapter
that uses this option must import `DifferentProofsBlueprint.ProofColor`:

```lean
:::theorem "thm:flt-binomial" (lean := "FermatLittleTheorem_Binomial") (proofColor := "#ddd6fe")
The binomial proof of Fermat's little theorem.
:::
```

The color must have the form `#RRGGBB`. It replaces the normal green proof fill
only when the theorem's Lean proof is sorry-free and every dependency recorded
in the blueprint is complete. Until then, the node keeps its ordinary status
color, and its tooltip says that the custom color is still pending. This makes
`proofColor` safe to add while a proof is under development.

Blueprint text should be mathematically accurate but concise. It should explain
the proof idea and the role of important intermediate lemmas, not reproduce
every line of the Lean proof.

To build and preview the blueprint locally, run:

```sh
./scripts/ci-pages.sh
python3 -m http.server 8000 -d _out/site/html-multi
```

Then open `http://localhost:8000`. The generated site should be served over
HTTP; opening the HTML files directly via `file://` does not load all blueprint
data correctly.

## AI-assisted contributions

AI-assisted contributions are welcome, but they need extra care.

If you use AI tools to draft statements, proofs, explanations, refactors, or
review comments, please say so transparently in the pull request. Briefly
describe which tools were used and what parts of the contribution they helped
with.

Please check AI-assisted work line by line before submitting it. In particular:

- Verify that every theorem statement says exactly what is intended.
- Check that each proof step proves the intended intermediate claim, not merely
  something Lean accepts for accidental reasons.
- Review imports, names, comments, and blueprint text for mathematical accuracy.
- Do not rely on generated explanations unless you have independently checked
  them against the Lean code and the underlying mathematics.

The final responsibility for correctness and clarity rests with the contributor
submitting the pull request.

## Before opening a pull request

Please make sure the project builds locally:

```sh
lake build
```

For changes that affect the blueprint, also check that the blueprint still
builds and renders correctly.
