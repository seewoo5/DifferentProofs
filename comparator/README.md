# Comparator checks

[Comparator](https://github.com/leanprover/comparator) is a judge for Lean proofs. It
re-derives, without trusting the proof files, that a named theorem really proves an
independently stated goal.

Every proof in this project is supposed to prove *the same statement* as the other proofs of
its theorem — that is the whole point of the repository. The Lean compiler already checks that
each file compiles, but on its own it does not stop a proof from quietly drifting to a weaker
statement, or from resting on an extra axiom. Comparator closes that gap. For each theorem
listed in a config here it guarantees:

1. the proof in `DifferentProofs/` proves exactly the statement written in the matching
   challenge module,
2. it uses no axioms beyond `propext`, `Quot.sound`, and `Classical.choice` — in particular no
   `sorry`, and
3. the resulting proof term is accepted by a fresh run of the Lean kernel.

## Layout

- `DifferentProofsChallenge/<Topic>.lean` states each theorem the project claims to prove, with
  `sorry` as the proof. This is the *challenge*: the reviewed record of what is being asserted.
- `comparator/<Topic>.json` names the theorems to check for that topic.

The challenge modules are deliberately left out of `defaultTargets`, since every declaration in
them is a `sorry` and `lake build` would report nothing else. Comparator builds them itself.

The solution module is always `DifferentProofs`, the root module that imports every proof, so
Comparator finds all the theorems in one environment.

## Coverage

Every headline theorem in the project is checked — all 42 of them, with no exclusions:

| Topic | Theorems |
| --- | --- |
| `BaselProblem` | 2 |
| `CombinatorialIdentities` | 4 |
| `FermatLittleTheorem` | 4 |
| `InfinitudeOfPrimes` | 11 |
| `IntegerRectangle` | 12 |
| `IrrationalSqrtTwo` | 5 |
| `SumOfTwoSquares` | 4 |

A *headline* theorem is one whose statement is a `Prop` from the topic's `Defs.lean` — the
result the project claims — as opposed to a supporting lemma. Bridging results such as
`InfinitudeOfPrimes_iff_InfinitudeOfPrimes'`, whose statement relates two of those `Prop`s
rather than being one, are not checked.

## Adding a new proof

1. State the theorem in `DifferentProofsChallenge/<Topic>.lean`, using its fully qualified name
   and the statement from the topic's `Defs.lean`.
2. Add that name to `comparator/<Topic>.json`.
3. Run `lake exe mk_all --lib DifferentProofsChallenge --module` if you added a new topic module.

Use the fully qualified name. Several proofs live in a namespace, so the name in the config is
for example `IntegerRectangle.Polynomials.IntegerRectangleTheorem_Polynomials`, not the short
form that appears in the source file.

Comparator compares signatures syntactically, universe parameter *names* included. No statement
here is universe-polymorphic today — `IntegerRectangleTheorem` deliberately fixes its tile-index
type to `Type` — so the question does not currently arise. Should one become polymorphic, write
its universe parameters out explicitly (`theorem foo.{u} : Bar.{u}`) in both the proof file and
the challenge, rather than letting them be auto-bound: an auto-bound name depends on incidental
file layout, since a preceding `variable {ι : Type*}` line claims `u_1` and pushes the theorem
to `u_2`. If a statement mismatch is ever reported for a theorem whose type looks identical, a
universe name is the first thing to check.

## Running it locally

Comparator has to be built against the same Lean version as this project, because the two share
a Lean installation and `lean4export` reads the project's `.olean` files. Commit
`07bc4ea40f2266dcb861820a2ec1fa3244ed307f` is the last one on v4.32.0; bump it together with
`lean-toolchain`.

Check the tool out *outside* this repository — the directory name `comparator` is already taken
here by the configs — and build it. Below it lives next to the project as `../comparator-tool`:

```sh
git clone https://github.com/leanprover/comparator ../comparator-tool
git -C ../comparator-tool checkout 07bc4ea40f2266dcb861820a2ec1fa3244ed307f
lake -d ../comparator-tool build lean4export comparator
```

On Linux, also build [landrun](https://github.com/Zouuup/landrun) — it is what sandboxes the
builds — and put it on `PATH`. Then, from the root of this project:

```sh
TOOL=$(realpath ../comparator-tool)
COMPARATOR_LEAN4EXPORT=$TOOL/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env "$TOOL/.lake/build/bin/comparator" comparator/IrrationalSqrtTwo.json
```

landrun uses Landlock and so is Linux-only. On macOS, substitute the shim Comparator ships for
development, which runs the commands unsandboxed:

```sh
TOOL=$(realpath ../comparator-tool)
COMPARATOR_LANDRUN=$TOOL/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=$TOOL/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env "$TOOL/.lake/build/bin/comparator" comparator/IrrationalSqrtTwo.json
```

Each topic takes roughly half a minute to two minutes once the project is built. Note that
Comparator shells out to `lake build`, so it will block if another `lake` process is holding
the project's build lock.

## On the sandbox

Comparator's README wraps the run in `systemd-run` to harden landrun against a solution that
actively attacks the sandbox. CI here does not, matching Comparator's own CI. That hardening
matters when you are judging a solution from an untrusted third party; here the "solution" is
this repository's own source, which CI compiles anyway. What the check buys us is the statement,
axiom, and kernel guarantees above, not protection from hostile code.
