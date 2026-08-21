# Different Proofs

This project contains formalizations of different proofs of the same mathematical result(s).

[Blueprint](https://seewoo5.github.io/DifferentProofs/).

## Theorems and proofs

### Fermat's little theorem

- [Using Binomial theorem](DifferentProofs/FermatLittleTheorem/Binomial.lean)
- [Using Alkauskas' product expansion](DifferentProofs/FermatLittleTheorem/Alkauskas.lean)
- [Using Lagrange's theorem](DifferentProofs/FermatLittleTheorem/Lagrange.lean)
- [Using a dynamical system](DifferentProofs/FermatLittleTheorem/Dynamical.lean)

### Infinitude of primes

- [Euclid's proof](DifferentProofs/InfinitudeOfPrimes/Euclid.lean)
- [Goldbach's proof](DifferentProofs/InfinitudeOfPrimes/Goldbach.lean)
- [Euler's proof](DifferentProofs/InfinitudeOfPrimes/Euler.lean)
- [Saidak's proof](DifferentProofs/InfinitudeOfPrimes/Saidak.lean)
- [Wunderlich's proof](DifferentProofs/InfinitudeOfPrimes/Wunderlich.lean)
- [Infinitely many primes in certain congruence classes](DifferentProofs/InfinitudeOfPrimes/Dirichlet.lean)
- [Using the irrationality of π² and the Euler product for ζ(2)](DifferentProofs/InfinitudeOfPrimes/Zeta.lean)

### Irrationality of √2

- [Using infinite descent](DifferentProofs/IrrationalSqrtTwo/Descent.lean)
- [Using 2-adic valuations](DifferentProofs/IrrationalSqrtTwo/Valuation.lean)
- [Using Fermat's last theorem for n = 3](DifferentProofs/IrrationalSqrtTwo/FermatLastTheorem.lean)

### Fermat's theorem on sums of two squares

- [Using quadratic reciprocity](DifferentProofs/SumOfTwoSquares/QuadraticReciprocity.lean)
- [Using Wilson's theorem](DifferentProofs/SumOfTwoSquares/Wilson.lean)
- [Zagier's one-sentence proof](DifferentProofs/SumOfTwoSquares/Zagier.lean)
- [Alpoge's proof via Jacobi sums](DifferentProofs/SumOfTwoSquares/Jacobi.lean)

### Basel problem

- [Using Parseval's identity](DifferentProofs/BaselProblem/Parseval.lean)
- [Using Cauchy's cotangent squeeze](DifferentProofs/BaselProblem/Cauchy.lean)

### Combinatorial identities

Pascal's rule, $\binom{n}{k} + \binom{n}{k+1} = \binom{n+1}{k+1}$:

- [Using double counting](DifferentProofs/CombinatorialIdentities/Pascal/Counting.lean)
- [Using the binomial theorem](DifferentProofs/CombinatorialIdentities/Pascal/Binomial.lean)

The hockey-stick identity, $\sum_{i=0}^{n} \binom{i+k}{k} = \binom{n+k+1}{k+1}$:

- [Using induction on n](DifferentProofs/CombinatorialIdentities/HockeyStick/Induction.lean)
- [Using double counting](DifferentProofs/CombinatorialIdentities/HockeyStick/DoubleCounting.lean)

### Tiling a rectangle

A rectangle tiled by rectangles each having an integer side has an integer side
([Stan Wagon, *Fourteen Proofs of a Result About Tiling a Rectangle*](https://www.jstor.org/stable/2322213)).

Listed in the paper's order, keeping its numbering so the gaps show which of the
fourteen proofs are still to come.

- Proof 1: [Complex double integral (de Bruijn)](DifferentProofs/IntegerRectangle/ComplexIntegral.lean)
- Proof 2: [Real double integral](DifferentProofs/IntegerRectangle/RealIntegral.lean)
- Proof 3: [Checkerboard colouring (Rochberg–Stein)](DifferentProofs/IntegerRectangle/Checkerboard.lean)
- Proof 4: [Counting squares (Ruzsa–Gilbert)](DifferentProofs/IntegerRectangle/CountingSquares.lean)
- Proof 5: [Polynomials (Douady)](DifferentProofs/IntegerRectangle/Polynomials.lean)
- Proof 6: [Prime numbers (Robinson)](DifferentProofs/IntegerRectangle/Primes.lean)
- Proof 7: [Eulerian path (Paterson)](DifferentProofs/IntegerRectangle/EulerianPath.lean)
- Proof 8: [Bipartite graph](DifferentProofs/IntegerRectangle/BipartiteGraph.lean)
- Proof 9: [Induction on the number of H-tiles (Robinson)](DifferentProofs/IntegerRectangle/Staircase.lean)
- Proof 10: [Induction on reducible links (Bishop–Wagon)](DifferentProofs/IntegerRectangle/ReducibleLink.lean)
- Proof 12: [Sweep line (Bachman–Yannakakis)](DifferentProofs/IntegerRectangle/SweepLine.lean)
- Proof 13: [Step functions (Hochster–Maté)](DifferentProofs/IntegerRectangle/StepFunction.lean)

## Verifying that the proofs prove the same thing

Because the point of the project is that these proofs establish *the same*
result, CI runs [Comparator](https://github.com/leanprover/comparator) over
every headline theorem. For each one it re-checks, without trusting the proof
file, that the proof establishes exactly the statement recorded in
[`DifferentProofsChallenge/`](DifferentProofsChallenge), that it uses no axioms
beyond `propext`, `Quot.sound`, and `Classical.choice`, and that the proof term
is accepted by a fresh run of the Lean kernel. Each `comparator/<Topic>.json`
lists the theorems to check for one topic.

Running it locally is optional — CI runs it on every pull request. Check
Comparator out *outside* this repository, since the directory name `comparator`
is taken here by the configs. It has to be built against the same Lean version
as this project, because the two share a Lean installation and `lean4export`
reads the project's `.olean` files; the commit below is the last one on v4.32.0,
and should be bumped together with `lean-toolchain`.

```sh
git clone https://github.com/leanprover/comparator ../comparator-tool
git -C ../comparator-tool checkout 07bc4ea40f2266dcb861820a2ec1fa3244ed307f
lake -d ../comparator-tool build lean4export comparator
```

Then, from the root of this project, run one topic at a time:

```sh
TOOL=$(realpath ../comparator-tool)
COMPARATOR_LANDRUN=$TOOL/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=$TOOL/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env "$TOOL/.lake/build/bin/comparator" comparator/IrrationalSqrtTwo.json
```

`fake-landrun.sh` is the shim Comparator ships for development, which runs the
builds unsandboxed. On Linux, build [landrun](https://github.com/Zouuup/landrun)
instead and point `COMPARATOR_LANDRUN` at it. Each topic takes roughly half a
minute to a few minutes once the project is built.

## Building and serving the blueprint locally

The [blueprint](https://seewoo5.github.io/DifferentProofs/) is built with
[Verso](https://github.com/leanprover/verso). To preview it locally:

```sh
# 1. Build the blueprint and generate the static site into _out/site
#    (creates _out/site/html-multi/)
./scripts/ci-pages.sh

# 2. Serve over HTTP and open http://localhost:8000
python3 -m http.server 8000 -d _out/site/html-multi
```

The site must be served over HTTP (any static server works, e.g. `npx serve`);
opening the files directly via `file://` fails because the pages fetch
`-verso-data/*.json`.
