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

### Tiling a rectangle

A rectangle tiled by rectangles each having an integer side has an integer side
([Stan Wagon, *Fourteen Proofs of a Result About Tiling a Rectangle*](https://www.jstor.org/stable/2322213)).

Listed in the paper's order, keeping its numbering so the gaps show which of the
fourteen proofs are still to come.

- Proof 1: [Complex double integral (de Bruijn)](DifferentProofs/IntegerRectangle/ComplexIntegral.lean)
- Proof 2: [Real double integral](DifferentProofs/IntegerRectangle/RealIntegral.lean)
- Proof 3: [Checkerboard colouring (Rochberg–Stein)](DifferentProofs/IntegerRectangle/Checkerboard.lean)
- Proof 5: [Polynomials (Douady)](DifferentProofs/IntegerRectangle/Polynomials.lean)
- Proof 6: [Prime numbers (Robinson)](DifferentProofs/IntegerRectangle/Primes.lean)
- Proof 8: [Bipartite graph](DifferentProofs/IntegerRectangle/BipartiteGraph.lean)
- Proof 12: [Sweep line (Bachman–Yannakakis)](DifferentProofs/IntegerRectangle/SweepLine.lean)
- Proof 13: [Step functions (Hochster–Maté)](DifferentProofs/IntegerRectangle/StepFunction.lean)

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
