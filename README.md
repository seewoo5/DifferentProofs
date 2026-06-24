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

### Basel problem

- [Using Parseval's identity](DifferentProofs/BaselProblem/Parseval.lean)
- [Using Cauchy's cotangent squeeze](DifferentProofs/BaselProblem/Cauchy.lean)

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
