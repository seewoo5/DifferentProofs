import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.InfinitudeOfPrimes.Basic
import DifferentProofs.InfinitudeOfPrimes.Defs
import DifferentProofs.InfinitudeOfPrimes.Euclid
import DifferentProofs.InfinitudeOfPrimes.Euler
import DifferentProofs.InfinitudeOfPrimes.Goldbach
import DifferentProofs.InfinitudeOfPrimes.Saidak
import DifferentProofs.InfinitudeOfPrimes.Wunderlich

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Infinitude of Primes" =>

:::group "grp:inf-primes"
Infinitude of primes.
:::

:::definition "def:inf-primes" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes")
There are infinitely many prime numbers.
:::

:::definition "def:inf-primes-large" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes'")
For any natural number $`n`, there exists a prime number greater than $`n`.
:::

:::theorem "thm:inf-primes-iff" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_iff_InfinitudeOfPrimes'")
The formulations {uses "def:inf-primes"}[] and {uses "def:inf-primes-large"}[]
are equivalent.
:::

:::proof "thm:inf-primes-iff"
Specialize the general characterization of infinite subsets of a locally finite
linear order to the set of natural primes.
:::

First proof is by Euclid.

:::theorem "thm:inf-primes-euclid-prod-primes" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Euclid'")
There are infinitely many prime numbers. This proof uses the product of the
finite set of all primes and proves {uses "def:inf-primes"}[].
:::

:::proof "thm:inf-primes-euclid-prod-primes"
If the set of primes were finite, a prime divisor of one plus their product
would already lie in the set, and therefore divide both the product and the
product plus one.
:::

A variant of Euclid's proof uses $`n! + 1` instead of the product of all primes.

:::theorem "thm:inf-primes-euclid-factorial" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Euclid")
There are infinitely many prime numbers.
:::

:::proof "thm:inf-primes-euclid-factorial"
If all primes were bounded by $`n`, a prime divisor of $`n! + 1` would both
divide $`n!` and divide $`n! + 1`, hence divide $`1`, impossible; so the primes
are infinite {uses "def:inf-primes"}[].
:::

Second proof is by Goldbach, using Fermat numbers $`F_n = 2^{2^n} + 1` and their pairwise coprimality.

:::definition "def:fermat-number" (parent := "grp:inf-primes") (lean := "Fermat")
The $`n`-th Fermat number is $`F_n = 2^{2^n} + 1`.
:::

:::lemma_ "lem:fermat-ge-two" (parent := "grp:inf-primes") (lean := "Fermat_gt_two")
For all natural numbers $`n`, the Fermat number $`F_n` is at least $`2`.
This is about {uses "def:fermat-number"}[].
:::

:::proof "lem:fermat-ge-two"
Since $`2^{2^n} \ge 1`, adding one gives $`F_n \ge 2`.
:::

:::lemma_ "lem:fermat-odd" (parent := "grp:inf-primes") (lean := "Fermat_odd")
Every Fermat number is odd. This is about {uses "def:fermat-number"}[].
:::

:::proof "lem:fermat-odd"
The exponent $`2^n` is positive, so $`2^{2^n}` is even and
$`2^{2^n}+1` is odd.
:::

:::lemma_ "lem:fermat-recurrence" (parent := "grp:inf-primes") (lean := "Fermat_recurrence")
For all $`n`, the Fermat numbers satisfy
$`F_{n+1} = \prod_{k=0}^{n} F_k + 2`. This uses
{uses "def:fermat-number"}[].
:::

:::proof "lem:fermat-recurrence"
Inductively prove that $`\prod_{k<n} F_k = F_n - 2`, then rewrite the next
product using the difference-of-squares identity.
:::

:::lemma_ "lem:fermat-coprime" (parent := "grp:inf-primes") (lean := "Fermat_coprime")
For all $`n`, $`F_{n+1}` is coprime to $`\prod_{k=0}^{n} F_k`.
This depends on {uses "lem:fermat-recurrence"}[] and {uses "lem:fermat-odd"}[].
:::

:::proof "lem:fermat-coprime"
The recurrence writes $`F_{n+1}` as the product plus $`2`. The product is odd,
so the only possible common divisor with $`2` is $`1`.
:::

:::lemma_ "lem:fermat-pairwise-coprime" (parent := "grp:inf-primes") (lean := "Fermat_pairwise_coprime")
Distinct Fermat numbers are coprime. This follows from
{uses "lem:fermat-coprime"}[].
:::

:::proof "lem:fermat-pairwise-coprime"
For $`m<n`, the number $`F_m` divides the product of the earlier Fermat
numbers, which is coprime to $`F_n`.
:::

:::theorem "thm:inf-primes-goldbach" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Goldbach")
There are infinitely many prime numbers.
:::

:::proof "thm:inf-primes-goldbach"
Each Fermat number has a prime divisor. Pairwise coprimality
{uses "lem:fermat-pairwise-coprime"}[] makes the chosen prime divisors pairwise
distinct, producing infinitely many primes.
:::

Third proof is by Euler, using the divergence of the harmonic series and the Euler product formula.

:::theorem "thm:harmonic-unbounded" (parent := "grp:inf-primes") (lean := "harmonic_unbounded")
The harmonic series is unbounded.
:::

:::proof "thm:harmonic-unbounded"
Use the inequality $`\log(n+1) \le H_n` and the fact that the logarithm is
unbounded.
:::

:::theorem "thm:euler-prod-ge-harmonic" (parent := "grp:inf-primes") (lean := "prod_prime_div_prime_sub_one_ge_harmonic")
The finite Euler product over primes at most $`n` is at least the $`n`-th
harmonic number.
:::

:::proof "thm:euler-prod-ge-harmonic"
Expand each factor $`p/(p-1)` as a finite geometric sum. The resulting product
contains terms corresponding to reciprocals of positive integers up to $`n`.
:::

:::theorem "thm:inf-primes-euler" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Euler")
There are infinitely many prime numbers.
:::

:::proof "thm:inf-primes-euler"
If there were only finitely many primes, the Euler product over all of them
would be fixed. But the product over primes below a sufficiently large bound
{uses "thm:euler-prod-ge-harmonic"}[] dominates arbitrarily large harmonic sums
{uses "thm:harmonic-unbounded"}[], a contradiction.
:::

Fourth proof is by Saidak, using the sequence $`a_0 = 2` and $`a_{n+1} = a_n(a_n+1)`.

:::definition "def:saidak-sequence" (parent := "grp:inf-primes") (lean := "a")
Saidak's sequence is defined by $`a_0 = 2` and
$`a_{n+1} = a_n(a_n+1)`.
:::

:::lemma_ "lem:saidak-ge-two" (parent := "grp:inf-primes") (lean := "a_ge_two")
Every term of Saidak's sequence is at least $`2`. This is about
{uses "def:saidak-sequence"}[].
:::

:::proof "lem:saidak-ge-two"
The base case is $`2`; the inductive step multiplies two positive factors and
stays at least $`2`.
:::

:::lemma_ "lem:saidak-primeFactors-card" (parent := "grp:inf-primes") (lean := "a_primeFactors_card_ge")
For every $`n`, the term $`a_n` has at least $`n+1` distinct prime divisors.
This uses {uses "def:saidak-sequence"}[] and {uses "lem:saidak-ge-two"}[].
:::

:::proof "lem:saidak-primeFactors-card"
Consecutive numbers $`a_n` and $`a_n+1` are coprime, so the prime factors of
$`a_{n+1}` split as a disjoint union of the prime factors of the two factors.
:::

:::theorem "thm:inf-primes-saidak" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Saidak")
There are infinitely many prime numbers.
:::

:::proof "thm:inf-primes-saidak"
If only finitely many primes existed, the number of prime factors of any
$`a_n` would be bounded by that finite set, contradicting the previous lemma
{uses "lem:saidak-primeFactors-card"}[] for large $`n`.
:::

Fifth proof is by Wunderlich, using Fibonacci numbers, their coprimality, and the fact that $`F_{37}` has three distinct prime factors.

:::lemma_ "lem:fib-37-factorization" (parent := "grp:inf-primes") (lean := "fib_37")
The Fibonacci number $`F_{37}` factors as $`73 \cdot 149 \cdot 2221`.
:::

:::proof "lem:fib-37-factorization"
This is a direct computation.
:::

:::lemma_ "lem:fib-prime-ge-two" (parent := "grp:inf-primes") (lean := "fib_prime_ge_two")
For any odd prime $`p`, the Fibonacci number $`F_p` is at least $`2`.
:::

:::proof "lem:fib-prime-ge-two"
An odd prime is at least $`3`, and the Fibonacci sequence is monotone, so
$`F_p \ge F_3 = 2`.
:::

:::lemma_ "lem:fib-coprime-distinct-primes" (parent := "grp:inf-primes") (lean := "fib_coprime_of_distinct_primes")
If $`p` and $`q` are distinct primes, then $`F_p` and $`F_q` are coprime.
:::

:::proof "lem:fib-coprime-distinct-primes"
Distinct primes are coprime, and
$`\gcd(F_m,F_n) = F_{\gcd(m,n)}` reduces the result to $`F_1=1`.
:::

:::theorem "thm:inf-primes-wunderlich" (parent := "grp:inf-primes") (lean := "InfinitudeOfPrimes_Wunderlich")
There are infinitely many prime numbers.
:::

:::proof "thm:inf-primes-wunderlich"
Assuming finitely many primes, look at Fibonacci numbers indexed by odd primes,
each at least $`2` {uses "lem:fib-prime-ge-two"}[]. They are pairwise coprime
{uses "lem:fib-coprime-distinct-primes"}[], but $`F_{37}` already has three
distinct prime factors {uses "lem:fib-37-factorization"}[], contradicting the
finite counting bound.
:::
