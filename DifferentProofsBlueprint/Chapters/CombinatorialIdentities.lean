import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.CombinatorialIdentities.Defs
import DifferentProofs.CombinatorialIdentities.HockeyStick.DoubleCounting
import DifferentProofs.CombinatorialIdentities.Pascal.Binomial
import DifferentProofs.CombinatorialIdentities.HockeyStick.Induction
import DifferentProofs.CombinatorialIdentities.Pascal.Counting

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Combinatorial Identities" =>

:::group "grp:comb-identities"
Combinatorial identities.
:::

:::definition "def:pascal-identity" (parent := "grp:comb-identities") (lean := "PascalIdentity")
For all $`n, k`, $`\binom{n}{k} + \binom{n}{k+1} = \binom{n+1}{k+1}`.
:::

:::theorem "thm:pascal-identity-counting" (parent := "grp:comb-identities") (lean := "PascalIdentity_counting")
Pascal's identity holds.
:::

:::proof "thm:pascal-identity-counting"
Count the subsets of cardinality $`k + 1` of $`\{0, 1, \dots, n\}` in two ways.
There are $`\binom{n+1}{k+1}` of them.
On the other hand, split them according to whether they contain the distinguished
element $`n`: deleting $`n` is a bijection between those that do and the subsets of
cardinality $`k` of $`\{0, 1, \dots, n-1\}`, of which there are $`\binom{n}{k}`,
while those that do not are exactly the subsets of cardinality $`k + 1` of
$`\{0, 1, \dots, n-1\}`, of which there are $`\binom{n}{k+1}`.
:::

:::theorem "thm:pascal-identity-binomial" (parent := "grp:comb-identities") (lean := "PascalIdentity_binomial")
Pascal's identity holds.
:::

:::proof "thm:pascal-identity-binomial"
Compare the coefficients of $`X^{k+1}` on the two sides of
$`(1 + X)^{n+1} = (1 + X)(1 + X)^n`.
By the binomial theorem, which is proved by induction on $`n`, the coefficient of $`X^j`
in $`(1 + X)^n` is $`\binom{n}{j}`. So the left-hand side contributes $`\binom{n+1}{k+1}`,
while multiplying by $`1 + X` adds a copy of the coefficients shifted by one, making the
right-hand side $`\binom{n}{k+1} + \binom{n}{k}`.
:::

:::definition "def:hockey-stick-identity" (parent := "grp:comb-identities") (lean := "HockeyStickIdentity")
For all $`n, k`, $`\sum_{i=0}^{n} \binom{i+k}{k} = \binom{n+k+1}{k+1}`.
:::

:::theorem "thm:hockey-stick-identity-induction" (parent := "grp:comb-identities") (lean := "HockeyStickIdentity_induction")
The hockey-stick identity holds.
:::

:::proof "thm:hockey-stick-identity-induction"
Induct on $`n`. The successor step adds the last summand and then uses
Pascal's identity at the end of the diagonal.
:::

:::theorem "thm:hockey-stick-identity-double-counting" (parent := "grp:comb-identities") (lean := "HockeyStickIdentity_doubleCounting")
The hockey-stick identity holds.
:::

:::proof "thm:hockey-stick-identity-double-counting"
Count the subsets of cardinality $`k + 1` of $`\{0, 1, \dots, n + k\}` in two ways.
There are $`\binom{n+k+1}{k+1}` of them.
On the other hand, sort them by their largest element $`m`, which ranges over
$`k, k+1, \dots, n+k`: deleting $`m` is a bijection between the subsets with largest
element $`m` and the subsets of cardinality $`k` of $`\{0, 1, \dots, m-1\}`, of which
there are $`\binom{m}{k}`. Summing over $`m = i + k` for $`0 \le i \le n` gives the
left-hand side.
:::
