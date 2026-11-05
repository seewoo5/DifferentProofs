import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.CombinatorialIdentities.Defs
import DifferentProofs.CombinatorialIdentities.HockeyStick.DoubleCounting
import DifferentProofs.CombinatorialIdentities.HockeyStick.Induction

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Combinatorial Identities" =>

:::group "grp:comb-identities"
Combinatorial identities.
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
