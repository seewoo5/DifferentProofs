import Verso
import VersoManual
import VersoBlueprint
import DifferentProofs.CombinatorialIdentities.Defs
import DifferentProofs.CombinatorialIdentities.HockeyStick
import DifferentProofs.CombinatorialIdentities.Pascal

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
Pascal's identity says that
$`\binom{n}{k} + \binom{n}{k+1} = \binom{n+1}{k+1}`.
:::

:::theorem "thm:pascal-identity-counting" (parent := "grp:comb-identities") (lean := "PascalIdentity_counting")
Pascal's identity holds by a counting argument.
:::

:::proof "thm:pascal-identity-counting"
Count subsets of cardinality $`k + 1` in a set with $`n + 1` elements,
according to whether they contain a distinguished element.
:::

:::definition "def:hockey-stick-identity" (parent := "grp:comb-identities") (lean := "HockeyStickIdentity")
The hockey-stick identity says that
$`\sum_{i=0}^{n} \binom{i+k}{k} = \binom{n+k+1}{k+1}`.
:::

:::theorem "thm:hockey-stick-identity-induction" (parent := "grp:comb-identities") (lean := "HockeyStickIdentity_induction")
The hockey-stick identity holds by induction.
:::

:::proof "thm:hockey-stick-identity-induction"
Induct on $`n`. The successor step adds the last summand and then uses
Pascal's identity at the end of the diagonal.
:::
