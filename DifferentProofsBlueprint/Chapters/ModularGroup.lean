import Verso
import VersoManual
import VersoBlueprint
import DifferentProofsBlueprint.ProofColor
import DifferentProofs.ModularGroup.Alperin
import DifferentProofs.ModularGroup.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "The Modular Group" =>

:::group "grp:modular"
The modular group is a free product.
:::

:::definition "def:modular" (parent := "grp:modular") (lean := "ModularGroupFreeProduct")
The modular group $`\mathrm{PSL}(2, \mathbb{Z}) = \mathrm{SL}(2, \mathbb{Z}) / \{\pm 1\}` is isomorphic
to the free product $`C_2 * C_3` of a cyclic group of order two and a cyclic group of order three.
:::

First proof is Alperin's, by the ping-pong lemma, following the blog post
[An elementary application of ping-pong lemma](https://chiasme.wordpress.com/2015/03/08/an-elementary-application-of-ping-pong-lemma/).
The theorem is usually proved through the action of $`\mathrm{PSL}(2, \mathbb{Z})` on the hyperbolic
plane; R. C. Alperin (Amer. Math. Monthly 100 (1993), 385–386) observed that its action on the
irrational numbers by Möbius transformations is enough. Throughout,
$`S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}` and
$`T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}`.

:::lemma_ "lem:modular-alperin-generators" (parent := "grp:modular") (lean := "ModularGroup.Alperin.B_sq, ModularGroup.Alperin.C_pow_three, ModularGroup.Alperin.C_mul_B")
Let $`B` and $`C` be the images of $`S` and $`TS = \begin{pmatrix} 1 & -1 \\ 1 & 0 \end{pmatrix}`
in $`\mathrm{PSL}(2, \mathbb{Z})`. Then $`B^2 = 1`, $`C^3 = 1`, and $`CB = T`.
:::

:::proof "lem:modular-alperin-generators"
In $`\mathrm{SL}(2, \mathbb{Z})` one computes $`S^2 = (TS)^3 = -1` and $`TSS = -T`, and $`-1` is
central, so its image in $`\mathrm{PSL}(2, \mathbb{Z})` is trivial.
:::

:::lemma_ "lem:modular-alperin-action" (parent := "grp:modular") (lean := "ModularGroup.Alperin.smul_coe_eq_ite, ModularGroup.Alperin.B_smul, ModularGroup.Alperin.C_smul, ModularGroup.Alperin.C_inv_smul")
The group $`\mathrm{PSL}(2, \mathbb{Z})` acts on $`\mathbb{R} \cup \{\infty\}` by the Möbius
transformations $`\begin{pmatrix} a & b \\ c & d \end{pmatrix} \cdot x = \frac{ax + b}{cx + d}`.
In particular, $`B \cdot x = -\frac{1}{x}` and $`C \cdot x = 1 - \frac{1}{x}` for real $`x \neq 0`,
and $`C^{-1} \cdot x = \frac{1}{1 - x}` for real $`x \neq 1`.
:::

:::proof "lem:modular-alperin-action"
The group $`\mathrm{GL}(2, \mathbb{R})` acts on the projective line $`\mathbb{R} \cup \{\infty\}` by
Möbius transformations, and $`\mathrm{SL}(2, \mathbb{Z})` acts through it. A central element of
$`\mathrm{SL}(2, \mathbb{Z})` is a scalar matrix, which acts trivially, so the action factors
through $`\mathrm{PSL}(2, \mathbb{Z})`. The formulas for $`B` and $`C` are read off from the
matrices $`S` and $`TS`, and the one for $`C^{-1}` follows from
$`C \cdot \frac{1}{1 - x} = 1 - (1 - x) = x`.
:::

:::lemma_ "lem:modular-alperin-ping-pong-sets" (parent := "grp:modular") (lean := "ModularGroup.Alperin.B_smul_P, ModularGroup.Alperin.C_smul_N, ModularGroup.Alperin.C_inv_smul_N")
Let $`\mathcal{P}` and $`\mathcal{N}` be the sets of positive and of negative irrational numbers.
Then $`B(\mathcal{P}) \subseteq \mathcal{N}` and $`C^{\pm 1}(\mathcal{N}) \subseteq \mathcal{P}`.
:::

:::proof "lem:modular-alperin-ping-pong-sets"
By {uses "lem:modular-alperin-action"}[], the three maps are $`x \mapsto -\frac{1}{x}`,
$`x \mapsto 1 - \frac{1}{x}` and $`x \mapsto \frac{1}{1 - x}`, which send irrational numbers to
irrational numbers. If $`x > 0` then $`-\frac{1}{x} < 0`, and if $`x < 0` then
$`1 - \frac{1}{x} > 1` and $`0 < \frac{1}{1 - x} < 1`.
:::

:::lemma_ "lem:modular-alperin-injective" (parent := "grp:modular") (lean := "ModularGroup.Alperin.lift_toPSL_injective")
The homomorphism $`C_2 * C_3 \to \mathrm{PSL}(2, \mathbb{Z})` sending the generators of $`C_2` and
$`C_3` to $`B` and $`C` is injective.
:::

:::proof "lem:modular-alperin-injective"
The homomorphism exists because $`B^2 = 1` and $`C^3 = 1` {uses "lem:modular-alperin-generators"}[].
Apply the ping-pong lemma to the action of {uses "lem:modular-alperin-action"}[], with the set
$`\mathcal{N}` for the factor $`C_2` and $`\mathcal{P}` for $`C_3`. These sets are nonempty, as
they contain $`\mp\sqrt{2}`, and disjoint, and by {uses "lem:modular-alperin-ping-pong-sets"}[]
the nontrivial element $`B` of $`C_2` maps $`\mathcal{P}` into $`\mathcal{N}`, while the nontrivial
elements $`C` and $`C^{-1}` of $`C_3` map $`\mathcal{N}` into $`\mathcal{P}`. A nonempty reduced
word of odd length therefore maps $`\mathcal{P}` into $`\mathcal{N}` or $`\mathcal{N}` into
$`\mathcal{P}`, so it is not the identity. A word of even length begins in one factor and ends in
the other. The blog post conjugates it by $`B` if necessary, so that it begins with $`C^{\pm 1}`
and ends with $`B`, and observes that it maps $`\mathcal{P}` into the irrational numbers greater
than $`1` or into those less than $`1`. The ping-pong lemma, as formalized in mathlib, instead
conjugates it by an element of $`C_3`, which has three elements, to obtain a word of odd length.
:::

:::lemma_ "lem:modular-alperin-surjective" (parent := "grp:modular") (lean := "ModularGroup.Alperin.lift_toPSL_surjective")
The homomorphism $`C_2 * C_3 \to \mathrm{PSL}(2, \mathbb{Z})` is surjective.
:::

:::proof "lem:modular-alperin-surjective"
The matrices $`S` and $`T` generate $`\mathrm{SL}(2, \mathbb{Z})`, so their images $`B` and
$`T = CB` {uses "lem:modular-alperin-generators"}[] generate $`\mathrm{PSL}(2, \mathbb{Z})`. Both
lie in the image of the homomorphism.
:::

:::theorem "thm:modular-alperin" (parent := "grp:modular") (lean := "ModularGroupFreeProduct_Alperin") (proofColor := "#c7d2fe")
$`\mathrm{PSL}(2, \mathbb{Z}) \cong C_2 * C_3`.
:::

:::proof "thm:modular-alperin"
This proves {uses "def:modular"}[]: the homomorphism $`C_2 * C_3 \to \mathrm{PSL}(2, \mathbb{Z})` is
injective {uses "lem:modular-alperin-injective"}[] and surjective
{uses "lem:modular-alperin-surjective"}[], hence an isomorphism. The ping-pong lemma is stated in
mathlib for the free product of a family of groups, here indexed by the two booleans, which is
identified with the free product $`C_2 * C_3` of two groups.
:::
