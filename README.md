# Improved sum–difference inequalities in abelian groups

Logan J. Kleinwaks

For all finite sets $X,Y$ of an abelian group, we prove

$$
|X-Y|\\le |X+Y|^{\\lambda\_\\infty},\\qquad
\\lambda\_\\infty=\\frac{9451e-3286}{5378e+787}=1.454277448906\\ldots.
$$

A universal two-set exponent $\\lambda$ over the integers implies
$C\_{3a}\\le 2-1/\\lambda$, where $C_{3a}$ is the Gyarmati--Hennecart--Ruzsa constant defined in the [Optimization Constants in Mathematics repository](https://teorth.github.io/optimizationproblems/constants/3a.html). Consequently,

$$
C\_{3a}\\le\\frac{13524e-7359}{9451e-3286}=1.312373302115\\ldots.
$$

This improves on the classical exponents $\\lambda\\le \frac{3}{2}$ and $C_{3a}\\le \frac{4}{3}$.

For details, see the [proof paper](paper/sum-difference.pdf) or its [LaTeX source](paper/sum-difference.tex).
The proof paper includes a correspondence with Lean declarations.

## Reference environment and verification

* Lean: `leanprover/lean4:v4.28.0`
* Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
* The remaining dependencies are pinned in `lake-manifest.json`.

Install Lean's [elan toolchain manager](https://github.com/leanprover/elan).
From a clean checkout, run:

```sh
lake env lean --version
lake exe cache get
lake build
```

The toolchain file selects the required Lean version. Keep the committed
manifest; do not run `lake update` when reproducing this reference environment.
The build checks all twenty proof modules. No certificate generator, search
program, unpublished file, or external certificate data is needed.

For a direct statement and axiom inspection, put the following in a temporary
file outside this repository and run `lake env lean /absolute/path/check.lean`:

```lean
import SumDifference.ThetaClosedFormBound
#print SumsDifferences.Admissible
#print SumsDifferences.theta
#print SumsDifferences.pairCeilingExponents
#print SumsDifferences.lamSup
#check SumsDifferences.pair\_ceiling\_entropic
#check SumsDifferences.theta\_le\_of\_pair\_ceiling
#check SumsDifferences.theta\_le\_two\_sub\_inv\_lamSup
#check SumsDifferences.lamSup\_le\_closed\_form
#check SumsDifferences.theta\_le\_closed\_form
#check SumsDifferences.MultiScale.card\_sub\_pow\_le\_multiscale
#print axioms SumsDifferences.pair\_ceiling\_entropic
#print axioms SumsDifferences.theta\_le\_of\_pair\_ceiling
#print axioms SumsDifferences.theta\_le\_two\_sub\_inv\_lamSup
#print axioms SumsDifferences.lamSup\_le\_closed\_form
#print axioms SumsDifferences.theta\_le\_closed\_form
#print axioms SumsDifferences.MultiScale.card\_sub\_pow\_le\_multiscale
```

The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
`lamSup` is the infimum of the universal integer pair exponents, denoted
$\\lambda\_\*$ in the paper; its historical Lean name does not change this definition.

To compile the manuscript with a current TeX distribution:

```sh
cd paper
latexmk -pdf sum-difference.tex
```

## Proof modules

The local transitive import closure of `ThetaClosedFormBound` consists of
exactly these twenty files under `SumDifference/`:

|Modules|Content|
|-|-|
|`ThetaDefs`, `ThetaLocalization`, `ThetaMultiScaleCore`|Admissibility, packing, localisation, multiscale transfer|
|`FinEntropy`, `JointEntropy`, `CondEntropy`, `EntropyEquality`, `EntropyCompute`, `ProductLaw`|Finite probability laws and entropy|
|`EntropySumsetCalculus`, `CoupledEntropyCore`|Independent sums, representative coupling, entropy grid|
|`LinearFormsEntropy`, `LinearFormsNormalForm`, `LinearFormsPairs`|Integer linear forms and certified entropy identifications|
|`CopyLemma`, `MatusInequality`, `CompanionInequality`|Conditional copies and the two known non-Shannon families|
|`ThetaTwoCopyLemma`|Exact two-copy certificate|
|`ThetaGridClosedForm`|Integral weights and limiting array certificate|
|`ThetaClosedFormBound`|Symmetrisation and assembly of the headline bounds|

The mathematical namespace is `SumsDifferences`. The import prefix
`SumDifference` identifies the standalone package. Appendix A of the paper maps
its statements to the corresponding declarations.

## Authorship and AI use

Logan J. Kleinwaks is the author and responsible maintainer. Aristotle
(Harmonic) performed the mathematical formalisation and its simplification
under the author's instructions. Aristotle, GPT-6 Astra, and GPT-5.6 Sol
contributed to research and proof derivation. The author wrote the research-loop
instructions; GPT-6 Astra and GPT-5.6 Sol generated additional research
instructions. Aristotle wrote the initial paper under the author's instructions.
GPT-6 Astra revised the paper under the author's instructions and prepared the
publication packaging. The manuscript records the author's final revision and
responsibility for its claims.

## Citation and licence

See `CITATION.cff`. This repository snapshot is distributed under Apache-2.0;
see `LICENSE`. Cited works and fetched dependencies retain their own licences.

