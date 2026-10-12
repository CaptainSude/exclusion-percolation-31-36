# Proof guide

[Read the paper](../paper/nearest-neighbor-31-36.pdf) · [Literature inputs](literature.md) · [Main Lean theorem](../ExceptionalTimes/PublishedNearestNeighborDimension.lean#L17)

Starting from iid fair site colors on the triangular lattice, put an independent rate-one Poisson clock on each unordered nearest-neighbor edge and swap its endpoint colors at each ring. The main theorem proves, on one event of probability one,

$$
\dim_{\mathrm H}\{t\in(a,b):\omega_t\text{ has an infinite black cluster}\}=31/36
\qquad(0\le a<b<\infty).
$$

The Lean entry point is `ExceptionalTimes.PublishedNearestNeighborDimension.exists_realization_dimension`. It constructs the graphical realization and establishes the simultaneous statement for every time interval.

## Read the proof in this order

| Step | Mathematical content | Main modules |
| --- | --- | --- |
| 1. Pair laws and local clocks | Compare a rate-one uniform update preserving the pair's black count (`canonical`) with a rate-one update refreshing a uniformly chosen endpoint (`refresh`). A central reference response fixes each time scale. | [LocalDimerCalibration](../ExceptionalTimes/LocalDimerCalibration.lean), [LocalClockControl](../ExceptionalTimes/LocalClockControl.lean), [EffectiveDimerInsertion](../ExceptionalTimes/EffectiveDimerInsertion.lean) |
| 2. Signed sewing | Ordinary necklace readout gives the pair/square identity. Comparing both pair rules through the same fixed square cancels its response; reindexing and telescoping give uniform normalized full-degree comparison on separated tuples. | [SourcePolygonReading](../ExceptionalTimes/SourcePolygonReading.lean), [SourceDirectSewing](../ExceptionalTimes/SourceDirectSewing.lean), [SourceMicroscopicLimit](../ExceptionalTimes/SourceMicroscopicLimit.lean), [SourceFullNormalizedDyadic](../ExceptionalTimes/SourceFullNormalizedDyadic.lean) |
| 3. Forest control and integration | Annular arm estimates bound centered kernels. Higher moments make collision and boundary-strip contributions small; the ordered-tuple formula integrates the sewing limit. Optimized stopping radii give a common bound for every degree. | [DyadicForestGeometry](../ExceptionalTimes/DyadicForestGeometry.lean), [OrderedDegreeLimit](../ExceptionalTimes/OrderedDegreeLimit.lean), [DyadicDegreeConvergence](../ExceptionalTimes/DyadicDegreeConvergence.lean#L63), [DyadicForestMass](../ExceptionalTimes/DyadicForestMass.lean#L34) |
| 4. Actual dynamics and crossing words | Centered remainder estimates pass from first-order coefficients to the actual pair semigroups. Summable domination permits the full series limit. | [ActualProductTransfer](../ExceptionalTimes/ActualProductTransfer.lean), [WordProductBridge](../ExceptionalTimes/WordProductBridge.lean), [DyadicWordForestCertificate](../ExceptionalTimes/DyadicWordForestCertificate.lean#L72), [WordForestCertificate](../ExceptionalTimes/WordForestCertificate.lean) |
| 5. Annular mixing and energy | Static finite-word approximation transfers independent dynamical mixing to the two matching phases. Disjoint annuli and local pivotal probes yield the energy estimate. | [QuadAnnulusTransfer](../ExceptionalTimes/QuadAnnulusTransfer.lean#L77), [CalibratedAnnulusMixing](../ExceptionalTimes/CalibratedAnnulusMixing.lean), [DyadicFixedAspectEnergy](../ExceptionalTimes/DyadicFixedAspectEnergy.lean), [CanonicalEnergyFromProbeDecay](../ExceptionalTimes/CanonicalEnergyFromProbeDecay.lean) |
| 6. Exceptional times | Capacity, the graphical construction and spatial ergodicity give the lower bound in every window. The published exclusion upper bound completes the equality. | [FiniteEnergyDimension](../ExceptionalTimes/FiniteEnergyDimension.lean), [SingleDisplacementDimension](../ExceptionalTimes/SingleDisplacementDimension.lean), [DyadicDimension](../ExceptionalTimes/DyadicDimension.lean), [PublishedNearestNeighborDimension](../ExceptionalTimes/PublishedNearestNeighborDimension.lean) |

## Three formulas to keep in view

At mesh $\varepsilon=2^{-n}$, let $S_A(\varepsilon)$ be the probability that one update of rule $A\in\{C,M\}$ on the central horizontal pair changes the crossing of $Q_0=[-1,1]\times[-1/2,1/2]$. Then

$$
J_A=\frac{S_A}{2\varepsilon^2},\qquad
u_A=\frac{\varepsilon^2}{S_A}=\frac1{2J_A}.
$$

These are **local** responses. Canonical pair updates at rate one swap with probability one half. Refresh pair updates at rate one give independent site refresh at rate one half, so pair time $Tu_M$ is site-refresh time $Tu_M/2$.

For degree $k$, write $K_{A,k}(\mathbf x)$ for the averaged full signed overwrite kernel. Its normalized coefficient is

$$
c_{A,k}(\varepsilon)
=\frac{\varepsilon^{2k}}{k!}
  \sum_{\mathbf x\ \mathrm{ordered, distinct}}
  \frac{K_{A,k}(\mathbf x)}{S_A(\varepsilon)^k}.
$$

The sum is over matching anchors in the finite cover of the tested quads. The proof establishes $c_{C,k}-c_{M,k}\to0$ for each fixed $k$. The forest envelope bounds arbitrary centered insertion kernels by the product of their total variations, which also controls the nonlinear semigroup remainders. For a common constant $A_0$ and an admissible lower arm exponent $0<g<2$, its normalized degree mass is bounded by

$$
b_0=1,\qquad b_k=A_0^k k^{-(1-g/2)k}\quad(k\ge1),
\qquad \sum_{k\ge0}(2T)^k b_k<\infty.
$$

The resulting crossing-word comparison holds for **both** matchings $(2m+\sigma,n)\leftrightarrow(2m+\sigma+1,n)$, $\sigma=0,1$, every fixed finite family of dyadic grid quads in triangular coordinates, and every Boolean word in their literal closed-cell crossings. Here the coordinate map is $(u,v)\mapsto u+e^{i\pi/3}v$. For each fixed $T>0$, the difference of the two-time probabilities at pair times $Tu_C$ and $Tu_M$ tends to zero.

## Sewing limit order

The source error is the joint failure probability
$\mathbb P(N\cap A_4^{\rm mic}\cap A_4^{\rm sq})\le\epsilon\,a_\varepsilon(B\varepsilon)a_\varepsilon(h)$.
Choose the microscopic enlargement and finite trial list first; then fix the square size $h$ below all trials; then let $\varepsilon\to0$. Finally let $h\to0$. The other insertion cutoffs stay fixed independently of the target error. This mixed microscopic/square normalization is the one used in the common-square cancellation.

## Checking the implementation

The verified snapshot contains 443 Lean source files and audits 8,241 declarations, including 6,231 theorems. Its transitive axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The [literature index](literature.md) links all 24 imported formulations to their definitions and primary sources. Older helper modules may expose intermediate premises; the [final constructor](../ExceptionalTimes/DyadicWordForestCertificate.lean#L72) supplies the forest, integration and coefficient fields used by the main theorem.
