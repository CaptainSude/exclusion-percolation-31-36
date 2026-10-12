# Literature inputs

[Proof guide](proof-guide.md) · [Paper](../paper/nearest-neighbor-31-36.pdf) · [Main theorem](../ExceptionalTimes/PublishedNearestNeighborDimension.lean#L17)

The table follows the 24 named inputs in the main theorem. Its links open the exact Lean definitions; the source column distinguishes numbered results from the geometric or finite-mesh specializations used in this proof. The ordinary annular one-arm exponent is also required to be positive.

**Formalization note.** The cited results and the specializations recorded here are supplied as explicit hypotheses in Lean. The new local-clock estimates, signed pair comparison, forest bounds, integrated coefficient limits, semigroup transfer and exceptional-time lower-bound argument are proved in the development.

| # | Exact Lean input | Source and scope |
| --- | --- | --- |
| 1 | [PositivePoissonMarks](../ExceptionalTimes/PublishedPoissonConstruction.lean#L33) | [Last–Penrose][LP], Definition 3.1, Theorem 3.6 and Proposition 6.9: positive-rate Poisson marks. |
| 2 | [NormalizedGraphicalRegularity](../ExceptionalTimes/PublishedPoissonConstruction.lean#L37) | [Garban–Vanneuville][GV], Appendix A: no incident ties and finite backward traces for normalized summable rates. |
| 3 | [NormalizedDimensionUpper](../ExceptionalTimes/PublishedExclusionUpper.lean#L24) | [Garban–Vanneuville][GV], Proposition 3.3: the exclusion upper bound $31/36$. The rate-one time change is proved internally. |
| 4 | [SchrammSteifCapacity](../ExceptionalTimes/PublishedCapacity.lean#L26) | [Schramm–Steif][SS], Lemma 6.2, p. 650: the decreasing compact-set capacity criterion. |
| 5 | [PlaneClusterBoundaryCircuit](../ExceptionalTimes/PlaneBoundaryInput.lean#L24) | [Grimmett][Grimmett], §5.5: finite-cluster external boundary, stated with its actual planar enclosure. |
| 6 | [PublishedPolygonCrossingOrder](../ExceptionalTimes/PlaneJordanOrder.lean#L33) | [Diestel][Diestel], §4.1, and [OAI §2][OAI2]: the Jordan separation and crossing-order specialization for actual planar curves. |
| 7 | [PublishedAnnularCrosscutOrder](../ExceptionalTimes/AnnularCrosscutOrder.lean#L30) | [Diestel][Diestel], §4.1, and [OAI §2][OAI2]: preservation of cyclic order by disjoint proper annular crosscuts. |
| 8 | [PublishedCriticalRSW](../ExceptionalTimes/NolinCorridor.lean#L78) | [Nolin][Nolin], §§2.3 and 4: critical axial-rectangle crossings with the source endpoint convention. |
| 9 | [PublishedAnnularOneArmUpper](../ExceptionalTimes/NolinAnnular.lean#L76) | [Nolin][Nolin], ordinary critical RSW/arm estimates; [OAI §2][OAI2], Lemma 2.1: polynomial one-arm decay in buffered annuli. |
| 10 | [ClassicalFiniteEfronStein](../ExceptionalTimes/CanonicalEnergyFromProbeDecay.lean#L47) | [Boucheron–Bousquet–Lugosi–Massart][BBLM], Proposition 1, §2.2: finite independent-coordinate variance inequality. |
| 11 | [PublishedOriginQuasiMultiplicativity](../ExceptionalTimes/OriginOneArmInputs.lean#L80) | [Nolin][Nolin], Propositions 15–16: one-arm extension and quasi-multiplicativity, with fixed endpoint/shape adjustments. |
| 12 | [PublishedOriginOneArmExponent](../ExceptionalTimes/OriginOneArmInputs.lean#L88) | [Lawler–Schramm–Werner][LSW], Theorem 1.1: exponent $5/48$, used with an arbitrary positive exponent loss. |
| 13 | [PublishedIndependentLocalAnnulusMixing](../ExceptionalTimes/LocalAnnulusInput.lean#L28) | [Garban–Holden–Sepúlveda–Sun][GHSS], Theorems 1.3(i), 1.4(i), Remark 1.5 at $\gamma=0$, combined with [GPS][GPS] static arm convergence and ordinary pivotal/four-arm comparison. This is independent site-refresh mixing at the local clock. |
| 14 | [PublishedInvarianceOfDomain](../ExceptionalTimes/InvarianceOfDomainInput.lean#L19) | [Hatcher][Hatcher], Theorem 2B.3: invariance of domain. |
| 15 | [PublishedHexQuadApproximation](../ExceptionalTimes/StaticHexApproximation.lean#L58) | [Garban–Pete–Schramm][GPS], Lemma 2.9 and Corollary 2.10, with a dense quad family: finite Boolean-word approximation of the static hexagonal arm event. |
| 16 | [PublishedPolygonBulkArms](../ExceptionalTimes/PolygonLocalChange.lean#L183) | [OAI §2][OAI2], Lemma 2.2: bulk local change implies four alternating arms, with explicit closed-cell and buffer conventions. |
| 17 | [PublishedPolygonHalfArms](../ExceptionalTimes/HalfPlaneArms.lean#L162) | [OAI §2][OAI2], Lemma 2.2: the corresponding straight-side three-arm implication, away from corners and other sides. |
| 18 | [PublishedCircularArmInputs](../ExceptionalTimes/CircularStaticProfile.lean#L58) | [Nolin][Nolin], §§2.3 and 4, and [Smirnov–Werner][SW], Theorem 4; [OAI §2][OAI2], Lemma 2.1: same-mesh four-arm comparison, lower powers and quasi-multiplicativity. One may take the lower exponent $g=3/2<2$. |
| 19 | [PublishedHalfThreeArmBound](../ExceptionalTimes/HalfPlaneArms.lean#L209) | [Nolin][Nolin], Theorem 23(ii), and [OAI §2][OAI2], Lemma 2.1: ordinary half-plane three-arm upper bound with exponent two. |
| 20 | [PublishedUnitAttachment](../ExceptionalTimes/UnitStaticAttachment.lean#L116) | Ordinary [Nolin][Nolin] RSW, separated-arm extension and quasi-multiplicativity, plus finite energy and planar readout, applied to the checked finite collar and actual $Q_0$. See [the attachment deduction](source-specializations.md#unit-attachment). |
| 21 | [PublishedDyadicFourArmLower](../ExceptionalTimes/UnitClockControl.lean#L26) | [Smirnov–Werner][SW], Theorem 4, and [Nolin][Nolin] v1, Theorem 20: exponent $5/4$ with positive loss and fixed-shape comparison. |
| 22 | [PublishedFixedSquareSeams](../ExceptionalTimes/Source06Specialization.lean#L172) | [OAI §6][OAI6], Lemma **6.5** (join-bit reading), Lemma **6.6** (one-trial comparison), and the following many-trial bound, with [§2][OAI2] buffered-cut comparisons. |
| 23 | [PublishedFixedRadiusFourArmComparison](../ExceptionalTimes/SourceFixedArmComparison.lean#L25) | [OAI §2][OAI2]: ordinary fixed-shape/cut comparison and quasi-multiplicativity, from $64B\varepsilon$ to a fixed outer radius. Its constant is independent of the later sewing tolerance. |
| 24 | [PublishedReferenceSquareLower](../ExceptionalTimes/Source06Specialization.lean#L196) | [OAI §6][OAI6], Lemma 6.1: the actual $Q_0=[-1,1]\times[-1/2,1/2]$ and literal forced square, with [§2][OAI2] square/circle cost comparison. |

## Source conventions worth retaining

- **Sewing:** two independent ordinary fair fields; local, exchange-invariant success events; failure controlled jointly with the necessary arm events by $\epsilon a_\varepsilon(B\varepsilon)a_\varepsilon(h)$. The microscopic enlargement and finite trials precede $h$, and $h$ precedes the mesh limit. The triangular-lattice statement uses established triangular critical inputs, rather than the separate Voronoi Cardy premise.
- **Reference response:** the one-time square influence uses $\delta_1-\delta_0$. Its two-time jump response is half that influence; this identity is checked in [SourcePolygonCalibration](../ExceptionalTimes/SourcePolygonCalibration.lean).
- **Independent mixing:** [GHSS][GHSS] supplies mixing for measurable events, including nonmonotone alternating-arm events. The [local-clock specialization](source-specializations.md#independent-mixing) uses ordinary pivotal comparison and monotonicity of independent-refresh autocorrelations.
- **Pinned numbering:** [OAI's preamble][OAImain] shares one section counter between lemmas and propositions. Thus signed relative replacement is Proposition 6.2, necklace reading is Lemma 6.5, and one-trial comparison is Lemma 6.6.

The [source specializations](source-specializations.md) explain the attachment, static approximation, local mixing and sewing deductions. The original [Lean archive](../verification/nearest-neighbor-31-36-lean.zip) retains the complete source notes and verification record.

## Primary references

- **Last–Penrose:** *Lectures on the Poisson Process* (2017), [author manuscript][LP].
- **Garban–Vanneuville:** *Exceptional times for percolation under exclusion dynamics*, [arXiv:1605.04766v3][GV].
- **Schramm–Steif:** *Quantitative noise sensitivity and exceptional times for percolation*, Annals of Mathematics 171 (2010), 619–672, [published text][SS].
- **Grimmett:** *Probability on Graphs*, [author's 2012 revision][Grimmett].
- **Diestel:** *Graph Theory*, fifth edition (2017), [Chapter 4 preview][Diestel].
- **Hatcher:** *Algebraic Topology* (2002), [Chapter 2][Hatcher].
- **Nolin:** *Near-critical percolation in two dimensions*, [arXiv:0711.4948v1][Nolin]. Numbered references here use v1.
- **Boucheron–Bousquet–Lugosi–Massart:** *Moment inequalities for functions of independent random variables*, [arXiv:math/0503651][BBLM].
- **Lawler–Schramm–Werner:** *One-arm exponent for critical 2D percolation*, [arXiv:math/0108211][LSW].
- **Smirnov–Werner:** *Critical exponents for two-dimensional percolation*, [arXiv:math/0109120v2][SW].
- **Garban–Pete–Schramm:** *Pivotal, cluster and interface measures for critical planar percolation*, [arXiv:1008.1378v5][GPS].
- **Garban–Holden–Sepúlveda–Sun:** *Liouville dynamical percolation*, [arXiv:1905.06940v2][GHSS].
- **OpenAI:** *From critical crossings to quenched near-critical universality in Voronoi percolation*, 5 October 2026; [Section 2][OAI2], [Section 6][OAI6], [main source][OAImain], pinned at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

[LP]: https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf
[GV]: https://arxiv.org/pdf/1605.04766v3
[SS]: https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n2-p01-p.pdf
[Grimmett]: https://www.statslab.cam.ac.uk/~grg/books/USpgs-rev3.pdf
[Diestel]: https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch4.pdf
[Hatcher]: https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf
[Nolin]: https://arxiv.org/abs/0711.4948v1
[BBLM]: https://arxiv.org/abs/math/0503651
[LSW]: https://arxiv.org/abs/math/0108211
[SW]: https://arxiv.org/abs/math/0109120v2
[GPS]: https://arxiv.org/abs/1008.1378v5
[GHSS]: https://arxiv.org/abs/1905.06940v2
[OAI2]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/build/sections/02-inputs.tex
[OAI6]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/build/sections/06-sewing.tex
[OAImain]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/build/paper.tex
