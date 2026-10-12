# Source specializations

[Literature index](literature.md) · [Proof guide](proof-guide.md) · [Paper](../paper/nearest-neighbor-31-36.pdf)

These deductions put the cited results into the event and clock conventions used by the proof. Write $\varepsilon=2^{-n}$ for the mesh, $\alpha_{4,\varepsilon}(r,R)$ for the ordinary alternating four-arm probability with buffered circular cuts, and $a_\varepsilon(r)=\alpha_{4,\varepsilon}(r,1)$. All probabilities compared at a given step use the same mesh. The [literature index](literature.md) links each formulation to its Lean definition.

## Unit attachment

Take $Q_0=[-1,1]\times[-1/2,1/2]$ with its vertical sides as terminals, and a horizontal neighboring pair anchored at a lattice site in the fixed bulk rectangle $[-1/4,1/4]\times[-1/8,1/8]$. Fix $B\ge128$ before letting the mesh decrease.

Arm separation and extension, [Nolin, Propositions 15–16][Nolin], put four alternating arms in separated landing patches at radii comparable to $B\varepsilon$ and a fixed positive radius. Disjoint RSW corridors attach the two black arms to the left and right sides of $Q_0$, and the white arms to its other two sides. The bulk margin gives uniform positive corridor widths.

At the inner end, a fixed finite collar connects to the explicit radius-two necklace in [UnitGadgetNecklace](../ExceptionalTimes/UnitGadgetNecklace.lean). Prescribe the collar colors, leaving the pair's two bits free. Finite energy costs a positive constant depending on the fixed layout and $B$. The two white connections prevent a black bypass, so Jordan separation makes the rectangle crossing equal the necklace's inner join for every assignment of the two free bits. The checked local pattern makes this join the first free bit.

Quasi-multiplicativity and the fixed-shape comparisons in [OAI, §2][OAI2] therefore give

$$
\mathbb P(\text{attachment})\ge c\,a_\varepsilon(B\varepsilon),
$$

uniformly over the stated bulk locations and sufficiently fine meshes. For this projection truth table, the exact probability that either one canonical pair update or one endpoint-refresh update changes the crossing is $1/4$. Nonnegativity on the remaining configurations yields $S_C,S_M\ge(c/4)a_\varepsilon(B\varepsilon)$. These response calculations and restriction to the finite sample are proved in [UnitStaticAttachment](../ExceptionalTimes/UnitStaticAttachment.lean).

## Finite-cylinder approximation

Fix an annulus aspect $M\ge2$ and an error $\delta>0$. [Garban–Pete–Schramm, Lemma 2.9 and Corollary 2.10][GPS] give measurability and convergence of alternating-arm events for the fixed polygonal annulus. A countable dense family of quad-crossing coordinates generates the quad-crossing state space. Consequently, its arm-event indicator can be approximated in probability by a Boolean function of finitely many such coordinates. Approximate these quads by affine images of dyadic grid polygons under the fixed map $(u,v)\mapsto u+e^{i\pi/3}v$, choosing the boundary perturbations small enough to retain the prescribed error.

Choose that finite family and Boolean word $W$ first. Static convergence then gives a threshold $N$ such that, for every $n\ge N$,

$$
\mathbb P\bigl(A_{4,n}(1,M)\mathbin{\triangle}W_n\bigr)\le\delta.
$$

The finite iid sample contains the annulus and every chosen polygon support, so this is the same probability as in the full-plane fair field. Loop erasure and first/last-contact trimming identify the simple-path and cyclic-order conventions. See [StaticHexApproximation](../ExceptionalTimes/StaticHexApproximation.lean). Under any two-time coupling with these static marginals, replacing the arm event at both times costs at most $2\delta$; [FiniteEventTransfer](../ExceptionalTimes/FiniteEventTransfer.lean) proves that passage.

## Independent mixing

[Garban–Holden–Sepúlveda–Sun, Theorems 1.3(i), 1.4(i) and Remark 1.5][GHSS], at $\gamma=0$, give convergence to ordinary dynamical percolation and full mixing of its scaling limit. This applies to measurable alternating-arm events, including their nonmonotone color requirement. For each fixed $M$, the limiting two-time probability tends to the square of the static arm probability as time increases. The four-arm exponent with a fixed loss gives a uniform bound $C M^{-9/4}$ for that square. Finite-cylinder approximation and finite-dimensional convergence transfer the bound to sufficiently fine meshes.

The local clock agrees with this scale up to a fixed lower bound on elapsed time. If $p_0,p_1$ are the pivotal probabilities of the two central sites for $Q_0$, the exact endpoint-refresh calculation gives

$$
S_M(\varepsilon)=\frac{p_0+p_1}{4},\qquad
0<S_M(\varepsilon)\le C\alpha_{4,\varepsilon}(\varepsilon,1).
$$

Thus the actual independent site-refresh time used in the proof satisfies

$$
t_\varepsilon(T)=\frac{T\varepsilon^2}{2S_M(\varepsilon)}
\ge cT\frac{\varepsilon^2}{\alpha_{4,\varepsilon}(\varepsilon,1)}.
$$

For a finite Boolean event $f$, independent refresh has
$\mathbb E[f(\omega_0)f(\omega_t)]=\sum_S\widehat f(S)^2e^{-t|S|}$.
Its same-event probability is therefore nonincreasing in time. The preceding comparison suffices without a limit for the calibration ratio. We obtain precisely: there is $C$ such that, for every fixed $M\ge2$ and $\delta>0$, there exist $T>0$ and $N$ with

$$
\mathbb P\bigl(A_{4,n}(1,M;0)\cap A_{4,n}(1,M;t_{\varepsilon}(T))\bigr)
\le C M^{-9/4}+\delta\qquad(n\ge N).
$$

Here $T$ and $N$ may depend on $M$ and $\delta$. The factor $1/2$ in $t_\varepsilon(T)$ comes from the endpoint choice in the pair update. See [LocalAnnulusInput](../ExceptionalTimes/LocalAnnulusInput.lean) and [CalibratedAnnulusMixing](../ExceptionalTimes/CalibratedAnnulusMixing.lean).

## Arm exponents and buffered cuts

[Smirnov–Werner, Theorem 4][SW], and [Nolin v1, Theorem 20 and Propositions 15–16][Nolin], supply the four-arm exponent $5/4$, separation and quasi-multiplicativity. Iterating a sufficiently large fixed scale ratio gives uniform two-scale power inequalities with a strict exponent margin; the finitely many remaining lattice scales alter only the constants. In particular, one may use the lower power $c(r/R)^{3/2}$, and, for every $\eta>0$,

$$
a_\varepsilon(B\varepsilon)\ge c_\eta\varepsilon^{5/4+\eta}
$$

for sufficiently fine dyadic meshes. Together with attachment this gives $\varepsilon^2/S_A\le C_\eta\varepsilon^{3/4-\eta}$ for $0<\eta<3/4$. [Lawler–Schramm–Werner, Theorem 1.1][LSW] gives the one-arm exponent $5/48$ with the analogous positive loss. The half-plane three-arm upper bound is [Nolin v1, Theorem 23(ii)][Nolin].

[OAI, §2][OAI2] explicitly allows bounded changes of radii and buffered square/circle comparisons. For example, ordinary arms from $64B\varepsilon$ to a fixed $R>0$ have probability at most $C(B,R)a_\varepsilon(B\varepsilon)$. Both $B$ and $R$, and hence this constant, are fixed independently of the later sewing tolerance. All these are same-mesh comparisons. The forest's clipped profile below the microscopic cutoff and above its fixed stop is then defined and controlled in [CircularStaticProfile](../ExceptionalTimes/CircularStaticProfile.lean).

## Relative sewing

Fix finitely many polygon tests and a compact insertion range separated from all tested boundaries and other insertions. In two independent ordinary fair fields, the construction of [OAI, §6][OAI6] supplies annular success events $U_j$. Each event works for all four combinations of source inside and source outside, making it invariant under source exchange and its own inside exchange. **Lemma 6.5** says that success transmits the actual inner necklace's black-run join bit, with arbitrary fixed histories at the other insertion regions.

Let $N=\bigcap_j U_j^c$. Trim the formal arms to an inner graph cut slightly farther out and an outer graph cut slightly farther in. Simplicity, disjointness and alternating cyclic order are preserved, so their necessary event is contained in the source event $E$. **Lemma 6.6** compares failure with success at one specified trial. Summing over the disjoint events of exactly one successful trial gives the source's relative many-trial bound

$$
\limsup_{\varepsilon\downarrow0}
\frac{\mathbb P(E\cap N)}
 {A_\varepsilon(B\varepsilon,1)A_\varepsilon(h,1)}
\le\rho+\frac{C_*C(M,R)}{m}.
$$

Here $A_\varepsilon$ uses the source's square-annulus convention, $M$ is the microscopic enlargement, and $m$ is the number of trials. First fix the desired error $\epsilon>0$, absorbing the fixed square/circle comparison constants into the tolerance. Choose $M$ as in the source's cutoff step. Then fix the sleeve and extension ratios and the trim tolerance so that the disqualification term $\rho$ is sufficiently small. These choices fix $C_*$; now choose $m$ large enough to control $C_*C(M,R)/m$. Place the buffered trials, take $h$ below their inner boundaries, and finally take the mesh sufficiently small. This yields, uniformly on the fixed compact insertion range,

$$
\mathbb P\bigl(N\cap A_4^{\mathrm{mic}}(\omega)
                       \cap A_4^{\mathrm{sq}}(\eta)\bigr)
\le\epsilon\,a_\varepsilon(B\varepsilon)a_\varepsilon(h),
$$

where $\omega,\eta$ are independent fair fields. This is a joint failure-and-arms estimate with one microscopic and one fixed-square factor. The remaining insertion probes have fixed cutoffs independent of $\epsilon$.

For the same literal reference rectangle and forced square, **Lemma 6.1** gives the one-time influence
$D^\Delta_\varepsilon(h)\ge c\,a_\varepsilon(h)$.
The two-time square jump response is exactly $D^\Delta_\varepsilon(h)/2$, as proved in [SourcePolygonCalibration](../ExceptionalTimes/SourcePolygonCalibration.lean). The finite sample contains all tested cells and trial supports, preserving the two independent fair-field laws. These conventions are collected in [Source06Specialization](../ExceptionalTimes/Source06Specialization.lean); the signed pair-history comparison and common-square cancellation follow in the [proof guide](proof-guide.md).

[Nolin]: https://arxiv.org/abs/0711.4948v1
[SW]: https://arxiv.org/abs/math/0109120v2
[LSW]: https://arxiv.org/abs/math/0108211
[GPS]: https://arxiv.org/abs/1008.1378v5
[GHSS]: https://arxiv.org/abs/1905.06940v2
[OAI2]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/build/sections/02-inputs.tex
[OAI6]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/From-critical-crossings-to-quenched-near-critical-universality-in-Voronoi-percolation-October-5-2026/build/sections/06-sewing.tex
