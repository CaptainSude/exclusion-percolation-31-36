import ExceptionalTimes.HoleFilling

/-!
# A square-annulus reduction to the classical cluster-boundary theorem

The sole named input below is the shape-independent finite-cluster
enclosing-cycle property of triangular site percolation, as stated in
Grimmett, `Probability on Graphs`, section 5.5 (author's 2012 revision,
pp. 99--100; see also the enclosing-cycle discussion at Figure 3.1).
Its graph separation content is stated explicitly. It is an imported
published topology input, not a proved declaration or an added axiom.

All conditions specific to the actual finite wired square annulus are
proved: the filled cluster contains the hole, failure confines it to the
outer box, its external boundary is white, and that boundary uses only
original annular sites. No probability bound is an input or conclusion.
-/

namespace ExceptionalTimes.WiredBoundary

open HoleFilling

/-- Both components outside the annular vertex set are wired black. -/
def wireBoth (ω : Configuration) (r R : ℕ) : Configuration :=
  fun v => if v ∈ latticeBox r ∨ v ∉ latticeBox R then true else ω v

/-- The actual radial graph event for these two black wired components. -/
def WiredConnection (ω : Configuration) (r R : ℕ) : Prop :=
  OneArm (wireBoth ω r R) (0, 0) R

/-- Graph-theoretic content of surrounding a vertex set: every path from
it far enough towards infinity meets the proposed circuit vertex set. -/
def SeparatesFromInfinity (S C : Set Site) : Prop :=
  ∃ K : Finset Site, S ⊆ (K : Set Site) ∧
    ∀ u ∈ S, ∀ v, v ∉ K → ∀ p : triangularGraph.Walk u v,
      ∃ z ∈ p.support, z ∈ C

/-- Faithful, shape-independent imported cluster-boundary input. It is
strictly a statement about a finite cluster in the fixed triangular
lattice; square annuli, pivotal cells and arm bounds do not occur in it.
The final clause makes the enclosing meaning of the published external
boundary cycle explicit, instead of accepting a possibly irrelevant cycle.
-/
def FiniteClusterBoundaryCircuit : Prop :=
  ∀ (η : Configuration) (o : Site), η o = true → (BlackCluster η o).Finite →
    ∃ v : Site, ∃ c : triangularGraph.Walk v v,
      c.IsCycle ∧
      (∀ z ∈ c.support, z ∈ Necklace.externalBoundary triangularGraph (BlackCluster η o)) ∧
      SeparatesFromInfinity (BlackCluster η o) {z | z ∈ c.support}

theorem separates_mono {S T C : Set Site} (hST : S ⊆ T)
    (h : SeparatesFromInfinity T C) : SeparatesFromInfinity S C := by
  obtain ⟨K, hK, hcut⟩ := h
  exact ⟨K, hST.trans hK, fun u hu => hcut u (hST hu)⟩

@[simp] theorem wireBoth_inside (ω : Configuration) (r R : ℕ) {z : Site}
    (hz : z ∈ latticeBox r) : wireBoth ω r R z = true := by
  simp [wireBoth, hz]

@[simp] theorem wireBoth_outside (ω : Configuration) (r R : ℕ) {z : Site}
    (hz : z ∉ latticeBox R) : wireBoth ω r R z = true := by
  simp [wireBoth, hz]

theorem fillBox_le_wireBoth (ω : Configuration) (r R : ℕ) :
    blackGraph (fillBox ω r) ≤ blackGraph (wireBoth ω r R) := by
  apply blackGraph_mono
  intro z hz
  by_cases hzi : z ∈ latticeBox r
  · exact wireBoth_inside ω r R hzi
  by_cases hzo : z ∉ latticeBox R
  · exact wireBoth_outside ω r R hzo
  · simpa [fillBox, wireBoth, hzi, hzo] using hz

/-- Membership in the filled hole yields actual graph reachability from
the origin, using the lattice paths constructed in HoleFilling. -/
theorem hole_subset_cluster (ω : Configuration) (r R : ℕ) :
    (latticeBox r : Set Site) ⊆ BlackCluster (wireBoth ω r R) (0, 0) := by
  intro z hz
  exact ⟨wireBoth_inside ω r R (origin_mem_box r),
    (filled_box_reachable ω r hz).mono (fillBox_le_wireBoth ω r R)⟩

theorem failed_cluster_subset_outer (ω : Configuration) (r R : ℕ)
    (hfail : ¬WiredConnection ω r R) :
    BlackCluster (wireBoth ω r R) (0, 0) ⊆ (latticeBox R : Set Site) := by
  intro z hz
  by_contra hzout
  exact hfail ⟨z, hz, hzout⟩

theorem failed_cluster_finite (ω : Configuration) (r R : ℕ)
    (hfail : ¬WiredConnection ω r R) :
    (BlackCluster (wireBoth ω r R) (0, 0)).Finite :=
  (latticeBox R).finite_toSet.subset (failed_cluster_subset_outer ω r R hfail)

private theorem infinite_cluster_of_ray (η : Configuration) (f : ℕ → Site)
    (hc : ∀ n, η (f n) = true)
    (ha : ∀ n, TriangularAdj (f n) (f (n + 1)))
    (he : ∀ n, f n ∉ latticeBox n) : (BlackCluster η (f 0)).Infinite := by
  have hreach : ∀ n, (blackGraph η).Reachable (f 0) (f n) := by
    intro n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (show (blackGraph η).Adj (f n) (f (n + 1)) from
        ⟨ha n, hc n, hc (n + 1)⟩).reachable
  apply (infinite_iff_escapes_boxes _).2
  intro n
  exact ⟨f n, ⟨hc 0, hreach n⟩, he n⟩

/-- Each actual exterior vertex has an infinite black coordinate ray.
This proves the wired exterior's escape property from the six adjacency
directions, without assuming exterior connectivity or infinitude. -/
theorem exterior_cluster_infinite (ω : Configuration) (r R : ℕ) {v : Site}
    (hv : v ∉ latticeBox R) : (BlackCluster (wireBoth ω r R) v).Infinite := by
  rcases v with ⟨x, y⟩
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hv
  have hc : x < -(R : ℤ) ∨ (R : ℤ) < x ∨ y < -(R : ℤ) ∨ (R : ℤ) < y := by omega
  rcases hc with hx | hx | hy | hy
  · have h := infinite_cluster_of_ray (wireBoth ω r R) (fun n => (x - n, y))
      (by intro n; apply wireBoth_outside; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
      (by intro n; unfold TriangularAdj; omega)
      (by intro n; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
    simpa using h
  · have h := infinite_cluster_of_ray (wireBoth ω r R) (fun n => (x + n, y))
      (by intro n; apply wireBoth_outside; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
      (by intro n; unfold TriangularAdj; omega)
      (by intro n; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
    simpa using h
  · have h := infinite_cluster_of_ray (wireBoth ω r R) (fun n => (x, y - n))
      (by intro n; apply wireBoth_outside; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
      (by intro n; unfold TriangularAdj; omega)
      (by intro n; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
    simpa using h
  · have h := infinite_cluster_of_ray (wireBoth ω r R) (fun n => (x, y + n))
      (by intro n; apply wireBoth_outside; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
      (by intro n; unfold TriangularAdj; omega)
      (by intro n; simp only [latticeBox, Finset.product_eq_sprod,
          Finset.mem_product, Finset.mem_Icc]; omega)
    simpa using h

theorem wired_connection_cluster_infinite (ω : Configuration) (r R : ℕ)
    (h : WiredConnection ω r R) : (BlackCluster (wireBoth ω r R) (0, 0)).Infinite := by
  obtain ⟨v, hv, hvout⟩ := h
  apply (exterior_cluster_infinite ω r R hvout).mono
  intro z hz
  exact ⟨hv.1, hv.2.trans hz.2⟩

private theorem black_walk_colors (η : Configuration) {u v : Site}
    (p : (blackGraph η).Walk u v) (hu : η u = true) :
    ∀ z ∈ p.support, η z = true := by
  induction p with
  | nil => simpa using hu
  | @cons a b c hab p ih =>
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · simpa [hz] using hu
      · exact ih hab.2.2 z hz

theorem blackCluster_externalBoundary_white (η : Configuration) (o : Site)
    {z : Site} (hz : z ∈ Necklace.externalBoundary triangularGraph (BlackCluster η o)) :
    η z = false := by
  obtain ⟨x, hx, hxz⟩ := hz.2
  have hxcol : η x = true := by
    exact Necklace.reachable_has_color triangularGraph η true hx.1 hx.2
  cases hc : η z with
  | false => rfl
  | true =>
      exact (hz.1 ⟨hx.1, hx.2.trans (show (blackGraph η).Adj x z from
        ⟨hxz, hxcol, hc⟩).reachable⟩).elim

/-- Every vertex on the actual external boundary is an original white
annular site. Wiring forbids it from lying in either boundary component.
-/
theorem wired_externalBoundary_in_annulus (ω : Configuration) (r R : ℕ)
    {z : Site}
    (hz : z ∈ Necklace.externalBoundary triangularGraph
      (BlackCluster (wireBoth ω r R) (0, 0))) :
    z ∉ latticeBox r ∧ z ∈ latticeBox R ∧ ω z = false := by
  have hc := blackCluster_externalBoundary_white (wireBoth ω r R) (0, 0) hz
  have hzi : z ∉ latticeBox r := by
    intro hzi
    have := wireBoth_inside ω r R hzi
    simp only [hc, Bool.false_eq_true] at this
  have hzo : z ∈ latticeBox R := by
    by_contra hzo
    have := wireBoth_outside ω r R hzo
    simp only [hc, Bool.false_eq_true] at this
  refine ⟨hzi, hzo, ?_⟩
  simpa [wireBoth, hzi, hzo] using hc

/-- The essential white annular circuit follows from the literal
shape-independent published cluster-boundary input. All its model and
annulus hypotheses are discharged, including enclosure of the whole hole.
This is a conditional-on-published-input theorem, not an unconditional
formal proof of that input. -/
theorem failed_wired_connection_white_circuit
    (boundaryInput : FiniteClusterBoundaryCircuit)
    (ω : Configuration) (r R : ℕ) (hfail : ¬WiredConnection ω r R) :
    ∃ v : Site, ∃ c : triangularGraph.Walk v v,
      c.IsCycle ∧
      (∀ z ∈ c.support, z ∉ latticeBox r ∧ z ∈ latticeBox R ∧ ω z = false) ∧
      SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ c.support} := by
  obtain ⟨v, c, hc, hboundary, hsep⟩ := boundaryInput (wireBoth ω r R) (0, 0)
    (wireBoth_inside ω r R (origin_mem_box r)) (failed_cluster_finite ω r R hfail)
  exact ⟨v, c, hc, fun z hz => wired_externalBoundary_in_annulus ω r R (hboundary z hz),
    separates_mono (hole_subset_cluster ω r R) hsep⟩

/-- The converse direction needs no planar input: a white circuit with
the explicit surrounding property blocks every wired radial connection.
The proof uses the actual infinite exterior rays above. -/
theorem white_surrounding_set_blocks_wired_connection
    (ω : Configuration) (r R : ℕ) (C : Set Site)
    (hC : ∀ z ∈ C, z ∉ latticeBox r ∧ z ∈ latticeBox R ∧ ω z = false)
    (hsep : SeparatesFromInfinity (latticeBox r : Set Site) C) :
    ¬WiredConnection ω r R := by
  intro h
  obtain ⟨K, _, hcut⟩ := hsep
  obtain ⟨v, hv, hvK⟩ := ((wired_connection_cluster_infinite ω r R h).sdiff
    K.finite_toSet).nonempty
  obtain ⟨p⟩ := hv.2
  have hforget : blackGraph (wireBoth ω r R) ≤ triangularGraph := fun _ _ h => h.1
  obtain ⟨z, hz, hzC⟩ := hcut (0, 0) (origin_mem_box r) v hvK (p.mapLe hforget)
  have hc := black_walk_colors (wireBoth ω r R) p hv.1 z (by simpa using hz)
  obtain ⟨hzi, hzo, hwhite⟩ := hC z hzC
  simp only [wireBoth, hzi, hzo, not_true_eq_false, or_self, ↓reduceIte, hwhite,
    Bool.false_eq_true] at hc

/-- The actual wired annular duality, reduced to the shape-independent
published finite-cluster boundary theorem. Both directions and the
annular location of the surrounding simple cycle are proved. -/
theorem wired_annular_duality (boundaryInput : FiniteClusterBoundaryCircuit)
    (ω : Configuration) (r R : ℕ) :
    (¬WiredConnection ω r R) ↔
      ∃ v : Site, ∃ c : triangularGraph.Walk v v,
        c.IsCycle ∧
        (∀ z ∈ c.support, z ∉ latticeBox r ∧ z ∈ latticeBox R ∧ ω z = false) ∧
        SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ c.support} := by
  constructor
  · exact failed_wired_connection_white_circuit boundaryInput ω r R
  · rintro ⟨v, c, _, hc, hsep⟩
    exact white_surrounding_set_blocks_wired_connection ω r R _ hc hsep

#print axioms hole_subset_cluster
#print axioms failed_cluster_finite
#print axioms wired_externalBoundary_in_annulus
#print axioms failed_wired_connection_white_circuit
#print axioms exterior_cluster_infinite
#print axioms wired_annular_duality

end ExceptionalTimes.WiredBoundary
