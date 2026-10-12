import ExceptionalTimes.SourceSewingPlacement

open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open PolygonSewing EnvironmentVariance CenteredBlocks

/-- The finite source sample contains both actual sites of the first pair. -/
theorem first_pair_sampled {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e h B : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (z : Site)
    (hz : ‖triangularEmbedding z‖≤B) (hBeR : B*e<outerRadius G) :
    x 0∈sample G e he x h ∧ x 0+z∈sample G e he x h := by
  have hm (v : Site) (hv : dist (position e v) (position e (x 0))≤2*outerRadius G) :
      v∈sample G e he x h :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (G.disk_sites_subset e he x _ 0 (center_mem_sourceDiskSites e he (x 0) v _ hv)))
  constructor
  · exact hm _ (by simp only [dist_self]; linarith [outerRadius_pos G])
  · apply hm
    rw [pair_radius,abs_of_pos he]
    nlinarith [outerRadius_pos G]

/-- The source's explicit buffered trial radii place the actual first pair
and every cell meeting the forced square in every trial pocket. -/
theorem first_insertions_in_trial_pockets {q k n : ℕ} (G : SourceSeparatedGeometry q k)
    (e h B M : ℝ) (he : 0<e) (_hh : 0<h) (hB : 128≤B) (hM : 64≤M)
    (hesmall : e<h/4) (hsmall : 4*(M*(B*e))<outerRadius G)
    (x : Fin (k+1)→Site) (z : Site) (hz : ‖triangularEmbedding z‖≤B)
    (radii : Fin n→ℝ) (L : ℝ) (hr : ∀i,0<radii i) (hL : 1≤L)
    (hbuffer : ∀i,64*(M*(B*e)+h)<radii i/L)
    (A : AnnularSupports (sample G e he x h) e (x 0) n radii L) :
    (∀i,x 0∈(A.layout hr hL i).pocket) ∧
    (∀i,x 0+z∈(A.layout hr hL i).pocket) ∧
    (∀i,sourceSquareSites e he (x 0) h⊆(A.layout hr hL i).pocket) := by
  have hBe : 0<B*e := mul_pos (by linarith) he
  have hMB : 0<M*(B*e) := mul_pos (by linarith) hBe
  have hBeR : B*e<outerRadius G := by nlinarith
  have hs := first_pair_sampled G e h B he x z hz hBeR
  refine ⟨?_,?_,?_⟩
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hs.1,?_⟩
    rw [dist_self]
    linarith [hbuffer i]
  · intro i
    apply Finset.mem_filter.mpr
    refine ⟨hs.2,?_⟩
    rw [pair_radius,abs_of_pos he]
    have hez : e*‖triangularEmbedding z‖≤B*e := by nlinarith
    have hbm : B*e≤M*(B*e) := by nlinarith
    linarith [hbuffer i]
  · intro i v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_right _ hv,?_⟩
    have hrad := sourceSquareSites_radius e he (x 0) v h hv
    linarith [hbuffer i]

/-- Actual annular supports and probe agreement regions belong to their
respective independent fair-source coordinate disks. -/
theorem trial_coordinates {q k n : ℕ} (G : SourceSeparatedGeometry q k)
    (e h : ℝ) (he : 0<e) (x : Fin (k+1)→Site)
    (radii : Fin n→ℝ) (L : ℝ) (hr : ∀i,0<radii i) (hL : 1≤L)
    (houter : ∀i,L*radii i<outerRadius G)
    (A : AnnularSupports (sample G e he x h) e (x 0) n radii L) :
    ∀i (v : ↥(sample G e he x h)),(v : Site)∈(A.layout hr hL i).support→
      v∈sourceCoordinates G e x _ none := by
  intro i v hv
  change dist (position e v) (position e (x 0))≤2*outerRadius G
  linarith [A.upper i v hv,houter i,outerRadius_pos G]

theorem probe_coordinates {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (x : Fin (k+1)→Site) (Λ : Finset Site) (i : Option (Fin k))
    (P : Probe) (hmesh : P.mesh=e) (hcenter : P.center=x (insertionIndex i))
    (houter : P.outerRadius=outerRadius G) :
    ∀v : ↥Λ,(v : Site)∈P.region→v∈sourceCoordinates G e x Λ i := by
  intro v hv
  simpa only [sourceCoordinates,Set.mem_ofPred_eq,Probe.radius,hmesh,hcenter,houter] using hv.2

#print axioms first_insertions_in_trial_pockets
#print axioms trial_coordinates
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization


