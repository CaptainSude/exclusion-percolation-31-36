import ExceptionalTimes.SourceSewingGeometry

/-! Literal insertion and trial placements on a compact separated family. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open PolygonSewing EnvironmentVariance CenteredBlocks

theorem endpoint_radius_le {k : ℕ} (endpoint : Fin k × Fin 2 ↪ Site)
    (x : Fin (k+1)→Site) (z : Site) (e B : ℝ) (he : 0<e)
    (hz : ‖triangularEmbedding z‖≤B)
    (hfirst : ∀i,endpoint (i,0)=x i.succ)
    (hsecond : ∀i,endpoint (i,1)=x i.succ+z) (i : Fin k) (j : Fin 2) :
    dist (position e (endpoint (i,j))) (position e (x i.succ))≤B*e := by
  fin_cases j
  · change dist (position e (endpoint (i,0))) (position e (x i.succ))≤B*e
    rw [hfirst,dist_self]
    exact mul_nonneg ((norm_nonneg _).trans hz) he.le
  · change dist (position e (endpoint (i,1))) (position e (x i.succ))≤B*e
    rw [hsecond,pair_radius,abs_of_pos he]
    nlinarith

/-- The other probes use the fixed factor 64, independent of the source
failure tolerance and its first-point microscopic factor M. -/
theorem source_other_geometry {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e h B M : ℝ) (he : 0<e) (_hh : 0<h) (hB : 128≤B) (hM : 64≤M)
    (hesmall : e<h/4) (hsmall : 4*(M*(B*e))<outerRadius G)
    (hsquare : 4*(8*h)<outerRadius G)
    (x : Fin (k+1)→Site) (hx : G.Admissible e x) (z : Site)
    (hz : ‖triangularEmbedding z‖≤B)
    (endpoint : Fin k × Fin 2 ↪ Site)
    (hfirst : ∀i,endpoint (i,0)=x i.succ)
    (hsecond : ∀i,endpoint (i,1)=x i.succ+z)
    (mic sq : Probe) (other : Fin k→Probe)
    (hmicmesh : mic.mesh=e) (hmiccenter : mic.center=x 0)
    (hsqmesh : sq.mesh=e) (hsqcenter : sq.center=x 0)
    (hmicouter : mic.outerRadius=outerRadius G) (hsqouter : sq.outerRadius=outerRadius G)
    (hothermesh : ∀i,(other i).mesh=e) (hothercenter : ∀i,(other i).center=x i.succ)
    (hotherinner : ∀i,(other i).innerRadius=64*(B*e))
    (hotherouter : ∀i,(other i).outerRadius=outerRadius G) :
    SourceOtherProbeGeometry endpoint mic sq z (sourceSquareSites e he (x 0) h) other := by
  have hBe : 0<B*e := mul_pos (by linarith) he
  have hBeR : B*e<outerRadius G := by nlinarith
  have hnear := endpoint_radius_le endpoint x z e B he hz hfirst hsecond
  have hpocket : ∀i j,endpoint (i,j)∈(other i).pocket := by
    intro i j
    change (other i).radius _ < (other i).innerRadius/2
    simp only [Probe.radius,hothermesh,hothercenter,hotherinner]
    linarith [hnear i j]
  have hnot (i : Fin k) (j : Fin 2) (a : Fin (k+1)) (hia : i.succ≠a) :
      ¬dist (position e (endpoint (i,j))) (position e (x a))≤2*outerRadius G :=
    near_insertion_not_other_disk G e x hx i.succ a hia _ ((hnear i j).trans_lt hBeR)
  have hzero (i : Fin k) : i.succ≠(0 : Fin (k+1)) := Fin.succ_ne_zero i
  refine ⟨hpocket,?_,?_,?_,?_,?_,?_⟩
  · intro i j hv
    exact hnot i j 0 (hzero i) (by simpa only [Probe.radius,hmicmesh,hmiccenter,hmicouter] using hv.2)
  · intro i j hv
    exact hnot i j 0 (hzero i) (by simpa only [Probe.radius,hsqmesh,hsqcenter,hsqouter] using hv.2)
  · intro j i a hv
    by_cases hij : i=j
    · subst j
      exact pocket_not_region _ (hpocket i a) hv
    · exact hnot i a j.succ (fun heq => hij (Fin.succ_injective _ heq))
        (by simpa only [Probe.radius,hothermesh,hothercenter,hotherouter] using hv.2)
  · intro i hv
    apply near_insertion_not_other_disk G e x hx 0 i.succ (hzero i).symm (x 0)
      (by simpa using outerRadius_pos G)
    simpa only [Probe.radius,hmiccenter,hothermesh,hothercenter,hotherouter] using hv.2
  · intro i hv
    apply near_insertion_not_other_disk G e x hx 0 i.succ (hzero i).symm (x 0+z)
    · rw [pair_radius,abs_of_pos he]
      nlinarith
    · simpa only [Probe.radius,hmiccenter,hothermesh,hothercenter,hotherouter] using hv.2
  · intro i v hv hreg
    apply near_insertion_not_other_disk G e x hx 0 i.succ (hzero i).symm v
    · have hrad := sourceSquareSites_radius e he (x 0) v h hv
      linarith
    · simpa only [Probe.radius,hothermesh,hothercenter,hotherouter] using hreg.2

/-- Every other endpoint misses both the literal circular inside and the
actual annular support of each source trial. -/
theorem other_endpoints_avoid_trials {q k n : ℕ} (G : SourceSeparatedGeometry q k)
    (e h B : ℝ) (he : 0<e) (hBeR : B*e<outerRadius G)
    (x : Fin (k+1)→Site) (hx : G.Admissible e x) (z : Site)
    (hz : ‖triangularEmbedding z‖≤B) (endpoint : Fin k×Fin 2 ↪ Site)
    (hfirst : ∀i,endpoint (i,0)=x i.succ) (hsecond : ∀i,endpoint (i,1)=x i.succ+z)
    (radii : Fin n→ℝ) (L : ℝ) (hr : ∀i,0<radii i) (hL : 1≤L)
    (houter : ∀i,L*radii i<outerRadius G)
    (A : AnnularSupports (sample G e he x h) e (x 0) n radii L) :
    ∀j i a,endpoint (i,a)∉(A.layout hr hL j).inside ∧ endpoint (i,a)∉(A.layout hr hL j).support := by
  intro j i a
  have hnot := near_insertion_not_other_disk G e x hx i.succ 0 (Fin.succ_ne_zero i)
    (endpoint (i,a)) ((endpoint_radius_le endpoint x z e B he hz hfirst hsecond i a).trans_lt hBeR)
  have hR := outerRadius_pos G
  have hrad : radii j≤L*radii j := by nlinarith [hr j]
  constructor
  · intro hv
    have hv' := (Finset.mem_filter.mp hv).2
    exact hnot (by linarith [houter j])
  · intro hv
    exact hnot (by have hu := A.upper j _ hv; linarith [houter j])

#print axioms source_other_geometry
#print axioms other_endpoints_avoid_trials
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization


