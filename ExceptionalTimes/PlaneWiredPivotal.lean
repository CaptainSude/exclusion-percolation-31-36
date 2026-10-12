import ExceptionalTimes.PlaneBoundaryInput
import ExceptionalTimes.WiredPivotal

/-! The actual plane-enclosing circuit and a radial path with endpoints
in different complementary components. All model-specific hypotheses are
proved from the explicitly imported finite-cluster boundary result.
No cyclic ordering or four-arm probability is asserted here. -/

namespace ExceptionalTimes.WiredPivotal

open WiredBoundary HoleFilling TriangularPlane Set

theorem failed_wired_plane_circuit (boundaryInput : PlaneClusterBoundaryCircuit)
    (ω : Configuration) (r R : ℕ) (hfail : ¬WiredConnection ω r R) :
    ∃ v : Site,∃ c : triangularGraph.Walk v v,c.IsCycle ∧
      (∀ z∈c.support,z∉latticeBox r ∧ z∈latticeBox R ∧ ω z=false) ∧
      (∀ z∈latticeBox r,
        Bornology.IsBounded (connectedComponentIn (walkTrace c)ᶜ (point z))) := by
  obtain ⟨v,c,hc,hboundary,hinside⟩ := boundaryInput (wireBoth ω r R) (0,0)
    (wireBoth_inside ω r R (origin_mem_box r)) (failed_cluster_finite ω r R hfail)
  exact ⟨v,c,hc,fun z hz => wired_externalBoundary_in_annulus ω r R (hboundary z hz),
    fun z hz => hinside z (hole_subset_cluster ω r R hz)⟩

theorem opposite_wired_plane_witnesses (boundaryInput : PlaneClusterBoundaryCircuit)
    (a b : Configuration) (r R : ℕ) (v : Site)
    (hab : ∀ w,w≠v→a w=b w)
    (hyes : WiredConnection a r R) (hno : ¬WiredConnection b r R) :
    ∃ w x : Site,∃ p : triangularGraph.Walk (0,0) w,
      ∃ c : triangularGraph.Walk x x,
        w∉latticeBox R ∧ p.IsPath ∧ c.IsCycle ∧
        (∀ z∈p.support,wireBoth a r R z=true) ∧
        (∀ z∈c.support,z∉latticeBox r ∧ z∈latticeBox R ∧ b z=false) ∧
        SeparatesFromInfinity (latticeBox r : Set Site) {z | z∈c.support} ∧
        Bornology.IsBounded (connectedComponentIn (walkTrace c)ᶜ (point (0,0))) ∧
        point w∉connectedComponentIn (walkTrace c)ᶜ (point (0,0)) ∧
        v∈p.support ∧ v∈c.support ∧
        (∀ z∈p.support,z∈c.support→z=v) ∧
        (∀ z∈walkTrace p,z∈walkTrace c→z=point v) := by
  classical
  obtain ⟨x,c,hc,hcw,hinside⟩ := failed_wired_plane_circuit boundaryInput b r R hno
  have hsep := plane_enclosure_separates c (latticeBox r : Set Site)
    (latticeBox r).finite_toSet hinside
  obtain ⟨K,hK,hcut⟩ := hsep
  have hbounded := hinside (0,0) (origin_mem_box r)
  obtain ⟨n,hn⟩ := bounded_plane_sites_in_box hbounded
  obtain ⟨w,hw,hwout⟩ := ((wired_connection_cluster_infinite a r R hyes).sdiff
    ((K∪latticeBox R)∪latticeBox n).finite_toSet).nonempty
  have hwK : w∉K := fun h => hwout (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hwR : w∉latticeBox R := fun h => hwout (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hwn : w∉latticeBox n := fun h => hwout (Finset.mem_union_right _ h)
  have hwend : point w∉connectedComponentIn (walkTrace c)ᶜ (point (0,0)) := fun h => hwn (hn w h)
  obtain ⟨p,hp⟩ := hw.2.exists_isPath
  have hforget : blackGraph (wireBoth a r R)≤triangularGraph := fun _ _ h => h.1
  let q := p.mapLe hforget
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa [q] using hp.support_nodup
  have hblack : ∀ z∈q.support,wireBoth a r R z=true := by
    intro z hz
    exact black_walk_colors _ p hw.1 z (by simpa [q] using hz)
  have hwhite : ∀ z∈c.support,wireBoth b r R z=false := by
    intro z hz
    obtain ⟨hzi,hzo,hzcol⟩ := hcw z hz
    simp [wireBoth,hzi,hzo,hzcol]
  have hunique : ∀ z∈q.support,z∈c.support→z=v := by
    intro z hzp hzc
    by_contra hne
    have heq := wireBoth_agrees_away a b r R v hab z hne
    simp only [hblack z hzp,hwhite z hzc,Bool.true_eq_false] at heq
  obtain ⟨z,hzq,hzc⟩ := hcut (0,0) (origin_mem_box r) w hwK q
  have hzv := hunique z hzq hzc
  exact ⟨w,x,q,c,hwR,hq,hc,hblack,hcw,⟨K,hK,hcut⟩,hbounded,hwend,
    hzv ▸ hzq,hzv ▸ hzc,hunique,fun y hyp hyc => walkTrace_intersection_only q c hunique hyp hyc⟩

theorem cell_pivotal_plane_witnesses (boundaryInput : PlaneClusterBoundaryCircuit)
    {r R : ℕ} (hrR : r≤R) (D : Finset Site) (ω : Configuration)
    (hpiv : CellInterpolation.CellPivotal (wiredArmTest r R) D ω) :
    ∃ η v,v∈D ∧
      (∀ b : Bool,∀ z,z∉D→Function.update η v b z=ω z) ∧
      ∃ w x : Site,∃ p : triangularGraph.Walk (0,0) w,
        ∃ c : triangularGraph.Walk x x,
          w∉latticeBox (R+1) ∧ p.IsPath ∧ c.IsCycle ∧
          (∀ z∈p.support,wireBoth (Function.update η v true) r (R+1) z=true) ∧
          (∀ z∈c.support,z∉latticeBox r ∧ z∈latticeBox (R+1) ∧
            Function.update η v false z=false) ∧
          SeparatesFromInfinity (latticeBox r : Set Site) {z | z∈c.support} ∧
          Bornology.IsBounded (connectedComponentIn (walkTrace c)ᶜ (point (0,0))) ∧
          point w∉connectedComponentIn (walkTrace c)ᶜ (point (0,0)) ∧
          v∈p.support ∧ v∈c.support ∧
          (∀ z∈p.support,z∈c.support→z=v) ∧
          (∀ z∈walkTrace p,z∈walkTrace c→z=point v) := by
  classical
  obtain ⟨η,v,hv,hext,hyes,hno⟩ := CellInterpolation.monotone_cell_pivotal_black_white
    (wiredArmTest r R) (wiredArmTest_monotone hrR) D ω hpiv
  refine ⟨η,v,hv,hext,?_⟩
  apply opposite_wired_plane_witnesses boundaryInput
    (Function.update η v true) (Function.update η v false) r (R+1) v
  · intro z hz
    simp [hz]
  · exact (wiredConnection_succ_iff_wiredArm _ hrR).mpr
      ((wiredArmTest_eq_true r R _).mp hyes)
  · intro h
    exact ((wiredArmTest_eq_false r R _).mp hno)
      ((wiredConnection_succ_iff_wiredArm _ hrR).mp h)

#print axioms cell_pivotal_plane_witnesses

end ExceptionalTimes.WiredPivotal
