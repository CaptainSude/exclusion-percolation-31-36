import ExceptionalTimes.WiredBoundaryDictionary
import ExceptionalTimes.CellInterpolation
import ExceptionalTimes.TriangularPlane

/-! Actual pivotal radial witnesses. The only planar input is the published
finite-cluster surrounding-circuit theorem. This file does not assume or
claim the cyclic ordering of the resulting four branches. -/

namespace ExceptionalTimes.WiredPivotal

open WiredBoundary HoleFilling TriangularPlane

theorem black_walk_colors (η : Configuration) {u v : Site}
    (p : (blackGraph η).Walk u v) (hu : η u = true) :
    ∀ z ∈ p.support, η z = true := by
  induction p with
  | nil => simpa using hu
  | @cons a b c hab p ih =>
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · simpa [hz] using hu
      · exact ih hab.2.2 z hz

theorem wireBoth_agrees_away (a b : Configuration) (r R : ℕ) (v : Site)
    (hab : ∀ w, w ≠ v → a w = b w) :
    ∀ w, w ≠ v → wireBoth a r R w = wireBoth b r R w := by
  intro w hw
  simp only [wireBoth, hab w hw]

/-- A successful and failed completion differing at one site give a simple
black path from the hole beyond the outer box and a surrounding simple
white circuit. They meet at exactly that site, both as vertex sets and as
literal polygonal traces. This is stronger than mere disjointness away
from a *possible* pivot: the pivot is proved to occur in both witnesses. -/
theorem opposite_wired_completions_witnesses
    (boundaryInput : FiniteClusterBoundaryCircuit)
    (a b : Configuration) (r R : ℕ) (v : Site)
    (hab : ∀ w, w ≠ v → a w = b w)
    (hyes : WiredConnection a r R) (hno : ¬WiredConnection b r R) :
    ∃ w x : Site, ∃ p : triangularGraph.Walk (0,0) w,
      ∃ c : triangularGraph.Walk x x,
        w ∉ latticeBox R ∧ p.IsPath ∧ c.IsCycle ∧
        (∀ z ∈ p.support, wireBoth a r R z = true) ∧
        (∀ z ∈ c.support, z ∉ latticeBox r ∧ z ∈ latticeBox R ∧ b z = false) ∧
        SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ c.support} ∧
        v ∈ p.support ∧ v ∈ c.support ∧
        (∀ z ∈ p.support, z ∈ c.support → z = v) ∧
        (∀ z ∈ walkTrace p, z ∈ walkTrace c → z = point v) := by
  classical
  obtain ⟨x, c, hc, hcw, hsep⟩ :=
    failed_wired_connection_white_circuit boundaryInput b r R hno
  obtain ⟨K, hK, hcut⟩ := hsep
  obtain ⟨w, hw, hwout⟩ := ((wired_connection_cluster_infinite a r R hyes).sdiff
    (K ∪ latticeBox R).finite_toSet).nonempty
  have hwK : w ∉ K := fun h => hwout (Finset.mem_union_left _ h)
  have hwR : w ∉ latticeBox R := fun h => hwout (Finset.mem_union_right _ h)
  obtain ⟨p, hp⟩ := hw.2.exists_isPath
  have hforget : blackGraph (wireBoth a r R) ≤ triangularGraph := fun _ _ h => h.1
  let q := p.mapLe hforget
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simpa [q] using hp.support_nodup
  have hblack : ∀ z ∈ q.support, wireBoth a r R z = true := by
    intro z hz
    exact black_walk_colors _ p hw.1 z (by simpa [q] using hz)
  have hwhite : ∀ z ∈ c.support, wireBoth b r R z = false := by
    intro z hz
    obtain ⟨hzi, hzo, hzcol⟩ := hcw z hz
    simp [wireBoth, hzi, hzo, hzcol]
  have hunique : ∀ z ∈ q.support, z ∈ c.support → z = v := by
    intro z hzp hzc
    by_contra hne
    have heq := wireBoth_agrees_away a b r R v hab z hne
    simp only [hblack z hzp, hwhite z hzc, Bool.true_eq_false] at heq
  obtain ⟨z, hzq, hzc⟩ := hcut (0,0) (origin_mem_box r) w hwK q
  have hzv := hunique z hzq hzc
  refine ⟨w, x, q, c, hwR, hq, hc, hblack, hcw, ⟨K,hK,hcut⟩,
    hzv ▸ hzq, hzv ▸ hzc, hunique, ?_⟩
  intro y hyp hyc
  exact walkTrace_intersection_only q c hunique hyp hyc

noncomputable def wiredArmTest (r R : ℕ) (ω : Configuration) : Bool :=
  by
    classical
    exact if HoleFilling.WiredArm ω r R then true else false

@[simp] theorem wiredArmTest_eq_true (r R : ℕ) (ω : Configuration) :
    wiredArmTest r R ω = true ↔ HoleFilling.WiredArm ω r R := by
  classical
  simp [wiredArmTest]

@[simp] theorem wiredArmTest_eq_false (r R : ℕ) (ω : Configuration) :
    wiredArmTest r R ω = false ↔ ¬HoleFilling.WiredArm ω r R := by
  classical
  simp [wiredArmTest]

theorem wiredArmTest_monotone {r R : ℕ} (hrR : r ≤ R) :
    Monotone (wiredArmTest r R) := by
  intro a b hab
  cases hfa : wiredArmTest r R a with
  | false => simp
  | true =>
      have ha := (wiredArmTest_eq_true r R a).mp hfa
      have hgraph : blackGraph (fillBox a r) ≤ blackGraph (fillBox b r) := by
        apply blackGraph_mono
        intro z hz
        by_cases hzr : z ∈ latticeBox r
        · simp [fillBox, hzr]
        · have haz : a z = true := by simpa [fillBox, hzr] using hz
          have hle := hab z
          have hbz : b z = true := by
            cases hbz : b z
            · simp only [haz, hbz] at hle
              exact ((by decide : ¬(true ≤ false)) hle).elim
            · rfl
          simp [fillBox, hzr, hbz]
      obtain ⟨w, hw, hwout⟩ := (oneArm_fillBox_iff_wiredArm a hrR).mpr ha
      have hb : OneArm (fillBox b r) (0,0) R :=
        ⟨w, ⟨by simp [fillBox, origin_mem_box r], hw.2.mono hgraph⟩, hwout⟩
      have hfb := (wiredArmTest_eq_true r R b).mpr
        ((oneArm_fillBox_iff_wiredArm b hrR).mp hb)
      simp [hfb]

/-- The finite-cell pivotal event is reduced to actual black/white
single-site completions, then to literal path/circuit witnesses. The
outer radius of the circuit is R+1, matching the exact wiring dictionary. -/
theorem cell_pivotal_wired_witnesses
    (boundaryInput : FiniteClusterBoundaryCircuit)
    {r R : ℕ} (hrR : r ≤ R) (D : Finset Site) (ω : Configuration)
    (hpiv : CellInterpolation.CellPivotal (wiredArmTest r R) D ω) :
    ∃ η v, v ∈ D ∧
      (∀ c : Bool, ∀ z, z ∉ D → Function.update η v c z = ω z) ∧
      ∃ w x : Site, ∃ p : triangularGraph.Walk (0,0) w,
        ∃ c : triangularGraph.Walk x x,
          w ∉ latticeBox (R+1) ∧ p.IsPath ∧ c.IsCycle ∧
          (∀ z ∈ p.support, wireBoth (Function.update η v true) r (R+1) z = true) ∧
          (∀ z ∈ c.support, z ∉ latticeBox r ∧ z ∈ latticeBox (R+1) ∧
            Function.update η v false z = false) ∧
          SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ c.support} ∧
          v ∈ p.support ∧ v ∈ c.support ∧
          (∀ z ∈ p.support, z ∈ c.support → z = v) ∧
          (∀ z ∈ walkTrace p, z ∈ walkTrace c → z = point v) := by
  classical
  obtain ⟨η,v,hv,hext,hyes,hno⟩ := CellInterpolation.monotone_cell_pivotal_black_white
    (wiredArmTest r R) (wiredArmTest_monotone hrR) D ω hpiv
  refine ⟨η,v,hv,hext,?_⟩
  apply opposite_wired_completions_witnesses boundaryInput
    (Function.update η v true) (Function.update η v false) r (R+1) v
  · intro z hz
    simp [hz]
  · exact (wiredConnection_succ_iff_wiredArm _ hrR).mpr
      ((wiredArmTest_eq_true r R _).mp hyes)
  · intro h
    exact ((wiredArmTest_eq_false r R _).mp hno)
      ((wiredConnection_succ_iff_wiredArm _ hrR).mp h)

#print axioms opposite_wired_completions_witnesses
#print axioms cell_pivotal_wired_witnesses

end ExceptionalTimes.WiredPivotal
