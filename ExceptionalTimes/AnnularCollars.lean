import ExceptionalTimes.RadialMiddle

/-! Deterministic annular gluing through actual surrounding black circuits.
No circuit-existence or probability estimate is assumed as a theorem. -/

namespace ExceptionalTimes.AnnularCollars

open HoleFilling WiredBoundary

/-- An actual simple cycle outside the inner box, inside the outer box,
with the literal graph-theoretic surrounding property. -/
structure SurroundingCircuit (r R : ℕ) where
  base : Site
  walk : triangularGraph.Walk base base
  simple : walk.IsCycle
  outside : ∀ z ∈ walk.support, z ∉ latticeBox r
  inside : ∀ z ∈ walk.support, z ∈ latticeBox R
  surrounds : SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ walk.support}

def BlackCircuit (ω : Configuration) (r R : ℕ) : Prop :=
  ∃ C : SurroundingCircuit r R, ∀ z ∈ C.walk.support, ω z = true

theorem SurroundingCircuit.hits {r R : ℕ} (C : SurroundingCircuit r R)
    {u v : Site} (hu : u ∈ latticeBox r) (hv : v ∉ latticeBox R)
    (p : triangularGraph.Walk u v) : ∃ z ∈ p.support, z ∈ C.walk.support := by
  classical
  obtain ⟨K,_,hcut⟩ := C.surrounds
  let η := wireBoth (fun _ => false) r R
  obtain ⟨w,hw,hwK⟩ := (exterior_cluster_infinite (fun _ => false) r R hv).exists_notMem_finset K
  obtain ⟨q⟩ := hw.2
  have hforget : blackGraph η ≤ triangularGraph := fun _ _ h => h.1
  have hcolors := WiredPivotal.black_walk_colors η q hw.1
  obtain ⟨z,hz,hzC⟩ := hcut u hu w hwK (p.append (q.mapLe hforget))
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · exact ⟨z,hz,hzC⟩
  · have htrue : η z = true := hcolors z (by simpa using hz)
    have hfalse : η z = false := by simp [η,wireBoth,C.outside z hzC,C.inside z hzC]
    simp only [hfalse,Bool.false_eq_true] at htrue

theorem blackCircuit_mono {a b : Configuration} (hab : a ≤ b) {r R : ℕ}
    (h : BlackCircuit a r R) : BlackCircuit b r R := by
  obtain ⟨C,hC⟩ := h
  refine ⟨C,fun z hz => ?_⟩
  have hle := hab z
  rw [hC z hz] at hle
  exact Bool.eq_true_of_true_le hle

theorem blackCircuit_congr {a b : Configuration} {r R : ℕ}
    (hab : ∀ z ∈ latticeBox R, z ∉ latticeBox r → a z = b z) :
    BlackCircuit a r R ↔ BlackCircuit b r R := by
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C,fun z hz => (hab z (C.inside z hz) (C.outside z hz)).symm.trans (hC z hz)⟩
  · rintro ⟨C,hC⟩
    exact ⟨C,fun z hz => (hab z (C.inside z hz) (C.outside z hz)).trans (hC z hz)⟩

theorem reachable_of_colored_walk (ω : Configuration) {u v : Site}
    (p : triangularGraph.Walk u v) (hc : ∀ z ∈ p.support, ω z = true) :
    (blackGraph ω).Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
      have ha : ω a = true := hc a (by simp)
      have hb : ω b = true := hc b (by simp)
      exact (show (blackGraph ω).Adj a b from ⟨hab,ha,hb⟩).reachable.trans
        (ih (fun z hz => hc z (List.mem_cons_of_mem a hz)))

theorem colored_walk_reachable_between (ω : Configuration) {a b u v : Site}
    (p : triangularGraph.Walk a b) (hc : ∀ z ∈ p.support, ω z = true)
    (hu : u ∈ p.support) (hv : v ∈ p.support) : (blackGraph ω).Reachable u v := by
  have hu' := reachable_of_colored_walk ω (p.takeUntil u hu)
    (fun z hz => hc z (p.support_takeUntil_subset_support hu hz))
  have hv' := reachable_of_colored_walk ω (p.takeUntil v hv)
    (fun z hz => hc z (p.support_takeUntil_subset_support hv hz))
  exact hu'.symm.trans hv'

/-- The first wired vertex may be white in the original field. Every
subsequent vertex of the simple arm is originally black. -/
theorem wiredArm_tail (ω : Configuration) {r R : ℕ} (h : WiredArm ω r R) :
    ∃ u ∈ latticeBox r, ∃ a v : Site, v ∉ latticeBox R ∧
      ∃ (_e : TriangularAdj u a) (q : triangularGraph.Walk a v),
        (∀ z ∈ q.support, ω z = true) ∧
        (∀ z ∈ q.support, z ∉ latticeBox r) := by
  obtain ⟨u,hu,v,hv,p,hpath,hne,hcol,_⟩ := h
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ a _ e q =>
      have hnot : u ∉ q.support := (List.nodup_cons.mp hpath.support_nodup).1
      refine ⟨u,hu,a,v,hv,e,q,?_,?_⟩
      · intro z hz
        exact (hcol z (List.mem_cons_of_mem _ hz) (fun h => hnot (h ▸ hz))).2
      · intro z hz
        exact (hcol z (List.mem_cons_of_mem _ hz) (fun h => hnot (h ▸ hz))).1

/-- Two radial arms whose overlap contains a surrounding black circuit
join into the full radial arm. This is actual graph gluing, not an
assumed quasi-multiplicativity estimate. -/
theorem wiredArm_glue (ω : Configuration) {r s U R : ℕ}
    (hrs : r ≤ s) (hsU : s ≤ U) (hUR : U ≤ R)
    (hinner : WiredArm ω r U) (houter : WiredArm ω s R)
    (hcircle : BlackCircuit ω s U) : WiredArm ω r R := by
  classical
  obtain ⟨C,hC⟩ := hcircle
  obtain ⟨u,hu,a,v,hv,e,q,hq,hqo⟩ := wiredArm_tail ω houter
  have hvU : v ∉ latticeBox U := fun h => hv (latticeBox_mono hUR h)
  obtain ⟨z,hz,hzC⟩ := C.hits hu hvU (SimpleGraph.Walk.cons e q)
  have hzu : z ≠ u := fun h => C.outside z hzC (h.symm ▸ hu)
  have hzq : z ∈ q.support := by
    rcases List.mem_cons.mp hz with h | h
    · exact (hzu h).elim
    · exact h
  have hzv : (blackGraph ω).Reachable z v :=
    colored_walk_reachable_between ω q hq hzq q.end_mem_support
  obtain ⟨w,hw,hwU⟩ := (oneArm_fillBox_iff_wiredArm ω (hrs.trans hsU)).mpr hinner
  obtain ⟨p⟩ := hw.2
  have hforget : blackGraph (fillBox ω r) ≤ triangularGraph := fun _ _ h => h.1
  obtain ⟨y,hyp,hyC⟩ := C.hits (origin_mem_box s) hwU (p.mapLe hforget)
  have hyp' : y ∈ p.support := by simpa using hyp
  have h0y : (blackGraph (fillBox ω r)).Reachable (0,0) y :=
    (p.takeUntil y hyp').reachable
  have hyz : (blackGraph ω).Reachable y z :=
    colored_walk_reachable_between ω C.walk hC hyC hzC
  have hmono : blackGraph ω ≤ blackGraph (fillBox ω r) := by
    apply blackGraph_mono
    intro x hx
    by_cases hxr : x ∈ latticeBox r
    · exact fillBox_inside ω r hxr
    · simpa only [fillBox_outside ω r hxr] using hx
  apply (oneArm_fillBox_iff_wiredArm ω (hrs.trans (hsU.trans hUR))).mp
  exact ⟨v,⟨fillBox_inside ω r (origin_mem_box r),h0y.trans ((hyz.trans hzv).mono hmono)⟩,hv⟩

/-- Four increasing events in fixed-ratio boundary collars. -/
def CollarBridge (ω : Configuration) (r R : ℕ) : Prop :=
  WiredArm ω r (3*r) ∧ BlackCircuit ω (2*r) (3*r) ∧
    WiredArm ω (R/4) R ∧ BlackCircuit ω (R/4) (R/3)

theorem collarBridge_support {r R : ℕ} (hR : 16*r ≤ R)
    {ω η : Configuration}
    (heq : ∀ v ∈ annularSites r (3*r) ∪ annularSites (R/4) R, ω v = η v) :
    CollarBridge ω r R ↔ CollarBridge η r R := by
  have heq1 : ∀ v ∈ annularSites r (3*r), ω v = η v :=
    fun v hv => heq v (Finset.mem_union_left _ hv)
  have heq2 : ∀ v ∈ annularSites (R/4) R, ω v = η v :=
    fun v hv => heq v (Finset.mem_union_right _ hv)
  have ha1 : WiredArm ω r (3*r) ↔ WiredArm η r (3*r) :=
    wiredArm_congr_on_annulus ω η (by omega)
      (fun v hv hi => heq1 v (Finset.mem_sdiff.mpr ⟨hv,hi⟩))
  have ha2 : WiredArm ω (R/4) R ↔ WiredArm η (R/4) R :=
    wiredArm_congr_on_annulus ω η (by omega)
      (fun v hv hi => heq2 v (Finset.mem_sdiff.mpr ⟨hv,hi⟩))
  have hc1 : BlackCircuit ω (2*r) (3*r) ↔ BlackCircuit η (2*r) (3*r) := by
    apply blackCircuit_congr
    intro v hv hi
    apply heq1 v
    exact Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,
      fun h => hi (latticeBox_mono (by omega) h)⟩
  have hc2 : BlackCircuit ω (R/4) (R/3) ↔ BlackCircuit η (R/4) (R/3) := by
    apply blackCircuit_congr
    intro v hv hi
    apply heq2 v
    exact Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,hi⟩
  exact and_congr ha1 (and_congr hc1 (and_congr ha2 hc2))

theorem wiredArm_mono {ω η : Configuration} (hle : ω ≤ η) {r R : ℕ} (hrR : r ≤ R)
    (h : WiredArm ω r R) : WiredArm η r R := by
  have htest := WiredPivotal.wiredArmTest_monotone hrR hle
  rw [(WiredPivotal.wiredArmTest_eq_true r R ω).mpr h] at htest
  exact (WiredPivotal.wiredArmTest_eq_true _ _ _).mp (Bool.eq_true_of_true_le htest)

theorem collarBridge_mono {ω η : Configuration} (hle : ω ≤ η) (r R : ℕ)
    (h : CollarBridge ω r R) : CollarBridge η r R :=
  ⟨wiredArm_mono hle (by omega) h.1,blackCircuit_mono hle h.2.1,
    wiredArm_mono hle (by omega) h.2.2.1,blackCircuit_mono hle h.2.2.2⟩

/-- The literal middle-arm and collar implication required by the proved
mixed-law comparison. All circuit and arm events retain their original
site colors, with no wiring silently imposed on a circuit. -/
theorem middle_and_collar_implies_arm (ω : Configuration) {r R : ℕ}
    (hR : 16*r ≤ R) (hmiddle : WiredArm ω (2*r) (R/2))
    (hbridge : CollarBridge ω r R) : WiredArm ω r R := by
  have hfirst : WiredArm ω r (R/2) :=
    wiredArm_glue ω (by omega) (by omega) (by omega) hbridge.1 hmiddle hbridge.2.1
  have hshort : WiredArm ω r (R/3) :=
    wiredArm_restrict ω le_rfl (by omega) (by omega) hfirst
  exact wiredArm_glue ω (by omega) (by omega) (by omega)
    hshort hbridge.2.2.1 hbridge.2.2.2

theorem arm_implies_middle (ω : Configuration) {r R : ℕ}
    (hR : 16*r ≤ R) (h : WiredArm ω r R) : WiredArm ω (2*r) (R/2) :=
  wiredArm_restrict ω (by omega) (by omega) (by omega) h

#print axioms wiredArm_glue
#print axioms middle_and_collar_implies_arm

end ExceptionalTimes.AnnularCollars
