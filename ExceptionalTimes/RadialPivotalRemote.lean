import ExceptionalTimes.AnnularCollars
import ExceptionalTimes.MesoscopicCells

/-! The remote one-arm necessities of a pivotal cell. These conclusions
are in the original coloring, not in a modified pivotal completion. -/

namespace ExceptionalTimes.RadialPivotalRemote

open HoleFilling CellInterpolation AnnularCollars

theorem pivotal_has_true_completion (F : Configuration → Bool)
    (D : Finset Site) (ω : Configuration) (h : CellPivotal F D ω) :
    ∃ η : Configuration, (∀ v, v ∉ D → η v=ω v) ∧ F η=true := by
  obtain ⟨a,b,ha,hb,hne⟩ := h
  cases hfa : F a <;> cases hfb : F b
  · exact False.elim (hne (hfa.trans hfb.symm))
  · exact ⟨b,hb,hfb⟩
  · exact ⟨a,ha,hfa⟩
  · exact False.elim (hne (hfa.trans hfb.symm))

theorem pivotal_remote_arm (D : Finset Site) (ω : Configuration)
    {r s S R : ℕ} (hrs : r≤s) (hsS : s≤S) (hSR : S≤R)
    (hdis : Disjoint D (annularSites s S))
    (hpiv : CellPivotal (wiredArmTest r R) D ω) : WiredArm ω s S := by
  obtain ⟨η,hext,hη⟩ := pivotal_has_true_completion _ D ω hpiv
  have hη' : WiredArm η r R := by simpa only [wiredArmTest,decide_eq_true_eq] using hη
  have hshort := wiredArm_restrict η hrs hsS hSR hη'
  apply (wiredArm_congr_on_annulus η ω hsS _).mp hshort
  intro v hvS hvs
  exact hext v (fun hvD => Finset.disjoint_left.mp hdis hvD
    (Finset.mem_sdiff.mpr ⟨hvS,hvs⟩))

theorem pivotal_remote_pair (D : Finset Site) (ω : Configuration)
    {r a b R : ℕ} (hra : r≤a) (haR : a≤R) (hrb : r≤b) (hbR : b≤R)
    (hinner : Disjoint D (latticeBox (a+1))) (houter : D ⊆ latticeBox b)
    (hpiv : CellPivotal (wiredArmTest r R) D ω) :
    WiredArm ω r a ∧ WiredArm ω b R := by
  constructor
  · apply pivotal_remote_arm D ω le_rfl hra haR _ hpiv
    apply Finset.disjoint_left.mpr
    intro v hvD hvA
    exact Finset.disjoint_left.mp hinner hvD (Finset.mem_sdiff.mp hvA).1
  · apply pivotal_remote_arm D ω hrb hbR le_rfl _ hpiv
    apply Finset.disjoint_left.mpr
    intro v hvD hvA
    exact (Finset.mem_sdiff.mp hvA).2 (houter hvD)

/-- Literal displacement bounds suffice for both support exclusions,
including the exiting layer of the inner remote arm. -/
theorem buffered_cell_remote_pair (D : Finset Site) (ω : Configuration)
    (x : Site) {n r a b R : ℕ}
    (hD : ∀ v∈D, v-x ∈ latticeBox n)
    (hin : x ∉ latticeBox (a+1+n)) (hout : latticeRadius x+n≤b)
    (hra : r≤a) (haR : a≤R) (hrb : r≤b) (hbR : b≤R)
    (hpiv : CellPivotal (wiredArmTest r R) D ω) :
    WiredArm ω r a ∧ WiredArm ω b R := by
  apply pivotal_remote_pair D ω hra haR hrb hbR _ _ hpiv
  · apply Finset.disjoint_left.mpr
    intro v hvD hva
    have hh := MesoscopicCells.sub_mem_box hva (hD v hvD)
    have he : v-(v-x)=x := by abel
    rw [he] at hh
    exact hin hh
  · intro v hvD
    have hh := MesoscopicCells.add_mem_box
      (mem_latticeBox_of_radius_le (le_refl (latticeRadius x))) (hD v hvD)
    have he : x+(v-x)=v := by abel
    rw [he] at hh
    exact latticeBox_mono hout hh

theorem dimer_cell_remote_pair {B : Type*} [Fintype B]
    (m : ℕ) (hm : 0<m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d : ℕ} (hz : z∈latticeBox d)
    (hpartner : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (cell : Site) (hcell : cell∈MesoscopicCells.occupied m slot)
    (ω : Configuration) {r a b R : ℕ}
    (hin : MesoscopicCells.anchor m slot cell ∉ latticeBox (a+1+2*(m+d)))
    (hout : MesoscopicCells.anchorRadius m slot cell+2*(m+d)≤b)
    (hra : r≤a) (haR : a≤R) (hrb : r≤b) (hbR : b≤R)
    (hpiv : CellPivotal (wiredArmTest r R) (MesoscopicCells.dimerCell m slot cell) ω) :
    WiredArm ω r a ∧ WiredArm ω b R := by
  apply buffered_cell_remote_pair _ ω (MesoscopicCells.anchor m slot cell) _ hin hout
    hra haR hrb hbR hpiv
  intro v hv
  exact MesoscopicCells.dimerCell_diameter m hm slot z hz hpartner hv
    (MesoscopicCells.anchor_mem m slot cell hcell)

/-- Reconnect the remote arms across their gap using a middle arm and
two surrounding circuits. The bridge can overlap the remote events. -/
def GapBridge (ω : Configuration) (c a b d : ℕ) : Prop :=
  WiredArm ω c d ∧ BlackCircuit ω c a ∧ BlackCircuit ω b d

theorem gapBridge_mono {ω η : Configuration} (h : ω≤η)
    {c a b d : ℕ} (hcd : c≤d) (hb : GapBridge ω c a b d) :
    GapBridge η c a b d :=
  ⟨wiredArm_mono h hcd hb.1,blackCircuit_mono h hb.2.1,blackCircuit_mono h hb.2.2⟩

theorem remote_pair_and_gap_implies_arm (ω : Configuration)
    {r c a b d R : ℕ} (hrc : r≤c) (hca : c≤a) (had : a≤d)
    (hrb : r≤b) (hbd : b≤d) (hdR : d≤R)
    (hinner : WiredArm ω r a) (houter : WiredArm ω b R)
    (hgap : GapBridge ω c a b d) : WiredArm ω r R := by
  have hfirst := wiredArm_glue ω hrc hca had hinner hgap.1 hgap.2.1
  exact wiredArm_glue ω hrb hbd hdR hfirst houter hgap.2.2

#print axioms buffered_cell_remote_pair
#print axioms remote_pair_and_gap_implies_arm

end ExceptionalTimes.RadialPivotalRemote
