import ExceptionalTimes.RadialPivotalRemote

/-! Gap gluing with either remote arm omitted when it would extend beyond
the original annulus. The bridge is always supported in that annulus. -/

namespace ExceptionalTimes.ClippedRadialGap

open HoleFilling AnnularCollars RadialPivotalRemote

def InnerRemote (ω : Configuration) (r c a : ℕ) : Prop := r≤c → WiredArm ω r a
def OuterRemote (ω : Configuration) (b d R : ℕ) : Prop := d≤R → WiredArm ω b R

def Bridge (ω : Configuration) (r c a b d R : ℕ) : Prop :=
  WiredArm ω (max r c) (min R d) ∧
    (r≤c → BlackCircuit ω c a) ∧ (d≤R → BlackCircuit ω b d)

theorem bridge_radii {r c a b d R : ℕ} (hrR : r≤R) (hca : c≤a)
    (haR : a≤R) (had : a≤d) (hrb : r≤b) (hbd : b≤d) : max r c≤min R d := by
  omega

theorem innerRemote_mono {ω η : Configuration} (h : ω≤η)
    {r c a : ℕ} (hca : c≤a) (hω : InnerRemote ω r c a) : InnerRemote η r c a :=
  fun hr => wiredArm_mono h (hr.trans hca) (hω hr)

theorem outerRemote_mono {ω η : Configuration} (h : ω≤η)
    {b d R : ℕ} (hbd : b≤d) (hω : OuterRemote ω b d R) : OuterRemote η b d R :=
  fun hd => wiredArm_mono h (hbd.trans hd) (hω hd)

theorem bridge_mono {ω η : Configuration} (h : ω≤η)
    {r c a b d R : ℕ} (hmid : max r c≤min R d)
    (hω : Bridge ω r c a b d R) : Bridge η r c a b d R :=
  ⟨wiredArm_mono h hmid hω.1,fun hr => blackCircuit_mono h (hω.2.1 hr),
    fun hd => blackCircuit_mono h (hω.2.2 hd)⟩

theorem gap_implies_bridge (ω : Configuration) {r c a b d R : ℕ}
    (hmid : max r c≤min R d) (hgap : GapBridge ω c a b d) : Bridge ω r c a b d R :=
  ⟨wiredArm_restrict ω (le_max_right _ _) hmid (min_le_right _ _) hgap.1,
    fun _ => hgap.2.1,fun _ => hgap.2.2⟩

theorem remote_and_bridge_implies_arm (ω : Configuration)
    {r c a b d R : ℕ} (_hrR : r≤R) (hca : c≤a) (haR : a≤R)
    (had : a≤d) (hrb : r≤b) (hbd : b≤d)
    (hinner : InnerRemote ω r c a) (houter : OuterRemote ω b d R)
    (hbridge : Bridge ω r c a b d R) : WiredArm ω r R := by
  obtain ⟨hm,hci,hco⟩ := hbridge
  by_cases hin : r≤c
  · rw [max_eq_right hin] at hm
    by_cases hout : d≤R
    · rw [min_eq_right hout] at hm
      exact remote_pair_and_gap_implies_arm ω hin hca had hrb hbd hout
        (hinner hin) (houter hout) ⟨hm,hci hin,hco hout⟩
    · rw [min_eq_left (le_of_not_ge hout)] at hm
      exact wiredArm_glue ω hin hca haR (hinner hin) hm (hci hin)
  · rw [max_eq_left (le_of_not_ge hin)] at hm
    by_cases hout : d≤R
    · rw [min_eq_right hout] at hm
      exact wiredArm_glue ω hrb hbd hout hm (houter hout) (hco hout)
    · simpa only [min_eq_left (le_of_not_ge hout)] using hm

theorem bridge_locality {ω η : Configuration} {r c a b d R : ℕ}
    (hrR : r≤R) (hca : c≤a) (haR : a≤R) (had : a≤d) (hrb : r≤b) (hbd : b≤d)
    (heq : ∀ v∈annularSites r R, ω v=η v) :
    Bridge ω r c a b d R ↔ Bridge η r c a b d R := by
  have hm := wiredArm_congr_on_annulus ω η (bridge_radii hrR hca haR had hrb hbd)
    (fun v hv hi => heq v (annularSites_mono (le_max_left _ _) (min_le_left _ _)
      (Finset.mem_sdiff.mpr ⟨hv,hi⟩)))
  have hci (hrc : r≤c) : BlackCircuit ω c a ↔ BlackCircuit η c a := by
    apply blackCircuit_congr
    intro v hv hi
    exact heq v (Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,
      fun h => hi (latticeBox_mono hrc h)⟩)
  have hco (hdR : d≤R) : BlackCircuit ω b d ↔ BlackCircuit η b d := by
    apply blackCircuit_congr
    intro v hv hi
    exact heq v (Finset.mem_sdiff.mpr ⟨latticeBox_mono (by omega) hv,
      fun h => hi (latticeBox_mono hrb h)⟩)
  exact and_congr hm (and_congr (forall_congr' hci) (forall_congr' hco))

#print axioms remote_and_bridge_implies_arm
#print axioms bridge_locality

end ExceptionalTimes.ClippedRadialGap

