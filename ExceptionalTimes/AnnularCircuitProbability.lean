import ExceptionalTimes.AnnularCollars
import ExceptionalTimes.FiniteHaar
import ExceptionalTimes.EnvironmentVariance

/-! Black surrounding circuits from failure of the opposite-color radial
event. Wide collars can therefore use a static one-arm upper bound; a
new circuit-probability input is unnecessary. -/

namespace ExceptionalTimes.AnnularCollars

open HoleFilling WiredBoundary FiniteHaar EnvironmentVariance
open scoped Classical

theorem blackCircuit_iff_no_white_arm (boundaryInput : FiniteClusterBoundaryCircuit)
    (ω : Configuration) {r R : ℕ} (hrR : r ≤ R) :
    BlackCircuit ω r (R+1) ↔ ¬WiredArm (fun z => !(ω z)) r R := by
  rw [wiredArm_annular_duality boundaryInput _ hrR]
  constructor
  · rintro ⟨C,hC⟩
    exact ⟨C.base,C.walk,C.simple,fun z hz =>
      ⟨C.outside z hz,C.inside z hz,by simp only [hC z hz,Bool.not_true]⟩,C.surrounds⟩
  · rintro ⟨v,c,hc,hcol,hsep⟩
    refine ⟨⟨v,c,hc,fun z hz => (hcol z hz).1,fun z hz => (hcol z hz).2.1,hsep⟩,?_⟩
    intro z hz
    have h := (hcol z hz).2.2
    cases hzcol : ω z <;> simp_all

/-- Exact finite-law complement identity. The supplied involution need
only flip the actual annular site colors; exterior completion is irrelevant. -/
theorem blackCircuit_probability_complement
    {S : Type*} [Fintype S] [Nonempty S]
    (boundaryInput : FiniteClusterBoundaryCircuit)
    (decode : S → Configuration) (flip : S ≃ S)
    {r R : ℕ} (hrR : r ≤ R)
    (hflip : ∀ x v, v ∈ annularSites r R → decode (flip x) v = !(decode x v)) :
    average (fun x => indicator (BlackCircuit (decode x) r (R+1))) =
      1 - average (fun x => indicator (WiredArm (decode x) r R)) := by
  have he : ∀ x, WiredArm (decode (flip x)) r R ↔ WiredArm (fun z => !(decode x z)) r R := by
    intro x
    apply wiredArm_congr_on_annulus _ _ hrR
    intro v hv hi
    exact hflip x v (Finset.mem_sdiff.mpr ⟨hv,hi⟩)
  have hi : (fun x => indicator (BlackCircuit (decode x) r (R+1))) =
      fun x => 1-indicator (WiredArm (decode (flip x)) r R) := by
    funext x
    rw [blackCircuit_iff_no_white_arm boundaryInput _ hrR,← he x]
    by_cases h : WiredArm (decode (flip x)) r R <;> simp [indicator,h]
  rw [hi,average_sub,average_const,
    average_equiv flip (fun x => indicator (WiredArm (decode x) r R))]

theorem blackCircuit_probability_lower
    {S : Type*} [Fintype S] [Nonempty S]
    (boundaryInput : FiniteClusterBoundaryCircuit)
    (decode : S → Configuration) (flip : S ≃ S)
    {r R : ℕ} (hrR : r ≤ R)
    (hflip : ∀ x v, v ∈ annularSites r R → decode (flip x) v = !(decode x v))
    {a : ℝ} (hupper : average (fun x => indicator (WiredArm (decode x) r R)) ≤ a) :
    1-a ≤ average (fun x => indicator (BlackCircuit (decode x) r (R+1))) := by
  rw [blackCircuit_probability_complement boundaryInput decode flip hrR hflip]
  linarith

/-- Collar sizes may be arbitrary fixed ratios. This permits choosing a
wide enough circuit annulus for a published one-arm upper bound <1. -/
def CollarBridgeAt (ω : Configuration) (r s u v w R : ℕ) : Prop :=
  WiredArm ω r u ∧ BlackCircuit ω s u ∧ WiredArm ω v R ∧ BlackCircuit ω v w

theorem middle_and_collarAt_implies_arm (ω : Configuration) {r s u v w t R : ℕ}
    (hrs : r ≤ s) (hsu : s ≤ u) (hut : u ≤ t)
    (hrv : r ≤ v) (hvw : v ≤ w) (hwt : w ≤ t) (htR : t ≤ R)
    (hmiddle : WiredArm ω s t) (hbridge : CollarBridgeAt ω r s u v w R) :
    WiredArm ω r R := by
  have hfirst := wiredArm_glue ω hrs hsu hut hbridge.1 hmiddle hbridge.2.1
  have hshort : WiredArm ω r w := wiredArm_restrict ω le_rfl (hrv.trans hvw) hwt hfirst
  exact wiredArm_glue ω hrv hvw (hwt.trans htR) hshort hbridge.2.2.1 hbridge.2.2.2

theorem collarBridgeAt_mono {ω η : Configuration} (hle : ω ≤ η)
    {r s u v w R : ℕ} (hru : r ≤ u) (hvR : v ≤ R)
    (h : CollarBridgeAt ω r s u v w R) : CollarBridgeAt η r s u v w R :=
  ⟨wiredArm_mono hle hru h.1,blackCircuit_mono hle h.2.1,
    wiredArm_mono hle hvR h.2.2.1,blackCircuit_mono hle h.2.2.2⟩

theorem uniform_intersection_lower
    {S : Type*} [Fintype S] [DistribLattice S] [Nonempty S]
    (E F : Set S) (hE : IsUpperSet E) (hF : IsUpperSet F)
    {a b : ℝ} (hb : 0 ≤ b)
    (haE : a ≤ average (eventIndicator E)) (hbF : b ≤ average (eventIndicator F)) :
    a*b ≤ average (eventIndicator (E ∩ F)) := by
  have hmul := mul_le_mul haE hbF hb (average_nonneg (eventIndicator_nonneg E))
  apply hmul.trans
  rw [eventIndicator_inter]
  exact uniform_harris _ _ (eventIndicator_nonneg E) (eventIndicator_nonneg F)
    (eventIndicator_monotone E hE) (eventIndicator_monotone F hF)

theorem uniform_four_events_lower
    {S : Type*} [Fintype S] [DistribLattice S] [Nonempty S]
    (E F G H : Set S) (hE : IsUpperSet E) (hF : IsUpperSet F)
    (hG : IsUpperSet G) (hH : IsUpperSet H)
    {c : ℝ} (hc : 0 ≤ c)
    (he : c ≤ average (eventIndicator E)) (hf : c ≤ average (eventIndicator F))
    (hg : c ≤ average (eventIndicator G)) (hh : c ≤ average (eventIndicator H)) :
    c^4 ≤ average (eventIndicator (E ∩ F ∩ (G ∩ H))) := by
  have hEF : IsUpperSet (E ∩ F) := fun _ _ hxy h => ⟨hE hxy h.1,hF hxy h.2⟩
  have hGH : IsUpperSet (G ∩ H) := fun _ _ hxy h => ⟨hG hxy h.1,hH hxy h.2⟩
  have h := uniform_intersection_lower (E ∩ F) (G ∩ H) hEF hGH (mul_nonneg hc hc)
    (uniform_intersection_lower E F hE hF hc he hf)
    (uniform_intersection_lower G H hG hH hc hg hh)
  convert h using 1
  ring

/-- Static collar lower bound is derived by ordinary finite Harris from
the four literal one-time probabilities, with no dynamical assumption. -/
theorem collarAt_probability_lower
    {S : Type*} [Fintype S] [DistribLattice S] [Nonempty S]
    (decode : S → Configuration) (hdecode : Monotone decode)
    {r s u v w R : ℕ} (hru : r ≤ u) (hvR : v ≤ R)
    {c : ℝ} (hc : 0 ≤ c)
    (hinner : c ≤ average (fun x => indicator (WiredArm (decode x) r u)))
    (hcircle1 : c ≤ average (fun x => indicator (BlackCircuit (decode x) s u)))
    (houter : c ≤ average (fun x => indicator (WiredArm (decode x) v R)))
    (hcircle2 : c ≤ average (fun x => indicator (BlackCircuit (decode x) v w))) :
    c^4 ≤ average (fun x => indicator (CollarBridgeAt (decode x) r s u v w R)) := by
  let E : Set S := {x | WiredArm (decode x) r u}
  let F : Set S := {x | BlackCircuit (decode x) s u}
  let G : Set S := {x | WiredArm (decode x) v R}
  let H : Set S := {x | BlackCircuit (decode x) v w}
  have hE : IsUpperSet E := fun _ _ hxy h => wiredArm_mono (hdecode hxy) hru h
  have hF : IsUpperSet F := fun _ _ hxy h => blackCircuit_mono (hdecode hxy) h
  have hG : IsUpperSet G := fun _ _ hxy h => wiredArm_mono (hdecode hxy) hvR h
  have hH : IsUpperSet H := fun _ _ hxy h => blackCircuit_mono (hdecode hxy) h
  have h := uniform_four_events_lower E F G H hE hF hG hH hc hinner hcircle1 houter hcircle2
  have heq : eventIndicator (E ∩ F ∩ (G ∩ H)) =
      fun x => indicator (CollarBridgeAt (decode x) r s u v w R) := by
    have hset : E ∩ F ∩ (G ∩ H) = {x | CollarBridgeAt (decode x) r s u v w R} := by
      ext x
      exact and_assoc
    rw [hset]
    rfl
  rw [heq] at h
  exact h

#print axioms blackCircuit_probability_complement
#print axioms middle_and_collarAt_implies_arm
#print axioms collarAt_probability_lower

end ExceptionalTimes.AnnularCollars
