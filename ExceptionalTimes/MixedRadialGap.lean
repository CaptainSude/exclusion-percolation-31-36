import ExceptionalTimes.RadialPivotalRemote
import ExceptionalTimes.AnnularCircuitProbability
import ExceptionalTimes.MixedAnnularCollar

/-! Reconnecting the remote factors in the actual mixed dimer law.
Only three static bridge probabilities are supplied; the two-time
comparison follows from proved Harris inequalities and literal gluing. -/

open scoped Classical
open Set

namespace ExceptionalTimes.MixedRadialGap

open DimerLaw FiniteHaar CanonicalHarris EnvironmentVariance MixedCanonicalLaw
open HoleFilling AnnularCollars RadialPivotalRemote

variable {A O : Type*} [Fintype A] [Fintype O]

theorem gap_static_lower
    {S : Type*} [Fintype S] [DistribLattice S] [Nonempty S]
    (decode : S→Configuration) (hdecode : Monotone decode)
    {c a b d : ℕ} (hcd : c≤d) {δ : ℝ} (hδ : 0≤δ)
    (hmiddle : δ≤average (fun x => indicator (WiredArm (decode x) c d)))
    (hcircle1 : δ≤average (fun x => indicator (BlackCircuit (decode x) c a)))
    (hcircle2 : δ≤average (fun x => indicator (BlackCircuit (decode x) b d))) :
    δ^3≤average (fun x => indicator (GapBridge (decode x) c a b d)) := by
  let E : Set S := {x | WiredArm (decode x) c d}
  let F : Set S := {x | BlackCircuit (decode x) c a}
  let H : Set S := {x | BlackCircuit (decode x) b d}
  have hE : IsUpperSet E := fun _ _ hxy h => wiredArm_mono (hdecode hxy) hcd h
  have hF : IsUpperSet F := fun _ _ hxy h => blackCircuit_mono (hdecode hxy) h
  have hH : IsUpperSet H := fun _ _ hxy h => blackCircuit_mono (hdecode hxy) h
  have hFH : IsUpperSet (F∩H) := fun _ _ hxy h => ⟨hF hxy h.1,hH hxy h.2⟩
  have hh := uniform_intersection_lower E (F∩H) hE hFH (mul_nonneg hδ hδ)
    hmiddle (uniform_intersection_lower F H hF hH hδ hcircle1 hcircle2)
  change δ*(δ*δ)≤average (fun x => indicator (GapBridge (decode x) c a b d)) at hh
  convert hh using 1
  ring

/-- The product of the two remote paired probabilities is controlled by
the full radial paired probability. No independence of the bridge and
remote events is asserted or needed. -/
theorem mixed_remote_comparison
    (decode : ((A→Color)×(O→Color))→Configuration) (hdecode : Monotone decode)
    (p : A→ℝ) (hp0 : ∀ i, 0≤p i) (hp1 : ∀ i, p i≤1)
    {r c a b d R : ℕ} (hrc : r≤c) (hca : c≤a) (had : a≤d)
    (hrb : r≤b) (hbd : b≤d) (hdR : d≤R)
    {δ : ℝ} (hδ : 0<δ)
    (hmiddle : δ≤average (fun x => indicator (WiredArm (decode x) c d)))
    (hcircle1 : δ≤average (fun x => indicator (BlackCircuit (decode x) c a)))
    (hcircle2 : δ≤average (fun x => indicator (BlackCircuit (decode x) b d))) :
    mixedProbability p (fun x => WiredArm (decode x) r a)*
      mixedProbability p (fun x => WiredArm (decode x) b R) ≤
        mixedProbability p (fun x => WiredArm (decode x) r R)/δ^6 := by
  let E : Set ((A→Color)×(O→Color)) := {x | WiredArm (decode x) r a}
  let F : Set ((A→Color)×(O→Color)) := {x | WiredArm (decode x) b R}
  let H : Set ((A→Color)×(O→Color)) := {x | GapBridge (decode x) c a b d}
  have hE : IsUpperSet E := fun _ _ hxy h => wiredArm_mono (hdecode hxy) (hrc.trans hca) h
  have hF : IsUpperSet F := fun _ _ hxy h => wiredArm_mono (hdecode hxy) (hbd.trans hdR) h
  have hH : IsUpperSet H := fun _ _ hxy h => gapBridge_mono (hdecode hxy) (hca.trans had) h
  have hEF : IsUpperSet (E∩F) := fun _ _ hxy h => ⟨hE hxy h.1,hF hxy h.2⟩
  have hpair := mixed_event_association p hp0 hp1 E F hE hF
  have hassoc := mixed_event_association p hp0 hp1 (E∩F) H hEF hH
  have hmono := mixedProbability_mono p hp0 hp1
    (fun x => x∈(E∩F)∩H) (fun x => WiredArm (decode x) r R)
    (fun x h => remote_pair_and_gap_implies_arm (decode x) hrc hca had hrb hbd hdR h.1.1 h.1.2 h.2)
  have hstatic := gap_static_lower decode hdecode (hca.trans had) hδ.le hmiddle hcircle1 hcircle2
  have hsquare := mixed_event_square_lower p hp0 hp1 (fun x => x∈H)
  have haverage : 0≤average (fun x => indicator (x∈H)) := average_nonneg (fun _ => indicator_nonneg _)
  have hδ3 : 0≤δ^3 := pow_nonneg hδ.le _
  have hbridge : δ^6≤mixedProbability p (fun x => x∈H) := by
    change δ^3≤average (fun x => indicator (x∈H)) at hstatic
    have he : δ^6=(δ^3)^2 := by ring
    rw [he]
    exact (pow_le_pow_left₀ hδ3 hstatic 2).trans hsquare
  have hnE := mixedProbability_nonneg p hp0 hp1 (fun x => x∈E)
  have hnF := mixedProbability_nonneg p hp0 hp1 (fun x => x∈F)
  have hnH := mixedProbability_nonneg p hp0 hp1 (fun x => x∈H)
  have hprod := mul_le_mul hpair hbridge (pow_nonneg hδ.le 6)
    (mixedProbability_nonneg p hp0 hp1 (fun x => x∈E∩F))
  apply (le_div_iff₀ (pow_pos hδ 6)).mpr
  exact hprod.trans (hassoc.trans hmono)

#print axioms mixed_remote_comparison

end ExceptionalTimes.MixedRadialGap
