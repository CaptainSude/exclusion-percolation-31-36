import ExceptionalTimes.MixedAnnularCollar
import ExceptionalTimes.AnnularCircuitProbability

/-! Mixed radial comparison using only four static one-arm estimates.
The two circuit probabilities are derived from actual annular duality. -/

namespace ExceptionalTimes.MixedAnnularCollar

open DimerLaw FiniteHaar ManyDimerLaw MixedCanonicalLaw
open HoleFilling AnnularCollars EnvironmentVariance WiredBoundary
open scoped Classical

noncomputable section

variable {A O : Type*}

def splitFlip : ((A → Color) × (O → Color)) ≃ ((A → Color) × (O → Color)) where
  toFun x := (fun a b => !(x.1 a b),fun o b => !(x.2 o b))
  invFun x := (fun a b => !(x.1 a b),fun o b => !(x.2 o b))
  left_inv x := by
    apply Prod.ext <;> funext a b <;> exact Bool.not_not _
  right_inv x := by
    apply Prod.ext <;> funext a b <;> exact Bool.not_not _

def Covers (slot : ((A ⊕ O) × Fin 2) ↪ Site) (S : Finset Site) : Prop :=
  ∀ v ∈ S, ∃ b, slot b = v

theorem splitDecode_flip (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (x : (A → Color) × (O → Color)) {v : Site} (hv : ∃ b, slot b=v) :
    splitDecode slot (splitFlip x) v = !(splitDecode slot x v) := by
  obtain ⟨⟨s,b⟩,rfl⟩ := hv
  unfold splitDecode
  rw [slot.injective.extend_apply,slot.injective.extend_apply]
  cases s <;> rfl

theorem activeArm_ignores_outside (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    {r R : ℕ} (hrR : r ≤ R) (hcover : ActiveCovers slot (annularSites r R))
    (a : A → Color) (o p : O → Color) :
    WiredArm (splitDecode slot (a,o)) r R ↔ WiredArm (splitDecode slot (a,p)) r R := by
  apply wiredArm_congr_on_annulus _ _ hrR
  intro v hv hi
  exact splitDecode_active_agree slot a o p (hcover v (Finset.mem_sdiff.mpr ⟨hv,hi⟩))

variable [Fintype A] [Fintype O]

theorem wide_radial_collar_comparison
    (boundaryInput : FiniteClusterBoundaryCircuit)
    (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    {r s u v w t R : ℕ}
    (hrs : r ≤ s) (hsu : s ≤ u) (hut : u+1 ≤ t)
    (hrv : r ≤ v) (hvw : v ≤ w) (hwt : w+1 ≤ t) (htR : t ≤ R)
    (hcover : ActiveCovers slot (annularSites s t))
    (hfull : Covers slot (annularSites r R))
    {c : ℝ} (hc : 0 < c)
    (hinner : c ≤ average (fun x => indicator (WiredArm (splitDecode slot x) r (u+1))))
    (houter : c ≤ average (fun x => indicator (WiredArm (splitDecode slot x) v R)))
    (hcircle1 : average (fun x => indicator (WiredArm (splitDecode slot x) s u)) ≤ 1-c)
    (hcircle2 : average (fun x => indicator (WiredArm (splitDecode slot x) v w)) ≤ 1-c) :
    manyProbability (Sum.elim p q) (fun x =>
      WiredArm (splitDecode slot (fun a => x (.inl a),fun o => x (.inr o))) r R) ≤
        mixedProbability p (fun x => WiredArm (splitDecode slot x) r R) / c^8 := by
  let E : Set ((A→Color)×(O→Color)) := {x | WiredArm (splitDecode slot x) r R}
  let B : Set ((A→Color)×(O→Color)) :=
    {x | CollarBridgeAt (splitDecode slot x) r s (u+1) v (w+1) R}
  let M : Set (A→Color) := {a | WiredArm (splitDecode slot (a,fun _ _ => false)) s t}
  have hrU : r ≤ u+1 := by omega
  have hsT : s ≤ t := by omega
  have hvR : v ≤ R := by omega
  have hM : IsUpperSet M := by
    intro x y hxy hx
    change WiredArm (splitDecode slot (x,fun _ _ => false)) s t at hx
    change WiredArm (splitDecode slot (y,fun _ _ => false)) s t
    have hxy' : (x,(fun _ _ => false : O → Color)) ≤ (y,fun _ _ => false) := ⟨hxy,le_rfl⟩
    exact wiredArm_mono (splitDecode_monotone slot hxy') hsT hx
  have hB : IsUpperSet B := by
    intro x y hxy hx
    exact collarBridgeAt_mono (splitDecode_monotone slot hxy) hrU hvR hx
  have hn : ∀ x ∈ E, x.1 ∈ M := by
    intro x hx
    exact (activeArm_ignores_outside slot hsT hcover x.1 x.2 _).mp
      (wiredArm_restrict _ hrs hsT htR hx)
  have hg : ∀ x, x.1 ∈ M → x ∈ B → x ∈ E := by
    intro x hm hB'
    exact middle_and_collarAt_implies_arm _ hrs (by omega) hut hrv (by omega) hwt htR
      ((activeArm_ignores_outside slot hsT hcover x.1 x.2 _).mpr hm) hB'
  have hf1 : ∀ x z, z ∈ annularSites s u →
      splitDecode slot (splitFlip x) z = !(splitDecode slot x z) := by
    intro x z hz
    exact splitDecode_flip slot x (hfull z (annularSites_mono hrs (by omega) hz))
  have hf2 : ∀ x z, z ∈ annularSites v w →
      splitDecode slot (splitFlip x) z = !(splitDecode slot x z) := by
    intro x z hz
    exact splitDecode_flip slot x (hfull z (annularSites_mono hrv (by omega) hz))
  have hc1 : c ≤ average (fun x => indicator (BlackCircuit (splitDecode slot x) s (u+1))) := by
    have h := blackCircuit_probability_lower boundaryInput (splitDecode slot) splitFlip hsu hf1 hcircle1
    linarith
  have hc2 : c ≤ average (fun x => indicator (BlackCircuit (splitDecode slot x) v (w+1))) := by
    have h := blackCircuit_probability_lower boundaryInput (splitDecode slot) splitFlip hvw hf2 hcircle2
    linarith
  have hbridge : c^4 ≤ average (eventIndicator B) :=
    collarAt_probability_lower (splitDecode slot) (splitDecode_monotone slot)
      hrU hvR hc.le hinner hc1 houter hc2
  have h := collar_comparison p q hp0 hp1 hq0 hq1 E B M hM hB hn hg (pow_pos hc 4) hbridge
  change bothCanonical p q hp0 hp1 hq0 hq1
    (fun x => indicator (WiredArm (splitDecode slot x) r R)) ≤ _ at h
  rw [MixedCanonicalDictionary.bothCanonical_indicator_eq_manyProbability] at h
  have hpow : (c^4)^2 = c^8 := by ring
  simpa only [hpow, E, Set.mem_ofPred_eq] using h

#print axioms wide_radial_collar_comparison

end

end ExceptionalTimes.MixedAnnularCollar
