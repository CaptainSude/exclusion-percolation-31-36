import ExceptionalTimes.AnnularCollars
import ExceptionalTimes.MixedCanonicalDictionary
import ExceptionalTimes.MixedCanonicalEvents

/-! Actual annular event specialization of the mixed collar comparison.
The only numerical probability hypothesis is a static bridge lower bound;
there is no assumed dynamical comparison or gluing implication. -/

namespace ExceptionalTimes.MixedAnnularCollar

open DimerLaw FiniteHaar ManyDimerLaw MixedCanonicalLaw
open HoleFilling AnnularCollars
open scoped Classical

noncomputable section

variable {A O : Type*} [Fintype A] [Fintype O]

def splitDecode (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (x : (A → Color) × (O → Color)) : Configuration :=
  Function.extend slot (fun b => Sum.elim x.1 x.2 b.1 b.2) (fun _ => false)

theorem splitDecode_monotone (slot : ((A ⊕ O) × Fin 2) ↪ Site) :
    Monotone (splitDecode slot) := by
  intro x y hxy v
  by_cases hex : ∃ b, slot b = v
  · obtain ⟨⟨s,b⟩,rfl⟩ := hex
    unfold splitDecode
    rw [slot.injective.extend_apply,slot.injective.extend_apply]
    cases s with
    | inl a => exact hxy.1 a b
    | inr o => exact hxy.2 o b
  · unfold splitDecode
    rw [Function.extend_apply' _ _ _ hex,Function.extend_apply' _ _ _ hex]

omit [Fintype A] [Fintype O] in
theorem splitDecode_active_agree (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (x : A → Color) (o p : O → Color) {v : Site}
    (hv : ∃ a b, slot (.inl a,b) = v) :
    splitDecode slot (x,o) v = splitDecode slot (x,p) v := by
  obtain ⟨a,b,rfl⟩ := hv
  unfold splitDecode
  rw [slot.injective.extend_apply,slot.injective.extend_apply]
  rfl

def ActiveCovers (slot : ((A ⊕ O) × Fin 2) ↪ Site) (S : Finset Site) : Prop :=
  ∀ v ∈ S, ∃ a b, slot (.inl a,b) = v

omit [Fintype A] [Fintype O] in
theorem middle_ignores_outside (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    {r R : ℕ} (hR : 16*r ≤ R) (hcover : ActiveCovers slot (annularSites (2*r) (R/2)))
    (a : A → Color) (o p : O → Color) :
    WiredArm (splitDecode slot (a,o)) (2*r) (R/2) ↔
      WiredArm (splitDecode slot (a,p)) (2*r) (R/2) := by
  apply wiredArm_congr_on_annulus _ _ (by omega)
  intro v hv hi
  exact splitDecode_active_agree slot a o p (hcover v (Finset.mem_sdiff.mpr ⟨hv,hi⟩))

theorem radial_collar_comparison (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    {r R : ℕ} (hR : 16*r ≤ R)
    (hcover : ActiveCovers slot (annularSites (2*r) (R/2)))
    {b : ℝ} (hb : 0 < b)
    (hbridge : b ≤ average (fun x => EnvironmentVariance.indicator
      (CollarBridge (splitDecode slot x) r R))) :
    manyProbability (Sum.elim p q) (fun x =>
      WiredArm (splitDecode slot (fun a => x (.inl a),fun o => x (.inr o))) r R) ≤
        mixedProbability p (fun x => WiredArm (splitDecode slot x) r R) / b^2 := by
  let E : Set ((A→Color)×(O→Color)) := {x | WiredArm (splitDecode slot x) r R}
  let B : Set ((A→Color)×(O→Color)) := {x | CollarBridge (splitDecode slot x) r R}
  let M : Set (A→Color) := {a | WiredArm (splitDecode slot (a,fun _ _ => false)) (2*r) (R/2)}
  have hM : IsUpperSet M := by
    intro x y hxy hx
    change WiredArm (splitDecode slot (x,fun _ _ => false)) (2*r) (R/2) at hx
    change WiredArm (splitDecode slot (y,fun _ _ => false)) (2*r) (R/2)
    have hxy' : (x,(fun _ _ => false : O → Color)) ≤ (y,fun _ _ => false) := ⟨hxy,le_rfl⟩
    exact wiredArm_mono (splitDecode_monotone slot hxy') (by omega) hx
  have hB : IsUpperSet B := by
    intro x y hxy hx
    exact collarBridge_mono (splitDecode_monotone slot hxy) r R hx
  have hn : ∀ x ∈ E, x.1 ∈ M := by
    intro x hx
    exact (middle_ignores_outside slot hR hcover x.1 x.2 _).mp
      (arm_implies_middle _ hR hx)
  have hg : ∀ x, x.1 ∈ M → x ∈ B → x ∈ E := by
    intro x hm hB'
    exact middle_and_collar_implies_arm _ hR
      ((middle_ignores_outside slot hR hcover x.1 x.2 _).mpr hm) hB'
  have h := collar_comparison p q hp0 hp1 hq0 hq1 E B M hM hB hn hg hb hbridge
  change bothCanonical p q hp0 hp1 hq0 hq1
    (fun x => EnvironmentVariance.indicator (WiredArm (splitDecode slot x) r R)) ≤ _ at h
  rw [MixedCanonicalDictionary.bothCanonical_indicator_eq_manyProbability] at h
  exact h

#print axioms radial_collar_comparison

end

end ExceptionalTimes.MixedAnnularCollar
