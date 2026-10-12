import ExceptionalTimes.DimerOrientation
import ExceptionalTimes.UnitReferenceCover
import ExceptionalTimes.IndependentSupportExtension

/-! Exact probability of every finitely supported local event is
independent of the finite cover and endpoint ordering used to describe
one fixed unit matching phase. No percolation input occurs here. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.MatchingCoverLaw
noncomputable section
open PairSquareSewing DimerLaw ManyDimerLaw ActivePartitionLaw
open EnvironmentVariance CanonicalSpatialProduct DimerOrientation CanonicalRadialLaw

variable {A B : Type*}

theorem manyLaw_embedding [Fintype A] [Fintype B] (j : A↪B)
    (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (f : ((A→Color)×(A→Color))→ℝ) :
    (manyLaw p hp0 hp1).expect (fun ω => f (fun a => ω.1 (j a),fun a => ω.2 (j a)))=
      (manyLaw (fun a => p (j a)) (fun a => hp0 (j a)) (fun a => hp1 (j a))).expect f := by
  rw [manyLaw_pi,manyLaw_pi]
  exact IndependentSupportExtension.pi_restrict j
    (fun b => jointLaw (p b) (hp0 b) (hp1 b)) (fun ω => f (pairCoordinates.symm ω))

theorem manyProbability_embedding [Fintype A] [Fintype B] (j : A↪B)
    (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1) (E : (A→Color)→Prop) :
    manyProbability p (fun ω => E (fun a => ω (j a)))=
      manyProbability (fun a => p (j a)) E := by
  rw [manyProbability_eq_joint p hp0 hp1,
    manyProbability_eq_joint _ (fun a => hp0 (j a)) (fun a => hp1 (j a))]
  exact manyLaw_embedding j p hp0 hp1 (fun ω => indicator (E ω.1 ∧ E ω.2))

theorem left_endpoint (phase : Bool) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (b : B) (i : Fin 2) : UnitReferenceCover.left phase (slot (b,i))=slot (b,0) := by
  fin_cases i
  · change UnitReferenceCover.left phase (slot (b,0))=slot (b,0)
    simp only [UnitReferenceCover.left,ite_eq_left (heven b),Prod.mk.eta]
  · change UnitReferenceCover.left phase (slot (b,1))=slot (b,0)
    rw [hpos b]
    have hodd : ((slot (b,0)).1+1+UnitReferenceCover.offset phase)%2≠0 := by
      have hh := heven b
      omega
    simp only [UnitReferenceCover.left,Prod.fst_add,Prod.snd_add,add_zero,
      ite_eq_right hodd]
    change (((slot (b,0)).1+1-1,(slot (b,0)).2))=slot (b,0)
    simp only [add_sub_cancel_right,Prod.mk.eta]

theorem exists_anchor (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (hcover : ∀ v∈S,∃ bi,slot bi=v) (a : UnitReferenceCover.anchors phase S) :
    ∃ b,slot (b,0)=a.val := by
  obtain ⟨v,hv,ha⟩ := Finset.mem_image.mp a.property
  obtain ⟨⟨b,i⟩,hb⟩ := hcover v hv
  exact ⟨b,(left_endpoint phase slot hpos heven b i).symm.trans
    ((congrArg (UnitReferenceCover.left phase) hb).trans ha)⟩

def selectAnchor (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (hcover : ∀ v∈S,∃ bi,slot bi=v) : UnitReferenceCover.anchors phase S ↪ B where
  toFun a := Classical.choose (exists_anchor phase S slot hpos heven hcover a)
  inj' := by
    intro a b h
    have ha := Classical.choose_spec (exists_anchor phase S slot hpos heven hcover a)
    have hb := Classical.choose_spec (exists_anchor phase S slot hpos heven hcover b)
    exact Subtype.ext (ha.symm.trans ((congrArg (fun b => slot (b,0)) h).trans hb))

theorem selectAnchor_endpoints (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (hcover : ∀ v∈S,∃ bi,slot bi=v) (a : UnitReferenceCover.anchors phase S) (i : Fin 2) :
    slot (selectAnchor phase S slot hpos heven hcover a,i)=UnitReferenceCover.slot phase S (a,i) := by
  have ha : slot (selectAnchor phase S slot hpos heven hcover a,0)=a.val :=
    Classical.choose_spec (exists_anchor phase S slot hpos heven hcover a)
  fin_cases i
  · change slot (selectAnchor phase S slot hpos heven hcover a,0)=UnitReferenceCover.slot phase S (a,0)
    simpa only [UnitReferenceCover.slot_zero] using ha
  · change slot (selectAnchor phase S slot hpos heven hcover a,1)=UnitReferenceCover.slot phase S (a,1)
    rw [hpos,ha,UnitReferenceCover.slot_one]

theorem selected_decoder_agrees (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (hcover : ∀ v∈S,∃ bi,slot bi=v) (ω : B→Color) :
    Set.EqOn (pairDecode slot ω)
      (pairDecode (UnitReferenceCover.slot phase S)
        (fun a => ω (selectAnchor phase S slot hpos heven hcover a))) S := by
  intro v hv
  obtain ⟨⟨a,i⟩,rfl⟩ := UnitReferenceCover.slot_covers phase S v hv
  have he := selectAnchor_endpoints phase S slot hpos heven hcover a i
  unfold pairDecode
  conv_lhs => rw [←he]
  rw [slot.injective.extend_apply,(UnitReferenceCover.slot phase S).injective.extend_apply]

theorem positive_cover_probability [Fintype B]
    (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpos : ∀ b,slot (b,1)=slot (b,0)+(1,0))
    (heven : ∀ b,((slot (b,0)).1+UnitReferenceCover.offset phase)%2=0)
    (hcover : ∀ v∈S,∃ bi,slot bi=v) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (E : Configuration→Prop) (hlocal : ∀ ω η,Set.EqOn ω η S → (E ω↔E η)) :
    manyProbability (fun _ : B => p) (fun ω => E (pairDecode slot ω))=
      manyProbability (fun _ => p) (fun ω => E (pairDecode (UnitReferenceCover.slot phase S) ω)) := by
  let j := selectAnchor phase S slot hpos heven hcover
  have he (ω : B→Color) : E (pairDecode slot ω)↔
      E (pairDecode (UnitReferenceCover.slot phase S) (fun a => ω (j a))) :=
    hlocal _ _ (selected_decoder_agrees phase S slot hpos heven hcover ω)
  rw [many_congr (fun _ => p) he]
  exact manyProbability_embedding j (fun _ => p) (fun _ => hp0) (fun _ => hp1)
    (fun ω => E (pairDecode (UnitReferenceCover.slot phase S) ω))

/-- Arbitrary endpoint orientations and all unused dimers disappear from
the law of a locally supported event at the same refresh parameter. -/
theorem cover_probability [Fintype B]
    (phase : Bool) (S : Finset Site) (slot : B×Fin 2 ↪ Site)
    (hpair : ∀ b,slot (b,1)=UnitMatchingTranslation.partner phase (slot (b,0)))
    (hcover : ∀ v∈S,∃ bi,slot bi=v) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1)
    (E : Configuration→Prop) (hlocal : ∀ ω η,Set.EqOn ω η S → (E ω↔E η)) :
    manyProbability (fun _ : B => p) (fun ω => E (pairDecode slot ω))=
      manyProbability (fun _ => p) (fun ω => E (pairDecode (UnitReferenceCover.slot phase S) ω)) := by
  rw [probability_orient slot (positiveChange phase slot)]
  exact positive_cover_probability phase S _ (positively_oriented phase slot hpair)
    (positive_zero_even phase slot hpair) (orient_covers slot _ S hcover) p hp0 hp1 E hlocal

/-- Two arbitrary finite covers of the same matching phase give exactly
the same two-time local-event probability. -/
theorem same_phase_cover_probability [Fintype A] [Fintype B]
    (phase : Bool) (S : Finset Site) (slotA : A×Fin 2 ↪ Site) (slotB : B×Fin 2 ↪ Site)
    (hpairA : ∀ a,slotA (a,1)=UnitMatchingTranslation.partner phase (slotA (a,0)))
    (hpairB : ∀ b,slotB (b,1)=UnitMatchingTranslation.partner phase (slotB (b,0)))
    (hcoverA : ∀ v∈S,∃ ai,slotA ai=v) (hcoverB : ∀ v∈S,∃ bi,slotB bi=v)
    (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (E : Configuration→Prop)
    (hlocal : ∀ ω η,Set.EqOn ω η S → (E ω↔E η)) :
    manyProbability (fun _ : A => p) (fun ω => E (pairDecode slotA ω))=
      manyProbability (fun _ : B => p) (fun ω => E (pairDecode slotB ω)) :=
  (cover_probability phase S slotA hpairA hcoverA p hp0 hp1 E hlocal).trans
    (cover_probability phase S slotB hpairB hcoverB p hp0 hp1 E hlocal).symm

#print axioms manyProbability_embedding
#print axioms same_phase_cover_probability
end
end ExceptionalTimes.MatchingCoverLaw


