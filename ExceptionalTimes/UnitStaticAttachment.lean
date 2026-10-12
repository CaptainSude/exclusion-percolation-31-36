import ExceptionalTimes.UnitGadgetNecklace
import ExceptionalTimes.SourceSampling

/-! A narrow ORDINARY static attachment consequence of arm separation,
RSW and finite energy (Nolin 0711.4948v1, Section 4.5), with the fixed
shape/cut comparison of source02. This is a conventional deduction,
not a verbatim quoted theorem. Its source deduction is outside Lean:
four separated alternating connections attach the checked finite collar
to Q0's two terminal and two dual sides; Jordan separation reads its
inner join for every assignment of the two free sites. The input below
has one iid fair field and one-time tests only. It contains no swap law,
signed response, jump rate or calibration statement. Those are derived.
-/

open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.UnitStaticAttachment
noncomputable section
open DimerBinaryResponse EnvironmentVariance ProbeProduct UnitProjectionGadget

def localTest (x : Site) (ω : Configuration) : Bool :=
  (necklace.joinQuad (latticeBox 2)).test (fun w => ω (x+w))

def ForcedAt (x : Site) (ω : Configuration) : Prop := Forced (fun w => ω (x+w))

theorem putPair_translate (ω : Configuration) (x : Site) (a b : Bool) :
    (fun w => putPair ω x (1,0) a b (x+w))=
      putPair (fun w => ω (x+w)) (0,0) (1,0) a b := by
  funext w
  simp [putPair,Function.update_apply,
    show (0,0)=(0 : Site) by rfl]

theorem localTest_forced (x : Site) (ω : Configuration) (hω : ForcedAt x ω)
    (a b : Bool) : localTest x (putPair ω x (1,0) a b)=a := by
  unfold localTest
  rw [putPair_translate]
  exact forced_necklace_test _ hω a b

/-- The outside arm attachment reads the literal finite inner join.
This is a one-time statement under each of the four free-site assignments. -/
def ReadsLocal (Q : PolygonQuad) (x : Site) (ω : Configuration) : Prop :=
  ∀ a b : Bool,Q.test (putPair ω x (1,0) a b)=localTest x (putPair ω x (1,0) a b)

def Attached (Q : PolygonQuad) (x : Site) (ω : Configuration) : Prop :=
  ForcedAt x ω ∧ ReadsLocal Q x ω

theorem attached_projection (Q : PolygonQuad) (x : Site) (ω : Configuration)
    (h : Attached Q x ω) (a b : Bool) : Q.test (putPair ω x (1,0) a b)=a :=
  (h.2 a b).trans (localTest_forced x ω h.1 a b)

theorem attached_canonical_response (Q : PolygonQuad) (x : Site) (ω : Configuration)
    (h : Attached Q x ω) : rawPairResponse canonical (fun _ => ω) x (1,0) Q.jump=1/4 := by
  norm_num [rawPairResponse,PolygonQuad.jump,pairHistory,attached_projection Q x ω h,
    canonical,Fintype.sum_bool]

theorem attached_refresh_response (Q : PolygonQuad) (x : Site) (ω : Configuration)
    (h : Attached Q x ω) : rawPairResponse refresh (fun _ => ω) x (1,0) Q.jump=1/4 := by
  norm_num [rawPairResponse,PolygonQuad.jump,pairHistory,attached_projection Q x ω h,
    refresh,Fintype.sum_bool]

theorem pair_jump_nonneg (rule : Rule) (Q : PolygonQuad) (x z : Site) (ω : Configuration) :
    0≤rawPairResponse rule.kernel (fun _ => ω) x z Q.jump := by
  rw [PolygonSewing.pair_jump_half_amplitude]
  cases rule <;> simp only [Rule.amplitude,SignedResponse.canonicalAmplitude,
    SignedResponse.refreshAmplitude] <;> split <;> norm_num

def averagedResponse (rule : Rule) (D : Finset Site) (Q : PolygonQuad) (x : Site) : ℝ :=
  (fairSites D).expect (fun ω => rawPairResponse rule.kernel (fun _ => complete ω) x (1,0) Q.jump)

theorem averagedResponse_nonneg (rule : Rule) (D : Finset Site) (Q : PolygonQuad) (x : Site) :
    0≤averagedResponse rule D Q x :=
  FiniteLaw.expect_nonneg _ (fun ω => pair_jump_nonneg rule Q x (1,0) (complete ω))

theorem raw_response_congr (rule : Rule) (Q : PolygonQuad) (x : Site)
    {ω η : Configuration} (h : Set.EqOn ω η (Q.support : Set Site)) :
    rawPairResponse rule.kernel (fun _ => ω) x (1,0) Q.jump=
      rawPairResponse rule.kernel (fun _ => η) x (1,0) Q.jump := by
  have ht (a b : Bool) : Q.test (putPair ω x (1,0) a b)=Q.test (putPair η x (1,0) a b) :=
    Q.test_congr (putPair_congr_on ω η x (1,0) a b _ h)
  simp only [rawPairResponse,PolygonQuad.jump,pairHistory,Bool.false_eq_true,
    ↓reduceIte,ht]

theorem averagedResponse_restrict (rule : Rule) (D : Finset Site) (Q : PolygonQuad)
    (x : Site) (hQ : Q.support⊆D) :
    averagedResponse rule D Q x=averagedResponse rule Q.support Q x := by
  exact FiniteSiteLaw.fairSites_restrict Q.support D hQ
    (fun ω => rawPairResponse rule.kernel (fun _ => ω) x (1,0) Q.jump)
    (fun _ _ h => raw_response_congr rule Q x (fun v hv => h v hv))

theorem attachment_probability_le_response (rule : Rule) (D : Finset Site)
    (Q : PolygonQuad) (x : Site) :
    probability (fairSites D) (fun ω => Attached Q x (complete ω))/4≤
      averagedResponse rule D Q x := by
  have hpoint (ω : D→Bool) :
      indicator (Attached Q x (complete ω))*(1/4 : ℝ)≤
        rawPairResponse rule.kernel (fun _ => complete ω) x (1,0) Q.jump := by
    by_cases h : Attached Q x (complete ω)
    · cases rule
      · simpa [indicator,h,Rule.kernel] using (attached_canonical_response Q x (complete ω) h).ge
      · simpa [indicator,h,Rule.kernel] using (attached_refresh_response Q x (complete ω) h).ge
    · simpa [indicator,h] using pair_jump_nonneg rule Q x (1,0) (complete ω)
  have hh := (fairSites D).expect_mono hpoint
  rw [FiniteLaw.expect_mul_const] at hh
  simpa only [div_eq_mul_inv,one_div,one_mul,probability,averagedResponse] using hh

/-- Fixed central subrectangle of the ACTUAL Euclidean Q0. -/
def Bulk (e : ℝ) (x : Site) : Prop :=
  |(position e x).re|≤1/4 ∧ |(position e x).im|≤1/8

def collarSites (x : Site) : Finset Site := (latticeBox 3).image (fun w => x+w)

def attachmentSample (Q : PolygonQuad) (x : Site) : Finset Site := Q.support ∪ collarSites x

/-- Conventional static arm-attachment consequence; see the module scope
note. The free pair and the complete finite collar are explicit and fixed.
The mesh threshold precedes the choice of every bulk lattice location. -/
def PublishedUnitAttachment (B0 : ℝ) : Prop :=
  128≤B0 ∧ ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℝ,∀ he : 0<e,e<e0 → ∀ hB : 0<B0,∀ hsmall : 4*(B0*e)<1,
      ∀ x : Site,Bulk e x →
        c*sourceArmCost e (B0*e) he (mul_pos hB he) hsmall ≤
          probability (fairSites (attachmentSample (sourceReferenceAt e he 0) x))
            (fun ω => Attached (sourceReferenceAt e he 0) x (complete ω))

theorem published_local_response (B0 : ℝ) (h : PublishedUnitAttachment B0) :
    ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧
      ∀ e : ℝ,∀ he : 0<e,e<e0 → ∀ hsmall : 4*(B0*e)<1,
        ∀ x : Site,Bulk e x → ∀ rule : Rule,
          c*sourceArmCost e (B0*e) he (mul_pos (by linarith [h.1]) he) hsmall ≤
            averagedResponse rule (attachmentSample (sourceReferenceAt e he 0) x)
              (sourceReferenceAt e he 0) x := by
  obtain ⟨hB,c,hc,e0,he0,hA⟩ := h
  refine ⟨c/4,by positivity,e0,he0,?_⟩
  intro e he hee hsmall x hx rule
  have ha := hA e he hee (by linarith) hsmall x hx
  have hb := attachment_probability_le_response rule
    (attachmentSample (sourceReferenceAt e he 0) x) (sourceReferenceAt e he 0) x
  linarith

/-- The finite cover may be any cover of the reference test; auxiliary
collar sites are introduced and summed out by the proved iid law. -/
theorem published_local_response_any_cover (B0 : ℝ) (h : PublishedUnitAttachment B0) :
    ∃ c : ℝ,0<c ∧ ∃ e0 : ℝ,0<e0 ∧
      ∀ e : ℝ,∀ he : 0<e,e<e0 → ∀ hsmall : 4*(B0*e)<1,
        ∀ x : Site,Bulk e x → ∀ rule : Rule,∀ D : Finset Site,
          (sourceReferenceAt e he 0).support⊆D →
          c*sourceArmCost e (B0*e) he (mul_pos (by linarith [h.1]) he) hsmall ≤
            averagedResponse rule D (sourceReferenceAt e he 0) x := by
  obtain ⟨c,hc,e0,he0,hbound⟩ := published_local_response B0 h
  refine ⟨c,hc,e0,he0,?_⟩
  intro e he hee hsmall x hx rule D hD
  have hb := hbound e he hee hsmall x hx rule
  rw [averagedResponse_restrict rule _ _ _
    (show (sourceReferenceAt e he 0).support⊆attachmentSample (sourceReferenceAt e he 0) x
      from Finset.subset_union_left)] at hb
  rwa [averagedResponse_restrict rule D _ _ hD]

#print axioms attached_canonical_response
#print axioms attachment_probability_le_response
#print axioms published_local_response
#print axioms published_local_response_any_cover
end
end ExceptionalTimes.PairSquareSewing.UnitStaticAttachment
