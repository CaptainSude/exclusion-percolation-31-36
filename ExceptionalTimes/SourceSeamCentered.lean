import ExceptionalTimes.SourceSeamInputs
import ExceptionalTimes.CenteredBlocks
import ExceptionalTimes.LocalProductLaw

/-! Full centered-history support for the k-insertion source adaptation.
The sum is kept signed until every necessary arm probe is recovered. -/

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing
open DimerBinaryResponse EnvironmentVariance CenteredBlocks

variable {I : Type*} [Fintype I] {H : I → Type*} [∀ i, Fintype (H i)]
noncomputable local instance : DecidableEq I := Classical.decEq _

noncomputable def multiPairResponse (w : ∀ i, H i → ℝ)
    (K : Kernel) (A : (∀ i, H i) → TwoTimeConfiguration) (x z : Site)
    (F : TwoTimeConfiguration → ℝ) : ℝ :=
  kernel w (fun h => rawPairResponse K (A h) x z F)

noncomputable def multiSquareResponse (w : ∀ i, H i → ℝ)
    (D : Finset Site) (A : (∀ i, H i) → TwoTimeConfiguration)
    (F : TwoTimeConfiguration → ℝ) : ℝ :=
  kernel w (fun h => rawSquareResponse D (A h) F)

theorem no_arm_pair_tests_constant {Q : Type*} (quads : Q → GraphQuad)
    (P : Probe) (ω : Configuration) (A B : TwoTimeConfiguration) (x z : Site)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hchange : ∀ t, Set.EqOn (A t) (B t) P.pocketᶜ)
    (hA : ∀ t, Set.EqOn (A t) ω P.region)
    (hB : ∀ t, Set.EqOn (B t) ω P.region)
    (hx : x ∉ P.region) (hz : x+z ∉ P.region) (hna : ¬ FourArms P ω) :
    ∀ a b q t, (quads q).test (pairHistory A x z a b t)=
      (quads q).test (pairHistory B x z a b t) := by
  intro a b q t
  apply not_not.mp
  intro hne
  apply hna
  apply hlocal q ω _ _ _ _ _ hne
  · intro v hv
    cases t <;> exact putPair_congr_on _ _ x z _ _ _ (hchange _) hv
  · intro v hv
    have hvx : v≠x := fun he => hx (he ▸ hv)
    have hvz : v≠x+z := fun he => hz (he ▸ hv)
    cases t <;> simpa [pairHistory,putPair,hvx,hvz] using hA _ hv
  · intro v hv
    have hvx : v≠x := fun he => hx (he ▸ hv)
    have hvz : v≠x+z := fun he => hz (he ▸ hv)
    cases t <;> simpa [pairHistory,putPair,hvx,hvz] using hB _ hv

theorem no_arm_square_tests_constant {Q : Type*} (quads : Q → GraphQuad)
    (P : Probe) (ω : Configuration) (A B : TwoTimeConfiguration) (D : Finset Site)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hchange : ∀ t, Set.EqOn (A t) (B t) P.pocketᶜ)
    (hA : ∀ t, Set.EqOn (A t) ω P.region)
    (hB : ∀ t, Set.EqOn (B t) ω P.region)
    (hD : ∀ v ∈ D, v ∉ P.region) (hna : ¬ FourArms P ω) :
    ∀ a q t, (quads q).test (squareHistory D A a t)=
      (quads q).test (squareHistory D B a t) := by
  intro a q t
  apply not_not.mp
  intro hne
  apply hna
  apply hlocal q ω _ _ _ _ _ hne
  · exact force_congr_on D _ _ _ _ (hchange t)
  · intro v hv
    have hvD : v ∉ D := fun h => hD v h hv
    simpa [squareHistory,force,hvD] using hA t hv
  · intro v hv
    have hvD : v ∉ D := fun h => hD v h hv
    simpa [squareHistory,force,hvD] using hB t hv

/-- Every OTHER centered insertion has its raw fair-field four-arm probe,
although the first insertion is still a jointly integrated two-site update.
No absolute value or sum over settings precedes this cancellation. -/
theorem multi_pair_nonzero_other_arms {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (w : ∀ i, H i → ℝ) (K : Kernel)
    (A : (∀ i, H i) → TwoTimeConfiguration) (x z : Site) (ω : Configuration)
    (P : I → Probe) (hw : ∀ i, ∑ h, w i h=0)
    (hlocal : ∀ i q, LocalChangeArms (quads q) (P i))
    (hchange : ∀ i h a t, Set.EqOn (A (Function.update h i a) t) (A h t) (P i).pocketᶜ)
    (hfrozen : ∀ i h t, Set.EqOn (A h t) ω (P i).region)
    (hx : ∀ i, x ∉ (P i).region) (hz : ∀ i, x+z ∉ (P i).region)
    (hne : multiPairResponse w K A x z (fun ξ => outer (crossingVector quads ξ)) ≠ 0) :
    ∀ i, FourArms (P i) ω := by
  intro i
  by_contra hna
  apply hne
  apply kernel_zero_of_block_constant w _ i (hw i)
  intro h a
  have ht := no_arm_pair_tests_constant quads (P i) ω (A (Function.update h i a))
    (A h) x z (hlocal i) (hchange i h a) (hfrozen i _) (hfrozen i h) (hx i) (hz i) hna
  have hv : ∀ before after, crossingVector quads (pairHistory (A (Function.update h i a)) x z before after)=
      crossingVector quads (pairHistory (A h) x z before after) := by
    intro before after
    funext qt
    exact ht before after qt.1 qt.2
  simp only [rawPairResponse,hv]

theorem multi_square_nonzero_other_arms {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (w : ∀ i, H i → ℝ) (D : Finset Site)
    (A : (∀ i, H i) → TwoTimeConfiguration) (ω : Configuration)
    (P : I → Probe) (hw : ∀ i, ∑ h, w i h=0)
    (hlocal : ∀ i q, LocalChangeArms (quads q) (P i))
    (hchange : ∀ i h a t, Set.EqOn (A (Function.update h i a) t) (A h t) (P i).pocketᶜ)
    (hfrozen : ∀ i h t, Set.EqOn (A h t) ω (P i).region)
    (hD : ∀ i v, v ∈ D → v ∉ (P i).region)
    (hne : multiSquareResponse w D A (fun ξ => outer (crossingVector quads ξ)) ≠ 0) :
    ∀ i, FourArms (P i) ω := by
  intro i
  by_contra hna
  apply hne
  apply kernel_zero_of_block_constant w _ i (hw i)
  intro h a
  have ht := no_arm_square_tests_constant quads (P i) ω (A (Function.update h i a))
    (A h) D (hlocal i) (hchange i h a) (hfrozen i _) (hfrozen i h) (hD i) hna
  have hv : ∀ c, crossingVector quads (squareHistory D (A (Function.update h i a)) c)=
      crossingVector quads (squareHistory D (A h) c) := by
    intro c
    funext qt
    exact ht c qt.1 qt.2
  simp only [rawSquareResponse,hv]

/-- Pointwise successful exchanges commute with the entire signed product
sum. The other histories are held fixed by the exchange, then summed. -/
theorem multi_successful_signed_exchange (w : ∀ i, H i → ℝ) (K : Kernel)
    (D : Finset Site) (x z : Site)
    (A A' : (∀ i, H i) → TwoTimeConfiguration) (B B' : TwoTimeConfiguration)
    (F G : TwoTimeConfiguration → ℝ)
    (h : ∀ c, rawPairResponse K (A c) x z F * rawSquareResponse D B G =
      rawSquareResponse D (A' c) F * rawPairResponse K B' x z G) :
    multiPairResponse w K A x z F * rawSquareResponse D B G =
      multiSquareResponse w D A' F * rawPairResponse K B' x z G := by
  unfold multiPairResponse multiSquareResponse kernel
  simp only [Finset.sum_mul,mul_assoc,h]

#print axioms multi_pair_nonzero_other_arms
#print axioms multi_square_nonzero_other_arms
#print axioms multi_successful_signed_exchange


/-- The two fair fields are exactly a product of independent two-bit site
coordinates. This bijection is only a rearrangement of the original law. -/
def sourcePairCoordinates {Λ : Finset Site} : Sources Λ ≃ (↥Λ → Bool × Bool) where
  toFun ω v := (ω.1 v,ω.2 v)
  invFun ξ := (fun v => (ξ v).1,fun v => (ξ v).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem source_expect_pairCoordinates {Λ : Finset Site} (F : Sources Λ → ℝ) :
    (sourceLaw Λ).expect F =
      (FiniteLaw.pi (fun _ : ↥Λ => ProbeProduct.fairBit.prod ProbeProduct.fairBit)).expect
        (fun ξ => F (sourcePairCoordinates.symm ξ)) := by
  unfold FiniteLaw.expect
  rw [← (sourcePairCoordinates (Λ := Λ)).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro ξ _
  congr 1
  change (∏ v : ↥Λ, ProbeProduct.fairBit.weight (ξ v).1) *
      (∏ v : ↥Λ, ProbeProduct.fairBit.weight (ξ v).2) =
    ∏ v : ↥Λ, (ProbeProduct.fairBit.prod ProbeProduct.fairBit).weight (ξ v)
  simp only [FiniteLaw.prod,Finset.prod_mul_distrib]

/-- Events on disjoint actual finite site sets factor for the original two
independent fair source fields. No new probabilistic independence premise. -/
theorem source_local_product {Λ : Finset Site} {J : Type*} [Fintype J] [DecidableEq J]
    (S : J → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (E : J → Sources Λ → Prop)
    (hlocal : ∀ j ω η, (∀ v ∈ S j, ω.1 v=η.1 v ∧ ω.2 v=η.2 v) → (E j ω ↔ E j η)) :
    probability (sourceLaw Λ) (fun ω => ∀ j, E j ω) =
      ∏ j, probability (sourceLaw Λ) (E j) := by
  simp only [probability,source_expect_pairCoordinates]
  apply LocalProductLaw.pi_local_product _ (false,false) S hdis
  intro j ω η heq
  apply hlocal
  intro v hv
  exact ⟨congrArg Prod.fst (heq hv),congrArg Prod.snd (heq hv)⟩

/-- Exact recovery of all OTHER insertion costs. The first event can be
the literal failed-seam event (including its two raw first-point probes).
All extra events are kept until the signed full sum has forced them. -/
theorem source_failure_product_bound {Λ : Finset Site}
    (S : Option I → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (E : Option I → Sources Λ → Prop)
    (hlocal : ∀ j ω η, (∀ v ∈ S j, ω.1 v=η.1 v ∧ ω.2 v=η.2 v) → (E j ω ↔ E j η))
    (c : ℝ) (cost : I → ℝ)
    (hfirst : probability (sourceLaw Λ) (E none) ≤ c)
    (hother : ∀ i, probability (sourceLaw Λ) (E (some i)) ≤ cost i) :
    probability (sourceLaw Λ) (fun ω => E none ω ∧ ∀ i, E (some i) ω) ≤
      c * ∏ i, cost i := by
  have he : probability (sourceLaw Λ) (fun ω => E none ω ∧ ∀ i, E (some i) ω) =
      probability (sourceLaw Λ) (fun ω => ∀ j, E j ω) := by
    apply ProbeProduct.probability_congr
    intro ω
    constructor
    · rintro ⟨hn,hs⟩ j
      cases j with
      | none => exact hn
      | some i => exact hs i
    · intro hall
      exact ⟨hall none,fun i => hall (some i)⟩
  rw [he,source_local_product S hdis E hlocal,Fintype.prod_option]
  apply mul_le_mul hfirst
  · exact Finset.prod_le_prod₀ (fun i _ => probability_nonneg _ _) (fun i _ => hother i)
  · exact Finset.prod_nonneg (fun i _ => probability_nonneg _ _)
  · exact (probability_nonneg _ _).trans hfirst

#print axioms source_failure_product_bound


/-- Agreement on finite source coordinates gives agreement of their
completed fields on any region whose visible coordinates are included. -/
theorem source_complete_eqOn {Λ : Finset Site} {ω η : Sources Λ}
    (S : Set ↥Λ) (R : Set Site)
    (heq : ∀ v ∈ S, ω.1 v=η.1 v ∧ ω.2 v=η.2 v)
    (hR : ∀ v : ↥Λ, (v : Site) ∈ R → v ∈ S) :
    Set.EqOn (complete ω.1) (complete η.1) R ∧
      Set.EqOn (complete ω.2) (complete η.2) R := by
  constructor <;> intro v hv <;> by_cases hvΛ : v ∈ Λ
  · simpa only [complete,dite_eq_left hvΛ] using (heq ⟨v,hvΛ⟩ (hR ⟨v,hvΛ⟩ hv)).1
  · simp only [complete,dite_eq_right hvΛ]
  · simpa only [complete,dite_eq_left hvΛ] using (heq ⟨v,hvΛ⟩ (hR ⟨v,hvΛ⟩ hv)).2
  · simp only [complete,dite_eq_right hvΛ]

def SourceOrientedE {Λ : Finset Site} (mic sq : Probe) (reverse : Bool) (ω : Sources Λ) : Prop :=
  if reverse then SourceE mic sq (complete ω.2) (complete ω.1)
  else SourceE mic sq (complete ω.1) (complete ω.2)

/-- Source06's first-point failure estimate acquires the OTHER insertion
arm factors by exact independence of disjoint raw finite coordinates.
This theorem never changes the mixed normalization a_e*a_e,h. -/
theorem source_failed_other_arms_bound {Λ : Finset Site} {n : ℕ}
    (layouts : Fin n → SourceSeamLayout) (mic sq : Probe) (other : I → Probe)
    (S : Option I → Set ↥Λ) (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (htrial : ∀ j (v : ↥Λ), (v : Site) ∈ (layouts j).support → v ∈ S none)
    (hmic : ∀ v : ↥Λ, (v : Site) ∈ mic.region → v ∈ S none)
    (hsq : ∀ v : ↥Λ, (v : Site) ∈ sq.region → v ∈ S none)
    (hregion : ∀ i (v : ↥Λ), (v : Site) ∈ (other i).region → v ∈ S (some i))
    (a b ε : ℝ) (cost : I → ℝ)
    (hfailure : SourceFixedSquareFailure (Λ := Λ) layouts mic sq a b ε)
    (hstatic : ∀ i, probability (sourceLaw Λ) (fun ω => FourArms (other i) (complete ω.1)) ≤ cost i)
    (reverse : Bool) :
    probability (sourceLaw Λ) (fun ω =>
      (AdaptiveExchange.select (fun j => (layouts j).success) (List.finRange n) ω=none ∧
        SourceOrientedE mic sq reverse ω) ∧ ∀ i, FourArms (other i) (complete ω.1)) ≤
      (ε*(a*b)) * ∏ i, cost i := by
  let E : Option I → Sources Λ → Prop := fun j ω => match j with
    | none => AdaptiveExchange.select (fun k => (layouts k).success) (List.finRange n) ω=none ∧
        SourceOrientedE mic sq reverse ω
    | some i => FourArms (other i) (complete ω.1)
  apply source_failure_product_bound S hdis E
  · intro j ω η heq
    cases j with
    | some i => exact fourArms_congr (other i) (source_complete_eqOn _ _ heq (hregion i)).1
    | none =>
      have htest : ∀ k, (layouts k).success ω=(layouts k).success η := by
        intro k
        exact (layouts k).success_supported ω η (fun v hv => heq v (htrial k v hv))
      have hselect : AdaptiveExchange.select (fun k => (layouts k).success) (List.finRange n) ω =
          AdaptiveExchange.select (fun k => (layouts k).success) (List.finRange n) η := by
        unfold AdaptiveExchange.select
        congr 1
        funext k
        exact htest k
      have hm := source_complete_eqOn _ _ heq hmic
      have hs := source_complete_eqOn _ _ heq hsq
      change (_ ∧ SourceOrientedE mic sq reverse ω) ↔ (_ ∧ SourceOrientedE mic sq reverse η)
      rw [hselect]
      apply and_congr Iff.rfl
      cases reverse
      · exact and_congr (fourArms_congr mic hm.1) (fourArms_congr sq hs.2)
      · exact and_congr (fourArms_congr mic hm.2) (fourArms_congr sq hs.1)
  · cases reverse
    · exact hfailure
    · change probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select (fun j => (layouts j).success) (List.finRange n) ω=none ∧
        SourceE mic sq (complete ω.2) (complete ω.1)) ≤ ε*(a*b)
      rw [source_failure_symmetry _ _ (fun j => (layouts j).success_swap) mic sq]
      exact hfailure
  · exact hstatic

#print axioms source_failed_other_arms_bound

end ExceptionalTimes.PairSquareSewing


