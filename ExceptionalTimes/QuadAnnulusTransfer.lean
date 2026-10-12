import ExceptionalTimes.StaticHexApproximation
import ExceptionalTimes.FiniteEventTransfer
import ExceptionalTimes.IndependentSupportExtension
import ExceptionalTimes.LocalAnnulusInput
import ExceptionalTimes.MatchingCoverLaw

/-! Literal finite-word transfer implies the required four-arm transfer.
Finite support changes and two matching phases are handled exactly. The
only approximation input here is the explicitly named static source fact. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.QuadAnnulusTransfer
noncomputable section

open PairSquareSewing CanonicalHexAnnuli StaticHexApproximation
open DimerLaw ManyDimerLaw ActivePartitionLaw EnvironmentVariance ProbeProduct
open IndependentAnnulusInput LocalDimerCalibration LocalAnnulusInput
open AnnulusTransferMixing CalibratedAnnulusMixing

def armSupport (M n : ℕ) : Finset Site :=
  (latticeBox (M*2^n)).filter (fun v => v∈region 0 ((2^n:ℕ):ℤ) ((M*2^n:ℕ):ℤ))

theorem mem_armSupport (M n : ℕ) (v : Site) :
    v∈armSupport M n ↔ v∈region 0 ((2^n:ℕ):ℤ) ((M*2^n:ℕ):ℤ) := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨region_subset_box _ _ h,h⟩

theorem arm_support_local (M n : ℕ) {ω η : Configuration}
    (h : Set.EqOn ω η (armSupport M n)) : armEvent M n ω ↔ armEvent M n η :=
  HexFourArms.congr (fun v hv => h ((mem_armSupport M n v).mpr hv))

/-- NEW dynamical comparison, not an assumed literature result. It is
stated on a concrete positive matching cover, with its actual finite law.
The finite support can be any one returned by the proof (e.g. a fixed box). -/
def NewFiniteWordTransfer (hplane : PublishedInvarianceOfDomain) : Prop :=
  ∀ q : ℕ,∀ T : DyadicQuadFamily (Fin q),∀ word : (Fin q→Bool)→Bool,
    ∀ τ : ℝ,0<τ → ∀ δ : ℝ,0<δ → ∃ N : ℕ,T.maxLevel≤N ∧
      ∀ n,N≤n → ∃ D : Finset Site,polygonFamilySupport (quads hplane T n)⊆D ∧
        ∀ b : Bool,
          |manyProbability (fun _ => refreshProbability (τ/(2*localClock .canonical n)))
            (fun ω => wordEvent T n word (pairDecode (UnitReferenceCover.slot b D) ω))-
            jointProbability D (independentTime τ n) (wordEvent T n word)|≤δ

theorem word_on_sample {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (n M : ℕ) (hn : T.maxLevel≤n)
    (word : (Fin q→Bool)→Bool) (b : Bool) (D : Finset Site)
    (hD : polygonFamilySupport (quads hplane T n)⊆D)
    (t u δ : ℝ) (ht : 0≤t) (hu : 0≤u)
    (hword : |manyProbability (fun _ => refreshProbability t)
      (fun ω => wordEvent T n word (pairDecode (UnitReferenceCover.slot b D) ω))-
      jointProbability D u (wordEvent T n word)|≤δ) :
    |manyProbability (fun _ => refreshProbability t)
      (fun ω => wordEvent T n word (pairDecode (UnitReferenceCover.slot b (sample hplane M n T)) ω))-
      jointProbability (sample hplane M n T) u (wordEvent T n word)|≤δ := by
  let S := polygonFamilySupport (quads hplane T n)
  have hS : S⊆sample hplane M n T := Finset.subset_union_right
  have hlocal : ∀ ω η,Set.EqOn ω η S → (wordEvent T n word ω ↔ wordEvent T n word η) :=
    fun _ _ h => word_local hplane T n hn word h
  have hc := MatchingCoverLaw.same_phase_cover_probability b S
    (UnitReferenceCover.slot b (sample hplane M n T)) (UnitReferenceCover.slot b D)
    (UnitReferenceCover.slot_phase b _) (UnitReferenceCover.slot_phase b _)
    (fun v hv => UnitReferenceCover.slot_covers b _ v (hS hv))
    (fun v hv => UnitReferenceCover.slot_covers b _ v (hD hv))
    (refreshProbability t) (refreshProbability_nonneg ht) (refreshProbability_le_one t)
    (wordEvent T n word) hlocal
  have hi₁ := IndependentSupportExtension.jointProbability_restrict S (sample hplane M n T)
    hS u hu (wordEvent T n word) hlocal
  have hi₂ := IndependentSupportExtension.jointProbability_restrict S D hD u hu
    (wordEvent T n word) hlocal
  rw [hc,hi₁,←hi₂]
  exact hword

theorem annulus_transfer_of_words (hplane : PublishedInvarianceOfDomain)
    (hstatic : PublishedHexQuadApproximation hplane)
    (hclockC : NewClockControl (localClock .canonical))
    (hclockM : NewClockControl (localClock .refresh))
    (hword : NewFiniteWordTransfer hplane) :
    NewCalibratedAnnulusTransfer (localClock .canonical) independentTime := by
  intro M hM τ hτ δ hδ
  obtain ⟨q,T,word,Ns,hNs,hs⟩ := hstatic M hM (δ/8) (by positivity)
  obtain ⟨Nw,hNw,hw⟩ := hword q T word τ hτ (δ/2) (by positivity)
  obtain ⟨Nc,hc,_⟩ := hclockC
  obtain ⟨Nm,hm,_⟩ := hclockM
  let N := max (max Ns Nw) (max Nc Nm)
  refine ⟨N,?_⟩
  intro n hn b k slot hp hcover
  have hns : Ns≤n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnw : Nw≤n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnc : Nc≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnm : Nm≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have ht : 0≤τ/(2*localClock .canonical n) :=
    div_nonneg hτ.le (mul_nonneg (by norm_num) (hc n hnc).le)
  have hu : 0≤ independentTime τ n :=
    div_nonneg hτ.le (mul_nonneg (by norm_num) (hm n hnm).le)
  obtain ⟨D,hD,hwD⟩ := hw n hnw
  let Λ := sample hplane M n T
  let e := UnitReferenceCover.slot b Λ
  have hE : ∀ ω η,Set.EqOn ω η Λ → (armEvent M n ω ↔ armEvent M n η) := by
    intro ω η he
    exact arm_local M n (fun _ hv => he (Finset.mem_union_left _ hv))
  have hF : ∀ ω η,Set.EqOn ω η Λ → (wordEvent T n word ω ↔ wordEvent T n word η) := by
    intro ω η he
    exact word_local hplane T n (hNs.trans hns) word
      (fun _ hv => he (Finset.mem_union_right _ hv))
  have hwΛ := word_on_sample hplane T n M (hNw.trans hnw) word b D hD
    (τ/(2*localClock .canonical n)) (independentTime τ n) (δ/2) ht hu (hwD b)
  have he := FiniteEventTransfer.transfer e Λ (UnitReferenceCover.slot_covers b Λ)
    (armEvent M n) (wordEvent T n word) hE hF _ _ ht hu (δ/8) (δ/2) (hs n hns) hwΛ
  have hsupport : armSupport M n⊆Λ := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_filter.mp hv).1
  have hmatch := MatchingCoverLaw.same_phase_cover_probability b (armSupport M n) slot e
    hp (UnitReferenceCover.slot_phase b Λ)
    (fun v hv => hcover v ((mem_armSupport M n v).mp hv))
    (fun v hv => UnitReferenceCover.slot_covers b Λ v (hsupport hv))
    (refreshProbability (τ/(2*localClock .canonical n)))
    (refreshProbability_nonneg ht) (refreshProbability_le_one _)
    (armEvent M n) (fun _ _ h => arm_support_local M n h)
  have hi := IndependentSupportExtension.jointProbability_restrict (latticeBox (M*2^n)) Λ
    Finset.subset_union_left (independentTime τ n) hu (armEvent M n)
    (fun _ _ h => arm_local M n h)
  change manyProbability _ (fun ω => armEvent M n (pairDecode slot ω))≤_
  rw [hmatch]
  change _≤jointProbability (latticeBox (M*2^n)) (independentTime τ n) (armEvent M n)+δ
  rw [←hi]
  linarith [(abs_le.mp he).2]

#print axioms annulus_transfer_of_words
end
end ExceptionalTimes.QuadAnnulusTransfer
