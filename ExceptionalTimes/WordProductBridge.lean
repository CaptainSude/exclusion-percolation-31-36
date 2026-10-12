import ExceptionalTimes.QuadAnnulusTransfer
import ExceptionalTimes.DimerProbabilityDictionary
import ExceptionalTimes.ClockVanishing

/-! Exact conversion of actual semigroup product limits into the concrete
finite-word transfer used by the dimension theorem. -/
open Filter
open scoped Classical Topology
namespace ExceptionalTimes.WordProductBridge
noncomputable section
open PairSquareSewing StaticHexApproximation QuadAnnulusTransfer
open DimerLaw DimerExpansion CenteredBlocks DimerProbabilityDictionary
open IndependentAnnulusInput LocalDimerCalibration LocalAnnulusInput AnnulusTransferMixing

abbrev localScale (rule : Rule) (n : ℕ) : ℝ := (mesh n)^2/localS rule n

theorem localScale_positive (rule : Rule) (h : NewClockControl (localClock rule)) :
    ∀ᶠ n in atTop,0<localScale rule n := by
  obtain ⟨N,hN,_⟩ := h
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [show localScale rule n=1/(2*localClock rule n) from by
    simpa only [one_mul] using (local_clock_time rule n 1).symm]
  exact div_pos (by norm_num) (mul_pos (by norm_num) (hN n hn))

def wordTest {q : ℕ} (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool)
    (D : Finset Site) (phase : Bool) (n : ℕ) :=
  pairedTest (UnitReferenceCover.slot phase D) (wordEvent T n word)

theorem word_transfer_of_kernel_limits (hplane : PublishedInvarianceOfDomain)
    (hclock : ∀ r,NewClockControl (localClock r))
    (hlimit : ∀ q : ℕ,∀ T : DyadicQuadFamily (Fin q),∀ word : (Fin q→Bool)→Bool,
      ∀ τ : ℝ,0<τ → ∃ D : ℕ→Finset Site,
        (∀ᶠ n in atTop,polygonFamilySupport (quads hplane T n)⊆D n) ∧
        ∀ phase : Bool,Tendsto (fun n =>
          kernel (fun _ : UnitReferenceCover.anchors phase (D n) =>
            canonicalLaw (τ*localScale .canonical n)) (wordTest T word (D n) phase n)-
          kernel (fun _ : UnitReferenceCover.anchors phase (D n) =>
            refreshLaw (τ*localScale .refresh n)) (wordTest T word (D n) phase n))
          atTop (𝓝 0)) : NewFiniteWordTransfer hplane := by
  intro q T word τ hτ δ hδ
  obtain ⟨D,hD,hlim⟩ := hlimit q T word τ hτ
  have hsmall : ∀ᶠ n in atTop,∀ phase : Bool,
      |kernel (fun _ : UnitReferenceCover.anchors phase (D n) =>
          canonicalLaw (τ*localScale .canonical n)) (wordTest T word (D n) phase n)-
        kernel (fun _ : UnitReferenceCover.anchors phase (D n) =>
          refreshLaw (τ*localScale .refresh n)) (wordTest T word (D n) phase n)|<δ := by
    rw [Filter.eventually_all]
    intro phase
    have h := (hlim phase).abs.eventually (gt_mem_nhds (by simpa only [abs_zero] using hδ))
    simpa only [abs_zero] using h
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (hsmall.and (hD.and ((localScale_positive .canonical (hclock .canonical)).and
      (localScale_positive .refresh (hclock .refresh)))))
  refine ⟨max T.maxLevel N,le_max_left _ _,?_⟩
  intro n hn
  have hn' := hN n ((le_max_right _ _).trans hn)
  have hlev : T.maxLevel≤n := (le_max_left _ _).trans hn
  refine ⟨D n,hn'.2.1,?_⟩
  intro phase
  have hloc : ∀ ω η,Set.EqOn ω η (D n) → (wordEvent T n word ω↔wordEvent T n word η) := by
    intro ω η h
    apply word_local hplane T n hlev word
    intro v hv
    exact h (hn'.2.1 hv)
  have hC := canonical_probability (UnitReferenceCover.slot phase (D n)) (wordEvent T n word)
    (τ*localScale .canonical n) (mul_pos hτ hn'.2.2.1).le
  have hM := refresh_probability (UnitReferenceCover.slot phase (D n)) (D n)
    (UnitReferenceCover.slot_covers phase (D n)) (wordEvent T n word) hloc
    (τ*localScale .refresh n) (mul_pos hτ hn'.2.2.2).le
  have htime : (τ*localScale .refresh n)/2=independentTime τ n := by
    rw [show τ*localScale .refresh n=τ/(2*localClock .refresh n) from
      by simpa only [localScale,mul_div_assoc] using (local_clock_time .refresh n τ).symm]
    unfold independentTime
    ring
  rw [htime] at hM
  have h := (hn'.1 phase).le
  change |kernel _ (pairedTest _ _)-kernel _ (pairedTest _ _)|≤δ at h
  rw [hC,hM] at h
  rw [local_clock_time .canonical n τ]
  simpa only [localScale,mul_div_assoc] using h

#print axioms word_transfer_of_kernel_limits
end
end ExceptionalTimes.WordProductBridge
