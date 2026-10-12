import Mathlib.Dynamics.Ergodic.Ergodic

/-! A measurable conull set of good samples can be made exactly invariant
under an invertible measure-preserving map by taking all integer translates. -/

open MeasureTheory Set Function
open scoped Classical

namespace ExceptionalTimes.InvariantConullCore

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem exists_invariant_conull_subset (e : Ω ≃ᵐ Ω) (he : MeasurePreserving e μ μ)
    (p : Ω → Prop) (hp : ∀ᵐ ω ∂μ, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ ω ∂μ, ω ∈ G) ∧
      (∀ ω ∈ G, p ω) ∧ (∀ ω, e ω ∈ G ↔ ω ∈ G) := by
  obtain ⟨N,hN,hNm,hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  let A := Nᶜ
  have hAm : MeasurableSet A := hNm.compl
  have hAae : ∀ᵐ ω ∂μ, ω ∈ A := by
    rw [ae_iff]
    simpa [A] using hNzero
  have hAp : ∀ ω ∈ A, p ω := by
    intro ω hω
    by_contra hbad
    exact hω (hN hbad)
  let G : Set Ω := {ω | ∀ n : ℕ, e^[n] ω ∈ A ∧ e.symm^[n] ω ∈ A}
  have hGm : MeasurableSet G := by
    simp only [G,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    exact ((he.measurable.iterate n) hAm).inter ((e.symm.measurable.iterate n) hAm)
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := by
    apply ae_all_iff.mpr
    intro n
    exact ((he.iterate n).quasiMeasurePreserving.ae hAae).and
      (((he.symm e).iterate n).quasiMeasurePreserving.ae hAae)
  have hforward : ∀ ω ∈ G, e ω ∈ G := by
    intro ω hω n
    constructor
    · simpa only [Function.iterate_succ_apply] using (hω (n+1)).1
    · cases n with
      | zero => simpa using (hω 1).1
      | succ n => simpa only [Function.iterate_succ_apply,MeasurableEquiv.symm_apply_apply] using (hω n).2
  have hbackward : ∀ ω ∈ G, e.symm ω ∈ G := by
    intro ω hω n
    constructor
    · cases n with
      | zero => simpa using (hω 1).2
      | succ n => simpa only [Function.iterate_succ_apply,MeasurableEquiv.apply_symm_apply] using (hω n).1
    · simpa only [Function.iterate_succ_apply] using (hω (n+1)).2
  refine ⟨G,hGm,hGae,fun ω hω => hAp ω ?_,?_⟩
  · simpa using (hω 0).1
  · intro ω
    exact ⟨fun h => by simpa only [MeasurableEquiv.symm_apply_apply] using hbackward (e ω) h,
      hforward ω⟩

#print axioms exists_invariant_conull_subset

end ExceptionalTimes.InvariantConullCore
