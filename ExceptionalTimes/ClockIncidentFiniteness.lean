import ExceptionalTimes.FiniteClockSlices
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! Summability of incident rates gives almost-sure local finiteness of
actual incident marks, directly from the original count-cylinder law. -/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ExceptionalTimes.ClockIncidentFiniteness

open FiniteClockSlices

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem count_zero_probability (P : PoissonGraphicalRealization μ rate)
    (e : Sym2 Site) (T : ℝ) (hT : 0 < T) :
    μ {ω | (P.clocks ω).markCount e 0 T = 0} = ENNReal.ofReal (Real.exp (-(rate e*T))) := by
  let tests : ClockTests 1 := {
    edge := fun _ => e
    start := fun _ => 0
    finish := fun _ => T
    start_nonneg := fun _ => le_refl 0
    nonempty := fun _ => hT
    disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim }
  simpa [tests,poissonMass] using
    P.independent_law ∅ (fun _ => false) 1 tests (fun _ => 0)

theorem count_nonzero_probability_le (P : PoissonGraphicalRealization μ rate)
    (e : Sym2 Site) (T : ℝ) (hT : 0 < T) :
    μ {ω | (P.clocks ω).markCount e 0 T ≠ 0} ≤ ENNReal.ofReal (rate e*T) := by
  let := P.independent_law.isProbabilityMeasure
  have hm : MeasurableSet {ω | (P.clocks ω).markCount e 0 T = 0} :=
    (P.measurable_counts e 0 T) (measurableSet_singleton 0)
  change μ {ω | (P.clocks ω).markCount e 0 T = 0}ᶜ ≤ _
  rw [prob_compl_eq_one_sub hm,
    count_zero_probability P e T hT,← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.one_sub_le_exp_neg (rate e*T)]

theorem ae_finite_incident_partners (P : PoissonGraphicalRealization μ rate)
    (hsum : ∀ v, Summable (fun w => rate s(v,w))) (v : Site) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂μ, {w | (P.clocks ω).markCount s(v,w) 0 T ≠ 0}.Finite := by
  apply ae_finite_setOfPred_mem
  exact ne_top_of_le_ne_top ((hsum v).mul_right T).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum (fun w => count_nonzero_probability_le P s(v,w) T hT))

theorem finite_incident_marks_of_finite_partners (C : ClockField)
    (hc : C.FiniteEdgeCounts) (v : Site) (T : ℝ)
    (H : {w | C.markCount s(v,w) 0 T ≠ 0}.Finite) :
    {p : ℝ × Site | C.Rings v p.2 p.1 ∧ p.1 ≤ T}.Finite := by
  have hfin := H.biUnion (fun w _ => (hc s(v,w) T).image (fun t => (t,w)))
  apply hfin.subset
  intro p hp
  apply Set.mem_iUnion.mpr ⟨p.2,?_⟩
  apply Set.mem_iUnion.mpr ⟨?_,?_⟩
  · change (C.marks s(v,p.2) ∩ Ioc 0 T).ncard ≠ 0
    rw [ne_eq,Set.ncard_eq_zero (hc s(v,p.2) T)]
    exact Set.nonempty_iff_ne_empty.mp ⟨p.1,hp.1,hp.1.pos,hp.2⟩
  · exact ⟨p.1,⟨hp.1,hp.1.pos,hp.2⟩,rfl⟩

theorem ae_locallyFiniteIncident (P : PoissonGraphicalRealization μ rate)
    (hsum : ∀ v, Summable (fun w => rate s(v,w))) :
    ∀ᵐ ω ∂μ, (P.clocks ω).LocallyFiniteIncident := by
  have H : ∀ᵐ ω ∂μ, ∀ v : Site, ∀ n : ℕ,
      {w | (P.clocks ω).markCount s(v,w) 0 (n+1) ≠ 0}.Finite := by
    rw [ae_all_iff]
    intro v
    rw [ae_all_iff]
    intro n
    exact ae_finite_incident_partners P hsum v (n+1) (by positivity)
  filter_upwards [H] with ω hω
  intro v T
  obtain ⟨n,hn⟩ := exists_nat_gt T
  apply (finite_incident_marks_of_finite_partners (P.clocks ω)
    (P.finiteEdgeCounts ω) v (n+1) (hω v n)).subset
  intro p hp
  exact ⟨hp.1,by linarith [hp.2]⟩

theorem ae_locallyFiniteIncident_kernel (k : RateKernel)
    (P : PoissonGraphicalRealization μ k.unorderedPairRate) :
    ∀ᵐ ω ∂μ, (P.clocks ω).LocallyFiniteIncident :=
  ae_locallyFiniteIncident P k.pairRate_summable

#print axioms ae_locallyFiniteIncident_kernel

end ExceptionalTimes.ClockIncidentFiniteness
