import ExceptionalTimes.ClockStationarity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Joint measurability of clock counts with variable interval endpoints.
Only fixed-interval measurability and the literal finite clock sets are
used; no stochastic path regularity is assumed. -/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ExceptionalTimes.ClockCountMeasurability

theorem cumulative_mono (C : ClockField) (hc : C.FiniteEdgeCounts) (e : Sym2 Site) :
    Monotone (C.markCount e 0) := by
  intro a b hab
  exact Set.ncard_le_ncard (fun _ hx => ⟨hx.1,hx.2.1,hx.2.2.trans hab⟩) (hc e b)

/-- Finitely many marks on a bounded interval leave a rational time just
after t with exactly the same cumulative count. -/
theorem exists_rat_same_count (C : ClockField) (hc : C.FiniteEdgeCounts)
    (e : Sym2 Site) (t : ℝ) :
    ∃ q : ℚ, t < (q : ℝ) ∧ C.markCount e 0 (q : ℝ) = C.markCount e 0 t := by
  let S := (hc e (t+1)).toFinset
  let U := insert (t+1) (S.filter (fun r => t < r))
  have hUne : U.Nonempty := ⟨t+1,Finset.mem_insert_self _ _⟩
  have hgt : ∀ r ∈ U, t < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · linarith
    · exact (Finset.mem_filter.mp hr).2
  have htmin : t < U.min' hUne := hgt _ (U.min'_mem hUne)
  obtain ⟨q,htq,hq⟩ := exists_rat_btwn htmin
  have hq1 : (q : ℝ) < t+1 :=
    hq.trans_le (U.min'_le _ (Finset.mem_insert_self _ _))
  refine ⟨q,htq,?_⟩
  apply congrArg Set.ncard
  ext r
  constructor
  · rintro ⟨hr,hr0,hrq⟩
    refine ⟨hr,hr0,?_⟩
    by_contra! htr
    have hrS : r ∈ S := (hc e (t+1)).mem_toFinset.mpr ⟨hr,hr0,hrq.trans hq1.le⟩
    have hrU : r ∈ U := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hrS,htr⟩)
    exact (not_lt_of_ge hrq) (hq.trans_le (U.min'_le _ hrU))
  · rintro ⟨hr,hr0,hrt⟩
    exact ⟨hr,hr0,hrt.trans htq.le⟩

theorem cumulative_le_iff_rat (C : ClockField) (hc : C.FiniteEdgeCounts)
    (e : Sym2 Site) (t : ℝ) (n : ℕ) :
    C.markCount e 0 t ≤ n ↔ ∃ q : ℚ, t < (q : ℝ) ∧ C.markCount e 0 (q : ℝ) ≤ n := by
  constructor
  · intro hn
    obtain ⟨q,hq,heq⟩ := exists_rat_same_count C hc e t
    exact ⟨q,hq,heq ▸ hn⟩
  · rintro ⟨q,hq,hn⟩
    exact (cumulative_mono C hc e hq.le).trans hn

theorem interval_count_eq_sub (C : ClockField) (hc : C.FiniteEdgeCounts)
    (e : Sym2 Site) (a b : ℝ) :
    C.markCount e a b = C.markCount e 0 b - C.markCount e 0 a := by
  by_cases hab : a ≤ b
  · have hsub : C.marks e ∩ Set.Ioc 0 a ⊆ C.marks e ∩ Set.Ioc 0 b :=
      fun _ hx => ⟨hx.1,hx.2.1,hx.2.2.trans hab⟩
    have hset : C.marks e ∩ Set.Ioc a b =
        (C.marks e ∩ Set.Ioc 0 b) \ (C.marks e ∩ Set.Ioc 0 a) := by
      ext r
      constructor
      · rintro ⟨hr,hra,hrb⟩
        exact ⟨⟨hr,C.positive_time e r hr,hrb⟩,fun h => (not_le_of_gt hra) h.2.2⟩
      · rintro ⟨⟨hr,hr0,hrb⟩,hna⟩
        exact ⟨hr,lt_of_not_ge (fun hra => hna ⟨hr,hr0,hra⟩),hrb⟩
    simp only [ClockField.markCount,hset,Set.ncard_sdiff hsub (hc e a)]
  · have hba : b ≤ a := (lt_of_not_ge hab).le
    rw [Nat.sub_eq_zero_of_le (cumulative_mono C hc e hba)]
    simp only [ClockField.markCount,Set.Ioc_eq_empty_of_le hba,Set.inter_empty,Set.ncard_empty]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

theorem measurable_cumulative (P : PoissonGraphicalRealization μ rate) (e : Sym2 Site) :
    Measurable (fun p : Ω × ℝ => (P.clocks p.1).markCount e 0 p.2) := by
  apply measurable_of_Iic
  intro n
  have hset : (fun p : Ω × ℝ => (P.clocks p.1).markCount e 0 p.2) ⁻¹' Set.Iic n =
      ⋃ q : ℚ, {p : Ω × ℝ | p.2 < (q : ℝ)} ∩
        {p : Ω × ℝ | (P.clocks p.1).markCount e 0 (q : ℝ) ≤ n} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
    exact cumulative_le_iff_rat (P.clocks p.1) (P.finiteEdgeCounts p.1) e p.2 n
  rw [hset]
  apply MeasurableSet.iUnion
  intro q
  exact (measurableSet_lt measurable_snd measurable_const).inter
    (((P.measurable_counts e 0 (q : ℝ)).comp measurable_fst) measurableSet_Iic)

set_option maxHeartbeats 1000000 in
/-- Counts are jointly measurable in the sample and both endpoints. -/
theorem measurable_interval_count (P : PoissonGraphicalRealization μ rate) (e : Sym2 Site) :
    Measurable (fun p : Ω × (ℝ × ℝ) => (P.clocks p.1).markCount e p.2.1 p.2.2) := by
  have hma : Measurable (fun p : Ω × (ℝ × ℝ) => (p.1,p.2.1)) := by fun_prop
  have hmb : Measurable (fun p : Ω × (ℝ × ℝ) => (p.1,p.2.2)) := by fun_prop
  have ha : Measurable (fun p : Ω × (ℝ × ℝ) => (P.clocks p.1).markCount e 0 p.2.1) :=
    (measurable_cumulative P e).comp hma
  have hb : Measurable (fun p : Ω × (ℝ × ℝ) => (P.clocks p.1).markCount e 0 p.2.2) :=
    (measurable_cumulative P e).comp hmb
  have heq : (fun p : Ω × (ℝ × ℝ) => (P.clocks p.1).markCount e p.2.1 p.2.2) =
      (fun p => (P.clocks p.1).markCount e 0 p.2.2 - (P.clocks p.1).markCount e 0 p.2.1) :=
    funext (fun p => interval_count_eq_sub _ (P.finiteEdgeCounts p.1) e p.2.1 p.2.2)
  rw [heq]
  exact (Measurable.of_discrete (f := fun p : ℕ × ℕ => p.1-p.2)).comp (hb.prodMk ha)

#print axioms exists_rat_same_count
#print axioms measurable_interval_count

end ExceptionalTimes.ClockCountMeasurability
