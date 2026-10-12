import ExceptionalTimes.PoissonDimerLaw
import ExceptionalTimes.FiniteClockLaw

/-!
# Literal finite matching clocks and the product dimer law

Distinct slots encode disjoint pairs of actual lattice sites. Local trace
transfer proves that simultaneous rings on different pairs cause no issue.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace ExceptionalTimes.MatchingDimerLaw

open FiniteClockBridge PoissonDimerLaw DimerLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : ℕ}

def edge (slot : Fin k × Fin 2 ↪ Site) (b : Fin k) : Sym2 Site :=
  s(slot (b, 0), slot (b, 1))

def edges (slot : Fin k × Fin 2 ↪ Site) : Finset (Sym2 Site) :=
  Finset.univ.image (edge slot)

def project (slot : Fin k × Fin 2 ↪ Site) (η : Configuration) : Fin k → Color :=
  fun b i => η (slot (b, i))

theorem project_pairProjection (slot : Fin k × Fin 2 ↪ Site) (η : Configuration)
    (b : Fin k) : project slot η b = pairProjection (slot (b, 0)) (slot (b, 1)) η := by
  symm
  exact pair_ext (project slot η b)

theorem edge_mem_block {slot : Fin k × Fin 2 ↪ Site} {b c : Fin k} {i : Fin 2}
    (h : slot (b, i) ∈ edge slot c) : b = c := by
  rcases Sym2.mem_iff.mp h with h | h
  · exact congrArg Prod.fst (slot.injective h)
  · exact congrArg Prod.fst (slot.injective h)

theorem edge_injective (slot : Fin k × Fin 2 ↪ Site) : Function.Injective (edge slot) := by
  intro b c h
  apply edge_mem_block (i := 0)
  rw [← h]
  exact Sym2.mem_mk_left _ _

theorem edge_sites_ne (slot : Fin k × Fin 2 ↪ Site) (b : Fin k) :
    slot (b, 0) ≠ slot (b, 1) := by
  intro h
  have := congrArg Prod.snd (slot.injective h)
  exact (by decide : (0 : Fin 2) ≠ 1) this

theorem trace_transfer {C D : ClockField} (A : Set Site)
    (hclosed : ∀ v ∈ A, ∀ w t, C.Rings v w t → w ∈ A)
    (hagree : ∀ v ∈ A, ∀ w t, C.Rings v w t ↔ D.Rings v w t)
    {c : TimeCutoff} {v origin : Site} (hp : C.BackwardTrace c v origin) (hv : v ∈ A) :
    D.BackwardTrace c v origin := by
  induction hp with
  | @stop c v h =>
    exact .stop (fun w t hr ha => h w t ((hagree v hv w t).mpr hr) ha)
  | @jump c v t w origin h tail ih =>
    exact .jump ⟨(hagree v hv w t).mp h.rings, h.allowed,
      fun z r hr ha => h.latest z r ((hagree v hv z r).mpr hr) ha⟩
      (ih (hclosed v hv w t h.rings))

theorem single_matching_rings (C : ClockField) (slot : Fin k × Fin 2 ↪ Site)
    (b : Fin k) {v : Site} (hv : v = slot (b, 0) ∨ v = slot (b, 1)) (w : Site) (t : ℝ) :
    (C.restrictEdges {edge slot b}).Rings v w t ↔
      (C.restrictEdges (edges slot)).Rings v w t := by
  rw [ClockField.restrictEdges_rings, ClockField.restrictEdges_rings]
  constructor
  · rintro ⟨he, hr⟩
    refine ⟨?_, hr⟩
    rw [Finset.mem_singleton.mp he]
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  · rintro ⟨he, hr⟩
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp he
    have hvc : v ∈ edge slot c := hc ▸ Sym2.mem_mk_left v w
    have hbc : b = c := hv.elim
      (fun h => edge_mem_block (h ▸ hvc)) (fun h => edge_mem_block (h ▸ hvc))
    subst c
    exact ⟨Finset.mem_singleton.mpr hc.symm, hr⟩

theorem single_closed (C : ClockField) (x y : Site) :
    ∀ v ∈ ({x, y} : Set Site), ∀ w t,
      (C.restrictEdges {s(x, y)}).Rings v w t → w ∈ ({x, y} : Set Site) := by
  intro v _ w t hr
  have he := Finset.mem_singleton.mp ((ClockField.restrictEdges_rings C {s(x, y)} v w t).mp hr).1
  have hw : w ∈ s(x, y) := he ▸ Sym2.mem_mk_right v w
  exact Sym2.mem_iff.mp hw

theorem matching_ancestor_single (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (slot : Fin k × Fin 2 ↪ Site) (b : Fin k) (i : Fin 2)
    (c : TimeCutoff) :
    (C.restrictEdges (edges slot)).ancestor
        (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) c (slot (b, i)) =
      (C.restrictEdges {edge slot b}).ancestor
        (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) c (slot (b, i)) := by
  apply ClockField.ancestor_eq_of_trace (ht.restrictEdges _) _
  apply trace_transfer ({slot (b, 0), slot (b, 1)} : Set Site)
    (single_closed C _ _) (fun v hv w t => single_matching_rings C slot b hv w t)
    ((C.restrictEdges {edge slot b}).ancestor_trace
      (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) c (slot (b, i)))
  fin_cases i <;> simp

/-- Every block of the actual retained matching trajectory follows its own
edge-count parity, without any hypothesis excluding disjoint clock ties. -/
theorem trajectory_matching (C : ClockField) (hc : C.FiniteEdgeCounts)
    (ht : C.NoIncidentTies) (slot : Fin k × Fin 2 ↪ Site) (η : Configuration) (t : ℝ) :
    project slot ((C.restrictEdges (edges slot)).trajectory
      (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) η t) =
      afterCounts (fun b => C.markCount (edge slot b) 0 t) (project slot η) := by
  funext b
  have he : project slot ((C.restrictEdges (edges slot)).trajectory
      (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) η t) b =
      project slot ((C.restrictEdges {edge slot b}).trajectory
        (ClockField.restrictEdges_hasFiniteBackwardTraces hc _) η t) b := by
    funext i
    unfold project ClockField.trajectory ClockField.colorAt
    rw [matching_ancestor_single C hc ht slot b i]
  rw [he, project_pairProjection]
  simp only [edge]
  rw [trajectory_single_pair C hc ht]
  rw [afterCounts, project_pairProjection]

def tests (slot : Fin k × Fin 2 ↪ Site) (t : ℝ) (ht : 0 < t) : ClockTests k where
  edge := edge slot
  start _ := 0
  finish _ := t
  start_nonneg _ := le_refl 0
  nonempty _ := ht
  disjoint _i _j hij he := (hij (edge_injective slot he)).elim

/-- The product initial-pair/count law is inherited from the original
infinite iid field on the actual distinct sites; no independence premise
is added at the matching level. -/
theorem initial_many_count_law {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ} {initial : Ξ → Configuration}
    {clocks : Ξ → ClockField} (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (slot : Fin k × Fin 2 ↪ Site) (t : ℝ) (ht : 0 < t)
    (ω : Fin k → Color) (n : Fin k → ℕ) :
    μ {a | project slot (initial a) = ω ∧
      (fun b => (clocks a).markCount (edge slot b) 0 t) = n} =
      (1 / 4 : ℝ≥0∞) ^ k * ∏ b, poissonMass (rate (edge slot b) * t) (n b) := by
  let V : Finset Site := Finset.univ.image slot
  let η : Configuration := Function.extend slot (fun p => ω p.1 p.2) (fun _ => false)
  have hη (b : Fin k) (i : Fin 2) : η (slot (b, i)) = ω b i :=
    slot.injective.extend_apply _ _ (b, i)
  have hcolor (a : Ξ) : project slot (initial a) = ω ↔
      ∀ v ∈ V, initial a v = η v := by
    constructor
    · intro h v hv
      obtain ⟨⟨b, i⟩, _, rfl⟩ := Finset.mem_image.mp hv
      rw [hη]
      exact congrFun (congrFun h b) i
    · intro h
      funext b i
      exact (h _ (Finset.mem_image.mpr ⟨(b, i), Finset.mem_univ _, rfl⟩)).trans (hη b i)
  have he : {a | project slot (initial a) = ω ∧
      (fun b => (clocks a).markCount (edge slot b) 0 t) = n} =
      {a | (∀ v ∈ V, initial a v = η v) ∧ ∀ b,
        (clocks a).markCount ((tests slot t ht).edge b)
          ((tests slot t ht).start b) ((tests slot t ht).finish b) = n b} := by
    ext a
    simp only [Set.mem_ofPred_eq, hcolor, funext_iff, tests]
  rw [he, hlaw V η k (tests slot t ht) n]
  have hcard : V.card = k * 2 := by
    dsimp only [V]
    rw [Finset.card_image_of_injective _ slot.injective]
    simp
  rw [hcard, Nat.mul_comm k 2, pow_mul]
  have hquarter : (1 / 2 : ℝ≥0∞) ^ 2 = 1 / 4 := by
    norm_num
    rw [← ENNReal.inv_pow]
    norm_num
  rw [hquarter]
  simp only [tests, sub_zero]

theorem measurable_project {Ξ : Type*} [MeasurableSpace Ξ]
    {initial : Ξ → Configuration} (hi : Measurable initial)
    (slot : Fin k × Fin 2 ↪ Site) : Measurable (fun a => project slot (initial a)) := by
  apply Measurable.of_eval
  intro b
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply (slot (b, i))).comp hi

/-- Exact `ManyDimerLaw` probabilities of the actual same-clock matching
restriction. The physical swap rates are one half, hence the canonical
rate-one refresh parameter `1-exp(-t)`. -/
theorem graphical_matching_twoTimeWeight {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (slot : Fin k × Fin 2 ↪ Site)
    (hrate : ∀ b, rate (edge slot b) = 1 / 2) (t : ℝ) (ht : 0 < t)
    (ω η : Fin k → Color) :
    μ {a | project slot (P.initial a) = ω ∧
      project slot (((P.clocks a).restrictEdges (edges slot)).trajectory
        (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts a) _)
        (P.initial a) t) = η} =
      ENNReal.ofReal (ManyDimerLaw.manyWeight (fun _ => refreshProbability t) ω η) := by
  have hlaw : ∀ ξ n, μ {a | project slot (P.initial a) = ξ ∧
      (fun b => (P.clocks a).markCount (edge slot b) 0 t) = n} =
      (1 / 4 : ℝ≥0∞) ^ k * ∏ b, poissonMass (t / 2) (n b) := by
    intro ξ n
    rw [initial_many_count_law P.independent_law slot t ht]
    congr 1
    apply Finset.prod_congr rfl
    intro b _
    rw [hrate b]
    congr 1
    ring
  have hN : Measurable (fun a b => (P.clocks a).markCount (edge slot b) 0 t) := by
    apply Measurable.of_eval
    intro b
    exact P.measurable_counts _ _ _
  have h := random_many_twoTimeWeight k (measurable_project P.measurable_initial slot)
    hN t ht.le hlaw ω η
  convert h using 1
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [trajectory_matching (P.clocks a) (P.finiteEdgeCounts a)
    (P.no_incident_ties a) slot (P.initial a) t]

#print axioms trajectory_matching
#print axioms initial_many_count_law
#print axioms graphical_matching_twoTimeWeight

theorem measurable_matching_project {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (slot : Fin k × Fin 2 ↪ Site) (t : ℝ) :
    Measurable (fun a => project slot (((P.clocks a).restrictEdges (edges slot)).trajectory
      (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts a) _)
      (P.initial a) t)) := by
  have he : (fun a => project slot (((P.clocks a).restrictEdges (edges slot)).trajectory
      (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts a) _)
      (P.initial a) t)) =
      (fun a => afterCounts (fun b => (P.clocks a).markCount (edge slot b) 0 t)
        (project slot (P.initial a))) := by
    funext a
    exact trajectory_matching (P.clocks a) (P.finiteEdgeCounts a) (P.no_incident_ties a)
      slot (P.initial a) t
  rw [he]
  have hN : Measurable (fun a b => (P.clocks a).markCount (edge slot b) 0 t) := by
    apply Measurable.of_eval
    intro b
    exact P.measurable_counts _ _ _
  exact (Measurable.of_discrete (f := fun z : (Fin k → ℕ) × (Fin k → Color) =>
    afterCounts z.1 z.2)).comp (hN.prodMk (measurable_project P.measurable_initial slot))

/-- Event probabilities under retained half-rate matching clocks are the
literal finite product-dimer event probabilities used by Harris and the
conditional variance estimates. -/
theorem graphical_matching_pairedProbability {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) (slot : Fin k × Fin 2 ↪ Site)
    (hrate : ∀ b, rate (edge slot b) = 1 / 2) (t : ℝ) (ht : 0 < t)
    (E : (Fin k → Color) → Prop) :
    μ {a | E (project slot (P.initial a)) ∧
      E (project slot (((P.clocks a).restrictEdges (edges slot)).trajectory
        (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts a) _)
        (P.initial a) t))} =
      ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => refreshProbability t) E) := by
  classical
  rw [FiniteClockLaw.paired_event_eq_sum
    (measurable_project P.measurable_initial slot).aemeasurable
    (measurable_matching_project P slot t).aemeasurable]
  have hw (ω η : Fin k → Color) :
      0 ≤ ManyDimerLaw.manyWeight (fun _ => refreshProbability t) ω η := by
    exact Finset.prod_nonneg (fun b _ =>
      twoTimeWeight_nonneg (refreshProbability_nonneg ht.le) (refreshProbability_le_one t) _ _)
  have hterm (ω η : Fin k → Color) : 0 ≤
      ManyDimerLaw.manyWeight (fun _ => refreshProbability t) ω η *
        (EnvironmentVariance.indicator (E ω) * EnvironmentVariance.indicator (E η)) := by
    apply mul_nonneg (hw ω η)
    unfold EnvironmentVariance.indicator
    split_ifs <;> norm_num
  rw [ManyDimerLaw.manyProbability, ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => Finset.sum_nonneg (fun η _ => hterm ω η))]
  congr 1
  · ext ω
    simp
  · funext ω
    rw [ENNReal.ofReal_sum_of_nonneg (fun η _ => hterm ω η)]
    congr 1
    · ext η
      simp
    · funext η
      by_cases hω : E ω <;> by_cases hη : E η
      · simp only [hω, hη, and_self, ite_true, EnvironmentVariance.indicator, mul_one]
        exact graphical_matching_twoTimeWeight P slot hrate t ht ω η
      · simp [hω, hη, EnvironmentVariance.indicator]
      · simp [hω, hη, EnvironmentVariance.indicator]
      · simp [hω, hη, EnvironmentVariance.indicator]

#print axioms graphical_matching_pairedProbability

end ExceptionalTimes.MatchingDimerLaw
