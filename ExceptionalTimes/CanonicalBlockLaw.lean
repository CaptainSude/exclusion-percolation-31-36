import ExceptionalTimes.PoissonMarkProduct
import ExceptionalTimes.CanonicalEdgeIndex
import ExceptionalTimes.ProductSpatialShift

/-! Exact finite color/count cylinders for iid anchor blocks. Each block
contains one fair color and one independent clock for each positively
oriented displacement. The finite law is derived from the product measure. -/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace ExceptionalTimes.CanonicalBlockLaw

open CanonicalEdgeIndex

abbrev Block := Bool × (Displacement → PositiveMarks)
abbrev Sample := Site → Block

noncomputable def fairBit : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac false + (1/2 : ℝ≥0∞) • Measure.dirac true

instance : IsProbabilityMeasure fairBit where
  measure_univ := by simpa [fairBit] using ENNReal.add_halves (1 : ℝ≥0∞)

theorem fairBit_singleton (b : Bool) : fairBit {b} = (1/2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairBit]

noncomputable def blockLaw (ν : Displacement → Measure PositiveMarks) : Measure Block :=
  fairBit.prod (Measure.infinitePi ν)

noncomputable def law (ν : Displacement → Measure PositiveMarks) : Measure Sample :=
  ProductSpatialShift.latticeLaw (blockLaw ν)

instance (ν : Displacement → Measure PositiveMarks) [∀ z, IsProbabilityMeasure (ν z)] :
    IsProbabilityMeasure (blockLaw ν) := by unfold blockLaw; infer_instance

instance (ν : Displacement → Measure PositiveMarks) [∀ z, IsProbabilityMeasure (ν z)] :
    IsProbabilityMeasure (law ν) := by unfold law ProductSpatialShift.latticeLaw; infer_instance

def initial (ω : Sample) (v : Site) : Bool := (ω v).1

theorem measurable_initial : Measurable initial := by
  exact measurable_pi_iff.mpr fun v => measurable_fst.comp (measurable_pi_apply v)

theorem joint_count_law (ν : Displacement → Measure PositiveMarks)
    [∀ z, IsProbabilityMeasure (ν z)] (rate : Displacement → ℝ)
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (rate z))
    (s : Finset Site) (η : Configuration)
    (I : Type) [Fintype I] (edge : I → Index) (a b : I → ℝ) (n : I → ℕ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → edge i = edge j →
      Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) :
    law ν {ω | (∀ v ∈ s, initial ω v = η v) ∧
        ∀ i, ((ω (edge i).1).2 (edge i).2).count (a i) (b i) = n i} =
      (1/2 : ℝ≥0∞)^s.card * ∏ i, poissonMass (rate (edge i).2 * (b i-a i)) (n i) := by
  let S : Finset Site := s ∪ Finset.univ.image (fun i => (edge i).1)
  let A : Site → Set Bool := fun v => {c | v ∈ s → c = η v}
  let B : Site → Set (Displacement → PositiveMarks) := fun v =>
    {m | ∀ i, (edge i).1 = v → (m (edge i).2).count (a i) (b i) = n i}
  let E : Site → Set Block := fun v => A v ×ˢ B v
  have hB : ∀ v, MeasurableSet (B v) := by
    intro v
    simp only [B,Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      ((PositiveMarks.measurable_count (a i) (b i)).comp
        (measurable_pi_apply (edge i).2)) (measurableSet_singleton (n i))
  have hevent : {ω : Sample | (∀ v ∈ s, initial ω v = η v) ∧
        ∀ i, ((ω (edge i).1).2 (edge i).2).count (a i) (b i) = n i} =
      (S : Set Site).pi E := by
    ext ω
    constructor
    · rintro ⟨hc,hm⟩ v _
      refine ⟨fun hv => hc v hv,?_⟩
      intro i hi
      simpa only [← hi] using hm i
    · intro h
      constructor
      · intro v hv
        exact (h v (Finset.mem_union_left _ hv)).1 hv
      · intro i
        exact (h (edge i).1 (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))).2 i rfl
  change Measure.infinitePi (fun _ : Site => blockLaw ν) _ = _
  rw [hevent,Measure.infinitePi_pi _ (fun v _ => (MeasurableSet.of_discrete :
    MeasurableSet (A v)).prod (hB v))]
  have hA (v : Site) : fairBit (A v) = if v ∈ s then (1/2 : ℝ≥0∞) else 1 := by
    by_cases hv : v ∈ s
    · have hset : A v = {η v} := by ext c; simp [A,hv]
      rw [hset,ite_eq_left hv,fairBit_singleton]
    · have hset : A v = Set.univ := by ext c; simp [A,hv]
      rw [hset,ite_eq_right hv,measure_univ]
  have hfiber (v : Site) : Measure.infinitePi ν (B v) =
      ∏ i ∈ Finset.univ with (edge i).1 = v,
        poissonMass (rate (edge i).2 * (b i-a i)) (n i) := by
    let T : Finset I := Finset.univ.filter (fun i => (edge i).1 = v)
    have hT : ∀ i : T, (edge i.val).1 = v := fun i => (Finset.mem_filter.mp i.property).2
    have H := PositiveMarks.product_count_law ν rate hlaw T (fun i => (edge i.val).2)
      (fun i => a i.val) (fun i => b i.val) (fun i => n i.val)
      (fun i => ha i.val) (fun i => hab i.val)
      (fun i j hij hdisp => hdisj i.val j.val (fun h => hij (Subtype.ext h))
        (Prod.ext ((hT i).trans (hT j).symm) hdisp))
    have hset : {m : Displacement → PositiveMarks | ∀ i : T,
        (m (edge i.val).2).count (a i.val) (b i.val) = n i.val} = B v := by
      ext m
      constructor
      · intro h i hi
        exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
      · intro h i
        exact h i.val (hT i)
    rw [hset] at H
    exact H.trans (Finset.prod_coe_sort T
      (fun i => poissonMass (rate (edge i).2 * (b i-a i)) (n i)))
  simp only [blockLaw,Measure.prod_prod,hA,hfiber,Finset.prod_mul_distrib]
  have hcolor : (∏ v ∈ S, if v ∈ s then (1/2 : ℝ≥0∞) else 1) = (1/2 : ℝ≥0∞)^s.card := by
    calc
      _ = ∏ v ∈ s, if v ∈ s then (1/2 : ℝ≥0∞) else 1 :=
        (Finset.prod_subset Finset.subset_union_left (fun v _ hv => by simp [hv])).symm
      _ = _ := by simp
  rw [hcolor]
  congr 1
  exact Finset.prod_fiberwise_of_maps_to
    (fun i _ => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)) _

#print axioms joint_count_law

end ExceptionalTimes.CanonicalBlockLaw
