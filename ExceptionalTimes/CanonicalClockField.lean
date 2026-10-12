import ExceptionalTimes.CanonicalBlockLaw
import ExceptionalTimes.PoissonClockInputs

/-! Decode iid anchor blocks into the literal unordered-edge clock field.
Diagonals are empty on every sample. The decoding is exactly equivariant
under translation, before any null-set repair is performed. -/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ExceptionalTimes.CanonicalClockField

open CanonicalEdgeIndex CanonicalBlockLaw

theorem clockField_ext {C D : ClockField} (h : C.marks = D.marks) : C = D := by
  cases C
  cases D
  cases h
  rfl

noncomputable def clocks (ω : Sample) : ClockField where
  marks e := if h : e.IsDiag then ∅ else
    let a := edgeEquiv.symm ⟨e,h⟩
    ((ω a.1).2 a.2).marks
  positive_time e t ht := by
    by_cases h : e.IsDiag
    · simp only [dite_eq_left h,mem_empty_iff_false] at ht
    · simp only [dite_eq_right h] at ht
      exact PositiveMarks.positive _ t ht
  diagonal_empty v := by simp only [Sym2.mk_isDiag_iff,dite_true]

theorem marks_pair (ω : Sample) (a : Index) :
    (clocks ω).marks (pair a) = ((ω a.1).2 a.2).marks := by
  have he : (⟨pair a,pair_not_diag a⟩ : Edge) = edgeEquiv a := rfl
  simp only [clocks,dite_eq_right (pair_not_diag a),he,Equiv.symm_apply_apply]

theorem markCount_pair (ω : Sample) (a : Index) (s t : ℝ) :
    (clocks ω).markCount (pair a) s t = ((ω a.1).2 a.2).count s t := by
  simp only [ClockField.markCount,PositiveMarks.count,marks_pair]

theorem markCount_diag (ω : Sample) {e : Sym2 Site} (h : e.IsDiag) (s t : ℝ) :
    (clocks ω).markCount e s t = 0 := by
  simp [ClockField.markCount,clocks,h]

theorem rate_diag (k : RateKernel) {e : Sym2 Site} (h : e.IsDiag) :
    k.unorderedPairRate e = 0 := by
  rw [← Sym2.diag_diagElem h]
  exact k.pairRate_diagonal _

theorem finite_counts (ω : Sample) (e : Sym2 Site) (s t : ℝ) :
    ((clocks ω).marks e ∩ Ioc s t).Finite := by
  by_cases h : e.IsDiag
  · simp only [clocks,dite_eq_left h,empty_inter]
    exact finite_empty
  · simp only [clocks,dite_eq_right h]
    exact PositiveMarks.finite _ s t

theorem measurable_counts (e : Sym2 Site) (s t : ℝ) :
    Measurable (fun ω => (clocks ω).markCount e s t) := by
  by_cases h : e.IsDiag
  · have heq : (fun ω => (clocks ω).markCount e s t) = fun _ => 0 := by
      funext ω
      simp [ClockField.markCount,clocks,h]
    rw [heq]
    exact measurable_const
  · obtain ⟨a,rfl⟩ := pair_surjective e h
    simp only [markCount_pair]
    exact (PositiveMarks.measurable_count s t).comp
      ((measurable_pi_apply a.2).comp (measurable_snd.comp (measurable_pi_apply a.1)))

theorem initial_translation (z : Site) (ω : Sample) :
    initial (ProductSpatialShift.translation z ω) = translateConfiguration z (initial ω) := by
  funext v
  simp only [initial,ProductSpatialShift.translation_apply,translateConfiguration]

theorem clocks_translation (z : Site) (ω : Sample) :
    clocks (ProductSpatialShift.translation z ω) = (clocks ω).spatialTranslate z := by
  apply clockField_ext
  funext e
  by_cases h : e.IsDiag
  · rw [← Sym2.diag_diagElem h]
    simp only [Sym2.diag,ClockField.diagonal_empty]
  · obtain ⟨a,rfl⟩ := pair_surjective e h
    change (clocks (ProductSpatialShift.translation z ω)).marks (pair a) =
      (clocks ω).marks ((pair a).map (fun x => x-z))
    simp only [sub_eq_add_neg,← pair_translate,marks_pair]
    rw [ProductSpatialShift.translation_apply]
    rfl

theorem independent_law (k : RateKernel) (ν : Displacement → Measure PositiveMarks)
    [∀ z, IsProbabilityMeasure (ν z)]
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.rate z.val)) :
    IndependentPoissonInitial (law ν) k.unorderedPairRate initial clocks := by
  intro s η n T count
  by_cases hbad : ∃ i, (T.edge i).IsDiag ∧ count i ≠ 0
  · obtain ⟨i,hi,hcount⟩ := hbad
    have hempty : {ω : Sample | (∀ v ∈ s, initial ω v = η v) ∧
        ∀ j, (clocks ω).markCount (T.edge j) (T.start j) (T.finish j) = count j} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hcount ((markCount_diag ω hi _ _).symm.trans (hω.2 i)).symm
    rw [hempty,measure_empty]
    have hzero : (∏ j, poissonMass (k.unorderedPairRate (T.edge j) *
        (T.finish j-T.start j)) (count j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [rate_diag k hi,poissonMass,hcount]
    rw [hzero,mul_zero]
  · have hdiag : ∀ i, (T.edge i).IsDiag → count i = 0 := by
      intro i hi
      by_contra hc
      exact hbad ⟨i,hi,hc⟩
    let I := {i : Fin n // ¬ (T.edge i).IsDiag}
    let edge : I → Index := fun i => edgeEquiv.symm ⟨T.edge i.val,i.property⟩
    have hedge : ∀ i : I, pair (edge i) = T.edge i.val := by
      intro i
      exact congrArg Subtype.val (edgeEquiv.apply_symm_apply ⟨T.edge i.val,i.property⟩)
    have H := CanonicalBlockLaw.joint_count_law ν (fun z => k.rate z.val) hlaw s η I edge
      (fun i => T.start i.val) (fun i => T.finish i.val) (fun i => count i.val)
      (fun i => T.start_nonneg i.val) (fun i => T.nonempty i.val)
      (fun i j hij he => T.disjoint i.val j.val (fun h => hij (Subtype.ext h))
        ((hedge i).symm.trans ((congrArg pair he).trans (hedge j))))
    have hevent : {ω : Sample | (∀ v ∈ s, initial ω v = η v) ∧
        ∀ i, (clocks ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} =
        {ω : Sample | (∀ v ∈ s, initial ω v = η v) ∧
        ∀ i : I, ((ω (edge i).1).2 (edge i).2).count
          (T.start i.val) (T.finish i.val) = count i.val} := by
      ext ω
      refine and_congr_right fun _ => ⟨?_,?_⟩
      · intro h i
        rw [← markCount_pair,hedge]
        exact h i.val
      · intro h i
        by_cases hi : (T.edge i).IsDiag
        · rw [markCount_diag ω hi,hdiag i hi]
        · have H := h ⟨i,hi⟩
          rw [← markCount_pair,hedge] at H
          exact H
    rw [hevent,H]
    congr 1
    have hrate (i : I) : k.rate (edge i).2.val = k.unorderedPairRate (T.edge i.val) := by
      rw [← hedge i,rate_pair]
    simp_rw [hrate]
    have hremoved : (∏ i : {i : Fin n // ¬ ¬ (T.edge i).IsDiag},
        poissonMass (k.unorderedPairRate (T.edge i.val) *
          (T.finish i.val-T.start i.val)) (count i.val)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      have hi : (T.edge i.val).IsDiag := not_not.mp i.property
      simp [rate_diag k hi,hdiag i.val hi,poissonMass]
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => ¬ (T.edge i).IsDiag)
      (fun i => poissonMass (k.unorderedPairRate (T.edge i) *
        (T.finish i-T.start i)) (count i)),hremoved,mul_one]

noncomputable def inputs (k : RateKernel) (ν : Displacement → Measure PositiveMarks)
    [∀ z, IsProbabilityMeasure (ν z)]
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.rate z.val)) :
    PoissonClockInputs (law ν) k.unorderedPairRate where
  initial := initial
  clocks := clocks
  measurable_initial := measurable_initial
  measurable_counts := measurable_counts
  finite_counts := finite_counts
  independent_law := independent_law k ν hlaw

/-- Assembly of the actual product law, the separately supplied a.e.
graphical regularity, and a theorem about the ordinary iid column shift.
Neither of the two latter facts is asserted by this construction lemma. -/
theorem exists_ergodic_realization (k : RateKernel) (ν : Displacement → Measure PositiveMarks)
    [∀ z, IsProbabilityMeasure (ν z)]
    (hlaw : ∀ z, PositiveMarks.HasPoissonCounts (ν z) (k.rate z.val))
    (hgood : ∀ᵐ ω ∂law ν, (clocks ω).NoIncidentTies ∧ (clocks ω).HasFiniteBackwardTraces)
    (hshift : Ergodic (ProductSpatialShift.shift (B := ℤ → Block))
      (ProductSpatialShift.columnsLaw (blockLaw ν))) :
    ∃ P : PoissonGraphicalRealization (law ν) k.unorderedPairRate,
      P.initial = initial ∧ P.clocks =ᵐ[law ν] clocks ∧
      Ergodic (ProductSpatialShift.translation (B := Block) (1,0)) (law ν) ∧
      Function.Semiconj P.trajectories (ProductSpatialShift.translation (1,0))
        (translateTrajectory (1,0)) := by
  obtain ⟨P,hinit,hclocks,hequiv⟩ := (inputs k ν hlaw).exists_equivariant_realization
    (ProductSpatialShift.translation (1,0))
    (ProductSpatialShift.measurePreserving_translation (blockLaw ν) (1,0)) (1,0)
    (initial_translation (1,0)) (clocks_translation (1,0)) hgood
  exact ⟨P,hinit,hclocks,ProductSpatialShift.ergodic_translation_of_columnShift
    (blockLaw ν) hshift,hequiv⟩

#print axioms clocks_translation
#print axioms inputs
#print axioms exists_ergodic_realization

end ExceptionalTimes.CanonicalClockField
