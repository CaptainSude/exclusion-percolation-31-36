import ExceptionalTimes.StochasticModel

namespace ExceptionalTimes.FairOneArm

open MeasureTheory
open scoped ENNReal

theorem origin_mem_latticeBox (R : ℕ) : (0, 0) ∈ latticeBox R := by
  apply mem_latticeBox_of_radius_le
  simp [latticeRadius]

theorem allBlack_oneArm (R : ℕ) : OneArm (fun _ => true) (0, 0) R := by
  have hreach : ∀ n : ℕ, (blackGraph (fun _ => true)).Reachable (0, 0) ((n : ℤ), 0) := by
    intro n
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      refine ⟨?_, rfl, rfl⟩
      exact Or.inl ⟨by simp, rfl⟩
  refine ⟨((R + 1 : ℕ), 0), ⟨rfl, hreach (R + 1)⟩, ?_⟩
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  omega

theorem oneArm_of_box_black {η : Configuration} (R : ℕ)
    (hη : ∀ v ∈ latticeBox (R + 1), η v = true) : OneArm η (0, 0) R :=
  (oneArm_congr_of_eqOn_box (origin_mem_latticeBox R) hη).mpr (allBlack_oneArm R)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {rate : Sym2 Site → ℝ}

noncomputable def probability (P : PoissonGraphicalRealization μ rate) (R : ℕ) : ℝ≥0∞ :=
  μ {ω | OneArm (P.initial ω) (0, 0) R}

theorem probability_pos (P : PoissonGraphicalRealization μ rate) (R : ℕ) :
    0 < probability P R := by
  have hfair := P.independent_law.fair_initial (latticeBox (R + 1)) (fun _ => true)
  have hsub : {ω | ∀ v ∈ latticeBox (R + 1), P.initial ω v = true} ⊆
      {ω | OneArm (P.initial ω) (0, 0) R} := fun _ h => oneArm_of_box_black R h
  have hpos : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) ^ (latticeBox (R + 1)).card :=
    pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  exact hpos.trans_le (hfair ▸ measure_mono hsub)

theorem probability_ne_top (P : PoissonGraphicalRealization μ rate) (R : ℕ) :
    probability P R ≠ ⊤ := by
  let : IsProbabilityMeasure μ := P.independent_law.isProbabilityMeasure
  exact measure_ne_top μ _

end ExceptionalTimes.FairOneArm

#print axioms ExceptionalTimes.FairOneArm.probability_pos
