import ExceptionalTimes.HexCells
import Mathlib.Analysis.Complex.Basic

namespace ExceptionalTimes.HexTiling

open Set HexCells

theorem unit_square_covered {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : ∃ u : Site, (x,y) ∈ cell u := by
  by_cases hxy : y ≤ x
  · by_cases h0 : 2*x+y ≤ 1
    · refine ⟨(0,0), ?_⟩
      norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_zero, mul_zero, zero_add,
        zero_sub, sub_zero]
      repeat' constructor
      all_goals linarith [hx.1, hx.2, hy.1, hy.2]
    · by_cases h1 : 2 ≤ x+2*y
      · refine ⟨(1,1), ?_⟩
        norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_one]
        repeat' constructor
        all_goals linarith [hx.1, hx.2, hy.1, hy.2]
      · refine ⟨(1,0), ?_⟩
        norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_one, Int.cast_zero]
        repeat' constructor
        all_goals linarith [hx.1, hx.2, hy.1, hy.2]
  · by_cases h0 : x+2*y ≤ 1
    · refine ⟨(0,0), ?_⟩
      norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_zero]
      repeat' constructor
      all_goals linarith [hx.1, hx.2, hy.1, hy.2]
    · by_cases h1 : 2 ≤ 2*x+y
      · refine ⟨(1,1), ?_⟩
        norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_one]
        repeat' constructor
        all_goals linarith [hx.1, hx.2, hy.1, hy.2]
      · refine ⟨(0,1), ?_⟩
        norm_num only [cell, mem_ofPred, mem_Icc, Int.cast_one, Int.cast_zero]
        repeat' constructor
        all_goals linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_cell_translate (p : ℝ × ℝ) (u v : Site) :
    p + center u ∈ cell (u + v) ↔ p ∈ cell v := by
  simp only [cell, HexCells.center, mem_ofPred, mem_Icc, Prod.fst_add, Prod.snd_add, Int.cast_add]
  constructor <;> rintro ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩
  all_goals repeat' constructor
  all_goals linarith

theorem plane_covered (p : ℝ × ℝ) : ∃ u : Site, p ∈ cell u := by
  let u : Site := (⌊p.1⌋, ⌊p.2⌋)
  let q := p - center u
  have hx : q.1 ∈ Icc (0 : ℝ) 1 := by
    change 0 ≤ p.1 - ⌊p.1⌋ ∧ p.1 - ⌊p.1⌋ ≤ 1
    exact ⟨sub_nonneg.mpr (Int.floor_le p.1), by linarith [Int.lt_floor_add_one p.1]⟩
  have hy : q.2 ∈ Icc (0 : ℝ) 1 := by
    change 0 ≤ p.2 - ⌊p.2⌋ ∧ p.2 - ⌊p.2⌋ ≤ 1
    exact ⟨sub_nonneg.mpr (Int.floor_le p.2), by linarith [Int.lt_floor_add_one p.2]⟩
  obtain ⟨v, hv⟩ := unit_square_covered hx hy
  refine ⟨u+v, ?_⟩
  have h := (mem_cell_translate q u v).mpr hv
  simpa only [q, sub_add_cancel] using h

noncomputable def planeMap (p : ℝ × ℝ) : ℂ :=
  ⟨p.1 + p.2/2, Real.sqrt 3 * p.2/2⟩

theorem planeMap_center (u : Site) : planeMap (center u) = triangularEmbedding u := rfl

theorem continuous_planeMap : Continuous planeMap := by
  have h : Continuous (fun p : ℝ × ℝ => ((p.1+p.2/2 : ℝ) : ℂ) +
      ((Real.sqrt 3*p.2/2 : ℝ) : ℂ)*Complex.I) := by fun_prop
  convert h using 1
  funext p
  apply Complex.ext <;> simp [planeMap]

theorem planeMap_sub (p q : ℝ × ℝ) : planeMap (p-q) = planeMap p - planeMap q := by
  apply Complex.ext <;> simp [planeMap] <;> ring

theorem planeMap_normSq (p : ℝ × ℝ) :
    Complex.normSq (planeMap p) = p.1^2 + p.1*p.2 + p.2^2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [planeMap, Complex.normSq_apply]
  nlinarith [sq_nonneg p.2]

theorem planeMap_norm_le_coordinates (p : ℝ × ℝ) :
    ‖planeMap p‖ ≤ |p.1| + |p.2| := by
  have hs := planeMap_normSq p
  rw [Complex.normSq_eq_norm_sq] at hs
  have hprod := le_abs_self (p.1*p.2)
  rw [abs_mul] at hprod
  nlinarith [sq_abs p.1, sq_abs p.2, abs_nonneg p.1, abs_nonneg p.2,
    mul_nonneg (abs_nonneg p.1) (abs_nonneg p.2)]

theorem planeMap_injective : Function.Injective planeMap := by
  intro p q h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  dsimp [planeMap] at hi hr
  have h2 : p.2 = q.2 := by nlinarith
  exact Prod.ext (by linarith) h2

theorem planeMap_surjective : Function.Surjective planeMap := by
  intro z
  refine ⟨(z.re-z.im/Real.sqrt 3, 2*z.im/Real.sqrt 3), ?_⟩
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply Complex.ext
  · dsimp [planeMap]
    ring
  · dsimp [planeMap]
    field_simp

noncomputable def physicalCell (ε : ℝ) (u : Site) : Set ℂ :=
  (fun p => (ε : ℂ) * planeMap p) '' cell u

theorem isCompact_physicalCell (ε : ℝ) (u : Site) : IsCompact (physicalCell ε u) := by
  exact (isCompact_cell u).image (continuous_const.mul continuous_planeMap)

theorem isClosed_physicalCell (ε : ℝ) (u : Site) : IsClosed (physicalCell ε u) :=
  (isCompact_physicalCell ε u).isClosed

theorem physicalCenter_mem (ε : ℝ) (u : Site) :
    (ε : ℂ)*triangularEmbedding u ∈ physicalCell ε u :=
  ⟨center u, center_mem_cell u, rfl⟩

theorem physicalCell_radius {ε : ℝ} {u : Site} {z : ℂ}
    (hz : z ∈ physicalCell ε u) :
    dist z ((ε : ℂ)*triangularEmbedding u) ≤ 2*|ε| := by
  obtain ⟨p, hp, rfl⟩ := hz
  obtain ⟨hx, hy⟩ := coordinate_bounds hp
  rw [Complex.dist_eq, ← mul_sub, ← planeMap_center, ← planeMap_sub, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have h := planeMap_norm_le_coordinates (p-center u)
  change ‖planeMap (p-center u)‖ ≤ |p.1-u.1| + |p.2-u.2| at h
  have hnorm : ‖planeMap (p-center u)‖ ≤ 2 := by linarith
  calc
    |ε| * ‖planeMap (p-center u)‖ ≤ |ε| * 2 := mul_le_mul_of_nonneg_left hnorm (abs_nonneg ε)
    _ = 2*|ε| := mul_comm _ _

theorem physicalCell_subset_ball {ε r : ℝ} {u : Site} {z : ℂ}
    (hu : dist ((ε : ℂ)*triangularEmbedding u) z + 2*|ε| < r) :
    physicalCell ε u ⊆ Metric.ball z r := by
  intro p hp
  apply lt_of_le_of_lt (dist_triangle p ((ε : ℂ)*triangularEmbedding u) z)
  have h := physicalCell_radius hp
  linarith

theorem physicalCell_disjoint_ball {ε r : ℝ} {u : Site} {z : ℂ}
    (hu : r + 2*|ε| ≤ dist ((ε : ℂ)*triangularEmbedding u) z) :
    Disjoint (physicalCell ε u) (Metric.ball z r) := by
  apply Set.disjoint_left.mpr
  intro p hp hpr
  have h := physicalCell_radius hp
  have htri := dist_triangle ((ε : ℂ)*triangularEmbedding u) p z
  rw [dist_comm ((ε : ℂ)*triangularEmbedding u) p] at htri
  have hlt : dist p z < r := hpr
  linarith

theorem physical_plane_covered {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    ∃ u : Site, z ∈ physicalCell ε u := by
  obtain ⟨p, hp⟩ := planeMap_surjective (z / (ε : ℂ))
  obtain ⟨u, hu⟩ := plane_covered p
  refine ⟨u, p, hu, ?_⟩
  dsimp only
  rw [hp]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  field_simp

theorem physical_cell_inter_nonempty_iff {ε : ℝ} (hε : ε ≠ 0) (u v : Site) :
    (physicalCell ε u ∩ physicalCell ε v).Nonempty ↔ u = v ∨ TriangularAdj u v := by
  have hi : Function.Injective (fun p => (ε : ℂ) * planeMap p) := by
    intro p q hpq
    apply planeMap_injective
    exact mul_left_cancel₀ (by exact_mod_cast hε) hpq
  rw [← cell_inter_nonempty_iff]
  constructor
  · rintro ⟨z, ⟨p, hp, hpz⟩, ⟨q, hq, hqz⟩⟩
    have heq := hi (hpz.trans hqz.symm)
    exact ⟨p, hp, heq ▸ hq⟩
  · rintro ⟨p, hp, hq⟩
    exact ⟨(ε : ℂ)*planeMap p, ⟨p, hp, rfl⟩, ⟨p, hq, rfl⟩⟩

end ExceptionalTimes.HexTiling

#print axioms ExceptionalTimes.HexTiling.plane_covered
#print axioms ExceptionalTimes.HexTiling.physical_cell_inter_nonempty_iff
