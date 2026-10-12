import ExceptionalTimes.PolyhexBoundary
import ExceptionalTimes.HexTiling

namespace ExceptionalTimes.PairSquareSewing

open Set HexCells HexTiling

theorem planeMap_coordinate_le_norm (p : ℝ × ℝ) :
    |p.1| ≤ 2*‖planeMap p‖ ∧ |p.2| ≤ 2*‖planeMap p‖ := by
  have h := planeMap_normSq p
  rw [Complex.normSq_eq_norm_sq] at h
  constructor
  · nlinarith [sq_nonneg (p.1+2*p.2), sq_abs p.1, norm_nonneg (planeMap p), abs_nonneg p.1]
  · nlinarith [sq_nonneg (2*p.1+p.2), sq_abs p.2, norm_nonneg (planeMap p), abs_nonneg p.2]

theorem open_box_subset_polyhex (n : ℕ) :
    Ioo (-(n : ℝ)) n ×ˢ Ioo (-(n : ℝ)) n ⊆ polyhex n := by
  intro p hp
  obtain ⟨u, hu⟩ := plane_covered p
  obtain ⟨hx,hy⟩ := coordinate_bounds hu
  rw [abs_le] at hx hy
  have hb1 : -(n : ℤ) ≤ u.1 := by
    by_contra h
    have h' : (u.1 : ℝ) ≤ -(n : ℝ)-1 := by exact_mod_cast (show u.1 ≤ -(n : ℤ)-1 by omega)
    linarith [hp.1.1]
  have hb2 : u.1 ≤ (n : ℤ) := by
    by_contra h
    have h' : (n : ℝ)+1 ≤ (u.1 : ℝ) := by exact_mod_cast (show (n : ℤ)+1 ≤ u.1 by omega)
    linarith [hp.1.2]
  have hb3 : -(n : ℤ) ≤ u.2 := by
    by_contra h
    have h' : (u.2 : ℝ) ≤ -(n : ℝ)-1 := by exact_mod_cast (show u.2 ≤ -(n : ℤ)-1 by omega)
    linarith [hp.2.1]
  have hb4 : u.2 ≤ (n : ℤ) := by
    by_contra h
    have h' : (n : ℝ)+1 ≤ (u.2 : ℝ) := by exact_mod_cast (show (n : ℤ)+1 ≤ u.2 by omega)
    linarith [hp.2.2]
  have hubox : u ∈ latticeBox n := by
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨hb1,hb2⟩,⟨hb3,hb4⟩⟩
  exact mem_iUnion₂_of_mem hubox hu

theorem open_box_subset_interior_polyhex (n : ℕ) :
    Ioo (-(n : ℝ)) n ×ˢ Ioo (-(n : ℝ)) n ⊆ interior (polyhex n) := by
  rw [← (isOpen_Ioo.prod isOpen_Ioo).interior_eq]
  exact interior_mono (open_box_subset_polyhex n)

noncomputable def physicalPolyhexInterior (ε : ℝ) (n : ℕ) : Set ℂ :=
  (fun p => (ε : ℂ)*planeMap p) '' interior (polyhex n)

/-- An explicit generous bulk margin, in physical units. No equivalence
between coordinate boxes and Euclidean balls is silently assumed. -/
theorem closedBall_subset_physicalPolyhexInterior
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (z : ℂ) (R : ℝ)
    (hmargin : 2*(‖z‖+R) < ε*n) :
    Metric.closedBall z R ⊆ physicalPolyhexInterior ε n := by
  intro w hw
  obtain ⟨p,hp⟩ := planeMap_surjective (w/(ε : ℂ))
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hwp : (ε : ℂ)*planeMap p = w := by rw [hp]; field_simp
  have hnorm : ε*‖planeMap p‖ = ‖w‖ := by
    rw [← hwp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hwbound : ‖w‖ ≤ ‖z‖+R := by
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    have hdist : ‖w-z‖ ≤ R := by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨hx,hy⟩ := planeMap_coordinate_le_norm p
  have hnx : |p.1| < (n : ℝ) := by nlinarith
  have hny : |p.2| < (n : ℝ) := by nlinarith
  refine ⟨p, open_box_subset_interior_polyhex n ?_, hwp⟩
  exact ⟨abs_lt.mp hnx, abs_lt.mp hny⟩

theorem probe_closedBall_subset_physicalPolyhexInterior
    (P : Probe) (n : ℕ)
    (hmargin : 2*(‖position P.mesh P.center‖+2*P.outerRadius) < P.mesh*n) :
    Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalPolyhexInterior P.mesh n :=
  closedBall_subset_physicalPolyhexInterior P.mesh_pos n _ _ hmargin

#print axioms probe_closedBall_subset_physicalPolyhexInterior

end ExceptionalTimes.PairSquareSewing
