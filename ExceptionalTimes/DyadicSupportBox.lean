import ExceptionalTimes.DyadicGoodSewing
import ExceptionalTimes.FixedMeshSelectedForest
import ExceptionalTimes.UnitReferenceCover

/-! A fixed physical box contains every refined support of a fixed
finite polygon family. The actual positive-orientation matching anchors
stay in a fixed physical ball for both phases. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open IndependentAnnulusInput LatticeRadial

theorem scaled_polygon_support_box {F : Type*} [Fintype F] (Q : F→PolygonQuad) :
    ∃R : ℕ,1≤R ∧ ∀n : ℕ,
      polygonFamilySupport (fun i => (Q i).scale ((2:ℝ)^n) (pow_ne_zero _ (by norm_num)))⊆
        latticeBox (R*2^n) := by
  have hc : IsCompact (⋃i,(Q i).carrier) := isCompact_iUnion (fun i => (Q i).compact)
  obtain ⟨r,hr⟩ := hc.isBounded.subset_closedBall (0 : ℝ×ℝ)
  obtain ⟨R,hR⟩ := exists_nat_gt (max r 0+2)
  have hR1 : 1≤R := by
    have hreal : (1:ℝ)≤R := by linarith [le_max_right r 0]
    exact_mod_cast hreal
  refine ⟨R,hR1,?_⟩
  intro n v hv
  obtain ⟨i,p,hpc,hpQ⟩ := (mem_polygonFamilySupport _ v).mp hv
  obtain ⟨p0,hp0,rfl⟩ := hpQ
  have hp0n : ‖p0‖≤r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hr (Set.mem_iUnion.mpr ⟨i,hp0⟩)
  have hp0x : |p0.1|≤r := (norm_fst_le p0).trans hp0n
  have hp0y : |p0.2|≤r := (norm_snd_le p0).trans hp0n
  have ht : 0<(2:ℝ)^n := by positivity
  have ht1 : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hroom : (2:ℝ)^n*r+2/3≤(R:ℝ)*(2:ℝ)^n := by
    have hh := mul_lt_mul_of_pos_right hR ht
    have hm := mul_le_mul_of_nonneg_right (le_max_left r 0) ht.le
    nlinarith
  obtain ⟨hcx,hcy⟩ := HexCells.coordinate_bounds hpc
  change |(2:ℝ)^n*p0.1-(v.1:ℝ)|≤2/3 at hcx
  change |(2:ℝ)^n*p0.2-(v.2:ℝ)|≤2/3 at hcy
  have hxscaled : |(2:ℝ)^n*p0.1|≤(2:ℝ)^n*r := by
    rw [abs_mul,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hp0x ht.le
  have hyscaled : |(2:ℝ)^n*p0.2|≤(2:ℝ)^n*r := by
    rw [abs_mul,abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left hp0y ht.le
  have hxv : -((R*2^n:ℕ):ℝ)≤(v.1:ℝ) ∧ (v.1:ℝ)≤((R*2^n:ℕ):ℝ) := by
    push_cast
    have hx := abs_le.mp hxscaled
    have hh := abs_le.mp hcx
    constructor <;> linarith
  have hyv : -((R*2^n:ℕ):ℝ)≤(v.2:ℝ) ∧ (v.2:ℝ)≤((R*2^n:ℕ):ℝ) := by
    push_cast
    have hy := abs_le.mp hyscaled
    have hh := abs_le.mp hcy
    constructor <;> linarith
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  constructor <;> constructor
  · exact_mod_cast hxv.1
  · exact_mod_cast hxv.2
  · exact_mod_cast hyv.1
  · exact_mod_cast hyv.2

theorem dyadic_testSupport_box {F : Type*} [Fintype F] (T : DyadicQuadFamily F)
    (hplane : PublishedInvarianceOfDomain) :
    ∃R : ℕ,1≤R ∧ ∀n : ℕ,FixedMeshSelectedForest.testSupport hplane T n⊆latticeBox (R*2^n) :=
  scaled_polygon_support_box (fun i => (T.grid i).polygon hplane)

theorem left_mem_box_succ (phase : Bool) {v : Site} {m : ℕ} (hv : v∈latticeBox m) :
    UnitReferenceCover.left phase v∈latticeBox (m+1) := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] at hv ⊢
  unfold UnitReferenceCover.left
  dsimp
  split <;> omega

theorem box_anchor_physical_bound (R n : ℕ) (phase : Bool)
    (a : Site) (ha : a∈UnitReferenceCover.anchors phase (latticeBox (R*2^n))) :
    ‖scaledEmbedding (mesh n) a‖≤2*((R:ℝ)+1) := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
  have hnorm := triangularEmbedding_norm_le_of_mem_box (left_mem_box_succ phase hv)
  have hm : mesh n≤1 := by
    unfold mesh
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hscale : mesh n*((2:ℝ)^n)=1 := by unfold mesh; field_simp
  have hh := mul_le_mul_of_nonneg_left hnorm (mesh_pos n).le
  rw [scaledEmbedding,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mesh_pos n)]
  push_cast at hh
  calc
    _≤mesh n*(2*((R:ℝ)*(2:ℝ)^n+1)) := hh
    _=2*(R:ℝ)*(mesh n*(2:ℝ)^n)+2*mesh n := by ring
    _≤_ := by rw [hscale]; linarith

theorem dyadic_support_and_anchors {F : Type*} [Fintype F] (T : DyadicQuadFamily F)
    (hplane : PublishedInvarianceOfDomain) :
    ∃R : ℕ,1≤R ∧ (∀n : ℕ,FixedMeshSelectedForest.testSupport hplane T n⊆latticeBox (R*2^n)) ∧
      ∀n : ℕ,∀phase : Bool,∀a∈UnitReferenceCover.anchors phase (latticeBox (R*2^n)),
        ‖scaledEmbedding (mesh n) a‖≤2*((R:ℝ)+1) := by
  obtain ⟨R,hR,hs⟩ := dyadic_testSupport_box T hplane
  exact ⟨R,hR,hs,fun n phase a ha => box_anchor_physical_bound R n phase a ha⟩

#print axioms dyadic_testSupport_box
#print axioms dyadic_support_and_anchors
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization
