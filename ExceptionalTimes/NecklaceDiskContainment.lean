import ExceptionalTimes.NecklacePlaneTransmission
import Mathlib.Analysis.Normed.Group.Bounded

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open TriangularPlane

/-- A separating half-plane cannot contain a bounded complementary
component on its exterior side: a straight ray escapes to infinity. -/
theorem NecklaceShape.planeDisk_linear_le (C : NecklaceShape)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ) (hw : L w = 1) (a : ℝ)
    (htrace : ∀ p ∈ C.planeTrace, L p ≤ a) :
    ∀ p ∈ C.planeDisk, L p ≤ a := by
  intro p hp
  rcases hp with hp | hp
  · exact htrace p hp
  by_contra hpa
  have hpa' : a < L p := lt_of_not_ge hpa
  let ray : ℝ → ℝ × ℝ := fun t => p+t • w
  have hcont : Continuous ray := by fun_prop
  have hray : ∀ t, L (ray t) = L p+t := by
    intro t
    simp [ray,map_add,map_smul,hw]
  have hdis : ray '' Ici (0:ℝ) ⊆ C.planeTraceᶜ := by
    rintro q ⟨t,ht,rfl⟩ hq
    have := htrace (ray t) hq
    rw [hray] at this
    change 0 ≤ t at ht
    linarith
  have hconn : IsPreconnected (ray '' Ici (0:ℝ)) :=
    isPreconnected_Ici.image _ hcont.continuousOn
  have hbase : p ∈ ray '' Ici (0:ℝ) := ⟨0,by simp,by simp [ray]⟩
  have hsub := hconn.subset_connectedComponentIn hbase hdis
  obtain ⟨M,hM⟩ := hp.exists_norm_le
  let t : ℝ := max 0 (‖L‖*M-L p+1)
  have ht : 0 ≤ t := le_max_left _ _
  have hbig : ‖L‖*M-L p+1 ≤ t := le_max_right _ _
  have hb : ‖ray t‖ ≤ M := hM _ (hsub ⟨t,ht,rfl⟩)
  have hL : L (ray t) ≤ ‖L‖*M :=
    (le_abs_self _).trans ((L.le_opNorm (ray t)).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _)))
  rw [hray] at hL
  linarith

theorem edgePoint_eq_affine (u v : Site) (t : ℝ) :
    edgePoint u v t = (1-t) • point u+t • point v := by
  ext <;> simp [edgePoint,point] <;> ring

theorem walkTrace_linear_le {u v : Site} (p : triangularGraph.Walk u v)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (a : ℝ)
    (h : ∀ z ∈ p.support, L (point z) ≤ a) :
    ∀ q ∈ walkTrace p, L q ≤ a := by
  intro q hq
  rcases walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ |
    ⟨z,hz,y,hy,_,t,ht0,ht1,rfl⟩
  · exact h z hz
  · rw [edgePoint_eq_affine,map_add,map_smul,map_smul]
    change (1-t)*L (point z)+t*L (point y) ≤ a
    have hz' := h z hz
    have hy' := h y hy
    nlinarith

/-- The actual filled disk inherits every linear bound on its boundary
vertices, with no convexity assumption on the necklace itself. -/
theorem NecklaceShape.planeDisk_linear_le_vertices (C : NecklaceShape)
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ) (hw : L w = 1) (a : ℝ)
    (h : ∀ v ∈ C.vertices, L (point v) ≤ a) :
    ∀ p ∈ C.planeDisk, L p ≤ a := by
  apply C.planeDisk_linear_le L w hw a
  apply walkTrace_linear_le
  intro v hv
  exact h v (by simpa only [← C.cycle_support, List.mem_toFinset] using hv)

#print axioms NecklaceShape.planeDisk_linear_le_vertices

theorem NecklaceShape.planeDisk_coordinate_bounds (C : NecklaceShape) (a : ℝ)
    (h : ∀ v ∈ C.vertices, |(v.1:ℝ)| ≤ a ∧ |(v.2:ℝ)| ≤ a) :
    ∀ p ∈ C.planeDisk, |p.1| ≤ a ∧ |p.2| ≤ a := by
  have hx := C.planeDisk_linear_le_vertices (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (1,0) (by simp) a (fun v hv => (le_abs_self _).trans (h v hv).1)
  have hy := C.planeDisk_linear_le_vertices (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (0,1) (by simp) a (fun v hv => (le_abs_self _).trans (h v hv).2)
  have hnx := C.planeDisk_linear_le_vertices (-ContinuousLinearMap.fst ℝ ℝ ℝ)
    (-1,0) (by simp) a (fun v hv => (neg_le_abs _).trans (h v hv).1)
  have hny := C.planeDisk_linear_le_vertices (-ContinuousLinearMap.snd ℝ ℝ ℝ)
    (0,-1) (by simp) a (fun v hv => (neg_le_abs _).trans (h v hv).2)
  intro p hp
  have hx' := hx p hp
  have hy' := hy p hp
  have hnx' := hnx p hp
  have hny' := hny p hp
  change p.1 ≤ a at hx'
  change p.2 ≤ a at hy'
  change -p.1 ≤ a at hnx'
  change -p.2 ≤ a at hny'
  rw [abs_le,abs_le]
  constructor <;> constructor <;> linarith

/-- A necklace in a finite axial box has its entire literal disk, and
therefore every interior lattice site, in that same box. -/
theorem NecklaceShape.insideSites_subset_latticeBox (C : NecklaceShape) (n : ℕ)
    (h : C.vertices ⊆ latticeBox n) : C.insideSites ⊆ (latticeBox n : Set Site) := by
  have hb : ∀ v ∈ C.vertices, |(v.1:ℝ)| ≤ (n:ℝ) ∧ |(v.2:ℝ)| ≤ (n:ℝ) := by
    intro v hv
    have hmem := h hv
    simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] at hmem
    rw [abs_le,abs_le]
    exact_mod_cast hmem
  intro v hv
  have hvb := C.planeDisk_coordinate_bounds (n:ℝ) hb (point v) hv
  simp only [point,abs_le] at hvb
  change v ∈ latticeBox n
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  exact_mod_cast hvb

#print axioms NecklaceShape.insideSites_subset_latticeBox

/-- The literal disk graph used by the published finite Hex alternative
has only finitely many lattice sites. This follows from geometry alone. -/
theorem NecklaceShape.insideSites_finite (C : NecklaceShape) : C.insideSites.Finite := by
  obtain ⟨n,hn⟩ := finite_set_subset_latticeBox C.vertices.finite_toSet
  exact (latticeBox n).finite_toSet.subset (C.insideSites_subset_latticeBox n hn)

#print axioms NecklaceShape.insideSites_finite

theorem NecklaceShape.planeDisk_centered_coordinate_bounds (C : NecklaceShape)
    (c : ℝ × ℝ) (a : ℝ)
    (h : ∀ v ∈ C.vertices, |(v.1:ℝ)-c.1| ≤ a ∧ |(v.2:ℝ)-c.2| ≤ a) :
    ∀ p ∈ C.planeDisk, |p.1-c.1| ≤ a ∧ |p.2-c.2| ≤ a := by
  have hx := C.planeDisk_linear_le_vertices (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (1,0) (by simp) (a+c.1) (by
      intro v hv
      change (v.1:ℝ) ≤ a+c.1
      have := (abs_le.mp (h v hv).1).2
      linarith)
  have hy := C.planeDisk_linear_le_vertices (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (0,1) (by simp) (a+c.2) (by
      intro v hv
      change (v.2:ℝ) ≤ a+c.2
      have := (abs_le.mp (h v hv).2).2
      linarith)
  have hnx := C.planeDisk_linear_le_vertices (-ContinuousLinearMap.fst ℝ ℝ ℝ)
    (-1,0) (by simp) (a-c.1) (by
      intro v hv
      change -(v.1:ℝ) ≤ a-c.1
      have := (abs_le.mp (h v hv).1).1
      linarith)
  have hny := C.planeDisk_linear_le_vertices (-ContinuousLinearMap.snd ℝ ℝ ℝ)
    (0,-1) (by simp) (a-c.2) (by
      intro v hv
      change -(v.2:ℝ) ≤ a-c.2
      have := (abs_le.mp (h v hv).2).1
      linarith)
  intro p hp
  have hx' := hx p hp
  have hy' := hy p hp
  have hnx' := hnx p hp
  have hny' := hny p hp
  change p.1 ≤ a+c.1 at hx'
  change p.2 ≤ a+c.2 at hy'
  change -p.1 ≤ a-c.1 at hnx'
  change -p.2 ≤ a-c.2 at hny'
  rw [abs_le,abs_le]
  constructor <;> constructor <;> linarith

theorem NecklaceShape.insideSites_centered_box (C : NecklaceShape) (c : Site) (n : ℕ)
    (h : ∀ v ∈ C.vertices, v-c ∈ latticeBox n) :
    ∀ v ∈ C.insideSites, v-c ∈ latticeBox n := by
  have hb : ∀ v ∈ C.vertices,
      |(v.1:ℝ)-(c.1:ℝ)| ≤ (n:ℝ) ∧ |(v.2:ℝ)-(c.2:ℝ)| ≤ (n:ℝ) := by
    intro v hv
    have hmem := h v hv
    simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      Prod.fst_sub,Prod.snd_sub] at hmem
    rw [abs_le,abs_le]
    exact_mod_cast hmem
  intro v hv
  have hvb := C.planeDisk_centered_coordinate_bounds (point c) (n:ℝ) hb (point v) hv
  simp only [point,abs_le] at hvb
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    Prod.fst_sub,Prod.snd_sub]
  exact_mod_cast hvb

/-- A geometric certificate for the frozen inner background: if the
inner necklace lies in a box on the inside of the seam, its entire disk
reads only the designated inside source in every sewn combination. -/
theorem NecklaceShape.sewnField_eqOn_inner_of_box {Λ : Finset Site}
    (C : NecklaceShape) (c : Site) (n : ℕ) (inside : Finset Site)
    (hC : ∀ v ∈ C.vertices, v-c ∈ latticeBox n)
    (hbox : ∀ v, v-c ∈ latticeBox n → v ∈ inside)
    (ω : Sources Λ) (a b : Bool) :
    Set.EqOn (complete (sewnField inside ω a b))
      (complete (if a then ω.2 else ω.1)) C.insideSites := by
  intro v hv
  have hvIn := hbox v (C.insideSites_centered_box c n hC v hv)
  by_cases hvΛ : v ∈ Λ
  · cases a <;> simp [complete,sewnField,hvΛ,hvIn]
  · simp [complete,hvΛ]

#print axioms NecklaceShape.insideSites_centered_box
#print axioms NecklaceShape.sewnField_eqOn_inner_of_box

end ExceptionalTimes.PairSquareSewing
