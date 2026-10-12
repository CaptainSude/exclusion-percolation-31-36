import ExceptionalTimes.PolygonLocalChange

/-! Literal closed-cell polygon crossings are finite-coordinate events.
This avoids replacing clipped polygon cells by an induced lattice graph. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

def cellSupport (A : Set (ℝ × ℝ)) : Set Site :=
  {v | (HexCells.cell v ∩ A).Nonempty}

theorem compact_cellSupport_subset_box {A : Set (ℝ × ℝ)} (hA : IsCompact A) :
    ∃ n, cellSupport A ⊆ (latticeBox n : Set Site) := by
  obtain ⟨r,hr⟩ := hA.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨n,hn⟩ := exists_nat_gt (r+1)
  refine ⟨n,?_⟩
  rintro v ⟨p,hpv,hpA⟩
  have hp : ‖p‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hr hpA
  have hx : |p.1| ≤ r := by simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans hp
  have hy : |p.2| ≤ r := by simpa only [Real.norm_eq_abs] using (norm_snd_le p).trans hp
  obtain ⟨hcx,hcy⟩ := HexCells.coordinate_bounds hpv
  have hxv : -(n:ℝ) ≤ (v.1:ℝ) ∧ (v.1:ℝ) ≤ n := by
    have hp' := abs_le.mp hx
    have hc' := abs_le.mp hcx
    constructor <;> linarith
  have hyv : -(n:ℝ) ≤ (v.2:ℝ) ∧ (v.2:ℝ) ≤ n := by
    have hp' := abs_le.mp hy
    have hc' := abs_le.mp hcy
    constructor <;> linarith
  change v ∈ latticeBox n
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  exact ⟨by exact_mod_cast hxv,by exact_mod_cast hyv⟩

theorem finite_cellSupport {A : Set (ℝ × ℝ)} (hA : IsCompact A) :
    (cellSupport A).Finite := by
  obtain ⟨n,hn⟩ := compact_cellSupport_subset_box hA
  exact (latticeBox n).finite_toSet.subset hn

noncomputable def PolygonQuad.support (Q : PolygonQuad) : Finset Site :=
  (finite_cellSupport Q.compact).toFinset

theorem PolygonQuad.mem_support (Q : PolygonQuad) (v : Site) :
    v ∈ Q.support ↔ (HexCells.cell v ∩ Q.carrier).Nonempty := by
  simp [PolygonQuad.support,cellSupport]

theorem blackCells_inter_eq_of_agree {A : Set (ℝ × ℝ)} {a b : Configuration}
    (hab : EqOn a b (cellSupport A)) :
    globalBlackCells a ∩ A = globalBlackCells b ∩ A := by
  ext p
  constructor
  · rintro ⟨⟨v,hav,hpv⟩,hpA⟩
    exact ⟨⟨v,(hab ⟨p,hpv,hpA⟩) ▸ hav,hpv⟩,hpA⟩
  · rintro ⟨⟨v,hbv,hpv⟩,hpA⟩
    exact ⟨⟨v,(hab ⟨p,hpv,hpA⟩).symm ▸ hbv,hpv⟩,hpA⟩

theorem PolygonQuad.crossing_congr (Q : PolygonQuad) {a b : Configuration}
    (hab : EqOn a b (Q.support : Set Site)) : Q.Crossing a ↔ Q.Crossing b := by
  have heq := blackCells_inter_eq_of_agree (A := Q.carrier) (a := a) (b := b)
    (fun v hv => hab ((Q.mem_support v).mpr hv))
  unfold PolygonQuad.Crossing
  rw [heq]

noncomputable def PolygonQuad.test (Q : PolygonQuad) (ω : Configuration) : Bool :=
  decide (Q.Crossing ω)

theorem PolygonQuad.test_eq_iff (Q : PolygonQuad) (a b : Configuration) :
    Q.test a = Q.test b ↔ (Q.Crossing a ↔ Q.Crossing b) := by
  simp [PolygonQuad.test]

theorem PolygonQuad.test_congr (Q : PolygonQuad) {a b : Configuration}
    (hab : EqOn a b (Q.support : Set Site)) : Q.test a = Q.test b :=
  (Q.test_eq_iff a b).mpr (Q.crossing_congr hab)

noncomputable def polygonFamilySupport {Q : Type*} [Fintype Q]
    (quads : Q → PolygonQuad) : Finset Site :=
  Finset.univ.biUnion (fun q => (quads q).support)

theorem mem_polygonFamilySupport {Q : Type*} [Fintype Q]
    (quads : Q → PolygonQuad) (v : Site) :
    v ∈ polygonFamilySupport quads ↔
      ∃ q, (HexCells.cell v ∩ (quads q).carrier).Nonempty := by
  simp [polygonFamilySupport,PolygonQuad.mem_support]

theorem polygon_test_vector_congr {Q : Type*} [Fintype Q]
    (quads : Q → PolygonQuad) {a b : Configuration}
    (hab : EqOn a b (polygonFamilySupport quads : Set Site)) :
    (fun q => (quads q).test a) = (fun q => (quads q).test b) := by
  funext q
  apply (quads q).test_congr
  intro v hv
  exact hab ((mem_polygonFamilySupport quads v).mpr
    ⟨q,((quads q).mem_support v).mp hv⟩)

theorem PolygonQuad.changed_cell (Q : PolygonQuad) {a b : Configuration}
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b)) :
    ∃ v, a v ≠ b v ∧ (HexCells.cell v ∩ Q.carrier).Nonempty := by
  by_contra hn
  apply hchange
  apply Q.crossing_congr
  intro v hv
  by_contra hab
  exact hn ⟨v,hab,(Q.mem_support v).mp hv⟩

/-- A literal changed crossing intersects the changed pocket, up to the
explicit radius of one actual hexagonal cell. -/
theorem PolygonQuad.changed_cell_near_carrier (Q : PolygonQuad) (P : Probe)
    {a b : Configuration} (hab : ∀ v, v ∉ P.pocket → a v = b v)
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b)) :
    ∃ v, v ∈ P.pocket ∧ a v ≠ b v ∧ ∃ p ∈ Q.carrier,
      p ∈ HexCells.cell v ∧
      dist (physicalHomeomorph P p) (position P.mesh P.center) <
        P.innerRadius/2 + 2*P.mesh := by
  obtain ⟨v,hv,p,hpv,hpQ⟩ := Q.changed_cell hchange
  have hpk : v ∈ P.pocket := by by_contra hn; exact hv (hab v hn)
  refine ⟨v,hpk,hv,p,hpQ,hpv,?_⟩
  have hc := HexTiling.physicalCell_radius (ε := P.mesh) ⟨p,hpv,rfl⟩
  rw [abs_of_pos P.mesh_pos] at hc
  have ht := dist_triangle (physicalHomeomorph P p) (position P.mesh v)
    (position P.mesh P.center)
  change dist (physicalHomeomorph P p) (position P.mesh v) ≤ 2*P.mesh at hc
  change dist (position P.mesh v) (position P.mesh P.center) < P.innerRadius/2 at hpk
  linarith

theorem PolygonQuad.changed_carrier_meets_buffered_ball (Q : PolygonQuad) (P : Probe)
    (he : 16*P.mesh < P.innerRadius) {a b : Configuration}
    (hab : ∀ v, v ∉ P.pocket → a v = b v)
    (hchange : ¬ (Q.Crossing a ↔ Q.Crossing b)) :
    (physicalHomeomorph P '' Q.carrier ∩
      Metric.ball (position P.mesh P.center) (3*P.innerRadius/4)).Nonempty := by
  obtain ⟨v,hv,p,hpv,hpQ⟩ := Q.changed_cell hchange
  exact ⟨physicalHomeomorph P p,⟨p,hpQ,rfl⟩,
    changed_cell_in_buffered_ball P he hab hv ⟨p,hpv,rfl⟩⟩

#print axioms compact_cellSupport_subset_box
#print axioms PolygonQuad.changed_carrier_meets_buffered_ball

end ExceptionalTimes.PairSquareSewing
