import ExceptionalTimes.LatticeBadMass
import ExceptionalTimes.PolygonBoundarySide

/-! The literal distance to an axial polygon boundary implies the thin
coordinate bands counted above. All constants are uniform over the mesh. -/
open Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.LatticeBoundaryMass
noncomputable section
open LatticeRadial LatticeStripMass LatticeBadMass PairSquareSewing HexTiling

theorem scaled_embedding_physical (ε : ℝ) (v : Site) :
    scaledEmbedding ε v=axialPhysical 1 (ε • HexCells.center v) := by
  apply Complex.ext <;>
    simp [scaledEmbedding,axialPhysical,planeMap,triangularEmbedding,HexCells.center] <;> ring

theorem near_segment_band (edge : AxialSegment) {ε δ : ℝ} {v : Site}
    (hδ : 0≤δ) (hnear : ∃ p,edge.contains p ∧
      dist (scaledEmbedding ε v) (planeMap p)≤δ) :
    band edge.horizontal ε edge.level (2*δ) v := by
  obtain ⟨p,⟨t,ht,rfl⟩,hd⟩ := hnear
  have hp := edge.point_onLine t
  have he : planeMap (edge.point t)=axialPhysical 1 (edge.point t) := by
    simp only [axialPhysical,Complex.ofReal_one,one_mul]
  rw [scaled_embedding_physical,he] at hd
  have hc := physical_coordinate_le (by norm_num : (0:ℝ)≤1)
    (ε • HexCells.center v) (edge.point t)
  dsimp only [HexCells.center] at hd
  cases hh : edge.horizontal
  · have hp' : (edge.point t).1=edge.first.1 := by
      simpa only [AxialSegment.onLine,hh,Bool.false_eq_true,ite_false] using hp
    have hb := hc.1
    simp only [one_mul,Prod.smul_fst,smul_eq_mul,HexCells.center,hp'] at hb
    simp only [band,AxialSegment.level,hh,Bool.false_eq_true,ite_false]
    linarith
  · have hp' : (edge.point t).2=edge.first.2 := by
      simpa only [AxialSegment.onLine,hh,ite_true] using hp
    have hb := hc.2
    simp only [one_mul,Prod.smul_snd,smul_eq_mul,HexCells.center,hp'] at hb
    simp only [band,AxialSegment.level,hh,ite_true]
    linarith

theorem near_polygon_band {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) {ε δ : ℝ} {v : Site}
    (hδ : 0≤δ) (hnear : ∃ p∈frontier Q.carrier,
      dist (scaledEmbedding ε v) (planeMap p)≤δ) :
    ∃ e,band (A.edge e).horizontal ε (A.edge e).level (2*δ) v := by
  obtain ⟨p,hp,hd⟩ := hnear
  obtain ⟨e,he⟩ := (A.frontier_iff p).mp hp
  exact ⟨e,near_segment_band (A.edge e) hδ ⟨p,he,hd⟩⟩

def geometricBadTuples {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (edge : E→AxialSegment) (ε δ : ℝ) : Finset (Fin k→s) :=
  Finset.univ.filter (fun x =>
    (∃ i j,i≠j ∧ dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ) ∨
    (∃ i e p,(edge e).contains p ∧ dist (scaledEmbedding ε (x i)) (planeMap p)≤δ))

theorem geometric_bad_mass_le {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (edge : E→AxialSegment) {ε δ r : ℝ} (center : ℂ)
    (hε : 0<ε) (hδ : ε≤δ) (hδ1 : δ≤1) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((geometricBadTuples s k edge ε δ).card:ℝ)≤
      badConstant k (Fintype.card E) r 2 center*δ := by
  have hsub : geometricBadTuples s k edge ε δ ⊆
      badTuples s k (fun e => (edge e).horizontal) (fun e => (edge e).level) ε δ 2 := by
    intro x hx
    rw [geometricBadTuples,Finset.mem_filter] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hx.2 with h | ⟨i,e,p,hp,hd⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,e,near_segment_band (edge e) (hε.le.trans hδ) ⟨p,hp,hd⟩⟩
  have hc : ((geometricBadTuples s k edge ε δ).card:ℝ)≤
      ((badTuples s k (fun e => (edge e).horizontal) (fun e => (edge e).level) ε δ 2).card:ℝ) :=
    by exact_mod_cast Finset.card_le_card hsub
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (bad_mass_le_linear s k _ _ center hε hδ hδ1 hr (by norm_num) hs)


def polygonBadTuples {F : Type*} [Fintype F] (s : Finset Site) (k : ℕ)
    (Q : F→PolygonQuad) (ε δ : ℝ) : Finset (Fin k→s) :=
  Finset.univ.filter (fun x =>
    (∃ i j,i≠j ∧ dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ) ∨
    (∃ i f p,p∈frontier (Q f).carrier ∧
      dist (scaledEmbedding ε (x i)) (planeMap p)≤δ))

/-- The finite family of actual polygon frontiers, together with all
pair collisions, has scaled lattice mass tending uniformly to zero. -/
theorem polygon_bad_mass_le {F : Type*} [Fintype F] {E : F→Type*} [∀ f,Fintype (E f)]
    (s : Finset Site) (k : ℕ) (Q : F→PolygonQuad)
    (A : ∀ f,AxialPolygonPresentation (Q f) (E f))
    {ε δ r : ℝ} (center : ℂ) (hε : 0<ε) (hδ : ε≤δ) (hδ1 : δ≤1) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((polygonBadTuples s k Q ε δ).card:ℝ)≤
      badConstant k (Fintype.card (Σ f,E f)) r 2 center*δ := by
  let edge : (Σ f,E f)→AxialSegment := fun e => (A e.1).edge e.2
  have hsub : polygonBadTuples s k Q ε δ ⊆ geometricBadTuples s k edge ε δ := by
    intro x hx
    rw [polygonBadTuples,Finset.mem_filter] at hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases hx.2 with h | ⟨i,f,p,hp,hd⟩
    · exact Or.inl h
    · obtain ⟨e,he⟩ := ((A f).frontier_iff p).mp hp
      exact Or.inr ⟨i,⟨f,e⟩,p,he,hd⟩
  have hc : ((polygonBadTuples s k Q ε δ).card:ℝ)≤
      ((geometricBadTuples s k edge ε δ).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (geometric_bad_mass_le s k edge center hε hδ hδ1 hr hs)

#print axioms polygon_bad_mass_le
#print axioms near_polygon_band
#print axioms geometric_bad_mass_le
end
end ExceptionalTimes.LatticeBoundaryMass



