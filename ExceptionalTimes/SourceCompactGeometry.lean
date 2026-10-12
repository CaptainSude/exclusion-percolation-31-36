import ExceptionalTimes.SourceFullNormalizedDyadic
import ExceptionalTimes.LatticeBoundaryMass

/-! Concrete compact good-location ranges for the actual polygon tests.
The complement of the counted collision/frontier event lies in this
range, so the uniform source sewing theorem applies directly. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mem_polygon_bad {F : Type*} [Fintype F] (s : Finset Site) (k : ℕ)
    (Q : F→PolygonQuad) (e δ : ℝ) (x : Fin k→s) :
    x∈LatticeBoundaryMass.polygonBadTuples s k Q e δ ↔
      (∃i j,i≠j ∧ dist (LatticeRadial.scaledEmbedding e (x i)) (LatticeRadial.scaledEmbedding e (x j))≤δ) ∨
      (∃i j p,p∈frontier (Q j).carrier ∧ dist (LatticeRadial.scaledEmbedding e (x i)) (HexTiling.planeMap p)≤δ) := by
  simp only [LatticeBoundaryMass.polygonBadTuples,Finset.mem_filter,Finset.mem_univ,true_and]

def compactLocations {q k : ℕ} (Q : Fin q→PolygonQuad) (center : ℂ) (r δ : ℝ) :
    Set (Fin (k+1)→ℂ) :=
  {x | (∀i,‖x i-center‖≤r) ∧
    (∀i j,i≠j→δ≤dist (x i) (x j)) ∧
    (∀i j,∀p∈frontier (Q j).carrier,δ≤dist (x i) (HexTiling.planeMap p))}

theorem compactLocations_closed {q k : ℕ} (Q : Fin q→PolygonQuad) (center : ℂ) (r δ : ℝ) :
    IsClosed (compactLocations (k:=k) Q center r δ) := by
  have hb : IsClosed {x : Fin (k+1)→ℂ | ∀i,‖x i-center‖≤r} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le ((continuous_apply i).sub continuous_const).norm continuous_const)
  have hp : IsClosed {x : Fin (k+1)→ℂ | ∀i j,i≠j→δ≤dist (x i) (x j)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_le continuous_const ((continuous_apply i).dist (continuous_apply j)))))
  have hf : IsClosed {x : Fin (k+1)→ℂ |
      ∀i j,∀p∈frontier (Q j).carrier,δ≤dist (x i) (HexTiling.planeMap p)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _j => isClosed_iInter (fun _p =>
      isClosed_iInter (fun _ => isClosed_le continuous_const ((continuous_apply i).dist continuous_const)))))
  exact hb.inter (hp.inter hf)

theorem compactLocations_compact {q k : ℕ} (Q : Fin q→PolygonQuad) (center : ℂ) (r δ : ℝ) :
    IsCompact (compactLocations (k:=k) Q center r δ) := by
  apply (isCompact_univ_pi (fun _ : Fin (k+1) => isCompact_closedBall center r)).of_isClosed_subset
    (compactLocations_closed Q center r δ)
  intro x hx i _
  exact (Metric.mem_closedBall).mpr (by simpa only [dist_eq_norm] using hx.1 i)

def compactGeometry {q k : ℕ} (Q : Fin q→PolygonQuad) (center : ℂ) (r δ : ℝ)
    (hδ : 0<δ) : SourceSeparatedGeometry q k where
  quads := Q
  locations := compactLocations Q center r δ
  compact_locations := compactLocations_compact Q center r δ
  margin := δ
  margin_pos := hδ
  boxRadius := ‖center‖+r+δ
  separated := fun _ hx => hx.2.1
  boundary_separated := fun _ hx => hx.2.2
  box_separated := by
    intro x hx i
    have hn : ‖x i‖≤‖x i-center‖+‖center‖ := by
      calc
        _=‖(x i-center)+center‖ := by rw [sub_add_cancel]
        _≤_ := norm_add_le _ _
    linarith [hx.1 i]

theorem compactGeometry_admissible_of_not_bad {q k : ℕ} (Q : Fin q→PolygonQuad)
    (center : ℂ) (r δ : ℝ) (hδ : 0<δ) (s : Finset Site) (e : ℝ)
    (hs : ∀v∈s,‖LatticeRadial.scaledEmbedding e v-center‖≤r)
    (x : Fin (k+1)→s)
    (hx : x∉LatticeBoundaryMass.polygonBadTuples s (k+1) Q e δ) :
    (compactGeometry Q center r δ hδ).Admissible e (fun i => (x i).val) := by
  change (∀i,‖position e (x i)-center‖≤r) ∧
    (∀i j,i≠j→δ≤dist (position e (x i)) (position e (x j))) ∧
    (∀i j,∀p∈frontier (Q j).carrier,δ≤dist (position e (x i)) (HexTiling.planeMap p))
  have hpos (v : Site) : position e v=LatticeRadial.scaledEmbedding e v := rfl
  refine ⟨fun i => hs (x i) (x i).property,?_,?_⟩
  · intro i j hij
    by_contra h
    apply hx
    apply (mem_polygon_bad s (k+1) Q e δ x).mpr
    exact Or.inl ⟨i,j,hij,(lt_of_not_ge (by simpa only [hpos] using h)).le⟩
  · intro i j p hp
    by_contra h
    apply hx
    apply (mem_polygon_bad s (k+1) Q e δ x).mpr
    exact Or.inr ⟨i,j,p,hp,(lt_of_not_ge (by simpa only [hpos] using h)).le⟩

#print axioms compactLocations_compact
#print axioms compactGeometry_admissible_of_not_bad
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization
