import ExceptionalTimes.PolygonProbeChoice
import ExceptionalTimes.PolygonDimerWitness

/-! All actual polygon vertices and marked points are fixed forest roots.
The existing Kruskal life theorem supplies their clearance, so the polygon
probe selection applies to each literal positive life. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open ForestArmProbability CenteredBlocks

variable {I J : Type*} [Fintype I] [Fintype J]

theorem dimer_life_polygon_clearance {E : Type*} (G : DimerGeometry I J)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (edge : E → AxialSegment)
    (vertex : E → Bool → J)
    (hvertex : ∀ i b, G.root (vertex i b)=
      axialPhysical G.mesh (if b then (edge i).last else (edge i).first))
    (life : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop life) :
    let P := dimerLifeProbe G cutoff stop hcut life hactive
    ∀ i, 8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (edge i).first) ∧
      8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (edge i).last) := by
  let P := dimerLifeProbe G cutoff stop hcut life hactive
  have hs := ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop life.property
  change ∀ i, 8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (edge i).first) ∧
    8*P.outerRadius≤dist (position P.mesh P.center) (axialPhysical P.mesh (edge i).last)
  intro i
  have hd (b : Bool) : KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop life.val ≤
      dist (position G.mesh P.center)
        (axialPhysical G.mesh (if b then (edge i).last else (edge i).first)) := by
    have hout : Sum.inr (vertex i b) ∉ life.val :=
      fun hin => hs.2.1 _ hin ⟨vertex i b,rfl⟩
    have h := KruskalLives.life_external_distance hs.1 hs.2.2
      (center_mem selectedRoot (dimerAnchor G) cutoff stop life) hout
    rw [lifeProbe_center G cutoff stop hcut life hactive] at h
    change KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop life.val ≤
      dist (position G.mesh P.center) (G.root (vertex i b)) at h
    rwa [hvertex] at h
  have hf := hd false
  have hl := hd true
  simp only [Bool.false_eq_true,ite_false,ite_true] at hf hl
  change 8*(KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop life.val/8)≤_ ∧
    8*(KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop life.val/8)≤_
  have hmesh : P.mesh=G.mesh := rfl
  rw [hmesh]
  constructor <;> linarith

theorem exists_dimer_life_polygon_choice {Q : PolygonQuad} {E : Type*}
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (hsmall : G.margin≤cutoff/100) (A : AxialPolygonPresentation Q E) {δ : ℝ}
    (hscale : 6*(stop/8)<G.mesh*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (vertex : E → Bool → J)
    (hvertex : ∀ i b, G.root (vertex i b)=
      axialPhysical G.mesh (if b then (A.edge i).last else (A.edge i).first))
    (hinteger : ∀ i, ∃ level : ℤ, (A.edge i).level=(level:ℝ))
    (life : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop life) :
    let P := dimerLifeProbe G cutoff stop hcut life hactive
    ∃ choice : PolygonArmChoice P, ∀ ω a b : Configuration,
      (∀ v, v ∉ P.pocket → a v=b v) → EqOn a ω P.region → EqOn b ω P.region →
      ¬ (Q.Crossing a ↔ Q.Crossing b) → choice.event ω := by
  let P := dimerLifeProbe G cutoff stop hcut life hactive
  have hs := ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop life.property
  have hstop := KruskalLives.death_le_stop hs.1
  apply exists_polygonArmChoice hbulk hhalf A P
    (lifeProbe_mesh_gap G cutoff stop hcut hsmall life hactive) _ hparallel
    (dimer_life_polygon_clearance G cutoff stop hcut A.edge vertex hvertex life hactive) hinteger
  change 6*(KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop life.val/8)<G.mesh*δ
  linarith

abbrev PolygonLifeChoiceAssignment (G : DimerGeometry I J)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (Q : Type*) :=
  ∀ life : DimerLife G cutoff stop, ∀ ha : LifeProbeActive G cutoff stop life,
    Q → PolygonArmChoice (dimerLifeProbe G cutoff stop hcut life ha)

def PolygonLifeEvent {Q T : Type*} {G : DimerGeometry I J}
    {cutoff stop : ℝ} {hcut : 0<cutoff}
    (choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q)
    (life : DimerLife G cutoff stop) (background : T → Configuration) : Prop :=
  ∀ ha, ∃ q t, (choice life ha q).event (background t)

/-- The probe choices are fixed before any background configuration or
signed history is supplied. Only quad/time alternatives remain in each
necessary life event. -/
theorem exists_polygon_life_assignment {Q T : Type*} [Fintype T] [DecidableEq T]
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (hsmall : G.margin≤cutoff/100) (quads : Q → PolygonQuad) (E : Q → Type*)
    (A : ∀ q, AxialPolygonPresentation (quads q) (E q)) (δ : Q → ℝ)
    (hscale : ∀ q, 6*(stop/8)<G.mesh*δ q)
    (hparallel : ∀ q i j, ((A q).edge i).horizontal=((A q).edge j).horizontal →
      ((A q).edge i).level≠((A q).edge j).level →
        δ q≤|((A q).edge i).level-((A q).edge j).level|)
    (vertex : ∀ q, E q → Bool → J)
    (hvertex : ∀ q i b, G.root (vertex q i b)=axialPhysical G.mesh
      (if b then ((A q).edge i).last else ((A q).edge i).first))
    (hinteger : ∀ q i, ∃ level : ℤ, ((A q).edge i).level=(level:ℝ)) :
    ∃ choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q,
      ∀ (background : T → Configuration) (w : I → (T → PairColor) → ℝ)
        (outer : (Q × T → Bool) → ℝ),
        (∀ i, ∑ z, w i z=0) →
        kernel w (fun z => outer (historyTests (polygonOverwrittenCross G.endpoint quads background) z))≠0 →
        ∀ life, PolygonLifeEvent choice life background := by
  choose choices hchoices using fun (life : DimerLife G cutoff stop)
      (ha : LifeProbeActive G cutoff stop life) (q : Q) =>
    exists_dimer_life_polygon_choice hbulk hhalf G cutoff stop hcut hsmall
      (A q) (hscale q) (hparallel q) (vertex q) (hvertex q) (hinteger q) life ha
  refine ⟨choices,?_⟩
  intro background w outer hw hk life ha
  obtain ⟨q,t,a,b,hab,haa,hbb,hchange,_⟩ := nonzero_polygon_life_comparison
    G cutoff stop hcut hsmall quads background w outer hw hk life ha
  exact ⟨q,t,hchoices life ha q (background t) a b hab haa hbb hchange⟩

#print axioms dimer_life_polygon_clearance
#print axioms exists_dimer_life_polygon_choice
#print axioms exists_polygon_life_assignment

end ExceptionalTimes.PairSquareSewing
