import ExceptionalTimes.PolygonCrossingLocality
import ExceptionalTimes.DimerProbeWitness

/-! Arbitrary literal polygon crossing tests, interpreted directly from
the centered finite history kernel. No induced graph dictionary is used. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open CenteredBlocks

variable {I J Q T : Type*}

noncomputable def polygonOverwrittenCross (endpoint : I × Fin 2 ↪ Site)
    (quads : Q → PolygonQuad) (background : T → Configuration) :
    Q → T → (I → PairColor) → Bool :=
  fun q t color => (quads q).test (overwriteDimers endpoint (background t) color)

/-- A flip that changes a literal polygon crossing changes its one
actual endpoint cell, and that cell intersects the polygon carrier. -/
theorem polygon_flip_cell_contact (endpoint : I × Fin 2 ↪ Site) (quad : PolygonQuad)
    (ω : Configuration) (color : I → PairColor) (i : I) (e : Fin 2)
    (hchange : quad.test (overwriteDimers endpoint ω
      (Function.update color i (Function.update (color i) e (!(color i e))))) ≠
      quad.test (overwriteDimers endpoint ω color)) :
    (HexCells.cell (endpoint (i,e)) ∩ quad.carrier).Nonempty := by
  have hc : ¬ (quad.Crossing (overwriteDimers endpoint ω
      (Function.update color i (Function.update (color i) e (!(color i e))))) ↔
      quad.Crossing (overwriteDimers endpoint ω color)) :=
    fun hh => hchange ((quad.test_eq_iff _ _).mpr hh)
  obtain ⟨v,hv,hcontact⟩ := quad.changed_cell hc
  have he : v=endpoint (i,e) := by
    by_contra hn
    exact hv (overwriteDimers_flip_other endpoint ω color i e hn)
  exact he ▸ hcontact

variable [Fintype I] [Fintype J] [Fintype T] [DecidableEq T]

omit [Fintype T] in
/-- Nonzero response forces a genuine changed polygon comparison for
every positive forest life. All other selected dimers agree with the raw
background on its full annular buffer; displacement need not be adjacent. -/
theorem polygon_endpoint_pivotal_life_comparison
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (hsmall : G.margin≤cutoff/100) (quads : Q → PolygonQuad)
    (background : T → Configuration)
    (hpiv : AllEndpointPivotal (polygonOverwrittenCross G.endpoint quads background))
    (life : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop life) :
    let P := dimerLifeProbe G cutoff stop hcut life hactive
    ∃ q t, ∃ a b : Configuration,
      (∀ v, v ∉ P.pocket → a v=b v) ∧ EqOn a (background t) P.region ∧
      EqOn b (background t) P.region ∧ ¬ ((quads q).Crossing a ↔ (quads q).Crossing b) ∧
      (physicalHomeomorph P '' (quads q).carrier ∩
        Metric.ball (position P.mesh P.center) (3*P.innerRadius/4)).Nonempty := by
  let P := dimerLifeProbe G cutoff stop hcut life hactive
  let i := lifeBlock G cutoff stop life
  obtain ⟨z,q,t,e,hchange⟩ := hpiv i
  let color := slice z t
  let changed := Function.update color i (Function.update (color i) e (!(color i e)))
  let a := overwriteDimers G.endpoint (background t) changed
  let b := overwriteDimers G.endpoint (background t) color
  have hc : (quads q).test a ≠ (quads q).test b := by
    simpa only [polygonOverwrittenCross,slice_flipHistory,changed,color,slice,a,b] using hchange
  have hab : ∀ v, v ∉ P.pocket → a v=b v := by
    intro v hv
    apply overwriteDimers_flip_other
    intro he
    apply hv
    rw [he]
    exact lifeProbe_center_endpoint_pocket G cutoff stop hcut life hactive e
  have hcross : ¬ ((quads q).Crossing a ↔ (quads q).Crossing b) :=
    fun hh => hc (((quads q).test_eq_iff _ _).mpr hh)
  refine ⟨q,t,a,b,hab,?_,?_,hcross,?_⟩
  · exact lifeProbe_overwrite_agrees G cutoff stop hcut hsmall life hactive _ _
  · exact lifeProbe_overwrite_agrees G cutoff stop hcut hsmall life hactive _ _
  · exact (quads q).changed_carrier_meets_buffered_ball P
      (lifeProbe_mesh_gap G cutoff stop hcut hsmall life hactive) hab hcross

theorem nonzero_polygon_life_comparison
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (hsmall : G.margin≤cutoff/100) (quads : Q → PolygonQuad)
    (background : T → Configuration) (w : I → (T → PairColor) → ℝ)
    (outer : (Q × T → Bool) → ℝ) (hw : ∀ i, ∑ z, w i z=0)
    (hne : kernel w (fun z => outer (historyTests (polygonOverwrittenCross G.endpoint quads background) z))≠0)
    (life : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop life) :
    let P := dimerLifeProbe G cutoff stop hcut life hactive
    ∃ q t, ∃ a b : Configuration,
      (∀ v, v ∉ P.pocket → a v=b v) ∧ EqOn a (background t) P.region ∧
      EqOn b (background t) P.region ∧ ¬ ((quads q).Crossing a ↔ (quads q).Crossing b) ∧
      (physicalHomeomorph P '' (quads q).carrier ∩
        Metric.ball (position P.mesh P.center) (3*P.innerRadius/4)).Nonempty :=
  polygon_endpoint_pivotal_life_comparison G cutoff stop hcut hsmall quads background
    (pair_history_pivotal_witness w (polygonOverwrittenCross G.endpoint quads background) outer hw hne)
    life hactive

#print axioms polygon_flip_cell_contact
#print axioms nonzero_polygon_life_comparison

end ExceptionalTimes.PairSquareSewing
