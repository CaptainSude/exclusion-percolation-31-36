import ExceptionalTimes.PolygonLifeChoice
import ExceptionalTimes.CanonicalForestProbability

/-! Literal polygon life events factor under the actual canonical law
because their whole dimer-coordinate supports are disjoint. The selected
events are constructed from polygon geometry before the signed response. -/

open Set
open scoped Classical BigOperators

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ManyDimerLaw DimerLaw CenteredBlocks

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B]

theorem canonical_polygon_life_event_local (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff)
    (choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q) (a : DimerLife G cutoff stop)
    (ω η : (B → Color) × (B → Color))
    (he : ∀ b ∈ lifeBlocks G slot cutoff stop hcut a, ω.1 b=η.1 b ∧ ω.2 b=η.2 b) :
    PolygonLifeEvent choice a (canonicalBackground slot ω) ↔
      PolygonLifeEvent choice a (canonicalBackground slot η) := by
  apply forall_congr'
  intro hactive
  apply exists_congr
  intro q
  apply exists_congr
  intro t
  apply (choice a hactive q).locality
  apply canonicalBackground_agrees
  intro b e hb
  exact he b ⟨hactive,e,hb⟩

theorem canonical_polygon_life_event_product (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q) :
    probability (manyLaw p hp0 hp1)
      (fun z => ∀ a, PolygonLifeEvent choice a (canonicalBackground slot z)) =
      ∏ a, probability (manyLaw p hp0 hp1)
        (fun z => PolygonLifeEvent choice a (canonicalBackground slot z)) :=
  CanonicalSpatialProduct.manyLaw_local_product p hp0 hp1
    (lifeBlocks G slot cutoff stop hcut) (lifeBlocks_pairwise G slot hspan cutoff stop hcut hsmall)
    _ (canonical_polygon_life_event_local G slot cutoff stop hcut choice)

/-- This is the actual signed-law bound. All necessary arm events are
derived from finite polygon geometry and the two published local-change
clauses; no event-level forest probability estimate is a premise. -/
theorem canonical_polygon_centered_life_product
    (hbulk : PublishedPolygonBulkArms) (hhalf : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (quads : Q → PolygonQuad) (E : Q → Type*)
    (A : ∀ q, AxialPolygonPresentation (quads q) (E q)) (δ : Q → ℝ)
    (hscale : ∀ q, 6*(stop/8)<G.mesh*δ q)
    (hparallel : ∀ q i j, ((A q).edge i).horizontal=((A q).edge j).horizontal →
      ((A q).edge i).level≠((A q).edge j).level →
        δ q≤|((A q).edge i).level-((A q).edge j).level|)
    (vertex : ∀ q, E q → Bool → J)
    (hvertex : ∀ q i b, G.root (vertex q i b)=axialPhysical G.mesh
      (if b then ((A q).edge i).last else ((A q).edge i).first))
    (hinteger : ∀ q i, ∃ level : ℤ, ((A q).edge i).level=(level:ℝ))
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (w : I → (Bool → PairColor) → ℝ)
    (outer : ((B → Color) × (B → Color)) → (Q × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ z, w i z=0)
    (hf : ∀ o z,
      |outer o (historyTests (polygonOverwrittenCross G.endpoint quads (canonicalBackground slot o)) z)|≤1) :
    ∃ choice : PolygonLifeChoiceAssignment G cutoff stop hcut Q,
      |(manyLaw p hp0 hp1).expect (fun o => kernel w (fun z =>
        outer o (historyTests (polygonOverwrittenCross G.endpoint quads (canonicalBackground slot o)) z)))| ≤
        (∏ i, variation (w i))*∏ a, probability (manyLaw p hp0 hp1)
          (fun z => PolygonLifeEvent choice a (canonicalBackground slot z)) := by
  obtain ⟨choice,hnecessary⟩ := exists_polygon_life_assignment (T := Bool) hbulk hhalf G
    cutoff stop hcut hsmall quads E A δ hscale hparallel vertex hvertex hinteger
  refine ⟨choice,?_⟩
  let Event := fun o => ∀ a, PolygonLifeEvent choice a (canonicalBackground slot o)
  let f := fun o => kernel w (fun z =>
    outer o (historyTests (polygonOverwrittenCross G.endpoint quads (canonicalBackground slot o)) z))
  have hpoint (o) : |f o|≤(∏ i, variation (w i))*EnvironmentVariance.indicator (Event o) := by
    by_cases he : Event o
    · simp only [EnvironmentVariance.indicator,ite_eq_left he,mul_one]
      simpa only [mul_one] using kernel_variation_bound w _ 1 (hf o)
    · have hz : f o=0 := by
        by_contra hn
        exact he (hnecessary (canonicalBackground slot o) w (outer o) hw hn)
      simp only [hz,abs_zero,EnvironmentVariance.indicator,ite_eq_right he,mul_zero,le_refl]
  calc
    _ ≤ (manyLaw p hp0 hp1).expect (fun o => |f o|) := (manyLaw p hp0 hp1).abs_expect_le f
    _ ≤ (manyLaw p hp0 hp1).expect (fun o => (∏ i, variation (w i))*EnvironmentVariance.indicator (Event o)) :=
      (manyLaw p hp0 hp1).expect_mono hpoint
    _ = _ := by
      rw [FiniteLaw.expect_const_mul]
      congr 1
      exact canonical_polygon_life_event_product G slot hspan cutoff stop hcut hsmall p hp0 hp1 choice

#print axioms canonical_polygon_life_event_product
#print axioms canonical_polygon_centered_life_product

end ExceptionalTimes.PairSquareSewing
