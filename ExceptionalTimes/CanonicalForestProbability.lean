import ExceptionalTimes.CanonicalLifeStatic
import ExceptionalTimes.CanonicalSpatialProduct

/-! The actual canonical two-time exterior, grouped by the whole dimers
meeting each actual life probe. Spatial independence and the necessary
event map are proved for one identified law. -/

open scoped Classical BigOperators
open Set
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw ForestArmProbability
open CenteredBlocks

variable {I J B Q : Type*} [Fintype I] [Fintype J] [Fintype B]

/-- An entire exterior dimer touching the annular region lies in the
expanded forest buffer, provided its endpoint distance is at most margin. -/
theorem lifeProbe_near_region_buffer (G : DimerGeometry I J)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (a : DimerLife G cutoff stop)
    (hactive : LifeProbeActive G cutoff stop a) {v w : Site}
    (hv : v ∈ (dimerLifeProbe G cutoff stop hcut a hactive).region)
    (hvw : dist (position G.mesh v) (position G.mesh w)≤G.margin) :
    w ∈ sites selectedRoot (dimerAnchor G) cutoff stop G.margin (position G.mesh) a := by
  let P := dimerLifeProbe G cutoff stop hcut a hactive
  change P.innerRadius/2≤dist (position G.mesh v) (position G.mesh P.center) ∧
    dist (position G.mesh v) (position G.mesh P.center)≤2*P.outerRadius at hv
  rw [dist_comm (position G.mesh v) (position G.mesh P.center)] at hv
  have h1 := hv.1
  have h2 := hv.2
  have ht := dist_triangle (position G.mesh P.center) (position G.mesh v) (position G.mesh w)
  have hs := dist_triangle (position G.mesh P.center) (position G.mesh w) (position G.mesh v)
  rw [dist_comm (position G.mesh w) (position G.mesh v)] at hs
  change 4*max _ _-G.margin≤dist _ _ ∧ dist _ _≤_ /4+G.margin
  rw [lifeProbe_center G cutoff stop hcut a hactive]
  change 4*max _ _-G.margin≤dist (position G.mesh P.center) (position G.mesh w) ∧
    dist (position G.mesh P.center) (position G.mesh w)≤_ /4+G.margin
  dsimp only [P,dimerLifeProbe,lifeInner,lifeOuter] at *
  constructor <;> linarith

def lifeBlocks (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (a : DimerLife G cutoff stop) : Set B :=
  {b | ∃ hactive : LifeProbeActive G cutoff stop a, ∃ e,
    slot (b,e) ∈ (dimerLifeProbe G cutoff stop hcut a hactive).region}

omit [Fintype B] in
theorem lifeBlocks_pairwise (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100) :
    Pairwise (fun a b => Disjoint (lifeBlocks G slot cutoff stop hcut a)
      (lifeBlocks G slot cutoff stop hcut b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro d ⟨ha,e,he⟩ ⟨hb,f,hf⟩
  exact Set.disjoint_left.mp
    (sites_pairwise selectedRoot (dimerAnchor G) (position G.mesh) hcut hsmall hab)
    (lifeProbe_region_subset G cutoff stop hcut a ha he)
    (lifeProbe_near_region_buffer G cutoff stop hcut b hb hf (hspan d f e))

theorem canonicalBackground_agrees (slot : B × Fin 2 ↪ Site) (S : Set Site)
    (ω η : (B → Color) × (B → Color))
    (he : ∀ b e, slot (b,e) ∈ S → ω.1 b=η.1 b ∧ ω.2 b=η.2 b) (t : Bool) :
    EqOn (canonicalBackground slot ω t) (canonicalBackground slot η t) S := by
  intro v hv
  by_cases hr : v ∈ Set.range slot
  · obtain ⟨⟨b,e⟩,rfl⟩ := hr
    have h := he b e hv
    unfold canonicalBackground ActivePartitionLaw.pairDecode
    rw [slot.injective.extend_apply,slot.injective.extend_apply]
    cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact congrFun h.1 e
    · exact congrFun h.2 e
  · unfold canonicalBackground ActivePartitionLaw.pairDecode
    rw [Function.extend_apply' _ _ _ hr,Function.extend_apply' _ _ _ hr]

theorem canonical_life_event_local (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (board : Q → ℕ) (a : DimerLife G cutoff stop)
    (ω η : (B → Color) × (B → Color))
    (he : ∀ b ∈ lifeBlocks G slot cutoff stop hcut a, ω.1 b=η.1 b ∧ ω.2 b=η.2 b) :
    DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot ω) ↔
      DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot η) := by
  apply forall_congr'
  intro hactive
  apply exists_congr
  intro q
  apply exists_congr
  intro t
  apply straightProbeArms_locality
  apply canonicalBackground_agrees
  intro b e hb
  exact he b ⟨hactive,e,hb⟩

/-- Exact factorization of the actual life events, including their
quad/time alternatives, under the actual canonical dimer law. -/
theorem canonical_life_event_product (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1) (board : Q → ℕ) :
    probability (manyLaw p hp0 hp1)
      (fun z => ∀ a, DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot z)) =
      ∏ a, probability (manyLaw p hp0 hp1)
        (fun z => DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot z)) :=
  CanonicalSpatialProduct.manyLaw_local_product p hp0 hp1
    (lifeBlocks G slot cutoff stop hcut) (lifeBlocks_pairwise G slot hspan cutoff stop hcut hsmall)
    _ (canonical_life_event_local G slot cutoff stop hcut board)

/-- A literal nonzero centered response is supported on all the life
events. The resulting product bound follows from canonical spatial
factorization, with no assumed event-level forest estimate. -/
theorem canonical_centered_life_product
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (slot : B × Fin 2 ↪ Site)
    (hspan : ∀ b e f, dist (position G.mesh (slot (b,e))) (position G.mesh (slot (b,f)))≤G.margin)
    (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (board : Q → ℕ) (hboard : ∀ q, 0<board q) (hscale : ∀ q, 3*(stop/8)<G.mesh*board q)
    (corner : Q → Bool → Bool → J)
    (hcorner : ∀ q s t, G.root (corner q s t)=axialPhysical G.mesh
      (signedSide (board q) s,signedSide (board q) t))
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (w : I → (Bool → CenteredBlocks.PairColor) → ℝ)
    (outer : ((B → Color) × (B → Color)) → (Q × Bool → Bool) → ℝ)
    (hw : ∀ i, ∑ z, w i z=0)
    (hf : ∀ o z, |outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z)|≤1) :
    |(manyLaw p hp0 hp1).expect (fun o => kernel w (fun z =>
      outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z)))| ≤
      (∏ i, variation (w i))*∏ a, probability (manyLaw p hp0 hp1)
        (fun z => DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot z)) := by
  let E := fun o => ∀ a, DimerLifeArmEvent G cutoff stop hcut board a (canonicalBackground slot o)
  let f := fun o => kernel w (fun z =>
    outer o (historyTests (overwrittenCross G.endpoint board (canonicalBackground slot o)) z))
  have hpoint (o) : |f o|≤(∏ i, variation (w i))*EnvironmentVariance.indicator (E o) := by
    by_cases he : E o
    · simp only [EnvironmentVariance.indicator,ite_eq_left he,mul_one]
      simpa only [mul_one] using kernel_variation_bound w _ 1 (hf o)
    · have hz : f o=0 := by
        by_contra hn
        exact he (nonzero_centered_life_events hbulkSource hhalfSource G cutoff stop hcut hsmall
          board hboard hscale corner hcorner (canonicalBackground slot o) w (outer o) hw hn)
      simp only [hz,abs_zero,EnvironmentVariance.indicator,ite_eq_right he,mul_zero,le_refl]
  calc
    _ ≤ (manyLaw p hp0 hp1).expect (fun o => |f o|) := (manyLaw p hp0 hp1).abs_expect_le f
    _ ≤ (manyLaw p hp0 hp1).expect (fun o => (∏ i, variation (w i))*EnvironmentVariance.indicator (E o)) :=
      (manyLaw p hp0 hp1).expect_mono hpoint
    _ = _ := by
      rw [FiniteLaw.expect_const_mul]
      congr 1
      exact canonical_life_event_product G slot hspan cutoff stop hcut hsmall p hp0 hp1 board

#print axioms canonical_life_event_product
#print axioms canonical_centered_life_product

end ExceptionalTimes.PairSquareSewing
