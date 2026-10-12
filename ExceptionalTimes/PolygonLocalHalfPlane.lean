import ExceptionalTimes.PolygonSegmentSeparation
import Mathlib.Analysis.Convex.PathConnected

/-! The local closed-side conclusion follows from actual boundary geometry
and regular closedness. No local carrier/half-plane identity is assumed. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

theorem preconnected_avoiding_frontier {X : Type*} [TopologicalSpace X]
    {A S : Set X} (hA : IsClosed A) (hS : IsPreconnected S)
    (havoid : ∀ x ∈ S, x ∉ frontier A) :
    S ⊆ interior A ∨ S ⊆ Aᶜ := by
  apply hS.subset_or_subset isOpen_interior hA.isOpen_compl
  · exact disjoint_left.mpr (fun _ hx hn => hn (interior_subset hx))
  · intro x hx
    by_cases hxA : x ∈ A
    · left
      by_contra hn
      exact havoid x hx (hA.frontier_eq ▸ ⟨hxA,hn⟩)
    · exact Or.inr hxA

/-- If the boundary of a regular closed set is one affine hyperplane in
an open convex neighborhood, the carrier occupies exactly one closed side
there. This also excludes cracks and double-sided boundary conventions. -/
theorem local_halfSpace_of_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A U : Set E) (L : E →ᵃ[ℝ] ℝ)
    (hregular : closure (interior A) = A) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hzero : ∃ z ∈ U, L z = 0)
    (hline : ∀ x ∈ U, x ∈ frontier A ↔ L x = 0) :
    (∀ x ∈ U, x ∈ A ↔ 0 ≤ L x) ∨
      (∀ x ∈ U, x ∈ A ↔ L x ≤ 0) := by
  have hA : IsClosed A := hregular ▸ isClosed_closure
  have hpos := preconnected_avoiding_frontier hA
    (hconv.inter ((convex_Ioi (0:ℝ)).affine_preimage L)).isPreconnected
    (fun x hx hf => ne_of_gt hx.2 ((hline x hx.1).mp hf))
  have hneg := preconnected_avoiding_frontier hA
    (hconv.inter ((convex_Iio (0:ℝ)).affine_preimage L)).isPreconnected
    (fun x hx hf => ne_of_lt hx.2 ((hline x hx.1).mp hf))
  have hzA : ∀ x ∈ U, L x = 0 → x ∈ A := by
    intro x hx hz
    exact hA.frontier_subset ((hline x hx).mpr hz)
  have hnotBothInside : ¬ ((U ∩ L ⁻¹' Ioi 0) ⊆ interior A ∧
      (U ∩ L ⁻¹' Iio 0) ⊆ interior A) := by
    rintro ⟨hp,hn⟩
    have hsub : U ⊆ A := by
      intro x hx
      rcases lt_trichotomy (L x) 0 with h | h | h
      · exact interior_subset (hn ⟨hx,h⟩)
      · exact hzA x hx h
      · exact interior_subset (hp ⟨hx,h⟩)
    obtain ⟨z,hz,hz0⟩ := hzero
    have hfront := (hline z hz).mpr hz0
    exact hfront.2 (interior_maximal hsub hU hz)
  have hnotBothOutside : ¬ ((U ∩ L ⁻¹' Ioi 0) ⊆ Aᶜ ∧
      (U ∩ L ⁻¹' Iio 0) ⊆ Aᶜ) := by
    rintro ⟨hp,hn⟩
    have hsub : U ⊆ (interior A)ᶜ := by
      intro x hx hxi
      rcases lt_trichotomy (L x) 0 with h | h | h
      · exact hn ⟨hx,h⟩ (interior_subset hxi)
      · exact ((hline x hx).mpr h).2 hxi
      · exact hp ⟨hx,h⟩ (interior_subset hxi)
    obtain ⟨z,hz,hz0⟩ := hzero
    have hzc : z ∈ closure (interior A) := hregular.symm ▸ hzA z hz hz0
    have hzint : z ∈ interior ((interior A)ᶜ) := interior_maximal hsub hU hz
    rw [interior_compl] at hzint
    exact hzint hzc
  rcases hpos with hp | hp <;> rcases hneg with hn | hn
  · exact False.elim (hnotBothInside ⟨hp,hn⟩)
  · left
    intro x hx
    constructor
    · intro hxA
      by_contra hh
      exact hn ⟨hx,lt_of_not_ge hh⟩ hxA
    · intro hh
      rcases eq_or_lt_of_le hh with hh | hh
      · exact hzA x hx hh.symm
      · exact interior_subset (hp ⟨hx,hh⟩)
  · right
    intro x hx
    constructor
    · intro hxA
      by_contra hh
      exact hp ⟨hx,lt_of_not_ge hh⟩ hxA
    · intro hh
      rcases lt_or_eq_of_le hh with hh | hh
      · exact interior_subset (hn ⟨hx,hh⟩)
      · exact hzA x hx hh
  · exact False.elim (hnotBothOutside ⟨hp,hn⟩)

theorem closed_halfSpace_of_local_side {E : Type*} [TopologicalSpace E]
    (A U : Set E) (f : E → ℝ) (hf : Continuous f) (hA : IsClosed A)
    (hline : ∀ x ∈ closure U, x ∈ frontier A ↔ f x = 0)
    (hside : ∀ x ∈ U, x ∈ A ↔ 0 ≤ f x) :
    ∀ x ∈ closure U, x ∈ A ↔ 0 ≤ f x := by
  intro x hx
  constructor
  · intro hxA
    by_contra hn
    have hneg : f x < 0 := lt_of_not_ge hn
    have hxi : x ∈ interior A := by
      by_contra hi
      have hz := (hline x hx).mp (hA.frontier_eq ▸ ⟨hxA,hi⟩)
      linarith
    have hc : x ∈ closure (U ∩ {y | f y < 0}) :=
      (isOpen_lt hf continuous_const).closure_inter ⟨hx,hneg⟩
    have hdis : U ∩ {y | f y < 0} ⊆ (interior A)ᶜ := by
      rintro y ⟨hyU,hyf⟩ hyA
      exact not_lt_of_ge ((hside y hyU).mp (interior_subset hyA)) hyf
    exact closure_minimal hdis isOpen_interior.isClosed_compl hc hxi
  · intro hxnonneg
    rcases eq_or_lt_of_le hxnonneg with hz | hpos
    · exact hA.frontier_subset ((hline x hx).mpr hz.symm)
    · have hc : x ∈ closure (U ∩ {y | 0 < f y}) :=
        (isOpen_lt continuous_const hf).closure_inter ⟨hx,hpos⟩
      apply closure_minimal (t := A) _ hA hc
      rintro y ⟨hyU,hyf⟩
      exact (hside y hyU).mpr hyf.le

/-- The exact closed-ball version follows from the open version and the
same literal frontier identity, including points on the ball boundary. -/
theorem local_closed_halfSpace_of_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A U : Set E) (L : E →ᵃ[ℝ] ℝ) (hL : Continuous L)
    (hregular : closure (interior A) = A) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hzero : ∃ z ∈ U, L z = 0)
    (hline : ∀ x ∈ closure U, x ∈ frontier A ↔ L x = 0) :
    (∀ x ∈ closure U, x ∈ A ↔ 0 ≤ L x) ∨
      (∀ x ∈ closure U, x ∈ A ↔ L x ≤ 0) := by
  have hA : IsClosed A := hregular ▸ isClosed_closure
  rcases local_halfSpace_of_frontier A U L hregular hU hconv hzero
    (fun x hx => hline x (subset_closure hx)) with hp | hn
  · exact Or.inl (closed_halfSpace_of_local_side A U L hL hA hline hp)
  · right
    have ht := closed_halfSpace_of_local_side A U (fun x => -L x) hL.neg hA
      (by simpa only [neg_eq_zero] using hline)
      (by simpa only [neg_nonneg] using hn)
    simpa only [neg_nonneg] using ht

#print axioms local_halfSpace_of_frontier
#print axioms local_closed_halfSpace_of_frontier

noncomputable def axialPhysicalLinear (ε : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℂ where
  toFun := axialPhysical ε
  map_add' p q := by
    apply Complex.ext <;> simp [axialPhysical,HexTiling.planeMap] <;> ring
  map_smul' a p := by
    apply Complex.ext <;> simp [axialPhysical,HexTiling.planeMap] <;> ring

noncomputable def AxialSegment.signedCoordinate (s : AxialSegment) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  (if s.horizontal then (LinearMap.snd ℝ ℝ ℝ).toAffineMap
    else (LinearMap.fst ℝ ℝ ℝ).toAffineMap) - AffineMap.const ℝ (ℝ × ℝ) s.level

theorem AxialSegment.signedCoordinate_eq_zero (s : AxialSegment) (p : ℝ × ℝ) :
    s.signedCoordinate p = 0 ↔ s.onLine p := by
  cases hh : s.horizontal <;> simp [signedCoordinate,onLine,level,hh,sub_eq_zero]

theorem AxialSegment.continuous_signedCoordinate (s : AxialSegment) :
    Continuous s.signedCoordinate := by
  cases hh : s.horizontal
  · simp only [signedCoordinate,hh,Bool.false_eq_true,ite_false]
    change Continuous (fun p : ℝ × ℝ => p.1 - s.level)
    fun_prop
  · simp only [signedCoordinate,hh,ite_true]
    change Continuous (fun p : ℝ × ℝ => p.2 - s.level)
    fun_prop

/-- The finite segment separation result now yields an actual carrier
half-plane identity on the full closed probe ball. The contact is taken
in the inner concentric ball so the supporting line crosses its interior. -/
theorem polygon_carrier_eq_halfSpace {E : Type*} (Q : PolygonQuad) (P : Probe)
    (c : ℝ × ℝ)
    (edge : E → AxialSegment) (hsimple : SimpleSegmentFamily edge)
    (hboundary : ∀ p, p ∈ frontier Q.carrier ↔ ∃ i, (edge i).contains p)
    {R δ : ℝ} (hR : 0<R) (hscale : 6*R<P.mesh*δ)
    (hparallel : ∀ i j, (edge i).horizontal=(edge j).horizontal →
      (edge i).level≠(edge j).level → δ≤|(edge i).level-(edge j).level|)
    (hroots : ∀ i,
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (edge i).first) ∧
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (edge i).last))
    (i : E) (hi : (edge i).contact P.mesh c (R/2)) :
    (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
      (p ∈ Q.carrier ↔ 0≤(edge i).signedCoordinate p)) ∨
    (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
      (p ∈ Q.carrier ↔ (edge i).signedCoordinate p≤0)) := by
  let U : Set (ℝ × ℝ) := physicalHomeomorph P ⁻¹'
    Metric.ball (axialPhysical P.mesh c) (2*R)
  have hopen : IsOpen U := Metric.isOpen_ball.preimage (physicalHomeomorph P).continuous
  have hconv : Convex ℝ U :=
    (convex_ball (axialPhysical P.mesh c) (2*R)).linear_preimage (axialPhysicalLinear P.mesh)
  have hclosure : closure U = physicalHomeomorph P ⁻¹'
      Metric.closedBall (axialPhysical P.mesh c) (2*R) := by
    dsimp only [U]
    rw [← (physicalHomeomorph P).preimage_closure,closure_ball _ (by positivity)]
  have hi' : (edge i).contact P.mesh c R := by
    obtain ⟨t,ht,hd⟩ := hi
    exact ⟨t,ht,by linarith⟩
  have hzero : ∃ p ∈ U, (edge i).signedCoordinate p=0 := by
    obtain ⟨t,ht,hd⟩ := hi
    refine ⟨(edge i).point t,?_,((edge i).signedCoordinate_eq_zero _).mpr
      ((edge i).point_onLine t)⟩
    change dist (physicalHomeomorph P ((edge i).point t)) (axialPhysical P.mesh c)<2*R
    change dist (axialPhysical P.mesh c) (physicalHomeomorph P ((edge i).point t))≤2*(R/2) at hd
    rw [dist_comm]
    linarith
  have hline : ∀ p ∈ closure U, p ∈ frontier Q.carrier ↔ (edge i).signedCoordinate p=0 := by
    intro p hp
    rw [hclosure] at hp
    have hd : dist (axialPhysical P.mesh c)
        (axialPhysical P.mesh p)≤2*R := by
      simpa only [mem_preimage,Metric.mem_closedBall,physicalHomeomorph_apply,
        axialPhysical,dist_comm] using hp
    rw [hboundary,(edge i).signedCoordinate_eq_zero]
    exact polygon_boundary_eq_line edge hsimple P.mesh_pos.le hR hscale hparallel
      hroots i hi' p hd
  have hh := local_closed_halfSpace_of_frontier Q.carrier U (edge i).signedCoordinate
    (edge i).continuous_signedCoordinate Q.regularClosed hopen hconv hzero hline
  simpa only [hclosure,mem_preimage,Metric.mem_closedBall,dist_comm] using hh

#print axioms polygon_carrier_eq_halfSpace

end ExceptionalTimes.PairSquareSewing
