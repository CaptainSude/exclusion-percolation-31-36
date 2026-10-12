import ExceptionalTimes.PolygonLocalHalfPlane
import ExceptionalTimes.HalfPlaneArms

/-! A finite polygon presentation records the actual four terminal arcs,
including any marked point splitting an otherwise straight side. The
local source geometry follows from its finite segments and their roots. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

structure AxialPolygonPresentation (Q : PolygonQuad) (E : Type*) where
  edge : E → AxialSegment
  label : E → Bool × Bool
  simple : SimpleSegmentFamily edge
  side_eq : ∀ s p, p ∈ Q.side s ↔ ∃ i, label i=s ∧ (edge i).contains p

theorem PolygonQuad.frontier_iff_side (Q : PolygonQuad) (p : ℝ × ℝ) :
    p ∈ frontier Q.carrier ↔ ∃ s, p ∈ Q.side s := by
  rw [Q.frontier_eq]
  simp [PolygonQuad.side,or_assoc,or_comm]

theorem AxialPolygonPresentation.frontier_iff {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) (p : ℝ × ℝ) :
    p ∈ frontier Q.carrier ↔ ∃ i, (A.edge i).contains p := by
  rw [Q.frontier_iff_side]
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨i,_,hi⟩ := (A.side_eq s p).mp hs
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨A.label i,(A.side_eq _ p).mpr ⟨i,rfl,hi⟩⟩

theorem AxialPolygonPresentation.local_side {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) {ε R δ : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hR : 0<R) (hscale : 6*R<ε*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i, 8*R≤dist (axialPhysical ε c) (axialPhysical ε (A.edge i).first) ∧
      8*R≤dist (axialPhysical ε c) (axialPhysical ε (A.edge i).last))
    (i : E) (hi : (A.edge i).contact ε c R) (p : ℝ × ℝ)
    (hp : dist (axialPhysical ε c) (axialPhysical ε p)≤2*R) :
    p ∈ Q.side (A.label i) ↔ (A.edge i).onLine p := by
  constructor
  · intro hs
    obtain ⟨j,_,t,ht,hp'⟩ := (A.side_eq _ p).mp hs
    have hj : (A.edge j).contact ε c R := ⟨t,ht,by rwa [hp']⟩
    have he := polygon_contact_unique A.edge A.simple hε hR hscale hparallel hroots hi hj
    subst j
    rw [← hp']
    exact (A.edge i).point_onLine t
  · intro hl
    apply (A.side_eq _ p).mpr
    exact ⟨i,rfl,(A.edge i).contains_of_near_line hR hi (hroots i).1 (hroots i).2 hl
      (by linarith)⟩

theorem AxialPolygonPresentation.other_side_distance {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) {ε R δ : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hR : 0<R) (hscale : 6*R<ε*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i, 8*R≤dist (axialPhysical ε c) (axialPhysical ε (A.edge i).first) ∧
      8*R≤dist (axialPhysical ε c) (axialPhysical ε (A.edge i).last))
    (i : E) (hi : (A.edge i).contact ε c R) (s : Bool × Bool) (hs : s≠A.label i)
    (p : ℝ × ℝ) (hp : p ∈ Q.side s) :
    2*R<dist (axialPhysical ε c) (axialPhysical ε p) := by
  by_contra hn
  have hd := le_of_not_gt hn
  obtain ⟨j,hjs,t,ht,hp'⟩ := (A.side_eq s p).mp hp
  have hj : (A.edge j).contact ε c R := ⟨t,ht,by rwa [hp']⟩
  have he := polygon_contact_unique A.edge A.simple hε hR hscale hparallel hroots hi hj
  subst j
  exact hs hjs.symm

theorem AxialSegment.lattice_boundary (s : AxialSegment) (level : ℤ)
    (hlevel : s.level=(level:ℝ)) (positive : Bool) (p : ℝ × ℝ) :
    p ∈ (LatticeHalfPlane.mk s.horizontal positive level).boundary ↔ s.onLine p := by
  cases hh : s.horizontal <;>
    simp only [AxialSegment.level,hh,Bool.false_eq_true,ite_false,ite_true] at hlevel
  all_goals simp [LatticeHalfPlane.boundary,LatticeHalfPlane.coordinate,AxialSegment.onLine,hh,hlevel]

theorem AxialSegment.lattice_carrier (s : AxialSegment) (level : ℤ)
    (hlevel : s.level=(level:ℝ)) (positive : Bool) (p : ℝ × ℝ) :
    p ∈ (LatticeHalfPlane.mk s.horizontal positive level).carrier ↔
      (if positive then 0≤s.signedCoordinate p else s.signedCoordinate p≤0) := by
  cases hh : s.horizontal <;> cases positive <;>
    simp [LatticeHalfPlane.carrier,LatticeHalfPlane.coordinate,
      signedCoordinate,hh,hlevel,sub_nonneg]

/-- All polygon segments, including collinear splits at marked points,
are retained in the source's side identity and other-side exclusion. -/
theorem AxialPolygonPresentation.local_source_geometry {Q : PolygonQuad} {E : Type*}
    (A : AxialPolygonPresentation Q E) (P : Probe) (c : ℝ × ℝ)
    {R δ : ℝ} (hR : 0<R) (hscale : 6*R<P.mesh*δ)
    (hparallel : ∀ i j, (A.edge i).horizontal=(A.edge j).horizontal →
      (A.edge i).level≠(A.edge j).level → δ≤|(A.edge i).level-(A.edge j).level|)
    (hroots : ∀ i,
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (A.edge i).first) ∧
      8*R≤dist (axialPhysical P.mesh c) (axialPhysical P.mesh (A.edge i).last))
    (i : E) (hc : (A.edge i).contains c)
    (level : ℤ) (hlevel : (A.edge i).level=(level:ℝ)) :
    ∃ H : LatticeHalfPlane,
      H.horizontal=(A.edge i).horizontal ∧ H.level=level ∧ c ∈ Q.side (A.label i) ∧
      c ∈ H.boundary ∧
      (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
        (p ∈ Q.carrier ↔ p ∈ H.carrier)) ∧
      (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
        (p ∈ Q.side (A.label i) ↔ p ∈ H.boundary)) ∧
      (∀ s, s≠A.label i → ∀ p ∈ Q.side s,
        2*R<dist (axialPhysical P.mesh c) (physicalHomeomorph P p)) := by
  have hcontact : (A.edge i).contact P.mesh c (R/2) := by
    obtain ⟨u,hu,he⟩ := hc
    exact ⟨u,hu,by rw [he,dist_self]; positivity⟩
  have hcontact' : (A.edge i).contact P.mesh c R := by
    obtain ⟨u,hu,he⟩ := hc
    exact ⟨u,hu,by rw [he,dist_self]; positivity⟩
  have hcside : c ∈ Q.side (A.label i) := (A.side_eq _ c).mpr ⟨i,rfl,hc⟩
  have hcline : (A.edge i).onLine c := by
    obtain ⟨u,hu,rfl⟩ := hc
    exact (A.edge i).point_onLine u
  have hh := polygon_carrier_eq_halfSpace Q P c A.edge A.simple A.frontier_iff
    hR hscale hparallel hroots i hcontact
  have hfinish (positive : Bool)
      (hhalf : ∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
        (p ∈ Q.carrier ↔ if positive then 0≤(A.edge i).signedCoordinate p
          else (A.edge i).signedCoordinate p≤0)) :
      ∃ H : LatticeHalfPlane,
        H.horizontal=(A.edge i).horizontal ∧ H.level=level ∧ c ∈ Q.side (A.label i) ∧
        c ∈ H.boundary ∧
        (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
          (p ∈ Q.carrier ↔ p ∈ H.carrier)) ∧
        (∀ p, dist (axialPhysical P.mesh c) (physicalHomeomorph P p)≤2*R →
          (p ∈ Q.side (A.label i) ↔ p ∈ H.boundary)) ∧
        (∀ s, s≠A.label i → ∀ p ∈ Q.side s,
          2*R<dist (axialPhysical P.mesh c) (physicalHomeomorph P p)) := by
    refine ⟨⟨(A.edge i).horizontal,positive,level⟩,rfl,rfl,hcside,
      ((A.edge i).lattice_boundary level hlevel positive c).mpr hcline,?_,?_,?_⟩
    · intro p hp
      exact (hhalf p hp).trans ((A.edge i).lattice_carrier level hlevel positive p).symm
    · intro p hp
      exact (A.local_side P.mesh_pos.le hR hscale hparallel hroots i hcontact' p hp).trans
        ((A.edge i).lattice_boundary level hlevel positive p).symm
    · exact A.other_side_distance P.mesh_pos.le hR hscale hparallel hroots i hcontact'
  rcases hh with hp | hn
  · exact hfinish true (by simpa only [ite_true] using hp)
  · exact hfinish false (by simpa only [Bool.false_eq_true,ite_false] using hn)

#print axioms AxialPolygonPresentation.local_side
#print axioms AxialPolygonPresentation.other_side_distance
#print axioms AxialPolygonPresentation.local_source_geometry

end ExceptionalTimes.PairSquareSewing
