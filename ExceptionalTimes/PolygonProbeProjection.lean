import ExceptionalTimes.PolygonBoundarySide
import ExceptionalTimes.StraightBoxProbeGeometry

/-! The boundary probe center is the literal coordinate projection onto
the contacted polygon segment. Clearance proves that it lies on the finite
segment, and that every actual polygon vertex remains far from it. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

noncomputable def AxialSegment.projection (s : AxialSegment) (c : ℝ × ℝ) : ℝ × ℝ :=
  if s.horizontal then (c.1,s.level) else (s.level,c.2)

theorem AxialSegment.projection_onLine (s : AxialSegment) (c : ℝ × ℝ) :
    s.onLine (s.projection c) := by
  cases hh : s.horizontal <;> simp [projection,onLine,level,hh]

theorem AxialSegment.projection_distance (s : AxialSegment) (c : ℝ × ℝ)
    {ε : ℝ} (hε : 0≤ε) :
    dist (axialPhysical ε c) (axialPhysical ε (s.projection c)) =
      ε*|s.signedCoordinate c| := by
  rw [axialPhysical_dist hε]
  obtain ⟨x,y⟩ := c
  cases hh : s.horizontal <;>
    simp [projection,signedCoordinate,hh,Prod.mk_sub_mk,
      planeMap_norm_vertical,planeMap_norm_horizontal]

theorem AxialSegment.projection_distance_le {s : AxialSegment} {c : ℝ × ℝ}
    {ε R : ℝ} (hε : 0≤ε) (hc : s.contact ε c R) :
    dist (axialPhysical ε c) (axialPhysical ε (s.projection c))≤3*R := by
  rw [s.projection_distance c hε]
  have hb := s.contact_coordinate hε hc
  cases hh : s.horizontal <;>
    simpa [signedCoordinate,hh] using hb

theorem AxialSegment.projection_mem_segment {s : AxialSegment} {c : ℝ × ℝ}
    {ε R : ℝ} (hε : 0≤ε) (hR : 0<R) (hc : s.contact ε c R)
    (hfirst : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.first))
    (hlast : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.last)) :
    s.contains (s.projection c) := by
  exact s.contains_of_near_line hR hc hfirst hlast (s.projection_onLine c)
    (by linarith [s.projection_distance_le hε hc])

theorem polygon_projection_root_clearance {E : Type*} (edge : E → AxialSegment)
    {ε R : ℝ} {c : ℝ × ℝ} (hε : 0≤ε) (hR : 0<R)
    (hroots : ∀ i, 8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).first) ∧
      8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).last))
    (i : E) (hi : (edge i).contact ε c R) :
    ∀ j, 8*(R/8)≤dist (axialPhysical ε ((edge i).projection c)) (axialPhysical ε (edge j).first) ∧
      8*(R/8)≤dist (axialPhysical ε ((edge i).projection c)) (axialPhysical ε (edge j).last) := by
  have hd := (edge i).projection_distance_le hε hi
  intro j
  have hf := dist_triangle (axialPhysical ε c) (axialPhysical ε ((edge i).projection c))
    (axialPhysical ε (edge j).first)
  have hl := dist_triangle (axialPhysical ε c) (axialPhysical ε ((edge i).projection c))
    (axialPhysical ε (edge j).last)
  constructor <;> linarith [(hroots j).1,(hroots j).2]

/-- Distance to the supporting line controls every potential boundary
point of an active inner bulk piece. -/
theorem AxialSegment.projection_distance_le_point (s : AxialSegment)
    {ε : ℝ} (hε : 0≤ε) (c p : ℝ × ℝ) (hp : s.onLine p) :
    dist (axialPhysical ε c) (axialPhysical ε (s.projection c))≤
      (3/2:ℝ)*dist (axialPhysical ε c) (axialPhysical ε p) := by
  rw [s.projection_distance c hε]
  have hh := physical_coordinate_le hε c p
  cases hd : s.horizontal
  · simp only [onLine,hd,Bool.false_eq_true,ite_false] at hp
    simpa [signedCoordinate,level,hd,hp] using hh.1
  · simp only [onLine,hd,ite_true] at hp
    simpa [signedCoordinate,level,hd,hp] using hh.2

#print axioms AxialSegment.projection_mem_segment
#print axioms polygon_projection_root_clearance

end ExceptionalTimes.PairSquareSewing
