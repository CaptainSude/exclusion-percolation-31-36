import ExceptionalTimes.StraightBoxHalfArms

/-! The two actual pieces of a near-boundary probe. Their site buffers
are disjoint and lie inside the original probe buffer. The changed pocket
is contained in the larger half-plane pocket. No independence or arm
probability estimate is assumed in these geometric statements. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

noncomputable def Probe.distanceTo (P : Probe) (q : ℝ × ℝ) : ℝ :=
  dist (position P.mesh P.center) ((P.mesh : ℂ)*HexTiling.planeMap q)

def BulkPartActive (P : Probe) (q : ℝ × ℝ) : Prop :=
  4*P.innerRadius < min P.outerRadius (P.distanceTo q/8)

def HalfPartActive (P : Probe) (q : ℝ × ℝ) : Prop :=
  4*(8*max P.innerRadius (P.distanceTo q)) < P.outerRadius/8

noncomputable def Probe.bulkPart (P : Probe) (q : ℝ × ℝ) (h : BulkPartActive P q) : Probe where
  mesh := P.mesh
  center := P.center
  innerRadius := P.innerRadius
  outerRadius := min P.outerRadius (P.distanceTo q/8)
  mesh_pos := P.mesh_pos
  inner_pos := P.inner_pos
  radii := h

noncomputable def Probe.halfPart (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (h : HalfPartActive P q) : HalfProbe where
  mesh := P.mesh
  halfPlane := H
  center := q
  center_on_line := hq
  innerRadius := 8*max P.innerRadius (P.distanceTo q)
  outerRadius := P.outerRadius/8
  mesh_pos := P.mesh_pos
  inner_pos := by have := le_max_left P.innerRadius (P.distanceTo q); linarith [P.inner_pos]
  radii := h

theorem Probe.bulkPart_region (P : Probe) (q : ℝ × ℝ) (h : BulkPartActive P q) :
    (P.bulkPart q h).region ⊆ P.region := by
  intro v hv
  change P.innerRadius/2 ≤ P.radius v ∧ P.radius v ≤ 2*min P.outerRadius (P.distanceTo q/8) at hv
  exact ⟨hv.1,hv.2.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))⟩

theorem Probe.halfPart_region (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (h : HalfPartActive P q) :
    (P.halfPart H q hq h).region ⊆ P.region := by
  intro v hv
  have hM := le_max_left P.innerRadius (P.distanceTo q)
  have hd := le_max_right P.innerRadius (P.distanceTo q)
  have h1 := dist_triangle (position P.mesh v) (position P.mesh P.center)
    ((P.mesh:ℂ)*HexTiling.planeMap q)
  have h2 := dist_triangle (position P.mesh v) ((P.mesh:ℂ)*HexTiling.planeMap q)
    (position P.mesh P.center)
  rw [dist_comm ((P.mesh:ℂ)*HexTiling.planeMap q) (position P.mesh P.center)] at h2
  have hv2 := hv.2
  change 8*max P.innerRadius (P.distanceTo q)/2 ≤
      dist (position P.mesh v) ((P.mesh:ℂ)*HexTiling.planeMap q) ∧
    dist (position P.mesh v) ((P.mesh:ℂ)*HexTiling.planeMap q) ≤ 2*(P.outerRadius/8) at hv2
  change 4*(8*max P.innerRadius (P.distanceTo q)) < P.outerRadius/8 at h
  change P.innerRadius/2 ≤ P.radius v ∧ P.radius v ≤ 2*P.outerRadius
  dsimp only [Probe.radius,Probe.distanceTo] at *
  constructor <;> linarith [hv2.1,hv2.2,P.inner_pos]

theorem Probe.halfPart_pocket (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (h : HalfPartActive P q) :
    P.pocket ⊆ (P.halfPart H q hq h).pocket := by
  intro v hv
  have hM := le_max_left P.innerRadius (P.distanceTo q)
  have hd := le_max_right P.innerRadius (P.distanceTo q)
  have ht := dist_triangle (position P.mesh v) (position P.mesh P.center)
    ((P.mesh:ℂ)*HexTiling.planeMap q)
  change dist (position P.mesh v) ((P.mesh:ℂ)*HexTiling.planeMap q) <
    8*max P.innerRadius (P.distanceTo q)/2
  change P.radius v < P.innerRadius/2 at hv
  dsimp only [Probe.radius,Probe.distanceTo] at *
  linarith [P.inner_pos]

theorem Probe.bulk_half_disjoint (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (hb : BulkPartActive P q) (hh : HalfPartActive P q) :
    Disjoint (P.bulkPart q hb).region (P.halfPart H q hq hh).region := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have hM := le_max_left P.innerRadius (P.distanceTo q)
  have hd := le_max_right P.innerRadius (P.distanceTo q)
  have hbnd := min_le_right P.outerRadius (P.distanceTo q/8)
  have ht := dist_triangle (position P.mesh v) (position P.mesh P.center)
    ((P.mesh:ℂ)*HexTiling.planeMap q)
  change P.innerRadius/2 ≤ P.radius v ∧ P.radius v ≤ 2*min P.outerRadius (P.distanceTo q/8) at hv
  have hwlo : 8*max P.innerRadius (P.distanceTo q)/2 ≤
      dist (position P.mesh v) ((P.mesh:ℂ)*HexTiling.planeMap q) := hw.2.1
  dsimp only [Probe.radius,Probe.distanceTo] at *
  linarith [hv.2,P.inner_pos]

def MixedBoundaryArms (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (ω : Configuration) : Prop :=
  (∀ hb : BulkPartActive P q, FourArms (P.bulkPart q hb) ω) ∧
  (∀ hh : HalfPartActive P q, HalfThreeArms (P.halfPart H q hq hh) ω)

/-- Only local published necessity for each active piece is used. The
original comparison may contain arbitrarily many other changes held fixed. -/
theorem mixedBoundaryArms_of_localChange (Q : GraphQuad) (P : Probe)
    (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary)
    (hbulk : ∀ hb, LocalChangeArms Q (P.bulkPart q hb))
    (hhalf : ∀ hh, LocalChangeHalfArms Q (P.halfPart H q hq hh))
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region) (hc : Q.test a ≠ Q.test b) :
    MixedBoundaryArms P H q hq ω := by
  constructor
  · intro h
    exact hbulk h ω a b hab (ha.mono (P.bulkPart_region q h))
      (hb.mono (P.bulkPart_region q h)) hc
  · intro h
    apply hhalf h ω a b
    · intro v hv
      exact hab v (fun hp => hv (P.halfPart_pocket H q hq h hp))
    · exact ha.mono (P.halfPart_region H q hq h)
    · exact hb.mono (P.halfPart_region H q hq h)
    · exact hc

/-- If both pieces are empty, only a bounded annular ratio remains.
This is the deterministic reason empty probes have bounded cost. -/
theorem no_active_piece_bounded_ratio (P : Probe) (q : ℝ × ℝ)
    (hb : ¬ BulkPartActive P q) (hh : ¬ HalfPartActive P q) :
    P.outerRadius ≤ 8192*P.innerRadius := by
  have hR := P.radii
  have hd : P.distanceTo q ≤ 32*P.innerRadius := by
    have hm : min P.outerRadius (P.distanceTo q/8) ≤ 4*P.innerRadius := le_of_not_gt hb
    rcases le_or_gt P.outerRadius (P.distanceTo q/8) with h | h
    · rw [min_eq_left h] at hm
      linarith
    · rw [min_eq_right h.le] at hm
      linarith
  have hmax : max P.innerRadius (P.distanceTo q) ≤ 32*P.innerRadius :=
    max_le (by linarith [P.inner_pos]) hd
  have hh' : P.outerRadius/8 ≤ 4*(8*max P.innerRadius (P.distanceTo q)) := le_of_not_gt hh
  linarith

#print axioms Probe.bulk_half_disjoint
#print axioms mixedBoundaryArms_of_localChange
#print axioms no_active_piece_bounded_ratio

end ExceptionalTimes.PairSquareSewing

