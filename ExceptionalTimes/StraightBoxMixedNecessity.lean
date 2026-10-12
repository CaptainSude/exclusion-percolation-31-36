import ExceptionalTimes.StraightBoxProbeGeometry

open Set

namespace ExceptionalTimes.PairSquareSewing

theorem pocket_slack_lower (P : Probe) (n : ℕ) (t : Bool × Bool)
    (hv : ∃ v ∈ latticeBox n, v ∈ P.pocket) :
    -P.innerRadius < P.mesh*boxSideSlack n (HexCells.center P.center) t := by
  obtain ⟨v,hv,hvp⟩ := hv
  have hin := (mem_rectangle_iff_slacks n (HexCells.center v)).mp (center_mem_axialRectangle hv) t
  have hd := boxSideSlack_dist P.mesh_pos.le n t (HexCells.center P.center) (HexCells.center v)
  have hlow := mul_le_mul_of_nonneg_left
    (neg_le_abs (boxSideSlack n (HexCells.center P.center) t-boxSideSlack n (HexCells.center v) t)) P.mesh_pos.le
  have hinside := mul_nonneg P.mesh_pos.le hin
  have hpocket : dist (axialPhysical P.mesh (HexCells.center P.center))
      (axialPhysical P.mesh (HexCells.center v)) < P.innerRadius/2 := by
    change dist (position P.mesh P.center) (position P.mesh v) < P.innerRadius/2
    rw [dist_comm]
    exact hvp
  linarith

theorem probe_projection_distance (P : Probe) (n : ℕ) (s : Bool × Bool) :
    P.distanceTo (boxSideProjection n s (HexCells.center P.center)) =
      P.mesh*|boxSideSlack n (HexCells.center P.center) s| :=
  boxSideProjection_distance n s (HexCells.center P.center) P.mesh_pos.le

theorem contacted_projection_distance (P : Probe) (n : ℕ) (s : Bool × Bool)
    (hs : SideContact P.mesh n P.outerRadius (HexCells.center P.center) s) :
    P.distanceTo (boxSideProjection n s (HexCells.center P.center)) ≤ 3*P.outerRadius := by
  rw [probe_projection_distance]
  obtain ⟨a,b⟩ := s
  cases a <;> cases b
  all_goals dsimp [SideContact,signedSide] at hs
  all_goals first
    | have ht := nearVertical_coordinate P.mesh_pos.le hs
      simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true]
      first
      | simp only [sub_neg_eq_add] at ht; linarith
      | rw [abs_sub_comm]; linarith
    | have ht := nearHorizontal_coordinate P.mesh_pos.le hs
      simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true]
      first
      | simp only [sub_neg_eq_add] at ht; linarith
      | rw [abs_sub_comm]; linarith

theorem halfPart_otherMargins (P : Probe) (n : ℕ) (s : Bool × Bool)
    (hv : ∃ v ∈ latticeBox n, v ∈ P.pocket)
    (hother : ∀ t, t≠s → ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) t)
    (hh : HalfPartActive P (boxSideProjection n s (HexCells.center P.center))) :
    (P.halfPart (boxHalfPlane n s) (boxSideProjection n s (HexCells.center P.center))
      (boxSideProjection_boundary n s (HexCells.center P.center)) hh).OtherMargins n s := by
  intro t ht
  let q := boxSideProjection n s (HexCells.center P.center)
  have h := inward_slack_of_pocket P n t hv (hother t ht)
  have hd := boxSideSlack_dist P.mesh_pos.le n t q (HexCells.center P.center)
  have hlo := mul_le_mul_of_nonneg_left
    (neg_le_abs (boxSideSlack n q t-boxSideSlack n (HexCells.center P.center) t)) P.mesh_pos.le
  have hdist : dist (axialPhysical P.mesh q) (axialPhysical P.mesh (HexCells.center P.center)) =
      P.distanceTo q := dist_comm _ _
  rw [hdist] at hd
  have hm := le_max_right P.innerRadius (P.distanceTo q)
  have hh' : 4*(8*max P.innerRadius (P.distanceTo q))<P.outerRadius/8 := hh
  change 4*(P.outerRadius/8)<P.mesh*boxSideSlack n q t
  linarith [P.inner_pos,P.radii]

theorem interior_rectangle_of_slacks (n : ℕ) (p : ℝ × ℝ)
    (h : ∀ s, 0<boxSideSlack n p s) : p ∈ interior (axialRectangle n) := by
  have h00 := h (false,false)
  have h01 := h (false,true)
  have h10 := h (true,false)
  have h11 := h (true,true)
  simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true] at h00 h01 h10 h11
  change p ∈ interior ((Icc (-(n:ℝ)) n) ×ˢ (Icc (-(n:ℝ)) n))
  rw [interior_prod_eq,interior_Icc]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem bulkPart_inside (P : Probe) (n : ℕ) (s : Bool × Bool)
    (hv : ∃ v ∈ latticeBox n, v ∈ P.pocket)
    (hs : SideContact P.mesh n P.outerRadius (HexCells.center P.center) s)
    (hother : ∀ t, t≠s → ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) t)
    (hb : BulkPartActive P (boxSideProjection n s (HexCells.center P.center))) :
    Metric.closedBall (position P.mesh P.center)
      (2*(P.bulkPart (boxSideProjection n s (HexCells.center P.center)) hb).outerRadius) ⊆
      physicalHomeomorph (P.bulkPart (boxSideProjection n s (HexCells.center P.center)) hb) ''
        interior (axialRectangle n) := by
  let q := boxSideProjection n s (HexCells.center P.center)
  let B := P.bulkPart q hb
  have hbd : B.outerRadius≤P.distanceTo q/8 := min_le_right _ _
  have hb' : 4*P.innerRadius<B.outerRadius := hb
  have hd := contacted_projection_distance P n s hs
  have hselected : P.mesh*boxSideSlack n (HexCells.center P.center) s=P.distanceTo q := by
    rw [probe_projection_distance]
    have hlo := pocket_slack_lower P n s hv
    by_cases hp : 0≤boxSideSlack n (HexCells.center P.center) s
    · rw [abs_of_nonneg hp]
    · have he := probe_projection_distance P n s
      rw [abs_of_neg (lt_of_not_ge hp)] at he
      change P.distanceTo q = _ at he
      exfalso
      linarith [P.inner_pos]
  have hclear (t : Bool × Bool) : 4*B.outerRadius<P.mesh*boxSideSlack n (HexCells.center P.center) t := by
    by_cases ht : t=s
    · rw [ht,hselected]
      linarith [P.inner_pos]
    · have hh := inward_slack_of_pocket P n t hv (hother t ht)
      change P.distanceTo q≤3*P.outerRadius at hd
      linarith [P.inner_pos,P.radii]
  intro z hz
  let p := (physicalHomeomorph B).symm z
  have hpz : physicalHomeomorph B p=z := (physicalHomeomorph B).apply_symm_apply z
  refine ⟨p,interior_rectangle_of_slacks n p ?_,hpz⟩
  intro t
  have hdif := boxSideSlack_dist P.mesh_pos.le n t p (HexCells.center P.center)
  have hlo := mul_le_mul_of_nonneg_left
    (neg_le_abs (boxSideSlack n p t-boxSideSlack n (HexCells.center P.center) t)) P.mesh_pos.le
  have hpz' : axialPhysical P.mesh p=z := hpz
  rw [hpz'] at hdif
  have hz' : dist z (axialPhysical P.mesh (HexCells.center P.center))≤2*B.outerRadius := hz
  have hpos : 0<P.mesh*boxSideSlack n p t := by linarith [hclear t]
  exact (mul_pos_iff_of_pos_left P.mesh_pos).mp hpos

/-- Literal mixed-arm necessity from one contacted side and exclusion of
the other three. The inside-board pocket witness is derived from the
changed graph crossing, so there is no extra location hypothesis. -/
theorem mixedBoundaryArms_of_unique_side
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (n : ℕ) (hn : 0<n) (P : Probe) (s : Bool × Bool) (he : 16*P.mesh<P.innerRadius)
    (hs : SideContact P.mesh n P.outerRadius (HexCells.center P.center) s)
    (hother : ∀ t, t≠s → ¬SideContact P.mesh n P.outerRadius (HexCells.center P.center) t)
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hc : (axialBoxQuad n).test a ≠ (axialBoxQuad n).test b) :
    MixedBoundaryArms P (boxHalfPlane n s) (boxSideProjection n s (HexCells.center P.center))
      (boxSideProjection_boundary n s (HexCells.center P.center)) ω := by
  have hv : ∃ v ∈ latticeBox n, v ∈ P.pocket := (axialBoxQuad n).changed_pocket P hab hc
  apply mixedBoundaryArms_of_localChange (axialBoxQuad n) P (boxHalfPlane n s)
    (boxSideProjection n s (HexCells.center P.center)) (boxSideProjection_boundary n s (HexCells.center P.center))
    _ _ ω a b hab ha hb hc
  · intro ht
    exact straightBox_localChangeArms_of_published hbulkSource n hn _ he (bulkPart_inside P n s hv hs hother ht)
  · intro ht
    apply straightBox_localChangeHalfArms hhalfSource n hn _ s _ rfl (halfPart_otherMargins P n s hv hother ht)
    change 16*P.mesh<8*max P.innerRadius (P.distanceTo (boxSideProjection n s (HexCells.center P.center)))
    have hm := le_max_left P.innerRadius (P.distanceTo (boxSideProjection n s (HexCells.center P.center)))
    linarith [P.inner_pos]

/-- The one-side exclusion is supplied by the actual Kruskal life and
its four fixed corner roots, not by an extra geometric hypothesis. -/
theorem life_mixedBoundaryArms_of_contact {V : Type*} [Fintype V]
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (fixed : V → Prop) (anchor : V → ℂ) {cutoff stop : ℝ}
    (hcut : 0<cutoff) (n : ℕ) (hn : 0<n) (P : Probe)
    (hscale : 3*(stop/8)<P.mesh*n)
    (corner : Bool → Bool → V) (hfixed : ∀ s t, fixed (corner s t))
    (hcorner : ∀ s t, anchor (corner s t)=
      axialPhysical P.mesh (signedSide n s,signedSide n t))
    (life : ForestArmProbability.Life fixed anchor cutoff stop)
    (hcenter : anchor (ForestArmProbability.center fixed anchor cutoff stop life)=position P.mesh P.center)
    (houter : P.outerRadius=KruskalLives.death fixed anchor cutoff stop life.val/8)
    (s : Bool × Bool) (he : 16*P.mesh<P.innerRadius)
    (hs : SideContact P.mesh n P.outerRadius (HexCells.center P.center) s)
    (ω a b : Configuration) (hab : ∀ v, v ∉ P.pocket → a v=b v)
    (ha : EqOn a ω P.region) (hb : EqOn b ω P.region)
    (hc : (axialBoxQuad n).test a ≠ (axialBoxQuad n).test b) :
    MixedBoundaryArms P (boxHalfPlane n s) (boxSideProjection n s (HexCells.center P.center))
      (boxSideProjection_boundary n s (HexCells.center P.center)) ω := by
  apply mixedBoundaryArms_of_unique_side hbulkSource hhalfSource n hn P s he hs _ ω a b hab ha hb hc
  intro t hts ht
  apply hts
  rw [houter] at hs ht
  exact life_sideContact_unique fixed anchor hcut P.mesh_pos.le hscale corner hfixed hcorner
    life (HexCells.center P.center) hcenter ht hs

#print axioms mixedBoundaryArms_of_unique_side
#print axioms life_mixedBoundaryArms_of_contact

end ExceptionalTimes.PairSquareSewing
