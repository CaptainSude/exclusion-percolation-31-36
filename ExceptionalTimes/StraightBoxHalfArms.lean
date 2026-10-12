import ExceptionalTimes.HalfPlaneArms

open Set

namespace ExceptionalTimes.PairSquareSewing

def boxSideCoordinate (s : Bool × Bool) (p : ℝ × ℝ) : ℝ :=
  if s.1 then p.2 else p.1

def boxSideSlack (n : ℕ) (p : ℝ × ℝ) (s : Bool × Bool) : ℝ :=
  if s.2 then n-boxSideCoordinate s p else boxSideCoordinate s p+n

def boxHalfPlane (n : ℕ) (s : Bool × Bool) : LatticeHalfPlane where
  horizontal := s.1
  positive := !s.2
  level := if s.2 then (n : ℤ) else -(n : ℤ)

theorem mem_boxHalfPlane_iff (n : ℕ) (s : Bool × Bool) (p : ℝ × ℝ) :
    p ∈ (boxHalfPlane n s).carrier ↔ 0 ≤ boxSideSlack n p s := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp [boxHalfPlane,LatticeHalfPlane.carrier,LatticeHalfPlane.coordinate,
      boxSideSlack,boxSideCoordinate] <;> constructor <;> intro h <;> linarith

theorem mem_boxBoundary_iff (n : ℕ) (s : Bool × Bool) (p : ℝ × ℝ) :
    p ∈ (boxHalfPlane n s).boundary ↔ boxSideSlack n p s=0 := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp [boxHalfPlane,LatticeHalfPlane.boundary,LatticeHalfPlane.coordinate,
      boxSideSlack,boxSideCoordinate] <;> constructor <;> intro h <;> linarith

theorem mem_rectangle_iff_slacks (n : ℕ) (p : ℝ × ℝ) :
    p ∈ axialRectangle n ↔ ∀ s, 0 ≤ boxSideSlack n p s := by
  constructor
  · intro hp s
    obtain ⟨a,b⟩ := s
    change (- (n:ℝ) ≤ p.1 ∧ p.1 ≤ n) ∧ (-(n:ℝ) ≤ p.2 ∧ p.2 ≤ n) at hp
    cases a <;> cases b <;> simp [boxSideSlack,boxSideCoordinate] <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2]
  · intro h
    have h00 := h (false,false)
    have h01 := h (false,true)
    have h10 := h (true,false)
    have h11 := h (true,true)
    simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true] at h00 h01 h10 h11
    change (- (n:ℝ) ≤ p.1 ∧ p.1 ≤ n) ∧ (-(n:ℝ) ≤ p.2 ∧ p.2 ≤ n)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

theorem mem_straightSide_iff (n : ℕ) (hn : 0<n) (s : Bool × Bool) (p : ℝ × ℝ) :
    p ∈ (straightBoxPolygonQuad n hn).side s ↔
      p ∈ axialRectangle n ∧ boxSideSlack n p s=0 := by
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp only [PolygonQuad.side,straightBoxPolygonQuad,Bool.false_eq_true,ite_false,ite_true,
      straightLeft,straightRight,straightTop,straightBottom,axialRectangle,mem_ofPred_eq,
      mem_Icc,boxSideSlack,boxSideCoordinate]
  all_goals constructor
  all_goals
    first
    | rintro ⟨h,ha,hb⟩; refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩ <;> linarith [Nat.cast_nonneg (α:=ℝ) n]
    | rintro ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,he⟩; exact ⟨by linarith,by linarith,by linarith⟩

theorem HalfProbe.coordinate_dist (P : HalfProbe) (p q : ℝ × ℝ) :
    P.mesh*|p.1-q.1| ≤ 2*dist (P.physical p) (P.physical q) ∧
    P.mesh*|p.2-q.2| ≤ 2*dist (P.physical p) (P.physical q) := by
  have hd : dist (P.physical p) (P.physical q) = P.mesh*‖HexTiling.planeMap (p-q)‖ := by
    rw [dist_eq_norm,HalfProbe.physical,HalfProbe.physical,← mul_sub,← HexTiling.planeMap_sub,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.mesh_pos]
  obtain ⟨hx,hy⟩ := planeMap_coordinate_le_norm (p-q)
  rw [hd]
  constructor
  · simpa only [Prod.fst_sub,mul_left_comm] using mul_le_mul_of_nonneg_left hx P.mesh_pos.le
  · simpa only [Prod.snd_sub,mul_left_comm] using mul_le_mul_of_nonneg_left hy P.mesh_pos.le

theorem HalfProbe.slack_dist (P : HalfProbe) (n : ℕ) (s : Bool × Bool) (p q : ℝ × ℝ) :
    P.mesh*|boxSideSlack n p s-boxSideSlack n q s| ≤
      2*dist (P.physical p) (P.physical q) := by
  have h := P.coordinate_dist p q
  obtain ⟨a,b⟩ := s
  cases a <;> cases b <;>
    simp only [boxSideSlack,boxSideCoordinate,Bool.false_eq_true,ite_false,ite_true]
  · simpa only [add_sub_add_right_eq_sub] using h.1
  · have he : (n:ℝ)-p.1-(n-q.1) = -(p.1-q.1) := by ring
    simpa only [he,abs_neg] using h.1
  · simpa only [add_sub_add_right_eq_sub] using h.2
  · have he : (n:ℝ)-p.2-(n-q.2) = -(p.2-q.2) := by ring
    simpa only [he,abs_neg] using h.2

/-- Numerical clearance is measured to all three other supporting lines. -/
def HalfProbe.OtherMargins (P : HalfProbe) (n : ℕ) (s : Bool × Bool) : Prop :=
  ∀ t, t ≠ s → 4*P.outerRadius < P.mesh*boxSideSlack n P.center t

theorem HalfProbe.other_slack_pos (P : HalfProbe) (n : ℕ) (s : Bool × Bool)
    (hm : P.OtherMargins n s) {p : ℝ × ℝ}
    (hp : dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius)
    {t : Bool × Bool} (ht : t ≠ s) : 0 < boxSideSlack n p t := by
  have h := P.slack_dist n t p P.center
  have hlow := mul_le_mul_of_nonneg_left (neg_le_abs (boxSideSlack n p t-boxSideSlack n P.center t)) P.mesh_pos.le
  have hmargin := hm t ht
  have hpos : 0 < P.mesh*boxSideSlack n p t := by nlinarith
  exact (mul_pos_iff_of_pos_left P.mesh_pos).mp hpos

theorem HalfProbe.rectangle_halfPlane (P : HalfProbe) (n : ℕ) (s : Bool × Bool)
    (heq : P.halfPlane=boxHalfPlane n s) (hm : P.OtherMargins n s)
    {p : ℝ × ℝ} (hp : dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius) :
    p ∈ axialRectangle n ↔ p ∈ P.halfPlane.carrier := by
  rw [heq,mem_boxHalfPlane_iff,mem_rectangle_iff_slacks]
  constructor
  · exact fun h => h s
  · intro h t
    by_cases ht : t=s
    · simpa only [ht] using h
    · exact (P.other_slack_pos n s hm hp ht).le

theorem HalfProbe.rectangle_side (P : HalfProbe) (n : ℕ) (hn : 0<n) (s : Bool × Bool)
    (heq : P.halfPlane=boxHalfPlane n s) (hm : P.OtherMargins n s)
    {p : ℝ × ℝ} (hp : dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius) :
    p ∈ (straightBoxPolygonQuad n hn).side s ↔ p ∈ P.halfPlane.boundary := by
  rw [mem_straightSide_iff,heq,mem_boxBoundary_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(mem_rectangle_iff_slacks n p).mpr ?_,h⟩
    intro t
    by_cases ht : t=s
    · simp only [ht,h,le_refl]
    · exact (P.other_slack_pos n s hm hp ht).le

theorem HalfProbe.rectangle_other_sides (P : HalfProbe) (n : ℕ) (hn : 0<n)
    (s : Bool × Bool) (hm : P.OtherMargins n s) {t : Bool × Bool} (ht : t ≠ s)
    {p : ℝ × ℝ} (hp : p ∈ (straightBoxPolygonQuad n hn).side t) :
    2*P.outerRadius < dist (P.physical p) (P.physical P.center) := by
  by_contra h
  have hh := P.other_slack_pos n s hm (le_of_not_gt h) ht
  exact (ne_of_gt hh) ((mem_straightSide_iff n hn t p).mp hp).2

/-- Actual board necessity from the published local statement and only
explicit numerical margins. All polygon/half-plane dictionary obligations
are discharged for the straight rectangle. -/
theorem straightBox_localChangeHalfArms
    (hsource : PublishedPolygonHalfArms) (n : ℕ) (hn : 0<n) (P : HalfProbe)
    (s : Bool × Bool) (he : 16*P.mesh < P.innerRadius)
    (heq : P.halfPlane=boxHalfPlane n s) (hm : P.OtherMargins n s) :
    LocalChangeHalfArms (axialBoxQuad n) P := by
  have hR : 0 ≤ 2*P.outerRadius := by linarith [P.inner_pos,P.radii]
  apply straightBox_localChangeHalfArms_of_published hsource n hn P s he
  · exact (P.rectangle_side n hn s heq hm (by simpa using hR)).mpr P.center_on_line
  · exact fun _ hp => P.rectangle_halfPlane n s heq hm hp
  · exact fun _ hp => P.rectangle_side n hn s heq hm hp
  · exact fun t ht _ hp => P.rectangle_other_sides n hn s hm ht hp

#print axioms straightBox_localChangeHalfArms

end ExceptionalTimes.PairSquareSewing


