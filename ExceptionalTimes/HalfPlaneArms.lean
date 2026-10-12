import ExceptionalTimes.StraightBoxPolygon

/-! Literal standard-orientation half-plane arm events.  The supporting
line passes through a lattice row.  Closed cells touching that half-plane
have their centers in it; this is proved using the strict 2/3-cell bound.
Published assumptions below are local event and single-annulus statements,
with their microscopic cutoff displayed. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

structure LatticeHalfPlane where
  horizontal : Bool
  positive : Bool
  level : ℤ

def LatticeHalfPlane.coordinate (H : LatticeHalfPlane) (p : ℝ × ℝ) : ℝ :=
  if H.horizontal then p.2 else p.1

def LatticeHalfPlane.carrier (H : LatticeHalfPlane) : Set (ℝ × ℝ) :=
  {p | if H.positive then (H.level : ℝ) ≤ H.coordinate p
    else H.coordinate p ≤ (H.level : ℝ)}

def LatticeHalfPlane.boundary (H : LatticeHalfPlane) : Set (ℝ × ℝ) :=
  {p | H.coordinate p = H.level}

theorem LatticeHalfPlane.cell_center {H : LatticeHalfPlane} {p : ℝ × ℝ} {v : Site}
    (hp : p ∈ H.carrier) (hc : p ∈ HexCells.cell v) : HexCells.center v ∈ H.carrier := by
  obtain ⟨hx,hy⟩ := HexCells.coordinate_bounds hc
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hylo := (abs_le.mp hy).1
  have hyhi := (abs_le.mp hy).2
  obtain ⟨axis,positive,level⟩ := H
  cases axis <;> cases positive <;>
    simp only [LatticeHalfPlane.carrier,LatticeHalfPlane.coordinate,mem_ofPred_eq,
      Bool.false_eq_true,ite_false,ite_true,HexCells.center] at hp ⊢
  all_goals
    first
    | have h : (v.1 : ℝ) < level+1 := by linarith
      have hi : v.1 < level+1 := by exact_mod_cast h
      exact_mod_cast (show v.1 ≤ level by omega)
    | have h : (level : ℝ) < v.1+1 := by linarith
      have hi : level < v.1+1 := by exact_mod_cast h
      exact_mod_cast (show level ≤ v.1 by omega)
    | have h : (v.2 : ℝ) < level+1 := by linarith
      have hi : v.2 < level+1 := by exact_mod_cast h
      exact_mod_cast (show v.2 ≤ level by omega)
    | have h : (level : ℝ) < v.2+1 := by linarith
      have hi : level < v.2+1 := by exact_mod_cast h
      exact_mod_cast (show level ≤ v.2 by omega)

structure HalfProbe where
  mesh : ℝ
  halfPlane : LatticeHalfPlane
  center : ℝ × ℝ
  center_on_line : center ∈ halfPlane.boundary
  innerRadius : ℝ
  outerRadius : ℝ
  mesh_pos : 0 < mesh
  inner_pos : 0 < innerRadius
  radii : 4*innerRadius < outerRadius

noncomputable def HalfProbe.physical (P : HalfProbe) (p : ℝ × ℝ) : ℂ :=
  (P.mesh : ℂ)*HexTiling.planeMap p

noncomputable def HalfProbe.radius (P : HalfProbe) (v : Site) : ℝ :=
  dist (position P.mesh v) (P.physical P.center)

def HalfProbe.region (P : HalfProbe) : Set Site :=
  {v | HexCells.center v ∈ P.halfPlane.carrier ∧
    P.innerRadius/2 ≤ P.radius v ∧ P.radius v ≤ 2*P.outerRadius}

def HalfProbe.pocket (P : HalfProbe) : Set Site := {v | P.radius v < P.innerRadius/2}

def HalfProbe.agreementShell (P : HalfProbe) : Set ℂ :=
  P.physical '' {p | p ∈ P.halfPlane.carrier ∧
    3*P.innerRadius/4 ≤ dist (P.physical p) (P.physical P.center) ∧
    dist (P.physical p) (P.physical P.center) ≤ 3*P.outerRadius/2}

def HalfProbe.OuterContact (P : HalfProbe) {u v : Site}
    (path : triangularGraph.Walk u v) (q : ℂ) : Prop :=
  ∃ w : Site, ∃ initial : triangularGraph.Walk u w, ∃ last : TriangularAdj w v,
    path = initial.concat last ∧
      (∀ z ∈ initial.support, P.radius z < P.outerRadius) ∧
      q ∈ edgeTrace P.mesh w v ∧ dist q (P.physical P.center) = P.outerRadius

def HalfProbe.OrderedOuter (P : HalfProbe) (q : Fin 3 → ℂ) : Prop :=
  (∀ i, dist (q i) (P.physical P.center) = P.outerRadius) ∧
  ∃ turns : Fin 3 → ℤ,
    let θ := fun i => Complex.arg (q i-P.physical P.center)+2*Real.pi*(turns i : ℝ)
    StrictMono θ ∧ θ 2 ≤ θ 0+Real.pi

/-- Both color orders are included. All three paths are site-disjoint,
including the two equal-colored outside arms. -/
def HalfThreeArms (P : HalfProbe) (ω : Configuration) : Prop :=
  ∃ firstBlack : Bool, ∃ start finish : Fin 3 → Site,
    ∃ path : ∀ i, triangularGraph.Walk (start i) (finish i),
      (∀ i, (path i).IsPath) ∧
      (∀ i, P.radius (start i) ≤ P.innerRadius) ∧
      (∀ i, P.outerRadius ≤ P.radius (finish i)) ∧
      (∀ i z, z ∈ (path i).support → z ∈ P.region ∧
        ω z = if i.val % 2 = 0 then firstBlack else !firstBlack) ∧
      (∀ i j, i ≠ j → List.Disjoint (path i).support (path j).support) ∧
      ∃ contact : Fin 3 → ℂ,
        (∀ i, P.OuterContact (path i) (contact i)) ∧ P.OrderedOuter contact

theorem HalfThreeArms.mono_eqOn {P : HalfProbe} {ω η : Configuration}
    (h : HalfThreeArms P ω) (heq : EqOn ω η P.region) : HalfThreeArms P η := by
  obtain ⟨b,s,t,p,hp,hs,ht,hcol,hdis,contacts⟩ := h
  refine ⟨b,s,t,p,hp,hs,ht,?_,hdis,contacts⟩
  intro i z hz
  have hh := hcol i z hz
  exact ⟨hh.1,(heq hh.1).symm.trans hh.2⟩

theorem halfThreeArms_eqOn {P : HalfProbe} {ω η : Configuration}
    (heq : EqOn ω η P.region) : HalfThreeArms P ω ↔ HalfThreeArms P η :=
  ⟨fun h => h.mono_eqOn heq,fun h => h.mono_eqOn heq.symm⟩

theorem HalfProbe.physical_injective (P : HalfProbe) : Function.Injective P.physical := by
  intro p q h
  apply axialPlaneHomeomorph.injective
  exact mul_left_cancel₀ (by exact_mod_cast ne_of_gt P.mesh_pos : (P.mesh : ℂ) ≠ 0) h

theorem HalfProbe.cell_meets_shell (P : HalfProbe) (he : 16*P.mesh < P.innerRadius)
    {v : Site} (hv : (HexTiling.physicalCell P.mesh v ∩ P.agreementShell).Nonempty) :
    v ∈ P.region := by
  obtain ⟨z,hcell,p,⟨hp,hlo,hhi⟩,rfl⟩ := hv
  obtain ⟨q,hq,hqp⟩ := hcell
  have hqp' : q=p := P.physical_injective hqp
  subst q
  have hdist := HexTiling.physicalCell_radius (show P.physical p ∈ HexTiling.physicalCell P.mesh v from ⟨p,hq,rfl⟩)
  rw [abs_of_pos P.mesh_pos] at hdist
  change dist (P.physical p) (position P.mesh v) ≤ 2*P.mesh at hdist
  have h1 := dist_triangle (P.physical p) (position P.mesh v) (P.physical P.center)
  have h2 := dist_triangle (position P.mesh v) (P.physical p) (P.physical P.center)
  rw [dist_comm (position P.mesh v) (P.physical p)] at h2
  refine ⟨P.halfPlane.cell_center hp hq,?_,?_⟩
  all_goals dsimp [HalfProbe.radius]; linarith [P.radii,P.inner_pos,P.mesh_pos]

theorem HalfProbe.changed_cell (P : HalfProbe) (he : 16*P.mesh < P.innerRadius)
    {a b : Configuration} (hab : ∀ v, v ∉ P.pocket → a v=b v)
    {v : Site} (hv : a v ≠ b v) :
    HexTiling.physicalCell P.mesh v ⊆ Metric.ball (P.physical P.center) (3*P.innerRadius/4) := by
  have hp : v ∈ P.pocket := by by_contra h; exact hv (hab v h)
  apply HexTiling.physicalCell_subset_ball
  rw [abs_of_pos P.mesh_pos]
  change P.radius v+2*P.mesh < 3*P.innerRadius/4
  change P.radius v < P.innerRadius/2 at hp
  linarith [P.mesh_pos]

def PolygonQuad.side (Q : PolygonQuad) (s : Bool × Bool) : Set (ℝ × ℝ) :=
  if s.1 then (if s.2 then Q.top else Q.bottom)
  else (if s.2 then Q.right else Q.left)

/-- Literal half-side clause of source02 Lemma 2.2. The selected side
is a straight line throughout the probe disk; the other three terminal
arcs are outside that disk. The quad equals the stated half-plane there.
Thus no microscopic polygon corners are suppressed in this interface. -/
def PublishedPolygonHalfArms : Prop :=
  ∀ (Q : PolygonQuad) (P : HalfProbe) (s : Bool × Bool) (ω a b : Configuration),
    16*P.mesh < P.innerRadius →
    P.center ∈ Q.side s →
    (∀ p, dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius →
      (p ∈ Q.carrier ↔ p ∈ P.halfPlane.carrier)) →
    (∀ p, dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius →
      (p ∈ Q.side s ↔ p ∈ P.halfPlane.boundary)) →
    (∀ t, t ≠ s → ∀ p ∈ Q.side t,
      2*P.outerRadius < dist (P.physical p) (P.physical P.center)) →
    (∀ v, a v ≠ b v → HexTiling.physicalCell P.mesh v ⊆
      Metric.ball (P.physical P.center) (3*P.innerRadius/4)) →
    (∀ v, (HexTiling.physicalCell P.mesh v ∩ P.agreementShell).Nonempty →
      a v=ω v ∧ b v=ω v) →
    ¬ (Q.Crossing a ↔ Q.Crossing b) → HalfThreeArms P ω

def LocalChangeHalfArms (Q : GraphQuad) (P : HalfProbe) : Prop :=
  ∀ ω a b : Configuration,
    (∀ v, v ∉ P.pocket → a v=b v) →
    EqOn a ω P.region → EqOn b ω P.region →
    Q.test a ≠ Q.test b → HalfThreeArms P ω

theorem straightBox_localChangeHalfArms_of_published
    (hsource : PublishedPolygonHalfArms) (n : ℕ) (hn : 0<n) (P : HalfProbe)
    (s : Bool × Bool) (he : 16*P.mesh < P.innerRadius)
    (hcenter : P.center ∈ (straightBoxPolygonQuad n hn).side s)
    (hcarrier : ∀ p, dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius →
      (p ∈ axialRectangle n ↔ p ∈ P.halfPlane.carrier))
    (hside : ∀ p, dist (P.physical p) (P.physical P.center) ≤ 2*P.outerRadius →
      (p ∈ (straightBoxPolygonQuad n hn).side s ↔ p ∈ P.halfPlane.boundary))
    (hother : ∀ t, t ≠ s → ∀ p ∈ (straightBoxPolygonQuad n hn).side t,
      2*P.outerRadius < dist (P.physical p) (P.physical P.center)) :
    LocalChangeHalfArms (axialBoxQuad n) P := by
  intro ω a b hab ha hb hchange
  apply hsource (straightBoxPolygonQuad n hn) P s ω a b he hcenter hcarrier hside hother
  · exact fun v hv => P.changed_cell he hab hv
  · exact fun v hv => ⟨ha (P.cell_meets_shell he hv),hb (P.cell_meets_shell he hv)⟩
  · rw [straightBoxPolygonQuad_crossing_iff,straightBoxPolygonQuad_crossing_iff]
    intro h
    exact hchange (decide_eq_decide.mpr h)

noncomputable def completeColors (D : Finset Site) (ω : D → Bool) : Configuration :=
  fun v => if h : v ∈ D then ω ⟨v,h⟩ else false

/-- Source02's standard-orientation alternating-three-arm upper bound,
for the literal iid fair-site law and with its mesh cutoff retained.
The two possible outside-arm colors are included in the constant C. -/
def PublishedHalfThreeArmBound (B₀ C : ℝ) : Prop :=
  ∀ (P : HalfProbe) (D : Finset Site), B₀*P.mesh ≤ P.innerRadius →
    P.region ⊆ (D : Set Site) →
    EnvironmentVariance.probability (ProbeProduct.fairSites D)
      (fun ω => HalfThreeArms P (completeColors D ω)) ≤ C*(P.innerRadius/P.outerRadius)^2

#print axioms LatticeHalfPlane.cell_center
#print axioms straightBox_localChangeHalfArms_of_published

end ExceptionalTimes.PairSquareSewing

