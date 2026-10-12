import ExceptionalTimes.PolyhexPolygon
import ExceptionalTimes.NecklaceDictionary
import ExceptionalTimes.PolyhexBulk

open Set

namespace ExceptionalTimes.PairSquareSewing

noncomputable def axialPlaneHomeomorph : (ℝ × ℝ) ≃ₜ ℂ where
  toFun := HexTiling.planeMap
  invFun := fun z => (z.re-z.im/Real.sqrt 3,2*z.im/Real.sqrt 3)
  left_inv := by
    intro p
    have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    apply Prod.ext
    · dsimp [HexTiling.planeMap]
      field_simp
      ring
    · dsimp [HexTiling.planeMap]
      field_simp
  right_inv := by
    intro z
    have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    apply Complex.ext
    · dsimp [HexTiling.planeMap]
      ring
    · dsimp [HexTiling.planeMap]
      field_simp
  continuous_toFun := HexTiling.continuous_planeMap
  continuous_invFun := by fun_prop

noncomputable def physicalHomeomorph (P : Probe) : (ℝ × ℝ) ≃ₜ ℂ :=
  axialPlaneHomeomorph.trans (Homeomorph.mulLeft₀ (P.mesh : ℂ) (by exact_mod_cast ne_of_gt P.mesh_pos))

theorem physicalHomeomorph_apply (P : Probe) (p : ℝ × ℝ) :
    physicalHomeomorph P p = (P.mesh : ℂ)*HexTiling.planeMap p := rfl

theorem physicalHomeomorph_center (P : Probe) (v : Site) :
    physicalHomeomorph P (HexCells.center v) = position P.mesh v := rfl

def whiteOutsideBox (n : ℕ) (ω : Configuration) : Configuration :=
  fun v => if v ∈ latticeBox n then ω v else false

def globalBlackCells (ω : Configuration) : Set (ℝ × ℝ) :=
  {p | ∃ u : Site, ω u = true ∧ p ∈ HexCells.cell u}

def PolygonQuad.Crossing (Q : PolygonQuad) (ω : Configuration) : Prop :=
  ∃ a ∈ Q.left, ∃ b ∈ Q.right, JoinedIn (globalBlackCells ω ∩ Q.carrier) a b

def globalPhysicalBlackCells (P : Probe) (ω : Configuration) : Set ℂ :=
  {z | ∃ v : Site, ω v = true ∧ z ∈ HexTiling.physicalCell P.mesh v}

theorem physicalBlackCells_eq_image (P : Probe) (ω : Configuration) :
    globalPhysicalBlackCells P ω = physicalHomeomorph P '' globalBlackCells ω := by
  ext z
  constructor
  · rintro ⟨v,hv,p,hp,rfl⟩
    exact ⟨p,⟨v,hv,hp⟩,rfl⟩
  · rintro ⟨p,⟨v,hv,hp⟩,rfl⟩
    exact ⟨v,hv,p,hp,rfl⟩

def PolygonQuad.PhysicalCrossing (Q : PolygonQuad) (P : Probe) (ω : Configuration) : Prop :=
  ∃ a ∈ physicalHomeomorph P '' Q.left, ∃ b ∈ physicalHomeomorph P '' Q.right,
    JoinedIn (globalPhysicalBlackCells P ω ∩ physicalHomeomorph P '' Q.carrier) a b

theorem PolygonQuad.physicalCrossing_iff (Q : PolygonQuad) (P : Probe) (ω : Configuration) :
    Q.PhysicalCrossing P ω ↔ Q.Crossing ω := by
  have hs : globalPhysicalBlackCells P ω ∩ physicalHomeomorph P '' Q.carrier =
      physicalHomeomorph P '' (globalBlackCells ω ∩ Q.carrier) := by
    rw [physicalBlackCells_eq_image,Set.image_inter (physicalHomeomorph P).injective]
  constructor
  · rintro ⟨a,⟨x,hx,rfl⟩,b,⟨y,hy,rfl⟩,hj⟩
    rw [hs] at hj
    have h := hj.map (physicalHomeomorph P).symm.continuous.continuousOn
    refine ⟨x,hx,y,hy,?_⟩
    simpa only [image_image,Function.comp_def,Homeomorph.symm_apply_apply,image_id'] using h
  · rintro ⟨a,ha,b,hb,hj⟩
    refine ⟨physicalHomeomorph P a,⟨a,ha,rfl⟩,physicalHomeomorph P b,⟨b,hb,rfl⟩,?_⟩
    rw [hs]
    exact hj.map (physicalHomeomorph P).continuous.continuousOn

theorem globalBlackCells_whiteOutside (n : ℕ) (ω : Configuration) :
    globalBlackCells (whiteOutsideBox n ω) = blackCellUnion HexCells.cell (axialBoxQuad n) ω := by
  ext p
  constructor
  · rintro ⟨u,hu,hpu⟩
    by_cases hud : u ∈ latticeBox n
    · exact ⟨u,hud,by simpa [whiteOutsideBox,hud] using hu,hpu⟩
    · simp [whiteOutsideBox,hud] at hu
  · rintro ⟨u,hud,hu,hpu⟩
    change u ∈ latticeBox n at hud
    exact ⟨u,by simpa [whiteOutsideBox,hud] using hu,hpu⟩

/-- White completion of the exterior fixes the closed-cell boundary
convention: no exterior black cell can contribute a boundary-only path. -/
theorem axialBox_polygonCrossing_iff (n : ℕ) (ω : Configuration) :
    (axialBoxPolygonQuad n).Crossing (whiteOutsideBox n ω) ↔ (axialBoxQuad n).Crossing ω := by
  have hset : globalBlackCells (whiteOutsideBox n ω) ∩ polyhex n =
      blackCellUnion HexCells.cell (axialBoxQuad n) ω := by
    rw [globalBlackCells_whiteOutside]
    exact inter_eq_left.mpr (blackCellUnion_subset_polyhex n ω)
  rw [axialBox_graphCrossing_iff_arcCrossing]
  change (∃ a ∈ leftPolyhexArc n, ∃ b ∈ rightPolyhexArc n,
    JoinedIn (globalBlackCells (whiteOutsideBox n ω) ∩ polyhex n) a b) ↔ _
  rw [hset]
  rfl

theorem center_mem_hexCell_iff (u v : Site) : HexCells.center u ∈ HexCells.cell v ↔ u = v := by
  constructor
  · intro h
    have hb := HexCells.coordinate_bounds h
    dsimp [HexCells.center] at hb
    have hxR : |(u.1 : ℝ)-(v.1 : ℝ)| < 1 := by linarith [hb.1]
    have hyR : |(u.2 : ℝ)-(v.2 : ℝ)| < 1 := by linarith [hb.2]
    have hx : |u.1-v.1| < 1 := by exact_mod_cast hxR
    have hy : |u.2-v.2| < 1 := by exact_mod_cast hyR
    rw [abs_lt] at hx hy
    apply Prod.ext <;> omega
  · rintro rfl
    exact HexCells.center_mem_cell _

theorem center_mem_polyhex_iff (n : ℕ) (u : Site) :
    HexCells.center u ∈ polyhex n ↔ u ∈ latticeBox n := by
  constructor
  · intro hp
    obtain ⟨v,hv,hpu⟩ := mem_iUnion₂.mp hp
    exact (center_mem_hexCell_iff u v).mp hpu ▸ hv
  · intro hu
    exact mem_iUnion₂_of_mem hu (HexCells.center_mem_cell u)

theorem whiteOutsideBox_agrees (n : ℕ) {a b : Configuration} {S : Set Site}
    (h : Set.EqOn a b S) : Set.EqOn (whiteOutsideBox n a) (whiteOutsideBox n b) S := by
  intro v hv
  by_cases hd : v ∈ latticeBox n
  · simpa [whiteOutsideBox,hd] using h hv
  · simp [whiteOutsideBox,hd]

theorem whiteOutsideBox_changed (n : ℕ) {a b : Configuration} {v : Site}
    (h : whiteOutsideBox n a v ≠ whiteOutsideBox n b v) : a v ≠ b v := by
  by_cases hd : v ∈ latticeBox n
  · simpa [whiteOutsideBox,hd] using h
  · simp [whiteOutsideBox,hd] at h

def Probe.agreementShell (P : Probe) : Set ℂ :=
  {z | 3*P.innerRadius/4 ≤ dist z (position P.mesh P.center) ∧
    dist z (position P.mesh P.center) ≤ 3*P.outerRadius/2}

/-- The source's annulus is strictly inside the site-agreement buffer.
The cell diameter correction is explicit and uses the actual hexagons. -/
theorem cell_meets_agreementShell_in_region (P : Probe) (he : 16*P.mesh < P.innerRadius)
    {v : Site} (hv : (HexTiling.physicalCell P.mesh v ∩ P.agreementShell).Nonempty) :
    v ∈ P.region := by
  obtain ⟨z,hz,hzshell⟩ := hv
  have hcell := HexTiling.physicalCell_radius hz
  rw [abs_of_pos P.mesh_pos] at hcell
  have h1 := dist_triangle z (position P.mesh v) (position P.mesh P.center)
  have h2 := dist_triangle (position P.mesh v) z (position P.mesh P.center)
  rw [dist_comm (position P.mesh v) z] at h2
  change dist z (position P.mesh v) ≤ 2*P.mesh at hcell
  change P.innerRadius/2 ≤ P.radius v ∧ P.radius v ≤ 2*P.outerRadius
  dsimp [Probe.radius]
  constructor <;> linarith [hzshell.1,hzshell.2,P.radii,P.inner_pos,P.mesh_pos]

theorem changed_cell_in_buffered_ball (P : Probe) (he : 16*P.mesh < P.innerRadius)
    {a b : Configuration} (hab : ∀ v, v ∉ P.pocket → a v = b v)
    {v : Site} (hv : a v ≠ b v) :
    HexTiling.physicalCell P.mesh v ⊆ Metric.ball (position P.mesh P.center) (3*P.innerRadius/4) := by
  have hpocket : v ∈ P.pocket := by by_contra h; exact hv (hab v h)
  apply HexTiling.physicalCell_subset_ball
  rw [abs_of_pos P.mesh_pos]
  change P.radius v + 2*P.mesh < 3*P.innerRadius/4
  change P.radius v < P.innerRadius/2 at hpocket
  linarith [P.mesh_pos]

/-- Literal bulk clause of the published necessary-arms lemma in
02-inputs.tex, Lemma 2.2, including its site-path conversion and first
outer/last inner trimming convention. The hex cells are the actual
scaled Euclidean cells. The change is contained in radius 3r/4;
the unchanged shell is [3r/4,3R/2], with 16e<r. One may start the
trimmed arms at radius 7r/8 and then stop at first contact with R.
This is a named published input, not a proved theorem or a global axiom.
There is no probabilistic estimate in this statement. -/
def PublishedPolygonBulkArms : Prop :=
  ∀ (Q : PolygonQuad) (P : Probe) (ω a b : Configuration),
    16*P.mesh < P.innerRadius →
    Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalHomeomorph P '' interior Q.carrier →
    (∀ v, a v ≠ b v → HexTiling.physicalCell P.mesh v ⊆
      Metric.ball (position P.mesh P.center) (3*P.innerRadius/4)) →
    (∀ v, (HexTiling.physicalCell P.mesh v ∩ P.agreementShell).Nonempty →
      a v = ω v ∧ b v = ω v) →
    ¬ (Q.PhysicalCrossing P a ↔ Q.PhysicalCrossing P b) →
    FourArms P ω

theorem bulk_region_inside_box (n : ℕ) (P : Probe)
    (hbulk : Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalHomeomorph P '' interior (polyhex n)) : P.region ⊆ (latticeBox n : Set Site) := by
  intro v hv
  have hvball : position P.mesh v ∈ Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) := hv.2
  obtain ⟨p,hp,hpp⟩ := hbulk hvball
  have hpe : p = HexCells.center v := (physicalHomeomorph P).injective
    (hpp.trans (physicalHomeomorph_center P v).symm)
  apply (center_mem_polyhex_iff n v).mp
  rw [← hpe]
  exact interior_subset hp

/-- Concrete source specialization for the actual finite axial board.
Every geometric dictionary condition has been proved; the only
percolation input here is the stated published bulk local-change lemma.
The remaining displayed bulk inclusion is a geometric size condition. -/
theorem axialBox_localChangeArms_of_published
    (hsource : PublishedPolygonBulkArms) (n : ℕ) (P : Probe)
    (he : 16*P.mesh < P.innerRadius)
    (hbulk : Metric.closedBall (position P.mesh P.center) (2*P.outerRadius) ⊆
      physicalHomeomorph P '' interior (polyhex n)) : LocalChangeArms (axialBoxQuad n) P := by
  intro ω a b hab ha hb hchange
  have hsourceArms := hsource (axialBoxPolygonQuad n) P (whiteOutsideBox n ω)
    (whiteOutsideBox n a) (whiteOutsideBox n b) he hbulk
  have hchanged : ∀ v, whiteOutsideBox n a v ≠ whiteOutsideBox n b v →
      HexTiling.physicalCell P.mesh v ⊆ Metric.ball (position P.mesh P.center) (3*P.innerRadius/4) := by
    intro v hv
    exact changed_cell_in_buffered_ball P he hab (whiteOutsideBox_changed n hv)
  have hagree : ∀ v, (HexTiling.physicalCell P.mesh v ∩ P.agreementShell).Nonempty →
      whiteOutsideBox n a v = whiteOutsideBox n ω v ∧
      whiteOutsideBox n b v = whiteOutsideBox n ω v := by
    intro v hv
    have hreg := cell_meets_agreementShell_in_region P he hv
    exact ⟨whiteOutsideBox_agrees n ha hreg,whiteOutsideBox_agrees n hb hreg⟩
  have hcross : ¬ ((axialBoxPolygonQuad n).PhysicalCrossing P (whiteOutsideBox n a) ↔
      (axialBoxPolygonQuad n).PhysicalCrossing P (whiteOutsideBox n b)) := by
    intro h
    rw [PolygonQuad.physicalCrossing_iff,PolygonQuad.physicalCrossing_iff,
      axialBox_polygonCrossing_iff,axialBox_polygonCrossing_iff] at h
    apply hchange
    exact decide_eq_decide.mpr h
  have har := hsourceArms hchanged hagree hcross
  apply (fourArms_congr P (ω := whiteOutsideBox n ω) (η := ω) ?_).mp har
  intro v hv
  have hvbox : v ∈ latticeBox n := bulk_region_inside_box n P hbulk hv
  simp [whiteOutsideBox,hvbox]

/-- A fully concrete axial-board instance, with only numerical mesh
and clearance conditions in addition to the published bulk lemma. -/
theorem axialBox_localChangeArms (hsource : PublishedPolygonBulkArms) (n : ℕ) (P : Probe)
    (he : 16*P.mesh < P.innerRadius)
    (hmargin : 2*(‖position P.mesh P.center‖+2*P.outerRadius) < P.mesh*n) :
    LocalChangeArms (axialBoxQuad n) P := by
  apply axialBox_localChangeArms_of_published hsource n P he
  exact probe_closedBall_subset_physicalPolyhexInterior P n hmargin

#print axioms axialBox_polygonCrossing_iff
#print axioms cell_meets_agreementShell_in_region
#print axioms axialBox_localChangeArms_of_published
#print axioms axialBox_localChangeArms

end ExceptionalTimes.PairSquareSewing
