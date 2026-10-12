import ExceptionalTimes.StraightBoxSeparation
import Mathlib.Analysis.Normed.Module.Convex

/-! Local geometry of genuine finite axial polygon segments. Endpoints are
explicit roots. A contact away from both endpoints sees the whole supporting
line inside a larger ball; this is independent of any crossing event. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open HexTiling

/-- An affine line crossing a convex set between parameters zero and one
cannot return to that set beyond either endpoint when both endpoints are
outside. This is applied to physical closed probe balls. -/
theorem affine_interval_of_convex (L : ℝ →ᵃ[ℝ] ℂ) (S : Set ℂ) (hS : Convex ℝ S)
    (hzero : L 0 ∉ S) (hone : L 1 ∉ S)
    {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (huS : L u ∈ S) (ht : L t ∈ S) :
    t ∈ Icc (0:ℝ) 1 := by
  have hc := (hS.affine_preimage L).ordConnected
  constructor
  · by_contra hn
    have hz : 0 ∈ L ⁻¹' S := hc.out ht huS ⟨(not_le.mp hn).le,hu.1⟩
    exact hzero hz
  · by_contra hn
    have hz : 1 ∈ L ⁻¹' S := hc.out huS ht ⟨hu.2,(not_le.mp hn).le⟩
    exact hone hz

theorem axialPhysical_lineMap (ε : ℝ) (a b : ℝ × ℝ) (t : ℝ) :
    axialPhysical ε (AffineMap.lineMap a b t) =
      AffineMap.lineMap (axialPhysical ε a) (axialPhysical ε b) t := by
  apply Complex.ext <;>
    simp [axialPhysical,planeMap,AffineMap.lineMap_apply_module] <;> ring

/-- A nondegenerate straight segment in one of the two axial grid directions. -/
structure AxialSegment where
  first : ℝ × ℝ
  last : ℝ × ℝ
  horizontal : Bool
  parallel : if horizontal then first.2=last.2 else first.1=last.1
  nondegenerate : first≠last

namespace AxialSegment

noncomputable def point (s : AxialSegment) (t : ℝ) : ℝ × ℝ :=
  AffineMap.lineMap s.first s.last t

def onLine (s : AxialSegment) (p : ℝ × ℝ) : Prop :=
  if s.horizontal then p.2=s.first.2 else p.1=s.first.1

def contains (s : AxialSegment) (p : ℝ × ℝ) : Prop :=
  ∃ t ∈ Icc (0:ℝ) 1, s.point t=p

def contact (s : AxialSegment) (ε : ℝ) (c : ℝ × ℝ) (R : ℝ) : Prop :=
  ∃ t ∈ Icc (0:ℝ) 1,
    dist (axialPhysical ε c) (axialPhysical ε (s.point t))≤2*R

theorem point_onLine (s : AxialSegment) (t : ℝ) : s.onLine (s.point t) := by
  have h := s.parallel
  cases hh : s.horizontal <;>
    simp only [hh,Bool.false_eq_true,ite_false,ite_true] at h
  · simp only [onLine,hh,Bool.false_eq_true,ite_false,point,AffineMap.lineMap_apply_module,
      Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    rw [← h]
    ring
  · simp only [onLine,hh,ite_true,point,AffineMap.lineMap_apply_module,
      Prod.snd_add,Prod.smul_snd,smul_eq_mul]
    rw [← h]
    ring

theorem onLine_iff_range (s : AxialSegment) (p : ℝ × ℝ) :
    s.onLine p ↔ ∃ t, s.point t=p := by
  constructor
  · intro hp
    have h := s.parallel
    cases hh : s.horizontal <;>
      simp only [onLine,hh,Bool.false_eq_true,ite_false,ite_true] at h hp
    · have hn : s.last.2-s.first.2≠0 := by
        intro he
        apply s.nondegenerate
        exact Prod.ext h (by linarith)
      refine ⟨(p.2-s.first.2)/(s.last.2-s.first.2),?_⟩
      apply Prod.ext
      · simp only [point,AffineMap.lineMap_apply_module,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
        rw [← h, hp]
        ring
      · simp only [point,AffineMap.lineMap_apply_module,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
        field_simp [hn]
        ring
    · have hn : s.last.1-s.first.1≠0 := by
        intro he
        apply s.nondegenerate
        exact Prod.ext (by linarith) h
      refine ⟨(p.1-s.first.1)/(s.last.1-s.first.1),?_⟩
      apply Prod.ext
      · simp only [point,AffineMap.lineMap_apply_module,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
        field_simp [hn]
        ring
      · simp only [point,AffineMap.lineMap_apply_module,Prod.snd_add,Prod.smul_snd,smul_eq_mul]
        rw [← h,hp]
        ring
  · rintro ⟨t,rfl⟩
    exact s.point_onLine t

/-- All of the supporting line within radius six R belongs to the actual
finite segment. Root distance eight R excludes seeing an endpoint. -/
theorem contains_of_near_line (s : AxialSegment) {ε R : ℝ} {c p : ℝ × ℝ}
    (hR : 0<R) (hc : s.contact ε c R)
    (hfirst : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.first))
    (hlast : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.last))
    (hp : s.onLine p) (hpc : dist (axialPhysical ε c) (axialPhysical ε p)≤6*R) :
    s.contains p := by
  obtain ⟨u,hu,huc⟩ := hc
  obtain ⟨t,rfl⟩ := (s.onLine_iff_range p).mp hp
  let L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap (axialPhysical ε s.first) (axialPhysical ε s.last)
  have h0 : L 0 ∉ Metric.closedBall (axialPhysical ε c) (6*R) := by
    simp only [L,AffineMap.lineMap_apply_zero,Metric.mem_closedBall,dist_comm]
    linarith
  have h1 : L 1 ∉ Metric.closedBall (axialPhysical ε c) (6*R) := by
    simp only [L,AffineMap.lineMap_apply_one,Metric.mem_closedBall,dist_comm]
    linarith
  have huS : L u ∈ Metric.closedBall (axialPhysical ε c) (6*R) := by
    rw [Metric.mem_closedBall,dist_comm]
    change dist _ (AffineMap.lineMap _ _ u)≤_
    rw [← axialPhysical_lineMap]
    change dist _ (axialPhysical ε (s.point u))≤_
    linarith
  have htS : L t ∈ Metric.closedBall (axialPhysical ε c) (6*R) := by
    rw [Metric.mem_closedBall,dist_comm]
    change dist _ (AffineMap.lineMap _ _ t)≤_
    rw [← axialPhysical_lineMap]
    exact hpc
  exact ⟨t,affine_interval_of_convex L _ (convex_closedBall _ _) h0 h1 hu huS htS,rfl⟩

noncomputable def level (s : AxialSegment) : ℝ :=
  if s.horizontal then s.first.2 else s.first.1

theorem contact_coordinate (s : AxialSegment) {ε R : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hc : s.contact ε c R) :
    ε*|(if s.horizontal then c.2 else c.1)-s.level|≤3*R := by
  obtain ⟨u,hu,huc⟩ := hc
  have hp := s.point_onLine u
  cases hh : s.horizontal
  · have h : NearVertical ε c s.first.1 (2*R) := by
      refine ⟨s.point u,?_,huc⟩
      simpa only [onLine,hh,Bool.false_eq_true,ite_false] using hp
    have ht := nearVertical_coordinate hε h
    simp only [level,hh,Bool.false_eq_true,ite_false]
    linarith
  · have h : NearHorizontal ε c s.first.2 (2*R) := by
      refine ⟨s.point u,?_,huc⟩
      simpa only [onLine,hh,ite_true] using hp
    have ht := nearHorizontal_coordinate hε h
    simp only [level,hh,ite_true]
    linarith

theorem parallel_contact_levels (s t : AxialSegment) {ε R : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hparallel : s.horizontal=t.horizontal)
    (hs : s.contact ε c R) (ht : t.contact ε c R) :
    ε*|s.level-t.level|≤6*R := by
  have h1 := s.contact_coordinate hε hs
  have h2 := t.contact_coordinate hε ht
  rw [hparallel] at h1
  have htri := abs_sub_le s.level (if t.horizontal then c.2 else c.1) t.level
  rw [abs_sub_comm s.level (if t.horizontal then c.2 else c.1)] at htri
  have hm := mul_le_mul_of_nonneg_left htri hε
  linarith

theorem perpendicular_contact_intersection (s t : AxialSegment) {ε R : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hR : 0<R) (hsdir : s.horizontal=false) (htdir : t.horizontal=true)
    (hs : s.contact ε c R) (ht : t.contact ε c R)
    (hsfirst : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.first))
    (hslast : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.last))
    (htfirst : 8*R≤dist (axialPhysical ε c) (axialPhysical ε t.first))
    (htlast : 8*R≤dist (axialPhysical ε c) (axialPhysical ε t.last)) :
    ∃ p, s.contains p ∧ t.contains p ∧ dist (axialPhysical ε c) (axialPhysical ε p)≤6*R := by
  have hsline : NearVertical ε c s.first.1 (2*R) := by
    obtain ⟨u,hu,huc⟩ := hs
    refine ⟨s.point u,?_,huc⟩
    simpa only [onLine,hsdir,Bool.false_eq_true,ite_false] using s.point_onLine u
  have htline : NearHorizontal ε c t.first.2 (2*R) := by
    obtain ⟨u,hu,huc⟩ := ht
    refine ⟨t.point u,?_,huc⟩
    simpa only [onLine,htdir,ite_true] using t.point_onLine u
  have hp : dist (axialPhysical ε c) (axialPhysical ε (s.first.1,t.first.2))≤6*R := by
    linarith [near_incident_corner hε hsline htline]
  refine ⟨(s.first.1,t.first.2),?_,?_,hp⟩
  · exact s.contains_of_near_line hR hs hsfirst hslast
      (by simp only [onLine,hsdir,Bool.false_eq_true,ite_false]) hp
  · exact t.contains_of_near_line hR ht htfirst htlast
      (by simp only [onLine,htdir,ite_true]) hp

theorem sameLine_contact_intersection (s t : AxialSegment) {ε R : ℝ} {c : ℝ × ℝ}
    (hR : 0<R) (hparallel : s.horizontal=t.horizontal) (hlevel : s.level=t.level)
    (hs : s.contact ε c R) (ht : t.contact ε c R)
    (hsfirst : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.first))
    (hslast : 8*R≤dist (axialPhysical ε c) (axialPhysical ε s.last)) :
    ∃ p, s.contains p ∧ t.contains p ∧ dist (axialPhysical ε c) (axialPhysical ε p)≤6*R := by
  obtain ⟨u,hu,huc⟩ := ht
  have hp : s.onLine (t.point u) := by
    have hp := t.point_onLine u
    cases hsdir : s.horizontal <;> have htdir := hsdir ▸ hparallel.symm
    · simp only [level,hsdir,htdir,Bool.false_eq_true,ite_false] at hlevel
      simpa only [onLine,hsdir,htdir,Bool.false_eq_true,ite_false,← hlevel] using hp
    · simp only [level,hsdir,htdir,ite_true] at hlevel
      simpa only [onLine,hsdir,htdir,ite_true,← hlevel] using hp
  have hd : dist (axialPhysical ε c) (axialPhysical ε (t.point u))≤6*R := by linarith
  exact ⟨t.point u,s.contains_of_near_line hR hs hsfirst hslast hp hd,⟨u,hu,rfl⟩,hd⟩

end AxialSegment

/-- The positive scale is extracted from the actual finite set of distinct
parallel supporting-line levels; it is not a probabilistic hypothesis. -/
theorem finite_parallel_level_separation {E : Type*} [Fintype E] (edge : E → AxialSegment) :
    ∃ δ : ℝ, 0<δ ∧ ∀ i j, (edge i).horizontal=(edge j).horizontal →
      (edge i).level≠(edge j).level → δ≤|(edge i).level-(edge j).level| := by
  let P : Finset (E × E) := Finset.univ.filter (fun ij =>
    (edge ij.1).horizontal=(edge ij.2).horizontal ∧ (edge ij.1).level≠(edge ij.2).level)
  by_cases hP : P.Nonempty
  · obtain ⟨ij,hij,hmin⟩ := P.exists_min_image (fun ij => |(edge ij.1).level-(edge ij.2).level|) hP
    have hne := (Finset.mem_filter.mp hij).2.2
    refine ⟨|(edge ij.1).level-(edge ij.2).level|,abs_pos.mpr (sub_ne_zero.mpr hne),?_⟩
    intro i j hh hl
    exact hmin (i,j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,hl⟩)
  · refine ⟨1,by norm_num,?_⟩
    intro i j hh hl
    exact (hP ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,hl⟩⟩).elim

/-- Distinct segments of a simple polygon meet only at segment endpoints.
This is literal segment geometry; no crossing or arm event occurs here. -/
def SimpleSegmentFamily {E : Type*} (edge : E → AxialSegment) : Prop :=
  ∀ i j, i≠j → ∀ p, (edge i).contains p → (edge j).contains p →
    p=(edge i).first ∨ p=(edge i).last

/-- Away from every real polygon vertex, a sufficiently small probe sees
at most one finite polygon segment, including collinear-segment cases. -/
theorem polygon_contact_unique {E : Type*} (edge : E → AxialSegment)
    (hsimple : SimpleSegmentFamily edge) {ε R δ : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hR : 0<R) (hscale : 6*R<ε*δ)
    (hparallel : ∀ i j, (edge i).horizontal=(edge j).horizontal →
      (edge i).level≠(edge j).level → δ≤|(edge i).level-(edge j).level|)
    (hroots : ∀ i, 8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).first) ∧
      8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).last))
    {i j : E} (hi : (edge i).contact ε c R) (hj : (edge j).contact ε c R) : i=j := by
  by_contra hne
  have hcommon : ∃ p, (edge i).contains p ∧ (edge j).contains p ∧
      dist (axialPhysical ε c) (axialPhysical ε p)≤6*R := by
    by_cases hdir : (edge i).horizontal=(edge j).horizontal
    · by_cases hlevel : (edge i).level=(edge j).level
      · exact AxialSegment.sameLine_contact_intersection _ _ hR hdir hlevel hi hj
          (hroots i).1 (hroots i).2
      · have hl := AxialSegment.parallel_contact_levels _ _ hε hdir hi hj
        have hm := mul_le_mul_of_nonneg_left (hparallel i j hdir hlevel) hε
        exact (not_lt_of_ge (hm.trans hl) hscale).elim
    · cases he : (edge i).horizontal <;> cases hf : (edge j).horizontal
      · exact (hdir (he.trans hf.symm)).elim
      · exact AxialSegment.perpendicular_contact_intersection _ _ hε hR he hf hi hj
          (hroots i).1 (hroots i).2 (hroots j).1 (hroots j).2
      · obtain ⟨p,hpj,hpi,hp⟩ := AxialSegment.perpendicular_contact_intersection _ _ hε hR hf he hj hi
          (hroots j).1 (hroots j).2 (hroots i).1 (hroots i).2
        exact ⟨p,hpi,hpj,hp⟩
      · exact (hdir (he.trans hf.symm)).elim
  obtain ⟨p,hpi,hpj,hp⟩ := hcommon
  rcases hsimple i j hne p hpi hpj with hpfirst | hplast
  · rw [hpfirst] at hp
    linarith [(hroots i).1]
  · rw [hplast] at hp
    linarith [(hroots i).2]


/-- Exact local boundary-set identity, not merely uniqueness of a chosen
contact. Inside the probe ball the polygon segment union is a full line. -/
theorem polygon_boundary_eq_line {E : Type*} (edge : E → AxialSegment)
    (hsimple : SimpleSegmentFamily edge) {ε R δ : ℝ} {c : ℝ × ℝ}
    (hε : 0≤ε) (hR : 0<R) (hscale : 6*R<ε*δ)
    (hparallel : ∀ i j, (edge i).horizontal=(edge j).horizontal →
      (edge i).level≠(edge j).level → δ≤|(edge i).level-(edge j).level|)
    (hroots : ∀ i, 8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).first) ∧
      8*R≤dist (axialPhysical ε c) (axialPhysical ε (edge i).last))
    (i : E) (hi : (edge i).contact ε c R) (p : ℝ × ℝ)
    (hp : dist (axialPhysical ε c) (axialPhysical ε p)≤2*R) :
    (∃ j, (edge j).contains p) ↔ (edge i).onLine p := by
  constructor
  · rintro ⟨j,t,ht,hp'⟩
    have hj : (edge j).contact ε c R := ⟨t,ht,by rwa [hp']⟩
    have he := polygon_contact_unique edge hsimple hε hR hscale hparallel hroots hi hj
    subst j
    rw [← hp']
    exact (edge i).point_onLine t
  · intro hline
    exact ⟨i,(edge i).contains_of_near_line hR hi (hroots i).1 (hroots i).2 hline (by linarith)⟩

/-- Every endpoint is an actual fixed forest root. The positive-life
external-distance theorem supplies the required eight-radius clearance. -/
theorem life_polygon_contact_unique {E V : Type*} [Fintype V]
    (edge : E → AxialSegment) (hsimple : SimpleSegmentFamily edge)
    (fixed : V → Prop) (anchor : V → ℂ) {cutoff stop ε δ : ℝ}
    (hcut : 0<cutoff) (hε : 0≤ε) (hscale : 6*(stop/8)<ε*δ)
    (hparallel : ∀ i j, (edge i).horizontal=(edge j).horizontal →
      (edge i).level≠(edge j).level → δ≤|(edge i).level-(edge j).level|)
    (vertex : E → Bool → V) (hfixed : ∀ i b, fixed (vertex i b))
    (hvertex : ∀ i b, anchor (vertex i b)=
      axialPhysical ε (if b then (edge i).last else (edge i).first))
    (a : ForestArmProbability.Life fixed anchor cutoff stop) (c : ℝ × ℝ)
    (hcenter : anchor (ForestArmProbability.center fixed anchor cutoff stop a)=axialPhysical ε c)
    {i j : E}
    (hi : (edge i).contact ε c (KruskalLives.death fixed anchor cutoff stop a.val/8))
    (hj : (edge j).contact ε c (KruskalLives.death fixed anchor cutoff stop a.val/8)) : i=j := by
  have h := ForestTelescope.positiveLives_spec fixed anchor cutoff stop a.property
  have hu := hcut.trans_le (KruskalLives.cutoff_le_birth h.1)
  have hv := hu.trans h.2.2
  have hstop := KruskalLives.death_le_stop h.1
  apply polygon_contact_unique edge hsimple hε (by positivity) (by linarith) hparallel _ hi hj
  intro e
  have hdist (b : Bool) : KruskalLives.death fixed anchor cutoff stop a.val ≤
      dist (axialPhysical ε c) (axialPhysical ε (if b then (edge e).last else (edge e).first)) := by
    have hout : vertex e b ∉ a.val := fun hin => h.2.1 _ hin (hfixed e b)
    have hd := KruskalLives.life_external_distance h.1 h.2.2
      (ForestArmProbability.center_mem fixed anchor cutoff stop a) hout
    rwa [hcenter,hvertex] at hd
  have hf := hdist false
  have hl := hdist true
  simp only [Bool.false_eq_true,ite_false,ite_true] at hf hl
  constructor <;> linarith

#print axioms AxialSegment.contains_of_near_line
#print axioms finite_parallel_level_separation
#print axioms polygon_contact_unique
#print axioms polygon_boundary_eq_line
#print axioms life_polygon_contact_unique

end ExceptionalTimes.PairSquareSewing
