import ExceptionalTimes.StraightBoxCells
import ExceptionalTimes.ForestArmProbability

/-! Numerical one-side geometry for the straight rectangle. Root separation
from its four genuine corners excludes two incident sides; an explicit scale
restriction excludes opposite sides. -/

open Set

namespace ExceptionalTimes.PairSquareSewing

open HexTiling

theorem planeMap_coordinate_sharp (p : ℝ × ℝ) :
    |p.1| ≤ (3/2:ℝ)*‖planeMap p‖ ∧ |p.2| ≤ (3/2:ℝ)*‖planeMap p‖ := by
  have h := planeMap_normSq p
  rw [Complex.normSq_eq_norm_sq] at h
  constructor
  · nlinarith [sq_nonneg (p.1+2*p.2),sq_abs p.1,norm_nonneg (planeMap p),abs_nonneg p.1]
  · nlinarith [sq_nonneg (2*p.1+p.2),sq_abs p.2,norm_nonneg (planeMap p),abs_nonneg p.2]

noncomputable def axialPhysical (ε : ℝ) (p : ℝ × ℝ) : ℂ := (ε:ℂ)*planeMap p

theorem axialPhysical_dist {ε : ℝ} (hε : 0 ≤ ε) (p q : ℝ × ℝ) :
    dist (axialPhysical ε p) (axialPhysical ε q) = ε*‖planeMap (p-q)‖ := by
  rw [axialPhysical, axialPhysical, dist_eq_norm, ← mul_sub, ← planeMap_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]

theorem physical_coordinate_le {ε : ℝ} (hε : 0 ≤ ε) (p q : ℝ × ℝ) :
    ε*|p.1-q.1| ≤ (3/2:ℝ)*dist (axialPhysical ε p) (axialPhysical ε q) ∧
      ε*|p.2-q.2| ≤ (3/2:ℝ)*dist (axialPhysical ε p) (axialPhysical ε q) := by
  rw [axialPhysical_dist hε]
  have h := planeMap_coordinate_sharp (p-q)
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 hε
    convert hh using 1
    ring
  · have hh := mul_le_mul_of_nonneg_left h.2 hε
    convert hh using 1
    ring

def NearVertical (ε : ℝ) (c : ℝ × ℝ) (x R : ℝ) : Prop :=
  ∃ p : ℝ × ℝ, p.1=x ∧ dist (axialPhysical ε c) (axialPhysical ε p) ≤ R

def NearHorizontal (ε : ℝ) (c : ℝ × ℝ) (y R : ℝ) : Prop :=
  ∃ p : ℝ × ℝ, p.2=y ∧ dist (axialPhysical ε c) (axialPhysical ε p) ≤ R

theorem nearVertical_coordinate {ε R x : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε)
    (h : NearVertical ε c x R) : ε*|c.1-x| ≤ (3/2:ℝ)*R := by
  obtain ⟨p,hp,hR⟩ := h
  have hh := (physical_coordinate_le hε c p).1
  rw [hp] at hh
  linarith

theorem nearHorizontal_coordinate {ε R y : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε)
    (h : NearHorizontal ε c y R) : ε*|c.2-y| ≤ (3/2:ℝ)*R := by
  obtain ⟨p,hp,hR⟩ := h
  have hh := (physical_coordinate_le hε c p).2
  rw [hp] at hh
  linarith

/-- Seeing two incident supporting lines forces the center near their true
corner. The constant 3 is smaller than the forest's separation ratio 8/2. -/
theorem near_incident_corner {ε R x y : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε)
    (hx : NearVertical ε c x R) (hy : NearHorizontal ε c y R) :
    dist (axialPhysical ε c) (axialPhysical ε (x,y)) ≤ 3*R := by
  rw [axialPhysical_dist hε]
  have h := mul_le_mul_of_nonneg_left (planeMap_norm_le_coordinates (c-(x,y))) hε
  have hx' := nearVertical_coordinate hε hx
  have hy' := nearHorizontal_coordinate hε hy
  change ε*‖planeMap (c-(x,y))‖ ≤ _
  dsimp only [Prod.fst_sub, Prod.snd_sub] at h
  nlinarith

theorem near_opposite_vertical {ε R n : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε)
    (hx : NearVertical ε c (-n) R) (hy : NearVertical ε c n R) : 2*ε*n ≤ 3*R := by
  have hx' := nearVertical_coordinate hε hx
  have hy' := nearVertical_coordinate hε hy
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self (c.1+n)) hε
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (c.1-n)) hε
  simp only [sub_neg_eq_add] at hx'
  nlinarith

theorem near_opposite_horizontal {ε R n : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε)
    (hx : NearHorizontal ε c (-n) R) (hy : NearHorizontal ε c n R) : 2*ε*n ≤ 3*R := by
  have hx' := nearHorizontal_coordinate hε hx
  have hy' := nearHorizontal_coordinate hε hy
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self (c.2+n)) hε
  have h2 := mul_le_mul_of_nonneg_left (neg_le_abs (c.2-n)) hε
  simp only [sub_neg_eq_add] at hx'
  nlinarith

def signedSide (n : ℝ) (positive : Bool) : ℝ := if positive then n else -n

/-- First Boolean selects horizontal/vertical, second selects positive/negative. -/
def SideContact (ε n R : ℝ) (c : ℝ × ℝ) (side : Bool × Bool) : Prop :=
  if side.1 then NearHorizontal ε c (signedSide n side.2) (2*R)
  else NearVertical ε c (signedSide n side.2) (2*R)

/-- This is the exact one-straight-side conclusion needed by a forest probe.
The corner distances are the genuine four-corner root distances. -/
theorem sideContact_unique {ε n R : ℝ} {c : ℝ × ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (hsize : 3*R < ε*n)
    (hcorners : ∀ s t : Bool, 8*R ≤ dist (axialPhysical ε c)
      (axialPhysical ε (signedSide n s,signedSide n t)))
    {a b : Bool × Bool} (ha : SideContact ε n R c a) (hb : SideContact ε n R c b) : a=b := by
  have hVV : ¬ (NearVertical ε c (-n) (2*R) ∧ NearVertical ε c n (2*R)) := by
    intro h
    have hh := near_opposite_vertical hε h.1 h.2
    linarith
  have hHH : ¬ (NearHorizontal ε c (-n) (2*R) ∧ NearHorizontal ε c n (2*R)) := by
    intro h
    have hh := near_opposite_horizontal hε h.1 h.2
    linarith
  have hVH (s t : Bool) : ¬ (NearVertical ε c (signedSide n s) (2*R) ∧
      NearHorizontal ε c (signedSide n t) (2*R)) := by
    intro h
    have hh := near_incident_corner hε h.1 h.2
    have hc := hcorners s t
    linarith
  have h00 := hVH false false
  have h01 := hVH false true
  have h10 := hVH true false
  have h11 := hVH true true
  obtain ⟨a₁,a₂⟩ := a
  obtain ⟨b₁,b₂⟩ := b
  cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    simp_all [SideContact,signedSide]

/-- Specialization to an actual positive forest life. The corner clearance
is derived from the real root separation, rather than required separately. -/
theorem life_sideContact_unique {V : Type*} [Fintype V]
    (fixed : V → Prop) (anchor : V → ℂ) {cutoff stop ε n : ℝ}
    (hcut : 0 < cutoff) (hε : 0 ≤ ε) (hscale : 3*(stop/8) < ε*n)
    (corner : Bool → Bool → V) (hfixed : ∀ s t, fixed (corner s t))
    (hcorner : ∀ s t, anchor (corner s t) = axialPhysical ε (signedSide n s,signedSide n t))
    (a : ForestArmProbability.Life fixed anchor cutoff stop) (c : ℝ × ℝ)
    (hcenter : anchor (ForestArmProbability.center fixed anchor cutoff stop a) = axialPhysical ε c)
    {s t : Bool × Bool}
    (hs : SideContact ε n (KruskalLives.death fixed anchor cutoff stop a.val/8) c s)
    (ht : SideContact ε n (KruskalLives.death fixed anchor cutoff stop a.val/8) c t) : s=t := by
  have h := ForestTelescope.positiveLives_spec fixed anchor cutoff stop a.property
  have hu := hcut.trans_le (KruskalLives.cutoff_le_birth h.1)
  have hv := hu.trans h.2.2
  have hstop := KruskalLives.death_le_stop h.1
  apply sideContact_unique hε (by positivity) (by linarith) _ hs ht
  intro i j
  have hc := ForestArmProbability.center_mem fixed anchor cutoff stop a
  have hout : corner i j ∉ a.val := fun hin => h.2.1 _ hin (hfixed i j)
  have hd := KruskalLives.life_external_distance h.1 h.2.2 hc hout
  rw [hcenter,hcorner] at hd
  linarith

#print axioms sideContact_unique
#print axioms life_sideContact_unique

end ExceptionalTimes.PairSquareSewing
