import ExceptionalTimes.HexRoundAnnulus
import ExceptionalTimes.PolygonalWalkPaths

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

open TriangularPlane

def axialForm (k : Fin 6) (p : ℝ × ℝ) : ℝ :=
  ![p.1,-p.1,p.2,-p.2,p.1+p.2,-(p.1+p.2)] k

def integerForm (k : Fin 6) (v : Site) : ℤ :=
  ![v.1,-v.1,v.2,-v.2,v.1+v.2,-(v.1+v.2)] k

theorem axialForm_point (k : Fin 6) (v : Site) :
    axialForm k (point v) = (integerForm k v : ℝ) := by
  fin_cases k <;> simp [axialForm,integerForm,point]

theorem axialForm_le_hexGauge (k : Fin 6) (p : ℝ × ℝ) : axialForm k p ≤ hexGauge p := by
  have hx : |p.1| ≤ hexGauge p := (le_max_left _ _).trans (le_max_left _ _)
  have hy : |p.2| ≤ hexGauge p := (le_max_right _ _).trans (le_max_left _ _)
  have hs : |p.1+p.2| ≤ hexGauge p := le_max_right _ _
  fin_cases k <;> norm_num [axialForm]
  all_goals linarith [le_abs_self p.1,neg_le_abs p.1,le_abs_self p.2,neg_le_abs p.2,
    le_abs_self (p.1+p.2),neg_le_abs (p.1+p.2)]

theorem hexGauge_le_iff (p : ℝ × ℝ) (a : ℝ) :
    hexGauge p ≤ a ↔ ∀ k, axialForm k p ≤ a := by
  constructor
  · exact fun h k => (axialForm_le_hexGauge k p).trans h
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [axialForm] at h0 h1 h2 h3 h4 h5
    simp only [hexGauge,max_le_iff,abs_le]
    constructor
    · constructor <;> constructor <;> linarith
    · constructor <;> linarith

theorem hexGauge_lt_iff (p : ℝ × ℝ) (a : ℝ) :
    hexGauge p < a ↔ ∀ k, axialForm k p < a := by
  constructor
  · exact fun h k => (axialForm_le_hexGauge k p).trans_lt h
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [axialForm] at h0 h1 h2 h3 h4 h5
    simp only [hexGauge,max_lt_iff,abs_lt]
    constructor
    · constructor <;> constructor <;> linarith
    · constructor <;> linarith

theorem integerForm_le_radius (k : Fin 6) (v : Site) : integerForm k v ≤ hexRadius v := by
  have h := axialForm_le_hexGauge k (point v)
  rw [axialForm_point] at h
  change (integerForm k v : ℝ) ≤ hexGauge ((v.1:ℝ),(v.2:ℝ)) at h
  rw [hexGauge_site] at h
  exact_mod_cast h

theorem hexRadius_lt_integerForm {r : ℤ} {v : Site} (h : r < hexRadius v) :
    ∃ k, r < integerForm k v := by
  by_contra hn
  push Not at hn
  have hb : hexGauge (point v) ≤ (r:ℝ) := (hexGauge_le_iff _ _).mpr (by
    intro k
    rw [axialForm_point]
    exact_mod_cast hn k)
  change hexGauge ((v.1:ℝ),(v.2:ℝ)) ≤ (r:ℝ) at hb
  rw [hexGauge_site] at hb
  have : hexRadius v ≤ r := by exact_mod_cast hb
  omega

theorem integerForm_step {u v : Site} (h : TriangularAdj u v) (k : Fin 6) :
    integerForm k v ≤ integerForm k u+1 := by
  unfold TriangularAdj at h
  fin_cases k <;> simp [integerForm] <;> omega

theorem axialForm_edgePoint (k : Fin 6) (u v : Site) (t : ℝ) :
    axialForm k (edgePoint u v t) =
      (1-t)*(integerForm k u : ℝ)+t*(integerForm k v : ℝ) := by
  fin_cases k <;> simp [axialForm,integerForm,edgePoint] <;> ring

/-- A lattice edge aimed strictly outside an integer hex level lies
strictly outside that polygon after its initial endpoint. This is the
discrete geometric fact needed to pass proper vertex paths to curves. -/
theorem edge_hexGauge_gt {u v : Site} (h : TriangularAdj u v) {r : ℤ}
    (hv : r < hexRadius v) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    (r:ℝ) < hexGauge (edgePoint u v t) := by
  obtain ⟨k,hk⟩ := hexRadius_lt_integerForm hv
  have hs := integerForm_step h k
  have hku : r ≤ integerForm k u := by omega
  have hku' : (r:ℝ) ≤ (integerForm k u : ℝ) := by exact_mod_cast hku
  have hkv' : (r:ℝ) < (integerForm k v : ℝ) := by exact_mod_cast hk
  have hform := axialForm_le_hexGauge k (edgePoint u v t)
  rw [axialForm_edgePoint] at hform
  nlinarith

theorem edge_hexGauge_le {u v : Site} {R : ℤ}
    (hu : hexRadius u ≤ R) (hv : hexRadius v ≤ R) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1) : hexGauge (edgePoint u v t) ≤ (R:ℝ) := by
  apply (hexGauge_le_iff _ _).mpr
  intro k
  rw [axialForm_edgePoint]
  have hku : (integerForm k u : ℝ) ≤ (R:ℝ) := by exact_mod_cast (integerForm_le_radius k u).trans hu
  have hkv : (integerForm k v : ℝ) ≤ (R:ℝ) := by exact_mod_cast (integerForm_le_radius k v).trans hv
  nlinarith

theorem edge_hexGauge_lt {u v : Site} {R : ℤ}
    (hu : hexRadius u ≤ R) (hv : hexRadius v < R) {t : ℝ}
    (ht : 0 < t) (ht' : t ≤ 1) : hexGauge (edgePoint u v t) < (R:ℝ) := by
  apply (hexGauge_lt_iff _ _).mpr
  intro k
  rw [axialForm_edgePoint]
  have hku : (integerForm k u : ℝ) ≤ (R:ℝ) := by exact_mod_cast (integerForm_le_radius k u).trans hu
  have hkv : (integerForm k v : ℝ) < (R:ℝ) := by exact_mod_cast (integerForm_le_radius k v).trans_lt hv
  nlinarith

#print axioms edge_hexGauge_gt
#print axioms edge_hexGauge_le
#print axioms edge_hexGauge_lt

theorem hexGauge_point (v : Site) : hexGauge (point v) = (hexRadius v : ℝ) := hexGauge_site v

theorem walkTrace_hexGauge_le {u v : Site} (p : triangularGraph.Walk u v) {R : ℤ}
    (h : ∀ z ∈ p.support, hexRadius z ≤ R) :
    ∀ q ∈ walkTrace p, hexGauge q ≤ (R:ℝ) := by
  intro q hq
  rcases walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ | ⟨x,hx,y,hy,_,t,ht0,ht1,rfl⟩
  · rw [hexGauge_point]
    exact_mod_cast h z hz
  · exact edge_hexGauge_le (h x hx) (h y hy) ht0 ht1

theorem walkTrace_hexGauge_gt_of_proper {u v : Site} (p : triangularGraph.Walk u v) {r : ℤ}
    (h : ∀ z ∈ p.support, r ≤ hexRadius z)
    (hproper : ∀ z ∈ p.support, hexRadius z = r → z = u) :
    ∀ q ∈ walkTrace p, q ≠ point u → (r:ℝ) < hexGauge q := by
  have hsite (z : Site) (hz : z ∈ p.support) (hzu : z ≠ u) : r < hexRadius z := by
    have hle := h z hz
    have hne : hexRadius z ≠ r := fun he => hzu (hproper z hz he)
    omega
  intro q hq hqu
  rcases walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ | ⟨x,hx,y,hy,hxy,t,ht0,ht1,rfl⟩
  · rw [hexGauge_point]
    exact_mod_cast hsite z hz (fun he => hqu (congrArg point he))
  · by_cases ht : t = 0
    · subst t
      rw [edgePoint_zero,hexGauge_point]
      exact_mod_cast hsite x hx (fun he => hqu (by simp [he]))
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    by_cases hyu : y ≠ u
    · exact edge_hexGauge_gt hxy (hsite y hy hyu) htpos ht1
    · have hyu' : y = u := not_not.mp hyu
      have hxu : x ≠ u := by
        intro hxu
        exact triangularAdj_irrefl u (by simpa [hxu,hyu'] using hxy)
      have htlt : t < 1 := by
        by_contra hlt
        have ht' : t = 1 := by linarith
        exact hqu (by simp [ht',hyu'])
      have hg := edge_hexGauge_gt (triangularAdj_symm hxy) (hsite x hx hxu)
        (by linarith : 0 < 1-t) (by linarith : 1-t ≤ 1)
      simpa only [edgePoint_reverse] using hg

theorem walkTrace_hexGauge_lt_of_proper {u v : Site} (p : triangularGraph.Walk u v) {R : ℤ}
    (h : ∀ z ∈ p.support, hexRadius z ≤ R)
    (hproper : ∀ z ∈ p.support, hexRadius z = R → z = v) :
    ∀ q ∈ walkTrace p, q ≠ point v → hexGauge q < (R:ℝ) := by
  have hsite (z : Site) (hz : z ∈ p.support) (hzv : z ≠ v) : hexRadius z < R := by
    have hle := h z hz
    have hne : hexRadius z ≠ R := fun he => hzv (hproper z hz he)
    omega
  intro q hq hqv
  rcases walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ | ⟨x,hx,y,hy,hxy,t,ht0,ht1,rfl⟩
  · rw [hexGauge_point]
    exact_mod_cast hsite z hz (fun he => hqv (congrArg point he))
  · by_cases ht : t = 0
    · subst t
      rw [edgePoint_zero,hexGauge_point]
      exact_mod_cast hsite x hx (fun he => hqv (by simp [he]))
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    by_cases hyv : y ≠ v
    · exact edge_hexGauge_lt (h x hx) (hsite y hy hyv) htpos ht1
    · have hyv' : y = v := not_not.mp hyv
      have hxv : x ≠ v := by
        intro hxv
        exact triangularAdj_irrefl v (by simpa [hxv,hyv'] using hxy)
      have htlt : t < 1 := by
        by_contra hlt
        have ht' : t = 1 := by linarith
        exact hqv (by simp [ht',hyv'])
      have hg := edge_hexGauge_lt (h y hy) (hsite x hx hxv)
        (by linarith : 0 < 1-t) (by linarith : 1-t ≤ 1)
      simpa only [edgePoint_reverse] using hg

theorem walkTrace_subset_hexAnnulus {u v : Site} (p : triangularGraph.Walk u v) {r R : ℤ}
    (hu : hexRadius u = r)
    (h : ∀ z ∈ p.support, r ≤ hexRadius z ∧ hexRadius z ≤ R)
    (hin : ∀ z ∈ p.support, hexRadius z = r → z = u) :
    walkTrace p ⊆ hexAnnulus r R := by
  intro q hq
  constructor
  · by_cases hqu : q = point u
    · rw [hqu,hexGauge_point,hu]
    · exact (walkTrace_hexGauge_gt_of_proper p (fun z hz => (h z hz).1) hin q hq hqu).le
  · exact walkTrace_hexGauge_le p (fun z hz => (h z hz).2) q hq

/-- Proper simple lattice paths produce injective continuous curves in
the actual polygon annulus, meeting each boundary only at its prescribed
endpoint. This includes all edge interiors, not just lattice vertices. -/
theorem walkPath_proper_hexAnnulus {u v : Site} (p : triangularGraph.Walk u v) {r R : ℤ}
    (hrR : r < R) (hp : p.IsPath) (hu : hexRadius u = r) (hv : hexRadius v = R)
    (h : ∀ z ∈ p.support, r ≤ hexRadius z ∧ hexRadius z ≤ R)
    (hin : ∀ z ∈ p.support, hexRadius z = r → z = u)
    (hout : ∀ z ∈ p.support, hexRadius z = R → z = v) :
    Function.Injective (walkPath p) ∧
      (∀ t, walkPath p t ∈ hexAnnulus r R) ∧
      (∀ t : unitInterval, 0 < (t:ℝ) → (t:ℝ) < 1 →
        (r:ℝ) < hexGauge (walkPath p t) ∧ hexGauge (walkPath p t) < (R:ℝ)) := by
  have hne : u ≠ v := by intro he; subst v; omega
  have hj := walkPath_injective p hp (SimpleGraph.Walk.not_nil_of_ne hne)
  have hrange (t : unitInterval) : walkPath p t ∈ walkTrace p :=
    (Set.ext_iff.mp (walkPath_range p) _).mp ⟨t,rfl⟩
  refine ⟨hj,fun t => walkTrace_subset_hexAnnulus p hu h hin (hrange t),?_⟩
  intro t ht0 ht1
  have hstart : walkPath p t ≠ point u := by
    intro he
    have he' := congrArg Subtype.val (hj (he.trans (walkPath p).source.symm))
    dsimp at he'
    linarith
  have hend : walkPath p t ≠ point v := by
    intro he
    have he' := congrArg Subtype.val (hj (he.trans (walkPath p).target.symm))
    dsimp at he'
    linarith
  exact ⟨walkTrace_hexGauge_gt_of_proper p (fun z hz => (h z hz).1) hin _ (hrange t) hstart,
    walkTrace_hexGauge_lt_of_proper p (fun z hz => (h z hz).2) hout _ (hrange t) hend⟩

#print axioms walkPath_proper_hexAnnulus

end ExceptionalTimes.Annulus
