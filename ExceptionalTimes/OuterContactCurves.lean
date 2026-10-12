import ExceptionalTimes.PolygonalWalkPaths
import ExceptionalTimes.MixedHexAnnulus

open Set
open scoped Classical unitInterval

namespace ExceptionalTimes.TriangularPlane

def partialEdgePath (u v : Site) (t : ℝ) : Path (point u) (edgePoint u v t) where
  toFun s := edgePoint u v (t*(s:ℝ))
  continuous_toFun := (edgePoint_continuous u v).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

theorem partialEdgePath_injective {u v : Site} (h : TriangularAdj u v) {t : ℝ} (ht : 0 < t) :
    Function.Injective (partialEdgePath u v t) := by
  intro a b hab
  have he := edgePoint_injective h hab
  apply Subtype.ext
  exact (mul_left_cancel₀ ht.ne' he)

noncomputable def walkToContact {w v : Site} (t : ℝ) :
    {u : Site} → triangularGraph.Walk u w → Path (point u) (edgePoint w v t)
  | _,.nil => partialEdgePath w v t
  | a,@SimpleGraph.Walk.cons _ _ _ b _ _ p =>
      (edgePath a b).trans (walkToContact t p)

theorem partialEdgePath_range {u v : Site} {t : ℝ} (ht : 0 < t) :
    Set.range (partialEdgePath u v t) = {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ t ∧ z = edgePoint u v s} := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨t*(s:ℝ),mul_nonneg ht.le s.2.1,?_,rfl⟩
    nlinarith [s.2.2]
  · rintro ⟨s,hs0,hst,rfl⟩
    have hdiv : s/t ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg hs0 ht.le,(div_le_one ht).mpr hst⟩
    refine ⟨⟨s/t,hdiv⟩,?_⟩
    change edgePoint u v (t*(s/t)) = edgePoint u v s
    rw [mul_div_cancel₀ _ ht.ne']

theorem walkToContact_range {u w v : Site} (p : triangularGraph.Walk u w)
    {t : ℝ} (ht : 0 < t) :
    Set.range (walkToContact (v := v) t p) =
      walkTrace p ∪ {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ t ∧ z = edgePoint w v s} := by
  induction p with
  | @nil a =>
    change Set.range (partialEdgePath a v t) = _
    rw [partialEdgePath_range ht]
    change _ = {point a} ∪ _
    symm
    apply Set.union_eq_right.mpr
    rintro z rfl
    exact ⟨0,le_rfl,ht.le,(edgePoint_zero a v).symm⟩
  | @cons a b w hab p ih =>
    change Set.range ((edgePath a b).trans (walkToContact t p)) = _
    rw [Path.trans_range,edgePath_range,ih]
    change _ = (_ ∪ _) ∪ _
    exact (Set.union_assoc _ _ _).symm

theorem walkToContact_range_subset {u w v : Site} (p : triangularGraph.Walk u w)
    (last : triangularGraph.Adj w v) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) :
    Set.range (walkToContact (v := v) t p) ⊆ walkTrace (p.concat last) := by
  induction p with
  | nil =>
    intro z hz
    rcases (Set.ext_iff.mp (partialEdgePath_range ht) z).mp hz with ⟨s,hs0,hst,he⟩
    exact Or.inl ⟨s,hs0,hst.trans ht',he⟩
  | @cons a b w hab p ih =>
    intro z hz
    rw [walkToContact,Path.trans_range] at hz
    rcases hz with hz | hz
    · exact Or.inl ((Set.ext_iff.mp (edgePath_range a b) z).mp hz)
    · exact Or.inr (ih last hz)

theorem walkToContact_injective {u w v : Site} (p : triangularGraph.Walk u w)
    (last : triangularGraph.Adj w v) (hp : (p.concat last).IsPath)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) : Function.Injective (walkToContact (v := v) t p) := by
  induction p with
  | nil => exact partialEdgePath_injective last ht
  | @cons a b w hab p ih =>
    have hp' : (SimpleGraph.Walk.cons hab (p.concat last)).IsPath := hp
    have ha : a ∉ (p.concat last).support := (List.nodup_cons.mp hp'.support_nodup).1
    apply path_trans_injective _ _ (edgePath_injective hab) (ih last hp'.of_cons)
    intro z hze hzt
    have hsingle : z ∈ walkTrace (SimpleGraph.Walk.cons hab (.nil : triangularGraph.Walk b b)) :=
      Or.inl ((Set.ext_iff.mp (edgePath_range a b) z).mp hze)
    have htail := walkToContact_range_subset p last ht ht' hzt
    apply walkTrace_intersection_only _ _ ?_ hsingle htail
    intro x hx hxp
    simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,List.mem_cons,
      List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact False.elim (ha hxp)
    · rfl

#print axioms walkToContact_range
#print axioms walkToContact_injective

theorem planeMap_add (p q : ℝ × ℝ) :
    HexTiling.planeMap (p+q) = HexTiling.planeMap p+HexTiling.planeMap q := by
  apply Complex.ext <;> simp [HexTiling.planeMap] <;> ring

theorem edgePoint_affine (u v : Site) (t : ℝ) :
    edgePoint u v t = (1-t) • point u+t • point v := by
  ext <;> simp [edgePoint,point] <;> ring

theorem partial_edgePoint_affine (u v : Site) (t a : ℝ) :
    edgePoint u v (t*a) = (1-a) • point u+a • edgePoint u v t := by
  ext <;> simp [edgePoint,point] <;> ring

theorem norm_planeMap_affine_le (p q : ℝ × ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖HexTiling.planeMap ((1-t) • p+t • q)‖ ≤
      (1-t)*‖HexTiling.planeMap p‖+t*‖HexTiling.planeMap q‖ := by
  rw [planeMap_add,Annulus.planeMap_smul,Annulus.planeMap_smul]
  have h := norm_add_le ((1-t) • HexTiling.planeMap p) (t • HexTiling.planeMap q)
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht0] using h

theorem walkTrace_norm_lt {u v : Site} (p : triangularGraph.Walk u v) (S : ℝ)
    (h : ∀ z ∈ p.support, ‖HexTiling.planeMap (point z)‖ < S) :
    ∀ q ∈ walkTrace p, ‖HexTiling.planeMap q‖ < S := by
  intro q hq
  rcases walkTrace_point_or_edge p hq with ⟨z,hz,rfl⟩ | ⟨x,hx,y,hy,_,t,ht0,ht1,rfl⟩
  · exact h z hz
  · rw [edgePoint_affine]
    have hconv := norm_planeMap_affine_le (point x) (point y) ht0 ht1
    have hx' := h x hx
    have hy' := h y hy
    have hxle := le_max_left ‖HexTiling.planeMap (point x)‖ ‖HexTiling.planeMap (point y)‖
    have hyle := le_max_right ‖HexTiling.planeMap (point x)‖ ‖HexTiling.planeMap (point y)‖
    have hmax : max ‖HexTiling.planeMap (point x)‖ ‖HexTiling.planeMap (point y)‖ < S := max_lt hx' hy'
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hxle),
      mul_nonneg ht0 (sub_nonneg.mpr hyle)]

/-- A partial terminal edge ends exactly at the first circle contact.
All earlier points lie strictly inside the circle by convexity. -/
theorem walkToContact_norm_lt {u w v : Site} (p : triangularGraph.Walk u w)
    (S : ℝ) {t : ℝ} (ht : 0 < t)
    (hin : ∀ z ∈ p.support, ‖HexTiling.planeMap (point z)‖ < S)
    (hend : ‖HexTiling.planeMap (edgePoint w v t)‖ = S) :
    ∀ q ∈ Set.range (walkToContact (v := v) t p), q ≠ edgePoint w v t →
      ‖HexTiling.planeMap q‖ < S := by
  intro q hq hne
  rw [walkToContact_range p ht] at hq
  rcases hq with hq | ⟨s,hs0,hst,rfl⟩
  · exact walkTrace_norm_lt p S hin q hq
  · have hst' : s < t := lt_of_le_of_ne hst (by intro he; exact hne (he ▸ rfl))
    have ha0 : 0 ≤ s/t := div_nonneg hs0 ht.le
    have ha1 : s/t < 1 := (div_lt_one ht).mpr hst'
    have hconv := norm_planeMap_affine_le (point w) (edgePoint w v t) ha0 ha1.le
    rw [←partial_edgePoint_affine] at hconv
    have hts : t*(s/t) = s := by field_simp
    rw [hts,hend] at hconv
    have hw := hin w p.end_mem_support
    nlinarith

theorem walkToContact_norm_le {u w v : Site} (p : triangularGraph.Walk u w)
    (S : ℝ) {t : ℝ} (ht : 0 < t)
    (hin : ∀ z ∈ p.support, ‖HexTiling.planeMap (point z)‖ < S)
    (hend : ‖HexTiling.planeMap (edgePoint w v t)‖ = S) :
    ∀ q ∈ Set.range (walkToContact (v := v) t p), ‖HexTiling.planeMap q‖ ≤ S := by
  intro q hq
  by_cases he : q = edgePoint w v t
  · rw [he,hend]
  · exact (walkToContact_norm_lt p S ht hin hend q hq he).le

#print axioms walkToContact_norm_lt
#print axioms walkToContact_norm_le

end ExceptionalTimes.TriangularPlane

