import ExceptionalTimes.ArmEvents
import ExceptionalTimes.NecklacePlaneAnnotations

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus

theorem hexRadius_step {u v : Site} (h : TriangularAdj u v) :
    hexRadius v ≤ hexRadius u + 1 := by
  have hx : |u.1| ≤ hexRadius u := (le_max_left _ _).trans (le_max_left _ _)
  have hy : |u.2| ≤ hexRadius u := (le_max_right _ _).trans (le_max_left _ _)
  have hs : |u.1+u.2| ≤ hexRadius u := le_max_right _ _
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hs' := abs_le.mp hs
  unfold hexRadius
  rw [max_le_iff,max_le_iff]
  have hvx : |v.1| ≤ hexRadius u + 1 := by
    rw [abs_le]
    unfold TriangularAdj at h
    omega
  have hvy : |v.2| ≤ hexRadius u + 1 := by
    rw [abs_le]
    unfold TriangularAdj at h
    omega
  have hvs : |v.1+v.2| ≤ hexRadius u + 1 := by
    rw [abs_le]
    unfold TriangularAdj at h
    omega
  exact ⟨⟨hvx,hvy⟩,hvs⟩

theorem triangularAdj_translate_sub {u v c : Site} (h : TriangularAdj u v) :
    TriangularAdj (u-c) (v-c) := by
  rcases u with ⟨ux,uy⟩
  rcases v with ⟨vx,vy⟩
  rcases c with ⟨cx,cy⟩
  simp only [Prod.fst_sub,Prod.snd_sub,TriangularAdj] at h ⊢
  omega

theorem centered_hexRadius_step (c : Site) {u v : Site} (h : TriangularAdj u v) :
    hexRadius (v-c) ≤ hexRadius (u-c) + 1 := hexRadius_step (triangularAdj_translate_sub h)

theorem walk_start_level (f : Site → ℤ)
    (hstep : ∀ {u v}, TriangularAdj u v → f v ≤ f u + 1)
    {u v : Site} (p : triangularGraph.Walk u v) (hnil : ¬p.Nil) (k : ℤ)
    (hu : f u ≤ k) (hproper : ∀ z ∈ p.support, f z ≤ k → z = u) : f u = k := by
  cases p with
  | nil => exact False.elim (hnil (by simp))
  | @cons u w v huw p =>
    have hw : w ∈ (SimpleGraph.Walk.cons huw p).support :=
      List.mem_cons_of_mem _ p.start_mem_support
    have hnot : ¬ f w ≤ k := by
      intro h
      have heq := hproper w hw h
      exact triangularAdj_irrefl u (heq ▸ huw)
    have hbound := hstep huw
    omega

/-- Last departure from the inner sublevel and first arrival in the
outer superlevel yield exact integer-level endpoints and a proper path.
The retained walk is a subwalk, so all original colors and disjointness
are preserved. No topological ordering assumption is hidden here. -/
theorem trim_path_integer_levels (f : Site → ℤ)
    (hstep : ∀ {u v}, TriangularAdj u v → f v ≤ f u + 1)
    (r R : ℤ) (hrR : r < R) {u v : Site} (p : triangularGraph.Walk u v)
    (hp : p.IsPath) (hu : f u ≤ r) (hv : R ≤ f v) :
    ∃ x, f x = r ∧ ∃ y, f y = R ∧ ∃ q : triangularGraph.Walk x y,
      q.IsPath ∧ q.IsSubwalk p ∧
      (∀ z ∈ q.support, r ≤ f z ∧ f z ≤ R) ∧
      (∀ z ∈ q.support, f z = r → z = x) ∧
      (∀ z ∈ q.support, f z = R → z = y) := by
  obtain ⟨x,hx,y,hy,q,hq,hsub,hinner,houter⟩ :=
    trim_path_between_sets {z | f z ≤ r} {z | R ≤ f z} p hp hu hv
  have hxy : x ≠ y := by
    intro h
    change f x ≤ r at hx
    change R ≤ f y at hy
    rw [h] at hx
    omega
  have hnil : ¬ q.Nil := fun h => hxy h.eq
  have hx' : f x = r := walk_start_level f hstep q hnil r hx hinner
  have hneg : ∀ {a b : Site}, TriangularAdj a b → -f b ≤ -f a + 1 := by
    intro a b hab
    have h := hstep (triangularAdj_symm hab)
    omega
  have hrevnil : ¬q.reverse.Nil := by
    intro h
    exact hxy h.eq.symm
  have hy' : f y = R := by
    have h := walk_start_level (fun z => -f z) hneg q.reverse hrevnil (-R) (by exact neg_le_neg hy)
      (by
        intro z hz hzr
        rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hz
        exact houter z hz (by change R ≤ f z; omega))
    omega
  refine ⟨x,hx',y,hy',q,hq,hsub,?_,?_,?_⟩
  · intro z hz
    constructor
    · by_cases hzr : f z ≤ r
      · have hzx := hinner z hz hzr
        rw [hzx,hx']
      · omega
    · by_cases hzR : R ≤ f z
      · have hzy := houter z hz hzR
        rw [hzy,hy']
      · omega
  · intro z hz hzr
    exact hinner z hz hzr.le
  · intro z hz hzR
    exact houter z hz hzR.ge

theorem trim_path_hex_levels (c : Site) (r R : ℤ) (hrR : r < R)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (hu : hexRadius (u-c) ≤ r) (hv : R ≤ hexRadius (v-c)) :
    ∃ x, hexRadius (x-c) = r ∧ ∃ y, hexRadius (y-c) = R ∧ ∃ q : triangularGraph.Walk x y,
      q.IsPath ∧ q.IsSubwalk p ∧
      (∀ z ∈ q.support, r ≤ hexRadius (z-c) ∧ hexRadius (z-c) ≤ R) ∧
      (∀ z ∈ q.support, hexRadius (z-c) = r → z = x) ∧
      (∀ z ∈ q.support, hexRadius (z-c) = R → z = y) :=
  trim_path_integer_levels (fun z => hexRadius (z-c)) (centered_hexRadius_step c) r R hrR p hp hu hv

theorem hexRadius_norm_comparison (v : Site) :
    (hexRadius v : ℝ) ≤ 4*‖triangularEmbedding v‖ ∧
      ‖triangularEmbedding v‖ ≤ 2*(hexRadius v : ℝ) := by
  obtain ⟨hx,hy⟩ := triangularEmbedding_coordinate_bounds v
  constructor
  · simp only [hexRadius,Int.cast_max,Int.cast_abs,Int.cast_add,max_le_iff]
    exact ⟨⟨by linarith [norm_nonneg (triangularEmbedding v)],
      by linarith [norm_nonneg (triangularEmbedding v)]⟩,
      (abs_add_le _ _).trans (by linarith)⟩
  · have hvx : |(v.1 : ℝ)| ≤ (hexRadius v : ℝ) := by
      exact_mod_cast (show |v.1| ≤ hexRadius v from (le_max_left _ _).trans (le_max_left _ _))
    have hvy : |(v.2 : ℝ)| ≤ (hexRadius v : ℝ) := by
      exact_mod_cast (show |v.2| ≤ hexRadius v from (le_max_right _ _).trans (le_max_left _ _))
    linarith [triangularEmbedding_norm_le_coordinates v]

theorem Probe.radius_eq_mesh_norm (P : Probe) (v : Site) :
    P.radius v = P.mesh * ‖triangularEmbedding (v-P.center)‖ := by
  rw [Probe.radius,position,position,Complex.dist_eq,← mul_sub,← triangularEmbedding_sub,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.mesh_pos]

theorem Probe.hexRadius_comparison (P : Probe) (v : Site) :
    P.mesh*(hexRadius (v-P.center) : ℝ) ≤ 4*P.radius v ∧
      P.radius v ≤ 2*P.mesh*(hexRadius (v-P.center) : ℝ) := by
  obtain ⟨hleft,hright⟩ := hexRadius_norm_comparison (v-P.center)
  rw [P.radius_eq_mesh_norm]
  constructor <;> nlinarith [P.mesh_pos]

/-- Explicit fixed-factor margins transfer a circular probe to exact
proper paths between deterministic hex-radius levels. This theorem keeps
colors and pairwise disjointness. Identifying the level sets as ordered
simple graph cycles is a separate obligation before using source 6.6. -/
theorem fourArms_proper_hex_paths (P : Probe) (ω : Configuration) (r R : ℤ)
    (hrR : r < R) (hr : 4*P.innerRadius ≤ P.mesh*(r : ℝ))
    (hR : 2*P.mesh*(R : ℝ) ≤ P.outerRadius) (ha : FourArms P ω) :
    ∃ s t : Fin 4 → Site, ∃ q : ∀ i, triangularGraph.Walk (s i) (t i),
      (∀ i, (q i).IsPath) ∧
      (∀ i, hexRadius (s i-P.center) = r ∧ hexRadius (t i-P.center) = R) ∧
      (∀ i z, z ∈ (q i).support →
        r ≤ hexRadius (z-P.center) ∧ hexRadius (z-P.center) ≤ R ∧
          ω z = decide (i.val % 2 = 0)) ∧
      (∀ i z, z ∈ (q i).support → hexRadius (z-P.center) = r → z = s i) ∧
      (∀ i z, z ∈ (q i).support → hexRadius (z-P.center) = R → z = t i) ∧
      (∀ i j, i ≠ j → List.Disjoint (q i).support (q j).support) := by
  obtain ⟨a,b,p,hp,hstart,hfinish,hcolor,hdis,_⟩ := ha
  have hcut (i : Fin 4) :
      hexRadius (a i-P.center) ≤ r ∧ R ≤ hexRadius (b i-P.center) := by
    have hleft := (P.hexRadius_comparison (a i)).1
    have hright := (P.hexRadius_comparison (b i)).2
    have hstart' := hstart i
    have hfinish' := hfinish i
    constructor
    · have h : (hexRadius (a i-P.center) : ℝ) ≤ (r : ℝ) := by nlinarith [P.mesh_pos]
      exact_mod_cast h
    · have h : (R : ℝ) ≤ (hexRadius (b i-P.center) : ℝ) := by nlinarith [P.mesh_pos]
      exact_mod_cast h
  have htrim (i : Fin 4) := trim_path_hex_levels P.center r R hrR (p i) (hp i)
    (hcut i).1 (hcut i).2
  choose s hs t ht q hq hsub hbounds hin hout using htrim
  refine ⟨s,t,q,hq,fun i => ⟨hs i,ht i⟩,?_,hin,hout,?_⟩
  · intro i z hz
    exact ⟨(hbounds i z hz).1,(hbounds i z hz).2,
      (hcolor i z ((hsub i).support_subset hz)).2⟩
  · intro i j hij z hzi hzj
    exact hdis i j hij ((hsub i).support_subset hzi) ((hsub j).support_subset hzj)

#print axioms centered_hexRadius_step
#print axioms trim_path_hex_levels
#print axioms Probe.hexRadius_comparison
#print axioms fourArms_proper_hex_paths

end ExceptionalTimes.PairSquareSewing
