import ExceptionalTimes.UnitProjectionGadget
import ExceptionalTimes.HexCutTrimming

/-! The unit forcing pattern has a literal four-run hexagonal necklace.
This supplies actual separated alternating boundary runs for an ordinary
static four-arm attachment; the second free site lies strictly inside it. -/

open Set
open scoped Classical
namespace ExceptionalTimes.PairSquareSewing.UnitProjectionGadget
noncomputable section
open Annulus

def eastRun : triangularGraph.Walk (2,-2) (0,2) :=
  .cons (by norm_num [TriangularAdj] : TriangularAdj (2,-2) (2,-1))
    (.cons (by norm_num [TriangularAdj] : TriangularAdj (2,-1) (2,0))
      (.cons (by norm_num [TriangularAdj] : TriangularAdj (2,0) (1,1))
        (.cons (by norm_num [TriangularAdj] : TriangularAdj (1,1) (0,2)) .nil)))

def upperRun : triangularGraph.Walk (-1,2) (-2,1) :=
  .cons (by norm_num [TriangularAdj] : TriangularAdj (-1,2) (-2,2))
    (.cons (by norm_num [TriangularAdj] : TriangularAdj (-2,2) (-2,1)) .nil)

def lowerRun : triangularGraph.Walk (-1,-1) (1,-2) :=
  .cons (by norm_num [TriangularAdj] : TriangularAdj (-1,-1) (0,-2))
    (.cons (by norm_num [TriangularAdj] : TriangularAdj (0,-2) (1,-2)) .nil)

@[simp] theorem eastRun_support : eastRun.support=[(2,-2),(2,-1),(2,0),(1,1),(0,2)] := rfl
@[simp] theorem upperRun_support : upperRun.support=[(-1,2),(-2,2),(-2,1)] := rfl
@[simp] theorem lowerRun_support : lowerRun.support=[(-1,-1),(0,-2),(1,-2)] := rfl

def necklace : NecklaceShape where
  start := ![(2,-2),(-1,2),(-2,0),(-1,-1)]
  finish := ![(0,2),(-2,1),(-2,0),(1,-2)]
  run := Fin.cases eastRun (Fin.cases upperRun
    (Fin.cases .nil (Fin.cases lowerRun (fun i => Fin.elim0 i))))
  simple i := by
    fin_cases i
    · change eastRun.IsPath
      simp [SimpleGraph.Walk.isPath_def]
    · change upperRun.IsPath
      simp [SimpleGraph.Walk.isPath_def]
    · change (SimpleGraph.Walk.nil : triangularGraph.Walk (-2,0) (-2,0)).IsPath
      simp
    · change lowerRun.IsPath
      simp [SimpleGraph.Walk.isPath_def]
  disjoint i j hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change List.Disjoint [(2,-2),(2,-1),(2,0),(1,1),(0,2)] [(-1,2),(-2,2),(-2,1)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(2,-2),(2,-1),(2,0),(1,1),(0,2)] [(-2,0)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(2,-2),(2,-1),(2,0),(1,1),(0,2)] [(-1,-1),(0,-2),(1,-2)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-1,2),(-2,2),(-2,1)] [(2,-2),(2,-1),(2,0),(1,1),(0,2)]
      norm_num [List.disjoint_left]
    · exact (hij rfl).elim
    · change List.Disjoint [(-1,2),(-2,2),(-2,1)] [(-2,0)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-1,2),(-2,2),(-2,1)] [(-1,-1),(0,-2),(1,-2)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-2,0)] [(2,-2),(2,-1),(2,0),(1,1),(0,2)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-2,0)] [(-1,2),(-2,2),(-2,1)]
      norm_num [List.disjoint_left]
    · exact (hij rfl).elim
    · change List.Disjoint [(-2,0)] [(-1,-1),(0,-2),(1,-2)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-1,-1),(0,-2),(1,-2)] [(2,-2),(2,-1),(2,0),(1,1),(0,2)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-1,-1),(0,-2),(1,-2)] [(-1,2),(-2,2),(-2,1)]
      norm_num [List.disjoint_left]
    · change List.Disjoint [(-1,-1),(0,-2),(1,-2)] [(-2,0)]
      norm_num [List.disjoint_left]
    · exact (hij rfl).elim
  bridge i := by
    fin_cases i
    all_goals norm_num [TriangularAdj]

theorem necklace_vertices :
    necklace.vertices = {(2,-2),(2,-1),(2,0),(1,1),(0,2),(-1,2),(-2,2),(-2,1),
      (-2,0),(-1,-1),(0,-2),(1,-2)} := by
  ext v
  simp only [NecklaceShape.vertices,Finset.mem_biUnion,Finset.mem_univ,true_and,
    List.mem_toFinset,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  change (v∈[(2,-2),(2,-1),(2,0),(1,1),(0,2)] ∨ v∈[(-1,2),(-2,2),(-2,1)] ∨ v∈[(-2,0)] ∨ v∈[(-1,-1),(0,-2),(1,-2)]) ↔ _
  simp only [List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem necklace_mem_iff (v : Site) : v∈necklace.vertices↔hexRadius v=2 := by
  rw [necklace_vertices]
  rcases v with ⟨x,y⟩
  constructor
  · intro hv
    simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hv
    rcases hv with h|h|h|h|h|h|h|h|h|h|h|h
    all_goals rcases h with ⟨rfl,rfl⟩; norm_num [hexRadius]
  · intro h
    have hx : |x| ≤ 2 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h.le
    have hy : |y| ≤ 2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h.le
    obtain ⟨hxl,hxu⟩ := abs_le.mp hx
    obtain ⟨hyl,hyu⟩ := abs_le.mp hy
    interval_cases x <;> interval_cases y <;> norm_num [hexRadius] at *

theorem necklace_colored (a b : Bool) : necklace.Colored (colors a b) := by
  intro i v hv
  fin_cases i
  · change v ∈ [(2,-2),(2,-1),(2,0),(1,1),(0,2)] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl
    all_goals norm_num [colors,westRay]
  · change v ∈ [(-1,2),(-2,2),(-2,1)] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl
    all_goals norm_num [colors,westRay]
  · change v ∈ [(-2,0)] at hv
    have hv' : v=(-2,0) := by simpa using hv
    subst v
    norm_num [colors,westRay]
  · change v ∈ [(-1,-1),(0,-2),(1,-2)] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl
    all_goals norm_num [colors,westRay]

theorem mem_box_two_of_hex_le {v : Site} (hv : hexRadius v≤2) : v∈latticeBox 2 := by
  have hx : |v.1|≤2 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hv
  have hy : |v.2|≤2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hv
  simpa [latticeBox] using And.intro (abs_le.mp hx) (abs_le.mp hy)

theorem walk_avoiding_necklace_bound {u v : Site} (p : triangularGraph.Walk u v) :
    hexRadius u≤2 → (∀w∈p.support,w∉necklace.vertices) → hexRadius v≤2 := by
  induction p with
  | nil => intro hu _; exact hu
  | @cons u w v h p ih =>
    intro hu hp
    have hu' : hexRadius u≠2 := fun heq =>
      hp u (by simp) ((necklace_mem_iff u).mpr heq)
    have hw : hexRadius w≤2 := by
      have hstep := hexRadius_step h
      omega
    exact ih hw (fun z hz => hp z (List.mem_cons_of_mem _ hz))

theorem hex_le_mem_filled {v : Site} (hv : hexRadius v≤2) :
    v∈necklace.filled (latticeBox 2) := by
  refine Finset.mem_filter.mpr ⟨mem_box_two_of_hex_le hv,?_⟩
  rintro ⟨w,hw,p,hp⟩
  exact hw (mem_box_two_of_hex_le (walk_avoiding_necklace_bound p hv hp))

theorem necklace_join_true (b : Bool) :
    (necklace.joinQuad (latticeBox 2)).Crossing (colors true b) := by
  refine ⟨(2,0),?_,(-2,0),?_,openPath.reverse,?_⟩
  · change (2,0)∈([(2,-2),(2,-1),(2,0),(1,1),(0,2)] : List Site).toFinset
    simp
  · change (-2,0)∈([(-2,0)] : List Site).toFinset
    simp
  · intro w hw
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse] at hw
    change w∈[(-2,0),(-1,0),(0,0),(0,1),(1,1),(2,0)] at hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals constructor
    all_goals first | exact hex_le_mem_filled (by norm_num [hexRadius]) |
      norm_num [colors,westRay]

theorem necklace_not_join_false (b : Bool) :
    ¬(necklace.joinQuad (latticeBox 2)).Crossing (colors false b) := by
  rintro ⟨u,hu,v,hv,p,hp⟩
  change u∈([(2,-2),(2,-1),(2,0),(1,1),(0,2)] : List Site).toFinset at hu
  change v∈([(-2,0)] : List Site).toFinset at hv
  have hv' : v=(-2,0) := by simpa using hv
  subst v
  have huW := black_walk_preserves_westRay b p.reverse (by norm_num [westRay])
    (fun w hw => (hp w (by simpa using hw)).2)
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [westRay] at huW

theorem necklace_test_eq_first (a b : Bool) :
    (necklace.joinQuad (latticeBox 2)).test (colors a b)=a := by
  cases a <;> simp [GraphQuad.test,necklace_not_join_false,necklace_join_true]

theorem forced_necklace_test (ω : Configuration) (hω : Forced ω) (a b : Bool) :
    (necklace.joinQuad (latticeBox 2)).test (putPair ω (0,0) (1,0) a b)=a := by
  calc
    _=(necklace.joinQuad (latticeBox 2)).test (putPair (colors false false) (0,0) (1,0) a b) := by
      apply GraphQuad.test_congr
      intro w hw
      have hw2 : w∈latticeBox 2 := (Finset.mem_filter.mp hw).1
      have hw3 : w∈latticeBox 3 := by
        simp only [latticeBox] at hw2 ⊢
        norm_num at hw2 ⊢
        omega
      by_cases hw0 : w=(0,0)
      · subst w; simp [putPair]
      by_cases hw1 : w=(1,0)
      · subst w; simp [putPair]
      simpa [putPair,hw0,hw1] using hω w hw3 hw0 hw1
    _=a := by rw [putPair_colors,necklace_test_eq_first]

#print axioms necklace_vertices
#print axioms necklace_mem_iff
#print axioms necklace_colored
#print axioms forced_necklace_test
end
end ExceptionalTimes.PairSquareSewing.UnitProjectionGadget



