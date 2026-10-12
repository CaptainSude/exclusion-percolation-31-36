import ExceptionalTimes.NecklaceDictionary

/-! A deterministic unit-displacement forcing gadget. The free vertices are
u=(0,0), v=(1,0). All other sites are black precisely in the positive
Euclidean east half-plane or on the negative horizontal axis. The west-east
join inside a fixed finite box is exactly the first free bit. In particular
the second free bit is irrelevant. No percolation estimate is imported. -/

open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.UnitProjectionGadget
noncomputable section
open DimerBinaryResponse

def westRay (w : Site) : Prop := w.2=0 ∧ w.1<0

noncomputable def colors (a b : Bool) (w : Site) : Bool :=
  if w=(0,0) then a else if w=(1,0) then b else
    decide (0<2*w.1+w.2 ∨ westRay w)

def quad : GraphQuad where
  domain := latticeBox 3
  firstSide := {(-2,0)}
  secondSide := {(2,0)}

theorem black_step_preserves_westRay (b : Bool) {u v : Site}
    (hu : westRay u) (h : TriangularAdj u v) (hv : colors false b v=true) :
    westRay v := by
  by_cases hv0 : v=(0,0)
  · simp [colors,hv0] at hv
  by_cases hv1 : v=(1,0)
  · subst v
    unfold westRay TriangularAdj at *
    omega
  have hc : 0<2*v.1+v.2 ∨ westRay v := by simpa [colors,hv0,hv1] using hv
  rcases u with ⟨u₁,u₂⟩
  rcases v with ⟨v₁,v₂⟩
  simp only [Prod.mk.injEq] at hv0
  unfold westRay TriangularAdj at *
  dsimp at *
  omega

theorem black_walk_preserves_westRay (b : Bool) {u v : Site}
    (p : triangularGraph.Walk u v) : westRay u→
    (∀w∈p.support,colors false b w=true)→westRay v := by
  induction p with
  | nil => intro hu _; exact hu
  | @cons u w v h p ih =>
    intro hu hc
    apply ih (black_step_preserves_westRay b hu h (hc w (by simp)))
    intro z hz
    exact hc z (by simp only [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)

def openPath : triangularGraph.Walk (-2,0) (2,0) :=
  .cons (by norm_num [TriangularAdj] : TriangularAdj (-2,0) (-1,0))
    (.cons (by norm_num [TriangularAdj] : TriangularAdj (-1,0) (0,0))
      (.cons (by norm_num [TriangularAdj] : TriangularAdj (0,0) (0,1))
        (.cons (by norm_num [TriangularAdj] : TriangularAdj (0,1) (1,1))
          (.cons (by norm_num [TriangularAdj] : TriangularAdj (1,1) (2,0)) .nil))))

theorem crossing_true (b : Bool) : quad.Crossing (colors true b) := by
  refine ⟨(-2,0),by simp [quad],(2,0),by simp [quad],openPath,?_⟩
  intro w hw
  change w ∈ [(-2,0),(-1,0),(0,0),(0,1),(1,1),(2,0)] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals norm_num [quad,latticeBox,colors,westRay]

theorem not_crossing_false (b : Bool) : ¬quad.Crossing (colors false b) := by
  rintro ⟨u,hu,v,hv,p,hp⟩
  simp only [quad,Finset.mem_singleton] at hu hv
  subst u
  subst v
  have hw := black_walk_preserves_westRay b p (by norm_num [westRay])
    (fun w hw => (hp w hw).2)
  norm_num [westRay] at hw

theorem crossing_iff (a b : Bool) : quad.Crossing (colors a b)↔a=true := by
  cases a
  · simp [not_crossing_false]
  · simp [crossing_true]

theorem test_eq_first (a b : Bool) : quad.test (colors a b)=a := by
  cases a <;> simp [GraphQuad.test,crossing_iff]

theorem putPair_colors (a b : Bool) :
    putPair (colors false false) (0,0) (1,0) a b=colors a b := by
  funext w
  by_cases hw0 : w=(0,0)
  · subst w; simp [putPair,colors]
  by_cases hw1 : w=(1,0)
  · subst w; simp [putPair,colors]
  simp [putPair,colors,hw0,hw1]

theorem forced_pair_table (a b : Bool) :
    quad.test (putPair (colors false false) (0,0) (1,0) a b)=a := by
  rw [putPair_colors,test_eq_first]

/-- Only the finite nonfree sites must be prescribed. Colors outside the
box and at both free sites are arbitrary. -/
def Forced (ω : Configuration) : Prop :=
  ∀w∈latticeBox 3,w≠(0,0)→w≠(1,0)→ω w=colors false false w

theorem forced_test (ω : Configuration) (hω : Forced ω) (a b : Bool) :
    quad.test (putPair ω (0,0) (1,0) a b)=a := by
    calc
    _=quad.test (putPair (colors false false) (0,0) (1,0) a b) := by
      apply quad.test_congr
      intro w hw
      by_cases hw0 : w=(0,0)
      · subst w; simp [putPair]
      by_cases hw1 : w=(1,0)
      · subst w; simp [putPair]
      simpa [putPair,hw0,hw1] using hω w hw hw0 hw1
    _=a := forced_pair_table a b

noncomputable def jump (ω : TwoTimeConfiguration) : ℝ :=
  if quad.test (ω false)≠quad.test (ω true) then 1 else 0

theorem canonical_jump :
    rawPairResponse canonical (fun _ => colors false false) (0,0) (1,0) jump=1/4 := by
  norm_num [rawPairResponse,jump,pairHistory,forced_pair_table,canonical,
    Fintype.sum_bool]

theorem refresh_jump :
    rawPairResponse refresh (fun _ => colors false false) (0,0) (1,0) jump=1/4 := by
  norm_num [rawPairResponse,jump,pairHistory,forced_pair_table,refresh,
    Fintype.sum_bool]

#print axioms forced_test
#print axioms crossing_iff
#print axioms forced_pair_table
#print axioms canonical_jump
#print axioms refresh_jump
end
end ExceptionalTimes.PairSquareSewing.UnitProjectionGadget




