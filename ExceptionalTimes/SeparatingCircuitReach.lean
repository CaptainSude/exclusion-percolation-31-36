import ExceptionalTimes.WiredPivotal
import ExceptionalTimes.LatticeEmbedding

/-! A circuit separating the origin from infinity must reach far away
from any remote probe center. The proof uses literal axis rays and the
already stated graph separation property, with no new planar input. -/

namespace ExceptionalTimes.SeparatingCircuitReach

set_option backward.isDefEq.respectTransparency false

open WiredBoundary

def rayWalk (f : ℕ→Site) (h : ∀ n,TriangularAdj (f n) (f (n+1))) :
    (n : ℕ)→triangularGraph.Walk (f 0) (f n)
  | 0 => .nil
  | n+1 => (rayWalk f h n).concat (h n)

theorem rayWalk_support (f : ℕ→Site) (h : ∀ n,TriangularAdj (f n) (f (n+1)))
    (n : ℕ) : ∀ z∈(rayWalk f h n).support, z∈Set.range f := by
  induction n with
  | zero =>
      intro z hz
      have hz' : z=f 0 := by simpa [rayWalk] using hz
      exact ⟨0,hz'.symm⟩
  | succ n ih =>
      intro z hz
      change z∈((rayWalk f h n).concat (h n)).support at hz
      rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz | hz
      · exact ih z hz
      · exact ⟨n+1,hz.symm⟩

theorem separates_hits_ray {S C : Set Site} (hsep : SeparatesFromInfinity S C)
    (f : ℕ→Site) (hf : Function.Injective f) (h0 : f 0∈S)
    (hstep : ∀ n,TriangularAdj (f n) (f (n+1))) : ∃ n,f n∈C := by
  obtain ⟨K,_,hcut⟩ := hsep
  obtain ⟨v,⟨n,rfl⟩,hv⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finset K
  obtain ⟨z,hz,hC⟩ := hcut (f 0) h0 (f n) hv (rayWalk f hstep n)
  obtain ⟨j,rfl⟩ := rayWalk_support f hstep n z hz
  exact ⟨j,hC⟩

theorem separates_hits_vertical {S C : Set Site} (hsep : SeparatesFromInfinity S C)
    (h0 : (0,0)∈S) : ∃ n : ℕ,(0,(n : ℤ))∈C := by
  refine separates_hits_ray hsep (fun n => (0,(n : ℤ))) ?_ h0 ?_
  · intro n m h
    exact Int.ofNat_inj.mp (congrArg Prod.snd h)
  · intro n
    apply Or.inr
    apply Or.inr
    apply Or.inl
    simp

theorem separates_hits_horizontal {S C : Set Site} (hsep : SeparatesFromInfinity S C)
    (h0 : (0,0)∈S) : ∃ n : ℕ,((n : ℤ),0)∈C := by
  refine separates_hits_ray hsep (fun n => ((n : ℤ),0)) ?_ h0 ?_
  · intro n m h
    exact Int.ofNat_inj.mp (congrArg Prod.fst h)
  · intro n
    apply Or.inl
    simp

/-- The separating set has a vertex at axial distance at least the
probe center's own distance from the origin. It cannot be a small local
loop contained in a remote probe. -/
theorem separating_set_reaches {S C : Set Site} (hsep : SeparatesFromInfinity S C)
    (h0 : (0,0)∈S) (x : Site) :
    ∃ z∈C,latticeRadius x≤latticeRadius (z-x) := by
  by_cases hx : x.2.natAbs≤x.1.natAbs
  · obtain ⟨n,hn⟩ := separates_hits_vertical hsep h0
    refine ⟨(0,(n : ℤ)),hn,?_⟩
    simp only [latticeRadius,Prod.fst_sub,zero_sub,Int.natAbs_neg,max_eq_left hx]
    exact Nat.le_max_left _ _
  · obtain ⟨n,hn⟩ := separates_hits_horizontal hsep h0
    refine ⟨((n : ℤ),0),hn,?_⟩
    have hy : x.1.natAbs≤x.2.natAbs := by omega
    simp only [latticeRadius,Prod.snd_sub,zero_sub,Int.natAbs_neg,max_eq_right hy]
    exact Nat.le_max_right _ _

theorem latticeRadius_le_two_norm (v : Site) :
    (latticeRadius v : ℝ)≤2*‖triangularEmbedding v‖ := by
  obtain ⟨hx,hy⟩ := triangularEmbedding_coordinate_bounds v
  simp only [latticeRadius,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs,max_le_iff]
  exact ⟨hx,hy⟩

theorem separating_set_euclidean_reach {S C : Set Site} (hsep : SeparatesFromInfinity S C)
    (h0 : (0,0)∈S) (x : Site) :
    ∃ z∈C,(latticeRadius x : ℝ)/2≤‖triangularEmbedding (z-x)‖ := by
  obtain ⟨z,hz,hρ⟩ := separating_set_reaches hsep h0 x
  refine ⟨z,hz,?_⟩
  have hh : (latticeRadius x : ℝ)≤latticeRadius (z-x) := by exact_mod_cast hρ
  linarith [latticeRadius_le_two_norm (z-x)]

#print axioms separates_hits_ray
#print axioms separating_set_euclidean_reach

end ExceptionalTimes.SeparatingCircuitReach
