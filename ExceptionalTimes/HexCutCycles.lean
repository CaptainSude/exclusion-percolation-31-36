import ExceptionalTimes.Annulus
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

/-- Clockwise parametrization of the six straight sides of an axial hexagon.
Each corner belongs to the side starting there. -/
def hexPoint (n i : ℤ) : Site :=
  if i < n then (n, -i)
  else if i < 2*n then (2*n-i, -n)
  else if i < 3*n then (2*n-i, i-3*n)
  else if i < 4*n then (-n, i-3*n)
  else if i < 5*n then (i-5*n, n)
  else (i-5*n, 6*n-i)

theorem hexPoint_injective {n : ℤ} (hn : 0 < n) {i j : ℤ}
    (hi : 0 ≤ i ∧ i < 6*n) (hj : 0 ≤ j ∧ j < 6*n)
    (h : hexPoint n i = hexPoint n j) : i = j := by
  unfold hexPoint at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega

theorem hexPoint_next {n i : ℤ} (_hn : 0 < n) (_hi : 0 ≤ i) (hi' : i+1 < 6*n) :
    TriangularAdj (hexPoint n i) (hexPoint n (i+1)) := by
  unfold hexPoint
  split_ifs <;> simp [TriangularAdj] <;> omega

theorem hexPoint_wrap {n : ℤ} (hn : 0 < n) :
    TriangularAdj (hexPoint n (6*n-1)) (hexPoint n 0) := by
  unfold hexPoint
  split_ifs <;> simp [TriangularAdj] <;> omega

theorem hexPoint_radius {n i : ℤ} (hn : 0 < n) (hi : 0 ≤ i ∧ i < 6*n) :
    hexRadius (hexPoint n i) = n := by
  unfold hexPoint
  split_ifs <;> simp only [hexRadius, abs_eq_max_neg] <;> omega

theorem hexPoint_surjective {n : ℤ} (hn : 0 < n) {v : Site} (hv : hexRadius v = n) :
    ∃ i : ℤ, (0 ≤ i ∧ i < 6*n) ∧ hexPoint n i = v := by
  rcases v with ⟨x,y⟩
  simp only [hexRadius, abs_eq_max_neg] at hv
  by_cases h0 : x = n
  · refine ⟨-y, by omega, ?_⟩
    unfold hexPoint
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  by_cases h1 : y = -n
  · refine ⟨2*n-x, by omega, ?_⟩
    unfold hexPoint
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  by_cases h2 : x+y = -n
  · refine ⟨2*n-x, by omega, ?_⟩
    unfold hexPoint
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  by_cases h3 : x = -n
  · refine ⟨3*n+y, by omega, ?_⟩
    unfold hexPoint
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  by_cases h4 : y = n
  · refine ⟨5*n+x, by omega, ?_⟩
    unfold hexPoint
    split_ifs <;> simp only [Prod.mk.injEq] <;> omega
  refine ⟨5*n+x, by omega, ?_⟩
  unfold hexPoint
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem cycleGraph_adj_steps {N : ℕ} {i j : Fin N} (h : (SimpleGraph.cycleGraph N).Adj i j) :
    i.val+1=j.val ∨ j.val+1=i.val ∨
      (i.val=0 ∧ j.val+1=N) ∨ (j.val=0 ∧ i.val+1=N) := by
  have h₁ := Fin.intCast_val_sub_eq_sub_add_ite i j
  have h₂ := Fin.intCast_val_sub_eq_sub_add_ite j i
  rw [SimpleGraph.cycleGraph_adj'] at h
  split_ifs at h₁ h₂ <;> omega

def hexCycleHom (n : ℕ) : SimpleGraph.cycleGraph (6*n+3+3) →g triangularGraph where
  toFun i := hexPoint (n+1) i.val
  map_rel' := by
    intro i j hij
    change TriangularAdj (hexPoint (n+1) i.val) (hexPoint (n+1) j.val)
    have hn : (0:ℤ) < n+1 := by omega
    rcases cycleGraph_adj_steps hij with h | h | ⟨hi,hj⟩ | ⟨hj,hi⟩
    · have h' : (j.val:ℤ) = i.val+1 := by omega
      rw [h']
      exact hexPoint_next hn (by omega) (by omega)
    · have h' : (i.val:ℤ) = j.val+1 := by omega
      rw [h']
      exact triangularAdj_symm (hexPoint_next hn (by omega) (by omega))
    · have hi' : (i.val:ℤ) = 0 := by omega
      have hj' : (j.val:ℤ) = 6*(n+1)-1 := by omega
      rw [hi',hj']
      exact triangularAdj_symm (hexPoint_wrap hn)
    · have hi' : (i.val:ℤ) = 6*(n+1)-1 := by omega
      have hj' : (j.val:ℤ) = 0 := by omega
      rw [hi',hj']
      exact hexPoint_wrap hn

theorem hexCycleHom_injective (n : ℕ) : Function.Injective (hexCycleHom n) := by
  intro i j hij
  apply Fin.ext
  have h := hexPoint_injective (n := (n:ℤ)+1) (by omega)
    (i := i.val) (j := j.val) (by omega) (by omega) hij
  omega

/-- The literal graph cycle cutting the lattice at hexagonal radius `n+1`. -/
def hexCycle (n : ℕ) : triangularGraph.Walk (hexCycleHom n 0) (hexCycleHom n 0) :=
  (SimpleGraph.cycleGraph.cycle (6*n+3)).map (hexCycleHom n)

theorem hexCycle_isCycle (n : ℕ) : (hexCycle n).IsCycle :=
  SimpleGraph.cycleGraph.isCycle_cycle.map (hexCycleHom_injective n)

theorem hexCycle_length (n : ℕ) : (hexCycle n).length = 6*(n+1) := by
  simp [hexCycle]
  omega

theorem hexCycle_mem_support (n : ℕ) (i : Fin (6*n+3+3)) :
    hexCycleHom n i ∈ (hexCycle n).support := by
  rw [hexCycle, SimpleGraph.Walk.support_map]
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  have hi : (SimpleGraph.cycleGraph.cycle (6*n+3)).getVert (6*n+3+3-i.val) = i := by
    rw [SimpleGraph.cycleGraph.getVert_cycle (by omega)]
    apply Fin.ext
    change (6*n+3+3-(6*n+3+3-i.val)) % (6*n+3+3) = i.val
    rw [Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt i.isLt]
  rw [←hi]
  exact SimpleGraph.Walk.getVert_mem_support _ _

theorem hexCycle_support (n : ℕ) :
    {v | v ∈ (hexCycle n).support} = hexBoundary (n+1) := by
  ext v
  constructor
  · intro hv
    rw [Set.mem_ofPred_eq,hexCycle,SimpleGraph.Walk.support_map] at hv
    rcases List.mem_map.mp hv with ⟨i,_,rfl⟩
    exact hexPoint_radius (by omega) (by omega)
  · intro hv
    obtain ⟨i,hi,hiv⟩ := hexPoint_surjective (by omega : (0:ℤ) < n+1) hv
    have hinat : i.toNat < 6*n+3+3 := by omega
    let j : Fin (6*n+3+3) := ⟨i.toNat,hinat⟩
    have hj : hexCycleHom n j = v := by
      change hexPoint (n+1) (i.toNat:ℤ) = v
      rw [Int.toNat_of_nonneg hi.1]
      exact hiv
    rw [←hj]
    exact hexCycle_mem_support n j

#print axioms hexCycle_isCycle
#print axioms hexCycle_support

def translateGraph (c : Site) : triangularGraph →g triangularGraph where
  toFun v := c+v
  map_rel' := by
    intro u v huv
    change TriangularAdj (c+u) (c+v)
    change TriangularAdj u v at huv
    simp only [TriangularAdj, Prod.fst_add, Prod.snd_add] at huv ⊢
    omega

theorem translateGraph_injective (c : Site) : Function.Injective (translateGraph c) := by
  intro u v h
  exact add_left_cancel h

def centeredHexCycle (c : Site) (n : ℕ) :
    triangularGraph.Walk (translateGraph c (hexCycleHom n 0)) (translateGraph c (hexCycleHom n 0)) :=
  (hexCycle n).map (translateGraph c)

theorem centeredHexCycle_isCycle (c : Site) (n : ℕ) : (centeredHexCycle c n).IsCycle :=
  (hexCycle_isCycle n).map (translateGraph_injective c)

theorem centeredHexCycle_support (c : Site) (n : ℕ) :
    {v | v ∈ (centeredHexCycle c n).support} = {v | hexRadius (v-c) = (n+1:ℕ)} := by
  ext v
  rw [Set.mem_ofPred_eq,centeredHexCycle,SimpleGraph.Walk.support_map]
  constructor
  · intro hv
    rcases List.mem_map.mp hv with ⟨w,hw,hv⟩
    have hr := Set.ext_iff.mp (hexCycle_support n) w |>.mp hw
    change hexRadius w = (n+1:ℕ) at hr
    change c+w=v at hv
    simpa [←hv,add_sub_cancel_left] using hr
  · intro hv
    apply List.mem_map.mpr
    refine ⟨v-c,?_,?_⟩
    · exact (Set.ext_iff.mp (hexCycle_support n) (v-c)).mpr hv
    · change c+(v-c)=v
      abel

#print axioms centeredHexCycle_isCycle
#print axioms centeredHexCycle_support

end ExceptionalTimes.Annulus
