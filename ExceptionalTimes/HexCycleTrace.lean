import ExceptionalTimes.HexCutCycles
import ExceptionalTimes.HexGaugePaths

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

open TriangularPlane

set_option maxHeartbeats 1200000 in
theorem boundary_neighbors_common_form {n : ℤ} (hn : 0 < n) {u v : Site}
    (hu : hexRadius u = n) (hv : hexRadius v = n) (hadj : TriangularAdj u v) :
    ∃ k : Fin 6, integerForm k u = n ∧ integerForm k v = n := by
  have hh : (u.1 = n ∧ v.1 = n) ∨ (u.1 = -n ∧ v.1 = -n) ∨
      (u.2 = n ∧ v.2 = n) ∨ (u.2 = -n ∧ v.2 = -n) ∨
      (u.1+u.2 = n ∧ v.1+v.2 = n) ∨ (u.1+u.2 = -n ∧ v.1+v.2 = -n) := by
    have hub := hu.le
    have hvb := hv.le
    simp only [hexRadius,max_le_iff,abs_le] at hub hvb
    have hue : u.1=n ∨ u.1= -n ∨ u.2=n ∨ u.2= -n ∨ u.1+u.2=n ∨ u.1+u.2= -n := by
      simp only [hexRadius,abs_eq_max_neg] at hu
      omega
    have hve : v.1=n ∨ v.1= -n ∨ v.2=n ∨ v.2= -n ∨ v.1+v.2=n ∨ v.1+v.2= -n := by
      simp only [hexRadius,abs_eq_max_neg] at hv
      omega
    clear hu hv
    unfold TriangularAdj at hadj
    rcases hue with h | h | h | h | h | h <;>
      rcases hve with h' | h' | h' | h' | h' | h' <;> omega
  rcases hh with h | h | h | h | h | h
  · exact ⟨0,by simpa [integerForm] using h⟩
  · refine ⟨1,?_⟩
    simp only [integerForm,Matrix.cons_val_one,Matrix.cons_val_zero]
    omega
  · exact ⟨2,by simpa [integerForm] using h⟩
  · refine ⟨3,?_⟩
    norm_num [integerForm]
    omega
  · exact ⟨4,by simpa [integerForm] using h⟩
  · refine ⟨5,?_⟩
    norm_num [integerForm]
    omega

theorem boundary_edge_hexGauge {n : ℤ} (hn : 0 < n) {u v : Site}
    (hu : hexRadius u = n) (hv : hexRadius v = n) (hadj : TriangularAdj u v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : hexGauge (edgePoint u v t) = (n:ℝ) := by
  apply le_antisymm (edge_hexGauge_le hu.le hv.le ht0 ht1)
  obtain ⟨k,hku,hkv⟩ := boundary_neighbors_common_form hn hu hv hadj
  have h := axialForm_le_hexGauge k (edgePoint u v t)
  rw [axialForm_edgePoint,hku,hkv] at h
  nlinarith

theorem hexCycle_trace_subset (n : ℕ) :
    walkTrace (hexCycle n) ⊆ {p | hexGauge p = (n+1:ℕ)} := by
  intro q hq
  have hrad (v : Site) (hv : v ∈ (hexCycle n).support) : hexRadius v = (n+1:ℕ) :=
    (Set.ext_iff.mp (hexCycle_support n) v).mp hv
  rcases walkTrace_point_or_edge (hexCycle n) hq with ⟨v,hv,rfl⟩ |
    ⟨u,hu,v,hv,hadj,t,ht0,ht1,rfl⟩
  · change hexGauge (point v) = _
    rw [hexGauge_point,hrad v hv]
    norm_cast
  · exact boundary_edge_hexGauge (by omega) (hrad u hu) (hrad v hv) hadj ht0 ht1

theorem walkTrace_getVert_edge {u v : Site} (p : triangularGraph.Walk u v)
    (i : ℕ) (hi : i < p.length) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    edgePoint (p.getVert i) (p.getVert (i+1)) t ∈ walkTrace p := by
  induction p generalizing i with
  | nil => simp at hi
  | cons hab p ih =>
    cases i with
    | zero =>
      apply Or.inl
      refine ⟨t,ht0,ht1,?_⟩
      simp
    | succ i =>
      apply Or.inr
      exact ih i (by simpa only [SimpleGraph.Walk.length_cons,Nat.succ_lt_succ_iff] using hi)

#print axioms hexCycle_trace_subset
#print axioms walkTrace_getVert_edge

noncomputable def realHexPoint (n s : ℝ) : ℝ × ℝ :=
  if s < n then (n,-s)
  else if s < 2*n then (2*n-s,-n)
  else if s < 3*n then (2*n-s,s-3*n)
  else if s < 4*n then (-n,s-3*n)
  else if s < 5*n then (s-5*n,n)
  else (s-5*n,6*n-s)

theorem realHexPoint_surjective {n : ℝ} (hn : 0 < n) {p : ℝ × ℝ}
    (hp : hexGauge p = n) : ∃ s : ℝ, (0 ≤ s ∧ s < 6*n) ∧ realHexPoint n s = p := by
  rcases p with ⟨x,y⟩
  have hb := hp.le
  simp only [hexGauge,max_le_iff,abs_le] at hb
  have hx : -n ≤ x ∧ x ≤ n := hb.1.1
  have hy : -n ≤ y ∧ y ≤ n := hb.1.2
  have hs : -n ≤ x+y ∧ x+y ≤ n := hb.2
  have hface : x=n ∨ y= -n ∨ x+y= -n ∨ x= -n ∨ y=n ∨ x+y=n := by
    by_contra h
    push Not at h
    have hlt : hexGauge (x,y) < n := by
      simp only [hexGauge,max_lt_iff,abs_lt]
      rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
      exact ⟨⟨⟨lt_of_le_of_ne hx.1 h3.symm,lt_of_le_of_ne hx.2 h0⟩,
        ⟨lt_of_le_of_ne hy.1 h1.symm,lt_of_le_of_ne hy.2 h4⟩⟩,
        ⟨lt_of_le_of_ne hs.1 h2.symm,lt_of_le_of_ne hs.2 h5⟩⟩
    rw [hp] at hlt
    exact hlt.false
  rcases hface with h0 | h1 | h2 | h3 | h4 | h5
  · refine ⟨-y,⟨by linarith,by linarith⟩,?_⟩
    unfold realHexPoint
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · by_cases hcorner : x=n
    · refine ⟨n,⟨hn.le,by linarith⟩,?_⟩
      unfold realHexPoint
      split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
    · refine ⟨2*n-x,⟨by linarith,by linarith⟩,?_⟩
      unfold realHexPoint
      split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · refine ⟨2*n-x,⟨by linarith,by linarith⟩,?_⟩
    unfold realHexPoint
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · refine ⟨3*n+y,⟨by linarith,by linarith⟩,?_⟩
    unfold realHexPoint
    split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · refine ⟨5*n+x,⟨by linarith,?_⟩,?_⟩
    · linarith
    · unfold realHexPoint
      split_ifs <;> apply Prod.ext <;> dsimp <;> linarith
  · by_cases hcorner : x=n
    · refine ⟨0,⟨le_rfl,by linarith⟩,?_⟩
      unfold realHexPoint
      split_ifs; apply Prod.ext <;> dsimp <;> linarith
    · have hxlt : x < n := lt_of_le_of_ne hx.2 hcorner
      refine ⟨5*n+x,⟨by linarith,by linarith⟩,?_⟩
      unfold realHexPoint
      split_ifs <;> apply Prod.ext <;> dsimp <;> linarith

def integerSidePoint (n i : ℤ) (k : Fin 6) : Site :=
  ![(n,-i),(2*n-i,-n),(2*n-i,i-3*n),(-n,i-3*n),(i-5*n,n),(i-5*n,6*n-i)] k

def realSidePoint (n s : ℝ) (k : Fin 6) : ℝ × ℝ :=
  ![(n,-s),(2*n-s,-n),(2*n-s,s-3*n),(-n,s-3*n),(s-5*n,n),(s-5*n,6*n-s)] k

theorem point_integerSidePoint (n i : ℤ) (k : Fin 6) :
    point (integerSidePoint n i k) = realSidePoint n i k := by
  fin_cases k <;> simp [integerSidePoint,realSidePoint,point]

theorem hexPoint_on_closed_side {n i : ℤ} (hn : 0 < n) (k : Fin 6)
    (hlo : (k.val:ℤ)*n ≤ i) (hhi : i ≤ (k.val+1:ℕ)*n) :
    hexPoint n i = integerSidePoint n i k := by
  fin_cases k <;> norm_num [integerSidePoint] at hlo hhi ⊢ <;>
    unfold hexPoint <;> split_ifs <;> simp only [Prod.mk.injEq,true_and,and_true] <;> omega

theorem realHexPoint_on_closed_side {n s : ℝ} (hn : 0 < n) (k : Fin 6)
    (hlo : (k.val:ℝ)*n ≤ s) (hhi : s ≤ (k.val+1:ℕ)*n) :
    realHexPoint n s = realSidePoint n s k := by
  fin_cases k <;> norm_num [realSidePoint] at hlo hhi ⊢ <;>
    unfold realHexPoint <;> split_ifs <;> apply Prod.ext <;> dsimp <;> linarith

theorem integer_edge_in_side {n i : ℤ} (_hn : 0 < n) (hi0 : 0 ≤ i) (hi1 : i < 6*n) :
    ∃ k : Fin 6, (k.val:ℤ)*n ≤ i ∧ i+1 ≤ (k.val+1:ℕ)*n := by
  by_cases h0 : i < n
  · exact ⟨0,by norm_num; omega⟩
  by_cases h1 : i < 2*n
  · exact ⟨1,by norm_num; omega⟩
  by_cases h2 : i < 3*n
  · exact ⟨2,by norm_num; omega⟩
  by_cases h3 : i < 4*n
  · exact ⟨3,by norm_num; omega⟩
  by_cases h4 : i < 5*n
  · exact ⟨4,by norm_num; omega⟩
  exact ⟨5,by norm_num; omega⟩

theorem realHexPoint_interpolate {n i : ℤ} (hn : 0 < n) (hi0 : 0 ≤ i) (hi1 : i < 6*n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    realHexPoint (n:ℝ) ((i:ℝ)+t) = edgePoint (hexPoint n i) (hexPoint n (i+1)) t := by
  obtain ⟨k,hlo,hhi⟩ := integer_edge_in_side hn hi0 hi1
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hlo' : (k.val:ℝ)*(n:ℝ) ≤ (i:ℝ) := by exact_mod_cast hlo
  have hhi' : (i:ℝ)+1 ≤ (k.val+1:ℕ)*(n:ℝ) := by exact_mod_cast hhi
  rw [realHexPoint_on_closed_side hn' k (by linarith) (by linarith),
    hexPoint_on_closed_side hn k hlo (by omega),
    hexPoint_on_closed_side hn k (by omega) hhi]
  fin_cases k <;> ext <;> simp [realSidePoint,integerSidePoint,edgePoint] <;> ring

#print axioms realHexPoint_surjective
#print axioms realHexPoint_interpolate

theorem hexPoint_end (n : ℤ) (hn : 0 < n) : hexPoint n (6*n) = hexPoint n 0 := by
  unfold hexPoint
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem hexCycle_edge_mem_trace (n i : ℕ) (hi : i < 6*(n+1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    edgePoint (hexPoint (n+1) i) (hexPoint (n+1) (i+1)) t ∈ walkTrace (hexCycle n) := by
  let N := 6*n+3+3
  let m := N-(i+1)
  have hiN : i < N := by dsimp [N]; omega
  have hm : m < N := by dsimp [m]; omega
  have hm' : m+1 ≤ N := by omega
  have hfirst : (hexCycle n).getVert m = hexPoint (n+1) (i+1) := by
    rw [hexCycle,SimpleGraph.Walk.getVert_map,SimpleGraph.cycleGraph.getVert_cycle (by omega)]
    change hexPoint (n+1) (((N-m)%N : ℕ):ℤ) = _
    have hsub : N-m = i+1 := by dsimp [m]; omega
    rw [hsub]
    by_cases hi' : i+1 < N
    · rw [Nat.mod_eq_of_lt hi']
      norm_cast
    · have hi' : i+1 = N := by omega
      rw [hi',Nat.mod_self]
      have hN : (N:ℤ) = 6*((n:ℤ)+1) := by dsimp [N]; omega
      have hix : (i:ℤ)+1 = N := by exact_mod_cast hi'
      rw [hix,hN]
      exact (hexPoint_end _ (by omega)).symm
  have hsecond : (hexCycle n).getVert (m+1) = hexPoint (n+1) i := by
    rw [hexCycle,SimpleGraph.Walk.getVert_map,SimpleGraph.cycleGraph.getVert_cycle (by omega)]
    change hexPoint (n+1) (((N-(m+1))%N : ℕ):ℤ) = _
    have hsub : N-(m+1) = i := by dsimp [m]; omega
    rw [hsub,Nat.mod_eq_of_lt hiN]
  have h := walkTrace_getVert_edge (hexCycle n) m
    (by rw [hexCycle_length]; dsimp [N] at hm; omega) (t := 1-t) (by linarith) (by linarith)
  rw [hfirst,hsecond,edgePoint_reverse] at h
  exact h

theorem realHexPoint_mem_hexCycle_trace (n : ℕ) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 6*(n+1:ℕ)) :
    realHexPoint (n+1:ℕ) s ∈ walkTrace (hexCycle n) := by
  let i : ℤ := ⌊s⌋
  have hi0 : 0 ≤ i := Int.le_floor.mpr (by exact_mod_cast hs0)
  have hi1 : i < 6*((n:ℤ)+1) := Int.floor_lt.mpr (by exact_mod_cast hs1)
  have hit : (i:ℝ) ≤ s := Int.floor_le s
  have hit' : s < (i:ℝ)+1 := Int.lt_floor_add_one s
  have he := realHexPoint_interpolate (by omega : (0:ℤ) < n+1) hi0 hi1
    (t := s-i) (by linarith) (by linarith)
  have his : (i:ℝ)+(s-i) = s := by ring
  rw [his] at he
  norm_cast at he ⊢
  rw [he]
  have h := hexCycle_edge_mem_trace n i.toNat (by omega) (t := s-i) (by linarith) (by linarith)
  simpa only [Int.toNat_of_nonneg hi0,Nat.cast_add,Nat.cast_one] using h

/-- The entire drawn lattice cycle is exactly the continuous hexagonal
level polygon, including every interior point of every boundary edge. -/
theorem hexCycle_trace (n : ℕ) :
    walkTrace (hexCycle n) = {p | hexGauge p = (n+1:ℕ)} := by
  apply Set.Subset.antisymm (hexCycle_trace_subset n)
  intro p hp
  obtain ⟨s,⟨hs0,hs1⟩,he⟩ := realHexPoint_surjective (by positivity : (0:ℝ) < (n+1:ℕ)) hp
  rw [←he]
  exact realHexPoint_mem_hexCycle_trace n hs0 hs1

#print axioms hexCycle_trace

theorem point_add (c u : Site) : point (c+u) = point c+point u := by
  ext <;> simp [point]

theorem edgePoint_add (c u v : Site) (t : ℝ) :
    edgePoint (c+u) (c+v) t = point c+edgePoint u v t := by
  ext <;> simp [edgePoint,point] <;> ring

theorem edge_trace_translate (c u v : Site) :
    {q | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q = edgePoint (c+u) (c+v) t} =
      (fun q => point c+q) '' {q | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q = edgePoint u v t} := by
  ext q
  constructor
  · rintro ⟨t,ht0,ht1,rfl⟩
    exact ⟨edgePoint u v t,⟨t,ht0,ht1,rfl⟩,(edgePoint_add c u v t).symm⟩
  · rintro ⟨q,⟨t,ht0,ht1,rfl⟩,rfl⟩
    exact ⟨t,ht0,ht1,(edgePoint_add c u v t).symm⟩

theorem walkTrace_translate (c : Site) {u v : Site} (p : triangularGraph.Walk u v) :
    walkTrace (p.map (translateGraph c)) = (fun q => point c+q) '' walkTrace p := by
  induction p with
  | nil => simp [SimpleGraph.Walk.map_nil,walkTrace,translateGraph,point_add]
  | @cons u w v hadj p ih =>
    change ({q | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ q = edgePoint (c+u) (c+w) t} ∪
      walkTrace (p.map (translateGraph c))) = _
    rw [edge_trace_translate,ih,←Set.image_union]
    rfl

/-- Translated graph cuts have precisely the translated continuous
polygon boundary, at every point of their drawn edges. -/
theorem centeredHexCycle_trace (c : Site) (n : ℕ) :
    walkTrace (centeredHexCycle c n) = {p | hexGauge (p-point c) = (n+1:ℕ)} := by
  rw [centeredHexCycle,walkTrace_translate,hexCycle_trace]
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa only [Set.mem_ofPred_eq,add_sub_cancel_left] using hq
  · intro hp
    refine ⟨p-point c,hp,?_⟩
    abel

#print axioms centeredHexCycle_trace

end ExceptionalTimes.Annulus
