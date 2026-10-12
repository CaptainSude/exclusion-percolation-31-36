import ExceptionalTimes.Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

/-!
# The concrete triangular lattice as a straight-edge plane drawing

The integer-coordinate drawing is an affine image of the usual equilateral
triangular lattice. This file checks actual edge noncrossing, without
assuming a planar-graph predicate or any Jordan/arm consequence.
-/

namespace ExceptionalTimes.TriangularPlane

def point (u : Site) : ℝ × ℝ := ((u.1 : ℝ), (u.2 : ℝ))

def edgePoint (u v : Site) (t : ℝ) : ℝ × ℝ :=
  ((u.1 : ℝ) + t * ((v.1 : ℝ) - u.1),
   (u.2 : ℝ) + t * ((v.2 : ℝ) - u.2))

@[simp] theorem edgePoint_zero (u v : Site) : edgePoint u v 0 = point u := by
  simp [edgePoint, point]

@[simp] theorem edgePoint_one (u v : Site) : edgePoint u v 1 = point v := by
  simp [edgePoint, point]

theorem point_injective : Function.Injective point := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [point, Int.cast_inj] at hx hy
  exact Prod.ext hx hy

theorem edgePoint_reverse (u v : Site) (t : ℝ) :
    edgePoint v u (1 - t) = edgePoint u v t := by
  ext <;> simp only [edgePoint] <;> ring

theorem edgePoint_continuous (u v : Site) : Continuous (edgePoint u v) := by
  unfold edgePoint
  fun_prop

private def east (u : Site) : Site := (u.1 + 1, u.2)
private def north (u : Site) : Site := (u.1, u.2 + 1)
private def southeast (u : Site) : Site := (u.1 + 1, u.2 - 1)

private def ForwardAdj (u v : Site) : Prop :=
  v = east u ∨ v = north u ∨ v = southeast u

private theorem adj_forward_or_reverse {u v : Site} (h : TriangularAdj u v) :
    ForwardAdj u v ∨ ForwardAdj v u := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  simp only [ForwardAdj, east, north, southeast, Prod.mk.injEq]
  unfold TriangularAdj at h
  omega

private theorem fractional_base_unique (a b : ℤ) {s t : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : (a : ℝ) + s = b + t) : a = b := by
  have hab : (a : ℝ) < (b : ℝ) + 1 := by linarith
  have hba : (b : ℝ) < (a : ℝ) + 1 := by linarith
  have hab' : a < b + 1 := by exact_mod_cast hab
  have hba' : b < a + 1 := by exact_mod_cast hba
  omega

private theorem fractional_ne_integer (a b : ℤ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : (a : ℝ) + t ≠ b := by
  intro h
  have hab : (a : ℝ) < b := by linarith
  have hba : (b : ℝ) < (a : ℝ) + 1 := by linarith
  have hab' : a < b := by exact_mod_cast hab
  have hba' : b < a + 1 := by exact_mod_cast hba
  omega

private theorem forward_interiors {u v x y : Site} {s t : ℝ}
    (huv : ForwardAdj u v) (hxy : ForwardAdj x y)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : edgePoint u v s = edgePoint x y t) : u = x ∧ v = y := by
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  rcases huv with rfl | rfl | rfl <;>
    rcases hxy with rfl | rfl | rfl <;>
    simp [edgePoint, east, north, southeast] at hx hy
  · have hu₁ := fractional_base_unique u.1 x.1 hs0 hs1 ht0 ht1 hx
    have hu₂ : u.2 = x.2 := by exact_mod_cast hy
    have hu : u = x := Prod.ext hu₁ hu₂
    subst x
    exact ⟨rfl, rfl⟩
  · exact (fractional_ne_integer u.1 x.1 hs0 hs1 hx).elim
  · have hty : (x.2 : ℝ) + (1 - t) = u.2 + 1 := by linarith
    have htint : (x.2 : ℝ) + (1 - t) ≠ ((u.2 + 1 : ℤ) : ℝ) :=
      fractional_ne_integer x.2 (u.2 + 1) (by linarith) (by linarith)
    exact (htint (by push_cast; exact hty)).elim
  · exact (fractional_ne_integer x.1 u.1 ht0 ht1 hx.symm).elim
  · have hu₁ : u.1 = x.1 := by exact_mod_cast hx
    have hu₂ := fractional_base_unique u.2 x.2 hs0 hs1 ht0 ht1 hy
    have hu : u = x := Prod.ext hu₁ hu₂
    subst x
    exact ⟨rfl, rfl⟩
  · exact (fractional_ne_integer x.1 u.1 ht0 ht1 hx.symm).elim
  · have hsy : (u.2 : ℝ) + (1 - s) = x.2 + 1 := by linarith
    have hsint : (u.2 : ℝ) + (1 - s) ≠ ((x.2 + 1 : ℤ) : ℝ) :=
      fractional_ne_integer u.2 (x.2 + 1) (by linarith) (by linarith)
    exact (hsint (by push_cast; exact hsy)).elim
  · exact (fractional_ne_integer u.1 x.1 hs0 hs1 hx).elim
  · have hu₁ := fractional_base_unique u.1 x.1 hs0 hs1 ht0 ht1 hx
    have hst : s = t := by simp only [hu₁] at hx; linarith
    have hu₂ : u.2 = x.2 := by exact_mod_cast (show (u.2 : ℝ) = x.2 by linarith)
    have hu : u = x := Prod.ext hu₁ hu₂
    subst x
    exact ⟨rfl, rfl⟩

/-- Two actual triangular-lattice edges meeting at interior points must
be the same unordered edge. -/
theorem edge_interiors_same_edge {u v x y : Site} {s t : ℝ}
    (huv : TriangularAdj u v) (hxy : TriangularAdj x y)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1)
    (h : edgePoint u v s = edgePoint x y t) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  rcases adj_forward_or_reverse huv with huv | huv <;>
    rcases adj_forward_or_reverse hxy with hxy | hxy
  · exact Or.inl (forward_interiors huv hxy hs0 hs1 ht0 ht1 h)
  · have h' : edgePoint u v s = edgePoint y x (1 - t) := by
      simpa only [edgePoint_reverse] using h
    obtain ⟨huy, hvx⟩ := forward_interiors huv hxy hs0 hs1
      (by linarith) (by linarith) h'
    exact Or.inr ⟨huy, hvx⟩
  · have h' : edgePoint v u (1 - s) = edgePoint x y t := by
      simpa only [edgePoint_reverse] using h
    obtain ⟨hvx, huy⟩ := forward_interiors huv hxy
      (by linarith) (by linarith) ht0 ht1 h'
    exact Or.inr ⟨huy, hvx⟩
  · have h' : edgePoint v u (1 - s) = edgePoint y x (1 - t) := by
      simpa only [edgePoint_reverse] using h
    obtain ⟨hvy, hux⟩ := forward_interiors huv hxy
      (by linarith) (by linarith) (by linarith) (by linarith) h'
    exact Or.inl ⟨hux, hvy⟩

private theorem forward_no_vertex {u v : Site} (huv : ForwardAdj u v)
    (w : Site) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    edgePoint u v t ≠ point w := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  rcases huv with rfl | rfl | rfl <;>
    simp [edgePoint, point, east, north, southeast] at hx hy
  · exact fractional_ne_integer u.1 w.1 ht0 ht1 hx
  · exact fractional_ne_integer u.2 w.2 ht0 ht1 hy
  · exact fractional_ne_integer u.1 w.1 ht0 ht1 hx

/-- No lattice vertex lies in the interior of a lattice edge. -/
theorem edge_interior_no_vertex {u v : Site} (huv : TriangularAdj u v)
    (w : Site) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    edgePoint u v t ≠ point w := by
  rcases adj_forward_or_reverse huv with hf | hf
  · exact forward_no_vertex hf w ht0 ht1
  · have hn := forward_no_vertex hf w (show 0 < 1 - t by linarith)
      (show 1 - t < 1 by linarith)
    simpa only [edgePoint_reverse] using hn

/-- The edge drawing is injective along its parameter interval (indeed
along the whole real line). -/
theorem edgePoint_injective {u v : Site} (huv : TriangularAdj u v) :
    Function.Injective (edgePoint u v) := by
  have hf : ∀ a b : Site, ForwardAdj a b → Function.Injective (edgePoint a b) := by
    intro a b hab s t h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    rcases hab with rfl | rfl | rfl <;>
      simp [edgePoint, east, north, southeast] at hx hy
    · exact hx
    · exact hy
    · exact hx
  rcases adj_forward_or_reverse huv with h | h
  · exact hf u v h
  · intro s t hst
    have heq : edgePoint v u (1 - s) = edgePoint v u (1 - t) := by
      simpa only [edgePoint_reverse] using hst
    have := hf v u h heq
    linarith

theorem vertex_on_edge_is_endpoint {u v w : Site} {t : ℝ}
    (huv : TriangularAdj u v) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : edgePoint u v t = point w) : w = u ∨ w = v := by
  by_cases hzero : t = 0
  · subst t
    exact Or.inl (point_injective (by simpa using h.symm))
  by_cases hone : t = 1
  · subst t
    exact Or.inr (point_injective (by simpa using h.symm))
  exact (edge_interior_no_vertex huv w (lt_of_le_of_ne ht0 (Ne.symm hzero))
    (lt_of_le_of_ne ht1 hone) h).elim

/-- Every intersection of two closed edges is either an overlap of the
same unordered edge or precisely a common endpoint. -/
theorem closed_edge_intersection {u v x y : Site} {s t : ℝ}
    (huv : TriangularAdj u v) (hxy : TriangularAdj x y)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : edgePoint u v s = edgePoint x y t) :
    ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) ∨
      ∃ z, (z = u ∨ z = v) ∧ (z = x ∨ z = y) ∧ edgePoint u v s = point z := by
  by_cases hs : s = 0 ∨ s = 1
  · obtain ⟨z, hz, hp⟩ : ∃ z, (z = u ∨ z = v) ∧ edgePoint u v s = point z := by
      rcases hs with rfl | rfl
      · exact ⟨u, Or.inl rfl, edgePoint_zero u v⟩
      · exact ⟨v, Or.inr rfl, edgePoint_one u v⟩
    exact Or.inr ⟨z, hz, vertex_on_edge_is_endpoint hxy ht0 ht1 (h.symm.trans hp), hp⟩
  by_cases ht : t = 0 ∨ t = 1
  · obtain ⟨z, hz, hp⟩ : ∃ z, (z = x ∨ z = y) ∧ edgePoint x y t = point z := by
      rcases ht with rfl | rfl
      · exact ⟨x, Or.inl rfl, edgePoint_zero x y⟩
      · exact ⟨y, Or.inr rfl, edgePoint_one x y⟩
    exact Or.inr ⟨z, vertex_on_edge_is_endpoint huv hs0 hs1 (h.trans hp), hz, h.trans hp⟩
  exact Or.inl (edge_interiors_same_edge huv hxy (by rcases not_or.mp hs with ⟨h0, h1⟩; rcases lt_or_eq_of_le hs0 with h | h; exact h; exact (h0 h.symm).elim)
    (by rcases not_or.mp hs with ⟨h0, h1⟩; exact lt_of_le_of_ne hs1 h1)
    (by rcases not_or.mp ht with ⟨h0, h1⟩; rcases lt_or_eq_of_le ht0 with h | h; exact h; exact (h0 h.symm).elim)
    (by rcases not_or.mp ht with ⟨h0, h1⟩; exact lt_of_le_of_ne ht1 h1) h)

/-- Disjoint vertex pairs give disjoint geometric closed edges. -/
theorem disjoint_edges_do_not_cross {u v x y : Site} {s t : ℝ}
    (huv : TriangularAdj u v) (hxy : TriangularAdj x y)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    edgePoint u v s ≠ edgePoint x y t := by
  intro h
  rcases closed_edge_intersection huv hxy hs0 hs1 ht0 ht1 h with (h | h) | ⟨z, hz, hz', _⟩
  · exact hux h.1
  · exact huy h.1
  · rcases hz with rfl | rfl <;> rcases hz' with h | h
    · exact hux h
    · exact huy h
    · exact hvx h
    · exact hvy h

/-- The literal polygonal trace of a graph walk, with its actual successive
edges and its singleton vertex in the zero-length case. -/
def walkTrace : {u v : Site} → triangularGraph.Walk u v → Set (ℝ × ℝ)
  | u, _, .nil => {point u}
  | u, _, @SimpleGraph.Walk.cons _ _ _ b _ _ p =>
      {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = edgePoint u b t} ∪ walkTrace p

theorem walkTrace_point_or_edge {u v : Site} (p : triangularGraph.Walk u v)
    {z : ℝ × ℝ} (hz : z ∈ walkTrace p) :
    (∃ a ∈ p.support, z = point a) ∨
    ∃ a ∈ p.support, ∃ b ∈ p.support, TriangularAdj a b ∧
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = edgePoint a b t := by
  induction p with
  | nil => exact Or.inl ⟨_, by simp, hz⟩
  | @cons a b c hab p ih =>
      rcases hz with ⟨t, ht0, ht1, rfl⟩ | hz
      · exact Or.inr ⟨a, by simp, b, by simp, hab, t, ht0, ht1, rfl⟩
      · rcases ih hz with ⟨x, hx, hxz⟩ | ⟨x, hx, y, hy, hxy, t, ht0, ht1, hzt⟩
        · exact Or.inl ⟨x, List.mem_cons_of_mem a hx, hxz⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem a hx, y, List.mem_cons_of_mem a hy,
            hxy, t, ht0, ht1, hzt⟩

/-- A geometric intersection of two actual walk traces forces a shared
lattice vertex. This supplies the disjoint-arcs hypothesis from the
already proved disjoint-support color arguments. -/
theorem walkTrace_intersection_vertex {u v x y : Site}
    (p : triangularGraph.Walk u v) (q : triangularGraph.Walk x y)
    {z : ℝ × ℝ} (hzp : z ∈ walkTrace p) (hzq : z ∈ walkTrace q) :
    ∃ a, a ∈ p.support ∧ a ∈ q.support := by
  rcases walkTrace_point_or_edge p hzp with ⟨a, ha, hp⟩ | ⟨a, ha, b, hb, hab, s, hs0, hs1, hp⟩ <;>
    rcases walkTrace_point_or_edge q hzq with ⟨c, hc, hq⟩ | ⟨c, hc, d, hd, hcd, t, ht0, ht1, hq⟩
  · have hac : a = c := point_injective (hp.symm.trans hq)
    exact ⟨a, ha, hac ▸ hc⟩
  · rcases vertex_on_edge_is_endpoint hcd ht0 ht1 (hq.symm.trans hp) with hac | had
    · exact ⟨a, ha, hac ▸ hc⟩
    · exact ⟨a, ha, had ▸ hd⟩
  · rcases vertex_on_edge_is_endpoint hab hs0 hs1 (hp.symm.trans hq) with hca | hcb
    · exact ⟨c, hca ▸ ha, hc⟩
    · exact ⟨c, hcb ▸ hb, hc⟩
  · rcases closed_edge_intersection hab hcd hs0 hs1 ht0 ht1 (hp.symm.trans hq) with
      (⟨hac, _⟩ | ⟨had, _⟩) | ⟨w, hw, hw', _⟩
    · exact ⟨a, ha, hac ▸ hc⟩
    · exact ⟨a, ha, had ▸ hd⟩
    · refine ⟨w, ?_, ?_⟩
      · rcases hw with rfl | rfl <;> assumption
      · rcases hw' with rfl | rfl <;> assumption

theorem disjoint_supports_disjoint_traces {u v x y : Site}
    (p : triangularGraph.Walk u v) (q : triangularGraph.Walk x y)
    (h : ∀ a ∈ p.support, a ∉ q.support) : Disjoint (walkTrace p) (walkTrace q) := by
  apply Set.disjoint_left.mpr
  intro z hzp hzq
  obtain ⟨a, ha, haq⟩ := walkTrace_intersection_vertex p q hzp hzq
  exact h a ha haq

/-- If walks share at most one lattice vertex, their geometric traces can
meet only at its embedded point. In particular no unseen edge crossing or
edge overlap can invalidate the single-site pivotal picture. -/
theorem walkTrace_intersection_only {u v x y w : Site}
    (p : triangularGraph.Walk u v) (q : triangularGraph.Walk x y)
    (hw : ∀ a ∈ p.support, a ∈ q.support → a = w)
    {z : ℝ × ℝ} (hzp : z ∈ walkTrace p) (hzq : z ∈ walkTrace q) : z = point w := by
  rcases walkTrace_point_or_edge p hzp with ⟨a, ha, hp⟩ | ⟨a, ha, b, hb, hab, s, hs0, hs1, hp⟩ <;>
    rcases walkTrace_point_or_edge q hzq with ⟨c, hc, hq⟩ | ⟨c, hc, d, hd, hcd, t, ht0, ht1, hq⟩
  · have hac : a = c := point_injective (hp.symm.trans hq)
    simpa only [hw a ha (hac ▸ hc)] using hp
  · have haq : a ∈ q.support := by
      rcases vertex_on_edge_is_endpoint hcd ht0 ht1 (hq.symm.trans hp) with hac | had
      · exact hac ▸ hc
      · exact had ▸ hd
    simpa only [hw a ha haq] using hp
  · have hcp : c ∈ p.support := by
      rcases vertex_on_edge_is_endpoint hab hs0 hs1 (hp.symm.trans hq) with hca | hcb
      · exact hca ▸ ha
      · exact hcb ▸ hb
    simpa only [hw c hcp hc] using hq
  · rcases closed_edge_intersection hab hcd hs0 hs1 ht0 ht1 (hp.symm.trans hq) with
      (⟨hac, hbd⟩ | ⟨had, hbc⟩) | ⟨e, he, he', hpoint⟩
    · have hab' : a = b := (hw a ha (hac ▸ hc)).trans (hw b hb (hbd ▸ hd)).symm
      exact (triangularAdj_irrefl a (hab' ▸ hab)).elim
    · have hab' : a = b := (hw a ha (had ▸ hd)).trans (hw b hb (hbc ▸ hc)).symm
      exact (triangularAdj_irrefl a (hab' ▸ hab)).elim
    · have hep : e ∈ p.support := by rcases he with rfl | rfl <;> assumption
      have heq : e ∈ q.support := by rcases he' with rfl | rfl <;> assumption
      simpa only [hw e hep heq] using hp.trans hpoint

/-- The two completion colors from single-site interpolation give the
literal unique-intersection property of the embedded polygonal traces. -/
theorem opposite_completion_traces_intersect_only_at_pivot
    (ω η : Configuration) (w : Site)
    (heq : ∀ a, a ≠ w → ω a = η a)
    {u v x y : Site} (p : triangularGraph.Walk u v) (q : triangularGraph.Walk x y)
    (hp : ∀ a ∈ p.support, ω a = true) (hq : ∀ a ∈ q.support, η a = false)
    {z : ℝ × ℝ} (hzp : z ∈ walkTrace p) (hzq : z ∈ walkTrace q) : z = point w := by
  apply walkTrace_intersection_only p q ?_ hzp hzq
  intro a ha haq
  by_contra hne
  have h := heq a hne
  simp only [hp a ha, hq a haq, Bool.true_eq_false] at h

#print axioms edge_interiors_same_edge
#print axioms edge_interior_no_vertex
#print axioms edgePoint_injective
#print axioms closed_edge_intersection
#print axioms disjoint_edges_do_not_cross
#print axioms disjoint_supports_disjoint_traces
#print axioms opposite_completion_traces_intersect_only_at_pivot

end ExceptionalTimes.TriangularPlane
