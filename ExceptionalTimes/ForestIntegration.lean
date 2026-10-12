import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Ring

/-!
Finite leaf integration with an explicit combinatorial elimination certificate.
The first remaining variable is either isolated, attached to one later variable,
or attached to one fixed root. Repeating this operation describes rooted forests
with at most one fixed root per component. No bound on a many-variable integral
is assumed: only nonnegativity, one-edge sums, and free-center masses enter.

Every finite acyclic graph with at most one marked root per component has such
an order. The graph's literal edge product is identified with the certified product.
-/

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestIntegration

variable {R X P : Type*}

/-- A certified leaf-elimination order. `none` leaves a free center; `inl j`
attaches the removed leaf to later variable `j`; `inr r` attaches it to fixed root `r`.
No step joins two existing components or two fixed roots. -/
inductive LeafOrder (R : Type*) : ℕ → Type _
  | nil : LeafOrder R 0
  | cons {n : ℕ} (parent : Option (Fin n ⊕ R)) (rest : LeafOrder R n) : LeafOrder R (n + 1)

/-- The actual parent of each variable vertex, in the full vertex indexing. -/
def LeafOrder.parent : {n : ℕ} → LeafOrder R n → Fin n → Option (Fin n ⊕ R)
  | _, .nil => Fin.elim0
  | _, .cons p F => Fin.cons (p.map (Sum.map Fin.succ id))
      (fun i => (F.parent i).map (Sum.map Fin.succ id))

/-- Each edge has its child removed strictly before its variable parent. -/
theorem LeafOrder.parent_later {n : ℕ} (F : LeafOrder R n) (i j : Fin n)
    (h : F.parent i = some (.inl j)) : i < j := by
  induction F with
  | nil => exact Fin.elim0 i
  | @cons n p F ih =>
    revert h
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      cases p with
      | none => simp [LeafOrder.parent] at h
      | some v =>
        cases v with
        | inl a =>
          simp [LeafOrder.parent] at h
          subst j
          exact Fin.succ_pos _
        | inr r => simp [LeafOrder.parent] at h
    · intro h
      cases hp : F.parent k with
      | none => simp [LeafOrder.parent, hp] at h
      | some v =>
        cases v with
        | inl a =>
          simp [LeafOrder.parent, hp] at h
          subst j
          exact Fin.succ_lt_succ_iff.mpr (ih k a hp)
        | inr r => simp [LeafOrder.parent, hp] at h

/-- Therefore the first variable has no edge coming from another remaining child. -/
theorem LeafOrder.no_parent_zero {n : ℕ} (F : LeafOrder R (n + 1)) (i : Fin (n + 1)) :
    F.parent i ≠ some (.inl 0) := by
  intro h
  exact (Fin.not_lt_zero i) (F.parent_later i 0 h)

def localFactor {n : ℕ} (p : Option (Fin n ⊕ R)) (position : X → P) (root : R → P)
    (K : X → P → ℝ) (a : X) (x : Fin n → X) : ℝ :=
  match p with
  | none => 1
  | some (.inl j) => K a (position (x j))
  | some (.inr r) => K a (root r)

/-- A literal array of edge factors, one per non-root variable; isolated/free
centers contribute the factor one. -/
def LeafOrder.factors (position : X → P) (root : R → P) :
    {n : ℕ} → LeafOrder R n → (Fin n → X → P → ℝ) → (Fin n → X) → Fin n → ℝ
  | _, .nil, _, _ => Fin.elim0
  | _, .cons p F, K, x => Fin.cons
      (localFactor p position root (K 0) (x 0) (fun j => x j.succ))
      (F.factors position root (fun j => K j.succ) (fun j => x j.succ))

noncomputable def integral [Fintype X] {n : ℕ} (F : LeafOrder R n)
    (position : X → P) (root : R → P) (μ : Fin n → X → ℝ) (K : Fin n → X → P → ℝ) : ℝ :=
  ∑ x : Fin n → X, (∏ i, μ i (x i)) * ∏ i, F.factors position root K x i

def stepBound {n : ℕ} (p : Option (Fin n ⊕ R)) (M C : ℝ) : ℝ :=
  match p with
  | none => M
  | some _ => C

def LeafOrder.bound : {n : ℕ} → LeafOrder R n → (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  | _, .nil, _, _ => 1
  | _, .cons p F, M, C => stepBound p (M 0) (C 0) *
      F.bound (fun j => M j.succ) (fun j => C j.succ)

def headTailEquiv (n : ℕ) (X : Type*) : X × (Fin n → X) ≃ (Fin (n + 1) → X) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun j => x j.succ)
  left_inv _ := rfl
  right_inv x := by funext i; exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem headTailEquiv_apply {n : ℕ} (a : X) (x : Fin n → X) :
    headTailEquiv n X (a, x) = Fin.cons a x := rfl

theorem integral_cons [Fintype X] {n : ℕ} (p : Option (Fin n ⊕ R)) (F : LeafOrder R n)
    (position : X → P) (root : R → P) (μ : Fin (n + 1) → X → ℝ)
    (K : Fin (n + 1) → X → P → ℝ) :
    integral (.cons p F) position root μ K =
      ∑ x : Fin n → X, ((∏ j, μ j.succ (x j)) *
        ∏ j, F.factors position root (fun j => K j.succ) x j) *
        ∑ a, μ 0 a * localFactor p position root (K 0) a x := by
  unfold integral
  rw [← (headTailEquiv n X).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [headTailEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, LeafOrder.factors]
  ring

theorem factors_nonneg {n : ℕ} (F : LeafOrder R n) (position : X → P) (root : R → P)
    (K : Fin n → X → P → ℝ) (hK : ∀ i a y, 0 ≤ K i a y) (x : Fin n → X) :
    ∀ i, 0 ≤ F.factors position root K x i := by
  induction F with
  | nil => intro i; exact Fin.elim0 i
  | @cons n p F ih =>
    intro i
    refine Fin.cases ?_ (fun j => ih _ (fun j => hK j.succ) _ j) i
    cases p with
    | none => exact zero_le_one
    | some v => cases v <;> exact hK 0 _ _

theorem local_sum_bound [Fintype X] {n : ℕ} (p : Option (Fin n ⊕ R))
    (position : X → P) (root : R → P) (μ : X → ℝ) (K : X → P → ℝ) (M C : ℝ)
    (hM : ∑ a, μ a ≤ M) (hC : ∀ y, ∑ a, μ a * K a y ≤ C) (x : Fin n → X) :
    (∑ a, μ a * localFactor p position root K a x) ≤ stepBound p M C := by
  cases p with
  | none => simpa [localFactor, stepBound] using hM
  | some v => cases v <;> exact hC _

/-- Leaf integration. Each selected edge is charged its one-variable bound;
each rootless component leaves exactly one free-center mass factor. -/
theorem integral_le_bound [Fintype X] {n : ℕ} (F : LeafOrder R n)
    (position : X → P) (root : R → P) (μ : Fin n → X → ℝ) (K : Fin n → X → P → ℝ)
    (M C : Fin n → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (hM0 : ∀ i, 0 ≤ M i) (hC0 : ∀ i, 0 ≤ C i)
    (hM : ∀ i, ∑ a, μ i a ≤ M i)
    (hC : ∀ i y, ∑ a, μ i a * K i a y ≤ C i) :
    integral F position root μ K ≤ F.bound M C := by
  induction F with
  | nil => simp [integral, LeafOrder.bound]
  | @cons n p F ih =>
    rw [integral_cons]
    calc
      _ ≤ ∑ x : Fin n → X, ((∏ j, μ j.succ (x j)) *
          ∏ j, F.factors position root (fun j => K j.succ) x j) *
          stepBound p (M 0) (C 0) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left
          (local_sum_bound p position root (μ 0) (K 0) (M 0) (C 0) (hM 0) (hC 0) x)
        exact mul_nonneg (Finset.prod_nonneg (fun j _ => hμ j.succ _))
          (Finset.prod_nonneg (fun j _ => factors_nonneg F position root _
            (fun j => hK j.succ) x j))
      _ = stepBound p (M 0) (C 0) *
          integral F position root (fun j => μ j.succ) (fun j => K j.succ) := by
        rw [← Finset.sum_mul, mul_comm]
        rfl
      _ ≤ F.bound (fun j => M j.succ) (fun j => C j.succ) *
          stepBound p (M 0) (C 0) := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right
          (ih _ _ _ _ (fun j => hμ j.succ) (fun j => hK j.succ)
            (fun j => hM0 j.succ) (fun j => hC0 j.succ)
            (fun j => hM j.succ) (fun j => hC j.succ))
        cases p <;> first | exact hM0 0 | exact hC0 0
      _ = _ := by rw [LeafOrder.bound, mul_comm]

def LeafOrder.edgeCount : {n : ℕ} → LeafOrder R n → ℕ
  | _, .nil => 0
  | _, .cons none F => F.edgeCount
  | _, .cons (some _) F => F.edgeCount + 1

def LeafOrder.freeCount : {n : ℕ} → LeafOrder R n → ℕ
  | _, .nil => 0
  | _, .cons none F => F.freeCount + 1
  | _, .cons (some _) F => F.freeCount

theorem LeafOrder.counts {n : ℕ} (F : LeafOrder R n) : F.edgeCount + F.freeCount = n := by
  induction F with
  | nil => rfl
  | cons p F ih => cases p <;> simpa [edgeCount, freeCount, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using congrArg Nat.succ ih

theorem LeafOrder.bound_uniform {n : ℕ} (F : LeafOrder R n) (M C : ℝ) :
    F.bound (fun _ => M) (fun _ => C) = C ^ F.edgeCount * M ^ F.freeCount := by
  induction F with
  | nil => simp [bound, edgeCount, freeCount]
  | cons p F ih => cases p <;>
      simp only [bound, stepBound, edgeCount, freeCount, ih, pow_succ] <;> ring

/-- Uniform forest estimate: one factor per edge and one mass per free component.
Fixed roots consume neither a variable integral nor a free-center mass factor. -/
theorem integral_le_uniform [Fintype X] {n : ℕ} (F : LeafOrder R n)
    (position : X → P) (root : R → P) (μ : Fin n → X → ℝ) (K : Fin n → X → P → ℝ)
    (M C : ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hM : ∀ i, ∑ a, μ i a ≤ M)
    (hC : ∀ i y, ∑ a, μ i a * K i a y ≤ C) :
    integral F position root μ K ≤ C ^ F.edgeCount * M ^ F.freeCount := by
  rw [← F.bound_uniform M C]
  exact integral_le_bound F position root μ K _ _ hμ hK (fun _ => hM0) (fun _ => hC0) hM hC

/-- Requiring distinct positions or additional Kruskal constraints can only
decrease the nonnegative forest integral. -/
theorem restricted_le_integral [Fintype X] {n : ℕ} (F : LeafOrder R n)
    (position : X → P) (root : R → P) (μ : Fin n → X → ℝ) (K : Fin n → X → P → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (D : (Fin n → X) → Prop) :
    (∑ x : Fin n → X, if D x then
      (∏ i, μ i (x i)) * ∏ i, F.factors position root K x i else 0) ≤
      integral F position root μ K := by
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hμ i _))
      (Finset.prod_nonneg (fun i _ => factors_nonneg F position root K hK x i))

section GraphLeaves

variable {V : Type*} [Fintype V]

/-- The marked vertices satisfy the exact one-fixed-root-per-component condition. -/
def RootsSeparated (G : SimpleGraph V) (fixed : V → Prop) : Prop :=
  ∀ u v, fixed u → fixed v → G.Reachable u v → u = v

omit [Fintype V] in
theorem roots_not_adj (G : SimpleGraph V) (fixed : V → Prop) (hroot : RootsSeparated G fixed)
    (u v : V) (hu : fixed u) (hv : fixed v) : ¬ G.Adj u v := by
  intro h
  exact h.ne (hroot u v hu hv h.reachable)

/-- Every finite forest with separated fixed roots and a free vertex has a free
vertex with at most one neighbor. This is the graph-theoretic leaf step. -/
theorem exists_free_leaf (G : SimpleGraph V) (hG : G.IsAcyclic) (fixed : V → Prop)
    (hroot : RootsSeparated G fixed) (hfree : ∃ v, ¬ fixed v) :
    ∃ v, ¬ fixed v ∧ ∀ a b, G.Adj v a → G.Adj v b → a = b := by
  classical
  obtain ⟨v, hv⟩ := hfree
  let c := G.connectedComponentMk v
  have hc : v ∈ c := rfl
  by_cases hs : Subsingleton c
  · let := hs
    refine ⟨v, hv, ?_⟩
    intro a b ha hb
    have ha' : a ∈ c := (c.mem_supp_congr_adj ha).mp hc
    have hb' : b ∈ c := (c.mem_supp_congr_adj hb).mp hc
    exact congrArg Subtype.val (Subsingleton.elim (⟨a, ha'⟩ : c) ⟨b, hb'⟩)
  · have : Nontrivial c := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨a, b, hab, ha, hb⟩ := (hG.isTree_connectedComponent c).exists_ne_and_degree_eq_one
    have chooseFree : ¬ fixed a.val ∨ ¬ fixed b.val := by
      by_contra hn
      have hra : fixed a.val := not_not.mp (fun h => hn (Or.inl h))
      have hrb : fixed b.val := not_not.mp (fun h => hn (Or.inr h))
      apply hab
      exact Subtype.ext (hroot a b hra hrb (c.reachable_of_mem_supp a.property b.property))
    have fromLeaf (a : c) (ha : c.toSimpleGraph.degree a = 1) (haf : ¬ fixed a.val) :
        ∃ v, ¬ fixed v ∧ ∀ x y, G.Adj v x → G.Adj v y → x = y := by
      refine ⟨a.val, haf, ?_⟩
      intro x y hx hy
      obtain ⟨z, _, hz⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp ha
      have hx' : x ∈ c := (c.mem_supp_congr_adj hx).mp a.property
      have hy' : y ∈ c := (c.mem_supp_congr_adj hy).mp a.property
      exact congrArg Subtype.val ((hz ⟨x, hx'⟩ hx).trans (hz ⟨y, hy'⟩ hy).symm)
    exact chooseFree.elim (fromLeaf a ha) (fromLeaf b hb)

/-- Every listed vertex is a leaf or isolated when it is removed; fixed roots
remain present at every stage. This predicate states only adjacency facts. -/
def Eliminates (G : SimpleGraph V) (fixed : V → Prop) : List V → Prop
  | [] => True
  | v :: L =>
      (∀ a b, (fixed a ∨ a ∈ L) → (fixed b ∨ b ∈ L) →
        G.Adj v a → G.Adj v b → a = b) ∧ Eliminates G fixed L

/-- A finite acyclic graph with at most one fixed root per component admits
a complete leaf-elimination list of any prescribed free-vertex subset. -/
theorem exists_elimination_list (G : SimpleGraph V) (hG : G.IsAcyclic)
    (fixed : V → Prop) (hroot : RootsSeparated G fixed) (s : Finset V)
    (hdis : ∀ v ∈ s, ¬ fixed v) :
    ∃ L : List V, L.Nodup ∧ (∀ v, v ∈ L ↔ v ∈ s) ∧ Eliminates G fixed L := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨[], List.nodup_nil, by simp, trivial⟩
    · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      let active : Set V := {v | fixed v ∨ v ∈ s}
      have hroots : RootsSeparated (G.induce active) (fun v => fixed v.val) := by
        intro a b ha hb hab
        apply Subtype.ext
        exact hroot a b ha hb (hab.map (SimpleGraph.Hom.comap Subtype.val G))
      obtain ⟨v, hv, hleaf⟩ := exists_free_leaf (G.induce active) (hG.induce active)
        (fun v => fixed v.val) hroots ⟨⟨u, Or.inr hu⟩, hdis u hu⟩
      have hvs : v.val ∈ s := v.property.resolve_left hv
      obtain ⟨L, hLn, hLm, hLe⟩ := ih (s.erase v.val) (Finset.erase_ssubset hvs)
        (fun w hw => hdis w (Finset.mem_of_mem_erase hw))
      refine ⟨v.val :: L, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨by simp [hLm], hLn⟩
      · intro w
        simp only [List.mem_cons, hLm, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, hw⟩)
          · exact hvs
          · exact hw
        · intro hw
          by_cases he : w = v.val
          · exact Or.inl he
          · exact Or.inr ⟨he, hw⟩
      · refine ⟨?_, hLe⟩
        intro a b ha hb hva hvb
        have active_of (w : V) (hw : fixed w ∨ w ∈ L) : w ∈ active := by
          rcases hw with hw | hw
          · exact Or.inl hw
          · exact Or.inr (Finset.mem_of_mem_erase ((hLm w).mp hw))
        exact congrArg Subtype.val (hleaf ⟨a, active_of a ha⟩ ⟨b, active_of b hb⟩ hva hvb)

/-- In particular, the entire variable set has a certified elimination order. -/
theorem exists_complete_elimination_list (G : SimpleGraph V) (hG : G.IsAcyclic)
    (fixed : V → Prop) (hroot : RootsSeparated G fixed) :
    ∃ L : List V, L.Nodup ∧ (∀ v, v ∈ L ↔ ¬ fixed v) ∧ Eliminates G fixed L := by
  classical
  simpa using exists_elimination_list G hG fixed hroot
    (Finset.univ.filter (fun v => ¬ fixed v)) (by simp)

def endpointLabel (fixed : V → Prop) (L : List V) : Fin L.length ⊕ {v // fixed v} → V
  | .inl i => L.get i
  | .inr r => r.val

omit [Fintype V] in
theorem endpointLabel_injective (fixed : V → Prop) (L : List V) (hL : L.Nodup)
    (hdis : ∀ v ∈ L, ¬ fixed v) : Function.Injective (endpointLabel fixed L) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (hL.injective_get hab)
    | inr r =>
      change L.get i = r.val at hab
      exact False.elim (hdis _ (List.get_mem _ _) (hab.symm ▸ r.property))
  | inr r =>
    cases b with
    | inl j =>
      change r.val = L.get j at hab
      exact False.elim (hdis _ (List.get_mem _ _) (hab ▸ r.property))
    | inr s => exact congrArg Sum.inr (Subtype.ext hab)

/-- Exact edge incidence is certified, not merely a bound on its integral. -/
def Encodes (G : SimpleGraph V) (fixed : V → Prop) :
    (L : List V) → LeafOrder {v // fixed v} L.length → Prop
  | [], .nil => True
  | v :: L, .cons p F =>
      (∀ q, G.Adj v (endpointLabel fixed L q) ↔ p = some q) ∧ Encodes G fixed L F

theorem elimination_encodes (G : SimpleGraph V) (fixed : V → Prop) (L : List V)
    (hL : L.Nodup) (hdis : ∀ v ∈ L, ¬ fixed v) (hElim : Eliminates G fixed L) :
    ∃ F : LeafOrder {v // fixed v} L.length, Encodes G fixed L F := by
  classical
  induction L with
  | nil => exact ⟨.nil, trivial⟩
  | cons v L ih =>
    obtain ⟨F, hF⟩ := ih hL.of_cons (fun w hw => hdis w (List.mem_cons_of_mem v hw)) hElim.2
    have hinj := endpointLabel_injective fixed L hL.of_cons
      (fun w hw => hdis w (List.mem_cons_of_mem v hw))
    have eligible (q : Fin L.length ⊕ {v // fixed v}) :
        fixed (endpointLabel fixed L q) ∨ endpointLabel fixed L q ∈ L := by
      cases q with
      | inl i => exact Or.inr (List.get_mem _ _)
      | inr r => exact Or.inl r.property
    by_cases he : ∃ q, G.Adj v (endpointLabel fixed L q)
    · obtain ⟨q, hq⟩ := he
      refine ⟨.cons (some q) F, ?_, hF⟩
      intro r
      constructor
      · intro hr
        exact congrArg some (hinj (hElim.1 _ _ (eligible q) (eligible r) hq hr))
      · intro hr
        have hqr : q = r := Option.some.inj hr
        simpa [← hqr] using hq
    · refine ⟨.cons none F, ?_, hF⟩
      intro q
      simp only [reduceCtorEq, iff_false]
      exact fun hq => he ⟨q, hq⟩

/-- Actual acyclic rooted graphs have certificates whose edge incidences agree
exactly with the graph, after listing the non-fixed vertices. -/
theorem exists_graph_encoding (G : SimpleGraph V) (hG : G.IsAcyclic)
    (fixed : V → Prop) (hroot : RootsSeparated G fixed) :
    ∃ (L : List V) (F : LeafOrder {v // fixed v} L.length),
      L.Nodup ∧ (∀ v, v ∈ L ↔ ¬ fixed v) ∧ Encodes G fixed L F := by
  obtain ⟨L, hL, hmem, hElim⟩ := exists_complete_elimination_list G hG fixed hroot
  obtain ⟨F, hF⟩ := elimination_encodes G fixed L hL (fun v hv => (hmem v).mp hv) hElim
  exact ⟨L, F, hL, hmem, hF⟩

def endpointPosition (fixed : V → Prop) (position : X → P) (root : {v // fixed v} → P)
    {n : ℕ} (x : Fin n → X) : Fin n ⊕ {v // fixed v} → P
  | .inl j => position (x j)
  | .inr r => root r

/-- Literal product of graph edge kernels: at each vertex, multiply the edges
to later variables and to fixed roots. Each variable-variable edge is used once. -/
noncomputable def graphProduct (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) :
    (L : List V) → (Fin L.length → X → P → ℝ) → (Fin L.length → X) → ℝ
  | [], _, _ => 1
  | v :: L, K, x =>
      (∏ q : Fin L.length ⊕ {v // fixed v}, if G.Adj v (endpointLabel fixed L q)
        then K 0 (x 0) (endpointPosition fixed position root (fun j => x j.succ) q) else 1) *
      graphProduct G fixed position root L (fun j => K j.succ) (fun j => x j.succ)

theorem encoded_product (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) (L : List V)
    (F : LeafOrder {v // fixed v} L.length) (hF : Encodes G fixed L F)
    (K : Fin L.length → X → P → ℝ) (x : Fin L.length → X) :
    graphProduct G fixed position root L K x = ∏ i, F.factors position root K x i := by
  classical
  induction L with
  | nil => cases F; simp [graphProduct]
  | cons v L ih =>
    cases F with
    | cons p F =>
      simp only [List.length_cons] at K x ⊢
      simp only [graphProduct, LeafOrder.factors]
      rw [Fin.prod_univ_succ (n := L.length)]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [ih F hF.2]
      congr 1
      simp_rw [hF.1]
      cases p with
      | none => simp [localFactor]
      | some q => cases q <;> simp [localFactor, endpointPosition]

/-- Number of literal edge factors in the ordered graph product. -/
noncomputable def graphEdgeCount (G : SimpleGraph V) (fixed : V → Prop) : List V → ℕ
  | [] => 0
  | v :: L => (Finset.univ.filter
      (fun q : Fin L.length ⊕ {v // fixed v} => G.Adj v (endpointLabel fixed L q))).card +
      graphEdgeCount G fixed L

theorem encoded_edgeCount (G : SimpleGraph V) (fixed : V → Prop) (L : List V)
    (F : LeafOrder {v // fixed v} L.length) (hF : Encodes G fixed L F) :
    graphEdgeCount G fixed L = F.edgeCount := by
  classical
  induction L with
  | nil => cases F; rfl
  | cons v L ih =>
    cases F with
    | cons p F =>
      rw [graphEdgeCount, ih F hF.2]
      simp_rw [hF.1]
      cases p with
      | none => simp [LeafOrder.edgeCount]
      | some q =>
        simp only [LeafOrder.edgeCount, Option.some.injEq]
        have he : (Finset.univ.filter (fun r => q = r)) = {q} := by
          ext r
          simp [eq_comm]
        rw [he, Finset.card_singleton, Nat.add_comm]

noncomputable def graphIntegral [Fintype X] (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) (L : List V)
    (μ : Fin L.length → X → ℝ) (K : Fin L.length → X → P → ℝ) : ℝ :=
  ∑ x : Fin L.length → X, (∏ i, μ i (x i)) * graphProduct G fixed position root L K x

/-- The graph expression is exactly the product expression that was integrated
by leaf elimination; no probabilistic factorization assertion is supplied as a premise. -/
theorem graphIntegral_eq [Fintype X] (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) (L : List V)
    (F : LeafOrder {v // fixed v} L.length) (hF : Encodes G fixed L F)
    (μ : Fin L.length → X → ℝ) (K : Fin L.length → X → P → ℝ) :
    graphIntegral G fixed position root L μ K = integral F position root μ K := by
  simp only [graphIntegral, integral, encoded_product G fixed position root L F hF]

theorem graphIntegral_le [Fintype X] (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) (L : List V)
    (F : LeafOrder {v // fixed v} L.length) (hF : Encodes G fixed L F)
    (μ : Fin L.length → X → ℝ) (K : Fin L.length → X → P → ℝ)
    (M C : ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hM : ∀ i, ∑ a, μ i a ≤ M)
    (hC : ∀ i y, ∑ a, μ i a * K i a y ≤ C) :
    graphIntegral G fixed position root L μ K ≤ C ^ F.edgeCount * M ^ F.freeCount := by
  rw [graphIntegral_eq G fixed position root L F hF]
  exact integral_le_uniform F position root μ K M C hμ hK hM0 hC0 hM hC

/-- The same estimate with the exponent identified as the graph's edge-factor
count and with one mass factor for each remaining free center. -/
theorem graphIntegral_le_count [Fintype X] (G : SimpleGraph V) (fixed : V → Prop)
    (position : X → P) (root : {v // fixed v} → P) (L : List V)
    (F : LeafOrder {v // fixed v} L.length) (hF : Encodes G fixed L F)
    (μ : Fin L.length → X → ℝ) (K : Fin L.length → X → P → ℝ)
    (M C : ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hK : ∀ i a y, 0 ≤ K i a y)
    (hM0 : 0 ≤ M) (hC0 : 0 ≤ C) (hM : ∀ i, ∑ a, μ i a ≤ M)
    (hC : ∀ i y, ∑ a, μ i a * K i a y ≤ C) :
    graphIntegral G fixed position root L μ K ≤
      C ^ graphEdgeCount G fixed L * M ^ (L.length - graphEdgeCount G fixed L) := by
  rw [encoded_edgeCount G fixed L F hF]
  have hfree : L.length - F.edgeCount = F.freeCount := by
    exact (congrArg (fun n => n - F.edgeCount) F.counts).symm.trans
      (Nat.add_sub_cancel_left F.edgeCount F.freeCount)
  rw [hfree]
  exact graphIntegral_le G fixed position root L F hF μ K M C hμ hK hM0 hC0 hM hC

/-- Complete finite-forest integration theorem, with no elimination certificate
assumed. The order is constructed from graph acyclicity and separated roots.
Its edge count is at most the number of integrated variables. -/
theorem finite_forest_integral [Fintype X] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (fixed : V → Prop) (hroot : RootsSeparated G fixed) :
    ∃ L : List V, L.Nodup ∧ (∀ v, v ∈ L ↔ ¬ fixed v) ∧
      graphEdgeCount G fixed L ≤ L.length ∧
      ∀ (position : X → P) (root : {v // fixed v} → P)
        (μ : Fin L.length → X → ℝ) (K : Fin L.length → X → P → ℝ) (M C : ℝ),
        (∀ i a, 0 ≤ μ i a) → (∀ i a y, 0 ≤ K i a y) → 0 ≤ M → 0 ≤ C →
        (∀ i, ∑ a, μ i a ≤ M) → (∀ i y, ∑ a, μ i a * K i a y ≤ C) →
        graphIntegral G fixed position root L μ K ≤
          C ^ graphEdgeCount G fixed L * M ^ (L.length - graphEdgeCount G fixed L) := by
  obtain ⟨L, F, hL, hmem, hF⟩ := exists_graph_encoding G hG fixed hroot
  refine ⟨L, hL, hmem, ?_, ?_⟩
  · rw [encoded_edgeCount G fixed L F hF]
    exact (Nat.le_add_right F.edgeCount F.freeCount).trans_eq F.counts
  · intro position root μ K M C hμ hK hM0 hC0 hM hC
    exact graphIntegral_le_count G fixed position root L F hF μ K M C hμ hK hM0 hC0 hM hC

end GraphLeaves

#print axioms integral_le_uniform
#print axioms exists_free_leaf
#print axioms exists_complete_elimination_list
#print axioms exists_graph_encoding
#print axioms graphIntegral_le
#print axioms finite_forest_integral

end ExceptionalTimes.ForestIntegration
