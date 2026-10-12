import ExceptionalTimes.Model
import ExceptionalTimes.Necklace

/-! # Concrete annular vertex sets and the four-apex gap graph

This file begins the explicit correspondence between the annular argument and
the finite Hex graph. No assertion of planarity or existence of an annular
necklace is included. The original lattice vertices are retained without
contracting their boundary chains, so their colors are not identified.
-/

namespace ExceptionalTimes.Annulus

open Necklace

/-- Hexagonal graph distance in the triangular-lattice coordinate convention. -/
def hexRadius (v : Site) : ℤ := max (max |v.1| |v.2|) |v.1 + v.2|

def closedAnnulus (r R : ℕ) : Set Site :=
  {v | (r : ℤ) ≤ hexRadius v ∧ hexRadius v ≤ (R : ℤ)}

def hexBoundary (r : ℕ) : Set Site := {v | hexRadius v = (r : ℤ)}

theorem closedAnnulus_subset_box (r R : ℕ) : closedAnnulus r R ⊆ (latticeBox R : Set Site) := by
  intro v hv
  have hrad : hexRadius v ≤ (R : ℤ) := hv.2
  have hx : |v.1| ≤ (R : ℤ) := (le_max_left _ _).trans ((le_max_left _ _).trans hrad)
  have hy : |v.2| ≤ (R : ℤ) := (le_max_right _ _).trans ((le_max_left _ _).trans hrad)
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  simpa only [latticeBox, Finset.product_eq_sprod, Finset.mem_coe,
    Finset.mem_product, Finset.mem_Icc] using And.intro hx' hy'

theorem closedAnnulus_finite (r R : ℕ) : (closedAnnulus r R).Finite :=
  (latticeBox R).finite_toSet.subset (closedAnnulus_subset_box r R)

theorem hexBoundaries_disjoint {r R : ℕ} (hne : r ≠ R) :
    Disjoint (hexBoundary r) (hexBoundary R) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have heq : (r : ℤ) = (R : ℤ) := hv.symm.trans hw
  exact hne (by exact_mod_cast heq)

/-- Original sites and four distinct artificial apex vertices. -/
abbrev GapVertex := Site ⊕ Fin 4

def apex (i : Fin 4) : GapVertex := Sum.inr i

/-- The outer apex edges form the four-cycle, with no radial diagonal. -/
def apexAdjacent (i j : Fin 4) : Prop :=
  (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val

instance (i j : Fin 4) : Decidable (apexAdjacent i j) :=
  inferInstanceAs (Decidable ((i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val))

theorem apexAdjacent_symm {i j : Fin 4} (h : apexAdjacent i j) : apexAdjacent j i := by
  exact h.symm

theorem apexAdjacent_irrefl (i : Fin 4) : ¬apexAdjacent i i := by
  exact (show ∀ j : Fin 4, ¬apexAdjacent j j by decide) i

/-- `core` is the set of original gap sites and `side i` is its ith boundary
arc. The side sets are not contracted. Indices 0,2 are lateral; 1,3 radial. -/
def gapAdjacent (core : Set Site) (side : Fin 4 → Set Site) : GapVertex → GapVertex → Prop
  | .inl x, .inl y => TriangularAdj x y ∧ x ∈ core ∧ y ∈ core
  | .inr i, .inl y => y ∈ side i ∧ y ∈ core
  | .inl x, .inr j => x ∈ side j ∧ x ∈ core
  | .inr i, .inr j => apexAdjacent i j

def gapGraph (core : Set Site) (side : Fin 4 → Set Site) : SimpleGraph GapVertex where
  Adj := gapAdjacent core side
  symm := ⟨by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact ⟨triangularAdj_symm h.1, h.2.2, h.2.1⟩
      | inr j => exact h
    | inr i =>
      cases y with
      | inl y => exact h
      | inr j => exact apexAdjacent_symm h⟩
  loopless := ⟨by
    intro x h
    cases x with
    | inl x => exact triangularAdj_irrefl x h.1
    | inr i => exact apexAdjacent_irrefl i h⟩

@[simp]
theorem gapGraph_original_adj (core : Set Site) (side : Fin 4 → Set Site) (x y : Site) :
    (gapGraph core side).Adj (.inl x) (.inl y) ↔
      TriangularAdj x y ∧ x ∈ core ∧ y ∈ core := Iff.rfl

@[simp]
theorem gapGraph_apex_original_adj (core : Set Site) (side : Fin 4 → Set Site)
    (i : Fin 4) (x : Site) :
    (gapGraph core side).Adj (apex i) (.inl x) ↔ x ∈ side i ∧ x ∈ core := Iff.rfl

/-- A walk cannot enter an original site outside the prescribed gap. -/
theorem original_members_in_core (core : Set Site) (side : Fin 4 → Set Site)
    {u v : GapVertex} (p : (gapGraph core side).Walk u v)
    (hstart : ∀ x : Site, u = .inl x → x ∈ core) :
    ∀ x : Site, (.inl x : GapVertex) ∈ p.support → x ∈ core := by
  induction p with
  | nil =>
    intro x hx
    exact hstart x (List.mem_singleton.mp hx).symm
  | @cons u v w hadj p ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · exact hstart x hx.symm
    · apply ih ?_ x hx
      intro y hy
      subst v
      cases u with
      | inl u => exact hadj.2.2
      | inr i => exact hadj.2

theorem no_radial_apex_edge (core : Set Site) (side : Fin 4 → Set Site) :
    ¬(gapGraph core side).Adj (apex 1) (apex 3) := by
  change ¬apexAdjacent 1 3
  decide

theorem apex_zero_ne_one : apex 0 ≠ apex 1 := by decide
theorem apex_one_ne_three : apex 1 ≠ apex 3 := by decide
theorem apex_two_ne_three : apex 2 ≠ apex 3 := by decide

/-- A top-apex neighbor avoiding the two lateral apices is an actual original
site, on the top boundary arc. There is no zero-interior radial shortcut. -/
theorem top_neighbor_original (core : Set Site) (side : Fin 4 → Set Site)
    {v : GapVertex} (h : (gapGraph core side).Adj (apex 1) v)
    (hleft : v ≠ apex 0) (hright : v ≠ apex 2) :
    ∃ x : Site, v = .inl x ∧ x ∈ side 1 ∧ x ∈ core := by
  cases v with
  | inl x => exact ⟨x, rfl, h.1, h.2⟩
  | inr i =>
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (show ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by decide) i
    rcases hi with rfl | rfl | rfl | rfl
    · exact False.elim (hleft rfl)
    · exact False.elim (h.ne rfl)
    · exact False.elim (hright rfl)
    · exact False.elim (no_radial_apex_edge core side h)

theorem bottom_neighbor_original (core : Set Site) (side : Fin 4 → Set Site)
    {v : GapVertex} (h : (gapGraph core side).Adj (apex 3) v)
    (hleft : v ≠ apex 0) (hright : v ≠ apex 2) :
    ∃ x : Site, v = .inl x ∧ x ∈ side 3 ∧ x ∈ core := by
  cases v with
  | inl x => exact ⟨x, rfl, h.1, h.2⟩
  | inr i =>
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (show ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by decide) i
    rcases hi with rfl | rfl | rfl | rfl
    · exact False.elim (hleft rfl)
    · exact False.elim (no_radial_apex_edge core side h.symm)
    · exact False.elim (hright rfl)
    · exact False.elim (h.ne rfl)

def originalVertices : Set GapVertex := {v | ∃ x : Site, v = .inl x}

theorem original_of_not_apices {v : GapVertex}
    (h0 : v ≠ apex 0) (h1 : v ≠ apex 1) (h2 : v ≠ apex 2) (h3 : v ≠ apex 3) :
    v ∈ originalVertices := by
  cases v with
  | inl x => exact ⟨x, rfl⟩
  | inr i =>
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (show ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by decide) i
    rcases hi with rfl | rfl | rfl | rfl
    · exact False.elim (h0 rfl)
    · exact False.elim (h1 rfl)
    · exact False.elim (h2 rfl)
    · exact False.elim (h3 rfl)

theorem path_start_not_mem_tail {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hn : ¬p.Nil) : u ∉ p.tail.support := by
  have hnodup := hp.support_nodup
  rw [← p.cons_support_tail hn] at hnodup
  exact (List.nodup_cons.mp hnodup).1

theorem path_end_not_mem_dropLast {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (hn : ¬p.Nil) : v ∉ p.dropLast.support := by
  have hnodup := hp.support_nodup
  rw [← p.support_dropLast_concat hn] at hnodup
  have hcross := (List.nodup_append.mp hnodup).2.2
  intro hv
  exact hcross v hv v (by simp) rfl

/-- Removing the two radial apex vertices from a simple radial path gives a
simple path of original sites between the original radial boundary arcs.
No boundary chain is contracted and every retained vertex was on the input
path, so all original colors are preserved. Proper-boundary trimming is a
separate next step. -/
theorem remove_radial_apices (core : Set Site) (side : Fin 4 → Set Site)
    (p : (gapGraph core side).Walk (apex 1) (apex 3)) (hp : p.IsPath)
    (hlateral : ∀ v ∈ p.support, v ≠ apex 0 ∧ v ≠ apex 2) :
    ∃ x ∈ side 1, ∃ y ∈ side 3,
      ∃ q : (gapGraph core side).Walk (.inl x) (.inl y),
        q.IsPath ∧ ∀ v ∈ q.support, v ∈ originalVertices ∧ v ∈ p.support := by
  have hn : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne apex_one_ne_three
  have hsnd : p.snd ∈ p.support := p.getVert_mem_support 1
  obtain ⟨x, hx, hxtop, _⟩ := top_neighbor_original core side (p.adj_snd hn)
    (hlateral _ hsnd).1 (hlateral _ hsnd).2
  let t := p.tail
  have htpath : t.IsPath := hp.drop 1
  have htneq : p.snd ≠ apex 3 := by rw [hx]; intro h; cases h
  have htn : ¬t.Nil := SimpleGraph.Walk.not_nil_of_ne htneq
  have htsub : ∀ v ∈ t.support, v ∈ p.support := by
    intro v hv
    rw [p.support_tail_of_not_nil hn] at hv
    exact List.mem_of_mem_tail hv
  have hpen : t.penultimate ∈ p.support := htsub _ (t.getVert_mem_support (t.length - 1))
  obtain ⟨y, hy, hybottom, _⟩ := bottom_neighbor_original core side
    (t.adj_penultimate htn).symm (hlateral _ hpen).1 (hlateral _ hpen).2
  have hmidpath : t.dropLast.IsPath := htpath.take (t.length - 1)
  have hmidsub : ∀ v ∈ t.dropLast.support, v ∈ t.support := by
    intro v hv
    rw [t.support_dropLast htn] at hv
    exact List.mem_of_mem_dropLast hv
  have hreal : ∀ v ∈ t.dropLast.support, v ∈ originalVertices ∧ v ∈ p.support := by
    intro v hv
    have hvp := htsub v (hmidsub v hv)
    have h01 := hlateral v hvp
    have hvtop : v ≠ apex 1 := by
      intro heq
      subst v
      exact path_start_not_mem_tail p hp hn (hmidsub _ hv)
    have hvbottom : v ≠ apex 3 := by
      intro heq
      subst v
      exact path_end_not_mem_dropLast t htpath htn hv
    exact ⟨original_of_not_apices h01.1 hvtop h01.2 hvbottom, hvp⟩
  refine ⟨x, hxtop, y, hybottom, t.dropLast.copy hx hy, ?_, ?_⟩
  · simpa using hmidpath
  · intro v hv
    exact hreal v (by simpa using hv)

def originalSite (v : originalVertices) : Site :=
  match v.1 with
  | .inl x => x
  | .inr _ => (0, 0)

theorem originalSite_spec (v : originalVertices) : Sum.inl (originalSite v) = v.1 := by
  obtain ⟨v, ⟨x, rfl⟩⟩ := v
  rfl

theorem originalSite_injective : Function.Injective originalSite := by
  intro u v h
  apply Subtype.ext
  rw [← originalSite_spec u, ← originalSite_spec v, h]

def originalProjectionHom (core : Set Site) (side : Fin 4 → Set Site) :
    (gapGraph core side).induce originalVertices →g triangularGraph where
  toFun := originalSite
  map_rel' := by
    intro u v huv
    obtain ⟨u, ⟨x, rfl⟩⟩ := u
    obtain ⟨v, ⟨y, rfl⟩⟩ := v
    exact huv.1

/-- Drop the artificial sum-type wrapper from an original-site-supported walk.
Every edge is an actual triangular-lattice edge. -/
def originalWalk (core : Set Site) (side : Fin 4 → Set Site) {x y : Site}
    (q : (gapGraph core side).Walk (.inl x) (.inl y))
    (hreal : ∀ v ∈ q.support, v ∈ originalVertices) : triangularGraph.Walk x y :=
  (q.induce originalVertices hreal).map (originalProjectionHom core side)

theorem originalWalk_isPath (core : Set Site) (side : Fin 4 → Set Site) {x y : Site}
    (q : (gapGraph core side).Walk (.inl x) (.inl y))
    (hreal : ∀ v ∈ q.support, v ∈ originalVertices) (hq : q.IsPath) :
    (originalWalk core side q hreal).IsPath := by
  have hind : (q.induce originalVertices hreal).IsPath :=
    SimpleGraph.Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
      (by simpa using hq)
  exact hind.map (show Function.Injective (originalProjectionHom core side) from
    originalSite_injective)

set_option backward.isDefEq.respectTransparency.types false in
theorem originalWalk_support (core : Set Site) (side : Fin 4 → Set Site) {x y z : Site}
    (q : (gapGraph core side).Walk (.inl x) (.inl y))
    (hreal : ∀ v ∈ q.support, v ∈ originalVertices)
    (hz : z ∈ (originalWalk core side q hreal).support) : (.inl z : GapVertex) ∈ q.support := by
  have hsupp : (originalWalk core side q hreal).support =
      (q.induce originalVertices hreal).support.map (originalProjectionHom core side) :=
    SimpleGraph.Walk.support_map _ _
  rw [hsupp, List.mem_map] at hz
  obtain ⟨v, hv, hvz⟩ := hz
  have hvq : v.1 ∈ q.support := by
    simpa [SimpleGraph.Walk.support_induce] using hv
  have hvz' : originalSite v = z := hvz
  have hv_eq : (.inl z : GapVertex) = v.1 := by rw [← hvz']; exact originalSite_spec v
  rw [hv_eq]
  exact hvq

/-- The concrete path-removal result with colors: a white radial path through
the augmented gap gives an actual white triangular-lattice walk between the
uncontracted radial boundary arcs. Its endpoints may still need the usual
first/last-boundary trimming to become a proper arm. -/
theorem white_radial_apices_give_lattice_walk
    (core : Set Site) (side : Fin 4 → Set Site) (coloring : Configuration)
    (p : (gapGraph core side).Walk (apex 1) (apex 3)) (hp : p.IsPath)
    (hlateral : ∀ v ∈ p.support, v ≠ apex 0 ∧ v ≠ apex 2)
    (hwhite : ∀ x : Site, (.inl x : GapVertex) ∈ p.support → coloring x = false) :
    ∃ x ∈ side 1, ∃ y ∈ side 3, ∃ q : triangularGraph.Walk x y,
      ∀ z ∈ q.support, coloring z = false := by
  obtain ⟨x, hx, y, hy, q, _, hreal⟩ := remove_radial_apices core side p hp hlateral
  let q' := originalWalk core side q (fun v hv => (hreal v hv).1)
  refine ⟨x, hx, y, hy, q', ?_⟩
  intro z hz
  have hzq := originalWalk_support core side q (fun v hv => (hreal v hv).1) hz
  exact hwhite z (hreal (.inl z) hzq).2

/-- The projection retains simplicity, gap membership, original color, and
membership in the input path. -/
theorem white_radial_apices_give_lattice_path
    (core : Set Site) (side : Fin 4 → Set Site) (coloring : Configuration)
    (p : (gapGraph core side).Walk (apex 1) (apex 3)) (hp : p.IsPath)
    (hlateral : ∀ v ∈ p.support, v ≠ apex 0 ∧ v ≠ apex 2)
    (hwhite : ∀ x : Site, (.inl x : GapVertex) ∈ p.support → coloring x = false) :
    ∃ x ∈ side 1, ∃ y ∈ side 3, ∃ q : triangularGraph.Walk x y,
      q.IsPath ∧ ∀ z ∈ q.support,
        z ∈ core ∧ coloring z = false ∧ (.inl z : GapVertex) ∈ p.support := by
  obtain ⟨x, hx, y, hy, q, hq, hreal⟩ := remove_radial_apices core side p hp hlateral
  let q' := originalWalk core side q (fun v hv => (hreal v hv).1)
  refine ⟨x, hx, y, hy, q', originalWalk_isPath core side q _ hq, ?_⟩
  intro z hz
  have hzq := originalWalk_support core side q (fun v hv => (hreal v hv).1) hz
  have hzp := (hreal (.inl z) hzq).2
  exact ⟨original_members_in_core core side p (by intro x h; cases h) z hzp,
    hwhite z hzp, hzp⟩

/-- A simple path between two sets contains a contiguous simple subpath whose
only contacts with either set are its respective endpoints. Choosing a shortest
eligible subwalk implements the last-departure/first-arrival trimming. -/
theorem trim_path_between_sets {V : Type*} {G : SimpleGraph V} {u v : V}
    (A B : Set V) (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ A) (hv : v ∈ B) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ q : G.Walk x y,
      q.IsPath ∧ q.IsSubwalk p ∧
      (∀ z ∈ q.support, z ∈ A → z = x) ∧
      (∀ z ∈ q.support, z ∈ B → z = y) := by
  classical
  let eligible : ℕ → Prop := fun n =>
    ∃ x ∈ A, ∃ y ∈ B, ∃ q : G.Walk x y, q.length = n ∧ q.IsSubwalk p
  have hex : ∃ n, eligible n := ⟨p.length, u, hu, v, hv, p, rfl, p.isSubwalk_rfl⟩
  obtain ⟨x, hx, y, hy, q, hlen, hsub⟩ := Nat.find_spec hex
  refine ⟨x, hx, y, hy, q, SimpleGraph.Walk.isPath_of_isSubwalk hsub hp, hsub, ?_, ?_⟩
  · intro z hz hzA
    by_contra hne
    have hmin : Nat.find hex ≤ (q.dropUntil z hz).length :=
      Nat.find_min' hex ⟨z, hzA, y, hy, q.dropUntil z hz, rfl,
        (q.isSubwalk_dropUntil hz).trans hsub⟩
    have hlt := q.length_dropUntil_lt_length hz hne
    omega
  · intro z hz hzB
    by_contra hne
    have hmin : Nat.find hex ≤ (q.takeUntil z hz).length :=
      Nat.find_min' hex ⟨x, hx, z, hzB, q.takeUntil z hz, rfl,
        (q.isSubwalk_takeUntil hz).trans hsub⟩
    have hlt := q.length_takeUntil_lt_length hz hne
    omega

/-- If the gap lies in an annulus and its two uncontracted radial sides lie on
distinct hexagonal boundaries, apex removal followed by trimming gives a
nontrivial proper white lattice path, with strictly intermediate interior radii.
All retained vertices lie in the prescribed gap and on the original input path.
This is a conditional path-conversion theorem; it does not construct the gap or
establish its planar Hex hypotheses. -/
theorem white_radial_apices_give_proper_path
    (core : Set Site) (side : Fin 4 → Set Site) (coloring : Configuration)
    {r R : ℕ} (hrR : r ≠ R)
    (hcore : core ⊆ closedAnnulus r R)
    (htop : side 1 ⊆ hexBoundary r) (hbottom : side 3 ⊆ hexBoundary R)
    (p : (gapGraph core side).Walk (apex 1) (apex 3)) (hp : p.IsPath)
    (hlateral : ∀ v ∈ p.support, v ≠ apex 0 ∧ v ≠ apex 2)
    (hwhite : ∀ x : Site, (.inl x : GapVertex) ∈ p.support → coloring x = false) :
    ∃ x ∈ hexBoundary r, ∃ y ∈ hexBoundary R, ∃ q : triangularGraph.Walk x y,
      q.IsPath ∧ ¬q.Nil ∧
      (∀ z ∈ q.support, z ∈ core ∧ coloring z = false ∧
        (.inl z : GapVertex) ∈ p.support) ∧
      (∀ z ∈ q.support, z ∈ hexBoundary r → z = x) ∧
      (∀ z ∈ q.support, z ∈ hexBoundary R → z = y) ∧
      (∀ z ∈ q.support, z ≠ x → z ≠ y →
        (r : ℤ) < hexRadius z ∧ hexRadius z < (R : ℤ)) := by
  obtain ⟨u, hu, v, hv, q, hq, hsupport⟩ :=
    white_radial_apices_give_lattice_path core side coloring p hp hlateral hwhite
  obtain ⟨x, hx, y, hy, q', hq', hsub, hinner, houter⟩ :=
    trim_path_between_sets (hexBoundary r) (hexBoundary R) q hq (htop hu) (hbottom hv)
  have hxy : x ≠ y := by
    intro h
    exact Set.disjoint_left.mp (hexBoundaries_disjoint hrR) hx (h ▸ hy)
  refine ⟨x, hx, y, hy, q', hq', SimpleGraph.Walk.not_nil_of_ne hxy, ?_, hinner, houter, ?_⟩
  · intro z hz
    exact hsupport z (hsub.support_subset hz)
  · intro z hz hzx hzy
    have hbounds := hcore (hsupport z (hsub.support_subset hz)).1
    have hinner_ne : hexRadius z ≠ (r : ℤ) := fun heq => hzx (hinner z hz heq)
    have houter_ne : hexRadius z ≠ (R : ℤ) := fun heq => hzy (houter z hz heq)
    exact ⟨lt_of_le_of_ne hbounds.1 (Ne.symm hinner_ne), lt_of_le_of_ne hbounds.2 houter_ne⟩

#print axioms remove_radial_apices
#print axioms white_radial_apices_give_lattice_path
#print axioms trim_path_between_sets
#print axioms white_radial_apices_give_proper_path

end ExceptionalTimes.Annulus
