import ExceptionalTimes.NecklaceDictionary
import ExceptionalTimes.HexCells
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected

/-!
Closed-cell/graph crossing equivalence. The topological direction uses
finite closed-cover connectivity, proved here from connected-set
separation. The cell hypotheses can be instantiated by literal hexagons;
no path traversal or planar crossing assertion is an input.
-/

open scoped Classical
open Set Relation

namespace ExceptionalTimes.PairSquareSewing

theorem finite_closed_cover_chain {X I : Type*} [TopologicalSpace X] [Finite I]
    (cell : I → Set X) (hclosed : ∀ i, IsClosed (cell i))
    (K : Set X) (hK : IsPreconnected K) (hcover : K ⊆ ⋃ i, cell i)
    (i j : I) (hi : (K ∩ cell i).Nonempty) (hj : (K ∩ cell j).Nonempty) :
    ReflTransGen (fun a b => (cell a ∩ cell b).Nonempty) i j := by
  classical
  by_contra hij
  let S : Set I := {k | ReflTransGen (fun a b => (cell a ∩ cell b).Nonempty) i k}
  let U : Set X := ⋃ k ∈ S, cell k
  let V : Set X := ⋃ k ∈ Sᶜ, cell k
  have hU : IsClosed U := S.toFinite.isClosed_biUnion (fun k _ => hclosed k)
  have hV : IsClosed V := Sᶜ.toFinite.isClosed_biUnion (fun k _ => hclosed k)
  have hsplit : K ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover hx)
    by_cases hs : k ∈ S
    · exact Or.inl (mem_iUnion₂_of_mem hs hk)
    · exact Or.inr (mem_iUnion₂_of_mem hs hk)
  obtain ⟨a, haK, hai⟩ := hi
  obtain ⟨b, hbK, hbj⟩ := hj
  have hiS : i ∈ S := ReflTransGen.refl
  have hjS : j ∈ Sᶜ := hij
  have hKU : (K ∩ U).Nonempty := ⟨a, haK, mem_iUnion₂_of_mem hiS hai⟩
  have hKV : (K ∩ V).Nonempty := ⟨b, hbK, mem_iUnion₂_of_mem hjS hbj⟩
  obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_closed_iff.mp hK U V hU hV hsplit hKU hKV
  obtain ⟨u, huS, hxu⟩ := mem_iUnion₂.mp hxU
  obtain ⟨v, hvS, hxv⟩ := mem_iUnion₂.mp hxV
  exact hvS (huS.tail ⟨x, hxu, hxv⟩)

variable {X : Type*} [TopologicalSpace X]

def blackCellUnion (cell : Site → Set X) (Q : GraphQuad) (ω : Configuration) : Set X :=
  {p | ∃ v ∈ Q.domain, ω v = true ∧ p ∈ cell v}

/-- A connected subset of the black closed cells joins the two terminal
rows. The terminal cells themselves are required to be black and in
the domain, matching the graph terminals exactly. -/
def CellCrossing (cell : Site → Set X) (Q : GraphQuad) (ω : Configuration) : Prop :=
  ∃ K : Set X, IsPreconnected K ∧ K ⊆ blackCellUnion cell Q ω ∧
    ∃ u ∈ Q.firstSide, u ∈ Q.domain ∧ ω u = true ∧ (K ∩ cell u).Nonempty ∧
    ∃ v ∈ Q.secondSide, v ∈ Q.domain ∧ ω v = true ∧ (K ∩ cell v).Nonempty

/-- Any connected black-cell crossing yields an actual supported graph
walk when the literal cell intersection graph is triangular adjacency. -/
theorem cellCrossing_to_graphCrossing (cell : Site → Set X)
    (hclosed : ∀ v, IsClosed (cell v))
    (hinter : ∀ u v, (cell u ∩ cell v).Nonempty → u = v ∨ TriangularAdj u v)
    (Q : GraphQuad) (ω : Configuration) (h : CellCrossing cell Q ω) : Q.Crossing ω := by
  classical
  obtain ⟨K, hK, hcover, u, hu, huD, huB, huK, v, hv, hvD, hvB, hvK⟩ := h
  let J := {w : ↥Q.domain // ω w = true}
  let C : J → Set X := fun w => cell w.1.1
  let ui : J := ⟨⟨u, huD⟩, huB⟩
  let vi : J := ⟨⟨v, hvD⟩, hvB⟩
  have hcover' : K ⊆ ⋃ w : J, C w := by
    intro p hp
    obtain ⟨w, hwD, hwB, hpw⟩ := hcover hp
    exact mem_iUnion_of_mem (⟨⟨w, hwD⟩, hwB⟩ : J) hpw
  have hchain := finite_closed_cover_chain C (fun w => hclosed w.1.1) K hK hcover'
    ui vi huK hvK
  have lift {a b : J} (hc : ReflTransGen (fun c d : J => (C c ∩ C d).Nonempty) a b) :
      ∃ p : triangularGraph.Walk a.1.1 b.1.1,
        ∀ z ∈ p.support, z ∈ Q.domain ∧ ω z = true := by
    induction hc with
    | refl =>
      refine ⟨.nil, ?_⟩
      intro z hz
      have hz' : z = a.1.1 := by simpa using hz
      subst z
      exact ⟨a.1.2, a.2⟩
    | @tail b c _ hbc ih =>
      obtain ⟨p, hp⟩ := ih
      rcases hinter b.1.1 c.1.1 hbc with heq | hadj
      · have heq' : b = c := Subtype.ext (Subtype.ext heq)
        subst c
        exact ⟨p, hp⟩
      · refine ⟨p.concat hadj, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_concat p hadj] at hz
        have hz' : z ∈ p.support ∨ z = c.1.1 := by
          simpa only [List.mem_append, List.mem_singleton] using hz
        rcases hz' with hz | rfl
        · exact hp z hz
        · exact ⟨c.1.2, c.2⟩
  obtain ⟨p, hp⟩ := lift hchain
  exact ⟨u, hu, v, hv, p, hp⟩

def walkCellUnion (cell : Site → Set X) {u v : Site}
    (p : triangularGraph.Walk u v) : Set X :=
  match p with
  | .nil => cell u
  | @SimpleGraph.Walk.cons _ _ a _ _ _ tail => cell a ∪ walkCellUnion cell tail

omit [TopologicalSpace X] in
theorem walkCellUnion_start (cell : Site → Set X) {u v : Site}
    (p : triangularGraph.Walk u v) : cell u ⊆ walkCellUnion cell p := by
  cases p with
  | nil => exact Subset.rfl
  | cons _ _ => exact subset_union_left

omit [TopologicalSpace X] in
theorem walkCellUnion_end (cell : Site → Set X) {u v : Site}
    (p : triangularGraph.Walk u v) : cell v ⊆ walkCellUnion cell p := by
  induction p with
  | nil => exact Subset.rfl
  | cons _ _ ih => exact ih.trans subset_union_right

theorem walkCellUnion_preconnected (cell : Site → Set X)
    (hconn : ∀ v, IsPreconnected (cell v))
    (hinter : ∀ u v, TriangularAdj u v → (cell u ∩ cell v).Nonempty)
    {u v : Site} (p : triangularGraph.Walk u v) : IsPreconnected (walkCellUnion cell p) := by
  induction p with
  | nil => exact hconn _
  | @cons a b c hab p ih =>
    obtain ⟨x, hxa, hxb⟩ := hinter a b hab
    exact (hconn a).union' ⟨x, hxa, walkCellUnion_start cell p hxb⟩ ih

omit [TopologicalSpace X] in
theorem walkCellUnion_subset (cell : Site → Set X) (Q : GraphQuad) (ω : Configuration)
    {u v : Site} (p : triangularGraph.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ Q.domain ∧ ω z = true) :
    walkCellUnion cell p ⊆ blackCellUnion cell Q ω := by
  induction p with
  | @nil w =>
    intro x hx
    exact ⟨w, (hp w (by simp)).1, (hp w (by simp)).2, hx⟩
  | @cons a b c hab p ih =>
    intro x hx
    rcases hx with hx | hx
    · exact ⟨a, (hp a (by simp)).1, (hp a (by simp)).2, hx⟩
    · exact ih (fun z hz => hp z (by simp [hz])) hx

/-- Every actual graph crossing gives a connected crossing in the full
closed-cell union; no clipping to an unrelated Euclidean rectangle is used. -/
theorem graphCrossing_to_cellCrossing (cell : Site → Set X)
    (hconn : ∀ v, IsConnected (cell v))
    (hinter : ∀ u v, TriangularAdj u v → (cell u ∩ cell v).Nonempty)
    (Q : GraphQuad) (ω : Configuration) (h : Q.Crossing ω) : CellCrossing cell Q ω := by
  obtain ⟨u, hu, v, hv, p, hp⟩ := h
  obtain ⟨a, ha⟩ := (hconn u).nonempty
  obtain ⟨b, hb⟩ := (hconn v).nonempty
  exact ⟨walkCellUnion cell p, walkCellUnion_preconnected cell (fun v => (hconn v).2) hinter p,
    walkCellUnion_subset cell Q ω p hp, u, hu, (hp u p.start_mem_support).1,
    (hp u p.start_mem_support).2, ⟨a, walkCellUnion_start cell p ha, ha⟩,
    v, hv, (hp v p.end_mem_support).1, (hp v p.end_mem_support).2,
    ⟨b, walkCellUnion_end cell p hb, hb⟩⟩

theorem graphCrossing_iff_cellCrossing (cell : Site → Set X)
    (hclosed : ∀ v, IsClosed (cell v)) (hconn : ∀ v, IsConnected (cell v))
    (hinter : ∀ u v, (cell u ∩ cell v).Nonempty ↔ u = v ∨ TriangularAdj u v)
    (Q : GraphQuad) (ω : Configuration) : Q.Crossing ω ↔ CellCrossing cell Q ω := by
  exact ⟨graphCrossing_to_cellCrossing cell hconn (fun u v h => (hinter u v).mpr (Or.inr h)) Q ω,
    cellCrossing_to_graphCrossing cell hclosed (fun u v => (hinter u v).mp) Q ω⟩

theorem walkCellUnion_pathConnected (cell : Site → Set X)
    (hconn : ∀ v, IsPathConnected (cell v))
    (hinter : ∀ u v, TriangularAdj u v → (cell u ∩ cell v).Nonempty)
    {u v : Site} (p : triangularGraph.Walk u v) : IsPathConnected (walkCellUnion cell p) := by
  induction p with
  | nil => exact hconn _
  | @cons a b c hab p ih =>
    obtain ⟨x, hxa, hxb⟩ := hinter a b hab
    exact (hconn a).union ih ⟨x, hxa, walkCellUnion_start cell p hxb⟩

/-- Literal continuous paths in the full black-cell union, with endpoints
in black cells of the two terminal rows. -/
def CellPathCrossing (cell : Site → Set X) (Q : GraphQuad) (ω : Configuration) : Prop :=
  ∃ u ∈ Q.firstSide, u ∈ Q.domain ∧ ω u = true ∧
    ∃ v ∈ Q.secondSide, v ∈ Q.domain ∧ ω v = true ∧
      ∃ a ∈ cell u, ∃ b ∈ cell v, JoinedIn (blackCellUnion cell Q ω) a b

theorem cellPathCrossing_to_cellCrossing (cell : Site → Set X) (Q : GraphQuad)
    (ω : Configuration) (h : CellPathCrossing cell Q ω) : CellCrossing cell Q ω := by
  obtain ⟨u, hu, huD, huB, v, hv, hvD, hvB, a, ha, b, hb, γ, hγ⟩ := h
  refine ⟨Set.range γ, isPreconnected_range γ.continuous, ?_, u, hu, huD, huB, ?_,
    v, hv, hvD, hvB, ?_⟩
  · rintro p ⟨t, rfl⟩
    exact hγ t
  · exact ⟨a, ⟨0, γ.source⟩, ha⟩
  · exact ⟨b, ⟨1, γ.target⟩, hb⟩

theorem graphCrossing_to_cellPathCrossing (cell : Site → Set X)
    (hconn : ∀ v, IsPathConnected (cell v))
    (hinter : ∀ u v, TriangularAdj u v → (cell u ∩ cell v).Nonempty)
    (Q : GraphQuad) (ω : Configuration) (h : Q.Crossing ω) : CellPathCrossing cell Q ω := by
  obtain ⟨u, hu, v, hv, p, hp⟩ := h
  obtain ⟨a, ha⟩ := (hconn u).nonempty
  obtain ⟨b, hb⟩ := (hconn v).nonempty
  have hc := walkCellUnion_pathConnected cell hconn hinter p
  have hj := hc.joinedIn a (walkCellUnion_start cell p ha) b (walkCellUnion_end cell p hb)
  exact ⟨u, hu, (hp u p.start_mem_support).1, (hp u p.start_mem_support).2,
    v, hv, (hp v p.end_mem_support).1, (hp v p.end_mem_support).2,
    a, ha, b, hb, hj.mono (walkCellUnion_subset cell Q ω p hp)⟩

theorem graphCrossing_iff_cellPathCrossing (cell : Site → Set X)
    (hclosed : ∀ v, IsClosed (cell v)) (hconn : ∀ v, IsPathConnected (cell v))
    (hinter : ∀ u v, (cell u ∩ cell v).Nonempty ↔ u = v ∨ TriangularAdj u v)
    (Q : GraphQuad) (ω : Configuration) : Q.Crossing ω ↔ CellPathCrossing cell Q ω := by
  constructor
  · exact graphCrossing_to_cellPathCrossing cell hconn
      (fun u v h => (hinter u v).mpr (Or.inr h)) Q ω
  · intro h
    exact cellCrossing_to_graphCrossing cell hclosed (fun u v => (hinter u v).mp) Q ω
      (cellPathCrossing_to_cellCrossing cell Q ω h)

/-- Concrete axial Hex board, with literal left/right terminal rows. -/
def axialBoxQuad (n : ℕ) : GraphQuad where
  domain := latticeBox n
  firstSide := (latticeBox n).filter (fun v => v.1 = -(n : ℤ))
  secondSide := (latticeBox n).filter (fun v => v.1 = (n : ℤ))

/-- The exact union of the domain's literal closed hexagons. -/
def polyhex (n : ℕ) : Set (ℝ × ℝ) := ⋃ u ∈ latticeBox n, HexCells.cell u

theorem polyhex_isCompact (n : ℕ) : IsCompact (polyhex n) :=
  (latticeBox n).isCompact_biUnion (fun u _ => HexCells.isCompact_cell u)

theorem blackCellUnion_subset_polyhex (n : ℕ) (ω : Configuration) :
    blackCellUnion HexCells.cell (axialBoxQuad n) ω ⊆ polyhex n := by
  rintro p ⟨u, hu, _, hp⟩
  exact mem_iUnion₂_of_mem hu hp

/-- A genuine cell dictionary: the cells are the explicit hexagons,
their intersection graph is proved, and all paths stay in their full
union. There is no assumed planar or crossing equivalence here. -/
theorem hex_graphCrossing_iff_cellPathCrossing (Q : GraphQuad) (ω : Configuration) :
    Q.Crossing ω ↔ CellPathCrossing HexCells.cell Q ω := by
  apply graphCrossing_iff_cellPathCrossing HexCells.cell HexCells.isClosed_cell
  · intro v
    exact (HexCells.convex_cell v).isPathConnected ⟨HexCells.center v, HexCells.center_mem_cell v⟩
  · exact HexCells.cell_inter_nonempty_iff

/-- The concrete axial box with terminal rows is a first literal
graph/closed-cell dictionary instance. Identifying the exposed terminal
arcs and the simple polygon boundary remains a separate planar step. -/
theorem axialBox_graphCrossing_iff_cellPathCrossing (n : ℕ) (ω : Configuration) :
    (axialBoxQuad n).Crossing ω ↔
      CellPathCrossing HexCells.cell (axialBoxQuad n) ω :=
  hex_graphCrossing_iff_cellPathCrossing _ _

#print axioms finite_closed_cover_chain
#print axioms graphCrossing_iff_cellCrossing
#print axioms graphCrossing_iff_cellPathCrossing
#print axioms axialBox_graphCrossing_iff_cellPathCrossing

end ExceptionalTimes.PairSquareSewing
