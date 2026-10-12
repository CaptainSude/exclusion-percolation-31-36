import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!+# Deterministic graph components of the proposed necklace argument

The proved results in this file concern genuine graph reachability. They do not
assume or assert existence of a necklace. In particular, the planar statement
that a gap boundary contains a radial path remains a separate proof obligation.

The first group proves that the external vertex boundary of a monochromatic
cluster has the opposite color, and that nonadjacency to another cluster makes
this boundary disjoint from the other cluster. The second group proves that an
interface consisting of two internally connected black runs transmits exactly
one connectivity bit. No probabilistic or unpublished geometric axiom is used.
-/

namespace ExceptionalTimes.Necklace

universe u
variable {V : Type u}

/-- The graph retaining precisely the edges with both endpoints of one color. -/
def monochromeGraph (G : SimpleGraph V) (c : V → Bool) (b : Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ c x = b ∧ c y = b
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro x h
    exact h.1.ne rfl

/-- A same-colored component attached to any of the specified seeds.
The seed color is required because graph reachability includes the zero walk. -/
def attachedCluster (G : SimpleGraph V) (c : V → Bool) (b : Bool)
    (seeds : Set V) : Set V :=
  {x | ∃ s ∈ seeds, c s = b ∧ (monochromeGraph G c b).Reachable s x}

/-- The external vertex boundary uses vertices outside the set adjacent to it. -/
def externalBoundary (G : SimpleGraph V) (S : Set V) : Set V :=
  {x | x ∉ S ∧ ∃ y ∈ S, G.Adj y x}

theorem reachable_has_color (G : SimpleGraph V) (c : V → Bool) (b : Bool)
    {x y : V} (hx : c x = b) (h : (monochromeGraph G c b).Reachable x y) :
    c y = b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hx
  | tail _ he _ => exact he.2.2

theorem attachedCluster_has_color (G : SimpleGraph V) (c : V → Bool) (b : Bool)
    (seeds : Set V) {x : V} (hx : x ∈ attachedCluster G c b seeds) : c x = b := by
  obtain ⟨s, _, hs, hreach⟩ := hx
  exact reachable_has_color G c b hs hreach

theorem attachedCluster_closed (G : SimpleGraph V) (c : V → Bool) (b : Bool)
    (seeds : Set V) {x y : V} (hx : x ∈ attachedCluster G c b seeds)
    (hxy : G.Adj x y) (hy : c y = b) : y ∈ attachedCluster G c b seeds := by
  obtain ⟨s, hs, hcs, hreach⟩ := hx
  have hcx := reachable_has_color G c b hcs hreach
  exact ⟨s, hs, hcs, hreach.trans
    (SimpleGraph.Adj.reachable (show (monochromeGraph G c b).Adj x y from
      ⟨hxy, hcx, hy⟩))⟩

theorem externalBoundary_not_color (G : SimpleGraph V) (c : V → Bool) (b : Bool)
    (seeds : Set V) {x : V}
    (hx : x ∈ externalBoundary G (attachedCluster G c b seeds)) : c x ≠ b := by
  intro hcx
  obtain ⟨y, hy, hyx⟩ := hx.2
  exact hx.1 (attachedCluster_closed G c b seeds hy hyx hcx)

/-- A black attached cluster's entire external vertex boundary is white. -/
theorem black_externalBoundary_white (G : SimpleGraph V) (c : V → Bool)
    (seeds : Set V) {x : V}
    (hx : x ∈ externalBoundary G (attachedCluster G c true seeds)) : c x = false := by
  have hn := externalBoundary_not_color G c true seeds hx
  cases hcx : c x with
  | false => rfl
  | true => exact False.elim (hn hcx)

/-- If no edge joins S to W, no vertex of W lies on S's external boundary. -/
theorem externalBoundary_disjoint_of_no_adj (G : SimpleGraph V) (S W : Set V)
    (h : ∀ x ∈ S, ∀ y ∈ W, ¬G.Adj x y) : Disjoint (externalBoundary G S) W := by
  apply Set.disjoint_left.mpr
  intro y hy hyW
  obtain ⟨x, hx, hxy⟩ := hy.2
  exact h x hx y hyW hxy

/-- The exact nonplanar conclusion needed in the gap-boundary construction.
The additional existence of a radial path in this boundary is NOT assumed here. -/
theorem gap_boundary_properties (G : SimpleGraph V) (c : V → Bool)
    (blackSeeds whiteSeeds : Set V)
    (hsep : ∀ x ∈ attachedCluster G c true blackSeeds,
      ∀ y ∈ attachedCluster G c false whiteSeeds, ¬G.Adj x y) :
    (∀ x ∈ externalBoundary G (attachedCluster G c true blackSeeds), c x = false) ∧
    Disjoint (externalBoundary G (attachedCluster G c true blackSeeds))
      (attachedCluster G c false whiteSeeds) := by
  constructor
  · intro x hx
    exact black_externalBoundary_white G c blackSeeds hx
  · exact externalBoundary_disjoint_of_no_adj G _ _ hsep

/-- Each of two boundary runs is internally connected. The type V may be
restricted to black vertices, or G may itself be a monochrome graph. -/
structure TwoRunInterface (G : SimpleGraph V) (boundary : Set V) where
  side : V → Bool
  representative : Bool → V
  representative_mem : ∀ b, representative b ∈ boundary
  representative_side : ∀ b, side (representative b) = b
  within_run : ∀ x ∈ boundary, ∀ y ∈ boundary,
    side x = side y → G.Reachable x y

/-- The bit indicating whether the two boundary runs are connected. -/
def TwoRunInterface.Joined {G : SimpleGraph V} {boundary : Set V}
    (I : TwoRunInterface G boundary) : Prop :=
  G.Reachable (I.representative false) (I.representative true)

/-- All boundary connectivity information is exactly: same run, or join bit. -/
theorem TwoRunInterface.reachable_iff {G : SimpleGraph V} {boundary : Set V}
    (I : TwoRunInterface G boundary) {x y : V} (hx : x ∈ boundary)
    (hy : y ∈ boundary) :
    G.Reachable x y ↔ I.side x = I.side y ∨ I.Joined := by
  have hxr : G.Reachable x (I.representative (I.side x)) :=
    I.within_run x hx _ (I.representative_mem _) (I.representative_side _).symm
  have hyr : G.Reachable y (I.representative (I.side y)) :=
    I.within_run y hy _ (I.representative_mem _) (I.representative_side _).symm
  constructor
  · intro hxy
    cases hsx : I.side x <;> cases hsy : I.side y
    · exact Or.inl rfl
    · exact Or.inr (by simpa [Joined, hsx, hsy] using hxr.symm.trans (hxy.trans hyr))
    · exact Or.inr (by simpa [Joined, hsx, hsy] using hyr.symm.trans (hxy.symm.trans hxr))
    · exact Or.inl rfl
  · intro h
    rcases h with hsame | hjoin
    · exact I.within_run x hx y hy hsame
    · cases hsx : I.side x <;> cases hsy : I.side y
      · exact I.within_run x hx y hy (hsx.trans hsy.symm)
      · have hxr' : G.Reachable x (I.representative false) := by simpa [hsx] using hxr
        have hyr' : G.Reachable y (I.representative true) := by simpa [hsy] using hyr
        exact hxr'.trans (hjoin.trans hyr'.symm)
      · have hxr' : G.Reachable x (I.representative true) := by simpa [hsx] using hxr
        have hyr' : G.Reachable y (I.representative false) := by simpa [hsy] using hyr
        exact hxr'.trans (hjoin.symm.trans hyr'.symm)
      · exact I.within_run x hx y hy (hsx.trans hsy.symm)

/-- Replacing the interior while preserving the one bit preserves every
boundary connectivity query. The graph-theoretic hypotheses are explicit. -/
theorem TwoRunInterface.same_bit_same_boundary_connectivity
    {G H : SimpleGraph V} {boundary : Set V}
    (I : TwoRunInterface G boundary) (J : TwoRunInterface H boundary)
    (hsides : ∀ x ∈ boundary, I.side x = J.side x)
    (hbit : I.Joined ↔ J.Joined) {x y : V}
    (hx : x ∈ boundary) (hy : y ∈ boundary) :
    G.Reachable x y ↔ H.Reachable x y := by
  rw [I.reachable_iff hx hy, J.reachable_iff hx hy]
  rw [hsides x hx, hsides y hy, hbit]

/-- An arbitrary finite excursion through an interior can be replaced whenever
the new interior connects every pair of interface vertices connected by the old
one. The interface is exactly the intersection of the two vertex domains.

This is stated for actual graph walks, not an abstract connectivity oracle.
The two domains need not cover all vertices, and neither graph need be finite. -/
theorem replace_interior_reachable
    (E J K : SimpleGraph V) (exterior interior : Set V)
    (hE : ∀ {x y}, E.Adj x y → x ∈ exterior ∧ y ∈ exterior)
    (hJ : ∀ {x y}, J.Adj x y → x ∈ interior ∧ y ∈ interior)
    (htransfer : ∀ x ∈ exterior ∩ interior, ∀ y ∈ exterior ∩ interior,
      J.Reachable x y → K.Reachable x y)
    {u v : V} (hu : u ∈ exterior) (hv : v ∈ exterior)
    (hpath : (E ⊔ J).Reachable u v) : (E ⊔ K).Reachable u v := by
  have state : ∀ {w}, (E ⊔ J).Reachable u w →
      (w ∈ exterior ∧ (E ⊔ K).Reachable u w) ∨
      ∃ b, b ∈ exterior ∩ interior ∧ (E ⊔ K).Reachable u b ∧
        J.Reachable b w ∧ w ∈ interior := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => exact Or.inl ⟨hu, SimpleGraph.Reachable.rfl⟩
    | @tail x y _ hedge ih =>
      change E.Adj x y ∨ J.Adj x y at hedge
      rcases ih with ⟨hxE, hux⟩ | ⟨b, hb, hub, hbx, hxI⟩
      · rcases hedge with he | hj
        · exact Or.inl ⟨(hE he).2,
            hux.trans (he.reachable.mono le_sup_left)⟩
        · exact Or.inr ⟨x, ⟨hxE, (hJ hj).1⟩, hux,
            hj.reachable, (hJ hj).2⟩
      · rcases hedge with he | hj
        · have hbxK := htransfer b hb x ⟨(hE he).1, hxI⟩ hbx
          exact Or.inl ⟨(hE he).2,
            (hub.trans (hbxK.mono le_sup_right)).trans
              (he.reachable.mono le_sup_left)⟩
        · exact Or.inr ⟨b, hb, hub, hbx.trans hj.reachable, (hJ hj).2⟩
  rcases state hpath with ⟨_, huv⟩ | ⟨b, hb, hub, hbv, hvI⟩
  · exact huv
  · exact hub.trans ((htransfer b hb v ⟨hv, hvI⟩ hbv).mono le_sup_right)

/-- Exact exterior connectivity invariance under replacing an interior with the
same interface connectivity relation. No planarity assumption is needed. -/
theorem replace_interior_reachable_iff
    (E J K : SimpleGraph V) (exterior interior : Set V)
    (hE : ∀ {x y}, E.Adj x y → x ∈ exterior ∧ y ∈ exterior)
    (hJ : ∀ {x y}, J.Adj x y → x ∈ interior ∧ y ∈ interior)
    (hK : ∀ {x y}, K.Adj x y → x ∈ interior ∧ y ∈ interior)
    (hinterface : ∀ x ∈ exterior ∩ interior, ∀ y ∈ exterior ∩ interior,
      J.Reachable x y ↔ K.Reachable x y)
    {u v : V} (hu : u ∈ exterior) (hv : v ∈ exterior) :
    (E ⊔ J).Reachable u v ↔ (E ⊔ K).Reachable u v := by
  constructor
  · exact replace_interior_reachable E J K exterior interior hE hJ
      (fun x hx y hy => (hinterface x hx y hy).mp) hu hv
  · exact replace_interior_reachable E K J exterior interior hE hK
      (fun x hx y hy => (hinterface x hx y hy).mpr) hu hv

/-- The one-bit boundary interface controls all exterior connectivity queries.
This supplies the combinatorial replacement step in the necklace argument;
the existence and geometry of an actual necklace remain separate. -/
theorem two_run_bit_controls_exterior
    (E J K : SimpleGraph V) (exterior interior : Set V)
    (hE : ∀ {x y}, E.Adj x y → x ∈ exterior ∧ y ∈ exterior)
    (hJ : ∀ {x y}, J.Adj x y → x ∈ interior ∧ y ∈ interior)
    (hK : ∀ {x y}, K.Adj x y → x ∈ interior ∧ y ∈ interior)
    (I : TwoRunInterface J (exterior ∩ interior))
    (I' : TwoRunInterface K (exterior ∩ interior))
    (hsides : ∀ x ∈ exterior ∩ interior, I.side x = I'.side x)
    (hbit : I.Joined ↔ I'.Joined)
    {u v : V} (hu : u ∈ exterior) (hv : v ∈ exterior) :
    (E ⊔ J).Reachable u v ↔ (E ⊔ K).Reachable u v := by
  apply replace_interior_reachable_iff E J K exterior interior hE hJ hK
  · intro x hx y hy
    exact I.same_bit_same_boundary_connectivity I' hsides hbit hx hy
  · exact hu
  · exact hv

/-! ## The precise finite Hex input and the frontier-path deduction

Lovász, *Graphs and Geometry* (2019), Proposition 6.3, states the Hex
alternative for a finite planar map whose outer face is a quadrilateral
`a,b,c,d` and whose other faces are triangles. Its existence half is precisely
`HexAlternative` below. The full published proposition also says that the two
crossings cannot coexist; that stronger part is not used here.

Source: https://page.math.tu-berlin.de/~felsner/Lehre/SemInter/Lovasz-Graphs-and-Geometry-Chapt6-2019.pdf

No instance of this property is assumed globally or asserted for an unproved
annular gap. All uses take it as an explicit hypothesis. Constructing the cut
gap as the required triangulated quadrilateral remains a geometric obligation.
-/

/-- The existence half of the published finite Hex theorem. -/
def HexAlternative (G : SimpleGraph V) (a b c d : V) : Prop :=
  ∀ coloring : V → Bool,
    coloring a = true → coloring c = true →
    coloring b = false → coloring d = false →
    (monochromeGraph G coloring true).Reachable a c ∨
      (monochromeGraph G coloring false).Reachable b d

/-- Recolor the entire external frontier and the two radial apex vertices white. -/
noncomputable def frontierColor (G : SimpleGraph V) (S : Set V) (b d : V) : V → Bool := by
  classical
  exact fun x => if x ∈ externalBoundary G S ∨ x = b ∨ x = d then false else true

theorem frontierColor_white_iff (G : SimpleGraph V) (S : Set V) (b d x : V) :
    frontierColor G S b d x = false ↔ x ∈ externalBoundary G S ∨ x = b ∨ x = d := by
  classical
  unfold frontierColor
  split <;> simp_all

theorem frontierColor_black_iff (G : SimpleGraph V) (S : Set V) (b d x : V) :
    frontierColor G S b d x = true ↔
      x ∉ externalBoundary G S ∧ x ≠ b ∧ x ≠ d := by
  classical
  unfold frontierColor
  split <;> simp_all
  all_goals aesop

theorem reachable_mem_of_closed (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S)
    {x y : V} (hx : x ∈ S) (hxy : G.Reachable x y) : y ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact hx
  | @tail u v _ huv ih => exact hclosed u ih v huv

theorem monochrome_walk_support_has_color (G : SimpleGraph V) (coloring : V → Bool)
    (color : Bool) {x y z : V} (hx : coloring x = color)
    (p : (monochromeGraph G coloring color).Walk x y) (hz : z ∈ p.support) :
    coloring z = color := by
  classical
  exact reachable_has_color G coloring color hx (p.takeUntil z hz).reachable

/-- Applying Hex to the frontier recoloring forces an actual simple radial
graph path inside the external frontier, apart from its two apex endpoints.

Here `a` is in the left cluster S, `c` is outside S and not adjacent to S,
and `b,d` are the radial apex vertices. No frontier-path assertion occurs
among the hypotheses: it is deduced from the published Hex alternative. -/
theorem hex_gives_frontier_path (G : SimpleGraph V) (S : Set V)
    (a b c d : V) (hex : HexAlternative G a b c d)
    (ha : a ∈ S) (hc : c ∉ S)
    (hca : ∀ x ∈ S, ¬G.Adj x c)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) :
    ∃ p : G.Walk b d, p.IsPath ∧
      ∀ x ∈ p.support, x ≠ b → x ≠ d → x ∈ externalBoundary G S := by
  let coloring := frontierColor G S b d
  have hcaB : c ∉ externalBoundary G S := by
    intro h
    obtain ⟨x, hx, hxc⟩ := h.2
    exact hca x hx hxc
  have haB : a ∉ externalBoundary G S := fun h => h.1 ha
  have hcola : coloring a = true :=
    (frontierColor_black_iff G S b d a).mpr ⟨haB, hab, had⟩
  have hcolc : coloring c = true :=
    (frontierColor_black_iff G S b d c).mpr ⟨hcaB, hcb, hcd⟩
  have hcolb : coloring b = false :=
    (frontierColor_white_iff G S b d b).mpr (Or.inr (Or.inl rfl))
  have hcold : coloring d = false :=
    (frontierColor_white_iff G S b d d).mpr (Or.inr (Or.inr rfl))
  have hclosed : ∀ x ∈ S, ∀ y, (monochromeGraph G coloring true).Adj x y → y ∈ S := by
    intro x hx y hxy
    by_contra hy
    have hyB : y ∈ externalBoundary G S := ⟨hy, x, hx, hxy.1⟩
    have hyW : coloring y = false :=
      (frontierColor_white_iff G S b d y).mpr (Or.inl hyB)
    rw [hxy.2.2] at hyW
    contradiction
  have hnot : ¬(monochromeGraph G coloring true).Reachable a c := by
    intro hac
    exact hc (reachable_mem_of_closed _ S hclosed ha hac)
  have hwhite := (hex coloring hcola hcolc hcolb hcold).resolve_left hnot
  obtain ⟨p, hp⟩ := hwhite.exists_isPath
  have hmono : monochromeGraph G coloring false ≤ G := fun _ _ h => h.1
  refine ⟨p.mapLe hmono, hp.mapLe hmono, ?_⟩
  intro x hx hxb hxd
  have hx' : x ∈ p.support := by simpa using hx
  have hcolor := monochrome_walk_support_has_color G coloring false hcolb p hx'
  rcases (frontierColor_white_iff G S b d x).mp hcolor with hfront | heq | heq
  · exact hfront
  · exact False.elim (hxb heq)
  · exact False.elim (hxd heq)

/-- Delete a set of vertices while keeping a common ambient vertex type.
Deleted vertices are isolated. This is convenient for the two radial apices. -/
def avoidGraph (G : SimpleGraph V) (removed : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ removed ∧ y ∉ removed
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem attachedCluster_avoids (G : SimpleGraph V) (removed : Set V)
    (coloring : V → Bool) (color : Bool) (seeds : Set V)
    (hseeds : ∀ s ∈ seeds, s ∉ removed) {x : V}
    (hx : x ∈ attachedCluster (avoidGraph G removed) coloring color seeds) :
    x ∉ removed := by
  obtain ⟨s, hs, _, hreach⟩ := hx
  apply reachable_mem_of_closed _ removedᶜ _ (hseeds s hs) hreach
  intro u _ v huv
  exact huv.1.2.2

/-- Outside the deleted apices, the full-graph frontier is still white. -/
theorem avoided_black_frontier_white (G : SimpleGraph V) (removed : Set V)
    (coloring : V → Bool) (seeds : Set V)
    (hseeds : ∀ s ∈ seeds, s ∉ removed) {x : V} (hx : x ∉ removed)
    (hfront : x ∈ externalBoundary G
      (attachedCluster (avoidGraph G removed) coloring true seeds)) :
    coloring x = false := by
  apply black_externalBoundary_white (avoidGraph G removed) coloring seeds
  refine ⟨hfront.1, ?_⟩
  obtain ⟨y, hy, hyx⟩ := hfront.2
  exact ⟨y, hy, hyx, attachedCluster_avoids G removed coloring true seeds hseeds hy, hx⟩

/-- An actual simple path from the top apex to the bottom apex, whose internal
vertices are white and avoid the two side clusters. This is the graph form of
the fifth arm before the two artificial apex vertices are removed. -/
def RadialWhitePath (G : SimpleGraph V) (coloring : V → Bool)
    (b d : V) (blackSide whiteSide : Set V) : Prop :=
  ∃ p : G.Walk b d, p.IsPath ∧
    ∀ x ∈ p.support, x ≠ b → x ≠ d →
      coloring x = false ∧ x ∉ blackSide ∧ x ∉ whiteSide

/-- If the two attached side clusters are not adjacent, the published Hex
alternative forces a fifth white radial path disjoint from both clusters.
The top and bottom apices are removed when forming the original clusters;
their original colors are irrelevant. -/
theorem no_cluster_adjacency_gives_fifth_path
    (G : SimpleGraph V) (coloring : V → Bool) (a b c d : V)
    (hex : HexAlternative G a b c d)
    (hacolor : coloring a = true) (hccolor : coloring c = false)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d)
    (hsep : ∀ x ∈ attachedCluster (avoidGraph G ({b, d} : Set V)) coloring true {a},
      ∀ y ∈ attachedCluster (avoidGraph G ({b, d} : Set V)) coloring false {c},
        ¬(avoidGraph G ({b, d} : Set V)).Adj x y) :
    RadialWhitePath G coloring b d
      (attachedCluster (avoidGraph G ({b, d} : Set V)) coloring true {a})
      (attachedCluster (avoidGraph G ({b, d} : Set V)) coloring false {c}) := by
  let removed : Set V := {b, d}
  let J := avoidGraph G removed
  let B := attachedCluster J coloring true {a}
  let W := attachedCluster J coloring false {c}
  have haseed : ∀ s ∈ ({a} : Set V), s ∉ removed := by
    intro s hs
    have hsa : s = a := Set.mem_singleton_iff.mp hs
    subst s
    simpa [removed] using (show a ≠ b ∧ a ≠ d from ⟨hab, had⟩)
  have hcseed : ∀ s ∈ ({c} : Set V), s ∉ removed := by
    intro s hs
    have hsc : s = c := Set.mem_singleton_iff.mp hs
    subst s
    simpa [removed] using (show c ≠ b ∧ c ≠ d from ⟨hcb, hcd⟩)
  have haB : a ∈ B := ⟨a, Set.mem_singleton a, hacolor, SimpleGraph.Reachable.rfl⟩
  have hcW : c ∈ W := ⟨c, Set.mem_singleton c, hccolor, SimpleGraph.Reachable.rfl⟩
  have hcB : c ∉ B := by
    intro hc
    have ht := attachedCluster_has_color J coloring true {a} hc
    rw [hccolor] at ht
    contradiction
  have hBavoid : ∀ x ∈ B, x ∉ removed := by
    intro x hx
    exact attachedCluster_avoids G removed coloring true {a} haseed hx
  have hWavoid : ∀ x ∈ W, x ∉ removed := by
    intro x hx
    exact attachedCluster_avoids G removed coloring false {c} hcseed hx
  have hsepG : ∀ x ∈ B, ∀ y ∈ W, ¬G.Adj x y := by
    intro x hx y hy hxy
    exact hsep x hx y hy ⟨hxy, hBavoid x hx, hWavoid y hy⟩
  have hca : ∀ x ∈ B, ¬G.Adj x c := fun x hx => hsepG x hx c hcW
  obtain ⟨p, hp, hfront⟩ := hex_gives_frontier_path G B a b c d hex haB hcB hca
    hab had hcb hcd
  refine ⟨p, hp, ?_⟩
  intro x hx hxb hxd
  have hxF := hfront x hx hxb hxd
  have hxavoid : x ∉ removed := by simpa [removed] using (show x ≠ b ∧ x ≠ d from ⟨hxb, hxd⟩)
  refine ⟨avoided_black_frontier_white G removed coloring {a} haseed hxavoid hxF,
    hxF.1, ?_⟩
  intro hxW
  obtain ⟨y, hy, hyx⟩ := hxF.2
  exact hsepG y hy x hxW hyx

/-- The contrapositive supplies an actual black-to-white connector: one
monochromatic path, one color-changing edge, and one monochromatic path.
The returned walks are simple. They share no vertices because their colors
are opposite. No connector assertion is assumed. -/
theorem no_fifth_path_gives_single_switch_connector
    (G : SimpleGraph V) (coloring : V → Bool) (a b c d : V)
    (hex : HexAlternative G a b c d)
    (hacolor : coloring a = true) (hccolor : coloring c = false)
    (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d)
    (hnofifth : ¬RadialWhitePath G coloring b d
      (attachedCluster (avoidGraph G ({b, d} : Set V)) coloring true {a})
      (attachedCluster (avoidGraph G ({b, d} : Set V)) coloring false {c})) :
    ∃ x y,
      ∃ p : (monochromeGraph (avoidGraph G ({b, d} : Set V)) coloring true).Walk a x,
      ∃ q : (monochromeGraph (avoidGraph G ({b, d} : Set V)) coloring false).Walk y c,
        p.IsPath ∧ q.IsPath ∧ (avoidGraph G ({b, d} : Set V)).Adj x y := by
  classical
  have hnotsep := mt (no_cluster_adjacency_gives_fifth_path G coloring a b c d hex
    hacolor hccolor hab had hcb hcd) hnofifth
  push Not at hnotsep
  obtain ⟨x, hx, y, hy, hxy⟩ := hnotsep
  obtain ⟨sa, hsa, _, hax⟩ := hx
  obtain ⟨sc, hsc, _, hcy⟩ := hy
  have hsa' : sa = a := Set.mem_singleton_iff.mp hsa
  have hsc' : sc = c := Set.mem_singleton_iff.mp hsc
  subst sa
  subst sc
  obtain ⟨p, hp⟩ := hax.exists_isPath
  obtain ⟨q, hq⟩ := hcy.symm.exists_isPath
  exact ⟨x, y, p, q, hp, hq, hxy⟩

/-- A black simple path and a white simple path joined by one edge form a
simple path. Thus the connector produced above needs no loop-erasure step. -/
theorem single_switch_splice_isPath
    (G : SimpleGraph V) (coloring : V → Bool) {a x y c : V}
    (hacolor : coloring a = true) (hccolor : coloring c = false)
    (p : (monochromeGraph G coloring true).Walk a x)
    (q : (monochromeGraph G coloring false).Walk y c)
    (hp : p.IsPath) (hq : q.IsPath) (hxy : G.Adj x y) :
    ((p.mapLe (show monochromeGraph G coloring true ≤ G from fun _ _ h => h.1)).append
      (SimpleGraph.Walk.cons hxy
        (q.mapLe (show monochromeGraph G coloring false ≤ G from fun _ _ h => h.1)))).IsPath := by
  have hycolor : coloring y = false :=
    reachable_has_color G coloring false hccolor q.reverse.reachable
  have hdisjoint : List.Disjoint p.support q.support := by
    apply List.disjoint_left.mpr
    intro v hvp hvq
    have hblack := monochrome_walk_support_has_color G coloring true hacolor p hvp
    have hwhite := monochrome_walk_support_has_color G coloring false hycolor q hvq
    rw [hblack] at hwhite
    contradiction
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_cons, List.tail_cons,
    SimpleGraph.Walk.support_mapLe_eq_support,
    SimpleGraph.Walk.support_mapLe_eq_support]
  apply List.nodup_append.mpr
  refine ⟨hp.support_nodup, hq.support_nodup, ?_⟩
  intro u hu v hv huv
  subst v
  exact List.disjoint_left.mp hdisjoint hu hv

end ExceptionalTimes.Necklace
