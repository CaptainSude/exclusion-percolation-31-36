import ExceptionalTimes.Annulus
import ExceptionalTimes.CellInterpolation

/-!
# The actual filled-hole bridge for a square annulus

This file works with literal triangular-lattice walks and the existing
`OneArm`. Filling a finite inner square black produces a wired annular
connection, with proper last-departure/first-arrival trimming. No planar
duality, arm extraction, or published probability inequality is assumed.
-/

namespace ExceptionalTimes.HoleFilling

def fillBox (ω : Configuration) (r : ℕ) : Configuration :=
  fun v => if v ∈ latticeBox r then true else ω v

@[simp] theorem fillBox_inside (ω : Configuration) (r : ℕ) {v : Site}
    (hv : v ∈ latticeBox r) : fillBox ω r v = true := by simp [fillBox, hv]

@[simp] theorem fillBox_outside (ω : Configuration) (r : ℕ) {v : Site}
    (hv : v ∉ latticeBox r) : fillBox ω r v = ω v := by simp [fillBox, hv]

theorem origin_mem_box (r : ℕ) : (0, 0) ∈ latticeBox r := by
  simp [latticeBox]

private theorem horizontal_reachable (ω : Configuration) (r : ℕ) (y x : ℤ)
    (hx : (x, y) ∈ latticeBox r) :
    (blackGraph (fillBox ω r)).Reachable (0, y) (x, y) := by
  induction x using Int.induction_on with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hprev : ((n : ℤ), y) ∈ latticeBox r := by
        simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_Icc] at hx ⊢
        omega
      apply (ih hprev).trans
      exact (show (blackGraph (fillBox ω r)).Adj ((n : ℤ), y) (n + 1, y) from
        ⟨Or.inl ⟨rfl, rfl⟩, fillBox_inside ω r hprev, fillBox_inside ω r hx⟩).reachable
  | pred n ih =>
      have hprev : (-(n : ℤ), y) ∈ latticeBox r := by
        simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_Icc] at hx ⊢
        omega
      apply (ih hprev).trans
      exact (show (blackGraph (fillBox ω r)).Adj (-(n : ℤ), y) (-n - 1, y) from
        ⟨Or.inr (Or.inl ⟨rfl, rfl⟩), fillBox_inside ω r hprev,
          fillBox_inside ω r hx⟩).reachable

private theorem vertical_reachable (ω : Configuration) (r : ℕ) (x y : ℤ)
    (hy : (x, y) ∈ latticeBox r) :
    (blackGraph (fillBox ω r)).Reachable (x, 0) (x, y) := by
  induction y using Int.induction_on with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      have hprev : (x, (n : ℤ)) ∈ latticeBox r := by
        simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_Icc] at hy ⊢
        omega
      apply (ih hprev).trans
      exact (show (blackGraph (fillBox ω r)).Adj (x, (n : ℤ)) (x, n + 1) from
        ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), fillBox_inside ω r hprev,
          fillBox_inside ω r hy⟩).reachable
  | pred n ih =>
      have hprev : (x, -(n : ℤ)) ∈ latticeBox r := by
        simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
          Finset.mem_Icc] at hy ⊢
        omega
      apply (ih hprev).trans
      exact (show (blackGraph (fillBox ω r)).Adj (x, -(n : ℤ)) (x, -n - 1) from
        ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
          fillBox_inside ω r hprev, fillBox_inside ω r hy⟩).reachable

/-- An actual lattice route inside the filled square joins the origin to
every site of that square. No connectivity hypothesis is supplied. -/
theorem filled_box_reachable (ω : Configuration) (r : ℕ) {v : Site}
    (hv : v ∈ latticeBox r) :
    (blackGraph (fillBox ω r)).Reachable (0, 0) v := by
  rcases v with ⟨x, y⟩
  have hx : (x, 0) ∈ latticeBox r := by
    simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
      Finset.mem_Icc] at hv ⊢
    omega
  exact (horizontal_reachable ω r 0 x hx).trans (vertical_reachable ω r x y hv)

theorem fillBox_nested (ω : Configuration) {s r : ℕ} (hsr : s ≤ r) :
    fillBox (fillBox ω r) s = fillBox ω r := by
  funext v
  by_cases hvs : v ∈ latticeBox s
  · simp [fillBox, hvs, latticeBox_mono hsr hvs]
  · simp [fillBox, hvs]

private theorem black_walk_colors (ω : Configuration) {u v : Site}
    (p : (blackGraph ω).Walk u v) (hu : ω u = true) :
    ∀ z ∈ p.support, ω z = true := by
  induction p with
  | nil => simpa using hu
  | @cons a b c hab p ih =>
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · simpa [hz] using hu
      · exact ih hab.2.2 z hz

private theorem reachable_of_colored_walk (ω : Configuration) {u v : Site}
    (p : triangularGraph.Walk u v) (hc : ∀ z ∈ p.support, ω z = true) :
    (blackGraph ω).Reachable u v := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
      have ha : ω a = true := hc a (by simp)
      have hb : ω b = true := hc b (by simp)
      exact (show (blackGraph ω).Adj a b from ⟨hab, ha, hb⟩).reachable.trans
        (ih (fun z hz => hc z (List.mem_cons_of_mem a hz)))

/-- Literal wired annular crossing: the initial site is in the wired hole,
the terminal site is outside the outer box, and the simple lattice path
meets these two regions only at the corresponding endpoints. All sites
after the first use the original colors. -/
def WiredArm (ω : Configuration) (r R : ℕ) : Prop :=
  ∃ u ∈ latticeBox r, ∃ v, v ∉ latticeBox R ∧
    ∃ p : triangularGraph.Walk u v,
      p.IsPath ∧ u ≠ v ∧
      (∀ z ∈ p.support, z ≠ u → z ∉ latticeBox r ∧ ω z = true) ∧
      (∀ z ∈ p.support, z ≠ v → z ∈ latticeBox R)

/-- Filling the inner box is exactly the wired radial event, with actual
simple path witnesses and proper boundary trimming. -/
theorem oneArm_fillBox_iff_wiredArm (ω : Configuration) {r R : ℕ}
    (hrR : r ≤ R) : OneArm (fillBox ω r) (0, 0) R ↔ WiredArm ω r R := by
  constructor
  · rintro ⟨v, hv, hvout⟩
    obtain ⟨p, hp⟩ := hv.2.exists_isPath
    obtain ⟨u, hu, w, hw, q, hq, _, hinner, houter⟩ :=
      Annulus.trim_path_between_sets (latticeBox r : Set Site)
        (↑(latticeBox R) : Set Site)ᶜ p hp (origin_mem_box r) hvout
    have hforget : blackGraph (fillBox ω r) ≤ triangularGraph := fun _ _ h => h.1
    have huw : u ≠ w := fun heq => hw (heq ▸ latticeBox_mono hrR hu)
    refine ⟨u, hu, w, hw, q.mapLe hforget, hq.mapLe hforget, huw, ?_, ?_⟩
    · intro z hz hzu
      have hzq : z ∈ q.support := by simpa using hz
      have hzout : z ∉ latticeBox r := fun hz => hzu (hinner z hzq hz)
      refine ⟨hzout, ?_⟩
      have hc := black_walk_colors (fillBox ω r) q (fillBox_inside ω r hu) z hzq
      simpa [fillBox, hzout] using hc
    · intro z hz hzw
      by_contra hzout
      exact hzw (houter z (by simpa using hz) hzout)
  · rintro ⟨u, hu, v, hvout, p, _, _, hinner, _⟩
    have hpcol : ∀ z ∈ p.support, fillBox ω r z = true := by
      intro z hz
      by_cases hzu : z = u
      · exact hzu ▸ fillBox_inside ω r hu
      · obtain ⟨hzout, hc⟩ := hinner z hz hzu
        simpa [fillBox, hzout] using hc
    exact ⟨v, ⟨fillBox_inside ω r (origin_mem_box r),
      (filled_box_reachable ω r hu).trans (reachable_of_colored_walk _ p hpcol)⟩, hvout⟩

/-- The macroscopic wired annulus becomes a unit-hole radial event after
filling. This is an actual event identity, not a probability comparison. -/
theorem unit_hole_bridge (ω : Configuration) {r R : ℕ}
    (hr : 1 ≤ r) (hrR : r ≤ R) :
    WiredArm (fillBox ω r) 1 R ↔ WiredArm ω r R := by
  rw [← oneArm_fillBox_iff_wiredArm (fillBox ω r) (hr.trans hrR),
    fillBox_nested ω hr, oneArm_fillBox_iff_wiredArm ω hrR]

/-- Only the original annular colors through the one-step outer boundary
are needed; colors overwritten in the hole are irrelevant. -/
theorem wiredArm_congr_on_annulus (ω η : Configuration) {r R : ℕ}
    (hrR : r ≤ R)
    (heq : ∀ v, v ∈ latticeBox (R + 1) → v ∉ latticeBox r → ω v = η v) :
    WiredArm ω r R ↔ WiredArm η r R := by
  rw [← oneArm_fillBox_iff_wiredArm ω hrR, ← oneArm_fillBox_iff_wiredArm η hrR]
  apply oneArm_congr_of_eqOn_box (origin_mem_box R)
  intro v hv
  by_cases hvr : v ∈ latticeBox r
  · simp [fillBox, hvr]
  · simp [fillBox, hvr, heq v hv hvr]

/-- An actual square probe in the same oblique integer coordinates used
for the triangular graph. -/
def probeBox (x : Site) (n : ℕ) : Set Site :=
  {y | (y.1 - x.1, y.2 - x.2) ∈ latticeBox n}

/-- A square probe cannot reach the filled hole when its center lies
outside the sum of their radii. This is a proved geometric support fact. -/
theorem probeBox_disjoint_hole (x : Site) (r n : ℕ)
    (hx : x ∉ latticeBox (r + n)) :
    Disjoint (probeBox x n) (latticeBox r : Set Site) := by
  apply Set.disjoint_left.mpr
  intro y hy hyr
  apply hx
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [probeBox, Set.mem_ofPred_eq, latticeBox, Finset.product_eq_sprod,
    Finset.mem_coe, Finset.mem_product, Finset.mem_Icc] at hy hyr ⊢
  omega

/-- In particular all colors of a sufficiently remote probe are literally
unchanged by the filled-hole reduction. -/
theorem fillBox_eqOn_probeBox (ω : Configuration) (x : Site) (r n : ℕ)
    (hx : x ∉ latticeBox (r + n)) :
    Set.EqOn (fillBox ω r) ω (probeBox x n) := by
  intro y hy
  exact fillBox_outside ω r (fun hyr =>
    Set.disjoint_left.mp (probeBox_disjoint_hole x r n hx) hy hyr)

/-- Every event determined outside the filled hole is unchanged. This is
the necessary locality check before applying a published arm implication
to a filled configuration and returning to the original fair colors. -/
theorem outside_test_fillBox (ω : Configuration) (r : ℕ)
    (E : Configuration → Prop)
    (hloc : ∀ a b : Configuration,
      (∀ v, v ∉ latticeBox r → a v = b v) → (E a ↔ E b)) :
    E (fillBox ω r) ↔ E ω :=
  hloc _ _ (fun _ hv => fillBox_outside ω r hv)

/-- Filling preserves agreement outside any cell, including cells crossing
the hole boundary. -/
theorem fillBox_eq_outside_cell (r : ℕ) (D : Finset Site)
    (a b : Configuration) (hab : ∀ v, v ∉ D → a v = b v) :
    ∀ v, v ∉ D → fillBox a r v = fillBox b r v := by
  intro v hv
  by_cases hvr : v ∈ latticeBox r
  · simp [fillBox, hvr]
  · simp [fillBox, hvr, hab v hv]

/-- Arbitrary-assignment pivotality of a test after filling gives genuine
pivotality of the unfilled test at the filled configuration. This is the
deterministic event dictionary needed for the GPS radial-box geometry. -/
theorem cell_pivotal_fillBox (F : Configuration → Bool) (r : ℕ)
    (D : Finset Site) (ω : Configuration)
    (h : CellInterpolation.CellPivotal (fun η => F (fillBox η r)) D ω) :
    CellInterpolation.CellPivotal F D (fillBox ω r) := by
  obtain ⟨a, b, ha, hb, hF⟩ := h
  exact ⟨fillBox a r, fillBox b r,
    fillBox_eq_outside_cell r D a ω ha, fillBox_eq_outside_cell r D b ω hb, hF⟩

/-- In fact the possible changes avoid every site overwritten by filling,
even when the original cell straddles the inner boundary. -/
theorem cell_pivotal_fillBox_sdiff (F : Configuration → Bool) (r : ℕ)
    (D : Finset Site) (ω : Configuration)
    (h : CellInterpolation.CellPivotal (fun η => F (fillBox η r)) D ω) :
    CellInterpolation.CellPivotal F (D \ latticeBox r) (fillBox ω r) := by
  obtain ⟨a, b, ha, hb, hF⟩ := h
  have hext : ∀ η : Configuration,
      (∀ v, v ∉ D → η v = ω v) →
      ∀ v, v ∉ D \ latticeBox r → fillBox η r v = fillBox ω r v := by
    intro η hη v hv
    by_cases hvr : v ∈ latticeBox r
    · simp [fillBox, hvr]
    · have hvD : v ∉ D := fun hvD => hv (Finset.mem_sdiff.mpr ⟨hvD, hvr⟩)
      simp [fillBox, hvr, hη v hvD]
  exact ⟨fillBox a r, fillBox b r, hext a ha, hext b hb, hF⟩

/-- The Boolean test for the actual properly trimmed wired path event. -/
noncomputable def wiredArmTest (r R : ℕ) (ω : Configuration) : Bool := by
  classical
  exact decide (WiredArm ω r R)

/-- Literal arbitrary-cell pivotality of the macroscopic annulus transfers
to the unit-hole test. The witness assignments change only sites outside
the filled hole, even when the original cell meets that hole. -/
theorem wiredArm_cell_pivotal_unit_hole (ω : Configuration)
    (D : Finset Site) {r R : ℕ} (hr : 1 ≤ r) (hrR : r ≤ R)
    (h : CellInterpolation.CellPivotal (wiredArmTest r R) D ω) :
    CellInterpolation.CellPivotal (wiredArmTest 1 R) (D \ latticeBox r)
      (fillBox ω r) := by
  apply cell_pivotal_fillBox_sdiff (wiredArmTest 1 R) r D ω
  have heq : (fun η => wiredArmTest 1 R (fillBox η r)) = wiredArmTest r R := by
    funext η
    simp only [wiredArmTest, decide_eq_decide]
    exact unit_hole_bridge η hr hrR
  rw [heq]
  exact h

#print axioms filled_box_reachable
#print axioms oneArm_fillBox_iff_wiredArm
#print axioms unit_hole_bridge
#print axioms fillBox_eqOn_probeBox
#print axioms cell_pivotal_fillBox
#print axioms cell_pivotal_fillBox_sdiff
#print axioms wiredArm_cell_pivotal_unit_hole

end ExceptionalTimes.HoleFilling
