import ExceptionalTimes.DyadicPolygonGeometry
import ExceptionalTimes.PolygonForestNumeric

/-! A fixed finite family of literal dyadic quads supplies the integer
presentations, uniformly positive physical feature scale, and finite fixed
roots required by the proved polygon forest estimate. Refinement changes
neither the physical quads nor their root set. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

structure DyadicQuadFamily (F : Type*) where
  quad : F → ParameterQuad ℂ
  grid : ∀ i, DyadicGridQuad (quad i)

namespace DyadicQuadFamily

variable {F : Type*} [Fintype F] (T : DyadicQuadFamily F)

noncomputable def maxLevel : ℕ := Finset.univ.sup (fun i => (T.grid i).level)

theorem level_le (i : F) : (T.grid i).level≤T.maxLevel := by
  exact Finset.le_sup (f := fun j => (T.grid j).level) (Finset.mem_univ i)

noncomputable def stop : ℝ := ((2:ℝ)^T.maxLevel)⁻¹/100

theorem stop_pos : 0<T.stop := by unfold stop; positivity

theorem stop_lt_spacing (i : F) : 6*(T.stop/8)<((2:ℝ)^(T.grid i).level)⁻¹ := by
  have hpow : (2:ℝ)^(T.grid i).level≤(2:ℝ)^T.maxLevel :=
    pow_le_pow_right₀ (by norm_num) (T.level_le i)
  have hscale : ((2:ℝ)^T.maxLevel)⁻¹≤((2:ℝ)^(T.grid i).level)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hp : 0<((2:ℝ)^T.maxLevel)⁻¹ := by positivity
  unfold stop
  linarith

def Edges (i : F) := (T.grid i).grid.edges

def Roots := Σ i : F, T.Edges i × Bool

noncomputable instance edgesFintype (i : F) : Fintype (T.Edges i) :=
  inferInstanceAs (Fintype (T.grid i).grid.edges)

noncomputable instance rootsFintype : Fintype T.Roots :=
  inferInstanceAs (Fintype (Σ i : F, T.Edges i × Bool))

noncomputable def root (hsource : PublishedInvarianceOfDomain) (j : T.Roots) : ℂ :=
  axialPlaneHomeomorph (if j.2.2 then (((T.grid j.1).presentation hsource).edge j.2.1).last
    else (((T.grid j.1).presentation hsource).edge j.2.1).first)

def vertex (i : F) (e : T.Edges i) (b : Bool) : T.Roots := ⟨i,e,b⟩

noncomputable def probe (n : ℕ) : Probe where
  mesh := ((2:ℝ)^n)⁻¹
  center := (0,0)
  innerRadius := 1
  outerRadius := 5
  mesh_pos := by positivity
  inner_pos := by norm_num
  radii := by norm_num

omit [Fintype F] in
theorem vertex_position (hsource : PublishedInvarianceOfDomain) (n : ℕ)
    (i : F) (e : T.Edges i) (b : Bool) :
    T.root hsource (T.vertex i e b)=axialPhysical ((2:ℝ)^n)⁻¹
      (if b then (((T.grid i).meshPresentation hsource n).edge e).last
        else (((T.grid i).meshPresentation hsource n).edge e).first) :=
  ((T.grid i).mesh_endpoint hsource n (probe n) rfl e b).symm

theorem feature_scale (n : ℕ) (i : F) :
    6*(T.stop/8)<((2:ℝ)^n)⁻¹*(T.grid i).meshSpacing n :=
  (T.grid i).forest_scale_condition n _ T.stop rfl (T.stop_lt_spacing i)

omit [Fintype F] in
theorem parallel_separation (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (i : F) (e f : T.Edges i)
    (hne : (((T.grid i).meshPresentation hsource n).edge e).level≠
      (((T.grid i).meshPresentation hsource n).edge f).level) :
    (T.grid i).meshSpacing n≤|(((T.grid i).meshPresentation hsource n).edge e).level-
      (((T.grid i).meshPresentation hsource n).edge f).level| :=
  (T.grid i).mesh_level_separation hsource n e f hne

theorem integer_levels (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : T.maxLevel≤n) (i : F) (e : T.Edges i) :
    ∃ z : ℤ, (((T.grid i).meshPresentation hsource n).edge e).level=(z:ℝ) :=
  (T.grid i).meshPresentation_integer hsource n ((T.level_le i).trans hn) e

theorem crossing_dictionary (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : T.maxLevel≤n) (i : F) (ω : Configuration) :
    ((T.quad i).transport euclideanAxialShear).LiteralCrossing
      (globalPhysicalBlackCells (probe n) ω) ↔
      ((T.grid i).meshPolygon hsource n).Crossing ω :=
  (T.grid i).physical_crossing_dictionary hsource n ((T.level_le i).trans hn) (probe n) rfl ω

noncomputable def test (n : ℕ) (i : F) (ω : Configuration) : Bool :=
  decide (((T.quad i).transport euclideanAxialShear).LiteralCrossing
    (globalPhysicalBlackCells (probe n) ω))

theorem test_eq (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : T.maxLevel≤n) (i : F) (ω : Configuration) :
    T.test n i ω=((T.grid i).meshPolygon hsource n).test ω := by
  unfold test PolygonQuad.test
  exact propext (T.crossing_dictionary hsource n hn i ω) ▸ rfl

noncomputable def overwrittenCross {I S : Type*} (n : ℕ)
    (endpoint : I × Fin 2 ↪ Site) (background : S → Configuration) :
    F → S → (I → CenteredBlocks.PairColor) → Bool :=
  fun i s color => T.test n i (overwriteDimers endpoint (background s) color)

theorem overwrittenCross_eq {I S : Type*} (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (hn : T.maxLevel≤n) (endpoint : I × Fin 2 ↪ Site)
    (background : S → Configuration) :
    T.overwrittenCross n endpoint background=polygonOverwrittenCross endpoint
      (fun i => (T.grid i).meshPolygon hsource n) background := by
  funext i s color
  exact T.test_eq hsource n hn i _

/-- The actual geometry of any family of disjoint pairs at fixed lattice
displacement. Its finite root positions are independent of the mesh. -/
noncomputable def geometry {I : Type*} (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (z : Site) (endpoint : I × Fin 2 ↪ Site)
    (hdisplacement : ∀ i, endpoint (i,1)=endpoint (i,0)+z) : DimerGeometry I T.Roots :=
  displacedDimerGeometry ((2:ℝ)^n)⁻¹ (by positivity) z endpoint hdisplacement (T.root hsource)

omit [Fintype F] in
theorem geometry_vertex {I : Type*} (hsource : PublishedInvarianceOfDomain)
    (n : ℕ) (z : Site) (endpoint : I × Fin 2 ↪ Site)
    (hdisplacement : ∀ i, endpoint (i,1)=endpoint (i,0)+z)
    (i : F) (e : T.Edges i) (b : Bool) :
    (T.geometry hsource n z endpoint hdisplacement).root (T.vertex i e b)=
      axialPhysical (T.geometry hsource n z endpoint hdisplacement).mesh
        (if b then (((T.grid i).meshPresentation hsource n).edge e).last
          else (((T.grid i).meshPresentation hsource n).edge e).first) :=
  T.vertex_position hsource n i e b

#print axioms crossing_dictionary
#print axioms geometry_vertex

end DyadicQuadFamily
end ExceptionalTimes.PairSquareSewing
