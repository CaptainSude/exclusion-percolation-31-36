import ExceptionalTimes.HexGaugePaths

open Set
open scoped Classical unitInterval

namespace ExceptionalTimes.Annulus

open TriangularPlane

/-- Counterclockwise order about the origin, with an arbitrary common
choice of angle lift. This predicate contains no color or arm event. -/
def CyclicAngles (z : Fin 4 → ℂ) : Prop :=
  ∃ turns : Fin 4 → ℤ,
    let θ := fun i => Complex.arg (z i)+2*Real.pi*(turns i:ℝ)
    StrictMono θ ∧ θ 3 < θ 0+2*Real.pi

/-- Classical deterministic planar separation input used in source02,
the proof of Lemma2.2, in the sentences beginning "Trim each path at
surrounding curves" and "Planar separation puts the four parts in
alternating order" (source commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a).

This is the crosscut-order form of that topological step, stated only for
actual continuous injective curves in a literal Euclidean annulus.
Their traces are disjoint, their endpoints lie on the two exact circles,
and their open parts lie strictly between them. Both circle orders use
the same counterclockwise polar convention. No polygon validity, lattice
path extraction, colors, arm probability, or sewing estimate is assumed.
It is an explicit named theorem parameter, never a global axiom. -/
def PublishedAnnularCrosscutOrder : Prop :=
  ∀ (r R : ℝ), 0 < r → r < R → ∀ γ : Fin 4 → unitInterval → ℂ,
    (∀ i, Continuous (γ i)) →
    (∀ i, Function.Injective (γ i)) →
    (∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))) →
    (∀ i, ‖γ i 0‖ = r ∧ ‖γ i 1‖ = R) →
    (∀ i (t : unitInterval), 0 < (t:ℝ) → (t:ℝ) < 1 → r < ‖γ i t‖ ∧ ‖γ i t‖ < R) →
    (CyclicAngles (fun i => γ i 0) ↔ CyclicAngles (fun i => γ i 1))

noncomputable def roundWalk {u v : Site} (p : triangularGraph.Walk u v) (r R : ℝ)
    (hr : 0 < r) (hm : ∀ t, walkPath p t ∈ hexAnnulus r R) : unitInterval → ℂ :=
  fun t => (hexAnnulusHomeomorph r R hr ⟨walkPath p t,hm t⟩ : ℂ)

theorem continuous_roundWalk {u v : Site} (p : triangularGraph.Walk u v) (r R : ℝ)
    (hr : 0 < r) (hm : ∀ t, walkPath p t ∈ hexAnnulus r R) :
    Continuous (roundWalk p r R hr hm) :=
  continuous_subtype_val.comp ((hexAnnulusHomeomorph r R hr).continuous.comp
    ((walkPath p).continuous.subtype_mk hm))

theorem roundWalk_injective {u v : Site} (p : triangularGraph.Walk u v) (r R : ℝ)
    (hr : 0 < r) (hm : ∀ t, walkPath p t ∈ hexAnnulus r R)
    (hp : Function.Injective (walkPath p)) : Function.Injective (roundWalk p r R hr hm) := by
  intro s t h
  have hh := (hexAnnulusHomeomorph r R hr).injective (Subtype.ext h)
  exact hp (congrArg Subtype.val hh)

theorem roundWalk_norm {u v : Site} (p : triangularGraph.Walk u v) (r R : ℝ)
    (hr : 0 < r) (hm : ∀ t, walkPath p t ∈ hexAnnulus r R) (t : unitInterval) :
    ‖roundWalk p r R hr hm t‖ = hexGauge (walkPath p t) :=
  hexAnnulusHomeomorph_radius r R hr _

theorem roundWalk_arg {u v : Site} (p : triangularGraph.Walk u v) (r R : ℝ)
    (hr : 0 < r) (hm : ∀ t, walkPath p t ∈ hexAnnulus r R) (t : unitInterval) :
    Complex.arg (roundWalk p r R hr hm t) = Complex.arg (HexTiling.planeMap (walkPath p t)) :=
  hexAnnulusHomeomorph_arg r R hr _

/-- All topological hypotheses are verified on actual proper simple
lattice paths between the exact positive hex levels. The only input is
the classical order theorem on round annuli stated above. -/
theorem proper_hex_paths_cyclic_order (orderInput : PublishedAnnularCrosscutOrder)
    (r R : ℤ) (hr : 0 < r) (hrR : r < R)
    (s t : Fin 4 → Site) (p : ∀ i, triangularGraph.Walk (s i) (t i))
    (hp : ∀ i, (p i).IsPath)
    (hs : ∀ i, hexRadius (s i) = r) (ht : ∀ i, hexRadius (t i) = R)
    (hb : ∀ i z, z ∈ (p i).support → r ≤ hexRadius z ∧ hexRadius z ≤ R)
    (hin : ∀ i z, z ∈ (p i).support → hexRadius z = r → z = s i)
    (hout : ∀ i z, z ∈ (p i).support → hexRadius z = R → z = t i)
    (hdis : ∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) :
    CyclicAngles (fun i => triangularEmbedding (s i)) ↔
      CyclicAngles (fun i => triangularEmbedding (t i)) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hrR' : (r:ℝ) < R := by exact_mod_cast hrR
  have htop (i : Fin 4) := walkPath_proper_hexAnnulus (p i) hrR (hp i) (hs i) (ht i)
    (hb i) (hin i) (hout i)
  let γ : Fin 4 → unitInterval → ℂ := fun i => roundWalk (p i) r R hr' (htop i).2.1
  have hc : ∀ i, Continuous (γ i) := fun i => continuous_roundWalk _ _ _ _ _
  have hj : ∀ i, Function.Injective (γ i) :=
    fun i => roundWalk_injective _ _ _ _ _ (htop i).1
  have hd : ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨a,rfl⟩ ⟨b,hb⟩
    have he := (hexAnnulusHomeomorph (r:ℝ) R hr').injective (Subtype.ext hb)
    have he' := congrArg Subtype.val he
    change walkPath (p j) b = walkPath (p i) a at he'
    have hai : walkPath (p i) a ∈ walkTrace (p i) :=
      (Set.ext_iff.mp (walkPath_range (p i)) _).mp ⟨a,rfl⟩
    have hbj : walkPath (p j) b ∈ walkTrace (p j) :=
      (Set.ext_iff.mp (walkPath_range (p j)) _).mp ⟨b,rfl⟩
    have htr := disjoint_supports_disjoint_traces (p i) (p j)
      (fun x hxi hxj => hdis i j hij hxi hxj)
    exact Set.disjoint_left.mp htr hai (he' ▸ hbj)
  have he : ∀ i, ‖γ i 0‖ = (r:ℝ) ∧ ‖γ i 1‖ = (R:ℝ) := by
    intro i
    constructor
    · change ‖roundWalk _ _ _ _ _ 0‖ = _
      rw [roundWalk_norm,(walkPath (p i)).source,hexGauge_point,hs]
    · change ‖roundWalk _ _ _ _ _ 1‖ = _
      rw [roundWalk_norm,(walkPath (p i)).target,hexGauge_point,ht]
  have ho : ∀ i (a : unitInterval), 0 < (a:ℝ) → (a:ℝ) < 1 → (r:ℝ) < ‖γ i a‖ ∧ ‖γ i a‖ < (R:ℝ) := by
    intro i a ha ha'
    change (r:ℝ) < ‖roundWalk _ _ _ _ _ a‖ ∧ ‖roundWalk _ _ _ _ _ a‖ < (R:ℝ)
    rw [roundWalk_norm]
    exact (htop i).2.2 a ha ha'
  have horder := orderInput r R hr' hrR' γ hc hj hd he ho
  have ha0 (i : Fin 4) : Complex.arg (γ i 0) = Complex.arg (triangularEmbedding (s i)) := by
    change Complex.arg (roundWalk _ _ _ _ _ 0) = _
    rw [roundWalk_arg,(walkPath (p i)).source]
    rfl
  have ha1 (i : Fin 4) : Complex.arg (γ i 1) = Complex.arg (triangularEmbedding (t i)) := by
    change Complex.arg (roundWalk _ _ _ _ _ 1) = _
    rw [roundWalk_arg,(walkPath (p i)).target]
    rfl
  simpa only [CyclicAngles,ha0,ha1] using horder

#print axioms proper_hex_paths_cyclic_order

end ExceptionalTimes.Annulus
