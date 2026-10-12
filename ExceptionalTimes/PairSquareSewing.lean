import ExceptionalTimes.LatticeEmbedding
import ExceptionalTimes.SignedResponse
import ExceptionalTimes.ProbeProduct
import AdaptiveExchange

/-!
Concrete local pair/square insertions and the support of their signed
responses. Published inputs are event-level local-change implications
for actual annular four-arm requests; no pair/square error estimate is
assumed. The final weighted failure estimate is separate from the
published geometric construction of the successful seams.
-/

open scoped BigOperators Classical
open DimerBinaryResponse

namespace ExceptionalTimes.PairSquareSewing

open SignedResponse EnvironmentVariance

/-- Literal graph crossing in a finite collection of triangular sites.
A caller using a published polygon quad must check its closed-cell
discretization gives this domain and these terminal sets. -/
structure GraphQuad where
  domain : Finset Site
  firstSide : Finset Site
  secondSide : Finset Site

def GraphQuad.Crossing (Q : GraphQuad) (ω : Configuration) : Prop :=
  ∃ u ∈ Q.firstSide, ∃ v ∈ Q.secondSide, ∃ p : triangularGraph.Walk u v,
    ∀ z ∈ p.support, z ∈ Q.domain ∧ ω z = true

noncomputable def GraphQuad.test (Q : GraphQuad) (ω : Configuration) : Bool :=
  decide (Q.Crossing ω)

noncomputable def position (e : ℝ) (v : Site) : ℂ :=
  (e : ℂ) * triangularEmbedding v

/-- Literal piecewise-linear trace of the successive embedded graph edges. -/
def edgeTrace (e : ℝ) (u v : Site) : Set ℂ :=
  {q | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    q = (1 - (t : ℂ)) * position e u + (t : ℂ) * position e v}

def polygonalTrace (e : ℝ) {u v : Site} (p : triangularGraph.Walk u v) : Set ℂ :=
  match p with
  | .nil => {position e u}
  | @SimpleGraph.Walk.cons _ _ a b _ _ tail => edgeTrace e a b ∪ polygonalTrace e tail

/-- The literal geometric parameters of the source's unchanged probe. -/
structure Probe where
  mesh : ℝ
  center : Site
  innerRadius : ℝ
  outerRadius : ℝ
  mesh_pos : 0 < mesh
  inner_pos : 0 < innerRadius
  radii : 4 * innerRadius < outerRadius

noncomputable def Probe.radius (P : Probe) (v : Site) : ℝ :=
  dist (position P.mesh v) (position P.mesh P.center)

/-- Fixed-factor margins are retained explicitly. -/
def Probe.region (P : Probe) : Set Site :=
  {v | P.innerRadius / 2 ≤ P.radius v ∧ P.radius v ≤ 2 * P.outerRadius}

def Probe.pocket (P : Probe) : Set Site :=
  {v | P.radius v < P.innerRadius / 2}

/-- Cyclic order is taken at actual edge contacts on ONE common circle,
not at first-exit lattice vertices of potentially different radii. -/
def Probe.CyclicOuter (P : Probe) (q : Fin 4 → ℂ) : Prop :=
  (∀ i, dist (q i) (position P.mesh P.center) = P.outerRadius) ∧
  ∃ turns : Fin 4 → ℤ,
    let θ := fun i => Complex.arg (q i - position P.mesh P.center) +
      2 * Real.pi * (turns i : ℝ)
    StrictMono θ ∧ θ 3 < θ 0 + 2 * Real.pi

/-- The contact lies on the first edge reaching the common outer circle.
Every vertex of the preceding walk is strictly inside that circle; the
convexity of the disk then keeps every preceding edge inside too. -/
def Probe.OuterContact (P : Probe) {u v : Site}
    (p : triangularGraph.Walk u v) (q : ℂ) : Prop :=
  ∃ w : Site, ∃ initial : triangularGraph.Walk u w, ∃ last : TriangularAdj w v,
    p = initial.concat last ∧
      (∀ z ∈ initial.support, P.radius z < P.outerRadius) ∧
      q ∈ edgeTrace P.mesh w v ∧
      dist q (position P.mesh P.center) = P.outerRadius

/-- Actual disjoint simple lattice paths, with alternating colors and
geometric endpoint order; not an abstract arm-probability symbol. -/
def FourArms (P : Probe) (ω : Configuration) : Prop :=
  ∃ start finish : Fin 4 → Site,
    ∃ path : ∀ i, triangularGraph.Walk (start i) (finish i),
      (∀ i, (path i).IsPath) ∧
      (∀ i, P.radius (start i) ≤ P.innerRadius) ∧
      (∀ i, P.outerRadius ≤ P.radius (finish i)) ∧
      (∀ i z, z ∈ (path i).support →
        z ∈ P.region ∧ ω z = decide (i.val % 2 = 0)) ∧
      (∀ i j, i ≠ j → List.Disjoint (path i).support (path j).support) ∧
      ∃ contact : Fin 4 → ℂ,
        (∀ i, P.OuterContact (path i) (contact i)) ∧ P.CyclicOuter contact

/-- This is the two-source microscopic/mesoscopic necessary event.
The arguments carry separate actual probe radii and source colorings. -/
def SourceE (mic square : Probe) (ω η : Configuration) : Prop :=
  FourArms mic ω ∧ FourArms square η

/-- Event-level content of the source's Lemma 2.2 for the given actual
quad/probe dictionary. Other changes outside the probe may be fixed.
This is a named premise, not an axiom or a relative-error hypothesis. -/
def LocalChangeArms (Q : GraphQuad) (P : Probe) : Prop :=
  ∀ ω a b : Configuration,
    (∀ v, v ∉ P.pocket → a v = b v) →
    Set.EqOn a ω P.region → Set.EqOn b ω P.region →
    Q.test a ≠ Q.test b → FourArms P ω

/-- Actual local pair overwrite. The partner is the literal site x+z. -/
def putPair (ω : Configuration) (x z : Site) (u v : Bool) : Configuration :=
  Function.update (Function.update ω x u) (x + z) v

@[simp] theorem putPair_outside (ω : Configuration) (x z y : Site)
    (u v : Bool) (hy : y ≠ x) (hyz : y ≠ x + z) :
    putPair ω x z u v y = ω y := by simp [putPair, hy, hyz]

theorem pair_radius (e : ℝ) (x z : Site) :
    dist (position e (x + z)) (position e x) =
      |e| * ‖triangularEmbedding z‖ := by
  rw [Complex.dist_eq, position, position, ← mul_sub,
    ← triangularEmbedding_sub]
  simp

theorem pair_fits_pocket (P : Probe) (z : Site)
    (hz : |P.mesh| * ‖triangularEmbedding z‖ < P.innerRadius / 2) :
    P.center ∈ P.pocket ∧ P.center + z ∈ P.pocket := by
  constructor
  · change dist _ _ < P.innerRadius / 2
    rw [dist_self]
    linarith [P.inner_pos]
  · change dist _ _ < P.innerRadius / 2
    rwa [pair_radius]

theorem pocket_not_region (P : Probe) {v : Site} (hv : v ∈ P.pocket) :
    v ∉ P.region := by
  intro h
  exact (not_lt_of_ge h.1) hv

abbrev TwoTimeConfiguration := Bool → Configuration

/-- Pair annotations are separate from the two exterior backgrounds. -/
def pairHistory (background : TwoTimeConfiguration) (x z : Site)
    (before after : State) : TwoTimeConfiguration :=
  fun t => if t then putPair (background t) x z after.1 after.2
    else putPair (background t) x z before.1 before.2

noncomputable def crossingVector {Q : Type*} (quads : Q → GraphQuad)
    (ω : TwoTimeConfiguration) : Q × Bool → Bool :=
  fun qt => (quads qt.1).test (ω qt.2)

/-- The actual sixteen equally weighted experiments for U_A=P_A-P_0.
Both endpoint bits are integrated jointly. -/
noncomputable def rawPairResponse (K : Kernel) (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) : ℝ :=
  (1 / 16) * ∑ u : Bool, ∑ v : Bool, ∑ coin : Bool, ∑ extra : Bool,
    (F (pairHistory background x z (u,v) (K u v coin extra)) -
      F (pairHistory background x z (u,v) (u,v)))

theorem nonzero_pair_change {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (K : Kernel)
    (background : TwoTimeConfiguration) (x z : Site)
    (hne : rawPairResponse K background x z
      (fun η => outer (crossingVector quads η)) ≠ 0) :
    ∃ u v coin extra q t,
      (quads q).test (pairHistory background x z (u,v) (K u v coin extra) t) ≠
      (quads q).test (pairHistory background x z (u,v) (u,v) t) := by
  by_contra hn
  apply hne
  have heq : ∀ u v coin extra,
      crossingVector quads (pairHistory background x z (u,v) (K u v coin extra)) =
      crossingVector quads (pairHistory background x z (u,v) (u,v)) := by
    intro u v coin extra
    funext qt
    exact not_not.mp (fun h => hn ⟨u,v,coin,extra,qt.1,qt.2,h⟩)
  simp [rawPairResponse, heq]

/-- A raw nonzero joint-pair response supplies the source's actual
four-arm request on untouched fair colors, with no union over histories. -/
theorem pair_response_source_arm {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (K : Kernel)
    (P : Probe) (z : Site) (ω : Configuration)
    (background : TwoTimeConfiguration)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hpair : P.center ∈ P.pocket ∧ P.center + z ∈ P.pocket)
    (hbackground : ∀ t, Set.EqOn (background t) ω P.region)
    (hne : rawPairResponse K background P.center z
      (fun η => outer (crossingVector quads η)) ≠ 0) : FourArms P ω := by
  obtain ⟨u,v,coin,extra,q,t,hchange⟩ :=
    nonzero_pair_change quads outer K background P.center z hne
  apply hlocal q ω _ _ _ _ _ hchange
  · intro y hy
    have hy₁ : y ≠ P.center := fun h => hy (h ▸ hpair.1)
    have hy₂ : y ≠ P.center + z := fun h => hy (h ▸ hpair.2)
    cases t <;> simp [pairHistory, putPair, hy₁, hy₂]
  · intro y hy
    have hy₁ : y ≠ P.center := fun h =>
      pocket_not_region P hpair.1 (h ▸ hy)
    have hy₂ : y ≠ P.center + z := fun h =>
      pocket_not_region P hpair.2 (h ▸ hy)
    cases t <;> simpa [pairHistory, putPair, hy₁, hy₂] using hbackground _ hy
  · intro y hy
    have hy₁ : y ≠ P.center := fun h =>
      pocket_not_region P hpair.1 (h ▸ hy)
    have hy₂ : y ≠ P.center + z := fun h =>
      pocket_not_region P hpair.2 (h ▸ hy)
    cases t <;> simpa [pairHistory, putPair, hy₁, hy₂] using hbackground _ hy

/-- The forcing set is a fixed actual finite set of lattice sites, e.g.
the sites whose hexagonal cells meet the physical source square. -/
def force (D : Finset Site) (ω : Configuration) (b : Bool) : Configuration :=
  fun v => if v ∈ D then b else ω v

def squareHistory (D : Finset Site) (background : TwoTimeConfiguration)
    (h : History) : TwoTimeConfiguration :=
  fun t => force D (background t) (if t then h.2 else h.1)

noncomputable def rawSquareResponse (D : Finset Site) (background : TwoTimeConfiguration)
    (F : TwoTimeConfiguration → ℝ) : ℝ :=
  bitResponse (fun h => F (squareHistory D background h))

/-- A nonzero W-square response also forces the actual annular request.
The proof uses centering, not an event that the fair square is monochromatic. -/
theorem square_response_source_arm {Q : Type*} (quads : Q → GraphQuad)
    (outer : (Q × Bool → Bool) → ℝ) (P : Probe)
    (D : Finset Site) (ω : Configuration) (background : TwoTimeConfiguration)
    (hlocal : ∀ q, LocalChangeArms (quads q) P)
    (hD : (D : Set Site) ⊆ P.pocket)
    (hbackground : ∀ t, Set.EqOn (background t) ω P.region)
    (hne : rawSquareResponse D background
      (fun η => outer (crossingVector quads η)) ≠ 0) : FourArms P ω := by
  by_contra hno
  have hconstant : ∀ h : History,
      crossingVector quads (squareHistory D background h) =
      crossingVector quads (squareHistory D background (false,false)) := by
    intro h
    funext qt
    by_contra hc
    apply hno
    apply hlocal qt.1 ω _ _ _ _ _ hc
    · intro v hv
      have hvD : v ∉ D := fun hmem => hv (hD hmem)
      simp [squareHistory, force, hvD]
    · intro v hv
      have hvD : v ∉ D := fun hmem => pocket_not_region P (hD hmem) hv
      simpa [squareHistory, force, hvD] using hbackground qt.2 hv
    · intro v hv
      have hvD : v ∉ D := fun hmem => pocket_not_region P (hD hmem) hv
      simpa [squareHistory, force, hvD] using hbackground qt.2 hv
  apply hne
  simp [rawSquareResponse, hconstant]

theorem rawPairResponse_bound (K : Kernel) (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) (hF : ∀ η, |F η| ≤ 1) :
    |rawPairResponse K background x z F| ≤ 2 := by
  let f := fun u v coin extra : Bool =>
    F (pairHistory background x z (u,v) (K u v coin extra)) -
      F (pairHistory background x z (u,v) (u,v))
  have hf : ∀ u v coin extra, |f u v coin extra| ≤ 2 := by
    intro u v coin extra
    exact (abs_sub _ _).trans (by
      have h₁ := hF (pairHistory background x z (u,v) (K u v coin extra))
      have h₂ := hF (pairHistory background x z (u,v) (u,v))
      linarith)
  have hs : |∑ u : Bool, ∑ v : Bool, ∑ c : Bool, ∑ d : Bool, f u v c d| ≤ 32 := by
    calc
      _ ≤ ∑ u : Bool, |∑ v : Bool, ∑ c : Bool, ∑ d : Bool, f u v c d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u : Bool, ∑ v : Bool, |∑ c : Bool, ∑ d : Bool, f u v c d| :=
        Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u : Bool, ∑ v : Bool, ∑ c : Bool, |∑ d : Bool, f u v c d| :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u : Bool, ∑ v : Bool, ∑ c : Bool, ∑ d : Bool, |f u v c d| :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          Finset.sum_le_sum fun c _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u : Bool, ∑ _v : Bool, ∑ _c : Bool, ∑ _d : Bool, (2 : ℝ) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => hf u v c d
      _ = 32 := by norm_num
  change |(1 / 16 : ℝ) * ∑ u : Bool, ∑ v : Bool, ∑ c : Bool, ∑ d : Bool, f u v c d| ≤ 2
  rw [abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
  linarith

theorem bitResponse_bound (f : History → ℝ) (hf : ∀ h, |f h| ≤ 1) :
    |bitResponse f| ≤ 1 := by
  have h₁ := abs_add_le (f (false,true)) (f (true,false))
  have h₂ := abs_sub (f (false,true) + f (true,false)) (f (false,false))
  have h₃ := abs_sub (f (false,true) + f (true,false) - f (false,false)) (f (true,true))
  have ha := hf (false,true)
  have hb := hf (true,false)
  have hc := hf (false,false)
  have hd := hf (true,true)
  rw [bitResponse, abs_div]
  norm_num
  linarith

theorem rawSquareResponse_bound (D : Finset Site) (background : TwoTimeConfiguration)
    (F : TwoTimeConfiguration → ℝ) (hF : ∀ η, |F η| ≤ 1) :
    |rawSquareResponse D background F| ≤ 1 :=
  bitResponse_bound _ (fun _ => hF _)

/-- Signed products have a bounded density even though their components
are not positive measures. No reciprocal arm factor appears here. -/
theorem raw_product_bound (K : Kernel) (D : Finset Site)
    (backgroundA backgroundB : TwoTimeConfiguration) (x z : Site)
    (F G : TwoTimeConfiguration → ℝ)
    (hF : ∀ η, |F η| ≤ 1) (hG : ∀ η, |G η| ≤ 1) :
    |rawPairResponse K backgroundA x z F *
      rawSquareResponse D backgroundB G| ≤ 2 := by
  rw [abs_mul]
  have h := mul_le_mul
    (rawPairResponse_bound K backgroundA x z F hF)
    (rawSquareResponse_bound D backgroundB G hG)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  simpa using h

/-- Combining the two genuinely local implications gives the source E
for the actual pair/square product, not a presumed relative-error bound. -/
theorem nonzero_product_sourceE {QA QB : Type*}
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (K : Kernel) (mic sq : Probe) (z : Site) (D : Finset Site)
    (ω η : Configuration) (backgroundA backgroundB : TwoTimeConfiguration)
    (hlocalA : ∀ q, LocalChangeArms (quadsA q) mic)
    (hlocalB : ∀ q, LocalChangeArms (quadsB q) sq)
    (hpair : mic.center ∈ mic.pocket ∧ mic.center + z ∈ mic.pocket)
    (hD : (D : Set Site) ⊆ sq.pocket)
    (hA : ∀ t, Set.EqOn (backgroundA t) ω mic.region)
    (hB : ∀ t, Set.EqOn (backgroundB t) η sq.region)
    (hne : rawPairResponse K backgroundA mic.center z
      (fun ξ => outerA (crossingVector quadsA ξ)) *
      rawSquareResponse D backgroundB
      (fun ξ => outerB (crossingVector quadsB ξ)) ≠ 0) :
    SourceE mic sq ω η := by
  refine ⟨pair_response_source_arm quadsA outerA K mic z ω backgroundA
    hlocalA hpair hA ?_, square_response_source_arm quadsB outerB sq D η
    backgroundB hlocalB hD hB ?_⟩
  · intro h
    exact hne (by rw [h, zero_mul])
  · intro h
    exact hne (by rw [h, mul_zero])

/-- A source necklace theorem supplies these pointwise evaluation
equalities on its success event. They concern actual local overwrites,
and their joint signed integration is proved below. -/
def PairTransmission (background : TwoTimeConfiguration) (x z : Site)
    (F : TwoTimeConfiguration → ℝ) (φ : Table) (f : History → ℝ) : Prop :=
  ∀ a b : State,
    F (pairHistory background x z a b) =
      f (φ.eval a.1 a.2, φ.eval b.1 b.2)

def SquareTransmission (D : Finset Site) (background : TwoTimeConfiguration)
    (F : TwoTimeConfiguration → ℝ) (ψ : Bool → Bool) (f : History → ℝ) : Prop :=
  ∀ h : History, F (squareHistory D background h) = f (ψ h.1, ψ h.2)

theorem rawPairResponse_transmitted (K : Kernel) (background : TwoTimeConfiguration)
    (x z : Site) (F : TwoTimeConfiguration → ℝ) (φ : Table) (f : History → ℝ)
    (h : PairTransmission background x z F φ f) :
    rawPairResponse K background x z F = pairResponse φ K f := by
  dsimp [PairTransmission] at h
  simp only [rawPairResponse, h, pairResponse]

noncomputable def squareAmplitude (ψ : Bool → Bool) : ℝ :=
  if ψ false = ψ true then 0 else 1

theorem square_bit_factor (ψ : Bool → Bool) (hψ : ψ false = true → ψ true = true)
    (f : History → ℝ) :
    bitResponse (fun h => f (ψ h.1, ψ h.2)) =
      squareAmplitude ψ * bitResponse f := by
  cases h0 : ψ false <;> cases h1 : ψ true <;>
    simp_all [squareAmplitude, bitResponse]

theorem rawSquareResponse_transmitted (D : Finset Site)
    (background : TwoTimeConfiguration) (F : TwoTimeConfiguration → ℝ)
    (ψ : Bool → Bool) (f : History → ℝ)
    (hψ : ψ false = true → ψ true = true)
    (h : SquareTransmission D background F ψ f) :
    rawSquareResponse D background F = squareAmplitude ψ * bitResponse f := by
  dsimp [SquareTransmission] at h
  unfold rawSquareResponse
  simp_rw [h]
  exact square_bit_factor ψ hψ f

/-- Four literal before/after evaluations encode transporting the pair and
square annotations, while their exterior test functions stay fixed. -/
theorem successful_signed_exchange
    (K : Kernel) (D : Finset Site) (x z : Site)
    (A B A' B' : TwoTimeConfiguration) (F G : TwoTimeConfiguration → ℝ)
    (φ : Table) (ψ : Bool → Bool) (f g : History → ℝ) (c : ℝ)
    (hK : ∀ test, pairResponse φ K test = c * bitResponse test)
    (hψ : ψ false = true → ψ true = true)
    (hAF : PairTransmission A x z F φ f)
    (hBG : SquareTransmission D B G ψ g)
    (hA'F : SquareTransmission D A' F ψ f)
    (hB'G : PairTransmission B' x z G φ g) :
    rawPairResponse K A x z F * rawSquareResponse D B G =
      rawSquareResponse D A' F * rawPairResponse K B' x z G := by
  rw [rawPairResponse_transmitted K A x z F φ f hAF,
    rawSquareResponse_transmitted D B G ψ g hψ hBG,
    rawSquareResponse_transmitted D A' F ψ f hψ hA'F,
    rawPairResponse_transmitted K B' x z G φ g hB'G, hK, hK]
  ring


/-- Two independent fair fields on an actual finite site set containing
all tested sites and trial supports. The completion outside is irrelevant
once the cylinder supports have been checked. -/
abbrev Sources (Λ : Finset Site) := (↥Λ → Bool) × (↥Λ → Bool)

def complete {Λ : Finset Site} (ω : ↥Λ → Bool) : Configuration :=
  fun v => if hv : v ∈ Λ then ω ⟨v,hv⟩ else false

noncomputable def sourceLaw (Λ : Finset Site) : FiniteLaw (Sources Λ) :=
  (ProbeProduct.fairSites ↥Λ).prod (ProbeProduct.fairSites ↥Λ)

/-- Literal exchange of both source interiors at a deterministic site cut. -/
def seamSwap {Λ : Finset Site} (inside : Finset Site) (ω : Sources Λ) : Sources Λ :=
  (fun v => if (v : Site) ∈ inside then ω.2 v else ω.1 v,
   fun v => if (v : Site) ∈ inside then ω.1 v else ω.2 v)

theorem seamSwap_involutive {Λ : Finset Site} (inside : Finset Site) :
    Function.Involutive (seamSwap (Λ := Λ) inside) := by
  intro ω
  apply Prod.ext <;> funext v <;>
    by_cases hv : (v : Site) ∈ inside <;> simp [seamSwap, hv]

theorem sourceLaw_weight_constant {Λ : Finset Site} (ω η : Sources Λ) :
    (sourceLaw Λ).weight ω = (sourceLaw Λ).weight η := rfl

/-- Adaptivity preserves the actual finite iid law, rather than merely
being an abstract bijection of an unspecified probability space. -/
theorem adaptive_source_expect {Λ : Finset Site} {I : Type*}
    (success : I → Sources Λ → Bool) (inside : I → Finset Site) (trials : List I)
    (hinvariant : ∀ i ω, success i ω = true →
      ∀ j, success j (seamSwap (inside i) ω) = success j ω)
    (f : Sources Λ → ℝ) :
    (sourceLaw Λ).expect (fun ω =>
      f (AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials ω)) =
    (sourceLaw Λ).expect f := by
  let T := AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials
  have hT : Function.Involutive T :=
    AdaptiveExchange.applyFirst_involutive success (fun i => seamSwap (inside i))
      trials (fun i => seamSwap_involutive (inside i)) hinvariant
  let e : Sources Λ ≃ Sources Λ := ⟨T, T, hT, hT⟩
  change ∑ ω, (sourceLaw Λ).weight ω * f (e ω) =
    ∑ ω, (sourceLaw Λ).weight ω * f ω
  calc
    _ = ∑ ω, (sourceLaw Λ).weight (e ω) * f (e ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [sourceLaw_weight_constant ω (e ω)]
    _ = _ := e.sum_comp (fun ω => (sourceLaw Λ).weight ω * f ω)

theorem abs_le_indicator_of_support {A : Type*} (f : A → ℝ) (E : A → Prop)
    (B : ℝ) (hbound : ∀ ω, |f ω| ≤ B)
    (hsupport : ∀ ω, f ω ≠ 0 → E ω) (ω : A) :
    |f ω| ≤ B * indicator (E ω) := by
  classical
  by_cases h : E ω
  · simpa [indicator, h] using hbound ω
  · have hz : f ω = 0 := by
      by_contra hn
      exact h (hsupport ω hn)
    simp [hz, indicator, h]

/-- The source trial criterion has a probability of the literal
two-source E on its right, not a presumed signed replacement error.
The successful identity is supplied by transported annotation evaluations,
as proved in successful_signed_exchange. -/
theorem adaptive_failure_weighting {Λ : Finset Site} {I : Type*}
    (success : I → Sources Λ → Bool) (inside : I → Finset Site) (trials : List I)
    (hinvariant : ∀ i ω, success i ω = true →
      ∀ j, success j (seamSwap (inside i) ω) = success j ω)
    (mic sq : Probe) (L R : Sources Λ → ℝ) (B : ℝ)
    (hL : ∀ ω, |L ω| ≤ B) (hR : ∀ ω, |R ω| ≤ B)
    (hsL : ∀ ω, L ω ≠ 0 → SourceE mic sq (complete ω.1) (complete ω.2))
    (hsR : ∀ ω, R ω ≠ 0 → SourceE mic sq (complete ω.2) (complete ω.1))
    (hgood : ∀ ω, AdaptiveExchange.select success trials ω ≠ none →
      L ω = R (AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials ω)) :
    |(sourceLaw Λ).expect L - (sourceLaw Λ).expect R| ≤
      B * (probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select success trials ω = none ∧
          SourceE mic sq (complete ω.1) (complete ω.2)) +
      probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select success trials ω = none ∧
          SourceE mic sq (complete ω.2) (complete ω.1))) := by
  classical
  let T := AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials
  let N := fun ω => AdaptiveExchange.select success trials ω = none
  let E₁ := fun ω : Sources Λ => SourceE mic sq (complete ω.1) (complete ω.2)
  let E₂ := fun ω : Sources Λ => SourceE mic sq (complete ω.2) (complete ω.1)
  have hdiff : (sourceLaw Λ).expect L - (sourceLaw Λ).expect R =
      (sourceLaw Λ).expect (fun ω => if N ω then L ω - R ω else 0) := by
    rw [← adaptive_source_expect success inside trials hinvariant R,
      ← FiniteLaw.expect_sub]
    apply FiniteLaw.expect_congr
    intro ω
    by_cases hn : N ω
    · have ht : T ω = ω := by
        have hs : AdaptiveExchange.select success trials ω = none := hn
        simp [T, AdaptiveExchange.applyFirst, hs]
      change L ω - R (T ω) = _
      simp [hn, ht]
    · have hg := hgood ω hn
      change L ω = R (T ω) at hg
      change L ω - R (T ω) = _
      simp [hn, hg]
  rw [hdiff]
  calc
    _ ≤ (sourceLaw Λ).expect
        (fun ω => |if N ω then L ω - R ω else 0|) :=
      FiniteLaw.abs_expect_le _ _
    _ ≤ (sourceLaw Λ).expect
        (fun ω => B * (indicator (N ω ∧ E₁ ω) + indicator (N ω ∧ E₂ ω))) := by
      apply FiniteLaw.expect_mono
      intro ω
      by_cases hn : N ω
      · have ha := abs_le_indicator_of_support L E₁ B hL hsL ω
        have hb := abs_le_indicator_of_support R E₂ B hR hsR ω
        simp only [ite_eq_left hn]
        simpa [indicator, hn, mul_add] using
          (abs_sub (L ω) (R ω)).trans (add_le_add ha hb)
      · simp [hn, indicator]
    _ = _ := by
      rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_add]
      rfl

#print axioms pair_response_source_arm
#print axioms square_response_source_arm
#print axioms nonzero_product_sourceE
#print axioms successful_signed_exchange
#print axioms adaptive_source_expect
#print axioms adaptive_failure_weighting


inductive Rule where
  | canonical
  | refresh

def Rule.kernel : Rule → Kernel
  | .canonical => DimerBinaryResponse.canonical
  | .refresh => DimerBinaryResponse.refresh

noncomputable def Rule.amplitude : Rule → Table → ℝ
  | .canonical => canonicalAmplitude
  | .refresh => refreshAmplitude

theorem Rule.response (A : Rule) (φ : Table) (hφ : Increasing φ)
    (f : History → ℝ) :
    pairResponse φ A.kernel f = A.amplitude φ * bitResponse f := by
  cases A
  · exact canonical_response φ hφ f
  · exact refresh_response φ hφ f

/-- The literal successful-seam content needed from source Lemma 6.5.
A and B include any fixed exterior annotations. Primed configurations
are obtained from the same annotation maps after exchanging the raw
fair interiors. No signed expectation occurs in this premise. -/
def TransmittedAnnotations (D : Finset Site) (x z : Site)
    (A B A' B' : TwoTimeConfiguration) (F G : TwoTimeConfiguration → ℝ) : Prop :=
  ∃ φ : Table, ∃ ψ : Bool → Bool, ∃ f g : History → ℝ,
    Increasing φ ∧ (ψ false = true → ψ true = true) ∧
      PairTransmission A x z F φ f ∧ SquareTransmission D B G ψ g ∧
      SquareTransmission D A' F ψ f ∧ PairTransmission B' x z G φ g

/-- A concrete finite-model sewing bound. Its right side is the probability
of the source's failed two-arm-probe event, to which the literal Lemma 6.6
and many-trial bound apply. It is not an assumed pair-relative-error.
Background maps allow arbitrary fixed other histories outside the probes.
All averaging is over the original two independent fair site fields. -/
theorem pair_square_sewing_failure_bound
    {Λ : Finset Site} {I QA QB : Type*}
    (success : I → Sources Λ → Bool) (inside : I → Finset Site) (trials : List I)
    (hinvariant : ∀ i ω, success i ω = true →
      ∀ j, success j (seamSwap (inside i) ω) = success j ω)
    (mic sq : Probe) (z : Site) (D : Finset Site) (rule : Rule)
    (A B : Sources Λ → TwoTimeConfiguration)
    (quadsA : QA → GraphQuad) (quadsB : QB → GraphQuad)
    (outerA : (QA × Bool → Bool) → ℝ) (outerB : (QB × Bool → Bool) → ℝ)
    (hboundA : ∀ c, |outerA c| ≤ 1) (hboundB : ∀ c, |outerB c| ≤ 1)
    (hlocalAmic : ∀ q, LocalChangeArms (quadsA q) mic)
    (hlocalAsq : ∀ q, LocalChangeArms (quadsA q) sq)
    (hlocalBmic : ∀ q, LocalChangeArms (quadsB q) mic)
    (hlocalBsq : ∀ q, LocalChangeArms (quadsB q) sq)
    (hpair : mic.center ∈ mic.pocket ∧ mic.center + z ∈ mic.pocket)
    (hD : (D : Set Site) ⊆ sq.pocket)
    (hAmic : ∀ ω t, Set.EqOn (A ω t) (complete ω.1) mic.region)
    (hAsq : ∀ ω t, Set.EqOn (A ω t) (complete ω.1) sq.region)
    (hBmic : ∀ ω t, Set.EqOn (B ω t) (complete ω.2) mic.region)
    (hBsq : ∀ ω t, Set.EqOn (B ω t) (complete ω.2) sq.region)
    (htransmit : ∀ ω, AdaptiveExchange.select success trials ω ≠ none →
      let ω' := AdaptiveExchange.applyFirst success (fun i => seamSwap (inside i)) trials ω
      TransmittedAnnotations D mic.center z (A ω) (B ω) (A ω') (B ω')
        (fun ξ => outerA (crossingVector quadsA ξ))
        (fun ξ => outerB (crossingVector quadsB ξ))) :
    |(sourceLaw Λ).expect (fun ω =>
        rawPairResponse rule.kernel (A ω) mic.center z
          (fun ξ => outerA (crossingVector quadsA ξ)) *
        rawSquareResponse D (B ω) (fun ξ => outerB (crossingVector quadsB ξ))) -
      (sourceLaw Λ).expect (fun ω =>
        rawSquareResponse D (A ω) (fun ξ => outerA (crossingVector quadsA ξ)) *
        rawPairResponse rule.kernel (B ω) mic.center z
          (fun ξ => outerB (crossingVector quadsB ξ)))| ≤
      2 * (probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select success trials ω = none ∧
          SourceE mic sq (complete ω.1) (complete ω.2)) +
      probability (sourceLaw Λ) (fun ω =>
        AdaptiveExchange.select success trials ω = none ∧
          SourceE mic sq (complete ω.2) (complete ω.1))) := by
  apply adaptive_failure_weighting success inside trials hinvariant mic sq
  · intro ω
    exact raw_product_bound rule.kernel D (A ω) (B ω) mic.center z _ _
      (fun ξ => hboundA _) (fun ξ => hboundB _)
  · intro ω
    rw [mul_comm]
    exact raw_product_bound rule.kernel D (B ω) (A ω) mic.center z _ _
      (fun ξ => hboundB _) (fun ξ => hboundA _)
  · intro ω hn
    exact nonzero_product_sourceE quadsA quadsB outerA outerB rule.kernel mic sq z D
      (complete ω.1) (complete ω.2) (A ω) (B ω) hlocalAmic hlocalBsq hpair hD
      (hAmic ω) (hBsq ω) hn
  · intro ω hn
    rw [mul_comm] at hn
    exact nonzero_product_sourceE quadsB quadsA outerB outerA rule.kernel mic sq z D
      (complete ω.2) (complete ω.1) (B ω) (A ω) hlocalBmic hlocalAsq hpair hD
      (hBmic ω) (hAsq ω) hn
  · intro ω hsuccess
    obtain ⟨φ, ψ, f, g, hφ, hψ, hAF, hBG, hA'F, hB'G⟩ := htransmit ω hsuccess
    exact successful_signed_exchange rule.kernel D mic.center z _ _ _ _ _ _
      φ ψ f g (rule.amplitude φ) (rule.response φ hφ) hψ hAF hBG hA'F hB'G

#print axioms pair_square_sewing_failure_bound

end ExceptionalTimes.PairSquareSewing











