import ExceptionalTimes.ClockTruncation
import ExceptionalTimes.FiniteSpectralEnergy

/-!
# Concrete finite clock sweeps and finite color cubes

A sweep lists the actual retained clock marks from latest to earliest.
Its deterministic color composition is proved equal to the existing
latest-mark/backward-label construction. This supplies the pathwise
identification needed before applying the finite Poisson-update theorem
in Levin--Peres, Markov Chains and Mixing Times, second edition, §20.1.
-/

open MeasureTheory
open scoped BigOperators Matrix ENNReal

namespace ExceptionalTimes.FiniteClockBridge

variable {I : Type*}

/-- The selected mark is globally latest, and is the only unordered pair
ringing at its time. This is stronger than absence of incident ties. -/
structure LatestGlobalMark (C : ClockField) (edge : I → Site × Site)
    (c : TimeCutoff) (t : ℝ) (i : I) : Prop where
  rings : C.Rings (edge i).1 (edge i).2 t
  allowed : c.Allows t
  latest : ∀ u v r, C.Rings u v r → c.Allows r → r ≤ t
  unique_pair : ∀ u v, C.Rings u v t → s(u, v) = s((edge i).1, (edge i).2)

/-- Every stage removes the unique latest mark and continues strictly
before it. The final stage requires absence of ALL earlier marks. -/
inductive IsSweep (C : ClockField) (edge : I → Site × Site) :
    TimeCutoff → List (ℝ × I) → Prop
  | nil {c} (h : ∀ v, C.NoEligibleRing c v) : IsSweep C edge c []
  | cons {c t i events} (h : LatestGlobalMark C edge c t i)
      (tail : IsSweep C edge (TimeCutoff.before t) events) :
      IsSweep C edge c ((t, i) :: events)

/-- Backward labels through a descending list of actual exchanges. -/
def backwardLabel (edge : I → Site × Site) : List (ℝ × I) → Site → Site
  | [], v => v
  | (_, i) :: events, v =>
      backwardLabel edge events (Equiv.swap (edge i).1 (edge i).2 v)

theorem IsSweep.backwardTrace {C : ClockField} {edge : I → Site × Site}
    {c : TimeCutoff} {events : List (ℝ × I)} (h : IsSweep C edge c events) (v : Site) :
    C.BackwardTrace c v (backwardLabel edge events v) := by
  induction h generalizing v with
  | nil h => exact .stop (h v)
  | @cons c t i events h tail ih =>
    by_cases hx : v = (edge i).1
    · subst v
      simpa only [backwardLabel, Equiv.swap_apply_left] using
        ClockField.BackwardTrace.jump
          (show C.LatestRing c (edge i).1 t (edge i).2 from
            ⟨h.rings, h.allowed, fun w r hr ha => h.latest _ w r hr ha⟩)
          (ih (edge i).2)
    · by_cases hy : v = (edge i).2
      · subst v
        simpa only [backwardLabel, Equiv.swap_apply_right] using
          ClockField.BackwardTrace.jump
            (show C.LatestRing c (edge i).2 t (edge i).1 from
              ⟨h.rings.symm, h.allowed, fun w r hr ha => h.latest _ w r hr ha⟩)
            (ih (edge i).1)
      · have hagree : C.CutoffsAgree v (TimeCutoff.before t) c := by
          intro w r hr
          constructor
          · intro hrt
            exact TimeCutoff.allows_of_lt h.allowed hrt
          · intro hrAllowed
            have hle := h.latest v w r hr hrAllowed
            apply lt_of_le_of_ne hle
            intro hrt
            have hp := h.unique_pair v w (hrt ▸ hr)
            have hv : v ∈ s((edge i).1, (edge i).2) := hp ▸ Sym2.mem_mk_left v w
            exact (Sym2.mem_iff.mp hv).elim hx hy
        simpa only [backwardLabel, Equiv.swap_apply_of_ne_of_ne hx hy] using
          (ih v).changeCutoff hagree

theorem IsSweep.ancestor_eq {C : ClockField} {edge : I → Site × Site}
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    {c : TimeCutoff} {events : List (ℝ × I)} (h : IsSweep C edge c events) (v : Site) :
    C.ancestor hf c v = backwardLabel edge events v :=
  ClockField.ancestor_eq_of_trace ht hf (h.backwardTrace v)

theorem IsSweep.same_pair_at_cutoff {C : ClockField} {edge : I → Site × Site}
    {t : ℝ} {events : List (ℝ × I)}
    (h : IsSweep C edge (TimeCutoff.closedAt t) events)
    {u v x y : Site} (huv : C.Rings u v t) (hxy : C.Rings x y t) :
    s(u, v) = s(x, y) := by
  cases h with
  | nil h => exact (h u v t huv (le_refl t)).elim
  | @cons c r i events h tail =>
    have hrt : r = t := le_antisymm h.allowed (h.latest u v t huv (le_refl t))
    subst r
    exact (h.unique_pair u v huv).trans (h.unique_pair x y hxy).symm

/-- Chronological color evolution. The latest exchange acts last. -/
def runColors {V : Type*} [DecidableEq V] (edge : I → V × V) :
    List (ℝ × I) → (V → Bool) → (V → Bool)
  | [], η => η
  | (_, i) :: events, η =>
      (runColors edge events η) ∘ Equiv.swap (edge i).1 (edge i).2

theorem runColors_apply (edge : I → Site × Site) (events : List (ℝ × I))
    (η : Configuration) (v : Site) :
    runColors edge events η v = η (backwardLabel edge events v) := by
  induction events generalizing v with
  | nil => rfl
  | cons event events ih => exact ih _

theorem IsSweep.colorAt_eq_runColors {C : ClockField} {edge : I → Site × Site}
    (ht : C.NoIncidentTies) (hf : C.HasFiniteBackwardTraces)
    {c : TimeCutoff} {events : List (ℝ × I)} (h : IsSweep C edge c events)
    (η : Configuration) : C.colorAt hf η c = runColors edge events η := by
  funext v
  rw [runColors_apply]
  exact congrArg η (h.ancestor_eq ht hf v)

/-- Global ties are a standard null event for finitely many independent
Poisson clocks. This definition itself asserts no probabilistic result. -/
def NoGlobalTies (C : ClockField) : Prop :=
  ∀ u v x y t, C.Rings u v t → C.Rings x y t → s(u, v) = s(x, y)

theorem sweep_exists_of_finite_time_support (C : ClockField) (edge : I → Site × Site)
    (hties : NoGlobalTies C)
    (hcover : ∀ u v t, C.Rings u v t → ∃ i, s(u, v) = s((edge i).1, (edge i).2))
    (T : Finset ℝ) (c : TimeCutoff)
    (hT : ∀ u v t, C.Rings u v t → c.Allows t → t ∈ T) :
    ∃ events, IsSweep C edge c events := by
  classical
  induction T using Finset.strongInductionOn generalizing c with
  | _ T ih =>
    by_cases hstop : ∀ v, C.NoEligibleRing c v
    · exact ⟨[], .nil hstop⟩
    · have hex : ∃ u v t, C.Rings u v t ∧ c.Allows t := by
        simpa only [ClockField.NoEligibleRing, not_forall, not_not, exists_prop] using hstop
      let E := T.filter (fun t => ∃ u v, C.Rings u v t ∧ c.Allows t)
      have hE : E.Nonempty := by
        obtain ⟨u, v, t, hr, ha⟩ := hex
        exact ⟨t, Finset.mem_filter.mpr ⟨hT u v t hr ha, u, v, hr, ha⟩⟩
      let t := E.max' hE
      obtain ⟨htT, u, v, hring, hallow⟩ := Finset.mem_filter.mp (E.max'_mem hE)
      obtain ⟨i, hi⟩ := hcover u v t hring
      have hselected : C.Rings (edge i).1 (edge i).2 t := by
        unfold ClockField.Rings at *
        rwa [← hi]
      have hl : LatestGlobalMark C edge c t i := by
        refine ⟨hselected, hallow, ?_, ?_⟩
        · intro x y r hr ha
          exact E.le_max' r (Finset.mem_filter.mpr ⟨hT x y r hr ha, x, y, hr, ha⟩)
        · intro x y hr
          exact hties x y _ _ t hr hselected
      obtain ⟨events, hevents⟩ := ih (T.erase t) (Finset.erase_ssubset htT)
        (TimeCutoff.before t) (fun x y r hr ha =>
          Finset.mem_erase.mpr ⟨ne_of_lt ha,
            hT x y r hr (TimeCutoff.allows_of_lt hallow ha)⟩)
      exact ⟨(t, i) :: events, .cons hl hevents⟩

section FiniteCube

variable (V : Finset Site)

def restrictColor (η : Configuration) : V → Bool := fun v => η v

def extendColor (η : V → Bool) : Configuration :=
  fun v => if hv : v ∈ V then η ⟨v, hv⟩ else false

@[simp]
theorem restrict_extendColor (η : V → Bool) : restrictColor V (extendColor V η) = η := by
  funext v
  simp [restrictColor, extendColor]

theorem restrictColor_eq_iff (η : Configuration) (ξ : V → Bool) :
    restrictColor V η = ξ ↔ ∀ v ∈ V, η v = extendColor V ξ v := by
  constructor
  · intro h v hv
    have := congrFun h ⟨v, hv⟩
    simpa [restrictColor, extendColor, hv] using this
  · intro h
    funext v
    simpa [restrictColor, extendColor, v.property] using h v v.property

def siteEdges (edge : I → V × V) : I → Site × Site :=
  fun i => ((edge i).1, (edge i).2)

def edgePair (edge : I → V × V) (i : I) : Sym2 Site :=
  s(((edge i).1 : Site), ((edge i).2 : Site))

def retainedEdges [Fintype I] (edge : I → V × V) : Finset (Sym2 Site) :=
  Finset.univ.image (edgePair V edge)

theorem restrictColor_swap (x y : V) (η : Configuration) :
    restrictColor V (η ∘ Equiv.swap (x : Site) (y : Site)) =
      restrictColor V η ∘ Equiv.swap x y := by
  funext v
  by_cases hx : v = x
  · subst v
    simp [restrictColor]
  · by_cases hy : v = y
    · subst v
      simp [restrictColor]
    · have hx' : (v : Site) ≠ x := fun h => hx (Subtype.ext h)
      have hy' : (v : Site) ≠ y := fun h => hy (Subtype.ext h)
      simp [restrictColor, Equiv.swap_apply_of_ne_of_ne hx hy,
        Equiv.swap_apply_of_ne_of_ne hx' hy']

theorem restrictColor_runColors (edge : I → V × V) (events : List (ℝ × I))
    (η : Configuration) :
    restrictColor V (runColors (siteEdges V edge) events η) =
      runColors edge events (restrictColor V η) := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    simp only [runColors, siteEdges]
    rw [restrictColor_swap, ih]

/-- Exact joint finite-cube/clock-count law inherited from the infinite
initial iid field. This also proves its independence from the clocks. -/
theorem finiteCube_joint_counts {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {rate : Sym2 Site → ℝ} {initial : Ξ → Configuration}
    {clocks : Ξ → ClockField} (hlaw : IndependentPoissonInitial μ rate initial clocks)
    (η : V → Bool) (n : ℕ) (T : ClockTests n) (count : Fin n → ℕ) :
    μ {ω | restrictColor V (initial ω) = η ∧
      ∀ i, (clocks ω).markCount (T.edge i) (T.start i) (T.finish i) = count i} =
      (1 / 2 : ℝ≥0∞) ^ V.card *
        ∏ i, poissonMass (rate (T.edge i) * (T.finish i - T.start i)) (count i) := by
  simp_rw [restrictColor_eq_iff]
  exact hlaw V (extendColor V η) n T count

theorem restricted_markCount_of_mem (C : ClockField) (F : Finset (Sym2 Site))
    {e : Sym2 Site} (he : e ∈ F) (a b : ℝ) :
    (C.restrictEdges F).markCount e a b = C.markCount e a b := by
  simp [ClockField.markCount, ClockField.restrictEdges, he]

theorem restricted_finite_counts (C : ClockField) (hc : C.FiniteEdgeCounts)
    (F : Finset (Sym2 Site)) : (C.restrictEdges F).FiniteEdgeCounts := by
  intro e T
  by_cases he : e ∈ F
  · simpa [ClockField.restrictEdges, he] using hc e T
  · simp [ClockField.restrictEdges, he]

theorem sweep_exists_restricted [Fintype I] (C : ClockField)
    (hc : C.FiniteEdgeCounts) (edge : I → V × V)
    (hties : NoGlobalTies (C.restrictEdges (retainedEdges V edge))) (c : TimeCutoff) :
    ∃ events, IsSweep (C.restrictEdges (retainedEdges V edge)) (siteEdges V edge) c events := by
  classical
  let F := retainedEdges V edge
  let T := F.biUnion (fun e => (hc e c.time).toFinset)
  refine sweep_exists_of_finite_time_support _ _ hties ?cover T c ?time
  case cover =>
    intro u v t hr
    have he := ((ClockField.restrictEdges_rings C F u v t).mp hr).1
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
    exact ⟨i, hi.symm⟩
  case time =>
    intro u v t hr ha
    obtain ⟨he, hring⟩ := (ClockField.restrictEdges_rings C F u v t).mp hr
    exact Finset.mem_biUnion.mpr ⟨s(u, v), he,
      (hc s(u, v) c.time).mem_toFinset.mpr
        ⟨hring, hring.pos, TimeCutoff.allows_le_time ha⟩⟩

/-- The finite-cube version of the actual restricted graphical trajectory. -/
noncomputable def projectedTrajectory [Fintype I] (C : ClockField)
    (hc : C.FiniteEdgeCounts) (edge : I → V × V) (η : Configuration) (t : ℝ) : V → Bool :=
  restrictColor V ((C.restrictEdges (retainedEdges V edge)).trajectory
    (ClockField.restrictEdges_hasFiniteBackwardTraces hc (retainedEdges V edge)) η t)

theorem projectedTrajectory_eq_sweep [Fintype I] (C : ClockField)
    (hc : C.FiniteEdgeCounts) (ht : C.NoIncidentTies) (edge : I → V × V)
    (η : Configuration) (t : ℝ) {events : List (ℝ × I)}
    (hsweep : IsSweep (C.restrictEdges (retainedEdges V edge)) (siteEdges V edge)
      (TimeCutoff.closedAt t) events) :
    projectedTrajectory V C hc edge η t = runColors edge events (restrictColor V η) := by
  unfold projectedTrajectory ClockField.trajectory
  rw [hsweep.colorAt_eq_runColors (ht.restrictEdges _) _]
  exact restrictColor_runColors V edge events η

end FiniteCube

#print axioms IsSweep.colorAt_eq_runColors
#print axioms sweep_exists_of_finite_time_support
#print axioms restrictColor_runColors
#print axioms finiteCube_joint_counts

end ExceptionalTimes.FiniteClockBridge
