import ExceptionalTimes.Model
import ExceptionalTimes.RateKernel

/-!
# Deterministic clock construction of color transport

This is the deterministic backward-tracing part of Garban--Vanneuville,
arXiv:1605.04766v3, Appendix A. Each unordered pair has ONE set of clock
marks. The initial time cutoff is closed; after crossing a mark it becomes
strict, so that the same exchange cannot immediately be crossed again.

No Poisson law, independence, nonexplosion probability, stationarity,
permutation property, or Hausdorff-dimension conclusion is postulated.
Existence of finite traces and absence of incident ties are explicit
deterministic hypotheses, to be discharged by a separately identified
probabilistic construction theorem.
-/

namespace ExceptionalTimes

/-- The rate on an unordered pair. The two orientations are not separate
clock indices. Diagonal indices have rate zero. -/
def RateKernel.unorderedPairRate (k : RateKernel) : Sym2 Site → ℝ :=
  Sym2.lift ⟨k.pairRate, k.pairRate_symmetric⟩

@[simp]
theorem RateKernel.unorderedPairRate_mk (k : RateKernel) (u v : Site) :
    k.unorderedPairRate s(u, v) = k.pairRate u v := rfl

/-- A realized family of clock marks. Self-pair clocks are empty and all
marks occur strictly after the initial time zero. -/
structure ClockField where
  marks : Sym2 Site → Set ℝ
  positive_time : ∀ e t, t ∈ marks e → 0 < t
  diagonal_empty : ∀ v : Site, marks s(v, v) = ∅

namespace ClockField

def Rings (C : ClockField) (u v : Site) (t : ℝ) : Prop :=
  t ∈ C.marks s(u, v)

theorem Rings.symm {C : ClockField} {u v : Site} {t : ℝ}
    (h : C.Rings u v t) : C.Rings v u t := by
  unfold Rings at *
  rwa [Sym2.eq_swap]

theorem Rings.pos {C : ClockField} {u v : Site} {t : ℝ}
    (h : C.Rings u v t) : 0 < t := C.positive_time _ _ h

theorem Rings.ne {C : ClockField} {u v : Site} {t : ℝ}
    (h : C.Rings u v t) : u ≠ v := by
  intro huv
  subst v
  have : t ∈ C.marks s(u, u) := h
  rw [C.diagonal_empty] at this
  exact this

/-- Simultaneous disjoint exchanges cause no problem. The ambiguity to
exclude is two different partners at the same site and time. -/
def NoIncidentTies (C : ClockField) : Prop :=
  ∀ u v w t, C.Rings u v t → C.Rings u w t → v = w

/-- This local finiteness condition alone does not assert nonexplosion of
a moving label, which can visit different sites. -/
def LocallyFiniteIncident (C : ClockField) : Prop :=
  ∀ v : Site, ∀ T : ℝ,
    {p : ℝ × Site | C.Rings v p.2 p.1 ∧ p.1 ≤ T}.Finite

def UsesOnlyPositiveRates (C : ClockField) (k : RateKernel) : Prop :=
  ∀ u v t, C.Rings u v t → 0 < k.pairRate u v

end ClockField

structure TimeCutoff where
  time : ℝ
  closed : Bool

namespace TimeCutoff

def closedAt (t : ℝ) : TimeCutoff := ⟨t, true⟩
def before (t : ℝ) : TimeCutoff := ⟨t, false⟩

def Allows (c : TimeCutoff) (s : ℝ) : Prop :=
  if c.closed then s ≤ c.time else s < c.time

@[simp]
theorem allows_at (t s : ℝ) : (closedAt t).Allows s ↔ s ≤ t := Iff.rfl

@[simp]
theorem allows_before (t s : ℝ) : (before t).Allows s ↔ s < t := Iff.rfl

end TimeCutoff

namespace ClockField

def NoEligibleRing (C : ClockField) (c : TimeCutoff) (v : Site) : Prop :=
  ∀ w s, C.Rings v w s → ¬ c.Allows s

/-- Both occurrence and maximality are required. An arbitrary proposed
label path cannot satisfy this interface unless it follows the clocks. -/
structure LatestRing (C : ClockField) (c : TimeCutoff) (v : Site)
    (s : ℝ) (w : Site) : Prop where
  rings : C.Rings v w s
  allowed : c.Allows s
  latest : ∀ z r, C.Rings v z r → c.Allows r → r ≤ s

theorem LatestRing.unique {C : ClockField} (ht : C.NoIncidentTies)
    {c : TimeCutoff} {v w z : Site} {s r : ℝ}
    (h : C.LatestRing c v s w) (h' : C.LatestRing c v r z) :
    s = r ∧ w = z := by
  have hs : s = r := le_antisymm
    (h'.latest w s h.rings h.allowed) (h.latest z r h'.rings h'.allowed)
  refine ⟨hs, ?_⟩
  exact ht v w z s h.rings (hs ▸ h'.rings)

theorem NoEligibleRing.not_latest {C : ClockField} {c : TimeCutoff}
    {v w : Site} {s : ℝ} (h : C.NoEligibleRing c v)
    (hl : C.LatestRing c v s w) : False :=
  h w s hl.rings hl.allowed

/-- A finite backward label trace. It ends only when there are no earlier
incident marks, and each jump must cross the latest actual mark. -/
inductive BackwardTrace (C : ClockField) : TimeCutoff → Site → Site → Prop
  | stop {c v} (h : C.NoEligibleRing c v) : BackwardTrace C c v v
  | jump {c v s w origin} (h : C.LatestRing c v s w)
      (tail : BackwardTrace C (TimeCutoff.before s) w origin) :
      BackwardTrace C c v origin

theorem BackwardTrace.endpoint_unique {C : ClockField} (ht : C.NoIncidentTies)
    {c : TimeCutoff} {v a b : Site}
    (p : C.BackwardTrace c v a) (q : C.BackwardTrace c v b) : a = b := by
  induction p with
  | stop h =>
      cases q with
      | stop _ => rfl
      | jump hl _ => exact (h.not_latest hl).elim
  | jump hl tail ih =>
      cases q with
      | stop h => exact (h.not_latest hl).elim
      | jump hl' tail' =>
          obtain ⟨hs, hw⟩ := hl.unique ht hl'
          subst hs
          subst hw
          exact ih tail'

/-- Two cutoffs may be interchanged at a site when they admit exactly the
same actual incident clock marks. Later cutoffs in a trace are unchanged. -/
def CutoffsAgree (C : ClockField) (v : Site) (c d : TimeCutoff) : Prop :=
  ∀ w s, C.Rings v w s → (c.Allows s ↔ d.Allows s)

theorem BackwardTrace.changeCutoff {C : ClockField} {c d : TimeCutoff}
    {v a : Site} (p : C.BackwardTrace c v a) (heq : C.CutoffsAgree v c d) :
    C.BackwardTrace d v a := by
  cases p with
  | stop h =>
      apply BackwardTrace.stop
      intro w s hs hd
      exact h w s hs ((heq w s hs).mpr hd)
  | jump h tail =>
      apply BackwardTrace.jump (w := _) (s := _) _ tail
      exact ⟨h.rings, (heq _ _ h.rings).mp h.allowed,
        fun w s hs hd => h.latest w s hs ((heq w s hs).mpr hd)⟩

/-- Nonexplosion/existence is expressed by actual finite clock traces.
This proposition is not asserted here to hold with any probability. -/
def HasFiniteBackwardTraces (C : ClockField) : Prop :=
  ∀ c : TimeCutoff, ∀ v : Site, ∃ origin, C.BackwardTrace c v origin

noncomputable def ancestor (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (c : TimeCutoff) (v : Site) : Site :=
  Classical.choose (hf c v)

theorem ancestor_trace (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (c : TimeCutoff) (v : Site) : C.BackwardTrace c v (C.ancestor hf c v) :=
  Classical.choose_spec (hf c v)

theorem ancestor_eq_of_trace {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) {c : TimeCutoff} {v a : Site}
    (h : C.BackwardTrace c v a) : C.ancestor hf c v = a :=
  (C.ancestor_trace hf c v).endpoint_unique ht h

theorem ancestor_eq_of_noEligibleRing {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) {c : TimeCutoff} {v : Site}
    (h : C.NoEligibleRing c v) : C.ancestor hf c v = v :=
  ancestor_eq_of_trace ht hf (.stop h)

theorem ancestor_eq_at_latest {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) {c : TimeCutoff} {v w : Site} {s : ℝ}
    (h : C.LatestRing c v s w) :
    C.ancestor hf c v = C.ancestor hf (TimeCutoff.before s) w :=
  ancestor_eq_of_trace ht hf (.jump h (C.ancestor_trace hf _ _))

theorem ancestor_eq_of_cutoffsAgree {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) {c d : TimeCutoff} {v : Site}
    (heq : C.CutoffsAgree v c d) : C.ancestor hf c v = C.ancestor hf d v :=
  (ancestor_eq_of_trace ht hf ((C.ancestor_trace hf c v).changeCutoff heq)).symm

/-- The color is transported from the uniquely determined initial label. -/
noncomputable def colorAt (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (ω : Configuration) (c : TimeCutoff) (v : Site) : Bool :=
  ω (C.ancestor hf c v)

noncomputable def trajectory (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (ω : Configuration) : Trajectory :=
  fun t v => C.colorAt hf ω (TimeCutoff.closedAt t) v

/-- Configuration obtained with a strict time cutoff. Its identification
with the actual left limit of the trajectory is a separate regularity
statement; that limit theorem is not silently assumed by this definition. -/
noncomputable def leftConfiguration (C : ClockField) (hf : C.HasFiniteBackwardTraces)
    (ω : Configuration) (t : ℝ) : Configuration :=
  fun v => C.colorAt hf ω (TimeCutoff.before t) v

theorem trajectory_zero {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (ω : Configuration) : C.trajectory hf ω 0 = ω := by
  funext v
  change ω (C.ancestor hf (TimeCutoff.closedAt 0) v) = ω v
  congr 1
  apply ancestor_eq_of_noEligibleRing ht hf
  intro w s hs hallowed
  exact (not_le_of_gt hs.pos) hallowed

theorem latestRing_at_mark {C : ClockField} {v w : Site} {t : ℝ}
    (h : C.Rings v w t) : C.LatestRing (TimeCutoff.closedAt t) v t w :=
  ⟨h, le_refl t, fun _ _ _ hr => hr⟩

/-- At an actual clock mark, the right-time color at either endpoint is
the other endpoint's pre-mark color. -/
theorem trajectory_at_mark {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (ω : Configuration) {v w : Site} {t : ℝ}
    (h : C.Rings v w t) :
    C.trajectory hf ω t v = C.leftConfiguration hf ω t w := by
  change ω (C.ancestor hf (TimeCutoff.closedAt t) v) =
    ω (C.ancestor hf (TimeCutoff.before t) w)
  rw [ancestor_eq_at_latest ht hf (latestRing_at_mark h)]

theorem trajectory_swaps_at_mark {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (ω : Configuration) {v w : Site} {t : ℝ}
    (h : C.Rings v w t) :
    C.trajectory hf ω t v = C.leftConfiguration hf ω t w ∧
      C.trajectory hf ω t w = C.leftConfiguration hf ω t v :=
  ⟨trajectory_at_mark ht hf ω h, trajectory_at_mark ht hf ω h.symm⟩

theorem cutoffsAgree_of_no_mark_at {C : ClockField} {v : Site} {t : ℝ}
    (h : ∀ w, ¬ C.Rings v w t) :
    C.CutoffsAgree v (TimeCutoff.closedAt t) (TimeCutoff.before t) := by
  intro w s hs
  change s ≤ t ↔ s < t
  constructor
  · intro hst
    by_contra hn
    have heq : s = t := le_antisymm hst (le_of_not_gt hn)
    exact h w (heq ▸ hs)
  · exact le_of_lt

theorem trajectory_unchanged_without_mark {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (ω : Configuration) {v : Site} {t : ℝ}
    (h : ∀ w, ¬ C.Rings v w t) :
    C.trajectory hf ω t v = C.leftConfiguration hf ω t v := by
  change ω (C.ancestor hf (TimeCutoff.closedAt t) v) =
    ω (C.ancestor hf (TimeCutoff.before t) v)
  rw [ancestor_eq_of_cutoffsAgree ht hf (cutoffsAgree_of_no_mark_at h)]

end ClockField
end ExceptionalTimes

#print axioms ExceptionalTimes.ClockField.BackwardTrace.endpoint_unique
#print axioms ExceptionalTimes.ClockField.trajectory_zero
#print axioms ExceptionalTimes.ClockField.trajectory_swaps_at_mark
#print axioms ExceptionalTimes.ClockField.trajectory_unchanged_without_mark
