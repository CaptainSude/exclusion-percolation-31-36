import ExceptionalTimes.StochasticModel

/-!
# Restricting actual clocks to finitely many unordered edges

A finite backward trace survives every restriction retaining its finitely many
used edges. This is proved by induction on the actual latest-mark trace. Finite
per-edge mark counts imply finite traces for every finite-edge restriction.
Consequently any increasing exhaustive edge sequence eventually gives exactly
the same ancestors and colors on a finite set at a fixed cutoff.

This deterministic module does not assert convergence of correlations or energy
integrals, or construct a Poisson realization.
-/

namespace ExceptionalTimes

namespace TimeCutoff

theorem allows_le_time {c : TimeCutoff} {s : ℝ} (h : c.Allows s) : s ≤ c.time := by
  cases hc : c.closed <;> simp [Allows, hc] at h
  · exact h.le
  · exact h

theorem allows_of_lt {c : TimeCutoff} {r s : ℝ} (hs : c.Allows s) (hrs : r < s) :
    c.Allows r := by
  cases hc : c.closed <;> simp [Allows, hc] at hs ⊢
  · exact hrs.trans hs
  · exact hrs.le.trans hs

end TimeCutoff

namespace ClockField

/-- Delete every mark on an edge outside the finite retained set. -/
def restrictEdges (C : ClockField) (F : Finset (Sym2 Site)) : ClockField where
  marks e := if e ∈ F then C.marks e else ∅
  positive_time e t ht := by
    split_ifs at ht with he
    · exact C.positive_time e t ht
    · exact False.elim ht
  diagonal_empty v := by simp [C.diagonal_empty]

@[simp]
theorem restrictEdges_rings (C : ClockField) (F : Finset (Sym2 Site))
    (u v : Site) (t : ℝ) :
    (C.restrictEdges F).Rings u v t ↔ s(u, v) ∈ F ∧ C.Rings u v t := by
  simp [Rings, restrictEdges]

theorem NoIncidentTies.restrictEdges {C : ClockField} (ht : C.NoIncidentTies)
    (F : Finset (Sym2 Site)) : (C.restrictEdges F).NoIncidentTies := by
  intro u v w t huv huw
  exact ht u v w t ((restrictEdges_rings C F u v t).mp huv).2
    ((restrictEdges_rings C F u w t).mp huw).2

theorem NoEligibleRing.restrictEdges {C : ClockField} {c : TimeCutoff} {v : Site}
    (h : C.NoEligibleRing c v) (F : Finset (Sym2 Site)) :
    (C.restrictEdges F).NoEligibleRing c v := by
  intro w t ht
  exact h w t ((restrictEdges_rings C F v w t).mp ht).2

/-- Retaining the selected latest mark preserves its maximality: deleting
other clocks cannot introduce a later eligible mark. -/
theorem LatestRing.restrictEdges {C : ClockField} {c : TimeCutoff}
    {v w : Site} {t : ℝ} (h : C.LatestRing c v t w)
    (F : Finset (Sym2 Site)) (he : s(v, w) ∈ F) :
    (C.restrictEdges F).LatestRing c v t w := by
  refine ⟨(restrictEdges_rings C F v w t).mpr ⟨he, h.rings⟩, h.allowed, ?_⟩
  intro z r hr hallow
  exact h.latest z r ((restrictEdges_rings C F v z r).mp hr).2 hallow

/-- The footprint is built from exactly the successive jump edges. The proof
reuses every jump's time and partner and the original terminal stop. -/
theorem BackwardTrace.finite_edge_footprint {C : ClockField} {c : TimeCutoff}
    {v origin : Site} (p : C.BackwardTrace c v origin) :
    ∃ S : Finset (Sym2 Site), ∀ F : Finset (Sym2 Site), S ⊆ F →
      (C.restrictEdges F).BackwardTrace c v origin := by
  induction p with
  | stop h => exact ⟨∅, fun F _ => .stop (h.restrictEdges F)⟩
  | @jump c v t w origin h tail ih =>
    obtain ⟨S, hS⟩ := ih
    refine ⟨insert s(v, w) S, ?_⟩
    intro F hF
    exact .jump (h.restrictEdges F (hF (Finset.mem_insert_self _ _)))
      (hS F (fun e he => hF (Finset.mem_insert_of_mem he)))

/-- A finite global set of eligible times forces termination of the moving
label, even without a no-ties assumption. Each jump deletes its own time. -/
theorem trace_exists_of_finite_time_support (C : ClockField) (T : Finset ℝ)
    (c : TimeCutoff) (v : Site)
    (hT : ∀ u w t, C.Rings u w t → c.Allows t → t ∈ T) :
    ∃ origin, C.BackwardTrace c v origin := by
  classical
  induction T using Finset.strongInductionOn generalizing c v with
  | _ T ih =>
    by_cases hstop : C.NoEligibleRing c v
    · exact ⟨v, .stop hstop⟩
    · have hex : ∃ w t, C.Rings v w t ∧ c.Allows t := by
        simpa only [NoEligibleRing, not_forall, not_not, exists_prop] using hstop
      let E := T.filter (fun t => ∃ w, C.Rings v w t ∧ c.Allows t)
      have hE : E.Nonempty := by
        obtain ⟨w, t, ht, ha⟩ := hex
        exact ⟨t, Finset.mem_filter.mpr ⟨hT v w t ht ha, w, ht, ha⟩⟩
      let t := E.max' hE
      have htE : t ∈ E := E.max'_mem hE
      obtain ⟨htT, w, hring, hallow⟩ := Finset.mem_filter.mp htE
      have hlatest : C.LatestRing c v t w := by
        refine ⟨hring, hallow, ?_⟩
        intro z r hr har
        exact E.le_max' r (Finset.mem_filter.mpr ⟨hT v z r hr har, z, hr, har⟩)
      have htail : ∀ u z r, C.Rings u z r → (TimeCutoff.before t).Allows r →
          r ∈ T.erase t := by
        intro u z r hr hrt
        exact Finset.mem_erase.mpr ⟨ne_of_lt hrt,
          hT u z r hr (TimeCutoff.allows_of_lt hallow hrt)⟩
      obtain ⟨origin, p⟩ := ih (T.erase t) (Finset.erase_ssubset htT)
        (TimeCutoff.before t) w htail
      exact ⟨origin, .jump hlatest p⟩

/-- Finiteness is an actual set property, not merely a natural-valued count. -/
def FiniteEdgeCounts (C : ClockField) : Prop :=
  ∀ e T, (C.marks e ∩ Set.Ioc 0 T).Finite

/-- Restriction to finitely many edges plus finite counts on each edge yields
finite backward traces; no separate truncation-construction axiom is needed. -/
theorem restrictEdges_hasFiniteBackwardTraces {C : ClockField}
    (hc : C.FiniteEdgeCounts) (F : Finset (Sym2 Site)) :
    (C.restrictEdges F).HasFiniteBackwardTraces := by
  classical
  intro c v
  let T := F.biUnion (fun e => (hc e c.time).toFinset)
  apply trace_exists_of_finite_time_support (C.restrictEdges F) T c v
  intro u w t ht ha
  obtain ⟨he, hr⟩ := (restrictEdges_rings C F u w t).mp ht
  exact Finset.mem_biUnion.mpr ⟨s(u, w), he,
    (hc s(u, w) c.time).mem_toFinset.mpr ⟨hr, hr.pos, TimeCutoff.allows_le_time ha⟩⟩

theorem finite_sites_edge_footprint {C : ClockField} (hf : C.HasFiniteBackwardTraces)
    (c : TimeCutoff) (A : Finset Site) :
    ∃ S : Finset (Sym2 Site), ∀ F : Finset (Sym2 Site), S ⊆ F →
      ∀ v ∈ A, (C.restrictEdges F).BackwardTrace c v (C.ancestor hf c v) := by
  classical
  choose S hS using fun v => (C.ancestor_trace hf c v).finite_edge_footprint
  refine ⟨A.biUnion S, ?_⟩
  intro F hF v hv
  apply hS v F
  intro e he
  exact hF (Finset.mem_biUnion.mpr ⟨v, hv, he⟩)

/-- Uniform ancestor agreement on a finite set follows from the proven trace
footprints and endpoint uniqueness in the restricted clock field. -/
theorem finite_sites_ancestor_stability {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hc : C.FiniteEdgeCounts)
    (c : TimeCutoff) (A : Finset Site) :
    ∃ S : Finset (Sym2 Site), ∀ F : Finset (Sym2 Site), S ⊆ F → ∀ v ∈ A,
      (C.restrictEdges F).ancestor (restrictEdges_hasFiniteBackwardTraces hc F) c v =
        C.ancestor hf c v := by
  obtain ⟨S, hS⟩ := finite_sites_edge_footprint hf c A
  refine ⟨S, ?_⟩
  intro F hF v hv
  exact ancestor_eq_of_trace (ht.restrictEdges F)
    (restrictEdges_hasFiniteBackwardTraces hc F) (hS F hF v hv)

theorem finite_subset_exhaustion {E : Type*} [DecidableEq E]
    (F : ℕ → Finset E) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (S : Finset E) : ∃ N, ∀ n, N ≤ n → S ⊆ F n := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert e S he ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨M, hM⟩ := hex e
    refine ⟨max N M, ?_⟩
    intro n hn x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmono ((le_max_right N M).trans hn) hM
    · exact hN n ((le_max_left N M).trans hn) hx

theorem eventually_ancestors_eq {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hc : C.FiniteEdgeCounts)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (c : TimeCutoff) (A : Finset Site) :
    ∃ N, ∀ n, N ≤ n → ∀ v ∈ A,
      (C.restrictEdges (F n)).ancestor (restrictEdges_hasFiniteBackwardTraces hc (F n)) c v =
        C.ancestor hf c v := by
  obtain ⟨S, hS⟩ := finite_sites_ancestor_stability ht hf hc c A
  obtain ⟨N, hN⟩ := finite_subset_exhaustion F hmono hex S
  exact ⟨N, fun n hn => hS (F n) (hN n hn)⟩

/-- The eventual index depends on the clocks and finite observation set, and
works simultaneously for every initial coloring. -/
theorem eventually_colors_eq {C : ClockField} (ht : C.NoIncidentTies)
    (hf : C.HasFiniteBackwardTraces) (hc : C.FiniteEdgeCounts)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (c : TimeCutoff) (A : Finset Site) :
    ∃ N, ∀ n, N ≤ n → ∀ ω : Configuration, ∀ v ∈ A,
      (C.restrictEdges (F n)).colorAt (restrictEdges_hasFiniteBackwardTraces hc (F n)) ω c v =
        C.colorAt hf ω c v := by
  obtain ⟨N, hN⟩ := eventually_ancestors_eq ht hf hc F hmono hex c A
  refine ⟨N, ?_⟩
  intro n hn ω v hv
  exact congrArg ω (hN n hn v hv)

end ClockField

namespace PoissonGraphicalRealization

theorem finiteEdgeCounts {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {rate : Sym2 Site → ℝ} (P : PoissonGraphicalRealization μ rate) (ω : Ω) :
    (P.clocks ω).FiniteEdgeCounts := fun e T => P.finite_counts ω e 0 T

/-- Literal pathwise convergence for a supplied graphical realization. No
stationarity, generator identity, or Poisson existence result is inserted. -/
theorem eventually_truncated_trajectory_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (ω : Ω) (t : ℝ) (A : Finset Site) :
    ∃ N, ∀ n, N ≤ n → ∀ v ∈ A,
      ((P.clocks ω).restrictEdges (F n)).trajectory
        (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts ω) (F n))
        (P.initial ω) t v = P.trajectories ω t v := by
  obtain ⟨N, hN⟩ := ClockField.eventually_colors_eq (P.no_incident_ties ω)
    (P.finite_backward_traces ω) (P.finiteEdgeCounts ω) F hmono hex
    (TimeCutoff.closedAt t) A
  exact ⟨N, fun n hn => hN n hn (P.initial ω)⟩

/-- In particular, every two-time test depending on finitely many terminal
sites is eventually identical pathwise. Its dependence on the initial
configuration is unrestricted because that configuration is unchanged. -/
theorem eventually_truncated_two_time_test_eq {Ω Y : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (F : ℕ → Finset (Sym2 Site)) (hmono : Monotone F) (hex : ∀ e, ∃ n, e ∈ F n)
    (t : ℝ) (A : Finset Site) (test : Configuration → Configuration → Y)
    (hlocal : ∀ initial η ξ, (∀ v ∈ A, η v = ξ v) → test initial η = test initial ξ)
    (ω : Ω) :
    ∃ N, ∀ n, N ≤ n →
      test (P.initial ω)
        (((P.clocks ω).restrictEdges (F n)).trajectory
          (ClockField.restrictEdges_hasFiniteBackwardTraces (P.finiteEdgeCounts ω) (F n))
          (P.initial ω) t) = test (P.initial ω) (P.trajectories ω t) := by
  obtain ⟨N, hN⟩ := P.eventually_truncated_trajectory_eq F hmono hex ω t A
  exact ⟨N, fun n hn => hlocal _ _ _ (hN n hn)⟩

end PoissonGraphicalRealization
end ExceptionalTimes

#print axioms ExceptionalTimes.ClockField.BackwardTrace.finite_edge_footprint
#print axioms ExceptionalTimes.ClockField.restrictEdges_hasFiniteBackwardTraces
#print axioms ExceptionalTimes.ClockField.eventually_ancestors_eq
#print axioms ExceptionalTimes.PoissonGraphicalRealization.eventually_truncated_trajectory_eq
#print axioms ExceptionalTimes.PoissonGraphicalRealization.eventually_truncated_two_time_test_eq
