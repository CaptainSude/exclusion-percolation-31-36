import ExceptionalTimes.Model

/-!
The deterministic bridge from closures of finite connection-time sets to
percolation after closing each site's black-time set. The stochastic statement
that closing site times preserves infinite connection is NOT asserted here;
that is the separately published GV Lemma 2.2 input.
-/

namespace ExceptionalTimes.TimeClosure

set_option autoImplicit false
open Set Filter
open scoped Topology

noncomputable def closedColors (X : Trajectory) (t : ℝ) : Configuration := by
  classical
  exact fun v => decide (t ∈ closure {s | 0 ≤ s ∧ X s v = true})

theorem closedColors_eq_true (X : Trajectory) (t : ℝ) (v : Site) :
    closedColors X t v = true ↔ t ∈ closure {s | 0 ≤ s ∧ X s v = true} := by
  classical
  simp [closedColors]

theorem eventually_black_implies_closed (X : Trajectory) (t : ℝ) (v : Site) :
    ∀ᶠ s in 𝓝 t, 0 ≤ s → X s v = true → closedColors X t v = true := by
  by_cases h : t ∈ closure {s | 0 ≤ s ∧ X s v = true}
  · exact Eventually.of_forall (fun _ _ _ => (closedColors_eq_true X t v).mpr h)
  · have hn : ∀ᶠ s in 𝓝 t, ¬ (0 ≤ s ∧ X s v = true) := by
      simpa only [mem_closure_iff_frequently, mem_ofPred_eq, not_frequently] using h
    exact hn.mono (fun _ hs hs0 hblack => (hs ⟨hs0, hblack⟩).elim)

/-- Increasing finite-color events remain true at any limit of their occurrence
times after each site's black-time set is closed. No path continuity is needed. -/
theorem increasing_cylinder_of_mem_closure (X : Trajectory) (A : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ v ∈ A, η v = ξ v) → (E η ↔ E ξ))
    (hmono : ∀ η ξ, (∀ v, η v = true → ξ v = true) → E η → E ξ)
    {t : ℝ} (ht : t ∈ closure {s | 0 ≤ s ∧ E (X s)}) :
    E (closedColors X t) := by
  classical
  have hev : ∀ᶠ s in 𝓝 t,
      ∀ v ∈ A, 0 ≤ s → X s v = true → closedColors X t v = true :=
    (eventually_all_finset A).mpr (fun v _ => eventually_black_implies_closed X t v)
  obtain ⟨s, hs, hvs⟩ := ((mem_closure_iff_frequently.mp ht).and_eventually hev).exists
  let ξ : Configuration := fun v => if v ∈ A then X s v else false
  have hEξ : E ξ := (hlocal (X s) ξ (fun v hv => by simp [ξ, hv])).mp hs.2
  apply hmono ξ (closedColors X t) _ hEξ
  intro v hv
  by_cases hvA : v ∈ A
  · exact hvs v hvA hs.1 (by simpa [ξ, hvA] using hv)
  · simp [ξ, hvA] at hv

theorem latticeBox_mono : Monotone latticeBox := by
  intro n m hnm v hv
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at *
  constructor <;> constructor <;> omega

theorem oneArm_radius_mono {η : Configuration} {v : Site} {n m : ℕ}
    (hnm : n ≤ m) (h : OneArm η v m) : OneArm η v n := by
  obtain ⟨w, hw, hwm⟩ := h
  exact ⟨w, hw, fun hwn => hwm (latticeBox_mono hnm hwn)⟩

theorem oneArm_colors_mono {η ξ : Configuration} (v : Site) (R : ℕ)
    (h : ∀ w, η w = true → ξ w = true) : OneArm η v R → OneArm ξ v R := by
  rintro ⟨w, hw, hR⟩
  exact ⟨w, blackCluster_mono h v hw, hR⟩

theorem oneArm_closedColors_of_mem_closure (X : Trajectory) (v : Site) (R : ℕ)
    (hv : v ∈ latticeBox R) {t : ℝ}
    (ht : t ∈ closure {s | 0 ≤ s ∧ OneArm (X s) v R}) :
    OneArm (closedColors X t) v R := by
  apply increasing_cylinder_of_mem_closure X (latticeBox (R + 1))
    (fun η => OneArm η v R) _ _ ht
  · intro η ξ heq
    exact oneArm_congr_of_eqOn_box hv (fun w hw => heq w hw)
  · intro η ξ h
    exact oneArm_colors_mono v R h

/-- The intersection of finite-radius closures gives an actual infinite black
cluster in the site-closed configuration, at the same specified vertex. -/
theorem infinite_closedColors_of_all_radius_closures (X : Trajectory) (v : Site)
    {t : ℝ} (ht : ∀ R : ℕ, t ∈ closure {s | 0 ≤ s ∧ OneArm (X s) v R}) :
    (BlackCluster (closedColors X t) v).Infinite := by
  apply (infinite_blackCluster_iff_oneArm _ _).mpr
  intro R
  let S := max R (latticeRadius v)
  have hvS : v ∈ latticeBox S := mem_latticeBox_of_radius_le (le_max_right _ _)
  exact oneArm_radius_mono (le_max_left _ _)
    (oneArm_closedColors_of_mem_closure X v S hvS (ht S))

/-- Explicit deterministic form of the path property furnished almost surely
by GV Lemma 2.2. No assertion that an arbitrary trajectory satisfies it. -/
def SiteClosurePreservesInfiniteAt (X : Trajectory) (v : Site) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (BlackCluster (closedColors X t) v).Infinite →
    (BlackCluster (X t) v).Infinite

/-- The weaker property actually needed by the exceptional-time dimension
argument. The surviving infinite cluster may have a different base vertex. -/
def SiteClosurePreservesPercolationAt (X : Trajectory) (v : Site) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (BlackCluster (closedColors X t) v).Infinite →
    HasInfiniteBlackCluster (X t)

theorem SiteClosurePreservesInfiniteAt.percolation {X : Trajectory} {v : Site}
    (h : SiteClosurePreservesInfiniteAt X v) : SiteClosurePreservesPercolationAt X v :=
  fun t ht hinf => ⟨v,h t ht hinf⟩

theorem exceptional_of_all_radius_closures_of_percolation (X : Trajectory) (v : Site)
    (hpreserve : SiteClosurePreservesPercolationAt X v) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ R : ℕ, t ∈ closure {s | 0 ≤ s ∧ OneArm (X s) v R}) :
    t ∈ exceptionalTimes X :=
  ⟨ht0,hpreserve t ht0 (infinite_closedColors_of_all_radius_closures X v ht)⟩

theorem exceptional_of_all_radius_closures (X : Trajectory) (v : Site)
    (hpreserve : SiteClosurePreservesInfiniteAt X v) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ R : ℕ, t ∈ closure {s | 0 ≤ s ∧ OneArm (X s) v R}) :
    t ∈ exceptionalTimes X :=
  ⟨ht0, v, hpreserve t ht0 (infinite_closedColors_of_all_radius_closures X v ht)⟩

end ExceptionalTimes.TimeClosure

#print axioms ExceptionalTimes.TimeClosure.increasing_cylinder_of_mem_closure
#print axioms ExceptionalTimes.TimeClosure.infinite_closedColors_of_all_radius_closures
#print axioms ExceptionalTimes.TimeClosure.exceptional_of_all_radius_closures
