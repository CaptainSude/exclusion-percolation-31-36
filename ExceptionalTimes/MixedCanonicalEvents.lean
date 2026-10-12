import ExceptionalTimes.MixedCanonicalLaw

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedCanonicalLaw

open FiniteHaar CanonicalHarris DimerLaw ManyDimerLaw EnvironmentVariance

variable {A O : Type*} [Fintype A] [Fintype O]

theorem mixedProbability_nonneg (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (E : ((A → Color) × (O → Color)) → Prop) : 0 ≤ mixedProbability p E := by
  rw [mixedProbability,mixed_eq_environment_square p hp0 hp1]
  exact FiniteLaw.expect_nonneg _ (fun _ => sq_nonneg _)

theorem mixedProbability_mono (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (E H : ((A → Color) × (O → Color)) → Prop) (h : ∀ z, E z → H z) :
    mixedProbability p E ≤ mixedProbability p H := by
  apply mixed_mono p hp0 hp1 _ _ (fun z => indicator_nonneg (E z))
  intro z
  by_cases he : E z
  · simp [indicator,he,h z he]
  · simp [indicator,he]
    exact indicator_nonneg (H z)

theorem mixed_event_association (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (E H : Set ((A → Color) × (O → Color))) (hE : IsUpperSet E) (hH : IsUpperSet H) :
    mixedProbability p (fun z => z ∈ E) * mixedProbability p (fun z => z ∈ H) ≤
      mixedProbability p (fun z => z ∈ E ∩ H) := by
  change mixed p (eventIndicator E) * mixed p (eventIndicator H) ≤ mixed p (eventIndicator (E∩H))
  rw [eventIndicator_inter]
  exact mixed_association p hp0 hp1 _ _ (eventIndicator_nonneg E) (eventIndicator_nonneg H)
    (eventIndicator_monotone E hE) (eventIndicator_monotone H hH)

theorem average_smooth (F : ((A → Color) × (O → Color)) → ℝ) :
    average (smooth F) = average F := by
  simp only [smooth,average,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,
    Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem mixed_event_square_lower (p : A → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (E : ((A → Color) × (O → Color)) → Prop) :
    (average (fun z => indicator (E z)))^2 ≤ mixedProbability p E := by
  have h := mixed_square_lower p hp0 hp1 (fun z => indicator (E z))
  rwa [average_smooth] at h

theorem mixedProbability_active (p : A → ℝ) (E : (A → Color) → Prop) :
    mixedProbability (O := O) p (fun z => E z.1) = manyProbability p E := by
  rw [mixedProbability,mixed_eq_joint]
  simp only [smooth,average_const]
  rfl

theorem bothCanonical_mono (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (F H : ((A → Color) × (O → Color)) → ℝ)
    (hF : ∀ z, 0 ≤ F z) (hFH : ∀ z, F z ≤ H z) :
    bothCanonical p q hp0 hp1 hq0 hq1 F ≤ bothCanonical p q hp0 hp1 hq0 hq1 H := by
  apply FiniteLaw.expect_mono
  intro e
  apply FiniteLaw.expect_mono
  intro d
  have hn : 0 ≤ (manyReplica e).expect (fun a => (manyReplica d).expect (fun o => F (a,o))) :=
    FiniteLaw.expect_nonneg _ (fun a => FiniteLaw.expect_nonneg _ (fun o => hF (a,o)))
  have hl : (manyReplica e).expect (fun a => (manyReplica d).expect (fun o => F (a,o))) ≤
      (manyReplica e).expect (fun a => (manyReplica d).expect (fun o => H (a,o))) :=
    FiniteLaw.expect_mono _ (fun a => FiniteLaw.expect_mono _ (fun o => hFH (a,o)))
  nlinarith

theorem bothCanonical_active (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1) (E : (A → Color) → Prop) :
    bothCanonical p q hp0 hp1 hq0 hq1 (fun z => indicator (E z.1)) = manyProbability p E := by
  rw [← mixedProbability_active (O := O),mixedProbability,mixed_eq_environment_square p hp0 hp1]
  have hs : smooth (fun z : (A→Color)×(O→Color) => indicator (E z.1)) =
      fun a => indicator (E a) := by
    funext a
    change average (fun _ : O → Color => indicator (E a)) = indicator (E a)
    exact average_const (I := O → Color) (indicator (E a))
  rw [hs]
  simp only [bothCanonical,FiniteLaw.expect_const]

/-- Actual finite-law collar comparison. Only deterministic event
inclusions and a one-time bridge probability are supplied. All two-time
Harris, marginal, and independent-exterior identities are proved here. -/
theorem collar_comparison (p : A → ℝ) (q : O → ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (E B : Set ((A → Color) × (O → Color))) (M : Set (A → Color))
    (hM : IsUpperSet M) (hB : IsUpperSet B)
    (hnecessary : ∀ z ∈ E, z.1 ∈ M)
    (hglue : ∀ z, z.1 ∈ M → z ∈ B → z ∈ E)
    {b : ℝ} (hb : 0 < b) (hbridge : b ≤ average (eventIndicator B)) :
    bothCanonical p q hp0 hp1 hq0 hq1 (eventIndicator E) ≤
      mixedProbability p (fun z => z ∈ E) / b^2 := by
  have hn : bothCanonical p q hp0 hp1 hq0 hq1 (eventIndicator E) ≤ manyProbability p (fun a => a∈M) := by
    rw [← bothCanonical_active p q hp0 hp1 hq0 hq1]
    apply bothCanonical_mono p q hp0 hp1 hq0 hq1 _ _ (eventIndicator_nonneg E)
    intro z
    by_cases hz : z ∈ E
    · simp [eventIndicator,indicator,hz,hnecessary z hz]
    · simp [eventIndicator,indicator,hz]
      exact indicator_nonneg (z.1 ∈ M)
  have hM' : IsUpperSet {z : (A → Color) × (O → Color) | z.1 ∈ M} := by
    intro x y hxy hx
    exact hM hxy.1 hx
  have ha := mixed_event_association p hp0 hp1 {z | z.1∈M} B hM' hB
  have hg := mixedProbability_mono p hp0 hp1
    (fun z => z∈({z | z.1∈M}∩B : Set ((A → Color) × (O → Color)))) (fun z => z∈E)
    (fun z hz => hglue z hz.1 hz.2)
  have hbridge2 : b^2 ≤ mixedProbability p (fun z => z∈B) := by
    have hsq := mixed_event_square_lower p hp0 hp1 (fun z => z∈B)
    have hnB : 0 ≤ average (eventIndicator B) := average_nonneg (eventIndicator_nonneg B)
    change (average (eventIndicator B))^2 ≤ _ at hsq
    nlinarith
  have hmid : 0 ≤ mixedProbability p (fun z : (A→Color)×(O→Color) => z.1∈M) :=
    mixedProbability_nonneg p hp0 hp1 _
  have hprod := mul_le_mul_of_nonneg_left hbridge2 hmid
  have hbound := hprod.trans (ha.trans hg)
  rw [mixedProbability_active] at hbound
  exact hn.trans ((le_div_iff₀ (sq_pos_of_pos hb)).mpr hbound)

#print axioms collar_comparison

end ExceptionalTimes.MixedCanonicalLaw
