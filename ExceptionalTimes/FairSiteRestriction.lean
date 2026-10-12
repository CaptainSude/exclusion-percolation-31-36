import ExceptionalTimes.FiniteSiteLaw

/-! Exact invariance of the finite iid fair-site probability of a local
event under enlargement of the sampled support. -/

open scoped Classical

namespace ExceptionalTimes.FiniteSiteLaw

noncomputable section

open FiniteHaar EnvironmentVariance ProbeProduct PairSquareSewing

theorem completeColors_eq_extend (D : Finset Site) (x : D → Bool) :
    completeColors D x =
      Function.extend (Function.Embedding.subtype (fun v => v ∈ D)) x (fun _ => false) := by
  funext v
  by_cases hv : v ∈ D
  · change completeColors D x (⟨v,hv⟩ : D).val = _
    rw [completeColors_agrees]
    exact ((Function.Embedding.subtype (fun v => v ∈ D)).injective.extend_apply x
      (fun _ => false) ⟨v,hv⟩).symm
  · have he : ¬ ∃ b : D, (Function.Embedding.subtype (fun v => v ∈ D)) b = v := by
      rintro ⟨b,hb⟩
      exact hv (hb ▸ b.property)
    rw [Function.extend_apply' _ _ _ he]
    simp [completeColors,hv]

theorem fairSites_restrict (S D : Finset Site) (hSD : S ⊆ D)
    (F : Configuration → ℝ)
    (hlocal : ∀ ω η, (∀ v ∈ S, ω v = η v) → F ω = F η) :
    (fairSites D).expect (fun x => F (completeColors D x)) =
      (fairSites S).expect (fun x => F (completeColors S x)) := by
  rw [fairSites_expect_eq_average]
  simp_rw [completeColors_eq_extend D]
  exact average_site_embedding (Function.Embedding.subtype (fun v => v ∈ D)) S
    (fun v hv => ⟨⟨v,hSD hv⟩,rfl⟩) F hlocal

theorem fairSites_probability_restrict (S D : Finset Site) (hSD : S ⊆ D)
    (E : Configuration → Prop)
    (hlocal : ∀ ω η, (∀ v ∈ S, ω v = η v) → (E ω ↔ E η)) :
    probability (fairSites D) (fun x => E (completeColors D x)) =
      probability (fairSites S) (fun x => E (completeColors S x)) :=
  fairSites_restrict S D hSD (fun ω => indicator (E ω))
    (fun ω η he => congrArg indicator (propext (hlocal ω η he)))

#print axioms fairSites_probability_restrict

end

end ExceptionalTimes.FiniteSiteLaw
