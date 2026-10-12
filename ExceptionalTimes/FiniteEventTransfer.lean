import ExceptionalTimes.TwoTimeMarginals

/-! The actual canonical and independent laws inherit an arm comparison
from finite crossing words, paying exactly four static approximation errors. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ExceptionalTimes.FiniteEventTransfer

noncomputable section

open EnvironmentVariance ProbeProduct PairSquareSewing DimerLaw ManyDimerLaw
open ActivePartitionLaw IndependentAnnulusInput IndependentJointAssociation TwoTimeMarginals

variable {B : Type*} [Fintype B]

theorem transfer (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀ v∈D,∃ b,slot b=v) (E F : Configuration→Prop)
    (hE : ∀ ω η,Set.EqOn ω η D → (E ω ↔ E η))
    (hF : ∀ ω η,Set.EqOn ω η D → (F ω ↔ F η))
    (t u : ℝ) (ht : 0≤t) (hu : 0≤u) (ε δ : ℝ)
    (hstatic : probability (fairSites D) (fun ω => ¬(E (complete ω) ↔ F (complete ω)))≤ε)
    (hword : |manyProbability (fun _ => refreshProbability t) (fun ω => F (pairDecode slot ω))-
      jointProbability D u F|≤δ) :
    |manyProbability (fun _ => refreshProbability t) (fun ω => E (pairDecode slot ω))-
      jointProbability D u E|≤4*ε+δ := by
  let ν := manyLaw (fun _ : B => refreshProbability t)
    (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)
  let μ := jointLaw (fun _ : D => refreshProbability u)
    (fun _ => refreshProbability_nonneg hu) (fun _ => refreshProbability_le_one u)
  let G : Configuration→Prop := fun ω => ¬(E ω ↔ F ω)
  have hG : ∀ ω η, (∀ v∈D,ω v=η v) → (G ω ↔ G η) := by
    intro ω η hh
    have hh' : Set.EqOn ω η D := fun _ hv => hh _ hv
    exact not_congr (iff_congr (hE _ _ hh') (hF _ _ hh'))
  have hs : FiniteHaar.average (fun ω => indicator (G (pairDecode slot ω)))≤ε := by
    rw [FiniteSiteLaw.average_pairDecode_fairSites slot D hcover G hG]
    exact hstatic
  have hν₀ : probability ν (fun ω => G (pairDecode slot ω.1))≤ε := by
    change ν.expect (fun ω => indicator (G (pairDecode slot ω.1)))≤ε
    exact (canonical_left (fun _ : B => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)
      (fun ω => indicator (G (pairDecode slot ω)))).le.trans hs
  have hν₁ : probability ν (fun ω => G (pairDecode slot ω.2))≤ε := by
    change ν.expect (fun ω => indicator (G (pairDecode slot ω.2)))≤ε
    exact (canonical_right (fun _ : B => refreshProbability t)
      (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)
      (fun ω => indicator (G (pairDecode slot ω)))).le.trans hs
  have hμ₀ : probability μ (fun ω => G (complete (fun v => (ω v).1)))≤ε := by
    change μ.expect (fun ω => indicator (G (complete (fun v => (ω v).1))))≤ε
    exact (independent_left (fun _ : D => refreshProbability u)
      (fun _ => refreshProbability_nonneg hu) (fun _ => refreshProbability_le_one u)
      (fun ω => indicator (G (complete ω)))).le.trans hstatic
  have hμ₁ : probability μ (fun ω => G (complete (fun v => (ω v).2)))≤ε := by
    change μ.expect (fun ω => indicator (G (complete (fun v => (ω v).2))))≤ε
    exact (independent_right (fun _ : D => refreshProbability u)
      (fun _ => refreshProbability_nonneg hu) (fun _ => refreshProbability_le_one u)
      (fun ω => indicator (G (complete ω)))).le.trans hstatic
  rw [manyProbability_eq_joint _ (fun _ => refreshProbability_nonneg ht)
    (fun _ => refreshProbability_le_one t),jointProbability_eq_law D u hu] at hword ⊢
  exact PairedEventTransfer.paired_event_transfer ν μ
    (fun ω => E (pairDecode slot ω.1)) (fun ω => E (pairDecode slot ω.2))
    (fun ω => F (pairDecode slot ω.1)) (fun ω => F (pairDecode slot ω.2))
    (fun ω => E (complete (fun v => (ω v).1)))
    (fun ω => E (complete (fun v => (ω v).2)))
    (fun ω => F (complete (fun v => (ω v).1)))
    (fun ω => F (complete (fun v => (ω v).2))) hν₀ hν₁ hμ₀ hμ₁ hword

#print axioms transfer

end
end ExceptionalTimes.FiniteEventTransfer
