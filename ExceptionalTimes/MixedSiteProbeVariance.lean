import ExceptionalTimes.MixedSiteVariance
import ExceptionalTimes.MixedProbeProduct

/-! Actual mixed Site-cell variance followed by a product of necessary
independent probes. Remote factors stay mixed; only the chosen local
factors need be replaced by numerical or fully canonical upper bounds. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedSiteProbeVariance

noncomputable section

open DimerLaw EnvironmentVariance FiniteHaar
open MixedCanonicalLaw MixedSiteVariance MixedProbeProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I O : Type*} [Fintype I] [Fintype O]
variable {J : I → Type*} [∀ i, Fintype (J i)]
variable {A : I → Type*} [∀ i, Fintype (A i)]
variable {K L : ∀ i, A i → Type*} [∀ i a, Fintype (K i a)] [∀ i a, Fintype (L i a)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

theorem mixed_site_variance_of_probes
    (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (p : Sigma J → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩))))
    (e : ∀ i, Sigma (K i) ≃ Sigma J) (f : ∀ i, Sigma (L i) ≃ O)
    (T : ∀ i a, ((K i a → Color) × (L i a → Color)) → Prop)
    (hnecessary : ∀ i x, CellInterpolation.CellPivotal F (cellSites slot i) (decode slot x) →
      ∀ a, T i a (fun j => x.1 (e i ⟨a,j⟩),fun j => x.2 (f i ⟨a,j⟩))) :
    mixedProbability p (fun x => F (decode slot x) = true) -
      (average (smooth (fun x => indicator (F (decode slot x) = true)))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, ∏ a, mixedProbability (fun j => p (e i ⟨a,j⟩)) (T i a) := by
  apply (mixed_site_variance slot p hp0 hp1 F hES).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  rw [mixedProbability_relabel (e i) (f i)]
  apply mixed_necessary_groups _ (fun s => hp0 (e i s)) (fun s => hp1 (e i s)) _ (T i)
  intro x hx
  have H := hnecessary i
    (fun b => x.1 ((e i).symm b),fun o => x.2 ((f i).symm o)) hx
  simpa only [Equiv.symm_apply_apply] using H

theorem mixed_site_variance_of_probe_bounds
    (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (p : Sigma J → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩))))
    (e : ∀ i, Sigma (K i) ≃ Sigma J) (f : ∀ i, Sigma (L i) ≃ O)
    (T : ∀ i a, ((K i a → Color) × (L i a → Color)) → Prop)
    (hnecessary : ∀ i x, CellInterpolation.CellPivotal F (cellSites slot i) (decode slot x) →
      ∀ a, T i a (fun j => x.1 (e i ⟨a,j⟩),fun j => x.2 (f i ⟨a,j⟩)))
    (bound : ∀ i, A i → ℝ)
    (hbound : ∀ i a, mixedProbability (fun j => p (e i ⟨a,j⟩)) (T i a) ≤ bound i a) :
    mixedProbability p (fun x => F (decode slot x) = true) -
      (average (smooth (fun x => indicator (F (decode slot x) = true)))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, ∏ a, bound i a := by
  apply (mixed_site_variance_of_probes slot p hp0 hp1 F hES e f T hnecessary).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.prod_le_prod₀
    (fun a _ => mixedProbability_nonneg _
      (fun j => hp0 (e i ⟨a,j⟩)) (fun j => hp1 (e i ⟨a,j⟩)) (T i a))
    (fun a _ => hbound i a)

#print axioms mixed_site_variance_of_probes
#print axioms mixed_site_variance_of_probe_bounds

end

end ExceptionalTimes.MixedSiteProbeVariance
