import ExceptionalTimes.MixedCanonicalVariance
import ExceptionalTimes.MixedCanonicalEvents
import ExceptionalTimes.ProbeProduct

/-! Exact factorization of the mixed two-time law over disjoint groups
of whole dimers. Both active and independently sampled exterior labels
are grouped, so a remote mixed factor is retained without replacing the
entire event by its fully canonical upper bound. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedProbeProduct

noncomputable section

open DimerLaw ManyDimerLaw FiniteHaar EnvironmentVariance
open GroupedDimerLaw MixedCanonicalLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Relabel

variable {A A' O O' : Type*} [Fintype A] [Fintype A'] [Fintype O] [Fintype O']

omit [Fintype A] [Fintype A'] in
theorem smooth_relabel (e : A' ≃ A) (f : O' ≃ O)
    (F : ((A → Color) × (O → Color)) → ℝ) (a : A' → Color) :
    smooth (fun x : (A' → Color) × (O' → Color) =>
      F (fun b => x.1 (e.symm b),fun o => x.2 (f.symm o))) a =
      smooth F (fun b => a (e.symm b)) :=
  average_equiv (Equiv.arrowCongr f (Equiv.refl Color))
    (fun o => F (fun b => a (e.symm b),o))

theorem mixed_relabel (e : A' ≃ A) (f : O' ≃ O)
    (p : A → ℝ) (F : ((A → Color) × (O → Color)) → ℝ) :
    mixed p F = mixed (fun a => p (e a)) (fun x : (A' → Color) × (O' → Color) =>
      F (fun b => x.1 (e.symm b),fun o => x.2 (f.symm o))) := by
  rw [mixed_eq_joint,mixed_eq_joint]
  simp only [smooth_relabel]
  let q : (A' → Color) ≃ (A → Color) := Equiv.arrowCongr e (Equiv.refl Color)
  rw [← q.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [← q.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold manyWeight
  rw [← e.prod_comp]
  simp [q]

theorem mixedProbability_relabel (e : A' ≃ A) (f : O' ≃ O)
    (p : A → ℝ) (E : ((A → Color) × (O → Color)) → Prop) :
    mixedProbability p E = mixedProbability (fun a => p (e a))
      (fun x : (A' → Color) × (O' → Color) =>
        E (fun b => x.1 (e.symm b),fun o => x.2 (f.symm o))) :=
  mixed_relabel e f p _

end Relabel

variable {I : Type*} [Fintype I]
variable {J L : I → Type*} [∀ i, Fintype (J i)] [∀ i, Fintype (L i)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)
local instance : DecidableEq (Sigma L) := fun a b => Classical.propDecidable (a = b)

theorem average_product (f : ∀ i, (L i → Color) → ℝ) :
    average (fun o : Sigma L → Color => ∏ i, f i (fun j => o ⟨i,j⟩)) =
      ∏ i, average (f i) := by
  let e := flattenEquiv (fun _ _ => Color : (i : I) → L i → Type)
  unfold average
  rw [← Fintype.card_congr e, ← e.sum_comp]
  change (Fintype.card (∀ i, L i → Color) : ℝ)⁻¹ *
    (∑ o : ∀ i, L i → Color, ∏ i, f i (o i)) = _
  rw [Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib, ← Fintype.prod_sum]
  exact (Finset.prod_mul_distrib).symm

omit [∀ i, Fintype (J i)] in
theorem smooth_product
    (F : ∀ i, ((J i → Color) × (L i → Color)) → ℝ)
    (a : Sigma J → Color) :
    smooth (fun x : (Sigma J → Color) × (Sigma L → Color) =>
      ∏ i, F i (fun j => x.1 ⟨i,j⟩,fun j => x.2 ⟨i,j⟩)) a =
      ∏ i, smooth (F i) (fun j => a ⟨i,j⟩) :=
  average_product (fun i o => F i (fun j => a ⟨i,j⟩,o))

/-- Independent active/exterior groups factor for arbitrary real tests,
not just increasing events. -/
theorem mixed_product (p : Sigma J → ℝ)
    (F : ∀ i, ((J i → Color) × (L i → Color)) → ℝ) :
    mixed p (fun x : (Sigma J → Color) × (Sigma L → Color) =>
      ∏ i, F i (fun j => x.1 ⟨i,j⟩,fun j => x.2 ⟨i,j⟩)) =
      ∏ i, mixed (fun j => p ⟨i,j⟩) (F i) := by
  rw [mixed_eq_joint]
  simp only [smooth_product]
  let e := flattenEquiv (fun _ _ => Color : (i : I) → J i → Type)
  rw [← e.sum_comp]
  have hin (a : ∀ i, J i → Color) :
      (∑ b : Sigma J → Color, manyWeight p (e a) b *
        ((∏ i, smooth (F i) (a i)) * ∏ i, smooth (F i) (fun j => b ⟨i,j⟩))) =
      ∏ i, ∑ b : J i → Color, manyWeight (fun j => p ⟨i,j⟩) (a i) b *
        (smooth (F i) (a i) * smooth (F i) b) := by
    rw [← e.sum_comp]
    calc
      _ = ∑ b : ∀ i, J i → Color, ∏ i,
          manyWeight (fun j => p ⟨i,j⟩) (a i) (b i) *
            (smooth (F i) (a i) * smooth (F i) (b i)) := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [manyWeight, Fintype.prod_sigma, Finset.prod_mul_distrib]
        rfl
      _ = _ := (Fintype.prod_sum (fun i (b : J i → Color) =>
        manyWeight (fun j => p ⟨i,j⟩) (a i) b *
          (smooth (F i) (a i) * smooth (F i) b))).symm
  change (∑ a : ∀ i, J i → Color, ∑ b : Sigma J → Color, manyWeight p (e a) b *
    ((∏ i, smooth (F i) (a i)) * ∏ i, smooth (F i) (fun j => b ⟨i,j⟩))) = _
  simp_rw [hin]
  rw [← Fintype.prod_sum (fun i (a : J i → Color) =>
    ∑ b : J i → Color, manyWeight (fun j => p ⟨i,j⟩) a b *
      (smooth (F i) a * smooth (F i) b))]
  apply Finset.prod_congr rfl
  intro i _
  exact (mixed_eq_joint _ (F i)).symm

/-- This exact equality keeps every remote probe under its mixed law.
Canonical domination may then be applied solely to selected local factors. -/
theorem mixed_independent_groups (p : Sigma J → ℝ)
    (E : ∀ i, ((J i → Color) × (L i → Color)) → Prop) :
    mixedProbability p (fun x : (Sigma J → Color) × (Sigma L → Color) =>
      ∀ i, E i (fun j => x.1 ⟨i,j⟩,fun j => x.2 ⟨i,j⟩)) =
      ∏ i, mixedProbability (fun j => p ⟨i,j⟩) (E i) := by
  unfold mixedProbability
  simp only [ProbeProduct.indicator_forall]
  exact mixed_product p (fun i x => indicator (E i x))

theorem mixed_necessary_groups (p : Sigma J → ℝ)
    (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (E : ((Sigma J → Color) × (Sigma L → Color)) → Prop)
    (T : ∀ i, ((J i → Color) × (L i → Color)) → Prop)
    (hnecessary : ∀ x, E x → ∀ i, T i
      (fun j => x.1 ⟨i,j⟩,fun j => x.2 ⟨i,j⟩)) :
    mixedProbability p E ≤ ∏ i, mixedProbability (fun j => p ⟨i,j⟩) (T i) :=
  (mixedProbability_mono p hp0 hp1 _ _ hnecessary).trans_eq (mixed_independent_groups p T)

#print axioms mixed_product
#print axioms mixed_independent_groups

end

end ExceptionalTimes.MixedProbeProduct
