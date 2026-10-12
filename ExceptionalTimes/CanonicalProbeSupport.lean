import ExceptionalTimes.CanonicalRadialLaw

/-! Exact independence for probes supported on disjoint sets of whole
dimer labels. Unused coordinates are integrated out from the literal
normalized law; no full partition or enumeration premise is required. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.CanonicalProbeSupport

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance CanonicalRadialLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {U V B C : Type*} [Fintype U] [Fintype V] [Fintype B] [Fintype C]

local instance : DecidableEq (U ⊕ V) := fun a b => Classical.propDecidable (a = b)

def sumLayers : (((U ⊕ V) → Color) × ((U ⊕ V) → Color)) ≃
    (((U → Color) × (U → Color)) × ((V → Color) × (V → Color))) where
  toFun x := ((fun u => x.1 (.inl u), fun u => x.2 (.inl u)),
    (fun v => x.1 (.inr v), fun v => x.2 (.inr v)))
  invFun x := (Sum.elim x.1.1 x.2.1, Sum.elim x.1.2 x.2.2)
  left_inv x := by ext s <;> cases s <;> rfl
  right_inv _ := rfl

theorem sum_expect (p : U ⊕ V → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (f : (((U ⊕ V) → Color) × ((U ⊕ V) → Color)) → ℝ) :
    (manyLaw p hp0 hp1).expect f =
      ((manyLaw (fun u => p (.inl u)) (fun u => hp0 (.inl u)) (fun u => hp1 (.inl u))).prod
        (manyLaw (fun v => p (.inr v)) (fun v => hp0 (.inr v)) (fun v => hp1 (.inr v)))).expect
          (fun x => f (sumLayers.symm x)) := by
  unfold FiniteLaw.expect
  rw [← sumLayers.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change (∏ s : U ⊕ V, twoTimeWeight (p s)
      (Sum.elim x.1.1 x.2.1 s) (Sum.elim x.1.2 x.2.2 s)) =
    (∏ u, twoTimeWeight (p (.inl u)) (x.1.1 u) (x.1.2 u)) *
      ∏ v, twoTimeWeight (p (.inr v)) (x.2.1 v) (x.2.2 v)
  exact Fintype.prod_sum_type _

theorem many_sum_left (p : U ⊕ V → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (U → Color) → Prop) :
    manyProbability p (fun x => E (fun u => x (.inl u))) =
      manyProbability (fun u => p (.inl u)) E := by
  rw [manyProbability_eq_joint p hp0 hp1,
    manyProbability_eq_joint _ (fun u => hp0 (.inl u)) (fun u => hp1 (.inl u))]
  unfold probability
  rw [sum_expect, FiniteLaw.expect_prod]
  simp only [sumLayers, Equiv.coe_fn_symm_mk, Sum.elim_inl, FiniteLaw.expect_const]

/-- Any injective selection of whole dimers has its original product law. -/
theorem many_restrict (f : C ↪ B) (p : B → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (C → Color) → Prop) :
    manyProbability p (fun x => E (fun c => x (f c))) =
      manyProbability (fun c => p (f c)) E := by
  let Z := {b : B // b ∉ Set.range f}
  let e : C ⊕ Z ≃ B :=
    (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl Z)).trans
      (Equiv.sumCompl (fun b => b ∈ Set.range f))
  have he (c : C) : e (.inl c) = f c := rfl
  rw [many_relabel e]
  have hE (x : C ⊕ Z → Color) :
      E (fun c => x (e.symm (f c))) ↔ E (fun c => x (.inl c)) := by
    simp only [← he, Equiv.symm_apply_apply]
  rw [many_congr _ hE]
  exact many_sum_left (fun b => p (e b)) (fun b => hp0 (e b)) (fun b => hp1 (e b)) E

variable {I : Type*} [Fintype I]

local instance (D : I → Finset B) : DecidableEq (Σ i, {b // b ∈ D i}) :=
  fun a b => Classical.propDecidable (a = b)

def supportEmbedding (D : I → Finset B) (hD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    (Σ i, {b // b ∈ D i}) ↪ B where
  toFun s := s.2.val
  inj' := by
    rintro ⟨i, b, hb⟩ ⟨j, c, hc⟩ h
    dsimp at h
    subst c
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hD hne) hb hc
    subst j
    rfl

/-- Probes on disjoint finite sets of dimer labels are exactly independent
under the paired law, even when their union omits some dimers. -/
theorem many_disjoint_supports (D : I → Finset B) (hD : Pairwise (fun i j => Disjoint (D i) (D j)))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : ∀ i, ({b // b ∈ D i} → Color) → Prop) :
    manyProbability p (fun x => ∀ i, E i (fun b => x b)) =
      ∏ i, manyProbability (fun b : {b // b ∈ D i} => p b) (E i) := by
  let f := supportEmbedding D hD
  have h := many_restrict f p hp0 hp1 (fun x => ∀ i, E i (fun b => x ⟨i,b⟩))
  have h' := many_independent_groups (fun s => p (f s)) (fun s => hp0 (f s))
    (fun s => hp1 (f s)) E
  exact h.trans h'

#print axioms many_restrict
#print axioms many_disjoint_supports

end

end ExceptionalTimes.CanonicalProbeSupport
