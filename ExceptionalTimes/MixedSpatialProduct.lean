import ExceptionalTimes.LocalProductLaw
import ExceptionalTimes.CanonicalSpatialProduct
import ExceptionalTimes.MixedCanonicalVariance
import ExceptionalTimes.MixedAnnularCollar

/-! Spatial independence under the actual mixed two-time law. Outside
dimers have two independently sampled colors; active dimers keep the
canonical correlated two-time law. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.MixedSpatialProduct

open EnvironmentVariance ProbeProduct DimerLaw ManyDimerLaw FiniteHaar
open MixedCanonicalLaw MixedCanonicalVariance CanonicalSpatialProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A O I : Type*} [Fintype A] [Fintype O]

noncomputable def uniformColor : FiniteLaw Color where
  weight _ := (Fintype.card Color : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp

noncomputable def coordinateLaw (p : A→ℝ) (hp0 : ∀ a, 0≤p a)
    (hp1 : ∀ a, p a≤1) : A⊕O → FiniteLaw (Color×Color) :=
  Sum.elim (fun a => jointLaw (p a) (hp0 a) (hp1 a)) (fun _ => uniformColor.prod uniformColor)

def histories : (((A→Color)×(A→Color))×((O→Color)×(O→Color))) ≃
    (A⊕O→Color×Color) where
  toFun x := Sum.elim (fun a => (x.1.1 a,x.1.2 a)) (fun o => (x.2.1 o,x.2.2 o))
  invFun x := ((fun a => (x (.inl a)).1,fun a => (x (.inl a)).2),
    (fun o => (x (.inr o)).1,fun o => (x (.inr o)).2))
  left_inv _ := rfl
  right_inv x := by funext b; cases b <;> rfl

theorem outside_weight (x : (O→Color)×(O→Color)) :
    (∏ o : O, (uniformColor.prod uniformColor).weight (x.1 o,x.2 o)) =
      (Fintype.card (O→Color) : ℝ)⁻¹ * (Fintype.card (O→Color) : ℝ)⁻¹ := by
  simp only [FiniteLaw.prod,uniformColor,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fun,Nat.cast_pow,inv_pow]

theorem mixed_eq_product_expect (p : A→ℝ) (hp0 : ∀ a, 0≤p a)
    (hp1 : ∀ a, p a≤1) (F : ((A→Color)×(O→Color))→ℝ) :
    mixed p F = (FiniteLaw.pi (coordinateLaw (O := O) p hp0 hp1)).expect
      (fun x => F (fun a => (x (.inl a)).1,fun o => (x (.inr o)).1) *
        F (fun a => (x (.inl a)).2,fun o => (x (.inr o)).2)) := by
  rw [mixed_eq_joint]
  unfold FiniteLaw.expect
  rw [← (histories (A := A) (O := O)).sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hw (o v : O→Color) :
      (FiniteLaw.pi (coordinateLaw (O := O) p hp0 hp1)).weight (histories ((a,b),(o,v))) =
        manyWeight p a b * ((Fintype.card (O→Color) : ℝ)⁻¹ *
          (Fintype.card (O→Color) : ℝ)⁻¹) := by
    change (∏ s : A⊕O, (coordinateLaw p hp0 hp1 s).weight (histories ((a,b),(o,v)) s)) = _
    rw [Fintype.prod_sum_type]
    change manyWeight p a b * (∏ i : O, (uniformColor.prod uniformColor).weight (o i,v i)) = _
    exact congrArg (manyWeight p a b * ·) (outside_weight (o,v))
  simp only [hw]
  simp only [smooth,average,Finset.mul_sum,Finset.sum_mul,histories,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  apply Finset.sum_congr rfl
  intro v _
  ring

#print axioms mixed_eq_product_expect

theorem mixedProbability_eq_product_probability (p : A→ℝ) (hp0 : ∀ a, 0≤p a)
    (hp1 : ∀ a, p a≤1) (E : ((A→Color)×(O→Color))→Prop) :
    mixedProbability p E = probability (FiniteLaw.pi (coordinateLaw (O := O) p hp0 hp1))
      (fun x => E (fun a => (x (.inl a)).1,fun o => (x (.inr o)).1) ∧
        E (fun a => (x (.inl a)).2,fun o => (x (.inr o)).2)) := by
  rw [mixedProbability,mixed_eq_product_expect p hp0 hp1]
  apply FiniteLaw.expect_congr
  intro x
  dsimp only
  simp only [indicator]
  split_ifs <;> simp_all

variable [Fintype I] [DecidableEq I]

/-- Arbitrary events on disjoint sets of whole dimer labels factor under
the mixed law, with their original active/exterior status retained. -/
theorem mixed_local_product (p : A→ℝ) (hp0 : ∀ a, 0≤p a)
    (hp1 : ∀ a, p a≤1) (S : I→Set (A⊕O))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (E : I→((A→Color)×(O→Color))→Prop)
    (hlocal : ∀ i x y, (∀ b∈S i, Sum.elim x.1 x.2 b=Sum.elim y.1 y.2 b) →
      (E i x↔E i y)) :
    mixedProbability p (fun x => ∀ i, E i x)=∏ i, mixedProbability p (E i) := by
  simp_rw [mixedProbability_eq_product_probability p hp0 hp1]
  let F : I→(A⊕O→Color×Color)→Prop := fun i x =>
    E i (fun a => (x (.inl a)).1,fun o => (x (.inr o)).1) ∧
      E i (fun a => (x (.inl a)).2,fun o => (x (.inr o)).2)
  have hlocalF : ∀ i x y, Set.EqOn x y (S i) → (F i x↔F i y) := by
    intro i x y he
    apply and_congr
    · apply hlocal
      intro b hb
      cases b with
      | inl a => exact congrArg Prod.fst (he hb)
      | inr o => exact congrArg Prod.fst (he hb)
    · apply hlocal
      intro b hb
      cases b with
      | inl a => exact congrArg Prod.snd (he hb)
      | inr o => exact congrArg Prod.snd (he hb)
  have h := LocalProductLaw.pi_local_product (coordinateLaw (O := O) p hp0 hp1)
    ((fun _ => false),(fun _ => false)) S hdis F hlocalF
  convert h using 1
  apply probability_congr
  intro x
  exact forall_and.symm

#print axioms mixed_local_product

open MixedAnnularCollar

def siteLabels (slot : ((A⊕O)×Fin 2) ↪ Site) (S : Set Site) : Set (A⊕O) :=
  {b | ∃ i, slot (b,i)∈S}

theorem mixed_sites_local_product (p : A→ℝ) (hp0 : ∀ a, 0≤p a)
    (hp1 : ∀ a, p a≤1) (slot : ((A⊕O)×Fin 2) ↪ Site)
    (S : I→Set Site)
    (hdis : Pairwise (fun i j => Disjoint (siteLabels slot (S i)) (siteLabels slot (S j))))
    (E : I→Configuration→Prop)
    (hlocal : ∀ i ω η, Set.EqOn ω η (S i) → (E i ω↔E i η)) :
    mixedProbability p (fun x => ∀ i, E i (splitDecode slot x)) =
      ∏ i, mixedProbability p (fun x => E i (splitDecode slot x)) := by
  apply mixed_local_product p hp0 hp1 (fun i => siteLabels slot (S i)) hdis
  intro i x y he
  apply hlocal
  intro v hv
  by_cases hex : ∃ bi, slot bi=v
  · obtain ⟨⟨b,j⟩,rfl⟩ := hex
    have hc := congrFun (he b ⟨j,hv⟩) j
    simpa only [splitDecode,slot.injective.extend_apply] using hc
  · simp only [splitDecode,Function.extend_apply' _ _ _ hex]

#print axioms mixed_sites_local_product

end ExceptionalTimes.MixedSpatialProduct
