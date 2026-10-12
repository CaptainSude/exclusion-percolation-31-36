import ExceptionalTimes.LocalEventIndependence

/-! Exact independence for disjoint coordinate sets under arbitrary finite
product laws. Coordinates may be entire two-time dimer histories. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LocalProductLaw

open EnvironmentVariance ProbeProduct ForestProbes

variable {D E A X : Type*}

def relabel (e : D ≃ E) : (D → X) ≃ (E → X) where
  toFun ω y := ω (e.symm y)
  invFun η x := η (e x)
  left_inv ω := by funext x; simp
  right_inv η := by funext y; simp

def split {U : Type*} {S : A → Type*} :
    ((U ⊕ Sigma S) → X) ≃ ((U → X) × (∀ a, S a → X)) where
  toFun ω := (fun u => ω (.inl u), fun a s => ω (.inr ⟨a,s⟩))
  invFun o := Sum.elim o.1 (fun s => o.2 s.1 s.2)
  left_inv ω := by funext s; rcases s with u | ⟨a,s⟩ <;> rfl
  right_inv _ := rfl

def restrict (P : A → Set D) (ω : D → X) :
    ({d : D // ∀ a, d ∉ P a} → X) × (∀ a, {d : D // d ∈ P a} → X) :=
  (fun d => ω d.val,fun _ d => ω d.val)

noncomputable def partitionEquiv (P : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (P a) (P b))) :
    (D → X) ≃ (({d : D // ∀ a, d ∉ P a} → X) × (∀ a, {d : D // d ∈ P a} → X)) :=
  (relabel (sitePartition P hdis).symm).trans split

theorem partitionEquiv_apply (P : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (P a) (P b))) (ω : D → X) :
    partitionEquiv P hdis ω=restrict P ω := rfl

variable [Fintype D] [DecidableEq D] [Fintype A] [DecidableEq A] [Fintype X]

theorem pi_partition (μ : D → FiniteLaw X) (P : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (P a) (P b)))
    (f : (({d : D // ∀ a, d ∉ P a} → X) × (∀ a, {d : D // d ∈ P a} → X)) → ℝ) :
    (FiniteLaw.pi μ).expect (fun ω => f (restrict P ω)) =
      (probeLaw (FiniteLaw.pi (fun d : {d : D // ∀ a, d ∉ P a} => μ d.val))
        (fun a => FiniteLaw.pi (fun d : {d : D // d ∈ P a} => μ d.val))).expect f := by
  unfold FiniteLaw.expect
  rw [← (partitionEquiv (X := X) P hdis).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro o _
  have hf : restrict P ((partitionEquiv P hdis).symm o)=o :=
    (partitionEquiv P hdis).apply_symm_apply o
  dsimp only
  rw [hf]
  congr 1
  change (∏ d : D, (μ d).weight ((partitionEquiv P hdis).symm o d)) =
    (∏ d : {d : D // ∀ a, d ∉ P a}, (μ d.val).weight (o.1 d)) *
      ∏ a, ∏ d : {d : D // d ∈ P a}, (μ d.val).weight (o.2 a d)
  rw [← (sitePartition P hdis).prod_comp]
  simp only [Fintype.prod_sum_type,Fintype.prod_sigma]
  congr 1
  · apply Finset.prod_congr rfl
    intro d _
    exact congrArg (fun x => (μ d.val).weight x) (congrArg (fun o => o.1 d) hf)
  · apply Finset.prod_congr rfl
    intro a _
    apply Finset.prod_congr rfl
    intro d _
    exact congrArg (fun x => (μ d.val).weight x) (congrArg (fun o => o.2 a d) hf)

noncomputable def fill (default : X) (S : Set D) (ω : S → X) : D → X :=
  fun d => if h : d ∈ S then ω ⟨d,h⟩ else default

omit [Fintype D] [DecidableEq D] [Fintype X] in
theorem fill_agrees (default : X) (S : Set D) (ω : D → X) :
    Set.EqOn ω (fill default S (fun d => ω d.val)) S := by
  intro d hd
  simp only [fill,dite_eq_left hd]

theorem pi_local_product (μ : D → FiniteLaw X) (default : X) (P : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (P a) (P b)))
    (E : A → (D → X) → Prop)
    (hlocal : ∀ a ω η, Set.EqOn ω η (P a) → (E a ω ↔ E a η)) :
    probability (FiniteLaw.pi μ) (fun ω => ∀ a, E a ω) =
      ∏ a, probability (FiniteLaw.pi μ) (E a) := by
  let L : ∀ a, (P a → X) → Prop := fun a η => E a (fill default (P a) η)
  have hE (ω : D → X) (a : A) : E a ω ↔ L a (fun d => ω d.val) :=
    hlocal a ω _ (fill_agrees default (P a) ω)
  have hwhole : probability (FiniteLaw.pi μ) (fun ω => ∀ a, E a ω) =
      ∏ a, probability (FiniteLaw.pi (fun d : P a => μ d.val)) (L a) := by
    rw [probability_congr (FiniteLaw.pi μ) (fun ω => forall_congr' (hE ω))]
    change (FiniteLaw.pi μ).expect (fun ω => indicator (∀ a, L a ((restrict P ω).2 a))) = _
    rw [pi_partition μ P hdis (fun o => indicator (∀ a, L a (o.2 a)))]
    exact probability_probeLaw _ _ L
  have hsingle (a : A) : probability (FiniteLaw.pi μ) (E a) =
      probability (FiniteLaw.pi (fun d : P a => μ d.val)) (L a) := by
    rw [probability_congr (FiniteLaw.pi μ) (fun ω => hE ω a)]
    change (FiniteLaw.pi μ).expect (fun ω => indicator (L a ((restrict P ω).2 a))) = _
    rw [pi_partition μ P hdis (fun o => indicator (L a (o.2 a)))]
    unfold probeLaw
    rw [FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const,probability]
    exact expect_pi_coordinate (fun a => FiniteLaw.pi (fun d : {d : D // d ∈ P a} => μ d.val)) a (fun x => indicator (L a x))
  rw [hwhole]
  exact Finset.prod_congr rfl (fun a _ => (hsingle a).symm)

#print axioms pi_local_product

end ExceptionalTimes.LocalProductLaw
