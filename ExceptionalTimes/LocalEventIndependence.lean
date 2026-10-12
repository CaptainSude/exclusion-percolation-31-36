import ExceptionalTimes.ForestProbes

/-! Independence of actual local events follows from the proved partition
of the original finite fair coloring. No probabilistic independence is
an input to these theorems. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.ProbeProduct

open EnvironmentVariance

noncomputable def fillLocal {D : Type*} (S : Set D) (ω : S → Bool) : D → Bool :=
  fun d => if h : d ∈ S then ω ⟨d,h⟩ else false

theorem restrict_fill_eqOn {D : Type*} (S : Set D) (ω : D → Bool) :
    Set.EqOn ω (fillLocal S (fun d => ω d.val)) S := by
  intro d hd
  simp only [fillLocal,dite_eq_left hd]

theorem expect_pi_coordinate {A : Type*} [Fintype A] [DecidableEq A]
    {X : A → Type*} [∀ a, Fintype (X a)] (μ : ∀ a, FiniteLaw (X a))
    (a : A) (f : X a → ℝ) :
    (FiniteLaw.pi μ).expect (fun x => f (x a)) = (μ a).expect f := by
  rw [FiniteLaw.expect_pi_split μ a]
  simp [Equiv.piSplitAt,FiniteLaw.expect_const]

theorem probability_congr {D : Type*} [Fintype D] (μ : FiniteLaw D)
    {E F : D → Prop} (h : ∀ d, E d ↔ F d) : probability μ E = probability μ F := by
  unfold probability
  congr 1
  funext d
  rw [h d]

/-- All dependence is expressed by literal equality of colors on the
specified subsets of the original site set. -/
theorem fairSites_local_product {D A : Type*} [Fintype D] [DecidableEq D]
    [Fintype A] [DecidableEq A] (S : A → Set D)
    (hdis : Pairwise (fun a b => Disjoint (S a) (S b)))
    (E : A → (D → Bool) → Prop)
    (hlocal : ∀ a ω η, Set.EqOn ω η (S a) → (E a ω ↔ E a η)) :
    probability (fairSites D) (fun ω => ∀ a, E a ω) =
      ∏ a, probability (fairSites D) (E a) := by
  let L : ∀ a, (S a → Bool) → Prop := fun a η => E a (fillLocal (S a) η)
  have hE (ω : D → Bool) (a : A) : E a ω ↔ L a (fun d => ω d.val) :=
    hlocal a ω _ (restrict_fill_eqOn (S a) ω)
  have hwhole : probability (fairSites D) (fun ω => ∀ a, E a ω) =
      ∏ a, probability (fairSites (S a)) (L a) := by
    rw [probability_congr (fairSites D) (fun ω => forall_congr' (hE ω))]
    change (fairSites D).expect (fun ω => indicator (∀ a, L a ((ForestProbes.groupColors S ω).2 a))) = _
    rw [ForestProbes.fairSites_partition S hdis (fun o => indicator (∀ a, L a (o.2 a)))]
    exact probability_probeLaw (fairSites {d : D // ∀ a, d ∉ S a})
      (fun a => fairSites (S a)) L
  have hsingle (a : A) : probability (fairSites D) (E a) =
      probability (fairSites (S a)) (L a) := by
    rw [probability_congr (fairSites D) (fun ω => hE ω a)]
    change (fairSites D).expect (fun ω => indicator (L a ((ForestProbes.groupColors S ω).2 a))) = _
    rw [ForestProbes.fairSites_partition S hdis (fun o => indicator (L a (o.2 a)))]
    unfold probeLaw
    rw [FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const,probability]
    exact expect_pi_coordinate (fun a => fairSites (S a)) a (fun x => indicator (L a x))
  rw [hwhole]
  exact Finset.prod_congr rfl (fun a _ => (hsingle a).symm)

theorem fairSites_two_local {D : Type*} [Fintype D] [DecidableEq D]
    (S T : Set D) (hdis : Disjoint S T) (E F : (D → Bool) → Prop)
    (hE : ∀ ω η, Set.EqOn ω η S → (E ω ↔ E η))
    (hF : ∀ ω η, Set.EqOn ω η T → (F ω ↔ F η)) :
    probability (fairSites D) (fun ω => E ω ∧ F ω) =
      probability (fairSites D) E * probability (fairSites D) F := by
  let sets : Bool → Set D := fun b => if b then T else S
  let events : Bool → (D → Bool) → Prop := fun b => if b then F else E
  have hd : Pairwise (fun a b => Disjoint (sets a) (sets b)) := by
    intro a b hab
    cases a <;> cases b <;> simp_all [sets,disjoint_comm]
  have hl : ∀ a ω η, Set.EqOn ω η (sets a) → (events a ω ↔ events a η) := by
    intro a
    cases a
    · exact hE
    · exact hF
  have h := fairSites_local_product sets hd events hl
  simpa only [events,Bool.forall_bool,Bool.false_eq_true,ite_false,ite_true,
    Fintype.prod_bool,mul_comm] using h

#print axioms fairSites_local_product
#print axioms fairSites_two_local

end ExceptionalTimes.ProbeProduct


