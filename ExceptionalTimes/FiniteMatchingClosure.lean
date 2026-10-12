import ExceptionalTimes.FiniteClockEnergy
import ExceptionalTimes.PeriodicMatching

open scoped BigOperators Classical

namespace ExceptionalTimes.FiniteMatchingClosure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Type*} [Fintype S]

noncomputable def rank (x : S) : ℕ := (Fintype.equivFin S x).val

theorem rank_injective : Function.Injective (rank (S := S)) :=
  fun _ _ h => (Fintype.equivFin S).injective (Fin.ext h)

abbrev Representatives (p : S → S) := {x : S // rank x < rank (p x)}

noncomputable def pairMap (p : S → S) (a : Representatives p × Fin 2) : S :=
  if a.2 = 0 then a.1.val else p a.1.val

theorem representative_ne_partner (p : S → S) (hp : Function.Involutive p)
    (a b : Representatives p) : a.val ≠ p b.val := by
  intro he
  have ha := a.property
  rw [he, hp] at ha
  exact not_lt_of_ge b.property.le ha

theorem pairMap_injective (p : S → S) (hp : Function.Involutive p) :
    Function.Injective (pairMap p) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ he
  fin_cases i <;> fin_cases j <;> simp [pairMap] at he
  · exact Prod.ext (Subtype.ext he) rfl
  · exact (representative_ne_partner p hp a b he).elim
  · exact (representative_ne_partner p hp b a he.symm).elim
  · exact Prod.ext (Subtype.ext (hp.injective he)) rfl

theorem pairMap_surjective (p : S → S) (hp : Function.Involutive p)
    (hfixed : ∀ x, p x ≠ x) : Function.Surjective (pairMap p) := by
  intro x
  by_cases hx : rank x < rank (p x)
  · exact ⟨(⟨x, hx⟩, 0), by simp [pairMap]⟩
  · have hpx : rank (p x) < rank (p (p x)) := by
      rw [hp]
      exact lt_of_le_of_ne (le_of_not_gt hx) (fun he => hfixed x (rank_injective he))
    exact ⟨(⟨p x, hpx⟩, 1), by simpa only [pairMap, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hp x⟩

/-- A finite fixed-point-free involution is enumerated by actual disjoint
pairs. The enumeration is constructed, rather than assumed as input. -/
theorem exists_pair_enumeration (p : S → S) (hp : Function.Involutive p)
    (hfixed : ∀ x, p x ≠ x) :
    ∃ k : ℕ, ∃ e : (Fin k × Fin 2) ≃ S, ∀ b, e (b, 1) = p (e (b, 0)) := by
  classical
  let R := Representatives p
  let E : R × Fin 2 ≃ S := Equiv.ofBijective (pairMap p)
    ⟨pairMap_injective p hp, pairMap_surjective p hp hfixed⟩
  let e : (Fin (Fintype.card R) × Fin 2) ≃ S :=
    (Equiv.prodCongr (Fintype.equivFin R).symm (Equiv.refl (Fin 2))).trans E
  refine ⟨Fintype.card R, e, ?_⟩
  intro b
  change pairMap p (_, 1) = p (pairMap p (_, 0))
  simp [pairMap]

section Closure

variable {α : Type*} [DecidableEq α]

def closure (p : α → α) (A : Finset α) : Finset α := A ∪ A.image p

theorem subset_closure (p : α → α) (A : Finset α) : A ⊆ closure p A := Finset.subset_union_left

theorem closure_invariant (p : α → α) (hp : Function.Involutive p) (A : Finset α)
    {x : α} (hx : x ∈ closure p A) : p x ∈ closure p A := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [hp]
    exact Finset.mem_union_left _ hy

theorem exists_closure_enumeration (p : α → α) (hp : Function.Involutive p)
    (hfixed : ∀ x, p x ≠ x) (A : Finset α) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ α,
      (∀ x, x ∈ closure p A ↔ ∃ b, slot b = x) ∧
      (∀ b, slot (b, 1) = p (slot (b, 0))) := by
  let q : closure p A → closure p A := fun x => ⟨p x, closure_invariant p hp A x.property⟩
  have hq : Function.Involutive q := fun x => Subtype.ext (hp x)
  have hqn : ∀ x, q x ≠ x := fun x he => hfixed x (congrArg Subtype.val he)
  obtain ⟨k, e, he⟩ := exists_pair_enumeration q hq hqn
  let slot : Fin k × Fin 2 ↪ α := e.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨k, slot, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := e.surjective ⟨x, hx⟩
      exact ⟨b, congrArg Subtype.val hb⟩
    · rintro ⟨b, rfl⟩
      exact (e b).property
  · intro b
    exact congrArg Subtype.val (he b)

end Closure

theorem periodic_closure_enumeration (z : Site) (hz : z ≠ (0, 0)) (A : Finset Site) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ x, x ∈ closure (PeriodicMatching.partner z) A ↔ ∃ b, slot b = x) ∧
      (∀ b, slot (b, 1) = PeriodicMatching.partner z (slot (b, 0))) :=
  exists_closure_enumeration (PeriodicMatching.partner z)
    (PeriodicMatching.partner_involutive z hz) (PeriodicMatching.partner_ne_self z hz) A

noncomputable def closureEdges (p : Site → Site) (A : Finset Site) : Finset (Sym2 Site) :=
  (closure p A).image (fun x => s(x, p x))

theorem enumeration_edges {k : ℕ} (p : Site → Site) (hp : Function.Involutive p)
    (A : Finset Site) (slot : Fin k × Fin 2 ↪ Site)
    (hcover : ∀ x, x ∈ closure p A ↔ ∃ b, slot b = x)
    (hpair : ∀ b, slot (b, 1) = p (slot (b, 0))) :
    MatchingDimerLaw.edges slot = closureEdges p A := by
  ext e
  constructor
  · intro he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_image.mpr
    exact ⟨slot (b, 0), (hcover _).mpr ⟨(b, 0), rfl⟩, by rw [← hpair]; rfl⟩
  · intro he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨⟨b, i⟩, rfl⟩ := (hcover x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨b, Finset.mem_univ _, ?_⟩
    fin_cases i
    · change s(slot (b, 0), slot (b, 1)) = s(slot (b, 0), p (slot (b, 0)))
      rw [← hpair]
    · change s(slot (b, 0), slot (b, 1)) = s(slot (b, 1), p (slot (b, 1)))
      rw [hpair, hp]
      exact Sym2.eq_swap

noncomputable def decode {k : ℕ} (slot : Fin k × Fin 2 ↪ Site)
    (η : Fin k → DimerLaw.Color) : Configuration :=
  Function.extend slot (fun b => η b.1 b.2) (fun _ => false)

theorem decode_project_agrees {k : ℕ} (slot : Fin k × Fin 2 ↪ Site)
    (η : Configuration) {x : Site} (hx : ∃ b, slot b = x) :
    decode slot (MatchingDimerLaw.project slot η) x = η x := by
  obtain ⟨b, rfl⟩ := hx
  exact Function.Injective.extend_apply slot.injective _ _ b

theorem matching_cylinder_law {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : MeasureTheory.Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate) {k : ℕ} (slot : Fin k × Fin 2 ↪ Site)
    (hrate : ∀ b, rate (MatchingDimerLaw.edge slot b) = 1 / 2)
    (A : Finset Site) (hcover : ∀ x ∈ A, ∃ b, slot b = x)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ))
    (t : ℝ) (ht : 0 < t) :
    P.truncatedPairedCylinderProbability (MatchingDimerLaw.edges slot) E t =
      ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
        (fun η => E (decode slot η))) := by
  have he (η : Configuration) : E η ↔ E (decode slot (MatchingDimerLaw.project slot η)) :=
    hlocal _ _ (fun x hx => (decode_project_agrees slot η (hcover x hx)).symm)
  have H := MatchingDimerLaw.graphical_matching_pairedProbability P slot hrate t ht
    (fun η => E (decode slot η))
  rw [← H]
  unfold PoissonGraphicalRealization.truncatedPairedCylinderProbability
  congr 1
  ext ω
  exact and_congr (he _) (he _)

theorem closure_cylinder_law {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : MeasureTheory.Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (p : Site → Site) (hp : Function.Involutive p) (hfixed : ∀ x, p x ≠ x)
    (hrate : ∀ x, rate s(x, p x) = 1 / 2) (A : Finset Site)
    (E : Configuration → Prop)
    (hlocal : ∀ η ξ, (∀ x ∈ A, η x = ξ x) → (E η ↔ E ξ)) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ x, x ∈ closure p A ↔ ∃ b, slot b = x) ∧
      (∀ b, slot (b, 1) = p (slot (b, 0))) ∧
      ∀ t : ℝ, 0 < t → P.truncatedPairedCylinderProbability (closureEdges p A) E t =
        ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
          (fun η => E (decode slot η))) := by
  obtain ⟨k, slot, hcover, hpair⟩ := exists_closure_enumeration p hp hfixed A
  refine ⟨k, slot, hcover, hpair, ?_⟩
  intro t ht
  rw [← enumeration_edges p hp A slot hcover hpair]
  apply matching_cylinder_law P slot ?_ A ?_ E hlocal t ht
  · intro b
    unfold MatchingDimerLaw.edge
    rw [hpair]
    exact hrate _
  · intro x hx
    exact (hcover x).mp (subset_closure p A hx)

theorem periodic_oneArm_law {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : MeasureTheory.Measure Ξ} {rate : Sym2 Site → ℝ}
    (P : PoissonGraphicalRealization μ rate)
    (z : Site) (hz : z ≠ (0, 0))
    (hrate : ∀ x, rate s(x, PeriodicMatching.partner z x) = 1 / 2)
    (v : Site) (R : ℕ) (hv : v ∈ latticeBox R) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ x, x ∈ closure (PeriodicMatching.partner z) (latticeBox (R + 1)) ↔ ∃ b, slot b = x) ∧
      (∀ b, slot (b, 1) = PeriodicMatching.partner z (slot (b, 0))) ∧
      ∀ t : ℝ, 0 < t → P.truncatedPairedCylinderProbability
        (closureEdges (PeriodicMatching.partner z) (latticeBox (R + 1)))
        (fun η => OneArm η v R) t =
        ENNReal.ofReal (ManyDimerLaw.manyProbability (fun _ => DimerLaw.refreshProbability t)
          (fun η => OneArm (decode slot η) v R)) :=
  closure_cylinder_law P (PeriodicMatching.partner z)
    (PeriodicMatching.partner_involutive z hz) (PeriodicMatching.partner_ne_self z hz)
    hrate (latticeBox (R + 1)) (fun η => OneArm η v R)
    (fun _ _ he => oneArm_congr_of_eqOn_box hv he)

#print axioms exists_pair_enumeration
#print axioms periodic_closure_enumeration
#print axioms closure_cylinder_law
#print axioms periodic_oneArm_law

end ExceptionalTimes.FiniteMatchingClosure
