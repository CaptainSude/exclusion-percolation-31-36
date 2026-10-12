import ExceptionalTimes.DyadicSupportBox
import ExceptionalTimes.InsertionCounting
import ExceptionalTimes.EffectiveDimerInsertion

/-! Exact ordered-tuple formula for the actual finite expansion
coefficients, with the local clock normalization and its factorial. -/
open scoped Classical BigOperators
namespace ExceptionalTimes.OrderedDimerCoefficients
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PairSquareSewing Source06Specialization CenteredBlocks EnvironmentVariance
open DimerExpansion DimerSelectedDictionary DimerBaseField CanonicalSpatialProduct
open BlockExpansion ExpansionLimit EffectiveDimerInsertion InsertionCounting

theorem fullCoefficient_relabel {I J : Type*} [Fintype I] [Fintype J]
    (e : J≃I) (Λ : Finset Site) (endpoint : I×Fin 2 ↪ Site) (rules : I→Rule)
    (F : TwoTimeConfiguration→ℝ) :
    fullCoefficient Λ (relabelEndpoint e endpoint) (fun j => rules (e j)) F=
      fullCoefficient Λ endpoint rules F := by
  apply FiniteLaw.expect_congr
  intro ω
  simp only [overwrite_relabel]
  exact kernel_relabel e (fun i => (rules i).insertionWeight)
    (fun h => F (overwriteSourceHistory endpoint (complete ω) h))

variable {B : Type*} [Fintype B]

theorem selected_fair_full (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀v∈D,∃be,slot be=v) (rule : Rule) (S : Finset B)
    (F : TwoTimeConfiguration→ℝ)
    (hlocal : ∀ω η : TwoTimeConfiguration,(∀t v,v∈D→ω t v=η t v)→F ω=F η) :
    selectedKernel (fun _ => base) (fun _ => insertion rule) S
      (fun h => F (canonicalBackground slot (pairCoordinates.symm h)))=
      fullCoefficient D (selectedSlot slot S) (fun _ => rule) F := by
  rw [selected_coefficient_fair_overwrites slot D hcover _ S F hlocal]
  cases rule <;> rfl

def orderedEndpoint (slot : B×Fin 2 ↪ Site) {k : ℕ} (o : OrderedSelections B k) :
    Fin k×Fin 2 ↪ Site := relabelEndpoint o.2 (selectedSlot slot o.1.val)

@[simp] theorem orderedEndpoint_apply (slot : B×Fin 2 ↪ Site) {k : ℕ}
    (o : OrderedSelections B k) (i : Fin k) (a : Fin 2) :
    orderedEndpoint slot o (i,a)=slot (anchorTuple o i,a) := rfl

theorem selected_ordered_full (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀v∈D,∃be,slot be=v) (rule : Rule) {k : ℕ} (o : OrderedSelections B k)
    (F : TwoTimeConfiguration→ℝ)
    (hlocal : ∀ω η : TwoTimeConfiguration,(∀t v,v∈D→ω t v=η t v)→F ω=F η) :
    selectedKernel (fun _ => base) (fun _ => insertion rule) o.1.val
      (fun h => F (canonicalBackground slot (pairCoordinates.symm h)))=
      fullCoefficient D (orderedEndpoint slot o) (fun _ => rule) F := by
  rw [selected_fair_full slot D hcover rule o.1.val F hlocal]
  exact (fullCoefficient_relabel o.2 D (selectedSlot slot o.1.val) (fun _ => rule) F).symm

theorem coefficient_ordered (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀v∈D,∃be,slot be=v) (rule : Rule) (k : ℕ)
    (F : TwoTimeConfiguration→ℝ)
    (hlocal : ∀ω η : TwoTimeConfiguration,(∀t v,v∈D→ω t v=η t v)→F ω=F η) :
    coefficient (fun _ => base) (fun _ => insertion rule)
      (fun h => F (canonicalBackground slot (pairCoordinates.symm h))) k=
      (∑o : OrderedSelections B k,fullCoefficient D (orderedEndpoint slot o) (fun _ => rule) F)/
        (k.factorial:ℝ) := by
  have hfac : (k.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [coefficient_selection_sum]
  apply (eq_div_iff hfac).mpr
  rw [mul_comm,←ordered_sum_eq_factorial k (fun S => selectedKernel (fun _ => base)
    (fun _ => insertion rule) S (fun h => F (canonicalBackground slot (pairCoordinates.symm h))))]
  apply Finset.sum_congr rfl
  intro o _
  exact selected_ordered_full slot D hcover rule o F hlocal

theorem scaledCoefficient_ordered (slot : B×Fin 2 ↪ Site) (D : Finset Site)
    (hcover : ∀v∈D,∃be,slot be=v) (rule : Rule) (k : ℕ) (ε S : ℝ)
    (F : TwoTimeConfiguration→ℝ)
    (hlocal : ∀ω η : TwoTimeConfiguration,(∀t v,v∈D→ω t v=η t v)→F ω=F η) :
    scaledCoefficient rule (fun h => F (canonicalBackground slot (pairCoordinates.symm h)))
      (ε^2/S) k=
      (ε^(2*k)/(k.factorial:ℝ))*
        ∑o : OrderedSelections B k,fullCoefficient D (orderedEndpoint slot o) (fun _ => rule) F/S^k := by
  unfold scaledCoefficient
  rw [coefficient_ordered slot D hcover rule k F hlocal,div_pow,←pow_mul,←Finset.sum_div]
  ring

#print axioms coefficient_ordered
#print axioms scaledCoefficient_ordered
end
end ExceptionalTimes.OrderedDimerCoefficients
