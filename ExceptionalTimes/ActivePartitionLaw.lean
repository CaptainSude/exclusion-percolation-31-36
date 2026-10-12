import ExceptionalTimes.ActiveMiddlePartition
import ExceptionalTimes.MesoscopicVariance
import ExceptionalTimes.MixedProbeProduct

/-! Exact color-law dictionaries for the constructed active/exterior
partition and its mesoscopic regrouping. These hold for arbitrary tests,
so they do not impose monotonicity on local arm probes. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.ActivePartitionLaw

noncomputable section

open DimerLaw ManyDimerLaw FiniteHaar EnvironmentVariance
open ActiveMiddlePartition MixedAnnularCollar MixedCanonicalLaw MesoscopicVariance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {A O : Type*} : DecidableEq (A ⊕ O) :=
  fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a = b)

local instance {A O : Type*} [Fintype A] (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) :
    DecidableEq (Sigma (Fiber m slot)) := fun a b => Classical.propDecidable (a = b)

def pairDecode {B : Type*} (slot : B × Fin 2 ↪ Site) (x : B → Color) : Configuration :=
  Function.extend slot (fun b => x b.1 b.2) (fun _ => false)

def reindexSlot {B C : Type*} (slot : B × Fin 2 ↪ Site) (e : C ≃ B) :
    C × Fin 2 ↪ Site := (e.prodCongr (Equiv.refl (Fin 2))).toEmbedding.trans slot

theorem pairDecode_reindex {B C : Type*} (slot : B × Fin 2 ↪ Site) (e : C ≃ B)
    (x : C → Color) :
    pairDecode (reindexSlot slot e) x = pairDecode slot (fun b => x (e.symm b)) := by
  funext v
  by_cases hex : ∃ b, slot b = v
  · obtain ⟨⟨b,k⟩,rfl⟩ := hex
    have he : reindexSlot slot e (e.symm b,k) = slot (b,k) := by simp [reindexSlot]
    unfold pairDecode
    conv_lhs => rw [← he]
    rw [(reindexSlot slot e).injective.extend_apply,slot.injective.extend_apply]
  · have hnew : ¬ ∃ c, reindexSlot slot e c = v := by
      rintro ⟨⟨c,k⟩,hc⟩
      exact hex ⟨(e c,k),hc⟩
    unfold pairDecode
    rw [Function.extend_apply' _ _ _ hnew,Function.extend_apply' _ _ _ hex]

theorem splitDecode_eq_pairDecode {A O : Type*}
    (slot : ((A ⊕ O) × Fin 2) ↪ Site) (x : (A → Color) × (O → Color)) :
    splitDecode slot x = pairDecode slot (Sum.elim x.1 x.2) := rfl

theorem partition_decode {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site)
    (x : ActiveLabels slot z S ⊕ ExteriorLabels slot z S → Color) :
    splitDecode (splitSlot slot z S) (fun a => x (.inl a),fun o => x (.inr o)) =
      pairDecode slot (fun b => x ((splitEquiv slot z S).symm b)) := by
  rw [splitDecode_eq_pairDecode]
  have he : (Sum.elim (fun a => x (.inl a)) (fun o => x (.inr o))) = x := by
    funext s
    cases s <;> rfl
  rw [he]
  exact pairDecode_reindex slot (splitEquiv slot z S) x

theorem partition_manyProbability {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site)
    (p : B → ℝ) (E : Configuration → Prop) :
    manyProbability p (fun x => E (pairDecode slot x)) =
      manyProbability (Sum.elim (fun a : ActiveLabels slot z S => p a.val)
        (fun o : ExteriorLabels slot z S => p o.val))
        (fun x => E (splitDecode (splitSlot slot z S)
          (fun a => x (.inl a),fun o => x (.inr o)))) := by
  rw [CanonicalRadialLaw.many_relabel (splitEquiv slot z S)]
  have hp : (fun c => p (splitEquiv slot z S c)) =
      Sum.elim (fun a : ActiveLabels slot z S => p a.val)
        (fun o : ExteriorLabels slot z S => p o.val) := by
    funext c
    cases c <;> rfl
  rw [hp]
  congr 1
  funext x
  rw [partition_decode]

theorem grouped_decode {A O : Type*} [Fintype A]
    (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (x : (Sigma (Fiber m slot) → Color) × (O → Color)) :
    MixedSiteVariance.decode (groupedSlot m slot) x =
      splitDecode slot (fun a => x.1 ((MesoscopicCells.groupingEquiv m (activeSlot slot)).symm a),x.2) := by
  change pairDecode (reindexSlot slot
    (Equiv.sumCongr (MesoscopicCells.groupingEquiv m (activeSlot slot)) (Equiv.refl O)))
    (Sum.elim x.1 x.2) = _
  rw [pairDecode_reindex,splitDecode_eq_pairDecode]
  congr 1
  funext s
  cases s <;> rfl

theorem grouped_mixedProbability {A O : Type*} [Fintype A] [Fintype O]
    (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) (p : A → ℝ)
    (E : Configuration → Prop) :
    mixedProbability p (fun x => E (splitDecode slot x)) =
      mixedProbability (fun s => p (MesoscopicCells.groupingEquiv m (activeSlot slot) s))
        (fun x => E (MixedSiteVariance.decode (groupedSlot m slot) x)) := by
  rw [MixedProbeProduct.mixedProbability_relabel
    (MesoscopicCells.groupingEquiv m (activeSlot slot)) (Equiv.refl O)]
  congr 1
  funext x
  rw [grouped_decode]
  rfl

theorem grouped_average {A O : Type*} [Fintype A] [Fintype O]
    (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) (F : Configuration → ℝ) :
    average (smooth (fun x => F (splitDecode slot x))) =
      average (smooth (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x))) := by
  have he : (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x)) =
      (fun x => F (splitDecode slot
        (fun a => x.1 ((MesoscopicCells.groupingEquiv m (activeSlot slot)).symm a),x.2))) := by
    funext x
    rw [grouped_decode]
  rw [he]
  exact (average_equiv (Equiv.arrowCongr (MesoscopicCells.groupingEquiv m (activeSlot slot))
    (Equiv.refl Color)) (fun a => average (fun o => F (splitDecode slot (a,o))))).symm

theorem partition_average {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) (F : Configuration → ℝ) :
    average (fun x => F (pairDecode slot x)) =
      average (smooth (fun x => F (splitDecode (splitSlot slot z S) x))) := by
  rw [average_smooth]
  have h₁ := average_equiv
    (Equiv.arrowCongr (splitEquiv slot z S) (Equiv.refl Color))
    (fun x => F (pairDecode slot x))
  have h₂ := average_equiv (Equiv.sumArrowEquivProdArrow
    (ActiveLabels slot z S) (ExteriorLabels slot z S) Color)
    (fun x => F (splitDecode (splitSlot slot z S) x))
  apply h₁.symm.trans
  apply Eq.trans _ h₂
  congr 1
  funext x
  exact congrArg F (partition_decode slot z S x).symm

/-- Canonical collar comparison on the original dimer labels, with the
active partition constructed from the literal middle-annulus support. -/
theorem partition_collar_comparison {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    {r R : ℕ} (hR : 16*r ≤ R)
    (hcover : ∀ v ∈ HoleFilling.annularSites (2*r) (R/2), ∃ b, slot b = v)
    {b : ℝ} (hb : 0 < b)
    (hbridge : b ≤ average (fun x => indicator (AnnularCollars.CollarBridge
      (splitDecode (splitSlot slot z (HoleFilling.annularSites (2*r) (R/2))) x) r R))) :
    manyProbability p (fun x => HoleFilling.WiredArm (pairDecode slot x) r R) ≤
      mixedProbability (fun a : ActiveLabels slot z (HoleFilling.annularSites (2*r) (R/2)) => p a.val)
        (fun x => HoleFilling.WiredArm
          (splitDecode (splitSlot slot z (HoleFilling.annularSites (2*r) (R/2))) x) r R) / b^2 := by
  rw [partition_manyProbability slot z (HoleFilling.annularSites (2*r) (R/2))
    p (fun ω => HoleFilling.WiredArm ω r R)]
  exact radial_collar_comparison
    (A := ActiveLabels slot z (HoleFilling.annularSites (2*r) (R/2)))
    (O := ExteriorLabels slot z (HoleFilling.annularSites (2*r) (R/2)))
    _ _ _ (fun a => hp0 a.val) (fun a => hp1 a.val)
    (fun o => hp0 o.val) (fun o => hp1 o.val) hR
    (activeCovers_split slot z hz0 _ hp hcover) hb hbridge

theorem split_covers {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S V : Finset Site)
    (hcover : ∀ v ∈ V, ∃ b, slot b = v) :
    ∀ v ∈ V, ∃ b, splitSlot slot z S b = v := by
  intro v hv
  obtain ⟨⟨b,k⟩,rfl⟩ := hcover v hv
  exact ⟨((splitEquiv slot z S).symm b,k),by simp [splitSlot]⟩

/-- The complete split is available for any finite observation support
and any active sub-support, including arbitrary wide middle annuli. -/
theorem exists_support_partition (z : Site) (hz0 : z ≠ (0,0))
    (S V : Finset Site) (hSV : S ⊆ V) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ v, v ∈ FiniteMatchingClosure.closure (PeriodicMatching.partner z) V ↔ ∃ b, slot b = v) ∧
      (∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) ∧
      ActiveCovers (splitSlot slot z S) S ∧
      (∀ v ∈ V, ∃ b, splitSlot slot z S b = v) := by
  obtain ⟨k,slot,hcover,hp⟩ := FiniteMatchingClosure.periodic_closure_enumeration z hz0 V
  have hV : ∀ v ∈ V, ∃ b, slot b = v :=
    fun v hv => (hcover v).mp (FiniteMatchingClosure.subset_closure _ V hv)
  exact ⟨k,slot,hcover,hp,activeCovers_split slot z hz0 S hp (fun v hv => hV v (hSV hv)),
    split_covers slot z S V hV⟩

#print axioms pairDecode_reindex
#print axioms partition_manyProbability
#print axioms grouped_mixedProbability
#print axioms grouped_average
#print axioms partition_average
#print axioms partition_collar_comparison
#print axioms exists_support_partition

end

end ExceptionalTimes.ActivePartitionLaw
