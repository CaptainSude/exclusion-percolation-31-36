import ExceptionalTimes.ActivePartitionLaw
import ExceptionalTimes.MixedWideCollar

/-! The wide-collar comparison on the original finite matching law.
The active partition, static-law transport, and complete support are
constructed. Numerical premises are ordinary static arm probabilities. -/

open scoped Classical

namespace ExceptionalTimes.ActivePartitionLaw

noncomputable section

open DimerLaw ManyDimerLaw FiniteHaar EnvironmentVariance
open ActiveMiddlePartition MixedAnnularCollar MixedCanonicalLaw HoleFilling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance {A O : Type*} : DecidableEq (A ⊕ O) :=
  fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a = b)

local instance {B : Type*} (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a = b)

theorem partition_average_full {B : Type*} [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) (F : Configuration → ℝ) :
    average (fun x => F (pairDecode slot x)) =
      average (fun x => F (splitDecode (splitSlot slot z S) x)) :=
  (partition_average slot z S F).trans (average_smooth _)

theorem partition_wide_collar_comparison {B : Type*} [Fintype B]
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    {r s u v w t R : ℕ}
    (hrs : r ≤ s) (hsu : s ≤ u) (hut : u+1 ≤ t)
    (hrv : r ≤ v) (hvw : v ≤ w) (hwt : w+1 ≤ t) (htR : t ≤ R)
    (hfull : ∀ x ∈ annularSites r R, ∃ b, slot b = x)
    {c : ℝ} (hc : 0 < c)
    (hinner : c ≤ average (fun x => indicator (WiredArm (pairDecode slot x) r (u+1))))
    (houter : c ≤ average (fun x => indicator (WiredArm (pairDecode slot x) v R)))
    (hcircle1 : average (fun x => indicator (WiredArm (pairDecode slot x) s u)) ≤ 1-c)
    (hcircle2 : average (fun x => indicator (WiredArm (pairDecode slot x) v w)) ≤ 1-c) :
    manyProbability p (fun x => WiredArm (pairDecode slot x) r R) ≤
      mixedProbability (fun a : ActiveLabels slot z (annularSites s t) => p a.val)
        (fun x => WiredArm (splitDecode (splitSlot slot z (annularSites s t)) x) r R) / c^8 := by
  rw [partition_manyProbability slot z (annularSites s t) p (fun ω => WiredArm ω r R)]
  apply wide_radial_collar_comparison boundaryInput
    (splitSlot slot z (annularSites s t)) _ _
    (fun a => hp0 a.val) (fun a => hp1 a.val) (fun o => hp0 o.val) (fun o => hp1 o.val)
    hrs hsu hut hrv hvw hwt htR
  · apply activeCovers_split slot z hz0 _ hp
    intro x hx
    exact hfull x (annularSites_mono hrs htR hx)
  · exact split_covers slot z _ _ hfull
  · exact hc
  · rw [← partition_average_full slot z _ (fun ω => indicator (WiredArm ω r (u+1)))]
    exact hinner
  · rw [← partition_average_full slot z _ (fun ω => indicator (WiredArm ω v R))]
    exact houter
  · rw [← partition_average_full slot z _ (fun ω => indicator (WiredArm ω s u))]
    exact hcircle1
  · rw [← partition_average_full slot z _ (fun ω => indicator (WiredArm ω v w))]
    exact hcircle2

#print axioms partition_wide_collar_comparison

end

end ExceptionalTimes.ActivePartitionLaw
