import ExceptionalTimes.MesoscopicCells
import ExceptionalTimes.MixedSiteVariance
import ExceptionalTimes.MixedCanonicalEvents

/-! The concrete square-grid grouping in the active-only variance bound.
The weighted cell count and all shell bookkeeping are proved internally.
Only the individual pivotal probability estimate remains an input. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MesoscopicVariance

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar GroupedDimerLaw
open MixedCanonicalLaw MesoscopicCells

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A O : Type*} [Fintype A] [Fintype O]

def activeSlot (slot : ((A ⊕ O) × Fin 2) ↪ Site) : A × Fin 2 ↪ Site :=
  ⟨fun b => slot (.inl b.1,b.2), by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have he := Prod.mk.inj (slot.injective h)
    exact Prod.ext (Sum.inl.inj he.1) he.2⟩

abbrev Cells (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) :=
  CellLabels m (activeSlot slot)

abbrev Fiber (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) (c : Cells m slot) :=
  {a : A // group m (activeSlot slot) a = c}

local instance (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) :
    DecidableEq (Cells m slot) := fun a b => Classical.propDecidable (a = b)

local instance (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) (c : Cells m slot) :
    DecidableEq (Fiber m slot c) := fun a b => Classical.propDecidable (a = b)

local instance (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) :
    DecidableEq (Sigma (Fiber m slot)) := fun a b => Classical.propDecidable (a = b)

def groupedSlot (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) :
    ((Sigma (Fiber m slot) ⊕ O) × Fin 2) ↪ Site :=
  ((Equiv.sumCongr (groupingEquiv m (activeSlot slot)) (Equiv.refl O)).prodCongr
    (Equiv.refl (Fin 2))).toEmbedding.trans slot

omit [Fintype O] in
theorem groupedSlot_inl (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (c : Cells m slot) (a : Fiber m slot c) (b : Fin 2) :
    groupedSlot m slot (.inl ⟨c,a⟩,b) = activeSlot slot (a.val,b) := rfl

omit [Fintype O] in
theorem cellSites_eq (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site) (c : Cells m slot) :
    MixedSiteVariance.cellSites (groupedSlot m slot) c =
      dimerCell m (activeSlot slot) c.val := by
  ext v
  simp only [MixedSiteVariance.cellSites,dimerCell,Finset.mem_image,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨a,b⟩,rfl⟩
    exact ⟨(a.val,b),congrArg Subtype.val a.property,rfl⟩
  · rintro ⟨⟨a,b⟩,ha,rfl⟩
    exact ⟨(⟨a,Subtype.ext ha⟩,b),rfl⟩

/-- Actual active mesocell variance, with the finite sum indexed by the
occupied integer grid cells rather than a supplied grouping. -/
theorem grid_variance (m : ℕ) (slot : ((A ⊕ O) × Fin 2) ↪ Site)
    (p : Sigma (Fiber m slot) → ℝ)
    (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun c => FiniteLaw.pi
      (fun a => environmentLaw (p ⟨c,a⟩) (hp0 ⟨c,a⟩) (hp1 ⟨c,a⟩)))) :
    mixedProbability p (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x) = true) -
      (average (smooth (fun x => indicator
        (F (MixedSiteVariance.decode (groupedSlot m slot) x) = true))))^2 ≤
      (1/2 : ℝ) * ∑ c ∈ occupied m (activeSlot slot), mixedProbability p
        (fun x => CellInterpolation.CellPivotal F
          (dimerCell m (activeSlot slot) c) (MixedSiteVariance.decode (groupedSlot m slot) x)) := by
  have h := MixedSiteVariance.mixed_site_variance
    (I := Cells m slot) (O := O) (J := Fiber m slot)
    (groupedSlot m slot) p hp0 hp1 F hES
  simp only [cellSites_eq] at h
  let cost : Site → ℝ := fun c => mixedProbability p
    (fun x => CellInterpolation.CellPivotal F (dimerCell m (activeSlot slot) c)
      (MixedSiteVariance.decode (groupedSlot m slot) x))
  have hs : (∑ c : Cells m slot, cost c) = ∑ c ∈ occupied m (activeSlot slot), cost c := by
    exact Finset.sum_attach _ cost
  change _ ≤ (1/2 : ℝ) * ∑ c : Cells m slot, cost c at h
  rw [hs] at h
  exact h

/-- The complete finite-grid bulk estimate. Each cell contributes once;
the coefficient comes from the proved square-grid count and geometric
series, with no probabilistic arm estimate hidden in the statement. -/
theorem grid_variance_bulk (m r : ℕ) (hm : 0 < m) (hmr : m ≤ r)
    (slot : ((A ⊕ O) × Fin 2) ↪ Site) (z : Site) {d : ℕ}
    (hz : z ∈ latticeBox d) (hdm : d ≤ m)
    (hpartner : ∀ a, activeSlot slot (a,1) =
      PeriodicMatching.partner z (activeSlot slot (a,0)))
    (p : Sigma (Fiber m slot) → ℝ)
    (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun c => FiniteLaw.pi
      (fun a => environmentLaw (p ⟨c,a⟩) (hp0 ⟨c,a⟩) (hp1 ⟨c,a⟩))))
    (K q h : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hh : 0 < h)
    (hmin : ∀ c ∈ occupied m (activeSlot slot), r ≤ anchorRadius m (activeSlot slot) c)
    (hcost : ∀ c ∈ occupied m (activeSlot slot), mixedProbability p
      (fun x => CellInterpolation.CellPivotal F (dimerCell m (activeSlot slot) c)
        (MixedSiteVariance.decode (groupedSlot m slot) x)) ≤
      K*q*((m : ℝ)/anchorRadius m (activeSlot slot) c)^(2+h)) :
    mixedProbability p (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x) = true) -
      (average (smooth (fun x => indicator
        (F (MixedSiteVariance.decode (groupedSlot m slot) x) = true))))^2 ≤
      98*K*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  apply (grid_variance m slot p hp0 hp1 F hES).trans
  have hsum := all_bulk_cell_sum m r hm hmr (activeSlot slot) z hz hdm hpartner
    (occupied m (activeSlot slot)) (fun _ hc => hc)
    (fun c => mixedProbability p (fun x => CellInterpolation.CellPivotal F
      (dimerCell m (activeSlot slot) c) (MixedSiteVariance.decode (groupedSlot m slot) x)))
    K q h hK hq hh hmin (fun _ _ => mixedProbability_nonneg p hp0 hp1 _) hcost
  nlinarith only [hsum]

#print axioms cellSites_eq
#print axioms grid_variance
#print axioms grid_variance_bulk

end

end ExceptionalTimes.MesoscopicVariance
