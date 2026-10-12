import ExceptionalTimes.ActualProductTransfer
import ExceptionalTimes.WordProductBridge

/-! The exact finite-word certificate needed by the concrete dimension
proof. Its fields are new obligations, not literature assumptions. The
following implication assembles the checked semigroup and probability steps. -/
open Filter
open scoped Classical Topology
namespace ExceptionalTimes.WordForestCertificate
noncomputable section
open PairSquareSewing StaticHexApproximation QuadAnnulusTransfer
open DimerExpansion SelectedPerturbation EffectiveDimerInsertion ActualProductTransfer
open WordProductBridge LocalDimerCalibration AnnulusTransferMixing

/-- Concrete forest and sewing data. A completed proof must construct this
from the named ordinary source inputs; assuming this record does not solve
any new percolation comparison. -/
structure Data (hplane : PublishedInvarianceOfDomain) {q : ℕ}
    (T : DyadicQuadFamily (Fin q)) (word : (Fin q→Bool)→Bool) where
  sites : ℕ→Finset Site
  support : ∀ᶠ n in atTop,polygonFamilySupport (quads hplane T n)⊆sites n
  G : ∀ phase : Bool,∀ n,Finset (UnitReferenceCover.anchors phase (sites n))→ℝ
  A : ℝ
  β : ℝ
  A_nonneg : 0≤A
  β_pos : 0<β
  geometry : ∀ phase : Bool,∀ᶠ n in atTop,
    GeometryBound (fun _ => baseLaw) (wordTest T word (sites n) phase n) (G phase n) ∧
      ∀ S,0≤G phase n S
  mass : ∀ phase : Bool,∀ rule : Rule,∀ᶠ n in atTop,∀ k,
    (localScale rule n)^k*geometryDegree (G phase n) k≤A^k*(k:ℝ)^(-β*k)
  degree : ∀ phase : Bool,∀ k,Tendsto (fun n =>
    scaledCoefficient .canonical (wordTest T word (sites n) phase n) (localScale .canonical n) k-
    scaledCoefficient .refresh (wordTest T word (sites n) phase n) (localScale .refresh n) k)
    atTop (𝓝 0)

theorem transfer_of_data (hplane : PublishedInvarianceOfDomain)
    (hclock : ∀ r,NewClockControl (localClock r))
    (hdata : ∀ q : ℕ,∀ T : DyadicQuadFamily (Fin q),∀ word : (Fin q→Bool)→Bool,
      Nonempty (Data hplane T word)) : NewFiniteWordTransfer hplane := by
  apply word_transfer_of_kernel_limits hplane hclock
  intro q T word τ hτ
  let d := Classical.choice (hdata q T word)
  refine ⟨d.sites,d.support,?_⟩
  intro phase
  exact actual_product_transfer_of_forest
    (fun n => wordTest T word (d.sites n) phase n) (d.G phase) localScale
    d.A_nonneg d.β_pos (d.geometry phase)
    (fun r => localScale_positive r (hclock r))
    (fun r => ClockVanishing.local_scale_tendsto_zero r (hclock r))
    (d.mass phase) (d.degree phase) hτ

#print axioms transfer_of_data
end
end ExceptionalTimes.WordForestCertificate
