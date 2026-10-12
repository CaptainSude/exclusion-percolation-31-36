import ExceptionalTimes.DyadicDenseFamily
import ExceptionalTimes.IndependentAnnulusInput

/-! Literal finite-word approximation of a fixed hexagonal arm event.
The approximation input is the conventional static consequence of GPS
1008.1378v5 Lemma 2.9 and the dense dyadic quad family. It is not a
canonical dynamical comparison. Every finite sample and test is explicit. -/

open scoped Classical

namespace ExceptionalTimes.StaticHexApproximation

open PairSquareSewing CanonicalHexAnnuli EnvironmentVariance ProbeProduct
open IndependentAnnulusInput

noncomputable section

def quads {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (n : ℕ) : Fin q→PolygonQuad :=
  fun i => (T.grid i).meshPolygon hplane n

def sample {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (M n : ℕ) (T : DyadicQuadFamily (Fin q)) : Finset Site :=
  latticeBox (M*2^n) ∪ polygonFamilySupport (quads hplane T n)

def wordEvent {q : ℕ} (T : DyadicQuadFamily (Fin q)) (n : ℕ)
    (word : (Fin q→Bool)→Bool) (ω : Configuration) : Prop :=
  word (fun i => T.test n i ω)=true

def armEvent (M n : ℕ) : Configuration→Prop :=
  HexFourArms 0 ((2^n : ℕ) : ℤ) ((M*2^n : ℕ) : ℤ)

theorem region_subset_box (r : ℤ) (R : ℕ) :
    region 0 r (R : ℤ) ⊆ (latticeBox R : Set Site) := by
  intro v hv
  have hh : Annulus.hexRadius v≤(R : ℤ) := by simpa [region] using hv.2
  have hx : |v.1|≤(R : ℤ) :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hh
  have hy : |v.2|≤(R : ℤ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hh
  simpa only [latticeBox,Finset.mem_coe,Finset.product_eq_sprod,
    Finset.mem_product,Finset.mem_Icc] using And.intro (abs_le.mp hx) (abs_le.mp hy)

theorem arm_local (M n : ℕ) {ω η : Configuration}
    (h : Set.EqOn ω η (latticeBox (M*2^n))) : armEvent M n ω ↔ armEvent M n η :=
  HexFourArms.congr (fun _ hv => h (region_subset_box _ _ hv))

theorem word_local {q : ℕ} (hplane : PublishedInvarianceOfDomain)
    (T : DyadicQuadFamily (Fin q)) (n : ℕ) (hn : T.maxLevel≤n)
    (word : (Fin q→Bool)→Bool) {ω η : Configuration}
    (h : Set.EqOn ω η (polygonFamilySupport (quads hplane T n))) :
    wordEvent T n word ω ↔ wordEvent T n word η := by
  have he : (fun i => T.test n i ω)=(fun i => T.test n i η) := by
    simp_rw [T.test_eq hplane n hn]
    exact polygon_test_vector_congr (quads hplane T n) h
  simp only [wordEvent,he]

def PublishedHexQuadApproximation (hplane : PublishedInvarianceOfDomain) : Prop :=
  ∀ M : ℕ,2≤M → ∀ δ : ℝ,0<δ →
    ∃ q : ℕ,∃ T : DyadicQuadFamily (Fin q),∃ word : (Fin q→Bool)→Bool,
      ∃ N : ℕ,T.maxLevel≤N ∧ ∀ n,N≤n →
        probability (fairSites (sample hplane M n T))
          (fun ω => ¬(armEvent M n (complete ω) ↔ wordEvent T n word (complete ω)))≤δ

#print axioms region_subset_box
#print axioms word_local

end
end ExceptionalTimes.StaticHexApproximation
