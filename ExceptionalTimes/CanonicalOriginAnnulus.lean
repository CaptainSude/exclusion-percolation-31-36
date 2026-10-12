import ExceptionalTimes.CanonicalSpatialProduct
import ExceptionalTimes.RadialDimerSeparation
import ExceptionalTimes.ActivePartitionLaw
import ExceptionalTimes.CanonicalRadialEnergy
import ExceptionalTimes.FiniteSiteLaw

/-! A literal origin one-arm event is bounded by an independent inner
one-arm event and outer wired annular event. Independence is derived from
whole-dimer separation, and the inner factor uses only its static marginal.
No new percolation probability estimate is assumed for this separation. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.CanonicalOriginAnnulus

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar ActivePartitionLaw
open RadialDimerSeparation CanonicalSpatialProduct CanonicalRadialLaw HoleFilling
open TimeClosure ProbeProduct

variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]

theorem many_sites_local_product (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (slot : B×Fin 2 ↪ Site) (S : I→Set Site)
    (hdis : Pairwise (fun i j => Disjoint (touching slot (S i)) (touching slot (S j))))
    (E : I→Configuration→Prop)
    (hlocal : ∀ i ω η,Set.EqOn ω η (S i) → (E i ω↔E i η)) :
    manyProbability p (fun x => ∀ i,E i (pairDecode slot x)) =
      ∏ i,manyProbability p (fun x => E i (pairDecode slot x)) := by
  simp_rw [manyProbability_eq_joint p hp0 hp1]
  let F : I→((B→Color)×(B→Color))→Prop := fun i x =>
    E i (pairDecode slot x.1) ∧ E i (pairDecode slot x.2)
  have heq {S : Set Site} (x y : B→Color)
      (he : ∀ b∈touching slot S,x b=y b) :
      Set.EqOn (pairDecode slot x) (pairDecode slot y) S := by
    intro v hv
    by_cases hex : ∃ bi,slot bi=v
    · obtain ⟨⟨b,j⟩,rfl⟩ := hex
      simpa only [pairDecode,slot.injective.extend_apply]
        using congrFun (he b ⟨j,hv⟩) j
    · simp only [pairDecode,Function.extend_apply' _ _ _ hex]
  have h := manyLaw_local_product p hp0 hp1 (fun i => touching slot (S i)) hdis F
    (by
      intro i x y he
      exact and_congr (hlocal i _ _ (heq _ _ (fun b hb => (he b hb).1)))
        (hlocal i _ _ (heq _ _ (fun b hb => (he b hb).2))))
  convert h using 1
  apply probability_congr
  intro x
  exact forall_and.symm

theorem oneArm_implies_wiredArm {ω : Configuration} {r R : ℕ} (hrR : r≤R)
    (h : OneArm ω (0,0) R) : WiredArm ω r R := by
  apply (oneArm_fillBox_iff_wiredArm ω hrR).mp
  apply oneArm_colors_mono (0,0) R ?_ h
  intro v hv
  by_cases hin : v∈latticeBox r <;> simp [fillBox,hin,hv]

theorem oneArm_inner_outer_product (slot : B×Fin 2 ↪ Site) (z : Site) {d s r R : ℕ}
    (hz : z∈latticeBox d)
    (hp : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (hgap : s+1+d≤r) (hrR : r≤R)
    (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1) :
    manyProbability p (fun x => OneArm (pairDecode slot x) (0,0) R) ≤
      average (fun x => indicator (OneArm (pairDecode slot x) (0,0) s)) *
        manyProbability p (fun x => WiredArm (pairDecode slot x) r R) := by
  let S : Fin 2→Set Site := ![(latticeBox (s+1) : Set Site),(latticeBox r : Set Site)ᶜ]
  let E : Fin 2→Configuration→Prop := ![fun ω => OneArm ω (0,0) s,fun ω => WiredArm ω r R]
  have hsep : Disjoint (touching slot (S 0)) (touching slot (S 1)) := by
    apply touching_disjoint slot z hz hp
    intro v hv w hw hdiff
    have hh := MesoscopicCells.sub_mem_box hv hdiff
    have he : v-(v-w)=w := by abel
    rw [he] at hh
    exact hw (latticeBox_mono hgap hh)
  have hdis : Pairwise (fun i j => Disjoint (touching slot (S i)) (touching slot (S j))) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hsep
    · exact hsep.symm
    · exact (hij rfl).elim
  have hlocal : ∀ i ω η,Set.EqOn ω η (S i) → (E i ω↔E i η) := by
    intro i ω η he
    fin_cases i
    · exact oneArm_congr_of_eqOn_box (origin_mem_box s) (fun v hv => he hv)
    · exact wiredArm_congr_on_annulus ω η hrR (fun v _ hv => he hv)
  have hprod := many_sites_local_product p hp0 hp1 slot S hdis E hlocal
  have hprod' : manyProbability p (fun x =>
      OneArm (pairDecode slot x) (0,0) s ∧ WiredArm (pairDecode slot x) r R) =
        manyProbability p (fun x => OneArm (pairDecode slot x) (0,0) s)*
          manyProbability p (fun x => WiredArm (pairDecode slot x) r R) := by
    simpa [E,Fin.prod_univ_succ,Fin.forall_fin_succ] using hprod
  have hnecess := many_mono p hp0 hp1 (fun x (h : OneArm (pairDecode slot x) (0,0) R) =>
    And.intro (oneArm_radius_mono (by omega : s≤R) h) (oneArm_implies_wiredArm hrR h))
  rw [hprod'] at hnecess
  exact hnecess.trans (mul_le_mul_of_nonneg_right
    (many_le_marginal p hp0 hp1 _) (many_nonneg p hp0 hp1 _))

theorem mean_oneArm_eq_finiteFair (slot : B×Fin 2 ↪ Site) (R : ℕ)
    (hcover : ∀ v∈latticeBox (R+1),∃ b,slot b=v) :
    average (fun x => indicator (OneArm (pairDecode slot x) (0,0) R)) =
      (ConcreteCanonicalDriver.finiteFairOneArm R).toReal := by
  rw [FiniteSiteLaw.average_pairDecode_fairSites slot (latticeBox (R+1)) hcover
    (fun ω => OneArm ω (0,0) R)
    (fun _ _ h => oneArm_congr_of_eqOn_box (origin_mem_box R) h)]
  change _ = (ENNReal.ofReal _).toReal
  rw [ENNReal.toReal_ofReal (EnvironmentVariance.probability_nonneg _ _)]
  rfl

#print axioms many_sites_local_product
#print axioms oneArm_inner_outer_product
#print axioms mean_oneArm_eq_finiteFair

end ExceptionalTimes.CanonicalOriginAnnulus
