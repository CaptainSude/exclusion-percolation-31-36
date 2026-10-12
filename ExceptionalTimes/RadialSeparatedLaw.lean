import ExceptionalTimes.RadialDimerSeparation
import ExceptionalTimes.MixedSpatialProduct
import ExceptionalTimes.ClippedGapLaw
import ExceptionalTimes.MesoscopicVariance

/-! Exact three-region factorization for a local test and its two remote
radial connections. All spatial independence is derived from whole-dimer
separation; no independence between the two observation times is used. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.RadialSeparatedLaw

open DimerLaw EnvironmentVariance MixedCanonicalLaw MixedAnnularCollar
open RadialDimerSeparation MixedSpatialProduct ClippedRadialGap HoleFilling

variable {A O : Type*} [Fintype A] [Fintype O]

theorem mixed_three_regions (slot : ((A⊕O)×Fin 2) ↪ Site)
    (z : Site) {d : ℕ} (hz : z∈latticeBox d)
    (hpartner : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (p : A→ℝ) (hp0 : ∀ a, 0≤p a) (hp1 : ∀ a, p a≤1)
    (x : Site) {r c a b D R q : ℕ} (hca : c≤a) (hbD : b≤D)
    (hin : a+1+q+d<latticeRadius x)
    (hout : latticeRadius x+q+d≤b) (hfar : a+1+d≤b)
    (E : Configuration→Prop)
    (hE : ∀ ω η, (∀ v, v-x∈latticeBox q → ω v=η v) → (E ω↔E η)) :
    mixedProbability p (fun y => InnerRemote (splitDecode slot y) r c a ∧
      E (splitDecode slot y) ∧ OuterRemote (splitDecode slot y) b D R) =
      mixedProbability p (fun y => InnerRemote (splitDecode slot y) r c a) *
        mixedProbability p (fun y => E (splitDecode slot y)) *
          mixedProbability p (fun y => OuterRemote (splitDecode slot y) b D R) := by
  let events : Fin 3→Configuration→Prop :=
    ![fun ω => InnerRemote ω r c a,E,fun ω => OuterRemote ω b D R]
  have hdis : Pairwise (fun i j => Disjoint
      (siteLabels slot (regions x a q b i)) (siteLabels slot (regions x a q b j))) := by
    intro i j hij
    exact touching_disjoint slot z hz hpartner _ _ (region_separation x hin hout hfar i j hij)
  have hlocal : ∀ i ω η, Set.EqOn ω η (regions x a q b i) → (events i ω↔events i η) := by
    intro i ω η he
    fin_cases i
    · change InnerRemote ω r c a↔InnerRemote η r c a
      apply forall_congr'
      intro hrc
      apply wiredArm_congr_on_annulus ω η (hrc.trans hca)
      intro v hv _
      exact he hv
    · exact hE ω η (fun v hv => he hv)
    · change OuterRemote ω b D R↔OuterRemote η b D R
      apply forall_congr'
      intro hDR
      apply wiredArm_congr_on_annulus ω η (hbD.trans hDR)
      intro v _ hv
      exact he hv
  have h := mixed_sites_local_product p hp0 hp1 slot (regions x a q b) hdis events hlocal
  simpa [events,Fin.prod_univ_succ,Fin.forall_fin_succ,mul_assoc] using h

#print axioms mixed_three_regions

universe u v

/-- The two remote factors cost one uniform constant times the original
paired radial probability. The chosen radii apply in every endpoint
regime, and the constants precede all finite dimer label types. -/
theorem uniform_position_remote_comparison
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, 2≤K ∧ ∃ δ : ℝ, 0<δ ∧
      ∀ m ρ r R : ℕ, 0<m → B₀≤m → 32*K*m≤ρ → r≤ρ → ρ≤R →
        ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
          (slot : ((A⊕O)×Fin 2) ↪ Site),
          (∀ s∈annularSites r R, ∃ ie, slot ie=s) →
          ∀ p : A→ℝ, (∀ i, 0≤p i) → (∀ i, p i≤1) →
            let n := RadialGapRadii.innerScale K ρ
            mixedProbability p (fun x => InnerRemote (splitDecode slot x) r n (K*n+1))*
              mixedProbability p (fun x => OuterRemote (splitDecode slot x) ((8*K)*n) (K*(8*K)*n+1) R) ≤
                mixedProbability p (fun x => WiredArm (splitDecode slot x) r R)/δ^6 := by
  obtain ⟨K,hK,hJ⟩ := ClippedGapLaw.exists_uniform_clipped_mixed_gap boundaryInput hRSW hupper hβ
  obtain ⟨δ,hδ,hgap⟩ := hJ (8*K) (by omega)
  refine ⟨K,hK,δ,hδ,?_⟩
  intro m ρ r R hm hBm hscale hr hR A O instA instO slot hcover p hp0 hp1
  let n := RadialGapRadii.innerScale K ρ
  obtain ⟨hn,hin,hout⟩ := RadialGapRadii.chosen_radii hK hm (Nat.zero_le m) hscale
  apply hgap n r R (by omega) (by omega) (hr.trans hR) _ _ slot hcover p hp0 hp1
  · exact hr.trans (by change ρ+2*(m+0)≤(8*K)*n at hout; omega)
  · change K*n+2+2*(m+0)<ρ at hin
    omega

#print axioms uniform_position_remote_comparison

/-- Reduction of the actual cell pivotal probability to a single local
test. Its local necessity remains an explicit geometric premise; this
theorem does not assert a four-arm extraction or its two-time decay. -/
theorem uniform_pivotal_local_reduction
    (boundaryInput : WiredBoundary.FiniteClusterBoundaryCircuit)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C β) (hβ : 0<β) :
    ∃ K : ℕ, 2≤K ∧ ∃ δ : ℝ, 0<δ ∧
      ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
        (slot : ((A⊕O)×Fin 2) ↪ Site) (z : Site) (m d r R : ℕ),
        0<m → B₀≤m → d≤m → z∈latticeBox d →
        (∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
        (∀ s∈annularSites r R, ∃ ie, slot ie=s) →
        ∀ cell∈MesoscopicCells.occupied m (MesoscopicVariance.activeSlot slot),
          let x := MesoscopicCells.anchor m (MesoscopicVariance.activeSlot slot) cell
          let ρ := MesoscopicCells.anchorRadius m (MesoscopicVariance.activeSlot slot) cell
          let n := RadialGapRadii.innerScale K ρ
          32*K*m≤ρ → r≤ρ → ρ≤R →
          ∀ E : Configuration→Prop,
            (∀ ω η, (∀ s, s-x∈latticeBox (K*n) → ω s=η s) → (E ω↔E η)) →
            (∀ ω, CellInterpolation.CellPivotal (wiredArmTest r R)
              (MesoscopicCells.dimerCell m (MesoscopicVariance.activeSlot slot) cell) ω → E ω) →
            ∀ p : A→ℝ, (∀ i, 0≤p i) → (∀ i, p i≤1) →
              mixedProbability p (fun y => CellInterpolation.CellPivotal (wiredArmTest r R)
                (MesoscopicCells.dimerCell m (MesoscopicVariance.activeSlot slot) cell) (splitDecode slot y)) ≤
                mixedProbability p (fun y => E (splitDecode slot y)) *
                  mixedProbability p (fun y => WiredArm (splitDecode slot y) r R)/δ^6 := by
  obtain ⟨K,hK,δ,hδ,hremote⟩ := uniform_position_remote_comparison boundaryInput hRSW hupper hβ
  refine ⟨K,hK,δ,hδ,?_⟩
  intro A O instA instO slot z m d r R hm hBm hdm hz hpartner hcover cell hcell
  dsimp only
  intro hscale hr hR E hE hnecessary p hp0 hp1
  let slots := MesoscopicVariance.activeSlot slot
  let x := MesoscopicCells.anchor m slots cell
  let ρ := MesoscopicCells.anchorRadius m slots cell
  let n := RadialGapRadii.innerScale K ρ
  have hca : n≤K*n+1 := (Nat.le_mul_of_pos_left n (by omega)).trans (Nat.le_succ _)
  have hbD : (8*K)*n≤K*(8*K)*n+1 := by
    have h := Nat.le_mul_of_pos_left ((8*K)*n) (by omega : 0<K)
    nlinarith
  obtain ⟨hin,hout,hfar⟩ := chosen_support_radii hK hm hdm hscale
  have hprod := mixed_three_regions slot z hz hpartner p hp0 hp1 x (r := r) (R := R) hca hbD hin hout hfar E hE
  have hmono := MixedCanonicalLaw.mixedProbability_mono p hp0 hp1
    (fun y => CellInterpolation.CellPivotal (wiredArmTest r R) (MesoscopicCells.dimerCell m slots cell) (splitDecode slot y))
    (fun y => InnerRemote (splitDecode slot y) r n (K*n+1) ∧
      E (splitDecode slot y) ∧ OuterRemote (splitDecode slot y) ((8*K)*n) (K*(8*K)*n+1) R)
    (by
      intro y hy
      have hh := RadialGapRadii.dimer_cell_optional_remote m K hm hK slots z hz hdm
        (fun a => hpartner (.inl a)) cell hcell (splitDecode slot y) (hr.trans hR) hscale hr hR hy
      exact ⟨hh.1,hnecessary _ hy,hh.2⟩)
  rw [hprod] at hmono
  have hg := hremote m ρ r R hm hBm hscale hr hR slot hcover p hp0 hp1
  have hmul := mul_le_mul_of_nonneg_left hg
    (MixedCanonicalLaw.mixedProbability_nonneg p hp0 hp1 (fun y => E (splitDecode slot y)))
  have hcomm :
      mixedProbability p (fun y => InnerRemote (splitDecode slot y) r n (K*n+1)) *
        mixedProbability p (fun y => E (splitDecode slot y)) *
          mixedProbability p (fun y => OuterRemote (splitDecode slot y) ((8*K)*n) (K*(8*K)*n+1) R) =
      mixedProbability p (fun y => E (splitDecode slot y)) *
        (mixedProbability p (fun y => InnerRemote (splitDecode slot y) r n (K*n+1)) *
          mixedProbability p (fun y => OuterRemote (splitDecode slot y) ((8*K)*n) (K*(8*K)*n+1) R)) := by ring
  rw [hcomm] at hmono
  exact hmono.trans (by simpa only [mul_div_assoc] using hmul)

#print axioms uniform_pivotal_local_reduction

end ExceptionalTimes.RadialSeparatedLaw

