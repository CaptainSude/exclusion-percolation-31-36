import ExceptionalTimes.CanonicalRadialLocal
import ExceptionalTimes.ActiveWideLaw
import ExceptionalTimes.MatchingCollarUniversal
import ExceptionalTimes.RadialPivotalArms

/-! Quantitative variance for the literal active mesoscopic cells.
The homogeneous paired four-arm power estimate is explicitly NEW and is
not asserted to follow from a published result in this module. Given that
estimate, the pivotal extraction, remote factors, actual cell partition,
and geometric shell sum are composed here rather than supplied as bounds.
-/

open scoped BigOperators Classical

namespace ExceptionalTimes.RadialMixedAbsorption

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar GroupedDimerLaw
open MixedCanonicalLaw MixedAnnularCollar MesoscopicCells MesoscopicVariance
open ActivePartitionLaw ActiveMiddlePartition HoleFilling RadialFourArmProbe PairSquareSewing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

variable {A O : Type*} [Fintype A] [Fintype O]

local instance (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) : DecidableEq (Cells m slot) :=
  fun a b => Classical.propDecidable (a=b)

local instance (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) (c : Cells m slot) :
    DecidableEq (Fiber m slot c) := fun a b => Classical.propDecidable (a=b)

local instance (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) :
    DecidableEq (Sigma (Fiber m slot)) := fun a b => Classical.propDecidable (a=b)

local instance {B : Type*} (slot : B×Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ActiveLabels slot z S) := fun a b => Classical.propDecidable (a=b)

local instance {B : Type*} (slot : B×Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    DecidableEq (ExteriorLabels slot z S) := fun a b => Classical.propDecidable (a=b)

/-- Regrouping with the same finite fiber instances as the variance sum. -/
theorem regrouped_probability (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site)
    (p : A→ℝ) (E : Configuration→Prop) :
    mixedProbability p (fun x => E (splitDecode slot x)) =
      mixedProbability (fun s => p (groupingEquiv m (activeSlot slot) s))
        (fun x => E (MixedSiteVariance.decode (groupedSlot m slot) x)) := by
  rw [MixedProbeProduct.mixedProbability_relabel
    (groupingEquiv m (activeSlot slot)) (Equiv.refl O)]
  congr 1
  funext x
  rw [grouped_decode]
  rfl

theorem regrouped_mean (m : ℕ) (slot : ((A⊕O)×Fin 2) ↪ Site) (F : Configuration→ℝ) :
    average (smooth (fun x => F (splitDecode slot x))) =
      average (smooth (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x))) := by
  have he : (fun x => F (MixedSiteVariance.decode (groupedSlot m slot) x)) =
      (fun x => F (splitDecode slot (fun a => x.1 ((groupingEquiv m (activeSlot slot)).symm a),x.2))) := by
    funext x
    rw [grouped_decode]
  rw [he]
  exact (average_equiv (Equiv.arrowCongr (groupingEquiv m (activeSlot slot)) (Equiv.refl Color))
    (fun a => average (fun o => F (splitDecode slot (a,o))))).symm

/-- The same actual variance estimate before regrouping the active labels.
The Efron--Stein premise is the existing classical finite-product theorem. -/
theorem original_grid_variance_bulk (m r : ℕ) (hm : 0<m) (hmr : m≤r)
    (slot : ((A⊕O)×Fin 2) ↪ Site) (z : Site) {d : ℕ}
    (hz : z∈latticeBox d) (hdm : d≤m)
    (hpartner : ∀ a, activeSlot slot (a,1)=PeriodicMatching.partner z (activeSlot slot (a,0)))
    (p : A→ℝ) (hp0 : ∀ a,0≤p a) (hp1 : ∀ a,p a≤1)
    (F : Configuration→Bool)
    (hES : EfronStein (fun c => FiniteLaw.pi (fun a : Fiber m slot c =>
      environmentLaw (p a.val) (hp0 a.val) (hp1 a.val))))
    (C q h : ℝ) (hC : 0≤C) (hq : 0≤q) (hh : 0<h)
    (hmin : ∀ c∈occupied m (activeSlot slot), r≤anchorRadius m (activeSlot slot) c)
    (hcost : ∀ c∈occupied m (activeSlot slot), mixedProbability p
      (fun x => CellInterpolation.CellPivotal F (dimerCell m (activeSlot slot) c)
        (splitDecode slot x)) ≤ C*q*((m : ℝ)/anchorRadius m (activeSlot slot) c)^(2+h)) :
    mixedProbability p (fun x => F (splitDecode slot x)=true) -
      (average (smooth (fun x => indicator (F (splitDecode slot x)=true))))^2 ≤
        98*C*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  rw [regrouped_probability m slot p (fun ω => F ω=true),
    regrouped_mean m slot (fun ω => indicator (F ω=true))]
  apply grid_variance_bulk m r hm hmr slot z hz hdm hpartner
    (fun s => p (groupingEquiv m (activeSlot slot) s))
    (fun s => hp0 _) (fun s => hp1 _) F hES C q h hC hq hh hmin
  intro c hc
  rw [←regrouped_probability m slot p
    (fun ω => CellInterpolation.CellPivotal F (dimerCell m (activeSlot slot) c) ω)]
  exact hcost c hc

/-- NEW and unproved: the actual homogeneous canonical probability of
the concrete circular four-arm probe has an exponent strictly above two.
The full finite matching covers the probe, so default exterior colors
are not used to assert an arm estimate. -/
def NewPairedProbeDecay {B : Type*} [Fintype B]
    (slot : B×Fin 2 ↪ Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (a C h : ℝ) : Prop :=
  ∀ x : Site, ∀ hscale : 8192*K*m≤latticeRadius x,
    (∀ v∈(probe x K m d hK hm hd hscale).region, ∃ b,slot b=v) →
      manyProbability (fun _ : B => a)
        (fun y => FourArms (probe x K m d hK hm hd hscale) (pairDecode slot y)) ≤
          C*((m : ℝ)/latticeRadius x)^(2+h)

theorem NewPairedProbeDecay.reindex {B J : Type*} [Fintype B] [Fintype J]
    {slot : B×Fin 2 ↪ Site} {K m d : ℕ} {hK : 2≤K} {hm : 0<m} {hd : d≤m}
    {a C h : ℝ} (H : NewPairedProbeDecay slot K m d hK hm hd a C h) (e : J≃B) :
    NewPairedProbeDecay (reindexSlot slot e) K m d hK hm hd a C h := by
  intro x hscale hcover
  have hc : ∀ v∈(probe x K m d hK hm hd hscale).region,∃ b,slot b=v := by
    intro v hv
    obtain ⟨⟨b,i⟩,hb⟩ := hcover v hv
    exact ⟨(e b,i),hb⟩
  have he := CanonicalRadialLaw.many_relabel e (fun _ : B => a)
    (fun y => FourArms (probe x K m d hK hm hd hscale) (pairDecode slot y))
  simpa only [pairDecode_reindex,←he] using H x hscale hc

universe u v

/-- All pivotal and remote-factor premises are discharged. The only new
probabilistic premise is the displayed homogeneous paired four-arm decay. -/
theorem uniform_mixed_variance_of_new_paired_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β) :
    ∃ K : ℕ, ∃ hK : 2≤K, ∃ δ : ℝ, 0<δ ∧
      ∀ {A : Type u} {O : Type v} [Fintype A] [Fintype O]
        (slot : ((A⊕O)×Fin 2) ↪ Site) (z : Site) (m d r R : ℕ)
        (hm : 0<m), B₀≤m → ∀ hd : d≤m, z∈latticeBox d →
        (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
        (∀ s∈annularSites r R,∃ ie,slot ie=s) →
        8192*K*m≤r → 0<r → 16*r≤R → 2*d≤r →
        (∀ cell∈occupied m (activeSlot slot),
          anchor m (activeSlot slot) cell∈annularSites (2*r-d) (R/2+d)) →
        ∀ (p : A→ℝ) (hp0 : ∀ a,0≤p a) (hp1 : ∀ a,p a≤1),
        EfronStein (fun c => FiniteLaw.pi (fun a : Fiber m slot c =>
          environmentLaw (p a.val) (hp0 a.val) (hp1 a.val))) →
        ∀ a C h : ℝ, 0≤a → a≤1 → (∀ i,a≤p i) → 0≤C → 0<h →
        NewPairedProbeDecay slot K m d hK hm hd a C h →
          let q := mixedProbability p (fun y => WiredArm (splitDecode slot y) r R)
          let α := average (smooth (fun y => indicator (WiredArm (splitDecode slot y) r R)))
          q-α^2≤98*(C/δ^6)*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  obtain ⟨K,hK,δ,hδ,hlocal⟩ :=
    CanonicalRadialLocal.uniform_pivotal_canonical_fourArms boundaryInput.graph_cut hRSW hupper hβ
  refine ⟨K,hK,δ,hδ,?_⟩
  intro A O instA instO slot z m d r R hm hBm hd hz hp hcover hscale hr hR hdr hbulk
    p hp0 hp1 hES a C h ha0 ha1 hap hC hh hdecay
  dsimp only
  have hmr : m≤r := by nlinarith
  have hmin (cell : Site) (hc : cell∈occupied m (activeSlot slot)) :
      r≤anchorRadius m (activeSlot slot) cell := by
    have hn := (Finset.mem_sdiff.mp (hbulk cell hc)).2
    by_contra! h
    apply hn
    apply mem_latticeBox_of_radius_le
    change anchorRadius m (activeSlot slot) cell≤_
    omega
  have hmax (cell : Site) (hc : cell∈occupied m (activeSlot slot)) :
      anchorRadius m (activeSlot slot) cell≤R := by
    have H := radius_le_of_mem_box (Finset.mem_sdiff.mp (hbulk cell hc)).1
    change anchorRadius m (activeSlot slot) cell≤R/2+d+1 at H
    omega
  have H := original_grid_variance_bulk m r hm hmr slot z hz hd
    (fun a => hp (.inl a)) p hp0 hp1 (wiredArmTest r R) hES
    (C/δ^6) (mixedProbability p (fun y => WiredArm (splitDecode slot y) r R)) h
    (div_nonneg hC (pow_nonneg hδ.le 6)) (mixedProbability_nonneg p hp0 hp1 _) hh hmin ?_
  · simpa only [wiredArmTest,decide_eq_true_eq] using H
  intro cell hc
  let x := anchor m (activeSlot slot) cell
  have hs : 8192*K*m≤latticeRadius x := hscale.trans (hmin cell hc)
  have hnecessary : ∀ ω,CellInterpolation.CellPivotal (wiredArmTest r R)
      (dimerCell m (activeSlot slot) cell) ω → FourArms (probe x K m d hK hm hd hs) ω := by
    intro ω hω
    exact RadialPivotalArms.cell_pivotal_fourArms boundaryInput hJordan
      (activeSlot slot) z K m d r R hK hm hd hz (fun a => hp (.inl a))
      cell hc hs hr hR hdr (hbulk cell hc) ω hω
  have hcoverP : ∀ v∈(probe x K m d hK hm hd hs).region,∃ b,slot b=v := by
    intro v hv
    have H := probe_region_avoids_boundaries x K m d r R hK hm hd hs hr hR hdr (hbulk cell hc) v hv
    exact hcover v (Finset.mem_sdiff.mpr ⟨latticeBox_mono (Nat.le_succ R) H.1,H.2⟩)
  have hprob := hlocal slot z m d r R hm hBm hd hz hp hcover cell hc hs
    (hmin cell hc) (hmax cell hc) hnecessary p hp0 hp1 a ha0 ha1 hap
  apply hprob.trans
  have hprod := mul_le_mul_of_nonneg_right (hdecay x hs hcoverP)
    (mixedProbability_nonneg p hp0 hp1 (fun y => WiredArm (splitDecode slot y) r R))
  apply (div_le_div_of_nonneg_right hprod (pow_nonneg hδ.le 6)).trans_eq
  dsimp only [x,anchorRadius]
  ring

/-- The explicit packing coefficient can be absorbed without changing
the remaining paired probability into a full canonical factor. -/
theorem absorb {q α C δ h x : ℝ} (hq : 0≤q)
    (hvariance : q-α^2≤98*(C/δ^6)*q*DyadicPacking.dyadicConstant (-h)*x^h)
    (hsmall : 98*(C/δ^6)*DyadicPacking.dyadicConstant (-h)*x^h≤1/2) : q≤2*α^2 := by
  have H := mul_le_mul_of_nonneg_right hsmall hq
  nlinarith [hvariance]

/-- Every actual active-cell anchor belongs to the required buffered
bulk band, for any selected middle annulus contained in that band. -/
theorem active_wide_anchor_margin {B : Type*} [Fintype B]
    (slot : B×Fin 2 ↪ Site) (z : Site) (hz0 : z≠(0,0))
    {d r R s t : ℕ} (hz : z∈latticeBox d) (hdr : 2*d≤r)
    (hrs : 2*r≤s) (htR : t≤R/2)
    (hp : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (m : ℕ) (cell : Site)
    (hc : cell∈occupied m (activeSlot (splitSlot slot z (annularSites s t)))) :
    anchor m (activeSlot (splitSlot slot z (annularSites s t))) cell∈
      annularSites (2*r-d) (R/2+d) := by
  have hv := anchor_mem m (activeSlot (splitSlot slot z (annularSites s t))) cell hc
  obtain ⟨⟨a,b⟩,_,he⟩ := Finset.mem_image.mp hv
  rw [←he]
  apply annularSites_mono (Nat.sub_le_sub_right hrs d) (Nat.add_le_add_right htR d)
  exact active_annular_margin slot z hz0 hz (by omega) hp a b

/-- The literal active/exterior partition is now constructed from its
middle annulus. No pivotal-cost or per-cell position assumption remains. -/
theorem uniform_active_variance_of_new_paired_decay
    (boundaryInput : WiredBoundary.PlaneClusterBoundaryCircuit)
    (hJordan : PublishedPolygonCrossingOrder)
    (hRSW : NolinCorridor.PublishedCriticalRSW) {B₀ : ℕ} {C₀ β : ℝ}
    (hupper : NolinCorridor.PublishedAnnularOneArmUpper B₀ C₀ β) (hβ : 0<β) :
    ∃ K : ℕ, ∃ hK : 2≤K, ∃ δ : ℝ, 0<δ ∧
      ∀ {B : Type u} [Fintype B] (slot : B×Fin 2 ↪ Site) (z : Site),z≠(0,0) →
      ∀ m d r R s t : ℕ, ∀ hm : 0<m, B₀≤m → ∀ hd : d≤m, z∈latticeBox d →
        (∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0))) →
        (∀ v∈annularSites r R,∃ b,slot b=v) →
        8192*K*m≤r → 0<r → 16*r≤R → 2*d≤r → 2*r≤s → t≤R/2 →
        ∀ (p : B→ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1),
          let sl := splitSlot slot z (annularSites s t)
          let pa := fun a : ActiveLabels slot z (annularSites s t) => p a.val
          let hp0a := fun a : ActiveLabels slot z (annularSites s t) => hp0 a.val
          let hp1a := fun a : ActiveLabels slot z (annularSites s t) => hp1 a.val
          EfronStein (fun c => FiniteLaw.pi (fun a : Fiber m sl c =>
            environmentLaw (pa a.val) (hp0a a.val) (hp1a a.val))) →
          ∀ a C h : ℝ,0≤a → a≤1 → (∀ i,a≤p i) → 0≤C → 0<h →
          NewPairedProbeDecay slot K m d hK hm hd a C h →
            let q := mixedProbability pa (fun y => WiredArm (splitDecode sl y) r R)
            let α := average (fun y => indicator (WiredArm (pairDecode slot y) r R))
            q-α^2≤98*(C/δ^6)*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  obtain ⟨K,hK,δ,hδ,hmain⟩ :=
    uniform_mixed_variance_of_new_paired_decay boundaryInput hJordan hRSW hupper hβ
  refine ⟨K,hK,δ,hδ,?_⟩
  intro B instB slot z hz0 m d r R s t hm hBm hd hz hp hcover hscale hr hR hdr hrs htR p hp0 hp1
  dsimp only
  intro hES a C h ha0 ha1 hap hC hh hdecay
  rw [partition_average slot z (annularSites s t) (fun ω => indicator (WiredArm ω r R))]
  apply hmain (splitSlot slot z (annularSites s t)) z m d r R hm hBm hd hz
    (splitSlot_partner slot z _ hp) (split_covers slot z _ _ hcover)
    hscale hr hR hdr (active_wide_anchor_margin slot z hz0 hz hdr hrs htR hp m)
    (fun a => p a.val) (fun a => hp0 a.val) (fun a => hp1 a.val) hES a C h
    ha0 ha1 (fun a => hap a.val) hC hh
  exact hdecay.reindex (splitEquiv slot z (annularSites s t))

#print axioms original_grid_variance_bulk
#print axioms uniform_mixed_variance_of_new_paired_decay
#print axioms absorb
#print axioms NewPairedProbeDecay.reindex
#print axioms active_wide_anchor_margin
#print axioms uniform_active_variance_of_new_paired_decay

end

end ExceptionalTimes.RadialMixedAbsorption
