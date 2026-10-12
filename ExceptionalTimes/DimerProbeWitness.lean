import ExceptionalTimes.FullLifeProbe

/-! Literal selected-dimer overwrites and the probes of their actual
root-contracted forest. Histories outside the selected dimers are arbitrary;
no independence between test times is used for the necessary-event map. -/

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open CenteredBlocks ForestArmProbability

variable {I J : Type*}

noncomputable def overwriteDimers (endpoint : I × Fin 2 ↪ Site)
    (ω : Configuration) (color : I → CenteredBlocks.PairColor) : Configuration :=
  Function.extend endpoint (fun ie => color ie.1 ie.2) ω

theorem overwriteDimers_endpoint (endpoint : I × Fin 2 ↪ Site) (ω : Configuration)
    (color : I → CenteredBlocks.PairColor) (ie : I × Fin 2) :
    overwriteDimers endpoint ω color (endpoint ie)=color ie.1 ie.2 :=
  endpoint.injective.extend_apply _ _ _

theorem overwriteDimers_outside (endpoint : I × Fin 2 ↪ Site) (ω : Configuration)
    (color : I → CenteredBlocks.PairColor) {v : Site} (h : v ∉ Set.range endpoint) :
    overwriteDimers endpoint ω color v=ω v := Function.extend_apply' _ _ _ h

theorem overwriteDimers_flip_other (endpoint : I × Fin 2 ↪ Site) (ω : Configuration)
    (color : I → CenteredBlocks.PairColor) (i : I) (e : Fin 2) {v : Site}
    (hv : v≠endpoint (i,e)) :
    overwriteDimers endpoint ω (Function.update color i (Function.update (color i) e (!(color i e)))) v=
      overwriteDimers endpoint ω color v := by
  by_cases hm : v ∈ Set.range endpoint
  · obtain ⟨⟨j,f⟩,rfl⟩ := hm
    rw [overwriteDimers_endpoint,overwriteDimers_endpoint]
    by_cases hj : j=i
    · subst j
      have hf : f≠e := fun h => hv (by rw [h])
      simp [hf]
    · simp [hj]
  · rw [overwriteDimers_outside endpoint ω _ hm,overwriteDimers_outside endpoint ω _ hm]

/-- Geometry for arbitrary disjoint two-site blocks. The endpoints need not
be lattice neighbors; margin records their physical displacement. -/
structure DimerGeometry (I J : Type*) where
  mesh : ℝ
  margin : ℝ
  mesh_pos : 0<mesh
  mesh_le_margin : mesh≤margin
  endpoint : I × Fin 2 ↪ Site
  root : J → ℂ
  endpoint_bound : ∀ i e,
    dist (position mesh (endpoint (i,0))) (position mesh (endpoint (i,e)))≤margin

theorem DimerGeometry.margin_nonneg (G : DimerGeometry I J) : 0≤G.margin :=
  G.mesh_pos.le.trans G.mesh_le_margin

/-- Every fixed lattice displacement has the required geometry. There is
no adjacency premise. An embedding of the endpoints carries disjointness. -/
noncomputable def displacedDimerGeometry (mesh : ℝ) (hmesh : 0<mesh)
    (z : Site) (endpoint : I × Fin 2 ↪ Site)
    (hdisplacement : ∀ i, endpoint (i,1)=endpoint (i,0)+z) (root : J → ℂ) :
    DimerGeometry I J where
  mesh := mesh
  margin := max mesh (mesh*‖triangularEmbedding z‖)
  mesh_pos := hmesh
  mesh_le_margin := le_max_left _ _
  endpoint := endpoint
  root := root
  endpoint_bound := by
    intro i e
    fin_cases e
    · change dist (position mesh (endpoint (i,0))) (position mesh (endpoint (i,0)))≤_
      rw [dist_self]
      exact hmesh.le.trans (le_max_left _ _)
    · change dist (position mesh (endpoint (i,0))) (position mesh (endpoint (i,1)))≤_
      rw [hdisplacement,dist_comm,pair_radius,abs_of_pos hmesh]
      exact le_max_right _ _

def selectedRoot (v : I ⊕ J) : Prop := ∃ j, v=Sum.inr j

variable [Fintype I] [Fintype J]

noncomputable def dimerAnchor (G : DimerGeometry I J) : I ⊕ J → ℂ :=
  Sum.elim (fun i => position G.mesh (G.endpoint (i,0))) G.root

abbrev DimerLife (G : DimerGeometry I J)
    (cutoff stop : ℝ) := Life selectedRoot (dimerAnchor G) cutoff stop

theorem center_is_selected (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) :
    ∃ i : I, center selectedRoot (dimerAnchor G) cutoff stop a=Sum.inl i := by
  have hc := center_mem selectedRoot (dimerAnchor G) cutoff stop a
  have hr := (ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop a.property).2.1
  cases he : center selectedRoot (dimerAnchor G) cutoff stop a with
  | inl i => exact ⟨i,rfl⟩
  | inr j => exact (hr _ hc ⟨j,he⟩).elim

noncomputable def lifeBlock (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) : I :=
  (center_is_selected G cutoff stop a).choose

theorem lifeBlock_center (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) :
    center selectedRoot (dimerAnchor G) cutoff stop a=
      Sum.inl (lifeBlock G cutoff stop a) :=
  (center_is_selected G cutoff stop a).choose_spec

noncomputable def lifeInner (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) : ℝ :=
  8*max (KruskalLives.birth selectedRoot (dimerAnchor G) cutoff stop a.val)
    (ForestProbes.span selectedRoot (dimerAnchor G) cutoff a.val+2*G.margin)

noncomputable def lifeOuter (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) : ℝ :=
  KruskalLives.death selectedRoot (dimerAnchor G) cutoff stop a.val/8

def LifeProbeActive (G : DimerGeometry I J)
    (cutoff stop : ℝ) (a : DimerLife G cutoff stop) : Prop :=
  4*lifeInner G cutoff stop a<lifeOuter G cutoff stop a

noncomputable def dimerLifeProbe (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a) : Probe where
  mesh := G.mesh
  center := G.endpoint (lifeBlock G cutoff stop a,0)
  innerRadius := lifeInner G cutoff stop a
  outerRadius := lifeOuter G cutoff stop a
  mesh_pos := G.mesh_pos
  inner_pos := by
    have ht := (ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop a.property).1
    have hb := KruskalLives.cutoff_le_birth ht
    have hm := le_max_left (KruskalLives.birth selectedRoot (dimerAnchor G) cutoff stop a.val)
      (ForestProbes.span selectedRoot (dimerAnchor G) cutoff a.val+2*G.margin)
    dsimp [lifeInner]
    linarith
  radii := hactive

theorem lifeProbe_center (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a) :
    dimerAnchor G (center selectedRoot (dimerAnchor G) cutoff stop a)=
      position G.mesh (dimerLifeProbe G cutoff stop hcut a hactive).center := by
  rw [lifeBlock_center]
  rfl

theorem lifeProbe_region_subset (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a) :
    (dimerLifeProbe G cutoff stop hcut a hactive).region ⊆
      sites selectedRoot (dimerAnchor G) cutoff stop G.margin (position G.mesh) a := by
  intro v hv
  apply annular_region_subset_buffer selectedRoot (dimerAnchor G) G.margin_nonneg a
  rw [lifeProbe_center G cutoff stop hcut a hactive,dist_comm]
  exact hv

theorem lifeProbe_endpoint_excluded (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a)
    (i : I) (e : Fin 2) : G.endpoint (i,e) ∉ (dimerLifeProbe G cutoff stop hcut a hactive).region := by
  intro hv
  exact selected_support_excluded selectedRoot (dimerAnchor G) (position G.mesh)
    hcut hsmall a (Sum.inl i) (G.endpoint (i,e)) (G.endpoint_bound i e)
    (lifeProbe_region_subset G cutoff stop hcut a hactive hv)

theorem lifeProbe_overwrite_agrees (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a)
    (ω : Configuration) (color : I → CenteredBlocks.PairColor) :
    EqOn (overwriteDimers G.endpoint ω color) ω (dimerLifeProbe G cutoff stop hcut a hactive).region := by
  intro v hv
  apply overwriteDimers_outside
  rintro ⟨⟨i,e⟩,rfl⟩
  exact lifeProbe_endpoint_excluded G cutoff stop hcut hsmall a hactive i e hv

theorem lifeProbe_center_endpoint_pocket (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a)
    (e : Fin 2) : G.endpoint (lifeBlock G cutoff stop a,e) ∈
      (dimerLifeProbe G cutoff stop hcut a hactive).pocket := by
  have hc := center_mem selectedRoot (dimerAnchor G) cutoff stop a
  rw [lifeBlock_center] at hc
  have ht := selected_support_in_pocket selectedRoot (dimerAnchor G) hcut G.margin_nonneg a hc
    (G.endpoint_bound (lifeBlock G cutoff stop a) e)
  rw [lifeProbe_center G cutoff stop hcut a hactive,dist_comm] at ht
  exact ht

theorem lifeProbe_mesh_gap (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (a : DimerLife G cutoff stop) (hactive : LifeProbeActive G cutoff stop a) :
    16*G.mesh<(dimerLifeProbe G cutoff stop hcut a hactive).innerRadius := by
  have ht := (ForestTelescope.positiveLives_spec selectedRoot (dimerAnchor G) cutoff stop a.property).1
  have hb := KruskalLives.cutoff_le_birth ht
  have hm := le_max_left (KruskalLives.birth selectedRoot (dimerAnchor G) cutoff stop a.val)
    (ForestProbes.span selectedRoot (dimerAnchor G) cutoff a.val+2*G.margin)
  change 16*G.mesh<8*max _ _
  linarith [G.mesh_le_margin]

variable {Q T : Type*} [Fintype T] [DecidableEq T]

noncomputable def overwrittenCross (endpoint : I × Fin 2 ↪ Site) (board : Q → ℕ)
    (background : T → Configuration) : Q → T → (I → CenteredBlocks.PairColor) → Bool :=
  fun q t color => (axialBoxQuad (board q)).test (overwriteDimers endpoint (background t) color)

/-- The quad/time alternatives are finite when Q and T are finite. There
is no union over the assignments used by the pivotal witness. -/
def DimerLifeArmEvent (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (board : Q → ℕ)
    (a : DimerLife G cutoff stop) (background : T → Configuration) : Prop :=
  ∀ hactive : LifeProbeActive G cutoff stop a,
    ∃ q t, StraightProbeArms (board q)
      (dimerLifeProbe G cutoff stop hcut a hactive) (background t)

omit [Fintype T] in
/-- CenteredBlocks' actual endpoint-flip witness is interpreted as a
literal changed site configuration. Every other selected overwrite is
automatically outside the probe's agreement region. -/
theorem endpoint_pivotal_life_event
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (board : Q → ℕ) (hboard : ∀ q, 0<board q) (hscale : ∀ q, 3*(stop/8)<G.mesh*board q)
    (corner : Q → Bool → Bool → J)
    (hcorner : ∀ q s t, G.root (corner q s t)=axialPhysical G.mesh (signedSide (board q) s,signedSide (board q) t))
    (background : T → Configuration)
    (hpiv : AllEndpointPivotal (overwrittenCross G.endpoint board background))
    (a : DimerLife G cutoff stop) :
    DimerLifeArmEvent G cutoff stop hcut board a background := by
  intro hactive
  let P := dimerLifeProbe G cutoff stop hcut a hactive
  let i := lifeBlock G cutoff stop a
  obtain ⟨z,q,t,e,hchange⟩ := hpiv i
  let color := slice z t
  let changed := Function.update color i (Function.update (color i) e (!(color i e)))
  have hc : (axialBoxQuad (board q)).test (overwriteDimers G.endpoint (background t) changed) ≠
      (axialBoxQuad (board q)).test (overwriteDimers G.endpoint (background t) color) := by
    simpa only [overwrittenCross,slice_flipHistory,changed,color,slice] using hchange
  refine ⟨q,t,?_⟩
  apply life_straightProbeArms hbulkSource hhalfSource selectedRoot (dimerAnchor G)
    hcut (board q) (hboard q) P (hscale q) (fun s t => Sum.inr (corner q s t))
    (fun s t => ⟨corner q s t,rfl⟩) (hcorner q) a
    (lifeProbe_center G cutoff stop hcut a hactive) rfl
    (lifeProbe_mesh_gap G cutoff stop hcut hsmall a hactive)
    (background t) (overwriteDimers G.endpoint (background t) changed)
    (overwriteDimers G.endpoint (background t) color) _ _ _ hc
  · intro v hv
    apply overwriteDimers_flip_other
    intro he
    apply hv
    rw [he]
    exact lifeProbe_center_endpoint_pocket G cutoff stop hcut a hactive e
  · exact lifeProbe_overwrite_agrees G cutoff stop hcut hsmall a hactive _ _
  · exact lifeProbe_overwrite_agrees G cutoff stop hcut hsmall a hactive _ _

/-- No monotonicity of the outer test is needed. A nonzero centered signed
history kernel forces the actual full arm event for every positive life. -/
theorem nonzero_centered_life_events
    (hbulkSource : PublishedPolygonBulkArms) (hhalfSource : PublishedPolygonHalfArms)
    (G : DimerGeometry I J) (cutoff stop : ℝ) (hcut : 0<cutoff) (hsmall : G.margin≤cutoff/100)
    (board : Q → ℕ) (hboard : ∀ q, 0<board q) (hscale : ∀ q, 3*(stop/8)<G.mesh*board q)
    (corner : Q → Bool → Bool → J)
    (hcorner : ∀ q s t, G.root (corner q s t)=axialPhysical G.mesh (signedSide (board q) s,signedSide (board q) t))
    (background : T → Configuration) (w : I → (T → CenteredBlocks.PairColor) → ℝ)
    (outer : (Q × T → Bool) → ℝ) (hw : ∀ i, ∑ z, w i z=0)
    (hne : kernel w (fun z => outer (historyTests (overwrittenCross G.endpoint board background) z))≠0) :
    ∀ a, DimerLifeArmEvent G cutoff stop hcut board a background := by
  exact endpoint_pivotal_life_event hbulkSource hhalfSource G cutoff stop hcut hsmall
    board hboard hscale corner hcorner background
    (pair_history_pivotal_witness w (overwrittenCross G.endpoint board background) outer hw hne)

#print axioms lifeProbe_overwrite_agrees
#print axioms lifeProbe_center_endpoint_pocket
#print axioms nonzero_centered_life_events

end ExceptionalTimes.PairSquareSewing

