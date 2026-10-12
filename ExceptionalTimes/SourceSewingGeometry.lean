import ExceptionalTimes.Source06Specialization

/-! Concrete geometry for applying source trials on compact separated
insertion tuples. Every coordinate support is an actual physical disk;
no local-change, sampling, or independence interface is assumed. -/

open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open PolygonSewing EnvironmentVariance CenteredBlocks

theorem outerRadius_margin {q k : ℕ} (G : SourceSeparatedGeometry q k) :
    128*outerRadius G≤G.margin := by
  have h := min_le_left G.margin 1
  dsimp [outerRadius]
  linarith

theorem outerRadius_le {q k : ℕ} (G : SourceSeparatedGeometry q k) :
    outerRadius G≤1/128 := by
  exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

theorem four_outerRadius_lt_margin {q k : ℕ} (G : SourceSeparatedGeometry q k) :
    4*outerRadius G<G.margin := by
  have hp := outerRadius_pos G
  have hm := outerRadius_margin G
  linarith

theorem sourcePhysicalMap_scale (e : ℝ) (he : 0<e) (p : ℝ×ℝ) :
    sourcePhysicalMap e he (e⁻¹ • p)=HexTiling.planeMap p := by
  have h := sourcePhysicalMap_shift_scale e he (0,0) p
  have h0 : HexCells.center ((0,0) : Site)=(0 : ℝ×ℝ) := by
    ext <;> norm_num [HexCells.center]
  have hpos : position e ((0,0) : Site)=0 := by
    apply Complex.ext <;> simp [position,triangularEmbedding]
  simpa only [h0,zero_add,hpos] using h

/-- The fixed physical boundary margin survives the exact inverse-mesh
scaling used by the literal polygon tests. -/
theorem source_quad_localChange {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (hbulk : PublishedPolygonBulkArms) (e : ℝ) (he : 0<e)
    (x : Fin (k+1)→Site) (hx : G.Admissible e x) (i : Fin (k+1))
    (P : Probe) (hmesh : P.mesh=e) (hcenter : P.center=x i)
    (houter : P.outerRadius=outerRadius G) (hinner : 16*e<P.innerRadius) :
    ∀j, PolygonSewing.LocalChangeArms (G.latticeQuads e he j) P := by
  intro j
  apply localChangeArms_of_no_frontier hbulk _ P (by simpa only [hmesh] using hinner)
  intro p hp
  change p∈frontier (axialScale e⁻¹ (inv_ne_zero he.ne') '' (G.quads j).carrier) at hp
  rw [←(axialScale e⁻¹ (inv_ne_zero he.ne')).image_frontier] at hp
  obtain ⟨y,hy,rfl⟩ := hp
  have hmargin := G.boundary_separated _ hx i j y hy
  have hphysical : physicalHomeomorph P (axialScale e⁻¹ (inv_ne_zero he.ne') y)=
      HexTiling.planeMap y := by
    change (P.mesh : ℂ)*HexTiling.planeMap (e⁻¹ • y)=_
    rw [hmesh]
    exact sourcePhysicalMap_scale e he y
  rw [hphysical,hmesh,hcenter,houter]
  exact (show 2*outerRadius G<G.margin by linarith [four_outerRadius_lt_margin G,outerRadius_pos G]).trans_le hmargin

/-- The actual reference rectangle contains a physical ball about its
center, with a fixed margin independent of the tolerance and mesh. -/
theorem sourceReferenceAt_ball_interior (e : ℝ) (he : 0<e) (x : Site)
    (R : ℝ) (hR : R≤1/128) :
    Metric.closedBall (position e x) (2*R) ⊆
      sourcePhysicalMap e he '' interior (sourceReferenceAt e he x).carrier := by
  rw [(sourcePhysicalMap e he).image_interior]
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨1/8,by norm_num,?_⟩
  intro y hy
  have hz' : dist z (position e x)≤2*R := hz
  have hy' : dist y z<1/8 := hy
  have hd : ‖y-position e x‖<1/2 := by
    have ht := dist_triangle y z (position e x)
    rw [dist_eq_norm] at ht
    linarith
  rw [sourceReferenceAt_carrier]
  refine ⟨y-position e x,⟨?_,?_⟩,by simp⟩
  · have hreal := Complex.abs_re_le_norm (y-position e x)
    exact ⟨by linarith [abs_le.mp (le_of_lt (hreal.trans_lt hd))],
      by linarith [abs_le.mp (le_of_lt (hreal.trans_lt hd))]⟩
  · have him := (Complex.abs_im_le_norm (y-position e x)).trans_lt hd
    exact ⟨by linarith [(abs_lt.mp him).1],(abs_lt.mp him).2.le⟩

theorem source_reference_localChange {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (hbulk : PublishedPolygonBulkArms) (e : ℝ) (he : 0<e) (x : Site)
    (P : Probe) (hmesh : P.mesh=e) (hcenter : P.center=x)
    (houter : P.outerRadius=outerRadius G) (hinner : 16*e<P.innerRadius) :
    PolygonSewing.LocalChangeArms (sourceReferenceAt e he x) P := by
  intro ω a b hab ha hb hchange
  apply hbulk _ P ω a b (by simpa only [hmesh] using hinner)
  · have h := sourceReferenceAt_ball_interior e he x (outerRadius G) (outerRadius_le G)
    simpa only [hmesh,hcenter,houter,physicalHomeomorph,sourcePhysicalMap] using h
  · exact fun v hv => changed_cell_in_buffered_ball P (by simpa only [hmesh] using hinner) hab hv
  · exact fun v hv => ⟨ha (cell_meets_agreementShell_in_region P (by simpa only [hmesh] using hinner) hv),
      hb (cell_meets_agreementShell_in_region P (by simpa only [hmesh] using hinner) hv)⟩
  · intro hc
    apply hchange
    apply ((sourceReferenceAt e he x).test_eq_iff a b).mpr
    simpa only [PolygonQuad.physicalCrossing_iff] using hc

def insertionIndex {k : ℕ} : Option (Fin k) → Fin (k+1)
  | none => 0
  | some i => i.succ

theorem insertionIndex_injective {k : ℕ} : Function.Injective (@insertionIndex k) := by
  intro i j hij
  cases i <;> cases j <;> simp_all [insertionIndex,Fin.succ_inj]
  have h := congrArg Fin.val hij
  simp at h

noncomputable def sourceCoordinates {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (x : Fin (k+1)→Site) (Λ : Finset Site) : Option (Fin k)→Set ↥Λ :=
  fun i => {v | dist (position e v) (position e (x (insertionIndex i)))≤2*outerRadius G}

theorem sourceCoordinates_disjoint {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (x : Fin (k+1)→Site) (hx : G.Admissible e x) (Λ : Finset Site) :
    Pairwise (fun i j => Disjoint (sourceCoordinates G e x Λ i) (sourceCoordinates G e x Λ j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hi hj
  have hs := G.separated _ hx (insertionIndex i) (insertionIndex j)
    (fun heq => hij (insertionIndex_injective heq))
  have ht := dist_triangle (position e (x (insertionIndex i))) (position e v)
    (position e (x (insertionIndex j)))
  rw [dist_comm (position e (x (insertionIndex i))) (position e v)] at ht
  change dist (position e v) (position e (x (insertionIndex i)))≤2*outerRadius G at hi
  change dist (position e v) (position e (x (insertionIndex j)))≤2*outerRadius G at hj
  have hm := four_outerRadius_lt_margin G
  have hp := outerRadius_pos G
  linarith

/-- A point within one outer radius of one insertion misses the doubled
probe disk of every other insertion. -/
theorem near_insertion_not_other_disk {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (x : Fin (k+1)→Site) (hx : G.Admissible e x)
    (i j : Fin (k+1)) (hij : i≠j) (v : Site)
    (hv : dist (position e v) (position e (x i))<outerRadius G) :
    ¬ dist (position e v) (position e (x j))≤2*outerRadius G := by
  intro hj
  have hs := G.separated _ hx i j hij
  have ht := dist_triangle (position e (x i)) (position e v) (position e (x j))
  rw [dist_comm (position e (x i)) (position e v)] at ht
  have hm := four_outerRadius_lt_margin G
  have hp := outerRadius_pos G
  linarith

theorem sample_contains_probe_region {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) (i : Fin (k+1))
    (P : Probe) (hmesh : P.mesh=e) (hcenter : P.center=x i)
    (houter : P.outerRadius=outerRadius G) :
    P.region ⊆ (sample G e he x h : Set Site) := by
  intro v hv
  have hvd := center_mem_sourceDiskSites e he (x i) v (2*outerRadius G)
    (by simpa only [Probe.radius,hmesh,hcenter,houter] using hv.2)
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (G.disk_sites_subset e he x _ i hvd))

#print axioms source_quad_localChange
#print axioms source_reference_localChange
#print axioms sourceCoordinates_disjoint
#print axioms sample_contains_probe_region
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization
