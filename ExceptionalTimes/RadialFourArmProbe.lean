import ExceptionalTimes.RadialSeparatedLaw
import ExceptionalTimes.HexCutTrimming
import ExceptionalTimes.NecklaceDictionary

/-! Concrete circular probes for the local term in the radial variance
estimate. All site support and mesoscopic-cell margins are proved here.
No local pivotal-to-four-arm implication or two-time decay is assumed to
be a proved result. -/

namespace ExceptionalTimes.RadialFourArmProbe

open PairSquareSewing MesoscopicCells RadialGapRadii HoleFilling

theorem radius_le_outer_box (P : Probe) {q : ℕ}
    (hq : 4*P.outerRadius ≤ P.mesh*(q : ℝ)) :
    ∀ v, P.radius v≤2*P.outerRadius → v-P.center∈latticeBox q := by
  intro v hv
  obtain ⟨hx,hy⟩ := triangularEmbedding_coordinate_bounds (v-P.center)
  have hr := hv
  rw [P.radius_eq_mesh_norm] at hr
  have hx' : |((v-P.center).1 : ℝ)| ≤ q := by nlinarith [P.mesh_pos]
  have hy' : |((v-P.center).2 : ℝ)| ≤ q := by nlinarith [P.mesh_pos]
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
  exact ⟨⟨by exact_mod_cast (abs_le.mp hx').1,by exact_mod_cast (abs_le.mp hx').2⟩,
    ⟨by exact_mod_cast (abs_le.mp hy').1,by exact_mod_cast (abs_le.mp hy').2⟩⟩

theorem region_subset_box (P : Probe) {q : ℕ}
    (hq : 4*P.outerRadius ≤ P.mesh*(q : ℝ)) :
    ∀ v∈P.region, v-P.center∈latticeBox q :=
  fun v hv => radius_le_outer_box P hq v hv.2

theorem fourArms_box_local (P : Probe) {q : ℕ}
    (hq : 4*P.outerRadius ≤ P.mesh*(q : ℝ)) (ω η : Configuration)
    (heq : ∀ v, v-P.center∈latticeBox q → ω v=η v) :
    FourArms P ω ↔ FourArms P η :=
  fourArms_congr P (fun v hv => heq v (region_subset_box P hq v hv))

theorem innerScale_large {K m d ρ : ℕ} (hK : 2≤K) (hm : 0<m)
    (hd : d≤m) (hscale : 8192*K*m≤ρ) :
    512*(m+d+1)<K*innerScale K ρ := by
  have hden : 0<4*K := by positivity
  have hn : 2048*m ≤ innerScale K ρ := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith
  have hKn := Nat.mul_le_mul_left K hn
  have hKm := Nat.mul_le_mul_right m hK
  nlinarith

/-- The local circular event is comfortably inside the independent
middle box. The large numerical constant only fixes deterministic margins. -/
noncomputable def probe (x : Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 8192*K*m≤latticeRadius x) : Probe where
  mesh := 1
  center := x
  innerRadius := 16*(m+d+1 : ℕ)
  outerRadius := (K*innerScale K (latticeRadius x) : ℕ)/8
  mesh_pos := by norm_num
  inner_pos := by positivity
  radii := by
    have h : (512*(m+d+1) : ℝ)<(K*innerScale K (latticeRadius x) : ℕ) := by
      exact_mod_cast innerScale_large hK hm hd hscale
    push_cast at h ⊢
    linarith

theorem probe_mesh_margin (x : Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m)
    (hd : d≤m) (hscale : 8192*K*m≤latticeRadius x) :
    16*(probe x K m d hK hm hd hscale).mesh <
      (probe x K m d hK hm hd hscale).innerRadius := by
  dsimp [probe]
  have hm' : 0<(m : ℝ) := by exact_mod_cast hm
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) d]

theorem probe_region (x : Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m)
    (hd : d≤m) (hscale : 8192*K*m≤latticeRadius x) :
    ∀ v∈(probe x K m d hK hm hd hscale).region,
      v-x∈latticeBox (K*innerScale K (latticeRadius x)) := by
  apply region_subset_box
  dsimp [probe]
  linarith [Nat.cast_nonneg (α := ℝ) (K*innerScale K (latticeRadius x))]

theorem probe_locality (x : Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m)
    (hd : d≤m) (hscale : 8192*K*m≤latticeRadius x)
    (ω η : Configuration)
    (heq : ∀ v, v-x∈latticeBox (K*innerScale K (latticeRadius x)) → ω v=η v) :
    FourArms (probe x K m d hK hm hd hscale) ω ↔
      FourArms (probe x K m d hK hm hd hscale) η :=
  fourArms_congr _ (fun v hv => heq v (probe_region x K m d hK hm hd hscale v hv))

theorem cell_in_pocket {B : Type*} [Fintype B]
    (slot : B×Fin 2 ↪ Site) (z : Site) (K m d : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m) (hz : z∈latticeBox d)
    (hp : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (c : Site) (hc : c∈occupied m slot)
    (hscale : 8192*K*m≤anchorRadius m slot c) :
    ∀ v∈dimerCell m slot c,
      v∈(probe (anchor m slot c) K m d hK hm hd hscale).pocket := by
  intro v hv
  have hb := dimerCell_diameter m hm slot z hz hp hv (anchor_mem m slot c hc)
  have hnorm := triangularEmbedding_norm_le_of_mem_box hb
  change (probe (anchor m slot c) K m d hK hm hd hscale).radius v < _
  rw [Probe.radius_eq_mesh_norm]
  dsimp [probe]
  push_cast at hnorm ⊢
  linarith

theorem probe_region_avoids_boundaries (x : Site) (K m d r R : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 8192*K*m≤latticeRadius x)
    (hr : 0<r) (hR : 16*r≤R) (hdr : 2*d≤r)
    (hx : x∈annularSites (2*r-d) (R/2+d)) :
    ∀ v∈(probe x K m d hK hm hd hscale).region,
      v∈latticeBox R ∧ v∉latticeBox r := by
  intro v hv
  apply ActiveMiddlePartition.translated_probe_bulk hr hR hdr hx
  apply latticeBox_mono _ (probe_region x K m d hK hm hd hscale v hv)
  have hprod := Nat.mul_div_le (latticeRadius x) (4*K)
  apply (Nat.le_div_iff_mul_le (by norm_num : 0<4)).mpr
  change 4*K*innerScale K (latticeRadius x)≤latticeRadius x at hprod
  nlinarith

theorem probe_closed_ball_bulk (x : Site) (K m d r R : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 8192*K*m≤latticeRadius x)
    (hr : 0<r) (hR : 16*r≤R) (hdr : 2*d≤r)
    (hx : x∈annularSites (2*r-d) (R/2+d)) :
    ∀ v, (probe x K m d hK hm hd hscale).radius v≤
        2*(probe x K m d hK hm hd hscale).outerRadius →
      v∈latticeBox R ∧ v∉latticeBox r := by
  intro v hv
  apply ActiveMiddlePartition.translated_probe_bulk hr hR hdr hx
  apply latticeBox_mono _ (radius_le_outer_box (probe x K m d hK hm hd hscale)
    (q := K*innerScale K (latticeRadius x)) (by
      dsimp [probe]
      linarith [Nat.cast_nonneg (α := ℝ) (K*innerScale K (latticeRadius x))]) v hv)
  have hprod := Nat.mul_div_le (latticeRadius x) (4*K)
  apply (Nat.le_div_iff_mul_le (by norm_num : 0<4)).mpr
  change 4*K*innerScale K (latticeRadius x)≤latticeRadius x at hprod
  nlinarith

theorem probe_far_outside (x : Site) (K m d : ℕ) (hK : 2≤K) (hm : 0<m)
    (hd : d≤m) (hscale : 8192*K*m≤latticeRadius x) {s : Site}
    (hs : (latticeRadius x : ℝ)/2≤‖triangularEmbedding (s-x)‖) :
    2*(probe x K m d hK hm hd hscale).outerRadius<
      (probe x K m d hK hm hd hscale).radius s := by
  have hprod := Nat.mul_div_le (latticeRadius x) (4*K)
  have hprod' : 4*(K*innerScale K (latticeRadius x) : ℕ)≤(latticeRadius x : ℝ) := by
    exact_mod_cast (show 4*(K*innerScale K (latticeRadius x))≤latticeRadius x from by
      simpa only [innerScale,mul_assoc] using hprod)
  have hρ : 0<(latticeRadius x : ℝ) := by
    have : 0<latticeRadius x := by nlinarith
    exact_mod_cast this
  rw [Probe.radius_eq_mesh_norm]
  dsimp [probe]
  linarith

theorem probe_fourArms_fillBox (x : Site) (K m d r R : ℕ)
    (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 8192*K*m≤latticeRadius x)
    (hr : 0<r) (hR : 16*r≤R) (hdr : 2*d≤r)
    (hx : x∈annularSites (2*r-d) (R/2+d)) (ω : Configuration) :
    FourArms (probe x K m d hK hm hd hscale) (fillBox ω r) ↔
      FourArms (probe x K m d hK hm hd hscale) ω := by
  apply fourArms_congr
  intro v hv
  exact fillBox_outside ω r
    (probe_region_avoids_boundaries x K m d r R hK hm hd hscale hr hR hdr hx v hv).2

#print axioms probe_locality
#print axioms cell_in_pocket
#print axioms probe_fourArms_fillBox

end ExceptionalTimes.RadialFourArmProbe
