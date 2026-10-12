import ExceptionalTimes.DyadicForestStop

/-! Fixed-mesh versions of the ordinary arm-estimate proof chain.
The profile is required only for probes at the specified lattice mesh;
no comparison between different meshes is assumed. -/
open Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.PairSquareSewing
noncomputable section
open EnvironmentVariance ProbeProduct ArmEnlargement ManyDimerLaw DimerLaw
variable {B : Type*} [Fintype B] {ε : ℝ}

/-- The usual circular-buffer ordinary four-arm estimate at one fixed
mesh. This is the needed source scope for a mesh-dependent arm profile. -/
def PublishedFourArmBoundAt (ε B₀ C : ℝ) (α : ℝ→ℝ→ℝ) : Prop :=
  ∀ (P : Probe),P.mesh=ε → ∀ (D : Finset Site),B₀*P.mesh≤P.innerRadius →
    P.region⊆(D:Set Site) →
    probability (fairSites D) (fun ω => FourArms P (completeColors D ω))≤
      C*α P.innerRadius P.outerRadius

theorem mixed_active_probability_bound_at_mesh
    {B₀ C₄ C₃ c g : ℝ} (α : ℝ → ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ε B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (heP : P.mesh=ε) (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary)
    (hb : BulkPartActive P q) (hh : HalfPartActive P q) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh ≤ P.innerRadius)
    (hg : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hα : 0≤α P.innerRadius (min P.outerRadius (P.distanceTo q/8)))
    (hlower : c*((8*max P.innerRadius (P.distanceTo q))/(P.outerRadius/8))^g ≤
      α (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8)) :
    probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) ≤
      (C₄*C₃/c)*α P.innerRadius (min P.outerRadius (P.distanceTo q/8)) *
        α (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8) := by
  have heq : probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) =
      probability (fairSites D) (fun ω => FourArms (P.bulkPart q hb) (completeColors D ω) ∧
        HalfThreeArms (P.halfPart H q hq hh) (completeColors D ω)) := by
    apply probability_congr
    intro ω
    exact ⟨fun h => ⟨h.1 hb,h.2 hh⟩,fun h => ⟨fun _ => h.1,fun _ => h.2⟩⟩
  rw [heq,bulk_half_probability_product _ _ D (P.bulk_half_disjoint H q hq hb hh)]
  have hfour' := hfour (P.bulkPart q hb) heP D hmesh ((P.bulkPart_region q hb).trans hD)
  have hhalfmesh : B₀*(P.halfPart H q hq hh).mesh ≤ (P.halfPart H q hq hh).innerRadius := by
    change B₀*P.mesh ≤ 8*max P.innerRadius (P.distanceTo q)
    have hm := le_max_left P.innerRadius (P.distanceTo q)
    linarith [P.inner_pos]
  have hthree' := halfThree_probability_le_four hthree (P.halfPart H q hq hh) D hhalfmesh
    ((P.halfPart_region H q hq hh).trans hD) hg hc hC₃ α hlower
  have hprod := mul_le_mul hfour' hthree' (probability_nonneg _ _) (mul_nonneg hC₄ hα)
  convert hprod using 1
  dsimp [Probe.bulkPart,Probe.halfPart]
  ring

theorem mixed_probability_le_profile_at_mesh
    {B₀ C₄ C₃ c C Q g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ε B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (heP : P.mesh=ε) (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh ≤ P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*Q) (hKH : 1≤C₃*Q/c)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤Q*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) ≤
      ((C₄*Q)*(C₃*Q/c)*C^3*(8192:ℝ)^g)*(p P.innerRadius/p P.outerRadius) := by
  have hbulk (hb : BulkPartActive P q) :
      probability (fairSites D) (fun ω => FourArms (P.bulkPart q hb) (completeColors D ω)) ≤
        (C₄*Q)*(p P.innerRadius/p (min P.outerRadius (P.distanceTo q/8))) := by
    have hstat := hfour (P.bulkPart q hb) heP D hmesh ((P.bulkPart_region q hb).trans hD)
    have hab : P.innerRadius < min P.outerRadius (P.distanceTo q/8) := by
      have h : 4*P.innerRadius < min P.outerRadius (P.distanceTo q/8) := hb
      linarith [P.inner_pos]
    have ht := mul_le_mul_of_nonneg_left
      (hquasi _ _ P.inner_pos hab (min_le_left _ _)) hC₄
    apply hstat.trans
    change C₄*α P.innerRadius (min P.outerRadius (P.distanceTo q/8)) ≤ _
    convert ht using 1
    ring
  have hhalf (hh : HalfPartActive P q) :
      probability (fairSites D) (fun ω => HalfThreeArms (P.halfPart H q hq hh) (completeColors D ω)) ≤
        (C₃*Q/c)*(p (8*max P.innerRadius (P.distanceTo q))/p (P.outerRadius/8)) := by
    have ha0 : 0<8*max P.innerRadius (P.distanceTo q) := (P.halfPart H q hq hh).inner_pos
    have ha : B₀*P.mesh≤8*max P.innerRadius (P.distanceTo q) := by
      have hm := le_max_left P.innerRadius (P.distanceTo q)
      linarith [P.inner_pos]
    have hab : 8*max P.innerRadius (P.distanceTo q)<P.outerRadius/8 := by
      have ht : 4*(8*max P.innerRadius (P.distanceTo q))<P.outerRadius/8 := hh
      linarith
    have hbR : P.outerRadius/8≤P.outerRadius := by linarith [P.radii,P.inner_pos]
    exact halfThree_probability_le_profile hthree (P.halfPart H q hq hh) D ha
      ((P.halfPart_region H q hq hh).trans hD) hg2 hc hC₃ α p
      (hfourlower _ _ ha ha0 hab.le hbR) (hquasi _ _ ha0 hab hbR)
  have h := mixed_probability_le_split P H q hq D p hKB hKH hbulk hhalf
  have hK : 0≤(C₄*Q)*(C₃*Q/c) := mul_nonneg (by linarith) (by linarith)
  have hcost := mul_le_mul_of_nonneg_left (splitProfileCost_le P q p hC hg0 hp hlower) hK
  apply h.trans
  convert hcost using 1
  ring

theorem interior_probability_le_profile_at_mesh
    {B₀ C₄ C Q g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ε B₀ C₄ α) (P : Probe) (heP : P.mesh=ε) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg : 0≤g) (hC : 1≤C) (hC₄ : 0≤C₄) (hK : 1≤C₄*Q)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤Q*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a) :
    probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω)) ≤
      ((C₄*Q)*C^2*(16:ℝ)^g)*(p P.innerRadius/p P.outerRadius) := by
  have hr := P.inner_pos
  have hR : 0<P.outerRadius := by linarith [P.radii]
  have hrR : P.innerRadius≤P.outerRadius := by linarith [P.radii]
  have hpr := hp P.innerRadius hr hrR
  have hpR := hp P.outerRadius hR le_rfl
  have hC0 : 0≤C := by linarith
  have hK0 : 0≤C₄*Q := by linarith
  by_cases h : 16*P.innerRadius<P.outerRadius
  · have heq : probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω)) =
        probability (fairSites D) (fun ω => FourArms (P.inset h) (completeColors D ω)) := by
      apply probability_congr
      exact fun _ => ⟨fun h' => h' h,fun h' _ => h'⟩
    rw [heq]
    have hab : P.innerRadius<P.outerRadius/4 := by linarith
    have hbR : P.outerRadius/4≤P.outerRadius := by linarith
    have hstat := hfour (P.inset h) heP D hmesh ((P.inset_region h).trans hD)
    have hstat' : probability (fairSites D) (fun ω => FourArms (P.inset h) (completeColors D ω)) ≤
        (C₄*Q)*(p P.innerRadius/p (P.outerRadius/4)) := by
      apply hstat.trans
      have ht := mul_le_mul_of_nonneg_left (hquasi _ _ hr hab hbR) hC₄
      change C₄*α P.innerRadius (P.outerRadius/4)≤_
      convert ht using 1
      ring
    have hb0 : 0<P.outerRadius/4 := by positivity
    have hratio := ratio_compare p hr le_rfl hab.le hbR le_rfl hC0 hpr.le (hp _ hb0 hbR) hpR hlower
    have hscale : (P.innerRadius/P.innerRadius)*(P.outerRadius/(P.outerRadius/4))=4 := by
      field_simp
    rw [hscale] at hratio
    have hpow := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤4) (by norm_num : (4:ℝ)≤16) hg
    have hbound : p P.innerRadius/p (P.outerRadius/4)≤C^2*(16:ℝ)^g*(p P.innerRadius/p P.outerRadius) := by
      have hr' : p P.innerRadius/p (P.outerRadius/4)≤C^2*(4:ℝ)^g*(p P.innerRadius/p P.outerRadius) := by
        convert hratio using 1
        ring
      exact hr'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg C)) (div_nonneg hpr.le hpR.le))
    have ht := mul_le_mul_of_nonneg_left hbound hK0
    apply hstat'.trans
    convert ht using 1
    ring
  · have heq : probability (fairSites D) (fun ω => InteriorProbeArms P (completeColors D ω))=1 := by
      have he : ∀ ω, InteriorProbeArms P (completeColors D ω)↔True :=
        fun _ => ⟨fun _ => trivial,fun _ hh => (h hh).elim⟩
      rw [probability_congr (fairSites D) he]
      simp [probability,EnvironmentVariance.indicator,FiniteLaw.expect_const]
    rw [heq]
    have hscale : P.outerRadius/P.innerRadius≤16 := (div_le_iff₀ hr).mpr (le_of_not_gt h)
    have hpow := Real.rpow_le_rpow (div_nonneg hR.le hr.le) hscale hg
    have hCC : C≤(C₄*Q)*C^2 := by
      have h2 : C≤C^2 := by nlinarith
      have hk := mul_le_mul_of_nonneg_right hK (sq_nonneg C)
      linarith
    have hlarge : p P.outerRadius≤((C₄*Q)*C^2*(16:ℝ)^g)*p P.innerRadius := by
      calc
        _ ≤ C*(P.outerRadius/P.innerRadius)^g*p P.innerRadius := hlower _ _ hr hrR le_rfl
        _ ≤ C*(16:ℝ)^g*p P.innerRadius := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC0) hpr.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (by norm_num) g)) hpr.le
    have ht := div_le_div_of_nonneg_right hlarge hpR.le
    rw [div_self (ne_of_gt hpR)] at ht
    convert ht using 1
    ring

theorem PolygonArmChoice.probability_le_profile_at_mesh
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ε B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (heP : P.mesh=ε) (choice : PolygonArmChoice P) (D : Finset Site)
    (hD : P.region ⊆ (D : Set Site)) (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hp : ∀ t, 0<t → t≤P.outerRadius → 0<p t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤K*(p a/p b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → p b≤C*(b/a)^g*p a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (fairSites D) (fun ω => choice.event (completeColors D ω)) ≤
      fullProbeConstant C₄ C₃ c C K g*(p P.innerRadius/p P.outerRadius) := by
  have hC0 : 0≤C := by linarith
  have hKB0 : 0≤C₄*K := by linarith
  have hKH0 : 0≤C₃*K/c := by linarith
  have hrR : P.innerRadius≤P.outerRadius := by linarith [P.radii,P.inner_pos]
  have hR : 0<P.outerRadius := P.inner_pos.trans_le hrR
  have hpRatio : 0≤p P.innerRadius/p P.outerRadius :=
    div_nonneg (hp _ P.inner_pos hrR).le (hp _ hR le_rfl).le
  have hMix : 0≤(C₄*K)*(C₃*K/c)*C^3*(8192:ℝ)^g := by positivity
  have hInt : 0≤(C₄*K)*C^2*(16:ℝ)^g := by positivity
  cases choice with
  | bulk =>
    apply (interior_probability_le_profile_at_mesh α p hfour P heP D hD hmesh hg0 hC hC₄ hKB hp hquasi hlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hMix) hpRatio
  | boundary H q hq =>
    apply (mixed_probability_le_profile_at_mesh α p hfour hthree P heP H q hq D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hp hquasi hlower hfourlower).trans
    unfold fullProbeConstant
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hInt) hpRatio

theorem canonical_polygonProbe_union_bound_at_mesh {Q : Type*} [Fintype Q]
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBoundAt ε B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (P : Probe) (heP : P.mesh=ε) (choice : Q → PolygonArmChoice P) (hD : P.region ⊆ (D : Set Site))
    (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hprofile : ∀ t, 0<t → t≤P.outerRadius → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (manyLaw p hp0 hp1)
      (fun z => ∃ q t, (choice q).event (canonicalBackground slot z t)) ≤
      (Fintype.card (Q × Bool) : ℝ)*fullProbeConstant C₄ C₃ c C K g*
        (profile P.innerRadius/profile P.outerRadius) := by
  let E : (Q × Bool) → ((B → Color) × (B → Color)) → Prop :=
    fun qt z => (choice qt.1).event (canonicalBackground slot z qt.2)
  have hprob : probability (manyLaw p hp0 hp1)
      (fun z => ∃ q t, (choice q).event (canonicalBackground slot z t)) =
      probability (manyLaw p hp0 hp1) (fun z => ∃ qt, E qt z) := by
    apply probability_congr
    exact fun _ => ⟨fun ⟨q,t,h⟩ => ⟨(q,t),h⟩,fun ⟨⟨q,t⟩,h⟩ => ⟨q,t,h⟩⟩
  rw [hprob]
  apply (probability_exists_le (manyLaw p hp0 hp1) E).trans
  have hsingle (qt : Q × Bool) : probability (manyLaw p hp0 hp1) (E qt)≤
      fullProbeConstant C₄ C₃ c C K g*(profile P.innerRadius/profile P.outerRadius) := by
    change probability (manyLaw p hp0 hp1) (fun z => (choice qt.1).event (canonicalBackground slot z qt.2))≤_
    rw [canonicalBackground_marginal p hp0 hp1 slot D hcover qt.2 _
      (fun ω η he => (choice qt.1).locality (fun v hv => he v (hD hv)))]
    exact PolygonArmChoice.probability_le_profile_at_mesh α profile hfour hthree P heP (choice qt.1) D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hprofile hquasi hlower hfourlower
  have ht := Finset.sum_le_sum (fun qt (_ : qt∈Finset.univ) => hsingle qt)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using ht
#print axioms canonical_polygonProbe_union_bound_at_mesh
end
end ExceptionalTimes.PairSquareSewing
