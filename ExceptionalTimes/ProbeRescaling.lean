import ExceptionalTimes.HexCutTrimming

/-! Exact positive rescaling of the literal four-arm event, including
its first-contact convention and cyclic order. No comparison of laws or
scaling-limit theorem is used. -/

namespace ExceptionalTimes.PairSquareSewing

noncomputable def Probe.rescale (P : Probe) (a : ℝ) (ha : 0<a) : Probe where
  mesh := a*P.mesh
  center := P.center
  innerRadius := a*P.innerRadius
  outerRadius := a*P.outerRadius
  mesh_pos := mul_pos ha P.mesh_pos
  inner_pos := mul_pos ha P.inner_pos
  radii := by nlinarith [P.radii]

theorem position_rescale (a e : ℝ) (v : Site) :
    position (a*e) v=(a : ℂ)*position e v := by
  simp only [position,Complex.ofReal_mul,mul_assoc]

theorem complex_dist_rescale (a : ℝ) (ha : 0<a) (z w : ℂ) :
    dist ((a : ℂ)*z) ((a : ℂ)*w)=a*dist z w := by
  simp only [Complex.dist_eq,← mul_sub,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ha]

theorem Probe.radius_rescale (P : Probe) (a : ℝ) (ha : 0<a) (v : Site) :
    (P.rescale a ha).radius v=a*P.radius v := by
  simp only [Probe.radius_eq_mesh_norm,Probe.rescale,mul_assoc]

theorem Probe.region_rescale (P : Probe) (a : ℝ) (ha : 0<a) :
    (P.rescale a ha).region=P.region := by
  ext v
  change _/2≤(P.rescale a ha).radius v ∧ (P.rescale a ha).radius v≤2*_ ↔ _
  rw [P.radius_rescale]
  change a*P.innerRadius/2≤a*P.radius v ∧ a*P.radius v≤2*(a*P.outerRadius) ↔
    P.innerRadius/2≤P.radius v ∧ P.radius v≤2*P.outerRadius
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

theorem edgeTrace_rescale (a e : ℝ) {u v : Site} {q : ℂ}
    (hq : q∈edgeTrace e u v) : (a : ℂ)*q∈edgeTrace (a*e) u v := by
  obtain ⟨t,ht0,ht1,rfl⟩ := hq
  refine ⟨t,ht0,ht1,?_⟩
  rw [position_rescale,position_rescale]
  ring

theorem Probe.outerContact_rescale (P : Probe) (a : ℝ) (ha : 0<a)
    {u v : Site} {p : triangularGraph.Walk u v} {q : ℂ}
    (hq : P.OuterContact p q) :
    (P.rescale a ha).OuterContact p ((a : ℂ)*q) := by
  obtain ⟨w,initial,last,heq,hinside,hedge,hdist⟩ := hq
  refine ⟨w,initial,last,heq,?_,edgeTrace_rescale a P.mesh hedge,?_⟩
  · intro z hz
    rw [P.radius_rescale]
    exact mul_lt_mul_of_pos_left (hinside z hz) ha
  · change dist ((a : ℂ)*q) (position (a*P.mesh) P.center)=a*P.outerRadius
    rw [position_rescale,complex_dist_rescale a ha,hdist]

theorem Probe.cyclicOuter_rescale (P : Probe) (a : ℝ) (ha : 0<a)
    {q : Fin 4→ℂ} (hq : P.CyclicOuter q) :
    (P.rescale a ha).CyclicOuter (fun i => (a : ℂ)*q i) := by
  obtain ⟨hdist,turns,hmono,hlt⟩ := hq
  constructor
  · intro i
    change dist ((a : ℂ)*q i) (position (a*P.mesh) P.center)=a*P.outerRadius
    rw [position_rescale,complex_dist_rescale a ha,hdist]
  · refine ⟨turns,?_,?_⟩
    · change StrictMono (fun i => Complex.arg ((a : ℂ)*q i-position (a*P.mesh) P.center)+
        2*Real.pi*(turns i : ℝ))
      simpa only [position_rescale,← mul_sub,Complex.arg_real_mul _ ha] using hmono
    · change Complex.arg ((a : ℂ)*q 3-position (a*P.mesh) P.center)+2*Real.pi*(turns 3 : ℝ)<
        Complex.arg ((a : ℂ)*q 0-position (a*P.mesh) P.center)+2*Real.pi*(turns 0 : ℝ)+2*Real.pi
      simpa only [position_rescale,← mul_sub,Complex.arg_real_mul _ ha] using hlt

theorem FourArms.rescale {P : Probe} {ω : Configuration} (h : FourArms P ω)
    (a : ℝ) (ha : 0<a) : FourArms (P.rescale a ha) ω := by
  obtain ⟨s,t,p,hp,hs,ht,hcol,hdis,q,hcontact,horder⟩ := h
  refine ⟨s,t,p,hp,?_,?_,?_,hdis,(fun i => (a : ℂ)*q i),
    (fun i => P.outerContact_rescale a ha (hcontact i)),P.cyclicOuter_rescale a ha horder⟩
  · intro i
    rw [P.radius_rescale]
    exact mul_le_mul_of_nonneg_left (hs i) ha.le
  · intro i
    rw [P.radius_rescale]
    exact mul_le_mul_of_nonneg_left (ht i) ha.le
  · intro i z hz
    rw [P.region_rescale]
    exact hcol i z hz

theorem Probe.rescale_inverse (P : Probe) (a : ℝ) (ha : 0<a) :
    (P.rescale a ha).rescale a⁻¹ (inv_pos.mpr ha)=P := by
  cases P
  simp only [Probe.rescale,← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul]

theorem fourArms_rescale_iff (P : Probe) (a : ℝ) (ha : 0<a) (ω : Configuration) :
    FourArms (P.rescale a ha) ω ↔ FourArms P ω := by
  constructor
  · intro h
    have hh := h.rescale a⁻¹ (inv_pos.mpr ha)
    rwa [P.rescale_inverse a ha] at hh
  · exact fun h => h.rescale a ha

#print axioms Probe.cyclicOuter_rescale
#print axioms fourArms_rescale_iff

end ExceptionalTimes.PairSquareSewing
