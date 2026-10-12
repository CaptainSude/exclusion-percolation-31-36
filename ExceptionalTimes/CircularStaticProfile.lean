import ExceptionalTimes.FixedMeshArmBounds
import ExceptionalTimes.SourceSampling

/-! Literal ordinary circular arm probabilities and a clipped finite-mesh
profile. The input below is the uniform lower power and one direction of
quasi-multiplicativity from source02 Lemma 2.1, with its stated fixed
circular cut margins (Nolin and Smirnov--Werner). No canonical law,
centered response, or forest estimate is present in this literature input. -/
open Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.CircularStaticProfile
noncomputable section
open PairSquareSewing EnvironmentVariance ProbeProduct

/-- Literal centered circular probability at separated positive radii;
the value one is the explicit convention for overlapping or invalid cuts. -/
def annulus (ε : ℝ) (he : 0<ε) (a b : ℝ) : ℝ :=
  if h : 0<a ∧ 4*a<b then
    probability (fairSites (sourceDiskSites ε he (0,0) 2))
      (fun ω => FourArms (⟨ε,(0,0),a,b,he,h.1,h.2⟩ : Probe) (complete ω))
  else 1

/-- The literal source normalization, extended by one outside its domain. -/
def cost (ε : ℝ) (he : 0<ε) (a : ℝ) : ℝ :=
  if h : 0<a ∧ 4*a<1 then sourceArmCost ε a he h.1 h.2 else 1

theorem cost_eq (ε : ℝ) (he : 0<ε) (a : ℝ) (ha : 0<a) (hsmall : 4*a<1) :
    cost ε he a=sourceArmCost ε a he ha hsmall := by
  have h : 0<a ∧ 4*a<1 := ⟨ha,hsmall⟩
  simp only [cost,dite_eq_left h]

theorem annulus_one (ε : ℝ) (he : 0<ε) (a : ℝ) : annulus ε he a 1=cost ε he a := by
  unfold annulus cost
  split_ifs with h
  · rfl
  · rfl

theorem cost_nonneg (ε : ℝ) (he : 0<ε) (a : ℝ) : 0≤cost ε he a := by
  unfold cost
  split_ifs
  · exact sourceArmCost_nonneg ..
  · norm_num

theorem annulus_nonneg (ε : ℝ) (he : 0<ε) (a b : ℝ) : 0≤annulus ε he a b := by
  unfold annulus
  split_ifs
  · exact probability_nonneg _ _
  · norm_num

/-- Ordinary, uniform fixed-mesh consequences of source02 Lemma 2.1.
All costs here are actual finite fair-site probabilities. Translation and
fixed circular-cut comparison is included explicitly in the first clause.
For triangular percolation one may take g=3/2; this weakens the source's
strict exponent margin above 5/4. This is a stated source consequence,
not a verbatim quotation and not an assumed dynamical bound. -/
def PublishedCircularArmInputs (B C₄ Q c g : ℝ) : Prop :=
  128≤B ∧ 1≤C₄ ∧ 1≤Q ∧ 0<c ∧ 0<g ∧ g<2 ∧
  (∀ (ε : ℝ) (he : 0<ε) (P : Probe) (D : Finset Site),P.mesh=ε →
    P.outerRadius≤1 → B*ε≤P.innerRadius → P.region⊆(D:Set Site) →
    probability (fairSites D) (fun ω => FourArms P (completeColors D ω))≤
      C₄*annulus ε he P.innerRadius P.outerRadius) ∧
  (∀ (ε : ℝ) (he : 0<ε) (a b : ℝ),B*ε≤a → 0<a → a≤b → b≤1 →
    c*(a/b)^g≤annulus ε he a b) ∧
  (∀ (ε : ℝ) (he : 0<ε) (a b : ℝ),B*ε≤a → 0<a → a≤b → 4*b<1 →
    annulus ε he a b*cost ε he b≤Q*cost ε he a)

variable {B C₄ Q c g : ℝ}

theorem input_cost_lower (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (a : ℝ) (hcut : B*ε≤a) (ha : 0<a) (hsmall : 4*a<1) :
    c*a^g≤cost ε he a := by
  have hb : a≤1 := by linarith
  simpa only [div_one,annulus_one] using h.2.2.2.2.2.2.2.1 ε he a 1 hcut ha hb le_rfl

theorem input_cost_pos (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (a : ℝ) (hcut : B*ε≤a) (ha : 0<a) (hsmall : 4*a<1) :
    0<cost ε he a :=
  (mul_pos h.2.2.2.1 (Real.rpow_pos_of_pos ha g)).trans_le
    (input_cost_lower h ε he a hcut ha hsmall)

theorem input_quasi (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (a b : ℝ)
    (hcut : B*ε≤a) (ha : 0<a) (hab : a≤b) (hb : 4*b<1) :
    annulus ε he a b≤Q*(cost ε he a/cost ε he b) := by
  have hpb := input_cost_pos h ε he b (hcut.trans hab) (ha.trans_le hab) hb
  have hh := h.2.2.2.2.2.2.2.2 ε he a b hcut ha hab hb
  apply (le_div_iff₀ hpb).mpr at hh
  convert hh using 1
  ring

theorem input_growth (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (a b : ℝ)
    (hcut : B*ε≤a) (ha : 0<a) (hab : a≤b) (hb : 4*b<1) :
    cost ε he b≤(Q/c)*(b/a)^g*cost ε he a := by
  have hc := h.2.2.2.1
  have hb0 : 0<b := ha.trans_le hab
  have hb1 : b≤1 := by linarith
  have hlo := h.2.2.2.2.2.2.2.1 ε he a b hcut ha hab hb1
  have hqm := h.2.2.2.2.2.2.2.2 ε he a b hcut ha hab hb
  have hmul := (mul_le_mul_of_nonneg_right hlo (cost_nonneg ε he b)).trans hqm
  have hinv : (a/b)^g*(b/a)^g=1 := by
    rw [←Real.mul_rpow (div_nonneg ha.le hb0.le) (div_nonneg hb0.le ha.le)]
    have hr : a/b*(b/a)=1 := by field_simp
    rw [hr,Real.one_rpow]
  calc
    cost ε he b=((a/b)^g*(b/a)^g)*cost ε he b := by rw [hinv,one_mul]
    _ = ((b/a)^g/c)*(c*(a/b)^g*cost ε he b) := by field_simp
    _ ≤ ((b/a)^g/c)*(Q*cost ε he a) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring


def clippedRadius (cut stop t : ℝ) : ℝ := max cut (min t stop)

theorem clipped_le (cut stop t : ℝ) (hcut : cut≤stop) : clippedRadius cut stop t≤stop :=
  max_le hcut (min_le_right _ _)

theorem le_clipped (cut stop t : ℝ) : cut≤clippedRadius cut stop t := le_max_left _ _

theorem clipped_eq_max (cut stop t : ℝ) (ht : t≤stop) :
    clippedRadius cut stop t=max cut t := by simp only [clippedRadius,min_eq_left ht]

theorem clipped_eq (cut stop t : ℝ) (hc : cut≤t) (ht : t≤stop) :
    clippedRadius cut stop t=t := by rw [clipped_eq_max _ _ _ ht,max_eq_right hc]

/-- The only sub-lattice extension is an explicit constant plateau;
the same formula is one above stop after normalization. -/
def profile (ε : ℝ) (he : 0<ε) (B stop t : ℝ) : ℝ :=
  cost ε he (clippedRadius (B*ε) stop t)/cost ε he stop

/-- Below the microscopic cut use clipped radii; above the fixed stop
use one. Both conventions are explicit and do not assert a lattice event
at a sub-lattice radius. -/
def alpha (ε : ℝ) (he : 0<ε) (B stop a b : ℝ) : ℝ :=
  if b≤stop then annulus ε he (max (B*ε) a) (max (B*ε) b) else 1

theorem cutoff_pos (h : PublishedCircularArmInputs B C₄ Q c g) {ε : ℝ} (he : 0<ε) :
    0<B*ε := mul_pos (by linarith [h.1]) he

theorem profile_pos (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hcut : B*ε≤stop) (hstop : 4*stop<1) (t : ℝ) :
    0<profile ε he B stop t := by
  have hcp := cutoff_pos h he
  have hsp := hcp.trans_le hcut
  unfold profile
  apply div_pos
  · exact input_cost_pos h ε he _ (le_clipped _ _ _) (hcp.trans_le (le_clipped _ _ _))
      (by have hh := clipped_le (B*ε) stop t hcut; linarith)
  · exact input_cost_pos h ε he stop hcut hsp hstop

theorem profile_at_stop (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hcut : B*ε≤stop) (hstop : 4*stop<1) :
    profile ε he B stop stop=1 := by
  rw [profile,clipped_eq _ _ _ hcut le_rfl]
  exact div_self (input_cost_pos h ε he stop hcut ((cutoff_pos h he).trans_le hcut) hstop).ne'

theorem profile_quasi (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hcut : B*ε≤stop) (hstop : 4*stop<1)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hb : b≤stop) :
    alpha ε he B stop a b≤Q*(profile ε he B stop a/profile ε he B stop b) := by
  have hden := input_cost_pos h ε he stop hcut ((cutoff_pos h he).trans_le hcut) hstop
  rw [alpha,ite_eq_left hb,profile,profile,clipped_eq_max _ _ _ (hab.le.trans hb),
    clipped_eq_max _ _ _ hb,div_div_div_cancel_right₀ hden.ne']
  exact input_quasi h ε he _ _ (le_max_left _ _) (ha.trans_le (le_max_right _ _))
    (max_le_max le_rfl hab.le) (by have hh := max_le hcut hb; linarith)

theorem max_ratio_le {cut a b : ℝ} (hcut : 0<cut) (ha : 0<a) (hab : a≤b) :
    max cut b/max cut a≤b/a := by
  by_cases hca : cut≤a
  · rw [max_eq_right hca,max_eq_right (hca.trans hab)]
  · rw [max_eq_left (le_of_not_ge hca)]
    by_cases hcb : cut≤b
    · rw [max_eq_right hcb]
      apply (div_le_div_iff₀ hcut ha).mpr
      nlinarith [ha.trans_le hab]
    · rw [max_eq_left (le_of_not_ge hcb),div_self hcut.ne']
      exact (le_div_iff₀ ha).mpr (by simpa only [one_mul] using hab)

theorem profile_growth (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hcut : B*ε≤stop) (hstop : 4*stop<1)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hb : b≤stop) :
    profile ε he B stop b≤max 1 (Q/c)*(b/a)^g*profile ε he B stop a := by
  have hcp := cutoff_pos h he
  have hden := input_cost_pos h ε he stop hcut (hcp.trans_le hcut) hstop
  have hA : 0<max (B*ε) a := hcp.trans_le (le_max_left _ _)
  have hB : max (B*ε) b≤stop := max_le hcut hb
  have hgrowth := input_growth h ε he (max (B*ε) a) (max (B*ε) b)
    (le_max_left _ _) hA (max_le_max le_rfl hab) (by linarith)
  have hp := Real.rpow_le_rpow (div_nonneg (hA.trans_le (max_le_max le_rfl hab)).le hA.le)
    (max_ratio_le hcp ha hab) h.2.2.2.2.1.le
  have hQa : 0≤Q/c := div_nonneg (by linarith [h.2.2.1]) h.2.2.2.1.le
  have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hQa)
    (cost_nonneg ε he (max (B*ε) a))
  have hbig := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (le_max_right (1:ℝ) (Q/c)) (Real.rpow_nonneg (div_nonneg (ha.trans_le hab).le ha.le) g))
    (cost_nonneg ε he (max (B*ε) a))
  have hh := div_le_div_of_nonneg_right ((hgrowth.trans hstep).trans hbig) hden.le
  unfold profile
  rw [clipped_eq_max _ _ _ hb,clipped_eq_max _ _ _ (hab.trans hb)]
  convert hh using 1
  ring


theorem alpha_fourArm_at_mesh (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hstop : 4*stop<1) :
    PublishedFourArmBoundAt ε B C₄ (alpha ε he B stop) := by
  intro P hP D hcut hD
  have hcut' : B*ε≤P.innerRadius := by simpa only [hP] using hcut
  by_cases hb : P.outerRadius≤stop
  · rw [alpha,ite_eq_left hb,max_eq_right hcut',
      max_eq_right (hcut'.trans (by linarith [P.radii,P.inner_pos]))]
    exact h.2.2.2.2.2.2.1 ε he P D hP (by linarith) hcut' hD
  · rw [alpha,ite_eq_right hb,mul_one]
    exact (probability_le_one _ _).trans h.2.1

theorem alpha_lower (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop : ℝ) (hstop : 4*stop<1)
    (a b : ℝ) (hcut : B*ε≤a) (ha : 0<a) (hab : a≤b) (hb : b≤stop) :
    c*(a/b)^g≤alpha ε he B stop a b := by
  rw [alpha,ite_eq_left hb,max_eq_right hcut,max_eq_right (hcut.trans hab)]
  exact h.2.2.2.2.2.2.2.1 ε he a b hcut ha hab (by linarith)

def cutoffConstant (B Q c g κ stop : ℝ) : ℝ := (Q/c)*(κ/B)^g/(c*stop^g)

theorem profile_cutoff_le_cost (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop κ : ℝ)
    (hκ : B≤κ) (hκstop : κ*ε≤stop) (hstop : 4*stop<1) :
    profile ε he B stop (κ*ε)≤cutoffConstant B Q c g κ stop*cost ε he (B*ε) := by
  have hB : 0<B := by linarith [h.1]
  have hc := h.2.2.2.1
  have hκε : B*ε≤κ*ε := mul_le_mul_of_nonneg_right hκ he.le
  have hcut := hκε.trans hκstop
  have hcp := cutoff_pos h he
  have hsp := hcp.trans_le hcut
  have hbase : 0<c*stop^g := mul_pos hc (Real.rpow_pos_of_pos hsp g)
  have hden := input_cost_pos h ε he stop hcut hsp hstop
  have hdenLower := input_cost_lower h ε he stop hcut hsp hstop
  have hgrowth := input_growth h ε he (B*ε) (κ*ε) le_rfl hcp hκε (by linarith)
  have heq : κ*ε/(B*ε)=κ/B := by field_simp
  rw [heq] at hgrowth
  have hcoef : 0≤(Q/c)*(κ/B)^g := by
    apply mul_nonneg (div_nonneg (by linarith [h.2.2.1]) hc.le)
    exact Real.rpow_nonneg (div_nonneg (hB.le.trans hκ) hB.le) _
  rw [profile,clipped_eq _ _ _ hκε hκstop]
  calc
    _ ≤ ((Q/c)*(κ/B)^g*cost ε he (B*ε))/cost ε he stop :=
      div_le_div_of_nonneg_right hgrowth hden.le
    _ = ((Q/c)*(κ/B)^g)*(cost ε he (B*ε)/cost ε he stop) := by ring
    _ ≤ ((Q/c)*(κ/B)^g)*(cost ε he (B*ε)/(c*stop^g)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (cost_nonneg ε he (B*ε)) hbase hdenLower) hcoef
    _ = _ := by unfold cutoffConstant; ring

theorem profile_cutoff_le_sourceArmCost (h : PublishedCircularArmInputs B C₄ Q c g)
    (ε : ℝ) (he : 0<ε) (stop κ : ℝ)
    (hκ : B≤κ) (hκstop : κ*ε≤stop) (hstop : 4*stop<1)
    (hB : 0<B) (hsmall : 4*(B*ε)<1) :
    profile ε he B stop (κ*ε)≤cutoffConstant B Q c g κ stop*
      sourceArmCost ε (B*ε) he (mul_pos hB he) hsmall := by
  rw [←cost_eq ε he (B*ε) (mul_pos hB he) hsmall]
  exact profile_cutoff_le_cost h ε he stop κ hκ hκstop hstop

#print axioms alpha_fourArm_at_mesh
#print axioms profile_cutoff_le_sourceArmCost
#print axioms profile_growth
#print axioms profile_quasi
#print axioms input_growth
end
end ExceptionalTimes.CircularStaticProfile


