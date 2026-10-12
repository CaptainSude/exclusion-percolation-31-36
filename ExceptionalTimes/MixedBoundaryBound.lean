import ExceptionalTimes.MixedBoundaryProbability
import ExceptionalTimes.SplitArmProfile

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ArmEnlargement

noncomputable def bulkPieceProbability (P : Probe) (q : ℝ × ℝ) (D : Finset Site) : ℝ :=
  if hb : BulkPartActive P q then
    probability (fairSites D) (fun ω => FourArms (P.bulkPart q hb) (completeColors D ω)) else 1

noncomputable def halfPieceProbability (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (D : Finset Site) : ℝ :=
  if hh : HalfPartActive P q then
    probability (fairSites D) (fun ω => HalfThreeArms (P.halfPart H q hq hh) (completeColors D ω)) else 1

theorem mixed_probability_eq_product (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (D : Finset Site) :
    probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) =
      bulkPieceProbability P q D * halfPieceProbability P H q hq D := by
  by_cases hb : BulkPartActive P q <;> by_cases hh : HalfPartActive P q
  · rw [bulkPieceProbability,halfPieceProbability,dite_eq_left hb,dite_eq_left hh,
      ← bulk_half_probability_product _ _ D (P.bulk_half_disjoint H q hq hb hh)]
    apply probability_congr
    exact fun _ => ⟨fun h => ⟨h.1 hb,h.2 hh⟩,fun h => ⟨fun _ => h.1,fun _ => h.2⟩⟩
  · rw [bulkPieceProbability,halfPieceProbability,dite_eq_left hb,dite_eq_right hh,mul_one]
    apply probability_congr
    exact fun _ => ⟨fun h => h.1 hb,fun h => ⟨fun _ => h,fun ht => (hh ht).elim⟩⟩
  · rw [bulkPieceProbability,halfPieceProbability,dite_eq_right hb,dite_eq_left hh,one_mul]
    apply probability_congr
    exact fun _ => ⟨fun h => h.2 hh,fun h => ⟨fun ht => (hb ht).elim,fun _ => h⟩⟩
  · rw [bulkPieceProbability,halfPieceProbability,dite_eq_right hb,dite_eq_right hh,one_mul]
    have he : ∀ ω, MixedBoundaryArms P H q hq (completeColors D ω) ↔ True :=
      fun _ => ⟨fun _ => trivial,fun _ => ⟨fun ht => (hb ht).elim,fun ht => (hh ht).elim⟩⟩
    rw [probability_congr (fairSites D) he]
    simp [probability,EnvironmentVariance.indicator,FiniteLaw.expect_const]

/-- Local one-piece estimates plus proved geometric factorization give
the full mixed event, including every empty-piece case. -/
theorem mixed_probability_le_split (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ)
    (hq : q ∈ H.boundary) (D : Finset Site) (p : ℝ → ℝ) {KB KH : ℝ}
    (hKB : 1≤KB) (hKH : 1≤KH)
    (hbulk : ∀ hb : BulkPartActive P q,
      probability (fairSites D) (fun ω => FourArms (P.bulkPart q hb) (completeColors D ω)) ≤
        KB*(p P.innerRadius/p (min P.outerRadius (P.distanceTo q/8))))
    (hhalf : ∀ hh : HalfPartActive P q,
      probability (fairSites D) (fun ω => HalfThreeArms (P.halfPart H q hq hh) (completeColors D ω)) ≤
        KH*(p (8*max P.innerRadius (P.distanceTo q))/p (P.outerRadius/8))) :
    probability (fairSites D) (fun ω => MixedBoundaryArms P H q hq (completeColors D ω)) ≤
      (KB*KH)*splitProfileCost P q p := by
  let B := separatedArmCost (fun a b => p a/p b) P.innerRadius (min P.outerRadius (P.distanceTo q/8))
  let A := separatedArmCost (fun a b => p a/p b) (8*max P.innerRadius (P.distanceTo q)) (P.outerRadius/8)
  have hB : bulkPieceProbability P q D ≤ KB*B := by
    by_cases hb : BulkPartActive P q
    · have hb' : 4*P.innerRadius<min P.outerRadius (P.distanceTo q/8) := hb
      simpa only [bulkPieceProbability,dite_eq_left hb,B,separatedArmCost,ite_eq_left hb'] using hbulk hb
    · have hb' : ¬4*P.innerRadius<min P.outerRadius (P.distanceTo q/8) := hb
      simpa only [bulkPieceProbability,dite_eq_right hb,B,separatedArmCost,ite_eq_right hb',mul_one] using hKB
  have hA : halfPieceProbability P H q hq D ≤ KH*A := by
    by_cases hh : HalfPartActive P q
    · have hh' : 4*(8*max P.innerRadius (P.distanceTo q))<P.outerRadius/8 := hh
      simpa only [halfPieceProbability,dite_eq_left hh,A,separatedArmCost,ite_eq_left hh'] using hhalf hh
    · have hh' : ¬4*(8*max P.innerRadius (P.distanceTo q))<P.outerRadius/8 := hh
      simpa only [halfPieceProbability,dite_eq_right hh,A,separatedArmCost,ite_eq_right hh',mul_one] using hKH
  have hB0 : 0≤bulkPieceProbability P q D := by
    unfold bulkPieceProbability
    split_ifs
    · exact probability_nonneg _ _
    · norm_num
  have hA0 : 0≤halfPieceProbability P H q hq D := by
    unfold halfPieceProbability
    split_ifs
    · exact probability_nonneg _ _
    · norm_num
  rw [mixed_probability_eq_product]
  have h := mul_le_mul hB hA hA0 (hB0.trans hB)
  convert h using 1
  dsimp [splitProfileCost,B,A]
  ring

/-- The actual mixed event is bounded by the original four-arm profile.
All probability inputs are the two published individual arm estimates;
the distance-to-side and active/empty case analysis have been proved. -/
theorem mixed_probability_le_profile
    {B₀ C₄ C₃ c C Q g : ℝ} (α : ℝ → ℝ → ℝ) (p : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (P : Probe) (H : LatticeHalfPlane) (q : ℝ × ℝ) (hq : q ∈ H.boundary) (D : Finset Site)
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
    have hstat := hfour (P.bulkPart q hb) D hmesh ((P.bulkPart_region q hb).trans hD)
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

#print axioms mixed_probability_eq_product
#print axioms mixed_probability_le_profile

end ExceptionalTimes.PairSquareSewing
