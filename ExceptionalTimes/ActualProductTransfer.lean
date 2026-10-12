import ExceptionalTimes.SelectedPerturbation
import ExceptionalTimes.EffectiveDimerInsertion

/-! Passing from the sewn first derivatives to the actual finite semigroups.
The geometric bounds are explicit hypotheses in this general analytic lemma. -/

open scoped Classical BigOperators Topology
namespace ExceptionalTimes.ActualProductTransfer
noncomputable section
open Filter DimerLaw DimerExpansion CenteredBlocks BlockExpansion ExpansionLimit
open PairSquareSewing EnvironmentVariance SelectedPerturbation EffectiveDimerInsertion

noncomputable def baseLaw : FiniteLaw History := jointLaw 0 (by norm_num) (by norm_num)

variable {B : Type*} [Fintype B]

theorem scaled_remainder (rule : Rule) (f : (B→History)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound (fun _ => baseLaw) f G) (hG0 : ∀ S,0≤G S)
    {scale T c : ℝ} (hs : 0≤scale) (ht : 0<T*scale) (ht1 : T*scale≤1)
    (k : ℕ) (hm : scale^k*geometryDegree G k≤c) :
    |effectiveCoefficient rule f scale T k-scaledCoefficient rule f scale k|≤
      c*((T*scale)*k*(1+T*scale)^(k-1)) := by
  have h := coefficient_remainder (fun _ : B => baseLaw) f G hG hG0
    (fun _ => insertion rule) (fun _ => correction rule (T*scale))
    (fun _ => insertion_centered rule) (fun _ => correction_centered rule _)
    (by norm_num : (0:ℝ)≤1) ht.le
    (fun _ => insertion_variation rule) (fun _ => correction_variation rule ht ht1) k
  change |coefficient (fun _ : B => base) (fun _ => effective rule (T*scale)) f k-
    coefficient (fun _ : B => base) (fun _ => insertion rule) f k|≤_ at h
  unfold effectiveCoefficient scaledCoefficient
  rw [←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg hs _)]
  calc
    _ ≤ scale^k*(geometryDegree G k*((T*scale)*k*(1+T*scale)^(k-1))) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hs _)
    _ = (scale^k*geometryDegree G k)*((T*scale)*k*(1+T*scale)^(k-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)

theorem effective_bound (rule : Rule) (f : (B→History)→ℝ) (G : Finset B→ℝ)
    (hG : GeometryBound (fun _ => baseLaw) f G) (hG0 : ∀ S,0≤G S)
    {scale T c : ℝ} (hs : 0≤scale) (ht : 0<T*scale) (ht1 : T*scale≤1)
    (k : ℕ) (hm : scale^k*geometryDegree G k≤c) :
    |effectiveCoefficient rule f scale T k|≤c*2^k := by
  have h := coefficient_bound (fun _ : B => baseLaw) f G hG hG0
    (fun _ => effective rule (T*scale)) (fun _ => effective_centered rule _)
    (by norm_num : (0:ℝ)≤2) (fun _ => effective_variation rule ht ht1) k
  change |coefficient (fun _ : B => base) (fun _ => effective rule (T*scale)) f k|≤_ at h
  unfold effectiveCoefficient
  rw [abs_mul,abs_of_nonneg (pow_nonneg hs _)]
  calc
    _ ≤ scale^k*(geometryDegree G k*2^k) := mul_le_mul_of_nonneg_left h (pow_nonneg hs _)
    _ = (scale^k*geometryDegree G k)*2^k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)

variable {Bs : ℕ→Type*} [∀ n,Fintype (Bs n)]

theorem correction_tendsto_zero (rule : Rule) (f : ∀ n,(Bs n→History)→ℝ)
    (G : ∀ n,Finset (Bs n)→ℝ) (scale : ℕ→ℝ) (c : ℕ→ℝ)
    (hG : ∀ᶠ n in atTop,GeometryBound (fun _ => baseLaw) (f n) (G n) ∧ ∀ S,0≤G n S)
    (hpos : ∀ᶠ n in atTop,0<scale n)
    (hscale : Tendsto scale atTop (𝓝 0))
    (hm : ∀ᶠ n in atTop,∀ k,(scale n)^k*geometryDegree (G n) k≤c k)
    {T : ℝ} (hT : 0<T) (k : ℕ) :
    Tendsto (fun n => effectiveCoefficient rule (f n) (scale n) T k-
      scaledCoefficient rule (f n) (scale n) k) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => T*scale n) atTop (𝓝 0) := by
    simpa using hscale.const_mul T
  have ht1 : ∀ᶠ n in atTop,T*scale n≤1 := (ht.eventually (gt_mem_nhds (by norm_num))).mono (fun _ h => h.le)
  have herr : Tendsto (fun n => c k*((T*scale n)*k*(1+T*scale n)^(k-1))) atTop (𝓝 0) := by
    convert (((ht.mul_const (k:ℝ)).mul ((tendsto_const_nhds.add ht).pow (k-1))).const_mul (c k)) using 1; simp
  apply squeeze_zero_norm' ?_ herr
  filter_upwards [hG,hpos,hm,ht1] with n hn hp hb ht'
  rw [Real.norm_eq_abs]
  exact scaled_remainder rule (f n) (G n) hn.1 hn.2 hp.le (mul_pos hT hp) ht' k (hb k)


theorem effective_series_summable (rule : Rule) (f : (B→History)→ℝ) (scale T : ℝ) :
    Summable (fun k : ℕ => T^k*effectiveCoefficient rule f scale T k) := by
  apply summable_of_ne_finset_zero (s := Finset.range (Fintype.card B+1))
  intro k hk
  have hc : Fintype.card B<k := by
    simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hk
  simp only [effectiveCoefficient,coefficient_eq_zero_of_card_lt _ _ _ hc,mul_zero]

/-- A common summable geometric degree bound and the proved fixed-degree
sewing limits imply convergence of the actual semigroup products. -/
theorem actual_product_transfer (f : ∀ n,(Bs n→History)→ℝ)
    (G : ∀ n,Finset (Bs n)→ℝ) (scale : Rule→ℕ→ℝ) (c : ℕ→ℝ)
    (hG : ∀ᶠ n in atTop,GeometryBound (fun _ => baseLaw) (f n) (G n) ∧ ∀ S,0≤G n S)
    (hpos : ∀ rule,∀ᶠ n in atTop,0<scale rule n)
    (hscale : ∀ rule,Tendsto (scale rule) atTop (𝓝 0))
    (hm : ∀ rule,∀ᶠ n in atTop,∀ k,(scale rule n)^k*geometryDegree (G n) k≤c k)
    (hraw : ∀ k,Tendsto (fun n =>
      scaledCoefficient .canonical (f n) (scale .canonical n) k-
      scaledCoefficient .refresh (f n) (scale .refresh n) k) atTop (𝓝 0))
    {T : ℝ} (hT : 0<T)
    (hsum : Summable (fun k : ℕ => 2*(2*T)^k*c k)) :
    Tendsto (fun n =>
      kernel (fun _ : Bs n => law .canonical (T*scale .canonical n)) (f n)-
      kernel (fun _ : Bs n => law .refresh (T*scale .refresh n)) (f n)) atTop (𝓝 0) := by
  let a := fun n k => T^k*(effectiveCoefficient .canonical (f n) (scale .canonical n) T k-
    effectiveCoefficient .refresh (f n) (scale .refresh n) T k)
  have hdegree : ∀ k,Tendsto (fun n => a n k) atTop (𝓝 0) := by
    intro k
    have hC := correction_tendsto_zero .canonical f G (scale .canonical) c hG
      (hpos .canonical) (hscale .canonical) (hm .canonical) hT k
    have hM := correction_tendsto_zero .refresh f G (scale .refresh) c hG
      (hpos .refresh) (hscale .refresh) (hm .refresh) hT k
    have h := ((hC.add (hraw k)).sub hM).const_mul (T^k)
    convert h using 1
    · funext n
      dsimp [a]
      ring
    · ring
  have ht1 (rule : Rule) : ∀ᶠ n in atTop,T*scale rule n≤1 := by
    have ht : Tendsto (fun n => T*scale rule n) atTop (𝓝 0) := by
      simpa using (hscale rule).const_mul T
    exact (ht.eventually (gt_mem_nhds (by norm_num))).mono (fun _ h => h.le)
  have hbound : ∀ᶠ n in atTop,∀ k,‖a n k‖≤2*(2*T)^k*c k := by
    filter_upwards [hG,hpos .canonical,hpos .refresh,hm .canonical,hm .refresh,
      ht1 .canonical,ht1 .refresh] with n hn hpC hpM hbC hbM htC htM k
    have hc := effective_bound .canonical (f n) (G n) hn.1 hn.2 hpC.le
      (mul_pos hT hpC) htC k (hbC k)
    have hm' := effective_bound .refresh (f n) (G n) hn.1 hn.2 hpM.le
      (mul_pos hT hpM) htM k (hbM k)
    rw [Real.norm_eq_abs]
    dsimp [a]
    rw [abs_mul,abs_of_nonneg (pow_nonneg hT.le _)]
    calc
      _ ≤ T^k*(c k*2^k+c k*2^k) := mul_le_mul_of_nonneg_left
        ((abs_sub _ _).trans (add_le_add hc hm')) (pow_nonneg hT.le _)
      _ = _ := by rw [mul_pow]; ring
  have hlim : Tendsto (fun n => ∑' k,a n k) atTop (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence hsum hdegree hbound
  apply hlim.congr'
  filter_upwards [hpos .canonical,hpos .refresh] with n hpC hpM
  rw [actual_series .canonical _ _ _ (mul_pos hT hpC).ne',
    actual_series .refresh _ _ _ (mul_pos hT hpM).ne',
    ←(effective_series_summable .canonical (f n) (scale .canonical n) T).tsum_sub
      (effective_series_summable .refresh (f n) (scale .refresh n) T)]
  apply tsum_congr
  intro k
  dsimp [a]
  ring

/-- The forest majorant is summable at every finite positive macroscopic time. -/
theorem actual_product_transfer_of_forest (f : ∀ n,(Bs n→History)→ℝ)
    (G : ∀ n,Finset (Bs n)→ℝ) (scale : Rule→ℕ→ℝ) {A β : ℝ}
    (hA : 0≤A) (hβ : 0<β)
    (hG : ∀ᶠ n in atTop,GeometryBound (fun _ => baseLaw) (f n) (G n) ∧ ∀ S,0≤G n S)
    (hpos : ∀ rule,∀ᶠ n in atTop,0<scale rule n)
    (hscale : ∀ rule,Tendsto (scale rule) atTop (𝓝 0))
    (hm : ∀ rule,∀ᶠ n in atTop,∀ k,(scale rule n)^k*geometryDegree (G n) k≤
      A^k*(k:ℝ)^(-β*k))
    (hraw : ∀ k,Tendsto (fun n =>
      scaledCoefficient .canonical (f n) (scale .canonical n) k-
      scaledCoefficient .refresh (f n) (scale .refresh n) k) atTop (𝓝 0))
    {T : ℝ} (hT : 0<T) :
    Tendsto (fun n =>
      kernel (fun _ : Bs n => law .canonical (T*scale .canonical n)) (f n)-
      kernel (fun _ : Bs n => law .refresh (T*scale .refresh n)) (f n)) atTop (𝓝 0) := by
  apply actual_product_transfer f G scale (fun k => A^k*(k:ℝ)^(-β*k))
    hG hpos hscale hm hraw hT
  have h := (ForestCounting.summable_superfactor
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hT.le) hA) hβ).mul_left 2
  convert h using 1
  funext k
  rw [mul_pow]
  ring

#print axioms correction_tendsto_zero
#print axioms actual_product_transfer
end
end ExceptionalTimes.ActualProductTransfer



