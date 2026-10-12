import ExceptionalTimes.MixedCanonicalDictionary

/-! Monotonicity of two-time quadratic coefficients in refresh parameters.
This applies to arbitrary real functions, in particular to nonmonotone
alternating-arm events. The flag coupling is explicit. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.CanonicalParameterOrder

open CanonicalHarris FiniteHaar DimerLaw ManyDimerLaw EnvironmentVariance MixedCanonicalLaw

variable {B : Type*} [Fintype B]

def flagCoupling (p q : ℝ) (s t : Bool) : ℝ :=
  if s then (if t then p else 0) else (if t then q-p else 1-q)

theorem flagCoupling_nonneg {p q : ℝ} (hp : 0≤p) (hpq : p≤q) (hq : q≤1)
    (s t : Bool) : 0≤flagCoupling p q s t := by
  cases s <;> cases t <;> simp [flagCoupling] <;> linarith

theorem flagCoupling_left (p q : ℝ) (s : Bool) :
    (∑ t : Bool,flagCoupling p q s t)=if s then p else 1-p := by
  cases s <;> simp [flagCoupling]

theorem flagCoupling_right (p q : ℝ) (t : Bool) :
    (∑ s : Bool,flagCoupling p q s t)=if t then q else 1-q := by
  cases t <;> simp [flagCoupling]

noncomputable def couplingWeight (p q : B→ℝ) (s t : B→Bool) : ℝ :=
  ∏ b,flagCoupling (p b) (q b) (s b) (t b)

theorem couplingWeight_left (p q : B→ℝ) (s : B→Bool) :
    (∑ t : B→Bool,couplingWeight p q s t)=flagWeight p s := by
  unfold couplingWeight flagWeight
  rw [← Fintype.prod_sum (fun b t => flagCoupling (p b) (q b) (s b) t)]
  exact Finset.prod_congr rfl (fun b _ => flagCoupling_left (p b) (q b) (s b))

theorem couplingWeight_right (p q : B→ℝ) (t : B→Bool) :
    (∑ s : B→Bool,couplingWeight p q s t)=flagWeight q t := by
  unfold couplingWeight flagWeight
  rw [← Fintype.prod_sum (fun b s => flagCoupling (p b) (q b) s (t b))]
  exact Finset.prod_congr rfl (fun b _ => flagCoupling_right (p b) (q b) (t b))

theorem couplingWeight_of_not_le (p q : B→ℝ) {s t : B→Bool} (h : ¬s≤t) :
    couplingWeight p q s t=0 := by
  classical
  have hbad : ∃ b,s b=true ∧ t b=false := by
    by_contra! hh
    apply h
    intro b
    cases hs : s b <;> cases ht : t b <;> simp_all
  obtain ⟨b,hs,ht⟩ := hbad
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [flagCoupling,hs,ht])

theorem flagAverage_parameter_antitone (p q : B→ℝ)
    (hp : ∀ b,0≤p b) (hpq : p≤q) (hq : ∀ b,q b≤1)
    (f : (B→Bool)→ℝ) (hf : Antitone f) : flagAverage q f≤flagAverage p f := by
  have hleft : (∑ s,∑ t,couplingWeight p q s t*f s)=flagAverage p f := by
    simp only [← Finset.sum_mul,couplingWeight_left,flagAverage]
  have hright : (∑ s,∑ t,couplingWeight p q s t*f t)=flagAverage q f := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,couplingWeight_right,flagAverage]
  rw [← hleft,← hright]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  by_cases hst : s≤t
  · exact mul_le_mul_of_nonneg_left (hf hst) (Finset.prod_nonneg
      (fun b _ => flagCoupling_nonneg (hp b) (hpq b) (hq b) (s b) (t b)))
  · rw [couplingWeight_of_not_le p q hst]
    simp

theorem canonical_parameter_antitone {G X : Type*} [Group G] [Fintype G]
    [Fintype X] [MulAction G X] (p q : B→ℝ)
    (hp : ∀ b,0≤p b) (hpq : p≤q) (hq : ∀ b,q b≤1)
    (f : (B→X)→ℝ) : canonical (G := G) q f≤canonical (G := G) p f :=
  flagAverage_parameter_antitone p q hp hpq hq _ (conditional_antitone f)

theorem manyProbability_parameter_antitone (p q : B→ℝ)
    (hp : ∀ b,0≤p b) (hpq : p≤q) (hq : ∀ b,q b≤1)
    (E : (B→Color)→Prop) : manyProbability q E≤manyProbability p E := by
  let := coordinateAction (G := PairGroup) (I := Fin 2)
  change (∑ a,∑ b,manyWeight q a b*(indicator (E a)*indicator (E b)))≤
    ∑ a,∑ b,manyWeight p a b*(indicator (E a)*indicator (E b))
  rw [← real_canonical_eq_joint,← real_canonical_eq_joint]
  exact canonical_parameter_antitone p q hp hpq hq _

variable {O : Type*} [Fintype O]

theorem mixed_parameter_antitone (p q : B→ℝ)
    (hp : ∀ b,0≤p b) (hpq : p≤q) (hq : ∀ b,q b≤1)
    (F : ((B→Color)×(O→Color))→ℝ) : mixed q F≤mixed p F := by
  let := coordinateAction (G := PairGroup) (I := Fin 2)
  exact canonical_parameter_antitone p q hp hpq hq (smooth F)

/-- Increasing the canonical refresh probabilities and replacing any
outside canonical histories by independent colors can only lower a
paired event probability. The event need not be increasing. -/
theorem mixedProbability_le_manyProbability (p q : B→ℝ) (r : O→ℝ)
    (hp : ∀ b,0≤p b) (hpq : p≤q) (hq : ∀ b,q b≤1)
    (hr0 : ∀ o,0≤r o) (hr1 : ∀ o,r o≤1)
    (E : ((B→Color)×(O→Color))→Prop) :
    mixedProbability q E≤manyProbability (Sum.elim p r)
      (fun x => E (fun b => x (.inl b),fun o => x (.inr o))) := by
  have hp1 : ∀ b,p b≤1 := fun b => (hpq b).trans (hq b)
  apply (mixed_parameter_antitone p q hp hpq hq (fun x => indicator (E x))).trans
  have h := mixed_le_bothCanonical p r hp hp1 hr0 hr1 (fun x => indicator (E x))
  rwa [MixedCanonicalDictionary.bothCanonical_indicator_eq_manyProbability] at h

#print axioms flagAverage_parameter_antitone
#print axioms manyProbability_parameter_antitone
#print axioms mixedProbability_le_manyProbability

end ExceptionalTimes.CanonicalParameterOrder
