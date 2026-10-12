import ExceptionalTimes.DimerProbeWitness
import ExceptionalTimes.FiniteSiteLaw

/-! Single-time marginals of the actual canonical product dimer law are
the original fair-site law. Therefore the finite quad/time alternatives
in each literal forest-life event are paid for by a finite union bound,
without independence between the two times. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw FiniteHaar

variable {B : Type*} [Fintype B]

theorem manyLaw_time_expect (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (t : Bool) (f : (B → Color) → ℝ) :
    (manyLaw p hp0 hp1).expect (fun z => f (if t then z.2 else z.1))=average f := by
  have h := many_expect_replica p hp0 hp1 (fun ω η => f (if t then η else ω))
  change (∑ z : (B → Color) × (B → Color), manyWeight p z.1 z.2*f (if t then z.2 else z.1))=_
  rw [Fintype.sum_prod_type,h]
  cases t <;> simp only [Bool.false_eq_true,ite_false,ite_true,FiniteLaw.expect_const]
  all_goals exact many_marginal_expect p hp0 hp1 f

noncomputable def canonicalBackground (slot : B × Fin 2 ↪ Site)
    (z : (B → Color) × (B → Color)) (t : Bool) : Configuration :=
  ActivePartitionLaw.pairDecode slot (if t then z.2 else z.1)

theorem canonicalBackground_marginal (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (t : Bool) (E : Configuration → Prop)
    (hlocal : ∀ ω η, (∀ v ∈ D, ω v=η v) → (E ω ↔ E η)) :
    probability (manyLaw p hp0 hp1) (fun z => E (canonicalBackground slot z t))=
      probability (fairSites D) (fun ω => E (completeColors D ω)) := by
  unfold probability canonicalBackground
  change (manyLaw p hp0 hp1).expect (fun z => (fun x => EnvironmentVariance.indicator (E (ActivePartitionLaw.pairDecode slot x))) (if t then z.2 else z.1)) = _
  exact (manyLaw_time_expect p hp0 hp1 t (fun x => EnvironmentVariance.indicator (E (ActivePartitionLaw.pairDecode slot x)))).trans
    (FiniteSiteLaw.average_pairDecode_fairSites slot D hcover E hlocal)

/-- Literal one-life event bound under the actual two-time canonical law.
The card(Q×Bool) cost counts only crossing/time tests. -/
theorem canonical_straightProbe_union_bound {Q : Type*} [Fintype Q]
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (board : Q → ℕ) (P : Probe) (hD : P.region ⊆ (D : Set Site))
    (hmesh : B₀*P.mesh≤P.innerRadius)
    (hg0 : 0≤g) (hg2 : g≤2) (hc : 0<c) (hC₃ : 0≤C₃) (hC₄ : 0≤C₄)
    (hC : 1≤C) (hKB : 1≤C₄*K) (hKH : 1≤C₃*K/c)
    (hprofile : ∀ t, 0<t → t≤P.outerRadius → 0<profile t)
    (hquasi : ∀ a b, 0<a → a<b → b≤P.outerRadius → α a b≤K*(profile a/profile b))
    (hlower : ∀ a b, 0<a → a≤b → b≤P.outerRadius → profile b≤C*(b/a)^g*profile a)
    (hfourlower : ∀ a b, B₀*P.mesh≤a → 0<a → a≤b → b≤P.outerRadius → c*(a/b)^g≤α a b) :
    probability (manyLaw p hp0 hp1)
      (fun z => ∃ q t, StraightProbeArms (board q) P (canonicalBackground slot z t)) ≤
      (Fintype.card (Q × Bool) : ℝ)*fullProbeConstant C₄ C₃ c C K g*
        (profile P.innerRadius/profile P.outerRadius) := by
  let E : (Q × Bool) → ((B → Color) × (B → Color)) → Prop :=
    fun qt z => StraightProbeArms (board qt.1) P (canonicalBackground slot z qt.2)
  have hprob : probability (manyLaw p hp0 hp1)
      (fun z => ∃ q t, StraightProbeArms (board q) P (canonicalBackground slot z t)) =
      probability (manyLaw p hp0 hp1) (fun z => ∃ qt, E qt z) := by
    apply probability_congr
    exact fun _ => ⟨fun ⟨q,t,h⟩ => ⟨(q,t),h⟩,fun ⟨⟨q,t⟩,h⟩ => ⟨q,t,h⟩⟩
  rw [hprob]
  apply (probability_exists_le (manyLaw p hp0 hp1) E).trans
  have hsingle (qt : Q × Bool) : probability (manyLaw p hp0 hp1) (E qt)≤
      fullProbeConstant C₄ C₃ c C K g*(profile P.innerRadius/profile P.outerRadius) := by
    change probability (manyLaw p hp0 hp1) (fun z => StraightProbeArms (board qt.1) P (canonicalBackground slot z qt.2))≤_
    rw [canonicalBackground_marginal p hp0 hp1 slot D hcover qt.2 _
      (fun ω η he => straightProbeArms_locality (board qt.1) P (fun v hv => he v (hD hv)))]
    exact straightProbe_probability_le_profile α profile hfour hthree (board qt.1) P D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hprofile hquasi hlower hfourlower
  have ht := Finset.sum_le_sum (fun qt (_ : qt∈Finset.univ) => hsingle qt)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using ht

#print axioms canonicalBackground_marginal
#print axioms canonical_straightProbe_union_bound

end ExceptionalTimes.PairSquareSewing


