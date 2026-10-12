import ExceptionalTimes.PolygonProbeChoice
import ExceptionalTimes.CanonicalLifeStatic

/-! The actual canonical two-time law has the same one-time marginal
for every literal polygon probe choice. Only the finite quad/time tests
are unioned; there is no enumeration of overwrite assignments. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.PairSquareSewing

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw

variable {B : Type*} [Fintype B]

/-- Literal one-life event bound under the actual two-time canonical law.
The card(Q×Bool) cost counts only crossing/time tests. -/
theorem canonical_polygonProbe_union_bound {Q : Type*} [Fintype Q]
    {B₀ C₄ C₃ c C K g : ℝ} (α : ℝ → ℝ → ℝ) (profile : ℝ → ℝ)
    (hfour : PublishedFourArmBound B₀ C₄ α)
    (hthree : PublishedHalfThreeArmBound B₀ C₃)
    (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (slot : B × Fin 2 ↪ Site) (D : Finset Site) (hcover : ∀ v ∈ D, ∃ ie, slot ie=v)
    (P : Probe) (choice : Q → PolygonArmChoice P) (hD : P.region ⊆ (D : Set Site))
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
    exact PolygonArmChoice.probability_le_profile α profile hfour hthree P (choice qt.1) D hD hmesh
      hg0 hg2 hc hC₃ hC₄ hC hKB hKH hprofile hquasi hlower hfourlower
  have ht := Finset.sum_le_sum (fun qt (_ : qt∈Finset.univ) => hsingle qt)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using ht

#print axioms canonical_polygonProbe_union_bound

end ExceptionalTimes.PairSquareSewing


