import ExceptionalTimes.CanonicalParameterOrder
import ExceptionalTimes.CanonicalSpatialProduct
import ExceptionalTimes.CanonicalRadialLaw

/-! Scale amplification under the actual canonical product law. The
only probability estimates supplied below are individual fixed-aspect
event bounds at reference times. Spatial independence and extension to
later times are proved from the literal dimer law. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.CanonicalScaleProduct

open CanonicalParameterOrder CanonicalSpatialProduct CanonicalRadialLaw
open ManyDimerLaw DimerLaw EnvironmentVariance ProbeProduct

theorem refreshProbability_mono : Monotone refreshProbability := by
  intro s t hst
  unfold refreshProbability
  have he := Real.exp_le_exp.mpr (neg_le_neg hst)
  linarith

variable {B A : Type*} [Fintype B] [Fintype A]

theorem many_time_antitone (E : (B → Color) → Prop) {s t : ℝ}
    (hs : 0≤s) (hst : s≤t) :
    manyProbability (fun _ => refreshProbability t) E≤
      manyProbability (fun _ => refreshProbability s) E :=
  manyProbability_parameter_antitone _ _ (fun _ => refreshProbability_nonneg hs)
    (fun _ => refreshProbability_mono hst) (fun _ => refreshProbability_le_one t) E

theorem local_event_product (p : B → ℝ) (hp0 : ∀ b,0≤p b) (hp1 : ∀ b,p b≤1)
    (S : A → Set B) (hdis : Pairwise (fun a b => Disjoint (S a) (S b)))
    (E : A → (B → Color) → Prop)
    (hlocal : ∀ a x y, Set.EqOn x y (S a) → (E a x ↔ E a y)) :
    manyProbability p (fun x => ∀ a,E a x)=∏ a,manyProbability p (E a) := by
  classical
  simp_rw [manyProbability_eq_joint p hp0 hp1]
  have h := manyLaw_local_product p hp0 hp1 S hdis
    (fun a z => E a z.1 ∧ E a z.2) (by
      intro a x y he
      exact and_congr (hlocal a x.1 y.1 (fun b hb => (he b hb).1))
        (hlocal a x.2 y.2 (fun b hb => (he b hb).2)))
  have he : probability (manyLaw p hp0 hp1)
      (fun z => (∀ a,E a z.1) ∧ ∀ a,E a z.2)=
      probability (manyLaw p hp0 hp1) (fun z => ∀ a,E a z.1 ∧ E a z.2) := by
    apply probability_congr
    intro z
    exact forall_and.symm
  exact he.trans h

/-- The reference time may depend on the annulus. Monotonicity is valid
for nonmonotone events, including alternating arms. -/
theorem required_events_bound (S : A → Set B)
    (hdis : Pairwise (fun a b => Disjoint (S a) (S b)))
    (E : A → (B → Color) → Prop) (large : (B → Color) → Prop)
    (hlocal : ∀ a x y, Set.EqOn x y (S a) → (E a x ↔ E a y))
    (hnecessary : ∀ x,large x → ∀ a,E a x)
    (reference : A → ℝ) (t : ℝ) (ht : 0≤t)
    (href0 : ∀ a,0≤reference a) (href : ∀ a,reference a≤t)
    (bound : A → ℝ)
    (hbound : ∀ a,manyProbability (fun _ => refreshProbability (reference a)) (E a)≤bound a) :
    manyProbability (fun _ => refreshProbability t) large≤∏ a,bound a := by
  have hp0 : ∀ _ : B,0≤refreshProbability t := fun _ => refreshProbability_nonneg ht
  have hp1 : ∀ _ : B,refreshProbability t≤1 := fun _ => refreshProbability_le_one t
  calc
    _ ≤ manyProbability (fun _ => refreshProbability t) (fun x => ∀ a,E a x) :=
      many_mono _ hp0 hp1 hnecessary
    _ = ∏ a,manyProbability (fun _ => refreshProbability t) (E a) :=
      local_event_product _ hp0 hp1 S hdis E hlocal
    _ ≤ _ := Finset.prod_le_prod₀ (fun a _ => many_nonneg _ hp0 hp1 (E a))
      (fun a _ => (many_time_antitone (E a) (href0 a) (href a)).trans (hbound a))

theorem required_events_geometric (N : ℕ) (S : Fin N → Set B)
    (hdis : Pairwise (fun a b => Disjoint (S a) (S b)))
    (E : Fin N → (B → Color) → Prop) (large : (B → Color) → Prop)
    (hlocal : ∀ a x y, Set.EqOn x y (S a) → (E a x ↔ E a y))
    (hnecessary : ∀ x,large x → ∀ a,E a x)
    (reference : Fin N → ℝ) (t : ℝ) (ht : 0≤t)
    (href0 : ∀ a,0≤reference a) (href : ∀ a,reference a≤t)
    (β : ℝ)
    (hbound : ∀ a,manyProbability (fun _ => refreshProbability (reference a)) (E a)≤β) :
    manyProbability (fun _ => refreshProbability t) large≤β^N := by
  simpa using required_events_bound S hdis E large hlocal hnecessary reference t ht href0 href
    (fun _ => β) hbound

#print axioms many_time_antitone
#print axioms required_events_geometric

end ExceptionalTimes.CanonicalScaleProduct
