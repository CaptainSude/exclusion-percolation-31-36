import ExceptionalTimes.LocalProductLaw
import ExceptionalTimes.ManyDimerLaw

/-! The canonical two-time dimer law is literally a product over dimers.
Disjoint groups of whole dimers therefore give independent arbitrary
two-time events, without any independence assumption about the times. -/

open scoped Classical BigOperators

namespace ExceptionalTimes.CanonicalSpatialProduct

open EnvironmentVariance ProbeProduct ManyDimerLaw DimerLaw

variable {B A : Type*} [Fintype B]

def pairCoordinates : ((B → Color) × (B → Color)) ≃ (B → Color × Color) where
  toFun z b := (z.1 b,z.2 b)
  invFun x := (fun b => (x b).1,fun b => (x b).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem manyLaw_pi (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (f : ((B → Color) × (B → Color)) → ℝ) :
    (manyLaw p hp0 hp1).expect f =
      (FiniteLaw.pi (fun b => jointLaw (p b) (hp0 b) (hp1 b))).expect
        (fun x => f (pairCoordinates.symm x)) := by
  unfold FiniteLaw.expect
  rw [← (pairCoordinates (B := B)).symm.sum_comp]
  rfl

variable [Fintype A] [DecidableEq A]

theorem manyLaw_local_product (p : B → ℝ) (hp0 : ∀ b, 0≤p b) (hp1 : ∀ b, p b≤1)
    (S : A → Set B) (hdis : Pairwise (fun a b => Disjoint (S a) (S b)))
    (E : A → ((B → Color) × (B → Color)) → Prop)
    (hlocal : ∀ a ω η,
      (∀ b ∈ S a, ω.1 b=η.1 b ∧ ω.2 b=η.2 b) → (E a ω ↔ E a η)) :
    probability (manyLaw p hp0 hp1) (fun z => ∀ a, E a z)=
      ∏ a, probability (manyLaw p hp0 hp1) (E a) := by
  unfold probability
  simp_rw [manyLaw_pi]
  apply LocalProductLaw.pi_local_product _ ((fun _ => false),(fun _ => false)) S hdis
  intro a ω η he
  apply hlocal
  intro b hb
  exact ⟨congrArg Prod.fst (he hb),congrArg Prod.snd (he hb)⟩

#print axioms manyLaw_local_product

end ExceptionalTimes.CanonicalSpatialProduct
