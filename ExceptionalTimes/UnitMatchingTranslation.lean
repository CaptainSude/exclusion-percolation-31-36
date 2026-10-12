import ExceptionalTimes.CanonicalHexAnnuli

/-! Exact translation of every finite covered annulus to one of the two
unit-displacement matching phases. No uniformity in an infinite family of
translated quads is inferred from pointwise convergence. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.UnitMatchingTranslation

open PairSquareSewing CanonicalHexAnnuli ActivePartitionLaw DimerLaw ManyDimerLaw

def phase (x : Site) : Bool := decide (x.1%2≠0)

def partner (b : Bool) (v : Site) : Site :=
  if (v.1+(if b then 1 else 0))%2=0 then v+(1,0) else v-(1,0)

theorem unit_partner (v : Site) :
    PeriodicMatching.partner (1,0) v=if v.1%2=0 then v+(1,0) else v-(1,0) := by
  simp [PeriodicMatching.partner,PeriodicMatching.partnerOnAxis,PeriodicMatching.chooseAxis,
    PeriodicMatching.height,PeriodicMatching.coord,PeriodicMatching.add,PeriodicMatching.sub]
  split_ifs <;> ext <;> simp

theorem translated_partner (x v : Site) :
    PeriodicMatching.partner (1,0) (v+x)-x=partner (phase x) v := by
  have hp : (v.1+x.1)%2=(v.1+(if phase x then 1 else 0))%2 := by
    by_cases h : x.1%2=0 <;> simp [phase,h] <;> omega
  rw [unit_partner]
  simp only [Prod.fst_add,hp,partner]
  split_ifs <;> ext <;> simp <;> omega

def shiftSlot {B : Type*} (slot : B×Fin 2 ↪ Site) (x : Site) : B×Fin 2 ↪ Site where
  toFun b := slot b-x
  inj' := by
    intro a b h
    apply slot.injective
    have H := congrArg (fun v : Site => v+x) h
    simpa only [sub_add_cancel] using H

theorem shifted_pairs {B : Type*} (slot : B×Fin 2 ↪ Site) (x : Site)
    (hpair : ∀ b,slot (b,1)=PeriodicMatching.partner (1,0) (slot (b,0))) :
    ∀ b,shiftSlot slot x (b,1)=partner (phase x) (shiftSlot slot x (b,0)) := by
  intro b
  change slot (b,1)-x=partner (phase x) (slot (b,0)-x)
  rw [hpair,← translated_partner]
  simp only [sub_add_cancel]

theorem shift_decode {B : Type*} (slot : B×Fin 2 ↪ Site) (x : Site) (ω : B→Color) :
    pairDecode (shiftSlot slot x) ω=fun v => pairDecode slot ω (v+x) := by
  funext v
  by_cases he : ∃ b,shiftSlot slot x b=v
  · obtain ⟨b,rfl⟩ := he
    have hv : shiftSlot slot x b+x=slot b := sub_add_cancel _ _
    unfold pairDecode
    rw [hv,(shiftSlot slot x).injective.extend_apply,slot.injective.extend_apply]
  · have hn : ¬∃ b,slot b=v+x := by
      rintro ⟨b,hb⟩
      apply he
      exact ⟨b,by change slot b-x=v; rw [hb]; simp⟩
    unfold pairDecode
    rw [Function.extend_apply' _ _ _ he,Function.extend_apply' _ _ _ hn]

theorem arms_shift (x : Site) (r R : ℤ) (ω : Configuration) :
    HexFourArms x r R ω ↔ HexFourArms 0 r R (fun v => ω (v+x)) := by
  simp only [HexFourArms,add_zero]

theorem shifted_cover {B : Type*} (slot : B×Fin 2 ↪ Site) (x : Site) (r R : ℤ)
    (hcover : ∀ v∈region x r R,∃ b,slot b=v) :
    ∀ v∈region 0 r R,∃ b,shiftSlot slot x b=v := by
  intro v hv
  have hm : v+x∈region x r R := by simpa [region] using hv
  obtain ⟨b,hb⟩ := hcover (v+x) hm
  exact ⟨b,by change slot b-x=v; rw [hb]; simp⟩

theorem translated_probability {B : Type*} [Fintype B]
    (slot : B×Fin 2 ↪ Site) (x : Site) (r R : ℤ) (p : B→ℝ) :
    manyProbability p (fun ω => HexFourArms x r R (pairDecode slot ω))=
      manyProbability p (fun ω => HexFourArms 0 r R (pairDecode (shiftSlot slot x) ω)) := by
  congr 1
  funext ω
  apply propext
  rw [shift_decode]
  exact arms_shift x r R _

/-- Only two centered phase estimates are needed, including their literal
finite observation covers. -/
theorem all_centers_of_two_phases (r R : ℤ) (t bound : ℝ)
    (hphase : ∀ b : Bool,∀ k : ℕ,∀ slot : Fin k×Fin 2 ↪ Site,
      (∀ i,slot (i,1)=partner b (slot (i,0))) →
      (∀ v∈region 0 r R,∃ i,slot i=v) →
      manyProbability (fun _ => refreshProbability t)
        (fun ω => HexFourArms 0 r R (pairDecode slot ω))≤bound) :
    ∀ k : ℕ,∀ slot : Fin k×Fin 2 ↪ Site,
      (∀ i,slot (i,1)=PeriodicMatching.partner (1,0) (slot (i,0))) →
      ∀ x,(∀ v∈region x r R,∃ i,slot i=v) →
      manyProbability (fun _ => refreshProbability t)
        (fun ω => HexFourArms x r R (pairDecode slot ω))≤bound := by
  intro k slot hp x hc
  rw [translated_probability slot x r R]
  exact hphase (phase x) k (shiftSlot slot x) (shifted_pairs slot x hp)
    (shifted_cover slot x r R hc)

#print axioms all_centers_of_two_phases

end ExceptionalTimes.UnitMatchingTranslation
