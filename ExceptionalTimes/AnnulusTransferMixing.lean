import ExceptionalTimes.DyadicFixedAspectEnergy
import ExceptionalTimes.DyadicAspectChoice
import ExceptionalTimes.UnitMatchingTranslation
import ExceptionalTimes.IndependentAnnulusInput

/-! The new finite-annulus comparison plus the new canonical clock lower
bound imply the exact dyadic mixing input of the dimension theorem.
Both new premises remain visible. Only independent mixing is published. -/

open scoped Classical

namespace ExceptionalTimes.AnnulusTransferMixing

open PairSquareSewing CanonicalHexAnnuli DimerLaw ManyDimerLaw ActivePartitionLaw
open DyadicScaleRounding DyadicFixedAspectEnergy IndependentAnnulusInput

/-- The remaining canonical calibration bound on the exact global jump sum. -/
def NewClockControl (J : ℕ→ℝ) : Prop :=
  ∃ N : ℕ,(∀ n,N≤n → 0<J n) ∧
    ∀ η : ℝ,0<η → η<3/4 → ∃ C : ℝ,0≤C ∧
      ∀ n,N≤n → 1/(2*J n)≤C*((2^n : ℕ) : ℝ)^(-(3/4-η))

/-- NEW, not a literature input: the exact annular consequence of the
finite-quad transfer. The same threshold covers both matching phases and
all finite enumerations covering the tested annulus. -/
def NewCenteredAnnulusTransfer (J : ℕ→ℝ) : Prop :=
  ∀ M : ℕ,2≤M → ∀ T : ℝ,0<T → ∀ δ : ℝ,0<δ →
    ∃ N : ℕ,∀ n,N≤n → ∀ b : Bool,∀ k : ℕ,∀ slot : Fin k×Fin 2 ↪ Site,
      (∀ i,slot (i,1)=UnitMatchingTranslation.partner b (slot (i,0))) →
      (∀ v∈region 0 ((2^n : ℕ) : ℤ) ((M*2^n : ℕ) : ℤ),∃ i,slot i=v) →
      manyProbability (fun _ => refreshProbability (T/(2*J n)))
        (fun ω => HexFourArms 0 ((2^n : ℕ) : ℤ) ((M*2^n : ℕ) : ℤ) (pairDecode slot ω)) ≤
          annularProbability M n (T/pivotalMean n)+δ

private theorem exponent_le_of_pow_le {a b : ℕ} (h : 2^a≤2^b) : a≤b := by
  by_contra hn
  have hp := Nat.pow_lt_pow_right (by norm_num : 1<2) (Nat.lt_of_not_ge hn)
  omega

theorem dyadic_mixing_of_new_transfer
    (hsource : PublishedIndependentAnnulusMixing) (J : ℕ→ℝ)
    (hclock : NewClockControl J) (htransfer : NewCenteredAnnulusTransfer J) :
    NewDyadicFixedAspectMixing (1,0) := by
  obtain ⟨C,hC,hind⟩ := hsource
  obtain ⟨M,hM,hMd,hgap⟩ := DyadicAspectChoice.exists_aspect C
  let target : ℝ := (2*(M : ℝ))^(-(17/8 : ℝ))
  have htarget : 0<target := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨T,hT,Nind,hind⟩ := hind M hM (target/4) (by positivity)
  obtain ⟨Ntr,htr⟩ := htransfer M hM T hT (target/4) (by positivity)
  obtain ⟨Nclock,hJ,hpower⟩ := hclock
  let N := max Nclock (max Nind Ntr)
  have hNc : Nclock≤N := le_max_left _ _
  have hNi : Nind≤N := (le_max_left _ _).trans (le_max_right _ _)
  have hNt : Ntr≤N := (le_max_right _ _).trans (le_max_right _ _)
  let refTime : ℕ→ℝ := fun s => if IsDyadic s then T/(2*J (Nat.log 2 s)) else 0
  have href (n : ℕ) : refTime (2^n)=T/(2*J n) := by
    simp only [refTime,ite_eq_left (show IsDyadic (2^n) from ⟨n,rfl⟩),Nat.log_pow (by norm_num : 1<2)]
  refine ⟨M,hM,hMd,1/8,by norm_num,2^N,refTime,?_,?_,?_⟩
  · intro s hs
    by_cases hd : IsDyadic s
    · obtain ⟨n,rfl⟩ := hd
      rw [href]
      exact div_nonneg hT.le (mul_nonneg (by norm_num) (hJ n (hNc.trans (exponent_le_of_pow_le hs))).le)
    · simp only [refTime,ite_eq_right hd,le_refl]
  · intro η hη0 hη1
    obtain ⟨D,hD,hDpower⟩ := hpower η hη0 hη1
    refine ⟨T*D,mul_nonneg hT.le hD,?_⟩
    intro s hs
    by_cases hd : IsDyadic s
    · obtain ⟨n,rfl⟩ := hd
      rw [href]
      have h := mul_le_mul_of_nonneg_left (hDpower n (hNc.trans (exponent_le_of_pow_le hs))) hT.le
      convert h using 1 <;> ring
    · simp only [refTime,ite_eq_right hd]
      positivity
  · intro k slot hp x s hs hsd hcover
    obtain ⟨n,rfl⟩ := hsd
    rw [href]
    have hn : N≤n := exponent_le_of_pow_le hs
    have hi := hind n (hNi.trans hn)
    have hg : C*(M : ℝ)^(-(9/4 : ℝ))<target/4 := hgap
    apply UnitMatchingTranslation.all_centers_of_two_phases
      ((2^n : ℕ) : ℤ) ((M*2^n : ℕ) : ℤ) (T/(2*J n))
      ((2*(M : ℝ))^(-(2+(1/8 : ℝ)))) ?_ k slot hp x hcover
    intro b k' slot' hp' hc'
    have hc := htr n (hNt.trans hn) b k' slot' hp' hc'
    have he : (2*(M : ℝ))^(-(2+(1/8 : ℝ)))=target := by norm_num [target]
    rw [he]
    linarith

#print axioms dyadic_mixing_of_new_transfer

end ExceptionalTimes.AnnulusTransferMixing

