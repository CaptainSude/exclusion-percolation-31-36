import ExceptionalTimes.DecorrelationLength
import ExceptionalTimes.GeometricAnnulusScales
import Mathlib.Data.Nat.Log

/-! Dyadic rounding costs at most a factor two. This lets a transfer proved
only along dyadic meshes supply all times in the energy argument, without
claiming convergence along unproved mesh sequences. -/

namespace ExceptionalTimes.DyadicScaleRounding

def IsDyadic (n : ℕ) : Prop := ∃ k : ℕ,n=2^k

def round (n : ℕ) : ℕ := 2^(Nat.log 2 n+1)

theorem round_dyadic (n : ℕ) : IsDyadic (round n) := ⟨_,rfl⟩

theorem le_round (n : ℕ) : n≤round n :=
  (Nat.lt_pow_succ_log_self (by norm_num : 1<2) n).le

theorem round_le_twice {n : ℕ} (hn : 0<n) : round n≤2*n := by
  have h := Nat.pow_log_le_self 2 hn.ne'
  dsimp [round]
  rw [pow_succ]
  omega

theorem mul_dyadic {m n : ℕ} (hm : IsDyadic m) (hn : IsDyadic n) :
    IsDyadic (m*n) := by
  obtain ⟨i,rfl⟩ := hm
  obtain ⟨j,rfl⟩ := hn
  exact ⟨i+j,(pow_add 2 i j).symm⟩

theorem scale_dyadic {M m : ℕ} (hM : IsDyadic M) (hm : IsDyadic m) (i : ℕ) :
    IsDyadic (GeometricAnnulusScales.scale M m i) := by
  obtain ⟨a,rfl⟩ := hM
  obtain ⟨b,rfl⟩ := hm
  refine ⟨(a+1)*i+b,?_⟩
  simp only [GeometricAnnulusScales.scale,pow_add,pow_mul,pow_one]
  ring

theorem times_256_dyadic {m : ℕ} (hm : IsDyadic m) : IsDyadic (256*m) :=
  mul_dyadic ⟨8,by norm_num⟩ hm

theorem exists_dyadic_scale (base : ℕ) (hbase : 0<base)
    {C v : ℝ} (hC : 0≤C) (hv : 0<v) (reference : ℕ→ℝ)
    (href : ∀ s,base≤s → reference s≤C*(s : ℝ)^(-v)) :
    ∃ D : ℝ,0≤D ∧ ∃ m : ℝ→ℕ,
      (∀ t,IsDyadic (m t)) ∧
      ∀ t,t∈Set.Ioo (0 : ℝ) 1 →
        base≤m t ∧ (m t : ℝ)≤D*t^(-(1/v)) ∧
          ∀ s,m t≤s → reference s≤t := by
  obtain ⟨D,hD,m,hm⟩ := DecorrelationLength.exists_integer_scale base hbase hC hv reference href
  refine ⟨2*D,by positivity,(fun t => round (m t)),(fun t => round_dyadic _),?_⟩
  intro t ht
  obtain ⟨hbm,hmt,hrefm⟩ := hm t ht
  have hp : 0<m t := hbase.trans_le hbm
  have hr : (round (m t) : ℝ)≤2*(m t : ℝ) := by exact_mod_cast round_le_twice hp
  refine ⟨hbm.trans (le_round _),?_,(fun s hs => hrefm s ((le_round _).trans hs))⟩
  calc
    _ ≤ 2*(m t : ℝ) := hr
    _ ≤ 2*(D*t^(-(1/v))) := mul_le_mul_of_nonneg_left hmt (by norm_num)
    _ = _ := by ring

#print axioms exists_dyadic_scale

end ExceptionalTimes.DyadicScaleRounding

