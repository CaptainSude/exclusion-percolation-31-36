import ExceptionalTimes.FiniteMatchingNormalization
import ExceptionalTimes.Model

/-! Literal rate-one nearest-neighbor exchanges on the triangular
lattice form a RateKernel. The rate is one on each of the six adjacent
displacements and zero elsewhere. -/

namespace ExceptionalTimes.NearestNeighborRates

open scoped Classical

noncomputable def rate (z : Site) : ℝ := if TriangularAdj (0,0) z then 1 else 0

theorem rate_nonneg (z : Site) : 0≤rate z := by
  unfold rate
  split_ifs <;> norm_num

theorem rate_symmetric (z : Site) : rate (-z)=rate z := by
  have h : TriangularAdj (0,0) (-z) ↔ TriangularAdj (0,0) z := by
    simp only [TriangularAdj,Prod.fst_neg,Prod.snd_neg]
    omega
  simp only [rate,h]

theorem rate_diagonal : rate 0=0 := by
  norm_num [rate,TriangularAdj]

theorem rate_finite_support : Function.HasFiniteSupport rate := by
  apply (latticeBox 1).finite_toSet.subset
  intro z hz
  have h : TriangularAdj (0,0) z := by
    by_contra hn
    exact hz (by simp [rate,hn])
  exact mem_latticeBox_succ_of_adj (by simp [latticeBox]) h

theorem rate_summable : Summable rate := summable_of_hasFiniteSupport rate_finite_support

theorem rate_unit : rate (1,0)=1 := by norm_num [rate,TriangularAdj]

noncomputable def kernel : RateKernel where
  rate := rate
  nonneg := rate_nonneg
  symmetric := rate_symmetric
  diagonal := rate_diagonal
  summable := rate_summable
  positive_mass := rate_summable.tsum_pos rate_nonneg (1,0) (by rw [rate_unit]; norm_num)

theorem pairRate_eq (x y : Site) : kernel.pairRate x y=if TriangularAdj x y then 1 else 0 := by
  have h : TriangularAdj (0,0) (y-x) ↔ TriangularAdj x y := by
    simp only [TriangularAdj,Prod.fst_sub,Prod.snd_sub]
    omega
  simp only [RateKernel.pairRate,kernel,rate,h]

#print axioms kernel
#print axioms pairRate_eq

end ExceptionalTimes.NearestNeighborRates
