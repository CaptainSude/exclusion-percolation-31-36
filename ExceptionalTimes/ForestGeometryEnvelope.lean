import ExceptionalTimes.ForestSelectionIntegral
import ExceptionalTimes.OptimizedForestStop
import ExceptionalTimes.SelectedPerturbation

/-! The actual per-selection geometry used in the semigroup estimate.
Degree zero is the static expectation bound; positive degrees use the
literal truncated Kruskal forest at their optimized stopping radius. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.ForestGeometryEnvelope
open PairSquareSewing NormalizedForestProfile SelectedPerturbation InsertionCounting

variable {B J : Type*} [Fintype B] [Fintype J]

noncomputable def envelope (G : (S : Finset B) → DimerGeometry S J)
    (cutoff stop D C K g : ℝ) (p : ℝ→ℝ) (S : Finset B) : ℝ :=
  if S=∅ then 1 else
    canonicalForestValue (G S) cutoff (OptimizedForestStop.radius stop D S.card) C K g
      (normalized p (OptimizedForestStop.radius stop D S.card))

omit [Fintype B] in
theorem envelope_empty (G : (S : Finset B) → DimerGeometry S J)
    (cutoff stop D C K g : ℝ) (p : ℝ→ℝ) :
    envelope G cutoff stop D C K g p ∅=1 := by simp [envelope]

omit [Fintype B] in
theorem envelope_nonneg (G : (S : Finset B) → DimerGeometry S J)
    (cutoff stop D C K g : ℝ) (p : ℝ→ℝ) (hp : ∀ t,0<p t) (S : Finset B) :
    0≤envelope G cutoff stop D C K g p S := by
  unfold envelope
  split_ifs
  · norm_num
  · unfold canonicalForestValue
    apply mul_nonneg (pow_nonneg (by positivity) _)
    apply div_nonneg
    · exact pow_nonneg (div_pos (hp _) (hp _)).le _
    · exact Finset.prod_nonneg (fun _ _ => (div_pos (hp _) (hp _)).le)

omit [Fintype J] in
 theorem geometryDegree_eq_selections (f : Finset B→ℝ) (k : ℕ) :
    geometryDegree f k=∑ S : Selections B k,f S.val := by
  unfold geometryDegree
  exact Finset.sum_subtype _ (by intro S; simp) _

omit [Fintype J] in
 theorem geometryDegree_zero (f : Finset B→ℝ) : geometryDegree f 0=f ∅ := by
  simp [geometryDegree,Finset.card_eq_zero,Finset.sum_filter]

omit [Fintype J] in
 theorem geometryDegree_gt_card (f : Finset B→ℝ) {k : ℕ} (hk : Fintype.card B<k) :
    geometryDegree f k=0 := by
  apply Finset.sum_eq_zero
  intro S hS
  have hcard := (Finset.mem_filter.mp hS).2
  have hle : S.card≤Fintype.card B := Finset.card_le_univ S
  omega

theorem envelope_degree (G : (S : Finset B) → DimerGeometry S J)
    (cutoff stop D C K g : ℝ) (p : ℝ→ℝ) {k : ℕ} (hk : 1≤k) :
    geometryDegree (envelope G cutoff stop D C K g p) k=
      ∑ S : Selections B k,canonicalForestValue (G S.val) cutoff
        (OptimizedForestStop.radius stop D k) C K g
        (normalized p (OptimizedForestStop.radius stop D k)) := by
  rw [geometryDegree_eq_selections]
  apply Finset.sum_congr rfl
  intro S _
  have hS : S.val≠∅ := by
    intro h
    have he := S.property
    rw [h,Finset.card_empty] at he
    omega
  simp only [envelope,ite_eq_right hS,S.property]

#print axioms envelope_degree
#print axioms envelope_nonneg
end ExceptionalTimes.ForestGeometryEnvelope

