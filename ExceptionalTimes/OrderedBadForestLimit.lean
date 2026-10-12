import ExceptionalTimes.ForestBadLocation
import ExceptionalTimes.ForestSelectionIntegral
import ExceptionalTimes.UnitClockControl

/-! Negligible polygon/collision mass for actual ordered selections.
The controlling forest bound and the lattice bad-location estimate have
already been proved; the injection below removes no needed configurations. -/
open Filter
open scoped Classical BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.OrderedBadForestLimit
noncomputable section
open PairSquareSewing InsertionCounting ForestSelectionIntegral ForestBadLocation
open LatticeBoundaryMass IndependentAnnulusInput LatticeRadial
open ForestRelabel RootedAnchorLabels ForestLatticeFamily

variable {F J : Type*} [Fintype F] [Fintype J]

def badOrders (s : Finset Site) (k : ℕ) (Q : F→PolygonQuad) (ε δ : ℝ) :
    Finset (OrderedSelections s k) :=
  Finset.univ.filter (fun o => anchorTuple o∈polygonBadTuples s k Q ε δ)

omit [Fintype J] in
theorem bad_sum_le_tuple_sum (s : Finset Site) (k : ℕ) (Q : F→PolygonQuad)
    (ε δ : ℝ) (f : (Fin k→s)→ℝ) (hf : ∀ x,0≤f x) :
    (∑ o∈badOrders s k Q ε δ,f (anchorTuple o))≤
      ∑ x∈polygonBadTuples s k Q ε δ,f x := by
  have hmap : (badOrders s k Q ε δ).image (fun o : OrderedSelections s k => anchorTuple o)⊆
      polygonBadTuples s k Q ε δ := by
    intro x hx
    obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hx
    change o∈Finset.univ.filter (fun o : OrderedSelections s k =>
      anchorTuple o∈polygonBadTuples s k Q ε δ) at ho
    exact (Finset.mem_filter.mp ho).2
  exact Finset.sum_le_sum_of_injOn (fun o : OrderedSelections s k => anchorTuple o)
    (fun _ _ _ _ h => anchorTuple_injective k h) hmap
    (fun _ _ => le_rfl) (fun x _ _ => hf x)
theorem weighted_bad_small {E : F→Type*} [∀ j,Fintype (E j)]
    (k : ℕ) (s : ℕ→Finset Site) (Q : F→PolygonQuad)
    (A : ∀ j,AxialPolygonPresentation (Q j) (E j))
    (b : ℕ→ℝ) (root : ℕ→J→ℂ)
    (f h : ∀ n,OrderedSelections (s n) k→ℝ)
    {κ g R r p q C W : ℝ} (center : ℂ)
    (hκ : 0<κ) (hg : 0≤g) (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr : 0<r) (hC : 0≤C) (hW : 0≤W)
    (hb : ∀ᶠ n in atTop,κ*mesh n≤b n)
    (hs : ∀ᶠ n in atTop,∀ v∈s n,‖scaledEmbedding (mesh n) v-center‖≤r)
    (hbound : ∀ᶠ n in atTop,∀ o,
      |f n o|+|h n o|≤W*forestTuple k (s n) (mesh n) (b n) g R C (root n) (anchorTuple o)) :
    ∀η : ℝ,0<η → ∃δ : ℝ,0<δ ∧ ∀ᶠ n in atTop,
      (∑ o∈badOrders (s n) k Q (mesh n) δ,
        (mesh n)^(2*k)*(|f n o|+|h n o|))<η := by
  intro η hη
  let η' := η/(2*(W+1))
  have hη' : 0<η' := by dsimp [η']; positivity
  obtain ⟨δ,hδ,_hδ1,hsmall⟩ := uniform_polygon_bad_small (J := J) k Q A center
    hκ hg hpq hgp hR hr.le (mul_nonneg hC (Real.rpow_nonneg hR.le _)) hη'
  have hεδ : ∀ᶠ n in atTop,mesh n≤δ :=
    (UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hεr : ∀ᶠ n in atTop,mesh n≤r :=
    (UnitClockControl.mesh_tendsto_zero.eventually (gt_mem_nhds hr)).mono (fun _ h => h.le)
  have hηW : W*η'<η := by
    have he : η'*(W+1)=η/2 := by
      dsimp [η']
      have hn : W+1≠0 := by positivity
      field_simp
    nlinarith
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hb,hs,hbound,hεδ,hεr] with n hbn hsn hfn hd hn
  let F := forestTuple k (s n) (mesh n) (b n) g R C (root n)
  have hF : ∀ x,0≤F x := fun x => forestTuple_nonneg _ _ _ _ _ _ _ _ x hC hR.le
  have hsum := bad_sum_le_tuple_sum (s n) k Q (mesh n) δ F hF
  have hui := hsmall (mesh n) (b n) (s n) (mesh_pos n) hd hn hbn hsn (root n)
  have hF' (x : Fin k→s n) : F x=∑ H : eligibleForests (fixed k J),
      graphWeight H.val (anchorPosition k (fun v : s n => scaledEmbedding (mesh n) v)
        (root n) x) (b n) g R (C*R^g) := by
    exact (Finset.sum_coe_sort _ _).symm
  have hforest : (mesh n)^(2*k)*(∑ x∈polygonBadTuples (s n) k Q (mesh n) δ,F x)≤η' := by
    simp only [hF']
    exact hui
  calc
    _ ≤ ∑ o∈badOrders (s n) k Q (mesh n) δ,
        (mesh n)^(2*k)*(W*F (anchorTuple o)) := by
      apply Finset.sum_le_sum
      intro o _
      exact mul_le_mul_of_nonneg_left (hfn o) (pow_nonneg (mesh_pos n).le _)
    _ = W*((mesh n)^(2*k)*∑ o∈badOrders (s n) k Q (mesh n) δ,F (anchorTuple o)) := by
      rw [←Finset.mul_sum,←Finset.mul_sum]
      ring
    _ ≤ W*((mesh n)^(2*k)*∑ x∈polygonBadTuples (s n) k Q (mesh n) δ,F x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum
        (pow_nonneg (mesh_pos n).le _)) hW
    _ ≤ W*η' := mul_le_mul_of_nonneg_left hforest hW
    _ < η := hηW

/-- Every exponent strictly between zero and two admits the higher moment
needed by the forest bound. -/
theorem exists_holder_margin {g : ℝ} (hg : 0<g) (hg2 : g<2) :
    ∃p q : ℝ,Real.HolderConjugate p q ∧ g*p<2 := by
  let p := (g+2)/(2*g)
  have hp : 1<p := by
    dsimp [p]
    apply (lt_div_iff₀ (by positivity : 0<2*g)).mpr
    linarith
  refine ⟨p,Real.conjExponent p,Real.HolderConjugate.conjExponent hp,?_⟩
  have he : g*p=(g+2)/2 := by dsimp [p]; field_simp
  rw [he]
  linarith

#print axioms weighted_bad_small
end
end ExceptionalTimes.OrderedBadForestLimit

