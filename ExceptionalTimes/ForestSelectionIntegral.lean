import ExceptionalTimes.CanonicalForestOrdered
import ExceptionalTimes.InsertionCounting

/-! Literal selection sums inherit the factorial and the clipped-forest
lattice bound. The injection into the lattice includes every ordering of
every selected set, and permits arbitrary nonnegative extra lattice tuples. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestSelectionIntegral

open ForestRelabel RootedAnchorLabels ForestLatticeFamily OrderedForestIntegral
open LatticeRadial ForestCoefficientIntegral InsertionCounting
open PairSquareSewing CanonicalForestOrdered NormalizedForestProfile

variable {B J : Type*} [Fintype B] [Fintype J]

noncomputable def forestTuple (k : ℕ) (s : Finset Site) (ε b g R C : ℝ)
    (root : J → ℂ) (x : Fin k → s) : ℝ :=
  ∑ H∈eligibleForests (fixed k J),
    graphWeight H (anchorPosition k (fun v : s => scaledEmbedding ε v) root x)
      b g R (C*R^g)

theorem forestTuple_nonneg (k : ℕ) (s : Finset Site) (ε b g R C : ℝ)
    (root : J → ℂ) (x : Fin k → s) (hC : 0≤C) (hR : 0≤R) :
    0≤forestTuple k s ε b g R C root x := by
  apply Finset.sum_nonneg
  intro H _
  exact graphWeight_nonneg H _ _ _ _ _ (mul_nonneg hC (Real.rpow_nonneg hR g))

theorem lattice_embedding_sum (k : ℕ) (s : Finset Site) (anchor : B ↪ s)
    (f : (Fin k → s) → ℝ) (hf : ∀ x,0≤f x) :
    (∑ x : Fin k → B,f (fun i => anchor (x i)))≤∑ x : Fin k → s,f x := by
  apply Finset.sum_le_sum_of_injOn (fun x : Fin k → B => fun i => anchor (x i))
  · intro x _ y _ h
    funext i
    exact anchor.injective (congrFun h i)
  · exact Finset.subset_univ _
  · intro _ _
    exact le_rfl
  · intro x _ _
    exact hf x

theorem selected_geometric_integral (k : ℕ) (hk : 1≤k)
    (s : Finset Site) (anchor : B ↪ s) (f : Finset B → ℝ)
    {ε b c g R r₀ C d D W : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀) (hC : 0≤C) (hd : 0<d) (hW : 0≤W)
    (hlower : d*(k:ℝ)^(-(1/2:ℝ))≤R)
    (hupper : R≤D*(k:ℝ)^(-(1/2:ℝ)))
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀) (root : J → ℂ)
    (hordered : ∀ o : OrderedSelections B k,
      f o.1.val≤W^k*R^(-g*(k:ℝ))*forestTuple k s ε b g R C root
        (fun i => anchor (anchorTuple o i))) :
    ε^(2*k)*(∑ S : Selections B k,f S.val)≤
      W^k*(summationConstant (Fintype.card J) d D C c g r₀)^k*
        (k:ℝ)^(-(1-g/2)*k) := by
  let F := forestTuple k s ε b g R C root
  have hF : ∀ x,0≤F x := fun x => forestTuple_nonneg k s ε b g R C root x hC hR.le
  have ha : 0≤W^k*R^(-g*(k:ℝ)) := by positivity
  have hfac : (0:ℝ)<k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hsel := selection_sum_le_tuple_sum k f
    (fun x => W^k*R^(-g*(k:ℝ))*F (fun i => anchor (x i)))
    (fun x => mul_nonneg ha (hF _)) hordered
  rw [←Finset.mul_sum] at hsel
  have hmap := lattice_embedding_sum k s anchor F hF
  have hsum := hsel.trans (mul_le_mul_of_nonneg_left hmap ha)
  have hdiv : (∑ S : Selections B k,f S.val)≤
      (W^k*R^(-g*(k:ℝ))*(∑ x : Fin k → s,F x))/(k.factorial:ℝ) := by
    apply (le_div_iff₀ hfac).mpr
    simpa only [mul_comm] using hsum
  have hi := ordered_lattice_forest_bound k hk s center hε hc hb hg hg2 hR hr₀ hC
    hd hlower hupper hs root
  calc
    _ ≤ ε^(2*k)*((W^k*R^(-g*(k:ℝ))*(∑ x : Fin k → s,F x))/(k.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = W^k*(R^(-g*(k:ℝ))/(k.factorial:ℝ)*(ε^(2*k)*∑ x : Fin k → s,F x)) := by ring
    _ ≤ W^k*((summationConstant (Fintype.card J) d D C c g r₀)^k*
        (k:ℝ)^(-(1-g/2)*k)) := mul_le_mul_of_nonneg_left hi (pow_nonneg hW _)
    _ = _ := by ring

omit [Fintype J] in
theorem prefactor_nonneg {I : Type*} [Fintype I] (G : DimerGeometry I J)
    {b stop C K g : ℝ} (hC : 0≤C) (hstop : 0≤stop) :
    0≤prefactor G b stop C K g :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg hC (Real.rpow_nonneg hstop _))

omit [Fintype J] in
theorem prefactor_le {I : Type*} [Fintype I] (G : DimerGeometry I J)
    {b stop C K g : ℝ} (hb : 0<b) (hstop : 0≤stop) (hC : 0≤C) (hg : 0≤g)
    (hmargin : G.margin≤b/100) :
    prefactor G b stop C K g≤
      ((K*C^2*256^g)^2*Real.exp (g*(1+4/100)))*(C*stop^g) := by
  have hm : 4*G.margin/b≤4/100 := by
    apply (div_le_iff₀ hb).mpr
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith : 1+4*G.margin/b≤1+4/100) hg))
      (sq_nonneg _)) (mul_nonneg hC (Real.rpow_nonneg hstop _))

theorem selected_forest_integral (k : ℕ) (hk : 1≤k)
    (s : Finset Site) (anchor : B ↪ s) (G : (S : Finset B) → DimerGeometry S J)
    {ε b c g R stop r₀ C K d D P : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hbR : b≤R) (hRs : R≤stop) (hr₀ : ε≤r₀) (hC : 0≤C) (hd : 0<d) (hP : 0≤P)
    (hlowerR : d*(k:ℝ)^(-(1/2:ℝ))≤R)
    (hupperR : R≤D*(k:ℝ)^(-(1/2:ℝ)))
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀) (root : J → ℂ)
    (hroot : ∀ S,(G S).root=root)
    (hanchor : ∀ (S : Finset B) (i : S),position (G S).mesh ((G S).endpoint (i,0))=
      scaledEmbedding ε (anchor i.val))
    (hPbound : ∀ S,prefactor (G S) b stop C K g≤P)
    (p : ℝ → ℝ) (hpstop : p stop=1)
    (hp : ∀ t,0<t → t≤stop → 0<p t)
    (hlower : ∀ a t,0<a → a≤t → t≤stop → p t≤C*(t/a)^g*p a) :
    ε^(2*k)*(∑ S : Selections B k,canonicalForestValue (G S.val) b R C K g (normalized p R))≤
      (P*p b)^k*(summationConstant (Fintype.card J) d D C c g r₀)^k*
        (k:ℝ)^(-(1-g/2)*k) := by
  have hbpos : 0<b := (mul_pos hc hε).trans_le hb
  have hR : 0<R := hbpos.trans_le hbR
  have hstop : 0<stop := hR.trans_le hRs
  have hpc : 0≤p b := (hp b hbpos (hbR.trans hRs)).le
  apply selected_geometric_integral k hk s anchor
    (fun S => canonicalForestValue (G S) b R C K g (normalized p R)) center
    hε hc hb hg hg2 hR hr₀ hC hd (mul_nonneg hP hpc)
    hlowerR hupperR hs root
  intro o
  have ha := actual_forest_ordered_bound o.2 (G o.1.val) (K := K) hbpos hbR hRs hC p hpstop hp hlower
  rw [hroot o.1.val] at ha
  have hpos : (fun i => position (G o.1.val).mesh ((G o.1.val).endpoint (o.2 i,0)))=
      fun i => scaledEmbedding ε (anchor (anchorTuple o i)) := by
    funext i
    exact hanchor o.1.val (o.2 i)
  rw [hpos] at ha
  have ht : 0≤forestTuple k s ε b g R C root (fun i => anchor (anchorTuple o i)) :=
    forestTuple_nonneg k s ε b g R C root _ hC hR.le
  have htEq : (∑ H∈eligibleForests (fixed k J),
      graphWeight H (anchorPosition k id root (fun i => scaledEmbedding ε (anchor (anchorTuple o i))))
        b g R (C*R^g))=forestTuple k s ε b g R C root (fun i => anchor (anchorTuple o i)) := by
    rfl
  rw [htEq] at ha
  apply ha.trans
  have hpow := pow_le_pow_left₀ (prefactor_nonneg (G o.1.val) hC hstop.le) (hPbound _) k
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (pow_nonneg hpc k))
      (Real.rpow_nonneg hR.le (-g*(k:ℝ)))) ht
  simpa only [mul_pow,mul_assoc] using hh

#print axioms selected_forest_integral
#print axioms selected_geometric_integral
end ExceptionalTimes.ForestSelectionIntegral


