import ExceptionalTimes.FiniteClockComparison

open scoped BigOperators ENNReal Classical Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ExceptionalTimes.FiniteClockDomination

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FiniteGenerator FiniteFractional

variable {S I J : Type*} [Fintype S] [DecidableEq S] [Fintype I] [Fintype J] [DecidableEq I]

noncomputable def pushedRate (e : J ↪ I) (r : J → ℝ) (i : I) : ℝ :=
  ∑ j, if e j = i then r j else 0

omit [Fintype S] [DecidableEq S] [Fintype I] in
theorem pushedRate_apply (e : J ↪ I) (r : J → ℝ) (j : J) :
    pushedRate e r (e j) = r j := by
  classical
  simp [pushedRate, e.injective.eq_iff]

omit [Fintype S] [DecidableEq S] [Fintype I] in
theorem pushedRate_le (e : J ↪ I) (r : J → ℝ) (R : I → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hr : ∀ j, r j ≤ R (e j)) (i : I) :
    pushedRate e r i ≤ R i := by
  by_cases hi : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [pushedRate_apply]
    exact hr j
  · have hzero : pushedRate e r i = 0 := by
      unfold pushedRate
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun h => hi ⟨j, h⟩)
    rw [hzero]
    exact hR i

omit [Fintype S] in
theorem generatorMatrix_pushedRate (e : J ↪ I) (σ : I → Equiv.Perm S) (r : J → ℝ) :
    generatorMatrix σ (pushedRate e r) = generatorMatrix (fun j => σ (e j)) r := by
  ext x y
  simp only [generatorMatrix, pushedRate, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

theorem complexGenerator_embedded_le (e : J ↪ I) (σ : I → Equiv.Perm S)
    (hσ : ∀ i, Function.Involutive (σ i)) (r : J → ℝ) (R : I → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hr : ∀ j, r j ≤ R (e j)) :
    complexGenerator (fun j => σ (e j)) r ≤ complexGenerator σ R := by
  have he : complexGenerator (fun j => σ (e j)) r = complexGenerator σ (pushedRate e r) := by
    unfold complexGenerator
    rw [generatorMatrix_pushedRate]
  rw [he]
  exact complexGenerator_mono σ hσ (pushedRate_le e r R hR hr)

#print axioms complexGenerator_embedded_le

omit [Fintype S] [DecidableEq S] [Fintype I] [Fintype J] [DecidableEq I] in
theorem colorSwap_eq_of_unordered_eq (V : Finset Site) (a b : V × V)
    (he : s((a.1 : Site), (a.2 : Site)) = s((b.1 : Site), (b.2 : Site))) :
    colorSwap a.1 a.2 = colorSwap b.1 b.2 := by
  rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have h₁' : a.1 = b.1 := Subtype.ext h₁
    have h₂' : a.2 = b.2 := Subtype.ext h₂
    rw [h₁', h₂']
  · have h₁' : a.1 = b.2 := Subtype.ext h₁
    have h₂' : a.2 = b.1 := Subtype.ext h₂
    rw [h₁', h₂']
    ext η v
    simp only [colorSwap_apply, Equiv.swap_comm]

omit [Fintype S] [DecidableEq S] in
theorem colorSwap_generator_subset_le (V : Finset Site)
    (edge : I → V × V) (slowEdge : J → V × V)
    (hslowinj : Function.Injective (FiniteClockBridge.edgePair V slowEdge))
    (hsub : FiniteClockBridge.retainedEdges V slowEdge ⊆ FiniteClockBridge.retainedEdges V edge)
    (rate slowRate : Sym2 Site → ℝ)
    (hr : ∀ i, 0 ≤ rate (FiniteClockBridge.edgePair V edge i))
    (hsr : ∀ j, slowRate (FiniteClockBridge.edgePair V slowEdge j) ≤
      rate (FiniteClockBridge.edgePair V slowEdge j)) :
    complexGenerator (fun j => colorSwap (slowEdge j).1 (slowEdge j).2)
        (fun j => slowRate (FiniteClockBridge.edgePair V slowEdge j)) ≤
      complexGenerator (fun i => colorSwap (edge i).1 (edge i).2)
        (fun i => rate (FiniteClockBridge.edgePair V edge i)) := by
  classical
  have hcontains (j : J) : ∃ i, FiniteClockBridge.edgePair V edge i =
      FiniteClockBridge.edgePair V slowEdge j := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hsub (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    exact ⟨i, hi⟩
  let e : J ↪ I := ⟨fun j => (hcontains j).choose, by
    intro j k he
    apply hslowinj
    exact (hcontains j).choose_spec.symm.trans
      ((congrArg (FiniteClockBridge.edgePair V edge) he).trans (hcontains k).choose_spec)⟩
  have hperm : (fun j => colorSwap (slowEdge j).1 (slowEdge j).2) =
      (fun j => colorSwap (edge (e j)).1 (edge (e j)).2) := by
    funext j
    exact colorSwap_eq_of_unordered_eq V _ _ (hcontains j).choose_spec.symm
  rw [hperm]
  apply complexGenerator_embedded_le e (fun i => colorSwap (edge i).1 (edge i).2)
    (fun _ => colorSwap_involutive _ _)
    (fun j => slowRate (FiniteClockBridge.edgePair V slowEdge j))
    (fun i => rate (FiniteClockBridge.edgePair V edge i)) hr
  intro j
  simpa only [show FiniteClockBridge.edgePair V edge (e j) =
    FiniteClockBridge.edgePair V slowEdge j from (hcontains j).choose_spec] using hsr j

#print axioms colorSwap_generator_subset_le

end ExceptionalTimes.FiniteClockDomination
