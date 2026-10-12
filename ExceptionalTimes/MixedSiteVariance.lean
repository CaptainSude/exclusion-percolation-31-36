import ExceptionalTimes.MixedCanonicalVariance
import ExceptionalTimes.CanonicalRadialLaw

/-! The active-only mixed variance estimate on literal triangular-lattice
site colorings. A concrete injection of the pair endpoints determines the
cell support; its locality is proved from that injection. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MixedSiteVariance

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar GroupedDimerLaw
open MixedCanonicalLaw MixedEnvironmentVariance MixedCanonicalVariance

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I O : Type*} [Fintype I] [Fintype O]
variable {J : I → Type*} [∀ i, Fintype (J i)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

def decode (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (x : (Sigma J → Color) × (O → Color)) : Configuration :=
  Function.extend slot (fun b => Sum.elim x.1 x.2 b.1 b.2) (fun _ => false)

def cellSites (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site) (i : I) : Finset Site :=
  Finset.univ.image (fun b : J i × Fin 2 => slot (.inl ⟨i,b.1⟩,b.2))

omit [Fintype I] [Fintype O] in
theorem mem_cellSites (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (i : I) (j : J i) (b : Fin 2) : slot (.inl ⟨i,j⟩,b) ∈ cellSites slot i := by
  exact Finset.mem_image.mpr ⟨(j,b),Finset.mem_univ _,rfl⟩

omit [Fintype I] [Fintype O] in
theorem cellSites_disjoint (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    {i j : I} (hij : i ≠ j) : Disjoint (cellSites slot i) (cellSites slot j) := by
  apply Finset.disjoint_left.mpr
  intro v hv hi
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hv
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hi
  have he := slot.injective (ha.trans hb.symm)
  have hs := Sum.inl.inj (congrArg Prod.fst he)
  exact hij (congrArg Sigma.fst hs)

omit [Fintype I] [Fintype O] in
theorem decode_agrees_outside (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (i : I) (x y : Sigma J → Color) (o : O → Color)
    (h : ∀ s, s.1 ≠ i → x s = y s)
    (v : Site) (hv : v ∉ cellSites slot i) : decode slot (x,o) v = decode slot (y,o) v := by
  by_cases hex : ∃ b, slot b = v
  · obtain ⟨⟨s,b⟩,rfl⟩ := hex
    unfold decode
    rw [slot.injective.extend_apply,slot.injective.extend_apply]
    cases s with
    | inl s =>
        change x s b = y s b
        apply congrFun (h s _) b
        intro hs
        rcases s with ⟨j,a⟩
        dsimp at hs
        subst j
        exact hv (mem_cellSites slot i a b)
    | inr s => rfl
  · unfold decode
    rw [Function.extend_apply' _ _ _ hex,Function.extend_apply' _ _ _ hex]

omit [Fintype I] [Fintype O] in
/-- An active group pivotal witness supplies two actual site colorings
that keep every exterior site, including all independent collar colors,
unchanged. -/
theorem activeGroupPivotal_site_pivotal
    (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site) (F : Configuration → Bool)
    (i : I) (x : (Sigma J → Color) × (O → Color))
    (hpiv : activeGroupPivotal (S := fun _ _ => Color)
      (fun y => F (decode slot y) = true) i x) :
    CellInterpolation.CellPivotal F (cellSites slot i) (decode slot x) := by
  obtain ⟨y,z,hout,hF⟩ := (groupPivotal_iff_outside
    (J := J) (S := fun _ _ => Color)
    (fun y => F (decode slot (y,x.2)) = true) i x.1).mp hpiv
  refine ⟨decode slot (y,x.2),decode slot (z,x.2),?_,?_,?_⟩
  · intro v hv
    exact decode_agrees_outside slot i y x.1 x.2 (fun s hs => (hout s hs).1) v hv
  · intro v hv
    exact decode_agrees_outside slot i z x.1 x.2 (fun s hs => (hout s hs).2) v hv
  · intro heq
    exact hF (by rw [heq])

/-- Actual Site-cell variance for the mixed law: there is one summand per
active group, and none for the independently resampled exterior. -/
theorem mixed_site_variance
    (slot : ((Sigma J ⊕ O) × Fin 2) ↪ Site)
    (p : Sigma J → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∀ s, p s ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun j => environmentLaw (p ⟨i,j⟩) (hp0 ⟨i,j⟩) (hp1 ⟨i,j⟩)))) :
    mixedProbability p (fun x => F (decode slot x) = true) -
      (average (smooth (fun x => indicator (F (decode slot x) = true)))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, mixedProbability p
        (fun x => CellInterpolation.CellPivotal F (cellSites slot i) (decode slot x)) := by
  apply (mixed_dimer_variance p hp0 hp1 (fun x => F (decode slot x) = true) hES).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply mixed_mono p hp0 hp1 _ _ (fun x => indicator_nonneg _) _
  intro x
  by_cases hp : activeGroupPivotal (S := fun _ _ => Color)
      (fun y => F (decode slot y) = true) i x
  · simp [indicator, hp, activeGroupPivotal_site_pivotal slot F i x hp]
  · simpa only [indicator, ite_eq_right hp] using
      indicator_nonneg (CellInterpolation.CellPivotal F (cellSites slot i) (decode slot x))

#print axioms activeGroupPivotal_site_pivotal
#print axioms mixed_site_variance

end

end ExceptionalTimes.MixedSiteVariance
