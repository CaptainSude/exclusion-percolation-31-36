import ExceptionalTimes.GroupedDimerLaw
import ExceptionalTimes.ProbeProduct
import ExceptionalTimes.FiniteMatchingClosure
import ExceptionalTimes.CellInterpolation
import ExceptionalTimes.RadialEnergy

/-! Literal finite-law operations for the radial bootstrap. Event inclusions
and necessary probe events are kept separate from numerical probability
bounds. No planar extraction or paired arm-decay statement is assumed to be
a published theorem here. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.CanonicalRadialLaw

noncomputable section

open DimerLaw ManyDimerLaw EnvironmentVariance FiniteHaar GroupedDimerLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {B : Type*} [Fintype B]

theorem probability_mono {S : Type*} [Fintype S] (ν : FiniteLaw S)
    {E F : S → Prop} (h : ∀ x, E x → F x) : probability ν E ≤ probability ν F := by
  apply ν.expect_mono
  intro x
  by_cases hx : E x
  · simp [indicator, hx, h x hx]
  · simpa only [indicator, ite_eq_right hx] using indicator_nonneg (F x)

theorem many_nonneg (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (B → Color) → Prop) : 0 ≤ manyProbability p E := by
  rw [manyProbability_eq_joint p hp0 hp1]
  exact probability_nonneg _ _

theorem many_le_one (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (B → Color) → Prop) : manyProbability p E ≤ 1 := by
  rw [manyProbability_eq_joint p hp0 hp1]
  exact probability_le_one _ _

theorem many_le_marginal (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (B → Color) → Prop) :
    manyProbability p E ≤ average (fun x => indicator (E x)) := by
  rw [manyProbability_eq_paired p hp0 hp1, pairedProbability_eq,
    ← many_marginal_probability p hp0 hp1]
  apply FiniteLaw.expect_mono
  intro x
  nlinarith [probability_nonneg (manyReplica x) E, probability_le_one (manyReplica x) E]

theorem many_mono (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    {E F : (B → Color) → Prop} (h : ∀ x, E x → F x) :
    manyProbability p E ≤ manyProbability p F := by
  simp_rw [manyProbability_eq_joint p hp0 hp1]
  exact probability_mono _ (fun x hx => ⟨h _ hx.1, h _ hx.2⟩)

theorem many_congr (p : B → ℝ) {E F : (B → Color) → Prop}
    (h : ∀ x, E x ↔ F x) : manyProbability p E = manyProbability p F := by
  simp only [manyProbability, h]

/-- Relabeling the actual dimer coordinates preserves the same finite law. -/
theorem many_relabel {C : Type*} [Fintype C] (e : C ≃ B)
    (p : B → ℝ) (E : (B → Color) → Prop) :
    manyProbability p E =
      manyProbability (fun c => p (e c)) (fun x => E (fun b => x (e.symm b))) := by
  let q : (C → Color) ≃ (B → Color) := Equiv.arrowCongr e (Equiv.refl Color)
  unfold manyProbability
  rw [← q.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [← q.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  unfold manyWeight
  rw [← e.prod_comp]
  simp [q]

theorem average_relabel {C : Type*} [Fintype C] (e : C ≃ B)
    (f : (B → Color) → ℝ) :
    average f = average (fun x : C → Color => f (fun b => x (e.symm b))) := by
  let q : (C → Color) ≃ (B → Color) := Equiv.arrowCongr e (Equiv.refl Color)
  unfold average
  rw [← Fintype.card_congr q, ← q.sum_comp]
  rfl

/-- A deterministic increasing-event gluing is converted to a lower bound
under the actual canonical law by the already proved duplicated Harris. -/
theorem glue_two (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E F G : Set (B → Color)) (hE : IsUpperSet E) (hF : IsUpperSet F)
    (hglue : E ∩ F ⊆ G) :
    manyProbability p (fun x => x ∈ E) * manyProbability p (fun x => x ∈ F) ≤
      manyProbability p (fun x => x ∈ G) :=
  (many_harris p hp0 hp1 E F hE hF).trans (many_mono p hp0 hp1 (fun _ h => hglue h))

theorem glue_with_bridge (p : B → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E F C G : Set (B → Color))
    (hE : IsUpperSet E) (hF : IsUpperSet F) (hC : IsUpperSet C)
    (hglue : (E ∩ F) ∩ C ⊆ G) :
    (manyProbability p (fun x => x ∈ E) * manyProbability p (fun x => x ∈ F)) *
        (average (fun x => indicator (x ∈ C))) ^ 2 ≤ manyProbability p (fun x => x ∈ G) := by
  have h1 := many_harris p hp0 hp1 E F hE hF
  have h2 := many_square_lower p hp0 hp1 (fun x => x ∈ C)
  have hprod := mul_le_mul h1 h2 (sq_nonneg _)
    (many_nonneg p hp0 hp1 (fun x => x ∈ E ∩ F))
  exact hprod.trans (glue_two p hp0 hp1 (E ∩ F) C G (hE.inter hF) hC hglue)

#print axioms glue_with_bridge
#print axioms many_relabel

section Groups

variable {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]

local instance : DecidableEq (Sigma J) := fun a b => Classical.propDecidable (a = b)

def groupedLayers : ((Sigma J → Color) × (Sigma J → Color)) ≃
    (∀ i, (J i → Color) × (J i → Color)) where
  toFun x i := (fun j => x.1 ⟨i, j⟩, fun j => x.2 ⟨i, j⟩)
  invFun x := (fun s => (x s.1).1 s.2, fun s => (x s.1).2 s.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem grouped_expect (p : Sigma J → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (f : ((Sigma J → Color) × (Sigma J → Color)) → ℝ) :
    (manyLaw p hp0 hp1).expect f =
      (FiniteLaw.pi (fun i => manyLaw (fun j => p ⟨i,j⟩)
        (fun j => hp0 ⟨i,j⟩) (fun j => hp1 ⟨i,j⟩))).expect
          (fun x => f (groupedLayers.symm x)) := by
  unfold FiniteLaw.expect
  rw [← groupedLayers.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change (∏ s : Sigma J, twoTimeWeight (p s) ((x s.1).1 s.2) ((x s.1).2 s.2)) =
    ∏ i, ∏ j, twoTimeWeight (p ⟨i,j⟩) ((x i).1 j) ((x i).2 j)
  exact Fintype.prod_sigma _

/-- Necessary events in disjoint groups of dimers are exactly independent
at both times. The grouping is of whole dimers, not individual site colors. -/
theorem many_independent_groups (p : Sigma J → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : ∀ i, (J i → Color) → Prop) :
    manyProbability p (fun x => ∀ i, E i (fun j => x ⟨i,j⟩)) =
      ∏ i, manyProbability (fun j => p ⟨i,j⟩) (E i) := by
  rw [manyProbability_eq_joint p hp0 hp1]
  unfold probability
  rw [grouped_expect]
  have he : (fun x : ∀ i, (J i → Color) × (J i → Color) =>
      indicator ((∀ i, E i ((x i).1)) ∧ ∀ i, E i ((x i).2))) =
      (fun x => indicator (∀ i, E i (x i).1 ∧ E i (x i).2)) := by
    funext x
    simp only [forall_and]
  change (FiniteLaw.pi (fun i => manyLaw (fun j => p ⟨i,j⟩)
    (fun j => hp0 ⟨i,j⟩) (fun j => hp1 ⟨i,j⟩))).expect
      (fun x => indicator ((∀ i, E i ((x i).1)) ∧ ∀ i, E i ((x i).2))) = _
  rw [he]
  rw [← probability, ProbeProduct.probability_pi
    (fun i => manyLaw (fun j => p ⟨i,j⟩) (fun j => hp0 ⟨i,j⟩) (fun j => hp1 ⟨i,j⟩))
    (fun i z => E i z.1 ∧ E i z.2)]
  apply Finset.prod_congr rfl
  intro i _
  exact (manyProbability_eq_joint _ _ _ _).symm

theorem many_necessary_groups (p : Sigma J → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (E : (Sigma J → Color) → Prop) (T : ∀ i, (J i → Color) → Prop)
    (hnecessary : ∀ x, E x → ∀ i, T i (fun j => x ⟨i,j⟩)) :
    manyProbability p E ≤ ∏ i, manyProbability (fun j => p ⟨i,j⟩) (T i) :=
  (many_mono p hp0 hp1 hnecessary).trans_eq (many_independent_groups p hp0 hp1 T)

end Groups

#print axioms many_independent_groups

section Cells

variable {I : Type*} [Fintype I] {k : ℕ} (cell : Fin k → I)

abbrev CellFiber (i : I) := {b : Fin k // cell b = i}

local instance (i : I) : DecidableEq (CellFiber cell i) :=
  fun a b => Classical.propDecidable (a = b)

local instance : DecidableEq (Sigma (CellFiber cell)) :=
  fun a b => Classical.propDecidable (a = b)

def ungroup (x : Sigma (CellFiber cell) → Color) : Fin k → Color :=
  fun b => x ⟨cell b, ⟨b, rfl⟩⟩

def cellSites (slot : Fin k × Fin 2 ↪ Site) (i : I) : Finset Site :=
  (Finset.univ.filter (fun b : Fin k × Fin 2 => cell b.1 = i)).image slot

omit [Fintype I] in
theorem mem_cellSites (slot : Fin k × Fin 2 ↪ Site) (i : I) (b : Fin k × Fin 2)
    (hb : cell b.1 = i) : slot b ∈ cellSites cell slot i := by
  exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

omit [Fintype I] in
theorem cellSites_disjoint (slot : Fin k × Fin 2 ↪ Site) {i j : I} (hij : i ≠ j) :
    Disjoint (cellSites cell slot i) (cellSites cell slot j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.mp hx
  obtain ⟨c, hc, hcx⟩ := Finset.mem_image.mp hy
  have heq := slot.injective (hbx.trans hcx.symm)
  subst c
  exact hij ((Finset.mem_filter.mp hb).2.symm.trans (Finset.mem_filter.mp hc).2)

omit [Fintype I] in
theorem decode_agrees_outside_cell (slot : Fin k × Fin 2 ↪ Site) (i : I)
    (x y : Fin k → Color) (h : ∀ b, cell b ≠ i → x b = y b)
    (v : Site) (hv : v ∉ cellSites cell slot i) :
    FiniteMatchingClosure.decode slot x v = FiniteMatchingClosure.decode slot y v := by
  by_cases hex : ∃ b, slot b = v
  · obtain ⟨b, rfl⟩ := hex
    unfold FiniteMatchingClosure.decode
    rw [slot.injective.extend_apply, slot.injective.extend_apply]
    exact congrFun (h b.1 (fun hb => hv (mem_cellSites cell slot i b hb))) b.2
  · unfold FiniteMatchingClosure.decode
    rw [Function.extend_apply' _ _ _ hex, Function.extend_apply' _ _ _ hex]

omit [Fintype I] in
/-- Whole-group pivotality in the finite law supplies literal alternative
Site colorings with the unchanged exterior required by the planar pivot lemma. -/
theorem group_pivotal_site_pivotal (slot : Fin k × Fin 2 ↪ Site)
    (F : Configuration → Bool) (i : I) (x : Sigma (CellFiber cell) → Color)
    (h : GroupPivotal (S := fun _ _ => Color)
      (fun y => F (FiniteMatchingClosure.decode slot (ungroup cell y)) = true) i x) :
    CellInterpolation.CellPivotal F (cellSites cell slot i)
      (FiniteMatchingClosure.decode slot (ungroup cell x)) := by
  obtain ⟨y, z, hout, hF⟩ := (groupPivotal_iff_outside
    (J := CellFiber cell) (S := fun _ _ => Color)
    (fun y => F (FiniteMatchingClosure.decode slot (ungroup cell y)) = true) i x).mp h
  refine ⟨FiniteMatchingClosure.decode slot (ungroup cell y),
    FiniteMatchingClosure.decode slot (ungroup cell z), ?_, ?_, ?_⟩
  · intro v hv
    exact decode_agrees_outside_cell cell slot i _ _
      (fun b hb => (hout ⟨cell b, ⟨b, rfl⟩⟩ hb).1) v hv
  · intro v hv
    exact decode_agrees_outside_cell cell slot i _ _
      (fun b hb => (hout ⟨cell b, ⟨b, rfl⟩⟩ hb).2) v hv
  · intro heq
    apply hF
    rw [heq]

/-- The genuine grouped dimer variance inequality now sums literal pivotal
events of the disjoint Site cells. No extra factor counts dimers in a cell. -/
theorem site_cell_variance (slot : Fin k × Fin 2 ↪ Site)
    (p : Fin k → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun b : CellFiber cell i => environmentLaw (p b) (hp0 b) (hp1 b)))) :
    manyProbability p (fun x => F (FiniteMatchingClosure.decode slot x) = true) -
      (average (fun x => indicator (F (FiniteMatchingClosure.decode slot x) = true))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, manyProbability p (fun x =>
        CellInterpolation.CellPivotal F (cellSites cell slot i) (FiniteMatchingClosure.decode slot x)) := by
  let e := Equiv.sigmaFiberEquiv cell
  have hq := many_relabel e p (fun x => F (FiniteMatchingClosure.decode slot x) = true)
  have ha : (average (fun x : Fin k → Color => indicator (F (FiniteMatchingClosure.decode slot x) = true))) =
      average (fun x : Sigma (CellFiber cell) → Color =>
        indicator (F (FiniteMatchingClosure.decode slot (ungroup cell x)) = true)) := by
    convert average_relabel e (fun x => indicator (F (FiniteMatchingClosure.decode slot x) = true)) using 1 <;>
      exact average_congr_instances _ _ _ _ (fun _ => rfl)
  rw [hq, ha]
  have H := grouped_dimer_variance (I := I) (J := CellFiber cell)
    (fun s => p s.2.val) (fun s => hp0 s.2.val) (fun s => hp1 s.2.val)
    (fun y => F (FiniteMatchingClosure.decode slot (ungroup cell y)) = true) hES
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ manyProbability (fun s => p (e s)) (fun y =>
        CellInterpolation.CellPivotal F (cellSites cell slot i)
          (FiniteMatchingClosure.decode slot (ungroup cell y))) :=
      many_mono _ (fun s => hp0 (e s)) (fun s => hp1 (e s))
        (fun y hy => group_pivotal_site_pivotal cell slot F i y hy)
    _ = _ := (many_relabel e p (fun x => CellInterpolation.CellPivotal F
      (cellSites cell slot i) (FiniteMatchingClosure.decode slot x))).symm

theorem site_cell_variance_of_necessary (slot : Fin k × Fin 2 ↪ Site)
    (p : Fin k → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun b : CellFiber cell i => environmentLaw (p b) (hp0 b) (hp1 b))))
    (T : I → Configuration → Prop)
    (hnecessary : ∀ i η, CellInterpolation.CellPivotal F (cellSites cell slot i) η → T i η) :
    manyProbability p (fun x => F (FiniteMatchingClosure.decode slot x) = true) -
      (average (fun x => indicator (F (FiniteMatchingClosure.decode slot x) = true))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, manyProbability p (fun x => T i (FiniteMatchingClosure.decode slot x)) := by
  apply (site_cell_variance cell slot p hp0 hp1 F hES).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact many_mono p hp0 hp1 (fun x hx => hnecessary i _ hx)

/-- Each pivotal cell is tested against its own explicit partition of ALL
dimer coordinates into independent probes. Unused coordinates can be a
probe with the always-true event. Only a deterministic necessity premise
connects the actual Site pivotality to those probe events. -/
theorem site_cell_variance_of_disjoint_probes
    {A : I → Type*} [∀ i, Fintype (A i)]
    {J : ∀ i, A i → Type*} [∀ i a, Fintype (J i a)]
    (slot : Fin k × Fin 2 ↪ Site)
    (p : Fin k → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun b : CellFiber cell i => environmentLaw (p b) (hp0 b) (hp1 b))))
    (e : ∀ i, Sigma (J i) ≃ Fin k) (T : ∀ i a, (J i a → Color) → Prop)
    (hnecessary : ∀ i x, CellInterpolation.CellPivotal F (cellSites cell slot i)
      (FiniteMatchingClosure.decode slot x) → ∀ a, T i a (fun j => x (e i ⟨a,j⟩))) :
    manyProbability p (fun x => F (FiniteMatchingClosure.decode slot x) = true) -
      (average (fun x => indicator (F (FiniteMatchingClosure.decode slot x) = true))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, ∏ a, manyProbability (fun j => p (e i ⟨a,j⟩)) (T i a) := by
  apply (site_cell_variance cell slot p hp0 hp1 F hES).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  rw [many_relabel (e i)]
  apply many_necessary_groups _ (fun s => hp0 (e i s)) (fun s => hp1 (e i s)) _ (T i)
  intro x hx
  have H := hnecessary i (fun b => x ((e i).symm b)) hx
  simpa only [Equiv.symm_apply_apply] using H

theorem site_cell_variance_of_probe_bounds
    {A : I → Type*} [∀ i, Fintype (A i)]
    {J : ∀ i, A i → Type*} [∀ i a, Fintype (J i a)]
    (slot : Fin k × Fin 2 ↪ Site)
    (p : Fin k → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1)
    (F : Configuration → Bool)
    (hES : EfronStein (fun i => FiniteLaw.pi
      (fun b : CellFiber cell i => environmentLaw (p b) (hp0 b) (hp1 b))))
    (e : ∀ i, Sigma (J i) ≃ Fin k) (T : ∀ i a, (J i a → Color) → Prop)
    (hnecessary : ∀ i x, CellInterpolation.CellPivotal F (cellSites cell slot i)
      (FiniteMatchingClosure.decode slot x) → ∀ a, T i a (fun j => x (e i ⟨a,j⟩)))
    (bound : ∀ i, A i → ℝ)
    (hbound : ∀ i a, manyProbability (fun j => p (e i ⟨a,j⟩)) (T i a) ≤ bound i a) :
    manyProbability p (fun x => F (FiniteMatchingClosure.decode slot x) = true) -
      (average (fun x => indicator (F (FiniteMatchingClosure.decode slot x) = true))) ^ 2 ≤
      (1 / 2 : ℝ) * ∑ i, ∏ a, bound i a := by
  apply (site_cell_variance_of_disjoint_probes cell slot p hp0 hp1 F hES e T hnecessary).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.prod_le_prod₀
    (fun a _ => many_nonneg _ (fun j => hp0 (e i ⟨a,j⟩)) (fun j => hp1 (e i ⟨a,j⟩)) (T i a))
    (fun a _ => hbound i a)

end Cells

#print axioms group_pivotal_site_pivotal
#print axioms site_cell_variance
#print axioms site_cell_variance_of_necessary
#print axioms site_cell_variance_of_disjoint_probes
#print axioms site_cell_variance_of_probe_bounds

end

end ExceptionalTimes.CanonicalRadialLaw
