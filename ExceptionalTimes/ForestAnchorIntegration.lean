import ExceptionalTimes.ForestLatticeFamily

/-! The forest integral written with the original free-vertex labels.
The change of variables is an actual bijection, so each forest can use
its own leaf order while all forests are summed over the same anchors. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.ForestAnchorIntegration

open ForestIntegration ForestEdgeProduct ForestLatticeFamily
open ForestArmRadial LatticeRadial LatticeForest ForestCounting

variable {V A P : Type*}

noncomputable def freeLabels (fixed : V → Prop) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v,v∈L ↔ ¬fixed v) : Fin L.length ≃ {v // ¬fixed v} :=
  Equiv.ofBijective (fun i => ⟨L.get i,(hmem _).mp (List.get_mem _ _)⟩) ⟨
    fun i j h => hL.injective_get (congrArg Subtype.val h), by
    intro v
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hmem v).mpr v.property)
    exact ⟨i,Subtype.ext hi⟩⟩

noncomputable def assignedPosition (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (x : {v // ¬fixed v} → A) (v : V) : P :=
  if h : fixed v then root ⟨v,h⟩ else position (x ⟨v,h⟩)

@[simp] theorem assignedPosition_root (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (x : {v // ¬fixed v} → A) (v : {v // fixed v}) :
    assignedPosition fixed position root x v=root v := by
  simp [assignedPosition,v.property]

@[simp] theorem assignedPosition_free (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (x : {v // ¬fixed v} → A) (v : {v // ¬fixed v}) :
    assignedPosition fixed position root x v=position (x v) := by
  simp [assignedPosition,v.property]

theorem configuredPosition_eq_assigned (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v,v∈L ↔ ¬fixed v) (x : {v // ¬fixed v} → A) :
    configuredPosition fixed position root L hL hmem (fun i => x (freeLabels fixed L hL hmem i))=
      assignedPosition fixed position root x := by
  funext v
  by_cases hv : fixed v
  · simpa [assignedPosition,hv] using configuredPosition_root fixed position root L hL hmem
      (fun i => x (freeLabels fixed L hL hmem i)) ⟨v,hv⟩
  · obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((hmem v).mpr hv)
    subst v
    rw [configuredPosition_get]
    exact (assignedPosition_free fixed position root x (freeLabels fixed L hL hmem i)).symm

variable [Fintype V] [Fintype A]

/-- A literal change of variables, valid for every functional of the
whole position assignment, not just a radial product. -/
theorem sum_configured_eq_assigned (fixed : V → Prop) (position : A → P)
    (root : {v // fixed v} → P) (L : List V) (hL : L.Nodup)
    (hmem : ∀ v,v∈L ↔ ¬fixed v) (F : (V → P) → ℝ) :
    (∑ x : Fin L.length → A,F (configuredPosition fixed position root L hL hmem x))=
      ∑ x : {v // ¬fixed v} → A,F (assignedPosition fixed position root x) := by
  let e := Equiv.arrowCongr (freeLabels fixed L hL hmem) (Equiv.refl A)
  rw [← e.symm.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg F (configuredPosition_eq_assigned fixed position root L hL hmem x)

theorem radialIntegral_eq_anchorSum {N : ℕ} (G : SimpleGraph (Fin N))
    (fixed : Fin N → Prop) (position : A → ℂ) (root : {v // fixed v} → ℂ)
    (L : List (Fin N)) (hL : L.Nodup) (hmem : ∀ v,v∈L ↔ ¬fixed v)
    (mass b g R : ℝ) :
    radialIntegral G fixed position root L hL hmem (fun _ _ => mass) b g R=
      mass^Fintype.card {v // ¬fixed v} *
        ∑ x : {v // ¬fixed v} → A,
          ∏ e∈G.edgeFinset,radialEdge (assignedPosition fixed position root x) b g R e := by
  have hlen : L.length=Fintype.card {v // ¬fixed v} := by
    simpa using Fintype.card_congr (freeLabels fixed L hL hmem)
  unfold radialIntegral
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←Finset.mul_sum,sum_configured_eq_assigned fixed position root L hL hmem
    (fun p => ∏ e∈G.edgeFinset,radialEdge p b g R e),hlen]
  congr 1
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  rfl

set_option maxHeartbeats 800000 in
/-- Every forest now has the same anchor domain. The leaf order has
disappeared from both sides of the bound. -/
theorem all_forests_anchor_sum (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ) :
    ε^(2*k) *
      (∑ x : {v // ¬fixed v} → s, ∑ G : eligibleForests fixed,
        ∏ e∈G.val.edgeFinset,
          radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      ∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*
        ((radialConstant g+121/c^2)*R^(2-g))^j*(121*r₀^2)^(k-j) := by
  obtain ⟨L,hL,hmem,_,hbound⟩ := all_forests_lattice_integral k J fixed hrootsize s center
    hε hc hb hg hg2 hR hr₀ hs root
  have hfree : Fintype.card {v // ¬fixed v}=k := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,hrootsize]
    omega
  simp_rw [radialIntegral_eq_anchorSum,hfree] at hbound
  rw [←Finset.mul_sum,Finset.sum_comm,←pow_mul] at hbound
  exact hbound

/-- The position-dependent Kruskal forest is dominated by the actual
sum of eligible forests, with no new integral assumption. -/
theorem selected_forests_anchor_sum (k J : ℕ) (fixed : Fin (k+J) → Prop)
    (hrootsize : Fintype.card {v // fixed v}=J)
    (s : Finset Site) {ε b c g R r₀ : ℝ} (center : ℂ)
    (hε : 0<ε) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g) (hg2 : g<2)
    (hR : 0<R) (hr₀ : ε≤r₀)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r₀)
    (root : {v // fixed v} → ℂ)
    (choice : ({v // ¬fixed v} → s) → eligibleForests fixed) :
    ε^(2*k) *
      (∑ x : {v // ¬fixed v} → s,
        ∏ e∈(choice x).val.edgeFinset,
          radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)≤
      ∑ j∈Finset.range (k+1),(((k+J)^2).choose j : ℝ)*
        ((radialConstant g+121/c^2)*R^(2-g))^j*(121*r₀^2)^(k-j) := by
  apply le_trans _ (all_forests_anchor_sum k J fixed hrootsize s center hε hc hb hg hg2 hR hr₀ hs root)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.le _)
  apply Finset.sum_le_sum
  intro x _
  exact Finset.single_le_sum (f := fun G : eligibleForests fixed => ∏ e∈G.val.edgeFinset,
    radialEdge (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e)
    (fun G _ => Finset.prod_nonneg (fun e _ => radialEdge_nonneg (assignedPosition fixed (fun v : s => scaledEmbedding ε v) root x) b g R e))
    (Finset.mem_univ (choice x))

#print axioms all_forests_anchor_sum
#print axioms selected_forests_anchor_sum

end ExceptionalTimes.ForestAnchorIntegration




