import ExceptionalTimes.ForestWeightedAnchors

/-! Relabelling an actual rooted forest preserves its radial edge product.
This places forests with arbitrary finite vertex labels in the same counted
family used by the lattice integral. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

namespace ExceptionalTimes.ForestRelabel

open ForestIntegration ForestLatticeFamily ForestArmRadial ForestAnchorIntegration
open ForestCounting ForestCharge

variable {V W A X : Type*} [Fintype V] [Fintype W] [PseudoMetricSpace X]



noncomputable def rootEquiv (e : V ≃ W) (fixed : V → Prop) :
    {w // fixed (e.symm w)} ≃ {v // fixed v} where
  toFun w := ⟨e.symm w,w.property⟩
  invFun v := ⟨e v,by simpa using v.property⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

noncomputable def freeEquiv (e : V ≃ W) (fixed : V → Prop) :
    {w // ¬fixed (e.symm w)} ≃ {v // ¬fixed v} := rootEquiv e (fun v => ¬fixed v)

omit [Fintype V] [Fintype W] in
theorem rootsSeparated_map (e : V ≃ W) (fixed : V → Prop) (G : SimpleGraph V)
    (h : RootsSeparated G fixed) :
    RootsSeparated (G.map e) (fun w => fixed (e.symm w)) := by
  intro u v hu hv huv
  apply e.symm.injective
  exact h _ _ hu hv (huv.map (SimpleGraph.Iso.map e G).symm.toHom)

omit [Fintype V] [Fintype W] in
theorem radialEdge_map (e : V ≃ W) (p : V → X) (b g R : ℝ) (a : Sym2 V) :
    radialEdge (fun w => p (e.symm w)) b g R (e.toEmbedding.sym2Map a)=
      radialEdge p b g R a := by
  induction a using Sym2.inductionOn with
  | _ u v => simp [radialEdge_mk]

theorem edgeFinset_map_equiv (e : V ≃ W) (G : SimpleGraph V) :
    (G.map e).edgeFinset=G.edgeFinset.map e.toEmbedding.sym2Map := by
  apply Finset.coe_injective
  simp only [SimpleGraph.coe_edgeFinset,Finset.coe_map]
  exact G.edgeSet_map e.toEmbedding
theorem radial_product_map (e : V ≃ W) (G : SimpleGraph V) (p : V → X) (b g R : ℝ) :
    (∏ a∈(G.map e).edgeFinset,radialEdge (fun w => p (e.symm w)) b g R a)=
      ∏ a∈G.edgeFinset,radialEdge p b g R a := by
  rw [edgeFinset_map_equiv,Finset.prod_map]
  apply Finset.prod_congr rfl
  intro a _
  exact radialEdge_map e p b g R a

omit [Fintype V] [Fintype W] [PseudoMetricSpace X] in
theorem assignedPosition_map (e : V ≃ W) (fixed : V → Prop)
    (position : A → X) (root : {v // fixed v} → X) (x : {v // ¬fixed v} → A) :
    assignedPosition (fun w => fixed (e.symm w)) position
      (fun w => root (rootEquiv e fixed w)) (fun w => x (freeEquiv e fixed w))=
      fun w => assignedPosition fixed position root x (e.symm w) := by
  funext w
  by_cases hw : fixed (e.symm w)
  · simp [assignedPosition,hw,rootEquiv]
  · simp [assignedPosition,hw,freeEquiv,rootEquiv]

noncomputable def graphWeight (G : SimpleGraph V) (p : V → X) (b g R w : ℝ) : ℝ :=
  w^G.edgeFinset.card*∏ a∈G.edgeFinset,radialEdge p b g R a

theorem graphWeight_map (e : V ≃ W) (G : SimpleGraph V)
    (p : V → X) (b g R w : ℝ) :
    graphWeight (G.map e) (fun v => p (e.symm v)) b g R w=graphWeight G p b g R w := by
  unfold graphWeight
  apply congrArg₂ (fun x y : ℝ => x*y)
  · apply congrArg (fun n : ℕ => w^n)
    have hc := congrArg Finset.card (edgeFinset_map_equiv e G)
    rw [Finset.card_map] at hc
    convert hc using 1
    congr 1
    ext a
    simp only [SimpleGraph.mem_edgeFinset]
  · convert radial_product_map e G p b g R using 1
    all_goals
      apply Finset.prod_congr (by ext a; simp only [SimpleGraph.mem_edgeFinset])
      intro a _
      rfl

theorem graphWeight_nonneg (G : SimpleGraph V) (p : V → X) (b g R w : ℝ) (hw : 0≤w) :
    0≤graphWeight G p b g R w :=
  mul_nonneg (pow_nonneg hw _) (Finset.prod_nonneg (fun a _ => radialEdge_nonneg p b g R a))

theorem graph_le_all_forests {N : ℕ} (e : V ≃ Fin N) (fixed : V → Prop)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hroot : RootsSeparated G fixed)
    (p : V → X) (b g R w : ℝ) (hw : 0≤w) :
    graphWeight G p b g R w≤
      ∑ H ∈ eligibleForests (fun v : Fin N => fixed (e.symm v)),
        graphWeight H (fun v => p (e.symm v)) b g R w := by
  have hm : G.map e ∈ eligibleForests (fun v : Fin N => fixed (e.symm v)) := by
    rw [mem_eligibleForests]
    exact ⟨(SimpleGraph.Iso.map e G).isAcyclic_iff.mp hG,rootsSeparated_map e fixed G hroot⟩
  rw [←graphWeight_map e G p b g R w]
  exact Finset.single_le_sum (fun H _ => graphWeight_nonneg H _ b g R w hw) hm

variable [Fintype A]

theorem sum_assignments (e : V ≃ W) (fixed : V → Prop)
    (F : ({w // ¬fixed (e.symm w)} → A) → ℝ) :
    (∑ x : {v // ¬fixed v} → A,F (fun w => x (freeEquiv e fixed w)))=
      ∑ y : {w // ¬fixed (e.symm w)} → A,F y := by
  let a := Equiv.arrowCongr (freeEquiv e fixed).symm (Equiv.refl A)
  exact a.sum_comp F

#print axioms graph_le_all_forests

end ExceptionalTimes.ForestRelabel
