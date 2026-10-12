import ExceptionalTimes.Model

/-! Existence of an infinite black cluster somewhere is unchanged by
finitely many color changes on the triangular lattice. The witness vertex
may change; no assertion about preserving a particular vertex is made. -/

open Set
open scoped Classical

namespace ExceptionalTimes.FiniteRecoloring

theorem reachable_black {η : Configuration} {v w : Site}
    (h : (blackGraph η).Reachable v w) (hv : η v = true) : η w = true := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hv
  | @cons a b c hab p ih => exact ih hab.2.2

theorem cluster_subset_finite_union {ω η : Configuration} (v : Site) (n : ℕ)
    (hv : v ∈ latticeBox n) (heq : ∀ x, x ∉ latticeBox n → ω x = η x) :
    BlackCluster ω v ⊆ (latticeBox (n+1) : Set Site) ∪
      ⋃ u ∈ (latticeBox (n+1) : Set Site), BlackCluster η u := by
  intro w hw
  by_cases hwn : w ∈ latticeBox (n+1)
  · exact Or.inl hwn
  · right
    have hwblack : η w = true := by
      rw [← heq w (fun h => hwn (latticeBox_mono (Nat.le_succ n) h))]
      exact reachable_black hw.2 hw.1
    have hedge : ∀ a b, a ∈ (latticeBox (n+1) : Set Site)ᶜ →
        (blackGraph ω).Adj a b → (blackGraph η).Adj a b := by
      intro a b ha hab
      have han : a ∉ latticeBox n := fun h => ha (latticeBox_mono (Nat.le_succ n) h)
      have hbn : b ∉ latticeBox n := by
        intro hb
        exact ha (mem_latticeBox_succ_of_adj hb (triangularAdj_symm hab.1))
      exact ⟨hab.1,(heq a han) ▸ hab.2.1,(heq b hbn) ▸ hab.2.2⟩
    obtain ⟨u,hu,hwu⟩ := reachable_exit_transfer hedge hw.2.symm hwn
      (by change ¬ ¬ v ∈ latticeBox (n+1); exact not_not.mpr (latticeBox_mono (Nat.le_succ n) hv))
    have hu' : u ∈ latticeBox (n+1) := by
      change ¬ ¬ u ∈ latticeBox (n+1) at hu
      exact not_not.mp hu
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu',reachable_black hwu hwblack,hwu.symm⟩⟩

theorem hasInfiniteBlackCluster_of_finite_changes {ω η : Configuration}
    {S : Set Site} (hS : S.Finite) (heq : ∀ x, x ∉ S → ω x = η x)
    (hω : HasInfiniteBlackCluster ω) : HasInfiniteBlackCluster η := by
  obtain ⟨v,hv⟩ := hω
  obtain ⟨n,hn⟩ := finite_set_subset_latticeBox (hS.union (Set.finite_singleton v))
  have hvn : v ∈ latticeBox n := hn (Or.inr (Set.mem_singleton v))
  have heqn : ∀ x, x ∉ latticeBox n → ω x = η x := by
    intro x hx
    exact heq x (fun h => hx (hn (Or.inl h)))
  by_contra hη
  have hf (u : Site) : (BlackCluster η u).Finite :=
    Set.not_infinite.mp (fun h => hη ⟨u,h⟩)
  have hfinite := (latticeBox (n+1)).finite_toSet.union
    ((latticeBox (n+1)).finite_toSet.biUnion (fun u _ => hf u))
  exact hv (hfinite.subset (cluster_subset_finite_union v n hvn heqn))

theorem hasInfiniteBlackCluster_iff_of_finite_changes {ω η : Configuration}
    {S : Set Site} (hS : S.Finite) (heq : ∀ x, x ∉ S → ω x = η x) :
    HasInfiniteBlackCluster ω ↔ HasInfiniteBlackCluster η :=
  ⟨hasInfiniteBlackCluster_of_finite_changes hS heq,
    hasInfiniteBlackCluster_of_finite_changes hS (fun x hx => (heq x hx).symm)⟩

#print axioms hasInfiniteBlackCluster_iff_of_finite_changes

end ExceptionalTimes.FiniteRecoloring
