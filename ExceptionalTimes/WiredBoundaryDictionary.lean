import ExceptionalTimes.WiredBoundary

/-! Exact outer-boundary convention dictionary. Wiring the exterior of
box R+1 black is equivalent to the original-color arm beyond box R.
The one-layer shift is necessary and is not suppressed. -/

namespace ExceptionalTimes.WiredBoundary

open HoleFilling

theorem exists_adjacent_outside_larger_box {R : ℕ} {w : Site}
    (hw : w ∉ latticeBox R) :
    ∃ v : Site, TriangularAdj w v ∧ v ∉ latticeBox (R+1) := by
  rcases w with ⟨x,y⟩
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] at hw
  have h : x < -(R : ℤ) ∨ (R : ℤ) < x ∨ y < -(R : ℤ) ∨ (R : ℤ) < y := by omega
  rcases h with h | h | h | h
  · refine ⟨(x-1,y), ?_, ?_⟩
    · unfold TriangularAdj
      omega
    · simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega
  · refine ⟨(x+1,y), ?_, ?_⟩
    · unfold TriangularAdj
      omega
    · simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega
  · refine ⟨(x,y-1), ?_, ?_⟩
    · unfold TriangularAdj
      omega
    · simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega
  · refine ⟨(x,y+1), ?_, ?_⟩
    · unfold TriangularAdj
      omega
    · simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega

theorem wireBoth_eq_fillBox_on_outer (ω : Configuration) (r R : ℕ) :
    Set.EqOn (wireBoth ω r R) (fillBox ω r) (latticeBox R : Set Site) := by
  intro v hv
  change v ∈ latticeBox R at hv
  simp only [wireBoth, fillBox, hv, not_true_eq_false, or_false]

theorem wiredConnection_succ_iff_oneArm (ω : Configuration) (r R : ℕ) :
    WiredConnection ω r (R+1) ↔ OneArm (fillBox ω r) (0,0) R := by
  constructor
  · intro h
    have hsmall : OneArm (wireBoth ω r (R+1)) (0,0) R := by
      obtain ⟨w, hw, hout⟩ := h
      exact ⟨w, hw, fun hR => hout (latticeBox_mono (Nat.le_succ R) hR)⟩
    exact oneArm_transfer_of_eqOn_box (origin_mem_box R)
      (wireBoth_eq_fillBox_on_outer ω r (R+1)) hsmall
  · rintro ⟨w, hw, hout⟩
    obtain ⟨v, hv, hvout⟩ := exists_adjacent_outside_larger_box hout
    have hreach : (blackGraph (wireBoth ω r (R+1))).Reachable (0,0) w :=
      hw.2.mono (fillBox_le_wireBoth ω r (R+1))
    have hzero : wireBoth ω r (R+1) (0,0) = true :=
      wireBoth_inside ω r (R+1) (origin_mem_box r)
    have hwcol : wireBoth ω r (R+1) w = true :=
      Necklace.reachable_has_color triangularGraph _ true hzero hreach
    exact ⟨v, ⟨hzero, hreach.trans (show (blackGraph (wireBoth ω r (R+1))).Adj w v from
      ⟨hv, hwcol, wireBoth_outside ω r (R+1) hvout⟩).reachable⟩, hvout⟩

theorem wiredConnection_succ_iff_wiredArm (ω : Configuration) {r R : ℕ}
    (hrR : r ≤ R) : WiredConnection ω r (R+1) ↔ WiredArm ω r R := by
  rw [wiredConnection_succ_iff_oneArm, oneArm_fillBox_iff_wiredArm ω hrR]

theorem wiredArm_annular_duality (boundaryInput : FiniteClusterBoundaryCircuit)
    (ω : Configuration) {r R : ℕ} (hrR : r ≤ R) :
    (¬ WiredArm ω r R) ↔
      ∃ v : Site, ∃ c : triangularGraph.Walk v v,
        c.IsCycle ∧
        (∀ z ∈ c.support, z ∉ latticeBox r ∧ z ∈ latticeBox (R+1) ∧ ω z = false) ∧
        SeparatesFromInfinity (latticeBox r : Set Site) {z | z ∈ c.support} := by
  rw [← wiredConnection_succ_iff_wiredArm ω hrR]
  exact wired_annular_duality boundaryInput ω r (R+1)

end ExceptionalTimes.WiredBoundary

#print axioms ExceptionalTimes.WiredBoundary.wiredConnection_succ_iff_wiredArm
#print axioms ExceptionalTimes.WiredBoundary.wiredArm_annular_duality
