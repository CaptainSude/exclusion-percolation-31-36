import ExceptionalTimes.ClippedRadialGap
import ExceptionalTimes.ActiveMiddlePartition

/-! Integer gap radii for the actual buffered dimer cells. Every floor
and the exiting layer of the inner remote arm are retained. -/

namespace ExceptionalTimes.RadialGapRadii

open HoleFilling MesoscopicCells RadialPivotalRemote ClippedRadialGap

def innerScale (K ρ : ℕ) : ℕ := ρ/(4*K)

theorem chosen_radii {K m d ρ : ℕ} (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 32*K*m≤ρ) :
    8*m≤ innerScale K ρ ∧
      K*innerScale K ρ+2+2*(m+d)<ρ ∧
      ρ+2*(m+d)≤(8*K)*innerScale K ρ := by
  let n := innerScale K ρ
  have hden : 0<4*K := by positivity
  have hlo : 8*m≤n := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    nlinarith
  have hprod : 4*K*n≤ρ := Nat.mul_div_le ρ (4*K)
  have hhi : ρ<4*K*(n+1) := Nat.lt_mul_div_succ ρ hden
  have hKm : 2*m≤K*m := Nat.mul_le_mul_right m hK
  have hρm : 64*m≤ρ := by nlinarith
  have hKpos : 0<K := by omega
  have hnm : m≤n := by omega
  have hKnm := Nat.mul_le_mul_left K hlo
  refine ⟨hlo,?_,?_⟩
  · change K*n+2+2*(m+d)<ρ
    nlinarith
  · change ρ+2*(m+d)≤8*K*n
    have hKm0 : K≤K*m := Nat.le_mul_of_pos_right K hm
    nlinarith

/-- The actual cell forces precisely the remote events used by clipped
gluing. When a remote annulus does not fit, that implication is vacuous. -/
theorem dimer_cell_optional_remote {B : Type*} [Fintype B]
    (m K : ℕ) (hm : 0<m) (hK : 2≤K) (slot : B×Fin 2 ↪ Site)
    (z : Site) {d : ℕ} (hz : z∈latticeBox d) (hd : d≤m)
    (hpartner : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (cell : Site) (hcell : cell∈occupied m slot)
    (ω : Configuration) {r R : ℕ} (_hrR : r≤R)
    (hscale : 32*K*m≤anchorRadius m slot cell)
    (hr : r≤anchorRadius m slot cell) (hR : anchorRadius m slot cell≤R)
    (hpiv : CellInterpolation.CellPivotal (wiredArmTest r R) (dimerCell m slot cell) ω) :
    let n := innerScale K (anchorRadius m slot cell)
    InnerRemote ω r n (K*n+1) ∧ OuterRemote ω ((8*K)*n) (K*(8*K)*n+1) R := by
  let x := anchor m slot cell
  let ρ := anchorRadius m slot cell
  let n := innerScale K ρ
  obtain ⟨_,hin,hout⟩ := chosen_radii hK hm hd hscale
  have hca : n≤K*n+1 := (Nat.le_mul_of_pos_left n (by omega)).trans (Nat.le_succ _)
  have haρ : K*n+1≤ρ := by change K*n+2+2*(m+d)<ρ at hin; omega
  have hρb : ρ≤(8*K)*n := by change ρ+2*(m+d)≤(8*K)*n at hout; omega
  have hcellbuff : ∀ v∈dimerCell m slot cell, v-x∈latticeBox (2*(m+d)) :=
    fun _ hv => dimerCell_diameter m hm slot z hz hpartner hv (anchor_mem m slot cell hcell)
  constructor
  · intro hrc
    apply pivotal_remote_arm _ ω le_rfl (hrc.trans hca) (haρ.trans hR) _ hpiv
    apply Finset.disjoint_left.mpr
    intro v hvD hvA
    have hv := (Finset.mem_sdiff.mp hvA).1
    have hh := MesoscopicCells.sub_mem_box hv (hcellbuff v hvD)
    have he : v-(v-x)=x := by abel
    rw [he] at hh
    have hx := ActiveMiddlePartition.radius_le_of_mem_box hh
    change ρ≤K*n+1+1+2*(m+d) at hx
    change K*n+2+2*(m+d)<ρ at hin
    omega
  · intro hdR
    have hbR : (8*K)*n≤R := by
      have hh : (8*K)*n≤K*((8*K)*n) := Nat.le_mul_of_pos_left _ (by omega)
      change K*(8*K)*n+1≤R at hdR
      nlinarith
    apply pivotal_remote_arm _ ω (hr.trans hρb) hbR le_rfl _ hpiv
    apply Finset.disjoint_left.mpr
    intro v hvD hvA
    have hh := MesoscopicCells.add_mem_box
      (mem_latticeBox_of_radius_le (le_refl (latticeRadius x))) (hcellbuff v hvD)
    have he : x+(v-x)=v := by abel
    rw [he] at hh
    exact (Finset.mem_sdiff.mp hvA).2 (latticeBox_mono hout hh)

#print axioms chosen_radii
#print axioms dimer_cell_optional_remote

end ExceptionalTimes.RadialGapRadii


