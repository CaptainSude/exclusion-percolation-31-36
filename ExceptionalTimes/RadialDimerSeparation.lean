import ExceptionalTimes.RadialGapRadii

/-! Separation of whole dimer coordinates in the inner remote annulus,
a local box about the pivotal cell, and the outer remote annulus. -/

open scoped Classical

namespace ExceptionalTimes.RadialDimerSeparation

open MesoscopicCells ActiveMiddlePartition RadialGapRadii

variable {B : Type*}

def touching (slot : B×Fin 2 ↪ Site) (S : Set Site) : Set B :=
  {b | ∃ i, slot (b,i)∈S}

theorem endpoint_difference (slot : B×Fin 2 ↪ Site) (z : Site) {d : ℕ}
    (hz : z∈latticeBox d)
    (hpartner : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (b : B) (i j : Fin 2) : slot (b,i)-slot (b,j)∈latticeBox d := by
  have h := PeriodicMatching.partner_displacement z (slot (b,0))
  fin_cases i <;> fin_cases j
  · simp [latticeBox]
  · change slot (b,0)-slot (b,1)∈latticeBox d
    rw [hpartner]
    rcases h with h | h <;> rw [h]
    all_goals simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      PeriodicMatching.add,PeriodicMatching.sub,Prod.fst_sub,Prod.snd_sub] at hz ⊢
    all_goals omega
  · change slot (b,1)-slot (b,0)∈latticeBox d
    rw [hpartner]
    rcases h with h | h <;> rw [h]
    all_goals simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      PeriodicMatching.add,PeriodicMatching.sub,Prod.fst_sub,Prod.snd_sub] at hz ⊢
    all_goals omega
  · simp [latticeBox]

theorem touching_disjoint (slot : B×Fin 2 ↪ Site) (z : Site) {d : ℕ}
    (hz : z∈latticeBox d)
    (hpartner : ∀ b, slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (S T : Set Site) (hseparate : ∀ v∈S, ∀ w∈T, v-w∉latticeBox d) :
    Disjoint (touching slot S) (touching slot T) := by
  apply Set.disjoint_left.mpr
  intro b ⟨i,hi⟩ ⟨j,hj⟩
  exact hseparate _ hi _ hj (endpoint_difference slot z hz hpartner b i j)

def regions (x : Site) (a q b : ℕ) : Fin 3→Set Site :=
  ![(latticeBox (a+1) : Set Site),{v | v-x∈latticeBox q},(latticeBox b : Set Site)ᶜ]

theorem region_separation (x : Site) {a q b d : ℕ}
    (hin : a+1+q+d<latticeRadius x)
    (hout : latticeRadius x+q+d≤b) (hfar : a+1+d≤b) :
    ∀ i j : Fin 3, i≠j → ∀ v∈regions x a q b i, ∀ w∈regions x a q b j,
      v-w∉latticeBox d := by
  have h01 : ∀ v∈latticeBox (a+1), ∀ w, w-x∈latticeBox q → v-w∉latticeBox d := by
    intro v hv w hw hdiff
    have hx := sub_mem_box (sub_mem_box hv hdiff) hw
    have he : v-(v-w)-(w-x)=x := by abel
    rw [he] at hx
    have hrad := radius_le_of_mem_box hx
    omega
  have h02 : ∀ v∈latticeBox (a+1), ∀ w, w∉latticeBox b → v-w∉latticeBox d := by
    intro v hv w hw hdiff
    have hh := sub_mem_box hv hdiff
    have he : v-(v-w)=w := by abel
    rw [he] at hh
    exact hw (latticeBox_mono hfar hh)
  have h12 : ∀ v, v-x∈latticeBox q → ∀ w, w∉latticeBox b → v-w∉latticeBox d := by
    intro v hv w hw hdiff
    have hh := sub_mem_box
      (add_mem_box (mem_latticeBox_of_radius_le (le_refl (latticeRadius x))) hv) hdiff
    have he : x+(v-x)-(v-w)=w := by abel
    rw [he] at hh
    exact hw (latticeBox_mono hout hh)
  have hflip (v w : Site) (h : v-w∈latticeBox d) : w-v∈latticeBox d := by
    simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      Prod.fst_sub,Prod.snd_sub] at h ⊢
    omega
  intro i j hij v hv w hw hd
  fin_cases i <;> fin_cases j
  all_goals first | exact hij rfl | exact h01 _ hv _ hw hd | exact h02 _ hv _ hw hd |
    exact h12 _ hv _ hw hd | exact h01 _ hw _ hv (hflip _ _ hd) |
    exact h02 _ hw _ hv (hflip _ _ hd) | exact h12 _ hw _ hv (hflip _ _ hd)

theorem chosen_support_radii {K m d ρ : ℕ} (hK : 2≤K) (hm : 0<m) (hd : d≤m)
    (hscale : 32*K*m≤ρ) :
    let n := innerScale K ρ
    (K*n+1)+1+(K*n)+d<ρ ∧ ρ+(K*n)+d≤(8*K)*n ∧ (K*n+1)+1+d≤(8*K)*n := by
  let n := innerScale K ρ
  have hn := (chosen_radii hK hm hd hscale).1
  have hprod : 4*K*n≤ρ := Nat.mul_div_le ρ (4*K)
  have hhi : ρ<4*K*(n+1) := Nat.lt_mul_div_succ ρ (by positivity)
  have hKn := Nat.mul_le_mul_left K hn
  have hKm : K≤K*m := Nat.le_mul_of_pos_right K hm
  have hKm' : 2*m≤K*m := Nat.mul_le_mul_right m hK
  change (K*n+1)+1+K*n+d<ρ ∧ ρ+K*n+d≤8*K*n ∧ (K*n+1)+1+d≤8*K*n
  constructor
  · nlinarith
  constructor <;> nlinarith

#print axioms endpoint_difference
#print axioms region_separation
#print axioms chosen_support_radii

end ExceptionalTimes.RadialDimerSeparation
