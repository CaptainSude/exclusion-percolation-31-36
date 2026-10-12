import ExceptionalTimes.LatticeRadial
import ExceptionalTimes.PeriodicMatching
import ExceptionalTimes.DyadicPacking

/-! Concrete mesoscopic cells for whole dimers. A dimer is assigned by
one endpoint to an integer square grid. The diameter buffer and the
number of occupied cells in a finite radius are proved geometrically. -/

open scoped BigOperators Classical

namespace ExceptionalTimes.MesoscopicCells

noncomputable section

def gridIndex (m : ℕ) (v : Site) : Site := (v.1 / (m : ℤ),v.2 / (m : ℤ))

def gridOrigin (m : ℕ) (c : Site) : Site := ((m : ℤ) * c.1,(m : ℤ) * c.2)

theorem remainder_box (m : ℕ) (hm : 0 < m) (v : Site) :
    v - gridOrigin m (gridIndex m v) ∈ latticeBox m := by
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  have hx0 := Int.emod_nonneg v.1 hmz.ne'
  have hx1 := Int.emod_lt_of_pos v.1 hmz
  have hy0 := Int.emod_nonneg v.2 hmz.ne'
  have hy1 := Int.emod_lt_of_pos v.2 hmz
  have hxe := Int.mul_ediv_add_emod v.1 (m : ℤ)
  have hye := Int.mul_ediv_add_emod v.2 (m : ℤ)
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    Prod.fst_sub,Prod.snd_sub,gridIndex,gridOrigin]
  omega

theorem same_cell_difference (m : ℕ) (hm : 0 < m) (v w : Site)
    (h : gridIndex m v = gridIndex m w) : v - w ∈ latticeBox m := by
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [gridIndex] at hx hy
  have hx0 := Int.emod_nonneg v.1 hmz.ne'
  have hx1 := Int.emod_lt_of_pos v.1 hmz
  have hx2 := Int.emod_nonneg w.1 hmz.ne'
  have hx3 := Int.emod_lt_of_pos w.1 hmz
  have hy0 := Int.emod_nonneg v.2 hmz.ne'
  have hy1 := Int.emod_lt_of_pos v.2 hmz
  have hy2 := Int.emod_nonneg w.2 hmz.ne'
  have hy3 := Int.emod_lt_of_pos w.2 hmz
  have hxe := Int.mul_ediv_add_emod v.1 (m : ℤ)
  have hye := Int.mul_ediv_add_emod v.2 (m : ℤ)
  have hxw := Int.mul_ediv_add_emod w.1 (m : ℤ)
  have hyw := Int.mul_ediv_add_emod w.2 (m : ℤ)
  rw [hx] at hxe
  rw [hy] at hye
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    Prod.fst_sub,Prod.snd_sub]
  omega

theorem add_mem_box {v w : Site} {r s : ℕ}
    (hv : v ∈ latticeBox r) (hw : w ∈ latticeBox s) : v+w ∈ latticeBox (r+s) := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    Prod.fst_add,Prod.snd_add] at hv hw ⊢
  omega

theorem sub_mem_box {v w : Site} {r s : ℕ}
    (hv : v ∈ latticeBox r) (hw : w ∈ latticeBox s) : v-w ∈ latticeBox (r+s) := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    Prod.fst_sub,Prod.snd_sub] at hv hw ⊢
  omega

/-- The second endpoint costs only the displacement radius beyond the
grid-cell buffer; all dimers in one group fit this same translated box. -/
theorem partner_cell_buffer (m : ℕ) (hm : 0 < m) (z v : Site)
    {d : ℕ} (hz : z ∈ latticeBox d) :
    PeriodicMatching.partner z v - gridOrigin m (gridIndex m v) ∈ latticeBox (m+d) := by
  have hv := remainder_box m hm v
  rcases PeriodicMatching.partner_displacement z v with hp | hp
  all_goals rw [hp]
  all_goals simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
    PeriodicMatching.add,PeriodicMatching.sub,Prod.fst_sub,Prod.snd_sub] at hv hz ⊢
  all_goals omega

theorem ediv_box_bound (m R : ℕ) (hm : 0 < m) {x : ℤ}
    (hx : -(R : ℤ) ≤ x ∧ x ≤ R) :
    -((R / m + 1 : ℕ) : ℤ) ≤ x / m ∧ x / m ≤ (R / m + 1 : ℕ) := by
  have hmz : 0 < (m : ℤ) := by exact_mod_cast hm
  have hhigh := Int.ediv_le_ediv hmz hx.2
  have hlow := Int.ediv_le_ediv hmz hx.1
  rw [Int.neg_ediv,Int.sign_eq_one_of_pos hmz] at hlow
  have he : (R : ℤ) / (m : ℤ) = (R / m : ℕ) := by omega
  rw [he] at hhigh hlow
  split_ifs at hlow <;> omega

theorem gridIndex_mem_box (m R : ℕ) (hm : 0 < m) {v : Site}
    (hv : v ∈ latticeBox R) : gridIndex m v ∈ latticeBox (R/m+1) := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] at hv ⊢
  exact ⟨ediv_box_bound m R hm hv.1,ediv_box_bound m R hm hv.2⟩

/-- The number of occupied grid cells depends on the radius divided by
the mesh, not on the number of dimers in any cell. -/
theorem occupied_cells_card (m R : ℕ) (hm : 0 < m) (V : Finset Site)
    (hV : V ⊆ latticeBox R) :
    (V.image (gridIndex m)).card ≤ (2*(R/m+1)+1)^2 := by
  rw [← LatticeRadial.latticeBox_card]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
  exact gridIndex_mem_box m R hm (hV hv)

variable {B : Type*} [Fintype B]

def dimerIndex (m : ℕ) (slot : B × Fin 2 ↪ Site) (b : B) : Site :=
  gridIndex m (slot (b,0))

def occupied (m : ℕ) (slot : B × Fin 2 ↪ Site) : Finset Site :=
  Finset.univ.image (dimerIndex m slot)

/-- The actual finite cell-label type used to group the dimer coordinates. -/
abbrev CellLabels (m : ℕ) (slot : B × Fin 2 ↪ Site) := ↥(occupied m slot)

def group (m : ℕ) (slot : B × Fin 2 ↪ Site) (b : B) : CellLabels m slot :=
  ⟨dimerIndex m slot b,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩

def groupingEquiv (m : ℕ) (slot : B × Fin 2 ↪ Site) :
    (Σ c : CellLabels m slot, {b : B // group m slot b = c}) ≃ B :=
  Equiv.sigmaFiberEquiv (group m slot)

def dimerCell (m : ℕ) (slot : B × Fin 2 ↪ Site) (c : Site) : Finset Site :=
  (Finset.univ.filter (fun b : B × Fin 2 => dimerIndex m slot b.1 = c)).image slot

theorem endpoint_in_cell (m : ℕ) (slot : B × Fin 2 ↪ Site) (b : B) (i : Fin 2) :
    slot (b,i) ∈ dimerCell m slot (dimerIndex m slot b) := by
  exact Finset.mem_image.mpr ⟨(b,i),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩

theorem dimerCell_disjoint (m : ℕ) (slot : B × Fin 2 ↪ Site) {c d : Site} (hcd : c ≠ d) :
    Disjoint (dimerCell m slot c) (dimerCell m slot d) := by
  apply Finset.disjoint_left.mpr
  intro v hc hd
  obtain ⟨b,hb,hbv⟩ := Finset.mem_image.mp hc
  obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp hd
  have hab := slot.injective (hbv.trans hav.symm)
  subst a
  exact hcd ((Finset.mem_filter.mp hb).2.symm.trans (Finset.mem_filter.mp ha).2)

theorem dimerCell_nonempty_iff (m : ℕ) (slot : B × Fin 2 ↪ Site) (c : Site) :
    (dimerCell m slot c).Nonempty ↔ c ∈ occupied m slot := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨⟨b,i⟩,hb,_⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,(Finset.mem_filter.mp hb).2⟩
  · intro hc
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hc
    exact ⟨slot (b,0),endpoint_in_cell m slot b 0⟩

/-- Cells are literally unions of complete matching orbits, rather than
sets of sites that may cut a conserved pair in half. -/
theorem dimerCell_partner_invariant (m : ℕ) (slot : B × Fin 2 ↪ Site)
    (z : Site) (hz0 : z ≠ (0,0))
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v : Site} (hv : v ∈ dimerCell m slot c) :
    PeriodicMatching.partner z v ∈ dimerCell m slot c := by
  obtain ⟨⟨b,i⟩,hb,rfl⟩ := Finset.mem_image.mp hv
  have hc := (Finset.mem_filter.mp hb).2
  rw [← hc]
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [← hp b]
    exact endpoint_in_cell m slot b 1
  · rw [hp b,PeriodicMatching.partner_involutive z hz0]
    exact endpoint_in_cell m slot b 0

/-- Every whole-dimer cell has its proved displacement buffer. -/
theorem dimerCell_buffer (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v : Site} (hv : v ∈ dimerCell m slot c) :
    v - gridOrigin m c ∈ latticeBox (m+d) := by
  obtain ⟨⟨b,i⟩,hb,rfl⟩ := Finset.mem_image.mp hv
  have hc := (Finset.mem_filter.mp hb).2
  change gridIndex m (slot (b,0)) = c at hc
  rw [← hc]
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact latticeBox_mono (Nat.le_add_right m d) (remainder_box m hm (slot (b,0)))
  · rw [hp b]
    exact partner_cell_buffer m hm z (slot (b,0)) hz

theorem dimerCell_diameter (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v w : Site} (hv : v ∈ dimerCell m slot c) (hw : w ∈ dimerCell m slot c) :
    v-w ∈ latticeBox (2*(m+d)) := by
  have h := sub_mem_box (dimerCell_buffer m hm slot z hz hp hv)
    (dimerCell_buffer m hm slot z hz hp hw)
  have he : (v-gridOrigin m c)-(w-gridOrigin m c) = v-w := by abel
  simpa only [he,two_mul] using h

omit [Fintype B] in
theorem base_endpoint_mem_box (slot : B × Fin 2 ↪ Site) (z : Site) {d R : ℕ}
    (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (b : B) (i : Fin 2) (hv : slot (b,i) ∈ latticeBox R) :
    slot (b,0) ∈ latticeBox (R+d) := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · exact latticeBox_mono (Nat.le_add_right R d) hv
  · rw [hp b] at hv
    rcases PeriodicMatching.partner_displacement z (slot (b,0)) with he | he
    all_goals rw [he] at hv
    all_goals simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      PeriodicMatching.add,PeriodicMatching.sub] at hv hz ⊢
    all_goals omega

theorem touching_cell_index (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d R : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c : Site} (hc : ∃ v ∈ dimerCell m slot c, v ∈ latticeBox R) :
    c ∈ latticeBox ((R+d)/m+1) := by
  obtain ⟨v,hv,hvR⟩ := hc
  obtain ⟨⟨b,i⟩,hb,rfl⟩ := Finset.mem_image.mp hv
  have he := (Finset.mem_filter.mp hb).2
  rw [← he]
  exact gridIndex_mem_box m (R+d) hm (base_endpoint_mem_box slot z hz hp b i hvR)

/-- Finite collections of cells touching a radius-R box obey a uniform
packing bound, including the partner-displacement buffer. -/
theorem touching_cells_card (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d R : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (C : Finset Site) (hC : ∀ c ∈ C, ∃ v ∈ dimerCell m slot c, v ∈ latticeBox R) :
    C.card ≤ (2*((R+d)/m+1)+1)^2 := by
  rw [← LatticeRadial.latticeBox_card]
  exact Finset.card_le_card (fun c hc => touching_cell_index m hm slot z hz hp (hC c hc))

/-- The scale-invariant packing constant is explicit. It is uniform in
the retained dimer set and in the number of dimers per occupied cell. -/
theorem touching_cells_card_real (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d R : ℕ} (hz : z ∈ latticeBox d) (hdm : d ≤ m) (hmR : m ≤ R)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (C : Finset Site) (hC : ∀ c ∈ C, ∃ v ∈ dimerCell m slot c, v ∈ latticeBox R) :
    (C.card : ℝ) ≤ 49 * ((R : ℝ) / m)^2 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd' : (d : ℝ) ≤ m := by exact_mod_cast hdm
  have hR' : (m : ℝ) ≤ R := by exact_mod_cast hmR
  have hratio : 1 ≤ (R : ℝ) / m := (one_le_div hm').mpr hR'
  have hq : (((R+d)/m : ℕ) : ℝ) ≤ (R : ℝ)/m+1 := by
    apply (Nat.cast_div_le (m := R+d) (n := m)).trans
    rw [Nat.cast_add,add_div]
    linarith [(div_le_one hm').mpr hd']
  have hcard : (C.card : ℝ) ≤ (2*((((R+d)/m : ℕ) : ℝ)+1)+1)^2 := by
    exact_mod_cast touching_cells_card m hm slot z hz hp C hC
  calc
    _ ≤ (2*((((R+d)/m : ℕ) : ℝ)+1)+1)^2 := hcard
    _ ≤ (7*((R : ℝ)/m))^2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    _ = _ := by ring

theorem dimerCell_embedding_radius (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v : Site} (hv : v ∈ dimerCell m slot c) :
    ‖triangularEmbedding v - triangularEmbedding (gridOrigin m c)‖ ≤ 2*(m+d : ℕ) := by
  rw [← triangularEmbedding_sub]
  exact triangularEmbedding_norm_le_of_mem_box (dimerCell_buffer m hm slot z hz hp hv)

theorem cell_origin_mem_enlarged_box (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d R : ℕ} (hz : z ∈ latticeBox d)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v : Site} (hv : v ∈ dimerCell m slot c) (hvR : v ∈ latticeBox R) :
    gridOrigin m c ∈ latticeBox (R+(m+d)) := by
  have h := sub_mem_box hvR (dimerCell_buffer m hm slot z hz hp hv)
  have he : v-(v-gridOrigin m c) = gridOrigin m c := by abel
  simpa only [he] using h

theorem cell_origin_not_mem_smaller_box (m : ℕ) (hm : 0 < m) (slot : B × Fin 2 ↪ Site)
    (z : Site) {d r : ℕ} (hz : z ∈ latticeBox d) (hmd : m+d ≤ r)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    {c v : Site} (hv : v ∈ dimerCell m slot c) (hvr : v ∉ latticeBox r) :
    gridOrigin m c ∉ latticeBox (r-(m+d)) := by
  intro hc
  have h := add_mem_box hc (dimerCell_buffer m hm slot z hz hp hv)
  have he : gridOrigin m c+(v-gridOrigin m c) = v := by abel
  rw [he,Nat.sub_add_cancel hmd] at h
  exact hvr h

/-- The bulk dyadic sum uses the proved physical cell count. The only
probabilistic premise is the individual cell cost; there is no assumed
aggregate packing or variance estimate. Shells may have arbitrary finite
cutoffs, and cells may contain arbitrarily many dimers. -/
theorem bulk_cell_sum (m r : ℕ) (hm : 0 < m) (hmr : m ≤ r)
    (slot : B × Fin 2 ↪ Site) (z : Site) {d : ℕ}
    (hz : z ∈ latticeBox d) (hdm : d ≤ m)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (N : Finset ℕ) (C : ℕ → Finset Site) (cost : ℕ → Site → ℝ)
    (K q h : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hh : 0 < h)
    (htouch : ∀ i ∈ N, ∀ c ∈ C i,
      ∃ v ∈ dimerCell m slot c, v ∈ latticeBox (2*(r*2^i)))
    (hcost : ∀ i ∈ N, ∀ c ∈ C i, cost i c ≤
      K*q*((m : ℝ)/DyadicPacking.dyadicScale (r : ℝ) i)^(2+h)) :
    (∑ i ∈ N, ∑ c ∈ C i, cost i c) ≤
      196*K*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr : 0 < r := lt_of_lt_of_le hm hmr
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmr' : (m : ℝ) ≤ r := by exact_mod_cast hmr
  have hc (i : ℕ) (hi : i ∈ N) :
      (∑ c ∈ C i, cost i c) ≤
        (196*K*q)*DyadicPacking.bulkWeight m (DyadicPacking.dyadicScale r i) h := by
    have hpow : 1 ≤ 2^i := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero i (by decide))
    have hri : r ≤ r*2^i := by simpa using Nat.mul_le_mul_left r hpow
    have hmR : m ≤ 2*(r*2^i) := by omega
    have hcard := touching_cells_card_real m hm slot z hz hdm hmR hp (C i) (htouch i hi)
    have hcard' : ((C i).card : ℝ) ≤
        196*(DyadicPacking.dyadicScale (r : ℝ) i/m)^2 := by
      convert hcard using 1
      simp only [DyadicPacking.dyadicScale,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring
    have hpow0 : 0 ≤ ((m : ℝ)/DyadicPacking.dyadicScale (r : ℝ) i)^(2+h) :=
      Real.rpow_nonneg (div_pos hm' (DyadicPacking.dyadicScale_pos hr' i)).le _
    calc
      _ ≤ ∑ _c ∈ C i, K*q*((m : ℝ)/DyadicPacking.dyadicScale (r : ℝ) i)^(2+h) :=
        Finset.sum_le_sum (fun c hc => hcost i hi c hc)
      _ = ((C i).card : ℝ)*(K*q*((m : ℝ)/DyadicPacking.dyadicScale (r : ℝ) i)^(2+h)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (196*(DyadicPacking.dyadicScale (r : ℝ) i/m)^2)*
          (K*q*((m : ℝ)/DyadicPacking.dyadicScale (r : ℝ) i)^(2+h)) :=
        mul_le_mul_of_nonneg_right hcard' (mul_nonneg (mul_nonneg hK hq) hpow0)
      _ = _ := by unfold DyadicPacking.bulkWeight; ring
  calc
    _ ≤ ∑ i ∈ N, (196*K*q)*DyadicPacking.bulkWeight m (DyadicPacking.dyadicScale r i) h :=
      Finset.sum_le_sum hc
    _ = (196*K*q)*(∑ i ∈ N, DyadicPacking.bulkWeight m (DyadicPacking.dyadicScale r i) h) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (196*K*q)*(DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h) :=
      mul_le_mul_of_nonneg_left
        (DyadicPacking.original_bulk_sum_le hm' hr' hmr' hh le_rfl N) (by positivity)
    _ = _ := by ring

theorem exists_dyadic_shell {r n N : ℕ} (hlo : r ≤ n) (hhi : n < r*2^N) :
    ∃ i ∈ Finset.range N, r*2^i ≤ n ∧ n < 2*(r*2^i) := by
  induction N with
  | zero => simp only [pow_zero,mul_one] at hhi; omega
  | succ N ih =>
      by_cases hprev : n < r*2^N
      · obtain ⟨i,hi,h1,h2⟩ := ih hprev
        exact ⟨i,Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),h1,h2⟩
      · refine ⟨N,Finset.mem_range.mpr (by omega),by omega,?_⟩
        convert hhi using 1
        ring

def anchor (m : ℕ) (slot : B × Fin 2 ↪ Site) (c : Site) : Site :=
  if h : (dimerCell m slot c).Nonempty then Classical.choose h else (0,0)

theorem anchor_mem (m : ℕ) (slot : B × Fin 2 ↪ Site) (c : Site)
    (hc : c ∈ occupied m slot) : anchor m slot c ∈ dimerCell m slot c := by
  have h := (dimerCell_nonempty_iff m slot c).mpr hc
  simp only [anchor,dite_eq_left h]
  exact Classical.choose_spec h

def anchorRadius (m : ℕ) (slot : B × Fin 2 ↪ Site) (c : Site) : ℕ :=
  latticeRadius (anchor m slot c)

/-- Complete finite-cell bulk summation. Dyadic shell coverage and the
physical packing estimate are proved internally. The premise is only
the pointwise cost at each actual cell anchor, plus its bulk radius. -/
theorem all_bulk_cell_sum (m r : ℕ) (hm : 0 < m) (hmr : m ≤ r)
    (slot : B × Fin 2 ↪ Site) (z : Site) {d : ℕ}
    (hz : z ∈ latticeBox d) (hdm : d ≤ m)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (C : Finset Site) (hC : C ⊆ occupied m slot) (cost : Site → ℝ)
    (K q h : ℝ) (hK : 0 ≤ K) (hq : 0 ≤ q) (hh : 0 < h)
    (hmin : ∀ c ∈ C, r ≤ anchorRadius m slot c)
    (hnonneg : ∀ c ∈ C, 0 ≤ cost c)
    (hcost : ∀ c ∈ C, cost c ≤ K*q*((m : ℝ)/anchorRadius m slot c)^(2+h)) :
    (∑ c ∈ C, cost c) ≤
      196*K*q*DyadicPacking.dyadicConstant (-h)*((m : ℝ)/r)^h := by
  let ρ := anchorRadius m slot
  let N := C.sup ρ
  let S : ℕ → Finset Site := fun i => C.filter (fun c => r*2^i ≤ ρ c ∧ ρ c < 2*(r*2^i))
  have hr : 0 < r := lt_of_lt_of_le hm hmr
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hcover (c : Site) (hc : c ∈ C) : ∃ i ∈ Finset.range N, c ∈ S i := by
    have hρ : ρ c ≤ N := Finset.le_sup hc
    have hpow : 2^N ≤ r*2^N := by
      simpa using Nat.mul_le_mul_right (2^N) (Nat.one_le_iff_ne_zero.mpr hr.ne')
    obtain ⟨i,hi,h1,h2⟩ := exists_dyadic_shell (hmin c hc)
      (hρ.trans_lt (Nat.lt_two_pow_self.trans_le hpow))
    exact ⟨i,hi,Finset.mem_filter.mpr ⟨hc,h1,h2⟩⟩
  have hsum : (∑ c ∈ C, cost c) ≤ ∑ i ∈ Finset.range N, ∑ c ∈ S i, cost c := by
    simp only [S,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro c hc
    obtain ⟨i,hi,hci⟩ := hcover c hc
    have hcond := (Finset.mem_filter.mp hci).2
    calc
      cost c = if r*2^i ≤ ρ c ∧ ρ c < 2*(r*2^i) then cost c else 0 := (ite_eq_left hcond).symm
      _ ≤ _ := Finset.single_le_sum
        (f := fun j => if r*2^j ≤ ρ c ∧ ρ c < 2*(r*2^j) then cost c else 0)
        (fun j _ => by split_ifs <;> first | exact hnonneg c hc | exact le_rfl) hi
  apply hsum.trans
  apply bulk_cell_sum m r hm hmr slot z hz hdm hp (Finset.range N) S (fun _ c => cost c)
    K q h hK hq hh
  · intro i _ c hc
    obtain ⟨hcC,_,hρ⟩ := Finset.mem_filter.mp hc
    exact ⟨anchor m slot c,anchor_mem m slot c (hC hcC),
      mem_latticeBox_of_radius_le hρ.le⟩
  · intro i _ c hc
    obtain ⟨hcC,hρ,_⟩ := Finset.mem_filter.mp hc
    apply (hcost c hcC).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hq)
    have hi : DyadicPacking.dyadicScale (r : ℝ) i ≤ (ρ c : ℝ) := by
      unfold DyadicPacking.dyadicScale
      exact_mod_cast hρ
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    exact div_le_div_of_nonneg_left hm'.le (DyadicPacking.dyadicScale_pos hr' i) hi

#print axioms partner_cell_buffer
#print axioms occupied_cells_card
#print axioms dimerCell_buffer
#print axioms touching_cells_card
#print axioms touching_cells_card_real
#print axioms dimerCell_partner_invariant
#print axioms bulk_cell_sum
#print axioms all_bulk_cell_sum

end

end ExceptionalTimes.MesoscopicCells
