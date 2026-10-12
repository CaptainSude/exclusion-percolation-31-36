import ExceptionalTimes.LatticeStripMass

/-! Direct finite counting for bad insertion tuples. -/
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ExceptionalTimes.LatticeBadMass
noncomputable section
open LatticeRadial

theorem card_filter_real {X : Type*} [Fintype X] (P : X→Prop) :
    ((Finset.univ.filter P).card:ℝ)=∑ x,if P x then (1:ℝ) else 0 := by
  exact (Finset.sum_boole P Finset.univ).symm

theorem tuple_fiber_mass_le {X : Type*} [Fintype X] {k : ℕ} (i : Fin k)
    (P : (Fin k→X)→Prop) {μ M B : ℝ} (hμ : 0≤μ) (hB : 0≤B)
    (hM : μ*(Fintype.card X:ℝ)≤M)
    (hf : ∀ y : {j : Fin k // j≠i}→X,
      μ*((Finset.univ.filter (fun a => P ((Equiv.funSplitAt i X).symm (a,y)))).card:ℝ)≤B) :
    μ^k*((Finset.univ.filter P).card:ℝ)≤B*M^(k-1) := by
  have hk : 0<k := by have hi := i.isLt; omega
  have hexp : k=(k-1)+1 := by omega
  have hrest : Fintype.card {j : Fin k // j≠i}=k-1 := by
    simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype_eq]
  rw [card_filter_real,←(Equiv.funSplitAt i X).symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    μ^k*(∑ y,∑ a,if P ((Equiv.funSplitAt i X).symm (a,y)) then (1:ℝ) else 0)
        = μ^(k-1)*(∑ y,μ*(∑ a,if P ((Equiv.funSplitAt i X).symm (a,y)) then (1:ℝ) else 0)) := by
            rw [←Finset.mul_sum,←mul_assoc,←pow_succ,←hexp]
    _ ≤ μ^(k-1)*(∑ _y : {j : Fin k // j≠i}→X,B) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hμ _)
      apply Finset.sum_le_sum
      intro y _
      simpa only [card_filter_real] using hf y
    _ = B*(μ*(Fintype.card X:ℝ))^(k-1) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,hrest,
        Nat.cast_pow,mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hμ (Nat.cast_nonneg _)) hM _) hB


theorem card_filter_subtype (s : Finset Site) (P : Site→Prop) :
    (Finset.univ.filter (fun v : s => P v)).card=(s.filter P).card := by
  have he : (Finset.univ.filter (fun v : s => P v)).image Subtype.val=s.filter P := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨w.property,(Finset.mem_filter.mp hw).2⟩
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩,rfl⟩
  rw [←he,Finset.card_image_of_injective _ Subtype.val_injective]

theorem collision_coordinate_mass (s : Finset Site) {k : ℕ} (i j : Fin k)
    (hij : i≠j) {ε δ r : ℝ} (center : ℂ) (hε : 0<ε) (hδ : ε≤δ) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((Finset.univ.filter (fun x : Fin k→s =>
      dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ)).card:ℝ)≤
        (121*δ^2)*(121*r^2)^(k-1) := by
  have hmass : ε^2*(Fintype.card s:ℝ)≤121*r^2 := by
    simpa only [Fintype.card_coe] using scaled_ball_mass_le s hε hr center hs
  have h := tuple_fiber_mass_le i
    (fun x : Fin k→s => dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ)
    (sq_nonneg ε) (by positivity : 0≤121*δ^2) hmass ?_
  · simpa only [pow_mul] using h
  intro y
  have hji : j≠i := Ne.symm hij
  simp only [Equiv.funSplitAt_symm_apply,dite_true,dite_eq_right hji]
  rw [card_filter_subtype s (fun v => dist (scaledEmbedding ε v) (scaledEmbedding ε (y ⟨j,hji⟩))≤δ)]
  exact scaled_ball_mass_le _ hε hδ (scaledEmbedding ε (y ⟨j,hji⟩))
    (fun v hv => by simpa only [dist_eq_norm] using (Finset.mem_filter.mp hv).2)

theorem band_coordinate_mass (s : Finset Site) {k : ℕ} (i : Fin k)
    {ε δ r a : ℝ} (center : ℂ) (horizontal : Bool)
    (hε : 0<ε) (hδ : 0≤δ) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((Finset.univ.filter (fun x : Fin k→s =>
      LatticeStripMass.band horizontal ε a δ (x i))).card:ℝ)≤
        ((4*δ+3*ε)*(8*(r+‖center‖)+3*ε))*(121*r^2)^(k-1) := by
  have hr0 : 0≤r := hε.le.trans hr
  have hmass : ε^2*(Fintype.card s:ℝ)≤121*r^2 := by
    simpa only [Fintype.card_coe] using scaled_ball_mass_le s hε hr center hs
  have h := tuple_fiber_mass_le i
    (fun x : Fin k→s => LatticeStripMass.band horizontal ε a δ (x i))
    (sq_nonneg ε) (by positivity : 0≤(4*δ+3*ε)*(8*(r+‖center‖)+3*ε)) hmass ?_
  · simpa only [pow_mul] using h
  intro y
  simp only [Equiv.funSplitAt_symm_apply,dite_true]
  rw [card_filter_subtype]
  exact LatticeStripMass.band_mass_le _ center horizontal hε hδ hr0
    (fun v hv => hs v (Finset.mem_filter.mp hv).1)
    (fun v hv => (Finset.mem_filter.mp hv).2)


theorem exists_mass_le_sum {A X : Type*} [Fintype A] [Fintype X]
    (P : A→X→Prop) {μ : ℝ} (hμ : 0≤μ) :
    μ*((Finset.univ.filter (fun x => ∃ a,P a x)).card:ℝ)≤
      ∑ a,μ*((Finset.univ.filter (P a)).card:ℝ) := by
  have he : Finset.univ.filter (fun x => ∃ a,P a x)=
      Finset.univ.biUnion (fun a => Finset.univ.filter (P a)) := by ext x; simp
  have hc : ((Finset.univ.filter (fun x => ∃ a,P a x)).card:ℝ)≤
      ∑ a,((Finset.univ.filter (P a)).card:ℝ) := by
    rw [he]
    exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ)
      (t := fun a => Finset.univ.filter (P a)))
  exact (mul_le_mul_of_nonneg_left hc hμ).trans_eq (Finset.mul_sum ..)

theorem collision_mass (s : Finset Site) (k : ℕ)
    {ε δ r : ℝ} (center : ℂ) (hε : 0<ε) (hδ : ε≤δ) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((Finset.univ.filter (fun x : Fin k→s =>
      ∃ i j,i≠j ∧ dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ)).card:ℝ)≤
        (k:ℝ)^2*(121*δ^2)*(121*r^2)^(k-1) := by
  classical
  let P := fun (ij : Fin k×Fin k) (x : Fin k→s) =>
    ij.1≠ij.2 ∧ dist (scaledEmbedding ε (x ij.1)) (scaledEmbedding ε (x ij.2))≤δ
  have hf (ij : Fin k×Fin k) :
      ε^(2*k)*((Finset.univ.filter (P ij)).card:ℝ)≤(121*δ^2)*(121*r^2)^(k-1) := by
    by_cases hij : ij.1=ij.2
    · simp only [P,hij,ne_eq,not_true_eq_false,false_and,Finset.filter_false,
        Finset.card_empty,Nat.cast_zero,mul_zero]
      positivity
    · simpa only [P,hij,ne_eq,not_false_eq_true,true_and] using
        collision_coordinate_mass s ij.1 ij.2 hij center hε hδ hr hs
  have hsum : (∑ ij : Fin k×Fin k,ε^(2*k)*((Finset.univ.filter (P ij)).card:ℝ))≤
      ∑ _ij : Fin k×Fin k,(121*δ^2)*(121*r^2)^(k-1) := by
    apply Finset.sum_le_sum
    intro ij _
    exact hf ij
  have h := exists_mass_le_sum P (by positivity : 0≤ε^(2*k))
  have hsum' : (∑ ij : Fin k×Fin k,ε^(2*k)*
      ((@Finset.filter (Fin k→s) (P ij) (fun x => Classical.propDecidable (P ij x)) Finset.univ).card:ℝ))≤
      ∑ _ij : Fin k×Fin k,(121*δ^2)*(121*r^2)^(k-1) := by
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro ij _
    congr 3
    ext x
    simp
  have h := h.trans hsum'
  have he : (fun x : Fin k→s => ∃ ij,P ij x)=
      (fun x : Fin k→s => ∃ i j,i≠j ∧
        dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ) := by
    funext x
    simp only [P,Prod.exists]
  simp only [he] at h
  convert h using 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul]
  ring

theorem bands_mass {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (horizontal : E→Bool) (level : E→ℝ) {ε δ r : ℝ} (center : ℂ)
    (hε : 0<ε) (hδ : 0≤δ) (hr : ε≤r)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((Finset.univ.filter (fun x : Fin k→s => ∃ i e,
      LatticeStripMass.band (horizontal e) ε (level e) δ (x i))).card:ℝ)≤
        (k:ℝ)*(Fintype.card E:ℝ)*((4*δ+3*ε)*(8*(r+‖center‖)+3*ε))*(121*r^2)^(k-1) := by
  let P := fun (ie : Fin k×E) (x : Fin k→s) =>
    LatticeStripMass.band (horizontal ie.2) ε (level ie.2) δ (x ie.1)
  have h := (exists_mass_le_sum P (by positivity : 0≤ε^(2*k))).trans
    (Finset.sum_le_sum (fun ie _ => band_coordinate_mass s ie.1 center (horizontal ie.2) hε hδ hr hs
      (a := level ie.2)))
  have he : (fun x : Fin k→s => ∃ ie,P ie x)=
      (fun x : Fin k→s => ∃ i e,LatticeStripMass.band (horizontal e) ε (level e) δ (x i)) := by
    funext x
    simp only [P,Prod.exists]
  simp only [he] at h
  convert h using 1
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul]
  ring


def badTuples {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (horizontal : E→Bool) (level : E→ℝ) (ε δ c : ℝ) : Finset (Fin k→s) :=
  Finset.univ.filter (fun x =>
    (∃ i j,i≠j ∧ dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ) ∨
    (∃ i e,LatticeStripMass.band (horizontal e) ε (level e) (c*δ) (x i)))

theorem bad_mass_le {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (horizontal : E→Bool) (level : E→ℝ) {ε δ r c : ℝ} (center : ℂ)
    (hε : 0<ε) (hδ : ε≤δ) (hr : ε≤r) (hc : 0≤c)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((badTuples s k horizontal level ε δ c).card:ℝ)≤
      (k:ℝ)^2*(121*δ^2)*(121*r^2)^(k-1)+
      (k:ℝ)*(Fintype.card E:ℝ)*((4*(c*δ)+3*ε)*(8*(r+‖center‖)+3*ε))*(121*r^2)^(k-1) := by
  let A := Finset.univ.filter (fun x : Fin k→s =>
    ∃ i j,i≠j ∧ dist (scaledEmbedding ε (x i)) (scaledEmbedding ε (x j))≤δ)
  let B := Finset.univ.filter (fun x : Fin k→s =>
    ∃ i e,LatticeStripMass.band (horizontal e) ε (level e) (c*δ) (x i))
  have he : badTuples s k horizontal level ε δ c=A∪B := by ext x; simp [badTuples,A,B]
  have hcard : ((badTuples s k horizontal level ε δ c).card:ℝ)≤(A.card:ℝ)+B.card := by
    rw [he]
    exact_mod_cast Finset.card_union_le A B
  calc
    _ ≤ ε^(2*k)*((A.card:ℝ)+B.card) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = ε^(2*k)*(A.card:ℝ)+ε^(2*k)*(B.card:ℝ) := mul_add _ _ _
    _ ≤ _ := add_le_add (collision_mass s k center hε hδ hr hs)
      (bands_mass s k horizontal level center hε (mul_nonneg hc (hε.le.trans hδ)) hr hs)

def badConstant (k q : ℕ) (r c : ℝ) (center : ℂ) : ℝ :=
  ((k:ℝ)^2*121+(k:ℝ)*(q:ℝ)*(4*c+3)*(8*(r+‖center‖)+3))*(121*r^2)^(k-1)

theorem bad_mass_le_linear {E : Type*} [Fintype E] (s : Finset Site) (k : ℕ)
    (horizontal : E→Bool) (level : E→ℝ) {ε δ r c : ℝ} (center : ℂ)
    (hε : 0<ε) (hδ : ε≤δ) (hδ1 : δ≤1) (hr : ε≤r) (hc : 0≤c)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ε^(2*k)*((badTuples s k horizontal level ε δ c).card:ℝ)≤
      badConstant k (Fintype.card E) r c center*δ := by
  have hd0 : 0≤δ := hε.le.trans hδ
  have hr0 : 0≤r := hε.le.trans hr
  have he1 : ε≤1 := hδ.trans hδ1
  have hδsq : δ^2≤δ := by nlinarith
  have hstrip : (4*(c*δ)+3*ε)*(8*(r+‖center‖)+3*ε)≤
      (4*c+3)*(8*(r+‖center‖)+3)*δ := by
    calc
      _ ≤ ((4*c+3)*δ)*(8*(r+‖center‖)+3) :=
        mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hcol := mul_le_mul_of_nonneg_left hδsq (by positivity : 0≤(k:ℝ)^2*121)
  have hband := mul_le_mul_of_nonneg_left hstrip
    (by positivity : 0≤(k:ℝ)*(Fintype.card E:ℝ))
  have hp : 0≤(121*r^2)^(k-1) := by positivity
  have h := add_le_add (mul_le_mul_of_nonneg_right hcol hp)
    (mul_le_mul_of_nonneg_right hband hp)
  have hmain := bad_mass_le s k horizontal level center hε hδ hr hc hs
  apply hmain.trans
  dsimp [badConstant]
  convert h using 1 <;> ring


theorem badConstant_nonneg (k q : ℕ) {r c : ℝ} (center : ℂ)
    (hr : 0≤r) (hc : 0≤c) : 0≤badConstant k q r c center := by
  unfold badConstant
  positivity

/-- Uniform smallness is a conclusion of lattice counting, including all
finite site sets inside the fixed ball and every sufficiently small mesh. -/
theorem uniform_bad_mass_small {E : Type*} [Fintype E] (k : ℕ)
    (horizontal : E→Bool) (level : E→ℝ) {r c η : ℝ} (center : ℂ)
    (hr : 0≤r) (hc : 0≤c) (hη : 0<η) :
    ∃ δ>0,δ≤1 ∧ ∀ (ε : ℝ) (s : Finset Site),0<ε → ε≤δ → ε≤r →
      (∀ v∈s,‖scaledEmbedding ε v-center‖≤r) →
      ε^(2*k)*((badTuples s k horizontal level ε δ c).card:ℝ)≤η := by
  let C := badConstant k (Fintype.card E) r c center
  have hC : 0≤C := badConstant_nonneg k _ center hr hc
  let δ := min 1 (η/(C+1))
  have hd : 0<δ := lt_min (by norm_num) (div_pos hη (by linarith))
  have hd1 : δ≤1 := min_le_left _ _
  have hbound : C*δ≤η := by
    have hle : δ*(C+1)≤η := (le_div_iff₀ (by linarith : 0<C+1)).mp (min_le_right _ _)
    nlinarith
  refine ⟨δ,hd,hd1,?_⟩
  intro ε s hε hεδ hεr hs
  exact (bad_mass_le_linear s k horizontal level center hε hεδ hd1 hεr hc hs).trans hbound

#print axioms uniform_bad_mass_small
#print axioms bad_mass_le_linear
#print axioms collision_mass
#print axioms bands_mass
#print axioms collision_coordinate_mass
#print axioms band_coordinate_mass
#print axioms tuple_fiber_mass_le
end
end ExceptionalTimes.LatticeBadMass









