import ExceptionalTimes.LatticeRadial

/-! Explicit scaled counting mass for thin axial strips. The finite site
set is arbitrary; no continuum area or limiting lattice-count premise is used. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.LatticeStripMass

open LatticeRadial

theorem scaled_coordinate_difference {ε δ a : ℝ} {x y : ℤ}
    (hε : 0<ε) (hx : |ε*x-a|≤δ) (hy : |ε*y-a|≤δ) :
    ε*|((x-y:ℤ):ℝ)|≤2*δ := by
  calc
    _ = |ε*((x:ℝ)-(y:ℝ))| := by rw [abs_mul,abs_of_pos hε,Int.cast_sub]
    _ = |(ε*x-a)-(ε*y-a)| := by congr 1; ring
    _ ≤ |ε*x-a|+|ε*y-a| := abs_sub _ _
    _ ≤ 2*δ := by linarith

theorem scaled_ceil_le {ε δ : ℝ} (hε : 0<ε) (hδ : 0≤δ) :
    ε*(⌈2*δ/ε⌉₊:ℝ)≤2*δ+ε := by
  have h := (Nat.ceil_lt_add_one (show 0≤2*δ/ε by positivity)).le
  have hm := mul_le_mul_of_nonneg_left h hε.le
  field_simp at hm ⊢
  nlinarith

theorem centered_interval_card (n : ℕ) :
    (Finset.Icc (-(n:ℤ)) (n:ℤ)).card=2*n+1 := by
  rw [Int.card_Icc]
  omega

theorem rectangle_mass_le (s : Finset Site) {ε δ r a b : ℝ}
    (hε : 0<ε) (hδ : 0≤δ) (hr : 0≤r)
    (hs : ∀ v∈s,|ε*v.1-a|≤δ ∧ |ε*v.2-b|≤r) :
    ε^2*(s.card:ℝ)≤(4*δ+3*ε)*(4*r+3*ε) := by
  by_cases he : s.Nonempty
  · obtain ⟨v₀,hv₀⟩ := he
    let n₁ : ℕ := ⌈2*δ/ε⌉₊
    let n₂ : ℕ := ⌈2*r/ε⌉₊
    let box : Finset Site := (Finset.Icc (-(n₁:ℤ)) (n₁:ℤ)).product
      (Finset.Icc (-(n₂:ℤ)) (n₂:ℤ))
    have hdiff (v : Site) (hv : v∈s) : v-v₀∈box := by
      have hx := scaled_coordinate_difference hε (hs v hv).1 (hs v₀ hv₀).1
      have hy := scaled_coordinate_difference hε (hs v hv).2 (hs v₀ hv₀).2
      have hn₁ : 2*δ≤(n₁:ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil _)
      have hn₂ : 2*r≤(n₂:ℝ)*ε := (div_le_iff₀ hε).mp (Nat.le_ceil _)
      change ε*|((v-v₀).1:ℝ)|≤2*δ at hx
      change ε*|((v-v₀).2:ℝ)|≤2*r at hy
      have hx' : |((v-v₀).1:ℝ)|≤(n₁:ℝ) := by nlinarith
      have hy' : |((v-v₀).2:ℝ)|≤(n₂:ℝ) := by nlinarith
      change (v-v₀)∈(Finset.Icc (-(n₁:ℤ)) (n₁:ℤ)).product (Finset.Icc (-(n₂:ℤ)) (n₂:ℤ))
      rw [Finset.product_eq_sprod]
      simp only [Finset.mem_product,Finset.mem_Icc]
      constructor <;> constructor
      · exact_mod_cast (abs_le.mp hx').1
      · exact_mod_cast (abs_le.mp hx').2
      · exact_mod_cast (abs_le.mp hy').1
      · exact_mod_cast (abs_le.mp hy').2
    have hcard : s.card≤(2*n₁+1)*(2*n₂+1) := by
      rw [←centered_interval_card n₁,←centered_interval_card n₂,←Finset.card_product]
      calc
        s.card=(s.image (fun v => v-v₀)).card :=
          (Finset.card_image_of_injective s (fun v w h => by
            simpa using congrArg (fun z : Site => z+v₀) h)).symm
        _ ≤ box.card := Finset.card_le_card (by
          intro v hv
          obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
          exact hdiff w hw)
    have hcast : (s.card:ℝ)≤(2*(n₁:ℝ)+1)*(2*(n₂:ℝ)+1) := by exact_mod_cast hcard
    have hu₁ := scaled_ceil_le hε hδ
    have hu₂ := scaled_ceil_le hε hr
    calc
      _ ≤ ε^2*((2*(n₁:ℝ)+1)*(2*(n₂:ℝ)+1)) :=
        mul_le_mul_of_nonneg_left hcast (sq_nonneg ε)
      _ = (ε*(2*(n₁:ℝ)+1))*(ε*(2*(n₂:ℝ)+1)) := by ring
      _ ≤ _ := mul_le_mul (by dsimp [n₁]; nlinarith) (by dsimp [n₂]; nlinarith)
        (by positivity) (by positivity)
  · have hs0 : s=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hs0,Finset.card_empty,Nat.cast_zero,mul_zero]
    positivity

theorem vertical_strip_mass_le (s : Finset Site) {ε δ r a : ℝ}
    (hε : 0<ε) (hδ : 0≤δ) (hr : 0≤r)
    (hball : ∀ v∈s,‖scaledEmbedding ε v‖≤r)
    (hstrip : ∀ v∈s,|ε*v.1-a|≤δ) :
    ε^2*(s.card:ℝ)≤(4*δ+3*ε)*(8*r+3*ε) := by
  have hb : ∀ v∈s,|ε*v.2-(0:ℝ)|≤2*r := by
    intro v hv
    have hc := (triangularEmbedding_coordinate_bounds v).2
    have hn : ε*‖triangularEmbedding v‖≤r := by
      simpa [scaledEmbedding,norm_mul,Complex.norm_real,abs_of_pos hε] using hball v hv
    rw [sub_zero,abs_mul,abs_of_pos hε]
    nlinarith
  have h := rectangle_mass_le s hε hδ (by positivity : 0≤2*r)
    (a := a) (b := 0) (fun v hv => ⟨hstrip v hv,hb v hv⟩)
  convert h using 1
  ring

#print axioms rectangle_mass_le
#print axioms vertical_strip_mass_le


theorem horizontal_strip_mass_le (s : Finset Site) {ε δ r a : ℝ}
    (hε : 0<ε) (hδ : 0≤δ) (hr : 0≤r)
    (hball : ∀ v∈s,‖scaledEmbedding ε v‖≤r)
    (hstrip : ∀ v∈s,|ε*v.2-a|≤δ) :
    ε^2*(s.card:ℝ)≤(4*δ+3*ε)*(8*r+3*ε) := by
  have hb : ∀ v∈s,|ε*v.1-(0:ℝ)|≤2*r := by
    intro v hv
    have hc := (triangularEmbedding_coordinate_bounds v).1
    have hn : ε*‖triangularEmbedding v‖≤r := by
      simpa [scaledEmbedding,norm_mul,Complex.norm_real,abs_of_pos hε] using hball v hv
    rw [sub_zero,abs_mul,abs_of_pos hε]
    nlinarith
  have h := rectangle_mass_le s hε (by positivity : 0≤2*r) hδ
    (a := 0) (b := a) (fun v hv => ⟨hb v hv,hstrip v hv⟩)
  convert h using 1
  ring

theorem norm_le_of_ball (s : Finset Site) (ε r : ℝ) (center : ℂ)
    (hball : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) :
    ∀ v∈s,‖scaledEmbedding ε v‖≤r+‖center‖ := by
  intro v hv
  calc
    _ ≤ ‖scaledEmbedding ε v-center‖+‖center‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add (hball v hv) le_rfl

def band (horizontal : Bool) (ε a δ : ℝ) (v : Site) : Prop :=
  |ε*(if horizontal then (v.2:ℝ) else (v.1:ℝ))-a|≤δ

theorem band_mass_le (s : Finset Site) {ε δ r a : ℝ} (center : ℂ)
    (horizontal : Bool) (hε : 0<ε) (hδ : 0≤δ) (hr : 0≤r)
    (hball : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r)
    (hband : ∀ v∈s,band horizontal ε a δ v) :
    ε^2*(s.card:ℝ)≤(4*δ+3*ε)*(8*(r+‖center‖)+3*ε) := by
  cases horizontal
  · exact vertical_strip_mass_le s hε hδ (by positivity)
      (norm_le_of_ball s ε r center hball) hband
  · exact horizontal_strip_mass_le s hε hδ (by positivity)
      (norm_le_of_ball s ε r center hball) hband

#print axioms band_mass_le
end ExceptionalTimes.LatticeStripMass



