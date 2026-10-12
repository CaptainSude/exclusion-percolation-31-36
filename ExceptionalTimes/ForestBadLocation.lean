import ExceptionalTimes.OrderedForestUI
import ExceptionalTimes.LatticeBoundaryMass

/-! The actual polygon-frontier and collision exclusions have uniformly
small forest-weighted mass, proved from lattice counting and the higher
radial moment. No probability or uniform-integrability premise is added. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.ForestBadLocation
open OrderedForestUI ForestRelabel RootedAnchorLabels ForestLatticeFamily
open LatticeRadial LatticeBadMass LatticeBoundaryMass PairSquareSewing

variable {J F : Type*} [Fintype J] [Fintype F]

theorem polygon_bad_bound {E : F→Type*} [∀ f,Fintype (E f)]
    (k : ℕ) (s : Finset Site) (Q : F→PolygonQuad)
    (A : ∀ f,AxialPolygonPresentation (Q f) (E f))
    {ε δ b c g R r p q w : ℝ} (center : ℂ)
    (hε : 0<ε) (hδ : ε≤δ) (hδ1 : δ≤1) (hc : 0<c) (hb : c*ε≤b) (hg : 0≤g)
    (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr : ε≤r) (hw : 0≤w)
    (hs : ∀ v∈s,‖scaledEmbedding ε v-center‖≤r) (root : J → ℂ) :
    ε^(2*k)*(∑ x∈polygonBadTuples s k Q ε δ,∑ G : eligibleForests (fixed k J),
      graphWeight G.val (anchorPosition k (fun v : s => scaledEmbedding ε v) root x) b g R w)≤
      (badConstant k (Fintype.card (Σ f,E f)) r 2 center*δ)^(1/q)*
        momentConstant (J := J) k c g R r p w := by
  have h := counted_bad_bound k s (polygonBadTuples s k Q ε δ) center
    hε hc hb hg hpq hgp hR hr hw hs root
  have hm := polygon_bad_mass_le s k Q A center hε hδ hδ1 hr hs
  exact h.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_nonneg (pow_nonneg hε.le _) (Nat.cast_nonneg _)) hm
      (one_div_nonneg.mpr hpq.symm.pos.le)) (momentConstant_nonneg k hgp hR.le hw))

theorem uniform_polygon_bad_small {E : F→Type*} [∀ f,Fintype (E f)]
    (k : ℕ) (Q : F→PolygonQuad) (A : ∀ f,AxialPolygonPresentation (Q f) (E f))
    {c g R r p q w η : ℝ} (center : ℂ) (hc : 0<c) (hg : 0≤g)
    (hpq : Real.HolderConjugate p q) (hgp : g*p<2)
    (hR : 0<R) (hr : 0≤r) (hw : 0≤w) (hη : 0<η) :
    ∃δ>0,δ≤1 ∧ ∀(ε b : ℝ) (s : Finset Site),0<ε → ε≤δ → ε≤r → c*ε≤b →
      (∀ v∈s,‖scaledEmbedding ε v-center‖≤r) → ∀root : J→ℂ,
      ε^(2*k)*(∑ x∈polygonBadTuples s k Q ε δ,∑ G : eligibleForests (fixed k J),
        graphWeight G.val (anchorPosition k (fun v : s => scaledEmbedding ε v) root x) b g R w)≤η := by
  let C := badConstant k (Fintype.card (Σ f,E f)) r 2 center
  let M := momentConstant (J := J) k c g R r p w
  have hC : 0≤C := badConstant_nonneg k _ center hr (by norm_num)
  have hM : 0≤M := momentConstant_nonneg k hgp hR.le hw
  let a := η/(M+1)
  have ha : 0<a := div_pos hη (by linarith)
  let θ := a^q
  have hθ : 0<θ := Real.rpow_pos_of_pos ha _
  let δ := min 1 (θ/(C+1))
  have hd : 0<δ := lt_min (by norm_num) (div_pos hθ (by linarith))
  have hd1 : δ≤1 := min_le_left _ _
  have hCd : C*δ≤θ := by
    have h := (le_div_iff₀ (by linarith : 0<C+1)).mp (min_le_right 1 (θ/(C+1)))
    change δ*(C+1)≤θ at h
    nlinarith
  have hθq : θ^(1/q)=a := by
    dsimp [θ]
    rw [←Real.rpow_mul ha.le]
    have hq : q*(1/q)=(1:ℝ) := by field_simp [hpq.symm.pos.ne']
    rw [hq,Real.rpow_one]
  have ham : a*M≤η := by
    have h := (div_mul_cancel₀ η (show M+1≠0 by linarith))
    change a*(M+1)=η at h
    nlinarith
  refine ⟨δ,hd,hd1,?_⟩
  intro ε b s hε hεδ hεr hb hs root
  apply (polygon_bad_bound k s Q A center hε hεδ hd1 hc hb hg hpq hgp hR hεr hw hs root).trans
  change (C*δ)^(1/q)*M≤η
  have hpow := Real.rpow_le_rpow (mul_nonneg hC hd.le) hCd (one_div_nonneg.mpr hpq.symm.pos.le)
  rw [hθq] at hpow
  exact (mul_le_mul_of_nonneg_right hpow hM).trans ham

#print axioms uniform_polygon_bad_small
end ExceptionalTimes.ForestBadLocation
