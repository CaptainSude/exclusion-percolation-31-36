import ExceptionalTimes.ForestGeometryEnvelope
import ExceptionalTimes.CircularStaticProfile
import ExceptionalTimes.DyadicSupportBox

/-! One concrete forest envelope, shared by the geometry, mass and
fixed-degree sewing certificates on the actual positive matching cover. -/
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace ExceptionalTimes.DyadicForestEnvelope
open PairSquareSewing IndependentAnnulusInput UnitReferenceCover DimerSelectedDictionary
open CircularStaticProfile ForestGeometryEnvelope LatticeRadial

variable {F : Type*} [Fintype F]

noncomputable def sites (R n : ℕ) : Finset Site := latticeBox (R*2^n)
noncomputable abbrev Blocks (R : ℕ) (phase : Bool) (n : ℕ) := anchors phase (sites R n)
noncomputable def ballRadius (R : ℕ) : ℝ := 2*((R:ℝ)+1)

noncomputable def geometry (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) (n : ℕ) (S : Finset (Blocks R phase n)) : DimerGeometry S T.Roots :=
  T.geometry hplane n (1,0) (selectedSlot (slot phase (sites R n)) S)
    (fun i => slot_positive phase (sites R n) i.val)

noncomputable def value (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) (B C₄ C₃ Q c g : ℝ) (n : ℕ) : Finset (Blocks R phase n)→ℝ :=
  envelope (geometry hplane T R phase n) (B*mesh n) T.stop (11*B*ballRadius R)
    (max 1 (Q/c)) (canonicalForestConstant F C₄ C₃ c (max 1 (Q/c)) Q g) g
    (profile (mesh n) (mesh_pos n) B T.stop)

theorem ballRadius_pos (R : ℕ) : 0<ballRadius R := by unfold ballRadius; positivity

theorem stop_four_lt_one (T : DyadicQuadFamily F) : 4*T.stop<1 := by
  have hi : ((2:ℝ)^T.maxLevel)⁻¹≤1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  unfold DyadicQuadFamily.stop
  linarith

omit [Fintype F] in
theorem geometry_root (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) (n : ℕ) (S : Finset (Blocks R phase n)) :
    (geometry hplane T R phase n S).root=T.root hplane := rfl

omit [Fintype F] in
theorem geometry_anchor (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) (n : ℕ) (S : Finset (Blocks R phase n)) (i : S) :
    position (geometry hplane T R phase n S).mesh
      ((geometry hplane T R phase n S).endpoint (i,0))=scaledEmbedding (mesh n) i.val.val := by
  change position (mesh n) (slot phase (sites R n) (i.val,0))=_
  rw [slot_zero]
  rfl

omit [Fintype F] in
theorem geometry_margin (hplane : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (R : ℕ) (phase : Bool) (n : ℕ) (S : Finset (Blocks R phase n)) :
    (geometry hplane T R phase n S).margin=mesh n := by
  have he : triangularEmbedding ((1,0) : Site)=(1:ℂ) := by
    apply Complex.ext <;> norm_num [triangularEmbedding]
  change max (mesh n) (mesh n*‖triangularEmbedding ((1,0) : Site)‖)=_
  rw [he,norm_one,mul_one,max_self]

theorem anchor_bound (R : ℕ) (phase : Bool) (n : ℕ) (a : Site)
    (ha : a∈anchors phase (sites R n)) :
    ‖scaledEmbedding (mesh n) a-(0:ℂ)‖≤ballRadius R := by
  simpa only [sub_zero, ballRadius] using Source06Specialization.box_anchor_physical_bound R n phase a ha

#print axioms geometry_margin
#print axioms anchor_bound
end ExceptionalTimes.DyadicForestEnvelope
