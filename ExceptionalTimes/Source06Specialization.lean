import ExceptionalTimes.SourceSampling

/-!
Finite, physical specialization of source06, pinned at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The imported statement below is a
consequence of Lemma 6.5 and the relative many-trial estimate (6.6 and its
following averaging argument), together with source02 fixed-shape/cut
quasi-multiplicativity. It is not claimed verbatim: the source uses square
annular costs, while this statement uses the literal circular-cut costs
`sourceArmCost`. The fixed comparison constants are absorbed in the desired
error BEFORE the finite list of trials is chosen.

The inputs are fixed finite physical polygons and a compact separated
location range. The outputs are ordinary iid source events, their stated
local/symmetry properties, the ordinary one-time necklace reading, and the
FIRST-POINT failure probability. No signed pair expectation, canonical
block law, arbitrary filter/cost function, full-k error, or limiting
dynamical comparison is included in the published input.
-/

open Set
open scoped Classical
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open EnvironmentVariance PolygonSewing

noncomputable def outerRadius {q k : ℕ} (G : SourceSeparatedGeometry q k) : ℝ :=
  min G.margin 1 / 128

theorem outerRadius_pos {q k : ℕ} (G : SourceSeparatedGeometry q k) :
    0<outerRadius G := div_pos (lt_min G.margin_pos (by norm_num)) (by norm_num)

/-- The ordinary source sample is fixed by actual tested-cell supports.
No arbitrary finite exterior is substituted for the full-plane cylinders. -/
noncomputable def sample {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : ℝ) (he : 0<e) (x : Fin (k+1)→Site) (h : ℝ) : Finset Site :=
  G.sampleSites e he x (2*outerRadius G) ∪
    (sourceReferenceAt e he (x 0)).support ∪ sourceSquareSites e he (x 0) h

/-- Physical circular inside and central pocket; only the annular support
is supplied by the source construction. The unused sleeve fields of the
algebraic layout are empty, because ordinary readout supplies its actual
necklace witnesses directly. -/
noncomputable def annularLayout (Λ support : Finset Site) (e : ℝ) (x : Site)
    (r L : ℝ) (hr : 0<r) (hL : 1≤L)
    (hlo : ∀v∈support,r/L≤dist (position e v) (position e x)) : SourceSeamLayout where
  inside := Λ.filter (fun v => dist (position e v) (position e x)≤r)
  support := support
  innerSleeve := ∅
  outerSleeve := ∅
  pocket := Λ.filter (fun v => dist (position e v) (position e x)<r/L)
  inner_supported := Finset.empty_subset _
  outer_supported := Finset.empty_subset _
  pocket_inside := by
    intro v hv
    obtain ⟨hvΛ,hv⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hvΛ,hv.le.trans (div_le_self hr.le hL)⟩
  pocket_disjoint := by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    exact (not_lt_of_ge (hlo v hs)) (Finset.mem_filter.mp hv).2

structure AnnularSupports (Λ : Finset Site) (e : ℝ) (x : Site) (n : ℕ)
    (radii : Fin n→ℝ) (L : ℝ) where
  sites : Fin n→Finset Site
  sampled : ∀i,sites i⊆Λ
  lower : ∀i v,v∈sites i→ radii i/L≤dist (position e v) (position e x)
  upper : ∀i v,v∈sites i→dist (position e v) (position e x)≤L*radii i

noncomputable def AnnularSupports.layout {Λ : Finset Site} {e : ℝ} {x : Site} {n : ℕ}
    {radii : Fin n→ℝ} {L : ℝ} (A : AnnularSupports Λ e x n radii L)
    (hr : ∀i,0<radii i) (hL : 1≤L) (i : Fin n) : SourceSeamLayout :=
  annularLayout Λ (A.sites i) e x (radii i) L (hr i) hL (A.lower i)

/-- Ordered buffered radii give adaptive cross-trial invariance entirely
by deterministic support geometry. No adaptive-invariance theorem is
added to the published probability input. -/
theorem AnnularSupports.nested {Λ : Finset Site} {e : ℝ} {x : Site} {n : ℕ}
    {radii : Fin n→ℝ} {L : ℝ} (A : AnnularSupports Λ e x n radii L)
    (hr : ∀i,0<radii i) (hL : 1≤L)
    (hsep : ∀i j,i<j→L*radii i<radii j/L) :
    ∀i j,j=i ∨ (A.layout hr hL j).support⊆(A.layout hr hL i).inside ∨
      Disjoint (A.layout hr hL j).support (A.layout hr hL i).inside := by
  intro i j
  rcases lt_trichotomy i j with hij|heq|hji
  · right; right
    change Disjoint (A.sites j) (Λ.filter _)
    apply Finset.disjoint_left.mpr
    intro v hv hi
    have hrad : radii i≤L*radii i := by nlinarith [hr i]
    have hlo := A.lower j v hv
    have hup := (Finset.mem_filter.mp hi).2
    have hs := hsep i j hij
    linarith
  · exact Or.inl heq.symm
  · right; left
    intro v hv
    change v∈Λ.filter _
    refine Finset.mem_filter.mpr ⟨A.sampled j hv,?_⟩
    have hu := A.upper j v hv
    have hs := hsep j i hji
    exact hu.trans (hs.le.trans (div_le_self (hr i).le hL))

noncomputable def microProbe (e : ℝ) (he : 0<e) (x : Site) (B0 M R : ℝ)
    (hB0 : 0<B0) (hM : 0<M) (hsmall : 4*(M*(B0*e))<R) : Probe :=
  ⟨e,x,M*(B0*e),R,he,mul_pos hM (mul_pos hB0 he),hsmall⟩

noncomputable def squareProbe (e : ℝ) (he : 0<e) (x : Site) (h R : ℝ)
    (hh : 0<h) (hsmall : 4*(8*h)<R) : Probe :=
  ⟨e,x,8*h,R,he,mul_pos (by norm_num) hh,hsmall⟩

/-- This is a specialization to the actual source event U, not to the
stronger and separately formalized `SourceSeamLayout.success` predicate.
Source Lemma 6.5 supplies `reading`; the source's four inside/outside
combinations supply the two exchange symmetries. -/
structure SourceTrials {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (B0 M ε : ℝ) (hB0 : 0<B0) (hM : 0<M)
    (n : ℕ) (radii : Fin n→ℝ) (L : ℝ) (hr : ∀i,0<radii i) (hL : 1≤L)
    (h e : ℝ) (hh : 0<h) (he : 0<e) (x : Fin (k+1)→Site)
    (hmic : 4*(M*(B0*e))<outerRadius G) (hsq : 4*(8*h)<outerRadius G)
    (ha : 4*(B0*e)<1) (hb : 4*h<1) where
  annuli : AnnularSupports (sample G e he x h) e (x 0) n radii L
  success : Fin n→Sources (sample G e he x h)→Bool
  supported : ∀i,SupportedSourceTest (annuli.sites i) (success i)
  source_swap : ∀i ω,success i ω.swap=success i ω
  inside_swap : ∀i ω,success i (seamSwap (annuli.layout hr hL i).inside ω)=success i ω
  reading : ∀i ω,success i ω=true→
    SourcePolygonSeamReading (annuli.layout hr hL i) ω
      (G.latticeQuads e he) (fun _ : Unit => sourceReferenceAt e he (x 0))
  failure : SourceEventFixedSquareFailure success
    (microProbe e he (x 0) B0 M (outerRadius G) hB0 hM hmic)
    (squareProbe e he (x 0) h (outerRadius G) hh hsq)
    (sourceArmCost e (B0*e) he (mul_pos hB0 he) ha)
    (sourceArmCost e h he hh hb) ε

theorem SourceTrials.adaptive_invariance {q k : ℕ} {G : SourceSeparatedGeometry q k}
    {B0 M ε : ℝ} {hB0 : 0<B0} {hM : 0<M}
    {n : ℕ} {radii : Fin n→ℝ} {L : ℝ} {hr : ∀i,0<radii i} {hL : 1≤L}
    {h e : ℝ} {hh : 0<h} {he : 0<e} {x : Fin (k+1)→Site}
    {hmic : 4*(M*(B0*e))<outerRadius G} {hsq : 4*(8*h)<outerRadius G}
    {ha : 4*(B0*e)<1} {hb : 4*h<1}
    (T : SourceTrials G B0 M ε hB0 hM n radii L hr hL h e hh he x hmic hsq ha hb)
    (hsep : ∀i j,i<j→L*radii i<radii j/L) :
    ∀i ω,T.success i ω=true→∀j,
      T.success j (seamSwap (T.annuli.layout hr hL i).inside ω)=T.success j ω :=
  trial_invariance_of_nested_supports T.success
    (fun i => (T.annuli.layout hr hL i).inside) T.annuli.sites
    T.supported T.source_swap T.inside_swap (T.annuli.nested hr hL hsep)

/-- Exact epsilon bookkeeping for the fixed-shape/cut comparison.
The source estimate is used with epsilon/C^2 BEFORE its trials are chosen.
Only inequalities between the costs are used, never an asserted equality. -/
theorem relative_error_of_cost_comparison {p A B a b C ε : ℝ}
    (hC : 0<C) (hε : 0≤ε) (ha : 0≤a) (hB : 0≤B)
    (hA : A≤C*a) (hB' : B≤C*b)
    (hp : p≤(ε/(C*C))*(A*B)) : p≤ε*(a*b) := by
  calc
    p≤(ε/(C*C))*(A*B) := hp
    _≤(ε/(C*C))*((C*a)*(C*b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hA hB' hB (mul_nonneg hC.le ha))
        (div_nonneg hε (mul_nonneg hC.le hC.le))
    _=ε*(a*b) := by
      field_simp [ne_of_gt hC]

/-- Published geometric/probabilistic consequence, with genuine real
small-parameter order. M, the finite trial list and its enlargement are
fixed before h; h is fixed before e. The mesh threshold is uniform over
all admissible locations in the specified compact separated range.

The lower bound on B0 expresses the source's fixed microscopic cutoff.
It does not assert any conclusion about the canonical dimer process. -/
def PublishedFixedSquareSeams (B0 : ℝ) : Prop :=
  128≤B0 ∧ ∀q k (G : SourceSeparatedGeometry q k) (ε : ℝ),0<ε→
    ∃M : ℝ,64≤M ∧ ∃n : ℕ,0<n ∧ ∃L : ℝ,2≤L ∧ ∃radii : Fin n→ℝ,
    (∀i,0<radii i) ∧ (∀i,L*radii i<outerRadius G) ∧
    (∀i j,i<j→L*radii i<radii j/L) ∧
    ∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀hh : 0<h,h<h0→
      ∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
        ∀x : Fin (k+1)→Site,G.Admissible e x→
          ∃hB0 : 0<B0,∃hM : 0<M,∃hr : ∀i,0<radii i,∃hL : 1≤L,
          ∃hmic : 4*(M*(B0*e))<outerRadius G,
          ∃hsq : 4*(8*h)<outerRadius G,
          ∃ha : 4*(B0*e)<1,∃hb : 4*h<1,
            (∀i,64*(M*(B0*e)+h)<radii i/L) ∧
            Nonempty (SourceTrials G B0 M ε hB0 hM n radii L hr hL
              h e hh he x hmic hsq ha hb)

/-- Minimal literal finite sample for the source's reference square Delta. -/
noncomputable def referenceSample (e : ℝ) (he : 0<e) (x : Site) (h : ℝ) : Finset Site :=
  (sourceReferenceAt e he x).support ∪ sourceSquareSites e he x h

/-- Source06 Lemma 6.1 for its actual Q0 and its literal forced square.
The circular cost is obtained by the separately identified conventional
source02 fixed-shape/cut comparison. Translation is only by lattice sites.
This statement is about an ordinary static fair field, not a pair process. -/
def PublishedReferenceSquareLower : Prop :=
  ∃c : ℝ,0<c ∧ ∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀hh : 0<h,h<h0→
    ∃hb : 4*h<1,∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→∀x : Site,
      c*sourceArmCost e h he hh hb ≤
        averagedSquareDelta (referenceSample e he x h)
          (sourceSquareSites e he x h) (sourceReferenceAt e he x)

/-- The SAME actual jump observable has the source's half normalization;
there is no free reference-area or calibrator parameter in this adapter. -/
theorem reference_square_jump_lower (hsource : PublishedReferenceSquareLower) :
    ∃c : ℝ,0<c ∧ ∃h0 : ℝ,0<h0 ∧ ∀h : ℝ,∀hh : 0<h,h<h0→
      ∃hb : 4*h<1,∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→∀x : Site,
        c*sourceArmCost e h he hh hb ≤
          averagedSquareResponse (referenceSample e he x h)
            (sourceSquareSites e he x h) (sourceReferenceAt e he x).jump := by
  obtain ⟨c,hc,h0,hh0,hsource⟩ := hsource
  refine ⟨c/2,half_pos hc,h0,hh0,?_⟩
  intro h hh hh0'
  obtain ⟨hb,e0,he0,hbound⟩ := hsource h hh hh0'
  refine ⟨hb,e0,he0,?_⟩
  intro e he he0' x
  exact square_jump_lower_of_delta _ _ _ _ _ (hbound e he he0' x)

#print axioms relative_error_of_cost_comparison
#print axioms SourceTrials.adaptive_invariance
#print axioms reference_square_jump_lower
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization





