import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Concrete state space and exceptional-time target

Sites are pairs of integers with the six adjacencies of the triangular
lattice. Black clusters use mathlib's actual graph-walk reachability, and
the dimension target uses mathlib's actual Hausdorff dimension.

This module does not define a fake exclusion process by a list of desired
conclusions. A trajectory is just a function until its probability law and
clock dynamics are separately constructed or identified.
-/

namespace ExceptionalTimes

open scoped ENNReal

abbrev Site := ℤ × ℤ
abbrev Configuration := Site → Bool
abbrev Trajectory := ℝ → Configuration

/-- Coordinates in the basis of two lattice directions at sixty degrees.
The third pair of directions is their difference. -/
def TriangularAdj (u v : Site) : Prop :=
  (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨
  (v.1 = u.1 - 1 ∧ v.2 = u.2) ∨
  (v.1 = u.1 ∧ v.2 = u.2 + 1) ∨
  (v.1 = u.1 ∧ v.2 = u.2 - 1) ∨
  (v.1 = u.1 + 1 ∧ v.2 = u.2 - 1) ∨
  (v.1 = u.1 - 1 ∧ v.2 = u.2 + 1)

theorem triangularAdj_symm {u v : Site} (h : TriangularAdj u v) :
    TriangularAdj v u := by
  unfold TriangularAdj at *
  omega

theorem triangularAdj_irrefl (u : Site) : ¬ TriangularAdj u u := by
  unfold TriangularAdj
  omega

def triangularGraph : SimpleGraph Site where
  Adj := TriangularAdj
  symm := ⟨fun _ _ h => triangularAdj_symm h⟩
  loopless := ⟨triangularAdj_irrefl⟩

/-- White vertices are isolated; an edge is retained exactly when both
endpoints are black. -/
def blackGraph (ω : Configuration) : SimpleGraph Site where
  Adj u v := TriangularAdj u v ∧ ω u = true ∧ ω v = true
  symm := ⟨fun _ _ h => ⟨triangularAdj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => triangularAdj_irrefl u h.1⟩

/-- Requiring the initial vertex to be black removes the isolated white
singleton produced by reflexivity of graph reachability. -/
def BlackCluster (ω : Configuration) (v : Site) : Set Site :=
  {w | ω v = true ∧ (blackGraph ω).Reachable v w}

def HasInfiniteBlackCluster (ω : Configuration) : Prop :=
  ∃ v, (BlackCluster ω v).Infinite

def exceptionalTimes (X : Trajectory) : Set ℝ :=
  {t | 0 ≤ t ∧ HasInfiniteBlackCluster (X t)}

@[simp]
theorem mem_exceptionalTimes (X : Trajectory) (t : ℝ) :
    t ∈ exceptionalTimes X ↔ 0 ≤ t ∧ HasInfiniteBlackCluster (X t) := Iff.rfl

theorem blackGraph_mono {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true) : blackGraph ω ≤ blackGraph η := by
  intro u v huv
  exact ⟨huv.1, h u huv.2.1, h v huv.2.2⟩

theorem blackCluster_mono {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true) (v : Site) :
    BlackCluster ω v ⊆ BlackCluster η v := by
  intro w hw
  exact ⟨h v hw.1, hw.2.mono (blackGraph_mono h)⟩

theorem hasInfiniteBlackCluster_mono {ω η : Configuration}
    (h : ∀ v, ω v = true → η v = true)
    (hω : HasInfiniteBlackCluster ω) : HasInfiniteBlackCluster η := by
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, hv.mono (blackCluster_mono h v)⟩

/-- A finite parallelogram in triangular-lattice coordinates. -/
def latticeBox (n : ℕ) : Finset Site :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).product
    (Finset.Icc (-(n : ℤ)) (n : ℤ))

def latticeRadius (v : Site) : ℕ := max v.1.natAbs v.2.natAbs

theorem mem_latticeBox_of_radius_le {v : Site} {n : ℕ}
    (h : latticeRadius v ≤ n) : v ∈ latticeBox n := by
  rcases v with ⟨x, y⟩
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  have hx : x.natAbs ≤ n := (le_max_left _ _).trans h
  have hy : y.natAbs ≤ n := (le_max_right _ _).trans h
  have hx₁ := Int.le_natAbs (a := x)
  have hx₂ : -x ≤ (x.natAbs : ℤ) := by
    simpa using (Int.le_natAbs (a := -x))
  have hy₁ := Int.le_natAbs (a := y)
  have hy₂ : -y ≤ (y.natAbs : ℤ) := by
    simpa using (Int.le_natAbs (a := -y))
  omega

theorem finite_set_subset_latticeBox {S : Set Site} (hS : S.Finite) :
    ∃ n, S ⊆ (latticeBox n : Set Site) := by
  classical
  refine ⟨hS.toFinset.sup latticeRadius, ?_⟩
  intro v hv
  apply mem_latticeBox_of_radius_le
  exact Finset.le_sup (f := latticeRadius) (hS.mem_toFinset.mpr hv)

/-- Infinite subsets are exactly those that escape every finite box. -/
theorem infinite_iff_escapes_boxes (S : Set Site) :
    S.Infinite ↔ ∀ n, ∃ v ∈ S, v ∉ latticeBox n := by
  classical
  constructor
  · intro hS n
    obtain ⟨v, hv⟩ := (hS.sdiff (latticeBox n).finite_toSet).nonempty
    exact ⟨v, hv.1, hv.2⟩
  · intro hS hfinite
    obtain ⟨n, hn⟩ := finite_set_subset_latticeBox hfinite
    obtain ⟨v, hv, hvn⟩ := hS n
    exact hvn (hn hv)

/-- Connection to the exterior of a box is stated through actual finite
black graph walks, rather than an abstract arm-probability symbol. -/
def OneArm (ω : Configuration) (v : Site) (n : ℕ) : Prop :=
  ∃ w ∈ BlackCluster ω v, w ∉ latticeBox n

theorem infinite_blackCluster_iff_oneArm (ω : Configuration) (v : Site) :
    (BlackCluster ω v).Infinite ↔ ∀ n, OneArm ω v n :=
  infinite_iff_escapes_boxes (BlackCluster ω v)

theorem hasInfiniteBlackCluster_iff_oneArm (ω : Configuration) :
    HasInfiniteBlackCluster ω ↔ ∃ v, ∀ n, OneArm ω v n := by
  exact exists_congr fun v => infinite_blackCluster_iff_oneArm ω v

theorem mem_exceptionalTimes_iff_oneArm (X : Trajectory) (t : ℝ) :
    t ∈ exceptionalTimes X ↔ 0 ≤ t ∧ ∃ v, ∀ n, OneArm (X t) v n := by
  rw [mem_exceptionalTimes, hasInfiniteBlackCluster_iff_oneArm]

theorem latticeBox_mono {m n : ℕ} (hmn : m ≤ n) : latticeBox m ⊆ latticeBox n := by
  rintro ⟨x, y⟩ h
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc] at h ⊢
  omega

theorem mem_latticeBox_succ_of_adj {u v : Site} {n : ℕ}
    (hu : u ∈ latticeBox n) (huv : TriangularAdj u v) : v ∈ latticeBox (n + 1) := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  simp only [latticeBox, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc] at hu ⊢
  unfold TriangularAdj at huv
  omega

/-- A graph walk leaving a region can be transferred up to its first exit
provided every edge starting inside the region is also present in the
second graph. This is a finite-walk induction, with no planar input. -/
theorem reachable_exit_transfer
    {V : Type*} {G H : SimpleGraph V} {S : Set V}
    (hedge : ∀ a b, a ∈ S → G.Adj a b → H.Adj a b)
    {u v : V} (huv : G.Reachable u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ w, w ∉ S ∧ H.Reachable u w := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact (hv hu).elim
  | @cons a b c hab p ih =>
      have hab' : H.Adj a b := hedge a b hu hab
      by_cases hb : b ∈ S
      · obtain ⟨w, hw, hbw⟩ := ih hb hv
        exact ⟨w, hw, hab'.reachable.trans hbw⟩
      · exact ⟨b, hb, hab'.reachable⟩

theorem oneArm_transfer_of_eqOn_box
    {ω η : Configuration} {v : Site} {n : ℕ} (hv : v ∈ latticeBox n)
    (heq : Set.EqOn ω η (latticeBox (n + 1) : Set Site))
    (hω : OneArm ω v n) : OneArm η v n := by
  obtain ⟨w, hw, hwn⟩ := hω
  have hedge : ∀ a b, a ∈ (latticeBox n : Set Site) →
      (blackGraph ω).Adj a b → (blackGraph η).Adj a b := by
    intro a b ha hab
    have ha' : a ∈ latticeBox (n + 1) := latticeBox_mono (Nat.le_succ n) ha
    have hb' : b ∈ latticeBox (n + 1) := mem_latticeBox_succ_of_adj ha hab.1
    refine ⟨hab.1, ?_, ?_⟩
    · rw [← heq ha']
      exact hab.2.1
    · rw [← heq hb']
      exact hab.2.2
  obtain ⟨z, hzn, hvz⟩ := reachable_exit_transfer hedge hw.2 hv hwn
  refine ⟨z, ⟨?_, hvz⟩, hzn⟩
  rw [← heq (latticeBox_mono (Nat.le_succ n) hv)]
  exact hw.1

/-- The one-arm event from a vertex inside the box depends on only
finitely many colors: the next larger box. The original global-walk
definition is unchanged. -/
theorem oneArm_congr_of_eqOn_box
    {ω η : Configuration} {v : Site} {n : ℕ} (hv : v ∈ latticeBox n)
    (heq : Set.EqOn ω η (latticeBox (n + 1) : Set Site)) :
    OneArm ω v n ↔ OneArm η v n :=
  ⟨oneArm_transfer_of_eqOn_box hv heq, oneArm_transfer_of_eqOn_box hv heq.symm⟩

abbrev BoxConfiguration (n : ℕ) := ↥(latticeBox (n + 1)) → Bool

def boxRestriction (n : ℕ) (ω : Configuration) : BoxConfiguration n := fun v => ω v

/-- One explicit extension of a finite coloring; the choice of white
outside the box is irrelevant to the one-arm event by the theorem above. -/
def boxCompletion (n : ℕ) (ξ : BoxConfiguration n) : Configuration := fun v =>
  if hv : v ∈ latticeBox (n + 1) then ξ ⟨v, hv⟩ else false

theorem boxCompletion_restriction_eqOn (n : ℕ) (ω : Configuration) :
    Set.EqOn ω (boxCompletion n (boxRestriction n ω))
      (latticeBox (n + 1) : Set Site) := by
  intro v hv
  change v ∈ latticeBox (n + 1) at hv
  simp [boxCompletion, boxRestriction, hv]

theorem measurable_boxRestriction (n : ℕ) : Measurable (boxRestriction n) :=
  measurable_pi_iff.mpr fun v => measurable_pi_apply (v : Site)

theorem oneArm_iff_black_of_not_mem_box
    (ω : Configuration) {v : Site} {n : ℕ} (hv : v ∉ latticeBox n) :
    OneArm ω v n ↔ ω v = true := by
  constructor
  · rintro ⟨w, hw, _⟩
    exact hw.1
  · intro hω
    exact ⟨v, ⟨hω, SimpleGraph.Reachable.refl v⟩, hv⟩

/-- One-arm events are measurable cylinder events in the independent-color
configuration space. This theorem assumes no probability law. -/
theorem measurableSet_oneArm (v : Site) (n : ℕ) :
    MeasurableSet {ω : Configuration | OneArm ω v n} := by
  classical
  by_cases hv : v ∈ latticeBox n
  · have hlocal : MeasurableSet
        {ξ : BoxConfiguration n | OneArm (boxCompletion n ξ) v n} :=
      (Set.toFinite _).measurableSet
    have hevent : {ω : Configuration | OneArm ω v n} =
        boxRestriction n ⁻¹' {ξ | OneArm (boxCompletion n ξ) v n} := by
      ext ω
      exact oneArm_congr_of_eqOn_box hv (boxCompletion_restriction_eqOn n ω)
    rw [hevent]
    exact hlocal.preimage (measurable_boxRestriction n)
  · have hevent : {ω : Configuration | OneArm ω v n} =
        (fun ω : Configuration => ω v) ⁻¹' {true} := by
      ext ω
      exact oneArm_iff_black_of_not_mem_box ω hv
    rw [hevent]
    exact (measurableSet_singleton true).preimage (measurable_pi_apply v)

theorem measurableSet_hasInfiniteBlackCluster :
    MeasurableSet {ω : Configuration | HasInfiniteBlackCluster ω} := by
  have hevent : {ω : Configuration | HasInfiniteBlackCluster ω} =
      ⋃ v : Site, ⋂ n : ℕ, {ω : Configuration | OneArm ω v n} := by
    ext ω
    simpa only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter] using
      hasInfiniteBlackCluster_iff_oneArm ω
  rw [hevent]
  exact MeasurableSet.iUnion fun v => MeasurableSet.iInter fun n => measurableSet_oneArm v n

theorem measurableSet_exceptionalTimes (X : Trajectory) (hX : Measurable X) :
    MeasurableSet (exceptionalTimes X) :=
  measurableSet_Ici.inter (measurableSet_hasInfiniteBlackCluster.preimage hX)

/-- The exact target for a fixed realized trajectory. This definition
contains no dynamical or probabilistic claim. -/
def ExceptionalDimension (X : Trajectory) (d : ℝ≥0∞) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b →
    dimH (exceptionalTimes X ∩ Set.Ioo a b) = d

/-- Checking rational endpoints suffices for all positive-length windows.
This is the deterministic step needed after taking a countable intersection
of probability-one events. -/
theorem exceptionalDimension_of_rational_windows
    (X : Trajectory) (d : ℝ≥0∞)
    (h : ∀ p q : ℚ, 0 ≤ p → p < q →
      dimH
        (exceptionalTimes X ∩ Set.Ioo (p : ℝ) (q : ℝ)) = d) :
    ExceptionalDimension X d := by
  intro a b ha hab
  obtain ⟨p, hap, hpb⟩ := exists_rat_btwn hab
  obtain ⟨q, hpq, hqb⟩ := exists_rat_btwn hpb
  have hp0 : 0 ≤ p := by exact_mod_cast (ha.trans hap.le)
  have hpq' : p < q := by exact_mod_cast hpq
  have hlower : d ≤ dimH (exceptionalTimes X ∩ Set.Ioo a b) := by
    rw [← h p q hp0 hpq']
    apply dimH_mono
    intro t ht
    exact ⟨ht.1, hap.trans ht.2.1, ht.2.2.trans hqb⟩
  obtain ⟨r, hbr⟩ := exists_rat_gt b
  have hr0 : (0 : ℚ) < r := by
    exact_mod_cast (ha.trans_lt (hab.trans hbr))
  have hupper : dimH (exceptionalTimes X ∩ Set.Ioo a b) ≤ d := by
    rw [← h 0 r (le_refl 0) hr0]
    apply dimH_mono
    intro t ht
    refine ⟨ht.1, ?_, ht.2.2.trans hbr⟩
    simpa only [Rat.cast_zero] using ha.trans_lt ht.2.1
  exact le_antisymm hupper hlower

theorem exceptionalDimension_iff_rational_windows (X : Trajectory) (d : ℝ≥0∞) :
    ExceptionalDimension X d ↔
      ∀ p q : ℚ, 0 ≤ p → p < q →
        dimH
          (exceptionalTimes X ∩ Set.Ioo (p : ℝ) (q : ℝ)) = d := by
  constructor
  · intro h p q hp hpq
    apply h (p : ℝ) (q : ℝ)
    · exact_mod_cast hp
    · exact_mod_cast hpq
  · exact exceptionalDimension_of_rational_windows X d

/-- Countability of rational windows permits a single probability-one
event on which the target holds for every real window simultaneously.
There is no measurability assumption hidden in this deterministic upgrade:
the displayed almost-everywhere hypotheses are its exact input. -/
theorem ae_exceptionalDimension_of_ae_rational_windows
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X : Ω → Trajectory) (d : ℝ≥0∞)
    (h : ∀ p q : ℚ, 0 ≤ p → p < q →
      ∀ᵐ ω ∂μ, dimH
        (exceptionalTimes (X ω) ∩ Set.Ioo (p : ℝ) (q : ℝ)) = d) :
    ∀ᵐ ω ∂μ, ExceptionalDimension (X ω) d := by
  have h' : ∀ p q : ℚ, ∀ᵐ ω ∂μ, 0 ≤ p → p < q →
      dimH (exceptionalTimes (X ω) ∩ Set.Ioo (p : ℝ) (q : ℝ)) = d := by
    intro p q
    by_cases hp : 0 ≤ p
    · by_cases hpq : p < q
      · exact (h p q hp hpq).mono fun _ hω _ _ => hω
      · exact Filter.Eventually.of_forall fun _ _ hpq' => (hpq hpq').elim
    · exact Filter.Eventually.of_forall fun _ hp' _ => (hp hp').elim
  have hboth : ∀ᵐ ω ∂μ, ∀ p q : ℚ, 0 ≤ p → p < q →
      dimH (exceptionalTimes (X ω) ∩ Set.Ioo (p : ℝ) (q : ℝ)) = d :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      MeasureTheory.ae_all_iff.mpr fun q => h' p q
  exact hboth.mono fun ω hω => exceptionalDimension_of_rational_windows (X ω) d hω

theorem ExceptionalDimension.nonempty_window
    {X : Trajectory} {d : ℝ≥0∞} (hX : ExceptionalDimension X d) (hd : d ≠ 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (exceptionalTimes X ∩ Set.Ioo a b).Nonempty := by
  by_contra h
  have hempty : exceptionalTimes X ∩ Set.Ioo a b = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp h
  have hdim := hX a b ha hab
  rw [hempty, dimH_empty] at hdim
  exact hd hdim.symm

def rescaleTime (c : ℝ) (X : Trajectory) : Trajectory := fun t => X (c * t)

/-- Multiplying every clock rate by the same positive constant preserves
the dimension target in every interval. This is a statement about actual
Hausdorff dimension under an invertible linear change of the time axis. -/
theorem ExceptionalDimension.rescaleTime
    {X : Trajectory} {d : ℝ≥0∞} (hX : ExceptionalDimension X d)
    {c : ℝ} (hc : 0 < c) : ExceptionalDimension (ExceptionalTimes.rescaleTime c X) d := by
  intro a b ha hab
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc.ne')
  have he : ∀ t : ℝ, e t = c * t := fun _ => rfl
  have hsets : exceptionalTimes (ExceptionalTimes.rescaleTime c X) ∩ Set.Ioo a b =
      e ⁻¹' (exceptionalTimes X ∩ Set.Ioo (c * a) (c * b)) := by
    ext t
    change ((0 ≤ t ∧ HasInfiniteBlackCluster (X (c * t))) ∧ a < t ∧ t < b) ↔
      ((0 ≤ e t ∧ HasInfiniteBlackCluster (X (e t))) ∧ c * a < e t ∧ e t < c * b)
    rw [he]
    simp only [mul_nonneg_iff_of_pos_left hc, mul_lt_mul_iff_right₀ hc]
  rw [hsets, e.dimH_preimage]
  exact hX (c * a) (c * b) (mul_nonneg hc.le ha) (mul_lt_mul_of_pos_left hab hc)

/-- This is the literal numerical target, not a theorem asserting it. -/
def HasConjecturedExceptionalDimension (X : Trajectory) : Prop :=
  ExceptionalDimension X (31 / 36 : ℝ≥0∞)

def AlmostSureConjecturedDimension
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X : Ω → Trajectory) : Prop :=
  ∀ᵐ ω ∂μ, HasConjecturedExceptionalDimension (X ω)

end ExceptionalTimes

#print axioms ExceptionalTimes.infinite_iff_escapes_boxes
#print axioms ExceptionalTimes.hasInfiniteBlackCluster_iff_oneArm
#print axioms ExceptionalTimes.exceptionalDimension_of_rational_windows
#print axioms ExceptionalTimes.ae_exceptionalDimension_of_ae_rational_windows
#print axioms ExceptionalTimes.oneArm_congr_of_eqOn_box
#print axioms ExceptionalTimes.measurableSet_hasInfiniteBlackCluster
#print axioms ExceptionalTimes.ExceptionalDimension.rescaleTime
