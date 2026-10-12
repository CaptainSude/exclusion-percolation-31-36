import ExceptionalTimes.CanonicalScaleProduct
import ExceptionalTimes.ContactCrosscutOrder
import ExceptionalTimes.RadialDimerSeparation
import ExceptionalTimes.ActivePartitionLaw

/-! Literal separated hexagonal annuli required by a circular four-arm
probe. Their supports consist of whole dimers and are proved disjoint
for every fixed displacement. The resulting decay is under the actual
canonical finite product law, not an assumed independence principle. -/

open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.CanonicalHexAnnuli

open Annulus PairSquareSewing CanonicalScaleProduct RadialDimerSeparation
open ActivePartitionLaw ManyDimerLaw DimerLaw

def region (x : Site) (r R : ℤ) : Set Site :=
  {v | r≤hexRadius (v-x) ∧ hexRadius (v-x)≤R}

/-- Four actual alternating simple paths with the exact endpoint order
at both hexagonal boundaries. -/
def HexFourArms (x : Site) (r R : ℤ) (ω : Configuration) : Prop :=
  ∃ s t : Fin 4 → Site, ∃ q : ∀ i, triangularGraph.Walk (s i) (t i),
    (∀ i, (q i).IsPath) ∧
    (∀ i, hexRadius (s i)=r ∧ hexRadius (t i)=R) ∧
    (∀ i z,z∈(q i).support → r≤hexRadius z ∧ hexRadius z≤R ∧
      ω (z+x)=decide (i.val % 2=0)) ∧
    (∀ i z,z∈(q i).support → hexRadius z=r → z=s i) ∧
    (∀ i z,z∈(q i).support → hexRadius z=R → z=t i) ∧
    (∀ i j,i≠j → List.Disjoint (q i).support (q j).support) ∧
    CyclicAngles (fun i => triangularEmbedding (s i)) ∧
    CyclicAngles (fun i => triangularEmbedding (t i))

theorem HexFourArms.congr {x : Site} {r R : ℤ} {ω η : Configuration}
    (he : Set.EqOn ω η (region x r R)) : HexFourArms x r R ω ↔ HexFourArms x r R η := by
  have forward {a b : Configuration} (h : Set.EqOn a b (region x r R))
      (ha : HexFourArms x r R a) : HexFourArms x r R b := by
    obtain ⟨s,t,q,hpath,hends,hcolor,hin,hout,hdis,hs,ht⟩ := ha
    refine ⟨s,t,q,hpath,hends,?_,hin,hout,hdis,hs,ht⟩
    intro i z hz
    obtain ⟨hlo,hhi,hcol⟩ := hcolor i z hz
    refine ⟨hlo,hhi,?_⟩
    have hm : z+x∈region x r R := by simpa only [region,Set.mem_ofPred_eq,add_sub_cancel_right] using And.intro hlo hhi
    exact (h hm).symm.trans hcol
  exact ⟨forward he,forward he.symm⟩

theorem circular_requires_hex (orderInput : PublishedAnnularCrosscutOrder)
    (P : Probe) (r R : ℤ) (hr : 0<r) (hrR : r<R)
    (hinner : 4*P.innerRadius≤P.mesh*(r:ℝ))
    (houter : 2*P.mesh*(R:ℝ)≤P.outerRadius) {ω : Configuration}
    (ha : FourArms P ω) : HexFourArms P.center r R ω :=
  fourArms_ordered_hex_paths orderInput P ω r R hr hrR hinner houter ha

theorem hexRadius_add_le (v w : Site) : hexRadius (v+w)≤hexRadius v+hexRadius w := by
  have vx : |v.1|≤hexRadius v := (le_max_left _ _).trans (le_max_left _ _)
  have vy : |v.2|≤hexRadius v := (le_max_right _ _).trans (le_max_left _ _)
  have vs : |v.1+v.2|≤hexRadius v := le_max_right _ _
  have wx : |w.1|≤hexRadius w := (le_max_left _ _).trans (le_max_left _ _)
  have wy : |w.2|≤hexRadius w := (le_max_right _ _).trans (le_max_left _ _)
  have ws : |w.1+w.2|≤hexRadius w := le_max_right _ _
  simp only [hexRadius,Prod.fst_add,Prod.snd_add,max_le_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact (abs_add_le _ _).trans (add_le_add vx wx)
  · exact (abs_add_le _ _).trans (add_le_add vy wy)
  · have he : v.1+w.1+(v.2+w.2)=(v.1+v.2)+(w.1+w.2) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add vs ws)

theorem hexRadius_le_twice_box {v : Site} {d : ℕ} (hv : v∈latticeBox d) :
    hexRadius v≤2*(d:ℤ) := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] at hv
  have hx : |v.1|≤(d:ℤ) := abs_le.mpr hv.1
  have hy : |v.2|≤(d:ℤ) := abs_le.mpr hv.2
  simp only [hexRadius,max_le_iff]
  refine ⟨⟨by omega,by omega⟩,?_⟩
  exact (abs_add_le _ _).trans (by omega)

theorem region_gap {x v w : Site} {r R s S : ℤ} {d : ℕ}
    (hgap : R+2*(d:ℤ)<s) (hv : v∈region x r R) (hw : w∈region x s S) :
    v-w∉latticeBox d := by
  intro hdiff
  have hn : w-v∈latticeBox d := by
    simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc,
      Prod.fst_sub,Prod.snd_sub] at hdiff ⊢
    omega
  have hnorm := hexRadius_add_le (w-v) (v-x)
  have he : w-v+(v-x)=w-x := by abel
  rw [he] at hnorm
  have hd := hexRadius_le_twice_box hn
  change r≤hexRadius (v-x) ∧ hexRadius (v-x)≤R at hv
  change s≤hexRadius (w-x) ∧ hexRadius (w-x)≤S at hw
  omega

variable {B : Type*}

theorem decoded_local (slot : B×Fin 2 ↪ Site) (S : Set Site) {a b : B → Color}
    (he : Set.EqOn a b (touching slot S)) : Set.EqOn (pairDecode slot a) (pairDecode slot b) S := by
  intro v hv
  by_cases hm : v∈Set.range slot
  · obtain ⟨⟨i,e⟩,rfl⟩ := hm
    simp only [pairDecode,slot.injective.extend_apply]
    exact congrFun (he (show i∈touching slot S from ⟨e,hv⟩)) e
  · simp only [pairDecode,Function.extend_apply' _ _ _ hm]

theorem hex_local (slot : B×Fin 2 ↪ Site) (x : Site) (r R : ℤ) (a b : B → Color)
    (he : Set.EqOn a b (touching slot (region x r R))) :
    HexFourArms x r R (pairDecode slot a) ↔ HexFourArms x r R (pairDecode slot b) :=
  HexFourArms.congr (decoded_local slot _ he)

theorem touching_annuli_pairwise (N : ℕ) (slot : B×Fin 2 ↪ Site) (z x : Site) {d : ℕ}
    (hz : z∈latticeBox d)
    (hpartner : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (r R : Fin N → ℤ) (hgap : ∀ i j,i<j → R i+2*(d:ℤ)<r j) :
    Pairwise (fun i j => Disjoint (touching slot (region x (r i) (R i)))
      (touching slot (region x (r j) (R j)))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact touching_disjoint slot z hz hpartner _ _ (fun _ hv _ hw => region_gap (hgap i j h) hv hw)
  · exact (touching_disjoint slot z hz hpartner _ _ (fun _ hv _ hw => region_gap (hgap j i h) hv hw)).symm

variable [Fintype B]

/-- Actual circular four-arm probability is bounded by the product of
reference-time probabilities on separated fixed-aspect hex annuli. -/
theorem circular_probability_le_power (orderInput : PublishedAnnularCrosscutOrder)
    (N : ℕ) (slot : B×Fin 2 ↪ Site) (z : Site) {d : ℕ}
    (hz : z∈latticeBox d)
    (hpartner : ∀ b,slot (b,1)=PeriodicMatching.partner z (slot (b,0)))
    (P : Probe) (r R : Fin N → ℤ) (hr : ∀ i,0<r i) (hrR : ∀ i,r i<R i)
    (hgap : ∀ i j,i<j → R i+2*(d:ℤ)<r j)
    (hinner : ∀ i,4*P.innerRadius≤P.mesh*(r i:ℝ))
    (houter : ∀ i,2*P.mesh*(R i:ℝ)≤P.outerRadius)
    (reference : Fin N → ℝ) (t : ℝ) (ht : 0≤t)
    (href0 : ∀ i,0≤reference i) (href : ∀ i,reference i≤t)
    (β : ℝ) (hbound : ∀ i,
      manyProbability (fun _ => refreshProbability (reference i))
        (fun ω => HexFourArms P.center (r i) (R i) (pairDecode slot ω))≤β) :
    manyProbability (fun _ => refreshProbability t) (fun ω => FourArms P (pairDecode slot ω))≤β^N := by
  apply required_events_geometric N (fun i => touching slot (region P.center (r i) (R i)))
    (touching_annuli_pairwise N slot z P.center hz hpartner r R hgap)
    (fun i ω => HexFourArms P.center (r i) (R i) (pairDecode slot ω)) _
    (fun i => hex_local slot P.center (r i) (R i))
    (fun ω h i => circular_requires_hex orderInput P (r i) (R i) (hr i) (hrR i)
      (hinner i) (houter i) h) reference t ht href0 href β hbound

#print axioms touching_annuli_pairwise
#print axioms circular_probability_le_power

end ExceptionalTimes.CanonicalHexAnnuli
