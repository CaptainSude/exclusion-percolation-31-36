import ExceptionalTimes.RadialMiddle
import ExceptionalTimes.MesoscopicCells
import ExceptionalTimes.MixedAnnularCollar

/-! A concrete active/exterior split of a finite matching. Active labels
are exactly the dimers meeting the middle annulus. The partition and its
bulk spatial margins are constructed, rather than assumed. -/

open scoped Classical

namespace ExceptionalTimes.ActiveMiddlePartition

noncomputable section

open FiniteMatchingClosure HoleFilling MesoscopicCells

variable {B : Type*}

def Active (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) (b : B) : Prop :=
  slot (b,0) ∈ closure (PeriodicMatching.partner z) S

abbrev ActiveLabels (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :=
  {b : B // Active slot z S b}

abbrev ExteriorLabels (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :=
  {b : B // ¬ Active slot z S b}

def splitEquiv (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    ActiveLabels slot z S ⊕ ExteriorLabels slot z S ≃ B :=
  Equiv.sumCompl (Active slot z S)

def splitSlot (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    ((ActiveLabels slot z S ⊕ ExteriorLabels slot z S) × Fin 2) ↪ Site :=
  ((splitEquiv slot z S).prodCongr (Equiv.refl (Fin 2))).toEmbedding.trans slot

theorem splitSlot_inl (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site)
    (a : ActiveLabels slot z S) (b : Fin 2) : splitSlot slot z S (.inl a,b) = slot (a.val,b) := rfl

theorem active_endpoint_mem (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (S : Finset Site) (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (a : ActiveLabels slot z S) (b : Fin 2) :
    splitSlot slot z S (.inl a,b) ∈ closure (PeriodicMatching.partner z) S := by
  fin_cases b
  · exact a.property
  · change slot (a.val,1) ∈ _
    rw [hp]
    exact closure_invariant _ (PeriodicMatching.partner_involutive z hz0) S a.property

theorem active_covers (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (S : Finset Site) (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (hcover : ∀ v ∈ S, ∃ b, slot b = v) :
    ∀ v ∈ S, ∃ a b, splitSlot slot z S (.inl a,b) = v := by
  intro v hv
  obtain ⟨⟨b,k⟩,rfl⟩ := hcover v hv
  have hb : Active slot z S b := by
    fin_cases k
    · exact subset_closure _ S hv
    · have h := closure_invariant _ (PeriodicMatching.partner_involutive z hz0) S
        (subset_closure _ S hv)
      change PeriodicMatching.partner z (slot (b,1)) ∈ _ at h
      rw [hp,PeriodicMatching.partner_involutive z hz0] at h
      exact h
  exact ⟨⟨b,hb⟩,k,rfl⟩

theorem activeCovers_split (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    (S : Finset Site) (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (hcover : ∀ v ∈ S, ∃ b, slot b = v) :
    MixedAnnularCollar.ActiveCovers (splitSlot slot z S) S :=
  active_covers slot z hz0 S hp hcover

/-- The finite matching realization covering the full observed box is
constructed first, and its active middle/exterior split then covers the
middle event with the exact support convention used by the collar law. -/
theorem exists_middle_partition (z : Site) (hz0 : z ≠ (0,0)) (r R : ℕ) :
    ∃ k : ℕ, ∃ slot : Fin k × Fin 2 ↪ Site,
      (∀ v, v ∈ closure (PeriodicMatching.partner z) (latticeBox (R+1)) ↔ ∃ b, slot b = v) ∧
      (∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) ∧
      MixedAnnularCollar.ActiveCovers
        (splitSlot slot z (annularSites (2*r) (R/2))) (annularSites (2*r) (R/2)) := by
  obtain ⟨k,slot,hcover,hp⟩ := periodic_closure_enumeration z hz0 (latticeBox (R+1))
  refine ⟨k,slot,hcover,hp,activeCovers_split slot z hz0 _ hp ?_⟩
  intro v hv
  apply (hcover v).mp
  apply FiniteMatchingClosure.subset_closure
  exact latticeBox_mono (by omega) (Finset.mem_sdiff.mp hv).1

theorem splitSlot_partner (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (b : ActiveLabels slot z S ⊕ ExteriorLabels slot z S) :
    splitSlot slot z S (b,1) = PeriodicMatching.partner z (splitSlot slot z S (b,0)) :=
  hp (splitEquiv slot z S b)

/-- Every selected endpoint lies in the explicitly buffered middle
annulus; no exterior label has been silently retained as active. -/
theorem active_annular_margin (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d s t : ℕ} (hz : z ∈ latticeBox d) (hds : d ≤ s)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (a : ActiveLabels slot z (annularSites s t)) (b : Fin 2) :
    splitSlot slot z (annularSites s t) (.inl a,b) ∈ annularSites (s-d) (t+d) :=
  matchingClosure_annularSites_subset z hz0 hz hds (active_endpoint_mem slot z hz0 _ hp a b)

theorem active_middle_margin (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d r R : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ 2*r)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (a : ActiveLabels slot z (annularSites (2*r) (R/2))) (b : Fin 2) :
    splitSlot slot z (annularSites (2*r) (R/2)) (.inl a,b) ∈
      annularSites (2*r-d) (R/2+d) :=
  active_annular_margin slot z hz0 hz hdr hp a b

def activeEmbedding (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site) :
    ActiveLabels slot z S × Fin 2 ↪ Site :=
  ⟨fun b => slot (b.1.val,b.2),by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have he := Prod.mk.inj (slot.injective h)
    exact Prod.ext (Subtype.ext he.1) he.2⟩

theorem activeEmbedding_partner (slot : B × Fin 2 ↪ Site) (z : Site) (S : Finset Site)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (a : ActiveLabels slot z S) :
    activeEmbedding slot z S (a,1) = PeriodicMatching.partner z (activeEmbedding slot z S (a,0)) :=
  hp a.val

theorem active_cell_margin [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d r R : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ 2*r)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) (m : ℕ) (c : Site) :
    dimerCell m (activeEmbedding slot z (annularSites (2*r) (R/2))) c ⊆
      annularSites (2*r-d) (R/2+d) := by
  intro v hv
  obtain ⟨⟨a,b⟩,_,rfl⟩ := Finset.mem_image.mp hv
  exact active_middle_margin slot z hz0 hz hdr hp a b

theorem active_anchor_margin [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d r R : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ 2*r)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) (m : ℕ) (c : Site)
    (hc : c ∈ occupied m (activeEmbedding slot z (annularSites (2*r) (R/2)))) :
    anchor m (activeEmbedding slot z (annularSites (2*r) (R/2))) c ∈
      annularSites (2*r-d) (R/2+d) :=
  active_cell_margin slot z hz0 hz hdr hp m c (anchor_mem _ _ _ hc)

theorem active_anchor_radius [Fintype B]
    (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d r R : ℕ} (hz : z ∈ latticeBox d) (hdr : d ≤ r)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0))) (m : ℕ) (c : Site)
    (hc : c ∈ occupied m (activeEmbedding slot z (annularSites (2*r) (R/2)))) :
    r ≤ anchorRadius m (activeEmbedding slot z (annularSites (2*r) (R/2))) c := by
  have hn := (Finset.mem_sdiff.mp (active_anchor_margin slot z hz0 hz (by omega) hp m c hc)).2
  by_contra! hr
  apply hn
  apply mem_latticeBox_of_radius_le
  change anchorRadius _ _ _ ≤ _
  omega

theorem radius_le_of_mem_box {v : Site} {R : ℕ} (hv : v ∈ latticeBox R) :
    latticeRadius v ≤ R := by
  simp only [latticeBox,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc] at hv
  unfold latticeRadius
  apply max_le
  all_goals omega

/-- At every active site the translated box with one quarter of its
radial distance lies between the original hole and outer boundary. -/
theorem translated_probe_bulk {r R d : ℕ} (hr : 0 < r) (hR : 16*r ≤ R)
    (hdr : 2*d ≤ r) {x v : Site}
    (hx : x ∈ annularSites (2*r-d) (R/2+d))
    (hv : v-x ∈ latticeBox (latticeRadius x/4)) :
    v ∈ latticeBox R ∧ v ∉ latticeBox r := by
  obtain ⟨hxR,hxr⟩ := Finset.mem_sdiff.mp hx
  have hxrad := radius_le_of_mem_box hxR
  have hrad : 2*r-d < latticeRadius x := by
    by_contra! h
    exact hxr (mem_latticeBox_of_radius_le h)
  have hout : latticeRadius x + latticeRadius x/4 ≤ R := by omega
  have hin : r+latticeRadius x/4 < latticeRadius x := by omega
  constructor
  · have h := add_mem_box (mem_latticeBox_of_radius_le (le_refl (latticeRadius x))) hv
    have he : x+(v-x) = v := by abel
    rw [he] at h
    exact latticeBox_mono hout h
  · intro hvr
    have h := sub_mem_box hvr hv
    have he : v-(v-x) = x := by abel
    rw [he] at h
    exact (not_le_of_gt hin) (radius_le_of_mem_box h)

/-- Wide-collar specialization: any middle support inside the standard
bulk band has the same quarter-radius local-probe margin. -/
theorem active_wide_probe_bulk (slot : B × Fin 2 ↪ Site) (z : Site) (hz0 : z ≠ (0,0))
    {d r R s t : ℕ} (hr : 0 < r) (hR : 16*r ≤ R)
    (hz : z ∈ latticeBox d) (hdr : 2*d ≤ r) (hrs : 2*r ≤ s) (htR : t ≤ R/2)
    (hp : ∀ b, slot (b,1) = PeriodicMatching.partner z (slot (b,0)))
    (a : ActiveLabels slot z (annularSites s t)) (b : Fin 2) (v : Site)
    (hv : v - splitSlot slot z (annularSites s t) (.inl a,b) ∈
      latticeBox (latticeRadius (splitSlot slot z (annularSites s t) (.inl a,b))/4)) :
    v ∈ latticeBox R ∧ v ∉ latticeBox r := by
  apply translated_probe_bulk hr hR hdr _ hv
  exact annularSites_mono (Nat.sub_le_sub_right hrs d) (Nat.add_le_add_right htR d)
    (active_annular_margin slot z hz0 hz (by omega) hp a b)

#print axioms active_covers
#print axioms exists_middle_partition
#print axioms active_middle_margin
#print axioms active_anchor_radius
#print axioms translated_probe_bulk
#print axioms active_wide_probe_bulk

end

end ExceptionalTimes.ActiveMiddlePartition
