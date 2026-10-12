import ExceptionalTimes.ClockSpatial

/-! Translation-equivariant indexing of each non-diagonal unordered edge
exactly once, by its anchor and positive lexicographic displacement. -/

open scoped Classical

namespace ExceptionalTimes.CanonicalEdgeIndex

def Positive (z : Site) : Prop := 0 < z.1 ∨ z.1 = 0 ∧ 0 < z.2

abbrev Displacement := {z : Site // Positive z}
abbrev Index := Site × Displacement
abbrev Edge := {e : Sym2 Site // ¬ e.IsDiag}

theorem positive_ne_zero {z : Site} (hz : Positive z) : z ≠ 0 := by
  intro h
  subst z
  simp [Positive] at hz

theorem positive_not_neg {z : Site} (hz : Positive z) : ¬ Positive (-z) := by
  rcases z with ⟨x,y⟩
  simp only [Positive,Prod.fst_neg,Prod.snd_neg] at *
  omega

theorem positive_or_neg {z : Site} (hz : z ≠ 0) : Positive z ∨ Positive (-z) := by
  rcases z with ⟨x,y⟩
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! h
    exact hz (Prod.ext h.1 h.2)
  simp only [Positive,Prod.fst_neg,Prod.snd_neg]
  omega

def pair (a : Index) : Sym2 Site := s(a.1,a.1+a.2.val)

theorem pair_not_diag (a : Index) : ¬ (pair a).IsDiag := by
  intro h
  have he := Sym2.mk_isDiag_iff.mp h
  have hz : a.2.val = 0 := by
    have H := congrArg (fun v : Site => v-a.1) he
    simpa using H.symm
  exact positive_ne_zero a.2.property hz

theorem pair_injective : Function.Injective pair := by
  rintro ⟨x,z⟩ ⟨y,w⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hxy,hzw⟩ | ⟨hx,hy⟩
  · apply Prod.ext hxy
    apply Subtype.ext
    rw [hxy] at hzw
    exact add_left_cancel hzw
  · have hz : z.val = -w.val := by
      have hsum : w.val+z.val = 0 := by
        have H := congrArg (fun v : Site => v-y) (hx ▸ hy)
        simpa [add_assoc] using H
      have H := congrArg (fun v : Site => v-w.val) hsum
      simpa [add_comm,add_left_comm,add_assoc] using H
    exact (positive_not_neg w.property (hz ▸ z.property)).elim

theorem pair_surjective (e : Sym2 Site) (he : ¬ e.IsDiag) : ∃ a : Index, pair a = e := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : u ≠ v := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    have hvu : v-u ≠ 0 := sub_ne_zero.mpr huv.symm
    rcases positive_or_neg hvu with hpos | hneg
    · exact ⟨(u,⟨v-u,hpos⟩),by simp [pair]⟩
    · have hpos : Positive (u-v) := by simpa only [neg_sub] using hneg
      exact ⟨(v,⟨u-v,hpos⟩),by simp [pair,Sym2.eq_swap]⟩

def toEdge (a : Index) : Edge := ⟨pair a,pair_not_diag a⟩

theorem toEdge_bijective : Function.Bijective toEdge := by
  constructor
  · intro a b h
    exact pair_injective (congrArg Subtype.val h)
  · intro e
    obtain ⟨a,ha⟩ := pair_surjective e.val e.property
    exact ⟨a,Subtype.ext ha⟩

noncomputable def edgeEquiv : Index ≃ Edge := Equiv.ofBijective toEdge toEdge_bijective

def translate (z : Site) (a : Index) : Index := (a.1+z,a.2)

theorem pair_translate (z : Site) (a : Index) :
    pair (translate z a) = (pair a).map (fun x => x+z) := by
  simp only [pair,translate,Sym2.map_mk]
  congr 1
  abel

theorem rate_pair (k : RateKernel) (a : Index) : k.unorderedPairRate (pair a) = k.rate a.2.val := by
  simp [pair,RateKernel.unorderedPairRate_mk,RateKernel.pairRate]

#print axioms toEdge_bijective
#print axioms pair_translate

end ExceptionalTimes.CanonicalEdgeIndex
