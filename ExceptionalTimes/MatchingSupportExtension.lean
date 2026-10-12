import ExceptionalTimes.CanonicalExtensionLaw
import ExceptionalTimes.ActivePartitionLaw

/-! An arbitrary finite matching observation can be enlarged by disjoint
whole dimers, keeping its original orientations and its two-time local law. -/

open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ExceptionalTimes.MatchingSupportExtension

noncomputable section

open FiniteMatchingClosure ActivePartitionLaw DimerLaw ManyDimerLaw CanonicalRadialLaw

variable {B C : Type*} [Fintype B] [Fintype C]

local instance : DecidableEq (B⊕C) := fun a b => Classical.propDecidable (a=b)

noncomputable def sites (slot : B×Fin 2 ↪ Site) : Finset Site := Finset.univ.image slot

theorem mem_sites (slot : B×Fin 2 ↪ Site) (v : Site) :
    v∈sites slot ↔ ∃ b,slot b=v := by simp [sites]

theorem sites_invariant (slot : B×Fin 2 ↪ Site) (p : Site→Site)
    (hp : Function.Involutive p) (hpair : ∀ b,slot (b,1)=p (slot (b,0))) :
    ∀ v∈sites slot,p v∈sites slot := by
  intro v hv
  obtain ⟨⟨b,i⟩,rfl⟩ := (mem_sites slot v).mp hv
  fin_cases i
  · exact (mem_sites slot _).mpr ⟨(b,1),hpair b⟩
  · change p (slot (b,1))∈sites slot
    rw [hpair,hp]
    exact (mem_sites slot _).mpr ⟨(b,0),rfl⟩

def sumSlot (slot : B×Fin 2 ↪ Site) (extra : C×Fin 2 ↪ Site)
    (hdis : ∀ a b,slot a≠extra b) : (B⊕C)×Fin 2 ↪ Site where
  toFun b := Sum.elim (fun a => slot (a,b.2)) (fun c => extra (c,b.2)) b.1
  inj' := by
    rintro ⟨a,i⟩ ⟨b,j⟩ he
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have h := slot.injective he
        cases h
        rfl
      | inr b => exact (hdis (a,i) (b,j) he).elim
    | inr a =>
      cases b with
      | inl b => exact (hdis (b,j) (a,i) he.symm).elim
      | inr b =>
        have h := extra.injective he
        cases h
        rfl

theorem exists_support_extension (slot : B×Fin 2 ↪ Site) (p : Site→Site)
    (hp : Function.Involutive p) (hfixed : ∀ v,p v≠v)
    (hpair : ∀ b,slot (b,1)=p (slot (b,0))) (D : Finset Site) :
    ∃ k : ℕ,∃ ext : (B⊕Fin k)×Fin 2 ↪ Site,
      (∀ b i,ext (.inl b,i)=slot (b,i)) ∧
      (∀ b,ext (b,1)=p (ext (b,0))) ∧
      (∀ v∈D,∃ b,ext b=v) := by
  let A := D\sites slot
  have hclosed := sites_invariant slot p hp hpair
  have hout : ∀ v∈closure p A,v∉sites slot := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_sdiff.mp hv).2
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      intro hn
      have hh := hclosed (p w) hn
      rw [hp] at hh
      exact (Finset.mem_sdiff.mp hw).2 hh
  obtain ⟨k,extra,hcover,hepair⟩ := exists_closure_enumeration p hp hfixed A
  have hdis : ∀ a b,slot a≠extra b := by
    intro a b he
    have hx := hout (extra b) ((hcover _).mpr ⟨b,rfl⟩)
    exact hx ((mem_sites slot _).mpr ⟨a,he⟩)
  let ext := sumSlot slot extra hdis
  refine ⟨k,ext,(fun _ _ => rfl),?_,?_⟩
  · intro b
    cases b with
    | inl b => exact hpair b
    | inr b => exact hepair b
  · intro v hv
    by_cases ho : v∈sites slot
    · obtain ⟨⟨b,i⟩,hb⟩ := (mem_sites slot v).mp ho
      exact ⟨(.inl b,i),hb⟩
    · have ha : v∈A := Finset.mem_sdiff.mpr ⟨hv,ho⟩
      obtain ⟨⟨b,i⟩,hb⟩ := (hcover v).mp (subset_closure p A ha)
      exact ⟨(.inr b,i),hb⟩

omit [Fintype C] in
theorem extended_decoder_agrees (slot : B×Fin 2 ↪ Site)
    (ext : (B⊕C)×Fin 2 ↪ Site) (hext : ∀ b i,ext (.inl b,i)=slot (b,i))
    (ω : B⊕C → Color) :
    Set.EqOn (pairDecode ext ω) (pairDecode slot (fun b => ω (.inl b))) (sites slot) := by
  intro v hv
  obtain ⟨⟨b,i⟩,rfl⟩ := (mem_sites slot v).mp hv
  unfold pairDecode
  conv_lhs => rw [← hext b i]
  rw [ext.injective.extend_apply,slot.injective.extend_apply]

/-- The larger observation has exactly the old probability for every
event supported on the original observed sites, at the same actual time. -/
theorem extended_probability (slot : B×Fin 2 ↪ Site)
    (ext : (B⊕C)×Fin 2 ↪ Site) (hext : ∀ b i,ext (.inl b,i)=slot (b,i))
    (E : Configuration→Prop)
    (hlocal : ∀ ω η,Set.EqOn ω η (sites slot) → (E ω ↔ E η))
    (t : ℝ) (ht : 0≤t) :
    manyProbability (fun _ => refreshProbability t) (fun ω => E (pairDecode ext ω))=
      manyProbability (fun _ => refreshProbability t) (fun ω => E (pairDecode slot ω)) := by
  have hpoint : ∀ ω : B⊕C → Color,
      E (pairDecode ext ω) ↔ E (pairDecode slot (fun b => ω (.inl b))) := by
    intro ω
    exact hlocal _ _ (extended_decoder_agrees slot ext hext ω)
  calc
    _ = manyProbability (fun _ => refreshProbability t)
        (fun ω => E (pairDecode slot (fun b => ω (.inl b)))) :=
      many_congr _ hpoint
    _ = _ := by
      have hh := CanonicalExtensionLaw.manyProbability_inl (A := B) (B := C)
        (fun _ => refreshProbability t)
        (fun _ => refreshProbability_nonneg ht) (fun _ => refreshProbability_le_one t)
        (fun ω => E (pairDecode slot ω))
      exact hh

#print axioms exists_support_extension
#print axioms extended_probability

end
end ExceptionalTimes.MatchingSupportExtension
