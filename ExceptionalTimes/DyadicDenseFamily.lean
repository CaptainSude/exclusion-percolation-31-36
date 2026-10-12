import ExceptionalTimes.DyadicFiniteFamily

/-! The published Euclidean dyadic family supplies a countable dense
axial family in every bounded open physical domain. Any finite selection
has the already proved exact crossing dictionary and forest geometry. -/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

universe u

theorem published_dense_axial_family (hsource : PublishedDyadicQuadDensity)
    (D : Set ℂ) (hopen : IsOpen D) (hbounded : Bornology.IsBounded D) :
    ∃ family : Set (ParameterQuad ℂ), family.Countable ∧ BoundaryDense D family ∧
      (∀ Q ∈ family, range Q.map ⊆ D) ∧
      ∀ (F : Type u) (selected : F → ParameterQuad ℂ),
        (∀ i, selected i ∈ family) →
          ∃ T : DyadicQuadFamily F, ∀ i, (T.quad i).transport euclideanAxialShear=selected i := by
  let U := euclideanAxialShear.symm '' D
  have hUopen : IsOpen U := euclideanAxialShear.symm.isOpenMap D hopen
  have hUbounded : Bornology.IsBounded U :=
    (hbounded.isCompact_closure.image euclideanAxialShear.symm.continuous).isBounded.subset
      (image_mono subset_closure)
  obtain ⟨family,hcount,hdense,hgrid⟩ :=
    published_axial_quad_family hsource U hUopen hUbounded
  have hUD : euclideanAxialShear '' U=D := by
    simp only [U,image_image,Homeomorph.apply_symm_apply,image_id']
  rw [hUD] at hdense
  refine ⟨family,hcount,hdense,?_,?_⟩
  · intro Q hQ
    obtain ⟨R,_,hR,rfl⟩ := hgrid Q hQ
    rintro p ⟨x,rfl⟩
    change euclideanAxialShear (R.map x) ∈ D
    rw [← hUD]
    exact ⟨R.map x,hR ⟨x,rfl⟩,rfl⟩
  · intro F selected hselected
    choose R hR hRU heq using fun i => hgrid (selected i) (hselected i)
    refine ⟨⟨R,fun i => Classical.choice (hR i)⟩,?_⟩
    exact fun i => (heq i).symm

theorem selected_crossing_dictionary {F : Type*} [Fintype F]
    (hsource : PublishedInvarianceOfDomain) (T : DyadicQuadFamily F)
    (selected : F → ParameterQuad ℂ)
    (hselected : ∀ i, (T.quad i).transport euclideanAxialShear=selected i)
    (n : ℕ) (hn : T.maxLevel≤n) (i : F) (ω : Configuration) :
    (selected i).LiteralCrossing (globalPhysicalBlackCells (DyadicQuadFamily.probe n) ω) ↔
      ((T.grid i).meshPolygon hsource n).Crossing ω := by
  rw [← hselected i]
  exact T.crossing_dictionary hsource n hn i ω

#print axioms published_dense_axial_family
#print axioms selected_crossing_dictionary

end ExceptionalTimes.PairSquareSewing
