import ExceptionalTimes.QuadFamilyTransport

/-! Classical external input, with no polygon or percolation conclusions.

Allen Hatcher, Algebraic Topology, Theorem 2B.3, printed page 172:
https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf (PDF page 76).
The source explicitly allows a continuous injection from an open subset
of R^n to R^n and concludes that its image is open. The hypothesis below
is precisely that general statement, in finite-coordinate real space.
All consequences for closed carriers and their frontiers are proved here.
-/

open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace ExceptionalTimes.PairSquareSewing

def PublishedInvarianceOfDomain : Prop :=
  ∀ (n : ℕ) (U : Set (Fin n → ℝ)), IsOpen U →
    ∀ f : U → (Fin n → ℝ), Continuous f → Function.Injective f → IsOpen (range f)

theorem invarianceOfDomain_homeomorph (hsource : PublishedInvarianceOfDomain)
    {X : Type*} [TopologicalSpace X] (n : ℕ) (e : X ≃ₜ (Fin n → ℝ))
    (U : Set X) (hU : IsOpen U) (f : U → X)
    (hf : Continuous f) (hinj : Function.Injective f) : IsOpen (range f) := by
  let d := e.image U
  let g : (e '' U) → (Fin n → ℝ) := fun x => e (f (d.symm x))
  have hg : Continuous g := e.continuous.comp (hf.comp d.symm.continuous)
  have hgi : Function.Injective g := e.injective.comp (hinj.comp d.symm.injective)
  have ho := hsource n (e '' U) (e.isOpenMap U hU) g hg hgi
  have hr : e.symm '' range g=range f := by
    ext x
    constructor
    · rintro ⟨y,⟨p,rfl⟩,rfl⟩
      exact ⟨d.symm p,(e.symm_apply_apply _).symm⟩
    · rintro ⟨p,rfl⟩
      exact ⟨g (d p),⟨d p,rfl⟩,by simp [g]⟩
  rw [← hr]
  exact e.symm.isOpenMap _ ho

theorem invarianceOfDomain_plane (hsource : PublishedInvarianceOfDomain)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (f : U → (ℝ × ℝ))
    (hf : Continuous f) (hinj : Function.Injective f) : IsOpen (range f) :=
  invarianceOfDomain_homeomorph hsource 2
    (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm U hU f hf hinj

/-- An embedding of a planar set preserves which of its points are
ambient interior points. Both directions use only invariance of domain. -/
theorem planarEmbedding_interior_iff (hsource : PublishedInvarianceOfDomain)
    {S : Set (ℝ × ℝ)} {f : S → (ℝ × ℝ)} (hf : Topology.IsEmbedding f) (x : S) :
    f x ∈ interior (range f) ↔ (x.val : ℝ × ℝ) ∈ interior S := by
  let e := hf.toHomeomorph
  constructor
  · intro hx
    let g : interior (range f) → (ℝ × ℝ) :=
      fun y => (e.symm ⟨y.val,interior_subset y.property⟩).val
    have hg : Continuous g := continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
    have hgi : Function.Injective g := by
      intro y z hyz
      have he : e.symm ⟨y.val,interior_subset y.property⟩=
          e.symm ⟨z.val,interior_subset z.property⟩ := Subtype.ext hyz
      exact Subtype.ext (congrArg (fun u : range f => u.val) (e.symm.injective he))
    have hopen := invarianceOfDomain_plane hsource _ isOpen_interior g hg hgi
    have hsub : range g ⊆ S := by
      rintro y ⟨z,rfl⟩
      exact (e.symm ⟨z.val,interior_subset z.property⟩).property
    apply interior_maximal hsub hopen
    refine ⟨⟨f x,hx⟩,?_⟩
    change (hf.toHomeomorph.symm ⟨f x,_⟩).val=x.val
    rw [Topology.IsEmbedding.toHomeomorph_symm_apply]
  · intro hx
    let g : interior S → (ℝ × ℝ) := fun y => f ⟨y.val,interior_subset y.property⟩
    have hg : Continuous g := hf.continuous.comp (continuous_subtype_val.subtype_mk _)
    have hgi : Function.Injective g := by
      intro y z hyz
      exact Subtype.ext (congrArg (fun u : S => u.val) (hf.injective hyz))
    have hopen := invarianceOfDomain_plane hsource _ isOpen_interior g hg hgi
    have hsub : range g ⊆ range f := by rintro y ⟨z,rfl⟩; exact ⟨_,rfl⟩
    exact interior_maximal hsub hopen ⟨⟨x.val,hx⟩,rfl⟩

theorem planarEmbedding_interior_image (hsource : PublishedInvarianceOfDomain)
    {S : Set (ℝ × ℝ)} {f : S → (ℝ × ℝ)} (hf : Topology.IsEmbedding f) :
    interior (range f)=f '' (Subtype.val ⁻¹' interior S) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,rfl⟩ := interior_subset hy
    exact ⟨x,(planarEmbedding_interior_iff hsource hf x).mp hy,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    exact (planarEmbedding_interior_iff hsource hf x).mpr hx

theorem planarClosedEmbedding_regularClosed (hsource : PublishedInvarianceOfDomain)
    {S : Set (ℝ × ℝ)} (hS : closure (interior S)=S)
    {f : S → (ℝ × ℝ)} (hf : Topology.IsClosedEmbedding f) :
    closure (interior (range f))=range f := by
  have hd : closure (Subtype.val ⁻¹' interior S : Set S)=univ := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_val,inter_eq_right.mpr interior_subset,hS]
    exact Set.eq_univ_iff_forall.mpr (fun x => x.property)
  rw [planarEmbedding_interior_image hsource hf.isEmbedding,hf.closure_image_eq,hd,image_univ]

theorem planarClosedEmbedding_frontier (hsource : PublishedInvarianceOfDomain)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    {f : S → (ℝ × ℝ)} (hf : Topology.IsClosedEmbedding f) :
    frontier (range f)=f '' (Subtype.val ⁻¹' frontier S) := by
  rw [hf.isClosed_range.frontier_eq,hS.frontier_eq]
  ext y
  constructor
  · rintro ⟨⟨x,rfl⟩,hx⟩
    exact ⟨x,⟨x.property,fun h => hx ((planarEmbedding_interior_iff hsource hf.isEmbedding x).mpr h)⟩,rfl⟩
  · rintro ⟨x,⟨_hxS,hx⟩,rfl⟩
    exact ⟨⟨x,rfl⟩,fun h => hx ((planarEmbedding_interior_iff hsource hf.isEmbedding x).mp h)⟩

#print axioms planarClosedEmbedding_regularClosed
#print axioms planarClosedEmbedding_frontier

end ExceptionalTimes.PairSquareSewing
