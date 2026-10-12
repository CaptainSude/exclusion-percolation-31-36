import ExceptionalTimes.SourceMicroscopicSample

/-! Exact lattice translation of literal closed-cell polygon tests and
raw pair responses, retaining every boundary cell. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open PolygonSewing EnvironmentVariance ProbeProduct

theorem blackCells_shift (x : Site) (ω : Configuration) :
    globalBlackCells ω=(Homeomorph.addLeft (HexCells.center x)) ''
      globalBlackCells (fun v => ω (x+v)) := by
  ext p
  constructor
  · rintro ⟨v,hv,hp⟩
    refine ⟨p-HexCells.center x,⟨v-x,by simpa using hv,?_⟩,by simp⟩
    have hc := HexTiling.mem_cell_translate (p-HexCells.center x) x (v-x)
    apply hc.mp
    simpa [add_comm] using hp
  · rintro ⟨p,⟨v,hv,hp⟩,rfl⟩
    refine ⟨x+v,hv,?_⟩
    change HexCells.center x+p∈HexCells.cell (x+v)
    simpa only [add_comm] using (HexTiling.mem_cell_translate p x v).mpr hp

theorem crossing_shift (Q : PolygonQuad) (x : Site) (ω : Configuration) :
    (Q.shift (HexCells.center x)).Crossing ω↔Q.Crossing (fun v => ω (x+v)) := by
  let H := Homeomorph.addLeft (HexCells.center x)
  have hs : globalBlackCells ω∩H '' Q.carrier=H '' (globalBlackCells (fun v => ω (x+v))∩Q.carrier) := by
    rw [blackCells_shift x ω,Set.image_inter H.injective]
  constructor
  · rintro ⟨a,⟨p,hp,rfl⟩,b,⟨q,hq,rfl⟩,hj⟩
    change JoinedIn (globalBlackCells ω∩H '' Q.carrier) (H p) (H q) at hj
    rw [hs] at hj
    have ht := hj.map H.symm.continuous.continuousOn
    refine ⟨p,hp,q,hq,?_⟩
    simpa only [image_image,Function.comp_def,Homeomorph.symm_apply_apply,image_id'] using ht
  · rintro ⟨p,hp,q,hq,hj⟩
    refine ⟨H p,⟨p,hp,rfl⟩,H q,⟨q,hq,rfl⟩,?_⟩
    change JoinedIn (globalBlackCells ω∩H '' Q.carrier) (H p) (H q)
    rw [hs]
    exact hj.map H.continuous.continuousOn

theorem test_shift (Q : PolygonQuad) (x : Site) (ω : Configuration) :
    (Q.shift (HexCells.center x)).test ω=Q.test (fun v => ω (x+v)) := by
  unfold PolygonQuad.test
  rw [crossing_shift]

theorem support_shift (Q : PolygonQuad) (x v : Site) :
    x+v∈(Q.shift (HexCells.center x)).support↔v∈Q.support := by
  rw [PolygonQuad.mem_support,PolygonQuad.mem_support]
  constructor
  · rintro ⟨p,hpc,q,hq,hpq⟩
    have hpq' : HexCells.center x+q=p := hpq
    refine ⟨q,?_,hq⟩
    apply (HexTiling.mem_cell_translate q x v).mp
    rw [←hpq'] at hpc
    simpa only [add_comm] using hpc
  · rintro ⟨p,hpc,hp⟩
    refine ⟨HexCells.center x+p,?_,p,hp,rfl⟩
    simpa only [add_comm] using (HexTiling.mem_cell_translate p x v).mpr hpc

theorem putPair_shift (ω : Configuration) (x y z : Site) (u v : Bool) :
    (fun a => putPair ω (x+y) z u v (x+a))=
      putPair (fun a => ω (x+a)) y z u v := by
  funext a
  simp only [putPair,Function.update_apply,add_assoc,add_left_cancel_iff]

theorem pairHistory_shift (A : TwoTimeConfiguration) (x y z : Site)
    (u v : DimerBinaryResponse.State) :
    (fun t a => pairHistory A (x+y) z u v t (x+a))=
      pairHistory (fun t a => A t (x+a)) y z u v := by
  funext t
  cases t <;> exact putPair_shift _ x y z _ _

theorem raw_pair_jump_shift (Q : PolygonQuad) (x y z : Site) (ω : Configuration) (rule : Rule) :
    rawPairResponse rule.kernel (fun _ => ω) (x+y) z (Q.shift (HexCells.center x)).jump=
      rawPairResponse rule.kernel (fun _ a => ω (x+a)) y z Q.jump := by
  have hh (u v : DimerBinaryResponse.State) :
      (Q.shift (HexCells.center x)).jump (pairHistory (fun _ => ω) (x+y) z u v)=
        Q.jump (pairHistory (fun _ a => ω (x+a)) y z u v) := by
    unfold PolygonQuad.jump
    rw [test_shift,test_shift]
    have he := pairHistory_shift (fun _ => ω) x y z u v
    rw [←he]
  simp only [rawPairResponse,hh]

#print axioms crossing_shift
#print axioms raw_pair_jump_shift
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

