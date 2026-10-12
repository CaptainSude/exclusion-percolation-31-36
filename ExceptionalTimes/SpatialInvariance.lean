import ExceptionalTimes.Model

/-!
Spatial invariance of the actual exceptional-time set. This is the geometric
invariance needed by a spatial zero-one argument. No ergodicity or measurability
of a random Hausdorff-dimension event is asserted here.
-/

namespace ExceptionalTimes

set_option autoImplicit false
open scoped ENNReal

def translateConfiguration (z : Site) (ω : Configuration) : Configuration :=
  fun v => ω (v - z)

theorem triangularAdj_translate (z u v : Site) :
    TriangularAdj (u + z) (v + z) ↔ TriangularAdj u v := by
  simp only [TriangularAdj, Prod.fst_add, Prod.snd_add]
  omega

def translatedBlackGraphIso (z : Site) (ω : Configuration) :
    blackGraph ω ≃g blackGraph (translateConfiguration z ω) where
  toEquiv := Equiv.addRight z
  map_rel_iff' := by
    intro u v
    change (TriangularAdj (u + z) (v + z) ∧
      ω (u + z - z) = true ∧ ω (v + z - z) = true) ↔
      (TriangularAdj u v ∧ ω u = true ∧ ω v = true)
    simp only [triangularAdj_translate, add_sub_cancel_right]

theorem blackCluster_translate (z : Site) (ω : Configuration) (v : Site) :
    BlackCluster (translateConfiguration z ω) (v + z) =
      (fun w => w + z) '' BlackCluster ω v := by
  ext w
  constructor
  · intro hw
    refine ⟨w - z, ?_, sub_add_cancel w z⟩
    constructor
    · simpa [BlackCluster, translateConfiguration] using hw.1
    · have h : (blackGraph (translateConfiguration z ω)).Reachable
          ((translatedBlackGraphIso z ω) v) ((translatedBlackGraphIso z ω) (w - z)) := by
        simpa [translatedBlackGraphIso] using hw.2
      exact SimpleGraph.Iso.reachable_iff.mp h
  · rintro ⟨u, hu, rfl⟩
    constructor
    · simpa [translateConfiguration] using hu.1
    · exact hu.2.map (translatedBlackGraphIso z ω).toHom

theorem hasInfiniteBlackCluster_translate (z : Site) (ω : Configuration) :
    HasInfiniteBlackCluster (translateConfiguration z ω) ↔ HasInfiniteBlackCluster ω := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v - z, ?_⟩
    have h := blackCluster_translate z ω (v - z)
    rw [sub_add_cancel] at h
    rw [h] at hv
    exact hv.of_image _
  · rintro ⟨v, hv⟩
    refine ⟨v + z, ?_⟩
    rw [blackCluster_translate]
    exact hv.image (Equiv.addRight z).injective.injOn

def translateTrajectory (z : Site) (X : Trajectory) : Trajectory :=
  fun t => translateConfiguration z (X t)

theorem exceptionalTimes_translate (z : Site) (X : Trajectory) :
    exceptionalTimes (translateTrajectory z X) = exceptionalTimes X := by
  ext t
  simp only [mem_exceptionalTimes, translateTrajectory, hasInfiniteBlackCluster_translate]

theorem exceptionalDimension_translate (z : Site) (X : Trajectory) (d : ℝ≥0∞) :
    ExceptionalDimension (translateTrajectory z X) d ↔ ExceptionalDimension X d := by
  simp only [ExceptionalDimension, exceptionalTimes_translate]

end ExceptionalTimes

#print axioms ExceptionalTimes.blackCluster_translate
#print axioms ExceptionalTimes.hasInfiniteBlackCluster_translate
#print axioms ExceptionalTimes.exceptionalTimes_translate
