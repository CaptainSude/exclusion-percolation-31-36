import ExceptionalTimes.CardinalTrackGeometry
import ExceptionalTimes.NolinCorridor

open Set
open scoped Classical

namespace ExceptionalTimes.PairSquareSewing

open Annulus NolinCorridor EnvironmentVariance FiniteHaar ProbeProduct

/-- The four explicit translated lattice symmetries placing the source
rectangle in the east, north, west and south tracks. -/
def cardinalMap (r : ℤ) (w : ℕ) (i : Fin 4) : triangularGraph →g triangularGraph where
  toFun z := ![(r-1+z.1,z.2-w),(z.2-w,r-1+z.1),
    (-r+1-z.1,(w:ℤ)-z.2),((w:ℤ)-z.2,-r+1-z.1)] i
  map_rel' := by
    intro u v huv
    change TriangularAdj u v at huv
    change TriangularAdj _ _
    fin_cases i <;> dsimp <;> simp only [TriangularAdj] at huv ⊢ <;> omega

theorem cardinalMap_injective (r : ℤ) (w : ℕ) (i : Fin 4) :
    Function.Injective (cardinalMap r w i) := by
  intro u v huv
  have hx := congrArg Prod.fst huv
  have hy := congrArg Prod.snd huv
  fin_cases i <;> simp [cardinalMap] at hx hy <;> apply Prod.ext <;> omega

/-- A one-layer trim removes Nolin's uncolored endpoints. The remaining
vertices, including both terminal rows of our track, have their original
colors. Translation, reflection and coordinate exchange are literal
lattice graph maps. -/
theorem nolinCrossing_to_cardinal (r : ℤ) (w M : ℕ) (hM : 3 ≤ M)
    (i : Fin 4) (color : Bool) (ω : Configuration)
    (h : HorizontalCrossing
      (fun z => if color then ω (cardinalMap r w i z) else !(ω (cardinalMap r w i z))) M (2*w)) :
    (cardinalTrack r (r+M-2) w i).ColorCrossing color ω := by
  obtain ⟨u,v,hu,huy0,huyN,hv,hvy0,hvyN,p,hp,hcol⟩ := h
  have hstep : ∀ {a b : Site}, TriangularAdj a b → b.1 ≤ a.1+1 := by
    intro a b hab
    simp only [TriangularAdj] at hab
    omega
  obtain ⟨x,hx,y,hy,q,_hq,hsub,hbounds,_hi,_ho⟩ :=
    trim_path_integer_levels (fun z : Site => z.1) hstep 1 ((M:ℤ)-1) (by omega) p hp
      (by omega) (by omega)
  have hqcol (z : Site) (hz : z ∈ q.support) :
      1 ≤ z.1 ∧ z.1 ≤ (M:ℤ)-1 ∧ 0 < z.2 ∧ z.2 < 2*w ∧
        ω (cardinalMap r w i z)=color := by
    have hzuv := hbounds z hz
    have hzu : z ≠ u := by intro he; subst z; omega
    have hzv : z ≠ v := by intro he; subst z; omega
    have hcolor := hcol z (hsub.support_subset hz) hzu hzv
    refine ⟨hzuv.1,hzuv.2,hcolor.2.2.1,hcolor.2.2.2.1,?_⟩
    cases color <;> simpa using hcolor.2.2.2.2
  have hdom (z : Site) (hz : z ∈ q.support) :
      cardinalMap r w i z ∈ (cardinalTrack r (r+M-2) w i).domain := by
    have hz' := hqcol z hz
    fin_cases i <;>
      simp [cardinalMap,cardinalTrack,horizontalTrack,verticalTrack,axialRectangleSites] <;> omega
  have hmapped : ∀ z ∈ (q.map (cardinalMap r w i)).support,
      z ∈ (cardinalTrack r (r+M-2) w i).domain ∧ ω z=color := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    exact ⟨hdom t ht,(hqcol t ht).2.2.2.2⟩
  have hdx := hdom x q.start_mem_support
  have hdy := hdom y q.end_mem_support
  fin_cases i
  · refine ⟨_,Finset.mem_filter.mpr ⟨hdx,?_⟩,_,Finset.mem_filter.mpr ⟨hdy,?_⟩,
      q.map (cardinalMap r w 0),hmapped⟩
    · simp [cardinalMap,hx]
    · simp [cardinalMap,hy]; omega
  · refine ⟨_,Finset.mem_filter.mpr ⟨hdx,?_⟩,_,Finset.mem_filter.mpr ⟨hdy,?_⟩,
      q.map (cardinalMap r w 1),hmapped⟩
    · simp [cardinalMap,hx]
    · simp [cardinalMap,hy]; omega
  · refine ⟨_,Finset.mem_filter.mpr ⟨hdy,?_⟩,_,Finset.mem_filter.mpr ⟨hdx,?_⟩,
      (q.map (cardinalMap r w 2)).reverse,?_⟩
    · simp [cardinalMap,hy]; omega
    · simp [cardinalMap,hx]
    · intro z hz
      apply hmapped z
      simpa [SimpleGraph.Walk.support_map,cardinalMap] using hz
  · refine ⟨_,Finset.mem_filter.mpr ⟨hdy,?_⟩,_,Finset.mem_filter.mpr ⟨hdx,?_⟩,
      (q.map (cardinalMap r w 3)).reverse,?_⟩
    · simp [cardinalMap,hy]; omega
    · simp [cardinalMap,hx]
    · intro z hz
      apply hmapped z
      simpa [SimpleGraph.Walk.support_map,cardinalMap] using hz

theorem average_favorable_restrict {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (select : A ↪ B) (color : Bool)
    (f : (A → Bool) → ℝ) :
    average (fun ω : B → Bool => f (fun a => if color then ω (select a) else !(ω (select a)))) =
      average f := by
  cases color
  · simp only [Bool.false_eq_true,ite_false]
    rw [FiniteSiteLaw.average_restrict select (fun ω => f (fun a => !(ω a)))]
    have hflip : Function.Involutive (fun ω : A → Bool => fun a => !(ω a)) := by
      intro ω
      funext a
      exact Bool.not_not _
    exact average_equiv hflip.toPerm f
  · simpa only [ite_true] using FiniteSiteLaw.average_restrict select f

/-- Critical RSW is applied to the original endpoint-free rectangle,
then transferred to the concrete colored cardinal track. All four
orientations, either color and arbitrary finite ambient site sets are
covered by exact fair-site marginalization. -/
theorem cardinal_track_lower_of_RSW (hsource : PublishedCriticalRSW)
    (k : ℕ) (hk : 2 ≤ k) : ∃ δ : ℝ, 0 < δ ∧
      ∀ (w : ℕ), 1 ≤ w → ∀ (r : ℤ) (Λ : Finset Site) (i : Fin 4),
        (∀ z ∈ rectangle (k*(2*w)) (2*w), cardinalMap r w i z ∈ Λ) →
        ∀ color : Bool, δ ≤ probability (fairSites ↥Λ)
          (fun ω => (cardinalTrack r (r+k*(2*w)-2) w i).ColorCrossing color (complete ω)) := by
  obtain ⟨δ,hδ,hbound⟩ := hsource k hk
  refine ⟨δ,hδ,?_⟩
  intro w hw r Λ i hΛ color
  let D := rectangle (k*(2*w)) (2*w)
  let select : D ↪ Λ :=
    ⟨fun z => ⟨cardinalMap r w i z, hΛ z z.property⟩,by
      intro a b hab
      apply Subtype.ext
      exact cardinalMap_injective r w i (congrArg Subtype.val hab)⟩
  let restrict (ω : Λ → Bool) : D → Bool :=
    fun z => if color then ω (select z) else !(ω (select z))
  let E (ω : D → Bool) := HorizontalCrossing (completeColors D ω) (k*(2*w)) (2*w)
  have hprob : probability (fairSites ↥Λ) (fun ω => E (restrict ω)) =
      probability (fairSites ↥D) E := by
    simp only [probability,FiniteSiteLaw.fairSites_expect_eq_average]
    exact average_favorable_restrict select color (fun ω => indicator (E ω))
  have hlow : δ ≤ probability (fairSites ↥Λ) (fun ω => E (restrict ω)) := by
    rw [hprob]
    exact hbound (2*w) (by omega) D (fun _ h => h)
  apply hlow.trans (CanonicalRadialLaw.probability_mono _ ?_)
  intro ω hω
  apply nolinCrossing_to_cardinal r w (k*(2*w)) (by nlinarith) i color (complete ω)
  apply (horizontalCrossing_congr (ω := completeColors D (restrict ω))
    (η := fun z => if color then complete ω (cardinalMap r w i z)
      else !(complete ω (cardinalMap r w i z))) ?_).mp hω
  intro z hz
  have hzΛ := hΛ z hz
  simp [completeColors,complete,restrict,select,hz,hzΛ,D]
  rfl

#print axioms nolinCrossing_to_cardinal
#print axioms cardinal_track_lower_of_RSW

end ExceptionalTimes.PairSquareSewing
