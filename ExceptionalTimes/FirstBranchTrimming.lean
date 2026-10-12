import ExceptionalTimes.PlaneJordanOrder
import ExceptionalTimes.WiredBranchTrimming

namespace ExceptionalTimes.WiredBranches

open PairSquareSewing TriangularPlane Set

structure FirstTrimmedBranches (P : Probe) (ω : Configuration) (D : Finset Site) (r R : ℕ)
    {v s w : Site} (B : Branches ω D r R v s w) extends TrimmedBranches P ω D r R B where
  firstExits : ∀ i,P.FirstExit (B.path i) (contact i)

theorem trim_branches_first (P : Probe) (hmesh : 2*P.mesh<P.innerRadius)
    {ω : Configuration} {D : Finset Site} {r R : ℕ} {v s w : Site}
    (B : Branches ω D r R v s w) (hv : v∈P.pocket)
    (hD : ∀ z∈D,z∈P.pocket)
    (hs : 2*P.outerRadius<P.radius s)
    (hend : ∀ i,P.outerRadius≤P.radius (B.endpoint i))
    (hregion : ∀ z∈P.region,z∉latticeBox r ∧ z∈latticeBox (R+1)) :
    Nonempty (FirstTrimmedBranches P ω D r R B) := by
  have hx : P.radius v≤P.innerRadius := by
    change P.radius v<P.innerRadius/2 at hv
    linarith [P.inner_pos]
  have htrim (i : Fin 4) := trim_first_circle_with_original_contact P hmesh
    (B.path i) (B.path_isPath i) hx (hend i)
  choose start hstart finish hfinish path hpath hsub hbounds contact hcontact hfirst using htrim
  have houtD : ∀ z∈P.region,z∉D := by
    intro z hz hzD
    exact (not_lt_of_ge hz.1) (hD z hzD)
  refine ⟨{
    start := start
    finish := finish
    path := path
    isPath := hpath
    isSubwalk := hsub
    starts := hstart
    finishes := hfinish
    colors := ?_
    disjoint := ?_
    contact := contact
    contacts := hcontact
    firstExits := hfirst }⟩
  · intro i z hz
    have hreg := hbounds i z hz
    exact ⟨hreg,B.path_color i z ((hsub i).support_subset hz) (houtD z hreg)
      (hregion z hreg).1 (hregion z hreg).2⟩
  · intro i j hij z hzi hzj
    have hreg := hbounds i z hzi
    rcases B.path_intersection i j hij z ((hsub i).support_subset hzi)
      ((hsub j).support_subset hzj) with rfl | rfl
    · exact (not_lt_of_ge hreg.1) hv
    · exact (not_lt_of_ge hreg.2) hs

theorem TrimmedBranches.fourArms_of_white_reversal {P : Probe} {ω : Configuration}
    {D : Finset Site} {r R : ℕ} {v s w : Site} {B : Branches ω D r R v s w}
    (T : TrimmedBranches P ω D r R B)
    (horder : P.CyclicOuter ![T.contact 0,T.contact 3,T.contact 2,T.contact 1]) :
    FourArms P ω := by
  classical
  let σ : Fin 4≃Fin 4 := Equiv.swap 1 3
  have hσcolor : ∀ i : Fin 4,decide ((σ i).val%2=0)=decide (i.val%2=0) := by
    intro i
    fin_cases i <;> norm_num [σ,Equiv.swap_apply_def]
  refine ⟨(fun i => T.start (σ i)),(fun i => T.finish (σ i)),
    (fun i => T.path (σ i)),(fun i => T.isPath (σ i)),
    (fun i => T.starts (σ i)),(fun i => T.finishes (σ i)),?_,?_,
    (fun i => T.contact (σ i)),(fun i => T.contacts (σ i)),?_⟩
  · intro i z hz
    simpa only [hσcolor] using T.colors (σ i) z hz
  · intro i j hij
    exact T.disjoint (σ i) (σ j) (fun h => hij (σ.injective h))
  · have heq : (fun i => T.contact (σ i))=![T.contact 0,T.contact 3,T.contact 2,T.contact 1] := by
      funext i
      fin_cases i <;> simp [σ,Equiv.swap_apply_def]
    rwa [heq]

theorem FirstTrimmedBranches.fourArms_of_plane
    (hJordan : PublishedPolygonCrossingOrder)
    {P : Probe} {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} {B : Branches ω D r R v s w}
    (T : FirstTrimmedBranches P ω D r R B)
    (hv : P.radius v<P.outerRadius)
    (hzero : P.outerRadius≤P.radius (0,0)) (hw : P.outerRadius≤P.radius w)
    (hs : P.outerRadius<P.radius s)
    (hc : (B.whiteFirst.append B.whiteSecond.reverse).IsCycle)
    (hzeroC : point (0,0)∉walkTrace (B.whiteFirst.append B.whiteSecond.reverse))
    (hwC : point w∉walkTrace (B.whiteFirst.append B.whiteSecond.reverse))
    (hsep : point w∉connectedComponentIn
      (walkTrace (B.whiteFirst.append B.whiteSecond.reverse))ᶜ (point (0,0))) :
    FourArms P ω := by
  have horder := hJordan P v (0,0) w s hv hzero hw hs B.blackIn B.blackOut
    B.whiteFirst B.whiteSecond B.blackIn_path B.blackOut_path
    B.whiteFirst_path B.whiteSecond_path hc B.black_intersection B.opposite_intersection
    hzeroC hwC hsep (T.contact 0) (T.contact 1) (T.contact 2) (T.contact 3)
    (T.firstExits 0) (T.firstExits 1) (T.firstExits 2) (T.firstExits 3)
  rcases horder with horder | horder
  · apply T.toTrimmedBranches.fourArms_of_cyclic
    have heq : ![T.contact 0,T.contact 1,T.contact 2,T.contact 3]=T.contact := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at horder
  · exact T.toTrimmedBranches.fourArms_of_white_reversal horder

#print axioms trim_branches_first
#print axioms FirstTrimmedBranches.fourArms_of_plane

end ExceptionalTimes.WiredBranches
