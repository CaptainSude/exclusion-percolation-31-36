import ExceptionalTimes.WiredBranches
import ExceptionalTimes.CirclePathTrimming

/-! All radial path extraction and circular trimming, with initial cyclic
order deliberately kept separate. This module does not identify unordered
two-black/two-white paths with the alternating four-arm event. -/

namespace ExceptionalTimes.WiredBranches

open PairSquareSewing

def Branches.endpoint {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} (_B : Branches ω D r R v s w) : Fin 4→Site := ![(0,0),s,w,s]

def Branches.path {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} (B : Branches ω D r R v s w) (i : Fin 4) :
    triangularGraph.Walk v (B.endpoint i) := by
  refine Fin.cases B.blackIn (fun j => ?_) i
  refine Fin.cases B.whiteFirst (fun j => ?_) j
  refine Fin.cases B.blackOut (fun j => ?_) j
  exact Fin.cases B.whiteSecond (fun k => Fin.elim0 k) j

theorem Branches.path_isPath {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} (B : Branches ω D r R v s w) (i : Fin 4) : (B.path i).IsPath := by
  fin_cases i
  · exact B.blackIn_path
  · exact B.whiteFirst_path
  · exact B.blackOut_path
  · exact B.whiteSecond_path

theorem Branches.path_intersection {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} (B : Branches ω D r R v s w)
    (i j : Fin 4) (hij : i≠j) (z : Site)
    (hi : z∈(B.path i).support) (hj : z∈(B.path j).support) : z=v ∨ z=s := by
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  · exact Or.inl (B.opposite_intersection z (Or.inl hi) (Or.inl hj))
  · exact Or.inl (B.black_intersection z hi hj)
  · exact Or.inl (B.opposite_intersection z (Or.inl hi) (Or.inr hj))
  · exact Or.inl (B.opposite_intersection z (Or.inl hj) (Or.inl hi))
  · exact Or.inl (B.opposite_intersection z (Or.inr hj) (Or.inl hi))
  · exact B.white_intersection z hi hj
  · exact Or.inl (B.black_intersection z hj hi)
  · exact Or.inl (B.opposite_intersection z (Or.inr hi) (Or.inl hj))
  · exact Or.inl (B.opposite_intersection z (Or.inr hi) (Or.inr hj))
  · exact Or.inl (B.opposite_intersection z (Or.inl hj) (Or.inr hi))
  · exact B.white_intersection z hj hi
  · exact Or.inl (B.opposite_intersection z (Or.inr hj) (Or.inr hi))

theorem Branches.path_color {ω : Configuration} {D : Finset Site} {r R : ℕ}
    {v s w : Site} (B : Branches ω D r R v s w) (i : Fin 4) (z : Site)
    (hi : z∈(B.path i).support) (hzD : z∉D)
    (hzr : z∉latticeBox r) (hzR : z∈latticeBox (R+1)) :
    ω z=decide (i.val%2=0) := by
  fin_cases i
  · exact B.black_color z (Or.inl hi) hzD hzr hzR
  · exact B.white_color z (Or.inl hi) hzD
  · exact B.black_color z (Or.inr hi) hzD hzr hzR
  · exact B.white_color z (Or.inr hi) hzD

/-- This contains every actual four-arm witness condition except the
cyclic ordering of the contacts. The subwalk data links each output to
its original pivotal branch for a subsequent topological argument. -/
structure TrimmedBranches (P : Probe) (ω : Configuration) (D : Finset Site) (r R : ℕ)
    {v s w : Site} (B : Branches ω D r R v s w) where
  start : Fin 4→Site
  finish : Fin 4→Site
  path : ∀ i,triangularGraph.Walk (start i) (finish i)
  isPath : ∀ i,(path i).IsPath
  isSubwalk : ∀ i,(path i).IsSubwalk (B.path i)
  starts : ∀ i,P.radius (start i)≤P.innerRadius
  finishes : ∀ i,P.outerRadius≤P.radius (finish i)
  colors : ∀ i z,z∈(path i).support→z∈P.region ∧ ω z=decide (i.val%2=0)
  disjoint : ∀ i j,i≠j→List.Disjoint (path i).support (path j).support
  contact : Fin 4→ℂ
  contacts : ∀ i,P.OuterContact (path i) (contact i)

theorem trim_branches (P : Probe) (hmesh : 2*P.mesh<P.innerRadius)
    {ω : Configuration} {D : Finset Site} {r R : ℕ} {v s w : Site}
    (B : Branches ω D r R v s w) (hv : v∈P.pocket)
    (hD : ∀ z∈D,z∈P.pocket)
    (hs : 2*P.outerRadius<P.radius s)
    (hend : ∀ i,P.outerRadius≤P.radius (B.endpoint i))
    (hregion : ∀ z∈P.region,z∉latticeBox r ∧ z∈latticeBox (R+1)) :
    Nonempty (TrimmedBranches P ω D r R B) := by
  have hx : P.radius v≤P.innerRadius := by
    change P.radius v<P.innerRadius/2 at hv
    linarith [P.inner_pos]
  have htrim (i : Fin 4) := trim_path_circle P hmesh (B.path i) (B.path_isPath i) hx (hend i)
  choose start hstart finish hfinish path hpath hsub hbounds _ contact hcontact using htrim
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
    contacts := hcontact }⟩
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

theorem TrimmedBranches.fourArms_of_cyclic {P : Probe} {ω : Configuration}
    {D : Finset Site} {r R : ℕ} {v s w : Site} {B : Branches ω D r R v s w}
    (T : TrimmedBranches P ω D r R B) (horder : P.CyclicOuter T.contact) :
    FourArms P ω :=
  ⟨T.start,T.finish,T.path,T.isPath,T.starts,T.finishes,T.colors,T.disjoint,
    T.contact,T.contacts,horder⟩

#print axioms trim_branches

end ExceptionalTimes.WiredBranches
