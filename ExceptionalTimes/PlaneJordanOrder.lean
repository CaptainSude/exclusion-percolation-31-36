import ExceptionalTimes.FirstCircleTrimming
import ExceptionalTimes.PlaneCycleBranches

/-! Explicit deterministic Jordan crossing criterion.

This is a classical reformulation of planar separation, not a new
percolation or probability assumption. References: Diestel, Graph Theory,
Section 4.1, Theorem 4.1.1 and Lemma 4.1.2; the same alternating-order step
is used in the proof of OpenAI source02 Lemma 2.2, pinned commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a. The displayed formulation is
the finite straight-line triangular-drawing specialization, not a literal
quotation of a separately numbered theorem in either source.

The complete drawn white cycle, actual complementary components, unique
intersection at the common vertex, and FIRST circle contacts are explicit.
No color event, pivotality, arm probability, or graph-cut surrogate occurs.
The input is a theorem parameter and is not asserted as a proved theorem.
-/

namespace ExceptionalTimes.PairSquareSewing

open TriangularPlane Set

/-- The contact belongs to an initial segment of the entire original
branch; earlier points of that segment stay inside the same circle. -/
def Probe.FirstExit (P : Probe) {u v : Site}
    (p : triangularGraph.Walk u v) (q : ℂ) : Prop :=
  ∃ w,∃ initial : triangularGraph.Walk u w,∃ tail : triangularGraph.Walk w v,
    initial.append tail=p ∧ P.OuterContact initial q

/-- An explicitly assumed classical topological result. Reversing the
two white branches accounts for the two orientations of the cycle. -/
def PublishedPolygonCrossingOrder : Prop :=
  ∀ (P : Probe) (v a b s : Site),P.radius v<P.outerRadius →
    P.outerRadius≤P.radius a → P.outerRadius≤P.radius b → P.outerRadius<P.radius s →
    ∀ (blackIn : triangularGraph.Walk v a) (blackOut : triangularGraph.Walk v b)
      (whiteFirst whiteSecond : triangularGraph.Walk v s),
      blackIn.IsPath → blackOut.IsPath → whiteFirst.IsPath → whiteSecond.IsPath →
      (whiteFirst.append whiteSecond.reverse).IsCycle →
      (∀ z∈blackIn.support,z∈blackOut.support→z=v) →
      (∀ z,(z∈blackIn.support ∨ z∈blackOut.support) →
        (z∈whiteFirst.support ∨ z∈whiteSecond.support) → z=v) →
      point a∉walkTrace (whiteFirst.append whiteSecond.reverse) →
      point b∉walkTrace (whiteFirst.append whiteSecond.reverse) →
      point b∉connectedComponentIn (walkTrace (whiteFirst.append whiteSecond.reverse))ᶜ (point a) →
      ∀ q₀ q₁ q₂ q₃ : ℂ,
        P.FirstExit blackIn q₀ → P.FirstExit whiteFirst q₁ →
        P.FirstExit blackOut q₂ → P.FirstExit whiteSecond q₃ →
        P.CyclicOuter ![q₀,q₁,q₂,q₃] ∨ P.CyclicOuter ![q₀,q₃,q₂,q₁]

theorem trim_first_circle_with_original_contact (P : Probe) (hmesh : 2*P.mesh<P.innerRadius)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (hu : P.radius u≤P.innerRadius) (hv : P.outerRadius≤P.radius v) :
    ∃ x,P.radius x≤P.innerRadius ∧ ∃ y,P.outerRadius≤P.radius y ∧
      ∃ q : triangularGraph.Walk x y,q.IsPath ∧ q.IsSubwalk p ∧
        (∀ z∈q.support,z∈P.region) ∧
        ∃ contact : ℂ,P.OuterContact q contact ∧ P.FirstExit p contact := by
  obtain ⟨x,hx,y,hy,before,q,after,heq,hq,hsub,hregion,_,contact,hcontact,hfirst⟩ :=
    trim_first_circle P hmesh p hp hu hv
  exact ⟨x,hx,y,hy,q,hq,hsub,hregion,contact,hcontact,y,before.append q,after,heq,hfirst⟩

#print axioms trim_first_circle_with_original_contact

end ExceptionalTimes.PairSquareSewing
