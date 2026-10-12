import ExceptionalTimes.SourceNormalizedInsertion

/-! Finite telescoping of actual mixed insertion histories. Every
denominator is the central microscopic Q0 response matched by sewing.
The result is uniform on each fixed compact separated location family. -/
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CenteredBlocks ProbeProduct EnvironmentVariance

theorem fullCoefficient_restrict_polygons {I Q : Type*} [Fintype I]
    (quads : Q→PolygonQuad) (S Λ : Finset Site) (hS : S⊆Λ)
    (hQ : ∀q,(quads q).support⊆S) (outer : (Q×Bool→Bool)→ℝ)
    (endpoint : I×Fin 2 ↪ Site) (rules : I→Rule) :
    fullCoefficient Λ endpoint rules (fun ξ => outer (PolygonSewing.crossingVector quads ξ))=
      fullCoefficient S endpoint rules (fun ξ => outer (PolygonSewing.crossingVector quads ξ)) := by
  apply FiniteSiteLaw.fairSites_restrict S Λ hS
    (fun ω => kernel (fun i => (rules i).insertionWeight)
      (fun h => outer (PolygonSewing.crossingVector quads (overwriteSourceHistory endpoint ω h))))
  intro ω η heq
  unfold kernel
  apply Finset.sum_congr rfl
  intro hist _
  congr 1
  apply congrArg outer
  funext qt
  apply (quads qt.1).test_congr
  exact fun v hv => overwriteSourceHistory_congr endpoint ω η hist _
    (fun _ hs => heq _ hs) qt.2 (hQ qt.1 hv)

def hybridRules {N : ℕ} (m : ℕ) (r₁ r₂ : Rule) (i : Fin N) : Rule :=
  if i.val<m then r₁ else r₂

theorem hybridRules_step {N m : ℕ} (hm : m<N) (r₁ r₂ : Rule) :
    hybridRules (m+1) r₁ r₂=Function.update (hybridRules m r₁ r₂) ⟨m,hm⟩ r₁ := by
  funext i
  by_cases hi : i=⟨m,hm⟩
  · subst i
    simp [hybridRules]
  · have hv : i.val≠m := fun h => hi (Fin.ext h)
    simp only [Function.update_of_ne hi,hybridRules]
    have ht : i.val<m+1 ↔ i.val<m := by omega
    simp only [ht]

theorem hybridRules_old {N m : ℕ} (hm : m<N) (r₁ r₂ : Rule) :
    hybridRules m r₁ r₂=Function.update (hybridRules m r₁ r₂) ⟨m,hm⟩ r₂ := by
  symm
  apply Function.update_eq_self_iff.mpr
  simp [hybridRules]

theorem finite_rule_telescope {N : ℕ} (F : (Fin N→Rule)→ℝ) (η : ℝ) (_hη : 0≤η)
    (hstep : ∀i : Fin N,∀rules : Fin N→Rule,∀r₁ r₂ : Rule,
      |F (Function.update rules i r₁)-F (Function.update rules i r₂)|≤η)
    (r₁ r₂ : Rule) : |F (fun _ => r₁)-F (fun _ => r₂)|≤N*η := by
  have hchain : ∀m : ℕ,m≤N→
      |F (hybridRules m r₁ r₂)-F (hybridRules 0 r₁ r₂)|≤m*η := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : m<N := by omega
      have hlocal := hstep ⟨m,hm'⟩ (hybridRules m r₁ r₂) r₁ r₂
      rw [←hybridRules_step hm' r₁ r₂,←hybridRules_old hm' r₁ r₂] at hlocal
      calc
        _≤|F (hybridRules (m+1) r₁ r₂)-F (hybridRules m r₁ r₂)|+
          |F (hybridRules m r₁ r₂)-F (hybridRules 0 r₁ r₂)| := abs_sub_le _ _ _
        _≤η+m*η := add_le_add hlocal (ih (by omega))
        _=_ := by push_cast; ring
  have hfinal : hybridRules N r₁ r₂=(fun _ : Fin N => r₁) := by
    funext i
    exact ite_eq_left i.isLt
  have hfirst : hybridRules 0 r₁ r₂=(fun _ : Fin N => r₂) := by
    funext i
    exact ite_eq_right (Nat.not_lt_zero _)
  simpa only [hfinal,hfirst] using hchain N le_rfl

theorem uniform_full_normalized_limit {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hseams : PublishedFixedSquareSeams B) (hstatic : PublishedFixedRadiusFourArmComparison B)
    (hbulk : PublishedPolygonBulkArms) (hlower : PublishedReferenceSquareLower)
    (harmlower : PublishedCircularArmLower B) (hattach : UnitStaticAttachment.PublishedUnitAttachment B) :
    ∀δ : ℝ,0<δ→∃e0 : ℝ,0<e0 ∧ ∀e : ℝ,∀he : 0<e,e<e0→
      ∀x : Fin (k+1)→Site,G.Admissible e x→∀endpoint : Fin (k+1)×Fin 2 ↪ Site,
      (∀j,endpoint (j,0)=x j)→(∀j,endpoint (j,1)=x j+(1,0))→
      ∀r₁ r₂ : Rule,∀outer : (Fin q×Bool→Bool)→ℝ,(∀c,|outer c|≤1)→
      |fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (fun _ => r₁)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))/(centralS e he r₁)^(k+1)-
       fullCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint (fun _ => r₂)
        (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ))/(centralS e he r₂)^(k+1)|<δ := by
  intro δ hδ
  let η : ℝ := δ/(2*(k+1))
  have hη : 0<η := by dsimp [η]; positivity
  choose ei hei hbound using fun i : Fin (k+1) =>
    uniform_normalized_update G B hseams hstatic hbulk hlower harmlower hattach i η hη
  let e0 := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin (k+1))).Nonempty) ei
  have he0 : 0<e0 := (Finset.lt_inf'_iff _).mpr (fun i _ => hei i)
  refine ⟨e0,he0,?_⟩
  intro e he he0' x hx endpoint h0 h1 r₁ r₂ outer hout
  let F := fun rules : Fin (k+1)→Rule =>
    normalizedCoefficient (polygonFamilySupport (G.latticeQuads e he)) endpoint rules
      (fun ξ => outer (PolygonSewing.crossingVector (G.latticeQuads e he) ξ)) (centralS e he)
  have hstep (i : Fin (k+1)) (rules : Fin (k+1)→Rule) (s₁ s₂ : Rule) :
      |F (Function.update rules i s₁)-F (Function.update rules i s₂)|≤η := by
    exact (hbound i e he (he0'.trans_le (Finset.inf'_le ei (Finset.mem_univ i)))
      x hx endpoint h0 h1 rules s₁ s₂ outer hout).le
  have htel := finite_rule_telescope F η hη.le hstep r₁ r₂
  have hlast : ((k+1 : ℕ) : ℝ)*η<δ := by
    dsimp [η]
    have hn : (0 : ℝ)<k+1 := by positivity
    push_cast
    field_simp
    linarith
  have hh := htel.trans_lt hlast
  simpa [F,normalizedCoefficient] using hh

#print axioms finite_rule_telescope
#print axioms uniform_full_normalized_limit
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

