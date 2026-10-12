import ExceptionalTimes.SourceTrialsBound

/-!
Ordinary static normalization at a FIXED microscopic multiplier and outer
radius. The named input is the triangular-lattice consequence of source02,
Lemma 2.1, equations (four-powers) and (qm), and its explicit bounded-shape
and buffered square/circle conventions. The primary literature identified
there is Nolin (2008), Sections 2.3 and 4, Theorems 21--22.

This is a consequence, not a verbatim quotation: arm separation permits
the fixed changes of the inner cut by factor 64 and of the outer cut by a
fixed R. Quasi-multiplicativity and the positive fixed-scale lower bound
then compare with A_e(B e,1). The constant may depend on B and R; both are
fixed BEFORE the sewing tolerance. The input contains no paired law,
sewing error, or dynamical estimate.
-/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
open EnvironmentVariance ProbeProduct

/-- Literal fixed-radius fair-field consequence of the named static arm
inputs. The sample is the actual set of cells meeting the doubled disk. -/
def PublishedFixedRadiusFourArmComparison (B : ℝ) : Prop :=
  128≤B ∧ ∀R : ℝ,0<R→R≤1→∃C : ℝ,0<C ∧ ∃e0 : ℝ,0<e0 ∧
    ∀e : ℝ,∀he : 0<e,e<e0→∀x : Site,∀hB : 0<B,
      ∀hsmall : 4*(64*(B*e))<R,∀ha : 4*(B*e)<1,
      probability (fairSites (sourceDiskSites e he x (2*R)))
        (fun ω => FourArms (microProbe e he x B 64 R hB (by norm_num) hsmall) (complete ω))≤
        C*sourceArmCost e (B*e) he (mul_pos hB he) ha

theorem source_probability_first (Λ : Finset Site) (E : Configuration→Prop) :
    probability (sourceLaw Λ) (fun ω => E (complete ω.1))=
      probability (fairSites Λ) (fun ω => E (complete ω)) := by
  rw [probability,sourceLaw,FiniteLaw.expect_prod]
  simp only [FiniteLaw.expect_const]
  rfl

/-- The actual larger source sample has exactly the same local arm law
as the published minimal disk sample. -/
theorem source_probe_probability_disk (P : Probe) (Λ : Finset Site)
    (hcover : sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius)⊆Λ) :
    probability (sourceLaw Λ) (fun ω => FourArms P (complete ω.1))=
      probability (fairSites (sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius)))
        (fun ω => FourArms P (complete ω)) := by
  rw [source_probability_first]
  apply FiniteSiteLaw.fairSites_probability_restrict _ Λ hcover (FourArms P)
  intro ω η hagree
  apply fourArms_congr
  intro v hv
  exact hagree v (probe_region_subset_disk P hv)

/-- Fixed constants control every translated other-insertion probe,
uniformly in the source square, the remaining points and the tolerance. -/
theorem fixed_other_arm_bound {q k : ℕ} (G : SourceSeparatedGeometry q k) (B : ℝ)
    (hstatic : PublishedFixedRadiusFourArmComparison B) :
    ∃C : ℝ,0<C ∧ ∃e0 : ℝ,0<e0 ∧
      ∀e : ℝ,∀he : 0<e,e<e0→∀h : ℝ,∀x : Fin (k+1)→Site,∀i : Fin k,
      ∀hB : 0<B,∀hsmall : 4*(64*(B*e))<outerRadius G,∀ha : 4*(B*e)<1,
      probability (sourceLaw (sample G e he x h))
        (fun ω => FourArms (fixedOtherProbe G e he B hB hsmall (x i.succ)) (complete ω.1))≤
        C*sourceArmCost e (B*e) he (mul_pos hB he) ha := by
  obtain ⟨C,hC,e0,he0,hbound⟩ := hstatic.2 (outerRadius G) (outerRadius_pos G)
    (by linarith [outerRadius_le G])
  refine ⟨C,hC,e0,he0,?_⟩
  intro e he he0' h x i hB hsmall ha
  let P := fixedOtherProbe G e he B hB hsmall (x i.succ)
  have hcover : sourceDiskSites P.mesh P.mesh_pos P.center (2*P.outerRadius)⊆sample G e he x h := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (G.disk_sites_subset e he x _ i.succ hv))
  rw [source_probe_probability_disk P _ hcover]
  exact hbound e he he0' (x i.succ) hB hsmall ha

#print axioms source_probe_probability_disk
#print axioms fixed_other_arm_bound
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization

