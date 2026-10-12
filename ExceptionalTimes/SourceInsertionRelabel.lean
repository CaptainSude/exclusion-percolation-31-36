import ExceptionalTimes.SourceDimerDistinguished
import ExceptionalTimes.SourceCalibratorTranslation
import Mathlib.Logic.Equiv.Fin.Basic

/-! Relabeling actual insertion histories and compact physical location
ranges. These identities select an arbitrary insertion without changing
the polygon tests, the iid field, or the signed coefficient. -/
open Set
open scoped Classical BigOperators
namespace ExceptionalTimes.PairSquareSewing.Source06Specialization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CenteredBlocks ProbeProduct EnvironmentVariance

theorem kernel_relabel {I J H : Type*} [Fintype I] [Fintype J] [Fintype H]
    (e : J ≃ I) (w : I → H → ℝ) (f : (I → H) → ℝ) :
    kernel (fun j => w (e j)) (fun h => f (fun i => h (e.symm i)))=kernel w f := by
  unfold kernel
  let E := Equiv.arrowCongr e (Equiv.refl H)
  calc
    _ = ∑ h : J→H, (∏i,w i (h (e.symm i)))*f (fun i => h (e.symm i)) := by
      apply Finset.sum_congr rfl
      intro h _
      congr 1
      calc
        _ = ∏j : J,w (e j) (h (e.symm (e j))) := by
          apply Finset.prod_congr rfl
          intro j _
          exact congrArg (fun a => w (e j) (h a)) (e.symm_apply_apply j).symm
        _ = _ := e.prod_comp (fun i : I => w i (h (e.symm i)))
    _ = _ := E.sum_comp (fun h => (∏i,w i (h i))*f h)

def relabelEndpoint {I J : Type*} (e : J ≃ I) (endpoint : I×Fin 2 ↪ Site) : J×Fin 2 ↪ Site :=
  (Equiv.prodCongr e (Equiv.refl (Fin 2))).toEmbedding.trans endpoint

theorem overwrite_relabel {I J : Type*} (e : J ≃ I) (endpoint : I×Fin 2 ↪ Site)
    (ω : Configuration) (h : J → Bool → PairColor) :
    overwriteSourceHistory (relabelEndpoint e endpoint) ω h=
      overwriteSourceHistory endpoint ω (fun i => h (e.symm i)) := by
  funext t v
  by_cases hv : v∈Set.range endpoint
  · obtain ⟨⟨i,a⟩,rfl⟩ := hv
    have hp : endpoint (i,a)=relabelEndpoint e endpoint (e.symm i,a) := by simp [relabelEndpoint]
    change overwriteDimers _ _ _ _=overwriteDimers _ _ _ _
    rw [overwriteDimers_endpoint,hp,overwriteDimers_endpoint]
  · have hv' : v∉Set.range (relabelEndpoint e endpoint) := by
      rintro ⟨⟨j,a⟩,hh⟩
      exact hv ⟨(e j,a),hh⟩
    exact (overwriteDimers_outside _ _ _ hv').trans (overwriteDimers_outside _ _ _ hv).symm

theorem multiPairResponse_relabel {I J : Type*} [Fintype I] [Fintype J]
    (e : J ≃ I) (endpoint : I×Fin 2 ↪ Site) (w : I→(Bool→PairColor)→ℝ)
    (ω : Configuration) (rule : Rule) (x z : Site) (F : TwoTimeConfiguration→ℝ) :
    multiPairResponse (fun j => w (e j)) rule.kernel
      (overwriteSourceHistory (relabelEndpoint e endpoint) ω) x z F=
      multiPairResponse w rule.kernel (overwriteSourceHistory endpoint ω) x z F := by
  simp only [multiPairResponse,overwrite_relabel]
  exact kernel_relabel e w (fun h => rawPairResponse rule.kernel (overwriteSourceHistory endpoint ω h) x z F)

theorem averaged_multi_relabel {I J : Type*} [Fintype I] [Fintype J]
    (e : J ≃ I) (endpoint : I×Fin 2 ↪ Site) (w : I→(Bool→PairColor)→ℝ)
    (Λ : Finset Site) (rule : Rule) (x z : Site) (F : TwoTimeConfiguration→ℝ) :
    averagedMultiPairResponse Λ (fun j => w (e j)) rule
      (relabelEndpoint e endpoint) x z F=
      averagedMultiPairResponse Λ w rule endpoint x z F := by
  apply FiniteLaw.expect_congr
  intro ω
  exact multiPairResponse_relabel e endpoint w (complete ω) rule x z F

def insertionOrder {k : ℕ} (i : Fin (k+1)) : Equiv.Perm (Fin (k+1)) :=
  (finSuccEquiv k).trans (finSuccEquiv' i).symm

@[simp] theorem insertionOrder_zero {k : ℕ} (i : Fin (k+1)) : insertionOrder i 0=i := by
  simp [insertionOrder]

@[simp] theorem insertionOrder_succ {k : ℕ} (i : Fin (k+1)) (j : Fin k) :
    insertionOrder i j.succ=i.succAbove j := by simp [insertionOrder]

def _root_.ExceptionalTimes.PairSquareSewing.SourceSeparatedGeometry.relabel {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (e : Equiv.Perm (Fin (k+1))) : SourceSeparatedGeometry q k where
  quads := G.quads
  locations := (fun x j => x (e j)) '' G.locations
  compact_locations := G.compact_locations.image (continuous_pi (fun j => continuous_apply (e j)))
  margin := G.margin
  margin_pos := G.margin_pos
  boxRadius := G.boxRadius
  separated := by
    rintro _ ⟨x,hx,rfl⟩ i j hij
    exact G.separated x hx (e i) (e j) (fun h => hij (e.injective h))
  boundary_separated := by
    rintro _ ⟨x,hx,rfl⟩ i j y hy
    exact G.boundary_separated x hx (e i) j y hy
  box_separated := by
    rintro _ ⟨x,hx,rfl⟩ i
    exact G.box_separated x hx (e i)

theorem _root_.ExceptionalTimes.PairSquareSewing.SourceSeparatedGeometry.admissible_relabel {q k : ℕ} (G : SourceSeparatedGeometry q k)
    (p : Equiv.Perm (Fin (k+1))) (e : ℝ) (x : Fin (k+1)→Site) (hx : G.Admissible e x) :
    (G.relabel p).Admissible e (fun i => x (p i)) := ⟨_,hx,rfl⟩

def residualEndpoint {k : ℕ} (endpoint : Fin (k+1)×Fin 2 ↪ Site) (i : Fin (k+1)) :
    Fin k×Fin 2 ↪ Site := relabelEndpoint (finSuccAboveEquiv i) (otherEndpoint endpoint i)

@[simp] theorem residualEndpoint_apply {k : ℕ} (endpoint : Fin (k+1)×Fin 2 ↪ Site)
    (i : Fin (k+1)) (j : Fin k) (a : Fin 2) :
    residualEndpoint endpoint i (j,a)=endpoint (i.succAbove j,a) := rfl

noncomputable def fullCoefficient {I : Type*} [Fintype I] (Λ : Finset Site)
    (endpoint : I×Fin 2 ↪ Site) (rules : I→Rule) (F : TwoTimeConfiguration→ℝ) : ℝ :=
  (fairSites Λ).expect (fun ω => kernel (fun i => (rules i).insertionWeight)
    (fun h => F (overwriteSourceHistory endpoint (complete ω) h)))

theorem fullCoefficient_distinguished {k : ℕ} (Λ : Finset Site)
    (endpoint : Fin (k+1)×Fin 2 ↪ Site) (rules : Fin (k+1)→Rule)
    (i : Fin (k+1)) (x z : Site) (h0 : endpoint (i,0)=x) (h1 : endpoint (i,1)=x+z)
    (F : TwoTimeConfiguration→ℝ) :
    fullCoefficient Λ endpoint rules F=
      averagedMultiPairResponse Λ (fun j => (rules (i.succAbove j)).insertionWeight)
        (rules i) (residualEndpoint endpoint i) x z F := by
  let : DecidableEq (Fin (k+1)) := Classical.decEq _
  rw [fullCoefficient,averaged_centered_kernel_distinguished Λ endpoint i _ (rules i) rfl x z h0 h1 F]
  exact (averaged_multi_relabel (finSuccAboveEquiv i) (otherEndpoint endpoint i)
    (fun j => (rules j).insertionWeight) Λ (rules i) x z F).symm

#print axioms kernel_relabel
#print axioms fullCoefficient_distinguished
end
end ExceptionalTimes.PairSquareSewing.Source06Specialization




