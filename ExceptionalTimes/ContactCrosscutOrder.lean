import ExceptionalTimes.OuterContactCurves
import ExceptionalTimes.AnnularCrosscutOrder
import ExceptionalTimes.PathEndTrimming

open Set
open scoped Classical unitInterval

namespace ExceptionalTimes.Annulus

open TriangularPlane

theorem walkToContact_proper_mixedAnnulus {u w v : Site} (p : triangularGraph.Walk u w)
    (last : triangularGraph.Adj w v) (hp : (p.concat last).IsPath)
    (r : ℤ) (S : ℝ) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1)
    (hu : hexRadius u = r)
    (hlower : ∀ z ∈ (p.concat last).support, r ≤ hexRadius z)
    (hproper : ∀ z ∈ (p.concat last).support, hexRadius z = r → z = u)
    (hin : ∀ z ∈ p.support, ‖HexTiling.planeMap (point z)‖ < S)
    (hend : ‖HexTiling.planeMap (edgePoint w v t)‖ = S) :
    Function.Injective (walkToContact (v := v) t p) ∧
      (∀ a, walkToContact (v := v) t p a ∈ mixedHexAnnulus r S) ∧
      (∀ a : unitInterval, 0 < (a:ℝ) → (a:ℝ) < 1 →
        (r:ℝ) < hexGauge (walkToContact (v := v) t p a) ∧
          ‖HexTiling.planeMap (walkToContact (v := v) t p a)‖ < S) := by
  have hj := walkToContact_injective p last hp ht ht'
  have hmem (a : unitInterval) : walkToContact (v := v) t p a ∈
      Set.range (walkToContact (v := v) t p) := ⟨a,rfl⟩
  have htrace (a : unitInterval) := walkToContact_range_subset p last ht ht' (hmem a)
  refine ⟨hj,?_,?_⟩
  · intro a
    constructor
    · by_cases he : walkToContact (v := v) t p a = point u
      · rw [he,hexGauge_point,hu]
      · exact (walkTrace_hexGauge_gt_of_proper (p.concat last) hlower hproper _ (htrace a) he).le
    · exact walkToContact_norm_le p S ht hin hend _ (hmem a)
  · intro a ha0 ha1
    have hstart : walkToContact (v := v) t p a ≠ point u := by
      intro he
      have he' := congrArg Subtype.val (hj (he.trans (walkToContact (v := v) t p).source.symm))
      dsimp at he'
      linarith
    have hfinish : walkToContact (v := v) t p a ≠ edgePoint w v t := by
      intro he
      have he' := congrArg Subtype.val (hj (he.trans (walkToContact (v := v) t p).target.symm))
      dsimp at he'
      linarith
    exact ⟨walkTrace_hexGauge_gt_of_proper (p.concat last) hlower hproper _ (htrace a) hstart,
      walkToContact_norm_lt p S ht hin hend _ (hmem a) hfinish⟩

/-- The original partial terminal-edge contacts determine the order of
the inner hex cut. All round-annulus hypotheses are derived from the
actual paths and the explicit mixed-annulus homeomorphism. -/
theorem contact_hex_cyclic_order (orderInput : PublishedAnnularCrosscutOrder)
    (r : ℤ) (S : ℝ) (hr : 0 < r) (hS : 2*(r:ℝ) < S)
    (u w v : Fin 4 → Site) (p : ∀ i, triangularGraph.Walk (u i) (w i))
    (last : ∀ i, triangularGraph.Adj (w i) (v i))
    (hp : ∀ i, ((p i).concat (last i)).IsPath)
    (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i ∧ t i ≤ 1)
    (hu : ∀ i, hexRadius (u i) = r)
    (hlower : ∀ i z, z ∈ ((p i).concat (last i)).support → r ≤ hexRadius z)
    (hproper : ∀ i z, z ∈ ((p i).concat (last i)).support → hexRadius z = r → z = u i)
    (hin : ∀ i z, z ∈ (p i).support → ‖HexTiling.planeMap (point z)‖ < S)
    (hend : ∀ i, ‖HexTiling.planeMap (edgePoint (w i) (v i) (t i))‖ = S)
    (hdis : ∀ i j, i ≠ j → List.Disjoint ((p i).concat (last i)).support
      ((p j).concat (last j)).support) :
    CyclicAngles (fun i => triangularEmbedding (u i)) ↔
      CyclicAngles (fun i => HexTiling.planeMap (edgePoint (w i) (v i) (t i))) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hrS : (r:ℝ) < S := by linarith
  have htop (i : Fin 4) := walkToContact_proper_mixedAnnulus (p i) (last i) (hp i) r S
    (ht i).1 (ht i).2 (hu i) (hlower i) (hproper i) (hin i) (hend i)
  let curve (i : Fin 4) := walkToContact (v := v i) (t i) (p i)
  let H := mixedHexAnnulusHomeomorph (r:ℝ) S hr' hS
  let γ : Fin 4 → unitInterval → ℂ := fun i a => (H ⟨curve i a,(htop i).2.1 a⟩ : ℂ)
  have hc : ∀ i, Continuous (γ i) := fun i =>
    continuous_subtype_val.comp (H.continuous.comp ((curve i).continuous.subtype_mk _))
  have hj : ∀ i, Function.Injective (γ i) := by
    intro i a b hab
    exact (htop i).1 (congrArg Subtype.val (H.injective (Subtype.ext hab)))
  have hd : ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨a,rfl⟩ ⟨b,hb⟩
    have he := congrArg Subtype.val (H.injective (Subtype.ext hb))
    change curve j b = curve i a at he
    have hai := walkToContact_range_subset (p i) (last i) (ht i).1 (ht i).2 ⟨a,rfl⟩
    have hbj := walkToContact_range_subset (p j) (last j) (ht j).1 (ht j).2 ⟨b,rfl⟩
    have htr := disjoint_supports_disjoint_traces ((p i).concat (last i)) ((p j).concat (last j))
      (fun x hxi hxj => hdis i j hij hxi hxj)
    exact Set.disjoint_left.mp htr hai (he ▸ hbj)
  have he : ∀ i, ‖γ i 0‖ = (r:ℝ) ∧ ‖γ i 1‖ = S := by
    intro i
    constructor
    · apply mixedHexAnnulusHomeomorph_inner
      change hexGauge (curve i 0) = _
      rw [(curve i).source,hexGauge_point,hu]
    · change ‖(mixedHexAnnulusHomeomorph _ _ _ _ _ : ℂ)‖ = _
      rw [mixedHexAnnulusHomeomorph_outer]
      · change ‖HexTiling.planeMap (curve i 1)‖ = _
        rw [(curve i).target]
        exact hend i
      · change ‖HexTiling.planeMap (curve i 1)‖ = _
        rw [(curve i).target]
        exact hend i
  have ho : ∀ i (a : unitInterval), 0 < (a:ℝ) → (a:ℝ) < 1 →
      (r:ℝ) < ‖γ i a‖ ∧ ‖γ i a‖ < S := by
    intro i a ha ha'
    exact mixedHexAnnulusHomeomorph_strict _ _ _ _ _ ((htop i).2.2 a ha ha').1
      ((htop i).2.2 a ha ha').2
  have horder := orderInput r S hr' hrS γ hc hj hd he ho
  have ha0 (i : Fin 4) : Complex.arg (γ i 0) = Complex.arg (triangularEmbedding (u i)) := by
    change Complex.arg (mixedHexAnnulusHomeomorph _ _ _ _ _ : ℂ) = _
    rw [mixedHexAnnulusHomeomorph_arg]
    change Complex.arg (HexTiling.planeMap (curve i 0)) = _
    rw [(curve i).source]
    rfl
  have ha1 (i : Fin 4) : Complex.arg (γ i 1) =
      Complex.arg (HexTiling.planeMap (edgePoint (w i) (v i) (t i))) := by
    change Complex.arg (mixedHexAnnulusHomeomorph _ _ _ _ _ : ℂ) = _
    rw [mixedHexAnnulusHomeomorph_arg]
    change Complex.arg (HexTiling.planeMap (curve i 1)) = _
    rw [(curve i).target]
  simpa only [CyclicAngles,ha0,ha1] using horder

#print axioms walkToContact_proper_mixedAnnulus
#print axioms contact_hex_cyclic_order

/-- Retain the last inner-level departure while keeping the original
terminal edge literally unchanged. In particular its circle contact is
still the same point, even if the original path revisited the inner cut. -/
theorem last_departure_before_last_edge (f : Site → ℤ)
    (hstep : ∀ {u v}, TriangularAdj u v → f v ≤ f u+1)
    {u w v : Site} (p : triangularGraph.Walk u w) (last : triangularGraph.Adj w v)
    (hp : (p.concat last).IsPath) (r : ℤ) (hu : f u ≤ r) (hv : r < f v) :
    ∃ x, f x = r ∧ ∃ q : triangularGraph.Walk x w, ∃ before : triangularGraph.Walk u x,
      before.append q = p ∧ (q.concat last).IsPath ∧ (q.concat last).IsSubwalk (p.concat last) ∧
      (∀ z ∈ (q.concat last).support, r ≤ f z ∧ (f z = r → z = x)) := by
  have hpinitial : p.IsPath := (SimpleGraph.Walk.isPath_concat last).mp hp |>.1
  obtain ⟨x,hx,q,before,hbefore,_,_,hA⟩ := last_departure_suffix {z | f z ≤ r} p hpinitial hu
  have heq : before.append (q.concat last) = p.concat last := by
    rw [SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.append_assoc,hbefore,
      SimpleGraph.Walk.concat_eq_append]
  have hsub : (q.concat last).IsSubwalk (p.concat last) :=
    SimpleGraph.Walk.isSubwalk_of_append_right heq.symm
  have hA' : ∀ z ∈ (q.concat last).support, f z ≤ r → z = x := by
    intro z hz hzr
    rw [SimpleGraph.Walk.support_concat,List.mem_append] at hz
    rcases hz with hz | hz
    · exact hA z hz hzr
    · have hzv : z = v := by simpa only [List.mem_singleton] using hz
      subst z
      omega
  have hxv : x ≠ v := by intro he; subst x; change f v ≤ r at hx; omega
  have hx' := PairSquareSewing.walk_start_level f hstep (q.concat last)
    (SimpleGraph.Walk.not_nil_of_ne hxv) r hx hA'
  refine ⟨x,hx',q,before,hbefore,SimpleGraph.Walk.isPath_of_isSubwalk hsub hp,hsub,?_⟩
  intro z hz
  constructor
  · by_cases hzr : f z ≤ r
    · rw [hA' z hz hzr,hx']
    · omega
  · exact fun he => hA' z hz he.le

theorem first_arrival_level (f : Site → ℤ)
    (hstep : ∀ {u v}, TriangularAdj u v → f v ≤ f u+1)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (R : ℤ) (hu : f u < R) (hv : R ≤ f v) :
    ∃ y, f y = R ∧ ∃ q : triangularGraph.Walk u y,
      q.IsPath ∧ q.IsSubwalk p ∧
      (∀ z ∈ q.support, f z ≤ R ∧ (f z = R → z = y)) := by
  obtain ⟨y,hy,q,_,_,hq,hsub,hB⟩ := first_arrival_prefix {z | R ≤ f z} p hp hv
  have hnegstep : ∀ {a b}, TriangularAdj a b → -f b ≤ -f a+1 := by
    intro a b hab
    have := hstep (triangularAdj_symm hab)
    omega
  have hyu : y ≠ u := by intro he; subst y; change R ≤ f u at hy; omega
  have hrevproper : ∀ z ∈ q.reverse.support, -f z ≤ -R → z = y := by
    intro z hz hzr
    apply hB z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
    change R ≤ f z
    omega
  have hyneg := PairSquareSewing.walk_start_level (fun z => -f z) hnegstep q.reverse
    (SimpleGraph.Walk.not_nil_of_ne hyu) (-R) (neg_le_neg hy) hrevproper
  have hy' : f y = R := by omega
  refine ⟨y,hy',q,hq,hsub,?_⟩
  intro z hz
  constructor
  · by_cases hzr : R ≤ f z
    · rw [hB z hz hzr,hy']
    · omega
  · exact fun he => hB z hz he.ge

#print axioms last_departure_before_last_edge
#print axioms first_arrival_level

/-- Actual circle-contact paths admit ordered, proper hex-to-hex
subpaths. Their input supports are retained explicitly, so their colors
and membership in a source event transfer without any extra premise. -/
theorem circle_contacts_to_ordered_hex_paths (orderInput : PublishedAnnularCrosscutOrder)
    (r R : ℤ) (S : ℝ) (hr : 0 < r) (hrR : r < R) (hS : 2*(r:ℝ) < S)
    (u w v : Fin 4 → Site) (p : ∀ i, triangularGraph.Walk (u i) (w i))
    (last : ∀ i, triangularGraph.Adj (w i) (v i))
    (hp : ∀ i, ((p i).concat (last i)).IsPath)
    (t : Fin 4 → ℝ) (ht : ∀ i, 0 < t i ∧ t i ≤ 1)
    (hu : ∀ i, hexRadius (u i) ≤ r) (hv : ∀ i, R ≤ hexRadius (v i))
    (hin : ∀ i z, z ∈ (p i).support → ‖HexTiling.planeMap (point z)‖ < S)
    (hend : ∀ i, ‖HexTiling.planeMap (edgePoint (w i) (v i) (t i))‖ = S)
    (hdis : ∀ i j, i ≠ j → List.Disjoint ((p i).concat (last i)).support
      ((p j).concat (last j)).support)
    (horder : CyclicAngles (fun i => HexTiling.planeMap (edgePoint (w i) (v i) (t i)))) :
    ∃ a b : Fin 4 → Site, ∃ q : ∀ i, triangularGraph.Walk (a i) (b i),
      (∀ i, (q i).IsPath ∧ (q i).IsSubwalk ((p i).concat (last i))) ∧
      (∀ i, hexRadius (a i) = r ∧ hexRadius (b i) = R) ∧
      (∀ i z, z ∈ (q i).support → r ≤ hexRadius z ∧ hexRadius z ≤ R) ∧
      (∀ i z, z ∈ (q i).support → hexRadius z = r → z = a i) ∧
      (∀ i z, z ∈ (q i).support → hexRadius z = R → z = b i) ∧
      (∀ i j, i ≠ j → List.Disjoint (q i).support (q j).support) ∧
      CyclicAngles (fun i => triangularEmbedding (a i)) ∧
      CyclicAngles (fun i => triangularEmbedding (b i)) := by
  have hstep : ∀ {u v}, TriangularAdj u v → hexRadius v ≤ hexRadius u+1 := by
    intro u v huv
    simpa only [sub_zero] using PairSquareSewing.centered_hexRadius_step 0 huv
  have htrim (i : Fin 4) := last_departure_before_last_edge hexRadius hstep (p i) (last i)
    (hp i) r (hu i) (hrR.trans_le (hv i))
  choose a ha tail before hbefore htail hsub hproper using htrim
  have htailin : ∀ i z, z ∈ (tail i).support → ‖HexTiling.planeMap (point z)‖ < S := by
    intro i z hz
    exact hin i z ((SimpleGraph.Walk.isSubwalk_of_append_right (hbefore i).symm).support_subset hz)
  have htaildis : ∀ i j, i ≠ j → List.Disjoint ((tail i).concat (last i)).support
      ((tail j).concat (last j)).support := by
    intro i j hij z hzi hzj
    exact hdis i j hij ((hsub i).support_subset hzi) ((hsub j).support_subset hzj)
  have hinnerorder := (contact_hex_cyclic_order orderInput r S hr hS a w v tail last htail t ht ha
    (fun i z hz => (hproper i z hz).1) (fun i z hz => (hproper i z hz).2)
    htailin hend htaildis).mpr horder
  have hcut (i : Fin 4) := first_arrival_level hexRadius hstep ((tail i).concat (last i))
    (htail i) R (by rw [ha]; exact hrR) (hv i)
  choose b hb q hq hqsub hqbound using hcut
  have hqfull (i : Fin 4) := (hqsub i).trans (hsub i)
  have hbounds : ∀ i z, z ∈ (q i).support → r ≤ hexRadius z ∧ hexRadius z ≤ R :=
    fun i z hz => ⟨(hproper i z ((hqsub i).support_subset hz)).1,(hqbound i z hz).1⟩
  have hinner : ∀ i z, z ∈ (q i).support → hexRadius z = r → z = a i :=
    fun i z hz => (hproper i z ((hqsub i).support_subset hz)).2
  have houter : ∀ i z, z ∈ (q i).support → hexRadius z = R → z = b i :=
    fun i z hz => (hqbound i z hz).2
  have hqdis : ∀ i j, i ≠ j → List.Disjoint (q i).support (q j).support := by
    intro i j hij z hzi hzj
    exact hdis i j hij ((hqfull i).support_subset hzi) ((hqfull j).support_subset hzj)
  have houterorder := (proper_hex_paths_cyclic_order orderInput r R hr hrR a b q hq ha hb
    hbounds hinner houter hqdis).mp hinnerorder
  exact ⟨a,b,q,fun i => ⟨hq i,hqfull i⟩,fun i => ⟨ha i,hb i⟩,hbounds,hinner,houter,hqdis,
    hinnerorder,houterorder⟩

#print axioms circle_contacts_to_ordered_hex_paths

end ExceptionalTimes.Annulus

namespace ExceptionalTimes.PairSquareSewing

open Annulus TriangularPlane

def centerGraph (c : Site) : triangularGraph →g triangularGraph where
  toFun v := v-c
  map_rel' := by
    intro u v huv
    change TriangularAdj (u-c) (v-c)
    change TriangularAdj u v at huv
    simp only [TriangularAdj,Prod.fst_sub,Prod.snd_sub] at huv ⊢
    omega

theorem centerGraph_injective (c : Site) : Function.Injective (centerGraph c) := by
  intro u v h
  have he := congrArg (fun z : Site => z+c) h
  change (u-c)+c = (v-c)+c at he
  simpa only [sub_add_cancel] using he

theorem centerGraph_concat (c : Site) {u w v : Site} (p : triangularGraph.Walk u w)
    (last : triangularGraph.Adj w v) :
    (p.concat last).map (centerGraph c) =
      (p.map (centerGraph c)).concat ((centerGraph c).map_adj last) := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa only [SimpleGraph.Walk.concat_cons,SimpleGraph.Walk.map_cons] using congrArg (SimpleGraph.Walk.cons _) (ih last)

theorem edgeTrace_centered (mesh : ℝ) (c u v : Site) {q : ℂ} (hq : q ∈ edgeTrace mesh u v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      q-position mesh c = (mesh:ℂ)*HexTiling.planeMap (edgePoint (u-c) (v-c) t) := by
  obtain ⟨t,ht0,ht1,rfl⟩ := hq
  refine ⟨t,ht0,ht1,?_⟩
  apply Complex.ext <;>
    simp [position,triangularEmbedding,HexTiling.planeMap,edgePoint] <;> ring

theorem contact_radius_normalized (P : Probe) {w v : Site} {q : ℂ} {t : ℝ}
    (he : q-position P.mesh P.center =
      (P.mesh:ℂ)*HexTiling.planeMap (edgePoint (w-P.center) (v-P.center) t))
    (hq : dist q (position P.mesh P.center) = P.outerRadius) :
    ‖HexTiling.planeMap (edgePoint (w-P.center) (v-P.center) t)‖ = P.outerRadius/P.mesh := by
  rw [Complex.dist_eq,he,norm_mul] at hq
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos P.mesh_pos] at hq
  apply (eq_div_iff P.mesh_pos.ne').mpr
  linarith

theorem contact_parameter_pos (P : Probe) {w v : Site} {q : ℂ} {t : ℝ}
    (ht : 0 ≤ t) (hw : P.radius w < P.outerRadius)
    (he : q-position P.mesh P.center =
      (P.mesh:ℂ)*HexTiling.planeMap (edgePoint (w-P.center) (v-P.center) t))
    (hq : dist q (position P.mesh P.center) = P.outerRadius) : 0 < t := by
  apply lt_of_le_of_ne ht
  intro hz
  have htzero : t = 0 := hz.symm
  have hn := contact_radius_normalized P he hq
  rw [htzero,edgePoint_zero] at hn
  change ‖triangularEmbedding (w-P.center)‖ = P.outerRadius/P.mesh at hn
  rw [P.radius_eq_mesh_norm,hn,mul_div_cancel₀ _ P.mesh_pos.ne'] at hw
  exact hw.false

#print axioms centerGraph_concat
#print axioms edgeTrace_centered
#print axioms contact_parameter_pos

/-- The literal circular four-arm event gives alternating, disjoint,
proper paths between exact positive hex levels, in counterclockwise
order at both cuts. Coordinates are translated to the probe center;
colors are read from the original configuration at the translated site.
All radial margins and the sole classical order input are explicit. -/
theorem fourArms_ordered_hex_paths (orderInput : PublishedAnnularCrosscutOrder)
    (P : Probe) (ω : Configuration) (r R : ℤ) (hr : 0 < r) (hrR : r < R)
    (hradius : 4*P.innerRadius ≤ P.mesh*(r:ℝ))
    (hRadius : 2*P.mesh*(R:ℝ) ≤ P.outerRadius) (ha : FourArms P ω) :
    ∃ s t : Fin 4 → Site, ∃ q : ∀ i, triangularGraph.Walk (s i) (t i),
      (∀ i, (q i).IsPath) ∧
      (∀ i, hexRadius (s i) = r ∧ hexRadius (t i) = R) ∧
      (∀ i z, z ∈ (q i).support → r ≤ hexRadius z ∧ hexRadius z ≤ R ∧
        ω (z+P.center) = decide (i.val % 2 = 0)) ∧
      (∀ i z, z ∈ (q i).support → hexRadius z = r → z = s i) ∧
      (∀ i z, z ∈ (q i).support → hexRadius z = R → z = t i) ∧
      (∀ i j, i ≠ j → List.Disjoint (q i).support (q j).support) ∧
      CyclicAngles (fun i => triangularEmbedding (s i)) ∧
      CyclicAngles (fun i => triangularEmbedding (t i)) := by
  obtain ⟨a,b,p,hp,hstart,hfinish,hcolor,hdis,contact,hcontact,hcyc⟩ := ha
  choose w initial last heq hin hedge hdist using hcontact
  choose τ hτ0 hτ1 hτeq using fun i => edgeTrace_centered P.mesh P.center (w i) (b i) (hedge i)
  let f := centerGraph P.center
  let p' (i : Fin 4) := (initial i).map f
  have last' (i : Fin 4) : triangularGraph.Adj (f (w i)) (f (b i)) := f.map_adj (last i)
  have hmap (i : Fin 4) : (p i).map f = (p' i).concat (last' i) := by
    rw [heq i]
    exact centerGraph_concat P.center (initial i) (last i)
  have hp' (i : Fin 4) : ((p' i).concat (last' i)).IsPath := by
    rw [←hmap]
    exact (hp i).map (centerGraph_injective P.center)
  have hτ (i : Fin 4) : 0 < τ i ∧ τ i ≤ 1 :=
    ⟨contact_parameter_pos P (hτ0 i) (hin i _ (initial i).end_mem_support) (hτeq i) (hdist i),hτ1 i⟩
  have hcuts (i : Fin 4) : hexRadius (f (a i)) ≤ r ∧ R ≤ hexRadius (f (b i)) := by
    have hleft := (P.hexRadius_comparison (a i)).1
    have hright := (P.hexRadius_comparison (b i)).2
    have hs := hstart i
    have hf := hfinish i
    constructor
    · change hexRadius (a i-P.center) ≤ r
      have h : (hexRadius (a i-P.center):ℝ) ≤ (r:ℝ) := by nlinarith [P.mesh_pos]
      exact_mod_cast h
    · change R ≤ hexRadius (b i-P.center)
      have h : (R:ℝ) ≤ (hexRadius (b i-P.center):ℝ) := by nlinarith [P.mesh_pos]
      exact_mod_cast h
  have hinside : ∀ i z, z ∈ (p' i).support →
      ‖HexTiling.planeMap (point z)‖ < P.outerRadius/P.mesh := by
    intro i z hz
    change z ∈ ((initial i).map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
    change ‖triangularEmbedding (x-P.center)‖ < P.outerRadius/P.mesh
    apply (lt_div_iff₀ P.mesh_pos).mpr
    have h := hin i x hx
    rw [P.radius_eq_mesh_norm] at h
    nlinarith
  have hends (i : Fin 4) :
      ‖HexTiling.planeMap (edgePoint (f (w i)) (f (b i)) (τ i))‖ = P.outerRadius/P.mesh :=
    contact_radius_normalized P (hτeq i) (hdist i)
  have hdis' : ∀ i j, i ≠ j → List.Disjoint ((p' i).concat (last' i)).support
      ((p' j).concat (last' j)).support := by
    intro i j hij z hzi hzj
    rw [←hmap,SimpleGraph.Walk.support_map] at hzi hzj
    obtain ⟨x,hx,hxe⟩ := List.mem_map.mp hzi
    obtain ⟨y,hy,hye⟩ := List.mem_map.mp hzj
    have hxy : x = y := centerGraph_injective P.center (hxe.trans hye.symm)
    exact hdis i j hij hx (hxy.symm ▸ hy)
  have harg (i : Fin 4) : Complex.arg (contact i-position P.mesh P.center) =
      Complex.arg (HexTiling.planeMap (edgePoint (f (w i)) (f (b i)) (τ i))) := by
    rw [hτeq]
    exact Complex.arg_real_mul _ P.mesh_pos
  have horder : CyclicAngles (fun i =>
      HexTiling.planeMap (edgePoint (f (w i)) (f (b i)) (τ i))) := by
    simpa only [CyclicAngles,harg] using hcyc.2
  have hS : 2*(r:ℝ) < P.outerRadius/P.mesh := by
    apply (lt_div_iff₀ P.mesh_pos).mpr
    have hrR' : (r:ℝ) < (R:ℝ) := by exact_mod_cast hrR
    nlinarith [P.mesh_pos]
  obtain ⟨s,t,q,hq,he,hbounds,hinner,houter,hd,hsorder,htorder⟩ :=
    circle_contacts_to_ordered_hex_paths orderInput r R (P.outerRadius/P.mesh) hr hrR hS
      (fun i => f (a i)) (fun i => f (w i)) (fun i => f (b i)) p' last' hp' τ hτ
      (fun i => (hcuts i).1) (fun i => (hcuts i).2) hinside hends hdis' horder
  refine ⟨s,t,q,fun i => (hq i).1,he,?_,hinner,houter,hd,hsorder,htorder⟩
  intro i z hz
  refine ⟨(hbounds i z hz).1,(hbounds i z hz).2,?_⟩
  have hzm := (hq i).2.support_subset hz
  rw [←hmap,SimpleGraph.Walk.support_map] at hzm
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hzm
  change ω ((x-P.center)+P.center) = _
  simpa only [sub_add_cancel] using (hcolor i x hx).2

#print axioms fourArms_ordered_hex_paths

end ExceptionalTimes.PairSquareSewing
