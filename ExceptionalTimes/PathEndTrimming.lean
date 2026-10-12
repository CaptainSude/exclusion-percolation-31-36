import ExceptionalTimes.HexCutTrimming

open Set
open scoped Classical

namespace ExceptionalTimes.Annulus

/-- Choose the last departure from A on the entire input path. The
retained path is an actual suffix and keeps the original final endpoint.
This is stronger than merely choosing any proper A-to-B subpath. -/
theorem last_departure_suffix {V : Type*} {G : SimpleGraph V} {u v : V}
    (A : Set V) (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ A) :
    ∃ x ∈ A, ∃ q : G.Walk x v, ∃ initialPart : G.Walk u x,
      initialPart.append q = p ∧ q.IsPath ∧ q.IsSubwalk p ∧
        (∀ z ∈ q.support, z ∈ A → z = x) := by
  classical
  let eligible : ℕ → Prop := fun n =>
    ∃ x ∈ A, ∃ q : G.Walk x v, ∃ initialPart : G.Walk u x,
      q.length = n ∧ initialPart.append q = p
  have hex : ∃ n, eligible n := ⟨p.length,u,hu,p,.nil,rfl,by simp⟩
  obtain ⟨x,hx,q,initialPart,hlen,heq⟩ := Nat.find_spec hex
  have hsub : q.IsSubwalk p := SimpleGraph.Walk.isSubwalk_of_append_right heq.symm
  refine ⟨x,hx,q,initialPart,heq,SimpleGraph.Walk.isPath_of_isSubwalk hsub hp,hsub,?_⟩
  intro z hz hzA
  by_contra hne
  have hmin : Nat.find hex ≤ (q.dropUntil z hz).length :=
    Nat.find_min' hex ⟨z,hzA,q.dropUntil z hz,initialPart.append (q.takeUntil z hz),rfl,by
      rw [←SimpleGraph.Walk.append_assoc,q.take_spec]
      exact heq⟩
  have hlt := q.length_dropUntil_lt_length hz hne
  omega

/-- Choose the first arrival at B on the entire input path. The retained
path is an actual initialPart and keeps the original starting endpoint. -/
theorem first_arrival_prefix {V : Type*} {G : SimpleGraph V} {u v : V}
    (B : Set V) (p : G.Walk u v) (hp : p.IsPath) (hv : v ∈ B) :
    ∃ y ∈ B, ∃ q : G.Walk u y, ∃ suffix : G.Walk y v,
      q.append suffix = p ∧ q.IsPath ∧ q.IsSubwalk p ∧
        (∀ z ∈ q.support, z ∈ B → z = y) := by
  classical
  let eligible : ℕ → Prop := fun n =>
    ∃ y ∈ B, ∃ q : G.Walk u y, ∃ suffix : G.Walk y v,
      q.length = n ∧ q.append suffix = p
  have hex : ∃ n, eligible n := ⟨p.length,v,hv,p,.nil,rfl,by simp⟩
  obtain ⟨y,hy,q,suffix,hlen,heq⟩ := Nat.find_spec hex
  have hsub : q.IsSubwalk p := SimpleGraph.Walk.isSubwalk_of_append_left heq.symm
  refine ⟨y,hy,q,suffix,heq,SimpleGraph.Walk.isPath_of_isSubwalk hsub hp,hsub,?_⟩
  intro z hz hzB
  by_contra hne
  have hmin : Nat.find hex ≤ (q.takeUntil z hz).length :=
    Nat.find_min' hex ⟨z,hzB,q.takeUntil z hz,(q.dropUntil z hz).append suffix,rfl,by
      rw [SimpleGraph.Walk.append_assoc,q.take_spec]
      exact heq⟩
  have hlt := q.length_takeUntil_lt_length hz hne
  omega

/-- The exact suffix/initialPart choice required for order transfer: first
retain everything after the final visit to A, then stop at the first B
visit on that tail. The full retained tail is also recorded. -/
theorem last_departure_first_arrival {V : Type*} {G : SimpleGraph V} {u v : V}
    (A B : Set V) (p : G.Walk u v) (hp : p.IsPath) (hu : u ∈ A) (hv : v ∈ B) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ before : G.Walk u x, ∃ middle : G.Walk x y,
      ∃ after : G.Walk y v,
        before.append (middle.append after) = p ∧
        (middle.append after).IsPath ∧ (middle.append after).IsSubwalk p ∧
        middle.IsPath ∧ middle.IsSubwalk p ∧
        (∀ z ∈ (middle.append after).support, z ∈ A → z = x) ∧
        (∀ z ∈ middle.support, z ∈ B → z = y) := by
  obtain ⟨x,hx,tail,before,hbefore,htail,htailsub,hA⟩ := last_departure_suffix A p hp hu
  obtain ⟨y,hy,middle,after,hafter,hmid,hmidsub,hB⟩ := first_arrival_prefix B tail htail hv
  refine ⟨x,hx,y,hy,before,middle,after,?_,?_,?_,hmid,hmidsub.trans htailsub,?_,hB⟩
  · rwa [hafter]
  · rwa [hafter]
  · rwa [hafter]
  · rwa [hafter]

#print axioms last_departure_suffix
#print axioms first_arrival_prefix
#print axioms last_departure_first_arrival

/-- Integer-valued nearest-neighbor levels turn the exact global
last-departure/first-arrival choice into exact, proper level endpoints.
The full final tail stays outside the inner cut, which is the extra
certificate needed to compare its order with a later outer circle. -/
theorem last_departure_first_arrival_levels (f : Site → ℤ)
    (hstep : ∀ {u v}, TriangularAdj u v → f v ≤ f u+1)
    {u v : Site} (p : triangularGraph.Walk u v) (hp : p.IsPath)
    (r R : ℤ) (hrR : r < R) (hu : f u ≤ r) (hv : R ≤ f v) :
    ∃ x, f x = r ∧ ∃ y, f y = R ∧ ∃ before : triangularGraph.Walk u x,
      ∃ middle : triangularGraph.Walk x y, ∃ after : triangularGraph.Walk y v,
        before.append (middle.append after) = p ∧
        (middle.append after).IsPath ∧ (middle.append after).IsSubwalk p ∧
        middle.IsPath ∧ middle.IsSubwalk p ∧
        (∀ z ∈ (middle.append after).support, r ≤ f z ∧ (f z = r → z = x)) ∧
        (∀ z ∈ middle.support, f z ≤ R ∧ (f z = R → z = y)) := by
  obtain ⟨x,hx,y,hy,before,middle,after,heq,htail,hsub,hmid,hmsub,hA,hB⟩ :=
    last_departure_first_arrival {z | f z ≤ r} {z | R ≤ f z} p hp hu hv
  have hxn : x ≠ v := by
    intro h
    have he := congrArg f h
    change f x ≤ r at hx
    omega
  have hx' := PairSquareSewing.walk_start_level f hstep (middle.append after)
    (SimpleGraph.Walk.not_nil_of_ne hxn) r hx hA
  have hxyn : x ≠ y := by intro h; subst y; change R ≤ f x at hy; omega
  have hnegstep : ∀ {a b}, TriangularAdj a b → -f b ≤ -f a+1 := by
    intro a b hab
    have := hstep (triangularAdj_symm hab)
    omega
  have hrevproper : ∀ z ∈ middle.reverse.support, -f z ≤ -R → z = y := by
    intro z hz hzr
    apply hB z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
    change R ≤ f z
    omega
  have hyneg := PairSquareSewing.walk_start_level (fun z => -f z) hnegstep middle.reverse
    (SimpleGraph.Walk.not_nil_of_ne (Ne.symm hxyn)) (-R) (neg_le_neg hy)
    hrevproper
  have hy' : f y = R := by omega
  refine ⟨x,hx',y,hy',before,middle,after,heq,htail,hsub,hmid,hmsub,?_,?_⟩
  · intro z hz
    constructor
    · by_cases hzr : f z ≤ r
      · have he := hA z hz hzr
        rw [he,hx']
      · omega
    · exact fun he => hA z hz he.le
  · intro z hz
    constructor
    · by_cases hzR : R ≤ f z
      · have he := hB z hz hzR
        rw [he,hy']
      · omega
    · exact fun he => hB z hz he.ge

#print axioms last_departure_first_arrival_levels

end ExceptionalTimes.Annulus
