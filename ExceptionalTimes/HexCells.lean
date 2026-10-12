import ExceptionalTimes.LatticeEmbedding
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact

/-! Literal closed hexagons in axial coordinates. The ordinary triangular
embedding sends these polygons to the regular hexagonal percolation cells.
Cell intersection is proved to give exactly the six-neighbor graph. -/

namespace ExceptionalTimes.HexCells

open Set

def center (u : Site) : ℝ × ℝ := ((u.1 : ℝ), (u.2 : ℝ))

def cell (u : Site) : Set (ℝ × ℝ) := {p |
    2 * p.1 + p.2 ∈ Icc (2 * u.1 + u.2 - 1 : ℝ) (2 * u.1 + u.2 + 1) ∧
    p.1 + 2 * p.2 ∈ Icc (u.1 + 2 * u.2 - 1 : ℝ) (u.1 + 2 * u.2 + 1) ∧
    p.1 - p.2 ∈ Icc (u.1 - u.2 - 1 : ℝ) (u.1 - u.2 + 1)}

theorem center_mem_cell (u : Site) : center u ∈ cell u := by
  dsimp [cell, center]
  constructor
  · constructor <;> linarith
  · constructor <;> constructor <;> linarith

theorem isClosed_cell (u : Site) : IsClosed (cell u) := by
  exact ((isClosed_Icc.preimage (by fun_prop : Continuous (fun p : ℝ × ℝ => 2*p.1+p.2))).inter
    ((isClosed_Icc.preimage (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1+2*p.2))).inter
      (isClosed_Icc.preimage (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1-p.2)))))

theorem convex_slab (a b lo hi : ℝ) :
    Convex ℝ {p : ℝ × ℝ | a * p.1 + b * p.2 ∈ Icc lo hi} := by
  apply (convex_Icc lo hi).is_linear_preimage
  change IsLinearMap ℝ (fun p : ℝ × ℝ => a * p.1 + b * p.2)
  constructor
  · intro p q
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · intro c p
    change a * (c * p.1) + b * (c * p.2) = c * (a * p.1 + b * p.2)
    ring

theorem convex_cell (u : Site) : Convex ℝ (cell u) := by
  have h := (convex_slab 2 1 (2*u.1+u.2-1) (2*u.1+u.2+1)).inter
    ((convex_slab 1 2 (u.1+2*u.2-1) (u.1+2*u.2+1)).inter
      (convex_slab 1 (-1) (u.1-u.2-1) (u.1-u.2+1)))
  simpa only [cell, Set.ofPred_and, one_mul, neg_one_mul, sub_eq_add_neg] using h

theorem coordinate_bounds {u : Site} {p : ℝ × ℝ} (hp : p ∈ cell u) :
    |p.1 - u.1| ≤ 2/3 ∧ |p.2 - u.2| ≤ 2/3 := by
  rcases hp with ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem isCompact_cell (u : Site) : IsCompact (cell u) := by
  apply (isCompact_Icc (a := (u.1 : ℝ)-1) (b := u.1+1)).prod
    (isCompact_Icc (a := (u.2 : ℝ)-1) (b := u.2+1)) |>.of_isClosed_subset (isClosed_cell u)
  intro p hp
  obtain ⟨hx, hy⟩ := coordinate_bounds hp
  rw [abs_le] at hx hy
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem intersection_only_neighbors {u v : Site} {p : ℝ × ℝ}
    (hu : p ∈ cell u) (hv : p ∈ cell v) : u = v ∨ TriangularAdj u v := by
  rcases hu with ⟨⟨ha, ha'⟩, ⟨hb, hb'⟩, ⟨hc, hc'⟩⟩
  rcases hv with ⟨⟨hd, hd'⟩, ⟨he, he'⟩, ⟨hf, hf'⟩⟩
  have h1 : (-2 : ℤ) ≤ 2 * (u.1-v.1) + (u.2-v.2) := by
    exact_mod_cast (show (-2 : ℝ) ≤ 2 * ((u.1 : ℝ)-v.1) + ((u.2 : ℝ)-v.2) by linarith)
  have h2 : 2 * (u.1-v.1) + (u.2-v.2) ≤ (2 : ℤ) := by
    exact_mod_cast (show 2 * ((u.1 : ℝ)-v.1) + ((u.2 : ℝ)-v.2) ≤ (2 : ℝ) by linarith)
  have h3 : (-2 : ℤ) ≤ (u.1-v.1) + 2 * (u.2-v.2) := by
    exact_mod_cast (show (-2 : ℝ) ≤ ((u.1 : ℝ)-v.1) + 2 * ((u.2 : ℝ)-v.2) by linarith)
  have h4 : (u.1-v.1) + 2 * (u.2-v.2) ≤ (2 : ℤ) := by
    exact_mod_cast (show ((u.1 : ℝ)-v.1) + 2 * ((u.2 : ℝ)-v.2) ≤ (2 : ℝ) by linarith)
  have h5 : (-2 : ℤ) ≤ (u.1-v.1) - (u.2-v.2) := by
    exact_mod_cast (show (-2 : ℝ) ≤ ((u.1 : ℝ)-v.1) - ((u.2 : ℝ)-v.2) by linarith)
  have h6 : (u.1-v.1) - (u.2-v.2) ≤ (2 : ℤ) := by
    exact_mod_cast (show ((u.1 : ℝ)-v.1) - ((u.2 : ℝ)-v.2) ≤ (2 : ℝ) by linarith)
  by_cases h : u = v
  · exact Or.inl h
  · right
    have hne : u.1 ≠ v.1 ∨ u.2 ≠ v.2 := by
      by_contra hh
      push Not at hh
      exact h (Prod.ext hh.1 hh.2)
    unfold TriangularAdj
    omega

theorem midpoint_mem_of_adj {u v : Site} (h : TriangularAdj u v) :
    (((u.1 : ℝ) + v.1) / 2, ((u.2 : ℝ) + v.2) / 2) ∈ cell u := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  dsimp [TriangularAdj] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [cell, mem_ofPred, mem_Icc, Int.cast_add, Int.cast_sub, Int.cast_one]
  all_goals repeat' constructor
  all_goals linarith

theorem cell_inter_nonempty_iff (u v : Site) :
    (cell u ∩ cell v).Nonempty ↔ u = v ∨ TriangularAdj u v := by
  constructor
  · rintro ⟨p, hp, hq⟩
    exact intersection_only_neighbors hp hq
  · rintro (rfl | h)
    · exact ⟨center u, center_mem_cell u, center_mem_cell u⟩
    · refine ⟨(((u.1 : ℝ) + v.1) / 2, ((u.2 : ℝ) + v.2) / 2), midpoint_mem_of_adj h, ?_⟩
      simpa only [add_comm] using midpoint_mem_of_adj (triangularAdj_symm h)

end ExceptionalTimes.HexCells

#print axioms ExceptionalTimes.HexCells.cell_inter_nonempty_iff
