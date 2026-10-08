import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Per-group memory density, including the factorial normalization. -/
def pd4c_listDensity (ν : Particle → ℝ) (l : List Particle) : ℝ :=
  (l.map ν).prod / (l.length.factorial : ℝ)

theorem pd4c_remove_filter_map (l : List Particle) (D : Finset (Fin l.length)) :
    removeIndices l D = ((List.finRange l.length).filter (fun j => j ∉ D)).map l.get := by
  classical
  unfold removeIndices
  calc
    _ = (List.finRange l.length).filterMap
        (fun k => if decide (k ∉ D) then some (l.get k) else none) := by
      apply List.filterMap_congr
      intro k hk
      by_cases h : k ∈ D <;> simp [h]
    _ = _ := by
      rw [← List.filterMap_filter (p := fun k => decide (k ∉ D))
        (f := fun k => some (l.get k))]
      simp [List.filterMap_eq_map]

/-- Deleting one indexed particle removes exactly its density factor. -/
theorem pd4c_remove_singleton_prod (ν : Particle → ℝ) (l : List Particle) (k : Fin l.length) :
    ((removeIndices l {k}).map ν).prod * ν (l.get k) = (l.map ν).prod := by
  classical
  have hmap : (List.finRange l.length).map l.get = l := by
    simpa only [List.ofFn_eq_map] using List.ofFn_get l
  have h := List.prod_map_filter_mul_prod_map_filter_not (fun j : Fin l.length => j ≠ k)
    (fun j => ν (l.get j)) (List.finRange l.length)
  have hwhole : ((List.finRange l.length).map (fun j => ν (l.get j))).prod = (l.map ν).prod := by
    simpa only [List.map_map, Function.comp_def] using congrArg (fun L => (L.map ν).prod) hmap
  rw [hwhole] at h
  rw [pd4c_remove_filter_map]
  simpa [List.filter_eq, List.count_finRange, List.map_map, Function.comp_def] using h

/-- Indexed deletion decreases length by exactly one, including with repeated particles. -/
theorem pd4c_remove_singleton_length (l : List Particle) (k : Fin l.length) :
    (removeIndices l {k}).length + 1 = l.length := by
  classical
  have hNot : (fun j : Fin l.length => !(decide (j ≠ k))) = fun j => decide (j = k) := by
    funext j
    by_cases h : j = k <;> simp [h]
  have h := List.length_eq_length_filter_add (l := List.finRange l.length)
    (fun j => decide (j ≠ k))
  rw [hNot] at h
  rw [pd4c_remove_filter_map]
  simpa [List.filter_eq, List.count_finRange] using h.symm

/-- Appending a stored particle has the creation factor `1/(n+1)`. -/
theorem pd4c_listDensity_append (ν : Particle → ℝ) (l : List Particle) (e : Particle) :
    ((l.length + 1 : ℕ) : ℝ) * pd4c_listDensity ν (l ++ [e]) =
      ν e * pd4c_listDensity ν l := by
  unfold pd4c_listDensity
  simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
    List.length_append, List.length_singleton, Nat.factorial_succ, Nat.cast_mul]
  have hn : ((l.length + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l.length
  have hf : (l.length.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l.length
  field_simp [hn, hf]

/-- Removing a promoted index has the annihilation factor `1/n`. -/
theorem pd4c_listDensity_remove (ν : Particle → ℝ) (l : List Particle) (k : Fin l.length) :
    (l.length : ℝ) * pd4c_listDensity ν l =
      ν (l.get k) * pd4c_listDensity ν (removeIndices l {k}) := by
  have hlen := (pd4c_remove_singleton_length l k).symm
  have hprod := pd4c_remove_singleton_prod ν l k
  unfold pd4c_listDensity
  have hfac : (l.length.factorial : ℝ) =
      (((removeIndices l {k}).length + 1 : ℕ) : ℝ) *
        ((removeIndices l {k}).length.factorial : ℝ) := by
    calc
      (l.length.factorial : ℝ) = (((removeIndices l {k}).length + 1).factorial : ℝ) :=
        congrArg (fun n : ℕ => (n.factorial : ℝ)) hlen
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]
  have hlenR : (l.length : ℝ) = (((removeIndices l {k}).length + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlen
  rw [← hprod, hfac, hlenR]
  have hn : (((removeIndices l {k}).length + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (removeIndices l {k}).length
  have hf : ((removeIndices l {k}).length.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (removeIndices l {k}).length
  field_simp [hn, hf]

/-- Creation may be put at the front when the continuation is symmetric. -/
theorem pd4c_listDensity_cons (ν : Particle → ℝ) (l : List Particle) (e : Particle) :
    ((l.length + 1 : ℕ) : ℝ) * pd4c_listDensity ν (e :: l) =
      ν e * pd4c_listDensity ν l := by
  unfold pd4c_listDensity
  simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.factorial_succ, Nat.cast_mul]
  have hn : ((l.length + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l.length
  have hf : (l.length.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l.length
  field_simp [hn, hf]

end

end ArtinPrimitiveRoots.TypeII.PD
