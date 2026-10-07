import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Density
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Endpoint damping absorbs the multiplicity of a promoted indexed hit. -/
theorem pd4c_index_damping (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h : ℕ) :
    (h : ℝ) * ρ ^ (h - 1) ≤ 1 / (1 - ρ) ^ 2 := by
  by_cases hh : h = 0
  · subst h
    simp only [Nat.cast_zero, zero_mul]
    exact one_div_nonneg.mpr (sq_nonneg _)
  have hnorm : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ1
  have hsum : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ρ ^ n) (1 / (1 - ρ) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hnorm
  have hterm := hsum.summable.le_tsum (h - 1)
    (fun n hn => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ0 n))
  rw [hsum.tsum_eq] at hterm
  have hpred : h - 1 + 1 = h := by omega
  simpa only [hpred] using hterm

/-- The same bound applies to all eligible indices, with repetitions retained. -/
theorem pd4c_hit_index_damping (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (l : List Particle) (z : ℤ × ℤ) :
    (∑ k : Fin l.length, if particleHits (l.get k) z then ρ ^ (hitCount l z - 1) else 0) ≤
      1 / (1 - ρ) ^ 2 := by
  classical
  rw [← Finset.sum_filter]
  simpa only [Finset.sum_const, nsmul_eq_mul, hitCount, hitIndices] using
    pd4c_index_damping ρ hρ0 hρ1 (hitCount l z)

/-- The index definition of hits agrees with counting the hitting entries of the list. -/
theorem pd4c_hitCount_eq_countP (l : List Particle) (z : ℤ × ℤ) :
    hitCount l z = l.countP (fun e => decide (particleHits e z)) := by
  classical
  have hmap : (List.finRange l.length).map l.get = l := by
    simpa only [List.ofFn_eq_map] using List.ofFn_get l
  have hAll : (List.finRange l.length).toFinset = (Finset.univ : Finset (Fin l.length)) := by
    ext k
    simp
  have h := (List.nodup_finRange l.length).card_eq_countP
    (P := fun k => particleHits (l.get k) z)
  rw [hAll] at h
  have hcount := congrArg (fun L : List Particle => L.countP (fun e => decide (particleHits e z))) hmap
  simp only [List.countP_map, Function.comp_def] at hcount
  exact h.trans hcount

private theorem pd4c_hit_sum (l : List Particle) (z : ℤ × ℤ) :
    (l.map (fun e => if particleHits e z then (1 : ℕ) else 0)).sum = hitCount l z := by
  rw [pd4c_hitCount_eq_countP]
  induction l with
  | nil => simp
  | cons e l ih =>
    by_cases h : particleHits e z <;> simp [h, ih, Nat.add_comm]

/-- One eligible indexed deletion removes one hit even when particles repeat. -/
theorem pd4c_hitCount_remove_singleton (l : List Particle) (z : ℤ × ℤ)
    (k : Fin l.length) (hk : particleHits (l.get k) z) :
    hitCount (removeIndices l {k}) z + 1 = hitCount l z := by
  classical
  let f : Particle → ℕ := fun e => if particleHits e z then 1 else 0
  have hmap : (List.finRange l.length).map l.get = l := by
    simpa only [List.ofFn_eq_map] using List.ofFn_get l
  have hwhole : ((List.finRange l.length).map (fun j => f (l.get j))).sum = hitCount l z := by
    have h := congrArg (fun L : List Particle => (L.map f).sum) hmap
    simpa only [List.map_map, Function.comp_def, f, pd4c_hit_sum] using h
  have hret : ((removeIndices l {k}).map f).sum =
      (((List.finRange l.length).filter (fun j => j ≠ k)).map (fun j => f (l.get j))).sum := by
    rw [pd4c_remove_filter_map]
    simp only [Finset.mem_singleton, List.map_map, Function.comp_def]
  have h := List.sum_map_filter_add_sum_map_filter_not (fun j : Fin l.length => j ≠ k)
    (fun j => f (l.get j)) (List.finRange l.length)
  rw [← hret, hwhole] at h
  have hk' : particleHits l[k.val] z := by simpa only [List.get_eq_getElem] using hk
  simpa [List.filter_eq, List.count_finRange, f, hk', pd4c_hit_sum] using h

theorem pd4c_hitCount_append (l m : List Particle) (z : ℤ × ℤ) :
    hitCount (l ++ m) z = hitCount l z + hitCount m z := by
  simp only [pd4c_hitCount_eq_countP, List.countP_append]

/-- Newly stored hits can only strengthen the outgoing promotion damping. -/
theorem pd4c_promotion_target_damping (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (l m : List Particle) (z : ℤ × ℤ) (k : Fin l.length)
    (hk : particleHits (l.get k) z) :
    ρ ^ hitCount (removeIndices l {k} ++ m) z ≤ ρ ^ (hitCount l z - 1) := by
  have hdel := pd4c_hitCount_remove_singleton l z k hk
  have hlen : hitCount l z - 1 = hitCount (removeIndices l {k}) z := by omega
  rw [pd4c_hitCount_append, hlen]
  exact pow_le_pow_of_le_one hρ0 hρ1 (Nat.le_add_right _ _)

end

end ArtinPrimitiveRoots.TypeII.PD
