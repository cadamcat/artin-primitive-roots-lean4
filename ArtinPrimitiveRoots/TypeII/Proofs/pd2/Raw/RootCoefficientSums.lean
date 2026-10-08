import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootWeightedFrequency
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootIntervalDensity

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_zmod_sum_val (m : ℕ) [NeZero m] (F : ℕ → ℝ) :
    (∑ h : ZMod m, F h.val) = ∑ n ∈ Finset.range m, F n := by
  have hval : ∀ n : Fin m, (ZMod.finEquiv m n).val = n.val := by
    intro n
    cases m with
    | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
    | succ m => rfl
  calc
    _ = ∑ n : Fin m, F (ZMod.finEquiv m n).val := (ZMod.finEquiv m).sum_comp (fun h => F h.val) |>.symm
    _ = ∑ n : Fin m, F n.val := by simp only [hval]
    _ = _ := Fin.sum_univ_eq_sum_range F m

lemma pd2a_zmod_val_zero_iff (m : ℕ) [NeZero m] (h : ZMod m) : h.val = 0 ↔ h = 0 := by
  constructor
  · intro hz
    have hc := ZMod.natCast_zmod_val h
    rw [hz, Nat.cast_zero] at hc
    exact hc.symm
  · intro hz
    simp [hz]

lemma pd2a_range_nonzero_sum (m : ℕ) (hm : 0 < m) (F : ℕ → ℝ) :
    (∑ n ∈ Finset.range m, if n = 0 then 0 else F n) = ∑ n ∈ Finset.Icc 1 (m - 1), F n := by
  have hSet : Finset.range m = insert 0 (Finset.Icc 1 (m - 1)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hSet, Finset.sum_insert (by simp), if_pos rfl, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hb := Finset.mem_Icc.mp hn
  exact if_neg (by omega)

lemma pd2a_nonzero_coefficient_gcd_sum (m u a N : ℕ) (hm : 0 < m) (hu : 0 < u) (hdiv : u ∣ m)
    [NeZero m] :
    (∑ h : ZMod m, if h = 0 then (0 : ℝ) else
      ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖ * (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ)) ≤
      4 * (u.divisors.card : ℝ) * (1 + Real.log (m : ℝ)) := by
  have hpoint : ∀ h : ZMod m,
      (if h = 0 then (0 : ℝ) else ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖ * (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ)) ≤
      if h.val = 0 then 0 else 2 * ((Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ) / (min h.val (m - h.val) : ℕ)) := by
    intro h
    by_cases hh : h = 0
    · simp [hh]
    · have hv : h.val ≠ 0 := fun hn => hh ((pd2a_zmod_val_zero_iff m h).mp hn)
      rw [if_neg hh, if_neg hv]
      have hb := mul_le_mul_of_nonneg_right (pd2a_rootIntervalDensity_coefficient_bound m a N h hh)
        (Real.rpow_nonneg (Nat.cast_nonneg (Nat.gcd h.val u)) (1 / 4 : ℝ))
      exact hb.trans_eq (by ring)
  calc
    _ ≤ ∑ h : ZMod m, if h.val = 0 then 0 else 2 * ((Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ) / (min h.val (m - h.val) : ℕ)) :=
      Finset.sum_le_sum (fun h hh => hpoint h)
    _ = ∑ n ∈ Finset.range m, if n = 0 then 0 else 2 * ((Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (min n (m - n) : ℕ)) :=
      pd2a_zmod_sum_val m (fun n => if n = 0 then 0 else 2 * ((Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (min n (m - n) : ℕ)))
    _ = 2 * ∑ n ∈ Finset.Icc 1 (m - 1), (Nat.gcd n u : ℝ) ^ (1 / 4 : ℝ) / (min n (m - n) : ℕ) := by
      rw [pd2a_range_nonzero_sum m hm, Finset.mul_sum]
    _ ≤ 2 * (2 * (u.divisors.card : ℝ) * (1 + Real.log (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (pd2a_min_frequency_gcd_sum m u hm hu hdiv) (by norm_num)
    _ = _ := by ring

lemma pd2a_nonzero_coefficient_sum (m a N : ℕ) (hm : 0 < m) [NeZero m] :
    (∑ h : ZMod m, if h = 0 then (0 : ℝ) else ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖) ≤
      4 * (1 + Real.log (m : ℝ)) := by
  simpa using pd2a_nonzero_coefficient_gcd_sum m 1 a N hm (by norm_num) (one_dvd m)

lemma pd2a_coefficient_sum (m a N : ℕ) (hm : 0 < m) [NeZero m] :
    (∑ h : ZMod m, ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖) ≤
      (N : ℝ) / m + 4 * (1 + Real.log (m : ℝ)) := by
  let F := fun h : ZMod m => ‖pd2a_rootDFT m (pd2a_rootIntervalDensity m a N) h‖
  have hsplit : (∑ h : ZMod m, F h) = F 0 + ∑ h : ZMod m, if h = 0 then 0 else F h := by
    calc
      _ = ∑ h : ZMod m, ((if h = 0 then F 0 else 0) + (if h = 0 then 0 else F h)) := by
        apply Finset.sum_congr rfl
        intro h hh
        by_cases hz : h = 0 <;> simp [hz]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit]
  exact add_le_add (by dsimp only [F]; rw [pd2a_rootIntervalDensity_zero_norm]) (pd2a_nonzero_coefficient_sum m a N hm)

end ArtinPrimitiveRoots.TypeII.PD
