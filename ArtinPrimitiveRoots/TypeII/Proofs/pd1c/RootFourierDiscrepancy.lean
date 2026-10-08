import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootKloostermanBound
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootCoefficientSums

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd1c_two_direction_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : ι) (df dg gp : ι → ℝ) (H : ι → ι → ℝ) (B : ℝ)
    (hdf : ∀ h, 0 ≤ df h) (hdg : ∀ k, 0 ≤ dg k)
    (hL : ∀ h k, H h k ≤ B * gp h) (hR : ∀ h k, H h k ≤ B * gp k) :
    (∑ h : ι, ∑ k : ι, if h = o ∧ k = o then 0 else df h * dg k * H h k) ≤
      B * (∑ h : ι, if h = o then 0 else df h * gp h) * (∑ k : ι, dg k) +
        B * df o * (∑ k : ι, if k = o then 0 else dg k * gp k) := by
  have hpoint : ∀ h k : ι,
      (if h = o ∧ k = o then 0 else df h * dg k * H h k) ≤
      (if h = o then 0 else B * df h * gp h * dg k) +
      (if h = o then (if k = o then 0 else B * df o * dg k * gp k) else 0) := by
    intro h k
    by_cases hh : h = o
    · subst h
      by_cases hk : k = o
      · simp [hk]
      · simp only [hk, and_false, ite_false, ite_true, zero_add]
        exact (mul_le_mul_of_nonneg_left (hR o k) (mul_nonneg (hdf o) (hdg k))).trans_eq (by ring)
    · simp only [hh, false_and, ite_false, add_zero]
      exact (mul_le_mul_of_nonneg_left (hL h k) (mul_nonneg (hdf h) (hdg k))).trans_eq (by ring)
  have hFirst : (∑ h : ι, ∑ k : ι, if h = o then 0 else B * df h * gp h * dg k) =
      B * (∑ h : ι, if h = o then 0 else df h * gp h) * (∑ k : ι, dg k) := by
    conv_rhs => rw [mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    by_cases ho : h = o <;> simp [ho] <;> ring
  have hSecond : (∑ h : ι, ∑ k : ι, if h = o then (if k = o then 0 else B * df o * dg k * gp k) else 0) =
      B * df o * (∑ k : ι, if k = o then 0 else dg k * gp k) := by
    rw [Finset.sum_eq_single o]
    · simp only [ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases ko : k = o <;> simp [ko] <;> ring
    · intro h hh hne
      simp [hne]
    · simp
  calc
    _ ≤ ∑ h : ι, ∑ k : ι,
      ((if h = o then 0 else B * df h * gp h * dg k) +
        (if h = o then (if k = o then 0 else B * df o * dg k * gp k) else 0)) :=
      Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpoint h k
    _ = _ := by simp only [Finset.sum_add_distrib]; rw [hFirst, hSecond]

lemma pd1c_density_fourier_discrepancy (m u ac Nc av Nv : ℕ)
    (hm : 0 < m) (hu : 0 < u) (hdiv : u ∣ m) (hNc : Nc ≤ m) [NeZero m]
    (G : Finset (ZMod m × ZMod m)) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ h k : ZMod m, ‖pd1c_rootGraphTransform m G h k‖ ≤
      B * (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ))
    (hR : ∀ h k : ZMod m, ‖pd1c_rootGraphTransform m G h k‖ ≤
      B * (Nat.gcd k.val u : ℝ) ^ (1 / 4 : ℝ)) :
    ‖(∑ z ∈ G, pd1c_rootIntervalDensity m ac Nc z.1 * pd1c_rootIntervalDensity m av Nv z.2) -
      (G.card : ℂ) * (Nc : ℂ) * (Nv : ℂ) / (m : ℂ) ^ 2‖ ≤
      4 * B * (u.divisors.card : ℝ) * (1 + Real.log (m : ℝ)) *
        ((Nv : ℝ) / m + 5 * (1 + Real.log (m : ℝ))) := by
  let fc := pd1c_rootIntervalDensity m ac Nc
  let fv := pd1c_rootIntervalDensity m av Nv
  let df := fun h : ZMod m => ‖pd1c_rootDFT m fc h‖
  let dg := fun k : ZMod m => ‖pd1c_rootDFT m fv k‖
  let gp := fun h : ZMod m => (Nat.gcd h.val u : ℝ) ^ (1 / 4 : ℝ)
  let H := fun h k : ZMod m => ‖pd1c_rootGraphTransform m G h k‖
  let L := 1 + Real.log (m : ℝ)
  let T := (u.divisors.card : ℝ)
  have hLp : 1 ≤ L := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp [L]
    linarith [Real.log_nonneg hmR]
  have hLnonneg : 0 ≤ L := by linarith
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hdf : ∀ h : ZMod m, 0 ≤ df h := fun h => norm_nonneg _
  have hdg : ∀ k : ZMod m, 0 ≤ dg k := fun k => norm_nonneg _
  have hfw : (∑ h : ZMod m, if h = 0 then 0 else df h * gp h) ≤ 4 * T * L :=
    pd1c_nonzero_coefficient_gcd_sum m u ac Nc hm hu hdiv
  have hgw : (∑ k : ZMod m, if k = 0 then 0 else dg k * gp k) ≤ 4 * T * L :=
    pd1c_nonzero_coefficient_gcd_sum m u av Nv hm hu hdiv
  have hgSum : (∑ k : ZMod m, dg k) ≤ (Nv : ℝ) / m + 4 * L := pd1c_coefficient_sum m av Nv hm
  have hfZero : df 0 ≤ 1 := by
    dsimp only [df, fc]
    rw [pd1c_rootIntervalDensity_zero_norm]
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    exact (div_le_one hmR).mpr (by exact_mod_cast hNc)
  have hfSumNonneg : 0 ≤ ∑ h : ZMod m, if h = 0 then 0 else df h * gp h :=
    Finset.sum_nonneg (fun h hh => by
      by_cases hz : h = 0
      · simp [hz]
      · rw [if_neg hz]
        exact mul_nonneg (hdf h) (Real.rpow_nonneg (Nat.cast_nonneg (Nat.gcd h.val u)) (1 / 4 : ℝ)))
  have hgSumNonneg : 0 ≤ ∑ k : ZMod m, if k = 0 then 0 else dg k * gp k :=
    Finset.sum_nonneg (fun k hk => by
      by_cases hz : k = 0
      · simp [hz]
      · rw [if_neg hz]
        exact mul_nonneg (hdg k) (Real.rpow_nonneg (Nat.cast_nonneg (Nat.gcd k.val u)) (1 / 4 : ℝ)))
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hMain : pd1c_rootDFT m fc 0 * pd1c_rootDFT m fv 0 * (G.card : ℂ) =
      (G.card : ℂ) * (Nc : ℂ) * (Nv : ℂ) / (m : ℂ) ^ 2 := by
    rw [pd1c_rootIntervalDensity_zero, pd1c_rootIntervalDensity_zero]
    ring
  rw [← hMain]
  calc
    _ ≤ ∑ h : ZMod m, ∑ k : ZMod m,
      if h = 0 ∧ k = 0 then 0 else df h * dg k * H h k := pd1c_root_graph_fourier_error m G fc fv
    _ ≤ B * (∑ h : ZMod m, if h = 0 then 0 else df h * gp h) * (∑ k : ZMod m, dg k) +
        B * df 0 * (∑ k : ZMod m, if k = 0 then 0 else dg k * gp k) :=
      pd1c_two_direction_sum_bound 0 df dg gp H B hdf hdg hL hR
    _ ≤ B * (4 * T * L) * ((Nv : ℝ) / m + 4 * L) + B * 1 * (4 * T * L) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hfw hB) hgSum
          (Finset.sum_nonneg (fun k hk => hdg k)) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hfZero hB) hgw hgSumNonneg (by simpa using hB)
    _ ≤ 4 * B * T * L * ((Nv : ℝ) / m + 5 * L) := by
      have hcoef : 0 ≤ 4 * B * T * L := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hLp hcoef]

end ArtinPrimitiveRoots.TypeII.PD
