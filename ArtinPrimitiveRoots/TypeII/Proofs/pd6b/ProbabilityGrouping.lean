import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GroupedCounting

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- Finite grouping separates the probability-weighted model from the unweighted grid error. -/
theorem probability_grouping_upper {α κ ζ : Type*} [DecidableEq α] [DecidableEq κ] [DecidableEq ζ]
    (S : Finset α) (L : Finset κ) (Z : Finset ζ) (key : α → κ × ζ)
    (hkey : ∀ x ∈ S, key x ∈ L ×ˢ Z) (f : α → ℝ) (w : κ → ℝ) (h m : κ → ζ → ℝ)
    (μ U b E N H M : ℝ) (hU : 0 ≤ U) (hb : 0 ≤ b) (hE : 0 ≤ E) (hN : 0 ≤ N)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hw : ∀ k ∈ L, 0 ≤ w k) (hwsum : ∑ k ∈ L, w k ≤ 1)
    (hh : ∀ k ∈ L, ∀ z ∈ Z, 0 ≤ h k z ∧ h k z ≤ H)
    (hmodel : ∀ k ∈ L, ∑ z ∈ Z, m k z * h k z ≤ M)
    (hfiber : ∀ k ∈ L, ∀ z ∈ Z,
      μ * (∑ x ∈ S.filter (fun x => key x = (k, z)), f x) ≤
        U * w k * (27 * m k z * h k z + b * h k z) + E * N * h k z) :
    μ * (∑ x ∈ S, f x) ≤
      U * (27 * M + b * (Z.card : ℝ) * H) + E * N * (L.card : ℝ) * (Z.card : ℝ) * H := by
  have hsum : ∑ x ∈ S, f x = ∑ k ∈ L, ∑ z ∈ Z, ∑ x ∈ S.filter (fun x => key x = (k, z)), f x := by
    calc
      _ = ∑ kz ∈ L ×ˢ Z, ∑ x ∈ S.filter (fun x => key x = kz), f x :=
        (Finset.sum_fiberwise_of_maps_to hkey f).symm
      _ = _ := Finset.sum_product _ _ _
  have hHs (k : κ) (hk : k ∈ L) : ∑ z ∈ Z, h k z ≤ (Z.card : ℝ) * H := by
    calc
      _ ≤ ∑ z ∈ Z, H := Finset.sum_le_sum (fun z hz => (hh k hk z hz).2)
      _ = _ := by simp [nsmul_eq_mul]
  have hinner (k : κ) (hk : k ∈ L) :
      (∑ z ∈ Z, (U * w k * (27 * m k z * h k z + b * h k z) + E * N * h k z)) ≤
        U * w k * (27 * M + b * ((Z.card : ℝ) * H)) + E * N * ((Z.card : ℝ) * H) := by
    have hUw := mul_nonneg hU (hw k hk)
    have hEN := mul_nonneg hE hN
    have hbH := mul_le_mul_of_nonneg_left (hHs k hk) hb
    have hMH := mul_le_mul_of_nonneg_left (hmodel k hk) (by norm_num : (0 : ℝ) ≤ 27)
    have hmodel' := mul_le_mul_of_nonneg_left (add_le_add hMH hbH) hUw
    have herr' := mul_le_mul_of_nonneg_left (hHs k hk) hEN
    calc
      _ = U * w k * (27 * (∑ z ∈ Z, m k z * h k z) + b * (∑ z ∈ Z, h k z)) +
          E * N * (∑ z ∈ Z, h k z) := by
        have hf (z : ζ) : U * w k * (27 * m k z * h k z + b * h k z) + E * N * h k z =
            (U * w k * 27) * (m k z * h k z) + (U * w k * b) * h k z + (E * N) * h k z := by ring
        simp_rw [hf, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ ≤ _ := add_le_add hmodel' herr'
  have hmodel0 : 0 ≤ 27 * M + b * ((Z.card : ℝ) * H) := by positivity
  have hdist : μ * (∑ k ∈ L, ∑ z ∈ Z, ∑ x ∈ S.filter (fun x => key x = (k, z)), f x) =
      ∑ k ∈ L, ∑ z ∈ Z, μ * (∑ x ∈ S.filter (fun x => key x = (k, z)), f x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact Finset.mul_sum _ _ _
  rw [hsum, hdist]
  calc
    _ ≤ ∑ k ∈ L, ∑ z ∈ Z,
        (U * w k * (27 * m k z * h k z + b * h k z) + E * N * h k z) :=
      Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun z hz => hfiber k hk z hz))
    _ ≤ ∑ k ∈ L,
        (U * w k * (27 * M + b * ((Z.card : ℝ) * H)) + E * N * ((Z.card : ℝ) * H)) :=
      Finset.sum_le_sum hinner
    _ = U * (∑ k ∈ L, w k) * (27 * M + b * ((Z.card : ℝ) * H)) +
        (L.card : ℝ) * (E * N * ((Z.card : ℝ) * H)) := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ U * 1 * (27 * M + b * ((Z.card : ℝ) * H)) +
        (L.card : ℝ) * (E * N * ((Z.card : ℝ) * H)) := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwsum hU) hmodel0
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
