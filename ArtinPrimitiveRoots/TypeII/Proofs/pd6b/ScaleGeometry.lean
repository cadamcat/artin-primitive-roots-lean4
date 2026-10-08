import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.UnionLabels
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.GeometryTube

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

theorem dyadicScale_upper (x : ℝ) (K : ℕ) (Y : ℝ) (hY : Y ∈ dyadicScales x K) :
    0 < Y ∧ Y ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
  obtain ⟨hImage, hBounds⟩ := Finset.mem_filter.mp hY
  obtain ⟨k, hk, hkY⟩ := Finset.mem_image.mp hImage
  have hYpos : 0 < Y := by rw [← hkY]; positivity
  exact ⟨hYpos, (Real.exp_log hYpos).symm.trans_le (Real.exp_le_exp.mpr hBounds.2)⟩


theorem dyadicScale_one_le (x : ℝ) (K : ℕ) (Y : ℝ) (hY : Y ∈ dyadicScales x K) : 1 ≤ Y := by
  obtain ⟨hImage, hBounds⟩ := Finset.mem_filter.mp hY
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hImage
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem padScale_upper (x : ℝ) (K d₀ : ℕ) (hL : 0 ≤ Real.log x) (hd : d₀ ∈ padScales x K) :
    0 < d₀ ∧ (d₀ : ℝ) ≤ Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) *
      Real.rpow (Real.log x) (21 / 100 : ℝ)) := by
  obtain ⟨k, hk, hkD⟩ := Finset.mem_image.mp hd
  have hkBound : (k : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) := by
    have hkn : k ≤ ⌊((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)⌋₊ := by
      have h := Finset.mem_range.mp hk
      omega
    exact (Nat.le_floor_iff (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL _))).mp hkn
  have hDpos : 0 < d₀ := by rw [← hkD]; positivity
  have hlog : Real.log (d₀ : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [← hkD, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨hDpos, ?_⟩
  calc
    (d₀ : ℝ) = Real.exp (Real.log (d₀ : ℝ)) := (Real.exp_log (Nat.cast_pos.mpr hDpos)).symm
    _ = Real.exp ((k : ℝ) * Real.log 2) := by rw [hlog]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_right hkBound hlog2.le
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h)

theorem physicalLastProduct_upper {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hL : 1 ≤ Real.log S.x) (P : PState F S) :
    (lastProduct P.labels : ℝ) ≤ Real.exp (6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
  let f : Fin K → Fin 1 → ℕ := fun i j => P.labels i (lastSlot S.x)
  have hOne : 1 ≤ Real.rpow S.L (1 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hN : (1 : ℝ) ≤ 3 * Real.rpow S.L (1 / 100 : ℝ) := by linarith
  have hN' : ((1 : ℕ) : ℝ) ≤ 3 * Real.rpow (Real.log S.x) (1 / 100 : ℝ) := by
    simpa only [Nat.cast_one, PDScale.L] using hN
  have h := primeMatrixProduct_le_exp hF.1 hL hN' f (fun i j => P.label_in_band i (lastSlot S.x))
  simpa only [f, Fin.prod_univ_one, lastProduct, PDScale.L] using h

def physicalTubeRadius (x : ℝ) (K : ℕ) (R : ℝ) : ℝ :=
  16 + 2 * Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) *
    (2 * Real.exp (6 * (K : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) +
      R * Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ)))

/-- Every positive envelope edge lies in an explicit uniformly finite coordinate tube. -/
theorem physicalEnvelope_coordinates_le_radius {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    {δ c₁ c₂ : ℝ} (hS : S.Valid K δ c₁ c₂) (hU : 0 < S.U) (hL : 1 ≤ Real.log S.x)
    (R B : ℝ) (hR : 0 ≤ R) (P Q : PState F S) (h : 0 < physicalEnvelope F S R B P Q) :
    |((edgeCoordinates P Q).1 : ℝ)| ≤ physicalTubeRadius S.x K R ∧
      |((edgeCoordinates P Q).2 : ℝ)| ≤ physicalTubeRadius S.x K R := by
  have hY := dyadicScale_upper S.x K S.Y hS.2.2.2.2.2.1
  have hd := padScale_upper S.x K S.d₀ (by linarith [hL]) hS.2.2.2.2.2.2
  have hcond : IsSlotTransition P.labels Q.labels ∧
      IsPadAdmissible S.d₀ (sharedProduct P.labels) (det2 P.pos Q.pos) := by
    by_contra hnot
    simp [physicalEnvelope, hnot] at h
  have hDhi : (sharedProduct P.labels : ℝ) ≤ 2 * Real.exp
      (Real.log 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log S.x) (21 / 100 : ℝ)) :=
    hcond.2.2.1.le.trans (mul_le_mul_of_nonneg_left hd.2 (by norm_num))
  have hpLast := physicalLastProduct_upper F S hF hL P
  have hqLast := physicalLastProduct_upper F S hF hL Q
  have hsum : (lastProduct P.labels : ℝ) + (lastProduct Q.labels : ℝ) + R * S.Y ≤
      2 * Real.exp (6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) +
        R * Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log S.x) (1 / 5 : ℝ)) := by
    have hRY := mul_le_mul_of_nonneg_left hY.2 hR
    linarith
  have hz₂ := physicalEnvelope_positive_tube F S P Q R B hR hY.1 h
  have hRadiusPart : |((edgeCoordinates P Q).2 : ℝ)| ≤
      2 * Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log S.x) (21 / 100 : ℝ)) *
        (2 * Real.exp (6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) +
          R * Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log S.x) (1 / 5 : ℝ))) := by
    apply hz₂.trans
    exact mul_le_mul hDhi hsum
      (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg hR hY.1.le))
      (by positivity)
  have hz₁ := edgeCoordinates_first_abs_le F S hU P Q
  constructor
  · dsimp [physicalTubeRadius]
    change |((edgeCoordinates P Q).1 : ℝ)| ≤ 16 + _
    have hb := add_le_add (le_rfl : (16 : ℝ) ≤ 16) hRadiusPart
    exact hz₁.trans hb
  · dsimp [physicalTubeRadius]
    have hR0 : (0 : ℝ) ≤ 16 := by norm_num
    exact hRadiusPart.trans (le_add_of_nonneg_left hR0)


/-- The literal tube radius is subexponential with a fixed coefficient depending only on K,R. -/
theorem physicalTubeRadius_le_exp (x : ℝ) (K : ℕ) (R : ℝ) (hR : 0 < R) (hL : 1 ≤ Real.log x) :
    physicalTubeRadius x K R ≤
      Real.exp ((8 * ((K + 1 : ℕ) : ℝ) + |Real.log R| + 22) * Real.rpow (Real.log x) (21 / 100 : ℝ)) := by
  let q := Real.rpow (Real.log x) (21 / 100 : ℝ)
  let v := Real.rpow (Real.log x) (1 / 5 : ℝ)
  let A := 7 * ((K + 1 : ℕ) : ℝ) + |Real.log R|
  let B := ((K + 1 : ℕ) : ℝ) + A
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hq : 1 ≤ q := Real.one_le_rpow hL (by norm_num)
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hv : v ≤ q := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpad : Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) * q) ≤ Real.exp (((K + 1 : ℕ) : ℝ) * q) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hlog2
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) (K + 1)) hqPos.le)
    nlinarith
  have hfirst : Real.exp (6 * (K : ℝ) * q) ≤ Real.exp (A * q) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hqPos.le
    dsimp [A]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) K, abs_nonneg (Real.log R)]
  have hRbound : R ≤ Real.exp (|Real.log R| * q) := by
    calc
      R = Real.exp (Real.log R) := (Real.exp_log hR).symm
      _ ≤ _ := Real.exp_le_exp.mpr ((le_abs_self _).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (abs_nonneg _)))
  have hsecond : R * Real.exp (((K + 1 : ℕ) : ℝ) * v) ≤ Real.exp (A * q) := by
    calc
      _ ≤ Real.exp (|Real.log R| * q) * Real.exp (((K + 1 : ℕ) : ℝ) * q) :=
        mul_le_mul hRbound (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _)))
          (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((|Real.log R| + ((K + 1 : ℕ) : ℝ)) * q) := by rw [← Real.exp_add]; congr 1 <;> ring
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
        dsimp [A]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) K]) hqPos.le)
  have hsum : 2 * Real.exp (6 * (K : ℝ) * q) + R * Real.exp (((K + 1 : ℕ) : ℝ) * v) ≤ 3 * Real.exp (A * q) := by
    nlinarith
  have hproduct : 2 * Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) * q) *
      (2 * Real.exp (6 * (K : ℝ) * q) + R * Real.exp (((K + 1 : ℕ) : ℝ) * v)) ≤
      6 * Real.exp (B * q) := by
    calc
      _ ≤ (2 * Real.exp (((K + 1 : ℕ) : ℝ) * q)) * (3 * Real.exp (A * q)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpad (by norm_num)) hsum (by positivity) (by positivity)
      _ = _ := by
        dsimp [B]
        have heq : (((K + 1 : ℕ) : ℝ) + A) * q = ((K + 1 : ℕ) : ℝ) * q + A * q := by ring
        rw [heq, Real.exp_add]
        ring
  have hBexp : 1 ≤ Real.exp (B * q) := by
    apply Real.one_le_exp_iff.mpr
    dsimp [B, A]
    positivity
  have h22 : 22 ≤ Real.exp (22 * q) := by
    have h := Real.add_one_le_exp (22 * q)
    linarith
  calc
    physicalTubeRadius x K R = 16 + 2 * Real.exp (Real.log 2 * ((K + 1 : ℕ) : ℝ) * q) *
      (2 * Real.exp (6 * (K : ℝ) * q) + R * Real.exp (((K + 1 : ℕ) : ℝ) * v)) := rfl
    _ ≤ 16 + 6 * Real.exp (B * q) := by linarith
    _ ≤ 22 * Real.exp (B * q) := by nlinarith
    _ ≤ Real.exp (22 * q) * Real.exp (B * q) := mul_le_mul_of_nonneg_right h22 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; dsimp [B, A, q]; congr 1 <;> ring


theorem physicalTubeRadius_small_eventually (K : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → 1 ≤ Real.log x ∧
      physicalTubeRadius x K R ≤ Real.exp (Real.rpow (Real.log x) (1 / 2 : ℝ)) := by
  let C := 8 * ((K + 1 : ℕ) : ℝ) + |Real.log R| + 22
  have ht : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (29 / 100 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, C ≤ Real.rpow (Real.log x) (29 / 100 : ℝ) ∧ 1 ≤ Real.log x := by
    filter_upwards [ht.eventually_ge_atTop C, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hgap hL
    exact ⟨hgap, hL⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨hgap, hL⟩ := hx₁ x ((le_max_right _ _).trans hx)
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hprod : Real.rpow (Real.log x) (21 / 100 : ℝ) * Real.rpow (Real.log x) (29 / 100 : ℝ) =
      Real.rpow (Real.log x) (1 / 2 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) ((21 / 100 : ℝ) + (29 / 100 : ℝ)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by norm_num
  have hCpow : C * Real.rpow (Real.log x) (21 / 100 : ℝ) ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) := by
    have h : C * Real.rpow (Real.log x) (21 / 100 : ℝ) ≤
        Real.rpow (Real.log x) (29 / 100 : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hLpos.le (21 / 100 : ℝ))
    have heq : Real.rpow (Real.log x) (29 / 100 : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) =
        Real.rpow (Real.log x) (1 / 2 : ℝ) := (mul_comm _ _).trans hprod
    rwa [heq] at h
  exact ⟨hL, (physicalTubeRadius_le_exp x K R hR hL).trans (Real.exp_le_exp.mpr hCpow)⟩

end
end ArtinPrimitiveRoots.TypeII.PD
