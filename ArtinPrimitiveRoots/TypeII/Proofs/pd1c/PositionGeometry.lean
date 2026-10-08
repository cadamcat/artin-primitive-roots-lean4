import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

set_option maxHeartbeats 1000000

lemma pd1c_det_line_repr (u v u₀ v₀ c d e : ℤ)
    (hOne : u₀ * d - v₀ * c = 1) (hDet : u₀ * v - v₀ * u = e) :
    u = u₀ * (d * u - c * v) + c * e ∧
      v = v₀ * (d * u - c * v) + d * e := by
  constructor
  · linear_combination -u * hOne + c * hDet
  · linear_combination -v * hOne + d * hDet

lemma pd1c_det_line_card (s : Finset (ℕ × ℕ)) (U : ℝ) (hU : 0 < U)
    (u₀ v₀ : ℕ) (hu₀ : U ≤ (u₀ : ℝ)) (hcop : Nat.Coprime u₀ v₀) (e : ℤ)
    (hs : ∀ z ∈ s, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16 * U ∧
      (u₀ : ℤ) * (z.2 : ℤ) - (v₀ : ℤ) * (z.1 : ℤ) = e) :
    s.card ≤ 17 := by
  have hu₀pos : 0 < u₀ := by exact_mod_cast (hU.trans_le hu₀)
  have hu₀R : 0 < (u₀ : ℝ) := hU.trans_le hu₀
  obtain ⟨c, d, hOne, hc0, hc1⟩ := pd1c_root_completion_exists u₀ v₀ hu₀pos hcop
  let q (z : ℕ × ℕ) : ℤ := d * (z.1 : ℤ) - c * (z.2 : ℤ)
  let L : ℝ := (U - (c : ℝ) * (e : ℝ)) / (u₀ : ℝ)
  let k : ℤ := ⌊L⌋
  have hqBound : ∀ z ∈ s, 0 ≤ q z - k ∧ q z - k < 17 := by
    intro z hz
    obtain ⟨hlo, hhi, hDet⟩ := hs z hz
    have hrepr := (pd1c_det_line_repr (z.1 : ℤ) (z.2 : ℤ)
      u₀ v₀ c d e hOne hDet).1
    have hreprR : (z.1 : ℝ) = (u₀ : ℝ) * (q z : ℝ) + (c : ℝ) * (e : ℝ) := by
      exact_mod_cast hrepr
    have hloq : L ≤ (q z : ℝ) := by
      apply (div_le_iff₀ hu₀R).mpr
      nlinarith [hlo, hreprR]
    have hhiq : (q z : ℝ) ≤ L + 15 := by
      have h := (le_div_iff₀ hu₀R).mpr
        (show (q z : ℝ) * (u₀ : ℝ) ≤ 16 * U - (c : ℝ) * e by nlinarith [hhi, hreprR])
      calc
        (q z : ℝ) ≤ (16 * U - (c : ℝ) * e) / (u₀ : ℝ) := h
        _ ≤ L + 15 := by
          rw [div_le_iff₀ hu₀R]
          have hL : L * (u₀ : ℝ) = U - (c : ℝ) * e := by
            dsimp only [L]
            exact div_mul_cancel₀ _ hu₀R.ne'
          nlinarith [hu₀, hL]
    have hfloor : (k : ℝ) ≤ L := Int.floor_le L
    have hceil : L < (k : ℝ) + 1 := Int.lt_floor_add_one L
    have hnonnegR : (0 : ℝ) ≤ (q z : ℝ) - (k : ℝ) := by linarith
    have hupperR : (q z : ℝ) - (k : ℝ) < 17 := by linarith
    constructor
    · exact_mod_cast hnonnegR
    · exact_mod_cast hupperR
  letI : Fintype s := Fintype.ofFinset s (by intro z; rfl)
  let f : s → Fin 17 := fun z =>
    ⟨(q z.1 - k).toNat, by have h := hqBound z.1 z.2; omega⟩
  have hf : Function.Injective f := by
    intro z z' hzz
    have hval : (q z.1 - k).toNat = (q z'.1 - k).toNat := congrArg Fin.val hzz
    have hz := hqBound z.1 z.2
    have hz' := hqBound z'.1 z'.2
    have hq : q z.1 = q z'.1 := by omega
    have hrep := pd1c_det_line_repr (z.1.1 : ℤ) (z.1.2 : ℤ)
      u₀ v₀ c d e hOne (hs z.1 z.2).2.2
    have hrep' := pd1c_det_line_repr (z'.1.1 : ℤ) (z'.1.2 : ℤ)
      u₀ v₀ c d e hOne (hs z'.1 z'.2).2.2
    apply Subtype.ext
    apply Prod.ext
    · have h : (z.1.1 : ℤ) = (z'.1.1 : ℤ) := by
        calc
          _ = (u₀ : ℤ) * q z.1 + c * e := hrep.1
          _ = (u₀ : ℤ) * q z'.1 + c * e := by rw [hq]
          _ = _ := hrep'.1.symm
      exact_mod_cast h
    · have h : (z.1.2 : ℤ) = (z'.1.2 : ℤ) := by
        calc
          _ = (v₀ : ℤ) * q z.1 + d * e := hrep.2
          _ = (v₀ : ℤ) * q z'.1 + d * e := by rw [hq]
          _ = _ := hrep'.2.symm
      exact_mod_cast h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe] using hcard


lemma pd1c_det_slab_card (s : Finset (ℕ × ℕ)) (U H : ℝ) (hU : 0 < U) (hH : 1 ≤ H)
    (u₀ v₀ : ℕ) (hu₀ : U ≤ (u₀ : ℝ)) (hcop : Nat.Coprime u₀ v₀)
    (hs : ∀ z ∈ s, U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16 * U ∧
      |(u₀ : ℝ) * (z.2 : ℝ) - (v₀ : ℝ) * (z.1 : ℝ)| ≤ 256 * H) :
    (s.card : ℝ) ≤ 9000 * H := by
  let k : ℤ := ⌊256 * H⌋
  let t : Finset ℤ := Finset.Icc (-k) k
  let d (z : ℕ × ℕ) : ℤ := (u₀ : ℤ) * (z.2 : ℤ) - (v₀ : ℤ) * (z.1 : ℤ)
  have hk : 0 ≤ k := Int.floor_nonneg.mpr (by linarith)
  have hmaps : (s : Set (ℕ × ℕ)).MapsTo d t := by
    intro z hz
    have hzB := (hs z hz).2.2
    have hdR : (d z : ℝ) = (u₀ : ℝ) * (z.2 : ℝ) - (v₀ : ℝ) * (z.1 : ℝ) := by
      dsimp only [d]
      norm_cast
    rw [← hdR, abs_le] at hzB
    have hupper : d z ≤ k := Int.le_floor.mpr hzB.2
    have hlower : -(d z) ≤ k := Int.le_floor.mpr (by
      push_cast
      linarith [hzB.1])
    change d z ∈ Finset.Icc (-k) k
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : s.card = ∑ e ∈ t, (s.filter fun z => d z = e).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ e ∈ t, (s.filter fun z => d z = e).card ≤ 17 := by
    intro e he
    apply pd1c_det_line_card _ U hU u₀ v₀ hu₀ hcop e
    intro z hz
    obtain ⟨hzs, hze⟩ := Finset.mem_filter.mp hz
    exact ⟨(hs z hzs).1, (hs z hzs).2.1, hze⟩
  have hsBound : s.card ≤ t.card * 17 := by
    rw [hcard]
    calc
      _ ≤ ∑ e ∈ t, 17 := Finset.sum_le_sum hfiber
      _ = _ := by simp
  have htInt : (t.card : ℤ) = 2 * k + 1 := by
    simp only [t, Int.card_Icc]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ k + 1 - -k)]
    ring
  have htReal : (t.card : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast htInt
  have hkReal : (k : ℝ) ≤ 256 * H := Int.floor_le _
  have hsReal : (s.card : ℝ) ≤ (t.card : ℝ) * 17 := by exact_mod_cast hsBound
  rw [htReal] at hsReal
  nlinarith

lemma pd1c_slope_cell_card (s : Finset (ℕ × ℕ)) (U H : ℝ) (hU : 0 < U) (hH : 1 ≤ H)
    (hs : ∀ z ∈ s, Nat.Coprime z.1 z.2 ∧ U ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ 16 * U)
    (hWidth : ∀ z ∈ s, ∀ w ∈ s,
      |(z.2 : ℝ) / z.1 - (w.2 : ℝ) / w.1| ≤ H / U ^ 2) :
    (s.card : ℝ) ≤ 9000 * H := by
  by_cases hne : s.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    have hPivot := hs z₀ hz₀
    apply pd1c_det_slab_card s U H hU hH z₀.1 z₀.2 hPivot.2.1 hPivot.1
    intro z hz
    have hZ := hs z hz
    refine ⟨hZ.2.1, hZ.2.2, ?_⟩
    have hu₀ : 0 < (z₀.1 : ℝ) := hU.trans_le hPivot.2.1
    have hu : 0 < (z.1 : ℝ) := hU.trans_le hZ.2.1
    have hdet : (z₀.1 : ℝ) * (z.2 : ℝ) - (z₀.2 : ℝ) * (z.1 : ℝ) =
        ((z₀.1 : ℝ) * (z.1 : ℝ)) *
          ((z.2 : ℝ) / z.1 - (z₀.2 : ℝ) / z₀.1) := by
      field_simp [hu₀.ne', hu.ne']
    have hprod : (z₀.1 : ℝ) * (z.1 : ℝ) ≤ 256 * U ^ 2 := by
      calc
        _ ≤ (16 * U) * (16 * U) := mul_le_mul hPivot.2.2 hZ.2.2 hu.le (by positivity)
        _ = _ := by ring
    rw [hdet, abs_mul, abs_of_pos (mul_pos hu₀ hu)]
    calc
      _ ≤ ((z₀.1 : ℝ) * (z.1 : ℝ)) * (H / U ^ 2) :=
        mul_le_mul_of_nonneg_left (hWidth z hz z₀ hz₀) (mul_pos hu₀ hu).le
      _ ≤ (256 * U ^ 2) * (H / U ^ 2) :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = 256 * H := by field_simp [hU.ne']
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    linarith


lemma pd1c_equal_floor_distance (x y : ℝ) (h : ⌊x⌋ = (⌊y⌋ : ℤ)) : |x - y| ≤ 1 := by
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  rw [h] at hx₀ hx₁
  rw [abs_le]
  constructor <;> linarith

lemma pd1c_floor_distance_le (x y : ℝ) :
    |((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)| ≤ |x - y| + 1 := by
  have hx₀ := Int.floor_le x
  have hx₁ := Int.lt_floor_add_one x
  have hy₀ := Int.floor_le y
  have hy₁ := Int.lt_floor_add_one y
  push_cast
  rw [abs_le]
  constructor
  · linarith [neg_le_abs (x - y)]
  · linarith [le_abs_self (x - y)]

lemma pd1c_integer_neighbors_card (s : Finset ℤ) (c : ℤ) (m : ℕ) :
    (s.filter fun j => |c - j| ≤ (m : ℤ)).card ≤ 2 * m + 1 := by
  let t := Finset.Icc (c - (m : ℤ)) (c + (m : ℤ))
  have hsub : (s.filter fun j => |c - j| ≤ (m : ℤ)) ⊆ t := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    rw [abs_le] at h
    change j ∈ Finset.Icc _ _
    rw [Finset.mem_Icc]
    constructor <;> omega
  have ht : t.card = 2 * m + 1 := by
    simp only [t, Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans (by rw [ht])

end ArtinPrimitiveRoots.TypeII.PD
