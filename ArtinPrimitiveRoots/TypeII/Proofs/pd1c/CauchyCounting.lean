import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyWeights

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_product_minus_one_card (N m d : ℕ) (hd : 0 < d) :
    ((Finset.range (N + 1)).filter (fun n => 1 ≤ m * n ∧ d ∣ m * n - 1)).card ≤ N / d + 1 := by
  let s := (Finset.range (N + 1)).filter (fun n => 1 ≤ m * n ∧ d ∣ m * n - 1)
  by_cases hs : s.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hs
    have heq : ∀ n ∈ s, (m : ZMod d) * (n : ZMod d) = 1 := by
      intro n hn
      have hdata := (Finset.mem_filter.mp hn).2
      have hzero : ((m * n - 1 : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdata.2
      rw [Nat.cast_sub hdata.1, Nat.cast_mul, Nat.cast_one] at hzero
      exact sub_eq_zero.mp hzero
    have hResidue : ∀ a ∈ s, ∀ b ∈ s, a % d = b % d := by
      intro a ha b hb
      have haEq := heq a ha
      have hbEq := heq b hb
      have h₀ := heq n₀ hn₀
      have hz : (a : ZMod d) = (b : ZMod d) := by
        calc
          (a : ZMod d) = (n₀ : ZMod d) * ((m : ZMod d) * (a : ZMod d)) := by rw [← mul_assoc, mul_comm (n₀ : ZMod d) _, h₀, one_mul]
          _ = (n₀ : ZMod d) := by rw [haEq, mul_one]
          _ = (n₀ : ZMod d) * ((m : ZMod d) * (b : ZMod d)) := by rw [hbEq, mul_one]
          _ = (b : ZMod d) := by rw [← mul_assoc, mul_comm (n₀ : ZMod d) _, h₀, one_mul]
      exact (ZMod.natCast_eq_natCast_iff' a b d).mp hz
    letI : Fintype s := Fintype.ofFinset s (by intro h; rfl)
    let f : s → Fin (N / d + 1) := fun n =>
      ⟨n.1 / d, Nat.lt_succ_of_le (Nat.div_le_div_right
        (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp n.2).1)))⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hq : a.1 / d = b.1 / d := congrArg Fin.val hab
      have hm := hResidue a.1 a.2 b.1 b.2
      have ha := Nat.mod_add_div a.1 d
      have hb := Nat.mod_add_div b.1 d
      rw [hm, hq] at ha
      exact Subtype.ext (ha.symm.trans hb)
    have hc := Fintype.card_le_of_injective f hf
    simpa [s, Fintype.card_coe] using hc
  · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ _
    simp [hz]

lemma pd1c_dyadic_product_minus_one_count (H : ℝ) (m d : ℕ) (hH : 0 ≤ H)
    (hd : 0 < d) (hdH : (d : ℝ) ≤ H)
    (hPos : ∀ n ∈ dyadicIntegers H, 1 ≤ m * n) :
    (∑ n ∈ dyadicIntegers H, if d ∣ m * n - 1 then (1 : ℝ) else 0) ≤ 3 * H / d := by
  let s := (dyadicIntegers H).filter (fun n => d ∣ m * n - 1)
  have hs : s ⊆ (Finset.range (⌊2 * H⌋₊ + 1)).filter (fun n => 1 ≤ m * n ∧ d ∣ m * n - 1) := by
    intro n hn
    have h := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h.1).1, hPos n h.1, h.2⟩
  have hcard := (Finset.card_le_card hs).trans (pd1c_product_minus_one_card ⌊2 * H⌋₊ m d hd)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdiv : ((⌊2 * H⌋₊ / d : ℕ) : ℝ) ≤ 2 * H / d := by
    have hmul : (⌊2 * H⌋₊ / d) * d ≤ ⌊2 * H⌋₊ := Nat.div_mul_le_self _ _
    have hmulR : ((⌊2 * H⌋₊ / d : ℕ) : ℝ) * d ≤ (⌊2 * H⌋₊ : ℝ) := by exact_mod_cast hmul
    apply (le_div_iff₀ hdpos).mpr
    exact hmulR.trans (Nat.floor_le (by positivity))
  have h1 : (1 : ℝ) ≤ H / d := (le_div_iff₀ hdpos).mpr (by simpa using hdH)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  change (s.card : ℝ) ≤ _
  calc
    _ ≤ ((⌊2 * H⌋₊ / d : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    _ ≤ 2 * H / d + H / d := add_le_add hdiv h1
    _ = _ := by ring

lemma pd1c_dyadic_card_bound (H : ℝ) (hH : 1 ≤ H) :
    ((dyadicIntegers H).card : ℝ) ≤ 3 * H := by
  have hc : (dyadicIntegers H).card ≤ ⌊2 * H⌋₊ + 1 := (Finset.card_filter_le _ _).trans (by simp)
  have hf : (⌊2 * H⌋₊ : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
  calc
    _ ≤ (⌊2 * H⌋₊ : ℝ) + 1 := by exact_mod_cast hc
    _ ≤ _ := by linarith

lemma pd1c_marked_square_small_eventual (δ : ℝ) (hδ : 0 < δ) (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → 2 ≤ x ^ δ ∧
      ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) ^ 2 ≤ x ^ δ := by
  have he : ∀ᶠ L : ℝ in atTop, L ^ (-(4 / 5 : ℝ)) ≤ δ / 4 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4 / 5)).eventually (Iio_mem_nhds (by positivity))).mono (fun L h => h.le)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp he
  let L₀ := max 1 (max L₁ (Real.log 2 / δ))
  refine ⟨max 2 (Real.exp L₀), le_max_left _ _, ?_⟩
  intro x hx
  have hL : L₀ ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx)
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hL
  have hLp : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL1
  have hxpos : 0 < x := by linarith [(le_max_left 2 (Real.exp L₀)).trans hx]
  have hExp : 4 * (Real.log x) ^ (1 / 5 : ℝ) ≤ δ * Real.log x := by
    have h := hL₁ (Real.log x) ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
    have hPow : (Real.log x) ^ (1 / 5 : ℝ) = Real.log x * (Real.log x) ^ (-(4 / 5 : ℝ)) := by
      calc
        (Real.log x) ^ (1 / 5 : ℝ) = (Real.log x) ^ (1 + -(4 / 5 : ℝ)) := by congr 1; norm_num
        _ = (Real.log x) ^ (1 : ℝ) * (Real.log x) ^ (-(4 / 5 : ℝ)) := Real.rpow_add hLp _ _
        _ = _ := by rw [Real.rpow_one]
    rw [hPow]
    nlinarith [mul_le_mul_of_nonneg_left h hLp.le]
  have h2 : Real.log 2 ≤ δ * Real.log x := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    have hd := mul_le_mul_of_nonneg_left h hδ.le
    field_simp at hd
    linarith
  constructor
  · rw [Real.rpow_def_of_pos hxpos]
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · intro i p hp
    have hm := (Finset.mem_filter.mp hp).2
    have ht := Real.rpow_le_rpow_of_exponent_le hL1 (ha.2.1 i).2.le
    calc
      (p : ℝ) ^ 2 ≤ (Real.exp (2 * Real.rpow (Real.log x) (a i))) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hm.2.2 2
      _ = Real.exp (4 * Real.rpow (Real.log x) (a i)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (δ * Real.log x) := Real.exp_le_exp.mpr (by simp only [Real.rpow_eq_pow] at hm ht ⊢; linarith)
      _ = x ^ δ := by rw [Real.rpow_def_of_pos hxpos]; congr 1; ring

end ArtinPrimitiveRoots.TypeII.PD
