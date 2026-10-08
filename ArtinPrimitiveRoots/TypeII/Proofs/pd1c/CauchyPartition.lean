import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.CauchyPrimes

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_partition_eta_le_one (eta : ℝ → ℝ)
    (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (hnonneg : ∀ y, 0 ≤ eta y) (hpart : IsDyadicPartition eta) (y : ℝ) : eta y ≤ 1 := by
  by_cases hy : 0 < y
  · have hs : Summable (fun k : ℤ => eta (y / (2 : ℝ) ^ k)) := by
      by_contra h
      have hp := hpart y hy
      rw [tsum_eq_zero_of_not_summable h] at hp
      norm_num at hp
    have h := hs.sum_le_tsum ({0} : Finset ℤ) (fun k hk => hnonneg _) 
    simpa [hpart y hy] using h
  · have hz : eta y = 0 := by
      by_contra h
      have hsup := hEta (Function.mem_support.mpr h)
      exact hy (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hsup.1)
    simp [hz]

lemma pd1c_eta_log_window (eta : ℝ → ℝ)
    (hEta : Function.support eta ⊆ Set.Icc 1 4) (b : ℝ) (hb : 0 < b)
    (k : ℤ) (hk : eta (b / (2 : ℝ) ^ k) ≠ 0) :
    Real.log b - Real.log 4 ≤ (k : ℝ) * Real.log 2 ∧
      (k : ℝ) * Real.log 2 ≤ Real.log b := by
  have hs := hEta (Function.mem_support.mpr hk)
  have hz : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hlo : (2 : ℝ) ^ k ≤ b := by
    simpa only [one_mul] using (le_div_iff₀ hz).mp hs.1
  have hhi : b ≤ 4 * (2 : ℝ) ^ k := (div_le_iff₀ hz).mp hs.2
  have hl := Real.log_le_log hz hlo
  have hh := Real.log_le_log hb hhi
  rw [Real.log_zpow] at hl
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hz.ne', Real.log_zpow] at hh
  constructor <;> linarith

lemma pd1c_partition_finite_dyads {x : ℝ} {K : ℕ}
    (eta : ℝ → ℝ) (hEta : Function.support eta ⊆ Set.Icc 1 4)
    (hpart : IsDyadicPartition eta) (b : ℝ) (hb : 0 < b)
    (hLower : (1 / 20 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ) ≤ Real.log b - Real.log 4)
    (hUpper : Real.log b ≤ ((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ))
    (hL : 0 ≤ Real.log x) :
    ∑ Y ∈ dyadicScales x K, eta (b / Y) = 1 := by
  let N := ⌊((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) / Real.log 2⌋₊
  let s : Finset ℕ := Finset.range (N + 1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinj : Function.Injective (fun k : ℕ => (2 : ℝ) ^ k) := by
    intro i j hij
    have h := congrArg Real.log hij
    simp only [Real.log_pow] at h
    have heq : (i : ℝ) = j := by nlinarith
    exact_mod_cast heq
  have hZ : ∀ k : ℤ, eta (b / (2 : ℝ) ^ k) ≠ 0 → k ∈ s.image (fun n : ℕ => (n : ℤ)) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := pd1c_eta_log_window eta hEta b hb k hk
    have hk0 : 0 ≤ k := by
      have hlow0 : 0 ≤ (1 / 20 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ) := by positivity
      have : 0 ≤ (k : ℝ) := by nlinarith [hLower]
      exact_mod_cast this
    have hkN : k.toNat ≤ N := by
      apply (Nat.le_floor_iff (by positivity : 0 ≤ ((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) / Real.log 2)).mpr
      have : (k : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (hhi.trans hUpper)
      have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      rw [hcast]
      exact this
    exact Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (Nat.lt_succ_of_le hkN), Int.toNat_of_nonneg hk0⟩
  have hzsum : ∑' k : ℤ, eta (b / (2 : ℝ) ^ k) = ∑ k ∈ s, eta (b / (2 : ℝ) ^ k) := by
    rw [tsum_eq_sum (s := s.image (fun n : ℕ => (n : ℤ))) (fun k hk => by
      by_contra hn; exact hk (hZ k hn))]
    rw [Finset.sum_image (fun i hi j hj hij => Int.ofNat_inj.mp hij)]
    simp only [zpow_natCast]
  rw [← hpart b hb, hzsum]
  unfold dyadicScales
  change ∑ Y ∈ (s.image (fun k => (2 : ℝ) ^ k)).filter _, eta (b / Y) = _
  rw [Finset.sum_filter]
  rw [Finset.sum_image (fun i hi j hj hij => hinj hij)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : eta (b / (2 : ℝ) ^ k) = 0
  · simp [he]
  · obtain ⟨hlo, hhi⟩ := pd1c_eta_log_window eta hEta b hb (k : ℤ) (by simpa using he)
    have hwin : (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log ((2 : ℝ) ^ k) ∧
        Real.log ((2 : ℝ) ^ k) ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
      rw [Real.log_pow]
      exact ⟨hLower.trans (by simpa using hlo), (show (k : ℝ) * Real.log 2 ≤ Real.log b by exact_mod_cast hhi).trans hUpper⟩
    exact if_pos hwin

lemma pd1c_tuple_log (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (t : Fin K → ℕ)
    (ht : IsMarkedPrimeTuple x K a t) :
    Real.log (tupleProduct t : ℝ) = ∑ i : Fin K, Real.log (t i : ℝ) := by
  simp only [tupleProduct, Nat.cast_prod]
  exact Real.log_prod (fun i hi => by exact_mod_cast (pd1c_tuple_entry_prime ht i).ne_zero)

lemma pd1c_tuple_log_range_eventual (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ t : Fin K → ℕ,
      IsMarkedPrimeTuple x K a t →
      (1 / 20 : ℝ) * (Real.log x) ^ (1 / 10 : ℝ) ≤ Real.log (tupleProduct t : ℝ) - Real.log 4 ∧
      Real.log (tupleProduct t : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) := by
  have he : ∀ᶠ L : ℝ in atTop, ∀ i : Fin K, L ^ (a i - 1 / 5 : ℝ) ≤ 1 / 2 := by
    apply eventually_all.mpr
    intro i
    exact ((tendsto_rpow_neg_atTop (sub_pos.mpr (ha.2.1 i).2)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun L h => by simpa [sub_eq_add_neg] using h.le)
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp he
  have he2 : ∀ᶠ L : ℝ in atTop, 2 * Real.log 4 ≤ L ^ (1 / 10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually (eventually_ge_atTop _)
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp he2
  let L₀ := max 1 (max L₁ L₂)
  refine ⟨max 2 (Real.exp L₀), le_max_left _ _, ?_⟩
  intro x hx t ht
  have hL : L₀ ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx)
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hL
  have hLp : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL1
  have hSmall : ∀ i : Fin K, Real.rpow (Real.log x) (a i) ≤ (Real.log x) ^ (1 / 5 : ℝ) / 2 := by
    intro i
    have h := hL₁ (Real.log x) ((le_max_left _ _).trans ((le_max_right _ _).trans hL)) i
    have hp : Real.rpow (Real.log x) (a i) =
        (Real.log x) ^ (1 / 5 : ℝ) * (Real.log x) ^ (a i - 1 / 5 : ℝ) := by
      rw [← Real.rpow_add hLp]
      congr 1
      ring
    rw [hp]
    nlinarith [mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hLp.le (1 / 5 : ℝ))]
  have hPrimeBounds : ∀ i : Fin K, (Real.log x) ^ (1 / 10 : ℝ) ≤ Real.log (t i : ℝ) ∧
      Real.log (t i : ℝ) ≤ (Real.log x) ^ (1 / 5 : ℝ) := by
    intro i
    have hm := (Finset.mem_filter.mp (ht i)).2
    have htpos : 0 < (t i : ℝ) := by exact_mod_cast hm.1.pos
    have hl := Real.log_le_log (Real.exp_pos _) hm.2.1
    have hu := Real.log_le_log htpos hm.2.2
    rw [Real.log_exp] at hl hu
    constructor
    · exact (Real.rpow_le_rpow_of_exponent_le hL1 (ha.2.1 i).1.le).trans hl
    · linarith [hSmall i]
  rw [pd1c_tuple_log x K a t ht]
  constructor
  · let i₀ : Fin K := ⟨0, ha.1⟩
    have hi : Real.log (t i₀ : ℝ) ≤ ∑ i : Fin K, Real.log (t i : ℝ) :=
      Finset.single_le_sum (fun i hi => (Real.rpow_nonneg hLp.le _).trans (hPrimeBounds i).1) (Finset.mem_univ _)
    have he2 := hL₂ (Real.log x) ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
    have hp0 := Real.rpow_nonneg hLp.le (1 / 10 : ℝ)
    linarith [(hPrimeBounds i₀).1]
  · calc
      _ ≤ ∑ i : Fin K, (Real.log x) ^ (1 / 5 : ℝ) := Finset.sum_le_sum (fun i hi => (hPrimeBounds i).2)
      _ = (K : ℝ) * (Real.log x) ^ (1 / 5 : ℝ) := by simp
      _ ≤ _ := by push_cast; nlinarith [Real.rpow_nonneg hLp.le (1 / 5 : ℝ)]

end ArtinPrimitiveRoots.TypeII.PD
