import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.Goodness

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical ArtinPrimitiveRoots.TypeII Filter
set_option maxHeartbeats 1000000

lemma pd1c_eventual_bands_separated (K : ℕ) (a : Fin K → ℝ) (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) ∧
      (∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) < roughCutoff x) := by
  obtain ⟨Lgap, hLgap, hgap⟩ := pd1c_lowerBandRpow_small K a ha
  have hlim : Tendsto (fun L : ℝ => Real.rpow L (-(1 / 25 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hevent : ∀ᶠ L : ℝ in atTop, Real.rpow L (-(1 / 25 : ℝ)) < 1 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨Lbelow, hbelow⟩ := eventually_atTop.mp hevent
  let L₀ := max Lgap Lbelow
  let x₀ := max 2 (Real.exp L₀)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx
  have hL : L₀ ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx)
  have hLg : Lgap ≤ Real.log x := (le_max_left _ _).trans hL
  have hLb : Lbelow ≤ Real.log x := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ Real.log x := hLgap.trans hLg
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL1
  have hK : 1 ≤ (K : ℝ) := by
    have hKpos := ha.1
    exact_mod_cast (by omega : 1 ≤ K)
  have hOrdered : ∀ i j : Fin K, i.val < j.val →
      ∀ p ∈ primeBand x (a i), ∀ q ∈ primeBand x (a j), (p : ℝ) < q := by
    intro i j hij p hp q hq
    have hsmall := hgap (Real.log x) hLg i j hij
    have ht : 0 < Real.rpow (Real.log x) (a j) := Real.rpow_pos_of_pos hLpos _
    have hden : 64 ≤ 64 * (K : ℝ) := by nlinarith
    have hsmall' : Real.rpow (Real.log x) (a i) ≤ Real.rpow (Real.log x) (a j) / 64 :=
      hsmall.trans (div_le_div_of_nonneg_left ht.le (by norm_num) hden)
    have hExp : Real.exp (2 * Real.rpow (Real.log x) (a i)) <
        Real.exp (Real.rpow (Real.log x) (a j)) := by
      apply Real.exp_lt_exp.mpr
      simp only [Real.rpow_eq_pow] at hsmall' ht ⊢
      nlinarith [hsmall']
    have hP := (Finset.mem_filter.mp hp).2
    have hQ := (Finset.mem_filter.mp hq).2
    exact lt_of_le_of_lt hP.2.2 (lt_of_lt_of_le hExp hQ.2.1)
  constructor
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases lt_or_gt_of_ne hij with h | h
    · exact (lt_irrefl (p : ℝ)) (hOrdered i j h p hp p hq)
    · exact (lt_irrefl (p : ℝ)) (hOrdered j i h p hq p hp)
  · intro i p hp
    have hsmall := hbelow (Real.log x) hLb
    have hpow : Real.rpow (Real.log x) (1 / 5 : ℝ) =
        Real.rpow (Real.log x) (24 / 100 : ℝ) *
          Real.rpow (Real.log x) (-(1 / 25 : ℝ)) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hLpos]
      congr 1
      norm_num
    have hPower : 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) <
        Real.rpow (Real.log x) (24 / 100 : ℝ) := by
      have htop : 0 < Real.rpow (Real.log x) (24 / 100 : ℝ) :=
        Real.rpow_pos_of_pos hLpos _
      rw [hpow]
      simp only [Real.rpow_eq_pow] at hsmall htop ⊢
      nlinarith [hsmall]
    have hAi : Real.rpow (Real.log x) (a i) ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (ha.2.1 i).2.le
    have hP := (Finset.mem_filter.mp hp).2
    unfold roughCutoff
    refine lt_of_le_of_lt hP.2.2 (Real.exp_lt_exp.mpr ?_)
    simp only [Real.rpow_eq_pow] at hAi hPower ⊢
    linarith


lemma pd1c_dyadic_small_relative_to_X (K : ℕ) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ X : ℝ, c₁ * x ≤ X →
      1 ≤ Real.log x ∧ 1 ≤ X ∧ ∀ Y ∈ dyadicScales x K, 0 < Y ∧ Y ≤ X ^ (1 / 4 : ℝ) := by
  let k : ℝ := ((K + 1 : ℕ) : ℝ)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hlim : Tendsto (fun L : ℝ => L ^ (-(4 / 5 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hε : 0 < 1 / (8 * k) := by positivity
  have hsmall : ∀ᶠ L : ℝ in atTop, L ^ (-(4 / 5 : ℝ)) < 1 / (8 * k) :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨Lsmall, hLsmall⟩ := eventually_atTop.mp hsmall
  let L₀ := max 1 (max Lsmall (2 * |Real.log c₁| + 2))
  let x₀ := max 2 (Real.exp L₀)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx X hX
  let L := Real.log x
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hx)
  have hL : L₀ ≤ L := by
    simpa only [L, Real.log_exp] using Real.log_le_log (Real.exp_pos L₀) ((le_max_right _ _).trans hx)
  have hLone : 1 ≤ L := (le_max_left _ _).trans hL
  have hLs : Lsmall ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLabs : 2 * |Real.log c₁| + 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hXpos : 0 < X := (mul_pos hc₁ hxpos).trans_le hX
  have hLogX : L / 2 + 1 ≤ Real.log X := by
    have hlog := Real.log_le_log (mul_pos hc₁ hxpos) hX
    rw [Real.log_mul hc₁.ne' hxpos.ne'] at hlog
    change Real.log c₁ + L ≤ Real.log X at hlog
    linarith [neg_le_abs (Real.log c₁)]
  have hXone : 1 ≤ X := by
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
      _ = X := Real.exp_log hXpos
  have hCoef : k * L ^ (-(4 / 5 : ℝ)) ≤ 1 / 8 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * k)).mp (hLsmall L hLs)
    nlinarith
  have hPow : L ^ (1 / 5 : ℝ) = L * L ^ (-(4 / 5 : ℝ)) := by
    calc
      L ^ (1 / 5 : ℝ) = L ^ (1 + -(4 / 5 : ℝ)) := by congr 1; norm_num
      _ = L ^ (1 : ℝ) * L ^ (-(4 / 5 : ℝ)) := Real.rpow_add hLpos _ _
      _ = _ := by rw [Real.rpow_one]
  have hUpper : k * L ^ (1 / 5 : ℝ) ≤ L / 8 := by
    rw [hPow]
    have h := mul_le_mul_of_nonneg_right hCoef hLpos.le
    nlinarith
  refine ⟨hLone, hXone, ?_⟩
  intro Y hY
  obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hY).1
  have hYpos : 0 < Y := by rw [← hjeq]; positivity
  refine ⟨hYpos, ?_⟩
  have hYlog : Real.log Y ≤ k * L ^ (1 / 5 : ℝ) := (pd1c_dyadicScale_log_bounds hY).2
  calc
    Y = Real.exp (Real.log Y) := (Real.exp_log hYpos).symm
    _ ≤ Real.exp (Real.log X * (1 / 4 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = X ^ (1 / 4 : ℝ) := (Real.rpow_def_of_pos hXpos _).symm

end ArtinPrimitiveRoots.TypeII.PD
