import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.FixedCutoff

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical Filter
open scoped Topology
open ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.Construction

/-- Primes above a fixed power exceed the rough cutoff and avoid every group integer. -/
theorem large_prime_coprime_group (M K : ℕ) (a : Fin K → ℝ) (b : ℝ)
    (hM : 0 < M) (ha : ValidBands K a) (hb : 0 < b) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ n : ℕ, n.Prime → Real.rpow x b < (n : ℝ) →
        roughCutoff x < (n : ℝ) ∧
          ∀ r : ℕ, IsGroupInteger x K a r → Nat.Coprime n (M * r) := by
  obtain ⟨Xw, hXw₂, hcut⟩ := fixed_block_cutoff b hb 0
  have hL80 : Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) (4 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      Real.tendsto_log_atTop
  obtain ⟨Tmarked, hTmarked⟩ := eventually_atTop.mp
    (hL80.eventually_ge_atTop (2 / b))
  obtain ⟨TM, hTM⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hb).eventually_gt_atTop (M : ℝ))
  refine ⟨max Xw (max Tmarked (max TM (Real.exp 1))),
    hXw₂.trans (le_max_left _ _), ?_⟩
  intro x hx n hn hnbound
  have hxw : Xw ≤ x := (le_max_left _ _).trans hx
  have hxmarked : Tmarked ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxM : TM ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hx))
  have hxexp : Real.exp 1 ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hx))
  have hx₂ : 2 ≤ x := hXw₂.trans hxw
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hLone : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := by simp
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hxexp
  have hLpos : 0 < Real.log x := by linarith
  have hWone : 1 ≤ roughCutoff x := by
    change 1 ≤ Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ))
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ)) :=
        Real.exp_le_exp.mpr (Real.rpow_nonneg hLpos.le _)
  have hWsq : (roughCutoff x) ^ 2 ≤ Real.rpow x (b / 2) := by
    simpa using hcut x hxw
  have hWbound : roughCutoff x ≤ Real.rpow x b := by
    calc
      roughCutoff x ≤ (roughCutoff x) ^ 2 := by
        nlinarith [sq_nonneg (roughCutoff x - 1)]
      _ ≤ Real.rpow x (b / 2) := hWsq
      _ ≤ Real.rpow x b :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
  have hfactor : (2 : ℝ) ≤ b * Real.rpow (Real.log x) (4 / 5 : ℝ) := by
    have h := (div_le_iff₀ hb).mp (hTmarked x hxmarked)
    simpa only [mul_comm] using h
  have hsplit : Real.rpow (Real.log x) (4 / 5 : ℝ) *
      Real.rpow (Real.log x) (1 / 5 : ℝ) = Real.log x := by
    change (Real.log x) ^ (4 / 5 : ℝ) *
      (Real.log x) ^ (1 / 5 : ℝ) = Real.log x
    rw [← Real.rpow_add hLpos]
    rw [show (4 / 5 + 1 / 5 : ℝ) = 1 by norm_num]
    exact Real.rpow_one _
  have hpowBound : 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) ≤ b * Real.log x := by
    calc
      2 * Real.rpow (Real.log x) (1 / 5 : ℝ) ≤
          (b * Real.rpow (Real.log x) (4 / 5 : ℝ)) *
            Real.rpow (Real.log x) (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hLpos.le _)
      _ = b * Real.log x := by rw [mul_assoc, hsplit]
  have hexp : Real.exp (b * Real.log x) = Real.rpow x b := by
    rw [mul_comm]
    exact (Real.rpow_def_of_pos hxpos b).symm
  have hMarkedBound (p : ℕ) (hp : p ∈ markedPrimes x K a) :
      (p : ℝ) ≤ Real.rpow x b := by
    simp only [markedPrimes, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hpi⟩ := hp
    rcases (Finset.mem_filter.mp hpi).2 with ⟨_, _, hpupper⟩
    have hai : Real.rpow (Real.log x) (a i) ≤
        Real.rpow (Real.log x) (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLone (ha.2.1 i).2.le
    calc
      (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) (a i)) := hpupper
      _ ≤ Real.exp (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hai (by norm_num))
      _ ≤ Real.exp (b * Real.log x) := Real.exp_le_exp.mpr hpowBound
      _ = Real.rpow x b := hexp
  refine ⟨hWbound.trans_lt hnbound, ?_⟩
  intro r hr
  apply hn.coprime_iff_not_dvd.mpr
  intro hdiv
  rcases hn.dvd_mul.mp hdiv with hnM | hnr
  · have hnleM : (n : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hM hnM
    exact (not_le_of_gt ((hTM x hxM).trans hnbound)) hnleM
  · exact (not_le_of_gt hnbound) (hMarkedBound n (hr n hn hnr))

end ArtinPrimitiveRoots.Proofs.c_bins_sol
