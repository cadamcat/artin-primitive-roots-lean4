import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_logPower_expDecay (A B c : ℝ) (hc : 0 < c) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) ≤
        Real.rpow L (-A) := by
  have hpowTendsto : Filter.Tendsto (fun L : ℝ => Real.rpow L (1 / 10 : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (y := (1 / 10 : ℝ)) (by norm_num)
  have hcomp :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (A + B)) c hc).comp hpowTendsto
  have heq : (fun L : ℝ =>
      Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) =ᶠ[Filter.atTop]
      (fun L : ℝ => Real.rpow L (A + B) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    have hpower : Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
        Real.rpow L (A + B) := by
      have hlogpow : Real.log (Real.rpow L (1 / 10 : ℝ)) =
          (1 / 10 : ℝ) * Real.log L := by
        change Real.log (L ^ (1 / 10 : ℝ)) = _
        exact Real.log_rpow hL _
      calc
        Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
            Real.exp (Real.log (Real.rpow L (1 / 10 : ℝ)) * (10 * (A + B))) :=
              Real.rpow_def_of_pos (Real.rpow_pos_of_pos hL _) _
        _ = Real.exp (Real.log L * (A + B)) := by
          rw [hlogpow]
          congr 1
          ring
        _ = Real.rpow L (A + B) := (Real.rpow_def_of_pos hL _).symm
    rw [hpower]
  have hlim : Filter.Tendsto (fun L : ℝ =>
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)))
        Filter.atTop (nhds 0) :=
    hcomp.congr' heq
  have hevent : ∀ᶠ L : ℝ in Filter.atTop,
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  rcases Filter.eventually_atTop.mp hevent with ⟨L₁, hL₁⟩
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hL₀ : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hsmall := (hL₁ L hL₀).le
  have hpow : Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L B := by
    calc
      Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L (-A + (A + B)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L B := by congr 1 <;> ring
  calc
    Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) =
        Real.rpow L (-A) *
          (Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
            rw [← hpow]
            ring
    _ ≤ Real.rpow L (-A) * 1 := mul_le_mul_of_nonneg_left hsmall
      (Real.rpow_nonneg (le_of_lt hLpos) _)
    _ = Real.rpow L (-A) := by ring

/-- A fixed multiplicative constant is absorbed by one extra power before exponential decay. -/
theorem pd4c_logPower_expDecay_const (A B c C : ℝ) (hc : 0 < c) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      C * Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) ≤ Real.rpow L (-A) := by
  obtain ⟨L₁, hL₁, hdecay⟩ := pd4c_logPower_expDecay A (B + 1) c hc
  refine ⟨max L₁ C, le_trans hL₁ (le_max_left _ _), ?_⟩
  intro L hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans hL₁ (le_trans (le_max_left _ _) hL))
  have hCL : C ≤ L := le_trans (le_max_right _ _) hL
  have hpow : C * Real.rpow L B ≤ Real.rpow L (B + 1) := by
    calc
      _ ≤ L * Real.rpow L B := mul_le_mul_of_nonneg_right hCL (Real.rpow_pos_of_pos hLpos _).le
      _ = Real.rpow L 1 * Real.rpow L B := by
        have hOne : Real.rpow L 1 = L := Real.rpow_one L
        rw [hOne]
      _ = Real.rpow L (1 + B) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1; ring
  exact (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le).trans
    (hdecay L (le_trans (le_max_left _ _) hL))

/-- Every admitted dyad has exponentially small inverse tenth-power in the log scale. -/
theorem pd4c_scale_Y_inv_tenth_le {K : ℕ} (δ c₁ c₂ : ℝ) (S : PDScale)
    (hS : S.Valid K δ c₁ c₂) :
    Real.rpow S.Y (-(1 / 10 : ℝ)) ≤
      Real.exp (-(1 / 200 : ℝ) * Real.rpow S.L (1 / 10 : ℝ)) := by
  rcases Finset.mem_filter.mp hS.2.2.2.2.2.1 with ⟨hYmem, hYbounds⟩
  rcases Finset.mem_image.mp hYmem with ⟨n, hn, heq⟩
  have hYpos : 0 < S.Y := by rw [← heq]; positivity
  have hPowEq : Real.rpow S.Y (-(1 / 10 : ℝ)) =
      Real.exp (Real.log S.Y * (-(1 / 10 : ℝ))) := Real.rpow_def_of_pos hYpos _
  rw [hPowEq]
  apply Real.exp_le_exp.mpr
  have hlower : (1 / 20 : ℝ) * Real.rpow S.L (1 / 10 : ℝ) ≤ Real.log S.Y := hYbounds.1
  linarith

/-- The memory cutoff has the quadratic log-scale upper bound used by both dirty estimates. -/
theorem pd4c_memoryCutoff_le (S : PDScale) (hL : 1 ≤ S.L) :
    (memoryCutoff S : ℝ) ≤ 2 * Real.rpow S.L 2 := by
  have hLpos : 0 < S.L := by linarith
  have hpow : 1 ≤ Real.rpow S.L 2 := Real.one_le_rpow hL (by norm_num)
  have hc : (memoryCutoff S : ℝ) < Real.rpow S.L 2 + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_pos_of_pos hLpos 2).le
  linarith

theorem pd4c_slots_ge_logPower (S : PDScale) :
    Real.rpow S.L (1 / 100 : ℝ) ≤ (S.M : ℝ) := by
  simpa only [PDScale.M, slotCount, momentJ, PDScale.L, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one (Real.rpow S.L (1 / 100 : ℝ))).le

/-- The main raw small-side term is at most twice its exact log power. -/
theorem pd4c_cutoff_over_slots_le (S : PDScale) (K : ℕ) (hL : 1 ≤ S.L) :
    (memoryCutoff S : ℝ) / (S.M : ℝ) ^ K ≤ 2 * Real.rpow S.L (2 - (K : ℝ) / 100) := by
  have hLpos : 0 < S.L := by linarith
  have hM := pd4c_slots_ge_logPower S
  have hPpos : 0 < Real.rpow S.L (1 / 100 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hMpos : 0 < (S.M : ℝ) := lt_of_lt_of_le hPpos hM
  have hMpow := pow_le_pow_left₀ hPpos.le hM K
  calc
    _ ≤ (2 * Real.rpow S.L 2) / (Real.rpow S.L (1 / 100 : ℝ)) ^ K :=
      div_le_div₀ (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos hLpos 2).le)
        (pd4c_memoryCutoff_le S hL) (pow_pos hPpos _) hMpow
    _ = 2 * Real.rpow S.L (2 - (K : ℝ) / 100) := by
      have hPow : (Real.rpow S.L (1 / 100 : ℝ)) ^ K = Real.rpow S.L ((K : ℝ) / 100) := by
        calc
          _ = Real.rpow (Real.rpow S.L (1 / 100 : ℝ)) (K : ℝ) := (Real.rpow_natCast _ K).symm
          _ = Real.rpow S.L ((1 / 100 : ℝ) * (K : ℝ)) := (Real.rpow_mul hLpos.le _ _).symm
          _ = _ := by congr 1; ring
      rw [hPow]
      have hsub : Real.rpow S.L (2 - (K : ℝ) / 100) =
          Real.rpow S.L 2 / Real.rpow S.L ((K : ℝ) / 100) := Real.rpow_sub hLpos _ _
      rw [hsub]
      ring

/-- The complete raw error factor has the exact log exponent and is eventually at most one. -/
theorem pd4c_raw_scale_bounds (K : ℕ) (hK : 201 ≤ K) (c : ℝ) (hc : 0 < c) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ S : PDScale, L₀ ≤ S.L →
      let D := (memoryCutoff S : ℝ) / (S.M : ℝ) ^ K +
        (memoryCutoff S : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ))
      0 ≤ D ∧ D ≤ 1 ∧ D ≤ 4 * Real.rpow S.L (2 - (K : ℝ) / 100) := by
  let a := (K : ℝ) / 100 - 2
  have ha : 0 < a := by
    have hKr : (201 : ℝ) ≤ K := by exact_mod_cast hK
    dsimp [a]
    linarith
  obtain ⟨L₁, hL₁, hdecay⟩ := pd4c_logPower_expDecay_const a (2 * (K : ℝ)) c ((2 : ℝ) ^ K) hc
  obtain ⟨L₂, hL₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop ha).eventually_ge_atTop (3 : ℝ))
  refine ⟨max L₁ (max 1 L₂), le_trans hL₁ (le_max_left _ _), ?_⟩
  intro S hL₀
  have hL : 1 ≤ S.L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL₀
  have hLpos : 0 < S.L := by linarith
  have hpowlarge : 3 ≤ Real.rpow S.L a := hL₂ S.L
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL₀)
  have hmain := pd4c_cutoff_over_slots_le S K hL
  have hBpow : (memoryCutoff S : ℝ) ^ K ≤ (2 : ℝ) ^ K * Real.rpow S.L (2 * (K : ℝ)) := by
    calc
      _ ≤ (2 * Real.rpow S.L 2) ^ K := pow_le_pow_left₀ (Nat.cast_nonneg _) (pd4c_memoryCutoff_le S hL) K
      _ = (2 : ℝ) ^ K * (Real.rpow S.L 2) ^ K := mul_pow _ _ _
      _ = _ := by
        have hpow : (Real.rpow S.L 2) ^ K = Real.rpow S.L (2 * (K : ℝ)) := by
          calc
            _ = Real.rpow (Real.rpow S.L 2) (K : ℝ) := (Real.rpow_natCast _ K).symm
            _ = _ := (Real.rpow_mul hLpos.le _ _).symm
        rw [hpow]
  have hexp : (memoryCutoff S : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)) ≤
      Real.rpow S.L (2 - (K : ℝ) / 100) := by
    have hdec := hdecay S.L (le_trans (le_max_left _ _) hL₀)
    have haeq : -a = 2 - (K : ℝ) / 100 := by dsimp [a]; ring
    rw [haeq] at hdec
    exact (mul_le_mul_of_nonneg_right hBpow (Real.exp_pos _).le).trans hdec
  have hsum : (memoryCutoff S : ℝ) / (S.M : ℝ) ^ K +
      (memoryCutoff S : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)) ≤
      3 * Real.rpow S.L (2 - (K : ℝ) / 100) := by linarith
  have hrate : Real.rpow S.L (2 - (K : ℝ) / 100) = 1 / Real.rpow S.L a := by
    calc
      _ = Real.rpow S.L (-a) := by dsimp [a]; congr 1; ring
      _ = (Real.rpow S.L a)⁻¹ := Real.rpow_neg hLpos.le a
      _ = _ := by simp only [one_div]
  have hsmall : 3 * Real.rpow S.L (2 - (K : ℝ) / 100) ≤ 1 := by
    rw [hrate, mul_one_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hLpos a)).2 (by simpa using hpowlarge)
  have hDnonneg : 0 ≤ (memoryCutoff S : ℝ) / (S.M : ℝ) ^ K +
      (memoryCutoff S : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)) := by positivity
  exact ⟨hDnonneg, hsum.trans hsmall, hsum.trans (by nlinarith [Real.rpow_pos_of_pos hLpos (2 - (K : ℝ) / 100)])⟩

theorem pd4c_memoryCutoff_pow_le (S : PDScale) (K : ℕ) (hL : 1 ≤ S.L) :
    (memoryCutoff S : ℝ) ^ K ≤ (2 : ℝ) ^ K * Real.rpow S.L (2 * (K : ℝ)) := by
  have hLpos : 0 < S.L := by linarith
  calc
    _ ≤ (2 * Real.rpow S.L 2) ^ K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (pd4c_memoryCutoff_le S hL) K
    _ = (2 : ℝ) ^ K * (Real.rpow S.L 2) ^ K := mul_pow _ _ _
    _ = _ := by
      have hpow : (Real.rpow S.L 2) ^ K = Real.rpow S.L (2 * (K : ℝ)) := by
        calc
          _ = Real.rpow (Real.rpow S.L 2) (K : ℝ) := (Real.rpow_natCast _ K).symm
          _ = _ := (Real.rpow_mul hLpos.le _ _).symm
      rw [hpow]

/-- The comparison saving is exponential uniformly over every admitted dyadic scale. -/
theorem pd4c_comparison_saving_le {K : ℕ} (δ c₁ c₂ : ℝ) (S : PDScale)
    (hS : S.Valid K δ c₁ c₂) (hL : 1 ≤ S.L) :
    Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) + Real.rpow S.Y (-(1 / 10 : ℝ)) ≤
      2 * Real.exp (-(1 / 200 : ℝ) * Real.rpow S.L (1 / 10 : ℝ)) := by
  have hT : 0 ≤ Real.rpow S.L (1 / 10 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hfirst : Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) ≤
      Real.exp (-(1 / 200 : ℝ) * Real.rpow S.L (1 / 10 : ℝ)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsecond := pd4c_scale_Y_inv_tenth_le δ c₁ c₂ S hS
  linarith

/-- All cutoff and major-arc powers are polynomial in L before the comparison saving. -/
theorem pd4c_comparison_row_scale_le {K : ℕ} (δ c₁ c₂ : ℝ) (S : PDScale)
    (hS : S.Valid K δ c₁ c₂) (hL : 1 ≤ S.L) (A₀ C : ℝ) (hC : 0 ≤ C) :
    C * Real.rpow S.L A₀ ^ 3 * (memoryCutoff S : ℝ) ^ K *
      (Real.exp (-Real.rpow S.L (1 / 10 : ℝ)) + Real.rpow S.Y (-(1 / 10 : ℝ))) ≤
        (2 * C * (2 : ℝ) ^ K) * Real.rpow S.L (3 * A₀ + 2 * (K : ℝ)) *
          Real.exp (-(1 / 200 : ℝ) * Real.rpow S.L (1 / 10 : ℝ)) := by
  have hLpos : 0 < S.L := by linarith
  have hpow : Real.rpow S.L A₀ ^ 3 * Real.rpow S.L (2 * (K : ℝ)) =
      Real.rpow S.L (3 * A₀ + 2 * (K : ℝ)) := by
    have hcube : Real.rpow S.L A₀ ^ 3 = Real.rpow S.L (3 * A₀) := by
      calc
        _ = Real.rpow (Real.rpow S.L A₀) (3 : ℝ) := (Real.rpow_natCast _ 3).symm
        _ = Real.rpow S.L (A₀ * 3) := (Real.rpow_mul hLpos.le _ _).symm
        _ = _ := by congr 1; ring
    rw [hcube]
    exact (Real.rpow_add hLpos _ _).symm
  have hsave := pd4c_comparison_saving_le δ c₁ c₂ S hS hL
  have hB := pd4c_memoryCutoff_pow_le S K hL
  have hp : 0 ≤ C * Real.rpow S.L A₀ ^ 3 := mul_nonneg hC (pow_nonneg (Real.rpow_pos_of_pos hLpos _).le _)
  calc
    _ ≤ C * Real.rpow S.L A₀ ^ 3 * ((2 : ℝ) ^ K * Real.rpow S.L (2 * (K : ℝ))) *
        (2 * Real.exp (-(1 / 200 : ℝ) * Real.rpow S.L (1 / 10 : ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB hp) hsave
        (add_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by
          rcases Finset.mem_filter.mp hS.2.2.2.2.2.1 with ⟨hm, _⟩
          rcases Finset.mem_image.mp hm with ⟨n, hn, heq⟩
          rw [← heq]; positivity) _))
        (mul_nonneg hp (mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_pos_of_pos hLpos _).le))
    _ = _ := by rw [← hpow]; ring

end

end ArtinPrimitiveRoots.TypeII.PD
