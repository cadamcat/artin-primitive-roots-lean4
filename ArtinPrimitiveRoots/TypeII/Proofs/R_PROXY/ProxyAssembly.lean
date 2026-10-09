import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.PhaseBounds
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.MertensBounds

/-!
Finite divisor-mass and residue-class assembly for the rough proxy source.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical
open Filter

private theorem prime_product_pos (S : Finset ℕ)
    (hP : ∀ p ∈ S, p.Prime) : 0 < ∏ p ∈ S, p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpPrime := hP p (Finset.mem_insert_self p S)
    have hTail : ∀ q ∈ S, q.Prime := by
      intro q hq
      exact hP q (Finset.mem_insert_of_mem hq)
    have hTailPos := ih hTail
    simpa [Finset.prod_insert, hp] using Nat.mul_pos hpPrime.pos hTailPos

/-- The retained inclusion-exclusion divisors have reciprocal mass at most
`1/V(W)`. -/
theorem truncated_divisor_reciprocal_mass_le_inv_sieve_product
    (W : ℝ) (r : ℕ) :
    (∑ S ∈ (primesUpTo W).powerset.filter (fun S => S.card < r),
      1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤
      (roughSieveProduct W)⁻¹ := by
  classical
  let P := primesUpTo W
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    exact (Finset.mem_filter.mp hp).2
  have hterm (p : ℕ) (hp : p ∈ P) :
      1 + 1 / (p : ℝ) ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    have hpPrime := hPprime p hp
    have hpCast : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpPrime.two_le
    have hrecipPos : 0 < 1 / (p : ℝ) := by positivity
    have hrecipLe : 1 / (p : ℝ) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hpCast
    have hfactorPos : 0 < 1 - 1 / (p : ℝ) := by linarith
    rw [← one_div]
    apply (le_div_iff₀ hfactorPos).2
    nlinarith [sq_nonneg (1 / (p : ℝ))]
  have hEuler :
      (∏ p ∈ P, (1 + 1 / (p : ℝ))) ≤
        ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := by
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      exact hterm p hp
  have hInv :
      (∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹) =
        (∏ p ∈ P, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
  have hMass := truncated_divisor_reciprocal_mass P
    (fun p hp => hPprime p hp) r
  calc
    _ ≤ ∏ p ∈ P, (1 + 1 / (p : ℝ)) := hMass
    _ ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))⁻¹ := hEuler
    _ = (roughSieveProduct W)⁻¹ := by
      rw [hInv]
      simp [P, roughSieveProduct]

/-- The high-frequency cutoff is eventually below any fixed positive power
of `x`, as needed for the PP residue estimate. -/
theorem high_phase_threshold_below_power (δ : ℝ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        Real.exp (L / Real.log L ^ 2) ≤ Real.rpow x (δ / 2) := by
  let C : ℝ := Real.sqrt (2 / δ)
  have hCpos : 0 < C := by
    dsimp [C]
    exact Real.sqrt_pos.2 (by positivity)
  have hlogLog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hCevent : ∀ᶠ x : ℝ in atTop, C ≤ Real.log (Real.log x) :=
    hlogLog.eventually_ge_atTop C
  have htwoEvent : ∀ᶠ x : ℝ in atTop, 2 ≤ x := eventually_ge_atTop 2
  have hfinal : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ C ≤ Real.log (Real.log x) := by
    filter_upwards [htwoEvent, hCevent] with x hx₂ hCLog
    exact ⟨hx₂, hCLog⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨x₀, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx
  dsimp
  obtain ⟨hx₂, hCLog⟩ := hx₀ x hx
  let L : ℝ := Real.log x
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hlogLpos : 0 < Real.log L := by
    have : C ≤ Real.log L := by simpa [L] using hCLog
    linarith
  have hlogLSq : 2 / δ ≤ (Real.log L) ^ 2 := by
    have hrootSq : C ^ 2 = 2 / δ := by
      dsimp [C]
      exact Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.log L - C)]
  have hsmall : 1 / (Real.log L) ^ 2 ≤ δ / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogLpos)).2
    have hmul := mul_le_mul_of_nonneg_left hlogLSq (by positivity : 0 ≤ δ / 2)
    have hcancel : (δ / 2) * (2 / δ) = 1 := by
      field_simp [ne_of_gt hδ]
    nlinarith
  have hratio : L / (Real.log L) ^ 2 ≤ L * (δ / 2) := by
    calc
      L / (Real.log L) ^ 2 = L * (1 / (Real.log L) ^ 2) := by ring
      _ ≤ L * (δ / 2) := mul_le_mul_of_nonneg_left hsmall hLpos.le
  calc
    Real.exp (L / Real.log L ^ 2) ≤ Real.exp (L * (δ / 2)) :=
      Real.exp_le_exp.mpr hratio
    _ = Real.rpow x (δ / 2) := by
      simpa [L, mul_comm] using (Real.rpow_def_of_pos hxpos (δ / 2)).symm

/-- Apply the moderate and high phase inputs on their respective frequency
 ranges to a reciprocal-log residue sum. -/
theorem reciprocal_log_phase_regime_bound
    (δ A₀ : ℝ) (hδ : 0 < δ) (hA₀ : 0 < A₀) :
    ∃ C_m c_m C_p C₃p x₀ : ℝ,
      0 < C_m ∧ 0 < c_m ∧ 0 < C_p ∧ 0 < C₃p ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let Tstar := Real.exp (L / Real.log L ^ 2)
          ∀ N M : ℝ, Real.rpow x (δ / 2) ≤ N →
            N ≤ 2 * Real.rpow x 5 → 1 < M → 1 ≤ Real.log M →
            ∀ d : ℕ, 0 < d → M ≤ (d : ℝ) * N →
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
                ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                    ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                      if |u| ≤ Tstar then
                        4 * C_m * (N / (q : ℝ)) / Real.log M *
                          (|u|⁻¹ + Real.rpow x (-c_m))
                      else
                        4 * C_p * (N / (q : ℝ)) / Real.log M *
                          Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
  have hδhalf : 0 < δ / 2 := by positivity
  obtain ⟨C_m, c_m, x_m, hCm, hcm, hxm, hModerate⟩ :=
    moderate_reciprocal_log_residue_bound (δ / 2) A₀ hδhalf hA₀
  obtain ⟨C₃p, hC₃p, hHighForA⟩ := high_reciprocal_log_residue_bound
  obtain ⟨C_p, x_p, hCp, hxp, hHigh⟩ := hHighForA A₀ hA₀
  obtain ⟨x_cut, hxcut, hCut⟩ := high_phase_threshold_below_power δ hδ
  let x₀ := max 2 (max (max x_m x_p) (max x_cut (Real.exp 2)))
  refine ⟨C_m, c_m, C_p, C₃p, x₀, hCm, hcm, hCp, hC₃p,
    le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro N M hN hNupper hM hlogM d hd hMD q hq hqBound a u huLower huUpper l r hl hlr hr
  rcases max_le_iff.mp hx with ⟨hxTwo, hxCore⟩
  rcases max_le_iff.mp hxCore with ⟨hxMP, hxCutExp⟩
  rcases max_le_iff.mp hxMP with ⟨hxM, hxP⟩
  rcases max_le_iff.mp hxCutExp with ⟨hxCut, hxExpTwo⟩
  have hlogXtwo : 2 ≤ Real.log x := by
    calc
      2 = Real.log (Real.exp 2) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 2) hxExpTwo
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hlogLpos : 0 < Real.log L := Real.log_pos (by dsimp [L]; linarith)
  have hTstarLower : Real.exp (L / Real.log L ^ 2) ≤ N := by
    calc
      Real.exp (L / Real.log L ^ 2) ≤ Real.rpow x (δ / 2) := by
        simpa [L] using hCut x hxCut
      _ ≤ N := hN
  by_cases huModerate : |u| ≤ Tstar
  · have hModBound := hModerate x hxM N M hN hM hlogM d hd hMD
      q hq hqBound a u huLower (by simpa [L, Tstar] using huModerate)
      l r hl hlr hr
    simpa [L, Tstar, huModerate] using hModBound
  · have hlogLSqPos : 0 < (Real.log L) ^ 2 := sq_pos_of_pos hlogLpos
    have hfracEq : L / (2 * (Real.log L) ^ 2) =
        (1 / 2) * (L / (Real.log L) ^ 2) := by
      field_simp [ne_of_gt hlogLSqPos]
      <;> ring
    have hfrac : L / (2 * (Real.log L) ^ 2) ≤ L / (Real.log L) ^ 2 := by
      rw [hfracEq]
      calc
        (1 / 2 : ℝ) * (L / (Real.log L) ^ 2) ≤
            1 * (L / (Real.log L) ^ 2) :=
          mul_le_mul_of_nonneg_right
            (by norm_num : (1 / 2 : ℝ) ≤ 1)
            (div_nonneg hLpos.le hlogLSqPos.le)
        _ = L / (Real.log L) ^ 2 := by ring
    have hPPfreqLower :
        Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ |u| := by
      have hhalf : Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ Tstar := by
        dsimp [Tstar]
        exact Real.exp_le_exp.mpr hfrac
      exact hhalf.trans (le_of_lt (lt_of_not_ge huModerate))
    have hxgeone : 1 ≤ x := by linarith
    have hpow23 : Real.rpow x 2 ≤ Real.rpow x 3 :=
      Real.rpow_le_rpow_of_exponent_le hxgeone (by norm_num)
    have hpow3nonneg : 0 ≤ Real.rpow x 3 :=
      Real.rpow_nonneg hxpos.le _
    have hpowUpper : Real.rpow x 2 ≤ 4 * Real.rpow x 3 := by
      nlinarith
    have hPPfreqUpper : |u| ≤ 4 * Real.rpow x 3 := huUpper.trans hpowUpper
    have hHighBound := hHigh x hxP N M hTstarLower hNupper hM hlogM d hd hMD
      q hq hqBound a u hPPfreqLower hPPfreqUpper l r hl hlr hr
    simpa [L, Tstar, huModerate] using hHighBound

/-- The high-phase estimate with a fixed absolute logarithmic exponent. -/
def HighPhaseResidueBound (C₃p : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.log L
        ∀ N M : ℝ, Real.exp (L / T ^ 2) ≤ N →
          N ≤ 2 * Real.rpow x 5 → 1 < M → 1 ≤ Real.log M →
          ∀ d : ℕ, 0 < d → M ≤ (d : ℝ) * N →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ a : ZMod q, ∀ u : ℝ,
                Real.exp (L / (2 * T ^ 2)) ≤ |u| →
                |u| ≤ 4 * Real.rpow x 3 →
                  ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                    ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                      4 * C₀ * (N / (q : ℝ)) / Real.log M *
                        Real.exp (-L / Real.rpow T C₃p)

/-- Apply the two phase estimates while keeping the global PP exponent fixed. -/
theorem reciprocal_log_phase_regime_bound_fixed
    (δ A₀ C₃p : ℝ) (hδ : 0 < δ) (hA₀ : 0 < A₀) (hC₃p : 0 < C₃p)
    (hHigh : HighPhaseResidueBound C₃p) :
    ∃ C_m c_m C_p x₀ : ℝ,
      0 < C_m ∧ 0 < c_m ∧ 0 < C_p ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let Tstar := Real.exp (L / Real.log L ^ 2)
          ∀ N M : ℝ, Real.rpow x (δ / 2) ≤ N →
            N ≤ 2 * Real.rpow x 5 → 1 < M → 1 ≤ Real.log M →
            ∀ d : ℕ, 0 < d → M ≤ (d : ℝ) * N →
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
                ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                    ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                      if |u| ≤ Tstar then
                        4 * C_m * (N / (q : ℝ)) / Real.log M *
                          (|u|⁻¹ + Real.rpow x (-c_m))
                      else
                        4 * C_p * (N / (q : ℝ)) / Real.log M *
                          Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
  have hδhalf : 0 < δ / 2 := by positivity
  obtain ⟨C_m, c_m, x_m, hCm, hcm, hxm, hModerate⟩ :=
    moderate_reciprocal_log_residue_bound (δ / 2) A₀ hδhalf hA₀
  obtain ⟨C_p, x_p, hCp, hxp, hHighA⟩ := hHigh A₀ hA₀
  obtain ⟨x_cut, hxcut, hCut⟩ := high_phase_threshold_below_power δ hδ
  let x₀ := max 2 (max (max x_m x_p) (max x_cut (Real.exp 2)))
  refine ⟨C_m, c_m, C_p, x₀, hCm, hcm, hCp, le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro N M hN hNupper hM hlogM d hd hMD q hq hqBound a u huLower huUpper l r hl hlr hr
  rcases max_le_iff.mp hx with ⟨hxTwo, hxCore⟩
  rcases max_le_iff.mp hxCore with ⟨hxMP, hxCutExp⟩
  rcases max_le_iff.mp hxMP with ⟨hxM, hxP⟩
  rcases max_le_iff.mp hxCutExp with ⟨hxCut, hxExpTwo⟩
  have hlogXtwo : 2 ≤ Real.log x := by
    calc
      2 = Real.log (Real.exp 2) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 2) hxExpTwo
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hlogLpos : 0 < Real.log L := Real.log_pos (by dsimp [L]; linarith)
  have hTstarLower : Real.exp (L / Real.log L ^ 2) ≤ N := by
    calc
      Real.exp (L / Real.log L ^ 2) ≤ Real.rpow x (δ / 2) := by
        simpa [L] using hCut x hxCut
      _ ≤ N := hN
  by_cases huModerate : |u| ≤ Tstar
  · have hModBound := hModerate x hxM N M hN hM hlogM d hd hMD
      q hq hqBound a u huLower (by simpa [L, Tstar] using huModerate)
      l r hl hlr hr
    simpa [L, Tstar, huModerate] using hModBound
  · have hlogLSqPos : 0 < (Real.log L) ^ 2 := sq_pos_of_pos hlogLpos
    have hfracEq : L / (2 * (Real.log L) ^ 2) =
        (1 / 2) * (L / (Real.log L) ^ 2) := by
      field_simp [ne_of_gt hlogLSqPos]
      <;> ring
    have hfrac : L / (2 * (Real.log L) ^ 2) ≤ L / (Real.log L) ^ 2 := by
      rw [hfracEq]
      calc
        (1 / 2 : ℝ) * (L / (Real.log L) ^ 2) ≤
            1 * (L / (Real.log L) ^ 2) :=
          mul_le_mul_of_nonneg_right
            (by norm_num : (1 / 2 : ℝ) ≤ 1)
            (div_nonneg hLpos.le hlogLSqPos.le)
        _ = L / (Real.log L) ^ 2 := by ring
    have hPPfreqLower :
        Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ |u| := by
      have hhalf : Real.exp (L / (2 * (Real.log L) ^ 2)) ≤ Tstar := by
        dsimp [Tstar]
        exact Real.exp_le_exp.mpr hfrac
      exact hhalf.trans (le_of_lt (lt_of_not_ge huModerate))
    have hxgeone : 1 ≤ x := by linarith
    have hpow23 : Real.rpow x 2 ≤ Real.rpow x 3 :=
      Real.rpow_le_rpow_of_exponent_le hxgeone (by norm_num)
    have hpow3nonneg : 0 ≤ Real.rpow x 3 := Real.rpow_nonneg hxpos.le _
    have hpowUpper : Real.rpow x 2 ≤ 4 * Real.rpow x 3 := by nlinarith
    have hPPfreqUpper : |u| ≤ 4 * Real.rpow x 3 := huUpper.trans hpowUpper
    have hHighBound := hHighA x hxP N M hTstarLower hNupper hM hlogM d hd hMD
      q hq hqBound a u hPPfreqLower hPPfreqUpper l r hl hlr hr
    simpa [L, Tstar, huModerate] using hHighBound

/-- Keep the analytic phase constants fixed while varying the sieve order. -/
theorem retained_subset_residue_phase_bound_fixed
    (δ A₀ lam C_m c_m C_p C₃p xPhase : ℝ)
    (hδ : 0 < δ) (hlam : 0 < lam)
    (hCm : 0 < C_m) (hcm : 0 < c_m) (hCp : 0 < C_p) (hC₃p : 0 < C₃p)
    (hxPhase : 2 ≤ xPhase)
    (hPhase : ∀ x : ℝ, xPhase ≤ x →
      let L := Real.log x
      let Tstar := Real.exp (L / Real.log L ^ 2)
      ∀ N M : ℝ, Real.rpow x (δ / 2) ≤ N →
        N ≤ 2 * Real.rpow x 5 → 1 < M → 1 ≤ Real.log M →
        ∀ d : ℕ, 0 < d → M ≤ (d : ℝ) * N →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
            ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| →
              |u| ≤ Real.rpow x 2 →
                ∀ l rr : ℝ, N ≤ l → l ≤ rr → rr ≤ 2 * N →
                  ‖reciprocalLogResiduePhaseSum d q a u l rr‖ ≤
                    if |u| ≤ Tstar then
                      4 * C_m * (N / (q : ℝ)) / Real.log M *
                        (|u|⁻¹ + Real.rpow x (-c_m))
                    else
                      4 * C_p * (N / (q : ℝ)) / Real.log M *
                        Real.exp (-L / Real.rpow (Real.log L) C₃p)) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let Tstar := Real.exp (L / Real.log L ^ 2)
        ∀ M : ℝ, Real.rpow x δ ≤ M → 1 < M →
          M ≤ 2 * Real.rpow x 5 → 1 ≤ Real.log M →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
            ∀ r : ℕ, r = ⌈lam * Real.log L⌉₊ →
              ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
                  (fun S => S.card < r),
                ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| →
                  |u| ≤ Real.rpow x 2 →
                    ∀ l rr : ℝ, M ≤ l → l ≤ rr → rr ≤ 2 * M →
                      ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) q a u
                          (l / ((∏ p ∈ S, p : ℕ) : ℝ))
                          (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
                        if |u| ≤ Tstar then
                          4 * C_m *
                            ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (q : ℝ)) /
                              Real.log M *
                            (|u|⁻¹ + Real.rpow x (-c_m))
                        else
                          4 * C_p *
                            ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (q : ℝ)) /
                              Real.log M *
                            Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
  obtain ⟨xRet, hxRet, hRet⟩ := retained_subset_product_bound δ lam hδ hlam
  let x₀ := max xPhase xRet
  have hx₀two : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxPhase (le_max_left _ _)
  refine ⟨x₀, hx₀two, ?_⟩
  intro x hx
  dsimp
  intro M hMx hMgt hMupper hlogM q hq hqBound r hr S hS a u huLower huUpper
    l rr hl hlr hrr
  have hxPhase' : xPhase ≤ x := le_trans (le_max_left _ _) hx
  have hxRet' : xRet ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := le_trans hxPhase hxPhase'
  have hxpos : 0 < x := by linarith
  have hxRetBound := hRet x hxRet'
  have hSRet : S ∈ (primesUpTo (roughCutoff x)).powerset.filter
      (fun S => S.card < ⌈lam * Real.log (Real.log x)⌉₊) := by
    simpa [hr] using hS
  have hDposNat : 0 < ∏ p ∈ S, p := by
    have hSP : S ⊆ primesUpTo (roughCutoff x) :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hSRet).1
    have hPrime : ∀ p ∈ S, p.Prime := by
      intro p hp
      exact (Finset.mem_filter.mp (hSP hp)).2
    exact prime_product_pos S hPrime
  let dR : ℝ := ((∏ p ∈ S, p : ℕ) : ℝ)
  have hDpos : 0 < dR := by dsimp [dR]; exact_mod_cast hDposNat
  have hDone : 1 ≤ dR := by
    have hNat : 1 ≤ ∏ p ∈ S, p := Nat.one_le_iff_ne_zero.mpr hDposNat.ne'
    change (1 : ℝ) ≤ ((∏ p ∈ S, p : ℕ) : ℝ)
    exact_mod_cast hNat
  have hDbound : dR ≤ Real.rpow x (δ / 8) := by
    simpa [dR] using hxRetBound S hSRet
  have hPowScale :
      dR * Real.rpow x (δ / 2) ≤ Real.rpow x δ := by
    have hPowD : Real.rpow x (δ / 8) * Real.rpow x (δ / 2) =
        Real.rpow x (5 * δ / 8) := by
      calc
        _ = Real.rpow x ((δ / 8) + (δ / 2)) :=
          (Real.rpow_add hxpos _ _).symm
        _ = Real.rpow x (5 * δ / 8) := by congr 1 <;> ring
    have hExponent : 5 * δ / 8 ≤ δ := by linarith
    have hPowMonotone : Real.rpow x (5 * δ / 8) ≤ Real.rpow x δ :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hExponent
    calc
      dR * Real.rpow x (δ / 2) ≤
          Real.rpow x (δ / 8) * Real.rpow x (δ / 2) :=
        mul_le_mul_of_nonneg_right hDbound (Real.rpow_nonneg hxpos.le _)
      _ = Real.rpow x (5 * δ / 8) := hPowD
      _ ≤ Real.rpow x δ := hPowMonotone
  let N : ℝ := M / dR
  have hNlower : Real.rpow x (δ / 2) ≤ N := by
    dsimp [N]
    apply (le_div_iff₀ hDpos).2
    calc
      Real.rpow x (δ / 2) * dR ≤ Real.rpow x δ := by
        simpa [mul_comm] using hPowScale
      _ ≤ M := hMx
  have hNupper : N ≤ 2 * Real.rpow x 5 := by
    dsimp [N]
    apply (div_le_iff₀ hDpos).2
    calc
      M = M * 1 := by ring
      _ ≤ M * dR := mul_le_mul_of_nonneg_left hDone (by linarith)
      _ ≤ (2 * Real.rpow x 5) * dR :=
        mul_le_mul_of_nonneg_right hMupper hDpos.le
  have hMD : M ≤ dR * N := by
    have hEq : dR * (M / dR) = M := by field_simp [ne_of_gt hDpos]
    simpa [N] using hEq.symm.le
  have hqBound' : (q : ℝ) ≤ Real.rpow (Real.log x) A₀ := by
    simpa using hqBound
  have hphase := hPhase x hxPhase' N M hNlower hNupper hMgt hlogM
    (∏ p ∈ S, p) hDposNat hMD q hq hqBound' a u huLower huUpper
    (l / dR) (rr / dR)
  have hl' : N ≤ l / dR := by
    dsimp [N]
    exact div_le_div_of_nonneg_right hl hDpos.le
  have hlr' : l / dR ≤ rr / dR := by
    exact div_le_div_of_nonneg_right hlr hDpos.le
  have hrr' : rr / dR ≤ 2 * N := by
    dsimp [N]
    calc
      rr / dR ≤ (2 * M) / dR := div_le_div_of_nonneg_right hrr hDpos.le
      _ = 2 * (M / dR) := by ring
  have hphase' := hphase hl' hlr' hrr'
  simpa [dR, N] using hphase'

/-- Apply the two phase regimes uniformly to each retained inclusion-exclusion
divisor. The retained product is small enough that the quotient interval still
lies above the phase estimates' lower scale. -/
theorem retained_subset_residue_phase_bound
    (δ A₀ lam : ℝ) (hδ : 0 < δ) (hA₀ : 0 < A₀) (hlam : 0 < lam) :
    ∃ C_m c_m C_p C₃p x₀ : ℝ,
      0 < C_m ∧ 0 < c_m ∧ 0 < C_p ∧ 0 < C₃p ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let Tstar := Real.exp (L / Real.log L ^ 2)
          ∀ M : ℝ, Real.rpow x δ ≤ M → 1 < M →
            M ≤ 2 * Real.rpow x 5 → 1 ≤ Real.log M →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
              ∀ r : ℕ, r = ⌈lam * Real.log L⌉₊ →
                ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
                    (fun S => S.card < r),
                  ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| →
                    |u| ≤ Real.rpow x 2 →
                    ∀ l rr : ℝ, M ≤ l → l ≤ rr → rr ≤ 2 * M →
                      ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) q a u
                          (l / ((∏ p ∈ S, p : ℕ) : ℝ))
                          (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
                        if |u| ≤ Tstar then
                          4 * C_m *
                            ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (q : ℝ)) /
                              Real.log M *
                            (|u|⁻¹ + Real.rpow x (-c_m))
                        else
                          4 * C_p *
                            ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (q : ℝ)) /
                              Real.log M *
                            Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
  obtain ⟨C_m, c_m, C_p, C₃p, xPhase, hCm, hcm, hCp, hC3p, hxPhase,
      hPhase⟩ := reciprocal_log_phase_regime_bound δ A₀ hδ hA₀
  obtain ⟨x₀, hx₀, hBound⟩ := retained_subset_residue_phase_bound_fixed
    δ A₀ lam C_m c_m C_p C₃p xPhase hδ hlam hCm hcm hCp hC3p hxPhase hPhase
  exact ⟨C_m, c_m, C_p, C₃p, x₀, hCm, hcm, hCp, hC3p, hx₀, hBound⟩

/-- Sum the per-residue phase estimates over all retained subset divisors.
The hypotheses isolate the analytic estimate from the finite reindexing. -/
theorem truncated_source_interval_norm_bound
    (x u M V B : ℝ) (r k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (l rr : ℝ)
    (hM : 0 < M) (hB : 0 ≤ B)
    (hl : M ≤ l) (hlr : l ≤ rr)
    (hMass :
      (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤ 1 / V)
    (hResidue : ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
        (fun S => S.card < r), ∀ a : ZMod k,
        ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) k a u
            (l / ((∏ p ∈ S, p : ℕ) : ℝ))
            (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
          B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) :
    ‖∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
        (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
        (smallPrimeTruncation x r m : ℂ) *
          ((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ))‖ ≤ B * M / V := by
  classical
  let I : Finset ℕ := (Finset.range (⌊rr⌋₊ + 1)).filter
    (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr)
  let Q : Finset (Finset ℕ) :=
    (primesUpTo (roughCutoff x)).powerset.filter (fun S => S.card < r)
  have hMpos : 0 < M := hM
  have hlpos : 0 < l := lt_of_lt_of_le hMpos hl
  have hIpos : ∀ m ∈ I, 0 < m := by
    intro m hm
    have hml : l ≤ (m : ℝ) := (Finset.mem_filter.mp hm).2.1
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hlpos hml
    exact_mod_cast hmpos
  have hReindex := truncated_source_reindex_with_weight
    x u r k χ I hIpos (fun _ => (1 : ℂ))
  have hReindex' :
      (∑ m ∈ I,
        (smallPrimeTruncation x r m : ℂ) *
          ((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ))) =
        ∑ S ∈ Q,
          ((-1 : ℂ) ^ S.card) *
            ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u *
                Real.log ((∏ p ∈ S, p : ℕ) : ℝ))) *
            ∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
              (χ (h : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                  Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ) := by
    simpa [I, Q] using hReindex
  have hDivPos (S : Finset ℕ) (hS : S ∈ Q) :
      0 < ∏ p ∈ S, p := by
    have hSP : S ⊆ primesUpTo (roughCutoff x) := by
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hPrime (p : ℕ) (hp : p ∈ S) : p.Prime := by
      exact (Finset.mem_filter.mp (hSP hp)).2
    exact prime_product_pos S hPrime
  have hInner (S : Finset ℕ) (hS : S ∈ Q) :
      ‖∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
          (χ (h : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
              Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ)‖ ≤
        B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) := by
    let d : ℕ := ∏ p ∈ S, p
    let dR : ℝ := (d : ℝ)
    let J : Finset ℕ := divisorQuotients I d
    let f : ℕ → ℂ := fun h =>
      Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
        Real.log ((d * h : ℕ) : ℝ)
    have hd : 0 < d := by simpa [d] using hDivPos S hS
    have hdR : 0 < dR := by dsimp [dR]; exact_mod_cast hd
    have hQuot : J =
        (Finset.range (⌊rr / dR⌋₊ + 1)).filter
          (fun (h : ℕ) => l / dR ≤ (h : ℝ) ∧ (h : ℝ) ≤ rr / dR) := by
      dsimp [J, I, dR]
      exact divisorQuotients_dyadic_interval l rr d hlpos hlr hd
    have hLocalSet (a : ZMod k) :
        J.filter (fun (h : ℕ) => (h : ZMod k) = a) =
          (Finset.range (⌊rr / dR⌋₊ + 1)).filter
            (fun (h : ℕ) => l / dR ≤ (h : ℝ) ∧ (h : ℝ) ≤ rr / dR ∧
              (h : ZMod k) = a) := by
      rw [hQuot]
      ext h
      simp only [Finset.mem_filter, Finset.mem_range]
      tauto
    have hLocal (a : ZMod k) :
        (∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h) =
          reciprocalLogResiduePhaseSum d k a u (l / dR) (rr / dR) := by
      unfold reciprocalLogResiduePhaseSum
      rw [hLocalSet]
    let R : ℝ := B * (M / dR) / (k : ℝ)
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne k))
    have hClassBound (a : ZMod k) :
        ‖∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h‖ ≤ R := by
      rw [hLocal]
      dsimp [R, d, dR]
      exact hResidue S hS a
    have hSplit := sum_character_mul_residue_classes k χ J f
    have hSumBound :
        ‖∑ a ∈ (Finset.univ : Finset (ZMod k)),
            (χ a : ℂ) *
              ∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h‖ ≤
          B * (M / dR) := by
      have hCard : Fintype.card (ZMod k) = k := by simp
      calc
        _ ≤ ∑ a ∈ (Finset.univ : Finset (ZMod k)),
              ‖(χ a : ℂ) *
                ∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h‖ :=
          norm_sum_le _ _
        _ ≤ ∑ a ∈ (Finset.univ : Finset (ZMod k)), R := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul]
          calc
            ‖χ a‖ *
                ‖∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h‖ ≤
              1 * R :=
                (mul_le_mul_of_nonneg_right (χ.norm_le_one a)
                    (norm_nonneg _)).trans
                  (mul_le_mul_of_nonneg_left (hClassBound a) (by norm_num))
            _ = R := by ring
        _ = (k : ℝ) * R := by simp [Finset.sum_const, hCard]
        _ = B * (M / dR) := by
          dsimp [R]
          field_simp [ne_of_gt hkpos]
    have hInnerEq :
        (∑ h ∈ J, (χ (h : ZMod k) : ℂ) * f h) =
          ∑ a ∈ (Finset.univ : Finset (ZMod k)),
            (χ a : ℂ) *
              ∑ h ∈ (J.filter (fun (h : ℕ) => (h : ZMod k) = a)), f h := by
      simpa [J, f] using hSplit
    have hBound := hSumBound
    rw [← hInnerEq] at hBound
    convert hBound using 1 <;> simp [J, f, d, dR] <;> ring
  have hCoeffNorm (S : Finset ℕ) (hS : S ∈ Q) :
      ‖((-1 : ℂ) ^ S.card) *
        ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
          Complex.exp (Complex.I * u *
            Real.log ((∏ p ∈ S, p : ℕ) : ℝ)))‖ ≤ 1 := by
    have hχ : ‖χ ((∏ p ∈ S, p : ℕ) : ZMod k)‖ ≤ 1 :=
      χ.norm_le_one _
    have hExp : ‖Complex.exp (Complex.I * u *
        Real.log ((∏ p ∈ S, p : ℕ) : ℝ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (Complex.I * u *
          Real.log ((∏ p ∈ S, p : ℕ) : ℝ)).re = 0 := by simp
      simp [hre]
    calc
      ‖((-1 : ℂ) ^ S.card) *
          ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u *
              Real.log ((∏ p ∈ S, p : ℕ) : ℝ)))‖ =
        ‖(-1 : ℂ) ^ S.card‖ *
          (‖χ ((∏ p ∈ S, p : ℕ) : ZMod k)‖ *
            ‖Complex.exp (Complex.I * u *
              Real.log ((∏ p ∈ S, p : ℕ) : ℝ))‖) := by
                rw [norm_mul, norm_mul]
      _ = ‖χ ((∏ p ∈ S, p : ℕ) : ZMod k)‖ := by
        rw [show ‖(-1 : ℂ) ^ S.card‖ = 1 by simp, hExp]
        ring
      _ ≤ 1 := hχ
  have hOuter := hReindex'
  rw [hOuter]
  calc
    _ ≤ ∑ S ∈ Q,
          ‖((-1 : ℂ) ^ S.card) *
            ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u *
                Real.log ((∏ p ∈ S, p : ℕ) : ℝ))) *
              ∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ S ∈ Q, B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hNormInner := hInner S hS
      have hNormCoeff := hCoeffNorm S hS
      rw [norm_mul]
      calc
        ‖((-1 : ℂ) ^ S.card) *
            ((χ ((∏ p ∈ S, p : ℕ) : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u *
                Real.log ((∏ p ∈ S, p : ℕ) : ℝ)))‖ *
              ‖∑ h ∈ divisorQuotients I (∏ p ∈ S, p),
                (χ (h : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
                    Real.log (((∏ p ∈ S, p) * h : ℕ) : ℝ)‖ ≤
            1 * (B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) : ℝ) :=
          mul_le_mul hNormCoeff hNormInner (norm_nonneg _) (by positivity)
        _ = B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) := by ring
    _ = B * M *
          ∑ S ∈ Q, 1 / ((∏ p ∈ S, p : ℕ) : ℝ) := by
      calc
        _ = ∑ S ∈ Q,
              (B * M) * (1 / ((∏ p ∈ S, p : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intro S hS
                ring
        _ = B * M *
              ∑ S ∈ Q, 1 / ((∏ p ∈ S, p : ℕ) : ℝ) := by
                rw [Finset.mul_sum]
    _ ≤ B * M * (1 / V) := by
      apply mul_le_mul_of_nonneg_left hMass
      positivity
    _ = B * M / V := by ring

/-- Apply the retained-divisor phase bounds to every subset in the truncated
source expansion, then sum using its reciprocal mass. -/
theorem truncated_source_interval_phase_bound
    (δ A₀ lam : ℝ) (hδ : 0 < δ) (hA₀ : 0 < A₀) (hlam : 0 < lam) :
    ∃ C_m c_m C_p C₃p vMin x₀ : ℝ,
      0 < C_m ∧ 0 < c_m ∧ 0 < C_p ∧ 0 < C₃p ∧ 0 < vMin ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let Tstar := Real.exp (L / Real.log L ^ 2)
          let r := ⌈lam * Real.log L⌉₊
          vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ roughSieveProduct (roughCutoff x) ∧
          ∀ M : ℝ, Real.rpow x δ ≤ M → 1 < M →
            M ≤ 2 * Real.rpow x 5 → 1 ≤ Real.log M →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
              ∀ χ : DirichletCharacter ℂ k,
              ∀ u : ℝ, 1 ≤ |u| → |u| ≤ Real.rpow x 2 →
                ∀ l rr : ℝ, M ≤ l → l ≤ rr → rr ≤ 2 * M →
                  ‖∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
                      (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
                      (smallPrimeTruncation x r m : ℂ) *
                        ((χ (m : ZMod k) : ℂ) *
                          Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                            Real.log (m : ℝ))‖ ≤
                    (if |u| ≤ Tstar then
                      4 * C_m / Real.log M *
                        (|u|⁻¹ + Real.rpow x (-c_m))
                    else
                      4 * C_p / Real.log M *
                        Real.exp (-L / Real.rpow (Real.log L) C₃p)) * M /
                      roughSieveProduct (roughCutoff x) := by
  obtain ⟨C_m, c_m, C_p, C₃p, xPhase, hCm, hcm, hCp, hC₃p, hxPhase,
      hPhase⟩ := retained_subset_residue_phase_bound δ A₀ lam hδ hA₀ hlam
  obtain ⟨_s₀, vMin, xMertens, _hs₀, hvMin, hxMertens, hMertens⟩ :=
    rough_mertens_bounds
  let x₀ := max xPhase xMertens
  have hx₀two : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxPhase (le_max_left _ _)
  refine ⟨C_m, c_m, C_p, C₃p, vMin, x₀, hCm, hcm, hCp, hC₃p, hvMin,
    hx₀two, ?_⟩
  intro x hx
  dsimp
  have hxPhase' : xPhase ≤ x := le_trans (le_max_left _ _) hx
  have hxMertens' : xMertens ≤ x := le_trans (le_max_right _ _) hx
  have hMertensX := hMertens x hxMertens'
  rcases hMertensX with ⟨_, hVlower⟩
  refine ⟨hVlower, ?_⟩
  intro M hMx hMgt hMupper hlogM k hk hkBound χ u huLower huUpper l rr hl hlr hrr
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  let r : ℕ := ⌈lam * Real.log L⌉₊
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let B : ℝ := if |u| ≤ Tstar then
      4 * C_m / Real.log M * (|u|⁻¹ + Real.rpow x (-c_m))
    else
      4 * C_p / Real.log M *
        Real.exp (-L / Real.rpow (Real.log L) C₃p)
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith [hx₀two.trans hx])
  have hVlower' : vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ V := by
    simpa [L, V] using hVlower
  have hVpos : 0 < V := by
    have hpos : 0 < vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
      mul_pos hvMin (Real.rpow_pos_of_pos hLpos _)
    exact lt_of_lt_of_le hpos hVlower'
  have hMass :
      (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤ 1 / V := by
    have hMassInv :=
      truncated_divisor_reciprocal_mass_le_inv_sieve_product (roughCutoff x) r
    simpa [V, one_div] using hMassInv
  have hB : 0 ≤ B := by
    dsimp [B]
    have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by norm_num) hlogM
    have hxpos : 0 < x := by linarith [hx₀two.trans hx]
    split_ifs <;> positivity
  have hResidue : ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
      (fun S => S.card < r), ∀ a : ZMod k,
        ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) k a u
            (l / ((∏ p ∈ S, p : ℕ) : ℝ))
            (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
          B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
    intro S hS a
    have hBound := hPhase x hxPhase' M hMx hMgt hMupper hlogM k hk
      (by simpa [L] using hkBound)
      r (by rfl) S hS a u huLower huUpper l rr hl hlr hrr
    by_cases huModerate : |u| ≤ Tstar
    · calc
        _ ≤ 4 * C_m * ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) /
              Real.log M * (|u|⁻¹ + Real.rpow x (-c_m)) := by
          simpa [L, Tstar, huModerate] using hBound
        _ = B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
          simp [B, huModerate]
          ring
    · calc
        _ ≤ 4 * C_p * ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) /
              Real.log M * Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
          simpa [L, Tstar, huModerate] using hBound
        _ = B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
          simp [B, huModerate]
          ring
  letI : NeZero k := ⟨by omega⟩
  have hTruncated := truncated_source_interval_norm_bound x u M V B r k χ l rr
    hMpos hB hl hlr hMass hResidue
  simpa [B, V, L, Tstar, r] using hTruncated

/-- The truncated-source phase estimate with its analytic constants supplied
in advance, so the later choice of sieve order cannot move them. -/
theorem truncated_source_interval_phase_bound_fixed
    (δ A₀ lam C_m c_m C_p C₃p xPhase s₀ vMin xMertens : ℝ)
    (hδ : 0 < δ) (hA₀ : 0 < A₀) (hlam : 0 < lam)
    (hCm : 0 < C_m) (hcm : 0 < c_m) (hCp : 0 < C_p) (hC₃p : 0 < C₃p)
    (hs₀ : 0 < s₀) (hvMin : 0 < vMin)
    (hxPhase : 2 ≤ xPhase) (hxMertens : 2 ≤ xMertens)
    (hPhase : ∀ x : ℝ, xPhase ≤ x →
      let L := Real.log x
      let Tstar := Real.exp (L / Real.log L ^ 2)
      ∀ N M : ℝ, Real.rpow x (δ / 2) ≤ N →
        N ≤ 2 * Real.rpow x 5 → 1 < M → 1 ≤ Real.log M →
        ∀ d : ℕ, 0 < d → M ≤ (d : ℝ) * N →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L A₀ →
            ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ Real.rpow x 2 →
              ∀ l rr : ℝ, N ≤ l → l ≤ rr → rr ≤ 2 * N →
                ‖reciprocalLogResiduePhaseSum d q a u l rr‖ ≤
                  if |u| ≤ Tstar then
                    4 * C_m * (N / (q : ℝ)) / Real.log M *
                      (|u|⁻¹ + Real.rpow x (-c_m))
                  else
                    4 * C_p * (N / (q : ℝ)) / Real.log M *
                      Real.exp (-L / Real.rpow (Real.log L) C₃p))
    (hMertens : ∀ x : ℝ, xMertens ≤ x →
      let L := Real.log x
      (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ) ≤ s₀ * Real.log L) ∧
      vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ roughSieveProduct (roughCutoff x)) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let Tstar := Real.exp (L / Real.log L ^ 2)
        let r := ⌈lam * Real.log L⌉₊
        vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ roughSieveProduct (roughCutoff x) ∧
        ∀ M : ℝ, Real.rpow x δ ≤ M → 1 < M →
          M ≤ 2 * Real.rpow x 5 → 1 ≤ Real.log M →
          ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
            ∀ χ : DirichletCharacter ℂ k,
            ∀ u : ℝ, 1 ≤ |u| → |u| ≤ Real.rpow x 2 →
              ∀ l rr : ℝ, M ≤ l → l ≤ rr → rr ≤ 2 * M →
                ‖∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
                    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
                    (smallPrimeTruncation x r m : ℂ) *
                      ((χ (m : ZMod k) : ℂ) *
                        Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                          Real.log (m : ℝ))‖ ≤
                  (if |u| ≤ Tstar then
                    4 * C_m / Real.log M *
                      (|u|⁻¹ + Real.rpow x (-c_m))
                  else
                    4 * C_p / Real.log M *
                      Real.exp (-L / Real.rpow (Real.log L) C₃p)) * M /
                    roughSieveProduct (roughCutoff x) := by
  obtain ⟨xRet, hxRet, hRet⟩ :=
    retained_subset_residue_phase_bound_fixed δ A₀ lam C_m c_m C_p C₃p
      xPhase hδ hlam hCm hcm hCp hC₃p hxPhase hPhase
  let x₀ := max xRet xMertens
  have hx₀two : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxRet (le_max_left _ _)
  refine ⟨x₀, hx₀two, ?_⟩
  intro x hx
  dsimp
  have hxRet' : xRet ≤ x := le_trans (le_max_left _ _) hx
  have hxMertens' : xMertens ≤ x := le_trans (le_max_right _ _) hx
  have hMertensX := hMertens x hxMertens'
  rcases hMertensX with ⟨_, hVlower⟩
  refine ⟨hVlower, ?_⟩
  intro M hMx hMgt hMupper hlogM k hk hkBound χ u huLower huUpper l rr hl hlr hrr
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  let r : ℕ := ⌈lam * Real.log L⌉₊
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let B : ℝ := if |u| ≤ Tstar then
      4 * C_m / Real.log M * (|u|⁻¹ + Real.rpow x (-c_m))
    else
      4 * C_p / Real.log M *
        Real.exp (-L / Real.rpow (Real.log L) C₃p)
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith [hx₀two.trans hx])
  have hVlower' : vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ V := by
    simpa [L, V] using hVlower
  have hVpos : 0 < V := by
    have hpos : 0 < vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
      mul_pos hvMin (Real.rpow_pos_of_pos hLpos _)
    exact lt_of_lt_of_le hpos hVlower'
  have hMass :
      (∑ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
          (fun S => S.card < r),
        1 / ((∏ p ∈ S, p : ℕ) : ℝ)) ≤ 1 / V := by
    have hMassInv :=
      truncated_divisor_reciprocal_mass_le_inv_sieve_product (roughCutoff x) r
    simpa [V, one_div] using hMassInv
  have hB : 0 ≤ B := by
    dsimp [B]
    have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by norm_num) hlogM
    have hxpos : 0 < x := by linarith [hx₀two.trans hx]
    split_ifs <;> positivity
  have hResidue : ∀ S ∈ (primesUpTo (roughCutoff x)).powerset.filter
      (fun S => S.card < r), ∀ a : ZMod k,
        ‖reciprocalLogResiduePhaseSum (∏ p ∈ S, p) k a u
            (l / ((∏ p ∈ S, p : ℕ) : ℝ))
            (rr / ((∏ p ∈ S, p : ℕ) : ℝ))‖ ≤
          B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
    intro S hS a
    have hBound := hRet x hxRet' M hMx hMgt hMupper hlogM k hk
      (by simpa [L] using hkBound)
      r (by rfl) S hS a u huLower huUpper l rr hl hlr hrr
    by_cases huModerate : |u| ≤ Tstar
    · calc
        _ ≤ 4 * C_m * ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) /
              Real.log M * (|u|⁻¹ + Real.rpow x (-c_m)) := by
          simpa [L, Tstar, huModerate] using hBound
        _ = B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
          simp [B, huModerate]
          ring
    · calc
        _ ≤ 4 * C_p * ((M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ)) /
              Real.log M * Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
          simpa [L, Tstar, huModerate] using hBound
        _ = B * (M / ((∏ p ∈ S, p : ℕ) : ℝ)) / (k : ℝ) := by
          simp [B, huModerate]
          ring
  letI : NeZero k := ⟨by omega⟩
  have hTruncated := truncated_source_interval_norm_bound x u M V B r k χ l rr
    hMpos hB hl hlr hMass hResidue
  simpa [B, V, L, Tstar, r] using hTruncated

/-- The normalized rough source differs from its finite inclusion-exclusion
truncation by at most the normalized pointwise sieve remainder. -/
theorem rough_source_truncation_error
    (x u M V E : ℝ) (r k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (l rr : ℝ)
    (hM : 0 < M) (hV : 0 < V) (hlogM : 1 ≤ Real.log M)
    (hl : M ≤ l) (hlr : l ≤ rr)
    (hRemainder :
      (∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
          (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
        |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m|) / (M * V) ≤ E) :
    ‖(∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
          (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr ∧
            roughAbove m (roughCutoff x)),
        (χ (m : ZMod k) : ℂ) *
          Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
            Real.log (m : ℝ)) / (M * V) -
      (∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
          (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr),
        (smallPrimeTruncation x r m : ℂ) *
          ((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ))) / (M * V)‖ ≤ E := by
  classical
  let I : Finset ℕ := (Finset.range (⌊rr⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr)
  let R : Finset ℕ := (Finset.range (⌊rr⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr ∧
      roughAbove m (roughCutoff x))
  let f : ℕ → ℂ := fun m =>
    (χ (m : ZMod k) : ℂ) *
      Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
        Real.log (m : ℝ)
  have hR : R = I.filter (fun m => roughAbove m (roughCutoff x)) := by
    ext m
    simp only [R, I, Finset.mem_filter, Finset.mem_range]
    tauto
  have hRoughSum : (∑ m ∈ R, f m) =
      ∑ m ∈ I, (if roughAbove m (roughCutoff x) then (1 : ℂ) else 0) * f m := by
    rw [hR, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hrough : roughAbove m (roughCutoff x) <;> simp [hrough]
  have hIndicatorTerm (m : ℕ) :
      (if roughAbove m (roughCutoff x) then (1 : ℂ) else 0) * f m -
          (smallPrimeTruncation x r m : ℂ) * f m =
        (((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m : ℝ) : ℂ) * f m := by
    by_cases hrough : roughAbove m (roughCutoff x) <;>
      simp [hrough, f, mul_sub] <;> ring
  have hDiffEq :
      (∑ m ∈ R, f m) -
        ∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m =
      ∑ m ∈ I,
        (((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m : ℝ) : ℂ) * f m := by
    rw [hRoughSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    exact hIndicatorTerm m
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by norm_num) hlogM
  have hWeightNorm : ∀ m ∈ I, ‖f m‖ ≤ 1 := by
    intro m hm
    have hmBounds := (Finset.mem_filter.mp hm).2
    have hMm : M ≤ (m : ℝ) := le_trans hl hmBounds.1
    have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hM hMm
    have hlogmLower : Real.log M ≤ Real.log (m : ℝ) :=
      Real.log_le_log hM hMm
    have hlogmPos : 0 < Real.log (m : ℝ) :=
      lt_of_lt_of_le hlogMpos hlogmLower
    have hExpNorm : ‖Complex.exp
        (Complex.I * u * Real.log (m : ℝ))‖ = 1 := by
      have hArg : Complex.I * (u : ℂ) * (Real.log (m : ℝ) : ℂ) =
          Complex.I * ((u * Real.log (m : ℝ) : ℝ) : ℂ) := by
        calc
          _ = Complex.I * ((u : ℂ) * (Real.log (m : ℝ) : ℂ)) := by ring
          _ = Complex.I * ((u * Real.log (m : ℝ) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul]
      rw [hArg]
      exact Complex.norm_exp_I_mul_ofReal _
    have hχ := χ.norm_le_one (m : ZMod k)
    change ‖(χ (m : ZMod k) : ℂ) *
        Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
          (Real.log (m : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, norm_mul, hExpNorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hlogmPos]
    apply (div_le_iff₀ hlogmPos).2
    have hden : 1 ≤ Real.log (m : ℝ) := le_trans hlogM hlogmLower
    nlinarith [hχ, hden]
  have hDiffNorm :
      ‖(∑ m ∈ R, f m) -
          ∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m‖ ≤
        ∑ m ∈ I,
          |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
            smallPrimeTruncation x r m| := by
    rw [hDiffEq]
    calc
      _ ≤ ∑ m ∈ I,
            ‖(((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
              smallPrimeTruncation x r m : ℝ) : ℂ) * f m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ I,
            |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
              smallPrimeTruncation x r m| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul]
        have hCastNorm :
            ‖(((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
              smallPrimeTruncation x r m : ℝ) : ℂ)‖ =
              |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
                smallPrimeTruncation x r m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        rw [hCastNorm]
        calc
          _ ≤ |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
                smallPrimeTruncation x r m| * 1 :=
            mul_le_mul_of_nonneg_left (hWeightNorm m hm) (abs_nonneg _)
          _ = |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
                smallPrimeTruncation x r m| := by ring
  have hDenom : 0 < M * V := mul_pos hM hV
  have hRemainder' :
      (∑ m ∈ I,
        |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m|) / (M * V) ≤ E := by
    simpa [I] using hRemainder
  have hQuotient :
      (∑ m ∈ R, f m) / (M * V) -
          (∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m) / (M * V) =
        ((∑ m ∈ R, f m) -
          ∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m) /
            ((M * V : ℝ) : ℂ) := by
    push_cast
    ring
  calc
    _ = ‖((∑ m ∈ R, f m) -
          ∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m) /
            ((M * V : ℝ) : ℂ)‖ := by rw [hQuotient]
    _ = ‖(∑ m ∈ R, f m) -
          ∑ m ∈ I, (smallPrimeTruncation x r m : ℂ) * f m‖ /
            (M * V) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hDenom]
    _ ≤ (∑ m ∈ I,
          |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
            smallPrimeTruncation x r m|) / (M * V) :=
      div_le_div_of_nonneg_right hDiffNorm hDenom.le
    _ ≤ E := hRemainder'

/-- The rough-filtered reciprocal-log source on a real interval. -/
noncomputable def roughSourceIntervalSum
    (x : ℝ) (k : ℕ) (χ : DirichletCharacter ℂ k) (u l rr : ℝ) : ℂ :=
  ∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
      (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr ∧
        roughAbove m (roughCutoff x)),
    (χ (m : ZMod k) : ℂ) *
      Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
        Real.log (m : ℝ)

/-- The source estimate keeps its analytic constants fixed while the sieve
order is chosen for each requested logarithmic accuracy. -/
theorem proxy_high_source_bound
    (δ A₀ wMin C₃p : ℝ)
    (hδ : 0 < δ) (hA₀ : 0 < A₀) (hwMin : 0 < wMin)
    (hC₃p : 0 < C₃p) (hHigh : HighPhaseResidueBound C₃p) :
    ∃ c_m K : ℝ, 0 < c_m ∧ 0 < K ∧
      ∀ A_s : ℝ, 0 < A_s →
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            let L := Real.log x
            let Tstar := Real.exp (L / Real.log L ^ 2)
            ∀ M : ℝ, Real.rpow x δ ≤ M → wMin * L ≤ Real.log M →
              M ≤ 2 * Real.rpow x 5 →
              ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
                ∀ χ : DirichletCharacter ℂ k, ∀ u : ℝ,
                  1 ≤ |u| → |u| ≤ Real.rpow x 2 →
                    ∀ l rr : ℝ, M ≤ l → l ≤ rr → rr ≤ 2 * M →
                      ‖roughSourceIntervalSum x k χ u l rr /
                          (M * roughSieveProduct (roughCutoff x))‖ ≤
                        Real.rpow L (-A_s) +
                          K * (if |u| ≤ Tstar then
                            |u|⁻¹ + Real.rpow x (-c_m)
                          else
                            Real.exp (-L / Real.rpow (Real.log L) C₃p)) := by
  obtain ⟨C_m, c_m, C_p, xPhase, hCm, hcm, hCp, hxPhase, hPhase⟩ :=
    reciprocal_log_phase_regime_bound_fixed δ A₀ C₃p hδ hA₀ hC₃p hHigh
  obtain ⟨s₀, vMin, xMertens, hs₀, hvMin, hxMertens, hMertens⟩ :=
    rough_mertens_bounds
  let K : ℝ := 4 * max C_m C_p / (vMin ^ 2 * wMin)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨c_m, K, hcm, hK, ?_⟩
  intro A_s hA_s
  let H : ℝ := A_s + 3
  have hH : 0 < H := by dsimp [H]; linarith
  obtain ⟨lam, xFact, hlam, hxFact, hFactorial⟩ :=
    factorial_decay_choice s₀ H hs₀ hH
  obtain ⟨xTrunc, hxTrunc, hTruncated⟩ :=
    truncated_source_interval_phase_bound_fixed δ A₀ lam C_m c_m C_p C₃p
      xPhase s₀ vMin xMertens hδ hA₀ hlam hCm hcm hCp hC₃p hs₀ hvMin
      hxPhase hxMertens hPhase hMertens
  have hExp : 0 < H - A_s - 24 / 100 := by
    dsimp [H]
    norm_num
  have hRpow : Tendsto
      (fun y : ℝ => Real.rpow (Real.log y) (H - A_s - 24 / 100)) atTop atTop :=
    (tendsto_rpow_atTop hExp).comp Real.tendsto_log_atTop
  have hScaled : Tendsto
      (fun y : ℝ => vMin * Real.rpow (Real.log y) (H - A_s - 24 / 100))
      atTop atTop := hRpow.const_mul_atTop hvMin
  obtain ⟨xLarge, hLarge⟩ :=
    Filter.eventually_atTop.mp (hScaled.eventually_ge_atTop 2)
  have hLogTarget : Tendsto (fun y : ℝ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop
  obtain ⟨xLog, hLog⟩ :=
    Filter.eventually_atTop.mp
      (hLogTarget.eventually_ge_atTop (max 1 (1 / wMin)))
  let x₀ := max xMertens (max xTrunc (max xFact (max xLarge xLog)))
  have hx₀two : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxTrunc
      (le_trans (le_max_left _ _) (le_max_right _ _))
  refine ⟨x₀, hx₀two, ?_⟩
  intro x hx
  dsimp [x₀] at hx
  rcases max_le_iff.mp hx with ⟨hxMertens', hxRest⟩
  rcases max_le_iff.mp hxRest with ⟨hxTrunc', hxRest⟩
  rcases max_le_iff.mp hxRest with ⟨hxFact', hxRest⟩
  rcases max_le_iff.mp hxRest with ⟨hxLarge', hxLog'⟩
  dsimp
  intro M hMx hlogMlower hMupper k hk hkBound χ u huLower huUpper l rr hl hlr hrr
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  let r : ℕ := ⌈lam * Real.log L⌉₊
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let I : Finset ℕ := (Finset.range (⌊rr⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr)
  have hx₂ : 2 ≤ x := le_trans hx₀two hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have hLogX : max 1 (1 / wMin) ≤ L := by
    simpa [L] using hLog x hxLog'
  have hLone : 1 ≤ L := le_trans (le_max_left _ _) hLogX
  have hOneOver : 1 / wMin ≤ L := le_trans (le_max_right _ _) hLogX
  have hwLone : 1 ≤ wMin * L := by
    have hm := mul_le_mul_of_nonneg_left hOneOver hwMin.le
    have hcancel : wMin * (1 / wMin) = 1 := by
      field_simp [ne_of_gt hwMin]
    nlinarith
  have hlogM : 1 ≤ Real.log M := by
    have hlogM' : wMin * L ≤ Real.log M := by simpa [L] using hlogMlower
    linarith
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by norm_num) hlogM
  have hRpowPos : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
  have hMpos : 0 < M := lt_of_lt_of_le hRpowPos hMx
  have hMgt : 1 < M := (Real.log_pos_iff hMpos.le).mp hlogMpos
  have hVlower : vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ V := by
    have h := (hMertens x hxMertens').2
    simpa [L, V] using h
  have hVpos : 0 < V := by
    have hbase : 0 < vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
      mul_pos hvMin (Real.rpow_pos_of_pos hLpos _)
    exact lt_of_lt_of_le hbase hVlower
  have hMertensMass :
      (∑ p ∈ primesUpTo (roughCutoff x), 1 / (p : ℝ)) ≤
        s₀ * Real.log (Real.log x) := by
    simpa using (hMertens x hxMertens').1
  have hFactX :
      1 ≤ r ∧ ∀ s : ℝ, 0 ≤ s → s ≤ s₀ * Real.log L →
        s ^ r / (r.factorial : ℝ) ≤ Real.rpow L (-H) := by
    simpa [L, r] using hFactorial x hxFact'
  rcases hFactX with ⟨hr, hDecay⟩
  have hVlarge :
      2 ≤ vMin * Real.rpow L (H - A_s - 24 / 100) := by
    simpa [L] using hLarge x hxLarge'
  have hI : ∀ m ∈ I, 0 < m ∧ (m : ℝ) ≤ 2 * M := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_, hmBounds⟩
    rcases hmBounds with ⟨hmLower, hmUpper⟩
    constructor
    · have hmPos : 0 < (m : ℝ) :=
        lt_of_lt_of_le hMpos (le_trans hl hmLower)
      exact_mod_cast hmPos
    · exact hmUpper.trans hrr
  have hRemainder := normalized_sieve_remainder_bound x M A_s H s₀ vMin r I
    hx₂ hMpos hr hvMin hI hMertensMass hDecay hVlower hVlarge
  have hTruncData := hTruncated x hxTrunc'
  rcases hTruncData with ⟨_, hTruncAll⟩
  have hTruncatedNorm := hTruncAll M hMx hMgt hMupper hlogM k hk
    (by simpa [L] using hkBound) χ u huLower huUpper l rr hl hlr hrr
  let phase : ℝ := if |u| ≤ Tstar then
      |u|⁻¹ + Real.rpow x (-c_m)
    else Real.exp (-L / Real.rpow (Real.log L) C₃p)
  let truncBound : ℝ := if |u| ≤ Tstar then
      4 * C_m / Real.log M * (|u|⁻¹ + Real.rpow x (-c_m))
    else
      4 * C_p / Real.log M * Real.exp (-L / Real.rpow (Real.log L) C₃p)
  have hphaseNonneg : 0 ≤ phase := by
    dsimp [phase]
    split_ifs <;> positivity
  have htruncBoundNonneg : 0 ≤ truncBound := by
    dsimp [truncBound]
    split_ifs <;> positivity
  have hTruncatedNorm' :
      ‖(∑ m ∈ I,
          (smallPrimeTruncation x r m : ℂ) *
            ((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                Real.log (m : ℝ)))‖ ≤ truncBound * M / V := by
    simpa [I, r, Tstar, L, truncBound] using hTruncatedNorm
  have hDenom : 0 < M * V := mul_pos hMpos hVpos
  have hTruncatedNormDiv :
      ‖(∑ m ∈ I,
          (smallPrimeTruncation x r m : ℂ) *
            ((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                Real.log (m : ℝ))) /
          ((M * V : ℝ) : ℂ)‖ ≤ truncBound / V ^ 2 := by
    calc
      _ = ‖(∑ m ∈ I,
            (smallPrimeTruncation x r m : ℂ) *
              ((χ (m : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                  Real.log (m : ℝ)))‖ / (M * V) := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDenom]
      _ ≤ (truncBound * M / V) / (M * V) :=
        div_le_div_of_nonneg_right hTruncatedNorm' hDenom.le
      _ = truncBound / V ^ 2 := by
        field_simp [ne_of_gt hMpos, ne_of_gt hVpos]
        <;> ring
  have hVhalf : vMin * Real.rpow L (-(1 / 2 : ℝ)) ≤ V := by
    have hpow : Real.rpow L (-(1 / 2 : ℝ)) ≤
        Real.rpow L (-(24 / 100 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
    calc
      _ ≤ vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hvMin.le
      _ ≤ V := hVlower
  have hRpowSquare :
      (Real.rpow L (-(1 / 2 : ℝ))) ^ 2 = Real.rpow L (-1) := by
    calc
      _ = Real.rpow L (-(1 / 2 : ℝ)) * Real.rpow L (-(1 / 2 : ℝ)) := by ring
      _ = Real.rpow L (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L (-1) := by congr 1 <;> norm_num
  have hInvRpow : L * Real.rpow L (-1) = 1 := by
    have hNeg : Real.rpow L (-1) = L⁻¹ := Real.rpow_neg_one L
    calc
      _ = L * L⁻¹ := congrArg (fun z : ℝ => L * z) hNeg
      _ = 1 := by field_simp [ne_of_gt hLpos]
  have hVhalfSq :
      (vMin * Real.rpow L (-(1 / 2 : ℝ))) ^ 2 ≤ V ^ 2 :=
    by
      have hApos : 0 ≤ vMin * Real.rpow L (-(1 / 2 : ℝ)) :=
        mul_nonneg hvMin.le (Real.rpow_nonneg hLpos.le _)
      exact (sq_le_sq₀ hApos hVpos.le).2 hVhalf
  have hVtermSq :
      (vMin * Real.rpow L (-(1 / 2 : ℝ))) ^ 2 =
        vMin ^ 2 * Real.rpow L (-1) := by
    rw [mul_pow, hRpowSquare]
  have hDenLower : wMin * vMin ^ 2 ≤ Real.log M * V ^ 2 := by
    have hDenEq :
        (wMin * L) * (vMin ^ 2 * Real.rpow L (-1)) = wMin * vMin ^ 2 := by
      calc
        _ = wMin * vMin ^ 2 * (L * Real.rpow L (-1)) := by ring
        _ = wMin * vMin ^ 2 := by rw [hInvRpow, mul_one]
    calc
      _ = (wMin * L) * (vMin ^ 2 * Real.rpow L (-1)) := hDenEq.symm
      _ = (wMin * L) *
          (vMin * Real.rpow L (-(1 / 2 : ℝ))) ^ 2 := by rw [hVtermSq]
      _ ≤ Real.log M * V ^ 2 :=
        mul_le_mul (by simpa [L] using hlogMlower) hVhalfSq (by positivity)
          (by positivity)
  have hDenLowerPos : 0 < wMin * vMin ^ 2 := by positivity
  have hInvDen : 1 / (Real.log M * V ^ 2) ≤ 1 / (wMin * vMin ^ 2) :=
    one_div_le_one_div_of_le hDenLowerPos hDenLower
  have hCoeffM : 4 * C_m / (Real.log M * V ^ 2) ≤ K := by
    have hNumerator : 4 * C_m ≤ 4 * max C_m C_p :=
      mul_le_mul_of_nonneg_left (le_max_left C_m C_p) (by norm_num)
    calc
      _ = (4 * C_m) * (1 / (Real.log M * V ^ 2)) := by ring
      _ ≤ (4 * max C_m C_p) * (1 / (wMin * vMin ^ 2)) :=
        mul_le_mul hNumerator hInvDen (by positivity) (by positivity)
      _ = K := by dsimp [K]; ring
  have hCoeffP : 4 * C_p / (Real.log M * V ^ 2) ≤ K := by
    have hNumerator : 4 * C_p ≤ 4 * max C_m C_p :=
      mul_le_mul_of_nonneg_left (le_max_right C_m C_p) (by norm_num)
    calc
      _ = (4 * C_p) * (1 / (Real.log M * V ^ 2)) := by ring
      _ ≤ (4 * max C_m C_p) * (1 / (wMin * vMin ^ 2)) :=
        mul_le_mul hNumerator hInvDen (by positivity) (by positivity)
      _ = K := by dsimp [K]; ring
  have hLowPhaseNonneg : 0 ≤ |u|⁻¹ + Real.rpow x (-c_m) := by
    have huAbsPos : 0 < |u| := lt_of_lt_of_le (by norm_num) huLower
    exact add_nonneg (inv_nonneg.mpr huAbsPos.le) (Real.rpow_nonneg hxpos.le _)
  have hHighPhaseNonneg :
      0 ≤ Real.exp (-L / Real.rpow (Real.log L) C₃p) := (Real.exp_pos _).le
  have hTruncatedPhase :
      ‖(∑ m ∈ I,
          (smallPrimeTruncation x r m : ℂ) *
            ((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                Real.log (m : ℝ))) /
          ((M * V : ℝ) : ℂ)‖ ≤ K * phase := by
    by_cases hu : |u| ≤ Tstar
    · calc
        _ ≤ truncBound / V ^ 2 := hTruncatedNormDiv
        _ = (4 * C_m / (Real.log M * V ^ 2)) *
              (|u|⁻¹ + Real.rpow x (-c_m)) := by
          simp [truncBound, hu]
          field_simp [ne_of_gt hlogMpos, ne_of_gt hVpos]
          <;> ring
        _ ≤ K * (|u|⁻¹ + Real.rpow x (-c_m)) :=
          mul_le_mul_of_nonneg_right hCoeffM hLowPhaseNonneg
        _ = K * phase := by simp [phase, hu]
    · calc
        _ ≤ truncBound / V ^ 2 := hTruncatedNormDiv
        _ = (4 * C_p / (Real.log M * V ^ 2)) *
              Real.exp (-L / Real.rpow (Real.log L) C₃p) := by
          simp [truncBound, hu]
          field_simp [ne_of_gt hlogMpos, ne_of_gt hVpos]
          <;> ring
        _ ≤ K * Real.exp (-L / Real.rpow (Real.log L) C₃p) :=
          mul_le_mul_of_nonneg_right hCoeffP hHighPhaseNonneg
        _ = K * phase := by simp [phase, hu]
  letI : NeZero k := ⟨by omega⟩
  let E : ℝ := Real.rpow L (-A_s)
  have hRemainder' :
      (∑ m ∈ I,
        |(if roughAbove m (roughCutoff x) then (1 : ℝ) else 0) -
          smallPrimeTruncation x r m|) / (M * V) ≤ E := by
    simpa [E] using hRemainder
  have hDiff := rough_source_truncation_error x u M V E r k χ l rr
    hMpos hVpos hlogM hl hlr hRemainder'
  have hDiff' :
      ‖roughSourceIntervalSum x k χ u l rr /
          ((M * V : ℝ) : ℂ) -
        (∑ m ∈ I,
          (smallPrimeTruncation x r m : ℂ) *
            ((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                Real.log (m : ℝ))) /
          ((M * V : ℝ) : ℂ)‖ ≤ E := by
    simpa [roughSourceIntervalSum, I, E] using hDiff
  have hSourceBound :
      ‖roughSourceIntervalSum x k χ u l rr /
          ((M * V : ℝ) : ℂ)‖ ≤ E + K * phase := by
    calc
      _ = ‖(roughSourceIntervalSum x k χ u l rr /
              ((M * V : ℝ) : ℂ) -
            (∑ m ∈ I,
              (smallPrimeTruncation x r m : ℂ) *
                ((χ (m : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                    Real.log (m : ℝ))) /
              ((M * V : ℝ) : ℂ)) +
            (∑ m ∈ I,
              (smallPrimeTruncation x r m : ℂ) *
                ((χ (m : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                    Real.log (m : ℝ))) /
              ((M * V : ℝ) : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖roughSourceIntervalSum x k χ u l rr /
              ((M * V : ℝ) : ℂ) -
            (∑ m ∈ I,
              (smallPrimeTruncation x r m : ℂ) *
                ((χ (m : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                    Real.log (m : ℝ))) /
              ((M * V : ℝ) : ℂ)‖ +
          ‖(∑ m ∈ I,
              (smallPrimeTruncation x r m : ℂ) *
                ((χ (m : ZMod k) : ℂ) *
                  Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                    Real.log (m : ℝ))) /
              ((M * V : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ E + K * phase := add_le_add hDiff' hTruncatedPhase
  simpa [L, Tstar, phase, E] using hSourceBound

/-- A discrete Abel estimate for a Lipschitz multiplier of the smooth rough
source. -/
theorem weighted_rough_source_interval_bound
    (Q : ℝ → ℝ) (x M V L wMin wMax B BQ KQ : ℝ)
    (k : ℕ) (χ : DirichletCharacter ℂ k) (u l rr : ℝ)
    (hL : 1 ≤ L) (hM : 1 < M) (hV : 0 < V)
    (hwMin : 0 < wMin) (hwMinMax : wMin < wMax)
    (hlogM : wMin * L ≤ Real.log M)
    (hlog2M : Real.log (2 * M) ≤ wMax * L)
    (hBQ : 0 ≤ BQ) (hKQ : 0 ≤ KQ)
    (hQbound : ∀ z, wMin ≤ z → z ≤ wMax → |Q z| ≤ BQ)
    (hQlip : ∀ z₁ z₂, wMin ≤ z₁ → z₁ ≤ wMax →
      wMin ≤ z₂ → z₂ ≤ wMax → |Q z₁ - Q z₂| ≤ KQ * |z₁ - z₂|)
    (hSource : ∀ l' rr', M ≤ l' → l' ≤ rr' → rr' ≤ 2 * M →
      ‖roughSourceIntervalSum x k χ u l' rr' /
          (M * V)‖ ≤ B)
    (hl : M ≤ l) (hlr : l ≤ rr) (hrr : rr ≤ 2 * M) :
    ‖(∑ m ∈ (Finset.range (⌊rr⌋₊ + 1)).filter
        (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr ∧
          roughAbove m (roughCutoff x)),
        (Q (Real.log (m : ℝ) / L) : ℂ) *
          ((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ))) /
      (M * V)‖ ≤ 2 * (BQ + KQ) * B := by
  classical
  let nLo : ℕ := ⌈l⌉₊
  let nHi : ℕ := ⌊rr⌋₊
  let n : ℕ := nHi + 1
  let I : Finset ℕ := (Finset.range n).filter (fun m : ℕ =>
    l ≤ (m : ℝ) ∧ (m : ℝ) ≤ rr ∧ roughAbove m (roughCutoff x))
  let J : Finset ℕ := (Finset.range n).filter (fun m : ℕ =>
    nLo ≤ m ∧ roughAbove m (roughCutoff x))
  let den : ℂ := (M : ℂ) * (V : ℂ)
  let f : ℕ → ℂ := fun m =>
    (χ (m : ZMod k) : ℂ) *
      Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
        Real.log (m : ℝ)
  let a : ℕ → ℂ := fun i =>
    (if nLo ≤ i ∧ roughAbove i (roughCutoff x) then f i else 0) / den
  let w : ℕ → ℝ := fun i =>
    Q (Real.log ((max nLo i : ℕ) : ℝ) / L)
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hrrNonneg : 0 ≤ rr := by
    linarith [hl, hlr, hrr]
  have hnLoCast : l ≤ (nLo : ℝ) := by
    dsimp [nLo]
    exact Nat.le_ceil l
  have hnHiCast : (nHi : ℝ) ≤ rr := by
    dsimp [nHi]
    exact Nat.floor_le hrrNonneg
  have hnLoLower : M ≤ (nLo : ℝ) := le_trans hl hnLoCast
  have hLowerEquiv (m : ℕ) : l ≤ (m : ℝ) ↔ nLo ≤ m := by
    constructor
    · intro hm
      dsimp [nLo]
      exact Nat.ceil_le.mpr hm
    · intro hm
      exact le_trans hnLoCast (Nat.cast_le.mpr hm)
  have hUpperEquiv (m : ℕ) : (m : ℝ) ≤ rr ↔ m ≤ nHi := by
    constructor
    · intro hm
      dsimp [nHi]
      exact (Nat.le_floor_iff hrrNonneg).2 hm
    · intro hm
      exact (Nat.cast_le.mpr hm).trans hnHiCast
  have hTargetFilter : I = J := by
    ext m
    simp only [I, J, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmn, hlm, hmr, hrough⟩
      exact ⟨hmn, (hLowerEquiv m).mp hlm, hrough⟩
    · rintro ⟨hmn, hnlo, hrough⟩
      exact ⟨hmn, (hLowerEquiv m).mpr hnlo,
        (hUpperEquiv m).mpr (by dsimp [n] at hmn; omega), hrough⟩
  have hB : 0 ≤ B := by
    have hSourceNorm := hSource l l hl le_rfl (le_trans hlr hrr)
    exact le_trans (norm_nonneg _) hSourceNorm
  have hQargBounds (m : ℕ) (hmLo : nLo ≤ m) (hmHi : m ≤ nHi) :
      wMin ≤ Real.log (m : ℝ) / L ∧ Real.log (m : ℝ) / L ≤ wMax := by
    have hmLower : M ≤ (m : ℝ) :=
      le_trans hl (le_trans hnLoCast (Nat.cast_le.mpr hmLo))
    have hmUpper : (m : ℝ) ≤ 2 * M :=
      le_trans (Nat.cast_le.mpr hmHi) (le_trans hnHiCast hrr)
    have hlogLower : Real.log M ≤ Real.log (m : ℝ) :=
      Real.log_le_log hMpos hmLower
    have hlogUpper : Real.log (m : ℝ) ≤ Real.log (2 * M) :=
      Real.log_le_log (lt_of_lt_of_le hMpos hmLower) hmUpper
    constructor
    · apply (le_div_iff₀ hLpos).2
      exact hlogM.trans hlogLower
    · apply (div_le_iff₀ hLpos).2
      exact hlogUpper.trans hlog2M
  change ‖(∑ m ∈ I,
      (Q (Real.log (m : ℝ) / L) : ℂ) * f m) / den‖ ≤
    2 * (BQ + KQ) * B
  by_cases hNonempty : nLo ≤ nHi
  · have hLogStep (i : ℕ) (hiLo : nLo ≤ i) :
        |Real.log ((i + 1 : ℕ) : ℝ) / L - Real.log (i : ℝ) / L| ≤
          1 / (L * M) := by
      have hiLower : M ≤ (i : ℝ) :=
        le_trans hl (le_trans hnLoCast (Nat.cast_le.mpr hiLo))
      let y : ℝ := (i : ℝ)
      have hypos : 0 < y := lt_of_lt_of_le hMpos hiLower
      have hyOne : 0 < y + 1 := by linarith
      have hlogDiv : Real.log ((y + 1) / y) =
          Real.log (y + 1) - Real.log y :=
        Real.log_div (ne_of_gt hyOne) (ne_of_gt hypos)
      have hratioPos : 0 < (y + 1) / y := div_pos (by linarith) hypos
      have hlogStep : Real.log (y + 1) - Real.log y ≤ 1 / y := by
        calc
          _ = Real.log ((y + 1) / y) := hlogDiv.symm
          _ ≤ (y + 1) / y - 1 := Real.log_le_sub_one_of_pos hratioPos
          _ = 1 / y := by field_simp [ne_of_gt hypos]; ring
      have hlogMono : Real.log y ≤ Real.log (y + 1) :=
        Real.log_le_log hypos (by linarith)
      have hInv : 1 / y ≤ 1 / M := one_div_le_one_div_of_le hMpos hiLower
      have hCastSucc : ((i + 1 : ℕ) : ℝ) = y + 1 := by simp [y]
      have hCastSelf : (i : ℝ) = y := by rfl
      calc
        _ = |(Real.log (y + 1) - Real.log y) / L| := by
          rw [hCastSucc, hCastSelf]
          congr 1 <;> ring
        _ = (Real.log (y + 1) - Real.log y) / L :=
          abs_of_nonneg (div_nonneg (sub_nonneg.mpr hlogMono) hLpos.le)
        _ ≤ (1 / y) / L := div_le_div_of_nonneg_right hlogStep hLpos.le
        _ = 1 / (L * y) := by field_simp [ne_of_gt hLpos, ne_of_gt hypos]
        _ ≤ 1 / (L * M) := by
          apply one_div_le_one_div_of_le (mul_pos hLpos hMpos)
          exact mul_le_mul_of_nonneg_left hiLower hLpos.le
    have hQargBoundsMax (i : ℕ) (hi : i < n) :
        wMin ≤ Real.log ((max nLo i : ℕ) : ℝ) / L ∧
          Real.log ((max nLo i : ℕ) : ℝ) / L ≤ wMax := by
      have hiUpper : i ≤ nHi := by
        dsimp [n] at hi
        omega
      have hmaxUpper : max nLo i ≤ nHi := (Nat.max_le).2 ⟨hNonempty, hiUpper⟩
      exact hQargBounds (max nLo i) (Nat.le_max_left _ _) hmaxUpper
    have hLastBound : |w (n - 1)| ≤ BQ := by
      have hnSub : n - 1 = nHi := by simp [n]
      have hargs := hQargBounds nHi hNonempty le_rfl
      rw [hnSub]
      change |Q (Real.log ((max nLo nHi : ℕ) : ℝ) / L)| ≤ BQ
      rw [Nat.max_eq_right hNonempty]
      exact hQbound _ hargs.1 hargs.2
    have hDelta : ∀ i ∈ Finset.range (n - 1),
        |w (i + 1) - w i| ≤ KQ / (L * M) := by
      intro i hi
      have hiNat : i < nHi := by
        have hi' := Finset.mem_range.mp hi
        dsimp [n] at hi'
        omega
      by_cases hiLo : nLo ≤ i
      · have hiNext : i + 1 ≤ nHi := by omega
        have hargs0 := hQargBounds i hiLo (Nat.le_of_lt hiNat)
        have hargs1 := hQargBounds (i + 1) (le_trans hiLo (Nat.le_succ i)) hiNext
        let z₀ : ℝ := Real.log (i : ℝ) / L
        let z₁ : ℝ := Real.log ((i + 1 : ℕ) : ℝ) / L
        have hwEq : w (i + 1) - w i = Q z₁ - Q z₀ := by
          change Q (Real.log ((max nLo (i + 1) : ℕ) : ℝ) / L) -
              Q (Real.log ((max nLo i : ℕ) : ℝ) / L) = Q z₁ - Q z₀
          rw [Nat.max_eq_right (le_trans hiLo (Nat.le_succ i)),
            Nat.max_eq_right hiLo]
        calc
          _ = |Q z₁ - Q z₀| := by rw [hwEq]
          _ ≤ KQ * |z₁ - z₀| :=
            hQlip z₁ z₀ hargs1.1 hargs1.2 hargs0.1 hargs0.2
          _ ≤ KQ / (L * M) := by
            calc
              _ ≤ KQ * (1 / (L * M)) :=
                mul_le_mul_of_nonneg_left (by simpa [z₀, z₁] using hLogStep i hiLo) hKQ
              _ = KQ / (L * M) := by ring
      · have hiNext : i + 1 ≤ nLo := by omega
        have hiCur : i ≤ nLo := le_trans (Nat.le_succ i) hiNext
        have hwEq : w (i + 1) - w i = 0 := by
          change Q (Real.log ((max nLo (i + 1) : ℕ) : ℝ) / L) -
              Q (Real.log ((max nLo i : ℕ) : ℝ) / L) = 0
          rw [Nat.max_eq_left hiNext, Nat.max_eq_left hiCur]
          ring
        rw [hwEq]
        simpa using (div_nonneg hKQ (by positivity : 0 ≤ L * M))
    have hVariationSum :
        (∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i|) ≤
          ((n - 1 : ℕ) : ℝ) * (KQ / (L * M)) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (n - 1), KQ / (L * M) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hDelta i hi
        _ = ((n - 1 : ℕ) : ℝ) * (KQ / (L * M)) := by simp
    have hnCount : ((n - 1 : ℕ) : ℝ) ≤ 2 * M := by
      have hcast : ((nHi : ℕ) : ℝ) ≤ 2 * M := le_trans hnHiCast hrr
      simpa [n] using hcast
    have hVariationCore :
        ((n - 1 : ℕ) : ℝ) * (KQ / (L * M)) ≤ 2 * KQ := by
      calc
        _ ≤ (2 * M) * (KQ / (L * M)) :=
          mul_le_mul_of_nonneg_right hnCount (by positivity)
        _ = (2 * KQ) / L := by
          field_simp [ne_of_gt hLpos, ne_of_gt hMpos]
          <;> ring
        _ ≤ 2 * KQ := div_le_self (by positivity) hL
    have hVariation : |w (n - 1)| +
        ∑ i ∈ Finset.range (n - 1), |w (i + 1) - w i| ≤
          2 * (BQ + KQ) := by
      calc
        _ ≤ BQ + 2 * KQ := add_le_add hLastBound
          (hVariationSum.trans hVariationCore)
        _ ≤ 2 * (BQ + KQ) := by nlinarith [hBQ]
    have hprefix : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, a i‖ ≤ B := by
      intro j hj
      by_cases hjLo : j ≤ nLo
      · have hzero : (∑ i ∈ Finset.range j, a i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hik := Finset.mem_range.mp hi
          have hnot : ¬ nLo ≤ i := by omega
          simp [a, hnot]
        rw [hzero]
        simpa using hB
      · have hnLo : nLo < j := Nat.lt_of_not_ge hjLo
        let l' : ℝ := (nLo : ℕ)
        let rr' : ℝ := ((j - 1 : ℕ) : ℝ)
        have hjpos : 1 ≤ j := by omega
        have hlower : M ≤ l' := by
          dsimp [l']
          exact hnLoLower
        have hlowerUpper : l' ≤ rr' := by
          have hnat : nLo ≤ j - 1 := by omega
          dsimp [l', rr']
          exact_mod_cast hnat
        have hjUpper : j - 1 ≤ nHi := by
          dsimp [n] at hj
          omega
        have hupper : rr' ≤ 2 * M := by
          have hcast : ((j - 1 : ℕ) : ℝ) ≤ (nHi : ℝ) := Nat.cast_le.mpr hjUpper
          exact le_trans hcast (le_trans hnHiCast hrr)
        have hRange : ⌊rr'⌋₊ + 1 = j := by
          dsimp [rr']
          simp [Nat.floor_natCast, Nat.sub_add_cancel hjpos]
        have hActFilter :
            (Finset.range j).filter (fun i : ℕ =>
                nLo ≤ i ∧ roughAbove i (roughCutoff x)) =
              (Finset.range (⌊rr'⌋₊ + 1)).filter (fun i : ℕ =>
                l' ≤ (i : ℝ) ∧ (i : ℝ) ≤ rr' ∧ roughAbove i (roughCutoff x)) := by
          rw [hRange]
          ext i
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨hik, hlo, hrough⟩
            have hiupper : i ≤ j - 1 := by omega
            have hlo' : l' ≤ (i : ℝ) := by
              dsimp [l']
              exact_mod_cast hlo
            have hiupper' : (i : ℝ) ≤ rr' := by
              dsimp [rr']
              exact_mod_cast hiupper
            exact ⟨hik, hlo', hiupper', hrough⟩
          · rintro ⟨hik, hlo, _, hrough⟩
            have hlo' : nLo ≤ i := by
              dsimp [l'] at hlo
              exact_mod_cast hlo
            exact ⟨hik, hlo', hrough⟩
        have hActSum :
            (∑ i ∈ Finset.range j,
              if nLo ≤ i ∧ roughAbove i (roughCutoff x) then f i else 0) =
              roughSourceIntervalSum x k χ u l' rr' := by
          change (∑ i ∈ Finset.range j,
              if nLo ≤ i ∧ roughAbove i (roughCutoff x) then f i else 0) =
            ∑ i ∈ (Finset.range (⌊rr'⌋₊ + 1)).filter (fun i : ℕ =>
              l' ≤ (i : ℝ) ∧ (i : ℝ) ≤ rr' ∧ roughAbove i (roughCutoff x)), f i
          rw [← hActFilter, Finset.sum_filter]
        have hPrefixEq :
            (∑ i ∈ Finset.range j, a i) =
              roughSourceIntervalSum x k χ u l' rr' / den := by
          calc
            _ = (∑ i ∈ Finset.range j,
                  if nLo ≤ i ∧ roughAbove i (roughCutoff x) then f i else 0) / den := by
              dsimp [a]
              rw [← Finset.sum_div]
            _ = _ := by rw [hActSum]
        have hSourcePrefix := hSource l' rr' hlower hlowerUpper hupper
        rw [hPrefixEq]
        simpa [den, Complex.ofReal_mul] using hSourcePrefix
    have hAbel := norm_sum_range_weighted_le_of_variation
      a w n B (2 * (BQ + KQ)) hB hprefix hVariation
    have hWeightedEq :
        (∑ m ∈ I, (Q (Real.log (m : ℝ) / L) : ℂ) * f m) / den =
          ∑ i ∈ Finset.range n, (w i : ℂ) * a i := by
      rw [Finset.sum_div, hTargetFilter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hAct : nLo ≤ i ∧ roughAbove i (roughCutoff x)
      · have hmax : max nLo i = i := Nat.max_eq_right hAct.1
        simp [a, w, f, hAct, hmax]
        ring
      · simp [a, hAct]
    calc
      _ = ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ := by rw [hWeightedEq]
      _ ≤ B * (2 * (BQ + KQ)) := hAbel
      _ = 2 * (BQ + KQ) * B := by ring
  · have hJempty : J = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hmRange, hmActive⟩
      rcases hmActive with ⟨hmLo, _⟩
      have hmRange' : m < nHi + 1 := by simpa [n] using hmRange
      have hmHi : m ≤ nHi := Nat.le_of_lt_succ hmRange'
      exact hNonempty (le_trans hmLo hmHi)
    rw [hTargetFilter, hJempty]
    simp
    positivity

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
