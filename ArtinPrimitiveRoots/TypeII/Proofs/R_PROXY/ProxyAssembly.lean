import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.PhaseBounds

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

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
