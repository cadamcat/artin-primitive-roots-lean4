import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiBoundary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.Strip

set_option autoImplicit false

open scoped NumberField
open NumberField ArtinPrimitiveRoots.Splitting Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

set_option maxHeartbeats 2000000 in
/-- A uniform translated Jensen majorant for Xi normalized at the Euler center. -/
theorem xi_normalized_sphere_bound
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (T : ℝ),
      let c : ℂ := (2 : ℂ) + (T + 1 / 2) * Complex.I
      dedekindXi K c ≠ 0 ∧ ∀ z ∈ Metric.sphere c 4,
        ‖dedekindXi K z / dedekindXi K c‖ ≤
          Real.exp (C * (Real.log (absoluteDiscriminant K) +
            (Module.finrank ℚ K : ℝ) * Real.log (2 + |T|))) := by
  classical
  obtain ⟨B, hB, m, hboundary⟩ := xiGammaQuotient_boundary_polynomial_bound hdigamma
  obtain ⟨A, hA, hR, hC⟩ := deligne_ratio_on_fixed_strips hdigamma
  let q : ℝ := (riemannZeta 4).re / (riemannZeta 2).re
  have hq : 0 < q := div_pos
    (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 4))
    (riemannZeta_re_pos_of_one_lt (by norm_num : (1 : ℝ) < 2))
  let Q : ℝ := |Real.log q|
  let kB : ℝ := Real.log 9 / Real.log 2 + 1
  let kG : ℝ := Real.log 8 / Real.log 2 + 1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkB : 0 < kB := by dsimp [kB]; positivity
  have hkG : 0 < kG := by dsimp [kG]; positivity
  have hQ : 0 ≤ Q := abs_nonneg _
  let C : ℝ := B + (B + Q) / Real.log 2 + ((m : ℝ) + 2) * kB + A * kG + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro K _ _ T
  let c : ℂ := (2 : ℂ) + (T + 1 / 2) * Complex.I
  let n : ℕ := Module.finrank ℚ K
  let r1 : ℕ := InfinitePlace.nrRealPlaces K
  let r2 : ℕ := InfinitePlace.nrComplexPlaces K
  let d : ℝ := absoluteDiscriminant K
  have hnNat : 1 ≤ n := Nat.succ_le_iff.mpr (show 0 < n from Module.finrank_pos)
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat
  have hrank : r1 + 2 * r2 = n := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces : r1 + r2 ≤ n := by omega
  have hd1 : 1 ≤ d := by
    dsimp [d, absoluteDiscriminant]
    have hne := NumberField.discr_ne_zero K
    by_cases hpos : 0 ≤ discr K
    · rw [abs_of_nonneg (show (0 : ℝ) ≤ (discr K : ℝ) by exact_mod_cast hpos)]
      have hh : (1 : ℤ) ≤ discr K := by omega
      exact_mod_cast hh
    · rw [abs_of_neg (show (discr K : ℝ) < 0 by exact_mod_cast (lt_of_not_ge hpos))]
      have hh : (1 : ℤ) ≤ -discr K := by omega
      exact_mod_cast hh
  have hdpos : 0 < d := by linarith
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  obtain ⟨hFdiff, hFgrow⟩ := xiGammaQuotient_entire_and_growth hdigamma K
  have hstrip (w : ℂ) (hwa : -2 ≤ w.re) (hwb : w.re ≤ 6) :
      ‖xiGammaQuotient K w‖ ≤ Real.exp (B * (Real.log d + (n : ℝ))) *
        ‖w + 10‖ ^ (m * n + 2) := by
    apply polynomial_bound_on_vertical_strip
      (a := -2) (b := 6) (d := 10) (m := m * n + 2)
    · norm_num
    · norm_num
    · exact (Real.exp_pos _).le
    · exact hFdiff.diffContOnCl
    · exact hFgrow
    · intro v hv
      simpa only [n, d, Complex.ofReal_ofNat] using hboundary K v (Or.inl hv)
    · intro v hv
      simpa only [n, d, Complex.ofReal_ofNat] using hboundary K v (Or.inr hv)
    · exact hwa
    · exact hwb
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = T + 1 / 2 := by simp [c]
  have hζlow : q ^ n ≤ ‖dedekindZeta K c‖ := by
    have hh := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
      (by norm_num : (1 : ℝ) < 2) (T + 1 / 2)).1
    norm_num at hh
    simpa [q, c, n] using hh
  have hζpos : 0 < ‖dedekindZeta K c‖ := lt_of_lt_of_le (pow_pos hq _) hζlow
  have hGC (w : ℂ) (hw : 0 < w.re) : Complex.Gammaℂ w ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hw)
    simp [Real.pi_ne_zero]
  have hRc : Complex.Gammaℝ c ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hcre]; norm_num)
  have hCc : Complex.Gammaℂ c ≠ 0 := hGC c (by rw [hcre]; norm_num)
  have hRcn : 0 < ‖Complex.Gammaℝ c‖ := norm_pos_iff.mpr hRc
  have hCcn : 0 < ‖Complex.Gammaℂ c‖ := norm_pos_iff.mpr hCc
  have hcn : 1 ≤ ‖c‖ := by linarith [Complex.re_le_norm c]
  have hc1n : 1 ≤ ‖c - 1‖ := by
    have hh := Complex.re_le_norm (c - 1)
    simp only [Complex.sub_re, Complex.one_re, hcre] at hh
    linarith
  have hpoly1 : 1 ≤ ‖c‖ * ‖c - 1‖ := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ‖c‖ * ‖c - 1‖ := mul_le_mul hcn hc1n (by norm_num) (norm_nonneg _)
  have hpolyD : 1 ≤ (‖c‖ * ‖c - 1‖) * d := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (‖c‖ * ‖c - 1‖) * d :=
        mul_le_mul hpoly1 hd1 (by norm_num) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  let V : ℝ := (‖c‖ * ‖c - 1‖) * d * ‖dedekindZeta K c‖
  have hVζ : ‖dedekindZeta K c‖ ≤ V := by
    dsimp [V]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpolyD (norm_nonneg (dedekindZeta K c))
  have hVpos : 0 < V := hζpos.trans_le hVζ
  have hspec := Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)
  have hXiC : dedekindXi K c = c * (c - 1) *
      ArtinPrimitiveRoots.Hecke.dedekindPrefactor K c * dedekindZeta K c :=
    hspec.2.1 c (by rw [hcre]; norm_num)
  have hcenter : ‖dedekindXi K c‖ = V * ‖Complex.Gammaℝ c‖ ^ r1 *
      ‖Complex.Gammaℂ c‖ ^ r2 := by
    rw [hXiC, ArtinPrimitiveRoots.Hecke.dedekindPrefactor]
    simp only [norm_mul, norm_pow]
    change _ = _
    have hdcenter : ‖(d : ℂ) ^ (c / 2)‖ = d := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
      simp only [Complex.div_ofNat_re, hcre, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    change ‖c‖ * ‖c - 1‖ * (‖(d : ℂ) ^ (c / 2)‖ *
      (‖Complex.Gammaℝ c‖ ^ r1 * ‖Complex.Gammaℂ c‖ ^ r2)) * ‖dedekindZeta K c‖ = _
    rw [hdcenter]
    dsimp [V]
    ring
  have hXiNe : dedekindXi K c ≠ 0 := norm_pos_iff.mp (by
    rw [hcenter]
    exact mul_pos (mul_pos hVpos (pow_pos hRcn _)) (pow_pos hCcn _))
  refine ⟨hXiNe, ?_⟩
  intro z hz
  have hdist : ‖z - c‖ ≤ 4 := by
    have hh : dist z c = 4 := Metric.mem_sphere.mp hz
    rw [dist_eq_norm] at hh
    exact hh.le
  have hre : -2 ≤ z.re ∧ z.re ≤ 6 := by
    have hh : |z.re - 2| ≤ 4 := by
      have hb := (Complex.abs_re_le_norm (z - c)).trans hdist
      simpa only [Complex.sub_re, hcre] using hb
    rcases abs_le.mp hh with ⟨ha, hb⟩
    constructor <;> linarith
  have hRz : Complex.Gammaℝ (z + 8) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re]; norm_num; linarith [hre.1])
  have hCz : Complex.Gammaℂ (z + 4) ≠ 0 :=
    hGC _ (by simp only [Complex.add_re]; norm_num; linarith [hre.1])
  have hrestore : ‖dedekindXi K z‖ = ‖xiGammaQuotient K z‖ *
      ‖Complex.Gammaℝ (z + 8)‖ ^ r1 * ‖Complex.Gammaℂ (z + 4)‖ ^ r2 := by
    simp only [xiGammaQuotient, norm_mul, norm_pow, norm_inv, inv_pow]
    dsimp only [r1, r2]
    field_simp [norm_ne_zero_iff.mpr hRz, norm_ne_zero_iff.mpr hCz]
  have hnormratio : ‖dedekindXi K z / dedekindXi K c‖ =
      (‖xiGammaQuotient K z‖ *
        (‖Complex.Gammaℝ (z + 8) / Complex.Gammaℝ c‖ ^ r1 *
          ‖Complex.Gammaℂ (z + 4) / Complex.Gammaℂ c‖ ^ r2)) / V := by
    rw [norm_div, hrestore, hcenter]
    simp only [norm_div, norm_mul, norm_inv, norm_pow]
    simp only [div_pow, div_eq_mul_inv, inv_pow]
    ring
  have hqi : q⁻¹ ≤ Real.exp Q := by
    have heq : q⁻¹ = Real.exp (-Real.log q) := by rw [Real.exp_neg, Real.exp_log hq]
    rw [heq]
    exact Real.exp_le_exp.mpr (by dsimp [Q]; exact neg_le_abs _)
  have hVinv : V⁻¹ ≤ Real.exp (Q * (n : ℝ)) := by
    have hVlow : q ^ n ≤ V := hζlow.trans hVζ
    calc
      V⁻¹ ≤ (q ^ n)⁻¹ := by
        simpa only [one_div] using div_le_div_of_nonneg_left
          (by norm_num : (0 : ℝ) ≤ 1) (pow_pos hq n) hVlow
      _ = (q⁻¹) ^ n := (inv_pow _ _).symm
      _ ≤ (Real.exp Q) ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hq.le) hqi n
      _ = Real.exp ((n : ℝ) * Q) := (Real.exp_nat_mul Q n).symm
      _ = Real.exp (Q * (n : ℝ)) := by rw [mul_comm]
  let l : ℝ := Real.log (2 + |T|)
  have hl2 : Real.log (2 : ℝ) ≤ l :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
  have hl : 0 ≤ l := hlog2.le.trans hl2
  have hlogCompare (a u v : ℝ) (ha : 1 ≤ a) (hu : 0 < u) (hv : 2 ≤ v)
      (huv : u ≤ a * v) : Real.log u ≤ (Real.log a / Real.log 2 + 1) * Real.log v := by
    have hloga : 0 ≤ Real.log a := Real.log_nonneg ha
    have hlogv : Real.log (2 : ℝ) ≤ Real.log v := Real.log_le_log (by norm_num) hv
    have hterm : Real.log a ≤ (Real.log a / Real.log 2) * Real.log v := by
      calc
        Real.log a = (Real.log a / Real.log 2) * Real.log 2 := by field_simp [hlog2.ne']
        _ ≤ (Real.log a / Real.log 2) * Real.log v :=
          mul_le_mul_of_nonneg_left hlogv (div_nonneg hloga hlog2.le)
    calc
      Real.log u ≤ Real.log (a * v) := Real.log_le_log hu huv
      _ = Real.log a + Real.log v := Real.log_mul (by linarith) (by linarith)
      _ ≤ (Real.log a / Real.log 2 + 1) * Real.log v := by nlinarith
  have hT : |T + 1 / 2| ≤ |T| + 1 / 2 := by
    have hh := abs_add_le T (1 / 2 : ℝ)
    norm_num at hh
    exact hh
  have hlogB : Real.log (17 + |T|) ≤ kB * l := hlogCompare 9 (17 + |T|) (2 + |T|)
    (by norm_num) (by positivity) (by linarith [abs_nonneg T]) (by linarith [abs_nonneg T])
  have hlogG : Real.log (|T + 1 / 2| + 14) ≤ kG * l :=
    hlogCompare 8 (|T + 1 / 2| + 14) (2 + |T|) (by norm_num) (by positivity)
      (by linarith [abs_nonneg T]) (by linarith [abs_nonneg T])
  have hcUpper : ‖c + 10‖ ≤ 12 + |T + 1 / 2| := by
    have heq : c + 10 = (12 : ℂ) + ((T + 1 / 2 : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    rw [heq]
    refine (norm_add_le _ _).trans_eq ?_
    have hcast : ‖((T + 1 / 2 : ℝ) : ℂ)‖ = |T + 1 / 2| :=
      @RCLike.norm_ofReal ℂ inferInstance (T + 1 / 2)
    rw [norm_mul, Complex.norm_I, mul_one, hcast]
    norm_num
  have hzUpper : ‖z + 10‖ ≤ 17 + |T| := by
    calc
      ‖z + 10‖ = ‖(z - c) + (c + 10)‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖c + 10‖ := norm_add_le _ _
      _ ≤ 4 + (12 + |T + 1 / 2|) := add_le_add hdist hcUpper
      _ ≤ 17 + |T| := by linarith
  have hpoly : ‖z + 10‖ ^ (m * n + 2) ≤
      Real.exp ((((m : ℝ) + 2) * kB) * ((n : ℝ) * l)) := by
    have hexp : ((m * n + 2 : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * (n : ℝ) := by
      push_cast
      nlinarith
    calc
      ‖z + 10‖ ^ (m * n + 2) ≤ (17 + |T|) ^ (m * n + 2) :=
        pow_le_pow_left₀ (norm_nonneg _) hzUpper _
      _ = Real.exp (((m * n + 2 : ℕ) : ℝ) * Real.log (17 + |T|)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
      _ ≤ Real.exp (((m * n + 2 : ℕ) : ℝ) * (kB * l)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg _))
      _ ≤ Real.exp ((((m : ℝ) + 2) * (n : ℝ)) * (kB * l)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp (mul_nonneg hkB.le hl))
      _ = Real.exp ((((m : ℝ) + 2) * kB) * ((n : ℝ) * l)) := by congr 1; ring
  have hdistR : ‖(z + 8) - c‖ ≤ 12 := by
    calc
      ‖(z + 8) - c‖ = ‖(z - c) + 8‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖(8 : ℂ)‖ := norm_add_le _ _
      _ ≤ 12 := by norm_num; linarith
  have hdistC : ‖(z + 4) - c‖ ≤ 12 := by
    calc
      ‖(z + 4) - c‖ = ‖(z - c) + 4‖ := by congr 1; ring
      _ ≤ ‖z - c‖ + ‖(4 : ℂ)‖ := norm_add_le _ _
      _ ≤ 12 := by norm_num; linarith
  have hGR : ‖Complex.Gammaℝ (z + 8) / Complex.Gammaℝ c‖ ≤
      Real.exp (A * Real.log (|T + 1 / 2| + 14)) := by
    simpa only [hcim] using hR c (z + 8) (by rw [hcre]) (by rw [hcre]; norm_num)
      (by norm_num; linarith [hre.1]) (by norm_num; linarith [hre.2]) hdistR
  have hGCratio : ‖Complex.Gammaℂ (z + 4) / Complex.Gammaℂ c‖ ≤
      Real.exp (A * Real.log (|T + 1 / 2| + 14)) := by
    simpa only [hcim] using hC c (z + 4) (by rw [hcre]; norm_num) (by rw [hcre]; norm_num)
      (by norm_num; linarith [hre.1]) (by norm_num; linarith [hre.2]) hdistC
  have harch : ‖Complex.Gammaℝ (z + 8) / Complex.Gammaℝ c‖ ^ r1 *
      ‖Complex.Gammaℂ (z + 4) / Complex.Gammaℂ c‖ ^ r2 ≤
      Real.exp ((A * kG) * ((n : ℝ) * l)) := by
    have hlogX : 0 ≤ Real.log (|T + 1 / 2| + 14) :=
      Real.log_nonneg (by linarith [abs_nonneg (T + 1 / 2)])
    have hcount : ((r1 + r2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hplaces
    calc
      ‖Complex.Gammaℝ (z + 8) / Complex.Gammaℝ c‖ ^ r1 *
          ‖Complex.Gammaℂ (z + 4) / Complex.Gammaℂ c‖ ^ r2 ≤
          (Real.exp (A * Real.log (|T + 1 / 2| + 14))) ^ r1 *
            (Real.exp (A * Real.log (|T + 1 / 2| + 14))) ^ r2 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hGR r1)
          (pow_le_pow_left₀ (norm_nonneg _) hGCratio r2) (by positivity) (by positivity)
      _ = Real.exp (((r1 + r2 : ℕ) : ℝ) * (A * Real.log (|T + 1 / 2| + 14))) := by
        rw [← pow_add, ← Real.exp_nat_mul]
      _ ≤ Real.exp ((n : ℝ) * (A * Real.log (|T + 1 / 2| + 14))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcount (mul_nonneg hA.le hlogX))
      _ ≤ Real.exp ((n : ℝ) * (A * (kG * l))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlogG hA.le) (Nat.cast_nonneg n))
      _ = Real.exp ((A * kG) * ((n : ℝ) * l)) := by congr 1; ring
  have hF : ‖xiGammaQuotient K z‖ ≤ Real.exp (B * (Real.log d + (n : ℝ))) *
      Real.exp ((((m : ℝ) + 2) * kB) * ((n : ℝ) * l)) :=
    (hstrip z hre.1 hre.2).trans (mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le)
  have hraw : ‖dedekindXi K z / dedekindXi K c‖ ≤
      (Real.exp (B * (Real.log d + (n : ℝ))) *
        Real.exp ((((m : ℝ) + 2) * kB) * ((n : ℝ) * l))) *
        Real.exp ((A * kG) * ((n : ℝ) * l)) * Real.exp (Q * (n : ℝ)) := by
    rw [hnormratio, div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul hF harch (by positivity) (by positivity)) hVinv
      (inv_nonneg.mpr hVpos.le) (by positivity)
  have hbase : (B + Q) * (n : ℝ) ≤ ((B + Q) / Real.log 2) * ((n : ℝ) * l) := by
    have ht : B + Q ≤ ((B + Q) / Real.log 2) * l := by
      calc
        B + Q = ((B + Q) / Real.log 2) * Real.log 2 := by field_simp [hlog2.ne']
        _ ≤ ((B + Q) / Real.log 2) * l :=
          mul_le_mul_of_nonneg_left hl2 (div_nonneg (add_nonneg hB.le hQ) hlog2.le)
    calc
      (B + Q) * (n : ℝ) ≤ (((B + Q) / Real.log 2) * l) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg n)
      _ = ((B + Q) / Real.log 2) * ((n : ℝ) * l) := by ring
  have hCB : B ≤ C := by
    dsimp [C]
    have hp : 0 ≤ (B + Q) / Real.log 2 := div_nonneg (add_nonneg hB.le hQ) hlog2.le
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2) hkB.le,
      mul_nonneg hA.le hkG.le]
  have hCC : (B + Q) / Real.log 2 + ((m : ℝ) + 2) * kB + A * kG ≤ C := by
    dsimp [C]
    linarith
  have hfinal : B * (Real.log d + (n : ℝ)) +
      (((m : ℝ) + 2) * kB) * ((n : ℝ) * l) + (A * kG) * ((n : ℝ) * l) + Q * (n : ℝ) ≤
      C * (Real.log d + (n : ℝ) * l) := by
    calc
      B * (Real.log d + (n : ℝ)) + (((m : ℝ) + 2) * kB) * ((n : ℝ) * l) +
          (A * kG) * ((n : ℝ) * l) + Q * (n : ℝ) =
          B * Real.log d + (B + Q) * (n : ℝ) +
            ((((m : ℝ) + 2) * kB) + A * kG) * ((n : ℝ) * l) := by ring
      _ ≤ B * Real.log d + ((B + Q) / Real.log 2) * ((n : ℝ) * l) +
          ((((m : ℝ) + 2) * kB) + A * kG) * ((n : ℝ) * l) := by linarith [hbase]
      _ = B * Real.log d + ((B + Q) / Real.log 2 + ((m : ℝ) + 2) * kB + A * kG) *
          ((n : ℝ) * l) := by ring
      _ ≤ C * Real.log d + C * ((n : ℝ) * l) := add_le_add
        (mul_le_mul_of_nonneg_right hCB hlogd)
        (mul_le_mul_of_nonneg_right hCC (mul_nonneg (Nat.cast_nonneg n) hl))
      _ = C * (Real.log d + (n : ℝ) * l) := by ring
  change ‖dedekindXi K z / dedekindXi K c‖ ≤ Real.exp (C * (Real.log d + (n : ℝ) * l))
  refine hraw.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hfinal

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
