import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.XiGrowth
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EXT_ZEROS.DeligneRatio
import ArtinPrimitiveRoots.Hecke.Elementary

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField ArtinPrimitiveRoots.Splitting Complex

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

set_option maxHeartbeats 1000000 in
/-- Absolute polynomial boundary bounds for the entire shifted Xi quotient. -/
theorem xiGammaQuotient_boundary_polynomial_bound
    (hdigamma : ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, 1 ≤ u.re → u.re ≤ 10 →
      ‖deriv Complex.Gamma u / Complex.Gamma u‖ ≤ C * Real.log (|u.im| + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ m : ℕ,
      ∀ (K : Type*) [Field K] [NumberField K] (s : ℂ),
        (s.re = -2 ∨ s.re = 6) →
        ‖xiGammaQuotient K s‖ ≤
          Real.exp (C * (Real.log (absoluteDiscriminant K) + (Module.finrank ℚ K : ℝ))) *
            ‖s + 10‖ ^ (m * Module.finrank ℚ K + 2) := by
  classical
  obtain ⟨A, hA, hR, hC⟩ := deligne_ratio_on_fixed_strips hdigamma
  obtain ⟨m, hm⟩ := exists_nat_gt A
  let P : ℝ := |(riemannZeta 3).re| + |(riemannZeta 6).re| + 1
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨P + 3 * (m : ℝ) + 12, by positivity, m, ?_⟩
  intro K _ _ s hs
  let n : ℕ := Module.finrank ℚ K
  let r1 : ℕ := InfinitePlace.nrRealPlaces K
  let r2 : ℕ := InfinitePlace.nrComplexPlaces K
  let d : ℝ := absoluteDiscriminant K
  have hspec := Classical.choose_spec (ArtinPrimitiveRoots.Hecke.dedekind_completed K)
  have hconjR (u : ℂ) : ‖Complex.Gammaℝ (conj u)‖ = ‖Complex.Gammaℝ u‖ := by
    simp only [Complex.Gammaℝ_def, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.conj_re]
    have hh : conj u / 2 = conj (u / 2) := by
      have htwo : conj (2 : ℂ) = 2 := by apply Complex.ext <;> norm_num
      simp [htwo]
    rw [hh, Complex.Gamma_conj, Complex.norm_conj]
  have hconjC (u : ℂ) : ‖Complex.Gammaℂ (conj u)‖ = ‖Complex.Gammaℂ u‖ := by
    have hp : 0 < 2 * Real.pi := by positivity
    have hbase : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    simp only [Complex.Gammaℂ_def, norm_mul]
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re, Complex.conj_re, Complex.Gamma_conj, Complex.norm_conj]
  have hdata : ∃ u v : ℂ, (u.re = 3 ∨ u.re = 6) ∧
      dedekindXi K s = dedekindXi K u ∧
      ‖u‖ * ‖u - 1‖ = ‖s‖ * ‖s - 1‖ ∧
      ‖Complex.Gammaℝ u‖ = ‖Complex.Gammaℝ v‖ ∧
      ‖Complex.Gammaℂ u‖ = ‖Complex.Gammaℂ v‖ ∧
      (2 ≤ v.re ∧ v.re ≤ 6) ∧ v.im = s.im ∧
      ‖v - (s + 8)‖ ≤ 12 ∧ ‖v - (s + 4)‖ ≤ 12 := by
    rcases hs with hs | hs
    · have hpoly : ‖1 - s‖ * ‖(1 - s) - 1‖ = ‖s‖ * ‖s - 1‖ := by
        rw [show 1 - s = -(s - 1) by ring, norm_neg,
          show -(s - 1) - 1 = -s by ring, norm_neg]
        ring
      have hdistR : conj (1 - s) - (s + 8) = (-3 : ℂ) := by
        apply Complex.ext <;> norm_num [hs]
      have hdistC : conj (1 - s) - (s + 4) = (1 : ℂ) := by
        apply Complex.ext <;> norm_num [hs]
      refine ⟨1 - s, conj (1 - s), Or.inl (by norm_num [hs]),
        (hspec.2.2.1 s).symm, hpoly, (hconjR _).symm, (hconjC _).symm,
        by norm_num [hs], by simp, ?_, ?_⟩
      · rw [hdistR]; norm_num
      · rw [hdistC]; norm_num
    · refine ⟨s, s, Or.inr hs, rfl, rfl, rfl, rfl,
        by norm_num [hs], rfl, ?_, ?_⟩
      · rw [show s - (s + 8) = (-8 : ℂ) by ring]; norm_num
      · rw [show s - (s + 4) = (-4 : ℂ) by ring]; norm_num
  obtain ⟨u, v, hure, hXi, hpoly, hRn, hCn, hvre, hvim, hdistR, hdistC⟩ := hdata
  have hu1 : 1 < u.re := by rcases hure with h | h <;> rw [h] <;> norm_num
  have hu6 : u.re ≤ 6 := by rcases hure with h | h <;> rw [h] <;> norm_num
  have hXiForm : dedekindXi K s = u * (u - 1) *
      ArtinPrimitiveRoots.Hecke.dedekindPrefactor K u * dedekindZeta K u :=
    hXi.trans (hspec.2.1 u hu1)
  have hzaR : 2 ≤ (s + 8).re ∧ (s + 8).re ≤ 14 := by
    rcases hs with hs | hs <;> norm_num [hs]
  have hzaC : 1 ≤ (s + 4).re ∧ (s + 4).re ≤ 10 := by
    rcases hs with hs | hs <;> norm_num [hs]
  have hgammaR : ‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ≤
      Real.exp (A * Real.log (|s.im| + 14)) := by
    rw [norm_div, hRn, ← norm_div]
    simpa using hR (s + 8) v hzaR.1 hzaR.2 hvre.1 (by linarith [hvre.2]) hdistR
  have hgammaC : ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ≤
      Real.exp (A * Real.log (|s.im| + 14)) := by
    rw [norm_div, hCn, ← norm_div]
    simpa using hC (s + 4) v (by linarith [hzaC.1]) hzaC.2
      (by linarith [hvre.1]) (by linarith [hvre.2]) hdistC
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
  have hdisc : ‖(d : ℂ) ^ (u / 2)‖ ≤ Real.exp (3 * Real.log d) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdpos, Real.rpow_def_of_pos hdpos]
    apply Real.exp_le_exp.mpr
    simp only [Complex.div_ofNat_re]
    nlinarith [mul_le_mul_of_nonneg_left hu6 hlogd]
  have huz : u = (u.re : ℂ) + u.im * Complex.I := by apply Complex.ext <;> simp
  have hzeta : ‖dedekindZeta K u‖ ≤ Real.exp ((n : ℝ) * P) := by
    have hh := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K hu1 u.im).2
    rw [← huz] at hh
    have hmajor : |(riemannZeta u.re).re| ≤ P := by
      rcases hure with h | h <;> rw [h] <;> dsimp [P] <;>
        linarith [abs_nonneg (riemannZeta 3).re, abs_nonneg (riemannZeta 6).re]
    have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
    calc
      ‖dedekindZeta K u‖ ≤ (riemannZeta u.re).re ^ n := hh
      _ ≤ |(riemannZeta u.re).re| ^ n := by
        simpa only [abs_pow] using le_abs_self ((riemannZeta u.re).re ^ n)
      _ ≤ P ^ n := pow_le_pow_left₀ (abs_nonneg _) hmajor n
      _ ≤ (Real.exp P) ^ n := pow_le_pow_left₀ hP.le hPexp n
      _ = Real.exp ((n : ℝ) * P) := (Real.exp_nat_mul P n).symm
  have hF : ‖xiGammaQuotient K s‖ = (‖s‖ * ‖s - 1‖) * ‖(d : ℂ) ^ (u / 2)‖ *
      (‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ^ r1 *
        ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ^ r2) * ‖dedekindZeta K u‖ := by
    rw [xiGammaQuotient, hXiForm, ArtinPrimitiveRoots.Hecke.dedekindPrefactor]
    simp only [norm_mul, norm_pow, norm_inv, norm_div]
    rw [hpoly]
    dsimp only [d, absoluteDiscriminant, r1, r2]
    simp only [div_eq_mul_inv]
    ring
  let x : ℝ := |s.im| + 14
  let b : ℝ := ‖s + 10‖
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [abs_nonneg s.im]
  have hx0 : 0 ≤ x := by linarith
  have hb8 : 8 ≤ b := by
    have hlow : -2 ≤ s.re := by rcases hs with hs | hs <;> rw [hs] <;> norm_num
    have hh := Complex.re_le_norm (s + 10)
    simp only [Complex.add_re] at hh
    norm_num at hh
    dsimp [b]
    linarith
  have hb0 : 0 ≤ b := by dsimp [b]; exact norm_nonneg _
  have hxb : x ≤ 3 * b := by
    have him : |s.im| ≤ b := by simpa [b] using Complex.abs_im_le_norm (s + 10)
    dsimp [x]
    linarith
  have hnorms : ‖s‖ ≤ 3 * b := by
    have hh : ‖s‖ ≤ b + 10 := by
      calc
        ‖s‖ = ‖(s + 10) - (10 : ℂ)‖ := by congr 1; ring
        _ ≤ ‖s + 10‖ + ‖(10 : ℂ)‖ := norm_sub_le _ _
        _ = b + 10 := by simp [b]
    linarith
  have hnorms1 : ‖s - 1‖ ≤ 3 * b := by
    have hh : ‖s - 1‖ ≤ b + 11 := by
      calc
        ‖s - 1‖ = ‖(s + 10) - (11 : ℂ)‖ := by congr 1; ring
        _ ≤ ‖s + 10‖ + ‖(11 : ℂ)‖ := norm_sub_le _ _
        _ = b + 11 := by simp [b]
    linarith
  have hpolyBound : ‖s‖ * ‖s - 1‖ ≤ 9 * b ^ 2 := by
    calc
      ‖s‖ * ‖s - 1‖ ≤ (3 * b) * (3 * b) :=
        mul_le_mul hnorms hnorms1 (norm_nonneg _) (by positivity)
      _ = 9 * b ^ 2 := by ring
  have hExpPow : Real.exp (A * Real.log x) ≤ x ^ m := by
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    calc
      Real.exp (A * Real.log x) ≤ Real.exp ((m : ℝ) * Real.log x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm.le hlogx)
      _ = (Real.exp (Real.log x)) ^ m := Real.exp_nat_mul _ _
      _ = x ^ m := by rw [Real.exp_log (by linarith : 0 < x)]
  have hRBound : ‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ≤ x ^ m :=
    hgammaR.trans hExpPow
  have hCBound : ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ≤ x ^ m :=
    hgammaC.trans hExpPow
  have harch : ‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ^ r1 *
      ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ^ r2 ≤ x ^ (m * n) := by
    calc
      ‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ^ r1 *
          ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ^ r2 ≤
          (x ^ m) ^ r1 * (x ^ m) ^ r2 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hRBound r1)
          (pow_le_pow_left₀ (norm_nonneg _) hCBound r2) (by positivity) (by positivity)
      _ = x ^ (m * (r1 + r2)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, Nat.mul_add]
      _ ≤ x ^ (m * n) := pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left m hplaces)
  have h3pow : (3 : ℝ) ^ (m * n) ≤ Real.exp ((3 * (m : ℝ)) * (n : ℝ)) := by
    have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc
      (3 : ℝ) ^ (m * n) ≤ (Real.exp 3) ^ (m * n) :=
        pow_le_pow_left₀ (by norm_num) hthree _
      _ = Real.exp (((m * n : ℕ) : ℝ) * 3) := (Real.exp_nat_mul 3 (m * n)).symm
      _ = Real.exp ((3 * (m : ℝ)) * (n : ℝ)) := by congr 1; push_cast; ring
  have hxpow : x ^ (m * n) ≤
      Real.exp ((3 * (m : ℝ)) * (n : ℝ)) * b ^ (m * n) := by
    calc
      x ^ (m * n) ≤ (3 * b) ^ (m * n) := pow_le_pow_left₀ hx0 hxb _
      _ = (3 : ℝ) ^ (m * n) * b ^ (m * n) := mul_pow _ _ _
      _ ≤ Real.exp ((3 * (m : ℝ)) * (n : ℝ)) * b ^ (m * n) :=
        mul_le_mul_of_nonneg_right h3pow (pow_nonneg hb0 _)
  have hfirst : (‖s‖ * ‖s - 1‖) * ‖(d : ℂ) ^ (u / 2)‖ ≤
      (9 * b ^ 2) * Real.exp (3 * Real.log d) :=
    mul_le_mul hpolyBound hdisc (norm_nonneg _) (by positivity)
  have hsecond : (‖s‖ * ‖s - 1‖) * ‖(d : ℂ) ^ (u / 2)‖ *
      (‖Complex.Gammaℝ u / Complex.Gammaℝ (s + 8)‖ ^ r1 *
        ‖Complex.Gammaℂ u / Complex.Gammaℂ (s + 4)‖ ^ r2) ≤
        (9 * b ^ 2) * Real.exp (3 * Real.log d) * x ^ (m * n) :=
    mul_le_mul hfirst harch (by positivity) (by positivity)
  have hraw : ‖xiGammaQuotient K s‖ ≤
      (9 * b ^ 2) * Real.exp (3 * Real.log d) * x ^ (m * n) * Real.exp ((n : ℝ) * P) := by
    rw [hF]
    exact mul_le_mul hsecond hzeta (norm_nonneg _) (by positivity)
  have hexp : Real.exp (3 * Real.log d) * Real.exp ((3 * (m : ℝ)) * (n : ℝ)) *
      Real.exp ((n : ℝ) * P) =
      Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hraw2 : ‖xiGammaQuotient K s‖ ≤
      9 * Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) * b ^ (m * n + 2) := by
    refine hraw.trans ?_
    calc
      (9 * b ^ 2) * Real.exp (3 * Real.log d) * x ^ (m * n) * Real.exp ((n : ℝ) * P) ≤
          (9 * b ^ 2) * Real.exp (3 * Real.log d) *
            (Real.exp ((3 * (m : ℝ)) * (n : ℝ)) * b ^ (m * n)) *
            Real.exp ((n : ℝ) * P) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxpow (by positivity)) (Real.exp_pos _).le
      _ = 9 * (Real.exp (3 * Real.log d) * Real.exp ((3 * (m : ℝ)) * (n : ℝ)) *
          Real.exp ((n : ℝ) * P)) * (b ^ (m * n) * b ^ 2) := by ring
      _ = 9 * Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) *
          b ^ (m * n + 2) := by rw [hexp, ← pow_add]
  have hcoeff : 9 * Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) ≤
      Real.exp ((P + 3 * (m : ℝ) + 12) * (Real.log d + (n : ℝ))) := by
    calc
      9 * Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) ≤
          Real.exp 9 * Real.exp (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (9 : ℝ)])
          (Real.exp_pos _).le
      _ = Real.exp (9 + (3 * Real.log d + (3 * (m : ℝ) + P) * (n : ℝ))) :=
        (Real.exp_add _ _).symm
      _ ≤ Real.exp ((P + 3 * (m : ℝ) + 12) * (Real.log d + (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hP.le hlogd, mul_nonneg (Nat.cast_nonneg m) hlogd]
  change ‖xiGammaQuotient K s‖ ≤
    Real.exp ((P + 3 * (m : ℝ) + 12) * (Real.log d + (n : ℝ))) * b ^ (m * n + 2)
  exact hraw2.trans (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hb0 _))

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
