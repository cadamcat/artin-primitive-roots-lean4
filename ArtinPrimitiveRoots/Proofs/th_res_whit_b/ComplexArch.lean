import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

/-- The positive radial factor in the complex spherical section after applying `w n(z)` and a
fixed right translate. -/
def complexSphericalRatio (g : GL (Fin 2) ℂ) (z : ℂ) : ℝ :=
  ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
    (‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2)

private def complexSphericalDen (g : GL (Fin 2) ℂ) (z : ℂ) : ℝ :=
  ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
    ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2

private theorem complexSphericalDen_formula (g : GL (Fin 2) ℂ) (z : ℂ) :
    complexSphericalDen g z =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + z * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + z * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  simp [complexSphericalDen, weylM, upperM, Matrix.mul_apply, Fin.sum_univ_two]

private theorem complexSphericalRatio_num (g : GL (Fin 2) ℂ) (z : ℂ) :
    ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ =
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ := by
  change ‖((weylM ℂ).val * (upperM ℂ z).val * g.val).det‖ = ‖g.val.det‖
  have hW : ((weylM ℂ).val : Matrix (Fin 2) (Fin 2) ℂ).det = -1 := by
    simp [weylM, Matrix.det_fin_two]
  have hN : ((upperM ℂ z).val : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    simp [upperM, Matrix.det_fin_two]
  rw [Matrix.det_mul, Matrix.det_mul, hW, hN]
  simp

/-- The spherical ratio after a fixed translate is comparable to `(1+‖z‖²)⁻¹`. -/
private theorem complexSphericalRatio_bounds (g : GL (Fin 2) ℂ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z : ℂ, c / (1 + ‖z‖ ^ 2) ≤ complexSphericalRatio g z ∧
        complexSphericalRatio g z ≤ C / (1 + ‖z‖ ^ 2) := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := g
  let a := M 0 0
  let b := M 0 1
  let c₀ := M 1 0
  let d := M 1 1
  let detM : ℝ := ‖M.det‖
  let p := ‖a‖ + ‖b‖ + 1
  let q := ‖c₀‖ + ‖d‖ + 1
  let cLower := min (detM ^ 2 / (2 * q ^ 2)) (detM ^ 2 / (2 * p ^ 2)) / 2
  let cUpper := 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c₀‖ ^ 2 + ‖d‖ ^ 2) + 1
  have hdet : detM ≠ 0 := by
    dsimp [detM, M]
    exact norm_ne_zero_iff.mpr g.det_ne_zero
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hcUpper : 0 < cUpper := by
    dsimp [cUpper]
    positivity
  have hden : ∀ z : ℂ, complexSphericalDen g z =
      ‖a + z * c₀‖ ^ 2 + ‖b + z * d‖ ^ 2 := by
    intro z
    rw [complexSphericalDen_formula]
  have hdetA (z : ℂ) :
      ‖M.det‖ = ‖(a + z * c₀) * d - (b + z * d) * c₀‖ := by
    congr 1
    dsimp [M, a, b, c₀, d]
    rw [Matrix.det_fin_two]
    ring
  have hdetB (z : ℂ) :
      ‖z‖ * ‖M.det‖ = ‖(b + z * d) * a - (a + z * c₀) * b‖ := by
    have hcomplex : z * M.det = (b + z * d) * a - (a + z * c₀) * b := by
      dsimp [M, a, b, c₀, d]
      rw [Matrix.det_fin_two]
      ring
    calc
      ‖z‖ * ‖M.det‖ = ‖z * M.det‖ := by rw [norm_mul]
      _ = ‖(b + z * d) * a - (a + z * c₀) * b‖ := by rw [hcomplex]
  have hDupper (z : ℂ) : complexSphericalDen g z ≤
      (4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c₀‖ ^ 2 + ‖d‖ ^ 2) + 1) * (1 + ‖z‖ ^ 2) := by
    rw [hden z]
    have h₁ : ‖a + z * c₀‖ ≤ ‖a‖ + ‖z‖ * ‖c₀‖ := by
      calc
        ‖a + z * c₀‖ ≤ ‖a‖ + ‖z * c₀‖ := norm_add_le _ _
        _ = ‖a‖ + ‖z‖ * ‖c₀‖ := by rw [norm_mul]
    have h₂ : ‖b + z * d‖ ≤ ‖b‖ + ‖z‖ * ‖d‖ := by
      calc
        ‖b + z * d‖ ≤ ‖b‖ + ‖z * d‖ := norm_add_le _ _
        _ = ‖b‖ + ‖z‖ * ‖d‖ := by rw [norm_mul]
    have h₁sq : ‖a + z * c₀‖ ^ 2 ≤ (‖a‖ + ‖z‖ * ‖c₀‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h₁
    have h₂sq : ‖b + z * d‖ ^ 2 ≤ (‖b‖ + ‖z‖ * ‖d‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))).2 h₂
    nlinarith [h₁sq, h₂sq, sq_nonneg (‖a‖ - ‖z‖ * ‖c₀‖),
      sq_nonneg (‖b‖ - ‖z‖ * ‖d‖)]
  have hsumSq (z : ℂ) :
      (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 ≤ 2 * complexSphericalDen g z := by
    rw [hden z]
    nlinarith [sq_nonneg (‖a + z * c₀‖ - ‖b + z * d‖)]
  have hDlowerA (z : ℂ) : detM ^ 2 ≤ 2 * complexSphericalDen g z * q ^ 2 := by
    have hy₀ : 0 ≤ ‖a + z * c₀‖ := norm_nonneg _
    have hy₁ : 0 ≤ ‖b + z * d‖ := norm_nonneg _
    have hprod : ‖M.det‖ ≤
        (‖a + z * c₀‖ + ‖b + z * d‖) * q := by
      rw [hdetA]
      calc
        ‖(a + z * c₀) * d - (b + z * d) * c₀‖ ≤
            ‖(a + z * c₀) * d‖ + ‖(b + z * d) * c₀‖ := norm_sub_le _ _
        _ = ‖a + z * c₀‖ * ‖d‖ + ‖b + z * d‖ * ‖c₀‖ := by rw [norm_mul, norm_mul]
        _ ≤ (‖a + z * c₀‖ + ‖b + z * d‖) * q := by
          dsimp [q]
          nlinarith [hy₀, hy₁, norm_nonneg c₀, norm_nonneg d]
    have hprodSq' : ‖M.det‖ ^ 2 ≤
        ((‖a + z * c₀‖ + ‖b + z * d‖) * q) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (add_nonneg hy₀ hy₁) (le_of_lt hq))).2 hprod
    have hprodSq : ‖M.det‖ ^ 2 ≤
        (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * q ^ 2 := by
      calc
        ‖M.det‖ ^ 2 ≤ ((‖a + z * c₀‖ + ‖b + z * d‖) * q) ^ 2 := hprodSq'
        _ = (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * q ^ 2 := by ring
    calc
      detM ^ 2 ≤ (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * q ^ 2 := by simpa [detM] using hprodSq
      _ ≤ 2 * complexSphericalDen g z * q ^ 2 := by
        exact mul_le_mul_of_nonneg_right (hsumSq z) (sq_nonneg q)
  have hDlowerB (z : ℂ) : ‖z‖ ^ 2 * detM ^ 2 ≤
      2 * complexSphericalDen g z * p ^ 2 := by
    have hy₀ : 0 ≤ ‖a + z * c₀‖ := norm_nonneg _
    have hy₁ : 0 ≤ ‖b + z * d‖ := norm_nonneg _
    have hprod : ‖z‖ * ‖M.det‖ ≤
        (‖a + z * c₀‖ + ‖b + z * d‖) * p := by
      rw [hdetB]
      calc
        ‖(b + z * d) * a - (a + z * c₀) * b‖ ≤
            ‖(b + z * d) * a‖ + ‖(a + z * c₀) * b‖ := norm_sub_le _ _
        _ = ‖b + z * d‖ * ‖a‖ + ‖a + z * c₀‖ * ‖b‖ := by rw [norm_mul, norm_mul]
        _ ≤ (‖a + z * c₀‖ + ‖b + z * d‖) * p := by
          dsimp [p]
          nlinarith [hy₀, hy₁, norm_nonneg a, norm_nonneg b]
    have hprodSq' : (‖z‖ * ‖M.det‖) ^ 2 ≤
        ((‖a + z * c₀‖ + ‖b + z * d‖) * p) ^ 2 := by
      exact (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg (add_nonneg hy₀ hy₁) (le_of_lt hp))).2 hprod
    have hprodSq : (‖z‖ * ‖M.det‖) ^ 2 ≤
        (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * p ^ 2 := by
      calc
        (‖z‖ * ‖M.det‖) ^ 2 ≤ ((‖a + z * c₀‖ + ‖b + z * d‖) * p) ^ 2 := hprodSq'
        _ = (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * p ^ 2 := by ring
    calc
      ‖z‖ ^ 2 * detM ^ 2 ≤
          (‖a + z * c₀‖ + ‖b + z * d‖) ^ 2 * p ^ 2 := by
            simpa [detM, mul_pow] using hprodSq
      _ ≤ 2 * complexSphericalDen g z * p ^ 2 :=
            mul_le_mul_of_nonneg_right (hsumSq z) (sq_nonneg p)
  have hDlower (z : ℂ) : cLower * (1 + ‖z‖ ^ 2) ≤ complexSphericalDen g z := by
    let a₀ : ℝ := detM ^ 2 / (2 * q ^ 2)
    let a₁ : ℝ := detM ^ 2 / (2 * p ^ 2)
    have h0 : a₀ ≤ complexSphericalDen g z := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * q ^ 2)).2
      nlinarith [hDlowerA z]
    have h1 : a₁ * ‖z‖ ^ 2 ≤ complexSphericalDen g z := by
      have hp2 : 0 < 2 * p ^ 2 := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp2).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hDlowerB z
    have ha₀ : 0 < a₀ := by positivity
    have ha₁ : 0 < a₁ := by positivity
    have hmin : min a₀ a₁ * (1 + ‖z‖ ^ 2) ≤ a₀ + a₁ * ‖z‖ ^ 2 := by
      have hleft := min_le_left a₀ a₁
      have hright := min_le_right a₀ a₁
      have hmul := mul_le_mul_of_nonneg_right hright (sq_nonneg ‖z‖)
      nlinarith
    have havg : (a₀ + a₁ * ‖z‖ ^ 2) / 2 ≤ complexSphericalDen g z := by
      nlinarith [h0, h1]
    calc
      cLower * (1 + ‖z‖ ^ 2) = min a₀ a₁ * (1 + ‖z‖ ^ 2) / 2 := by
        dsimp [cLower, a₀, a₁]
        ring
      _ ≤ (a₀ + a₁ * ‖z‖ ^ 2) / 2 := by nlinarith [hmin]
      _ ≤ complexSphericalDen g z := havg
  have hcLower : 0 < cLower := by
    dsimp [cLower]
    have hdetpos : 0 < detM := by
      dsimp [detM]
      exact norm_pos_iff.mpr g.det_ne_zero
    positivity
  have hdetpos : 0 < detM := by
    dsimp [detM]
    exact norm_pos_iff.mpr g.det_ne_zero
  refine ⟨detM / cUpper, detM / cLower, div_pos hdetpos hcUpper,
    div_pos hdetpos hcLower, ?_⟩
  intro z
  have hdenpos : 0 < complexSphericalDen g z := by
    exact lt_of_lt_of_le (mul_pos hcLower (by positivity)) (hDlower z)
  have hnum : ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ).det‖ = detM := complexSphericalRatio_num g z
  have hratio : complexSphericalRatio g z = detM / complexSphericalDen g z := by
    change ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ).det‖ / complexSphericalDen g z = _
    rw [hnum]
  constructor
  · rw [hratio, div_div]
    have hdenA : 0 < cUpper * (1 + ‖z‖ ^ 2) := mul_pos hcUpper (by positivity)
    apply (div_le_div_iff₀ hdenA hdenpos).2
    exact mul_le_mul_of_nonneg_left (hDupper z) (le_of_lt hdetpos)
  · rw [hratio, div_div]
    have hdenB : 0 < cLower * (1 + ‖z‖ ^ 2) := mul_pos hcLower (by positivity)
    apply (div_le_div_iff₀ hdenpos hdenB).2
    exact mul_le_mul_of_nonneg_left (hDlower z) (le_of_lt hdetpos)

private theorem complexSphericalRatio_continuous (g : GL (Fin 2) ℂ) :
    Continuous (complexSphericalRatio g) := by
  obtain ⟨c, C, hc, hC, hb⟩ := complexSphericalRatio_bounds g
  have hpos (z : ℂ) : 0 < complexSphericalRatio g z := by
    exact lt_of_lt_of_le (div_pos hc (by positivity)) (hb z).1
  have hdenNe (z : ℂ) : complexSphericalDen g z ≠ 0 := by
    intro hz
    have hzero : complexSphericalRatio g z = 0 := by
      change _ / complexSphericalDen g z = 0
      rw [hz, div_zero]
    have hzpos := hpos z
    rw [hzero] at hzpos
    exact (lt_irrefl 0) hzpos
  have hnum : Continuous (fun z : ℂ =>
      ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖) := by
    fun_prop
  have hden : Continuous (complexSphericalDen g) := by
    have heq : complexSphericalDen g = fun z =>
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + z * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + z * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
      funext z
      exact complexSphericalDen_formula g z
    rw [heq]
    fun_prop
  change Continuous (fun z =>
    ‖((weylM ℂ * upperM ℂ z * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      complexSphericalDen g z)
  exact hnum.div hden hdenNe

private theorem complex_cpow_ofReal_norm {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ‖(r : ℂ) ^ (1 + 2 * s)‖ = r ^ (1 + 2 * s.re) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hr), Complex.norm_exp]
  rw [← Complex.ofReal_log hr.le, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.one_re, Complex.mul_re]
  norm_num
  rw [Real.rpow_def_of_pos hr]

private theorem hasDerivAt_complex_cpow_ofReal {r : ℝ} (hr : 0 < r) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (r : ℂ) ^ (1 + 2 * z))
      (((r : ℂ) ^ (1 + 2 * s)) * Complex.log (r : ℂ) * 2) s := by
  have hlin : HasDerivAt (fun z : ℂ => (1 : ℂ) + 2 * z) 2 s := by
    simpa [mul_comm, add_comm] using
      ((hasDerivAt_id s).const_mul (2 : ℂ)).add_const (1 : ℂ)
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    hlin.const_cpow (Or.inl (by exact_mod_cast ne_of_gt hr))

private def complexJacquetIntegrand (g : PGL2 ℂ) (s : ℂ) (z : ℂ) : ℂ :=
  psiC (-z) * (((complexSphericalRatio (Quotient.out g) z : ℝ) : ℂ) ^ (1 + 2 * s))

private def complexJacquetIntegrandDeriv (g : PGL2 ℂ) (s : ℂ) (z : ℂ) : ℂ :=
  psiC (-z) * (((complexSphericalRatio (Quotient.out g) z : ℝ) : ℂ) ^ (1 + 2 * s) *
    Complex.log ((complexSphericalRatio (Quotient.out g) z : ℝ) : ℂ) * 2)

private theorem complexJacquetIntegrand_continuous (g : PGL2 ℂ) (s : ℂ) :
    Continuous (fun z => complexJacquetIntegrand g s z) := by
  let ρ : ℂ → ℝ := complexSphericalRatio (Quotient.out g)
  have hρcont : Continuous ρ := complexSphericalRatio_continuous _
  have hρpos (z : ℂ) : 0 < ρ z := by
    obtain ⟨c, C, hc, hC, hb⟩ := complexSphericalRatio_bounds (Quotient.out g)
    exact lt_of_lt_of_le (div_pos hc (by positivity)) (hb z).1
  have hlogReal : Continuous (fun z => Real.log (ρ z)) :=
    hρcont.log (fun z => ne_of_gt (hρpos z))
  have hlog : Continuous (fun z => (Real.log (ρ z) : ℂ)) :=
    Complex.continuous_ofReal.comp hlogReal
  have hpow (z : ℂ) : (ρ z : ℂ) ^ (1 + 2 * s) =
      Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt (hρpos z))]
    rw [← Complex.ofReal_log (hρpos z).le]
  have hpsi : Continuous (fun z : ℂ => psiC (-z)) := by fun_prop [psiC]
  have hExp : Continuous (fun z : ℂ =>
      Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s))) := by
    exact Complex.continuous_exp.comp (hlog.mul continuous_const)
  have hEq : (fun z => complexJacquetIntegrand g s z) =
      fun z => psiC (-z) * Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s)) := by
    funext z
    simp [complexJacquetIntegrand, ρ, hpow z]
  rw [hEq]
  exact hpsi.mul hExp

private theorem complexJacquetIntegrandDeriv_continuous (g : PGL2 ℂ) (s : ℂ) :
    Continuous (fun z => complexJacquetIntegrandDeriv g s z) := by
  let ρ : ℂ → ℝ := complexSphericalRatio (Quotient.out g)
  have hρcont : Continuous ρ := complexSphericalRatio_continuous _
  have hρpos (z : ℂ) : 0 < ρ z := by
    obtain ⟨c, C, hc, hC, hb⟩ := complexSphericalRatio_bounds (Quotient.out g)
    exact lt_of_lt_of_le (div_pos hc (by positivity)) (hb z).1
  have hlogReal : Continuous (fun z => Real.log (ρ z)) :=
    hρcont.log (fun z => ne_of_gt (hρpos z))
  have hlog : Continuous (fun z => (Real.log (ρ z) : ℂ)) :=
    Complex.continuous_ofReal.comp hlogReal
  have hpow (z : ℂ) : (ρ z : ℂ) ^ (1 + 2 * s) =
      Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt (hρpos z))]
    rw [← Complex.ofReal_log (hρpos z).le]
  have hlogC (z : ℂ) : Complex.log (ρ z : ℂ) = (Real.log (ρ z) : ℂ) :=
    (Complex.ofReal_log (hρpos z).le).symm
  have hpsi : Continuous (fun z : ℂ => psiC (-z)) := by fun_prop [psiC]
  have hExp : Continuous (fun z : ℂ =>
      Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s))) := by
    exact Complex.continuous_exp.comp (hlog.mul continuous_const)
  have hEq : (fun z => complexJacquetIntegrandDeriv g s z) =
      fun z => psiC (-z) *
        (Complex.exp ((Real.log (ρ z) : ℂ) * (1 + 2 * s)) *
          (Real.log (ρ z) : ℂ) * 2) := by
    funext z
    simp [complexJacquetIntegrandDeriv, ρ, hpow z, hlogC z]
  rw [hEq]
  exact hpsi.mul ((hExp.mul hlog).mul continuous_const)

private theorem hasDerivAt_complexJacquetIntegrand (g : PGL2 ℂ) (z : ℂ) (s : ℂ)
    (hr : 0 < complexSphericalRatio (Quotient.out g) z) :
    HasDerivAt (fun s => complexJacquetIntegrand g s z)
      (complexJacquetIntegrandDeriv g s z) s := by
  simpa [complexJacquetIntegrand, complexJacquetIntegrandDeriv, mul_assoc, mul_left_comm,
    mul_comm] using
      (hasDerivAt_complex_cpow_ofReal hr s).const_mul (psiC (-z))

private theorem complexRatio_log_bound (ρ : ℂ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ z, c / (1 + ‖z‖ ^ 2) ≤ ρ z)
    (hhi : ∀ z, ρ z ≤ C / (1 + ‖z‖ ^ 2)) :
    ∀ z, |Real.log (ρ z)| ≤ |Real.log C| + |Real.log c| + Real.log (1 + ‖z‖ ^ 2) := by
  intro z
  let D := 1 + ‖z‖ ^ 2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg ‖z‖]
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hrho : 0 < ρ z := lt_of_lt_of_le (div_pos hc hDpos) (hlo z)
  have hCdiv : 0 < C / D := div_pos hC hDpos
  have hUp := Real.log_le_log hrho (hhi z)
  rw [Real.log_div hC.ne' hDpos.ne'] at hUp
  have hLow := Real.log_le_log (div_pos hc hDpos) (hlo z)
  rw [Real.log_div hc.ne' hDpos.ne'] at hLow
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hlogCabs : 0 ≤ |Real.log C| := abs_nonneg _
  have hlogcAbs : 0 ≤ |Real.log c| := abs_nonneg _
  apply abs_le.mpr
  constructor
  · have hcabs := neg_abs_le (Real.log c)
    nlinarith
  · have hCabs := le_abs_self (Real.log C)
    nlinarith

private theorem complex_rpow_radial_bound {ρ C D p p₀ p₁ : ℝ}
    (hρ : 0 < ρ) (hρC : ρ ≤ C / D) (hC : 0 < C) (hD : 1 ≤ D)
    (hp₀nonneg : 0 ≤ p₀) (hp₀p₁ : p₀ ≤ p₁)
    (hp₀ : p₀ ≤ p) (hp₁ : p ≤ p₁) :
    ρ ^ p ≤ (C ^ p₀ + C ^ p₁ + 1) * D ^ (-p₀) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hRpos : 0 < C / D := div_pos hC hDpos
  have hρle : ρ ^ p ≤ (C / D) ^ p :=
    Real.rpow_le_rpow hρ.le hρC (by linarith [hp₀nonneg, hp₀])
  have hK₀ : C ^ p₀ ≤ C ^ p₀ + C ^ p₁ + 1 := by
    nlinarith [Real.rpow_nonneg hC.le p₀, Real.rpow_nonneg hC.le p₁]
  have hK₁ : C ^ p₁ ≤ C ^ p₀ + C ^ p₁ + 1 := by
    nlinarith [Real.rpow_nonneg hC.le p₀, Real.rpow_nonneg hC.le p₁]
  by_cases hR : C / D ≤ 1
  · have hdiv : (C / D) ^ p₀ = C ^ p₀ / D ^ p₀ :=
      Real.div_rpow hC.le hDpos.le _
    calc
      ρ ^ p ≤ (C / D) ^ p := hρle
      _ ≤ (C / D) ^ p₀ := Real.rpow_le_rpow_of_exponent_ge hRpos hR hp₀
      _ = C ^ p₀ / D ^ p₀ := hdiv
      _ ≤ (C ^ p₀ + C ^ p₁ + 1) / D ^ p₀ :=
        div_le_div_of_nonneg_right hK₀ (Real.rpow_nonneg hDpos.le p₀)
      _ = (C ^ p₀ + C ^ p₁ + 1) * D ^ (-p₀) := by
        rw [Real.rpow_neg hDpos.le]
        exact div_eq_mul_inv _ _
  · have hRlarge : 1 ≤ C / D := (not_le.mp hR).le
    have hmono : (C / D) ^ p ≤ (C / D) ^ p₁ :=
      Real.rpow_le_rpow_of_exponent_le hRlarge hp₁
    have hdiv : (C / D) ^ p₁ = C ^ p₁ / D ^ p₁ :=
      Real.div_rpow hC.le hDpos.le _
    have hDpow : D ^ p₀ ≤ D ^ p₁ := Real.rpow_le_rpow_of_exponent_le hD hp₀p₁
    have hnum : C ^ p₁ * D ^ p₀ ≤ (C ^ p₀ + C ^ p₁ + 1) * D ^ p₁ := by
      calc
        C ^ p₁ * D ^ p₀ ≤ (C ^ p₀ + C ^ p₁ + 1) * D ^ p₀ :=
          mul_le_mul_of_nonneg_right hK₁ (Real.rpow_nonneg hDpos.le p₀)
        _ ≤ (C ^ p₀ + C ^ p₁ + 1) * D ^ p₁ :=
          mul_le_mul_of_nonneg_left hDpow (by positivity)
    have hdivle : C ^ p₁ / D ^ p₁ ≤ (C ^ p₀ + C ^ p₁ + 1) / D ^ p₀ := by
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hDpos _)
        (Real.rpow_pos_of_pos hDpos _)).2
      simpa [mul_comm] using hnum
    calc
      ρ ^ p ≤ (C / D) ^ p := hρle
      _ ≤ (C / D) ^ p₁ := hmono
      _ = C ^ p₁ / D ^ p₁ := hdiv
      _ ≤ (C ^ p₀ + C ^ p₁ + 1) / D ^ p₀ := hdivle
      _ = (C ^ p₀ + C ^ p₁ + 1) * D ^ (-p₀) := by
        rw [Real.rpow_neg hDpos.le]
        exact div_eq_mul_inv _ _

/-- Unfold the complex Jacquet integral of a translated spherical section to its scalar power
integral. -/
theorem jacquetC_spherical_eq_integral (s : ℂ) (g : PGL2 ℂ) :
    jacquetC (rtr g (sphC s)) =
      ∫ z : ℂ, psiC (-z) *
        (((complexSphericalRatio (Quotient.out g) z : ℝ) : ℂ) ^ (1 + 2 * s)) := by
  let g₀ : GL (Fin 2) ℂ := Quotient.out g
  have hg₀ : QuotientGroup.mk g₀ = g := Quotient.out_eq _
  unfold jacquetC rtr
  congr 1
  funext z
  have hgroup : wC * nC z * g =
      QuotientGroup.mk (weylM ℂ * upperM ℂ z * g₀) := by
    rw [← hg₀]
    simp [wC, nC, map_mul, mul_assoc]
  rw [hgroup, sphC_mk]
  rfl

private theorem hasDerivAt_jacquetC_spherical (g : PGL2 ℂ) (s : ℂ)
    (hs : 0 < s.re) :
    HasDerivAt (fun u => jacquetC (rtr g (sphC u)))
      (∫ z : ℂ, complexJacquetIntegrandDeriv g s z) s := by
  let ρ : ℂ → ℝ := complexSphericalRatio (Quotient.out g)
  let δ : ℝ := s.re / 4
  let U : Set ℂ := Metric.ball s δ
  let p₀ : ℝ := 1 + s.re
  let p₁ : ℝ := 1 + 3 * s.re
  let q : ℝ := p₀ - δ
  obtain ⟨c, C, hc, hC, hb⟩ := complexSphericalRatio_bounds (Quotient.out g)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp₀ : 0 < p₀ := by dsimp [p₀]; linarith
  have hp₀p₁ : p₀ ≤ p₁ := by dsimp [p₀, p₁]; linarith
  have hq : 1 < q := by dsimp [q, p₀, δ]; linarith
  have hρpos (z : ℂ) : 0 < ρ z := by
    have hD : 0 < 1 + ‖z‖ ^ 2 := by positivity
    exact lt_of_lt_of_le (div_pos hc hD) (by simpa [ρ] using (hb z).1)
  have hlog := complexRatio_log_bound ρ c C hc hC
    (fun z => by simpa [ρ] using (hb z).1) (fun z => by simpa [ρ] using (hb z).2)
  have hlogC : ∀ z : ℂ, Complex.log (ρ z : ℂ) = (Real.log (ρ z) : ℂ) := by
    intro z
    exact (Complex.ofReal_log (hρpos z).le).symm
  have hpsiNorm (z : ℂ) : ‖psiC (-z)‖ = 1 := by
    simp [psiC, Complex.norm_exp, Complex.mul_re]
  have hradial (u : ℂ) (hu : u ∈ U) (z : ℂ) :
      (ρ z) ^ (1 + 2 * u.re) ≤
        (C ^ p₀ + C ^ p₁ + 1) * (1 + ‖z‖ ^ 2) ^ (-p₀) := by
    have hnorm : ‖u - s‖ < δ := by
      simpa [U, Complex.dist_eq] using Metric.mem_ball.mp hu
    have hre : |u.re - s.re| < δ := by
      calc
        |u.re - s.re| = |(u - s).re| := by simp
        _ ≤ ‖u - s‖ := Complex.abs_re_le_norm _
        _ < δ := hnorm
    have hp₀nonneg : 0 ≤ p₀ := le_of_lt hp₀
    have hplow : p₀ ≤ 1 + 2 * u.re := by
      dsimp [p₀, δ] at *
      rcases abs_lt.mp hre with ⟨hlo, hhi⟩
      nlinarith [hs]
    have hphigh : 1 + 2 * u.re ≤ p₁ := by
      dsimp [p₁, δ] at *
      rcases abs_lt.mp hre with ⟨hlo, hhi⟩
      nlinarith [hs]
    let D : ℝ := 1 + ‖z‖ ^ 2
    have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg ‖z‖]
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hcomp₀ : ρ z ≤ C / D := by simpa [ρ, D] using (hb z).2
    have hρ := hρpos z
    have hbound := complex_rpow_radial_bound hρ hcomp₀ hC hD hp₀nonneg hp₀p₁ hplow hphigh
    simpa [D] using hbound
  have hlogRadial (u : ℂ) (hu : u ∈ U) (z : ℂ) :
      |Real.log (ρ z)| ≤
        (|Real.log C| + |Real.log c| + δ⁻¹) * (1 + ‖z‖ ^ 2) ^ δ := by
    let D : ℝ := 1 + ‖z‖ ^ 2
    have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg ‖z‖]
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDpow : 1 ≤ D ^ δ := Real.one_le_rpow hD (le_of_lt hδ)
    have hlogD : Real.log D ≤ D ^ δ / δ :=
      Real.log_le_rpow_div (le_of_lt hDpos) hδ
    have hM : 0 ≤ |Real.log C| + |Real.log c| := by positivity
    have hMle : |Real.log C| + |Real.log c| ≤
        (|Real.log C| + |Real.log c|) * D ^ δ := by
      simpa using mul_le_mul_of_nonneg_left hDpow hM
    have hsum : |Real.log C| + |Real.log c| + Real.log D ≤
        (|Real.log C| + |Real.log c| + δ⁻¹) * D ^ δ := by
      calc
        |Real.log C| + |Real.log c| + Real.log D ≤
            |Real.log C| + |Real.log c| + D ^ δ / δ := by
              simpa [add_comm] using add_le_add_left hlogD (|Real.log C| + |Real.log c|)
        _ = (|Real.log C| + |Real.log c|) + δ⁻¹ * D ^ δ := by
          rw [div_eq_mul_inv, mul_comm]
        _ ≤ (|Real.log C| + |Real.log c|) * D ^ δ + δ⁻¹ * D ^ δ :=
          by simpa [add_comm] using add_le_add_right hMle (δ⁻¹ * D ^ δ)
        _ = (|Real.log C| + |Real.log c| + δ⁻¹) * D ^ δ := by ring
    have hlogz := hlog z
    simpa [D] using hlogz.trans hsum
  let K₀ : ℝ := C ^ p₀ + C ^ p₁ + 1
  let K₁ : ℝ := 2 * K₀ * (|Real.log C| + |Real.log c| + δ⁻¹)
  have hFbound (u : ℂ) (hu : u ∈ U) (z : ℂ) :
      ‖complexJacquetIntegrand g u z‖ ≤ K₀ * (1 + ‖z‖ ^ 2) ^ (-p₀) := by
    have hr := hρpos z
    have hpow := complex_cpow_ofReal_norm hr u
    have hrad := hradial u hu z
    change ‖psiC (-z) * ((ρ z : ℝ) : ℂ) ^ (1 + 2 * u)‖ ≤ _
    rw [norm_mul, hpsiNorm z, hpow]
    simp only [one_mul]
    exact hrad
  have hFderivBound (u : ℂ) (hu : u ∈ U) (z : ℂ) :
      ‖complexJacquetIntegrandDeriv g u z‖ ≤ K₁ * (1 + ‖z‖ ^ 2) ^ (-q) := by
    have hr := hρpos z
    have hpow := complex_cpow_ofReal_norm hr u
    have hrad := hradial u hu z
    have hlogz := hlogRadial u hu z
    have hnorm : ‖complexJacquetIntegrandDeriv g u z‖ =
        2 * (ρ z) ^ (1 + 2 * u.re) * |Real.log (ρ z)| := by
      rw [complexJacquetIntegrandDeriv]
      change ‖psiC (-z) * (((ρ z : ℝ) : ℂ) ^ (1 + 2 * u) *
        Complex.log ((ρ z : ℝ) : ℂ) * (2 : ℂ))‖ = _
      simp only [norm_mul, hpsiNorm z]
      rw [hpow, hlogC z]
      norm_num [mul_assoc, mul_left_comm, mul_comm]
    have hmul : (ρ z) ^ (1 + 2 * u.re) * |Real.log (ρ z)| ≤
        K₀ * (1 + ‖z‖ ^ 2) ^ (-p₀) *
          ((|Real.log C| + |Real.log c| + δ⁻¹) * (1 + ‖z‖ ^ 2) ^ δ) := by
      exact mul_le_mul hrad hlogz (abs_nonneg _) (by positivity)
    have hpowmul : (1 + ‖z‖ ^ 2) ^ (-p₀) * (1 + ‖z‖ ^ 2) ^ δ =
        (1 + ‖z‖ ^ 2) ^ (-q) := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + ‖z‖ ^ 2)]
      congr 1
      dsimp [q]
      ring
    rw [hnorm]
    calc
      2 * (ρ z) ^ (1 + 2 * u.re) * |Real.log (ρ z)| ≤
          2 * (K₀ * (1 + ‖z‖ ^ 2) ^ (-p₀) *
            ((|Real.log C| + |Real.log c| + δ⁻¹) * (1 + ‖z‖ ^ 2) ^ δ)) := by
              have htwo : (0 : ℝ) ≤ 2 := by norm_num
              simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmul htwo
      _ = K₁ * (1 + ‖z‖ ^ 2) ^ (-q) := by
        calc
          _ = 2 * K₀ * (|Real.log C| + |Real.log c| + δ⁻¹) *
              ((1 + ‖z‖ ^ 2) ^ (-p₀) * (1 + ‖z‖ ^ 2) ^ δ) := by ring
          _ = K₁ * (1 + ‖z‖ ^ 2) ^ (-q) := by
            rw [hpowmul]
  have hweightInt (r : ℝ) (hr : 2 < r) :
      Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-r / 2)) volume := by
    have hdim : (Module.finrank ℝ ℂ : ℝ) < r := by
      rw [Complex.finrank_real_complex]
      exact hr
    exact integrable_rpow_neg_one_add_norm_sq (μ := volume) hdim
  have hdecay₀ : Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-p₀)) volume := by
    have h := hweightInt (2 * p₀) (by dsimp [p₀]; nlinarith [hs])
    simpa [show -(2 * p₀) / 2 = -p₀ by ring] using h
  have hdecay₁ : Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-q)) volume := by
    have h := hweightInt (2 * q) (by dsimp [q, p₀, δ]; nlinarith [hs])
    simpa [show -(2 * q) / 2 = -q by ring] using h
  have hbound₀ : Integrable (fun z : ℂ => K₀ * (1 + ‖z‖ ^ 2) ^ (-p₀)) volume := by
    simpa [mul_comm] using hdecay₀.const_mul K₀
  have hbound₁ : Integrable (fun z : ℂ => K₁ * (1 + ‖z‖ ^ 2) ^ (-q)) volume := by
    simpa [mul_comm] using hdecay₁.const_mul K₁
  have hFint : Integrable (fun z : ℂ => complexJacquetIntegrand g s z) volume := by
    have hsU : s ∈ U := by
      change s ∈ Metric.ball s δ
      exact Metric.mem_ball_self hδ
    apply hbound₀.mono' (complexJacquetIntegrand_continuous g s).aestronglyMeasurable
    filter_upwards [] with z
    simpa [K₀] using hFbound s hsU z
  have hmeas : ∀ᶠ u in 𝓝 s,
      AEStronglyMeasurable (fun z : ℂ => complexJacquetIntegrand g u z) volume :=
    Filter.Eventually.of_forall fun u =>
      (complexJacquetIntegrand_continuous g u).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂volume, ∀ u ∈ U,
      ‖complexJacquetIntegrandDeriv g u z‖ ≤ K₁ * (1 + ‖z‖ ^ 2) ^ (-q) := by
    filter_upwards [] with z
    intro u hu
    simpa [K₁] using hFderivBound u hu z
  have hdiff : ∀ᵐ z ∂volume, ∀ u ∈ U,
      HasDerivAt (fun u => complexJacquetIntegrand g u z)
        (complexJacquetIntegrandDeriv g u z) u := by
    filter_upwards [] with z
    intro u hu
    exact hasDerivAt_complexJacquetIntegrand g z u (hρpos z)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s hδ) hmeas hFint
    (complexJacquetIntegrandDeriv_continuous g s).aestronglyMeasurable
    hbound hbound₁ hdiff
  have hEq : (fun u : ℂ => jacquetC (rtr g (sphC u))) =
      fun u => ∫ z : ℂ, complexJacquetIntegrand g u z := by
    funext u
    exact jacquetC_spherical_eq_integral u g
  rw [hEq]
  exact hderiv.2

theorem jacquetC_spherical_analytic (g : PGL2 ℂ) :
    AnalyticOnNhd ℂ (fun s => jacquetC (rtr g (sphC s))) {s | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  rw [Complex.analyticOnNhd_iff_differentiableOn hopen]
  intro s hs
  exact (hasDerivAt_jacquetC_spherical g s hs).differentiableAt.differentiableWithinAt

end ArtinPrimitiveRoots.A1.Theta
