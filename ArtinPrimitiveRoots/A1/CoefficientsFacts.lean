import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import ArtinPrimitiveRoots.A1.Coefficients

/-!
# A1 coefficient family facts (P-COEFF)

The Gaussian transform, decay estimate, and value at zero from `02a`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The displayed definition in eq:reflection-gaussian (02a:30–32). -/
theorem PG_formula (t : ℝ) :
    PG t = (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4) := by
  rfl

/-- The absolutely convergent Mellin transform in eq:reflection-gaussian (02a:30–38).
The `IntegrableOn` conjunct records absolute convergence. -/
theorem PG_mellin (ξ : ℂ) :
    IntegrableOn (fun t : ℝ => (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) = Complex.exp (ξ ^ 2) := by
  let k : ℝ := (2 * Real.sqrt Real.pi)⁻¹
  let g : ℝ → ℂ := fun x => (k : ℂ) *
    Complex.exp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ))
  have hg : Integrable g := by
    have h := integrable_cexp_quadratic (b := (1 / 4 : ℂ)) (by norm_num) ξ 0
    have h' : Integrable (fun x : ℝ => Complex.exp
        (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ))) := by
      convert h using 1 <;> simp
    convert h'.const_mul (k : ℂ) using 1
  have hcpow (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ ξ = Complex.exp (ξ * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
    rw [Complex.ofReal_log ht.le, mul_comm]
  have hEval (t : ℝ) (ht : 0 < t) :
      (t⁻¹ : ℝ) • g (Real.log t) =
        (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) := by
    change ((t⁻¹ : ℝ) : ℂ) * g (Real.log t) = _
    dsimp only [g]
    rw [PG, hcpow t ht, Complex.exp_add]
    simp only [k, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
    have hq : -(1 / 4 : ℂ) * (Real.log t : ℂ) ^ 2 =
        ((-(Real.log t) ^ 2 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hq]
    push_cast
    rw [div_eq_mul_inv]
    field_simp
  have hInt : IntegrableOn (fun t : ℝ => (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ)) (Set.Ioi 0) := by
    have hcomp : IntegrableOn (fun t : ℝ => (t⁻¹ : ℝ) • g (Real.log t)) (Set.Ioi 0) :=
      (integrableOn_comp_log_Ioi_zero (g := g)).2 hg
    exact hcomp.congr_fun (fun t ht => hEval t ht) measurableSet_Ioi
  refine ⟨hInt, ?_⟩
  have hsubst :
      ∫ t in Set.Ioi (0 : ℝ), (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) = ∫ x, g x := by
    have := (integral_comp_log_Ioi_zero (g := g))
    rw [← this]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact (hEval t ht).symm
  rw [hsubst]
  have hgauss := integral_cexp_quadratic (b := (-(1 / 4 : ℂ))) (by norm_num) ξ 0
  dsimp only [g]
  rw [integral_const_mul]
  have hgauss' :
      ∫ x : ℝ, Complex.exp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ)) =
        ((Real.pi : ℂ) / (1 / 4 : ℂ)) ^ (1 / (2 : ℂ)) *
          Complex.exp (0 - ξ ^ 2 / (4 * -(1 / 4 : ℂ))) := by
    simpa only [add_zero, neg_neg] using hgauss
  rw [hgauss']
  have hsqrt : ((Real.pi : ℂ) / (1 / 4 : ℂ)) ^ (1 / (2 : ℂ)) =
      (2 * Real.sqrt Real.pi : ℂ) := by
    have hdiv : (Real.pi : ℂ) / (1 / 4 : ℂ) = 4 * Real.pi := by
      field_simp
    rw [hdiv]
    rw [show (4 * Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [show (1 / (2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi) (1 / 2 : ℝ)]
    norm_cast
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    norm_num
  rw [hsqrt]
  have hexp : (0 - ξ ^ 2 / (4 * -(1 / 4 : ℂ))) = ξ ^ 2 := by
    field_simp
    ring
  rw [hexp]
  have hk : (k : ℂ) * (2 * Real.sqrt Real.pi : ℂ) = 1 := by
    dsimp [k]
    rw [Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp
    norm_num
  rw [← mul_assoc, hk, one_mul]

/-- Gaussian power decay from eq:reflection-gaussian (02a:36–38). -/
theorem PG_decay (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → PG t ≤ C * Real.rpow t (-σ) := by
  refine ⟨(2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2), by positivity, ?_⟩
  intro t ht
  have hx : -(Real.log t) ^ 2 / 4 ≤ σ ^ 2 - σ * Real.log t := by
    nlinarith [sq_nonneg (Real.log t - 2 * σ)]
  have he : Real.exp (-(Real.log t) ^ 2 / 4) ≤
      Real.exp (σ ^ 2 - σ * Real.log t) := Real.exp_le_exp.mpr hx
  have hpow : Real.rpow t (-σ) = Real.exp (Real.log t * (-σ)) :=
    Real.rpow_def_of_pos ht _
  rw [PG, hpow]
  calc
    (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4) ≤
        (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2 - σ * Real.log t) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2) * Real.exp (Real.log t * (-σ)) := by
      rw [show σ ^ 2 - σ * Real.log t = σ ^ 2 + (-σ * Real.log t) by ring,
        Real.exp_add]
      rw [show -σ * Real.log t = Real.log t * (-σ) by ring]
      ring

/-- The value at zero from cf:B0 (02a:63–64). -/
theorem B0_eq_PG (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (ϑ : HeckeChar F) (cgen : S.SqfExtIdeal → F) (Z : ℝ) (hZ : 0 < Z) :
    Bm D S A ϑ cgen 0 Z = (PG (1 / Z) : ℂ) := by
  sorry

end ArtinPrimitiveRoots.A1
