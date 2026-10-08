import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Pair
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2

/-!
# Mellin form of the dual transition weight

For P2 data `P` of a square weight `f` (`P.D` the dual Mellin data on `1/2 ≤ Re u ≤ 3/2`), the
dual sum `Σ_b (T f)(y N b)` is `(1/2π) ∫ y^{-u} ζ_K(u) D(u)` on `Re u = 3/2` (Fubini over the
Dirichlet series).  The transition weight of the dual kernel,
`M/(E √x) · (Z/u) · Σ_b (T f)(Z N b/u)` with `Z = √(E x/(M A))`, is therefore
`∫ x^{-u(t)/2} g(t) dt` with `‖g(t)‖ = (M/E) c^{-1/2} ‖ζ D‖/(2π)`, `c = √(E/(MA))/u`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Complex
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSC3

open QSP2

variable {K : Type} [Field K] [NumberField K]

/-- `u(t) = 3/2 + i t`. -/
def uL (t : ℝ) : ℂ := ((3/2 : ℝ) : ℂ) + t * I

/-- The column exponent `-u(t)/2`. -/
def sT (t : ℝ) : ℂ := -(uL t) / 2

theorem uL_re (t : ℝ) : (uL t).re = 3/2 := by simp [uL]

theorem sT_re (t : ℝ) : (sT t).re = -(3/4) := by
  simp [sT, uL]; norm_num

theorem continuous_sT : Continuous sT := by
  unfold sT uL; fun_prop

theorem dual_tsum_eq [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) {y : ℝ} (hy : 0 < y) :
    ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, qsTransform K f (y * nb b) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (-(uL t)) * qsZetaCont K (uL t) * P.D (uL t) := by
  set A : ℝ := ∫ t : ℝ, ‖P.D (uL t)‖ with hA
  have hDi : Integrable (fun t : ℝ => P.D (uL t)) := integrable_D_line P (σ := 3/2)
    (by norm_num) (by norm_num)
  have hxb : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥}, 0 < y * nb b := fun b => mul_pos hy (nb_pos b)
  set Fb : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ → ℂ :=
    fun b t => ((nb b : ℝ) : ℂ) ^ (-(uL t)) * ((y : ℂ) ^ (-(uL t)) * P.D (uL t)) with hF
  have hnorm : ∀ (z : ℝ), 0 < z → ∀ t, ‖(z : ℂ) ^ (-(uL t))‖ = z ^ (-(3/2 : ℝ)) := by
    intro z hz t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hz]
    simp [uL]
  have hFn : ∀ b t, ‖Fb b t‖ = nb b ^ (-(3/2 : ℝ)) * (y ^ (-(3/2 : ℝ)) * ‖P.D (uL t)‖) := by
    intro b t
    rw [hF, norm_mul, norm_mul, hnorm _ (nb_pos b), hnorm _ hy]
  have hcont : ∀ z : ℝ, 0 < z → Continuous fun t : ℝ => (z : ℂ) ^ (-(uL t)) := by
    intro z hz
    exact Continuous.const_cpow (by unfold uL; fun_prop) (Or.inl (by exact_mod_cast hz.ne'))
  have hFi : ∀ b, Integrable (Fb b) := by
    intro b
    refine Integrable.mono' ((hDi.norm.const_mul (y ^ (-(3/2 : ℝ)))).const_mul
      (nb b ^ (-(3/2 : ℝ)))) ?_ (Filter.Eventually.of_forall fun t => le_of_eq (hFn b t))
    exact ((hcont _ (nb_pos b)).aestronglyMeasurable).mul
      (((hcont _ hy).aestronglyMeasurable).mul hDi.aestronglyMeasurable)
  have hFint : Summable (fun b => ∫ t : ℝ, ‖Fb b t‖) := by
    simp_rw [hFn, integral_const_mul]
    exact (summable_nb_rpow (K := K) (σ := 3/2) (by norm_num)).mul_right _
  have hrep : ∀ b, qsTransform K f (y * nb b) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, Fb b t := by
    intro b
    rw [transform_eq P (hxb b), mellinInv, Complex.real_smul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul, hF]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (nb_pos b).le]
    simp only [uL]
    ring
  simp_rw [hrep]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hFi hFint]
  congr 1
  congr 1
  funext t
  have hb : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥}, Fb b t =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-(uL t)) * ((y : ℂ) ^ (-(uL t)) * P.D (uL t)) := by
    intro b
    rw [hF]
    simp only [nb, Complex.ofReal_natCast]
  simp_rw [hb]
  rw [tsum_mul_right, (hasSum_norm_cpow (by rw [uL_re]; norm_num)).tsum_eq,
    ← qsZetaCont_eq_dedekindZeta (by rw [uL_re]; norm_num)]
  ring

/-- The density of the transition weight. -/
def gT (f : ℝ → ℂ) (P : P2Data K f) (M E A u : ℝ) (t : ℝ) : ℂ :=
  ((M / E * (Real.sqrt (E / (M * A)) / u) / (2 * Real.pi) : ℝ) : ℂ) *
    ((Real.sqrt (E / (M * A)) / u : ℝ) : ℂ) ^ (-(uL t)) * qsZetaCont K (uL t) * P.D (uL t)

theorem sqrt_cpow_eq {x : ℝ} (hx : 0 ≤ x) (w : ℂ) :
    ((Real.sqrt x : ℝ) : ℂ) ^ w = (x : ℂ) ^ (w / 2) := by
  rw [Real.sqrt_eq_rpow, ← Complex.cpow_mul_ofReal_nonneg hx]
  congr 1
  push_cast
  ring

/-- The transition weight as a Mellin mixture in `x = N(cd)`. -/
theorem trans_weight_eq [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) {M E A u x : ℝ}
    (hM : 0 < M) (hE : 0 < E) (hA : 0 < A) (hu : 0 < u) (hx : 0 < x) :
    ((M / (E * Real.sqrt x) : ℝ) : ℂ) * ((Real.sqrt (E * x / (M * A)) / u : ℝ) : ℂ) *
        ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          qsTransform K f (Real.sqrt (E * x / (M * A)) * nb b / u) =
      ∫ t : ℝ, (x : ℂ) ^ (sT t) * gT f P M E A u t := by
  set c₁ : ℝ := Real.sqrt (E / (M * A)) / u with hc₁
  have hc₁0 : 0 < c₁ := div_pos (Real.sqrt_pos.mpr (by positivity)) hu
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hy : Real.sqrt (E * x / (M * A)) / u = c₁ * Real.sqrt x := by
    rw [hc₁, show E * x / (M * A) = E / (M * A) * x by ring, Real.sqrt_mul (by positivity)]
    ring
  have harg : ∀ b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      Real.sqrt (E * x / (M * A)) * nb b / u = (c₁ * Real.sqrt x) * nb b := by
    intro b; rw [← hy]; ring
  simp_rw [harg]
  rw [dual_tsum_eq P (mul_pos hc₁0 hsx), hy]
  have hpre : ((M / (E * Real.sqrt x) : ℝ) : ℂ) * ((c₁ * Real.sqrt x : ℝ) : ℂ) =
      ((M / E * c₁ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [← mul_assoc, hpre, ← Complex.ofReal_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [gT]
  have hsplit : ((c₁ * Real.sqrt x : ℝ) : ℂ) ^ (-(uL t)) =
      ((c₁ : ℝ) : ℂ) ^ (-(uL t)) * (x : ℂ) ^ (sT t) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc₁0.le hsx.le, sqrt_cpow_eq hx.le]
    rfl
  rw [hsplit, ← hc₁]
  push_cast
  ring

theorem norm_gT [IsTotallyComplex K] {f : ℝ → ℂ} (P : P2Data K f) {M E A u : ℝ}
    (hM : 0 < M) (hE : 0 < E) (hA : 0 < A) (hu : 0 < u) (t : ℝ) :
    ‖gT f P M E A u t‖ ≤
      M / E * (Real.sqrt (E / (M * A)) / u) ^ (-(1/2 : ℝ)) / (2 * Real.pi) * zb K *
        ‖P.D (uL t)‖ := by
  set c₁ : ℝ := Real.sqrt (E / (M * A)) / u with hc₁
  have hc₁0 : 0 < c₁ := div_pos (Real.sqrt_pos.mpr (by positivity)) hu
  unfold gT
  rw [← hc₁, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc₁0,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hre : (-(uL t)).re = -(3/2 : ℝ) := by simp [uL]
  rw [hre]
  have hz := norm_qsZetaCont_le (K := K) (uL_re t)
  have hcc : M / E * c₁ / (2 * Real.pi) * c₁ ^ (-(3/2 : ℝ)) =
      M / E * c₁ ^ (-(1/2 : ℝ)) / (2 * Real.pi) := by
    have : c₁ * c₁ ^ (-(3/2 : ℝ)) = c₁ ^ (-(1/2 : ℝ)) := by
      have h := Real.rpow_add hc₁0 (1 : ℝ) (-(3/2 : ℝ))
      rw [Real.rpow_one] at h
      rw [← h]; norm_num
    rw [← this]; ring
  calc M / E * c₁ / (2 * Real.pi) * c₁ ^ (-(3/2 : ℝ)) * ‖qsZetaCont K (uL t)‖ * ‖P.D (uL t)‖
      = M / E * c₁ ^ (-(1/2 : ℝ)) / (2 * Real.pi) * ‖qsZetaCont K (uL t)‖ * ‖P.D (uL t)‖ := by
        rw [hcc]
    _ ≤ M / E * c₁ ^ (-(1/2 : ℝ)) / (2 * Real.pi) * zb K * ‖P.D (uL t)‖ := by
        gcongr

end ArtinPrimitiveRoots.A2.QSC3
