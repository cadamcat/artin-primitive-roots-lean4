import ArtinPrimitiveRoots.Spec.Main
import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.UnitaryScalar

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

/-- The spherical complex section equals the corresponding hyperbolic height power. -/
theorem sphC_sl2_height (s : ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : ℂ) (y : ℝ) (hy : 0 < y) :
    sphC s (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
      QuotientGroup.mk (upperM ℂ x) *
      QuotientGroup.mk (diagM ℂ (Units.mk0 (y : ℂ)
        (Complex.ofReal_ne_zero.mpr hy.ne')))) =
      (ArtinPrimitiveRoots.A1.Spec.height
        (γ • ArtinPrimitiveRoots.A1.Spec.pt x y) : ℂ) ^ (1 + 2 * s) := by
  let u : ℂˣ := Units.mk0 (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne')
  let a := Matrix.SpecialLinearGroup.toGL γ * upperM ℂ x * diagM ℂ u
  have ha : (a : Matrix (Fin 2) (Fin 2) ℂ) =
      (γ : Matrix (Fin 2) (Fin 2) ℂ) * !![1, x; 0, 1] * !![(y : ℂ), 0; 0, 1] := by
    rfl
  have hdet : (a : Matrix (Fin 2) (Fin 2) ℂ).det = (y : ℂ) := by
    rw [ha, Matrix.det_mul, Matrix.det_mul, γ.det_coe]
    simp [Matrix.det_fin_two]
  have hrow0 : (a : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = γ 1 0 * (y : ℂ) := by
    rw [ha]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrow1 : (a : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = γ 1 0 * x + γ 1 1 := by
    rw [ha]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_of_nonneg hy.le]
  have hbase : ‖(a : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(a : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖(a : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) =
      ArtinPrimitiveRoots.A1.Spec.height (γ • ArtinPrimitiveRoots.A1.Spec.pt x y) := by
    rw [hdet, hrow0, hrow1, ArtinPrimitiveRoots.A1.Spec.height_smul_pt γ x y hy,
      norm_mul, hny]
    simp only [Complex.normSq_eq_norm_sq]
    congr 1
    ring
  have hq : QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
      QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ u) =
      (QuotientGroup.mk a : PGL2 ℂ) := by
    simp only [a, QuotientGroup.mk_mul]
  change sphC s (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
    QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ u)) = _
  rw [hq, sphC_mk]
  unfold sphericalC
  rw [hbase]

variable {F : Type} [Field F] [NumberField F]

/-- The rational diagonal weights separate from the product of complex height factors. -/
theorem sphC_rational_arch_product [IsTotallyComplex F] (s : ℂ) (δ : Fˣ)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F)
    (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) :
    (∏ w : InfinitePlace F, sphC s
      (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding
        (diagGL δ * Matrix.SpecialLinearGroup.toGL τ)) *
      QuotientGroup.mk (upperM ℂ (x w)) *
      QuotientGroup.mk (diagM ℂ (Units.mk0 ((y w : ℝ) : ℂ)
        (Complex.ofReal_ne_zero.mpr (hy w).ne'))))) =
      (∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s)) *
        (ArtinPrimitiveRoots.A1.Spec.normHeight F
          (τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y) : ℂ) ^ (1 + 2 * s) := by
  have hup0 : upperM ℂ 0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperM]
  have hdiag (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (diagGL δ) =
        diagM ℂ (Units.map w.embedding.toMonoidHom δ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, diagM]
  have hSL (w : InfinitePlace F) :
      Matrix.GeneralLinearGroup.map w.embedding (Matrix.SpecialLinearGroup.toGL τ) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map w.embedding τ) := by
    ext i j
    rfl
  let z := τ • ArtinPrimitiveRoots.A1.Spec.ptX' F x y
  have hterm (w : InfinitePlace F) :
      sphC s (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding
        (diagGL δ * Matrix.SpecialLinearGroup.toGL τ)) *
        QuotientGroup.mk (upperM ℂ (x w)) *
        QuotientGroup.mk (diagM ℂ (Units.mk0 (y w : ℂ)
          (Complex.ofReal_ne_zero.mpr (hy w).ne')))) =
      (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s) *
        (ArtinPrimitiveRoots.A1.Spec.height (z w) : ℂ) ^ (1 + 2 * s) := by
    let ds : ℂˣ := Units.map w.embedding.toMonoidHom δ
    let γ : Matrix.SpecialLinearGroup (Fin 2) ℂ := Matrix.SpecialLinearGroup.map w.embedding τ
    let ys : ℂˣ := Units.mk0 (y w : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')
    have hcov : sphC s (QuotientGroup.mk (diagM ℂ ds) *
        QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
        QuotientGroup.mk (upperM ℂ (x w)) * QuotientGroup.mk (diagM ℂ ys)) =
      (Complex.normSq (ds : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s) *
        sphC s (QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
          QuotientGroup.mk (upperM ℂ (x w)) * QuotientGroup.mk (diagM ℂ ys)) := by
      let r : PGL2 ℂ := QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
        QuotientGroup.mk (upperM ℂ (x w)) * QuotientGroup.mk (diagM ℂ ys)
      have hlaw := (sphC_isSection s).1 0 ds r
      rw [hup0, QuotientGroup.mk_one, one_mul] at hlaw
      have he : (QuotientGroup.mk (diagM ℂ ds) : PGL2 ℂ) *
          QuotientGroup.mk (Matrix.SpecialLinearGroup.toGL γ) *
          QuotientGroup.mk (upperM ℂ (x w)) * QuotientGroup.mk (diagM ℂ ys) =
          QuotientGroup.mk (diagM ℂ ds) * r := by
        dsimp only [r]
        simp only [mul_assoc]
      rw [he]
      exact hlaw
    rw [map_mul, hdiag, hSL, QuotientGroup.mk_mul, hcov]
    have hz : z w = γ • ArtinPrimitiveRoots.A1.Spec.pt (x w) (y w) := rfl
    rw [hz]
    exact congrArg
      (fun t : ℂ => (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s) * t)
      (sphC_sl2_height s γ (x w) (y w) (hy w))
  have hpos (w : InfinitePlace F) : 0 < ArtinPrimitiveRoots.A1.Spec.height (z w) := by
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
  have hpow (T : Finset (InfinitePlace F)) :
      (∏ w ∈ T, (ArtinPrimitiveRoots.A1.Spec.height (z w) : ℂ) ^ (1 + 2 * s)) =
        ((∏ w ∈ T, ArtinPrimitiveRoots.A1.Spec.height (z w) : ℝ) : ℂ) ^ (1 + 2 * s) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert w T hw ih =>
      rw [Finset.prod_insert hw, Finset.prod_insert hw, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (hpos w).le
          (Finset.prod_nonneg (fun v _ => (hpos v).le)) (1 + 2 * s), ih]
  calc
    _ = ∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s) *
          (ArtinPrimitiveRoots.A1.Spec.height (z w) : ℂ) ^ (1 + 2 * s) :=
      Finset.prod_congr rfl (fun w _ => hterm w)
    _ = (∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s)) *
          ∏ w, (ArtinPrimitiveRoots.A1.Spec.height (z w) : ℂ) ^ (1 + 2 * s) :=
      Finset.prod_mul_distrib
    _ = _ := congrArg
      (fun t : ℂ => (∏ w : InfinitePlace F,
        (Complex.normSq (w.embedding (δ : F)) : ℂ) ^ ((1 : ℂ) / 2 + s)) * t)
      (hpow Finset.univ)

end ArtinPrimitiveRoots.A1.Theta
