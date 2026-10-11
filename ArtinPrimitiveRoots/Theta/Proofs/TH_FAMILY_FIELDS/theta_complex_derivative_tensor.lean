import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem thetaWhit_arch_factor {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (r : P.RP)
    (hr : ∀ v, v ∉ S.Sf → P.compF v r = 1)
    (z : InfinitePlace F → ℂ) :
    thetaWhit B.C (P.q r * nInf P z) =
      N.Λ (fun v => jacquet (P.loc v.1) A (N.μ v.1)
        (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))) *
      ∏ w, jacquetC (rtr (P.compC w r * nC (z w)) (sphC (1 / 6))) := by
  classical
  let u : S.FS := (fun _ => 0, z)
  obtain ⟨x, hxq, hxF, hxC⟩ := P.nS_components u
  have hxF1 (v : FinPlace F) : P.compF v x = 1 := by
    rw [hxF v]
    by_cases hv : v ∈ S.Sf
    · simp [u, hv]
    · simp [hv]
  have hq : P.q (r * x) = P.q r * nInf P z := by
    rw [(P.q).map_mul, hxq]
    rfl
  have hF (v : FinPlace F) : P.compF v (r * x) = P.compF v r := by
    rw [(P.compF v).map_mul, hxF1 v, mul_one]
  have hC (w : InfinitePlace F) :
      P.compC w (r * x) = P.compC w r * nC (z w) := by
    rw [(P.compC w).map_mul, hxC w]
    rfl
  have h := N.coefficient B.Fam B.C (r * x) B.level B.exterior_section
    (fun v hv => by rw [hF v, hr v hv])
  rw [hq] at h
  simpa only [hF, hC] using h

private def thetaRootDerivative (m : ℤ) (f : ℂ → ℂ) : ℂ :=
  fderiv ℝ f 0 1 - (m : ℂ) * Complex.I * fderiv ℝ f 0 Complex.I

private def thetaGroupDerivativeFold {P : CoverPackage D S H A}
    (m : InfinitePlace F → ℤ) (l : List (InfinitePlace F))
    (Ψ : P.tc.G → ℂ) : P.tc.G → ℂ :=
  l.foldr (fun w acc g =>
    thetaRootDerivative (m w) (fun z => acc (g * nInf P (Pi.single w z)))) Ψ

private def thetaCoordinateDerivativeFold (m : InfinitePlace F → ℤ)
    (l : List (InfinitePlace F)) (f : (InfinitePlace F → ℂ) → ℂ)
    (z : InfinitePlace F → ℂ) : ℂ :=
  l.foldr (fun w acc z =>
    thetaRootDerivative (m w) (fun t => acc (z + Pi.single w t))) f z

private theorem thetaNInf_add {P : CoverPackage D S H A}
    (x y : InfinitePlace F → ℂ) : nInf P x * nInf P y = nInf P (x + y) := by
  change P.tc.nS (Multiplicative.ofAdd (0, x)) *
      P.tc.nS (Multiplicative.ofAdd (0, y)) =
    P.tc.nS (Multiplicative.ofAdd (0, x + y))
  rw [← map_mul, ← ofAdd_add]
  congr 1
  have hpair : ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) +
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), y) =
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + y) := by
    apply Prod.ext
    · funext v
      simp
    · rfl
  rw [hpair]

private theorem thetaRootDerivative_congr (m : ℤ) {f g : ℂ → ℂ} (h : f = g) :
    thetaRootDerivative m f = thetaRootDerivative m g := by
  rw [h]

private theorem thetaCoordinateDerivativeFold_shift (m : InfinitePlace F → ℤ)
    (l : List (InfinitePlace F)) (f : (InfinitePlace F → ℂ) → ℂ)
    (a z : InfinitePlace F → ℂ) :
    thetaCoordinateDerivativeFold m l (fun x => f (a + x)) z =
      thetaCoordinateDerivativeFold m l f (a + z) := by
  induction l generalizing z with
  | nil => rfl
  | cons w l ih =>
      change thetaRootDerivative (m w) (fun t =>
        thetaCoordinateDerivativeFold m l (fun x => f (a + x)) (z + Pi.single w t)) =
        thetaRootDerivative (m w) (fun t =>
          thetaCoordinateDerivativeFold m l f (a + z + Pi.single w t))
      apply thetaRootDerivative_congr
      funext t
      rw [ih]
      congr 1
      simp [add_assoc]

private theorem thetaPiSingle_apply (w v : InfinitePlace F) (t : ℂ) :
    (Pi.single w t : InfinitePlace F → ℂ) v = if v = w then t else 0 := by
  simp [Pi.single_apply]

private theorem thetaGroupDerivativeFold_eq_coordinate
    {P : CoverPackage D S H A} (m : InfinitePlace F → ℤ)
    (l : List (InfinitePlace F)) (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (f : (InfinitePlace F → ℂ) → ℂ)
    (hf : ∀ z, Ψ (g * nInf P z) = f z) :
    thetaGroupDerivativeFold m l Ψ g = thetaCoordinateDerivativeFold m l f 0 := by
  induction l generalizing g f with
  | nil =>
      have h0 : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
        change P.tc.nS (Multiplicative.ofAdd (0 : S.FS)) = 1
        simp
      simpa [thetaGroupDerivativeFold, thetaCoordinateDerivativeFold, h0] using hf 0
  | cons w l ih =>
      have hshift (t : ℂ) (z : InfinitePlace F → ℂ) :
          Ψ ((g * nInf P (Pi.single w t)) * nInf P z) =
            f (Pi.single w t + z) := by
        calc
          Ψ ((g * nInf P (Pi.single w t)) * nInf P z) =
              Ψ (g * (nInf P (Pi.single w t) * nInf P z)) := by rw [mul_assoc]
          _ = Ψ (g * nInf P (Pi.single w t + z)) := by rw [thetaNInf_add]
          _ = f (Pi.single w t + z) := hf _
      have hfun :
          (fun t => thetaGroupDerivativeFold m l Ψ
            (g * nInf P (Pi.single w t))) =
          fun t => thetaCoordinateDerivativeFold m l f (Pi.single w t) := by
        funext t
        calc
          thetaGroupDerivativeFold m l Ψ (g * nInf P (Pi.single w t)) =
              thetaCoordinateDerivativeFold m l (fun z => f (Pi.single w t + z)) 0 :=
            ih (g * nInf P (Pi.single w t)) (fun z => f (Pi.single w t + z)) (hshift t)
          _ = thetaCoordinateDerivativeFold m l f (Pi.single w t) :=
            by simpa using thetaCoordinateDerivativeFold_shift m l f (Pi.single w t) 0
      simp only [thetaGroupDerivativeFold, thetaCoordinateDerivativeFold, List.foldr]
      simpa [thetaGroupDerivativeFold, thetaCoordinateDerivativeFold] using
        thetaRootDerivative_congr (m w) hfun

private theorem thetaCoordinateDerivativeFold_product
    (m : InfinitePlace F → ℤ) (l : List (InfinitePlace F))
    (hl : l.Nodup) (c : ℂ) (J : InfinitePlace F → ℂ → ℂ)
    (d : InfinitePlace F → ℂ)
    (hD : ∀ w, thetaRootDerivative (m w) (J w) = d w)
    (z : InfinitePlace F → ℂ) (hz : ∀ w ∈ l, z w = 0) :
    thetaCoordinateDerivativeFold m l
        (fun x => c * ∏ w : InfinitePlace F, J w (x w)) z =
      c * l.toFinset.prod d *
        (Finset.univ \ l.toFinset).prod (fun w => J w (z w)) := by
  induction l generalizing z with
  | nil =>
      simp [thetaCoordinateDerivativeFold]
  | cons w l ih =>
      rcases List.nodup_cons.mp hl with ⟨hnot, hl⟩
      have hzw : z w = 0 := hz w (by simp)
      let T : Finset (InfinitePlace F) := Finset.univ \ l.toFinset
      have hwT : w ∈ T := by simp [T, hnot]
      have hnot' : w ∉ l.toFinset := by simpa using hnot
      have hzTail (t : ℂ) : ∀ v ∈ l,
          (z + (Pi.single w t : InfinitePlace F → ℂ)) v = 0 := by
        intro v hv
        have hvne : v ≠ w := fun h => hnot (h ▸ hv)
        simp [Pi.add_apply, Pi.single_apply, hvne, hz v (by simp [hv])]
      have hsplit (t : ℂ) :
          T.prod (fun v => J v ((z + (Pi.single w t : InfinitePlace F → ℂ)) v)) =
            J w t * (T.erase w).prod (fun v => J v (z v)) := by
        rw [← Finset.mul_prod_erase T _ hwT]
        congr 1
        · simp [Pi.add_apply, Pi.single_apply, hzw]
        · apply Finset.prod_congr rfl
          intro v hv
          have hvne : v ≠ w := (Finset.mem_erase.mp hv).1
          simp [Pi.add_apply, Pi.single_apply, hvne]
      let K : ℂ := c * l.toFinset.prod d *
        (T.erase w).prod (fun v => J v (z v))
      have hfun :
          (fun t => thetaCoordinateDerivativeFold m l
            (fun x => c * ∏ v : InfinitePlace F, J v (x v))
            (z + (Pi.single w t : InfinitePlace F → ℂ))) = fun t => K * J w t := by
        funext t
        rw [ih hl (z + (Pi.single w t : InfinitePlace F → ℂ)) (hzTail t), hsplit t]
        simp only [K]
        ring
      have hroot := thetaRootDerivative_congr (m w) hfun
      change thetaRootDerivative (m w)
        (fun t => thetaCoordinateDerivativeFold m l
          (fun x => c * ∏ v : InfinitePlace F, J v (x v))
          (z + (Pi.single w t : InfinitePlace F → ℂ))) = _
      rw [hroot]
      have hK : thetaRootDerivative (m w) (fun t => K * J w t) = K * d w := by
        by_cases hK0 : K = 0
        · have hKzero : K = 0 := by simpa [K] using hK0
          have hfun0 : (fun t => K * J w t) = fun _ => 0 := by
            funext t
            simp [hKzero]
          rw [thetaRootDerivative_congr (m w) hfun0]
          simp [thetaRootDerivative, hKzero]
        · letI : Invertible K := invertibleOfNonzero hK0
          have hscale (v : ℂ) :
              fderiv ℝ (fun t => K * J w t) 0 v =
                K * fderiv ℝ (J w) 0 v := by
            change fderiv ℝ (K • J w) 0 v = _
            rw [fderiv_const_smul_of_invertible (𝕜 := ℝ) K]
            simp [smul_eq_mul]
          unfold thetaRootDerivative at hD ⊢
          rw [hscale 1, hscale Complex.I]
          calc
            _ = K * (fderiv ℝ (J w) 0 1 -
                (m w : ℂ) * Complex.I * fderiv ℝ (J w) 0 Complex.I) := by ring
            _ = K * d w := by rw [← hD w]
      have hcomp : Finset.univ \ (insert w l.toFinset) = T.erase w := by
        ext v
        simp [T, hnot]
      calc
        _ = K * d w := hK
        _ = c * (w :: l).toFinset.prod d *
            (Finset.univ \ (w :: l).toFinset).prod (fun v => J v (z v)) := by
              simp only [List.toFinset_cons]
              rw [hcomp, Finset.prod_insert hnot']
              simp only [K, T]
              ring

private theorem sphC_rightRoot_mk (h : PGL2 ℂ) (x z : ℂ) :
    sphC (1 / 6) (wC * nC x * h * nC z) =
      sphericalC (1 / 6) (weylM ℂ * upperM ℂ x * (Quotient.out h) * upperM ℂ z) := by
  let M : GL (Fin 2) ℂ := Quotient.out h
  have hq : QuotientGroup.mk M = h := QuotientGroup.out_eq' h
  have hmul : wC * nC x * h * nC z =
      QuotientGroup.mk (weylM ℂ * upperM ℂ x * M * upperM ℂ z) := by
    rw [← hq]
    simp [wC, nC]
  rw [hmul, sphC_mk]

private def thetaSphericalDen (M : GL (Fin 2) ℂ) (x z : ℂ) : ℝ :=
  ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * x‖ ^ 2 +
    ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * x +
      z * ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 +
        (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * x)‖ ^ 2

@[simp] private theorem upperM_zero_eq_one_tensor (K : Type) [Field K] :
    upperM K 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperM]

@[simp] private theorem nC_zero_tensor : nC (0 : ℂ) = 1 := by
  simp [nC, upperM_zero_eq_one_tensor]

private theorem continuous_nC_tensor : Continuous (nC : ℂ → PGL2 ℂ) := by
  have hval : Continuous
      (fun x : ℂ => ((upperM ℂ x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    change Continuous (fun x : ℂ => !![(1 : ℂ), x; 0, 1])
    fun_prop
  have hmul (x : ℂ) : upperM ℂ x * upperM ℂ (-x) = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
  have hinv (x : ℂ) : (upperM ℂ x)⁻¹ = upperM ℂ (-x) :=
    inv_eq_of_mul_eq_one_right (hmul x)
  have hinv_cont : Continuous
      (fun x : ℂ => (((upperM ℂ x)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have heq :
        (fun x : ℂ => (((upperM ℂ x)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun x => ((upperM ℂ (-x) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext x
      exact congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) (hinv x)
    rw [heq]
    exact hval.comp continuous_neg
  have hu : Continuous (upperM ℂ) := Units.continuous_iff.mpr ⟨hval, hinv_cont⟩
  unfold nC
  exact continuous_quotient_mk'.comp hu

private theorem thetaSphericalDen_lower (M : GL (Fin 2) ℂ) (x z : ℂ)
    (hz : ‖z‖ ≤ 1) :
    let a := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    let b := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1
    let c := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0
    let d := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
    let C := 1 + ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
    (‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ 2 / (8 * C ^ 2)) *
      (1 + ‖x‖) ^ 2 ≤ thetaSphericalDen M x z := by
  dsimp only
  set a : ℂ := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set b : ℂ := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  set c : ℂ := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  set d : ℂ := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  set A : ℂ := a + c * x
  set B : ℂ := b + d * x + z * A
  set δ : ℝ := ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖
  set C : ℝ := 1 + ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
  have hdet : a * d - b * c = (M : Matrix (Fin 2) (Fin 2) ℂ).det := by
    dsimp [a, b, c, d]
    rw [Matrix.det_fin_two]
  have hdetne : a * d - b * c ≠ 0 := by
    rw [hdet]
    exact M.det_ne_zero
  have hδ : 0 < δ := by
    dsimp [δ]
    exact norm_pos_iff.mpr M.det_ne_zero
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hcoef₁ : ‖d + z * c‖ ≤ C := by
    calc
      ‖d + z * c‖ ≤ ‖d‖ + ‖z * c‖ := norm_add_le _ _
      _ = ‖d‖ + ‖z‖ * ‖c‖ := by rw [norm_mul]
      _ ≤ C := by
        have hzc : ‖z‖ * ‖c‖ ≤ ‖c‖ := by
          calc
            ‖z‖ * ‖c‖ ≤ 1 * ‖c‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg c)
            _ = ‖c‖ := by ring
        dsimp [C]
        nlinarith [hzc, norm_nonneg a, norm_nonneg b]
  have hcoef₂ : ‖c‖ ≤ C := by
    dsimp [C]
    linarith [norm_nonneg a, norm_nonneg b, norm_nonneg d]
  have hcoef₃ : ‖b + z * a‖ ≤ C := by
    calc
      ‖b + z * a‖ ≤ ‖b‖ + ‖z * a‖ := norm_add_le _ _
      _ = ‖b‖ + ‖z‖ * ‖a‖ := by rw [norm_mul]
      _ ≤ C := by
        have hza : ‖z‖ * ‖a‖ ≤ ‖a‖ := by
          calc
            ‖z‖ * ‖a‖ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg a)
            _ = ‖a‖ := by ring
        dsimp [C]
        nlinarith [hza, norm_nonneg c, norm_nonneg d]
  have hcoef₄ : ‖a‖ ≤ C := by
    dsimp [C]
    linarith [norm_nonneg b, norm_nonneg c, norm_nonneg d]
  have hA : A * (d + z * c) - B * c = a * d - b * c := by
    dsimp [A, B]
    ring
  have hB : B * a - A * (b + z * a) = x * (a * d - b * c) := by
    dsimp [A, B]
    ring
  have h₁ : δ ≤ C * (‖A‖ + ‖B‖) := by
    calc
      δ = ‖a * d - b * c‖ := by rw [hdet]
      _ = ‖A * (d + z * c) - B * c‖ := by rw [hA]
      _ ≤ ‖A * (d + z * c)‖ + ‖B * c‖ := norm_sub_le _ _
      _ = ‖A‖ * ‖d + z * c‖ + ‖B‖ * ‖c‖ := by rw [norm_mul, norm_mul]
      _ ≤ C * (‖A‖ + ‖B‖) := by
        have hA0 := norm_nonneg A
        have hB0 := norm_nonneg B
        calc
          ‖A‖ * ‖d + z * c‖ + ‖B‖ * ‖c‖ ≤ ‖A‖ * C + ‖B‖ * C :=
            add_le_add (mul_le_mul_of_nonneg_left hcoef₁ hA0)
              (mul_le_mul_of_nonneg_left hcoef₂ hB0)
          _ = C * (‖A‖ + ‖B‖) := by ring
  have h₂ : δ * ‖x‖ ≤ C * (‖A‖ + ‖B‖) := by
    calc
      δ * ‖x‖ = ‖x‖ * ‖a * d - b * c‖ := by
        rw [show δ = ‖a * d - b * c‖ by rw [hdet]]
        ring
      _ = ‖x * (a * d - b * c)‖ := by rw [norm_mul]
      _ = ‖B * a - A * (b + z * a)‖ := by rw [hB]
      _ ≤ ‖B * a‖ + ‖A * (b + z * a)‖ := norm_sub_le _ _
      _ = ‖B‖ * ‖a‖ + ‖A‖ * ‖b + z * a‖ := by rw [norm_mul, norm_mul]
      _ ≤ C * (‖A‖ + ‖B‖) := by
        have hA0 := norm_nonneg A
        have hB0 := norm_nonneg B
        calc
          ‖B‖ * ‖a‖ + ‖A‖ * ‖b + z * a‖ ≤ ‖B‖ * C + ‖A‖ * C :=
            add_le_add (mul_le_mul_of_nonneg_left hcoef₄ hB0)
              (mul_le_mul_of_nonneg_left hcoef₃ hA0)
          _ = C * (‖A‖ + ‖B‖) := by ring
  have hsum : δ * (1 + ‖x‖) ≤ 2 * C * (‖A‖ + ‖B‖) := by
    calc
      δ * (1 + ‖x‖) = δ + δ * ‖x‖ := by ring
      _ ≤ C * (‖A‖ + ‖B‖) + C * (‖A‖ + ‖B‖) := add_le_add h₁ h₂
      _ = 2 * C * (‖A‖ + ‖B‖) := by ring
  have hAB : (‖A‖ + ‖B‖) ^ 2 ≤ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hsq : δ ^ 2 * (1 + ‖x‖) ^ 2 ≤
      8 * C ^ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    have hsq' : (δ * (1 + ‖x‖)) ^ 2 ≤ (2 * C * (‖A‖ + ‖B‖)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hsum
    calc
      δ ^ 2 * (1 + ‖x‖) ^ 2 = (δ * (1 + ‖x‖)) ^ 2 := by ring
      _ ≤ (2 * C * (‖A‖ + ‖B‖)) ^ 2 := hsq'
      _ = 4 * C ^ 2 * (‖A‖ + ‖B‖) ^ 2 := by ring
      _ ≤ 8 * C ^ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
        calc
          4 * C ^ 2 * (‖A‖ + ‖B‖) ^ 2 ≤
              4 * C ^ 2 * (2 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hAB (by positivity)
          _ = 8 * C ^ 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by ring
  rw [thetaSphericalDen]
  calc
    (δ ^ 2 / (8 * C ^ 2)) * (1 + ‖x‖) ^ 2 =
        (δ ^ 2 * (1 + ‖x‖) ^ 2) / (8 * C ^ 2) := by ring
    _ ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * C ^ 2)).2
      simpa [mul_comm] using hsq

private theorem thetaSphericalDen_lipschitz (M : GL (Fin 2) ℂ) (x : ℂ) :
    LipschitzOnWith
      (Real.toNNReal (4 *
        (1 + ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ +
          ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ +
          ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ +
          ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖) ^ 2 * (1 + ‖x‖) ^ 2))
      (fun z => thetaSphericalDen M x z) (Metric.closedBall 0 1) := by
  classical
  let a := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  let b := (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  let c := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  let d := (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1
  let A := a + c * x
  let B (z : ℂ) := b + d * x + z * A
  let C := 1 + ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
  have hA : ‖A‖ ≤ C * (1 + ‖x‖) := by
    dsimp [A, C]
    calc
      ‖a + c * x‖ ≤ ‖a‖ + ‖c * x‖ := norm_add_le _ _
      _ = ‖a‖ + ‖c‖ * ‖x‖ := by rw [norm_mul]
      _ ≤ (1 + ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) * (1 + ‖x‖) := by
        nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d,
          norm_nonneg x]
  have hB (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖B z‖ ≤ 2 * C * (1 + ‖x‖) := by
    dsimp [B]
    have hb0 : ‖b + d * x‖ ≤ ‖b‖ + ‖d‖ * ‖x‖ := by
      calc
        ‖b + d * x‖ ≤ ‖b‖ + ‖d * x‖ := norm_add_le _ _
        _ = ‖b‖ + ‖d‖ * ‖x‖ := by rw [norm_mul]
    calc
      ‖b + d * x + z * A‖ ≤ ‖b‖ + ‖d‖ * ‖x‖ + ‖z‖ * ‖A‖ := by
        calc
          ‖b + d * x + z * A‖ ≤ ‖b + d * x‖ + ‖z * A‖ := norm_add_le _ _
          _ ≤ ‖b‖ + ‖d‖ * ‖x‖ + ‖z‖ * ‖A‖ := by
            rw [norm_mul]
            linarith [hb0]
      _ ≤ C * (1 + ‖x‖) + C * (1 + ‖x‖) := by
        have hdb : ‖b‖ + ‖d‖ * ‖x‖ ≤ C * (1 + ‖x‖) := by
          dsimp [C]
          nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d,
            norm_nonneg x]
        have hzA : ‖z‖ * ‖A‖ ≤ ‖A‖ := by
          calc
            ‖z‖ * ‖A‖ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg A)
            _ = ‖A‖ := by ring
        exact add_le_add hdb (hzA.trans hA)
      _ = 2 * C * (1 + ‖x‖) := by ring
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz z' hz'
  have hz₁ : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz₂ : ‖z'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  have hbdiff : ‖B z - B z'‖ = ‖z - z'‖ * ‖A‖ := by
    dsimp [B]
    rw [show b + d * x + z * A - (b + d * x + z' * A) = (z - z') * A by ring,
      norm_mul]
  have hnsq : |‖B z‖ ^ 2 - ‖B z'‖ ^ 2| ≤
      ‖B z - B z'‖ * (‖B z‖ + ‖B z'‖) := by
    rw [show ‖B z‖ ^ 2 - ‖B z'‖ ^ 2 =
      (‖B z‖ - ‖B z'‖) * (‖B z‖ + ‖B z'‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖B z‖ + ‖B z'‖)]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  have hD : |thetaSphericalDen M x z - thetaSphericalDen M x z'| ≤
      4 * C ^ 2 * (1 + ‖x‖) ^ 2 * ‖z - z'‖ := by
    calc
      |thetaSphericalDen M x z - thetaSphericalDen M x z'| =
          |‖B z‖ ^ 2 - ‖B z'‖ ^ 2| := by simp [thetaSphericalDen, A, B, a, b, c, d]
      _ ≤ ‖B z - B z'‖ * (‖B z‖ + ‖B z'‖) := hnsq
      _ = ‖z - z'‖ * ‖A‖ * (‖B z‖ + ‖B z'‖) := by rw [hbdiff]
      _ ≤ 4 * C ^ 2 * (1 + ‖x‖) ^ 2 * ‖z - z'‖ := by
        have hsum : ‖B z‖ + ‖B z'‖ ≤ 4 * C * (1 + ‖x‖) := by
          linarith [hB z hz₁, hB z' hz₂]
        have hprod : ‖A‖ * (‖B z‖ + ‖B z'‖) ≤
            4 * C ^ 2 * (1 + ‖x‖) ^ 2 := by
          calc
            ‖A‖ * (‖B z‖ + ‖B z'‖) ≤
                (C * (1 + ‖x‖)) * (4 * C * (1 + ‖x‖)) :=
              mul_le_mul hA hsum (by positivity) (by positivity)
            _ = 4 * C ^ 2 * (1 + ‖x‖) ^ 2 := by ring
        calc
          ‖z - z'‖ * ‖A‖ * (‖B z‖ + ‖B z'‖) =
              ‖z - z'‖ * (‖A‖ * (‖B z‖ + ‖B z'‖)) := by ring
          _ ≤ ‖z - z'‖ * (4 * C ^ 2 * (1 + ‖x‖) ^ 2) :=
            mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
          _ = 4 * C ^ 2 * (1 + ‖x‖) ^ 2 * ‖z - z'‖ := by ring
  rw [Real.dist_eq, dist_eq_norm]
  have hK : 0 ≤ 4 * C ^ 2 * (1 + ‖x‖) ^ 2 := by positivity
  change |thetaSphericalDen M x z - thetaSphericalDen M x z'| ≤
    (Real.toNNReal (4 * C ^ 2 * (1 + ‖x‖) ^ 2) : ℝ) * ‖z - z'‖
  rw [Real.coe_toNNReal _ hK]
  exact hD

private theorem thetaRealPower_lipschitz (δ u₀ : ℝ) (hδ : 0 < δ) (hu₀ : 0 < u₀) :
    LipschitzOnWith
      (Real.toNNReal ((4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) * (δ / u₀ ^ 2)))
      (fun u : ℝ => (δ / u) ^ (4 / 3 : ℝ)) (Set.Ici u₀) := by
  let p : ℝ → ℝ := fun u => (δ / u) ^ (4 / 3 : ℝ)
  let K : ℝ := (4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) * (δ / u₀ ^ 2)
  have hK : 0 ≤ K := by positivity
  have hderiv (u : ℝ) (hu : u ∈ Set.Ici u₀) :
      deriv p u = -((δ / u ^ 2) * (4 / 3 : ℝ) * (δ / u) ^ (1 / 3 : ℝ)) := by
    have hu' : 0 < u := lt_of_lt_of_le hu₀ hu
    have hdiv : HasDerivAt (fun t : ℝ => δ / t) (-δ / u ^ 2) u := by
      convert (hasDerivAt_const u δ).div (hasDerivAt_id u) hu'.ne' using 1
      · funext t
        rfl
      · field_simp [hu'.ne']
        simp
        ring
    have hpow := hdiv.rpow_const (Or.inr (by norm_num : (1 : ℝ) ≤ (4 / 3 : ℝ)))
    simpa [p, show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num, neg_div] using hpow.deriv
  have hbound (u : ℝ) (hu : u ∈ Set.Ici u₀) : ‖deriv p u‖₊ ≤ Real.toNNReal K := by
    have hu' : 0 < u := lt_of_lt_of_le hu₀ hu
    have hu_le : u₀ ≤ u := hu
    have hratio : δ / u ≤ δ / u₀ := by gcongr
    have hratio2 : δ / u ^ 2 ≤ δ / u₀ ^ 2 := by
      have hsq : u₀ ^ 2 ≤ u ^ 2 := by nlinarith [hu₀.le, hu_le]
      gcongr
    have hpow : (δ / u) ^ (1 / 3 : ℝ) ≤ (δ / u₀) ^ (1 / 3 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) hratio (by norm_num)
    have hreal : ‖deriv p u‖ ≤ K := by
      rw [hderiv u hu, Real.norm_eq_abs, abs_neg, abs_of_nonneg]
      · calc
          (δ / u ^ 2) * (4 / 3 : ℝ) * (δ / u) ^ (1 / 3 : ℝ) ≤
              (δ / u₀ ^ 2) * (4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) := by
                gcongr
          _ = K := by dsimp [K]; ring
      · positivity
    have hreal' : (‖deriv p u‖₊ : ℝ) ≤ (Real.toNNReal K : ℝ) := by
      change ‖deriv p u‖ ≤ (Real.toNNReal K : ℝ)
      rw [Real.coe_toNNReal _ hK]
      exact hreal
    exact NNReal.coe_le_coe.1 hreal'
  have hdiff (u : ℝ) (hu : u ∈ Set.Ici u₀) : DifferentiableAt ℝ p u := by
    have hu' : 0 < u := lt_of_lt_of_le hu₀ hu
    have hdiv : HasDerivAt (fun t : ℝ => δ / t) (-δ / u ^ 2) u := by
      convert (hasDerivAt_const u δ).div (hasDerivAt_id u) hu'.ne' using 1
      · funext t
        rfl
      · field_simp [hu'.ne']
        simp
        ring
    exact (hdiv.rpow_const (Or.inr (by norm_num : (1 : ℝ) ≤ (4 / 3 : ℝ)))).differentiableAt
  exact Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun u hu => hdiff u hu) (fun u hu => hbound u hu) (convex_Ici u₀)

private noncomputable def thetaSphericalCoeffBound (M : GL (Fin 2) ℂ) : ℝ :=
  1 + ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ +
    ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ +
    ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ +
    ‖(M : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖

private noncomputable def thetaSphericalDetNorm (M : GL (Fin 2) ℂ) : ℝ :=
  ‖(M : Matrix (Fin 2) (Fin 2) ℂ).det‖

private noncomputable def thetaSphericalDenFloor (M : GL (Fin 2) ℂ) (x : ℂ) : ℝ :=
  (thetaSphericalDetNorm M) ^ 2 /
    (8 * (thetaSphericalCoeffBound M) ^ 2) * (1 + ‖x‖) ^ 2

private noncomputable def thetaJacquetPathLip (M : GL (Fin 2) ℂ) (x : ℂ) : NNReal :=
  Real.toNNReal ((4 / 3 : ℝ) *
      (thetaSphericalDetNorm M / thetaSphericalDenFloor M x) ^ (1 / 3 : ℝ) *
      (thetaSphericalDetNorm M / (thetaSphericalDenFloor M x) ^ 2)) *
    Real.toNNReal (4 * (thetaSphericalCoeffBound M) ^ 2 * (1 + ‖x‖) ^ 2)

private theorem thetaSphericalDet (M : GL (Fin 2) ℂ) (x z : ℂ) :
    ((weylM ℂ * upperM ℂ x * M * upperM ℂ z : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ).det =
        -((M : Matrix (Fin 2) (Fin 2) ℂ).det) := by
  change ((Matrix.GeneralLinearGroup.det
      (weylM ℂ * upperM ℂ x * M * upperM ℂ z) : ℂˣ) : ℂ) =
    -((M : Matrix (Fin 2) (Fin 2) ℂ).det)
  have hdet : (weylM ℂ * upperM ℂ x * M * upperM ℂ z).det =
      (weylM ℂ).det * (upperM ℂ x).det * M.det * (upperM ℂ z).det := by
    simp [map_mul, mul_assoc]
  rw [hdet]
  simp [Matrix.GeneralLinearGroup.det, upperM, weylM, Matrix.det_fin_two, mul_assoc]

private theorem sphC_rightRoot_formula (h : PGL2 ℂ) (x z : ℂ) :
    sphC (1 / 6) (wC * nC x * h * nC z) =
      ((‖((Quotient.out h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        thetaSphericalDen (Quotient.out h) x z : ℝ) : ℂ) ^ (4 / 3 : ℂ) := by
  rw [sphC_rightRoot_mk]
  unfold sphericalC
  have hexp : (1 : ℂ) + 2 * (1 / 6 : ℂ) = (4 / 3 : ℂ) := by norm_num
  rw [hexp]
  apply congrArg (fun q : ℂ => q ^ (4 / 3 : ℂ))
  apply congrArg Complex.ofReal
  congr 1
  · rw [thetaSphericalDet, norm_neg]
  · apply congrArg₂ (· + ·)
    · congr 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.mul_apply,
        upperM, weylM]
      ring
    · congr 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Matrix.mul_apply,
        upperM, weylM]
      ring

private theorem sphC_rightRoot_rpow (h : PGL2 ℂ) (x z : ℂ) (hz : ‖z‖ ≤ 1) :
    sphC (1 / 6) (wC * nC x * h * nC z) =
      ((Real.rpow (‖((Quotient.out h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        thetaSphericalDen (Quotient.out h) x z) (4 / 3 : ℝ) : ℝ) : ℂ) := by
  let M : GL (Fin 2) ℂ := Quotient.out h
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let u₀ := thetaSphericalDenFloor M x
  have hdetne : (M : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := M.det_ne_zero
  have hδ : 0 < δ := by
    dsimp [δ, thetaSphericalDetNorm]
    exact norm_pos_iff.mpr hdetne
  have hC : 0 < C := by
    dsimp [C, thetaSphericalCoeffBound]
    positivity
  have hu₀ : 0 < u₀ := by
    dsimp [u₀, thetaSphericalDenFloor]
    positivity
  have hlow : u₀ ≤ thetaSphericalDen M x z := by
    simpa [u₀, thetaSphericalDenFloor, C, thetaSphericalCoeffBound,
      δ, thetaSphericalDetNorm] using thetaSphericalDen_lower M x z hz
  have hden : 0 < thetaSphericalDen M x z := lt_of_lt_of_le hu₀ hlow
  have hbase :
      ‖((Quotient.out h : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
        thetaSphericalDen (Quotient.out h) x z =
          δ / thetaSphericalDen M x z := by
    simp [δ, thetaSphericalDetNorm, M]
  rw [sphC_rightRoot_formula h x z, hbase]
  rw [show (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) by norm_num]
  exact (Complex.ofReal_cpow (div_nonneg (le_of_lt hδ) hden.le)
    (4 / 3 : ℝ)).symm

private theorem thetaSphericalDen_differentiableAt (M : GL (Fin 2) ℂ) (x z : ℂ) :
    DifferentiableAt ℝ (fun z' => thetaSphericalDen M x z') z := by
  unfold thetaSphericalDen
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  fun_prop

private theorem thetaJacquetPath_differentiableAt (h : PGL2 ℂ) (x : ℂ) :
    DifferentiableAt ℝ
      (fun z => psiC (-x) * sphC (1 / 6) (wC * nC x * h * nC z)) 0 := by
  let M : GL (Fin 2) ℂ := Quotient.out h
  let δ := thetaSphericalDetNorm M
  let u₀ := thetaSphericalDenFloor M x
  have hδ : 0 < δ := by
    dsimp [δ, thetaSphericalDetNorm]
    exact norm_pos_iff.mpr M.det_ne_zero
  have hC : 0 < thetaSphericalCoeffBound M := by
    dsimp [thetaSphericalCoeffBound]
    positivity
  have hu₀ : 0 < u₀ := by
    have hu₀' : u₀ = δ ^ 2 /
        (8 * (thetaSphericalCoeffBound M) ^ 2) * (1 + ‖x‖) ^ 2 := by
      rfl
    rw [hu₀']
    positivity
  have hden0 : 0 < thetaSphericalDen M x 0 := by
    have hlow := thetaSphericalDen_lower M x 0 (by simp)
    have hu₀' : 0 < thetaSphericalDenFloor M x := by
      dsimp [thetaSphericalDenFloor]
      positivity
    exact lt_of_lt_of_le hu₀' hlow
  have hdenDiff := thetaSphericalDen_differentiableAt M x 0
  have hinv : DifferentiableAt ℝ
      (fun z : ℂ => (thetaSphericalDen M x z)⁻¹) 0 := hdenDiff.inv hden0.ne'
  have hconst : DifferentiableAt ℝ (fun _ : ℂ => δ) 0 := by
    exact differentiableAt_const δ
  have hq : DifferentiableAt ℝ (fun z : ℂ => δ / thetaSphericalDen M x z) 0 := by
    have hfun : (fun z : ℂ => δ / thetaSphericalDen M x z) =
        (fun _ : ℂ => δ) * (fun z => (thetaSphericalDen M x z)⁻¹) := by
      funext z
      simp [div_eq_mul_inv]
    exact hfun ▸ hconst.mul hinv
  have hpow : DifferentiableAt ℝ
      (fun z : ℂ => (δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ)) 0 :=
    hq.rpow_const (Or.inr (by norm_num : (1 : ℝ) ≤ (4 / 3 : ℝ)))
  have hcast : DifferentiableAt ℝ
      (fun z : ℂ => (((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ) : ℝ) : ℂ)) 0 := by
    exact Complex.ofRealCLM.differentiableAt.comp 0 hpow
  have hG : DifferentiableAt ℝ
      (fun z : ℂ => psiC (-x) *
        (((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ) : ℝ) : ℂ)) 0 :=
    DifferentiableAt.mul (𝕜 := ℝ)
      (differentiableAt_const (𝕜 := ℝ) (x := (0 : ℂ)) (psiC (-x))) hcast
  have heq :
      (fun z : ℂ => psiC (-x) * sphC (1 / 6) (wC * nC x * h * nC z)) =ᶠ[𝓝 0]
      (fun z : ℂ => psiC (-x) *
        (((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ) : ℝ) : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz' : ‖z‖ ≤ 1 := by
      have : dist z 0 < (1 : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      simpa using this.le
    rw [sphC_rightRoot_rpow h x z hz']
    simp [δ, thetaSphericalDetNorm, M]
  exact hG.congr_of_eventuallyEq heq

private theorem thetaJacquetPath_lipschitz (h : PGL2 ℂ) (x : ℂ) :
    LipschitzOnWith (thetaJacquetPathLip (Quotient.out h) x)
      (fun z => psiC (-x) * sphC (1 / 6) (wC * nC x * h * nC z))
      (Metric.closedBall (0 : ℂ) 1) := by
  classical
  let M : GL (Fin 2) ℂ := Quotient.out h
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let u₀ := thetaSphericalDenFloor M x
  let Kp := Real.toNNReal ((4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) *
    (δ / u₀ ^ 2))
  let Kd := Real.toNNReal (4 * C ^ 2 * (1 + ‖x‖) ^ 2)
  have hdetne : (M : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := M.det_ne_zero
  have hδ : 0 < δ := by
    dsimp [δ, thetaSphericalDetNorm]
    exact norm_pos_iff.mpr hdetne
  have hC : 0 < C := by
    dsimp [C, thetaSphericalCoeffBound]
    positivity
  have hu₀ : 0 < u₀ := by
    dsimp [u₀, thetaSphericalDenFloor]
    positivity
  have hp : LipschitzOnWith Kp (fun u : ℝ => (δ / u) ^ (4 / 3 : ℝ)) (Set.Ici u₀) :=
    thetaRealPower_lipschitz δ u₀ hδ hu₀
  have hd : LipschitzOnWith Kd (fun z => thetaSphericalDen M x z)
      (Metric.closedBall (0 : ℂ) 1) := by
    simpa [Kd, C, thetaSphericalCoeffBound] using thetaSphericalDen_lipschitz M x
  have hcomp : LipschitzOnWith (Kp * Kd)
      (fun z => (δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ))
      (Metric.closedBall (0 : ℂ) 1) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro z hz z' hz'
    have hlow₁ : u₀ ≤ thetaSphericalDen M x z := by
      simpa [u₀, thetaSphericalDenFloor, C, thetaSphericalCoeffBound,
        δ, thetaSphericalDetNorm] using thetaSphericalDen_lower M x z (by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
    have hlow₂ : u₀ ≤ thetaSphericalDen M x z' := by
      simpa [u₀, thetaSphericalDenFloor, C, thetaSphericalCoeffBound,
        δ, thetaSphericalDetNorm] using thetaSphericalDen_lower M x z' (by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hz')
    calc
      dist ((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ))
          ((δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ)) ≤
          (Kp : NNReal) * dist (thetaSphericalDen M x z) (thetaSphericalDen M x z') :=
        hp.dist_le_mul (thetaSphericalDen M x z) hlow₁
          (thetaSphericalDen M x z') hlow₂
      _ ≤ (Kp : NNReal) * ((Kd : NNReal) * dist z z') :=
        mul_le_mul_of_nonneg_left (hd.dist_le_mul z hz z' hz') (by positivity)
      _ = ((Kp * Kd : NNReal) * dist z z') := by
        rw [NNReal.coe_mul]
        ac_rfl
  have hformula (z : ℂ) (hz : ‖z‖ ≤ 1) :
      sphC (1 / 6) (wC * nC x * h * nC z) =
        ((Real.rpow (δ / thetaSphericalDen M x z) (4 / 3 : ℝ) : ℝ) : ℂ) := by
    simpa [δ, thetaSphericalDetNorm, M] using sphC_rightRoot_rpow h x z hz
  have hψ : ‖psiC (-x)‖ = 1 := by
    unfold psiC
    have harg : -(4 * Real.pi * Complex.I * ((-x).re : ℂ)) =
        Complex.I * (4 * Real.pi * x.re : ℝ) := by
      rw [Complex.neg_re, Complex.ofReal_neg]
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal]
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro z hz z' hz'
  have hz₁ : ‖z‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hz₂ : ‖z'‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz'
  rw [dist_eq_norm]
  rw [hformula z hz₁, hformula z' hz₂]
  calc
    ‖psiC (-x) * ↑((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ)) -
      psiC (-x) * ↑((δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ))‖ =
        dist ((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ))
          ((δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ)) := by
          calc
            _ = ‖psiC (-x)‖ * ‖((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ) -
                (δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ) : ℝ)‖ := by
              rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real]
            _ = ‖((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ) -
                (δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ) : ℝ)‖ := by rw [hψ, one_mul]
            _ = dist ((δ / thetaSphericalDen M x z) ^ (4 / 3 : ℝ))
                ((δ / thetaSphericalDen M x z') ^ (4 / 3 : ℝ)) := by
              rw [Real.norm_eq_abs, Real.dist_eq]
    _ ≤ (Kp * Kd : NNReal) * dist z z' := hcomp.dist_le_mul z hz z' hz'

private noncomputable def thetaJacquetPathBoundConst (M : GL (Fin 2) ℂ) : ℝ :=
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let a := δ ^ 2 / (8 * C ^ 2)
  (4 / 3 : ℝ) * (δ / a) ^ (1 / 3 : ℝ) * (δ / a ^ 2) * (4 * C ^ 2)

private theorem thetaJacquetPathLip_eq_bound (M : GL (Fin 2) ℂ) (x : ℂ) :
    (thetaJacquetPathLip M x : ℝ) =
      thetaJacquetPathBoundConst M * (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let R := 1 + ‖x‖
  let a := δ ^ 2 / (8 * C ^ 2)
  let u₀ := thetaSphericalDenFloor M x
  have hδ : 0 < δ := by
    dsimp [δ, thetaSphericalDetNorm]
    exact norm_pos_iff.mpr M.det_ne_zero
  have hC : 0 < C := by
    dsimp [C, thetaSphericalCoeffBound]
    positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hu₀ : u₀ = a * R ^ 2 := by
    change (thetaSphericalDetNorm M) ^ 2 /
        (8 * (thetaSphericalCoeffBound M) ^ 2) *
        (1 + ‖x‖) ^ 2 = a * R ^ 2
    rfl
  have hq₁ : δ / u₀ = (δ / a) / R ^ 2 := by
    rw [hu₀]
    field_simp [ha.ne', hR.ne']
  have hq₂ : δ / u₀ ^ 2 = (δ / a ^ 2) / R ^ 4 := by
    rw [hu₀]
    field_simp [ha.ne', hR.ne']
  have hRpow₂ : R ^ 2 = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
  have hpow₂ : (R ^ 2) ^ (1 / 3 : ℝ) = R ^ (2 / 3 : ℝ) := by
    calc
      (R ^ 2) ^ (1 / 3 : ℝ) = (R ^ (2 : ℝ)) ^ (1 / 3 : ℝ) :=
        congrArg (fun t : ℝ => t ^ (1 / 3 : ℝ)) hRpow₂
      _ = (R ^ (1 / 3 : ℝ)) ^ 2 := by
        rw [← hRpow₂]
        exact (Real.rpow_pow_comm hR.le (1 / 3 : ℝ) 2).symm
      _ = (R ^ (1 / 3 : ℝ)) ^ (2 : ℝ) :=
        (Real.rpow_natCast (R ^ (1 / 3 : ℝ)) 2).symm
      _ = R ^ ((1 / 3 : ℝ) * 2) := (Real.rpow_mul hR.le _ _).symm
      _ = R ^ (2 / 3 : ℝ) := by congr 1 <;> norm_num
  have hpowneg₂ : ((R ^ 2) ^ (1 / 3 : ℝ))⁻¹ = R ^ (-(2 / 3 : ℝ)) := by
    calc
      ((R ^ 2) ^ (1 / 3 : ℝ))⁻¹ = (R ^ 2) ^ (-(1 / 3 : ℝ)) :=
        (Real.rpow_neg (by positivity : 0 ≤ R ^ 2) (1 / 3 : ℝ)).symm
      _ = (R ^ (-(1 / 3 : ℝ))) ^ 2 := by
        exact (Real.rpow_pow_comm hR.le (-(1 / 3 : ℝ)) 2).symm
      _ = (R ^ (-(1 / 3 : ℝ))) ^ (2 : ℝ) :=
        (Real.rpow_natCast (R ^ (-(1 / 3 : ℝ))) 2).symm
      _ = R ^ ((-(1 / 3 : ℝ)) * 2) := (Real.rpow_mul hR.le _ _).symm
      _ = R ^ (-(2 / 3 : ℝ)) := by congr 1 <;> norm_num
  have hpowneg₄ : (R ^ 4)⁻¹ = R ^ (-(4 : ℝ)) := by
    calc
      (R ^ 4)⁻¹ = (R ^ (4 : ℝ))⁻¹ := by
        rw [show R ^ (4 : ℝ) = R ^ 4 from Real.rpow_natCast R 4]
      _ = R ^ (-(4 : ℝ)) := (Real.rpow_neg hR.le 4).symm
  have hdecay :
      ((R ^ 2) ^ (1 / 3 : ℝ))⁻¹ * (R ^ 4)⁻¹ * R ^ 2 =
        R ^ (-(8 / 3 : ℝ)) := by
    calc
      _ = R ^ (-(2 / 3 : ℝ)) * R ^ (-(4 : ℝ)) * R ^ (2 : ℝ) := by
        rw [hpowneg₂, hpowneg₄, hRpow₂]
      _ = R ^ (-(2 / 3 : ℝ) + -(4 : ℝ) + (2 : ℝ)) := by
        rw [← Real.rpow_add hR, ← Real.rpow_add hR]
      _ = R ^ (-(8 / 3 : ℝ)) := by congr 1 <;> norm_num
  have hu₀_pos : 0 < u₀ := by rw [hu₀]; positivity
  have hα : 0 ≤ (4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) * (δ / u₀ ^ 2) := by
    positivity
  have hβ : 0 ≤ 4 * C ^ 2 * R ^ 2 := by positivity
  change (Real.toNNReal ((4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) *
      (δ / u₀ ^ 2)) : ℝ) *
    (Real.toNNReal (4 * C ^ 2 * R ^ 2) : ℝ) = _
  rw [Real.coe_toNNReal _ hα, Real.coe_toNNReal _ hβ]
  unfold thetaJacquetPathBoundConst
  dsimp only
  calc
    (4 / 3 : ℝ) * (δ / u₀) ^ (1 / 3 : ℝ) * (δ / u₀ ^ 2) *
        (4 * C ^ 2 * R ^ 2) =
      ((4 / 3 : ℝ) * (δ / a) ^ (1 / 3 : ℝ) * (δ / a ^ 2) *
        (4 * C ^ 2)) *
        (((R ^ 2) ^ (1 / 3 : ℝ))⁻¹ * (R ^ 4)⁻¹ * R ^ 2) := by
          rw [hq₁, hq₂, Real.div_rpow (by positivity) (by positivity)]
          ring
    _ = ((4 / 3 : ℝ) * (δ / a) ^ (1 / 3 : ℝ) * (δ / a ^ 2) *
        (4 * C ^ 2)) * R ^ (-(8 / 3 : ℝ)) := by rw [hdecay]
    _ = thetaJacquetPathBoundConst M * (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
      simp [thetaJacquetPathBoundConst, δ, C, a, R]

private noncomputable def thetaJacquetPathValueBoundConst (M : GL (Fin 2) ℂ) : ℝ :=
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let a := δ ^ 2 / (8 * C ^ 2)
  (δ / a) ^ (4 / 3 : ℝ)

private theorem thetaJacquetPath_value_bound (h : PGL2 ℂ) (x : ℂ) :
    ‖psiC (-x) * sphC (1 / 6) (wC * nC x * h)‖ ≤
      thetaJacquetPathValueBoundConst (Quotient.out h) *
        (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
  let M : GL (Fin 2) ℂ := Quotient.out h
  let δ := thetaSphericalDetNorm M
  let C := thetaSphericalCoeffBound M
  let R := 1 + ‖x‖
  let a := δ ^ 2 / (8 * C ^ 2)
  let u₀ := thetaSphericalDenFloor M x
  have hδ : 0 < δ := by
    dsimp [δ, thetaSphericalDetNorm]
    exact norm_pos_iff.mpr M.det_ne_zero
  have hC : 0 < C := by
    dsimp [C, thetaSphericalCoeffBound]
    positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hu₀ : u₀ = a * R ^ 2 := by
    change (thetaSphericalDetNorm M) ^ 2 /
        (8 * (thetaSphericalCoeffBound M) ^ 2) *
        (1 + ‖x‖) ^ 2 = a * R ^ 2
    rfl
  have hu₀_pos : 0 < u₀ := by rw [hu₀]; positivity
  have hlow : u₀ ≤ thetaSphericalDen M x 0 := by
    have hz : ‖(0 : ℂ)‖ ≤ 1 := by simp
    simpa [u₀, thetaSphericalDenFloor, C, thetaSphericalCoeffBound,
      δ, thetaSphericalDetNorm] using thetaSphericalDen_lower M x 0 hz
  have hden : 0 < thetaSphericalDen M x 0 := by
    have : 0 < u₀ := by rw [hu₀]; positivity
    exact lt_of_lt_of_le this hlow
  have hratio : δ / thetaSphericalDen M x 0 ≤ (δ / a) / R ^ 2 := by
    calc
      δ / thetaSphericalDen M x 0 ≤ δ / u₀ :=
        div_le_div_of_nonneg_left hδ.le hu₀_pos hlow
      _ = (δ / a) / R ^ 2 := by rw [hu₀]; field_simp [ha.ne', hR.ne']
  have hpowR : (R ^ 2) ^ (4 / 3 : ℝ) = R ^ (8 / 3 : ℝ) := by
    have hRpow₂ : R ^ 2 = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
    calc
      (R ^ 2) ^ (4 / 3 : ℝ) = (R ^ (2 : ℝ)) ^ (4 / 3 : ℝ) :=
        congrArg (fun t : ℝ => t ^ (4 / 3 : ℝ)) hRpow₂
      _ = R ^ ((2 : ℝ) * (4 / 3 : ℝ)) := by rw [← Real.rpow_mul hR.le]
      _ = R ^ (8 / 3 : ℝ) := by congr 1 <;> norm_num
  have hscale : ((δ / a) / R ^ 2) ^ (4 / 3 : ℝ) =
      (δ / a) ^ (4 / 3 : ℝ) * R ^ (-(8 / 3 : ℝ)) := by
    rw [Real.div_rpow (by positivity) (by positivity), hpowR, div_eq_mul_inv,
      ← Real.rpow_neg hR.le (8 / 3 : ℝ)]
  have hψ : ‖psiC (-x)‖ = 1 := by
    unfold psiC
    have harg : -(4 * Real.pi * Complex.I * ((-x).re : ℂ)) =
        Complex.I * (4 * Real.pi * x.re : ℝ) := by
      rw [Complex.neg_re, Complex.ofReal_neg]
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal]
  have hformula : sphC (1 / 6) (wC * nC x * h) =
      ((Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ) : ℝ) : ℂ) := by
    simpa [δ, thetaSphericalDetNorm, M, nC_zero_tensor] using
      sphC_rightRoot_rpow h x 0 (by simp)
  have hratio_nonneg : 0 ≤ δ / thetaSphericalDen M x 0 := by positivity
  have hpower_le :
      (δ / thetaSphericalDen M x 0) ^ (4 / 3 : ℝ) ≤
        ((δ / a) / R ^ 2) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hratio_nonneg hratio (by norm_num)
  have hnorm :
      ‖psiC (-x) * sphC (1 / 6) (wC * nC x * h)‖ =
        Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ) := by
    rw [hformula, norm_mul, hψ, Complex.norm_real, Real.norm_eq_abs]
    change 1 * |Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ)| = _
    calc
      1 * |Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ)| =
          1 * Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ) := by
            congr 1
            exact abs_of_nonneg (Real.rpow_nonneg hratio_nonneg _)
      _ = Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ) := one_mul _
  calc
    ‖psiC (-x) * sphC (1 / 6) (wC * nC x * h)‖ =
        Real.rpow (δ / thetaSphericalDen M x 0) (4 / 3 : ℝ) := hnorm
    _ ≤ ((δ / a) / R ^ 2) ^ (4 / 3 : ℝ) := hpower_le
    _ = thetaJacquetPathValueBoundConst (Quotient.out h) *
        (1 + ‖x‖) ^ (-(8 / 3 : ℝ)) := by
          rw [hscale]
          simp [thetaJacquetPathValueBoundConst, δ, C, a, R, M]

private theorem thetaJacquetPath_integrable (h : PGL2 ℂ) :
    Integrable (fun x : ℂ => psiC (-x) * sphC (1 / 6) (wC * nC x * h)) volume := by
  have hpow : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) volume := by
    apply integrable_one_add_norm
    norm_num [Complex.finrank_real_complex]
  have hcont : Continuous
      (fun x : ℂ => psiC (-x) * sphC (1 / 6) (wC * nC x * h)) := by
    have hψ : Continuous (psiC : ℂ → ℂ) := by
      unfold psiC
      fun_prop
    have hn : Continuous nC := continuous_nC_tensor
    have hsph := (sphC_isSection (1 / 6)).2
    fun_prop
  refine (hpow.const_mul (thetaJacquetPathValueBoundConst (Quotient.out h))).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards [] with x
  exact thetaJacquetPath_value_bound h x

set_option maxHeartbeats 1000000 in
private theorem jacquetC_rightRoot_derivative (m : ℤ) (h : PGL2 ℂ) :
    thetaRootDerivative m
        (fun z => jacquetC (rtr (h * nC z) (sphC (1 / 6)))) =
      jacquetC (rtr h (derivVecC m (sphC (1 / 6)))) := by
  classical
  let F : ℂ → ℂ → ℂ := fun z x =>
    psiC (-x) * sphC (1 / 6) (wC * nC x * h * nC z)
  let G : ℂ → ℂ → ℂ := fun x z => F z x
  let F' : ℂ → ℂ →L[ℝ] ℂ := fun x => fderiv ℝ (F · x) 0
  have hcont : Continuous (Function.uncurry F) := by
    have hψ : Continuous (psiC : ℂ → ℂ) := by
      unfold psiC
      fun_prop
    have hn : Continuous nC := continuous_nC_tensor
    have hsph := (sphC_isSection (1 / 6)).2
    change Continuous (fun p : ℂ × ℂ =>
      psiC (-p.2) * sphC (1 / 6) (wC * nC p.2 * h * nC p.1))
    fun_prop
  have hF_meas : ∀ᶠ z in 𝓝 (0 : ℂ), AEStronglyMeasurable (F z) volume := by
    filter_upwards [] with z
    have hmap : Continuous (fun x : ℂ => (z, x)) := by fun_prop
    have hz : Continuous (F z) := hcont.comp hmap
    exact hz.aestronglyMeasurable
  have hF_int : Integrable (F 0) volume := by
    simpa [F, nC_zero_tensor] using thetaJacquetPath_integrable h
  have hF'_meas : AEStronglyMeasurable F' volume := by
    have hswap : Continuous (fun p : ℂ × ℂ => (p.2, p.1)) := by fun_prop
    have hGcont : Continuous (Function.uncurry G) := by
      change Continuous (Function.uncurry F ∘ fun p : ℂ × ℂ => (p.2, p.1))
      exact hcont.comp hswap
    have hm := measurable_fderiv_with_param ℝ hGcont
    have hdiag : Measurable (fun x : ℂ => (x, (0 : ℂ))) := by fun_prop
    have hm' : Measurable F' := by
      change Measurable (fun x : ℂ => fderiv ℝ (fun z => F z x) 0)
      exact hm.comp hdiag
    exact hm'.aestronglyMeasurable
  have h_lip : ∀ᵐ x : ℂ ∂volume,
      LipschitzOnWith (Real.nnabs (thetaJacquetPathLip (Quotient.out h) x : ℝ))
        (F · x) (Metric.ball (0 : ℂ) 1) := by
    filter_upwards [] with x
    have hLip := (thetaJacquetPath_lipschitz h x).mono Metric.ball_subset_closedBall
    simpa [F, Real.nnabs_of_nonneg (NNReal.coe_nonneg _)] using hLip
  have hbound_int :
      Integrable (fun x : ℂ => (thetaJacquetPathLip (Quotient.out h) x : ℝ)) volume := by
    have hpow : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(8 / 3 : ℝ))) volume := by
      apply integrable_one_add_norm
      norm_num [Complex.finrank_real_complex]
    have hconst := hpow.const_mul (thetaJacquetPathBoundConst (Quotient.out h))
    simpa [thetaJacquetPathLip_eq_bound] using hconst
  have hdiff : ∀ᵐ x : ℂ ∂volume, HasFDerivAt (F · x) (F' x) 0 := by
    filter_upwards [] with x
    exact (thetaJacquetPath_differentiableAt h x).hasFDerivAt
  have hparam := hasFDerivAt_integral_of_dominated_loc_of_lip
    (s := Metric.ball (0 : ℂ) 1) (x₀ := (0 : ℂ))
    (bound := fun x => (thetaJacquetPathLip (Quotient.out h) x : ℝ))
    (μ := volume) (Metric.ball_mem_nhds 0 (by norm_num))
    hF_meas hF_int hF'_meas h_lip hbound_int hdiff
  have hJ :
      (fun z => jacquetC (rtr (h * nC z) (sphC (1 / 6)))) =
      (fun z => ∫ x, F z x) := by
    funext z
    simp [jacquetC, F, rtr, mul_assoc]
  have hψnorm (x : ℂ) : ‖psiC (-x)‖ = 1 := by
    unfold psiC
    have harg : -(4 * Real.pi * Complex.I * ((-x).re : ℂ)) =
        Complex.I * (4 * Real.pi * x.re : ℝ) := by
      rw [Complex.neg_re, Complex.ofReal_neg]
      push_cast
      ring
    rw [harg, Complex.norm_exp_I_mul_ofReal]
  have hFderiv (x : ℂ) (v : ℂ) :
      F' x v = psiC (-x) *
        fderiv ℝ (fun z => sphC (1 / 6) (wC * nC x * h * nC z)) 0 v := by
    have hψne : psiC (-x) ≠ 0 := by
      intro hz
      have hxψ := hψnorm x
      rw [hz, norm_zero] at hxψ
      norm_num at hxψ
    letI : Invertible (psiC (-x)) := invertibleOfNonzero hψne
    change fderiv ℝ (psiC (-x) • fun z => sphC (1 / 6) (wC * nC x * h * nC z)) 0 v = _
    rw [fderiv_const_smul_of_invertible (𝕜 := ℝ) (psiC (-x))]
    simp [smul_eq_mul]
  have hpoint (x : ℂ) :
      F' x 1 - (m : ℂ) * Complex.I * F' x Complex.I =
        psiC (-x) * derivVecC m (sphC (1 / 6)) (wC * nC x * h) := by
    rw [hFderiv x 1, hFderiv x Complex.I]
    simp [derivVecC, rtr, mul_assoc]
    ring
  rcases hparam with ⟨hF'_int, hHas⟩
  let c : ℂ := (m : ℂ) * Complex.I
  let T : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)) -
      (ContinuousLinearMap.mulLeftRight ℝ ℂ c 1).comp
        (ContinuousLinearMap.apply ℝ ℂ Complex.I)
  have hcombo :
      (∫ x, F' x) 1 - c * (∫ x, F' x) Complex.I =
        ∫ x, F' x 1 - c * F' x Complex.I := by
    have hT := T.integral_comp_comm hF'_int
    simpa [T, c, ContinuousLinearMap.mulLeftRight_apply, mul_assoc] using hT.symm
  calc
    thetaRootDerivative m (fun z => jacquetC (rtr (h * nC z) (sphC (1 / 6)))) =
        thetaRootDerivative m (fun z => ∫ x, F z x) := by
          exact thetaRootDerivative_congr m hJ
    _ = (∫ x, F' x) 1 - (m : ℂ) * Complex.I * (∫ x, F' x) Complex.I := by
          simp only [thetaRootDerivative]
          rw [hHas.fderiv]
    _ = (∫ x, F' x 1) - (m : ℂ) * Complex.I * (∫ x, F' x Complex.I) := by
          rw [ContinuousLinearMap.integral_apply hF'_int 1,
            ContinuousLinearMap.integral_apply hF'_int Complex.I]
    _ = ∫ x, F' x 1 - (m : ℂ) * Complex.I * F' x Complex.I := by
          rw [← ContinuousLinearMap.integral_apply hF'_int 1,
            ← ContinuousLinearMap.integral_apply hF'_int Complex.I]
          simpa [c] using hcombo
    _ = ∫ x, psiC (-x) * derivVecC m (sphC (1 / 6)) (wC * nC x * h) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hpoint x
    _ = jacquetC (rtr h (derivVecC m (sphC (1 / 6)))) := by
          simp [jacquetC, rtr, mul_assoc]

/-- Differentiate the actual residue coefficient at a lift with identity exterior components; retain the finite multilinear form for the Weyl-sheet proof.
Uses ThetaNormalizationInput.coefficient, ThetaCommonSections, joint root differentiation under torus integrals and jacquetC_derivative. -/
theorem theta_complex_derivative_tensor {P : CoverPackage D S H A}
    {N : ThetaNormalizationInput P} {𝓛 : Finset (SChar S)}
    (B : ThetaCommonSections P N 𝓛) (Q : ThetaFamilyUpstream B) (L : SChar S) (hL : L ∈ 𝓛)
    (r : P.RP) (hr : ∀ v, v ∉ S.Sf → P.compF v r = 1) :
    thetaFamilyW B L (P.q r) = (thetaNormalizationScalar N)⁻¹ *
      N.Λ (fun v => jacquet (P.loc v.1) A (N.μ v.1)
        (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1))) *
      ∏ w, jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6)))) := by
  classical
  let l := (Finset.univ : Finset (InfinitePlace F)).toList
  let c := N.Λ (fun v => jacquet (P.loc v.1) A (N.μ v.1)
    (rtr (P.compF v.1 r) ((B.Fam.sec (1 / 6)).f v.1)))
  let J : InfinitePlace F → ℂ → ℂ := fun w z =>
    jacquetC (rtr (P.compC w r * nC z) (sphC (1 / 6)))
  let d : InfinitePlace F → ℂ := fun w =>
    jacquetC (rtr (P.compC w r) (derivVecC (L.m w) (sphC (1 / 6))))
  have hfactor (z : InfinitePlace F → ℂ) :
      thetaWhit B.C (P.q r * nInf P z) = c * ∏ w, J w (z w) := by
    simpa [c, J] using thetaWhit_arch_factor B r hr z
  have hD : ∀ w, thetaRootDerivative (L.m w) (J w) = d w := by
    intro w
    exact jacquetC_rightRoot_derivative (L.m w) (P.compC w r)
  have hz : ∀ w ∈ l, (0 : InfinitePlace F → ℂ) w = 0 := by
    intro w hw
    simp
  have hproduct := thetaCoordinateDerivativeFold_product L.m l
    (Finset.nodup_toList _) c J d hD 0 hz
  have hfold :
      thetaFamilyDeriv P L.m (thetaWhit B.C) (P.q r) = c * ∏ w, d w := by
    have hcoord := thetaGroupDerivativeFold_eq_coordinate L.m l
      (thetaWhit B.C) (P.q r) (fun z => c * ∏ w, J w (z w)) hfactor
    have hlist : thetaFamilyDeriv P L.m (thetaWhit B.C) (P.q r) =
        thetaGroupDerivativeFold L.m l (thetaWhit B.C) (P.q r) := by
      rfl
    rw [hlist, hcoord]
    simpa [l] using hproduct
  rw [thetaFamilyW, hfold]
  dsimp [c, d]
  ring
end ArtinPrimitiveRoots.A1.Theta
