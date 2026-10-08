import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrefactorDeriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- Off the real axis and xi's zeros, the sharp-zeta logarithmic derivative separates its factors. -/
theorem sharp_logderiv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s.im ≠ 0) (hxi : dedekindXi K s ≠ 0) :
    DifferentiableAt ℂ (dedekindZetaSharp K) s ∧
    dedekindZetaSharp K s ≠ 0 ∧
    dedekindZetaLogDerivative K s =
      -(deriv (dedekindXi K) s / dedekindXi K s) + 1 / s + 1 / (s - 1) +
        deriv (dedekindPrefactor K) s / dedekindPrefactor K s := by
  have hdXi : Differentiable ℂ (dedekindXi K) :=
    (Classical.choose_spec (dedekind_completed K)).1
  have hs₀ : s ≠ 0 := by
    intro h
    apply hs
    simp [h]
  have hs₁ : s - 1 ≠ 0 := by
    intro h
    have heq : s = 1 := sub_eq_zero.mp h
    apply hs
    simp [heq]
  obtain ⟨hdP, hP, _⟩ := prefactor_logderiv K hs
  have hdSub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
    differentiableAt_id.sub_const (1 : ℂ)
  let d : ℂ → ℂ := fun z => z * (z - 1) * dedekindPrefactor K z
  have hd : d s ≠ 0 := mul_ne_zero (mul_ne_zero hs₀ hs₁) hP
  have hdd : DifferentiableAt ℂ d s :=
    (differentiableAt_id.mul hdSub).mul hdP
  have hsharp : dedekindZetaSharp K = fun z : ℂ => dedekindXi K z / d z := rfl
  have hdSharp : DifferentiableAt ℂ (dedekindZetaSharp K) s := by
    rw [hsharp]
    exact (hdXi s).div hdd hd
  have hSharp : dedekindZetaSharp K s ≠ 0 := by
    rw [hsharp]
    exact div_ne_zero hxi hd
  have hSubDer : deriv (fun z : ℂ => z - 1) s = 1 :=
    ((hasDerivAt_id s).sub_const (1 : ℂ)).deriv
  have hSubLog : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, hSubDer]
  have hdlog : logDeriv d s = 1 / s + 1 / (s - 1) +
      deriv (dedekindPrefactor K) s / dedekindPrefactor K s := by
    dsimp only [d]
    rw [logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
        (g := dedekindPrefactor K) s (mul_ne_zero hs₀ hs₁) hP
        (differentiableAt_id.mul hdSub) hdP,
      logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
        s hs₀ hs₁ differentiableAt_id hdSub,
      logDeriv_id', hSubLog, logDeriv_apply]
  have hsharplog : logDeriv (dedekindZetaSharp K) s =
      logDeriv (dedekindXi K) s - logDeriv d s := by
    rw [hsharp]
    exact logDeriv_fun_div (f := dedekindXi K) (g := d) s hxi hd (hdXi s) hdd
  refine ⟨hdSharp, hSharp, ?_⟩
  rw [dedekindZetaLogDerivative, neg_div, ← logDeriv_apply, hsharplog, hdlog,
    logDeriv_apply]
  ring

/-- Away from the real axis, the endpoint and archimedean terms contribute only logarithmic growth. -/
theorem sharp_xi_difference_bound (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      s.re ∈ Set.Icc (-1 / 2 : ℝ) 2 → 3 ≤ |s.im| → dedekindXi K s ≠ 0 →
      ‖dedekindZetaLogDerivative K s +
        deriv (dedekindXi K) s / dedekindXi K s‖ ≤
          C * Real.log (2 + |s.im|) := by
  obtain ⟨B, hB, hgamma⟩ := gamma_horizontal_bound
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  let c : ℝ := NumberField.InfinitePlace.nrComplexPlaces K
  let d : ℝ := |Real.log (absoluteDiscriminant K)| / 2
  let p : ℝ := |Real.log Real.pi| / 2
  let q : ℝ := |Real.log (2 * Real.pi)|
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := abs_nonneg _
  let F : ℝ := 2 + d + r * p + c * q
  let G : ℝ := B * (r / 2 + c)
  have hF : 0 < F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let L₀ : ℝ := Real.log 2
  have hL₀ : 0 < L₀ := Real.log_pos (by norm_num)
  let C : ℝ := F / L₀ + G + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s hRe him hxi
  have hsim : s.im ≠ 0 := by
    intro h
    simp only [h, abs_zero] at him
    linarith only [him]
  let L : ℝ := Real.log (2 + |s.im|)
  have hLge : L₀ ≤ L :=
    Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by linarith [abs_nonneg s.im])
  have hL : 0 < L := hL₀.trans_le hLge
  have hfull : ‖deriv Complex.Gamma s / Complex.Gamma s‖ ≤ B * L :=
    hgamma s hRe (by linarith only [him])
  have hhalfRe : (s / 2).re ∈ Set.Icc (-1 / 2 : ℝ) 2 := by
    rw [Complex.div_ofNat_re]
    constructor <;> linarith [hRe.1, hRe.2]
  have hhalfIm : |(s / 2).im| = |s.im| / 2 := by
    rw [Complex.div_ofNat_im, abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
  have hhalfHeight : 1 ≤ |(s / 2).im| := by
    rw [hhalfIm]
    linarith only [him]
  have hloghalf : Real.log (2 + |(s / 2).im|) ≤ L := by
    apply Real.log_le_log (by positivity : 0 < 2 + |(s / 2).im|)
    rw [hhalfIm]
    linarith only [abs_nonneg s.im]
  have hhalf : ‖deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)‖ ≤ B * L :=
    (hgamma (s / 2) hhalfRe hhalfHeight).trans
      (mul_le_mul_of_nonneg_left hloghalf hB.le)
  let R : ℂ := -(Real.log Real.pi : ℂ) / 2 +
    (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2
  let Q : ℂ := -(Real.log (2 * Real.pi) : ℂ) +
    deriv Complex.Gamma s / Complex.Gamma s
  have hhalfDiv : ‖(deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2‖ ≤
      B * L / 2 := by
    rw [norm_div, Complex.norm_two]
    exact div_le_div_of_nonneg_right hhalf (by norm_num)
  have hR : ‖R‖ ≤ p + B * L / 2 := by
    calc
      ‖R‖ ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ +
          ‖(deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2‖ :=
        norm_add_le _ _
      _ = p + ‖(deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2‖ := by
        simp [p, norm_div, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ p + B * L / 2 := by linarith only [hhalfDiv]
  have hQ : ‖Q‖ ≤ q + B * L := by
    calc
      ‖Q‖ ≤ ‖-(Real.log (2 * Real.pi) : ℂ)‖ +
          ‖deriv Complex.Gamma s / Complex.Gamma s‖ := norm_add_le _ _
      _ = q + ‖deriv Complex.Gamma s / Complex.Gamma s‖ := by
        simp [q, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ q + B * L := by linarith only [hfull]
  have hPform : deriv (dedekindPrefactor K) s / dedekindPrefactor K s =
      (Real.log (absoluteDiscriminant K) : ℂ) / 2 +
        (NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R +
        (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q :=
    (prefactor_logderiv K hsim).2.2
  have hP : ‖deriv (dedekindPrefactor K) s / dedekindPrefactor K s‖ ≤
      d + r * (p + B * L / 2) + c * (q + B * L) := by
    rw [hPform]
    calc
      _ ≤ ‖(Real.log (absoluteDiscriminant K) : ℂ) / 2 +
            (NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R‖ +
          ‖(NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q‖ := norm_add_le _ _
      _ ≤ (‖(Real.log (absoluteDiscriminant K) : ℂ) / 2‖ +
            ‖(NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R‖) +
          ‖(NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q‖ := by
        have h := norm_add_le ((Real.log (absoluteDiscriminant K) : ℂ) / 2)
          ((NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R)
        linarith only [h]
      _ = d + r * ‖R‖ + c * ‖Q‖ := by
        simp [d, r, c, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ d + r * (p + B * L / 2) + c * (q + B * L) := by
        have h₁ := mul_le_mul_of_nonneg_left hR hr
        have h₂ := mul_le_mul_of_nonneg_left hQ hc
        linarith only [h₁, h₂]
  have hrecip (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖(1 : ℂ) / z‖ ≤ 1 := by
    rw [norm_div, norm_one]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hz)).2
    simpa using hz
  have hsNorm : 1 ≤ ‖s‖ :=
    (by linarith only [him] : 1 ≤ |s.im|).trans (Complex.abs_im_le_norm s)
  have hsubNorm : 1 ≤ ‖s - 1‖ := by
    have h : |s.im| ≤ ‖s - 1‖ := by
      simpa only [Complex.sub_im, Complex.one_im, sub_zero] using
        Complex.abs_im_le_norm (s - 1)
    linarith only [him, h]
  have h₁ := hrecip s hsNorm
  have h₂ := hrecip (s - 1) hsubNorm
  have heq : dedekindZetaLogDerivative K s + deriv (dedekindXi K) s / dedekindXi K s =
      1 / s + 1 / (s - 1) + deriv (dedekindPrefactor K) s / dedekindPrefactor K s := by
    rw [(sharp_logderiv K hsim hxi).2.2]
    ring
  have hdiff : ‖dedekindZetaLogDerivative K s +
      deriv (dedekindXi K) s / dedekindXi K s‖ ≤ F + G * L := by
    rw [heq]
    calc
      _ ≤ ‖1 / s + 1 / (s - 1)‖ +
          ‖deriv (dedekindPrefactor K) s / dedekindPrefactor K s‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖) +
          ‖deriv (dedekindPrefactor K) s / dedekindPrefactor K s‖ := by
        have h := norm_add_le ((1 : ℂ) / s) ((1 : ℂ) / (s - 1))
        linarith only [h]
      _ ≤ 2 + d + r * (p + B * L / 2) + c * (q + B * L) := by
        linarith only [h₁, h₂, hP]
      _ = F + G * L := by dsimp [F, G]; ring
  have hFabsorb : F ≤ (F / L₀) * L := by
    have h := mul_le_mul_of_nonneg_left hLge (div_nonneg hF.le hL₀.le)
    have heqF : (F / L₀) * L₀ = F := by field_simp
    rwa [heqF] at h
  have hCge : F / L₀ + G ≤ C := by dsimp [C]; linarith
  calc
    _ ≤ F + G * L := hdiff
    _ ≤ (F / L₀) * L + G * L := by linarith only [hFabsorb]
    _ = (F / L₀ + G) * L := by ring
    _ ≤ C * L := mul_le_mul_of_nonneg_right hCge hL.le

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
