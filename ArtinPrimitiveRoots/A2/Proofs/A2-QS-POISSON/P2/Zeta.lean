import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.Gamma
import ArtinPrimitiveRoots.Hecke.Dedekind.Bounds
import ArtinPrimitiveRoots.Hecke.Theta.DirichletDecomposition
import ArtinPrimitiveRoots.Hecke.Elementary

/-!
# The continued Dedekind zeta function for P2 (totally complex fields)

`Z = qsZetaCont K`: Dirichlet series on `Re s > 1`, the functional equation
`Z(s) = R(1-s) Z(1-s)`, the entire function `Z₁(s) = (s-1) Z(s)` with `Z₁(1) = ρ_K`, and the
polynomial bound of `Z₁` on `-1/2 ≤ Re s ≤ 3/2` (Phragmén–Lindelöf).
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory NumberField
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

variable {K : Type} [Field K] [NumberField K]

theorem qsZetaCont_eq_dedekindZeta [IsTotallyComplex K] {s : ℂ} (hs : 1 < s.re) :
    qsZetaCont K s = dedekindZeta K s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hG : Hecke.dedekindPrefactor K s ≠ 0 :=
    prefactor_ne_zero (not_nonpos_int_of_re_pos (by linarith))
  rw [qsZetaCont, DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
    DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K hs,
    ← Hecke.dedekindPrefactor_eq_completedZetaPrefactor]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

/-- `charValue` of the trivial character of the trivial modulus is `1` on nonzero ideals. -/
theorem charValue_one_trivial {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Hecke.charValue (1 : ClassFieldTheory.RayClassGroup
      (⟨0, ∅⟩ : ClassFieldTheory.RayClassModulus K) →* ℂˣ) I = 1 := by
  have hc : Hecke.IsCoprimeTo (⟨0, ∅⟩ : ClassFieldTheory.RayClassModulus K) I := by
    refine ⟨hI, ?_⟩
    intro v hv
    simp at hv
  unfold Hecke.charValue
  rw [dif_pos hc, MonoidHom.one_apply, Units.val_one]

theorem hasSum_norm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-s))
      (dedekindZeta K s) := by
  set m : ClassFieldTheory.RayClassModulus K := ⟨0, ∅⟩
  have h1 := Hecke.LSeriesRay_eq_tsum_rayIdealDirichletTerm_of_re_gt
    (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) hs
  have h2 := Hecke.summable_rayIdealDirichletTerm (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) hs
  rw [Hecke.LSeriesRay_trivial_eq_dedekindZeta] at h1
  have hHS : HasSum (fun I : Ideal (𝓞 K) =>
      Hecke.rayIdealDirichletTerm (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) s I)
      (dedekindZeta K s) := by
    rw [h1]; exact h2.hasSum
  have hsupp : Function.support (fun I : Ideal (𝓞 K) =>
      Hecke.rayIdealDirichletTerm (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) s I) ⊆
      {I | I ≠ ⊥} := by
    intro I hI h0
    apply hI
    simp [Hecke.rayIdealDirichletTerm, h0]
  have h3 := (hasSum_subtype_iff_of_support_subset hsupp).mpr hHS
  have h4 : HasSum (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      Hecke.rayIdealDirichletTerm (1 : ClassFieldTheory.RayClassGroup m →* ℂˣ) s b.1)
      (dedekindZeta K s) := h3
  convert h4 using 1
  funext b
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    intro h; exact b.2 (Ideal.absNorm_eq_zero_iff.mp h)
  simp only [Function.comp_apply, Hecke.rayIdealDirichletTerm, if_neg hb,
    charValue_one_trivial b.2, Complex.cpow_neg]
  simp

theorem summable_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ((Ideal.absNorm b.1 : ℕ) : ℝ) ^ (-σ)) := by
  have h := (Hecke.summable_idealNormRpow (K := K) hσ).subtype {I | I ≠ ⊥}
  have h' : Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => Hecke.idealNormRpowTerm σ b.1) := h
  convert h' using 1
  funext b
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    intro h; exact b.2 (Ideal.absNorm_eq_zero_iff.mp h)
  simp [Hecke.idealNormRpowTerm, hb]

theorem norm_natCast_cpow_ideal (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) (s : ℂ) :
    ‖((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (-s)‖ = ((Ideal.absNorm b.1 : ℕ) : ℝ) ^ (-s.re) := by
  have hb : 0 < Ideal.absNorm b.1 := by
    rw [Nat.pos_iff_ne_zero]
    intro h; exact b.2 (Ideal.absNorm_eq_zero_iff.mp h)
  rw [Complex.norm_natCast_cpow_of_pos hb]
  simp

/-- `ζ_K(3/2) = Σ N b^{-3/2}` as a real bound. -/
def zb (K : Type) [Field K] [NumberField K] : ℝ :=
  ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, ((Ideal.absNorm b.1 : ℕ) : ℝ) ^ (-(3/2 : ℝ))

theorem zb_nonneg : 0 ≤ zb K := tsum_nonneg (fun _ => by positivity)

theorem norm_qsZetaCont_le [IsTotallyComplex K] {s : ℂ} (hs : s.re = 3/2) :
    ‖qsZetaCont K s‖ ≤ zb K := by
  rw [qsZetaCont_eq_dedekindZeta (by rw [hs]; norm_num), ← (hasSum_norm_cpow (K := K)
    (by rw [hs]; norm_num)).tsum_eq]
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine (summable_norm_rpow (K := K) (σ := 3/2) (by norm_num)).congr (fun b => ?_)
    rw [norm_natCast_cpow_ideal, hs]
  · unfold zb
    congr 1
    funext b
    rw [norm_natCast_cpow_ideal, hs]

/-- The functional equation `Z(s) = R(1-s) Z(1-s)`. -/
theorem qsZetaCont_fe [IsTotallyComplex K] {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (h1 : ∀ m : ℕ, s ≠ -m) (h2 : ∀ m : ℕ, 1 - s ≠ -m) :
    qsZetaCont K s = qsGammaRatio K (1 - s) * qsZetaCont K (1 - s) := by
  have hG1 : Hecke.dedekindPrefactor K s ≠ 0 := prefactor_ne_zero h1
  have hG2 : Hecke.dedekindPrefactor K (1 - s) ≠ 0 := prefactor_ne_zero h2
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1s1 : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hxi : DedekindResidue.completedDedekindZetaEntire K (1 - s) =
      DedekindResidue.completedDedekindZetaEntire K s := by
    rw [DedekindResidue.completedDedekindZetaEntire_eq K h1s0 h1s1,
      DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
      DedekindResidue.completedDedekindZeta_one_sub]
    ring
  rw [qsZetaCont, qsZetaCont, qsGammaRatio, show (1 : ℂ) - (1 - s) = s by ring, hxi]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-! ### `Z₁(s) = (s-1) Z(s)` as an entire function -/

/-- An entire expression for `(s · G_K(s))⁻¹`. -/
def zetaE (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹ * ((Gammaℂ s)⁻¹) ^ (InfinitePlace.nrComplexPlaces K - 1) *
    ((2 * (Real.pi : ℂ)) ^ s / 2) * (Complex.Gamma (s + 1))⁻¹

/-- `Z₁(s) = ξ_K(s) (s G_K(s))⁻¹ = (s-1) ζ_K(s)`. -/
def Z1 (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  DedekindResidue.completedDedekindZetaEntire K s * zetaE K s

theorem differentiable_zetaE : Differentiable ℂ (zetaE K) := by
  intro s
  unfold zetaE
  refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul ?_ ?_) ?_) ?_
  · refine DifferentiableAt.inv ?_ ?_
    · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl (by exact_mod_cast dK_pos.ne'))
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast dK_pos.ne'))
  · exact (differentiable_Gammaℂ_inv s).pow _
  · exact (differentiableAt_id.const_cpow (Or.inl (by simp [Real.pi_ne_zero]))).div_const 2
  · exact (Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)) s |>.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp [one_div])

theorem differentiable_Z1 : Differentiable ℂ (Z1 K) :=
  (DedekindResidue.differentiable_completedDedekindZetaEntire K).mul differentiable_zetaE

theorem zetaE_eq [IsTotallyComplex K] {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) :
    zetaE K s = (s * Hecke.dedekindPrefactor K s)⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hr := one_le_nrComplexPlaces (K := K)
  obtain ⟨k, hk⟩ : ∃ k, InfinitePlace.nrComplexPlaces K = k + 1 :=
    ⟨InfinitePlace.nrComplexPlaces K - 1, by omega⟩
  have hD : ((dK K : ℝ) : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast dK_pos.ne'))
  have h2pi : (2 * (Real.pi : ℂ)) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hΓc : Gammaℂ s ≠ 0 := by
    rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) hΓ
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by simp [Real.pi_ne_zero]))
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [prefactor_tc, zetaE, Complex.Gamma_add_one s hs0, hk, show k + 1 - 1 = k by omega,
    pow_succ]
  have e1 : ((dK K : ℝ) : ℂ) ^ (s / 2) * (((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hD
  have e2 : Gammaℂ s ^ k * ((Gammaℂ s)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hΓc, one_pow]
  have e3 : Gammaℂ s * ((2 * (Real.pi : ℂ)) ^ s / 2) = Complex.Gamma s := by
    rw [Gammaℂ_def, Complex.cpow_neg]
    field_simp
  have e4 : s * Complex.Gamma s * (s * Complex.Gamma s)⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero hs0 hΓ)
  calc s * (((dK K : ℝ) : ℂ) ^ (s / 2) * (Gammaℂ s ^ k * Gammaℂ s)) *
        ((((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹ * (Gammaℂ s)⁻¹ ^ k * ((2 * (Real.pi : ℂ)) ^ s / 2) *
          (s * Complex.Gamma s)⁻¹)
      = (((dK K : ℝ) : ℂ) ^ (s / 2) * (((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹) *
          (Gammaℂ s ^ k * ((Gammaℂ s)⁻¹) ^ k) *
          (s * (Gammaℂ s * ((2 * (Real.pi : ℂ)) ^ s / 2)) * (s * Complex.Gamma s)⁻¹) := by ring
    _ = 1 := by rw [e1, e2, e3, e4]; ring

theorem Z1_eq [IsTotallyComplex K] {s : ℂ} (hs1 : s ≠ 1) (hs : ∀ m : ℕ, s ≠ -m) :
    Z1 K s = (s - 1) * qsZetaCont K s := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hG : Hecke.dedekindPrefactor K s ≠ 0 := prefactor_ne_zero hs
  rw [Z1, zetaE_eq hs, qsZetaCont]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

theorem Z1_one [IsTotallyComplex K] : Z1 K 1 = (qsResidueOne K : ℂ) := by
  have hc1 : ContinuousAt (fun x : ℝ => Z1 K (x : ℂ)) 1 :=
    ((differentiable_Z1 (K := K)) ((1 : ℝ) : ℂ)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hcont : Tendsto (fun x : ℝ => Z1 K (x : ℂ)) (𝓝[>] 1) (𝓝 (Z1 K 1)) := by
    have := hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
    rw [Complex.ofReal_one] at this
    exact this
  have hlim : Tendsto (fun x : ℝ => Z1 K (x : ℂ)) (𝓝[>] 1)
      (𝓝 ((NumberField.dedekindZeta_residue K : ℝ) : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hre : 1 < (x : ℂ).re := by simpa using hx1
    rw [Z1_eq (by intro h; have := congrArg Complex.re h; simp at this; linarith)
      (not_nonpos_int_of_re_pos (by simp; linarith)), qsZetaCont_eq_dedekindZeta hre]
  exact tendsto_nhds_unique hcont hlim

/-- Crude growth of `zetaE` on the strip. -/
theorem exists_zetaE_growth [IsTotallyComplex K] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      ‖zetaE K s‖ ≤ C * Real.exp ((InfinitePlace.nrComplexPlaces K * Real.pi) * |s.im|) := by
  obtain ⟨M', hM'0, hM'⟩ := exists_norm_inv_Gamma_le
  set r := InfinitePlace.nrComplexPlaces K
  have hr := one_le_nrComplexPlaces (K := K)
  have hd1 := dK_one_le (K := K)
  set P : ℝ := (2 * Real.pi) ^ (2:ℝ)
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by norm_num)
  refine ⟨dK K ^ ((1:ℝ)/4) * (P * M') ^ (r - 1) * P * M', by positivity, fun s h1 h2 ht => ?_⟩
  have h2pi : ∀ x : ℝ, x ≤ 2 → (2 * Real.pi) ^ x ≤ P := fun x hx =>
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hx
  have hnorm2pi : ‖(2 * (Real.pi : ℂ)) ^ s‖ = (2 * Real.pi) ^ s.re := by
    have : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have hA : ‖(((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹‖ ≤ dK K ^ ((1:ℝ)/4) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos dK_pos, ← Real.rpow_neg dK_pos.le]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by simp; linarith)
  have hB : ‖(Gammaℂ s)⁻¹‖ ≤ P * M' * Real.exp (Real.pi * |s.im|) := by
    rw [norm_inv, norm_Gammaℂ, mul_inv, mul_inv, Real.rpow_neg (by positivity), inv_inv,
      ← norm_inv]
    have hg := hM' s (by linarith) (by linarith) ht
    have hp := h2pi s.re (by linarith)
    calc 2⁻¹ * (2 * Real.pi) ^ s.re * ‖(Complex.Gamma s)⁻¹‖
        ≤ 1 * P * (M' * Real.exp (Real.pi * |s.im|)) := by
          gcongr
          norm_num
      _ = P * M' * Real.exp (Real.pi * |s.im|) := by ring
  have hC : ‖(2 * (Real.pi : ℂ)) ^ s / 2‖ ≤ P := by
    rw [norm_div, hnorm2pi, Complex.norm_two]
    have := h2pi s.re (by linarith)
    have : 0 ≤ (2 * Real.pi) ^ s.re := by positivity
    linarith
  have hDg : ‖(Complex.Gamma (s + 1))⁻¹‖ ≤ M' * Real.exp (Real.pi * |s.im|) := by
    have := hM' (s + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using this
  unfold zetaE
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  calc ‖(((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹‖ * ‖(Gammaℂ s)⁻¹‖ ^ (r - 1) *
        ‖(2 * (Real.pi : ℂ)) ^ s / 2‖ * ‖(Complex.Gamma (s + 1))⁻¹‖
      ≤ dK K ^ ((1:ℝ)/4) * (P * M' * Real.exp (Real.pi * |s.im|)) ^ (r - 1) * P *
          (M' * Real.exp (Real.pi * |s.im|)) := by
        have e1 := pow_le_pow_left₀ (norm_nonneg _) hB (r - 1)
        have e2 : ‖(((dK K : ℝ) : ℂ) ^ (s / 2))⁻¹‖ * ‖(Gammaℂ s)⁻¹‖ ^ (r - 1) ≤
            dK K ^ ((1:ℝ)/4) * (P * M' * Real.exp (Real.pi * |s.im|)) ^ (r - 1) :=
          mul_le_mul hA e1 (by positivity) (by positivity)
        have e3 := mul_le_mul e2 hC (norm_nonneg _) (by positivity)
        exact mul_le_mul e3 hDg (norm_nonneg _) (by positivity)
    _ = dK K ^ ((1:ℝ)/4) * (P * M') ^ (r - 1) * P * M' *
          (Real.exp (Real.pi * |s.im|) ^ (r - 1) * Real.exp (Real.pi * |s.im|)) := by
        rw [mul_pow]; ring
    _ = dK K ^ ((1:ℝ)/4) * (P * M') ^ (r - 1) * P * M' *
          Real.exp ((r * Real.pi) * |s.im|) := by
        rw [← pow_succ, show r - 1 + 1 = r by omega, ← Real.exp_nat_mul]
        ring_nf

/-- Polynomial bound for `Z₁` on `-1/2 ≤ Re s ≤ 3/2`. -/
theorem exists_Z1_poly [IsTotallyComplex K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 →
      ‖Z1 K s‖ ≤ C * (1 + |s.im|) ^ (2 * InfinitePlace.nrComplexPlaces K + 1) := by
  obtain ⟨B, hB0, hB⟩ :=
    Hecke.DedekindBounds.exists_completedDedekindZetaEntire_strip_bound K (-1/2) (3/2)
      (by norm_num)
  obtain ⟨CE, hCE0, hCE⟩ := exists_zetaE_growth (K := K)
  set r := InfinitePlace.nrComplexPlaces K
  have hzb := zb_nonneg (K := K)
  have hd1 := dK_one_le (K := K)
  -- growth
  have hgr : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → 1 ≤ |s.im| →
      ‖Z1 K s‖ ≤ (B * (25/4) * CE) * Real.exp ((r * Real.pi + 2) * |s.im|) := by
    intro s h1 h2 ht
    have hs : 1 + ‖s‖ ≤ (5/2) * Real.exp |s.im| := by
      have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      have hre : |s.re| ≤ 3/2 := abs_le.mpr ⟨by linarith, h2⟩
      have he := Real.add_one_le_exp |s.im|
      nlinarith [abs_nonneg s.im]
    have hxi : ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
        B * ((5/2) * Real.exp |s.im|) ^ 2 :=
      (hB s h1 h2).trans (by gcongr)
    rw [Z1, norm_mul]
    calc ‖DedekindResidue.completedDedekindZetaEntire K s‖ * ‖zetaE K s‖
        ≤ (B * ((5/2) * Real.exp |s.im|) ^ 2) * (CE * Real.exp ((r * Real.pi) * |s.im|)) :=
          mul_le_mul hxi (hCE s h1 h2 ht) (norm_nonneg _) (by positivity)
      _ = (B * (25/4) * CE) * (Real.exp |s.im| ^ 2 * Real.exp ((r * Real.pi) * |s.im|)) := by
          ring
      _ = (B * (25/4) * CE) * Real.exp ((r * Real.pi + 2) * |s.im|) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          ring_nf
  -- edges
  have hright : ∀ s : ℂ, s.re = 3/2 →
      ‖Z1 K s‖ ≤ (zb K + 2 * dK K * zb K) * (1 + |s.im|) ^ (2 * r + 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    rw [Z1_eq hs1 (not_nonpos_int_of_re_pos (by rw [hs]; norm_num)), norm_mul]
    have h1 : ‖s - 1‖ ≤ 1 + |s.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (s - 1)
      have hre : (s - 1).re = 1/2 := by simp [hs]; norm_num
      have him : (s - 1).im = s.im := by simp
      rw [hre, him] at this
      norm_num at this
      linarith
    have hp : 1 + |s.im| ≤ (1 + |s.im|) ^ (2 * r + 1) :=
      le_self_pow₀ (by linarith [abs_nonneg s.im]) (by omega)
    have hpos1 : (0:ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
    calc ‖s - 1‖ * ‖qsZetaCont K s‖ ≤ (1 + |s.im|) * zb K :=
          mul_le_mul h1 (norm_qsZetaCont_le hs) (norm_nonneg _) hpos1
      _ ≤ (1 + |s.im|) ^ (2 * r + 1) * zb K := mul_le_mul_of_nonneg_right hp hzb
      _ ≤ (zb K + 2 * dK K * zb K) * (1 + |s.im|) ^ (2 * r + 1) := by
          have : 0 ≤ 2 * dK K * zb K * (1 + |s.im|) ^ (2 * r + 1) :=
            mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) dK_pos.le) hzb) (pow_nonneg hpos1 _)
          nlinarith
  have hleft : ∀ s : ℂ, s.re = -1/2 →
      ‖Z1 K s‖ ≤ (zb K + 2 * dK K * zb K) * (1 + |s.im|) ^ (2 * r + 1) := by
    intro s hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have hnint : ∀ m : ℕ, s ≠ -m := by
      refine not_nonpos_int_of_re_not_int (fun m hm => ?_)
      rw [hs] at hm
      have : (2 : ℝ) * m = -1 := by linarith
      have h' : (2 * m : ℤ) = -1 := by exact_mod_cast this
      omega
    have h1s : (1 - s).re = 3/2 := by simp [hs]; norm_num
    rw [Z1_eq hs1 hnint, qsZetaCont_fe hs0 hs1 hnint (not_nonpos_int_of_re_pos (by rw [h1s]; norm_num)),
      norm_mul, norm_mul, norm_ratio_three_halves h1s]
    have hsm1 : ‖s - 1‖ ≤ 2 * (1 + |s.im|) := by
      have := Complex.norm_le_abs_re_add_abs_im (s - 1)
      have hre : (s - 1).re = -3/2 := by simp [hs]; norm_num
      have him : (s - 1).im = s.im := by simp
      rw [hre, him] at this
      norm_num at this
      linarith [abs_nonneg s.im]
    have hv : ‖1 - s - 1‖ ^ 2 = 1/4 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hs]
      ring
    have hq : (‖1 - s - 1‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r ≤ (1 + |s.im|) ^ (2 * r) := by
      rw [pow_mul, hv]
      refine pow_le_pow_left₀ (by positivity) ?_ r
      have h4 : (1:ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have : 1/4 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
      exact (div_le_self (by positivity) h4).trans this
    have hz := norm_qsZetaCont_le (K := K) h1s
    have hpos1 : (0:ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
    have hdz : 0 ≤ dK K := dK_pos.le
    have hA : dK K * (‖1 - s - 1‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * ‖qsZetaCont K (1 - s)‖ ≤
        dK K * (1 + |s.im|) ^ (2 * r) * zb K :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq hdz) hz (norm_nonneg _)
        (mul_nonneg hdz (pow_nonneg hpos1 _))
    have hAn : 0 ≤ dK K * (‖1 - s - 1‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * ‖qsZetaCont K (1 - s)‖ :=
      mul_nonneg (mul_nonneg hdz (by positivity)) (norm_nonneg _)
    calc ‖s - 1‖ * (dK K * (‖1 - s - 1‖ ^ 2 / (4 * Real.pi ^ 2)) ^ r * ‖qsZetaCont K (1 - s)‖)
        ≤ (2 * (1 + |s.im|)) * (dK K * (1 + |s.im|) ^ (2 * r) * zb K) :=
          mul_le_mul hsm1 hA hAn (by linarith)
      _ = 2 * dK K * zb K * (1 + |s.im|) ^ (2 * r + 1) := by ring
      _ ≤ (zb K + 2 * dK K * zb K) * (1 + |s.im|) ^ (2 * r + 1) := by
          have : 0 ≤ zb K * (1 + |s.im|) ^ (2 * r + 1) := mul_nonneg hzb (pow_nonneg hpos1 _)
          nlinarith
  have hbd := pl_poly_strip (f := Z1 K) (a := -1/2) (b := 3/2) (by norm_num)
    (fun s _ _ => (differentiable_Z1 (K := K)) s) (r * Real.pi + 2) (B * (25/4) * CE) hgr
    (2 * r + 1) (zb K + 2 * dK K * zb K) hleft hright
  refine ⟨_, ?_, hbd⟩
  have : 0 ≤ zb K + 2 * dK K * zb K :=
    add_nonneg hzb (mul_nonneg (mul_nonneg (by norm_num) dK_pos.le) hzb)
  exact mul_nonneg (mul_nonneg this (by positivity)) (by norm_num)

end ArtinPrimitiveRoots.A2.QSP2
