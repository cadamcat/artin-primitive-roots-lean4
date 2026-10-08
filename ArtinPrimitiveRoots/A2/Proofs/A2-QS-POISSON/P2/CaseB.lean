import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.CaseA
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0

/-!
# P2 data for the transformed square weight `f(y) = (T h)(y²)`

`Mellin f(s) = ½ R(s/2) Φ_h(1 - s/2)` (via `qs_transform_mellin_P0`);
`Ψ(s) = ½ ξ_K(s) Q(s) G_K(1-s/2)⁻¹ Φ_h(1-s/2)` with `Q(s) = G_K(s/2)/G_K(s)` written
holomorphically near `s = 0`; `D(u) = ½ G_K(u) Q(1-u) G_K((1+u)/2)⁻¹ Φ_h((1+u)/2)`.
-/

set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set NumberField
open scoped NumberField

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSP2

variable {K : Type} [Field K] [NumberField K]

/-- A holomorphic expression for `G_K(s/2)/G_K(s)` (on `Re s > -2`). -/
def Qd (K : Type) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((dK K : ℝ) : ℂ) ^ (s / 4))⁻¹ *
    ((2 * (Real.pi : ℂ)) ^ (s / 2) * 2 * Complex.Gamma (s / 2 + 1) *
      (Complex.Gamma (s + 1))⁻¹) ^ InfinitePlace.nrComplexPlaces K

theorem differentiableAt_Qd {s : ℂ} (hs : -2 < s.re) : DifferentiableAt ℂ (Qd K) s := by
  unfold Qd
  refine DifferentiableAt.mul ?_ (DifferentiableAt.pow ?_ _)
  · refine DifferentiableAt.inv ?_ ?_
    · exact (differentiableAt_id.div_const 4).const_cpow (Or.inl (by exact_mod_cast dK_pos.ne'))
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast dK_pos.ne'))
  · refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul ?_
      (differentiableAt_const _)) ?_) ?_
    · exact (differentiableAt_id.div_const 2).const_cpow (Or.inl (by simp [Real.pi_ne_zero]))
    · refine DifferentiableAt.comp (g := Complex.Gamma) (f := fun s : ℂ => s / 2 + 1) s ?_
        (by fun_prop)
      exact Complex.differentiableAt_Gamma _ (not_nonpos_int_of_re_pos (by simp; linarith))
    · exact DifferentiableAt.comp (g := fun z => (Complex.Gamma z)⁻¹) (f := fun s : ℂ => s + 1) s
        (Complex.differentiable_one_div_Gamma.differentiableAt.congr_of_eventuallyEq
          (Eventually.of_forall fun z => by simp [one_div])) (by fun_prop)

theorem Qd_eq [IsTotallyComplex K] {s : ℂ} (hs0 : s ≠ 0) (hs : ∀ m : ℕ, s ≠ -m)
    (hs2 : ∀ m : ℕ, s / 2 ≠ -m) :
    Qd K s = Hecke.dedekindPrefactor K (s / 2) * (Hecke.dedekindPrefactor K s)⁻¹ := by
  have hG : Hecke.dedekindPrefactor K s ≠ 0 := prefactor_ne_zero hs
  rw [eq_mul_inv_iff_mul_eq₀ hG, prefactor_tc, prefactor_tc, Qd]
  set D : ℂ := ((dK K : ℝ) : ℂ) with hD
  set P : ℂ := 2 * (Real.pi : ℂ) with hP
  have hD0 : D ≠ 0 := by rw [hD]; exact_mod_cast dK_pos.ne'
  have hP0 : P ≠ 0 := by rw [hP]; simp [Real.pi_ne_zero]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hΓ2 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hs2
  have hs20 : s / 2 ≠ 0 := by simpa using hs2 0
  have hD4 : D ^ (s / 2) = D ^ (s / 4) * D ^ (s / 4) := by
    rw [← Complex.cpow_add _ _ hD0]; ring_nf
  have hD4' : D ^ (s / 4) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hD0)
  have hPs : P ^ (-s) = (P ^ (s / 2) * P ^ (s / 2))⁻¹ := by
    rw [← Complex.cpow_add _ _ hP0, ← Complex.cpow_neg]; ring_nf
  have hPs2 : P ^ (-(s / 2)) = (P ^ (s / 2))⁻¹ := Complex.cpow_neg _ _
  have hP2 : P ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP0)
  have hkey : (P ^ (s / 2) * 2 * Complex.Gamma (s / 2 + 1) * (Complex.Gamma (s + 1))⁻¹) *
      Gammaℂ s = Gammaℂ (s / 2) := by
    rw [Gammaℂ_def, Gammaℂ_def, Complex.Gamma_add_one _ hs20, Complex.Gamma_add_one _ hs0,
      ← hP, hPs, hPs2]
    field_simp
  rw [hD4, show s / 2 / 2 = s / 4 by ring]
  calc (D ^ (s / 4))⁻¹ * (P ^ (s / 2) * 2 * Complex.Gamma (s / 2 + 1) *
        (Complex.Gamma (s + 1))⁻¹) ^ InfinitePlace.nrComplexPlaces K *
        (D ^ (s / 4) * D ^ (s / 4) * Gammaℂ s ^ InfinitePlace.nrComplexPlaces K)
      = ((D ^ (s / 4))⁻¹ * D ^ (s / 4)) * D ^ (s / 4) *
        ((P ^ (s / 2) * 2 * Complex.Gamma (s / 2 + 1) * (Complex.Gamma (s + 1))⁻¹) *
          Gammaℂ s) ^ InfinitePlace.nrComplexPlaces K := by rw [mul_pow]; ring
    _ = D ^ (s / 4) * Gammaℂ (s / 2) ^ InfinitePlace.nrComplexPlaces K := by
        rw [inv_mul_cancel₀ hD4', one_mul, hkey]

/-! ### Case B -/

def caseBPhi (K : Type) [Field K] [NumberField K] (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * qsGammaRatio K (s / 2) * qsPhiH h (1 - s / 2)

theorem mellin_caseB [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) {s : ℂ}
    (h1 : 0 < s.re) (h2 : s.re < 2) :
    mellin (fun y : ℝ => qsTransform K h (y ^ 2)) s = caseBPhi K h s := by
  rw [mellin_sq, qs_transform_mellin_P0 h hh (s / 2) (by simp; linarith) (by simp; linarith),
    mellin_qsWeight hh (by simp; linarith), caseBPhi]
  ring

theorem continuousAt_caseBPhi [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) {s : ℂ}
    (h1 : 0 < s.re) (h2 : s.re < 2) : ContinuousAt (caseBPhi K h) s := by
  have hd1 : DifferentiableAt ℂ (fun s : ℂ => qsGammaRatio K (s / 2)) s :=
    DifferentiableAt.comp (g := qsGammaRatio K) (f := fun s : ℂ => s / 2) s
      (differentiableAt_ratio (not_nonpos_int_of_re_pos (by simp; linarith))) (by fun_prop)
  have hne : 1 - s / 2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hd2 : DifferentiableAt ℂ (fun s : ℂ => qsPhiH h (1 - s / 2)) s :=
    DifferentiableAt.comp (g := qsPhiH h) (f := fun s : ℂ => 1 - s / 2) s
      (differentiableAt_qsPhiH hh hne) (by fun_prop)
  exact ((continuousAt_const.mul hd1.continuousAt).mul hd2.continuousAt)

/-- Decay of `Φ_B` on `Re s = σ ∈ (0, 2)`, `|Im s| ≥ 2`. -/
theorem caseBPhi_decay [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 3/2 → 2 ≤ |s.im| →
      ‖caseBPhi K h s‖ ≤ C * (1 + |s.im|) ^ (2 * InfinitePlace.nrComplexPlaces K) /
        (|s.im| / 2) ^ M := by
  obtain ⟨CR, hCR0, hCR⟩ := exists_ratio_poly_wide (K := K)
  obtain ⟨C, hC⟩ := qsPhiH_decay hh M (1/4) (5/4)
  set r := InfinitePlace.nrComplexPlaces K
  refine ⟨CR * |C| / 2, by positivity, fun s h1 h2 ht => ?_⟩
  have hre : (s / 2).re = s.re / 2 := by simp
  have him : (s / 2).im = s.im / 2 := by simp
  have hR := hCR (s / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him, abs_div, abs_two]; linarith)
  rw [him, abs_div, abs_two] at hR
  have hre' : (1 - s / 2).re = 1 - s.re / 2 := by simp
  have him' : (1 - s / 2).im = -(s.im / 2) := by simp
  have hφ := hC (1 - s / 2) (by rw [hre']; linarith) (by rw [hre']; linarith)
    (by rw [him', abs_neg, abs_div, abs_two]; linarith)
  rw [him', abs_neg, abs_div, abs_two] at hφ
  have hpos : 0 < (|s.im| / 2) ^ M := by
    have : 0 < |s.im| := by linarith
    positivity
  have hR' : ‖qsGammaRatio K (s / 2)‖ ≤ CR * (1 + |s.im|) ^ (2 * r) := by
    refine hR.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hCR0)
    linarith [abs_nonneg s.im]
  unfold caseBPhi
  rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖qsGammaRatio K (s / 2)‖ * ‖qsPhiH h (1 - s / 2)‖
      ≤ 1 / 2 * (CR * (1 + |s.im|) ^ (2 * r)) * (|C| / (|s.im| / 2) ^ M) := by
        gcongr
        exact hφ.trans (div_le_div_of_nonneg_right (le_abs_self _) hpos.le)
    _ = CR * |C| / 2 * (1 + |s.im|) ^ (2 * r) / (|s.im| / 2) ^ M := by ring

theorem caseBPhi_line_decay [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) {σ : ℝ}
    (h1 : -1/2 ≤ σ) (h2 : σ ≤ 3/2) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖caseBPhi K h (σ + t * I)‖ ≤ C / t ^ 2 := by
  set r := InfinitePlace.nrComplexPlaces K
  obtain ⟨C, hC0, hC⟩ := caseBPhi_decay (K := K) hh (2 * r + 2)
  refine ⟨C * 4 ^ (2 * r + 1), fun t ht => ?_⟩
  have hb := hC (σ + t * I) (by simp; linarith) (by simp; linarith) (by simpa using ht)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_zero, mul_one, zero_add, add_zero] at hb
  have ht1 : 1 ≤ |t| := by linarith
  have hsq : t ^ 2 = |t| ^ 2 := (sq_abs _).symm
  calc ‖caseBPhi K h (σ + t * I)‖ ≤ C * (1 + |t|) ^ (2 * r) / (|t| / 2) ^ (2 * r + 2) := hb
    _ = C * ((1 + |t|) ^ (2 * r) / (|t| / 2) ^ (2 * r + 2)) := by ring
    _ ≤ C * (4 ^ (2 * r + 1) / |t| ^ 2) :=
        mul_le_mul_of_nonneg_left (pow_div_aux (2 * r) ht1) hC0
    _ = C * 4 ^ (2 * r + 1) / t ^ 2 := by rw [hsq]; ring

/-- `Mellin(T h ∘ sq)` converges absolutely on `Re s = 3/2`. -/
theorem mellinConvergent_caseB [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) :
    MellinConvergent (fun y : ℝ => qsTransform K h (y ^ 2)) ((3/2 : ℝ) : ℂ) := by
  obtain ⟨hsm, C, hC0, hC⟩ := qs_transform_bounds_P0 (K := K) h hh 2 0 (1/8) (by norm_num)
  simp only [iteratedDeriv_zero] at hC
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (((3/2 : ℝ) : ℂ) - 1) •
      qsTransform K h (t ^ 2)) (Ioi 0) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.smul (continuousAt_ofReal_cpow_const _ _ (Or.inr ht0.ne')) ?_
    have hT : ContinuousAt (qsTransform K h) (t ^ 2) :=
      hsm.continuousOn.continuousAt (Ioi_mem_nhds (by positivity))
    exact ContinuousAt.comp (g := qsTransform K h) (f := fun a : ℝ => a ^ 2) hT
      (continuous_pow 2).continuousAt
  have hmeas := hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hnorm : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ (((3/2 : ℝ) : ℂ) - 1) • qsTransform K h (t ^ 2)‖ =
      t ^ (1/2 : ℝ) * ‖qsTransform K h (t ^ 2)‖ := by
    intro t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    norm_num
  have hsqpow : ∀ t : ℝ, 0 < t → ∀ c : ℝ, (t ^ 2) ^ c = t ^ (2 * c) := by
    intro t ht c
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' (integrableOn_const (C := C) (μ := volume) (s := Ioc (0:ℝ) 1)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [hnorm t ht0]
    have hb := (hC (t ^ 2) (by positivity)).1 (by nlinarith [ht.2])
    rw [hsqpow t ht0] at hb
    calc t ^ (1/2 : ℝ) * ‖qsTransform K h (t ^ 2)‖ ≤ t ^ (1/2 : ℝ) * (C * t ^ (2 * (-((0:ℕ):ℝ) - 1/8))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * t ^ (1/4 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add ht0]
          norm_num
      _ ≤ C * 1 := by
          gcongr
          exact Real.rpow_le_one ht0.le ht.2 (by norm_num)
      _ = C := mul_one C
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-7/2 : ℝ) < -1)
      zero_lt_one).const_mul C) (hmeas.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    rw [hnorm t ht0]
    have hb := (hC (t ^ 2) (by positivity)).2 (by nlinarith)
    rw [hsqpow t ht0] at hb
    calc t ^ (1/2 : ℝ) * ‖qsTransform K h (t ^ 2)‖ ≤ t ^ (1/2 : ℝ) * (C * t ^ (2 * (-((2:ℕ):ℝ)))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * t ^ (-7/2 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add ht0]
          norm_num

theorem not_nonpos_int_half {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) (hs0 : s ≠ 0) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have hm1 : (m : ℝ) ≤ 1/4 := by linarith
  have hm0 : m = 0 := by
    by_contra h
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith
  subst hm0
  apply hs0
  have : s / 2 = 0 := by simpa using hm
  simpa using this

theorem not_nonpos_int_strip {s : ℂ} (h1 : -1/2 ≤ s.re) (h2 : s.re ≤ 3/2) (hs0 : s ≠ 0) :
    ∀ m : ℕ, s ≠ -m := by
  intro m hm
  have hre := congrArg Complex.re hm
  simp at hre
  have hm1 : (m : ℝ) ≤ 1/2 := by linarith
  have hm0 : m = 0 := by
    by_contra h
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith
  subst hm0
  exact hs0 (by simpa using hm)

/-- The P2 data of `(T h)(y²)`. -/
def caseBData [IsTotallyComplex K] {h : ℝ → ℂ} (hh : IsQSWeight h) :
    P2Data K (fun y : ℝ => qsTransform K h (y ^ 2)) where
  Φ := caseBPhi K h
  Ψ := fun s => (1 / 2 : ℂ) * DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
    (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2)
  D := fun u => (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * Qd K (1 - u) *
    (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * qsPhiH h ((1 + u) / 2)
  inv := by
    intro x hx
    have hvert : VerticalIntegrable (mellin (fun y : ℝ => qsTransform K h (y ^ 2))) (3/2) := by
      unfold Complex.VerticalIntegrable
      obtain ⟨C, hC⟩ := caseBPhi_line_decay (K := K) hh (σ := 3/2) (by norm_num) (by norm_num)
      have hc : Continuous (fun t : ℝ => caseBPhi K h ((3/2 : ℝ) + t * I)) := by
        refine continuous_iff_continuousAt.2 (fun t => ?_)
        exact (continuousAt_caseBPhi hh (by norm_num) (by norm_num)).comp
          (f := fun t : ℝ => ((3/2 : ℝ) : ℂ) + t * I) (by fun_prop)
      have := integrable_of_cont_decay_T hc (by norm_num) hC
      refine this.congr (Eventually.of_forall fun t => ?_)
      exact (mellin_caseB hh (by norm_num) (by norm_num)).symm
    obtain ⟨hsm, -⟩ := qs_transform_bounds_P0 (K := K) h hh 0 0 1 (by norm_num)
    have hcont : ContinuousAt (fun y : ℝ => qsTransform K h (y ^ 2)) x :=
      ContinuousAt.comp (g := qsTransform K h) (f := fun a : ℝ => a ^ 2)
        (hsm.continuousOn.continuousAt (Ioi_mem_nhds (by positivity)))
        (continuous_pow 2).continuousAt
    rw [← mellinInv_mellin_eq (3/2) _ hx (mellinConvergent_caseB hh) hvert hcont]
    simp only [mellinInv]
    congr 2
    funext t
    rw [mellin_caseB hh (by norm_num) (by norm_num)]
  Φint := by
    obtain ⟨C, hC⟩ := caseBPhi_line_decay (K := K) hh (σ := 3/2) (by norm_num) (by norm_num)
    have hc : Continuous (fun t : ℝ => caseBPhi K h ((3/2 : ℝ) + t * I)) := by
      refine continuous_iff_continuousAt.2 (fun t => ?_)
      exact (continuousAt_caseBPhi hh (by norm_num) (by norm_num)).comp
        (f := fun t : ℝ => ((3/2 : ℝ) : ℂ) + t * I) (by fun_prop)
    exact integrable_of_cont_decay_T hc (by norm_num) hC
  mel := fun s h1 h2 => mellin_caseB hh h1 h2
  Φc1 := continuousAt_caseBPhi hh (by norm_num) (by norm_num)
  Ψd := by
    intro s h1 h2
    have hne : 1 - s / 2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
      (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_) ?_) ?_
    · exact DedekindResidue.differentiable_completedDedekindZetaEntire K s
    · exact differentiableAt_Qd (by linarith)
    · exact DifferentiableAt.comp (g := fun w => (Hecke.dedekindPrefactor K w)⁻¹)
            (f := fun s : ℂ => 1 - s / 2) s (differentiable_prefactor_inv (K := K) _) (by fun_prop)
    · exact DifferentiableAt.comp (g := qsPhiH h) (f := fun s : ℂ => 1 - s / 2) s
        (differentiableAt_qsPhiH hh hne) (by fun_prop)
  Ψeq := by
    intro s h1 h2 hs0 hs1
    have hnint := not_nonpos_int_strip h1 h2 hs0
    have hnint2 := not_nonpos_int_half h1 h2 hs0
    have hG : Hecke.dedekindPrefactor K s ≠ 0 := prefactor_ne_zero hnint
    show (1 / 2 : ℂ) * DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
      (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2) = _
    rw [Qd_eq hs0 hnint hnint2, Z1, zetaE_eq hnint, caseBPhi, qsGammaRatio]
    field_simp
  Ψbd := by
    obtain ⟨CZ, hCZ0, hCZ⟩ := exists_Z1_poly (K := K)
    set r := InfinitePlace.nrComplexPlaces K
    set N := 2 * r + 1
    obtain ⟨CB, hCB0, hCB⟩ := caseBPhi_decay (K := K) hh (N + 2 * r + 1)
    refine strip_bounded_extend (F := fun s => (1 / 2 : ℂ) *
      DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
      (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2))
      (a := -1/2) (b := 3/2) (T := 2) (C := 2 * CZ * CB * 4 ^ (N + 2 * r + 1))
      (fun s h1 h2 => ?_) (fun s h1 h2 ht => ?_)
    · have hne : 1 - s / 2 ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hd : DifferentiableAt ℂ (fun s => (1 / 2 : ℂ) *
          DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
          (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2)) s := by
        refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
          (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_) ?_) ?_
        · exact DedekindResidue.differentiable_completedDedekindZetaEntire K s
        · exact differentiableAt_Qd (by linarith)
        · exact DifferentiableAt.comp (g := fun w => (Hecke.dedekindPrefactor K w)⁻¹)
            (f := fun s : ℂ => 1 - s / 2) s (differentiable_prefactor_inv (K := K) _) (by fun_prop)
        · exact DifferentiableAt.comp (g := qsPhiH h) (f := fun s : ℂ => 1 - s / 2) s
            (differentiableAt_qsPhiH hh hne) (by fun_prop)
      exact hd.continuousAt
    · have hs0 : s ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
      have hnint := not_nonpos_int_strip h1 h2 hs0
      have hnint2 := not_nonpos_int_half h1 h2 hs0
      have hG : Hecke.dedekindPrefactor K s ≠ 0 := prefactor_ne_zero hnint
      have heq : (1 / 2 : ℂ) * DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
          (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2) =
          s * Z1 K s * caseBPhi K h s := by
        rw [Qd_eq hs0 hnint hnint2, Z1, zetaE_eq hnint, caseBPhi, qsGammaRatio]
        field_simp
      show ‖(1 / 2 : ℂ) * DedekindResidue.completedDedekindZetaEntire K s * Qd K s *
          (Hecke.dedekindPrefactor K (1 - s / 2))⁻¹ * qsPhiH h (1 - s / 2)‖ ≤ _
      rw [heq, norm_mul, norm_mul]
      have ht1 : 1 ≤ |s.im| := by linarith
      have hns : ‖s‖ ≤ 2 * (1 + |s.im|) := by
        have := Complex.norm_le_abs_re_add_abs_im s
        have hre : |s.re| ≤ 3/2 := abs_le.mpr ⟨by linarith, h2⟩
        linarith
      have hz := hCZ s h1 h2
      have hb := hCB s h1 h2 ht
      have hpos1 : (0:ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
      calc ‖s‖ * ‖Z1 K s‖ * ‖caseBPhi K h s‖
          ≤ (2 * (1 + |s.im|)) * (CZ * (1 + |s.im|) ^ N) *
              (CB * (1 + |s.im|) ^ (2 * r) / (|s.im| / 2) ^ (N + 2 * r + 1)) := by
            gcongr
        _ = 2 * CZ * CB * ((1 + |s.im|) ^ (N + 2 * r + 1) / (|s.im| / 2) ^ (N + 2 * r + 1)) := by
            ring
        _ ≤ 2 * CZ * CB * 4 ^ (N + 2 * r + 1) :=
            mul_le_mul_of_nonneg_left (pow_div_aux' _ ht1) (by positivity)
  Dd := by
    intro u h1 h2
    have hne : (1 + u) / 2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith
    refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
      (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_) ?_) ?_
    · exact differentiableAt_prefactor (not_nonpos_int_of_re_pos (by linarith))
    · exact DifferentiableAt.comp (g := Qd K) (f := fun u : ℂ => 1 - u) u
        (differentiableAt_Qd (by simp; linarith)) (by fun_prop)
    · exact DifferentiableAt.comp (g := fun w => (Hecke.dedekindPrefactor K w)⁻¹)
            (f := fun u : ℂ => (1 + u) / 2) u (differentiable_prefactor_inv (K := K) _) (by fun_prop)
    · exact DifferentiableAt.comp (g := qsPhiH h) (f := fun u : ℂ => (1 + u) / 2) u
        (differentiableAt_qsPhiH hh hne) (by fun_prop)
  Deq := by
    intro u h1 h2 hu1
    have h1u : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    have hnint := not_nonpos_int_one_sub h1 h2 hu1
    have hnint2 : ∀ m : ℕ, (1 - u) / 2 ≠ -m :=
      not_nonpos_int_half (by simp; linarith) (by simp; linarith) h1u
    have hG : Hecke.dedekindPrefactor K (1 - u) ≠ 0 := prefactor_ne_zero hnint
    show (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * Qd K (1 - u) *
      (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * qsPhiH h ((1 + u) / 2) = _
    rw [Qd_eq h1u hnint hnint2, caseBPhi, qsGammaRatio, qsGammaRatio,
      show 1 - (1 - u) / 2 = (1 + u) / 2 by ring]
    field_simp
  Dbd := by
    obtain ⟨CR, hCR0, hCR⟩ := exists_ratio_poly (K := K)
    set r := InfinitePlace.nrComplexPlaces K
    obtain ⟨CB, hCB0, hCB⟩ := caseBPhi_decay (K := K) hh (4 * r + 2)
    refine strip_decay_extend (F := fun u => (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u *
      Qd K (1 - u) * (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * qsPhiH h ((1 + u) / 2))
      (a := 1/2) (b := 3/2) (T := 2) (C := CR * CB * 4 ^ (4 * r + 1)) (by norm_num)
      (fun u h1 h2 _ => ?_) (fun u h1 h2 ht => ?_)
    · have hne : (1 + u) / 2 ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hd : DifferentiableAt ℂ (fun u => (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u *
          Qd K (1 - u) * (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ *
          qsPhiH h ((1 + u) / 2)) u := by
        refine DifferentiableAt.mul (DifferentiableAt.mul (DifferentiableAt.mul
          (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_) ?_) ?_
        · exact differentiableAt_prefactor (not_nonpos_int_of_re_pos (by linarith))
        · exact DifferentiableAt.comp (g := Qd K) (f := fun u : ℂ => 1 - u) u
            (differentiableAt_Qd (by simp; linarith)) (by fun_prop)
        · exact DifferentiableAt.comp (g := fun w => (Hecke.dedekindPrefactor K w)⁻¹)
            (f := fun u : ℂ => (1 + u) / 2) u (differentiable_prefactor_inv (K := K) _) (by fun_prop)
        · exact DifferentiableAt.comp (g := qsPhiH h) (f := fun u : ℂ => (1 + u) / 2) u
            (differentiableAt_qsPhiH hh hne) (by fun_prop)
      exact hd.continuousAt
    · have hu1 : u ≠ 1 := by intro h; rw [h] at ht; simp at ht; linarith
      have h1u : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
      have hnint := not_nonpos_int_one_sub h1 h2 hu1
      have hnint2 : ∀ m : ℕ, (1 - u) / 2 ≠ -m :=
        not_nonpos_int_half (by simp; linarith) (by simp; linarith) h1u
      have hG : Hecke.dedekindPrefactor K (1 - u) ≠ 0 := prefactor_ne_zero hnint
      have heq : (1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * Qd K (1 - u) *
          (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * qsPhiH h ((1 + u) / 2) =
          qsGammaRatio K u * caseBPhi K h (1 - u) := by
        rw [Qd_eq h1u hnint hnint2, caseBPhi, qsGammaRatio, qsGammaRatio,
          show 1 - (1 - u) / 2 = (1 + u) / 2 by ring]
        field_simp
      show ‖(1 / 2 : ℂ) * Hecke.dedekindPrefactor K u * Qd K (1 - u) *
          (Hecke.dedekindPrefactor K ((1 + u) / 2))⁻¹ * qsPhiH h ((1 + u) / 2)‖ ≤ _
      rw [heq, norm_mul]
      have ht1 : 1 ≤ |u.im| := by linarith
      have hR := hCR u h1 h2
      have hb := hCB (1 - u) (by simp; linarith) (by simp; linarith) (by simpa using ht)
      rw [show (1 - u).im = -u.im by simp, abs_neg] at hb
      have hsq : u.im ^ 2 = |u.im| ^ 2 := (sq_abs _).symm
      calc ‖qsGammaRatio K u‖ * ‖caseBPhi K h (1 - u)‖
          ≤ (CR * (1 + |u.im|) ^ (2 * r)) *
              (CB * (1 + |u.im|) ^ (2 * r) / (|u.im| / 2) ^ (4 * r + 2)) := by
            gcongr
        _ = CR * CB * ((1 + |u.im|) ^ (4 * r) / (|u.im| / 2) ^ (4 * r + 2)) := by
            rw [show 4 * r = 2 * r + 2 * r by ring, pow_add]; ring
        _ ≤ CR * CB * (4 ^ (4 * r + 1) / |u.im| ^ 2) :=
            mul_le_mul_of_nonneg_left (pow_div_aux (4 * r) ht1) (mul_nonneg hCR0 hCB0)
        _ = CR * CB * 4 ^ (4 * r + 1) / u.im ^ 2 := by rw [hsq]; ring

end ArtinPrimitiveRoots.A2.QSP2
