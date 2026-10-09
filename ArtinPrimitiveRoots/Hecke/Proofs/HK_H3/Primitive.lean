import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_fe_export_to_ext_hecke_continuation
import ArtinPrimitiveRoots.Hecke.Proofs.«HK-ANALYTIC».GammaRatio
import Mathlib.Analysis.Complex.PhragmenLindelof

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Complex Filter Topology Asymptotics
open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.hk_misc_muse

open ArtinPrimitiveRoots.Hecke
open ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

private theorem ray_nonneg_re_not_neg_nat {z : ℂ} (hz : 0 < z.re) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n h
  have hre : z.re = -(n : ℝ) := by
    have hh := congrArg Complex.re h
    simpa using hh
  have hn : 0 ≤ (n : ℝ) := by positivity
  linarith

private theorem gammaC_ne_zero_of_re_between {z : ℂ} (hlo : -1 < z.re)
    (hhi : z.re < 0) : Complex.Gammaℂ z ≠ 0 := by
  have hΓ : Complex.Gamma z ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre : z.re = -(n : ℝ) := by
      have hh := congrArg Complex.re hn
      simpa using hh
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst n
      simp at hre
      linarith
    · have hnat : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      linarith
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpC : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpow : (2 * Real.pi : ℂ) ^ (-z) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  rw [Complex.Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero (by norm_num) hpow) hΓ

private def hkH3FEFactor [IsTotallyComplex K] (m : RayClassModulus K)
    (s W : ℂ) : ℂ :=
  W * (((((discr K).natAbs : ℝ) * (modulusNorm m : ℝ)) : ℂ) ^ ((1 - s) / 2) /
    ((((discr K).natAbs : ℝ) * (modulusNorm m : ℝ)) : ℂ) ^ (s / 2)) *
      (Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
        NumberField.InfinitePlace.nrComplexPlaces K

private theorem hk_primitive_fe_formula [IsTotallyComplex K]
    {m : RayClassModulus K} {ψ : RayClassGroup m →* ℂˣ}
    (hψ : ψ ≠ 1) (hp : HKPrimitive ψ)
    (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (t : ℝ) :
    ∃ W : ℂ, ‖W‖ = 1 ∧ hkEntireL ψ ((-δ : ℂ) + t * Complex.I) =
      hkH3FEFactor m ((-δ : ℂ) + t * Complex.I) W *
        hkEntireL (ψ⁻¹) (1 - ((-δ : ℂ) + t * Complex.I)) := by
  classical
  let s : ℂ := (-δ : ℂ) + t * Complex.I
  let q : ℝ := ((discr K).natAbs : ℝ) * modulusNorm m
  let qC : ℂ := (q : ℂ)
  have hsre : s.re = -δ := by simp [s]
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (by exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)))
      (by exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m)
  have hqC : qC = (q : ℂ) := rfl
  have hqCne : qC ≠ 0 := by rw [hqC]; exact_mod_cast hq.ne'
  have hbase : qC ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hqCne)
  have hGamma : Complex.Gammaℂ s ≠ 0 := by
    apply gammaC_ne_zero_of_re_between
    · rw [hsre]
      linarith
    · rw [hsre]
      linarith
  have hGammaPow : Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
    pow_ne_zero _ hGamma
  have hCoeff : qC ^ (s / 2) *
      Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 :=
    mul_ne_zero hbase hGammaPow
  have hsNoNeg : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n hn
    have hre : s.re = -(n : ℝ) := by
      have hh := congrArg Complex.re hn
      simpa using hh
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst n
      rw [hsre] at hre
      norm_num at hre
      have hn : -δ < 0 := neg_neg_of_pos hδ
      linarith
    · have hnat : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      rw [hsre] at hre
      linarith
  have hsInvNoNeg : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) :=
    ray_nonneg_re_not_neg_nat (by rw [Complex.sub_re, Complex.one_re, hsre]; linarith)
  obtain ⟨_, _, _, _, _, _, hCompVal, hCompInvVal, hRoot⟩ :=
    hk_fe_export_to_ext_hecke_continuation ψ hψ hp
  obtain ⟨W, hW, hFE⟩ := hRoot
  have hFEval := hFE s
  rw [hCompVal s hsNoNeg, hCompInvVal (1 - s) hsInvNoNeg] at hFEval
  rw [hkCompletedValue, hkCompletedValue] at hFEval
  change qC ^ (s / 2) * Complex.Gammaℂ s ^
      NumberField.InfinitePlace.nrComplexPlaces K * hkEntireL ψ s =
    W * (qC ^ ((1 - s) / 2) * Complex.Gammaℂ (1 - s) ^
      NumberField.InfinitePlace.nrComplexPlaces K * hkEntireL (ψ⁻¹) (1 - s)) at hFEval
  have hformula : hkEntireL ψ s =
      W * (qC ^ ((1 - s) / 2) / qC ^ (s / 2)) *
        (Complex.Gammaℂ (1 - s) / Complex.Gammaℂ s) ^
          NumberField.InfinitePlace.nrComplexPlaces K * hkEntireL (ψ⁻¹) (1 - s) := by
    calc
      hkEntireL ψ s = (qC ^ (s / 2) * Complex.Gammaℂ s ^
          NumberField.InfinitePlace.nrComplexPlaces K)⁻¹ *
          (qC ^ (s / 2) * Complex.Gammaℂ s ^
            NumberField.InfinitePlace.nrComplexPlaces K * hkEntireL ψ s) := by
          field_simp [hCoeff]
      _ = (qC ^ (s / 2) * Complex.Gammaℂ s ^
          NumberField.InfinitePlace.nrComplexPlaces K)⁻¹ *
          (W * (qC ^ ((1 - s) / 2) * Complex.Gammaℂ (1 - s) ^
            NumberField.InfinitePlace.nrComplexPlaces K * hkEntireL (ψ⁻¹) (1 - s))) := by
          rw [hFEval]
      _ = _ := by
          rw [div_pow]
          field_simp [hbase, hGamma]
  exact ⟨W, hW, by simpa [s, qC, q, hkH3FEFactor] using hformula⟩

theorem exists_hk_primitive_uniform_bound [IsTotallyComplex K]
    (δ : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : RayClassModulus K) (ψ : RayClassGroup m →* ℂˣ),
        HKPrimitive ψ → ψ ≠ 1 →
        Differentiable ℂ (hkEntireL ψ) ∧
        (∀ s : ℂ, 1 < s.re → hkEntireL ψ s = LSeriesRay ψ s) ∧
        ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 4 →
          ‖hkEntireL ψ s‖ ≤ C * (modulusNorm m : ℝ) ^ ((1 : ℝ) / 2 + δ) *
            (2 + |s.im|) ^ (Module.finrank ℚ K + 2 : ℕ) := by
  classical
  let d : ℕ := Module.finrank ℚ K
  let N : ℕ := d + 2
  let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
  let Q : ℝ := (discr K).natAbs
  let p : ℝ := (1 : ℝ) / 2 + δ
  let κ : ℝ := ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant δ
  let Zδ : ℝ := (riemannZeta (1 + δ : ℝ)).re ^ d
  let Z4 : ℝ := (riemannZeta (4 : ℝ)).re ^ d
  let Cleft : ℝ := Q ^ p * κ ^ r * Zδ
  let Cboundary : ℝ := 1 + Cleft * 3 ^ N + Z4
  let C : ℝ := Cboundary * 4 ^ N
  have hp : 0 < p := by dsimp [p]; linarith
  have hp0 : 0 ≤ p := hp.le
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  have hκ : 0 < κ := by
    dsimp [κ]
    exact ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaCLeftConstant_pos δ hδ hδ4
  have hZδ : 0 < Zδ := by
    dsimp [Zδ]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by linarith)) _
  have hZ4 : 0 < Z4 := by
    dsimp [Z4]
    exact pow_pos (riemannZeta_re_pos_of_one_lt (by norm_num)) _
  have hCleft : 0 < Cleft := by dsimp [Cleft]; positivity
  have hCboundary : 0 < Cboundary := by dsimp [Cboundary]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hplaces : 2 * r = d := by
    have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h
    exact h
  have hZetaδ : ‖dedekindZeta K ((1 + δ : ℝ) : ℂ)‖ ≤ Zδ := by
    have h := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
      (by linarith : (1 : ℝ) < 1 + δ) 0).2
    simpa [Zδ, d] using h
  have hZeta4 : ‖dedekindZeta K (4 : ℂ)‖ ≤ Z4 := by
    have h := (ArtinPrimitiveRoots.Hecke.dedekindZeta_norm_bounds K
      (by norm_num : (1 : ℝ) < 4) 0).2
    simpa [Z4, d] using h
  refine ⟨C, hC, ?_⟩
  intro m ψ hpψ hψ
  obtain ⟨hLdiff, hLInvdiff, hLright, hLInvright, _, _, _, _, _⟩ :=
    hk_fe_export_to_ext_hecke_continuation ψ hψ hpψ
  refine ⟨hLdiff, hLright, ?_⟩
  intro s hs0 hs4
  let a : ℝ := -δ
  let b : ℝ := 4
  let H : ℂ → ℂ := fun z => hkEntireL ψ z / (z + 2) ^ N
  let S : Set ℂ := Complex.re ⁻¹' Set.Ioo a b
  have hab : a ≤ b := by dsimp [a, b]; linarith
  obtain ⟨Cpre, Bpre, hCpre, hBpre, hPrelim⟩ :=
    hk_entire_L_preliminary_growth ψ hψ hpψ a b hab
  have hClosed : IsClosed (Complex.re ⁻¹' Set.Icc a b) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hClosure : closure S ⊆ Complex.re ⁻¹' Set.Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    · exact hClosed
  have hDenOne {z : ℂ} (hz : a ≤ z.re) : 1 ≤ ‖z + 2‖ := by
    have hre : 1 ≤ (z + 2).re := by
      rw [show (z + 2).re = z.re + 2 by simp]
      dsimp [a] at hz
      linarith [hδ4]
    exact (hre.trans (le_abs_self _)).trans (Complex.abs_re_le_norm _)
  have hDenNe {z : ℂ} (hz : z ∈ closure S) : (z + 2) ^ N ≠ 0 := by
    have hzIcc := hClosure hz
    have hnorm : 1 ≤ ‖z + 2‖ := hDenOne hzIcc.1
    have hbase : z + 2 ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      norm_num at hnorm
    exact pow_ne_zero _ hbase
  have hDenDiff : DifferentiableOn ℂ (fun z : ℂ => (z + 2) ^ N) (closure S) := by
    fun_prop
  have hHdiff : DifferentiableOn ℂ H (closure S) := by
    dsimp [H]
    exact hLdiff.differentiableOn.div hDenDiff (fun z hz => hDenNe hz)
  have hfd : DiffContOnCl ℂ H S :=
    ⟨hHdiff.mono subset_closure, hHdiff.continuousOn⟩
  have hSevent : ∀ᶠ z : ℂ in
      Filter.comap (fun z : ℂ => |z.im|) atTop ⊓ Filter.principal S, z ∈ S := by
    have hself : ∀ᶠ z : ℂ in Filter.principal S, z ∈ S := by simp
    exact hself.filter_mono inf_le_right
  let Bdouble : ℝ := Cpre + 4 * Bpre
  have hBdouble : 0 < Bdouble := by dsimp [Bdouble]; positivity
  have hBigO : ∃ c < Real.pi / (b - a), ∃ B : ℝ,
      H =O[Filter.comap (fun z : ℂ => |z.im|) atTop ⊓ Filter.principal S]
        fun z => Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1 / 4, ?_, Bdouble, ?_⟩
    · have hwidth : 0 < b - a := by dsimp [a, b]; linarith
      have hsmall : (1 / 4 : ℝ) * (b - a) < Real.pi := by
        dsimp [a, b]
        nlinarith [hδ4, Real.pi_gt_three]
      exact (lt_div_iff₀ hwidth).2 hsmall
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hSevent] with z hzS
    have hzlo : a ≤ z.re := le_of_lt hzS.1
    have hzhi : z.re ≤ b := le_of_lt hzS.2
    have hLz := hPrelim z hzlo hzhi
    have hDenPow : 1 ≤ ‖(z + 2) ^ N‖ := by
      rw [norm_pow]
      exact one_le_pow₀ (hDenOne hzlo)
    have hHleL : ‖H z‖ ≤ ‖hkEntireL ψ z‖ := by
      dsimp [H]
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hDenPow
    let T : ℝ := |z.im|
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hExpT : 1 + T ≤ 4 * Real.exp (T / 4) := by
      have h := Real.add_one_le_exp (T / 4)
      dsimp [T] at h ⊢
      nlinarith [abs_nonneg z.im]
    have hExpOne : 1 ≤ Real.exp (T / 4) := by
      calc
        1 = Real.exp 0 := by simp
        _ ≤ Real.exp (T / 4) := Real.exp_le_exp.mpr (by linarith)
    have hCoef : Cpre + Bpre * (1 + T) ≤ Bdouble * Real.exp (T / 4) := by
      dsimp [Bdouble]
      calc
        Cpre + Bpre * (1 + T) ≤ Cpre * Real.exp (T / 4) +
            Bpre * (4 * Real.exp (T / 4)) := by
          exact add_le_add
            (by simpa using mul_le_mul_of_nonneg_left hExpOne hCpre.le)
            (mul_le_mul_of_nonneg_left hExpT hBpre.le)
        _ = (Cpre + 4 * Bpre) * Real.exp (T / 4) := by ring
    have hCpreExp : Cpre ≤ Real.exp Cpre := by
      have h := Real.add_one_le_exp Cpre
      linarith
    have hExpBound : Cpre * Real.exp (Bpre * (1 + T)) ≤
        Real.exp (Bdouble * Real.exp (T / 4)) := by
      calc
        Cpre * Real.exp (Bpre * (1 + T)) ≤
            Real.exp Cpre * Real.exp (Bpre * (1 + T)) :=
          mul_le_mul_of_nonneg_right hCpreExp (Real.exp_nonneg _)
        _ = Real.exp (Cpre + Bpre * (1 + T)) := by rw [← Real.exp_add]
        _ ≤ Real.exp (Bdouble * Real.exp (T / 4)) :=
          Real.exp_le_exp.mpr hCoef
    calc
      ‖H z‖ ≤ ‖hkEntireL ψ z‖ := hHleL
      _ ≤ Cpre * Real.exp (Bpre * (1 + |z.im|)) := hLz
      _ ≤ Real.exp (Bdouble * Real.exp ((1 / 4 : ℝ) * |z.im|)) := by
        simpa [T, div_eq_mul_inv, mul_comm] using hExpBound
      _ = 1 * ‖Real.exp (Bdouble * Real.exp ((1 / 4 : ℝ) * |z.im|))‖ := by
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hδBase : 0 < (modulusNorm m : ℝ) := by
    exact_mod_cast ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
  have hδBaseOne : 1 ≤ (modulusNorm m : ℝ) := by
    have hnat : 1 ≤ modulusNorm m := Nat.one_le_iff_ne_zero.mpr (by
      exact (Nat.ne_of_gt (ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m)))
    exact_mod_cast hnat
  have hqpowOne : 1 ≤ (modulusNorm m : ℝ) ^ p := Real.one_le_rpow hδBaseOne hp0
  have hleftCoefficient : Cleft * 3 ^ N ≤ Cboundary := by
    dsimp [Cboundary]
    have hnonneg : 0 ≤ 1 + Z4 := by positivity
    nlinarith [hnonneg]
  have hrightCoefficient : Z4 ≤ Cboundary := by
    dsimp [Cboundary]
    nlinarith [le_of_lt hCleft, (pow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) N),
      pow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) N]
  have hBoundaryLeft : ∀ z : ℂ, z.re = a →
      ‖H z‖ ≤ Cboundary * (modulusNorm m : ℝ) ^ p := by
    intro z hzre
    have hrepr : z = (-δ : ℂ) + z.im * Complex.I := by
      apply Complex.ext <;> simp [hzre] <;> ring
    obtain ⟨W, hW, hFEz⟩ := hk_primitive_fe_formula hψ hpψ δ hδ hδ4 z.im
    have hFEz' : hkEntireL ψ z = hkH3FEFactor m z W *
        hkEntireL (ψ⁻¹) (1 - z) := by
      calc
        hkEntireL ψ z = hkEntireL ψ ((-δ : ℂ) + z.im * Complex.I) :=
          congrArg (fun w : ℂ => hkEntireL ψ w) hrepr
        _ = hkH3FEFactor m ((-δ : ℂ) + z.im * Complex.I) W *
              hkEntireL (ψ⁻¹) (1 - ((-δ : ℂ) + z.im * Complex.I)) := hFEz
        _ = hkH3FEFactor m z W * hkEntireL (ψ⁻¹) (1 - z) :=
          congrArg (fun w : ℂ => hkH3FEFactor m w W * hkEntireL (ψ⁻¹) (1 - w))
            hrepr.symm
    have hzInv : 1 < (1 - z).re := by rw [Complex.sub_re, Complex.one_re, hzre]; dsimp [a]; linarith
    have hInvAgree := hLInvright (1 - z) hzInv
    have hInvRay : ‖LSeriesRay (ψ⁻¹) (1 - z)‖ ≤ Zδ := by
      have hRay := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le (η := ψ⁻¹) hzInv).1
      have hReZ : (dedekindZeta K (1 + δ : ℝ)).re ≤
          ‖dedekindZeta K ((1 + δ : ℝ) : ℂ)‖ := by
        exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
      calc
        ‖LSeriesRay (ψ⁻¹) (1 - z)‖ ≤ (dedekindZeta K (1 - z).re).re := hRay
        _ = (dedekindZeta K (1 + δ : ℝ)).re := by
          congr 2
          rw [Complex.sub_re, Complex.one_re, hzre]
          dsimp [a]
          ring
        _ ≤ ‖dedekindZeta K ((1 + δ : ℝ) : ℂ)‖ := hReZ
        _ ≤ Zδ := hZetaδ
    have hInvBound : ‖hkEntireL (ψ⁻¹) (1 - z)‖ ≤ Zδ := by
      rw [hInvAgree]
      exact hInvRay
    let q : ℝ := modulusNorm m
    let base : ℝ := Q * q
    let baseC : ℂ := (base : ℂ)
    have hq : 0 < q := by dsimp [q]; exact_mod_cast
      ArtinPrimitiveRoots.Dictionary.HKDICTRay.modulusNorm_pos m
    have hbase : 0 < base := by dsimp [base]; exact mul_pos hQ hq
    have hbaseNorm : ‖baseC ^ ((1 - z) / 2) / baseC ^ (z / 2)‖ =
        base ^ p := by
      have hnormPow (w : ℂ) : ‖baseC ^ w‖ = base ^ w.re := by
        rw [show baseC = (base : ℂ) by rfl]
        exact Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hbase) w
      rw [norm_div, hnormPow, hnormPow]
      have hnum : ((1 - z) / 2).re = (1 + δ) / 2 := by
        rw [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re, hzre]
        simp [a]
      have hden : (z / 2).re = -δ / 2 := by
        rw [Complex.div_ofNat_re, hzre]
      rw [hnum, hden, ← Real.rpow_sub hbase]
      congr 1
      dsimp [p]
      ring
    have hGammaRatio :=
      ArtinPrimitiveRoots.Proofs.HK_ANALYTIC.gammaC_left_ratio_bound δ z.im hδ hδ4
    have hGammaPow : ‖(Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z) ^ r‖ ≤
        κ ^ r * (2 + |z.im|) ^ d := by
      have hratio : ‖Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z‖ ≤
          κ * (2 + |z.im|) ^ 2 := by
        have heq := congrArg (fun w : ℂ =>
          ‖Complex.Gammaℂ (1 - w) / Complex.Gammaℂ w‖) hrepr
        calc
          ‖Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z‖ =
              ‖Complex.Gammaℂ (1 - ((-δ : ℂ) + z.im * Complex.I)) /
                Complex.Gammaℂ ((-δ : ℂ) + z.im * Complex.I)‖ := heq
          _ ≤ κ * (2 + |z.im|) ^ 2 := by simpa [κ] using hGammaRatio
      calc
        ‖(Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z) ^ r‖ =
            ‖Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z‖ ^ r := norm_pow _ _
        _ ≤ (κ * (2 + |z.im|) ^ 2) ^ r :=
          pow_le_pow_left₀ (norm_nonneg _) hratio _
        _ = κ ^ r * (2 + |z.im|) ^ (2 * r) := by rw [mul_pow, pow_mul]
        _ = κ ^ r * (2 + |z.im|) ^ d := by rw [hplaces]
    have hRatProd :
        ‖baseC ^ ((1 - z) / 2) / baseC ^ (z / 2)‖ *
          ‖(Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z) ^ r‖ ≤
          base ^ p * (κ ^ r * (2 + |z.im|) ^ d) := by
      rw [hbaseNorm]
      exact mul_le_mul_of_nonneg_left hGammaPow (Real.rpow_nonneg hbase.le _)
    have hFactorNorm : ‖hkH3FEFactor m z W‖ =
        ‖W‖ * (‖baseC ^ ((1 - z) / 2) / baseC ^ (z / 2)‖ *
          ‖(Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z) ^ r‖) := by
      have hbaseCeq :
          (((((discr K).natAbs : ℝ) * (modulusNorm m : ℝ)) : ℂ)) = baseC := by
        simp [baseC, base, Q, q]
      have hr_eq : r = NumberField.InfinitePlace.nrComplexPlaces K := rfl
      dsimp only [hkH3FEFactor]
      rw [norm_mul, norm_mul, norm_div, ← norm_div, hbaseCeq, ← hr_eq]
      exact mul_assoc _ _ _
    have hLeftRaw : ‖hkEntireL ψ z‖ ≤ Cleft * q ^ p * (2 + |z.im|) ^ d := by
      calc
        ‖hkEntireL ψ z‖ = ‖W‖ *
            (‖baseC ^ ((1 - z) / 2) / baseC ^ (z / 2)‖ *
              ‖(Complex.Gammaℂ (1 - z) / Complex.Gammaℂ z) ^ r‖) *
            ‖hkEntireL (ψ⁻¹) (1 - z)‖ := by
          rw [hFEz', norm_mul, hFactorNorm]
        _ ≤ 1 * (base ^ p * (κ ^ r * (2 + |z.im|) ^ d)) * Zδ := by
          have hmul := mul_le_mul hRatProd hInvBound (norm_nonneg _) (by positivity)
          rw [hW]
          simpa using hmul
        _ = Cleft * q ^ p * (2 + |z.im|) ^ d := by
          dsimp [Cleft, base, q]
          rw [Real.mul_rpow hQ.le hq.le]
          ring
    have hheight : 1 ≤ 2 + |z.im| := by have h := abs_nonneg z.im; linarith
    have hleftN : ‖hkEntireL ψ z‖ ≤ Cleft * q ^ p * (2 + |z.im|) ^ N := by
      calc
        ‖hkEntireL ψ z‖ ≤ Cleft * q ^ p * (2 + |z.im|) ^ d := hLeftRaw
        _ ≤ Cleft * q ^ p * (2 + |z.im|) ^ N := by
          apply mul_le_mul_of_nonneg_left
          · apply pow_le_pow_right₀ hheight
            dsimp [N, d]
            omega
          · positivity
    have hDenCompare : 2 + |z.im| ≤ 3 * ‖z + 2‖ := by
      have hden1 := hDenOne (z := z) hzre.ge
      have him : |z.im| ≤ ‖z + 2‖ := by
        simpa using (Complex.abs_im_le_norm (z + 2))
      nlinarith
    have hDenPow : (2 + |z.im|) ^ N ≤ 3 ^ N * ‖(z + 2) ^ N‖ := by
      calc
        (2 + |z.im|) ^ N ≤ (3 * ‖z + 2‖) ^ N :=
          pow_le_pow_left₀ (by positivity) hDenCompare _
        _ = 3 ^ N * ‖(z + 2) ^ N‖ := by rw [mul_pow, norm_pow]
    have hDenNpos : 0 < ‖(z + 2) ^ N‖ := by
      rw [norm_pow]
      exact pow_pos (lt_of_lt_of_le zero_lt_one (hDenOne (z := z) hzre.ge)) _
    have hNormNumerator : ‖hkEntireL ψ z‖ ≤
        (Cleft * 3 ^ N * q ^ p) * ‖(z + 2) ^ N‖ := by
      calc
        ‖hkEntireL ψ z‖ ≤ Cleft * q ^ p * (2 + |z.im|) ^ N := hleftN
        _ ≤ Cleft * q ^ p * (3 ^ N * ‖(z + 2) ^ N‖) := by
          exact mul_le_mul_of_nonneg_left hDenPow (by positivity)
        _ = (Cleft * 3 ^ N * q ^ p) * ‖(z + 2) ^ N‖ := by ring
    have hNormH : ‖H z‖ ≤ Cboundary * q ^ p := by
      dsimp [H]
      rw [norm_div]
      apply (div_le_iff₀ hDenNpos).2
      calc
        ‖hkEntireL ψ z‖ ≤ (Cleft * 3 ^ N * q ^ p) * ‖(z + 2) ^ N‖ := hNormNumerator
        _ ≤ (Cboundary * q ^ p) * ‖(z + 2) ^ N‖ := by
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [hleftCoefficient]) (norm_nonneg _)
    have hqeq : q = (modulusNorm m : ℝ) := rfl
    simpa [a, q, hqeq] using hNormH
  have hBoundaryRight : ∀ z : ℂ, z.re = b →
      ‖H z‖ ≤ Cboundary * (modulusNorm m : ℝ) ^ p := by
    intro z hzre
    have hz1 : 1 < z.re := by rw [hzre]; norm_num [b]
    have hLz : hkEntireL ψ z = LSeriesRay ψ z := hLright z hz1
    have hRay := (ArtinPrimitiveRoots.Hecke.norm_LSeriesRay_le (η := ψ) hz1).1
    have hReZ : (dedekindZeta K (4 : ℝ)).re ≤
        ‖dedekindZeta K (4 : ℂ)‖ := by
      exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hRight : ‖hkEntireL ψ z‖ ≤ Z4 := by
      rw [hLz]
      calc
        ‖LSeriesRay ψ z‖ ≤ (dedekindZeta K z.re).re := hRay
        _ = (dedekindZeta K (4 : ℝ)).re := by rw [hzre]
        _ ≤ ‖dedekindZeta K (4 : ℂ)‖ := hReZ
        _ ≤ Z4 := hZeta4
    have hzlo : a ≤ z.re := by rw [hzre]; dsimp [a]; linarith
    have hden : 1 ≤ ‖(z + 2) ^ N‖ := by
      rw [norm_pow]
      exact one_le_pow₀ (hDenOne hzlo)
    have hHbound : ‖H z‖ ≤ Z4 := by
      dsimp [H]
      rw [norm_div]
      exact (div_le_self (norm_nonneg _) hden).trans hRight
    have hqpow : 1 ≤ (modulusNorm m : ℝ) ^ p := hqpowOne
    calc
      ‖H z‖ ≤ Z4 := hHbound
      _ ≤ Cboundary := hrightCoefficient
      _ ≤ Cboundary * (modulusNorm m : ℝ) ^ p :=
        le_mul_of_one_le_right hCboundary.le hqpow
  have hPL (z : ℂ) (hzlo : a ≤ z.re) (hzhi : z.re ≤ b) :
      ‖H z‖ ≤ Cboundary * (modulusNorm m : ℝ) ^ p :=
    PhragmenLindelof.vertical_strip hfd hBigO hBoundaryLeft hBoundaryRight hzlo hzhi
  have hPLs := hPL s (by dsimp [a]; linarith [hs0]) (by dsimp [b]; exact hs4)
  have hsBound : ‖s + 2‖ ≤ 4 * (2 + |s.im|) := by
    have hRe : |s.re + 2| ≤ 6 := by
      rw [abs_le]
      constructor <;> linarith [hs0, hs4]
    calc
      ‖s + 2‖ ≤ |(s + 2).re| + |(s + 2).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re + 2| + |s.im| := by simp
      _ ≤ 6 + |s.im| := add_le_add hRe le_rfl
      _ ≤ 4 * (2 + |s.im|) := by nlinarith [abs_nonneg s.im]
  have hsplus : s + 2 ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    have hre' : s.re + 2 = 0 := by simpa using hre
    linarith [hs0]
  have hEq : hkEntireL ψ s = H s * (s + 2) ^ N := by
    dsimp [H]
    field_simp [hsplus]
  have hqpow : 0 ≤ (modulusNorm m : ℝ) ^ p := by positivity
  calc
    ‖hkEntireL ψ s‖ = ‖H s‖ * ‖(s + 2) ^ N‖ := by rw [hEq, norm_mul, norm_pow]
    _ ≤ (Cboundary * (modulusNorm m : ℝ) ^ p) *
        (4 * (2 + |s.im|)) ^ N :=
      mul_le_mul hPLs (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hsBound _)
        (by positivity) (by positivity)
    _ = C * (modulusNorm m : ℝ) ^ p * (2 + |s.im|) ^ N := by
      dsimp [C]
      rw [mul_pow]
      ring
    _ = C * (modulusNorm m : ℝ) ^ ((1 : ℝ) / 2 + δ) *
        (2 + |s.im|) ^ (Module.finrank ℚ K + 2 : ℕ) := by
      simp [p, N, d]

end ArtinPrimitiveRoots.Proofs.hk_misc_muse
