import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_mellin_FE_completed
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_completed_gamma_product
import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».hk_entire_L_agreement
import Mathlib.Algebra.Order.BigOperators.Group.Finset


set_option autoImplicit false
open NumberField NumberField.InfinitePlace ClassFieldTheory DedekindResidue MeasureTheory Filter Asymptotics
open ArtinPrimitiveRoots.Hecke.Theta
open scoped NumberField NNReal
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

private theorem norm_complexGamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  calc
    ‖Complex.Gamma z‖ =
        ‖∫ x in Set.Ioi (0 : ℝ), (↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ := by
      rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral]
    _ ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖(↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ := norm_integral_le_integral_norm _
    _ = ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change ‖(↑(-x).exp : ℂ) * (↑x : ℂ) ^ (z - 1)‖ =
        Real.exp (-x) * x ^ (z.re - 1)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    _ = Real.Gamma z.re := (Real.Gamma_eq_integral hz).symm

private theorem complexGamma_add_nat {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    Complex.Gamma (z + (n : ℂ)) =
      (∏ k ∈ Finset.range n, (z + (k : ℂ))) * Complex.Gamma z := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hne : z + (n : ℂ) ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        have hz0 : z.im = 0 := by simpa using him
        exact hz hz0
      rw [show z + (n.succ : ℂ) = (z + (n : ℂ)) + 1 by push_cast; ring,
        Complex.Gamma_add_one _ hne, ih, Finset.prod_range_succ]
      ring

private theorem norm_sin_pi_mul_le (z : ℂ) :
    ‖Complex.sin (Real.pi * z)‖ ≤ Real.exp (Real.pi * |z.im|) := by
  change ‖(Complex.exp (-(Real.pi * z) * Complex.I) -
    Complex.exp ((Real.pi * z) * Complex.I)) * Complex.I / 2‖ ≤ _
  have h1 : ‖Complex.exp (-(Real.pi * z) * Complex.I)‖ =
      Real.exp (Real.pi * z.im) := by
    rw [Complex.norm_exp]
    have hre : (-(Real.pi * z) * Complex.I).re = Real.pi * z.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
  have h2 : ‖Complex.exp ((Real.pi * z) * Complex.I)‖ =
      Real.exp (-(Real.pi * z.im)) := by
    rw [Complex.norm_exp]
    have hre : ((Real.pi * z) * Complex.I).re = -(Real.pi * z.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
  have hfactor :
      ‖(Complex.exp (-(Real.pi * z) * Complex.I) -
        Complex.exp ((Real.pi * z) * Complex.I)) * Complex.I / 2‖ =
        ‖Complex.exp (-(Real.pi * z) * Complex.I) -
          Complex.exp ((Real.pi * z) * Complex.I)‖ / 2 := by
    simp [norm_div, norm_mul, Complex.norm_I]
  rw [hfactor]
  have hsum : Real.exp (Real.pi * z.im) + Real.exp (-(Real.pi * z.im)) ≤
      2 * Real.exp (Real.pi * |z.im|) := by
    have hleft := Real.exp_le_exp.mpr (le_abs_self (Real.pi * z.im))
    have hright := Real.exp_le_exp.mpr (neg_le_abs (Real.pi * z.im))
    have habs : |Real.pi * z.im| = Real.pi * |z.im| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [habs] at hleft hright
    nlinarith
  calc
    ‖Complex.exp (-(Real.pi * z) * Complex.I) -
        Complex.exp ((Real.pi * z) * Complex.I)‖ / 2 ≤
      (‖Complex.exp (-(Real.pi * z) * Complex.I)‖ +
        ‖Complex.exp ((Real.pi * z) * Complex.I)‖) / 2 := by
          exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = (Real.exp (Real.pi * z.im) + Real.exp (-(Real.pi * z.im))) / 2 := by
      rw [h1, h2]
    _ ≤ Real.exp (Real.pi * |z.im|) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hsum]

private theorem exists_gamma_inv_strip_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (B * (1 + |s.im|)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt b
  let lo : ℝ := (N : ℝ) + 1 - b
  let hi : ℝ := (N : ℝ) + 1 - a
  have hlo : 1 < lo := by dsimp [lo]; linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hGpos : 0 < Real.Gamma (hi + 1) := by
    apply Real.Gamma_pos_of_pos
    dsimp [hi]
    linarith
  let box : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (-1) 1
  let finv : ℝ × ℝ → ℝ := fun p =>
    ‖(Complex.Gamma ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))⁻¹‖
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hinput : Continuous (fun p : ℝ × ℝ =>
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hinv : Continuous (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hfinv : Continuous finv := by
    dsimp [finv]
    exact continuous_norm.comp (hinv.comp hinput)
  have himage : IsCompact (finv '' box) := hbox.image hfinv
  obtain ⟨Csmall, hCsmall⟩ := himage.bddAbove
  let C : ℝ := max 1 (max Csmall (Real.Gamma (hi + 1) / Real.pi))
  refine ⟨C, Real.pi, ?_, Real.pi_pos, ?_⟩
  · dsimp [C]
    positivity
  intro s hsa hsb
  by_cases him : 1 ≤ |s.im|
  · have him0 : s.im ≠ 0 := by
      intro hz
      rw [hz] at him
      norm_num at him
    have hΓs : Complex.Gamma s ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hs0 : s.im = 0 := by
        have heq := congrArg Complex.im hn
        simpa using heq
      exact him0 hs0
    have hΓone : Complex.Gamma (1 - s) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n hn
      have hs0 : s.im = 0 := by
        have heq := congrArg Complex.im hn
        simp at heq
        linarith
      exact him0 hs0
    have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
      apply Complex.sin_ne_zero_iff.mpr
      intro k hk
      have heq : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (k : ℂ) := by
        simpa [mul_comm] using hk
      have hsEq : s = (k : ℂ) := mul_left_cancel₀
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) heq
      have hs0 : s.im = 0 := by rw [hsEq]; simp
      exact him0 hs0
    have hreflect : (Complex.Gamma s)⁻¹ =
        Complex.Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
      calc
        (Complex.Gamma s)⁻¹ =
            (Complex.Gamma s * Complex.Gamma (1 - s))⁻¹ * Complex.Gamma (1 - s) := by
          field_simp [hΓs, hΓone]
        _ = (Real.pi / Complex.sin (Real.pi * s))⁻¹ * Complex.Gamma (1 - s) := by
          rw [Complex.Gamma_mul_Gamma_one_sub]
        _ = Complex.Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
          field_simp [hsin, Real.pi_ne_zero]
    have hz : (1 - s).im ≠ 0 := by
      intro h0
      have hs0 : s.im = 0 := by simpa using h0
      exact him0 hs0
    have hshift : Complex.Gamma ((1 - s) + (N : ℂ)) =
        (∏ k ∈ Finset.range N, ((1 - s) + (k : ℂ))) * Complex.Gamma (1 - s) :=
      complexGamma_add_nat hz N
    have hprod : 1 ≤ ‖∏ k ∈ Finset.range N, ((1 - s) + (k : ℂ))‖ := by
      rw [norm_prod]
      have hprodAux : ∀ n : ℕ,
          (1 : ℝ) ≤ ∏ k ∈ Finset.range n, ‖(1 - s) + (k : ℂ)‖ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.prod_range_succ]
          have hImNorm := Complex.abs_im_le_norm ((1 - s) + (n : ℂ))
          have hImEq : ((1 - s) + (n : ℂ)).im = (1 - s).im := by simp
          rw [hImEq] at hImNorm
          have hImGe : 1 ≤ |(1 - s).im| := by simpa using him
          have hlast : 1 ≤ ‖(1 - s) + (n : ℂ)‖ := hImGe.trans hImNorm
          have hprev : 0 ≤ ∏ k ∈ Finset.range n, ‖(1 - s) + (k : ℂ)‖ := by positivity
          calc
            1 = 1 * 1 := by norm_num
            _ ≤ (∏ k ∈ Finset.range n, ‖(1 - s) + (k : ℂ)‖) *
                ‖(1 - s) + (n : ℂ)‖ := by
                  exact mul_le_mul ih hlast (by norm_num) hprev
      exact hprodAux N
    have hshiftNorm : ‖Complex.Gamma (1 - s)‖ ≤
        ‖Complex.Gamma ((1 - s) + (N : ℂ))‖ := by
      calc
        ‖Complex.Gamma (1 - s)‖ = 1 * ‖Complex.Gamma (1 - s)‖ := by simp
        _ ≤ ‖∏ k ∈ Finset.range N, ((1 - s) + (k : ℂ))‖ *
              ‖Complex.Gamma (1 - s)‖ :=
            mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ = ‖Complex.Gamma ((1 - s) + (N : ℂ))‖ := by rw [hshift, norm_mul]
    have hshiftRe : ((1 - s) + (N : ℂ)).re = (N : ℝ) + 1 - s.re := by
      simp
      ring
    have hrealGamma : Real.Gamma (((1 - s) + (N : ℂ)).re) ≤ Real.Gamma (hi + 1) := by
      have hxlo : lo ≤ ((1 - s) + (N : ℂ)).re := by rw [hshiftRe]; dsimp [lo]; linarith
      have hxhi : ((1 - s) + (N : ℂ)).re ≤ hi := by rw [hshiftRe]; dsimp [hi]; linarith
      have hxpos : 0 < ((1 - s) + (N : ℂ)).re := by linarith [hlo, hxlo]
      have hstep : Real.Gamma (((1 - s) + (N : ℂ)).re) ≤
          Real.Gamma (((1 - s) + (N : ℂ)).re + 1) := by
        rw [Real.Gamma_add_one hxpos.ne']
        nlinarith [Real.Gamma_pos_of_pos hxpos]
      have hmono : Real.Gamma (((1 - s) + (N : ℂ)).re + 1) ≤
          Real.Gamma (hi + 1) := by
        have hleft : 2 ≤ ((1 - s) + (N : ℂ)).re + 1 := by
          rw [hshiftRe]
          have hsN : s.re < (N : ℝ) := lt_of_le_of_lt hsb hN
          linarith
        have hright : 2 ≤ hi + 1 := by
          dsimp [hi]
          have haN : a < (N : ℝ) := lt_of_le_of_lt hab hN
          linarith
        have hle : ((1 - s) + (N : ℂ)).re + 1 ≤ hi + 1 := by
          simpa [add_comm] using add_le_add_right hxhi 1
        exact Real.Gamma_strictMonoOn_Ici.monotoneOn hleft hright hle
      exact hstep.trans hmono
    have hGamma1Bound : ‖Complex.Gamma (1 - s)‖ ≤ Real.Gamma (hi + 1) := by
      calc
        ‖Complex.Gamma (1 - s)‖ ≤ ‖Complex.Gamma ((1 - s) + (N : ℂ))‖ := hshiftNorm
        _ ≤ Real.Gamma (((1 - s) + (N : ℂ)).re) :=
          norm_complexGamma_le_realGamma (by rw [hshiftRe]; linarith [hN, hsb])
        _ ≤ Real.Gamma (hi + 1) := hrealGamma
    have hsinBound := norm_sin_pi_mul_le s
    have hhigh : ‖(Complex.Gamma s)⁻¹‖ ≤
        (Real.Gamma (hi + 1) / Real.pi) * Real.exp (Real.pi * |s.im|) := by
      rw [hreflect, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      calc
        ‖Complex.Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / Real.pi ≤
          Real.Gamma (hi + 1) * Real.exp (Real.pi * |s.im|) / Real.pi := by
            gcongr
        _ = (Real.Gamma (hi + 1) / Real.pi) * Real.exp (Real.pi * |s.im|) := by ring
    calc
      ‖(Complex.Gamma s)⁻¹‖ ≤
          (Real.Gamma (hi + 1) / Real.pi) * Real.exp (Real.pi * |s.im|) := hhigh
      _ ≤ C * Real.exp (Real.pi * (1 + |s.im|)) := by
        have he : Real.exp (Real.pi * |s.im|) ≤ Real.exp (Real.pi * (1 + |s.im|)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos]
        have hc : Real.Gamma (hi + 1) / Real.pi ≤ C := by
          dsimp [C]
          exact le_max_of_le_right (le_max_right _ _)
        exact mul_le_mul hc he (Real.exp_nonneg _) (by positivity)
  · have himle : |s.im| ≤ 1 := le_of_not_ge him
    have hp : (s.re, s.im) ∈ box := by
      exact ⟨⟨hsa, hsb⟩, abs_le.mp himle⟩
    have hsmall := hCsmall ⟨(s.re, s.im), hp, rfl⟩
    have hsrepr : (s.re : ℂ) + (s.im : ℂ) * Complex.I = s := Complex.re_add_im s
    have hsmall' : ‖(Complex.Gamma s)⁻¹‖ ≤ Csmall := by
      simpa [finv, hsrepr] using hsmall
    calc
      ‖(Complex.Gamma s)⁻¹‖ ≤ Csmall := hsmall'
      _ ≤ C * Real.exp (Real.pi * (1 + |s.im|)) := by
        have hCsmall' : Csmall ≤ C := by
          dsimp [C]
          exact (le_max_left Csmall _).trans (le_max_right 1 _)
        have he : 1 ≤ Real.exp (Real.pi * (1 + |s.im|)) := by
          calc
            1 = Real.exp 0 := by simp
            _ ≤ Real.exp (Real.pi * (1 + |s.im|)) :=
              Real.exp_le_exp.mpr (by positivity)
        exact hCsmall'.trans (le_mul_of_one_le_right (by positivity) he)

/-- Preliminary exponential growth on a fixed real strip, sufficient for later PL.
Guide: sol-thin-hk2/PROOFS.md:1547–1592. Uses the split completed Mellin integral,
hk_mellin_FE_completed, reciprocal Gamma reflection/recurrence and compact continuity.
The constants may depend on this character; polynomial growth is supplied by HK-H3. -/
theorem hk_entire_L_preliminary_growth [IsTotallyComplex K] {m : RayClassModulus K}
    (ψ : RayClassGroup m →* ℂˣ) (hψ : ψ ≠ 1) (hp : HKPrimitive ψ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖hkEntireL ψ s‖ ≤ C * Real.exp (B * (1 + |s.im|)) := by
  classical
  letI : Finite (RayClassGroup m) := rayClassGroup_finite_viaCFT m
  letI : Fintype (RayClassGroup m) := Fintype.ofFinite _
  let R := hkRayRepresentatives m
  let P := rayCharacterFEPair R ψ
  have hP : IsStrongFEPair P := by
    constructor
    · exact finiteFEPair_f₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => rayFEPair m (R.ideal C) (R.coprime C))
        (rayPrimalConstant m : ℂ) (fun _ => rfl) (1 / 2) (by norm_num)
        (fun _ => rfl)
    · exact finiteFEPair_g₀_eq_zero_of_nontrivialCharacter ψ hψ
        (fun C => rayFEPair m (R.ideal C) (R.coprime C))
        (rayDualConstant m : ℂ) (fun _ => by simp [rayFEPair]) (1 / 2) (by norm_num)
        (fun _ => rfl)
  let α : ℝ := a / 2
  let β : ℝ := b / 2
  have hαβ : α ≤ β := by dsimp [α, β]; linarith
  have hnormMellin (u : ℝ) : IntegrableOn
      (fun t : ℝ => t ^ (u - 1) * ‖P.f t‖) (Set.Ioi 0) := by
    have hM := (hP.hasMellin (u : ℂ)).1
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((u : ℂ) - 1) • P.f t)
      (Set.Ioi 0) at hM
    have hnorm := hM.norm
    refine IntegrableOn.congr_fun hnorm (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have henv : IntegrableOn
      (fun t : ℝ => (t ^ (α - 1) + t ^ (β - 1)) * ‖P.f t‖) (Set.Ioi 0) := by
    have hsum := (hnormMellin α).add (hnormMellin β)
    refine IntegrableOn.congr_fun hsum (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  let M : ℝ := ∫ t : ℝ,
    (t ^ (α - 1) + t ^ (β - 1)) * ‖P.f t‖ ∂(volume.restrict (Set.Ioi 0))
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg_of_ae
    exact (ae_restrict_iff' measurableSet_Ioi).2 <|
      Filter.Eventually.of_forall (fun t ht => by
        have ht0 : 0 < t := ht
        positivity)
  have hstripLambda : ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖P.Λ (s / 2)‖ ≤ M := by
    intro s hsa hsb
    have hMs : MellinConvergent P.f (s / 2) := (hP.hasMellin (s / 2)).1
    have hre : α ≤ (s / 2).re ∧ (s / 2).re ≤ β := by
      dsimp [α, β]
      constructor <;> norm_num [Complex.div_re] <;> linarith
    have hkernel (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
        ‖(t : ℂ) ^ (s / 2 - 1) • P.f t‖ ≤
          (t ^ (α - 1) + t ^ (β - 1)) * ‖P.f t‖ := by
      have htpos : 0 < t := ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos]
      have hpow : t ^ ((s / 2).re - 1) ≤ t ^ (α - 1) + t ^ (β - 1) := by
        by_cases ht1 : t ≤ 1
        · have hle := Real.rpow_le_rpow_of_exponent_ge htpos ht1
            (show α - 1 ≤ (s / 2).re - 1 by linarith)
          exact hle.trans (le_add_of_nonneg_right (Real.rpow_nonneg htpos.le _))
        · have ht1' : 1 ≤ t := le_of_not_ge ht1
          have hle := Real.rpow_le_rpow_of_exponent_le ht1'
            (show (s / 2).re - 1 ≤ β - 1 by linarith)
          exact hle.trans (le_add_of_nonneg_left (Real.rpow_nonneg htpos.le _))
      exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    have hnormInt : Integrable (fun t : ℝ =>
        ‖(t : ℂ) ^ (s / 2 - 1) • P.f t‖) (volume.restrict (Set.Ioi 0)) := by
      change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f t) (Set.Ioi 0)
        at hMs
      exact hMs.norm
    have hle : (fun t : ℝ => ‖(t : ℂ) ^ (s / 2 - 1) • P.f t‖) ≤ᵐ[
        volume.restrict (Set.Ioi 0)]
        (fun t : ℝ => (t ^ (α - 1) + t ^ (β - 1)) * ‖P.f t‖) := by
      exact (ae_restrict_iff' measurableSet_Ioi).2 <|
        Filter.Eventually.of_forall (fun t ht => hkernel t ht)
    have hmono := integral_mono_ae hnormInt henv hle
    calc
      ‖P.Λ (s / 2)‖ = ‖mellin P.f (s / 2)‖ := by rw [hP.Λ_eq]
      _ = ‖∫ t : ℝ, (t : ℂ) ^ (s / 2 - 1) • P.f t
            ∂(volume.restrict (Set.Ioi 0))‖ := by
        rfl
      _ ≤ ∫ t : ℝ, ‖(t : ℂ) ^ (s / 2 - 1) • P.f t‖
            ∂(volume.restrict (Set.Ioi 0)) := norm_integral_le_integral_norm _
      _ ≤ M := by simpa [M] using hmono
  obtain ⟨Cγ, Bγ, hCγ, hBγ, hGamma⟩ := exists_gamma_inv_strip_bound a b hab
  let jR : ℝ := ((heckeJacobian K : ℝ≥0) : ℝ)
  let βR : ℝ := heckeBeta K
  let Cpi : ℝ := max (Real.pi ^ a) (Real.pi ^ b)
  let Cbeta : ℝ := max (βR ^ (a / 2)) (βR ^ (b / 2))
  have hjR : 0 < jR := by
    dsimp [jR]
    exact_mod_cast DedekindResidue.heckeJacobian_pos K
  have hβR : 0 < βR := by
    dsimp [βR]
    exact DedekindResidue.heckeBeta_pos K
  have hCpi : 0 < Cpi := by
    dsimp [Cpi]
    positivity
  have hCbeta : 0 < Cbeta := by
    dsimp [Cbeta, βR]
    positivity
  have hplaces : Fintype.card (InfinitePlace K) = nrComplexPlaces K := by
    calc
      Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      _ = nrComplexPlaces K := by simp
  have hpowBound (x l u v : ℝ) (hx : 0 < x) (hl : l ≤ v) (hu : v ≤ u) :
      x ^ v ≤ max (x ^ l) (x ^ u) := by
    by_cases h1 : 1 ≤ x
    · exact (Real.rpow_le_rpow_of_exponent_le h1 hu).trans (le_max_right _ _)
    · have hx1 : x ≤ 1 := le_of_not_ge h1
      exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 hl).trans (le_max_left _ _)
  have hpiPow (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
      ‖(Real.pi : ℂ) ^ s‖ ≤ Cpi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact hpowBound Real.pi a b s.re Real.pi_pos hsa hsb
  have hbetaPow (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
      ‖(heckeBeta K : ℂ) ^ (s / 2)‖ ≤ Cbeta := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hβR]
    apply hpowBound βR (a / 2) (b / 2) ((s / 2).re) hβR ?_ ?_
    · norm_num [Complex.div_re]
      linarith
    · norm_num [Complex.div_re]
      linarith
  have hthetaFactor (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b)
      (w : InfinitePlace K) :
      ‖(Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
        (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ ≤
        Cpi * Cγ * Real.exp (Bγ * (1 + |s.im|)) := by
    simp only [NumberField.IsTotallyComplex.mult_eq]
    have harg : (2 : ℂ) * s / (2 : ℂ) = s := by field_simp
    change ‖(Real.pi : ℂ) ^ ((2 : ℂ) * s / 2) *
      (Complex.Gamma ((2 : ℂ) * s / 2))⁻¹‖ ≤ _
    rw [harg, norm_mul]
    calc
      ‖(Real.pi : ℂ) ^ s‖ * ‖(Complex.Gamma s)⁻¹‖ ≤
          Cpi * (Cγ * Real.exp (Bγ * (1 + |s.im|))) :=
        mul_le_mul (hpiPow s hsa hsb) (hGamma s hsa hsb)
          (norm_nonneg _) (by positivity)
      _ = Cpi * Cγ * Real.exp (Bγ * (1 + |s.im|)) := by ring
  have hGammaProd (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
      ‖∏ w : InfinitePlace K,
          (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
            (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ ≤
        (Cpi * Cγ) ^ nrComplexPlaces K *
          Real.exp ((nrComplexPlaces K : ℝ) * Bγ * (1 + |s.im|)) := by
    rw [norm_prod]
    let D : ℝ := Cpi * Cγ * Real.exp (Bγ * (1 + |s.im|))
    have hD : 0 < D := by dsimp [D]; positivity
    have hprod : ∀ S : Finset (InfinitePlace K),
        (∏ w ∈ S, ‖(Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
          (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖) ≤ D ^ S.card := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [D]
      | @insert w S hw ih =>
          rw [Finset.prod_insert hw, Finset.card_insert_of_notMem hw]
          have hprev : 0 ≤ ∏ w ∈ S,
              ‖(Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ := by positivity
          calc
            ‖(Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ *
                ∏ w ∈ S, ‖(Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                  (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖
              ≤ D * D ^ S.card := by
                exact mul_le_mul (by simpa [D] using hthetaFactor s hsa hsb w)
                  ih hprev hD.le
            _ = D ^ (S.card + 1) := by rw [pow_succ]; ring
    calc
      _ ≤ D ^ Fintype.card (InfinitePlace K) := hprod Finset.univ
      _ = D ^ nrComplexPlaces K := by rw [hplaces]
      _ = (Cpi * Cγ) ^ nrComplexPlaces K *
            Real.exp ((nrComplexPlaces K : ℝ) * Bγ * (1 + |s.im|)) := by
        dsimp [D]
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  let Cnorm : ℝ := jR⁻¹ * Cbeta * (Cpi * Cγ) ^ nrComplexPlaces K
  let Bnorm : ℝ := (nrComplexPlaces K : ℝ) * Bγ
  have hCnorm : 0 < Cnorm := by
    dsimp [Cnorm]
    positivity
  have hBnorm : 0 < Bnorm := by
    dsimp [Bnorm]
    have hr : (0 : ℝ) < (nrComplexPlaces K : ℝ) := by
      have hcard : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos_iff.mpr inferInstance
      rw [hplaces] at hcard
      exact_mod_cast hcard
    exact mul_pos hr hBγ
  have hnormalizer (s : ℂ) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
      ‖rayMellinNormalization K s‖ ≤
        Cnorm * Real.exp (Bnorm * (1 + |s.im|)) := by
    have hjNorm :
        ‖((((heckeJacobian K : ℝ≥0) : ℝ) : ℂ))⁻¹‖ = jR⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hjR]
    unfold rayMellinNormalization
    rw [norm_mul, norm_mul, hjNorm]
    have hinner :
        ‖(heckeBeta K : ℂ) ^ (s / 2)‖ *
          ‖∏ w : InfinitePlace K,
            (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
              (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ ≤
        Cbeta * ((Cpi * Cγ) ^ nrComplexPlaces K *
          Real.exp ((nrComplexPlaces K : ℝ) * Bγ * (1 + |s.im|))) := by
      calc
        _ ≤ Cbeta * ‖∏ w : InfinitePlace K,
              (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖ :=
          mul_le_mul_of_nonneg_right (hbetaPow s hsa hsb) (norm_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hGammaProd s hsa hsb) (le_of_lt hCbeta)
    calc
      jR⁻¹ * ‖(heckeBeta K : ℂ) ^ (s / 2)‖ *
          ‖∏ w : InfinitePlace K,
            (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
              (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖
        ≤ jR⁻¹ * (Cbeta * ((Cpi * Cγ) ^ nrComplexPlaces K *
            Real.exp ((nrComplexPlaces K : ℝ) * Bγ * (1 + |s.im|)))) := by
          calc
            _ = jR⁻¹ * (‖(heckeBeta K : ℂ) ^ (s / 2)‖ *
                ‖∏ w : InfinitePlace K,
                  (Real.pi : ℂ) ^ ((mult w : ℂ) * s / 2) *
                    (Complex.Gamma ((mult w : ℂ) * s / 2))⁻¹‖) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr hjR.le)
      _ = Cnorm * Real.exp (Bnorm * (1 + |s.im|)) := by
          dsimp [Cnorm, Bnorm]
          ring_nf
  let C : ℝ := max 1 (Cnorm * M)
  let B : ℝ := Bnorm + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hBpos : 0 < B := by dsimp [B]; linarith [hBnorm]
  refine ⟨C, B, hCpos, hBpos, ?_⟩
  intro s hsa hsb
  have hnormalizer' := hnormalizer s hsa hsb
  have hLambda := hstripLambda s hsa hsb
  calc
    ‖hkEntireL ψ s‖ =
        ‖rayMellinNormalization K s * P.Λ (s / 2)‖ := rfl
    _ = ‖rayMellinNormalization K s‖ * ‖P.Λ (s / 2)‖ := norm_mul _ _
    _ ≤ (Cnorm * Real.exp (Bnorm * (1 + |s.im|))) * M :=
      mul_le_mul hnormalizer' hLambda (norm_nonneg _) (by positivity)
    _ = (Cnorm * M) * Real.exp (Bnorm * (1 + |s.im|)) := by ring
    _ ≤ C * Real.exp (B * (1 + |s.im|)) := by
      have hC : Cnorm * M ≤ C := by dsimp [C]; exact le_max_right _ _
      have hExp : Real.exp (Bnorm * (1 + |s.im|)) ≤
          Real.exp (B * (1 + |s.im|)) := by
        apply Real.exp_le_exp.mpr
        dsimp [B]
        nlinarith [abs_nonneg s.im]
      exact mul_le_mul hC hExp (Real.exp_nonneg _) (by positivity)

end ArtinPrimitiveRoots.Hecke
