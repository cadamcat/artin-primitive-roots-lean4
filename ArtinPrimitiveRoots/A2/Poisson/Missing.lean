import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Interface

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

section Poisson
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)

/-- def:po-weights, 05:24–36,84–90. Support is compact inside the unit locus, not merely away
from the single zero point of the product ring. -/
structure PoissonWeights where
  W1 : ℝ → ℂ
  W1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W1
  W1_compact : HasCompactSupport W1
  W1_positive_support : tsupport W1 ⊆ Set.Ioi 0
  W1_nonnegative : ∀ t, (W1 t).im = 0 ∧ 0 ≤ (W1 t).re
  W1_nonzero : ∃ t, W1 t ≠ 0
  arch : InfinitePlace F → SchwartzMap ℂ ℂ
  finite : ∀ v : S.Sf, S.FiniteTest v
  W0 : S.FS → ℂ
  W0_tensor : ∀ y, W0 y = (∏ v : S.Sf, (finite v).1 (y.1 v)) * ∏ w : InfinitePlace F, arch w (y.2 w)
  W0_Bruhat : W0 ∈ S.BruhatSchwartz
  W0_compact : HasCompactSupport W0
  W0_units : ∀ y ∈ tsupport W0, IsUnit y

variable (W : PoissonWeights (S := S))
def weightFourier : S.FS → ℂ := S.fourier A sd.measure W.W0
def weightM (z : ℂ) : ℂ := ∫ y, weightFourier sd W y * (S.absS y : ℂ) ^ z ∂(R.sheets.mul)
def weightW1hat (w : ℂ) : ℂ := ∫ t in Set.Ioi (0 : ℝ), W.W1 t * (t : ℂ) ^ w / (t : ℂ)
def weightV0 (T : ℝ) : ℂ :=
  ∫ y, weightFourier sd W y ∂(R.sheets.sheet T)

def WeightSpec : Prop := weightFourier sd W 0 = 0 ∧ weightM R sd W (1 / 6) ≠ 0

def WeightDecay : Prop :=
  DifferentiableOn ℂ (weightM R sd W) {z | 0 < z.re} ∧ Differentiable ℂ (weightW1hat W) ∧
  (∀ l r A0 : ℝ, 0 < l → l ≤ r → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ σ τ : ℝ, l ≤ σ → σ ≤ r →
      ‖weightM R sd W (σ + τ * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-A0)) ∧
  (∀ l r A0 : ℝ, l ≤ r → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ σ τ : ℝ, l ≤ σ → σ ≤ r →
      ‖weightW1hat W (σ + τ * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-A0)) ∧
  (∀ σ : ℝ, 0 < σ → Integrable (fun y =>
    ‖weightFourier sd W y‖ * S.absS y ^ σ) R.sheets.mul)

/-- po:weights-exist, 05:37–75. The existence and universal analytic conclusions are separate. -/
theorem po_weights_exist :
  (∃ W : PoissonWeights (S := S), WeightSpec R sd W) ∧
    ∀ W : PoissonWeights (S := S), WeightDecay R sd W := by
  sorry
/-- ext:tate-local-FE, finite-place version at the actual completion and frozen additive sign.
A scalar c_v(s) is independent of the test function; the strip is open. -/
theorem ext_tate_local_FE_fin (v : FinPlace F) :
  ∃ c : ℂ → ℂ, c (1 / 6) ≠ 0 ∧ ∀ f : v.adicCompletion F → ℂ,
    Continuous f → HasCompactSupport f → IsLocallyConstant f → ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (∫ y, (∫ x, f x * A.ψ v (-(x * y)) ∂(μ v).μ) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin (μ v)) =
      c s * ∫ y, f y * (absFin v y : ℂ) ^ (1 - s) ∂Theta.mulHaarFin (μ v) := by
  sorry
/-- ext:tate-local-FE, complex-place version. Haar scalings are absorbed in c_v. -/
theorem ext_tate_local_FE_complex :
  ∃ c : ℂ → ℂ, c (1 / 6) ≠ 0 ∧ ∀ f : SchwartzMap ℂ ℂ, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    (∫ y : ℂ, (∫ x : ℂ, f x * psiC (-(x * y))) * (Complex.normSq y : ℂ) ^ s ∂Theta.mulHaarC) =
      c s * ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (1 - s) ∂Theta.mulHaarC := by
  sorry
/-- def:po-finite-factor: Gauss sum over the actual R/(I), with an explicit allowed generator. -/
def finiteGaussAt (I : S.ExtIdeal) (a : Fˣ) (k : F) : ℂ :=
  ∑ᶠ x : ResidueRing R.exterior I, chiIdealPow D I.1 (x.out : F) 1 * S.e A (S.diag (k * (x.out : F) / (a : F)))
def finiteGauss (I : S.ExtIdeal) (k : F) : ℂ := finiteGaussAt R I (bc.gen I) k

def finiteFactor (s I : S.ExtIdeal) (a : Fˣ) (h : F) : ℂ :=
  ∑ᶠ d : ResidueRing R.exterior s,
    if ∃ x : S.R, h - (a : F) * (d.out : F) = (bc.gen s : F) * (x : F) then
      chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R I a ((h - (a : F) * (d.out : F)) / (bc.gen s : F))
    else 0

/-- def:po-probe, 05:77–101. Quotient integration is implemented by the fixed Ω₁. -/
def probeIntegrand (X Y Z : ℝ) (t : S.FSˣ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : S.ExtIdeal, W.W1 (qI s.1 / Y) * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑' m : S.R, (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m : F)) *
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
        Bm D S A ϑ (cgen R) (m : F) Z

def probe (X Y Z : ℝ) : ℂ := omegaInt R 1 (probeIntegrand R W X Y Z)

private theorem po_probe_weight_zero : W.W0 0 = 0 := by
  by_contra h
  have hmem : 0 ∈ Function.support W.W0 := Function.mem_support.mpr h
  have hts : 0 ∈ tsupport W.W0 := subset_closure hmem
  exact (W.W0_units 0 hts).ne_zero rfl

private theorem po_probe_weight_continuous (W : PoissonWeights (S := S)) :
    Continuous W.W0 := by
  have hEq : W.W0 = fun y : S.FS =>
      (∏ v : S.Sf, (W.finite v).1 (y.1 v)) *
        ∏ w : InfinitePlace F, W.arch w (y.2 w) := funext W.W0_tensor
  rw [hEq]
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    exact (W.finite v).2.1.comp ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    exact (W.arch w).continuous.comp ((continuous_apply w).comp continuous_snd)

private theorem po_absS_continuous (S : SData F CE condη) : Continuous S.absS := by
  unfold SData.absS
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v hv
    have habs : Continuous (absFin v.1) := by
      convert (continuous_norm : Continuous fun x : v.1.adicCompletion F => ‖x‖) using 1
      ext x
      exact A1.Theta.absFin_eq_norm v.1 x
    exact habs.comp ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w hw
    exact Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)

private theorem po_absS_one_isUnit (S : SData F CE condη) (y : S.FS)
    (hy : S.absS y = 1) : IsUnit y := by
  have hfin (v : S.Sf) : absFin v.1 (y.1 v) ≠ 0 := by
    intro hz
    have hprod : (∏ v' : S.Sf, absFin v'.1 (y.1 v')) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) hz
    have hzero : S.absS y = 0 := by
      unfold SData.absS
      rw [hprod]
      simp
    rw [hy] at hzero
    norm_num at hzero
  have harch (w : InfinitePlace F) : Complex.normSq (y.2 w) ≠ 0 := by
    intro hz
    have hprod : (∏ w' : InfinitePlace F, Complex.normSq (y.2 w')) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ w) hz
    have hzero : S.absS y = 0 := by
      unfold SData.absS
      rw [hprod]
      simp
    rw [hy] at hzero
    norm_num at hzero
  have hfin' (v : S.Sf) : y.1 v ≠ 0 := by
    intro h
    apply hfin v
    simp [h, absFin]
  have harch' (w : InfinitePlace F) : y.2 w ≠ 0 := by
    intro h
    exact harch w (by simp [h])
  simpa [Prod.isUnit_iff, Pi.isUnit_iff] using And.intro hfin' harch'

private theorem po_finite_diagR_inter_compact (D : FieldData F) (K : Set S.FS)
    (hK : IsCompact K) :
    (K ∩ S.diagR).Finite := by
  let Hring : Subring S.FS := (S.diag.comp S.R.val.toRingHom).range
  let H : AddSubgroup S.FS := Hring.toAddSubgroup
  have hH : (H : Set S.FS) = S.diagR := by
    change Set.range (fun x : S.R => S.diag (x : F)) = _
    rfl
  have hdiscrete : IsDiscrete (H : Set S.FS) := by
    simpa only [hH] using (S.diagR_discrete_cocompact D).1
  have hclosed : IsClosed (H : Set S.FS) := H.isClosed_of_isDiscrete hdiscrete
  have hcompact : IsCompact (K ∩ (H : Set S.FS)) := hK.inter_right hclosed
  have hdiscrete' : IsDiscrete (K ∩ (H : Set S.FS)) :=
    hdiscrete.mono Set.inter_subset_right
  have hfinite := hcompact.finite hdiscrete'
  simpa only [hH] using hfinite

private theorem po_probe_row_support_finite (X : ℝ) (t : S.FSˣ) (s : S.ExtIdeal) :
    (Function.support (fun m : S.R =>
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val))).Finite := by
  classical
  let a : S.FSˣ := t * R.sheets.ellU (qI s.1 * X)
  let K : Set S.FS := (fun y : S.FS => y * (a : S.FS)) '' tsupport W.W0
  have hWcompact : IsCompact (tsupport W.W0) := W.W0_compact
  have hK : IsCompact K := by
    change IsCompact ((fun y : S.FS => y * (a : S.FS)) '' tsupport W.W0)
    exact hWcompact.image (continuous_id.mul continuous_const)
  have hfinite := po_finite_diagR_inter_compact D K hK
  have hdiag : Function.Injective (fun m : S.R => S.diag (m : F)) := by
    intro m n hmn
    apply Subtype.ext
    apply v0.embedding.injective
    change (S.diag (m : F)).2 v0 = (S.diag (n : F)).2 v0
    exact congrArg (fun y : S.FS => y.2 v0) hmn
  apply Set.Finite.of_injOn (f := fun m : S.R => S.diag (m : F))
    (s := Function.support (fun m : S.R =>
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val)))
    (t := K ∩ S.diagR) ?_ ?_ hfinite
  · intro m hm
    have hts : S.diag (m : F) * (a⁻¹ : S.FS) ∈ tsupport W.W0 := by
      apply subset_closure
      have hne : W.W0 (S.diag (m : F) * (a⁻¹ : S.FS)) ≠ 0 := by
        simpa [a] using Function.mem_support.mp hm
      exact Function.mem_support.mpr hne
    constructor
    · refine ⟨S.diag (m : F) * (a⁻¹ : S.FS), hts, ?_⟩
      change (S.diag (m : F) * (a⁻¹ : S.FS)) * (a : S.FS) = S.diag (m : F)
      calc
        _ = S.diag (m : F) * ((a⁻¹ : S.FS) * (a : S.FS)) := by ac_rfl
        _ = S.diag (m : F) := by simp
    · exact ⟨m, rfl⟩
  · intro m hm n hn hmn
    exact hdiag hmn

private theorem po_probe_row_support_uniform (X : ℝ) (s : S.ExtIdeal) :
    {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}.Finite := by
  classical
  obtain ⟨K, hK, hOmega⟩ := R.sheets.omega_bounded
  let a0 : S.FSˣ := R.sheets.ellU 1
  let a1 : S.FSˣ := R.sheets.ellU (qI s.1 * X)
  let Kunit : Set S.FS := (fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K
  have hWcompact : IsCompact (tsupport W.W0) := W.W0_compact
  have hKunit : IsCompact Kunit := by
    change IsCompact ((fun x : S.FS => (a0 : S.FS) * x * (a1 : S.FS)) '' K)
    exact hK.image ((continuous_const.mul continuous_id).mul continuous_const)
  let Ktotal : Set S.FS :=
    (fun p : S.FS × S.FS => p.1 * p.2) '' (tsupport W.W0 ×ˢ Kunit)
  have hKtotal : IsCompact Ktotal := by
    change IsCompact ((fun p : S.FS × S.FS => p.1 * p.2) ''
      (tsupport W.W0 ×ˢ Kunit))
    exact (hWcompact.prod hKunit).image (continuous_fst.mul continuous_snd)
  have hfinite := po_finite_diagR_inter_compact D Ktotal hKtotal
  have hdiag : Function.Injective (fun m : S.R => S.diag (m : F)) := by
    intro m n hmn
    apply Subtype.ext
    apply v0.embedding.injective
    change (S.diag (m : F)).2 v0 = (S.diag (n : F)).2 v0
    exact congrArg (fun y : S.FS => y.2 v0) hmn
  apply Set.Finite.of_injOn (f := fun m : S.R => S.diag (m : F))
    (s := {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ omegaAt R 1 ∧
      W.W0 (S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val) ≠ 0})
    (t := Ktotal ∩ S.diagR) ?_ ?_ hfinite
  · intro m hm
    obtain ⟨t, ht, hW⟩ := hm
    let y : S.FS :=
      S.diag (m : F) * ((t * a1)⁻¹ : S.FSˣ).val
    have hy : y ∈ tsupport W.W0 := by
      apply subset_closure
      exact Function.mem_support.mpr hW
    rcases ht with ⟨x, hx, htx⟩
    have hta : (t : S.FS) * (a1 : S.FS) ∈ Kunit := by
      refine ⟨x, hOmega hx, ?_⟩
      dsimp [Kunit]
      rw [htx]
    constructor
    · refine ⟨(y, (t : S.FS) * (a1 : S.FS)), ⟨hy, hta⟩, ?_⟩
      dsimp [y]
      simp [mul_assoc]
    · exact ⟨m, rfl⟩
  · intro m hm n hn hmn
    exact hdiag hmn

private theorem po_probe_rows_on_compact (X : ℝ) (s : S.ExtIdeal)
    (K : Set S.FS) (hK : IsCompact K) :
    {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ K ∧
      W.W0 (S.diag (m : F) *
        ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0}.Finite := by
  classical
  let ell : S.FSˣ := R.sheets.ellU (qI s.1 * X)
  let Kunit : Set S.FS := (fun y : S.FS => y * (ell : S.FS)) '' K
  have hWcompact : IsCompact (tsupport W.W0) := W.W0_compact
  have hKunit : IsCompact Kunit := by
    change IsCompact ((fun y : S.FS => y * (ell : S.FS)) '' K)
    exact hK.image (continuous_id.mul continuous_const)
  let Ktotal : Set S.FS :=
    (fun p : S.FS × S.FS => p.1 * p.2) '' (tsupport W.W0 ×ˢ Kunit)
  have hKtotal : IsCompact Ktotal := by
    change IsCompact ((fun p : S.FS × S.FS => p.1 * p.2) ''
      (tsupport W.W0 ×ˢ Kunit))
    exact (hWcompact.prod hKunit).image (continuous_fst.mul continuous_snd)
  have hfinite := po_finite_diagR_inter_compact D Ktotal hKtotal
  have hdiag : Function.Injective (fun m : S.R => S.diag (m : F)) := by
    intro m n hmn
    apply Subtype.ext
    apply v0.embedding.injective
    change (S.diag (m : F)).2 v0 = (S.diag (n : F)).2 v0
    exact congrArg (fun y : S.FS => y.2 v0) hmn
  apply Set.Finite.of_injOn (f := fun m : S.R => S.diag (m : F))
    (s := {m : S.R | ∃ t : S.FSˣ, (t : S.FS) ∈ K ∧
      W.W0 (S.diag (m : F) * ((t * ell)⁻¹ : S.FSˣ).val) ≠ 0})
    (t := Ktotal ∩ S.diagR) ?_ ?_ hfinite
  · intro m hm
    obtain ⟨t, ht, hW⟩ := hm
    have hts : S.diag (m : F) * ((t * ell)⁻¹ : S.FSˣ).val ∈ tsupport W.W0 := by
      apply subset_closure
      exact Function.mem_support.mpr hW
    have harg : S.diag (m : F) * ((t * ell)⁻¹ : S.FSˣ).val * (t * ell : S.FS) =
        S.diag (m : F) := by simp [mul_assoc]
    constructor
    · refine ⟨(S.diag (m : F) * ((t * ell)⁻¹ : S.FSˣ).val, (t : S.FS) * ell),
        ⟨hts, ⟨(t : S.FS), ht, rfl⟩⟩, ?_⟩
      simpa [mul_assoc] using harg
    · exact ⟨m, rfl⟩
  · intro m hm n hn hmn
    exact hdiag hmn

private lemma po_count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma po_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    po_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe F v (by
      simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hn),
    ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe F v (by
      simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hd),
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd),
    v.intValuation_if_neg hn, v.intValuation_if_neg hd,
    WithZero.log_exp, WithZero.log_exp]
  ring

private theorem po_gen_ratio_mem_R (I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1) :
    ((R.exterior.genR I : F) / (a : F)) ∈ S.R := by
  have hg : S.IsGen (R.exterior.genR I : F) I.1 := by
    rw [R.exterior.genR_val]
    exact (bc.gen_spec I).1
  change ∀ v : FinPlace F, v ∉ S.Sf →
    HeightOneSpectrum.valuation F v ((R.exterior.genR I : F) / (a : F)) ≤ 1
  intro v hv
  have hcount := po_count_spanSingleton_div v (R.exterior.genR I : F) (a : F)
    hg.2.1 a.ne_zero
  rw [hg.2.2 v hv, ha.2.2 v hv, sub_self] at hcount
  have hlog := po_count_spanSingleton_eq_neg_log_valuation v
    ((R.exterior.genR I : F) / (a : F)) (div_ne_zero hg.2.1 a.ne_zero)
  rw [hcount] at hlog
  have hlog0 : WithZero.log
      (HeightOneSpectrum.valuation F v ((R.exterior.genR I : F) / (a : F))) = 0 := by
    linarith
  have hv0 : HeightOneSpectrum.valuation F v ((R.exterior.genR I : F) / (a : F)) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr (div_ne_zero hg.2.1 a.ne_zero)
  have hv1 : HeightOneSpectrum.valuation F v ((R.exterior.genR I : F) / (a : F)) = 1 := by
    have h := WithZero.exp_log hv0
    rw [hlog0] at h
    simpa using h.symm
  rw [hv1]

private theorem po_gen_lt_one (I : S.ExtIdeal) (v : FinPlace F)
    (hvI : v.asIdeal ∣ I.1) :
    HeightOneSpectrum.valuation F v (R.exterior.genR I : F) < 1 := by
  have hg : S.IsGen (R.exterior.genR I : F) I.1 := by
    rw [R.exterior.genR_val]
    exact (bc.gen_spec I).1
  have hI0 : I.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using I.2.1
  have hcountI : 0 < FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.count_coe F v hI0]
    exact_mod_cast Nat.pos_of_ne_zero
      ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).2 hvI)
  have hvS : v ∉ S.Sf := fun hv => I.2.2 v hv (Ideal.le_of_dvd hvI)
  have hcountg := hg.2.2 v hvS
  have hlog := po_count_spanSingleton_eq_neg_log_valuation v
    (R.exterior.genR I : F) hg.2.1
  rw [hcountg] at hlog
  have hloglt : WithZero.log (HeightOneSpectrum.valuation F v (R.exterior.genR I : F)) < 0 := by
    linarith
  have hgval0 : HeightOneSpectrum.valuation F v (R.exterior.genR I : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hg.2.1
  calc
    HeightOneSpectrum.valuation F v (R.exterior.genR I : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (R.exterior.genR I : F))) :=
      (WithZero.exp_log hgval0).symm
    _ < 1 := WithZero.exp_lt_one_iff.mpr hloglt

private theorem po_e_add (S : SData F CE condη) (A : AddCharData F)
    (x y : S.FS) : S.e A (x + y) = S.e A x * S.e A y := by
  unfold SData.e
  have hfin : (∏ v : S.Sf, A.ψ v.1 ((x + y).1 v)) =
      (∏ v : S.Sf, A.ψ v.1 (x.1 v)) * ∏ v : S.Sf, A.ψ v.1 (y.1 v) := by
    calc
      _ = ∏ v : S.Sf, A.ψ v.1 (x.1 v) * A.ψ v.1 (y.1 v) := by
        apply Finset.prod_congr rfl
        intro v hv
        exact (A.ψ v.1).map_add_eq_mul (x.1 v) (y.1 v)
      _ = _ := Finset.prod_mul_distrib
  have harch : (∏ w : InfinitePlace F, psiC ((x + y).2 w)) =
      (∏ w : InfinitePlace F, psiC (x.2 w)) * ∏ w : InfinitePlace F, psiC (y.2 w) := by
    calc
      _ = ∏ w : InfinitePlace F, psiC (x.2 w) * psiC (y.2 w) := by
        apply Finset.prod_congr rfl
        intro w hw
        dsimp [psiC]
        have harg : -(4 * Real.pi * Complex.I *
          (((x.2 w).re : ℂ) + ((y.2 w).re : ℂ))) =
            -(4 * Real.pi * Complex.I * ((x.2 w).re : ℂ)) +
            -(4 * Real.pi * Complex.I * ((y.2 w).re : ℂ)) := by ring
        rw [Complex.ofReal_add, harg, Complex.exp_add]
      _ = _ := Finset.prod_mul_distrib
  rw [hfin, harch]
  ring

private theorem po_e_diagR_one (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F) (x : S.R) : S.e A (S.diag (x : F)) = 1 := by
  have hx : S.diag (x : F) ∈ S.diagR := ⟨x, rfl⟩
  have hAnn : S.diag (x : F) ∈ S.annihilator A S.diagR := by
    rw [← S.diagR_eq_annihilator D A]
    exact hx
  have h1 : S.diag (1 : F) ∈ S.diagR := ⟨1, rfl⟩
  have h := hAnn (S.diag (1 : F)) h1
  simpa [SData.diag] using h

private theorem po_chiIdealPow_six (D : FieldData F) (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (y : F)
    (hy : ∀ v : FinPlace F, v.asIdeal ∣ I →
      HeightOneSpectrum.valuation F v y = 1) :
    chiIdealPow D I y 1 ^ 6 = 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  unfold chiIdealPow
  have hprod (s : Multiset ℂ) : s.prod ^ 6 = (s.map fun z => z ^ 6).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons z s ih => simp [mul_pow, ih]
  rw [hprod]
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨z₀, hz₀, hpow⟩ := Multiset.mem_map.mp hz
  rw [← hpow]
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz₀
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · simp only [dif_pos hp]
    let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hvI : v.asIdeal ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hres : residue v y ≠ 0 :=
      (SB.residue_ne_zero v y (by rw [hy v hvI])).2 (hy v hvI)
    rw [SB.chiPow_nonzero v y 1 hres]
    simpa using SB.chi_six v y hres
  · simp [hp]

private theorem po_chiIdealPow_sixArg (D : FieldData F) (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (y : F)
    (hy : ∀ v : FinPlace F, v.asIdeal ∣ I →
      HeightOneSpectrum.valuation F v y = 1) :
    chiIdealPow D I (y ^ 6) 1 = 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  unfold chiIdealPow
  apply Multiset.prod_eq_one
  intro z hz
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hz
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · simp only [dif_pos hp]
    let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hvI : v.asIdeal ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hvS : v ∉ S.Sf := fun hv => hI.2 v hv (Ideal.le_of_dvd hvI)
    have hy1 : HeightOneSpectrum.valuation F v y = 1 := hy v hvI
    have hy_le : HeightOneSpectrum.valuation F v y ≤ 1 := hy1.le
    have hres : residue v y ≠ 0 := (SB.residue_ne_zero v y hy_le).2 hy1
    have hyPow : HeightOneSpectrum.valuation F v (y ^ 6) = 1 := by
      rw [map_pow, hy1]
      norm_num
    have hresPow : residue v (y ^ 6) ≠ 0 :=
      (SB.residue_ne_zero v (y ^ 6) hyPow.le).2 hyPow
    have hchi1 : chi D v 1 = 1 := by
      have hchi0 := SB.chi_six v y hres
      have hchiNe : chi D v y ≠ 0 := by
        intro h
        rw [h] at hchi0
        norm_num at hchi0
      have hone : HeightOneSpectrum.valuation F v (1 : F) ≤ 1 := by simp
      have hmul := SB.chi_mul v hvS y 1 hy_le hone
      have hmul' : chi D v y * chi D v 1 = chi D v y * 1 := by
        simpa using hmul.symm
      exact mul_left_cancel₀ hchiNe hmul'
    have hchiPow : ∀ n : ℕ, chi D v (y ^ n) = chi D v y ^ n := by
      intro n
      induction n with
      | zero => simp [hchi1]
      | succ n ih =>
          have hyn : HeightOneSpectrum.valuation F v (y ^ n) ≤ 1 := by
            rw [map_pow, hy1]
            simp
          calc
            chi D v (y ^ (n + 1)) = chi D v (y ^ n * y) := by rw [pow_succ]
            _ = chi D v (y ^ n) * chi D v y := SB.chi_mul v hvS (y ^ n) y hyn hy_le
            _ = chi D v y ^ (n + 1) := by rw [ih, pow_succ]
    rw [SB.chiPow_nonzero v (y ^ 6) 1 hresPow, zpow_one, hchiPow 6,
      SB.chi_six v y hres]
  · simp [hp]

private theorem po_chiIdealPow_congr (I : Ideal (𝓞 F)) (hI : S.IsExterior I)
    (x y : F)
    (hxy : ∀ v : FinPlace F, v.asIdeal ∣ I →
      HeightOneSpectrum.valuation F v x ≤ 1 ∧
      HeightOneSpectrum.valuation F v y ≤ 1 ∧
      HeightOneSpectrum.valuation F v (x - y) < 1) :
    chiIdealPow D I x 1 = chiIdealPow D I y 1 := by
  classical
  let SB := a2_bridge_SYMBOL D S
  unfold chiIdealPow
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · simp only [dif_pos hp]
    let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hvI : v.asIdeal ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hres := SB.residue_congr v x y (hxy v hvI).1 (hxy v hvI).2.1 (hxy v hvI).2.2
    simpa only [chiPow, zpow_one] using
      (show (if residue v x = 0 then (0 : ℂ) else chi D v x) =
          (if residue v y = 0 then (0 : ℂ) else chi D v y) by
        rw [hres, SB.chi_congr v x y hres])
  · simp [hp]

private theorem po_chiIdealPow_US_six (D : FieldData F) (S : SData F CE condη)
    (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (u : S.US) (x : S.R) :
    chiIdealPow D I (((u : Fˣ) : F) ^ 6 * (x : F)) 1 =
      chiIdealPow D I (x : F) 1 := by
  let SB := a2_bridge_SYMBOL D S
  have hu (v : FinPlace F) (hvI : v.asIdeal ∣ I) :
      HeightOneSpectrum.valuation F v ((u : Fˣ) : F) = 1 := by
    have hvS : v ∉ S.Sf := fun hv => hI.2 v hv (Ideal.le_of_dvd hvI)
    exact u.property v hvS
  have hmul : chiIdealPow D I ((((u : Fˣ) : F) ^ 6) * (x : F)) 1 =
      chiIdealPow D I (((u : Fˣ) : F) ^ 6) 1 * chiIdealPow D I (x : F) 1 :=
    SB.ideal_element_mul I hI (((u : Fˣ) : F) ^ 6) (x : F) 1 (by
      intro v hvI
      have hvS : v ∉ S.Sf := fun hv => hI.2 v hv (Ideal.le_of_dvd hvI)
      constructor
      · rw [map_pow, hu v hvI]
        norm_num
      · exact x.property v hvS)
  rw [po_chiIdealPow_sixArg D S I hI ((u : Fˣ) : F) hu, one_mul] at hmul
  exact hmul

private def po_probe_actUnit (S : SData F CE condη) : Gamma S →* S.FSˣ :=
  S.diagU.comp (S.US.subtype.comp (Gamma S).subtype)

private instance po_probe_smul (S : SData F CE condη) : SMul (Gamma S) S.FS :=
  ⟨fun γ y => (po_probe_actUnit S γ : S.FS) * y⟩

private instance po_probe_mulAction (S : SData F CE condη) : MulAction (Gamma S) S.FS where
  one_smul := by
    intro y
    change (po_probe_actUnit S 1 : S.FS) * y = y
    simp [po_probe_actUnit]
  mul_smul := by
    intro γ δ y
    change (po_probe_actUnit S (γ * δ) : S.FS) * y =
      (po_probe_actUnit S γ : S.FS) * ((po_probe_actUnit S δ : S.FS) * y)
    rw [map_mul]
    simp [mul_assoc]

private instance po_probe_measurableConstSMul (S : SData F CE condη) :
    MeasurableConstSMul (Gamma S) S.FS :=
  ⟨fun γ => by
    change Measurable (fun y : S.FS => (po_probe_actUnit S γ : S.FS) * y)
    exact (continuous_const.mul continuous_id).measurable⟩

private theorem po_probe_measurePreserving (γ : Gamma S) :
    MeasurePreserving (fun y : S.FS => γ • y)
      (R.sheets.sheet 1) (R.sheets.sheet 1) := by
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  change Measure.map (fun y : S.FS => (po_probe_actUnit S γ : S.FS) * y)
    (R.sheets.sheet 1) = R.sheets.sheet 1
  have hnorm : S.absS (po_probe_actUnit S γ : S.FS) = 1 :=
    (a2_bridge_NORM D S).2.2.2.1 (γ.1 : S.US)
  have htrans := R.sheets.sheet_translate (po_probe_actUnit S γ) 1 (by norm_num)
  rw [hnorm, one_mul] at htrans
  exact htrans

private instance po_probe_smulInvariantMeasure :
    SMulInvariantMeasure (Gamma S) S.FS (R.sheets.sheet 1) :=
  ⟨fun γ E hE => (po_probe_measurePreserving (R := R) γ).measure_preimage
      hE.nullMeasurableSet⟩

set_option maxHeartbeats 3000000 in
private theorem po_probe_fundamentalDomain (O : Set S.FS)
    (hO : IsFundamentalAt (S := S) O 1) :
    MeasureTheory.IsFundamentalDomain (Gamma S) O (R.sheets.sheet 1) := by
  classical
  have hMP (γ : Gamma S) :
      MeasurePreserving (fun y : S.FS => γ • y)
        (R.sheets.sheet 1) (R.sheets.sheet 1) := po_probe_measurePreserving (R := R) γ
  have hQMP (γ : Gamma S) :
      Measure.QuasiMeasurePreserving (fun y : S.FS => γ • y)
        (R.sheets.sheet 1) (R.sheets.sheet 1) :=
    (hMP γ).quasiMeasurePreserving
  apply MeasureTheory.IsFundamentalDomain.mk''
  · exact hO.1.nullMeasurableSet
  · have hcover : ∀ᵐ y ∂(R.sheets.sheet 1), ∃ γ : Gamma S, γ • y ∈ O := by
      filter_upwards [R.sheets.sheet_support 1 (by norm_num)] with y hy
      let u : S.FSˣ := hy.1.unit
      have hval : (u : S.FS) = y := hy.1.unit_spec
      have hnorm : S.absS (u : S.FS) = 1 := by
        simpa [hval] using hy.2
      obtain ⟨δ, hδ, hδuniq⟩ := hO.2.2 u hnorm
      refine ⟨δ⁻¹, ?_⟩
      have hact : (po_probe_actUnit S (δ⁻¹) : S.FS) * y =
          (((S.diagU (δ.1 : Fˣ))⁻¹ * u : S.FSˣ) : S.FS) := by
        simp [po_probe_actUnit, hval]
      change (po_probe_actUnit S (δ⁻¹) : S.FS) * y ∈ O
      rw [hact]
      exact hδ
    exact hcover
  · intro g hg
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro y hyImage hyO
    obtain ⟨x, hxO, hgy⟩ := hyImage
    let u : S.FSˣ := (hO.2.1 y hyO).1.unit
    have hval : (u : S.FS) = y := (hO.2.1 y hyO).1.unit_spec
    have hnorm : S.absS (u : S.FS) = 1 := (hO.2.1 y hyO).2
    obtain ⟨γ₀, hγ₀, hγ₀uniq⟩ := hO.2.2 u hnorm
    have hOne : ((S.diagU (1 : Fˣ))⁻¹ * u : S.FSˣ).val ∈ O := by
      simpa [u, hval] using hyO
    have hgy' : (po_probe_actUnit S g : S.FS) * x = (u : S.FS) := by
      calc
        (po_probe_actUnit S g : S.FS) * x = y := hgy
        _ = (u : S.FS) := hval.symm
    have hG : ((S.diagU (g.1 : Fˣ))⁻¹ * u : S.FSˣ).val ∈ O := by
      have hInvEq : (po_probe_actUnit S (g⁻¹) : S.FS) * (u : S.FS) = x := by
        rw [← hgy']
        simp [po_probe_actUnit, mul_assoc]
      change ((po_probe_actUnit S (g⁻¹) : S.FSˣ) * u : S.FSˣ).val ∈ O
      have hvalG : ((po_probe_actUnit S (g⁻¹) : S.FSˣ) * u : S.FSˣ).val = x := hInvEq
      rw [hvalG]
      exact hxO
    have hγ₁ : (1 : Gamma S) = γ₀ := hγ₀uniq 1 hOne
    have hγg : g = γ₀ := hγ₀uniq g hG
    have hEq : (1 : Gamma S) = g := hγ₁.trans hγg.symm
    exact hg hEq.symm
  · exact hQMP

/-- `po:probe-well-defined`, 05:82–112. Finiteness means finite support, not `tsum` definedness.
The generator-independence frequency is restricted to `k : S.R` per `sol-thin-a2rp`, since its
residue phase needs integrality. -/
theorem po_probe_well_defined :
  (∀ I (a b : Fˣ), S.IsGen (a : F) I.1 → Bd.Allowed a → S.IsGen (b : F) I.1 → Bd.Allowed b →
    ∀ k : S.R, finiteGaussAt R I a (k : F) = finiteGaussAt R I b (k : F)) ∧
  (∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
    (∀ γ : Gamma S, ∀ t, probeIntegrand R W X Y Z (S.diagU (γ.1 : Fˣ) * t) = probeIntegrand R W X Y Z t) ∧
    (∀ t (s : S.ExtIdeal), (Function.support (fun m : S.R =>
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val))).Finite) ∧
    IntegrableOn (onUnits (probeIntegrand R W X Y Z)) (omegaAt R 1) (R.sheets.sheet 1) ∧
    (∀ O, IsFundamentalAt (S := S) O 1 →
      (∫ y in O, onUnits (probeIntegrand R W X Y Z) y ∂(R.sheets.sheet 1)) = probe R W X Y Z)) ∧
  W.W0 0 = 0 := by
  have hgen :
      (∀ I (a b : Fˣ), S.IsGen (a : F) I.1 → Bd.Allowed a →
        S.IsGen (b : F) I.1 → Bd.Allowed b → ∀ k : S.R,
          finiteGaussAt R I a (k : F) = finiteGaussAt R I b (k : F)) := by
    intro I a b ha haAllowed hb hbAllowed k
    classical
    letI := R.exterior.residueFinite I
    obtain ⟨ε, hε, hrel⟩ :=
      Bd.allowed_unique I.1 a b ⟨ha, haAllowed⟩ ⟨hb, hbAllowed⟩
    let epsUS : S.US := ⟨ε, hε⟩
    let uR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F epsUS
    have huR : ((uR : S.R) : F) = (ε : Fˣ) := by rfl
    have habF : (a : F) = ((ε : Fˣ) : F) ^ 6 * (b : F) := by
      have h := congrArg (fun z : Fˣ => (z : F)) hrel
      simpa using h
    let Q : Type := ResidueRing R.exterior I
    let J : Ideal S.R := Ideal.span {R.exterior.genR I}
    let qMap : S.R →+* Q := Ideal.Quotient.mk J
    let uQ : Qˣ := Units.map qMap uR
    let uQ6 : Qˣ := uQ ^ 6
    let e : Q ≃ Q := {
      toFun x := (uQ6 : Q) * x
      invFun x := ((uQ6⁻¹ : Qˣ) : Q) * x
      left_inv := by intro x; simp [mul_assoc]
      right_inv := by intro x; simp [mul_assoc] }
    let fA : Q → ℂ := fun x =>
      chiIdealPow D I.1 (x.out : F) 1 *
        S.e A (S.diag ((k : F) * (x.out : F) / (a : F)))
    let fB : Q → ℂ := fun x =>
      chiIdealPow D I.1 (x.out : F) 1 *
        S.e A (S.diag ((k : F) * (x.out : F) / (b : F)))
    have hmap (x : Q) :
        Ideal.Quotient.mk J ((uR : S.R) ^ 6 * x.out) = e x := by
      simp [e, uQ6, uQ, qMap, Q]
    have hterm : ∀ x : Q, fA (e x) = fB x := by
      intro x
      dsimp [fA, fB]
      let base : S.R := (uR : S.R) ^ 6 * x.out
      have hclass : Ideal.Quotient.mk J base = e x := by
        simpa [base] using hmap x
      have houtClass : Ideal.Quotient.mk J (e x).out = e x :=
        Ideal.Quotient.mk_out _
      have hbaseOut : Ideal.Quotient.mk J base =
          Ideal.Quotient.mk J (e x).out := hclass.trans houtClass.symm
      have hmem : base - (e x).out ∈ J :=
        (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hbaseOut
      obtain ⟨r₀, hr₀⟩ := Ideal.mem_span_singleton'.mp (by simpa [J] using hmem)
      let r : S.R := -r₀
      have hout : (e x).out = base + R.exterior.genR I * r := by
        dsimp [r]
        calc
          _ = base - (base - (e x).out) := by ring
          _ = base - (r₀ * R.exterior.genR I) := by rw [hr₀]
          _ = base + R.exterior.genR I * (-r₀) := by ring
      have houtF : ((e x).out : F) =
          ((uR : S.R) : F) ^ 6 * (x.out : F) +
            (R.exterior.genR I : F) * (r : F) := by
        have h := congrArg (fun z : S.R => (z : F)) hout
        simpa [base] using h
      have hdiffF : ((e x).out : F) - (base : F) =
          (R.exterior.genR I : F) * (r : F) := by
        have hdiffR : (e x).out - base = R.exterior.genR I * r := by
          rw [hout]
          ring
        exact congrArg (fun z : S.R => (z : F)) hdiffR
      have hbaseF : (base : F) = ((uR : S.R) : F) ^ 6 * (x.out : F) := by
        dsimp [base]
      have hratioR : ((R.exterior.genR I : F) / (a : F)) ∈ S.R :=
        po_gen_ratio_mem_R R I a ha
      let ratioR : S.R := ⟨(R.exterior.genR I : F) / (a : F), hratioR⟩
      let z : S.R := k * ratioR * r
      have hz : (z : F) = (k : F) * (R.exterior.genR I : F) * (r : F) / (a : F) := by
        dsimp [z, ratioR]
        field_simp [a.ne_zero]
      have hvS (v : FinPlace F) (hvI : v.asIdeal ∣ I.1) : v ∉ S.Sf :=
        fun hv => I.2.2 v hv (Ideal.le_of_dvd hvI)
      have hchar : chiIdealPow D I.1 ((e x).out : F) 1 =
          chiIdealPow D I.1 (x.out : F) 1 := by
        calc
          chiIdealPow D I.1 ((e x).out : F) 1 =
              chiIdealPow D I.1 (base : F) 1 := by
                apply po_chiIdealPow_congr I.1 I.2 _ _ ?_
                intro v hvI
                refine ⟨(e x).out.property v (hvS v hvI),
                  base.property v (hvS v hvI), ?_⟩
                rw [hdiffF, map_mul]
                have hgenlt := po_gen_lt_one R I v hvI
                have hrv : HeightOneSpectrum.valuation F v (r : F) ≤ 1 :=
                  r.property v (hvS v hvI)
                calc
                  _ ≤ HeightOneSpectrum.valuation F v (R.exterior.genR I : F) * 1 :=
                    mul_le_mul_of_nonneg_left hrv (by exact zero_le)
                  _ < 1 := by simpa using hgenlt
          _ = chiIdealPow D I.1 (((uR : S.R) : F) ^ 6 * (x.out : F)) 1 := by
                rw [hbaseF]
          _ = chiIdealPow D I.1 (x.out : F) 1 := by
                simpa [huR] using
                  po_chiIdealPow_US_six D S I.1 I.2 epsUS x.out
      have hphaseAlg : (k : F) * ((e x).out : F) / (a : F) =
          (k : F) * (x.out : F) / (b : F) + (k : F) *
            (R.exterior.genR I : F) * (r : F) / (a : F) := by
        rw [houtF, huR, habF]
        field_simp [a.ne_zero, b.ne_zero, (ε : Fˣ).ne_zero]
      have hphaseDiag : S.diag ((k : F) * ((e x).out : F) / (a : F)) =
          S.diag ((k : F) * (x.out : F) / (b : F)) + S.diag (z : F) := by
        rw [hphaseAlg, ← hz]
        exact map_add _ _ _
      have hphase : S.e A (S.diag ((k : F) * ((e x).out : F) / (a : F))) =
          S.e A (S.diag ((k : F) * (x.out : F) / (b : F))) := by
        rw [hphaseDiag, po_e_add S A, po_e_diagR_one S D A z]
        simp
      rw [hchar, hphase]
    change (∑ᶠ x : Q, fA x) = ∑ᶠ x : Q, fB x
    rw [finsum_eq_sum_of_fintype fA, finsum_eq_sum_of_fintype fB]
    exact Fintype.sum_bijective e.symm e.symm.bijective fA fB (by
      intro x
      simpa using hterm (e.symm x))
  constructor
  · exact hgen
  · constructor
    · intro X Y Z hX hY hZ
      have hInvariant :
          (∀ γ : Gamma S, ∀ t : S.FSˣ,
            probeIntegrand R W X Y Z (S.diagU (γ.1 : Fˣ) * t) =
              probeIntegrand R W X Y Z t) := by
        intro γ t
        obtain ⟨eps, heps⟩ := γ.2
        have heps6 : eps ^ 6 = γ.1 := by
          simpa [sixthPowerOnUS] using heps
        let gammaF : Fˣ := (γ.1 : Fˣ)
        have hgammaF : gammaF = (eps : Fˣ) ^ 6 := by
          exact congrArg (fun u : S.US => (u : Fˣ)) heps6.symm
        have hgammaVal (v : FinPlace F) (hv : v ∉ S.Sf) :
            HeightOneSpectrum.valuation F v (gammaF : F) = 1 :=
          (γ.1).property v hv
        have hdiagGamma : S.diagU gammaF ∈
            (powMonoidHom 6 : S.FSˣ →* S.FSˣ).range := by
          refine ⟨S.diagU (eps : Fˣ), ?_⟩
          calc
            (S.diagU (eps : Fˣ)) ^ 6 = S.diagU ((eps : Fˣ) ^ 6) := by simp
            _ = S.diagU gammaF := by rw [← hgammaF]
        have hquotGamma : (QuotientGroup.mk (S.diagU gammaF) : S.V) = 1 :=
          (QuotientGroup.eq_one_iff _).2 hdiagGamma
        have hallowedDiv (a : Fˣ) (ha : Bd.Allowed a) :
            Bd.Allowed (a / gammaF) := by
          have hclass : (QuotientGroup.mk (S.diagU (a / gammaF)) : S.V) =
              QuotientGroup.mk (S.diagU a) := by
            simp [map_div, hquotGamma]
          change (QuotientGroup.mk (S.diagU (a / gammaF)) : S.V) ∈ Bd.B
          rw [hclass]
          exact ha
        have hgenDiv (s : S.ExtIdeal) (a : Fˣ)
            (ha : S.IsGen (a : F) s.1) : S.IsGen ((a / gammaF : Fˣ) : F) s.1 := by
          refine ⟨ha.1, (a / gammaF).ne_zero, ?_⟩
          intro v hv
          have hcountGamma : FractionalIdeal.count F v
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (gammaF : F)) = 0 := by
            rw [po_count_spanSingleton_eq_neg_log_valuation v (gammaF : F) gammaF.ne_zero,
              hgammaVal v hv]
            simp
          have hcount := po_count_spanSingleton_div v (a : F) (gammaF : F)
            ha.2.1 gammaF.ne_zero
          rw [ha.2.2 v hv, hcountGamma] at hcount
          simpa using hcount
        have hgaussScale (s : S.ExtIdeal) (m : S.R) :
            finiteGauss R s (-((gammaF : F) * (m : F))) =
              finiteGaussAt R s (bc.gen s / gammaF) (-(m : F)) := by
          letI := R.exterior.residueFinite s
          unfold finiteGauss finiteGaussAt
          apply finsum_congr
          intro x
          have harg :
              (-((gammaF : F) * (m : F))) * (x.out : F) / (bc.gen s : F) =
                (-(m : F)) * (x.out : F) / ((bc.gen s / gammaF : Fˣ) : F) := by
            simp only [Units.val_div_eq_div_val]
            field_simp [gammaF.ne_zero, (bc.gen s).ne_zero]
          rw [harg]
        have hgaussInv (s : S.ExtIdeal) (m : S.R) :
            finiteGauss R s (-((gammaF : F) * (m : F))) =
              finiteGauss R s (-(m : F)) := by
          calc
            finiteGauss R s (-((gammaF : F) * (m : F))) =
                finiteGaussAt R s (bc.gen s / gammaF) (-(m : F)) := hgaussScale s m
            _ = finiteGaussAt R s (bc.gen s) (-(m : F)) :=
              hgen s (bc.gen s / gammaF) (bc.gen s)
                (hgenDiv s (bc.gen s) (bc.gen_spec s).1)
                (hallowedDiv (bc.gen s) (bc.gen_spec s).2)
                (bc.gen_spec s).1 (bc.gen_spec s).2 (-m : S.R)
            _ = finiteGauss R s (-(m : F)) := rfl
        have hBmInv (m : S.R) :
            Bm D S A ϑ (cgen R) ((gammaF : F) * (m : F)) Z =
              Bm D S A ϑ (cgen R) (m : F) Z := by
          unfold Bm
          apply tsum_congr
          intro p
          have hAext : S.IsExterior (p.1.1 * p.2.1 ^ 3) := by
            simpa [Aideal, R.exterior.mul_val, R.exterior.ofSqf_val,
              R.exterior.pow_val] using (Aideal R p.1 p.2).2
          have hchi : chiIdealPow D (p.1.1 * p.2.1 ^ 3)
              ((gammaF : F) * (m : F)) 1 =
                chiIdealPow D (p.1.1 * p.2.1 ^ 3) (m : F) 1 := by
            rw [hgammaF]
            exact po_chiIdealPow_US_six D S (p.1.1 * p.2.1 ^ 3) hAext eps m
          rw [hchi]
        let gammaR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F γ.1
        have hgammaR : ((gammaR : S.R) : F) = (gammaF : F) := by rfl
        let em : S.R ≃ S.R := {
          toFun m := (gammaR : S.R) * m
          invFun m := ((gammaR⁻¹ : S.Rˣ) : S.R) * m
          left_inv := by intro m; simp [mul_assoc]
          right_inv := by intro m; simp [mul_assoc] }
        have hdiagGammaVal : S.diag (gammaF : F) = (S.diagU gammaF : S.FS) := by rfl
        have hWarg (s : S.ExtIdeal) (m : S.R) :
            S.diag ((gammaF : F) * (m : F)) *
                (((S.diagU gammaF * t) * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val =
              S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val := by
          calc
            _ = (S.diagU gammaF : S.FS) * S.diag (m : F) *
                (((S.diagU gammaF * t) * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val := by
                  rw [map_mul, hdiagGammaVal]
            _ = _ := by simp [mul_assoc, mul_left_comm, mul_comm]
        let fLeft (s : S.ExtIdeal) (m : S.R) : ℂ :=
          (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m : F)) *
            W.W0 (S.diag (m : F) *
              (((S.diagU gammaF * t) * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
            Bm D S A ϑ (cgen R) (m : F) Z
        let fRight (s : S.ExtIdeal) (m : S.R) : ℂ :=
          (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m : F)) *
            W.W0 (S.diag (m : F) *
              ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
            Bm D S A ϑ (cgen R) (m : F) Z
        have htermSum (s : S.ExtIdeal) (m : S.R) :
            fLeft s (em m) = fRight s m := by
          dsimp [fLeft, fRight]
          have hGauss : finiteGauss R s (-((em m : S.R) : F)) =
              finiteGauss R s (-(m : F)) := by
            simpa [em, hgammaR] using hgaussInv s m
          have hB : Bm D S A ϑ (cgen R) ((em m : S.R) : F) Z =
              Bm D S A ϑ (cgen R) (m : F) Z := by
            simpa [em, hgammaR] using hBmInv m
          have hargW : S.diag ((em m : S.R) : F) *
                (((S.diagU gammaF * t) * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val =
              S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val := by
            simpa [em, hgammaR] using hWarg s m
          rw [hGauss, hargW, hB]
        have hinner (s : S.ExtIdeal) :
            (∑' m : S.R, fLeft s m) = ∑' m : S.R, fRight s m := by
          calc
            _ = ∑' m : S.R, fLeft s (em m) := (em.tsum_eq (fun m => fLeft s m)).symm
            _ = _ := tsum_congr (htermSum s)
        unfold probeIntegrand
        apply congrArg (fun z : ℂ => (Y : ℂ)⁻¹ * z)
        apply tsum_congr
        intro s
        rw [hinner s]
      constructor
      · exact hInvariant
      · constructor
        · intro t s
          exact po_probe_row_support_finite R W X t s
        · constructor
          · have hOuterSupport :
                (Function.support (fun s : S.ExtIdeal => W.W1 (qI s.1 / Y))).Finite := by
              classical
              have hcompact : IsCompact (tsupport W.W1) := W.W1_compact
              obtain ⟨B, hB⟩ :=
                (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcompact.isBounded
              let cutoff : ℝ := Y * max B 1
              have hcutoff : 0 ≤ cutoff := by dsimp [cutoff]; positivity
              have hfinite := a2_bridge_COUNT_finite S cutoff hcutoff
              apply hfinite.1.subset
              intro I hI
              have hts : qI I.1 / Y ∈ tsupport W.W1 := by
                apply subset_closure
                exact Function.mem_support.mpr hI
              have hball := hB hts
              have hdist : dist (qI I.1 / Y) 0 ≤ B := by
                simpa only [Metric.mem_closedBall, dist_zero_right] using hball
              have hfrac : qI I.1 / Y ≤ max B 1 := by
                calc
                  qI I.1 / Y ≤ |qI I.1 / Y| := le_abs_self _
                  _ = dist (qI I.1 / Y) 0 := by
                    simpa only [sub_zero] using (Real.dist_eq (qI I.1 / Y) 0).symm
                  _ ≤ B := hdist
                  _ ≤ max B 1 := le_max_left _ _
              have hq : qI I.1 ≤ cutoff := by
                dsimp [cutoff]
                calc
                  qI I.1 ≤ max B 1 * Y := (div_le_iff₀ hY).mp hfrac
                  _ = Y * max B 1 := by ring
              simpa [qI, idealNorm] using hq
            let Sfin : Finset S.ExtIdeal := hOuterSupport.toFinset
            obtain ⟨K0, hK0, hOmegaK⟩ := R.sheets.omega_bounded
            have hOmegaClosureK : closure R.sheets.omega ⊆ K0 :=
              closure_minimal hOmegaK hK0.isClosed
            let OmegaClosure : Set S.FS := closure R.sheets.omega
            have hOmegaClosureCompact : IsCompact OmegaClosure :=
              hK0.of_isClosed_subset isClosed_closure hOmegaClosureK
            have hOmegaClosureNorm : ∀ y ∈ OmegaClosure, S.absS y = 1 := by
              have hclosed : IsClosed {y : S.FS | S.absS y = 1} :=
                isClosed_singleton.preimage (po_absS_continuous S)
              have hsub : R.sheets.omega ⊆ {y : S.FS | S.absS y = 1} := by
                intro y hy
                exact (R.sheets.omega_norm y hy).2
              exact closure_minimal hsub hclosed
            let a0 : S.FSˣ := R.sheets.ellU 1
            let Kdom : Set S.FS := (fun y : S.FS => (a0 : S.FS) * y) '' OmegaClosure
            have hKdom : IsCompact Kdom := by
              change IsCompact ((fun y : S.FS => (a0 : S.FS) * y) '' OmegaClosure)
              exact hOmegaClosureCompact.image (continuous_const.mul continuous_id)
            have hKdomUnit : ∀ y ∈ Kdom, IsUnit y := by
              intro y hy
              rcases hy with ⟨x, hx, rfl⟩
              exact a0.isUnit.mul (po_absS_one_isUnit S x (hOmegaClosureNorm x hx))
            have hOmegaAtK : omegaAt R 1 ⊆ Kdom := by
              intro y hy
              rcases hy with ⟨x, hx, rfl⟩
              exact ⟨x, subset_closure hx, rfl⟩
            let rowFin : S.ExtIdeal → Finset S.R := fun s =>
              (po_probe_rows_on_compact R W X s Kdom hKdom).toFinset
            let innerTerm (s : S.ExtIdeal) (u : S.FSˣ) (m : S.R) : ℂ :=
              (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m : F)) *
                W.W0 (S.diag (m : F) *
                  ((u * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
                Bm D S A ϑ (cgen R) (m : F) Z
            let outerTerm (u : S.FSˣ) (s : S.ExtIdeal) : ℂ :=
              W.W1 (qI s.1 / Y) * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
                ∑' m : S.R, innerTerm s u m
            let outerFiniteTerm (u : S.FSˣ) (s : S.ExtIdeal) : ℂ :=
              W.W1 (qI s.1 / Y) * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
                ∑ m ∈ rowFin s, innerTerm s u m
            let approxUnit (u : S.FSˣ) : ℂ :=
              (Y : ℂ)⁻¹ * ∑ s ∈ Sfin, outerFiniteTerm u s
            have hrowMem (s : S.ExtIdeal) (u : S.FSˣ)
                (hu : (u : S.FS) ∈ Kdom) (m : S.R)
                (hm : W.W0 (S.diag (m : F) *
                  ((u * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) ≠ 0) :
                m ∈ rowFin s := by
              apply (po_probe_rows_on_compact R W X s Kdom hKdom).mem_toFinset.mpr
              exact ⟨u, hu, hm⟩
            have hInnerTrunc (s : S.ExtIdeal) (u : S.FSˣ)
                (hu : (u : S.FS) ∈ Kdom) :
                (∑' m : S.R, innerTerm s u m) = ∑ m ∈ rowFin s, innerTerm s u m := by
              apply tsum_eq_sum
              intro m hm
              by_cases hW : W.W0 (S.diag (m : F) *
                  ((u * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) = 0
              · change innerTerm s u m = 0
                dsimp [innerTerm]
                rw [hW]
                simp
              · exact (hm (hrowMem s u hu m hW)).elim
            have hOuterTrunc (u : S.FSˣ) :
                (∑' s : S.ExtIdeal, outerTerm u s) = ∑ s ∈ Sfin, outerTerm u s := by
              apply tsum_eq_sum
              intro s hs
              by_cases hW : W.W1 (qI s.1 / Y) = 0
              · simp [outerTerm, hW]
              · have hmem : s ∈ Sfin :=
                  hOuterSupport.mem_toFinset.mpr (Function.mem_support.mpr hW)
                exact (hs hmem).elim
            have hOuterFinCong (u : S.FSˣ) (hu : (u : S.FS) ∈ Kdom) :
                (∑ s ∈ Sfin, outerTerm u s) = ∑ s ∈ Sfin, outerFiniteTerm u s := by
              apply Finset.sum_congr rfl
              intro s hs
              simp only [outerTerm, outerFiniteTerm]
              rw [hInnerTrunc s u hu]
            have hApproxEq (u : S.FSˣ) (hu : (u : S.FS) ∈ Kdom) :
                probeIntegrand R W X Y Z u = approxUnit u := by
              change (Y : ℂ)⁻¹ * (∑' s : S.ExtIdeal, outerTerm u s) = approxUnit u
              rw [hOuterTrunc u, hOuterFinCong u hu]

            have hW0cont : Continuous W.W0 := po_probe_weight_continuous W
            have hWtermCont (s : S.ExtIdeal) (m : S.R) :
                Continuous (fun u : S.FSˣ => W.W0 (S.diag (m : F) *
                  ((u * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val)) := by
              have hInv : Continuous (fun u : S.FSˣ =>
                  (u * R.sheets.ellU (qI s.1 * X))⁻¹) :=
                continuous_inv.comp (continuous_id.mul continuous_const)
              have hvalInv : Continuous (fun u : S.FSˣ =>
                  (((u * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ) : S.FS)) :=
                Units.continuous_val.comp hInv
              exact hW0cont.comp (continuous_const.mul hvalInv)
            have hInnerCont (s : S.ExtIdeal) :
                Continuous (fun u : S.FSˣ => ∑ m ∈ rowFin s, innerTerm s u m) := by
              apply continuous_finsetSum (rowFin s)
              intro m hm
              dsimp [innerTerm]
              exact ((continuous_const.mul continuous_const).mul (hWtermCont s m)).mul
                continuous_const
            have hOuterFiniteCont :
                Continuous (fun u : S.FSˣ => ∑ s ∈ Sfin, outerFiniteTerm u s) := by
              apply continuous_finsetSum Sfin
              intro s hs
              dsimp [outerFiniteTerm]
              exact (continuous_const.mul continuous_const).mul (hInnerCont s)
            have hApproxCont : Continuous approxUnit := by
              dsimp [approxUnit]
              exact continuous_const.mul hOuterFiniteCont
            let KdomUnits := {y : S.FS // y ∈ Kdom}
            let unitLift : KdomUnits → S.FSˣ :=
              fun y => (hKdomUnit y.1 y.2).unit
            have hvalLift : Continuous (fun y : KdomUnits => (unitLift y : S.FS)) := by
              convert continuous_subtype_val using 1
              funext y
              exact (hKdomUnit y.1 y.2).unit_spec
            have hRingInvK : ContinuousOn (fun y : S.FS => Ring.inverse y) Kdom := by
              have hfin (v : S.Sf) :
                  ContinuousOn (fun y : S.FS => (Ring.inverse y).1 v) Kdom := by
                have hcoord : ContinuousOn (fun y : S.FS => y.1 v) Kdom :=
                  ((continuous_apply v).comp continuous_fst).continuousOn
                have hnz : ∀ y ∈ Kdom, y.1 v ≠ 0 := by
                  intro y hy
                  have hu := hKdomUnit y hy
                  exact (Pi.isUnit_iff.mp (Prod.isUnit_iff.mp hu).1 v).ne_zero
                have hcoordInv : ContinuousOn (fun y : S.FS => (y.1 v)⁻¹) Kdom :=
                  hcoord.inv₀ hnz
                apply hcoordInv.congr
                intro y hy
                simp [Ring.inverse, hKdomUnit y hy]
              have harch (w : InfinitePlace F) :
                  ContinuousOn (fun y : S.FS => (Ring.inverse y).2 w) Kdom := by
                have hcoord : ContinuousOn (fun y : S.FS => y.2 w) Kdom :=
                  ((continuous_apply w).comp continuous_snd).continuousOn
                have hnz : ∀ y ∈ Kdom, y.2 w ≠ 0 := by
                  intro y hy
                  have hu := hKdomUnit y hy
                  exact (Pi.isUnit_iff.mp (Prod.isUnit_iff.mp hu).2 w).ne_zero
                have hcoordInv : ContinuousOn (fun y : S.FS => (y.2 w)⁻¹) Kdom :=
                  hcoord.inv₀ hnz
                apply hcoordInv.congr
                intro y hy
                simp [Ring.inverse, hKdomUnit y hy]
              exact (continuousOn_pi.2 hfin).prodMk (continuousOn_pi.2 harch)
            have hInvLift : Continuous (fun y : KdomUnits =>
                (((unitLift y)⁻¹ : S.FSˣ) : S.FS)) := by
              have hcont :=
                (continuousOn_iff_continuous_domRestrict).mp hRingInvK
              convert hcont using 1
              funext y
              change (((unitLift y)⁻¹ : S.FSˣ) : S.FS) = Ring.inverse y.1
              rw [Ring.inverse_of_isUnit (hKdomUnit y.1 y.2)]
            have hUnitLiftCont : Continuous unitLift :=
              Units.continuous_iff.mpr ⟨hvalLift, hInvLift⟩
            have hRestrictedCont :
                Continuous (fun y : KdomUnits => onUnits (probeIntegrand R W X Y Z) y.1) := by
              convert hApproxCont.comp hUnitLiftCont using 1
              funext y
              have hunit := hKdomUnit y.1 y.2
              have hval : (unitLift y : S.FS) = y.1 := hunit.unit_spec
              have hEq := hApproxEq (unitLift y) (by simpa [hval] using y.2)
              simpa [onUnits, unitLift, hunit] using hEq
            have hRestrictedContOn :
                ContinuousOn (onUnits (probeIntegrand R W X Y Z)) Kdom :=
              (continuousOn_iff_continuous_domRestrict).2 hRestrictedCont
            have hSheet := a2_bridge_SHEET R.sheets 1 (by norm_num)
            have hOmegaMeas : MeasurableSet (omegaAt R 1) := by
              simpa [omegaAt, bridgeOmegaAt] using hSheet.1.1
            have hOmegaMeasure : R.sheets.sheet 1 (omegaAt R 1) ≠ ⊤ := by
              have hlt : R.sheets.sheet 1 (bridgeOmegaAt R.sheets 1) < ⊤ := hSheet.2.1
              simpa [omegaAt, bridgeOmegaAt] using ne_of_lt hlt
            exact hRestrictedContOn.integrableOn_of_subset_isCompact
              hKdom hOmegaMeas hOmegaAtK hOmegaMeasure
          · intro O hO
            classical
            let actUnit : Gamma S →* S.FSˣ := po_probe_actUnit S
            have hSheet := a2_bridge_SHEET R.sheets 1 (by norm_num)
            have hfd (E : Set S.FS) (hE : IsFundamentalAt (S := S) E 1) :
                MeasureTheory.IsFundamentalDomain (Gamma S) E (R.sheets.sheet 1) :=
              po_probe_fundamentalDomain (R := R) E hE
            have hOmegaFund : IsFundamentalAt (S := S) (omegaAt R 1) 1 := by
              exact hSheet.1
            have hInvOnUnits (γ : Gamma S) (y : S.FS) :
                onUnits (probeIntegrand R W X Y Z) (γ • y) =
                  onUnits (probeIntegrand R W X Y Z) y := by
              change onUnits (probeIntegrand R W X Y Z) ((actUnit γ : S.FS) * y) =
                onUnits (probeIntegrand R W X Y Z) y
              by_cases hy : IsUnit y
              · let u : S.FSˣ := hy.unit
                have hval : (u : S.FS) = y := hy.unit_spec
                have hmul : IsUnit ((actUnit γ : S.FS) * y) := (actUnit γ).isUnit.mul hy
                have hmulVal : hmul.unit = actUnit γ * u := by
                  apply Units.ext
                  simp [hval]
                calc
                  onUnits (probeIntegrand R W X Y Z) ((actUnit γ : S.FS) * y) =
                      probeIntegrand R W X Y Z (actUnit γ * u) := by
                        simp [onUnits, hmul, hmulVal]
                  _ = probeIntegrand R W X Y Z u := by
                        simpa [actUnit, po_probe_actUnit] using hInvariant γ u
                  _ = onUnits (probeIntegrand R W X Y Z) y := by
                        simp [onUnits, hy, u]
              · have hmul : ¬ IsUnit ((actUnit γ : S.FS) * y) := by
                  intro h
                  exact hy ((actUnit γ).isUnit.mul_left_iff.mp h)
                simp [onUnits, hy, hmul]
            letI : Countable (Gamma S) := hSheet.2.2
            have hIntegralEq :=
              (hfd O hO).setIntegral_eq (hfd (omegaAt R 1) hOmegaFund) hInvOnUnits
            calc
              (∫ y in O, onUnits (probeIntegrand R W X Y Z) y ∂(R.sheets.sheet 1)) =
                  ∫ y in omegaAt R 1,
                    onUnits (probeIntegrand R W X Y Z) y ∂(R.sheets.sheet 1) := hIntegralEq
              _ = probe R W X Y Z := by rfl
    · exact po_probe_weight_zero W
/-- Corrected `prop:probe-low` consumer, `sol-gate-a2b` (05:194–246): the legacy reflection
route receives the split Gauss characters, including the angular datum used by the admissible
row-character producer. -/
def probeLowStatement (η : HeckeChar F) : Prop :=
  GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
    ‖probe R W (Z ^ a) (Z ^ b) Z‖ ≤ C * Z ^ (933 / 2000 + ε)

/-- `prop:probe-low`, 05:194–246, with the corrected split-character input from `sol-gate-a2b`. -/
theorem prop_probe_low (η : HeckeChar F)
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
    ‖probe R W (Z ^ a) (Z ^ b) Z‖ ≤ C * Z ^ (933 / 2000 + ε) := by
  sorry
/-- po:finite-poisson-transform, 05:267–282: no coprimality hypothesis on s,I. -/
theorem po_finite_poisson_transform : ∀ (s I : S.ExtIdeal) (a : Fˣ),
  S.IsGen (a : F) I.1 → Bd.Allowed a → ∀ h : S.R,
    (∑ᶠ m : ResidueRing R.exterior (R.exterior.mul s I),
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m.out : F)) *
        chiIdealPow D I.1 (m.out : F) 1 *
          S.e A (S.diag ((h : F) * (m.out : F) / ((bc.gen s : F) * (a : F))))) =
      (qI s.1 ^ (1 / 2 : ℝ) : ℝ) * finiteFactor R s I a (h : F) ∧
    ‖finiteFactor R s I a (h : F)‖ ≤ qI s.1 * qI I.1 ∧
    ∀ γ : Gamma S, finiteFactor R s I a (((γ.1 : Fˣ) : F) * (h : F)) = finiteFactor R s I a (h : F) := by
  sorry
variable (η : HeckeChar F) (U : FrequencyData S D η)
def poissonOrbitTerm (X Y Z : ℝ)
    (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) : ℂ :=
  let c := p.1
  let n := p.2.1
  let s := p.2.2.1
  let u := p.2.2.2.1
  let r := p.2.2.2.2
  gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
    (qI c.1 ^ (-(1 / 2 : ℝ)) / qI n.1 / qI (Aideal R c n).1 : ℝ) *
      (PG (qI (Aideal R c n).1 / Z) : ℂ) * W.W1 (qI s.1 / Y) *
        finiteFactor R s (Aideal R c n) (Agen R c n) ((U.repr u : F) * (bc.gen r : F) ^ 6) *
          weightV0 R sd W (X * U.q u * qI r.1 ^ 6 / qI (Aideal R c n).1)

/-- Vertical integrals include the 1/(2π) after parametrizing s=σ+it. -/
def vertical (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (σ + t * Complex.I)
def tripleVertical (σξ σw σz : ℝ) (f : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  vertical σξ (fun ξ => vertical σw (fun w => vertical σz (fun z => f ξ w z)))
/-- po:poisson-orbits, 05:284–350, including the V₀ Mellin dictionary. -/
theorem po_poisson_orbits : WeightSpec R sd W →
  (ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weightV0 R sd W) (Set.Ioi 0)) ∧
  (∀ z : ℂ, 0 < z.re → mellin (weightV0 R sd W) z = weightM R sd W z) ∧
  (∀ σ T : ℝ, 0 < σ → 0 < T →
    weightV0 R sd W T = vertical σ (fun z => weightM R sd W z * (T : ℂ) ^ (-z))) ∧
  ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
    Summable (fun p => ‖poissonOrbitTerm R sd W η U X Y Z p‖) ∧
    probe R W X Y Z = ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) * ∑' p, poissonOrbitTerm R sd W η U X Y Z p := by
  sorry
/-- def:calF within po:mellin-triple, 05:353–389; all four ideal indices are actual exterior ideals. -/
def calFTerm (u : U.U) (ξ w z : ℂ) (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal) : ℂ :=
  let c := p.1
  let n := p.2.1
  let s := p.2.2.1
  let r := p.2.2.2
  gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
    finiteFactor R s (Aideal R c n) (Agen R c n) ((U.repr u : F) * (bc.gen r : F) ^ 6) *
      (qI c.1 : ℂ) ^ (-1 / 2 - ξ) * (qI n.1 : ℂ) ^ (-1 - 3 * ξ) *
        (qI s.1 : ℂ) ^ (-w) * (qI r.1 : ℂ) ^ (-6 * z)
def calF (u : U.U) (ξ w z : ℂ) : ℂ := ∑' p, calFTerm R η U u ξ w z p

def mellinWeight (X Y Z : ℝ) (ξ w z : ℂ) : ℂ :=
  (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w

/-- po:mellin-triple, 05:353–389. `Summable` prevents interpreting a divergent total tsum as 0. -/
theorem po_mellin_triple : WeightSpec R sd W → ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
  (∀ ξ w z : ℂ, ξ.re = 4 → w.re = 4 → z.re = 2 →
    (∀ u, Summable (fun p => ‖calFTerm R η U u ξ w z p‖)) ∧
      Summable (fun u => ‖(U.q u : ℂ) ^ (-z) * calF R η U u ξ w z‖)) ∧
  Integrable (fun t : ℝ × ℝ × ℝ =>
    mellinWeight R sd W X Y Z (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) *
      ∑' u, (U.q u : ℂ) ^ (-(2 + t.2.2 * Complex.I)) * calF R η U u
        (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)) ∧
  probe R W X Y Z = tripleVertical 4 4 2 (fun ξ w z =>
    mellinWeight R sd W X Y Z ξ w z * ∑' u, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z) := by
  sorry
/-- Stripped local C uses the negative exterior additive sign (05:444–550). -/
def localC (v : FinPlace F) (hv : v ∉ S.Sf) (t k J : ℕ) : ℂ :=
  let pi := R.exterior.prime v hv
  ∑ᶠ d : ResidueRing R.exterior (R.exterior.pow pi k),
    if ∃ x : S.R, (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
      (primeGen R v : F) ^ k * (x : F) then
      (if k = 0 then 1 else chiPow D v (d.out : F) k) *
      ∑ᶠ x : ResidueRing R.exterior (R.exterior.pow pi t),
        (if t = 0 then 1 else chiPow D v (x.out : F) t) * A.ψ v (algebraMap F _
          (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F)) *
            (x.out : F) / (primeGen R v : F) ^ (k + t))))
    else 0

def localT (v : FinPlace F) (e : ℤ) (y : F) : ℂ :=
  ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) e *
    A.ψ v (algebraMap F _ (-(y * algebraMap (𝓞 F) F x.out / (primeGen R v : F))))

/-- po:C-local-values, 05:552–595. At J=t-1 use J+1-t, not saturated J-t+1. -/
theorem po_C_local_values : ∀ v (hv : v ∉ S.Sf) J,
  localC R v hv 0 0 J = 1 ∧
  (∀ k : ℕ, 0 < k → localC R v hv 0 k J = if J = 0 then 1 else 0) ∧
  (∀ t : ℕ, 0 < t →
    localC R v hv t 0 J = (if t - 1 ≤ J then
      (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v t ((primeGen R v : F) ^ (J + 1 - t)) else 0) ∧
    localC R v hv t 1 J = (if t ≤ J then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
      localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (J - t)) else 0) ∧
    (∀ k : ℕ, 2 ≤ k → localC R v hv t k J = 0) ∧
    ‖localC R v hv t 0 J‖ ≤ qI v.asIdeal ^ (t : ℝ) ∧
    ‖localC R v hv t 1 J‖ ≤ qI v.asIdeal ^ ((t : ℝ) + 1 / 2)) := by
  sorry
def frequencyValuation (u : U.U) (v : FinPlace F) : ℕ :=
  (FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F))).toNat

def localEulerTerm (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  let e := i.1.1
  let l := i.2.1
  let k := i.2.2.1
  let m := i.2.2.2
  let j := frequencyValuation η U u v
  gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e * ϑ.primeValue v ^ (e + 3 * l) *
    chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^ ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
      localC R v hv (e + 3 * l) k (j + 6 * m) *
        (qI v.asIdeal : ℂ) ^ (-(e : ℂ) * (1 / 2 + ξ) - (l : ℂ) * (1 + 3 * ξ) - (k : ℂ) * w - 6 * (m : ℂ) * z)

def localEuler (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ) : ℂ :=
  ∑' i, localEulerTerm R η U u v hv ξ w z i

def initialRegion (ξ w z : ℂ) : Prop := 3 / 2 < ξ.re ∧ 2 < w.re ∧ 1 / 6 < z.re

/-- po:euler-local-factorization, 05:444–550. Product convergence uses HasProd, never finprod. -/
theorem po_euler_local_factorization : ∀ u ξ w z, initialRegion ξ w z →
  Summable (fun p => ‖calFTerm R η U u ξ w z p‖) ∧
  (∀ v hv, Summable (fun i => ‖localEulerTerm R η U u v hv ξ w z i‖)) ∧
  HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} => localEuler R η U u v.1 v.2 ξ w z) (calF R η U u ξ w z) := by
  sorry
/-- Exact arithmetic input from A1 gauss-characters/vartheta-S, including finite order of η. -/
def EulerHypotheses : Prop := IsOfFinOrder η ∧ (∀ v, v ∉ S.Sf → η.UnramifiedAt v) ∧
  ∀ v, v ∉ S.Sf → gamma D S A 1 v.asIdeal (primeGen R v : F) *
    gamma D S A 2 v.asIdeal (primeGen R v : F) * ϑ.primeValue v = -η.primeValue v

def localV (v : FinPlace F) (z : ℂ) : ℂ := (qI v.asIdeal : ℂ) ^ (-6 * z)
def localWvar (u : U.U) (v : FinPlace F) (w : ℂ) : ℂ := chi D v (U.repr u : F) * (qI v.asIdeal : ℂ) ^ (-w)
def localDvar (u : U.U) (v : FinPlace F) (ξ : ℂ) : ℂ :=
  η.primeValue v * star (chi D v (U.repr u : F)) * (qI v.asIdeal : ℂ) ^ (-ξ)
def localEvar (v : FinPlace F) (ξ z : ℂ) : ℂ :=
  ϑ.primeValue v ^ 6 * (qI v.asIdeal : ℂ) ^ (4 - 6 * ξ) * localV v z

def normalizedLocal (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ) : ℂ :=
  (1 - localV v z) * (1 - localWvar η U u v w) / (1 - localDvar η U u v ξ) *
    localEuler R η U u v hv ξ w z

/-- po:euler-good-closed, 05:596-659. The zero-valuation local series is the frozen closed factor. -/
theorem po_euler_good_closed : EulerHypotheses R η → ∀ u v hv ξ w z, initialRegion ξ w z → frequencyValuation η U u v = 0 →
  localEuler R η U u v hv ξ w z = eulerGoodClosed (qI v.asIdeal) (localV v z)
    (localWvar η U u v w) (localDvar η U u v ξ) (localEvar (ϑ := ϑ) v ξ z) := by
  sorry
abbrev Triple := Fin 3 → ℂ

def eulerNeighborhood (p : Triple) : Prop :=
  (998 / 1000 - 1 / 100000 < (p 0).re ∧ 3 / 1000 - 1 / 100000 < (p 1).re ∧
    4 / 10 - 1 / 100000 < (p 2).re) ∨
  (998 / 1000 - 1 / 100000 < (p 0).re ∧ 95 / 100 - 1 / 100000 < (p 1).re ∧
    16 / 100 - 1 / 100000 < (p 2).re)

/-- po:H-local-bounds, 05:660–729, for supplied numerical constants. The separate absolute
uniformity obligation below places those constants before all arithmetic data. -/
def HasPoHLocalBounds (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (η : HeckeChar F) (U : FrequencyData S D η) (C Q0 : ℝ) : Prop :=
  0 < C ∧ 1 < Q0 ∧ ∀ u v hv p,
  Q0 < qI v.asIdeal → eulerNeighborhood p →
  Summable (fun i => ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖) ∧
  ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
    C * qI v.asIdeal ^ (if frequencyValuation η U u v = 0 then (-1 - 1 / 4000 : ℝ) else (-1 / 4000 : ℝ))

/-- Corrected by `sol-gate-a2b`: the constants are outputs of the local estimate, not arbitrary
inputs (`po:H-local-bounds`, 05:660–729). -/
theorem po_H_local_bounds :
  EulerHypotheses R η → ∃ C Q0 : ℝ, 0 < C ∧ 1 < Q0 ∧ HasPoHLocalBounds R η U C Q0 := by
  sorry
/-- H_u is a proposed limit object; its HasProd law is an explicit node conclusion below. -/
structure EulerCorrection (η : HeckeChar F) (U : FrequencyData S D η) where
  H : U.U → Triple → ℂ
  H_eq : ∀ u p, H u p = ∏' v : {v : FinPlace F // v ∉ S.Sf},
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)

variable (HC : EulerCorrection R η U)
def Heta (s : ℂ) : ℂ := HC.H U.one ![s, 1, 1 / 6]

/-- po:H-product, 05:731–755: normal convergence and holomorphy in three complex variables. -/
def HasPoHProduct (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (HC : EulerCorrection R η U) : Prop :=
  (∀ u p, eulerNeighborhood p →
    HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} =>
      normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) (HC.H u p)) ∧
  (∀ u, DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p}) ∧
  (∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
    ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F), V ⊆ V' →
      ∀ p ∈ K, ‖(∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
        normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) - HC.H u p‖ < ε) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ u p, eulerNeighborhood p → ‖HC.H u p‖ ≤ C * U.q u ^ ε

theorem po_H_product : EulerHypotheses R η → HasPoHProduct R η U HC := by
  sorry
variable (HA : HeckeAnalysis F)
/-- prop:euler-product, 05:407–433: analytic continuations, masked exterior values retained. -/
theorem prop_euler_product : EulerHypotheses R η →
  HasPoHProduct R η U HC ∧ (∀ u ξ w z, initialRegion ξ w z →
    calF R η U u ξ w z = HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
      HA.LS S (η * (U.kummer u)⁻¹) ξ) ∧
  ((∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
      ∀ p, eulerNeighborhood p → HC.H U.one p ≠ 0) := by
  sorry
/-- def:po-H-eta, 05:757–765: the larger open half-plane includes the closed .998 boundary. -/
theorem po_H_eta_properties : EulerHypotheses R η →
  (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
  DifferentiableOn ℂ (Heta R η U HC) {s | 998 / 1000 - 1 / 100000 < s.re} ∧
  (∀ s, 998 / 1000 - 1 / 100000 < s.re → Heta R η U HC s ≠ 0) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ s, 998 / 1000 - 1 / 100000 < s.re → ‖Heta R η U HC s‖ ≤ C := by
  sorry
end Poisson


section PoissonSupplementary
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
/-- po:weights-exist: local absolute weighted derivatives (05:56–65). -/
theorem po_weights_local_integrability :
  (∀ v : S.Sf, ∀ σ : ℝ, 0 < σ → Integrable (fun y =>
    ‖∫ x, (W.finite v).1 x * A.ψ v.1 (-(x * y)) ∂(μ v.1).μ‖ * absFin v.1 y ^ σ)
      (Theta.mulHaarFin (μ v.1))) ∧
  ∀ w : InfinitePlace F, ∀ j : ℕ, ∀ σ : ℝ, 0 < σ →
    Integrable (fun y : ℂ => ‖normDeriv j (fun y => ∫ x : ℂ, W.arch w x * psiC (-(x * y))) y‖ *
      Complex.normSq y ^ σ) Theta.mulHaarC := by
  sorry
/-- po:probe-well-defined: finite outer support and absolute B_m series for every row. -/
theorem po_probe_absolute : ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
  (Function.support (fun I : S.ExtIdeal => W.W1 (qI I.1 / Y))).Finite ∧
  (∀ m : S.R, Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
    ‖gamma D S A 2 p.1.1 (cgen R p.1) * (qI p.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.1 : ℝ) *
      ϑ.idealValue (Aideal R p.1 p.2).1 * chiIdealPow D (Aideal R p.1 p.2).1 (m : F) 1 *
        (PG (qI (Aideal R p.1 p.2).1 / Z) : ℂ)‖)) := by
  intro X Y Z hX hY hZ
  constructor
  · classical
    have hcompact : IsCompact (tsupport W.W1) := W.W1_compact
    obtain ⟨B, hB⟩ :=
      (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hcompact.isBounded
    let cutoff : ℝ := Y * max B 1
    have hcutoff : 0 ≤ cutoff := by
      dsimp [cutoff]
      positivity
    have hfinite := a2_bridge_COUNT_finite S cutoff hcutoff
    apply hfinite.1.subset
    intro I hI
    have hts : qI I.1 / Y ∈ tsupport W.W1 := by
      apply subset_closure
      exact Function.mem_support.mpr hI
    have hball := hB hts
    have hdist : dist (qI I.1 / Y) 0 ≤ B := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    have hfrac : qI I.1 / Y ≤ max B 1 := by
      calc
        qI I.1 / Y ≤ |qI I.1 / Y| := le_abs_self _
        _ = dist (qI I.1 / Y) 0 := by
          simpa only [sub_zero] using (Real.dist_eq (qI I.1 / Y) 0).symm
        _ ≤ B := hdist
        _ ≤ max B 1 := le_max_left _ _
    have hq : qI I.1 ≤ cutoff := by
      dsimp [cutoff]
      calc
        qI I.1 ≤ max B 1 * Y := (div_le_iff₀ hY).mp hfrac
        _ = Y * max B 1 := by ring
    simpa [qI, idealNorm] using hq
  · intro m
    have hsum := Bm_summable D S A H Bd ϑ R.vartheta_unitary (cgen R)
      (cgen_valid R) m Z hZ
    apply hsum.congr
    intro p
    simp only [Aideal, R.exterior.mul_val, R.exterior.ofSqf_val,
      R.exterior.pow_val, qI, idealNorm, div_eq_mul_inv]
/-- po:C-local-values: the one-prime T_v table, including the masked v≡0 case. -/
theorem po_C_local_T_values : ∀ v, v ∉ S.Sf → ∀ e : ℤ, ∀ y : S.R,
  localT R v e (y : F) =
    (if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e * localT R v e 1
      else if e % 6 = 0 then qI v.asIdeal - 1 else 0) ∧
  (e % 6 ≠ 0 → ‖localT R v e 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ)) ∧ localT R v 0 1 = -1 := by
  sorry
/-- po:euler-local-factorization, 05:444-550. Cross-prime exponents cancel modulo six. -/
theorem cross_prime_exponent_cancel (e e' l l' : ℕ) :
    6 ∣ 2 * (e + 3 * l) * (e' + 3 * l') + 4 * e * e' := by
  refine ⟨e * e' + e * l' + l * e' + 3 * l * l', ?_⟩
  ring

/-- po:H-local-bounds: C,Q0 chosen before the field, set S, phases, or frequency.
This is the absolute-cutoff obligation used when choosing S in A1. -/
theorem po_H_local_bounds_absolute :
  ∃ C Q0 : ℝ, 0 < C ∧ 1 < Q0 ∧
  ∀ (F' : Type) [Field F'] [NumberField F'] (CE' : ℕ) (cond' : Ideal (𝓞 F'))
    (D' : FieldData F') (S' : SData F' CE' cond') (H' : HilbertData F') (Bd' : BData S' H')
    (A' : AddCharData F') (ϑ' : HeckeChar F') (bc' : BalancedChoices D' S' H' Bd')
    (μ' : ∀ v : FinPlace F', Theta.LocHaar v) (v0' : InfinitePlace F')
    (R' : ReflectionSetup D' S' H' Bd' A' ϑ' bc' μ' v0') (η' : HeckeChar F')
    (U' : FrequencyData S' D' η'),
      EulerHypotheses R' η' → HasPoHLocalBounds R' η' U' C Q0 := by
  sorry
/-- po:H-local-bounds, 05:660-729. The numerical Q1 cutoff is fixed independently of arithmetic data. -/
theorem po_H_cutoff_from_constants (C Q0 : ℝ) : ∃ Q1 : ℕ,
  Q0 < (Q1 : ℝ) ∧ ∀ Q : ℝ, (Q1 : ℝ) < Q → C * Q ^ (-(1 + 1 / 4000 : ℝ)) < 1 / 2 := by
  sorry
/-- Named refutation gate: saturated subtraction changes the J=t-1 boundary in a naive translation. -/
theorem localC_natural_subtraction_gate : (0 - 1 + 1 : ℕ) = 1 ∧ (0 + 1 - 1 : ℕ) = 0 := by decide

/-- Named refutation gate: ordinary zeroth powers cannot implement the masked nonunit value. -/
theorem zeroth_power_mask_gate : (0 : ℂ) ^ (0 : ℕ) ≠ 0 := by norm_num

end PoissonSupplementary

section FinalPoissonClauses
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U)

def continuedCalF (u : U.U) (ξ w z : ℂ) : ℂ :=
  HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
    HA.LS S (η * (U.kummer u)⁻¹) ξ

/-- po:H-product / prop:euler-product: continuation identity with coordinatewise meromorphy.
The raw calF tsum is only compared in its convergence domain. -/
theorem po_euler_meromorphic_identity : EulerHypotheses R η →
  (∀ u ξ w z, initialRegion ξ w z → continuedCalF R η U HA HC u ξ w z = calF R η U u ξ w z) ∧
  (∀ u w z, MeromorphicOn (fun ξ => continuedCalF R η U HA HC u ξ w z)
    {ξ | eulerNeighborhood ![ξ,w,z]}) ∧
  (∀ u ξ z, MeromorphicOn (fun w => continuedCalF R η U HA HC u ξ w z)
    {w | eulerNeighborhood ![ξ,w,z]}) ∧
  (∀ u ξ w, MeromorphicOn (fun z => continuedCalF R η U HA HC u ξ w z)
    {z | eulerNeighborhood ![ξ,w,z]}) := by
  sorry
end FinalPoissonClauses
section CanonicalEulerObject
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

/-- Actual infinite-product definition; it assumes no convergence or nonvanishing result. -/
def canonicalEulerCorrection : EulerCorrection R η U where
  H u p := ∏' v : {v : FinPlace F // v ∉ S.Sf},
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)
  H_eq _ _ := rfl

/-- po:H-local-bounds: installing the numerical cutoff in the frozen CE parameter implies
small principal factors on the entire enlarged neighborhoods. -/
theorem po_H_principal_cutoff (C Q0 : ℝ) (Q1 : ℕ) :
  EulerHypotheses R η → HasPoHLocalBounds R η U C Q0 → Q0 < (Q1 : ℝ) → Q1 ≤ CE →
  (∀ Q : ℝ, (Q1 : ℝ) < Q → C * Q ^ (-(1 + 1 / 4000 : ℝ)) < 1 / 2) →
  ∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2 := by
  sorry
end CanonicalEulerObject
end ArtinPrimitiveRoots.A2
