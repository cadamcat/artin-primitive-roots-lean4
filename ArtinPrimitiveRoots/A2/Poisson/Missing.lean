import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Complex
import ArtinPrimitiveRoots.A2.Proofs.A2_WEIGHTS.Finite
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

set_option maxHeartbeats 10000000 in
private theorem po_e_residue_norm_one (I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1) (x : S.R)
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) :
    ‖S.e A (S.diag ((x : F) / (a : F)))‖ = 1 := by
  classical
  let Q : Type := ResidueRing R0.exterior I
  let g : S.R := R0.exterior.genR I
  let J : Ideal S.R := Ideal.span {g}
  let q : ℕ := Ideal.absNorm I.1
  letI : Fintype Q := R0.exterior.residueFinite I
  have hcard : Fintype.card Q = q := by
    dsimp [Q, q]
    exact R0.exterior.residue_card I
  let qMap : S.R →+* Q := Ideal.Quotient.mk J
  have hclass : qMap ((q : S.R) * x) = 0 := by
    have hkill : (Fintype.card Q) • qMap x = 0 := card_nsmul_eq_zero
    calc
      qMap ((q : S.R) * x) = qMap (q • x) := by simp [nsmul_eq_mul]
      _ = q • qMap x := map_nsmul qMap q x
      _ = 0 := by rw [← hcard]; exact hkill
  have hmem : (q : S.R) * x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hclass
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (by simpa [J] using hmem)
  have hgenRatio : ((R0.exterior.genR I : F) / (a : F)) ∈ S.R :=
    po_gen_ratio_mem_R (R := R0) I a ha
  let gdiv : S.R := ⟨((R0.exterior.genR I : S.R) : F) / (a : F), hgenRatio⟩
  let y : S.R := gdiv * r
  have hy : (y : F) = (q : F) * ((x : F) / (a : F)) := by
    dsimp [y, gdiv]
    have hrcast := congrArg (fun z : S.R => (z : F)) hr
    change (r : F) * (R0.exterior.genR I : F) = (q : F) * (x : F) at hrcast
    calc
      (R0.exterior.genR I : F) / (a : F) * (r : F) =
          ((r : F) * (R0.exterior.genR I : F)) / (a : F) := by
            field_simp [a.ne_zero] <;> ring
      _ = ((q : F) * (x : F)) / (a : F) := by rw [hrcast]
      _ = (q : F) * ((x : F) / (a : F)) := by ring
  let eDiag : AddChar F ℂ := {
    toFun := fun z => S.e A (S.diag z)
    map_zero_eq_one' := po_e_diagR_one S D A 0
    map_add_eq_mul' := by
      intro z₁ z₂
      calc
        S.e A (S.diag (z₁ + z₂)) = S.e A (S.diag z₁ + S.diag z₂) := by rw [map_add]
        _ = S.e A (S.diag z₁) * S.e A (S.diag z₂) := po_e_add S A _ _ }
  have hphasePow (n : ℕ) :
      S.e A (S.diag ((n : F) * ((x : F) / (a : F)))) =
        (S.e A (S.diag ((x : F) / (a : F)))) ^ n := by
    simpa [eDiag, nsmul_eq_mul] using
      (eDiag.map_nsmul_eq_pow n ((x : F) / (a : F)))
  have hphaseOne :
      S.e A (S.diag ((q : F) * ((x : F) / (a : F)))) = 1 := by
    rw [← hy]
    exact po_e_diagR_one S D A y
  have hqpos : 0 < q := by
    dsimp [q]
    have hI0 : I.1 ≠ 0 := by
      simpa only [Ideal.zero_eq_bot] using I.2.1
    exact Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
  have hpow := hphasePow q
  rw [hphaseOne] at hpow
  have hfin : IsOfFinOrder (S.e A (S.diag ((x : F) / (a : F)))) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨q, hqpos, hpow.symm⟩
  exact hfin.norm_eq_one

private theorem po_chi_norm_one (D : FieldData F) (P : FinPlace F) (x : F)
    (hx : residue P x ≠ 0) : ‖chi D P x‖ = 1 := by
  let ζ : rootsOfUnity 6 (𝓞 F) := chiAlg P x
  have hζ : (ζ : (𝓞 F)ˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 (ζ : (𝓞 F)ˣ)).mp ζ.property
  let ζ0 : 𝓞 F := ((ζ : (𝓞 F)ˣ) : 𝓞 F)
  have hζOF : ζ0 ^ 6 = 1 := by
    simpa [ζ0] using congrArg Units.val hζ
  have hζC : (D.σ0 (algebraMap (𝓞 F) F ζ0)) ^ 6 = 1 := by
    calc
      _ = D.σ0 (algebraMap (𝓞 F) F (ζ0 ^ 6)) := by simp only [map_pow]
      _ = 1 := by rw [hζOF]; simp
  have hpow : (chi D P x) ^ 6 = 1 := by
    rw [chi, if_neg hx]
    exact hζC
  have hfin : IsOfFinOrder (chi D P x) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨6, by norm_num, hpow⟩
  exact hfin.norm_eq_one

private theorem po_chiPow_norm_le_one (D : FieldData F) (P : FinPlace F)
    (x : F) (j : ℤ) : ‖chiPow D P x j‖ ≤ 1 := by
  by_cases hx : residue P x = 0
  · simp [chiPow, hx]
  · simp [chiPow, hx, po_chi_norm_one D P x hx]

private theorem po_multiset_map_prod_norm_le_one {α : Type*} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _)
        (ih fun x hx => hf x (Multiset.mem_cons_of_mem hx))

private theorem po_chiIdealPow_norm_le_one (D : FieldData F) (I : Ideal (𝓞 F))
    (x : F) (j : ℤ) : ‖chiIdealPow D I x j‖ ≤ 1 := by
  unfold chiIdealPow
  apply po_multiset_map_prod_norm_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using po_chiPow_norm_le_one D ⟨P, h.1, h.2⟩ x j
  · simp [h]

set_option maxHeartbeats 3000000 in
private theorem po_finiteGaussAt_norm_le (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1) (k : S.R) :
    ‖finiteGaussAt R0 I a (k : F)‖ ≤ qI I.1 := by
  classical
  let Q : Type := ResidueRing R0.exterior I
  letI : Fintype Q := R0.exterior.residueFinite I
  let f (x : Q) : ℂ :=
    chiIdealPow D I.1 (x.out : F) 1 *
      S.e A (S.diag ((k : F) * (x.out : F) / (a : F)))
  have hf (x : Q) : ‖f x‖ ≤ 1 := by
    dsimp [f]
    have hchi : ‖chiIdealPow D I.1 (x.out : F) 1‖ ≤ 1 :=
      po_chiIdealPow_norm_le_one D (I.1) (x.out : F) 1
    have he := po_e_residue_norm_one I a ha (k * x.out) R0
    have harg : ((k * x.out : S.R) : F) / (a : F) =
        (k : F) * (x.out : F) / (a : F) := by simp
    rw [harg] at he
    rw [norm_mul]
    exact mul_le_one₀ hchi (norm_nonneg _) he.le
  have hsumEq : finiteGaussAt R0 I a (k : F) = ∑ x : Q, f x := by
    dsimp [finiteGaussAt, f]
    exact finsum_eq_sum_of_fintype _
  have hcard : (Fintype.card Q : ℝ) = qI I.1 := by
    change (Fintype.card Q : ℝ) = (Ideal.absNorm I.1 : ℝ)
    exact_mod_cast R0.exterior.residue_card I
  calc
    ‖finiteGaussAt R0 I a (k : F)‖ = ‖∑ x : Q, f x‖ := by rw [hsumEq]
    _ ≤ ∑ x : Q, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Q, (1 : ℝ) := Finset.sum_le_sum fun x hx => hf x
    _ = (Fintype.card Q : ℝ) := by simp
    _ = qI I.1 := hcard

set_option maxHeartbeats 3000000 in
private theorem po_finiteFactor_norm_le (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1) (h : F) :
    ‖finiteFactor R0 s I a h‖ ≤ qI s.1 * qI I.1 := by
  classical
  let Q : Type := ResidueRing R0.exterior s
  letI : Fintype Q := R0.exterior.residueFinite s
  let term (d : Q) : ℂ :=
    if ∃ x : S.R, h - (a : F) * (d.out : F) =
        (bc.gen s : F) * (x : F) then
      chiIdealPow D s.1 (d.out : F) 1 *
        finiteGaussAt R0 I a ((h - (a : F) * (d.out : F)) / (bc.gen s : F))
    else 0
  have hterm (d : Q) : ‖term d‖ ≤ qI I.1 := by
    dsimp [term]
    by_cases hc : ∃ x : S.R, h - (a : F) * (d.out : F) =
        (bc.gen s : F) * (x : F)
    · obtain ⟨x, hx⟩ := hc
      have hb0 : (bc.gen s : F) ≠ 0 := Units.ne_zero (bc.gen s)
      have harg : (h - (a : F) * (d.out : F)) / (bc.gen s : F) = (x : F) := by
        rw [hx]
        field_simp [hb0]
      rw [if_pos (show ∃ x : S.R, h - (a : F) * (d.out : F) =
        (bc.gen s : F) * (x : F) from ⟨x, hx⟩), harg]
      have hchi : ‖chiIdealPow D s.1 (d.out : F) 1‖ ≤ 1 :=
        po_chiIdealPow_norm_le_one D s.1 (d.out : F) 1
      have hgauss : ‖finiteGaussAt R0 I a (x : F)‖ ≤ qI I.1 :=
        po_finiteGaussAt_norm_le R0 I a ha x
      calc
        ‖chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R0 I a (x : F)‖ =
            ‖chiIdealPow D s.1 (d.out : F) 1‖ *
              ‖finiteGaussAt R0 I a (x : F)‖ := norm_mul _ _
        _ ≤ 1 * qI I.1 := mul_le_mul hchi hgauss (norm_nonneg _) (by positivity)
        _ = qI I.1 := one_mul _
    · simp [hc, qI]
  have hsumEq : finiteFactor R0 s I a h = ∑ d : Q, term d := by
    dsimp [finiteFactor, term]
    exact finsum_eq_sum_of_fintype _
  have hcard : (Fintype.card Q : ℝ) = qI s.1 := by
    change (Fintype.card Q : ℝ) = (Ideal.absNorm s.1 : ℝ)
    exact_mod_cast R0.exterior.residue_card s
  have hqnonneg : 0 ≤ qI I.1 := by dsimp [qI]; positivity
  calc
    ‖finiteFactor R0 s I a h‖ = ‖∑ d : Q, term d‖ := by rw [hsumEq]
    _ ≤ ∑ d : Q, ‖term d‖ := norm_sum_le _ _
    _ ≤ ∑ _d : Q, qI I.1 := Finset.sum_le_sum fun d hd => hterm d
    _ = (Fintype.card Q : ℝ) * qI I.1 := by simp
    _ = qI s.1 * qI I.1 := by rw [hcard]

private theorem po_isGen_mul (I J : Ideal (𝓞 F)) (a b : Fˣ)
    (ha : S.IsGen (a : F) I) (hb : S.IsGen (b : F) J) :
    S.IsGen ((a * b : Fˣ) : F) (I * J) := by
  have hExt : S.IsExterior (I * J) := by
    constructor
    · exact mul_ne_zero ha.1.1 hb.1.1
    · intro v hvS hsub
      have hdiv := v.isPrime.mul_le.mp hsub
      rcases hdiv with hI | hJ
      · exact ha.1.2 v hvS hI
      · exact hb.1.2 v hvS hJ
  have hI0 : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using ha.1.1
  have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using hb.1.1
  have hcoe : ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    FractionalIdeal.coeIdeal_mul I J
  refine ⟨hExt, mul_ne_zero a.ne_zero b.ne_zero, ?_⟩
  intro v hvS
  calc
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a : F) * (b : F))) =
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) :=
      FractionalIdeal.count_mul F v
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr a.ne_zero)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr b.ne_zero)
    _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [ha.2.2 v hvS, hb.2.2 v hvS]
    _ = FractionalIdeal.count F v
        ((I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
          (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :=
      (FractionalIdeal.count_mul F v hI0 hJ0).symm
    _ = FractionalIdeal.count F v
        ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      exact congrArg (FractionalIdeal.count F v) hcoe.symm

private theorem po_allowed_generator_lift (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1) (hallowed : Bd.Allowed a) :
    ∃ u : S.Rˣ, ((u ^ 6 * R0.exterior.genR I : S.R) : F) = (a : F) := by
  obtain ⟨ε, hε, hrel⟩ :=
    Bd.allowed_unique I.1 a (bc.gen I) ⟨ha, hallowed⟩ (bc.gen_spec I)
  let epsUS : S.US := ⟨ε, hε⟩
  let epsR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F epsUS
  have hrelF : (a : F) = ((ε : Fˣ) : F) ^ 6 * (bc.gen I : F) := by
    have h := congrArg (fun z : Fˣ => (z : F)) hrel
    simpa using h
  have hepsR : ((epsR : S.Rˣ) : F) = (ε : Fˣ) := by rfl
  refine ⟨epsR, ?_⟩
  calc
    ((epsR ^ 6 * R0.exterior.genR I : S.R) : F) =
        ((epsR : S.Rˣ) : F) ^ 6 * ((R0.exterior.genR I : S.R) : F) := by simp
    _ = ((ε : Fˣ) : F) ^ 6 * (bc.gen I : F) := by
      rw [hepsR, R0.exterior.genR_val]
    _ = (a : F) := hrelF.symm

private theorem po_quotientProd_diff_mem {R : Type*} [CommRing R]
    (a b : R) (m : R ⧸ Ideal.span {a * b}) :
    m.out - (Ideal.Quotient.mk (Ideal.span {a}) m.out).out ∈ Ideal.span {a} := by
  have heq : Ideal.Quotient.mk (Ideal.span {a}) m.out =
      Ideal.Quotient.mk (Ideal.span {a})
        (Ideal.Quotient.mk (Ideal.span {a}) m.out).out := by
    rw [Ideal.Quotient.mk_out]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp heq

private noncomputable def po_quotientProdSecond {R : Type*} [CommRing R]
    (a b : R) (m : R ⧸ Ideal.span {a * b}) : R :=
  Classical.choose (Ideal.mem_span_singleton'.mp (po_quotientProd_diff_mem a b m))

private theorem po_quotientProdSecond_spec {R : Type*} [CommRing R]
    (a b : R) (m : R ⧸ Ideal.span {a * b}) :
    po_quotientProdSecond a b m * a =
      m.out - (Ideal.Quotient.mk (Ideal.span {a}) m.out).out :=
  Classical.choose_spec (Ideal.mem_span_singleton'.mp (po_quotientProd_diff_mem a b m))

private noncomputable def po_quotientProdMap {R : Type*} [CommRing R]
    (a b : R) (m : R ⧸ Ideal.span {a * b}) :
    (R ⧸ Ideal.span {a}) × (R ⧸ Ideal.span {b}) :=
  (Ideal.Quotient.mk (Ideal.span {a}) m.out,
    Ideal.Quotient.mk (Ideal.span {b}) (po_quotientProdSecond a b m))

private theorem po_quotientProdMap_injective {R : Type*} [CommRing R]
    (a b : R) :
    Function.Injective (po_quotientProdMap a b) := by
  intro m n h
  have hv : Ideal.Quotient.mk (Ideal.span {a}) m.out =
      Ideal.Quotient.mk (Ideal.span {a}) n.out := congrArg Prod.fst h
  have hj : Ideal.Quotient.mk (Ideal.span {b}) (po_quotientProdSecond a b m) =
      Ideal.Quotient.mk (Ideal.span {b}) (po_quotientProdSecond a b n) := congrArg Prod.snd h
  have hvOut : (Ideal.Quotient.mk (Ideal.span {a}) m.out).out =
      (Ideal.Quotient.mk (Ideal.span {a}) n.out).out := congrArg Quotient.out hv
  have hrdiff : po_quotientProdSecond a b m - po_quotientProdSecond a b n ∈
      Ideal.span {b} := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hj
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hrdiff
  have hdiff : m.out - n.out =
      (po_quotientProdSecond a b m - po_quotientProdSecond a b n) * a := by
    calc
      m.out - n.out =
          (m.out - (Ideal.Quotient.mk (Ideal.span {a}) m.out).out) -
            (n.out - (Ideal.Quotient.mk (Ideal.span {a}) n.out).out) := by
              rw [hvOut]
              ring
      _ = _ := by rw [← po_quotientProdSecond_spec a b m,
        ← po_quotientProdSecond_spec a b n]; ring
  have hmem : m.out - n.out ∈ Ideal.span {a * b} := by
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨t, ?_⟩
    calc
      t * (a * b) = (t * b) * a := by ring
      _ = (po_quotientProdSecond a b m - po_quotientProdSecond a b n) * a := by rw [ht]
      _ = m.out - n.out := hdiff.symm
  have hmk : Ideal.Quotient.mk (Ideal.span {a * b}) m.out =
      Ideal.Quotient.mk (Ideal.span {a * b}) n.out :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 hmem
  simpa only [Ideal.Quotient.mk_out] using hmk

private noncomputable def po_quotientProdEquiv {R : Type*} [CommRing R]
    (a b : R) [Fintype (R ⧸ Ideal.span {a * b})]
    [Fintype (R ⧸ Ideal.span {a})] [Fintype (R ⧸ Ideal.span {b})]
    (hcard : Fintype.card (R ⧸ Ideal.span {a * b}) =
      Fintype.card ((R ⧸ Ideal.span {a}) × (R ⧸ Ideal.span {b}))) :
    (R ⧸ Ideal.span {a * b}) ≃ (R ⧸ Ideal.span {a}) × (R ⧸ Ideal.span {b}) :=
  Equiv.ofBijective (po_quotientProdMap a b)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨po_quotientProdMap_injective a b, hcard⟩)

private theorem po_quotientProdEquiv_symm_mk {R : Type*} [CommRing R] [IsDomain R]
    (a b : R) (ha : a ≠ 0) [Fintype (R ⧸ Ideal.span {a * b})]
    [Fintype (R ⧸ Ideal.span {a})] [Fintype (R ⧸ Ideal.span {b})]
    (hcard : Fintype.card (R ⧸ Ideal.span {a * b}) =
      Fintype.card ((R ⧸ Ideal.span {a}) × (R ⧸ Ideal.span {b})))
    (v : R ⧸ Ideal.span {a}) (j : R ⧸ Ideal.span {b}) :
    (po_quotientProdEquiv a b hcard).symm (v, j) =
      Ideal.Quotient.mk (Ideal.span {a * b}) (v.out + a * j.out) := by
  let C : Ideal R := Ideal.span {a * b}
  let A : Ideal R := Ideal.span {a}
  let B : Ideal R := Ideal.span {b}
  let m : R ⧸ C := Ideal.Quotient.mk C (v.out + a * j.out)
  let v' : R ⧸ A := Ideal.Quotient.mk A m.out
  have hCsubA : C ≤ A := by
    apply Ideal.span_singleton_le_span_singleton.mpr
    exact ⟨b, by ring⟩
  have hmOut : Ideal.Quotient.mk C m.out = Ideal.Quotient.mk C (v.out + a * j.out) := by
    rw [Ideal.Quotient.mk_out]
  have hmDiff : m.out - (v.out + a * j.out) ∈ C :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hmOut
  have hma : Ideal.Quotient.mk A m.out =
      Ideal.Quotient.mk A (v.out + a * j.out) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (hCsubA hmDiff)
  have hAj : a * j.out ∈ A := Ideal.mem_span_singleton'.mpr ⟨j.out, by ring⟩
  have hxa : Ideal.Quotient.mk A (v.out + a * j.out) = v := by
    calc
      Ideal.Quotient.mk A (v.out + a * j.out) =
          Ideal.Quotient.mk A v.out + Ideal.Quotient.mk A (a * j.out) := by rw [map_add]
      _ = v + 0 := by rw [Ideal.Quotient.mk_out, Ideal.Quotient.eq_zero_iff_mem.mpr hAj]
      _ = v := by simp
  have hfirst : v' = v := hma.trans hxa
  have hsecond :
      Ideal.Quotient.mk B (po_quotientProdSecond a b m) = j := by
    have hr := po_quotientProdSecond_spec a b m
    have hvOut : v'.out = v.out := congrArg Quotient.out hfirst
    let t := Classical.choose (Ideal.mem_span_singleton'.mp hmDiff)
    have hChoose : t * (a * b) = m.out - (v.out + a * j.out) :=
      Classical.choose_spec (Ideal.mem_span_singleton'.mp hmDiff)
    have hsplit : m.out - v.out = a * j.out + (m.out - (v.out + a * j.out)) := by ring
    have hsecondMul : po_quotientProdSecond a b m * a = (j.out + t * b) * a := by
      rw [hr, hvOut, hsplit, hChoose.symm]
      ring
    have hrEq : po_quotientProdSecond a b m =
        j.out + t * b :=
      mul_right_cancel₀ ha hsecondMul
    have htMem : t * b ∈ B := Ideal.mem_span_singleton'.mpr ⟨t, by ring⟩
    calc
      Ideal.Quotient.mk B (po_quotientProdSecond a b m) =
          Ideal.Quotient.mk B (j.out + t * b) := by rw [hrEq]
      _ = Ideal.Quotient.mk B j.out := by
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr htMem, add_zero]
      _ = j := Ideal.Quotient.mk_out j
  have hmap : po_quotientProdMap a b m = (v, j) := by
    apply Prod.ext
    · dsimp [po_quotientProdMap, m, v']
      exact hfirst
    · exact hsecond
  let e := po_quotientProdEquiv a b hcard
  apply e.injective
  rw [e.apply_symm_apply]
  change (v, j) = po_quotientProdMap a b m
  exact hmap.symm

set_option maxHeartbeats 5000000 in
private theorem po_residueProductDecomp (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) :
    ∃ (aR : S.R), (aR : F) = (a : F) ∧
      Ideal.span {R0.exterior.genR I} = Ideal.span {aR} ∧
      Ideal.span {R0.exterior.genR (R0.exterior.mul s I)} =
        Ideal.span {aR * R0.exterior.genR s} ∧
      ∃ u : S.Rˣ, aR * R0.exterior.genR s = u * R0.exterior.genR (R0.exterior.mul s I) := by
  classical
  obtain ⟨uI, huI⟩ := po_allowed_generator_lift R0 I a ha hallowed
  let aR : S.R := uI ^ 6 * R0.exterior.genR I
  have haRVal : (aR : F) = (a : F) := by simpa [aR] using huI
  let gI : S.R := R0.exterior.genR I
  let gS : S.R := R0.exterior.genR s
  let total : S.ExtIdeal := R0.exterior.mul s I
  let gTotal : S.R := R0.exterior.genR total
  have hAssocA : Associated aR gI := by
    dsimp [aR, gI]
    exact associated_unit_mul_left (R0.exterior.genR I) (uI ^ 6) (uI ^ 6).isUnit
  have hSpanA : Ideal.span {gI} = Ideal.span {aR} := by
    exact Ideal.span_singleton_eq_span_singleton.mpr hAssocA.symm
  have hProdGen : S.IsGen ((bc.gen s * a : Fˣ) : F) total.1 := by
    dsimp [total]
    rw [R0.exterior.mul_val]
    exact po_isGen_mul s.1 I.1 (bc.gen s) a (bc.gen_spec s).1 ha
  have hProdAllowed : Bd.Allowed (bc.gen s * a) := by
    change (QuotientGroup.mk (S.diagU (bc.gen s * a)) : S.V) ∈ Bd.B
    rw [map_mul]
    exact Bd.B.mul_mem (bc.gen_spec s).2 hallowed
  obtain ⟨ε, hε, hrel⟩ :=
    Bd.allowed_unique total.1 (bc.gen s * a) (bc.gen total)
      ⟨hProdGen, hProdAllowed⟩ (bc.gen_spec total)
  let epsUS : S.US := ⟨ε, hε⟩
  let epsR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F epsUS
  have hepsR : ((epsR : S.Rˣ) : F) = (ε : Fˣ) := by rfl
  have hrelF : ((bc.gen s * a : Fˣ) : F) =
      ((ε : Fˣ) : F) ^ 6 * (bc.gen total : F) := by
    simpa using congrArg (fun z : Fˣ => (z : F)) hrel
  have hprodVal : ((gS * aR : S.R) : F) =
      ((epsR ^ 6 * gTotal : S.R) : F) := by
    change ((gS : S.R) : F) * (aR : F) =
      ((epsR ^ 6 * gTotal : S.R) : F)
    calc
      _ = (bc.gen s : F) * (aR : F) := by rw [R0.exterior.genR_val s]
      _ = (bc.gen s : F) * (a : F) := by rw [haRVal]
      _ = ((ε : Fˣ) : F) ^ 6 * (bc.gen total : F) := hrelF
      _ = ((epsR ^ 6 * gTotal : S.R) : F) := by
        dsimp [gTotal]
        rw [hepsR, R0.exterior.genR_val]
  have hprodEq : gS * aR = epsR ^ 6 * gTotal := Subtype.ext hprodVal
  have hprodEq' : aR * gS = epsR ^ 6 * gTotal := by
    rw [mul_comm, hprodEq]
  have hAssocTotal : Associated (aR * gS) gTotal := by
    rw [hprodEq']
    exact associated_unit_mul_left gTotal (epsR ^ 6) (epsR ^ 6).isUnit
  have hSpanTotal : Ideal.span {gTotal} = Ideal.span {aR * gS} :=
    Ideal.span_singleton_eq_span_singleton.mpr hAssocTotal.symm
  exact ⟨aR, haRVal, hSpanA, hSpanTotal, epsR ^ 6, hprodEq'⟩

private theorem po_chiIdealPow_eq_of_mod (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (x y : S.R)
    (hxy : (x : S.R) - y ∈ Ideal.span {R0.exterior.genR I}) :
    chiIdealPow D I.1 (x : F) 1 = chiIdealPow D I.1 (y : F) 1 := by
  apply po_chiIdealPow_congr I.1 I.2 (x : F) (y : F)
  intro v hvI
  have hvS : v ∉ S.Sf := by
    intro hv
    exact I.2.2 v hv (Ideal.le_of_dvd hvI)
  have hx : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hvS
  have hy : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hvS
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hxy
  have hdiff : (x : F) - (y : F) = (r : F) * (R0.exterior.genR I : F) := by
    have := congrArg (fun z : S.R => (z : F)) hr
    simpa using this.symm
  have hrval : HeightOneSpectrum.valuation F v (r : F) ≤ 1 := r.property v hvS
  have hgen : HeightOneSpectrum.valuation F v (R0.exterior.genR I : F) < 1 :=
    po_gen_lt_one (R := R0) I v hvI
  have hdiffval : HeightOneSpectrum.valuation F v ((x : F) - (y : F)) < 1 := by
    rw [hdiff, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hrval zero_le hgen
  exact ⟨hx, hy, hdiffval⟩

private theorem po_finiteGaussAt_quotientEq
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (I : S.ExtIdeal)
    (a : Fˣ) (aR : S.R) (haR : (aR : F) = (a : F))
    (hspan : Ideal.span {R0.exterior.genR I} = Ideal.span {aR}) (k : S.R) :
    finiteGaussAt R0 I a (k : F) =
      ∑ᶠ v : S.R ⧸ Ideal.span {aR},
        chiIdealPow D I.1 (v.out : F) 1 *
          S.e A (S.diag ((k : F) * (v.out : F) / (a : F))) := by
  classical
  let QI := ResidueRing R0.exterior I
  let QA := S.R ⧸ Ideal.span {aR}
  let e : QI ≃ QA := Ideal.quotEquivOfEq hspan
  letI : Fintype QI := R0.exterior.residueFinite I
  letI : Fintype QA := Fintype.ofEquiv QI e
  let f : QI → ℂ := fun x =>
    chiIdealPow D I.1 (x.out : F) 1 *
      S.e A (S.diag ((k : F) * (x.out : F) / (a : F)))
  let g : QA → ℂ := fun x =>
    chiIdealPow D I.1 (x.out : F) 1 *
      S.e A (S.diag ((k : F) * (x.out : F) / (a : F)))
  have headd (x y : F) :
      S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
    calc
      S.e A (S.diag (x + y)) = S.e A (S.diag x + S.diag y) := by rw [map_add]
      _ = S.e A (S.diag x) * S.e A (S.diag y) := po_e_add S A _ _
  have hterm (x : QI) : f x = g (e x) := by
    dsimp [f, g]
    have hclass : Ideal.Quotient.mk (Ideal.span {aR}) (e x).out =
        Ideal.Quotient.mk (Ideal.span {aR}) x.out := by
      calc
        Ideal.Quotient.mk (Ideal.span {aR}) (e x).out = e x :=
          Ideal.Quotient.mk_out (e x)
        _ = Ideal.Quotient.mk (Ideal.span {aR}) x.out :=
          by simpa [e] using Ideal.quotEquivOfEq_mk hspan x.out
    have hmem : (e x).out - x.out ∈ Ideal.span {aR} :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hrep : ((e x).out : F) = (x.out : F) + (r : F) * (aR : F) := by
      have hcast := congrArg (fun z : S.R => (z : F)) hr
      change (r : F) * (aR : F) = ((e x).out : F) - (x.out : F) at hcast
      calc
        ((e x).out : F) = (x.out : F) +
            (((e x).out : F) - (x.out : F)) := by ring
        _ = (x.out : F) + (r : F) * (aR : F) := by rw [← hcast]
    have hmemI : (e x).out - x.out ∈ Ideal.span {R0.exterior.genR I} :=
      (congrArg (fun J : Ideal S.R => (e x).out - x.out ∈ J) hspan.symm).mp hmem
    have hchar : chiIdealPow D I.1 ((e x).out : F) 1 =
        chiIdealPow D I.1 (x.out : F) 1 :=
      po_chiIdealPow_eq_of_mod R0 I (e x).out x.out hmemI
    have harg : (k : F) * ((e x).out : F) / (a : F) =
        (k : F) * (x.out : F) / (a : F) + (k : F) * (r : F) := by
      rw [hrep, haR]
      field_simp [a.ne_zero]
    have hphase : S.e A (S.diag ((k : F) * ((e x).out : F) / (a : F))) =
        S.e A (S.diag ((k : F) * (x.out : F) / (a : F))) := by
      rw [harg, headd]
      have hkr : (k : F) * (r : F) = ((k * r : S.R) : F) := by simp
      rw [hkr, po_e_diagR_one S D A (k * r)]
      simp
    rw [hchar, hphase]
  change (∑ᶠ x : QI, f x) = ∑ᶠ x : QA, g x
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact Fintype.sum_bijective e e.bijective f g (by
    intro x
    exact hterm x)

private instance po_residueFintype (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) : Fintype (ResidueRing R0.exterior I) :=
  R0.exterior.residueFinite I

private theorem po_finiteGaussAt_add_aR (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (a : Fˣ) (k r : S.R) :
    finiteGaussAt R0 I a ((k : F) + (a : F) * (r : F)) =
      finiteGaussAt R0 I a (k : F) := by
  classical
  letI := R0.exterior.residueFinite I
  unfold finiteGaussAt
  simp only [finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro x hx
  have harg : ((k : F) + (a : F) * (r : F)) * (x.out : F) / (a : F) =
      (k : F) * (x.out : F) / (a : F) + (r : F) * (x.out : F) := by
    field_simp [a.ne_zero]
  rw [harg, map_add,
    po_e_add S A (S.diag ((k : F) * (x.out : F) / (a : F)))
      (S.diag ((r : F) * (x.out : F)))]
  have htriv : S.e A (S.diag ((r * x.out : S.R) : F)) = 1 :=
    po_e_diagR_one S D A (r * x.out)
  rw [show (r : F) * (x.out : F) = ((r * x.out : S.R) : F) by simp, htriv]
  simp

private theorem po_finiteGaussAt_gamma_scale
    (I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (γ : Gamma S) (k : S.R) :
    finiteGaussAt R I a (((γ.1 : Fˣ) : F) * (k : F)) =
      finiteGaussAt R I a (k : F) := by
  classical
  obtain ⟨eps, heps⟩ := γ.2
  have heps6 : eps ^ 6 = γ.1 := by simpa [sixthPowerOnUS] using heps
  let gammaF : Fˣ := (γ.1 : Fˣ)
  have hgammaF : gammaF = (eps : Fˣ) ^ 6 :=
    congrArg (fun u : S.US => (u : Fˣ)) heps6.symm
  let gammaR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F γ.1
  have hgammaRVal : ((gammaR : S.Rˣ) : F) = (gammaF : F) := by rfl
  let gI : S.R := R.exterior.genR I
  have hgIdiv : ((gI : F) / (a : F)) ∈ S.R :=
    po_gen_ratio_mem_R (R := R) I a ha
  let ratioR : S.R := ⟨(gI : F) / (a : F), hgIdiv⟩
  let Q : Type := ResidueRing R.exterior I
  let J : Ideal S.R := Ideal.span {gI}
  let qMap : S.R →+* Q := Ideal.Quotient.mk J
  let gammaQ : Qˣ := Units.map qMap gammaR
  letI : Fintype Q := R.exterior.residueFinite I
  let e : Q ≃ Q := {
    toFun x := (gammaQ : Q) * x
    invFun x := ((gammaQ⁻¹ : Qˣ) : Q) * x
    left_inv := by intro x; simp [mul_assoc]
    right_inv := by intro x; simp [mul_assoc] }
  have hEclass (x : Q) :
      e x = Ideal.Quotient.mk J ((gammaR : S.R) * x.out) := by
    simp [e, gammaQ, qMap, map_mul]
  let f (x : Q) : ℂ :=
    chiIdealPow D I.1 (x.out : F) 1 *
      S.e A (S.diag (((gammaF : F) * (k : F)) * (x.out : F) / (a : F)))
  let g (x : Q) : ℂ :=
    chiIdealPow D I.1 (x.out : F) 1 *
      S.e A (S.diag ((k : F) * (x.out : F) / (a : F)))
  have hEadd (x y : F) :
      S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
    calc
      S.e A (S.diag (x + y)) = S.e A (S.diag x + S.diag y) := by rw [map_add]
      _ = S.e A (S.diag x) * S.e A (S.diag y) := po_e_add S A _ _
  have hterm (x : Q) : f x = g (e x) := by
    dsimp [f, g]
    have hclass : Ideal.Quotient.mk J (e x).out =
        Ideal.Quotient.mk J ((gammaR : S.R) * x.out) := by
      calc
        Ideal.Quotient.mk J (e x).out = e x := Ideal.Quotient.mk_out (e x)
        _ = Ideal.Quotient.mk J ((gammaR : S.R) * x.out) := hEclass x
    have hmem : (e x).out - (gammaR : S.R) * x.out ∈ J :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hrep : (e x).out = (gammaR : S.R) * x.out + r * gI := by
      calc
        (e x).out = (gammaR : S.R) * x.out +
            ((e x).out - (gammaR : S.R) * x.out) := by ring
        _ = (gammaR : S.R) * x.out + r * gI := by rw [← hr]
    have hmemI : (e x).out - (gammaR : S.R) * x.out ∈
        Ideal.span {R.exterior.genR I} := by
      change (e x).out - (gammaR : S.R) * x.out ∈ J
      exact hmem
    have hcharRep : chiIdealPow D I.1 ((e x).out : F) 1 =
        chiIdealPow D I.1 (((gammaR : S.R) * x.out : S.R) : F) 1 :=
      po_chiIdealPow_eq_of_mod R I (e x).out ((gammaR : S.R) * x.out) hmemI
    have hcharSix : chiIdealPow D I.1
        (((gammaR : S.R) * x.out : S.R) : F) 1 =
          chiIdealPow D I.1 (x.out : F) 1 := by
      have hGammaProd : (((gammaR : S.R) * x.out : S.R) : F) =
          (gammaF : F) * (x.out : F) := by simp [hgammaRVal]
      rw [hGammaProd, hgammaF]
      exact po_chiIdealPow_US_six D S I.1 I.2 eps x.out
    have hchar : chiIdealPow D I.1 ((e x).out : F) 1 =
        chiIdealPow D I.1 (x.out : F) 1 := hcharRep.trans hcharSix
    have hrepF : ((e x).out : F) = (gammaF : F) * (x.out : F) +
        (r : F) * (gI : F) := by
      have h := congrArg (fun z : S.R => (z : F)) hrep
      simpa [hgammaRVal] using h
    have harg : (k : F) * ((e x).out : F) / (a : F) =
        (((gammaF : F) * (k : F)) * (x.out : F) / (a : F)) +
          (k : F) * (r : F) * (ratioR : F) := by
      rw [hrepF]
      dsimp [ratioR]
      field_simp [a.ne_zero] <;> ring
    have hphase : S.e A (S.diag ((k : F) * ((e x).out : F) / (a : F))) =
        S.e A (S.diag ((((gammaF : F) * (k : F)) * (x.out : F) / (a : F)))) := by
      rw [harg]
      have hz : (k : F) * (r : F) * (ratioR : F) =
          ((k * r * ratioR : S.R) : F) := by simp
      rw [hz, hEadd, po_e_diagR_one S D A (k * r * ratioR)]
      simp
    rw [hchar, hphase]
  change (∑ᶠ x : Q, f x) = ∑ᶠ x : Q, g x
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact Fintype.sum_bijective e e.bijective f g (by
    intro x
    exact hterm x)

private noncomputable def po_exteriorResidueProductEquiv
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (s I : S.ExtIdeal) (aR : S.R)
    (hI : Ideal.span {R0.exterior.genR I} = Ideal.span {aR})
    (hT : Ideal.span {R0.exterior.genR (R0.exterior.mul s I)} =
      Ideal.span {aR * R0.exterior.genR s}) :
    ResidueRing R0.exterior (R0.exterior.mul s I) ≃
      (S.R ⧸ Ideal.span {aR}) × ResidueRing R0.exterior s := by
  classical
  let QI := ResidueRing R0.exterior I
  let QS := ResidueRing R0.exterior s
  let QT := ResidueRing R0.exterior (R0.exterior.mul s I)
  let QA := S.R ⧸ Ideal.span {aR}
  let QP := S.R ⧸ Ideal.span {aR * R0.exterior.genR s}
  let total := R0.exterior.mul s I
  let eI : QI ≃ QA := Ideal.quotEquivOfEq hI
  let eT : QT ≃ QP := Ideal.quotEquivOfEq hT
  letI : Fintype QI := R0.exterior.residueFinite I
  letI : Fintype QS := R0.exterior.residueFinite s
  letI : Fintype QT := R0.exterior.residueFinite total
  letI : Fintype QA := Fintype.ofEquiv QI eI
  letI : Fintype QP := Fintype.ofEquiv QT eT
  have hcardA : Fintype.card QA = Ideal.absNorm I.1 := by
    calc
      Fintype.card QA = Fintype.card QI := Fintype.card_congr eI.symm
      _ = Ideal.absNorm I.1 := R0.exterior.residue_card I
  have hcardS : Fintype.card QS = Ideal.absNorm s.1 := R0.exterior.residue_card s
  have hcardT : Fintype.card QT = Ideal.absNorm total.1 :=
    R0.exterior.residue_card total
  have hnorm : Ideal.absNorm total.1 = Ideal.absNorm s.1 * Ideal.absNorm I.1 := by
    dsimp [total]
    rw [R0.exterior.mul_val]
    exact map_mul Ideal.absNorm s.1 I.1
  have hcard : Fintype.card QP =
      Fintype.card (QA × QS) := by
    calc
      Fintype.card QP = Fintype.card QT := (Fintype.card_congr eT).symm
      _ = Ideal.absNorm total.1 := hcardT
      _ = Ideal.absNorm s.1 * Ideal.absNorm I.1 := hnorm
      _ = Fintype.card QA * Fintype.card QS := by
        rw [hcardA, hcardS, mul_comm]
      _ = Fintype.card (QA × QS) := by rw [Fintype.card_prod]
  exact eT.trans (po_quotientProdEquiv aR (R0.exterior.genR s) hcard)

private theorem po_exteriorResidueProductEquiv_symm_mk
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (s I : S.ExtIdeal) (aR : S.R)
    (haR : aR ≠ 0)
    (hI : Ideal.span {R0.exterior.genR I} = Ideal.span {aR})
    (hT : Ideal.span {R0.exterior.genR (R0.exterior.mul s I)} =
      Ideal.span {aR * R0.exterior.genR s})
    (v : S.R ⧸ Ideal.span {aR}) (j : ResidueRing R0.exterior s) :
    (po_exteriorResidueProductEquiv R0 s I aR hI hT).symm (v, j) =
      Ideal.Quotient.mk (Ideal.span {R0.exterior.genR (R0.exterior.mul s I)})
        (v.out + aR * j.out) := by
  classical
  let QI := ResidueRing R0.exterior I
  let QS := ResidueRing R0.exterior s
  let QT := ResidueRing R0.exterior (R0.exterior.mul s I)
  let QA := S.R ⧸ Ideal.span {aR}
  let QP := S.R ⧸ Ideal.span {aR * R0.exterior.genR s}
  let total := R0.exterior.mul s I
  let eI : QI ≃ QA := Ideal.quotEquivOfEq hI
  let eT : QT ≃ QP := Ideal.quotEquivOfEq hT
  letI : Fintype QI := R0.exterior.residueFinite I
  letI : Fintype QS := R0.exterior.residueFinite s
  letI : Fintype QT := R0.exterior.residueFinite total
  letI : Fintype QA := Fintype.ofEquiv QI eI
  letI : Fintype QP := Fintype.ofEquiv QT eT
  have hcardA : Fintype.card QA = Ideal.absNorm I.1 := by
    calc
      Fintype.card QA = Fintype.card QI := Fintype.card_congr eI.symm
      _ = Ideal.absNorm I.1 := R0.exterior.residue_card I
  have hcardS : Fintype.card QS = Ideal.absNorm s.1 := R0.exterior.residue_card s
  have hcardT : Fintype.card QT = Ideal.absNorm total.1 :=
    R0.exterior.residue_card total
  have hnorm : Ideal.absNorm total.1 = Ideal.absNorm s.1 * Ideal.absNorm I.1 := by
    dsimp [total]
    rw [R0.exterior.mul_val]
    exact map_mul Ideal.absNorm s.1 I.1
  have hcard : Fintype.card QP =
      Fintype.card (QA × QS) := by
    calc
      Fintype.card QP = Fintype.card QT := (Fintype.card_congr eT).symm
      _ = Ideal.absNorm total.1 := hcardT
      _ = Ideal.absNorm s.1 * Ideal.absNorm I.1 := hnorm
      _ = Fintype.card QA * Fintype.card QS := by
        rw [hcardA, hcardS, mul_comm]
      _ = Fintype.card (QA × QS) := by rw [Fintype.card_prod]
  change (eT.trans (po_quotientProdEquiv aR (R0.exterior.genR s) hcard)).symm
      (v, j) = _
  rw [Equiv.symm_trans_apply]
  rw [po_quotientProdEquiv_symm_mk aR (R0.exterior.genR s) haR]
  change (Ideal.quotEquivOfEq hT).symm
      (Ideal.Quotient.mk (Ideal.span {aR * R0.exterior.genR s}) (v.out + aR * j.out)) = _
  rw [Ideal.quotEquivOfEq_symm]
  exact Ideal.quotEquivOfEq_mk hT.symm _

set_option maxHeartbeats 5000000 in
private theorem po_residue_addPhase_sum (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (s : S.ExtIdeal) (c : S.R) :
    (∑ j : ResidueRing R0.exterior s,
      S.e A (S.diag ((c : F) * (j.out : F) / (R0.exterior.genR s : F)))) =
      if ∃ x : S.R, (c : F) = (R0.exterior.genR s : F) * (x : F) then
        (Ideal.absNorm s.1 : ℂ) else 0 := by
  classical
  let Q : Type := ResidueRing R0.exterior s
  let g : S.R := R0.exterior.genR s
  have hg0 : (g : F) ≠ 0 := by
    rw [R0.exterior.genR_val]
    exact Units.ne_zero (bc.gen s)
  let phase (j : Q) : ℂ := S.e A (S.diag ((c : F) * (j.out : F) / (g : F)))
  have hEadd (x y : F) :
      S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
    calc
      S.e A (S.diag (x + y)) = S.e A (S.diag x + S.diag y) := by rw [map_add]
      _ = S.e A (S.diag x) * S.e A (S.diag y) := po_e_add S A _ _
  have hphaseAdd (j k : Q) : phase (j + k) = phase j * phase k := by
    dsimp [phase]
    let z : Q := j + k
    have hclass : Ideal.Quotient.mk (Ideal.span {g}) z.out =
        Ideal.Quotient.mk (Ideal.span {g}) (j.out + k.out) := by
      calc
        Ideal.Quotient.mk (Ideal.span {g}) z.out = z := Ideal.Quotient.mk_out z
        _ = j + k := rfl
        _ = Ideal.Quotient.mk (Ideal.span {g}) j.out +
              Ideal.Quotient.mk (Ideal.span {g}) k.out := by
                rw [Ideal.Quotient.mk_out j, Ideal.Quotient.mk_out k]
        _ = Ideal.Quotient.mk (Ideal.span {g}) (j.out + k.out) := by rw [map_add]
    have hmem : z.out - (j.out + k.out) ∈ Ideal.span {g} :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (by simpa [g] using hmem)
    have harg : (c : F) * (z.out : F) / (g : F) =
        ((c : F) * (j.out : F) / (g : F) +
          (c : F) * (k.out : F) / (g : F)) + (c : F) * (r : F) := by
      have hrep : (z.out : F) = (j.out : F) + (k.out : F) + (r : F) * (g : F) := by
        have hcast := congrArg (fun w : S.R => (w : F)) hr
        change (r : F) * (g : F) = (z.out : F) - ((j.out : F) + (k.out : F)) at hcast
        calc
          (z.out : F) = (j.out : F) + (k.out : F) +
              ((z.out : F) - ((j.out : F) + (k.out : F))) := by ring
          _ = (j.out : F) + (k.out : F) + (r : F) * (g : F) := by rw [← hcast]
      rw [hrep]
      field_simp [hg0]

    rw [harg]
    calc
      S.e A (S.diag (((c : F) * (j.out : F) / (g : F) +
          (c : F) * (k.out : F) / (g : F)) + (c : F) * (r : F))) =
        S.e A (S.diag ((c : F) * (j.out : F) / (g : F) +
          (c : F) * (k.out : F) / (g : F))) *
          S.e A (S.diag ((c : F) * (r : F))) := by
            exact hEadd _ _
      _ = (S.e A (S.diag ((c : F) * (j.out : F) / (g : F))) *
          S.e A (S.diag ((c : F) * (k.out : F) / (g : F)))) *
          S.e A (S.diag ((c : F) * (r : F))) := by
            rw [hEadd]
      _ = phase j * phase k := by
        have htriv : S.e A (S.diag ((c * r : S.R) : F)) = 1 := po_e_diagR_one S D A (c * r)
        rw [show S.e A (S.diag ((c : F) * (j.out : F) / (g : F))) = phase j by rfl,
          show S.e A (S.diag ((c : F) * (k.out : F) / (g : F))) = phase k by rfl]
        rw [show S.e A (S.diag ((c : F) * (r : F))) = 1 by simpa using htriv]
        ring
  have hphaseOne_of_condition
      (hc : ∃ x : S.R, (c : F) = (g : F) * (x : F)) (j : Q) : phase j = 1 := by
    obtain ⟨x, hx⟩ := hc
    dsimp [phase]
    have harg : (c : F) * (j.out : F) / (g : F) = (x : F) * (j.out : F) := by
      rw [hx]
      field_simp [hg0]
    rw [harg]
    simpa using po_e_diagR_one S D A (x * j.out)
  by_cases hc : ∃ x : S.R, (c : F) = (g : F) * (x : F)
  · rw [if_pos hc]
    calc
      (∑ j : Q, S.e A (S.diag ((c : F) * (j.out : F) / (g : F)))) =
          ∑ _j : Q, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hphaseOne_of_condition hc j
      _ = (Fintype.card Q : ℂ) := by simp
      _ = (Ideal.absNorm s.1 : ℂ) := by exact_mod_cast R0.exterior.residue_card s
  · rw [if_neg hc]
    have hnontrivial : ∃ j : Q, phase j ≠ 1 := by
      by_contra hnone
      push_neg at hnone
      have hrow (m : S.R) :
          S.e A (S.diag ((c : F) * (m : F) / (g : F))) = 1 := by
        let j : Q := Ideal.Quotient.mk (Ideal.span {g}) m
        have hclass : Ideal.Quotient.mk (Ideal.span {g}) m =
            Ideal.Quotient.mk (Ideal.span {g}) j.out := by
          simp [j]
        have hmem : m - j.out ∈ Ideal.span {g} :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
        have hrep : (m : F) = (j.out : F) + (r : F) * (g : F) := by
          have hcast := congrArg (fun w : S.R => (w : F)) hr
          change (r : F) * (g : F) = (m : F) - (j.out : F) at hcast
          calc
            (m : F) = (j.out : F) + ((m : F) - (j.out : F)) := by ring
            _ = (j.out : F) + (r : F) * (g : F) := by rw [← hcast]
        have harg : (c : F) * (m : F) / (g : F) =
            (c : F) * (j.out : F) / (g : F) + (c : F) * (r : F) := by
          rw [hrep]
          field_simp [hg0]

        rw [harg]
        calc
          S.e A (S.diag ((c : F) * (j.out : F) / (g : F) + (c : F) * (r : F))) =
              phase j * S.e A (S.diag ((c : F) * (r : F))) := by
                simpa [phase] using hEadd
                  ((c : F) * (j.out : F) / (g : F)) ((c : F) * (r : F))
          _ = 1 := by
            rw [hnone j]
            simpa using po_e_diagR_one S D A (c * r)
      have hAnn : S.diag ((c : F) / (g : F)) ∈ S.annihilator A S.diagR := by
        intro y hy
        obtain ⟨m, rfl⟩ := hy
        have hmul : S.diag (m : F) * S.diag ((c : F) / (g : F)) =
            S.diag ((c : F) * (m : F) / (g : F)) := by
          calc
            S.diag (m : F) * S.diag ((c : F) / (g : F)) =
                S.diag ((m : F) * ((c : F) / (g : F))) := (map_mul (S.diag) _ _).symm
            _ = S.diag ((c : F) * (m : F) / (g : F)) := by
              congr 1
              field_simp [hg0]
        rw [hmul]
        exact hrow m
      have hdiagMem : S.diag ((c : F) / (g : F)) ∈ S.diagR := by
        rw [S.diagR_eq_annihilator D A]
        exact hAnn
      obtain ⟨r, hr⟩ := hdiagMem
      have hdiagInj : Function.Injective (S.diag : F →+* S.FS) := by
        intro x y hxy
        apply v0.embedding.injective
        change (S.diag x).2 v0 = (S.diag y).2 v0
        exact congrArg (fun z : S.FS => z.2 v0) hxy
      have hratio : (r : F) = (c : F) / (g : F) := hdiagInj hr
      apply hc
      refine ⟨r, ?_⟩
      calc
        (c : F) = (c : F) / (g : F) * (g : F) := by field_simp [hg0]
        _ = (r : F) * (g : F) := by rw [hratio]
        _ = (g : F) * (r : F) := by ring
    obtain ⟨j₀, hj₀⟩ := hnontrivial
    let e : Q ≃ Q := Equiv.addRight (-j₀)
    have hsumReindex : (∑ j : Q, phase j) = ∑ j : Q, phase (j + j₀) := by
      exact Fintype.sum_bijective e e.bijective phase (fun j => phase (j + j₀)) (by
        intro j
        simp [e, add_assoc, add_comm, add_left_comm])
    have hsumFactor : (∑ j : Q, phase (j + j₀)) =
        (∑ j : Q, phase j) * phase j₀ := by
      calc
        _ = ∑ j : Q, phase j * phase j₀ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hphaseAdd]
        _ = _ := by rw [Finset.sum_mul]
    have hmul : (∑ j : Q, phase j) * (1 - phase j₀) = 0 := by
      calc
        _ = (∑ j : Q, phase j) - (∑ j : Q, phase j) * phase j₀ := by ring
        _ = 0 := by rw [← hsumFactor, hsumReindex]; ring
    have hne : 1 - phase j₀ ≠ 0 := by
      intro h
      apply hj₀
      exact (sub_eq_zero.mp h).symm
    have hzero : (∑ j : Q, phase j) = 0 := (mul_eq_zero.mp hmul).resolve_right hne
    simpa [phase] using hzero

set_option maxHeartbeats 10000000 in
private theorem po_finite_poisson_identity
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (s I : S.ExtIdeal) (a : Fˣ)
    (ha : S.IsGen (a : F) I.1) (hallowed : Bd.Allowed a) (h : S.R) :
    (∑ᶠ m : ResidueRing R0.exterior (R0.exterior.mul s I),
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R0 s (-(m.out : F)) *
        chiIdealPow D I.1 (m.out : F) 1 *
          S.e A (S.diag ((h : F) * (m.out : F) /
            ((bc.gen s : F) * (a : F))))) =
      (qI s.1 ^ (1 / 2 : ℝ) : ℝ) * finiteFactor R0 s I a (h : F) := by
  classical
  let total := R0.exterior.mul s I
  let gI : S.R := R0.exterior.genR I
  let gS : S.R := R0.exterior.genR s
  let gT : S.R := R0.exterior.genR total
  obtain ⟨aR, haR, hSpanI, hSpanT, huExists⟩ :=
    po_residueProductDecomp R0 s I a ha hallowed
  obtain ⟨u, hu⟩ := huExists
  have haR0 : aR ≠ 0 := by
    intro hz
    apply a.ne_zero
    have hzF : (aR : F) = 0 := congrArg (fun x : S.R => (x : F)) hz
    simpa [haR] using hzF
  have haF0 : (aR : F) ≠ 0 := by simpa [haR] using a.ne_zero
  have hgS0 : (gS : F) ≠ 0 := by
    dsimp [gS]
    rw [R0.exterior.genR_val]
    exact (bc.gen s).ne_zero
  have hgSval : (gS : F) = ((bc.gen s : Fˣ) : F) := R0.exterior.genR_val s
  let uInvR : S.R := (u⁻¹ : S.Rˣ)
  have huF0 : (((u : S.Rˣ) : S.R) : F) ≠ 0 := by
    intro hz
    have huS0 : ((u : S.Rˣ) : S.R) ≠ 0 := Units.ne_zero u
    apply huS0
    apply Subtype.ext
    exact hz
  have huValF : (aR : F) * (gS : F) =
      (((u : S.Rˣ) : S.R) : F) * (gT : F) :=
    congrArg (fun x : S.R => (x : F)) hu
  have hgTval : (gT : F) = (uInvR : F) * (aR : F) * (gS : F) := by
    have hInvMul : (uInvR : F) * (((u : S.Rˣ) : S.R) : F) = 1 := by
      have hInvMulR : uInvR * ((u : S.Rˣ) : S.R) = 1 := by simp [uInvR]
      exact congrArg (fun z : S.R => (z : F)) hInvMulR
    calc
      (gT : F) = 1 * (gT : F) := by simp
      _ = (uInvR : F) * (((u : S.Rˣ) : S.R) : F) * (gT : F) := by
        rw [hInvMul]
      _ = (uInvR : F) * ((((u : S.Rˣ) : S.R) : F) * (gT : F)) := by ring
      _ = (uInvR : F) * ((aR : F) * (gS : F)) := by rw [← huValF]
      _ = (uInvR : F) * (aR : F) * (gS : F) := by ring
  let QI := ResidueRing R0.exterior I
  let QS := ResidueRing R0.exterior s
  let QT := ResidueRing R0.exterior total
  let QA := S.R ⧸ Ideal.span {aR}
  let eA : QI ≃ QA := Ideal.quotEquivOfEq hSpanI
  letI : Fintype QI := R0.exterior.residueFinite I
  letI : Fintype QS := R0.exterior.residueFinite s
  letI : Fintype QT := R0.exterior.residueFinite total
  letI : Fintype QA := Fintype.ofEquiv QI eA
  let eSplit := po_exteriorResidueProductEquiv R0 s I aR hSpanI hSpanT
  have hSplitInv (v : QA) (j : QS) :
      eSplit.symm (v, j) =
        Ideal.Quotient.mk (Ideal.span {gT}) (v.out + aR * j.out) :=
    po_exteriorResidueProductEquiv_symm_mk R0 s I aR haR0 hSpanI hSpanT v j
  have hprodLE : Ideal.span {aR * gS} ≤ Ideal.span {aR} := by
    apply Ideal.span_singleton_le_span_singleton.mpr
    exact ⟨gS, by ring⟩
  let cR (d : QS) : S.R := h - aR * d.out
  let cond (d : QS) : Prop :=
    ∃ x : S.R, (h : F) - (a : F) * (d.out : F) =
      ((bc.gen s : Fˣ) : F) * (x : F)
  let phaseNeg (m : QT) (d : QS) : ℂ :=
    S.e A (S.diag (-((m.out : F) * (d.out : F)) / (gS : F)))
  let phaseH (m : QT) : ℂ :=
    S.e A (S.diag ((h : F) * (m.out : F) / ((gS : F) * (aR : F))))
  let phaseV (d : QS) (v : QA) : ℂ :=
    S.e A (S.diag ((cR d : F) * (v.out : F) / ((gS : F) * (aR : F))))
  let phaseJ (d : QS) (j : QS) : ℂ :=
    S.e A (S.diag ((cR d : F) * (j.out : F) / (gS : F)))
  let term (m : QT) (d : QS) : ℂ :=
    chiIdealPow D s.1 (d.out : F) 1 * phaseNeg m d *
      chiIdealPow D I.1 (m.out : F) 1 * phaseH m
  let K (d : QS) (v : QA) : ℂ :=
    chiIdealPow D s.1 (d.out : F) 1 * chiIdealPow D I.1 (v.out : F) 1 * phaseV d v
  let qminus : ℝ := qI s.1 ^ (-(1 / 2 : ℝ))
  have hEadd (x y : F) :
      S.e A (S.diag (x + y)) = S.e A (S.diag x) * S.e A (S.diag y) := by
    calc
      S.e A (S.diag (x + y)) = S.e A (S.diag x + S.diag y) := by rw [map_add]
      _ = S.e A (S.diag x) * S.e A (S.diag y) := po_e_add S A _ _
  have hGauss (m : QT) :
      finiteGauss R0 s (-(m.out : F)) =
        ∑ d : QS, chiIdealPow D s.1 (d.out : F) 1 * phaseNeg m d := by
    letI := R0.exterior.residueFinite s
    unfold finiteGauss finiteGaussAt
    rw [finsum_eq_sum_of_fintype]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [phaseNeg]
    rw [← hgSval]
    congr 1
    congr 1
    ring
  have hargPair (m : QT) (d : QS) :
      (h : F) * (m.out : F) / ((gS : F) * (aR : F)) +
          (-((m.out : F) * (d.out : F)) / (gS : F)) =
        (cR d : F) * (m.out : F) / ((gS : F) * (aR : F)) := by
    have hc : (cR d : F) = (h : F) - (aR : F) * (d.out : F) := by
      simp [cR]
    rw [hc]
    field_simp [haF0, hgS0] <;> ring
  have hpairPhase (m : QT) (d : QS) :
      phaseNeg m d * phaseH m =
        S.e A (S.diag ((cR d : F) * (m.out : F) / ((gS : F) * (aR : F)))) := by
    dsimp [phaseNeg, phaseH]
    calc
      _ = S.e A (S.diag ((h : F) * (m.out : F) / ((gS : F) * (aR : F)))) *
          S.e A (S.diag (-((m.out : F) * (d.out : F)) / (gS : F))) := by ring
      _ = S.e A (S.diag ((h : F) * (m.out : F) / ((gS : F) * (aR : F)) +
          (-((m.out : F) * (d.out : F)) / (gS : F)))) := (hEadd _ _).symm
      _ = _ := by rw [hargPair]
  have hterm (v : QA) (j : QS) (d : QS) :
      term (eSplit.symm (v, j)) d =
        chiIdealPow D s.1 (d.out : F) 1 *
          chiIdealPow D I.1 (v.out : F) 1 * phaseV d v * phaseJ d j := by
    let m : QT := eSplit.symm (v, j)
    have hmclass : Ideal.Quotient.mk (Ideal.span {gT}) (v.out + aR * j.out) = m :=
      (hSplitInv v j).symm
    have hclass : Ideal.Quotient.mk (Ideal.span {gT}) m.out =
        Ideal.Quotient.mk (Ideal.span {gT}) (v.out + aR * j.out) :=
      (Ideal.Quotient.mk_out m).trans hmclass.symm
    have hmem : m.out - (v.out + aR * j.out) ∈ Ideal.span {gT} :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hmOut : m.out = v.out + aR * j.out + r * gT := by
      calc
        m.out = (v.out + aR * j.out) + (m.out - (v.out + aR * j.out)) := by ring
        _ = (v.out + aR * j.out) + r * gT := by rw [← hr]
    have hmProd : m.out - (v.out + aR * j.out) ∈ Ideal.span {aR * gS} :=
      (congrArg (fun J : Ideal S.R => m.out - (v.out + aR * j.out) ∈ J) hSpanT).mp hmem
    have hDiffA : m.out - v.out ∈ Ideal.span {aR} := by
      rw [show m.out - v.out = (m.out - (v.out + aR * j.out)) + aR * j.out by ring]
      exact Ideal.add_mem _ (hprodLE hmProd)
        (Ideal.mem_span_singleton'.mpr ⟨j.out, by ring⟩)
    have hDiffI : m.out - v.out ∈ Ideal.span {gI} :=
      (congrArg (fun J : Ideal S.R => m.out - v.out ∈ J) hSpanI.symm).mp hDiffA
    have hchar : chiIdealPow D I.1 (m.out : F) 1 =
        chiIdealPow D I.1 (v.out : F) 1 :=
      po_chiIdealPow_eq_of_mod R0 I m.out v.out hDiffI
    have hmOutF : (m.out : F) = (v.out : F) + (aR : F) * (j.out : F) +
        (r : F) * (gT : F) := by
      have h := congrArg (fun z : S.R => (z : F)) hmOut
      simpa using h
    have harg : (cR d : F) * (m.out : F) / ((gS : F) * (aR : F)) =
        (cR d : F) * (v.out : F) / ((gS : F) * (aR : F)) +
          (cR d : F) * (j.out : F) / (gS : F) +
            (cR d : F) * (r : F) * (uInvR : F) := by
      rw [hmOutF, hgTval]
      field_simp [haF0, hgS0] <;> ring
    have hphase :
        S.e A (S.diag ((cR d : F) * (m.out : F) / ((gS : F) * (aR : F)))) =
          phaseV d v * phaseJ d j := by
      rw [harg]
      calc
        S.e A (S.diag ((cR d : F) * (v.out : F) / ((gS : F) * (aR : F)) +
            (cR d : F) * (j.out : F) / (gS : F) +
              (cR d : F) * (r : F) * (uInvR : F))) =
            S.e A (S.diag ((cR d : F) * (v.out : F) / ((gS : F) * (aR : F)) +
              (cR d : F) * (j.out : F) / (gS : F))) *
              S.e A (S.diag ((cR d : F) * (r : F) * (uInvR : F))) := by
                exact hEadd _ _
        _ = phaseV d v * phaseJ d j := by
          rw [hEadd]
          have hErr : (cR d : F) * (r : F) * (uInvR : F) =
              ((cR d * r * uInvR : S.R) : F) := by simp
          rw [hErr, po_e_diagR_one S D A (cR d * r * uInvR)]
          dsimp [phaseV, phaseJ]
          ring
    calc
      term (eSplit.symm (v, j)) d =
          chiIdealPow D s.1 (d.out : F) 1 *
            (phaseNeg m d * phaseH m) * chiIdealPow D I.1 (m.out : F) 1 := by
              dsimp [term]
              ring
      _ = chiIdealPow D s.1 (d.out : F) 1 *
            (S.e A (S.diag ((cR d : F) * (m.out : F) / ((gS : F) * (aR : F)))) *
              chiIdealPow D I.1 (v.out : F) 1) := by rw [hpairPhase, hchar]; ring
      _ = chiIdealPow D s.1 (d.out : F) 1 *
            chiIdealPow D I.1 (v.out : F) 1 * phaseV d v * phaseJ d j := by
              rw [hphase]
              ring
  have hSumJ (d : QS) (v : QA) :
      (∑ j : QS, term (eSplit.symm (v, j)) d) =
        K d v * ∑ j : QS, phaseJ d j := by
    calc
      _ = ∑ j : QS, K d v * phaseJ d j := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa [K] using hterm v j d
      _ = _ := by rw [← Finset.mul_sum (s := Finset.univ)]
  have hKsum (d : QS) :
      (∑ v : QA, K d v) = chiIdealPow D s.1 (d.out : F) 1 *
        ∑ v : QA, chiIdealPow D I.1 (v.out : F) 1 * phaseV d v := by
    dsimp [K]
    calc
      (∑ v : QA, chiIdealPow D s.1 (d.out : F) 1 *
          chiIdealPow D I.1 (v.out : F) 1 * phaseV d v) =
        ∑ v : QA, chiIdealPow D s.1 (d.out : F) 1 *
          (chiIdealPow D I.1 (v.out : F) 1 * phaseV d v) := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = chiIdealPow D s.1 (d.out : F) 1 *
          ∑ v : QA, chiIdealPow D I.1 (v.out : F) 1 * phaseV d v := by
            rw [← Finset.mul_sum (s := Finset.univ)]
  have horth (d : QS) :
      (∑ j : QS, phaseJ d j) =
        if cond d then (Ideal.absNorm s.1 : ℂ) else 0 := by
    simpa [phaseJ, cond, cR, gS, haR, hgSval] using
      (po_residue_addPhase_sum R0 s (cR d))
  have hArgV (d : QS) (x : S.R) (hx :
      (cR d : F) = (gS : F) * (x : F)) (v : QA) :
      (cR d : F) * (v.out : F) / ((gS : F) * (aR : F)) =
        (x : F) * (v.out : F) / (a : F) := by
    rw [hx, haR]
    field_simp [hgS0] <;> ring
  have hGaussAt (d : QS) (x : S.R) (hx :
      (cR d : F) = (gS : F) * (x : F)) :
      finiteGaussAt R0 I a (x : F) =
        ∑ v : QA, chiIdealPow D I.1 (v.out : F) 1 * phaseV d v := by
    have hraw := po_finiteGaussAt_quotientEq R0 I a aR haR hSpanI x
    rw [finsum_eq_sum_of_fintype] at hraw
    calc
      finiteGaussAt R0 I a (x : F) =
          ∑ v : QA, chiIdealPow D I.1 (v.out : F) 1 *
            S.e A (S.diag ((x : F) * (v.out : F) / (a : F))) := hraw
      _ = ∑ v : QA, chiIdealPow D I.1 (v.out : F) 1 * phaseV d v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← hArgV d x hx v]
  have hInner (d : QS) :
      (∑ v : QA, ∑ j : QS, term (eSplit.symm (v, j)) d) =
        if cond d then
          (Ideal.absNorm s.1 : ℂ) * chiIdealPow D s.1 (d.out : F) 1 *
            finiteGaussAt R0 I a
              (((h : F) - (a : F) * (d.out : F)) /
                ((bc.gen s : Fˣ) : F))
        else 0 := by
    by_cases hc : cond d
    · obtain ⟨x, hx⟩ := hc
      have hcond : cond d := ⟨x, hx⟩
      have hx' : (cR d : F) = (gS : F) * (x : F) := by
        simpa [cond, cR, haR, hgSval] using hx
      have hgauss := hGaussAt d x hx'
      have hdiv : (((h : F) - (a : F) * (d.out : F)) /
            ((bc.gen s : Fˣ) : F)) = (x : F) := by
        rw [← hgSval]
        have hcVal : (h : F) - (a : F) * (d.out : F) = (cR d : F) := by
          simp [cR, haR]
        rw [hcVal, hx']
        field_simp [hgS0]
      rw [if_pos hcond]
      calc
        _ = ∑ v : QA, K d v * ∑ j : QS, phaseJ d j := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hSumJ d v
        _ = ∑ v : QA, K d v * (Ideal.absNorm s.1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [horth, if_pos hcond]
        _ = (∑ v : QA, K d v) * (Ideal.absNorm s.1 : ℂ) := by
          rw [← Finset.sum_mul (s := Finset.univ)]
        _ = (Ideal.absNorm s.1 : ℂ) * chiIdealPow D s.1 (d.out : F) 1 *
            finiteGaussAt R0 I a
              (((h : F) - (a : F) * (d.out : F)) /
                ((bc.gen s : Fˣ) : F)) := by
          rw [hKsum, hdiv, ← hgauss]
          ring
    · rw [if_neg hc]
      calc
        _ = ∑ v : QA, K d v * ∑ j : QS, phaseJ d j := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hSumJ d v
        _ = ∑ v : QA, K d v * 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [horth, if_neg hc]
        _ = 0 := by simp
  have hFactor : finiteFactor R0 s I a (h : F) =
      ∑ d : QS, if cond d then
        chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R0 I a
          (((h : F) - (a : F) * (d.out : F)) / ((bc.gen s : Fˣ) : F))
      else 0 := by
    unfold finiteFactor
    simp only [finsum_eq_sum_of_fintype]
    rfl
  have hSumD :
      (∑ d : QS, ∑ v : QA, ∑ j : QS, term (eSplit.symm (v, j)) d) =
        (Ideal.absNorm s.1 : ℂ) * finiteFactor R0 s I a (h : F) := by
    calc
      _ = ∑ d : QS, if cond d then
            (Ideal.absNorm s.1 : ℂ) * chiIdealPow D s.1 (d.out : F) 1 *
              finiteGaussAt R0 I a
                (((h : F) - (a : F) * (d.out : F)) /
                  ((bc.gen s : Fˣ) : F))
          else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hInner d
      _ = (Ideal.absNorm s.1 : ℂ) *
          ∑ d : QS, if cond d then
            chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R0 I a
              (((h : F) - (a : F) * (d.out : F)) /
                ((bc.gen s : Fˣ) : F))
          else 0 := by
        calc
          _ = ∑ d : QS, (Ideal.absNorm s.1 : ℂ) *
              (if cond d then
                chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R0 I a
                  (((h : F) - (a : F) * (d.out : F)) /
                    ((bc.gen s : Fˣ) : F))
              else 0) := by
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hc : cond d <;> simp [hc] <;> ring
          _ = _ := by rw [← Finset.mul_sum (s := Finset.univ)]
      _ = (Ideal.absNorm s.1 : ℂ) * finiteFactor R0 s I a (h : F) := by
        rw [hFactor]
  have hMain :
      (∑ᶠ m : QT, (qminus : ℂ) * finiteGauss R0 s (-(m.out : F)) *
        chiIdealPow D I.1 (m.out : F) 1 *
          S.e A (S.diag ((h : F) * (m.out : F) /
            ((bc.gen s : F) * (a : F))))) =
        (qminus : ℂ) * ∑ d : QS, ∑ v : QA, ∑ j : QS,
          term (eSplit.symm (v, j)) d := by
    have hExpand (m : QT) :
        (qminus : ℂ) * finiteGauss R0 s (-(m.out : F)) *
          chiIdealPow D I.1 (m.out : F) 1 *
            S.e A (S.diag ((h : F) * (m.out : F) /
              ((bc.gen s : F) * (a : F)))) =
          (qminus : ℂ) * ∑ d : QS, term m d := by
      calc
        _ = (qminus : ℂ) *
            ((∑ d : QS, chiIdealPow D s.1 (d.out : F) 1 * phaseNeg m d) *
              (chiIdealPow D I.1 (m.out : F) 1 * phaseH m)) := by
          rw [hGauss m, ← hgSval, ← haR]
          ring
        _ = (qminus : ℂ) * ∑ d : QS,
            (chiIdealPow D s.1 (d.out : F) 1 * phaseNeg m d) *
              (chiIdealPow D I.1 (m.out : F) 1 * phaseH m) := by
          rw [Finset.sum_mul (s := Finset.univ)]
        _ = (qminus : ℂ) * ∑ d : QS, term m d := by
          congr 2
          funext d
          dsimp [term]
          ring
    rw [finsum_eq_sum_of_fintype]
    calc
      _ = ∑ m : QT, (qminus : ℂ) * ∑ d : QS, term m d := by
        apply Finset.sum_congr rfl
        intro m hm
        exact hExpand m
      _ = (qminus : ℂ) * ∑ m : QT, ∑ d : QS, term m d := by
        rw [← Finset.mul_sum (s := Finset.univ)]
      _ = (qminus : ℂ) * ∑ d : QS, ∑ m : QT, term m d := by
        rw [Finset.sum_comm]
      _ = (qminus : ℂ) * ∑ d : QS, ∑ v : QA, ∑ j : QS,
            term (eSplit.symm (v, j)) d := by
        congr 2
        funext d
        calc
          _ = ∑ p : QA × QS, term (eSplit.symm p) d :=
            Fintype.sum_bijective eSplit eSplit.bijective
              (fun m => term m d) (fun p => term (eSplit.symm p) d) (by
                intro p
                simp)
          _ = ∑ v : QA, ∑ j : QS, term (eSplit.symm (v, j)) d := by
            rw [Fintype.sum_prod_type]
  have hqpos : 0 < qI s.1 := by
    dsimp [qI]
    have hs0 : s.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using s.2.1
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨s.1, mem_nonZeroDivisors_iff_ne_zero.mpr hs0⟩
  have hpow : qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 =
      qI s.1 ^ (1 / 2 : ℝ) := by
    calc
      _ = qI s.1 ^ (-(1 / 2 : ℝ)) * qI s.1 ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = qI s.1 ^ (-(1 / 2 : ℝ) + 1) := by rw [← Real.rpow_add hqpos]
      _ = _ := by congr 1 <;> norm_num
  have hnormCast : (Ideal.absNorm s.1 : ℂ) = (qI s.1 : ℂ) := by simp [qI]
  have hscalar : (qminus : ℂ) * (Ideal.absNorm s.1 : ℂ) =
      (qI s.1 ^ (1 / 2 : ℝ) : ℝ) := by
    dsimp [qminus]
    rw [hnormCast, ← Complex.ofReal_mul, hpow]
  calc
    _ = (qminus : ℂ) * ∑ d : QS, ∑ v : QA, ∑ j : QS,
          term (eSplit.symm (v, j)) d := hMain
    _ = (qminus : ℂ) * (Ideal.absNorm s.1 : ℂ) * finiteFactor R0 s I a (h : F) := by
      rw [hSumD]
      ring
    _ = (qI s.1 ^ (1 / 2 : ℝ) : ℝ) * finiteFactor R0 s I a (h : F) := by
      rw [hscalar]

set_option maxHeartbeats 10000000 in
private theorem po_finiteFactor_gamma_invariant
    (s I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1)
    (hallowed : Bd.Allowed a) (h : S.R) (γ : Gamma S) :
    finiteFactor R s I a (((γ.1 : Fˣ) : F) * (h : F)) =
      finiteFactor R s I a (h : F) := by
  classical
  obtain ⟨eps, heps⟩ := γ.2
  have heps6 : eps ^ 6 = γ.1 := by simpa [sixthPowerOnUS] using heps
  let gammaF : Fˣ := (γ.1 : Fˣ)
  have hgammaF : gammaF = (eps : Fˣ) ^ 6 :=
    congrArg (fun u : S.US => (u : Fˣ)) heps6.symm
  let gammaR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F γ.1
  have hgammaRVal : ((gammaR : S.Rˣ) : F) = (gammaF : F) := by rfl
  obtain ⟨aR, haR, hSpanI, hSpanTotal, hu⟩ :=
    po_residueProductDecomp R s I a ha hallowed
  let gS : S.R := R.exterior.genR s
  have hgSval : (gS : F) = ((bc.gen s : Fˣ) : F) := R.exterior.genR_val s
  have hgS0 : (gS : F) ≠ 0 := by
    rw [hgSval]
    exact (bc.gen s).ne_zero
  have hgGen0 : (R.exterior.genR s : F) ≠ 0 := by
    simpa [gS] using hgS0
  let J : Ideal S.R := Ideal.span {gS}
  let Q := ResidueRing R.exterior s
  let qMap : S.R →+* Q := Ideal.Quotient.mk J
  let gammaQ : Qˣ := Units.map qMap gammaR
  letI : Fintype Q := R.exterior.residueFinite s
  let e : Q ≃ Q := {
    toFun d := (gammaQ : Q) * d
    invFun d := ((gammaQ⁻¹ : Qˣ) : Q) * d
    left_inv := by intro d; simp [mul_assoc]
    right_inv := by intro d; simp [mul_assoc] }
  have hEclass (d : Q) :
      e d = Ideal.Quotient.mk J ((gammaR : S.R) * d.out) := by
    simp [e, gammaQ, qMap, map_mul]
  let c0 (d : Q) : S.R := h - aR * d.out
  let cGamma (d : Q) : S.R := (gammaR : S.R) * h - aR * d.out
  let cond0 (d : Q) : Prop :=
    ∃ x : S.R, (h : F) - (a : F) * (d.out : F) =
      ((bc.gen s : Fˣ) : F) * (x : F)
  let condGamma (d : Q) : Prop :=
    ∃ x : S.R, ((gammaF : F) * (h : F)) - (a : F) * (d.out : F) =
      ((bc.gen s : Fˣ) : F) * (x : F)
  let arg0 (d : Q) : F :=
    ((h : F) - (a : F) * (d.out : F)) / ((bc.gen s : Fˣ) : F)
  let argGamma (d : Q) : F :=
    ((gammaF : F) * (h : F) - (a : F) * (d.out : F)) /
      ((bc.gen s : Fˣ) : F)
  let term0 (d : Q) : ℂ :=
    if cond0 d then
      chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R I a (arg0 d)
    else 0
  let termGamma (d : Q) : ℂ :=
    if condGamma d then
      chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R I a (argGamma d)
    else 0
  have hWitness (z : S.R) :
      (∃ x : S.R, (z : F) = (gS : F) * (x : F)) ↔ z ∈ J := by
    constructor
    · rintro ⟨x, hx⟩
      have hxR : z = gS * x := Subtype.ext hx
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨x, ?_⟩
      rw [hxR]
      ring
    · intro hz
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨x, ?_⟩
      have hcast := congrArg (fun z : S.R => (z : F)) hx
      calc
        (z : F) = (x : F) * (gS : F) := hcast.symm
        _ = (gS : F) * (x : F) := by ring
  have hCond0Mem (d : Q) : cond0 d ↔ c0 d ∈ J := by
    simpa [cond0, c0, haR, gS, R.exterior.genR_val] using hWitness (c0 d)
  have hCondGammaMem (d : Q) : condGamma d ↔ cGamma d ∈ J := by
    simpa [condGamma, cGamma, haR, hgammaRVal, gS, R.exterior.genR_val] using
      hWitness (cGamma d)
  have hFG0 : finiteFactor R s I a (h : F) = ∑ d : Q, term0 d := by
    unfold finiteFactor
    simp only [finsum_eq_sum_of_fintype]
    rfl
  have hFGamma : finiteFactor R s I a ((gammaF : F) * (h : F)) =
      ∑ d : Q, termGamma d := by
    unfold finiteFactor
    simp only [finsum_eq_sum_of_fintype]
    rfl
  have hpoint (d : Q) : term0 d = termGamma (e d) := by
    let d' : Q := e d
    have hclass : Ideal.Quotient.mk J d'.out =
        Ideal.Quotient.mk J ((gammaR : S.R) * d.out) := by
      calc
        Ideal.Quotient.mk J d'.out = d' := Ideal.Quotient.mk_out d'
        _ = Ideal.Quotient.mk J ((gammaR : S.R) * d.out) := hEclass d
    have hmem : d'.out - (gammaR : S.R) * d.out ∈ J :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hclass
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    have hdOut : d'.out = (gammaR : S.R) * d.out + r * gS := by
      calc
        d'.out = (gammaR : S.R) * d.out +
            (d'.out - (gammaR : S.R) * d.out) := by ring
        _ = (gammaR : S.R) * d.out + r * gS := by rw [← hr]
    have hcGamma : cGamma d' = (gammaR : S.R) * c0 d - aR * r * gS := by
      dsimp [cGamma, c0]
      rw [hdOut]
      ring
    have hArMem : aR * r * gS ∈ J := by
      have hgMem : gS ∈ J := Ideal.mem_span_singleton_self gS
      simpa [mul_assoc] using Ideal.mul_mem_left J (aR * r) hgMem
    have hCondEq : condGamma d' ↔ cond0 d := by
      rw [hCondGammaMem, hCond0Mem]
      constructor
      · intro hc
        have hmul : (gammaR : S.R) * c0 d ∈ J := by
          have hsum : (gammaR : S.R) * c0 d = cGamma d' + aR * r * gS := by
            rw [hcGamma]
            ring
          rw [hsum]
          exact Ideal.add_mem J hc hArMem
        have hinv := Ideal.mul_mem_left J ((gammaR⁻¹ : S.Rˣ) : S.R) hmul
        simpa [mul_assoc] using hinv
      · intro hc
        have hmul := Ideal.mul_mem_left J (gammaR : S.R) hc
        rw [hcGamma]
        exact Ideal.sub_mem J hmul hArMem
    have hcharRep : chiIdealPow D s.1 (d'.out : F) 1 =
        chiIdealPow D s.1 (((gammaR : S.R) * d.out : S.R) : F) 1 :=
      po_chiIdealPow_eq_of_mod R s d'.out ((gammaR : S.R) * d.out) hmem
    have hcharSix : chiIdealPow D s.1
        (((gammaR : S.R) * d.out : S.R) : F) 1 =
        chiIdealPow D s.1 (d.out : F) 1 := by
      have hGammaProd :
          (((gammaR : S.R) * d.out : S.R) : F) = (gammaF : F) * (d.out : F) := by
        simp [hgammaRVal]
      rw [hGammaProd, hgammaF]
      exact po_chiIdealPow_US_six D S s.1 s.2 eps d.out
    have hchar : chiIdealPow D s.1 (d'.out : F) 1 =
        chiIdealPow D s.1 (d.out : F) 1 := hcharRep.trans hcharSix
    by_cases hc : cond0 d
    · obtain ⟨x, hx⟩ := hc
      have hx0 : (c0 d : F) = (gS : F) * (x : F) := by
        simpa [c0, gS, haR, hgSval] using hx
      let xGamma : S.R := (gammaR : S.R) * x - aR * r
      have hxGamma : (cGamma d' : F) = (gS : F) * (xGamma : F) := by
        have h : (cGamma d' : F) =
            ((gammaR : S.R) : F) * (c0 d : F) -
              (aR : F) * (r : F) * (gS : F) := by
          simpa using congrArg (fun z : S.R => (z : F)) hcGamma
        rw [hx0] at h
        dsimp [xGamma]
        calc
          (cGamma d' : F) =
              ((gammaR : S.R) : F) * ((gS : S.R) : F) * (x : F) -
                (aR : F) * (r : F) * (gS : F) := by
                  simpa [mul_assoc] using h
          _ = (gS : F) *
                (((gammaR : S.R) : F) * (x : F) - (aR : F) * (r : F)) := by ring
          _ = (gS : F) * (xGamma : F) := by rfl
      have hcGamma' : condGamma d' := by
        refine ⟨xGamma, ?_⟩
        simpa [condGamma, cGamma, haR, hgammaRVal, gS, R.exterior.genR_val] using hxGamma
      have hArg0 : arg0 d = (x : F) := by
        dsimp [arg0]
        rw [← R.exterior.genR_val s]
        have hnum : (h : F) - (a : F) * (d.out : F) = (c0 d : F) := by
          simp [c0, haR]
        rw [hnum, hx0]
        dsimp [gS]
        field_simp [hgGen0]
      have hArgGamma : argGamma d' = (xGamma : F) := by
        dsimp [argGamma]
        rw [← R.exterior.genR_val s]
        have hnum : ((gammaF : F) * (h : F)) - (a : F) * (d'.out : F) =
            (cGamma d' : F) := by
          simp [cGamma, haR, hgammaRVal]
        rw [hnum, hxGamma]
        dsimp [gS]
        field_simp [hgGen0]
      let kGamma : S.R := (gammaR : S.R) * x
      have hKGamma : (kGamma : F) = ((gammaF : F) * (x : F)) := by
        simp [kGamma, hgammaRVal]
      have hXGamma : (xGamma : F) = (kGamma : F) + (a : F) * (-r : S.R) := by
        dsimp [xGamma, kGamma]
        rw [haR]
        ring
      have hGauss : finiteGaussAt R I a (x : F) =
          finiteGaussAt R I a (xGamma : F) := by
        calc
          finiteGaussAt R I a (x : F) =
              finiteGaussAt R I a ((gammaF : F) * (x : F)) :=
                (po_finiteGaussAt_gamma_scale R I a ha γ x).symm
          _ = finiteGaussAt R I a (kGamma : F) := by rw [hKGamma]
          _ = finiteGaussAt R I a ((kGamma : F) + (a : F) * (-r : S.R)) :=
                (po_finiteGaussAt_add_aR R I a kGamma (-r)).symm
          _ = finiteGaussAt R I a (xGamma : F) := by rw [hXGamma]
      have hArgGauss : finiteGaussAt R I a (arg0 d) =
          finiteGaussAt R I a (argGamma d') := by rw [hArg0, hArgGamma, hGauss]
      have hcond0 : cond0 d := ⟨x, hx⟩
      simp [term0, termGamma, d', hcond0, hcGamma', hchar, hArgGauss]
    · have hcGamma' : ¬ condGamma d' := by
        intro hcGamma'
        exact hc ((hCondEq).mp hcGamma')
      simp [term0, termGamma, d', hc, hcGamma']
  have hSum : (∑ d : Q, term0 d) = ∑ d : Q, termGamma d :=
    Fintype.sum_bijective e e.bijective term0 termGamma hpoint
  calc
    finiteFactor R s I a (((gammaF : F) * (h : F))) =
        ∑ d : Q, termGamma d := hFGamma
    _ = ∑ d : Q, term0 d := hSum.symm
    _ = finiteFactor R s I a (h : F) := hFG0.symm

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
  classical
  intro s I a ha hallowed h
  exact ⟨po_finite_poisson_identity R s I a ha hallowed h,
    po_finiteFactor_norm_le R s I a ha (h : F),
    fun γ => po_finiteFactor_gamma_invariant R s I a ha hallowed h γ⟩
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
  constructor
  · intro v σ hσ
    let f : v.1.adicCompletion F → ℂ := (W.finite v).1
    obtain ⟨k, hperiod⟩ := ArtinPrimitiveRoots.Proofs.a2_weights.finiteTest_exists_period_ball
      v.1 f (W.finite v).2.2.2 (W.finite v).2.2.1
    have hcompact : HasCompactSupport
        (ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1) f) := by
      exact ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier_hasCompactSupport_of_period
        v.1 A (μ v.1) f k hperiod
    have hcontinuous : Continuous
        (ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1) f) :=
      (ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier_isLocallyConstant
        v.1 A (μ v.1) f (W.finite v).2.2.1).continuous
    simpa [ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier, f] using
      (ArtinPrimitiveRoots.Proofs.a2_weights.finiteWeightedIntegrable_of_continuous_compact
        v.1 (μ v.1) (ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier v.1 A (μ v.1) f)
        hcontinuous hcompact σ hσ)
  · intro w j σ hσ
    exact ArtinPrimitiveRoots.Proofs.a2_weights.complexFourierDerivative_integrable
      (W.arch w) j σ hσ
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
