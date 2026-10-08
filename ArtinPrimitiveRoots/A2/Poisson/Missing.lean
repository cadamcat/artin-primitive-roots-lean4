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
  obtain ⟨c, hc, hFE⟩ :=
    ArtinPrimitiveRoots.Proofs.a2_weights.finiteLocalFunctionalEquation_all v A (μ v)
  refine ⟨c, hc, ?_⟩
  intro f hf hfc hflc s hs h1s
  simpa [ArtinPrimitiveRoots.Proofs.a2_weights.finiteFourier] using
    hFE f hf hfc hflc s hs h1s
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
private instance eulerResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
private noncomputable instance eulerResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private lemma euler_count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma euler_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma euler_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
    euler_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    euler_count_spanSingleton_eq_neg_log_intValuation v n hn,
    euler_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma euler_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

/-- po:C-local-values: the one-prime T_v table, including the masked v≡0 case. -/
theorem po_C_local_T_values : ∀ v, v ∉ S.Sf → ∀ e : ℤ, ∀ y : S.R,
  localT R v e (y : F) =
    (if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e * localT R v e 1
      else if e % 6 = 0 then qI v.asIdeal - 1 else 0) ∧
  (e % 6 ≠ 0 → ‖localT R v e 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ)) ∧ localT R v 0 1 = -1 := by
  intro v hv e y
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let SB := a2_bridge_SYMBOL D S
  let p : Fˣ := primeGen R v
  have hp0 : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v hv)).1
    simpa [p, primeGen, hv, R.exterior.prime_val] using h
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp0.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := euler_count_spanSingleton_eq_neg_log_valuation v (p : F) hp0.2.1
    rw [hcountP] at h
    linarith
  have hvalP : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hp0.2.1
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hpvalne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  obtain ⟨hchars, hchiSix, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp0
  obtain ⟨χ₁, hχ₁order, hχ₁eval⟩ := hchiSix
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  obtain ⟨χe, hχeeval⟩ := hchars e
  have hresAlg (x : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hmulchar_zpow (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
      (u : (𝓞 F ⧸ v.asIdeal)ˣ) : χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = χ u ^ e := by
    have h := χ.toUnitHom.map_zpow u e
    calc
      χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = (χ.toUnitHom (u ^ e) : ℂ) :=
        (MulChar.coe_toUnitHom χ (u ^ e)).symm
      _ = (χ.toUnitHom u : ℂ) ^ e := by
        simpa only [Units.val_zpow_eq_zpow_val] using congrArg Units.val h
      _ = χ u ^ e := by rw [MulChar.coe_toUnitHom]
  have hχpow_eq : χe = χ₁ ^ e := by
    apply MulChar.ext
    intro u
    have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact u.ne_zero
    calc
      χe (u : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
      _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
        SB.chiPow_nonzero v _ e hu
      _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 ^ e := by
        rw [SB.chiPow_nonzero v _ 1 hu, zpow_one]
      _ = χ₁ (u : 𝓞 F ⧸ v.asIdeal) ^ e := by rw [hχ₁eval]
      _ = χ₁ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) := (hmulchar_zpow χ₁ u).symm
      _ = (χ₁ ^ e) (u : 𝓞 F ⧸ v.asIdeal) :=
        (MulChar.zpow_apply_coe χ₁ e u).symm
  have hχe_one : e % 6 = 0 → χe = 1 := by
    intro he
    have hdvd : (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.mpr he
    have horderDvd : (orderOf χ₁ : ℤ) ∣ e := by rw [hχ₁order]; exact hdvd
    have hpow : χ₁ ^ e = 1 := (orderOf_dvd_iff_zpow_eq_one).mp horderDvd
    rw [hχpow_eq, hpow]
  have hχe_ne_one : e % 6 ≠ 0 → χe ≠ 1 := by
    intro he hχ
    have hpow : χ₁ ^ e = 1 := hχpow_eq.symm.trans hχ
    have hdvd : (orderOf χ₁ : ℤ) ∣ e := (orderOf_dvd_iff_zpow_eq_one).mpr hpow
    rw [hχ₁order] at hdvd
    exact he (Int.dvd_iff_emod_eq_zero.mp hdvd)
  have hphaseErr (z : F)
      (hz : HeightOneSpectrum.valuation F v z ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z / (p : F))) = 1 := by
    have hvalDiv : HeightOneSpectrum.valuation F v (z / (p : F)) ≤ 1 := by
      rw [map_div₀, hvalP]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hz
    have hlocal : algebraMap F (v.adicCompletion F) (z / (p : F)) ∈
        v.adicCompletionIntegers F := by
      change ((z / (p : F) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    exact A.integral v _ hlocal
  have hphaseCongr (z₁ z₂ : F)
      (hz : HeightOneSpectrum.valuation F v (z₁ - z₂) ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
    have harg : algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F)) =
        algebraMap F (v.adicCompletion F) (z₁ / (p : F)) -
          algebraMap F (v.adicCompletion F) (z₂ / (p : F)) := by
      have hF : (z₁ - z₂) / (p : F) = z₁ / (p : F) - z₂ / (p : F) := by
        field_simp [Units.ne_zero p]
      rw [hF, map_sub]
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) (z₁ / (p : F)))
      (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))
    have hz₂ : A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
          (A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) /
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))) *
              A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) :=
        (div_mul_cancel₀ _ hz₂).symm
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F))) *
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [hphaseErr (z₁ - z₂) hz, one_mul]
  have hphase (y : S.R) (x : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
        ψ (-(residue v (y : F)) * x) := by
    have hyval : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
    obtain ⟨ay, dy, hdy⟩ := v.exists_primeCompl_mul_eq_of_integer (y : F) hyval
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have hdyNot : dy.1 ∉ v.asIdeal := by
      exact Ideal.mem_primeCompl_iff.mp dy.2
    have hresY : residue v (y : F) =
        Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy :=
      euler_residue_rep v (y : F) ay dy.1 hdyNot hdy
    let b : 𝓞 F := (-a).out
    have hdq : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
      intro hzero
      exact hdyNot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have hmkB : Ideal.Quotient.mk v.asIdeal b = -a := by
      simp [b]
    have hmk : Ideal.Quotient.mk v.asIdeal (ay + b * dy) = 0 := by
      calc
        Ideal.Quotient.mk v.asIdeal (ay + b * dy) =
            Ideal.Quotient.mk v.asIdeal ay +
              Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by simp
        _ = (Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy +
              Ideal.Quotient.mk v.asIdeal b) * Ideal.Quotient.mk v.asIdeal dy := by
          have hcancel : (Ideal.Quotient.mk v.asIdeal ay /
              Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy =
                Ideal.Quotient.mk v.asIdeal ay := div_mul_cancel₀ _ hdq
          calc
            _ = (Ideal.Quotient.mk v.asIdeal ay /
                Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy +
                  Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by rw [hcancel]
            _ = _ := by ring
        _ = (residue v (y : F) + Ideal.Quotient.mk v.asIdeal b) *
              Ideal.Quotient.mk v.asIdeal dy := by rw [hresY]
        _ = 0 := by rw [hmkB]; ring
    have hmem : ay + b * dy ∈ v.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    have hvalNum : HeightOneSpectrum.valuation F v
        (algebraMap (𝓞 F) F (ay + b * dy)) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (ay + b * dy) 1).2
      simpa using hmem
    have hvalDy : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_eq_one_iff_mem_primeCompl dy.1).2 dy.2
    have hmul : ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
        algebraMap (𝓞 F) F (ay + b * dy) := by
      calc
        ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
            (y : F) * algebraMap (𝓞 F) F dy +
              (b : F) * algebraMap (𝓞 F) F dy := by ring
        _ = algebraMap (𝓞 F) F ay + algebraMap (𝓞 F) F (b * dy) := by
          rw [hdy, map_mul]
        _ = algebraMap (𝓞 F) F (ay + b * dy) := by rw [map_add]
    have hvalYb : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) ≤
        WithZero.exp (-1 : ℤ) := by
      have heq : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) =
          HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F (ay + b * dy)) := by
        calc
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) * 1 := by simp
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
                HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) := by rw [hvalDy]
          _ = HeightOneSpectrum.valuation F v
                (((y : F) + (b : F)) * algebraMap (𝓞 F) F dy) := by
            rw [(v.valuation F).map_mul]
          _ = _ := by rw [hmul]
      rw [heq]
      exact hvalNum
    have hvalErr : HeightOneSpectrum.valuation F v
        (-(y : F) * algebraMap (𝓞 F) F x.out - (b : F) * algebraMap (𝓞 F) F x.out) ≤
          WithZero.exp (-1 : ℤ) := by
      have hident : -(y : F) * algebraMap (𝓞 F) F x.out -
          (b : F) * algebraMap (𝓞 F) F x.out =
            -(((y : F) + (b : F)) * algebraMap (𝓞 F) F x.out) := by ring
      rw [hident, (v.valuation F).map_neg, (v.valuation F).map_mul]
      have hxval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤ 1 :=
        v.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
            HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤
            WithZero.exp (-1 : ℤ) * 1 :=
          mul_le_mul hvalYb hxval (zero_le) (zero_le)
        _ = WithZero.exp (-1 : ℤ) := mul_one _
    have hphase' := hphaseCongr
      (-(y : F) * algebraMap (𝓞 F) F x.out)
      ((b : F) * algebraMap (𝓞 F) F x.out) hvalErr
    have harg : -((y : F) * algebraMap (𝓞 F) F x.out / (p : F)) =
        (-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F) := by ring
    calc
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := by rw [harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (((b : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := hphase'
      _ = ψ (-(residue v (y : F)) * x) := by
        symm
        simpa [a, b, mul_comm] using hψeval (-a) x
  have hfiniteT (y : S.R) : localT R v e (y : F) =
      ∑ x : 𝓞 F ⧸ v.asIdeal,
        χe x * ψ (-(residue v (y : F)) * x) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = χe x * A.ψ v (algebraMap F (v.adicCompletion F)
          (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) := by
        rw [← hχeeval x]
      _ = _ := by rw [hphase y x]
  have hresOne : residue v (1 : F) = 1 := by
    simpa using SB.residue_algebraMap v (1 : 𝓞 F)
  have hresZero : residue v (0 : F) = 0 := by
    simpa using SB.residue_algebraMap v (0 : 𝓞 F)
  have hfiniteShift (y : S.R) : localT R v e (y : F) =
      gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
    calc
      localT R v e (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
          χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
      _ = gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
        simp [gaussSum, AddChar.mulShift_apply]
  have hfiniteOne : localT R v e 1 = gaussSum χe (ψ.mulShift (-1)) := by
    simpa [hresOne] using hfiniteShift (1 : S.R)
  have hχ₁minus : χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) = -1 := by
      simpa using hresAlg (-1 : 𝓞 F ⧸ v.asIdeal)
    have hresNeg : residue v (-1 : F) = -1 := by
      simpa using SB.residue_algebraMap v (-1 : 𝓞 F)
    calc
      χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 1 := hχ₁eval _
      _ = chi D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) :=
        by simpa [pow_one] using
          SB.chiPow_nonzero v _ 1 (by rw [hres]; exact neg_ne_zero.mpr one_ne_zero)
      _ = chi D v (-1 : F) := SB.chi_congr v _ _ (hres.trans hresNeg.symm)
      _ = 1 := SB.chi_minus_one v hv
  have hχeminus : χe (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hχ₁unit : χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχ₁minus
    calc
      χe (-1 : 𝓞 F ⧸ v.asIdeal) = χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by simp
      _ = (χ₁ ^ e) (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by rw [hχpow_eq]
      _ = χ₁ ((↑((-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e) : 𝓞 F ⧸ v.asIdeal)) :=
        MulChar.zpow_apply_coe χ₁ e (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
      _ = χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e := hmulchar_zpow χ₁ (-1)
      _ = 1 := by rw [hχ₁unit]; simp
  have hshiftGauss : gaussSum χe (ψ.mulShift (-1)) = gaussSum χe ψ := by
    have h := gaussSum_mulShift_eq χe ψ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
    have hχeunit : χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχeminus
    have hinvχ : χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      calc
        χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) =
            (χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ))⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = 1 := by rw [hχeunit]; simp
    calc
      gaussSum χe (ψ.mulShift (-1)) = χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) *
          gaussSum χe ψ := h
      _ = gaussSum χe ψ := by rw [hinvχ, one_mul]
  have hfiniteOneGauss : localT R v e 1 = gaussSum χe ψ := hfiniteOne.trans hshiftGauss
  have hscale : residue v (y : F) ≠ 0 →
      localT R v e (y : F) =
        star (chi D v (y : F)) ^ e * localT R v e 1 := by
    intro hy
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have ha : a ≠ 0 := by simpa [a] using hy
    let u : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ha).unit
    have hu : (u : 𝓞 F ⧸ v.asIdeal) = a :=
      (isUnit_iff_ne_zero.mpr ha).unit_spec
    have hshift : ψ.mulShift (-a) = (ψ.mulShift (-1)).mulShift (u : 𝓞 F ⧸ v.asIdeal) := by
      ext x
      simp [AddChar.mulShift_apply, hu, mul_assoc]
    have hsum := gaussSum_mulShift_eq χe (ψ.mulShift (-1)) u
    have hunitGauss : gaussSum χe (ψ.mulShift (-a)) =
        χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := by
      rw [hshift]
      exact hsum
    have hchiA : χe u = chi D v (y : F) ^ e := by
      have hresu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
          residue v (y : F) := by rw [hresAlg, hu]
      have hresu_ne : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresu]
        exact hy
      calc
        χe u = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
        _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
          SB.chiPow_nonzero v _ e hresu_ne
        _ = chi D v (y : F) ^ e := by rw [SB.chi_congr v _ _ hresu]
    have hnormChi : ‖chi D v (y : F)‖ = 1 := SB.chi_norm v _ hy
    have hnormPow : ‖chi D v (y : F) ^ e‖ = 1 := by
      rw [Complex.norm_zpow, hnormChi]
      norm_num
    have hinv : (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F)) ^ e := by
      calc
        (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F) ^ e) :=
          Complex.inv_eq_conj hnormPow
        _ = star (chi D v (y : F)) ^ e := by simp
    have hχinv : χe⁻¹ u = star (chi D v (y : F)) ^ e := by
      calc
        χe⁻¹ u = (χe u)⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = star (chi D v (y : F)) ^ e := by rw [hchiA, hinv]
    calc
      localT R v e (y : F) = gaussSum χe (ψ.mulShift (-a)) := by
        simpa [a] using hfiniteShift y
      _ = χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := hunitGauss
      _ = star (chi D v (y : F)) ^ e * localT R v e 1 := by
        rw [hχinv, ← hfiniteOne]
  have hzeroSum : localT R v e (0 : F) =
      (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
    have hsum : localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := by
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χe x * ψ (-(residue v (0 : F)) * x) := by
          simpa [hresZero] using hfiniteT (0 : S.R)
        _ = _ := by simp [hresZero]
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hcardPos : 1 ≤ Ideal.absNorm v.asIdeal := by
      have h : 1 ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
        exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
      rw [hcard] at h
      exact h
    by_cases he : e % 6 = 0
    · have hunitCard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
        calc
          Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ :=
          Nat.card_eq_fintype_card
          _ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 := Fintype.card_units (α := 𝓞 F ⧸ v.asIdeal)
          _ = Ideal.absNorm v.asIdeal - 1 := by rw [hcard]
      have hunitReal : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℝ) = qI v.asIdeal - 1 := by
        rw [hunitCard]
        dsimp [qI]
        rw [Nat.cast_sub hcardPos]
        norm_num
      have hunitComplex : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) =
          (qI v.asIdeal : ℂ) - 1 := by exact_mod_cast hunitReal
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = ∑ x : 𝓞 F ⧸ v.asIdeal,
              (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hχe_one he]
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by simp [gaussSum]
        _ = (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) := by rw [gaussSum_one_one]
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
          simpa [he] using hunitComplex
    ·
      have hsumZero : (∑ x : 𝓞 F ⧸ v.asIdeal, χe x) = 0 := by
        simpa [gaussSum] using (MulChar.sum_eq_zero_of_ne_one (hχe_ne_one he))
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = 0 := hsumZero
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by simp [he]
  constructor
  · by_cases hy : residue v (y : F) ≠ 0
    · simpa [hy] using hscale hy
    · have hresY0 : residue v (y : F) = 0 := by simpa using hy
      have hfiniteTzero : localT R v e (0 : F) =
          ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
        simpa using hfiniteT (0 : S.R)
      have hlocalY0 : localT R v e (y : F) = localT R v e (0 : F) := by
        calc
          localT R v e (y : F) =
              ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
          _ = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
            rw [hresY0, hresZero]
          _ = localT R v e (0 : F) := hfiniteTzero.symm
      calc
        localT R v e (y : F) = localT R v e (0 : F) := hlocalY0
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := hzeroSum
        _ = if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e *
              localT R v e 1 else if e % 6 = 0 then qI v.asIdeal - 1 else 0 := by
          have hdiv : (e % 6 = 0) ↔ (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.symm
          have hresNot : ¬(residue v (y : F) ≠ 0) := by simp [hresY0]
          by_cases h : (6 : ℤ) ∣ e
          · rw [if_pos (hdiv.mpr h), if_pos (hdiv.mpr h)]
            rw [if_neg hresNot]
            exact Complex.ofReal_sub _ _
          · rw [if_neg (fun he => h (hdiv.mp he)), if_neg (fun he => h (hdiv.mp he))]
            rw [if_neg hresNot]
            rfl
  constructor
  · intro he
    have hχne := hχe_ne_one he
    have hlocalEq : localT R v e 1 = gaussSum χe ψ := hfiniteOneGauss
    have hprod : gaussSum χe ψ * star (gaussSum χe ψ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        gaussSum χe ψ * star (gaussSum χe ψ) =
            gaussSum χe ψ * gaussSum χe⁻¹ ψ⁻¹ := by rw [star_gaussSum_eq]
        _ = _ := gaussSum_mul_gaussSum_eq_card hχne hψprim
    have hnormSqC : (Complex.normSq (gaussSum χe ψ) : ℂ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        (Complex.normSq (gaussSum χe ψ) : ℂ) =
            gaussSum χe ψ * star (gaussSum χe ψ) := (Complex.mul_conj _).symm
        _ = _ := hprod
    have hnormSq : ‖gaussSum χe ψ‖ ^ 2 =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast hnormSqC
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hnormSqQ : ‖gaussSum χe ψ‖ ^ 2 = qI v.asIdeal := by
      rw [hnormSq, hcard]
      rfl
    have hnormG : ‖gaussSum χe ψ‖ = qI v.asIdeal ^ (1 / 2 : ℝ) := by
      calc
        ‖gaussSum χe ψ‖ = Real.sqrt (‖gaussSum χe ψ‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        _ = Real.sqrt (qI v.asIdeal) := by rw [hnormSqQ]
        _ = qI v.asIdeal ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    simpa [hlocalEq] using hnormG
  · obtain ⟨χ0, hχ0eval⟩ := hchars (0 : ℤ)
    have hχ0one : χ0 = 1 := by
      apply MulChar.ext
      intro u
      have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresAlg]
        exact u.ne_zero
      rw [hχ0eval u, SB.chiPow_nonzero v _ 0 hu, zpow_zero]
      simp
    have hfiniteT0 (y : S.R) : localT R v 0 (y : F) =
        ∑ x : 𝓞 F ⧸ v.asIdeal, χ0 x * ψ (-(residue v (y : F)) * x) := by
      unfold localT
      rw [a2_bridge_FINITE_CHAR_finsum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hχ0eval x, hphase y x]
    have hfiniteShift0 (y : S.R) : localT R v 0 (y : F) =
        gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
      calc
        localT R v 0 (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χ0 x * ψ (-(residue v (y : F)) * x) := hfiniteT0 y
        _ = gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
          simp [gaussSum, AddChar.mulShift_apply]
    have hlocalZero : localT R v 0 1 =
        gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
          (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)) := by
      calc
        localT R v 0 1 = gaussSum χ0 (ψ.mulShift (-1)) := by
          simpa [hresOne] using hfiniteShift0 (1 : S.R)
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (ψ.mulShift (-1)) := by rw [hχ0one]
    have hψshiftPrim : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).IsPrimitive := by
      intro a ha htriv
      have hnonzero : (-1 : 𝓞 F ⧸ v.asIdeal) * a ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha
      have htriv' : ψ.mulShift ((-1 : 𝓞 F ⧸ v.asIdeal) * a) = 1 := by
        simpa only [AddChar.mulShift_mulShift] using htriv
      exact (hψprim hnonzero) htriv'
    have hψshiftNe : ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal) ≠ 1 := by
      intro h
      have h' : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).mulShift 1 = 1 := by
        simpa using h
      exact (hψshiftPrim one_ne_zero) h'
    rw [hlocalZero]
    exact gaussSum_one_left hψshiftNe

/-- po:C-local-values, 05:552–595. At J=t-1 use J+1-t, not saturated J-t+1. -/
private lemma euler_generators_unit_ratio (I : Ideal (𝓞 F))
    (x y : F) (hx : S.IsGen x I) (hy : S.IsGen y I) :
    ∃ u : S.US, x = (u : Fˣ) * y := by
  have hxy0 : x / y ≠ 0 := div_ne_zero hx.2.1 hy.2.1
  let r : Fˣ := Units.mk0 (x / y) hxy0
  have hrVal : ∀ w : FinPlace F, w ∉ S.Sf →
      HeightOneSpectrum.valuation F w (r : Fˣ) = 1 := by
    intro w hw
    have hcountW : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) = 0 := by
      rw [euler_count_spanSingleton_div w x y hx.2.1 hy.2.1,
        hx.2.2 w hw, hy.2.2 w hw]
      ring
    have hlogW : WithZero.log (HeightOneSpectrum.valuation F w (x / y)) = 0 := by
      have h := euler_count_spanSingleton_eq_neg_log_valuation w (x / y) hxy0
      rw [hcountW] at h
      omega
    have hne : HeightOneSpectrum.valuation F w (x / y) ≠ 0 :=
      (w.valuation F).ne_zero_iff.mpr hxy0
    calc
      HeightOneSpectrum.valuation F w (r : Fˣ) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F w (x / y))) := by
        change HeightOneSpectrum.valuation F w (x / y) = _
        exact (WithZero.exp_log hne).symm
      _ = 1 := by rw [hlogW]; simp
  have hrUnit : r ∈ S.US := by
    change r ∈ (S.Sf : Set (FinPlace F)).unit F
    exact hrVal
  refine ⟨⟨r, hrUnit⟩, ?_⟩
  change x = (r : Fˣ) * y
  dsimp [r]
  field_simp [hy.2.1]

private lemma euler_residue_add_integral (v : FinPlace F) (x y : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1)
    (hy : HeightOneSpectrum.valuation F v y ≤ 1) :
    residue v (x + y) = residue v x + residue v y := by
  letI := eulerResidueMaximal v
  letI := eulerResidueField v
  obtain ⟨a, b, hxb⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  obtain ⟨c, d, hyd⟩ := v.exists_primeCompl_mul_eq_of_integer y hy
  have hbd : b.1 * d.1 ∉ v.asIdeal := by
    intro hmem
    rcases v.isPrime.mem_or_mem hmem with hb | hd
    · exact b.2 hb
    · exact d.2 hd
  have hsumrep : (x + y) * algebraMap (𝓞 F) F (b.1 * d.1) =
      algebraMap (𝓞 F) F (a * d.1 + c * b.1) := by
    calc
      (x + y) * algebraMap (𝓞 F) F (b.1 * d.1) =
          x * algebraMap (𝓞 F) F b.1 * algebraMap (𝓞 F) F d.1 +
            y * algebraMap (𝓞 F) F d.1 * algebraMap (𝓞 F) F b.1 := by
        rw [map_mul]
        ring
      _ = algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F d.1 +
            algebraMap (𝓞 F) F c * algebraMap (𝓞 F) F b.1 := by
        rw [hxb, hyd]
      _ = algebraMap (𝓞 F) F (a * d.1 + c * b.1) := by
        rw [map_add, map_mul, map_mul]
  have hbnot : b.1 ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp b.property
  have hdnot : d.1 ∉ v.asIdeal := Ideal.mem_primeCompl_iff.mp d.property
  have hbq : Ideal.Quotient.mk v.asIdeal b.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hbnot
  have hdq : Ideal.Quotient.mk v.asIdeal d.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hdnot
  calc
    residue v (x + y) = Ideal.Quotient.mk v.asIdeal (a * d.1 + c * b.1) /
        Ideal.Quotient.mk v.asIdeal (b.1 * d.1) :=
      euler_residue_rep v (x + y) (a * d.1 + c * b.1) (b.1 * d.1) hbd hsumrep
    _ = residue v x + residue v y := by
      rw [euler_residue_rep v x a b.1 hbnot hxb,
        euler_residue_rep v y c d.1 hdnot hyd]
      simp only [map_add, map_mul]
      field_simp [hbq, hdq]

private lemma euler_span_singleton_eq_of_generators (v : FinPlace F) (hv : v ∉ S.Sf)
    (I : Ideal (𝓞 F)) (x y : S.R)
    (hx : S.IsGen (x : F) I) (hy : S.IsGen (y : F) I) :
    Ideal.span ({x} : Set S.R) = Ideal.span {y} := by
  classical
  rcases euler_generators_unit_ratio I (x : F) (y : F) hx hy with ⟨u, hu⟩
  let uR : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F u
  have huF : (uR : F) = (u : Fˣ) := rfl
  have hrel : x = uR * y := by
    apply Subtype.ext
    change (x : F) = (uR : F) * (y : F)
    rw [huF]
    exact hu
  calc
    Ideal.span ({x} : Set S.R) = Ideal.span {uR * y} := by rw [hrel]
    _ = Ideal.span {y} := Ideal.span_singleton_mul_left_unit uR.isUnit y

private lemma euler_prime_power_associated (v : FinPlace F) (hv : v ∉ S.Sf) (k : ℕ) :
    ∃ (u : S.US) (c : S.Rˣ),
      (primeGen R v : F) ^ k = (c : F) *
        (R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k) : F) := by
  classical
  let pi := R.exterior.prime v hv
  let I := R.exterior.pow pi k
  let p := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  have hIideal : I.1 = v.asIdeal ^ k := by
    change (R.exterior.pow pi k).1 = _
    rw [R.exterior.pow_val, R.exterior.prime_val]
  have hIcoerce : (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k := by
    calc
      (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          ((v.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        congrArg (fun J : Ideal (𝓞 F) =>
          (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) hIideal
      _ = (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k :=
        FractionalIdeal.coeIdeal_pow (nonZeroDivisors (𝓞 F)) F v.asIdeal k
  have hpPow : S.IsGen ((p : F) ^ k) I.1 := by
    refine ⟨I.2, pow_ne_zero k hp.2.1, ?_⟩
    intro w hw
    have hsp : FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((p : F) ^ k)) =
        (k : ℤ) * FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) := by
      rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
    calc
      FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((p : F) ^ k)) =
          (k : ℤ) * FractionalIdeal.count F w
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) := hsp
      _ = (k : ℤ) * FractionalIdeal.count F w
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
          rw [hp.2.2 w hw]
      _ = FractionalIdeal.count F w
            ((v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ k) := by
          rw [FractionalIdeal.count_pow]
      _ = FractionalIdeal.count F w
            (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by rw [← hIcoerce]
  have hgen : S.IsGen (R.exterior.genR I : F) I.1 := by
    rw [R.exterior.genR_val I]
    exact (bc.gen_spec I).1
  rcases euler_generators_unit_ratio I.1 ((p : F) ^ k)
      (R.exterior.genR I : F) hpPow hgen with ⟨u, hu⟩
  let c : S.Rˣ := Set.unitEquivUnitsInteger (S.Sf : Set (FinPlace F)) F u
  have hcF : (c : F) = (u : Fˣ) := rfl
  refine ⟨u, c, ?_⟩
  change (p : F) ^ k = (c : F) * (R.exterior.genR I : F)
  rw [hcF]
  exact hu

private lemma euler_prime_power_quotient_generator (v : FinPlace F) (hv : v ∉ S.Sf)
    (k : ℕ) :
    ∃ (u : S.US) (c : S.Rˣ) (pR : S.R),
      (primeGen R v : F) ^ k = (pR : F) ∧
      pR = (c : S.R) * R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k) := by
  obtain ⟨u, c, hc⟩ := euler_prime_power_associated R v hv k
  refine ⟨u, c, (c : S.R) *
    R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) k), ?_, rfl⟩
  exact hc

private lemma euler_power_divisibility_iff (p : Fˣ) (k : ℕ) (pR : S.R)
    (hpR : (p : F) ^ k = (pR : F)) (A0 : S.R) :
    (∃ x : S.R, (A0 : F) = (p : F) ^ k * (x : F)) ↔
      A0 ∈ Ideal.span ({pR} : Set S.R) := by
  constructor
  · rintro ⟨x, hx⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (A0 : F) = (pR : F) * (x : F)
    rw [← hpR]
    exact hx
  · intro hA
    rcases Ideal.mem_span_singleton.mp hA with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have hxF : (A0 : F) = (pR : F) * (x : F) := congrArg (fun z : S.R => (z : F)) hx
    simpa [← hpR] using hxF

private lemma euler_residue_card_pow (v : FinPlace F) (hv : v ∉ S.Sf) (k : ℕ) :
    @Fintype.card (ResidueRing R.exterior
      (R.exterior.pow (R.exterior.prime v hv) k))
      (R.exterior.residueFinite (R.exterior.pow (R.exterior.prime v hv) k)) =
      Ideal.absNorm v.asIdeal ^ k := by
  let pi := R.exterior.prime v hv
  let I := R.exterior.pow pi k
  have hI : I.1 = v.asIdeal ^ k := by
    change (R.exterior.pow pi k).1 = _
    rw [R.exterior.pow_val, R.exterior.prime_val]
  calc
    @Fintype.card _ (R.exterior.residueFinite I) = Ideal.absNorm I.1 :=
      R.exterior.residue_card I
    _ = Ideal.absNorm (v.asIdeal ^ k) := by rw [hI]
    _ = Ideal.absNorm v.asIdeal ^ k := map_pow Ideal.absNorm v.asIdeal k

private lemma euler_finsum_unique {α : Type} [Fintype α] [Unique α] (f : α → ℂ) :
    (∑ᶠ x, f x) = f default := by
  rw [finsum_eq_sum_of_fintype, Fintype.sum_unique]

private lemma euler_addchar_one_of_S_R (v : FinPlace F) (hv : v ∉ S.Sf) (x : S.R) :
    A.ψ v (algebraMap F (v.adicCompletion F) (x : F)) = 1 := by
  have hxval : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hv
  have hxint : algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
    change ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxval
  exact A.integral v _ hxint

private lemma euler_primeGen_valuation (v : FinPlace F) (hv : v ∉ S.Sf) :
    HeightOneSpectrum.valuation F v (primeGen R v : F) = WithZero.exp (-1 : ℤ) := by
  let pi := R.exterior.prime v hv
  let p := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlog : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := euler_count_spanSingleton_eq_neg_log_valuation v (p : F) hp.2.1
    rw [hcount] at h
    linarith
  have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hp.2.1
  calc
    HeightOneSpectrum.valuation F v (p : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
      (WithZero.exp_log hpvalne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog]

private lemma euler_residueRing_bijective (v : FinPlace F) (hv : v ∉ S.Sf) :
    ∃ f : ResidueRing R.exterior (R.exterior.prime v hv) → 𝓞 F ⧸ v.asIdeal,
      Function.Bijective f ∧ ∀ a : S.R,
        f (Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.prime v hv)}) a) =
          residue v (a : F) := by
  classical
  let pi := R.exterior.prime v hv
  let g := R.exterior.genR pi
  letI : Fintype (ResidueRing R.exterior pi) := R.exterior.residueFinite pi
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let rho : S.R →+* (𝓞 F ⧸ v.asIdeal) := by
    refine {
      toFun := fun x => residue v (x : F)
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_ }
    · simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (1 : 𝓞 F)
    · intro x y
      exact (a2_bridge_SYMBOL D S).residue_mul v (x : F) (y : F)
        (x.property v hv) (y.property v hv)
    · simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
    · intro x y
      exact euler_residue_add_integral v (x : F) (y : F)
        (x.property v hv) (y.property v hv)
  let SB : SymbolBridge D S := a2_bridge_SYMBOL D S
  have hp : S.IsGen (primeGen R v : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [pi, primeGen, hv, R.exterior.prime_val] using h
  have hg : S.IsGen (g : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [g, pi, R.exterior.genR_val, R.exterior.prime_val] using h
  obtain ⟨u, hu⟩ := euler_generators_unit_ratio v.asIdeal
    (primeGen R v : F) (g : F) hp hg
  have huVal : HeightOneSpectrum.valuation F v (u : Fˣ) = 1 := u.property v hv
  have hvalpg : HeightOneSpectrum.valuation F v (primeGen R v : F) =
      HeightOneSpectrum.valuation F v (u : Fˣ) * HeightOneSpectrum.valuation F v (g : F) := by
    calc
      _ = HeightOneSpectrum.valuation F v ((u : Fˣ) * (g : F)) := by rw [hu]
      _ = _ := (v.valuation F).map_mul _ _
  have hvalg : HeightOneSpectrum.valuation F v (g : F) =
      WithZero.exp (-1 : ℤ) := by
    rw [huVal, one_mul] at hvalpg
    rw [← hvalpg]
    exact euler_primeGen_valuation R v hv
  have hvalgLt : HeightOneSpectrum.valuation F v (g : F) < 1 := by
    rw [hvalg]
    simp
  have hresg : residue v (g : F) = 0 := by
    by_contra hne
    have hvalone := (SB.residue_ne_zero v (g : F) hvalgLt.le).mp hne
    exact (ne_of_lt hvalgLt) hvalone
  have hIle : Ideal.span ({g} : Set S.R) ≤ RingHom.ker rho := by
    rw [Ideal.span_singleton_le_iff_mem]
    change rho g = 0
    exact hresg
  have hIzero : ∀ a : S.R, a ∈ Ideal.span ({g} : Set S.R) → rho a = 0 := by
    intro a ha
    have h : a ∈ RingHom.ker rho := hIle ha
    simpa using h
  let f : ResidueRing R.exterior pi →+* (𝓞 F ⧸ v.asIdeal) :=
    Ideal.Quotient.lift (Ideal.span {g}) rho hIzero
  have hsurj : Function.Surjective f := by
    intro z
    let a : S.R := ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
    refine ⟨Ideal.Quotient.mk (Ideal.span {g}) a, ?_⟩
    change Ideal.Quotient.lift (Ideal.span {g}) rho hIzero
      (Ideal.Quotient.mk (Ideal.span {g}) a) = z
    rw [Ideal.Quotient.lift_mk]
    change residue v (a : F) = z
    simpa [a] using SB.residue_algebraMap v z.out
  have hcardQ : Fintype.card (ResidueRing R.exterior pi) = Ideal.absNorm v.asIdeal := by
    calc
      Fintype.card (ResidueRing R.exterior pi) = Ideal.absNorm pi.1 := R.exterior.residue_card pi
      _ = Ideal.absNorm v.asIdeal := by rw [R.exterior.prime_val]
  have hcardO : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcardQ.trans hcardO.symm⟩
  refine ⟨f, hbij, ?_⟩
  intro a
  change (Ideal.Quotient.lift (Ideal.span {g}) rho hIzero)
      (Ideal.Quotient.mk (Ideal.span {g}) a) = residue v (a : F)
  rw [Ideal.Quotient.lift_mk]
  rfl

private lemma euler_primePower_reduction (v : FinPlace F) (hv : v ∉ S.Sf) (t : ℕ)
    (ht : 0 < t) :
    ∃ rho : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v hv) t) →+*
        ResidueRing R.exterior (R.exterior.prime v hv),
      Function.Surjective rho ∧ ∀ a : S.R,
        rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.pow (R.exterior.prime v hv) t)}) a) =
          Ideal.Quotient.mk (Ideal.span {R.exterior.genR (R.exterior.prime v hv)}) a := by
  classical
  let pi := R.exterior.prime v hv
  let It := R.exterior.pow pi t
  let I1 := pi
  let gt := R.exterior.genR It
  let g1 := R.exterior.genR I1
  obtain ⟨_, ct, pt, hpt, hptgen⟩ := euler_prime_power_quotient_generator R v hv t
  obtain ⟨_, c1, p1, hp1, hp1gen⟩ := euler_prime_power_quotient_generator R v hv 1
  obtain ⟨_, _, pm, hpm, _⟩ := euler_prime_power_quotient_generator R v hv (t - 1)
  have hptmul : pt = p1 * pm := by
    apply Subtype.ext
    change (pt : F) = (p1 : F) * (pm : F)
    rw [← hpt, ← hp1, ← hpm]
    have he : 1 + (t - 1) = t := by omega
    calc
      (primeGen R v : F) ^ t = (primeGen R v : F) ^ (1 + (t - 1)) := by rw [he]
      _ = (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (t - 1) := by rw [pow_add]
  have hspanT : Ideal.span ({pt} : Set S.R) = Ideal.span {gt} := by
    rw [hptgen]
    exact Ideal.span_singleton_mul_left_unit ct.isUnit gt
  have hgenP : S.IsGen (primeGen R v : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [pi, primeGen, hv, R.exterior.prime_val] using h
  have hp1eq : (p1 : F) = (primeGen R v : F) := by simpa using hp1.symm
  have hgenP1 : S.IsGen (p1 : F) v.asIdeal := by rw [hp1eq]; exact hgenP
  have hgenG1 : S.IsGen (g1 : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [g1, pi, R.exterior.genR_val, R.exterior.prime_val] using h
  have hspan1 : Ideal.span ({p1} : Set S.R) = Ideal.span {g1} := by
    exact euler_span_singleton_eq_of_generators v hv v.asIdeal p1 g1 hgenP1 hgenG1
  have hdiv : p1 ∣ pt := ⟨pm, hptmul⟩
  have hle : Ideal.span ({gt} : Set S.R) ≤ Ideal.span {g1} := by
    calc
      Ideal.span ({gt} : Set S.R) = Ideal.span {pt} := hspanT.symm
      _ ≤ Ideal.span {p1} := Ideal.span_singleton_le_span_singleton.mpr hdiv
      _ = Ideal.span {g1} := hspan1
  let rho : ResidueRing R.exterior It →+* ResidueRing R.exterior I1 :=
    Ideal.quotientMap (Ideal.span {g1}) (RingHom.id S.R) hle
  have hsurj : Function.Surjective rho := by
    change Function.Surjective
      (Ideal.quotientMap (Ideal.span {g1}) (RingHom.id S.R) hle)
    exact Ideal.quotientMap_surjective (f := RingHom.id S.R) (H := hle)
      (fun x => ⟨x, rfl⟩)
  refine ⟨rho, hsurj, ?_⟩
  intro a
  exact Ideal.quotientMap_mk (J := Ideal.span {gt}) (I := Ideal.span {g1})
    (f := RingHom.id S.R) (H := hle) (x := a)

private lemma euler_addHom_fiber_card {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (b : B) :
    Fintype.card {x : A // f x = b} = Fintype.card {x : A // f x = 0} := by
  classical
  obtain ⟨x₀, hx₀⟩ := hf b
  let e : {x : A // f x = b} ≃ {x : A // f x = 0} := {
    toFun := fun x => ⟨x.1 - x₀, by simp [map_sub, x.2, hx₀]⟩
    invFun := fun x => ⟨x.1 + x₀, by simp [map_add, x.2, hx₀]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      simp [add_sub_cancel_right]
    right_inv := by
      intro x
      apply Subtype.ext
      simp [sub_add_cancel]
  }
  exact Fintype.card_congr e

private lemma euler_addHom_card_eq_card_mul_fiber {A B : Type}
    [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Fintype.card A = Fintype.card B * Fintype.card {x : A // f x = 0} := by
  calc
    Fintype.card A = ∑ x : A, (1 : ℕ) := Fintype.card_eq_sum_ones
    _ = ∑ b : B, ∑ x : {x : A // f x = b}, (1 : ℕ) :=
      (Fintype.sum_fiberwise (fun x : A => f x) (fun _ => (1 : ℕ))).symm
    _ = ∑ b : B, Fintype.card {x : A // f x = b} := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (Fintype.card_eq_sum_ones (α := {x : A // f x = b})).symm
    _ = ∑ b : B, Fintype.card {x : A // f x = 0} := by
      apply Finset.sum_congr rfl
      intro b hb
      exact euler_addHom_fiber_card f hf b
    _ = Fintype.card B * Fintype.card {x : A // f x = 0} := by simp

private lemma euler_sum_fiberwise_const {A B M : Type} [Fintype A] [Fintype B]
    [AddCommMonoid M] (rho : A → B) (hrho : Function.Surjective rho)
    (g : A → M) (hg : ∀ x y, rho x = rho y → g x = g y) :
    ∑ x : A, g x = ∑ b : B,
      Fintype.card {x : A // rho x = b} • g (Classical.choose (hrho b)) := by
  classical
  rw [← Fintype.sum_fiberwise rho g]
  apply Finset.sum_congr rfl
  intro b hb
  let x₀ := Classical.choose (hrho b)
  have hx₀ : rho x₀ = b := Classical.choose_spec (hrho b)
  calc
    (∑ x : {x : A // rho x = b}, g x.1) =
        ∑ x : {x : A // rho x = b}, g x₀ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hg x.1 x₀ (x.2.trans hx₀.symm)
    _ = Fintype.card {x : A // rho x = b} • g x₀ := by simp

private lemma euler_residue_zero_valuation_bound (D : FieldData F)
    (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : S.R) (hx : residue v (x : F) = 0) :
    HeightOneSpectrum.valuation F v (x : F) ≤ WithZero.exp (-1 : ℤ) := by
  let SB := a2_bridge_SYMBOL D S
  have hxval : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hv
  by_cases hx0 : (x : F) = 0
  · simp [hx0]
  · have hxneVal : HeightOneSpectrum.valuation F v (x : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hx0
    have hxneOne : HeightOneSpectrum.valuation F v (x : F) ≠ 1 := by
      intro hxone
      have hresne := (SB.residue_ne_zero v (x : F) hxval).mpr hxone
      rw [hx] at hresne
      exact hresne rfl
    have hloglt : WithZero.log (HeightOneSpectrum.valuation F v (x : F)) < 0 := by
      have h := (WithZero.log_lt_log hxneVal (by simp : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).2
        (lt_of_le_of_ne hxval hxneOne)
      simpa using h
    have hlogle : WithZero.log (HeightOneSpectrum.valuation F v (x : F)) ≤ -1 := by omega
    exact (WithZero.log_le_iff_le_exp hxneVal).mp hlogle

private lemma euler_chiPow_residue_congr (D : FieldData F)
    (S : SData F CE condη) (v : FinPlace F)
    (x y : F) (e : ℤ) (hres : residue v x = residue v y) :
    chiPow D v x e = chiPow D v y e := by
  by_cases hx : residue v x = 0
  · have hy : residue v y = 0 := by rw [← hres, hx]
    simp [chiPow, hx, hy]
  · have hy : residue v y ≠ 0 := by rw [← hres]; exact hx
    rw [chiPow, if_neg hx, chiPow, if_neg hy]
    rw [(a2_bridge_SYMBOL D S).chi_congr v x y hres]

private lemma euler_addchar_congr_integral (A : AddCharData F) (v : FinPlace F) (x y : F)
    (hxy : HeightOneSpectrum.valuation F v (x - y) ≤ 1) :
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
      A.ψ v (algebraMap F (v.adicCompletion F) y) := by
  have hInt : algebraMap F (v.adicCompletion F) (x - y) ∈ v.adicCompletionIntegers F := by
    change ((x - y : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hxy
  have hψdiff := A.integral v (algebraMap F (v.adicCompletion F) (x - y)) hInt
  have hψy : A.ψ v (algebraMap F (v.adicCompletion F) y) ≠ 0 :=
    (AddChar.val_isUnit (A.ψ v) (algebraMap F (v.adicCompletion F) y)).ne_zero
  have harg : algebraMap F (v.adicCompletion F) (x - y) =
      algebraMap F (v.adicCompletion F) x - algebraMap F (v.adicCompletion F) y := by simp
  have hdiv := (A.ψ v).map_sub_eq_div
    (algebraMap F (v.adicCompletion F) x) (algebraMap F (v.adicCompletion F) y)
  calc
    A.ψ v (algebraMap F (v.adicCompletion F) x) =
        (A.ψ v (algebraMap F (v.adicCompletion F) x) /
          A.ψ v (algebraMap F (v.adicCompletion F) y)) *
            A.ψ v (algebraMap F (v.adicCompletion F) y) :=
      (div_mul_cancel₀ _ hψy).symm
    _ = A.ψ v (algebraMap F (v.adicCompletion F) (x - y)) *
          A.ψ v (algebraMap F (v.adicCompletion F) y) := by
      rw [← hdiv, ← harg]
    _ = A.ψ v (algebraMap F (v.adicCompletion F) y) := by rw [hψdiff, one_mul]

private lemma euler_addchar_div_residue_congr (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ)
    (hpVal : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ))
    (x y : S.R) (hres : residue v (x : F) = residue v (y : F)) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((x : F) / (p : F))) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((y : F) / (p : F))) := by
  have hresDiff : residue v ((x : F) - (y : F)) = 0 := by
    have hadd := euler_residue_add_integral v
      ((x : F) - (y : F)) (y : F)
      ((x - y).property v hv) (y.property v hv)
    have hident : ((x : F) - (y : F)) + (y : F) = (x : F) := by ring
    rw [hident] at hadd
    have hcancel : residue v ((x : F) - (y : F)) + residue v (y : F) =
        0 + residue v (y : F) := by
      calc
        _ = residue v (x : F) := hadd.symm
        _ = residue v (y : F) := hres
        _ = 0 + residue v (y : F) := by simp
    exact add_right_cancel hcancel
  have hvalDiff := euler_residue_zero_valuation_bound D v hv (x - y) hresDiff
  have hpPos : 0 < HeightOneSpectrum.valuation F v (p : F) := by
    rw [hpVal]
    exact lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  have harg : (x : F) / (p : F) - (y : F) / (p : F) =
      ((x : F) - (y : F)) / (p : F) := by field_simp [Units.ne_zero p]
  have hval : HeightOneSpectrum.valuation F v
      ((x : F) / (p : F) - (y : F) / (p : F)) ≤ 1 := by
    rw [harg, map_div₀]
    exact (div_le_one₀ hpPos).2 (by rw [hpVal]; exact hvalDiff)
  exact euler_addchar_congr_integral A v ((x : F) / (p : F))
    ((y : F) / (p : F)) hval

private lemma euler_localT_norm_le (v : FinPlace F) (hv : v ∉ S.Sf)
    (e : ℤ) (y : S.R) : ‖localT R v e (y : F)‖ ≤ qI v.asIdeal := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let p : Fˣ := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v hv)).1
    simpa [p, primeGen, hv, R.exterior.prime_val] using h
  obtain ⟨_, _, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  let SB := a2_bridge_SYMBOL D S
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
    ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
  have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue a : S.R) : F) = a := by
    change residue v (algebraMap (𝓞 F) F a.out) = a
    calc
      _ = Ideal.Quotient.mk v.asIdeal a.out := SB.residue_algebraMap v a.out
      _ = a := Ideal.Quotient.mk_out a
  have hψnorm (a : 𝓞 F ⧸ v.asIdeal) : ‖ψ a‖ = 1 := by
    have hzero : addOrderOf a • a = 0 := addOrderOf_nsmul_eq_zero a
    have hpow : ψ a ^ addOrderOf a = 1 := by
      rw [← ψ.map_nsmul_eq_pow]
      rw [hzero, ψ.map_zero_eq_one]
    exact Complex.norm_eq_one_of_pow_eq_one hpow (addOrderOf_pos a).ne'
  let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
  have hphase (x : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
      ψ (a * -x) := by
    let targetR : S.R := -(y * liftResidue x)
    let finiteR : S.R := liftResidue (-x) * liftResidue a
    have hresMul : residue v ((y * liftResidue x : S.R) : F) = a * x := by
      change residue v ((y : F) * (liftResidue x : F)) = a * x
      rw [SB.residue_mul v (y : F) (liftResidue x : F)
        (y.property v hv) ((liftResidue x).property v hv), hresLift]
    have hresZero : residue v (0 : F) = 0 := by
      simpa using SB.residue_algebraMap v (0 : 𝓞 F)
    have hresTarget : residue v (targetR : F) = -(a * x) := by
      have hadd := euler_residue_add_integral v
        (targetR : F) ((y * liftResidue x : S.R) : F)
        (targetR.property v hv) ((y * liftResidue x).property v hv)
      have hident : (targetR : F) + (y * liftResidue x : S.R) = 0 := by
        dsimp [targetR]
        ring
      rw [hident, hresZero, hresMul] at hadd
      exact eq_neg_iff_add_eq_zero.mpr hadd.symm
    have hresFinite : residue v (finiteR : F) = -(a * x) := by
      change residue v ((liftResidue (-x) : S.R) * (liftResidue a : S.R) : F) = _
      rw [SB.residue_mul v (liftResidue (-x) : F) (liftResidue a : F)
        ((liftResidue (-x)).property v hv) ((liftResidue a).property v hv),
        hresLift, hresLift]
      dsimp [a]
      ring
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = -(a * x) := hresTarget
        _ = residue v (finiteR : F) := hresFinite.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval a (-x)
    have htarget : (targetR : F) =
        -((y : F) * algebraMap (𝓞 F) F x.out) := by
      simp [targetR, liftResidue]
    have hfinite : (finiteR : F) =
        algebraMap (𝓞 F) F (-x).out * algebraMap (𝓞 F) F a.out := by
      simp [finiteR, liftResidue]
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        congr 1
        rw [htarget]
        ring
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ (a * -x) := by simpa [p, hfinite] using heval.symm
  have hfinite : localT R v e (y : F) =
      ∑ x : 𝓞 F ⧸ v.asIdeal,
        chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hphase]
  have hterm (x : 𝓞 F ⧸ v.asIdeal) :
      ‖chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (SB.chiPow_norm_le v _ e)
        (hψnorm _).le (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  calc
    ‖localT R v e (y : F)‖ =
        ‖∑ x : 𝓞 F ⧸ v.asIdeal,
          chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ :=
      congrArg norm hfinite
    _ ≤ ∑ x : 𝓞 F ⧸ v.asIdeal,
          ‖chiPow D v (algebraMap (𝓞 F) F x.out) e * ψ (a * -x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : 𝓞 F ⧸ v.asIdeal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hterm x
    _ = Ideal.absNorm v.asIdeal := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp [hcard]
    _ = qI v.asIdeal := by simp [qI]

private lemma euler_localD_gauss_sum (v : FinPlace F) (hv : v ∉ S.Sf)
    (x : S.R) (hx : residue v (x : F) ≠ 0)
    [instQ1 : Fintype (ResidueRing R.exterior (R.exterior.prime v hv))] :
    ∑ d : ResidueRing R.exterior (R.exterior.prime v hv), chiPow D v (d.out : F) 1 *
      A.ψ v (algebraMap F (v.adicCompletion F)
        ((d.out : F) * (x : F) / (primeGen R v : F))) =
      localT R v 1 1 * star (chi D v (x : F)) := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let Q1 := ResidueRing R.exterior pi
  letI : Fintype Q1 := instQ1
  let SB := a2_bridge_SYMBOL D S
  let p : Fˣ := primeGen R v
  have hp : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec pi).1
    simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
  obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
  let resEquiv : Q1 ≃ 𝓞 F ⧸ v.asIdeal := Equiv.ofBijective resEq hresEqBij
  obtain ⟨_, hchiSix, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp
  obtain ⟨χ, hχorder, hχeval⟩ := hchiSix
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  let SB := a2_bridge_SYMBOL D S
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
    ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
  have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue z : S.R) : F) = z := by
    change residue v (algebraMap (𝓞 F) F z.out) = z
    calc
      _ = Ideal.Quotient.mk v.asIdeal z.out := SB.residue_algebraMap v z.out
      _ = z := Ideal.Quotient.mk_out z
  let a : 𝓞 F ⧸ v.asIdeal := residue v (x : F)
  have ha : a ≠ 0 := by simpa [a] using hx
  have hresD (d : Q1) : residue v (d.out : F) = resEq d := by
    calc
      residue v (d.out : F) = resEq
          (Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out) :=
        (hresEqMk d.out).symm
      _ = resEq d := by rw [Ideal.Quotient.mk_out d]
  have hchiD (d : Q1) : chiPow D v (d.out : F) 1 = χ (resEq d) := by
    have hres : residue v (d.out : F) =
        residue v ((liftResidue (resEq d) : S.R) : F) := by
      calc
        _ = resEq d := hresD d
        _ = _ := (hresLift (resEq d)).symm
    calc
      chiPow D v (d.out : F) 1 =
          chiPow D v ((liftResidue (resEq d) : S.R) : F) 1 :=
        euler_chiPow_residue_congr D S v (d.out : F)
          ((liftResidue (resEq d) : S.R) : F) 1 hres
      _ = χ (resEq d) := (hχeval (resEq d)).symm
  have hphaseD (d : Q1) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        ((d.out : F) * (x : F) / (p : F))) =
      ψ (resEq d * a) := by
    let targetR : S.R := d.out * x
    let finiteR : S.R := liftResidue a * liftResidue (resEq d)
    have hresTarget : residue v (targetR : F) = (resEq d) * a := by
      calc
        residue v (targetR : F) =
            residue v ((d.out : F) * (x : F)) := rfl
        _ = residue v (d.out : F) * residue v (x : F) :=
          SB.residue_mul v (d.out : F) (x : F)
            ((d.out).property v hv) (x.property v hv)
        _ = (resEq d) * a := by rw [hresD]
    have hresFinite : residue v (finiteR : F) = (resEq d) * a := by
      calc
        residue v (finiteR : F) =
            residue v (liftResidue a : F) *
              residue v (liftResidue (resEq d) : F) :=
          SB.residue_mul v (liftResidue a : F) (liftResidue (resEq d) : F)
            ((liftResidue a).property v hv) ((liftResidue (resEq d)).property v hv)
        _ = a * resEq d := by rw [hresLift, hresLift]
        _ = (resEq d) * a := mul_comm _ _
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = (resEq d) * a := hresTarget
        _ = _ := hresFinite.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval (resEq d) a
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        have harg : (d.out : F) * (x : F) / (p : F) =
            (targetR : F) / (p : F) := rfl
        exact congrArg (fun z : F => A.ψ v (algebraMap F (v.adicCompletion F) z)) harg
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ (resEq d * a) := by
        simpa [finiteR, liftResidue, p] using heval.symm
  have hresidueSum :
      (∑ d : Q1, chiPow D v (d.out : F) 1 *
        A.ψ v (algebraMap F (v.adicCompletion F)
          ((d.out : F) * (x : F) / (p : F)))) =
        ∑ z : 𝓞 F ⧸ v.asIdeal, χ z * ψ (z * a) := by
    exact Fintype.sum_equiv resEquiv _ _ (by
      intro d
      rw [hchiD d, hphaseD d]
      simpa [resEquiv])
  have houterGauss :
      (∑ d : Q1, chiPow D v (d.out : F) 1 *
        A.ψ v (algebraMap F (v.adicCompletion F)
          ((d.out : F) * (x : F) / (p : F)))) =
        gaussSum χ (ψ.mulShift a) := by
    rw [hresidueSum]
    simp [gaussSum, AddChar.mulShift_apply, mul_comm]
  have hTphase (z : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-(algebraMap (𝓞 F) F z.out) / (p : F))) =
      ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
    let targetR : S.R := -liftResidue z
    let finiteR : S.R := liftResidue z * liftResidue (-1)
    have hresNeg : residue v (targetR : F) = -z := by
      have hadd := euler_residue_add_integral v (targetR : F)
        (liftResidue z : F) (targetR.property v hv) ((liftResidue z).property v hv)
      have hident : (targetR : F) + (liftResidue z : S.R) = 0 := by
        dsimp [targetR]
        ring
      have hzero : residue v (0 : F) = 0 := by
        simpa using SB.residue_algebraMap v (0 : 𝓞 F)
      rw [hident, hzero, hresLift] at hadd
      exact eq_neg_iff_add_eq_zero.mpr hadd.symm
    have hresProd : residue v (finiteR : F) = -z := by
      change residue v ((liftResidue z : S.R) *
        (liftResidue (-1) : S.R) : F) = _
      rw [SB.residue_mul v (liftResidue z : F) (liftResidue (-1) : F)
        ((liftResidue z).property v hv) ((liftResidue (-1)).property v hv),
        hresLift, hresLift]
      simp
    have hresCompare : residue v (targetR : F) = residue v (finiteR : F) := by
      calc
        _ = -z := hresNeg
        _ = _ := hresProd.symm
    have hcompare := euler_addchar_div_residue_congr D A v hv p
      (euler_primeGen_valuation R v hv) targetR finiteR hresCompare
    have heval := hψeval (-1 : 𝓞 F ⧸ v.asIdeal) z
    calc
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((targetR : F) / (p : F))) := by
        simpa [targetR, liftResidue]
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            ((finiteR : F) / (p : F))) := hcompare
      _ = ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
        simpa [finiteR, liftResidue, p] using heval.symm
  have hTone : localT R v 1 1 = gaussSum χ (ψ.mulShift (-1)) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    calc
      _ = ∑ z : 𝓞 F ⧸ v.asIdeal, χ z * ψ ((-1 : 𝓞 F ⧸ v.asIdeal) * z) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [(hχeval z).symm]
        calc
          _ = χ z * A.ψ v (algebraMap F (v.adicCompletion F)
                ((-(algebraMap (𝓞 F) F z.out)) / (p : F))) := by
            apply congrArg (fun w : F => χ z * A.ψ v (algebraMap F (v.adicCompletion F) w))
            ring
          _ = _ := by rw [hTphase z]
      _ = _ := by simp [gaussSum, AddChar.mulShift_apply]
  have hresMinusAlg : residue v
      (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) = -1 := by
    simpa using SB.residue_algebraMap v ((-1 : 𝓞 F ⧸ v.asIdeal).out)
  have hresMinus : residue v (-1 : F) = -1 := by
    simpa using SB.residue_algebraMap v (-1 : 𝓞 F)
  have hchiMinus : χ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    calc
      χ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 1 :=
        hχeval _
      _ = chiPow D v (-1 : F) 1 :=
        euler_chiPow_residue_congr D S v _ _ 1 (hresMinusAlg.trans hresMinus.symm)
      _ = chi D v (-1 : F) := by
        rw [SB.chiPow_nonzero v (-1 : F) 1 (by rw [hresMinus]; exact neg_ne_zero.mpr one_ne_zero)]
        simp
      _ = 1 := SB.chi_minus_one v hv
  let u : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ha).unit
  have hu : (u : 𝓞 F ⧸ v.asIdeal) = a := (isUnit_iff_ne_zero.mpr ha).unit_spec
  have hshift : ψ.mulShift a = (ψ.mulShift (-1)).mulShift (-u) := by
    ext z
    simp [AddChar.mulShift_apply, hu, mul_assoc]
  have hGaussShift := gaussSum_mulShift_eq χ (ψ.mulShift (-1)) (-u)
  have hchiU : χ u = chi D v (x : F) := by
    have hresU : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
        residue v (x : F) := by
      have hresAlgU : residue v
          (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
            (u : 𝓞 F ⧸ v.asIdeal) := by
        simpa using SB.residue_algebraMap v (u : 𝓞 F ⧸ v.asIdeal).out
      calc
        _ = (u : 𝓞 F ⧸ v.asIdeal) := hresAlgU
        _ = a := hu
        _ = _ := rfl
    calc
      χ u = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 := hχeval u
      _ = chiPow D v (x : F) 1 :=
        euler_chiPow_residue_congr D S v _ _ 1 hresU
      _ = chi D v (x : F) := by
        rw [SB.chiPow_nonzero v (x : F) 1 hx]
        simp
  have hchiMinusUnit : χ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
    simpa using hchiMinus
  have hchiNegU : χ (-u) = chi D v (x : F) := by
    calc
      χ (-u) = χ ((-1 : (𝓞 F ⧸ v.asIdeal)ˣ) * u) := by congr 1 <;> simp
      _ = χ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) * χ u := map_mul χ _ _
      _ = chi D v (x : F) := by rw [hchiMinusUnit, hchiU]; simp
  have hchiInv : χ⁻¹ (-u) = star (chi D v (x : F)) := by
    calc
      χ⁻¹ (-u) = (χ (-u))⁻¹ := MulChar.inv_apply_eq_inv' χ _
      _ = (chi D v (x : F))⁻¹ := by rw [hchiNegU]
      _ = star (chi D v (x : F)) := Complex.inv_eq_conj (SB.chi_norm v _ hx)
  calc
    _ = gaussSum χ (ψ.mulShift a) := houterGauss
    _ = χ⁻¹ (-u) * gaussSum χ (ψ.mulShift (-1)) := by
      rw [hshift]
      exact hGaussShift
    _ = localT R v 1 1 * star (chi D v (x : F)) := by
      rw [hchiInv, ← hTone]
      ring

private lemma euler_localFactor_residue_congr
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (v : FinPlace F) (hv : v ∉ S.Sf) (y x₁ x₂ : S.R) (e : ℤ)
    (hres : residue v (x₁ : F) = residue v (x₂ : F)) :
    chiPow D v (x₁ : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x₁ : F) / (primeGen R v : F)))) =
    chiPow D v (x₂ : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x₂ : F) / (primeGen R v : F)))) := by
  have hresDiff : residue v ((x₁ : F) - (x₂ : F)) = 0 := by
    have hsum := euler_residue_add_integral v
      ((x₁ : F) - (x₂ : F)) (x₂ : F)
      ((x₁ - x₂).property v hv) (x₂.property v hv)
    have hident : ((x₁ : F) - (x₂ : F)) + (x₂ : F) = (x₁ : F) := by ring
    rw [hident] at hsum
    have hsum' : residue v ((x₁ : F) - (x₂ : F)) + residue v (x₂ : F) =
        0 + residue v (x₂ : F) := by
      simpa using hsum.symm.trans hres
    exact add_right_cancel hsum'
  have hvalDiff := euler_residue_zero_valuation_bound D v hv (x₁ - x₂) hresDiff
  have hyVal : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
  have hvalProd : HeightOneSpectrum.valuation F v
      ((y : F) * ((x₁ : F) - (x₂ : F))) ≤ WithZero.exp (-1 : ℤ) := by
    rw [(v.valuation F).map_mul]
    calc
      HeightOneSpectrum.valuation F v (y : F) *
          HeightOneSpectrum.valuation F v ((x₁ : F) - (x₂ : F)) ≤
          1 * WithZero.exp (-1 : ℤ) :=
        mul_le_mul hyVal hvalDiff (zero_le) (zero_le)
      _ = WithZero.exp (-1 : ℤ) := one_mul _
  have hpVal := euler_primeGen_valuation R v hv
  have hpPos : 0 < HeightOneSpectrum.valuation F v (primeGen R v : F) := by
    rw [hpVal]
    exact lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
  have harg : -((y : F) * (x₁ : F) / (primeGen R v : F)) -
      -((y : F) * (x₂ : F) / (primeGen R v : F)) =
        -((y : F) * ((x₁ : F) - (x₂ : F)) / (primeGen R v : F)) := by
    field_simp [Units.ne_zero (primeGen R v)]
    ring
  have hargVal : HeightOneSpectrum.valuation F v
      (-((y : F) * (x₁ : F) / (primeGen R v : F)) -
        -((y : F) * (x₂ : F) / (primeGen R v : F))) ≤ 1 := by
    rw [harg, (v.valuation F).map_neg, map_div₀]
    exact (div_le_one₀ hpPos).2 (by rw [hpVal]; exact hvalProd)
  have hpsi := euler_addchar_congr_integral A v
      (-((y : F) * (x₁ : F) / (primeGen R v : F)))
      (-((y : F) * (x₂ : F) / (primeGen R v : F))) hargVal
  have hchi := euler_chiPow_residue_congr D S v (x₁ : F) (x₂ : F) e hres
  rw [hchi, hpsi]

private lemma euler_primePower_localT_sum (v : FinPlace F) (hv : v ∉ S.Sf)
    (t : ℕ) (ht : 0 < t) (e : ℤ) (y : S.R)
    [instQt : Fintype (ResidueRing R.exterior
      (R.exterior.pow (R.exterior.prime v hv) t))] :
    let pi := R.exterior.prime v hv
    let It := R.exterior.pow pi t
    let Qt := ResidueRing R.exterior It
    letI : Fintype Qt := instQt
    ∑ x : Qt,
      chiPow D v (x.out : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * (x.out : F) / (primeGen R v : F) ^ 1))) =
      (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v e (y : F) := by
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let It := R.exterior.pow pi t
  let Qt := ResidueRing R.exterior It
  let Q1 := ResidueRing R.exterior pi
  letI : Fintype Qt := instQt
  letI : Fintype Q1 := R.exterior.residueFinite pi
  obtain ⟨rho, hrho, hrhoMk⟩ := euler_primePower_reduction R v hv t ht
  have hcardQt : @Fintype.card Qt instQt = Ideal.absNorm v.asIdeal ^ t := by
    have hinst : instQt = R.exterior.residueFinite It := Subsingleton.elim _ _
    calc
      @Fintype.card Qt instQt = @Fintype.card Qt (R.exterior.residueFinite It) := by
        rw [hinst]
      _ = Ideal.absNorm v.asIdeal ^ t := by
        simpa [Qt, It, pi] using euler_residue_card_pow R v hv t
  have hcardQ1 : @Fintype.card Q1 (R.exterior.residueFinite pi) =
      Ideal.absNorm v.asIdeal := by
    change @Fintype.card _ (R.exterior.residueFinite pi) = _
    rw [R.exterior.residue_card, R.exterior.prime_val]
  obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
  have hresReduce (x : Qt) : resEq (rho x) = residue v (x.out : F) := by
    have hxmk : rho x = Ideal.Quotient.mk
        (Ideal.span {R.exterior.genR pi}) x.out := by
      calc
        rho x = rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out) :=
          congrArg rho (Ideal.Quotient.mk_out x).symm
        _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := hrhoMk x.out
    rw [hxmk]
    exact hresEqMk x.out
  let f : Qt →+ Q1 := rho.toAddMonoidHom
  have hcardSum := euler_addHom_card_eq_card_mul_fiber f hrho
  rw [hcardQt, hcardQ1] at hcardSum
  have hpow : Ideal.absNorm v.asIdeal ^ t =
      Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal ^ (t - 1) := by
    have ht' : (t - 1) + 1 = t := by omega
    calc
      _ = Ideal.absNorm v.asIdeal ^ ((t - 1) + 1) :=
        congrArg (fun n : ℕ => Ideal.absNorm v.asIdeal ^ n) ht'.symm
      _ = Ideal.absNorm v.asIdeal ^ (t - 1) * Ideal.absNorm v.asIdeal := by rw [pow_succ]
      _ = _ := Nat.mul_comm _ _
  have hfiber0 : Fintype.card {x : Qt // f x = 0} =
      Ideal.absNorm v.asIdeal ^ (t - 1) := by
    have hqpos : 0 < Ideal.absNorm v.asIdeal :=
      lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
    rw [hpow] at hcardSum
    exact Nat.mul_left_cancel hqpos hcardSum.symm
  have hfiber (b : Q1) : Fintype.card {x : Qt // rho x = b} =
      Ideal.absNorm v.asIdeal ^ (t - 1) := by
    simpa [f] using (euler_addHom_fiber_card f hrho b).trans hfiber0
  let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
    ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
  have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
      residue v ((liftResidue z : S.R) : F) = z := by
    change residue v (algebraMap (𝓞 F) F z.out) = z
    calc
      _ = Ideal.Quotient.mk v.asIdeal z.out :=
        (a2_bridge_SYMBOL D S).residue_algebraMap v z.out
      _ = z := Ideal.Quotient.mk_out z
  let G' : (𝓞 F ⧸ v.asIdeal) → ℂ := fun z =>
    chiPow D v ((liftResidue z : S.R) : F) e *
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * ((liftResidue z : S.R) : F) / (primeGen R v : F))))
  let g : Qt → ℂ := fun x =>
    chiPow D v (x.out : F) e * A.ψ v (algebraMap F (v.adicCompletion F)
      (-((y : F) * (x.out : F) / (primeGen R v : F))))
  have hconst (x₁ x₂ : Qt) (h : rho x₁ = rho x₂) : g x₁ = g x₂ := by
    have hres : residue v (x₁.out : F) = residue v (x₂.out : F) := by
      rw [← hresReduce x₁, h, hresReduce x₂]
    simpa [g] using euler_localFactor_residue_congr R v hv y x₁.out x₂.out e hres
  have hpoint (b : Q1) :
      g (Classical.choose (hrho b)) = G' (resEq b) := by
    let x₀ : Qt := Classical.choose (hrho b)
    have hx₀ : rho x₀ = b := Classical.choose_spec (hrho b)
    have hres : residue v (x₀.out : F) =
        residue v ((liftResidue (resEq b) : S.R) : F) := by
      calc
        _ = resEq (rho x₀) := (hresReduce x₀).symm
        _ = resEq b := by rw [hx₀]
        _ = _ := (hresLift (resEq b)).symm
    simpa [g, G', x₀] using
      euler_localFactor_residue_congr R v hv y x₀.out
        (liftResidue (resEq b)) e hres
  have hfiberSum : ∑ x : Qt, g x =
      ∑ b : Q1,
        Fintype.card {x : Qt // rho x = b} • G' (resEq b) := by
    calc
      _ = ∑ b : Q1,
          Fintype.card {x : Qt // rho x = b} • g (Classical.choose (hrho b)) :=
        euler_sum_fiberwise_const rho hrho g hconst
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hpoint b]
  have hfactor :
      ∑ b : Q1, Fintype.card {x : Qt // rho x = b} • G' (resEq b) =
        (qI v.asIdeal : ℂ) ^ (t - 1) *
          ∑ z : 𝓞 F ⧸ v.asIdeal, G' z := by
    have hcardComplex (b : Q1) :
        (Fintype.card {x : Qt // rho x = b} : ℂ) =
          (qI v.asIdeal : ℂ) ^ (t - 1) := by
      rw [hfiber b]
      simp [qI]
    calc
      _ = ∑ b : Q1,
          (qI v.asIdeal : ℂ) ^ (t - 1) * G' (resEq b) := by
        apply Finset.sum_congr rfl
        intro b hb
        calc
          _ = (Fintype.card {x : Qt // rho x = b} : ℂ) * G' (resEq b) := by simp
          _ = _ := by rw [hcardComplex b]
      _ = (qI v.asIdeal : ℂ) ^ (t - 1) *
          ∑ b : Q1, G' (resEq b) := by rw [Finset.mul_sum]
      _ = _ := by
        exact congrArg (fun z : ℂ =>
          (qI v.asIdeal : ℂ) ^ (t - 1) * z)
          (Fintype.sum_equiv (Equiv.ofBijective resEq hresEqBij)
            _ _ (by intro z; rfl))
  have hG : ∑ z : 𝓞 F ⧸ v.asIdeal, G' z = localT R v e (y : F) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
  calc
    _ = ∑ x : Qt, g x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [g, pow_one]
    _ = (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v e (y : F) := by
      rw [hfiberSum, hfactor, hG]

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
  intro v hv J
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let pi := R.exterior.prime v hv
  let I0 := R.exterior.pow pi 0
  let Q0 := ResidueRing R.exterior I0
  letI : Fintype Q0 := R.exterior.residueFinite I0
  have hcard0 : Fintype.card Q0 = 1 := by
    have h := euler_residue_card_pow R v hv 0
    simpa [Q0, I0, pi] using h
  letI : Unique Q0 := Classical.choice (Fintype.card_eq_one_iff_nonempty_unique.mp hcard0)
  obtain ⟨_, cJ, pRJ, hpJ, hpJgen⟩ := euler_prime_power_quotient_generator R v hv J
  have hcondition (d : Q0) : ∃ x : S.R,
      (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
        (primeGen R v : F) ^ 0 * (x : F) := by
    refine ⟨pRJ - d.out, ?_⟩
    rw [hpJ]
    simp
  have hphase (d x : Q0) : A.ψ v (algebraMap F (v.adicCompletion F)
      (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F)) *
        (x.out : F) / (primeGen R v : F) ^ (0 + 0)))) = 1 := by
    let z : S.R := (pRJ - d.out) * x.out
    have hz : -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F)) *
        (x.out : F) / (primeGen R v : F) ^ (0 + 0)) = (-(z : S.R) : F) := by
      rw [hpJ]
      simp [z]
    rw [hz]
    exact euler_addchar_one_of_S_R v hv (-z)
  have hcase00 : localC R v hv 0 0 J = 1 := by
    let d0 : Q0 := 0
    let x0 : Q0 := 0
    have hcondD := hcondition d0
    unfold localC
    rw [finsum_eq_sum_of_fintype]
    rw [Finset.sum_eq_single_of_mem d0 (Finset.mem_univ _) (by
      intro d hd hne
      exact False.elim (hne (Subsingleton.elim d d0)))]
    split
    · simp only [if_pos (by norm_num : 0 = 0), one_mul]
      rw [finsum_eq_sum_of_fintype]
      rw [Finset.sum_eq_single_of_mem x0 (Finset.mem_univ _) (by
        intro x hx hne
        exact False.elim (hne (Subsingleton.elim x x0)))]
      simpa using hphase d0 x0
    · rename_i hfalse
      exact False.elim (hfalse hcondD)
  let p : Fˣ := primeGen R v
  let SB := a2_bridge_SYMBOL D S
  have hpVal : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    simpa [p] using euler_primeGen_valuation R v hv
  have hpValLt : HeightOneSpectrum.valuation F v (p : F) < 1 := by
    rw [hpVal]
    simp
  have hpValLe : HeightOneSpectrum.valuation F v (p : F) ≤ 1 := hpValLt.le
  have hvalPowLe (n : ℕ) : HeightOneSpectrum.valuation F v ((p : F) ^ n) ≤ 1 := by
    obtain ⟨_, _, pRn, hpRn, _⟩ := euler_prime_power_quotient_generator R v hv n
    rw [hpRn]
    exact pRn.property v hv
  have hvalPowLt (n : ℕ) (hn : 0 < n) :
      HeightOneSpectrum.valuation F v ((p : F) ^ n) < 1 := by
    rw [(v.valuation F).map_pow]
    exact pow_lt_one₀ zero_le hpValLt hn.ne'
  have hresOne : residue v (1 : F) = 1 := by
    simpa using SB.residue_algebraMap v (1 : 𝓞 F)
  have hresPow : ∀ n : ℕ, residue v ((p : F) ^ n) = residue v (p : F) ^ n := by
    intro n
    induction n with
    | zero => simp [hresOne]
    | succ n ih =>
      calc
        residue v ((p : F) ^ (n + 1)) =
            residue v ((p : F) ^ n * (p : F)) := by rw [pow_succ]
        _ = residue v ((p : F) ^ n) * residue v (p : F) :=
          SB.residue_mul v _ _ (hvalPowLe n) hpValLe
        _ = residue v (p : F) ^ n * residue v (p : F) := by rw [ih]
        _ = residue v (p : F) ^ (n + 1) := by rw [pow_succ]
  have hresPzero : residue v (p : F) = 0 := by
    by_contra hne
    have hvalOne := (SB.residue_ne_zero v (p : F) hpValLe).mp hne
    have hexpOne : WithZero.exp (-1 : ℤ) = 1 := hpVal.symm.trans hvalOne
    have hlog := congrArg WithZero.log hexpOne
    simp at hlog
  have hresPowZero (n : ℕ) (hn : 0 < n) : residue v ((p : F) ^ n) = 0 := by
    rw [hresPow, hresPzero]
    simp [hn.ne']
  have hchiOne : chi D v (1 : F) = 1 := by
    have hresne : residue v (1 : F) ≠ 0 := by rw [hresOne]; exact one_ne_zero
    have hnorm := SB.chi_norm v (1 : F) hresne
    have hχne : chi D v (1 : F) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [hnorm]
      norm_num
    have hmul := SB.chi_mul v hv (1 : F) 1
      (v.valuation_le_one (1 : 𝓞 F)) (v.valuation_le_one (1 : 𝓞 F))
    have hmul' : chi D v (1 : F) * 1 = chi D v (1 : F) * chi D v (1 : F) := by
      simpa using hmul
    exact (mul_left_cancel₀ hχne hmul').symm
  constructor
  · exact hcase00
  · constructor
    · intro k hk
      let Ik := R.exterior.pow pi k
      let Qk := ResidueRing R.exterior Ik
      letI : Fintype Qk := R.exterior.residueFinite Ik
      obtain ⟨_, cK, pRK, hpK, hpKgen⟩ := euler_prime_power_quotient_generator R v hv k
      let gK := R.exterior.genR Ik
      have hspanK : Ideal.span ({pRK} : Set S.R) = Ideal.span {gK} := by
        rw [hpKgen]
        exact Ideal.span_singleton_mul_left_unit cK.isUnit gK
      let d0 : Qk := Ideal.Quotient.mk (Ideal.span {gK}) pRJ
      have hdivMem (d : Qk) :
          (∃ x : S.R, (pRJ : F) - (d.out : F) = (p : F) ^ k * (x : F)) ↔
            (pRJ - d.out) ∈ Ideal.span {gK} := by
        have h := euler_power_divisibility_iff p k pRK hpK (pRJ - d.out)
        rw [hspanK] at h
        exact h
      have hcondition (d : Qk) :
          (∃ x : S.R, (p : F) ^ J - (d.out : F) = (p : F) ^ k * (x : F)) ↔ d = d0 := by
        have hmem : (∃ x : S.R, (p : F) ^ J - (d.out : F) =
            (p : F) ^ k * (x : F)) ↔ (pRJ - d.out) ∈ Ideal.span {gK} := by
          constructor
          · rintro ⟨x, hx⟩
            apply hdivMem d |>.mp
            exact ⟨x, by rw [← hpJ]; exact hx⟩
          · intro hm
            rcases (hdivMem d).mpr hm with ⟨x, hx⟩
            exact ⟨x, by rw [hpJ]; exact hx⟩
        have hquot : (pRJ - d.out) ∈ Ideal.span {gK} ↔ d = d0 := by
          constructor
          · intro hm
            have hmk : Ideal.Quotient.mk (Ideal.span {gK}) pRJ =
                Ideal.Quotient.mk (Ideal.span {gK}) d.out :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ d.out).2 hm
            calc
              d = Ideal.Quotient.mk (Ideal.span {gK}) d.out := (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {gK}) pRJ := hmk.symm
              _ = d0 := rfl
          · intro hd
            have hmk : Ideal.Quotient.mk (Ideal.span {gK}) pRJ =
                Ideal.Quotient.mk (Ideal.span {gK}) d.out := by
              calc
                Ideal.Quotient.mk (Ideal.span {gK}) pRJ = d0 := rfl
                _ = d := hd.symm
                _ = Ideal.Quotient.mk (Ideal.span {gK}) d.out := (Ideal.Quotient.mk_out d).symm
            exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ d.out).mp hmk
        exact hmem.trans hquot
      have hconditionLocal (d : Qk) :
          (∃ x : S.R, (p : F) ^ J - (p : F) ^ 0 * (d.out : F) =
            (p : F) ^ k * (x : F)) ↔ d = d0 := by
        simpa [pow_zero] using hcondition d
      have hinner (d : Qk) (hd :
          ∃ x : S.R, (p : F) ^ J - (d.out : F) = (p : F) ^ k * (x : F)) :
          ∑ᶠ x : Q0, (if 0 = 0 then 1 else chiPow D v (x.out : F) 0) *
            A.ψ v (algebraMap F (v.adicCompletion F)
              (-(((p : F) ^ J - (p : F) ^ 0 * (d.out : F)) *
                (x.out : F) / (p : F) ^ (k + 0)))) = 1 := by
        obtain ⟨y, hy⟩ := hd
        let x0 : Q0 := 0
        have hphaseK (x : Q0) : A.ψ v (algebraMap F (v.adicCompletion F)
            (-(((p : F) ^ J - (d.out : F)) * (x.out : F) / (p : F) ^ k))) = 1 := by
          let z : S.R := y * x.out
          have hz : -(((p : F) ^ J - (d.out : F)) * (x.out : F) / (p : F) ^ k) =
              (-(z : S.R) : F) := by
            rw [hy]
            field_simp [pow_ne_zero k (Units.ne_zero p)]
            change -((y : F) * (x.out : F)) = -(z : F)
            simp [z]
          rw [hz]
          exact euler_addchar_one_of_S_R v hv (-z)
        rw [finsum_eq_sum_of_fintype]
        rw [Finset.sum_eq_single_of_mem x0 (Finset.mem_univ _) (by
          intro x hx hne
          exact False.elim (hne (Subsingleton.elim x x0)))]
        have hphaseK0 : A.ψ v (algebraMap F (v.adicCompletion F)
            (-(((p : F) ^ J - (p : F) ^ 0 * (d.out : F)) *
              (x0.out : F) / (p : F) ^ (k + 0)))) = 1 := by
          simpa [pow_zero, Nat.add_zero] using hphaseK x0
        simp only [if_pos (by norm_num : 0 = 0), one_mul]
        rw [hphaseK0]
        simp
      have hcond0 : ∃ x : S.R, (p : F) ^ J - (d0.out : F) =
          (p : F) ^ k * (x : F) := (hcondition d0).2 rfl
      have hcond0Local : ∃ x : S.R, (p : F) ^ J - (p : F) ^ 0 * (d0.out : F) =
          (p : F) ^ k * (x : F) := (hconditionLocal d0).2 rfl
      have hchar : chiPow D v (d0.out : F) k = if J = 0 then 1 else 0 := by
        obtain ⟨y, hy⟩ := hcond0
        have hvalDiff : HeightOneSpectrum.valuation F v
            ((p : F) ^ J - (d0.out : F)) < 1 := by
          have hvalY : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
          have hmul : HeightOneSpectrum.valuation F v ((p : F) ^ k * (y : F)) < 1 := by
            rw [(v.valuation F).map_mul]
            by_cases hy0 : HeightOneSpectrum.valuation F v (y : F) = 0
            · rw [hy0, mul_zero]
              exact zero_lt_one
            · have hypos : 0 < HeightOneSpectrum.valuation F v (y : F) :=
                lt_of_le_of_ne (zero_le) (Ne.symm hy0)
              calc
                _ < 1 * HeightOneSpectrum.valuation F v (y : F) :=
                  mul_lt_mul_of_pos_right (hvalPowLt k hk) hypos
                _ ≤ 1 := by simpa using hvalY
          calc
            HeightOneSpectrum.valuation F v ((p : F) ^ J - (d0.out : F)) =
                HeightOneSpectrum.valuation F v ((p : F) ^ k * (y : F)) := by rw [hy]
            _ < 1 := hmul
        have hresEq := SB.residue_congr v ((p : F) ^ J) (d0.out : F)
          (hvalPowLe J) (d0.out.property v hv) hvalDiff
        by_cases hJ : J = 0
        · subst J
          have hresD : residue v (d0.out : F) = 1 := by
            simpa [hresOne] using hresEq.symm
          have hresD' : residue v (d0.out : F) = residue v (1 : F) := by
            calc
              residue v (d0.out : F) = 1 := hresD
              _ = residue v (1 : F) := hresOne.symm
          have hχD : chi D v (d0.out : F) = 1 := by
            calc
              chi D v (d0.out : F) = chi D v (1 : F) :=
                SB.chi_congr v (d0.out : F) 1 hresD'
              _ = 1 := hchiOne
          have hresDne : residue v (d0.out : F) ≠ 0 := by
            rw [hresD]
            exact one_ne_zero
          have hmask : chiPow D v (d0.out : F) (k : ℤ) = 1 := by
            rw [SB.chiPow_nonzero v (d0.out : F) (k : ℤ) hresDne, hχD]
            simp
          simpa using hmask
        · have hresD : residue v (d0.out : F) = 0 := by
            calc
              residue v (d0.out : F) = residue v ((p : F) ^ J) := hresEq.symm
              _ = 0 := hresPowZero J (Nat.pos_of_ne_zero hJ)
          rw [if_neg hJ]
          exact SB.chiPow_zero v (d0.out : F) (k : ℤ) hresD
      unfold localC
      rw [finsum_eq_sum_of_fintype]
      rw [Finset.sum_eq_single_of_mem d0 (Finset.mem_univ _) (by
        intro d hd hne
        have hnot : ¬ (∃ x : S.R,
            (primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d.out : F) =
              (primeGen R v : F) ^ k * (x : F)) := by
          intro h
          have hsimp : ∃ x : S.R, (p : F) ^ J - (d.out : F) =
              (p : F) ^ k * (x : F) := by simpa [p, pow_zero] using h
          exact hne ((hcondition d).mp hsimp)
        simp only [if_neg hnot])]
      split
      · have hinnerEq : ∑ᶠ x : Q0,
            A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d0.out : F)) *
                  (x.out : F) / (primeGen R v : F) ^ (k + 0)))) = 1 := by
          simpa [p, pow_zero, Nat.add_zero] using hinner d0 hcond0
        have hchar' : chiPow D v (d0.out : F) k = if J = 0 then 1 else 0 := by
          simpa [p] using hchar
        have hcond0' : ∃ x : S.R, (primeGen R v : F) ^ J -
            (primeGen R v : F) ^ 0 * (d0.out : F) =
              (primeGen R v : F) ^ k * (x : F) := by
          simpa [p] using hcond0Local
        have hmask := hchar'
        simp only [if_neg (Nat.ne_of_gt hk), if_true, one_mul]
        have hinnerEq' :
            (∑ᶠ x : ResidueRing R.exterior (R.exterior.pow (R.exterior.prime v hv) 0),
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ 0 * (d0.out : F)) *
                  (x.out : F) / (primeGen R v : F) ^ (k + 0))))) = 1 := by
          simpa [Q0, I0, pi] using hinnerEq
        rw [hinnerEq']
        simpa using hmask
      · rename_i hfalse
        have hcond0' : ∃ x : S.R, (primeGen R v : F) ^ J -
            (primeGen R v : F) ^ 0 * (d0.out : F) =
              (primeGen R v : F) ^ k * (x : F) := by simpa [p] using hcond0Local
        exact False.elim (hfalse hcond0')
    · intro t ht
      let It := R.exterior.pow pi t
      let Qt := ResidueRing R.exterior It
      let Q1 := ResidueRing R.exterior pi
      letI : Fintype Qt := R.exterior.residueFinite It
      letI : Fintype Q1 := R.exterior.residueFinite pi
      obtain ⟨rho, hrho, hrhoMk⟩ := euler_primePower_reduction R v hv t ht
      let f : Qt →+ Q1 := rho.toAddMonoidHom
      have hcardQt : Fintype.card Qt = Ideal.absNorm v.asIdeal ^ t := by
        simpa [Qt, It, pi] using euler_residue_card_pow R v hv t
      have hcardQ1 : Fintype.card Q1 = Ideal.absNorm v.asIdeal := by
        change @Fintype.card _ (R.exterior.residueFinite pi) = _
        rw [R.exterior.residue_card, R.exterior.prime_val]
      obtain ⟨resEq, hresEqBij, hresEqMk⟩ := euler_residueRing_bijective R v hv
      have hresReduce (x : Qt) : resEq (rho x) = residue v (x.out : F) := by
        have hxmk : rho x = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := by
          calc
            rho x = rho (Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out) :=
              congrArg rho (Ideal.Quotient.mk_out x).symm
            _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) x.out := hrhoMk x.out
        rw [hxmk]
        exact hresEqMk x.out
      have hcardSum := euler_addHom_card_eq_card_mul_fiber f hrho
      rw [hcardQt, hcardQ1] at hcardSum
      have hpow : Ideal.absNorm v.asIdeal ^ t =
          Ideal.absNorm v.asIdeal * Ideal.absNorm v.asIdeal ^ (t - 1) := by
        have ht' : (t - 1) + 1 = t := by omega
        calc
          _ = Ideal.absNorm v.asIdeal ^ ((t - 1) + 1) :=
            congrArg (fun n : ℕ => Ideal.absNorm v.asIdeal ^ n) ht'.symm
          _ = Ideal.absNorm v.asIdeal ^ (t - 1) * Ideal.absNorm v.asIdeal := by
            rw [pow_succ]
          _ = _ := Nat.mul_comm _ _
      have hfiber0 : Fintype.card {x : Qt // f x = 0} =
          Ideal.absNorm v.asIdeal ^ (t - 1) := by
        have hqpos : 0 < Ideal.absNorm v.asIdeal := by
          exact lt_trans Nat.zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)
        rw [hpow] at hcardSum
        exact Nat.mul_left_cancel hqpos hcardSum.symm
      have hfiber (a : Q1) : Fintype.card {x : Qt // rho x = a} =
          Ideal.absNorm v.asIdeal ^ (t - 1) := by
        simpa [f] using (euler_addHom_fiber_card f hrho a).trans hfiber0
      let d₀ : Q0 := 0
      obtain ⟨_, cT, pRT, hpT, hpTgen⟩ := euler_prime_power_quotient_generator R v hv t
      have houterCond (d : Q0) : ∃ x : S.R,
          (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
            (primeGen R v : F) ^ 0 * (x : F) := by
        refine ⟨pRJ - pRT * d.out, ?_⟩
        rw [hpJ, hpT, pow_zero]
        simp
      have hlocalC0 : localC R v hv t 0 J =
          ∑ᶠ x : Qt, (if t = 0 then 1 else chiPow D v (x.out : F) t) *
            A.ψ v (algebraMap F (v.adicCompletion F)
              (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d₀.out : F)) *
                (x.out : F) / (primeGen R v : F) ^ t))) := by
        unfold localC
        rw [finsum_eq_sum_of_fintype]
        rw [Finset.sum_eq_single_of_mem d₀ (Finset.mem_univ _) (by
          intro d hd hne
          exact False.elim (hne (Subsingleton.elim d d₀)))]
        split
        · simp only [if_pos (by norm_num : (0 : ℕ) = 0), one_mul]
          simp [Qt, It, pi]
        · rename_i hfalse
          exact False.elim (hfalse (houterCond d₀))
      have h0 : localC R v hv t 0 J = (if t - 1 ≤ J then
          (qI v.asIdeal : ℂ) ^ (t - 1) *
            localT R v t ((primeGen R v : F) ^ (J + 1 - t)) else 0) := by
        by_cases hcut : t - 1 ≤ J
        · let m : ℕ := J + 1 - t
          have hm : m + t = J + 1 := by
            dsimp [m]
            omega
          have hm' : t + m = J + 1 := by omega
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hfrac : (primeGen R v : F) ^ J / (primeGen R v : F) ^ t =
              (primeGen R v : F) ^ m / (primeGen R v : F) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            field_simp [hpne]
            rw [← pow_succ, ← pow_add, hm']
          have hbase (x : Qt) :
              -((primeGen R v : F) ^ J * (x.out : F) /
                (primeGen R v : F) ^ t) =
              -((pRm : F) * (x.out : F) / (primeGen R v : F)) := by
            have hmul : (primeGen R v : F) ^ J * (x.out : F) /
                (primeGen R v : F) ^ t =
                ((primeGen R v : F) ^ J / (primeGen R v : F) ^ t) * (x.out : F) := by
              ring
            rw [hmul, hfrac, hpm]
            ring
          have harg (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                    (d₀.out : F)) * (x.out : F) /
                  (primeGen R v : F) ^ t))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((pRm : F) * (x.out : F) / (primeGen R v : F)))) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            let a := -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
              (d₀.out : F)) * (x.out : F) / (primeGen R v : F) ^ t)
            let b := -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
            have hab : a - b = (d₀.out * x.out : S.R) := by
              dsimp [a, b]
              field_simp [hpne]
              ring
            have habVal : HeightOneSpectrum.valuation F v (a - b) ≤ 1 := by
              rw [hab]
              exact (d₀.out * x.out).property v hv
            calc
              A.ψ v (algebraMap F (v.adicCompletion F) a) =
                  A.ψ v (algebraMap F (v.adicCompletion F) b) :=
                euler_addchar_congr_integral A v a b habVal
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((pRm : F) * (x.out : F) / (primeGen R v : F)))) := by
                rw [← hbase x]
          let g : Qt → ℂ := fun x =>
            chiPow D v (x.out : F) t * A.ψ v (algebraMap F (v.adicCompletion F)
              (-((pRm : F) * (x.out : F) / (primeGen R v : F))))
          have hCsum : localC R v hv t 0 J = ∑ x : Qt, g x := by
            rw [hlocalC0, finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro x hx
            change (if t = 0 then 1 else chiPow D v (x.out : F) t) *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                      (d₀.out : F)) * (x.out : F) /
                    (primeGen R v : F) ^ t))) = g x
            rw [if_neg (Nat.ne_of_gt ht), harg x]
          have hconst (x y : Qt) (hxy : rho x = rho y) : g x = g y := by
            have hres : residue v (x.out : F) = residue v (y.out : F) := by
              rw [← hresReduce x, hxy, hresReduce y]
            simpa [g] using euler_localFactor_residue_congr R v hv pRm x.out y.out t hres
          let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun z =>
            ⟨algebraMap (𝓞 F) F z.out, fun w hw => w.valuation_le_one z.out⟩
          have hresLift (z : 𝓞 F ⧸ v.asIdeal) :
              residue v ((liftResidue z : S.R) : F) = z := by
            change residue v (algebraMap (𝓞 F) F z.out) = z
            calc
              _ = Ideal.Quotient.mk v.asIdeal z.out :=
                (a2_bridge_SYMBOL D S).residue_algebraMap v z.out
              _ = z := Ideal.Quotient.mk_out z
          have hresEqLift (z : 𝓞 F ⧸ v.asIdeal) :
              resEq (Ideal.Quotient.mk
                (Ideal.span {R.exterior.genR pi}) (liftResidue z)) = z := by
            rw [hresEqMk, hresLift]
          let G : (𝓞 F ⧸ v.asIdeal) → ℂ := fun z =>
            chiPow D v ((liftResidue z : S.R) : F) t *
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((pRm : F) * ((liftResidue z : S.R) : F) /
                  (primeGen R v : F))))
          have hfiberSum : ∑ x : Qt, g x =
              ∑ b : Q1,
                (Fintype.card {x : Qt // rho x = b} : ℂ) *
                  g (Classical.choose (hrho b)) := by
            calc
              _ = ∑ b : Q1,
                    Fintype.card {x : Qt // rho x = b} •
                      g (Classical.choose (hrho b)) :=
                euler_sum_fiberwise_const rho hrho g hconst
              _ = _ := by
                apply Finset.sum_congr rfl
                intro b hb
                simp
          have hcardComplex (b : Q1) :
              (Fintype.card {x : Qt // rho x = b} : ℂ) =
                (qI v.asIdeal : ℂ) ^ (t - 1) := by
            rw [hfiber b]
            simp [qI]
          have hpoint (b : Q1) :
              g (Classical.choose (hrho b)) = G (resEq b) := by
            let x : Qt := Classical.choose (hrho b)
            have hx : rho x = b := Classical.choose_spec (hrho b)
            have hres : residue v (x.out : F) =
                residue v ((liftResidue (resEq b) : S.R) : F) := by
              calc
                residue v (x.out : F) = resEq (rho x) := (hresReduce x).symm
                _ = resEq b := by rw [hx]
                _ = residue v ((liftResidue (resEq b) : S.R) : F) :=
                  (hresLift (resEq b)).symm
            simpa [g, G, x] using
              euler_localFactor_residue_congr R v hv pRm x.out
                (liftResidue (resEq b)) t hres
          have hreindex :
              ∑ b : Q1, g (Classical.choose (hrho b)) =
                ∑ z : 𝓞 F ⧸ v.asIdeal, G z := by
            exact Fintype.sum_equiv (Equiv.ofBijective resEq hresEqBij)
              _ _ hpoint
          have hfactor :
              ∑ b : Q1,
                (Fintype.card {x : Qt // rho x = b} : ℂ) *
                  g (Classical.choose (hrho b)) =
                (qI v.asIdeal : ℂ) ^ (t - 1) *
                  ∑ z : 𝓞 F ⧸ v.asIdeal, G z := by
            calc
              _ = ∑ b : Q1,
                    (qI v.asIdeal : ℂ) ^ (t - 1) *
                      g (Classical.choose (hrho b)) := by
                apply Finset.sum_congr rfl
                intro b hb
                rw [hcardComplex]
              _ = (qI v.asIdeal : ℂ) ^ (t - 1) *
                    ∑ b : Q1, g (Classical.choose (hrho b)) := by
                rw [Finset.mul_sum]
              _ = _ := by rw [hreindex]
          have hG : ∑ z : 𝓞 F ⧸ v.asIdeal, G z =
              localT R v t (pRm : F) := by
            unfold localT
            rw [a2_bridge_FINITE_CHAR_finsum]
          rw [hCsum, hfiberSum, hfactor, hG]
          rw [if_pos (by omega)]
          rw [← hpm]
        · let gl : Qt → ℂ := fun x =>
            chiPow D v (x.out : F) t *
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((primeGen R v : F) ^ J * (x.out : F) /
                  (primeGen R v : F) ^ t)))
          have hphaseBase (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                    (d₀.out : F)) * (x.out : F) /
                  (primeGen R v : F) ^ t))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((primeGen R v : F) ^ J * (x.out : F) /
                  (primeGen R v : F) ^ t))) := by
            have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
            let a := -(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
              (d₀.out : F)) * (x.out : F) / (primeGen R v : F) ^ t)
            let b := -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
            have hab : a - b = (d₀.out * x.out : S.R) := by
              dsimp [a, b]
              field_simp [hpne]
              ring
            have habVal : HeightOneSpectrum.valuation F v (a - b) ≤ 1 := by
              rw [hab]
              exact (d₀.out * x.out).property v hv
            exact euler_addchar_congr_integral A v a b habVal
          have hCsumLow : localC R v hv t 0 J = ∑ x : Qt, gl x := by
            rw [hlocalC0, finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro x hx
            rw [if_neg (Nat.ne_of_gt ht), hphaseBase x]
          obtain ⟨hchars, hchiSix, hpsi⟩ :=
            a2_bridge_FINITE_CHAR D S A v hv (primeGen R v) (by
              have h := (bc.gen_spec pi).1
              simpa [pi, primeGen, hv, R.exterior.prime_val] using h)
          obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
          have hψne : ψ ≠ (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by
            intro h
            have hshift : ψ.mulShift (1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
              ext z
              simp [AddChar.mulShift_apply, h]
            exact (hψprim one_ne_zero) hshift
          have hψwitness : ∃ z : 𝓞 F ⧸ v.asIdeal, ψ z ≠ 1 := by
            by_contra h
            push_neg at h
            apply hψne
            ext z
            exact h z
          obtain ⟨z, hz⟩ := hψwitness
          have hz0 : z ≠ 0 := by
            intro hz0
            subst z
            simpa using hz
          let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
            ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
          have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
              residue v ((liftResidue a : S.R) : F) = a := by
            change residue v (algebraMap (𝓞 F) F a.out) = a
            calc
              _ = Ideal.Quotient.mk v.asIdeal a.out :=
                (a2_bridge_SYMBOL D S).residue_algebraMap v a.out
              _ = a := Ideal.Quotient.mk_out a
          let posProdR : S.R := liftResidue 1 * liftResidue z
          have hresPosProd : residue v (posProdR : F) = z := by
            change residue v ((liftResidue 1 : S.R) * (liftResidue z : S.R) : F) = z
            rw [(a2_bridge_SYMBOL D S).residue_mul v
              (liftResidue 1 : F) (liftResidue z : F)
              ((liftResidue 1).property v hv) ((liftResidue z).property v hv),
              hresLift, hresLift]
            simp
          let negProdR : S.R := -posProdR
          have hresZero : residue v (0 : F) = 0 := by
            simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
          have hresNegProd : residue v (negProdR : F) = -z := by
            have hsum := euler_residue_add_integral v
              (negProdR : F) (posProdR : F)
              ((negProdR).property v hv) ((posProdR).property v hv)
            have hident : (negProdR : F) + (posProdR : F) = 0 := by
              dsimp [negProdR]
              ring
            rw [hident, hresZero, hresPosProd] at hsum
            exact eq_neg_iff_add_eq_zero.mpr hsum.symm
          let lambdaR : S.R := liftResidue (-z)
          have hresLambda : residue v (lambdaR : F) = -z := hresLift (-z)
          have hresNegEq : residue v (negProdR : F) = residue v (lambdaR : F) :=
            hresNegProd.trans hresLambda.symm
          have hnegProdNe : residue v (negProdR : F) ≠ 0 := by
            rw [hresNegProd]
            exact neg_ne_zero.mpr hz0
          have hlambdaNe : residue v (lambdaR : F) ≠ 0 := by
            rw [hresLambda]
            exact neg_ne_zero.mpr hz0
          have hmaskNeg : chiPow D v (negProdR : F) (0 : ℤ) = 1 := by
            simp [chiPow, hnegProdNe]
          have hmaskLambda : chiPow D v (lambdaR : F) (0 : ℤ) = 1 := by
            simp [chiPow, hlambdaNe]
          have hlocalCompare :=
            euler_localFactor_residue_congr R v hv 1 negProdR lambdaR 0 hresNegEq
          have hargPos : -((1 : F) * (negProdR : F) /
              (primeGen R v : F)) = (posProdR : F) / (primeGen R v : F) := by
            dsimp [negProdR]
            ring
          have hargLambda : -((1 : F) * (lambdaR : F) /
              (primeGen R v : F)) = -((lambdaR : F) / (primeGen R v : F)) := by
            ring
          have hψCompare :
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((posProdR : F) / (primeGen R v : F))) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((lambdaR : F) / (primeGen R v : F)))) := by
            rw [hmaskNeg, hmaskLambda, one_mul, one_mul] at hlocalCompare
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((1 : F) * (negProdR : F) / (primeGen R v : F)))) :=
                congrArg (fun w : F => A.ψ v (algebraMap F (v.adicCompletion F) w))
                  hargPos.symm
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((1 : F) * (lambdaR : F) / (primeGen R v : F)))) := hlocalCompare
              _ = _ := congrArg
                (fun w : F => A.ψ v (algebraMap F (v.adicCompletion F) w)) hargLambda
          have hψevalProd : ψ z =
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((posProdR : F) / (primeGen R v : F))) := by
            simpa [posProdR, liftResidue] using hψeval z (1 : 𝓞 F ⧸ v.asIdeal)
          let c : ℂ := ψ z
          have hψconst :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-((lambdaR : F) / (primeGen R v : F)))) = c := by
            exact (hψevalProd.trans hψCompare).symm
          let r : ℕ := t - 1 - J
          have hr : 0 < r := by
            dsimp [r]
            omega
          have hJr : J + r + 1 = t := by
            dsimp [r]
            omega
          obtain ⟨_, _, pRr, hpRr, _⟩ :=
            euler_prime_power_quotient_generator R v hv r
          obtain ⟨_, _, pRprev, hpRprev, _⟩ :=
            euler_prime_power_quotient_generator R v hv (r - 1)
          obtain ⟨_, c1, pR1, hpR1, hpR1gen⟩ :=
            euler_prime_power_quotient_generator R v hv 1
          have hpPowMul : (primeGen R v : F) ^ r =
              (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (r - 1) := by
            have hr' : 1 + (r - 1) = r := by omega
            calc
              _ = (primeGen R v : F) ^ (1 + (r - 1)) :=
                congrArg (fun n : ℕ => (primeGen R v : F) ^ n) hr'.symm
              _ = _ := by rw [pow_add]
          have hprev : pRr = pR1 * pRprev := by
            apply Subtype.ext
            calc
              (pRr : F) = (primeGen R v : F) ^ r := hpRr.symm
              _ = (primeGen R v : F) ^ 1 * (primeGen R v : F) ^ (r - 1) := hpPowMul
              _ = (pR1 : F) * (pRprev : F) := by rw [← hpR1, ← hpRprev]
          have hpGen : S.IsGen (primeGen R v : F) v.asIdeal := by
            have h := (bc.gen_spec pi).1
            simpa [pi, primeGen, hv, R.exterior.prime_val] using h
          have hpR1Gen : S.IsGen (pR1 : F) v.asIdeal := by
            rw [← hpR1, pow_one]
            exact hpGen
          have hpiGen : S.IsGen (R.exterior.genR pi : F) v.asIdeal := by
            rw [R.exterior.genR_val pi]
            have h := (bc.gen_spec pi).1
            simpa [pi, R.exterior.prime_val] using h
          have hspan1 : Ideal.span ({pR1} : Set S.R) =
              Ideal.span {R.exterior.genR pi} :=
            euler_span_singleton_eq_of_generators v hv v.asIdeal pR1
              (R.exterior.genR pi) hpR1Gen hpiGen
          have hspanT : Ideal.span ({pRT} : Set S.R) =
              Ideal.span {R.exterior.genR It} := by
            rw [hpTgen]
            exact Ideal.span_singleton_mul_left_unit cT.isUnit
              (R.exterior.genR It)
          let zR : S.R := pRr * lambdaR
          have hzMem : zR ∈ Ideal.span ({pR1} : Set S.R) := by
            apply Ideal.mem_span_singleton.mpr
            refine ⟨pRprev * lambdaR, ?_⟩
            dsimp [zR]
            rw [hprev]
            ring
          let δ : Qt := Ideal.Quotient.mk
            (Ideal.span {R.exterior.genR It}) zR
          have hredδ : rho δ = 0 := by
            change rho (Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR It}) zR) = 0
            rw [hrhoMk]
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            rw [← hspan1]
            exact hzMem
          let τ : Qt ≃ Qt := {
            toFun := fun x => x + δ
            invFun := fun x => x - δ
            left_inv := by intro x; simp
            right_inv := by intro x; simp }
          have hredτ (x : Qt) : rho (τ x) = rho x := by
            change rho (x + δ) = rho x
            calc
              rho (x + δ) = rho x + rho δ := rho.map_add x δ
              _ = rho x := by rw [hredδ]; simp
          have hresτ (x : Qt) :
              residue v ((τ x).out : F) = residue v (x.out : F) := by
            calc
              residue v ((τ x).out : F) = resEq (rho (τ x)) :=
                (hresReduce (τ x)).symm
              _ = resEq (rho x) := by rw [hredτ]
              _ = residue v (x.out : F) := hresReduce x
          have hquotτ (x : Qt) :
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) (τ x).out =
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR It})
                  (x.out + zR) := by
            calc
              _ = τ x := Ideal.Quotient.mk_out (τ x)
              _ = x + δ := rfl
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) x.out +
                    Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) zR := by
                rw [Ideal.Quotient.mk_out x]
              _ = _ := by simp [δ]
          have hmemT (x : Qt) :
              (τ x).out - (x.out + zR) ∈ Ideal.span ({pRT} : Set S.R) := by
            have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
              (τ x).out (x.out + zR)).mp (hquotτ x)
            exact hspanT.symm ▸ hm
          let aLift (x : Qt) : S.R :=
            Classical.choose (Ideal.mem_span_singleton.mp (hmemT x))
          have haLift (x : Qt) :
              (τ x).out - (x.out + zR) = pRT * aLift x :=
            Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemT x))
          have hdelta (x : Qt) :
              ((τ x).out : F) - (x.out : F) =
                (zR : F) + (pRT : F) * (aLift x : F) := by
            have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
            change ((τ x).out : F) - ((x.out : F) + (zR : F)) =
              (pRT : F) * (aLift x : F) at haF
            calc
              ((τ x).out : F) - (x.out : F) =
                  (((τ x).out : F) - ((x.out : F) + (zR : F))) + (zR : F) := by ring
              _ = (pRT : F) * (aLift x : F) + (zR : F) := by rw [haF]
              _ = (zR : F) + (pRT : F) * (aLift x : F) := by ring
          have hpne : (primeGen R v : F) ≠ 0 := Units.ne_zero _
          have hratio : (primeGen R v : F) ^ J *
              (primeGen R v : F) ^ r / (primeGen R v : F) ^ t =
                1 / (primeGen R v : F) := by
            calc
              _ = (primeGen R v : F) ^ (J + r) /
                    (primeGen R v : F) ^ t := by rw [← pow_add]
              _ = 1 / (primeGen R v : F) := by
                field_simp [hpne]
                rw [← pow_succ, hJr]
          have hscale : (primeGen R v : F) ^ J * (zR : F) /
              (primeGen R v : F) ^ t = (lambdaR : F) /
                (primeGen R v : F) := by
            calc
              _ = ((primeGen R v : F) ^ J * (primeGen R v : F) ^ r /
                    (primeGen R v : F) ^ t) * (lambdaR : F) := by
                dsimp [zR]
                rw [← hpRr]
                ring
              _ = (1 / (primeGen R v : F)) * (lambdaR : F) := by rw [hratio]
              _ = _ := by ring
          let arg (x : Qt) : F :=
            -((primeGen R v : F) ^ J * (x.out : F) /
              (primeGen R v : F) ^ t)
          let cArg : F := -((lambdaR : F) / (primeGen R v : F))
          have hargDiff (x : Qt) :
              arg (τ x) - (arg x + cArg) =
                -((primeGen R v : F) ^ J * (aLift x : F)) := by
            have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
            change ((τ x).out : F) - ((x.out : F) + (zR : F)) =
              (pRT : F) * (aLift x : F) at haF
            have hfirst : arg (τ x) - (arg x + cArg) =
                -((primeGen R v : F) ^ J * (zR : F) /
                    (primeGen R v : F) ^ t) -
                  (primeGen R v : F) ^ J * (aLift x : F) +
                    (lambdaR : F) / (primeGen R v : F) := by
              dsimp [arg, cArg]
              calc
                _ = -((primeGen R v : F) ^ J *
                      (((τ x).out : F) - (x.out : F)) /
                      (primeGen R v : F) ^ t) +
                    (lambdaR : F) / (primeGen R v : F) := by ring
                _ = _ := by
                  rw [hdelta x, ← hpT]
                  field_simp [hpne]
                  ring
            rw [hfirst, hscale, hpJ]
            ring
          have hphaseTrans (x : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ x))) =
                c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
            have hval : HeightOneSpectrum.valuation F v
                (arg (τ x) - (arg x + cArg)) ≤ 1 := by
              rw [hargDiff x, hpJ]
              exact (-(pRJ * aLift x)).property v hv
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (arg x + cArg)) :=
                euler_addchar_congr_integral A v (arg (τ x)) (arg x + cArg) hval
              _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) *
                    A.ψ v (algebraMap F (v.adicCompletion F) cArg) := by
                rw [← (A.ψ v).map_add_eq_mul]
                simp
              _ = c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
                rw [show cArg = -((lambdaR : F) / (primeGen R v : F)) by rfl,
                  hψconst]
                ring
          have htrans (x : Qt) : gl (τ x) = c * gl x := by
            have hchi := euler_chiPow_residue_congr D S v
              (x.out : F) ((τ x).out : F) (t : ℤ) (hresτ x).symm
            dsimp [gl]
            rw [hchi, hphaseTrans]
            ring
          have hsumShift : (∑ x : Qt, gl x) = ∑ x : Qt, gl (τ x) := by
            exact Fintype.sum_equiv τ.symm _ _ (by intro x; simp)
          have hsumMul : (∑ x : Qt, gl (τ x)) =
              c * ∑ x : Qt, gl x := by
            calc
              _ = ∑ x : Qt, c * gl x := by
                apply Finset.sum_congr rfl
                intro x hx
                exact htrans x
              _ = _ := by rw [Finset.mul_sum]
          have hsumEq : (∑ x : Qt, gl x) = c * ∑ x : Qt, gl x :=
            hsumShift.trans hsumMul
          have hsumZero : (∑ x : Qt, gl x) = 0 := by
            have hmul : (1 - c) * (∑ x : Qt, gl x) = 0 := by
              calc
                _ = (∑ x : Qt, gl x) - c * ∑ x : Qt, gl x := by ring
                _ = 0 := by rw [← hsumEq]; ring
            have hcnz : 1 - c ≠ 0 := by
              apply sub_ne_zero.mpr
              intro heq
              apply hz
              simpa [c] using heq.symm
            exact (mul_eq_zero.mp hmul).resolve_left hcnz
          rw [hCsumLow]
          rw [if_neg hcut]
          exact hsumZero
      have hC1 : localC R v hv t 1 J =
          (if t ≤ J then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
            localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (J - t)) else 0) := by
        by_cases hJ0 : J = 0
        · subst J
          let I1 := R.exterior.pow pi 1
          let Q1local := ResidueRing R.exterior I1
          letI : Fintype Q1local := R.exterior.residueFinite I1
          let p : Fˣ := primeGen R v
          have hpValLocal : HeightOneSpectrum.valuation F v (p : F) =
              WithZero.exp (-1 : ℤ) := by simpa [p] using euler_primeGen_valuation R v hv
          have hpLtLocal : HeightOneSpectrum.valuation F v (p : F) < 1 := by
            rw [hpValLocal]
            simp
          obtain ⟨_, _, pRTprev, hpRTprev, _⟩ :=
            euler_prime_power_quotient_generator R v hv (t - 1)
          have hpTfactor : (p : F) ^ t = (p : F) * (pRTprev : F) := by
            have ht' : t = 1 + (t - 1) := by omega
            rw [ht', pow_add, hpRTprev]
            simp [p]
          have hnoSupport (d : Q1local) :
              ¬ ∃ z : S.R, (p : F) ^ 0 - (p : F) ^ t * (d.out : F) =
                (p : F) ^ 1 * (z : F) := by
            rintro ⟨z, hz⟩
            have hz' : 1 - (p : F) ^ t * (d.out : F) =
                (p : F) * (z : F) := by simpa [pow_zero, pow_one] using hz
            let w : S.R := z + pRTprev * d.out
            have hw : (p : F) * (w : F) = 1 := by
              dsimp [w]
              have hz'' := hz'
              rw [hpTfactor] at hz''
              calc
                (p : F) * ((z : F) + (pRTprev : F) * (d.out : F)) =
                    (p : F) * (z : F) +
                      (p : F) * ((pRTprev : F) * (d.out : F)) := by rw [mul_add]
                _ = 1 := by
                  rw [← mul_assoc, ← hz'']
                  exact sub_add_cancel _ _
            have hwVal : HeightOneSpectrum.valuation F v (w : F) ≤ 1 := w.property v hv
            have hwProd : HeightOneSpectrum.valuation F v ((p : F) * (w : F)) < 1 := by
              rw [(v.valuation F).map_mul]
              by_cases hw0 : HeightOneSpectrum.valuation F v (w : F) = 0
              · rw [hw0, mul_zero]
                exact zero_lt_one
              · have hwpos : 0 < HeightOneSpectrum.valuation F v (w : F) :=
                  lt_of_le_of_ne zero_le (Ne.symm hw0)
                calc
                  _ < 1 * HeightOneSpectrum.valuation F v (w : F) :=
                    mul_lt_mul_of_pos_right hpLtLocal hwpos
                  _ ≤ 1 := by simpa using hwVal
            rw [hw] at hwProd
            simp at hwProd
          unfold localC
          rw [finsum_eq_sum_of_fintype]
          change (∑ d ∈ (Finset.univ : Finset Q1local),
              (if ∃ z : S.R, (primeGen R v : F) ^ 0 -
                  (primeGen R v : F) ^ t * (d.out : F) =
                    (primeGen R v : F) ^ 1 * (z : F) then
                (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                  ∑ᶠ z : Qt,
                    (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                      A.ψ v (algebraMap F (v.adicCompletion F)
                        (-(((primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t *
                            (d.out : F)) * (z.out : F) /
                          (primeGen R v : F) ^ (1 + t)))) else 0)) =
            if t ≤ 0 then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
              localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (0 - t)) else 0
          rw [if_neg (by omega)]
          apply Finset.sum_eq_zero
          intro d hd
          have hcond : ¬ ∃ z : S.R,
              (primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) := by
            simpa only [p, pow_zero, pow_one] using hnoSupport d
          change (if ∃ z : S.R,
              (primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) then
              (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                ∑ᶠ z : Qt,
                  (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-(((primeGen R v : F) ^ 0 - (primeGen R v : F) ^ t *
                          (d.out : F)) * (z.out : F) /
                        (primeGen R v : F) ^ (1 + t)))) else 0) = 0
          rw [if_neg hcond]
        · have hJpos : 0 < J := by omega
          let I1 := R.exterior.pow pi 1
          let Q1local := ResidueRing R.exterior I1
          letI : Fintype Q1local := R.exterior.residueFinite I1
          let p : Fˣ := primeGen R v
          have hpne : (p : F) ≠ 0 := Units.ne_zero _
          have hpValLocal : HeightOneSpectrum.valuation F v (p : F) =
              WithZero.exp (-1 : ℤ) := by simpa [p] using euler_primeGen_valuation R v hv
          obtain ⟨_, _, pRJm1, hpRJm1, _⟩ :=
            euler_prime_power_quotient_generator R v hv (J - 1)
          obtain ⟨_, _, pRTm1, hpRTm1, _⟩ :=
            euler_prime_power_quotient_generator R v hv (t - 1)
          have hpJfactor : (p : F) ^ J = (p : F) * (pRJm1 : F) := by
            have hJ' : J = 1 + (J - 1) := by omega
            rw [hJ', pow_add, hpRJm1]
            simp [p]
          have hpTfactor1 : (p : F) ^ t = (p : F) * (pRTm1 : F) := by
            have ht' : t = 1 + (t - 1) := by omega
            rw [ht', pow_add, hpRTm1]
            simp [p]
          obtain ⟨rho1, hrho1, hrho1Mk⟩ :=
            euler_primePower_reduction R v hv 1 (by norm_num)
          have hcardQ1local : Fintype.card Q1local = Ideal.absNorm v.asIdeal := by
            simpa [Q1local, I1, pi] using euler_residue_card_pow R v hv 1
          have hcardSame : Fintype.card Q1local = Fintype.card Q1 :=
            hcardQ1local.trans hcardQ1.symm
          have hbij1 : Function.Bijective rho1 :=
            (Fintype.bijective_iff_surjective_and_card rho1).2 ⟨hrho1, hcardSame⟩
          let e1 : Q1local ≃ Q1 := Equiv.ofBijective rho1 hbij1
          have hredMk1 (d : Q1local) :
              rho1 d = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out := by
            calc
              rho1 d = rho1 (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR I1}) d.out) :=
                congrArg rho1 (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out :=
                hrho1Mk d.out
          have hresD1 (d : Q1local) :
              residue v (d.out : F) = residue v ((rho1 d).out : F) := by
            calc
              residue v (d.out : F) =
                  resEq (Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out) :=
                (hresEqMk d.out).symm
              _ = resEq (rho1 d) := by rw [hredMk1]
              _ = resEq (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) (rho1 d).out) := by
                rw [Ideal.Quotient.mk_out]
              _ = residue v ((rho1 d).out : F) := hresEqMk (rho1 d).out
          have houterLocal (x₀ : Qt) (hx₀ : residue v (x₀.out : F) ≠ 0) :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F)))) =
                localT R v 1 1 * star (chi D v (x₀.out : F)) := by
            let f₁ : Q1 → ℂ := fun b =>
              chiPow D v (b.out : F) 1 * A.ψ v (algebraMap F (v.adicCompletion F)
                ((b.out : F) * (x₀.out : F) / (p : F)))
            have hterm (d : Q1local) :
                chiPow D v (d.out : F) 1 * A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F))) = f₁ (rho1 d) := by
              have hchi := euler_chiPow_residue_congr D S v
                (d.out : F) ((rho1 d).out : F) 1 (hresD1 d)
              have hresProd : residue v ((d.out * x₀.out : S.R) : F) =
                  residue v (((rho1 d).out * x₀.out : S.R) : F) := by
                calc
                  _ = residue v (d.out : F) * residue v (x₀.out : F) :=
                    SB.residue_mul v (d.out : F) (x₀.out : F)
                      (d.out.property v hv) (x₀.out.property v hv)
                  _ = residue v ((rho1 d).out : F) * residue v (x₀.out : F) := by
                    rw [hresD1]
                  _ = _ := (SB.residue_mul v ((rho1 d).out : F) (x₀.out : F)
                    ((rho1 d).out.property v hv) (x₀.out.property v hv)).symm
              have hpsi := euler_addchar_div_residue_congr D A v hv p hpValLocal
                (d.out * x₀.out) ((rho1 d).out * x₀.out) hresProd
              have hpsi' : A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (x₀.out : F) / (p : F))) =
                  A.ψ v (algebraMap F (v.adicCompletion F)
                  (((rho1 d).out : F) * (x₀.out : F) / (p : F))) := by
                simpa only [Subalgebra.coe_mul] using hpsi
              calc
                _ = chiPow D v ((rho1 d).out : F) 1 *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((d.out : F) * (x₀.out : F) / (p : F))) := by rw [hchi]
                _ = _ := by rw [hpsi']
            calc
              _ = ∑ d : Q1local, f₁ (rho1 d) := by
                apply Finset.sum_congr rfl
                intro d hd
                exact hterm d
              _ = ∑ b : Q1, f₁ b := by
                exact Fintype.sum_equiv e1 (fun d => f₁ (e1 d)) f₁
                  (by intro d; rfl)
              _ = localT R v 1 1 * star (chi D v (x₀.out : F)) :=
                euler_localD_gauss_sum R v hv x₀.out hx₀
          let yD : Q1local → S.R := fun d => pRJm1 - pRTm1 * d.out
          have hnum (d : Q1local) :
              (p : F) ^ J - (p : F) ^ t * (d.out : F) =
                (p : F) * (yD d : F) := by
            rw [hpJfactor, hpTfactor1]
            dsimp [yD]
            ring
          have hsupport (d : Q1local) : ∃ z : S.R,
              (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
                (primeGen R v : F) ^ 1 * (z : F) := by
            refine ⟨yD d, ?_⟩
            simpa [p, pow_one] using hnum d
          have hargSplit (d : Q1local) (z : Qt) :
              -(((p : F) ^ J - (p : F) ^ t * (d.out : F)) * (z.out : F) /
                  (p : F) ^ (1 + t)) =
                -((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) +
                  (d.out : F) * (z.out : F) / (p : F) := by
            field_simp [hpne]
            ring
          have hphaseFactor (d : Q1local) (z : Qt) :
              A.ψ v (algebraMap F (v.adicCompletion F)
                (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) * (z.out : F) /
                    (p : F) ^ (1 + t)))) =
                A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
              A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (z.out : F) / (p : F))) := by
            have hmap : algebraMap F (v.adicCompletion F)
                (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) +
                  (d.out : F) * (z.out : F) / (p : F)) =
                algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))) +
                  algebraMap F (v.adicCompletion F)
                    ((d.out : F) * (z.out : F) / (p : F)) := by simp
            rw [hargSplit]
            rw [hmap]
            exact (A.ψ v).map_add_eq_mul _ _
          have hCsum : localC R v hv t 1 J =
              ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
                        (z.out : F) / (p : F) ^ (1 + t)))) := by
            unfold localC
            simp_rw [finsum_eq_sum_of_fintype]
            apply Finset.sum_congr rfl
            intro d hd
            have hs := hsupport d
            change (if ∃ z : S.R,
                (primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                  (d.out : F) = (primeGen R v : F) ^ 1 * (z : F) then
                (if 1 = 0 then 1 else chiPow D v (d.out : F) 1) *
                  ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                          (d.out : F)) * (z.out : F) /
                        (primeGen R v : F) ^ (1 + t)))) else 0) =
              chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t *
                        (d.out : F)) * (z.out : F) /
                      (primeGen R v : F) ^ (1 + t))))
            rw [if_pos hs]
            simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0)]
          have hsumRearrange :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                ∑ z : Qt, (if t = 0 then 1 else chiPow D v (z.out : F) t) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
                        (z.out : F) / (p : F) ^ (1 + t))))) =
                ∑ z : Qt, chiPow D v (z.out : F) t *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                  ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((d.out : F) * (z.out : F) / (p : F))) := by
            simp only [if_neg (Nat.ne_of_gt ht)]
            simp_rw [hphaseFactor]
            calc
              _ = ∑ d : Q1local, ∑ z : Qt,
                  chiPow D v (d.out : F) 1 *
                    (chiPow D v (z.out : F) t *
                      (A.ψ v (algebraMap F (v.adicCompletion F)
                        (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                        A.ψ v (algebraMap F (v.adicCompletion F)
                          ((d.out : F) * (z.out : F) / (p : F))))) := by
                apply Finset.sum_congr rfl
                intro d hd
                rw [Finset.mul_sum]
              _ = ∑ z : Qt, ∑ d : Q1local,
                  chiPow D v (d.out : F) 1 *
                    (chiPow D v (z.out : F) t *
                      (A.ψ v (algebraMap F (v.adicCompletion F)
                        (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                        A.ψ v (algebraMap F (v.adicCompletion F)
                          ((d.out : F) * (z.out : F) / (p : F))))) :=
                Finset.sum_comm
              _ = _ := by
                apply Finset.sum_congr rfl
                intro z hz
                conv_rhs => rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro d hd
                ring
          have houter (z : Qt) (hz : residue v (z.out : F) ≠ 0) :
              (∑ d : Q1local, chiPow D v (d.out : F) 1 *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((d.out : F) * (z.out : F) / (p : F)))) =
                localT R v 1 1 * star (chi D v (z.out : F)) := by
            exact houterLocal z hz
          have hcharTimes (z : Qt) :
              chiPow D v (z.out : F) t * star (chi D v (z.out : F)) =
                chiPow D v (z.out : F) ((t : ℤ) - 1) := by
            by_cases hz : residue v (z.out : F) = 0
            · rw [SB.chiPow_zero v (z.out : F) t hz,
                SB.chiPow_zero v (z.out : F) ((t : ℤ) - 1) hz]
              simp
            · rw [SB.chiPow_nonzero v (z.out : F) t hz,
                SB.chiPow_nonzero v (z.out : F) ((t : ℤ) - 1) hz]
              have hstar : star (chi D v (z.out : F)) =
                  (chi D v (z.out : F))⁻¹ := by
                exact (Complex.inv_eq_conj
                  (SB.chi_norm v (z.out : F) hz)).symm
              have hchiNe : chi D v (z.out : F) ≠ 0 := by
                apply norm_ne_zero_iff.mp
                rw [SB.chi_norm v (z.out : F) hz]
                norm_num
              rw [hstar]
              rw [← zpow_neg_one]
              rw [show (t : ℤ) - 1 = (t : ℤ) + (-1 : ℤ) by omega]
              conv_rhs => rw [zpow_add₀ hchiNe]
          have hcollapsed :
              (∑ z : Qt, chiPow D v (z.out : F) t *
                A.ψ v (algebraMap F (v.adicCompletion F)
                  (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) *
                ∑ d : Q1local, chiPow D v (d.out : F) 1 *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    ((d.out : F) * (z.out : F) / (p : F)))) =
              localT R v 1 1 *
                ∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)))) := by
            calc
              _ = ∑ z : Qt, localT R v 1 1 *
                  (chiPow D v (z.out : F) ((t : ℤ) - 1) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) := by
                apply Finset.sum_congr rfl
                intro z hz
                by_cases hz0 : residue v (z.out : F) = 0
                · rw [SB.chiPow_zero v (z.out : F) t hz0,
                    SB.chiPow_zero v (z.out : F) ((t : ℤ) - 1) hz0]
                  simp
                · rw [houter z hz0]
                  calc
                    _ = localT R v 1 1 *
                        ((chiPow D v (z.out : F) t *
                            star (chi D v (z.out : F))) *
                          A.ψ v (algebraMap F (v.adicCompletion F)
                            (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) := by
                      ring
                    _ = _ := by rw [hcharTimes]
              _ = _ := by rw [Finset.mul_sum]
          by_cases hcut1 : t ≤ J
          · let m : ℕ := J - t
            obtain ⟨_, _, pRm, hpm, _⟩ :=
              euler_prime_power_quotient_generator R v hv m
            have hm : J = t + m := by
              dsimp [m]
              omega
            have hpNum : (p : F) ^ J = (p : F) ^ t * (pRm : F) := by
              rw [hm, pow_add, hpm]
            have hpDen : (p : F) ^ (1 + t) = (p : F) ^ t * (p : F) := by
              rw [show 1 + t = t + 1 by omega, pow_succ]
            have hpne : (p : F) ≠ 0 := Units.ne_zero _
            have hbase (z : Qt) :
                -((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t)) =
                  -((pRm : F) * (z.out : F) / (p : F)) := by
              rw [hpNum, hpDen]
              field_simp [hpne]
            have hlocalSum :
                (∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    (-((p : F) ^ J * (z.out : F) / (p : F) ^ (1 + t))))) =
                  (qI v.asIdeal : ℂ) ^ (t - 1) *
                    localT R v ((t : ℤ) - 1) (pRm : F) := by
              calc
                _ = ∑ z : Qt, chiPow D v (z.out : F) ((t : ℤ) - 1) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      (-((pRm : F) * (z.out : F) / (p : F)))) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  rw [hbase z]
                _ = _ := by
                  simpa [Qt, It, pi] using
                    (euler_primePower_localT_sum R v hv t ht ((t : ℤ) - 1) pRm)
            rw [hCsum, hsumRearrange, hcollapsed, hlocalSum, if_pos hcut1]
            rw [hpm]
            ring
          · let r : ℕ := t - J
            have hr : 0 < r := by dsimp [r]; omega
            have hJr : J + r = t := by dsimp [r]; omega
            obtain ⟨_, _, pRr, hpRr, _⟩ :=
              euler_prime_power_quotient_generator R v hv r
            obtain ⟨_, cTt, pRTt, hpRTt, hpRTtgen⟩ :=
              euler_prime_power_quotient_generator R v hv t
            have hspanT : Ideal.span ({pRTt} : Set S.R) =
                Ideal.span {R.exterior.genR It} := by
              rw [hpRTtgen]
              exact Ideal.span_singleton_mul_left_unit cTt.isUnit
                (R.exterior.genR It)
            have hpGen' : S.IsGen (p : F) v.asIdeal := by
              have h := (bc.gen_spec pi).1
              simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
            obtain ⟨_, _, hpsi⟩ :=
              a2_bridge_FINITE_CHAR D S A v hv p hpGen'
            obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
            have hψne : ψ ≠ (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by
              intro hψone
              have hshift : ψ.mulShift (1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
                ext z
                simp [AddChar.mulShift_apply, hψone]
              exact (hψprim one_ne_zero) hshift
            have hψwitness : ∃ z : 𝓞 F ⧸ v.asIdeal, ψ z ≠ 1 := by
              by_contra h
              push_neg at h
              apply hψne
              ext z
              exact h z
            obtain ⟨z, hz⟩ := hψwitness
            have hz0 : z ≠ 0 := by
              intro hz0
              subst z
              simpa using hz
            let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
              ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
            have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
                residue v ((liftResidue a : S.R) : F) = a := by
              change residue v (algebraMap (𝓞 F) F a.out) = a
              calc
                _ = Ideal.Quotient.mk v.asIdeal a.out :=
                  SB.residue_algebraMap v a.out
                _ = a := Ideal.Quotient.mk_out a
            let lambdaR : S.R := liftResidue z
            let posProdR : S.R := liftResidue 1 * liftResidue z
            let c : ℂ := ψ z
            have hresPosProd : residue v (posProdR : F) = z := by
              change residue v ((liftResidue 1 : S.R) *
                (liftResidue z : S.R) : F) = z
              rw [SB.residue_mul v (liftResidue 1 : F) (liftResidue z : F)
                ((liftResidue 1).property v hv) ((liftResidue z).property v hv),
                hresLift, hresLift]
              simp
            have hψevalLambda :
                A.ψ v (algebraMap F (v.adicCompletion F)
                  ((lambdaR : F) / (p : F))) = c := by
              have hψevalProd : ψ z = A.ψ v (algebraMap F (v.adicCompletion F)
                  ((posProdR : F) / (p : F))) := by
                simpa [posProdR, liftResidue, p] using
                  hψeval z (1 : 𝓞 F ⧸ v.asIdeal)
              calc
                _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    ((posProdR : F) / (p : F))) :=
                  (euler_addchar_div_residue_congr D A v hv p hpValLocal
                    posProdR lambdaR (hresPosProd.trans (hresLift z).symm)).symm
                _ = ψ z := hψevalProd.symm
                _ = c := rfl
            have hpRrRes : residue v (pRr : F) = 0 := by
              rw [← hpRr, hresPowZero r hr]
            let deltaR : S.R := pRr * lambdaR
            have hresDelta : residue v (deltaR : F) = 0 := by
              change residue v ((pRr : F) * (lambdaR : F)) = 0
              rw [SB.residue_mul v (pRr : F) (lambdaR : F)
                (pRr.property v hv) (lambdaR.property v hv), hpRrRes]
              simp
            have hresZero : residue v (0 : F) = 0 := by
              simpa using SB.residue_algebraMap v (0 : 𝓞 F)
            have hresEqZero : resEq (0 : Q1) = 0 := by
              have hmk0 : Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) (0 : S.R) = (0 : Q1) := by simp
              rw [← hmk0]
              exact (hresEqMk 0).trans hresZero
            let δ : Qt := Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR It}) deltaR
            have hresRhoδ : resEq (rho δ) = 0 := by
              have hmkδ : rho δ = Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR pi}) deltaR := by
                dsimp [δ]
                exact hrhoMk deltaR
              rw [hmkδ, hresEqMk]
              exact hresDelta
            have hrhoδ : rho δ = 0 :=
              hresEqBij.1 (hresRhoδ.trans hresEqZero.symm)
            let τ : Qt ≃ Qt := {
              toFun := fun x => x - δ
              invFun := fun x => x + δ
              left_inv := by intro x; simp
              right_inv := by intro x; simp }
            have hredτ (x : Qt) : rho (τ x) = rho x := by
              calc
                rho (τ x) = rho (x - δ) := rfl
                _ = rho x - rho δ := rho.map_sub x δ
                _ = rho x := by rw [hrhoδ]; simp
            have hresτ (x : Qt) :
                residue v ((τ x).out : F) = residue v (x.out : F) := by
              calc
                _ = resEq (rho (τ x)) := (hresReduce (τ x)).symm
                _ = resEq (rho x) := by rw [hredτ]
                _ = _ := hresReduce x
            have hquotτ (x : Qt) :
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR It}) (τ x).out =
                  Ideal.Quotient.mk (Ideal.span {R.exterior.genR It})
                    (x.out - deltaR) := by
              calc
                _ = τ x := Ideal.Quotient.mk_out (τ x)
                _ = x - δ := rfl
                _ = _ := by simp [δ]
            have hmemT (x : Qt) :
                (τ x).out - (x.out - deltaR) ∈
                  Ideal.span ({pRTt} : Set S.R) := by
              have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
                (τ x).out (x.out - deltaR)).mp (hquotτ x)
              exact hspanT.symm ▸ hm
            let aLift (x : Qt) : S.R :=
              Classical.choose (Ideal.mem_span_singleton.mp (hmemT x))
            have haLift (x : Qt) :
                (τ x).out - (x.out - deltaR) = pRTt * aLift x :=
              Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemT x))
            have hdelta (x : Qt) :
                ((τ x).out : F) - (x.out : F) =
                  -((deltaR : F)) + (pRTt : F) * (aLift x : F) := by
              have haF := congrArg (fun y : S.R => (y : F)) (haLift x)
              change ((τ x).out : F) - ((x.out : F) - (deltaR : F)) =
                (pRTt : F) * (aLift x : F) at haF
              calc
                _ = (((τ x).out : F) - ((x.out : F) - (deltaR : F))) -
                    (deltaR : F) := by ring
                _ = (pRTt : F) * (aLift x : F) - (deltaR : F) := by rw [haF]
                _ = _ := by ring
            have hpPowShift : (p : F) ^ J * (p : F) ^ r = (p : F) ^ t := by
              calc
                _ = (p : F) ^ (J + r) := by rw [← pow_add]
                _ = _ := by rw [hJr]
            have hscaleDelta :
                (p : F) ^ J * (deltaR : F) / (p : F) ^ (1 + t) =
                  (lambdaR : F) / (p : F) := by
              dsimp [deltaR]
              rw [← hpRr, show 1 + t = t + 1 by omega, pow_succ]
              rw [show (p : F) ^ J * ((p : F) ^ r * (lambdaR : F)) =
                ((p : F) ^ J * (p : F) ^ r) * (lambdaR : F) by ring,
                hpPowShift]
              field_simp [hpne]
            have hscaleError :
                (p : F) ^ J * (pRTt : F) / (p : F) ^ (1 + t) =
                  (p : F) ^ (J - 1) := by
              rw [← hpRTt, show 1 + t = t + 1 by omega]
              have hexp : J + t = (J - 1) + (t + 1) := by omega
              calc
                _ = (p : F) ^ (J + t) / (p : F) ^ (t + 1) := by
                  rw [← pow_add]
                _ = ((p : F) ^ (J - 1) * (p : F) ^ (t + 1)) /
                    (p : F) ^ (t + 1) := by rw [hexp, pow_add]
                _ = _ := by
                  rw [pow_succ]
                  field_simp [hpne]
            have hscaleErrorMul (x : Qt) :
                (p : F) ^ J * (pRTt : F) * (aLift x : F) /
                    (p : F) ^ (1 + t) =
                  (p : F) ^ (J - 1) * (aLift x : F) := by
              calc
                _ = ((p : F) ^ J * (pRTt : F) /
                    (p : F) ^ (1 + t)) * (aLift x : F) := by ring
                _ = _ := by rw [hscaleError]
            have hdeltaPoint (x : Qt) :
                ((τ x).out : F) =
                  (x.out : F) - (deltaR : F) +
                    (pRTt : F) * (aLift x : F) := by
              calc
                _ = (((τ x).out : F) - (x.out : F)) + (x.out : F) := by ring
                _ = (-((deltaR : F)) + (pRTt : F) * (aLift x : F)) +
                    (x.out : F) := by rw [hdelta]
                _ = _ := by ring
            let arg (x : Qt) : F :=
              -((p : F) ^ J * (x.out : F) / (p : F) ^ (1 + t))
            have hargDiff (x : Qt) :
                arg (τ x) - (arg x + (lambdaR : F) / (p : F)) =
                  -((pRJm1 * aLift x : S.R) : F) := by
              calc
                _ = (p : F) ^ J * (deltaR : F) / (p : F) ^ (1 + t) -
                    (p : F) ^ J * (pRTt : F) * (aLift x : F) /
                      (p : F) ^ (1 + t) - (lambdaR : F) / (p : F) := by
                  dsimp [arg]
                  rw [hdeltaPoint x]
                  field_simp [hpne]
                  ring
                _ = (lambdaR : F) / (p : F) -
                    (p : F) ^ (J - 1) * (aLift x : F) -
                      (lambdaR : F) / (p : F) := by
                  rw [hscaleDelta, hscaleErrorMul]
                _ = -((pRJm1 * aLift x : S.R) : F) := by
                  rw [hpRJm1]
                  simp
            have hargVal (x : Qt) :
                HeightOneSpectrum.valuation F v
                  (arg (τ x) - (arg x + (lambdaR : F) / (p : F))) ≤ 1 := by
              rw [hargDiff x]
              exact (-(pRJm1 * aLift x)).property v hv
            have hphaseTrans (x : Qt) :
                A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ x))) =
                  c * A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) := by
              calc
                _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (arg x + (lambdaR : F) / (p : F))) :=
                  euler_addchar_congr_integral A v (arg (τ x))
                    (arg x + (lambdaR : F) / (p : F)) (hargVal x)
                _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg x)) *
                    A.ψ v (algebraMap F (v.adicCompletion F)
                      ((lambdaR : F) / (p : F))) := by
                  rw [← (A.ψ v).map_add_eq_mul]
                  simp
                _ = _ := by rw [hψevalLambda]; dsimp [c]; ring
            let g : Qt → ℂ := fun x =>
              chiPow D v (x.out : F) ((t : ℤ) - 1) *
                A.ψ v (algebraMap F (v.adicCompletion F) (arg x))
            have htrans (x : Qt) : g (τ x) = c * g x := by
              have hchi := euler_chiPow_residue_congr D S v
                (x.out : F) ((τ x).out : F) ((t : ℤ) - 1) (hresτ x).symm
              dsimp [g]
              rw [hchi, hphaseTrans]
              ring
            have hsumShift : (∑ x : Qt, g x) = ∑ x : Qt, g (τ x) := by
              exact Fintype.sum_equiv τ.symm _ _ (by intro x; simp)
            have hsumMul : (∑ x : Qt, g (τ x)) = c * ∑ x : Qt, g x := by
              calc
                _ = ∑ x : Qt, c * g x := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  exact htrans x
                _ = _ := by rw [Finset.mul_sum]
            have hsumEq : (∑ x : Qt, g x) = c * ∑ x : Qt, g x :=
              hsumShift.trans hsumMul
            have hsumZero : (∑ x : Qt, g x) = 0 := by
              have hmul : (1 - c) * (∑ x : Qt, g x) = 0 := by
                calc
                  _ = (∑ x : Qt, g x) - c * ∑ x : Qt, g x := by ring
                  _ = 0 := by rw [← hsumEq]; ring
              have hcnz : 1 - c ≠ 0 := by
                apply sub_ne_zero.mpr
                intro heq
                apply hz
                simpa [c] using heq.symm
              exact (mul_eq_zero.mp hmul).resolve_left hcnz
            have hbaseZero :
                (∑ x : Qt, chiPow D v (x.out : F) ((t : ℤ) - 1) *
                  A.ψ v (algebraMap F (v.adicCompletion F) (arg x))) = 0 := by
              simpa [g] using hsumZero
            rw [hCsum, hsumRearrange, hcollapsed, if_neg hcut1]
            rw [hbaseZero]
            simp
      refine ⟨h0, hC1, ?_, ?_, ?_⟩
      · intro k hk
        have hkpos : 0 < k := by omega
        have hkne : k ≠ 0 := by omega
        let Ik := R.exterior.pow pi k
        let Qk := ResidueRing R.exterior Ik
        letI : Fintype Qk := R.exterior.residueFinite Ik
        let p : Fˣ := primeGen R v
        obtain ⟨_, cK, pRK, hpK, hpKgen⟩ :=
          euler_prime_power_quotient_generator R v hv k
        have hspanK : Ideal.span ({pRK} : Set S.R) =
            Ideal.span {R.exterior.genR Ik} := by
          rw [hpKgen]
          exact Ideal.span_singleton_mul_left_unit cK.isUnit
            (R.exterior.genR Ik)
        obtain ⟨rhoK, hrhoK, hrhoKMk⟩ :=
          euler_primePower_reduction R v hv k hkpos
        have hresReduceK (d : Qk) : resEq (rhoK d) =
            residue v (d.out : F) := by
          have hmk : rhoK d = Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR pi}) d.out := by
            calc
              rhoK d = rhoK (Ideal.Quotient.mk
                  (Ideal.span {R.exterior.genR Ik}) d.out) :=
                congrArg rhoK (Ideal.Quotient.mk_out d).symm
              _ = Ideal.Quotient.mk (Ideal.span {R.exterior.genR pi}) d.out :=
                hrhoKMk d.out
          rw [hmk]
          exact hresEqMk d.out
        obtain ⟨_, cKm1, pRKm1, hpRKm1, _⟩ :=
          euler_prime_power_quotient_generator R v hv (k - 1)
        obtain ⟨_, cTm1, pRTm1, hpRTm1, _⟩ :=
          euler_prime_power_quotient_generator R v hv (t - 1)
        have hpCross : (pRT : F) * (pRKm1 : F) =
            (pRK : F) * (pRTm1 : F) := by
          calc
            _ = (p : F) ^ t * (p : F) ^ (k - 1) := by
              rw [hpT, hpRKm1]
            _ = (p : F) ^ (t + (k - 1)) := by rw [← pow_add]
            _ = (p : F) ^ (k + (t - 1)) := by congr 1 <;> omega
            _ = (p : F) ^ k * (p : F) ^ (t - 1) := by rw [pow_add]
            _ = _ := by rw [← hpK, ← hpRTm1]
        let supports : Qk → Prop := fun d =>
          ∃ y : S.R, (p : F) ^ J - (p : F) ^ t * (d.out : F) =
            (p : F) ^ k * (y : F)
        have hsupportMem (d : Qk) : supports d ↔
            pRJ - pRT * d.out ∈ Ideal.span ({pRK} : Set S.R) := by
          have hdiv := euler_power_divisibility_iff p k pRK hpK
            (pRJ - pRT * d.out)
          constructor
          · rintro ⟨y, hy⟩
            apply hdiv.mp
            refine ⟨y, ?_⟩
            change (pRJ : F) - (pRT : F) * (d.out : F) =
              (p : F) ^ k * (y : F)
            calc
              _ = (p : F) ^ J - (p : F) ^ t * (d.out : F) := by
                rw [hpJ, hpT]
              _ = _ := hy
          · intro hmem
            rcases hdiv.mpr hmem with ⟨y, hy⟩
            refine ⟨y, ?_⟩
            calc
              (p : F) ^ J - (p : F) ^ t * (d.out : F) =
                  (pRJ : F) - (pRT : F) * (d.out : F) := by
                rw [hpJ, hpT]
              _ = (p : F) ^ k * (y : F) := hy
        have hsupportQuot (d : Qk) : supports d ↔
            Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik}) pRJ =
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                (pRT * d.out) := by
          calc
            _ ↔ pRJ - pRT * d.out ∈ Ideal.span {pRK} := hsupportMem d
            _ ↔ pRJ - pRT * d.out ∈
                Ideal.span {R.exterior.genR Ik} := by rw [hspanK]
            _ ↔ _ :=
              (Ideal.Quotient.mk_eq_mk_iff_sub_mem pRJ (pRT * d.out)).symm
        let arg (d : Qk) (x : Qt) : F :=
          -(((p : F) ^ J - (p : F) ^ t * (d.out : F)) *
            (x.out : F) / (p : F) ^ (k + t))
        have hCsum : localC R v hv t k J =
            ∑ x : Qt, chiPow D v (x.out : F) t *
              ∑ d : Qk, (if supports d then
                  chiPow D v (d.out : F) k *
                  A.ψ v (algebraMap F (v.adicCompletion F) (arg d x))
                else 0) := by
          unfold localC
          simp_rw [finsum_eq_sum_of_fintype]
          simp only [if_neg hkne, if_neg (Nat.ne_of_gt ht)]
          calc
            _ = ∑ d : Qk, ∑ x : Qt,
                (if supports d then chiPow D v (d.out : F) k *
                  (chiPow D v (x.out : F) t *
                    A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)))
                 else 0) := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hs : supports d
              · have hsRaw : ∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F) := by
                  change ∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)
                  exact hs
                conv_lhs => rw [if_pos hsRaw]
                conv_rhs => simp only [if_pos hs]
                rw [Finset.mul_sum]
              · have hsRaw : ¬ (∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)) := by
                  change ¬ (∃ y : S.R, (p : F) ^ J -
                    (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F))
                  exact hs
                conv_lhs => rw [if_neg hsRaw]
                conv_rhs => simp only [if_neg hs]
                simp
            _ = ∑ x : Qt, ∑ d : Qk,
                (if supports d then chiPow D v (d.out : F) k *
                  (chiPow D v (x.out : F) t *
                    A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)))
                 else 0) := Finset.sum_comm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                _ = ∑ d : Qk, chiPow D v (x.out : F) t *
                    (if supports d then chiPow D v (d.out : F) k *
                      A.ψ v (algebraMap F (v.adicCompletion F) (arg d x))
                     else 0) := by
                  apply Finset.sum_congr rfl
                  intro d hd
                  by_cases hs : supports d
                  · have hsRaw : ∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F) := by
                      change ∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)
                      exact hs
                    conv_lhs => rw [if_pos hs]
                    conv_rhs => simp only [if_pos hs]
                    ring
                  · have hsRaw : ¬ (∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F)) := by
                      change ¬ (∃ y : S.R, (p : F) ^ J -
                        (p : F) ^ t * (d.out : F) = (p : F) ^ k * (y : F))
                      exact hs
                    conv_lhs => rw [if_neg hs]
                    conv_rhs => simp only [if_neg hs]
                    simp
                _ = _ := by rw [Finset.mul_sum]
        have hpGen : S.IsGen (p : F) v.asIdeal := by
          have h := (bc.gen_spec pi).1
          simpa [p, pi, primeGen, hv, R.exterior.prime_val] using h
        obtain ⟨_, _, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hpGen
        obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
        let liftResidue : (𝓞 F ⧸ v.asIdeal) → S.R := fun a =>
          ⟨algebraMap (𝓞 F) F a.out, fun w hw => w.valuation_le_one a.out⟩
        have hresLift (a : 𝓞 F ⧸ v.asIdeal) :
            residue v ((liftResidue a : S.R) : F) = a := by
          change residue v (algebraMap (𝓞 F) F a.out) = a
          calc
            _ = Ideal.Quotient.mk v.asIdeal a.out :=
              (a2_bridge_SYMBOL D S).residue_algebraMap v a.out
            _ = a := Ideal.Quotient.mk_out a
        have hresZero : residue v (0 : F) = 0 := by
          simpa using (a2_bridge_SYMBOL D S).residue_algebraMap v (0 : 𝓞 F)
        have hresEqZero : resEq (0 : Q1) = 0 := by
          have hmk0 : Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR pi}) (0 : S.R) = (0 : Q1) := by simp
          rw [← hmk0]
          exact (hresEqMk 0).trans hresZero
        have hresRhoDelta (deltaR : S.R)
            (hdelta : residue v (deltaR : F) = 0) :
            rhoK (Ideal.Quotient.mk
              (Ideal.span {R.exterior.genR Ik}) deltaR) = 0 := by
          apply hresEqBij.1
          calc
            resEq (rhoK (Ideal.Quotient.mk
                (Ideal.span {R.exterior.genR Ik}) deltaR)) =
                residue v (deltaR : F) := by
              rw [hrhoKMk, hresEqMk]
            _ = 0 := hdelta
            _ = resEq 0 := hresEqZero.symm
        have hresPkm1 : residue v (pRKm1 : F) = 0 := by
          rw [← hpRKm1, hresPowZero (k - 1) (by omega)]
        have hcoeffDelta :
            (p : F) ^ t * (pRKm1 : F) / (p : F) ^ (k + t) =
              1 / (p : F) := by
          rw [← hpRKm1]
          have hexp : k + t = t + (k - 1) + 1 := by omega
          calc
            _ = (p : F) ^ (t + (k - 1)) / (p : F) ^ (k + t) := by
              rw [← pow_add]
            _ = (p : F) ^ (t + (k - 1)) /
                (p : F) ^ (t + (k - 1) + 1) := by rw [hexp]
            _ = _ := by
              rw [pow_succ]
              field_simp [Units.ne_zero p]
        have hcoeffError :
            (p : F) ^ t * (pRK : F) / (p : F) ^ (k + t) = 1 := by
          rw [← hpK]
          calc
            _ = (p : F) ^ (t + k) / (p : F) ^ (k + t) := by
              rw [← pow_add]
            _ = _ := by rw [Nat.add_comm t k]; field_simp [Units.ne_zero p]
        let supportsD : Qk → Prop := supports
        have hDsumZero (x : Qt)
            (hxmask : chiPow D v (x.out : F) t ≠ 0) :
            (∑ d : Qk, (if supportsD d then chiPow D v (d.out : F) k *
              A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) else 0)) = 0 := by
          let a : 𝓞 F ⧸ v.asIdeal := resEq (rho x)
          have hresx : residue v (x.out : F) = a := (hresReduce x).symm
          have hresxNe : residue v (x.out : F) ≠ 0 := by
            intro hzero
            have hzpow := SB.chiPow_zero v (x.out : F) (t : ℤ) hzero
            rw [hzpow] at hxmask
            exact hxmask rfl
          have ha : a ≠ 0 := by rw [← hresx]; exact hresxNe
          have hψshiftNe : ψ.mulShift a ≠ 1 := hψprim ha
          have hψwitness : ∃ b : 𝓞 F ⧸ v.asIdeal, ψ.mulShift a b ≠ 1 := by
            by_contra h
            push_neg at h
            apply hψshiftNe
            ext b
            exact h b
          obtain ⟨b, hb⟩ := hψwitness
          let c : ℂ := ψ.mulShift a b
          have hcne : c ≠ 1 := hb
          have hcval : c = ψ (b * a) := by
            change ψ (a * b) = ψ (b * a)
            exact congrArg ψ (mul_comm a b)
          let lambdaR : S.R := liftResidue b
          let prodLift : S.R := liftResidue b * liftResidue a
          let prodR : S.R := liftResidue b * x.out
          have hresProdR : residue v (prodR : F) = b * a := by
            change residue v ((liftResidue b : S.R) * x.out : F) = b * a
            rw [SB.residue_mul v (liftResidue b : F) (x.out : F)
              ((liftResidue b).property v hv) (x.out.property v hv),
              hresLift, hresx]
          have hresProdLift : residue v (prodLift : F) = b * a := by
            change residue v ((liftResidue b : S.R) *
              (liftResidue a : S.R) : F) = b * a
            rw [SB.residue_mul v (liftResidue b : F) (liftResidue a : F)
              ((liftResidue b).property v hv) ((liftResidue a).property v hv),
              hresLift, hresLift]
          have hψevalProd : ψ (b * a) =
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((prodLift : F) / (p : F))) := by
            have hprodLift : (prodLift : F) =
                (liftResidue b : F) * (liftResidue a : F) := by
              rfl
            calc
              ψ (b * a) = ψ (a * b) := by congr 1 <;> exact (mul_comm b a)
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    (((liftResidue b : F) * (liftResidue a : F)) / (p : F))) :=
                hψeval a b
              _ = _ := by rw [← hprodLift]
          have hphaseValue :
              A.ψ v (algebraMap F (v.adicCompletion F)
                ((prodR : F) / (p : F))) = c := by
            have hresProd : residue v (prodR : F) = residue v (prodLift : F) :=
              hresProdR.trans hresProdLift.symm
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                    ((prodLift : F) / (p : F))) :=
                euler_addchar_div_residue_congr D A v hv p hpVal
                  prodR prodLift hresProd
              _ = ψ (b * a) := hψevalProd.symm
              _ = c := hcval.symm
          let deltaR : S.R := pRKm1 * lambdaR
          have hresDelta : residue v (deltaR : F) = 0 := by
            change residue v ((pRKm1 : F) * (lambdaR : F)) = 0
            rw [SB.residue_mul v (pRKm1 : F) (lambdaR : F)
              (pRKm1.property v hv) (lambdaR.property v hv), hresPkm1]
            simp
          let δ : Qk := Ideal.Quotient.mk
            (Ideal.span {R.exterior.genR Ik}) deltaR
          have hrhoδ : rhoK δ = 0 := hresRhoDelta deltaR hresDelta
          let τ : Qk ≃ Qk := {
            toFun := fun d => d + δ
            invFun := fun d => d - δ
            left_inv := by intro d; simp
            right_inv := by intro d; simp }
          have hresτ (d : Qk) :
              residue v ((τ d).out : F) = residue v (d.out : F) := by
            have hredτ : rhoK (τ d) = rhoK d := by
              calc
                rhoK (τ d) = rhoK (d + δ) := rfl
                _ = rhoK d + rhoK δ := rhoK.map_add d δ
                _ = rhoK d := by rw [hrhoδ]; simp
            calc
              _ = resEq (rhoK (τ d)) := (hresReduceK (τ d)).symm
              _ = resEq (rhoK d) := by rw [hredτ]
              _ = _ := hresReduceK d
          have hquotτ (d : Qk) :
              Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik}) (τ d).out =
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                  (d.out + deltaR) := by
            calc
              _ = τ d := Ideal.Quotient.mk_out (τ d)
              _ = d + δ := rfl
              _ = _ := by simp [δ]
          have hmemK (d : Qk) :
              (τ d).out - (d.out + deltaR) ∈
                Ideal.span ({pRK} : Set S.R) := by
            have hm := (Ideal.Quotient.mk_eq_mk_iff_sub_mem
              (τ d).out (d.out + deltaR)).mp (hquotτ d)
            exact hspanK.symm ▸ hm
          let aLift (d : Qk) : S.R :=
            Classical.choose (Ideal.mem_span_singleton.mp (hmemK d))
          have haLift (d : Qk) :
              (τ d).out - (d.out + deltaR) = pRK * aLift d :=
            Classical.choose_spec (Ideal.mem_span_singleton.mp (hmemK d))
          have hdelta (d : Qk) :
              (τ d).out - d.out = deltaR + pRK * aLift d := by
            calc
              _ = ((τ d).out - (d.out + deltaR)) + deltaR := by ring
              _ = pRK * aLift d + deltaR := by rw [haLift]
              _ = _ := by ring
          have hmulDiff (d : Qk) :
              pRT * (τ d).out - pRT * d.out ∈
                Ideal.span ({pRK} : Set S.R) := by
            apply Ideal.mem_span_singleton.mpr
            refine ⟨pRTm1 * lambdaR + pRT * aLift d, ?_⟩
            apply Subtype.ext
            calc
              ((pRT * (τ d).out - pRT * d.out : S.R) : F) =
                  (pRT : F) * (((τ d).out : F) - (d.out : F)) := by
                simp only [Subalgebra.coe_sub, Subalgebra.coe_mul]
                ring
              _ = (pRT : F) *
                    ((deltaR : F) + (pRK : F) * (aLift d : F)) := by
                have hdeltaF := congrArg (fun y : S.R => (y : F)) (hdelta d)
                change ((τ d).out : F) - (d.out : F) =
                  (deltaR : F) + (pRK : F) * (aLift d : F) at hdeltaF
                rw [hdeltaF]
              _ = (pRK : F) *
                    ((pRTm1 : F) * (lambdaR : F) +
                      (pRT : F) * (aLift d : F)) := by
                dsimp [deltaR]
                calc
                  _ = ((pRT : F) * (pRKm1 : F)) * (lambdaR : F) +
                      ((pRT : F) * (pRK : F)) * (aLift d : F) := by ring
                  _ = ((pRK : F) * (pRTm1 : F)) * (lambdaR : F) +
                      ((pRT : F) * (pRK : F)) * (aLift d : F) := by rw [hpCross]
                  _ = _ := by ring
          have hsupportτ (d : Qk) : supports (τ d) ↔ supports d := by
            have hmkMul :
                Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                    (pRT * (τ d).out) =
                  Ideal.Quotient.mk (Ideal.span {R.exterior.genR Ik})
                    (pRT * d.out) := by
              apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
              have hmemMul : pRT * (τ d).out - pRT * d.out ∈
                  Ideal.span {R.exterior.genR Ik} := by
                simpa only [hspanK] using hmulDiff d
              exact hmemMul
            rw [hsupportQuot (τ d), hsupportQuot d]
            constructor
            · intro h
              exact h.trans hmkMul
            · intro h
              exact h.trans hmkMul.symm
          let f : Qk → ℂ := fun d =>
            if supportsD d then chiPow D v (d.out : F) k *
              A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) else 0
          have hphaseTrans (d : Qk) :
              A.ψ v (algebraMap F (v.adicCompletion F) (arg (τ d) x)) =
                c * A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) := by
            have hpne : (p : F) ≠ 0 := Units.ne_zero p
            have hcoeffDelta :
                (p : F) ^ t * (pRKm1 : F) / (p : F) ^ (k + t) =
                  1 / (p : F) := by
              rw [← hpRKm1]
              have hexp : k + t = t + (k - 1) + 1 := by omega
              calc
                _ = (p : F) ^ (t + (k - 1)) / (p : F) ^ (k + t) := by
                  rw [← pow_add]
                _ = (p : F) ^ (t + (k - 1)) /
                    (p : F) ^ (t + (k - 1) + 1) := by rw [hexp]
                _ = _ := by rw [pow_succ]; field_simp [hpne]
            have hcoeffError :
                (p : F) ^ t * (pRK : F) / (p : F) ^ (k + t) = 1 := by
              rw [← hpK]
              calc
                _ = (p : F) ^ (t + k) / (p : F) ^ (k + t) := by
                  rw [← pow_add]
                _ = _ := by rw [Nat.add_comm t k]; field_simp [hpne]
            have hscaleDelta :
                (p : F) ^ t * (deltaR : F) / (p : F) ^ (k + t) =
                  (lambdaR : F) / (p : F) := by
              dsimp [deltaR]
              calc
                _ = ((p : F) ^ t * (pRKm1 : F) /
                    (p : F) ^ (k + t)) * (lambdaR : F) := by ring
                _ = _ := by rw [hcoeffDelta]; ring
            have hargDiff (d : Qk) :
                arg (τ d) x - (arg d x +
                    (prodR : F) / (p : F)) =
                  ((aLift d * x.out : S.R) : F) := by
              calc
                _ = (((p : F) ^ t * (deltaR : F) /
                      (p : F) ^ (k + t)) * (x.out : F)) +
                    (((p : F) ^ t * (pRK : F) /
                      (p : F) ^ (k + t)) * (aLift d : F) * (x.out : F)) -
                    (prodR : F) / (p : F) := by
                  dsimp [arg]
                  have hrep : (τ d).out = d.out + deltaR + pRK * aLift d := by
                    calc
                      _ = ((τ d).out - d.out) + d.out := by ring
                      _ = deltaR + pRK * aLift d + d.out := by rw [hdelta]
                      _ = _ := by ring
                  rw [hrep]
                  dsimp [prodR]
                  field_simp [hpne]
                  ring
                _ = ((aLift d * x.out : S.R) : F) := by
                  rw [hscaleDelta, hcoeffError]
                  dsimp [prodR]
                  ring
            have hargVal (d : Qk) :
                HeightOneSpectrum.valuation F v
                  (arg (τ d) x - (arg d x + (prodR : F) / (p : F))) ≤ 1 := by
              rw [hargDiff d]
              exact (aLift d * x.out).property v hv
            calc
              _ = A.ψ v (algebraMap F (v.adicCompletion F)
                  (arg d x + (prodR : F) / (p : F))) :=
                euler_addchar_congr_integral A v (arg (τ d) x)
                  (arg d x + (prodR : F) / (p : F)) (hargVal d)
              _ = A.ψ v (algebraMap F (v.adicCompletion F) (arg d x)) *
                  A.ψ v (algebraMap F (v.adicCompletion F)
                    ((prodR : F) / (p : F))) := by
                rw [← (A.ψ v).map_add_eq_mul]
                simp
              _ = _ := by rw [hphaseValue]; ring
          have htrans (d : Qk) : f (τ d) = c * f d := by
            by_cases hs : supportsD d
            · have hsτ : supportsD (τ d) := (hsupportτ d).2 hs
              have hchi := euler_chiPow_residue_congr D S v
                ((τ d).out : F) (d.out : F) k (hresτ d)
              simp only [f, if_pos hsτ, if_pos hs]
              rw [hchi, hphaseTrans]
              ring
            · have hsτ : ¬ supportsD (τ d) := by
                intro h
                exact hs ((hsupportτ d).1 h)
              simp [f, hs, hsτ]
          have hsumShift : (∑ d : Qk, f d) = ∑ d : Qk, f (τ d) := by
            exact Fintype.sum_equiv τ.symm _ _ (by intro d; simp)
          have hsumMul : (∑ d : Qk, f (τ d)) = c * ∑ d : Qk, f d := by
            calc
              _ = ∑ d : Qk, c * f d := by
                apply Finset.sum_congr rfl
                intro d hd
                exact htrans d
              _ = _ := by rw [Finset.mul_sum]
          have hsumEq : (∑ d : Qk, f d) = c * ∑ d : Qk, f d :=
            hsumShift.trans hsumMul
          have hsumZero : (∑ d : Qk, f d) = 0 := by
            have hmul : (1 - c) * (∑ d : Qk, f d) = 0 := by
              calc
                _ = (∑ d : Qk, f d) - c * ∑ d : Qk, f d := by ring
                _ = 0 := by rw [← hsumEq]; ring
            have hcnz : 1 - c ≠ 0 := by
              intro heq
              exact hcne (sub_eq_zero.mp heq).symm
            exact (mul_eq_zero.mp hmul).resolve_left hcnz
          exact hsumZero
        have hresSum : localC R v hv t k J = 0 := by
          rw [hCsum]
          apply Finset.sum_eq_zero
          intro x hx
          by_cases hχx : chiPow D v (x.out : F) t = 0
          · simp [hχx]
          · rw [hDsumZero x hχx]
            simp
        exact hresSum
      · by_cases hcut : t - 1 ≤ J
        · let m : ℕ := J + 1 - t
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hT := euler_localT_norm_le R v hv (t : ℤ) pRm
          have hT' : ‖localT R v t ((primeGen R v : F) ^ m)‖ ≤
              qI v.asIdeal := by
            simpa [hpm] using hT
          have hqnonneg : 0 ≤ qI v.asIdeal := by simp [qI]
          have hpowNorm :
              ‖(qI v.asIdeal : ℂ) ^ (t - 1)‖ = qI v.asIdeal ^ (t - 1) := by
            rw [norm_pow]
            simp [qI, Real.norm_eq_abs, abs_of_nonneg hqnonneg]
          rw [h0, if_pos hcut]
          calc
            ‖(qI v.asIdeal : ℂ) ^ (t - 1) *
                localT R v t ((primeGen R v : F) ^ (J + 1 - t))‖ =
                qI v.asIdeal ^ (t - 1) *
                  ‖localT R v t ((primeGen R v : F) ^ (J + 1 - t))‖ := by
              rw [norm_mul, hpowNorm]
            _ ≤ qI v.asIdeal ^ (t - 1) * qI v.asIdeal :=
              mul_le_mul_of_nonneg_left hT'
                (pow_nonneg hqnonneg (t - 1))
            _ = qI v.asIdeal ^ t := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega)]
            _ = qI v.asIdeal ^ (t : ℝ) := by
              rw [Real.rpow_natCast]
        · rw [h0, if_neg hcut]
          simpa only [norm_zero] using
            (Real.rpow_nonneg (show 0 ≤ qI v.asIdeal by simp [qI]) (t : ℝ))
      · by_cases hcut : t ≤ J
        · rw [hC1, if_pos hcut]
          let m : ℕ := J - t
          obtain ⟨_, _, pRm, hpm, _⟩ :=
            euler_prime_power_quotient_generator R v hv m
          have hT2 :
              ‖localT R v ((t : ℤ) - 1)
                ((primeGen R v : F) ^ (J - t))‖ ≤ qI v.asIdeal := by
            have h := euler_localT_norm_le R v hv ((t : ℤ) - 1) pRm
            simpa [m, hpm] using h
          have hT1 : ‖localT R v 1 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ) := by
            exact (po_C_local_T_values R v hv (1 : ℤ) (1 : S.R)).2.1
              (by norm_num)
          have hqnonneg : 0 ≤ qI v.asIdeal := by simp [qI]
          have hqpos : 0 < qI v.asIdeal := by
            have hqone : 1 < qI v.asIdeal := by
              have hn : 1 < Ideal.absNorm v.asIdeal :=
                HeightOneSpectrum.one_lt_absNorm v
              have hr : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
                exact_mod_cast hn
              simpa [qI] using hr
            linarith
          have hpowNorm :
              ‖(qI v.asIdeal : ℂ) ^ (t - 1)‖ = qI v.asIdeal ^ (t - 1) := by
            rw [norm_pow]
            simp [qI, Real.norm_eq_abs, abs_of_nonneg hqnonneg]
          have hpowComb :
              qI v.asIdeal ^ (1 / 2 : ℝ) *
                qI v.asIdeal ^ (t - 1) * qI v.asIdeal =
                  qI v.asIdeal ^ ((t : ℝ) + 1 / 2) := by
            calc
              _ = qI v.asIdeal ^ (1 / 2 : ℝ) *
                  qI v.asIdeal ^ ((t - 1 : ℕ) : ℝ) *
                  qI v.asIdeal ^ (1 : ℝ) := by simp [Real.rpow_natCast]
              _ = qI v.asIdeal ^ ((1 / 2 : ℝ) +
                  ((t - 1 : ℕ) : ℝ) + 1) := by
                rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
              _ = _ := by
                congr 1
                have ht : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
                  norm_cast
                  omega
                calc
                  _ = ((t - 1 : ℕ) : ℝ) + 1 + (1 / 2 : ℝ) := by ring
                  _ = (t : ℝ) + 1 / 2 := by rw [ht]
          calc
            _ = ‖localT R v 1 1‖ * qI v.asIdeal ^ (t - 1) *
                ‖localT R v ((t : ℤ) - 1)
                  ((primeGen R v : F) ^ (J - t))‖ := by
              simp only [norm_mul, hpowNorm]
            _ ≤ qI v.asIdeal ^ (1 / 2 : ℝ) *
                qI v.asIdeal ^ (t - 1) * qI v.asIdeal := by
              rw [hT1]
              exact mul_le_mul_of_nonneg_left hT2
                (mul_nonneg (Real.rpow_nonneg hqnonneg _)
                  (pow_nonneg hqnonneg _))
            _ = qI v.asIdeal ^ ((t : ℝ) + 1 / 2) := hpowComb
        · rw [hC1, if_neg hcut]
          simpa only [norm_zero] using
            (Real.rpow_nonneg (show 0 ≤ qI v.asIdeal by simp [qI])
              ((t : ℝ) + 1 / 2))

/-- po:euler-local-factorization, 05:444-550. Cross-prime exponents cancel modulo six. -/
theorem cross_prime_exponent_cancel (e e' l l' : ℕ) :
    6 ∣ 2 * (e + 3 * l) * (e' + 3 * l') + 4 * e * e' := by
  refine ⟨e * e' + e * l' + l * e' + 3 * l * l', ?_⟩
  ring

/-- po:euler-local-factorization, 05:444–550. Product convergence uses HasProd, never finprod. -/
/- The local gamma estimate is the triangle bound after the normalized Gauss-sum definition. -/
private theorem euler_gamma_prime_norm_le (v : FinPlace F) (hv : v ∉ S.Sf) :
    ‖gamma D S A 2 v.asIdeal (primeGen R v : F)‖ ≤ qI v.asIdeal ^ (1 / 2 : ℝ) := by
  classical
  let I := R.exterior.prime v hv
  let a : Fˣ := primeGen R v
  have hgen : S.IsGen (a : F) I.1 := by
    have h := (bc.gen_spec I).1
    simpa [a, I, primeGen, hv, R.exterior.prime_val] using h
  have hIne : I.1 ≠ ⊥ := by
    simpa only [Ideal.zero_eq_bot] using I.2.1
  have hqNat : 0 < Ideal.absNorm I.1 :=
    Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩
  let Q := 𝓞 F ⧸ I.1
  letI : Finite Q := (Ideal.absNorm_ne_zero_iff I.1).mp hqNat.ne'
  letI : Fintype Q := Fintype.ofFinite _
  have hcard : Fintype.card Q = Ideal.absNorm I.1 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let g : Q → ℂ := fun x =>
    chiIdealPow D I.1 (algebraMap (𝓞 F) F x.out) 2 *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / (a : F)))
  have hg (x : Q) : ‖g x‖ ≤ 1 := by
    dsimp [g]
    have hχ := po_chiIdealPow_norm_le_one D I.1
      (algebraMap (𝓞 F) F x.out) 2
    let xR : S.R := ⟨algebraMap (𝓞 F) F x.out, fun w hw => w.valuation_le_one x.out⟩
    have he := po_e_residue_norm_one I a hgen xR R
    have he' : ‖S.e A (S.diag (algebraMap (𝓞 F) F x.out / (a : F)))‖ = 1 := by
      simpa [xR] using he
    calc
      _ ≤ ‖chiIdealPow D I.1 (algebraMap (𝓞 F) F x.out) 2‖ *
          ‖S.e A (S.diag (algebraMap (𝓞 F) F x.out / (a : F)))‖ := norm_mul_le _ _
      _ ≤ 1 := by rw [he']; simpa using hχ
  have hsum : ‖∑ᶠ x : Q, g x‖ ≤ qI I.1 := by
    calc
      _ = ‖∑ x : Q, g x‖ := by rw [finsum_eq_sum_of_fintype]
      _ ≤ ∑ x : Q, ‖g x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Q, (1 : ℝ) := Finset.sum_le_sum fun x _ => hg x
      _ = (Fintype.card Q : ℝ) := by simp
      _ = qI I.1 := by rw [hcard]; simp [qI]
  have hqpos : 0 < qI I.1 := by
    dsimp [qI]
    exact_mod_cast hqNat
  have hqReal : 0 < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hqNat
  have hscale : 0 ≤ (Ideal.absNorm I.1 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsum' : ‖∑ᶠ x : Q, g x‖ ≤ (Ideal.absNorm I.1 : ℝ) := by
    simpa [qI] using hsum
  have hnormGamma' : ‖gamma D S A 2 I.1 (a : F)‖ ≤
      (Ideal.absNorm I.1 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [gamma, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscale]
    calc
      (Ideal.absNorm I.1 : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖∑ᶠ x : 𝓞 F ⧸ I.1,
            chiIdealPow D I.1 (algebraMap (𝓞 F) F x.out) 2 *
              S.e A (S.diag (algebraMap (𝓞 F) F x.out / (a : F)))‖ ≤
        (Ideal.absNorm I.1 : ℝ) ^ (-(1 / 2 : ℝ)) *
            (Ideal.absNorm I.1 : ℝ) :=
          mul_le_mul_of_nonneg_left hsum' (Real.rpow_nonneg hqReal.le _)
      _ = (Ideal.absNorm I.1 : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          _ = (Ideal.absNorm I.1 : ℝ) ^ (-(1 / 2 : ℝ)) *
              (Ideal.absNorm I.1 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (Ideal.absNorm I.1 : ℝ) ^ (-(1 / 2 : ℝ) + 1) :=
            (Real.rpow_add hqReal _ _).symm
          _ = _ := by congr 1 <;> ring
  have hnormGamma : ‖gamma D S A 2 I.1 (a : F)‖ ≤ qI I.1 ^ (1 / 2 : ℝ) := by
    simpa [qI] using hnormGamma'
  simpa [I, a, primeGen, hv, R.exterior.prime_val] using hnormGamma

private theorem euler_hecke_prime_norm_le
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (v : FinPlace F) :
    ‖ϑ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with h
  · have hunit := ReflectionSetup.vartheta_unitary R0
      (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) )
    exact le_of_eq (by simpa [HeckeChar.loc] using hunit)
  · simp

private theorem euler_chi_zpow_norm_le_one (v : FinPlace F) (x : F) (n : ℤ) :
    ‖chi D v x ^ n‖ ≤ 1 := by
  by_cases hx : residue v x = 0
  · cases n with
    | ofNat k => by_cases hk : k = 0 <;> simp [chi, hx, hk]
    | negSucc k => simp [chi, hx]
  · simpa [norm_zpow, po_chi_norm_one D v x hx]

private theorem euler_localC_norm_le (v : FinPlace F) (hv : v ∉ S.Sf)
    (t k J : ℕ) :
    ‖localC R v hv t k J‖ ≤ qI v.asIdeal ^ ((t + k : ℕ) : ℝ) := by
  have hq : 1 < qI v.asIdeal := qI_prime_gt_one v
  by_cases ht : t = 0
  · subst t
    by_cases hk : k = 0
    · subst k
      rw [(po_C_local_values R v hv J).1]
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hC := (po_C_local_values R v hv J).2.1 k hkpos
      rw [hC]
      by_cases hJ : J = 0
      · have hpow : (1 : ℝ) ≤ qI v.asIdeal ^ k :=
          one_le_pow₀ hq.le
        simpa [hJ, Real.rpow_natCast] using hpow
      · have hnonneg : 0 ≤ qI v.asIdeal ^ k :=
          pow_nonneg (by positivity) k
        simpa [hJ, Real.rpow_natCast] using hnonneg
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have hCT := (po_C_local_values R v hv J).2.2 t htpos
    by_cases hk0 : k = 0
    · subst k
      simpa [Real.rpow_natCast] using hCT.2.2.2.1
    · by_cases hk1 : k = 1
      · subst k
        have hexp : (t : ℝ) + 1 / 2 ≤ ((t + 1 : ℕ) : ℝ) := by
          have htCast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by norm_cast
          rw [htCast]
          linarith
        have hpow := Real.rpow_le_rpow_of_exponent_le hq.le hexp
        exact (hCT.2.2.2.2).trans (by simpa [Real.rpow_natCast] using hpow)
      · have hkge : 2 ≤ k := by omega
        rw [hCT.2.2.1 k hkge]
        simp only [norm_zero]
        exact Real.rpow_nonneg (by positivity) _

private theorem euler_localEulerTerm_norm_le (u : U.U) (v : FinPlace F)
    (hv : v ∉ S.Sf) (ξ w z : ℂ) (hreg : initialRegion ξ w z)
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
      qI v.asIdeal ^ (-((i.2.1 + i.2.2.1 + i.2.2.2 : ℕ) : ℝ)) := by
  classical
  let e : ℕ := i.1.1
  let l : ℕ := i.2.1
  let k : ℕ := i.2.2.1
  let m : ℕ := i.2.2.2
  let j : ℕ := frequencyValuation η U u v
  let t : ℕ := e + 3 * l
  let E : ℂ := -(e : ℂ) * (1 / 2 + ξ) - (l : ℂ) * (1 + 3 * ξ) -
    (k : ℂ) * w - 6 * (m : ℂ) * z
  change ‖gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e *
      ϑ.primeValue v ^ (e + 3 * l) *
      chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^
        ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
      localC R v hv (e + 3 * l) k (j + 6 * m) *
      (qI v.asIdeal : ℂ) ^ E‖ ≤
    qI v.asIdeal ^ (-((l + k + m : ℕ) : ℝ))
  rcases hreg with ⟨hξ, hw, hz⟩
  have hq : 1 < qI v.asIdeal := qI_prime_gt_one v
  have hqpos : 0 < qI v.asIdeal := lt_trans zero_lt_one hq
  have helt : e < 2 := by dsimp [e]; exact i.1.2
  have hgamma :
      ‖gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e‖ ≤
        qI v.asIdeal ^ ((e : ℝ) / 2) := by
    have hecases : e = 0 ∨ e = 1 := by omega
    rcases hecases with he0 | he1
    · simp [he0]
    · simpa [he1] using euler_gamma_prime_norm_le R v hv
  have htheta : ‖ϑ.primeValue v ^ (e + 3 * l)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (euler_hecke_prime_norm_le R v)
  have hchi := euler_chi_zpow_norm_le_one (D := D) v
    ((U.repr u : F) / (primeGen R v : F) ^ j)
    ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ))
  have hC := euler_localC_norm_le R v hv (e + 3 * l) k (j + 6 * m)
  have hpow : ‖(qI v.asIdeal : ℂ) ^ E‖ = qI v.asIdeal ^ E.re :=
    Complex.norm_cpow_eq_rpow_re_of_pos hqpos E
  have hEre : E.re =
      -(e : ℝ) * (1 / 2 + ξ.re) - (l : ℝ) * (1 + 3 * ξ.re) -
        (k : ℝ) * w.re - 6 * (m : ℝ) * z.re := by
    simp [E, Complex.mul_re] <;> ring
  have htotal :
      (e : ℝ) / 2 + ((e + 3 * l + k : ℕ) : ℝ) + E.re =
        (e : ℝ) * (1 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
          (k : ℝ) * (1 - w.re) - 6 * (m : ℝ) * z.re := by
    rw [hEre]
    push_cast
    ring
  have hsumCast : ((l + k + m : ℕ) : ℝ) = (l : ℝ) + (k : ℝ) + (m : ℝ) := by
    norm_cast
  have hePart : (e : ℝ) * (1 - ξ.re) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg e) (by linarith)
  have hlPart : (l : ℝ) * (2 - 3 * ξ.re) ≤ -(l : ℝ) := by
    have hc : 2 - 3 * ξ.re ≤ -1 := by linarith
    simpa using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg l)
  have hkPart : (k : ℝ) * (1 - w.re) ≤ -(k : ℝ) := by
    have hc : 1 - w.re ≤ -1 := by linarith
    simpa using mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg k)
  have hmPart : -6 * (m : ℝ) * z.re ≤ -(m : ℝ) := by
    have hc : -6 * z.re ≤ -1 := by linarith
    calc
      -6 * (m : ℝ) * z.re = (m : ℝ) * (-6 * z.re) := by ring
      _ ≤ (m : ℝ) * (-1) := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg m)
      _ = -(m : ℝ) := by ring
  have htotalLe :
      (e : ℝ) * (1 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
          (k : ℝ) * (1 - w.re) - 6 * (m : ℝ) * z.re ≤
        -((l + k + m : ℕ) : ℝ) := by
    rw [hsumCast]
    linarith
  calc
    _ = ‖gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e‖ *
        ‖ϑ.primeValue v ^ (e + 3 * l)‖ *
        ‖chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^
          ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ))‖ *
        ‖localC R v hv (e + 3 * l) k (j + 6 * m)‖ *
        ‖(qI v.asIdeal : ℂ) ^ E‖ := by simp only [norm_mul]
    _ ≤ qI v.asIdeal ^ ((e : ℝ) / 2) * 1 * 1 *
        qI v.asIdeal ^ ((e + 3 * l + k : ℕ) : ℝ) *
        qI v.asIdeal ^ E.re := by
      rw [hpow]
      gcongr
    _ = qI v.asIdeal ^
        ((e : ℝ) / 2 + ((e + 3 * l + k : ℕ) : ℝ) + E.re) := by
      simp only [mul_one]
      rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    _ = qI v.asIdeal ^
        ((e : ℝ) * (1 - ξ.re) + (l : ℝ) * (2 - 3 * ξ.re) +
          (k : ℝ) * (1 - w.re) - 6 * (m : ℝ) * z.re) := by rw [htotal]
    _ ≤ qI v.asIdeal ^ (-((l + k + m : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq.le htotalLe

private theorem euler_localEuler_summable (u : U.U) (v : FinPlace F)
    (hv : v ∉ S.Sf) (ξ w z : ℂ) (hreg : initialRegion ξ w z) :
    Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖localEulerTerm R η U u v hv ξ w z i‖) := by
  classical
  let q : ℝ := qI v.asIdeal
  let g : ℕ → ℝ := fun n => q ^ (-(n : ℝ))
  have hq : 1 < q := by dsimp [q]; exact qI_prime_gt_one v
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  let r : ℝ := q⁻¹
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ hqpos).2 hq
  have hgeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hrpos.le hrlt
  have hg : Summable g := by
    apply hgeom.congr
    intro n
    dsimp [g, r]
    rw [Real.rpow_neg hqpos.le, Real.rpow_natCast, inv_pow]
  have hg_nonneg (n : ℕ) : 0 ≤ g n := by
    dsimp [g]
    exact Real.rpow_nonneg hqpos.le _
  have h2 : Summable (fun p : ℕ × ℕ => g p.1 * g p.2) :=
    hg.mul_of_nonneg hg hg_nonneg hg_nonneg
  have h3 : Summable (fun p : ℕ × (ℕ × ℕ) =>
      g p.1 * (g p.2.1 * g p.2.2)) :=
    hg.mul_of_nonneg h2 hg_nonneg (fun p =>
      mul_nonneg (hg_nonneg p.1) (hg_nonneg p.2))
  have hfin : Summable (fun _ : Fin 2 => (1 : ℝ)) := Summable.of_finite
  have hmajor : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      1 * (g i.2.1 * (g i.2.2.1 * g i.2.2.2))) :=
    hfin.mul_of_nonneg h3 (fun _ => by norm_num)
      (fun p => mul_nonneg (hg_nonneg p.1) (mul_nonneg
        (hg_nonneg p.2.1) (hg_nonneg p.2.2)))
  have hgeomEq (l k m : ℕ) :
      q ^ (-((l + k + m : ℕ) : ℝ)) = g l * (g k * g m) := by
    dsimp [g]
    calc
      q ^ (-((l + k + m : ℕ) : ℝ)) = q ^ (-(l : ℝ) + (-(k : ℝ) + -(m : ℝ))) := by
        congr 1
        push_cast
        ring
      _ = q ^ (-(l : ℝ)) * (q ^ (-(k : ℝ)) * q ^ (-(m : ℝ))) := by
        rw [Real.rpow_add hqpos, Real.rpow_add hqpos]
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) ?_ hmajor
  intro i
  let l : ℕ := i.2.1
  let k : ℕ := i.2.2.1
  let m : ℕ := i.2.2.2
  calc
    ‖localEulerTerm R η U u v hv ξ w z i‖ ≤
        q ^ (-((l + k + m : ℕ) : ℝ)) := by
          simpa [q, l, k, m] using
            euler_localEulerTerm_norm_le R η U u v hv ξ w z hreg i
    _ = g l * (g k * g m) := hgeomEq l k m
    _ = 1 * (g l * (g k * g m)) := by ring

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
private lemma euler_frequency_valuation_one_eq_zero (v : FinPlace F) (hv : v ∉ S.Sf)
    (hcount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr U.one : F))) :
    frequencyValuation η U U.one v = 0 := by
  classical
  let x : S.R := U.repr U.one
  have hx : (x : F) ≠ 0 := U.repr_nonzero U.one
  have hxnorm : S.absS (S.diag (x : F)) = 1 := by
    rw [← U.q_eq_absS U.one, U.q_one]
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun w => ‖FinitePlace.embedding w (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ w : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding w (x : F)‖) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun w => ‖FinitePlace.embedding w (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ w : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding w (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ w : InfinitePlace F, w (x : F) ^ w.mult := absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) *
      (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) = 1 := by
    rw [h_absS]
    calc
      ((∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
          ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖)
        = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
            ((∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
              ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) := by ring
      _ = 1 := hprod
  have hext : ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ = 1 := by
    simpa [hxnorm] using h_prod_absS
  have h_eq : (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) =
      ∏ w ∈ hf_supp.toFinset with w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ :=
    finprod_mem_eq_prod_filter (fun w => ‖FinitePlace.embedding w (x : F)‖)
      ((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) hf_supp
  have hprod_fin : (∏ w ∈ hf_supp.toFinset with w ∉ S.Sf,
      ‖FinitePlace.embedding w (x : F)‖) = 1 := by
    rw [← h_eq]
    exact hext
  have hle : ∀ w ∈ hf_supp.toFinset.filter (fun w => w ∉ S.Sf),
      ‖FinitePlace.embedding w (x : F)‖₊ ≤ 1 := by
    intro w hw
    have hws := Finset.mem_filter.mp hw
    exact_mod_cast norm_embedding_le_one_of_valuation_le_one w (x : F)
      (x.property w hws.2)
  have hprod_fin_nn : (∏ w ∈ hf_supp.toFinset with w ∉ S.Sf,
      ‖FinitePlace.embedding w (x : F)‖₊) = 1 := by
    apply NNReal.coe_injective
    simpa using hprod_fin
  have hterms := (Finset.prod_eq_one_iff_of_le_one hle).mp hprod_fin_nn
  have hnorm_v : ‖FinitePlace.embedding v (x : F)‖ = 1 := by
    by_cases hmem : v ∈ hf_supp.toFinset
    · have hterm := hterms v (Finset.mem_filter.mpr ⟨hmem, hv⟩)
      have htermR : (‖FinitePlace.embedding v (x : F)‖₊ : ℝ) = 1 := by
        exact_mod_cast hterm
      simpa using htermR
    · have hnot : v ∉ Function.mulSupport
          (fun w => ‖FinitePlace.embedding w (x : F)‖) := by
        intro h
        apply hmem
        simpa using h
      have hnot' : ¬ ‖FinitePlace.embedding v (x : F)‖ ≠ 1 := by
        intro hne
        exact hnot ((Function.mem_mulSupport).2 hne)
      exact not_not.mp hnot'
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^
      (-FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))) = 1 := by
    rw [← norm_embedding_eq_absNorm_zpow v (x : F) hx, hnorm_v]
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have htoNat : (FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))).toNat = 0 := by
    by_contra hn
    let n := (FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))).toNat
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hncast : (n : ℤ) = FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) :=
      Int.toNat_of_nonneg hcount
    have hpow' : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) = 1 := by
      rw [hncast]
      exact hpow
    have hgt : 1 < (Ideal.absNorm v.asIdeal : ℝ) ^
        n :=
      one_lt_pow₀ hq hnpos.ne'
    have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact (inv_lt_one₀ (pow_pos (by positivity) _)).2 hgt
    linarith
  simpa [frequencyValuation, x] using htoNat


theorem po_H_eta_properties : EulerHypotheses R η →
  (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
  DifferentiableOn ℂ (Heta R η U HC) {s | 998 / 1000 - 1 / 100000 < s.re} ∧
  (∀ s, 998 / 1000 - 1 / 100000 < s.re → Heta R η U HC s ≠ 0) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ s, 998 / 1000 - 1 / 100000 < s.re → ‖Heta R η U HC s‖ ≤ C := by
  intro hEuler hloc
  have hProduct := po_H_product R η U HC hEuler
  rcases hProduct with ⟨_, hDiff, _, hBound⟩
  let HA0 : HeckeAnalysis F := Classical.choice (heckeAnalysis_exists F)
  obtain ⟨_, _, hNonzero⟩ := prop_euler_product R η U HC HA0 hEuler
  have hMaps : Set.MapsTo (fun s : ℂ => ![s, 1, 1 / 6])
      {s | 998 / 1000 - 1 / 100000 < s.re}
      {p | eulerNeighborhood p} := by
    intro s hs
    right
    refine ⟨?_, by norm_num, by norm_num⟩
    simpa using hs
  have hφ : DifferentiableOn ℂ (fun s : ℂ => ![s, 1, 1 / 6])
      {s | 998 / 1000 - 1 / 100000 < s.re} := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hDiffEta :
      DifferentiableOn ℂ (Heta R η U HC)
        {s | 998 / 1000 - 1 / 100000 < s.re} := by
    change DifferentiableOn ℂ
      (fun s : ℂ => HC.H U.one ![s, 1, 1 / 6])
      {s | 998 / 1000 - 1 / 100000 < s.re}
    exact (hDiff U.one).comp hφ hMaps
  obtain ⟨C, hC, hB⟩ := hBound 1 (by norm_num)
  refine ⟨hDiffEta, ?_, ⟨C, hC, ?_⟩⟩
  · intro s hs
    simpa [Heta] using hNonzero hloc (![s, 1, 1 / 6]) (hMaps hs)
  · intro s hs
    have h := hB U.one (![s, 1, 1 / 6]) (hMaps hs)
    simpa [Heta, U.q_one] using h


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
  let M : ℝ := max Q0 (max 1 (2 * C))
  obtain ⟨Q1, hQ1⟩ := exists_nat_gt M
  refine ⟨Q1, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hQ1
  · intro Q hQ
    have hMQ : M < Q := lt_trans hQ1 hQ
    have hQone : 1 < Q := lt_of_le_of_lt
      (le_trans (le_max_left 1 (2 * C)) (le_max_right Q0 (max 1 (2 * C)))) hMQ
    have hQpos : 0 < Q := by linarith
    by_cases hC : C ≤ 0
    · have hp : 0 < Q ^ (-(1 + 1 / 4000 : ℝ)) := Real.rpow_pos_of_pos hQpos _
      have hle : C * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC hp.le
      linarith
    · have hCpos : 0 < C := lt_of_not_ge hC
      have hQ2C : 2 * C < Q := lt_of_le_of_lt
        (le_trans (le_max_right 1 (2 * C)) (le_max_right Q0 (max 1 (2 * C)))) hMQ
      have hpow : Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ Q ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hQone.le
        norm_num
      rw [Real.rpow_neg_one] at hpow
      have hdiv : C / Q < 1 / 2 := (div_lt_iff₀ hQpos).2 (by nlinarith)
      calc
        C * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ C * Q⁻¹ :=
          mul_le_mul_of_nonneg_left hpow hCpos.le
        _ < 1 / 2 := by simpa [div_eq_mul_inv] using hdiv
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

open Filter
open scoped Topology

private theorem euler_hecke_LS_meromorphic (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
    MeromorphicOn (HA.LS S χ) Set.univ := by
  have hA := HA.2
  rcases hA with ⟨hSeries, hNontriv, hLdiff, hGdiff, hGrel, hGim, hGpos⟩
  have hL : MeromorphicOn (HA.L χ) Set.univ := by
    by_cases htriv : χ = 1
    · subst χ
      intro s hs
      by_cases hs1 : s = 1
      · subst s
        have hGanalytic : AnalyticAt ℂ HA.1.2 1 := hGdiff.analyticAt 1
        have hden : MeromorphicAt (fun z : ℂ => z - 1) 1 :=
          (analyticAt_id.sub analyticAt_const).meromorphicAt
        have hquot : MeromorphicAt (fun z : ℂ => HA.1.2 z / (z - 1)) 1 :=
          hGanalytic.meromorphicAt.div hden
        have hEq : (fun z : ℂ => HA.1.2 z / (z - 1)) =ᶠ[𝓝[≠] (1 : ℂ)] HA.L 1 := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hz1 : z ≠ 1 := by simpa using hz
          rw [hGrel z hz1]
          field_simp [sub_ne_zero.mpr hz1]
          rfl
        exact hquot.congr hEq
      · have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
        have han : AnalyticOnNhd ℂ (HA.L 1) {z : ℂ | z ≠ 1} :=
          hLdiff.analyticOnNhd hopen
        exact (han s hs1).meromorphicAt
    · obtain ⟨C, hC⟩ := hNontriv χ hχ htriv
      have hC' : C.value = HA.L χ := by
        simpa [HeckeAnalysis.L] using hC
      have hDiff : Differentiable ℂ (HA.L χ) := by
        rw [← hC']
        exact C.differentiable
      exact fun s hs => (hDiff.analyticAt s).meromorphicAt
  have hFactorDiff : Differentiable ℂ (fun s : ℂ =>
      ∏ v ∈ S.Sf, (1 - χ.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    refine Differentiable.fun_finsetProd ?_
    intro v hv
    have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
      intro hN
      exact v.ne_bot ((Ideal.absNorm_eq_zero_iff).mp hN)
    have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast hNnat
    have hpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro s
      exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (χ.primeValue v)).mul hpow)
  have hFactor : MeromorphicOn (fun s : ℂ =>
      ∏ v ∈ S.Sf, (1 - χ.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) Set.univ := by
    intro s hs
    exact (hFactorDiff.analyticAt s).meromorphicAt
  intro s hs
  change MeromorphicAt (fun z : ℂ => HA.L χ z *
    ∏ v ∈ S.Sf, (1 - χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))) s
  exact (hL s (Set.mem_univ _)).mul (hFactor s (Set.mem_univ _))

private theorem euler_kummer_finiteOrder (u : U.U) (hη : IsOfFinOrder η) :
    IsOfFinOrder (U.kummer u) := by
  obtain ⟨m, hm, hηpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hη)
  obtain ⟨n, hn, hωpow⟩ :=
    (isOfFinOrder_iff_pow_eq_one.mp (U.omega_finiteOrder u))
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  ext x
  have hηx : (η x) ^ m = 1 := by
    simpa using congrArg (fun f : HeckeChar F => f x) hηpow
  have hωx : (U.omega u x) ^ n = 1 := by
    simpa using congrArg (fun f : HeckeChar F => f x) hωpow
  have hrel : U.omega u x = η x * (U.kummer u x)⁻¹ :=
    congrArg (fun f : HeckeChar F => f x) (U.omega_induces_twist u)
  have hηxn : (η x) ^ (m * n) = 1 := by
    rw [pow_mul, hηx, one_pow]
  have hωxn : (U.omega u x) ^ (m * n) = 1 := by
    rw [Nat.mul_comm m n, pow_mul, hωx, one_pow]
  have hprod : (U.omega u x) ^ (m * n) =
      (η x) ^ (m * n) * ((U.kummer u x) ^ (m * n))⁻¹ := by
    rw [hrel, mul_pow, inv_pow]
  have hκinv : ((U.kummer u x) ^ (m * n))⁻¹ = 1 := by
    have h := hprod
    rw [hωxn, hηxn] at h
    simpa using h.symm
  have hκpow : (U.kummer u x) ^ (m * n) = 1 := inv_eq_one.mp hκinv
  change ((U.kummer u ^ (m * n)) x : ℂ) = 1
  rw [ContinuousMonoidHom.pow_apply]
  exact congrArg (fun y : ℂˣ => (y : ℂ)) hκpow

private theorem euler_H_slice_meromorphic (hEuler : EulerHypotheses R η)
    (u : U.U) (φ : ℂ → Triple) (hφ : Differentiable ℂ φ) :
    MeromorphicOn (fun s : ℂ => HC.H u (φ s)) {s | eulerNeighborhood (φ s)} := by
  have hNeighborhoodOpen : IsOpen {p : Triple | eulerNeighborhood p} := by
    have h0 : Continuous (fun p : Triple => (p 0).re) := by fun_prop
    have h1 : Continuous (fun p : Triple => (p 1).re) := by fun_prop
    have h2 : Continuous (fun p : Triple => (p 2).re) := by fun_prop
    change IsOpen
      ({p : Triple | 998 / 1000 - 1 / 100000 < (p 0).re ∧
        3 / 1000 - 1 / 100000 < (p 1).re ∧ 4 / 10 - 1 / 100000 < (p 2).re} ∪
       {p : Triple | 998 / 1000 - 1 / 100000 < (p 0).re ∧
        95 / 100 - 1 / 100000 < (p 1).re ∧ 16 / 100 - 1 / 100000 < (p 2).re})
    apply IsOpen.union
    · exact (isOpen_lt continuous_const h0).inter
        ((isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2))
    · exact (isOpen_lt continuous_const h0).inter
        ((isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2))
  let dom : Set ℂ := {s | eulerNeighborhood (φ s)}
  have hdomOpen : IsOpen dom := hNeighborhoodOpen.preimage hφ.continuous
  have hProduct := po_H_product R η U HC hEuler
  rcases hProduct with ⟨_, hDiff, _, _⟩
  have hMaps : Set.MapsTo φ dom {p | eulerNeighborhood p} := by
    intro s hs
    exact hs
  have hDiffComp : DifferentiableOn ℂ (fun s : ℂ => HC.H u (φ s)) dom :=
    (hDiff u).comp hφ.differentiableOn hMaps
  have hAnalytic : AnalyticOnNhd ℂ (fun s : ℂ => HC.H u (φ s)) dom :=
    hDiffComp.analyticOnNhd hdomOpen
  simpa only [dom] using hAnalytic.meromorphicOn

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
  intro hEuler
  have hOne : IsOfFinOrder (1 : HeckeChar F) :=
    (isOfFinOrder_iff_pow_eq_one).2 ⟨1, by norm_num, by simp⟩
  have hKummer (u : U.U) : IsOfFinOrder (U.kummer u) :=
    euler_kummer_finiteOrder η U u hEuler.1
  have hTwist (u : U.U) : IsOfFinOrder (η * (U.kummer u)⁻¹) := by
    rw [← U.omega_induces_twist u]
    exact U.omega_finiteOrder u
  have hLSOne := euler_hecke_LS_meromorphic (S := S) (HA := HA)
    (1 : HeckeChar F) hOne
  have hProduct := prop_euler_product R η U HC HA hEuler
  rcases hProduct with ⟨_, hCalF, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u ξ w z hreg
    simpa [continuedCalF] using (hCalF u ξ w z hreg).symm
  · intro u w z
    let φ : ℂ → Triple := fun ξ => ![ξ, w, z]
    have hφ : Differentiable ℂ φ := by
      rw [differentiable_pi]
      intro i
      fin_cases i <;> simp [φ]
    have hH := euler_H_slice_meromorphic R η U HC hEuler u φ hφ
    have hdom : {ξ : ℂ | eulerNeighborhood ![ξ, w, z]} =
        {ξ : ℂ | eulerNeighborhood (φ ξ)} := rfl
    have hLSK := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (U.kummer u) (hKummer u)
    have hLST := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (η * (U.kummer u)⁻¹)
      (hTwist u)
    have hH' : MeromorphicOn (fun ξ : ℂ => HC.H u ![ξ, w, z])
        {ξ | eulerNeighborhood ![ξ, w, z]} := by
      simpa [φ] using hH
    have hNum : MeromorphicOn (fun ξ : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z])
        {ξ | eulerNeighborhood ![ξ, w, z]} := by
      intro ξ hξ
      change MeromorphicAt
        ((fun _ : ℂ => HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w) *
          (fun ξ : ℂ => HC.H u ![ξ, w, z])) ξ
      exact (MeromorphicAt.const _ ξ).mul (hH' ξ hξ)
    have hDen : MeromorphicOn (HA.LS S (η * (U.kummer u)⁻¹))
        {ξ | eulerNeighborhood ![ξ, w, z]} := by
      intro ξ hξ
      exact hLST ξ (Set.mem_univ _)
    have hquot : MeromorphicOn (fun ξ : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z] /
          HA.LS S (η * (U.kummer u)⁻¹) ξ)
        {ξ | eulerNeighborhood ![ξ, w, z]} := by
      intro ξ hξ
      change MeromorphicAt
        ((fun ξ : ℂ => HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
          HC.H u ![ξ, w, z]) /
        (fun ξ : ℂ => HA.LS S (η * (U.kummer u)⁻¹) ξ)) ξ
      exact (hNum ξ hξ).div (hDen ξ hξ)
    simpa [continuedCalF, Pi.div_apply] using hquot
  · intro u ξ z
    let φ : ℂ → Triple := fun w => ![ξ, w, z]
    have hφ : Differentiable ℂ φ := by
      rw [differentiable_pi]
      intro i
      fin_cases i <;> simp [φ]
    have hH := euler_H_slice_meromorphic R η U HC hEuler u φ hφ
    have hLSK := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (U.kummer u) (hKummer u)
    have hLST := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (η * (U.kummer u)⁻¹)
      (hTwist u)
    have hH' : MeromorphicOn (fun w : ℂ => HC.H u ![ξ, w, z])
        {w | eulerNeighborhood ![ξ, w, z]} := by
      simpa [φ] using hH
    have hNum : MeromorphicOn (fun w : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z])
        {w | eulerNeighborhood ![ξ, w, z]} := by
      intro w hw
      have hK : MeromorphicAt (HA.LS S (U.kummer u)) w := hLSK w (Set.mem_univ _)
      change MeromorphicAt
        ((fun _ : ℂ => HA.LS S 1 (6 * z)) * (HA.LS S (U.kummer u)) *
          (fun w : ℂ => HC.H u ![ξ, w, z])) w
      simpa only [mul_assoc] using
        ((MeromorphicAt.const _ w).mul hK).mul (hH' w hw)
    have hDen : MeromorphicOn (fun _ : ℂ => HA.LS S (η * (U.kummer u)⁻¹) ξ)
        {w | eulerNeighborhood ![ξ, w, z]} := by
      intro w hw
      exact MeromorphicAt.const _ w
    have hquot : MeromorphicOn (fun w : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z] /
          HA.LS S (η * (U.kummer u)⁻¹) ξ)
        {w | eulerNeighborhood ![ξ, w, z]} := by
      intro w hw
      change MeromorphicAt
        ((fun w : ℂ => HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
          HC.H u ![ξ, w, z]) /
        (fun _ : ℂ => HA.LS S (η * (U.kummer u)⁻¹) ξ)) w
      exact (hNum w hw).div (hDen w hw)
    simpa [continuedCalF, Pi.div_apply] using hquot
  · intro u ξ w
    let φ : ℂ → Triple := fun z => ![ξ, w, z]
    let ψ : ℂ → ℂ := fun z => 6 * z
    have hφ : Differentiable ℂ φ := by
      rw [differentiable_pi]
      intro i
      fin_cases i <;> simp [φ]
    have hψ : AnalyticOnNhd ℂ ψ {z : ℂ | eulerNeighborhood ![ξ, w, z]} := by
      fun_prop
    have hMap : Set.MapsTo ψ {z : ℂ | eulerNeighborhood ![ξ, w, z]} Set.univ :=
      fun _ _ => Set.mem_univ _
    have hH := euler_H_slice_meromorphic R η U HC hEuler u φ hφ
    have hH' : MeromorphicOn (fun z : ℂ => HC.H u ![ξ, w, z])
        {z | eulerNeighborhood ![ξ, w, z]} := by
      simpa [φ] using hH
    have hLSK := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (U.kummer u) (hKummer u)
    have hLST := euler_hecke_LS_meromorphic (S := S) (HA := HA)
      (η * (U.kummer u)⁻¹)
      (hTwist u)
    have hLSOneComp : MeromorphicOn (fun z : ℂ => HA.LS S 1 (6 * z))
        {z | eulerNeighborhood ![ξ, w, z]} := by
      intro z hz
      have hψAt := hψ z hz
      have hLAt := hLSOne (6 * z) (Set.mem_univ _)
      change MeromorphicAt (fun z : ℂ => HA.LS S 1 (ψ z)) z
      have hcomp := hLAt.comp_analyticAt hψAt
      change MeromorphicAt (fun z : ℂ => HA.LS S 1 (ψ z)) z at hcomp
      simpa [ψ] using hcomp
    have hNum : MeromorphicOn (fun z : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z])
        {z | eulerNeighborhood ![ξ, w, z]} := by
      intro z hz
      have hK : MeromorphicAt (fun _ : ℂ => HA.LS S (U.kummer u) w) z :=
        MeromorphicAt.const _ z
      change MeromorphicAt
        ((fun z : ℂ => HA.LS S 1 (6 * z)) *
          (fun _ : ℂ => HA.LS S (U.kummer u) w) *
          (fun z : ℂ => HC.H u ![ξ, w, z])) z
      simpa only [mul_assoc] using
        (hLSOneComp z hz).mul (hK.mul (hH' z hz))
    have hDen : MeromorphicOn (fun _ : ℂ => HA.LS S (η * (U.kummer u)⁻¹) ξ)
        {z | eulerNeighborhood ![ξ, w, z]} := by
      intro z hz
      exact MeromorphicAt.const _ z
    have hquot : MeromorphicOn (fun z : ℂ =>
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z] /
          HA.LS S (η * (U.kummer u)⁻¹) ξ)
        {z | eulerNeighborhood ![ξ, w, z]} := by
      intro z hz
      change MeromorphicAt
        ((fun z : ℂ => HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
          HC.H u ![ξ, w, z]) /
        (fun _ : ℂ => HA.LS S (η * (U.kummer u)⁻¹) ξ)) z
      exact (hNum z hz).div (hDen z hz)
    simpa [continuedCalF, Pi.div_apply] using hquot
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
  intro hEuler hBounds hQ0 hQ1 hCut v hv p hp
  have hreprCount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr U.one : F)) :=
    (U.sixth_power_free U.one v hv).1
  have hfreq := euler_frequency_valuation_one_eq_zero (D := D) (S := S)
    (η := η) (U := U) v hv hreprCount
  have hnorm : (Q1 : ℝ) < qI v.asIdeal := by
    have hnot : ¬ Ideal.absNorm v.asIdeal ≤ CE := by
      intro hle
      exact hv (S.euler_mem v hle)
    have hCE : CE < Ideal.absNorm v.asIdeal := Nat.lt_of_not_ge hnot
    have hqCE : (CE : ℝ) < qI v.asIdeal := by
      change (CE : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
      exact_mod_cast hCE
    have hQ1CE : (Q1 : ℝ) ≤ (CE : ℝ) := by exact_mod_cast hQ1
    exact lt_of_le_of_lt hQ1CE hqCE
  have hnorm0 : Q0 < qI v.asIdeal := lt_trans hQ0 hnorm
  rcases hBounds with ⟨hC, hQ0pos, hLocal⟩
  have hlocal := (hLocal U.one v hv p hnorm0 hp).2
  have hcut := hCut (qI v.asIdeal) hnorm
  have hexp : (-1 - 1 / 4000 : ℝ) = -(1 + 1 / 4000 : ℝ) := by ring
  have hlocal' : ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ ≤
      C * qI v.asIdeal ^ (-(1 + 1 / 4000 : ℝ)) := by
    rw [if_pos hfreq] at hlocal
    rw [hexp] at hlocal
    exact hlocal
  exact lt_of_le_of_lt hlocal' hcut
end CanonicalEulerObject
end ArtinPrimitiveRoots.A2
