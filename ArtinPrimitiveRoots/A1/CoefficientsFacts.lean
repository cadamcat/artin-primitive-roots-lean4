import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import ArtinPrimitiveRoots.A1.Coefficients
import ArtinPrimitiveRoots.A1.SLattice

/-!
# A1 coefficient family facts (P-COEFF)

The Gaussian transform, decay estimate, and value at zero from `02a`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The displayed definition in eq:reflection-gaussian (02a:30–32). -/
theorem PG_formula (t : ℝ) :
    PG t = (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4) := by
  rfl

/-- The absolutely convergent Mellin transform in eq:reflection-gaussian (02a:30–38).
The `IntegrableOn` conjunct records absolute convergence. -/
theorem PG_mellin (ξ : ℂ) :
    IntegrableOn (fun t : ℝ => (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) = Complex.exp (ξ ^ 2) := by
  let k : ℝ := (2 * Real.sqrt Real.pi)⁻¹
  let g : ℝ → ℂ := fun x => (k : ℂ) *
    Complex.exp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ))
  have hg : Integrable g := by
    have h := integrable_cexp_quadratic (b := (1 / 4 : ℂ)) (by norm_num) ξ 0
    have h' : Integrable (fun x : ℝ => Complex.exp
        (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ))) := by
      convert h using 1 <;> simp
    convert h'.const_mul (k : ℂ) using 1
  have hcpow (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ ξ = Complex.exp (ξ * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
    rw [Complex.ofReal_log ht.le, mul_comm]
  have hEval (t : ℝ) (ht : 0 < t) :
      (t⁻¹ : ℝ) • g (Real.log t) =
        (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) := by
    change ((t⁻¹ : ℝ) : ℂ) * g (Real.log t) = _
    dsimp only [g]
    rw [PG, hcpow t ht, Complex.exp_add]
    simp only [k, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_inv]
    have hq : -(1 / 4 : ℂ) * (Real.log t : ℂ) ^ 2 =
        ((-(Real.log t) ^ 2 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hq]
    push_cast
    rw [div_eq_mul_inv]
    field_simp
  have hInt : IntegrableOn (fun t : ℝ => (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ)) (Set.Ioi 0) := by
    have hcomp : IntegrableOn (fun t : ℝ => (t⁻¹ : ℝ) • g (Real.log t)) (Set.Ioi 0) :=
      (integrableOn_comp_log_Ioi_zero (g := g)).2 hg
    exact hcomp.congr_fun (fun t ht => hEval t ht) measurableSet_Ioi
  refine ⟨hInt, ?_⟩
  have hsubst :
      ∫ t in Set.Ioi (0 : ℝ), (PG t : ℂ) * (t : ℂ) ^ ξ / (t : ℂ) = ∫ x, g x := by
    have := (integral_comp_log_Ioi_zero (g := g))
    rw [← this]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact (hEval t ht).symm
  rw [hsubst]
  have hgauss := integral_cexp_quadratic (b := (-(1 / 4 : ℂ))) (by norm_num) ξ 0
  dsimp only [g]
  rw [integral_const_mul]
  have hgauss' :
      ∫ x : ℝ, Complex.exp (-(1 / 4 : ℂ) * (x : ℂ) ^ 2 + ξ * (x : ℂ)) =
        ((Real.pi : ℂ) / (1 / 4 : ℂ)) ^ (1 / (2 : ℂ)) *
          Complex.exp (0 - ξ ^ 2 / (4 * -(1 / 4 : ℂ))) := by
    simpa only [add_zero, neg_neg] using hgauss
  rw [hgauss']
  have hsqrt : ((Real.pi : ℂ) / (1 / 4 : ℂ)) ^ (1 / (2 : ℂ)) =
      (2 * Real.sqrt Real.pi : ℂ) := by
    have hdiv : (Real.pi : ℂ) / (1 / 4 : ℂ) = 4 * Real.pi := by
      field_simp
    rw [hdiv]
    rw [show (4 * Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [show (1 / (2 : ℂ)) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (by positivity : 0 ≤ 4 * Real.pi) (1 / 2 : ℝ)]
    norm_cast
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    norm_num
  rw [hsqrt]
  have hexp : (0 - ξ ^ 2 / (4 * -(1 / 4 : ℂ))) = ξ ^ 2 := by
    field_simp
    ring
  rw [hexp]
  have hk : (k : ℂ) * (2 * Real.sqrt Real.pi : ℂ) = 1 := by
    dsimp [k]
    rw [Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp
    norm_num
  rw [← mul_assoc, hk, one_mul]

/-- Gaussian power decay from eq:reflection-gaussian (02a:36–38). -/
theorem PG_decay (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → PG t ≤ C * Real.rpow t (-σ) := by
  refine ⟨(2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2), by positivity, ?_⟩
  intro t ht
  have hx : -(Real.log t) ^ 2 / 4 ≤ σ ^ 2 - σ * Real.log t := by
    nlinarith [sq_nonneg (Real.log t - 2 * σ)]
  have he : Real.exp (-(Real.log t) ^ 2 / 4) ≤
      Real.exp (σ ^ 2 - σ * Real.log t) := Real.exp_le_exp.mpr hx
  have hpow : Real.rpow t (-σ) = Real.exp (Real.log t * (-σ)) :=
    Real.rpow_def_of_pos ht _
  rw [PG, hpow]
  calc
    (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4) ≤
        (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2 - σ * Real.log t) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (σ ^ 2) * Real.exp (Real.log t * (-σ)) := by
      rw [show σ ^ 2 - σ * Real.log t = σ ^ 2 + (-σ * Real.log t) by ring,
        Real.exp_add]
      rw [show -σ * Real.log t = Real.log t * (-σ) by ring]
      ring

private theorem residue_zero (P : FinPlace F) : residue P (0 : F) = 0 := by
  classical
  have hwit : ∃ ab : 𝓞 F × 𝓞 F,
      ab.2 ∉ P.asIdeal ∧ (0 : F) * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := by
    refine ⟨(0, 1), Ideal.IsPrime.one_notMem P.isPrime, ?_⟩
    simp
  have hfirst : algebraMap (𝓞 F) F hwit.choose.1 = 0 := by
    simpa using hwit.choose_spec.2.symm
  have ha0 : hwit.choose.1 = 0 := (IsFractionRing.injective (𝓞 F) F) hfirst
  rw [residue, dif_pos hwit, ha0]
  simp

private theorem chiIdealPow_zero_of_ne_top (D : FieldData F) (I : Ideal (𝓞 F))
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) : chiIdealPow D I 0 1 = 0 := by
  classical
  have hnotunit : ¬ IsUnit I := by simpa [Ideal.isUnit_iff] using hItop
  obtain ⟨Q, hQ⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI0 hnotunit
  have hQprime : Q.IsPrime := Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ)
  have hQne : Q ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hQ
  have hfactor : (if h : Q.IsPrime ∧ Q ≠ ⊥ then
      chiPow D ⟨Q, h.1, h.2⟩ (0 : F) (1 : ℤ) else 1) = 0 := by
    rw [dif_pos ⟨hQprime, hQne⟩]
    simp [chiPow, residue_zero]
  unfold chiIdealPow
  apply Multiset.prod_eq_zero
  exact Multiset.mem_map.mpr ⟨Q, hQ, hfactor⟩

private theorem ideal_mul_cube_eq_top_imp (I J : Ideal (𝓞 F))
    (h : I * J ^ 3 = ⊤) : I = ⊤ ∧ J = ⊤ := by
  have hu : IsUnit (I * J ^ 3) := by
    rw [h]
    exact Ideal.isUnit_iff.mpr rfl
  have huI : IsUnit I := isUnit_of_dvd_unit ⟨J ^ 3, by simp⟩ hu
  have hdivJ : J ^ 3 ∣ I * J ^ 3 := ⟨I, by simp [mul_comm]⟩
  have huJpow : IsUnit (J ^ 3) := isUnit_of_dvd_unit hdivJ hu
  exact ⟨Ideal.isUnit_iff.mp huI,
    Ideal.isUnit_iff.mp ((isUnit_pow_iff (by norm_num : (3 : ℕ) ≠ 0)).mp huJpow)⟩

private theorem count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private theorem count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private theorem count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
    count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    count_spanSingleton_eq_neg_log_intValuation v n hn,
    count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem top_generator_valuation (S : SData F CE condη) {c : F}
    (hc : S.IsGen c ⊤) (v : FinPlace F) (hv : v ∉ S.Sf) : v.valuation F c = 1 := by
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) c) = 0 := by
    simpa only [FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one] using hc.2.2 v hv
  have hcount' := hcount
  rw [count_spanSingleton_eq_neg_log_valuation v c hc.2.1] at hcount'
  have hlog : WithZero.log (v.valuation F c) = 0 := by linarith
  have hcval : v.valuation F c ≠ 0 := (v.valuation F).ne_zero_iff.mpr hc.2.1
  calc
    v.valuation F c = WithZero.exp (WithZero.log (v.valuation F c)) :=
      (WithZero.exp_log hcval).symm
    _ = 1 := by rw [hlog]; simp

private theorem top_generator_div_mem_R (S : SData F CE condη) {c : F}
    (hc : S.IsGen c ⊤) (r : 𝓞 F) :
    (algebraMap (𝓞 F) F r) / c ∈ S.R := by
  change ∀ v : FinPlace F, v ∉ S.Sf →
    v.valuation F ((algebraMap (𝓞 F) F r) / c) ≤ 1
  intro v hv
  rw [map_div₀, top_generator_valuation S hc v hv, div_one]
  exact v.valuation_le_one r

private theorem chiIdealPow_top (D : FieldData F) (x : F) (j : ℤ) :
    chiIdealPow D ⊤ x j = 1 := by
  unfold chiIdealPow
  rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit
    (x := (⊤ : Ideal (𝓞 F))) (Ideal.isUnit_iff.mpr rfl)]
  simp

private theorem HeckeChar.idealValue_top (ϑ : HeckeChar F) :
    ϑ.idealValue ⊤ = 1 := by
  unfold HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_of_isUnit
    (x := (⊤ : Ideal (𝓞 F))) (Ideal.isUnit_iff.mpr rfl)]
  simp

private theorem gamma_top_eq_one (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (c : F) (hc : S.IsGen c ⊤) :
    gamma D S A 2 ⊤ c = 1 := by
  classical
  letI : Subsingleton (𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) := inferInstance
  have hpsi (x : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) :
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / c)) = 1 := by
    let z : S.R := ⟨(algebraMap (𝓞 F) F x.out) / c,
      top_generator_div_mem_R S hc x.out⟩
    have hone : S.diag (1 : F) ∈ S.diagR := ⟨(1 : S.R), rfl⟩
    have hone' : S.diag (1 : F) ∈ S.annihilator A S.diagR := by
      rw [← S.diagR_eq_annihilator D A]
      exact hone
    have hz : S.diag (z : F) ∈ S.diagR := ⟨z, rfl⟩
    have h := hone' (S.diag (z : F)) hz
    change S.e A (S.diag (z : F) * S.diag (1 : F)) = 1 at h
    rw [map_one, mul_one] at h
    simpa [z] using h
  let f : (𝓞 F ⧸ (⊤ : Ideal (𝓞 F))) → ℂ := fun x =>
    chiIdealPow D ⊤ (algebraMap (𝓞 F) F x.out) 2 *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / c))
  have hf : ∀ x, f x = 1 := by
    intro x
    change chiIdealPow D ⊤ (algebraMap (𝓞 F) F x.out) 2 *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / c)) = 1
    rw [chiIdealPow_top, hpsi x]
    simp
  have hsum : (∑ᶠ x : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F)), f x) = 1 := by
    calc
      (∑ᶠ x : 𝓞 F ⧸ (⊤ : Ideal (𝓞 F)), f x) = f 0 :=
        finsum_eq_single f 0 (by
          intro x hx
          exact (hx (Subsingleton.elim x 0)).elim)
      _ = 1 := hf 0
  unfold gamma
  rw [Ideal.absNorm_top]
  simp only [Nat.cast_one, Real.one_rpow, Complex.ofReal_one, one_mul]
  simpa [f] using hsum

/-- The value at zero from cf:B0 (02a:63–64). The unit-ideal representative is normalized;
representatives at other ideals do not affect this value. -/
theorem B0_eq_PG (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (ϑ : HeckeChar F) (cgen : S.SqfExtIdeal → F)
    (hunit : ∀ I : S.SqfExtIdeal, I.1 = ⊤ → S.IsGen (cgen I) ⊤)
    (Z : ℝ) (hZ : 0 < Z) :
    Bm D S A ϑ cgen 0 Z = (PG (1 / Z) : ℂ) := by
  classical
  let htopExt : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨top_ne_bot, ?_⟩
    intro v hv hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  let I₀ : S.SqfExtIdeal := ⟨⊤, ⟨htopExt, by simp [Ideal.one_eq_top]⟩⟩
  let J₀ : S.ExtIdeal := ⟨⊤, htopExt⟩
  let p₀ : S.SqfExtIdeal × S.ExtIdeal := (I₀, J₀)
  let term : S.SqfExtIdeal × S.ExtIdeal → ℂ := fun p =>
    gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) *
      chiIdealPow D (p.1.1 * p.2.1 ^ 3) 0 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)
  have hterm_zero : ∀ p, p ≠ p₀ → term p = 0 := by
    intro p hp
    rcases p with ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩
    have hprod0 : I * J ^ 3 ≠ ⊥ := mul_ne_zero hI.1.1 (pow_ne_zero 3 hJ.1)
    have hprodtop : I * J ^ 3 ≠ ⊤ := by
      intro h
      obtain ⟨hIeq, hJeq⟩ := ideal_mul_cube_eq_top_imp I J h
      apply hp
      apply Prod.ext
      · apply Subtype.ext
        exact hIeq
      · apply Subtype.ext
        exact hJeq
    have hchi := chiIdealPow_zero_of_ne_top D (I * J ^ 3) hprod0 hprodtop
    simp [term, hchi]
  have hc₀ : S.IsGen (cgen I₀) ⊤ := hunit I₀ (by simp [I₀])
  have hgamma₀ := gamma_top_eq_one D S A (cgen I₀) hc₀
  have hterm₀ : term p₀ = (PG (1 / Z) : ℂ) := by
    simp [term, p₀, I₀, J₀, hgamma₀, HeckeChar.idealValue_top,
      chiIdealPow_top, Ideal.absNorm_top, Ideal.top_pow]
  change (∑' p, term p) = (PG (1 / Z) : ℂ)
  rw [tsum_eq_single p₀ hterm_zero]
  exact hterm₀

end ArtinPrimitiveRoots.A1
