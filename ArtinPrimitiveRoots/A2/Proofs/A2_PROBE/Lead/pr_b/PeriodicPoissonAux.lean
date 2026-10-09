import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts

set_option autoImplicit false
set_option maxHeartbeats 5000000
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.pr_b

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}

theorem e_add (S : SData F CE condη) (A : AddCharData F) (x y : S.FS) :
    S.e A (x + y) = S.e A x * S.e A y := by
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

theorem e_diagR_one (S : SData F CE condη) (D : FieldData F)
    (A : AddCharData F) (x : S.R) : S.e A (S.diag (x : F)) = 1 := by
  have hx : S.diag (x : F) ∈ S.diagR := ⟨x, rfl⟩
  have hAnn : S.diag (x : F) ∈ S.annihilator A S.diagR := by
    rw [← S.diagR_eq_annihilator D A]
    exact hx
  have h1 : S.diag (1 : F) ∈ S.diagR := ⟨1, rfl⟩
  have h := hAnn (S.diag (1 : F)) h1
  simpa [SData.diag] using h

private lemma count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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

private theorem gen_lt_one (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (v : FinPlace F) (hvI : v.asIdeal ∣ I.1) :
    HeightOneSpectrum.valuation F v (R.exterior.genR I : F) < 1 := by
  have hg : S.IsGen (R.exterior.genR I : F) I.1 := by
    rw [R.exterior.genR_val]
    exact (bc.gen_spec I).1
  have hI0 : I.1 ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using I.2.1
  have hcountI : 0 < FractionalIdeal.count F v
      (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.count_coe F v hI0]
    exact_mod_cast Nat.pos_of_ne_zero
      ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).2 hvI)
  have hvS : v ∉ S.Sf := fun hv => I.2.2 v hv (Ideal.le_of_dvd hvI)
  have hcountg := hg.2.2 v hvS
  have hlog := count_spanSingleton_eq_neg_log_valuation v
    (R.exterior.genR I : F) hg.2.1
  rw [hcountg] at hlog
  have hloglt : WithZero.log (HeightOneSpectrum.valuation F v
      (R.exterior.genR I : F)) < 0 := by linarith
  have hgval0 : HeightOneSpectrum.valuation F v (R.exterior.genR I : F) ≠ 0 :=
    (v.valuation F).ne_zero_iff.mpr hg.2.1
  calc
    HeightOneSpectrum.valuation F v (R.exterior.genR I : F) =
        WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v
          (R.exterior.genR I : F))) :=
      (WithZero.exp_log hgval0).symm
    _ < 1 := WithZero.exp_lt_one_iff.mpr hloglt

private theorem chiIdealPow_congr (I : Ideal (𝓞 F)) (hI : S.IsExterior I)
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

theorem chiIdealPow_eq_of_mod (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (x y : S.R)
    (hxy : x - y ∈ Ideal.span {R.exterior.genR I}) :
    chiIdealPow D I.1 (x : F) 1 = chiIdealPow D I.1 (y : F) 1 := by
  apply chiIdealPow_congr I.1 I.2 (x : F) (y : F)
  intro v hvI
  have hvS : v ∉ S.Sf := by
    intro hv
    exact I.2.2 v hv (Ideal.le_of_dvd hvI)
  have hx : HeightOneSpectrum.valuation F v (x : F) ≤ 1 := x.property v hvS
  have hy : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hvS
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hxy
  have hdiff : (x : F) - (y : F) = (r : F) * (R.exterior.genR I : F) := by
    have := congrArg (fun z : S.R => (z : F)) hr
    simpa using this.symm
  have hrval : HeightOneSpectrum.valuation F v (r : F) ≤ 1 := r.property v hvS
  have hgen : HeightOneSpectrum.valuation F v (R.exterior.genR I : F) < 1 :=
    gen_lt_one R I v hvI
  have hdiffval : HeightOneSpectrum.valuation F v ((x : F) - (y : F)) < 1 := by
    rw [hdiff, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hrval zero_le hgen
  exact ⟨hx, hy, hdiffval⟩

theorem isGen_mul (I J : Ideal (𝓞 F)) (a b : Fˣ)
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
        (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := FractionalIdeal.coeIdeal_mul I J
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

theorem allowed_generator_lift (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (I : S.ExtIdeal) (a : Fˣ) (ha : S.IsGen (a : F) I.1) (hallowed : Bd.Allowed a) :
    ∃ u : S.Rˣ, ((u ^ 6 * R.exterior.genR I : S.R) : F) = (a : F) := by
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
    ((epsR ^ 6 * R.exterior.genR I : S.R) : F) =
        ((epsR : S.Rˣ) : F) ^ 6 * ((R.exterior.genR I : S.R) : F) := by simp
    _ = ((ε : Fˣ) : F) ^ 6 * (bc.gen I : F) := by
      rw [hepsR, R.exterior.genR_val]
    _ = (a : F) := hrelF.symm

end ArtinPrimitiveRoots.Proofs.pr_b
