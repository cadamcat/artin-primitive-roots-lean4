import ArtinPrimitiveRoots.A1.SLattice
import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».Defs

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma bridge_absFin_mul (v : FinPlace F) (x y : v.adicCompletion F) :
    absFin v (x * y) = absFin v x * absFin v y := by
  dsimp [absFin]
  let h : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  simp only [dif_pos h]
  change (((WithZeroMulInt.toNNReal h (Valued.v (x * y))) : NNReal) : ℝ) = _
  rw [map_mul, (WithZeroMulInt.toNNReal h).map_mul]
  norm_cast

private lemma bridge_absS_mul (S : SData F CE condη) (x y : S.FS) :
    S.absS (x * y) = S.absS x * S.absS y := by
  unfold SData.absS
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
  simp_rw [bridge_absFin_mul, Complex.normSq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

private lemma bridge_absFin_one (v : FinPlace F) : absFin v 1 = 1 := by
  dsimp [absFin]
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  simp

private lemma bridge_absS_one (S : SData F CE condη) : S.absS (1 : S.FS) = 1 := by
  simp [SData.absS, bridge_absFin_one]

private lemma bridge_fsUnit_finite_ne_zero (S : SData F CE condη) (x : S.FSˣ)
    (v : S.Sf) : (x : S.FS).1 v ≠ 0 := by
  have hcoord := congrArg (fun z : S.FS => z.1 v) x.val_inv
  simp only [Prod.fst_mul, Pi.mul_apply] at hcoord
  have hne : (x : S.FS).1 v * x.inv.1 v ≠ 0 := by
    rw [hcoord]
    exact one_ne_zero
  exact (mul_ne_zero_iff.mp hne).1

private lemma bridge_fsUnit_arch_ne_zero (S : SData F CE condη) (x : S.FSˣ)
    (w : InfinitePlace F) : (x : S.FS).2 w ≠ 0 := by
  have hcoord := congrArg (fun z : S.FS => z.2 w) x.val_inv
  simp only [Prod.snd_mul, Pi.mul_apply] at hcoord
  have hne : (x : S.FS).2 w * x.inv.2 w ≠ 0 := by
    rw [hcoord]
    exact one_ne_zero
  exact (mul_ne_zero_iff.mp hne).1

private lemma bridge_absFin_pos (v : FinPlace F) (x : v.adicCompletion F) (hx : x ≠ 0) :
    0 < absFin v x := by
  dsimp [absFin]
  let h : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
  rw [dif_pos h]
  have hv : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.mpr hx
  exact NNReal.coe_pos.mpr (WithZeroMulInt.toNNReal_pos h hv)

private lemma bridge_absS_unit_pos (S : SData F CE condη) (x : S.FSˣ) :
    0 < S.absS (x : S.FS) := by
  unfold SData.absS
  apply mul_pos
  · apply Finset.prod_pos
    intro v hv
    exact bridge_absFin_pos v.1 _ (bridge_fsUnit_finite_ne_zero S x v)
  · apply Finset.prod_pos
    intro w hw
    rw [Complex.normSq_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (bridge_fsUnit_arch_ne_zero S x w))

private noncomputable def bridge_absSUnits (S : SData F CE condη) : S.FSˣ →* ℝˣ where
  toFun x := Units.mk0 (S.absS (x : S.FS)) (bridge_absS_unit_pos S x).ne'
  map_one' := by
    apply Units.ext
    simp [bridge_absS_one]
  map_mul' x y := by
    apply Units.ext
    exact bridge_absS_mul S (x : S.FS) (y : S.FS)

private lemma bridge_count_spanSingleton_div (v : FinPlace F) (x y : F)
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

private lemma bridge_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma bridge_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
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
  have hval : HeightOneSpectrum.valuation F v z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    bridge_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    bridge_count_spanSingleton_eq_neg_log_intValuation v n hn,
    bridge_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma bridge_isGen_unit (S : SData F CE condη) (e : S.US) :
    S.IsGen ((e : Fˣ) : F) ⊤ := by
  have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨top_ne_bot, ?_⟩
    intro v hv hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  refine ⟨htop, Units.ne_zero (e : Fˣ), ?_⟩
  intro v hv
  have hval : HeightOneSpectrum.valuation F v ((e : Fˣ) : F) = 1 := by
    exact Set.unit_valuation_eq_one (S := (S.Sf : Set (FinPlace F))) (K := F) e hv
  rw [bridge_count_spanSingleton_eq_neg_log_valuation v ((e : Fˣ) : F)
    (Units.ne_zero (e : Fˣ)), hval]
  simpa using (FractionalIdeal.count_one F v).symm

/-- Norm positivity and multiplicative transport, independent of balanced generator choices.
Guide: sol-thin-a2rp/PROOFS.md:20–31. Uses absS_diag_eq_norm_ofFieldData for US_norm. -/
theorem a2_bridge_NORM (D : FieldData F) (S : SData F CE condη) :
    (∀ I : S.ExtIdeal, 0 < idealNorm I.1 ∧ 1 ≤ idealNorm I.1) ∧
    (∀ x y : S.FS, S.absS (x * y) = S.absS x * S.absS y) ∧
    (∀ x : S.FSˣ, 0 < S.absS (x : S.FS)) ∧
    (∀ e : S.US, S.absS (S.diagU e : S.FS) = 1) ∧
    (∀ x y : S.FSˣ, S.absS (x / y : S.FSˣ).val =
      S.absS (x : S.FS) / S.absS (y : S.FS)) ∧
    (∀ (x : S.FSˣ) (e : ℤ), S.absS (x ^ e : S.FSˣ).val = S.absS (x : S.FS) ^ e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I
    have hN : 0 < Ideal.absNorm I.1 :=
      Ideal.absNorm_pos_of_nonZeroDivisors
        ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
          (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩
    constructor
    · change 0 < (Ideal.absNorm I.1 : ℝ)
      exact_mod_cast hN
    · change 1 ≤ (Ideal.absNorm I.1 : ℝ)
      have hN' : 1 ≤ Ideal.absNorm I.1 := Nat.one_le_iff_ne_zero.mpr hN.ne'
      exact_mod_cast hN'
  · intro x y
    exact bridge_absS_mul S x y
  · intro x
    exact bridge_absS_unit_pos S x
  · intro e
    have hgen := bridge_isGen_unit S e
    change S.absS (S.diag ((e : Fˣ) : F)) = 1
    rw [S.absS_diag_eq_norm_ofFieldData D ((e : Fˣ) : F) ⊤ hgen.1 hgen]
    simp
  · intro x y
    have h := congrArg (fun z : ℝˣ => (z : ℝ)) (map_div (bridge_absSUnits S) x y)
    simpa [bridge_absSUnits] using h
  · intro x e
    have h := congrArg (fun z : ℝˣ => (z : ℝ)) (map_zpow (bridge_absSUnits S) x e)
    simpa [bridge_absSUnits] using h

/-- Balanced-generator norm, with only the inputs needed for that generator.
Guide: sol-thin-a2rp/PROOFS.md:20–31. Uses absS_diag_eq_norm_ofFieldData and bc.gen_spec. -/
theorem a2_bridge_NORM_gen (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd) (I : S.ExtIdeal) :
    S.absS (S.diagU (bc.gen I) : S.FS) = idealNorm I.1 := by
  change S.absS (S.diag (bc.gen I : F)) = idealNorm I.1
  simpa [idealNorm] using
    S.absS_diag_eq_norm_ofFieldData D (bc.gen I : F) I.1 I.property (bc.gen_spec I).1

end ArtinPrimitiveRoots.A2
