import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.LocalCharacter

set_option autoImplicit false

open Filter NumberField IsDedekindDomain Topology
open Classical
open scoped NumberField AdeleRing FiniteAdeleRing RestrictedProduct

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- At an exterior place, a Hecke character unramified there evaluates a generator by the
uniformizer value raised to the ideal valuation. -/
theorem rf_heckeChar_loc_gen_factor_unit
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hχ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt χ v)
    (I : Ideal (𝓞 F)) (a : Fˣ)
    (ha : S.IsGen (a : F) I)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    χ.loc v (ArtinPrimitiveRoots.A1.toLoc v a) =
      χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
        (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))) ^
        ArtinPrimitiveRoots.A1.idealExp v I := by
  classical
  let n : ℕ := ArtinPrimitiveRoots.A1.idealExp v I
  have hI0 : I ≠ 0 := by
    simpa only [Ideal.zero_eq_bot] using ha.1.1
  have hcount :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
          (ArtinPrimitiveRoots.A1.idealExp v I : ℤ) := by
    rw [ha.2.2 v hv, FractionalIdeal.count_coe F v hI0]
    rfl
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) ha.2.1
  rw [hcount] at hlog
  have hLog : WithZero.log (v.valuation F (a : F)) =
      -(ArtinPrimitiveRoots.A1.idealExp v I : ℤ) := by
    linarith
  have hval_nonzero : v.valuation F (a : F) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation F)).mpr ha.2.1
  have hval : v.valuation F (a : F) =
      WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp v I : ℤ)) := by
    calc
      v.valuation F (a : F) =
          WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
        (WithZero.exp_log hval_nonzero).symm
      _ = WithZero.exp (-(ArtinPrimitiveRoots.A1.idealExp v I : ℤ)) := by rw [hLog]
  let π : (v.adicCompletion F)ˣ :=
    ArtinPrimitiveRoots.A1.toLoc v
      (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v
      (algebraMap F (v.adicCompletion F) (ArtinPrimitiveRoots.A1.unif v)) = _
    calc
      _ = v.valuation F (ArtinPrimitiveRoots.A1.unif v) :=
        v.valuedAdicCompletion_eq_valuation' (ArtinPrimitiveRoots.A1.unif v)
      _ = WithZero.exp (-1 : ℤ) :=
        (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπpow : Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-(n : ℤ)) := by
    calc
      _ = Valued.v (π : v.adicCompletion F) ^ n := by simp
      _ = WithZero.exp (-(n : ℤ)) := by
        rw [hπval]
        simpa [n] using (WithZero.exp_zsmul (n : ℤ) (-1 : ℤ)).symm
  let u : (v.adicCompletion F)ˣ := ArtinPrimitiveRoots.A1.toLoc v a * (π ^ n)⁻¹
  have huval : Valued.v (u : v.adicCompletion F) = 1 := by
    calc
      Valued.v (u : v.adicCompletion F) =
          Valued.v (ArtinPrimitiveRoots.A1.toLoc v a : v.adicCompletion F) *
            (Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ := by
              simp [u]
      _ = WithZero.exp (-(n : ℤ)) * (WithZero.exp (-(n : ℤ)))⁻¹ := by
        rw [show Valued.v (ArtinPrimitiveRoots.A1.toLoc v a : v.adicCompletion F) =
          v.valuation F (a : F) by
            exact v.valuedAdicCompletion_eq_valuation' (a : F)]
        rw [hval, hπpow]
      _ = 1 := mul_inv_cancel₀ (a := WithZero.exp (-(n : ℤ))) (by simp)
  have hu_mem : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [huval]
  have hu_inv_mem : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [Units.val_inv_eq_inv_val, huval]
  have hlocalUnit : χ.loc v u = 1 := hχ v hv u hu_mem hu_inv_mem
  have hdecomp : u * π ^ n = ArtinPrimitiveRoots.A1.toLoc v a := by
    dsimp [u]
    group
  have hloc : χ.loc v (ArtinPrimitiveRoots.A1.toLoc v a) = χ.loc v π ^ n := by
    rw [← hdecomp, map_mul, hlocalUnit, one_mul, map_pow]
  simpa [n, π] using hloc

/-- The complex-valued form of the local generator factorization. -/
theorem rf_heckeChar_loc_gen_factor
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hχ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt χ v)
    (I : Ideal (𝓞 F)) (a : Fˣ)
    (ha : S.IsGen (a : F) I)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    ((χ.loc v (ArtinPrimitiveRoots.A1.toLoc v a) : ℂˣ) : ℂ) =
      χ.primeValue v ^ ArtinPrimitiveRoots.A1.idealExp v I := by
  have hunit := rf_heckeChar_loc_gen_factor_unit S χ hχ I a ha v hv
  have hprime : χ.primeValue v =
      ((χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
        (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
          (ArtinPrimitiveRoots.A1.unif_ne_zero v))) : ℂˣ) : ℂ) := by
    simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hχ v hv]
  rw [hunit, Units.val_pow_eq_pow_val, hprime]

/-- The finite set of prime places appearing in an ideal's normalized factorization. -/
private def rfFactorPlaces (I : Ideal (𝓞 F)) : Finset (ArtinPrimitiveRoots.A1.FinPlace F) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  exact M.toFinset.attach.image fun p =>
    ⟨p.1,
      Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
          (Multiset.mem_toFinset.mp p.2)),
      (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
        (Multiset.mem_toFinset.mp p.2)).ne_zero⟩

private theorem rf_mem_factorPlaces (I : Ideal (𝓞 F)) (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (hv : v ∈ rfFactorPlaces I) : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Multiset.mem_toFinset.mp p.2

private theorem rf_factorPlaces_dvd (I : Ideal (𝓞 F))
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∈ rfFactorPlaces I) : v.asIdeal ∣ I := by
  exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (rf_mem_factorPlaces I v hv)

private theorem rf_factorPlaces_of_mem (I : Ideal (𝓞 F))
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (hv : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    v ∈ rfFactorPlaces I := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨v.asIdeal, Multiset.mem_toFinset.mpr hv⟩, by simp [rfFactorPlaces], ?_⟩
  apply HeightOneSpectrum.ext
  rfl

private theorem rf_exp_zero_of_not_factor (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ rfFactorPlaces I) :
    ArtinPrimitiveRoots.A1.idealExp v I = 0 := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
    intro hmem
    exact hv (rf_factorPlaces_of_mem I v hmem)
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
  exact Multiset.count_eq_zero.mpr hnot

private theorem rf_mem_factorPlaces_of_exp_ne_zero (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (hv : ArtinPrimitiveRoots.A1.idealExp v I ≠ 0) : v ∈ rfFactorPlaces I := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hcount :
      (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal =
        ArtinPrimitiveRoots.A1.idealExp v I := by
    change _ = (Associates.mk v.asIdeal).count (Associates.mk I).factors
    exact (Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot).symm
  have hpos : 0 < (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
    rw [hcount]
    exact Nat.pos_of_ne_zero hv
  exact rf_factorPlaces_of_mem I v (Multiset.count_pos.mp hpos)

private theorem rf_ideleFiniteCoord_principal (a : Fˣ) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v
      (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) = ArtinPrimitiveRoots.A1.toLoc v a := by
  apply Units.ext
  rfl

private theorem rf_tendsto_restrictedProduct_truncate
    {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
    [∀ i, TopologicalSpace (G i)] [∀ i, One (G i)]
    (hA : ∀ i, (1 : G i) ∈ A i)
    (x : Πʳ i, [G i, A i]) :
    Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) atTop
      (@nhds (Πʳ i, [G i, A i]) (RestrictedProduct.topologicalSpace G A cofinite) x) := by
  classical
  letI : TopologicalSpace (Πʳ i, [G i, A i]) :=
    RestrictedProduct.topologicalSpace G A cofinite
  let S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  let xS : Πʳ i, [G i, A i]_[𝓟 S] := ⟨x, by
    rw [eventually_principal]
    intro i hi
    simpa [S] using hi⟩
  have hconvPi : Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i)) := by
    apply tendsto_pi_nhds.2
    intro i
    have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s := by
      exact eventually_atTop.2 ⟨{i}, fun s hs => Finset.singleton_subset_iff.mp hs⟩
    have heq : (fun s : Finset ι => if i ∈ s then xS i else 1) =ᶠ[atTop]
        fun _ => xS i := by
      filter_upwards [hi] with s hs
      simp [hs]
    exact tendsto_const_nhds.congr' heq.symm
  letI : TopologicalSpace (Πʳ i, [G i, A i]_[𝓟 S]) :=
    RestrictedProduct.topologicalSpace G A (𝓟 S)
  have hconvS : Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then xS i else 1,
        by
          rw [eventually_principal]
          intro i hi
          by_cases his : i ∈ s
          · simp [his]
            change x i ∈ A i at hi
            simpa [xS] using hi
          · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) atTop
      (@nhds (Πʳ i, [G i, A i]_[𝓟 S])
        (RestrictedProduct.topologicalSpace G A (𝓟 S)) xS) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := A)
      (S := S)).tendsto_nhds_iff.mpr
    change Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i))
    exact hconvPi
  have hinc := (RestrictedProduct.continuous_inclusion (R := G) (A := A) hS).continuousAt
    |>.tendsto.comp hconvS
  have hx : RestrictedProduct.inclusion G A hS xS = x := rfl
  have hfun : (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) =
      RestrictedProduct.inclusion G A hS ∘ (fun s : Finset ι =>
        (⟨fun i => if i ∈ s then xS i else 1,
          by
            rw [eventually_principal]
            intro i hi
            by_cases his : i ∈ s
            · simp [his]
              change x i ∈ A i at hi
              simpa [xS] using hi
            · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) := by
    funext s
    apply Subtype.ext
    rfl
  rw [hfun]
  have hnhds : 𝓝 (RestrictedProduct.inclusion G A hS xS) = 𝓝 x :=
    congrArg (fun y => 𝓝 y) hx
  rw [← hnhds]
  exact hinc

private def rfFiniteSupportTrunc (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then
      (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1,
    by
      filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ T := by simpa using hv
      simp [hv']⟩

/-- A finite-support idele approximation defined locally in this lane to avoid the unavailable
upstream RestrictedProductDensity helper. -/
private def rfIdeleSupportTrunc (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : NumberField.IdeleGroup (𝓞 F) F :=
  (∏ w ∈ Finset.univ,
      NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
        (ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x)) *
    ∏ v ∈ T, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
      (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x)

private theorem rfIdeleSupportTrunc_infiniteCoord (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoord w (rfIdeleSupportTrunc x T) =
      ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoord w x := by
  have hunit : ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w
      (rfIdeleSupportTrunc x T) = ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x := by
    dsimp [rfIdeleSupportTrunc]
    rw [map_mul, ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit_finsetProduct]
    simp [ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]
  exact congrArg Units.val hunit

private theorem rfIdeleSupportTrunc_finiteCoord (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    (((rfIdeleSupportTrunc x T : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2 v) =
      rfFiniteSupportTrunc x T v := by
  classical
  have hcoord : ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v (rfIdeleSupportTrunc x T) =
      if v ∈ T then ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x else 1 := by
    dsimp [rfIdeleSupportTrunc]
    rw [map_mul]
    have hleft : ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v
        (∏ w ∈ Finset.univ,
          NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
            (ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x)) = 1 := by
      simp [ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord_ofCompletion]
    rw [hleft, one_mul, ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord_finsetProduct]
  calc
    ((rfIdeleSupportTrunc x T : AdeleRing (𝓞 F) F).2 v) =
        ((ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v (rfIdeleSupportTrunc x T) :
          (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
      (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord_apply v _).symm
    _ = (if v ∈ T then
          (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x : (v.adicCompletion F)ˣ)
            else 1) := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hcoord
    _ = rfFiniteSupportTrunc x T v := by
      have heval : rfFiniteSupportTrunc x T v =
          (if v ∈ T then
            (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1) :=
        rfl
      rw [heval]
      by_cases h : v ∈ T
      · simp [h]
      · simp [h]

private theorem rfIdeleSupportTrunc_coe (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (rfIdeleSupportTrunc x T : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, rfFiniteSupportTrunc x T) := by
  apply Prod.ext
  · funext w
    exact rfIdeleSupportTrunc_infiniteCoord x T w
  · apply DFunLike.ext
    intro v
    exact rfIdeleSupportTrunc_finiteCoord x T v

private theorem rfFiniteSupportTrunc_tendsto (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => rfFiniteSupportTrunc x T)
      atTop (𝓝 ((x : AdeleRing (𝓞 F) F).2)) := by
  change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (⟨fun v => if v ∈ T then ((x : AdeleRing (𝓞 F) F).2 v) else 1,
        by
          filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
          have hv' : v ∉ T := by simpa using hv
          simp [hv']⟩ : Πʳ v : HeightOneSpectrum (𝓞 F),
            [v.adicCompletion F, v.adicCompletionIntegers F])) atTop
      (@nhds (Πʳ v : HeightOneSpectrum (𝓞 F),
        [v.adicCompletion F, v.adicCompletionIntegers F])
        (RestrictedProduct.topologicalSpace
          (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
          (fun v => v.adicCompletionIntegers F) cofinite)
        ((x : AdeleRing (𝓞 F) F).2))
  exact rf_tendsto_restrictedProduct_truncate (hA := fun v => by simp)
    ((x : AdeleRing (𝓞 F) F).2)

private theorem rfIdeleSupportTrunc_inv (x : NumberField.IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (rfIdeleSupportTrunc x T)⁻¹ = rfIdeleSupportTrunc x⁻¹ T := by
  classical
  simp [rfIdeleSupportTrunc, map_inv, Finset.prod_inv_distrib]
  ac_rfl

private theorem rfIdeleSupportTrunc_coe_tendsto (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (rfIdeleSupportTrunc x T : AdeleRing (𝓞 F) F)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F))) := by
  have hprod : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((x : AdeleRing (𝓞 F) F).1, rfFiniteSupportTrunc x T)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2)) :=
    (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, rfFiniteSupportTrunc_tendsto x⟩
  have hfun : (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (rfIdeleSupportTrunc x T : AdeleRing (𝓞 F) F)) =
      fun T => ((x : AdeleRing (𝓞 F) F).1, rfFiniteSupportTrunc x T) := by
    funext T
    exact rfIdeleSupportTrunc_coe x T
  rw [hfun]
  have hxpair : (x : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2) := by
    cases x
    rfl
  rw [hxpair]
  exact hprod

private theorem rfIdeleSupportTrunc_tendsto (x : NumberField.IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => rfIdeleSupportTrunc x T)
      atTop (𝓝 x) := by
  classical
  have hval := rfIdeleSupportTrunc_coe_tendsto x
  have hvalInv : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (((rfIdeleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) atTop
      (𝓝 ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) := by
    simpa only [rfIdeleSupportTrunc_inv] using rfIdeleSupportTrunc_coe_tendsto (x⁻¹)
  have hvalInvOp : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      MulOpposite.op (((rfIdeleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) :
        AdeleRing (𝓞 F) F)) atTop
      (𝓝 (MulOpposite.op ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))) :=
    (MulOpposite.opHomeomorph.continuous.tendsto
      ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)).comp hvalInv
  have hEmbed : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      Units.embedProduct (AdeleRing (𝓞 F) F) (rfIdeleSupportTrunc x T)) atTop
      (𝓝 (Units.embedProduct (AdeleRing (𝓞 F) F) x)) := by
    change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((rfIdeleSupportTrunc x T : AdeleRing (𝓞 F) F),
        MulOpposite.op (((rfIdeleSupportTrunc x T)⁻¹ : NumberField.IdeleGroup (𝓞 F) F) :
          AdeleRing (𝓞 F) F))) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F),
        MulOpposite.op ((x⁻¹ : NumberField.IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)))
    rw [Prod.tendsto_iff]
    exact ⟨hval, hvalInvOp⟩
  exact Units.isEmbedding_embedProduct.tendsto_nhds_iff.mpr hEmbed

private theorem rf_ideleInfiniteCoord_principal (a : Fˣ) (w : InfinitePlace F) :
    ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
        Units.map (algebraMap F w.Completion).toMonoidHom a := by
  apply Units.ext
  rfl

private theorem rf_compC_diagU (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (a : Fˣ) (w : InfinitePlace F) :
    S.compC w (S.diagU a) = Units.map w.embedding.toMonoidHom a := by
  apply Units.ext
  rfl

private theorem rf_idele_inf_comp (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (a : Fˣ) (w : InfinitePlace F) :
    Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w (S.diagU a)) =
      ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w
        (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  rw [rf_compC_diagU, rf_ideleInfiniteCoord_principal]
  apply Units.ext
  apply e.injective
  simp [e, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]

private theorem rf_units_val_prod {α : Type*} (s : Finset α) (f : α → ℂˣ) :
    ((∏ v ∈ s, f v : ℂˣ) : ℂ) = ∏ v ∈ s, (f v : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih => simp [hv, ih]

/-- For an exterior ideal generator, the partial Hecke ideal value is exactly the inverse local
idele factor at `S`. This uses only that the character is unramified outside `S`. -/
theorem rf_heckeChar_idealValue_eq_LS_of_gen
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hχ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt χ v)
    (I : Ideal (𝓞 F)) (a : Fˣ)
    (ha : S.IsGen (a : F) I) :
    χ.idealValue I = S.LS χ (S.diagU a) := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := S.Sf ∪ rfFactorPlaces I
  let x : NumberField.IdeleGroup (𝓞 F) F := NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a
  let q : NumberField.IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F :=
    QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
  let ψ : NumberField.IdeleGroup (𝓞 F) F →* ℂˣ :=
    (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp q
  let locLocal (v : ArtinPrimitiveRoots.A1.FinPlace F) : ℂˣ :=
    χ.loc v (ArtinPrimitiveRoots.A1.toLoc v a)
  let infLocal (w : InfinitePlace F) : ℂˣ :=
    χ.locInf w (ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x)
  let finS : ℂˣ := ∏ v : S.Sf, locLocal v.1
  let infS : ℂˣ := ∏ w : InfinitePlace F, infLocal w
  let factorLocal : ℂˣ :=
    ∏ v ∈ rfFactorPlaces I,
      χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
        (Units.mk0 (ArtinPrimitiveRoots.A1.unif v) (ArtinPrimitiveRoots.A1.unif_ne_zero v))) ^
          ArtinPrimitiveRoots.A1.idealExp v I
  have hprincipalClass : q x = 1 := by
    change (x : NumberField.IdeleGroup (𝓞 F) F ⧸ NumberField.IdeleGroup.principalSubgroup (𝓞 F) F) = 1
    exact (QuotientGroup.eq_one_iff
      (N := NumberField.IdeleGroup.principalSubgroup (𝓞 F) F) x).mpr (by
        change x ∈ (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F).range
        exact ⟨a, rfl⟩)
  have hprincipal : ψ x = 1 := by
    change χ (q x) = 1
    rw [hprincipalClass, map_one]
  have hψcont : Continuous (fun z : NumberField.IdeleGroup (𝓞 F) F => ψ z) := by
    dsimp [ψ, q]
    exact χ.continuous.comp continuous_quotient_mk'
  have hEval (U : Finset (HeightOneSpectrum (𝓞 F))) :
      ψ (rfIdeleSupportTrunc x U) =
        (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
    calc
      ψ (rfIdeleSupportTrunc x U) =
          ψ ((∏ w ∈ Finset.univ,
            NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
              (ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x)) *
            ∏ v ∈ U, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x)) := rfl
      _ = ψ (∏ w ∈ Finset.univ,
            NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
              (ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x)) *
          ψ (∏ v ∈ U, NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x)) := map_mul ψ _ _
      _ = (∏ w : InfinitePlace F, infLocal w) *
          ∏ v ∈ U, χ.loc v (ArtinPrimitiveRoots.Dictionary.ideleFiniteCoord v x) := by
            rw [map_prod, map_prod]
            rfl
      _ = (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
            apply congrArg (fun z : ℂˣ => (∏ w : InfinitePlace F, infLocal w) * z)
            apply Finset.prod_congr rfl
            intro v hv
            rw [rf_ideleFiniteCoord_principal]
  have htruncLimit : Tendsto (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
      ψ (rfIdeleSupportTrunc x U)) atTop (𝓝 (1 : ℂˣ)) := by
    have hlim := hψcont.continuousAt.tendsto.comp (rfIdeleSupportTrunc_tendsto x)
    have hfun : ((fun z => ψ z) ∘ fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        rfIdeleSupportTrunc x U) = fun U => ψ (rfIdeleSupportTrunc x U) := by
      funext U
      rfl
    rw [hfun] at hlim
    simpa [hprincipal] using hlim
  have hlocOne (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ T) :
      locLocal v = 1 := by
    have hvS : v ∉ S.Sf := by
      intro h
      exact hv (Finset.mem_union_left _ h)
    have hvF : v ∉ rfFactorPlaces I := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hexp := rf_exp_zero_of_not_factor I ha.1.1 v hvF
    have hloc := rf_heckeChar_loc_gen_factor_unit S χ hχ I a ha v hvS
    simpa [locLocal, hexp] using hloc
  have hprodEventually :
      (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (rfIdeleSupportTrunc x U)) =ᶠ[atTop]
        fun _ => ψ (rfIdeleSupportTrunc x T) := by
    filter_upwards [eventually_atTop.2 ⟨T, fun U hTU => hTU⟩] with U hTU
    have hlocalProd : (∏ v ∈ U, locLocal v) = ∏ v ∈ T, locLocal v :=
      (Finset.prod_subset hTU (fun v hvU hvT => hlocOne v hvT)).symm
    rw [hEval U, hEval T, hlocalProd]
  have htruncOne : ψ (rfIdeleSupportTrunc x T) = 1 := by
    have hconst : Tendsto (fun _ : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (rfIdeleSupportTrunc x T)) atTop (𝓝 (1 : ℂˣ)) :=
      htruncLimit.congr' hprodEventually
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hdisj : Disjoint S.Sf (rfFactorPlaces I) := by
    rw [Finset.disjoint_left]
    intro v hvS hvF
    have hdvd := rf_factorPlaces_dvd I v hvF
    exact (ha.1.2 v hvS) (Ideal.le_of_dvd hdvd)
  have hfactorGenerator :
      (∏ v ∈ rfFactorPlaces I, locLocal v) = factorLocal := by
    apply Finset.prod_congr rfl
    intro v hvF
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (rf_factorPlaces_dvd I v hvF))
    exact rf_heckeChar_loc_gen_factor_unit S χ hχ I a ha v hvS
  have htruncProduct : infS * finS * factorLocal = 1 := by
    have h := htruncOne
    rw [hEval T] at h
    change (∏ w : InfinitePlace F, infLocal w) *
      (∏ v ∈ T, locLocal v) = 1 at h
    rw [show T = S.Sf ∪ rfFactorPlaces I by rfl,
      Finset.prod_union hdisj, hfactorGenerator] at h
    have hattach : (∏ v ∈ S.Sf, locLocal v) = finS :=
      (Finset.prod_attach S.Sf locLocal).symm
    rw [hattach] at h
    change infS * (finS * factorLocal) = 1 at h
    simpa [mul_assoc] using h
  have hfactorSupport : Function.mulSupport
      (fun v : ArtinPrimitiveRoots.A1.FinPlace F =>
        χ.primeValue v ^ ArtinPrimitiveRoots.A1.idealExp v I) ⊆ rfFactorPlaces I := by
    intro v hv
    change χ.primeValue v ^ ArtinPrimitiveRoots.A1.idealExp v I ≠ 1 at hv
    by_contra hnot
    have hexp := rf_exp_zero_of_not_factor I ha.1.1 v hnot
    simp [hexp] at hv
  have hprimeValue (v : ArtinPrimitiveRoots.A1.FinPlace F)
      (hvF : v ∈ rfFactorPlaces I) :
      χ.primeValue v =
        ((χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
          (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
            (ArtinPrimitiveRoots.A1.unif_ne_zero v))) : ℂˣ) : ℂ) := by
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (rf_factorPlaces_dvd I v hvF))
    simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hχ v hvS]
  have hidealValue : χ.idealValue I = (factorLocal : ℂ) := by
    rw [ArtinPrimitiveRoots.A2.qs_nq0_ideal_value_finprod χ I ha.1.1]
    rw [finprod_eq_prod_of_mulSupport_subset _ hfactorSupport]
    change (∏ v ∈ rfFactorPlaces I,
      χ.primeValue v ^ ArtinPrimitiveRoots.A1.idealExp v I) = (factorLocal : ℂ)
    calc
      _ = ∏ v ∈ rfFactorPlaces I,
          ((χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
            (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
              (ArtinPrimitiveRoots.A1.unif_ne_zero v))) ^
                ArtinPrimitiveRoots.A1.idealExp v I : ℂˣ) : ℂ) := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [hprimeValue v hv]
          simp [Units.val_pow_eq_pow_val]
      _ = (factorLocal : ℂ) := by
          dsimp [factorLocal]
          exact (rf_units_val_prod (rfFactorPlaces I)
            (fun v : ArtinPrimitiveRoots.A1.FinPlace F =>
            χ.loc v (ArtinPrimitiveRoots.A1.toLoc v
              (Units.mk0 (ArtinPrimitiveRoots.A1.unif v)
                (ArtinPrimitiveRoots.A1.unif_ne_zero v))) ^
                  ArtinPrimitiveRoots.A1.idealExp v I)).symm
  have hcompU (v : S.Sf) :
      S.compU v (S.diagU a) = ArtinPrimitiveRoots.A1.toLoc v.1 a := by
    ext
    rfl
  have hcompC (w : InfinitePlace F) (hw : w.IsComplex) :
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
          (S.compC w (S.diagU a)) =
        ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x :=
    rf_idele_inf_comp D S a w
  have hLS : S.LS χ (S.diagU a) =
      ((finS⁻¹ * infS⁻¹ : ℂˣ) : ℂ) := by
    have hfinite :
        (∏ v : S.Sf,
          (((χ.loc v.1 (S.compU v (S.diagU a)))⁻¹ : ℂˣ) : ℂ)) =
            ((finS⁻¹ : ℂˣ) : ℂ) := by
      simp [finS, locLocal, hcompU, Finset.prod_inv_distrib]
    let complexComp (w : InfinitePlace F) (hw : w.IsComplex) : w.Completionˣ :=
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
        (S.compC w (S.diagU a))
    have hterm (w : InfinitePlace F) :
        (if hw : w.IsComplex then
          (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ)
         else 1) = (((infLocal w)⁻¹ : ℂˣ) : ℂ) := by
      let hw : w.IsComplex := D.isTotallyComplex.isComplex w
      have hcomp : complexComp w hw = ArtinPrimitiveRoots.Dictionary.ideleInfiniteCoordUnit w x :=
        hcompC w hw
      rw [dif_pos hw]
      change (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ) =
        (((infLocal w)⁻¹ : ℂˣ) : ℂ)
      rw [hcomp]
    have hinfinite :
        (∏ w : InfinitePlace F,
          if hw : w.IsComplex then
            (((χ.locInf w (complexComp w hw))⁻¹ : ℂˣ) : ℂ)
          else 1) = ((infS⁻¹ : ℂˣ) : ℂ) := by
      calc
        _ = ∏ w : InfinitePlace F, (((infLocal w)⁻¹ : ℂˣ) : ℂ) :=
          Finset.prod_congr rfl (fun w _ => hterm w)
        _ = ((∏ w : InfinitePlace F, (infLocal w)⁻¹ : ℂˣ) : ℂ) := by
          rw [← rf_units_val_prod Finset.univ (fun w => (infLocal w)⁻¹)]
        _ = ((infS⁻¹ : ℂˣ) : ℂ) := by simp [infS, Finset.prod_inv_distrib]
    unfold ArtinPrimitiveRoots.A1.SData.LS
    rw [hfinite, hinfinite]
    simp
  have hfactorEq : factorLocal = finS⁻¹ * infS⁻¹ := by
    have hp : factorLocal * (finS * infS) = 1 := by
      calc
        factorLocal * (finS * infS) = infS * finS * factorLocal := by ac_rfl
        _ = 1 := htruncProduct
    calc
      factorLocal = factorLocal * ((finS * infS) * (finS * infS)⁻¹) := by simp
      _ = (factorLocal * (finS * infS)) * (finS * infS)⁻¹ := by group
      _ = (finS * infS)⁻¹ := by rw [hp]; simp
      _ = finS⁻¹ * infS⁻¹ := by simp [mul_comm]
  calc
    χ.idealValue I = (factorLocal : ℂ) := hidealValue
    _ = ((finS⁻¹ * infS⁻¹ : ℂˣ) : ℂ) := congrArg Units.val hfactorEq
    _ = S.LS χ (S.diagU a) := hLS.symm

end ArtinPrimitiveRoots.A2
