import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_rf_local_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

lemma ord_log (v : FinPlace F) (x : (v.adicCompletion F)ˣ) :
    ordv v x = -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  unfold ordv
  exact congrArg Neg.neg (WithZero.toAdd_unzero_eq_log
    ((Valuation.ne_zero_iff _).mpr x.ne_zero))

lemma ord_count (v : FinPlace F) (x : Fˣ) :
    ordv v (toLoc v x) = FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) := by
  rw [ord_log, qs_nq0_count_spanSingleton_eq_neg_log_valuation v (x : F) x.ne_zero]
  congr 2
  change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']

lemma ord_gen (S : SData F CE condη) (I : S.ExtIdeal) (x : Fˣ)
    (hx : S.IsGen (x : F) I.1) (v : FinPlace F) (hv : v ∉ S.Sf) :
    ordv v (toLoc v x) = (idealExp v I.1 : ℤ) := by
  rw [ord_count, hx.2.2 v hv, FractionalIdeal.count_coe F v I.property.1]
  rfl

lemma ord_mul (v : FinPlace F) (x y : Fˣ) :
    ordv v (toLoc v (x * y)) = ordv v (toLoc v x) + ordv v (toLoc v y) := by
  simp only [ord_count, Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero)

lemma ord_inv (v : FinPlace F) (x : Fˣ) :
    ordv v (toLoc v x⁻¹) = -ordv v (toLoc v x) := by
  have h := ord_mul v x x⁻¹
  have hone : ordv v (toLoc v (1 : Fˣ)) = 0 := by simp [ord_log]
  rw [mul_inv_cancel, hone] at h
  omega

lemma ord_div (v : FinPlace F) (x y : Fˣ) :
    ordv v (toLoc v (x / y)) = ordv v (toLoc v x) - ordv v (toLoc v y) := by
  rw [div_eq_mul_inv, ord_mul, ord_inv, sub_eq_add_neg]

lemma ord_pow (v : FinPlace F) (x : Fˣ) (n : ℕ) :
    ordv v (toLoc v (x ^ n)) = n * ordv v (toLoc v x) := by
  induction n with
  | zero => simp [ord_log]
  | succ n ih => rw [pow_succ, ord_mul, ih]; push_cast; ring

lemma ord_sunit (S : SData F CE condη) (ε : S.US)
    (v : FinPlace F) (hv : v ∉ S.Sf) : ordv v (toLoc v (ε : Fˣ)) = 0 := by
  rw [ord_count, qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ (ε : Fˣ).ne_zero,
    ε.property v hv]
  simp

lemma sunit_of_ord_zero (S : SData F CE condη) (x : Fˣ)
    (hx : ∀ v, v ∉ S.Sf → ordv v (toLoc v x) = 0) : x ∈ S.US := by
  intro v hv
  have hlog : WithZero.log (v.valuation F (x : F)) = 0 := by
    have h := hx v hv
    rw [ord_count, qs_nq0_count_spanSingleton_eq_neg_log_valuation v _ x.ne_zero] at h
    exact neg_eq_zero.mp h
  rw [← WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr x.ne_zero), hlog,
    WithZero.exp_zero]

lemma ord_finite (x : Fˣ) : (fun v : FinPlace F => ordv v (toLoc v x)).HasFiniteSupport := by
  let a := FiniteAdeleRing.unitEmbedding (𝓞 F) F x
  have hfinite := FiniteAdeleRing.hasFiniteMulSupport_valued a
  apply hfinite.subset
  intro v hv
  simp only [Function.mem_support] at hv
  simp only [Function.mem_mulSupport]
  intro hvone
  apply hv
  rw [ord_log]
  have hval : Valued.v (toLoc v x : v.adicCompletion F) = Valued.v (a.1 v) := rfl
  rw [hval, hvone]
  simp

lemma exp_ne_zero (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (v : FinPlace F) :
    idealExp v I ≠ 0 ↔ v.asIdeal ∣ I :=
  Associates.count_ne_zero_iff_dvd hI v.irreducible

lemma exp_zero_at_S (S : SData F CE condη) (I : S.ExtIdeal)
    (v : FinPlace F) (hv : v ∈ S.Sf) : idealExp v I.1 = 0 := by
  by_contra h
  exact I.property.2 v hv (Ideal.dvd_iff_le.mp ((exp_ne_zero _ I.property.1 v).mp h))

lemma exp_emultiplicity (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (v : FinPlace F) :
    emultiplicity v.asIdeal I = (idealExp v I : ℕ∞) := by
  rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hI,
    normalize_eq]
  exact_mod_cast (Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot).symm

lemma exp_squarefree_le (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (h : Squarefree I)
    (v : FinPlace F) : idealExp v I ≤ 1 := by
  have hh := ((squarefree_iff_emultiplicity_le_one I).mp h v.asIdeal).resolve_right
    v.prime.not_isUnit
  rw [exp_emultiplicity I hI v] at hh
  exact_mod_cast hh

lemma squarefree_of_exp_le (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (h : ∀ v : FinPlace F, idealExp v I ≤ 1) : Squarefree I := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hI]
  intro P hp hdvd
  let v : FinPlace F := HeightOneSpectrum.ofPrime hp.prime
  have hm : (2 : ℕ∞) ≤ emultiplicity v.asIdeal I :=
    (pow_dvd_iff_le_emultiplicity).mp (by simpa [pow_two, v, HeightOneSpectrum.ofPrime] using hdvd)
  rw [exp_emultiplicity I hI v] at hm
  have hm' : 2 ≤ idealExp v I := by exact_mod_cast hm
  have := h v
  omega

lemma ideal_ext (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ v : FinPlace F, idealExp v I = idealExp v J) : I = J := by
  let a : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
    Units.mk0 (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  let b : ClassFieldTheory.NumberFieldFractionalIdealGroup F :=
    Units.mk0 (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)
  have hab : a = b := by
    apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
    intro v
    change FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    rw [FractionalIdeal.count_coe F v hI, FractionalIdeal.count_coe F v hJ]
    exact_mod_cast h v
  exact FractionalIdeal.coeIdeal_injective (congrArg Units.val hab)

lemma ideal_of_exponents (S : SData F CE condη) (e : FinPlace F →₀ ℕ)
    (heS : ∀ v ∈ S.Sf, e v = 0) :
    ∃ I : S.ExtIdeal, ∀ v : FinPlace F, idealExp v I.1 = e v := by
  let ez : FinPlace F →₀ ℤ := e.mapRange (fun n : ℕ => (n : ℤ)) (by simp)
  let J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    ez.prod (HeightOneSpectrum.asIdeal · ^ ·)
  have hnonneg (v : FinPlace F) : 0 ≤ ez v := by simp [ez]
  have hle : J ≤ 1 := by
    dsimp [J]
    rw [Finsupp.prod]
    apply Finset.prod_le_one
    intro v hv
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hnonneg v)
    rw [hn, zpow_natCast]
    exact Left.pow_le_one_of_le FractionalIdeal.coeIdeal_le_one _
  have hne : J ≠ 0 := by
    dsimp [J]
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr (fun v hv =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
  have hc (v : FinPlace F) : FractionalIdeal.count F v J = (e v : ℤ) := by
    simpa [J, ez] using FractionalIdeal.count_finsuppProd F v ez
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hIne : I ≠ ⊥ := by
    intro h
    apply hne
    rw [← hI, h, FractionalIdeal.coeIdeal_bot]
  have hExt : S.IsExterior I := by
    refine ⟨hIne, ?_⟩
    intro v hv hIv
    have hmono := FractionalIdeal.count_mono (K := F) (v := v) hne
      (show J ≤ (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) by
        rw [← hI]; exact (FractionalIdeal.coeIdeal_le_coeIdeal F).mpr hIv)
    rw [hc, FractionalIdeal.count_self, heS v hv] at hmono
    norm_num at hmono
  refine ⟨⟨I, hExt⟩, ?_⟩
  intro v
  have hcount := hc v
  rw [← hI, FractionalIdeal.count_coe F v hIne] at hcount
  exact_mod_cast hcount

lemma coprime_of_exp_disjoint (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ v : FinPlace F, idealExp v I = 0 ∨ idealExp v J = 0) :
    IsCoprime I J := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hsup
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hsup
  have hIM : I ≤ M := le_sup_left.trans hle
  have hJM : J ≤ M := le_sup_right.trans hle
  have hM0 : M ≠ ⊥ := by
    intro hbot
    exact hI (bot_unique (hbot ▸ hIM))
  let v : FinPlace F := ⟨M, hM.isPrime, hM0⟩
  have hIexp : idealExp v I ≠ 0 := (exp_ne_zero I hI v).mpr (Ideal.dvd_iff_le.mpr hIM)
  have hJexp : idealExp v J ≠ 0 := (exp_ne_zero J hJ v).mpr (Ideal.dvd_iff_le.mpr hJM)
  exact (h v).elim hIexp hJexp

end ArtinPrimitiveRoots.Proofs.a2_rf_local_sol
