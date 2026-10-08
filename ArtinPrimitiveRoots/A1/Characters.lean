import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Equality
import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ResidueUnits

/-!
# A1 interface, §5: Hecke, Kummer, class and Gauss correction characters

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open Filter Topology
open scoped Classical
open scoped NumberField AdeleRing FiniteAdeleRing RestrictedProduct

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 5. Hecke characters, Kummer / class / Gauss correction characters -/

/-- Hecke characters of `F` (continuous characters of the idele class group; TauCeti's
`HeckeCharacter` is the same type). -/
abbrev HeckeChar (F : Type) [Field F] [NumberField F] :=
  ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) ℂˣ

/-- Local component at a finite place. -/
def HeckeChar.loc (χ : HeckeChar F) (v : FinPlace F) : (v.adicCompletion F)ˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v)

/-- Local component at an infinite place. -/
def HeckeChar.locInf (χ : HeckeChar F) (w : InfinitePlace F) : w.Completionˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp (IdeleClassGroup.ofCompletion (𝓞 F) F w)

/-- Unramified at `v`: trivial on the local units. -/
def HeckeChar.UnramifiedAt (χ : HeckeChar F) (v : FinPlace F) : Prop :=
  ∀ u : (v.adicCompletion F)ˣ, (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      χ.loc v u = 1

/-- A fixed global uniformizer at `v`. -/
def unif (v : FinPlace F) : F :=
  (HeightOneSpectrum.valuation_exists_uniformizer F v).choose

theorem unif_ne_zero (v : FinPlace F) : unif v ≠ 0 := by
  intro h
  have := (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  rw [← unif, h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- `χ(𝔭) := χ_v(ϖ_v)` at an unramified `v` (ideal-character convention), else 0. -/
def HeckeChar.primeValue (χ : HeckeChar F) (v : FinPlace F) : ℂ :=
  if χ.UnramifiedAt v then
    ((χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) : ℂˣ) : ℂ) else 0

/-- Ideal value `χ(I) = Π_{P^k ∥ I} χ(P)^k`. -/
def HeckeChar.idealValue (χ : HeckeChar F) (I : Ideal (𝓞 F)) : ℂ :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then χ.primeValue ⟨P, h.1, h.2⟩ else 1).prod

/-- Exponent of the prime `v` in an ideal. -/
def idealExp (v : FinPlace F) (I : Ideal (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk I).factors

/-- A modulus bound for the conductor: `χ` is trivial on the local units `u ≡ 1 mod 𝔭_v^{e_v(𝔪)}`
at every finite `v` (for `e_v(𝔪) = 0`: on all local units); then the conductor divides `𝔪`.
Corrected 2026-10-07: the first version quantified `∀ x ∈ 𝔪` and was vacuous at `x = 0`
(A2 agent, `research/design/A2-ThetaCheck.lean`, `conductorDvd_vacuous`). -/
def HeckeChar.ConductorDvd (χ : HeckeChar F) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ v : FinPlace F, ∀ u : (v.adicCompletion F)ˣ,
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(idealExp v 𝔪 : ℤ)) →
    χ.loc v u = 1

/-- Kummer character `κ_u` (ar:kummer-hecke, 02:285–357): finite order, unramified at exterior
`v` with `v(u) = 0`, and `κ_u(v) = χ_v(u)` there. Package P-ARITH-KUMMER. -/
theorem kummer_exists (D : FieldData F) (S : SData F CE condη) (u : Fˣ) :
    ∃ κ : HeckeChar F, IsOfFinOrder κ ∧ ∀ v : FinPlace F, v ∉ S.Sf → residue v (u : F) ≠ 0 →
      κ.UnramifiedAt v ∧ κ.primeValue v = chi D v (u : F) := by
  obtain ⟨H⟩ := HilbertData.nonempty D
  obtain ⟨κ, hκ, _, hloc⟩ := KummerProofs.kummer_character_exists D H u
  refine ⟨κ, isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκ⟩, ?_⟩
  intro P hP hu
  have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hP (S.over6 P h)
  exact KummerProofs.kummer_prime_values D H u κ hloc P h6 hu

/-- eq:kummer-conductor (02:290–298), modulus form: `κ_u` (and `η κ_u^{-1}`) has conductor
dividing a modulus of norm `≤ C·N rad(uR)`. -/
theorem kummer_conductor (D : FieldData F) (S : SData F CE condη) (η : HeckeChar F) :
    ∃ C : ℝ, ∀ u : 𝓞 F, u ≠ 0 → ∀ κ : HeckeChar F,
      (∀ v : FinPlace F, v ∉ S.Sf → residue v (u : F) ≠ 0 →
        κ.UnramifiedAt v ∧ κ.primeValue v = chi D v (u : F)) → IsOfFinOrder κ →
      (∃ 𝔪 : Ideal (𝓞 F), κ.ConductorDvd 𝔪 ∧
        (Ideal.absNorm 𝔪 : ℝ) ≤ C * Ideal.absNorm (Ideal.span {u}).radical) ∧
      (∃ 𝔪 : Ideal (𝓞 F), (η * κ⁻¹).ConductorDvd 𝔪 ∧
        (Ideal.absNorm 𝔪 : ℝ) ≤ C * Ideal.absNorm (Ideal.span {u}).radical) := by
  sorry

/-- ar:kummer-equality (02:299–300): `κ_u = κ_v ↔ u/v ∈ F^{×6}`. Package P-ARITH-KUMMER. -/
theorem kummer_eq_iff (D : FieldData F) (S : SData F CE condη) (u v : Fˣ) (κu κv : HeckeChar F)
    (hu : ∀ P : FinPlace F, P ∉ S.Sf → residue P (u : F) ≠ 0 →
      κu.UnramifiedAt P ∧ κu.primeValue P = chi D P (u : F))
    (hv : ∀ P : FinPlace F, P ∉ S.Sf → residue P (v : F) ≠ 0 →
      κv.UnramifiedAt P ∧ κv.primeValue P = chi D P (v : F))
    (hfu : IsOfFinOrder κu) (hfv : IsOfFinOrder κv) :
    κu = κv ↔ ∃ t : Fˣ, u / v = t ^ 6 := by
  obtain ⟨H⟩ := HilbertData.nonempty D
  obtain ⟨κu₀, hκu₀, huInf, huloc⟩ := KummerProofs.kummer_character_exists D H u
  obtain ⟨κv₀, hκv₀, hvInf, hvloc⟩ := KummerProofs.kummer_character_exists D H v
  have hfu₀ : IsOfFinOrder κu₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκu₀⟩
  have hfv₀ : IsOfFinOrder κv₀ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨6, by decide, hκv₀⟩
  let T := S.Sf ∪ (KummerProofs.residue_zero_finite u).toFinset ∪
    (KummerProofs.residue_zero_finite v).toFinset
  have hout (P : FinPlace F) (hP : P ∉ T) :
      P ∉ S.Sf ∧ residue P (u : F) ≠ 0 ∧ residue P (v : F) ≠ 0 := by
    simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP
    exact ⟨hP.1.1, hP.1.2, hP.2⟩
  have heu : κu = κu₀ := by
    apply KummerProofs.finite_order_good_prime_unique κu κu₀ hfu hfu₀ T
    intro P hP
    obtain ⟨hPS, huP, _⟩ := hout P hP
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hPS (S.over6 P h)
    have h₁ := hu P hPS huP
    have h₂ := KummerProofs.kummer_prime_values D H u κu₀ huloc P h6 huP
    exact ⟨h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩
  have hev : κv = κv₀ := by
    apply KummerProofs.finite_order_good_prime_unique κv κv₀ hfv hfv₀ T
    intro P hP
    obtain ⟨hPS, _, hvP⟩ := hout P hP
    have h6 : (6 : 𝓞 F) ∉ P.asIdeal := fun h => hPS (S.over6 P h)
    have h₁ := hv P hPS hvP
    have h₂ := KummerProofs.kummer_prime_values D H v κv₀ hvloc P h6 hvP
    exact ⟨h₁.1, h₂.1, h₁.2.trans h₂.2.symm⟩
  rw [heu, hev]
  exact KummerProofs.kummer_realization_eq_iff D H u v κu₀ κv₀ huInf hvInf huloc hvloc

/-- ar:B-character-extension (02:302–303, 359–366): every character of `B` evaluated on allowed
generators extends to a finite-order Hecke character unramified outside `S`. Package
P-ARITH-KUMMER. -/
theorem class_character_extension (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (θB : Bd.B →* ℂˣ) :
    ∃ θ : HeckeChar F, IsOfFinOrder θ ∧ (∀ v : FinPlace F, v ∉ S.Sf → θ.UnramifiedAt v) ∧
      ∀ (I : Ideal (𝓞 F)) (a : Fˣ), S.IsExterior I → S.IsGen (a : F) I → (ha : Bd.Allowed a) →
        θ.idealValue I = ((θB ⟨_, ha⟩ : ℂˣ) : ℂ) := by
  sorry

/-- Archimedean angular type of a Hecke character at the complex places. -/
def HeckeChar.HasAngularType (D : FieldData F) (χ : HeckeChar F) : Prop :=
  ∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧
    ∀ z : ℂˣ,
      ((χ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) : ℂˣ) : ℂ) =
        ((z : ℂ) / ‖(z : ℂ)‖) ^ m

/-- lem:gauss-characters (02:411–436): `Λ` unitary, `G` finite order, both unramified at `v ∉ S`,
with `γ_2(𝔭)³ = -Λ(𝔭)`, `G(𝔭) = conj(χ_𝔭(4))γ_3(𝔭)`, `γ_1(𝔭)γ_2(𝔭) = -Λ(𝔭)G(𝔭)` for every exterior
prime and allowed generator. Package P-ARITH-GAUSS (Λ: P-ARITH-LAMBDA, G: P-WEIL).
Corrected per rev-theta to include `Λ`'s angular type and the cubic-sign character. -/
theorem gauss_characters (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) :
    ∃ Λ G : HeckeChar F, IsOfFinOrder G ∧
      (∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1) ∧
      HeckeChar.HasAngularType D Λ ∧
      (∃ θB : Bd.B →* ℂˣ, ∀ v : FinPlace F, v ∉ S.Sf →
        ∀ p : Fˣ, ∀ (hpgen : S.IsGen (p : F) v.asIdeal),
          ∀ (hpAllowed : Bd.Allowed p),
          (gamma D S A 3 v.asIdeal (p : F) = 1 ∨
            gamma D S A 3 v.asIdeal (p : F) = -1) ∧
          gamma D S A 3 v.asIdeal (p : F) =
            ((θB ⟨(QuotientGroup.mk (S.diagU p) : S.V), hpAllowed⟩ : ℂˣ) : ℂ)) ∧
      ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          gamma D S A 2 v.asIdeal (p : F) ^ 3 = -Λ.primeValue v ∧
          G.primeValue v = (starRingEnd ℂ) (chi D v 4) * gamma D S A 3 v.asIdeal (p : F) ∧
          gamma D S A 1 v.asIdeal (p : F) * gamma D S A 2 v.asIdeal (p : F) =
            -(Λ.primeValue v * G.primeValue v) := by
  sorry

/-- `ϑ = Λ̄ Ḡ η = Λ⁻¹ G⁻¹ η` (unitary) (02:606–608). -/
def vartheta (Λ G η : HeckeChar F) : HeckeChar F := Λ⁻¹ * G⁻¹ * η

/-- `L_S(y) = Π_{v∈S} ϑ_v(y_v)^{-1}` (02:610–613). Complex places through
`ringEquivComplexOfIsComplex`. -/
def SData.LS (S : SData F CE condη) (ϑ : HeckeChar F) (y : S.FSˣ) : ℂ :=
  (∏ v : S.Sf, (((ϑ.loc v.1 (S.compU v y))⁻¹ : ℂˣ) : ℂ)) *
    ∏ w : InfinitePlace F,
      if hw : w.IsComplex then
        (((ϑ.locInf w (Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
            (S.compC w y)))⁻¹ : ℂˣ) : ℂ)
      else 1

private def conductor_factorPlaces (I : Ideal (𝓞 F)) : Finset (FinPlace F) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  exact M.toFinset.attach.image fun p =>
    ⟨p.1,
      Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
          (Multiset.mem_toFinset.mp p.2)),
      (UniqueFactorizationMonoid.prime_of_normalized_factor p.1
        (Multiset.mem_toFinset.mp p.2)).ne_zero⟩

private theorem conductor_mem_factorPlaces (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_factorPlaces I) :
    v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
  exact Multiset.mem_toFinset.mp p.2

private theorem conductor_factorPlaces_dvd (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v ∈ conductor_factorPlaces I) : v.asIdeal ∣ I :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (conductor_mem_factorPlaces I v hv)

private theorem conductor_factorPlaces_of_mem (I : Ideal (𝓞 F)) (v : FinPlace F)
    (hv : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    v ∈ conductor_factorPlaces I := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨v.asIdeal, Multiset.mem_toFinset.mpr hv⟩, by simp [conductor_factorPlaces], ?_⟩
  apply HeightOneSpectrum.ext
  rfl

private theorem conductor_exp_zero_of_not_factor (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : FinPlace F) (hv : v ∉ conductor_factorPlaces I) : idealExp v I = 0 := by
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I := by
    intro hmem
    exact hv (conductor_factorPlaces_of_mem I v hmem)
  change (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
  rw [Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
  exact Multiset.count_eq_zero.mpr hnot

private theorem conductor_loc_gen_factor_unit
    (S : SData F CE condη) (χ : HeckeChar F)
    (hχ : ∀ v : FinPlace F, v ∉ S.Sf → χ.UnramifiedAt v)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    χ.loc v (toLoc v a) =
      χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I := by
  classical
  let n : ℕ := idealExp v I
  have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using ha.1.1
  have hcount :
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
          (idealExp v I : ℤ) := by
    rw [ha.2.2 v hv, FractionalIdeal.count_coe F v hI0]
    rfl
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) ha.2.1
  rw [hcount] at hlog
  have hLog : WithZero.log (v.valuation F (a : F)) = -(idealExp v I : ℤ) := by
    linarith
  have hval_nonzero : v.valuation F (a : F) ≠ 0 :=
    (Valuation.ne_zero_iff (v.valuation F)).mpr ha.2.1
  have hval : v.valuation F (a : F) = WithZero.exp (-(idealExp v I : ℤ)) := by
    calc
      v.valuation F (a : F) =
          WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
        (WithZero.exp_log hval_nonzero).symm
      _ = WithZero.exp (-(idealExp v I : ℤ)) := by rw [hLog]
  let π : (v.adicCompletion F)ˣ :=
    toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
  have hπval : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (unif v)) = _
    calc
      _ = v.valuation F (unif v) := v.valuedAdicCompletion_eq_valuation' (unif v)
      _ = WithZero.exp (-1 : ℤ) :=
        (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπpow : Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-(n : ℤ)) := by
    calc
      _ = Valued.v (π : v.adicCompletion F) ^ n := by simp
      _ = WithZero.exp (-(n : ℤ)) := by
        rw [hπval]
        simpa [n] using (WithZero.exp_zsmul (n : ℤ) (-1 : ℤ)).symm
  let u : (v.adicCompletion F)ˣ := toLoc v a * (π ^ n)⁻¹
  have huval : Valued.v (u : v.adicCompletion F) = 1 := by
    calc
      Valued.v (u : v.adicCompletion F) =
          Valued.v (toLoc v a : v.adicCompletion F) *
            (Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ := by
              simp [u]
      _ = WithZero.exp (-(n : ℤ)) * (WithZero.exp (-(n : ℤ)))⁻¹ := by
        rw [show Valued.v (toLoc v a : v.adicCompletion F) = v.valuation F (a : F) by
          exact v.valuedAdicCompletion_eq_valuation' (a : F)]
        rw [hval, hπpow]
      _ = 1 := mul_inv_cancel₀ (a := WithZero.exp (-(n : ℤ))) (by simp)
  have hu_mem : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, huval]
  have hu_inv_mem : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [Units.val_inv_eq_inv_val, huval]
  have hlocalUnit : χ.loc v u = 1 := hχ v hv u hu_mem hu_inv_mem
  have hdecomp : u * π ^ n = toLoc v a := by
    dsimp [u]
    group
  have hloc : χ.loc v (toLoc v a) = χ.loc v π ^ n := by
    rw [← hdecomp, map_mul, hlocalUnit, one_mul, map_pow]
  simpa [n, π] using hloc

private theorem conductor_idealValue_finprod (χ : HeckeChar F) (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) : χ.idealValue I = ∏ᶠ v : FinPlace F, χ.primeValue v ^ idealExp v I := by
  classical
  unfold HeckeChar.idealValue
  rw [Multiset.prod_map_eq_finprod]
  rw [← finprod_emb_domain' IsDedekindDomain.HeightOneSpectrum.asIdeal_injective
    (fun v : FinPlace F => χ.primeValue v ^ idealExp v I)]
  apply finprod_congr
  intro P
  by_cases hp : P.IsPrime ∧ P ≠ ⊥
  · let v : FinPlace F := ⟨P, hp.1, hp.2⟩
    have hmem : P ∈ Set.range (fun v : FinPlace F => v.asIdeal) := ⟨v, rfl⟩
    rw [dif_pos hp, dif_pos hmem]
    have hv : Classical.choose hmem = v :=
      IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Classical.choose_spec hmem)
    rw [hv]
    congr 1
    have hI0 : I ≠ 0 := by simpa only [Ideal.zero_eq_bot] using hI
    exact (Ideal.count_associates_factors_eq hI0 hp.1 hp.2).symm
  · have hnot : P ∉ Set.range (fun v : FinPlace F => v.asIdeal) := by
      rintro ⟨v, rfl⟩
      exact hp ⟨v.isPrime, v.ne_bot⟩
    simp only [dif_neg hp, one_pow, dif_neg hnot]

private theorem conductor_idele_inf_comp
    (D : FieldData F) (S : SData F CE condη) (a : Fˣ) (w : InfinitePlace F) :
    Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w (S.diagU a)) =
      Dictionary.ideleInfiniteCoordUnit w (IdeleGroup.unitEmbedding (𝓞 F) F a) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  have hcomp : S.compC w (S.diagU a) = Units.map w.embedding.toMonoidHom a := by
    apply Units.ext
    rfl
  have hprincipal : Dictionary.ideleInfiniteCoordUnit w
      (IdeleGroup.unitEmbedding (𝓞 F) F a) =
        Units.map (algebraMap F w.Completion).toMonoidHom a := by
    apply Units.ext
    rfl
  rw [hcomp, hprincipal]
  apply Units.ext
  apply e.injective
  simp [e, InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply,
    InfinitePlace.Completion.extensionEmbedding_coe]

private theorem conductor_units_val_prod {α : Type*} (s : Finset α) (f : α → ℂˣ) :
    ((∏ v ∈ s, f v : ℂˣ) : ℂ) = ∏ v ∈ s, (f v : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih => simp [hv, ih]

private theorem conductor_rp_truncate
    {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
    [∀ i, TopologicalSpace (G i)] [∀ i, One (G i)]
    (hA : ∀ i, (1 : G i) ∈ A i) (x : Πʳ i, [G i, A i]) :
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
    have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s :=
      eventually_atTop.2 ⟨{i}, fun s hs => Finset.singleton_subset_iff.mp hs⟩
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

private def conductor_finiteSupportTrunc (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then
      (Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1,
    by
      filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ T := by simpa using hv
      simp [hv']⟩

private def conductor_ideleSupportTrunc (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) : IdeleGroup (𝓞 F) F :=
  (∏ w ∈ Finset.univ,
      IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w x)) *
    ∏ v ∈ T, IdeleGroup.ofAdicCompletion (𝓞 F) F v (Dictionary.ideleFiniteCoord v x)

private theorem conductor_ideleSupportTrunc_infiniteCoord (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    Dictionary.ideleInfiniteCoord w (conductor_ideleSupportTrunc x T) =
      Dictionary.ideleInfiniteCoord w x := by
  have hunit : Dictionary.ideleInfiniteCoordUnit w (conductor_ideleSupportTrunc x T) =
      Dictionary.ideleInfiniteCoordUnit w x := by
    dsimp [conductor_ideleSupportTrunc]
    rw [map_mul, Dictionary.ideleInfiniteCoordUnit_finsetProduct]
    simp [Dictionary.ideleInfiniteCoordUnit_ofAdicCompletion]
  exact congrArg Units.val hunit

private theorem conductor_ideleSupportTrunc_finiteCoord (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    (((conductor_ideleSupportTrunc x T : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2 v) =
      conductor_finiteSupportTrunc x T v := by
  classical
  have hcoord : Dictionary.ideleFiniteCoord v (conductor_ideleSupportTrunc x T) =
      if v ∈ T then Dictionary.ideleFiniteCoord v x else 1 := by
    dsimp [conductor_ideleSupportTrunc]
    rw [map_mul]
    have hleft : Dictionary.ideleFiniteCoord v
        (∏ w ∈ Finset.univ,
          IdeleGroup.ofCompletion (𝓞 F) F w (Dictionary.ideleInfiniteCoordUnit w x)) = 1 := by
      simp [Dictionary.ideleFiniteCoord_ofCompletion]
    rw [hleft, one_mul, Dictionary.ideleFiniteCoord_finsetProduct]
  calc
    (((conductor_ideleSupportTrunc x T : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F).2 v) =
        ((Dictionary.ideleFiniteCoord v (conductor_ideleSupportTrunc x T) :
          (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
      (Dictionary.ideleFiniteCoord_apply v _).symm
    _ = (if v ∈ T then
          (Dictionary.ideleFiniteCoord v x : (v.adicCompletion F)ˣ) else 1) :=
            congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) hcoord
    _ = conductor_finiteSupportTrunc x T v := by
      have heval : conductor_finiteSupportTrunc x T v =
          (if v ∈ T then
            (Dictionary.ideleFiniteCoord v x : v.adicCompletion F) else 1) := rfl
      rw [heval]
      by_cases h : v ∈ T <;> simp [h]

private theorem conductor_ideleSupportTrunc_coe (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T) := by
  apply Prod.ext
  · funext w
    exact conductor_ideleSupportTrunc_infiniteCoord x T w
  · apply DFunLike.ext
    intro v
    exact conductor_ideleSupportTrunc_finiteCoord x T v

private theorem conductor_finiteSupportTrunc_tendsto (x : IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => conductor_finiteSupportTrunc x T)
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
  exact conductor_rp_truncate (hA := fun v => by simp)
    ((x : AdeleRing (𝓞 F) F).2)

private theorem conductor_ideleSupportTrunc_inv (x : IdeleGroup (𝓞 F) F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    (conductor_ideleSupportTrunc x T)⁻¹ = conductor_ideleSupportTrunc x⁻¹ T := by
  classical
  simp [conductor_ideleSupportTrunc, map_inv, Finset.prod_inv_distrib]
  ac_rfl

private theorem conductor_ideleSupportTrunc_coe_tendsto (x : IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F))) := by
  have hprod : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T)) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2)) :=
    (Prod.tendsto_iff _ _).2 ⟨tendsto_const_nhds, conductor_finiteSupportTrunc_tendsto x⟩
  have hfun : (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F)) =
      fun T => ((x : AdeleRing (𝓞 F) F).1, conductor_finiteSupportTrunc x T) := by
    funext T
    exact conductor_ideleSupportTrunc_coe x T
  rw [hfun]
  have hxpair : (x : AdeleRing (𝓞 F) F) =
      ((x : AdeleRing (𝓞 F) F).1, (x : AdeleRing (𝓞 F) F).2) := by
    cases x
    rfl
  rw [hxpair]
  exact hprod

private theorem conductor_tendsto_ideleSupportTrunc (x : IdeleGroup (𝓞 F) F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => conductor_ideleSupportTrunc x T)
      atTop (𝓝 x) := by
  classical
  have hval := conductor_ideleSupportTrunc_coe_tendsto x
  have hvalInv : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (((conductor_ideleSupportTrunc x T)⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))
      atTop (𝓝 ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)) := by
    simpa only [conductor_ideleSupportTrunc_inv] using
      conductor_ideleSupportTrunc_coe_tendsto (x⁻¹)
  have hvalInvOp : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      MulOpposite.op (((conductor_ideleSupportTrunc x T)⁻¹ : IdeleGroup (𝓞 F) F) :
        AdeleRing (𝓞 F) F)) atTop
      (𝓝 (MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F))) :=
    (MulOpposite.opHomeomorph.continuous.tendsto
      ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)).comp hvalInv
  have hEmbed : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      Units.embedProduct (AdeleRing (𝓞 F) F) (conductor_ideleSupportTrunc x T)) atTop
      (𝓝 (Units.embedProduct (AdeleRing (𝓞 F) F) x)) := by
    change Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      ((conductor_ideleSupportTrunc x T : AdeleRing (𝓞 F) F),
        MulOpposite.op (((conductor_ideleSupportTrunc x T)⁻¹ : IdeleGroup (𝓞 F) F) :
          AdeleRing (𝓞 F) F))) atTop
      (𝓝 ((x : AdeleRing (𝓞 F) F),
        MulOpposite.op ((x⁻¹ : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F)))
    rw [Prod.tendsto_iff]
    exact ⟨hval, hvalInvOp⟩
  exact Units.isEmbedding_embedProduct.tendsto_nhds_iff.mpr hEmbed

private theorem conductor_heckeChar_idealValue_eq_LS_of_gen
    (D : FieldData F) (S : SData F CE condη) (χ : HeckeChar F)
    (hχ : ∀ v : FinPlace F, v ∉ S.Sf → χ.UnramifiedAt v)
    (I : Ideal (𝓞 F)) (a : Fˣ) (ha : S.IsGen (a : F) I) :
    χ.idealValue I = S.LS χ (S.diagU a) := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := S.Sf ∪ conductor_factorPlaces I
  let x : IdeleGroup (𝓞 F) F := IdeleGroup.unitEmbedding (𝓞 F) F a
  let q : IdeleGroup (𝓞 F) F →* IdeleClassGroup (𝓞 F) F :=
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let ψ : IdeleGroup (𝓞 F) F →* ℂˣ :=
    (χ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp q
  let locLocal (v : FinPlace F) : ℂˣ := χ.loc v (toLoc v a)
  let infLocal (w : InfinitePlace F) : ℂˣ :=
    χ.locInf w (Dictionary.ideleInfiniteCoordUnit w x)
  let finS : ℂˣ := ∏ v : S.Sf, locLocal v.1
  let infS : ℂˣ := ∏ w : InfinitePlace F, infLocal w
  let factorLocal : ℂˣ :=
    ∏ v ∈ conductor_factorPlaces I,
      χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I
  have hprincipalClass : q x = 1 := by
    change (x : IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F) = 1
    exact (QuotientGroup.eq_one_iff
      (N := IdeleGroup.principalSubgroup (𝓞 F) F) x).mpr (by
        change x ∈ (IdeleGroup.unitEmbedding (𝓞 F) F).range
        exact ⟨a, rfl⟩)
  have hprincipal : ψ x = 1 := by
    change χ (q x) = 1
    rw [hprincipalClass, map_one]
  have hψcont : Continuous (fun z : IdeleGroup (𝓞 F) F => ψ z) := by
    dsimp [ψ, q]
    exact χ.continuous.comp continuous_quotient_mk'
  have hcoord : ∀ v : FinPlace F,
      Dictionary.ideleFiniteCoord v x = toLoc v a := by
    intro v
    apply Units.ext
    rfl
  have hEval (U : Finset (HeightOneSpectrum (𝓞 F))) :
      ψ (conductor_ideleSupportTrunc x U) =
        (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
    calc
      ψ (conductor_ideleSupportTrunc x U) =
          ψ ((∏ w ∈ Finset.univ,
            IdeleGroup.ofCompletion (𝓞 F) F w
              (Dictionary.ideleInfiniteCoordUnit w x)) *
            ∏ v ∈ U, IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (Dictionary.ideleFiniteCoord v x)) := rfl
      _ = ψ (∏ w ∈ Finset.univ,
            IdeleGroup.ofCompletion (𝓞 F) F w
              (Dictionary.ideleInfiniteCoordUnit w x)) *
          ψ (∏ v ∈ U, IdeleGroup.ofAdicCompletion (𝓞 F) F v
              (Dictionary.ideleFiniteCoord v x)) := map_mul ψ _ _
      _ = (∏ w : InfinitePlace F, infLocal w) *
          ∏ v ∈ U, χ.loc v (Dictionary.ideleFiniteCoord v x) := by
            rw [map_prod, map_prod]
            rfl
      _ = (∏ w : InfinitePlace F, infLocal w) * ∏ v ∈ U, locLocal v := by
            apply congrArg (fun z : ℂˣ => (∏ w : InfinitePlace F, infLocal w) * z)
            apply Finset.prod_congr rfl
            intro v hv
            rw [hcoord v]
  have htruncLimit : Tendsto (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
      ψ (conductor_ideleSupportTrunc x U)) atTop (𝓝 (1 : ℂˣ)) := by
    have hlim := hψcont.continuousAt.tendsto.comp
      (conductor_tendsto_ideleSupportTrunc x)
    have hfun : ((fun z => ψ z) ∘ fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        conductor_ideleSupportTrunc x U) = fun U => ψ (conductor_ideleSupportTrunc x U) := by
      funext U
      rfl
    rw [hfun] at hlim
    simpa [hprincipal] using hlim
  have hlocOne (v : FinPlace F) (hv : v ∉ T) : locLocal v = 1 := by
    have hvS : v ∉ S.Sf := by
      intro h
      exact hv (Finset.mem_union_left _ h)
    have hvF : v ∉ conductor_factorPlaces I := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hexp := conductor_exp_zero_of_not_factor I ha.1.1 v hvF
    have hloc := conductor_loc_gen_factor_unit S χ hχ I a ha v hvS
    simpa [locLocal, hexp] using hloc
  have hprodEventually :
      (fun U : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (conductor_ideleSupportTrunc x U)) =ᶠ[atTop]
        fun _ => ψ (conductor_ideleSupportTrunc x T) := by
    filter_upwards [eventually_atTop.2 ⟨T, fun U hTU => hTU⟩] with U hTU
    have hlocalProd : (∏ v ∈ U, locLocal v) = ∏ v ∈ T, locLocal v :=
      (Finset.prod_subset hTU (fun v hvU hvT => hlocOne v hvT)).symm
    rw [hEval U, hEval T, hlocalProd]
  have htruncOne : ψ (conductor_ideleSupportTrunc x T) = 1 := by
    have hconst : Tendsto (fun _ : Finset (HeightOneSpectrum (𝓞 F)) =>
        ψ (conductor_ideleSupportTrunc x T)) atTop (𝓝 (1 : ℂˣ)) :=
      htruncLimit.congr' hprodEventually
    exact (tendsto_nhds_unique hconst tendsto_const_nhds).symm
  have hdisj : Disjoint S.Sf (conductor_factorPlaces I) := by
    rw [Finset.disjoint_left]
    intro v hvS hvF
    have hdvd := conductor_factorPlaces_dvd I v hvF
    exact (ha.1.2 v hvS) (Ideal.le_of_dvd hdvd)
  have hfactorGenerator :
      (∏ v ∈ conductor_factorPlaces I, locLocal v) = factorLocal := by
    apply Finset.prod_congr rfl
    intro v hvF
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (conductor_factorPlaces_dvd I v hvF))
    exact conductor_loc_gen_factor_unit S χ hχ I a ha v hvS
  have htruncProduct : infS * finS * factorLocal = 1 := by
    have h := htruncOne
    rw [hEval T] at h
    change (∏ w : InfinitePlace F, infLocal w) *
      (∏ v ∈ T, locLocal v) = 1 at h
    rw [show T = S.Sf ∪ conductor_factorPlaces I by rfl,
      Finset.prod_union hdisj, hfactorGenerator] at h
    have hattach : (∏ v ∈ S.Sf, locLocal v) = finS :=
      (Finset.prod_attach S.Sf locLocal).symm
    rw [hattach] at h
    change infS * (finS * factorLocal) = 1 at h
    simpa [mul_assoc] using h
  have hfactorSupport : Function.mulSupport
      (fun v : FinPlace F => χ.primeValue v ^ idealExp v I) ⊆ conductor_factorPlaces I := by
    intro v hv
    change χ.primeValue v ^ idealExp v I ≠ 1 at hv
    by_contra hnot
    have hexp := conductor_exp_zero_of_not_factor I ha.1.1 v hnot
    simp [hexp] at hv
  have hprimeValue (v : FinPlace F) (hvF : v ∈ conductor_factorPlaces I) :
      χ.primeValue v =
        ((χ.loc v (toLoc v
          (Units.mk0 (unif v) (unif_ne_zero v))) : ℂˣ) : ℂ) := by
    have hvS : v ∉ S.Sf := by
      intro hv
      exact (ha.1.2 v hv) (Ideal.le_of_dvd (conductor_factorPlaces_dvd I v hvF))
    simp [HeckeChar.primeValue, hχ v hvS]
  have hidealValue : χ.idealValue I = (factorLocal : ℂ) := by
    rw [conductor_idealValue_finprod χ I ha.1.1]
    rw [finprod_eq_prod_of_mulSupport_subset _ hfactorSupport]
    change (∏ v ∈ conductor_factorPlaces I,
      χ.primeValue v ^ idealExp v I) = (factorLocal : ℂ)
    calc
      _ = ∏ v ∈ conductor_factorPlaces I,
          ((χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^
              idealExp v I : ℂˣ) : ℂ) := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [hprimeValue v hv]
          simp [Units.val_pow_eq_pow_val]
      _ = (factorLocal : ℂ) := by
          dsimp [factorLocal]
          exact (conductor_units_val_prod (conductor_factorPlaces I)
            (fun v : FinPlace F =>
              χ.loc v (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))) ^ idealExp v I)).symm
  have hcompU (v : S.Sf) : S.compU v (S.diagU a) = toLoc v.1 a := by
    ext
    rfl
  have hcompC (w : InfinitePlace F) (hw : w.IsComplex) :
      Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
          (S.compC w (S.diagU a)) =
        Dictionary.ideleInfiniteCoordUnit w x :=
    conductor_idele_inf_comp D S a w
  have hLS : S.LS χ (S.diagU a) = ((finS⁻¹ * infS⁻¹ : ℂˣ) : ℂ) := by
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
      have hcomp : complexComp w hw = Dictionary.ideleInfiniteCoordUnit w x := hcompC w hw
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
          rw [← conductor_units_val_prod Finset.univ (fun w => (infLocal w)⁻¹)]
        _ = ((infS⁻¹ : ℂˣ) : ℂ) := by simp [infS, Finset.prod_inv_distrib]
    unfold SData.LS
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

private theorem hecke_locInf_eq_one_of_finite_order
    (D : FieldData F) (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (w : InfinitePlace F) (z : ℂˣ) :
    χ.locInf w
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) = 1 := by
  classical
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hχ
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  let eh := InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)
  let toCompletion : ℂˣ → w.Completionˣ := Units.map e.symm.toMonoidHom
  let f : ℂˣ → ℂˣ := fun x => χ.locInf w (toCompletion x)
  have htoCompletion : Continuous toCompletion := by
    apply Units.continuous_iff.mpr
    change Continuous (fun x : ℂˣ => e.symm (x : ℂ)) ∧
      Continuous (fun x : ℂˣ => e.symm (((x⁻¹ : ℂˣ) : ℂ)))
    exact ⟨(eh.symm.isometry_toFun.continuous).comp Units.continuous_val,
      (eh.symm.isometry_toFun.continuous).comp Units.continuous_coe_inv⟩
  have hloc : Continuous (χ.locInf w) := by
    change Continuous (fun u : w.Completionˣ =>
      χ (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
    exact χ.continuous.comp (IdeleClassGroup.continuous_ofCompletion (𝓞 F) F w)
  have hf : Continuous f := hloc.comp htoCompletion
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hroot : (Set.univ : Set (rootsOfUnity n ℂ)).Finite := Set.finite_univ
  let T : Set ℂˣ := (fun x : rootsOfUnity n ℂ => (x : ℂˣ)) '' Set.univ
  have hT : T.Finite := hroot.image _
  have hTdisc : IsDiscrete T := hT.isDiscrete
  have hpoint (x : ℂˣ) : f x ^ n = 1 := by
    have heval := congrArg (fun ψ : HeckeChar F => ψ
      (IdeleClassGroup.ofCompletion (𝓞 F) F w (toCompletion x))) hpow
    simpa [f, HeckeChar.locInf] using heval
  have hmaps : Set.MapsTo f Set.univ T := by
    intro x _
    change f x ∈ (fun y : rootsOfUnity n ℂ => (y : ℂˣ)) '' Set.univ
    exact ⟨⟨f x, hpoint x⟩, Set.mem_univ _, rfl⟩
  have hconst : f z = f 1 :=
    (isPreconnected_univ : IsPreconnected (Set.univ : Set ℂˣ)).constant_of_mapsTo
      hTdisc hf.continuousOn hmaps (Set.mem_univ z) (Set.mem_univ 1)
  simpa [f, toCompletion] using hconst

/-- eq:vartheta-s (02:615–625): `ϑ(𝔞) = L_S(a)` for every generator, `L_S = 1` on `U_S`, angular
type `±1` at complex places, and `γ_1γ_2ϑ = -η` at exterior primes. Package P-ARITH-GAUSS.
Corrected per rev-theta to require the finite-order and angular hypotheses used by the lemma; C5 of
`sol-gate-theta` also requires the three characters to be unramified outside `S`. -/
theorem vartheta_S (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (η Λ G : HeckeChar F)
    (hηram : ∀ v : FinPlace F, v ∉ S.Sf → η.UnramifiedAt v)
    (hΛram : ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v)
    (hGram : ∀ v : FinPlace F, v ∉ S.Sf → G.UnramifiedAt v)
    (hη : IsOfFinOrder η) (hG : IsOfFinOrder G)
    (hΛunitary : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hΛangular : HeckeChar.HasAngularType D Λ)
    (hΛG : ∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
        -(Λ.primeValue v * G.primeValue v)) :
    (∀ (I : Ideal (𝓞 F)) (a : Fˣ), S.IsExterior I → S.IsGen (a : F) I →
      (vartheta Λ G η).idealValue I = S.LS (vartheta Λ G η) (S.diagU a)) ∧
    (∀ ε ∈ S.US, S.LS (vartheta Λ G η) (S.diagU ε) = 1) ∧
    (∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      S.LS (vartheta Λ G η) (S.atComplex w z) = ((z : ℂ) / ‖(z : ℂ)‖) ^ m) ∧
    (∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
      gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p * (vartheta Λ G η).primeValue v =
        -η.primeValue v) := by
  classical
  have hvarthetaRam : ∀ v : FinPlace F, v ∉ S.Sf → (vartheta Λ G η).UnramifiedAt v := by
    intro v hv u hu huinv
    change (Λ.loc v u)⁻¹ * (G.loc v u)⁻¹ * η.loc v u = 1
    rw [hΛram v hv u hu huinv, hGram v hv u hu huinv, hηram v hv u hu huinv]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I a hI ha
    exact conductor_heckeChar_idealValue_eq_LS_of_gen D S (vartheta Λ G η)
      hvarthetaRam I a ha
  · intro ε hε
    let εUS : S.US := ⟨ε, hε⟩
    have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
      refine ⟨top_ne_bot, ?_⟩
      intro v hv hle
      exact v.isPrime.ne_top (top_le_iff.mp hle)
    have hgen : S.IsGen ((ε : Fˣ) : F) ⊤ := by
      refine ⟨htop, Units.ne_zero (ε : Fˣ), ?_⟩
      intro v hv
      have hval : HeightOneSpectrum.valuation F v ((ε : Fˣ) : F) = 1 :=
        εUS.property v hv
      rw [ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
        v ((ε : Fˣ) : F) (Units.ne_zero (ε : Fˣ)), hval]
      simpa using (FractionalIdeal.count_one F v).symm
    have hLS := conductor_heckeChar_idealValue_eq_LS_of_gen D S
      (vartheta Λ G η) hvarthetaRam ⊤ (ε : Fˣ) hgen
    have htop1 : (⊤ : Ideal (𝓞 F)) = 1 := by
      ext x
      simp
    have htopValue : (vartheta Λ G η).idealValue ⊤ = 1 := by
      unfold HeckeChar.idealValue
      have hnorm : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
        calc
          UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) =
              UniqueFactorizationMonoid.normalizedFactors (1 : Ideal (𝓞 F)) :=
                congrArg UniqueFactorizationMonoid.normalizedFactors htop1
          _ = 0 := UniqueFactorizationMonoid.normalizedFactors_one
      rw [hnorm]
      simp
    calc
      S.LS (vartheta Λ G η) (S.diagU ε) = (vartheta Λ G η).idealValue ⊤ := hLS.symm
      _ = 1 := htopValue
  · intro w
    obtain ⟨m, hm, hangular⟩ := hΛangular w
    refine ⟨m, hm, ?_⟩
    intro z
    let hw : w.IsComplex := D.isTotallyComplex.isComplex w
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hcompU (v : S.Sf) : S.compU v (S.atComplex w z) = 1 := by
      apply Units.ext
      rfl
    have hcompC (w' : InfinitePlace F) :
        S.compC w' (S.atComplex w z) = if w' = w then z else 1 := by
      by_cases h : w' = w
      · subst w'
        apply Units.ext
        simp [SData.compC, SData.atComplex]
      · apply Units.ext
        simp [SData.compC, SData.atComplex, h]
    have hfinite :
        (∏ v : S.Sf,
          (((((vartheta Λ G η).loc v.1 (S.compU v (S.atComplex w z)))⁻¹ : ℂˣ) : ℂ))) = 1 := by
      simp [hcompU]
    let zc : w.Completionˣ := Units.map e.symm.toMonoidHom z
    let localAt (w' : InfinitePlace F) (hw' : w'.IsComplex) : ℂˣ :=
      (vartheta Λ G η).locInf w'
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm.toMonoidHom
          (S.compC w' (S.atComplex w z)))
    have hterm (w' : InfinitePlace F) :
        (if hw' : w'.IsComplex then
          (((localAt w' hw')⁻¹ : ℂˣ) : ℂ) else 1) =
          if w' = w then ((Λ.locInf w zc : ℂˣ) : ℂ) else 1 := by
      let hw' : w'.IsComplex := D.isTotallyComplex.isComplex w'
      rw [dif_pos hw']
      by_cases h : w' = w
      · subst w'
        have hηloc := hecke_locInf_eq_one_of_finite_order D η hη w z
        have hGloc := hecke_locInf_eq_one_of_finite_order D G hG w z
        have hηval : η (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) = 1 := by
          change η.locInf w zc = 1
          exact hηloc
        have hGval : G (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) = 1 := by
          change G.locInf w zc = 1
          exact hGloc
        have hθloc : (vartheta Λ G η).locInf w zc = (Λ.locInf w zc)⁻¹ := by
          change (Λ (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹ *
            (G (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹ *
            η (IdeleClassGroup.ofCompletion (𝓞 F) F w zc) =
              (Λ (IdeleClassGroup.ofCompletion (𝓞 F) F w zc))⁻¹
          rw [hηval, hGval]
          simp
        have hlocal : localAt w hw = (Λ.locInf w zc)⁻¹ := by
          dsimp [localAt]
          rw [hcompC]
          simpa [zc] using hθloc
        simp [hlocal]
      · have hz1 : S.compC w' (S.atComplex w z) = 1 := by
          rw [hcompC]
          simp [h]
        have hlocal : localAt w' hw' = 1 := by
          dsimp [localAt]
          rw [hcompC]
          simp [h, hz1]
        simp [h, hlocal]
    have hinfinite :
        (∏ w' : InfinitePlace F,
          if hw' : w'.IsComplex then
            (((localAt w' hw')⁻¹ : ℂˣ) : ℂ) else 1) =
          ((Λ.locInf w zc : ℂˣ) : ℂ) := by
      calc
        _ = ∏ w' : InfinitePlace F, (if w' = w then ((Λ.locInf w zc : ℂˣ) : ℂ) else 1) :=
          Finset.prod_congr rfl (fun w' _ => hterm w')
        _ = ((Λ.locInf w zc : ℂˣ) : ℂ) := by
          rw [Finset.prod_eq_single w]
          · simp
          · intro w' hw' hne
            simp [hne]
          · simp
    unfold SData.LS
    rw [hfinite, hinfinite, one_mul]
    exact hangular z
  · intro v hv p hpgen hpAllowed
    let π : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))
    have hloc : (vartheta Λ G η).loc v π =
        (Λ.loc v π)⁻¹ * (G.loc v π)⁻¹ * η.loc v π := by
      let y := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
      have hinv (χ : HeckeChar F) : χ⁻¹ y = (χ y)⁻¹ := rfl
      change (Λ⁻¹ * G⁻¹ * η)
          (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π) =
        (Λ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))⁻¹ *
          (G (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))⁻¹ *
            η (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π)
      rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.mul_apply,
        hinv Λ, hinv G]
    have hΛpv : Λ.primeValue v = ((Λ.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hΛram v hv]
    have hGpv : G.primeValue v = ((G.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hGram v hv]
    have hηpv : η.primeValue v = ((η.loc v π : ℂˣ) : ℂ) := by
      simp [HeckeChar.primeValue, π, hηram v hv]
    have hprime : (vartheta Λ G η).primeValue v =
        (Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v := by
      change (if (vartheta Λ G η).UnramifiedAt v then
        (((vartheta Λ G η).loc v π : ℂˣ) : ℂ) else 0) = _
      rw [if_pos (hvarthetaRam v hv), hloc, hΛpv, hGpv, hηpv]
      simp [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev]
      ring
    have hΛne : Λ.primeValue v ≠ 0 := by
      rw [HeckeChar.primeValue, if_pos (hΛram v hv)]
      exact Units.ne_zero _
    have hGne : G.primeValue v ≠ 0 := by
      rw [HeckeChar.primeValue, if_pos (hGram v hv)]
      exact Units.ne_zero _
    rw [hprime, hΛG v hv p hpgen hpAllowed]
    change -(Λ.primeValue v * G.primeValue v) *
      ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v) = -η.primeValue v
    calc
      -(Λ.primeValue v * G.primeValue v) *
          ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v) =
        -((Λ.primeValue v * G.primeValue v) *
          ((Λ.primeValue v * G.primeValue v)⁻¹ * η.primeValue v)) := by simp
      _ = -η.primeValue v := by simp [mul_assoc, hΛne, hGne]


end ArtinPrimitiveRoots.A1
