import ArtinPrimitiveRoots.A1.AddChar

/-!
# A1 interface, §5: Hecke, Kummer, class and Gauss correction characters

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

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

/-- A modulus bound for the conductor: `χ` is trivial on `1 + 𝔪O_v` at every finite `v` and on
the units at `v ∤ 𝔪` (then the conductor divides `𝔪`). -/
def HeckeChar.ConductorDvd (χ : HeckeChar F) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ v : FinPlace F, ∀ u : (v.adicCompletion F)ˣ,
    (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    (∀ x ∈ 𝔪, Valued.v ((u : v.adicCompletion F) - 1) ≤
      Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F x))) →
    χ.loc v u = 1

/-- Kummer character `κ_u` (ar:kummer-hecke, 02:285–357): finite order, unramified at exterior
`v` with `v(u) = 0`, and `κ_u(v) = χ_v(u)` there. Package P-ARITH-KUMMER. -/
theorem kummer_exists (D : FieldData F) (S : SData F CE condη) (u : Fˣ) :
    ∃ κ : HeckeChar F, IsOfFinOrder κ ∧ ∀ v : FinPlace F, v ∉ S.Sf → residue v (u : F) ≠ 0 →
      κ.UnramifiedAt v ∧ κ.primeValue v = chi D v (u : F) := by
  sorry

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
  sorry

/-- ar:B-character-extension (02:302–303, 359–366): every character of `B` evaluated on allowed
generators extends to a finite-order Hecke character unramified outside `S`. Package
P-ARITH-KUMMER. -/
theorem class_character_extension (D : FieldData F) (S : SData F CE condη) (H : HilbertData F)
    (Bd : BData S H) (θB : Bd.B →* ℂˣ) :
    ∃ θ : HeckeChar F, IsOfFinOrder θ ∧ (∀ v : FinPlace F, v ∉ S.Sf → θ.UnramifiedAt v) ∧
      ∀ (I : Ideal (𝓞 F)) (a : Fˣ), S.IsExterior I → S.IsGen (a : F) I → (ha : Bd.Allowed a) →
        θ.idealValue I = ((θB ⟨_, ha⟩ : ℂˣ) : ℂ) := by
  sorry

/-- lem:gauss-characters (02:411–436): `Λ` unitary, `G` finite order, both unramified at `v ∉ S`,
with `γ_2(𝔭)³ = -Λ(𝔭)`, `G(𝔭) = conj(χ_𝔭(4))γ_3(𝔭)`, `γ_1(𝔭)γ_2(𝔭) = -Λ(𝔭)G(𝔭)` for every exterior
prime and allowed generator. Package P-ARITH-GAUSS (Λ: P-ARITH-LAMBDA, G: P-WEIL). -/
theorem gauss_characters (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (H : HilbertData F) (Bd : BData S H) :
    ∃ Λ G : HeckeChar F, IsOfFinOrder G ∧
      (∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ v : FinPlace F, v ∉ S.Sf → Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
        ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
          gamma D S A 2 v.asIdeal p ^ 3 = -Λ.primeValue v ∧
          G.primeValue v = (starRingEnd ℂ) (chi D v 4) * gamma D S A 3 v.asIdeal p ∧
          gamma D S A 1 v.asIdeal p * gamma D S A 2 v.asIdeal p =
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

/-- eq:vartheta-s (02:615–625): `ϑ(𝔞) = L_S(a)` for every generator, `L_S = 1` on `U_S`, angular
type `±1` at complex places, and `γ_1γ_2ϑ = -η` at exterior primes. Package P-ARITH-GAUSS. -/
theorem vartheta_S (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (η Λ G : HeckeChar F)
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
  sorry


end ArtinPrimitiveRoots.A1
