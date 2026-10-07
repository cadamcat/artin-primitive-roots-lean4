import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.Hecke.Defs
import OAI.NumberTheory.DirichletL.FiniteFourier

/-! Exact ideal, local-component, and residue objects for the conductor sieve.
The infinite components use the actual completions, including real places. -/

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **ext:primitive-conductor** (06-zero-free.tex:37-73): a modulus of least norm on which the
idelic character is trivial in A1's local congruence sense. Corrected per rev-a2 to exclude the
zero ideal from the minimization. -/
def IsPrimitiveConductor (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (𝔣 : Ideal (𝓞 F)) : Prop :=
  𝔣 ≠ ⊥ ∧ χ.ConductorDvd 𝔣 ∧
    ∀ 𝔤 : Ideal (𝓞 F), 𝔤 ≠ ⊥ → χ.ConductorDvd 𝔤 →
      Ideal.absNorm 𝔣 ≤ Ideal.absNorm 𝔤

/-- The finite-place local components at a fixed finite set `S`. -/
abbrev SLocalCharacter (S : ArtinPrimitiveRoots.A1.SData F CE condη) :=
  ∀ v : S.Sf, (v.1.adicCompletion F)ˣ →* ℂˣ

/-- Restriction of an idelic Hecke character to the fixed finite places in `S`. -/
def SComponent (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) : SLocalCharacter S :=
  fun v => χ.loc v.1

/-- The exact finite norm cutoff, including the bottom ideal. -/
abbrev conductorIdealCutoff (F : Type) [Field F] [NumberField F] (N : ℝ) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).toFinset

/-- Prime factors supported at the fixed finite set S. -/
def conductorSPart (S : A1.SData F CE condη) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((UniqueFactorizationMonoid.normalizedFactors I).filter
    (fun P => ∃ v ∈ S.Sf, P = v.asIdeal)).prod

/-- Prime factors outside the fixed finite set S. -/
def conductorExteriorPart (S : A1.SData F CE condη) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ((UniqueFactorizationMonoid.normalizedFactors I).filter
    (fun P => ¬ ∃ v ∈ S.Sf, P = v.asIdeal)).prod

/-- Nonzero ideals whose prime divisors lie in S. -/
def ConductorSupportedAtS (S : A1.SData F CE condη) (J : Ideal (𝓞 F)) : Prop :=
  J ≠ ⊥ ∧ ∀ v : A1.FinPlace F, v.asIdeal ∣ J → v ∈ S.Sf

/-- The S-pieces occurring in the nonzero finite norm cutoff. -/
def conductorSPieces (S : A1.SData F CE condη) (N : ℝ) : Finset (Ideal (𝓞 F)) :=
  ((conductorIdealCutoff F N).filter (fun I => I ≠ ⊥)).image (conductorSPart S)

/-- The exact finite exterior norm cutoff. -/
def conductorExteriorCutoff (S : A1.SData F CE condη) (N : ℝ) : Finset S.ExtIdeal :=
  let B := (conductorIdealCutoff F N).filter S.IsExterior
  B.attach.map
    { toFun := fun I : { I : Ideal (𝓞 F) // I ∈ B } =>
        (⟨I.1, (Finset.mem_filter.mp I.2).2⟩ : S.ExtIdeal)
      inj' := by
        intro I J h
        apply Subtype.ext
        exact congrArg (fun x : S.ExtIdeal => x.1) h }

/-- Dyads also cover norm one: the first dyad starts at T=1. -/
def conductorExteriorDyad (S : A1.SData F CE condη) (T : ℝ) : Finset S.ExtIdeal :=
  (conductorExteriorCutoff S (2 * T)).filter (fun I => T ≤ idealNorm I.1)

/-- All infinite local components, retaining real-place signs. -/
abbrev ConductorInfiniteLocal (F : Type) [Field F] [NumberField F] :=
  ∀ w : InfinitePlace F, w.Completionˣ →* ℂˣ

/-- Restriction to all infinite local components. -/
def conductorInfiniteComponent (ω : A1.HeckeChar F) : ConductorInfiniteLocal F :=
  fun w => ω.locInf w

/-- The common inverse local factor dictated by the rational-idele relation. -/
def conductorLambdaS (S : A1.SData F CE condη) (ℓ : SLocalCharacter S)
    (τ : ConductorInfiniteLocal F) (a : Fˣ) : ℂ :=
  ((∏ v : S.Sf, ℓ v (Units.map
    (algebraMap F (v.1.adicCompletion F)).toMonoidHom a)) *
    (∏ w : InfinitePlace F, τ w (Units.map
      (algebraMap F w.Completion).toMonoidHom a)) : ℂˣ)⁻¹

/-- Generators balanced in the actual local absolute values. Unlike BalancedChoices,
this object is meaningful for every number field, with real archimedean weight one.
Only upper bounds are needed to place a dyad in a fixed compact box. -/
structure ConductorGenerators (S : A1.SData F CE condη) where
  gen : S.ExtIdeal → S.R
  generates : ∀ I, S.IsGen (gen I : F) I.1
  height : ℝ
  height_pos : 0 < height
  finite_bound : ∀ I (v : S.Sf),
    A1.absFin v.1 (algebraMap F (v.1.adicCompletion F) (gen I : F)) ≤ height
  infinite_bound : ∀ I (w : InfinitePlace F),
    ‖w.embedding (gen I : F)‖ ≤ height *
      Real.rpow (idealNorm I.1) (1 / (Module.finrank ℚ F : ℝ))

/-- A generator as a unit of the number field. -/
def ConductorGenerators.unit {S : A1.SData F CE condη}
    (G : ConductorGenerators S) (I : S.ExtIdeal) : Fˣ :=
  Units.mk0 (G.gen I : F) (G.generates I).2.1

/-- The ordinary integral residue ring, with S-integers mapped into it below. -/
abbrev ConductorResidueRing {S : A1.SData F CE condη} (q : S.ExtIdeal) := 𝓞 F ⧸ q.1

instance conductorResidueFinite {S : A1.SData F CE condη} (q : S.ExtIdeal) :
    Finite (ConductorResidueRing q) := by
  letI : NeZero q.1 := ⟨q.2.1⟩
  infer_instance

instance conductorResidueFintype {S : A1.SData F CE condη} (q : S.ExtIdeal) :
    Fintype (ConductorResidueRing q) := Fintype.ofFinite _

/-- Exact localization comparison with O_F/q, including the unit ideal. -/
structure ConductorResidues (S : A1.SData F CE condη) where
  red : ∀ q : S.ExtIdeal, S.R →+* ConductorResidueRing q
  integral : ∀ q (a : 𝓞 F),
    red q (algebraMap (𝓞 F) S.R a) = Ideal.Quotient.mk q.1 a
  ker : ∀ q, RingHom.ker (red q) = Ideal.map (algebraMap (𝓞 F) S.R) q.1
  surjective : ∀ q, Function.Surjective (red q)

/-- A primitive additive character on every exact residue ring. All choices of such
characters give the same sum over units, so no arbitrary Fourier phases enter the estimate. -/
structure ConductorAdditiveCharacters (S : A1.SData F CE condη) where
  ψ : ∀ q : S.ExtIdeal, AddChar (ConductorResidueRing q) ℂ
  primitive : ∀ q, (ψ q).IsPrimitive

/-- The character-family hypotheses of the frozen conductor sieve. -/
def ConductorFamily (S : A1.SData F CE condη) (C₀ U : ℝ)
    (𝓛S : Finset (SLocalCharacter S)) (𝓧 : Finset (A1.HeckeChar F)) : Prop :=
  ∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U

/-- A single finite/infinite local-component group. -/
def ConductorGroup (S : A1.SData F CE condη) (C₀ U : ℝ)
    (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (𝓧 : Finset (A1.HeckeChar F)) : Prop :=
  ∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω = ℓ ∧
    conductorInfiniteComponent ω = τ ∧
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U

/-- Exact residue realization for a fixed local group. -/
def ConductorResidueRealizes (S : A1.SData F CE condη) (G : ConductorGenerators S)
    (ρ : ConductorResidues S) (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    (q : S.ExtIdeal) (lambdaq : MulChar (ConductorResidueRing q) ℂ)
    (ω : A1.HeckeChar F) : Prop :=
  ∀ I : S.ExtIdeal, ω.idealValue I.1 =
    conductorLambdaS S ℓ τ (G.unit I) * lambdaq (ρ.red q (G.gen I))

end ArtinPrimitiveRoots.A2
