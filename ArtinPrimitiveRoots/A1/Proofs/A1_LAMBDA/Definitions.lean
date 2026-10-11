import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Types
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.Gamma
import ArtinPrimitiveRoots.Hecke.Dict.IdeleCoordinates
import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius

/-! A1-LAMBDA interfaces below Characters.
The character abbreviations and angular condition unfold to the frozen bodies.
Eisenstein primary generators are reused from the prebuilt OAI IdealMobius module. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical Topology

noncomputable section

-- Preserve the cyclotomic instance used by the frozen Eisenstein interfaces.
attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open ArtinPrimitiveRoots.A1

abbrev E := OAI.ActualEisensteinCubic.K
abbrev OE := OAI.ActualEisensteinCubic.O
abbrev omega := OAI.ActualEisensteinCubic.omega
abbrev lambda := OAI.ActualEisensteinCubic.lambda
abbrev primary := OAI.CompletedGauss.primaryGenerator

abbrev LambdaChar (F : Type) [Field F] [NumberField F] := KummerProofs.KummerChar F
abbrev localComponent {F : Type} [Field F] [NumberField F] :=
  KummerProofs.localComponent (F := F)
abbrev infiniteComponent {F : Type} [Field F] [NumberField F] :=
  KummerProofs.infiniteComponent (F := F)
abbrev unramifiedAt {F : Type} [Field F] [NumberField F] :=
  KummerProofs.unramifiedAt (F := F)
abbrev primeValue {F : Type} [Field F] [NumberField F] :=
  KummerProofs.primeValue (F := F)

def unitary {F : Type} [Field F] [NumberField F] (χ : LambdaChar F) : Prop :=
  ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def localUnit {F : Type} [Field F] [NumberField F] (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ) : Prop :=
  (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
      v.adicCompletionIntegers F

def simpleAngularType {F : Type} [Field F] [NumberField F]
    (χ : LambdaChar F) : Prop :=
  ∀ (w : InfinitePlace F) (hw : w.IsComplex), ∃ m : ℤ,
    (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      ((infiniteComponent χ w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) :
          ℂˣ) : ℂ) = ((z : ℂ) / ‖(z : ℂ)‖) ^ m

def angularType {F : Type} [Field F] [NumberField F]
    (D : FieldData F) (χ : LambdaChar F) : Prop :=
  ∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
    ((infiniteComponent χ w (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) : ℂˣ) : ℂ) =
      ((z : ℂ) / ‖(z : ℂ)‖) ^ m

def integerEmbedding {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) : OE →+* 𝓞 F :=
  NumberField.RingOfIntegers.mapRingHom ι.toRingHom

def basePlace {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) : FinPlace E :=
  letI : Algebra E F := ι.toRingHom.toAlgebra
  v.under OE

theorem basePlace_asIdeal {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) :
    (basePlace ι v).asIdeal = Ideal.comap (integerEmbedding ι) v.asIdeal := rfl

def residueMap {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) :
    (OE ⧸ (basePlace ι v).asIdeal) →+* (𝓞 F ⧸ v.asIdeal) :=
  Ideal.quotientMap v.asIdeal (integerEmbedding ι) (by
    rw [basePlace_asIdeal])

def residueAlgebra {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) :
    Algebra (OE ⧸ (basePlace ι v).asIdeal) (𝓞 F ⧸ v.asIdeal) :=
  (residueMap ι v).toAlgebra

def residueDegree {F : Type} [Field F] [NumberField F]
    (ι : E →ₐ[ℚ] F) (v : FinPlace F) : ℕ :=
  letI := residueAlgebra ι v
  Module.finrank (OE ⧸ (basePlace ι v).asIdeal) (𝓞 F ⧸ v.asIdeal)

def complexEmbedding {F : Type} [Field F] [NumberField F]
    (D : FieldData F) (ι : E →ₐ[ℚ] F) : E →+* ℂ := D.σ0.comp ι.toRingHom

def integerComplex (σ : E →+* ℂ) : OE →+* ℂ :=
  σ.comp (algebraMap OE E)

def eisensteinPrimeValue (σ : E →+* ℂ) (v : FinPlace E) : ℂ :=
  integerComplex σ (primary v.asIdeal) / ‖integerComplex σ (primary v.asIdeal)‖

def baseCubicChar (σ : E →+* ℂ) (v : FinPlace E) (hv : lambda ∉ v.asIdeal) :
    MulChar (OE ⧸ v.asIdeal) ℂ :=
  letI : v.asIdeal.IsMaximal := v.isMaximal
  (OAI.ActualEisensteinCubic.cubicChar v.asIdeal hv).ringHomComp (integerComplex σ)

def normalizedJacobi {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (α : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) : ℂ :=
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) * jacobiSum α α

/-- Local characters with the restricted-product support and principal relation.
Uses: finite product continuity and character descent. Guide: 428-439. -/
structure LocalCharacterData (F : Type) [Field F] [NumberField F] where
  finite : ∀ v : FinPlace F, ContinuousMonoidHom (v.adicCompletion F)ˣ ℂˣ
  infinite : ∀ w : InfinitePlace F, ContinuousMonoidHom w.Completionˣ ℂˣ
  eventually_unit_trivial : ∀ᶠ v : FinPlace F in Filter.cofinite,
    ∀ u : (v.adicCompletion F)ˣ, localUnit v u → finite v u = 1
  finite_unitary : ∀ (v : FinPlace F) (u : (v.adicCompletion F)ˣ),
    ‖((finite v u : ℂˣ) : ℂ)‖ = 1
  infinite_unitary : ∀ (w : InfinitePlace F) (u : w.Completionˣ),
    ‖((infinite w u : ℂˣ) : ℂ)‖ = 1
  principal_product : ∀ a : Fˣ,
    (∏ w : InfinitePlace F, infinite w (Dictionary.ideleInfiniteCoordUnit w
      (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a))) *
      (∏ᶠ v : FinPlace F, finite v (toLoc v a)) = 1

/-- The base primary character's local data, including its exterior values.
Uses: base-character descent. Guide: 428-439. -/
structure BaseLocalData (σ : E →+* ℂ) extends LocalCharacterData E where
  exterior_units : ∀ v : FinPlace E, lambda ∉ v.asIdeal →
    ∀ u : (v.adicCompletion E)ˣ, localUnit v u → finite v u = 1
  prime_formula : ∀ v : FinPlace E, lambda ∉ v.asIdeal →
    ((finite v (toLoc v (KummerProofs.uniformizerUnit v)) : ℂˣ) : ℂ) =
      eisensteinPrimeValue σ v
  angular : ∀ (w : InfinitePlace E) (hw : w.IsComplex), ∃ m : ℤ,
    (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      ((infinite w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom z) :
          ℂˣ) : ℂ) = ((z : ℂ) / ‖(z : ℂ)‖) ^ m

/-- The relative norm before principal descent, with the local transport needed by Λ.
`principal_norm` specifies the global norm, and `uniformizer_norm` fixes its residue
degree normalization. The norm is built from completion norms. Guide: 428-439. -/
structure RelativeNormData {F : Type} [Field F] [NumberField F]
    (D : FieldData F) (ι : E →ₐ[ℚ] F) where
  norm : NumberField.IdeleGroup (𝓞 F) F →* NumberField.IdeleGroup OE E
  continuous_norm : Continuous norm
  principal_norm : ∀ a : Fˣ,
    letI : Algebra E F := ι.toRingHom.toAlgebra
    norm (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F a) =
      NumberField.IdeleGroup.unitEmbedding OE E (Units.map (Algebra.norm E) a)
  unit_norm : ∀ (v : FinPlace F) (u : (v.adicCompletion F)ˣ), localUnit v u →
    ∃ b : ((basePlace ι v).adicCompletion E)ˣ, localUnit (basePlace ι v) b ∧
      norm (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v u) =
        NumberField.IdeleGroup.ofAdicCompletion OE E (basePlace ι v) b
  uniformizer_norm : ∀ v : FinPlace F,
    ∃ b : ((basePlace ι v).adicCompletion E)ˣ, localUnit (basePlace ι v) b ∧
      norm (NumberField.IdeleGroup.ofAdicCompletion (𝓞 F) F v
        (toLoc v (KummerProofs.uniformizerUnit v))) =
      NumberField.IdeleGroup.ofAdicCompletion OE E (basePlace ι v)
        (toLoc (basePlace ι v) (KummerProofs.uniformizerUnit (basePlace ι v)) ^
          residueDegree ι v * b)
  angular_norm : ∀ χ : LambdaChar E, simpleAngularType χ →
    ∀ w : InfinitePlace F, ∃ m : ℤ, (m = 1 ∨ m = -1) ∧ ∀ z : ℂˣ,
      ((χ (QuotientGroup.mk (norm (NumberField.IdeleGroup.ofCompletion (𝓞 F) F w
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z)))) : ℂˣ) : ℂ) =
        ((z : ℂ) / ‖(z : ℂ)‖) ^ m

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
