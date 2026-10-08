import ArtinPrimitiveRoots.A1.AddChar

/-! Helper interfaces below `Characters`, avoiding an import cycle. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

abbrev KummerChar (F : Type) [Field F] [NumberField F] :=
  ContinuousMonoidHom (IdeleClassGroup (𝓞 F) F) ℂˣ

def localComponent (κ : KummerChar F) (P : FinPlace F) :
    (P.adicCompletion F)ˣ →* ℂˣ :=
  (κ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp
    (IdeleClassGroup.ofAdicCompletion (𝓞 F) F P)

def infiniteComponent (κ : KummerChar F) (w : InfinitePlace F) :
    w.Completionˣ →* ℂˣ :=
  (κ : IdeleClassGroup (𝓞 F) F →* ℂˣ).comp
    (IdeleClassGroup.ofCompletion (𝓞 F) F w)

def unramifiedAt (κ : KummerChar F) (P : FinPlace F) : Prop :=
  ∀ x : (P.adicCompletion F)ˣ, (x : P.adicCompletion F) ∈ P.adicCompletionIntegers F →
    ((x⁻¹ : (P.adicCompletion F)ˣ) : P.adicCompletion F) ∈ P.adicCompletionIntegers F →
      localComponent κ P x = 1

def uniformizer (P : FinPlace F) : F :=
  (HeightOneSpectrum.valuation_exists_uniformizer F P).choose

def uniformizerUnit (P : FinPlace F) : Fˣ :=
  Units.mk0 (uniformizer P) (by
    intro h
    have hv := (HeightOneSpectrum.valuation_exists_uniformizer F P).choose_spec
    rw [← uniformizer, h, map_zero] at hv
    exact WithZero.zero_ne_coe hv)

def primeValue (κ : KummerChar F) (P : FinPlace F) : ℂ :=
  if unramifiedAt κ P then
    ((localComponent κ P (toLoc P (uniformizerUnit P)) : ℂˣ) : ℂ) else 0

/-- Read the sextic Hilbert value through the fixed embedding. -/
def kummerLocal (D : FieldData F) (H : HilbertData F)
    (P : FinPlace F) (a : (P.adicCompletion F)ˣ) : (P.adicCompletion F)ˣ →* ℂˣ :=
  (Units.map D.σ0.toMonoidHom).comp
    ((rootsOfUnity 6 F).subtype.comp
      (MonoidHom.mk' (fun x => H.hilb P a x) (fun x y => H.mul_right P a x y)))

end ArtinPrimitiveRoots.A1.KummerProofs
