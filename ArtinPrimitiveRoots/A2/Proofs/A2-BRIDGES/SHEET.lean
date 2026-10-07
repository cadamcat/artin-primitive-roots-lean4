import ArtinPrimitiveRoots.A2.Interface
import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».NORM

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη}
variable {μ : ∀ v : FinPlace F, Theta.LocHaar v} {v0 : InfinitePlace F}

/-- Translate the actual fundamental set. Definitionally equal to omegaAt R l for G=R.sheets.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses SheetGeometry, without importing its consumers. -/
def bridgeOmegaAt (G : SheetGeometry D S μ v0) (l : ℝ) : Set S.FS :=
  {y | ∃ x ∈ G.omega, y = (G.ellU l : S.FS) * x}

/-- Exact representative condition; definitionally equal to IsFundamentalAt in Reflection/Missing.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses Gamma and the actual diagonal action. -/
def bridgeFundamentalAt (S : SData F CE condη) (O : Set S.FS) (l : ℝ) : Prop :=
  MeasurableSet O ∧ (∀ y ∈ O, IsUnit y ∧ S.absS y = l) ∧
  ∀ y : S.FSˣ, S.absS (y : S.FS) = l →
    ∃! γ : Gamma S, ((S.diagU (γ.1 : Fˣ))⁻¹ * y : S.FSˣ).val ∈ O

/-- The actual sheet integral; definitionally equal to sheetIntegral R for G=R.sheets.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses Interface.onUnits. -/
def bridgeSheetIntegral (G : SheetGeometry D S μ v0) (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y, onUnits f y ∂(G.sheet l)

/-- Fundamental-set integral; definitionally equal to omegaInt R for G=R.sheets.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses bridgeOmegaAt and Interface.onUnits. -/
def bridgeOmegaInt (G : SheetGeometry D S μ v0) (l : ℝ) (f : S.FSˣ → ℂ) : ℂ :=
  ∫ y in bridgeOmegaAt G l, onUnits f y ∂(G.sheet l)

variable (G : SheetGeometry D S μ v0)

/-- Measurability, exact fundamental-domain condition, and finite restricted mass.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses NORM and SheetGeometry fields. -/
theorem a2_bridge_SHEET (l : ℝ) (hl : 0 < l) :
    bridgeFundamentalAt S (bridgeOmegaAt G l) l ∧
    G.sheet l (bridgeOmegaAt G l) < ⊤ ∧ Countable (Gamma S) := by
  sorry

/-- Multiplication transport of integrable unit functions.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses NORM and SheetGeometry.sheet_translate. -/
theorem a2_bridge_SHEET_transport (l : ℝ) (hl : 0 < l) (a : S.FSˣ)
    (f : S.FSˣ → ℂ) (hf : Integrable (onUnits f) (G.sheet (S.absS (a : S.FS) * l))) :
    Integrable (onUnits (fun y => f (a * y))) (G.sheet l) ∧
    bridgeSheetIntegral G l (fun y => f (a * y)) =
      bridgeSheetIntegral G (S.absS (a : S.FS) * l) f := by
  sorry

/-- Integrable unfolding on the actual diagonal Γ and positive norm sheet.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses SHEET and NORM.
The integrability premise is supplied by ANALYSIS before application. -/
theorem a2_bridge_SHEET_unfold (l : ℝ) (hl : 0 < l) (f : S.FSˣ → ℂ)
    (hf : Integrable (onUnits f) (G.sheet l)) :
    (∀ γ : Gamma S, IntegrableOn (onUnits (fun y => f (S.diagU (γ.1 : Fˣ) * y)))
      (bridgeOmegaAt G l) (G.sheet l)) ∧
    Summable (fun γ : Gamma S => bridgeOmegaInt G l (fun y => f (S.diagU (γ.1 : Fˣ) * y))) ∧
    (∑' γ : Gamma S, bridgeOmegaInt G l (fun y => f (S.diagU (γ.1 : Fˣ) * y))) =
      bridgeSheetIntegral G l f := by
  sorry

/-- Integrable inversion between reciprocal positive sheets.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses NORM and SheetGeometry.sheet_inversion. -/
theorem a2_bridge_SHEET_inversion (l : ℝ) (hl : 0 < l) (f : S.FSˣ → ℂ)
    (hf : Integrable (onUnits f) (G.sheet l⁻¹)) :
    Integrable (onUnits (fun y => f y⁻¹)) (G.sheet l) ∧
    bridgeSheetIntegral G l (fun y => f y⁻¹) = bridgeSheetIntegral G l⁻¹ f := by
  sorry

end ArtinPrimitiveRoots.A2
