import /- Local package with a hyphenated directory name. -/ ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».SHEET

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

/-- Absolute tensor sum on units; definitionally equal to rotatedAbs with projected R.rotated data.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses the actual finite and complex factors. -/
def bridgeRotatedAbs (S : SData F CE condη) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (y : S.FSˣ) : ℝ :=
  ∑ ℓ : Fin J, (∏ v : S.Sf, ‖ff ℓ v ((y : S.FS).1 v)‖) *
    ∏ w : InfinitePlace F, ‖fc ℓ w ((y : S.FS).2 w)‖

/-- Absolute sheet profile, definitionally equal to profileAbs on the consumer's projected data.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses bridgeRotatedAbs and bridgeSheetIntegral. -/
def bridgeProfileAbs (G : SheetGeometry D S μ v0) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (x : ℝ) : ℝ :=
  (bridgeSheetIntegral G x (fun y => (bridgeRotatedAbs S J ff fc y : ℂ))).re

/-- One profile tensor with its actual bounded multiplier. No ReflectionSetup import is needed.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses bridgeSheetIntegral. -/
def bridgeProfileH (G : SheetGeometry D S μ v0) (m : S.FSˣ → ℂ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ) (ℓ : Fin J) (x : ℝ) : ℂ :=
  bridgeSheetIntegral G x (fun y => m y *
    (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
    ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))

variable (G : SheetGeometry D S μ v0)

/-- Absolute tensors are integrable on each positive sheet.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses local hypotheses and the sheet parametrization. -/
theorem a2_bridge_ANALYSIS (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w)) :
    ∀ x : ℝ, 0 < x →
      Integrable (onUnits (fun y => (bridgeRotatedAbs S J ff fc y : ℂ))) (G.sheet x) := by
  sorry

/-- Each tensor multiplied by an admissible bounded S-character/class multiplier is integrable.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses ANALYSIS and Theta.SheetMultiplier. -/
theorem a2_bridge_ANALYSIS_tensor (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∀ (ℓ : Fin J) (x : ℝ), 0 < x →
      Integrable (onUnits (fun y => m y *
        (∏ v : S.Sf, ff ℓ v ((y : S.FS).1 v)) *
        ∏ w : InfinitePlace F, fc ℓ w ((y : S.FS).2 w))) (G.sheet x) := by
  sorry

/-- Convolution majorants exist as integrable functions before bounds on their integrals.
Guide: sol-thin-a2rp/PROOFS.md:55–62. Uses ANALYSIS, ANALYSIS_tensor and all kernel moments. -/
theorem a2_bridge_ANALYSIS_convolution (δ : ℝ) (hδ : 0 < δ) (J : ℕ)
    (ff : Fin J → (v : S.Sf) → v.1.adicCompletion F → ℂ)
    (fc : Fin J → InfinitePlace F → ℂ → ℂ)
    (hff : ∀ ℓ v, SheetHypFin v.1 δ (ff ℓ v)) (hfc : ∀ ℓ w, SheetHypC δ (fc ℓ w))
    (K : ℝ → ℂ) (hKmeas : AEStronglyMeasurable K (volume.restrict (Set.Ioi (0 : ℝ))))
    (hK : ∀ β : ℝ, IntegrableOn (fun T : ℝ => ‖K T‖ * T ^ β / T) (Set.Ioi 0))
    (m : S.FSˣ → ℂ) (hm : Theta.SheetMultiplier S (onUnits m)) :
    ∀ x : ℝ, 0 < x →
      IntegrableOn (fun T : ℝ => ‖K T‖ * bridgeProfileAbs G J ff fc (x / T) / T) (Set.Ioi 0) ∧
      IntegrableOn (fun T : ℝ => ‖K T‖ * bridgeProfileAbs G J ff fc (x * T) / T) (Set.Ioi 0) ∧
      (∀ ℓ : Fin J,
        IntegrableOn (fun T : ℝ => K T * bridgeProfileH G m J ff fc ℓ (x / T) / (T : ℂ))
          (Set.Ioi 0)) := by
  sorry

end ArtinPrimitiveRoots.A2
