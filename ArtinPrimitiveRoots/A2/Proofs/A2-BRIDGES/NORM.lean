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
  sorry

/-- Balanced-generator norm, with only the inputs needed for that generator.
Guide: sol-thin-a2rp/PROOFS.md:20–31. Uses absS_diag_eq_norm_ofFieldData and bc.gen_spec. -/
theorem a2_bridge_NORM_gen (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (bc : BalancedChoices D S H Bd) (I : S.ExtIdeal) :
    S.absS (S.diagU (bc.gen I) : S.FS) = idealNorm I.1 := by
  sorry

end ArtinPrimitiveRoots.A2
