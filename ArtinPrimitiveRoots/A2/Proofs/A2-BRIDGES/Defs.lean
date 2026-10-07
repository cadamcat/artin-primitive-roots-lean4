import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.Theta.Shared
import Mathlib.NumberTheory.GaussSum

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Actual exterior ideals of norm at most X; no finiteness claim is hidden in ncard.
Guide: sol-thin-a2rp/PROOFS.md:42–49. Uses Ideal.finite_setOfPred_absNorm_le. -/
def bridgeNormFinset (S : SData F CE condη) (X : ℝ) : Finset S.ExtIdeal :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊X⌋₊).toFinset.subtype S.IsExterior

/-- Finite Euclidean norm on an actual finite index set.
Guide: sol-thin-a2rp/PROOFS.md:67–68. Uses no other bridge. -/
def bridgeL2 {α : Type*} (T : Finset α) (f : α → ℂ) : ℝ :=
  Real.sqrt (∑ i ∈ T, ‖f i‖ ^ 2)

/-- Unit part of a positive norm sheet, with the inherited measurable structure.
Guide: sol-thin-a2rp/PROOFS.md:50–54. Uses S.absS. -/
def BridgeSheet (S : SData F CE condη) (l : ℝ) :=
  {y : S.FSˣ // S.absS (y : S.FS) = l}

/-- The measurable structure of a sheet: the subtype structure inherited from `S.FSˣ`
(refutation gate `sol-gate-bridges`: the frozen `def` does not let Lean infer it). -/
instance bridgeSheetMeasurableSpace (S : SData F CE condη) (l : ℝ) :
    MeasurableSpace (BridgeSheet S l) :=
  inferInstanceAs (MeasurableSpace {y : S.FSˣ // S.absS (y : S.FS) = l})

/-- The actual prime residue field. Instances are local to these definitions;
we do not install competing global field instances.
Guide: sol-thin-a2rp/PROOFS.md:63–64. -/
def bridgeResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  exact Ideal.Quotient.field v.asIdeal

/-- Enumeration of the actual nonzero-prime quotient.
Guide: sol-thin-a2rp/PROOFS.md:63–64. Uses Ring.HasFiniteQuotients.finiteQuotient. -/
def bridgeResidueFintype (v : FinPlace F) : Fintype (𝓞 F ⧸ v.asIdeal) := by
  letI : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  exact Fintype.ofFinite _

/-- SYMBOL contract: valuation-ring residues, the actual masked symbol, and actual localChi.
Guide: sol-thin-a2rp/PROOFS.md:32–41. Uses A1.Residue and Theta.Shared.localChi_basic.
No formula replaces chiIdealPow by an unmasked power. -/
structure SymbolBridge (D : FieldData F) (S : SData F CE condη) : Prop where
  residue_algebraMap : ∀ (v : FinPlace F) (a : 𝓞 F),
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a
  residue_congr : ∀ (v : FinPlace F) (x y : F),
    HeightOneSpectrum.valuation F v x ≤ 1 → HeightOneSpectrum.valuation F v y ≤ 1 →
    HeightOneSpectrum.valuation F v (x - y) < 1 → residue v x = residue v y
  residue_mul : ∀ (v : FinPlace F) (x y : F),
    HeightOneSpectrum.valuation F v x ≤ 1 → HeightOneSpectrum.valuation F v y ≤ 1 →
    residue v (x * y) = residue v x * residue v y
  residue_ne_zero : ∀ (v : FinPlace F) (x : F),
    HeightOneSpectrum.valuation F v x ≤ 1 →
    (residue v x ≠ 0 ↔ HeightOneSpectrum.valuation F v x = 1)
  chi_mul : ∀ (v : FinPlace F), v ∉ S.Sf → ∀ (x y : F),
    HeightOneSpectrum.valuation F v x ≤ 1 → HeightOneSpectrum.valuation F v y ≤ 1 →
    chi D v (x * y) = chi D v x * chi D v y
  chi_congr : ∀ (v : FinPlace F) (x y : F),
    residue v x = residue v y → chi D v x = chi D v y
  chi_six : ∀ (v : FinPlace F) (x : F), residue v x ≠ 0 → chi D v x ^ (6 : ℕ) = 1
  chi_norm : ∀ (v : FinPlace F) (x : F), residue v x ≠ 0 → ‖chi D v x‖ = 1
  chiPow_nonzero : ∀ (v : FinPlace F) (x : F) (e : ℤ),
    residue v x ≠ 0 → chiPow D v x e = chi D v x ^ e
  chiPow_zero : ∀ (v : FinPlace F) (x : F) (e : ℤ),
    residue v x = 0 → chiPow D v x e = 0
  chi_minus_one : ∀ (v : FinPlace F), v ∉ S.Sf → chi D v (-1) = 1
  chi_norm_le : ∀ (v : FinPlace F) (x : F), ‖chi D v x‖ ≤ 1
  chi_zpow_norm_le : ∀ (v : FinPlace F) (x : F) (e : ℤ), ‖chi D v x ^ e‖ ≤ 1
  chiPow_norm_le : ∀ (v : FinPlace F) (x : F) (e : ℤ), ‖chiPow D v x e‖ ≤ 1
  localChi_approximant : ∀ (v : FinPlace F), v ∉ S.Sf →
    ∀ (t : (v.adicCompletion F)ˣ), Theta.IsLocUnit v t → ∀ (a : 𝓞 F), a ∉ v.asIdeal →
    Valued.v ((t : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F a)) < 1 →
    localChi D v t = chi D v (algebraMap (𝓞 F) F a)
  localChi_norm_le : ∀ (v : FinPlace F) (t : (v.adicCompletion F)ˣ), ‖localChi D v t‖ ≤ 1
  localChi_six : ∀ (v : FinPlace F), v ∉ S.Sf →
    ∀ (t : (v.adicCompletion F)ˣ), Theta.IsLocUnit v t → localChi D v t ^ (6 : ℕ) = 1
  localChi_norm : ∀ (v : FinPlace F), v ∉ S.Sf →
    ∀ (t : (v.adicCompletion F)ˣ), Theta.IsLocUnit v t → ‖localChi D v t‖ = 1
  ideal_one : ∀ (x : F) (e : ℤ), chiIdealPow D ⊤ x e = 1
  ideal_norm_le : ∀ (I : Ideal (𝓞 F)) (x : F) (e : ℤ), ‖chiIdealPow D I x e‖ ≤ 1
  ideal_mul : ∀ (I J : Ideal (𝓞 F)), I ≠ ⊥ → J ≠ ⊥ → ∀ (x : F) (e : ℤ),
    chiIdealPow D (I * J) x e = chiIdealPow D I x e * chiIdealPow D J x e
  ideal_element_mul : ∀ (I : Ideal (𝓞 F)), S.IsExterior I → ∀ (x y : F) (e : ℤ),
    (∀ v : FinPlace F, v.asIdeal ∣ I →
      HeightOneSpectrum.valuation F v x ≤ 1 ∧ HeightOneSpectrum.valuation F v y ≤ 1) →
    chiIdealPow D I (x * y) e = chiIdealPow D I x e * chiIdealPow D I y e
  ideal_exponent_add : ∀ (I : Ideal (𝓞 F)) (x : F) (e f : ℤ),
    chiIdealPow D I x (e + f) = chiIdealPow D I x e * chiIdealPow D I x f
  ideal_zero_exponent : ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ∀ (x : F),
    chiIdealPow D I x 0 = if ∀ v : FinPlace F, v.asIdeal ∣ I → residue v x ≠ 0
      then 1 else 0

end ArtinPrimitiveRoots.A2
