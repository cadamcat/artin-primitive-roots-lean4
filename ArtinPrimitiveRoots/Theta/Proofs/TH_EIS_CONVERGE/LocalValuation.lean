import ArtinPrimitiveRoots.Theta.TorusInd
import TauCeti.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The exponent in a rational element's local uniformizer decomposition is the
count of its principal fractional ideal at that place. -/
theorem toLoc_uniformizer_decomposition (v : FinPlace F) (δ : Fˣ) :
    ∃ u : (v.adicCompletion F)ˣ, IsLocUnit v u ∧
      toLoc v δ = unifLoc v ^ FractionalIdeal.count F v
        (toPrincipalIdeal (𝓞 F) F δ : FractionalIdeal (𝓞 F)⁰ F) * u := by
  let e := FractionalIdeal.count F v
    (toPrincipalIdeal (𝓞 F) F δ : FractionalIdeal (𝓞 F)⁰ F)
  have hδ : Valued.v (toLoc v δ : v.adicCompletion F) = WithZero.exp (-e) := by
    change Valued.v ((δ : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    dsimp only [e]
    rw [FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation, neg_neg]
    exact (WithZero.exp_log ((v.valuation F).ne_zero_iff.mpr δ.ne_zero)).symm
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    have hcoe : (unifLoc v : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (unif v) := by
      simp [unifLoc, toLoc]
    rw [hcoe]
    change Valued.v ((unif v : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  let u := unifLoc v ^ (-e) * toLoc v δ
  have hu : Valued.v (u : v.adicCompletion F) = 1 := by
    dsimp only [u]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, hδ]
    simp [← WithZero.exp_zsmul, ← WithZero.exp_add]
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val,
      map_inv₀, hu, inv_one]
  · change toLoc v δ = unifLoc v ^ e * (unifLoc v ^ (-e) * toLoc v δ)
    rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

end ArtinPrimitiveRoots.A1.Theta
