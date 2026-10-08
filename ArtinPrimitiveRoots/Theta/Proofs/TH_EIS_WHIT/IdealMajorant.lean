import ArtinPrimitiveRoots.Theta.Proofs.TH_EIS_WHIT.RationalEncoding
import ArtinPrimitiveRoots.Hecke.Theta.IdealNormSummability

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- An injective ideal code with finitely many extra coordinates transfers ideal-norm convergence. -/
theorem whit_ideal_norm_majorant {Q B : Type} [Finite B]
    (f : Q → ℂ)
    (code : {q : Q // f q ≠ 0} → Ideal (𝓞 F) × B)
    (hinj : Function.Injective code)
    (σ C : ℝ) (hσ : 1 < σ) (hC : 0 ≤ C)
    (hbound : ∀ q : {q : Q // f q ≠ 0},
      ‖f q.1‖ ≤ C * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ (code q).1) :
    Summable (fun q : Q => ‖f q‖) := by
  letI : Fintype B := Fintype.ofFinite B
  have hnonneg (I : Ideal (𝓞 F)) :
      0 ≤ ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ I := by
    unfold ArtinPrimitiveRoots.Hecke.idealNormRpowTerm
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hI : Summable (fun I : Ideal (𝓞 F) =>
      C * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ I) :=
    (ArtinPrimitiveRoots.Hecke.summable_idealNormRpow hσ).mul_left C
  have hmajor : Summable (fun p : Ideal (𝓞 F) × B =>
      C * ArtinPrimitiveRoots.Hecke.idealNormRpowTerm σ p.1) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg hC (hnonneg p.1))).mpr
    constructor
    · intro I
      exact Summable.of_finite
    · have hcard := hI.mul_left (Fintype.card B : ℝ)
      simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hcard
  have hsupport : Summable (fun q : {q : Q // f q ≠ 0} => ‖f q.1‖) :=
    (hmajor.comp_injective hinj).of_nonneg_of_le (fun q => norm_nonneg _) hbound
  have hsubset : Function.support (fun q : Q => ‖f q‖) ⊆ {q : Q | f q ≠ 0} := by
    intro q hq hf
    change ‖f q‖ ≠ 0 at hq
    exact hq (by rw [hf, norm_zero])
  exact ⟨_, (hasSum_subtype_iff_of_support_subset hsubset).mp hsupport.hasSum⟩

end ArtinPrimitiveRoots.A1.Theta
