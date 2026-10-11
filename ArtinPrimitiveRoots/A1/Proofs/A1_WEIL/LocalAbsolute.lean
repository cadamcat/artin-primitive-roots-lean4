import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private lemma absFin_eq_norm (v : FinPlace F) (x : v.adicCompletion F) :
    absFin v x = ‖x‖ := by
  dsimp [absFin]
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

/-- Basic positivity and multiplication for the frozen normalized finite absolute value.
Uses: absFin; Ideal.absNorm_pos; WithZeroMulInt.toNNReal. -/
theorem local_absolute_value (v : FinPlace F) :
    absFin v 1 = 1 ∧
    (∀ a : (v.adicCompletion F)ˣ, 0 < absFin v (a : v.adicCompletion F)) ∧
    (∀ a b : (v.adicCompletion F)ˣ,
      absFin v ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        absFin v (a : v.adicCompletion F) * absFin v (b : v.adicCompletion F)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [absFin_eq_norm, norm_one]
  · intro a
    rw [absFin_eq_norm]
    exact norm_pos_iff.mpr (Units.ne_zero a)
  · intro a b
    simp only [absFin_eq_norm, Units.val_mul, norm_mul]

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
