import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianBinary
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSign
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianSquare
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianOne

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem complexRoot_injective (D : FieldData F) :
    Function.Injective (complexRoot D) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply D.σ0.injective
  exact congrArg (fun z : ℂˣ => (z : ℂ)) hxy

private theorem hilbert_pow_left (H : HilbertData F) (v : FinPlace F)
    (a b : (v.adicCompletion F)ˣ) (n : ℕ) :
    H.hilb v (a ^ n) b = H.hilb v a b ^ n := by
  induction n with
  | zero =>
      simpa using H.sixth_power v 1 b ⟨1, by simp⟩
  | succ n ih =>
      rw [pow_succ, H.mul_left, ih, pow_succ]

private theorem quadratic_hilbert_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (c b : (v.adicCompletion F)ˣ) :
    complexRoot D (H.hilb v (c ^ 2) b) ^ 3 = 1 := by
  rw [← map_pow, ← hilbert_pow_left, ← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [H.sixth_power v (c ^ 6) b ⟨c, rfl⟩, map_one]

/-- Cubing the sextic Hilbert pairing has exactly the square subgroup as its radical.
This isolates the Hilbert nondegeneracy needed for the Gaussian comparison.
Guide: PROOFS.md:474–475; uses only the frozen Hilbert multiplicativity,
sixth-power vanishing, and nondegeneracy fields. -/
theorem quadratic_hilbert_trivial_iff_square (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    (∀ b, complexRoot D (H.hilb v a b) ^ 3 = 1) ↔
      ∃ c : (v.adicCompletion F)ˣ, a = c ^ 2 := by
  constructor
  · intro ha
    have hcube : ∀ b, H.hilb v (a ^ 3) b = 1 := by
      intro b
      apply complexRoot_injective D
      rw [hilbert_pow_left, map_pow, map_one]
      exact ha b
    obtain ⟨c, hc⟩ := H.nondeg v (a ^ 3) hcube
    refine ⟨a ^ 2 / c ^ 3, ?_⟩
    calc
      a = a ^ 4 / a ^ 3 := by
        rw [show a ^ 4 = a * a ^ 3 from pow_succ' a 3]
        simp
      _ = (a ^ 2 / c ^ 3) ^ 2 := by
        rw [hc]
        simp only [div_pow, ← pow_mul, Nat.reduceMul]
  · rintro ⟨c, rfl⟩ b
    exact quadratic_hilbert_square D H v c b

/-- Identify the Gaussian multiplicative defect with the quadratic Hilbert symbol.
Guide: PROOFS.md:474–475. Uses: local_index_binary; local_index_sign; local_index_square; H.steinberg; H.nondeg; H.tame; H.product_formula. -/
theorem local_index_hilbert_defect (D : FieldData F) (A : AddCharData F) (H : HilbertData F) (W : LocalGaussianData A)
    (v : FinPlace F) (a b : (v.adicCompletion F)ˣ) :
    W.index v a * W.index v b =
      complexRoot D (H.hilb v a b) ^ 3 * W.index v (a * b) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
