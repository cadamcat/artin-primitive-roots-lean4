import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

noncomputable def pd7dConjugateCharacter {k : ℕ} (χ : DirichletCharacter ℂ k) :
    DirichletCharacter ℂ k := χ.ringHomComp (starRingEnd ℂ)

lemma pd7dConjugateCharacter_apply {k : ℕ} (χ : DirichletCharacter ℂ k) (x : ZMod k) :
    pd7dConjugateCharacter χ x = star (χ x) := rfl

lemma pd7d_negative_phase_star (t l : ℝ) :
    star (Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * (l : ℂ))) =
      Complex.exp (Complex.I * (t : ℂ) * (l : ℂ)) := by
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

lemma pd7d_character_polynomial_star {k : ℕ} (χ : DirichletCharacter ℂ k)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    star (∑ n ∈ S, c n * pd7dConjugateCharacter χ (n : ZMod k) *
      Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * Real.log (n : ℝ))) =
      ∑ n ∈ S, star (c n) * χ (n : ZMod k) * Complex.exp (Complex.I * t * Real.log (n : ℝ)) := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [star_mul, star_mul, pd7dConjugateCharacter_apply, star_star, pd7d_negative_phase_star]
  ring

end ArtinPrimitiveRoots.TypeII.PD
