import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.NaturalResidueExpansion

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

lemma pd7d_residual_phase (Y lam b m n a r s : ℝ) :
    additiveCharacter (lam * (b*m*n-a*r*s-b+a)/Y) =
      additiveCharacter (-lam*b/Y) * additiveCharacter (lam*a/Y) *
        additiveCharacter (lam*(b*m*n-a*r*s)/Y) := by
  rw [← pd7d_additiveCharacter_add, ← pd7d_additiveCharacter_add]
  congr 1
  ring

noncomputable def pd7dSixCoordinates {α β : Type*} (b m n : α → ℕ) (a r s : β → ℕ)
    (i : α) (j : β) : Fin 6 → ℕ := ![b i, m i, n i, a j, r j, s j]

lemma pd7d_finite_character_pair {α β : Type*} (S : Finset α) (T : Finset β)
    (b m n : α → ℕ) (a r s : β → ℕ) (c : α → ℂ) (d : β → ℂ)
    (h : ℤ) (k : ℕ) [NeZero k] (Y lam : ℝ) (ψ : ℝ → ℝ)
    (hc : ∀ i ∈ S, c i ≠ 0 → IsUnit (b i : ZMod k) ∧ IsUnit (m i : ZMod k) ∧ IsUnit (n i : ZMod k))
    (hd : ∀ j ∈ T, d j ≠ 0 → IsUnit (a j : ZMod k) ∧ IsUnit (r j : ZMod k) ∧ IsUnit (s j : ZMod k)) :
    (∑ i ∈ S, ∑ j ∈ T, c i * d j *
      (ψ (((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y) : ℂ) *
      additiveCharacter ((h : ℝ)*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j-b i+a j)/k) *
      additiveCharacter (lam*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j-b i+a j)/Y)) =
    ∑ χ : Fin 6 → DirichletCharacter ℂ k,
      pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ *
      ∑ i ∈ S, ∑ j ∈ T,
        (c i * χ 0 (b i : ZMod k) * χ 1 (m i : ZMod k) * χ 2 (n i : ZMod k) *
          additiveCharacter (-lam*(b i : ℝ)/Y)) *
        (d j * χ 3 (a j : ZMod k) * χ 4 (r j : ZMod k) * χ 5 (s j : ZMod k) *
          additiveCharacter (lam*(a j : ℝ)/Y)) *
        ((ψ (((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y) : ℂ) *
          additiveCharacter (lam*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y)) := by
  have hterm (i : α) (hi : i ∈ S) (j : β) (hj : j ∈ T) :
      c i*d j*(ψ (((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y) : ℂ)*
      additiveCharacter ((h : ℝ)*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j-b i+a j)/k)*
      additiveCharacter (lam*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j-b i+a j)/Y) =
      ∑ χ : Fin 6 → DirichletCharacter ℂ k,
        pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ *
        (c i * χ 0 (b i : ZMod k) * χ 1 (m i : ZMod k) * χ 2 (n i : ZMod k) *
          additiveCharacter (-lam*(b i : ℝ)/Y)) *
        (d j * χ 3 (a j : ZMod k) * χ 4 (r j : ZMod k) * χ 5 (s j : ZMod k) *
          additiveCharacter (lam*(a j : ℝ)/Y)) *
        ((ψ (((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y) : ℂ) *
          additiveCharacter (lam*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y)) := by
    by_cases hci : c i = 0
    · simp only [hci, zero_mul, mul_zero, Finset.sum_const_zero]
    by_cases hdj : d j = 0
    · simp only [hdj, zero_mul, mul_zero, Finset.sum_const_zero]
    let z := pd7dSixCoordinates b m n a r s i j
    have hz : ∀ l : Fin 6, IsUnit (z l : ZMod k) := by
      intro l
      fin_cases l
      · exact (hc i hi hci).1
      · exact (hc i hi hci).2.1
      · exact (hc i hi hci).2.2
      · exact (hd j hj hdj).1
      · exact (hd j hj hdj).2.1
      · exact (hd j hj hdj).2.2
    have hh := pd7d_natural_residue_character_expansion h k z hz
    dsimp [z,pd7dSixCoordinates] at hh
    push_cast at hh
    rw [hh, pd7d_residual_phase Y lam]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hprod := pd7d_six_character_product χ z
    dsimp [z,pd7dSixCoordinates] at hprod
    rw [hprod]
    ring
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ χ : Fin 6 → DirichletCharacter ℂ k,
        pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ *
        (c i * χ 0 (b i : ZMod k) * χ 1 (m i : ZMod k) * χ 2 (n i : ZMod k) *
          additiveCharacter (-lam*(b i : ℝ)/Y)) *
        (d j * χ 3 (a j : ZMod k) * χ 4 (r j : ZMod k) * χ 5 (s j : ZMod k) *
          additiveCharacter (lam*(a j : ℝ)/Y)) *
        ((ψ (((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y) : ℂ) *
          additiveCharacter (lam*((b i : ℝ)*m i*n i-(a j : ℝ)*r j*s j)/Y)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm i hi j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := Finset.univ)]
      rw [Finset.sum_comm (s := S) (t := Finset.univ)]
      simp only [Finset.mul_sum, mul_assoc]
end ArtinPrimitiveRoots.TypeII.PD
