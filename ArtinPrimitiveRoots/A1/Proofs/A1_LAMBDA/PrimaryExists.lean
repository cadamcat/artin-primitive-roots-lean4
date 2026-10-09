import OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open OAI.ActualEisensteinCubic

theorem primary_generator_exists (I : Ideal O) (hI : I ≠ ⊥)
    (hcop : I ⊔ Ideal.span {lambda} = ⊤) :
    ∃ p : O, I = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 := by
  classical
  have hex (J : Ideal O) : J ≠ ⊥ → J ⊔ Ideal.span {lambda} = ⊤ →
      ∃ p : O, J = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 := by
    refine UniqueFactorizationMonoid.induction_on_prime J ?_ ?_ ?_
    · intro hzero _
      exact (hzero rfl).elim
    · intro J hunit _ _
      refine ⟨1, ?_, by simp⟩
      simpa using Ideal.isUnit_iff.mp hunit
    · intro J P hJ hP ih _ hcopPJ
      have hcopP : P ⊔ Ideal.span {lambda} = ⊤ := by
        apply top_le_iff.mp
        rw [← hcopPJ]
        exact sup_le_sup_right Ideal.mul_le_left _
      have hcopJ : J ⊔ Ideal.span {lambda} = ⊤ := by
        apply top_le_iff.mp
        rw [← hcopPJ]
        exact sup_le_sup_right Ideal.mul_le_right _
      have hgood : lambda ∉ P := by
        intro hmem
        have hle : Ideal.span {lambda} ≤ P :=
          (Ideal.span_singleton_le_iff_mem P).mpr hmem
        exact (Ideal.isPrime_of_prime hP).ne_top
          ((sup_eq_left.mpr hle).symm.trans hcopP)
      letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      obtain ⟨p, hp, hprimary, _⟩ := cubicJacobi_exists_primary_generator P hgood
      obtain ⟨q, hq, hqprimary⟩ := ih hJ hcopJ
      refine ⟨p * q, ?_, ?_⟩
      · rw [hp, hq, Ideal.span_singleton_mul_span_singleton]
      · have hdvd := dvd_add (dvd_mul_of_dvd_left hprimary q) hqprimary
        convert hdvd using 1 <;> ring
  exact hex I hI hcop

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
