import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem squarefree_cube_injective {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη) :
    Function.Injective (fun p : S.SqfExtIdeal × S.ExtIdeal =>
      p.1.1 * p.2.1 ^ (3 : ℕ)) := by
  classical
  have hEm (P I : Ideal (𝓞 F)) (hP : Prime P) (hI : I ≠ 0) :
      emultiplicity P I = (factorization I P : ℕ∞) := by
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP.irreducible hI]
    simp [factorization, normalize_eq]
  intro p q hpq
  have hpC0 : p.1.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using p.1.property.1.1
  have hpN0 : p.2.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using p.2.property.1
  have hqC0 : q.1.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using q.1.property.1.1
  have hqN0 : q.2.1 ≠ 0 := by simpa only [Ideal.zero_eq_bot] using q.2.property.1
  have hfac := congrArg (fun I : Ideal (𝓞 F) => factorization I) hpq
  rw [factorization_mul hpC0 (pow_ne_zero 3 hpN0), factorization_pow,
    factorization_mul hqC0 (pow_ne_zero 3 hqN0), factorization_pow] at hfac
  have hcounts (P : Ideal (𝓞 F)) :
      factorization p.1.1 P = factorization q.1.1 P ∧
        factorization p.2.1 P = factorization q.2.1 P := by
    by_cases hP : Prime P
    · have hcp : factorization p.1.1 P ≤ 1 := by
        have h := ((squarefree_iff_emultiplicity_le_one p.1.1).mp
          p.1.property.2 P).resolve_right hP.not_isUnit
        rw [hEm P p.1.1 hP hpC0] at h
        exact_mod_cast h
      have hcq : factorization q.1.1 P ≤ 1 := by
        have h := ((squarefree_iff_emultiplicity_le_one q.1.1).mp
          q.1.property.2 P).resolve_right hP.not_isUnit
        rw [hEm P q.1.1 hP hqC0] at h
        exact_mod_cast h
      have hsum := congrArg (fun f : Ideal (𝓞 F) →₀ ℕ => f P) hfac
      simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hsum
      omega
    · have hnotNorm (J : Ideal (𝓞 F)) :
          P ∉ UniqueFactorizationMonoid.normalizedFactors J := by
        intro hPJ
        exact hP (UniqueFactorizationMonoid.prime_of_normalized_factor P hPJ)
      have hzero (J : Ideal (𝓞 F)) : factorization J P = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hsupp
        have hPfin : P ∈ (UniqueFactorizationMonoid.normalizedFactors J).toFinset := by
          simpa [support_factorization] using hsupp
        exact hnotNorm J (Multiset.mem_toFinset.mp hPfin)
      simp [hzero]
  have hCfac : factorization p.1.1 = factorization q.1.1 := by
    ext P
    exact (hcounts P).1
  have hNfac : factorization p.2.1 = factorization q.2.1 := by
    ext P
    exact (hcounts P).2
  have hC : p.1.1 = q.1.1 := associated_iff_eq.mp
    (associated_of_factorization_eq p.1.1 q.1.1 hpC0 hqC0 hCfac)
  have hN : p.2.1 = q.2.1 := associated_iff_eq.mp
    (associated_of_factorization_eq p.2.1 q.2.1 hpN0 hqN0 hNfac)
  exact Prod.ext (Subtype.ext hC) (Subtype.ext hN)

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
