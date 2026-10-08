import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.Family

/-!
# Admissibility of exterior finite prime supports

The planned support-admissibility statement is:
```
theorem qs_nq0_support_admissible
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη)
    (m : ClassFieldTheory.RayClassModulus K)
    (hm : m.finitePart.support = Sd.Sf)
    (qS : Ideal (𝓞 K)) (hqS : qS ≠ ⊥)
    (hsupport : ∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf)
    (T : Finset (FinPlace K)) (hT : Disjoint T Sd.Sf) :
    Sd.IsExterior (qsIdealOf T) ∧ QSAdm m qS (qsIdealOf T)
```
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- A finite prime support disjoint from S gives an exterior admissible squarefree index. -/
theorem qs_nq0_support_admissible
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (Sd : SData K CE condη)
    (m : ClassFieldTheory.RayClassModulus K)
    (hm : m.finitePart.support = Sd.Sf)
    (qS : Ideal (𝓞 K)) (hqS : qS ≠ ⊥)
    (hsupport : ∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf)
    (T : Finset (FinPlace K)) (hT : Disjoint T Sd.Sf) :
    Sd.IsExterior (qsIdealOf T) ∧ QSAdm m qS (qsIdealOf T) := by
  classical
  have hI0 : qsIdealOf T ≠ ⊥ := by
    change (∏ v ∈ T, v.asIdeal) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => v.ne_bot)
  have hexterior : Sd.IsExterior (qsIdealOf T) := by
    refine ⟨hI0, ?_⟩
    intro v hv hle
    change (∏ w ∈ T, w.asIdeal) ≤ v.asIdeal at hle
    obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp hle
    have hweq : w = v := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)
    subst w
    exact Finset.disjoint_left.mp hT hw hv
  have hsq : Squarefree (qsIdealOf T) := by
    change Squarefree (∏ v ∈ T, v.asIdeal)
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro v hv w hw hne
      letI : v.asIdeal.IsMaximal := v.isMaximal
      letI : w.asIdeal.IsMaximal := w.isMaximal
      exact (Ideal.isCoprime_of_isMaximal
        (fun heq => hne (HeightOneSpectrum.ext heq))).isRelPrime
    · intro v hv
      exact v.irreducible.squarefree
  have hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (qsIdealOf T) := by
    refine ⟨hI0, ?_⟩
    change ∀ v, v ∈ m.finitePart.support → FractionalIdeal.count K v
      (qsIdealOf T : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0
    intro v hv
    have hvS : v ∈ Sd.Sf := by rwa [hm] at hv
    have hzero : idealExp v (qsIdealOf T) = 0 := by
      by_contra hne
      have hdiv : v.asIdeal ∣ qsIdealOf T :=
        (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne
      exact hexterior.2 v hvS (Ideal.dvd_iff_le.mp hdiv)
    rw [FractionalIdeal.count_coe K v hI0]
    change (idealExp v (qsIdealOf T) : ℤ) = 0
    rw [hzero, Int.natCast_zero]
  have hcoprime : IsCoprime (qsIdealOf T) qS := by
    change IsCoprime (∏ v ∈ T, v.asIdeal) qS
    apply IsCoprime.prod_left
    intro v hv
    apply Ideal.isCoprime_iff_sup_eq.mpr
    by_contra htop
    have heq : v.asIdeal = v.asIdeal ⊔ qS := v.isMaximal.eq_of_le htop le_sup_left
    have hle : qS ≤ v.asIdeal := by rw [heq]; exact le_sup_right
    exact Finset.disjoint_left.mp hT hv (hsupport v hle)
  exact ⟨hexterior, hsq, hcm, hcoprime⟩

end ArtinPrimitiveRoots.A2
