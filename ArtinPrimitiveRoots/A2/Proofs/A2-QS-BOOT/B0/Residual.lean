import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-BOOT».B0.Basic

/-!
# B0 helpers: the residual columns of a small gcd block form a C4 block

For a part `P` of one ray class in a dyad `(n', 2n']` and `g = c ⊔ d` (`c, d ∈ P`), the residual
columns `c' (g c' ∈ P)` given by `qs_residual_form_S0` satisfy `QSBlockCols m qS (qsBadRad g) n`
with `n = n'/N g`, and their coefficient energy is at most that of `P`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSB0

open QSC2 QSC3

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

theorem prime_of_mem_nf {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) : Prime P :=
  prime_of_normalized_factor P h

theorem maximal_of_mem_nf {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) : P.IsMaximal := by
  have hp := prime_of_mem_nf h
  have h0 : P ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero
  exact Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime hp) h0

theorem qsRad_squarefree (I : Ideal (𝓞 K)) : Squarefree (qsRad I) := by
  classical
  unfold qsRad
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro P hP Q hQ hPQ
    have := maximal_of_mem_nf (Multiset.mem_toFinset.mp hP)
    have := maximal_of_mem_nf (Multiset.mem_toFinset.mp hQ)
    exact (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  · intro P hP
    exact (prime_of_mem_nf (Multiset.mem_toFinset.mp hP)).squarefree

theorem qsRad_dvd (I : Ideal (𝓞 K)) : qsRad I ∣ I := by
  classical
  unfold qsRad
  refine Finset.prod_dvd_of_coprime ?_ fun P hP =>
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  intro P hP Q hQ hPQ
  have := maximal_of_mem_nf (Multiset.mem_toFinset.mp hP)
  have := maximal_of_mem_nf (Multiset.mem_toFinset.mp hQ)
  exact Ideal.isCoprime_of_isMaximal hPQ

/-- An admissible ideal is coprime to `qsBadRad`. -/
theorem coprime_bad_of_QSAdm {a : Ideal (𝓞 K)} (ha : QSAdm m qS a) :
    IsCoprime a (qsBadRad m qS) := by
  have h1 : IsCoprime a (qsModulusRad m) := ((qs_isCoprimeTo_iff_M0 a).mp ha.2.1).2
  have h2 : IsCoprime a (qsModulusRad m * qS) := IsCoprime.mul_right h1 ha.2.2
  exact isCoprime_of_le h2.symm (Ideal.le_of_dvd (qsRad_dvd _)) |>.symm

theorem qsN_badRad_pos (hqS : qS ≠ ⊥) : 0 < qsN (qsBadRad m qS) := by
  refine qsN_pos ?_
  intro h0
  have hd : qsRad (qsModulusRad m * qS) ∣ qsModulusRad m * qS := qsRad_dvd _
  unfold qsBadRad at h0
  rw [h0] at hd
  exact badIdeal_ne_bot (m := m) hqS (le_bot_iff.mp (Ideal.le_of_dvd hd))

/-- The residual columns form a C4 block. -/
theorem residual_blockCols (hqS : qS ≠ ⊥) {P cols' : Finset (Ideal (𝓞 K))} {g : Ideal (𝓞 K)}
    {n' : ℝ} (hP : ∀ c ∈ P, QSAdm m qS c ∧ n' < qsN c ∧ qsN c ≤ 2 * n')
    (hcl : ∀ c ∈ P, ∀ d ∈ P, ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd)
    (hg : ∃ c ∈ P, ∃ d ∈ P, g = c ⊔ d)
    (hcols' : ∀ c' ∈ cols', QSAdm m qS c' ∧ IsCoprime c' g ∧ g * c' ∈ P) :
    QSBlockCols m qS (qsBadRad m qS * g) (n' / qsN g) cols' := by
  obtain ⟨c₀, hc₀, d₀, hd₀, rfl⟩ := hg
  have hc₀A := (hP c₀ hc₀).1
  have hgdvd : c₀ ⊔ d₀ ∣ c₀ := Ideal.dvd_iff_le.mpr le_sup_left
  have hgA : QSAdm m qS (c₀ ⊔ d₀) := QSAdm_of_dvd hc₀A hgdvd
  have hg0 : c₀ ⊔ d₀ ≠ ⊥ := ne_bot_of_QSAdm hgA
  have hgpos : 0 < qsN (c₀ ⊔ d₀) := qsN_pos hg0
  refine ⟨?_, dvd_mul_right _ _, ?_, ?_⟩
  · -- squarefree
    rw [squarefree_mul_iff]
    exact ⟨(coprime_bad_of_QSAdm hgA).symm.isRelPrime, qsRad_squarefree _, hgA.1⟩
  · intro c' hc'
    obtain ⟨hA, hcop, hmem⟩ := hcols' c' hc'
    obtain ⟨_, hlo, hhi⟩ := hP _ hmem
    rw [qsN_mul] at hlo hhi
    refine ⟨hA, IsCoprime.mul_right (coprime_bad_of_QSAdm hA) hcop, ?_, ?_⟩
    · rw [div_lt_iff₀ hgpos]; linarith
    · rw [mul_div_assoc', le_div_iff₀ hgpos]; linarith
  · intro c' hc' d' hd'
    obtain ⟨hcA, _, hcm⟩ := hcols' c' hc'
    obtain ⟨hdA, _, hdm⟩ := hcols' d' hd'
    obtain ⟨h1, h2, heq⟩ := hcl _ hcm _ hdm
    refine ⟨hcA.2.1, hdA.2.1, ?_⟩
    rw [rayClass_mul' (c₀ ⊔ d₀) c' hgA.2.1 hcA.2.1 h1,
      rayClass_mul' (c₀ ⊔ d₀) d' hgA.2.1 hdA.2.1 h2] at heq
    have := congrArg (fun x => (ArtinPrimitiveRoots.Hecke.rayClass m (c₀ ⊔ d₀) hgA.2.1)⁻¹ * x) heq
    simpa using this

/-- The residual coefficient energy is at most the part energy. -/
theorem residual_energy_le {P cols' : Finset (Ideal (𝓞 K))} {g : Ideal (𝓞 K)} (hg0 : g ≠ ⊥)
    (z z' : Ideal (𝓞 K) → ℂ) (hcols' : ∀ c' ∈ cols', g * c' ∈ P ∧ z' c' = z (g * c')) :
    ∑ c' ∈ cols', ‖z' c'‖ ^ 2 ≤ ∑ c ∈ P, ‖z c‖ ^ 2 := by
  classical
  have hg0' : g ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hinj : Set.InjOn (fun c' => g * c') cols' := fun a _ b _ h => mul_left_cancel₀ hg0' h
  calc ∑ c' ∈ cols', ‖z' c'‖ ^ 2 = ∑ c' ∈ cols', ‖z (g * c')‖ ^ 2 :=
        Finset.sum_congr rfl fun c' hc' => by rw [(hcols' c' hc').2]
    _ = ∑ c ∈ cols'.image (fun c' => g * c'), ‖z c‖ ^ 2 :=
        (Finset.sum_image (f := fun c => ‖z c‖ ^ 2) hinj).symm
    _ ≤ ∑ c ∈ P, ‖z c‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
        intro c hc
        rw [Finset.mem_image] at hc
        obtain ⟨c', hc', rfl⟩ := hc
        exact (hcols' c' hc').1

end ArtinPrimitiveRoots.A2.QSB0
