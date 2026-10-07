import ArtinPrimitiveRoots.Hecke.Elementary

/-!
# Ideal norm summability for ray-class Dirichlet terms

The ideal-counting argument in this file is adapted from AINTLIB's
`projects/DedekindResidue/DedekindResidue/CompletedZeta/MellinAgreement.lean`
(Apache-2.0, Copyright 2026 Chris Birkbeck). It supplies the absolute convergence needed to
apply `LSeriesRay_eq_tsum_rayIdealDirichletTerm` on `Re s > 1`.
-/

set_option autoImplicit false

open scoped NumberField
open scoped nonZeroDivisors
open NumberField IsDedekindDomain
open Filter
open Asymptotics
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.Hecke

variable {K : Type*} [Field K] [NumberField K]
open ClassFieldTheory

local instance normFiberFinite (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype

private theorem sum_count_eq_card_le_nat (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} =
      Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} := by
  classical
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k)]
  simp [Set.coe_eq_subtype]

private theorem sum_count_eq_card_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) =
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) := by
  exact_mod_cast sum_count_eq_card_le_nat (K := K) n

private theorem count_LSeriesSummable :
    {s : ℝ} → 1 < s → LSeriesSummable
      (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) (s : ℂ) := by
  intro s hs
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_
    (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  have htend : Tendsto (fun n : ℕ =>
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) / (n : ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
    have h1 := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop
    refine h1.congr (fun n => ?_)
    simp only [Function.comp_apply]
    congr 2
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun I => ?_))
    exact_mod_cast Iff.rfl
  have hbigO : (fun n : ℕ =>
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ))
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
    have h2 : (fun n : ℕ =>
        (Nat.card {I : (Ideal (𝓞 K))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ n} : ℝ) / (n : ℝ))
        =O[atTop] (fun _ : ℕ => (1 : ℝ)) := htend.isBigO_one ℝ
    have h3 := h2.mul (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
    refine (h3.congr' ?_ (by filter_upwards with n; rw [one_mul])).congr_left
      (fun n => rfl)
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    rw [div_mul_cancel₀]
    exact_mod_cast hn
  refine hbigO.congr' ?_ (by filter_upwards with n; rw [Real.rpow_one])
  filter_upwards with n
  rw [sum_count_eq_card_le]

def idealNormRpowTerm (σ : ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if Ideal.absNorm I = 0 then 0 else (Ideal.absNorm I : ℝ) ^ (-σ)

private theorem idealNormRpowTerm_normFiber_sum (σ : ℝ) (n : ℕ) :
    ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, idealNormRpowTerm σ I.1 =
      if n = 0 then 0 else
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-σ) := by
  classical
  letI : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := Fintype.ofFinite _
  rw [tsum_fintype]
  by_cases hn : n = 0
  · subst n
    apply Finset.sum_eq_zero
    intro I _
    simp [idealNormRpowTerm, I.property]
  · have hterm (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) :
        idealNormRpowTerm σ I.1 = (n : ℝ) ^ (-σ) := by
      unfold idealNormRpowTerm
      rw [ite_eq_right (fun h => hn (I.property.symm.trans h)), I.property]
    simp_rw [hterm]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card]
    simp [hn]

/-- The real norm-power sum over all integral ideals converges for exponent greater than one. -/
theorem summable_idealNormRpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : Ideal (𝓞 K) => idealNormRpowTerm σ I) := by
  classical
  have hLS := count_LSeriesSummable (K := K) hσ
  have hreal : Summable (fun n : ℕ =>
      if n = 0 then 0 else
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-σ)) := by
    have h1 : Summable (fun n : ℕ => LSeries.term (fun m =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} : ℝ) : ℂ)) (σ : ℂ) n) := hLS
    have h2 : ∀ n : ℕ, LSeries.term (fun m =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} : ℝ) : ℂ)) (σ : ℂ) n =
          (((if n = 0 then 0 else
            (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ σ) : ℝ) : ℂ) := by
      intro n
      rw [LSeries.term]
      split_ifs with hn
      · rw [Complex.ofReal_zero]
      · rw [Complex.ofReal_div]
        congr 1
        rw [show ((n : ℂ)) ^ (σ : ℂ) = ((n : ℝ) : ℂ) ^ ((σ : ℝ) : ℂ) by norm_cast,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    have h3 : Summable (fun n : ℕ => if n = 0 then 0 else
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) / (n : ℝ) ^ σ) := by
      rw [← Complex.summable_ofReal]
      exact h1.congr h2
    refine h3.congr (fun n => ?_)
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  let f : (Σ n : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = n}) → ℝ :=
    fun p => idealNormRpowTerm σ p.2.1
  have hf_nonneg : ∀ p, 0 ≤ f p := by
    intro p
    simp only [f, idealNormRpowTerm]
    split_ifs <;> positivity
  have houter : Summable (fun n : ℕ =>
      ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, idealNormRpowTerm σ I.1) := by
    refine hreal.congr (fun n => ?_)
    exact (idealNormRpowTerm_normFiber_sum σ n).symm
  have hSigma : Summable f :=
    (summable_sigma_of_nonneg hf_nonneg).2 ⟨fun _ => Summable.of_finite, houter⟩
  exact (Equiv.summable_iff (Equiv.sigmaFiberEquiv Ideal.absNorm)).1 hSigma

end ArtinPrimitiveRoots.Hecke

end
