import ArtinPrimitiveRoots.Hecke.Elementary
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped NumberField BigOperators
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.HK_MISC_P

open ArtinPrimitiveRoots.Hecke

def omittedEuler {K : Type*} [Field K] [NumberField K]
    (m : RayClassModulus K) {f : RayClassModulus K}
    (ψ : RayClassGroup f →* ℂˣ) (s : ℂ) : ℂ :=
  ∏ v ∈ m.finitePart.support,
    (1 - charValue ψ v.asIdeal *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))

theorem omittedEuler_differentiable {K : Type*} [Field K] [NumberField K]
    (m : RayClassModulus K) {f : RayClassModulus K}
    (ψ : RayClassGroup f →* ℂˣ) :
    Differentiable ℂ (omittedEuler m ψ) := by
  classical
  unfold omittedEuler
  refine Differentiable.fun_finsetProd ?_
  intro v hv
  have hqnat : Ideal.absNorm v.asIdeal ≠ 0 := by
    exact (Nat.ne_of_gt (Nat.zero_lt_of_lt
      (NumberField.HeightOneSpectrum.one_lt_absNorm v)))
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hqnat
  have hpow : Differentiable ℂ
      (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s
    exact (differentiableAt_id.neg).const_cpow (Or.inl hq)
  exact (differentiable_const (1 : ℂ)).sub
    ((differentiable_const (charValue ψ v.asIdeal)).mul hpow)

private theorem omittedEuler_factor_norm_le_two {K : Type*} [Field K] [NumberField K]
    {f : RayClassModulus K} (ψ : RayClassGroup f →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖1 - charValue ψ v.asIdeal *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 2 := by
  have hqnat : 0 < Ideal.absNorm v.asIdeal := by
    exact Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hq : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm v.asIdeal from by omega)
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hq (by simp; linarith)
  have hcpow :
      ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hqnat]
    simp
  have hchar := norm_charValue_le_one ψ v.asIdeal
  have hmul :
      ‖charValue ψ v.asIdeal‖ *
          ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [hcpow]
    exact (mul_le_mul hchar hpow (by positivity) (by norm_num : 0 ≤ (1 : ℝ))).trans_eq
      (by ring)
  calc
    _ ≤ ‖(1 : ℂ)‖ +
        ‖charValue ψ v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ = 1 + ‖charValue ψ v.asIdeal‖ *
        ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by simp [norm_mul]
    _ ≤ 2 := by linarith

private theorem omittedEuler_factor_norm_le_rpow {K : Type*} [Field K] [NumberField K]
    {f : RayClassModulus K} (ψ : RayClassGroup f →* ℂˣ)
    (ε : ℝ) (hε : 0 < ε) (R : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 0 ≤ s.re)
    (hv : R < Ideal.absNorm v.asIdeal)
    (hcut : Real.rpow 2 ε⁻¹ ≤ (R : ℝ)) :
    ‖1 - charValue ψ v.asIdeal *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ ε := by
  have hqnat : 0 < Ideal.absNorm v.asIdeal := by
    exact Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hq : (R : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hv
  have hbase : Real.rpow 2 ε⁻¹ < (Ideal.absNorm v.asIdeal : ℝ) := hcut.trans_lt hq
  have htwo : 2 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ ε := by
    calc
      2 = (Real.rpow 2 ε⁻¹) ^ ε := by
        exact (Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.ne').symm
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ ε :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase.le hε.le
  exact (omittedEuler_factor_norm_le_two ψ v hs).trans htwo

private theorem omittedEuler_modulus_rpow_eq {K : Type*} [Field K] [NumberField K]
    (m : RayClassModulus K) (ε : ℝ) :
    (∏ v ∈ m.finitePart.support,
      (Ideal.absNorm v.asIdeal : ℝ) ^ (ε * (m.finitePart v : ℝ))) =
      (modulusNorm m : ℝ) ^ ε := by
  classical
  calc
    _ = ∏ v ∈ m.finitePart.support,
        ((Ideal.absNorm v.asIdeal : ℝ) ^ (m.finitePart v : ℝ)) ^ ε := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [show ε * (m.finitePart v : ℝ) = (m.finitePart v : ℝ) * ε by ring,
        Real.rpow_natCast_mul (by positivity) (m.finitePart v) ε]
      simp only [Real.rpow_natCast]
    _ = (∏ v ∈ m.finitePart.support,
          (Ideal.absNorm v.asIdeal : ℝ) ^ (m.finitePart v : ℝ)) ^ ε :=
        Real.finsetProd_rpow _ _ (by intro v hv; positivity) ε
    _ = (modulusNorm m : ℝ) ^ ε := by
      congr 2
      simp [modulusNorm, Finsupp.prod, Nat.cast_prod, Nat.cast_pow, Real.rpow_natCast]

theorem exists_omittedEuler_bound {K : Type*} [Field K] [NumberField K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m f : RayClassModulus K)
      (ψ : RayClassGroup f →* ℂˣ) (s : ℂ), 0 ≤ s.re →
      ‖omittedEuler m ψ s‖ ≤ B * (modulusNorm m : ℝ) ^ ε := by
  classical
  let R : ℕ := Nat.ceil (Real.rpow 2 ε⁻¹)
  let smallPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | Ideal.absNorm v.asIdeal ≤ R}
  have hsmallFinite : smallPrimes.Finite := by
    simpa [smallPrimes] using
      (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le
        (S := 𝓞 K) R)
  let B : ℝ := (2 : ℝ) ^ hsmallFinite.toFinset.card
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro m f ψ s hs
  let smallSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
    m.finitePart.support.filter (fun v => Ideal.absNorm v.asIdeal ≤ R)
  have hsmallSubset : smallSupport ⊆ hsmallFinite.toFinset := by
    intro v hv
    change v ∈ m.finitePart.support.filter _ at hv
    rcases Finset.mem_filter.mp hv with ⟨_, hvbound⟩
    exact hsmallFinite.mem_toFinset.mpr hvbound
  have hsmallCard : smallSupport.card ≤ hsmallFinite.toFinset.card :=
    Finset.card_le_card hsmallSubset
  have hcut : Real.rpow 2 ε⁻¹ ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil _
  have hlocal (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ m.finitePart.support) :
      ‖1 - charValue ψ v.asIdeal *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (ε * (m.finitePart v : ℝ)) *
          (if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) := by
    have hvnz : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hvexp : 1 ≤ m.finitePart v := Nat.one_le_iff_ne_zero.mpr hvnz
    have hqone : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have hvnorm := NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hnat : 1 ≤ Ideal.absNorm v.asIdeal := by omega
      exact_mod_cast hnat
    have he : ε ≤ ε * (m.finitePart v : ℝ) := by
      have hecast : (1 : ℝ) ≤ (m.finitePart v : ℝ) := by exact_mod_cast hvexp
      nlinarith [hε]
    have hpowMon :
        (Ideal.absNorm v.asIdeal : ℝ) ^ ε ≤
          (Ideal.absNorm v.asIdeal : ℝ) ^ (ε * (m.finitePart v : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hqone he
    have hpowOne :
        1 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (ε * (m.finitePart v : ℝ)) :=
      Real.one_le_rpow hqone (mul_nonneg hε.le (by positivity))
    by_cases hsmall : Ideal.absNorm v.asIdeal ≤ R
    · have htwo := omittedEuler_factor_norm_le_two ψ v hs
      calc
        _ ≤ 2 := htwo
        _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^
              (ε * (m.finitePart v : ℝ)) * 2 := by nlinarith
        _ = _ := by simp [hsmall]
    · have hlarge : R < Ideal.absNorm v.asIdeal := Nat.lt_of_not_ge hsmall
      have hfactor := omittedEuler_factor_norm_le_rpow ψ ε hε R v hs hlarge hcut
      calc
        _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ ε := hfactor
        _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^
              (ε * (m.finitePart v : ℝ)) := hpowMon
        _ = _ := by simp [hsmall]
  have hfactorNorm :
      ‖omittedEuler m ψ s‖ ≤
        ∏ v ∈ m.finitePart.support,
          ‖1 - charValue ψ v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
    simpa [omittedEuler] using
      (Finset.norm_prod_le (s := m.finitePart.support) (f := fun v =>
        1 - charValue ψ v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))
  have hprod :
      (∏ v ∈ m.finitePart.support,
          ‖1 - charValue ψ v.asIdeal *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖) ≤
        (∏ v ∈ m.finitePart.support,
          (Ideal.absNorm v.asIdeal : ℝ) ^
              (ε * (m.finitePart v : ℝ))) *
            (∏ v ∈ m.finitePart.support,
              if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) := by
    calc
      _ ≤ ∏ v ∈ m.finitePart.support,
          ((Ideal.absNorm v.asIdeal : ℝ) ^
              (ε * (m.finitePart v : ℝ)) *
            (if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1)) := by
        have hprodAux (S : Finset (HeightOneSpectrum (𝓞 K)))
            (hS : S ⊆ m.finitePart.support) :
            (∏ v ∈ S,
                ‖1 - charValue ψ v.asIdeal *
                  ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖) ≤
              (∏ v ∈ S,
                (Ideal.absNorm v.asIdeal : ℝ) ^
                    (ε * (m.finitePart v : ℝ)) *
                  (if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1)) := by
          induction S using Finset.induction_on with
          | empty => simp
          | @insert v S hv ih =>
              simp only [Finset.prod_insert hv]
              have hpoint := hlocal v (hS (Finset.mem_insert_self v S))
              have htail :
                  0 ≤ ∏ x ∈ S,
                    ‖1 - charValue ψ x.asIdeal *
                      ((Ideal.absNorm x.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by positivity
              exact mul_le_mul hpoint
                (ih (Finset.Subset.trans (Finset.subset_insert v S) hS))
                htail (by positivity)
        exact hprodAux m.finitePart.support subset_rfl
      _ = _ := by rw [Finset.prod_mul_distrib]
  have hcorrection :
      (∏ v ∈ m.finitePart.support,
          if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) =
        (2 : ℝ) ^ smallSupport.card := by
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      m.finitePart.support (fun v => Ideal.absNorm v.asIdeal ≤ R)
      (fun v => if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1)
    have hsmallProd :
        (∏ v ∈ m.finitePart.support with Ideal.absNorm v.asIdeal ≤ R,
            if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) =
          (2 : ℝ) ^ smallSupport.card := by
      change (∏ v ∈ smallSupport,
        if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) = _
      calc
        _ = ∏ v ∈ smallSupport, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro v hv
          have hvsmall := (Finset.mem_filter.mp hv).2
          simp [hvsmall]
        _ = (2 : ℝ) ^ smallSupport.card := by simp
    have hlargeProd :
        (∏ v ∈ m.finitePart.support with ¬Ideal.absNorm v.asIdeal ≤ R,
            if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro v hv
      simp only [Finset.mem_filter] at hv
      simp [hv.2]
    rw [← hsplit, hsmallProd, hlargeProd, mul_one]
  have hsmallpow : (2 : ℝ) ^ smallSupport.card ≤ B := by
    dsimp [B]
    exact pow_le_pow_right₀ (by norm_num) hsmallCard
  calc
    ‖omittedEuler m ψ s‖ ≤
        (∏ v ∈ m.finitePart.support,
          (Ideal.absNorm v.asIdeal : ℝ) ^ (ε * (m.finitePart v : ℝ))) *
          (∏ v ∈ m.finitePart.support,
            if Ideal.absNorm v.asIdeal ≤ R then (2 : ℝ) else 1) :=
      hfactorNorm.trans hprod
    _ = (modulusNorm m : ℝ) ^ ε * (2 : ℝ) ^ smallSupport.card := by
      rw [omittedEuler_modulus_rpow_eq, hcorrection]
    _ ≤ (modulusNorm m : ℝ) ^ ε * B := by
      exact mul_le_mul_of_nonneg_left hsmallpow (by positivity)
    _ = B * (modulusNorm m : ℝ) ^ ε := by ring

end ArtinPrimitiveRoots.Proofs.HK_MISC_P
