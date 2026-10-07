import ArtinPrimitiveRoots.Splitting.ZeroFree

/-! `spl:field-bounds`, moved here on 2026-10-07 (statement unchanged): its proof assembles the
compositum and the zero-free descent of `Splitting/ZeroFree.lean`, which imports
`Splitting/Algebraic.lean`, so in `Algebraic.lean` it could never be proved (lane `sol-thin-s7`). -/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ArtinPrimitiveRoots.Ext.SplittingInputs

/-- **`spl:field-bounds`**, `07-splitting.tex:19-99`. There are thresholds and constants
depending only on `a` such that, for every sufficiently large prime `q`, the degree and
discriminant estimates and the inherited zero-free region hold. The unramifiedness clause is not
consumed by §7's splitting test. -/
theorem spl_field_bounds (a : ℤ) (ha : 1 < |a|) :
    ∃ qₐ : ℕ, ∃ C : ℝ, 5 ≤ qₐ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q], q.Prime → qₐ ≤ q →
        kummerDegree a q = q * (q - 1) ∧
        absoluteDiscriminant (kummerField a q) ≤
          (q : ℝ) ^ (q * (q - 2)) *
            ((q : ℝ) ^ q * (a.natAbs : ℝ) ^ (q - 1)) ^ (q - 1) ∧
        Real.log (absoluteDiscriminant (kummerField a q)) + kummerDegree a q ≤
          C * (kummerDegree a q : ℝ) * Real.log (2 * (q : ℝ)) ∧
        IsGalois ℚ (kummerField a q) ∧
        (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * (q : ℤ) →
          (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 (kummerField a q)) = 1) ∧
        ∀ s : ℂ, 1 - ArtinPrimitiveRoots.HeckeBoundary.δ₀ < s.re → s ≠ 1 →
          meromorphicOrderAt (dedekindZetaSharp (kummerField a q)) s ≤ 0 := by
  obtain ⟨C, hC, hdiscAll⟩ := spl_discriminant_bound a ha
  let qₐ : ℕ := max 5 (a.natAbs + 1)
  have hqₐ : 5 ≤ qₐ := by dsimp [qₐ]; exact le_max_left _ _
  refine ⟨qₐ, C, hqₐ, hC, ?_⟩
  intro q _ hq hqa
  have hqLarge : Nat.log2 a.natAbs < q := by
    have hlog : Nat.log2 a.natAbs ≤ a.natAbs := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_le_self 2 a.natAbs
    have hNat : a.natAbs + 1 ≤ q := (le_max_right 5 (a.natAbs + 1)).trans hqa
    omega
  have hdegree : kummerDegree a q = q * (q - 1) := by
    obtain ⟨_, _, _, hdeg, _⟩ := spl_kummer_degree a ha q hq hqLarge
    exact hdeg
  have hdiscLog := hdiscAll q hq hqLarge
  have hGalois : IsGalois ℚ (kummerField a q) := kummer_isGalois_rat a q
  haveI : IsGalois ℚ (kummerField a q) := hGalois
  have hUnram : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a * (q : ℤ) →
      (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 (kummerField a q)) = 1 := by
    intro p hp hpaq
    have hpNotAInt : ¬ (p : ℤ) ∣ a := by
      intro hpa
      exact hpaq (dvd_mul_of_dvd_left hpa (q : ℤ))
    have hpNotQInt : ¬ (p : ℤ) ∣ (q : ℤ) := by
      intro hpq
      exact hpaq (dvd_mul_of_dvd_right hpq a)
    have hpNotA : ¬ p ∣ a.natAbs := by
      intro hpa
      exact hpNotAInt (Int.natCast_dvd.mpr hpa)
    have hpNotQ : ¬ p ∣ q := by
      intro hpq
      exact hpNotQInt (Int.natCast_dvd_natCast.mpr hpq)
    have hpNotU : ¬ p ∣
        q ^ (q * (q - 2)) * (q ^ q * a.natAbs ^ (q - 1)) ^ (q - 1) := by
      intro hpU
      rcases hp.dvd_mul.mp hpU with hqpow | hother
      · exact hpNotQ (hp.dvd_of_dvd_pow hqpow)
      · have hprod : p ∣ q ^ q * a.natAbs ^ (q - 1) := hp.dvd_of_dvd_pow hother
        rcases hp.dvd_mul.mp hprod with hqpow | hapow
        · exact hpNotQ (hp.dvd_of_dvd_pow hqpow)
        · exact hpNotA (hp.dvd_of_dvd_pow hapow)
    have hdiscDvd := (kummer_discriminant_bound a ha q hq hqLarge).2
    have hpNotDiscNat : ¬ p ∣ (NumberField.discr (kummerField a q)).natAbs := by
      intro hd
      exact hpNotU (dvd_trans hd hdiscDvd)
    have hpInt : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpNotDiscInt : ¬ (p : ℤ) ∣ NumberField.discr (kummerField a q) := by
      intro hd
      have hdAbs : (p : ℤ) ∣ ((NumberField.discr (kummerField a q)).natAbs : ℤ) :=
        Int.dvd_natAbs.mpr hd
      exact hpNotDiscNat (Int.natCast_dvd_natCast.mp hdAbs)
    have hUnramIn : Algebra.IsUnramifiedIn (𝓞 (kummerField a q))
        (Ideal.span {(p : ℤ)}) :=
      (NumberField.not_dvd_discr_iff_isUnramifiedIn (kummerField a q)
        (𝓞 (kummerField a q)) hpInt).mp hpNotDiscInt
    have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    letI : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hpne).mpr hpInt
    obtain ⟨⟨P, _, hPover⟩⟩ :=
      (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 (kummerField a q))
    have hPidx : P.ramificationIdx ℤ = 1 := hUnramIn.ramificationIdx_eq_one hPover
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P
      Gal(kummerField a q / ℚ)]
    exact hPidx
  refine ⟨hdegree, hdiscLog.1, hdiscLog.2, hGalois, hUnram, ?_⟩
  letI : NeZero (12 * q) := ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
  have hq5 : 5 ≤ q := hqₐ.trans hqa
  obtain ⟨dK, dF, hrest⟩ := sp_compositum a ha q hq hq5
  letI : AbelianExtensionData (kummerField a q) (compositumField a q) := dK
  letI : AbelianExtensionData (heckeBaseField q) (compositumField a q) := dF
  rcases hrest with ⟨hTC_K, hTC_F, hTC_L, hFdegree, hFpow, hKpow, hKcard⟩
  obtain ⟨m, Art, Ef, X, hsurj, hFrob, hAnalytic, hEnonzero, hEuler, hchars, hcharCont,
    hTop⟩ := sp_upstairs_factor a q hq hq5
  letI : IsTotallyComplex (kummerField a q) := hTC_K
  obtain ⟨Q, hQ, hfactor⟩ := sp_quotient_factor a q hq hq5
  have hzero := spl_kummer_zero_free a q hq hq5 hTop Q hQ hfactor
  intro s hs hsne
  exact hzero s hs

end ArtinPrimitiveRoots.Splitting

end
