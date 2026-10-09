import ArtinPrimitiveRoots.Splitting.Proofs.S7_MELLIN.GammaLines
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».PrefactorDeriv

set_option autoImplicit false

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The two reflected prefactors have a uniform signature-linear bound. -/
theorem prefactor_reflection_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (K : Type*) [Field K] [NumberField K] (t : ℝ), t ≠ 0 →
      ‖deriv (dedekindPrefactor K) ((-1 / 2 : ℝ) + t * Complex.I) /
        dedekindPrefactor K ((-1 / 2 : ℝ) + t * Complex.I)‖ +
      ‖deriv (dedekindPrefactor K) ((3 / 2 : ℝ) + (-t) * Complex.I) /
        dedekindPrefactor K ((3 / 2 : ℝ) + (-t) * Complex.I)‖ ≤
      Real.log (absoluteDiscriminant K) +
        A * Module.finrank ℚ K * Real.log (2 + |t|) := by
  obtain ⟨B, hB, hgamma⟩ := gamma_reflection_line_bound
  let p : ℝ := |Real.log Real.pi| / 2
  let q : ℝ := |Real.log (2 * Real.pi)|
  let L₀ : ℝ := Real.log 2
  let E : ℝ := 2 * p + q
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := abs_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL₀ : 0 < L₀ := Real.log_pos (by norm_num)
  let A : ℝ := B + E / L₀ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro K _ _ t ht
  let r : ℝ := NumberField.InfinitePlace.nrRealPlaces K
  let c : ℝ := NumberField.InfinitePlace.nrComplexPlaces K
  let n : ℝ := Module.finrank ℚ K
  let D : ℝ := Real.log (absoluteDiscriminant K)
  let L : ℝ := Real.log (2 + |t|)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hdim : r + 2 * c = n := by
    dsimp only [r, c, n]
    exact_mod_cast NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hrn : r ≤ n := by linarith only [hdim, hc]
  have hcn : 2 * c ≤ n := by linarith only [hdim, hr]
  have hDOne : 1 ≤ absoluteDiscriminant K := by
    have hNat : 1 ≤ (NumberField.discr K).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
    simpa [absoluteDiscriminant, Nat.cast_natAbs] using
      (show (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) by exact_mod_cast hNat)
  have hlogD : 0 ≤ Real.log (absoluteDiscriminant K) := Real.log_nonneg hDOne
  have hLge : L₀ ≤ L :=
    Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by linarith [abs_nonneg t])
  have hL : 0 < L := hL₀.trans_le hLge
  have hpref (z : ℂ) (hzim : z.im ≠ 0)
      (hRe : z.re = (-1 / 2 : ℝ) ∨ z.re = (3 / 2 : ℝ))
      (him : |z.im| = |t|) :
      ‖deriv (dedekindPrefactor K) z / dedekindPrefactor K z‖ ≤
        D / 2 + r * (p + B * L / 2) + c * (q + B * L) := by
    have hfullRe : z.re = (-1 / 2 : ℝ) ∨ z.re = (-1 / 4 : ℝ) ∨
        z.re = (3 / 4 : ℝ) ∨ z.re = (3 / 2 : ℝ) := by
      rcases hRe with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    have hfull : ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤ B * L := by
      simpa only [him] using hgamma z hfullRe
    have hhalfRe : (z / 2).re = (-1 / 2 : ℝ) ∨ (z / 2).re = (-1 / 4 : ℝ) ∨
        (z / 2).re = (3 / 4 : ℝ) ∨ (z / 2).re = (3 / 2 : ℝ) := by
      rcases hRe with h | h
      · right; left
        rw [Complex.div_ofNat_re, h]
        norm_num
      · right; right; left
        rw [Complex.div_ofNat_re, h]
        norm_num
    have hhalfIm : |(z / 2).im| = |z.im| / 2 := by
      rw [Complex.div_ofNat_im, abs_div, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    have hloghalf : Real.log (2 + |(z / 2).im|) ≤ L := by
      apply Real.log_le_log (by positivity : 0 < 2 + |(z / 2).im|)
      rw [hhalfIm, him]
      linarith only [abs_nonneg t]
    have hhalf : ‖deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)‖ ≤ B * L :=
      (hgamma (z / 2) hhalfRe).trans
        (mul_le_mul_of_nonneg_left hloghalf hB.le)
    let R : ℂ := -(Real.log Real.pi : ℂ) / 2 +
      (deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) / 2
    let Q : ℂ := -(Real.log (2 * Real.pi) : ℂ) +
      deriv Complex.Gamma z / Complex.Gamma z
    have hhalfDiv : ‖(deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) / 2‖ ≤
        B * L / 2 := by
      rw [norm_div, Complex.norm_two]
      exact div_le_div_of_nonneg_right hhalf (by norm_num)
    have hR : ‖R‖ ≤ p + B * L / 2 := by
      calc
        ‖R‖ ≤ ‖-(Real.log Real.pi : ℂ) / 2‖ +
            ‖(deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) / 2‖ :=
          norm_add_le _ _
        _ = p + ‖(deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)) / 2‖ := by
          simp [p, norm_div, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ p + B * L / 2 := add_le_add le_rfl hhalfDiv
    have hQ : ‖Q‖ ≤ q + B * L := by
      calc
        ‖Q‖ ≤ ‖-(Real.log (2 * Real.pi) : ℂ)‖ +
            ‖deriv Complex.Gamma z / Complex.Gamma z‖ := norm_add_le _ _
        _ = q + ‖deriv Complex.Gamma z / Complex.Gamma z‖ := by
          simp [q, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ q + B * L := add_le_add le_rfl hfull
    have hPform : deriv (dedekindPrefactor K) z / dedekindPrefactor K z =
        (Real.log (absoluteDiscriminant K) : ℂ) / 2 +
          (NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R +
          (NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q :=
      (prefactor_logderiv K hzim).2.2
    rw [hPform]
    calc
      _ ≤ ‖(Real.log (absoluteDiscriminant K) : ℂ) / 2 +
            (NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R‖ +
          ‖(NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q‖ := norm_add_le _ _
      _ ≤ (‖(Real.log (absoluteDiscriminant K) : ℂ) / 2‖ +
            ‖(NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R‖) +
          ‖(NumberField.InfinitePlace.nrComplexPlaces K : ℂ) * Q‖ := by
        have h := norm_add_le ((Real.log (absoluteDiscriminant K) : ℂ) / 2)
          ((NumberField.InfinitePlace.nrRealPlaces K : ℂ) * R)
        linarith only [h]
      _ = D / 2 + r * ‖R‖ + c * ‖Q‖ := by
        simp [D, r, c, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlogD]
      _ ≤ D / 2 + r * (p + B * L / 2) + c * (q + B * L) := by
        have h₁ := mul_le_mul_of_nonneg_left hR hr
        have h₂ := mul_le_mul_of_nonneg_left hQ hc
        linarith only [h₁, h₂]
  have hleft := hpref ((-1 / 2 : ℝ) + t * Complex.I)
    (by simpa using ht) (Or.inl (by simp)) (by simp)
  have hright := hpref ((3 / 2 : ℝ) + (-t) * Complex.I)
    (by simpa using ht) (Or.inr (by simp)) (by simp)
  have hsum :
      ‖deriv (dedekindPrefactor K) ((-1 / 2 : ℝ) + t * Complex.I) /
        dedekindPrefactor K ((-1 / 2 : ℝ) + t * Complex.I)‖ +
      ‖deriv (dedekindPrefactor K) ((3 / 2 : ℝ) + (-t) * Complex.I) /
        dedekindPrefactor K ((3 / 2 : ℝ) + (-t) * Complex.I)‖ ≤
      D + 2 * r * p + 2 * c * q + n * B * L := by
    calc
      _ ≤ (D / 2 + r * (p + B * L / 2) + c * (q + B * L)) +
          (D / 2 + r * (p + B * L / 2) + c * (q + B * L)) := add_le_add hleft hright
      _ = D + 2 * r * p + 2 * c * q + (r + 2 * c) * B * L := by ring
      _ = D + 2 * r * p + 2 * c * q + n * B * L := by rw [hdim]
  have hconst : 2 * r * p + 2 * c * q ≤ n * E := by
    have h₁ := mul_le_mul_of_nonneg_right hrn hp
    have h₂ := mul_le_mul_of_nonneg_right hcn hq
    dsimp only [E]
    nlinarith only [h₁, h₂]
  have habsorb : E ≤ (E / L₀) * L := by
    have h := mul_le_mul_of_nonneg_left hLge (div_nonneg hE hL₀.le)
    have heq : (E / L₀) * L₀ = E := by field_simp [hL₀.ne']
    rwa [heq] at h
  have hnabsorb : n * E ≤ n * ((E / L₀) * L) :=
    mul_le_mul_of_nonneg_left habsorb hn
  calc
    _ ≤ D + 2 * r * p + 2 * c * q + n * B * L := hsum
    _ ≤ D + n * E + n * B * L := by linarith only [hconst]
    _ ≤ D + n * ((E / L₀) * L) + n * B * L :=
      add_le_add (add_le_add le_rfl hnabsorb) le_rfl
    _ ≤ D + n * ((E / L₀) * L) + n * B * L + n * L :=
      le_add_of_nonneg_right (mul_nonneg hn hL.le)
    _ = D + A * n * L := by dsimp only [A]; ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
