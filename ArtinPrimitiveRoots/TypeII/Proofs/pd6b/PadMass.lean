import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def padAllowedMass (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (ta tb : Fin K → ℕ) : ℝ :=
  ∑ d : PadChoice x K a, if PadChoiceGood d ta tb then padChoiceWeight x a d else 0

/-- An allowed-pad mass is a probability; its deficit is exactly the forbidden-pad mass. -/
theorem padAllowedMass_bounds {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (ta tb : Fin K → ℕ) :
    0 ≤ padAllowedMass x a ta tb ∧ padAllowedMass x a ta tb ≤ 1 ∧
      1 - padAllowedMass x a ta tb =
        ∑ d : PadChoice x K a, if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d := by
  have hw (d : PadChoice x K a) : 0 ≤ padChoiceWeight x a d := by
    unfold padChoiceWeight padAtomWeight
    apply Finset.prod_nonneg
    intro q hq
    have hv := (hV q.1).le
    exact div_nonneg (by norm_num) (mul_nonneg hv (Nat.cast_nonneg _))
  have hgood : 0 ≤ padAllowedMass x a ta tb := by
    unfold padAllowedMass
    exact Finset.sum_nonneg (fun d hd => by split_ifs; exact hw d; exact le_rfl)
  have hbad : 0 ≤ (∑ d : PadChoice x K a, if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d) :=
    Finset.sum_nonneg (fun d hd => by split_ifs; exact le_rfl; exact hw d)
  have htotal : padAllowedMass x a ta tb +
      (∑ d : PadChoice x K a, if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d) = 1 := by
    unfold padAllowedMass
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ d : PadChoice x K a, padChoiceWeight x a d := by
        apply Finset.sum_congr rfl
        intro d hd
        split_ifs <;> simp
      _ = 1 := padChoiceWeight_sum_eq_one a hV
  exact ⟨hgood, by linarith, by linarith⟩

/-- A forbidden-mass bound controls the scalar loss in each signed pad-summed term. -/
theorem padAllowedMass_scalar_loss {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (ta tb : Fin K → ℕ) (ε : ℝ)
    (hbad : (∑ d : PadChoice x K a,
      if PadChoiceGood d ta tb then 0 else padChoiceWeight x a d) ≤ ε) :
    ‖((padAllowedMass x a ta tb : ℝ) : ℂ) - 1‖ ≤ ε := by
  obtain ⟨hlo, hhi, hdef⟩ := padAllowedMass_bounds a hV ta tb
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : padAllowedMass x a ta tb - 1 ≤ 0)]
  linarith


/-- Summing the allowed harmonic pad weights gives their complex scalar mass. -/
theorem padAllowedMass_complex_sum {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (ta tb : Fin K → ℕ) (z : ℂ) :
    (∑ d : PadChoice x K a, if PadChoiceGood d ta tb then (padChoiceWeight x a d : ℂ) * z else 0) =
      (padAllowedMass x a ta tb : ℂ) * z := by
  have hpoint (d : PadChoice x K a) :
      (if PadChoiceGood d ta tb then (padChoiceWeight x a d : ℂ) * z else 0) =
        ((if PadChoiceGood d ta tb then padChoiceWeight x a d else 0 : ℝ) : ℂ) * z := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_mul]
  congr 1
  exact (map_sum Complex.ofRealHom _ _).symm

end
end ArtinPrimitiveRoots.TypeII.PD
