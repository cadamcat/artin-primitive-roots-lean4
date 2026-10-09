import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawFreshMass
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Mass

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- The second goodness test bounds the exceptional mass in the finite fresh
draw sum appearing after the actual edge-choice reindexing. -/
theorem raw_bad_fresh_nu_mass_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (p : PrimeLists S.x K) (r : ℝ) (I : Finset (Fin K)) (hI : I.Nonempty)
    (hV : ∀ i, 0 < bandMass S.x (F.a i))
    (hb : ∀ i, ∀ t ∈ primeBand S.x (F.a i),
      (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d t)
    (hgood : goodTestTwo S.x (S.d₀ : ℝ) K F.a p r) :
    (∑ fresh : RawFreshLabels S.x F.a I,
      if ∃ n₁ n₂,
        IsGoodnessTrialValue F.a p (S.d₀ : ℝ) I (I.max' hI)
          (rawFreshFunction S.x F.a I fresh) n₁ ∧
        IsGoodnessTrialValue F.a p (S.d₀ : ℝ) I (I.max' hI)
          (rawFreshFunction S.x F.a I fresh) n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤
          100 * Real.exp (-Real.rpow S.L (F.a (I.max' hI)))
      then ∏ i : Fin K, if i ∉ I then
        memoryNu S.x K F.a F.q_d i (rawFreshFunction S.x F.a I fresh i) else 1
      else 0) ≤
      (2 : ℝ) ^ K * Real.exp (-(1 / 4 : ℝ) * Real.rpow S.L (F.a (I.max' hI))) := by
  let bad (g : Fin K → ℕ) : Prop := ∃ n₁ n₂,
    IsGoodnessTrialValue F.a p (S.d₀ : ℝ) I (I.max' hI) g n₁ ∧
    IsGoodnessTrialValue F.a p (S.d₀ : ℝ) I (I.max' hI) g n₂ ∧ n₁ ≠ n₂ ∧
    circleDistance (((n₁ : ℝ) - n₂) * r) ≤
      100 * Real.exp (-Real.rpow S.L (F.a (I.max' hI)))
  let W (g : Fin K → ℕ) : ℝ :=
    ∏ i : Fin K, if i ∉ I then memoryNu S.x K F.a F.q_d i (g i) else 1
  change (∑ fresh : RawFreshLabels S.x F.a I,
    if bad (rawFreshFunction S.x F.a I fresh)
    then W (rawFreshFunction S.x F.a I fresh) else 0) ≤ _
  calc
    _ = ∑' g : Fin K → ℕ, if IsFreshChoice S.x F.a I g
        then (if bad g then W g else 0) else 0 :=
      raw_fresh_sum_reindex S.x F.a I (fun g => if bad g then W g else 0)
    _ = ∑' g : Fin K → ℕ,
        if IsFreshChoice S.x F.a I g ∧ bad g then W g else 0 := by
      simp only [ite_and]
    _ ≤ _ := pd4c_bad_fresh_nu_mass S.x (S.d₀ : ℝ) F.a F.q_d p r I hI hV hb hgood

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
