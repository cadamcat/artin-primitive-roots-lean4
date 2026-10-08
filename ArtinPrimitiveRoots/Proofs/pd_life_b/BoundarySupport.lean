import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.Proofs.pd_life_b
open ArtinPrimitiveRoots.TypeII.PD
open Classical MeasureTheory
noncomputable section

private theorem pd_life_b_tsum_zero_of_eq_zero {α : Type*} (f : α → ℂ)
    (hf : ∀ a, f a = 0) : (∑' a, f a) = 0 := by
  have hfun : f = fun _ => 0 := funext hf
  rw [hfun]
  simp

/-- The fixed-path history vanishes when the prescribed initial position is not the
left boundary position. `logHistoryFn` tests visit zero at its outermost recursive step,
while `logBoundaryIn` is supported at `(1,0)`. -/
theorem pd_life_b_memHistory_zero_of_start_ne_e1 {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (B : Option ℕ)
    (γ : EnvPath S.x K) (W : BirthLog K → ℂ)
    (hstart : (γ 0).1 ≠ (1, 0)) :
    memHistory F S ρ w B (some γ) W = 0 := by
  classical
  unfold memHistory logInner
  apply pd_life_b_tsum_zero_of_eq_zero
  intro σL
  by_cases hb : logBoundaryIn σL = 0
  · simp [hb]
  · have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hbnd : memBoundary σL.1 ≠ 0 := by
      simpa [logBoundaryIn, hlog] using hb
    have hz : σL.1.1 = (1, 0) := by
      by_contra hn
      apply hbnd
      simp [memBoundary, hn]
    have hcurrent : (σL.1.1, σL.1.2.1) ≠ γ 0 := by
      intro heq
      apply hstart
      calc
        (γ 0).1 = σL.1.1 := (congrArg Prod.fst heq).symm
        _ = (1, 0) := hz
    have hhist : logHistoryFn F S ρ w B (some γ) W (pathLength S.x) σL = 0 := by
      cases hN : pathLength S.x with
      | zero =>
          simp only [logHistoryFn]
          cases B <;> simp [hN, logTrunc, logPathRestrict, hcurrent]
      | succ n =>
          simp only [logHistoryFn]
          cases B <;> simp [hN, logTrunc, logPathRestrict, hcurrent]
    simp [hhist]

end
end ArtinPrimitiveRoots.Proofs.pd_life_b
