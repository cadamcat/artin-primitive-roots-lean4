import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

/-- A zero coefficient family with scales enlarged to the raw absolute-square range. -/
def scaledZeroFamily {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) :
    CoefficientFamily δ C (8 * c₁) (8 * c₂) where
  xMin := family.xMin
  xMin_ge_two := family.xMin_ge_two
  Hm := fun x => 4 * family.Hm x
  Hn := fun x => 2 * family.Hn x
  interval := fun _ => ∅
  alpha := fun _ _ => 0
  interval_property := by intro x; simp [IsNatInterval]
  scales := by
    intro x hx
    rcases family.scales x hx with ⟨hm, hn, hlo, hhi⟩
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (family.xMin_ge_two.trans hx)
    have hpow : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> nlinarith
  interval_bounds := by intro x hx m hm; simp at hm
  rough_support := by intro x hx m hm; exact (hm rfl).elim
  coefficient_bound := by intro x hx m hm; simp at hm

/-- The auxiliary zero family satisfies the long-coefficient input without cancellation. -/
theorem scaledZeroFamily_long {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) :
    HasLongCoefficientCancellation (scaledZeroFamily family) := by
  intro A₀ B A hA₀ hB hA
  refine ⟨1, max 2 family.xMin, by norm_num, le_max_left _ _, le_max_right _ _, ?_⟩
  intro x hx k hk hkmax χ t ht
  have hx₂ : 2 ≤ x := (le_max_left _ _).trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  simpa [scaledZeroFamily] using (Real.rpow_nonneg hlog (-A))

/-- Rescale the frozen progression-divisor estimate to `[Y,4Y]` and `h ≤ 4X/Y`. -/
theorem rawProgression_divisor_bound (δ C c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ Cdiv x₀ : ℝ, 0 < Cdiv ∧ 2 ≤ x₀ ∧
      ∀ family : CoefficientFamily δ C c₁ c₂, ∀ x : ℝ, x₀ ≤ x → family.xMin ≤ x →
        ∀ Y : ℝ, 0 < Y → 2 * Y ∈ dyadicScales x K → ∀ l : ℕ,
          Y ≤ (l : ℝ) → (l : ℝ) ≤ 4 * Y →
          (∑ h ∈ Finset.range (⌊4 * (family.Hm x * family.Hn x) / Y⌋₊ + 1),
            (tau (1 + l * h) : ℝ) ^ 2) ≤
            Cdiv * (family.Hm x * family.Hn x / Y) * Real.rpow (Real.log x) 3 := by
  obtain ⟨CA, Cscale, Cmain, CDiv, x₀, hCA, hCscale, hCmain, hCDiv, hx₀, hdec⟩ :=
    cauchy_decomposition δ C 1 F.q_d (8 * c₁) (8 * c₂) K F.a
      hδ hC (by norm_num) hF.2.1 hF.2.2.1 (by positivity) (by positivity) hF.1
      1 (by norm_num)
  refine ⟨4 * CDiv, x₀, by positivity, hx₀, ?_⟩
  intro family x hx hMin Y hY hdouble l hl₁ hl₂
  have hx₂ : 2 ≤ x := hx₀.trans hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hzeroBeta : ∀ n ∈ dyadicIntegers ((scaledZeroFamily family).Hn x),
      ‖(0 : ℂ)‖ ≤ Real.rpow (Real.log x) C := by
    intro n hn
    simpa using Real.rpow_nonneg hlog C
  have hzeroInvariant : IsMarkedInvariant x K F.a (fun _ => (0 : ℂ)) := by
    constructor
    · intro h; norm_num
    · intro p h hp hprime; rfl
  have hresult := hdec (scaledZeroFamily family) (scaledZeroFamily_long family)
    x hx hMin F.eta hF.2.2.2.2.1.1 hF.2.2.2.2.1.2.1
    hF.2.2.2.2.1.2.2.1 hF.2.2.2.2.1.2.2.2 (fun _ => (0 : ℂ))
    (by intro n hn; exact (hn rfl).elim) hzeroBeta (fun _ => (0 : ℂ)) hzeroInvariant
  have hbound := hresult.2.2.2.1 (2 * Y) hdouble l (by linarith) (by linarith)
  have hquot : (scaledZeroFamily family).Hm x * (scaledZeroFamily family).Hn x /
      (2 * Y) = 4 * (family.Hm x * family.Hn x) / Y := by
    dsimp [scaledZeroFamily]
    field_simp
    <;> ring
  rw [hquot] at hbound
  convert hbound using 1 <;> ring

end
end ArtinPrimitiveRoots.TypeII.PD
