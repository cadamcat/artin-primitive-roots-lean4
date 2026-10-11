import ArtinPrimitiveRoots.Proofs.pd_life_b.HistoryPaths
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_ordered_birth_bijection
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_history_scalar_charge
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_life_memory_bound

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_life_b
noncomputable section

/-- Lifespan selectors omit only assignments with more than B-KN ghost births, yielding
the doubled finite choice majorant. The complete error decomposes over contributing paths.
Uses
pd_ordered_birth_bijection and pd_history_scalar_charge; feeds pd_truncation_tail_absorb.
Factor the common signed path coefficient before taking the norm. -/
theorem pd_truncation_choice_majorant (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ B : ℕ, K * pathLength S.x ≤ B →
          (memHistory F S ρ w none none distinctWeight -
              memHistory F S ρ w (some B) none distinctWeight =
            ∑' γ : EnvPath S.x K, if IsContributingPath F S γ then
              memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some B) (some γ) distinctWeight else 0) ∧
          (∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ →
            ‖memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some B) (some γ) distinctWeight‖ ≤
              (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ)) *
                ‖pathCoefficient F S γ‖ * pathArch F S w γ * doubledLifeMajorant F S γ) := by
  classical
  intro K F hF ρ hρ
  obtain ⟨xBirth, hxBirth, hBirth⟩ :=
    pd_ordered_birth_bijection δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xHist, hxHist, hHist⟩ :=
    pd_life_b_history_paths δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨Cb, xRoot, hCb, hxRoot, hRoot⟩ :=
    root_budget δ c₁ c₂ hδ hc₁ K F hF
  obtain ⟨xScalar, hxScalar, hScalar⟩ :=
    pd_history_scalar_charge δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xMemory, hxMemory, hMemory⟩ :=
    pd_life_memory_bound δ c₁ c₂ hδ hc₁ K F hF
  let x₀ := max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
  have hx₀ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have hxBirth₀ : xBirth ≤ x₀ := by
    change xBirth ≤ max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
    calc
      xBirth ≤ max xBirth (max xHist (max xRoot (max xScalar xMemory))) := le_max_left _ _
      _ ≤ _ := le_max_right _ _
  have hxHist₀ : xHist ≤ x₀ := by
    change xHist ≤ max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
    calc
      xHist ≤ max xHist (max xRoot (max xScalar xMemory)) := le_max_left _ _
      _ ≤ max xBirth (max xHist (max xRoot (max xScalar xMemory))) := le_max_right _ _
      _ ≤ _ := le_max_right _ _
  have hxRoot₀ : xRoot ≤ x₀ := by
    change xRoot ≤ max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
    calc
      xRoot ≤ max xRoot (max xScalar xMemory) := le_max_left _ _
      _ ≤ max xHist (max xRoot (max xScalar xMemory)) := le_max_right _ _
      _ ≤ max xBirth (max xHist (max xRoot (max xScalar xMemory))) := le_max_right _ _
      _ ≤ _ := le_max_right _ _
  have hxScalar₀ : xScalar ≤ x₀ := by
    change xScalar ≤ max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
    calc
      xScalar ≤ max xScalar xMemory := le_max_left _ _
      _ ≤ max xRoot (max xScalar xMemory) := le_max_right _ _
      _ ≤ max xHist (max xRoot (max xScalar xMemory)) := le_max_right _ _
      _ ≤ max xBirth (max xHist (max xRoot (max xScalar xMemory))) := le_max_right _ _
      _ ≤ _ := le_max_right _ _
  have hxMemory₀ : xMemory ≤ x₀ := by
    change xMemory ≤ max 2 (max xBirth (max xHist (max xRoot (max xScalar xMemory))))
    calc
      xMemory ≤ max xScalar xMemory := le_max_right _ _
      _ ≤ max xRoot (max xScalar xMemory) := le_max_right _ _
      _ ≤ max xHist (max xRoot (max xScalar xMemory)) := le_max_right _ _
      _ ≤ max xBirth (max xHist (max xRoot (max xScalar xMemory))) := le_max_right _ _
      _ ≤ _ := le_max_right _ _
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx w hw B hKN
  have hxBirth' : xBirth ≤ S.x := hxBirth₀.trans hx
  have hxHist' : xHist ≤ S.x := hxHist₀.trans hx
  have hxRoot' : xRoot ≤ S.x := hxRoot₀.trans hx
  have hxScalar' : xScalar ≤ S.x := hxScalar₀.trans hx
  have hxMemory' : xMemory ≤ S.x := hxMemory₀.trans hx
  obtain ⟨hNorm, hBirthPath⟩ := hBirth S hS hxBirth'
  obtain ⟨hFinite, hCoeffBudget, _⟩ := hRoot S hS hxRoot'
  have hPathNone := hHist S hS hxHist' w hw
  have hPathNone' :
      memHistory F S ρ w none none distinctWeight =
        ∑' γ : EnvPath S.x K,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    simpa [historyDistinct] using hPathNone
  have hPathSome := pd_life_b_history_paths_trunc δ c₁ c₂ B F S ρ w hS hw
  let T : Finset (EnvPath S.x K) := hFinite.toFinset
  have hmemT (γ : EnvPath S.x K) : γ ∈ T ↔ IsContributingPath F S γ := by
    simp [T, Set.Finite.mem_toFinset]
  have hzero (γ : EnvPath S.x K) (hAdm : IsEnvPathAdmissible F S γ)
      (hNot : ¬ IsContributingPath F S γ) :
      memHistory F S ρ w none (some γ) distinctWeight = 0 ∧
        memHistory F S ρ w (some B) (some γ) distinctWeight = 0 := by
    have h0 := hBirthPath w hw γ hAdm none
    have hB := hBirthPath w hw γ hAdm (some B)
    by_cases hcoef : pathCoefficient F S γ = 0
    · constructor
      · rw [h0]
        simp [hcoef]
      · rw [hB]
        simp [hcoef]
    · have hArch : pathArch F S w γ = 0 := by
        by_contra hArch
        apply hNot
        exact ⟨hAdm, hcoef, ⟨w, hw, hArch⟩⟩
      constructor
      · rw [h0]
        simp [hArch]
      · rw [hB]
        simp [hArch]
  have hFiniteNoneIndicator :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w none (some γ) distinctWeight else 0) =
        ∑ γ ∈ T,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · by_cases hContrib : IsContributingPath F S γ
      · exact (hγ ((hmemT γ).2 hContrib)).elim
      · simp [hAdm, (hzero γ hAdm hContrib).1]
    · simp [hAdm]
  have hFiniteNone :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w none (some γ) distinctWeight else 0) =
        ∑ γ ∈ T, memHistory F S ρ w none (some γ) distinctWeight := by
    rw [hFiniteNoneIndicator]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hContrib : IsContributingPath F S γ := (hmemT γ).1 hγ
    simp [hContrib.1]
  have hFiniteCutIndicator :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w (some B) (some γ) distinctWeight else 0) =
        ∑ γ ∈ T,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w (some B) (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · by_cases hContrib : IsContributingPath F S γ
      · exact (hγ ((hmemT γ).2 hContrib)).elim
      · simp [hAdm, (hzero γ hAdm hContrib).2]
    · simp [hAdm]
  have hFiniteCut :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w (some B) (some γ) distinctWeight else 0) =
        ∑ γ ∈ T, memHistory F S ρ w (some B) (some γ) distinctWeight := by
    rw [hFiniteCutIndicator]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hContrib : IsContributingPath F S γ := (hmemT γ).1 hγ
    simp [hContrib.1]
  have hFiniteDecomp :
      memHistory F S ρ w none none distinctWeight -
          memHistory F S ρ w (some B) none distinctWeight =
        ∑ γ ∈ T,
          (memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some B) (some γ) distinctWeight) := by
    rw [hPathNone', hPathSome, hFiniteNone, hFiniteCut]
    rw [← Finset.sum_sub_distrib]
  have hContribSumIndicator :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then
          memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some B) (some γ) distinctWeight else 0) =
        ∑ γ ∈ T,
          if IsContributingPath F S γ then
            memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some B) (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    have hNot : ¬ IsContributingPath F S γ := by
      intro hC
      exact hγ ((hmemT γ).2 hC)
    simp [hNot]
  have hContribSum :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then
          memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some B) (some γ) distinctWeight else 0) =
        ∑ γ ∈ T,
          (memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some B) (some γ) distinctWeight) := by
    rw [hContribSumIndicator]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hContrib : IsContributingPath F S γ := (hmemT γ).1 hγ
    simp [hContrib]
  have hFirst :
      memHistory F S ρ w none none distinctWeight -
          memHistory F S ρ w (some B) none distinctWeight =
        ∑' γ : EnvPath S.x K,
          if IsContributingPath F S γ then
            memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some B) (some γ) distinctWeight else 0 := by
    rw [hFiniteDecomp, hContribSum]
  refine ⟨hFirst, ?_⟩
  intro γ hAdm
  by_cases hcoef : pathCoefficient F S γ = 0
  · have h0 := hBirthPath w hw γ hAdm none
    have hB := hBirthPath w hw γ hAdm (some B)
    rw [h0, hB]
    simp [hcoef]
  · by_cases harch : pathArch F S w γ = 0
    · have h0 := hBirthPath w hw γ hAdm none
      have hB := hBirthPath w hw γ hAdm (some B)
      rw [h0, hB]
      simp [harch]
    · have hContrib : IsContributingPath F S γ :=
        ⟨hAdm, hcoef, ⟨w, hw, harch⟩⟩
      have hScalarPath := hScalar S hS hxScalar' γ hAdm hcoef
      have hMemoryPath := hMemory S hS hxMemory' γ hAdm hcoef
      let lifeTail : ℝ :=
        ∑ H : PDLifeAssignment F S γ,
          if pdLifeMaxMemory F S γ H ≤ B then 0 else pdLifeAssignmentCharge F S γ H
      let tailFactor : ℝ := (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ))
      have hRawDiff :
          pdRawHistorySum F S ρ γ none - pdRawHistorySum F S ρ γ (some B) =
            pdActiveNormalization F S * lifeTail := by
        unfold pdRawHistorySum
        rw [← Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro H hH
        have hCharge := hScalarPath H
        by_cases hcut : pdLifeMaxMemory F S γ H ≤ B
        · simp [hcut, hCharge, lifeTail] <;> ring
        · simp [hcut, hCharge, lifeTail] <;> ring
      have hcancel :
          (pdActiveNormalization F S)⁻¹ *
              (pdRawHistorySum F S ρ γ none - pdRawHistorySum F S ρ γ (some B)) =
            lifeTail := by
        rw [hRawDiff]
        calc
          _ = ((pdActiveNormalization F S)⁻¹ * pdActiveNormalization F S) * lifeTail := by ring
          _ = lifeTail := by rw [inv_mul_cancel₀ hNorm]; ring
      have hBirthNone := hBirthPath w hw γ hAdm none
      have hBirthCut := hBirthPath w hw γ hAdm (some B)
      have hDelta :
          memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some B) (some γ) distinctWeight =
            pathCoefficient F S γ * (pathArch F S w γ : ℂ) * (lifeTail : ℂ) := by
        rw [hBirthNone, hBirthCut]
        have hcancelC :
            (((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ none : ℝ) : ℂ) -
                (((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ (some B) : ℝ) : ℂ) =
              (lifeTail : ℂ) := by
          have hsubReal :
              (pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ none -
                  (pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ (some B) =
                lifeTail := by
            calc
              _ = (pdActiveNormalization F S)⁻¹ *
                    (pdRawHistorySum F S ρ γ none - pdRawHistorySum F S ρ γ (some B)) := by ring
              _ = lifeTail := hcancel
          simpa only [Complex.ofReal_sub] using
            (congrArg (fun x : ℝ => (x : ℂ)) hsubReal)
        calc
          _ = pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
                ((((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ none : ℝ) : ℂ) -
                  (((pdActiveNormalization F S)⁻¹ * pdRawHistorySum F S ρ γ (some B : Option ℕ) : ℝ) : ℂ)) := by
                push_cast
                ring
          _ = _ := by rw [hcancelC]
      have hArchNonneg : 0 ≤ pathArch F S w γ := by
        unfold pathArch
        exact Finset.prod_nonneg fun j hj => by split_ifs <;> norm_num
      have hLifeAbs : |lifeTail| ≤ tailFactor * doubledLifeMajorant F S γ := by
        have hTerm (H : PDLifeAssignment F S γ) :
            (if pdLifeMaxMemory F S γ H ≤ B then 0 else
              |pdLifeAssignmentCharge F S γ H|) ≤
              tailFactor * ((2 : ℝ) ^ pdLifeGhostBirths F S γ H *
                |pdLifeAssignmentCharge F S γ H|) := by
          by_cases hcut : pdLifeMaxMemory F S γ H ≤ B
          · simp [hcut]
            positivity
          · have hMem := hMemoryPath H
            have hExpNat : B ≤ K * pathLength S.x + pdLifeGhostBirths F S γ H := by
              have hlt : B < pdLifeMaxMemory F S γ H := Nat.lt_of_not_ge hcut
              omega
            have hExpCast : (B : ℤ) ≤
                ((K * pathLength S.x + pdLifeGhostBirths F S γ H : ℕ) : ℤ) := by
              exact_mod_cast hExpNat
            have hExp : 0 ≤ -(B : ℤ) + (K * pathLength S.x : ℤ) +
                (pdLifeGhostBirths F S γ H : ℤ) := by
              omega
            have hPow :
                1 ≤ (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ) +
                  (pdLifeGhostBirths F S γ H : ℤ)) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hExp
            have hPowFactor :
                1 ≤ tailFactor * (2 : ℝ) ^ pdLifeGhostBirths F S γ H := by
              have hsplit := zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)
                (-(B : ℤ) + (K * pathLength S.x : ℤ))
                (pdLifeGhostBirths F S γ H : ℤ)
              have hsplit' :
                  (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ) +
                    (pdLifeGhostBirths F S γ H : ℤ)) =
                    tailFactor * (2 : ℝ) ^ pdLifeGhostBirths F S γ H := by
                simpa [tailFactor, zpow_natCast] using hsplit
              rw [← hsplit']
              exact hPow
            calc
              _ = 1 * |pdLifeAssignmentCharge F S γ H| := by simp [hcut]
              _ ≤ (tailFactor * (2 : ℝ) ^ pdLifeGhostBirths F S γ H) *
                    |pdLifeAssignmentCharge F S γ H| :=
                    mul_le_mul_of_nonneg_right hPowFactor (abs_nonneg _)
              _ = _ := by ring
        have hsum :
            (∑ H : PDLifeAssignment F S γ,
              if pdLifeMaxMemory F S γ H ≤ B then 0 else
                |pdLifeAssignmentCharge F S γ H|) ≤
              ∑ H : PDLifeAssignment F S γ,
                tailFactor * ((2 : ℝ) ^ pdLifeGhostBirths F S γ H *
                  |pdLifeAssignmentCharge F S γ H|) := by
          apply Finset.sum_le_sum
          intro H hH
          exact hTerm H
        have htriangle :
            |lifeTail| ≤
              ∑ H : PDLifeAssignment F S γ,
                (if pdLifeMaxMemory F S γ H ≤ B then 0 else
                  |pdLifeAssignmentCharge F S γ H|) := by
          dsimp [lifeTail]
          calc
            _ ≤ ∑ H : PDLifeAssignment F S γ,
                  |if pdLifeMaxMemory F S γ H ≤ B then 0 else
                    pdLifeAssignmentCharge F S γ H| :=
                    Finset.abs_sum_le_sum_abs _ _
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro H hH
                  by_cases hcut : pdLifeMaxMemory F S γ H ≤ B <;> simp [hcut]
        calc
          _ ≤ _ := htriangle.trans (by simpa using hsum)
          _ = _ := by
            rw [← pd_life_b_doubled_assignment_sum F S γ]
            rw [Finset.mul_sum]
      have hNormDelta :
          ‖memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some B) (some γ) distinctWeight‖ =
            ‖pathCoefficient F S γ‖ * pathArch F S w γ * |lifeTail| := by
        rw [hDelta, norm_mul, norm_mul]
        simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hArchNonneg]
      calc
        _ = ‖pathCoefficient F S γ‖ * pathArch F S w γ * |lifeTail| := hNormDelta
        _ ≤ ‖pathCoefficient F S γ‖ * pathArch F S w γ *
              (tailFactor * doubledLifeMajorant F S γ) := by
              apply mul_le_mul_of_nonneg_left hLifeAbs
              exact mul_nonneg (norm_nonneg _) hArchNonneg
        _ = tailFactor * ‖pathCoefficient F S γ‖ * pathArch F S w γ *
              doubledLifeMajorant F S γ := by ring

end
end ArtinPrimitiveRoots.TypeII.PD
