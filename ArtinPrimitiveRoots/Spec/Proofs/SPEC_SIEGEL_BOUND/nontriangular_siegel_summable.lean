import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.nontriangular_rows_unit_orbit
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.balanced_denominator_rows_bound
import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.eis_term_row_kernel_gradient

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem specSiegelB_lowerHeight_pos (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (i : d.ι) : 0 < SiegelData.lowerHeight F d i := by
  let g : SL(2,F) := (d.σ i)⁻¹
  have hrow : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have hd := g.property
    rw [Matrix.det_fin_two] at hd
    simp [h.1, h.2] at hd
  have hI : bottomRowFractionalIdeal F g ≠ 0 := by
    rw [bottomRowFractionalIdeal, FractionalIdeal.spanFinset_ne_zero]
    rcases hrow with h | h
    · exact ⟨0, Finset.mem_univ _, by simpa [bottomRow] using h⟩
    · exact ⟨1, Finset.mem_univ _, by simpa [bottomRow] using h⟩
  have hnorm : FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) ≠ 0 := by
    intro hz
    exact hI (FractionalIdeal.absNorm_eq_zero_iff.mp hz)
  have hnormQ : 0 < FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) :=
    lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnorm)
  have hnormR : 0 < ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F g) : ℚ) : ℝ) := by
    exact_mod_cast hnormQ
  dsimp [SiegelData.lowerHeight]
  exact inv_pos.mpr (mul_pos hnormR d.C_M_pos)

/-- Assemble the uniformly summable nontriangular terms and gradients on one
Siegel set. Guide: `sol-thin-spec/PROOFS.md:351,358–360`. Uses
`nontriangular_rows_unit_orbit`, `balanced_denominator_rows_bound`, and
`eis_term_row_kernel_gradient`; feeds the second conjunct of `E4_eis_siegel`.
For a nonempty parameter compactum use the extrema of `1+2 Re(s)` and `|1+2s|`;
for a nonempty Siegel set its balance constant is nonnegative and lowerHeight positive.
Empty parameter or Siegel sets give C=0. -/
theorem nontriangular_siegel_summable (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F))
    (Kₛ : Set ℂ) (hKₛ : IsCompact Kₛ)
    (hKₛstrip : Kₛ ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3}) (i : d.ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Kₛ, ∀ z ∈ SiegelData.setAt F d i,
      Summable (fun q : NontriangularCosets Γ σ (d.σ i) =>
        ‖eisTerm F Γ σ s ((d.σ i) • z) q.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖) ∧
      (∑' q : NontriangularCosets Γ σ (d.σ i),
        (‖eisTerm F Γ σ s ((d.σ i) • z) q.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s ((d.σ i) • x) q.1) z‖)) ≤ C := by
  by_cases hKne : Kₛ.Nonempty
  · by_cases hSne : (SiegelData.setAt F d i).Nonempty
    · let αfun : ℂ → ℝ := fun s => 1 + 2 * s.re
      have hαcont : Continuous αfun := by fun_prop
      obtain ⟨smin, hsmin, hαminOn⟩ := hKₛ.exists_isMinOn hKne hαcont.continuousOn
      obtain ⟨smax, hsmax, hαmaxOn⟩ := hKₛ.exists_isMaxOn hKne hαcont.continuousOn
      let αmin : ℝ := αfun smin
      let αmax : ℝ := αfun smax
      have hαmin : 2 < αmin := by
        have hs := hKₛstrip hsmin
        dsimp [αmin, αfun]
        rcases hs with ⟨hlo, hhi⟩
        linarith
      have hαmax7 : αmax < 7 := by
        have hs := hKₛstrip hsmax
        dsimp [αmax, αfun]
        rcases hs with ⟨hlo, hhi⟩
        linarith
      have hαrange : αmin ≤ αmax := by
        exact hαminOn hsmax
      have hαbound (s : ℂ) (hs : s ∈ Kₛ) :
          αmin ≤ 1 + 2 * s.re ∧ 1 + 2 * s.re ≤ αmax := by
        exact ⟨hαminOn hs, hαmaxOn hs⟩
      have hnormCont : Continuous (fun s : ℂ => ‖1 + 2 * s‖) := by fun_prop
      obtain ⟨sL, hsL, hLmax⟩ := hKₛ.exists_isMaxOn hKne hnormCont.continuousOn
      let L : ℝ := ‖1 + 2 * sL‖
      have hLbound (s : ℂ) (hs : s ∈ Kₛ) : ‖1 + 2 * s‖ ≤ L := by
        simpa [L] using hLmax hs
      obtain ⟨z₀, hz₀⟩ := hSne
      change ∃ x y, z₀ = ptX' F x y ∧ x ∈ d.P i ∧
        IsBalancedHeights F (2 * d.B i) y ∧
        SiegelData.lowerHeight F d i ≤ normHeight F (ptX' F x y) at hz₀
      obtain ⟨x₀, y₀, _, _, hbal₀, _⟩ := hz₀
      have hBy : 0 ≤ 2 * d.B i := by
        have hW : Nonempty (InfinitePlace F) :=
          Fintype.card_pos_iff.mp Fintype.card_pos
        obtain ⟨w⟩ := hW
        have hdev := hbal₀.2 w
        have hnonneg : 0 ≤ |Real.log (y₀ w) -
            (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
              ∑ w' : InfinitePlace F, Real.log (y₀ w')| := abs_nonneg _
        linarith
      let H : ℝ := SiegelData.lowerHeight F d i
      have hH : 0 < H := by
        exact specSiegelB_lowerHeight_pos Γ d i
      obtain ⟨D, hD, hrowProps, hrowUniq⟩ :=
        nontriangular_rows_unit_orbit Γ σ (d.σ i)
      let v : NontriangularCosets Γ σ (d.σ i) → F × F := fun q =>
        bottomRow F (siegelTransition Γ σ (d.σ i) q.1)
      have hvProps (q : NontriangularCosets Γ σ (d.σ i)) :
          HasDenominatorBound F D (v q).1 ∧ HasDenominatorBound F D (v q).2 := by
        rcases hrowProps q with ⟨_, h₁, h₂⟩
        exact ⟨h₁, h₂⟩
      have hvNe (q : NontriangularCosets Γ σ (d.σ i)) : (v q).1 ≠ 0 :=
        (hrowProps q).1
      have hvUniq (q q' : NontriangularCosets Γ σ (d.σ i))
          (h : unitAssociatedRows F (v q) (v q')) : q = q' :=
        hrowUniq q q' h
      obtain ⟨Crows, hCrows, hrowsBound⟩ :=
        balanced_denominator_rows_bound (F := F) D hD (2 * d.B i) H αmin αmax hBy hH
          (by linarith) hαrange
      refine ⟨(1 + L * Real.sqrt (placeCount F)) * Crows, ?_, ?_⟩
      · exact mul_nonneg (by positivity) hCrows
      · intro s hs z hz
        change ∃ x y, z = ptX' F x y ∧ x ∈ d.P i ∧
          IsBalancedHeights F (2 * d.B i) y ∧
          SiegelData.lowerHeight F d i ≤ normHeight F (ptX' F x y) at hz
        obtain ⟨x, y, rfl, _, hbal, hfloor⟩ := hz
        have hnormy : normHeight F (ptX' F x y) = ∏ w, y w := by
          unfold normHeight
          apply Finset.prod_congr rfl
          intro w hw
          exact height_pt (x w) (y w) (hbal.1 w)
        have hfloor' : H ≤ ∏ w, y w := by
          rw [← hnormy]
          simpa [H] using hfloor
        let α : ℝ := 1 + 2 * s.re
        have hαlo : αmin ≤ α := by simpa [α] using (hαbound s hs).1
        have hαhi : α ≤ αmax := by simpa [α] using (hαbound s hs).2
        obtain ⟨hrowSummable, hrowBound⟩ :=
          hrowsBound α hαlo hαhi v hvProps hvNe hvUniq
            (fun w => x w) (fun w => y w) hbal hfloor'
        let cₛ : ℝ := 1 + ‖1 + 2 * s‖ * Real.sqrt (placeCount F)
        have hcₛ_nonneg : 0 ≤ cₛ := by positivity
        have hcₛ_bound : cₛ ≤ 1 + L * Real.sqrt (placeCount F) := by
          dsimp [cₛ]
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right (hLbound s hs) (Real.sqrt_nonneg _)) 1
        have hpoint (q : NontriangularCosets Γ σ (d.σ i)) :
            (‖eisTerm F Γ σ s ((d.σ i) • (ptX' F x y)) q.1‖ +
              ‖fullGradient F (fun t => eisTerm F Γ σ s ((d.σ i) • t) q.1)
                (ptX' F x y)‖) = cₛ * siegelRowKernel (v q) x y α := by
          obtain ⟨hnorm, hgrad⟩ :=
            eis_term_row_kernel_gradient Γ σ (d.σ i) s q.1 (ptX' F x y)
          have hnorm' :
              ‖eisTerm F Γ σ s ((d.σ i) • (ptX' F x y)) q.1‖ =
                siegelRowKernel (v q) x y α := by
            simpa [v, α, ptX', horiz_pt, height_pt, hbal.1] using hnorm
          rw [hgrad, hnorm']
          dsimp [cₛ]
          ring
        have hfun :
            (fun q : NontriangularCosets Γ σ (d.σ i) =>
              ‖eisTerm F Γ σ s ((d.σ i) • (ptX' F x y)) q.1‖ +
                ‖fullGradient F (fun t => eisTerm F Γ σ s ((d.σ i) • t) q.1)
                  (ptX' F x y)‖) =
            (fun q => cₛ * siegelRowKernel (v q) x y α) := by
          funext q
          exact hpoint q
        have hsum : Summable (fun q : NontriangularCosets Γ σ (d.σ i) =>
            ‖eisTerm F Γ σ s ((d.σ i) • (ptX' F x y)) q.1‖ +
              ‖fullGradient F (fun t => eisTerm F Γ σ s ((d.σ i) • t) q.1)
                (ptX' F x y)‖) := by
          rw [hfun]
          exact hrowSummable.mul_left cₛ
        refine ⟨hsum, ?_⟩
        calc
          (∑' q : NontriangularCosets Γ σ (d.σ i),
              (‖eisTerm F Γ σ s ((d.σ i) • (ptX' F x y)) q.1‖ +
                ‖fullGradient F (fun t => eisTerm F Γ σ s ((d.σ i) • t) q.1)
                  (ptX' F x y)‖)) =
              cₛ * (∑' q : NontriangularCosets Γ σ (d.σ i),
                siegelRowKernel (v q) x y α) := by
                  rw [hfun, tsum_mul_left]
          _ ≤ cₛ * Crows := mul_le_mul_of_nonneg_left hrowBound hcₛ_nonneg
          _ ≤ (1 + L * Real.sqrt (placeCount F)) * Crows :=
            mul_le_mul_of_nonneg_right hcₛ_bound hCrows
    · refine ⟨0, by norm_num, ?_⟩
      intro s hs z hz
      exact (hSne ⟨z, hz⟩).elim
  · refine ⟨0, by norm_num, ?_⟩
    intro s hs z hz
    exact (hKne ⟨s, hs⟩).elim

end ArtinPrimitiveRoots.A1.Spec
