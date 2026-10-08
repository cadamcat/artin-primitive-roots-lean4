import ArtinPrimitiveRoots.A2.ZeroFree.Nodes

/-!
# A2-ZERO-DETECT: one exceptional family for all `ε`

The exceptional set `E U` collects the principal row and the characters whose supplied complete
continuation vanishes in `Re s ≥ 0.996`, `|Im s| ≤ 4 U^ρ`. It is chosen before `ε`. Its size comes
from `zf_detector_count` at the actual growth exponent, and the reciprocal bound outside it from
`zf_reciprocal_bound`. Both `prop_zero_density` and the dictionary producer use this core, with the
growth exponent supplied by `zf_convexity_growth_bound` or by the producer's own hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect

open ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **Zero-density core** (A2-ZERO-DETECT): `prop_zero_density` for any positive `A_F`, given a
growth bound at an exponent `A'` that may differ from `A_F`. -/
theorem zero_density_core
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (fd : FrequencyData S D η)
    (L : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (Linc : ∀ u : fd.U, fd.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹))
    (A_F : ℝ) (hAF : 0 < A_F) (A' : ℝ) (hA' : 0 < A')
    (hGrowth : ConductorHeightBound (F := F) A') :
    ∃ ρ U₀ Cexc : ℝ, ∃ E : ℝ → Finset fd.U,
      0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)) ∧
      2 ≤ U₀ ∧ 0 < Cexc ∧
      (∀ U : ℝ, U₀ ≤ U →
        (∀ u ∈ E U, U ≤ fd.q u ∧ fd.q u < 2 * U) ∧
        ((E U).card : ℝ) ≤ Cexc * Real.rpow U (1 / 2 : ℝ) ∧
        (∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          (fd.omega u = 1 ∨ ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
            996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧
              (L u hnon).value s = 0) → u ∈ E U)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ U : ℝ, U₀ ≤ U → ∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          u ∉ E U → ∀ hnon : fd.omega u ≠ 1, ∀ ξ : ℂ,
            998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * Real.rpow U ρ →
              ‖((Linc u hnon).value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε) := by
  set m : ℝ := min (1 / 10) (min (1 / (A_F + 1)) (1 / (A' + 1))) with hm
  have hm0 : 0 < m := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  set ρ : ℝ := m / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρm : ρ < m := by linarith
  have hρ1 : ρ < min (1 / 10) (1 / (A_F + 1)) := by
    have : m ≤ min (1 / 10) (1 / (A_F + 1)) :=
      le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hρ2 : ρ < min (1 / 10) (1 / (A' + 1)) := by
    have : m ≤ min (1 / 10) (1 / (A' + 1)) :=
      le_min (min_le_left _ _) ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hρ10 : ρ < 1 / 10 := lt_of_lt_of_le hρ1 (min_le_left _ _)
  obtain ⟨C1, hC1, hcnt⟩ := zf_detector_count S D η hη fd L A' ρ (1 / 100) hA' ⟨hρ0, hρ2⟩
    (by norm_num) hGrowth
  obtain ⟨U₀', hU₀', hrec⟩ := zf_reciprocal_bound S D η hη fd L Linc ρ hρ0
  obtain ⟨Cc, hCc, hdc⟩ := fd.dyadic_count
  let P : ℝ → fd.U → Prop := fun U u => fd.omega u = 1 ∨ ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
    996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧ (L u hnon).value s = 0
  let E : ℝ → Finset fd.U := fun U =>
    if hU : 2 ≤ U then (hdc U hU).1.toFinset.filter (P U) else ∅
  have hmemE : ∀ U, 2 ≤ U → ∀ u, u ∈ E U ↔ (U ≤ fd.q u ∧ fd.q u < 2 * U) ∧ P U u := by
    intro U hU u
    simp only [E, dif_pos hU, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  refine ⟨ρ, max 2 U₀', 1 + C1, E, hρ0, hρ1, le_max_left _ _, by positivity, ?_, ?_⟩
  · intro U hU
    have hU2 : 2 ≤ U := le_trans (le_max_left _ _) hU
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      exact ((hmemE U hU2 u).1 hu).1
    · let E1 := (E U).filter (fun u => fd.omega u = 1)
      let E2 := (E U).filter (fun u => ¬ fd.omega u = 1)
      have hsplit : E1.card + E2.card = (E U).card :=
        Finset.card_filter_add_card_filter_not _
      have hE1 : E1.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        have ha1 := (Finset.mem_filter.mp ha).2
        have hb1 := (Finset.mem_filter.mp hb).2
        exact fd.omega_injective a b (ha1.trans hb1.symm)
      have hE2 : (E2.card : ℝ) ≤ C1 * Real.rpow U (88 / 1000 + ρ + 1 / 100) := by
        apply hcnt U hU2 E2
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
        obtain ⟨⟨hq1, hq2⟩, hP⟩ := (hmemE U hU2 u).1 hu1
        refine ⟨hq1, hq2, ?_⟩
        rcases hP with h | h
        · exact absurd h hu2
        · exact h
      have hpow : Real.rpow U (88 / 1000 + ρ + 1 / 100) ≤ Real.rpow U (1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hone : 1 ≤ Real.rpow U (1 / 2) := Real.one_le_rpow (by linarith) (by norm_num)
      have hE1r : (E1.card : ℝ) ≤ 1 := by exact_mod_cast hE1
      calc ((E U).card : ℝ) = (E1.card : ℝ) + E2.card := by
            rw [← hsplit]
            push_cast
            ring
        _ ≤ 1 + C1 * Real.rpow U (1 / 2) := by
            have := mul_le_mul_of_nonneg_left hpow hC1.le
            linarith
        _ ≤ (1 + C1) * Real.rpow U (1 / 2) := by nlinarith
    · intro u hq1 hq2 hP
      exact (hmemE U hU2 u).2 ⟨⟨hq1, hq2⟩, hP⟩
  · intro ε hε
    obtain ⟨Cε, hCε, hb⟩ := hrec ε hε
    refine ⟨Cε, hCε, ?_⟩
    intro U hU u hq1 hq2 hnotin hnon ξ hξ1 hξ2
    have hU2 : 2 ≤ U := le_trans (le_max_left _ _) hU
    have hU0 : U₀' ≤ U := le_trans (le_max_right _ _) hU
    apply hb U hU0 u hq1 hq2 hnon _ ξ hξ1 hξ2
    intro s hs1 hs2 hz
    apply hnotin
    exact (hmemE U hU2 u).2 ⟨⟨hq1, hq2⟩, Or.inr ⟨hnon, s, hs1, hs2, hz⟩⟩

end ArtinPrimitiveRoots.A2.Proofs.A2ZeroDetect
