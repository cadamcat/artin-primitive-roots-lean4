import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».ZeroDictionary
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

open scoped NumberField Topology BigOperators
open NumberField IsDedekindDomain Complex Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Ext.SplittingInputs Classical

/-- A unit-height zero window is finite and its cardinal is bounded by its weighted count. -/
theorem zero_window_finite_count (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    {ρ : ℂ | ρ ∈ nontrivialZeros K ∧ T ≤ ρ.im ∧ ρ.im < T + 1}.Finite ∧
    ({ρ : ℂ | ρ ∈ nontrivialZeros K ∧ T ≤ ρ.im ∧ ρ.im < T + 1}.ncard : ℝ) ≤
      dedekindZeroWindowCount K T := by
  obtain ⟨C, hC, hcount⟩ := ext_dedekind_zero_count
  let S : Set ℂ := {ρ | ρ ∈ nontrivialZeros K ∧ T ≤ ρ.im ∧ ρ.im < T + 1}
  let F : ℂ → ℝ := fun ρ => if ρ ∈ S then (zeroMultiplicity K ρ : ℝ) else 0
  have hF : Summable F := (hcount K T).1
  have hnonneg (ρ : ℂ) : 0 ≤ F ρ := by
    dsimp [F]
    split_ifs <;> positivity
  have hge (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ F ρ := by
    have hm : 1 ≤ zeroMultiplicity K ρ :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ((xi_zero_dictionary K).2.2 ρ hρ.1))
    simpa only [F, if_pos hρ] using (show (1 : ℝ) ≤ (zeroMultiplicity K ρ : ℝ) by
      exact_mod_cast hm)
  have hevent : ∀ᶠ ρ in cofinite, F ρ < 1 :=
    hF.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hfinite : S.Finite := by
    have hbad := mem_cofinite.mp hevent
    refine hbad.subset ?_
    intro ρ hρ
    change ¬ F ρ < 1
    exact not_lt_of_ge (hge ρ hρ)
  refine ⟨hfinite, ?_⟩
  change (S.ncard : ℝ) ≤ dedekindZeroWindowCount K T
  rw [Set.ncard_eq_toFinset_card S hfinite]
  calc
    (hfinite.toFinset.card : ℝ) = ∑ ρ ∈ hfinite.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ ρ ∈ hfinite.toFinset, F ρ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact hge ρ (hfinite.mem_toFinset.mp hρ)
    _ ≤ ∑' ρ : ℂ, F ρ := hF.sum_le_tsum hfinite.toFinset (fun ρ _ => hnonneg ρ)
    _ = dedekindZeroWindowCount K T := rfl

/-- Every bounded closed height interval contains only finitely many nontrivial zeros. -/
theorem zero_strip_finite (K : Type*) [Field K] [NumberField K] (a b : ℝ) :
    {ρ : ℂ | ρ ∈ nontrivialZeros K ∧ a ≤ ρ.im ∧ ρ.im ≤ b}.Finite := by
  classical
  let I : Finset ℤ := Finset.Icc ⌊a⌋ ⌊b⌋
  let V : ℤ → Set ℂ := fun n =>
    {ρ : ℂ | ρ ∈ nontrivialZeros K ∧ (n : ℝ) ≤ ρ.im ∧ ρ.im < (n : ℝ) + 1}
  have hfinite : (⋃ n ∈ (I : Set ℤ), V n).Finite :=
    I.finite_toSet.biUnion fun n _ => (zero_window_finite_count K (n : ℝ)).1
  refine hfinite.subset ?_
  intro ρ hρ
  refine Set.mem_iUnion₂.mpr ⟨⌊ρ.im⌋, ?_, ?_⟩
  · change ⌊ρ.im⌋ ∈ Finset.Icc ⌊a⌋ ⌊b⌋
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono hρ.2.1, Int.floor_mono hρ.2.2⟩
  · exact ⟨hρ.1, Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im⟩

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
