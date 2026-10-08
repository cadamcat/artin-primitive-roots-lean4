import Mathlib

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory

/-- The total volume of selected constant cells is controlled by bounded overlap and bad cells. -/
theorem selectedCell_volume_upper {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
    (μ : Measure α) [IsFiniteMeasure μ] (T selected boundary : Finset κ)
    (cell : κ → Set α) (hcell : ∀ k ∈ T, MeasurableSet (cell k))
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (M : ℕ)
    (hselected : selected ⊆ T) (hboundary : boundary ⊆ T)
    (hconstant : ∀ k ∈ selected, k ∉ boundary → ∀ x ∈ cell k, P x)
    (hoverlap : ∀ x : α, (T.filter fun k => x ∈ cell k).card ≤ M) :
    (∑ k ∈ selected, μ.real (cell k)) ≤
      (M : ℝ) * μ.real {x | P x} + ∑ k ∈ boundary, μ.real (cell k) := by
  let f (k : κ) : α → ℝ := (cell k).indicator (fun _ => 1)
  let g : α → ℝ := {x | P x}.indicator (fun _ => 1)
  have hf (k : κ) (hk : k ∈ T) : Integrable (f k) μ :=
    (integrable_const (1 : ℝ)).indicator (hcell k hk)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hP
  have hpoint (x : α) : (∑ k ∈ selected, f k x) ≤
      (M : ℝ) * g x + ∑ k ∈ boundary, f k x := by
    have hcount (S : Finset κ) : (∑ k ∈ S, f k x) = ((S.filter fun k => x ∈ cell k).card : ℝ) := by
      simp [f, Set.indicator, Finset.sum_boole]
    have hnonneg : 0 ≤ ∑ k ∈ boundary, f k x := by
      rw [hcount]
      exact Nat.cast_nonneg _
    by_cases hPx : P x
    · have hsub : (selected.filter fun k => x ∈ cell k) ⊆ (T.filter fun k => x ∈ cell k) := by
        intro k hk
        exact Finset.mem_filter.mpr ⟨hselected (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
      have hnat := (Finset.card_le_card hsub).trans (hoverlap x)
      have hreal : ((selected.filter fun k => x ∈ cell k).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hnat
      rw [hcount]
      simpa [g, hPx] using hreal.trans (le_add_of_nonneg_right hnonneg)
    · have hsub : (selected.filter fun k => x ∈ cell k) ⊆ (boundary.filter fun k => x ∈ cell k) := by
        intro k hk
        obtain ⟨hksel, hxcell⟩ := Finset.mem_filter.mp hk
        have hkbound : k ∈ boundary := by
          by_contra hnot
          exact hPx (hconstant k hksel hnot x hxcell)
        exact Finset.mem_filter.mpr ⟨hkbound, hxcell⟩
      have hnat := Finset.card_le_card hsub
      have hreal : ((selected.filter fun k => x ∈ cell k).card : ℝ) ≤
          ((boundary.filter fun k => x ∈ cell k).card : ℝ) := by exact_mod_cast hnat
      rw [hcount, hcount]
      simpa [g, hPx] using hreal
  have hselInt : Integrable (fun x => ∑ k ∈ selected, f k x) μ :=
    integrable_finset_sum _ (fun k hk => hf k (hselected hk))
  have hboundInt : Integrable (fun x => (M : ℝ) * g x + ∑ k ∈ boundary, f k x) μ :=
    (hg.const_mul _).add (integrable_finset_sum _ (fun k hk => hf k (hboundary hk)))
  have hIntegral := integral_mono hselInt hboundInt hpoint
  rw [integral_finset_sum _ (fun k hk => hf k (hselected hk)), integral_add (hg.const_mul _)
    (integrable_finset_sum _ (fun k hk => hf k (hboundary hk))), integral_const_mul,
    integral_finset_sum _ (fun k hk => hf k (hboundary hk))] at hIntegral
  have hfVal (k : κ) (hk : k ∈ T) : (∫ x, f k x ∂μ) = μ.real (cell k) := by
    simpa only [f, smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) (hcell k hk)
  have hgVal : (∫ x, g x ∂μ) = μ.real {x | P x} := by
    simpa only [g, smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) hP
  have hselVal : (∑ k ∈ selected, ∫ x, f k x ∂μ) = ∑ k ∈ selected, μ.real (cell k) :=
    Finset.sum_congr rfl (fun k hk => hfVal k (hselected hk))
  have hboundVal : (∑ k ∈ boundary, ∫ x, f k x ∂μ) = ∑ k ∈ boundary, μ.real (cell k) :=
    Finset.sum_congr rfl (fun k hk => hfVal k (hboundary hk))
  rw [hselVal, hgVal, hboundVal] at hIntegral
  exact hIntegral

/-- Real overlap bounds are useful when target counts scale with the product dyad. -/
theorem selectedCell_volume_upper_real {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
    (μ : Measure α) [IsFiniteMeasure μ] (T selected boundary : Finset κ)
    (cell : κ → Set α) (hcell : ∀ k ∈ T, MeasurableSet (cell k))
    (P : α → Prop) (hP : MeasurableSet {x | P x}) (M : ℝ)
    (hselected : selected ⊆ T) (hboundary : boundary ⊆ T)
    (hconstant : ∀ k ∈ selected, k ∉ boundary → ∀ x ∈ cell k, P x)
    (hoverlap : ∀ x : α, ((T.filter fun k => x ∈ cell k).card : ℝ) ≤ M) :
    (∑ k ∈ selected, μ.real (cell k)) ≤
      (M : ℝ) * μ.real {x | P x} + ∑ k ∈ boundary, μ.real (cell k) := by
  let f (k : κ) : α → ℝ := (cell k).indicator (fun _ => 1)
  let g : α → ℝ := {x | P x}.indicator (fun _ => 1)
  have hf (k : κ) (hk : k ∈ T) : Integrable (f k) μ :=
    (integrable_const (1 : ℝ)).indicator (hcell k hk)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hP
  have hpoint (x : α) : (∑ k ∈ selected, f k x) ≤
      (M : ℝ) * g x + ∑ k ∈ boundary, f k x := by
    have hcount (S : Finset κ) : (∑ k ∈ S, f k x) = ((S.filter fun k => x ∈ cell k).card : ℝ) := by
      simp [f, Set.indicator, Finset.sum_boole]
    have hnonneg : 0 ≤ ∑ k ∈ boundary, f k x := by
      rw [hcount]
      exact Nat.cast_nonneg _
    by_cases hPx : P x
    · have hsub : (selected.filter fun k => x ∈ cell k) ⊆ (T.filter fun k => x ∈ cell k) := by
        intro k hk
        exact Finset.mem_filter.mpr ⟨hselected (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
      have hcard : ((selected.filter fun k => x ∈ cell k).card : ℝ) ≤
          ((T.filter fun k => x ∈ cell k).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      have hreal : ((selected.filter fun k => x ∈ cell k).card : ℝ) ≤ M := hcard.trans (hoverlap x)
      rw [hcount]
      simpa [g, hPx] using hreal.trans (le_add_of_nonneg_right hnonneg)
    · have hsub : (selected.filter fun k => x ∈ cell k) ⊆ (boundary.filter fun k => x ∈ cell k) := by
        intro k hk
        obtain ⟨hksel, hxcell⟩ := Finset.mem_filter.mp hk
        have hkbound : k ∈ boundary := by
          by_contra hnot
          exact hPx (hconstant k hksel hnot x hxcell)
        exact Finset.mem_filter.mpr ⟨hkbound, hxcell⟩
      have hnat := Finset.card_le_card hsub
      have hreal : ((selected.filter fun k => x ∈ cell k).card : ℝ) ≤
          ((boundary.filter fun k => x ∈ cell k).card : ℝ) := by exact_mod_cast hnat
      rw [hcount, hcount]
      simpa [g, hPx] using hreal
  have hselInt : Integrable (fun x => ∑ k ∈ selected, f k x) μ :=
    integrable_finset_sum _ (fun k hk => hf k (hselected hk))
  have hboundInt : Integrable (fun x => (M : ℝ) * g x + ∑ k ∈ boundary, f k x) μ :=
    (hg.const_mul _).add (integrable_finset_sum _ (fun k hk => hf k (hboundary hk)))
  have hIntegral := integral_mono hselInt hboundInt hpoint
  rw [integral_finset_sum _ (fun k hk => hf k (hselected hk)), integral_add (hg.const_mul _)
    (integrable_finset_sum _ (fun k hk => hf k (hboundary hk))), integral_const_mul,
    integral_finset_sum _ (fun k hk => hf k (hboundary hk))] at hIntegral
  have hfVal (k : κ) (hk : k ∈ T) : (∫ x, f k x ∂μ) = μ.real (cell k) := by
    simpa only [f, smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) (hcell k hk)
  have hgVal : (∫ x, g x ∂μ) = μ.real {x | P x} := by
    simpa only [g, smul_eq_mul, mul_one] using integral_indicator_const (1 : ℝ) hP
  have hselVal : (∑ k ∈ selected, ∫ x, f k x ∂μ) = ∑ k ∈ selected, μ.real (cell k) :=
    Finset.sum_congr rfl (fun k hk => hfVal k (hselected hk))
  have hboundVal : (∑ k ∈ boundary, ∫ x, f k x ∂μ) = ∑ k ∈ boundary, μ.real (cell k) :=
    Finset.sum_congr rfl (fun k hk => hfVal k (hboundary hk))
  rw [hselVal, hgVal, hboundVal] at hIntegral
  exact hIntegral

end ArtinPrimitiveRoots.TypeII.PD
