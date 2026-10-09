import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Positive compact probe support gives a fixed denominator interval, a linear ideal count,
and a bounded weighted inverse-norm mass, uniformly in the growing denominator scale. -/
theorem probe_denominator_control
    (S : SData F CE condη) (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f)
    (hpos : tsupport f ⊆ Set.Ioi 0)
    (hcont : Continuous f) (hne : ∃ t, f t ≠ 0) :
    ∃ L B C : ℝ, 0 < L ∧ 1 ≤ B ∧ 0 < C ∧
      (∀ v ∈ tsupport f, L ≤ v ∧ v ≤ B) ∧
      ∀ Y : ℝ, 1 ≤ Y → ∃ P : Finset S.ExtIdeal,
        (∀ I : S.ExtIdeal, I ∈ P ↔ f (idealNorm I.1 / Y) ≠ 0) ∧
        (P.card : ℝ) ≤ C * Y ∧
        (∑ I ∈ P, ‖f (idealNorm I.1 / Y)‖ ^ 2 / idealNorm I.1) ≤ C := by
  classical
  have hsupport : (tsupport f).Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, subset_closure (Function.mem_support.mpr ht)⟩
  obtain ⟨L, hLmem, hLmin⟩ := hcompact.exists_isMinOn hsupport
    (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) (tsupport f))
  obtain ⟨B0, hBmem, hBmax⟩ := hcompact.exists_isMaxOn hsupport
    (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) (tsupport f))
  obtain ⟨tM, htM, hMmax⟩ := hcompact.exists_isMaxOn hsupport hcont.norm.continuousOn
  let B : ℝ := max 1 B0
  let M : ℝ := ‖f tM‖
  have hL : 0 < L := hpos hLmem
  have hB : 1 ≤ B := le_max_left _ _
  have hM : 0 ≤ M := norm_nonneg _
  have hinterval (v : ℝ) (hv : v ∈ tsupport f) : L ≤ v ∧ v ≤ B :=
    ⟨hLmin hv, (hBmax hv).trans (le_max_right _ _)⟩
  have hnorm (v : ℝ) (hv : v ∈ tsupport f) : ‖f v‖ ≤ M := hMmax hv
  obtain ⟨C0, hC0, hcount⟩ := a2_bridge_COUNT S
  let C : ℝ := C0 * B * (1 + M ^ 2 / L) + 1
  have hC0B : 0 < C0 * B := mul_pos hC0 (lt_of_lt_of_le zero_lt_one hB)
  have hratio : 0 ≤ M ^ 2 / L := div_nonneg (sq_nonneg _) hL.le
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hCcard : C0 * B ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hC0B.le hratio]
  have hCmass : C0 * B * M ^ 2 / L ≤ C := by
    dsimp [C]
    have heq : C0 * B * M ^ 2 / L = C0 * B * (M ^ 2 / L) := by ring
    rw [heq]
    nlinarith
  refine ⟨L, B, C, hL, hB, hC, hinterval, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hBY : 1 ≤ B * Y := by nlinarith
  have hcut := (a2_bridge_COUNT_finite S (B * Y) (by positivity)).1
  let support : Set S.ExtIdeal := {I | f (idealNorm I.1 / Y) ≠ 0}
  have hbounds (I : S.ExtIdeal) (hI : I ∈ support) :
      L * Y ≤ idealNorm I.1 ∧ idealNorm I.1 ≤ B * Y := by
    have hts : idealNorm I.1 / Y ∈ tsupport f :=
      subset_closure (Function.mem_support.mpr hI)
    obtain ⟨hlow, hhigh⟩ := hinterval _ hts
    exact ⟨(le_div_iff₀ hY0).mp hlow, (div_le_iff₀ hY0).mp hhigh⟩
  have hsubset : support ⊆ {I : S.ExtIdeal | idealNorm I.1 ≤ B * Y} :=
    fun I hI => (hbounds I hI).2
  have hfinite : support.Finite := hcut.subset hsubset
  let P : Finset S.ExtIdeal := hfinite.toFinset
  have hP (I : S.ExtIdeal) : I ∈ P ↔ f (idealNorm I.1 / Y) ≠ 0 := by
    simp [P, support]
  have hcard : (P.card : ℝ) ≤ C0 * B * Y := by
    have hcardNat := Set.ncard_le_ncard hsubset hcut
    calc
      (P.card : ℝ) = (support.ncard : ℝ) := by
        rw [Set.ncard_eq_toFinset_card support hfinite]
      _ ≤ ({I : S.ExtIdeal | idealNorm I.1 ≤ B * Y}.ncard : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ C0 * (B * Y) := hcount _ hBY
      _ = C0 * B * Y := by ring
  refine ⟨P, hP, hcard.trans (mul_le_mul_of_nonneg_right hCcard hY0.le), ?_⟩
  have hterm (I : S.ExtIdeal) (hI : I ∈ P) :
      ‖f (idealNorm I.1 / Y)‖ ^ 2 / idealNorm I.1 ≤ M ^ 2 / (L * Y) := by
    have hIsupport : I ∈ support := (hP I).mp hI
    have hlow := (hbounds I hIsupport).1
    have hq : 0 < idealNorm I.1 := (mul_pos hL hY0).trans_le hlow
    have hts : idealNorm I.1 / Y ∈ tsupport f :=
      subset_closure (Function.mem_support.mpr hIsupport)
    have hsq : ‖f (idealNorm I.1 / Y)‖ ^ 2 ≤ M ^ 2 := by
      nlinarith [hnorm _ hts, norm_nonneg (f (idealNorm I.1 / Y))]
    calc
      _ ≤ M ^ 2 / idealNorm I.1 := div_le_div_of_nonneg_right hsq hq.le
      _ ≤ M ^ 2 / (L * Y) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hL hY0) hlow
  calc
    _ ≤ ∑ I ∈ P, M ^ 2 / (L * Y) := Finset.sum_le_sum hterm
    _ = (P.card : ℝ) * (M ^ 2 / (L * Y)) := by simp
    _ ≤ (C0 * B * Y) * (M ^ 2 / (L * Y)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = C0 * B * M ^ 2 / L := by field_simp
    _ ≤ C := hCmass

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
