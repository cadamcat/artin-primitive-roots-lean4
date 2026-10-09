import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.Proofs.A2_FREQUENCY.ZfConvOpus.Conductor
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict
import ArtinPrimitiveRoots.Hecke.Continuation

/-!
# The aggregate Hecke analysis for a totally complex field

Producer for `ArtinPrimitiveRoots.A2.heckeAnalysis_exists` under `[IsTotallyComplex F]`
(06:37-73, 139-153, 413-477). The conclusion is the body of the subtype abbreviation
`ArtinPrimitiveRoots.A2.HeckeAnalysis F` (`A2/Interface.lean`), written out so that
`Interface.lean` can import this file without an import cycle.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.zf_conv_opus

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]

private theorem one_primeValue (v : FinPlace F) : (1 : HeckeChar F).primeValue v = 1 := by
  have hUnram : (1 : HeckeChar F).UnramifiedAt v := by
    intro u hu hu'
    simp [HeckeChar.UnramifiedAt, HeckeChar.loc]
  unfold HeckeChar.primeValue
  simp [hUnram, HeckeChar.loc]

private theorem one_heckeLSeries_eq_LSeriesRay {s : ℂ} (hs : 1 < s.re) :
    heckeLSeries (1 : HeckeChar F) s =
      Hecke.LSeriesRay (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus F) →* ℂˣ) s := by
  apply ArtinPrimitiveRoots.A2.qsa_heckeLSeries_eq_LSeriesRay
  · intro I hI
    have hcop : Hecke.IsCoprimeTo (⟨0, ∅⟩ : RayClassModulus F) I := by
      refine ⟨hI, ?_⟩
      intro v hv
      simp at hv
    have hleft : (1 : HeckeChar F).idealValue I = 1 := by
      unfold HeckeChar.idealValue
      apply Multiset.prod_eq_one
      intro z hz
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hz
      by_cases h : P.IsPrime ∧ P ≠ ⊥
      · simp [h, one_primeValue]
      · simp [h]
    have hright : Hecke.charValue
        (1 : RayClassGroup (⟨0, ∅⟩ : RayClassModulus F) →* ℂˣ) I = 1 := by
      simp [Hecke.charValue, hcop]
    exact hleft.trans hright.symm
  · exact hs

/-- The principal regularization, valid for every number field. -/
private theorem principal_regularization :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * heckeLSeries (1 : HeckeChar F) s) ∧
      (G 1).im = 0 ∧ 0 < (G 1).re := by
  obtain ⟨G, hGdiff, hGeq, hGone⟩ :=
    Hecke.LSeriesRay_trivial_continuation (K := F) (⟨0, ∅⟩ : RayClassModulus F)
  refine ⟨G, hGdiff, ?_, ?_, ?_⟩
  · intro s hs
    rw [hGeq s hs, one_heckeLSeries_eq_LSeriesRay hs]
  · rw [hGone]
    exact Complex.ofReal_im _
  · rw [hGone, Complex.ofReal_re]
    simpa using NumberField.dedekindZeta_residue_pos F

/-- Nonprincipal finite-order continuation for a totally complex field. -/
theorem nonempty_heckeLContinuation [IsTotallyComplex F] (χ : HeckeChar F)
    (hfin : IsOfFinOrder χ) (hne : χ ≠ 1) : Nonempty (HeckeLContinuation χ) := by
  obtain ⟨f, hf⟩ := exists_isPrimitiveConductor χ
  obtain ⟨L, _, hL, _, hagree, _⟩ :=
    ArtinPrimitiveRoots.A2.ext_hecke_continuation inferInstance χ hfin hne f hf
  exact ⟨⟨L, hL, hagree⟩⟩

/-- **Producer for `heckeAnalysis_exists`** under `[IsTotallyComplex F]`: the conclusion is
the defining property of `HeckeAnalysis F`. -/
theorem heckeAnalysis_totallyComplex (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] :
    ∃ A : (HeckeChar F → ℂ → ℂ) × (ℂ → ℂ),
      (∀ χ s, 1 < s.re → A.1 χ s = heckeLSeries χ s) ∧
      (∀ χ, IsOfFinOrder χ → χ ≠ 1 →
        ∃ C : HeckeLContinuation χ, C.value = A.1 χ) ∧
      DifferentiableOn ℂ (A.1 1) {s | s ≠ 1} ∧ Differentiable ℂ A.2 ∧
      (∀ s, s ≠ 1 → A.2 s = (s - 1) * A.1 1 s) ∧
      (A.2 1).im = 0 ∧ 0 < (A.2 1).re := by
  classical
  obtain ⟨G, hGdiff, hGeq, hGim, hGre⟩ := principal_regularization (F := F)
  let P : ℂ → ℂ := fun s => G s / (s - 1)
  let L : HeckeChar F → ℂ → ℂ := fun χ =>
    if h : IsOfFinOrder χ ∧ χ ≠ 1 then
      (Classical.choice (nonempty_heckeLContinuation χ h.1 h.2)).value
    else if χ = 1 then P else heckeLSeries χ
  have hL1 : L 1 = P := by
    simp [L]
  refine ⟨(L, G), ?_, ?_, ?_, hGdiff, ?_, hGim, hGre⟩
  · intro χ s hs
    change L χ s = heckeLSeries χ s
    by_cases h : IsOfFinOrder χ ∧ χ ≠ 1
    · simp only [L, dif_pos h]
      exact (Classical.choice (nonempty_heckeLContinuation χ h.1 h.2)).agrees s hs
    · by_cases h1 : χ = 1
      · subst h1
        rw [hL1]
        have hs1 : s - 1 ≠ 0 := by
          intro h0
          have : s = 1 := sub_eq_zero.mp h0
          rw [this] at hs
          norm_num at hs
        change G s / (s - 1) = _
        rw [hGeq s hs]
        field_simp
      · simp only [L, dif_neg h, if_neg h1]
  · intro χ hfin hne
    refine ⟨Classical.choice (nonempty_heckeLContinuation χ hfin hne), ?_⟩
    change _ = L χ
    simp only [L, dif_pos (And.intro hfin hne)]
  · change DifferentiableOn ℂ (L 1) {s | s ≠ 1}
    rw [hL1]
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    exact ((hGdiff s).div ((differentiableAt_id.sub_const 1)) hs1).differentiableWithinAt
  · intro s hs
    change G s = (s - 1) * L 1 s
    rw [hL1]
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    change G s = (s - 1) * (G s / (s - 1))
    field_simp

end ArtinPrimitiveRoots.Proofs.zf_conv_opus
