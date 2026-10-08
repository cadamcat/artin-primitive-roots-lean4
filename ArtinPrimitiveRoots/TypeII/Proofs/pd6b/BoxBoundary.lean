import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.DummyGoodness
import ArtinPrimitiveRoots.TypeII.PD.RootReplacement

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

/-- The frozen good-and-box boundary estimate also bounds the box alone on contributing edges. -/
theorem rootBox_boundary_of_sourcePad (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ε : ℝ) (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
      ∀ p : PrimeLists S.x K, ValidPrimeLists S.x K F.a p →
        (S.d₀ : ℝ) ≤ (sharedProduct p : ℝ) → ∀ z : ℤ × ℤ, Int.gcd z.1 z.2 = 1 →
          |(z.1 : ℝ)| ≤ Real.exp (Real.rpow S.L (1 / 2 : ℝ)) →
          |(z.2 : ℝ)| ≤ Real.exp (Real.rpow S.L (1 / 2 : ℝ)) →
          (((gridIndices (Real.rpow S.x (-ε))).filter fun k =>
            IsNonconstantOn (fun y => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ z)
              (gridCube (Real.rpow S.x (-ε)) k)).card : ℝ) ≤
            Real.exp (Real.rpow S.L (9 / 10 : ℝ)) * Real.rpow S.x (2 * ε) := by
  have hHigher := higherPDFix_valid F hF
  obtain ⟨xLists, hxLists₂, hLists⟩ := validPrimeLists_exist_eventually (higherPDFix F).a hHigher.1
  obtain ⟨xGap, hxGap₂, hGap⟩ := higherBand_gap_eventually F hF
  obtain ⟨xBoundary, hxBoundary₂, hBoundary⟩ :=
    root_arch_boundary δ c₁ c₂ hδ hc₁ K (higherPDFix F) hHigher ε hε hε₁
  let x₀ := max 2 (max xLists (max xGap xBoundary))
  refine ⟨x₀, by simp [x₀], ?_⟩
  intro S hS hx p hp hpad z hz hz₁ hz₂
  have hxLists : xLists ≤ S.x := (by simp [x₀] : xLists ≤ x₀).trans hx
  have hxGap : xGap ≤ S.x := (by simp [x₀] : xGap ≤ x₀).trans hx
  have hxBoundary : xBoundary ≤ S.x := (by simp [x₀] : xBoundary ≤ x₀).trans hx
  obtain ⟨q, hq⟩ := hLists S.x hxLists
  obtain ⟨hL, hsep⟩ := hGap S.x hxGap
  have hd₀ : 0 < S.d₀ := by
    have hmem := hS.2.2.2.2.2.2
    unfold padScales at hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
    rw [← heq]
    positivity
  have hAllGood := higherLists_good_of_sourcePad F hF hL hsep p q hp hq S.d₀ hd₀ hpad (Y := S.Y)
  have hEnv : EnvValid (higherPDFix F) S (z, q) := ⟨hz, hq⟩
  have hCount := hBoundary S hS hxBoundary (z, q) hEnv hz₁ hz₂
  simpa only [envGood, hAllGood, and_true] using hCount

end ArtinPrimitiveRoots.TypeII.PD
