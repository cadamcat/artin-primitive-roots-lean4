import ArtinPrimitiveRoots.TypeII.PD.RootReplacement

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

def rootWindowSet (U V : ℝ) (Sq : ℕ) (lam : (p : ℕ) → Fin (p + 1))
    (lo hi : ℝ × ℝ × ℝ) : Set (ℕ × ℕ) :=
  {uv | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
    lo.1 ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ hi.1 ∧
    lo.2.1 ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ hi.2.1 ∧
    lo.2.2 ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧
      (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ hi.2.2 ∧
    ∀ p ∈ Sq.primeFactors, kernelLine p uv.1 (rootC uv.1 uv.2) = lam p}

/-- Every normalized root window is finite, so its ncard is an actual count. -/
theorem rootWindowSet_finite (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (Sq : ℕ) (lam : (p : ℕ) → Fin (p + 1)) (lo hi : ℝ × ℝ × ℝ)
    (hhi₁ : hi.1 ≤ 16) (hhi₂ : hi.2.1 ≤ 2) :
    (rootWindowSet U V Sq lam lo hi).Finite := by
  let T := (Finset.range (⌊16 * U⌋₊ + 1)) ×ˢ Finset.range (⌊2 * V⌋₊ + 1)
  apply T.finite_toSet.subset
  intro uv huv
  obtain ⟨hc, hu, hl₁, hr₁, hl₂, hr₂, hl₃, hr₃, hlines⟩ := huv
  have huR : (uv.1 : ℝ) ≤ 16 * U :=
    (div_le_iff₀ hU).mp (hr₁.trans hhi₁)
  have hvR : (uv.2 : ℝ) ≤ 2 * V :=
    (div_le_iff₀ hV).mp (hr₂.trans hhi₂)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr huR)),
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr hvR))⟩

/-- The frozen discrepancy estimate gives a direct upper count for each valid window. -/
theorem rootWindow_count_upper (U V E ρ : ℝ) (Sq : ℕ) (lam : (p : ℕ) → Fin (p + 1))
    (lo hi : ℝ × ℝ × ℝ)
    (hcount : |((rootWindowSet U V Sq lam lo hi).ncard : ℝ) -
      U * V * (hi.1 - lo.1) * (hi.2.1 - lo.2.1) * (hi.2.2 - lo.2.2) * ρ| ≤ E) :
    ((rootWindowSet U V Sq lam lo hi).ncard : ℝ) ≤
      U * V * ρ * ((hi.1 - lo.1) * (hi.2.1 - lo.2.1) * (hi.2.2 - lo.2.2)) + E := by
  have h := (abs_le.mp hcount).2
  nlinarith

/-- Corners of a closed grid cell clipped to the normalized root rectangle. -/
def clippedCubeLo (h : ℝ) (k : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  (max 1 ((k.1 : ℝ) * h), max 1 ((k.2.1 : ℝ) * h), max 0 ((k.2.2 : ℝ) * h))

def clippedCubeHi (h : ℝ) (k : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  (min 16 (((k.1 : ℝ) + 1) * h), min 2 (((k.2.1 : ℝ) + 1) * h),
    min 1 (((k.2.2 : ℝ) + 1) * h))

/-- A point witnessing a clipped cell supplies all interval hypotheses required by root_lines. -/
theorem clippedCube_bounds (h : ℝ) (k : ℤ × ℤ × ℤ) (y : ℝ × ℝ × ℝ)
    (hy : (1 ≤ y.1 ∧ y.1 ≤ 16) ∧ (1 ≤ y.2.1 ∧ y.2.1 ≤ 2) ∧ (0 ≤ y.2.2 ∧ y.2.2 ≤ 1))
    (hcell : y ∈ gridCube h k) :
    1 ≤ (clippedCubeLo h k).1 ∧ (clippedCubeLo h k).1 ≤ (clippedCubeHi h k).1 ∧
    (clippedCubeHi h k).1 ≤ 16 ∧ 1 ≤ (clippedCubeLo h k).2.1 ∧
    (clippedCubeLo h k).2.1 ≤ (clippedCubeHi h k).2.1 ∧ (clippedCubeHi h k).2.1 ≤ 2 ∧
    0 ≤ (clippedCubeLo h k).2.2 ∧ (clippedCubeLo h k).2.2 ≤ (clippedCubeHi h k).2.2 ∧
    (clippedCubeHi h k).2.2 ≤ 1 := by
  obtain ⟨hc₁, hc₂, hc₃, hc₄, hc₅, hc₆⟩ := hcell
  refine ⟨le_max_left _ _, ?_, min_le_left _ _, le_max_left _ _, ?_, min_le_left _ _,
    le_max_left _ _, ?_, min_le_left _ _⟩
  · exact (max_le hy.1.1 hc₁).trans (le_min hy.1.2 hc₂)
  · exact (max_le hy.2.1.1 hc₃).trans (le_min hy.2.1.2 hc₄)
  · exact (max_le hy.2.2.1 hc₅).trans (le_min hy.2.2.2 hc₆)

end
end ArtinPrimitiveRoots.TypeII.PD
