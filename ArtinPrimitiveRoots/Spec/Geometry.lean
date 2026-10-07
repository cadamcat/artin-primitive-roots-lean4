import ArtinPrimitiveRoots.Spec.Defs
import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace

/-! Geometry nodes G1--G6. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- G1 `spec:h3-basics` — P-SPEC.md:208, 258–260. Coordinate formulas, the action on height,
recovery of a point from its Hermitian matrix, and the positive-coordinate chart. -/
theorem G1_h3_basics :
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y, height (pt x y) = y) ∧
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y, horiz (pt x y) = x) ∧
    (∀ g : SL(2,ℂ), ∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y,
      height (g • pt x y) = y /
        (Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2)) ∧
    (∀ g : SL(2,ℂ), ∀ z : H3,
      herm (g • z) = (g : Matrix (Fin 2) (Fin 2) ℂ) * herm z *
        star (g : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    Function.Injective herm ∧
    (∀ z : H3, pt (horiz z) (height z) = z) ∧
    (∀ p : Coord F, p ∈ posSet F → coordsX F (ptX F p) = p) ∧
    (∀ z : X F, ptX F (coordsX F z) = z) ∧
    H3 = OAI.CubicEisenstein.HyperbolicSpace ∧
    height = OAI.CubicEisenstein.hyperbolicHeight ∧
    (∀ x : ℂ, ∀ y : ℝ, ∀ hy : 0 < y,
      pt x y = OAI.CubicEisenstein.upperPoint x y hy) ∧
    ∃ e : {p : Coord F // p ∈ posSet F} ≃ₜ X F,
      (∀ p, e p = ptX F p.1) ∧ (∀ z, (e.symm z).1 = coordsX F z) := by
  sorry

/-- G2 `spec:x-action` — P-SPEC.md:209, 271–275. Product height formula, triangular norm
scaling, unit diagonal norm preservation, and continuity of the product action. -/
theorem G2_x_action :
    (∀ g : SL(2,F), ∀ x : InfinitePlace F → ℂ, ∀ y : InfinitePlace F → ℝ,
      (∀ w, 0 < y w) →
      normHeight F (g • ptX' F x y) =
        ∏ w, y w / (Complex.normSq (w.embedding (g 1 0) * x w +
          w.embedding (g 1 1)) + Complex.normSq (w.embedding (g 1 0)) * y w ^ 2)) ∧
    (∀ b : SL(2,F), b ∈ borelSL F → ∀ z : X F,
      normHeight F (b • z) = absFieldNorm F (b 0 0) * normHeight F z) ∧
    (∀ γ : SL(2,𝓞 F), ∀ σ : SL(2,F),
      σ⁻¹ * toSLF F γ * σ ∈ borelSL F →
      (∃ ε : (𝓞 F)ˣ,
        algebraMap (𝓞 F) F (ε : 𝓞 F) = (σ⁻¹ * toSLF F γ * σ) 0 0 ∧
        absUnitNorm F ε = 1) ∧
      ∀ z : X F, normHeight F ((σ⁻¹ * toSLF F γ * σ) • z) = normHeight F z) ∧
    (∀ g : InfinitePlace F → SL(2,ℂ),
      ∃ e : X F ≃ₜ X F,
        (∀ z, e z = actAtPlaces F g z) ∧
        (∀ z, e.symm z = actAtPlaces F (fun w => (g w)⁻¹) z)) ∧
      ∀ z : X F, Continuous (fun h : InfinitePlace F → SL(2,ℂ) => actAtPlaces F h z) := by
  sorry

/-- G3 `spec:volume` — P-SPEC.md:210. Invariance, the coordinate density, local finiteness and
positivity, and the product measure formula for hyperbolic volume. -/
theorem G3_volume :
    (∀ g : InfinitePlace F → SL(2,ℂ),
      Measure.map (fun z : X F => actAtPlaces F g z) (volX F) = volX F) ∧
    (∀ f : X F → ℝ, Integrable f (volX F) →
      ∫ z, f z ∂(volX F) =
        ∫ p, f (ptX F p) * (∏ w, ((p w).2 ^ 3)⁻¹)
          ∂(volume.restrict (posSet F))) ∧
    (∀ K : Set (X F), IsCompact K → volX F K < ⊤) ∧
    (∀ U : Set (X F), IsOpen U → U.Nonempty → volX F U ≠ 0) ∧
    volX F = Measure.pi (fun _ : InfinitePlace F => volH3) := by
  sorry

/-- G6 `spec:ppi` — P-SPEC.md:213, 267–270. The point-pair invariant is isometry-invariant,
separates points, controls the coordinates in a small ball, and is smooth in positive coordinates. -/
theorem G6_ppi :
    (∀ g : SL(2,ℂ), ∀ z z' : H3,
      ppi (g • z) (g • z') = ppi z z') ∧
    (∀ g h : SL(2,ℂ),
      ppi (QuotientGroup.mk g : H3) (QuotientGroup.mk h : H3) =
        (∑ i : Fin 2, ∑ j : Fin 2,
          Complex.normSq ((g⁻¹ * h : SL(2,ℂ)) i j)) / 2) ∧
    (∀ z z' : H3, 1 ≤ ppi z z' ∧ (ppi z z' = 1 ↔ z = z')) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → ∀ z : H3,
      ppi (pt 0 1) z ≤ 1 + ρ →
        |Real.log (height z)| ≤ Real.arcosh (1 + ρ) ∧
          ‖horiz z‖ ≤ Real.sqrt (2 * ρ + ρ ^ 2)) ∧
    ∀ w : InfinitePlace F,
      ContDiffOn ℝ ∞ (fun pq : Coord F × Coord F => ppiCoordAt F w pq)
        {pq | pq.1 ∈ posSet F ∧ pq.2 ∈ posSet F} := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
