import ArtinPrimitiveRoots.Spec.Geometry

/-! Reduction-theory nodes R1--R14. This first stage states the nodes that can start against
the frozen interface. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- R1 `spec:cusp-lattice` — P-SPEC.md:214, 271–275. Integral multiples lie in the cusp
translation group, all translations have bounded denominators, and the embedded lattice has a
bounded measurable fundamental domain. The signed extension has at most two translation cosets. -/
theorem R1_cusp_lattice (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) :
    (∃ m : ℕ, 0 < m ∧ ∀ a : 𝓞 F,
      algebraMap (𝓞 F) F ((m : 𝓞 F) * a) ∈ cuspLattice F Γ σ) ∧
    (∃ D : ℕ, 0 < D ∧
      (∀ μ ∈ cuspLattice F Γ σ, HasDenominatorBound F D μ) ∧
      (∀ μ ∈ cuspTranslationExtension F Γ σ, HasDenominatorBound F D μ)) ∧
    (∀ μ : F, μ ∈ cuspTranslationExtension F Γ σ ↔ μ ∈ signedCuspTranslations F Γ σ) ∧
    (IsFullZLattice (cuspTranslationsZ F Γ σ) ∧
      cuspLattice F Γ σ ≤ cuspTranslationExtension F Γ σ ∧
      ∃ μ₀ ∈ cuspTranslationExtension F Γ σ,
        ∀ μ ∈ cuspTranslationExtension F Γ σ,
          μ ∈ cuspLattice F Γ σ ∨ μ - μ₀ ∈ cuspLattice F Γ σ) ∧
    ∃ P : Set (InfinitePlace F → ℂ),
      IsAddFundamentalDomain (cuspTranslations F Γ σ) P ∧ Bornology.IsBounded P ∧
        MeasurableSet P := by
  sorry

/-- R2 `spec:cusp-units` — P-SPEC.md:215, 277–280. The cusp diagonal units have finite index;
every stabilizer element has a bounded-denominator upper-triangular form; torsion units under a
free action are central; and the stabilizer acts by the stated affine and height maps. -/
theorem R2_cusp_units (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) :
    (cuspUnits F Γ σ).FiniteIndex ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ↔ ε ∈ cuspUnitSet F Γ σ) ∧
    ∃ D : ℕ, 0 < D ∧
      (∀ γ : cuspStab F Γ σ, ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        HasDenominatorBound F D μ ∧
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ) ∧
    (∀ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ → IsOfFinOrder ε →
      ε = 1 ∨ ε = -1) ∧
    (∀ γ : cuspStab F Γ σ, ∀ x : InfinitePlace F → ℂ, ∀ y : InfinitePlace F → ℝ,
      (∀ w, 0 < y w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ cuspUnits F Γ σ ∧ ∃ μ : F,
        σ⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ = cuspUnitMatrix F ε μ ∧
        (γ : SL(2,𝓞 F)) • (σ • ptX' F x y) =
          σ • ptX' F
            (fun w => (w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))) ^ 2 * x w +
              w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F)) * w.embedding μ)
            (fun w => Complex.normSq (w.embedding
              (algebraMap (𝓞 F) F (ε : 𝓞 F))) * y w)) := by
  sorry

/-- R3 `spec:cusps-finite` — P-SPEC.md:216, 282–289. The finite cusp representatives give the
bijective decomposition of `B(F) \ SL(2,F)` consumed by P-EIS and P-REDUCTION; bottom-row ideal
classes have precisely the `SL(2,O_F)` orbits as fibres. -/
theorem R3_cusps_finite (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2,𝓞 F))))) ∧
    (∀ g : SL(2,F), bottomRowFractionalIdeal F g ≠ 0) ∧
    Function.Surjective (bottomRowClass F) ∧
    ∀ g h : SL(2,F),
      bottomRowClass F g = bottomRowClass F h ↔
        ∃ γ : SL(2,𝓞 F),
          Quotient.mk (QuotientGroup.rightRel (borelSL F)) g =
            Quotient.mk (QuotientGroup.rightRel (borelSL F)) (h * toSLF F γ) := by
  sorry

/-- R4 `spec:unit-balance` — P-SPEC.md:217, 290–293. Every positive height vector can be moved
by a finite-index unit subgroup into a uniformly bounded logarithmic balance region. -/
theorem R4_unit_balance (E : Subgroup ((𝓞 F)ˣ)) [E.FiniteIndex] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : InfinitePlace F → ℝ, (∀ w, 0 < t w) →
      ∃ ε : (𝓞 F)ˣ, ε ∈ E ∧ ∀ w,
        |Real.log (‖w.embedding (algebraMap (𝓞 F) F (ε : 𝓞 F))‖ * t w) -
          (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t w')| ≤ B := by
  sorry

/-- R5 `spec:lattice-sums` — P-SPEC.md:218, 295–298. Rows in a fixed denominator multiple of
`O_F²`, with no two representatives in the same unit orbit, have the stated summable norm weight. -/
theorem R5_lattice_sums (D : ℕ) (hD : 0 < D) (α : ℝ) (hα : 4 < α)
    {ι : Type*} (v : ι → F × F)
    (hvD : ∀ i, HasDenominatorBound F D (v i).1 ∧ HasDenominatorBound F D (v i).2)
    (hv0 : ∀ i, v i ≠ (0, 0))
    (huniq : ∀ i j, (∃ ε : (𝓞 F)ˣ,
      v i = ((algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).1,
        (algebraMap (𝓞 F) F (ε : 𝓞 F)) * (v j).2)) → i = j) :
    Summable (fun i => ∏ w : InfinitePlace F, (rowNorm F (v i) w) ^ (-α)) := by
  sorry

/-- R6 `spec:two-heights` — P-SPEC.md:219, 300. A nonzero lower-left entry bounds the product
of the two heights, and denominator bounds make this uniform over the arithmetic subgroup. -/
theorem R6_two_heights (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex] :
    (∀ g : SL(2,F), ∀ z : X F, g 1 0 ≠ 0 →
      normHeight F z * normHeight F (g • z) ≤ (absFieldNorm F (g 1 0))⁻¹) ∧
    (∀ σ σ' : SL(2,F),
      ∃ C : ℝ, 0 < C ∧ ∀ γ : Γ, ∀ z : X F,
        (σ'⁻¹ * toSLF F (γ : SL(2,𝓞 F)) * σ) 1 0 ≠ 0 →
          normHeight F (σ⁻¹ • z) *
            normHeight F (σ'⁻¹ • ((γ : SL(2,𝓞 F)) • z)) ≤ C) := by
  sorry

/-- R7 `spec:minkowski` — P-SPEC.md:220, 302–306. A uniform Minkowski bound for a nonzero
integral row in the height-dependent positive Hermitian forms. -/
theorem R7_minkowski :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ z : X F, ∃ v : 𝓞 F × 𝓞 F,
      v ≠ (0, 0) ∧
        ∏ w : InfinitePlace F,
          rowHeightForm F
            (algebraMap (𝓞 F) F v.1, algebraMap (𝓞 F) F v.2) z w ≤ C_M := by
  sorry

/-- R11 `spec:free-level` — P-SPEC.md:224, 330–336. A nonzero principal congruence subgroup
acts freely on the product hyperbolic space. -/
theorem R11_free_level :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ FreeAction F (congrSubgroup F N) := by
  sorry

end ArtinPrimitiveRoots.A1.Spec
