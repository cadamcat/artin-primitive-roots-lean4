import ArtinPrimitiveRoots.Spec.Stage2

/-!
# P-SPEC: the package's top theorems

Moved here from `Spec/Interface.lean` on 2026-10-07 with unchanged statements: they are proved from the P-SPEC node
modules, which import `Interface.lean`, so they must come after them.
-/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

section A
/-- The action in coordinates (convention check; OAI `hyperbolicHeight_action_upperPoint`,
HyperbolicSpace.lean:163). Owner `spec:h3-basics`. -/
theorem height_smul_pt (g : SL(2,ℂ)) (x : ℂ) (y : ℝ) (hy : 0 < y) :
    height (g • pt x y) = y / (Complex.normSq (g 1 0 * x + g 1 1) + Complex.normSq (g 1 0) * y ^ 2) := by
  rw [height_eq_hyperbolicHeight, pt_eq_upperPoint x y hy]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact OAI.CubicEisenstein.hyperbolicHeight_action_upperPoint g x y hy

end A

section B
variable (F : Type) [Field F] [NumberField F]

end B

section C
variable (F : Type) [Field F] [NumberField F]
variable [IsTotallyComplex F]
/-- `spec:free-level`: some principal congruence subgroup acts freely. -/
theorem exists_free_congr : ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ FreeAction F (congrSubgroup F N) := by
  sorry

/-- `spec:cusps-finite` (boundary to P-EIS / P-REDUCTION): finitely many cusps; the map
`⊔_i Γ_{σ_i}\Γ → B(F)\SL(2,F)`, `(i, Γ_{σ_i}γ) ↦ B(F)σ_i⁻¹γ`, is a bijection. -/
theorem exists_cusp_reps (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex] :
    ∃ (ι : Type) (_ : Fintype ι) (σ : ι → SL(2,F)),
      Function.Bijective (fun p : (Σ i, CuspCosets F Γ (σ i)) =>
        (Quotient.mk (QuotientGroup.rightRel (borelSL F))
          ((σ p.1)⁻¹ * toSLF F ((p.2.out : Γ) : SL(2, 𝓞 F))))) := by
  exact (R3_cusps_finite Γ).1

/-- `spec:x-action`: the height of a translate, place by place (from `height_smul_pt`). -/
theorem normHeight_smul_ptX' (g : SL(2,F)) (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    normHeight F (g • ptX' F x y) = ∏ w, y w / (Complex.normSq (w.embedding (g 1 0) * x w +
      w.embedding (g 1 1)) + Complex.normSq (w.embedding (g 1 0)) * y w ^ 2) := by
  simp_rw [normHeight, height_smul_ptX'_at g x y hy]

/-- `spec:eis-def`: the term does not depend on the coset representative. -/
theorem eisTerm_mk (Γ : Subgroup SL(2, 𝓞 F)) (σ : SL(2,F)) (s : ℂ) (z : X F) (γ : Γ) :
    eisTerm F Γ σ s z (Quotient.mk _ γ) =
      ((normHeight F (σ⁻¹ • ((γ : SL(2, 𝓞 F)) • z)) : ℝ) : ℂ) ^ (1 + 2 * s) := by
  sorry

/-- `spec:eis-converge`: locally uniform absolute convergence for `Re s > 1/2`, uniformly on compact
sets of `z` and on vertical strips `σ₀ ≤ Re s ≤ σ₁`. -/
theorem eisSeries_majorant (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F))
    (K : Set (X F)) (hK : IsCompact K) (σ₀ σ₁ : ℝ) (h₀ : 1 / 2 < σ₀) :
    ∃ m : CuspCosets F Γ σ → ℝ, Summable m ∧
      ∀ z ∈ K, ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ∀ q, ‖eisTerm F Γ σ s z q‖ ≤ m q := by
  sorry

/-- `spec:eis-converge`: `Γ`-invariance in the convergence region. -/
theorem eisSeries_invariant (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex] (σ : SL(2,F)) (s : ℂ)
    (hs : 1 / 2 < s.re) (γ : SL(2, 𝓞 F)) (hγ : γ ∈ Γ) (z : X F) :
    eisSeries F Γ σ s (γ • z) = eisSeries F Γ σ s z := by
  sorry

/-- `spec:domain`. -/
theorem isOpen_contDomain (s₁ ε : ℝ) : IsOpen (contDomain s₁ ε) := by
  sorry

/-- `spec:domain`. -/
theorem isPreconnected_contDomain (s₁ ε : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ < 4) (hε : 0 < ε) :
    IsPreconnected (contDomain s₁ ε) := by
  sorry

/-- **Main theorem of P-SPEC** (`spec:api`). -/
theorem exists_continuedEisenstein (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex]
    (hfree : FreeAction F Γ) (σ : SL(2,F)) (s₁ : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) :
    Nonempty (ContinuedEisenstein F Γ σ s₁) := by
  sorry

/-- `spec:api` (uniqueness): two continuations agree on the common domain. -/
theorem ContinuedEisenstein.E_eq {Γ : Subgroup SL(2, 𝓞 F)} {σ : SL(2,F)} {s₁ : ℝ}
    (d d' : ContinuedEisenstein F Γ σ s₁) (h₁ : s₁ ≤ 1 / 2) :
    (∀ s ∈ contDomain s₁ (min d.ε d'.ε), d.E s = d'.E s) ∧ d.res = d'.res := by
  sorry

/-- **`spec:cuspidal`.** A finite linear combination of residues (same `Γ`, same `s₁`) all of whose
constant terms vanish is zero. The constant term along `τ` at height vector `y` is the integral over
a fundamental domain `P` of the cusp lattice of `τ`. (Consumer: P-RES, "θ_f depends only on M*f".) -/
theorem res_lincomb_eq_zero (Γ : Subgroup SL(2, 𝓞 F)) [Γ.FiniteIndex] (hfree : FreeAction F Γ)
    (s₁ : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ ≤ 1 / 2) {ι : Type} [Fintype ι] (σ : ι → SL(2,F))
    (d : ∀ i, ContinuedEisenstein F Γ (σ i) s₁) (c : ι → ℂ)
    (hct : ∀ (τ : SL(2,F)) (y : InfinitePlace F → ℝ), (∀ w, 0 < y w) →
      ∃ P : Set (InfinitePlace F → ℂ), IsAddFundamentalDomain (cuspTranslations F Γ τ) P ∧
        ∫ x in P, (∑ i, c i * (d i).res (τ • ptX' F x y)) = 0) :
    ∀ z, ∑ i, c i * (d i).res z = 0 := by
  sorry

end C

end ArtinPrimitiveRoots.A1.Spec
