import ArtinPrimitiveRoots.Spec.Energy

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise
open Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.spec_seed_p

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma normHeight_pos_seed (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    0 < ArtinPrimitiveRoots.A1.Spec.normHeight F z := by
  unfold ArtinPrimitiveRoots.A1.Spec.normHeight
  apply Finset.prod_pos
  intro w hw
  rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
  exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)

private lemma seedTerm_nonzero_height_gt
    (Γ : Subgroup SL(2,𝓞 F)) (σ : SL(2,F)) (A : ℝ)
    (τ : ℝ → ℝ) (hτ : ArtinPrimitiveRoots.A1.Spec.IsCuspCutoff A τ)
    (s : ℂ) (z : ArtinPrimitiveRoots.A1.Spec.X F)
    (q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)
    (hq : ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s z q ≠ 0) :
    A < ArtinPrimitiveRoots.A1.Spec.normHeight F
      (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z)) := by
  let h := ArtinPrimitiveRoots.A1.Spec.normHeight F
    (σ⁻¹ • (((q.out : Γ) : SL(2,𝓞 F)) • z))
  have hh : 0 < h := normHeight_pos_seed _
  have hτne : τ h ≠ 0 := by
    intro hzero
    apply hq
    simp [ArtinPrimitiveRoots.A1.Spec.seedTerm, h, hzero]
  have hnot : ¬ h ≤ A := by
    intro hle
    have hzero := hτ.2.2.1 h hle
    exact hτne hzero
  exact lt_of_not_ge hnot

theorem seedActiveFiniteOne
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (A₀ A : ℝ) (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hsep : ∀ γ γ' : Γ, ∀ z : ArtinPrimitiveRoots.A1.Spec.X F,
      A₀ ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
        (σ⁻¹ • ((γ : SL(2,𝓞 F)) • z)) →
      A₀ ≤ ArtinPrimitiveRoots.A1.Spec.normHeight F
        (σ⁻¹ • ((γ' : SL(2,𝓞 F)) • z)) →
      γ' * γ⁻¹ ∈ ArtinPrimitiveRoots.A1.Spec.cuspStab F Γ σ)
    (τ : ℝ → ℝ) (hτ : ArtinPrimitiveRoots.A1.Spec.IsCuspCutoff A τ)
    (s : ℂ) (z : ArtinPrimitiveRoots.A1.Spec.X F) :
    {q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ |
      ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s z q ≠ 0}.Finite ∧
    Nat.card {q : ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ |
      ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s z q ≠ 0} ≤ 1 := by
  let S : Set (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ) :=
    {q | ArtinPrimitiveRoots.A1.Spec.seedTerm F Γ σ τ s z q ≠ 0}
  have hunique : ∀ q ∈ S, ∀ q' ∈ S, q = q' := by
    intro q hq q' hq'
    have hqhigh := seedTerm_nonzero_height_gt Γ σ A τ hτ s z q hq
    have hq'high := seedTerm_nonzero_height_gt Γ σ A τ hτ s z q' hq'
    have hs := hsep q.out q'.out z
      (le_trans hA hqhigh.le)
      (le_trans hA hq'high.le)
    have hrel : QuotientGroup.rightRel (ArtinPrimitiveRoots.A1.Spec.cuspStab F Γ σ)
        q.out q'.out := QuotientGroup.rightRel_apply.mpr hs
    calc
      q = Quotient.mk _ q.out := (Quotient.out_eq' q).symm
      _ = Quotient.mk _ q'.out := Quotient.sound hrel
      _ = q' := Quotient.out_eq' q'
  have hsubs : ∀ q ∈ S, ∀ q' ∈ S, q = q' := hunique
  have hfinite : S.Finite := by
    classical
    by_cases hne : S.Nonempty
    · rcases hne with ⟨q₀, hq₀⟩
      have hsub : S ⊆ ({q₀} : Set (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)) := by
        intro q hq
        change q = q₀
        exact hunique q hq q₀ hq₀
      exact (Set.finite_singleton q₀).subset hsub
    · have hsub : S ⊆ (∅ : Set (ArtinPrimitiveRoots.A1.Spec.CuspCosets F Γ σ)) := by
        intro q hq
        exact (hne ⟨q, hq⟩).elim
      exact Set.finite_empty.subset hsub
  have hcard : Nat.card S ≤ 1 := by
    letI : Fintype S := hfinite.fintype
    apply Finite.card_le_one_iff_subsingleton.mpr
    exact ⟨fun q q' => Subtype.ext (hunique q.1 q.2 q'.1 q'.2)⟩
  simpa [S] using And.intro hfinite hcard

end ArtinPrimitiveRoots.Proofs.spec_seed_p
