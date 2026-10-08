import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

open Classical in
private theorem tsum_eq_if_unique {α : Type*} (f : α → ℂ)
    (huniq : ∀ a b, f a ≠ 0 → f b ≠ 0 → a = b) :
    ∑' a, f a = if h : ∃ a, f a ≠ 0 then f h.choose else 0 := by
  classical
  by_cases h : ∃ a, f a ≠ 0
  · rw [dif_pos h]
    apply tsum_eq_single h.choose
    intro a haa
    by_contra hfa
    exact haa (huniq a h.choose hfa h.choose_spec)
  · have hfzero : f = 0 := by
      funext a
      by_contra hfa
      exact h ⟨a, hfa⟩
    simp [h, hfzero]

open Classical in
private theorem probe_tri_tsum
    (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (d : SiegelData F Γ) (σ : SL(2,F)) (K : Set ℂ)
    (hK : IsCompact K) (hstrip : K ⊆ {s : ℂ | 2 < s.re ∧ s.re < 3})
    (s : ℂ) (hs : s ∈ K) (i : d.ι) (z : X F) :
    let tri (q : CuspCosets F Γ σ) :=
      σ⁻¹ * toSLF F (q.out : Γ) * d.σ i ∈ borelSL F
    ∑' q : {q : CuspCosets F Γ σ // tri q}, eisTerm F Γ σ s ((d.σ i) • z) q.1 =
      if h : ∃ q, tri q then eisTerm F Γ σ s ((d.σ i) • z) h.choose else 0 := by
  classical
  let tri (q : CuspCosets F Γ σ) :=
    σ⁻¹ * toSLF F (q.out : Γ) * d.σ i ∈ borelSL F
  have hE4 := E4_eis_siegel Γ d σ K hK hstrip
  have hUnique := (hE4 i).1
  dsimp [tri]
  apply tsum_eq_if_unique
  intro q q' hq hq'
  exact Subtype.ext (hUnique q.1 q'.1 q.2 q'.2)

end ArtinPrimitiveRoots.A1.Spec
