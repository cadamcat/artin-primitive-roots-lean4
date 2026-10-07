import ArtinPrimitiveRoots.A2.ZeroFree.Nodes

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **prop:zero-density** (06-zero-free.tex:165-185). One exceptional family `E(U)` is chosen
before `ε`, and each reciprocal constant is uniform in the growing dyadic variable. Corrected per
sol-gate-a2 to keep the same exceptional set for every `ε`. -/
theorem prop_zero_density
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (hηoutsideS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ S.Sf → η.UnramifiedAt v)
    (fd : FrequencyData S D η)
    (L : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u))
    (Linc : ∀ u : fd.U, fd.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹))
    (A_F : ℝ) (hAF : 0 < A_F) :
    ∃ ρ U₀ Cexc : ℝ, ∃ E : ℝ → Finset fd.U,
      0 < ρ ∧ ρ < min (1 / 10) (1 / (A_F + 1)) ∧
      2 ≤ U₀ ∧ 0 < Cexc ∧
      (∀ U : ℝ, U₀ ≤ U →
        (∀ u ∈ E U, U ≤ fd.q u ∧ fd.q u < 2 * U) ∧
        ((E U).card : ℝ) ≤ Cexc * Real.rpow U (1 / 2 : ℝ) ∧
        (∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          (fd.omega u = 1 ∨ ∃ hnon : fd.omega u ≠ 1, ∃ s : ℂ,
            996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * Real.rpow U ρ ∧
              (L u hnon).value s = 0) → u ∈ E U)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
        ∀ U : ℝ, U₀ ≤ U → ∀ u, U ≤ fd.q u → fd.q u < 2 * U →
          u ∉ E U → ∀ hnon : fd.omega u ≠ 1, ∀ ξ : ℂ,
            998 / 1000 ≤ ξ.re → |ξ.im| ≤ 2 * Real.rpow U ρ →
              ‖((Linc u hnon).value ξ)⁻¹‖ ≤ Cε * Real.rpow U ε) := by
  sorry

end ArtinPrimitiveRoots.A2
