import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.AdditiveDefs
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem additive_sieve
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (bc : BalancedChoices D S H Bd)
    (K : Set S.FS) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N V : ℝ, (hN : 2 ≤ N) → (hV : 2 ≤ V) →
        ∀ P : Finset S.FS,
          (∀ α ∈ P, α ∈ leadCandidates D S bc V) ∧
          (∀ α ∈ P, ∀ β ∈ P, α ≠ β → ¬ leadSameModulo S α β) →
          ∀ b : S.FS → ℂ,
            (∑' m : {m : S.R // leadRowWindow D S K N (by linarith [hN]) m},
              ‖∑ α ∈ P, b α * leadAdditivePhase S A m.1 α‖ ^ 2 ≤
                C * (N + V ^ 2) * ∑ α ∈ P, ‖b α‖ ^ 2) ∧
            (∀ c : S.R → ℂ,
              ∑ α ∈ P,
                ‖∑' m : {m : S.R // leadRowWindow D S K N (by linarith [hN]) m},
                    c m.1 * leadAdditivePhase S A m.1 α‖ ^ 2 ≤
                  C * (N + V ^ 2) *
                    ∑' m : {m : S.R // leadRowWindow D S K N (by linarith [hN]) m},
                      ‖c m.1‖ ^ 2) := by
  sorry

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
