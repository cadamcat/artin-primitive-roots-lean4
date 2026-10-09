import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A2.Proofs.A2_ADDSIEVE_OPUS.Assembly

/-!
# Section 5: additive large sieve and analytic probe
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Congruence of two `F_S` frequencies modulo the diagonal S-integer lattice. -/
def SameModuloSIntegers (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x y : S.FS) : Prop := ∃ r : S.R, x - y = S.diag (r : F)

/-- The compact annulus of S-integer rows used by the additive sieve. -/
def InAdditiveWindow (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FS) (N : ℝ) (hN : 0 < N) (m : S.R) : Prop :=
  ∃ x ∈ K, S.diag (m : F) = S.ell D N hN * x

/-- The frequencies `d/s` with `q_s ≤ V`, using the fixed balanced generators from A1; the
zero class from the unit ideal is included separately (05:118-152). -/
def AdditiveCandidates (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices D S H Bd) (V : ℝ) : Set S.FS :=
  {α | α = 0 ∨ ∃ I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
    idealNorm I.1 ≤ V ∧ ∃ d : 𝓞 F,
      IsCoprime (Ideal.span {d}) I.1 ∧
      α = S.diag ((algebraMap (𝓞 F) F d) / (bc.gen I : F))}

/-- The additive character of the row-frequency pairing. -/
def additivePhase (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (m : S.R) (α : S.FS) : ℂ :=
  S.e A (S.diag (m : F) * α)

/-- **lem:additive-sieve** (05-poisson.tex:118-192).  For fixed field, arithmetic data, balanced
choices and compact set, both the primal and dual inequalities hold with one constant independent
of the lengths, the frequency subset, and the coefficients. -/
theorem lem_additive_sieve
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
          (∀ α ∈ P, α ∈ AdditiveCandidates D S bc V) ∧
          (∀ α ∈ P, ∀ β ∈ P, α ≠ β → ¬ SameModuloSIntegers S α β) →
          ∀ b : S.FS → ℂ,
            (∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
              ‖∑ α ∈ P, b α * additivePhase S A m.1 α‖ ^ 2 ≤
                C * (N + V ^ 2) * ∑ α ∈ P, ‖b α‖ ^ 2) ∧
            (∀ c : S.R → ℂ,
              ∑ α ∈ P,
                ‖∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
                    c m.1 * additivePhase S A m.1 α‖ ^ 2 ≤
                  C * (N + V ^ 2) *
                    ∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
                      ‖c m.1‖ ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := ArtinPrimitiveRoots.Proofs.addsieve_opus.sieve_main D S A K hK
  refine ⟨C, hC, ?_⟩
  intro N V hN hV P hP b
  exact hmain N V hN hV (fun m => InAdditiveWindow D S K N (by linarith [hN]) m)
    (fun m hm => hm) P
    (fun α hα => ArtinPrimitiveRoots.Proofs.addsieve_opus.candidate_data D S bc A
      (by linarith) (hP.1 α hα))
    (fun α hα β hβ hne => hP.2 α hα β hβ hne) b

end ArtinPrimitiveRoots.A2
