import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.AddChar
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.SelfDualMeasure
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Congruence of two `F_S` frequencies modulo the diagonal S-integer lattice. -/
def leadSameModulo (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x y : S.FS) : Prop := ∃ r : S.R, x - y = S.diag (r : F)

/-- The compact annulus of S-integer rows used by the additive sieve. -/
def leadRowWindow (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FS) (N : ℝ) (hN : 0 < N) (m : S.R) : Prop :=
  ∃ x ∈ K, S.diag (m : F) = S.ell D N hN * x

/-- The frequencies `d/s` with `q_s ≤ V`, using the fixed balanced generators from A1; the
zero class from the unit ideal is included separately (05:118-152). -/
def leadCandidates (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices D S H Bd) (V : ℝ) : Set S.FS :=
  {α | α = 0 ∨ ∃ I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
    idealNorm I.1 ≤ V ∧ ∃ d : 𝓞 F,
      IsCoprime (Ideal.span {d}) I.1 ∧
      α = S.diag ((algebraMap (𝓞 F) F d) / (bc.gen I : F))}

/-- The additive character of the row-frequency pairing. -/
def leadAdditivePhase (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (m : S.R) (α : S.FS) : ℂ :=
  S.e A (S.diag (m : F) * α)


end ArtinPrimitiveRoots.Proofs.a2_probe_sol
