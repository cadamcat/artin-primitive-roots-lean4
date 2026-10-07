import ArtinPrimitiveRoots.A1.Characters

/-!
# A1 interface, §6: the coefficient family

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 6. The coefficient family (02a) -/

/-- `P_G(t) = (2√π)^{-1} exp(-(log t)²/4)` (eq:reflection-gaussian). -/
def PG (t : ℝ) : ℝ := (2 * Real.sqrt Real.pi)⁻¹ * Real.exp (-(Real.log t) ^ 2 / 4)

/-- Exterior ideals, squarefree exterior ideals (index types). -/
def SData.ExtIdeal (S : SData F CE condη) := {I : Ideal (𝓞 F) // S.IsExterior I}
def SData.SqfExtIdeal (S : SData F CE condη) := {I : Ideal (𝓞 F) // S.IsExterior I ∧ Squarefree I}

/-- `B_m(Z) = Σ_{𝔠 sqfree, 𝔫} γ_2(𝔠) q_𝔠^{-1/2} q_𝔫^{-1} ϑ(𝔄) χ_𝔄(m) P_G(q_𝔄/Z)`, `𝔄 = 𝔠𝔫³`
(eq:reflection-B-definition). `cgen` picks an allowed generator of each squarefree exterior ideal
(the value does not depend on the choice). -/
def Bm (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (ϑ : HeckeChar F)
    (cgen : S.SqfExtIdeal → F) (m : F) (Z : ℝ) : ℂ :=
  ∑' p : S.SqfExtIdeal × S.ExtIdeal,
    gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) * chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)

/-- eq:reflection-original-dirichlet-majorant (02a:54–62): absolute convergence. -/
theorem Bm_summable (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (ϑ : HeckeChar F) (hϑ : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1)
    (cgen : S.SqfExtIdeal → F) (hc : ∀ I, ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c)
    (m : F) (Z : ℝ) (hZ : 0 < Z) :
    Summable fun p : S.SqfExtIdeal × S.ExtIdeal =>
      ‖gamma D S A 2 p.1.1 (cgen p.1) *
      ((((Ideal.absNorm p.1.1 : ℝ) ^ (-(1 / 2 : ℝ)) * (Ideal.absNorm p.2.1 : ℝ)⁻¹) : ℝ) : ℂ) *
      ϑ.idealValue (p.1.1 * p.2.1 ^ 3) * chiIdealPow D (p.1.1 * p.2.1 ^ 3) m 1 *
      (PG ((Ideal.absNorm (p.1.1 * p.2.1 ^ 3) : ℝ) / Z) : ℂ)‖ := by
  sorry


end ArtinPrimitiveRoots.A1
