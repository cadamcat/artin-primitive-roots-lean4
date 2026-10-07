import ArtinPrimitiveRoots.A1.Field

/-!
# A1 interface, §2: residue symbols

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

/-! ## 2. Residue symbols (def:ar-residue-symbol; read through `σ0`) -/

/-- Residue of a `P`-integral element of `F` in `O_F/P` (0 if not `P`-integral). -/
def residue (P : FinPlace F) (x : F) : 𝓞 F ⧸ P.asIdeal :=
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 F ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  if h : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ P.asIdeal ∧ x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1
  then Ideal.Quotient.mk P.asIdeal h.choose.1 * (Ideal.Quotient.mk P.asIdeal h.choose.2)⁻¹
  else 0

/-- The sextic residue symbol at `P` as a root of unity of `O_F`:
the unique `ζ ∈ μ6` with `ζ ≡ x^{(NP-1)/6} mod P` (1 if no such root, e.g. `x ≡ 0`). -/
def chiAlg (P : FinPlace F) (x : F) : rootsOfUnity 6 (𝓞 F) :=
  if h : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk P.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 6)
  then h.choose else 1

/-- `χ_P(x) ∈ ℂ`: `σ0(chiAlg P x)` if `x` is a `P`-unit, else `0` (02:237–244). -/
def chi (D : FieldData F) (P : FinPlace F) (x : F) : ℂ :=
  if residue P x = 0 then 0
  else D.σ0 (algebraMap (𝓞 F) F ((chiAlg P x : (𝓞 F)ˣ) : 𝓞 F))

/-- `χ_P(x)^j` with the zero convention (also for `6 ∣ j`), `j ∈ ℤ` (02:245–247). -/
def chiPow (D : FieldData F) (P : FinPlace F) (x : F) (j : ℤ) : ℂ :=
  if residue P x = 0 then 0 else chi D P x ^ j

/-- `χ_I(x)^j = Π_{P^k ∥ I} χ_P(x)^{jk}` over the prime factorization of `I` (02:248–255);
`χ_{O_F} = 1`. -/
def chiIdealPow (D : FieldData F) (I : Ideal (𝓞 F)) (x : F) (j : ℤ) : ℂ :=
  ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
    if h : P.IsPrime ∧ P ≠ ⊥ then chiPow D ⟨P, h.1, h.2⟩ x j else 1).prod

/-- `χ_P²` is the cubic residue symbol (used in ar:residue-lift, 02:502–505). Package P-ARITH-GAUSS. -/
theorem chiAlg_sq_eq_cubic (D : FieldData F) (P : FinPlace F) (x : F)
    (hP : (6 : 𝓞 F) ∉ P.asIdeal) (hx : residue P x ≠ 0) :
    Ideal.Quotient.mk P.asIdeal ((((chiAlg P x) ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      residue P x ^ ((Ideal.absNorm P.asIdeal - 1) / 3) := by
  sorry


end ArtinPrimitiveRoots.A1
