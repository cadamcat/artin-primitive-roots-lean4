import ArtinPrimitiveRoots.A2.FSide
import ArtinPrimitiveRoots.A1.Coefficients

/-!
# Shared A2 notation

The analytic scale constants are in `FSide.lean`.  These definitions keep the unit quotient and
the field-theoretic row indices in the same types as the frozen A1 interface.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ### The unit quotient used by the reflection and Poisson sums -/

/-- **def:rf-row-units** (04-reflection.tex:19-35): sixth-power map on the S-unit group. -/
def sixthPowerOnUS (S : ArtinPrimitiveRoots.A1.SData F CE condη) : S.US →* S.US where
  toFun u := u ^ 6
  map_one' := by simp
  map_mul' u v := by ext; simp [mul_pow]

/-- **def:rf-row-units** (04-reflection.tex:30-32): `Γ = U_S^6`, as a subgroup of `U_S`. -/
def Gamma (S : ArtinPrimitiveRoots.A1.SData F CE condη) : Subgroup S.US :=
  (sixthPowerOnUS S).range

/-- **def:rf-row-units** (04-reflection.tex:30-32): `U_6 = U_S/Γ`. -/
abbrev UnitSix (S : ArtinPrimitiveRoots.A1.SData F CE condη) := S.US ⧸ Gamma S

/-- **def:rf-row-units** (04-reflection.tex:30-35): quotient class modulo sixth powers. -/
def unitSixClass (S : ArtinPrimitiveRoots.A1.SData F CE condη) (u : S.US) : UnitSix S :=
  QuotientGroup.mk u

/-! ### Ideals used as rows and columns -/

/-- Helper for **prop:reflection** (02a-coefficient-family.tex:84-96): an ideal is powerful when
every prime divisor occurs to exponent at least two. -/
def IsPowerful (I : Ideal (𝓞 F)) : Prop :=
  ∀ P : A1.FinPlace F, P.asIdeal ∣ I → P.asIdeal ^ 2 ∣ I

/-- **def:rf-row-units** (04-reflection.tex:37-38): exterior prime valuation modulo six. -/
def rowExponentModSix (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S)
    (P : ArtinPrimitiveRoots.A1.FinPlace F) : ℤ :=
  FractionalIdeal.count F P (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) % 6

/-- The norm of an exterior ideal. -/
def idealNorm (I : Ideal (𝓞 F)) : ℝ := (Ideal.absNorm I : ℝ)

/-- **def:rf-row-units** (04-reflection.tex:19-35) and **prop:reflection**
(02a-coefficient-family.tex:84-96): an element row with its ideal decomposition. -/
structure ReflectionRow (S : ArtinPrimitiveRoots.A1.SData F CE condη) where
  m : S.R
  ideal : ArtinPrimitiveRoots.A1.SData.ExtIdeal S
  h : ArtinPrimitiveRoots.A1.SData.ExtIdeal S
  d : ArtinPrimitiveRoots.A1.SData.ExtIdeal S
  generates : S.IsGen (m : F) ideal.1
  factorization : ideal.1 = h.1 * d.1
  h_powerful : IsPowerful h.1
  d_squarefree : Squarefree d.1
  coprime : IsCoprime h.1 d.1

/-- Membership in the compact annular row set `R ∩ ℓ_{Z^{M₀}} K`, translated by a fixed
norm-one element when the uniformity clause is used (02a:77-96). -/
def InReflectionBox (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FSˣ) (t : S.FSˣ) (Z : ℝ) (r : ReflectionRow S) : Prop :=
  ∃ y ∈ K, S.diag (r.m : F) = S.ell (Real.rpow Z M0) * ((t * y : S.FSˣ) : S.FS)

/-- Fixed balanced allowed-generator choices supplied by A1 `lem:balanced-generators`
(02-arithmetic.tex:134-227).
The compact set and all choices are fixed before the growing norm variables. -/
structure BalancedChoices (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) where
  Kbal : Set S.FS
  Kbal_compact : IsCompact Kbal
  Kbal_normOne : ∀ y ∈ Kbal, S.absS y = 1
  gen : ArtinPrimitiveRoots.A1.SData.ExtIdeal S → Fˣ
  gen_spec : ∀ I, S.IsGen (gen I : F) I.1 ∧ Bd.Allowed (gen I)
  gen_balanced : ∀ I,
    S.diag (gen I : F) * S.ell (idealNorm I.1)⁻¹ ∈ Kbal

/-! ### The balanced row-unit decomposition -/

/-- **def:rf-row-units** (04-reflection.tex:19-35): the row element as a unit of `F`. -/
def rowElement (S : ArtinPrimitiveRoots.A1.SData F CE condη) (r : ReflectionRow S) : Fˣ :=
  Units.mk0 (r.m : F) r.generates.1

/-- **def:rf-row-units** (04-reflection.tex:21-35): the ratio between a row generator and the
fixed balanced generator is an S-unit. -/
theorem exists_rowUnit (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices S H Bd) (r : ReflectionRow S) :
    ∃ ε : S.US, rowElement S r = ε * bc.gen r.ideal := by
  sorry

/-- **def:rf-row-units** (04-reflection.tex:21-35): `ε_m = m/m₀(𝔪)`. -/
noncomputable def rowEpsilon (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices S H Bd) (r : ReflectionRow S) : S.US :=
  Classical.choose (exists_rowUnit S bc r)

/-- **def:rf-row-units** (04-reflection.tex:30-35): the class `υ_m = ε_m Γ`. -/
noncomputable def rowUpsilon (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices S H Bd) (r : ReflectionRow S) : UnitSix S :=
  unitSixClass S (rowEpsilon S bc r)

/-- **def:rf-row-units** (04-reflection.tex:37-38): `j_𝔭 = v_𝔭((m)_S) mod 6`. -/
def rowPrimeExponent (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (P : ArtinPrimitiveRoots.A1.FinPlace F) : ℤ :=
  rowExponentModSix S r.ideal P

end ArtinPrimitiveRoots.A2
