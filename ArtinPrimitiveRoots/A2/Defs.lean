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

/-- **def:rf-row-units** (04-reflection.tex:30-32): the sixth-power unit quotient is finite.
Added per rev-a2 to record the finiteness assertion omitted by the quotient abbreviation. -/
def UnitSixFiniteStatement (S : ArtinPrimitiveRoots.A1.SData F CE condη) : Prop :=
  Finite (UnitSix S)

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
def InReflectionBox (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (K : Set S.FSˣ) (t : S.FSˣ) (Z : ℝ) (hZ : 0 < Z) (r : ReflectionRow S) : Prop :=
  ∃ y ∈ K, S.diag (r.m : F) =
    S.ell D (Real.rpow Z M0) (Real.rpow_pos_of_pos hZ M0) * ((t * y : S.FSˣ) : S.FS)

/-- Fixed balanced allowed-generator choices supplied by A1 `lem:balanced-generators`
(02-arithmetic.tex:134-227).
The compact set and all choices are fixed before the growing norm variables. -/
structure BalancedChoices (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) where
  Kbal : Set S.FS
  Kbal_compact : IsCompact Kbal
  Kbal_normOne : ∀ y ∈ Kbal, S.absS y = 1
  gen : ArtinPrimitiveRoots.A1.SData.ExtIdeal S → Fˣ
  gen_spec : ∀ I, S.IsGen (gen I : F) I.1 ∧ Bd.Allowed (gen I)
  gen_balanced : ∀ I,
    S.diag (gen I : F) * S.ell D (idealNorm I.1)⁻¹ (by
      have hnorm : 0 < Ideal.absNorm I.1 :=
        Ideal.absNorm_pos_of_nonZeroDivisors
          ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
            (by simpa [Ideal.zero_eq_bot] using I.2.1)⟩
      have hnormR : 0 < (Ideal.absNorm I.1 : ℝ) := by exact_mod_cast hnorm
      exact inv_pos.mpr (by simpa [idealNorm] using hnormR)) ∈ Kbal

/-! ### The balanced row-unit decomposition -/

/-- **def:rf-row-units** (04-reflection.tex:19-35): the row element as a unit of `F`. -/
def rowElement (S : ArtinPrimitiveRoots.A1.SData F CE condη) (r : ReflectionRow S) : Fˣ :=
  Units.mk0 (r.m : F) r.generates.2.1

private lemma rowUnit_count_spanSingleton_div (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private lemma rowUnit_count_spanSingleton_eq_neg_log_intValuation
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma rowUnit_count_spanSingleton_eq_neg_log_valuation (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (v.valuation F z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : v.valuation F z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    rowUnit_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    rowUnit_count_spanSingleton_eq_neg_log_intValuation v n hn,
    rowUnit_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma rowUnit_valuation_ne_zero (v : ArtinPrimitiveRoots.A1.FinPlace F)
    {z : F} (hz : z ≠ 0) : v.valuation F z ≠ 0 :=
  (v.valuation F).ne_zero_iff.mpr hz

/-- **def:rf-row-units** (04-reflection.tex:21-35): the ratio between a row generator and the
fixed balanced generator is an S-unit. -/
theorem exists_rowUnit (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {D : ArtinPrimitiveRoots.A1.FieldData F}
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices D S H Bd) (r : ReflectionRow S) :
    ∃ ε : S.US, rowElement S r = ε * bc.gen r.ideal := by
  classical
  let ε₀ : Fˣ := rowElement S r / bc.gen r.ideal
  have hε₀ : ε₀ ∈ S.US := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ (S.Sf : Set (ArtinPrimitiveRoots.A1.FinPlace F)) →
        v.valuation F ((ε₀ : Fˣ) : F) = 1
    intro v hv
    have hrow := r.generates.2.2 v hv
    have hbal := (bc.gen_spec r.ideal).1.2.2 v hv
    have hcounts :
        FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (r.m : F)) =
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
              ((bc.gen r.ideal : Fˣ) : F)) := hrow.trans hbal.symm
    have hlogs : WithZero.log (v.valuation F (r.m : F)) =
        WithZero.log (v.valuation F ((bc.gen r.ideal : Fˣ) : F)) := by
      rw [rowUnit_count_spanSingleton_eq_neg_log_valuation v (r.m : F) r.generates.2.1,
        rowUnit_count_spanSingleton_eq_neg_log_valuation v
          ((bc.gen r.ideal : Fˣ) : F) (Units.ne_zero (bc.gen r.ideal))] at hcounts
      exact neg_injective hcounts
    have hmne := rowUnit_valuation_ne_zero v r.generates.2.1
    have hbne := rowUnit_valuation_ne_zero v (Units.ne_zero (bc.gen r.ideal))
    have hval : v.valuation F (r.m : F) =
        v.valuation F ((bc.gen r.ideal : Fˣ) : F) := by
      apply le_antisymm
      · exact (WithZero.log_le_log hmne hbne).mp hlogs.le
      · exact (WithZero.log_le_log hbne hmne).mp hlogs.symm.le
    change v.valuation F ((rowElement S r / bc.gen r.ideal : Fˣ) : F) = 1
    rw [Units.val_div_eq_div_val, Valuation.map_div]
    have hrowval : v.valuation F ((rowElement S r : Fˣ) : F) =
        v.valuation F (r.m : F) := by simp [rowElement]
    rw [hrowval, hval, div_self hbne]
  refine ⟨⟨ε₀, hε₀⟩, ?_⟩
  change rowElement S r = ε₀ * bc.gen r.ideal
  dsimp [ε₀]
  simp

/-- **def:rf-row-units** (04-reflection.tex:21-35): `ε_m = m/m₀(𝔪)`. -/
noncomputable def rowEpsilon (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {D : ArtinPrimitiveRoots.A1.FieldData F}
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices D S H Bd) (r : ReflectionRow S) : S.US :=
  Classical.choose (exists_rowUnit S bc r)

/-- **def:rf-row-units** (04-reflection.tex:30-35): the class `υ_m = ε_m Γ`. -/
noncomputable def rowUpsilon (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {D : ArtinPrimitiveRoots.A1.FieldData F}
    {H : ArtinPrimitiveRoots.A1.HilbertData F} {Bd : ArtinPrimitiveRoots.A1.BData S H}
    (bc : BalancedChoices D S H Bd) (r : ReflectionRow S) : UnitSix S :=
  unitSixClass S (rowEpsilon S bc r)

/-- **def:rf-row-units** (04-reflection.tex:37-38): `j_𝔭 = v_𝔭((m)_S) mod 6`. -/
def rowPrimeExponent (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (r : ReflectionRow S) (P : ArtinPrimitiveRoots.A1.FinPlace F) : ℤ :=
  rowExponentModSix S r.ideal P

end ArtinPrimitiveRoots.A2
