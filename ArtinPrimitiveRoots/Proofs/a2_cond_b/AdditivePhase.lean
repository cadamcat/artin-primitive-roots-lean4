import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_additive_characters_exists
import Mathlib.GroupTheory.OrderOfElement
import OAI.NumberTheory.PrimeGaps.AdditiveSieve

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open ArtinPrimitiveRoots.A2
open scoped Classical nonZeroDivisors
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_cond_b

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- A real angle representative for a unit complex number. -/
noncomputable def conductorUnitAngle (z : ℂ) : ℝ := z.arg / (2 * Real.pi)

theorem conductorUnitAngle_exp {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (conductorUnitAngle z : ℂ)) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have h' : Complex.exp (z.arg * Complex.I) = z := by simpa [hz] using h
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (conductorUnitAngle z : ℂ) =
      z.arg * Complex.I := by
    simp only [conductorUnitAngle, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    field_simp [Real.pi_ne_zero]
  rw [harg]
  exact h'

/-- A real angle representative for a value of a character on a finite ring. -/
noncomputable def conductorAdditiveAngle {R : Type*} [Ring R]
    (ψ : AddChar R ℂ) (x : R) : ℝ := conductorUnitAngle (ψ x)

theorem conductorAdditive_norm_one {R : Type*} [Ring R] [Fintype R]
    (ψ : AddChar R ℂ) (x : R) : ‖ψ x‖ = 1 := by
  have hcard : (Fintype.card R : ℕ) ≠ 0 := Fintype.card_ne_zero
  have hpow : ψ x ^ Fintype.card R = 1 := by
    have hnsmul : (Fintype.card R : ℕ) • x = 0 := card_nsmul_eq_zero
    calc
      ψ x ^ Fintype.card R = ψ ((Fintype.card R : ℕ) • x) :=
        (AddChar.map_nsmul_eq_pow ψ (Fintype.card R) x).symm
      _ = ψ 0 := congrArg ψ hnsmul
      _ = 1 := ψ.map_zero_eq_one
  exact Complex.norm_eq_one_of_pow_eq_one hpow hcard

theorem conductorAdditiveAngle_exp {R : Type*} [Ring R] [Fintype R]
    (ψ : AddChar R ℂ) (x : R) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (conductorAdditiveAngle ψ x : ℂ)) = ψ x :=
  conductorUnitAngle_exp (conductorAdditive_norm_one ψ x)

/-- Pull a primitive residue character back to the S-integers and shift it by a residue unit. -/
def conductorAdditivePhaseChar (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    (q : S.ExtIdeal) (d : (ConductorResidueRing q)ˣ) : AddChar S.R ℂ :=
  (Ψ.ψ q).compAddMonoidHom
    { toFun := fun x => ρ.red q x * (d : ConductorResidueRing q)
      map_zero' := by simp
      map_add' := by intro x y; simp [map_add, add_mul] }

@[simp]
theorem conductorAdditivePhaseChar_apply (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    (q : S.ExtIdeal) (d : (ConductorResidueRing q)ˣ) (x : S.R) :
    conductorAdditivePhaseChar S ρ Ψ q d x =
      Ψ.ψ q (ρ.red q x * (d : ConductorResidueRing q)) := rfl

/-- The conductor ideal of this pulled-back additive character is exactly `ker (ρ.red q)`. -/
theorem conductorAdditivePhaseChar_annihilator (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    (q : S.ExtIdeal) (d : (ConductorResidueRing q)ˣ) :
    {a : S.R | ∀ x : S.R,
      conductorAdditivePhaseChar S ρ Ψ q d (a * x) = 1} =
        RingHom.ker (ρ.red q) := by
  ext a
  constructor
  · intro ha
    apply RingHom.mem_ker.mpr
    have hshift :
        (Ψ.ψ q).mulShift (ρ.red q a * (d : ConductorResidueRing q)) = 1 := by
      ext y
      obtain ⟨x, hx⟩ := ρ.surjective q y
      have h := ha x
      simpa [conductorAdditivePhaseChar_apply, AddChar.mulShift_apply,
        hx, mul_assoc, mul_comm, mul_left_comm] using h
    have hzero : ρ.red q a * (d : ConductorResidueRing q) = 0 := by
      by_contra hne
      exact (Ψ.primitive q hne) hshift
    apply d.isUnit.mul_right_injective
    simpa [mul_comm] using hzero
  · intro ha x
    have hzero : ρ.red q a = 0 := RingHom.mem_ker.mp ha
    simp [conductorAdditivePhaseChar_apply, hzero]

/-- For fixed `q`, the pulled-back shifted characters distinguish residue units. -/
theorem conductorAdditivePhaseChar_injective_unit (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    (q : S.ExtIdeal) {d d' : (ConductorResidueRing q)ˣ}
    (h : conductorAdditivePhaseChar S ρ Ψ q d =
      conductorAdditivePhaseChar S ρ Ψ q d') : d = d' := by
  have hshift :
      (Ψ.ψ q).mulShift (d : ConductorResidueRing q) =
        (Ψ.ψ q).mulShift (d' : ConductorResidueRing q) := by
    ext y
    obtain ⟨x, hx⟩ := ρ.surjective q y
    have hxy := congrArg (fun χ : AddChar S.R ℂ => χ x) h
    simpa [conductorAdditivePhaseChar_apply, AddChar.mulShift_apply,
      hx, mul_comm] using hxy
  apply Units.ext
  exact (AddChar.to_mulShift_inj_of_isPrimitive (Ψ.primitive q)) hshift

/-- Equality of pulled-back phases determines both the exterior modulus and its residue unit. -/
theorem conductorAdditivePhaseChar_injective (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    {q q' : S.ExtIdeal} {d : (ConductorResidueRing q)ˣ}
    {d' : (ConductorResidueRing q')ˣ}
    (h : conductorAdditivePhaseChar S ρ Ψ q d =
      conductorAdditivePhaseChar S ρ Ψ q' d') : q = q' ∧ HEq d d' := by
  have hsets :
      {a : S.R | ∀ x : S.R, conductorAdditivePhaseChar S ρ Ψ q d (a * x) = 1} =
      {a : S.R | ∀ x : S.R, conductorAdditivePhaseChar S ρ Ψ q' d' (a * x) = 1} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ha x
      rw [← h]
      exact ha x
    · intro ha x
      rw [h]
      exact ha x
  have hker : RingHom.ker (ρ.red q) = RingHom.ker (ρ.red q') := by
    apply SetLike.coe_injective
    calc
      (RingHom.ker (ρ.red q) : Set S.R) =
          {a : S.R | ∀ x : S.R, conductorAdditivePhaseChar S ρ Ψ q d (a * x) = 1} :=
        (conductorAdditivePhaseChar_annihilator S ρ Ψ q d).symm
      _ = {a : S.R | ∀ x : S.R, conductorAdditivePhaseChar S ρ Ψ q' d' (a * x) = 1} := hsets
      _ = (RingHom.ker (ρ.red q') : Set S.R) :=
        conductorAdditivePhaseChar_annihilator S ρ Ψ q' d'
  have hpre (q : S.ExtIdeal) :
      Ideal.comap (algebraMap (𝓞 F) S.R) (RingHom.ker (ρ.red q)) = q.1 := by
    ext a
    simp [ρ.integral, Ideal.Quotient.eq_zero_iff_mem]
  have hq : q = q' := by
    have hc := congrArg (Ideal.comap (algebraMap (𝓞 F) S.R)) hker
    rw [hpre q, hpre q'] at hc
    exact Subtype.ext hc
  subst q'
  have hdd : d = d' := conductorAdditivePhaseChar_injective_unit S ρ Ψ q h
  cases hdd
  exact ⟨rfl, HEq.rfl⟩

/-- The same residue phase, restricted to integral inputs. -/
def conductorIntegralAdditivePhaseChar (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) : AddChar (𝓞 F) ℂ :=
  (Ψ.ψ q).compAddMonoidHom
    { toFun := fun a => Ideal.Quotient.mk q.1 a * (d : ConductorResidueRing q)
      map_zero' := by simp
      map_add' := by intro a b; simp [map_add, add_mul] }

@[simp]
theorem conductorIntegralAdditivePhaseChar_apply (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (a : 𝓞 F) :
    conductorIntegralAdditivePhaseChar S Ψ q d a =
      Ψ.ψ q (Ideal.Quotient.mk q.1 a * (d : ConductorResidueRing q)) := rfl

theorem conductorIntegralAdditivePhaseChar_norm (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (a : 𝓞 F) :
    ‖conductorIntegralAdditivePhaseChar S Ψ q d a‖ = 1 := by
  rw [conductorIntegralAdditivePhaseChar_apply]
  exact conductorAdditive_norm_one (Ψ.ψ q) _

/-- The difference character for two residue phases, written as a pointwise product. -/
def conductorIntegralDifferenceChar (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q q' : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ) :
    AddChar (𝓞 F) ℂ :=
  conductorIntegralAdditivePhaseChar S Ψ q d *
    (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹

theorem conductorIntegralDifferenceChar_norm (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q q' : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ)
    (a : 𝓞 F) : ‖conductorIntegralDifferenceChar S Ψ q q' d d' a‖ = 1 := by
  simp [conductorIntegralDifferenceChar, norm_mul, norm_inv,
    conductorIntegralAdditivePhaseChar_norm]

/-- The torus frequency coordinates of a primitive residue phase on an integral basis. -/
noncomputable def conductorIntegralFrequencyVector (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) :
    Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ :=
  fun i => conductorAdditiveAngle (Ψ.ψ q)
    (Ideal.Quotient.mk q.1 (RingOfIntegers.basis F i) * (d : ConductorResidueRing q))

theorem conductorIntegralFrequencyVector_basis (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) =
        conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) :=
  calc
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (conductorAdditiveAngle (Ψ.ψ q)
          (Ideal.Quotient.mk q.1 (RingOfIntegers.basis F i) * (d : ConductorResidueRing q)) : ℂ)) =
        Ψ.ψ q (Ideal.Quotient.mk q.1 (RingOfIntegers.basis F i) * (d : ConductorResidueRing q)) :=
      conductorAdditiveAngle_exp _ _
    _ = conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) := rfl

noncomputable def conductorAdditiveCharacterFrequencyVector
    (ψ : AddChar (𝓞 F) ℂ) : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℝ :=
  fun i => conductorUnitAngle (ψ (RingOfIntegers.basis F i))

theorem conductorIntegralDifferenceFrequency_exp (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q q' : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ)
    (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (conductorAdditiveCharacterFrequencyVector
        (conductorIntegralDifferenceChar S Ψ q q' d d') i : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((conductorIntegralFrequencyVector S Ψ q d i -
          conductorIntegralFrequencyVector S Ψ q' d' i : ℝ) : ℂ)) := by
  have h1 := conductorIntegralFrequencyVector_basis S Ψ q d i
  have h2 := conductorIntegralFrequencyVector_basis S Ψ q' d' i
  have hψ : ∀ a : 𝓞 F,
      ‖conductorIntegralDifferenceChar S Ψ q q' d d' a‖ = 1 :=
    conductorIntegralDifferenceChar_norm S Ψ q q' d d'
  have h3 :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (conductorAdditiveCharacterFrequencyVector
          (conductorIntegralDifferenceChar S Ψ q q' d d') i : ℂ)) =
        conductorIntegralDifferenceChar S Ψ q q' d d'
          (RingOfIntegers.basis F i) :=
    conductorUnitAngle_exp (hψ (RingOfIntegers.basis F i))
  have hratio :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((conductorIntegralFrequencyVector S Ψ q d i -
            conductorIntegralFrequencyVector S Ψ q' d' i : ℝ) : ℂ)) =
        conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
          (conductorIntegralAdditivePhaseChar S Ψ q' d' (RingOfIntegers.basis F i))⁻¹ := by
    calc
      _ = Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
              (conductorIntegralFrequencyVector S Ψ q d i : ℂ) -
            2 * (Real.pi : ℂ) * Complex.I *
              (conductorIntegralFrequencyVector S Ψ q' d' i : ℂ)) := by
          congr 1
          push_cast
          ring_nf
      _ = Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I *
            (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) /
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I *
              (conductorIntegralFrequencyVector S Ψ q' d' i : ℂ)) :=
        Complex.exp_sub _ _
      _ = conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
          (conductorIntegralAdditivePhaseChar S Ψ q' d' (RingOfIntegers.basis F i))⁻¹ := by
          rw [h1, h2]
          simp [div_eq_mul_inv]
  have hdeval :
      conductorIntegralDifferenceChar S Ψ q q' d d' (RingOfIntegers.basis F i) =
        conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
          (conductorIntegralAdditivePhaseChar S Ψ q' d' (RingOfIntegers.basis F i))⁻¹ := by
    change conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
        (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹ (RingOfIntegers.basis F i) =
      conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
        (conductorIntegralAdditivePhaseChar S Ψ q' d' (RingOfIntegers.basis F i))⁻¹
    rw [AddChar.inv_apply']
  calc
    _ = conductorIntegralDifferenceChar S Ψ q q' d d'
          (RingOfIntegers.basis F i) := h3
    _ = conductorIntegralAdditivePhaseChar S Ψ q d (RingOfIntegers.basis F i) *
          (conductorIntegralAdditivePhaseChar S Ψ q' d' (RingOfIntegers.basis F i))⁻¹ := hdeval
    _ = _ := hratio.symm

theorem conductorAdditiveCharacter_basisExpansion (ψ : AddChar (𝓞 F) ℂ)
    (hunit : ∀ a, ‖ψ a‖ = 1) (a : 𝓞 F) :
    ψ a = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        (((RingOfIntegers.basis F).repr a i : ℤ) : ℂ) *
          (conductorAdditiveCharacterFrequencyVector ψ i : ℂ)) := by
  classical
  let B := RingOfIntegers.basis F
  let c := B.repr a
  have hsum : a = ∑ i, c i • B i := (B.sum_repr a).symm
  rw [hsum]
  have hchar (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      ψ (c i • B i) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((c i : ℤ) : ℂ) * (conductorAdditiveCharacterFrequencyVector ψ i : ℂ)) := by
    calc
      ψ (c i • B i) = ψ (B i) ^ c i := AddChar.map_zsmul_eq_zpow _ _ _
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (conductorAdditiveCharacterFrequencyVector ψ i : ℂ)) ^ c i := by
        rw [conductorAdditiveCharacterFrequencyVector, conductorUnitAngle_exp (hunit (B i))]
      _ = Complex.exp ((c i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I *
            (conductorAdditiveCharacterFrequencyVector ψ i : ℂ))) := by
        rw [← Complex.exp_int_mul]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((c i : ℤ) : ℂ) * (conductorAdditiveCharacterFrequencyVector ψ i : ℂ)) := by
        congr 1
        ring
  have hprod : ψ (∑ i, c i • B i) = ∏ i, ψ (c i • B i) := by
    induction (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 F))) using
        Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, AddChar.map_add_eq_mul, Finset.prod_insert hi, ih]
  rw [hprod]
  simp_rw [hchar]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hsum]
  simp [c]
  ring

theorem conductorIntegralPhase_basisExpansion (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (a : 𝓞 F) :
    conductorIntegralAdditivePhaseChar S Ψ q d a =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
          (((RingOfIntegers.basis F).repr a i : ℤ) : ℂ) *
            (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) := by
  classical
  let B := RingOfIntegers.basis F
  let c := B.repr a
  have hsum : a = ∑ i, c i • B i := (B.sum_repr a).symm
  rw [hsum]
  have hchar (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
      conductorIntegralAdditivePhaseChar S Ψ q d (c i • B i) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((c i : ℤ) : ℂ) * (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) := by
    calc
      conductorIntegralAdditivePhaseChar S Ψ q d (c i • B i) =
          conductorIntegralAdditivePhaseChar S Ψ q d (B i) ^ c i :=
        AddChar.map_zsmul_eq_zpow _ _ _
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) ^ c i := by
        rw [conductorIntegralFrequencyVector_basis]
      _ = Complex.exp ((c i : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I *
              (conductorIntegralFrequencyVector S Ψ q d i : ℂ))) := by
        rw [← Complex.exp_int_mul]
      _ = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ((c i : ℤ) : ℂ) * (conductorIntegralFrequencyVector S Ψ q d i : ℂ)) := by
        congr 1
        ring
  have hprod :
      conductorIntegralAdditivePhaseChar S Ψ q d (∑ i, c i • B i) =
        ∏ i, conductorIntegralAdditivePhaseChar S Ψ q d (c i • B i) := by
    classical
    induction (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ) using
        Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, AddChar.map_add_eq_mul, Finset.prod_insert hi, ih]
  rw [hprod]
  simp_rw [hchar]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hsum]
  simp [c]
  ring

theorem conductorIntegralPhase_basisProduct (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) (a : 𝓞 F) :
    conductorIntegralAdditivePhaseChar S Ψ q d a =
      ∏ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        OAI.LargePrimeGaps.bvExp
          ((((RingOfIntegers.basis F).repr a i : ℤ) : ℝ) *
            conductorIntegralFrequencyVector S Ψ q d i) := by
  rw [conductorIntegralPhase_basisExpansion]
  simp_rw [OAI.LargePrimeGaps.bvExp]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

/-- A nonzero ideal of bounded index contains a nonzero element with small integral-basis
coordinates. This is the finite pigeonhole form of Minkowski's lattice bound. -/
theorem exists_nonzero_mem_ideal_small_integralBasis_coords
    (K : Ideal (𝓞 F)) (hK : K ≠ ⊥) (L : ℕ)
    (hsize : (L + 1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) >
      Ideal.absNorm K) :
    ∃ a : 𝓞 F, a ∈ K ∧ a ≠ 0 ∧
      ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        |(RingOfIntegers.basis F).equivFun a i| ≤ L := by
  classical
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let B := RingOfIntegers.basis F
  let box : Finset (I → ℕ) := Fintype.piFinset (fun _ => Finset.range (L + 1))
  let elem : (I → ℕ) → 𝓞 F := fun c => B.equivFun.symm (fun i => (c i : ℤ))
  letI : Finite (𝓞 F ⧸ K) := Ring.HasFiniteQuotients.finiteQuotient hK
  letI : Fintype (𝓞 F ⧸ K) := Fintype.ofFinite _
  have hcardBox : box.card = (L + 1) ^ Fintype.card I := by
    simp [box]
  have hcardQuot : Fintype.card (𝓞 F ⧸ K) = Ideal.absNorm K := by
    simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  let f : (I → ℕ) → (𝓞 F ⧸ K) := fun c => Ideal.Quotient.mk K (elem c)
  letI : Fintype {c : I → ℕ // c ∈ box} := Fintype.ofFinite _
  have hcardDom : Fintype.card {c : I → ℕ // c ∈ box} = box.card := by simp
  have hnotinj : ¬ Function.Injective (fun c : {c : I → ℕ // c ∈ box} => f c.1) := by
    intro hinj
    have hle := Fintype.card_le_of_injective (fun c : {c : I → ℕ // c ∈ box} => f c.1) hinj
    rw [hcardDom, hcardBox, hcardQuot] at hle
    exact (not_le_of_gt hsize) hle
  obtain ⟨x, y, hxy, hfx⟩ := Function.not_injective_iff.mp hnotinj
  let a : 𝓞 F := elem x.1 - elem y.1
  have hmem : a ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk K (elem x.1 - elem y.1) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  have hrepr : B.equivFun a = fun i => (x.1 i : ℤ) - (y.1 i : ℤ) := by
    change B.equivFun (B.equivFun.symm (fun i => (x.1 i : ℤ)) -
      B.equivFun.symm (fun i => (y.1 i : ℤ))) = _
    rw [map_sub, B.equivFun.apply_symm_apply, B.equivFun.apply_symm_apply]
    ext i
    rfl
  have hne : a ≠ 0 := by
    intro ha
    have hxy' : x.1 = y.1 := by
      apply funext
      intro i
      have := congrFun hrepr i
      rw [ha, map_zero] at this
      exact_mod_cast (sub_eq_zero.mp this.symm)
    exact hfx (Subtype.ext hxy')
  refine ⟨a, hmem, hne, ?_⟩
  intro i
  rw [hrepr]
  have hxrange : x.1 i < L + 1 :=
    Finset.mem_range.mp ((Fintype.mem_piFinset.mp x.2) i)
  have hyrange : y.1 i < L + 1 :=
    Finset.mem_range.mp ((Fintype.mem_piFinset.mp y.2) i)
  have hxnonneg : 0 ≤ (x.1 i : ℤ) := Int.natCast_nonneg _
  have hynonneg : 0 ≤ (y.1 i : ℤ) := Int.natCast_nonneg _
  have hupper : (x.1 i : ℤ) - (y.1 i : ℤ) ≤ L := by omega
  have hlower : -(L : ℤ) ≤ (x.1 i : ℤ) - (y.1 i : ℤ) := by omega
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- A natural side length whose d-dimensional box dominates a conductor norm V². -/
noncomputable def conductorFrequencyRadius (V : ℝ) (d : ℕ) : ℕ :=
  ⌊Real.rpow (V ^ 2) (1 / (d : ℝ))⌋₊

theorem conductorFrequencyRadius_bounds {V : ℝ} (hV : 2 ≤ V) {d : ℕ} (hd : 0 < d) :
    (V ^ 2 : ℝ) < ((conductorFrequencyRadius V d + 1 : ℕ) : ℝ) ^ d ∧
      (conductorFrequencyRadius V d : ℝ) ≤
        2 * Real.rpow (V ^ 2) (1 / (d : ℝ)) := by
  let x := Real.rpow (V ^ 2) (1 / (d : ℝ))
  let L := conductorFrequencyRadius V d
  have hxnonneg : 0 ≤ x := Real.rpow_nonneg (sq_nonneg V) _
  have hxpow : x ^ d = V ^ 2 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg V)]
    have he : (1 / (d : ℝ)) * (d : ℝ) = 1 := by
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)]
    rw [he, Real.rpow_one]
  have hxlt : x < (L + 1 : ℕ) := by
    simpa [L, conductorFrequencyRadius, x] using Nat.lt_floor_add_one x
  have hpowlt := pow_lt_pow_left₀ hxlt hxnonneg (n := d) (Nat.ne_of_gt hd)
  constructor
  · simpa [hxpow] using hpowlt
  · have hL : (L : ℝ) ≤ x := Nat.floor_le hxnonneg
    have hx1 : 1 ≤ x := Real.one_le_rpow (by nlinarith [hV]) (by positivity)
    change (L : ℝ) ≤ 2 * x
    linarith

/-- A fixed coefficient bound for multiplication in an integral basis. -/
noncomputable def conductorBasisMultiplicationBound : ℝ :=
  ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
    ∑ j : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      ∑ k : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        |(((RingOfIntegers.basis F).equivFun
          (RingOfIntegers.basis F i * RingOfIntegers.basis F j) k : ℤ) : ℝ)|

theorem conductorBasis_mul_coord_bound (a : 𝓞 F) (L : ℕ)
    (ha : ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      |(((RingOfIntegers.basis F).equivFun a i : ℤ) : ℝ)| ≤ L)
    (j k : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    |(((RingOfIntegers.basis F).equivFun
      (a * RingOfIntegers.basis F j) k : ℤ) : ℝ)| ≤
        (L : ℝ) * conductorBasisMultiplicationBound (F := F) := by
  classical
  let B := RingOfIntegers.basis F
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  have hmul : B.equivFun (a * B j) =
      ∑ i : I, B.equivFun a i • B.equivFun (B i * B j) := by
    have hsum : a = ∑ i : I, B.equivFun a i • B i := (B.sum_repr a).symm
    calc
      B.equivFun (a * B j) =
          B.equivFun ((∑ i : I, B.equivFun a i • B i) * B j) := by
        rw [← hsum]
      _ = B.equivFun (∑ i : I, B.equivFun a i • (B i * B j)) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        simp [smul_eq_mul, mul_assoc]
      _ = ∑ i : I, B.equivFun a i • B.equivFun (B i * B j) := by
        simp only [map_sum, map_smul]
  have hcoord :
      (B.equivFun (a * B j) k : ℝ) =
        ∑ i : I, (B.equivFun a i : ℝ) * (B.equivFun (B i * B j) k : ℝ) := by
    rw [hmul]
    simp [Fintype.sum_apply, Pi.smul_apply, Int.cast_sum, Int.cast_mul]
  have hinner :
      (∑ i : I, |(B.equivFun a i : ℝ) * (B.equivFun (B i * B j) k : ℝ)|) ≤
        (L : ℝ) * ∑ i : I, |(B.equivFun (B i * B j) k : ℝ)| := by
    calc
      _ ≤ ∑ i : I, |(B.equivFun a i : ℝ)| * |(B.equivFun (B i * B j) k : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
      _ ≤ ∑ i : I, (L : ℝ) * |(B.equivFun (B i * B j) k : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
      _ = (L : ℝ) * ∑ i : I, |(B.equivFun (B i * B j) k : ℝ)| := by
        rw [Finset.mul_sum]
  have hsub :
      (∑ i : I, |(B.equivFun (B i * B j) k : ℝ)|) ≤
        conductorBasisMultiplicationBound (F := F) := by
    unfold conductorBasisMultiplicationBound
    calc
      _ ≤ ∑ i : I, ∑ j' : I, ∑ k' : I,
            |(B.equivFun (B i * B j') k' : ℝ)| := by
        apply Finset.sum_le_sum
        intro i hi
        have hk : |(B.equivFun (B i * B j) k : ℝ)| ≤
            ∑ k' : I, |(B.equivFun (B i * B j) k' : ℝ)| := by
          change (fun k' : I => |(B.equivFun (B i * B j) k' : ℝ)|) k ≤
            ∑ k' ∈ Finset.univ, |(B.equivFun (B i * B j) k' : ℝ)|
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun k' => |(B.equivFun (B i * B j) k' : ℝ)|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        have hj : (∑ k' : I, |(B.equivFun (B i * B j) k' : ℝ)|) ≤
            ∑ j' : I, ∑ k' : I, |(B.equivFun (B i * B j') k' : ℝ)| :=
          by
            change (∑ k' ∈ Finset.univ, |(B.equivFun (B i * B j) k' : ℝ)|) ≤
              ∑ j' ∈ Finset.univ, ∑ k' ∈ Finset.univ,
                |(B.equivFun (B i * B j') k' : ℝ)|
            exact Finset.single_le_sum (s := Finset.univ)
              (f := fun j' => ∑ k' ∈ Finset.univ,
                |(B.equivFun (B i * B j') k' : ℝ)|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
              (Finset.mem_univ j)
        exact le_trans hk hj
      _ = conductorBasisMultiplicationBound (F := F) := rfl
  calc
    |(B.equivFun (a * B j) k : ℝ)| = |∑ i : I,
        (B.equivFun a i : ℝ) * (B.equivFun (B i * B j) k : ℝ)| := by rw [hcoord]
    _ ≤ ∑ i : I, |(B.equivFun a i : ℝ) * (B.equivFun (B i * B j) k : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (L : ℝ) * ∑ i : I, |(B.equivFun (B i * B j) k : ℝ)| := hinner
    _ ≤ (L : ℝ) * conductorBasisMultiplicationBound (F := F) :=
      mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)

 /-- The ideal annihilator of an additive character under ring multiplication. -/
def conductorAdditiveAnnihilator {R : Type*} [CommRing R]
    (ψ : AddChar R ℂ) : Ideal R where
  carrier := {a | ∀ x, ψ (a * x) = 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    rw [add_mul, AddChar.map_add_eq_mul, ha x, hb x, one_mul]
  smul_mem' := by
    intro r a ha x
    change ψ ((r * a) * x) = 1
    simpa [mul_assoc, mul_left_comm, mul_comm] using ha (r * x)

theorem conductorAdditiveChar_angle_separation (ψ : AddChar (𝓞 F) ℂ)
    (hunit : ∀ a, ‖ψ a‖ = 1) (hψ : ψ ≠ 1)
    (K : Ideal (𝓞 F)) (hK : K ≠ ⊥)
    (hKann : K ≤ conductorAdditiveAnnihilator ψ)
    {V : ℝ} (hV : 2 ≤ V) (hKnorm : (Ideal.absNorm K : ℝ) ≤ V ^ 2) :
    ∃ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      1 / (4 * (Module.finrank ℚ F : ℝ) *
        (conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ))) ≤
        |conductorAdditiveCharacterFrequencyVector ψ i| := by
  classical
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let d := Module.finrank ℚ F
  let L := conductorFrequencyRadius V d
  let M := conductorBasisMultiplicationBound (F := F) + 1
  let δ := 1 / (2 * (d : ℝ) * M * L)
  have hd : 0 < d := Module.finrank_pos
  have hdim : Fintype.card I = d := (Module.finrank_eq_card_basis (NumberField.integralBasis F)).symm
  have hLbounds := conductorFrequencyRadius_bounds hV (d := d) hd
  have hsizeReal : (Ideal.absNorm K : ℝ) < ((L + 1 : ℕ) : ℝ) ^ Fintype.card I := by
    calc
      (Ideal.absNorm K : ℝ) ≤ V ^ 2 := hKnorm
      _ < ((L + 1 : ℕ) : ℝ) ^ d := by
        rw [show ((L + 1 : ℕ) : ℝ) ^ d = ((L + 1 : ℕ) : ℝ) ^ d from rfl]
        exact hLbounds.1
      _ = ((L + 1 : ℕ) : ℝ) ^ Fintype.card I := by rw [hdim]
  have hsize : (L + 1) ^ Fintype.card I > Ideal.absNorm K := by exact_mod_cast hsizeReal
  obtain ⟨a, haK, ha0, hcoords⟩ :=
    exists_nonzero_mem_ideal_small_integralBasis_coords K hK L hsize
  have hcoordsReal : ∀ i : I,
      |(((RingOfIntegers.basis F).equivFun a i : ℤ) : ℝ)| ≤ (L : ℝ) := by
    intro i
    exact_mod_cast hcoords i
  have hCmul : 0 ≤ conductorBasisMultiplicationBound (F := F) := by
    unfold conductorBasisMultiplicationBound
    positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hL1 : 0 < L := by
    have hx : 1 ≤ Real.rpow (V ^ 2) (1 / (d : ℝ)) :=
      Real.one_le_rpow (by nlinarith [hV]) (by positivity)
    have hfloor : 1 ≤ conductorFrequencyRadius V d :=
      (Nat.one_le_floor_iff _).2 hx
    exact lt_of_lt_of_le Nat.zero_lt_one hfloor
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC0 : 0 < (d : ℝ) * M * (L : ℝ) := by
    have hd' : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    have hL' : 0 < (L : ℝ) := Nat.cast_pos.mpr hL1
    positivity
  have hfreqSmall : ¬ ∀ i : I,
      |conductorAdditiveCharacterFrequencyVector ψ i| < δ := by
    intro hsmall
    have hzero (j : I) :
        (∑ i : I,
          (((RingOfIntegers.basis F).repr (a * RingOfIntegers.basis F j) i : ℤ) : ℝ) *
            conductorAdditiveCharacterFrequencyVector ψ i) = 0 := by
      let s : ℝ := ∑ i : I,
        (((RingOfIntegers.basis F).repr (a * RingOfIntegers.basis F j) i : ℤ) : ℝ) *
          conductorAdditiveCharacterFrequencyVector ψ i
      have hphase : ψ (a * RingOfIntegers.basis F j) = 1 :=
        hKann haK (RingOfIntegers.basis F j)
      have hexp := conductorAdditiveCharacter_basisExpansion ψ hunit
        (a * RingOfIntegers.basis F j)
      have hexp1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) = 1 := by
        simpa [s, Complex.ofReal_sum, Complex.ofReal_mul] using hexp.symm.trans hphase
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
      have hsc : (s : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
        calc
          (2 * (Real.pi : ℂ) * Complex.I) * (s : ℂ) = n * (2 * (Real.pi : ℂ) * Complex.I) := hn
          _ = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by ring
      have hsint : s = n := Complex.ofReal_inj.mp hsc
      have hcoeff :
          ∀ i : I,
            |(((RingOfIntegers.basis F).equivFun
                (a * RingOfIntegers.basis F j) i : ℤ) : ℝ)| ≤
              (L : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) := by
        intro i
        calc
          |(((RingOfIntegers.basis F).equivFun
              (a * RingOfIntegers.basis F j) i : ℤ) : ℝ)| ≤
              (L : ℝ) * conductorBasisMultiplicationBound (F := F) :=
            conductorBasis_mul_coord_bound a L hcoordsReal j i
          _ ≤ (L : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith [hCmul]) (Nat.cast_nonneg L)
      have hsbound : |s| ≤ (d : ℝ) * (L : ℝ) * M * δ := by
        calc
          |∑ i : I,
              (((RingOfIntegers.basis F).repr (a * RingOfIntegers.basis F j) i : ℤ) : ℝ) *
                conductorAdditiveCharacterFrequencyVector ψ i| ≤
              ∑ i : I,
                |(((RingOfIntegers.basis F).equivFun
                  (a * RingOfIntegers.basis F j) i : ℤ) : ℝ)| *
                  |conductorAdditiveCharacterFrequencyVector ψ i| := by
            change |∑ i ∈ Finset.univ,
                (((RingOfIntegers.basis F).repr
                  (a * RingOfIntegers.basis F j) i : ℤ) : ℝ) *
                  conductorAdditiveCharacterFrequencyVector ψ i| ≤
              ∑ i ∈ Finset.univ,
                |(((RingOfIntegers.basis F).equivFun
                  (a * RingOfIntegers.basis F j) i : ℤ) : ℝ)| *
                  |conductorAdditiveCharacterFrequencyVector ψ i|
            exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
              apply Finset.sum_congr rfl
              intro i hi
              simp [abs_mul])
          _ ≤ ∑ i : I, (L : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) * δ := by
            apply Finset.sum_le_sum
            intro i hi
            have hc := hcoeff i
            have ht := hsmall i
            calc
              _ = |(((RingOfIntegers.basis F).equivFun
                    (a * RingOfIntegers.basis F j) i : ℤ) : ℝ)| *
                    |conductorAdditiveCharacterFrequencyVector ψ i| := rfl
              _ ≤ _ := mul_le_mul hc (le_of_lt ht) (abs_nonneg _) (by positivity)
          _ = (Fintype.card I : ℝ) *
                ((L : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) * δ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ = (d : ℝ) * (L : ℝ) *
                (conductorBasisMultiplicationBound (F := F) + 1) * δ := by
            rw [hdim]
            ring
          _ = (d : ℝ) * (L : ℝ) * M * δ := by
            rfl
      have hsprod : (d : ℝ) * (L : ℝ) * M * δ = 1 / 2 := by
        dsimp [δ, M]
        field_simp [hC0.ne']
        <;> ring
      have hsnorm : |(n : ℝ)| < 1 := by
        rw [← hsint]
        rw [hsprod] at hsbound
        exact lt_of_le_of_lt hsbound (by norm_num)
      have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hsnorm).1
      have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hsnorm).2
      have hnzero : n = 0 := by omega
      have hs0 : s = 0 := by simp [hsint, hnzero]
      simpa [s] using hs0
    let Bq := NumberField.integralBasis F
    let f : F →ₗ[ℚ] ℝ := Bq.constr ℚ (conductorAdditiveCharacterFrequencyVector ψ)
    have hmulBasis (j : I) : f ((a : F) * Bq j) = 0 := by
      have harg : (a : F) * Bq j =
          algebraMap (𝓞 F) F (a * RingOfIntegers.basis F j) := by
        simp [Bq, NumberField.integralBasis_apply, map_mul]
      rw [harg]
      have h0 := hzero j
      change (Bq.constr ℚ (conductorAdditiveCharacterFrequencyVector ψ))
        (algebraMap (𝓞 F) F (a * RingOfIntegers.basis F j)) = 0
      rw [Bq.constr_apply]
      rw [Finsupp.sum_fintype _
        (fun i c => c • conductorAdditiveCharacterFrequencyVector ψ i)
        (fun _ => zero_smul _ _)]
      have hrepr (i : I) :
          Bq.repr (algebraMap (𝓞 F) F
              (a * RingOfIntegers.basis F j)) i =
            ((RingOfIntegers.basis F).repr
              (a * RingOfIntegers.basis F j) i : ℚ) := by
        exact NumberField.integralBasis_repr_apply (K := F)
          (a * RingOfIntegers.basis F j) i
      simp_rw [hrepr, Rat.smul_def]
      exact h0
    have hmulAll (y : F) : f ((a : F) * y) = 0 := by
      have hmul : (a : F) * y =
          ∑ i : I, (Bq.repr y i) • ((a : F) * Bq i) := by
        calc
          (a : F) * y = (a : F) * ∑ i : I, (Bq.repr y i) • Bq i :=
            congrArg (fun z : F => (a : F) * z) (Bq.sum_repr y).symm
          _ = ∑ i : I, (a : F) * ((Bq.repr y i) • Bq i) := by
            rw [Finset.mul_sum]
          _ = ∑ i : I, (Bq.repr y i) • ((a : F) * Bq i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      rw [hmul, map_sum]
      simp_rw [map_smul, hmulBasis]
      simp
    have haF : (a : F) ≠ 0 := by exact_mod_cast ha0
    have hfzero (y : F) : f y = 0 := by
      calc
        f y = f ((a : F) * ((a : F)⁻¹ * y)) := by congr 1 <;> field_simp [haF]
        _ = 0 := hmulAll _
    have hfreqzero (i : I) :
        conductorAdditiveCharacterFrequencyVector ψ i = 0 := by
      have hi := hfzero (Bq i)
      change (Bq.constr ℚ (conductorAdditiveCharacterFrequencyVector ψ)) (Bq i) = 0 at hi
      rw [Bq.constr_basis] at hi
      exact hi
    have hψone : ψ = 1 := by
      ext x
      rw [conductorAdditiveCharacter_basisExpansion ψ hunit x]
      simp [hfreqzero]
    exact hψ hψone
  have hseparated : ∃ i : I,
      δ ≤ |conductorAdditiveCharacterFrequencyVector ψ i| := by
    by_contra h
    push_neg at h
    exact hfreqSmall h
  obtain ⟨i, hi⟩ := hseparated
  refine ⟨i, ?_⟩
  have hδbound :
      1 / (4 * (d : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) *
        Real.rpow (V ^ 2) (1 / (d : ℝ))) ≤ δ := by
    have hXL : (L : ℝ) ≤ 2 * Real.rpow (V ^ 2) (1 / (d : ℝ)) := hLbounds.2
    dsimp [δ, M]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      2 * (d : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) * (L : ℝ) ≤
          2 * (d : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) *
            (2 * Real.rpow (V ^ 2) (1 / (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hXL (by positivity)
      _ = 4 * (d : ℝ) * (conductorBasisMultiplicationBound (F := F) + 1) *
            Real.rpow (V ^ 2) (1 / (d : ℝ)) := by ring
  exact hδbound.trans hi

/-- The annihilator ideal of an integral residue phase is its exact conductor `q`. -/
theorem conductorIntegralAdditivePhaseChar_annihilator (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal)
    (d : (ConductorResidueRing q)ˣ) :
    {a : 𝓞 F | ∀ x : 𝓞 F,
      conductorIntegralAdditivePhaseChar S Ψ q d (a * x) = 1} = q.1 := by
  ext a
  constructor
  · intro ha
    have hshift :
      (Ψ.ψ q).mulShift (Ideal.Quotient.mk q.1 a * (d : ConductorResidueRing q)) = 1 := by
      ext y
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
      have h := ha x
      simpa [conductorIntegralAdditivePhaseChar_apply, AddChar.mulShift_apply,
        hx, map_mul, mul_assoc, mul_comm, mul_left_comm] using h
    have hzero : Ideal.Quotient.mk q.1 a * (d : ConductorResidueRing q) = 0 := by
      by_contra hne
      exact (Ψ.primitive q hne) hshift
    have hmk : Ideal.Quotient.mk q.1 a = 0 := by
      apply d.isUnit.mul_right_injective
      simpa [mul_comm] using hzero
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hmk
  · intro ha x
    simp [conductorIntegralAdditivePhaseChar_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha]

theorem conductorIntegralAdditivePhaseChar_injective (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) {q q' : S.ExtIdeal}
    {d : (ConductorResidueRing q)ˣ} {d' : (ConductorResidueRing q')ˣ}
    (h : conductorIntegralAdditivePhaseChar S Ψ q d =
      conductorIntegralAdditivePhaseChar S Ψ q' d') : q = q' ∧ HEq d d' := by
  have hsets : {a : 𝓞 F | ∀ x : 𝓞 F,
      conductorIntegralAdditivePhaseChar S Ψ q d (a * x) = 1} =
      {a : 𝓞 F | ∀ x : 𝓞 F,
      conductorIntegralAdditivePhaseChar S Ψ q' d' (a * x) = 1} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ha x
      rw [← h]
      exact ha x
    · intro ha x
      rw [h]
      exact ha x
  have hqset : (q.1 : Set (𝓞 F)) = (q'.1 : Set (𝓞 F)) := by
    calc
      (q.1 : Set (𝓞 F)) = {a : 𝓞 F | ∀ x : 𝓞 F,
          conductorIntegralAdditivePhaseChar S Ψ q d (a * x) = 1} :=
        (conductorIntegralAdditivePhaseChar_annihilator S Ψ q d).symm
      _ = {a : 𝓞 F | ∀ x : 𝓞 F,
          conductorIntegralAdditivePhaseChar S Ψ q' d' (a * x) = 1} := hsets
      _ = q'.1 := conductorIntegralAdditivePhaseChar_annihilator S Ψ q' d'
  have hq1 : q.1 = q'.1 := SetLike.coe_injective hqset
  have hq : q = q' := Subtype.ext hq1
  subst q'
  have hshift : (Ψ.ψ q).mulShift (d : ConductorResidueRing q) =
      (Ψ.ψ q).mulShift (d' : ConductorResidueRing q) := by
    ext y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
    have hval := congrArg (fun χ : AddChar (𝓞 F) ℂ => χ a) h
    simpa [conductorIntegralAdditivePhaseChar_apply, AddChar.mulShift_apply,
      ha, mul_comm] using hval
  have hunit : d = d' :=
    Units.ext ((AddChar.to_mulShift_inj_of_isPrimitive (Ψ.primitive q)) hshift)
  cases hunit
  exact ⟨rfl, HEq.rfl⟩

theorem conductorIntegralDifference_annihilator_le (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) {q q' : S.ExtIdeal}
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ) :
    q.1 ⊓ q'.1 ≤ conductorAdditiveAnnihilator
      (conductorIntegralAdditivePhaseChar S Ψ q d *
        (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹) := by
  intro a ha
  change a ∈ q.1 ∧ a ∈ q'.1 at ha
  change ∀ x, _
  intro x
  simp [conductorIntegralAdditivePhaseChar_apply,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha.1, Ideal.Quotient.eq_zero_iff_mem.mpr ha.2]

theorem conductorIntegralDifference_annihilator_norm_le (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) {q q' : S.ExtIdeal}
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ) :
    Ideal.absNorm (conductorAdditiveAnnihilator
      (conductorIntegralAdditivePhaseChar S Ψ q d *
        (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹)) ≤
      Ideal.absNorm q.1 * Ideal.absNorm q'.1 := by
  let J := q.1 ⊓ q'.1
  let A := conductorAdditiveAnnihilator
    (conductorIntegralAdditivePhaseChar S Ψ q d *
      (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹)
  have hprod : q.1 * q'.1 ≠ ⊥ := by
    intro h
    rcases (Ideal.mul_eq_bot.mp h) with hq | hq'
    · exact q.2.1 hq
    · exact q'.2.1 hq'
  have hprod_le : q.1 * q'.1 ≤ J := by
    exact Ideal.mul_le_inf
  have hJne : J ≠ ⊥ := by
    intro h
    exact hprod (bot_unique (h ▸ hprod_le))
  have hJA : J ≤ A := conductorIntegralDifference_annihilator_le S Ψ d d'
  have hAne : A ≠ ⊥ := by
    intro h
    exact hJne (bot_unique (h ▸ hJA))
  have hJpos : 0 < Ideal.absNorm J :=
    Ideal.absNorm_pos_of_nonZeroDivisors ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJne⟩
  have hprodpos : 0 < Ideal.absNorm (q.1 * q'.1) := by
    rw [map_mul]
    exact mul_pos (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨q.1, mem_nonZeroDivisors_iff_ne_zero.mpr q.2.1⟩)
      (Ideal.absNorm_pos_of_nonZeroDivisors
      ⟨q'.1, mem_nonZeroDivisors_iff_ne_zero.mpr q'.2.1⟩)
  calc
    Ideal.absNorm A ≤ Ideal.absNorm J :=
      Nat.le_of_dvd hJpos (Ideal.absNorm_dvd_absNorm_of_le hJA)
    _ ≤ Ideal.absNorm (q.1 * q'.1) :=
      Nat.le_of_dvd hprodpos (Ideal.absNorm_dvd_absNorm_of_le hprod_le)
    _ = Ideal.absNorm q.1 * Ideal.absNorm q'.1 := by rw [map_mul]

theorem conductorExteriorCutoff_absNorm_le (S : A1.SData F CE condη)
    {V : ℝ} (hV : 0 ≤ V) {q : S.ExtIdeal}
    (hq : q ∈ conductorExteriorCutoff S V) :
    (Ideal.absNorm q.1 : ℝ) ≤ V := by
  classical
  let B := (conductorIdealCutoff F V).filter S.IsExterior
  dsimp [conductorExteriorCutoff, B] at hq
  obtain ⟨I, hI, hIq⟩ := Finset.mem_map.mp hq
  have hIbase : I.1 ∈ conductorIdealCutoff F V :=
    (Finset.mem_filter.mp I.2).1
  have hraw : I.1 = q.1 := congrArg (fun x : S.ExtIdeal => x.1) hIq
  have hqbase : q.1 ∈ conductorIdealCutoff F V := by
    rw [← hraw]
    exact hIbase
  have hnat : Ideal.absNorm q.1 ≤ ⌊V⌋₊ := by
    simpa [conductorIdealCutoff] using hqbase
  have hreal : (Ideal.absNorm q.1 : ℝ) ≤ (⌊V⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact le_trans hreal (Nat.floor_le hV)

theorem conductorUniformizer_norm {v : A1.FinPlace F} (π : 𝓞 F)
    (hπ : v.intValuation π = WithZero.exp (-1 : ℤ)) :
    ‖FinitePlace.embedding v (algebraMap (𝓞 F) F π)‖ =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [FinitePlace.norm_embedding_int, hπ]
  have hNv : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
    HeightOneSpectrum.absNorm_ne_zero v
  have hval : WithZero.exp (-1 : ℤ) ≠ 0 := by simp
  rw [WithZeroMulInt.toNNReal_neg_apply hNv hval]
  have htoAdd : (WithZero.unzero hval).toAdd = (-1 : ℤ) := by
    apply (WithZero.toAdd_unzero_eq_iff hval (-1)).2
    rfl
  rw [htoAdd]
  simp [zpow_neg]

theorem conductorExistsPrincipalPowerGenerator (v : A1.FinPlace F) :
    ∃ π : 𝓞 F,
      Ideal.span {π} = v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let n := Fintype.card (ClassGroup (𝓞 F))
  let p₀ : (Ideal (𝓞 F))⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hClass : ClassGroup.mk0 p₀ ^ n = 1 := by
    simpa [n, p₀] using (pow_card_eq_one (x := ClassGroup.mk0 p₀))
  have hpow0 : v.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ v.ne_bot
  have hClassPow :
      ClassGroup.mk0 ⟨v.asIdeal ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hpow0⟩ = 1 := by
    change ClassGroup.mk0 (p₀ ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (v.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hpow0)).mp hClassPow
  obtain ⟨π, hπ⟩ := hPrincipal.principal
  exact ⟨π, hπ.symm⟩

theorem conductorPrimeElement_norm_le_half (v : A1.FinPlace F) (a : 𝓞 F)
    (ha0 : a ≠ 0) (hamem : a ∈ v.asIdeal) :
    ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ ≤ 1 / 2 := by
  have hlt : ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < 1 :=
    (FinitePlace.norm_lt_one_iff_mem (K := F) (v := v) a).2 hamem
  have hneMap : algebraMap (𝓞 F) F a ≠ 0 := by
    intro hz
    have hzero : algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F 0 := by simpa using hz
    exact ha0 ((IsFractionRing.injective (𝓞 F) F) hzero)
  have hneEmbed : FinitePlace.embedding v (algebraMap (𝓞 F) F a) ≠ 0 := by
    intro hz
    exact hneMap ((RingHom.injective (FinitePlace.embedding v)) (by simpa using hz))
  have hpos : 0 < ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ := norm_pos_iff.mpr hneEmbed
  let z := (FinitePlace.embedding v (algebraMap (𝓞 F) F a))⁻¹
  have hz : 1 < ‖z‖ := by
    dsimp [z]
    rw [norm_inv]
    simpa [one_div] using (one_lt_div hpos).2 hlt
  have htwo := FinitePlace.two_le_norm_of_one_lt_norm (K := F) (v := v) z hz
  have hmul : 2 * ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ ≤ 1 := by
    have htwo' : (2 : ℝ) ≤
        1 / ‖FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ := by
      simpa [z, norm_inv] using htwo
    exact (le_div_iff₀ hpos).mp htwo'
  nlinarith

theorem conductorPrincipalPower_norm_bound (v w : A1.FinPlace F) {n : ℕ}
    (hn : 0 < n) (π : 𝓞 F) (hπ : Ideal.span {π} = v.asIdeal ^ n)
    (N : ℕ) :
    ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π ^ N))‖ ≤
      if v = w then (1 / 2 : ℝ) ^ N else 1 := by
  have hπ0 : π ≠ 0 := by
    intro hzero
    have hpow0 : v.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ v.ne_bot
    apply hpow0
    rw [← hπ, hzero]
    simp
  have hπmem : π ∈ v.asIdeal := by
    have hmem : π ∈ Ideal.span {π} := Ideal.subset_span (by simp)
    rw [hπ] at hmem
    exact (Ideal.pow_le_self (Nat.ne_of_gt hn)) hmem
  have hbase : ‖FinitePlace.embedding w (algebraMap (𝓞 F) F π)‖ ≤
      if v = w then (1 / 2 : ℝ) else 1 := by
    by_cases hvw : v = w
    · subst w
      simpa using conductorPrimeElement_norm_le_half v π hπ0 hπmem
    · rw [if_neg hvw]
      exact FinitePlace.norm_le_one (K := F) (v := w) π
  have hpowNorm : ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π ^ N))‖ =
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F π)‖ ^ N := by
    simp [map_pow, norm_pow]
  rw [hpowNorm]
  by_cases hvw : v = w
  · subst w
    simp only [if_pos rfl] at hbase ⊢
    exact pow_le_pow_left₀ (by norm_num) hbase N
  · simp only [if_neg hvw] at hbase ⊢
    simpa using pow_le_pow_left₀ (by norm_num) hbase N

private theorem exists_conductorGenerator_S_unit_scale_localUniformizers (S : A1.SData F CE condη)
    (G : ConductorGenerators S) :
    ∃ c : 𝓞 F, c ≠ 0 ∧
      (∀ I (v : S.Sf), A1.absFin v.1
        (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1) ∧
      (∀ w : A1.FinPlace F, w ∉ S.Sf →
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1) := by
  classical
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hn : 0 < n := Fintype.card_pos
  let π : S.Sf → 𝓞 F := fun v =>
    Classical.choose (conductorExistsPrincipalPowerGenerator v.1)
  have hπ (v : S.Sf) : Ideal.span {π v} = v.1.asIdeal ^ n := by
    simpa [n] using Classical.choose_spec (conductorExistsPrincipalPowerGenerator v.1)
  have hπ0 (v : S.Sf) : π v ≠ 0 := by
    intro hz
    have hpow0 : v.1.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ v.1.ne_bot
    have hspan0 : Ideal.span {π v} = ⊥ := by simp [hz]
    exact hpow0 (hπ v ▸ hspan0)
  have hπmem (v : S.Sf) : π v ∈ v.1.asIdeal := by
    have hmem : π v ∈ Ideal.span {π v} := Ideal.subset_span (by simp)
    rw [hπ v] at hmem
    exact (Ideal.pow_le_self (Nat.ne_of_gt hn)) hmem
  have hπnot (v : S.Sf) (w : A1.FinPlace F) (hvw : v.1 ≠ w) :
      π v ∉ w.asIdeal := by
    intro hm
    have hle : Ideal.span {π v} ≤ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hm
    rw [hπ v] at hle
    have hle' : v.1.asIdeal ≤ w.asIdeal :=
      (w.isPrime.pow_le_iff (Nat.ne_of_gt hn)).mp hle
    have hideal : v.1.asIdeal = w.asIdeal :=
      v.1.isMaximal.eq_of_le w.isPrime.ne_top hle'
    exact hvw (HeightOneSpectrum.ext hideal)
  let N : ℕ := ⌊G.height⌋₊ + 1
  have hHN : G.height < (N : ℝ) := by
    simpa [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one G.height
  have hpowN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := one_add_le_pow_of_two_add_nonneg (R := ℝ) (a := 1)
      (by norm_num) N
    norm_num at h
    linarith
  have hHpow : G.height ≤ (2 : ℝ) ^ N := le_trans hHN.le hpowN
  let c : 𝓞 F := ∏ v : S.Sf, π v ^ N
  have hc0 : c ≠ 0 := by
    dsimp [c]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ (hπ0 v)
  have hfactor (v : S.Sf) (w : A1.FinPlace F) :
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ ≤
        if v.1 = w then (1 / 2 : ℝ) ^ N else 1 :=
    conductorPrincipalPower_norm_bound v.1 w hn (π v) (hπ v) N
  have hnormcS (w : S.Sf) :
      ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ ≤ ((2 : ℝ) ^ N)⁻¹ := by
    have hrepr :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf,
            ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hprod :
        (∏ v : S.Sf,
          ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖) ≤
          ∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1 := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact norm_nonneg _
      · intro v hv
        exact hfactor v w.1
    have hprod_ite :
        (∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1) =
          (1 / 2 : ℝ) ^ N := by
      have heq (v : S.Sf) : (v.1 = w.1) ↔ v = w := Subtype.ext_iff.symm
      simp [heq]
    rw [hprod_ite] at hprod
    have hhalf : (1 / 2 : ℝ) ^ N = ((2 : ℝ) ^ N)⁻¹ := by rw [one_div, inv_pow]
    simpa [hhalf] using hprod
  have hnormcOutside (w : A1.FinPlace F) (hw : w ∉ S.Sf) :
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1 := by
    have hrepr :
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf,
            ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hfactorOne (v : S.Sf) :
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ = 1 := by
      have hvw : v.1 ≠ w := by
        intro heq
        exact hw (heq ▸ v.2)
      have hnot := hπnot v w hvw
      have hπnorm :=
        (FinitePlace.norm_eq_one_iff_notMem (K := F) (v := w) (π v)).2 hnot
      simp [map_pow, norm_pow, hπnorm]
    simp_rw [hfactorOne]
    simp
  have hscale (I : S.ExtIdeal) (w : S.Sf) :
      A1.absFin w.1 (algebraMap F (w.1.adicCompletion F)
        ((c : F) * (G.gen I : F))) ≤ 1 := by
    rw [A1.absFin_algebraMap, map_mul, norm_mul]
    have hgen := G.finite_bound I w
    rw [A1.absFin_algebraMap] at hgen
    have hmul :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ *
          ‖FinitePlace.embedding w.1 (G.gen I : F)‖ ≤
            ((2 : ℝ) ^ N)⁻¹ * G.height :=
      mul_le_mul (hnormcS w) hgen (norm_nonneg _) (by positivity)
    have hfinal : ((2 : ℝ) ^ N)⁻¹ * G.height ≤ 1 := by
      have hdiv : G.height / (2 : ℝ) ^ N ≤ 1 := (div_le_one (by positivity)).2 hHpow
      calc
        ((2 : ℝ) ^ N)⁻¹ * G.height = G.height / (2 : ℝ) ^ N := by
          rw [div_eq_mul_inv]
          ring
        _ ≤ 1 := hdiv
    exact le_trans hmul hfinal
  exact ⟨c, hc0, hscale, hnormcOutside⟩

theorem conductorSUnit_quotient_isUnit (S : A1.SData F CE condη)
    (q : S.ExtIdeal) (c : 𝓞 F)
    (houtside : ∀ w : A1.FinPlace F, w ∉ S.Sf →
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1) :
    IsUnit (Ideal.Quotient.mk q.1 c) := by
  have hsum : Ideal.span {c} ⊔ q.1 = ⊤ := by
    by_contra hsum
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hsum
    have hMne : M ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)
    let w : A1.FinPlace F := ⟨M, hM.isPrime, hMne⟩
    have hspan : Ideal.span {c} ≤ w.asIdeal := le_trans le_sup_left hle
    have hq : q.1 ≤ w.asIdeal := le_trans le_sup_right hle
    by_cases hw : w ∈ S.Sf
    · exact q.2.2 w hw hq
    · have hc : c ∈ w.asIdeal := (Ideal.span_singleton_le_iff_mem w.asIdeal).mp hspan
      have hlt := (FinitePlace.norm_lt_one_iff_mem (K := F) (v := w) c).2 hc
      rw [houtside w hw] at hlt
      norm_num at hlt
  have hcop : IsCoprime (Ideal.span {c}) q.1 := Ideal.isCoprime_iff_sup_eq.mpr hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.isCoprime_iff_exists.mp hcop)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hx
  have hct : c * t = x := by simpa [mul_comm] using ht
  have hxquot : Ideal.Quotient.mk q.1 x = 1 := by
    have h := congrArg (Ideal.Quotient.mk q.1) hxy
    simpa [Ideal.Quotient.eq_zero_iff_mem.mpr hy] using h
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Ideal.Quotient.mk q.1 t, ?_⟩
  calc
    Ideal.Quotient.mk q.1 c * Ideal.Quotient.mk q.1 t =
        Ideal.Quotient.mk q.1 (c * t) := (map_mul _ _ _).symm
    _ = Ideal.Quotient.mk q.1 x := by rw [hct]
    _ = 1 := hxquot

theorem conductorAdditivePhase_scale (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    (q : S.ExtIdeal) (c : 𝓞 F)
    (hc : IsUnit (Ideal.Quotient.mk q.1 c)) (x : S.R)
    (d : (ConductorResidueRing q)ˣ) :
    Ψ.ψ q (ρ.red q x * (d : ConductorResidueRing q)) =
      Ψ.ψ q
        (ρ.red q ((algebraMap (𝓞 F) S.R c) * x) *
          (d * hc.unit⁻¹ : (ConductorResidueRing q)ˣ)) := by
  let u := hc.unit
  let uInv : (ConductorResidueRing q)ˣ := u⁻¹
  have hu : ρ.red q (algebraMap (𝓞 F) S.R c) = (u : ConductorResidueRing q) := by
    rw [ρ.integral]
    exact hc.unit_spec.symm
  have huinv : (u : ConductorResidueRing q) * (uInv : ConductorResidueRing q) = 1 := by
    simp [uInv]
  have hres : ρ.red q x * (d : ConductorResidueRing q) =
      ρ.red q ((algebraMap (𝓞 F) S.R c) * x) *
        (d * uInv : (ConductorResidueRing q)ˣ) := by
    calc
      ρ.red q x * (d : ConductorResidueRing q) =
          (ρ.red q (algebraMap (𝓞 F) S.R c) * ρ.red q x) *
            ((d : ConductorResidueRing q) * (uInv : ConductorResidueRing q)) := by
        calc
          ρ.red q x * (d : ConductorResidueRing q) =
              ρ.red q x * (d : ConductorResidueRing q) *
                ((u : ConductorResidueRing q) * (uInv : ConductorResidueRing q)) := by
            rw [huinv]
            simp
          _ = (u * ρ.red q x) * ((d : ConductorResidueRing q) * (uInv : ConductorResidueRing q)) := by
            ring
          _ = (ρ.red q (algebraMap (𝓞 F) S.R c) * ρ.red q x) *
                ((d : ConductorResidueRing q) * (uInv : ConductorResidueRing q)) := by
            rw [← hu]
      _ = ρ.red q ((algebraMap (𝓞 F) S.R c) * x) *
            (d * uInv : (ConductorResidueRing q)ˣ) := by
        rw [map_mul, hu]
        simp [Units.val_mul, Units.val_inv]
  simpa [u, uInv] using congrArg (Ψ.ψ q) hres

theorem conductorAdditiveSum_scale (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (q : S.ExtIdeal) (c : 𝓞 F)
    (hc : IsUnit (Ideal.Quotient.mk q.1 c)) (B : Finset S.ExtIdeal)
    (b : S.ExtIdeal → ℂ) :
    (∑ d : (ConductorResidueRing q)ˣ,
      ‖∑ I ∈ B, b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
    (∑ d : (ConductorResidueRing q)ˣ,
      ‖∑ I ∈ B, b I *
        Ψ.ψ q (ρ.red q ((algebraMap (𝓞 F) S.R c) * G.gen I) *
          (d : ConductorResidueRing q))‖ ^ 2) := by
  classical
  let e : (ConductorResidueRing q)ˣ ≃ (ConductorResidueRing q)ˣ :=
    Equiv.mulRight (hc.unit⁻¹)
  let f (d : (ConductorResidueRing q)ˣ) : ℝ :=
    ‖∑ I ∈ B, b I * Ψ.ψ q
      (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2
  let g (d : (ConductorResidueRing q)ˣ) : ℝ :=
    ‖∑ I ∈ B, b I * Ψ.ψ q
      (ρ.red q ((algebraMap (𝓞 F) S.R c) * G.gen I) *
        (d : ConductorResidueRing q))‖ ^ 2
  have hsum (d : (ConductorResidueRing q)ˣ) :
      (∑ I ∈ B, b I * Ψ.ψ q
        (ρ.red q (G.gen I) * (d : ConductorResidueRing q))) =
      (∑ I ∈ B, b I * Ψ.ψ q
        (ρ.red q ((algebraMap (𝓞 F) S.R c) * G.gen I) *
          (e d : ConductorResidueRing q))) := by
    apply Finset.sum_congr rfl
    intro I hI
    congr 1
    exact conductorAdditivePhase_scale S ρ Ψ q c hc (G.gen I) d
  have hfg (d : (ConductorResidueRing q)ˣ) : f d = g (e d) := by
    dsimp [f, g]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hsum d)
  change (∑ d : (ConductorResidueRing q)ˣ, f d) =
    ∑ d : (ConductorResidueRing q)ˣ, g d
  calc
    (∑ d : (ConductorResidueRing q)ˣ, f d) =
        ∑ d : (ConductorResidueRing q)ˣ, g (e d) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hfg d
    _ = ∑ d : (ConductorResidueRing q)ˣ, g d := by
      exact Fintype.sum_equiv e (fun d => g (e d)) g (by intro d; rfl)

theorem exists_conductorGenerator_scale (S : A1.SData F CE condη)
    (G : ConductorGenerators S) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ I (v : S.Sf),
      A1.absFin v.1
        (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1 := by
  classical
  let N : ℕ := ⌊G.height⌋₊ + 1
  have hHN : G.height < (N : ℝ) := by
    simpa [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one G.height
  have hpowN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := one_add_le_pow_of_two_add_nonneg (R := ℝ) (a := 1)
      (by norm_num) N
    norm_num at h
    have h' : 1 + (N : ℝ) ≤ (2 : ℝ) ^ N := h
    linarith
  have hHpow : G.height ≤ (2 : ℝ) ^ N := le_trans hHN.le hpowN
  let u : S.Sf → 𝓞 F := fun v => Classical.choose v.1.intValuation_exists_uniformizer
  have hu (v : S.Sf) :
      v.1.intValuation (u v) = WithZero.exp (-1 : ℤ) :=
    Classical.choose_spec (v.1.intValuation_exists_uniformizer)
  let c : 𝓞 F := ∏ v : S.Sf, u v ^ N
  have hu0 (v : S.Sf) : u v ≠ 0 := by
    intro hzero
    have h := hu v
    rw [hzero] at h
    simp only [map_zero] at h
    have hne : WithZero.exp (-1 : ℤ) ≠ 0 := by simp
    exact hne h.symm
  have hc0 : c ≠ 0 := by
    dsimp [c]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ (hu0 v)
  have hnormc (w : S.Sf) :
      ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ ≤ ((2 : ℝ) ^ N)⁻¹ := by
    have hrepr :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf,
            ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (u v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hfactor (v : S.Sf) :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (u v ^ N))‖ ≤
          if v = w then ((2 : ℝ) ^ N)⁻¹ else 1 := by
      by_cases hv : v = w
      · subst v
        simp only [map_pow, norm_pow, if_pos rfl]
        rw [conductorUniformizer_norm (u w) (hu w)]
        have hN : (2 : ℝ) ^ N ≤
            (Ideal.absNorm w.1.asIdeal : ℝ) ^ N := by
          apply pow_le_pow_left₀ (by norm_num)
          have hNat : 1 < Ideal.absNorm w.1.asIdeal :=
            HeightOneSpectrum.one_lt_absNorm w.1
          have hNat2 : 2 ≤ Ideal.absNorm w.1.asIdeal := Nat.succ_le_iff.mpr hNat
          exact_mod_cast hNat2
        calc
          ((Ideal.absNorm w.1.asIdeal : ℝ)⁻¹) ^ N =
              ((Ideal.absNorm w.1.asIdeal : ℝ) ^ N)⁻¹ := by rw [inv_pow]
          _ ≤ ((2 : ℝ) ^ N)⁻¹ :=
            by simpa [one_div] using
              (one_div_le_one_div_of_le (by positivity) hN)
      · rw [if_neg hv]
        exact FinitePlace.norm_le_one (K := F) (v := w.1) (u v ^ N)
    have hprod :
        (∏ v : S.Sf,
          ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (u v ^ N))‖) ≤
          ∏ v : S.Sf, if v = w then ((2 : ℝ) ^ N)⁻¹ else 1 := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact norm_nonneg _
      · intro v hv
        exact hfactor v
    have hprod_ite :
        (∏ v : S.Sf, if v = w then ((2 : ℝ) ^ N)⁻¹ else 1) =
          ((2 : ℝ) ^ N)⁻¹ := by simp
    rw [hprod_ite] at hprod
    exact hprod
  refine ⟨c, hc0, ?_⟩
  intro I v
  rw [A1.absFin_algebraMap, map_mul, norm_mul]
  have hgen := G.finite_bound I v
  rw [A1.absFin_algebraMap] at hgen
  have hmul :
      ‖FinitePlace.embedding v.1 (algebraMap (𝓞 F) F c)‖ *
        ‖FinitePlace.embedding v.1 (G.gen I : F)‖ ≤
          ((2 : ℝ) ^ N)⁻¹ * G.height :=
    mul_le_mul (hnormc v) hgen (norm_nonneg _) (by positivity)
  have hfinal : ((2 : ℝ) ^ N)⁻¹ * G.height ≤ 1 := by
    have hdiv : G.height / (2 : ℝ) ^ N ≤ 1 := (div_le_one (by positivity)).2 hHpow
    calc
      ((2 : ℝ) ^ N)⁻¹ * G.height = G.height / (2 : ℝ) ^ N := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 1 := hdiv
  exact le_trans hmul hfinal

theorem exists_conductorGenerator_S_unit_scale (S : A1.SData F CE condη)
    (G : ConductorGenerators S) :
    ∃ c : 𝓞 F, c ≠ 0 ∧
      (∀ I (v : S.Sf), A1.absFin v.1
        (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1) ∧
      (∀ w : A1.FinPlace F, w ∉ S.Sf →
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1) := by
  classical
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hn : 0 < n := Fintype.card_pos
  let π : S.Sf → 𝓞 F := fun v =>
    Classical.choose (conductorExistsPrincipalPowerGenerator v.1)
  have hπ (v : S.Sf) : Ideal.span {π v} = v.1.asIdeal ^ n := by
    simpa [n] using Classical.choose_spec (conductorExistsPrincipalPowerGenerator v.1)
  have hπ0 (v : S.Sf) : π v ≠ 0 := by
    intro hz
    have hpow0 : v.1.asIdeal ^ n ≠ ⊥ := pow_ne_zero _ v.1.ne_bot
    have hspan0 : Ideal.span {π v} = ⊥ := by simp [hz]
    exact hpow0 (hπ v ▸ hspan0)
  have hπmem (v : S.Sf) : π v ∈ v.1.asIdeal := by
    have hmem : π v ∈ Ideal.span {π v} := Ideal.subset_span (by simp)
    rw [hπ v] at hmem
    exact (Ideal.pow_le_self (Nat.ne_of_gt hn)) hmem
  have hπnot (v : S.Sf) (w : A1.FinPlace F) (hvw : v.1 ≠ w) :
      π v ∉ w.asIdeal := by
    intro hm
    have hle : Ideal.span {π v} ≤ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem w.asIdeal).mpr hm
    rw [hπ v] at hle
    have hle' : v.1.asIdeal ≤ w.asIdeal :=
      (w.isPrime.pow_le_iff (Nat.ne_of_gt hn)).mp hle
    have hideal : v.1.asIdeal = w.asIdeal :=
      v.1.isMaximal.eq_of_le w.isPrime.ne_top hle'
    exact hvw (HeightOneSpectrum.ext hideal)
  let N : ℕ := ⌊G.height⌋₊ + 1
  have hHN : G.height < (N : ℝ) := by
    simpa [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one G.height
  have hpowN : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    have h := one_add_le_pow_of_two_add_nonneg (R := ℝ) (a := 1)
      (by norm_num) N
    norm_num at h
    linarith
  have hHpow : G.height ≤ (2 : ℝ) ^ N := le_trans hHN.le hpowN
  let c : 𝓞 F := ∏ v : S.Sf, π v ^ N
  have hc0 : c ≠ 0 := by
    dsimp [c]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ (hπ0 v)
  have hfactor (v : S.Sf) (w : A1.FinPlace F) :
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ ≤
        if v.1 = w then (1 / 2 : ℝ) ^ N else 1 :=
    conductorPrincipalPower_norm_bound v.1 w hn (π v) (hπ v) N
  have hnormcS (w : S.Sf) :
      ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ ≤ ((2 : ℝ) ^ N)⁻¹ := by
    have hrepr :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf,
            ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hprod :
        (∏ v : S.Sf,
          ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F (π v ^ N))‖) ≤
          ∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1 := by
      apply Finset.prod_le_prod₀
      · intro v hv
        exact norm_nonneg _
      · intro v hv
        exact hfactor v w.1
    have hprod_ite :
        (∏ v : S.Sf, if v.1 = w.1 then (1 / 2 : ℝ) ^ N else 1) =
          (1 / 2 : ℝ) ^ N := by
      have heq (v : S.Sf) : (v.1 = w.1) ↔ v = w := Subtype.ext_iff.symm
      simp [heq]
    rw [hprod_ite] at hprod
    have hhalf : (1 / 2 : ℝ) ^ N = ((2 : ℝ) ^ N)⁻¹ := by rw [one_div, inv_pow]
    simpa [hhalf] using hprod
  have hnormcOutside (w : A1.FinPlace F) (hw : w ∉ S.Sf) :
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1 := by
    have hrepr :
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ =
          ∏ v : S.Sf,
            ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ := by
      simp [c, map_prod, norm_prod]
    rw [hrepr]
    have hfactorOne (v : S.Sf) :
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F (π v ^ N))‖ = 1 := by
      have hvw : v.1 ≠ w := by
        intro heq
        exact hw (heq ▸ v.2)
      have hnot := hπnot v w hvw
      have hπnorm :=
        (FinitePlace.norm_eq_one_iff_notMem (K := F) (v := w) (π v)).2 hnot
      simp [map_pow, norm_pow, hπnorm]
    simp_rw [hfactorOne]
    simp
  have hscale (I : S.ExtIdeal) (w : S.Sf) :
      A1.absFin w.1 (algebraMap F (w.1.adicCompletion F)
        ((c : F) * (G.gen I : F))) ≤ 1 := by
    rw [A1.absFin_algebraMap, map_mul, norm_mul]
    have hgen := G.finite_bound I w
    rw [A1.absFin_algebraMap] at hgen
    have hmul :
        ‖FinitePlace.embedding w.1 (algebraMap (𝓞 F) F c)‖ *
          ‖FinitePlace.embedding w.1 (G.gen I : F)‖ ≤
            ((2 : ℝ) ^ N)⁻¹ * G.height :=
      mul_le_mul (hnormcS w) hgen (norm_nonneg _) (by positivity)
    have hfinal : ((2 : ℝ) ^ N)⁻¹ * G.height ≤ 1 := by
      have hdiv : G.height / (2 : ℝ) ^ N ≤ 1 := (div_le_one (by positivity)).2 hHpow
      calc
        ((2 : ℝ) ^ N)⁻¹ * G.height = G.height / (2 : ℝ) ^ N := by
          rw [div_eq_mul_inv]
          ring
        _ ≤ 1 := hdiv
    exact le_trans hmul hfinal
  exact ⟨c, hc0, hscale, hnormcOutside⟩

theorem conductorScaledGenerator_integral (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (c : 𝓞 F)
    (hscale : ∀ I (v : S.Sf), A1.absFin v.1
      (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1)
    (I : S.ExtIdeal) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (c : F) * (G.gen I : F) := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro v
  by_cases hv : v ∈ S.Sf
  · let vS : S.Sf := ⟨v, hv⟩
    have hlocal := hscale I vS
    rw [A1.absFin_algebraMap] at hlocal
    have hnorm : ‖FinitePlace.embedding v ((c : F) * (G.gen I : F))‖ ≤ 1 := by
      simpa using hlocal
    have hvalnormR :
        ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (v.valuation F ((c : F) * (G.gen I : F))) : NNReal) : ℝ) ≤ 1 := by
      simpa [FinitePlace.norm_embedding'] using hnorm
    have hvalnorm :
        WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (v.valuation F ((c : F) * (G.gen I : F))) ≤ 1 := by
      exact_mod_cast hvalnormR
    have hvalnorm' :
        WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (v.valuation F ((c : F) * (G.gen I : F))) ≤
        WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) 1 := by
      simpa using hvalnorm
    exact (WithZeroMulInt.toNNReal_strictMono
      (HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le.mp hvalnorm'
  · have hc : v.valuation F (c : F) ≤ 1 := by simpa using v.valuation_le_one c
    have hx : v.valuation F (G.gen I : F) ≤ 1 := (G.gen I).property v hv
    rw [map_mul]
    exact mul_le_one' hc hx

set_option maxHeartbeats 500000 in
theorem conductorIntegralBasis_coords_bound (a : 𝓞 F) {R : ℝ} (hR : 0 ≤ R)
    (hEmb : ∀ w : InfinitePlace F, ‖w.embedding (a : F)‖ ≤ R) :
    ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      |(((RingOfIntegers.basis F).equivFun a i : ℤ) : ℝ)| ≤
        (‖(NumberField.canonicalEmbedding.latticeBasis F).equivFunL.toContinuousLinearMap‖ + 1) * R := by
  classical
  let Bc := NumberField.canonicalEmbedding.latticeBasis F
  let g := Bc.equivFunL.toContinuousLinearMap
  have hcanon : ‖NumberField.canonicalEmbedding F (a : F)‖ ≤ R := by
    apply (NumberField.canonicalEmbedding.norm_le_iff (a : F) R).2
    intro φ
    let w : InfinitePlace F := InfinitePlace.mk φ
    rcases InfinitePlace.embedding_mk_eq φ with heq | heq
    · have hw := hEmb w
      simpa [w, heq] using hw
    · have hw := hEmb w
      rw [heq, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at hw
      simpa [w] using hw
  have hgvec : ‖g (NumberField.canonicalEmbedding F (a : F))‖ ≤
      (‖g‖ + 1) * R := by
    calc
      ‖g (NumberField.canonicalEmbedding F (a : F))‖ ≤
          ‖g‖ * ‖NumberField.canonicalEmbedding F (a : F)‖ := g.le_opNorm _
      _ ≤ (‖g‖ + 1) * R := by
        have hmul := mul_le_mul_of_nonneg_left hcanon (norm_nonneg g)
        nlinarith [hmul, mul_nonneg (norm_nonneg g) hR]
  intro i
  have hcoord :
      g (NumberField.canonicalEmbedding F (a : F)) i =
        (((RingOfIntegers.basis F).equivFun a i : ℤ) : ℂ) := by
    change Bc.repr (NumberField.canonicalEmbedding F (a : F)) i = _
    rw [NumberField.canonicalEmbedding.integralBasis_repr_apply]
    rw [NumberField.integralBasis_repr_apply]
    simp
  have hpi : ‖g (NumberField.canonicalEmbedding F (a : F)) i‖ ≤
      (‖g‖ + 1) * R := by
    let y : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ :=
      g (NumberField.canonicalEmbedding F (a : F))
    have hvec : ‖y‖ ≤ (‖g‖ + 1) * R := by simpa [y] using hgvec
    have hcoordnorm : ‖y i‖ ≤ ‖y‖ := by
      rw [Pi.norm_def]
      exact_mod_cast (Finset.le_sup (f := fun j : Module.Free.ChooseBasisIndex ℤ (𝓞 F) =>
        ‖y j‖₊) (Finset.mem_univ i))
    exact (hcoordnorm.trans hvec)
  rw [hcoord] at hpi
  simpa [Complex.norm_intCast, Int.cast_abs] using hpi

theorem conductorGenerators_dyad_coordinate_bound (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (c : 𝓞 F)
    (hscale : ∀ I (v : S.Sf), A1.absFin v.1
      (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T → ∀ I ∈ conductorExteriorDyad S T,
        ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (c : F) * (G.gen I : F) ∧
          ∀ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
            |(((RingOfIntegers.basis F).equivFun a i : ℤ) : ℝ)| ≤
              C * Real.rpow (2 * T) (1 / (Module.finrank ℚ F : ℝ)) := by
  classical
  let M := 1 + ∑ w : InfinitePlace F,
    ‖w.embedding (c : F)‖
  let B := ‖(NumberField.canonicalEmbedding.latticeBasis F).equivFunL.toContinuousLinearMap‖ + 1
  let C := B * (M * G.height)
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hC : 0 < C := by dsimp [C]; exact mul_pos hB (mul_pos hM G.height_pos)
  refine ⟨C, hC, ?_⟩
  intro T hT I hI
  obtain ⟨a, ha⟩ := conductorScaledGenerator_integral S G c hscale I
  have hIcut : I ∈ conductorExteriorCutoff S (2 * T) :=
    (Finset.mem_filter.mp hI).1
  have hInorm : idealNorm I.1 ≤ 2 * T := by
    change (Ideal.absNorm I.1 : ℝ) ≤ 2 * T
    exact conductorExteriorCutoff_absNorm_le S (by positivity) hIcut
  have hRpos : 0 < M * (G.height * Real.rpow (2 * T)
      (1 / (Module.finrank ℚ F : ℝ))) := by
    have hTpos : 0 < 2 * T := by linarith
    exact mul_pos hM (mul_pos G.height_pos (Real.rpow_pos_of_pos hTpos _))
  have hEmb : ∀ w : InfinitePlace F,
      ‖w.embedding (a : F)‖ ≤ M * (G.height *
        Real.rpow (2 * T) (1 / (Module.finrank ℚ F : ℝ))) := by
    intro w
    have hcEmb : ‖w.embedding (c : F)‖ ≤ M := by
      dsimp [M]
      let f : InfinitePlace F → ℝ := fun w' => ‖w'.embedding (c : F)‖
      have hsingle : f w ≤ ∑ w' : InfinitePlace F, f w' := by
        change f w ≤ ∑ w' ∈ (Finset.univ : Finset (InfinitePlace F)), f w'
        exact Finset.single_le_sum (s := Finset.univ) (f := f)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      linarith
    have hgen := G.infinite_bound I w
    have hmul : ‖w.embedding (c : F)‖ * ‖w.embedding (G.gen I : F)‖ ≤
        M * (G.height * Real.rpow (idealNorm I.1)
          (1 / (Module.finrank ℚ F : ℝ))) := by
      calc
        ‖w.embedding (c : F)‖ * ‖w.embedding (G.gen I : F)‖ ≤
            M * ‖w.embedding (G.gen I : F)‖ :=
          mul_le_mul_of_nonneg_right hcEmb (norm_nonneg _)
        _ ≤ M * (G.height * Real.rpow (idealNorm I.1)
            (1 / (Module.finrank ℚ F : ℝ))) :=
          mul_le_mul_of_nonneg_left hgen (by positivity)
    have hpow : Real.rpow (idealNorm I.1)
        (1 / (Module.finrank ℚ F : ℝ)) ≤
        Real.rpow (2 * T) (1 / (Module.finrank ℚ F : ℝ)) := by
      have hI0 : 0 ≤ idealNorm I.1 := by
        change (0 : ℝ) ≤ (Ideal.absNorm I.1 : ℝ)
        positivity
      have hα : 0 ≤ 1 / (Module.finrank ℚ F : ℝ) := by positivity
      exact Real.rpow_le_rpow hI0 hInorm hα
    have haVal : (a : F) = (c : F) * (G.gen I : F) := ha
    calc
      ‖w.embedding (a : F)‖ =
          ‖w.embedding (c : F)‖ * ‖w.embedding (G.gen I : F)‖ := by
        rw [haVal, map_mul, norm_mul]
      _ ≤ M * (G.height * Real.rpow (idealNorm I.1)
            (1 / (Module.finrank ℚ F : ℝ))) := hmul
      _ ≤ M * (G.height * Real.rpow (2 * T)
            (1 / (Module.finrank ℚ F : ℝ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (le_of_lt G.height_pos)) (le_of_lt hM)
  have hcoords := conductorIntegralBasis_coords_bound a (by positivity) hEmb
  refine ⟨a, ha, fun i => ?_⟩
  calc
    |(((RingOfIntegers.basis F).equivFun a i : ℤ) : ℝ)| ≤
        B * (M * (G.height * Real.rpow (2 * T)
          (1 / (Module.finrank ℚ F : ℝ)))) := hcoords i
    _ = C * Real.rpow (2 * T) (1 / (Module.finrank ℚ F : ℝ)) := by
      dsimp [C, B]
      ring

theorem conductorIntegralPhases_angle_separation (S : A1.SData F CE condη)
    (Ψ : ConductorAdditiveCharacters S) {q q' : S.ExtIdeal}
    (d : (ConductorResidueRing q)ˣ) (d' : (ConductorResidueRing q')ˣ)
    (hneq : conductorIntegralAdditivePhaseChar S Ψ q d ≠
      conductorIntegralAdditivePhaseChar S Ψ q' d')
    {V : ℝ} (hV : 2 ≤ V)
    (hq : (Ideal.absNorm q.1 : ℝ) ≤ V)
    (hq' : (Ideal.absNorm q'.1 : ℝ) ≤ V) :
    ∃ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      1 / (4 * (Module.finrank ℚ F : ℝ) *
        (conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ))) ≤
        |conductorAdditiveCharacterFrequencyVector
          (conductorIntegralDifferenceChar S Ψ q q' d d') i| := by
  classical
  let ψ := conductorIntegralDifferenceChar S Ψ q q' d d'
  let K := conductorAdditiveAnnihilator ψ
  have hJne : q.1 ⊓ q'.1 ≠ ⊥ := by
    have hprod : q.1 * q'.1 ≠ ⊥ := by
      intro h
      rcases Ideal.mul_eq_bot.mp h with hqbot | hq'bot
      · exact q.2.1 hqbot
      · exact q'.2.1 hq'bot
    have hprod_le : q.1 * q'.1 ≤ q.1 ⊓ q'.1 := Ideal.mul_le_inf
    intro hJ
    exact hprod (bot_unique (hJ ▸ hprod_le))
  have hJK : q.1 ⊓ q'.1 ≤ K := by
    change q.1 ⊓ q'.1 ≤ conductorAdditiveAnnihilator ψ
    exact conductorIntegralDifference_annihilator_le S Ψ d d'
  have hKne : K ≠ ⊥ := by
    intro hK
    exact hJne (bot_unique (hK ▸ hJK))
  have hKnorm : (Ideal.absNorm K : ℝ) ≤ V ^ 2 := by
    have hnormN : Ideal.absNorm K ≤ Ideal.absNorm q.1 * Ideal.absNorm q'.1 := by
      exact conductorIntegralDifference_annihilator_norm_le S Ψ d d'
    have hnormR : (Ideal.absNorm K : ℝ) ≤
        (Ideal.absNorm q.1 : ℝ) * (Ideal.absNorm q'.1 : ℝ) := by
      exact_mod_cast hnormN
    calc
      (Ideal.absNorm K : ℝ) ≤
          (Ideal.absNorm q.1 : ℝ) * (Ideal.absNorm q'.1 : ℝ) := hnormR
      _ ≤ V * V := mul_le_mul hq hq' (by positivity) (by positivity)
      _ = V ^ 2 := by ring
  have hψ : ψ ≠ 1 := by
    intro heq
    have heq' :
        conductorIntegralAdditivePhaseChar S Ψ q d *
          (conductorIntegralAdditivePhaseChar S Ψ q' d')⁻¹ = 1 := by
      simpa [ψ, conductorIntegralDifferenceChar] using heq
    exact hneq (mul_inv_eq_one.mp heq')
  have hunit : ∀ x : 𝓞 F, ‖ψ x‖ = 1 := by
    intro x
    exact conductorIntegralDifferenceChar_norm S Ψ q q' d d' x
  exact conductorAdditiveChar_angle_separation ψ hunit hψ K hKne
    (by rfl) hV hKnorm

/-- The finite index set of residue additive phases up to norm `V`. -/
abbrev ConductorAdditiveIndex (S : A1.SData F CE condη) (V : ℝ) :=
  {p : Σ q : S.ExtIdeal, (ConductorResidueRing q)ˣ //
    p ∈ (conductorExteriorCutoff S V).sigma (fun _ => Finset.univ)}

/-- The character of `S.R` attached to one exterior modulus and one residue unit. -/
def conductorAdditiveIndexPhase (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S) (V : ℝ)
    (i : ConductorAdditiveIndex S V) : AddChar S.R ℂ :=
  conductorAdditivePhaseChar S ρ Ψ i.1.1 i.1.2

/-- The set of distinct additive phases with exterior conductor norm at most `V`. -/
noncomputable def conductorAdditiveFrequencySet (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S) (V : ℝ) :
    Finset (AddChar S.R ℂ) := by
  classical
  exact Finset.univ.image (conductorAdditiveIndexPhase S ρ Ψ V)

theorem conductorAdditiveIndexPhase_injective (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S) (V : ℝ) :
    Function.Injective (conductorAdditiveIndexPhase S ρ Ψ V) := by
  classical
  intro i j h
  apply Subtype.ext
  have hchar : conductorAdditivePhaseChar S ρ Ψ i.1.1 i.1.2 =
      conductorAdditivePhaseChar S ρ Ψ j.1.1 j.1.2 := by
    simpa [conductorAdditiveIndexPhase] using h
  obtain ⟨hq, hd⟩ := conductorAdditivePhaseChar_injective S ρ Ψ hchar
  exact Sigma.ext hq hd

theorem conductorAdditiveIndex_angle_separation (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S) {V : ℝ}
    (hV : 2 ≤ V) (i j : ConductorAdditiveIndex S V)
    (hij : conductorAdditiveIndexPhase S ρ Ψ V i ≠
      conductorAdditiveIndexPhase S ρ Ψ V j) :
    ∃ k : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
      1 / (4 * (Module.finrank ℚ F : ℝ) *
        (conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ))) ≤
        |conductorAdditiveCharacterFrequencyVector
          (conductorIntegralDifferenceChar S Ψ i.1.1 j.1.1 i.1.2 j.1.2) k| := by
  have hqmem : i.1.1 ∈ conductorExteriorCutoff S V :=
    (Finset.mem_sigma.mp i.2).1
  have hq'mem : j.1.1 ∈ conductorExteriorCutoff S V :=
    (Finset.mem_sigma.mp j.2).1
  have hneq : conductorIntegralAdditivePhaseChar S Ψ i.1.1 i.1.2 ≠
      conductorIntegralAdditivePhaseChar S Ψ j.1.1 j.1.2 := by
    intro h
    obtain ⟨hq, hd⟩ := conductorIntegralAdditivePhaseChar_injective S Ψ h
    have hdata : i.1 = j.1 := Sigma.ext hq hd
    exact hij (congrArg (conductorAdditiveIndexPhase S ρ Ψ V) (Subtype.ext hdata))
  exact conductorIntegralPhases_angle_separation S Ψ i.1.2 j.1.2 hneq hV
    (conductorExteriorCutoff_absNorm_le S (by linarith) hqmem)
    (conductorExteriorCutoff_absNorm_le S (by linarith) hq'mem)

theorem conductorAdditive_reindex (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (T V : ℝ) (b : S.ExtIdeal → ℂ) :
    (∑ q ∈ conductorExteriorCutoff S V,
      ∑ d : (ConductorResidueRing q)ˣ,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
      (∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
        ‖∑ I ∈ conductorExteriorDyad S T, b I *
          χ (G.gen I)‖ ^ 2) := by
  classical
  let Q := conductorExteriorCutoff S V
  let f : (Σ q : S.ExtIdeal, (ConductorResidueRing q)ˣ) → ℝ := fun i =>
    ‖∑ I ∈ conductorExteriorDyad S T,
      b I * conductorAdditivePhaseChar S ρ Ψ i.1 i.2 (G.gen I)‖ ^ 2
  let hI : ConductorAdditiveIndex S V → AddChar S.R ℂ := fun i =>
    conductorAdditivePhaseChar S ρ Ψ i.1.1 i.1.2
  have hinj : Function.Injective hI := conductorAdditiveIndexPhase_injective S ρ Ψ V
  let QD := Q.sigma (fun q =>
    (Finset.univ : Finset (ConductorResidueRing q)ˣ))
  calc
    (∑ q ∈ Q, ∑ d : (ConductorResidueRing q)ˣ,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        ∑ i : ConductorAdditiveIndex S V, f i := by
      change (∑ q ∈ Q, ∑ d : (ConductorResidueRing q)ˣ, f ⟨q, d⟩) =
        ∑ i : ConductorAdditiveIndex S V, f i.1
      rw [← Finset.sum_sigma]
      simpa [ConductorAdditiveIndex, QD] using
        (Finset.sum_attach QD f).symm
    _ = ∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * χ (G.gen I)‖ ^ 2 := by
      let g : AddChar S.R ℂ → ℝ := fun χ =>
        ‖∑ I ∈ conductorExteriorDyad S T, b I * χ (G.gen I)‖ ^ 2
      calc
        (∑ i : ConductorAdditiveIndex S V, f i.1) =
            ∑ i : ConductorAdditiveIndex S V, g (hI i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rfl
        _ = ∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V, g χ := by
          change (∑ i : ConductorAdditiveIndex S V, g (hI i)) =
            ∑ χ ∈ Finset.univ.image hI, g χ
          symm
          exact Finset.sum_image hinj.injOn

theorem conductorAdditive_reindex_map (S : A1.SData F CE condη)
    (gen : S.ExtIdeal → S.R) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (T V : ℝ) (b : S.ExtIdeal → ℂ) :
    (∑ q ∈ conductorExteriorCutoff S V,
      ∑ d : (ConductorResidueRing q)ˣ,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * Ψ.ψ q (ρ.red q (gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
      (∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
        ‖∑ I ∈ conductorExteriorDyad S T, b I * χ (gen I)‖ ^ 2) := by
  classical
  let Q := conductorExteriorCutoff S V
  let f : (Σ q : S.ExtIdeal, (ConductorResidueRing q)ˣ) → ℝ := fun i =>
    ‖∑ I ∈ conductorExteriorDyad S T,
      b I * conductorAdditivePhaseChar S ρ Ψ i.1 i.2 (gen I)‖ ^ 2
  let hI : ConductorAdditiveIndex S V → AddChar S.R ℂ := fun i =>
    conductorAdditivePhaseChar S ρ Ψ i.1.1 i.1.2
  have hinj : Function.Injective hI := conductorAdditiveIndexPhase_injective S ρ Ψ V
  let QD := Q.sigma (fun q =>
    (Finset.univ : Finset (ConductorResidueRing q)ˣ))
  calc
    (∑ q ∈ Q,
      ∑ d : (ConductorResidueRing q)ˣ,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * Ψ.ψ q (ρ.red q (gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        ∑ i : ConductorAdditiveIndex S V, f i := by
      change (∑ q ∈ Q, ∑ d : (ConductorResidueRing q)ˣ, f ⟨q, d⟩) =
        ∑ i : ConductorAdditiveIndex S V, f i.1
      rw [← Finset.sum_sigma]
      simpa [ConductorAdditiveIndex, QD] using
        (Finset.sum_attach QD f).symm
    _ = ∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * χ (gen I)‖ ^ 2 := by
      let g : AddChar S.R ℂ → ℝ := fun χ =>
        ‖∑ I ∈ conductorExteriorDyad S T, b I * χ (gen I)‖ ^ 2
      calc
        (∑ i : ConductorAdditiveIndex S V, f i.1) =
            ∑ i : ConductorAdditiveIndex S V, g (hI i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rfl
        _ = ∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V, g χ := by
          change (∑ i : ConductorAdditiveIndex S V, g (hI i)) =
            ∑ χ ∈ Finset.univ.image hI, g χ
          symm
          exact Finset.sum_image hinj.injOn

theorem conductorAdditive_scaled_reindex (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (T V : ℝ) (b : S.ExtIdeal → ℂ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧
      (∀ I (v : S.Sf), A1.absFin v.1
        (algebraMap F (v.1.adicCompletion F) ((c : F) * (G.gen I : F))) ≤ 1) ∧
      (∀ w : A1.FinPlace F, w ∉ S.Sf →
        ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1) ∧
      (∑ q ∈ conductorExteriorCutoff S V,
        ∑ d : (ConductorResidueRing q)ˣ,
          ‖∑ I ∈ conductorExteriorDyad S T,
            b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        (∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
          ‖∑ I ∈ conductorExteriorDyad S T, b I *
            χ ((algebraMap (𝓞 F) S.R c) * G.gen I)‖ ^ 2) := by
  obtain ⟨c, hc0, hscale, houtside⟩ := exists_conductorGenerator_S_unit_scale S G
  have hunit (q : S.ExtIdeal) : IsUnit (Ideal.Quotient.mk q.1 c) :=
    conductorSUnit_quotient_isUnit S q c houtside
  have hrescale :
      (∑ q ∈ conductorExteriorCutoff S V,
        ∑ d : (ConductorResidueRing q)ˣ,
          ‖∑ I ∈ conductorExteriorDyad S T,
            b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        (∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              b I * Ψ.ψ q
                (ρ.red q ((algebraMap (𝓞 F) S.R c) * G.gen I) *
                  (d : ConductorResidueRing q))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact conductorAdditiveSum_scale S G ρ Ψ q c (hunit q)
      (conductorExteriorDyad S T) b
  refine ⟨c, hc0, hscale, houtside, hrescale.trans ?_⟩
  exact conductorAdditive_reindex_map S
    (fun I => (algebraMap (𝓞 F) S.R c) * G.gen I) ρ Ψ T V b

theorem conductorAdditive_reindex_with_scale (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (T V : ℝ)
    (b : S.ExtIdeal → ℂ) (c : 𝓞 F)
    (houtside : ∀ w : A1.FinPlace F, w ∉ S.Sf →
      ‖FinitePlace.embedding w (algebraMap (𝓞 F) F c)‖ = 1) :
    (∑ q ∈ conductorExteriorCutoff S V,
      ∑ d : (ConductorResidueRing q)ˣ,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
      (∑ χ ∈ conductorAdditiveFrequencySet S ρ Ψ V,
        ‖∑ I ∈ conductorExteriorDyad S T, b I *
          χ ((algebraMap (𝓞 F) S.R c) * G.gen I)‖ ^ 2) := by
  have hunit (q : S.ExtIdeal) : IsUnit (Ideal.Quotient.mk q.1 c) :=
    conductorSUnit_quotient_isUnit S q c houtside
  have hrescale :
      (∑ q ∈ conductorExteriorCutoff S V,
        ∑ d : (ConductorResidueRing q)ˣ,
          ‖∑ I ∈ conductorExteriorDyad S T,
            b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        (∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              b I * Ψ.ψ q
                (ρ.red q ((algebraMap (𝓞 F) S.R c) * G.gen I) *
                  (d : ConductorResidueRing q))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact conductorAdditiveSum_scale S G ρ Ψ q c (hunit q)
      (conductorExteriorDyad S T) b
  exact hrescale.trans (conductorAdditive_reindex_map S
    (fun I => (algebraMap (𝓞 F) S.R c) * G.gen I) ρ Ψ T V b)

/-- An exterior ideal's balanced generator determines the ideal. -/
theorem conductorGenerators_gen_injective (S : A1.SData F CE condη)
    (G : ConductorGenerators S) : Function.Injective G.gen := by
  classical
  intro I J hgen
  have hgenF : (G.gen I : F) = (G.gen J : F) := congrArg Subtype.val hgen
  have hcount_zero (K : S.ExtIdeal) (v : A1.FinPlace F) (hv : v ∈ S.Sf) :
      FractionalIdeal.count F v (K.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
    have hKne : K.1 ≠ 0 := by simpa [Ideal.zero_eq_bot] using K.2.1
    have hnot : ¬v.asIdeal ∣ K.1 := by
      intro hdiv
      exact K.2.2 v hv (Ideal.dvd_iff_le.mp hdiv)
    rw [FractionalIdeal.count_coe (K := F) (v := v) hKne]
    have hmult :
        (Associates.mk v.asIdeal).count (Associates.mk K.1).factors = 0 := by
      by_contra hne
      exact hnot <| (Associates.count_ne_zero_iff_dvd hKne v.irreducible).mp hne
    exact_mod_cast hmult
  have hcounts (v : A1.FinPlace F) :
      FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    by_cases hv : v ∈ S.Sf
    · rw [hcount_zero I v hv, hcount_zero J v hv]
    · calc
        FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
            FractionalIdeal.count F v
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (G.gen I : F)) :=
          ((G.generates I).2.2 v hv).symm
        _ = FractionalIdeal.count F v
              (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (G.gen J : F)) := by
          rw [hgenF]
        _ = FractionalIdeal.count F v (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          (G.generates J).2.2 v hv
  have hIne : I.1 ≠ 0 := by simpa [Ideal.zero_eq_bot] using I.2.1
  have hJne : J.1 ≠ 0 := by simpa [Ideal.zero_eq_bot] using J.2.1
  have hIfr : (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hIne
  have hJfr : (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJne
  have hfrac : (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    calc
      (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          ∏ᶠ v : A1.FinPlace F,
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
              FractionalIdeal.count F v I.1 :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization'
          (R := 𝓞 F) (K := F) hIfr).symm
      _ = ∏ᶠ v : A1.FinPlace F,
            (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^
              FractionalIdeal.count F v J.1 := by
        apply finprod_congr
        intro v
        rw [hcounts v]
      _ = (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        FractionalIdeal.finprod_heightOneSpectrum_factorization'
          (R := 𝓞 F) (K := F) hJfr
  have hideal : I.1 = J.1 := FractionalIdeal.coeIdeal_injective hfrac
  exact Subtype.ext hideal

theorem conductorGenerators_scaled_gen_injective (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (c : 𝓞 F) (hc : c ≠ 0) :
    Function.Injective (fun I : S.ExtIdeal =>
      (algebraMap (𝓞 F) S.R c) * G.gen I) := by
  intro I J h
  have hcF : (c : F) ≠ 0 := by
    intro hzero
    exact hc ((IsFractionRing.injective (𝓞 F) F)
      (by simpa using hzero))
  have hF : (c : F) * (G.gen I : F) = (c : F) * (G.gen J : F) :=
    congrArg (fun x : S.R => (x : F)) h
  have hgen : G.gen I = G.gen J := by
    apply Subtype.ext
    apply mul_left_cancel₀ hcF
    simpa using hF
  exact conductorGenerators_gen_injective S G hgen

end ArtinPrimitiveRoots.Proofs.a2_cond_b
