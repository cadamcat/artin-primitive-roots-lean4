import Mathlib
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import TauCeti.RingTheory.DedekindDomain.Factorization

/-! Adapted from TauCeti RingTheory/DedekindDomain/FiniteAdeleRing/ClassGroup.lean.
Copyright (c) 2026 The Tau Ceti contributors. Released under Apache-2.0. -/

set_option autoImplicit false

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing

open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing

namespace ArtinPrimitiveRoots.Dictionary

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The local orders of a finite idele -/

/-- Every component of a finite idele is nonzero. -/
theorem coe_units_apply_ne_zero (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    (x : 𝔸ᶠ[R, K]) v ≠ 0 :=
  (isUnit_iff.mp x.isUnit).1 v

/-- The valuation of a component of a finite idele is nonzero. -/
theorem valued_coe_units_apply_ne_zero (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    Valued.v ((x : 𝔸ᶠ[R, K]) v) ≠ 0 := by
  rw [ne_eq, Valuation.zero_iff]
  exact coe_units_apply_ne_zero x v

/-- A finite idele is a unit of the local integers at all but finitely many places. -/
theorem eventually_valued_coe_units_apply_eq_one (x : 𝔸ᶠ[R, K]ˣ) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, Valued.v ((x : 𝔸ᶠ[R, K]) v) = 1 :=
  (isUnit_iff.mp x.isUnit).2

/-- The valuations of a finite idele and of its inverse at a place are inverse to each other. -/
@[simp] theorem valued_coe_units_inv_apply (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    Valued.v (((x⁻¹ : 𝔸ᶠ[R, K]ˣ) : 𝔸ᶠ[R, K]) v) = (Valued.v ((x : 𝔸ᶠ[R, K]) v))⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by
    rw [← map_mul, ← mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply,
      map_one])).symm

/-- The `v`-adic order of a finite idele `x`, that is, the exponent of `v` in the fractional
ideal that `x` defines.  The sign is chosen so that a uniformizer at `v` has order `1`. -/
noncomputable def adicOrd (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) : ℤ :=
  -WithZero.log (Valued.v ((x : 𝔸ᶠ[R, K]) v))

/-- The defining formula for the `v`-adic order of a finite idele. -/
theorem adicOrd_def (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    adicOrd x v = -WithZero.log (Valued.v ((x : 𝔸ᶠ[R, K]) v)) := by
  simp only [adicOrd]

/-- The `v`-adic order vanishes exactly at the places where the idele is a local unit. -/
@[simp] theorem adicOrd_eq_zero_iff {x : 𝔸ᶠ[R, K]ˣ} {v : HeightOneSpectrum R} :
    adicOrd x v = 0 ↔ Valued.v ((x : 𝔸ᶠ[R, K]) v) = 1 := by
  rw [adicOrd_def, neg_eq_zero]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, WithZero.log_one]⟩
  have hexp := WithZero.exp_log (valued_coe_units_apply_ne_zero x v)
  rwa [h, WithZero.exp_zero, eq_comm] at hexp

/-- The unit idele has order `0` everywhere. -/
@[simp] theorem adicOrd_one (v : HeightOneSpectrum R) : adicOrd (1 : 𝔸ᶠ[R, K]ˣ) v = 0 := by
  rw [adicOrd_eq_zero_iff, Units.val_one, one_apply, map_one]

/-- The `v`-adic order is additive in the finite idele. -/
@[simp] theorem adicOrd_mul (x y : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    adicOrd (x * y) v = adicOrd x v + adicOrd y v := by
  simp only [adicOrd_def]
  rw [Units.val_mul, mul_apply, map_mul,
    WithZero.log_mul (valued_coe_units_apply_ne_zero x v) (valued_coe_units_apply_ne_zero y v),
    neg_add]

/-- The order of the inverse of a finite idele is the negative of its order. -/
@[simp] theorem adicOrd_inv (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    adicOrd x⁻¹ v = -adicOrd x v := by
  simp only [adicOrd_def, valued_coe_units_inv_apply, WithZero.log_inv]

/-- A finite idele has order `0` at all but finitely many places. -/
theorem eventually_adicOrd_eq_zero (x : 𝔸ᶠ[R, K]ˣ) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, adicOrd x v = 0 :=
  (eventually_valued_coe_units_apply_eq_one x).mono fun _ h ↦ adicOrd_eq_zero_iff.mpr h

/-- The prime powers cut out by the orders of a finite idele have finite multiplicative support,
so their product over all height one primes is defined. -/
theorem hasFiniteMulSupport_unitOfPrime_zpow_adicOrd (x : 𝔸ᶠ[R, K]ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum R ↦ v.unitOfPrime K ^ adicOrd x v).Finite :=
  (Filter.eventually_cofinite.mp (eventually_adicOrd_eq_zero x)).subset fun _ hv hc ↦
    hv (by simp only [hc, zpow_zero])

/-! ### The fractional ideal of a finite idele -/

/-- The invertible fractional ideal `∏_v v ^ ord_v(x)` attached to a finite idele `x`. -/
noncomputable def toFractionalIdeal : 𝔸ᶠ[R, K]ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := ∏ᶠ v : HeightOneSpectrum R, v.unitOfPrime K ^ adicOrd x v
  map_one' := by simp only [adicOrd_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [adicOrd_mul, zpow_add]
    exact finprod_mul_distrib (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd x)
      (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd y)

/-- The defining prime factorization of the fractional ideal of a finite idele. -/
theorem toFractionalIdeal_apply (x : 𝔸ᶠ[R, K]ˣ) :
    toFractionalIdeal x = ∏ᶠ v : HeightOneSpectrum R, v.unitOfPrime K ^ adicOrd x v := by
  simp only [toFractionalIdeal, MonoidHom.coe_mk, OneHom.coe_mk]

/-- **The characterizing property of `toFractionalIdeal`**: the multiplicity of `v` in the
fractional ideal of a finite idele is its `v`-adic order. -/
@[simp] theorem count_coe_toFractionalIdeal (x : 𝔸ᶠ[R, K]ˣ) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (toFractionalIdeal x : FractionalIdeal R⁰ K) = adicOrd x v := by
  have hmap : ((∏ᶠ w : HeightOneSpectrum R, w.unitOfPrime K ^ adicOrd x w :
        (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      ∏ᶠ w : HeightOneSpectrum R,
        ((w.unitOfPrime K ^ adicOrd x w : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) :=
    MonoidHom.map_finprod (Units.coeHom (FractionalIdeal R⁰ K))
      (hasFiniteMulSupport_unitOfPrime_zpow_adicOrd x)
  rw [toFractionalIdeal_apply, hmap]
  simp only [Units.val_zpow_eq_zpow_val, HeightOneSpectrum.coe_unitOfPrime]
  exact FractionalIdeal.count_finprod K v _ (eventually_adicOrd_eq_zero x)

/-- A finite idele defines the trivial fractional ideal exactly when all its orders vanish. -/
@[simp] theorem toFractionalIdeal_eq_one_iff {x : 𝔸ᶠ[R, K]ˣ} :
    toFractionalIdeal x = 1 ↔ ∀ v : HeightOneSpectrum R, adicOrd x v = 0 := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← count_coe_toFractionalIdeal x v, h, Units.val_one, FractionalIdeal.count_one]
  · rw [toFractionalIdeal_apply]
    simp only [h, zpow_zero, finprod_one]

/-- The fractional ideal of a principal finite idele is the corresponding principal fractional
ideal. -/
@[simp] theorem toFractionalIdeal_unitEmbedding (u : Kˣ) :
    toFractionalIdeal (FiniteAdeleRing.unitEmbedding R K u) = toPrincipalIdeal R K u := by
  have hcount (v : HeightOneSpectrum R) :
      FractionalIdeal.count K v
        (toFractionalIdeal (FiniteAdeleRing.unitEmbedding R K u) : FractionalIdeal R⁰ K) =
          FractionalIdeal.count K v (toPrincipalIdeal R K u : FractionalIdeal R⁰ K) := by
    rw [count_coe_toFractionalIdeal, adicOrd_def,
      FractionalIdeal.count_toPrincipalIdeal_eq_neg_log_valuation K v u,
      FiniteAdeleRing.unitEmbedding_apply, FiniteAdeleRing.algebraMap_apply,
      valuedAdicCompletion_eq_valuation']
  rw [FractionalIdeal.finprod_unitOfPrime_zpow_count
      (toFractionalIdeal (FiniteAdeleRing.unitEmbedding R K u)),
    FractionalIdeal.finprod_unitOfPrime_zpow_count (toPrincipalIdeal R K u)]
  simp only [hcount]

end ArtinPrimitiveRoots.Dictionary
