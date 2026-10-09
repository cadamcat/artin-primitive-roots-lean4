import ArtinPrimitiveRoots.A1.Proofs.A1_LAMBDA.BaseNearOne
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Group.Quotient

/-! The ramified completion character from its open principal-unit kernel. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology WithZero Valued
noncomputable section

attribute [local instance 2000] CyclotomicField.instNumberField

namespace ArtinPrimitiveRoots.Proofs.a1_lambda_sol

open ArtinPrimitiveRoots.A1

theorem valuation_eq_one_of_near_one {K : Type} [Field K]
    (v : Valuation K ℤᵐ⁰) {r : ℤᵐ⁰} (hr : r < 1) (u : Kˣ)
    (hu : v ((u : K) - 1) ≤ r) : v (u : K) = 1 := by
  have h : v ((u : K) - 1) < v 1 := by simpa using hu.trans_lt hr
  simpa using v.map_eq_of_sub_lt h

/-- Principal units defined by a strict subunit valuation bound. -/
def valuativeNearOne {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)
    (r : ℤᵐ⁰) (hr : r < 1) : Subgroup Kˣ where
  carrier := {u | v ((u : K) - 1) ≤ r}
  one_mem' := by simp
  mul_mem' := by
    intro u w hu hw
    change v ((u : K) - 1) ≤ r at hu
    change v ((w : K) - 1) ≤ r at hw
    have hwv := valuation_eq_one_of_near_one v hr w hw
    change v ((u : K) * (w : K) - 1) ≤ r
    have heq : (u : K) * (w : K) - 1 =
        ((u : K) - 1) * (w : K) + ((w : K) - 1) := by ring
    rw [heq]
    refine (v.map_add _ _).trans (max_le ?_ hw)
    simpa only [map_mul, hwv, mul_one] using hu
  inv_mem' := by
    intro u hu
    change v ((u : K) - 1) ≤ r at hu
    have huv := valuation_eq_one_of_near_one v hr u hu
    change v (((u⁻¹ : Kˣ) : K) - 1) ≤ r
    rw [Units.val_inv_eq_inv_val]
    have heq : (u : K)⁻¹ - 1 = (1 - (u : K)) / (u : K) := by
      field_simp [u.ne_zero]
    rw [heq, map_div₀, Valuation.map_sub_swap, huv, div_one]
    exact hu

/-- Nonzero valuation balls are open, hence so is the principal-unit subgroup. -/
theorem valuativeNearOne_isOpen {K : Type} [Field K] [Valued K ℤᵐ⁰]
    (hs : Function.Surjective (Valued.v : Valuation K ℤᵐ⁰))
    (r : ℤᵐ⁰) (hr : r < 1) (hr0 : r ≠ 0) :
    IsOpen (valuativeNearOne (Valued.v : Valuation K ℤᵐ⁰) r hr : Set Kˣ) := by
  obtain ⟨b, hb⟩ := hs r
  have hb0 : (Valued.v : Valuation K ℤᵐ⁰).restrict b ≠ 0 := by
    intro h0
    apply hr0
    exact hb.symm.trans ((Valuation.restrict_eq_zero_iff
      (v := (Valued.v : Valuation K ℤᵐ⁰))).mp h0)
  have hcont : Continuous (fun u : Kˣ => (u : K) - 1) :=
    Units.continuous_val.sub continuous_const
  have hopen := (Valued.isOpen_closedBall (R := K) hb0).preimage hcont
  convert hopen using 1
  ext u
  change Valued.v ((u : K) - 1) ≤ r ↔
    (Valued.v : Valuation K ℤᵐ⁰).restrict ((u : K) - 1) ≤
      (Valued.v : Valuation K ℤᵐ⁰).restrict b
  rw [Valuation.restrict_le_iff, hb]

/-- Density of a field embedding also gives density on its nonzero units. -/
theorem denseRange_units_map_of_denseRange {K L : Type} [Field K] [Field L]
    [TopologicalSpace L] [IsOpenUnits L] (f : K →+* L) (hf : DenseRange f) :
    DenseRange (Units.map f.toMonoidHom) := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hUne
  have hUi : IsOpen (Units.val '' U : Set L) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hU
  obtain ⟨x, u, huU, hux⟩ := hf.exists_mem_open hUi (hUne.image Units.val)
  have hx : x ≠ 0 := by
    intro hx
    apply u.ne_zero
    rw [hux, hx, map_zero]
  refine ⟨u, huU, Units.mk0 x hx, ?_⟩
  apply Units.ext
  exact hux.symm

/-- The second principal-unit subgroup of the ramified completion. -/
def lambdaNearOne : Subgroup (lambdaPlace.adicCompletion E)ˣ :=
  valuativeNearOne Valued.v (WithZero.exp (-2 : ℤ)) (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)

theorem lambdaNearOne_isOpen :
    IsOpen (lambdaNearOne : Set (lambdaPlace.adicCompletion E)ˣ) :=
  valuativeNearOne_isOpen (lambdaPlace.valuedAdicCompletion_surjective E)
    _ _ WithZero.exp_ne_zero

/-- The field-unit map onto the local discrete quotient. -/
def lambdaQuotientMap : Eˣ →* (lambdaPlace.adicCompletion E)ˣ ⧸ lambdaNearOne :=
  (QuotientGroup.mk' lambdaNearOne).comp (toLoc lambdaPlace)

theorem lambdaQuotientMap_surjective : Function.Surjective lambdaQuotientMap := by
  letI : DiscreteTopology ((lambdaPlace.adicCompletion E)ˣ ⧸ lambdaNearOne) :=
    QuotientGroup.discreteTopology lambdaNearOne_isOpen
  apply denseRange_discrete.mp
  exact (QuotientGroup.mk'_surjective lambdaNearOne).denseRange.comp
    (denseRange_units_map_of_denseRange (algebraMap E (lambdaPlace.adicCompletion E))
      (lambdaPlace.denseRange_algebraMap E)) QuotientGroup.continuous_mk

theorem lambdaQuotientMap_ker_le_correction (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) :
    lambdaQuotientMap.ker ≤ (baseFieldCorrection σ a).ker := by
  intro t ht
  have hmem : toLoc lambdaPlace t ∈ lambdaNearOne :=
    (QuotientGroup.eq_one_iff _).mp ht
  change Valued.v (algebraMap E (lambdaPlace.adicCompletion E) (t : E) - 1) ≤
    WithZero.exp (-2 : ℤ) at hmem
  have hsmall : Valued.v (algebraMap E (lambdaPlace.adicCompletion E)
      ((t : E) - 1)) ≤ WithZero.exp (-2 : ℤ) := by
    simpa only [map_sub, map_one] using hmem
  change Valued.v (((t : E) - 1 : E) : lambdaPlace.adicCompletion E) ≤ _ at hsmall
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hsmall
  exact baseFieldCorrection_near_one σ φ hφ a ha t hsmall

/-- The ramified correction extends through the discrete local quotient.
Every quotient class has a field-unit representative, so its values stay unitary. -/
theorem base_local_correction_exists (σ : E →+* ℂ) (φ : Ideal OE →*₀ ℂ)
    (hφ : ∀ I : Ideal OE,
      φ I = integerComplex σ (primary I) / ‖integerComplex σ (primary I)‖)
    (a : ContinuousMonoidHom ℂˣ ℂˣ)
    (ha : ∀ z : ℂˣ, (a z : ℂ) = (z : ℂ) / ‖(z : ℂ)‖) :
    ∃ κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ,
      (∀ u, ‖(κ u : ℂ)‖ = 1) ∧
      (∀ t : Eˣ, κ (toLoc lambdaPlace t) = baseFieldCorrection σ a t) := by
  letI : DiscreteTopology ((lambdaPlace.adicCompletion E)ˣ ⧸ lambdaNearOne) :=
    QuotientGroup.discreteTopology lambdaNearOne_isOpen
  let hs := lambdaQuotientMap_surjective
  let hg := lambdaQuotientMap_ker_le_correction σ φ hφ a ha
  let g := lambdaQuotientMap.liftOfSurjective hs ⟨baseFieldCorrection σ a, hg⟩
  have hgf (t : Eˣ) : g (lambdaQuotientMap t) = baseFieldCorrection σ a t :=
    lambdaQuotientMap.liftOfRightInverse_comp_apply (Function.surjInv hs)
      (Function.rightInverse_surjInv hs) ⟨baseFieldCorrection σ a, hg⟩ t
  have hcontg : Continuous g := continuous_of_discreteTopology
  let κ : ContinuousMonoidHom (lambdaPlace.adicCompletion E)ˣ ℂˣ :=
    ⟨g.comp (QuotientGroup.mk' lambdaNearOne),
      hcontg.comp QuotientGroup.continuous_mk⟩
  refine ⟨κ, ?_, hgf⟩
  intro u
  obtain ⟨t, ht⟩ := hs (QuotientGroup.mk' lambdaNearOne u)
  change ‖(g (QuotientGroup.mk' lambdaNearOne u) : ℂ)‖ = 1
  rw [← ht, hgf]
  exact baseFieldCorrection_unitary σ a ha t

end ArtinPrimitiveRoots.Proofs.a1_lambda_sol
