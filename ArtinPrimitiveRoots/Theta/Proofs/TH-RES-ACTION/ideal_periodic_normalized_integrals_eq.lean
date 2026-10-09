import ArtinPrimitiveRoots.Theta.Eis
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Countable

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- The normalized mean of a continuous function is independent of the
bounded ideal fundamental domain used to integrate it. -/
theorem ideal_periodic_normalized_integrals_eq
    (f : (InfinitePlace F → ℂ) → ℂ) (hf : Continuous f)
    (𝔞 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (Pd Qd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hQd : IsAddFundamentalDomain
      ((𝔟 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Qd volume)
    (hbP : Bornology.IsBounded Pd) (hbQ : Bornology.IsBounded Qd)
    (hμP : (volume Pd).toReal ≠ 0) (hμQ : (volume Qd).toReal ≠ 0)
    (hperP : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x, f (x + infEmbA ξ) = f x)
    (hperQ : ∀ ξ ∈ (𝔟 : Submodule (𝓞 F) F), ∀ x, f (x + infEmbA ξ) = f x) :
    ((volume Pd).toReal : ℂ)⁻¹ * (∫ x in Pd, f x) =
      ((volume Qd).toReal : ℂ)⁻¹ * (∫ x in Qd, f x) := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  -- Translating a fundamental domain does not change a periodic integral.
  have hshift (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (Rd : Set (InfinitePlace F → ℂ))
      (hRd : IsAddFundamentalDomain
        ((𝔠 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Rd volume)
      (hper : ∀ ξ ∈ (𝔠 : Submodule (𝓞 F) F), ∀ x, f (x + infEmbA ξ) = f x)
      (y : InfinitePlace F → ℂ) :
      (∫ x in Rd, f (x + y)) = ∫ x in Rd, f x := by
    let L := (𝔠 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
    have hcount : (L : Set (InfinitePlace F → ℂ)).Countable := by
      change (↑((𝔠 : Submodule (𝓞 F) F).toAddSubgroup.map
        infEmbA.toAddMonoidHom) : Set (InfinitePlace F → ℂ)).Countable
      rw [AddSubgroup.coe_map]
      exact (Set.to_countable _).image _
    let : Countable L := hcount.to_subtype
    have hperiod : ∀ (m : L) x, f (m +ᵥ x) = f x := by
      intro m x
      obtain ⟨ξ, hξ, hξm⟩ := AddSubgroup.mem_map.mp m.property
      change f ((m : InfinitePlace F → ℂ) + x) = f x
      rw [← hξm, add_comm]
      exact hper ξ hξ x
    have htr := measurePreserving_add_right
      (volume : Measure (InfinitePlace F → ℂ)) y
    have hpre : IsAddFundamentalDomain L ((fun x => x + y) ⁻¹' Rd) volume :=
      hRd.preimage_of_equiv htr.quasiMeasurePreserving
        (e := id) Function.bijective_id (fun m x => by
          change ((m : InfinitePlace F → ℂ) + x) + y =
            (m : InfinitePlace F → ℂ) + (x + y)
          exact add_assoc _ _ _)
    have hperiod_shift : ∀ (m : L) x, f ((m +ᵥ x) + y) = f (x + y) := by
      intro m x
      change f (((m : InfinitePlace F → ℂ) + x) + y) = _
      rw [add_assoc]
      exact hperiod m (x + y)
    calc
      (∫ x in Rd, f (x + y)) =
          ∫ x in (fun x => x + y) ⁻¹' Rd, f (x + y) :=
        hRd.setIntegral_eq hpre hperiod_shift
      _ = ∫ x in Rd, f x :=
        htr.setIntegral_preimage_emb (MeasurableEquiv.addRight y).measurableEmbedding f Rd
  -- Compact closures give integrability on the product of the two domains.
  have hcont : Continuous (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) =>
      f (p.1 + p.2)) := hf.comp (continuous_fst.add continuous_snd)
  have hint : Integrable (Function.uncurry (fun x y => f (x + y)))
      ((volume.restrict Pd).prod (volume.restrict Qd)) := by
    rw [Measure.prod_restrict]
    exact (hcont.continuousOn.integrableOn_compact
      (hbP.isCompact_closure.prod hbQ.isCompact_closure)).mono_set
        (Set.prod_mono subset_closure subset_closure)
  have hinnerP : ∀ y, (∫ x in Pd, f (x + y)) = ∫ x in Pd, f x :=
    hshift 𝔞 Pd hPd hperP
  have hinnerQ : ∀ x, (∫ y in Qd, f (x + y)) = ∫ y in Qd, f y := by
    intro x
    simpa only [add_comm] using hshift 𝔟 Qd hQd hperQ x
  have hswap := integral_integral_swap hint
  simp_rw [hinnerQ, hinnerP] at hswap
  rw [setIntegral_const, setIntegral_const, Complex.real_smul, Complex.real_smul] at hswap
  have hp : ((volume Pd).toReal : ℂ) ≠ 0 := by exact_mod_cast hμP
  have hq : ((volume Qd).toReal : ℂ) ≠ 0 := by exact_mod_cast hμQ
  apply (mul_left_cancel₀ (mul_ne_zero hp hq))
  calc
    (((volume Pd).toReal : ℂ) * ((volume Qd).toReal : ℂ)) *
        (((volume Pd).toReal : ℂ)⁻¹ * (∫ x in Pd, f x)) =
          ((volume Qd).toReal : ℂ) * (∫ x in Pd, f x) := by
      field_simp
    _ = ((volume Pd).toReal : ℂ) * (∫ x in Qd, f x) := hswap.symm
    _ = (((volume Pd).toReal : ℂ) * ((volume Qd).toReal : ℂ)) *
        (((volume Qd).toReal : ℂ)⁻¹ * (∫ x in Qd, f x)) := by
      field_simp

end ArtinPrimitiveRoots.A1.Theta
