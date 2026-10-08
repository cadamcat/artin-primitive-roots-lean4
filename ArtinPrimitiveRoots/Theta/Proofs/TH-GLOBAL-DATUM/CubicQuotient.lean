import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The local multiplicative cube quotient. -/
abbrev LocalCubeQuotient (v : FinPlace F) :=
  (v.adicCompletion F)ˣ ⧸ (powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range

/-- A nonzero finite torus model controls the cube quotient and its congruence kernel. -/
structure TorusCubeControl {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (T : TorusRep D H v) : Prop where
  finite : Finite (LocalCubeQuotient v)
  scalar_cube : ∀ x : (v.adicCompletion F)ˣ,
    (∃ c : ℂ, T.σa x = c • LinearMap.id) → ∃ t : (v.adicCompletion F)ˣ, x = t ^ 3

/-- Finite image and nondegeneracy replace an independent Hensel proof of cube-index finiteness. -/
theorem torusRep_cube_control {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (T : TorusRep D H v) [Nontrivial T.V] : TorusCubeControl T := by
  classical
  let K := (v.adicCompletion F)ˣ
  have hid : (LinearMap.id : T.V →ₗ[ℂ] T.V) ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := exists_ne (0 : T.V)
    exact hu (by simpa using DFunLike.congr_fun h u)
  have hσ (x : K) : T.σa x ≠ 0 := by
    intro hx
    have h := T.σa_mul x x⁻¹
    rw [hx, LinearMap.zero_comp, mul_inv_cancel, T.σa_one] at h
    exact (smul_ne_zero (muThree D (H.hilb v x x⁻¹) : ℂˣ).ne_zero hid) h.symm
  have scalar_cube (x : K) (hx : ∃ c : ℂ, T.σa x = c • LinearMap.id) :
      ∃ t : K, x = t ^ 3 := by
    obtain ⟨c, hc⟩ := hx
    apply torusPairing_nondeg (D := D) (H := H) (v := v) x
    intro y
    have hcomm : (T.σa x).comp (T.σa y) = (T.σa y).comp (T.σa x) := by
      rw [hc]
      simp only [LinearMap.smul_comp, LinearMap.id_comp, LinearMap.comp_smul,
        LinearMap.comp_id]
    have h := (T.σa_mul x y).symm.trans (hcomm.trans (T.σa_mul y x))
    rw [mul_comm y x] at h
    have hcoeff := smul_left_injective ℂ (hσ (x * y)) h
    have hroot : muThree D (H.hilb v x y) = muThree D (H.hilb v y x) :=
      rootsOfUnity.coe_injective hcoeff
    rw [torusPairing, hroot, mul_inv_cancel]
  have ratio_cube (x y : K) (hxy : T.σa x = T.σa y) :
      ∃ t : K, x * y⁻¹ = t ^ 3 := by
    apply scalar_cube
    let α : ℂ := ((muThree D (H.hilb v y y⁻¹) : ℂˣ) : ℂ)
    let β : ℂ := ((muThree D (H.hilb v x y⁻¹) : ℂˣ) : ℂ)
    have hβ : β ≠ 0 := (muThree D (H.hilb v x y⁻¹) : ℂˣ).ne_zero
    have h : α • (LinearMap.id : T.V →ₗ[ℂ] T.V) = β • T.σa (x * y⁻¹) := by
      calc
        α • (LinearMap.id : T.V →ₗ[ℂ] T.V) = (T.σa y).comp (T.σa y⁻¹) := by
          simpa only [mul_inv_cancel, T.σa_one] using (T.σa_mul y y⁻¹).symm
        _ = (T.σa x).comp (T.σa y⁻¹) := by rw [hxy]
        _ = β • T.σa (x * y⁻¹) := T.σa_mul x y⁻¹
    have h' := congrArg (fun f : T.V →ₗ[ℂ] T.V => β⁻¹ • f) h
    simp only [smul_smul, inv_mul_cancel₀ hβ, one_smul] at h'
    exact ⟨β⁻¹ * α, h'.symm⟩
  let R := Set.range T.σa
  letI : Fintype R := T.σa_finite.fintype
  let qmap : R → LocalCubeQuotient v := fun f => QuotientGroup.mk (Classical.choose f.property)
  have hqmap : Function.Surjective qmap := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    let r : R := ⟨T.σa x, ⟨x, rfl⟩⟩
    refine ⟨r, ?_⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ∃ t : K, t ^ 3 = Classical.choose r.property / x
    obtain ⟨t, ht⟩ := ratio_cube (Classical.choose r.property) x (Classical.choose_spec r.property)
    exact ⟨t, by simpa only [div_eq_mul_inv] using ht.symm⟩
  exact ⟨Finite.of_surjective qmap hqmap, scalar_cube⟩

end ArtinPrimitiveRoots.A1.Theta
