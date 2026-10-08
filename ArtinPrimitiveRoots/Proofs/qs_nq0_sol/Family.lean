import ArtinPrimitiveRoots.Proofs.qs_nq0_sol.ProductConductors
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».Defs

/-!
# The canonical narrow quadratic family

Assemble the local Hilbert-character family, its primitive conductors,
quadratic reciprocity, and the exact equal-class product conductor.
The planned signature is:
```
theorem qs_nq0_conductor_family
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη)
    (H : HilbertData K) (Bd : BData Sd H) (a : Ideal (𝓞 K) → Kˣ)
    (ha : ∀ I, Sd.IsExterior I → Sd.IsGen (a I : K) I ∧ Bd.Allowed (a I))
    (χ : Ideal (𝓞 K) → HeckeChar K)
    (hχ : ∀ I, χ I ^ 2 = 1)
    (hinf : ∀ I (w : InfinitePlace K) (u : w.Completionˣ), (χ I).locInf w u = 1)
    (hloc : ∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
      (((χ I).loc v u : ℂˣ) : ℂ) =
        D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3) :
    ∃ (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
      (F : QSFamily m qS),
      qS ≠ ⊥ ∧ m.finitePart.support = Sd.Sf ∧
      (∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf) ∧
      (∀ g h, F.rayFactor g h = 1) ∧
      (∀ I, Sd.IsExterior I → F.character I = χ I)
```
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain ArtinPrimitiveRoots.A1

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- The canonical quadratic characters and conductors form a narrow sieve family. -/
theorem qs_nq0_conductor_family
    {CE : ℕ} {condη : Ideal (𝓞 K)}
    (D : FieldData K) (Sd : SData K CE condη)
    (H : HilbertData K) (Bd : BData Sd H) (a : Ideal (𝓞 K) → Kˣ)
    (ha : ∀ I, Sd.IsExterior I → Sd.IsGen (a I : K) I ∧ Bd.Allowed (a I))
    (χ : Ideal (𝓞 K) → HeckeChar K)
    (hχ : ∀ I, χ I ^ 2 = 1)
    (hinf : ∀ I (w : InfinitePlace K) (u : w.Completionˣ), (χ I).locInf w u = 1)
    (hloc : ∀ I (v : FinPlace K) (u : (v.adicCompletion K)ˣ),
      (((χ I).loc v u : ℂˣ) : ℂ) =
        D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3) :
    ∃ (m : ClassFieldTheory.RayClassModulus K) (qS : Ideal (𝓞 K))
      (F : QSFamily m qS),
      qS ≠ ⊥ ∧ m.finitePart.support = Sd.Sf ∧
      (∀ v : FinPlace K, qS ≤ v.asIdeal → v ∈ Sd.Sf) ∧
      (∀ g h, F.rayFactor g h = 1) ∧
      (∀ I, Sd.IsExterior I → F.character I = χ I) := by
  classical
  have hlocal (I : Ideal (𝓞 K)) (v : FinPlace K) :
      (χ I).loc v = qsNQQuadraticLocal D H v (toLoc v (a I)) := by
    apply MonoidHom.ext
    intro u
    apply Units.ext
    change (((χ I).loc v u : ℂˣ) : ℂ) =
      D.σ0 (((H.hilb v (toLoc v (a I)) u : Kˣ) : K)) ^ 3
    exact hloc I v u
  obtain ⟨m, hm, _, hsix⟩ := qs_nq0_sixth_power_ray_modulus Sd.Sf
  have hexterior (I : Ideal (𝓞 K)) (hcm : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I) :
      Sd.IsExterior I := by
    obtain ⟨hI, hmem⟩ := hcm
    change ∀ v, v ∈ m.finitePart.support → FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 0 at hmem
    refine ⟨hI, ?_⟩
    intro v hv hle
    have hcount := hmem v (by rwa [hm])
    rw [FractionalIdeal.count_coe K v hI] at hcount
    change (idealExp v I : ℤ) = 0 at hcount
    have hzero : idealExp v I = 0 := by exact_mod_cast hcount
    have hnonzero : idealExp v I ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hI v.irreducible).mpr
        (Ideal.dvd_iff_le.mpr hle)
    exact hnonzero hzero
  obtain ⟨qS, hqS, hsupport, f, hf⟩ := qs_nq0_quadratic_family_conductors
    D Sd H a (fun I hI => (ha I hI).1) χ hlocal
  let F : QSFamily m qS := {
    character := χ
    conductor := f
    rayFactor := fun _ _ => 1
    rayFactor_quadratic := by intros; simp
    trivial_infinite_type := hinf
    indexCondition := by
      intro I hsq hcm
      obtain ⟨hprimitive, hfactor⟩ := hf I hsq (hexterior I hcm)
      exact ⟨isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hχ I⟩,
        hprimitive, hfactor⟩
    character_order_two := fun I _ _ => hχ I
    quadraticValues := fun I _ _ J => qs_nq0_quadratic_ideal_values (χ I) (hχ I) J
    reciprocity := by
      intro I J hI hcmI hJ hcmJ hcoprime
      change (χ I).idealValue J = ((1 : ℂˣ) : ℂ) * (χ J).idealValue I
      simpa only [Units.val_one, one_mul] using
        qs_nq0_quadratic_reciprocity D Sd H Bd I J (a I) (a J)
          (ha I (hexterior I hcmI)) (ha J (hexterior J hcmJ)) hcoprime
          (χ I) (χ J) (hχ I) (hlocal I) (hlocal J)
    equalClass_product_conductor := by
      intro I J hI hcmI hJ hcmJ hcoprime hclass
      have haI := ha I (hexterior I hcmI)
      have haJ := ha J (hexterior J hcmJ)
      have hroot := qs_nq0_equal_rayclass_allowed_ratio Sd H Bd m hm hsix
        I J (a I) (a J) haI haJ hcmI hcmJ hclass
      exact qs_nq0_quotient_primitive_conductor D Sd H I J hI hJ hcoprime
        (a I) (a J) haI.1 haJ.1 (χ I) (χ J) (hlocal I) (hlocal J) hroot
  }
  refine ⟨m, qS, F, hqS, hm, hsupport, ?_, ?_⟩
  · intro g h
    rfl
  · intro I hI
    rfl

end ArtinPrimitiveRoots.A2
