import /- Local package with a quoted directory name. -/ ArtinPrimitiveRoots.Hecke.Proofs.«HK-FE».Defs


set_option autoImplicit false
open NumberField ClassFieldTheory IsDedekindDomain DedekindResidue
open scoped NumberField nonZeroDivisors
noncomputable section
namespace ArtinPrimitiveRoots.Hecke
variable {K : Type*} [Field K] [NumberField K]

/-- The point ideal is integral, and contraction really recovers it.
Uses fractional-ideal invertibility and x in I;
no new quotient operation or principality of I is assumed. -/
theorem hk_point_ideal_integral (I : NumberFieldFractionalIdealGroup K) {x : K}
    (hx : x ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    ((hkIntegralPart (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
      (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by
  let F : FractionalIdeal (𝓞 K)⁰ K :=
    FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K)
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤
      (I : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
  have hunit : (I : FractionalIdeal (𝓞 K)⁰ K) *
      (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
    rw [← DedekindResidue.val_unit_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hFle : F ≤ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    dsimp [F]
    calc
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) ≤
          (I : FractionalIdeal (𝓞 K)⁰ K) *
            (I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) := by gcongr
      _ = 1 := hunit
  obtain ⟨J, hJ⟩ := (FractionalIdeal.le_one_iff_exists_coeIdeal).mp hFle
  have hcontract : hkIntegralPart F = J := by
    apply Ideal.ext
    intro a
    change (algebraMap (𝓞 K) K a ∈ F) ↔ a ∈ J
    rw [← hJ, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨b, hb, hba⟩
      have hEq : b = a := FaithfulSMul.algebraMap_injective (𝓞 K) K hba
      simpa [hEq] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  change ((hkIntegralPart F : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = F
  rw [hcontract, hJ]

end ArtinPrimitiveRoots.Hecke
