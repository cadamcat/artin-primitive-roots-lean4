import ArtinPrimitiveRoots.Hecke.Theta.CFTIdealBridge

/-!
# Finite character orthogonality for the ray class theta sum

This is the elementary finite-group input needed to cancel the constant term in the
character-weighted theta kernel.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace ArtinPrimitiveRoots.Hecke

theorem sum_char_eq_zero_of_nontrivial {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) : ∑ g : G, (χ g : ℂ) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : G, χ g ≠ 1 := by
    by_contra h
    push Not at h
    apply hχ
    ext x
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (h x)
  have hg' : (χ g : ℂ) ≠ 1 := by
    intro h
    apply hg
    exact Units.ext h
  let S : ℂ := ∑ x : G, (χ x : ℂ)
  have hmul : S = S * (χ g : ℂ) := by
    dsimp [S]
    calc
      (∑ x : G, (χ x : ℂ)) = ∑ x : G, (χ (x * g) : ℂ) := by
        exact (Equiv.sum_comp (Equiv.mulRight g) (fun x : G => (χ x : ℂ))).symm
      _ = ∑ x : G, ((χ x : ℂ) * (χ g : ℂ)) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [map_mul, Units.val_mul]
      _ = (∑ x : G, (χ x : ℂ)) * (χ g : ℂ) := by rw [Finset.sum_mul]
  have hzero : S * ((χ g : ℂ) - 1) = 0 := by
    calc
      S * ((χ g : ℂ) - 1) = S * (χ g : ℂ) - S := by ring
      _ = S - S := by rw [← hmul]
      _ = 0 := sub_self _
  have : S = 0 := (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hg')
  exact this

/-- Pulling back a nontrivial character along a surjective finite-group homomorphism preserves
nontriviality, so its sum over the source group also vanishes. -/
theorem sum_comp_char_eq_zero_of_surjective {H G : Type*} [Group H] [Fintype H]
    [Group G] [Fintype G] (f : H →* G) (hf : Function.Surjective f)
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ h : H, (χ (f h) : ℂ) = 0 := by
  apply sum_char_eq_zero_of_nontrivial (χ.comp f)
  intro hcomp
  apply hχ
  ext g
  obtain ⟨h, rfl⟩ := hf g
  simpa using congrArg (fun ψ : H →* ℂˣ => ψ h) hcomp

variable {K : Type*} [Field K] [NumberField K]

local instance rayClassGroupFintype [IsTotallyComplex K]
    (m : ClassFieldTheory.RayClassModulus K) : Fintype (ClassFieldTheory.RayClassGroup m) := by
  letI : Finite (ClassFieldTheory.RayClassGroup m) := rayClassGroup_finite_viaCFT m
  exact Fintype.ofFinite _

theorem rayClassCharacter_sum_eq_zero [IsTotallyComplex K]
    {m : ClassFieldTheory.RayClassModulus K}
    (η : ClassFieldTheory.RayClassGroup m →* ℂˣ) (hη : η ≠ 1) :
    ∑ C : ClassFieldTheory.RayClassGroup m, (η C : ℂ) = 0 := by
  classical
  exact sum_char_eq_zero_of_nontrivial η hη

end ArtinPrimitiveRoots.Hecke

end
