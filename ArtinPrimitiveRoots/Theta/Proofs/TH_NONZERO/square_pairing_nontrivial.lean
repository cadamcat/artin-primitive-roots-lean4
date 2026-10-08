import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- A square torus pair with nontrivial cubic commutator exists at every finite place.
A uniformizer squared has valuation two, so it is not a cube. Cubic nondegeneracy
then supplies a partner; squaring that partner preserves nontriviality in μ₃.
This route uses no tame-character surjectivity or topological closure. -/
theorem square_pairing_nontrivial (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) :
    ∃ t u : (v.adicCompletion F)ˣ, torusPairing D H v (t ^ 2) (u ^ 2) ≠ 1 := by
  have hmu (ζ ξ : rootsOfUnity 6 F) :
      muThree D (ζ * ξ) = muThree D ζ * muThree D ξ := by
    apply rootsOfUnity.coe_injective
    simp [muThree, map_mul, mul_pow]
  have hsq (x y : (v.adicCompletion F)ˣ) :
      torusPairing D H v x (y ^ 2) = torusPairing D H v x y ^ 2 := by
    unfold torusPairing
    rw [pow_two y, H.mul_right, H.mul_left, hmu, hmu, mul_inv_rev]
    simp only [pow_two]
    ac_rfl
  have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hnoncube : ¬ ∃ c : (v.adicCompletion F)ˣ, unifLoc v ^ 2 = c ^ 3 := by
    rintro ⟨c, hc⟩
    have hval := congrArg (fun x : (v.adicCompletion F)ˣ =>
      WithZero.log (Valued.v (x : v.adicCompletion F))) hc
    simp only [Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow, hπ,
      WithZero.log_exp, nsmul_eq_mul] at hval
    omega
  by_contra h
  push Not at h
  have htrivial (y : (v.adicCompletion F)ˣ) : torusPairing D H v (unifLoc v ^ 2) y = 1 := by
    let ζ := torusPairing D H v (unifLoc v ^ 2) y
    have htwo : ζ ^ 2 = 1 := by
      change torusPairing D H v (unifLoc v ^ 2) y ^ 2 = 1
      rw [← hsq]
      exact h (unifLoc v) y
    have hthree : ζ ^ 3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 (ζ : ℂˣ)).mp ζ.property
    have hthree' : ζ ^ 3 = ζ := by
      rw [pow_succ, htwo, one_mul]
    exact hthree'.symm.trans hthree
  exact hnoncube (torusPairing_nondeg (D := D) (H := H) (unifLoc v ^ 2) htrivial)
end ArtinPrimitiveRoots.A1.Theta
