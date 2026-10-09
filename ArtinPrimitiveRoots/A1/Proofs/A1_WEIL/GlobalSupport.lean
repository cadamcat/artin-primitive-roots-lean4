import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.IndexValue
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.GaussianUnit

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Bound the global index support by bad places and the divisor of a.
Guide: PROOFS.md:480–481. Uses: exterior_local_index_unit; SData.nonempty; finite fractional-ideal factorization. -/
theorem global_index_finite_support (D : FieldData F) (A : AddCharData F) (W : LocalGaussianData A) (a : Fˣ) :
    (Function.mulSupport fun v => W.index v (toLoc v a)).Finite := by
  classical
  -- Use an auxiliary nonzero conductor ideal: the exterior-unit lemma only needs
  -- a finite exceptional set and a nonzero ideal for its construction.
  let η : Ideal (𝓞 F) := Ideal.span ({1} : Set (𝓞 F))
  have hη : η ≠ ⊥ := by
    dsimp [η]
    simpa [Ideal.span_singleton_eq_bot]
  obtain ⟨S⟩ := SData.nonempty (F := F) 0 η hη
  let I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)
  have hcountEventually : ∀ᶠ v : FinPlace F in Filter.cofinite,
      FractionalIdeal.count F v I = 0 :=
    FractionalIdeal.finite_factors I
  have hcountFinite : {v : FinPlace F | FractionalIdeal.count F v I ≠ 0}.Finite := by
    exact Filter.eventually_cofinite.mp hcountEventually
  apply (S.Sf.finite_toSet.union hcountFinite).subset
  intro v hv
  simp only [Function.mem_mulSupport, ne_eq] at hv
  by_cases hvS : v ∈ S.Sf
  · exact Set.mem_union_left _ hvS
  · right
    by_contra hcount
    have hcount0 : FractionalIdeal.count F v I = 0 := not_ne_iff.mp hcount
    exact hv (exterior_local_index_unit D S A W v hvS a hcount0)

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
