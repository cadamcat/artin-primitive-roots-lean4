import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_GAUSS.Gamma

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Replace the quadratic multiplicative Gauss sum by the residue square sum.
Uses: A1_GAUSS residue character/additive helpers; quadraticChar_card_sqrts; additive orthogonality. -/
theorem gamma_three_eq_square_sum (D : FieldData F) (S : SData F CE condη) (A : AddCharData F)
    (v : FinPlace F) (hv : v ∉ S.Sf) (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal) :
    gamma D S A 3 v.asIdeal (p : F) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  let k := 𝓞 F ⧸ v.asIdeal
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (S.over6 v h)
  obtain ⟨χ, hχ, hχ6⟩ := ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_character_exists D v h6
  obtain ⟨ψ, hψ, hψprim⟩ :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_additive_character_exists
      D S A v hp.1 (p : F) hp
  have hodd : ringChar k ≠ 2 := by
    intro h
    have hneg' : (-1 : k) = 1 := neg_one_eq_one_iff.mpr h
    apply h6
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [map_ofNat]
    linear_combination -3 * hneg'
  have hχ3 : χ ^ 3 = ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex (k := k) :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.residue_character_cube_eq_quadraticComplex
      D v h6 χ hχ hχ6
  have hψne : ψ ≠ 1 := by
    intro heq
    have hprim := hψprim (a := (1 : k)) one_ne_zero
    exact hprim (by simp [heq])
  have hroots (s : k) :
      ((Finset.univ.filter (fun t : k => t ^ 2 = s)).card : ℂ) =
        ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex s + 1 := by
    have h : ((Finset.univ.filter (fun t : k => t ^ 2 = s)).card : ℤ) =
        quadraticChar k s + 1 := by
      simpa only [Set.toFinset_ofPred] using quadraticChar_card_sqrts hodd s
    have hc := congrArg (Int.castRingHom ℂ) h
    simpa [ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex] using hc
  have hsquare : (∑ t : k, ψ (t ^ 2)) =
      gaussSum (ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex (k := k)) ψ := by
    calc
      (∑ t : k, ψ (t ^ 2)) =
          ∑ s : k, ∑ t ∈ Finset.univ with t ^ 2 = s, ψ s :=
        (Finset.sum_fiberwise' Finset.univ (fun t : k => t ^ 2)
          (fun s : k => ψ s)).symm
      _ = ∑ s : k,
          (ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex s + 1) * ψ s := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_const, nsmul_eq_mul, hroots]
      _ = (∑ s : k,
          ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex s * ψ s) +
          ∑ s : k, ψ s := by
        simp only [add_mul, one_mul, Finset.sum_add_distrib]
      _ = gaussSum (ArtinPrimitiveRoots.Proofs.a1_gauss_sol.quadraticComplex (k := k)) ψ := by
        rw [ψ.sum_eq_zero_of_ne_one hψne]
        simp [gaussSum]
  have hcard : Fintype.card k = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have hgamma :=
    ArtinPrimitiveRoots.Proofs.a1_gauss_sol.gamma_prime_eq_normalizedGauss
      D S A v (p : F) χ hχ ψ hψ 3 (by decide)
  calc
    gamma D S A 3 v.asIdeal (p : F) =
        ArtinPrimitiveRoots.Proofs.a1_gauss_sol.normalizedGauss (χ ^ 3) ψ := hgamma
    _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
        ∑ᶠ x : 𝓞 F ⧸ v.asIdeal,
          S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by
      rw [hχ3]
      unfold ArtinPrimitiveRoots.Proofs.a1_gauss_sol.normalizedGauss
      rw [← hcard, ← hsquare, finsum_eq_sum_of_fintype]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      calc
        ψ (x ^ 2) = ψ ((Ideal.Quotient.mk v.asIdeal x.out) ^ 2) := by
          rw [Ideal.Quotient.mk_out]
        _ = ψ (Ideal.Quotient.mk v.asIdeal (x.out ^ 2)) := by rw [← map_pow]
        _ = S.e A (S.diag (algebraMap (𝓞 F) F (x.out ^ 2) / (p : F))) := hψ _
        _ = S.e A (S.diag ((algebraMap (𝓞 F) F x.out) ^ 2 / (p : F))) := by congr 1

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
