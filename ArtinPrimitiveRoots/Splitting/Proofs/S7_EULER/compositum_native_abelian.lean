import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.Defs

set_option autoImplicit false
open scoped NumberField
open NumberField
noncomputable section
namespace ArtinPrimitiveRoots.Splitting

/-- The native splitting-field algebra over the cyclotomic base is abelian.
Guide: ../sol-thin-s7/PROOFS.md:366–397; arithmetic prerequisite for the
specialization of the general Euler core. Uses the Kummer splitting-field lemmas
and the fact that the base contains the qth roots of unity. Feeds
`sp_upstairs_factor`, whose frozen Artin target uses this native algebra.
The arbitrary algebra stored in `AbelianExtensionData` is not definitionally
equal to the native splitting-field algebra. -/
theorem compositum_native_abelian (a : ℤ) (q : ℕ) [NeZero q] [NeZero (12 * q)]
    (hq : q.Prime) : IsAbelianGalois (heckeBaseField q) (compositumField a q) := by
  classical
  let K := heckeBaseField q
  let L := compositumField a q
  let f : Polynomial K := Polynomial.X ^ q - Polynomial.C (a : K)
  change IsAbelianGalois K L
  letI : IsCyclotomicExtension {12 * q} ℚ K :=
    CyclotomicField.isCyclotomicExtension (12 * q) ℚ
  let ζ : K := IsCyclotomicExtension.zeta (12 * q) ℚ K
  have hζ : IsPrimitiveRoot ζ (12 * q) :=
    IsCyclotomicExtension.zeta_spec (12 * q) ℚ K
  have hζq : IsPrimitiveRoot (ζ ^ 12) q := by
    have hdiv : 12 ∣ 12 * q := ⟨q, rfl⟩
    simpa using hζ.pow_of_dvd (by norm_num) hdiv
  have hprim : (primitiveRoots q K).Nonempty := by
    refine ⟨ζ ^ 12, ?_⟩
    exact (mem_primitiveRoots (NeZero.pos q)).mpr hζq
  by_cases hroot : ∃ b : K, b ^ q = (a : K)
  · obtain ⟨b, hb⟩ := hroot
    have hsplit : f.Splits :=
      X_pow_sub_C_splits_of_isPrimitiveRoot hζq hb
    have hAlg : Algebra.adjoin K (f.rootSet K) = ⊤ := by
      apply Algebra.eq_top_iff.mpr
      intro x
      simpa using (Algebra.adjoin K (f.rootSet K)).algebraMap_mem x
    have hbaseSplit : Polynomial.IsSplittingField K K f :=
      isSplittingField_iff_intermediateField.mpr
        ⟨by simpa using hsplit,
          IntermediateField.adjoin_eq_top_of_algebra K (f.rootSet K) hAlg⟩
    letI : Polynomial.IsSplittingField K K f := hbaseSplit
    have eL : L ≃ₐ[K] f.SplittingField := Polynomial.IsSplittingField.algEquiv L f
    have eK : K ≃ₐ[K] f.SplittingField := Polynomial.IsSplittingField.algEquiv K f
    let e : L ≃ₐ[K] K := eL.trans eK.symm
    letI : IsGalois K L := e.transfer_galois.mpr (IsGalois.self K)
    have hx (x : L) : x = algebraMap K L (e x) := by
      calc
        x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = algebraMap K L (e x) := by simpa using e.symm.commutes (e x)
    have hfix (σ : Gal(L/K)) (x : L) : σ x = x := by
      calc
        σ x = σ (algebraMap K L (e x)) := congrArg σ (hx x)
        _ = algebraMap K L (e x) := by simp
        _ = x := (hx x).symm
    haveI : Subsingleton (Gal(L/K)) := ⟨fun σ τ => by
      ext x
      calc
        σ x = x := hfix σ x
        _ = τ x := (hfix τ x).symm⟩
    exact IsAbelianGalois.of_isCyclic K L
  · have hIrr : Irreducible f := by
      exact ArtinPrimitiveRoots.Ext.SplittingInputs.ext_kummer_irreducible
        (K := K) hq (a := (a : K)) (by
          intro b hb
          exact hroot ⟨b, hb⟩)
    letI : IsGalois K L :=
      isGalois_of_isSplittingField_X_pow_sub_C hprim hIrr L
    letI : IsCyclic Gal(L/K) :=
      isCyclic_of_isSplittingField_X_pow_sub_C hprim hIrr L
    exact IsAbelianGalois.of_isCyclic K L

end ArtinPrimitiveRoots.Splitting
end
