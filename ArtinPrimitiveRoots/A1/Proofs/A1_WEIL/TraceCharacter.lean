import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.CharacterUniqueness
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».FiniteTraceCharacters

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations UniqueFactorizationMonoid
open scoped BigOperators nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {F : Type} [Field F] [NumberField F]

/-- Identify the supplied finite characters with the local trace of a rational
character family satisfying its global product formula. Keep the completion trace
comparison while proving global compatibility of the constructed family, then use
character uniqueness. Guide: PROOFS.md:480–485; the finite-support reindexing follows
A1-ADDITIVE/IntegralGlobalCharacters.lean. -/
theorem finite_trace_character_comparison (A : AddCharData F)
    (θ : (v : FinPlace ℚ) → AddChar (v.adicCompletion ℚ) ℂ)
    (hθint : ∀ (v : FinPlace ℚ) (x : v.adicCompletion ℚ),
      x ∈ v.adicCompletionIntegers ℚ → θ v x = 1)
    (hθglobal : ∀ r : ℚ,
      (Function.mulSupport fun v => θ v (algebraMap ℚ _ r)).Finite ∧
        (∏ᶠ v, θ v (algebraMap ℚ _ r)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (r : ℂ))) = 1) :
    ∀ (v : FinPlace ℚ)
      (a : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv ℚ v) F)
      (x : a.1.Completion),
      A.ψ (finitePlaceExtensionCentre (K := ℚ) (L := F) v a)
        (finitePlaceExtensionAdicCompletionRingEquiv (K := ℚ) (L := F) v a x) =
      θ v (relativeFinitePlaceCompletionAlgEquiv v
        (traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv ℚ v) a x)) := by
  classical
  let : ∀ v : FinPlace ℚ,
      Fintype {W : FinPlace F // finitePlaceBelow (K := ℚ) W = v} :=
    fun v => by
      let vK := NumberField.HeightOneSpectrum.adicAbv ℚ v
      letI := completionTensorDecomposition_extensionFintype (K := ℚ) (L := F) vK
        (RayClass.adicAbv_isNontrivial v)
      exact Fintype.ofEquiv (AbsoluteValueExtension vK F)
        (finitePlaceExtensionEquivAbove (K := ℚ) (L := F) v)
  obtain ⟨χ, hχint, hχprod, hχcomp⟩ :=
    finiteTraceChar_family (K := ℚ) (L := F) θ hθint
  have hχprod' (v : FinPlace ℚ) (z : F) :
      (∏ W : {W : FinPlace F // finitePlaceBelow (K := ℚ) W = v},
        χ W.1 (algebraMap F (W.1.adicCompletion F) z)) =
      θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) := by
    simpa only [eq_ratCast] using hχprod v z
  have hfinite (z : F) :
      (Function.mulSupport fun v => χ v (algebraMap F (v.adicCompletion F) z)).Finite := by
    obtain ⟨a, d, heq⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
    have hd0 : (d : 𝓞 F) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
    let I : Ideal (𝓞 F) := Ideal.span {(d : 𝓞 F)}
    have hI : I ≠ ⊥ := by simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hd0
    let s := (normalizedFactors I).toFinset
    have hs : {v : FinPlace F | v.asIdeal ∈ s}.Finite :=
      s.finite_toSet.preimage HeightOneSpectrum.asIdeal_injective.injOn
    refine hs.subset ?_
    intro v hv
    change χ v (algebraMap F (v.adicCompletion F) z) ≠ 1 at hv
    change v.asIdeal ∈ s
    by_contra hmem
    have hdnot : (d : 𝓞 F) ∉ v.asIdeal := by
      intro hdmem
      apply hmem
      apply Multiset.mem_toFinset.mpr
      exact (Ideal.mem_normalizedFactors_iff hI).mpr
        ⟨v.isPrime, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hdmem)⟩
    have hden : v.valuation F ((d : 𝓞 F) : F) = 1 :=
      v.valuation_eq_one_iff_notMem.mpr hdnot
    have hz : v.valuation F z ≤ 1 := by
      rw [← heq, IsFractionRing.mk'_eq_div, map_div₀, hden, div_one]
      exact v.valuation_le_one a
    have hzin : algebraMap F (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        v.valuedAdicCompletion_eq_valuation']
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using hz
    exact hv (hχint v _ hzin)
  have hχglobal : ∀ z : F,
      (Function.mulSupport fun v => χ v (algebraMap F _ z)).Finite ∧
        (∏ᶠ v, χ v (algebraMap F _ z)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1 := by
    intro z
    refine ⟨hfinite z, ?_⟩
    let f (W : FinPlace F) : ℂ := χ W (algebraMap F (W.adicCompletion F) z)
    let g (W : FinPlace F) : FinPlace ℚ := finitePlaceBelow (K := ℚ) W
    have hf : (Function.mulSupport f).Finite := hfinite z
    let s := hf.toFinset
    let t := s.image g
    have hfibre (v : FinPlace ℚ) :
        (∏ W ∈ s with g W = v, f W) =
          ∏ W : {W : FinPlace F // g W = v}, f W.1 := by
      rw [← finprod_eq_prod_of_fintype, finprod_subtype_eq_finprod_cond]
      symm
      apply finprod_cond_eq_prod_of_cond_iff
      intro W hW
      have hs : W ∈ s := hf.mem_toFinset.mpr hW
      simp only [Finset.mem_filter, hs, true_and]
    have hbaseout (v : FinPlace ℚ) (hv : v ∉ t) :
        θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) = 1 := by
      rw [← hχprod' v z, ← hfibre v]
      have hempty : s.filter (fun W => g W = v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro W hW
        exact hv (Finset.mem_image.mpr
          ⟨W, (Finset.mem_filter.mp hW).1, (Finset.mem_filter.mp hW).2⟩)
      rw [hempty, Finset.prod_empty]
    have hbasess :
        Function.mulSupport (fun v => θ v
          (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z))) ⊆ (t : Set _) := by
      intro v hv
      by_contra hnot
      exact hv (hbaseout v hnot)
    have hgroup : (∏ᶠ W, f W) = ∏ᶠ v,
        θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) := by
      calc
        (∏ᶠ W, f W) = ∏ W ∈ s, f W :=
          finprod_eq_prod_of_mulSupport_subset f (fun W hW => hf.mem_toFinset.mpr hW)
        _ = ∏ v ∈ t, ∏ W ∈ s with g W = v, f W :=
          (Finset.prod_fiberwise_of_maps_to (g := g) (s := s) (t := t)
            (fun W hW => Finset.mem_image.mpr ⟨W, hW, rfl⟩) f).symm
        _ = ∏ v ∈ t, θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) := by
          apply Finset.prod_congr rfl
          intro v _
          rw [hfibre v]
          exact hχprod' v z
        _ = ∏ᶠ v, θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) :=
          (finprod_eq_prod_of_mulSupport_subset _ hbasess).symm
    change (∏ᶠ W, f W) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1
    rw [hgroup]
    exact (hθglobal (Algebra.trace ℚ F z)).2
  have hA := integral_global_character_family_unique A χ hχint hχglobal
  intro v a x
  rw [hA]
  exact hχcomp v a x

end ArtinPrimitiveRoots.Proofs.a1_weil_sol
