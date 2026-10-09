import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».FiniteTraceCharacters
import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».RationalProduct

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations UniqueFactorizationMonoid
open scoped BigOperators nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

theorem integralGlobalChar_family (F : Type*) [Field F] [NumberField F] :
    ∃ ψ : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ,
      (∀ z : F,
        (Function.mulSupport fun v => ψ v (algebraMap F (v.adicCompletion F) z)).Finite ∧
          (∏ᶠ v, ψ v (algebraMap F (v.adicCompletion F) z)) *
            Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        x ∈ v.adicCompletionIntegers F → ψ v x = 1)
 := by
  classical
  choose θ hθ hformula using
    fun v : HeightOneSpectrum (𝓞 ℚ) => rationalCompletionChar_exists v
  let : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Fintype {W : HeightOneSpectrum (𝓞 F) // finitePlaceBelow (K := ℚ) W = v} :=
    fun v => by
      let vK := NumberField.HeightOneSpectrum.adicAbv ℚ v
      letI := completionTensorDecomposition_extensionFintype (K := ℚ) (L := F) vK
        (RayClass.adicAbv_isNontrivial v)
      exact Fintype.ofEquiv (AbsoluteValueExtension vK F)
        (finitePlaceExtensionEquivAbove (K := ℚ) (L := F) v)
  obtain ⟨ψ, hint, hprod, _hcomp⟩ :=
    finiteTraceChar_family (K := ℚ) (L := F) θ (fun v x hx => (hθ v x).mpr hx)
  have hfinite (z : F) :
      (Function.mulSupport fun v => ψ v (algebraMap F (v.adicCompletion F) z)).Finite := by
    obtain ⟨a, d, heq⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
    have hd0 : (d : 𝓞 F) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
    let I : Ideal (𝓞 F) := Ideal.span {(d : 𝓞 F)}
    have hI : I ≠ ⊥ := by simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hd0
    let s := (normalizedFactors I).toFinset
    have hs : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∈ s}.Finite :=
      s.finite_toSet.preimage HeightOneSpectrum.asIdeal_injective.injOn
    refine hs.subset ?_
    intro v hv
    change ψ v (algebraMap F (v.adicCompletion F) z) ≠ 1 at hv
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
    exact hv (hint v _ hzin)
  refine ⟨ψ, ?_, hint⟩
  intro z
  refine ⟨hfinite z, ?_⟩
  let f (W : HeightOneSpectrum (𝓞 F)) : ℂ := ψ W (algebraMap F (W.adicCompletion F) z)
  let g (W : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 ℚ) :=
    finitePlaceBelow (K := ℚ) W
  have hf : (Function.mulSupport f).Finite := hfinite z
  let s := hf.toFinset
  let t := s.image g
  have hfibre (v : HeightOneSpectrum (𝓞 ℚ)) :
      (∏ W ∈ s with g W = v, f W) =
        ∏ W : {W : HeightOneSpectrum (𝓞 F) // g W = v}, f W.1 := by
    rw [← finprod_eq_prod_of_fintype, finprod_subtype_eq_finprod_cond]
    symm
    apply finprod_cond_eq_prod_of_cond_iff
    intro W hW
    have hs : W ∈ s := hf.mem_toFinset.mpr hW
    simp only [Finset.mem_filter, hs, true_and]
  have hbaseout (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ t) :
      θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) = 1 := by
    rw [← hprod v z, ← hfibre v]
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
        exact hprod v z
      _ = ∏ᶠ v, θ v (algebraMap ℚ (v.adicCompletion ℚ) (Algebra.trace ℚ F z)) :=
        (finprod_eq_prod_of_mulSupport_subset _ hbasess).symm
  change (∏ᶠ W, f W) *
    Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1
  rw [hgroup]
  exact (rationalChar_product θ hθ hformula (Algebra.trace ℚ F z)).2

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
