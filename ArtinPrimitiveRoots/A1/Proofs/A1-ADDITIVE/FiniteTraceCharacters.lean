import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».NativeTraceCharacters

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

theorem finiteTraceChar_family
    [∀ v : HeightOneSpectrum (𝓞 K),
      Fintype {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}]
    (θ : (v : HeightOneSpectrum (𝓞 K)) → AddChar (v.adicCompletion K) ℂ)
    (hθ : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      x ∈ v.adicCompletionIntegers K → θ v x = 1) :
    ∃ ψ : (W : HeightOneSpectrum (𝓞 L)) → AddChar (W.adicCompletion L) ℂ,
      (∀ (W : HeightOneSpectrum (𝓞 L)) (x : W.adicCompletion L),
        x ∈ W.adicCompletionIntegers L → ψ W x = 1) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (z : L),
        (∏ W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v},
          ψ W.1 (algebraMap L (W.1.adicCompletion L) z)) =
        θ v (algebraMap K (v.adicCompletion K) (Algebra.trace K L z))) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K))
          (a : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv K v) L)
          (x : a.1.Completion),
        ψ (finitePlaceExtensionCentre (K := K) (L := L) v a)
            (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v a x) =
          θ v (relativeFinitePlaceCompletionAlgEquiv v
            (traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv K v) a x))) := by
  classical
  choose χ hcomp hint hprod using
    fun v : HeightOneSpectrum (𝓞 K) =>
      nativeTraceChar_family (K := K) (L := L) v (θ v) (hθ v)
  let ψ (W : HeightOneSpectrum (𝓞 L)) : AddChar (W.adicCompletion L) ℂ :=
    χ (finitePlaceBelow (K := K) W) ⟨W, rfl⟩
  have hψ (v : HeightOneSpectrum (𝓞 K))
      (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
      ψ W.1 = χ v W := by
    rcases W with ⟨W, hW⟩
    subst v
    rfl
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro W x hx
    exact hint (finitePlaceBelow (K := K) W) ⟨W, rfl⟩ x hx
  · intro v z
    calc
      (∏ W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v},
          ψ W.1 (algebraMap L (W.1.adicCompletion L) z)) =
          ∏ W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v},
            χ v W (algebraMap L (W.1.adicCompletion L) z) := by
        apply Finset.prod_congr rfl
        intro W _
        rw [hψ v W]
      _ = θ v (algebraMap K (v.adicCompletion K) (Algebra.trace K L z)) := hprod v z
  · intro v a x
    have h := hcomp v a x
    rw [← hψ v (finitePlaceExtensionEquivAbove (K := K) (L := L) v a)] at h
    exact h

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
