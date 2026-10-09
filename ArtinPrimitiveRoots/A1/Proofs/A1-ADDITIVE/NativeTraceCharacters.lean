import ArtinPrimitiveRoots.A1.Proofs.«A1-ADDITIVE».TraceCharacters
import ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison

set_option autoImplicit false

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open scoped BigOperators

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L]

theorem nativeTraceChar_family (v : HeightOneSpectrum (𝓞 K))
    [Fintype {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}]
    (θ : AddChar (v.adicCompletion K) ℂ)
    (hθ : ∀ x : v.adicCompletion K, x ∈ v.adicCompletionIntegers K → θ x = 1) :
    ∃ ψ : (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) →
        AddChar (W.1.adicCompletion L) ℂ,
      (∀ (a : AbsoluteValueExtension (NumberField.HeightOneSpectrum.adicAbv K v) L)
          (x : a.1.Completion),
        ψ (finitePlaceExtensionEquivAbove (K := K) (L := L) v a)
            (finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v a x) =
          θ (relativeFinitePlaceCompletionAlgEquiv v
            (traceAtCompletion (NumberField.HeightOneSpectrum.adicAbv K v) a x))) ∧
      (∀ (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v})
          (x : W.1.adicCompletion L), x ∈ W.1.adicCompletionIntegers L → ψ W x = 1) ∧
      (∀ z : L, (∏ W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v},
          ψ W (algebraMap L (W.1.adicCompletion L) z)) =
        θ (algebraMap K (v.adicCompletion K) (Algebra.trace K L z))) := by
  classical
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  have hvK : IsNonarchimedean (vK : K → ℝ) :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v
  have hvK0 : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) v
  let : Fintype (AbsoluteValueExtension vK L) :=
    Fintype.ofEquiv
      {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v} e.symm
  let baseE := relativeFinitePlaceCompletionAlgEquiv v
  let Θ : AddChar vK.Completion ℂ :=
    θ.compAddMonoidHom baseE.toRingHom.toAddMonoidHom
  have hΘ (x : vK.Completion) (hx : ‖x‖ ≤ 1) : Θ x = 1 := by
    change θ (baseE x) = 1
    apply hθ
    apply mem_adicCompletionIntegers_of_norm_le_one v
    rw [show ‖baseE x‖ = ‖x‖ from relativeFinitePlaceCompletionRingEquiv_norm v x]
    exact hx
  obtain ⟨ψa, hcomp, hint, hprod⟩ :=
    localTraceChar_family (K := K) (L := L) vK hvK hvK0 Θ hΘ
  let κ (a : AbsoluteValueExtension vK L) :
      a.1.Completion ≃+* (e a).1.adicCompletion L :=
    finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v a
  let P := fun W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v} =>
    AddChar (W.1.adicCompletion L) ℂ
  let f : (a : AbsoluteValueExtension vK L) → P (e a) :=
    fun a => (ψa a).compAddMonoidHom (κ a).symm.toRingHom.toAddMonoidHom
  let ψ := (Equiv.piCongrLeft P e) f
  have hψ (a : AbsoluteValueExtension vK L) : ψ (e a) = f a := by
    simp only [ψ, Equiv.piCongrLeft_apply_apply]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro a x
    rw [hψ a]
    change ψa a ((κ a).symm ((κ a) x)) = Θ (traceAtCompletion vK a x)
    rw [RingEquiv.symm_apply_apply]
    exact hcomp a x
  · intro W
    obtain ⟨a, rfl⟩ := e.surjective W
    intro x hx
    rw [hψ a]
    change ψa a ((κ a).symm x) = 1
    apply hint a _
    have haInt : κ a ((κ a).symm x) ∈ (e a).1.adicCompletionIntegers L := by
      simpa only [RingEquiv.apply_symm_apply] using hx
    have habs := (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
      (K := K) (L := L) v a ((κ a).symm x)).mp haInt
    simpa only [mem_absoluteValueCompletionIntegers_iff] using habs
  · intro z
    have hemb (a : AbsoluteValueExtension vK L) :
        κ a (algebraMap L a.1.Completion z) =
          algebraMap L ((e a).1.adicCompletion L) z := by
      have h := finitePlaceExtensionAdicCompletionRingEquiv_toCompletion
        (K := K) (L := L) v a z
      rw [AbsoluteValue.toCompletion_eq_algebraMap] at h
      convert h using 1 <;> rfl
    calc
      (∏ W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v},
          ψ W (algebraMap L (W.1.adicCompletion L) z)) =
          ∏ a : AbsoluteValueExtension vK L,
            ψ (e a) (algebraMap L ((e a).1.adicCompletion L) z) :=
        (e.prod_comp (fun W => ψ W (algebraMap L (W.1.adicCompletion L) z))).symm
      _ = ∏ a : AbsoluteValueExtension vK L,
          ψa a (algebraMap L a.1.Completion z) := by
        apply Finset.prod_congr rfl
        intro a _
        rw [← hemb a, hψ a]
        change ψa a ((κ a).symm ((κ a) (algebraMap L a.1.Completion z))) = _
        rw [RingEquiv.symm_apply_apply]
      _ = Θ (algebraMap K vK.Completion (Algebra.trace K L z)) := hprod z
      _ = θ (algebraMap K (v.adicCompletion K) (Algebra.trace K L z)) := by
        change θ (baseE (algebraMap K vK.Completion (Algebra.trace K L z))) = _
        rw [baseE.commutes]

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
