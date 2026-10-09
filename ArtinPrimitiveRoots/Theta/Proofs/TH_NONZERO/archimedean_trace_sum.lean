import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false
open NumberField
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

variable (F : Type*) [Field F] [NumberField F] [IsTotallyComplex F]

/-- The trace in a totally complex field is twice the sum of the real
parts of the chosen embeddings at its infinite places. -/
theorem archimedean_trace_sum (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  classical
  have hpair : (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F,
        (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
    have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := z)
    have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
      exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
    have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
      rw [hring.symm] at htrace
      exact htrace
    rw [hall]
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
    apply Finset.sum_congr rfl
    intro w hw
    have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
        φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
      constructor
      · intro h
        rw [← InfinitePlace.mk_embedding w] at h
        have h' := InfinitePlace.mk_eq_iff.mp h
        rcases h' with h' | h'
        · exact Or.inl (by simpa using h')
        · right
          have hc := congrArg ComplexEmbedding.conjugate h'
          simpa using hc
      · intro h
        rw [← InfinitePlace.mk_embedding w]
        apply InfinitePlace.mk_eq_iff.mpr
        rcases h with h | h
        · exact Or.inl (by simpa using h)
        · right
          have hc := congrArg ComplexEmbedding.conjugate h
          simpa using hc
    have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      apply (IsTotallyComplex.complexEmbedding_not_isReal w.embedding)
      rw [ComplexEmbedding.isReal_iff]
      exact h.symm
    have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
        ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
      ext φ
      simp [hmk]
    change (∑ φ ∈ Finset.univ.filter
      (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
    rw [hset, Finset.sum_pair hneq]
  rw [hpair]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

end ArtinPrimitiveRoots.A1.Theta
