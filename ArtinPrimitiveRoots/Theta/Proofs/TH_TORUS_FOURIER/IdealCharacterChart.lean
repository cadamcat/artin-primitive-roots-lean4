import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.DualIdealEquiv

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- The lattice chart identifies all archimedean characters with the positive
exponential Fourier characters on real coordinates. -/
theorem ideal_character_chart (D : FieldData F)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
    ∃ (b : Basis (Free.ChooseBasisIndex ℤ I) ℝ (InfinitePlace F → ℂ))
      (e : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1} ≃
        (Free.ChooseBasisIndex ℤ I → ℤ)),
      (∀ i, b i = infEmbA (basisOfFractionalIdeal F I i)) ∧
      (Submodule.span ℤ (Set.range b)).toAddSubgroup =
        (I : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom ∧
      ∀ (ν : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1})
        (x : Free.ChooseBasisIndex ℤ I → ℝ),
        psiInf ν.1 (b.equivFun.symm x) =
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
            ∑ i, (e ν i : ℂ) * (x i : ℂ)) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hpair (z : F) : (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F,
        (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
    have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
    have hring : (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
    have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
      rw [hring.symm] at htrace
      exact htrace
    rw [hall, ← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
    apply Finset.sum_congr rfl
    intro w _
    have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
        φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
      constructor
      · intro h
        rw [← InfinitePlace.mk_embedding w] at h
        rcases InfinitePlace.mk_eq_iff.mp h with h | h
        · exact Or.inl (by simpa using h)
        · right
          have hc := congrArg ComplexEmbedding.conjugate h
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
      apply IsTotallyComplex.complexEmbedding_not_isReal w.embedding
      rw [ComplexEmbedding.isReal_iff]
      exact h.symm
    have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
        ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
      ext φ
      simp [hmk]
    change (∑ φ ∈ Finset.univ.filter
      (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
    rw [hset, Finset.sum_pair hneq]
  have htrace (z : F) : (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
    rw [hpair]
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [Finset.mul_sum]
  obtain ⟨b, hb, hspan⟩ := ideal_lattice_chart D I
  obtain ⟨e, he⟩ := rational_ideal_dual_equiv D I
  let L (ν : F) : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ :=
    2 • ∑ w : InfinitePlace F,
      Complex.reLm.comp ((LinearMap.mulLeft ℝ (w.embedding ν)).comp (LinearMap.proj w))
  have hL (ν : F) (t : InfinitePlace F → ℂ) :
      (L ν t : ℂ) = (2 : ℂ) *
        ∑ w : InfinitePlace F, ((w.embedding ν * t w).re : ℂ) := by
    simp [L, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.proj_apply, Complex.ofReal_sum]
  have hLb (ν : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1})
      (i : Free.ChooseBasisIndex ℤ I) : L ν.1 (b i) = -(e ν i : ℝ) := by
    apply Complex.ofReal_injective
    rw [hL, hb]
    have ht := htrace (ν.1 * basisOfFractionalIdeal F I i)
    simp_rw [map_mul] at ht
    have hec : (e ν i : ℂ) =
        -(Algebra.trace ℚ F (ν.1 * basisOfFractionalIdeal F I i) : ℂ) := by
      exact_mod_cast he ν i
    simp only [Complex.ofReal_neg, Complex.ofReal_intCast]
    change (2 : ℂ) * ∑ w : InfinitePlace F,
      ((w.embedding ν.1 * w.embedding (basisOfFractionalIdeal F I i)).re : ℂ) =
        -(e ν i : ℂ)
    rw [← ht, hec, neg_neg]
  have hcoordinates
      (ν : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1})
      (x : Free.ChooseBasisIndex ℤ I → ℝ) :
      L ν.1 (b.equivFun.symm x) = -∑ i, (e ν i : ℝ) * x i := by
    rw [Basis.equivFun_symm_apply, map_sum]
    simp_rw [(L ν.1).map_smul, hLb, smul_eq_mul]
    simp only [mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hexp (ν : F) (t : InfinitePlace F → ℂ) :
      psiInf ν t = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (L ν t : ℂ))) := by
    unfold psiInf psiC
    rw [← Complex.exp_sum]
    apply congrArg Complex.exp
    rw [hL, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  refine ⟨b, e, hb, hspan, ?_⟩
  intro ν x
  rw [hexp, hcoordinates, Complex.ofReal_neg, Complex.ofReal_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

end ArtinPrimitiveRoots.Proofs.thsol_torusf
