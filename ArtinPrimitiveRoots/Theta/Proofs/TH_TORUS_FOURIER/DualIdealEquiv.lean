import ArtinPrimitiveRoots.Theta.Proofs.TH_TORUS_FOURIER.IdealLatticeChart

set_option autoImplicit false

open NumberField IsDedekindDomain Module
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]

/-- The full character dual of an ideal has integral coordinates in the rational
trace-dual basis. The sign agrees with the positive exponential Fourier characters. -/
theorem rational_ideal_dual_equiv (D : FieldData F)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) :
    ∃ e : {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1} ≃
        (Free.ChooseBasisIndex ℤ I → ℤ),
      ∀ ν i, (e ν i : ℚ) = -Algebra.trace ℚ F (ν * basisOfFractionalIdeal F I i) := by
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
  have hψ (ν ξ : F) : psiInf ν (infEmbA ξ) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (Algebra.trace ℚ F (ν * ξ) : ℂ))) := by
    change (∏ w : InfinitePlace F, psiC (w.embedding ν * w.embedding ξ)) = _
    simp_rw [← map_mul]
    unfold psiC
    rw [← Complex.exp_sum]
    apply congrArg Complex.exp
    rw [htrace (ν * ξ), Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  have hroot : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hInt (ν ξ : F) : psiInf ν (infEmbA ξ) = 1 ↔
      ∃ n : ℤ, (n : ℚ) = -Algebra.trace ℚ F (ν * ξ) := by
    rw [hψ ν ξ, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      have hmul : (2 * (Real.pi : ℂ) * Complex.I) *
          (-(Algebra.trace ℚ F (ν * ξ) : ℂ)) =
          (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
        calc
          _ = -(2 * (Real.pi : ℂ) * Complex.I *
              (Algebra.trace ℚ F (ν * ξ) : ℂ)) := by ring
          _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
          _ = _ := by ring
      have hc := mul_left_cancel₀ hroot hmul
      refine ⟨n, ?_⟩
      exact_mod_cast hc.symm
    · rintro ⟨n, hn⟩
      have hc : (n : ℂ) = -(Algebra.trace ℚ F (ν * ξ) : ℂ) := by
        exact_mod_cast hn
      refine ⟨n, ?_⟩
      rw [hc]
      ring
  let b := basisOfFractionalIdeal F I
  let l := b.traceDual.equivFun
  have hl (ν : F) (i : Free.ChooseBasisIndex ℤ I) :
      l ν i = Algebra.trace ℚ F (ν * b i) := by
    simp only [l, Basis.equivFun_apply, Basis.traceDual_repr_apply, Algebra.traceForm_apply]
  have hb (i : Free.ChooseBasisIndex ℤ I) : b i ∈ (I : Submodule (𝓞 F) F) := by
    apply (mem_span_basisOfFractionalIdeal (K := F) (I := I)).mp
    exact Submodule.subset_span ⟨i, rfl⟩
  have hDual (ν : F) :
      (∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1) ↔
        ∀ i : Free.ChooseBasisIndex ℤ I, ∃ n : ℤ, (n : ℚ) = -l ν i := by
    constructor
    · intro hν i
      rw [hl]
      exact (hInt ν (b i)).mp (hν (b i) (hb i))
    · intro hν ξ hξ
      have hspan : ξ ∈ Submodule.span ℤ (Set.range b) :=
        (mem_span_basisOfFractionalIdeal (K := F) (I := I)).mpr hξ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan
      choose a ha using hν
      let f : F →ₗ[ℤ] ℚ := (-Algebra.traceForm ℚ F ν).restrictScalars ℤ
      have hf (i : Free.ChooseBasisIndex ℤ I) : f (b i) = -l ν i := by
        change -(Algebra.traceForm ℚ F ν (b i)) = -l ν i
        rw [Algebra.traceForm_apply, hl]
      have ha' (i : Free.ChooseBasisIndex ℤ I) : (a i : ℚ) = f (b i) := by
        rw [hf]
        exact ha i
      apply (hInt ν ξ).mpr
      refine ⟨∑ i, c i * a i, ?_⟩
      change (∑ i, c i * a i : ℤ) = f ξ
      rw [← hc, map_sum]
      simp only [Int.cast_sum, Int.cast_mul]
      simp_rw [f.map_smul]
      simp only [zsmul_eq_mul, ha']
  let Du : Type :=
    {ν : F // ∀ ξ ∈ (I : Submodule (𝓞 F) F), psiInf ν (infEmbA ξ) = 1}
  let toF : Du → (Free.ChooseBasisIndex ℤ I → ℤ) := fun ν i =>
    Classical.choose ((hDual ν.1).mp ν.2 i)
  have hto (ν : Du) (i : Free.ChooseBasisIndex ℤ I) :
      (toF ν i : ℚ) = -l ν.1 i :=
    Classical.choose_spec ((hDual ν.1).mp ν.2 i)
  let invF (k : Free.ChooseBasisIndex ℤ I → ℤ) : Du :=
    ⟨l.symm (fun i => -(k i : ℚ)), (hDual _).mpr (by
      intro i
      exact ⟨k i, by simp⟩)⟩
  have hright (k : Free.ChooseBasisIndex ℤ I → ℤ) : toF (invF k) = k := by
    funext i
    apply Int.cast_injective (α := ℚ)
    rw [hto]
    simp [invF]
  have hleft (ν : Du) : invF (toF ν) = ν := by
    apply Subtype.ext
    apply l.injective
    change l (l.symm (fun i => -(toF ν i : ℚ))) = l ν.1
    rw [l.apply_symm_apply]
    funext i
    rw [hto]
    simp
  refine ⟨{ toFun := toF, invFun := invF, left_inv := hleft, right_inv := hright }, ?_⟩
  intro ν i
  change (toF ν i : ℚ) = _
  rw [hto, hl]

end ArtinPrimitiveRoots.Proofs.thsol_torusf
