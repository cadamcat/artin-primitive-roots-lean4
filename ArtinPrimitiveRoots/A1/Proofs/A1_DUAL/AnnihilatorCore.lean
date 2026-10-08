import ArtinPrimitiveRoots.A1.AddChar

/-! Core interfaces for the additive annihilator proof. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Module
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_dual_p

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The diagonal additive character is trivial on S-integers. -/
theorem e_diag_R_eq_one [IsTotallyComplex F] (D : A1.FieldData F)
    (S : A1.SData F CE condη) (A : A1.AddCharData F) (r : S.R) :
    S.e A (S.diag (r : F)) = 1 := by
  have hrmem : (r : F) ∈ (S.Sf : Set (A1.FinPlace F)).integer F := r.property
  have hr : ∀ v : A1.FinPlace F, v ∉ S.Sf → v.valuation F (r : F) ≤ 1 := by
    intro v hv
    change ∀ v ∉ S.Sf, v.valuation F (r : F) ≤ 1 at hrmem
    exact hrmem v hv
  have h1 : ∀ v : A1.FinPlace F, v ∉ S.Sf →
      v.valuation F (0 - (r : F)) ≤ 1 := by
    intro v hv
    rw [zero_sub, Valuation.map_neg]
    exact hr v hv
  have h2 : ∀ v : A1.FinPlace F, v ∈ S.Sf → v.valuation F (0 : F) ≤ 1 := by
    intro v hv
    simp
  rw [S.e_diag_eq A (r : F) 0 h1 h2]
  simp

/-- The product of two diagonal S-integers is annihilated by the fixed character. -/
theorem e_diag_product_eq_one [IsTotallyComplex F]
    (S : A1.SData F CE condη) (A : A1.AddCharData F) (r s : S.R) :
    S.e A (S.diag ((r : F) * (s : F))) = 1 := by
  have hrmem : (r : F) ∈ (S.Sf : Set (A1.FinPlace F)).integer F := r.property
  have hsmem : (s : F) ∈ (S.Sf : Set (A1.FinPlace F)).integer F := s.property
  have hr : ∀ v : A1.FinPlace F, v ∉ S.Sf → v.valuation F (r : F) ≤ 1 := by
    intro v hv
    change ∀ v ∉ S.Sf, v.valuation F (r : F) ≤ 1 at hrmem
    exact hrmem v hv
  have hs : ∀ v : A1.FinPlace F, v ∉ S.Sf → v.valuation F (s : F) ≤ 1 := by
    intro v hv
    change ∀ v ∉ S.Sf, v.valuation F (s : F) ≤ 1 at hsmem
    exact hsmem v hv
  have h1 : ∀ v : A1.FinPlace F, v ∉ S.Sf →
      v.valuation F (0 - ((r : F) * (s : F))) ≤ 1 := by
    intro v hv
    rw [zero_sub, Valuation.map_neg, map_mul]
    exact mul_le_one₀ (hr v hv) (bot_le) (hs v hv)
  have h2 : ∀ v : A1.FinPlace F, v ∈ S.Sf → v.valuation F (0 : F) ≤ 1 := by
    intro v hv
    simp
  rw [S.e_diag_eq A ((r : F) * (s : F)) 0 h1 h2]
  simp

/-- The projection of the S-integers to the finite S-completions is dense. -/
theorem finite_projection_dense (S : A1.SData F CE condη) :
    Dense (Set.range fun r : S.R =>
      (fun v : S.Sf => algebraMap F (v.1.adicCompletion F) (r : F))) := by
  sorry

/-- Approximate any finite S-coordinate tuple by an S-integer modulo the integral rings. -/
theorem s_integer_finite_approx (S : A1.SData F CE condη)
    (x : ∀ v : S.Sf, v.1.adicCompletion F) :
    ∃ r : S.R, ∀ v : S.Sf,
      x v - algebraMap F (v.1.adicCompletion F) (r : F) ∈
        v.1.adicCompletionIntegers F := by
  sorry

/-- The fixed character is additive on the product group. -/
theorem e_add (S : A1.SData F CE condη) (A : A1.AddCharData F) (x y : S.FS) :
    S.e A (x + y) = S.e A x * S.e A y := by
  unfold A1.SData.e
  have hfin : (∏ v : S.Sf, A.ψ v.1 ((x + y).1 v)) =
      (∏ v : S.Sf, A.ψ v.1 (x.1 v)) * ∏ v : S.Sf, A.ψ v.1 (y.1 v) := by
    calc
      (∏ v : S.Sf, A.ψ v.1 ((x + y).1 v)) =
          ∏ v : S.Sf, (A.ψ v.1 (x.1 v) * A.ψ v.1 (y.1 v)) := by
        apply Finset.prod_congr rfl
        intro v hv
        simpa using (A.ψ v.1).map_add_eq_mul (x.1 v) (y.1 v)
      _ = (∏ v : S.Sf, A.ψ v.1 (x.1 v)) *
          ∏ v : S.Sf, A.ψ v.1 (y.1 v) := by rw [Finset.prod_mul_distrib]
  have harch : (∏ w : InfinitePlace F, A1.psiC ((x + y).2 w)) =
      (∏ w : InfinitePlace F, A1.psiC (x.2 w)) *
        ∏ w : InfinitePlace F, A1.psiC (y.2 w) := by
    calc
      (∏ w : InfinitePlace F, A1.psiC ((x + y).2 w)) =
          ∏ w : InfinitePlace F, (A1.psiC (x.2 w) * A1.psiC (y.2 w)) := by
        apply Finset.prod_congr rfl
        intro w hw
        change A1.psiC (x.2 w + y.2 w) = _
        simp only [A1.psiC, Complex.add_re]
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      _ = (∏ w : InfinitePlace F, A1.psiC (x.2 w)) *
          ∏ w : InfinitePlace F, A1.psiC (y.2 w) := by rw [Finset.prod_mul_distrib]
  rw [hfin, harch]
  ring

/-- The fixed character sends a negation to the inverse value. -/
theorem e_neg (S : A1.SData F CE condη) (A : A1.AddCharData F) (x : S.FS) :
    S.e A (-x) = (S.e A x)⁻¹ := by
  have hzero : S.e A (0 : S.FS) = 1 := by
    simp [A1.SData.e, A1.psiC]
  have hadd := e_add S A x (-x)
  have hmul : S.e A x * S.e A (-x) = 1 := by
    simpa [hzero] using hadd.symm
  exact eq_inv_of_mul_eq_one_right hmul

/-- Subtracting a diagonal S-integer preserves annihilation of the diagonal S-integers. -/
theorem sub_diag_preserves_annihilator [IsTotallyComplex F]
    (D : A1.FieldData F) (S : A1.SData F CE condη) (A : A1.AddCharData F)
    (y : S.FS) (h : ∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) (t : S.R) :
    ∀ r : S.R, S.e A (S.diag (r : F) * (y - S.diag (t : F))) = 1 := by
  intro r
  rw [mul_sub, ← S.diag.map_mul, sub_eq_add_neg, e_add, e_neg, h r]
  rw [e_diag_product_eq_one S A r t]
  simp

/-- Integral finite components of an annihilator point leave the archimedean character trivial on
the embedded ordinary integers. -/
theorem arch_condition_of_integral_finite_annihilator
    (S : A1.SData F CE condη) (A : A1.AddCharData F) (y : S.FS)
    (hfin : ∀ v : S.Sf, y.1 v ∈ v.1.adicCompletionIntegers F)
    (hann : ∀ r : S.R, S.e A (S.diag (r : F) * y) = 1) :
    ∀ n : 𝓞 F,
      (∏ w : InfinitePlace F, A1.psiC (w.embedding (n : F) * y.2 w)) = 1 := by
  intro n
  let r : S.R := algebraMap (𝓞 F) S.R n
  have hr : (r : F) = (n : F) := rfl
  have hlocal (v : S.Sf) :
      A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y.1 v) = 1 := by
    apply A.integral
    apply mul_mem
    · rw [hr]
      change ((n : F) : v.1.adicCompletion F) ∈ v.1.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact v.1.valuation_le_one n
    · exact hfin v
  have h := hann r
  change (∏ v : S.Sf,
      A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y.1 v)) *
    ∏ w : InfinitePlace F, A1.psiC (w.embedding (r : F) * y.2 w) = 1 at h
  have hprod :
      (∏ v : S.Sf,
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y.1 v)) = 1 := by
    exact Finset.prod_eq_one fun v _ => hlocal v
  rw [hprod, one_mul, hr] at h
  exact h

/-- If the archimedean component vanishes, an annihilator point gives a trivial finite character on
the projected S-integers. -/
theorem finite_character_condition_of_zero_arch
    (S : A1.SData F CE condη) (A : A1.AddCharData F) (y : S.FS)
    (hann : ∀ r : S.R, S.e A (S.diag (r : F) * y) = 1)
    (harch : ∀ w : InfinitePlace F, y.2 w = 0) :
    ∀ r : S.R,
      (∏ v : S.Sf,
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y.1 v)) = 1 := by
  sorry

/-- Density and the open kernels of the finite characters extend triviality from `R` to all
finite S-components. -/
theorem finite_character_trivial_of_s_integer (S : A1.SData F CE condη)
    (A : A1.AddCharData F) (y : ∀ v : S.Sf, v.1.adicCompletion F)
    (h : ∀ r : S.R,
      (∏ v : S.Sf,
        A.ψ v.1 (algebraMap F (v.1.adicCompletion F) (r : F) * y v)) = 1) :
    ∀ x : ∀ v : S.Sf, v.1.adicCompletion F,
      (∏ v : S.Sf, A.ψ v.1 (x v * y v)) = 1 := by
  sorry

/-- Triviality on every finite tuple implies local triviality at any selected coordinate. -/
theorem finite_component_from_trivial (S : A1.SData F CE condη)
    (A : A1.AddCharData F) (y : ∀ v : S.Sf, v.1.adicCompletion F)
    (h : ∀ x : ∀ v : S.Sf, v.1.adicCompletion F,
      (∏ v : S.Sf, A.ψ v.1 (x v * y v)) = 1)
    (v : S.Sf) (a : v.1.adicCompletion F) :
    A.ψ v.1 (a * y v) = 1 := by
  sorry

/-- The field trace on a totally complex number field is twice the sum of the real parts at its
complex places. -/
theorem arch_trace_eq_two_real_sum [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  classical
  have hpairs : (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
    have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
    have hring :
        (∑ φ : F →+* ℂ, φ z) = ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
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
  rw [hpairs]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

/-- Triviality of the archimedean character on an integer argument makes its real trace pairing
an integer. -/
theorem arch_character_condition_integer [IsTotallyComplex F]
    (x : InfinitePlace F → ℂ)
    (h : ∀ n : 𝓞 F,
      (∏ w : InfinitePlace F,
        A1.psiC (w.embedding (n : F) * x w)) = 1)
    (n : 𝓞 F) :
    ∃ m : ℤ, (m : ℝ) =
      2 * ∑ w : InfinitePlace F, ((w.embedding (n : F) * x w).re) := by
  let q : ℝ := 2 * ∑ w : InfinitePlace F, ((w.embedding (n : F) * x w).re)
  have hprod :
      (∏ w : InfinitePlace F, A1.psiC (w.embedding (n : F) * x w)) =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (q : ℂ))) := by
    unfold A1.psiC
    rw [← Complex.exp_sum]
    congr 1
    calc
      (∑ w : InfinitePlace F,
          -(4 * Real.pi * Complex.I * ((w.embedding (n : F) * x w).re : ℂ))) =
          -(4 * Real.pi * Complex.I *
            ∑ w : InfinitePlace F, ((w.embedding (n : F) * x w).re : ℂ)) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      _ = -(2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)) := by
        dsimp [q]
        push_cast
        ring
  have hqexp : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (q : ℂ))) = 1 := by
    rw [← hprod]
    exact h n
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hqexp
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hmul :
      (2 * (Real.pi : ℂ) * Complex.I) * (-(q : ℂ)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
    calc
      (2 * (Real.pi : ℂ) * Complex.I) * (-(q : ℂ)) =
          -(2 * (Real.pi : ℂ) * Complex.I * (q : ℂ)) := by ring
      _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hk
      _ = (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by ring
  have hq : -(q : ℂ) = (k : ℂ) := mul_left_cancel₀ hc hmul
  have hq' : (q : ℂ) = ((-k : ℤ) : ℂ) := by
    have h := congrArg (fun z : ℂ => -z) hq
    simpa using h
  have hqReal : q = ((-k : ℤ) : ℝ) := by exact_mod_cast hq'
  exact ⟨-k, by simpa [q] using hqReal.symm⟩

/-- The chosen complex-place coordinates carry the real basis induced by the Minkowski lattice
basis of the ring of integers. -/
private def archComplexPlaceLinearEquiv [IsTotallyComplex F] :
    mixedEmbedding.mixedSpace F ≃ₗ[ℝ] (InfinitePlace F → ℂ) where
  toFun x w := x.2 ⟨w, IsTotallyComplex.isComplex w⟩
  invFun x := (fun w => False.elim
    ((not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2),
    fun w => x w.1)
  left_inv x := by
    apply Prod.ext
    · funext w
      exact ((not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w.1)) w.2).elim
    · funext w
      rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

theorem arch_embedding_real_basis [IsTotallyComplex F] :
    ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) ℝ (InfinitePlace F → ℂ),
      ∀ i, b i = fun w => w.embedding (NumberField.integralBasis F i) := by
  let b := (mixedEmbedding.latticeBasis F).map (archComplexPlaceLinearEquiv (F := F))
  refine ⟨b, ?_⟩
  intro i
  change archComplexPlaceLinearEquiv (mixedEmbedding.latticeBasis F i) = _
  rw [mixedEmbedding.latticeBasis_apply]
  rfl

/-- The archimedean annihilator of the integral lattice is the embedded inverse trace-dual
lattice; all its elements lie in the S-integers because the different is supported in `S`. -/
theorem arch_trace_dual_lattice [IsTotallyComplex F]
    (D : A1.FieldData F) (S : A1.SData F CE condη)
    (x : InfinitePlace F → ℂ)
    (h : ∀ n : 𝓞 F,
      (∏ w : InfinitePlace F,
        A1.psiC (w.embedding (n : F) * x w)) = 1) :
    ∃ t : F, (∀ w : InfinitePlace F, w.embedding t = x w) ∧ t ∈ S.R := by
  sorry

/-- The local additive character has no annihilator beyond zero. -/
theorem psi_local_nondegenerate [IsTotallyComplex F]
    (D : A1.FieldData F) (S : A1.SData F CE condη) (A : A1.AddCharData F)
    (v : S.Sf) (y : v.1.adicCompletion F)
    (h : ∀ x : v.1.adicCompletion F, A.ψ v.1 (x * y) = 1) :
    y = 0 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_dual_p
