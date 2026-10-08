import ArtinPrimitiveRoots.A1.AddChar
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-! Core interfaces for the additive annihilator proof. -/

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain Module
open scoped Classical
open scoped ComplexConjugate
open scoped nonZeroDivisors
open scoped Topology

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
  classical
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨V, hV, hVU⟩ := (isOpen_pi_iff'.mp hU) x hxU
  let a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F :=
    ⟨(fun v => if hv : v ∈ S.Sf then x ⟨v, hv⟩ else 0), by
      have houtside : ∀ᶠ v : A1.FinPlace F in Filter.cofinite, v ∉ S.Sf := by
        apply Filter.eventually_cofinite.mpr
        simpa using S.Sf.finite_toSet
      filter_upwards [houtside] with v hv
      simp [hv]⟩
  have ha_apply (v : A1.FinPlace F) :
      a v = (if hv : v ∈ S.Sf then x ⟨v, hv⟩ else 0) := rfl
  have hT (v : S.Sf) :
      (fun z : v.1.adicCompletionIntegers F => x v + z) ⁻¹' V v ∈ 𝓝 0 := by
    have h0 : (fun z : v.1.adicCompletionIntegers F => x v + z) 0 ∈ V v := by
      simpa using (hV v).2
    exact (continuous_const.add continuous_subtype_val).continuousAt.preimage_mem_nhds
      ((hV v).1.mem_nhds h0)
  let nLoc : S.Sf → ℕ := fun v =>
    (v.1.exists_maximalIdeal_pow_subset_of_mem_nhds (K := F) (hT v)).choose
  have hnLoc (v : S.Sf) :
      ((IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers F) ^ nLoc v :
        Ideal (v.1.adicCompletionIntegers F)) : Set (v.1.adicCompletionIntegers F)) ⊆
          (fun z : v.1.adicCompletionIntegers F => x v + z) ⁻¹' V v :=
    (v.1.exists_maximalIdeal_pow_subset_of_mem_nhds (K := F) (hT v)).choose_spec
  let nA : A1.FinPlace F → ℕ := fun v => if hv : v ∈ S.Sf then nLoc ⟨v, hv⟩ else 0
  obtain ⟨r, hnear, houter⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_forall_valued_sub_le_and_forall_valued_sub_le_one
      a S.Sf nA
  have hrR : r ∈ S.R := by
    change ∀ v : A1.FinPlace F, v ∉ S.Sf → v.valuation F r ≤ 1
    intro v hv
    have hav : a v = 0 := by
      rw [ha_apply]
      simp [hv]
    have h := houter v
    rw [hav, sub_zero] at h
    change Valued.v (r : v.adicCompletion F) ≤ 1 at h
    rw [v.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hcoords : ∀ v : S.Sf,
      algebraMap F (v.1.adicCompletion F) r ∈ V v := by
    intro v
    have hclose : Valued.v
        (algebraMap F (v.1.adicCompletion F) r - x v) ≤
          WithZero.exp (-(nLoc v : ℤ)) := by
      have h := hnear v.1 v.2
      have ha : a v.1 = x v := by
        rw [ha_apply]
        simp [v.2]
      have hnAeq : nA v.1 = nLoc v := by simp [nA, v.2]
      rw [ha, hnAeq] at h
      exact h
    let d : v.1.adicCompletionIntegers F :=
      ⟨algebraMap F (v.1.adicCompletion F) r - x v, by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hclose.trans (WithZero.exp_le_one_iff.mpr (by omega))⟩
    have hdPow : d ∈ IsLocalRing.maximalIdeal (v.1.adicCompletionIntegers F) ^ nLoc v := by
      rw [v.1.mem_maximalIdeal_pow_iff (K := F)]
      simpa [d] using hclose
    have hdV := hnLoc v hdPow
    change x v + (d : v.1.adicCompletion F) ∈ V v at hdV
    simpa [d] using hdV
  have hrU : (fun v : S.Sf => algebraMap F (v.1.adicCompletion F) r) ∈ U := by
    apply hVU
    intro v hv
    exact hcoords v
  let rR : S.R := ⟨r, hrR⟩
  refine ⟨(fun v : S.Sf => algebraMap F (v.1.adicCompletion F) (rR : F)), ?_⟩
  exact ⟨by simpa [rR] using hrU, ⟨rR, rfl⟩⟩

/-- Approximate any finite S-coordinate tuple by an S-integer modulo the integral rings. -/
theorem s_integer_finite_approx (S : A1.SData F CE condη)
    (x : ∀ v : S.Sf, v.1.adicCompletion F) :
    ∃ r : S.R, ∀ v : S.Sf,
      x v - algebraMap F (v.1.adicCompletion F) (r : F) ∈
        v.1.adicCompletionIntegers F := by
  classical
  let V : ∀ v : S.Sf, Set (v.1.adicCompletion F) := fun v =>
    {z | x v - z ∈ (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))}
  let U : Set (∀ v : S.Sf, v.1.adicCompletion F) := {z | ∀ v, z v ∈ V v}
  have hU : IsOpen U := by
    rw [isOpen_pi_iff']
    intro z hz
    refine ⟨V, ?_⟩
    constructor
    · intro v
      refine ⟨?_, hz v⟩
      exact (Valued.isOpen_valuationSubring _).preimage
        (continuous_const.sub continuous_id)
    · intro z' hz' v
      exact hz' v (Set.mem_univ _)
  have hUne : U.Nonempty := by
    refine ⟨x, ?_⟩
    simp [U, V]
  obtain ⟨z, hzU, hzRange⟩ :=
    (dense_iff_inter_open.mp (finite_projection_dense S)) U hU hUne
  rcases hzRange with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  intro v
  have hz := hzU v
  change x v - algebraMap F (v.1.adicCompletion F) (r : F) ∈
    (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))
  rw [← hr] at hz
  exact hz

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

/-- Integer values of the real trace pairing reconstruct a field element with the prescribed
archimedean coordinates. -/
theorem arch_trace_dual_element [IsTotallyComplex F]
    (D : A1.FieldData F) (x : InfinitePlace F → ℂ)
    (h : ∀ n : 𝓞 F,
      (∏ w : InfinitePlace F,
        A1.psiC (w.embedding (n : F) * x w)) = 1) :
    ∃ t : F, (∀ w : InfinitePlace F, w.embedding t = x w) ∧
      ∀ n : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((n : F) * t) = m := by
  classical
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let bQ : Basis I ℚ F := NumberField.integralBasis F
  obtain ⟨bR, hbR⟩ := arch_embedding_real_basis (F := F)
  let m : I → ℤ := fun i => Classical.choose
    (arch_character_condition_integer (F := F) x h (RingOfIntegers.basis F i))
  have hm (i : I) : (m i : ℝ) =
      2 * ∑ w : InfinitePlace F,
        ((w.embedding (NumberField.integralBasis F i) * x w).re) := by
    simpa [m, NumberField.integralBasis_apply] using
      (Classical.choose_spec
        (arch_character_condition_integer (F := F) x h (RingOfIntegers.basis F i)))
  let l := bQ.traceDual.equivFun
  have hl (u : F) (i : I) : l u i = Algebra.trace ℚ F (u * bQ i) := by
    simp [l, Basis.equivFun_apply, Basis.traceDual_repr_apply, Algebra.traceForm_apply]
  let mq : I → ℚ := fun i => (m i : ℚ)
  let t : F := l.symm mq
  have htracecoord (i : I) :
      Algebra.trace ℚ F (NumberField.integralBasis F i * t) = (m i : ℚ) := by
    calc
      Algebra.trace ℚ F (NumberField.integralBasis F i * t) =
          Algebra.trace ℚ F (t * NumberField.integralBasis F i) := by congr 1 <;> ring
      _ = l t i := (hl t i).symm
      _ = (m i : ℚ) := by
        change (l (l.symm mq)) i = _
        rw [l.apply_symm_apply]
  have htraceReal (i : I) :
      (Algebra.trace ℚ F (NumberField.integralBasis F i * t) : ℝ) = (m i : ℝ) := by
    exact_mod_cast htracecoord i
  have htraceFormula (z : F) :
      (Algebra.trace ℚ F z : ℝ) =
        2 * ∑ w : InfinitePlace F, ((w.embedding z).re) := by
    exact_mod_cast arch_trace_eq_two_real_sum (F := F) z
  have hpairT (i : I) :
      2 * ∑ w : InfinitePlace F,
        ((w.embedding (NumberField.integralBasis F i) * w.embedding t).re) =
          (m i : ℝ) := by
    calc
      2 * ∑ w : InfinitePlace F,
          ((w.embedding (NumberField.integralBasis F i) * w.embedding t).re) =
          2 * ∑ w : InfinitePlace F,
            ((w.embedding (NumberField.integralBasis F i * t)).re) := by
              congr 1
              apply Finset.sum_congr rfl
              intro w hw
              simp only [map_mul]
      _ = (Algebra.trace ℚ F (NumberField.integralBasis F i * t) : ℝ) :=
        (htraceFormula _).symm
      _ = (m i : ℝ) := htraceReal i
  let pairing (z : InfinitePlace F → ℂ) :
      (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ := {
    toFun := fun y => 2 * ∑ w : InfinitePlace F, ((y w * z w).re)
    map_add' := by
      intro y y'
      simp only [Pi.add_apply, add_mul, Complex.add_re]
      rw [Finset.sum_add_distrib]
      ring
    map_smul' := by
      intro c y
      simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
      rw [← Finset.mul_sum]
      simp only [RingHom.id_apply]
      ring
  }
  let δ : InfinitePlace F → ℂ := fun w => x w - w.embedding t
  let L := pairing δ
  have hLbasis (i : I) : L (bR i) = 0 := by
    rw [show bR i = fun w => w.embedding (NumberField.integralBasis F i) from hbR i]
    change 2 * ∑ w : InfinitePlace F,
      ((w.embedding (NumberField.integralBasis F i) *
        (x w - w.embedding t)).re) = 0
    simp only [mul_sub, Complex.sub_re]
    rw [Finset.sum_sub_distrib]
    have hX := (hm i).symm
    have hT := hpairT i
    linarith
  have hLzero (y : InfinitePlace F → ℂ) : L y = 0 := by
    calc
      L y = L (∑ i : I, bR.repr y i • bR i) :=
        congrArg L (bR.sum_repr y).symm
      _ = ∑ i : I, L (bR.repr y i • bR i) := by rw [map_sum]
      _ = 0 := by simp [hLbasis]
  have hnormsum : 2 * ∑ w : InfinitePlace F, Complex.normSq (δ w) = 0 := by
    have hz := hLzero (fun w => conj (δ w))
    change 2 * ∑ w : InfinitePlace F,
      ((conj (δ w) * δ w).re) = 0 at hz
    have hterm (w : InfinitePlace F) :
        (conj (δ w) * δ w).re = Complex.normSq (δ w) := by
      rw [← Complex.normSq_eq_conj_mul_self]
      simp
    simpa only [hterm] using hz
  have hnormzero (w : InfinitePlace F) : Complex.normSq (δ w) = 0 := by
    have hsum : (∑ v : InfinitePlace F, Complex.normSq (δ v)) = 0 := by
      nlinarith [hnormsum]
    have hle : Complex.normSq (δ w) ≤
        ∑ v : InfinitePlace F, Complex.normSq (δ v) :=
      Finset.single_le_sum (fun v hv => Complex.normSq_nonneg (δ v)) (Finset.mem_univ w)
    rw [hsum] at hle
    exact le_antisymm hle (Complex.normSq_nonneg _)
  have hEmbed (w : InfinitePlace F) : w.embedding t = x w := by
    have hd : δ w = 0 := Complex.normSq_eq_zero.mp (hnormzero w)
    exact (sub_eq_zero.mp hd).symm
  refine ⟨t, hEmbed, ?_⟩
  intro n
  obtain ⟨m', hm'⟩ := arch_character_condition_integer (F := F) x h n
  have htraceR := htraceFormula ((n : F) * t)
  have hcast : (m' : ℝ) = (Algebra.trace ℚ F ((n : F) * t) : ℝ) := by
    have hx : x = fun w : InfinitePlace F => w.embedding t :=
      funext fun w => (hEmbed w).symm
    rw [hx] at hm'
    have htraceR' : (Algebra.trace ℚ F ((n : F) * t) : ℝ) =
        2 * ∑ w : InfinitePlace F,
          ((w.embedding (n : F) * w.embedding t).re) := by
      simpa only [map_mul] using htraceR
    exact hm'.trans htraceR'.symm
  exact ⟨m', by exact_mod_cast hcast.symm⟩

private theorem a1_spanSingleton_div_count (v : A1.FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private theorem a1_spanSingleton_intValuation_count (v : A1.FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private theorem a1_spanSingleton_count (v : A1.FinPlace F) (z : F)
    (hz : z ≠ 0) :
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
        -WithZero.log (v.valuation F z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : v.valuation F z = v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    a1_spanSingleton_div_count v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    a1_spanSingleton_intValuation_count v n hn,
    a1_spanSingleton_intValuation_count v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn)
      (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

/-- Integral trace pairing against the ring of integers places an element in the codifferent;
away from the support of the different it is integral. -/
theorem trace_integral_mem_S_R (S : A1.SData F CE condη) (t : F)
    (h : ∀ n : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F ((n : F) * t) = m) :
    t ∈ S.R := by
  classical
  have hdual : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp ha
    obtain ⟨m, hm⟩ := h n
    have htr : Algebra.trace ℚ F (t * a) = (m : ℚ) := by
      rw [← hn, mul_comm]
      exact hm
    refine ⟨m, ?_⟩
    exact_mod_cast htr.symm
  let codifferent : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)
  have htCod : t ∈ (codifferent : Submodule (𝓞 F) F) := by
    simpa [codifferent, FractionalIdeal.coe_dual_one] using hdual
  let D := differentIdeal ℤ (𝓞 F)
  have hD0 : D ≠ ⊥ := differentIdeal_ne_bot
  have hDcod : (D : FractionalIdeal (𝓞 F)⁰ F) = codifferent⁻¹ := by
    simpa [D, codifferent] using (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  change ∀ v : A1.FinPlace F, v ∉ S.Sf → v.valuation F t ≤ 1
  intro v hvS
  by_cases ht0 : t = 0
  · simp [ht0]
  have hDnot : ¬ D ≤ v.asIdeal := by
    intro hle
    exact hvS (S.different_mem v hle)
  have hDcount : FractionalIdeal.count F v (D : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
    rw [FractionalIdeal.count_coe F v hD0]
    have hcount : (Associates.mk v.asIdeal).count (Associates.mk D).factors = 0 := by
      by_contra hcount
      have hdvd := (Associates.count_ne_zero_iff_dvd hD0 v.irreducible).mp hcount
      exact hDnot (Ideal.dvd_iff_le.mp hdvd)
    exact_mod_cast hcount
  have hcodcount : FractionalIdeal.count F v codifferent = 0 := by
    rw [hDcod, FractionalIdeal.count_inv] at hDcount
    linarith
  have hspanle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) t ≤
      codifferent := FractionalIdeal.spanSingleton_le_iff_mem.mpr htCod
  have hcountle := FractionalIdeal.count_mono F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ht0) hspanle
  have hcountt := a1_spanSingleton_count v t ht0
  have hlogle : WithZero.log (v.valuation F t) ≤ 0 := by
    rw [hcountt] at hcountle
    linarith
  simpa using (WithZero.log_le_iff_le_exp
    ((v.valuation F).ne_zero_iff.mpr ht0)).mp hlogle

/-- The archimedean annihilator of the integral lattice is the embedded inverse trace-dual
lattice; all its elements lie in the S-integers because the different is supported in `S`. -/
theorem arch_trace_dual_lattice [IsTotallyComplex F]
    (D : A1.FieldData F) (S : A1.SData F CE condη)
    (x : InfinitePlace F → ℂ)
    (h : ∀ n : 𝓞 F,
      (∏ w : InfinitePlace F,
        A1.psiC (w.embedding (n : F) * x w)) = 1) :
    ∃ t : F, (∀ w : InfinitePlace F, w.embedding t = x w) ∧ t ∈ S.R := by
  obtain ⟨t, htArch, htrace⟩ := arch_trace_dual_element D x h
  exact ⟨t, htArch, trace_integral_mem_S_R S t htrace⟩

/-- The local additive character has no annihilator beyond zero. -/
theorem psi_local_nondegenerate [IsTotallyComplex F]
    (D : A1.FieldData F) (S : A1.SData F CE condη) (A : A1.AddCharData F)
    (v : S.Sf) (y : v.1.adicCompletion F)
    (h : ∀ x : v.1.adicCompletion F, A.ψ v.1 (x * y) = 1) :
    y = 0 := by
  sorry

end ArtinPrimitiveRoots.Proofs.a1_dual_p
