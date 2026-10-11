import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs

/-!
# A1-FOURIER part `a1_fourier_e_basic` (IMPL)

Basic properties of the global character `S.e A` on `F_S`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open Filter
open scoped Classical Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem finitePsi_isLocallyConstant_aux (v : FinPlace F) (A : AddCharData F) :
    IsLocallyConstant (A.ψ v) := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  have hOopen : IsOpen O := by
    change IsOpen (v.adicCompletionIntegers F : Set K)
    exact Valued.isOpen_valuationSubring K
  apply (IsLocallyConstant.iff_exists_open (A.ψ v)).2
  intro x
  let U : Set K := {y | y - x ∈ O}
  have hUopen : IsOpen U := by
    apply hOopen.preimage
    fun_prop
  refine ⟨U, hUopen, ?_, ?_⟩
  · change x - x ∈ O
    simp [O]
  · intro y hy
    have hψ := A.integral v (y - x) hy
    calc
      A.ψ v y = A.ψ v (x + (y - x)) := by congr 1; abel
      _ = A.ψ v x * A.ψ v (y - x) := AddChar.map_add_eq_mul (A.ψ v) x (y - x)
      _ = A.ψ v x := by rw [hψ]; simp

private theorem psiC_add_aux (z w : ℂ) : psiC (z + w) = psiC z * psiC w := by
  unfold psiC
  have harg :
      -(4 * Real.pi * Complex.I * ((z + w).re : ℂ)) =
        -(4 * Real.pi * Complex.I * (z.re : ℂ)) +
          -(4 * Real.pi * Complex.I * (w.re : ℂ)) := by
    rw [Complex.add_re, Complex.ofReal_add]
    ring
  rw [harg, Complex.exp_add]

private theorem psiC_continuous_aux : Continuous psiC := by
  unfold psiC
  fun_prop

private theorem psiC_norm_one_aux (z : ℂ) : ‖psiC z‖ = 1 := by
  unfold psiC
  rw [Complex.norm_exp]
  have hre : (-(4 * Real.pi * Complex.I * (z.re : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero]

private theorem psiC_zero_aux : psiC 0 = 1 := by
  unfold psiC
  simp

private theorem finitePsi_norm_one_aux (v : FinPlace F) (A : AddCharData F)
    (x : v.adicCompletion F) : ‖A.ψ v x‖ = 1 := by
  haveI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  let p : ℕ := Ideal.absNorm (Ideal.under ℤ v.asIdeal)
  have hp : Nat.Prime p := by
    dsimp [p]
    exact Nat.absNorm_under_prime v.asIdeal
  have hpO : (p : 𝓞 F) ∈ v.asIdeal := by
    dsimp [p]
    exact Int.absNorm_under_mem v.asIdeal
  let q : v.adicCompletion F := (p : F)
  have hqval : Valued.v q < 1 := by
    change Valued.v ((p : F) : v.adicCompletion F) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
    exact (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 hpO
  have hqpow : Filter.Tendsto (fun k : ℕ => q ^ k) Filter.atTop (𝓝 (0 : v.adicCompletion F)) :=
    Valued.tendsto_zero_pow_of_v_lt_one hqval
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hevent : ∀ᶠ k : ℕ in Filter.atTop,
      q ^ k * x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    have ht := hqpow.mul_const x
    have hmem : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈
        𝓝 ((0 : v.adicCompletion F) * x) := by
      exact hOopen.mem_nhds (by simp)
    exact ht.eventually_mem hmem
  obtain ⟨k, hk⟩ := Filter.Eventually.exists hevent
  have hcast : (p : v.adicCompletion F) = q := by
    dsimp [q]
    exact (map_natCast (algebraMap F (v.adicCompletion F)) p).symm
  have hsmul : (p ^ k : ℕ) • x = q ^ k * x := by
    calc
      (p ^ k : ℕ) • x = (p ^ k : v.adicCompletion F) * x := by
        simp [nsmul_eq_mul]
      _ = q ^ k * x := by
        congr 1
        rw [hcast]
  have hchar : (A.ψ v x) ^ (p ^ k) = 1 := by
    calc
      (A.ψ v x) ^ (p ^ k) = A.ψ v ((p ^ k : ℕ) • x) :=
        (A.ψ v).map_nsmul_eq_pow (p ^ k) x |>.symm
      _ = 1 := A.integral v _ (by rw [hsmul]; exact hk)
  exact Complex.norm_eq_one_of_pow_eq_one hchar (pow_ne_zero _ hp.ne_zero)

private theorem e_continuous_aux (S : SData F CE condη) (A : AddCharData F) :
    Continuous (S.e A) := by
  unfold SData.e
  apply Continuous.mul
  · apply continuous_finsetProd Finset.univ
    intro v _
    exact (finitePsi_isLocallyConstant_aux v.1 A).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  · apply continuous_finsetProd Finset.univ
    intro w _
    exact psiC_continuous_aux.comp ((continuous_apply w).comp continuous_snd)

private theorem e_norm_aux (S : SData F CE condη) (A : AddCharData F)
    (x : S.FS) : ‖S.e A x‖ = 1 := by
  unfold SData.e
  have hfin : ‖∏ v : S.Sf, A.ψ v.1 (x.1 v)‖ = 1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro v _
    exact finitePsi_norm_one_aux v.1 A (x.1 v)
  have harch : ‖∏ w : InfinitePlace F, psiC (x.2 w)‖ = 1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro w _
    exact psiC_norm_one_aux (x.2 w)
  rw [norm_mul, hfin, harch, mul_one]

private theorem e_add_aux (S : SData F CE condη) (A : AddCharData F)
    (x y : S.FS) : S.e A (x + y) = S.e A x * S.e A y := by
  unfold SData.e
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, AddChar.map_add_eq_mul]
  simp_rw [psiC_add_aux]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

private theorem psiC_eighth_aux : psiC (1 / 8 : ℂ) = -Complex.I := by
  have hre : ((1 / 8 : ℂ).re = (1 / 8 : ℝ)) := by simp
  have harg : -(4 * Real.pi * Complex.I * (((1 / 8 : ℂ).re : ℝ) : ℂ)) =
      -Real.pi / 2 * Complex.I := by
    rw [hre]
    push_cast
    ring
  have heq : psiC (1 / 8 : ℂ) = Complex.exp (-Real.pi / 2 * Complex.I) := by
    unfold psiC
    rw [harg]
  rw [heq]
  exact Complex.exp_neg_pi_div_two_mul_I

private theorem neg_I_ne_one_aux : (-Complex.I : ℂ) ≠ 1 := by
  intro h
  have h2 := congrArg Complex.im h
  simp at h2

private theorem e_nontrivial_aux (S : SData F CE condη) (A : AddCharData F) :
    ∃ z : S.FS, S.e A z ≠ 1 := by
  classical
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let z : S.FS := ((fun _ => 0), (fun w => if w = w₀ then (1 / 8 : ℂ) else 0))
  refine ⟨z, ?_⟩
  have hfin : (∏ v : S.Sf, A.ψ v.1 (z.1 v)) = 1 := by
    apply Finset.prod_eq_one
    intro v _
    simp [z]
  have harch : (∏ w : InfinitePlace F, psiC (z.2 w)) = psiC (1 / 8 : ℂ) := by
    have h := Fintype.prod_eq_single w₀
      (f := fun w => psiC (z.2 w))
      (fun b hb => by simp [z, hb, psiC_zero_aux])
    simpa [z] using h
  have he : S.e A z = psiC (1 / 8 : ℂ) := by
    unfold SData.e
    rw [hfin, harch, one_mul]
  rw [he, psiC_eighth_aux]
  exact neg_I_ne_one_aux

/-- Basic properties of `e = ∏_{v∈S} ψ_v` on `F_S`: continuity (each `A.ψ v` is trivial on the
open subgroup `O_v` by `AddCharData.integral`, hence locally constant; `psiC` is continuous),
unit norm, additivity, and nontriviality (e.g. `z = (0, Pi.single w₀ (1/8))` gives
`psiC (1/8) = exp(-πi/2) = -i`; `InfinitePlace F` is nonempty).

Compare the private
`globalAddChar_continuous` in `A2/Proofs/A2_WEIGHTS/Exist.lean:314` (copy, do not import).
Used by: `a1_fourier_orthogonality`, `a1_fourier_uniqueness`, `a1_fourier_poisson_abstract`. -/
theorem a1_fourier_e_basic (S : SData F CE condη) (A : AddCharData F) :
    Continuous (S.e A) ∧ (∀ x : S.FS, ‖S.e A x‖ = 1) ∧
      (∀ x y : S.FS, S.e A (x + y) = S.e A x * S.e A y) ∧ ∃ z : S.FS, S.e A z ≠ 1 := by
  refine ⟨e_continuous_aux S A, e_norm_aux S A, e_add_aux S A, e_nontrivial_aux S A⟩

end ArtinPrimitiveRoots.A1
