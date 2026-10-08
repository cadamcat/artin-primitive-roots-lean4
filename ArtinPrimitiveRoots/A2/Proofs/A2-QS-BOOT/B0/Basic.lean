import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».Block
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0Slice
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3.Local

/-!
# B0 helpers: trivial energy bounds, empty matrices, residual columns

* `qsHighNorm` vanishes with no rows (`M < 1/3`) or no columns (`N < 1`);
* the trivial bound `E(cols, z) ≤ #cols · W_max · #{N a ≤ 5M/2} · ‖z‖²` and the same majorant for
  `qsHigh` of a character of modulus `≤ 1`;
* residual columns of a gcd block lie in one ray class; `qsBadRad · g` is squarefree.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2.QSB0

open QSC2 QSC3

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-! ### Empty matrices -/

theorem operator_norm_eq_zero_of_isEmpty_rows {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [IsEmpty ι] (A : Matrix ι κ ℂ) :
    ‖OAI.FiniteSieveOperator.operator A‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_
  have : OAI.FiniteSieveOperator.operator A x = 0 := Subsingleton.elim _ _
  rw [this, norm_zero]; positivity

theorem operator_norm_eq_zero_of_isEmpty_cols {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [IsEmpty κ] (A : Matrix ι κ ℂ) :
    ‖OAI.FiniteSieveOperator.operator A‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => ?_
  have : x = 0 := Subsingleton.elim _ _
  rw [this, map_zero, norm_zero]; positivity

theorem qsHighRows_eq_empty {M κ : ℝ} (hM : M < 1 / 3) : qsHighRows m qS M κ = ∅ := by
  classical
  ext a
  simp only [qsHighRows, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    Finset.notMem_empty, iff_false, not_and]
  intro ha hcop _
  have h0 : ⌊3 * M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
  rw [h0, Nat.le_zero, Ideal.absNorm_eq_zero_iff] at ha
  exact absurd ha hcop.1

theorem qsHighNorm_eq_zero_of_small_M (F : QSFamily m qS) (W : ℝ → ℝ) {M N κ : ℝ}
    (hM : M < 1 / 3) : qsHighNorm F W M N κ = 0 := by
  classical
  have hE : IsEmpty (qsHighRows m qS M κ) := by
    rw [qsHighRows_eq_empty hM]; infer_instance
  unfold qsHighNorm
  rw [operator_norm_eq_zero_of_isEmpty_rows]
  norm_num

theorem qsUpTo_eq_empty {N : ℝ} (hN : N < 1) : qsUpTo m qS N = ∅ := by
  classical
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  rw [mem_qsUpTo] at hc
  have := one_le_qsN (ne_bot_of_QSAdm hc.1)
  linarith [hc.2]

theorem qsHighNorm_eq_zero_of_small_N (F : QSFamily m qS) (W : ℝ → ℝ) {M N κ : ℝ}
    (hN : N < 1) : qsHighNorm F W M N κ = 0 := by
  classical
  have hE : IsEmpty (qsUpTo m qS N) := by
    rw [qsUpTo_eq_empty hN]; infer_instance
  unfold qsHighNorm
  rw [operator_norm_eq_zero_of_isEmpty_cols]
  norm_num

/-! ### The cap weight is bounded -/

theorem capWeight_bounded {W : ℝ → ℝ} (hW : IsCapWeight W) :
    ∃ Wm : ℝ, 0 ≤ Wm ∧ ∀ x : ℝ, 0 ≤ x → W x ≤ Wm := by
  have hc : Continuous W := by
    have h1 : Continuous (fun x : ℝ => (W x : ℂ)) := hW.1.1.continuous
    have : W = fun x => ((W x : ℂ)).re := by funext x; simp
    rw [this]; exact Complex.continuous_re.comp h1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (0 : ℝ) (5/2))
    hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  by_cases h : x ≤ 5/2
  · have := hB x ⟨hx, h⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  · rw [hW.2.2.2 x (by linarith)]; exact le_max_right _ _

/-! ### Row counts -/

/-- The nonzero ideals of norm `≤ ⌊X⌋`, as a finset of the subtype. -/
def rowSet (K : Type) [Field K] [NumberField K] (X : ℝ) : Finset {I : Ideal (𝓞 K) // I ≠ ⊥} :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.subtype (fun I => I ≠ ⊥)

theorem card_rowSet_le (X : ℝ) :
    (rowSet K X).card ≤ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊).toFinset.card := by
  classical
  unfold rowSet
  rw [Finset.card_subtype]
  exact Finset.card_filter_le _ _

theorem mem_rowSet_of_le {X : ℝ} {a : {I : Ideal (𝓞 K) // I ≠ ⊥}}
    (h : qsN a.1 ≤ X) : a ∈ rowSet K X := by
  classical
  unfold rowSet
  rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact Nat.le_floor h

/-- A nonnegative function on nonzero ideals supported on `N a ≤ X` and bounded by `B`. -/
theorem tsum_le_of_support {f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℝ} {X B : ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ B) (hsupp : ∀ a, X < qsN a.1 → f a = 0) :
    Summable f ∧ ∑' a, f a ≤ (rowSet K X).card * B := by
  classical
  have hzero : ∀ a ∉ rowSet K X, f a = 0 := by
    intro a ha
    refine hsupp a ?_
    by_contra h
    exact ha (mem_rowSet_of_le (not_lt.mp h))
  refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
  rw [tsum_eq_sum hzero]
  calc ∑ a ∈ rowSet K X, f a ≤ ∑ a ∈ rowSet K X, B := Finset.sum_le_sum fun a _ => hfB a
    _ = (rowSet K X).card * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `‖Σ_{c} z_c χ_c(a)‖² ≤ #cols Σ ‖z_c‖²` for admissible columns. -/
theorem norm_sum_sq_le (F : QSFamily m qS) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) (a : Ideal (𝓞 K)) :
    ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 ≤
      (cols.card : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  have h1 : ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ≤ ∑ c ∈ cols, ‖z c‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_idealValue_le_one F (hcols c hc) a)
  have h2 : (∑ c ∈ cols, ‖z c‖) ^ 2 ≤ (cols.card : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq cols (fun _ => (1 : ℝ)) (fun c => ‖z c‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
    exact this
  calc ‖∑ c ∈ cols, z c * (F.character c).idealValue a‖ ^ 2 ≤ (∑ c ∈ cols, ‖z c‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Trivial energy bound. -/
theorem energy_trivial (F : QSFamily m qS) {W : ℝ → ℝ} (hW : IsCapWeight W) {Wm : ℝ}
    (hWm : ∀ x : ℝ, 0 ≤ x → W x ≤ Wm) {M κ : ℝ} (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) :
    qsHighEnergy F W M κ cols z ≤
      (rowSet K (5 / 2 * M)).card * (Wm * ((cols.card : ℝ) * ∑ c ∈ cols, ‖z c‖ ^ 2)) := by
  classical
  have hWm0 : 0 ≤ Wm := le_trans (hW.2.1 0) (hWm 0 le_rfl)
  unfold qsHighEnergy
  refine (tsum_le_of_support (X := 5 / 2 * M) (fun a => ?_) (fun a => ?_) (fun a ha => ?_)).2
  · split_ifs
    · exact mul_nonneg (hW.2.1 _) (sq_nonneg _)
    · exact le_rfl
  · split_ifs
    · refine mul_le_mul (hWm _ (div_nonneg (Nat.cast_nonneg _) hM.le))
        (norm_sum_sq_le F cols hcols z a.1) (sq_nonneg _) hWm0
    · positivity
  · split_ifs
    · rw [hW.2.2.2 _ (by rw [le_div_iff₀ hM]; linarith), zero_mul]
    · rfl

/-! ### Residual columns -/

theorem rayClass_mul' (I J : Ideal (𝓞 K)) (hI : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I)
    (hJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m J)
    (hIJ : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m (I * J)) :
    ArtinPrimitiveRoots.Hecke.rayClass m (I * J) hIJ =
      ArtinPrimitiveRoots.Hecke.rayClass m I hI * ArtinPrimitiveRoots.Hecke.rayClass m J hJ := by
  rcases hI with ⟨hI0, hI'⟩
  rcases hJ with ⟨hJ0, hJ'⟩
  rcases hIJ with ⟨hIJ0, hIJ'⟩
  change QuotientGroup.mk (⟨ArtinPrimitiveRoots.Hecke.idealUnit (I * J) hIJ0, hIJ'⟩ :
      rayClassPrimeToIdeals m) =
    QuotientGroup.mk (⟨ArtinPrimitiveRoots.Hecke.idealUnit I hI0, hI'⟩ : rayClassPrimeToIdeals m) *
      QuotientGroup.mk (⟨ArtinPrimitiveRoots.Hecke.idealUnit J hJ0, hJ'⟩ :
        rayClassPrimeToIdeals m)
  rw [← QuotientGroup.mk_mul]
  congr 1
  refine Subtype.ext ?_
  refine Units.ext ?_
  simp [ArtinPrimitiveRoots.Hecke.idealUnit, FractionalIdeal.coeIdeal_mul]

end ArtinPrimitiveRoots.A2.QSB0
