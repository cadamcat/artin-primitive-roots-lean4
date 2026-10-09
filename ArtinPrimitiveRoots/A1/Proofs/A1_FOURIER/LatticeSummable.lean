import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# A1-FOURIER part `a1_fourier_lattice_summable` (IMPL)

Lattice-point summability for S-integers whose finite components lie in a compact set.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem mixed_norm_le_arch (x : F) :
    ‖NumberField.mixedEmbedding F x‖ ≤ ‖fun w : InfinitePlace F => w.embedding x‖ := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro w
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal,
      InfinitePlace.norm_embedding_of_isReal, ← InfinitePlace.norm_embedding_eq]
    exact norm_le_pi_norm (fun w : InfinitePlace F => w.embedding x) w.1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro w
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
    exact norm_le_pi_norm (fun w : InfinitePlace F => w.embedding x) w.1

private theorem integerLattice_summable_one_add (r : ℝ)
    (hr : (Module.finrank ℚ F : ℝ) < r)
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable (fun z : NumberField.mixedEmbedding.integerLattice F =>
      (1 + ‖(z : NumberField.mixedEmbedding.mixedSpace F) - x‖) ^ (-r)) := by
  let L := NumberField.mixedEmbedding.integerLattice F
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.cast_nonneg _) hr
  have hrank : Module.finrank ℤ L = Module.finrank ℚ F := by
    rw [ZLattice.rank ℝ L, NumberField.mixedEmbedding.finrank]
  have hs := ZLattice.summable_norm_sub_rpow L (-r) (by rw [hrank]; linarith) x
  apply hs.of_norm_bounded_eventually
  have hfinite : {z : L | (z : NumberField.mixedEmbedding.mixedSpace F) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro z hz w hw
    exact Subtype.ext (hz.trans hw.symm)
  filter_upwards [hfinite.eventually_cofinite_notMem] with z hz
  have hpos : 0 < ‖(z : NumberField.mixedEmbedding.mixedSpace F) - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

private theorem finiteCoset_difference_integer (S : SData F CE condη) (t m : S.R)
    (h : ∀ v : S.Sf,
      algebraMap F (v.1.adicCompletion F) (m : F) -
        algebraMap F (v.1.adicCompletion F) (t : F) ∈ v.1.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, (m : F) - (t : F) = (a : F) := by
  have hval (v : HeightOneSpectrum (𝓞 F)) :
      v.valuation F ((m : F) - (t : F)) ≤ 1 := by
    by_cases hv : v ∈ S.Sf
    · have hi := h ⟨v, hv⟩
      rw [← map_sub] at hi
      let z : F := (m : F) - (t : F)
      change (z : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hi
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        v.valuedAdicCompletion_eq_valuation'] at hi
      exact hi
    · exact Set.integer_valuation_le_one
        (S.Sf : Set (HeightOneSpectrum (𝓞 F))) F (m - t) hv
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F
    ((m : F) - (t : F)) hval
  exact ⟨a, ha.symm⟩

private theorem finiteCoset_summable (S : SData F CE condη) (t : S.R) (r : ℝ)
    (hr : (Module.finrank ℚ F : ℝ) < r) :
    Summable (Set.indicator
      {m : S.R | ∀ v : S.Sf,
        algebraMap F (v.1.adicCompletion F) (m : F) -
          algebraMap F (v.1.adicCompletion F) (t : F) ∈ v.1.adicCompletionIntegers F}
      (fun m : S.R => (1 + ‖(S.diag (m : F)).2‖) ^ (-r))) := by
  classical
  let P : Set S.R := {m | ∀ v : S.Sf,
    algebraMap F (v.1.adicCompletion F) (m : F) -
      algebraMap F (v.1.adicCompletion F) (t : F) ∈ v.1.adicCompletionIntegers F}
  let L := NumberField.mixedEmbedding.integerLattice F
  let f : P → L := fun m => ⟨NumberField.mixedEmbedding F ((m.1 : F) - (t : F)), by
    obtain ⟨a, ha⟩ := finiteCoset_difference_integer S t m.1 m.2
    change ∃ a : 𝓞 F, NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) =
      NumberField.mixedEmbedding F ((m.1 : F) - (t : F))
    exact ⟨a, by rw [ha]⟩⟩
  have hf : Function.Injective f := by
    intro m n hmn
    have he := NumberField.mixedEmbedding_injective F (congrArg Subtype.val hmn)
    exact Subtype.ext (Subtype.ext (sub_left_injective he))
  have hs := (integerLattice_summable_one_add r hr
    (-NumberField.mixedEmbedding F (t : F))).comp_injective hf
  apply summable_subtype_iff_indicator.mp
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by positivity) _) _ hs
  intro m
  have he : (f m : NumberField.mixedEmbedding.mixedSpace F) -
      -NumberField.mixedEmbedding F (t : F) = NumberField.mixedEmbedding F (m.1 : F) := by
    simp [f, map_sub]
  change (1 + ‖(S.diag (m.1 : F)).2‖) ^ (-r) ≤
    (1 + ‖(f m : NumberField.mixedEmbedding.mixedSpace F) -
      -NumberField.mixedEmbedding F (t : F)‖) ^ (-r)
  rw [he]
  apply Real.rpow_le_rpow_of_nonpos (by positivity)
  · exact add_le_add le_rfl (mixed_norm_le_arch (m.1 : F))
  · have := lt_of_le_of_lt (Nat.cast_nonneg _) hr
    linarith

/-- If the finite components of `m ∈ R` are confined to a compact set `Cf ⊆ ∏_{v∈S_f} F_v`, the
series `∑ (1 + ‖m_∞‖)^{-r}` converges for every `r > [F:ℚ]`.

Proof hint: a compact subset of `F_v` lies in a ball `Theta.ball v (-N)` (compare
`A2_WEIGHTS/Finite.lean` `compact_subset_large_thetaBall`; copy, do not import); hence such `m`
have `v(m) ≤ exp N` at `v ∈ S_f` and are integral outside `S_f`, i.e. lie in the fractional
ideal `J = ∏_{v∈S_f} P_v^{-N}` (a free `ℤ`-module of rank `[F:ℚ]`). Its archimedean image is a
discrete subgroup / `ℤ`-lattice of rank `[F:ℚ]` in `InfinitePlace F → ℂ` (compare
`A1_LATTICE.diagR_isDiscrete`, `NumberField.mixedEmbedding.fractionalIdealLatticeBasis`, and
`archToMixedEquiv D` in `A1_LATTICE/Core.lean`); conclude with
`ZLattice.summable_norm_rpow`/`summable_norm_sub_rpow` and `(1+t)^{-r} ≤ t^{-r}` off `0`.
Used by: `a1_fourier_tensor_majorant`. -/
theorem a1_fourier_lattice_summable (S : SData F CE condη) (D : FieldData F)
    (Cf : Set (∀ v : S.Sf, v.1.adicCompletion F)) (hCf : IsCompact Cf)
    (r : ℝ) (hr : (Module.finrank ℚ F : ℝ) < r) :
    Summable (fun m : S.R =>
      Set.indicator {m : S.R | (S.diag (m : F)).1 ∈ Cf}
        (fun m : S.R => (1 + ‖(S.diag (m : F)).2‖) ^ (-r)) m) := by
  classical
  let U : S.R → Set (∀ v : S.Sf, v.1.adicCompletion F) := fun t =>
    {x | ∀ v : S.Sf, x v - algebraMap F (v.1.adicCompletion F) (t : F) ∈
      v.1.adicCompletionIntegers F}
  have hUopen (t : S.R) : IsOpen (U t) := by
    let B : Set (∀ v : S.Sf, v.1.adicCompletion F) :=
      Set.pi Set.univ (fun v => (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))
    have hBopen : IsOpen B := isOpen_set_pi Set.finite_univ
      (fun v _ => Valued.isOpen_valuationSubring _)
    convert hBopen.preimage (continuous_id.sub (continuous_const (y := (S.diag (t : F)).1))) using 1
    ext x
    simp [U, B, SData.diag]
  have hcover : Cf ⊆ ⋃ t : S.R, U t := by
    intro x hx
    obtain ⟨t, ht⟩ := ArtinPrimitiveRoots.Proofs.A1_LATTICE.s_integer_finite_approx S x
    exact Set.mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨T, hT⟩ := hCf.elim_finite_subcover U hUopen hcover
  let P : S.R → Set S.R := fun t => {m | (S.diag (m : F)).1 ∈ U t}
  let f : S.R → ℝ := fun m => (1 + ‖(S.diag (m : F)).2‖) ^ (-r)
  have hsum : Summable (fun m : S.R => ∑ t ∈ T, (P t).indicator f m) := by
    apply summable_sum
    intro t ht
    exact finiteCoset_summable S t r hr
  apply Summable.of_nonneg_of_le _ _ hsum
  · intro m
    by_cases hm : m ∈ {m : S.R | (S.diag (m : F)).1 ∈ Cf}
    · simp only [Set.indicator_of_mem hm]
      positivity
    · simp [Set.indicator_of_notMem hm]
  · intro m
    by_cases hm : m ∈ {m : S.R | (S.diag (m : F)).1 ∈ Cf}
    · rw [Set.indicator_of_mem hm]
      obtain ⟨t, ht, hmt⟩ := Set.mem_iUnion₂.mp (hT hm)
      have he : (P t).indicator f m = f m := Set.indicator_of_mem (show m ∈ P t from hmt) f
      change f m ≤ ∑ t ∈ T, (P t).indicator f m
      calc
        f m = (P t).indicator f m := he.symm
        _ ≤ ∑ t ∈ T, (P t).indicator f m :=
          Finset.single_le_sum (fun t ht =>
            Set.indicator_nonneg (fun n hn => Real.rpow_nonneg (by positivity) _) m) ht
    · rw [Set.indicator_of_notMem hm]
      apply Finset.sum_nonneg
      intro t ht
      apply Set.indicator_nonneg
      intro n hn
      exact Real.rpow_nonneg (by positivity) _

end ArtinPrimitiveRoots.A1
