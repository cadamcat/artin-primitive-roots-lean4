import ArtinPrimitiveRoots.Theta.Cover
import ArtinPrimitiveRoots.Theta.LocalInt
import Mathlib.Topology.Maps.Proper.Basic

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The finite local cover has compact preimages of compact projective sets. -/
theorem local_cover_compact_preimage
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v)
    (K : Set (PGL2 (v.adicCompletion F))) (hK : IsCompact K) :
    IsCompact (L.pr ⁻¹' K) := by
  have hz (ζ : rootsOfUnity 3 ℂ) : L.pr (L.z ζ) = 1 := by
    change L.z ζ ∈ L.pr.ker
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hrel {g c : L.L} (h : L.pr g = L.pr c) :
      ∃ ζ : rootsOfUnity 3 ℂ, g = L.z ζ * c := by
    have hk : g * c⁻¹ ∈ L.pr.ker := by
      change L.pr (g * c⁻¹) = 1
      simp only [map_mul, map_inv, h, mul_inv_cancel]
    rw [L.pr_ker] at hk
    obtain ⟨ζ, hζ⟩ := hk
    exact ⟨ζ, by simp only [hζ, inv_mul_cancel_right]⟩
  have hclosed : IsClosedMap L.pr := by
    intro C hC
    apply ((Topology.isQuotientMap_iff_isClosed.mp
      (L.pr_open.isQuotientMap L.pr_cont L.pr_surj)).2 (L.pr '' C)).mpr
    have hsat : L.pr ⁻¹' (L.pr '' C) =
        ⋃ ζ : rootsOfUnity 3 ℂ, (fun g : L.L => L.z ζ * g) '' C := by
      ext g
      constructor
      · rintro ⟨c, hc, hcg⟩
        obtain ⟨ζ, hζ⟩ := hrel hcg.symm
        exact Set.mem_iUnion.mpr ⟨ζ, c, hc, hζ.symm⟩
      · intro hg
        obtain ⟨ζ, c, hc, rfl⟩ := Set.mem_iUnion.mp hg
        exact ⟨c, hc, by simp only [map_mul, hz, one_mul]⟩
    rw [hsat]
    exact isClosed_iUnion_of_finite fun ζ =>
      (Homeomorph.mulLeft (L.z ζ)).isClosedMap C hC
  have hfibers (y : PGL2 (v.adicCompletion F)) :
      IsCompact (L.pr ⁻¹' {y}) := by
    obtain ⟨a, ha⟩ := L.pr_surj y
    apply Set.Finite.isCompact
    apply (Set.finite_range fun ζ : rootsOfUnity 3 ℂ => L.z ζ * a).subset
    intro g hg
    obtain ⟨ζ, hζ⟩ := hrel ((Set.mem_singleton_iff.mp hg).trans ha.symm)
    exact ⟨ζ, hζ.symm⟩
  exact (isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨L.pr_cont, hclosed, hfibers⟩).isCompact_preimage hK

/-- Two integral lower-unipotent charts for the local projective compact part. -/
def localProjectiveCompact (v : FinPlace F) : Set (PGL2 (v.adicCompletion F)) :=
  (fun t : v.adicCompletion F => QuotientGroup.mk (lowerM _ t)) ''
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∪
  (fun t : v.adicCompletion F => QuotientGroup.mk (lowerM _ t * weylM _)) ''
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))

/-- Local projective Iwasawa decomposition with the bottom-row height formula. -/
theorem local_projective_iwasawa (v : FinPlace F)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    ∃ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
      (k : PGL2 (v.adicCompletion F)),
      k ∈ localProjectiveCompact v ∧
      QuotientGroup.mk g = QuotientGroup.mk (upperM _ x * diagM _ y) * k ∧
      absFin v (y : v.adicCompletion F) =
        absFin v (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det /
          (max (absFin v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0))
            (absFin v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1))) ^ 2 := by
  have hnormalize (a : GL (Fin 2) (v.adicCompletion F))
      (hcd : ‖a 1 0‖ ≤ ‖a 1 1‖) :
      ∃ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ),
        a 1 0 / a 1 1 ∈ v.adicCompletionIntegers F ∧
        (QuotientGroup.mk a : PGL2 (v.adicCompletion F)) =
          QuotientGroup.mk (upperM _ x * diagM _ y) *
            QuotientGroup.mk (lowerM _ (a 1 0 / a 1 1)) ∧
        ‖(y : v.adicCompletion F)‖ =
          ‖(a : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det‖ / ‖a 1 1‖ ^ 2 := by
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero a
    have hd : a 1 1 ≠ 0 := by
      intro hd
      have hc : a 1 0 = 0 := norm_eq_zero.mp
        (le_antisymm (by simpa only [hd, norm_zero] using hcd) (norm_nonneg _))
      exact hdet (by simp [Matrix.det_fin_two, hc, hd])
    let x : v.adicCompletion F := a 0 1 / a 1 1
    let y : (v.adicCompletion F)ˣ := Units.mk0
      ((a : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det / (a 1 1) ^ 2)
      (div_ne_zero hdet (pow_ne_zero 2 hd))
    let t : (v.adicCompletion F)ˣ := Units.mk0 (a 1 1) hd
    have ht : a 1 0 / a 1 1 ∈ v.adicCompletionIntegers F := by
      change a 1 0 / a 1 1 ∈ (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).integer
      rw [Valuation.mem_integer_iff, ← Valued.toNormedField.norm_le_one_iff]
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hd)).mpr hcd
    have hfactor : a = Matrix.GeneralLinearGroup.scalar (Fin 2) t *
        (upperM _ x * diagM _ y) * lowerM _ (a 1 0 / a 1 1) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change a i j = (Matrix.scalar (Fin 2) (a 1 1) *
        (!![1, x; 0, 1] * !![(y : v.adicCompletion F), 0; 0, 1]) *
          !![1, 0; a 1 0 / a 1 1, 1]) i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, x, y, Matrix.det_fin_two] <;>
        field_simp [hd] <;> ring
    have hscalar : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) t) :
        PGL2 (v.adicCompletion F)) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨t, rfl⟩
    refine ⟨x, y, ht, ?_, ?_⟩
    · calc
        QuotientGroup.mk a = QuotientGroup.mk
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t *
              (upperM _ x * diagM _ y) * lowerM _ (a 1 0 / a 1 1)) :=
          congrArg QuotientGroup.mk hfactor
        _ = _ := by simp only [QuotientGroup.mk_mul, hscalar, one_mul]
    · simp only [y, Units.val_mk0, norm_div, norm_pow]
  simp only [absFin_eq_norm]
  by_cases hcd : ‖g 1 0‖ ≤ ‖g 1 1‖
  · obtain ⟨x, y, ht, hfactor, hheight⟩ := hnormalize g hcd
    refine ⟨x, y, QuotientGroup.mk (lowerM _ (g 1 0 / g 1 1)), ?_, hfactor, ?_⟩
    · exact Or.inl ⟨g 1 0 / g 1 1, ht, rfl⟩
    · simpa only [max_eq_right hcd] using hheight
  · let a : GL (Fin 2) (v.adicCompletion F) := g * weylM _
    have hswap (i : Fin 2) (j : Fin 2) : a i j = g i (1 - j) := by
      fin_cases i <;> fin_cases j <;>
        simp [a, weylM, Matrix.mul_apply, Fin.sum_univ_two]
    have hdc : ‖a 1 0‖ ≤ ‖a 1 1‖ := by
      simpa only [hswap, sub_zero, sub_self] using (le_of_not_ge hcd)
    obtain ⟨x, y, ht, hfactor, hheight⟩ := hnormalize a hdc
    have hw : weylM (v.adicCompletion F) * weylM _ = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
    have hdet : (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det =
        -(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
      simp [a, Matrix.det_mul, weylM, Matrix.det_fin_two]
    refine ⟨x, y, QuotientGroup.mk (lowerM _ (a 1 0 / a 1 1) * weylM _),
      Or.inr ⟨a 1 0 / a 1 1, ht, rfl⟩, ?_, ?_⟩
    · calc
        QuotientGroup.mk g = QuotientGroup.mk (a * weylM _) := by
          simp only [a, mul_assoc, hw, mul_one]
        _ = QuotientGroup.mk (upperM _ x * diagM _ y) *
            QuotientGroup.mk (lowerM _ (a 1 0 / a 1 1)) * QuotientGroup.mk (weylM _) := by
          rw [QuotientGroup.mk_mul, hfactor]
        _ = _ := by simp only [QuotientGroup.mk_mul, mul_assoc]
    · simpa only [hswap, sub_self, hdet, norm_neg,
        max_eq_left (le_of_not_ge hcd)] using hheight

/-- The two integral projective charts form a compact set. -/
theorem local_projective_compact (v : FinPlace F) :
    IsCompact (localProjectiveCompact v) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hinv (t : K) : (lowerM K t)⁻¹ = lowerM K (-t) := by
    apply inv_eq_of_mul_eq_one_right
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerM, Matrix.mul_apply, Fin.sum_univ_two]
  have hentries : Continuous (fun t : K => (lowerM K t : Matrix (Fin 2) (Fin 2) K)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
  have hlower : Continuous (lowerM K) := by
    apply Units.continuous_iff.mpr
    refine ⟨hentries, ?_⟩
    simp only [hinv]
    exact hentries.comp continuous_neg
  have hfirst : Continuous (fun t : K => (QuotientGroup.mk (lowerM K t) : PGL2 K)) :=
    QuotientGroup.continuous_mk.comp hlower
  have hsecond : Continuous (fun t : K =>
      (QuotientGroup.mk (lowerM K t * weylM K) : PGL2 K)) :=
    QuotientGroup.continuous_mk.comp (hlower.mul continuous_const)
  exact (hcompact.image hfirst).union (hcompact.image hsecond)

/-- Local integral matrix units, including their integral inverses, form a compact set. -/
theorem local_integral_units_compact (v : FinPlace F) :
    IsCompact {k : GL (Fin 2) (v.adicCompletion F) |
      (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        v.adicCompletionIntegers F) ∧
      ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F} := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) =
        Metric.closedBall (0 : K) 1
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  let M : Submonoid (Matrix (Fin 2) (Fin 2) K) :=
    { carrier := {m | ∀ i j, m i j ∈ v.adicCompletionIntegers F}
      one_mem' := by
        intro i j
        change (1 : Matrix (Fin 2) (Fin 2) K) i j ∈ v.adicCompletionIntegers F
        by_cases h : i = j
        · simp [Matrix.one_apply, h]
        · simp [h]
      mul_mem' := by
        intro m n hm hn i j
        change (∑ t, m i t * n t j) ∈ v.adicCompletionIntegers F
        exact (v.adicCompletionIntegers F).sum_mem
          fun t _ => (v.adicCompletionIntegers F).mul_mem (m i t) (n t j) (hm i t) (hn t j) }
  have hM : IsCompact (M : Set (Matrix (Fin 2) (Fin 2) K)) := by
    have hset : (M : Set (Matrix (Fin 2) (Fin 2) K)) =
        Set.pi Set.univ (fun _ : Fin 2 =>
          Set.pi Set.univ (fun _ : Fin 2 => (v.adicCompletionIntegers F : Set K))) := by
      ext m
      change (∀ i j, m i j ∈ v.adicCompletionIntegers F) ↔
        ∀ i : Fin 2, i ∈ Set.univ →
          ∀ j : Fin 2, j ∈ Set.univ → m i j ∈ v.adicCompletionIntegers F
      simp only [Set.mem_univ, forall_true_left]
    rw [hset]
    exact isCompact_univ_pi fun _ : Fin 2 =>
      isCompact_univ_pi fun _ : Fin 2 => hcompact
  change IsCompact (M.units : Set (Matrix (Fin 2) (Fin 2) K)ˣ)
  exact Submonoid.units_isCompact hM

end ArtinPrimitiveRoots.A1.Theta
