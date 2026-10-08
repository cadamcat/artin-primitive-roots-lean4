import ArtinPrimitiveRoots.A1.Field
import ArtinPrimitiveRoots.Hecke.Dict.WeakApproximation

/-!
Helper interfaces for the A1 S-lattice proof.  This module is intentionally separate from
`SLattice`, so the arithmetic/topological statements can be developed without an import cycle.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A1_LATTICE

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem exists_principal_power_generator (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a : 𝓞 F,
      Ideal.span {a} = v.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p0 : (Ideal (𝓞 F))⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hClass : ClassGroup.mk0 p0 ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p0))
  have hn0 : v.asIdeal ^ n ≠ 0 := pow_ne_zero _ v.ne_bot
  have hClassPow :
      ClassGroup.mk0 ⟨v.asIdeal ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p0 ^ n) = 1
    rw [map_pow]
    exact hClass
  have hPrincipal : (v.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hClassPow
  obtain ⟨a, ha⟩ := hPrincipal.principal
  exact ⟨a, ha.symm⟩

theorem finite_diag_dense (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    DenseRange (fun a : F => fun v : S.Sf => algebraMap F (v.1.adicCompletion F) a) := by
  classical
  let Sinf : Finset (InfinitePlace F) := ∅
  have hweak := ArtinPrimitiveRoots.Dictionary.weakApproximation_denseRange
    (K := F) S.Sf Sinf
  have hproj : Function.Surjective
      (@Prod.fst (∀ v : S.Sf, v.1.adicCompletion F)
        (∀ w : {w : InfinitePlace F // w ∈ Sinf}, w.1.Completion)) :=
    Prod.fst_surjective
  simpa [Function.comp_def, Sinf] using
    hproj.denseRange.comp hweak continuous_fst

private theorem valuation_mul_div_le_one (v : HeightOneSpectrum (𝓞 F))
    (a b d : 𝓞 F) (hd : d ≠ 0) (n : ℕ)
    (ha : a ∈ v.asIdeal ^ n)
    (hn : n = (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors) :
    v.valuation F
      (algebraMap (𝓞 F) F (a * b) / algebraMap (𝓞 F) F d) ≤ 1 := by
  have hvald : v.intValuation d = WithZero.exp (-(n : ℤ)) := by
    rw [v.intValuation_if_neg hd, ← hn]
  have hvala : v.intValuation a ≤ WithZero.exp (-(n : ℤ)) :=
    (v.intValuation_le_pow_iff_mem a n).2 ha
  have hvalb : v.intValuation b ≤ 1 := v.intValuation_le_one b
  have hnum : v.intValuation (a * b) ≤ v.intValuation d := by
    rw [map_mul]
    calc
      v.intValuation a * v.intValuation b ≤
          WithZero.exp (-(n : ℤ)) * v.intValuation b :=
        mul_le_mul_of_nonneg_right hvala zero_le
      _ ≤ WithZero.exp (-(n : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left hvalb zero_le
      _ = v.intValuation d := by rw [hvald]; simp
  let ds : (𝓞 F)⁰ := ⟨d, mem_nonZeroDivisors_iff_ne_zero.mpr hd⟩
  rw [← IsFractionRing.mk'_eq_div (K := F) ds, v.valuation_of_mk']
  simpa only [map_mul] using
    (div_le_one₀ (zero_lt_iff.2 (v.intValuation_ne_zero d hd))).2 hnum

private theorem completion_integer_of_valuation (v : HeightOneSpectrum (𝓞 F)) (z : F)
    (hz : v.valuation F z ≤ 1) :
    algebraMap F (v.adicCompletion F) z ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v (z : v.adicCompletion F) ≤ 1
  rw [v.valuedAdicCompletion_eq_valuation']
  exact hz

theorem s_integer_adjust (S : ArtinPrimitiveRoots.A1.SData F CE condη) (x : F) :
    ∃ r : S.R, ∀ v : S.Sf,
      algebraMap F (v.1.adicCompletion F) (x - (r : F)) ∈
        v.1.adicCompletionIntegers F := by
  classical
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨d, hd⟩
  have hden : algebraMap (𝓞 F) F d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  let I : Ideal (𝓞 F) := Ideal.span {d}
  have hI : I ≠ ⊥ := by
    change Ideal.span {d} ≠ ⊥
    exact mt Ideal.span_singleton_eq_bot.mp hd0
  let e : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk I).factors
  have hsupport : {v : HeightOneSpectrum (𝓞 F) | e v ≠ 0}.Finite := by
    have hfinite := Filter.eventually_cofinite.mp (Associates.finite_factors hI)
    apply hfinite.subset
    intro v hv
    simpa [e, I, Int.natCast_ne_zero] using hv
  let s : Finset (HeightOneSpectrum (𝓞 F)) := hsupport.toFinset
  have hmem (v : HeightOneSpectrum (𝓞 F)) : v ∈ s ↔ e v ≠ 0 := by
    simp [s, e]
  have hprime (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ s) : Prime v.asIdeal :=
    Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hcoprime : ∀ᵉ (v ∈ s) (w ∈ s), v ≠ w → v.asIdeal ≠ w.asIdeal := by
    intro v hv w hw hvw heq
    exact hvw (HeightOneSpectrum.ext (by simpa using heq))
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
      (s := s) (P := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) e hprime hcoprime
      (fun v : s => if v.1 ∈ S.Sf then 1 else 0)
  have hc_at (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ s) :
      c - (if v ∈ S.Sf then 1 else 0) ∈ v.asIdeal ^ e v := by
    simpa using hc v hv
  have he0 (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) : e v = 0 := by
    by_contra hne
    exact hv ((hmem v).2 hne)
  have hcS (v : S.Sf) : c - 1 ∈ v.1.asIdeal ^ e v.1 := by
    by_cases hv : v.1 ∈ s
    · simpa [v.2] using hc_at v.1 hv
    · simp [he0 v.1 hv]
  have hcOutside (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S.Sf) :
      c ∈ v.asIdeal ^ e v := by
    by_cases hvs : v ∈ s
    · simpa [hv] using hc_at v hvs
    · simp [he0 v hvs]
  have hcx : algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d) =
      algebraMap (𝓞 F) F (c * b) / algebraMap (𝓞 F) F d := by
    rw [map_mul]
    field_simp [hden]
  have hdiff : algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d -
      algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d) =
        algebraMap (𝓞 F) F ((1 - c) * b) / algebraMap (𝓞 F) F d := by
    rw [map_mul, map_sub, map_one]
    field_simp [hden]
  have hrprop : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S.Sf →
      v.valuation F
        (algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d)) ≤ 1 := by
    intro v hv
    rw [hcx]
    exact valuation_mul_div_le_one v c b d hd0 (e v) (hcOutside v hv) rfl
  let r : S.R := ⟨
    algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F b / algebraMap (𝓞 F) F d), hrprop⟩
  refine ⟨r, ?_⟩
  intro v
  apply completion_integer_of_valuation v.1
  rw [hdiff]
  exact valuation_mul_div_le_one v.1 (1 - c) b d hd0 (e v.1) (by
    simpa using (Submodule.neg_mem (v.1.asIdeal ^ e v.1) (hcS v))) rfl

theorem s_integer_finite_approx (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x : ∀ v : S.Sf, v.1.adicCompletion F) :
    ∃ r : S.R, ∀ v : S.Sf,
      x v - algebraMap F (v.1.adicCompletion F) (r : F) ∈
        v.1.adicCompletionIntegers F := by
  classical
  let f : F → ∀ v : S.Sf, v.1.adicCompletion F := fun a v =>
    algebraMap F (v.1.adicCompletion F) a
  have hdense : DenseRange f := by
    simpa [f] using finite_diag_dense S
  let O : ∀ v : S.Sf, Set (v.1.adicCompletion F) :=
    fun v => v.1.adicCompletionIntegers F
  have hOopen (v : S.Sf) : IsOpen (O v) := by
    exact Valued.isOpen_valuationSubring _
  let B : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ O
  have hBopen : IsOpen B := by
    apply isOpen_set_pi Set.finite_univ
    intro v hv
    exact hOopen v
  let U : Set (∀ v : S.Sf, v.1.adicCompletion F) := {y | x - y ∈ B}
  have hUopen : IsOpen U := hBopen.preimage (continuous_const.sub continuous_id)
  have hUnonempty : U.Nonempty := by
    refine ⟨x, ?_⟩
    simp [U, B, O]
  obtain ⟨a, ha⟩ := hdense.exists_mem_open hUopen hUnonempty
  have happrox : ∀ v : S.Sf,
      x v - algebraMap F (v.1.adicCompletion F) a ∈ v.1.adicCompletionIntegers F := by
    intro v
    have h := ha
    change x - f a ∈ B at h
    have hv := h v (by simp)
    simpa [f, O] using hv
  obtain ⟨r, hr⟩ := s_integer_adjust S a
  refine ⟨r, ?_⟩
  intro v
  have hidentity :
      x v - algebraMap F (v.1.adicCompletion F) (r : F) =
        (x v - algebraMap F (v.1.adicCompletion F) a) +
          algebraMap F (v.1.adicCompletion F) (a - (r : F)) := by
    rw [map_sub]
    abel
  rw [hidentity]
  exact (v.1.adicCompletionIntegers F).add_mem _ _ (happrox v) (hr v)

private noncomputable def archToMixedEquiv (D : ArtinPrimitiveRoots.A1.FieldData F) :
    (InfinitePlace F → ℂ) ≃L[ℝ] NumberField.mixedEmbedding.mixedSpace F := by
  let e : (InfinitePlace F → ℂ) ≃ₗ[ℝ] NumberField.mixedEmbedding.mixedSpace F :=
    { toFun := fun z =>
        (fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsReal w} =>
          False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1)),
          fun w : {w : InfinitePlace F // NumberField.InfinitePlace.IsComplex w} => z w.1)
      invFun := fun z w => z.2 ⟨w, D.isTotallyComplex.isComplex w⟩
      left_inv := by intro z; rfl
      right_inv := by
        intro z
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_add' := by
        intro x y
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          rfl
      map_smul' := by
        intro c x
        apply Prod.ext
        · funext w
          exact False.elim
            ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
              (D.isTotallyComplex.isComplex w.1))
        · funext w
          simp }
  have hecont : Continuous e := by
    refine continuous_prodMk.mpr ⟨continuous_const, continuous_pi ?_⟩
    intro w
    exact continuous_apply w.1
  exact e.toContinuousLinearEquivOfContinuous hecont

theorem arch_integer_compact_reduction (D : ArtinPrimitiveRoots.A1.FieldData F) :
    ∃ C : Set (InfinitePlace F → ℂ), IsCompact C ∧
      ∀ z : InfinitePlace F → ℂ, ∃ a : 𝓞 F, ∃ p ∈ C,
        z = (fun w => w.embedding (a : F)) + p := by
  classical
  let e := archToMixedEquiv D
  let P : Set (NumberField.mixedEmbedding.mixedSpace F) :=
    ZSpan.fundamentalDomain (NumberField.mixedEmbedding.latticeBasis F)
  have hPbounded : Bornology.IsBounded P := by
    exact ZSpan.fundamentalDomain_isBounded _
  have hPcompact : IsCompact (closure P) := hPbounded.isCompact_closure
  let C : Set (InfinitePlace F → ℂ) := e.symm '' closure P
  refine ⟨C, ?_, ?_⟩
  · exact hPcompact.image e.symm.continuous
  · intro z
    let zM : NumberField.mixedEmbedding.mixedSpace F := e z
    obtain ⟨y, hy⟩ :=
      ZSpan.exist_unique_vadd_mem_fundamentalDomain
        (NumberField.mixedEmbedding.latticeBasis F) zM
    have hyP : (y : NumberField.mixedEmbedding.mixedSpace F) + zM ∈ P := by
      have hy' : (y : NumberField.mixedEmbedding.mixedSpace F) +ᵥ zM ∈ P := by
        exact hy.1
      simpa only [vadd_eq_add] using hy'
    have hyInt :
        (y : NumberField.mixedEmbedding.mixedSpace F) ∈
          NumberField.mixedEmbedding.integerLattice F :=
      (NumberField.mixedEmbedding.mem_span_latticeBasis F).mp y.property
    have hnegInt : -(y : NumberField.mixedEmbedding.mixedSpace F) ∈
        NumberField.mixedEmbedding.integerLattice F :=
      (NumberField.mixedEmbedding.integerLattice F).neg_mem hyInt
    change ∃ a : 𝓞 F,
        NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) =
          -(y : NumberField.mixedEmbedding.mixedSpace F) at hnegInt
    obtain ⟨a, ha⟩ := hnegInt
    let pM : NumberField.mixedEmbedding.mixedSpace F := (y : _) + zM
    have hpM : pM ∈ closure P := subset_closure (by simpa [pM] using hyP)
    have heDiag : e (fun w : InfinitePlace F => w.embedding (a : F)) =
        NumberField.mixedEmbedding F (a : F) := by
      apply Prod.ext
      · funext w
        exact False.elim
          ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
            (D.isTotallyComplex.isComplex w.1))
      · funext w
        rfl
    have hzM : zM = NumberField.mixedEmbedding F (a : F) + pM := by
      calc
        zM = -(y : NumberField.mixedEmbedding.mixedSpace F) + pM := by
          dsimp [pM, zM]
          abel
        _ = NumberField.mixedEmbedding F (a : F) + pM := by
          rw [← ha]
    refine ⟨a, e.symm pM, ⟨pM, hpM, rfl⟩, ?_⟩
    apply e.injective
    rw [map_add, heDiag, e.apply_symm_apply]
    exact hzM

theorem diagR_isDiscrete (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    IsDiscrete (Set.range fun r : S.R => S.diag (r : F)) := by
  sorry

theorem diagR_has_compact_cover (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧ ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K,
      x = S.diag (r : F) + k := by
  sorry

end ArtinPrimitiveRoots.Proofs.A1_LATTICE
