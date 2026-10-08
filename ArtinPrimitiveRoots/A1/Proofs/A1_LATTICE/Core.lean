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

private theorem archToMixedEquiv_apply_diag (D : ArtinPrimitiveRoots.A1.FieldData F) (x : F) :
    archToMixedEquiv D (fun w : InfinitePlace F => w.embedding x) =
      NumberField.mixedEmbedding F x := by
  apply Prod.ext
  · funext w
    exact False.elim
      ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr w.2)
        (D.isTotallyComplex.isComplex w.1))
  · funext w
    rfl

theorem diagR_isDiscrete (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    IsDiscrete (Set.range fun r : S.R => S.diag (r : F)) := by
  classical
  let e := archToMixedEquiv D
  let L := NumberField.mixedEmbedding.integerLattice F
  have hLtype : DiscreteTopology L := inferInstance
  have hLdisc : DiscreteTopology (L : Set (NumberField.mixedEmbedding.mixedSpace F)) :=
    isDiscrete_iff_discreteTopology.mp
      (SetLike.isDiscrete_iff_discreteTopology.mpr hLtype)
  have hLzero : (0 : NumberField.mixedEmbedding.mixedSpace F) ∈
      (L : Set (NumberField.mixedEmbedding.mixedSpace F)) := L.zero_mem
  obtain ⟨W, hWopen, hWinter⟩ :=
    (discreteTopology_subtype_iff' (S :=
      (L : Set (NumberField.mixedEmbedding.mixedSpace F)))).mp hLdisc 0 hLzero
  let U : Set (InfinitePlace F → ℂ) := e ⁻¹' W
  have hUopen : IsOpen U := hWopen.preimage e.continuous
  have hWzero : (0 : NumberField.mixedEmbedding.mixedSpace F) ∈ W := by
    have hpair : (0 : NumberField.mixedEmbedding.mixedSpace F) ∈
        W ∩ (L : Set (NumberField.mixedEmbedding.mixedSpace F)) := by
      rw [hWinter]
      simp
    exact hpair.1
  have hUzero : (0 : InfinitePlace F → ℂ) ∈ U := by
    change e 0 ∈ W
    simpa using hWzero
  let O : ∀ v : S.Sf, Set (v.1.adicCompletion F) :=
    fun v => v.1.adicCompletionIntegers F
  have hOopen (v : S.Sf) : IsOpen (O v) := Valued.isOpen_valuationSubring _
  let B : Set (∀ v : S.Sf, v.1.adicCompletion F) := Set.pi Set.univ O
  have hBopen : IsOpen B := by
    apply isOpen_set_pi Set.finite_univ
    intro v hv
    exact hOopen v
  have hBzero : (0 : ∀ v : S.Sf, v.1.adicCompletion F) ∈ B := by
    simp [B, O]
  let N : Set S.FS := B ×ˢ U
  have hNopen : IsOpen N := hBopen.prod hUopen
  have hNzero : (0 : S.FS) ∈ N := ⟨hBzero, hUzero⟩
  have hzeroR (r : S.R) (hrN : S.diag (r : F) ∈ N) : r = 0 := by
    have hrB : (S.diag (r : F)).1 ∈ B := hrN.1
    have hrU : (S.diag (r : F)).2 ∈ U := hrN.2
    have hlocal (v : S.Sf) :
        algebraMap F (v.1.adicCompletion F) (r : F) ∈
          v.1.adicCompletionIntegers F := by
      have hv := hrB v (by simp)
      simpa [B, O, ArtinPrimitiveRoots.A1.SData.diag] using hv
    have hval (v : HeightOneSpectrum (𝓞 F)) : v.valuation F (r : F) ≤ 1 := by
      by_cases hv : v ∈ S.Sf
      · let vS : S.Sf := ⟨v, hv⟩
        have hvint : algebraMap F (v.adicCompletion F) (r : F) ∈
            v.adicCompletionIntegers F := by
          simpa [vS] using hlocal vS
        change (r : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hvint
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hvint
        rw [v.valuedAdicCompletion_eq_valuation'] at hvint
        exact hvint
      · exact Set.integer_valuation_le_one
          (S.Sf : Set (HeightOneSpectrum (𝓞 F))) F r hv
    obtain ⟨a, ha⟩ :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one F (r : F) hval
    have hdiagArch : (ArtinPrimitiveRoots.A1.SData.diag S (r : F)).2 =
        (fun w : InfinitePlace F => w.embedding (r : F)) := by
      ext w
      rfl
    have harch : e (fun w : InfinitePlace F => w.embedding (r : F)) ∈ W := by
      rw [← hdiagArch]
      simpa [U] using hrU
    have harchEq :
        e (fun w : InfinitePlace F => w.embedding (r : F)) =
          NumberField.mixedEmbedding F (a : F) := by
      calc
        e (fun w : InfinitePlace F => w.embedding (r : F)) =
            e (fun w : InfinitePlace F => w.embedding (algebraMap (𝓞 F) F a)) := by
              rw [← ha]
        _ = NumberField.mixedEmbedding F (algebraMap (𝓞 F) F a) :=
          archToMixedEquiv_apply_diag D _
        _ = NumberField.mixedEmbedding F (a : F) := rfl
    have haW : NumberField.mixedEmbedding F (a : F) ∈ W := by
      rw [← harchEq]
      exact harch
    have haL : NumberField.mixedEmbedding F (a : F) ∈
        (L : Set (NumberField.mixedEmbedding.mixedSpace F)) := by
      change ∃ b : 𝓞 F,
        NumberField.mixedEmbedding F (algebraMap (𝓞 F) F b) =
          NumberField.mixedEmbedding F (a : F)
      exact ⟨a, rfl⟩
    have ha0 : NumberField.mixedEmbedding F (a : F) = 0 := by
      have hmem : NumberField.mixedEmbedding F (a : F) ∈
          W ∩ (L : Set (NumberField.mixedEmbedding.mixedSpace F)) := ⟨haW, haL⟩
      have hmem0 : NumberField.mixedEmbedding F (a : F) ∈ ({0} :
          Set (NumberField.mixedEmbedding.mixedSpace F)) := by
        rw [← hWinter]
        exact hmem
      simpa using hmem0
    have hmapzero : NumberField.mixedEmbedding F (a : F) =
        NumberField.mixedEmbedding F 0 := by simpa using ha0
    have haF0 : (a : F) = 0 := NumberField.mixedEmbedding_injective F hmapzero
    apply Subtype.ext
    calc
      (r : F) = algebraMap (𝓞 F) F a := ha.symm
      _ = 0 := haF0
  refine (isDiscrete_iff_forall_mem_exists_isOpen).2 ?_
  intro x hx
  obtain ⟨r, rfl⟩ := hx
  let Ux : Set S.FS := {y | y - S.diag (r : F) ∈ N}
  refine ⟨Ux, hNopen.preimage (continuous_id.sub continuous_const), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy, s, hs⟩
    have hyN : y - S.diag (r : F) ∈ N := by
      change y - S.diag (r : F) ∈ N at hy
      exact hy
    have hdiff : S.diag ((s - r : S.R) : F) ∈ N := by
      simpa [hs] using hyN
    have hsr : s - r = 0 := hzeroR (s - r) hdiff
    have hsreq : s = r := sub_eq_zero.mp hsr
    calc
      y = S.diag (s : F) := hs.symm
      _ = S.diag (r : F) := by simpa [hsreq]
  · intro hy
    subst y
    refine ⟨?_, ⟨r, rfl⟩⟩
    change S.diag (r : F) - S.diag (r : F) ∈ N
    simpa using hNzero

private theorem adicCompletionIntegers_compact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  classical
  let A : ValuationSubring F := (v.valuation F).valuationSubring
  let K := v.adicCompletion F
  let W : ValuationSubring K := v.adicCompletionIntegers F
  have hAfinite : Finite (IsLocalRing.ResidueField A) := by
    let B : ValuationSubring F := v.valuationSubringAtPrime F
    haveI : Finite (𝓞 F ⧸ v.asIdeal) :=
      Ring.HasFiniteQuotients.finiteQuotient (R := 𝓞 F) v.ne_bot
    have hBfinite : Finite (IsLocalRing.ResidueField B) := by
      have hBfinite' : Finite (B ⧸ IsLocalRing.maximalIdeal B) :=
        Finite.of_equiv (𝓞 F ⧸ v.asIdeal)
          (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal B).toEquiv
      change Finite (B ⧸ IsLocalRing.maximalIdeal B)
      exact hBfinite'
    have hBA : B = A := by
      exact v.valuationSubringAtPrime_eq_valuationSubring
    rw [← hBA]
    exact hBfinite
  let g : A →+* W := RingHom.codRestrict
      ((algebraMap F K).comp A.subtype) W (by
        intro a
        change Valued.v ((a : F) : K) ≤ 1
        rw [v.valuedAdicCompletion_eq_valuation']
        exact (Valuation.mem_valuationSubring_iff (v.valuation F) (a : F)).mp a.2)
  let resW : W →+* IsLocalRing.ResidueField W := IsLocalRing.residue W
  let f : A →+* IsLocalRing.ResidueField W := resW.comp g
  have hvW := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
    (R := 𝓞 F) (K := F) (v := v)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    let U : Set K := {z | Valued.v (z - (x : K)) < 1}
    have hUopen : IsOpen U := by
      have hball : IsOpen {z : K | Valued.v.restrict z < 1} := Valued.isOpen_ball K 1
      have hcont : Continuous (fun z : K => z - (x : K)) := by fun_prop
      have h := hball.preimage hcont
      simpa [U, Valued.v.restrict_lt_iff_lt_embedding] using h
    have hUne : U.Nonempty := ⟨x, by simp [U]⟩
    obtain ⟨b, hb⟩ := DenseRange.exists_mem_open
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v) hUopen hUne
    have hclose : Valued.v (algebraMap F K b - (x : K)) < 1 := by
      change Valued.v (algebraMap F K b - (x : K)) < 1 at hb
      exact hb
    have hxle : Valued.v (x : K) ≤ 1 :=
      (Valuation.mem_valuationSubring_iff Valued.v (x : K)).mp x.2
    have hbcomp : Valued.v (algebraMap F K b) ≤ 1 := by
      calc
        Valued.v (algebraMap F K b) =
            Valued.v ((algebraMap F K b - (x : K)) + (x : K)) := by
              congr 1
              ring
        _ ≤ max (Valued.v (algebraMap F K b - (x : K))) (Valued.v (x : K)) :=
          Valued.v.map_add _ _
        _ ≤ 1 := max_le hclose.le hxle
    have hbval : v.valuation F b ≤ 1 := by
      change Valued.v ((b : F) : K) ≤ 1 at hbcomp
      rw [v.valuedAdicCompletion_eq_valuation'] at hbcomp
      exact hbcomp
    let a : A := ⟨b, (Valuation.mem_valuationSubring_iff (v.valuation F) b).mpr hbval⟩
    have hdiff : (g a - x) ∈ IsLocalRing.maximalIdeal W := by
      have hnotUnit : ¬ IsUnit (g a - x) := by
        intro hu
        have hval := hvW.isUnit_iff_valuation_eq_one.mp hu
        change Valued.v ((g a - x : W) : K) = 1 at hval
        exact (not_lt_of_ge hval.ge) hclose
      rw [IsLocalRing.mem_maximalIdeal]
      exact hnotUnit
    have hres : resW (g a) = resW x := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hdiff
    exact ⟨a, by simpa [f] using hres.trans rfl⟩
  have hker : IsLocalRing.maximalIdeal A ≤ RingHom.ker f := by
    intro a ha
    change resW (g a) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    have hval : Valued.v ((g a : W) : K) < 1 := by
      change Valued.v ((a : F) : K) < 1
      rw [v.valuedAdicCompletion_eq_valuation']
      exact (Valuation.mem_maximalIdeal_iff F (v.valuation F)).mp ha
    have hnotUnit : ¬ IsUnit (g a) := by
      intro hu
      have hvalone := hvW.isUnit_iff_valuation_eq_one.mp hu
      change Valued.v ((g a : W) : K) = 1 at hvalone
      exact (not_lt_of_ge hvalone.ge) hval
    rw [IsLocalRing.mem_maximalIdeal]
    exact hnotUnit
  let fbar : A ⧸ IsLocalRing.maximalIdeal A →+* IsLocalRing.ResidueField W :=
    Ideal.Quotient.lift _ f hker
  have hbarSurj : Function.Surjective fbar := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    change f a = y
    simpa only [Ideal.Quotient.lift_mk] using ha
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := hAfinite
  haveI : Finite (IsLocalRing.ResidueField W) := Finite.of_surjective fbar hbarSurj
  letI : CompleteSpace K := inferInstance
  have hWclosed : IsClosed (W : Set K) := Valued.isClosed_valuationSubring K
  letI : CompleteSpace W := hWclosed.completeSpace_coe
  letI : IsDiscreteValuationRing W := inferInstance
  let e : W ≃+* Valued.integer K :=
    { toFun := fun x =>
        ⟨(x : K), (Valuation.mem_integer_iff Valued.v (x : K)).2
          ((Valuation.mem_valuationSubring_iff Valued.v (x : K)).mp x.2)⟩
      invFun := fun x =>
        ⟨(x : K), (Valuation.mem_valuationSubring_iff Valued.v (x : K)).mpr
          ((Valuation.mem_integer_iff Valued.v (x : K)).mp x.2)⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_mul' := by intro x y; rfl
      map_add' := by intro x y; rfl }
  haveI : IsDiscreteValuationRing (Valued.integer K) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  haveI : Finite (IsLocalRing.ResidueField (Valued.integer K)) :=
    Finite.of_equiv (IsLocalRing.ResidueField W) (IsLocalRing.ResidueField.mapEquiv e)
  have hOclosed : IsClosed (Valued.integer K : Set K) := by
    change IsClosed (W : Set K)
    exact hWclosed
  haveI : CompleteSpace (Valued.integer K) := hOclosed.completeSpace_coe
  haveI : CompactSpace (Valued.integer K) := by
    apply Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hc : IsCompact (Set.univ : Set (Valued.integer K)) := isCompact_univ_iff.mpr inferInstance
  have hcInt : IsCompact (Valued.integer K : Set K) := by
    simpa using hc.image continuous_subtype_val
  have hWEq : (W : Set K) = (Valued.integer K : Set K) := by
    ext z
    simp [W, Valued.integer, Valuation.integer,
      HeightOneSpectrum.adicCompletionIntegers,
      Valuation.mem_valuationSubring_iff, Valuation.mem_integer_iff]
  rw [hWEq]
  exact hcInt

theorem diagR_has_compact_cover (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F) :
    ∃ K : Set S.FS, IsCompact K ∧ ∀ x : S.FS, ∃ r : S.R, ∃ k ∈ K,
      x = S.diag (r : F) + k := by
  sorry

end ArtinPrimitiveRoots.Proofs.A1_LATTICE
