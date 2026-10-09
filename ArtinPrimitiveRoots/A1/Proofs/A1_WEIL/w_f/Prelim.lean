import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.Data
import ArtinPrimitiveRoots.A1.Proofs.A1_WEIL.LocalCharacter
import ArtinPrimitiveRoots.A1.Proofs.A1_DUAL.AnnihilatorCore
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped AdicCompletionIntegers

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

local instance completionMeasurable (v : FinPlace F) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance completionBorel (v : FinPlace F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

/-- At an exterior prime generator the local absolute value is one negative valuation step. -/
theorem gen_local_valuation (S : SData F CE condη) (v : FinPlace F)
    (hv : v ∉ S.Sf) (a : Fˣ) (ha : S.IsGen (a : F) v.asIdeal) :
    v.valuation F (a : F) = WithZero.exp (-1 : ℤ) := by
  have hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 1 := by
    rw [ha.2.2 v hv]
    exact FractionalIdeal.count_self F v
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    v (a : F) ha.2.1
  have hlog' : WithZero.log (v.valuation F (a : F)) = -1 := by
    have h := hlog.symm.trans hcount
    linarith
  have hne : v.valuation F (a : F) ≠ 0 := (v.valuation F).ne_zero_iff.mpr ha.2.1
  calc
    v.valuation F (a : F) = WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
      (WithZero.exp_log hne).symm
    _ = WithZero.exp (-1 : ℤ) := by rw [hlog']

/-- A generator of the exterior prime is a unit at every other exterior place. -/
theorem gen_local_valuation_other (S : SData F CE condη) (v w : FinPlace F)
    (hv : v ∉ S.Sf) (p : Fˣ) (hp : S.IsGen (p : F) v.asIdeal)
    (hw : w ∉ S.Sf) (hwv : w ≠ v) :
    w.valuation F (p : F) = 1 := by
  have hcount : FractionalIdeal.count F w
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 0 := by
    rw [hp.2.2 w hw]
    exact FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv)
  have hlog := ArtinPrimitiveRoots.A2.qs_nq0_count_spanSingleton_eq_neg_log_valuation
    w (p : F) hp.2.1
  have hlog' : WithZero.log (w.valuation F (p : F)) = 0 := by
    have h := hlog.symm.trans hcount
    linarith
  have hne : w.valuation F (p : F) ≠ 0 :=
    (w.valuation F).ne_zero_iff.mpr hp.2.1
  calc
    w.valuation F (p : F) = WithZero.exp (WithZero.log (w.valuation F (p : F))) :=
      (WithZero.exp_log hne).symm
    _ = 1 := by rw [hlog']; simp

/-- The archimedean factor in `S.e` is the trace exponential, without any integrality condition. -/
theorem arch_exp_eq_trace [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F, psiC (w.embedding z)) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  unfold psiC
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F,
        -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I *
          ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
            rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
      rw [ArtinPrimitiveRoots.Proofs.a1_dual_p.arch_trace_eq_two_real_sum]
      ring

/-- Global triviality identifies the character at an omitted finite place with the inverse of
the finite-plus-archimedean character on `F`. -/
theorem globalCharacterInverse (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (v : FinPlace F) (hv : v ∉ S.Sf) (z : F)
    (hout : ∀ w : FinPlace F, w ∉ S.Sf → w ≠ v → w.valuation F z ≤ 1) :
    A.ψ v (algebraMap F (v.adicCompletion F) z) =
      (S.e A (S.diag z))⁻¹ := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  let f : FinPlace F → ℂ := fun w =>
    A.ψ w (algebraMap F (w.adicCompletion F) z)
  have houtside (w : FinPlace F) (hw : w ∉ S.Sf) (hwv : w ≠ v) : f w = 1 := by
    have hmem : (algebraMap F (w.adicCompletion F) z) ∈ w.adicCompletionIntegers F := by
      change ((z : F) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hout w hw hwv
    exact A.integral w _ hmem
  let e : {w : FinPlace F // w ∈ S.Sf} ↪ PLift (FinPlace F) :=
    ⟨fun w => PLift.up w.1, fun a b h => Subtype.ext (congrArg PLift.down h)⟩
  let s : Finset (PLift (FinPlace F)) := insert (PLift.up v) (S.Sf.attach.map e)
  have hsupp : Function.mulSupport (f ∘ PLift.down) ⊆ s := by
    intro x hx
    change f x.down ≠ 1 at hx
    by_cases hxv : x.down = v
    · change x ∈ s
      apply Finset.mem_insert.mpr
      left
      cases x
      exact congrArg PLift.up hxv
    · by_cases hxS : x.down ∈ S.Sf
      · change x ∈ s
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_map.mpr
        refine ⟨⟨x.down, hxS⟩, Finset.mem_attach _ _, ?_⟩
        cases x
        rfl
      · exact (hx (houtside x.down hxS hxv)).elim
  have hnot : PLift.up v ∉ S.Sf.attach.map e := by
    intro hm
    rcases Finset.mem_map.mp hm with ⟨w, hw, heq⟩
    have hwv : (w : FinPlace F) = v := congrArg PLift.down heq
    exact hv (hwv ▸ w.property)
  have hprodS : (S.Sf.attach.map e).prod (fun x => f x.down) =
      ∏ w : S.Sf, f w := by
    rw [Finset.prod_map]
    apply Finset.prod_congr rfl
    intro w hw
    rfl
  have hfinprod : (∏ᶠ w, f w) = f v * ∏ w : S.Sf, f w := by
    rw [finprod_eq_prod_plift_of_mulSupport_subset hsupp]
    dsimp [s]
    rw [Finset.prod_insert hnot, hprodS]
    rfl
  have hglobal := (A.trivial_on_F z).2
  have harch := arch_exp_eq_trace z
  have hprod : f v * S.e A (S.diag z) = 1 := by
    change f v * ((∏ w : S.Sf, A.ψ w.1
        (algebraMap F (w.1.adicCompletion F) z)) *
        ∏ w : InfinitePlace F, psiC (w.embedding z)) = 1
    calc
      _ = (f v * ∏ w : S.Sf, f w) *
          ∏ w : InfinitePlace F, psiC (w.embedding z) := by ring
      _ = (∏ᶠ w, f w) * Complex.exp
          (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
            rw [← hfinprod, harch]
      _ = 1 := hglobal
  change f v = (S.e A (S.diag z))⁻¹
  exact eq_inv_of_mul_eq_one_left hprod

/-- The ring of integers of the completion is compact; its residue field is the given finite
residue field. -/
theorem completion_integers_compact (v : FinPlace F) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
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
  have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  rw [hset]
  exact hproper.isCompact_closedBall 0 1

/-- Integer powers of a local uniformizer have the expected discrete valuation. -/
theorem uniformizer_zpow_valuation (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    Valued.v ((π : v.adicCompletion F) ^ n) =
      WithZero.exp (-n) := by
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  congr 1
  simp

/-- Natural powers of a local uniformizer have the expected discrete valuation. -/
theorem unit_nat_valuation (v : FinPlace F) (π : (v.adicCompletion F)ˣ) (m : ℤ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp m) (n : ℕ) :
    Valued.v ((π : v.adicCompletion F) ^ n) =
      WithZero.exp ((n : ℤ) * m) := by
  calc
    Valued.v ((π : v.adicCompletion F) ^ n) = WithZero.exp m ^ n := by
      rw [map_pow, hπ]
    _ = WithZero.exp ((n : ℤ) * m) := by
      simpa [zsmul_eq_mul] using (WithZero.exp_zsmul (n : ℤ) m).symm

/-- Natural powers of a local uniformizer have the expected discrete valuation. -/
theorem uniformizer_nat_valuation (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    Valued.v ((π : v.adicCompletion F) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  simpa using unit_nat_valuation v π (-1) hπ n

theorem uniformizer_nat_coe_valuation (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp (-(n : ℤ)) := by
  change Valued.v ((π : v.adicCompletion F) ^ n) = _
  exact uniformizer_nat_valuation v π hπ n

theorem unit_nat_coe_valuation (v : FinPlace F) (π : (v.adicCompletion F)ˣ) (m : ℤ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp m) (n : ℕ) :
    Valued.v ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      WithZero.exp ((n : ℤ) * m) := by
  change Valued.v ((π : v.adicCompletion F) ^ n) = _
  exact unit_nat_valuation v π m hπ n

/-- A finite-radius valuation ball is the scalar image of the integer ring. -/
theorem localBall_eq_inv_uniformizer_image (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    localBall v n =
      (fun x : v.adicCompletion F => ((π⁻¹ ^ n : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) * x) '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  constructor
  · intro hx
    have hy : ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈
        v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((π : v.adicCompletion F) ^ n) * x) ≤ 1
      rw [map_mul, uniformizer_nat_valuation v π hπ n]
      calc
        WithZero.exp (-(n : ℤ)) * Valued.v x ≤
            WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := by
              gcongr
              change Valued.v x ≤ WithZero.exp (n : ℤ) at hx
              exact hx
        _ = 1 := by rw [← WithZero.exp_add]; simp
    refine ⟨((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x, hy, ?_⟩
    simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    change Valued.v (((π⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) ≤
      WithZero.exp (n : ℤ)
    have hπinv :
        Valued.v ((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          WithZero.exp (1 : ℤ) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]
    rw [map_mul, unit_nat_coe_valuation v π⁻¹ 1 hπinv n]
    have hy' : Valued.v y ≤ 1 := by
      change Valued.v y ≤ 1 at hy
      exact hy
    calc
      WithZero.exp ((n : ℤ) * 1) * Valued.v y ≤
          WithZero.exp ((n : ℤ) * 1) * 1 := by gcongr
      _ = WithZero.exp (n : ℤ) := by simp

/-- Finite-radius balls are compact in the finite-residue local completion. -/
theorem localBall_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    IsCompact (localBall v n) := by
  rw [localBall_eq_inv_uniformizer_image v π hπ n]
  exact (completion_integers_compact v).image
    (continuous_const_mul (((π⁻¹ ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F)))

theorem localBall_open (v : FinPlace F) (n : ℕ) : IsOpen (localBall v n) := by
  change IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (n : ℤ)}
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

/-- The shell between the natural-radius balls at `n` and `n+1`. -/
def localShell (v : FinPlace F) (n : ℕ) : Set (v.adicCompletion F) :=
  localBall v (n + 1) \ localBall v n

theorem localShell_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    IsCompact (localShell v n) := by
  have hB : IsCompact (localBall v (n + 1)) := localBall_compact v π hπ _
  have hclosed : IsClosed (localShell v n) := by
    exact hB.isClosed.inter (localBall_open v n).isClosed_compl
  exact hB.of_isClosed_subset hclosed Set.sdiff_subset

theorem localShell_iff_valuation (v : FinPlace F) (x : v.adicCompletion F) (n : ℕ) :
    x ∈ localShell v n ↔ Valued.v x = WithZero.exp ((n + 1 : ℕ) : ℤ) := by
  change Valued.v x ≤ WithZero.exp ((n + 1 : ℕ) : ℤ) ∧
    ¬ Valued.v x ≤ WithZero.exp (n : ℤ) ↔ _
  constructor
  · rintro ⟨hle, hnot⟩
    have hne : Valued.v x ≠ 0 := by
      intro hz
      apply hnot
      rw [hz]
      exact bot_le
    lift Valued.v x to ℤ using hne with z hz
    have hzle : z ≤ (n + 1 : ℕ) := (WithZero.exp_le_exp.mp hle)
    have hzgt : n < z := by
      by_contra h
      apply hnot
      exact WithZero.exp_le_exp.mpr (by omega)
    have hzEq : z = (n + 1 : ℕ) := by omega
    simpa [hzEq]
  · intro hx
    constructor
    · rw [hx]
    · rw [hx]
      intro h
      have hn : ((n + 1 : ℕ) : ℤ) ≤ (n : ℤ) := WithZero.exp_le_exp.mp h
      omega

/-- The open maximal-ideal ball in the completion. -/
def primeBall (v : FinPlace F) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp (-1 : ℤ)}

/-- A local uniformizer maps the integer ring onto the maximal-ideal ball. -/
theorem primeBall_eq_uniformizer_image (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    primeBall v = (fun x : v.adicCompletion F => (π : v.adicCompletion F) * x) ''
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  constructor
  · intro hx
    have hy : ((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ∈
        v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ≤ 1
      rw [map_mul]
      have hπinv : Valued.v ((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          WithZero.exp (1 : ℤ) := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]
      rw [hπinv]
      calc
        WithZero.exp (1 : ℤ) * Valued.v x ≤
            WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := by
              gcongr
              exact hx
        _ = 1 := by rw [← WithZero.exp_add]; simp
    refine ⟨((π⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x, hy, ?_⟩
    simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    change Valued.v ((π : v.adicCompletion F) * y) ≤ WithZero.exp (-1 : ℤ)
    rw [map_mul, hπ]
    have hy' : Valued.v y ≤ 1 := by
      change Valued.v y ≤ 1 at hy
      exact hy
    calc
      WithZero.exp (-1 : ℤ) * Valued.v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ = WithZero.exp (-1 : ℤ) := by simp

theorem primeBall_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    IsCompact (primeBall v) := by
  rw [primeBall_eq_uniformizer_image v π hπ]
  exact (completion_integers_compact v).image (continuous_const_mul (π : v.adicCompletion F))

theorem primeBall_measurable (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    MeasurableSet (primeBall v) := (primeBall_compact v π hπ).measurableSet

theorem primeBall_open (v : FinPlace F) : IsOpen (primeBall v) := by
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

theorem valued_lt_one_iff_primeBall (v : FinPlace F) (x : v.adicCompletion F) :
    Valued.v x < 1 ↔ x ∈ primeBall v := by
  change Valued.v x < 1 ↔ Valued.v x ≤ WithZero.exp (-1 : ℤ)
  by_cases hx : Valued.v x = 0
  · simp [hx]
  · lift Valued.v x to ℤ using hx with n hn
    simp only [← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem completionMaximalIdeal_iff_primeBall (v : FinPlace F)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    (⟨x, hx⟩ : v.adicCompletionIntegers F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔ x ∈ primeBall v := by
  let K := v.adicCompletion F
  change (⟨x, hx⟩ : (Valued.v : Valuation K
    (WithZero (Multiplicative ℤ))).valuationSubring) ∈
      IsLocalRing.maximalIdeal ((Valued.v : Valuation K
        (WithZero (Multiplicative ℤ))).valuationSubring) ↔ _
  rw [Valuation.mem_maximalIdeal_iff]
  exact valued_lt_one_iff_primeBall v x

/-- Recover the residue field of a completion from the residue quotient of its integer ring. -/
noncomputable def completionResidueMap (v : FinPlace F) :
    v.adicCompletionIntegers F →+* (𝓞 F ⧸ v.asIdeal) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  exact e.symm.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal
    (v.adicCompletionIntegers F)))

/-- Canonical lift to the completion integer ring of a residue class. -/
noncomputable def completionResidueCenter (v : FinPlace F) (r : 𝓞 F ⧸ v.asIdeal) :
    v.adicCompletionIntegers F :=
  algebraMap (𝓞 F) (v.adicCompletionIntegers F) r.out

theorem completionResidueMap_center (v : FinPlace F) (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueMap v (completionResidueCenter v r) = r := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  have hmap := v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r.out
  change e.symm (Ideal.Quotient.mk M
    (algebraMap (𝓞 F) (v.adicCompletionIntegers F) r.out)) = r
  rw [← hmap]
  simp [e]

theorem completionResidueMap_eq_zero_iff (v : FinPlace F)
    (x : v.adicCompletionIntegers F) :
    completionResidueMap v x = 0 ↔ x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  change e.symm (Ideal.Quotient.mk M x) = 0 ↔ x ∈ M
  constructor
  · intro h
    have hq : Ideal.Quotient.mk M x = 0 := by
      have heq := congrArg e h
      simpa [e] using heq
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro h
    have hq : Ideal.Quotient.mk M x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    simpa [e] using congrArg e.symm hq

theorem completionResidueMap_algebraMap (v : FinPlace F) (a : 𝓞 F) :
    completionResidueMap v (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) =
      Ideal.Quotient.mk v.asIdeal a := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  have hmap := v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) a
  change e.symm (Ideal.Quotient.mk M (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a)) = _
  calc
    _ = e.symm (e (Ideal.Quotient.mk v.asIdeal a)) := by rw [hmap]
    _ = Ideal.Quotient.mk v.asIdeal a := e.symm_apply_apply _

theorem completionResidueCenter_isUnit (v : FinPlace F) (r : 𝓞 F ⧸ v.asIdeal)
    (hr : r ≠ 0) : IsUnit (completionResidueCenter v r) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  have hnotM : completionResidueCenter v r ∉
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro hM
    have hzero := (completionResidueMap_eq_zero_iff v (completionResidueCenter v r)).2 hM
    rw [completionResidueMap_center v r] at hzero
    exact hr hzero
  exact (IsLocalRing.notMem_maximalIdeal).mp hnotM

theorem completionResidueMap_eq_iff (v : FinPlace F) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueMap v ⟨x, hx⟩ = r ↔
      (⟨x, hx⟩ - completionResidueCenter v r : v.adicCompletionIntegers F) ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let M := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
  let e := v.residueFieldEquivAdicCompletionIntegers (K := F)
  have hcenter : e r = Ideal.Quotient.mk M (completionResidueCenter v r) := by
    simpa [e, completionResidueCenter] using
      (v.residueFieldEquivAdicCompletionIntegers_apply_mk (K := F) r.out)
  change e.symm (Ideal.Quotient.mk M ⟨x, hx⟩) = r ↔ _
  constructor
  · intro h
    have heq : Ideal.Quotient.mk M ⟨x, hx⟩ = e r := by
      simpa [completionResidueMap, e] using congrArg e h
    rw [hcenter] at heq
    exact Ideal.Quotient.eq.mp heq
  · intro h
    have hq : Ideal.Quotient.mk M ⟨x, hx⟩ =
        Ideal.Quotient.mk M (completionResidueCenter v r) := Ideal.Quotient.eq.mpr h
    have heq : e.symm (Ideal.Quotient.mk M ⟨x, hx⟩) = r := by
      calc
        e.symm (Ideal.Quotient.mk M ⟨x, hx⟩) =
            e.symm (Ideal.Quotient.mk M (completionResidueCenter v r)) :=
          congrArg e.symm hq
        _ = e.symm (e r) := by rw [hcenter.symm]
        _ = r := e.symm_apply_apply r
    simpa [completionResidueMap, e] using heq

theorem completionResidueMap_eq_iff_primeBall (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F)
    (r : 𝓞 F ⧸ v.asIdeal) :
    completionResidueMap v ⟨x, hx⟩ = r ↔
      x - (completionResidueCenter v r : v.adicCompletion F) ∈ primeBall v := by
  rw [completionResidueMap_eq_iff]
  have hd : x - (completionResidueCenter v r : v.adicCompletion F) ∈
      v.adicCompletionIntegers F := by
    exact (v.adicCompletionIntegers F).sub_mem hx (completionResidueCenter v r).property
  have hsub : (⟨x, hx⟩ - completionResidueCenter v r : v.adicCompletionIntegers F) =
      ⟨x - (completionResidueCenter v r : v.adicCompletion F), hd⟩ := by
    apply Subtype.ext
    rfl
  rw [hsub]
  exact completionMaximalIdeal_iff_primeBall v _ hd

/-- The radius-one maximal ideal, viewed as an additive subgroup of the completion. -/
def primeBallSubgroup (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    AddSubgroup (v.adicCompletion F) where
  carrier := primeBall v
  zero_mem' := by simp [primeBall]
  add_mem' := by
    intro x y hx hy
    rw [primeBall_eq_uniformizer_image v π hπ] at hx hy ⊢
    rcases hx with ⟨a, ha, rfl⟩
    rcases hy with ⟨b, hb, rfl⟩
    refine ⟨a + b, (v.adicCompletionIntegers F).add_mem a b ha hb, ?_⟩
    simp [mul_add]
  neg_mem' := by
    intro x hx
    rw [primeBall_eq_uniformizer_image v π hπ] at hx ⊢
    rcases hx with ⟨a, ha, rfl⟩
    refine ⟨-a, (v.adicCompletionIntegers F).neg_mem a ha, ?_⟩
    simp

/-- The residue-angular piece of a nonzero valuation shell. -/
noncomputable def localShellResidueFiber (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (n : ℕ) (r : (𝓞 F ⧸ v.asIdeal)ˣ) : Set (v.adicCompletion F) :=
  {x | (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x -
      (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)) ∈ primeBall v}

theorem localShellResidueFiber_add_iff (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (r : (𝓞 F ⧸ v.asIdeal)ˣ) (δ x : v.adicCompletion F)
    (hδ : (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * δ) ∈
      primeBallSubgroup v π hπ) :
    x + δ ∈ localShellResidueFiber v π n r ↔ x ∈ localShellResidueFiber v π n r := by
  change ((((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (x + δ) -
    (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)) ∈ primeBall v) ↔
      (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x -
        (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)) ∈ primeBall v
  let u : v.adicCompletion F :=
    ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x -
      (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)
  let q : v.adicCompletion F :=
    ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * δ
  have heq :
      (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * (x + δ) -
        (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)) = u + q := by
    dsimp [u, q]
    ring
  rw [heq]
  change u + q ∈ primeBallSubgroup v π hπ ↔ u ∈ primeBallSubgroup v π hπ
  constructor
  · intro h
    have hneg : -q ∈ primeBallSubgroup v π hπ :=
      (primeBallSubgroup v π hπ).neg_mem hδ
    have hsum : (u + q) + -q ∈ primeBallSubgroup v π hπ :=
      (primeBallSubgroup v π hπ).add_mem h hneg
    simpa using hsum
  · intro h
    exact (primeBallSubgroup v π hπ).add_mem h hδ

theorem localShellResidueFiber_subset_shell (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (r : (𝓞 F ⧸ v.asIdeal)ˣ) : localShellResidueFiber v π n r ⊆ localShell v n := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  intro x hx
  let c := completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal)
  let u := ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x
  have hdO : u - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v (u - (c : v.adicCompletion F)) ≤ 1
    have hle : Valued.v (u - (c : v.adicCompletion F)) ≤ WithZero.exp (-1 : ℤ) := hx
    exact hle.trans (by simp)
  have huO : u ∈ v.adicCompletionIntegers F := by
    have hadd := (v.adicCompletionIntegers F).add_mem (u - (c : v.adicCompletion F)) c
      hdO c.property
    simpa [sub_add_cancel] using hadd
  have hcond : u - (completionResidueCenter v r.val : v.adicCompletion F) ∈ primeBall v := by
    simpa [localShellResidueFiber, u, c] using hx
  have hres := (completionResidueMap_eq_iff_primeBall v π hπ u huO r.val).mpr hcond
  have hnotM : (⟨u, huO⟩ : v.adicCompletionIntegers F) ∉
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro hM
    have hzero := (completionResidueMap_eq_zero_iff v ⟨u, huO⟩).2 hM
    rw [hres] at hzero
    exact r.ne_zero hzero
  have hle : Valued.v u ≤ 1 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at huO
    exact huO
  have hnotlt : ¬ Valued.v u < 1 := by
    intro hlt
    apply hnotM
    exact (completionMaximalIdeal_iff_primeBall v u huO).2
      ((valued_lt_one_iff_primeBall v u).mp hlt)
  have huval : Valued.v u = 1 := le_antisymm hle (le_of_not_gt hnotlt)
  have hxval : Valued.v x = WithZero.exp ((n + 1 : ℕ) : ℤ) := by
    have hprod : WithZero.exp (-((n + 1 : ℕ) : ℤ)) * Valued.v x = 1 := by
      dsimp [u] at huval
      rw [map_mul, uniformizer_nat_valuation v π hπ (n + 1)] at huval
      exact huval
    have hcancel : WithZero.exp (-((n + 1 : ℕ) : ℤ)) * Valued.v x =
        WithZero.exp (-((n + 1 : ℕ) : ℤ)) *
          WithZero.exp (((n + 1 : ℕ) : ℤ)) := by
      rw [hprod, ← WithZero.exp_add]
      simp
    have hfac : WithZero.exp (-((n + 1 : ℕ) : ℤ)) ≠ 0 := by simp
    exact mul_left_cancel₀ hfac hcancel
  exact (localShell_iff_valuation v x n).mpr hxval

theorem localShell_eq_iUnion_residueFibers (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    localShell v n = ⋃ r : (𝓞 F ⧸ v.asIdeal)ˣ, localShellResidueFiber v π n r := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let k := 𝓞 F ⧸ v.asIdeal
  letI : Field k := Ideal.Quotient.field v.asIdeal
  ext x
  constructor
  · intro hx
    have hxval := (localShell_iff_valuation v x n).mp hx
    let u := ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x
    have huval : Valued.v u = 1 := by
      dsimp [u]
      rw [map_mul, uniformizer_nat_valuation v π hπ (n + 1), hxval]
      rw [← WithZero.exp_add]
      simp
    have huO : u ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, huval]
    let q := completionResidueMap v ⟨u, huO⟩
    have hqne : q ≠ 0 := by
      intro hq
      have huM : (⟨u, huO⟩ : v.adicCompletionIntegers F) ∈
          IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
        (completionResidueMap_eq_zero_iff v ⟨u, huO⟩).mp hq
      have hb := (completionMaximalIdeal_iff_primeBall v u huO).mp huM
      have hlt := (valued_lt_one_iff_primeBall v u).mpr hb
      rw [huval] at hlt
      exact (lt_irrefl 1) hlt
    let r : kˣ := Units.mk0 q hqne
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    have hres := completionResidueMap_eq_iff_primeBall v π hπ u huO (r : k)
    have hq : q = (r : k) := by simp [r]
    exact hres.mp hq
  · rintro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact localShellResidueFiber_subset_shell v π hπ n r hr

theorem localShellResidueFibers_pairwise (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    Pairwise (fun r s => Disjoint (localShellResidueFiber v π n r)
      (localShellResidueFiber v π n s)) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let k := 𝓞 F ⧸ v.asIdeal
  letI : Field k := Ideal.Quotient.field v.asIdeal
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro x hx hy
  let k := 𝓞 F ⧸ v.asIdeal
  let u := ((π ^ (n + 1 : ℕ) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x
  have hxShell := localShellResidueFiber_subset_shell v π hπ n r hx
  have hxval := (localShell_iff_valuation v x n).mp hxShell
  have huval : Valued.v u = 1 := by
    dsimp [u]
    rw [map_mul, uniformizer_nat_valuation v π hπ (n + 1), hxval]
    rw [← WithZero.exp_add]
    simp
  have huO : u ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, huval]
  have hrq := (completionResidueMap_eq_iff_primeBall v π hπ u huO r.val).mpr hx
  have hsq := (completionResidueMap_eq_iff_primeBall v π hπ u huO s.val).mpr hy
  have hval : (r : k) = (s : k) := hrq.symm.trans hsq
  exact hrs (Units.ext hval)

theorem localShellResidueFiber_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (r : (𝓞 F ⧸ v.asIdeal)ˣ) : IsCompact (localShellResidueFiber v π n r) := by
  let f : v.adicCompletion F → v.adicCompletion F := fun x =>
    ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x -
      (completionResidueCenter v (r : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F)
  have hf : Continuous f := by fun_prop
  have hclosed : IsClosed (localShellResidueFiber v π n r) := by
    dsimp [localShellResidueFiber]
    exact (primeBall_compact v π hπ).isClosed.preimage hf
  exact (localShell_compact v π hπ n).of_isClosed_subset hclosed
    (localShellResidueFiber_subset_shell v π hπ n r)

theorem localShellResidueFiber_measurable (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (r : (𝓞 F ⧸ v.asIdeal)ˣ) :
    MeasurableSet (localShellResidueFiber v π n r) :=
  (localShellResidueFiber_compact v π hπ n r).measurableSet

/-- A residue class inside the integer ring of the completion. -/
def localIntResidueFiber (v : FinPlace F) (r : 𝓞 F ⧸ v.asIdeal) :
    Set (v.adicCompletion F) :=
  {x | x ∈ v.adicCompletionIntegers F ∧
    x - (completionResidueCenter v r : v.adicCompletion F) ∈ primeBall v}

theorem primeBall_subset_integers (v : FinPlace F) :
    primeBall v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  change Valued.v x ≤ 1
  change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
  exact hx.trans (by simp)

theorem localIntResidueFiber_eq_translate (v : FinPlace F)
    (r : 𝓞 F ⧸ v.asIdeal) :
    localIntResidueFiber v r =
      (fun x : v.adicCompletion F => x + (completionResidueCenter v r : v.adicCompletion F)) ''
        primeBall v := by
  ext x
  constructor
  · rintro ⟨hxO, hx⟩
    refine ⟨x - (completionResidueCenter v r : v.adicCompletion F), hx, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    constructor
    · exact (v.adicCompletionIntegers F).add_mem y (completionResidueCenter v r)
        (primeBall_subset_integers v hy) (completionResidueCenter v r).property
    · simpa using hy

theorem localIntResidueFiber_compact (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (r : 𝓞 F ⧸ v.asIdeal) :
    IsCompact (localIntResidueFiber v r) := by
  rw [localIntResidueFiber_eq_translate]
  exact (primeBall_compact v π hπ).image
    (continuous_id.add continuous_const)

theorem localIntResidueFiber_measurable (v : FinPlace F) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (r : 𝓞 F ⧸ v.asIdeal) :
    MeasurableSet (localIntResidueFiber v r) :=
  (localIntResidueFiber_compact v π hπ r).measurableSet

theorem localIntResidueFiber_pairwise (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    Pairwise fun r s => Disjoint (localIntResidueFiber v r) (localIntResidueFiber v s) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hr := (completionResidueMap_eq_iff_primeBall v π hπ x hx.1 r).2 hx.2
  have hs := (completionResidueMap_eq_iff_primeBall v π hπ x hy.1 s).2 hy.2
  exact hrs (hr.symm.trans hs)

theorem localIntResidueFiber_iUnion (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    (⋃ r : 𝓞 F ⧸ v.asIdeal, localIntResidueFiber v r) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact hr.1
  · intro hx
    let r := completionResidueMap v ⟨x, hx⟩
    apply Set.mem_iUnion.mpr ⟨r, ?_⟩
    refine ⟨hx, ?_⟩
    exact (completionResidueMap_eq_iff_primeBall v π hπ x hx r).mp rfl

theorem localIntResidueFiber_measure (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (r : 𝓞 F ⧸ v.asIdeal) : μ.real (localIntResidueFiber v r) = μ.real (primeBall v) := by
  letI : Measure.IsAddHaarMeasure μ := hμ
  rw [localIntResidueFiber_eq_translate]
  let c : v.adicCompletion F := completionResidueCenter v r
  have himage : (fun x : v.adicCompletion F => x + c) '' primeBall v =
      (fun x : v.adicCompletion F => x - c) ⁻¹' primeBall v := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      refine ⟨x - c, hx, ?_⟩
      simp
  have hmeasure : μ ((fun x : v.adicCompletion F => x + c) '' primeBall v) =
      μ (primeBall v) := by
    rw [himage]
    simpa only [sub_eq_add_neg] using
      MeasureTheory.measure_preimage_add_right μ (-c) (primeBall v)
  exact congrArg ENNReal.toReal hmeasure

theorem localIntResidueFiber_measure_sum (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    [Fintype (𝓞 F ⧸ v.asIdeal)] :
    μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      ∑ r : 𝓞 F ⧸ v.asIdeal, μ.real (localIntResidueFiber v r) := by
  letI : Measure.IsAddHaarMeasure μ := hμ
  rw [← localIntResidueFiber_iUnion v π hπ]
  have hfinite (r : 𝓞 F ⧸ v.asIdeal) : μ (localIntResidueFiber v r) ≠ ⊤ :=
    (localIntResidueFiber_compact v π hπ r).measure_ne_top
  exact MeasureTheory.measureReal_iUnion_fintype
    (localIntResidueFiber_pairwise v π hπ)
    (fun r => localIntResidueFiber_measurable v π hπ r) hfinite

theorem completionIntegerCast (v : FinPlace F) (a : 𝓞 F) :
    (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (a : F) := by
  change ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) a :
    v.adicCompletionIntegers F) : v.adicCompletion F) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply
    (R := 𝓞 F) (K := F) v a]
  rfl

theorem globalIntegerImage_mem_completion (v : FinPlace F) (a : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (a : F) ∈ v.adicCompletionIntegers F := by
  rw [← completionIntegerCast v a]
  exact (algebraMap (𝓞 F) (v.adicCompletionIntegers F) a).property

theorem absFin_toLoc_inv (v : FinPlace F) (p : Fˣ)
    (hπ : Valued.v (toLoc v p : v.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    absFin v (toLoc v (p⁻¹) : v.adicCompletion F) =
      (Ideal.absNorm v.asIdeal : ℝ) := by
  have hval : Valued.v (toLoc v (p⁻¹) : v.adicCompletion F) =
      WithZero.exp (1 : ℤ) := by
    have hinv : toLoc v (p⁻¹) = (toLoc v p)⁻¹ := by simp
    rw [hinv, Units.val_inv_eq_inv_val, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg]
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hval,
    WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp),
    WithZero.toAdd_unzero_eq_log (by simp)]
  simp

set_option maxHeartbeats 5000000
theorem quadraticIntFiber_phase_eq (A : AddCharData F) (v : FinPlace F)
    (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (p : Fˣ) (hπp : π = toLoc v p)
    (r : 𝓞 F ⧸ v.asIdeal) (x : v.adicCompletion F)
    (hx : x ∈ localIntResidueFiber v r) :
    A.ψ v (((toLoc v (p⁻¹) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2) =
      A.ψ v (((toLoc v (p⁻¹) : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        (completionResidueCenter v r : v.adicCompletion F) ^ 2) := by
  let c : (v.adicCompletion F)ˣ := toLoc v (p⁻¹)
  have hc : c = π⁻¹ := by simp [c, hπp]
  have hball : x - (completionResidueCenter v r : v.adicCompletion F) ∈
      (fun y : v.adicCompletion F => (π : v.adicCompletion F) * y) ''
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [← primeBall_eq_uniformizer_image v π hπ]
    exact hx.2
  obtain ⟨s, hsO, hsEq⟩ := hball
  have hsEq' : (π : v.adicCompletion F) * s =
      x - (completionResidueCenter v r : v.adicCompletion F) := by
    change (π : v.adicCompletion F) * s = _
    exact hsEq
  have hxeq : x = (completionResidueCenter v r : v.adicCompletion F) +
      (π : v.adicCompletion F) * s := by
    calc
      x = (x - (completionResidueCenter v r : v.adicCompletion F)) +
          completionResidueCenter v r := by ring
      _ = (π : v.adicCompletion F) * s + completionResidueCenter v r := by rw [hsEq']
      _ = _ := by ring
  have hcinv : (c : v.adicCompletion F) * (π : v.adicCompletion F) = 1 := by
    rw [hc]
    rw [Units.val_inv_eq_inv_val]
    exact inv_mul_cancel₀ (Units.ne_zero π)
  have hcross : (c : v.adicCompletion F) *
      (completionResidueCenter v r : v.adicCompletion F) * (π : v.adicCompletion F) =
        (completionResidueCenter v r : v.adicCompletion F) := by
    calc
      _ = (completionResidueCenter v r : v.adicCompletion F) *
          ((c : v.adicCompletion F) * (π : v.adicCompletion F)) := by ring
      _ = _ := by rw [hcinv, mul_one]
  have hcross2 : (c : v.adicCompletion F) * (π : v.adicCompletion F) *
      (π : v.adicCompletion F) = (π : v.adicCompletion F) := by
    calc
      _ = ((c : v.adicCompletion F) * (π : v.adicCompletion F)) *
          (π : v.adicCompletion F) := by ring
      _ = _ := by rw [hcinv, one_mul]
  have harg : (c : v.adicCompletion F) * x ^ 2 =
      (c : v.adicCompletion F) * (completionResidueCenter v r : v.adicCompletion F) ^ 2 +
        ((2 : v.adicCompletion F) *
          (completionResidueCenter v r : v.adicCompletion F) * s +
          (π : v.adicCompletion F) * s ^ 2) := by
    rw [hxeq]
    calc
      _ = (c : v.adicCompletion F) * (completionResidueCenter v r : v.adicCompletion F) ^ 2 +
          2 * ((c : v.adicCompletion F) *
            (completionResidueCenter v r : v.adicCompletion F) * (π : v.adicCompletion F)) * s +
          ((c : v.adicCompletion F) * (π : v.adicCompletion F) *
            (π : v.adicCompletion F)) * s ^ 2 := by ring
      _ = _ := by rw [hcross, hcross2]; ring
  have h2O : (2 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    simpa using globalIntegerImage_mem_completion v (2 : 𝓞 F)
  have hπO : (π : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    change Valued.v (π : v.adicCompletion F) ≤ 1
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hs2O : s ^ 2 ∈ v.adicCompletionIntegers F := by
    simpa [pow_two] using
      (v.adicCompletionIntegers F).mul_mem s s hsO hsO
  have hcorr : (2 : v.adicCompletion F) *
      (completionResidueCenter v r : v.adicCompletion F) * s +
        (π : v.adicCompletion F) * s ^ 2 ∈ v.adicCompletionIntegers F := by
    apply (v.adicCompletionIntegers F).add_mem
    · exact (v.adicCompletionIntegers F).mul_mem
        ((2 : v.adicCompletion F) * (completionResidueCenter v r : v.adicCompletion F)) s
        ((v.adicCompletionIntegers F).mul_mem (2 : v.adicCompletion F)
          (completionResidueCenter v r : v.adicCompletion F) h2O
          (completionResidueCenter v r).property) hsO
    · exact (v.adicCompletionIntegers F).mul_mem (π : v.adicCompletion F) (s ^ 2) hπO hs2O
  rw [harg, (A.ψ v).map_add_eq_mul, A.integral v _ hcorr, mul_one]

set_option maxHeartbeats 1000000
/-- The quadratic oscillatory integral vanishes on every outer shell. The proof splits the shell
by the nonzero residue of `π^(n+1) x` and translates each fiber by a residue-dependent small shift. -/
theorem quadraticShellIntegralZero (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (p : Fˣ)
    (hπ : Valued.v (toLoc v p : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (b : 𝓞 F)
    (hψ : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 1)
    (n j : ℕ) (hj : j ≤ 1) :
    (∫ x in localShell v n,
      A.ψ v (((toLoc v (p⁻¹ ^ j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
        ∂μ) = 0 := by
  classical
  letI : Measure.IsAddHaarMeasure μ := hμ
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let k := 𝓞 F ⧸ v.asIdeal
  letI : Field k := Ideal.Quotient.field v.asIdeal
  letI : Finite k := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype k := Fintype.ofFinite k
  let π : (v.adicCompletion F)ˣ := toLoc v p
  have hπ' : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    simpa [π, toLoc] using hπ
  have hπle : Valued.v (π : v.adicCompletion F) ≤ 1 := by
    rw [hπ', ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  let c : (v.adicCompletion F)ˣ := toLoc v (p⁻¹ ^ j)
  have hc : c = π⁻¹ ^ j := by simp [c, π]
  have hjcases : j = 0 ∨ j = 1 := by omega
  have hscale : c * π ^ (n + j) = π ^ n := by
    rw [hc]
    rcases hjcases with hj0 | hj1
    · subst j
      simp
    · subst j
      simp only [pow_one]
      rw [pow_succ]
      group
  let f : v.adicCompletion F → ℂ := fun x =>
    A.ψ v (((c : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
  have hfcont : Continuous f := by
    have hψcont : Continuous (A.ψ v) :=
      (local_character_regular D A v).1
    apply hψcont.comp
    fun_prop
  have hfiberInt (r : kˣ) :
      IntegrableOn f (localShellResidueFiber v π n r) μ :=
    hfcont.continuousOn.integrableOn_compact
      (localShellResidueFiber_compact v π hπ' n r)
  have hfiberZero (r : kˣ) :
      (∫ x in localShellResidueFiber v π n r, f x ∂μ) = 0 := by
    let center : v.adicCompletionIntegers F := completionResidueCenter v (r : k)
    have hcenterUnit : IsUnit center :=
      completionResidueCenter_isUnit v (r : k) r.ne_zero
    have h2res : (Ideal.Quotient.mk v.asIdeal (2 : 𝓞 F) : k) ≠ 0 := by
      intro h
      exact h2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    let twoO : v.adicCompletionIntegers F := algebraMap (𝓞 F) _ (2 : 𝓞 F)
    have htwoMap := completionResidueMap_algebraMap v (2 : 𝓞 F)
    have htwoNotM : twoO ∉ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      intro hm
      have hz := (completionResidueMap_eq_zero_iff v twoO).2 hm
      rw [htwoMap] at hz
      exact h2res hz
    have htwoUnit : IsUnit twoO := (IsLocalRing.notMem_maximalIdeal).mp htwoNotM
    let dO : v.adicCompletionIntegers F := twoO * center
    have hdUnit : IsUnit dO := htwoUnit.mul hcenterUnit
    let du : (v.adicCompletionIntegers F)ˣ := hdUnit.unit
    have hdu : (du : v.adicCompletionIntegers F) = dO := hdUnit.unit_spec
    let bO : v.adicCompletionIntegers F := algebraMap (𝓞 F) _ b
    let duInv : (v.adicCompletionIntegers F)ˣ := du⁻¹
    let tO : v.adicCompletionIntegers F := (duInv : v.adicCompletionIntegers F) * bO
    have hdt : dO * tO = bO := by
      have hunitU : du * duInv = (1 : (v.adicCompletionIntegers F)ˣ) := by
        dsimp [duInv]
        exact mul_inv_cancel du
      have hunit : (du : v.adicCompletionIntegers F) *
          (duInv : v.adicCompletionIntegers F) = 1 := by
        exact congrArg (fun u : (v.adicCompletionIntegers F)ˣ => (u : v.adicCompletionIntegers F)) hunitU
      rw [← hdu]
      dsimp [tO]
      calc
        _ = ((du : v.adicCompletionIntegers F) * (duInv : v.adicCompletionIntegers F)) * bO := by
          rw [mul_assoc]
        _ = bO := by rw [hunit, one_mul]
    let t : v.adicCompletion F := tO
    have htwoCast : (twoO : v.adicCompletion F) = (2 : v.adicCompletion F) := by
      calc
        (twoO : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (2 : F) := by
          change ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) (2 : 𝓞 F) :
            v.adicCompletionIntegers F) : v.adicCompletion F) = _
          rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply
            (R := 𝓞 F) (K := F) v (2 : 𝓞 F)]
          rfl
        _ = (2 : v.adicCompletion F) := by
          exact map_natCast (algebraMap F (v.adicCompletion F)) 2
    have hdtK : (dO : v.adicCompletion F) * t =
        algebraMap F (v.adicCompletion F) (b : F) := by
      have hmap := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hdt
      have hbcast : (bO : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) (b : F) := by
        change ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) b :
          v.adicCompletionIntegers F) : v.adicCompletion F) = _
        rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply
          (R := 𝓞 F) (K := F) v b]
        change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b) = _
        rfl
      calc
        _ = ((dO * tO : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          change ((dO * tO : v.adicCompletionIntegers F) : v.adicCompletion F) = _
          rfl
        _ = (bO : v.adicCompletion F) := hmap
        _ = _ := hbcast
    have hct : (2 : v.adicCompletion F) * (center : v.adicCompletion F) * t =
        algebraMap F (v.adicCompletion F) (b : F) := by
      calc
        _ = (twoO : v.adicCompletion F) * (center : v.adicCompletion F) * t := by rw [htwoCast]
        _ = (dO : v.adicCompletion F) * t := by simp [dO]
        _ = _ := hdtK
    let delta : v.adicCompletion F :=
      ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t
    have hdeltaEq :
        ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * delta =
          (π : v.adicCompletion F) ^ (2 * n + j + 1) * t := by
      change (π : v.adicCompletion F) ^ (n + 1) *
          ((π : v.adicCompletion F) ^ (n + j) * t) = _
      calc
        _ = ((π : v.adicCompletion F) ^ (n + 1) *
            (π : v.adicCompletion F) ^ (n + j)) * t := by ring
        _ = (π : v.adicCompletion F) ^ ((n + 1) + (n + j)) * t := by rw [← pow_add]
        _ = (π : v.adicCompletion F) ^ (2 * n + j + 1) * t := by
          have hexp : (n + 1) + (n + j) = 2 * n + j + 1 := by omega
          rw [hexp]
    have hpowerPrime (m : ℕ) (hm : 1 ≤ m) (z : v.adicCompletion F)
        (hz : z ∈ v.adicCompletionIntegers F) :
        (π : v.adicCompletion F) ^ m * z ∈ primeBall v := by
      change Valued.v ((π : v.adicCompletion F) ^ m * z) ≤ WithZero.exp (-1 : ℤ)
      rw [map_mul, map_pow]
      have hz' : Valued.v z ≤ 1 := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hz
        exact hz
      have hpowl : (Valued.v (π : v.adicCompletion F)) ^ m ≤ Valued.v (π : v.adicCompletion F) := by
        simpa using pow_le_pow_right_of_le_one' hπle hm
      calc
        (Valued.v (π : v.adicCompletion F)) ^ m * Valued.v z ≤
            Valued.v (π : v.adicCompletion F) * 1 := by
          calc
            _ ≤ Valued.v (π : v.adicCompletion F) * Valued.v z :=
              mul_le_mul_of_nonneg_right hpowl bot_le
            _ ≤ _ := mul_le_mul_of_nonneg_left hz' bot_le
        _ = WithZero.exp (-1 : ℤ) := by rw [hπ']; simp
    have hshift :
        (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * delta) ∈
          primeBallSubgroup v π hπ' := by
      change _ ∈ primeBall v
      rw [hdeltaEq]
      apply hpowerPrime (2 * n + j + 1) (by omega) t tO.property
    have hfiberShift (x : v.adicCompletion F) :
        x + delta ∈ localShellResidueFiber v π n r ↔
          x ∈ localShellResidueFiber v π n r :=
      localShellResidueFiber_add_iff v π hπ' n r delta x hshift
    have hscaleK : (c : v.adicCompletion F) *
        ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      exact congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hscale
    have hcross (y : v.adicCompletion F) :
        (2 : v.adicCompletion F) * (c : v.adicCompletion F) * y * delta =
          (2 : v.adicCompletion F) *
              (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) * t /
                (π : v.adicCompletion F) := by
      calc
        _ = 2 * ((c : v.adicCompletion F) *
            ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * y * t := by ring
        _ = 2 * ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y * t := by
          rw [hscaleK]
        _ = _ := by
          change 2 * (π : v.adicCompletion F) ^ n * y * t =
            2 * ((π : v.adicCompletion F) ^ (n + 1) * y) * t / (π : v.adicCompletion F)
          rw [pow_succ]
          field_simp [Units.ne_zero π]
    have hratio :
        (algebraMap F (v.adicCompletion F) (b : F)) /
            (π : v.adicCompletion F) =
          algebraMap F (v.adicCompletion F) ((b : F) / (p : F)) := by
      change algebraMap F (v.adicCompletion F) (b : F) /
          algebraMap F (v.adicCompletion F) (p : F) = _
      rw [map_div₀]
    have hquadMem : (c : v.adicCompletion F) * delta ^ 2 ∈ v.adicCompletionIntegers F := by
      have hquadEq : (c : v.adicCompletion F) * delta ^ 2 =
          (π : v.adicCompletion F) ^ (2 * n + j) * t ^ 2 := by
        calc
          _ = ((c : v.adicCompletion F) *
              ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
              ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t ^ 2 := by
                change (c : v.adicCompletion F) *
                  (((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t) ^ 2 = _
                ring
          _ = ((π ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
              ((π ^ (n + j) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * t ^ 2 := by
                rw [hscaleK]
          _ = (π : v.adicCompletion F) ^ (2 * n + j) * t ^ 2 := by
                change ((π : v.adicCompletion F) ^ n *
                    (π : v.adicCompletion F) ^ (n + j)) * t ^ 2 = _
                rw [← pow_add]
                have hExp : n + (n + j) = 2 * n + j := by omega
                rw [hExp]
      have hπO : (π : v.adicCompletion F) ^ (2 * n + j) ∈
          v.adicCompletionIntegers F := by
        change Valued.v ((π : v.adicCompletion F) ^ (2 * n + j)) ≤ 1
        rw [map_pow]
        exact Left.pow_le_one_of_le hπle _
      rw [hquadEq]
      have htval : Valued.v t ≤ 1 := by
        have htO : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F := tO.property
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at htO
        exact htO
      have ht2O : t ^ 2 ∈ v.adicCompletionIntegers F := by
        change Valued.v (t ^ 2) ≤ 1
        rw [map_pow]
        exact Left.pow_le_one_of_le htval _
      exact (v.adicCompletionIntegers F).mul_mem
        ((π : v.adicCompletion F) ^ (2 * n + j)) (t ^ 2) hπO ht2O
    have hquadPsi : A.ψ v ((c : v.adicCompletion F) * delta ^ 2) = 1 :=
      A.integral v _ hquadMem
    let lam := A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F)))
    have hphase (y : v.adicCompletion F)
        (hy : y ∈ localShellResidueFiber v π n r) :
        A.ψ v ((c : v.adicCompletion F) * (y + delta) ^ 2) = lam *
          A.ψ v ((c : v.adicCompletion F) * y ^ 2) := by
      have hcond :
          (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y -
            (center : v.adicCompletion F)) ∈ primeBall v := by
        simpa [localShellResidueFiber] using hy
      have hcond' :
          (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y -
            (center : v.adicCompletion F)) ∈
            (fun x : v.adicCompletion F => (π : v.adicCompletion F) * x) ''
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [← primeBall_eq_uniformizer_image v π hπ']
        exact hcond
      obtain ⟨s, hsO, hsEq⟩ := hcond'
      have hsEq' : (π : v.adicCompletion F) * s =
          ((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y -
            (center : v.adicCompletion F) := by
        change (π : v.adicCompletion F) * s = _
        exact hsEq
      have huEq :
          (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) =
            (center : v.adicCompletion F) + (π : v.adicCompletion F) * s := by
        calc
          (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) =
              ((((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y -
                (center : v.adicCompletion F)) + center) := by ring
          _ = (π : v.adicCompletion F) * s + center := by rw [hsEq']
          _ = center + (π : v.adicCompletion F) * s := by ring
      have hquot :
          ((2 : v.adicCompletion F) *
              (((π ^ (n + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) * t) /
              (π : v.adicCompletion F) =
            (algebraMap F (v.adicCompletion F) (b : F)) /
                (π : v.adicCompletion F) + (2 : v.adicCompletion F) * s * t := by
        rw [huEq]
        calc
          _ = ((2 : v.adicCompletion F) * (center : v.adicCompletion F) * t +
              2 * (π : v.adicCompletion F) * s * t) / (π : v.adicCompletion F) := by ring
          _ = (algebraMap F (v.adicCompletion F) (b : F) +
              2 * (π : v.adicCompletion F) * s * t) / (π : v.adicCompletion F) := by
            rw [hct]
          _ = algebraMap F (v.adicCompletion F) (b : F) / (π : v.adicCompletion F) +
              2 * s * t := by
            field_simp [Units.ne_zero π]
      have hcrossPsi :
          A.ψ v ((2 : v.adicCompletion F) * (c : v.adicCompletion F) * y * delta) =
            A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) := by
        have h2st : A.ψ v ((2 : v.adicCompletion F) * s * t) = 1 :=
          A.integral v _ (by
            have h2O'' : (2 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
              rw [← htwoCast]
              exact twoO.property
            exact (v.adicCompletionIntegers F).mul_mem
              ((2 : v.adicCompletion F) * s) t
              ((v.adicCompletionIntegers F).mul_mem (2 : v.adicCompletion F) s h2O'' hsO)
              tO.property)
        rw [hcross y, hquot, hratio, (A.ψ v).map_add_eq_mul, h2st, mul_one]
      have harg : (c : v.adicCompletion F) * (y + delta) ^ 2 =
          (c : v.adicCompletion F) * y ^ 2 +
            (2 : v.adicCompletion F) * (c : v.adicCompletion F) * y * delta +
              (c : v.adicCompletion F) * delta ^ 2 := by ring
      rw [harg, (A.ψ v).map_add_eq_mul, (A.ψ v).map_add_eq_mul,
        hcrossPsi, hquadPsi, mul_one]
      ring
    let g : v.adicCompletion F → ℂ := (localShellResidueFiber v π n r).indicator
      (fun y => A.ψ v ((c : v.adicCompletion F) * y ^ 2))
    have hpoint (y : v.adicCompletion F) : g (y + delta) = lam * g y := by
      have hiff := hfiberShift y
      by_cases hy : y ∈ localShellResidueFiber v π n r
      · have hyplus := hiff.mpr hy
        simp only [g, Set.indicator_of_mem hyplus, Set.indicator_of_mem hy]
        exact hphase y hy
      · have hyplus : y + delta ∉ localShellResidueFiber v π n r := by
          intro h
          exact hy (hiff.mp h)
        change (if y + delta ∈ localShellResidueFiber v π n r then _ else 0) =
          lam * (if y ∈ localShellResidueFiber v π n r then _ else 0)
        simp [hyplus, hy]
    have hshift : (∫ y, g (y + delta) ∂μ) = ∫ y, g y ∂μ := by
      simpa [add_comm] using integral_add_left_eq_self (μ := μ) g delta
    have hlinear : (∫ y, g (y + delta) ∂μ) = lam * ∫ y, g y ∂μ := by
      calc
        _ = ∫ y, lam * g y ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
        _ = _ := by rw [integral_const_mul]
    have hmul : (lam - 1) * (∫ y, g y ∂μ) = 0 := by
      calc
        _ = lam * ∫ y, g y ∂μ - ∫ y, g y ∂μ := by ring
        _ = _ := by rw [← hlinear, hshift, sub_self]
    have hzero : (∫ y, g y ∂μ) = 0 := by
      rcases mul_eq_zero.mp hmul with hlam | hI
      · exact (hψ (sub_eq_zero.mp hlam)).elim
      · exact hI
    rw [MeasureTheory.integral_indicator (localShellResidueFiber_measurable v π hπ' n r)] at hzero
    exact hzero
  let φ : v.adicCompletion F → ℂ := fun x =>
    A.ψ v (((c : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
  have hcontψ : Continuous (A.ψ v) := (local_character_regular D A v).1
  have hcontφ : Continuous φ := by fun_prop
  have hIntegrable (r : kˣ) :
      IntegrableOn φ (localShellResidueFiber v π n r) μ :=
    hcontφ.continuousOn.integrableOn_compact (localShellResidueFiber_compact v π hπ' n r)
  rw [localShell_eq_iUnion_residueFibers v π hπ' n]
  rw [integral_iUnion_fintype
    (fun r => localShellResidueFiber_measurable v π hπ' n r)
    (localShellResidueFibers_pairwise v π hπ' n) hIntegrable]
  apply Finset.sum_eq_zero
  intro r hr
  dsimp [φ, c]
  exact hfiberZero r

theorem quadraticIntegral_succ_eq (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (p : Fˣ)
    (hπ : Valued.v (toLoc v p : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (b : 𝓞 F)
    (hψ : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 1)
    (j N : ℕ) (hj : j ≤ 1) :
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
      (toLoc v (p⁻¹ ^ j)) (N + 1) =
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
      (toLoc v (p⁻¹ ^ j)) N := by
  letI : Measure.IsAddHaarMeasure μ := hμ
  let a : (v.adicCompletion F)ˣ := toLoc v (p⁻¹ ^ j)
  let f : v.adicCompletion F → ℂ := fun x =>
    A.ψ v (((a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x ^ 2)
  change (∫ x in localBall v (N + 1), f x ∂μ) =
    ∫ x in localBall v N, f x ∂μ
  have hsub : localBall v N ⊆ localBall v (N + 1) := by
    intro x hx
    change Valued.v x ≤ WithZero.exp (N : ℤ) at hx
    change Valued.v x ≤ WithZero.exp ((N + 1 : ℕ) : ℤ)
    exact hx.trans (WithZero.exp_le_exp.mpr (by omega))
  have hdecomp : localBall v (N + 1) = localBall v N ∪ localShell v N := by
    ext x
    constructor
    · intro hx
      by_cases hmem : x ∈ localBall v N
      · exact Or.inl hmem
      · exact Or.inr ⟨hx, hmem⟩
    · rintro (hx | ⟨hx, hnot⟩)
      · exact hsub hx
      · exact hx
  let E : Bool → Set (v.adicCompletion F) := fun b =>
    if b then localShell v N else localBall v N
  have hE : (⋃ b : Bool, E b) = localBall v N ∪ localShell v N := by
    ext x
    simp [E]
  have hmeas : ∀ b : Bool, MeasurableSet (E b) := by
    intro b
    cases b
    · exact (localBall_open v N).measurableSet
    · exact (localBall_open v (N + 1)).measurableSet.diff
        (localBall_open v N).measurableSet
  have hdisj : Pairwise fun b b' => Disjoint (E b) (E b') := by
    intro b b' hbb'
    cases b <;> cases b'
    · exact (hbb' rfl).elim
    · exact Set.disjoint_left.mpr (by
        intro x hxball hxshell
        exact hxshell.2 hxball)
    · exact Set.disjoint_left.mpr (by
        intro x hxshell hxball
        exact hxshell.2 hxball)
    · exact (hbb' rfl).elim
  have hcont : Continuous f := by
    have hψcont : Continuous (A.ψ v) := (local_character_regular D A v).1
    apply hψcont.comp
    fun_prop
  have hballInt : IntegrableOn f (localBall v N) μ :=
    hcont.continuousOn.integrableOn_compact (localBall_compact v (toLoc v p) hπ N)
  have hshellInt : IntegrableOn f (localShell v N) μ :=
    hcont.continuousOn.integrableOn_compact
      (localShell_compact v (toLoc v p) hπ N)
  have hzero : (∫ x in localShell v N, f x ∂μ) = 0 := by
    exact quadraticShellIntegralZero D A v μ hμ p hπ h2 b hψ N j hj
  calc
    _ = ∫ x in ⋃ b : Bool, E b, f x ∂μ := by rw [hdecomp, hE]
    _ = ∑ b : Bool, ∫ x in E b, f x ∂μ :=
      integral_iUnion_fintype hmeas hdisj (by
        intro b
        cases b
        · exact hballInt
        · exact hshellInt)
    _ = ∫ x in localBall v N, f x ∂μ := by simp [E, hzero]

theorem quadraticIntegral_eq_ball_zero (D : FieldData F) (A : AddCharData F)
    (v : FinPlace F) (μ : Measure (v.adicCompletion F)) (hμ : Measure.IsAddHaarMeasure μ)
    (p : Fˣ)
    (hπ : Valued.v (toLoc v p : v.adicCompletion F) = WithZero.exp (-1 : ℤ))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (b : 𝓞 F)
    (hψ : A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / (p : F))) ≠ 1)
    (j N : ℕ) (hj : j ≤ 1) :
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
      (toLoc v (p⁻¹ ^ j)) N =
    ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
      (toLoc v (p⁻¹ ^ j)) 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    calc
      ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
          (toLoc v (p⁻¹ ^ j)) (N + 1) =
        ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
          (toLoc v (p⁻¹ ^ j)) N :=
            quadraticIntegral_succ_eq D A v μ hμ p hπ h2 b hψ j N hj
      _ = ArtinPrimitiveRoots.Proofs.a1_weil_sol.quadraticIntegral A v μ
          (toLoc v (p⁻¹ ^ j)) 0 := ih

end ArtinPrimitiveRoots.Proofs.a1_weil_sol.w_f

end
