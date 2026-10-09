import ArtinPrimitiveRoots.A1.Proofs.A1_FOURIER.Defs
import ArtinPrimitiveRoots.Theta.LocalInt

/-!
# A1-FOURIER part `a1_fourier_local_fourier_test` (IMPL)

The local Fourier transform of a finite test function is again a finite test function.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots.A1.Theta

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem f_h_exists_ball_subset_open_zero (v : FinPlace F)
    {U : Set (v.adicCompletion F)} (hU : IsOpen U) (h0 : (0 : v.adicCompletion F) ∈ U) :
    ∃ k : ℤ, Theta.ball v k ⊆ U := by
  obtain ⟨i, hsub⟩ := (Valued.mem_nhds_zero (R := v.adicCompletion F)).mp (hU.mem_nhds h0)
  let vf : v.adicCompletion F →*₀ WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ)))
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := vf)) i
  let n : ℤ := WithZero.log (γ : WithZero (Multiplicative ℤ))
  have hγ : (γ : WithZero (Multiplicative ℤ)) = WithZero.exp n := by
    dsimp [n]
    simpa using (WithZero.exp_log (Units.ne_zero γ)).symm
  refine ⟨1 - n, ?_⟩
  intro x hx
  have hxval : Valued.v x ≤ WithZero.exp (n - 1) := by
    simpa [Theta.ball, n] using hx
  have hlt : Valued.v x < (γ : WithZero (Multiplicative ℤ)) := by
    rw [hγ]
    exact lt_of_le_of_lt hxval ((WithZero.exp_lt_exp).2 (by omega))
  have hstrict : Valued.v.restrict x < i.val := by
    simpa [γ, Valued.v.restrict_lt_iff_lt_embedding] using hlt
  exact hsub hstrict

private theorem f_h_thetaBall_open (v : FinPlace F) (k : ℤ) :
    IsOpen (Theta.ball v k) := by
  unfold Theta.ball
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

private theorem f_h_thetaBall_mono (v : FinPlace F) {k l : ℤ} (hkl : k ≤ l) :
    Theta.ball v l ⊆ Theta.ball v k := by
  intro x hx
  change Valued.v x ≤ WithZero.exp (-l) at hx
  change Valued.v x ≤ WithZero.exp (-k)
  exact hx.trans ((WithZero.exp_le_exp).2 (by omega))

private theorem f_h_thetaBall_add (v : FinPlace F) (k : ℤ) {x y : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) (hy : y ∈ Theta.ball v k) :
    x + y ∈ Theta.ball v k := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v y ≤ WithZero.exp (-k) at hy
  change Valued.v (x + y) ≤ WithZero.exp (-k)
  exact Valued.v.map_add_le hx hy

private theorem f_h_thetaBall_neg (v : FinPlace F) (k : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) : -x ∈ Theta.ball v k := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v (-x) ≤ WithZero.exp (-k)
  simpa only [Valuation.map_neg] using hx

private theorem f_h_thetaBall_mul (v : FinPlace F) (k l : ℤ)
    {x y : v.adicCompletion F} (hx : x ∈ Theta.ball v k) (hy : y ∈ Theta.ball v l) :
    x * y ∈ Theta.ball v (k + l) := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v y ≤ WithZero.exp (-l) at hy
  change Valued.v (x * y) ≤ WithZero.exp (-(k + l))
  rw [Valuation.map_mul]
  calc
    Valued.v x * Valued.v y ≤ WithZero.exp (-k) * WithZero.exp (-l) := mul_le_mul' hx hy
    _ = WithZero.exp (-(k + l)) := by rw [← WithZero.exp_add]; congr 1; omega

private theorem f_h_thetaBall_abs_bound (v : FinPlace F) (k : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ Theta.ball v k) :
    absFin v x ≤ qv v ^ ((-k : ℤ) : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    rw [Theta.absFin_eq_norm]
    simp only [norm_zero]
    exact Real.rpow_nonneg (by linarith [qv_gt_one v]) _
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hxval : Valued.v x ≤ WithZero.exp (-k) := hx
  have hlog : (WithZero.unzero hvne).toAdd ≤ -k := by
    have h' : WithZero.exp (Valued.v x).log ≤ WithZero.exp (-k) := by
      rw [WithZero.exp_log hvne]
      exact hxval
    have h'' := (WithZero.exp_le_exp).1 h'
    simpa [WithZero.toAdd_unzero_eq_log hvne] using h''
  have hqNat : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqNN : 1 < (Ideal.absNorm v.asIdeal : NNReal) := by exact_mod_cast hqNat
  have hpow : (Ideal.absNorm v.asIdeal : NNReal) ^ (WithZero.unzero hvne).toAdd ≤
      (Ideal.absNorm v.asIdeal : NNReal) ^ (-k) := zpow_le_zpow_right₀ hqNN.le hlog
  have hpowCoe : ((Ideal.absNorm v.asIdeal : NNReal) ^ (WithZero.unzero hvne).toAdd : ℝ) ≤
      ((Ideal.absNorm v.asIdeal : NNReal) ^ (-k) : ℝ) := by exact_mod_cast hpow
  have hpowReal : (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.unzero hvne).toAdd ≤
      ((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹ := by
    calc
      (Ideal.absNorm v.asIdeal : ℝ) ^ (WithZero.unzero hvne).toAdd =
          ((Ideal.absNorm v.asIdeal : NNReal) ^ (WithZero.unzero hvne).toAdd : ℝ) := by
            simp [NNReal.coe_zpow, NNReal.coe_natCast]
      _ ≤ ((Ideal.absNorm v.asIdeal : NNReal) ^ (-k) : ℝ) := hpowCoe
      _ = ((Ideal.absNorm v.asIdeal : ℝ) ^ k)⁻¹ := by
            simp [NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg]
  rw [Theta.absFin_eq_norm, NumberField.FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) hvne]
  rw [Real.rpow_intCast, zpow_neg]
  simpa [qv, NNReal.coe_zpow, NNReal.coe_natCast] using hpowReal

private theorem f_h_properSpace (v : FinPlace F) : ProperSpace (v.adicCompletion F) := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  letI : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  exact (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩

private theorem f_h_thetaBall_compact (v : FinPlace F) (k : ℤ) :
    IsCompact (Theta.ball v k) := by
  let K := v.adicCompletion F
  let hproper : ProperSpace K := f_h_properSpace v
  letI : ProperSpace K := hproper
  let U : AddSubgroup K := Valued.v.leAddSubgroup (WithZero.exp (-k))
  have hEq : Theta.ball v k = (U : Set K) := rfl
  have hclosed : IsClosed (Theta.ball v k) := by
    rw [hEq]
    exact AddSubgroup.isClosed_of_isOpen U (by rw [← hEq]; exact f_h_thetaBall_open v k)
  let R : ℝ := qv v ^ ((-k : ℤ) : ℝ)
  have hsubset : Theta.ball v k ⊆ Metric.closedBall (0 : K) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, ← Theta.absFin_eq_norm v x]
    exact f_h_thetaBall_abs_bound v k hx
  exact (hproper.isCompact_closedBall 0 R).of_isClosed_subset hclosed hsubset

private theorem f_h_compact_subset_large_thetaBall (v : FinPlace F)
    (S : Set (v.adicCompletion F)) (hS : IsCompact S) (hSn : S.Nonempty) :
    ∃ N : ℕ, S ⊆ Theta.ball v (-(N : ℤ)) := by
  have hcover : S ⊆ ⋃ n : ℕ, Theta.ball v (-(n : ℤ)) := by
    intro x hx
    by_cases hxzero : Valued.v x = 0
    · have hx0 : x = 0 := by
        by_contra hne
        have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
        rw [hxzero] at hvne
        exact hvne rfl
      subst x
      refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      simp [Theta.ball]
    · let m : ℤ := WithZero.log (Valued.v x)
      have hxval : Valued.v x = WithZero.exp m := (WithZero.exp_log hxzero).symm
      let n : ℕ := Int.toNat (max 0 m)
      have hmn : m ≤ (n : ℤ) := by
        by_cases hm : 0 ≤ m
        · simp [n, max_eq_right hm, Int.toNat_of_nonneg hm]
        · have hm' : m < 0 := lt_of_not_ge hm
          have hmax : max 0 m = 0 := max_eq_left hm'.le
          simp [n, hmax]
          omega
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      change Valued.v x ≤ WithZero.exp (-(-(n : ℤ)))
      simp only [neg_neg]
      rw [hxval]
      exact (WithZero.exp_le_exp).2 hmn
  have hopen : ∀ n : ℕ, IsOpen (Theta.ball v (-(n : ℤ))) :=
    fun n => f_h_thetaBall_open v (-(n : ℤ))
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover
    (fun n : ℕ => Theta.ball v (-(n : ℤ))) hopen hcover
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, hx⟩ := hSn
    rcases Set.mem_iUnion₂.mp (hT hx) with ⟨n, hnT, _⟩
    exact ⟨n, hnT⟩
  let N := T.max' hTnonempty
  refine ⟨N, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.mp (hT hx) with ⟨n, hnT, hxn⟩
  have hnN : n ≤ N := Finset.le_max' T n hnT
  exact f_h_thetaBall_mono v (by omega) hxn

private theorem f_h_finiteTest_exists_period_ball (v : FinPlace F)
    (f : v.adicCompletion F → ℂ) (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ k : ℤ, ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x := by
  let K := v.adicCompletion F
  let S : Set K := tsupport f
  have hK : IsCompact S := hfc
  have hS_nonzero : ∀ x ∈ S, f x ≠ 0 := by
    intro x hx hzero
    change x ∈ closure (Function.support f) at hx
    obtain ⟨U, hU, hxU, heq⟩ := hf.exists_open x
    obtain ⟨y, hyU, hyS⟩ := (mem_closure_iff.mp hx) U hU hxU
    exact (Function.mem_support.mp hyS) (by rw [heq y hyU, hzero])
  by_cases hSempty : S = ∅
  · refine ⟨0, ?_⟩
    intro x t ht
    have hx : f x = 0 := by
      by_contra hne
      have hxTs : x ∈ tsupport f := subset_closure (Function.mem_support.mpr hne)
      simpa [S, hSempty] using hxTs
    have hxt : f (x + t) = 0 := by
      by_contra hne
      have hxtTs : x + t ∈ tsupport f := subset_closure (Function.mem_support.mpr hne)
      simpa [S, hSempty] using hxtTs
    rw [hxt, hx]
  · have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
    let Uloc : K → Set K := fun x => Classical.choose (hf.exists_open x)
    have hUloc (x : K) : IsOpen (Uloc x) ∧ x ∈ Uloc x ∧ ∀ y ∈ Uloc x, f y = f x :=
      Classical.choose_spec (hf.exists_open x)
    let Vloc : K → Set K := fun x => {t | x + t ∈ Uloc x}
    have hVopen (x : K) : IsOpen (Vloc x) := by
      apply (hUloc x).1.preimage
      fun_prop
    have hVzero (x : K) : (0 : K) ∈ Vloc x := by
      change x + 0 ∈ Uloc x
      simpa using (hUloc x).2.1
    let k : K → ℤ := fun x => Classical.choose
      (f_h_exists_ball_subset_open_zero v (hVopen x) (hVzero x))
    have hballV (x : K) : Theta.ball v (k x) ⊆ Vloc x :=
      Classical.choose_spec (f_h_exists_ball_subset_open_zero v (hVopen x) (hVzero x))
    let N : K → Set K := fun x => {y | y - x ∈ Theta.ball v (k x)}
    have hNopen (x : K) : IsOpen (N x) := by
      apply (f_h_thetaBall_open v (k x)).preimage
      fun_prop
    have hcover : S ⊆ ⋃ x : K, N x := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨x, ?_⟩
      change x - x ∈ Theta.ball v (k x)
      rw [sub_self]
      change Valued.v (0 : K) ≤ WithZero.exp (-(k x))
      simp
    obtain ⟨T, hT⟩ := hK.elim_finite_subcover N hNopen hcover
    have hTnonempty : T.Nonempty := by
      obtain ⟨x, hx⟩ := hSnonempty
      rcases Set.mem_iUnion.mp (hT hx) with ⟨a, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨haT, _⟩
      exact ⟨a, haT⟩
    let Tk := T.image k
    have hTk : Tk.Nonempty := hTnonempty.image k
    let K₀ : ℤ := Tk.max' hTk
    have hk_le (a : K) (ha : a ∈ T) : k a ≤ K₀ := by
      have hmem : k a ∈ Tk := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      simpa [K₀, Tk] using (Finset.le_max' (s := Tk) (k a) hmem)
    have hlocalEq (a y : K) (hy : y ∈ N a) : f y = f a := by
      have hyball : y - a ∈ Theta.ball v (k a) := hy
      have hymem : a + (y - a) ∈ Uloc a := hballV a hyball
      have hEq : a + (y - a) = y := by abel
      rw [hEq] at hymem
      exact (hUloc a).2.2 y hymem
    refine ⟨K₀, ?_⟩
    intro x t ht
    by_cases hx : x ∈ S
    · rcases Set.mem_iUnion.mp (hT hx) with ⟨a, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨haT, hxN⟩
      have htA : t ∈ Theta.ball v (k a) := f_h_thetaBall_mono v (hk_le a haT) ht
      have hxAt : x + t ∈ N a := by
        change (x + t) - a ∈ Theta.ball v (k a)
        have hsum := f_h_thetaBall_add v (k a) (by change x - a ∈ _; exact hxN) htA
        convert hsum using 1 <;> abel
      exact (hlocalEq a (x + t) hxAt).trans (hlocalEq a x hxN).symm
    · have hfx : f x = 0 := by
        by_contra hne
        exact hx (subset_closure (Function.mem_support.mpr hne))
      by_cases hxt : x + t ∈ S
      · rcases Set.mem_iUnion.mp (hT hxt) with ⟨a, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨haT, hxtN⟩
        have htA : -t ∈ Theta.ball v (k a) :=
          f_h_thetaBall_neg v (k a) (f_h_thetaBall_mono v (hk_le a haT) ht)
        have hxN : x ∈ N a := by
          change x - a ∈ Theta.ball v (k a)
          have hsum := f_h_thetaBall_add v (k a) (by change (x + t) - a ∈ _; exact hxtN) htA
          convert hsum using 1 <;> abel
        have hfxa := hlocalEq a x hxN
        have hxta := hlocalEq a (x + t) hxtN
        have hxt0 : f (x + t) = 0 := by
          calc
            f (x + t) = f a := hxta
            _ = f x := hfxa.symm
            _ = 0 := hfx
        exact False.elim ((hS_nonzero (x + t) hxt) hxt0)
      · have hxt0 : f (x + t) = 0 := by
          by_contra hne
          have hmem : x + t ∈ Function.support f := Function.mem_support.mpr hne
          exact hxt (subset_closure hmem)
        rw [hxt0, hfx]

private theorem f_h_fourier_eq_zero_of_nontrivial_on_period (v : FinPlace F)
    (A : AddCharData F) (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) (k : ℤ)
    (hperiod : ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x)
    (y t : v.adicCompletion F) (ht : t ∈ Theta.ball v k)
    (hψ : A.ψ v (-(t * y)) ≠ 1) : a1LocalFourier v A μ f y = 0 := by
  let H : v.adicCompletion F → ℂ := fun x => A.ψ v (-(x * y)) * f x
  have htrans (x : v.adicCompletion F) :
      H (x + t) = A.ψ v (-(t * y)) * H x := by
    have harg : -((x + t) * y) = -(x * y) + -(t * y) := by ring
    change A.ψ v (-((x + t) * y)) * f (x + t) =
      A.ψ v (-(t * y)) * (A.ψ v (-(x * y)) * f x)
    rw [hperiod x t ht, harg, AddChar.map_add_eq_mul]
    ring
  have hMP : MeasurePreserving (MeasurableEquiv.addRight t) μ μ :=
    measurePreserving_add_right μ t
  have hpres : (∫ x, H (x + t) ∂μ) = ∫ x, H x ∂μ := by
    simpa [MeasurableEquiv.addRight] using
      hMP.integral_comp (MeasurableEquiv.addRight t).measurableEmbedding H
  have hshift : (∫ x, H (x + t) ∂μ) = A.ψ v (-(t * y)) * ∫ x, H x ∂μ := by
    calc
      (∫ x, H (x + t) ∂μ) = ∫ x, A.ψ v (-(t * y)) * H x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact htrans x
      _ = A.ψ v (-(t * y)) * ∫ x, H x ∂μ := integral_const_mul _ _
  have hI : (∫ x, H x ∂μ) = A.ψ v (-(t * y)) * ∫ x, H x ∂μ := by
    rw [hpres] at hshift
    exact hshift
  have hmul : (A.ψ v (-(t * y)) - 1) * (∫ x, H x ∂μ) = 0 := by
    calc
      (A.ψ v (-(t * y)) - 1) * (∫ x, H x ∂μ) =
          A.ψ v (-(t * y)) * (∫ x, H x ∂μ) - ∫ x, H x ∂μ := by ring
      _ = 0 := by rw [← hI]; ring
  have hfactor : A.ψ v (-(t * y)) - 1 ≠ 0 := sub_ne_zero.mpr hψ
  have hzero : (∫ x, H x ∂μ) = 0 := (mul_eq_zero.mp hmul).resolve_left hfactor
  have hcomm : (∫ x, A.ψ v (-(x * y)) * f x ∂μ) =
      ∫ x, A.ψ v (-(y * x)) * f x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm x y]
  change (∫ x, A.ψ v (-(x * y)) * f x ∂μ) = 0 at hzero
  rw [hcomm] at hzero
  simpa [a1LocalFourier] using hzero

private theorem f_h_fourier_hasCompactSupport_of_period (v : FinPlace F)
    (A : AddCharData F) (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) (k : ℤ)
    (hperiod : ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x) :
    HasCompactSupport (a1LocalFourier v A μ f) := by
  obtain ⟨d, hdtriv, ⟨x₀, hx₀, hxψ⟩⟩ := Theta.psi_conductor A v
  have hsupport : ∀ y, a1LocalFourier v A μ f y ≠ 0 →
      y ∈ Theta.ball v (-((d : ℤ) + k + 1)) := by
    intro y hyF
    by_contra hyann
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      simpa [Theta.ball] using hyann
    have hx0 : x₀ ≠ 0 := by
      intro hxzero
      subst x₀
      simpa using hxψ
    have hvx : Valued.v x₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have hvy : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    let a : ℤ := WithZero.log (Valued.v x₀)
    let b : ℤ := WithZero.log (Valued.v y)
    have hxval : Valued.v x₀ = WithZero.exp a := (WithZero.exp_log hvx).symm
    have hyval : Valued.v y = WithZero.exp b := (WithZero.exp_log hvy).symm
    have hxa : a ≤ (d : ℤ) + 1 := by
      have h := hx₀
      change Valued.v x₀ ≤ WithZero.exp ((d : ℤ) + 1) at h
      rw [hxval] at h
      exact (WithZero.exp_le_exp).1 h
    have hyb : (d : ℤ) + k + 1 < b := by
      have hnot : ¬ Valued.v y ≤ WithZero.exp ((d : ℤ) + k + 1) := by
        intro h
        apply hyann
        change y ∈ Theta.ball v (-((d : ℤ) + k + 1))
        simpa [Theta.ball] using h
      rw [hyval] at hnot
      have : ¬ b ≤ (d : ℤ) + k + 1 := by
        intro hle
        exact hnot ((WithZero.exp_le_exp).2 hle)
      omega
    let t : v.adicCompletion F := x₀ / y
    have htv : Valued.v t = WithZero.exp (a - b) := by
      dsimp [t]
      rw [map_div₀, hxval, hyval]
    have htab : a - b ≤ -(k : ℤ) := by omega
    have ht : t ∈ Theta.ball v k := by
      change Valued.v t ≤ WithZero.exp (-k)
      rw [htv]
      exact (WithZero.exp_le_exp).2 htab
    have hmul : t * y = x₀ := by
      dsimp [t]
      field_simp [hy0]
    have hψ : A.ψ v (-(t * y)) ≠ 1 := by
      rw [hmul, AddChar.map_neg_eq_inv]
      exact inv_ne_one.mpr hxψ
    have hzero := f_h_fourier_eq_zero_of_nontrivial_on_period v A μ f k hperiod y t ht hψ
    exact hyF hzero
  let m : ℤ := -((d : ℤ) + k + 1)
  have hBall : IsCompact (Theta.ball v m) := f_h_thetaBall_compact v m
  have hfunSupport : Function.support (a1LocalFourier v A μ f) ⊆ Theta.ball v m := by
    intro y hy
    have hyne : a1LocalFourier v A μ f y ≠ 0 := Function.mem_support.mp hy
    simpa [m] using hsupport y hyne
  have htsupport : tsupport (a1LocalFourier v A μ f) ⊆ Theta.ball v m :=
    closure_minimal hfunSupport hBall.isClosed
  exact hBall.of_isClosed_subset (isClosed_tsupport _) htsupport

private theorem f_h_localFourier_shift_eq_of_compact_support (v : FinPlace F)
    (A : AddCharData F) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (N : ℕ)
    (hN : tsupport f ⊆ Theta.ball v (-(N : ℤ)))
    (y h : v.adicCompletion F) (hh : h ∈ Theta.ball v (N : ℤ)) :
    a1LocalFourier v A μ f (y + h) = a1LocalFourier v A μ f y := by
  unfold a1LocalFourier
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxs : x ∈ Function.support f
  · have hxts : x ∈ tsupport f := subset_closure hxs
    have hxball := hN hxts
    have hxprod : x * h ∈ Theta.ball v 0 := by
      simpa using f_h_thetaBall_mul v (-(N : ℤ)) N hxball hh
    have hneg : -(x * h) ∈ Theta.ball v 0 := f_h_thetaBall_neg v 0 hxprod
    have hO : -(x * h) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (-(x * h)) ≤ 1
      simpa [Theta.ball] using hneg
    have hψ : A.ψ v (-(x * h)) = 1 := A.integral v _ hO
    have harg : -((y + h) * x) = -(y * x) + -(x * h) := by ring
    simp [harg, AddChar.map_add_eq_mul, hψ]
  · have hfzero : f x = 0 := by
      by_contra hne
      exact hxs (Function.mem_support.mpr hne)
    simp [hfzero]

private theorem f_h_fourier_isLocallyConstant (v : FinPlace F) (A : AddCharData F)
    (μ : Measure (v.adicCompletion F)) (f : v.adicCompletion F → ℂ)
    (hfc : HasCompactSupport f) : IsLocallyConstant (a1LocalFourier v A μ f) := by
  let S := tsupport f
  have hN : ∃ N : ℕ, S ⊆ Theta.ball v (-(N : ℤ)) := by
    by_cases hS : S = ∅
    · exact ⟨0, by simp [hS, S]⟩
    · exact f_h_compact_subset_large_thetaBall v S hfc
        (Set.nonempty_iff_ne_empty.mpr hS)
  obtain ⟨N, hN⟩ := hN
  apply (IsLocallyConstant.iff_exists_open (a1LocalFourier v A μ f)).2
  intro y
  let U : Set (v.adicCompletion F) := {z | z - y ∈ Theta.ball v (N : ℤ)}
  have hUopen : IsOpen U := by
    apply (f_h_thetaBall_open v (N : ℤ)).preimage
    fun_prop
  refine ⟨U, hUopen, ?_, ?_⟩
  · change y - y ∈ Theta.ball v (N : ℤ)
    simp [Theta.ball]
  · intro z hz
    have hshift := f_h_localFourier_shift_eq_of_compact_support v A μ f N hN y (z - y) hz
    have heq : y + (z - y) = z := by abel
    rw [heq] at hshift
    exact hshift

/-- The local Fourier transform of a locally constant compactly supported function is
continuous, compactly supported and locally constant, for any Haar measure `μ` on `F_v`.

Proof hint: copy (do not import) `A2/Proofs/A2_WEIGHTS/Finite.lean`:
`finiteTest_exists_period_ball` (193), `finiteFourier_hasCompactSupport_of_period` (402),
`finiteFourier_isLocallyConstant` (943). There `finiteFourier v A μ f y = ∫ x, f x * A.ψ v (-(x*y))`
for a `Theta.LocHaar`; here the factors are swapped and `μ` is any Haar measure (nontriviality
of `A.ψ v` comes from `AddCharData` as in those proofs).
Used by: the glue `SData.fourier_isFSTensorSum` (`A1/SLattice.lean`). -/
theorem a1_fourier_local_fourier_test (v : FinPlace F) (A : AddCharData F)
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (φ : v.adicCompletion F → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hφl : IsLocallyConstant φ) :
    Continuous (a1LocalFourier v A μ φ) ∧ HasCompactSupport (a1LocalFourier v A μ φ) ∧
      IsLocallyConstant (a1LocalFourier v A μ φ) := by
  have hperiod := f_h_finiteTest_exists_period_ball v φ hφl hφs
  have hcompact := f_h_fourier_hasCompactSupport_of_period v A μ φ hperiod.choose hperiod.choose_spec
  have hlc := f_h_fourier_isLocallyConstant v A μ φ hφs
  exact ⟨hlc.continuous, hcompact, hlc⟩

end ArtinPrimitiveRoots.A1
