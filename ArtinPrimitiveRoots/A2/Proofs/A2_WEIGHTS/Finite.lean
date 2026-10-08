import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.Theta.LocalInt

open MeasureTheory
open Filter
open NumberField IsDedekindDomain
open scoped Classical

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_weights

open ArtinPrimitiveRoots A1 A2
open ArtinPrimitiveRoots.A1.Theta

def finiteFourier {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (y : v.adicCompletion F) : ℂ :=
  ∫ x, f x * A.ψ v (-(x * y)) ∂μ.μ

theorem exists_ball_subset_open_zero {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) {U : Set (v.adicCompletion F)} (hU : IsOpen U) (h0 : (0 : v.adicCompletion F) ∈ U) :
    ∃ k : ℤ, Theta.ball v k ⊆ U := by
  obtain ⟨i, hsub⟩ := (Valued.mem_nhds_zero (R := v.adicCompletion F)).mp (hU.mem_nhds h0)
  let vf : v.adicCompletion F →*₀ WithZero (Multiplicative ℤ) :=
    MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := vf)) i
  let n : ℤ := (WithZero.log (γ : WithZero (Multiplicative ℤ)))
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

private theorem thetaBall_open {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) : IsOpen (Theta.ball v k) := by
  unfold Theta.ball
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

private theorem thetaBall_mono {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) {k l : ℤ} (hkl : k ≤ l) : Theta.ball v l ⊆ Theta.ball v k := by
  intro x hx
  change Valued.v x ≤ WithZero.exp (-l) at hx
  change Valued.v x ≤ WithZero.exp (-k)
  exact hx.trans ((WithZero.exp_le_exp).2 (by omega))

private theorem thetaBall_add {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) {x y : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) (hy : y ∈ Theta.ball v k) :
    x + y ∈ Theta.ball v k := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v y ≤ WithZero.exp (-k) at hy
  change Valued.v (x + y) ≤ WithZero.exp (-k)
  exact Valued.v.map_add_le hx hy

private theorem thetaBall_neg {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) : -x ∈ Theta.ball v k := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v (-x) ≤ WithZero.exp (-k)
  simpa only [Valuation.map_neg] using hx

private theorem thetaBall_mul {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k l : ℤ) {x y : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) (hy : y ∈ Theta.ball v l) :
    x * y ∈ Theta.ball v (k + l) := by
  change Valued.v x ≤ WithZero.exp (-k) at hx
  change Valued.v y ≤ WithZero.exp (-l) at hy
  change Valued.v (x * y) ≤ WithZero.exp (-(k + l))
  rw [Valuation.map_mul]
  calc
    Valued.v x * Valued.v y ≤ WithZero.exp (-k) * WithZero.exp (-l) :=
      mul_le_mul' hx hy
    _ = WithZero.exp (-(k + l)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega

private theorem thetaBall_absFin_bound {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) {x : v.adicCompletion F}
    (hx : x ∈ Theta.ball v k) : absFin v x ≤ qv v ^ ((-k : ℤ) : ℝ) := by
  by_cases hx0 : x = 0
  · subst x
    rw [Theta.absFin_eq_norm]
    simp only [norm_zero]
    exact Real.rpow_nonneg (by linarith [qv_gt_one v]) _
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hxval : Valued.v x ≤ WithZero.exp (-k) := by
    change Valued.v x ≤ WithZero.exp (-k)
    exact hx
  have hlog : (WithZero.unzero hvne).toAdd ≤ -k := by
    have h' : WithZero.exp (Valued.v x).log ≤ WithZero.exp (-k) := by
      rw [WithZero.exp_log hvne]
      exact hxval
    have h'' := (WithZero.exp_le_exp).1 h'
    simpa [WithZero.toAdd_unzero_eq_log hvne] using h''
  have hqNat : 1 < Ideal.absNorm v.asIdeal :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqNN : 1 < (Ideal.absNorm v.asIdeal : NNReal) := by exact_mod_cast hqNat
  have hpow : (Ideal.absNorm v.asIdeal : NNReal) ^ (WithZero.unzero hvne).toAdd ≤
      (Ideal.absNorm v.asIdeal : NNReal) ^ (-k) :=
    zpow_le_zpow_right₀ hqNN.le hlog
  have hpowCoe : ((Ideal.absNorm v.asIdeal : NNReal) ^ (WithZero.unzero hvne).toAdd : ℝ) ≤
      ((Ideal.absNorm v.asIdeal : NNReal) ^ (-k) : ℝ) := by
    exact_mod_cast hpow
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

private theorem thetaBall_compact {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) : IsCompact (Theta.ball v k) := by
  let K := v.adicCompletion F
  let hproper : ProperSpace K := bridgeFin_properSpace v
  letI : ProperSpace K := hproper
  let U : AddSubgroup K := Valued.v.leAddSubgroup (WithZero.exp (-k))
  have hEq : Theta.ball v k = (U : Set K) := rfl
  have hclosed : IsClosed (Theta.ball v k) := by
    rw [hEq]
    exact AddSubgroup.isClosed_of_isOpen U (by
      rw [← hEq]
      exact thetaBall_open v k)
  let R : ℝ := qv v ^ ((-k : ℤ) : ℝ)
  have hsubset : Theta.ball v k ⊆ Metric.closedBall (0 : K) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, ← Theta.absFin_eq_norm v x]
    exact thetaBall_absFin_bound v k hx
  exact (hproper.isCompact_closedBall 0 R).of_isClosed_subset hclosed hsubset

private theorem compact_subset_large_thetaBall {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (S : Set (v.adicCompletion F)) (hS : IsCompact S)
    (hSn : S.Nonempty) :
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
    fun n => thetaBall_open v (-(n : ℤ))
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover (fun n : ℕ => Theta.ball v (-(n : ℤ))) hopen hcover
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, hx⟩ := hSn
    rcases Set.mem_iUnion₂.mp (hT hx) with ⟨n, hnT, _⟩
    exact ⟨n, hnT⟩
  let N := T.max' hTnonempty
  refine ⟨N, ?_⟩
  intro x hx
  rcases Set.mem_iUnion₂.mp (hT hx) with ⟨n, hnT, hxn⟩
  have hnN : n ≤ N := Finset.le_max' T n hnT
  exact thetaBall_mono v (by omega) hxn

/-- A compactly supported locally constant function on a finite completion is invariant under a
single valuation ball of translations. -/
theorem finiteTest_exists_period_ball {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
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
      have : x ∈ (∅ : Set K) := by simpa [S, hSempty] using hxTs
      simpa using this
    have hxt : f (x + t) = 0 := by
      by_contra hne
      have hxtTs : x + t ∈ tsupport f :=
        subset_closure (Function.mem_support.mpr hne)
      have : x + t ∈ (∅ : Set K) := by simpa [S, hSempty] using hxtTs
      simpa using this
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
    let k : K → ℤ := fun x => Classical.choose (exists_ball_subset_open_zero v (hVopen x) (hVzero x))
    have hballV (x : K) : Theta.ball v (k x) ⊆ Vloc x :=
      Classical.choose_spec (exists_ball_subset_open_zero v (hVopen x) (hVzero x))
    let N : K → Set K := fun x => {y | y - x ∈ Theta.ball v (k x)}
    have hNopen (x : K) : IsOpen (N x) := by
      apply (thetaBall_open v (k x)).preimage
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
      have htA : t ∈ Theta.ball v (k a) := thetaBall_mono v (hk_le a haT) ht
      have hxAt : x + t ∈ N a := by
        change (x + t) - a ∈ Theta.ball v (k a)
        have hsum := thetaBall_add v (k a) (by change x - a ∈ _; exact hxN) htA
        convert hsum using 1 <;> abel
      exact (hlocalEq a (x + t) hxAt).trans (hlocalEq a x hxN).symm
    · have hfx : f x = 0 := by
        by_contra hne
        exact hx (subset_closure (Function.mem_support.mpr hne))
      by_cases hxt : x + t ∈ S
      · rcases Set.mem_iUnion.mp (hT hxt) with ⟨a, ha⟩
        rcases Set.mem_iUnion.mp ha with ⟨haT, hxtN⟩
        have htA : -t ∈ Theta.ball v (k a) :=
          thetaBall_neg v (k a) (thetaBall_mono v (hk_le a haT) ht)
        have hxN : x ∈ N a := by
          change x - a ∈ Theta.ball v (k a)
          have hsum := thetaBall_add v (k a) (by change (x + t) - a ∈ _; exact hxtN) htA
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

/-- A locally translation-invariant test has Fourier transform zero where the character
does not annihilate its period ball. -/
theorem finiteFourier_eq_zero_of_nontrivial_on_period {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (k : ℤ)
    (hperiod : ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x)
    (y : v.adicCompletion F)
    (t : v.adicCompletion F) (ht : t ∈ Theta.ball v k)
    (hψ : A.ψ v (-(t * y)) ≠ 1) :
    finiteFourier v A μ f y = 0 := by
  let H : v.adicCompletion F → ℂ := fun x => f x * A.ψ v (-(x * y))
  have htrans (x : v.adicCompletion F) :
      H (x + t) = A.ψ v (-(t * y)) * H x := by
    have harg : -((x + t) * y) = -(x * y) + -(t * y) := by ring
    change f (x + t) * A.ψ v (-((x + t) * y)) =
      A.ψ v (-(t * y)) * (f x * A.ψ v (-(x * y)))
    rw [hperiod x t ht, harg, AddChar.map_add_eq_mul]
    ring
  have hMP : MeasurePreserving (MeasurableEquiv.addRight t) μ.μ μ.μ :=
    measurePreserving_add_right μ.μ t
  have hpres : (∫ x, H (x + t) ∂μ.μ) = ∫ x, H x ∂μ.μ := by
    simpa [MeasurableEquiv.addRight] using
      hMP.integral_comp (MeasurableEquiv.addRight t).measurableEmbedding H
  have hshift : (∫ x, H (x + t) ∂μ.μ) =
      A.ψ v (-(t * y)) * ∫ x, H x ∂μ.μ := by
    calc
      (∫ x, H (x + t) ∂μ.μ) = ∫ x, A.ψ v (-(t * y)) * H x ∂μ.μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact htrans x
      _ = A.ψ v (-(t * y)) * ∫ x, H x ∂μ.μ := integral_const_mul _ _
  have hI : (∫ x, H x ∂μ.μ) = A.ψ v (-(t * y)) * ∫ x, H x ∂μ.μ := by
    rw [hpres] at hshift
    exact hshift
  have hmul : (A.ψ v (-(t * y)) - 1) * (∫ x, H x ∂μ.μ) = 0 := by
    calc
      (A.ψ v (-(t * y)) - 1) * (∫ x, H x ∂μ.μ) =
          A.ψ v (-(t * y)) * (∫ x, H x ∂μ.μ) - ∫ x, H x ∂μ.μ := by ring
      _ = 0 := by rw [← hI]; ring
  have hfactor : A.ψ v (-(t * y)) - 1 ≠ 0 := sub_ne_zero.mpr hψ
  have : (∫ x, H x ∂μ.μ) = 0 := (mul_eq_zero.mp hmul).resolve_left hfactor
  exact this

theorem finiteFourier_compact_support_of_period {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (k : ℤ)
    (hperiod : ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x) :
    ∃ d : ℕ, ∀ y, finiteFourier v A μ f y ≠ 0 →
      y ∈ Theta.ball v (-(d + k + 1)) := by
  obtain ⟨d, hdtriv, ⟨x₀, hx₀, hxψ⟩⟩ := Theta.psi_conductor A v
  refine ⟨d, ?_⟩
  intro y hyF
  by_contra hyann
  have hy0 : y ≠ 0 := by
    intro hyzero
    subst y
    simp [Theta.ball] at hyann
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
      change y ∈ Theta.ball v (-(d + k + 1))
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
  have hzero := finiteFourier_eq_zero_of_nontrivial_on_period v A μ f k hperiod y t ht hψ
  exact hyF hzero

theorem finiteFourier_hasCompactSupport_of_period {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (k : ℤ)
    (hperiod : ∀ x t, t ∈ Theta.ball v k → f (x + t) = f x) :
    HasCompactSupport (finiteFourier v A μ f) := by
  obtain ⟨d, hsupport⟩ :=
    finiteFourier_compact_support_of_period v A μ f k hperiod
  let m : ℤ := -((d : ℤ) + k + 1)
  have hBall : IsCompact (Theta.ball v m) := thetaBall_compact v m
  have hfunSupport : Function.support (finiteFourier v A μ f) ⊆ Theta.ball v m := by
    intro y hy
    by_contra hnot
    have hyne : finiteFourier v A μ f y ≠ 0 := Function.mem_support.mp hy
    have hyball := hsupport y hyne
    exact hnot (by simpa [m] using hyball)
  have htsupport : tsupport (finiteFourier v A μ f) ⊆ Theta.ball v m :=
    closure_minimal hfunSupport hBall.isClosed
  exact hBall.of_isClosed_subset (isClosed_tsupport _) htsupport

/-- Successive additive valuation balls have the expected Haar-volume ratio. -/
private theorem finiteBall_measure_succ {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    μ.μ.real (Theta.ball v k) = qv v * μ.μ.real (Theta.ball v (k + 1)) := by
  let K := v.adicCompletion F
  let π : Kˣ := unifLoc v
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (π : K) = algebraMap F K (unif (F := F) v) := by
      simp [π, unifLoc, toLoc, K]
    rw [hπcoerce]
    change Valued.v ((unif (F := F) v : F) : K) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπabs : absFin v (π : K) = (qv v)⁻¹ := by
    rw [Theta.absFin_eq_norm, FinitePlace.norm_def, hπval]
    have hqexp : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (-1 : ℤ)) = ((Ideal.absNorm v.asIdeal : NNReal)⁻¹) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
      rw [WithZero.toAdd_unzero_eq_log (by simp)]
      simp [qv]
    change ((WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp (-1 : ℤ)) : NNReal) : ℝ) = _
    rw [hqexp]
    simp [qv]
  have hpre : ∀ x : K,
      (π : K) * x ∈ Theta.ball v (k + 1) ↔ x ∈ Theta.ball v k := by
    intro x
    change Valued.v ((π : K) * x) ≤ WithZero.exp (-(k + 1)) ↔
      Valued.v x ≤ WithZero.exp (-k)
    rw [Valuation.map_mul, hπval]
    by_cases hx : Valued.v x = 0
    · simp [hx]
    · lift Valued.v x to ℤ using hx with n hn
      rw [← WithZero.exp_add]
      simp only [WithZero.exp_le_exp]
      omega
  have hmeas0 : MeasurableSet (Theta.ball v k) := (thetaBall_open v k).measurableSet
  have hmeas1 : MeasurableSet (Theta.ball v (k + 1)) :=
    (thetaBall_open v (k + 1)).measurableSet
  let f : K → ℝ := (Theta.ball v (k + 1)).indicator (fun _ => (1 : ℝ))
  have hpreFun : (fun x : K => f ((π : K) * x)) =
      (Theta.ball v k).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp [f, Set.indicator, hpre x]
  have hI0 : (∫ x, (Theta.ball v k).indicator (fun _ => (1 : ℝ)) x ∂μ.μ) =
      μ.μ.real (Theta.ball v k) := by
    rw [MeasureTheory.integral_indicator_const 1 hmeas0]
    simp
  have hI1 : (∫ x, f x ∂μ.μ) = μ.μ.real (Theta.ball v (k + 1)) := by
    change (∫ x, (Theta.ball v (k + 1)).indicator (fun _ => (1 : ℝ)) x ∂μ.μ) = _
    rw [MeasureTheory.integral_indicator_const 1 hmeas1]
    simp
  have hscale := Theta.LocHaar.integral_comp_mul μ π f
  calc
    μ.μ.real (Theta.ball v k) = ∫ x, f ((π : K) * x) ∂μ.μ := by
      rw [hpreFun]
      exact hI0.symm
    _ = (absFin v (π : K))⁻¹ • ∫ x, f x ∂μ.μ := hscale
    _ = qv v * μ.μ.real (Theta.ball v (k + 1)) := by
      rw [hπabs, hI1]
      simp [smul_eq_mul]

/-- The normalized additive Haar volume of every valuation ball. -/
private theorem finiteBall_measure {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    μ.μ.real (Theta.ball v k) = (qv v) ^ ((-k : ℤ) : ℝ) := by
  let M : ℤ → ℝ := fun n => μ.μ.real (Theta.ball v n)
  have hbase : M 0 = 1 := by
    have hball : Theta.ball v 0 = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      ext x
      change Valued.v x ≤ WithZero.exp 0 ↔ x ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp
    simp [M, hball, Measure.real_def, μ.norm_O]
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have hqne : qv v ≠ 0 := hq.ne'
  suffices h : M k = (qv v) ^ ((-k : ℤ) : ℝ) by exact h
  induction k using Int.induction_on with
  | zero => simpa using hbase
  | succ n ih =>
      have hs := finiteBall_measure_succ v μ n
      change M n = qv v * M (n + 1) at hs
      have hcalc : M (n + 1) = (qv v) ^ ((-(n + 1 : ℤ)) : ℝ) := calc
        M (n + 1) = (qv v)⁻¹ * (qv v * M (n + 1)) := by
          field_simp [hqne]
        _ = (qv v)⁻¹ * M n := by rw [← hs]
        _ = (qv v)⁻¹ * (qv v) ^ ((-n : ℤ) : ℝ) := by rw [ih]
        _ = (qv v) ^ ((-(n + 1 : ℤ)) : ℝ) := by
          have hqinv : (qv v)⁻¹ = (qv v) ^ (-1 : ℝ) := by
            rw [Real.rpow_neg hq.le]
            simp
          rw [hqinv, ← Real.rpow_add hq]
          have hExp : (-1 : ℝ) + ((-n : ℤ) : ℝ) = ((-(n + 1 : ℤ)) : ℝ) := by
            push_cast
            ring
          exact congrArg (fun r : ℝ => (qv v) ^ r) hExp
      simpa only [Int.cast_neg] using hcalc
  | pred n ih =>
      calc
        M (-n - 1) = qv v * M (-n) := by
          have hs := finiteBall_measure_succ v μ (-n - 1)
          change M (-n - 1) = qv v * M (-n - 1 + 1) at hs
          simpa using hs
        _ = qv v * (qv v) ^ ((-(-n : ℤ) : ℤ) : ℝ) := by rw [ih]
        _ = (qv v) ^ ((-(-n - 1 : ℤ) : ℤ) : ℝ) := by
          have hn : -(-n : ℤ) = (n : ℤ) := by omega
          rw [hn]
          have hexp : (-(-n - 1 : ℤ) : ℤ) = (n + 1 : ℤ) := by omega
          calc
            qv v * (qv v) ^ ((n : ℤ) : ℝ) =
                (qv v) ^ (1 : ℝ) * (qv v) ^ ((n : ℤ) : ℝ) := by simp
            _ = (qv v) ^ ((1 : ℝ) + ((n : ℤ) : ℝ)) := by
              rw [← Real.rpow_add hq]
            _ = (qv v) ^ ((n + 1 : ℤ) : ℝ) := by congr 1 <;> push_cast <;> ring
            _ = (qv v) ^ ((-(-n - 1 : ℤ) : ℤ) : ℝ) := by rw [hexp]

/-- The finite absolute value is constant on a valuation shell. -/
private theorem finiteAbs_eq_qpow_of_boundary {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) (x : v.adicCompletion F)
    (hx : x ∈ Theta.ball v k) (hxn : x ∉ Theta.ball v (k + 1)) :
    absFin v x = (qv v) ^ ((-k : ℤ) : ℝ) := by
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    apply hxn
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-(k + 1))
    simp
  have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hle : Valued.v x ≤ WithZero.exp (-k) := by
    change Valued.v x ≤ WithZero.exp (-k) at hx
    exact hx
  have hnot : ¬ Valued.v x ≤ WithZero.exp (-(k + 1)) := by
    intro h
    exact hxn h
  let n : ℤ := WithZero.log (Valued.v x)
  have hval : Valued.v x = WithZero.exp n := (WithZero.exp_log hvne).symm
  have hnle : n ≤ -k := by
    have h := hle
    rw [hval] at h
    exact (WithZero.exp_le_exp).1 h
  have hngt : -(k + 1) < n := by
    have h' : ¬ n ≤ -(k + 1) := by
      intro hle'
      apply hnot
      rw [hval]
      exact (WithZero.exp_le_exp).2 hle'
    omega
  have hn : n = -k := by omega
  have hval' : Valued.v x = WithZero.exp (-k) := by rw [hval, hn]
  have hpow :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) =
        (Ideal.absNorm v.asIdeal : NNReal) ^ (-k : ℤ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v) hvne,
      WithZero.toAdd_unzero_eq_log hvne, hval', WithZero.log_exp]
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v), hpow]
  rw [Real.rpow_intCast, zpow_neg]
  simpa [qv, NNReal.coe_zpow, NNReal.coe_natCast]

/-- Convert the normalized real ball volume back to the measure value. -/
private theorem finiteBall_measure_ennreal {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    μ.μ (Theta.ball v k) = ENNReal.ofReal ((qv v) ^ ((-k : ℤ) : ℝ)) := by
  letI : Measure.IsAddHaarMeasure μ.μ := μ.isHaar
  have hfinite : μ.μ (Theta.ball v k) < ⊤ :=
    IsFiniteMeasureOnCompacts.lt_top_of_isCompact (thetaBall_compact v k)
  calc
    μ.μ (Theta.ball v k) = ENNReal.ofReal (μ.μ (Theta.ball v k)).toReal :=
      (ENNReal.ofReal_toReal hfinite.ne).symm
    _ = ENNReal.ofReal ((qv v) ^ ((-k : ℤ) : ℝ)) := by
      congr 1
      simpa [Measure.real_def] using finiteBall_measure v μ k

/-- Additive Haar measure of one shell. -/
private theorem finiteBall_boundary_measure {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    μ.μ.real (Theta.ball v k \ Theta.ball v (k + 1)) =
      (qv v) ^ ((-k : ℤ) : ℝ) * (1 - (qv v)⁻¹) := by
  have hsubset : Theta.ball v (k + 1) ⊆ Theta.ball v k :=
    thetaBall_mono v (by omega)
  have hBne : μ.μ (Theta.ball v k) ≠ ⊤ := by
    rw [finiteBall_measure_ennreal]
    exact ENNReal.ofReal_ne_top
  rw [measureReal_sdiff hsubset (thetaBall_open v (k + 1)).measurableSet hBne]
  rw [finiteBall_measure v μ k, finiteBall_measure v μ (k + 1)]
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have hpowNext' : (qv v) ^ (-((k : ℝ) + 1)) =
      (qv v) ^ (-(k : ℝ)) * (qv v)⁻¹ := by
    have hexp : -((k : ℝ) + 1) = (-(k : ℝ)) + (-1 : ℝ) := by ring
    rw [hexp, Real.rpow_add hq, Real.rpow_neg_one]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_one]
  rw [hpowNext']
  ring

/-- The multiplicative Haar measure of every finite-place valuation shell is `1-q⁻¹`. -/
private theorem finiteMulHaar_boundary_measure {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    Theta.mulHaarFin μ (Theta.ball v k \ Theta.ball v (k + 1)) =
      ENNReal.ofReal (1 - (qv v)⁻¹) := by
  let T : Set (v.adicCompletion F) := Theta.ball v k \ Theta.ball v (k + 1)
  have hTmeas : MeasurableSet T :=
    (thetaBall_open v k).measurableSet.diff (thetaBall_open v (k + 1)).measurableSet
  have hBfin : μ.μ (Theta.ball v k) < ⊤ := by
    letI : Measure.IsAddHaarMeasure μ.μ := μ.isHaar
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (thetaBall_compact v k)
  have hTfin : μ.μ T < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.sdiff_subset : T ⊆ Theta.ball v k)) hBfin
  have hTenn : μ.μ T = ENNReal.ofReal
      ((qv v) ^ ((-k : ℤ) : ℝ) * (1 - (qv v)⁻¹)) := by
    calc
      μ.μ T = ENNReal.ofReal (μ.μ T).toReal :=
        (ENNReal.ofReal_toReal hTfin.ne).symm
      _ = ENNReal.ofReal
          ((qv v) ^ ((-k : ℤ) : ℝ) * (1 - (qv v)⁻¹)) := by
        congr 1
        simpa [Measure.real_def, T] using finiteBall_boundary_measure v μ k
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  let r : ℝ := (qv v) ^ ((-k : ℤ) : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hq _
  let c : ENNReal := (ENNReal.ofReal r)⁻¹
  have hdens :
      (fun y : v.adicCompletion F => ENNReal.ofReal (absFin v y)⁻¹) =ᵐ[μ.μ.restrict T]
        fun _ => c := by
    filter_upwards [ae_restrict_mem hTmeas] with y hy
    have hy' : y ∈ Theta.ball v k \ Theta.ball v (k + 1) := hy
    have hnorm := finiteAbs_eq_qpow_of_boundary v k y hy'.1 hy'.2
    rw [hnorm]
    dsimp [c, r]
    exact ENNReal.ofReal_inv_of_pos hr
  rw [Theta.mulHaarFin, withDensity_apply _ hTmeas]
  calc
    ∫⁻ y in T, ENNReal.ofReal (absFin v y)⁻¹ ∂μ.μ =
        ∫⁻ y in T, c ∂μ.μ := by
          apply lintegral_congr_ae
          exact hdens
    _ = c * μ.μ T := by simp [lintegral_const, T]
    _ = ENNReal.ofReal (1 - (qv v)⁻¹) := by
      dsimp [c, r]
      rw [hTenn, ENNReal.ofReal_mul hr.le]
      have h0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
      exact ENNReal.inv_mul_cancel_left h0 ENNReal.ofReal_ne_top

/-- Fourier transform of a compact-open ball indicator: it is its volume on the
annihilator and zero whenever the character is nontrivial on the ball. -/
theorem finiteFourier_ball_indicator {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (y : v.adicCompletion F) :
    finiteFourier v A μ ((Theta.ball v k).indicator (fun _ => (1 : ℂ))) y =
      if h : ∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1 then
        (μ.μ.real (Theta.ball v k) : ℂ) else 0 := by
  classical
  let f : v.adicCompletion F → ℂ := (Theta.ball v k).indicator (fun _ => (1 : ℂ))
  by_cases h : ∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1
  · have hfun : (fun x : v.adicCompletion F =>
        f x * A.ψ v (-(x * y))) = f := by
      funext x
      by_cases hx : x ∈ Theta.ball v k
      · simp [f, Set.indicator, hx, h x hx]
      · simp [f, Set.indicator, hx]
    have hmeas : MeasurableSet (Theta.ball v k) :=
      (thetaBall_open v k).measurableSet
    rw [dif_pos h]
    calc
      finiteFourier v A μ f y = ∫ x, f x * A.ψ v (-(x * y)) ∂μ.μ := rfl
      _ = ∫ x, f x ∂μ.μ := by rw [hfun]
      _ = ∫ x, (Theta.ball v k).indicator (fun _ => (1 : ℂ)) x ∂μ.μ := rfl
      _ = (μ.μ.real (Theta.ball v k) : ℂ) := by
        rw [MeasureTheory.integral_indicator_const (1 : ℂ) hmeas]
        simp [smul_eq_mul]
  · have hnot := h
    push_neg at h
    obtain ⟨t, ht, hψ⟩ := h
    have hperiod : ∀ x u, u ∈ Theta.ball v k → f (x + u) = f x := by
      intro x u hu
      have hmem : x + u ∈ Theta.ball v k ↔ x ∈ Theta.ball v k := by
        constructor
        · intro hxu
          have hneg := thetaBall_neg v k hu
          have hsum := thetaBall_add v k hxu hneg
          convert hsum using 1 <;> abel
        · intro hx
          exact thetaBall_add v k hx hu
      simp [f, Set.indicator, hmem]
    have hz := finiteFourier_eq_zero_of_nontrivial_on_period v A μ f k
      hperiod y t ht hψ
    simpa [f, hnot] using hz

/-- A finite character annihilates an additive valuation ball exactly on its dual ball. -/
private theorem finitePsi_ball_annihilator_all {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) :
    ∃ d : ℕ, ∀ y : v.adicCompletion F,
      ∀ k : ℤ,
        (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
          y ∈ Theta.ball v (-(d + k)) := by
  obtain ⟨d, hdtriv, x₀, hx₀, hxψ⟩ := Theta.psi_conductor A v
  refine ⟨d, ?_⟩
  intro y k
  constructor
  · intro htriv
    by_contra hnotBall
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      exact hnotBall (by
        change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-(-(d + k)))
        simp)
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
    have hal : a ≤ (d : ℤ) + 1 := by
      have h := hx₀
      change Valued.v x₀ ≤ WithZero.exp ((d : ℤ) + 1) at h
      rw [hxval] at h
      exact (WithZero.exp_le_exp).1 h
    have hnotVal : ¬ Valued.v y ≤ WithZero.exp ((d : ℤ) + k) := by
      intro h
      exact hnotBall (by
        change Valued.v y ≤ WithZero.exp (-(-(d + k)))
        simpa only [neg_neg] using h)
    have hbg : (d : ℤ) + k < b := by
      have hnotle : ¬ b ≤ (d : ℤ) + k := by
        intro hle
        apply hnotVal
        rw [hyval]
        exact (WithZero.exp_le_exp).2 hle
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
    exact hψ (htriv t ht)
  · intro hyBall
    intro x hx
    have hprod : x * y ∈ Theta.ball v (-(d : ℤ)) := by
      have h := thetaBall_mul v k (-(d + k)) hx hyBall
      have hidx : k + (-(d + k)) = -(d : ℤ) := by omega
      simpa only [hidx] using h
    have hneg := thetaBall_neg v (-(d : ℤ)) hprod
    exact hdtriv _ hneg

private theorem finitePsi_ball_annihilator {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (k : ℤ) :
    ∃ d : ℕ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)) := by
  obtain ⟨d, hd⟩ := finitePsi_ball_annihilator_all v A
  exact ⟨d, fun y => hd y k⟩

/-- The transform of a ball indicator is exactly supported on its conductor dual ball. -/
private theorem finiteFourier_ball_indicator_exact {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (k : ℤ) :
    ∃ d : ℕ, ∀ y : v.adicCompletion F,
      finiteFourier v A μ ((Theta.ball v k).indicator (fun _ => (1 : ℂ))) y =
        if y ∈ Theta.ball v (-(d + k)) then
          (μ.μ.real (Theta.ball v k) : ℂ) else 0 := by
  obtain ⟨d, hd⟩ := finitePsi_ball_annihilator v A k
  refine ⟨d, ?_⟩
  intro y
  have hdk : -(d + k : ℤ) = -k + -(d : ℤ) := by omega
  by_cases hy : y ∈ Theta.ball v (-(d + k))
  · have htriv := (hd y).2 hy
    have hy' : y ∈ Theta.ball v (-k + -(d : ℤ)) := by
      simpa only [hdk] using hy
    rw [finiteFourier_ball_indicator, dif_pos htriv]
    simp [hy']
  · have hnon : ¬ (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) := by
      intro hall
      exact hy ((hd y).1 hall)
    have hnot' : y ∉ Theta.ball v (-k + -(d : ℤ)) := by
      intro h
      apply hy
      simpa only [hdk] using h
    rw [finiteFourier_ball_indicator, dif_neg hnon]
    simp [hnot']

/-- Additive character integral on a compact-open ball, with the conductor cutoff explicit. -/
private theorem finiteAddChar_integral_ball_of_annihilator {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) (d : ℕ)
    (hd : ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k))) :
    ∫ y in Theta.ball v k, A.ψ v (-(a * y)) ∂μ.μ =
      if a ∈ Theta.ball v (-(d + k)) then
        (μ.μ.real (Theta.ball v k) : ℂ) else 0 := by
  have hBmeas : MeasurableSet (Theta.ball v k) := (thetaBall_open v k).measurableSet
  let f : v.adicCompletion F → ℂ := (Theta.ball v k).indicator (fun _ => (1 : ℂ))
  have hEq : finiteFourier v A μ f a =
      ∫ y in Theta.ball v k, A.ψ v (-(a * y)) ∂μ.μ := by
    rw [finiteFourier]
    have hfun : (fun y : v.adicCompletion F =>
        f y * A.ψ v (-(y * a))) =
      (Theta.ball v k).indicator (fun y => A.ψ v (-(y * a))) := by
      funext y
      by_cases hy : y ∈ Theta.ball v k <;> simp [f, Set.indicator, hy]
    have hmul : ∀ y : v.adicCompletion F,
        A.ψ v (-(y * a)) = A.ψ v (-(a * y)) := by
      intro y
      congr 2
      ring
    calc
      ∫ y, f y * A.ψ v (-(y * a)) ∂μ.μ =
          ∫ y, (Theta.ball v k).indicator (fun y => A.ψ v (-(y * a))) y ∂μ.μ := by
            rw [hfun]
      _ = ∫ y, (Theta.ball v k).indicator (fun y => A.ψ v (-(a * y))) y ∂μ.μ := by
            apply integral_congr_ae
            filter_upwards with y
            by_cases hy : y ∈ Theta.ball v k <;> simp [hy, hmul]
      _ = ∫ y in Theta.ball v k, A.ψ v (-(a * y)) ∂μ.μ := by
            rw [MeasureTheory.integral_indicator hBmeas]
  have hdk : -(d + k : ℤ) = -k + -(d : ℤ) := by omega
  by_cases ha : a ∈ Theta.ball v (-(d + k))
  · have htriv := (hd a).2 ha
    have ha' : a ∈ Theta.ball v (-k + -(d : ℤ)) := by
      simpa only [hdk] using ha
    rw [← hEq, finiteFourier_ball_indicator, dif_pos htriv]
    simp [ha']
  · have hnon : ¬ (∀ x ∈ Theta.ball v k, A.ψ v (-(x * a)) = 1) := by
      intro hall
      exact ha ((hd a).1 hall)
    have hnot' : a ∉ Theta.ball v (-k + -(d : ℤ)) := by
      intro h
      apply ha
      simpa only [hdk] using h
    rw [← hEq, finiteFourier_ball_indicator, dif_neg hnon]
    simp [hnot']

/-- Additive character integral on a compact-open ball, with the conductor cutoff explicit. -/
private theorem finiteAddChar_integral_ball {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) :
    ∃ d : ℕ,
      ∫ y in Theta.ball v k, A.ψ v (-(a * y)) ∂μ.μ =
        if a ∈ Theta.ball v (-(d + k)) then
          (μ.μ.real (Theta.ball v k) : ℂ) else 0 := by
  obtain ⟨d, hd⟩ := finitePsi_ball_annihilator v A k
  exact ⟨d, finiteAddChar_integral_ball_of_annihilator v A μ k a d hd⟩

/-- Translation of a compact-open ball contributes the expected character phase. -/
theorem finiteFourier_translated_ball_indicator {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a y : v.adicCompletion F) :
    finiteFourier v A μ
        (fun x => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a)) y =
      A.ψ v (-(a * y)) *
        finiteFourier v A μ ((Theta.ball v k).indicator (fun _ => (1 : ℂ))) y := by
  let e : v.adicCompletion F ≃ᵐ v.adicCompletion F :=
    (Homeomorph.addRight a).toMeasurableEquiv
  let f : v.adicCompletion F → ℂ := (Theta.ball v k).indicator (fun _ => (1 : ℂ))
  let H : v.adicCompletion F → ℂ := fun x => f (x - a) * A.ψ v (-(x * y))
  have hmap : Measure.map e μ.μ = μ.μ := by
    simpa [e, Homeomorph.addRight] using
      (MeasureTheory.measurePreserving_add_right μ.μ a).map_eq
  have hcomp : (fun x => H (e x)) = fun x => A.ψ v (-(a * y)) *
      (f x * A.ψ v (-(x * y))) := by
    funext x
    have he : e x = x + a := by simp [e, Homeomorph.addRight]
    rw [he]
    dsimp [H]
    have hsub : (x + a) - a = x := by abel
    rw [hsub]
    have harg : -((x + a) * y) = -(x * y) + -(a * y) := by ring
    rw [harg, AddChar.map_add_eq_mul]
    ring
  change ∫ x, H x ∂μ.μ = A.ψ v (-(a * y)) *
    ∫ x, f x * A.ψ v (-(x * y)) ∂μ.μ
  calc
    ∫ x, H x ∂μ.μ = ∫ x, H x ∂Measure.map e μ.μ := by rw [hmap]
    _ = ∫ x, H (e x) ∂μ.μ := MeasureTheory.integral_map_equiv e H
    _ = ∫ x, A.ψ v (-(a * y)) * (f x * A.ψ v (-(x * y))) ∂μ.μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrFun hcomp x
    _ = A.ψ v (-(a * y)) *
        ∫ x, f x * A.ψ v (-(x * y)) ∂μ.μ := integral_const_mul _ _

private theorem finiteFourier_shift_eq_of_compact_support {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (N : ℕ)
    (hN : tsupport f ⊆ Theta.ball v (-(N : ℤ)))
    (y h : v.adicCompletion F) (hh : h ∈ Theta.ball v (N : ℤ)) :
    finiteFourier v A μ f (y + h) = finiteFourier v A μ f y := by
  unfold finiteFourier
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxs : x ∈ Function.support f
  · have hxts : x ∈ tsupport f := subset_closure hxs
    have hxball := hN hxts
    have hxprod : x * h ∈ Theta.ball v 0 := by
      simpa using thetaBall_mul v (-(N : ℤ)) N hxball hh
    have hneg : -(x * h) ∈ Theta.ball v 0 := thetaBall_neg v 0 hxprod
    have hO : -(x * h) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (-(x * h)) ≤ 1
      simpa [Theta.ball] using hneg
    have hψ : A.ψ v (-(x * h)) = 1 := A.integral v _ hO
    have harg : -(x * (y + h)) = -(x * y) + -(x * h) := by ring
    simp [harg, AddChar.map_add_eq_mul, hψ]
  · have hfzero : f x = 0 := by
      by_contra hne
      have hxmem : x ∈ Function.support f := Function.mem_support.mpr hne
      exact hxs hxmem
    simp [hfzero]

theorem finiteFourier_isLocallyConstant {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (hfc : HasCompactSupport f) :
    IsLocallyConstant (finiteFourier v A μ f) := by
  let S := tsupport f
  have hN : ∃ N : ℕ, S ⊆ Theta.ball v (-(N : ℤ)) := by
    by_cases hS : S = ∅
    · exact ⟨0, by simp [hS, S]⟩
    · exact compact_subset_large_thetaBall v S hfc (Set.nonempty_iff_ne_empty.mpr hS)
  obtain ⟨N, hN⟩ := hN
  apply (IsLocallyConstant.iff_exists_open (finiteFourier v A μ f)).2
  intro y
  let U : Set (v.adicCompletion F) := {z | z - y ∈ Theta.ball v (N : ℤ)}
  have hUopen : IsOpen U := by
    apply (thetaBall_open v (N : ℤ)).preimage
    fun_prop
  refine ⟨U, hUopen, ?_, ?_⟩
  · change y - y ∈ Theta.ball v (N : ℤ)
    simp [Theta.ball]
  · intro z hz
    have hshift := finiteFourier_shift_eq_of_compact_support v A μ f N hN y (z - y) hz
    have heq : y + (z - y) = z := by abel
    rw [heq] at hshift
    exact hshift

theorem finiteWeightedIntegrable_of_continuous_compact {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (σ : ℝ) (hσ : 0 < σ) :
    Integrable (fun y : v.adicCompletion F => ‖f y‖ * absFin v y ^ σ)
      (Theta.mulHaarFin μ) := by
  let K := v.adicCompletion F
  let q : ℝ := qv v
  have hq : 1 < q := qv_gt_one v
  let hproper : ProperSpace K := bridgeFin_properSpace v
  letI : ProperSpace K := hproper
  let hAbsContinuous : Continuous (absFin v) := by
    have hEq : absFin v = fun y : K => ‖y‖ := by
      funext y
      exact Theta.absFin_eq_norm v y
    rw [hEq]
    exact continuous_norm
  let hsupp : Set K := tsupport f
  have hcompact : IsCompact hsupp := hfc
  have hcompactF : IsCompact (f '' hsupp) := hcompact.image hf
  obtain ⟨B, hB⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hcompactF.isBounded
  let C : ℝ := max B 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnorm : ∀ y ∈ hsupp, ‖f y‖ ≤ C := by
    intro y hy
    have himage : f y ∈ f '' hsupp := ⟨y, hy, rfl⟩
    have hball := hB himage
    have habs : ‖f y‖ ≤ B := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    exact habs.trans (le_max_left B 1)
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 (hcompact.image hAbsContinuous).isBounded
  let R0 : ℝ := max R 1
  have hR0 : 0 ≤ R0 := le_trans (by norm_num) (le_max_right R 1)
  have hRbound : ∀ y ∈ hsupp, absFin v y ≤ R0 := by
    intro y hy
    have himage : absFin v y ∈ absFin v '' hsupp := ⟨y, hy, rfl⟩
    have hball := hR himage
    have hdist : dist (absFin v y) 0 ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    have habs : |absFin v y| ≤ R := by simpa [Real.dist_eq] using hdist
    have hnonneg : 0 ≤ absFin v y := by rw [Theta.absFin_eq_norm]; exact norm_nonneg _
    exact (le_of_abs_le habs).trans (le_max_left R 1)
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hq
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 hpow) R0)
  have hcut : ∀ y ∈ hsupp, absFin v y ≤ q ^ N := by
    intro y hy
    exact (hRbound y hy).trans (hN N le_rfl)
  have hweightCont : Continuous (fun y : K => absFin v y ^ σ) :=
    (Real.continuous_rpow_const hσ.le).comp hAbsContinuous
  have habsNonneg (y : K) : 0 ≤ absFin v y := by
    rw [Theta.absFin_eq_norm]
    exact norm_nonneg _
  have hmeas : AEStronglyMeasurable (fun y : K => ‖f y‖ * absFin v y ^ σ)
      (Theta.mulHaarFin μ) := (hf.norm.mul hweightCont).aestronglyMeasurable
  have hpoint : ∀ y : K, ‖f y‖ * absFin v y ^ σ ≤
      C * bridgeFinMajorant v σ N y := by
    intro y
    by_cases hcutoff : absFin v y ≤ q ^ N
    · by_cases hy : y ∈ hsupp
      · have hnorm' := hnorm y hy
        have hcutoff' : absFin v y ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N := by
          simpa [q, qv] using hcutoff
        have hmajor : bridgeFinMajorant v σ N y = absFin v y ^ σ := by
          simp [bridgeFinMajorant, hcutoff']
        calc
          ‖f y‖ * absFin v y ^ σ ≤ C * absFin v y ^ σ :=
            mul_le_mul_of_nonneg_right hnorm' (Real.rpow_nonneg (habsNonneg y) σ)
          _ = C * bridgeFinMajorant v σ N y := by rw [hmajor]
      · have hfzero : f y = 0 := by
          by_contra hne
          have hmem : y ∈ Function.support f := Function.mem_support.mpr hne
          exact hy (subset_closure hmem)
        have hcutoff' : absFin v y ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N := by
          simpa [q, qv] using hcutoff
        rw [hfzero]
        simp only [norm_zero, zero_mul]
        rw [show bridgeFinMajorant v σ N y = absFin v y ^ σ by
          simp [bridgeFinMajorant, hcutoff']]
        exact mul_nonneg hC (Real.rpow_nonneg (habsNonneg y) σ)
    · have hy : y ∉ hsupp := by
        intro hy
        exact hcutoff (hcut y hy)
      have hfzero : f y = 0 := by
        by_contra hne
        have hmem : y ∈ Function.support f := Function.mem_support.mpr hne
        exact hy (subset_closure hmem)
      have hcutoff' : ¬ absFin v y ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ N := by
        simpa [q, qv] using hcutoff
      simp [bridgeFinMajorant, hcutoff', hfzero]
  have hdom : Integrable (fun y : K => C * bridgeFinMajorant v σ N y)
      (Theta.mulHaarFin μ) :=
    (bridgeFinMajorant_integrable v μ σ hσ N).const_mul C
  refine hdom.mono' hmeas ?_
  filter_upwards with y
  have ht : 0 ≤ ‖f y‖ * absFin v y ^ σ :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (habsNonneg y) σ)
  rw [Real.norm_eq_abs, abs_of_nonneg ht]
  exact hpoint y

/-- A positive-real-part complex power is integrable on a compact-open valuation ball. -/
private theorem finiteBall_complexPower_integrable {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y : v.adicCompletion F =>
      (Theta.ball v k).indicator (fun _ => (1 : ℂ)) y * (absFin v y : ℂ) ^ s)
      (Theta.mulHaarFin μ) := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let f : K → ℂ := B.indicator (fun _ => (1 : ℂ))
  let g : K → ℂ := fun y => f y * (absFin v y : ℂ) ^ s
  have hBclopen : IsClopen B :=
    ⟨(thetaBall_compact v k).isClosed, thetaBall_open v k⟩
  have hfCont : Continuous f := by
    have hloc : IsLocallyConstant f :=
      ((LocallyConstant.const K (1 : ℂ)).indicator hBclopen).isLocallyConstant
    exact hloc.continuous
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (thetaBall_compact v k)
    exact Set.support_indicator_subset
  have habsCont : Continuous (absFin v) := by
    rw [show absFin v = fun y : K => ‖y‖ by
      funext y
      exact Theta.absFin_eq_norm v y]
    exact continuous_norm
  have hgCont : Continuous g := by
    apply Continuous.mul hfCont
    apply continuous_iff_continuousAt.mpr
    intro y
    have hpowAt : ContinuousAt (fun t : ℝ => (t : ℂ) ^ s) (absFin v y) :=
      Complex.continuousAt_ofReal_cpow_const (absFin v y) s (Or.inl hs)
    exact hpowAt.comp (habsCont.continuousAt (x := y))
  have hreal := finiteWeightedIntegrable_of_continuous_compact v μ f hfCont hfCompact
    s.re hs
  have hnorm : ∀ y : K,
      ‖g y‖ = ‖f y‖ * absFin v y ^ s.re := by
    intro y
    by_cases hy0 : y = 0
    · subst y
      have hB0 : (0 : K) ∈ B := by
        change Valued.v (0 : K) ≤ WithZero.exp (-k)
        simp
      have hsne : s ≠ 0 := by
        intro hz
        rw [hz] at hs
        norm_num at hs
      simp [g, f, Set.indicator, B, hB0, absFin_eq_norm,
        Complex.zero_cpow hsne, Real.zero_rpow hs.ne']
    · have habspos : 0 < absFin v y := absFin_pos hy0
      by_cases hyB : y ∈ B <;>
        simp [g, f, B, Set.indicator, hyB,
          Complex.norm_cpow_eq_rpow_re_of_pos habspos]
  have hnormAE : (fun y : K => ‖g y‖) =ᵐ[Theta.mulHaarFin μ]
      fun y => ‖f y‖ * absFin v y ^ s.re := Filter.Eventually.of_forall hnorm
  have hnormInt : Integrable (fun y : K => ‖g y‖) (Theta.mulHaarFin μ) :=
    hreal.congr hnormAE.symm
  exact (integrable_norm_iff hgCont.aestronglyMeasurable).1 hnormInt

private theorem finiteComplexPower_integrable_of_continuous_compact
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (f : v.adicCompletion F → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y => f y * (absFin v y : ℂ) ^ s) (Theta.mulHaarFin μ) := by
  classical
  let K := v.adicCompletion F
  let S : Set K := tsupport f
  by_cases hSempty : S = ∅
  · have hfzero (x : K) : f x = 0 := by
      by_contra hne
      have hx : x ∈ Function.support f := Function.mem_support.mpr hne
      have hxS : x ∈ S := subset_closure hx
      simpa [S, hSempty] using hxS
    simp [hfzero]
  · have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
    obtain ⟨N, hN⟩ := compact_subset_large_thetaBall v S hfc hSnonempty
    let k : ℤ := -(N : ℤ)
    let B : Set K := Theta.ball v k
    let pow : K → ℂ := fun y => (absFin v y : ℂ) ^ s
    have hsupport : S ⊆ B := by simpa [B, k] using hN
    have hPow := finiteBall_complexPower_integrable v μ k s hs
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1
      (hfc.image hf).isBounded
    let C : ℝ := max R 1
    have hbound : ∀ y : K, ‖f y‖ ≤ C := by
      intro y
      by_cases hy : y ∈ S
      · have him : f y ∈ f '' S := ⟨y, hy, rfl⟩
        have hball := hR him
        have hdist : dist (f y) 0 ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hball
        have hnorm : ‖f y‖ ≤ R := by simpa [dist_zero_right] using hdist
        exact hnorm.trans (le_max_left R 1)
      · have hfzero : f y = 0 := by
          by_contra hne
          have hy' : y ∈ Function.support f := Function.mem_support.mpr hne
          exact hy (subset_closure hy')
        simp [hfzero, C]
    have htwist : Integrable
        (fun y => (B.indicator (fun _ => (1 : ℂ)) y * pow y) * f y)
        (Theta.mulHaarFin μ) :=
      hPow.mul_bdd (c := C) hf.aestronglyMeasurable
        (Filter.Eventually.of_forall hbound)
    have hfun : (fun y => (B.indicator (fun _ => (1 : ℂ)) y * pow y) * f y) =
        fun y => f y * pow y := by
      funext y
      by_cases hy : y ∈ B
      · simp [Set.indicator, hy]
        ring
      · have hyS : y ∉ S := by
          intro hyS
          exact hy (hsupport hyS)
        have hfzero : f y = 0 := by
          by_contra hne
          exact hyS (subset_closure (Function.mem_support.mpr hne))
        simp [Set.indicator, hy, hfzero]
    exact hfun.symm ▸ htwist

private theorem finiteBallTranslate_indicator_regular {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) (t : v.adicCompletion F) :
    IsLocallyConstant (fun x => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - t)) ∧
      HasCompactSupport (fun x => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - t)) := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let C : Set K := {x | x - t ∈ B}
  let f₀ : K → ℂ := B.indicator (fun _ => (1 : ℂ))
  let f : K → ℂ := fun x => f₀ (x - t)
  have hBclopen : IsClopen B := ⟨(thetaBall_compact v k).isClosed, thetaBall_open v k⟩
  have hf₀ : IsLocallyConstant f₀ :=
    ((LocallyConstant.const K (1 : ℂ)).indicator hBclopen).isLocallyConstant
  have hsubCont : Continuous (fun x : K => x - t) := by fun_prop
  have hfloc : IsLocallyConstant f := hf₀.comp_continuous hsubCont
  have hCeq : C = (fun y : K => y + t) '' B := by
    ext x
    constructor
    · intro hx
      exact ⟨x - t, hx, sub_add_cancel x t⟩
    · rintro ⟨y, hy, rfl⟩
      change y + t - t ∈ B
      rw [add_sub_cancel_right]
      exact hy
  have hCcompact : IsCompact C := by
    rw [hCeq]
    exact (thetaBall_compact v k).image (by fun_prop)
  have hsupport : Function.support f ⊆ C := by
    intro x hx
    by_contra hxC
    have hxB : x - t ∉ B := by simpa [C] using hxC
    have hzero : f x = 0 := by simp [f, f₀, B, Set.indicator, hxB]
    exact (Function.mem_support.mp hx) hzero
  have htsupport : tsupport f ⊆ C := closure_minimal hsupport hCcompact.isClosed
  have hfc : HasCompactSupport f := hCcompact.of_isClosed_subset
    (isClosed_tsupport f) htsupport
  constructor
  · simpa [f, f₀, B] using hfloc
  · simpa [f, f₀, B] using hfc

/-- Additive characters in `AddCharData` are locally constant because they are trivial on the
open integer ring. -/
private theorem finiteAddChar_isLocallyConstant {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) : IsLocallyConstant (A.ψ v) := by
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
    simp [O, HeightOneSpectrum.mem_adicCompletionIntegers]
  · intro y hy
    have hψ := A.integral v (y - x) hy
    calc
      A.ψ v y = A.ψ v (x + (y - x)) := by congr 1 <;> abel
      _ = A.ψ v x * A.ψ v (y - x) := AddChar.map_add_eq_mul (A.ψ v) x (y - x)
      _ = A.ψ v x := by rw [hψ]; simp

set_option maxHeartbeats 800000 in
private theorem finiteAddChar_integrable_of_continuous_compact
    {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (f : v.adicCompletion F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (y : v.adicCompletion F) :
    Integrable (fun x => f x * A.ψ v (-(x * y))) μ.μ := by
  let K := v.adicCompletion F
  let g : K → ℂ := fun x => f x * A.ψ v (-(x * y))
  have hχ : Continuous (fun x : K => A.ψ v (-(x * y))) := by
    apply (finiteAddChar_isLocallyConstant v A).continuous.comp
    fun_prop
  have hg : Continuous g := hf.mul hχ
  have hsupport : Function.support g ⊆ tsupport f := by
    intro x hx
    by_contra hnot
    have hfzero : f x = 0 := by
      by_contra hne
      exact hnot (subset_closure (Function.mem_support.mpr hne))
    exact (Function.mem_support.mp hx) (by simp [g, hfzero])
  have htsupport : tsupport g ⊆ tsupport f :=
    closure_minimal hsupport (isClosed_tsupport f)
  have hcompact : IsCompact (tsupport g) := hfc.of_isClosed_subset
    (isClosed_tsupport g) htsupport
  exact hg.integrable_of_hasCompactSupport hcompact

/-- A locally constant finite character is integrable on each compact-open ball. -/
private theorem finiteAddChar_integrableOn_ball {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) :
    IntegrableOn (fun y => A.ψ v (-(a * y))) (Theta.ball v k) μ.μ := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  have harg : Continuous (fun y : K => -(a * y)) := by fun_prop
  have hf : Continuous (fun y : K => A.ψ v (-(a * y))) :=
    (finiteAddChar_isLocallyConstant v A).continuous.comp harg
  have himage : IsCompact ((fun y : K => A.ψ v (-(a * y))) '' B) :=
    (thetaBall_compact v k).image hf
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 himage.isBounded
  let C : ℝ := max R 1
  have hbound : ∀ y ∈ B, ‖A.ψ v (-(a * y))‖ ≤ C := by
    intro y hy
    have him : A.ψ v (-(a * y)) ∈ (fun y : K => A.ψ v (-(a * y))) '' B := ⟨y, hy, rfl⟩
    have hball := hR him
    have hdist : dist (A.ψ v (-(a * y))) 0 ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    have hnorm : ‖A.ψ v (-(a * y))‖ ≤ R := by simpa [dist_zero_right] using hdist
    exact hnorm.trans (le_max_left R 1)
  have hBne : μ.μ B ≠ ⊤ := by
    rw [finiteBall_measure_ennreal]
    exact ENNReal.ofReal_ne_top
  exact Measure.integrableOn_of_bounded hBne hf.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem (thetaBall_open v k).measurableSet] with y hy
      exact hbound y hy)

/-- Restricting multiplicative Haar measure to a finite shell leaves a constant density
multiple of additive Haar measure. -/
private theorem finiteMulHaar_restrict_boundary {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) :
    let T := Theta.ball v k \ Theta.ball v (k + 1)
    let r := (qv v) ^ ((-k : ℤ) : ℝ)
    (Theta.mulHaarFin μ).restrict T =
      ENNReal.ofReal (r⁻¹) • μ.μ.restrict T := by
  let T : Set (v.adicCompletion F) := Theta.ball v k \ Theta.ball v (k + 1)
  let r : ℝ := (qv v) ^ ((-k : ℤ) : ℝ)
  have hTmeas : MeasurableSet T :=
    (thetaBall_open v k).measurableSet.diff (thetaBall_open v (k + 1)).measurableSet
  have hr : 0 < r := Real.rpow_pos_of_pos (by linarith [qv_gt_one v]) _
  have hdens :
      (fun y : v.adicCompletion F => ENNReal.ofReal (absFin v y)⁻¹) =ᵐ[μ.μ.restrict T]
        fun _ => ENNReal.ofReal (r⁻¹) := by
    filter_upwards [ae_restrict_mem hTmeas] with y hy
    have hy' : y ∈ Theta.ball v k \ Theta.ball v (k + 1) := hy
    rw [finiteAbs_eq_qpow_of_boundary v k y hy'.1 hy'.2]
  calc
    (μ.μ.withDensity (fun y => ENNReal.ofReal (absFin v y)⁻¹)).restrict T =
        (μ.μ.restrict T).withDensity (fun y => ENNReal.ofReal (absFin v y)⁻¹) :=
          restrict_withDensity hTmeas _
    _ = (μ.μ.restrict T).withDensity (fun _ => ENNReal.ofReal (r⁻¹)) := by
      exact withDensity_congr_ae hdens
    _ = ENNReal.ofReal (r⁻¹) • μ.μ.restrict T := withDensity_const _

/-- On a finite shell, inserting the radial complex power contributes only its fixed value. -/
private theorem finiteBoundary_charMellin_integral {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) (s : ℂ) :
    ∫ y in Theta.ball v k \ Theta.ball v (k + 1),
      A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
      ((((qv v) ^ ((-k : ℤ) : ℝ))⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s *
          ∫ y in Theta.ball v k \ Theta.ball v (k + 1), A.ψ v (-(a * y)) ∂μ.μ := by
  let T : Set (v.adicCompletion F) := Theta.ball v k \ Theta.ball v (k + 1)
  let r : ℝ := (qv v) ^ ((-k : ℤ) : ℝ)
  have hTmeas : MeasurableSet T :=
    (thetaBall_open v k).measurableSet.diff (thetaBall_open v (k + 1)).measurableSet
  have hr : 0 < r := Real.rpow_pos_of_pos (by linarith [qv_gt_one v]) _
  have hrad : ∀ y ∈ T, (absFin v y : ℂ) ^ s = ((r : ℝ) : ℂ) ^ s := by
    intro y hy
    have hy' : y ∈ Theta.ball v k \ Theta.ball v (k + 1) := hy
    rw [finiteAbs_eq_qpow_of_boundary v k y hy'.1 hy'.2]
  have hrestrict : (Theta.mulHaarFin μ).restrict T =
      ENNReal.ofReal (r⁻¹) • μ.μ.restrict T := finiteMulHaar_restrict_boundary v μ k
  have htoReal : (ENNReal.ofReal (r⁻¹)).toReal = r⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.mpr hr.le)
  calc
    ∫ y in T, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
        (ENNReal.ofReal (r⁻¹)).toReal •
          ∫ y in T, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂μ.μ := by
          change ∫ y, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂
              (Theta.mulHaarFin μ).restrict T = _
          rw [hrestrict, integral_smul_measure]
    _ = ((r⁻¹ : ℝ) : ℂ) *
        ∫ y in T, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂μ.μ := by
          rw [htoReal]
          simp [smul_eq_mul]
    _ = ((r⁻¹ : ℝ) : ℂ) * (((r : ℝ) : ℂ) ^ s *
        ∫ y in T, A.ψ v (-(a * y)) ∂μ.μ) := by
          congr 1
          calc
            ∫ y in T, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂μ.μ =
                ∫ y in T, ((r : ℝ) : ℂ) ^ s * A.ψ v (-(a * y)) ∂μ.μ := by
                  apply integral_congr_ae
                  filter_upwards [ae_restrict_mem hTmeas] with y hy
                  rw [hrad y hy]
                  ring
            _ = ((r : ℝ) : ℂ) ^ s *
                ∫ y in T, A.ψ v (-(a * y)) ∂μ.μ := integral_const_mul _ _
    _ = ((((qv v) ^ ((-k : ℤ) : ℝ))⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s *
          ∫ y in T, A.ψ v (-(a * y)) ∂μ.μ := by dsimp [r]; ring

/-- Additive character integral on a finite valuation shell is the difference of its two ball
integrals. -/
private theorem finiteAddChar_shell_integral {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (j : ℤ) (a : v.adicCompletion F) :
    ∫ y in Theta.ball v j \ Theta.ball v (j + 1), A.ψ v (-(a * y)) ∂μ.μ =
      (if a ∈ Theta.ball v (-(d + j)) then (μ.μ.real (Theta.ball v j) : ℂ) else 0) -
      (if a ∈ Theta.ball v (-(d + (j + 1))) then
        (μ.μ.real (Theta.ball v (j + 1)) : ℂ) else 0) := by
  have hOn := finiteAddChar_integrableOn_ball v A μ j a
  rw [setIntegral_sdiff (thetaBall_open v (j + 1)).measurableSet hOn
    (thetaBall_mono v (by omega))]
  rw [finiteAddChar_integral_ball_of_annihilator v A μ j a d (hd j)]
  rw [finiteAddChar_integral_ball_of_annihilator v A μ (j + 1) a d (hd (j + 1))]

/-- The additive character shell integral changes only at the conductor threshold. -/
private theorem finiteAddChar_shell_integral_log {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (a : v.adicCompletion F) (ha : a ≠ 0) (b : ℤ)
    (hb : Valued.v a = WithZero.exp b) (j : ℤ) :
    ∫ y in Theta.ball v j \ Theta.ball v (j + 1), A.ψ v (-(a * y)) ∂μ.μ =
      if b - (d : ℤ) ≤ j then
        (((qv v) ^ ((-j : ℤ) : ℝ) * (1 - (qv v)⁻¹) : ℝ) : ℂ)
      else if b - (d : ℤ) = j + 1 then
        -(((qv v) ^ ((-(j + 1 : ℤ)) : ℝ) : ℝ) : ℂ)
      else 0 := by
  have hdual : ∀ m : ℤ,
      a ∈ Theta.ball v (-(d + m)) ↔ b - (d : ℤ) ≤ m := by
    intro m
    constructor
    · intro h
      have h' : Valued.v a ≤ WithZero.exp ((d : ℤ) + m) := by
        change Valued.v a ≤ WithZero.exp (-(-(d + m))) at h
        simpa only [neg_neg] using h
      rw [hb] at h'
      have hbm := (WithZero.exp_le_exp).1 h'
      omega
    · intro h
      change Valued.v a ≤ WithZero.exp (-(-(d + m)))
      rw [hb]
      apply (WithZero.exp_le_exp).2
      omega
  rw [finiteAddChar_shell_integral v A μ d hd j a, hdual j, hdual (j + 1)]
  by_cases h0 : b - (d : ℤ) ≤ j
  · have h1 : b - (d : ℤ) ≤ j + 1 := by omega
    have hBne : μ.μ (Theta.ball v j) ≠ ⊤ := by
      rw [finiteBall_measure_ennreal]
      exact ENNReal.ofReal_ne_top
    have hReal : μ.μ.real (Theta.ball v j) - μ.μ.real (Theta.ball v (j + 1)) =
        (qv v) ^ ((-j : ℤ) : ℝ) * (1 - (qv v)⁻¹) := by
      calc
        μ.μ.real (Theta.ball v j) - μ.μ.real (Theta.ball v (j + 1)) =
            μ.μ.real (Theta.ball v j \ Theta.ball v (j + 1)) :=
              (measureReal_sdiff (thetaBall_mono v (by omega))
                (thetaBall_open v (j + 1)).measurableSet hBne).symm
        _ = _ := finiteBall_boundary_measure v μ j
    simpa [h0, h1] using congrArg (fun x : ℝ => (x : ℂ)) hReal
  · by_cases hEq : b - (d : ℤ) = j + 1
    · simp [h0, hEq, finiteBall_measure]
    · have h1 : ¬ b - (d : ℤ) ≤ j + 1 := by omega
      simp [h0, hEq, h1]

/-- A finite character twist preserves positive-real-part Mellin integrability on a ball. -/
private theorem finiteBall_charPower_integrable {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun y : v.adicCompletion F =>
      (Theta.ball v k).indicator (fun y => A.ψ v (-(a * y))) y *
        (absFin v y : ℂ) ^ s) (Theta.mulHaarFin μ) := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let f : K → ℂ := B.indicator (fun _ => (1 : ℂ))
  let χ : K → ℂ := fun y => A.ψ v (-(a * y))
  let φ : K → ℂ := fun y => f y * χ y
  let pow : K → ℂ := fun y => (absFin v y : ℂ) ^ s
  have hBclopen : IsClopen B := ⟨(thetaBall_compact v k).isClosed, thetaBall_open v k⟩
  have hIndLC : IsLocallyConstant f :=
    ((LocallyConstant.const K (1 : ℂ)).indicator hBclopen).isLocallyConstant
  have hArgCont : Continuous (fun y : K => -(a * y)) := by fun_prop
  have hχLC : IsLocallyConstant χ :=
    (finiteAddChar_isLocallyConstant v A).comp_continuous hArgCont
  have hφCont : Continuous φ := by
    have hφLC : IsLocallyConstant φ := hIndLC.comp₂ hχLC (fun z w => z * w)
    exact hφLC.continuous
  have himage : IsCompact (φ '' B) := (thetaBall_compact v k).image hφCont
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 himage.isBounded
  let C : ℝ := max R 1
  have hφbound : ∀ y : K, ‖φ y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ B
    · have him : φ y ∈ φ '' B := ⟨y, hy, rfl⟩
      have hball := hR him
      have hdist : dist (φ y) 0 ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hball
      have hnorm : ‖φ y‖ ≤ R := by
        simpa [dist_zero_right] using hdist
      exact hnorm.trans (le_max_left R 1)
    · have hfzero : f y = 0 := by simp [f, B, Set.indicator, hy]
      simp [φ, hfzero, C]
  have hG := finiteBall_complexPower_integrable v μ k s hs
  have hGtwist : Integrable (fun y : K => (f y * pow y) * φ y) (Theta.mulHaarFin μ) :=
    hG.mul_bdd (c := C) hφCont.aestronglyMeasurable
      (Filter.Eventually.of_forall hφbound)
  have hEq : (fun y : K => (f y * pow y) * φ y) =
      (fun y => B.indicator (fun y => A.ψ v (-(a * y))) y * pow y) := by
    funext y
    by_cases hy : y ∈ B <;> simp [f, φ, pow, B, χ, Set.indicator, hy] <;> ring
  exact hEq ▸ hGtwist

/-- The weighted Mellin integral on one finite-place shell is a constant times its
fixed radial complex power. -/
private theorem finiteBoundary_shell_complexPower_integral {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) (s : ℂ) :
    ∫ y in Theta.ball v k \ Theta.ball v (k + 1), (absFin v y : ℂ) ^ s
      ∂Theta.mulHaarFin μ =
      ((1 - (qv v)⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s := by
  let T : Set (v.adicCompletion F) := Theta.ball v k \ Theta.ball v (k + 1)
  let c : ℂ := (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s
  have hTmeas : MeasurableSet T :=
    (thetaBall_open v k).measurableSet.diff (thetaBall_open v (k + 1)).measurableSet
  have hfactor : 0 < 1 - (qv v)⁻¹ := by
    have hqpos : 0 < qv v := by linarith [qv_gt_one v]
    have hinv : (qv v)⁻¹ < 1 := (inv_lt_one₀ hqpos).2 (qv_gt_one v)
    linarith
  have hconst : ∀ y ∈ T, (absFin v y : ℂ) ^ s = c := by
    intro y hy
    have hy' : y ∈ Theta.ball v k \ Theta.ball v (k + 1) := hy
    dsimp [c]
    rw [finiteAbs_eq_qpow_of_boundary v k y hy'.1 hy'.2]
  calc
    ∫ y in T, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
        ∫ y in T, c ∂Theta.mulHaarFin μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hTmeas] with y hy
          exact hconst y hy
    _ = ((Theta.mulHaarFin μ).real T : ℂ) * c := by simp [integral_const, smul_eq_mul]
    _ = ((1 - (qv v)⁻¹ : ℝ) : ℂ) * c := by
      congr 1
      simp [Measure.real_def, T, finiteMulHaar_boundary_measure, hfactor.le]

/-- A valuation ball is the disjoint union of its shells and the origin. -/
private theorem finiteBall_eq_singleton_union_shells {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) :
    Theta.ball v k = {0} ∪ ⋃ n : ℕ,
      Theta.ball v (k + n) \ Theta.ball v (k + n + 1) := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · subst x
      simp
    · right
      have hvne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
      let a : ℤ := WithZero.log (Valued.v x)
      have hval : Valued.v x = WithZero.exp a := (WithZero.exp_log hvne).symm
      have ha : a ≤ -k := by
        have h := hx
        change Valued.v x ≤ WithZero.exp (-k) at h
        rw [hval] at h
        exact (WithZero.exp_le_exp).1 h
      let n : ℕ := Int.toNat (-k - a)
      have hna : 0 ≤ -k - a := by omega
      have hnat : (n : ℤ) = -k - a := by
        simp [n, Int.toNat_of_nonneg hna]
      have han : a = -(k + n) := by omega
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      constructor
      · change Valued.v x ≤ WithZero.exp (-(k + n))
        rw [hval]
        exact (WithZero.exp_le_exp).2 (by omega)
      · intro hnext
        change Valued.v x ≤ WithZero.exp (-(k + n + 1)) at hnext
        rw [hval] at hnext
        have hnext' := (WithZero.exp_le_exp).1 hnext
        omega
  · intro hx
    simp only [Set.mem_union] at hx
    rcases hx with hx0 | hxsh
    · rcases Set.mem_singleton_iff.mp hx0 with rfl
      change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-k)
      simp
    · rcases Set.mem_iUnion.mp hxsh with ⟨n, hn⟩
      exact thetaBall_mono v (by omega) hn.1

/-- Integrate any integrable function vanishing at the origin by summing its valuation shells. -/
private theorem finiteBall_integral_eq_shell_tsum {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (hf : IntegrableOn f (Theta.ball v k) μ)
    (hf0 : f 0 = 0) :
    ∫ y in Theta.ball v k, f y ∂μ =
      ∑' n : ℕ, ∫ y in Theta.ball v (k + n) \ Theta.ball v (k + n + 1), f y ∂μ := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let shell : ℕ → Set K := fun n => Theta.ball v (k + n) \ Theta.ball v (k + n + 1)
  let U : Set K := ⋃ n : ℕ, shell n
  have hUnion : {0} ∪ U = B := by
    simpa [B, U, shell] using (finiteBall_eq_singleton_union_shells v k).symm
  have h0meas : MeasurableSet ({0} : Set K) := measurableSet_singleton (0 : K)
  have hUsub : U ⊆ B := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
    exact thetaBall_mono v (by omega) hyn.1
  have hUnionInt : ∫ y in B, f y ∂μ = ∫ y in U, f y ∂μ := by
    rw [← hUnion]
    rw [Set.union_comm]
    exact integral_union_eq_left_of_forall h0meas (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hf0)
  have hUintegrable : IntegrableOn f U μ := hf.mono_set hUsub
  have hmeas : ∀ n : ℕ, MeasurableSet (shell n) := fun n =>
    (thetaBall_open v (k + n)).measurableSet.diff (thetaBall_open v (k + n + 1)).measurableSet
  have hpair : Pairwise (fun n m => Disjoint (shell n) (shell m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro y hyn hym
    rcases (Set.mem_sdiff y).mp hyn with ⟨_, hnotn⟩
    rcases (Set.mem_sdiff y).mp hym with ⟨hym, hnotm⟩
    have hnm' : n < m ∨ m < n := by omega
    rcases hnm' with hnm' | hmn'
    · exact hnotn (thetaBall_mono v (by omega) hym)
    · exact hnotm (thetaBall_mono v (by omega) hyn.1)
  have hsum := integral_iUnion hmeas hpair hUintegrable
  calc
    ∫ y in B, f y ∂μ = ∫ y in U, f y ∂μ := hUnionInt
    _ = ∑' n : ℕ, ∫ y in shell n, f y ∂μ := hsum

/-- The disjoint-shell decomposition also exposes summability of the shell integrals. -/
private theorem finiteBall_integral_hasSum_shells {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (hf : IntegrableOn f (Theta.ball v k) μ)
    (hf0 : f 0 = 0) :
    HasSum (fun n : ℕ => ∫ y in Theta.ball v (k + n) \ Theta.ball v (k + n + 1), f y ∂μ)
      (∫ y in Theta.ball v k, f y ∂μ) := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let shell : ℕ → Set K := fun n => Theta.ball v (k + n) \ Theta.ball v (k + n + 1)
  let U : Set K := ⋃ n : ℕ, shell n
  have hUnion : {0} ∪ U = B := by
    simpa [B, U, shell] using (finiteBall_eq_singleton_union_shells v k).symm
  have h0meas : MeasurableSet ({0} : Set K) := measurableSet_singleton (0 : K)
  have hUsub : U ⊆ B := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
    exact thetaBall_mono v (by omega) hyn.1
  have hUnionInt : ∫ y in B, f y ∂μ = ∫ y in U, f y ∂μ := by
    rw [← hUnion, Set.union_comm]
    exact integral_union_eq_left_of_forall h0meas (by
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hf0)
  have hUintegrable : IntegrableOn f U μ := hf.mono_set hUsub
  have hmeas : ∀ n : ℕ, MeasurableSet (shell n) := fun n =>
    (thetaBall_open v (k + n)).measurableSet.diff (thetaBall_open v (k + n + 1)).measurableSet
  have hpair : Pairwise (fun n m => Disjoint (shell n) (shell m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro y hyn hym
    rcases (Set.mem_sdiff y).mp hyn with ⟨_, hnotn⟩
    rcases (Set.mem_sdiff y).mp hym with ⟨hym, hnotm⟩
    have hnm' : n < m ∨ m < n := by omega
    rcases hnm' with hnm' | hmn'
    · exact hnotn (thetaBall_mono v (by omega) hym)
    · exact hnotm (thetaBall_mono v (by omega) hyn.1)
  have hsum := hasSum_integral_iUnion hmeas hpair hUintegrable
  rw [← hUnionInt] at hsum
  exact hsum

/-- A finite character twist admits the same shell decomposition as the radial power. -/
private theorem finiteBall_charMellin_integral_tsum {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v k, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin μ =
      ∑' n : ℕ, ∫ y in Theta.ball v (k + n) \ Theta.ball v (k + n + 1),
        A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ := by
  let B : Set (v.adicCompletion F) := Theta.ball v k
  let p : v.adicCompletion F → ℂ := fun y => A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
  have hG := finiteBall_charPower_integrable v A μ k a s hs
  have hBallOn : IntegrableOn p B (Theta.mulHaarFin μ) := by
    apply hG.integrableOn.congr_fun
    · intro y hy
      simp [p, B, Set.indicator, hy]
    · exact (thetaBall_open v k).measurableSet
  have hsne : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  have hp0 : p 0 = 0 := by
    simp [p, absFin_eq_norm, Complex.zero_cpow hsne]
  simpa [B, p] using finiteBall_integral_eq_shell_tsum v k (Theta.mulHaarFin μ) p hBallOn hp0

/-- Rewrite the character-twisted ball Mellin integral using additive character shell integrals. -/
private theorem finiteBall_charMellin_additive_shell_series {F : Type}
    [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v)
    (k : ℤ) (a : v.adicCompletion F) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v k, A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin μ =
      ∑' n : ℕ,
        ((((qv v) ^ ((-(k + n : ℤ) : ℤ) : ℝ))⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((-(k + n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s *
          ∫ y in Theta.ball v (k + n) \ Theta.ball v (k + n + 1),
            A.ψ v (-(a * y)) ∂μ.μ := by
  rw [finiteBall_charMellin_integral_tsum v A μ k a s hs]
  apply tsum_congr
  intro n
  rw [finiteBoundary_charMellin_integral]

/-- Mellin integral on one finite-place shell. -/
private theorem finiteBoundary_shell_integral {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) (s : ℂ) :
    ∫ y in Theta.ball v k \ Theta.ball v (k + 1), (absFin v y : ℂ) ^ s
      ∂Theta.mulHaarFin μ =
      ((1 - (qv v)⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s := by
  let T : Set (v.adicCompletion F) := Theta.ball v k \ Theta.ball v (k + 1)
  let c : ℂ := (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s
  have hTmeas : MeasurableSet T :=
    (thetaBall_open v k).measurableSet.diff (thetaBall_open v (k + 1)).measurableSet
  have hfactor : 0 < 1 - (qv v)⁻¹ := by
    have hqpos : 0 < qv v := by linarith [qv_gt_one v]
    have hinv : (qv v)⁻¹ < 1 := (inv_lt_one₀ hqpos).2 (qv_gt_one v)
    linarith
  have hconst : ∀ y ∈ T, (absFin v y : ℂ) ^ s = c := by
    intro y hy
    have hy' : y ∈ Theta.ball v k \ Theta.ball v (k + 1) := hy
    dsimp [c]
    rw [finiteAbs_eq_qpow_of_boundary v k y hy'.1 hy'.2]
  have hmass : (Theta.mulHaarFin μ).real T = 1 - (qv v)⁻¹ := by
    simp [Measure.real_def, T, finiteMulHaar_boundary_measure, hfactor.le]
  calc
    ∫ y in T, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
        ∫ y in T, c ∂Theta.mulHaarFin μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hTmeas] with y hy
          exact hconst y hy
    _ = ((Theta.mulHaarFin μ).real T : ℂ) * c := by simp [integral_const, smul_eq_mul]
    _ = ((1 - (qv v)⁻¹ : ℝ) : ℂ) * c := by rw [hmass]

/-- Split the radial complex power on the `n`th smaller shell into a fixed factor and a
geometric ratio. -/
private theorem finiteRadius_cpow_nat {q : ℝ} (hq : 1 < q) (k : ℤ) (n : ℕ) (s : ℂ) :
    (((q ^ ((-(k + n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s) =
      (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) *
        (((q⁻¹ : ℝ) : ℂ) ^ s) ^ n := by
  have hqpos : 0 < q := by linarith
  have hqn : q ^ (-(n : ℝ)) = (q⁻¹) ^ n := by
    rw [Real.rpow_neg hqpos.le, Real.rpow_natCast, inv_pow]
  have hrad : q ^ ((-(k + n : ℤ) : ℤ) : ℝ) =
      q ^ ((-k : ℤ) : ℝ) * (q⁻¹) ^ n := by
    have hexp : ((-(k + n : ℤ) : ℤ) : ℝ) = ((-k : ℤ) : ℝ) + (-(n : ℝ)) := by
      push_cast
      ring
    rw [hexp, Real.rpow_add hqpos, hqn]
  have ha : 0 ≤ q ^ ((-k : ℤ) : ℝ) := Real.rpow_nonneg hqpos.le _
  have hb : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
  calc
    _ = (((q ^ ((-k : ℤ) : ℝ) * (q⁻¹) ^ n : ℝ) : ℝ) : ℂ) ^ s := by rw [hrad]
    _ = (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) *
        ((((q⁻¹) ^ n : ℝ) : ℂ) ^ s) := by
          rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha (pow_nonneg hb n) s]
    _ = (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) *
        ((q⁻¹ : ℂ) ^ ((n : ℂ) * s)) := by
          congr 1
          simpa [Complex.ofReal_inv] using (Complex.cpow_mul_ofReal_nonneg hb (n : ℝ) s).symm
    _ = (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) *
        (((q⁻¹ : ℝ) : ℂ) ^ s) ^ n := by
          rw [Complex.cpow_nat_mul]
          simp

/-- The finite-place ball Mellin integral is the sum of its valuation-shell integrals. -/
private theorem finiteBall_mellin_integral_tsum {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v k, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
      ∑' n : ℕ,
        ((1 - (qv v)⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((-(k + n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let p : K → ℂ := fun y => (absFin v y : ℂ) ^ s
  let shell : ℕ → Set K := fun n => Theta.ball v (k + n) \ Theta.ball v (k + n + 1)
  let pieces : Option ℕ → Set K := fun o => o.elim {0} shell
  have hUnion : (⋃ o : Option ℕ, pieces o) = B := by
    rw [Set.iUnion_option]
    change {0} ∪ ⋃ n : ℕ, shell n = B
    simpa [B, shell] using (finiteBall_eq_singleton_union_shells v k).symm
  have hmeas : ∀ o : Option ℕ, MeasurableSet (pieces o) := by
    intro o
    cases o with
    | none => exact measurableSet_singleton (0 : K)
    | some n =>
        exact (thetaBall_open v (k + n)).measurableSet.diff
          (thetaBall_open v (k + n + 1)).measurableSet
  have hpair : Pairwise (fun i j => Disjoint (pieces i) (pieces j)) := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hij rfl)
        | some n =>
            apply Set.disjoint_left.mpr
            intro y hy0 hys
            rcases Set.mem_singleton_iff.mp hy0 with rfl
            rcases (Set.mem_sdiff (0 : K)).mp hys with ⟨_, hn⟩
            exact hn (by
              change Valued.v (0 : K) ≤ WithZero.exp (-(k + n + 1))
              simp)
    | some n =>
        cases j with
        | none =>
            apply Set.disjoint_left.mpr
            intro y hys hy0
            rcases Set.mem_singleton_iff.mp hy0 with rfl
            rcases (Set.mem_sdiff (0 : K)).mp hys with ⟨_, hn⟩
            exact hn (by
              change Valued.v (0 : K) ≤ WithZero.exp (-(k + n + 1))
              simp)
        | some m =>
            apply Set.disjoint_left.mpr
            intro y hyn hym
            rcases (Set.mem_sdiff y).mp hyn with ⟨_, hnotn⟩
            rcases (Set.mem_sdiff y).mp hym with ⟨hym, hnotm⟩
            have hnm0 : n ≠ m := by
              intro hEq
              exact hij (congrArg some hEq)
            have hnm : n < m ∨ m < n := by omega
            rcases hnm with hnm | hmn
            · have hsub : Theta.ball v (k + m) ⊆ Theta.ball v (k + n + 1) :=
                thetaBall_mono v (by omega)
              exact hnotn (hsub hym)
            · have hsub : Theta.ball v (k + n) ⊆ Theta.ball v (k + m + 1) :=
                thetaBall_mono v (by omega)
              exact hnotm (hsub hyn.1)
  have hBallOn : IntegrableOn p B (Theta.mulHaarFin μ) := by
    have hG := finiteBall_complexPower_integrable v μ k s hs
    apply hG.integrableOn.congr_fun
    · intro y hy
      simp [p, B, Set.indicator, hy]
    · exact (thetaBall_open v k).measurableSet
  have hsne : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    norm_num at hs
  have h0meas : MeasurableSet ({0} : Set K) := measurableSet_singleton (0 : K)
  have hp0 : ∀ y ∈ ({0} : Set K), p y = 0 := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    simp [p, absFin_eq_norm, Complex.zero_cpow hsne]
  let U : Set K := ⋃ n : ℕ, shell n
  have hUnion' : U ∪ ({0} : Set K) = B := by
    calc
      U ∪ {0} = {0} ∪ U := Set.union_comm _ _
      _ = ⋃ o : Option ℕ, pieces o := by
        rw [Set.iUnion_option]
        simp [pieces, U]
      _ = B := hUnion
  have hUnionInt : ∫ y in B, p y ∂Theta.mulHaarFin μ =
      ∫ y in U, p y ∂Theta.mulHaarFin μ := by
    rw [← hUnion']
    exact integral_union_eq_left_of_forall h0meas hp0
  have hUsub : U ⊆ B := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
    exact thetaBall_mono v (by omega) hyn.1
  have hUintegrable : IntegrableOn p U (Theta.mulHaarFin μ) := hBallOn.mono_set hUsub
  have hNatMeas : ∀ n : ℕ, MeasurableSet (shell n) := fun n => hmeas (some n)
  have hNatPair : Pairwise (fun n m => Disjoint (shell n) (shell m)) := by
    intro n m hnm
    exact hpair (i := some n) (j := some m) (by simpa using hnm)
  have hsumNat := integral_iUnion hNatMeas hNatPair hUintegrable
  rw [hUnionInt, hsumNat]
  apply tsum_congr
  intro n
  simpa [shell, p] using finiteBoundary_shell_integral v μ (k + n) s

/-- Closed geometric-series form of the finite-place ball Mellin integral. -/
private theorem finiteBall_mellin_integral_closed {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v k, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
      ((1 - (qv v)⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s *
        (1 - (((qv v)⁻¹ : ℝ) : ℂ) ^ s)⁻¹ := by
  let factor : ℂ := ((1 - (qv v)⁻¹ : ℝ) : ℂ)
  let base : ℂ := (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ s
  let ratio : ℂ := (((qv v)⁻¹ : ℝ) : ℂ) ^ s
  have hqpos : 0 < qv v := by linarith [qv_gt_one v]
  have hInvPos : 0 < (qv v)⁻¹ := inv_pos.mpr hqpos
  have hInvLt : (qv v)⁻¹ < 1 := (inv_lt_one₀ hqpos).2 (qv_gt_one v)
  have hratio : ‖ratio‖ < 1 := by
    dsimp [ratio]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hInvPos s]
    exact Real.rpow_lt_one (inv_nonneg.mpr hqpos.le) hInvLt hs
  rw [finiteBall_mellin_integral_tsum v μ k s hs]
  calc
    ∑' n : ℕ, factor *
        (((qv v) ^ ((-(k + n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s =
        ∑' n : ℕ, (factor * base) * ratio ^ n := by
          apply tsum_congr
          intro n
          dsimp [factor, base, ratio]
          rw [finiteRadius_cpow_nat (q := qv v) (qv_gt_one v) k n s]
          ring
    _ = factor * base * ∑' n : ℕ, ratio ^ n := by rw [tsum_mul_left]
    _ = factor * base * (1 - ratio)⁻¹ := by rw [tsum_geometric_of_norm_lt_one hratio]
    _ = _ := by rfl

/-- The finite-place Tate scalar dictated by the conductor and multiplicative-Haar normalization. -/
private def finiteTateLocalFactor {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (d : ℕ) (s : ℂ) : ℂ :=
  ((((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s) *
    (1 - (((qv v)⁻¹ : ℝ) : ℂ) ^ (1 - s)) *
      (1 - (((qv v)⁻¹ : ℝ) : ℂ) ^ s)⁻¹

/-- Nonvanishing of the finite Tate scalar at the fixed positive exponent. -/
private theorem finiteTateLocalFactor_ne_zero {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (d : ℕ) : finiteTateLocalFactor v d (1 / 6) ≠ 0 := by
  let q : ℝ := qv v
  let u : ℂ := ((q⁻¹ : ℝ) : ℂ)
  have hq1 : 1 < q := qv_gt_one v
  have hq0 : 0 < q := by linarith
  have hu0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have hu1 : q⁻¹ < 1 := (inv_lt_one₀ hq0).2 hq1
  have hpow_lt : ∀ w : ℂ, 0 < w.re → ‖u ^ w‖ < 1 := by
    intro w hw
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    exact Real.rpow_lt_one (inv_nonneg.mpr hq0.le) hu1 hw
  have hden : 1 - u ^ (1 / 6 : ℂ) ≠ 0 := by
    intro h
    have hz : u ^ (1 / 6 : ℂ) = 1 := (sub_eq_zero.mp h).symm
    have hlt := hpow_lt (1 / 6 : ℂ) (by norm_num)
    rw [hz] at hlt
    norm_num at hlt
  have hnum : 1 - u ^ (1 - (1 / 6 : ℂ)) ≠ 0 := by
    intro h
    have hz : u ^ (1 - (1 / 6 : ℂ)) = 1 := (sub_eq_zero.mp h).symm
    have hlt := hpow_lt (1 - (1 / 6 : ℂ)) (by norm_num)
    rw [hz] at hlt
    norm_num at hlt
  have hbase : ((q ^ (d : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq0 _).ne'
  have hbasepow : (((q ^ (d : ℝ) : ℝ) : ℂ) ^ (1 / 6 : ℂ)) ≠ 0 :=
    (Complex.cpow_ne_zero_iff).2 (Or.inl hbase)
  unfold finiteTateLocalFactor
  dsimp [q, u]
  exact mul_ne_zero (mul_ne_zero hbasepow hnum) (inv_ne_zero hden)

/-- The finite absolute value is the residue cardinality to the valuation logarithm. -/
private theorem finiteAbs_eq_qpow_log {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (a : v.adicCompletion F) (ha : a ≠ 0) (b : ℤ)
    (hb : Valued.v a = WithZero.exp b) :
    absFin v a = (qv v) ^ (b : ℝ) := by
  have hball : a ∈ Theta.ball v (-b) := by
    change Valued.v a ≤ WithZero.exp (-(-b))
    rw [hb]
    exact le_of_eq (congrArg WithZero.exp (by omega))
  have hnext : a ∉ Theta.ball v (-b + 1) := by
    intro h
    change Valued.v a ≤ WithZero.exp (-(-b + 1)) at h
    rw [hb] at h
    have hle := (WithZero.exp_le_exp).1 h
    omega
  rw [finiteAbs_eq_qpow_of_boundary v (-b) a hball hnext]
  congr 1
  norm_cast
  omega

private theorem finiteRadius_log_ratio {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (d : ℕ) (a : v.adicCompletion F) (ha : a ≠ 0) (b : ℤ)
    (hb : Valued.v a = WithZero.exp b) :
    (qv v) ^ ((-((b : ℤ) - d) : ℤ) : ℝ) =
      (qv v) ^ (d : ℝ) / absFin v a := by
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  rw [finiteAbs_eq_qpow_log v a ha b hb]
  have hexp : (-((b : ℤ) - d) : ℤ) = (d : ℤ) - b := by omega
  rw [hexp]
  have hexpR : (((d : ℤ) - b : ℤ) : ℝ) = (d : ℝ) - (b : ℝ) := by
    push_cast
    ring
  rw [hexpR, Real.rpow_sub hq]

private theorem finiteRadius_log_ratio_cpow {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (d : ℕ) (a : v.adicCompletion F) (ha : a ≠ 0) (b : ℤ)
    (hb : Valued.v a = WithZero.exp b) (s : ℂ) :
    ((((qv v) ^ ((-((b : ℤ) - d) : ℤ) : ℝ) : ℝ) : ℂ) ^ s) =
      (((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s * ((absFin v a : ℝ) : ℂ) ^ (-s) := by
  rw [finiteRadius_log_ratio v d a ha b hb, Complex.ofReal_div]
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have hnum : 0 ≤ (qv v) ^ (d : ℝ) := Real.rpow_nonneg hq.le _
  have hden : 0 ≤ absFin v a := by rw [Theta.absFin_eq_norm]; exact norm_nonneg _
  rw [Complex.div_cpow_ofReal_nonneg hnum hden, Complex.cpow_neg]
  ring

private theorem finiteRadius_real_succ {q : ℝ} (hq : 0 < q) (j : ℤ) :
    q ^ ((-(j + 1 : ℤ) : ℤ) : ℝ) = q ^ ((-j : ℤ) : ℝ) / q := by
  have hexp : ((-(j + 1 : ℤ) : ℤ) : ℝ) = ((-j : ℤ) : ℝ) - 1 := by
    push_cast
    ring
  rw [hexp, Real.rpow_sub hq]
  simp

private theorem finiteBoundary_charMellin_integral_log {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (a : v.adicCompletion F) (ha : a ≠ 0) (b : ℤ)
    (hb : Valued.v a = WithZero.exp b) (j : ℤ) (s : ℂ) :
    ∫ y in Theta.ball v j \ Theta.ball v (j + 1),
      A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
      if b - (d : ℤ) ≤ j then
        (((1 - (qv v)⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((-j : ℤ) : ℝ) : ℝ) : ℂ) ^ s)
      else if b - (d : ℤ) = j + 1 then
        -(((qv v)⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((-j : ℤ) : ℝ) : ℝ) : ℂ) ^ s
      else 0 := by
  rw [finiteBoundary_charMellin_integral,
    finiteAddChar_shell_integral_log v A μ d hd a ha b hb j]
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have hr : 0 < (qv v) ^ ((-j : ℤ) : ℝ) := Real.rpow_pos_of_pos hq _
  have hrne : (((qv v) ^ ((-j : ℤ) : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr.ne'
  by_cases h1 : b - (d : ℤ) ≤ j
  · simp only [if_pos h1]
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [hrne]
  · by_cases h2 : b - (d : ℤ) = j + 1
    · simp only [if_neg h1, if_pos h2]
      have hnext := finiteRadius_real_succ hq j
      have hnext' : (qv v) ^ (-(j + 1 : ℤ) : ℝ) =
          (qv v) ^ ((-j : ℤ) : ℝ) / qv v := by
        simpa only [Int.cast_neg, Int.cast_add, Int.cast_one] using hnext
      rw [hnext', Complex.ofReal_div, Complex.ofReal_inv]
      field_simp [hrne, Complex.ofReal_ne_zero.mpr hq.ne']
      simp [Complex.ofReal_ne_zero.mpr hq.ne']
    · simp [h1, h2]

/-- Outside the original ball, the twisted dual-ball Mellin integral has one exceptional shell;
the remaining shells form the centered ball Mellin integral at the conductor threshold. -/
private theorem finiteBall_charMellin_outside_decompose {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (k : ℤ) (a : v.adicCompletion F) (ha : a ≠ 0) (hout : a ∉ Theta.ball v k)
    (b : ℤ) (hb : Valued.v a = WithZero.exp b) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v (-(d + k)), A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin μ =
      -(((qv v)⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((-(b - (d : ℤ) - 1 : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s +
        ∫ y in Theta.ball v (b - (d : ℤ)), (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ := by
  let m : ℤ := -(d + k)
  let t : ℤ := b - (d : ℤ)
  let N : ℕ := Int.toNat (b + k)
  have hbgt : -k < b := by
    have hnot : ¬ Valued.v a ≤ WithZero.exp (-k) := by
      change ¬ Valued.v a ≤ WithZero.exp (-k)
      exact hout
    rw [hb] at hnot
    have hnot' : ¬ b ≤ -k := by
      intro hle
      exact hnot ((WithZero.exp_le_exp).2 hle)
    omega
  have hN : (N : ℤ) = b + k := by
    have hnonneg : 0 ≤ b + k := by omega
    simp [N, Int.toNat_of_nonneg hnonneg]
  have hNpos : 0 < N := by omega
  have hindex : m + (N : ℤ) = t := by
    dsimp [m, t]
    rw [hN]
    omega
  let B : Set (v.adicCompletion F) := Theta.ball v m
  let p : v.adicCompletion F → ℂ := fun y => A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
  let g : ℕ → ℂ := fun n =>
    ∫ y in Theta.ball v (m + (n : ℤ)) \ Theta.ball v (m + (n : ℤ) + 1), p y
      ∂Theta.mulHaarFin μ
  have hterm (n : ℕ) :
      g n = if t ≤ m + (n : ℤ) then
          (((1 - (qv v)⁻¹ : ℝ) : ℂ) *
            (((qv v) ^ ((-(m + (n : ℤ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s)
        else if t = m + (n : ℤ) + 1 then
          -(((qv v)⁻¹ : ℝ) : ℂ) *
            (((qv v) ^ ((-(m + (n : ℤ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s
        else 0 := by
    dsimp [g, p]
    simpa [t] using finiteBoundary_charMellin_integral_log v A μ d hd a ha b hb
      (m + (n : ℤ)) s
  have hzero_head (n : ℕ) (hn : n < N) (hne : n ≠ N - 1) : g n = 0 := by
    have hjlt : m + (n : ℤ) < t := by rw [← hindex]; omega
    have hneq : t ≠ m + (n : ℤ) + 1 := by omega
    rw [hterm n]
    simp [not_le_of_gt hjlt, hneq]
  have hpred : m + ((N - 1 : ℕ) : ℤ) = t - 1 := by omega
  have hexception :
      g (N - 1) = -(((qv v)⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-(t - 1 : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s := by
    rw [hterm]
    have hfirst : ¬ t ≤ m + ((N - 1 : ℕ) : ℤ) := by omega
    have hsecond : t = m + ((N - 1 : ℕ) : ℤ) + 1 := by omega
    rw [if_neg hfirst, if_pos hsecond, hpred]
  have hhead : (∑ n ∈ Finset.range N, g n) = g (N - 1) := by
    apply Finset.sum_eq_single (N - 1)
    · intro n hn hne
      exact hzero_head n (Finset.mem_range.mp hn) hne
    · intro hnot
      apply False.elim
      apply hnot
      exact Finset.mem_range.mpr (by omega)
  have hjtail (n : ℕ) : m + ((n + N : ℕ) : ℤ) = t + (n : ℤ) := by
    rw [← hindex]
    push_cast
    omega
  have htailterm (n : ℕ) :
      g (n + N) = (((1 - (qv v)⁻¹ : ℝ) : ℂ) *
        (((qv v) ^ ((-(t + (n : ℤ) : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s) := by
    have hnormal : t ≤ m + ((n + N : ℕ) : ℤ) := by rw [hjtail]; omega
    rw [hterm, if_pos hnormal]
    rw [hjtail]
  have htail :
      (∑' n : ℕ, g (n + N)) =
        ∫ y in Theta.ball v t, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ := by
    rw [finiteBall_mellin_integral_tsum v μ t s hs]
    exact tsum_congr htailterm
  have hInt := finiteBall_charPower_integrable v A μ m a s hs
  have hBallOn : IntegrableOn p B (Theta.mulHaarFin μ) := by
    apply hInt.integrableOn.congr_fun
    · intro y hy
      simp [p, B, Set.indicator, hy]
    · exact (thetaBall_open v m).measurableSet
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hp0 : p 0 = 0 := by
    simp [p, absFin_eq_norm, Complex.zero_cpow hsne]
  have hhas := finiteBall_integral_hasSum_shells v m (Theta.mulHaarFin μ) p hBallOn hp0
  have hgsummable : Summable g := by simpa [g, p] using hhas.summable
  calc
    ∫ y in Theta.ball v (-(d + k)), p y ∂Theta.mulHaarFin μ = ∑' n : ℕ, g n := by
      simpa [g, p, m] using finiteBall_charMellin_integral_tsum v A μ m a s hs
    _ = (∑ n ∈ Finset.range N, g n) + ∑' n : ℕ, g (n + N) :=
      (hgsummable.sum_add_tsum_nat_add N).symm
    _ = g (N - 1) +
        ∫ y in Theta.ball v t, (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ := by
      rw [hhead, htail]
    _ = _ := by rw [hexception]

private theorem finiteRadius_real_pred {q : ℝ} (hq : 0 < q) (t : ℤ) :
    q ^ ((-(t - 1 : ℤ) : ℤ) : ℝ) = q * q ^ ((-t : ℤ) : ℝ) := by
  have hexp : ((-(t - 1 : ℤ) : ℤ) : ℝ) = 1 + ((-t : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_add hq, Real.rpow_one]

private theorem finiteRadius_pred_cpow {q : ℝ} (hq : 0 < q) (t : ℤ) (s : ℂ) :
    (((q ^ ((-(t - 1 : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s) =
      ((q : ℝ) : ℂ) ^ s * (((q ^ ((-t : ℤ) : ℝ) : ℝ) : ℂ) ^ s) := by
  rw [finiteRadius_real_pred hq t, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hq.le
    (Real.rpow_nonneg hq.le _) s]

private theorem finiteInvRadius_cpow_reflect {q : ℝ} (hq : 0 < q) (s : ℂ) :
    (((q⁻¹ : ℝ) : ℂ) ^ (1 - s)) = ((q : ℝ) : ℂ) ^ (s - 1) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  calc
    (((q⁻¹ : ℝ) : ℂ) ^ (1 - s)) = ((q : ℂ)⁻¹) ^ (1 - s) := by rw [Complex.ofReal_inv]
    _ = (((q : ℂ) ^ (1 - s))⁻¹) := Complex.inv_cpow_ofReal_nonneg hq.le _
    _ = (q : ℂ) ^ (-(1 - s)) := (Complex.cpow_neg (q : ℂ) (1 - s)).symm
    _ = (q : ℂ) ^ (s - 1) := by rw [show -(1 - s) = s - 1 by ring]

/-- Exact outside-ball character Mellin evaluation in the `mulHaarFin` normalization. -/
private theorem finiteBall_charMellin_outside_exact {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (k : ℤ) (a : v.adicCompletion F) (ha : a ≠ 0) (hout : a ∉ Theta.ball v k)
    (b : ℤ) (hb : Valued.v a = WithZero.exp b) (s : ℂ) (hs : 0 < s.re) :
    ∫ y in Theta.ball v (-(d + k)), A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin μ =
      ((absFin v a : ℝ) : ℂ) ^ (-s) * finiteTateLocalFactor v d s := by
  let t : ℤ := b - (d : ℤ)
  let qC : ℂ := (qv v : ℂ)
  let uC : ℂ := ((qv v)⁻¹ : ℝ)
  let R : ℂ := (((qv v) ^ ((-t : ℤ) : ℝ) : ℝ) : ℂ) ^ s
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have hqC : qC ≠ 0 := by dsimp [qC]; exact Complex.ofReal_ne_zero.mpr hq.ne'
  have huC : uC = qC ^ (-1 : ℂ) := by
    dsimp [uC, qC]
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one]
  have huCne : uC ≠ 0 := by rw [huC]; exact (Complex.cpow_ne_zero_iff).2 (Or.inl hqC)
  have hshift : uC * qC ^ s = qC ^ (s - 1) := by
    rw [huC, ← Complex.cpow_add _ _ hqC]
    congr 1
    ring
  have hreflect : uC ^ (1 - s) = qC ^ (s - 1) := by
    dsimp [uC, qC]
    exact finiteInvRadius_cpow_reflect hq s
  have hprod : uC ^ (1 - s) * uC ^ s = uC := by
    rw [← Complex.cpow_add _ _ huCne]
    simp
  have hprodR : R * uC ^ (1 - s) * uC ^ s = R * uC := by
    calc
      R * uC ^ (1 - s) * uC ^ s = R * (uC ^ (1 - s) * uC ^ s) := by rw [mul_assoc]
      _ = R * uC := by rw [hprod]
  have hcoef : (((1 - (qv v)⁻¹ : ℝ) : ℂ) = 1 - uC) := by
    dsimp [uC]
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have huPos : 0 < (qv v)⁻¹ := inv_pos.mpr hq
  have huLt : (qv v)⁻¹ < 1 := (inv_lt_one₀ hq).2 (qv_gt_one v)
  have hDenNorm : ‖uC ^ s‖ < 1 := by
    dsimp [uC]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos s]
    exact Real.rpow_lt_one (inv_nonneg.mpr hq.le) huLt hs
  have hden : 1 - uC ^ s ≠ 0 := by
    intro h
    have hval : uC ^ s = 1 := (sub_eq_zero.mp h).symm
    rw [hval] at hDenNorm
    norm_num at hDenNorm
  have hdecomp := finiteBall_charMellin_outside_decompose v A μ d hd k a ha hout b hb s hs
  have hcenter := finiteBall_mellin_integral_closed v μ t s hs
  have hpred :
      (((qv v) ^ ((-(t - 1 : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) ^ s = qC ^ s * R := by
    dsimp [qC, R]
    exact finiteRadius_pred_cpow hq t s
  have hJ :
      ∫ y in Theta.ball v (-(d + k)), A.ψ v (-(a * y)) * (absFin v y : ℂ) ^ s
          ∂Theta.mulHaarFin μ =
        -uC * (qC ^ s * R) +
          (((1 - (qv v)⁻¹ : ℝ) : ℂ) * R * (1 - uC ^ s)⁻¹) := by
    rw [finiteBall_charMellin_outside_decompose v A μ d hd k a ha hout b hb s hs]
    rw [finiteBall_mellin_integral_closed v μ t s hs]
    rw [hpred]
  have hR : R = (((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s * ((absFin v a : ℝ) : ℂ) ^ (-s) := by
    dsimp [R, t]
    exact finiteRadius_log_ratio_cpow v d a ha b hb s
  have hRcomm : ((absFin v a : ℝ) : ℂ) ^ (-s) *
      (((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s = R := by rw [hR]; ring
  calc
    _ = -uC * (qC ^ s * R) +
          (((1 - (qv v)⁻¹ : ℝ) : ℂ) * R * (1 - uC ^ s)⁻¹) := hJ
    _ = ((absFin v a : ℝ) : ℂ) ^ (-s) * finiteTateLocalFactor v d s := by
      unfold finiteTateLocalFactor
      have hfirst : -uC * (qC ^ s * R) = -uC ^ (1 - s) * R := by
        calc
          -uC * (qC ^ s * R) = -(uC * qC ^ s) * R := by ring
          _ = -(qC ^ (s - 1)) * R := by rw [hshift]
          _ = -uC ^ (1 - s) * R := by rw [hreflect]
      calc
        _ = -uC ^ (1 - s) * R +
            (((1 - (qv v)⁻¹ : ℝ) : ℂ) * R * (1 - uC ^ s)⁻¹) := by rw [hfirst]
        _ = R * (1 - uC ^ (1 - s)) * (1 - uC ^ s)⁻¹ := by
          rw [hcoef]
          field_simp [hden]
          ring_nf
          rw [hprodR]
          ring
        _ = ((absFin v a : ℝ) : ℂ) ^ (-s) *
            ((((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s *
              (1 - uC ^ (1 - s)) * (1 - uC ^ s)⁻¹) := by
          rw [← hRcomm]
          ring

private theorem finiteDualRadius_eq_ratio {q : ℝ} (hq : 0 < q) (d : ℕ) (k : ℤ) :
    q ^ ((d + k : ℤ) : ℝ) = q ^ (d : ℝ) / q ^ ((-k : ℤ) : ℝ) := by
  have hexp : ((d + k : ℤ) : ℝ) = (d : ℝ) - ((-k : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_sub hq]

private theorem finiteCenteredRadius_factor {q : ℝ} (hq : 0 < q)
    (d : ℕ) (k : ℤ) (s : ℂ) :
    ((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) *
        (((q ^ ((d + k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) =
      (((q ^ (d : ℝ) : ℝ) : ℂ) ^ s) *
        (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ (1 - s)) := by
  let r : ℝ := q ^ ((-k : ℤ) : ℝ)
  let Q : ℝ := q ^ (d : ℝ)
  have hr : 0 < r := Real.rpow_pos_of_pos hq _
  have hQ : 0 < Q := Real.rpow_pos_of_pos hq _
  have hrCne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hdual : q ^ ((d + k : ℤ) : ℝ) = Q / r := by
    dsimp [Q, r]
    exact finiteDualRadius_eq_ratio hq d k
  have hpow : (r : ℂ) * (r : ℂ) ^ (-s) = (r : ℂ) ^ (1 - s) := by
    calc
      (r : ℂ) * (r : ℂ) ^ (-s) = (r : ℂ) ^ (1 : ℂ) * (r : ℂ) ^ (-s) := by simp
      _ = (r : ℂ) ^ ((1 : ℂ) + (-s)) := (Complex.cpow_add _ _ hrCne).symm
      _ = (r : ℂ) ^ (1 - s) := by congr 1 <;> ring
  calc
    ((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) *
        (((q ^ ((d + k : ℤ) : ℝ) : ℝ) : ℂ) ^ s)
        =
        (r : ℂ) * ((((Q / r : ℝ) : ℂ) ^ s)) := by rw [hdual]
    _ = (r : ℂ) * (((Q : ℝ) : ℂ) ^ s / (r : ℂ) ^ s) := by
      rw [Complex.ofReal_div,
        Complex.div_cpow_ofReal_nonneg hQ.le hr.le s]
    _ = ((Q : ℝ) : ℂ) ^ s * ((r : ℂ) * ((r : ℂ) ^ s)⁻¹) := by ring
    _ = ((Q : ℝ) : ℂ) ^ s * ((r : ℂ) * (r : ℂ) ^ (-s)) := by
      rw [← Complex.cpow_neg]
    _ = ((Q : ℝ) : ℂ) ^ s * (r : ℂ) ^ (1 - s) := by rw [hpow]
    _ = (((q ^ (d : ℝ) : ℝ) : ℂ) ^ s) *
        (((q ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) ^ (1 - s)) := by rfl

private theorem finiteBall_centered_mellin_FE {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (d : ℕ) (k : ℤ) (s : ℂ)
    (hs : 0 < s.re) (h1s : 0 < (1 - s).re) :
    (μ.μ.real (Theta.ball v k) : ℂ) *
        (∫ y in Theta.ball v (-(d + k)), (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ) =
      finiteTateLocalFactor v d s *
        ∫ y in Theta.ball v k, (absFin v y : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ := by
  let q : ℝ := qv v
  let u : ℂ := ((qv v)⁻¹ : ℝ)
  let rC : ℂ := (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ)
  let Qs : ℂ := (((qv v) ^ (d : ℝ) : ℝ) : ℂ) ^ s
  have hq : 0 < qv v := by linarith [qv_gt_one v]
  have huPos : 0 < (qv v)⁻¹ := inv_pos.mpr hq
  have huLt : (qv v)⁻¹ < 1 := (inv_lt_one₀ hq).2 (qv_gt_one v)
  have hdenS : 1 - u ^ s ≠ 0 := by
    have hn : ‖u ^ s‖ < 1 := by
      dsimp [u]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos s]
      exact Real.rpow_lt_one (inv_nonneg.mpr hq.le) huLt hs
    intro h
    have hv : u ^ s = 1 := (sub_eq_zero.mp h).symm
    rw [hv] at hn
    norm_num at hn
  have hden1s : 1 - u ^ (1 - s) ≠ 0 := by
    have hn : ‖u ^ (1 - s)‖ < 1 := by
      dsimp [u]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos (1 - s)]
      exact Real.rpow_lt_one (inv_nonneg.mpr hq.le) huLt h1s
    intro h
    have hv : u ^ (1 - s) = 1 := (sub_eq_zero.mp h).symm
    rw [hv] at hn
    norm_num at hn
  have hmeasure : (μ.μ.real (Theta.ball v k) : ℂ) = rC := by
    dsimp [rC]
    exact congrArg (fun r : ℝ => (r : ℂ)) (finiteBall_measure v μ k)
  have hratio := finiteCenteredRadius_factor hq d k s
  have hratioC : rC * (((qv v) ^ ((d + k : ℤ) : ℝ) : ℝ) : ℂ) ^ s =
      Qs * rC ^ (1 - s) := by
    dsimp [rC, Qs]
    exact hratio
  have hcenterS := finiteBall_mellin_integral_closed v μ (-(d + k)) s hs
  have hcenter1S := finiteBall_mellin_integral_closed v μ k (1 - s) h1s
  calc
    _ = rC * ((((1 - (qv v)⁻¹ : ℝ) : ℂ) *
          (((qv v) ^ ((d + k : ℤ) : ℝ) : ℝ) : ℂ) ^ s *
            (1 - u ^ s)⁻¹)) := by
        rw [hmeasure, hcenterS]
        simp [u]
    _ = (((1 - (qv v)⁻¹ : ℝ) : ℂ) * (rC *
          (((qv v) ^ ((d + k : ℤ) : ℝ) : ℝ) : ℂ) ^ s) *
          (1 - u ^ s)⁻¹) := by ring
    _ = (((1 - (qv v)⁻¹ : ℝ) : ℂ) * Qs * rC ^ (1 - s) *
          (1 - u ^ s)⁻¹) := by rw [hratioC]; ring
    _ = finiteTateLocalFactor v d s *
          ((((1 - (qv v)⁻¹ : ℝ) : ℂ) * rC ^ (1 - s) *
            (1 - u ^ (1 - s))⁻¹)) := by
        have hcancel := mul_inv_cancel₀ hden1s
        calc
          _ = (((1 - (qv v)⁻¹ : ℝ) : ℂ) * Qs * rC ^ (1 - s) *
                (1 - u ^ s)⁻¹) * ((1 - u ^ (1 - s)) *
                  (1 - u ^ (1 - s))⁻¹) := by rw [hcancel]; ring
          _ = finiteTateLocalFactor v d s *
                ((((1 - (qv v)⁻¹ : ℝ) : ℂ) * rC ^ (1 - s) *
                  (1 - u ^ (1 - s))⁻¹)) := by
              unfold finiteTateLocalFactor
              dsimp [Qs, u]
              ring
    _ = finiteTateLocalFactor v d s *
          ∫ y in Theta.ball v k, (absFin v y : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ := by
        rw [hcenter1S]

private theorem finiteCoset_weighted_integral_outside {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (μ : Theta.LocHaar v) (k : ℤ)
    (a : v.adicCompletion F) (ha : a ≠ 0) (hout : a ∉ Theta.ball v k)
    (b : ℤ) (hb : Valued.v a = WithZero.exp b) (s : ℂ) :
    ∫ x, (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a) *
        (absFin v x : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ =
      (μ.μ.real (Theta.ball v k) : ℂ) * ((absFin v a : ℝ) : ℂ) ^ (-s) := by
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let C : Set K := {x | x - a ∈ B}
  let pow : K → ℂ := fun x => (absFin v x : ℂ) ^ (1 - s)
  have hBmeas : MeasurableSet B := (thetaBall_open v k).measurableSet
  have hCmeas : MeasurableSet C := by
    apply hBmeas.preimage
    fun_prop
  have hbgt : -k < b := by
    have hnot : ¬ Valued.v a ≤ WithZero.exp (-k) := by exact hout
    rw [hb] at hnot
    have hnot' : ¬ b ≤ -k := by
      intro hle
      exact hnot ((WithZero.exp_le_exp).2 hle)
    omega
  have hAbs : ∀ x ∈ C, absFin v x = absFin v a := by
    intro x hx
    have hxt : Valued.v (x - a) ≤ WithZero.exp (-k) := by
      change Valued.v (x - a) ≤ WithZero.exp (-k)
      exact hx
    have hta : Valued.v (x - a) < Valued.v a := by
      rw [hb]
      exact lt_of_le_of_lt hxt ((WithZero.exp_lt_exp).2 (by omega))
    have hsum : a + (x - a) = x := by abel
    have hval : Valued.v x = Valued.v a := by
      rw [← hsum]
      exact Valued.v.map_add_eq_of_lt_left hta
    rw [Theta.absFin_eq_norm, Theta.absFin_eq_norm,
      NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, hval]
  have hμC : μ.μ C = μ.μ B := by
    have hMP : MeasurePreserving (fun x : K => x - a) μ.μ μ.μ := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right μ.μ (-a)
    exact hMP.measure_preimage hBmeas.nullMeasurableSet
  have habspos : 0 < absFin v a := absFin_pos ha
  have hdens :
      (fun x : K => ENNReal.ofReal (absFin v x)⁻¹) =ᵐ[μ.μ.restrict C]
        fun _ => ENNReal.ofReal (absFin v a)⁻¹ := by
    filter_upwards [ae_restrict_mem hCmeas] with x hx
    rw [hAbs x hx]
  have hrestrict :
      (Theta.mulHaarFin μ).restrict C =
        ENNReal.ofReal (absFin v a)⁻¹ • μ.μ.restrict C := by
    calc
      (Theta.mulHaarFin μ).restrict C =
          (μ.μ.restrict C).withDensity (fun x => ENNReal.ofReal (absFin v x)⁻¹) :=
            restrict_withDensity hCmeas _
      _ = (μ.μ.restrict C).withDensity (fun _ => ENNReal.ofReal (absFin v a)⁻¹) :=
            withDensity_congr_ae hdens
      _ = ENNReal.ofReal (absFin v a)⁻¹ • μ.μ.restrict C := withDensity_const _
  have hmassENN :
      (Theta.mulHaarFin μ) C =
        ENNReal.ofReal ((absFin v a)⁻¹ * (qv v) ^ ((-k : ℤ) : ℝ)) := by
    calc
      (Theta.mulHaarFin μ) C = (Theta.mulHaarFin μ).restrict C Set.univ := by simp
      _ = ENNReal.ofReal (absFin v a)⁻¹ * μ.μ C := by rw [hrestrict]; simp
      _ = ENNReal.ofReal (absFin v a)⁻¹ * ENNReal.ofReal ((qv v) ^ ((-k : ℤ) : ℝ)) := by
        rw [hμC, finiteBall_measure_ennreal]
      _ = ENNReal.ofReal ((absFin v a)⁻¹) *
            ENNReal.ofReal ((qv v) ^ ((-k : ℤ) : ℝ)) := by
              rw [ENNReal.ofReal_inv_of_pos habspos]
      _ = ENNReal.ofReal ((absFin v a)⁻¹ * (qv v) ^ ((-k : ℤ) : ℝ)) := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.mpr habspos.le)]
  have hmassReal : (Theta.mulHaarFin μ).real C =
      (absFin v a)⁻¹ * (qv v) ^ ((-k : ℤ) : ℝ) := by
    rw [Measure.real_def, hmassENN]
    exact ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr habspos.le)
      (Real.rpow_nonneg (by linarith [qv_gt_one v]) _))
  have hfun :
      (fun x : K => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a) * pow x) =
        C.indicator pow := by
    funext x
    by_cases hx : x - a ∈ B
    · have hxC : x ∈ C := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxC]
      simp
    · have hxC : x ∉ C := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxC]
      simp
  have habsCne : ((absFin v a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr habspos.ne'
  have hAbsPow :
      ((absFin v a : ℝ) : ℂ)⁻¹ * ((absFin v a : ℝ) : ℂ) ^ (1 - s) =
        ((absFin v a : ℝ) : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ habsCne]
    congr 1
    ring
  calc
    ∫ x, (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a) *
        (absFin v x : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ =
          ∫ x, C.indicator pow x ∂Theta.mulHaarFin μ := by rw [hfun]
    _ = ∫ x in C, pow x ∂Theta.mulHaarFin μ :=
          MeasureTheory.integral_indicator hCmeas
    _ = ∫ x in C, ((absFin v a : ℝ) : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hCmeas] with x hx
          simp only [pow, hAbs x hx]
    _ = ((Theta.mulHaarFin μ).real C : ℂ) *
          ((absFin v a : ℝ) : ℂ) ^ (1 - s) := by simp [integral_const]
    _ = ((μ.μ.real (Theta.ball v k) : ℂ) * ((absFin v a : ℝ) : ℂ) ^ (-s)) := by
          rw [hmassReal, finiteBall_measure v μ k, Complex.ofReal_mul,
            Complex.ofReal_inv]
          calc
            _ = (((qv v) ^ ((-k : ℤ) : ℝ) : ℝ) : ℂ) *
                (((absFin v a : ℝ) : ℂ)⁻¹ * ((absFin v a : ℝ) : ℂ) ^ (1 - s)) := by ring
            _ = _ := by rw [hAbsPow]

private theorem finiteBallIndicator_localFE {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) (d : ℕ)
    (hd : ∀ k : ℤ, ∀ y : v.adicCompletion F,
      (∀ x ∈ Theta.ball v k, A.ψ v (-(x * y)) = 1) ↔
        y ∈ Theta.ball v (-(d + k)))
    (k : ℤ) (a : v.adicCompletion F) (s : ℂ)
    (hs : 0 < s.re) (h1s : 0 < (1 - s).re) :
    ∫ y, finiteFourier v A μ
        (fun x => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a)) y *
        (absFin v y : ℂ) ^ s ∂Theta.mulHaarFin μ =
      finiteTateLocalFactor v d s *
        ∫ x, (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - a) *
          (absFin v x : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ := by
  let B : Set (v.adicCompletion F) := Theta.ball v k
  let Bdual : Set (v.adicCompletion F) := Theta.ball v (-(d + k))
  let f : v.adicCompletion F → ℂ := fun x => B.indicator (fun _ => (1 : ℂ)) (x - a)
  let powS : v.adicCompletion F → ℂ := fun y => (absFin v y : ℂ) ^ s
  let pow1 : v.adicCompletion F → ℂ := fun x => (absFin v x : ℂ) ^ (1 - s)
  have hBmeas : MeasurableSet B := (thetaBall_open v k).measurableSet
  have hBdualMeas : MeasurableSet Bdual := (thetaBall_open v (-(d + k))).measurableSet
  have hballFourier (y : v.adicCompletion F) :
      finiteFourier v A μ (B.indicator (fun _ => (1 : ℂ))) y =
        if y ∈ Bdual then (μ.μ.real B : ℂ) else 0 := by
    rw [finiteFourier_ball_indicator]
    by_cases hy : y ∈ Bdual
    · have htriv := (hd k y).2 (by simpa [Bdual] using hy)
      rw [dif_pos htriv, if_pos hy]
    · have hnon : ¬ ∀ x ∈ B, A.ψ v (-(x * y)) = 1 := by
        intro hall
        exact hy ((hd k y).1 (by simpa [B] using hall))
      rw [dif_neg hnon, if_neg hy]
  have hFT (y : v.adicCompletion F) :
      finiteFourier v A μ f y =
        Bdual.indicator (fun y => (μ.μ.real B : ℂ) * A.ψ v (-(a * y))) y := by
    rw [finiteFourier_translated_ball_indicator, hballFourier]
    by_cases hy : y ∈ Bdual
    · rw [if_pos hy, Set.indicator_of_mem hy]
      ring
    · rw [if_neg hy, Set.indicator_of_notMem hy]
      simp
  have hLHS :
      ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
        (μ.μ.real B : ℂ) *
          ∫ y in Bdual, A.ψ v (-(a * y)) * powS y ∂Theta.mulHaarFin μ := by
    have hfun : (fun y => finiteFourier v A μ f y * powS y) =
        Bdual.indicator (fun y => (μ.μ.real B : ℂ) *
          (A.ψ v (-(a * y)) * powS y)) := by
      funext y
      rw [hFT]
      by_cases hy : y ∈ Bdual
      · simp [Set.indicator, hy]
        ring
      · simp [Set.indicator, hy]
    calc
      _ = ∫ y, Bdual.indicator (fun y => (μ.μ.real B : ℂ) *
          (A.ψ v (-(a * y)) * powS y)) y ∂Theta.mulHaarFin μ := by rw [hfun]
      _ = ∫ y in Bdual, (μ.μ.real B : ℂ) *
          (A.ψ v (-(a * y)) * powS y) ∂Theta.mulHaarFin μ :=
            MeasureTheory.integral_indicator hBdualMeas
      _ = (μ.μ.real B : ℂ) *
          ∫ y in Bdual, A.ψ v (-(a * y)) * powS y ∂Theta.mulHaarFin μ :=
            integral_const_mul _ _
  by_cases ha : a ∈ B
  · have hcoset (x : v.adicCompletion F) : x - a ∈ B ↔ x ∈ B := by
      constructor
      · intro hx
        have hsum := thetaBall_add v k hx ha
        convert hsum using 1 <;> abel
      · intro hx
        have hna := thetaBall_neg v k ha
        have hsum := thetaBall_add v k hx hna
        convert hsum using 1 <;> abel
    have hfEq : f = B.indicator (fun _ => (1 : ℂ)) := by
      funext x
      simp [f, B, Set.indicator, hcoset x]
    have hfun1 : (fun x => f x * pow1 x) = B.indicator pow1 := by
      funext x
      change B.indicator (fun _ => (1 : ℂ)) (x - a) * pow1 x = B.indicator pow1 x
      by_cases hx : x ∈ B
      · have hxa : x - a ∈ B := (hcoset x).2 hx
        rw [Set.indicator_of_mem hxa, Set.indicator_of_mem hx]
        simp
      · have hxa : x - a ∉ B := by
          intro hmem
          exact hx ((hcoset x).1 hmem)
        rw [Set.indicator_of_notMem hxa, Set.indicator_of_notMem hx]
        simp
    have hRHSinside :
        ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ =
          ∫ x in B, pow1 x ∂Theta.mulHaarFin μ := by
      rw [hfun1, MeasureTheory.integral_indicator hBmeas]
    have hψ : ∀ y ∈ Bdual, A.ψ v (-(a * y)) = 1 := by
      intro y hy
      exact (hd k y).2 (by simpa [B, Bdual] using hy) a ha
    have hinside :
        ∫ y in Bdual, A.ψ v (-(a * y)) * powS y ∂Theta.mulHaarFin μ =
          ∫ y in Bdual, powS y ∂Theta.mulHaarFin μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hBdualMeas] with y hy
      rw [hψ y hy]
      simp
    calc
      ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
          (μ.μ.real B : ℂ) *
            ∫ y in Bdual, powS y ∂Theta.mulHaarFin μ := by rw [hLHS, hinside]
      _ = finiteTateLocalFactor v d s * ∫ x in B, pow1 x ∂Theta.mulHaarFin μ := by
        simpa [B, Bdual, powS, pow1] using
          (finiteBall_centered_mellin_FE v μ d k s hs h1s)
      _ = finiteTateLocalFactor v d s * ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ := by
        rw [← hRHSinside]
  · have ha0 : a ≠ 0 := by
      intro hz
      subst a
      apply ha
      change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-k)
      simp
    have hvne : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    let b : ℤ := WithZero.log (Valued.v a)
    have hb : Valued.v a = WithZero.exp b := by
      dsimp [b]
      exact (WithZero.exp_log hvne).symm
    have houtside := finiteBall_charMellin_outside_exact v A μ d hd k a ha0 ha b hb s hs
    have hcoset := finiteCoset_weighted_integral_outside v μ k a ha0 ha b hb s
    have hcoset' :
        ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ =
          (μ.μ.real B : ℂ) * ((absFin v a : ℝ) : ℂ) ^ (-s) := by
      simpa [f, B, pow1] using hcoset
    calc
      ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
          (μ.μ.real B : ℂ) *
            ∫ y in Bdual, A.ψ v (-(a * y)) * powS y ∂Theta.mulHaarFin μ := hLHS
      _ = finiteTateLocalFactor v d s *
            ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ := by rw [houtside, hcoset']; ring

private theorem thetaBall_coset_membership {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (k : ℤ) (x t z : v.adicCompletion F)
    (hxt : x - t ∈ Theta.ball v k) :
    z - t ∈ Theta.ball v k ↔ x - z ∈ Theta.ball v k := by
  constructor
  · intro hzt
    have htz : t - z ∈ Theta.ball v k := by
      have hneg := thetaBall_neg v k hzt
      convert hneg using 1 <;> abel
    have heq : x - z = (x - t) + (t - z) := by abel
    rw [heq]
    exact thetaBall_add v k hxt htz
  · intro hzx
    have hzx' : z - x ∈ Theta.ball v k := by
      have hneg := thetaBall_neg v k hzx
      convert hneg using 1 <;> abel
    have heq : z - t = (z - x) + (x - t) := by abel
    rw [heq]
    exact thetaBall_add v k hzx' hxt

set_option maxHeartbeats 3000000 in
private theorem finiteTest_ballExpansion {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ k : ℤ, ∃ T : Finset (v.adicCompletion F), ∃ c : v.adicCompletion F → ℂ,
      ∀ x, f x = ∑ t ∈ T,
        c t * (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - t) := by
  classical
  obtain ⟨k, hperiod⟩ := finiteTest_exists_period_ball v f hf hfc
  let K := v.adicCompletion F
  let B : Set K := Theta.ball v k
  let S : Set K := tsupport f
  let N : K → Set K := fun t => {x | x - t ∈ B}
  have hScompact : IsCompact S := hfc
  have hopen : ∀ t : K, IsOpen (N t) := by
    intro t
    apply (thetaBall_open v k).preimage
    fun_prop
  have hcover : S ⊆ ⋃ t : K, N t := by
    intro x hx
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    change x - x ∈ Theta.ball v k
    rw [sub_self]
    change Valued.v (0 : K) ≤ WithZero.exp (-k)
    simp
  obtain ⟨T, hT⟩ := hScompact.elim_finite_subcover N hopen hcover
  let U : K → Finset K := fun x => T.filter (fun t => x - t ∈ B)
  let count : K → ℕ := fun t => (T.filter (fun z => z - t ∈ B)).card
  let c : K → ℂ := fun t => f t / (count t : ℂ)
  let ind : K → K → ℂ := fun t x => B.indicator (fun _ => (1 : ℂ)) (x - t)
  have hcount (x t : K) (ht : t ∈ U x) :
      T.filter (fun z => z - t ∈ B) = U x := by
    have hxt : x - t ∈ B := (Finset.mem_filter.mp ht).2
    dsimp [U]
    apply Finset.filter_congr (s := T)
    intro z hzT
    exact thetaBall_coset_membership v k x t z hxt
  have hcoeff (x t : K) (ht : t ∈ U x) : c t = f x / (U x).card := by
    have hxt : x - t ∈ B := (Finset.mem_filter.mp ht).2
    have htx : t - x ∈ B := by
      have hneg := thetaBall_neg v k hxt
      convert hneg using 1 <;> abel
    have hperiod' := hperiod x (t - x) htx
    have hsum : x + (t - x) = t := by abel
    have hft : f t = f x := by
      calc
        f t = f (x + (t - x)) := by rw [hsum]
        _ = f x := hperiod'
    have hcnt := hcount x t ht
    calc
      c t = f t / (count t : ℂ) := rfl
      _ = f x / (U x).card := by
        rw [hft, show count t = (U x).card by exact congrArg Finset.card hcnt]
  have htermSum (x : K) :
      (∑ t ∈ T, c t * ind t x) = ∑ t ∈ U x, c t := by
    calc
      (∑ t ∈ T, c t * ind t x) =
          ∑ t ∈ T, if x - t ∈ B then c t else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            by_cases hxt : x - t ∈ B <;> simp [ind, B, Set.indicator, hxt]
      _ = ∑ t ∈ U x, c t := by
            dsimp [U]
            rw [Finset.sum_filter]
  have hsum (x : K) : f x = ∑ t ∈ T, c t * ind t x := by
    by_cases hUnonempty : (U x).Nonempty
    · have hcard : (U x).card ≠ 0 := Finset.card_ne_zero.mpr hUnonempty
      calc
        f x = ∑ t ∈ U x, f x / (U x).card := by
          symm
          calc
            (∑ t ∈ U x, f x / (U x).card) =
                (U x).card * (f x / (U x).card) := by simp
            _ = f x := by field_simp [Nat.cast_ne_zero.mpr hcard]
        _ = ∑ t ∈ U x, c t := by
          apply Finset.sum_congr rfl
          intro t ht
          exact (hcoeff x t ht).symm
        _ = ∑ t ∈ T, c t * ind t x := (htermSum x).symm
    · have hfx0 : f x = 0 := by
        by_contra hne
        have hxS : x ∈ S := subset_closure (Function.mem_support.mpr hne)
        rcases Set.mem_iUnion₂.mp (hT hxS) with ⟨t, htT, hxt⟩
        have htU : t ∈ U x := Finset.mem_filter.mpr ⟨htT, hxt⟩
        exact hUnonempty ⟨t, htU⟩
      have hUempty : U x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUnonempty
      rw [hfx0, htermSum, hUempty]
      simp
  refine ⟨k, T, c, ?_⟩
  intro x
  simpa [ind, B] using hsum x

set_option maxHeartbeats 3000000 in
theorem finiteLocalFunctionalEquation_all {F : Type} [Field F] [NumberField F]
    (v : FinPlace F) (A : AddCharData F) (μ : Theta.LocHaar v) :
    ∃ c : ℂ → ℂ, c (1 / 6) ≠ 0 ∧
      ∀ f : v.adicCompletion F → ℂ, Continuous f → HasCompactSupport f →
        IsLocallyConstant f → ∀ s : ℂ, 0 < s.re → s.re < 1 →
          ∫ y, finiteFourier v A μ f y * (absFin v y : ℂ) ^ s
              ∂Theta.mulHaarFin μ =
            c s *
              ∫ x, f x * (absFin v x : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ := by
  classical
  obtain ⟨d, hd⟩ := finitePsi_ball_annihilator_all v A
  let c : ℂ → ℂ := fun s => finiteTateLocalFactor v d s
  refine ⟨c, ?_, ?_⟩
  · exact finiteTateLocalFactor_ne_zero v d
  intro f hf hfc hflc s hs h1s
  change ∫ y, finiteFourier v A μ f y * (absFin v y : ℂ) ^ s
      ∂Theta.mulHaarFin μ =
    finiteTateLocalFactor v d s *
      ∫ x, f x * (absFin v x : ℂ) ^ (1 - s) ∂Theta.mulHaarFin μ
  have h1sPos : 0 < (1 - s).re := by
    rw [Complex.sub_re]
    simp only [Complex.one_re]
    linarith
  let K := v.adicCompletion F
  let powS : K → ℂ := fun y => (absFin v y : ℂ) ^ s
  let pow1 : K → ℂ := fun y => (absFin v y : ℂ) ^ (1 - s)
  obtain ⟨k, T, c, hExpansion⟩ := finiteTest_ballExpansion v f hflc hfc
  let g : K → K → ℂ := fun t x => (Theta.ball v k).indicator (fun _ => (1 : ℂ)) (x - t)
  have hExp (x : K) : f x = ∑ t ∈ T, c t * g t x := by
    simpa [g] using hExpansion x
  have hreg (t : K) : IsLocallyConstant (g t) ∧ HasCompactSupport (g t) := by
    simpa [g] using finiteBallTranslate_indicator_regular v k t
  let per (t : K) : ℤ := Classical.choose
    (finiteTest_exists_period_ball v (g t) (hreg t).1 (hreg t).2)
  have hper (t : K) : ∀ x u, u ∈ Theta.ball v (per t) → g t (x + u) = g t x :=
    Classical.choose_spec (finiteTest_exists_period_ball v (g t) (hreg t).1 (hreg t).2)
  have hFTcompact (t : K) : HasCompactSupport (finiteFourier v A μ (g t)) :=
    finiteFourier_hasCompactSupport_of_period v A μ (g t) (per t) (hper t)
  have hFTcont (t : K) : Continuous (finiteFourier v A μ (g t)) :=
    (finiteFourier_isLocallyConstant v A μ (g t) (hreg t).2).continuous
  have hfperiod : ∃ n : ℤ, ∀ x u, u ∈ Theta.ball v n → f (x + u) = f x :=
    let ⟨n, hn⟩ := finiteTest_exists_period_ball v f hflc hfc
    ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hfperiod
  have hFTfcompact : HasCompactSupport (finiteFourier v A μ f) :=
    finiteFourier_hasCompactSupport_of_period v A μ f n hn
  have hFTfcont : Continuous (finiteFourier v A μ f) :=
    (finiteFourier_isLocallyConstant v A μ f hfc).continuous
  have hCharKernel (g₀ : K → ℂ) (hg₀ : Continuous g₀) (hcg₀ : HasCompactSupport g₀)
      (y : K) : Integrable (fun x => g₀ x * A.ψ v (-(x * y))) μ.μ :=
    finiteAddChar_integrable_of_continuous_compact v A μ g₀ hg₀ hcg₀ y
  have hKernelTerm (t : K) (y : K) :
      Integrable (fun x => c t * g t x * A.ψ v (-(x * y))) μ.μ := by
    have h := hCharKernel (g t) (hreg t).1.continuous (hreg t).2 y
    simpa [mul_assoc] using h.const_mul (c t)
  have hKernelPoint (x y : K) :
      f x * A.ψ v (-(x * y)) =
        ∑ t ∈ T, c t * g t x * A.ψ v (-(x * y)) := by
    calc
      f x * A.ψ v (-(x * y)) = (∑ t ∈ T, c t * g t x) * A.ψ v (-(x * y)) := by rw [hExp]
      _ = ∑ t ∈ T, c t * g t x * A.ψ v (-(x * y)) := by
        rw [Finset.sum_mul]
  have hFourier (y : K) :
      finiteFourier v A μ f y = ∑ t ∈ T, c t * finiteFourier v A μ (g t) y := by
    unfold finiteFourier
    calc
      ∫ x, f x * A.ψ v (-(x * y)) ∂μ.μ =
          ∫ x, ∑ t ∈ T, c t * g t x * A.ψ v (-(x * y)) ∂μ.μ := by
            apply integral_congr_ae
            filter_upwards with x
            exact hKernelPoint x y
      _ = ∑ t ∈ T,
          ∫ x, c t * g t x * A.ψ v (-(x * y)) ∂μ.μ := by
            rw [MeasureTheory.integral_finsetSum]
            intro t ht
            exact hKernelTerm t y
      _ = ∑ t ∈ T, c t * finiteFourier v A μ (g t) y := by
            apply Finset.sum_congr rfl
            intro t ht
            simp only [finiteFourier]
            calc
              ∫ x, c t * g t x * A.ψ v (-(x * y)) ∂μ.μ =
                  ∫ x, c t * (g t x * A.ψ v (-(x * y))) ∂μ.μ := by
                    apply integral_congr_ae
                    filter_upwards with x
                    ring
              _ = c t * ∫ x, g t x * A.ψ v (-(x * y)) ∂μ.μ := integral_const_mul _ _
  have hFTpow (t : K) :
      Integrable (fun y => finiteFourier v A μ (g t) y * powS y) (Theta.mulHaarFin μ) :=
    finiteComplexPower_integrable_of_continuous_compact v μ
      (finiteFourier v A μ (g t)) (hFTcont t) (hFTcompact t) s hs
  have hSourcePow (t : K) : Integrable (fun x => g t x * pow1 x) (Theta.mulHaarFin μ) :=
    finiteComplexPower_integrable_of_continuous_compact v μ (g t)
      (hreg t).1.continuous (hreg t).2 (1 - s) h1sPos
  have hLHSsum :
      ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
        ∑ t ∈ T, c t * ∫ y, finiteFourier v A μ (g t) y * powS y ∂Theta.mulHaarFin μ := by
    calc
      ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
          ∫ y, ∑ t ∈ T, c t * (finiteFourier v A μ (g t) y * powS y)
            ∂Theta.mulHaarFin μ := by
              apply integral_congr_ae
              filter_upwards with y
              rw [hFourier y, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro t ht
              ring
      _ = ∑ t ∈ T, ∫ y, c t *
          (finiteFourier v A μ (g t) y * powS y) ∂Theta.mulHaarFin μ := by
            rw [MeasureTheory.integral_finsetSum]
            intro t ht
            simpa [mul_assoc] using (hFTpow t).const_mul (c t)
      _ = ∑ t ∈ T, c t *
          ∫ y, finiteFourier v A μ (g t) y * powS y ∂Theta.mulHaarFin μ := by
            apply Finset.sum_congr rfl
            intro t ht
            exact integral_const_mul _ _
  have hRHSsum :
      ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ =
        ∑ t ∈ T, c t * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ := by
    calc
      ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ =
          ∫ x, ∑ t ∈ T, c t * (g t x * pow1 x) ∂Theta.mulHaarFin μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hExp x, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro t ht
            ring
      _ = ∑ t ∈ T, ∫ x, c t * (g t x * pow1 x) ∂Theta.mulHaarFin μ := by
            rw [MeasureTheory.integral_finsetSum]
            intro t ht
            simpa [mul_assoc] using (hSourcePow t).const_mul (c t)
      _ = ∑ t ∈ T, c t * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ := by
            apply Finset.sum_congr rfl
            intro t ht
            exact integral_const_mul _ _
  calc
    ∫ y, finiteFourier v A μ f y * powS y ∂Theta.mulHaarFin μ =
        ∑ t ∈ T, c t * ∫ y, finiteFourier v A μ (g t) y * powS y ∂Theta.mulHaarFin μ := hLHSsum
    _ = ∑ t ∈ T, c t *
        (finiteTateLocalFactor v d s * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact congrArg (fun z : ℂ => c t * z)
            (finiteBallIndicator_localFE v A μ d (fun k y => hd y k) k t s hs h1sPos)
    _ = finiteTateLocalFactor v d s *
        ∑ t ∈ T, c t * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ := by
          calc
            (∑ t ∈ T, c t *
                (finiteTateLocalFactor v d s *
                  ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ)) =
                ∑ t ∈ T, finiteTateLocalFactor v d s *
                  (c t * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    ring
            _ = finiteTateLocalFactor v d s *
                ∑ t ∈ T, c t * ∫ x, g t x * pow1 x ∂Theta.mulHaarFin μ := by
                  rw [← Finset.mul_sum]
    _ = finiteTateLocalFactor v d s * ∫ x, f x * pow1 x ∂Theta.mulHaarFin μ := by
          rw [hRHSsum]

end ArtinPrimitiveRoots.Proofs.a2_weights
end
