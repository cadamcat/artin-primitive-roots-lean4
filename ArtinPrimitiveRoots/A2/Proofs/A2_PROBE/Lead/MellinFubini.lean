import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

private theorem prF_qI_ext_pos (I : S.ExtIdeal) : 0 < qI I.1 := by
  unfold qI
  have h := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using I.2.1)⟩
  exact_mod_cast h

private theorem prF_qI_sqf_pos (c : S.SqfExtIdeal) : 0 < qI c.1 := by
  unfold qI
  have h := Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨c.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using c.2.1.1)⟩
  exact_mod_cast h

private theorem prF_real_summable_product {α β : Type*} (f : α → ℝ) (g : β → ℝ)
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) :
    Summable (fun p : α × β => f p.1 * g p.2) := by
  apply (summable_prod_of_nonneg (fun p : α × β => mul_nonneg (hf0 p.1) (hg0 p.2))).2
  constructor
  · intro x
    exact hg.mul_left (f x)
  · have hpoint : (fun x : α => ∑' y : β, f x * g y) =
        fun x => f x * ∑' y, g y := by
      funext x
      exact hg.tsum_mul_left (f x)
    rw [hpoint]
    exact hf.mul_right (∑' y, g y)

private def prF_frequencyShell (k : ℕ) : Set U.U :=
  {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧ U.q u < ((2 ^ (k + 1) : ℕ) : ℝ)}

private theorem prF_frequencyShell_partition : ∀ u : U.U,
    ∃! k : ℕ, u ∈ prF_frequencyShell η U k := by
  intro u
  have hq := U.q_ge_one u
  let n : ℕ := Nat.floor (U.q u)
  have hn : n ≠ 0 := by
    intro hn
    have hfloorLt : U.q u < (n + 1 : ℕ) := by
      exact_mod_cast (Nat.lt_floor_add_one (U.q u))
    rw [hn] at hfloorLt
    norm_num at hfloorLt
    linarith [hq]
  let k : ℕ := Nat.log 2 n
  have hloNat : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hn
  have hhiNat : n < 2 ^ (k + 1) := by
    simpa [k, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hlo : ((2 ^ k : ℕ) : ℝ) ≤ U.q u := by
    calc
      _ ≤ (n : ℝ) := by exact_mod_cast hloNat
      _ ≤ U.q u := Nat.floor_le (by linarith)
  have hfloorLt : U.q u < (n + 1 : ℕ) := by
    exact_mod_cast (Nat.lt_floor_add_one (U.q u))
  have hsuccNat : n + 1 ≤ 2 ^ (k + 1) := Nat.succ_le_iff.mpr hhiNat
  have hhi : U.q u < ((2 ^ (k + 1) : ℕ) : ℝ) := by
    exact hfloorLt.trans_le (by exact_mod_cast hsuccNat)
  refine ⟨k, ⟨hlo, hhi⟩, ?_⟩
  intro j hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hjk)
    have hpowR : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hpow
    linarith [hj.2, hlo]
  · have hpow : 2 ^ (k + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_iff.mpr hkj)
    have hpowR : ((2 ^ (k + 1) : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hpow
    linarith [hj.1, hhi]

private theorem prF_frequency_q_inv_sq_summable :
    Summable (fun u : U.U => U.q u ^ (-2 : ℝ)) := by
  classical
  obtain ⟨Cdyad, hCdyad, hdyad⟩ := U.dyadic_count
  obtain ⟨Clow, hClow, hlowFinite, hlowBound⟩ := U.low_shell_bound
  let C : ℝ := max Cdyad Clow
  have hC : 0 < C := lt_of_lt_of_le hCdyad (le_max_left _ _)
  have hShellFinite (k : ℕ) : (prF_frequencyShell η U k).Finite := by
    by_cases hk : k = 0
    · subst k
      apply hlowFinite.subset
      intro u hu
      exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast this
      obtain ⟨hfin, _⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      refine hfin.subset ?_
      intro u hu
      exact ⟨hu.1, hu.2.trans_eq (by
        rw [pow_succ]
        push_cast
        ring)⟩
  have hCount (k : ℕ) :
      (prF_frequencyShell η U k).ncard ≤ C * ((2 ^ k : ℕ) : ℝ) := by
    by_cases hk : k = 0
    · subst k
      have hsub : prF_frequencyShell η U 0 ⊆ {u | 1 ≤ U.q u ∧ U.q u < 4} := by
        intro u hu
        exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
      have hcard := Set.ncard_le_ncard hsub hlowFinite
      calc
        (prF_frequencyShell η U 0).ncard ≤
            ({u | 1 ≤ U.q u ∧ U.q u < 4}.ncard : ℝ) := by exact_mod_cast hcard
        _ ≤ Clow := hlowBound
        _ ≤ C := le_max_right _ _
        _ = C * ((2 ^ 0 : ℕ) : ℝ) := by simp [C]
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast this
      obtain ⟨hfin, hbound⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      have hsub : prF_frequencyShell η U k ⊆
          {u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧ U.q u < 2 * ((2 ^ k : ℕ) : ℝ)} := by
        intro u hu
        exact ⟨hu.1, hu.2.trans_eq (by
          rw [pow_succ]
          push_cast
          ring)⟩
      have hcard := Set.ncard_le_ncard hsub hfin
      calc
        (prF_frequencyShell η U k).ncard ≤
            ({u | ((2 ^ k : ℕ) : ℝ) ≤ U.q u ∧
              U.q u < 2 * ((2 ^ k : ℕ) : ℝ)}.ncard : ℝ) := by exact_mod_cast hcard
        _ ≤ Cdyad * ((2 ^ k : ℕ) : ℝ) := hbound
        _ ≤ C * ((2 ^ k : ℕ) : ℝ) := by
          dsimp [C]
          gcongr
          exact le_max_left _ _
  have hInner (k : ℕ) :
      Summable (fun u : prF_frequencyShell η U k => U.q u.1 ^ (-2 : ℝ)) := by
    letI := (hShellFinite k).fintype
    exact Summable.of_finite
  have hMass (k : ℕ) :
      (∑' u : prF_frequencyShell η U k, U.q u.1 ^ (-2 : ℝ)) ≤
        C * (1 / 2 : ℝ) ^ k := by
    let X : ℝ := ((2 ^ k : ℕ) : ℝ)
    have hX : 0 < X := by positivity
    have hterm (u : prF_frequencyShell η U k) : U.q u.1 ^ (-2 : ℝ) ≤ X ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hX (by simpa [X] using u.2.1) (by norm_num)
    letI := (hShellFinite k).fintype
    calc
      _ ≤ ∑' u : prF_frequencyShell η U k, X ^ (-2 : ℝ) :=
        (hInner k).tsum_le_tsum hterm (by
          letI := (hShellFinite k).fintype
          exact Summable.of_finite)
      _ = (Fintype.card (prF_frequencyShell η U k) : ℝ) * X ^ (-2 : ℝ) := by simp
      _ = ((prF_frequencyShell η U k).ncard : ℝ) * X ^ (-2 : ℝ) := by simp
      _ ≤ (C * X) * X ^ (-2 : ℝ) := by
        gcongr
        exact hCount k
      _ = C * (1 / 2 : ℝ) ^ k := by
        have hXcast : X = (2 : ℝ) ^ k := by
          dsimp [X]
          norm_cast
        rw [hXcast, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ k) 2,
          Real.rpow_two]
        simp only [one_div_pow, one_pow]
        field_simp
  have hOuter : Summable
      (fun k : ℕ => ∑' u : prF_frequencyShell η U k, U.q u.1 ^ (-2 : ℝ)) := by
    have hgeom : Summable (fun k : ℕ => C * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun u => ?_) hMass hgeom
    exact Real.rpow_nonneg (U.q_pos u.1).le _
  have hpart : ∀ u : U.U, ∃! k : ℕ, u ∈ prF_frequencyShell η U k :=
    prF_frequencyShell_partition η U
  have hf0 : ∀ u : U.U, 0 ≤ U.q u ^ (-2 : ℝ) :=
    fun u => Real.rpow_nonneg (U.q_pos u).le _
  exact (summable_partition hf0 hpart).2 ⟨hInner, hOuter⟩

private theorem prF_frequency_type_countable : Countable U.U := by
  classical
  obtain ⟨_, _, hdyad⟩ := U.dyadic_count
  obtain ⟨_, _, hlowFinite, _⟩ := U.low_shell_bound
  have hShellFinite (k : ℕ) : (prF_frequencyShell η U k).Finite := by
    by_cases hk : k = 0
    · subst k
      apply hlowFinite.subset
      intro u hu
      exact ⟨by simpa using hu.1, lt_trans hu.2 (by norm_num)⟩
    · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have hX : 2 ≤ ((2 ^ k : ℕ) : ℝ) := by
        have hn : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
        exact_mod_cast hn
      obtain ⟨hfin, _⟩ := hdyad ((2 ^ k : ℕ) : ℝ) hX
      apply hfin.subset
      intro u hu
      exact ⟨hu.1, hu.2.trans_eq (by
        rw [pow_succ]
        push_cast
        ring)⟩
  have hcover : (Set.univ : Set U.U) = ⋃ k : ℕ, prF_frequencyShell η U k := by
    ext u
    simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
    obtain ⟨k, hk, _⟩ := prF_frequencyShell_partition η U u
    exact ⟨k, hk⟩
  apply Set.countable_univ_iff.mp
  rw [hcover]
  exact Set.countable_iUnion (fun k => (hShellFinite k).countable)

private theorem prF_ideal_countable : Countable (Ideal (𝓞 F)) := by
  have hcover : (Set.univ : Set (Ideal (𝓞 F))) =
      ⋃ n : ℕ, {I | Ideal.absNorm I ≤ n} := by
    ext I
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
    exact ⟨Ideal.absNorm I, le_rfl⟩
  have hcount : (Set.univ : Set (Ideal (𝓞 F))).Countable := by
    rw [hcover]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOfPred_absNorm_le n).countable)
  exact Set.countable_univ_iff.mp hcount

private theorem prF_ext_ideal_rpow_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun I : S.ExtIdeal => qI I.1 ^ (-s)) := by
  simpa [qI, idealNorm] using a2_bridge_COUNT_summable S s hs

private theorem prF_sqf_ideal_rpow_summable
    (R0 : ReflectionSetup D S H Bd A ϑ bc μ v0) (s : ℝ) (hs : 1 < s) :
    Summable (fun c : S.SqfExtIdeal => qI c.1 ^ (-s)) := by
  have hExt := prF_ext_ideal_rpow_summable (S := S) s hs
  let e : S.SqfExtIdeal → S.ExtIdeal := R0.exterior.ofSqf
  have he : Function.Injective e := by
    intro c d h
    apply Subtype.ext
    have hval := congrArg Subtype.val h
    simpa [e, R0.exterior.ofSqf_val] using hval
  have h := hExt.comp_injective he
  change Summable (fun c : S.SqfExtIdeal => qI (e c).1 ^ (-s)) at h
  simpa [e, qI, R0.exterior.ofSqf_val] using h

private theorem prF_gaussian_shear_majorant_integrable (C : ℝ) :
    Integrable (fun t : ℝ × ℝ × ℝ => C * Real.exp (-(t.1 + t.2.2) ^ 2) *
      (1 + |t.2.2|) ^ (-2 : ℝ) * (1 + |t.2.1|) ^ (-2 : ℝ)) volume := by
  let tail : ℝ → ℝ := fun x => (1 + |x|) ^ (-2 : ℝ)
  let gauss : ℝ → ℝ := fun x => Real.exp (-x ^ 2)
  have htail : Integrable tail volume := by
    simpa [tail, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume)
        (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  have hgauss : Integrable gauss volume := by
    simpa [gauss] using
      (integrable_exp_neg_mul_sq (b := 1) (by norm_num : (0 : ℝ) < 1))
  let E := ℝ × ℝ × ℝ
  let μ : Measure E := volume
  let f : Module.Dual ℝ E :=
    (LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))
  let v : E := (1, (0, 0))
  have hfv : f v = 0 := by rfl
  let L : E ≃ₗ[ℝ] E := LinearEquiv.transvection hfv
  have hdetUnit : LinearEquiv.det L = 1 := by
    simp [L, LinearEquiv.transvection.det_eq_one]
  have hdet : LinearMap.det L.toLinearMap = 1 := by
    rw [← LinearEquiv.coe_det]
    exact congrArg (fun u : ℝˣ => (u : ℝ)) hdetUnit
  have hdet0 : LinearMap.det L.toLinearMap ≠ 0 := by rw [hdet]; norm_num
  letI : BorelSpace E := by infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure ℝ) := by infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    infer_instance
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, E]
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    infer_instance
  have hmap : Measure.map L.toLinearMap μ = μ := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := μ) (f := L.toLinearMap) hdet0]
    simp [hdet]
  have hL_apply (t : E) : L t = (t.1 + t.2.2, t.2) := by
    rw [LinearEquiv.transvection.apply hfv t]
    change t + t.2.2 • (1, (0, 0)) = (t.1 + t.2.2, t.2)
    apply Prod.ext
    · change t.1 + t.2.2 • (1 : ℝ) = _
      simp
    · apply Prod.ext
      · change t.2.1 + t.2.2 • (0 : ℝ) = _
        simp
      · change t.2.2 + t.2.2 • (0 : ℝ) = _
        simp
  have hLfun : (fun t : E => L t) = fun t => (t.1 + t.2.2, t.2) :=
    funext hL_apply
  have hLmeas : Measurable L.toLinearMap := by
    change Measurable (fun t : E => L t)
    rw [hLfun]
    fun_prop
  have hMP : MeasurePreserving L.toLinearMap μ μ := ⟨hLmeas, hmap⟩
  have hbaseProd : Integrable
      (fun t : E => gauss t.1 * (tail t.2.1 * tail t.2.2))
      (volume.prod (volume.prod volume)) := hgauss.mul_prod (htail.mul_prod htail)
  have hbase : Integrable
      (fun t : E => gauss t.1 * (tail t.2.1 * tail t.2.2)) μ := by
    dsimp [μ, E]
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
    exact hbaseProd
  have hshear : Integrable (fun t : E =>
      gauss (t.1 + t.2.2) * (tail t.2.1 * tail t.2.2)) μ := by
    have hcomp := hMP.integrable_comp_of_integrable hbase
    convert hcomp using 1
    ext t
    simp [Function.comp_apply, hL_apply, gauss, tail]
  simpa [gauss, tail, mul_assoc, mul_left_comm, mul_comm] using hshear.const_mul C

private theorem prF_tripleVertical_eq_integral_prod (f : ℂ → ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ × ℝ =>
      f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I))) :
    leadTripleVertical 4 4 2 f =
      (1 / (2 * Real.pi) : ℂ) ^ 3 * ∫ t : ℝ × ℝ × ℝ,
        f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) := by
  let κ : ℂ := 1 / (2 * Real.pi)
  let G (t : ℝ × (ℝ × ℝ)) : ℂ :=
    f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)
  have hp : Integrable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact hf
  have hPair : ∀ᵐ t : ℝ, leadVertical 4 (fun w => leadVertical 2
      (fun z => f (4 + t * Complex.I) w z)) = κ ^ 2 * ∫ v : ℝ × ℝ, G (t, v) := by
    filter_upwards [hp.prod_right_ae] with t ht
    unfold leadVertical
    rw [integral_const_mul]
    have hIntEq :
        (∫ tw : ℝ, ∫ tz : ℝ,
          f (4 + t * Complex.I) (4 + tw * Complex.I) (2 + tz * Complex.I)) =
        ∫ v : ℝ × ℝ, G (t, v) := by
      simpa only [Measure.volume_eq_prod ℝ ℝ] using
        (MeasureTheory.integral_integral
          (f := fun tw tz : ℝ => f (4 + t * Complex.I)
            (4 + tw * Complex.I) (2 + tz * Complex.I)) ht)
    change κ * (κ * ∫ tw : ℝ, ∫ tz : ℝ,
      f (4 + t * Complex.I) (4 + tw * Complex.I) (2 + tz * Complex.I)) = _
    rw [hIntEq]
    ring
  unfold leadTripleVertical
  change κ * (∫ t : ℝ, leadVertical 4 (fun w => leadVertical 2
      (fun z => f (4 + t * Complex.I) w z))) = _
  calc
    _ = κ * ∫ t : ℝ, κ ^ 2 * ∫ v : ℝ × ℝ, G (t, v) := by
      congr 1
      exact integral_congr_ae hPair
    _ = κ ^ 3 * ∫ t : ℝ, ∫ v : ℝ × ℝ, G (t, v) := by
      rw [integral_const_mul]
      ring
    _ = _ := by
      change κ ^ 3 * (∫ t : ℝ, ∫ v : ℝ × ℝ, G (t, v)) = κ ^ 3 * ∫ p : ℝ × (ℝ × ℝ), G p
      rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
      exact congrArg (fun x : ℂ => κ ^ 3 * x) (integral_prod G hp).symm

private def prF_indexEquiv :
    (S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) ≃
      (U.U × (S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal)) where
  toFun p := (p.2.2.2.1, (p.1, p.2.1, p.2.2.1, p.2.2.2.2))
  invFun q := (q.2.1, q.2.2.1, q.2.2.2.1, q.1, q.2.2.2.2)
  left_inv p := by
    cases p with
    | mk c rest =>
      cases rest with
      | mk n rest =>
        cases rest with
        | mk s rest =>
          cases rest with
          | mk u r => rfl
  right_inv q := by
    cases q with
    | mk u rest =>
      cases rest with
      | mk c rest =>
        cases rest with
        | mk n rest =>
          cases rest with
          | mk s r => rfl

/-- IMPL: dominate the individual terms before moving all sums through the integral. -/
theorem mellin_sum_interchange
    (hdecay : LeadWeightDecay R sd W) (hcoeff : LeadCoeffBoundContract R η U)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
    (∀ p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal,
      Integrable (fun t : ℝ × ℝ × ℝ =>
        leadMellinTerm R sd W η U X Y Z (4 + t.1 * Complex.I)
          (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) p)) ∧
    Summable (fun p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal =>
      ∫ t : ℝ × ℝ × ℝ,
        ‖leadMellinTerm R sd W η U X Y Z (4 + t.1 * Complex.I)
          (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) p‖) ∧
    leadTripleVertical 4 4 2 (fun ξ w z =>
      leadMellinWeight R sd W X Y Z ξ w z *
        ∑' u : U.U, (U.q u : ℂ) ^ (-z) * leadCalF R η U u ξ w z) =
      ∑' p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal,
        leadTripleVertical 4 4 2 (fun ξ w z =>
          leadMellinTerm R sd W η U X Y Z ξ w z p) := by
  classical
  let P := S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal
  let Q := S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal
  let ξ (t : ℝ × ℝ × ℝ) : ℂ := 4 + t.1 * Complex.I
  let w (t : ℝ × ℝ × ℝ) : ℂ := 4 + t.2.1 * Complex.I
  let z (t : ℝ × ℝ × ℝ) : ℂ := 2 + t.2.2 * Complex.I
  let Term (p : P) (t : ℝ × ℝ × ℝ) : ℂ :=
    leadMellinTerm R sd W η U X Y Z (ξ t) (w t) (z t) p
  let G (t : ℝ × ℝ × ℝ) : ℝ :=
    Real.exp (-(t.1 + t.2.2) ^ 2) *
      (1 + |t.2.2|) ^ (-2 : ℝ) * (1 + |t.2.1|) ^ (-2 : ℝ)
  let fC : S.SqfExtIdeal → ℝ := fun c => qI c.1 ^ (-3 : ℝ)
  let fN : S.ExtIdeal → ℝ := fun n => qI n.1 ^ (-10 : ℝ)
  let fS : S.ExtIdeal → ℝ := fun s => qI s.1 ^ (-3 : ℝ)
  let fU : U.U → ℝ := fun u => U.q u ^ (-2 : ℝ)
  let fR : S.ExtIdeal → ℝ := fun r => qI r.1 ^ (-12 : ℝ)
  let K : P → ℝ := fun p =>
    fC p.1 * (fN p.2.1 * (fS p.2.2.1 * (fU p.2.2.2.1 * fR p.2.2.2.2)))
  let K0 : Q → ℝ := fun p => fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2))
  rcases hdecay with ⟨hDM, hDW, hMDecay, hWDecay, _⟩
  obtain ⟨CM, hCM, hMbound⟩ := hMDecay 2 2 2 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CW, hCW, hWbound⟩ := hWDecay 4 4 2 le_rfl (by norm_num)
  let A0 : ℝ := X ^ (-(3 / 2 : ℝ)) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ) *
    Real.exp 25 * CM * CW
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hξre (t : ℝ × ℝ × ℝ) : (ξ t).re = 4 := by simp [ξ]
  have hwre (t : ℝ × ℝ × ℝ) : (w t).re = 4 := by simp [w]
  have hzre (t : ℝ × ℝ × ℝ) : (z t).re = 2 := by simp [z]
  have hMline : Continuous (fun t : ℝ × ℝ × ℝ => leadM R sd W (z t)) := by
    apply continuousOn_univ.mp
    apply hDM.continuousOn.comp
    · fun_prop
    · intro t ht
      simp [z]
  have hWline : Continuous (fun t : ℝ × ℝ × ℝ => leadW1hat W (w t)) :=
    hDW.continuous.comp (by fun_prop)
  have hWeightMeas : Measurable (fun t : ℝ × ℝ × ℝ =>
      leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t)) := by
    have hXpart : Measurable (fun t : ℝ × ℝ × ℝ =>
        (X : ℂ) ^ ((1 / 2 : ℂ) - z t)) := by fun_prop (disch := positivity)
    have hZpart : Measurable (fun t : ℝ × ℝ × ℝ =>
        (Z : ℂ) ^ (ξ t + z t - 1)) := by fun_prop (disch := positivity)
    have hYpart : Measurable (fun t : ℝ × ℝ × ℝ =>
        (Y : ℂ) ^ (w t - 1)) := by fun_prop (disch := positivity)
    have hExppart : Measurable (fun t : ℝ × ℝ × ℝ =>
        Complex.exp ((ξ t + z t - 1) ^ 2)) := by fun_prop
    unfold leadMellinWeight
    exact (((((hXpart.mul hZpart).mul hYpart).mul hExppart).mul hMline.measurable).mul
      hWline.measurable)
  have hcalFTermMeas (u : U.U) (p : Q) :
      Measurable (fun t : ℝ × ℝ × ℝ => leadCalFTerm R η U u (ξ t) (w t) (z t) p) := by
    dsimp [leadCalFTerm]
    fun_prop (disch := positivity)
  have hqPowMeas (u : U.U) :
      Measurable (fun t : ℝ × ℝ × ℝ => (U.q u : ℂ) ^ (-z t)) := by
    fun_prop (disch := positivity)
  have hTermMeas (p : P) : Measurable (Term p) := by
    cases p with
    | mk c rest => cases rest with
      | mk n rest => cases rest with
        | mk s rest => cases rest with
          | mk u r =>
            dsimp [Term, leadMellinTerm]
            exact (hWeightMeas.mul (hqPowMeas u)).mul
              (hcalFTermMeas u (c, n, s, r))
  letI : Countable (Ideal (𝓞 F)) := prF_ideal_countable
  letI : Countable S.ExtIdeal :=
    Function.Injective.countable (f := fun I : S.ExtIdeal => I.1) Subtype.val_injective
  letI : Countable S.SqfExtIdeal :=
    Function.Injective.countable (f := fun I : S.SqfExtIdeal => I.1) Subtype.val_injective
  letI : Countable U.U := prF_frequency_type_countable (η := η) (U := U)
  have hfC : Summable fC := by
    dsimp [fC]
    exact prF_sqf_ideal_rpow_summable (R0 := R) 3 (by norm_num)
  have hfN : Summable fN := by
    dsimp [fN]
    exact prF_ext_ideal_rpow_summable (S := S) 10 (by norm_num)
  have hfS : Summable fS := by
    dsimp [fS]
    exact prF_ext_ideal_rpow_summable (S := S) 3 (by norm_num)
  have hfU : Summable fU := by
    dsimp [fU]
    exact prF_frequency_q_inv_sq_summable (η := η) (U := U)
  have hfR : Summable fR := by
    dsimp [fR]
    exact prF_ext_ideal_rpow_summable (S := S) 12 (by norm_num)
  have hfC0 : ∀ c, 0 ≤ fC c := fun c =>
    Real.rpow_nonneg (prF_qI_sqf_pos (S := S) c).le _
  have hfN0 : ∀ n, 0 ≤ fN n := fun n =>
    Real.rpow_nonneg (prF_qI_ext_pos (S := S) n).le _
  have hfS0 : ∀ s, 0 ≤ fS s := fun s =>
    Real.rpow_nonneg (prF_qI_ext_pos (S := S) s).le _
  have hfU0 : ∀ u, 0 ≤ fU u := fun u => Real.rpow_nonneg (U.q_pos u).le _
  have hfR0 : ∀ r, 0 ≤ fR r := fun r =>
    Real.rpow_nonneg (prF_qI_ext_pos (S := S) r).le _
  have hSR := prF_real_summable_product fS fR hfS hfR hfS0 hfR0
  have hNSR := prF_real_summable_product fN
      (fun p : S.ExtIdeal × S.ExtIdeal => fS p.1 * fR p.2) hfN hSR hfN0
      (fun p => mul_nonneg (hfS0 p.1) (hfR0 p.2))
  have hCNSR := prF_real_summable_product fC
      (fun p : S.ExtIdeal × (S.ExtIdeal × S.ExtIdeal) =>
        fN p.1 * (fS p.2.1 * fR p.2.2)) hfC hNSR hfC0
      (fun p => mul_nonneg (hfN0 p.1) (mul_nonneg (hfS0 p.2.1) (hfR0 p.2.2)))
  have hK0 : Summable K0 := by simpa [K0] using hCNSR
  have hUR := prF_real_summable_product fU fR hfU hfR hfU0 hfR0
  have hSUR := prF_real_summable_product fS
      (fun p : U.U × S.ExtIdeal => fU p.1 * fR p.2) hfS hUR hfS0
      (fun p => mul_nonneg (hfU0 p.1) (hfR0 p.2))
  have hNSUR := prF_real_summable_product fN
      (fun p : S.ExtIdeal × (U.U × S.ExtIdeal) =>
        fS p.1 * (fU p.2.1 * fR p.2.2)) hfN hSUR hfN0
      (fun p => mul_nonneg (hfS0 p.1) (mul_nonneg (hfU0 p.2.1) (hfR0 p.2.2)))
  have hCNSUR := prF_real_summable_product fC
      (fun p : S.ExtIdeal × (S.ExtIdeal × (U.U × S.ExtIdeal)) =>
        fN p.1 * (fS p.2.1 * (fU p.2.2.1 * fR p.2.2.2))) hfC hNSUR hfC0
      (fun p => mul_nonneg (hfN0 p.1)
        (mul_nonneg (hfS0 p.2.1) (mul_nonneg (hfU0 p.2.2.1) (hfR0 p.2.2.2))))
  have hK : Summable K := by simpa [K] using hCNSUR
  have hKnonneg (p : P) : 0 ≤ K p := by
    exact mul_nonneg (hfC0 p.1) (mul_nonneg (hfN0 p.2.1)
      (mul_nonneg (hfS0 p.2.2.1) (mul_nonneg (hfU0 p.2.2.2.1) (hfR0 p.2.2.2.2))))
  let B : ℝ := ∑' p : P, K p
  have hKpair : Summable (fun q : U.U × Q => K ((prF_indexEquiv (U := U)).symm q)) :=
    hK.comp_injective (prF_indexEquiv (U := U)).symm.injective
  have hpairTerm (t : ℝ × ℝ × ℝ) (q : U.U × Q) :
      ‖(U.q q.1 : ℂ) ^ (-(z t)) *
          leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2‖ ≤
        K ((prF_indexEquiv (U := U)).symm q) := by
    have hpow : ‖(U.q q.1 : ℂ) ^ (-(z t))‖ = fU q.1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (U.q_pos q.1)]
      simp [fU, z]
    have hcoef := hcoeff (ξ t) (w t) (z t) (hξre t) (hwre t) (hzre t) q.1 q.2
    have hbound :
        ‖leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2‖ ≤ K0 q.2 := by
      calc
        _ ≤ qI q.2.1.1 ^ (-3 : ℝ) * qI q.2.2.1.1 ^ (-10 : ℝ) *
            qI q.2.2.2.1.1 ^ (-3 : ℝ) * qI q.2.2.2.2.1 ^ (-12 : ℝ) := hcoef
        _ = K0 q.2 := by simp [K0, fC, fN, fS, fR]; ring
    have hnorm :
        ‖(U.q q.1 : ℂ) ^ (-(z t)) *
          leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2‖ =
        ‖(U.q q.1 : ℂ) ^ (-(z t))‖ *
          ‖leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2‖ := norm_mul _ _
    have hreal := mul_le_mul (le_of_eq hpow) hbound (norm_nonneg _) (hfU0 q.1)
    calc
      _ = ‖(U.q q.1 : ℂ) ^ (-(z t))‖ *
          ‖leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2‖ := hnorm
      _ ≤ fU q.1 * K0 q.2 := hreal
      _ = K ((prF_indexEquiv (U := U)).symm q) := by
        simp [K, K0, prF_indexEquiv, fC, fN, fS, fU, fR]
        ring
  have hpairSummable (t : ℝ × ℝ × ℝ) : Summable (fun q : U.U × Q =>
      (U.q q.1 : ℂ) ^ (-(z t)) *
        leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2) := by
    apply Summable.of_norm_bounded hKpair
    intro q
    exact hpairTerm t q
  have hrowSummable (u : U.U) (t : ℝ × ℝ × ℝ) :
      Summable (fun p : Q => leadCalFTerm R η U u (ξ t) (w t) (z t) p) := by
    have hnormSummable : Summable (fun p : Q =>
        ‖leadCalFTerm R η U u (ξ t) (w t) (z t) p‖) := by
      apply Summable.of_nonneg_of_le (fun p => norm_nonneg _)
        (fun p => ?_) hK0
      have hcoef := hcoeff (ξ t) (w t) (z t) (hξre t) (hwre t) (hzre t) u p
      calc
        _ ≤ qI p.1.1 ^ (-3 : ℝ) * qI p.2.1.1 ^ (-10 : ℝ) *
            qI p.2.2.1.1 ^ (-3 : ℝ) * qI p.2.2.2.1 ^ (-12 : ℝ) := hcoef
        _ = K0 p := by simp [K0, fC, fN, fS, fR]; ring
    exact hnormSummable.of_norm
  have hMpow (t : ℝ × ℝ × ℝ) :
      ‖(X : ℂ) ^ ((1 / 2 : ℂ) - z t)‖ = X ^ (-(3 / 2 : ℝ)) := by
    have hre : ((1 / 2 : ℂ) - z t).re = -(3 / 2 : ℝ) := by
      simp [z]
      norm_num
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hre]
  have hZpow (t : ℝ × ℝ × ℝ) :
      ‖(Z : ℂ) ^ (ξ t + z t - 1)‖ = Z ^ (5 : ℝ) := by
    have hre : (ξ t + z t - 1).re = 5 := by
      simp [ξ, z]
      norm_num
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ, hre]
  have hYpow (t : ℝ × ℝ × ℝ) :
      ‖(Y : ℂ) ^ (w t - 1)‖ = Y ^ (3 : ℝ) := by
    have hre : (w t - 1).re = 3 := by
      simp [w]
      norm_num
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, hre]
  have hExp (t : ℝ × ℝ × ℝ) :
      ‖Complex.exp ((ξ t + z t - 1) ^ 2)‖ =
        Real.exp (25 - (t.1 + t.2.2) ^ 2) := by
    rw [Complex.norm_exp]
    have harg : ξ t + z t - 1 = (5 : ℂ) + ((t.1 + t.2.2 : ℝ) : ℂ) * Complex.I := by
      simp [ξ, z]
      ring
    rw [harg]
    have hsq : ((5 : ℂ) + ((t.1 + t.2.2 : ℝ) : ℂ) * Complex.I) ^ 2 =
        ((25 - (t.1 + t.2.2) ^ 2 : ℝ) : ℂ) +
          ((10 * (t.1 + t.2.2) : ℝ) : ℂ) * Complex.I := by
      calc
        _ = 25 + 10 * ((t.1 + t.2.2 : ℝ) : ℂ) * Complex.I +
            (((t.1 + t.2.2 : ℝ) : ℂ) * Complex.I) ^ 2 := by ring
        _ = 25 + 10 * ((t.1 + t.2.2 : ℝ) : ℂ) * Complex.I +
            ((t.1 + t.2.2 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 := by rw [mul_pow]
        _ = _ := by rw [Complex.I_sq]; push_cast; ring
    rw [hsq]
    simp
    norm_cast
  have hMdecay (t : ℝ × ℝ × ℝ) :
      ‖leadM R sd W (z t)‖ ≤ CM * (1 + |t.2.2|) ^ (-2 : ℝ) := by
    simpa [z] using hMbound 2 t.2.2 (by norm_num) (by norm_num)
  have hWdecay (t : ℝ × ℝ × ℝ) :
      ‖leadW1hat W (w t)‖ ≤ CW * (1 + |t.2.1|) ^ (-2 : ℝ) := by
    simpa [w] using hWbound 4 t.2.1 (by norm_num) (by norm_num)
  have hWeightBound (t : ℝ × ℝ × ℝ) :
      ‖leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t)‖ ≤ A0 * G t := by
    have hexp : Real.exp (25 - (t.1 + t.2.2) ^ 2) =
        Real.exp 25 * Real.exp (-(t.1 + t.2.2) ^ 2) := by
      rw [show 25 - (t.1 + t.2.2) ^ 2 = 25 + (-(t.1 + t.2.2) ^ 2) by ring,
        Real.exp_add]
    simp only [leadMellinWeight, norm_mul, hMpow t, hZpow t, hYpow t, hExp t]
    calc
      _ ≤ X ^ (-(3 / 2 : ℝ)) * Z ^ (5 : ℝ) * Y ^ (3 : ℝ) *
          (Real.exp 25 * Real.exp (-(t.1 + t.2.2) ^ 2)) *
            (CM * (1 + |t.2.2|) ^ (-2 : ℝ)) *
              (CW * (1 + |t.2.1|) ^ (-2 : ℝ)) := by
        rw [hexp]
        gcongr
        exact hMdecay t
        exact hWdecay t
      _ = A0 * G t := by dsimp [A0, G]; ring
  have hTermBound (p : P) (t : ℝ × ℝ × ℝ) :
      ‖Term p t‖ ≤ A0 * G t * K p := by
    let q := (p.1, p.2.1, p.2.2.1, p.2.2.2.2)
    have hqpow : ‖(U.q p.2.2.2.1 : ℂ) ^ (-z t)‖ = fU p.2.2.2.1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (U.q_pos p.2.2.2.1)]
      simp [fU, z]
    have hcoef := hcoeff (ξ t) (w t) (z t) (hξre t) (hwre t) (hzre t)
      p.2.2.2.1 q
    have htermEq : Term p t =
        leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
          ((U.q p.2.2.2.1 : ℂ) ^ (-z t) *
            leadCalFTerm R η U p.2.2.2.1 (ξ t) (w t) (z t) q) := by
      dsimp [Term, leadMellinTerm]
      exact mul_assoc _ _ _
    rw [htermEq, norm_mul, norm_mul]
    have hcoef' : ‖leadCalFTerm R η U p.2.2.2.1 (ξ t) (w t) (z t) q‖ ≤
        fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2.2)) := by
      calc
        _ ≤ qI p.1.1 ^ (-3 : ℝ) * qI p.2.1.1 ^ (-10 : ℝ) *
            qI p.2.2.1.1 ^ (-3 : ℝ) * qI p.2.2.2.2.1 ^ (-12 : ℝ) := hcoef
        _ = fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2.2)) := by
          simp [fC, fN, fS, fR]
          ring
    have hinner :
        ‖(U.q p.2.2.2.1 : ℂ) ^ (-z t)‖ *
          ‖leadCalFTerm R η U p.2.2.2.1 (ξ t) (w t) (z t) q‖ ≤
            fU p.2.2.2.1 *
              (fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2.2))) := by
      exact mul_le_mul (le_of_eq hqpow) hcoef' (norm_nonneg _) (hfU0 p.2.2.2.1)
    have hGt0 : 0 ≤ G t := by
      dsimp [G]
      positivity
    have hbase0 : 0 ≤ A0 * G t := mul_nonneg hA0 hGt0
    have hinner0 : 0 ≤
        ‖(U.q p.2.2.2.1 : ℂ) ^ (-z t)‖ *
          ‖leadCalFTerm R η U p.2.2.2.1 (ξ t) (w t) (z t) q‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t)‖ *
          (‖(U.q p.2.2.2.1 : ℂ) ^ (-z t)‖ *
            ‖leadCalFTerm R η U p.2.2.2.1 (ξ t) (w t) (z t) q‖) ≤
        (A0 * G t) * (fU p.2.2.2.1 *
          (fC p.1 * (fN p.2.1 * (fS p.2.2.1 * fR p.2.2.2.2)))) :=
        mul_le_mul (hWeightBound t) hinner hinner0 hbase0
      _ = A0 * G t * K p := by dsimp [K]; ring
  have hGint : Integrable G volume := by
    simpa [G] using prF_gaussian_shear_majorant_integrable (C := 1)
  have hGnonneg (t : ℝ × ℝ × ℝ) : 0 ≤ G t := by
    dsimp [G]
    positivity
  have hTermIntegrable (p : P) : Integrable (Term p) volume := by
    let Cp : ℝ := A0 * K p
    have hCp : 0 ≤ Cp := by
      dsimp [Cp]
      exact mul_nonneg hA0 (hKnonneg p)
    have hmajor : Integrable (fun t : ℝ × ℝ × ℝ => Cp * G t) volume := by
      have h := hGint.const_mul Cp
      simpa [Cp, mul_assoc, mul_left_comm, mul_comm] using h
    apply hmajor.mono' (hTermMeas p).aestronglyMeasurable
    filter_upwards with t
    simpa [Cp, mul_assoc, mul_left_comm, mul_comm] using hTermBound p t
  have hTermNormIntegral (p : P) :
      (∫ t : ℝ × ℝ × ℝ, ‖Term p t‖) ≤ (A0 * K p) * ∫ t : ℝ × ℝ × ℝ, G t := by
    let Cp : ℝ := A0 * K p
    have hmajor : Integrable (fun t : ℝ × ℝ × ℝ => Cp * G t) volume := by
      have h := hGint.const_mul Cp
      simpa [Cp, mul_assoc, mul_left_comm, mul_comm] using h
    have hdom (t : ℝ × ℝ × ℝ) : ‖Term p t‖ ≤ Cp * G t := by
      simpa [Cp, mul_assoc, mul_left_comm, mul_comm] using hTermBound p t
    calc
      _ ≤ ∫ t : ℝ × ℝ × ℝ, Cp * G t :=
        integral_mono (hTermIntegrable p).norm hmajor hdom
      _ = Cp * ∫ t : ℝ × ℝ × ℝ, G t := by rw [integral_const_mul]
      _ = _ := rfl
  let JG : ℝ := ∫ t : ℝ × ℝ × ℝ, G t
  have hJG : 0 ≤ JG := by
    dsimp [JG]
    exact integral_nonneg hGnonneg
  have hTermNormSummable : Summable (fun p : P => ∫ t : ℝ × ℝ × ℝ, ‖Term p t‖) := by
    have hmajor : Summable (fun p : P => (A0 * JG) * K p) := hK.mul_left (A0 * JG)
    apply Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _) ?_ hmajor
    intro p
    calc
      (∫ t : ℝ × ℝ × ℝ, ‖Term p t‖) ≤ (A0 * K p) * JG := by
        simpa [JG] using hTermNormIntegral p
      _ = (A0 * JG) * K p := by ring
  have hTotalMeas : Measurable (fun t : ℝ × ℝ × ℝ => ∑' p : P, Term p t) := by
    apply Measurable.tsum
    intro p
    exact hTermMeas p
  have hTotalBound (t : ℝ × ℝ × ℝ) :
      ‖∑' p : P, Term p t‖ ≤ (A0 * B) * G t := by
    have hscaled : Summable (fun p : P => (A0 * G t) * K p) := hK.mul_left (A0 * G t)
    have hpoint : Summable (fun p : P => ‖Term p t‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => hTermBound p t) hscaled
    calc
      _ ≤ ∑' p : P, ‖Term p t‖ := norm_tsum_le_tsum_norm hpoint
      _ ≤ ∑' p : P, (A0 * G t) * K p := hpoint.tsum_le_tsum
        (fun p => hTermBound p t) hscaled
      _ = (A0 * B) * G t := by
        rw [hK.tsum_mul_left (A0 * G t)]
        dsimp [B]
        ring
  have hTotalIntegrable : Integrable (fun t : ℝ × ℝ × ℝ => ∑' p : P, Term p t) volume := by
    have hmajor : Integrable (fun t : ℝ × ℝ × ℝ => (A0 * B) * G t) volume := by
      have h := hGint.const_mul (A0 * B)
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    apply hmajor.mono' hTotalMeas.aestronglyMeasurable
    filter_upwards with t
    exact hTotalBound t
  have hpairPointwise (t : ℝ × ℝ × ℝ) :
      (∑' p : P, Term p t) =
        leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
          ∑' u : U.U, (U.q u : ℂ) ^ (-(z t)) *
            leadCalF R η U u (ξ t) (w t) (z t) := by
    let e := prF_indexEquiv (U := U)
    let PairTerm (q : U.U × Q) : ℂ :=
      (U.q q.1 : ℂ) ^ (-(z t)) *
        leadCalFTerm R η U q.1 (ξ t) (w t) (z t) q.2
    have hTermPair (u : U.U) (p : Q) :
        Term (e.symm (u, p)) t =
          leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) * PairTerm (u, p) := by
      rcases p with ⟨c, n, s, r⟩
      have he : e.symm (u, (c, n, s, r)) = (c, n, s, u, r) := by
        rfl
      rw [he]
      dsimp [Term, PairTerm, leadMellinTerm]
      exact mul_assoc _ _ _
    have hTermFun : (fun q : U.U × Q => Term (e.symm q) t) =
        fun q => leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) * PairTerm q := by
      funext q
      rcases q with ⟨u, p⟩
      exact hTermPair u p
    have hrow (u : U.U) :
        (∑' q : Q, leadCalFTerm R η U u (ξ t) (w t) (z t) q) =
          leadCalF R η U u (ξ t) (w t) (z t) := by
      rfl
    calc
      _ = ∑' q : U.U × Q, Term (e.symm q) t := e.tsum_eq _
      _ = leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
          ∑' q : U.U × Q, PairTerm q := by
        rw [hTermFun]
        exact (hpairSummable t).tsum_mul_left _
      _ = leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
          ∑' u : U.U, (U.q u : ℂ) ^ (-(z t)) *
            leadCalF R η U u (ξ t) (w t) (z t) := by
        apply congrArg (fun a : ℂ =>
          leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) * a)
        calc
          (∑' q : U.U × Q, PairTerm q) =
              ∑' u : U.U, ∑' p : Q, PairTerm (u, p) := (hpairSummable t).tsum_prod
          _ = ∑' u : U.U,
              (U.q u : ℂ) ^ (-(z t)) *
                ∑' p : Q, leadCalFTerm R η U u (ξ t) (w t) (z t) p := by
            apply tsum_congr
            intro u
            simpa [PairTerm] using
              (hrowSummable u t).tsum_mul_left ((U.q u : ℂ) ^ (-(z t)))
          _ = _ := by simp [PairTerm, hrow]
  have hFsumIntegrable : Integrable (fun t : ℝ × ℝ × ℝ =>
      leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
        ∑' u : U.U, (U.q u : ℂ) ^ (-(z t)) *
          leadCalF R η U u (ξ t) (w t) (z t)) volume := by
    have hEq : (fun t : ℝ × ℝ × ℝ =>
        leadMellinWeight R sd W X Y Z (ξ t) (w t) (z t) *
          ∑' u : U.U, (U.q u : ℂ) ^ (-(z t)) *
            leadCalF R η U u (ξ t) (w t) (z t)) =
        fun t => ∑' p : P, Term p t := by
      funext t
      exact (hpairPointwise t).symm
    rw [hEq]
    exact hTotalIntegrable
  have hFubini := integral_tsum_of_summable_integral_norm hTermIntegrable hTermNormSummable
  have hIntTermSummable : Summable (fun p : P => ∫ t : ℝ × ℝ × ℝ, Term p t) :=
    hTermNormSummable.of_norm_bounded fun p =>
      norm_integral_le_integral_norm (μ := volume) (Term p)
  let fsum (ξ' w' z' : ℂ) := leadMellinWeight R sd W X Y Z ξ' w' z' *
    ∑' u : U.U, (U.q u : ℂ) ^ (-z') * leadCalF R η U u ξ' w' z'
  let fterm (p : P) (ξ' w' z' : ℂ) := leadMellinTerm R sd W η U X Y Z ξ' w' z' p
  have hTripleSum := prF_tripleVertical_eq_integral_prod fsum (by
    simpa [fsum, ξ, w, z] using hFsumIntegrable)
  have hTripleTerm (p : P) := prF_tripleVertical_eq_integral_prod (fterm p) (by
    simpa [fterm, Term, ξ, w, z] using hTermIntegrable p)
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact hTermIntegrable p
  · simpa [Term, ξ, w, z] using hTermNormSummable
  · change leadTripleVertical 4 4 2 fsum =
        ∑' p : P, leadTripleVertical 4 4 2 (fterm p)
    rw [hTripleSum]
    calc
      (1 / (2 * Real.pi) : ℂ) ^ 3 *
          (∫ t : ℝ × ℝ × ℝ, fsum (ξ t) (w t) (z t)) =
        (1 / (2 * Real.pi) : ℂ) ^ 3 *
          (∫ t : ℝ × ℝ × ℝ, ∑' p : P, Term p t) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
          (hpairPointwise t).symm)
      _ = (1 / (2 * Real.pi) : ℂ) ^ 3 *
          ∑' p : P, ∫ t : ℝ × ℝ × ℝ, Term p t := by
            exact congrArg _ hFubini.symm
      _ = ∑' p : P, (1 / (2 * Real.pi) : ℂ) ^ 3 *
          ∫ t : ℝ × ℝ × ℝ, Term p t :=
            (hIntTermSummable.tsum_mul_left _).symm
      _ = ∑' p : P, leadTripleVertical 4 4 2 (fterm p) := by
            apply tsum_congr
            intro p
            exact (hTripleTerm p).symm

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
