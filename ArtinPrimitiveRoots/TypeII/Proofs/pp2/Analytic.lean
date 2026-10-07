import Mathlib

namespace ArtinPrimitiveRoots.TypeII.PP.Proofs

open Complex Metric Set Filter
open scoped ComplexConjugate
open scoped Topology

theorem eq_of_continuousAt_of_eventuallyEq_nhdsNE {f g : ℂ → ℂ} {z : ℂ}
    (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (hfg : f =ᶠ[𝓝[≠] z] g) : f z = g z := by
  have hft : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have hgt : Tendsto g (𝓝[≠] z) (𝓝 (g z)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique (hft.congr' hfg) hgt

theorem eq_of_continuousAt_of_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ U) (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (hfg : f =ᶠ[Filter.codiscreteWithin U] g) : f z = g z := by
  apply eq_of_continuousAt_of_eventuallyEq_nhdsNE hf hg
  have heq := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hfg) z hz
  have hmem : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hU.mem_nhds hz)
  filter_upwards [heq, hmem] with w hwEq hwU
  exact hwEq hwU

theorem logDeriv_congr_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfg : f =ᶠ[Filter.codiscreteWithin U] g) :
    logDeriv f =ᶠ[Filter.codiscreteWithin U] logDeriv g := by
  have hderiv := hf.deriv_eventuallyEq_codiscreteWithin hg hfg
  filter_upwards [hfg, hderiv] with z hz hdz
  simp [logDeriv, hz, hdz]

theorem logDeriv_eq_of_analytic_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hz : z ∈ U) (hfz : f z ≠ 0) (hgz : g z ≠ 0)
    (hfg : f =ᶠ[Filter.codiscreteWithin U] g) : logDeriv f z = logDeriv g z := by
  have hlog := logDeriv_congr_codiscreteWithin hf.meromorphicOn hg.meromorphicOn hfg
  apply eq_of_continuousAt_of_codiscreteWithin hU hz ?_ ?_ hlog
  · dsimp [logDeriv]
    exact (hf z hz).deriv.continuousAt.div (hf z hz).continuousAt hfz
  · dsimp [logDeriv]
    exact (hg z hz).deriv.continuousAt.div (hg z hz).continuousAt hgz

theorem logDeriv_eq_of_meromorphic_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hU : IsOpen U) (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfa : AnalyticAt ℂ f z) (hga : AnalyticAt ℂ g z) (hz : z ∈ U)
    (hfz : f z ≠ 0) (hgz : g z ≠ 0)
    (hfg : f =ᶠ[Filter.codiscreteWithin U] g) : logDeriv f z = logDeriv g z := by
  have hlog := logDeriv_congr_codiscreteWithin hf hg hfg
  apply eq_of_continuousAt_of_codiscreteWithin hU hz ?_ ?_ hlog
  · dsimp [logDeriv]
    exact hfa.deriv.continuousAt.div hfa.continuousAt hfz
  · dsimp [logDeriv]
    exact hga.deriv.continuousAt.div hga.continuousAt hgz

/-- A finite list that records a natural multiplicity by repeating each supported point. -/
noncomputable def multiplicityList {α : Type*} (s : Finset α) (m : α → ℕ) : List α :=
  s.toList.flatMap fun a ↦ List.replicate (m a) a

theorem multiplicityList_length {α : Type*} (s : Finset α) (m : α → ℕ) :
    (multiplicityList s m).length = ∑ a ∈ s, m a := by
  simp [multiplicityList]

theorem multiplicityList_sum_map {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (m : α → ℕ) (g : α → β) :
    ((multiplicityList s m).map g).sum = ∑ a ∈ s, m a • g a := by
  change ((s.toList.flatMap fun a ↦ List.replicate (m a) a).map g).sum = _
  rw [List.map_flatMap]
  have hL (l : List α) :
      (l.flatMap fun a ↦ (List.replicate (m a) a).map g).sum =
        (l.map fun a ↦ m a • g a).sum := by
    induction l with
    | nil => simp
    | cons a l ih =>
        have ih' := ih
        simp only [List.map_replicate] at ih'
        simpa only [List.flatMap_cons, List.map_cons, List.sum_append, List.sum_cons,
          List.sum_replicate, List.map_replicate, ih']
  rw [hL]
  simp

theorem analyticOrderNatAt_pos_iff {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hfinite : analyticOrderAt f z ≠ ⊤) :
    0 < analyticOrderNatAt f z ↔ f z = 0 := by
  have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
    Nat.cast_analyticOrderNatAt hfinite
  constructor
  · intro h
    have horder : analyticOrderAt f z ≠ 0 := by
      have hne : (analyticOrderNatAt f z : ℕ∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt h)
      rw [hcast] at hne
      exact hne
    exact apply_eq_zero_of_analyticOrderAt_ne_zero horder
  · intro hzero
    have horder : analyticOrderAt f z ≠ 0 := hf.analyticOrderAt_ne_zero.mpr hzero
    have hne : (analyticOrderNatAt f z : ℕ∞) ≠ 0 := by rw [hcast]; exact horder
    apply Nat.pos_of_ne_zero
    intro hn
    exact hne (by exact_mod_cast hn)

theorem mem_multiplicityList {α : Type*} [DecidableEq α] {s : Finset α} {m : α → ℕ}
    {a : α} : a ∈ multiplicityList s m ↔ ∃ b ∈ s, b = a ∧ 0 < m b := by
  simp [multiplicityList, List.mem_flatMap]

theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  by_cases htop : analyticOrderAt f z = ⊤
  · simp [analyticOrderNatAt, htop]
  · have hcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
      Nat.cast_analyticOrderNatAt htop
    rw [← hcast]
    simp

theorem logDeriv_canonicalFactor {R : ℝ} (hR : 0 < R) {a z : ℂ}
    (haz : z ≠ a) (hnum : (R : ℂ) ^ 2 - conj a * z ≠ 0) :
    deriv (Complex.canonicalFactor R a) z / Complex.canonicalFactor R a z =
      -conj a / ((R : ℂ) ^ 2 - conj a * z) - 1 / (z - a) := by
  have hden : (R : ℂ) * (z - a) ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hR.ne') (sub_ne_zero.mpr haz)
  change deriv (fun w : ℂ ↦ ((R : ℂ) ^ 2 - conj a * w) / ((R : ℂ) * (w - a))) z /
      (((R : ℂ) ^ 2 - conj a * z) / ((R : ℂ) * (z - a))) = _
  have hquot := deriv_fun_div (c := fun w : ℂ ↦ (R : ℂ) ^ 2 - conj a * w)
    (d := fun w : ℂ ↦ (R : ℂ) * (w - a)) (x := z) (by fun_prop) (by fun_prop) hden
  have hnumD : deriv (fun w : ℂ ↦ (R : ℂ) ^ 2 - conj a * w) z = -conj a := by simp
  have hdenD : deriv (fun w : ℂ ↦ (R : ℂ) * (w - a)) z = (R : ℂ) := by simp
  rw [hquot, hnumD, hdenD]
  field_simp [hnum, hden, ofReal_ne_zero.mpr hR.ne']

/-- A circle in the Jensen window can be chosen to avoid all zeros, and its zero list
records the analytic multiplicities. -/
theorem disk_zero_list {r M : ℝ} (hr : 0 < r) (hM : 0 < M) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (8 * r)))
    (hbound : ∀ z ∈ closedBall 0 (8 * r), ‖f z‖ ≤ Real.exp M)
    (hcenter : Real.exp (-M) ≤ ‖f 0‖) :
    ∃ R : ℝ, ∃ S : Finset ℂ, ∃ Z : List ℂ,
      4 * r ≤ R ∧ R ≤ 5 * r ∧
      (∀ z : ℂ, ‖z‖ = R → f z ≠ 0) ∧
      Z = multiplicityList S (analyticOrderNatAt f) ∧
      (∀ a, a ∈ S ↔ a ∈ ball (0 : ℂ) R ∧ 0 < analyticOrderNatAt f a) ∧
      (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) ∧
      (∀ ρ, ρ ∈ Z ↔ f ρ = 0 ∧ ‖ρ‖ < R) := by
  classical
  have h0 : f 0 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hcenter)
  have hr8 : 0 < 8 * r := by positivity
  have hfiniteOnBall (z : ℂ) (hz : z ∈ ball 0 (8 * r)) : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    have hvanish : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have hzero : EqOn f 0 (ball 0 (8 * r)) :=
      (hf.mono ball_subset_closedBall).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_ball hz hvanish
    have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) (8 * r) := Metric.mem_ball_self hr8
    have hzero0 : f 0 = 0 := hzero hz0
    exact h0 hzero0
  have hfiniteOnSmall (z : ℂ) (hz : z ∈ closedBall 0 (5 * r)) :
      analyticOrderAt f z ≠ ⊤ := by
    apply hfiniteOnBall z
    rw [mem_ball_zero_iff]
    have hnorm := mem_closedBall_zero_iff.mp hz
    nlinarith [hr]
  have hf5 : AnalyticOnNhd ℂ f (closedBall 0 (5 * r)) := hf.mono (by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz ⊢
    nlinarith [hr])
  let d₅ : ℂ → ℤ := MeromorphicOn.divisor f (closedBall 0 (5 * r))
  have hTfinite : (d₅.support).Finite := by
    exact (MeromorphicOn.divisor f (closedBall 0 (5 * r))).finiteSupport
      (isCompact_closedBall 0 (5 * r))
  let T : Finset ℂ := hTfinite.toFinset
  have hTmem (a : ℂ) : a ∈ T ↔ a ∈ closedBall 0 (5 * r) ∧ 0 < analyticOrderNatAt f a := by
    constructor
    · intro ha
      have ha' : d₅ a ≠ 0 := hTfinite.mem_toFinset.mp ha
      have haClosed : a ∈ closedBall 0 (5 * r) :=
        (MeromorphicOn.divisor f (closedBall 0 (5 * r))).supportWithinDomain ha'
      have hdiv := divisor_eq_analyticOrderNatAt hf5 haClosed
      have horder := hfiniteOnSmall a haClosed
      change (MeromorphicOn.divisor f (closedBall 0 (5 * r)) a) ≠ 0 at ha'
      rw [hdiv] at ha'
      have hmpos : 0 < analyticOrderNatAt f a := Nat.pos_of_ne_zero (by
        intro hmzero
        apply ha'
        simp [hmzero])
      exact ⟨haClosed, hmpos⟩
    · rintro ⟨haClosed, hpos⟩
      apply hTfinite.mem_toFinset.mpr
      have hdiv := divisor_eq_analyticOrderNatAt hf5 haClosed
      change (MeromorphicOn.divisor f (closedBall 0 (5 * r)) a) ≠ 0
      rw [hdiv]
      exact_mod_cast (Nat.ne_of_gt hpos)
  have hzeroSupport (a : ℂ) (ha : a ∈ closedBall 0 (5 * r)) (hfa : f a = 0) : a ∈ T := by
    exact (hTmem a).2 ⟨ha, (analyticOrderNatAt_pos_iff (hf5 a ha) (hfiniteOnSmall a ha)).2 hfa⟩
  have hAvoidInfinite : (Set.Ioo (4 * r) (5 * r)).Infinite :=
    Set.Ioo_infinite (by nlinarith [hr])
  obtain ⟨R, hRint, hRnot⟩ := hAvoidInfinite.exists_notMem_finset (T.image fun a ↦ ‖a‖)
  have hRlower : 4 * r ≤ R := le_of_lt hRint.1
  have hRupper : R ≤ 5 * r := le_of_lt hRint.2
  have hboundary (z : ℂ) (hz : ‖z‖ = R) : f z ≠ 0 := by
    intro hzero
    have hzClosed : z ∈ closedBall 0 (5 * r) := by
      rw [mem_closedBall_zero_iff]
      rw [hz]
      exact hRupper
    have hzT := hzeroSupport z hzClosed hzero
    have : R ∈ T.image fun a ↦ ‖a‖ := Finset.mem_image.mpr ⟨z, hzT, hz⟩
    exact hRnot this
  have hBallR : ball (0 : ℂ) R ⊆ closedBall 0 (8 * r) := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_closedBall_zero_iff]
    nlinarith [hz, hRupper, hr]
  have hfR : AnalyticOnNhd ℂ f (ball (0 : ℂ) R) := hf.mono hBallR
  have hRfinite : (MeromorphicOn.divisor f (ball (0 : ℂ) R)).support.Finite :=
    hf.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall 0 (8 * r)) (by
      intro z hz
      rw [mem_ball_zero_iff] at hz
      rw [mem_closedBall_zero_iff]
      nlinarith [hRupper, hr])
  let S : Finset ℂ := hRfinite.toFinset
  have hSmem (a : ℂ) : a ∈ S ↔ a ∈ ball (0 : ℂ) R ∧ 0 < analyticOrderNatAt f a := by
    constructor
    · intro ha
      have ha' : (MeromorphicOn.divisor f (ball (0 : ℂ) R)) a ≠ 0 := hRfinite.mem_toFinset.mp ha
      have haBall : a ∈ ball (0 : ℂ) R := (MeromorphicOn.divisor f (ball 0 R)).supportWithinDomain ha'
      have hdiv := divisor_eq_analyticOrderNatAt hfR haBall
      have horder := hfiniteOnSmall a (by
        rw [mem_ball_zero_iff] at haBall
        rw [mem_closedBall_zero_iff]
        have hrR : R ≤ 5 * r := hRupper
        linarith [haBall, hrR])
      rw [hdiv] at ha'
      refine ⟨haBall, ?_⟩
      have ha8 : a ∈ closedBall 0 (8 * r) := by
        rw [mem_ball_zero_iff] at haBall
        rw [mem_closedBall_zero_iff]
        nlinarith [haBall, hRupper, hr]
      have hmn : analyticOrderNatAt f a ≠ 0 := by
        intro hmn
        apply ha'
        simp [hmn]
      exact Nat.pos_of_ne_zero hmn
    · rintro ⟨haBall, hpos⟩
      apply hRfinite.mem_toFinset.mpr
      have hdiv := divisor_eq_analyticOrderNatAt hfR haBall
      change (MeromorphicOn.divisor f (ball (0 : ℂ) R) a) ≠ 0
      rw [hdiv]
      exact_mod_cast (Nat.ne_of_gt hpos)
  let Z : List ℂ := multiplicityList S (analyticOrderNatAt f)
  have hlen : (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) := by
    let hf5 : AnalyticOnNhd ℂ f (closedBall 0 (5 * r)) := hf.mono (by
      intro z hz
      rw [mem_closedBall_zero_iff] at hz ⊢
      nlinarith [hr])
    have hf0 : f 0 ≠ 0 := h0
    have hfJ : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |8 * r|) := by
      simpa [abs_of_pos (by positivity : (0 : ℝ) < 8 * r)] using hf
    have hB5 : ∀ z ∈ Metric.sphere (0 : ℂ) |8 * r|, ‖f z‖ ≤ Real.exp M := by
      intro z hz
      have hz' : z ∈ closedBall (0 : ℂ) (8 * r) := by
        simpa [abs_of_pos (by positivity : (0 : ℝ) < 8 * r)] using sphere_subset_closedBall hz
      exact hbound z hz'
    have hjRaw := hfJ.sum_divisor_le (r := 5 * r) (R := 8 * r) (M := Real.exp M)
      (by positivity) (by rw [abs_of_pos (by positivity : 0 < 8 * r), abs_of_pos (by positivity : 0 < 5 * r)]; nlinarith [hr])
      (Real.one_le_exp hM.le) hf0 hB5
    have hj : (↑(∑ᶠ a, d₅ a) : ℝ) ≤
        Real.log (Real.exp M / ‖f 0‖) / Real.log ((8 * r) / (5 * r)) := by
      have hjRaw' := hjRaw
      rw [abs_of_pos (by positivity : (0 : ℝ) < 5 * r)] at hjRaw'
      simpa [d₅] using hjRaw'
    have hSsubset : S ⊆ T := by
      intro a ha
      obtain ⟨haBall, hpos⟩ := (hSmem a).1 ha
      have haClosed : a ∈ closedBall 0 (5 * r) := by
        rw [mem_ball_zero_iff] at haBall
        rw [mem_closedBall_zero_iff]
        nlinarith [haBall, hRupper]
      exact (hTmem a).2 ⟨haClosed, hpos⟩
    have hsumCompare : (∑ a ∈ S, (analyticOrderNatAt f a : ℝ)) ≤
        ∑ a ∈ T, (d₅ a : ℝ) := by
      calc
        _ = ∑ a ∈ S, (d₅ a : ℝ) := by
          apply Finset.sum_congr rfl
          intro a ha
          have haBall := (hSmem a).1 ha |>.1
          have haClosed : a ∈ closedBall 0 (5 * r) := by
            rw [mem_ball_zero_iff] at haBall
            rw [mem_closedBall_zero_iff]
            nlinarith [haBall, hRupper]
          have ha8 : a ∈ closedBall 0 (8 * r) := by
            rw [mem_closedBall_zero_iff] at haClosed ⊢
            nlinarith [haClosed, hr]
          have hdiv5 := divisor_eq_analyticOrderNatAt hf5 haClosed
          change (analyticOrderNatAt f a : ℝ) =
            ((MeromorphicOn.divisor f (closedBall 0 (5 * r)) a : ℤ) : ℝ)
          exact_mod_cast hdiv5.symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSsubset (by
          intro a ha _
          have haClosed := (hTmem a).1 ha |>.1
          have hdiv := divisor_eq_analyticOrderNatAt hf5 haClosed
          have hdiv' : ((MeromorphicOn.divisor f (closedBall 0 (5 * r)) a : ℤ) : ℝ) =
              (analyticOrderNatAt f a : ℝ) := by exact_mod_cast hdiv
          change 0 ≤ ((MeromorphicOn.divisor f (closedBall 0 (5 * r)) a : ℤ) : ℝ)
          rw [hdiv']
          positivity)
    have hsumCast : ∑ a ∈ T, (d₅ a : ℝ) = (∑ᶠ a, (d₅ a : ℝ)) := by
      symm
      apply finsum_eq_sum_of_support_subset (s := T)
      intro a ha
      by_contra hnot
      have hzero : d₅ a = 0 := by
        by_contra hne
        exact hnot (hTfinite.mem_toFinset.mpr hne)
      simp [Function.mem_support, hzero] at ha
    have hmap := map_finsum (Int.castRingHom ℝ)
      ((MeromorphicOn.divisor f (closedBall 0 (5 * r))).finiteSupport (isCompact_closedBall 0 (5 * r)))
    have hj' : (∑ᶠ a, (d₅ a : ℝ)) ≤ (Real.log (Real.exp M / ‖f 0‖) / Real.log ((8 * r) / (5 * r))) := by
      have hmap' : (∑ᶠ a, (d₅ a : ℝ)) = (↑(∑ᶠ a, d₅ a) : ℝ) := by
        simpa using hmap.symm
      rw [hmap']
      exact hj
    have hlog : Real.log (Real.exp M / ‖f 0‖) ≤ 2 * M := by
      have hpos : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
      have hinv : ‖f 0‖⁻¹ ≤ (Real.exp (-M))⁻¹ :=
        (inv_le_inv₀ hpos (Real.exp_pos _)).2 hcenter
      have hnorm : Real.exp M / ‖f 0‖ ≤ Real.exp M / Real.exp (-M) := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg M)
      calc
        Real.log (Real.exp M / ‖f 0‖) ≤ Real.log (Real.exp M / Real.exp (-M)) :=
          Real.log_le_log (div_pos (Real.exp_pos _) hpos) hnorm
        _ = 2 * M := by
          rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
          ring
    have hden : Real.log ((8 * r) / (5 * r)) = Real.log (8 / 5) := by
      congr 1 <;> field_simp
    have hlogden : 0 < Real.log (8 / 5) := Real.log_pos (by norm_num)
    have hlenReal : (Z.length : ℝ) = ∑ a ∈ S, (analyticOrderNatAt f a : ℝ) := by
      change ((multiplicityList S (analyticOrderNatAt f)).length : ℝ) = _
      rw [multiplicityList_length]
      simp [Nat.cast_sum]
    rw [hlenReal]
    calc
      (∑ a ∈ S, (analyticOrderNatAt f a : ℝ)) ≤ ∑ a ∈ T, (d₅ a : ℝ) := hsumCompare
      _ = ∑ᶠ a, (d₅ a : ℝ) := hsumCast
      _ ≤ Real.log (Real.exp M / ‖f 0‖) / Real.log (8 / 5) := by simpa [hden] using hj'
      _ ≤ 2 * M / Real.log (8 / 5) := div_le_div_of_nonneg_right hlog (le_of_lt hlogden)
  refine ⟨R, S, Z, hRlower, hRupper, hboundary, rfl, hSmem, hlen, ?_⟩
  intro ρ
  constructor
  · intro hρ
    obtain ⟨a, haS, haEq, hpos⟩ :=
      (mem_multiplicityList (s := S) (m := fun a ↦ analyticOrderNatAt f a) (a := ρ)).1
        (by simpa [Z] using hρ)
    subst ρ
    obtain ⟨haBall, hroot⟩ := (hSmem a).1 haS
    have haSmall : a ∈ closedBall 0 (5 * r) := by
      rw [mem_ball_zero_iff] at haBall
      rw [mem_closedBall_zero_iff]
      nlinarith [haBall, hRupper]
    exact ⟨(analyticOrderNatAt_pos_iff (hf5 a haSmall) (hfiniteOnSmall a haSmall)).mp hpos,
      (mem_ball_zero_iff.mp haBall)⟩
  · rintro ⟨hroot, hnorm⟩
    have haClosed : ρ ∈ closedBall 0 (5 * r) := by
      rw [mem_closedBall_zero_iff]
      nlinarith [hnorm, hRupper]
    have hpos := (analyticOrderNatAt_pos_iff (hf5 ρ haClosed) (hfiniteOnSmall ρ haClosed)).2 hroot
    have haS := (hSmem ρ).2 ⟨by
      rw [mem_ball_zero_iff]
      nlinarith [hnorm], hpos⟩
    exact (mem_multiplicityList (s := S) (m := fun a ↦ analyticOrderNatAt f a) (a := ρ)).2
      ⟨ρ, haS, rfl, hpos⟩

/-- The disk zero list comes with a zero-free analytic Blaschke quotient on the disk. -/
theorem disk_blaschke_factorization {r M : ℝ} (hr : 0 < r) (hM : 0 < M) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (8 * r)))
    (hbound : ∀ z ∈ closedBall 0 (8 * r), ‖f z‖ ≤ Real.exp M)
    (hcenter : Real.exp (-M) ≤ ‖f 0‖) :
    ∃ R : ℝ, ∃ S : Finset ℂ, ∃ Z : List ℂ, ∃ g : ℂ → ℂ,
      4 * r ≤ R ∧ R ≤ 5 * r ∧ (∀ z : ℂ, ‖z‖ = R → f z ≠ 0) ∧
      Z = multiplicityList S (analyticOrderNatAt f) ∧
      (∀ a, a ∈ S ↔ a ∈ ball (0 : ℂ) R ∧ 0 < analyticOrderNatAt f a) ∧
      (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) ∧
      (∀ ρ, ρ ∈ Z ↔ f ρ = 0 ∧ ‖ρ‖ < R) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      (∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ = ‖f z‖) ∧
      Real.exp (-M) ≤ ‖g 0‖ ∧
      f =ᶠ[Filter.codiscreteWithin (closedBall 0 R)]
        ((∏ a ∈ S, Complex.canonicalFactor R a ^
          (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a))) • g) := by
  classical
  obtain ⟨R, S, Z, hRlo, hRhi, hboundR, hZeq, hSmem, hlen, hZ⟩ :=
    disk_zero_list hr hM hf hbound hcenter
  have hclosedR : closedBall (0 : ℂ) R ⊆ closedBall 0 (8 * r) := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz ⊢
    nlinarith [hz, hRhi, hr]
  have hfR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := hf.mono hclosedR
  have hfRopen : AnalyticOnNhd ℂ f (ball (0 : ℂ) R) := hfR.mono ball_subset_closedBall
  have h0 : f 0 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hcenter)
  have hfiniteOnBall (z : ℂ) (hz : z ∈ ball (0 : ℂ) (8 * r)) : analyticOrderAt f z ≠ ⊤ := by
    intro htop
    have hvanish : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
    have hzero : EqOn f 0 (ball (0 : ℂ) (8 * r)) :=
      (hf.mono ball_subset_closedBall).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_ball hz hvanish
    have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) (8 * r) := Metric.mem_ball_self (by positivity)
    exact h0 (hzero hz0)
  have hfinite : ∀ u : closedBall (0 : ℂ) R, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    have hu8 : (u : ℂ) ∈ ball (0 : ℂ) (8 * r) := by
      rw [mem_ball_zero_iff]
      have huNorm : ‖(u : ℂ)‖ ≤ R := by
        simpa [dist_eq_norm] using (Metric.mem_closedBall.mp u.property)
      nlinarith [huNorm, hRhi, hr]
    have hOrder := hfiniteOnBall u hu8
    have hA := hfR u u.property
    simpa [hA.meromorphicOrderAt_eq] using hOrder
  obtain ⟨g, D⟩ := hfR.meromorphicOn.exists_ecanonicalDecomp hfinite
  have hSphereDiv (a : ℂ) : MeromorphicOn.divisor f (sphere (0 : ℂ) R) a = 0 := by
    by_cases ha : a ∈ sphere (0 : ℂ) R
    · have haNorm : ‖a‖ = R := by simpa [mem_sphere_zero_iff_norm] using ha
      have haClosed : a ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall ha
      have hfa := hboundR a haNorm
      have hnon : f a ≠ 0 := hboundR a haNorm
      have hOrder : analyticOrderAt f a = 0 := (hfR a haClosed).analyticOrderAt_eq_zero.mpr hnon
      rw [MeromorphicOn.divisor_apply (hfR.meromorphicOn.mono_set sphere_subset_closedBall) ha]
      have hmerOrder : meromorphicOrderAt f a = 0 := by
        rw [(hfR a haClosed).meromorphicOrderAt_eq]
        simp [hOrder]
      rw [hmerOrder]
      simp
    · exact (MeromorphicOn.divisor f (sphere (0 : ℂ) R)).apply_eq_zero_of_notMem ha
  have hdivFin : (MeromorphicOn.divisor f (ball (0 : ℂ) R)).support.Finite :=
    hfR.meromorphicOn.divisor_ball_support_finite
  have hfinprod :
      (∏ᶠ a : ℂ, Complex.canonicalFactor R a ^
        (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a))) =
        ∏ a ∈ S, Complex.canonicalFactor R a ^
          (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a)) := by
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro a ha
    have hda : MeromorphicOn.divisor f (ball (0 : ℂ) R) a ≠ 0 := by
      by_contra hzero
      apply ha
      simp [hzero]
    have haBall : a ∈ ball (0 : ℂ) R :=
      (MeromorphicOn.divisor f (ball (0 : ℂ) R)).supportWithinDomain hda
    have hdiv := divisor_eq_analyticOrderNatAt hfRopen haBall
    have hmn : analyticOrderNatAt f a ≠ 0 := by
      intro hzero
      apply hda
      rw [hdiv, hzero]
      simp
    exact (hSmem a).2 ⟨haBall, Nat.pos_of_ne_zero hmn⟩
  have hfinprodInv :
      (∏ᶠ a : ℂ, (Complex.canonicalFactor R a ^
        (MeromorphicOn.divisor f (ball (0 : ℂ) R) a))⁻¹) =
        ∏ a ∈ S, Complex.canonicalFactor R a ^
          (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a)) := by
    calc
      _ = ∏ᶠ a : ℂ, Complex.canonicalFactor R a ^
          (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a)) :=
        finprod_congr fun a ↦ by rw [zpow_neg]
      _ = _ := hfinprod
  have hfg : f =ᶠ[Filter.codiscreteWithin (closedBall (0 : ℂ) R)]
      ((∏ a ∈ S, Complex.canonicalFactor R a ^
        (-(MeromorphicOn.divisor f (ball (0 : ℂ) R) a))) • g) := by
    simpa [hSphereDiv, hfinprodInv] using D.eventuallyEq
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : 0 < 4 * r) hRlo
  have hcenterClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff]
    simpa using hRpos.le
  have hfRopen : AnalyticOnNhd ℂ f (ball (0 : ℂ) R) := hfR.mono ball_subset_closedBall
  have hinnerTerm (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) (a : ℂ) :
      MeromorphicOn.divisor f (ball (0 : ℂ) R) a * Real.log ‖Complex.canonicalFactor R a w‖ = 0 := by
    by_cases ha : a ∈ ball (0 : ℂ) R
    · rw [Complex.norm_canonicalFactor_eval_circle_eq_one ha hw]
      simp
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
        (MeromorphicOn.divisor f (ball (0 : ℂ) R)) ha]
      simp
  have hSphereTerm (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) :
      (∑ᶠ a, MeromorphicOn.divisor f (ball (0 : ℂ) R) a *
        Real.log ‖Complex.canonicalFactor R a w‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    exact hinnerTerm w hw
  have houterTerm (w : ℂ) :
      (∑ᶠ a, (MeromorphicOn.divisor f (sphere (0 : ℂ) R) a : ℝ) *
        Real.log ‖w - a‖) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro a
    simp [hSphereDiv]
  have hlogNormEq (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) :
      Real.log ‖g w‖ = Real.log ‖f w‖ := by
    have hwClosed : w ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hw
    have hfw : f w ≠ 0 := by
      have hwNorm : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
      exact hboundR w hwNorm
    have horder : meromorphicOrderAt f w = 0 := by
      rw [(hfR w hwClosed).meromorphicOrderAt_eq]
      have hOrder : analyticOrderAt f w = 0 := (hfR w hwClosed).analyticOrderAt_eq_zero.mpr hfw
      simp [hOrder]
    have hlog := D.log_norm_eq hwClosed horder hRpos
    rw [hSphereTerm w hw, houterTerm w] at hlog
    have htail := (hfR w hwClosed).meromorphicTrailingCoeffAt_of_ne_zero hfw
    rw [htail] at hlog
    simpa using hlog
  have hboundaryNorm (w : ℂ) (hw : w ∈ sphere (0 : ℂ) R) : ‖g w‖ = ‖f w‖ := by
    have hwClosed : w ∈ closedBall (0 : ℂ) R := sphere_subset_closedBall hw
    have hfw := hboundR w (by simpa [Metric.mem_sphere, dist_eq_norm] using hw)
    have hgpos : 0 < ‖g w‖ := norm_pos_iff.mpr (D.ne_zero w hwClosed)
    have hfpos : 0 < ‖f w‖ := norm_pos_iff.mpr hfw
    have hlog := hlogNormEq w hw
    calc
      ‖g w‖ = Real.exp (Real.log ‖g w‖) := (Real.exp_log hgpos).symm
      _ = Real.exp (Real.log ‖f w‖) := by rw [hlog]
      _ = ‖f w‖ := Real.exp_log hfpos
  have hcenterTerm (a : ℂ) :
      0 ≤ (MeromorphicOn.divisor f (ball (0 : ℂ) R) a : ℝ) *
        Real.log ‖Complex.canonicalFactor R a 0‖ := by
    by_cases ha : a ∈ ball (0 : ℂ) R
    · have hdiv := divisor_eq_analyticOrderNatAt hfRopen ha
      have hcoef : 0 ≤ (MeromorphicOn.divisor f (ball (0 : ℂ) R) a : ℝ) := by
        rw [hdiv]
        exact_mod_cast (Nat.zero_le (analyticOrderNatAt f a))
      by_cases ha0 : a = 0
      · subst a
        simp [Complex.canonicalFactor_apply_self]
      · have hnormB : ‖Complex.canonicalFactor R a 0‖ = R / ‖a‖ := by
          rw [Complex.canonicalFactor_apply]
          simp only [mul_zero, sub_zero, norm_div, norm_pow, norm_real, Real.norm_eq_abs,
            abs_of_pos hRpos, norm_mul, zero_sub, norm_neg]
          field_simp [ha0, hRpos.ne']
        have haNorm : ‖a‖ < R := by simpa [mem_ball_zero_iff] using ha
        have hlarge : 1 ≤ ‖Complex.canonicalFactor R a 0‖ := by
          rw [hnormB]
          exact (le_div_iff₀ (norm_pos_iff.mpr ha0)).2 (by linarith)
        exact mul_nonneg hcoef (Real.log_nonneg hlarge)
    · have hzero : MeromorphicOn.divisor f (ball (0 : ℂ) R) a = 0 :=
        (MeromorphicOn.divisor f (ball (0 : ℂ) R)).apply_eq_zero_of_notMem ha
      simp [hzero]
  have hcenterSumSupport :
      (Function.support fun a : ℂ ↦
        (MeromorphicOn.divisor f (ball (0 : ℂ) R) a : ℝ) *
          Real.log ‖Complex.canonicalFactor R a 0‖) ⊆ S := by
    intro a ha
    by_contra hnot
    have hd0 : MeromorphicOn.divisor f (ball (0 : ℂ) R) a = 0 := by
      by_cases haBall : a ∈ ball (0 : ℂ) R
      · have hdiv := divisor_eq_analyticOrderNatAt hfRopen haBall
        by_cases hpos : 0 < analyticOrderNatAt f a
        · exact False.elim (hnot ((hSmem a).2 ⟨haBall, hpos⟩))
        · have hzero : analyticOrderNatAt f a = 0 := Nat.eq_zero_of_not_pos hpos
          rw [hdiv, hzero]
          rfl
      · exact (MeromorphicOn.divisor f (ball (0 : ℂ) R)).apply_eq_zero_of_notMem haBall
    simp [Function.mem_support, hd0] at ha
  have hcenterSum :
      0 ≤ ∑ᶠ a, (MeromorphicOn.divisor f (ball (0 : ℂ) R) a : ℝ) *
        Real.log ‖Complex.canonicalFactor R a 0‖ := by
    rw [finsum_eq_sum_of_support_subset _ hcenterSumSupport]
    exact Finset.sum_nonneg fun a ha ↦ hcenterTerm a
  have hzeroOrderAtCenter : meromorphicOrderAt f (0 : ℂ) = 0 := by
    rw [(hfR 0 hcenterClosed).meromorphicOrderAt_eq]
    have hOrder : analyticOrderAt f 0 = 0 := (hfR 0 hcenterClosed).analyticOrderAt_eq_zero.mpr h0
    simp [hOrder]
  have hlogCenter := D.log_norm_eq hcenterClosed hzeroOrderAtCenter hRpos
  rw [houterTerm 0] at hlogCenter
  have htail0 := (hfR 0 hcenterClosed).meromorphicTrailingCoeffAt_of_ne_zero h0
  rw [htail0] at hlogCenter
  have hlogfCenter : -M ≤ Real.log ‖f 0‖ := by
    simpa using Real.log_le_log (Real.exp_pos _) hcenter
  have hloggCenter : -M ≤ Real.log ‖g 0‖ := by linarith [hlogCenter, hlogfCenter]
  have hg0pos : 0 < ‖g 0‖ := norm_pos_iff.mpr (D.ne_zero 0 hcenterClosed)
  have hcenterG : Real.exp (-M) ≤ ‖g 0‖ := by
    calc
      Real.exp (-M) ≤ Real.exp (Real.log ‖g 0‖) := Real.exp_le_exp.mpr hloggCenter
      _ = ‖g 0‖ := Real.exp_log hg0pos
  refine ⟨R, S, Z, g, hRlo, hRhi, hboundR, hZeq, hSmem, hlen, hZ,
    D.analyticOnNhd, D.ne_zero, hboundaryNorm, hcenterG, hfg⟩

/-- A bounded zero-free analytic function on a disk has a controlled logarithmic derivative
on its concentric half disk. -/
theorem logDeriv_bound_of_zero_free_disk {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0 < R) (hM : 0 < M)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hn : ∀ z ∈ ball 0 R, f z ≠ 0)
    (hb : ∀ z ∈ ball 0 R, ‖f z‖ ≤ Real.exp M)
    (h0 : Real.exp (-M) ≤ ‖f 0‖)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖deriv f z / f z‖ ≤ 100 * (M + 1) / R := by
  let k : ℂ → ℂ := fun w ↦ deriv f w / f w
  have hfa : AnalyticOnNhd ℂ f (ball 0 R) := hf.analyticOnNhd isOpen_ball
  have hk : DifferentiableOn ℂ k (ball 0 R) := by
    dsimp [k]
    exact hfa.deriv.differentiableOn.div hf hn
  obtain ⟨G, hG⟩ := hk.isExactOn_ball
  let F : ℂ → ℂ := fun w ↦ G w - G 0
  have hF' (w : ℂ) (hw : w ∈ ball 0 R) : HasDerivAt F (k w) w := by
    dsimp [F]
    exact (hG w hw).sub_const (G 0)
  have hF0 : F 0 = 0 := by simp [F]
  have hFd : DifferentiableOn ℂ F (ball 0 R) := by
    intro w hw
    exact (hF' w hw).differentiableAt.differentiableWithinAt
  let H : ℂ → ℂ := fun w ↦ f w * Complex.exp (-F w)
  have hHd : DifferentiableOn ℂ H (ball 0 R) := by
    intro w hw
    have hFw : DifferentiableAt ℂ F w := (hFd w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hExpAt : DifferentiableAt ℂ (fun v : ℂ ↦ Complex.exp (-F v)) w :=
      (Complex.differentiable_exp (-F w)).comp w hFw.neg
    exact (((hf w hw).differentiableAt (isOpen_ball.mem_nhds hw)).mul hExpAt).differentiableWithinAt
  have hHderiv (w : ℂ) (hw : w ∈ ball 0 R) : deriv H w = 0 := by
    have hfw := (hf w hw).differentiableAt (isOpen_ball.mem_nhds hw)
    have hFw := hF' w hw
    have hExp : HasDerivAt (fun v : ℂ ↦ Complex.exp (-F v))
        (Complex.exp (-F w) * -k w) w := by
      simpa [Function.comp_def, mul_comm] using (hasDerivAt_exp (-F w)).comp w hFw.neg
    have hmul := hfw.hasDerivAt.mul hExp
    have hmul' : deriv H w = deriv f w * Complex.exp (-F w) +
        f w * (Complex.exp (-F w) * -k w) := by
      calc
        deriv H w = deriv (f * fun v : ℂ ↦ Complex.exp (-F v)) w := rfl
        _ = _ := hmul.deriv
    rw [hmul']
    dsimp [k]
    field_simp [hn w hw]
    ring
  have hHconst : H z = H 0 :=
    isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball hHd (x := z) (y := 0)
      (fun w hw ↦ hHderiv w hw) (by
        have hzR : ‖z‖ < R := by nlinarith
        simpa [mem_ball_zero_iff] using hzR) (by simpa [mem_ball_zero_iff] using hR)
  have hrel : f z * Complex.exp (-F z) = f 0 := by
    simpa [H, hF0] using hHconst
  have hnorm : ‖f z‖ * Real.exp (-(F z).re) = ‖f 0‖ := by
    calc
      ‖f z‖ * Real.exp (-(F z).re) = ‖f z‖ * ‖Complex.exp (-F z)‖ := by
        congr 1
        simp [Complex.norm_exp]
      _ = ‖f z * Complex.exp (-F z)‖ := by rw [norm_mul]
      _ = ‖f 0‖ := by rw [hrel]
  have hnormmul : ‖f z‖ = ‖f 0‖ * Real.exp (F z).re := by
    have hexp : Real.exp (-(F z).re) * Real.exp (F z).re = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      ‖f z‖ = ‖f z‖ * (Real.exp (-(F z).re) * Real.exp (F z).re) := by rw [hexp, mul_one]
      _ = (‖f z‖ * Real.exp (-(F z).re)) * Real.exp (F z).re := by ring
      _ = ‖f 0‖ * Real.exp (F z).re := by rw [hnorm]
  have hzR : z ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    nlinarith
  have hlogz : Real.log ‖f z‖ ≤ M := by
    calc
      Real.log ‖f z‖ ≤ Real.log (Real.exp M) :=
        Real.log_le_log (norm_pos_iff.mpr (hn z hzR)) (hb z hzR)
      _ = M := Real.log_exp M
  have hlog0 : -M ≤ Real.log ‖f 0‖ := by
    simpa using Real.log_le_log (Real.exp_pos _) h0
  have hlogmul : Real.log ‖f z‖ = Real.log ‖f 0‖ + (F z).re := by
    rw [hnormmul, Real.log_mul (ne_of_gt (norm_pos_iff.mpr
      (hn 0 (by simpa [mem_ball_zero_iff] using hR)))) (Real.exp_ne_zero _), Real.log_exp]
  have hReF (w : ℂ) (hw : w ∈ ball 0 R) : (F w).re ≤ 2 * M := by
    have hw' : ‖w‖ < R := by simpa [mem_ball_zero_iff] using hw
    have hwbound := hb w hw
    have hwpos : 0 < ‖f w‖ := norm_pos_iff.mpr (hn w hw)
    have hwlog : Real.log ‖f w‖ ≤ M := by
      calc
        Real.log ‖f w‖ ≤ Real.log (Real.exp M) := Real.log_le_log hwpos hwbound
        _ = M := Real.log_exp M
    have hwmul : ‖f w‖ = ‖f 0‖ * Real.exp (F w).re := by
      have hrelw : f w * Complex.exp (-F w) = f 0 := by
        have hconstw := isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball hHd
          (x := w) (y := 0)
          (fun u hu ↦ hHderiv u hu) (by simpa [mem_ball_zero_iff] using hw')
          (by simpa [mem_ball_zero_iff] using hR)
        simpa [H, hF0] using hconstw
      have hnormw : ‖f w‖ * Real.exp (-(F w).re) = ‖f 0‖ := by
        calc
          ‖f w‖ * Real.exp (-(F w).re) = ‖f w‖ * ‖Complex.exp (-F w)‖ := by
            congr 1
            simp [Complex.norm_exp]
          _ = ‖f w * Complex.exp (-F w)‖ := by rw [norm_mul]
          _ = ‖f 0‖ := by rw [hrelw]
      have hexpw : Real.exp (-(F w).re) * Real.exp (F w).re = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        ‖f w‖ = ‖f w‖ * (Real.exp (-(F w).re) * Real.exp (F w).re) := by
          rw [hexpw, mul_one]
        _ = (‖f w‖ * Real.exp (-(F w).re)) * Real.exp (F w).re := by ring
        _ = ‖f 0‖ * Real.exp (F w).re := by rw [hnormw]
    have hlogmulw : Real.log ‖f w‖ = Real.log ‖f 0‖ + (F w).re := by
      rw [hwmul, Real.log_mul (ne_of_gt (norm_pos_iff.mpr
        (hn 0 (by simpa [mem_ball_zero_iff] using hR)))) (Real.exp_ne_zero _), Real.log_exp]
    linarith [hlog0, hlogmulw, hwlog]
  have hBC (w : ℂ) (hw : w ∈ ball 0 (3 * R / 4)) : ‖F w‖ ≤ 12 * M := by
    have hw0 : ‖w‖ < 3 * R / 4 := by simpa [mem_ball_zero_iff] using hw
    have hwR : w ∈ ball 0 R := by
      rw [mem_ball_zero_iff]
      linarith [hw0, hR]
    have hbc := Complex.borelCaratheodory_zero (M := 2 * M) (f := F)
      (by positivity) hFd hReF hR hwR hF0
    have hden : 0 < R - ‖w‖ := by linarith
    have hbc' : ‖F w‖ ≤ (4 * M * ‖w‖) / (R - ‖w‖) := by
      simpa only [show 2 * (2 * M) = 4 * M by ring] using hbc
    calc
      ‖F w‖ ≤ (4 * M * ‖w‖) / (R - ‖w‖) := hbc'
      _ ≤ 12 * M := (div_le_iff₀ hden).2 (by
        calc
          4 * M * ‖w‖ ≤ 3 * M * R := by nlinarith [hw0, hM]
          _ ≤ 12 * M * (R - ‖w‖) := by nlinarith [hw0, hR, hM])
  have hball : closedBall z (R / 8) ⊆ ball 0 R := by
    intro w hw
    rw [mem_ball_zero_iff]
    have hdist : dist w z ≤ R / 8 := by simpa using hw
    have hnormw : ‖w‖ ≤ 5 * R / 8 := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by congr 1 <;> ring
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
        _ ≤ R / 8 + R / 2 := add_le_add hdist hz
        _ = 5 * R / 8 := by ring
    nlinarith [hR]
  have hFclosed : DifferentiableOn ℂ F (closure (ball z (R / 8))) :=
    hFd.mono ((closure_minimal ball_subset_closedBall isClosed_closedBall).trans hball)
  have hρ : 0 < R / 8 := by positivity
  have hFderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := F) (c := z) (R := R / 8) (C := 12 * M) hρ hFclosed.diffContOnCl
    (fun w hw ↦ hBC w (by
      rw [mem_ball_zero_iff]
      have hdist : dist w z = R / 8 := Metric.mem_sphere.mp hw
      have hnormw : ‖w‖ ≤ 5 * R / 8 := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by congr 1 <;> ring
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = dist w z + ‖z‖ := by rw [dist_eq_norm]
          _ = R / 8 + ‖z‖ := by rw [hdist]
          _ ≤ 5 * R / 8 := by nlinarith [hz]
      have : 5 * R / 8 < 3 * R / 4 := by nlinarith [hR]
      exact hnormw.trans_lt this))
  have hFderivEq : deriv F z = k z := (hF' z hzR).deriv
  calc
    ‖deriv f z / f z‖ = ‖deriv F z‖ := by rw [hFderivEq]
    _ ≤ (12 * M) / (R / 8) := hFderiv
    _ = 96 * M / R := by field_simp <;> ring
    _ ≤ 100 * (M + 1) / R := by
      apply (div_le_div_iff₀ hR hR).2
      nlinarith [hM]

theorem disk_blaschke_logDeriv_formula {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 (8 * r)))
    (hbound : ∀ z ∈ closedBall 0 (8 * r), ‖f z‖ ≤ Real.exp M)
    (hcenter : Real.exp (-M) ≤ ‖f 0‖) :
    ∃ R : ℝ, ∃ S : Finset ℂ, ∃ Z : List ℂ, ∃ g : ℂ → ℂ,
      4 * r ≤ R ∧ R ≤ 5 * r ∧
      (∀ z : ℂ, ‖z‖ = R → f z ≠ 0) ∧
      (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) ∧
      (∀ ρ ∈ Z, f ρ = 0 ∧ ‖ρ‖ < R) ∧
      (∀ ρ, f ρ = 0 → ‖ρ‖ < R → ρ ∈ Z) ∧
      AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, g z ≠ 0) ∧
      (∀ z ∈ sphere (0 : ℂ) R, ‖g z‖ = ‖f z‖) ∧
      Real.exp (-M) ≤ ‖g 0‖ ∧
      (∀ z : ℂ, ‖z‖ ≤ 2 * r → f z ≠ 0 →
        logDeriv f z - (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum =
          logDeriv g z + (Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum) := by
  classical
  obtain ⟨R, S, Z, g, hRlo, hRhi, hboundary, hZeq, hSmem, hlen, hZ,
    hg, hg0, hboundaryNorm, hcenterG, hfg⟩ :=
      disk_blaschke_factorization hr hM hf hbound hcenter
  let d : ℂ → ℤ := MeromorphicOn.divisor f (ball (0 : ℂ) R)
  let F : ℂ → (ℂ → ℂ) := fun a ↦ Complex.canonicalFactor R a ^ (-d a)
  let Pfun : ℂ → ℂ := ∏ a ∈ S, F a
  let P : ℂ → ℂ := fun w ↦ ∏ a ∈ S, F a w
  have hPfun : Pfun = P := by
    ext w
    simp [P, Pfun, Finset.prod_apply]
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * r) hRlo
  have hRhalf : 0 < R / 2 := by positivity
  have hclosedR : closedBall (0 : ℂ) R ⊆ closedBall (0 : ℂ) (8 * r) := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw ⊢
    nlinarith [hw, hRhi, hr]
  have hfR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := hf.mono hclosedR
  have hfg' : f =ᶠ[Filter.codiscreteWithin (ball (0 : ℂ) R)]
      (P • g) := by
    have hle : Filter.codiscreteWithin (ball (0 : ℂ) R) ≤
        Filter.codiscreteWithin (closedBall (0 : ℂ) R) :=
      Filter.codiscreteWithin_mono (s₁ := ball (0 : ℂ) R)
        (s := closedBall (0 : ℂ) R) (show ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) R from ball_subset_closedBall)
    have hfg₁ := Filter.EventuallyEq.filter_mono hfg hle
    have hfg₂ : f =ᶠ[Filter.codiscreteWithin (ball (0 : ℂ) R)] (Pfun • g) := by
      simpa only [Pfun, F, d] using hfg₁
    simpa only [hPfun] using hfg₂
  have hFmer (a : ℂ) : MeromorphicOn (F a) (ball (0 : ℂ) R) := by
    change MeromorphicOn (Complex.canonicalFactor R a ^ (-d a)) (ball (0 : ℂ) R)
    exact ((meromorphicOn_univ.mpr (Complex.meromorphic_canonicalFactor R a)).mono_set
      (by intro w hw; trivial)).zpow _
  have hPmer : MeromorphicOn P (ball (0 : ℂ) R) := by
    exact MeromorphicOn.fun_prod (fun a ha ↦ hFmer a)
  have hgmer : MeromorphicOn g (ball (0 : ℂ) R) :=
    hg.meromorphicOn.mono_set ball_subset_closedBall
  have hpgmer : MeromorphicOn (P • g) (ball (0 : ℂ) R) := hPmer.smul hgmer
  have hsmallClosed (z : ℂ) (hz : ‖z‖ ≤ 2 * r) : z ∈ closedBall (0 : ℂ) (8 * r) := by
    rw [mem_closedBall_zero_iff]
    nlinarith [hz, hr]
  have hlocal (z : ℂ) (hz : ‖z‖ ≤ 2 * r) (hfz : f z ≠ 0) :
      logDeriv f z - (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum =
        logDeriv g z + (Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum := by
    have hzball : z ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]
      nlinarith [hz, hRlo, hr]
    have hzclosed : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hzball
    have hroot (a : ℂ) (ha : a ∈ S) : f a = 0 := by
      have hpos := (hSmem a).1 ha |>.2
      have hmem : a ∈ Z := by
        rw [hZeq]
        exact (mem_multiplicityList (s := S) (m := fun a ↦ analyticOrderNatAt f a)).2
          ⟨a, ha, rfl, hpos⟩
      exact ((hZ a).1 hmem).1
    have hza (a : ℂ) (ha : a ∈ S) : z ≠ a := by
      intro heq
      subst z
      exact hfz (hroot a ha)
    have hfactorAnalytic (a : ℂ) (ha : a ∈ S) :
        AnalyticAt ℂ (F a) z := by
      have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
      have hcf : AnalyticAt ℂ (Complex.canonicalFactor R a) z :=
        Complex.analyticOnNhd_canonicalFactor R a z (hza a ha)
      have hcfne : Complex.canonicalFactor R a z ≠ 0 :=
        Complex.canonicalFactor_ne_zero haBall hzclosed (hza a ha)
      change AnalyticAt ℂ (Complex.canonicalFactor R a ^ (-d a)) z
      exact hcf.zpow hcfne
    have hPanalytic : AnalyticAt ℂ P z := by
      exact S.analyticAt_fun_prod hfactorAnalytic
    have hPne : P z ≠ 0 := by
      dsimp [P]
      apply Finset.prod_ne_zero_iff.mpr
      intro a ha
      have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
      have hcfne : Complex.canonicalFactor R a z ≠ 0 :=
        Complex.canonicalFactor_ne_zero haBall hzclosed (hza a ha)
      exact zpow_ne_zero (-d a) hcfne
    have hfa : AnalyticAt ℂ f z := hf z (hsmallClosed z hz)
    have hga : AnalyticAt ℂ g z := hg z hzclosed
    have hpga : AnalyticAt ℂ (P • g) z := by
      change AnalyticAt ℂ (fun w ↦ P w * g w) z
      exact hPanalytic.mul hga
    have hpgne : P z * g z ≠ 0 := mul_ne_zero hPne (hg0 z hzclosed)
    have hlogfg := logDeriv_eq_of_meromorphic_codiscreteWithin isOpen_ball
      (hfR.meromorphicOn.mono_set ball_subset_closedBall) hpgmer
      hfa hpga hzball hfz hpgne hfg'
    have hlogmul : logDeriv (P • g) z = logDeriv P z + logDeriv g z := by
      change logDeriv (P * g) z = logDeriv P z + logDeriv g z
      exact logDeriv_mul z hPne (hg0 z hzclosed)
        hPanalytic.differentiableAt hga.differentiableAt
    have hlogP : logDeriv P z =
        ∑ a ∈ S, ((-d a : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R a) z := by
      rw [hPfun.symm]
      change logDeriv (∏ a ∈ S, F a) z = _
      rw [logDeriv_prod]
      · apply Finset.sum_congr rfl
        intro a ha
        have hcfA : AnalyticAt ℂ (Complex.canonicalFactor R a) z :=
          Complex.analyticOnNhd_canonicalFactor R a z (hza a ha)
        have hcfne : Complex.canonicalFactor R a z ≠ 0 := by
          have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
          exact Complex.canonicalFactor_ne_zero haBall hzclosed (hza a ha)
        change logDeriv (Complex.canonicalFactor R a ^ (-d a)) z = _
        exact logDeriv_fun_zpow hcfA.differentiableAt (-d a)
      · intro a ha
        have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
        have hcfne : Complex.canonicalFactor R a z ≠ 0 :=
          Complex.canonicalFactor_ne_zero haBall hzclosed (hza a ha)
        exact zpow_ne_zero (-d a) hcfne
      · intro a ha
        exact (hfactorAnalytic a ha).differentiableAt
    have hnum (a : ℂ) (ha : a ∈ S) : (R : ℂ) ^ 2 - conj a * z ≠ 0 := by
      have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
      have haNorm : ‖a‖ < R := by simpa [mem_ball_zero_iff] using haBall
      have hzRhalf : ‖z‖ ≤ R / 2 := by nlinarith [hz, hRlo]
      have hprod : ‖a‖ * ‖z‖ ≤ R ^ 2 / 2 := by
        calc
          ‖a‖ * ‖z‖ ≤ R * (R / 2) :=
            mul_le_mul (le_of_lt haNorm) hzRhalf (norm_nonneg z) (le_of_lt hRpos)
          _ = R ^ 2 / 2 := by ring
      have hnsmall : ‖conj a * z‖ < R ^ 2 := by
        rw [norm_mul, norm_conj]
        nlinarith [hprod, hRpos]
      intro hzero
      have hcastEq : (R : ℂ) ^ 2 = conj a * z := sub_eq_zero.mp hzero
      have hnormEq : ‖(R : ℂ) ^ 2‖ = ‖conj a * z‖ := by rw [hcastEq]
      rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hRpos] at hnormEq
      exact (ne_of_lt hnsmall) hnormEq.symm
    have hcfLog (a : ℂ) (ha : a ∈ S) :
        logDeriv (Complex.canonicalFactor R a) z =
          -conj a / ((R : ℂ) ^ 2 - conj a * z) - 1 / (z - a) := by
      rw [logDeriv_apply]
      exact logDeriv_canonicalFactor hRpos (hza a ha) (hnum a ha)
    have hterms (a : ℂ) (ha : a ∈ S) :
        ((-d a : ℤ) : ℂ) * logDeriv (Complex.canonicalFactor R a) z =
          (analyticOrderNatAt f a : ℂ) *
            (conj a / ((R : ℂ) ^ 2 - conj a * z) + 1 / (z - a)) := by
      rw [hcfLog a ha]
      have haBall : a ∈ ball (0 : ℂ) R := (hSmem a).1 ha |>.1
      have hdiv : d a = (analyticOrderNatAt f a : ℤ) := by
        exact divisor_eq_analyticOrderNatAt (hfR.mono ball_subset_closedBall) haBall
      rw [hdiv]
      push_cast
      ring
    have hlogP' : logDeriv P z =
        (∑ a ∈ S, (analyticOrderNatAt f a : ℂ) *
          (conj a / ((R : ℂ) ^ 2 - conj a * z))) +
        (∑ a ∈ S, (analyticOrderNatAt f a : ℂ) * (1 / (z - a))) := by
      calc
        logDeriv P z = ∑ a ∈ S, (analyticOrderNatAt f a : ℂ) *
            (conj a / ((R : ℂ) ^ 2 - conj a * z) + 1 / (z - a)) := by
          rw [hlogP]
          apply Finset.sum_congr rfl
          intro a ha
          exact hterms a ha
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    have hlistPole : (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum =
        ∑ a ∈ S, (analyticOrderNatAt f a : ℂ) * (1 / (z - a)) := by
      rw [hZeq, multiplicityList_sum_map]
      simp [nsmul_eq_mul]
    have hlistCorr : (Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum =
        ∑ a ∈ S, (analyticOrderNatAt f a : ℂ) *
          (conj a / ((R : ℂ) ^ 2 - conj a * z)) := by
      rw [hZeq, multiplicityList_sum_map]
      simp [nsmul_eq_mul]
    rw [hlogfg, hlogmul, hlogP', hlistPole, hlistCorr]
    ring
  refine ⟨R, S, Z, g, hRlo, hRhi, hboundary, hlen, ?_, ?_, hg, hg0,
    hboundaryNorm, hcenterG, hlocal⟩
  · intro ρ hρ
    exact hZ ρ |>.1 hρ
  · intro ρ hroot hnorm
    exact (hZ ρ).2 ⟨hroot, hnorm⟩

theorem norm_sum_map_le_length {α : Type*} (l : List α) (g : α → ℂ) (K : ℝ)
    (hbound : ∀ a ∈ l, ‖g a‖ ≤ K) :
    ‖(l.map g).sum‖ ≤ (l.length : ℝ) * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hbound a (by simp)
    have htail : ∀ b ∈ l, ‖g b‖ ≤ K := fun b hb ↦ hbound b (by simp [hb])
    have hsum := ih htail
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      ‖g a + (l.map g).sum‖ ≤ ‖g a‖ + ‖(l.map g).sum‖ := norm_add_le _ _
      _ ≤ K + (l.length : ℝ) * K := add_le_add ha hsum
      _ = ((l.length : ℝ) + 1) * K := by ring

theorem riemannZeta₀_norm_bound_near_one :
    ∀ᶠ r : ℝ in 𝓝 0,
      ‖riemannZeta₀ (1 + (r : ℂ))‖ ≤ ‖riemannZeta₀ 1‖ + 1 := by
  have hlin : ContinuousAt (fun r : ℝ ↦ (1 : ℂ) + (r : ℂ)) 0 := by fun_prop
  have hlim : Tendsto (fun r : ℝ ↦ riemannZeta₀ (1 + (r : ℂ))) (𝓝 0)
      (𝓝 (riemannZeta₀ 1)) :=
    by simpa [Function.comp_def] using
      ((differentiable_riemannZeta₀.continuous.continuousAt).comp hlin).tendsto
  have hnear : ∀ᶠ r : ℝ in 𝓝 0,
      dist (riemannZeta₀ (1 + (r : ℂ))) (riemannZeta₀ 1) < 1 :=
    hlim.eventually (Metric.ball_mem_nhds _ (by norm_num))
  filter_upwards [hnear] with r hr
  have hnorm := norm_sub_norm_le (riemannZeta₀ (1 + (r : ℂ))) (riemannZeta₀ 1)
  rw [dist_eq_norm] at hr
  linarith

theorem disk_local_logderiv_bound {r M : ℝ} (hr : 0 < r) (hM : 0 < M)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 (8 * r)))
    (hbound : ∀ z ∈ closedBall 0 (8 * r), ‖f z‖ ≤ Real.exp M)
    (hcenter : Real.exp (-M) ≤ ‖f 0‖) :
    ∃ R : ℝ, ∃ Z : List ℂ,
      4 * r ≤ R ∧ R ≤ 5 * r ∧
      (∀ z : ℂ, ‖z‖ = R → f z ≠ 0) ∧
      (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) ∧
      (∀ ρ ∈ Z, f ρ = 0 ∧ ‖ρ‖ < R) ∧
      (∀ ρ, f ρ = 0 → ‖ρ‖ < R → ρ ∈ Z) ∧
      (∀ z : ℂ, ‖z‖ ≤ 2 * r → f z ≠ 0 →
        ‖logDeriv f z - (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum‖ ≤
          100 * (M + 1) / R + 2 * (Z.length : ℝ) / R) := by
  classical
  obtain ⟨R, S, Z, g, hRlo, hRhi, hboundary, hlen, hZ, hZcomplete, hg, hg0,
    hboundaryNorm, hcenterG, hformula⟩ :=
      disk_blaschke_logDeriv_formula hr hM hf hbound hcenter
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * r) hRlo
  have hgDiff : DifferentiableOn ℂ g (closedBall (0 : ℂ) R) := by
    intro w hw
    exact (hg w hw).differentiableAt.differentiableWithinAt
  have hgFrontier (w : ℂ) (hw : w ∈ frontier (ball (0 : ℂ) R)) :
      ‖g w‖ ≤ Real.exp M := by
    have hwSphere : w ∈ sphere (0 : ℂ) R := by
      rw [frontier_ball (0 : ℂ) hRpos.ne'] at hw
      exact hw
    have hwNorm : ‖w‖ = R := by
      simpa [mem_sphere_zero_iff_norm] using hwSphere
    have hwOuter : w ∈ closedBall (0 : ℂ) (8 * r) := by
      rw [mem_closedBall_zero_iff, hwNorm]
      nlinarith [hRhi, hr]
    calc
      ‖g w‖ = ‖f w‖ := hboundaryNorm w hwSphere
      _ ≤ Real.exp M := hbound w hwOuter
  have hgBound (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : ‖g w‖ ≤ Real.exp M :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hgDiff.diffContOnCl_ball subset_rfl) hgFrontier (subset_closure hw)
  have hgDiffBall : DifferentiableOn ℂ g (ball (0 : ℂ) R) :=
    hgDiff.mono ball_subset_closedBall
  have hcorrTerm (z : ℂ) (hz : ‖z‖ ≤ 2 * r) (ρ : ℂ) (hρ : ρ ∈ Z) :
      ‖conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)‖ ≤ 2 / R := by
    have hρNorm : ‖ρ‖ < R := (hZ ρ hρ).2
    have hzRhalf : ‖z‖ ≤ R / 2 := by nlinarith [hz, hRlo]
    have hprod : ‖ρ‖ * ‖z‖ ≤ R ^ 2 / 2 := by
      calc
        ‖ρ‖ * ‖z‖ ≤ R * (R / 2) :=
          mul_le_mul (le_of_lt hρNorm) hzRhalf (norm_nonneg z) hRpos.le
        _ = R ^ 2 / 2 := by ring
    have hsmall : ‖conj ρ * z‖ ≤ R ^ 2 / 2 := by
      rw [norm_mul, norm_conj]
      exact hprod
    have hnormR : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
      simp [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    have hden : R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - conj ρ * z‖ := by
      calc
        R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2‖ - ‖conj ρ * z‖ := by
          rw [hnormR]
          linarith [hsmall]
        _ ≤ ‖(R : ℂ) ^ 2 - conj ρ * z‖ := norm_sub_norm_le _ _
    have hdenPos : 0 < R ^ 2 / 2 := by positivity
    calc
      ‖conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)‖ =
          ‖ρ‖ / ‖(R : ℂ) ^ 2 - conj ρ * z‖ := by rw [norm_div, norm_conj]
      _ ≤ R / (R ^ 2 / 2) := div_le_div₀ hRpos.le (le_of_lt hρNorm) hdenPos hden
      _ = 2 / R := by field_simp [hRpos.ne']
  have hcorrListAt (z : ℂ) (hz : ‖z‖ ≤ 2 * r) :
      ‖(Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum‖ ≤
        (Z.length : ℝ) * (2 / R) := by
    exact norm_sum_map_le_length Z
      (fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)) (2 / R)
      (fun ρ hρ ↦ hcorrTerm z hz ρ hρ)
  refine ⟨R, Z, hRlo, hRhi, hboundary, hlen, hZ, hZcomplete, ?_⟩
  intro z hz hfz
  have hzRhalf : ‖z‖ ≤ R / 2 := by nlinarith [hz, hRlo]
  have hlogg := logDeriv_bound_of_zero_free_disk hRpos hM hgDiffBall
    (fun w hw ↦ hg0 w (ball_subset_closedBall hw)) hgBound hcenterG hzRhalf
  have hlogg' : ‖logDeriv g z‖ ≤ 100 * (M + 1) / R := by
    simpa [logDeriv_apply] using hlogg
  calc
    ‖logDeriv f z - (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum‖ =
        ‖logDeriv g z + (Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum‖ := by
          rw [hformula z hz hfz]
    _ ≤ ‖logDeriv g z‖ +
        ‖(Z.map fun ρ ↦ conj ρ / ((R : ℂ) ^ 2 - conj ρ * z)).sum‖ := norm_add_le _ _
    _ ≤ 100 * (M + 1) / R + (Z.length : ℝ) * (2 / R) :=
      add_le_add hlogg' (hcorrListAt z hz)
    _ = 100 * (M + 1) / R + 2 * (Z.length : ℝ) / R := by ring

end ArtinPrimitiveRoots.TypeII.PP.Proofs
