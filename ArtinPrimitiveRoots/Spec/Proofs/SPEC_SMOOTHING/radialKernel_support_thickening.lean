import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SMOOTHING.Defs

set_option autoImplicit false
open NumberField

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

/-- Kernel support over a slightly enlarged compact coordinate set lies in one compact set in X.
The closure of the coordinate neighborhood stays in the positive chart.
Uses frozen `G1_h3_basics`, `G2_x_action`,
`G6_ppi` and its coordinate bounds; supplies `radialKernel_compact_control`. -/
theorem radialKernel_support_thickening (k₀ : ℝ → ℝ)
    (hkSupport : {t | k₀ t ≠ 0} ⊆ Set.Icc 1 (1 + 1 / 100))
    (K : Set (Coord F)) (hK : IsCompact K) (hKpos : K ⊆ posSet F) :
    ∃ (U : Set (Coord F)) (W : Set (X F)),
      IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ posSet F ∧
        IsCompact W ∧ ∀ p ∈ closure U, ∀ w : X F, w ∉ W →
          radialKernel F k₀ (ptX F p) w = 0 := by
  classical
  by_cases hKempty : K = ∅
  · subst K
    refine ⟨∅, ∅, isOpen_empty, by simp, ?_, by simp, isCompact_empty, by simp⟩
    simpa
  · rcases G1_h3_basics (F := F) with
      ⟨hheight, hhoriz, _, _, _, _, _, hptX, _, _, _, hchart⟩
    obtain ⟨e, he, _⟩ := hchart
    have hptXcontinuous : ContinuousOn (ptX F) (posSet F) := by
      have heq : (posSet F).domRestrict (ptX F) = e := by
        funext p
        exact (he p).symm
      exact continuousOn_iff_continuous_domRestrict.mpr (heq ▸ e.continuous)
    have hposOpen : IsOpen (posSet F) := by
      rw [posSet, Set.ofPred_forall]
      apply isOpen_iInter_of_finite
      intro v
      have hc : Continuous (fun p : Coord F => (p v).2) := by fun_prop
      exact IsOpen.preimage hc (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    obtain ⟨U₀, hU₀open, hKU₀, hU₀pos⟩ :=
      hK.exists_isOpen_closure_subset (hposOpen.mem_nhdsSet.2 hKpos)
    obtain ⟨V, hVopen, hKV, hVcompact⟩ := exists_isOpen_superset_and_isCompact_closure hK
    let U : Set (Coord F) := V ∩ U₀
    have hUopen : IsOpen U := hVopen.inter hU₀open
    have hKU : K ⊆ U := Set.subset_inter hKV hKU₀
    have hUcompact : IsCompact (closure U) :=
      hVcompact.of_isClosed_subset isClosed_closure
        (closure_mono Set.inter_subset_left)
    have hUpos : closure U ⊆ posSet F :=
      (closure_mono Set.inter_subset_right).trans hU₀pos
    have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    have hclosureNe : (closure U).Nonempty := by
      rcases hKne with ⟨p, hp⟩
      exact ⟨p, subset_closure (hKU hp)⟩
    have hlow_exists (v : InfinitePlace F) :
        ∃ a : ℝ, 0 < a ∧ ∀ p ∈ closure U, a ≤ (p v).2 := by
      have hc : ContinuousOn (fun p : Coord F => (p v).2) (closure U) := by fun_prop
      exact hUcompact.exists_forall_le' (f := fun p => (p v).2) hc (a := 0)
        (fun p hp => hUpos hp v)
    choose lo hlo_pos hlo_le using hlow_exists
    have hhigh_exists (v : InfinitePlace F) :
        ∃ a : ℝ, 0 < a ∧ ∀ p ∈ closure U, (p v).2 ≤ a := by
      have hc : ContinuousOn (fun p : Coord F => (p v).2) (closure U) := by fun_prop
      obtain ⟨p, hp, hmax⟩ := hUcompact.exists_isMaxOn hclosureNe hc
      exact ⟨(p v).2, hUpos hp v, fun q hq => hmax hq⟩
    choose hi hhi_pos hhi_le using hhigh_exists
    have hradius_exists (v : InfinitePlace F) :
        ∃ a : ℝ, 0 ≤ a ∧ ∀ p ∈ closure U, ‖(p v).1‖ ≤ a := by
      have hc : ContinuousOn (fun p : Coord F => ‖(p v).1‖) (closure U) := by fun_prop
      obtain ⟨p, hp, hmax⟩ := hUcompact.exists_isMaxOn hclosureNe hc
      exact ⟨‖(p v).1‖, norm_nonneg _, fun q hq => hmax hq⟩
    choose xr hx_nonneg hx_le using hradius_exists
    let ρ : ℝ := 1 / 100
    let A : ℝ := Real.arcosh (1 + ρ)
    let B : ℝ := Real.sqrt (2 * ρ + ρ ^ 2)
    have hρ : 0 ≤ ρ := by norm_num [ρ]
    have hB : 0 ≤ B := Real.sqrt_nonneg _
    let C : Set (Coord F) := Set.pi Set.univ fun v =>
      Metric.closedBall (0 : ℂ) (xr v + hi v * B) ×ˢ
        Set.Icc (lo v * Real.exp (-A)) (hi v * Real.exp A)
    have hCcompact : IsCompact C := by
      unfold C
      exact isCompact_univ_pi fun v =>
        (isCompact_closedBall (0 : ℂ) _).prod isCompact_Icc
    have hCpos : C ⊆ posSet F := by
      intro q hq v
      have hqv : q v ∈ Metric.closedBall (0 : ℂ) (xr v + hi v * B) ×ˢ
          Set.Icc (lo v * Real.exp (-A)) (hi v * Real.exp A) := by
        exact (Set.mem_pi.mp hq) v (Set.mem_univ v)
      exact (mul_pos (hlo_pos v) (Real.exp_pos _)).trans_le hqv.2.1
    let W : Set (X F) := ptX F '' C
    have hWcompact : IsCompact W := by
      exact hCcompact.image_of_continuousOn (hptXcontinuous.mono hCpos)
    refine ⟨U, W, hUopen, hKU, hUcompact, hUpos, hWcompact, ?_⟩
    intro p hp z hzw
    by_contra hkernel
    have hkernel' : radialKernel F k₀ (ptX F p) z ≠ 0 := hkernel
    have hprod : ∀ v : InfinitePlace F,
        (k₀ (ppi ((ptX F p) v) (z v)) : ℂ) ≠ 0 := by
      have hprod' : (∏ v : InfinitePlace F,
          (k₀ (ppi ((ptX F p) v) (z v)) : ℂ)) ≠ 0 := by
        simpa only [radialKernel] using hkernel'
      intro v
      exact (Finset.prod_ne_zero_iff.mp hprod') v (Finset.mem_univ v)
    have hpPos : p ∈ posSet F := hUpos hp
    have hzPos : coordsX F z ∈ posSet F := by
      intro v
      change 0 < height (z v)
      rw [height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z v)
    have hppiCoord (v : InfinitePlace F) :
        ppi ((ptX F p) v) (z v) = ppiCoordAt F v (p, coordsX F z) := by
      have hz : z v = (ptX F (coordsX F z)) v := by
        exact (congrFun (hptX z) v).symm
      rw [hz]
      change ppi (pt (p v).1 (p v).2)
        (pt ((coordsX F z v).1) ((coordsX F z v).2)) = _
      unfold ppi ppiCoordAt
      rw [hhoriz _ _ (hpPos v), hhoriz _ _ (hzPos v),
        hheight _ _ (hpPos v), hheight _ _ (hzPos v)]
    have hppiUpper (v : InfinitePlace F) :
        ppiCoordAt F v (p, coordsX F z) ≤ 1 + ρ := by
      have hk₀ : k₀ (ppi ((ptX F p) v) (z v)) ≠ 0 := by
        intro hz0
        apply hprod v
        simp [hz0]
      have hwindow := hkSupport hk₀
      have hwindow' : ppi ((ptX F p) v) (z v) ∈ Set.Icc 1 (1 + 1 / 100) := hwindow
      rw [hppiCoord v] at hwindow'
      change _ ≤ 1 + ρ
      simpa only [ρ] using hwindow'.2
    have hz_coord_bounds (v : InfinitePlace F) :
        ‖(coordsX F z v).1‖ ≤ xr v + hi v * B ∧
          lo v * Real.exp (-A) ≤ (coordsX F z v).2 ∧
          (coordsX F z v).2 ≤ hi v * Real.exp A := by
      let x₀ : ℂ := (p v).1
      let y₀ : ℝ := (p v).2
      let x₁ : ℂ := (coordsX F z v).1
      let y₁ : ℝ := (coordsX F z v).2
      let x' : ℂ := (x₁ - x₀) / y₀
      let y' : ℝ := y₁ / y₀
      have hy₀ : 0 < y₀ := hpPos v
      have hy₁ : 0 < y₁ := hzPos v
      have hy' : 0 < y' := div_pos hy₁ hy₀
      have hnormal : ppi (pt 0 1) (pt x' y') =
          ppiCoordAt F v (p, coordsX F z) := by
        have hnormsq : Complex.normSq x' = Complex.normSq (x₀ - x₁) / y₀ ^ 2 := by
          dsimp [x']
          rw [Complex.normSq_div, Complex.normSq_ofReal]
          rw [show x₁ - x₀ = -(x₀ - x₁) by ring, Complex.normSq_neg]
          ring
        have hnormsq0 : Complex.normSq (0 - x') =
            Complex.normSq (x₀ - x₁) / y₀ ^ 2 := by
          calc
            Complex.normSq (0 - x') = Complex.normSq (-x') := by congr 1 <;> abel
            _ = Complex.normSq x' := Complex.normSq_neg _
            _ = _ := hnormsq
        let N : ℝ := Complex.normSq (x₀ - x₁)
        have hnum : N / y₀ ^ 2 + 1 + (y₁ / y₀) ^ 2 =
            (N + y₀ ^ 2 + y₁ ^ 2) / y₀ ^ 2 := by
          dsimp [N]
          rw [div_pow]
          field_simp [hy₀.ne']
        have hfinal : (N + y₀ ^ 2 + y₁ ^ 2) / y₀ ^ 2 / (2 * (y₁ / y₀)) =
            (N + y₀ ^ 2 + y₁ ^ 2) / (2 * y₀ * y₁) := by
          rw [show 2 * (y₁ / y₀) = (2 * y₁) / y₀ by ring, div_div_div_eq]
          field_simp [hy₀.ne', hy₁.ne']
        have hmain :
            (N / y₀ ^ 2 + 1 + (y₁ / y₀) ^ 2) / (2 * (y₁ / y₀)) =
              (N + y₀ ^ 2 + y₁ ^ 2) / (2 * y₀ * y₁) := by
          calc
            _ = (N + y₀ ^ 2 + y₁ ^ 2) / y₀ ^ 2 / (2 * (y₁ / y₀)) := by rw [hnum]
            _ = _ := hfinal
        unfold ppi ppiCoordAt
        rw [hhoriz 0 1 (by norm_num), hheight 0 1 (by norm_num),
          hhoriz x' y' hy', hheight x' y' hy']
        rw [hnormsq0]
        simp only [one_pow, mul_one]
        simpa [N, x₀, x₁, y₀, y₁, y'] using hmain
      have hball : ppi (pt 0 1) (pt x' y') ≤ 1 + ρ := by
        rw [hnormal]
        exact hppiUpper v
      have hcontrol := (G6_ppi (F := F)).2.2.2.1 ρ hρ (pt x' y') hball
      have hlog : |Real.log y'| ≤ A := by
        simpa [A, hheight x' y' hy'] using hcontrol.1
      have hnorm : ‖x'‖ ≤ B := by
        simpa [B, hhoriz x' y' hy'] using hcontrol.2
      have hlog_bounds := (abs_le.mp hlog)
      have hy'_lo : Real.exp (-A) ≤ y' := by
        calc
          Real.exp (-A) ≤ Real.exp (Real.log y') := Real.exp_le_exp.mpr hlog_bounds.1
          _ = y' := Real.exp_log hy'
      have hy'_hi : y' ≤ Real.exp A := by
        calc
          y' = Real.exp (Real.log y') := (Real.exp_log hy').symm
          _ ≤ Real.exp A := Real.exp_le_exp.mpr hlog_bounds.2
      have hnorm_div : ‖x₁ - x₀‖ / y₀ ≤ B := by
        simpa [x', norm_div, Real.norm_eq_abs, abs_of_pos hy₀] using hnorm
      have hnorm_diff : ‖x₁ - x₀‖ ≤ y₀ * B := by
        have h := (div_le_iff₀ hy₀).mp hnorm_div
        nlinarith [h]
      have hnorm_diff' : ‖x₁ - x₀‖ ≤ hi v * B :=
        hnorm_diff.trans (mul_le_mul_of_nonneg_right (hhi_le v p hp) hB)
      have hx₁ : ‖x₁‖ ≤ xr v + hi v * B := by
        calc
          ‖x₁‖ = ‖(x₁ - x₀) + x₀‖ := by congr 1 <;> abel
          _ ≤ ‖x₁ - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ ≤ hi v * B + xr v := add_le_add hnorm_diff' (hx_le v p hp)
          _ = xr v + hi v * B := by ring
      have hy₁_lo : lo v * Real.exp (-A) ≤ y₁ := by
        calc
          lo v * Real.exp (-A) ≤ y₀ * Real.exp (-A) :=
            mul_le_mul_of_nonneg_right (hlo_le v p hp) (Real.exp_nonneg _)
          _ ≤ y₀ * y' := mul_le_mul_of_nonneg_left hy'_lo hy₀.le
          _ = y₁ := by dsimp [y']; field_simp [hy₀.ne']
      have hy₁_hi : y₁ ≤ hi v * Real.exp A := by
        calc
          y₁ = y₀ * y' := by dsimp [y']; field_simp [hy₀.ne']
          _ ≤ y₀ * Real.exp A := mul_le_mul_of_nonneg_left hy'_hi hy₀.le
          _ ≤ hi v * Real.exp A :=
            mul_le_mul_of_nonneg_right (hhi_le v p hp) (Real.exp_nonneg _)
      exact ⟨hx₁, hy₁_lo, hy₁_hi⟩
    have hzC : coordsX F z ∈ C := by
      change ∀ v ∈ Set.univ, _
      intro v _
      rcases hz_coord_bounds v with ⟨hx, hlo', hhi'⟩
      refine ⟨?_, ⟨hlo', hhi'⟩⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    apply hzw
    change z ∈ ptX F '' C
    exact ⟨coordsX F z, hzC, hptX z⟩

end ArtinPrimitiveRoots.A1.Spec
