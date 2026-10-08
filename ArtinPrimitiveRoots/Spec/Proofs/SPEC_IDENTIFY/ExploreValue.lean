import ArtinPrimitiveRoots.Spec.EisensteinExtra

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology Pointwise

noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec
variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private theorem tsum_eq_default_of_subsingleton {α : Type*} [Subsingleton α] [Inhabited α]
    (f : α → ℂ) : ∑' x, f x = f default := by
  exact tsum_eq_single default (fun x hx => (hx (Subsingleton.elim x default)).elim)

open Classical in
private theorem tsum_eq_if_unique {α : Type*} (f : α → ℂ)
    (huniq : ∀ a b, f a ≠ 0 → f b ≠ 0 → a = b) :
    ∑' a, f a = if h : ∃ a, f a ≠ 0 then f h.choose else 0 := by
  classical
  by_cases h : ∃ a, f a ≠ 0
  · rw [dif_pos h]
    apply tsum_eq_single h.choose
    intro a haa
    by_contra hfa
    exact haa (huniq a h.choose hfa h.choose_spec)
  · have hfzero : f = 0 := by
      funext a
      by_contra hfa
      exact h ⟨a, hfa⟩
    simp [h, hfzero]

private theorem activeSeed_unique (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ) (s : ℂ)
    (z : X F) {q q' : CuspCosets F Γ σ}
    (hq : seedTerm F Γ σ τ s z q ≠ 0) (hq' : seedTerm F Γ σ τ s z q' ≠ 0) : q = q' := by
  let h (q : CuspCosets F Γ σ) := normHeight F
    (σ⁻¹ • ((q.out : Γ) • z))
  have hhigh (q : CuspCosets F Γ σ) (hseed : seedTerm F Γ σ τ s z q ≠ 0) :
      cut.A < h q := by
    by_contra hnot
    have hle : h q ≤ cut.A := le_of_not_gt hnot
    have hτ0 := cut.cutoff.2.2.1 (h q) hle
    apply hseed
    unfold seedTerm
    change (τ (h q) : ℂ) * (h q : ℂ) ^ (1 + 2 * s) = 0
    rw [hτ0]
    simp
  have hqA : cut.A₀ ≤ h q := (cut.A_ge.trans (hhigh q hq).le)
  have hq'A : cut.A₀ ≤ h q' := (cut.A_ge.trans (hhigh q' hq').le)
  have hsep := cut.separation q.out q'.out z hqA hq'A
  have hrel : QuotientGroup.rightRel (cuspStab F Γ σ) q.out q'.out :=
    QuotientGroup.rightRel_apply.mpr hsep
  calc
    q = Quotient.mk _ q.out := (Quotient.out_eq' q).symm
    _ = Quotient.mk _ q'.out := Quotient.sound hrel
    _ = q' := Quotient.out_eq' q'

set_option maxHeartbeats 100000000 in
private theorem probe_cusp_value_bound (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (σ : SL(2,F)) (τ : ℝ → ℝ) (cut : CutoffData F Γ σ τ)
    (s : ℂ) (hs : s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2))
    (d : SiegelData F Γ) (i : d.ι) (y : X F)
    (hy : y ∈ SiegelData.setAt F d i) :
    ∃ B : ℝ, 0 ≤ B ∧
      ‖eisSeries F Γ σ s ((d.σ i) • y) - eisSeed F Γ σ τ s ((d.σ i) • y)‖ ≤ B := by
  classical
  have hdist : ‖s - (5 / 2 : ℂ)‖ < 1 / 2 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hreabs : |s.re - (5 / 2 : ℝ)| < 1 / 2 := by
    have h := Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
    have hre : (s - (5 / 2 : ℂ)).re = s.re - (5 / 2 : ℝ) := by simp
    rw [hre] at h
    exact lt_of_le_of_lt h hdist
  have hlow : 2 < s.re := by
    have h := abs_lt.mp hreabs
    norm_num at h
    linarith
  have hhigh : s.re < 3 := by
    have h := abs_lt.mp hreabs
    norm_num at h
    linarith
  have hhalf : 1 / 2 < s.re := by linarith
  have hKstrip : ({s} : Set ℂ) ⊆ {x : ℂ | 2 < x.re ∧ x.re < 3} := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact ⟨hlow, hhigh⟩
  have hE4 := E4_eis_siegel Γ d σ {s} isCompact_singleton hKstrip
  have hE4i := hE4 i
  let tri (q : CuspCosets F Γ σ) : Prop :=
    σ⁻¹ * toSLF F (q.out : Γ) * d.σ i ∈ borelSL F
  let z' : X F := (d.σ i) • y
  let a : ℂ := 1 + 2 * s
  let C : ℝ := Classical.choose hE4i.2.1
  have hC : 0 ≤ C ∧ ∀ s' ∈ ({s} : Set ℂ), ∀ z ∈ SiegelData.setAt F d i,
      Summable (fun q' : {q : CuspCosets F Γ σ // ¬ tri q} =>
        (‖eisTerm F Γ σ s' ((d.σ i) • z) q'.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s' ((d.σ i) • x) q'.1) z‖)) ∧
      (∑' q' : {q : CuspCosets F Γ σ // ¬ tri q},
        (‖eisTerm F Γ σ s' ((d.σ i) • z) q'.1‖ +
          ‖fullGradient F (fun x => eisTerm F Γ σ s' ((d.σ i) • x) q'.1) z‖)) ≤ C :=
    Classical.choose_spec hE4i.2.1
  have hE4point := hC.2 s (Set.mem_singleton s) y hy
  obtain ⟨hE4summ, hE4sum⟩ := hE4point
  obtain ⟨R, hRpos, hR⟩ := (R6_two_heights (F := F) Γ).2 (d.σ i) σ
  have hLower : 0 < SiegelData.lowerHeight F d i := by
    unfold SiegelData.lowerHeight
    have hI : bottomRowFractionalIdeal F ((d.σ i)⁻¹) ≠ 0 :=
      (R3_cusps_finite (F := F) Γ).2.1 ((d.σ i)⁻¹)
    have hnormNe : FractionalIdeal.absNorm
        (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) ≠ 0 := by
      intro hh
      exact hI ((FractionalIdeal.absNorm_eq_zero_iff).mp hh)
    have hnormPos : 0 < FractionalIdeal.absNorm
        (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm hnormNe)
    have hrealPos : 0 <
        ((FractionalIdeal.absNorm (bottomRowFractionalIdeal F ((d.σ i)⁻¹)) : ℚ) : ℝ) := by
      exact_mod_cast hnormPos
    exact inv_pos.mpr (mul_pos hrealPos d.C_M_pos)
  have hparamE2 := (E2_eis_converge (F := F) Γ σ).1
  let σ₀ : ℝ := (1 / 2 + s.re) / 2
  have hσ₀ : 1 / 2 < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀le : σ₀ ≤ s.re := by dsimp [σ₀]; linarith
  obtain ⟨m₀, hm₀, hm₀bound⟩ := hparamE2 {z'} isCompact_singleton σ₀ s.re hσ₀
  have hSeriesSumm : Summable (fun q : CuspCosets F Γ σ => eisTerm F Γ σ s z' q) := by
    apply Summable.of_norm_bounded hm₀
    intro q
    exact hm₀bound z' (Set.mem_singleton z') s hσ₀le le_rfl q
  let rem : ℂ := ∑' q' : {q : CuspCosets F Γ σ // ¬ tri q}, eisTerm F Γ σ s z' q'.1
  have hRemNorm : ‖rem‖ ≤ C := by
    have hsumNorm : Summable (fun q' : {q : CuspCosets F Γ σ // ¬ tri q} =>
        ‖eisTerm F Γ σ s z' q'.1‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun _ => le_add_of_nonneg_right (norm_nonneg _)) hE4summ
    have hleNorm : (∑' q' : {q : CuspCosets F Γ σ // ¬ tri q},
        ‖eisTerm F Γ σ s z' q'.1‖) ≤ C := by
      exact (hsumNorm.tsum_le_tsum
        (fun _ => le_add_of_nonneg_right (norm_nonneg _)) hE4summ).trans hE4sum
    exact (norm_tsum_le_tsum_norm hsumNorm).trans (by simpa [rem] using hleNorm)
  have hseriesSplit : eisSeries F Γ σ s z' =
      (∑' q : {q : CuspCosets F Γ σ // tri q}, eisTerm F Γ σ s z' q.1) + rem := by
    dsimp [eisSeries, rem]
    exact (hSeriesSumm.tsum_subtype_add_tsum_subtype_compl {q | tri q}).symm
  let lead : ℂ := if h : ∃ q, tri q then
    eisTerm F Γ σ s z' h.choose else 0
  have hTriUnique : ∀ q q' : CuspCosets F Γ σ, tri q → tri q' → q = q' := hE4i.1
  have htriSum : (∑' q : {q : CuspCosets F Γ σ // tri q}, eisTerm F Γ σ s z' q.1) = lead := by
    by_cases hTri : ∃ q, tri q
    · let q₀ := hTri.choose
      have hq₀ := hTri.choose_spec
      have hsingle : (∑' q : {q : CuspCosets F Γ σ // tri q}, eisTerm F Γ σ s z' q.1) =
          eisTerm F Γ σ s z' q₀ := by
        letI : Subsingleton {q : CuspCosets F Γ σ // tri q} := ⟨fun q q' =>
          Subtype.ext (hTriUnique q.1 q'.1 q.2 q'.2)⟩
        letI : Inhabited {q : CuspCosets F Γ σ // tri q} := ⟨⟨q₀, hq₀⟩⟩
        exact tsum_eq_default_of_subsingleton (fun q => eisTerm F Γ σ s z' q.1)
      dsimp [lead]
      rw [dif_pos hTri, hsingle]
    · have hzero : ∀ q : {q : CuspCosets F Γ σ // tri q}, eisTerm F Γ σ s z' q.1 = 0 := by
        intro q
        exact False.elim (hTri ⟨q.1, q.2⟩)
      have hfun : (fun q : {q : CuspCosets F Γ σ // tri q} =>
          eisTerm F Γ σ s z' q.1) = 0 := funext hzero
      simp [lead, hTri, hfun]
  have hNy : SiegelData.lowerHeight F d i ≤ normHeight F y := by
    have hy' := hy
    simp only [SiegelData.setAt, siegelSet] at hy'
    rcases hy' with ⟨x, y₀, hyEq, hx, hbal, hNy⟩
    rw [← hyEq] at hNy
    exact hNy
  have hAone : 1 ≤ cut.A := cut.A₀_ge.trans cut.A_ge
  have hApos : 0 < cut.A := lt_of_lt_of_le zero_lt_one hAone
  have h2Aone : 1 ≤ 2 * cut.A := by nlinarith
  have hrexp : 0 < a.re ∧ a.re ≤ 7 := by
    dsimp [a]
    constructor <;> simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero] <;> linarith
  let Mlead : ℝ := max 1 ((2 * cut.A) ^ 7)
  have hMlead : 0 ≤ Mlead := by dsimp [Mlead]; positivity
  have hpowBound (t : ℝ) (ht : 0 < t) (ht₂ : t ≤ 2 * cut.A) :
      t ^ a.re ≤ Mlead := by
    by_cases ht₁ : t ≤ 1
    · exact (Real.rpow_le_one ht.le ht₁ hrexp.1.le).trans (le_max_left _ _)
    · have ht₁' : 1 ≤ t := le_of_not_ge ht₁
      calc
        t ^ a.re ≤ (2 * cut.A) ^ a.re :=
          Real.rpow_le_rpow ht.le ht₂ hrexp.1.le
        _ ≤ (2 * cut.A) ^ 7 := Real.rpow_le_rpow_of_exponent_le h2Aone hrexp.2
        _ ≤ Mlead := le_max_right _ _
  have hτA : τ cut.A = 0 := cut.cutoff.2.2.1 cut.A le_rfl
  have hτ2A : τ (2 * cut.A) = 1 := cut.cutoff.2.2.2 (2 * cut.A) le_rfl
  have hτrange (t : ℝ) : 0 ≤ τ t ∧ τ t ≤ 1 := by
    constructor
    · by_cases ht : t ≤ cut.A
      · rw [cut.cutoff.2.2.1 t ht]
      · have hAt : cut.A ≤ t := le_of_not_ge ht
        have h := cut.cutoff.2.1 hAt
        rw [hτA] at h
        exact h
    · by_cases ht : 2 * cut.A ≤ t
      · rw [cut.cutoff.2.2.2 t ht]
      · have ht2A : t ≤ 2 * cut.A := le_of_not_ge ht
        calc
          τ t ≤ τ (2 * cut.A) := cut.cutoff.2.1 ht2A
          _ = 1 := hτ2A
  have hresidualBound (t : ℝ) (ht : 0 < t) :
      ‖((1 - τ t : ℝ) : ℂ) * (t : ℂ) ^ a‖ ≤ Mlead := by
    by_cases ht₂ : 2 * cut.A ≤ t
    · rw [cut.cutoff.2.2.2 t ht₂]
      simp [Mlead]
    · have ht₂' : t ≤ 2 * cut.A := le_of_not_ge ht₂
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        specIdentify_cpow_norm t a ht]
      have hfactor : |1 - τ t| ≤ 1 := by
        have hrange := hτrange t
        rw [abs_le]
        constructor <;> linarith
      have hnonneg : 0 ≤ t ^ a.re := (Real.rpow_pos_of_pos ht _).le
      calc
        |1 - τ t| * t ^ a.re ≤ 1 * t ^ a.re :=
          mul_le_mul_of_nonneg_right hfactor hnonneg
        _ ≤ Mlead := hpowBound t ht ht₂'
  let H : ℝ := max cut.A (R / SiegelData.lowerHeight F d i)
  obtain ⟨Mseed, hMseedNonneg, hMseed⟩ :=
    specIdentify_profile_interval_bound τ a cut.cutoff.1 (Real.log cut.A) (Real.log H) (by
      dsimp [H]
      exact Real.log_le_log hApos (le_max_left _ _))
  have hSeedUnique : ∀ q q' : CuspCosets F Γ σ,
      seedTerm F Γ σ τ s z' q ≠ 0 → seedTerm F Γ σ τ s z' q' ≠ 0 → q = q' :=
    activeSeed_unique Γ σ τ cut s z'
  have hseedFormula : eisSeed F Γ σ τ s z' =
      if h : ∃ q, seedTerm F Γ σ τ s z' q ≠ 0 then
        seedTerm F Γ σ τ s z' h.choose else 0 := by
    dsimp [eisSeed]
    exact tsum_eq_if_unique _ hSeedUnique
  have hseedActiveBound (q : CuspCosets F Γ σ) (hnotTri : ¬ tri q)
      (hactive : seedTerm F Γ σ τ s z' q ≠ 0) :
      ‖seedTerm F Γ σ τ s z' q‖ ≤ Mseed := by
    let t : ℝ := normHeight F (σ⁻¹ • ((q.out : Γ) • z'))
    have ht : 0 < t := by dsimp [t, z']; exact specIdentify_normHeight_pos _
    have htA : cut.A < t := by
      by_contra h
      have hle : t ≤ cut.A := le_of_not_gt h
      have hτ0 := cut.cutoff.2.2.1 t hle
      apply hactive
      unfold seedTerm
      change (τ t : ℂ) * (t : ℂ) ^ a = 0
      rw [hτ0]
      simp
    have htriHeight :
        (σ⁻¹ * toSLF F (q.out : Γ) * d.σ i) 1 0 ≠ 0 := by
      intro hz
      apply hnotTri
      change (σ⁻¹ * toSLF F (q.out : Γ) * d.σ i) 1 0 = 0
      exact hz
    have hRbound : normHeight F y * t ≤ R := by
      have h := hR (q.out : Γ) z' htriHeight
      simpa [z', t] using h
    have htUpper : t ≤ R / SiegelData.lowerHeight F d i := by
      apply (le_div_iff₀ hLower).2
      calc
        t * SiegelData.lowerHeight F d i ≤ t * normHeight F y :=
          mul_le_mul_of_nonneg_left hNy (le_of_lt ht)
        _ = normHeight F y * t := by ring
        _ ≤ R := hRbound
    have htH : t ≤ H := by
      dsimp [H]
      exact htUpper.trans (le_max_right _ _)
    have hlogt : Real.log t ∈ Set.Icc (Real.log cut.A) (Real.log H) := by
      rw [Set.mem_Icc]
      exact ⟨Real.log_le_log hApos htA.le, Real.log_le_log ht htH⟩
    have hprofile : ‖specIdentifyRadialProfile τ a (Real.log t)‖ ≤ Mseed :=
      (hMseed _ hlogt).1
    have hnormEq : ‖seedTerm F Γ σ τ s z' q‖ =
        ‖specIdentifyRadialProfile τ a (Real.log t)‖ := by
      unfold seedTerm
      change ‖(τ t : ℂ) * (t : ℂ) ^ a‖ = _
      rw [← specIdentifyRadialProfile_log τ a ht]
    rw [hnormEq]
    exact hprofile
  have hseedEq (q : CuspCosets F Γ σ) (hq : seedTerm F Γ σ τ s z' q ≠ 0) :
      eisSeed F Γ σ τ s z' = seedTerm F Γ σ τ s z' q := by
    rw [hseedFormula]
    by_cases h : ∃ q', seedTerm F Γ σ τ s z' q' ≠ 0
    · rw [dif_pos h]
      have heq := hSeedUnique h.choose q h.choose_spec hq
      rw [heq]
    · exact False.elim (h ⟨q, hq⟩)
  have hseedZero (h : ¬ ∃ q, seedTerm F Γ σ τ s z' q ≠ 0) :
      eisSeed F Γ σ τ s z' = 0 := by
    rw [hseedFormula]
    simp [h]
  have htriTermSmall (q : CuspCosets F Γ σ) (hq : tri q)
      (hnotActive : seedTerm F Γ σ τ s z' q = 0) :
      ‖eisTerm F Γ σ s z' q‖ ≤ Mlead := by
    let t : ℝ := normHeight F (σ⁻¹ • ((q.out : Γ) • z'))
    have ht : 0 < t := by dsimp [t, z']; exact specIdentify_normHeight_pos _
    have hsmall : t ≤ 2 * cut.A := by
      by_contra hlarge
      have hlarge' : 2 * cut.A ≤ t := le_of_not_ge hlarge
      have hτone := cut.cutoff.2.2.2 t hlarge'
      have hpowNe : (t : ℂ) ^ a ≠ 0 := by
        intro hz
        have hnorm := congrArg norm hz
        rw [specIdentify_cpow_norm t a ht] at hnorm
        have hpowPos : 0 < t ^ a.re := Real.rpow_pos_of_pos ht _
        exact hpowPos.ne' (by simpa using hnorm.symm)
      apply hnotActive
      unfold seedTerm
      change (τ t : ℂ) * (t : ℂ) ^ a ≠ 0
      rw [hτone]
      exact mul_ne_zero (by norm_num) hpowNe
    unfold eisTerm
    change ‖(t : ℂ) ^ a‖ ≤ Mlead
    rw [specIdentify_cpow_norm t a ht]
    exact hpowBound t ht hsmall
  let B : ℝ := C + 2 * Mlead + Mseed
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [hC.1, hMlead, hMseedNonneg]
  refine ⟨B, hB, ?_⟩
  by_cases hTri : ∃ q, tri q
  · let q₀ : CuspCosets F Γ σ := hTri.choose
    have hq₀ : tri q₀ := hTri.choose_spec
    have hlead : lead = eisTerm F Γ σ s z' q₀ := by
      simp [lead, hTri, q₀]
    by_cases hactive₀ : seedTerm F Γ σ τ s z' q₀ ≠ 0
    · have hseed := hseedEq q₀ hactive₀
      rw [hseriesSplit, htriSum, hlead, hseed]
      have hcancel :
          (eisTerm F Γ σ s z' q₀ + rem) - seedTerm F Γ σ τ s z' q₀ =
            rem + (eisTerm F Γ σ s z' q₀ - seedTerm F Γ σ τ s z' q₀) := by ring
      rw [hcancel]
      have htriRes :
          ‖eisTerm F Γ σ s z' q₀ - seedTerm F Γ σ τ s z' q₀‖ ≤ Mlead := by
        let t : ℝ := normHeight F (σ⁻¹ • ((q₀.out : Γ) • z'))
        have ht : 0 < t := by dsimp [t, z']; exact specIdentify_normHeight_pos _
        unfold eisTerm seedTerm
        change ‖(t : ℂ) ^ a - (τ t : ℂ) * (t : ℂ) ^ a‖ ≤ Mlead
        have hfactor : (t : ℂ) ^ a - (τ t : ℂ) * (t : ℂ) ^ a =
            ((1 - τ t : ℝ) : ℂ) * (t : ℂ) ^ a := by push_cast; ring
        rw [hfactor]
        exact hresidualBound t ht
      calc
        ‖rem + (eisTerm F Γ σ s z' q₀ - seedTerm F Γ σ τ s z' q₀)‖ ≤
            ‖rem‖ + ‖eisTerm F Γ σ s z' q₀ - seedTerm F Γ σ τ s z' q₀‖ :=
          norm_add_le _ _
        _ ≤ C + Mlead := add_le_add hRemNorm htriRes
        _ ≤ B := by dsimp [B]; linarith [hMlead, hMseedNonneg]
    · by_cases hactive : ∃ q, seedTerm F Γ σ τ s z' q ≠ 0
      · let q₁ := hactive.choose
        have hq₁ := hactive.choose_spec
        have hq₁notTri : ¬ tri q₁ := by
          intro htri₁
          have heq := hTriUnique q₁ q₀ htri₁ hq₀
          subst q₁
          exact hactive₀ hq₁
        have hseed := hseedEq q₁ hq₁
        have hleadSmall := htriTermSmall q₀ hq₀ hactive₀
        have hseedSmall := hseedActiveBound q₁ hq₁notTri hq₁
        rw [hseriesSplit, htriSum, hlead, hseed]
        calc
          ‖(eisTerm F Γ σ s z' q₀ + rem) - seedTerm F Γ σ τ s z' q₁‖ ≤
              (‖eisTerm F Γ σ s z' q₀‖ + ‖rem‖) +
                ‖seedTerm F Γ σ τ s z' q₁‖ := by
            calc
              _ = ‖(eisTerm F Γ σ s z' q₀ + rem) +
                    (-seedTerm F Γ σ τ s z' q₁)‖ := by congr 1 <;> ring
              _ ≤ ‖eisTerm F Γ σ s z' q₀ + rem‖ +
                    ‖seedTerm F Γ σ τ s z' q₁‖ := norm_add_le _ _
              _ ≤ (‖eisTerm F Γ σ s z' q₀‖ + ‖rem‖) +
                    ‖seedTerm F Γ σ τ s z' q₁‖ := by gcongr; exact norm_add_le _ _
          _ ≤ B := by dsimp [B]; linarith [hleadSmall, hRemNorm, hseedSmall]
      · have hseed := hseedZero hactive
        have hleadSmall := htriTermSmall q₀ hq₀ (by simpa using hactive₀)
        rw [hseriesSplit, htriSum, hlead, hseed]
        simp only [sub_zero]
        calc
          ‖eisTerm F Γ σ s z' q₀ + rem‖ ≤
              ‖eisTerm F Γ σ s z' q₀‖ + ‖rem‖ := norm_add_le _ _
          _ ≤ B := by dsimp [B]; linarith [hleadSmall, hRemNorm, hMlead, hMseedNonneg]
  · have hnoTri : ¬ ∃ q, tri q := hTri
    have hlead0 : lead = 0 := by simp [lead, hnoTri]
    by_cases hactive : ∃ q, seedTerm F Γ σ τ s z' q ≠ 0
    · let q₁ := hactive.choose
      have hq₁ := hactive.choose_spec
      have hq₁notTri : ¬ tri q₁ := fun hq => hnoTri ⟨q₁, hq⟩
      have hseed := hseedEq q₁ hq₁
      have hseedSmall := hseedActiveBound q₁ hq₁notTri hq₁
      rw [hseriesSplit, htriSum, hlead0, hseed]
      simp only [zero_add]
      calc
        ‖rem - seedTerm F Γ σ τ s z' q₁‖ ≤ ‖rem‖ + ‖seedTerm F Γ σ τ s z' q₁‖ := by
          calc
            _ = ‖rem + (-seedTerm F Γ σ τ s z' q₁)‖ := by congr 1 <;> ring
            _ ≤ _ := norm_add_le _ _
        _ ≤ B := by dsimp [B]; linarith [hRemNorm, hseedSmall, hMlead]
    · have hseed := hseedZero hactive
      rw [hseriesSplit, htriSum, hlead0, hseed]
      simp only [zero_add, sub_zero]
      calc
        ‖rem‖ ≤ C := hRemNorm
        _ ≤ B := by dsimp [B]; linarith [hMlead, hMseedNonneg]

end ArtinPrimitiveRoots.A1.Spec
