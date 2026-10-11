import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_majorKernel_volume_bound

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pd5_cutoff_bounds {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ E P R : ℝ, 1 ≤ E ∧ 1 ≤ P ∧ 4 ≤ R ∧
      (∀ u, |F.eta u| ≤ E) ∧ (∀ u, |F.psi u| ≤ P) ∧
      (∀ u, R < |u| → F.psi u = 0) := by
  rcases hF with ⟨_, _, _, _, hEta, hPsi⟩
  rcases hEta with ⟨hetaCont, hetaSupport, _, _⟩
  rcases hPsi with ⟨hpsiCont, hpsiCompact, _⟩
  obtain ⟨E₀, hE₀⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (1 : ℝ) 4)).exists_bound_of_continuousOn
      hetaCont.continuous.continuousOn
  obtain ⟨P₀, hP₀⟩ := hpsiCont.continuous.bounded_above_of_compact_support hpsiCompact
  obtain ⟨B, hBpos, hB⟩ := hpsiCompact.exists_pos_le_norm
  let E := max E₀ 1
  let P := max P₀ 1
  let R := max B 4
  have hE : 1 ≤ E := le_max_right _ _
  have hP : 1 ≤ P := le_max_right _ _
  have hR : 4 ≤ R := le_max_right _ _
  have heta (u : ℝ) : |F.eta u| ≤ E := by
    by_cases hu : u ∈ Set.Icc (1 : ℝ) 4
    · change |F.eta u| ≤ max E₀ 1
      rw [← Real.norm_eq_abs]
      exact (hE₀ u hu).trans (le_max_left _ _)
    · have hnot : u ∉ Function.support F.eta := fun hs => hu (hetaSupport hs)
      have hzero : F.eta u = 0 := by
        by_contra hn
        exact hnot (by simpa [Function.mem_support] using hn)
      simp [hzero, E]
  have hpsi (u : ℝ) : |F.psi u| ≤ P := by
    change |F.psi u| ≤ max P₀ 1
    rw [← Real.norm_eq_abs]
    exact (hP₀ u).trans (le_max_left _ _)
  have hpsiZero (u : ℝ) (hu : R < |u|) : F.psi u = 0 := by
    apply hB
    have hlt : B < |u| := lt_of_le_of_lt (le_max_left _ _) hu
    simpa [Real.norm_eq_abs] using hlt.le
  exact ⟨E, P, R, hE, hP, hR, heta, hpsi, hpsiZero⟩

private theorem pd5_arc_eventually (A₀ : ℝ) (hA₀ : 0 < A₀) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x, x₀ ≤ x →
      1 ≤ Real.log x ∧
      800 * A₀ ≤ Real.rpow (Real.log x) (1 / 20 : ℝ) ∧
      40 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) := by
  have hlog := Real.tendsto_log_atTop
  have hpow05 : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 20 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 20 : ℝ))).comp hlog
  have hpow10 : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp hlog
  have hAll : ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 1 ≤ Real.log x ∧
        800 * A₀ ≤ Real.rpow (Real.log x) (1 / 20 : ℝ) ∧
        40 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2,
      (Filter.tendsto_atTop.1 hlog 1),
      (Filter.tendsto_atTop.1 hpow05 (800 * A₀)),
      (Filter.tendsto_atTop.1 hpow10 (40 * Real.log 2))] with x hx hxL hx05 hx10
    exact ⟨hx, hxL, hx05, hx10⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hAll
  refine ⟨x₀, (hx₀ x₀ le_rfl).1, ?_⟩
  intro x hx
  exact (hx₀ x hx).2

private theorem pd5_dyadic_arc_guard (x Y : ℝ) (A₀ : ℝ) (K : ℕ)
    (hA₀ : 0 < A₀) (hL : 1 ≤ Real.log x)
    (hL05 : 800 * A₀ ≤ Real.rpow (Real.log x) (1 / 20 : ℝ))
    (hL10 : 40 * Real.log 2 ≤ Real.rpow (Real.log x) (1 / 10 : ℝ))
    (hYmem : Y ∈ dyadicScales x K) :
    1 ≤ Y ∧ 2 * Real.rpow (Real.log x) A₀ / Y ≤ 1 := by
  let L := Real.log x
  let U := Real.rpow L (1 / 20 : ℝ)
  let V := Real.rpow L (1 / 10 : ℝ)
  let T := Real.rpow L A₀
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hLnonneg : 0 ≤ L := hLpos.le
  have hUpos : 0 < U := Real.rpow_pos_of_pos hLpos _
  have hVpos : 0 < V := Real.rpow_pos_of_pos hLpos _
  have hVeq : V = U ^ 2 := by
    dsimp [V, U]
    rw [show (1 / 10 : ℝ) = (1 / 20 : ℝ) * 2 by norm_num,
      Real.rpow_mul hLnonneg]
    norm_num
  have hlogle : Real.log L ≤ U / (1 / 20 : ℝ) := Real.log_le_rpow_div hLnonneg (by norm_num)
  have hlogBound : A₀ * Real.log L ≤ V / 40 := by
    rw [hVeq]
    have hsmall : 20 * A₀ * U ≤ U ^ 2 / 40 := by nlinarith [hL05]
    calc
      A₀ * Real.log L ≤ A₀ * (U / (1 / 20 : ℝ)) := mul_le_mul_of_nonneg_left hlogle hA₀.le
      _ = 20 * A₀ * U := by ring
      _ ≤ U ^ 2 / 40 := hsmall
  have hTbound : T ≤ Real.exp (V / 40) := by
    dsimp [T]
    rw [Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    calc
      Real.log L * A₀ = A₀ * Real.log L := by ring
      _ ≤ V / 40 := hlogBound
  have hYlog : (1 / 20 : ℝ) * V ≤ Real.log Y := by
    unfold dyadicScales at hYmem
    exact (Finset.mem_filter.mp hYmem).2.1
  have hYpos : 0 < Y := by
    unfold dyadicScales at hYmem
    rcases Finset.mem_filter.mp hYmem with ⟨himage, _⟩
    rcases Finset.mem_image.mp himage with ⟨k, _, rfl⟩
    positivity
  have hYlower : Real.exp (V / 20) ≤ Y := by
    calc
      Real.exp (V / 20) ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr (by nlinarith [hYlog])
      _ = Y := Real.exp_log hYpos
  have hYone : 1 ≤ Y := by
    have hExp : 1 ≤ Real.exp (V / 20) := Real.one_le_exp_iff.mpr (by positivity)
    exact hExp.trans hYlower
  have hu : Real.log 2 ≤ V / 40 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 40)).2 (by linarith [hL10])
  have hhalf : Real.exp (-(V / 40)) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-(V / 40)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hu)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hratio : T / Y ≤ Real.exp (-(V / 40)) := by
    apply (div_le_iff₀ hYpos).2
    calc
      T ≤ Real.exp (V / 40) := hTbound
      _ = Real.exp (-(V / 40)) * Real.exp (V / 20) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ Real.exp (-(V / 40)) * Y :=
        mul_le_mul_of_nonneg_left hYlower (Real.exp_pos _).le
  have hTpos : 0 < T := Real.rpow_pos_of_pos hLpos _
  constructor
  · exact hYone
  · calc
      2 * T / Y = 2 * (T / Y) := by ring
      _ ≤ 2 * Real.exp (-(V / 40)) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 1 := by nlinarith [hhalf]

private theorem pd5_complement_det (z : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) : det2 z (complementVec z) = 1 := by
  have hBez : z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2 = 1 := by
    have h₁ := Int.gcd_eq_gcd_ab z.1 z.2
    have h₂ : (Int.gcd z.1 z.2 : ℤ) = 1 := by exact_mod_cast hz
    rw [h₁] at h₂
    exact h₂
  unfold det2 complementVec
  simp only [Prod.fst, Prod.snd]
  linear_combination hBez

private def pd5_detCoeff (z z' : ℤ × ℤ) (m : ℤ) : ℤ :=
  Int.gcdA z.1 z.2 * (z'.1 - m * (complementVec z).1) +
    Int.gcdB z.1 z.2 * (z'.2 - m * (complementVec z).2)

private theorem pd5_det_decomposition (z z' : ℤ × ℤ) (m : ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (hd : det2 z z' = m) :
    z' = (pd5_detCoeff z z' m * z.1 + m * (complementVec z).1,
          pd5_detCoeff z z' m * z.2 + m * (complementVec z).2) := by
  let w := complementVec z
  let v₁ := z'.1 - m * w.1
  let v₂ := z'.2 - m * w.2
  let h := pd5_detCoeff z z' m
  have hBez : z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2 = 1 := by
    have h₁ := Int.gcd_eq_gcd_ab z.1 z.2
    have h₂ : (Int.gcd z.1 z.2 : ℤ) = 1 := by exact_mod_cast hz
    rw [h₁] at h₂
    exact h₂
  have hwDet : z.1 * w.2 - z.2 * w.1 = 1 := by
    simpa [w, det2] using pd5_complement_det z hz
  have hvDet : z.1 * v₂ - z.2 * v₁ = 0 := by
    dsimp [v₁, v₂]
    have hd' : z.1 * z'.2 - z.2 * z'.1 = m := by simpa [det2] using hd
    calc
      z.1 * (z'.2 - m * w.2) - z.2 * (z'.1 - m * w.1) =
          (z.1 * z'.2 - z.2 * z'.1) - m * (z.1 * w.2 - z.2 * w.1) := by ring
      _ = 0 := by rw [hd', hwDet]; ring
  have hvDet' : z.2 * v₁ - z.1 * v₂ = 0 := by linarith [hvDet]
  have hv₁ : h * z.1 = v₁ := by
    dsimp [h]
    calc
      (Int.gcdA z.1 z.2 * v₁ + Int.gcdB z.1 z.2 * v₂) * z.1 =
          (z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2) * v₁ +
            Int.gcdB z.1 z.2 * (z.1 * v₂ - z.2 * v₁) := by ring
      _ = v₁ := by rw [hBez, hvDet]; ring
  have hv₂ : h * z.2 = v₂ := by
    dsimp [h]
    calc
      (Int.gcdA z.1 z.2 * v₁ + Int.gcdB z.1 z.2 * v₂) * z.2 =
          (z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2) * v₂ +
            Int.gcdA z.1 z.2 * (z.2 * v₁ - z.1 * v₂) := by ring
      _ = v₂ := by rw [hBez, hvDet']; ring
  change z' = (h * z.1 + m * w.1, h * z.2 + m * w.2)
  refine Prod.ext ?_ ?_
  · dsimp [v₁] at hv₁
    dsimp [w]
    linarith
  · dsimp [v₂] at hv₂
    dsimp [w]
    linarith

private theorem pd5_fixed_det_positions_card (S : PDScale) (w : ArchRoot)
    (z : ℤ × ℤ) (Z : Finset (ℤ × ℤ)) (m : ℤ)
    (hU : 0 < S.U) (hu : 0 < w.u)
    (hz : Int.gcd z.1 z.2 = 1) (hzbox : envBox S w z) :
    (Z.filter fun z' => envBox S w z' ∧ det2 z z' = m).card ≤ 18 := by
  let lo := S.U / w.u
  let tau := w.tau z
  let c := (m : ℝ) * w.tau (complementVec z)
  let A := (lo - c) / tau
  let F := Z.filter fun z' => envBox S w z' ∧ det2 z z' = m
  let J : Finset ℤ := Finset.Icc (⌊A⌋) (⌊A⌋ + 15)
  have hloPos : 0 < lo := div_pos hU hu
  have hsourceTau : lo ≤ tau := by
    apply (div_le_iff₀ hu).2
    simpa [tau, mul_comm] using hzbox.1
  have htauPos : 0 < tau := lt_of_lt_of_le hloPos hsourceTau
  have hloOverTau : lo / tau ≤ 1 := (div_le_one₀ htauPos).2 hsourceTau
  have hCoeffBounds (z' : ℤ × ℤ) (hz' : envBox S w z') (hdet : det2 z z' = m) :
      (⌊A⌋ : ℤ) ≤ pd5_detCoeff z z' m ∧ pd5_detCoeff z z' m ≤ ⌊A⌋ + 15 := by
    have hTauEq : w.tau z' =
        (pd5_detCoeff z z' m : ℝ) * tau + c := by
      calc
        w.tau z' = w.tau (pd5_detCoeff z z' m * z.1 + m * (complementVec z).1,
            pd5_detCoeff z z' m * z.2 + m * (complementVec z).2) :=
          congrArg w.tau (pd5_det_decomposition z z' m hz hdet)
        _ = (pd5_detCoeff z z' m : ℝ) * tau + c := by
          simp [ArchRoot.tau, tau, c]
          push_cast
          ring
    have htargetLo : lo ≤ w.tau z' := by
      apply (div_le_iff₀ hu).2
      simpa [lo, mul_comm] using hz'.1
    have htargetHi : w.tau z' ≤ 16 * lo := by
      calc
        w.tau z' ≤ (16 * S.U) / w.u := by
          apply (le_div_iff₀ hu).2
          simpa [mul_comm] using hz'.2.1
        _ = 16 * lo := by dsimp [lo]; ring
    have hrealLo : A ≤ (pd5_detCoeff z z' m : ℝ) := by
      apply (div_le_iff₀ htauPos).2
      dsimp [A, c, tau]
      rw [hTauEq] at htargetLo
      linarith
    have hrealHi : (pd5_detCoeff z z' m : ℝ) ≤ A + 15 := by
      have hcoeffHi : (pd5_detCoeff z z' m : ℝ) ≤ (16 * lo - c) / tau := by
        apply (le_div_iff₀ htauPos).2
        rw [hTauEq] at htargetHi
        dsimp [c, tau]
        linarith
      have hidentity : (16 * lo - c) / tau = A + 15 * (lo / tau) := by
        dsimp [A]
        field_simp [htauPos.ne']
        ring
      rw [hidentity] at hcoeffHi
      dsimp [A]
      linarith
    constructor
    · have hfloor : (⌊A⌋ : ℝ) ≤ (pd5_detCoeff z z' m : ℝ) :=
        (Int.floor_le A).trans hrealLo
      exact_mod_cast hfloor
    · have hminus : ((pd5_detCoeff z z' m - 15 : ℤ) : ℝ) ≤ A := by
        push_cast
        linarith
      have hfloor : pd5_detCoeff z z' m - 15 ≤ ⌊A⌋ := (Int.le_floor).2 hminus
      omega
  have hMaps : Set.MapsTo (fun z' => pd5_detCoeff z z' m) (F : Set (ℤ × ℤ)) (J : Set ℤ) := by
    intro z' hz'
    have hz' := Finset.mem_filter.mp hz'
    exact Finset.mem_Icc.mpr (hCoeffBounds z' hz'.2.1 hz'.2.2)
  have hInj : (F : Set (ℤ × ℤ)).InjOn (fun z' => pd5_detCoeff z z' m) := by
    intro z₁ hz₁ z₂ hz₂ heq
    have hd₁ := (Finset.mem_filter.mp hz₁).2.2
    have hd₂ := (Finset.mem_filter.mp hz₂).2.2
    have heq' : pd5_detCoeff z z₁ m = pd5_detCoeff z z₂ m := heq
    calc
      z₁ = (pd5_detCoeff z z₁ m * z.1 + m * (complementVec z).1,
            pd5_detCoeff z z₁ m * z.2 + m * (complementVec z).2) :=
              pd5_det_decomposition z z₁ m hz hd₁
      _ = (pd5_detCoeff z z₂ m * z.1 + m * (complementVec z).1,
            pd5_detCoeff z z₂ m * z.2 + m * (complementVec z).2) := by rw [heq']
      _ = z₂ := (pd5_det_decomposition z z₂ m hz hd₂).symm
  have hcard : F.card ≤ J.card := Finset.card_le_card_of_injOn _ hMaps hInj
  calc
    F.card ≤ J.card := hcard
    _ = 16 := by
      simp only [J, Int.card_Icc]
      have h : ⌊A⌋ + 15 + 1 - ⌊A⌋ = (16 : ℤ) := by ring
      rw [h]
      norm_num
    _ ≤ 18 := by norm_num

private theorem pd5_rawMultiplier_norm_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (E P : ℝ)
    (hD₀ : 0 < (S.d₀ : ℝ)) (hD : (S.d₀ : ℝ) ≤ (D : ℝ))
    (hE : 1 ≤ E) (hP : 0 ≤ P)
    (hEta : ∀ u, |F.eta u| ≤ E) (hPsi : ∀ u, |F.psi u| ≤ P) :
    ‖rawMultiplier F S D aa bb t‖ ≤ E ^ 2 * P := by
  have hDen : 0 < (D : ℝ) := lt_of_lt_of_le hD₀ hD
  have hRatioNonneg : 0 ≤ (S.d₀ : ℝ) / (D : ℝ) := div_nonneg hD₀.le hDen.le
  have hRatio : (S.d₀ : ℝ) / (D : ℝ) ≤ 1 := (div_le_one₀ hDen).2 hD
  by_cases hcond : t = (bb : ℤ) - aa
  · simp [rawMultiplier, hcond, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hRatioNonneg]
    calc
      (S.d₀ : ℝ) / (D : ℝ) * |F.eta ((bb : ℝ) / S.Y)| *
          |F.eta ((aa : ℝ) / S.Y)| * |F.psi (((bb : ℝ) - aa) / S.Y)| ≤ 1 * E * E * P := by
        gcongr
        · exact hEta _
        · exact hEta _
        · exact hPsi _
      _ = E ^ 2 * P := by ring
  · simp [rawMultiplier, hcond]
    positivity

private theorem pd5_comparisonMultiplier_norm_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (E P : ℝ)
    (hD₀ : 0 < (S.d₀ : ℝ)) (hD : (S.d₀ : ℝ) ≤ (D : ℝ))
    (hE : 1 ≤ E) (hP : 0 ≤ P)
    (hEta : ∀ u, |F.eta u| ≤ E) (hPsi : ∀ u, |F.psi u| ≤ P)
    (hx : 2 ≤ S.x) (hY : 1 ≤ S.Y)
    (hT : 1 ≤ Real.rpow (Real.log S.x) F.A₀)
    (hrad : 2 * Real.rpow (Real.log S.x) F.A₀ / S.Y ≤ 1) :
    ‖comparisonMultiplier F S D aa bb t‖ ≤
      E ^ 2 * (32 * P * (Real.rpow (Real.log S.x) F.A₀) ^ 3 / S.Y) := by
  have hDen : 0 < (D : ℝ) := lt_of_lt_of_le hD₀ hD
  have hRatioNonneg : 0 ≤ (S.d₀ : ℝ) / (D : ℝ) := div_nonneg hD₀.le hDen.le
  have hRatioAbs : |(S.d₀ : ℝ) / (D : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hRatioNonneg]
    exact (div_le_one₀ hDen).2 hD
  have hKernel := pd5_majorKernel_volume_bound S.x S.Y F.A₀ P (t : ℝ) aa bb F.psi
    hx hY hT hrad hP hPsi
  unfold comparisonMultiplier
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |(S.d₀ : ℝ) / (D : ℝ)| * |F.eta ((bb : ℝ) / S.Y)| *
        |F.eta ((aa : ℝ) / S.Y)| *
        ‖majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi‖ ≤
      1 * E * E * (32 * P * (Real.rpow (Real.log S.x) F.A₀) ^ 3 / S.Y) := by
        gcongr
        · exact hEta _
        · exact hEta _
    _ = E ^ 2 * (32 * P * (Real.rpow (Real.log S.x) F.A₀) ^ 3 / S.Y) := by ring

private theorem pd5_int_abs_mem_Icc (X : ℝ) (t : ℤ)
    (ht : |(t : ℝ)| ≤ X) :
    t ∈ Finset.Icc (-⌊X⌋) ⌊X⌋ := by
  have hAbs := abs_le.mp ht
  have hUpper : t ≤ ⌊X⌋ := Int.le_floor.mpr hAbs.2
  have htNeg : -(t : ℝ) ≤ X := by linarith [hAbs.1]
  have hNeg : -t ≤ ⌊X⌋ := Int.le_floor.mpr (by exact_mod_cast htNeg)
  exact Finset.mem_Icc.mpr ⟨by omega, hUpper⟩

/-- Uniform position sum before any label choices are integrated. Source primitivity, its
box and determinant divisibility remain in the hypotheses/guard; both multiplier parts and
both directions are included. Uses
pd5_majorKernel_volume_bound, a fixed-number determinant-line count and compact cutoff bounds.
Feeds positive prescribed edge rows and low-rank positive edge envelopes. -/
theorem pd5_edge_position_mass_le (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ Cgeom x₀ : ℝ, 0 < Cgeom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ z : ℤ × ℤ,
          Int.gcd z.1 z.2 = 1 → envBox S w z →
          ∀ p q : PrimeLists S.x K, S.d₀ ≤ sharedProduct p →
            ∀ forward : Bool, ∀ Z : Finset (ℤ × ℤ),
              (∑ z' ∈ Z, if envBox S w z' ∧ (sharedProduct p : ℤ) ∣ det2 z z' then
                ‖edgeMultiplier F S forward true p q z z'‖ +
                  ‖edgeMultiplier F S forward false p q z z'‖ else 0) ≤
                Cgeom * Real.rpow S.L (3 * F.A₀) := by
  obtain ⟨E, P, R, hE, hP, hR, hEta, hPsi, hPsiZero⟩ := pd5_cutoff_bounds F hF
  rcases hF with ⟨_, _, _, hA₀, _, _⟩
  obtain ⟨x₀, hx₀, hScaleEvent⟩ := pd5_arc_eventually F.A₀ hA₀
  let Cgeom := 18 * E ^ 2 * P * (1 + 32 * (2 * R + 1))
  have hCgeom : 0 < Cgeom := by dsimp [Cgeom]; positivity
  refine ⟨Cgeom, x₀, hCgeom, hx₀, ?_⟩
  intro S hS hxS w hw z hz hzbox p q hDle forward Z
  rcases hS with ⟨hxS2, hHm, _, _, _, hYmem, hpad⟩
  have hLdata := hScaleEvent S.x hxS
  rcases hLdata with ⟨hL, hL05, hL10⟩
  have hA₀pos : 0 < F.A₀ := hA₀
  have hGuard := pd5_dyadic_arc_guard S.x S.Y F.A₀ K hA₀pos hL hL05 hL10 hYmem
  have hYone : 1 ≤ S.Y := hGuard.1
  have hYpos : 0 < S.Y := lt_of_lt_of_le (by norm_num) hYone
  have hRad : 2 * Real.rpow (Real.log S.x) F.A₀ / S.Y ≤ 1 := hGuard.2
  have hTone : 1 ≤ Real.rpow (Real.log S.x) F.A₀ :=
    Real.one_le_rpow hL hA₀pos.le
  have hxpos : 0 < S.x := lt_of_lt_of_le (by norm_num) hxS2
  have hHmpos : 0 < S.Hm :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHm
  have hd₀posNat : 0 < S.d₀ := by
    unfold padScales at hpad
    rcases Finset.mem_image.mp hpad with ⟨k, _, hk⟩
    rw [← hk]
    positivity
  have hd₀pos : 0 < (S.d₀ : ℝ) := by exact_mod_cast hd₀posNat
  have hUpos : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    positivity
  have hu : 0 < w.u := lt_of_lt_of_le hUpos hw.1
  let D := sharedProduct p
  have hD : (S.d₀ : ℝ) ≤ (D : ℝ) := by exact_mod_cast hDle
  have hDintPos : 0 < (D : ℝ) := lt_of_lt_of_le hd₀pos hD
  let quotient (z' : ℤ × ℤ) : ℤ :=
    if forward then det2 z z' / (D : ℤ) else det2 z' z / (D : ℤ)
  let rawTarget : ℤ :=
    if forward then (lastProduct p : ℤ) - lastProduct q else
      (lastProduct q : ℤ) - lastProduct p
  let rawV (z' : ℤ × ℤ) : ℂ :=
    if forward then
      rawMultiplier F S D (lastProduct q) (lastProduct p) (quotient z')
    else
      star (rawMultiplier F S D (lastProduct p) (lastProduct q) (quotient z'))
  let compV (z' : ℤ × ℤ) : ℂ :=
    if forward then
      comparisonMultiplier F S D (lastProduct q) (lastProduct p) (quotient z')
    else
      star (comparisonMultiplier F S D (lastProduct p) (lastProduct q) (quotient z'))
  let valid := Z.filter fun z' => envBox S w z' ∧ (D : ℤ) ∣ det2 z z'
  let rawSupport := valid.filter fun z' => quotient z' = rawTarget
  let compSupport := valid.filter fun z' => |(quotient z' : ℝ)| ≤ R * S.Y
  let rawCost := E ^ 2 * P
  let T := Real.rpow (Real.log S.x) F.A₀
  let compCost := E ^ 2 * (32 * P * T ^ 3 / S.Y)
  have hsplit (z' : ℤ × ℤ) :
      ‖edgeMultiplier F S forward true p q z z'‖ +
          ‖edgeMultiplier F S forward false p q z z'‖ =
        ‖rawV z'‖ + ‖compV z'‖ := by
    cases forward <;> simp [edgeMultiplier, rawV, compV, quotient, D]
  have hDetQuot (z' : ℤ × ℤ) (hdiv : (D : ℤ) ∣ det2 z z') :
      det2 z z' = if forward then (D : ℤ) * quotient z' else
        -((D : ℤ) * quotient z') := by
    have hswap : det2 z' z = -det2 z z' := by simp [det2]; ring
    cases forward with
    | true =>
      dsimp [quotient]
      have h := Int.ediv_mul_cancel hdiv
      calc
        det2 z z' = (det2 z z' / (D : ℤ)) * (D : ℤ) := h.symm
        _ = (D : ℤ) * (det2 z z' / (D : ℤ)) := by ring
    | false =>
      have hdiv' : (D : ℤ) ∣ det2 z' z := by rw [hswap]; exact dvd_neg.mpr hdiv
      have h := Int.ediv_mul_cancel hdiv'
      calc
        det2 z z' = -det2 z' z := by rw [hswap]; ring
        _ = -((D : ℤ) * (det2 z' z / (D : ℤ))) := by
          congr 1
          calc
            det2 z' z = (det2 z' z / (D : ℤ)) * (D : ℤ) := h.symm
            _ = (D : ℤ) * (det2 z' z / (D : ℤ)) := by ring
  have hRawBound (z' : ℤ × ℤ) : ‖rawV z'‖ ≤ rawCost := by
    cases forward with
    | true =>
      simpa [rawV, quotient, rawCost, D] using
        (pd5_rawMultiplier_norm_le F S (sharedProduct p) (lastProduct q) (lastProduct p)
          (det2 z z' / (sharedProduct p : ℤ)) E P hd₀pos hD hE (by positivity) hEta hPsi)
    | false =>
      simpa [rawV, quotient, rawCost, D] using
        (pd5_rawMultiplier_norm_le F S (sharedProduct p) (lastProduct p) (lastProduct q)
          (det2 z' z / (sharedProduct p : ℤ)) E P hd₀pos hD hE (by positivity) hEta hPsi)
  have hRawZero (z' : ℤ × ℤ) (hne : quotient z' ≠ rawTarget) : rawV z' = 0 := by
    cases forward with
    | true =>
      have hne' : quotient z' ≠ (lastProduct p : ℤ) - lastProduct q := by
        simpa [rawTarget] using hne
      change rawMultiplier F S D (lastProduct q) (lastProduct p) (quotient z') = 0
      unfold rawMultiplier
      rw [if_neg hne']
      simp
    | false =>
      have hne' : quotient z' ≠ (lastProduct q : ℤ) - lastProduct p := by
        simpa [rawTarget] using hne
      change star (rawMultiplier F S D (lastProduct p) (lastProduct q) (quotient z')) = 0
      unfold rawMultiplier
      rw [if_neg hne']
      simp
  have hRawPoint (z' : ℤ × ℤ) :
      ‖rawV z'‖ ≤ if quotient z' = rawTarget then rawCost else 0 := by
    by_cases hq : quotient z' = rawTarget
    · simpa [hq] using hRawBound z'
    · simp [hq, hRawZero z' hq]
  have hCompBound (z' : ℤ × ℤ) : ‖compV z'‖ ≤ compCost := by
    cases forward with
    | true =>
      simpa [compV, quotient, compCost, T, D] using
        (pd5_comparisonMultiplier_norm_le F S (sharedProduct p) (lastProduct q) (lastProduct p)
          (det2 z z' / (sharedProduct p : ℤ)) E P hd₀pos hD hE (by positivity)
          hEta hPsi hxS2 hYone hTone hRad)
    | false =>
      simpa [compV, quotient, compCost, T, D] using
        (pd5_comparisonMultiplier_norm_le F S (sharedProduct p) (lastProduct p) (lastProduct q)
          (det2 z' z / (sharedProduct p : ℤ)) E P hd₀pos hD hE (by positivity)
          hEta hPsi hxS2 hYone hTone hRad)
  have hCompZero (z' : ℤ × ℤ)
      (hnot : ¬ |(quotient z' : ℝ)| ≤ R * S.Y) : compV z' = 0 := by
    have hsmall : R < |(quotient z' : ℝ)| / S.Y :=
      (lt_div_iff₀ hYpos).2 (lt_of_not_ge hnot)
    have hsmall' : R < |((quotient z' : ℝ) / S.Y)| := by
      have hEq : |((quotient z' : ℝ) / S.Y)| = |(quotient z' : ℝ)| / S.Y := by
        rw [abs_div, abs_of_pos hYpos]
      rw [hEq]
      exact hsmall
    have hpsi0 := hPsiZero ((quotient z' : ℝ) / S.Y) hsmall'
    have hKernelZero (a b : ℕ) : majorKernel S.x S.Y F.A₀ (quotient z' : ℝ)
        a b F.psi = 0 := by
      unfold majorKernel
      rw [hpsi0]
      simp
    cases forward with
    | true => simp [compV, comparisonMultiplier, hKernelZero]
    | false => simp [compV, comparisonMultiplier, hKernelZero]
  have hCompPoint (z' : ℤ × ℤ) :
      ‖compV z'‖ ≤ if |(quotient z' : ℝ)| ≤ R * S.Y then compCost else 0 := by
    by_cases hq : |(quotient z' : ℝ)| ≤ R * S.Y
    · simpa [hq] using hCompBound z'
    · simp [hq, hCompZero z' hq]
  have hSumEq :
      (∑ z' ∈ Z, if envBox S w z' ∧ (D : ℤ) ∣ det2 z z' then
        ‖edgeMultiplier F S forward true p q z z'‖ +
          ‖edgeMultiplier F S forward false p q z z'‖ else 0) =
        ∑ z' ∈ valid, (‖rawV z'‖ + ‖compV z'‖) := by
    calc
      _ = ∑ z' ∈ Z, if envBox S w z' ∧ (D : ℤ) ∣ det2 z z' then
            ‖rawV z'‖ + ‖compV z'‖ else 0 := by
              apply Finset.sum_congr rfl
              intro z' hz'
              by_cases hg : envBox S w z' ∧ (D : ℤ) ∣ det2 z z'
              · simp [hg, hsplit]
              · simp [hg]
      _ = ∑ z' ∈ valid, (‖rawV z'‖ + ‖compV z'‖) := by
            rw [← Finset.sum_filter]
  have hRawCardSubset : rawSupport ⊆
      Z.filter fun z' => envBox S w z' ∧
        det2 z z' = (if forward then (D : ℤ) * rawTarget else -((D : ℤ) * rawTarget)) := by
    intro z' hz'
    have hr := Finset.mem_filter.mp hz'
    have hv := Finset.mem_filter.mp hr.1
    have hdet := hDetQuot z' hv.2.2
    have hdet' : det2 z z' =
        (if forward then (D : ℤ) * rawTarget else -((D : ℤ) * rawTarget)) := by
      simpa [hr.2] using hdet
    exact Finset.mem_filter.mpr ⟨hv.1, ⟨hv.2.1, hdet'⟩⟩
  have hRawCard : rawSupport.card ≤ 18 := by
    calc
      rawSupport.card ≤ (Z.filter fun z' => envBox S w z' ∧
          det2 z z' = (if forward then (D : ℤ) * rawTarget else -((D : ℤ) * rawTarget))).card :=
        Finset.card_le_card hRawCardSubset
      _ ≤ 18 := pd5_fixed_det_positions_card S w z Z
        (if forward then (D : ℤ) * rawTarget else -((D : ℤ) * rawTarget))
        hUpos hu hz hzbox
  have hRawSum :
      (∑ z' ∈ valid, ‖rawV z'‖) ≤ rawCost * (rawSupport.card : ℝ) := by
    calc
      _ ≤ ∑ z' ∈ valid, if quotient z' = rawTarget then rawCost else 0 := by
        apply Finset.sum_le_sum
        intro z' hz'
        exact hRawPoint z'
      _ = ∑ z' ∈ rawSupport, rawCost := by
        rw [← Finset.sum_filter]
      _ = rawCost * (rawSupport.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  let X := R * S.Y
  let Tvals : Finset ℤ := Finset.Icc (-⌊X⌋) ⌊X⌋
  have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
  have hNnonneg : 0 ≤ ⌊X⌋ := (Int.floor_nonneg).2 hXnonneg
  have hNleX : (⌊X⌋ : ℝ) ≤ X := Int.floor_le X
  have hCompMaps : Set.MapsTo quotient (compSupport : Set (ℤ × ℤ)) (Tvals : Set ℤ) := by
    intro z' hz'
    have hc := Finset.mem_filter.mp hz'
    exact pd5_int_abs_mem_Icc X (quotient z') (by simpa [X] using hc.2)
  have hCardTInt : (Tvals.card : ℤ) = 2 * ⌊X⌋ + 1 := by
    dsimp [Tvals]
    rw [Int.card_Icc_of_le (-⌊X⌋) ⌊X⌋ (by omega)]
    ring
  have hCardTReal : (Tvals.card : ℝ) ≤ (2 * R + 1) * S.Y := by
    have hcast : (Tvals.card : ℝ) = 2 * (⌊X⌋ : ℝ) + 1 := by exact_mod_cast hCardTInt
    rw [hcast]
    dsimp [X] at hNleX
    nlinarith [hNleX, hYone]
  have hCompFiber (s : ℤ) :
      (compSupport.filter fun z' => quotient z' = s).card ≤ 18 := by
    let m : ℤ := if forward then (D : ℤ) * s else -((D : ℤ) * s)
    have hsubset : (compSupport.filter fun z' => quotient z' = s) ⊆
        Z.filter fun z' => envBox S w z' ∧ det2 z z' = m := by
      intro z' hz'
      have hq := Finset.mem_filter.mp hz'
      have hc := Finset.mem_filter.mp hq.1
      have hv := Finset.mem_filter.mp hc.1
      have hdet := hDetQuot z' hv.2.2
      have hdet' : det2 z z' = m := by simpa [m, hq.2] using hdet
      exact Finset.mem_filter.mpr ⟨hv.1, ⟨hv.2.1, hdet'⟩⟩
    exact (Finset.card_le_card hsubset).trans
      (pd5_fixed_det_positions_card S w z Z m hUpos hu hz hzbox)
  have hCompCardNat : compSupport.card ≤ 18 * Tvals.card := by
    rw [Finset.card_eq_sum_card_fiberwise hCompMaps]
    calc
      _ ≤ ∑ _s ∈ Tvals, 18 := by
        apply Finset.sum_le_sum
        intro s hs
        exact hCompFiber s
      _ = Tvals.card * 18 := by simp
      _ = 18 * Tvals.card := by omega
  have hCompCard : (compSupport.card : ℝ) ≤ 18 * ((2 * R + 1) * S.Y) := by
    calc
      (compSupport.card : ℝ) ≤ 18 * (Tvals.card : ℝ) := by exact_mod_cast hCompCardNat
      _ ≤ 18 * ((2 * R + 1) * S.Y) := by nlinarith [hCardTReal]
  have hCompSum :
      (∑ z' ∈ valid, ‖compV z'‖) ≤ compCost * (compSupport.card : ℝ) := by
    calc
      _ ≤ ∑ z' ∈ valid, if |(quotient z' : ℝ)| ≤ R * S.Y then compCost else 0 := by
        apply Finset.sum_le_sum
        intro z' hz'
        exact hCompPoint z'
      _ = ∑ z' ∈ compSupport, compCost := by rw [← Finset.sum_filter]
      _ = compCost * (compSupport.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hAllSum :
      (∑ z' ∈ Z, if envBox S w z' ∧ (D : ℤ) ∣ det2 z z' then
        ‖edgeMultiplier F S forward true p q z z'‖ +
          ‖edgeMultiplier F S forward false p q z z'‖ else 0) ≤
        18 * E ^ 2 * P * (1 + 32 * (2 * R + 1)) * T ^ 3 := by
    calc
      _ = (∑ z' ∈ valid, ‖rawV z'‖) + (∑ z' ∈ valid, ‖compV z'‖) := by
        rw [hSumEq, Finset.sum_add_distrib]
      _ ≤ rawCost * (rawSupport.card : ℝ) + compCost * (compSupport.card : ℝ) :=
        add_le_add hRawSum hCompSum
      _ ≤ rawCost * 18 * T ^ 3 + compCost * (18 * ((2 * R + 1) * S.Y)) := by
        have hTcube : 1 ≤ T ^ 3 := by
          calc
            1 = 1 ^ 3 := by norm_num
            _ ≤ T ^ 3 := by gcongr
        have hRawCoeff : 0 ≤ rawCost * 18 := by positivity
        have hRaw' : rawCost * (rawSupport.card : ℝ) ≤ rawCost * 18 * T ^ 3 := by
          calc
            _ ≤ rawCost * 18 := mul_le_mul_of_nonneg_left (by exact_mod_cast hRawCard) (by positivity)
            _ = rawCost * 18 * 1 := by ring
            _ ≤ rawCost * 18 * T ^ 3 := mul_le_mul_of_nonneg_left hTcube hRawCoeff
        have hComp' : compCost * (compSupport.card : ℝ) ≤
            compCost * (18 * ((2 * R + 1) * S.Y)) :=
          mul_le_mul_of_nonneg_left hCompCard (by positivity)
        exact add_le_add hRaw' hComp'
      _ = 18 * E ^ 2 * P * (1 + 32 * (2 * R + 1)) * T ^ 3 := by
        dsimp [rawCost, compCost]
        field_simp [ne_of_gt hYpos]
  have hTpow : T ^ 3 = Real.rpow S.L (3 * F.A₀) := by
    have hLnonneg : 0 ≤ S.L := by dsimp [PDScale.L]; linarith [hL]
    dsimp [T]
    calc
      (Real.rpow (Real.log S.x) F.A₀) ^ 3 =
          Real.rpow (Real.rpow (Real.log S.x) F.A₀) (3 : ℝ) :=
            (Real.rpow_natCast (Real.rpow (Real.log S.x) F.A₀) 3).symm
      _ = Real.rpow (Real.log S.x) (F.A₀ * 3) :=
            (Real.rpow_mul hLnonneg F.A₀ 3).symm
      _ = Real.rpow S.L (3 * F.A₀) := by
            rw [PDScale.L]
            congr 1
            ring
  calc
    _ ≤ 18 * E ^ 2 * P * (1 + 32 * (2 * R + 1)) * T ^ 3 := hAllSum
    _ = Cgeom * Real.rpow S.L (3 * F.A₀) := by
      rw [hTpow]

end
end ArtinPrimitiveRoots.TypeII.PD
