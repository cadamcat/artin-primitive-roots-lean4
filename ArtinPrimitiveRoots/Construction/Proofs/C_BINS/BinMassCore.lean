import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.BinReindex
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.GroupTail
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ConditionedAggregation
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.ReciprocalBin
import ArtinPrimitiveRoots.Construction.Proofs.C_BINS.LargePrime
import ArtinPrimitiveRoots.Construction.Proofs.C_BV.Mass
import ArtinPrimitiveRoots.Construction.Proofs.c1.SieveProductHelpers

namespace ArtinPrimitiveRoots.Proofs.c_bins_sol

open Classical Filter
open scoped Topology
open ArtinPrimitiveRoots.Construction ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Construction.Proofs.C_BINS

set_option maxHeartbeats 1000000 in
/-- The bin-mass conclusion from distribution, support, and small-group tail estimates. -/
theorem bin_mass_of_estimates
    (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (b κ ε γ γ' δtail : ℝ) (hM : 0 < M) (hc24 : c = 2 ∨ c = 4)
    (ha : ValidBands K a) (hΨ : IsTestFunction Ψ)
    (hb : 0 < b) (hκ : 0 < κ) (hκsmall : κ < 1 / 100)
    (hε : 0 < ε) (hεκ : ε < κ)
    (hγlo : b ≤ γ) (hγγ' : γ < γ') (hγhi : γ' ≤ 1 / 2 - κ)
    (hδtail : 0 < δtail)
    (c₀ C_A Ctail xMass xBV xTail xJ xSupport : ℝ)
    (hc₀ : 0 < c₀) (hCA : 0 < C_A) (hCtail : 0 < Ctail)
    (hMass : ∀ x : ℝ, xMass ≤ x →
      c₀ * x * groupHarmonicMass x K a / Real.log x ≤
        conTotalMass x M c u K a Ψ)
    (hBV : ∀ x : ℝ, xBV ≤ x →
      (∑ r ∈ (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
          (fun r => IsGroupInteger x K a r),
        ∑ ℓ ∈ oddSquarefreeUpTo (Real.rpow x (1 / 2 - κ / 2)),
          markedWeight x K a (1 / 2 : ℝ) r *
            |progressionPrimeSum x M c u Ψ r ℓ -
              localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|) ≤
        C_A * x * groupHarmonicMass x K a * Real.rpow (Real.log x) (-4 : ℝ))
    (hTail : ∀ x : ℝ, xTail ≤ x →
      |conTotalMass x M c u K a Ψ -
        (∑ r ∈ (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
            (fun r => IsGroupInteger x K a r),
          markedWeight x K a (1 / 2 : ℝ) r *
            progressionPrimeSum x M c u Ψ r 1)| ≤
        Ctail * x * Real.exp (-ε * Real.rpow (Real.log x) δtail))
    (hJ : ∀ x : ℝ, xJ ≤ x → 1 ≤ groupHarmonicMass x K a)
    (hSupport : ∀ x : ℝ, xSupport ≤ x → ∀ d,
      conWeight x M c u K a Ψ d ≠ 0 →
        x < (d : ℝ) ∧ (d : ℝ) < 2 * x ∧
          ∃ r Q : ℕ, d - 1 = c * r * Q ∧ Q.Prime ∧
            Real.rpow x (9 / 10 : ℝ) < (Q : ℝ) ∧
            IsGroupInteger x K a r ∧
            (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) ∧
            markedWeight x K a (1 / 2 : ℝ) (d - 1) =
              markedWeight x K a (1 / 2 : ℝ) r) :
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |primeDivisorBinSum x M c u K a Ψ γ γ' -
          (singularProduct M * conTotalMass x M c u K a Ψ *
            roughSieveProduct (roughCutoff x) * Real.log (γ' / γ))| ≤
          η * singularProduct M * conTotalMass x M c u K a Ψ *
            roughSieveProduct (roughCutoff x) := by
  classical
  intro η hη
  let S : ℝ := singularProduct M
  let E : ℝ := Real.exp (-Real.eulerMascheroniConstant)
  let Qlog : ℝ := Real.log (γ' / γ)
  have hS : 0 < S := singularProduct_pos M
  have hE : 0 < E := Real.exp_pos _
  have hγ : 0 < γ := hb.trans_le hγlo
  have hQ : 0 < Qlog := Real.log_pos ((one_lt_div hγ).mpr hγγ')
  have hQ1 : 0 < Qlog + 1 := by linarith only [hQ]
  let τ : ℝ := min (1 / 4 : ℝ) (η / (24 * (Qlog + 1)))
  let ρ : ℝ := min 1 (η / 8)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτsmall : τ ≤ 1 / 4 := min_le_left _ _
  have hτloss : τ ≤ η / (24 * (Qlog + 1)) := min_le_right _ _
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hρloss : ρ ≤ η / 8 := min_le_right _ _
  obtain ⟨Cblock, hCblock, hBlockBound⟩ := exists_localSieveBlockBound
  obtain ⟨Kblock, H₀, hKblock, hBlock⟩ := exists_blockApproximation Cblock
  let Cexp : ℝ := 16 * Kblock * (Qlog + 1) / η
  have hCexp : 0 < Cexp := by dsimp [Cexp]; positivity
  obtain ⟨Nblock, hNblock⟩ := exists_nat_gt (max (H₀ : ℝ) (Real.log Cexp))
  let H : ℕ := 2 * Nblock
  have hEvenH : Even H := ⟨Nblock, by dsimp [H]; ring⟩
  have hH₀N : H₀ ≤ Nblock := by
    exact_mod_cast ((le_max_left (H₀ : ℝ) (Real.log Cexp)).trans hNblock.le)
  have hH₀ : H₀ ≤ H := by dsimp [H]; omega
  have hHlog : Real.log Cexp ≤ (H : ℝ) := by
    have h := (le_max_right (H₀ : ℝ) (Real.log Cexp)).trans hNblock.le
    dsimp [H]
    push_cast
    linarith only [h, (Nat.cast_nonneg Nblock : (0 : ℝ) ≤ (Nblock : ℝ))]
  have hAlphaSmall : Kblock * Real.exp (-(H : ℝ)) ≤ η / (16 * (Qlog + 1)) := by
    have hExp := Real.exp_le_exp.mpr (neg_le_neg hHlog)
    have hInv : Real.exp (-Real.log Cexp) = η / (16 * Kblock * (Qlog + 1)) := by
      rw [Real.exp_neg, Real.exp_log hCexp]
      dsimp [Cexp]
      exact inv_div _ _
    rw [hInv] at hExp
    calc
      _ ≤ Kblock * (η / (16 * Kblock * (Qlog + 1))) :=
        mul_le_mul_of_nonneg_left hExp hKblock.le
      _ = _ := by field_simp [ne_of_gt hKblock, ne_of_gt hQ1]
  obtain ⟨xCut, hxCut₂, hCut⟩ := fixed_block_cutoff κ hκ H
  obtain ⟨xPrime, hxPrime₂, hPrime⟩ := large_prime_coprime_group M K a b hM ha hb
  obtain ⟨xRecip, hxRecip₂, hRecip⟩ := reciprocal_prime_bin γ γ' hγ hγγ' ρ hρ
  obtain ⟨yProduct, hyProduct₂, hProduct⟩ := progressionSieveProduct_relative M hM τ hτ
  obtain ⟨xGroup, hxGroup₂, hGroup⟩ := progressionSieveProductFor_relative M K a ha
  obtain ⟨yMertens, hyMertens, hMertens⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.2 (E / 2) (by positivity)
  have hWtop : Tendsto roughCutoff atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : 0 < (24 / 100 : ℝ))).comp
        Real.tendsto_log_atTop)
  have hDecay : Tendsto (fun x : ℝ =>
      Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
        Real.tendsto_log_atTop)
  obtain ⟨xDecay, hDecayAt⟩ := eventually_atTop.mp (hDecay.eventually (gt_mem_nhds hτ))
  obtain ⟨xTailRel, hTailRel⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_logPower_exp_small
      (Ctail / c₀) ε δtail τ hε hδtail hτ
  let Cnorm : ℝ := 16 * Ctail / (b * S * c₀ * E)
  have hCnorm : 0 ≤ Cnorm := by dsimp [Cnorm]; positivity
  obtain ⟨xTailNorm, hTailNorm⟩ :=
    ArtinPrimitiveRoots.Construction.ProofsC2.exists_logPower_exp_small
      (Real.sqrt Cnorm) (ε / 2) δtail (Real.sqrt η)
        (by positivity) hδtail (Real.sqrt_pos.mpr hη)
  let Tbound : ℝ := 8 * Kblock * C_A / (η * S * c₀ * E)
  have hTbound : 0 ≤ Tbound := by dsimp [Tbound]; positivity
  let Lreq : ℝ := max ((4 : ℝ) ^ 10) (Real.sqrt Tbound)
  let yReq : ℝ := max 2 (max yProduct yMertens)
  have hFinal : ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧
      |primeDivisorBinSum x M c u K a Ψ γ γ' -
          (S * conTotalMass x M c u K a Ψ * roughSieveProduct (roughCutoff x) * Qlog)| ≤
        η * S * conTotalMass x M c u K a Ψ * roughSieveProduct (roughCutoff x) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop xMass,
      eventually_ge_atTop xBV, eventually_ge_atTop xTail, eventually_ge_atTop xJ,
      eventually_ge_atTop xSupport, eventually_ge_atTop xCut, eventually_ge_atTop xPrime,
      eventually_ge_atTop xRecip, eventually_ge_atTop xGroup, eventually_ge_atTop xDecay,
      eventually_ge_atTop xTailRel, eventually_ge_atTop xTailNorm,
      Real.tendsto_log_atTop.eventually_ge_atTop Lreq, hWtop.eventually_ge_atTop yReq]
      with x hx₂ hxMass hxBV hxTail hxJ hxSupport hxCut hxPrime hxRecip hxGroup hxDecay
        hxTailRel hxTailNorm hxLog hxW
    refine ⟨hx₂, ?_⟩
    have hxpos : 0 < x := by linarith only [hx₂]
    have hxone : 1 ≤ x := by linarith only [hx₂]
    let L : ℝ := Real.log x
    let W : ℝ := roughCutoff x
    let V : ℝ := roughSieveProduct W
    let D : ℝ := Real.rpow x (1 / 2 - κ / 2)
    let Rall := (Finset.range (⌊2 * x⌋₊ + 1)).filter (fun r => IsGroupInteger x K a r)
    let Rsmall := (Finset.range (⌊Real.rpow x ε⌋₊ + 1)).filter
      (fun r => IsGroupInteger x K a r)
    let N := (primesUpTo (Real.rpow x γ')).filter
      (fun n : ℕ => Real.rpow x γ < (n : ℝ))
    let wr : ℕ → ℝ := fun r => markedWeight x K a (1 / 2 : ℝ) r
    let Ar : ℕ → ℝ := fun r => progressionPrimeSum x M c u Ψ r 1
    let Zr : ℕ → ℝ := fun r => ∑ n ∈ N,
      conditionedSiftedProgressionPrimeSum x M c u Ψ r n W
    let X0 : ℝ := conTotalMass x M c u K a Ψ
    let Xsmall : ℝ := ∑ r ∈ Rsmall, wr r * Ar r
    let Bmain : ℝ := ∑ r ∈ Rsmall, wr r * Ar r * progressionSieveProductFor M r W
    let T : ℝ := ∑ n ∈ N, 1 / ((n : ℝ) - 1)
    let Zsmall : ℝ := ∑ r ∈ Rsmall, wr r * Zr r
    let ErrTotal : ℝ := ∑ r ∈ Rsmall, ∑ ℓ ∈ oddSquarefreeUpTo D,
      wr r * |progressionPrimeSum x M c u Ψ r ℓ -
        localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1|
    let J : ℝ := groupHarmonicMass x K a
    let Scale : ℝ := S * X0 * V
    have hLlarge : (4 : ℝ) ^ 10 ≤ L := (le_max_left _ _).trans hxLog
    have hLone : 1 ≤ L := by norm_num at hLlarge ⊢; linarith only [hLlarge]
    have hLpos : 0 < L := by linarith only [hLone]
    have hW₂ : 2 ≤ W := (le_max_left _ _).trans hxW
    have hWyP : yProduct ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hxW)
    have hWyM : yMertens ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hxW)
    have hVnonneg : 0 ≤ V := roughSieveProduct_nonneg W
    have hX0nonneg : 0 ≤ X0 := conTotalMass_nonneg x M c u K a Ψ hΨ
    have hScaleNonneg : 0 ≤ Scale := mul_nonneg (mul_nonneg hS.le hX0nonneg) hVnonneg
    have hJlower : 1 ≤ J := hJ x hxJ
    have hJnonneg : 0 ≤ J := (by norm_num : (0 : ℝ) ≤ 1).trans hJlower
    have hMassLower : c₀ * x * J / L ≤ X0 := hMass x hxMass
    have hWr (r : ℕ) : 0 ≤ wr r := markedWeight_nonneg x K a (1 / 2 : ℝ) r (by norm_num)
    have hAr (r : ℕ) : 0 ≤ Ar r := by
      unfold Ar progressionPrimeSum
      exact Finset.sum_nonneg (fun Q hQ => hΨ.2.2.1 _)
    have hZr (r : ℕ) : 0 ≤ Zr r := by
      apply Finset.sum_nonneg
      intro n hn
      unfold conditionedSiftedProgressionPrimeSum
      apply Finset.sum_nonneg
      intro Q hQ
      split_ifs <;> first | exact hΨ.2.2.1 _ | exact le_rfl
    have hRsmallBounds (r : ℕ) (hr : r ∈ Rsmall) :
        IsGroupInteger x K a r ∧ (r : ℝ) ≤ Real.rpow x ε := by
      rcases Finset.mem_filter.mp hr with ⟨hrRange, hrGroup⟩
      have hrFloor : r ≤ ⌊Real.rpow x ε⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hrRange)
      have hrCast : (r : ℝ) ≤ (⌊Real.rpow x ε⌋₊ : ℝ) := by exact_mod_cast hrFloor
      exact ⟨hrGroup, hrCast.trans (Nat.floor_le (Real.rpow_nonneg hxpos.le ε))⟩
    have hεsmall : ε < (11 / 100 : ℝ) := by linarith only [hεκ, hκsmall]
    have hεone : ε ≤ 1 := by linarith only [hεsmall]
    have hRsub : Rsmall ⊆ Rall := by
      intro r hr
      have hrBound := hRsmallBounds r hr
      have hrMax : (r : ℝ) ≤ 2 * x := by
        calc
          _ ≤ Real.rpow x ε := hrBound.2
          _ ≤ x := Real.rpow_le_self_of_one_le hxone hεone
          _ ≤ 2 * x := by linarith only [hxpos]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), hrBound.1⟩
      exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).mpr hrMax
    have hMassAll : X0 = ∑ r ∈ Rall, wr r * Ar r :=
      ArtinPrimitiveRoots.Proofs.C_BV.conTotalMass_eq_groupProgressionSum
        x M c u K a Ψ hc24 hx₂ hxpos hLlarge ha hΨ.2.1 (hSupport x hxSupport)
    have hBinAll : primeDivisorBinSum x M c u K a Ψ γ γ' =
        ∑ r ∈ Rall, wr r * Zr r :=
      prime_divisor_bin_group_reindex x M c u K a Ψ γ γ'
        hc24 hx₂ hLlarge ha hΨ.2.1 (hSupport x hxSupport)
    have hXdiff : X0 - Xsmall = ∑ r ∈ Rall \ Rsmall, wr r * Ar r := by
      rw [hMassAll]
      exact (Finset.sum_sdiff_eq_sub hRsub).symm
    have hXdiffNonneg : 0 ≤ X0 - Xsmall := by
      rw [hXdiff]
      exact Finset.sum_nonneg (fun r hr => mul_nonneg (hWr r) (hAr r))
    have hXsmallUpper : Xsmall ≤ X0 := sub_nonneg.mp hXdiffNonneg
    have hXsmallNonneg : 0 ≤ Xsmall :=
      Finset.sum_nonneg (fun r hr => mul_nonneg (hWr r) (hAr r))
    have hNfacts (n : ℕ) (hn : n ∈ N) :
        n.Prime ∧ Real.rpow x b < (n : ℝ) ∧ (n : ℝ) ≤ Real.rpow x γ' := by
      rcases Finset.mem_filter.mp hn with ⟨hnP, hnLo⟩
      rcases Finset.mem_filter.mp hnP with ⟨hnRange, hnPrime⟩
      have hnFloor : n ≤ ⌊Real.rpow x γ'⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hnRange)
      have hnCast : (n : ℝ) ≤ (⌊Real.rpow x γ'⌋₊ : ℝ) := by exact_mod_cast hnFloor
      exact ⟨hnPrime, (Real.rpow_le_rpow_of_exponent_le hxone hγlo).trans_lt hnLo,
        hnCast.trans (Nat.floor_le (Real.rpow_nonneg hxpos.le γ'))⟩
    have hTnonneg : 0 ≤ T := by
      apply Finset.sum_nonneg
      intro n hn
      have hnTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (hNfacts n hn).1.two_le
      exact one_div_nonneg.mpr (by linarith only [hnTwo])
    have hTdiff : |T - Qlog| ≤ ρ := hRecip x hxRecip
    have hTcap : T ≤ Qlog + 1 := by
      have hUpper := (abs_le.mp hTdiff).2
      linarith only [hUpper, hρone]
    have hZdiff : primeDivisorBinSum x M c u K a Ψ γ γ' - Zsmall =
        ∑ r ∈ Rall \ Rsmall, wr r * Zr r := by
      rw [hBinAll]
      exact (Finset.sum_sdiff_eq_sub hRsub).symm
    have hZdiffNonneg : 0 ≤ primeDivisorBinSum x M c u K a Ψ γ γ' - Zsmall := by
      rw [hZdiff]
      exact Finset.sum_nonneg (fun r hr => mul_nonneg (hWr r) (hZr r))
    have hBinTailRaw : |primeDivisorBinSum x M c u K a Ψ γ γ' - Zsmall| ≤
        (2 / b) * (X0 - Xsmall) := by
      rw [abs_of_nonneg hZdiffNonneg, hZdiff, hXdiff, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have hPer := conditioned_group_bin_sum_le M c u Ψ r N x W b hx₂ hb hΨ
        (fun n hn => ⟨(hNfacts n hn).1, (hNfacts n hn).2.1⟩)
      have h := mul_le_mul_of_nonneg_left hPer (hWr r)
      simpa only [wr, Zr, Ar, mul_left_comm] using h
    have hTailBound : |X0 - Xsmall| ≤ Ctail * x * Real.exp (-ε * Real.rpow L δtail) :=
      hTail x hxTail
    have hLogW : Real.log W = Real.rpow L (24 / 100 : ℝ) := by
      simp [W, roughCutoff, L]
    have hLogWle : Real.log W ≤ L := by
      rw [hLogW]
      exact Real.rpow_le_self_of_one_le hLone (by norm_num)
    have hMertensLower : E / 2 ≤ V * Real.log W := by
      have h := (abs_le.mp (hMertens W hWyM)).1
      linarith only [h]
    have hVLower : E / (2 * L) ≤ V := by
      have h := hMertensLower.trans (mul_le_mul_of_nonneg_left hLogWle hVnonneg)
      apply (div_le_iff₀ (mul_pos (by norm_num) hLpos)).mpr
      nlinarith only [h]
    have hScaleLower : S * c₀ * E * (x * J) / (2 * L ^ 2) ≤ Scale := by
      have h := mul_le_mul hMassLower hVLower (by positivity : 0 ≤ E / (2 * L)) hX0nonneg
      have hs := mul_le_mul_of_nonneg_left h hS.le
      calc
        _ = S * ((c₀ * x * J / L) * (E / (2 * L))) := by
          field_simp [ne_of_gt hLpos] <;> ring
        _ ≤ S * (X0 * V) := hs
        _ = Scale := by dsimp [Scale]; ring
    have hTailRelMul : Ctail * (L * Real.exp (-ε * Real.rpow L δtail)) ≤ τ * c₀ := by
      have h := mul_le_mul_of_nonneg_left (hTailRel x hxTailRel) hc₀.le
      have hEq : c₀ * ((Ctail / c₀) * (L * Real.exp (-ε * Real.rpow L δtail))) =
          Ctail * (L * Real.exp (-ε * Real.rpow L δtail)) := by field_simp [ne_of_gt hc₀]
      rw [hEq] at h
      simpa only [mul_comm] using h
    have hTailRelPer : Ctail * Real.exp (-ε * Real.rpow L δtail) ≤ τ * c₀ / L := by
      apply (le_div_iff₀ hLpos).mpr
      convert hTailRelMul using 1 <;> ring
    have hBaseMass : c₀ * x / L ≤ X0 := by
      calc
        c₀ * x / L ≤ c₀ * x * J / L := by
          apply div_le_div_of_nonneg_right _ hLpos.le
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hJlower (by positivity : 0 ≤ c₀ * x)
        _ ≤ X0 := hMassLower
    have hTailRelScaled : Ctail * x * Real.exp (-ε * Real.rpow L δtail) ≤ τ * X0 := by
      calc
        _ = (Ctail * Real.exp (-ε * Real.rpow L δtail)) * x := by ring
        _ ≤ (τ * c₀ / L) * x := mul_le_mul_of_nonneg_right hTailRelPer hxpos.le
        _ = τ * (c₀ * x / L) := by ring
        _ ≤ τ * X0 := mul_le_mul_of_nonneg_left hBaseMass hτ.le
    have hXsmallLower : (1 - τ) * X0 ≤ Xsmall := by
      have h := (abs_le.mp hTailBound).2.trans hTailRelScaled
      linarith only [h]
    have hTailSquare : Cnorm * L ^ 2 * Real.exp (-ε * Real.rpow L δtail) ≤ η := by
      have hSmall := hTailNorm x hxTailNorm
      have hSq := mul_self_le_mul_self
        (by positivity : 0 ≤ Real.sqrt Cnorm * (L * Real.exp (-(ε / 2) * Real.rpow L δtail)))
        hSmall
      rw [← pow_two, ← pow_two, Real.sq_sqrt hη.le] at hSq
      have hExpSq : (Real.exp (-(ε / 2) * Real.rpow L δtail)) ^ 2 =
          Real.exp (-ε * Real.rpow L δtail) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, mul_pow, Real.sq_sqrt hCnorm, hExpSq] at hSq
      simpa only [mul_assoc] using hSq
    have hTailNum : 16 * Ctail * (L ^ 2 * Real.exp (-ε * Real.rpow L δtail)) ≤
        η * (b * S * c₀ * E) := by
      apply (div_le_iff₀ (by positivity : 0 < b * S * c₀ * E)).mp
      convert hTailSquare using 1 <;> dsimp [Cnorm] <;> ring
    have hTailCoeff : (2 / b) * Ctail * Real.exp (-ε * Real.rpow L δtail) ≤
        η * S * c₀ * E / (8 * L ^ 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 8 * L ^ 2)).mpr
      have hEq : ((2 / b) * Ctail * Real.exp (-ε * Real.rpow L δtail)) * (8 * L ^ 2) =
          (16 * Ctail * (L ^ 2 * Real.exp (-ε * Real.rpow L δtail))) / b := by ring
      rw [hEq]
      apply (div_le_iff₀ hb).mpr
      convert hTailNum using 1 <;> ring
    have hBinTail : |primeDivisorBinSum x M c u K a Ψ γ γ' - Zsmall| ≤
        (η / 4) * Scale := by
      calc
        _ ≤ (2 / b) * (X0 - Xsmall) := hBinTailRaw
        _ ≤ (2 / b) * (Ctail * x * Real.exp (-ε * Real.rpow L δtail)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 / b)
          exact (abs_le.mp hTailBound).2
        _ = ((2 / b) * Ctail * Real.exp (-ε * Real.rpow L δtail)) * x := by ring
        _ ≤ (η * S * c₀ * E / (8 * L ^ 2)) * x :=
          mul_le_mul_of_nonneg_right hTailCoeff hxpos.le
        _ ≤ (η * S * c₀ * E / (8 * L ^ 2)) * (x * J) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hJlower hxpos.le
        _ = (η / 4) * (S * c₀ * E * (x * J) / (2 * L ^ 2)) := by ring
        _ ≤ (η / 4) * Scale := mul_le_mul_of_nonneg_left hScaleLower (by positivity)
    have hSqrtLe : Real.sqrt Tbound ≤ L := (le_max_right _ _).trans hxLog
    have hSquare : Tbound ≤ L ^ 2 := by
      have h := mul_self_le_mul_self (Real.sqrt_nonneg Tbound) hSqrtLe
      simpa only [← pow_two, Real.sq_sqrt hTbound] using h
    have hBVNum : 8 * Kblock * C_A ≤ η * S * c₀ * E * L ^ 2 := by
      have h := (div_le_iff₀ (by positivity : 0 < η * S * c₀ * E)).mp hSquare
      convert h using 1 <;> ring
    have hBVDen : Kblock * C_A / L ^ 4 ≤ (η / 4) * (S * c₀ * E / (2 * L ^ 2)) := by
      apply (div_le_iff₀ (pow_pos hLpos 4)).mpr
      have hEq : ((η / 4) * (S * c₀ * E / (2 * L ^ 2))) * L ^ 4 =
          η * S * c₀ * E * L ^ 2 / 8 := by field_simp [ne_of_gt hLpos] <;> ring
      rw [hEq]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
      convert hBVNum using 1 <;> ring
    have hRpowNeg : Real.rpow L (-4 : ℝ) = 1 / L ^ 4 := by
      have hPower : Real.rpow L (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
      calc
        _ = (Real.rpow L (4 : ℝ))⁻¹ := Real.rpow_neg hLpos.le (4 : ℝ)
        _ = (L ^ 4)⁻¹ := congrArg (fun t : ℝ => t⁻¹) hPower
        _ = _ := (one_div _).symm
    have hErrDiv : ErrTotal ≤ C_A * x * J / L ^ 4 := by
      have h := hBV x hxBV
      change ErrTotal ≤ C_A * x * J * Real.rpow L (-4 : ℝ) at h
      rw [hRpowNeg, mul_one_div] at h
      exact h
    have hBVLoss : Kblock * ErrTotal ≤ (η / 4) * Scale := by
      calc
        _ ≤ Kblock * (C_A * x * J / L ^ 4) := mul_le_mul_of_nonneg_left hErrDiv hKblock.le
        _ = (Kblock * C_A / L ^ 4) * (x * J) := by ring
        _ ≤ ((η / 4) * (S * c₀ * E / (2 * L ^ 2))) * (x * J) :=
          mul_le_mul_of_nonneg_right hBVDen (mul_nonneg hxpos.le hJnonneg)
        _ = (η / 4) * (S * c₀ * E * (x * J) / (2 * L ^ 2)) := by ring
        _ ≤ (η / 4) * Scale := mul_le_mul_of_nonneg_left hScaleLower (by positivity)
    have hPnonneg : 0 ≤ progressionSieveProduct M W := progressionSieveProduct_nonneg M W
    have hPclose := abs_le.mp (hProduct W hWyP)
    have hPlower : (1 - τ) * (S * V) ≤ progressionSieveProduct M W := by
      linarith only [hPclose.1]
    have hPupper : progressionSieveProduct M W ≤ (1 + τ) * (S * V) := by
      linarith only [hPclose.2]
    have hDecaySmall : Real.exp (-Real.rpow L (1 / 10 : ℝ)) ≤ τ := (hDecayAt x hxDecay).le
    have hMinusNonneg : 0 ≤ 1 - τ := by linarith only [hτsmall]
    have hPlusNonneg : 0 ≤ 1 + τ := by linarith only [hτ]
    have hVfor (r : ℕ) (hr : r ∈ Rsmall) :
        (1 - τ) ^ 2 * S * V ≤ progressionSieveProductFor M r W ∧
          progressionSieveProductFor M r W ≤ (1 + τ) ^ 2 * S * V := by
      have hBounds := hRsmallBounds r hr
      have hrGroupMax : (r : ℝ) ≤ Real.rpow x (11 / 100 : ℝ) :=
        hBounds.2.trans (Real.rpow_le_rpow_of_exponent_le hxone hεsmall.le)
      have hCorr := abs_le.mp (hGroup x hxGroup r hBounds.1 hrGroupMax W hW₂)
      have hLoss := mul_le_mul_of_nonneg_right hDecaySmall hPnonneg
      have hVlow : (1 - τ) * progressionSieveProduct M W ≤ progressionSieveProductFor M r W := by
        linarith only [hCorr.1, hLoss]
      have hVhigh : progressionSieveProductFor M r W ≤ (1 + τ) * progressionSieveProduct M W := by
        linarith only [hCorr.2, hLoss]
      constructor
      · calc
          _ = (1 - τ) * ((1 - τ) * (S * V)) := by ring
          _ ≤ (1 - τ) * progressionSieveProduct M W :=
            mul_le_mul_of_nonneg_left hPlower hMinusNonneg
          _ ≤ _ := hVlow
      · calc
          _ ≤ (1 + τ) * progressionSieveProduct M W := hVhigh
          _ ≤ (1 + τ) * ((1 + τ) * (S * V)) :=
            mul_le_mul_of_nonneg_left hPupper hPlusNonneg
          _ = _ := by ring
    have hBLowerSmall : ((1 - τ) ^ 2 * S * V) * Xsmall ≤ Bmain := by
      dsimp [Xsmall, Bmain]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have h := mul_le_mul_of_nonneg_left (hVfor r hr).1 (mul_nonneg (hWr r) (hAr r))
      convert h using 1 <;> ring
    have hBUpperSmall : Bmain ≤ ((1 + τ) ^ 2 * S * V) * Xsmall := by
      dsimp [Xsmall, Bmain]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r hr
      have h := mul_le_mul_of_nonneg_left (hVfor r hr).2 (mul_nonneg (hWr r) (hAr r))
      convert h using 1 <;> ring
    have hBLower : (1 - τ) ^ 3 * Scale ≤ Bmain := by
      calc
        _ = ((1 - τ) ^ 2 * S * V) * ((1 - τ) * X0) := by dsimp [Scale]; ring
        _ ≤ ((1 - τ) ^ 2 * S * V) * Xsmall :=
          mul_le_mul_of_nonneg_left hXsmallLower (by positivity)
        _ ≤ Bmain := hBLowerSmall
    have hBUpper : Bmain ≤ (1 + τ) ^ 2 * Scale := by
      calc
        _ ≤ ((1 + τ) ^ 2 * S * V) * Xsmall := hBUpperSmall
        _ ≤ ((1 + τ) ^ 2 * S * V) * X0 :=
          mul_le_mul_of_nonneg_left hXsmallUpper (by positivity)
        _ = _ := by dsimp [Scale]; ring
    have hTauOne : τ ≤ 1 := by linarith only [hτsmall]
    have hTauSq : τ ^ 2 ≤ τ := by nlinarith only [hτ.le, hTauOne]
    have hTauCube : τ ^ 3 ≤ τ ^ 2 := by
      calc
        _ = τ ^ 2 * τ := by ring
        _ ≤ τ ^ 2 * 1 := mul_le_mul_of_nonneg_left hTauOne (sq_nonneg τ)
        _ = _ := by ring
    have hScalarLower : 1 - 3 * τ ≤ (1 - τ) ^ 3 := by
      nlinarith only [hTauCube, sq_nonneg τ]
    have hScalarUpper : (1 + τ) ^ 2 ≤ 1 + 3 * τ := by nlinarith only [hTauSq]
    have hBdiff : |Bmain - Scale| ≤ 3 * τ * Scale := by
      have hLow := (mul_le_mul_of_nonneg_right hScalarLower hScaleNonneg).trans hBLower
      have hHigh := hBUpper.trans (mul_le_mul_of_nonneg_right hScalarUpper hScaleNonneg)
      exact abs_le.mpr ⟨by linarith only [hLow], by linarith only [hHigh]⟩
    have hBnonneg : 0 ≤ Bmain :=
      (by positivity : 0 ≤ (1 - τ) ^ 3 * Scale).trans hBLower
    have hBcap : Bmain ≤ 4 * Scale := by
      have h := (abs_le.mp hBdiff).2
      have hτ3 : 3 * τ ≤ 3 := by linarith only [hTauOne]
      have hMul := mul_le_mul_of_nonneg_right hτ3 hScaleNonneg
      linarith only [h, hMul]
    have hCutN (n : ℕ) (hn : n ∈ N) : (n : ℝ) * W ^ (4 * H + 2) ≤ D := by
      calc
        _ ≤ Real.rpow x γ' * Real.rpow x (κ / 2) :=
          mul_le_mul (hNfacts n hn).2.2 (hCut x hxCut)
            (by positivity : 0 ≤ W ^ (4 * H + 2)) (Real.rpow_nonneg hxpos.le γ')
        _ = Real.rpow x (γ' + κ / 2) := (Real.rpow_add hxpos γ' (κ / 2)).symm
        _ ≤ D := Real.rpow_le_rpow_of_exponent_le hxone (by linarith only [hγhi])
    have hPerSieve (r : ℕ) (hr : r ∈ Rsmall) :
        |Zr r - Ar r * progressionSieveProductFor M r W * T| ≤
          (Kblock * Real.exp (-(H : ℝ))) * (Ar r * progressionSieveProductFor M r W * T) +
          Kblock * ∑ ℓ ∈ oddSquarefreeUpTo D,
            |progressionPrimeSum x M c u Ψ r ℓ -
              localSieveDensity M r ℓ * progressionPrimeSum x M c u Ψ r 1| := by
      have hConditionedN : ∀ n ∈ N, n.Prime ∧ W < (n : ℝ) ∧ Nat.Coprime n (M * r) := by
        intro n hn
        have h := hPrime x hxPrime n (hNfacts n hn).1 (hNfacts n hn).2.1
        exact ⟨(hNfacts n hn).1, h.1, h.2 r (hRsmallBounds r hr).1⟩
      have hBlockSum : ∀ v : ℝ, 1 < v →
          (∑ p ∈ ((primesUpTo W).filter (fun p : ℕ => 2 < p)).filter
              (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2),
            localSieveDensity M r p) ≤ Cblock := by
        intro v hv
        have hPrimes : ∀ p ∈ (primesUpTo W).filter (fun p : ℕ => 2 < p), p.Prime := by
          intro p hp
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hThree : ∀ p ∈ (primesUpTo W).filter (fun p : ℕ => 2 < p), 3 ≤ p := by
          intro p hp
          have h := (Finset.mem_filter.mp hp).2
          omega
        exact hBlockBound ((primesUpTo W).filter (fun p : ℕ => 2 < p)) hPrimes v hv r M hThree
      exact conditioned_bin_sieve_approx M c u Ψ r N x W D Kblock Cblock H H₀
        hKblock hBlock hc24 hΨ hW₂ (Real.rpow_nonneg hxpos.le _)
          hConditionedN hBlockSum hCutN hEvenH hH₀
    have hSmallSieve : |Zsmall - Bmain * T| ≤
        (Kblock * Real.exp (-(H : ℝ))) * (Bmain * T) + Kblock * ErrTotal :=
      weighted_conditioned_sieve_sum_approx M c u K a Ψ Rsmall N x W D
        (Kblock * Real.exp (-(H : ℝ))) Kblock hPerSieve
    have hMainCap : Bmain * T ≤ 4 * Scale * (Qlog + 1) :=
      mul_le_mul hBcap hTcap hTnonneg (by positivity)
    have hBlockLoss : (Kblock * Real.exp (-(H : ℝ))) * (Bmain * T) ≤
        (η / 4) * Scale := by
      calc
        _ ≤ (Kblock * Real.exp (-(H : ℝ))) * (4 * Scale * (Qlog + 1)) :=
          mul_le_mul_of_nonneg_left hMainCap (by positivity)
        _ ≤ (η / (16 * (Qlog + 1))) * (4 * Scale * (Qlog + 1)) :=
          mul_le_mul_of_nonneg_right hAlphaSmall (by positivity)
        _ = _ := by field_simp [ne_of_gt hQ1] <;> ring
    have hTauBudget : 3 * τ * (Qlog + 1) ≤ η / 8 := by
      have h := (le_div_iff₀ (by positivity : 0 < 24 * (Qlog + 1))).mp hτloss
      nlinarith only [h]
    have hProductLoss : |Bmain * T - Scale * Qlog| ≤ (η / 4) * Scale := by
      calc
        _ = |(Bmain - Scale) * T + Scale * (T - Qlog)| := by congr 1; ring
        _ ≤ |(Bmain - Scale) * T| + |Scale * (T - Qlog)| := abs_add_le _ _
        _ = |Bmain - Scale| * T + Scale * |T - Qlog| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hTnonneg, abs_of_nonneg hScaleNonneg]
        _ ≤ (3 * τ * Scale) * T + Scale * ρ :=
          add_le_add (mul_le_mul_of_nonneg_right hBdiff hTnonneg)
            (mul_le_mul_of_nonneg_left hTdiff hScaleNonneg)
        _ = Scale * (3 * τ * T + ρ) := by ring
        _ ≤ Scale * (3 * τ * (Qlog + 1) + ρ) := by
          apply mul_le_mul_of_nonneg_left _ hScaleNonneg
          exact add_le_add (mul_le_mul_of_nonneg_left hTcap (by positivity : 0 ≤ 3 * τ)) (le_refl ρ)
        _ ≤ Scale * (η / 8 + η / 8) :=
          mul_le_mul_of_nonneg_left (add_le_add hTauBudget hρloss) hScaleNonneg
        _ = _ := by ring
    have hTriangle₁ := abs_sub_le
      (primeDivisorBinSum x M c u K a Ψ γ γ') Zsmall (Scale * Qlog)
    have hTriangle₂ := abs_sub_le Zsmall (Bmain * T) (Scale * Qlog)
    have hResult : |primeDivisorBinSum x M c u K a Ψ γ γ' - Scale * Qlog| ≤ η * Scale := by
      linarith only [hTriangle₁, hTriangle₂, hBinTail, hSmallSieve,
        hBlockLoss, hBVLoss, hProductLoss]
    simpa only [Scale, X0, V, W, mul_assoc] using hResult
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hFinal
  refine ⟨max 2 x₀, le_max_left _ _, ?_⟩
  intro x hx
  have h := (hx₀ x ((le_max_right _ _).trans hx)).2
  simpa only [S, Qlog] using h

end ArtinPrimitiveRoots.Proofs.c_bins_sol
