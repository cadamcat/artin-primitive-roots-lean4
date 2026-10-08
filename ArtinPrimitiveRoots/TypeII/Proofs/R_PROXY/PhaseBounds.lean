import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.TruncatedSource
import ArtinPrimitiveRoots.TypeII.PP.Results
import Mathlib.Algebra.Order.Chebyshev

/-!
Finite Abel weighting tools for the reciprocal-log Type II source.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- A complex sum inherits the Abel bound for positive antitone weights from
uniform bounds on the unweighted prefix sums. -/
theorem norm_sum_range_weighted_le_of_prefix
    (a : ℕ → ℂ) (w : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hprefix : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, a i‖ ≤ B)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hwAnti : AntitoneOn w (Set.Iio n)) :
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ ≤ 2 * B * w 0 := by
  have hRePrefix : ∀ k ≤ n,
      |∑ i ∈ Finset.range k, (a i).re| ≤ B := by
    intro k hk
    have hsum : ∑ i ∈ Finset.range k, (a i).re =
        (∑ i ∈ Finset.range k, a i).re := by
      simp only [Complex.re_sum]
    rw [hsum]
    exact (Complex.abs_re_le_norm _).trans (hprefix k hk)
  have hImPrefix : ∀ k ≤ n,
      |∑ i ∈ Finset.range k, (a i).im| ≤ B := by
    intro k hk
    have hsum : ∑ i ∈ Finset.range k, (a i).im =
        (∑ i ∈ Finset.range k, a i).im := by
      simp only [Complex.im_sum]
    rw [hsum]
    exact (Complex.abs_im_le_norm _).trans (hprefix k hk)
  have hReAbel := Finset.abs_sum_mul_le_mul_of_abs_sum_range_le
    (f := fun i => (a i).re) (g := w) (n := n) hRePrefix hwNonneg hwAnti
  have hImAbel := Finset.abs_sum_mul_le_mul_of_abs_sum_range_le
    (f := fun i => (a i).im) (g := w) (n := n) hImPrefix hwNonneg hwAnti
  have hReEq : (∑ i ∈ Finset.range n, (w i : ℂ) * a i).re =
      ∑ i ∈ Finset.range n, (a i).re * w i := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Complex.mul_re]
    ring
  have hImEq : (∑ i ∈ Finset.range n, (w i : ℂ) * a i).im =
      ∑ i ∈ Finset.range n, (a i).im * w i := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Complex.mul_im]
    ring
  have hRe : |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).re| ≤ B * w 0 := by
    rw [hReEq]
    exact hReAbel
  have hIm : |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).im| ≤ B * w 0 := by
    rw [hImEq]
    exact hImAbel
  calc
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * a i‖ ≤
        |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).re| +
          |(∑ i ∈ Finset.range n, (w i : ℂ) * a i).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ B * w 0 + B * w 0 := add_le_add hRe hIm
    _ = 2 * B * w 0 := by ring

/-- One residue-class phase sum with the reciprocal logarithm attached. -/
noncomputable def reciprocalLogResiduePhaseSum
    (d q : ℕ) (a : ZMod q) (u l r : ℝ) : ℂ :=
  ∑ h ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (h : ℕ) =>
      l ≤ (h : ℝ) ∧ (h : ℝ) ≤ r ∧ (h : ZMod q) = a),
    Complex.exp (Complex.I * u * Real.log (h : ℝ)) /
      Real.log ((d * h : ℕ) : ℝ)

/-- Moderate-phase residue sums after Abel weighting by `1/log(d*h)`. -/
theorem moderate_reciprocal_log_residue_bound
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.exp (L / Real.log L ^ 2)
        ∀ N M : ℝ, Real.rpow x δ ≤ N → 1 < M →
          1 ≤ Real.log M → ∀ d : ℕ, 0 < d →
            M ≤ (d : ℝ) * N →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ a : ZMod q, ∀ u : ℝ, 1 ≤ |u| → |u| ≤ T →
                ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                  ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                    4 * C₀ * (N / (q : ℝ)) / Real.log M *
                      (|u|⁻¹ + Real.rpow x (-cδ)) := by
  sorry

/-- High-phase residue sums after Abel weighting by `1/log(d*h)`. -/
theorem high_reciprocal_log_residue_bound :
    ∃ C₃p : ℝ, 0 < C₃p ∧
      ∀ C : ℝ, 0 < C →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            let L := Real.log x
            let T := Real.log L
            ∀ N M : ℝ, Real.exp (L / T ^ 2) ≤ N →
              N ≤ 2 * Real.rpow x 5 → 1 < M →
              1 ≤ Real.log M → ∀ d : ℕ, 0 < d →
                M ≤ (d : ℝ) * N →
                ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                  ∀ a : ZMod q, ∀ u : ℝ,
                    Real.exp (L / (2 * T ^ 2)) ≤ |u| →
                    |u| ≤ 4 * Real.rpow x 3 →
                      ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                        ‖reciprocalLogResiduePhaseSum d q a u l r‖ ≤
                          4 * C₀ * (N / (q : ℝ)) / Real.log M *
                            Real.exp (-L / Real.rpow T C₃p) := by
  obtain ⟨C₃p, hC₃p, hForC⟩ := ArtinPrimitiveRoots.TypeII.PP.log_phase
  refine ⟨C₃p, hC₃p, ?_⟩
  intro C hC
  obtain ⟨C₀, x₀, hC₀, hx₀, hMain⟩ := hForC C hC
  refine ⟨C₀, x₀, hC₀, hx₀, ?_⟩
  intro x hx
  dsimp
  intro N M hN hNupper hM hlogM d hd hMN q hq hqBound a u huLower huUpper l r hl hlr hr
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < N := by nlinarith [hMN, hM]
  have hlpos : 0 < l := lt_of_lt_of_le hNpos hl
  have hrNonneg : 0 ≤ r := by linarith
  have hPP := hMain x hx N hN hNupper q hq hqBound a u huLower huUpper
  let nLo : ℕ := ⌈l⌉₊
  let nHi : ℕ := ⌊r⌋₊
  have hloCast : l ≤ (nLo : ℝ) := by
    dsimp [nLo]
    exact Nat.le_ceil l
  have hhiCast : (nHi : ℝ) ≤ r := by
    dsimp [nHi]
    exact Nat.floor_le hrNonneg
  have hNlo : N ≤ (nLo : ℝ) := le_trans hl hloCast
  have hloPos : 0 < nLo := by
    by_contra hnot
    have hzero : nLo = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hloCast
    have hloCast' : l ≤ 0 := by simpa using hloCast
    exact (not_le_of_gt hlpos) hloCast'
  have hhiUpper : (nHi : ℝ) ≤ 2 * N := le_trans hhiCast hr
  have hcastMul (j : ℕ) : ((d * j : ℕ) : ℝ) =
      (d : ℝ) * (j : ℝ) := by norm_cast
  have hprodLo : M ≤ ((d * nLo : ℕ) : ℝ) := by
    calc
      M ≤ (d : ℝ) * N := hMN
      _ ≤ (d : ℝ) * (nLo : ℝ) :=
        mul_le_mul_of_nonneg_left hNlo hdR.le
      _ = ((d * nLo : ℕ) : ℝ) := (hcastMul nLo).symm
  have hlogProdLo : 0 < Real.log ((d * nLo : ℕ) : ℝ) :=
    Real.log_pos (lt_of_lt_of_le hM hprodLo)
  have hprodPosLo : 0 < ((d * nLo : ℕ) : ℝ) := by
    exact lt_of_lt_of_le (lt_trans (by norm_num) hM) hprodLo
  have hprodLe (j : ℕ) (hj : nLo ≤ j) :
      ((d * nLo : ℕ) : ℝ) ≤ ((d * j : ℕ) : ℝ) := by
    rw [hcastMul, hcastMul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hdR.le
  have hlogPosAt (j : ℕ) (hj : nLo ≤ j) :
      0 < Real.log ((d * j : ℕ) : ℝ) :=
    Real.log_pos (lt_of_lt_of_le hM (le_trans hprodLo (hprodLe j hj)))
  by_cases hNonempty : nLo ≤ nHi
  · let w : ℕ → ℝ := fun j =>
      if nLo ≤ j then 1 / Real.log ((d * j : ℕ) : ℝ)
      else 1 / Real.log ((d * nLo : ℕ) : ℝ)
    let phase : ℕ → ℂ := fun j =>
      if nLo ≤ j ∧ j ≤ nHi ∧ (j : ZMod q) = a then
        Complex.exp (Complex.I * u * Real.log (j : ℝ)) else 0
    let B : ℝ := C₀ * (N / (q : ℝ)) *
      Real.exp (-Real.log x / Real.rpow (Real.log (Real.log x)) C₃p)
    have hwNonneg : ∀ j, 0 ≤ w j := by
      intro j
      by_cases hj : nLo ≤ j
      · simp [w, hj]
        simpa only [hcastMul] using (hlogPosAt j hj).le
      · simp [w, hj]
        simpa only [hcastMul] using hlogProdLo.le
    have hwAnti : AntitoneOn w (Set.Iio (nHi + 1)) := by
      intro i hi j hj hij
      by_cases hil : nLo ≤ i
      · have hjl : nLo ≤ j := le_trans hil hij
        simp [w, hil, hjl]
        have hprodIJ : ((d * i : ℕ) : ℝ) ≤ ((d * j : ℕ) : ℝ) := by
          rw [hcastMul, hcastMul]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hdR.le
        have hprodPosI := lt_of_lt_of_le hprodPosLo (hprodLe i hil)
        have hlogIJ := Real.log_le_log hprodPosI hprodIJ
        calc
          (Real.log ((d : ℝ) * (j : ℝ)))⁻¹ =
              1 / Real.log ((d * j : ℕ) : ℝ) := by
            rw [← hcastMul]
            exact (one_div _).symm
          _ ≤ 1 / Real.log ((d * i : ℕ) : ℝ) :=
            one_div_le_one_div_of_le (hlogPosAt i hil) hlogIJ
          _ = (Real.log ((d : ℝ) * (i : ℝ)))⁻¹ := by
            rw [← hcastMul]
            exact one_div _
      · by_cases hjl : nLo ≤ j
        · simp [w, hil, hjl]
          have hlogLe := Real.log_le_log hprodPosLo (hprodLe j hjl)
          calc
            (Real.log ((d : ℝ) * (j : ℝ)))⁻¹ =
                1 / Real.log ((d * j : ℕ) : ℝ) := by
              rw [← hcastMul]
              exact (one_div _).symm
            _ ≤ 1 / Real.log ((d * nLo : ℕ) : ℝ) :=
              one_div_le_one_div_of_le hlogProdLo hlogLe
            _ = (Real.log ((d : ℝ) * (nLo : ℝ)))⁻¹ := by
              rw [← hcastMul]
              exact one_div _
        · simp [w, hil, hjl]
    have hPrefix : ∀ k ≤ nHi + 1,
        ‖∑ i ∈ Finset.range k, phase i‖ ≤ B := by
      intro k hk
      by_cases hkLo : k ≤ nLo
      · have hzero : ∀ i ∈ Finset.range k, phase i = 0 := by
          intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          have hnot : ¬ nLo ≤ i := by omega
          simp [phase, hnot]
        rw [Finset.sum_eq_zero hzero]
        simp [B]
        positivity
      · have hkLo' : nLo < k := Nat.lt_of_not_ge hkLo
        let j : ℕ := k - 1
        have hjLo : nLo ≤ j := by dsimp [j]; omega
        have hjHi : j ≤ nHi := by dsimp [j]; omega
        let I : Set ℕ := {n | (nLo : ℝ) ≤ (n : ℝ) ∧
          (n : ℝ) ≤ (j : ℝ)}
        let Ssrc : Finset ℕ := (Finset.range k).filter
          (fun n => nLo ≤ n ∧ n ≤ nHi ∧ (n : ZMod q) = a)
        let Spp : Finset ℕ :=
          (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun n =>
            N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N ∧ n ∈ I ∧
              (n : ZMod q) = a)
        have hTwoNNonneg : 0 ≤ 2 * N := by positivity
        have hSset : Ssrc = Spp := by
          ext i
          simp only [Ssrc, Spp, I, Finset.mem_filter, Finset.mem_range,
            Nat.lt_succ_iff, Set.mem_setOf_eq]
          constructor
          · rintro ⟨hik, hlo, hhi, hmod⟩
            have hij : i ≤ j := by dsimp [j]; omega
            have hupper : (i : ℝ) ≤ 2 * N := by
              calc
                (i : ℝ) ≤ (nHi : ℝ) := by exact_mod_cast hhi
                _ ≤ 2 * N := hhiUpper
            have hfloor : i ≤ ⌊2 * N⌋₊ :=
              (Nat.le_floor_iff hTwoNNonneg).2 hupper
            exact ⟨hfloor,
              le_trans hNlo (by exact_mod_cast hlo), hupper,
              ⟨by exact_mod_cast hlo, by exact_mod_cast hij⟩, hmod⟩
          · rintro ⟨_, _, _, hinterval, hmod⟩
            have hlo : nLo ≤ i := by exact_mod_cast hinterval.1
            have hij : i ≤ j := by exact_mod_cast hinterval.2
            have hik : i < k := by dsimp [j] at hij ⊢; omega
            have hhi : i ≤ nHi := le_trans hij hjHi
            exact ⟨hik, hlo, hhi, hmod⟩
        have hSumSource :
            (∑ i ∈ Finset.range k, phase i) =
              ∑ i ∈ Ssrc, Complex.exp (Complex.I * u * Real.log (i : ℝ)) := by
          dsimp [phase, Ssrc]
          rw [← Finset.sum_filter]
        have hSumPP :
            ArtinPrimitiveRoots.TypeII.PP.residuePhaseSum N q a u I =
              ∑ i ∈ Spp, Complex.exp (Complex.I * u * Real.log (i : ℝ)) := by
          simp [Spp, I, ArtinPrimitiveRoots.TypeII.PP.residuePhaseSum]
        have hSumEq :
            (∑ i ∈ Finset.range k, phase i) =
              ArtinPrimitiveRoots.TypeII.PP.residuePhaseSum N q a u I := by
          calc
            _ = ∑ i ∈ Ssrc, Complex.exp (Complex.I * u * Real.log (i : ℝ)) :=
              hSumSource
            _ = ∑ i ∈ Spp, Complex.exp (Complex.I * u * Real.log (i : ℝ)) := by
              rw [hSset]
            _ = _ := hSumPP.symm
        have hupper : (j : ℝ) ≤ 2 * N := by
          calc
            (j : ℝ) ≤ (nHi : ℝ) := by exact_mod_cast hjHi
            _ ≤ 2 * N := hhiUpper
        have hprefix := hPP (nLo : ℝ) (j : ℝ) hNlo hupper
        have hPrefixBound : ‖∑ i ∈ Finset.range k, phase i‖ ≤ B := by
          rw [hSumEq]
          simpa [B, I] using hprefix
        exact hPrefixBound
    let Slocal : Finset ℕ :=
      (Finset.range (⌊r⌋₊ + 1)).filter (fun h =>
        l ≤ (h : ℝ) ∧ (h : ℝ) ≤ r ∧ (h : ZMod q) = a)
    let Ssupport : Finset ℕ :=
      (Finset.range (nHi + 1)).filter (fun h =>
        nLo ≤ h ∧ h ≤ nHi ∧ (h : ZMod q) = a)
    have hInterval (h : ℕ) :
        (l ≤ (h : ℝ) ∧ (h : ℝ) ≤ r) ↔ nLo ≤ h ∧ h ≤ nHi := by
      have hcast := Nat.cast_mem_Icc_iff (n := h) (a := l) (b := r) hrNonneg
      simpa [Set.mem_Icc, Finset.mem_Icc, nLo, nHi] using hcast
    have hLocalSet : Slocal = Ssupport := by
      ext h
      simp only [Slocal, Ssupport, Finset.mem_filter, Finset.mem_range,
        Nat.lt_succ_iff]
      constructor
      · rintro ⟨_, hloReal, hhiReal, hmod⟩
        have hnat := (hInterval h).mp ⟨hloReal, hhiReal⟩
        exact ⟨hnat.2, hnat.1, hnat.2, hmod⟩
      · rintro ⟨hrange, hloNat, hhiNat, hmod⟩
        have hreal := (hInterval h).mpr ⟨hloNat, hhiNat⟩
        exact ⟨hrange, hreal.1, hreal.2, hmod⟩
    have hWeightEq :
        (∑ i ∈ Finset.range (nHi + 1), (w i : ℂ) * phase i) =
          ∑ i ∈ Ssupport,
            Complex.exp (Complex.I * u * Real.log (i : ℝ)) /
              Real.log ((d * i : ℕ) : ℝ) := by
      calc
        _ = ∑ i ∈ Finset.range (nHi + 1),
              if nLo ≤ i ∧ i ≤ nHi ∧ (i : ZMod q) = a then
                Complex.exp (Complex.I * u * Real.log (i : ℝ)) /
                  Real.log ((d * i : ℕ) : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hs : nLo ≤ i ∧ i ≤ nHi ∧ (i : ZMod q) = a
          · simp [phase, w, hs]
            ring
          · simp [phase, hs]
        _ = _ := by
          rw [← Finset.sum_filter]
    have hLocalEq :
        ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.reciprocalLogResiduePhaseSum
            d q a u l r =
          ∑ i ∈ Finset.range (nHi + 1), (w i : ℂ) * phase i := by
      unfold reciprocalLogResiduePhaseSum
      change (∑ i ∈ Slocal,
        Complex.exp (Complex.I * u * Real.log (i : ℝ)) /
          Real.log ((d * i : ℕ) : ℝ)) = _
      rw [hLocalSet]
      exact hWeightEq.symm
    have hAbel := norm_sum_range_weighted_le_of_prefix
      phase w (nHi + 1) B hPrefix (fun _ => hwNonneg _) hwAnti
    rw [hLocalEq]
    let E : ℝ := Real.exp (-Real.log x /
      Real.rpow (Real.log (Real.log x)) C₃p)
    have hBnonneg : 0 ≤ C₀ * (N / (q : ℝ)) * E := by positivity
    have hw0 : w 0 ≤ 1 / Real.log M := by
      have hzero : w 0 = 1 / Real.log ((d * nLo : ℕ) : ℝ) := by
        simp [w, Nat.not_le_of_gt hloPos]
      rw [hzero]
      apply one_div_le_one_div_of_le (by linarith : 0 < Real.log M)
      exact Real.log_le_log (by linarith : 0 < M) hprodLo
    calc
      ‖∑ i ∈ Finset.range (nHi + 1), (w i : ℂ) * phase i‖ ≤
          2 * B * w 0 := hAbel
      _ ≤ 2 * B * (1 / Real.log M) :=
        mul_le_mul_of_nonneg_left hw0 (by positivity)
      _ = 2 * (C₀ * (N / (q : ℝ)) * E) / Real.log M := by
        dsimp [B, E]
        ring
      _ ≤ 4 * (C₀ * (N / (q : ℝ)) * E) / Real.log M := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have hcoeff : 2 * (C₀ * (N / (q : ℝ)) * E) ≤
            4 * (C₀ * (N / (q : ℝ)) * E) := by
          nlinarith [hBnonneg]
        exact mul_le_mul_of_nonneg_right hcoeff
          (inv_nonneg.mpr (le_of_lt (by linarith)))
      _ = 4 * C₀ * (N / (q : ℝ)) / Real.log M * E := by ring
  · have hempty : nHi < nLo := by omega
    have hLocalEmpty :
        (Finset.range (⌊r⌋₊ + 1)).filter (fun (h : ℕ) =>
          l ≤ (h : ℝ) ∧ (h : ℝ) ≤ r ∧ (h : ZMod q) = a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      rcases Finset.mem_filter.mp hh with ⟨_, ⟨hlo, hhi, _⟩⟩
      have hceil : nLo ≤ h := by
        dsimp [nLo]
        exact Nat.ceil_le.mpr hlo
      have hfloor : h ≤ nHi := (Nat.le_floor_iff hrNonneg).2 hhi
      omega
    unfold reciprocalLogResiduePhaseSum
    rw [hLocalEmpty]
    simp
    positivity

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
