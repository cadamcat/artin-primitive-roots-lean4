import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pp2.Analytic
import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.Proofs.pp1.HalaszMeanValue
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.LogPhaseLow

/-! Statements in the Prime Predecessors long-prime chain, PP
`02-long-prime.tex:8-579`. -/

namespace ArtinPrimitiveRoots.TypeII.PP

open Classical
open Complex Filter
open Metric
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP.Proofs
open scoped Topology

/-- `t2:pp.mean-value` — PP `02-long-prime.tex:48-183`, Lemma 3.2. -/
theorem mean_value :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ k : ℕ, 2 ≤ k →
        ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧
          ∀ M : ℕ, 1 ≤ M →
            (vinogradovCount s k M : ℝ) ≤
              Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
                Real.rpow (M : ℝ)
                  (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 : ℝ) := by
  exact mean_value_from_halasz

/-- `t2:pp.log-phase` — PP `02-long-prime.tex:185-310`, Lemma 3.3; also PD Lemma 2.4. `I` is an interval in
`[N', 2N']`, as in the paper (an arbitrary subset makes it false; lane `pp1`, 2026-10-07). -/
theorem log_phase :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ C : ℝ, 0 < C →
        ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            let L := Real.log x
            let T := Real.log L
            ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' → N' ≤ 2 * Real.rpow x 5 →
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                ∀ a : ZMod q, ∀ v : ℝ,
                  Real.exp (L / (2 * T ^ 2)) ≤ |v| → |v| ≤ 4 * Real.rpow x 3 →
                    ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
                      ‖residuePhaseSum N' q a v {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                        C₀ * (N' / q) * Real.exp (-L / Real.rpow T C₃) := by
  sorry

/-- `t2:pp.L-upper` — PP `02-long-prime.tex:312-368`, including the finite Dirichlet-series
approximation and the logarithmic growth bound in the window around `Re(s)=1`. -/
theorem L_upper :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              (∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re →
                  s.re ≤ 2 → 1 / 2 ≤ |s.im| →
                    ∀ Y : ℝ, 1 ≤ Y →
                      ‖dirichletLValue q hq χ s - dirichletPartialSum q χ Y s -
                        characterMean q χ *
                          Complex.exp ((1 - s) * Real.log Y) / (s - 1)‖ ≤
                        C₀ * q * (1 + ‖s‖) * Real.rpow Y (-s.re)) ∧
              (∀ σ v : ℝ, |σ - 1| ≤ 10 * rstar →
                (1 / 2 : ℝ) ≤ |v| → |v| ≤ 3 * Real.rpow x 3 →
                      ‖dirichletLValue q hq χ (⟨σ, v⟩ : ℂ)‖ ≤
                    Real.exp (C₀ * T ^ 2)) := by
  sorry

private theorem norm_LFunctionTrivChar_le_of_zeta₀_bound (q : ℕ) [NeZero q] (hq : 0 < q)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hζ₀ : ‖riemannZeta₀ (1 + (r : ℂ))‖ ≤ K) :
    ‖DirichletCharacter.LFunctionTrivChar q (1 + (r : ℂ))‖ ≤
      (q : ℝ) * (1 / r + K) := by
  have hsne : (1 + (r : ℂ)) ≠ 1 := by
    intro hs
    have := congrArg Complex.re hs
    simp at this
    linarith
  have hζeq := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (N := q) (s := 1 + (r : ℂ)) hsne
  have hζnorm : ‖riemannZeta (1 + (r : ℂ))‖ ≤ 1 / r + K := by
    rw [riemannZeta_eq_inv_sub_add hsne,
      show 1 + (r : ℂ) - 1 = (r : ℂ) by ring]
    have hinv : ‖((r : ℂ)⁻¹)‖ = 1 / r := by
      rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simp [one_div]
    calc
      ‖(r : ℂ)⁻¹ + riemannZeta₀ (1 + (r : ℂ))‖ ≤
          ‖(r : ℂ)⁻¹‖ + ‖riemannZeta₀ (1 + (r : ℂ))‖ := norm_add_le _ _
      _ ≤ 1 / r + K := add_le_add (le_of_eq hinv) hζ₀
  have hfac (p : ℕ) (hp : p ∈ q.primeFactors) :
      ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤ (p : ℝ) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hnorm : ‖(p : ℂ) ^ (-(1 + (r : ℂ)))‖ =
        (p : ℝ) ^ (-(1 + r)) := by
      have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := by norm_cast
      rw [hcast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hprime.pos)]
      simp
    have hpReal : (1 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hprime.two_le)
    have hpow : (p : ℝ) ^ (-(1 + r)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hpReal (by linarith)
    calc
      ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤
          ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-(1 + (r : ℂ)) )‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one, hnorm]; linarith
      _ ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hfacProd :
      ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 + (r : ℂ))))‖ ≤ (q : ℝ) := by
    rw [norm_prod]
    have hproduct :
        ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤
          ∏ p ∈ q.primeFactors, (p : ℝ) := by
      have hprodLe (s : Finset ℕ)
          (hs : ∀ p ∈ s, ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤ (p : ℝ)) :
          ∏ p ∈ s, ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤ ∏ p ∈ s, (p : ℝ) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          have htail : ∀ p ∈ s, ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤ (p : ℝ) := by
            intro p hp
            exact hs p (by simp [hp])
          exact mul_le_mul (hs a (by simp)) (ih htail)
            (Finset.prod_nonneg fun p hp ↦ norm_nonneg _) (by positivity)
      exact hprodLe q.primeFactors (fun p hp ↦ hfac p hp)
    calc
      ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-(1 + (r : ℂ)))‖ ≤
          ∏ p ∈ q.primeFactors, (p : ℝ) := hproduct
      _ ≤ (q : ℝ) := by
        have hnat : (∏ p ∈ q.primeFactors, p) ≤ q :=
          Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
        calc
          ∏ p ∈ q.primeFactors, (p : ℝ) = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by simp
          _ ≤ (q : ℝ) := by exact_mod_cast hnat
  calc
    ‖DirichletCharacter.LFunctionTrivChar q (1 + (r : ℂ))‖ =
        ‖(∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 + (r : ℂ)))) ) *
          riemannZeta (1 + (r : ℂ))‖ := by rw [hζeq]
    _ = ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-(1 + (r : ℂ))))‖ *
          ‖riemannZeta (1 + (r : ℂ))‖ := norm_mul _ _
    _ ≤ (q : ℝ) * (1 / r + K) :=
      mul_le_mul hfacProd hζnorm (norm_nonneg _) (by positivity)

set_option maxHeartbeats 1000000
/-- `t2:pp.local-logderiv` — PP `02-long-prime.tex:370-424`, Lemma 3.5. The finite zero list
records multiplicity by repetition, which is the convention in the logarithmic-derivative sum. -/
theorem local_logderiv :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let rstar := T ^ 4 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q, ∀ v : ℝ,
              1 ≤ |v| → |v| ≤ (5 / 2 : ℝ) * Real.rpow x 3 →
                let s₀ : ℂ := ⟨1 + rstar, v⟩
                ∃ R : ℝ, 4 * rstar ≤ R ∧ R ≤ 5 * rstar ∧
                  ∃ Z : List ℂ, (Z.length : ℝ) ≤ C₀ * T ^ 2 ∧
                    (∀ ρ ∈ Z, dirichletLValue q hq χ ρ = 0 ∧
                      ‖ρ - s₀‖ < R) ∧
                    (∀ ρ : ℂ, dirichletLValue q hq χ ρ = 0 →
                      ‖ρ - s₀‖ < R → ρ ∈ Z) ∧
                    (∀ z : ℂ, ‖z - s₀‖ = R →
                      dirichletLValue q hq χ z ≠ 0) ∧
                    (∀ z : ℂ, ‖z - s₀‖ ≤ 2 * rstar →
                      dirichletLValue q hq χ z ≠ 0 →
                        ‖deriv (dirichletLValue q hq χ) z /
                            dirichletLValue q hq χ z -
                          (Z.map fun ρ => (1 : ℂ) / (z - ρ)).sum‖ ≤
                          C₀ * T ^ 2 / rstar) := by
  classical
  intro C hC
  obtain ⟨CUpper, xUpper, hCUpper, hxUpper, hUpper⟩ := L_upper C hC
  let K : ℝ := CUpper + 3 * C + 30
  let COut : ℝ := 25 * (K + 1) + 2 * K / Real.log (8 / 5) + 1
  have hCOut : 0 < COut := by positivity
  let KZeta : ℝ := ‖riemannZeta₀ 1‖ + 1
  let Tfun : ℝ → ℝ := fun x ↦ Real.log (Real.log x)
  let rfun : ℝ → ℝ := fun x ↦ (Tfun x) ^ 4 / Real.log x
  have hTtend : Tendsto Tfun atTop atTop := by
    simpa [Tfun, Function.comp_def] using
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hrTend : Tendsto rfun atTop (𝓝 0) := by
    simpa [rfun, Tfun, Function.comp_def] using
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
        Real.tendsto_log_atTop)
  have hExpT : Tendsto (fun x ↦ Real.exp (Tfun x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hTtend
  have hζ₀event : ∀ᶠ x : ℝ in atTop,
      ‖riemannZeta₀ (1 + (rfun x : ℂ))‖ ≤ KZeta := by
    filter_upwards [hrTend.eventually riemannZeta₀_norm_bound_near_one] with x hx
    simpa [KZeta] using hx
  have hKZetaevent : ∀ᶠ x : ℝ in atTop, KZeta ≤ Real.exp (Tfun x) :=
    hExpT.eventually (eventually_ge_atTop KZeta)
  have hTevent : ∀ᶠ x : ℝ in atTop, 1 ≤ Tfun x :=
    hTtend.eventually (eventually_ge_atTop (1 : ℝ))
  have hrSmallEvent : ∀ᶠ x : ℝ in atTop, rfun x < 1 / 16 :=
    hrTend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hLarge : ∀ᶠ x : ℝ in atTop,
      xUpper ≤ x ∧ 2 < x ∧ 1 ≤ Tfun x ∧ rfun x < 1 / 16 ∧
        ‖riemannZeta₀ (1 + (rfun x : ℂ))‖ ≤ KZeta ∧
        KZeta ≤ Real.exp (Tfun x) := by
    filter_upwards [eventually_ge_atTop xUpper, eventually_gt_atTop (2 : ℝ),
      hTevent, hrSmallEvent, hζ₀event, hKZetaevent]
      with x hxU hx2 hxT hxr hζ hKZ
    exact ⟨hxU, hx2, hxT, hxr, hζ, hKZ⟩
  obtain ⟨x₀, hx₀large⟩ := Filter.eventually_atTop.1 hLarge
  have hx₀ : 2 < x₀ := (hx₀large x₀ le_rfl).2.1
  refine ⟨COut, x₀, hCOut, hx₀, ?_⟩
  intro x hx
  dsimp only
  intro q hq1 hqBound hq χ v hv hvmax
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let L : ℝ := Real.log x
  let T : ℝ := Real.log L
  let rstar : ℝ := T ^ 4 / L
  let s₀ : ℂ := ⟨1 + rstar, v⟩
  have hgood := hx₀large x hx
  rcases hgood with ⟨hxUpper, hx2, hTge, hrSmall, hζ₀, hKZeta⟩
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hTpos : 0 < T := by linarith
  have hTge' : 1 ≤ T := by simpa [T, L, Tfun] using hTge
  have hrpos : 0 < rstar := by dsimp [rstar]; positivity
  have hrSmall' : rstar < 1 / 16 := by simpa [rstar, T, L, Tfun, rfun] using hrSmall
  have hLexp : Real.exp T = L := Real.exp_log hLpos
  have hLgeOne : 1 ≤ L := by
    rw [← hLexp]
    have h2exp : 2 ≤ Real.exp T :=
      le_trans (le_of_lt Real.exp_one_gt_two) (Real.exp_le_exp.mpr hTge')
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) h2exp
  let xDouble : ℝ := 2 * x
  let LDouble : ℝ := Real.log xDouble
  let TDouble : ℝ := Real.log LDouble
  let rDouble : ℝ := TDouble ^ 4 / LDouble
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num)).2 (le_of_lt Real.exp_one_gt_two)
  have hLDoubleEq : LDouble = Real.log 2 + L := by
    dsimp [LDouble, xDouble, L]
    rw [Real.log_mul (by norm_num) hxpos.ne']
  have hLDoubleLower : L ≤ LDouble := by rw [hLDoubleEq]; linarith
  have hLDoubleUpper : LDouble ≤ 2 * L := by
    rw [hLDoubleEq]
    nlinarith [hlog2le, hLgeOne]
  have hLDoublePos : 0 < LDouble := lt_of_lt_of_le hLpos hLDoubleLower
  have hTDoubleLower : T ≤ TDouble :=
    Real.log_le_log hLpos hLDoubleLower
  have hTDoubleUpper : TDouble ≤ 2 * T := by
    calc
      TDouble = Real.log LDouble := rfl
      _ ≤ Real.log (2 * L) := Real.log_le_log hLDoublePos hLDoubleUpper
      _ = Real.log 2 + T := by rw [Real.log_mul (by norm_num) hLpos.ne']
      _ ≤ 2 * T := by nlinarith [hlog2le, hTge]
  have hTDoublePos : 0 < TDouble := lt_of_lt_of_le hTpos hTDoubleLower
  have hTpowLe : T ^ 4 ≤ TDouble ^ 4 := by
    exact pow_le_pow_left₀ (le_of_lt hTpos) hTDoubleLower 4
  have hrDoubleCompare : rstar ≤ 2 * rDouble := by
    dsimp [rDouble, rstar]
    calc
      T ^ 4 / L ≤ 2 * T ^ 4 / LDouble := by
        apply (div_le_div_iff₀ hLpos hLDoublePos).2
        nlinarith [mul_le_mul_of_nonneg_left hLDoubleUpper (pow_nonneg (le_of_lt hTpos) 4)]
      _ ≤ 2 * TDouble ^ 4 / LDouble := by
        apply (div_le_div_iff₀ hLDoublePos hLDoublePos).2
        have hscaled : 2 * T ^ 4 ≤ 2 * TDouble ^ 4 :=
          mul_le_mul_of_nonneg_left hTpowLe (by norm_num)
        exact mul_le_mul_of_nonneg_right hscaled hLDoublePos.le
      _ = 2 * (TDouble ^ 4 / LDouble) := by ring
  have hqBoundDouble : (q : ℝ) ≤ Real.rpow LDouble C := by
    exact hqBound.trans (Real.rpow_le_rpow (le_of_lt hLpos) hLDoubleLower (le_of_lt hC))
  have hUpperX := hUpper x hxUpper q hq1 hqBound hq χ
  have hUpperDouble := hUpper xDouble (by dsimp [xDouble]; linarith [hxUpper, hxpos])
    q hq1 hqBoundDouble hq (χ ^ 2)
  have hUpperBoundX := hUpperX.2
  have hUpperBoundDouble := hUpperDouble.2
  have hqExp : (q : ℝ) ≤ Real.exp (C * T) := by
    calc
      (q : ℝ) ≤ Real.rpow L C := hqBound
      _ = Real.exp (C * T) := by
        dsimp [T]
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        ring
  have hrInv : 1 / rstar ≤ Real.exp T := by
    have hTpow : 1 ≤ T ^ 4 := by
      calc
        1 = (1 : ℝ) ^ 4 := by norm_num
        _ ≤ T ^ 4 := pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hTge' 4
    have hInvEq : 1 / rstar = L / T ^ 4 := by
      dsimp [rstar]
      field_simp [hLpos.ne', hTpos.ne']
    rw [hInvEq]
    calc
      L / T ^ 4 ≤ L := div_le_self hLpos.le hTpow
      _ = Real.exp T := hLexp.symm
  have htwoExp : 2 * Real.exp T ≤ Real.exp (2 * T) := by
    have htwo : 2 ≤ Real.exp T := by
      exact le_trans (le_of_lt Real.exp_one_gt_two) (Real.exp_le_exp.mpr hTge')
    calc
      2 * Real.exp T ≤ Real.exp T * Real.exp T :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg T)
      _ = Real.exp (2 * T) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hζnormExp : 1 / rstar + KZeta ≤ Real.exp (2 * T) := by
    calc
      1 / rstar + KZeta ≤ Real.exp T + Real.exp T := add_le_add hrInv hKZeta
      _ = 2 * Real.exp T := by ring
      _ ≤ Real.exp (2 * T) := htwoExp
  have htrivBound :
      ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ≤
        Real.exp ((3 * C + 10) * T ^ 2) := by
    have hraw := norm_LFunctionTrivChar_le_of_zeta₀_bound q hq hrpos
      (by positivity : 0 ≤ KZeta) hζ₀
    calc
      ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ≤
          (q : ℝ) * (1 / rstar + KZeta) := hraw
      _ ≤ Real.exp (C * T) * Real.exp (2 * T) :=
        mul_le_mul hqExp hζnormExp (by positivity) (by positivity)
      _ = Real.exp ((C + 2) * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((3 * C + 10) * T ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hTle : T ≤ T ^ 2 := by nlinarith [hTge']
        have hCle : C + 2 ≤ 3 * C + 10 := by linarith [hC]
        calc
          (C + 2) * T ≤ (C + 2) * T ^ 2 :=
            mul_le_mul_of_nonneg_left hTle (by positivity)
          _ ≤ (3 * C + 10) * T ^ 2 :=
            mul_le_mul_of_nonneg_right hCle (sq_nonneg T)
  have hSigmaBound :
      |(1 + rstar) - 1| ≤ 10 * rDouble := by
    have hrCompare : rstar ≤ 10 * rDouble := by nlinarith [hrDoubleCompare]
    have hsub : (1 + rstar) - 1 = rstar := by ring
    rw [hsub, abs_of_pos hrpos]
    exact hrCompare
  have hrpow3 (a : ℝ) : Real.rpow a 3 = a ^ 3 := by
    convert Real.rpow_natCast a (3 : ℕ) using 1 <;> norm_num
  have hvDoubleLower : (1 / 2 : ℝ) ≤ |2 * v| := by
    calc
      (1 / 2 : ℝ) ≤ 2 := by norm_num
      _ ≤ 2 * |v| := by nlinarith [hv]
      _ = |2 * v| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hvDoubleUpper : |2 * v| ≤ 3 * Real.rpow xDouble 3 := by
    have hbase : |2 * v| ≤ 5 * Real.rpow x 3 := by
      calc
        |2 * v| = 2 * |v| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * ((5 / 2 : ℝ) * Real.rpow x 3) :=
          mul_le_mul_of_nonneg_left hvmax (by norm_num)
        _ = 5 * Real.rpow x 3 := by ring
    have hpow : Real.rpow xDouble 3 = 8 * Real.rpow x 3 := by
      calc
        Real.rpow xDouble 3 = xDouble ^ 3 := hrpow3 xDouble
        _ = (2 * x) ^ 3 := by dsimp [xDouble]
        _ = 8 * x ^ 3 := by ring
        _ = 8 * Real.rpow x 3 := by rw [hrpow3 x]
    rw [hpow]
    calc
      |2 * v| ≤ 5 * Real.rpow x 3 := hbase
      _ ≤ 24 * Real.rpow x 3 :=
        mul_le_mul_of_nonneg_right (by norm_num : (5 : ℝ) ≤ 24)
          (Real.rpow_nonneg (le_of_lt hxpos) 3)
      _ = 3 * (8 * Real.rpow x 3) := by ring
  have hUpperChi2 :
      ‖dirichletLValue q hq (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ ≤
        Real.exp (4 * CUpper * T ^ 2) := by
    have hbound := hUpperBoundDouble (1 + rstar) (2 * v)
      hSigmaBound hvDoubleLower hvDoubleUpper
    have hTpower : TDouble ^ 2 ≤ 4 * T ^ 2 := by
      calc
        TDouble ^ 2 ≤ (2 * T) ^ 2 :=
          (sq_le_sq₀ (le_of_lt hTDoublePos) (by positivity)).2 hTDoubleUpper
        _ = 4 * T ^ 2 := by ring
    have hbound' : ‖dirichletLValue q hq (χ ^ 2)
        (⟨1 + rstar, 2 * v⟩ : ℂ)‖ ≤ Real.exp (CUpper * TDouble ^ 2) := by
      simpa [dirichletLValue] using hbound
    have hexp : CUpper * TDouble ^ 2 ≤ 4 * CUpper * T ^ 2 := by
      calc
        CUpper * TDouble ^ 2 ≤ CUpper * (4 * T ^ 2) :=
          mul_le_mul_of_nonneg_left hTpower hCUpper.le
        _ = 4 * CUpper * T ^ 2 := by ring
    exact hbound'.trans (Real.exp_le_exp.mpr hexp)
  have hcenterEuler :
      ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ)) ^ 3 *
        DirichletCharacter.LFunction χ s₀ ^ 4 *
        DirichletCharacter.LFunction (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ ≥ 1 := by
    have hprod := χ.norm_LFunction_product_ge_one hrpos v
    have harg : (1 + (rstar : ℂ) + Complex.I * v) = s₀ := by
      rw [Complex.ext_iff]
      constructor <;> simp [s₀]
    have harg₂ : 1 + (rstar : ℂ) + 2 * Complex.I * v =
        (⟨1 + rstar, 2 * v⟩ : ℂ) := by
      rw [Complex.ext_iff]
      constructor <;> simp [mul_assoc]
    rw [harg] at hprod
    rw [harg₂] at hprod
    exact hprod
  have hcenterEulerNorm :
      1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ^ 3 *
        ‖dirichletLValue q hq χ s₀‖ ^ 4 *
        ‖dirichletLValue q hq (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ := by
    have hnorm : 1 ≤
        ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ^ 3 *
          ‖DirichletCharacter.LFunction χ s₀‖ ^ 4 *
          ‖DirichletCharacter.LFunction (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ := by
      simpa only [norm_mul, norm_pow] using hcenterEuler
    simpa [dirichletLValue] using hnorm
  have hprodUpper :
      ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ^ 3 *
        ‖dirichletLValue q hq (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ ≤
      Real.exp ((3 * (3 * C + 10) + 4 * CUpper) * T ^ 2) := by
    calc
      _ ≤ Real.exp (3 * ((3 * C + 10) * T ^ 2)) *
          Real.exp (4 * CUpper * T ^ 2) := by
        apply mul_le_mul
        · calc
            _ ≤ (Real.exp ((3 * C + 10) * T ^ 2)) ^ 3 := by gcongr
            _ = Real.exp (3 * ((3 * C + 10) * T ^ 2)) := by
              rw [← Real.exp_nat_mul]
              congr 1
        · exact hUpperChi2
        · positivity
        · positivity
      _ = Real.exp ((3 * (3 * C + 10) + 4 * CUpper) * T ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  let M : ℝ := K * T ^ 2
  have hM : 0 < M := by dsimp [M, K]; positivity
  have hBLe : (3 * (3 * C + 10) + 4 * CUpper) * T ^ 2 ≤ 4 * M := by
    have hCoeff : 3 * (3 * C + 10) + 4 * CUpper ≤ 4 * K := by
      dsimp [K]
      linarith [hC]
    dsimp [M]
    calc
      (3 * (3 * C + 10) + 4 * CUpper) * T ^ 2 ≤ 4 * K * T ^ 2 :=
        mul_le_mul_of_nonneg_right hCoeff (sq_nonneg T)
      _ = 4 * (K * T ^ 2) := by ring
  have hcenterPow : Real.exp (-4 * M) ≤ ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
    have hpre : 1 ≤ Real.exp ((3 * (3 * C + 10) + 4 * CUpper) * T ^ 2) *
        ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
      calc
        1 ≤ ‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ^ 3 *
            ‖dirichletLValue q hq χ s₀‖ ^ 4 *
            ‖dirichletLValue q hq (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖ := hcenterEulerNorm
        _ = (‖DirichletCharacter.LFunctionTrivChar q (1 + (rstar : ℂ))‖ ^ 3 *
            ‖dirichletLValue q hq (χ ^ 2) (⟨1 + rstar, 2 * v⟩ : ℂ)‖) *
            ‖dirichletLValue q hq χ s₀‖ ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hprodUpper (by positivity)
    have hneg : Real.exp (-(3 * (3 * C + 10) + 4 * CUpper) * T ^ 2) ≤
        ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
      let B : ℝ := (3 * (3 * C + 10) + 4 * CUpper) * T ^ 2
      have hdiv : 1 / Real.exp B ≤ ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
        apply (div_le_iff₀ (Real.exp_pos B)).2
        simpa [B, mul_comm] using hpre
      have hnegB : Real.exp (-B) ≤ ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
        rw [Real.exp_neg]
        simpa [one_div] using hdiv
      have hBexp : -(3 * (3 * C + 10) + 4 * CUpper) * T ^ 2 = -B := by
        dsimp [B]
        ring
      rw [hBexp]
      exact hnegB
    exact (Real.exp_le_exp.mpr (by linarith [hBLe])).trans hneg
  have hexp4 : (Real.exp (-M)) ^ 4 = Real.exp (-4 * M) := by
    calc
      (Real.exp (-M)) ^ 4 = Real.exp (4 * (-M)) := (Real.exp_nat_mul (-M) 4).symm
      _ = Real.exp (-4 * M) := by congr 1 <;> ring
  have hnorm4 : (Real.exp (-M)) ^ 4 ≤ ‖dirichletLValue q hq χ s₀‖ ^ 4 := by
    rw [hexp4]
    exact hcenterPow
  have hnorm4AsSq :
      ((Real.exp (-M)) ^ 2) ^ 2 ≤ (‖dirichletLValue q hq χ s₀‖ ^ 2) ^ 2 := by
    have ha : (Real.exp (-M)) ^ 4 = ((Real.exp (-M)) ^ 2) ^ 2 := by ring
    have hb : ‖dirichletLValue q hq χ s₀‖ ^ 4 =
        (‖dirichletLValue q hq χ s₀‖ ^ 2) ^ 2 := by ring
    rw [ha, hb] at hnorm4
    exact hnorm4
  have hnorm2 : (Real.exp (-M)) ^ 2 ≤ ‖dirichletLValue q hq χ s₀‖ ^ 2 :=
    (sq_le_sq₀ (sq_nonneg (Real.exp (-M))) (sq_nonneg _)).1 hnorm4AsSq
  have hnorm1 : Real.exp (-M) ≤ ‖dirichletLValue q hq χ s₀‖ :=
    (sq_le_sq₀ (Real.exp_nonneg _) (norm_nonneg _)).1 hnorm2
  have hcenter : Real.exp (-M) ≤ ‖dirichletLValue q hq χ s₀‖ := by
    exact hnorm1
  let F : ℂ → ℂ := fun w ↦ dirichletLValue q hq χ (s₀ + w)
  have hImag (w : ℂ) (hw : ‖w‖ ≤ 8 * rstar) :
      1 / 2 ≤ |v + w.im| ∧ |v + w.im| ≤ 3 * Real.rpow x 3 := by
    have hwIm : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hwImSmall : |w.im| ≤ 1 / 2 := by nlinarith [hwIm, hw, hrSmall']
    have htriangle : |v| ≤ |v + w.im| + |w.im| := by
      calc
        |v| = |(v + w.im) + (-w.im)| := by congr 1 <;> ring
        _ ≤ |v + w.im| + |-w.im| := abs_add_le _ _
        _ = |v + w.im| + |w.im| := by rw [abs_neg]
    have hpowx : 8 ≤ Real.rpow x 3 := by
      rw [hrpow3 x]
      have hpow : (2 : ℝ) ^ 3 ≤ x ^ 3 :=
        pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) (le_of_lt hx2) 3
      norm_num at hpow
      exact hpow
    refine ⟨?_, ?_⟩
    · linarith [hv, htriangle, hwImSmall]
    · have htriangle' : |v + w.im| ≤ |v| + |w.im| := abs_add_le _ _
      nlinarith [hvmax, htriangle', hwImSmall, hpowx]
  have hReBound (w : ℂ) (hw : ‖w‖ ≤ 8 * rstar) :
      |(s₀ + w).re - 1| ≤ 10 * rstar := by
    have hRew : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hReEq : (s₀ + w).re - 1 = rstar + w.re := by
      simp [s₀]
      ring
    rw [hReEq]
    calc
      |rstar + w.re| ≤ |rstar| + |w.re| := abs_add_le _ _
      _ ≤ rstar + 8 * rstar := add_le_add (le_of_eq (abs_of_pos hrpos)) (hRew.trans hw)
      _ ≤ 10 * rstar := by nlinarith [hrpos]
  have hLanalytic : AnalyticOnNhd ℂ
      (fun s : ℂ ↦ dirichletLValue q hq χ s) ({1}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
    intro s hs
    change DifferentiableWithinAt ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ) s
    exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hFanalytic : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) (8 * rstar)) := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 8 * rstar := by simpa [mem_closedBall_zero_iff] using hw
    have hnotPole : s₀ + w ≠ 1 := by
      intro heq
      have himEq : (s₀ + w).im = v + w.im := by simp [s₀]
      have himPositive : 1 / 2 ≤ |(s₀ + w).im| := by
        rw [himEq]
        exact (hImag w hwNorm).1
      rw [heq] at himPositive
      norm_num at himPositive
    have hLAt : AnalyticAt ℂ (fun s : ℂ ↦ dirichletLValue q hq χ s) (s₀ + w) :=
      hLanalytic (s₀ + w) (by simpa using hnotPole)
    have hshift : AnalyticAt ℂ (fun z : ℂ ↦ s₀ + z) w := by fun_prop
    simpa [F, Function.comp_def] using hLAt.comp hshift
  have hFbound : ∀ w ∈ closedBall (0 : ℂ) (8 * rstar), ‖F w‖ ≤ Real.exp M := by
    intro w hw
    have hwNorm : ‖w‖ ≤ 8 * rstar := by simpa [mem_closedBall_zero_iff] using hw
    let σ := (s₀ + w).re
    let y := (s₀ + w).im
    have hcoord : (⟨σ, y⟩ : ℂ) = s₀ + w := by
      rw [Complex.ext_iff]
      constructor <;> simp [σ, y, s₀]
    have hupper := hUpperBoundX σ y (by simpa [σ] using hReBound w hwNorm)
      (by simpa [y] using (hImag w hwNorm).1) (by simpa [y] using (hImag w hwNorm).2)
    have hupper' : ‖dirichletLValue q hq χ (s₀ + w)‖ ≤ Real.exp (CUpper * T ^ 2) := by
      simpa [dirichletLValue, hcoord] using hupper
    have hMupper : CUpper * T ^ 2 ≤ M := by
      have hCUpperK : CUpper ≤ K := by dsimp [K]; linarith [hC]
      dsimp [M]
      exact mul_le_mul_of_nonneg_right hCUpperK (sq_nonneg T)
    exact hupper'.trans (Real.exp_le_exp.mpr hMupper)
  have hcenterF : Real.exp (-M) ≤ ‖F 0‖ := by simpa [F, s₀] using hcenter
  obtain ⟨R, Z, hRlo, hRhi, hcircle, hZlen, hZroots, hZcomplete, hlogderiv⟩ :=
    disk_local_logderiv_bound hrpos hM hFanalytic hFbound hcenterF
  let Z' : List ℂ := Z.map fun ρ ↦ s₀ + ρ
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < 4 * rstar) hRlo
  have hlogden : 0 < Real.log (8 / 5) := Real.log_pos (by norm_num)
  have hZlen' : (Z'.length : ℝ) ≤ COut * T ^ 2 := by
    have hlenM : (Z.length : ℝ) ≤ 2 * K * T ^ 2 / Real.log (8 / 5) := by
      calc
        (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) := hZlen
        _ = 2 * K * T ^ 2 / Real.log (8 / 5) := by simp [M] <;> ring
    dsimp [Z']
    rw [List.length_map]
    have hcoeff : 2 * K / Real.log (8 / 5) ≤ COut := by
      dsimp [COut]
      linarith
    calc
      (Z.length : ℝ) ≤ 2 * K * T ^ 2 / Real.log (8 / 5) := hlenM
      _ = (2 * K / Real.log (8 / 5)) * T ^ 2 := by ring
      _ ≤ COut * T ^ 2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hZroots' : ∀ ρ ∈ Z',
      dirichletLValue q hq χ ρ = 0 ∧ ‖ρ - s₀‖ < R := by
    intro ρ hρ
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hρ
    have hroot := hZroots a ha
    refine ⟨?_, ?_⟩
    · simpa [F, s₀] using hroot.1
    · simpa using hroot.2
  have hZcomplete' : ∀ ρ : ℂ, dirichletLValue q hq χ ρ = 0 →
      ‖ρ - s₀‖ < R → ρ ∈ Z' := by
    intro ρ hroot hnorm
    have hlocalZero : F (ρ - s₀) = 0 := by simpa [F, sub_add_cancel] using hroot
    have hlocalMem := hZcomplete (ρ - s₀) hlocalZero (by simpa using hnorm)
    apply List.mem_map.mpr
    exact ⟨ρ - s₀, hlocalMem, by ring⟩
  have hcircle' : ∀ z : ℂ, ‖z - s₀‖ = R →
      dirichletLValue q hq χ z ≠ 0 := by
    intro z hz
    have hlocal := hcircle (z - s₀) (by simpa using hz)
    simpa [F, sub_add_cancel] using hlocal
  have hgenCoeff :
      100 * (M + 1) / R + 2 * (Z.length : ℝ) / R ≤
        COut * T ^ 2 / rstar := by
    have hterm1 : 100 * (M + 1) / R ≤ 25 * (K + 1) * T ^ 2 / rstar := by
      apply (div_le_div_iff₀ hRpos hrpos).2
      have hT2one : 1 ≤ T ^ 2 := by nlinarith [hTge']
      have hNumer : M + 1 ≤ (K + 1) * T ^ 2 := by
        dsimp [M]
        calc
          K * T ^ 2 + 1 ≤ K * T ^ 2 + T ^ 2 := add_le_add (le_refl _) hT2one
          _ = (K + 1) * T ^ 2 := by ring
      calc
        100 * (M + 1) * rstar ≤ 100 * ((K + 1) * T ^ 2) * rstar :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNumer (by norm_num)) hrpos.le
        _ = 25 * ((K + 1) * T ^ 2) * (4 * rstar) := by ring
        _ ≤ 25 * ((K + 1) * T ^ 2) * R :=
          mul_le_mul_of_nonneg_left hRlo (by positivity)
        _ = 25 * (K + 1) * T ^ 2 * R := by ring
    have hlenK : (Z.length : ℝ) ≤ 2 * K * T ^ 2 / Real.log (8 / 5) := by
      calc
        (Z.length : ℝ) ≤ 2 * M / Real.log (8 / 5) := hZlen
        _ = 2 * K * T ^ 2 / Real.log (8 / 5) := by dsimp [M]; ring
    have hterm2 : 2 * (Z.length : ℝ) / R ≤
        (K / Real.log (8 / 5)) * T ^ 2 / rstar := by
      apply (div_le_div_iff₀ hRpos hrpos).2
      have hlenScale : 2 * (Z.length : ℝ) ≤
          4 * K * T ^ 2 / Real.log (8 / 5) := by
        calc
          2 * (Z.length : ℝ) ≤ 2 * (2 * K * T ^ 2 / Real.log (8 / 5)) :=
            mul_le_mul_of_nonneg_left hlenK (by norm_num)
          _ = 4 * K * T ^ 2 / Real.log (8 / 5) := by ring
      calc
        (2 * (Z.length : ℝ)) * rstar ≤
            (4 * K * T ^ 2 / Real.log (8 / 5)) * rstar :=
          mul_le_mul_of_nonneg_right hlenScale hrpos.le
        _ = (K / Real.log (8 / 5) * T ^ 2) * (4 * rstar) := by ring
        _ ≤ (K / Real.log (8 / 5) * T ^ 2) * R :=
          mul_le_mul_of_nonneg_left hRlo (by positivity)
    calc
      100 * (M + 1) / R + 2 * (Z.length : ℝ) / R ≤
          25 * (K + 1) * T ^ 2 / rstar +
            (K / Real.log (8 / 5)) * T ^ 2 / rstar :=
          add_le_add hterm1 hterm2
      _ ≤ COut * T ^ 2 / rstar := by
        have hcoeff : 25 * (K + 1) + K / Real.log (8 / 5) ≤ COut := by
          have hratio : 0 ≤ K / Real.log (8 / 5) := by positivity
          have hsum : K / Real.log (8 / 5) ≤
              2 * K / Real.log (8 / 5) + 1 := by
            calc
              K / Real.log (8 / 5) ≤
                  K / Real.log (8 / 5) + K / Real.log (8 / 5) :=
                le_add_of_nonneg_right hratio
              _ ≤ K / Real.log (8 / 5) + K / Real.log (8 / 5) + 1 :=
                le_add_of_nonneg_right (by norm_num)
              _ = 2 * K / Real.log (8 / 5) + 1 := by ring
          calc
            25 * (K + 1) + K / Real.log (8 / 5) ≤
                25 * (K + 1) + (2 * K / Real.log (8 / 5) + 1) :=
              add_le_add (le_rfl) hsum
            _ = COut := by dsimp [COut]; ring
        calc
          _ = (25 * (K + 1) * T ^ 2 + (K / Real.log (8 / 5)) * T ^ 2) / rstar := by
            ring
          _ = (25 * (K + 1) + K / Real.log (8 / 5)) * T ^ 2 / rstar := by ring
          _ ≤ COut * T ^ 2 / rstar :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)) (le_of_lt hrpos)
  have hImagLowerAt (z : ℂ) (hz : ‖z - s₀‖ ≤ 2 * rstar) :
      (1 / 2 : ℝ) ≤ |z.im| := by
    have hlocalNorm : ‖z - s₀‖ ≤ 8 * rstar := by
      calc
        ‖z - s₀‖ ≤ 2 * rstar := hz
        _ ≤ 8 * rstar := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 8) hrpos.le
    have him := (hImag (z - s₀) hlocalNorm).1
    have himeq : v + (z - s₀).im = z.im := by
      simp [s₀]
    rw [himeq] at him
    exact him
  have hLdiffAt (z : ℂ) (hz : (1 / 2 : ℝ) ≤ |z.im|) :
      DifferentiableAt ℂ (fun s : ℂ ↦ dirichletLValue q hq χ s) z := by
    have hzPole : z ≠ 1 := by
      intro h
      have : (1 / 2 : ℝ) ≤ |(1 : ℂ).im| := by simpa [h] using hz
      norm_num at this
    change DifferentiableAt ℂ (DirichletCharacter.LFunction χ) z
    exact DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hzPole)
  have hderivShift (z : ℂ) (hz : (1 / 2 : ℝ) ≤ |z.im|) :
      deriv F (z - s₀) = deriv (fun s : ℂ ↦ dirichletLValue q hq χ s) z := by
    have houter := (hLdiffAt z hz).hasDerivAt
    have hinner : HasDerivAt (fun w : ℂ ↦ s₀ + w) 1 (z - s₀) := by
      simpa [add_comm] using (hasDerivAt_id (z - s₀)).const_add s₀
    have hpoint : z = s₀ + (z - s₀) := by ring
    have hcomp := HasDerivAt.comp_of_eq (hh₂ := houter) (hh := hinner) (hy := hpoint)
    simpa [F, Function.comp_def, sub_add_cancel, mul_one] using hcomp.deriv
  refine ⟨R, hRlo, hRhi, Z', hZlen', hZroots', hZcomplete', hcircle', ?_⟩
  intro z hz hne
  have hlocalNorm : ‖z - s₀‖ ≤ 2 * rstar := hz
  have hzImag := hImagLowerAt z hlocalNorm
  have hFne : F (z - s₀) ≠ 0 := by simpa [F, sub_add_cancel] using hne
  have herr := hlogderiv (z - s₀) (by simpa using hlocalNorm) hFne
  have hratio : logDeriv F (z - s₀) =
      deriv (fun s : ℂ ↦ dirichletLValue q hq χ s) z /
        dirichletLValue q hq χ z := by
    rw [logDeriv_apply, hderivShift z hzImag]
    simp [F, sub_add_cancel]
  have hpoles :
      (Z.map fun ρ ↦ (1 : ℂ) / ((z - s₀) - ρ)).sum =
        (Z'.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum := by
    simp only [Z', List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro ρ hρ
    congr 1
    ring
  have herrorShift :
      ‖deriv (fun s : ℂ ↦ dirichletLValue q hq χ s) z /
          dirichletLValue q hq χ z -
        (Z'.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum‖ ≤
        100 * (M + 1) / R + 2 * (Z.length : ℝ) / R := by
    have herr' := herr
    rw [hratio, hpoles] at herr'
    exact herr'
  exact herrorShift.trans hgenCoeff

set_option maxHeartbeats 200000

private theorem three_four_one_complex_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnorm2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have hsq : ‖z‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      exact sq_le_sq₀ (norm_nonneg _) (by norm_num) |>.2 hz
    have hsq' : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      ring
    simpa [hsq'] using hsq
  have hreal : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_two, Complex.mul_re]
  rw [hreal]
  nlinarith [sq_nonneg (1 + z.re), hnorm2]

set_option maxHeartbeats 1000000 in
private theorem three_four_one_lseries_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ v : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
          (σ : ℂ)).re +
        4 * (LSeries (fun n : ℕ ↦ χ (n : ZMod q) *
          (ArithmeticFunction.vonMangoldt n : ℂ))
          ((σ : ℂ) + Complex.I * v)).re +
        (LSeries (fun n : ℕ ↦ (χ (n : ZMod q)) ^ 2 *
          (ArithmeticFunction.vonMangoldt n : ℂ))
          ((σ : ℂ) + Complex.I * (2 * v))).re := by
  classical
  let Λc : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)
  let χc : ℕ → ℂ := fun n ↦ χ (n : ZMod q)
  let fA : ℕ → ℂ := Λc
  let fB : ℕ → ℂ := fun n ↦ χc n * Λc n
  let fC : ℕ → ℂ := fun n ↦ (χc n) ^ 2 * Λc n
  let sA : ℂ := (σ : ℂ)
  let sB : ℂ := (σ : ℂ) + Complex.I * v
  let sC : ℂ := (σ : ℂ) + Complex.I * (2 * v)
  have hsA : 1 < sA.re := by simpa [sA] using hσ
  have hsB : 1 < sB.re := by simpa [sB] using hσ
  have hsC : 1 < sC.re := by simpa [sC] using hσ
  have hsumA : LSeriesSummable fA sA := by
    simpa [fA, Λc] using ArithmeticFunction.LSeriesSummable_vonMangoldt hsA
  have hsumB : LSeriesSummable fB sB := by
    change LSeriesSummable ((fun n : ℕ ↦ χ (n : ZMod q)) *
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))) sB
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsB
  have hseqC : fC = fun n : ℕ ↦ (χ ^ 2) (n : ZMod q) * Λc n := by
    funext n
    simp [fC, χc, Λc, χ.pow_apply' two_ne_zero]
  have hsumC : LSeriesSummable fC sC := by
    rw [hseqC]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) hsC
  have hA := hasSum_re hsumA.LSeriesHasSum
  have hB := hasSum_re hsumB.LSeriesHasSum
  have hC := hasSum_re hsumC.LSeriesHasSum
  have hTotal : HasSum
      (fun n : ℕ ↦ 3 * (LSeries.term fA sA n).re +
        4 * (LSeries.term fB sB n).re + (LSeries.term fC sC n).re)
      (3 * (LSeries fA sA).re + 4 * (LSeries fB sB).re + (LSeries fC sC).re) := by
    exact (hA.mul_left 3).add (hB.mul_left 4) |>.add hC
  have hterm (n : ℕ) :
      0 ≤ 3 * (LSeries.term fA sA n).re +
        4 * (LSeries.term fB sB n).re + (LSeries.term fC sC n).re := by
    by_cases hn : n = 0
    · simp [hn, LSeries.term_zero]
    let b : ℝ := ArithmeticFunction.vonMangoldt n * Real.rpow (n : ℝ) (-σ)
    let a : ℂ := χc n * (n : ℂ) ^ (-(Complex.I * (v : ℂ)))
    have hpowA : (n : ℂ) ^ (-sA) = ((Real.rpow (n : ℝ) (-σ)) : ℂ) := by
      have hsA' : -sA = -(σ : ℂ) := by simp [sA]
      have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      calc
        (n : ℂ) ^ (-sA) = ((n : ℝ) : ℂ) ^ (-(σ : ℂ)) := by rw [hsA', hbase]
        _ = ((Real.rpow (n : ℝ) (-σ)) : ℂ) := by
          rw [← Complex.ofReal_neg]
          exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
    have hsB' : -sB = -sA + (-(Complex.I * (v : ℂ))) := by
      dsimp [sA, sB]
      ring
    have hpowB : (n : ℂ) ^ (-sB) =
        (n : ℂ) ^ (-sA) * (n : ℂ) ^ (-(Complex.I * (v : ℂ))) := by
      rw [hsB', Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    have hsC' : -sC = -sA + (-(Complex.I * (2 * v : ℂ))) := by
      dsimp [sA, sC]
      ring
    have hpowC : (n : ℂ) ^ (-sC) =
        (n : ℂ) ^ (-sA) * (n : ℂ) ^ (-(Complex.I * (2 * v : ℂ))) := by
      rw [hsC', Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    have hpowDouble : (n : ℂ) ^ (-(Complex.I * (2 * v : ℂ))) =
        ((n : ℂ) ^ (-(Complex.I * (v : ℂ)))) ^ 2 := by
      rw [show -(Complex.I * (2 * v : ℂ)) = (2 : ℕ) * (-(Complex.I * (v : ℂ))) by ring,
        Complex.cpow_nat_mul]
    have hΛzero : Λc 0 = 0 := by
      simp [Λc, ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
    have hAzero : fA 0 = 0 := by simpa [fA] using hΛzero
    have hBzero : fB 0 = 0 := by simp [fB, χc, Λc, hΛzero]
    have hCzero : fC 0 = 0 := by simp [fC, χc, Λc, hΛzero]
    have hAterm : LSeries.term fA sA n = (b : ℂ) := by
      rw [LSeries.term_def₀ hAzero sA n, hpowA]
      simp [fA, Λc, b, Complex.ofReal_mul]
    have hBterm : LSeries.term fB sB n = (b : ℂ) * a := by
      rw [LSeries.term_def₀ hBzero sB n, hpowB, hpowA]
      simp [fB, χc, Λc, a, b, Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm]
    have hCterm : LSeries.term fC sC n = (b : ℂ) * a ^ 2 := by
      rw [LSeries.term_def₀ hCzero sC n, hpowC, hpowA, hpowDouble]
      simp only [fC, χc, Λc, a, b, Complex.ofReal_mul]
      ring
    have hχnorm : ‖χc n‖ ≤ 1 := by simpa [χc] using χ.norm_le_one (n : ZMod q)
    have hpowNorm : ‖(n : ℂ) ^ (-(Complex.I * (v : ℂ)))‖ = 1 := by
      have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
      rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]
      simp
    have hanorm : ‖a‖ ≤ 1 := by
      change ‖χc n * (n : ℂ) ^ (-(Complex.I * (v : ℂ)))‖ ≤ 1
      rw [norm_mul, hpowNorm]
      simpa only [mul_one] using hχnorm
    have htrig := three_four_one_complex_nonneg hanorm
    have hbnonneg : 0 ≤ b := by
      dsimp [b]
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    calc
      0 ≤ b * (3 + 4 * a.re + (a ^ 2).re) := mul_nonneg hbnonneg htrig
      _ = 3 * (LSeries.term fA sA n).re +
          4 * (LSeries.term fB sB n).re + (LSeries.term fC sC n).re := by
        rw [hAterm, hBterm, hCterm]
        simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, zero_mul,
          mul_zero, sub_zero]
        ring
  have hsumNonneg : 0 ≤ ∑' n : ℕ,
      (3 * (LSeries.term fA sA n).re +
        4 * (LSeries.term fB sB n).re + (LSeries.term fC sC n).re) :=
    tsum_nonneg hterm
  have htotalEq := hTotal.tsum_eq
  have hgoal : 0 ≤ 3 * (LSeries fA sA).re + 4 * (LSeries fB sB).re +
      (LSeries fC sC).re := by simpa using hsumNonneg.trans_eq htotalEq
  simpa [fA, fB, fC, χc, Λc, sA, sB, sC] using hgoal

set_option maxHeartbeats 1000000 in
private theorem three_four_one_logderiv_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ v : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + Complex.I * v) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * v)).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + Complex.I * (2 * v)) /
          DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + Complex.I * (2 * v))).re := by
  let fA : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)
  let fB : ℕ → ℂ := fun n ↦ χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)
  let fC : ℕ → ℂ := fun n ↦ (χ (n : ZMod q)) ^ 2 *
    (ArithmeticFunction.vonMangoldt n : ℂ)
  let sA : ℂ := (σ : ℂ)
  let sB : ℂ := (σ : ℂ) + Complex.I * v
  let sC : ℂ := (σ : ℂ) + Complex.I * (2 * v)
  have hsA : 1 < sA.re := by simpa [sA] using hσ
  have hsB : 1 < sB.re := by simpa [sB] using hσ
  have hsC : 1 < sC.re := by simpa [sC] using hσ
  have hAeq : LSeries fA sA = -deriv riemannZeta sA / riemannZeta sA := by
    simpa [fA, sA] using ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsA
  have hBeq : LSeries fB sB =
      -deriv (DirichletCharacter.LFunction χ) sB /
        DirichletCharacter.LFunction χ sB := by
    have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hsB
    rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hsB,
      ← DirichletCharacter.LFunction_eq_LSeries χ hsB] at htw
    change LSeries ((fun n : ℕ ↦ χ (n : ZMod q)) *
      (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))) sB = _
    exact htw
  have hCeq : LSeries fC sC =
      -deriv (DirichletCharacter.LFunction (χ ^ 2)) sC /
        DirichletCharacter.LFunction (χ ^ 2) sC := by
    have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq (χ ^ 2) hsC
    rw [← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries (χ ^ 2) hsC,
      ← DirichletCharacter.LFunction_eq_LSeries (χ ^ 2) hsC] at htw
    have hseq : fC = fun n : ℕ ↦ (χ ^ 2) (n : ZMod q) *
        (ArithmeticFunction.vonMangoldt n : ℂ) := by
      funext n
      simp [fC, χ.pow_apply' two_ne_zero]
    rw [hseq]
    exact htw
  have hseries := three_four_one_lseries_nonneg (v := v) χ hσ
  rw [hAeq, hBeq, hCeq] at hseries
  simpa [fA, fB, fC, sA, sB, sC] using hseries

private theorem zeta_logderiv_bound_near_one :
    ∃ K ε : ℝ, 0 < K ∧ 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ < ε →
        (-(deriv riemannZeta (1 + (δ : ℂ)) /
          riemannZeta (1 + (δ : ℂ)))).re ≤ 1 / δ + K := by
  obtain ⟨K, hKpos, hK⟩ :=
    log_deriv_riemannZeta_add_inv_sub_bounded.exists_pos
  have hbound : ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖ ≤ K := by
    filter_upwards [hK.bound] with s hs
    simpa using hs
  have hbound' : ∀ᶠ s in 𝓝 (1 : ℂ),
      s ≠ 1 → ‖deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹‖ ≤ K := by
    simpa only [eventually_nhdsWithin_iff, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hbound
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.1 hbound'
  refine ⟨K, ε, hKpos, hεpos, ?_⟩
  intro δ hδ hδε
  let s : ℂ := 1 + (δ : ℂ)
  have hsne : s ≠ 1 := by
    intro hs
    have := congrArg Complex.re hs
    simp [s] at this
    linarith
  have hsminus : s - 1 = (δ : ℂ) := by simp [s]
  have hdist : dist s (1 : ℂ) < ε := by
    rw [dist_eq_norm, hsminus, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
    exact hδε
  have hErr := hε hdist hsne
  have hErrRe :
      (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹).re ≤ K := by
    exact (le_abs_self _).trans ((abs_re_le_norm _).trans hErr)
  have hErrReLower :
      -K ≤ (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹).re := by
    have habs := (abs_re_le_norm
      (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹)).trans hErr
    exact (abs_le.mp habs).1
  have hmain :
      -(deriv riemannZeta s / riemannZeta s) =
        (δ : ℂ)⁻¹ - (deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹) := by
    rw [hsminus]
    ring
  have hinv : ((δ : ℂ)⁻¹).re = 1 / δ := by
    rw [Complex.inv_re, Complex.normSq_ofReal, Complex.ofReal_re]
    field_simp [hδ.ne']
  have hboundS :
      (-(deriv riemannZeta s / riemannZeta s)).re ≤ 1 / δ + K := by
    rw [hmain, Complex.sub_re, hinv]
    linarith [hErrReLower]
  simpa [s] using hboundS

private theorem list_sum_nonneg_of_forall {α : Type*} (Z : List α) (f : α → ℝ)
    (h : ∀ a ∈ Z, 0 ≤ f a) : 0 ≤ (Z.map f).sum := by
  induction Z with
  | nil => simp
  | cons a Z ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha : 0 ≤ f a := h a (by simp)
    have hZ : ∀ b ∈ Z, 0 ≤ f b := by
      intro b hb
      exact h b (by simp [hb])
    have htail := ih hZ
    linarith

private theorem list_sum_ge_mem {α : Type*} (Z : List α) (f : α → ℝ)
    (h : ∀ a ∈ Z, 0 ≤ f a) {a : α} (ha : a ∈ Z) :
    f a ≤ (Z.map f).sum := by
  induction Z with
  | nil => simp at ha
  | cons b Z ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with hab | ha
    · cases hab
      have htail : 0 ≤ (Z.map f).sum :=
        list_sum_nonneg_of_forall Z f (by
          intro c hc
          exact h c (by simp [hc]))
      linarith
    · have hhead : 0 ≤ f b := h b (by simp)
      have htail : f a ≤ (Z.map f).sum := ih (by
        intro c hc
        exact h c (by simp [hc])) ha
      linarith

private theorem list_map_re_sum (Z : List ℂ) (f : ℂ → ℂ) :
    (Z.map f).sum.re = (Z.map fun z ↦ (f z).re).sum := by
  induction Z with
  | nil => simp
  | cons z Z ih => simp [ih]

private theorem list_reciprocal_sum_nonneg (Z : List ℂ) (z : ℂ)
    (hZ : ∀ ρ ∈ Z, ρ.re ≤ z.re) :
    0 ≤ (Z.map fun ρ ↦ (1 : ℂ) / (z - ρ)).sum.re := by
  rw [list_map_re_sum]
  apply list_sum_nonneg_of_forall
  intro ρ hρ
  have hdiff : 0 ≤ (z - ρ).re := by
    simpa [Complex.sub_re] using sub_nonneg.mpr (hZ ρ hρ)
  rw [Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_add, one_mul,
    zero_div, add_zero]
  have hden : 0 ≤ normSq (z - ρ) := by
    rw [normSq_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact div_nonneg hdiff hden

private theorem complex_reciprocal_re_nonneg (z ρ : ℂ) (hρ : ρ.re ≤ z.re) :
    0 ≤ ((1 : ℂ) / (z - ρ)).re := by
  have hdiff : 0 ≤ (z - ρ).re := by
    simpa [Complex.sub_re] using sub_nonneg.mpr hρ
  rw [Complex.div_re]
  simp only [Complex.one_re, Complex.one_im, zero_mul, zero_add, one_mul,
    zero_div, add_zero]
  have hden : 0 ≤ normSq (z - ρ) := by
    rw [normSq_apply]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact div_nonneg hdiff hden

private theorem complex_reciprocal_re_of_same_im (z ρ : ℂ)
    (him : z.im = ρ.im) (hre : ρ.re < z.re) :
    ((1 : ℂ) / (z - ρ)).re = 1 / (z.re - ρ.re) := by
  have hdiff : z - ρ = ((z.re - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext_iff.mpr
    constructor <;> simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, him]
  rw [hdiff, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.one_re, Complex.one_im, one_mul, zero_mul, add_zero]
  have hne : z.re - ρ.re ≠ 0 := ne_of_gt (sub_pos.mpr hre)
  field_simp [hne] <;> ring_nf

/-- A triangle bound for the finite logarithmic-derivative sum. -/
private theorem list_norm_sum_map_le {α : Type*} (Z : List α) (f : α → ℂ) (K : ℝ)
    (h : ∀ a ∈ Z, ‖f a‖ ≤ K) :
    ‖(Z.map f).sum‖ ≤ (Z.length : ℝ) * K := by
  induction Z with
  | nil => simp
  | cons a Z ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    have ha : ‖f a‖ ≤ K := h a (by simp)
    have hZ : ∀ b ∈ Z, ‖f b‖ ≤ K := by
      intro b hb
      exact h b (by simp [hb])
    have htail := ih hZ
    calc
      ‖f a + (Z.map f).sum‖ ≤ ‖f a‖ + ‖(Z.map f).sum‖ := norm_add_le _ _
      _ ≤ K + (Z.length : ℝ) * K := add_le_add ha htail
      _ = ((Z.length : ℝ) + 1) * K := by ring

private theorem complex_norm_sub_eq_abs_of_im_eq (z w : ℂ) (him : z.im = w.im) :
    ‖z - w‖ = |z.re - w.re| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [Complex.sq_norm, normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, him]
  ring

private theorem dirichletLFunction_zero_re_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) : ρ.re ≤ 1 := by
  by_contra h
  have hgt : 1 < ρ.re := lt_of_not_ge h
  have hne : ρ ≠ 1 := by
    intro heq
    have := congrArg Complex.re heq
    simp at this
    linarith
  exact (χ.LFunction_ne_zero_of_one_le_re (Or.inr hne) (le_of_lt hgt)) hzero

set_option maxHeartbeats 10000000
/-- `t2:pp.zero-free` — PP `02-long-prime.tex:426-481`, Lemma 3.6. -/
theorem zero_free :
    ∀ C : ℝ, 0 < C →
      ∃ c C₀ x₀ : ℝ, 0 < c ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let T := Real.log L
          let width := c * T ^ 2 / L
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ hq : 0 < q, ∀ χ : DirichletCharacter ℂ q,
              (∀ s : ℂ, 1 - width ≤ s.re →
                1 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 →
                  dirichletLValue q hq χ s ≠ 0) ∧
              (∀ s : ℂ, 1 - width / 2 ≤ s.re → s.re ≤ 1 + 1 / L →
                2 ≤ |s.im| → |s.im| ≤ Real.rpow x 3 / 2 →
                  ‖deriv (dirichletLValue q hq χ) s /
                    dirichletLValue q hq χ s‖ ≤ C₀ * L) := by
  classical
  intro C hC
  obtain ⟨CLog, xLog, hCLog, hxLog, hLocal⟩ := local_logderiv C hC
  obtain ⟨Kζ, εζ, hKζ, hεζ, hζBound⟩ := zeta_logderiv_bound_near_one
  let c : ℝ := 1 / (1000 * (CLog + 1))
  let COut : ℝ := 2 * CLog / c + CLog + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hc20 : 20 * c ≤ 1 := by
    dsimp [c]
    calc
      20 * (1 / (1000 * (CLog + 1))) = 20 / (1000 * (CLog + 1)) := by ring
      _ ≤ 1 := (div_le_iff₀ (by positivity : 0 < 1000 * (CLog + 1))).2 (by nlinarith [hCLog])
  have hcinv : c⁻¹ = 1000 * (CLog + 1) := by
    dsimp [c]
    field_simp
  have hcoeffMain : 3 / (20 * c) - 4 / (21 * c) = (-17 / 420) * c⁻¹ := by
    field_simp [hc.ne']
    ring
  have hcoeff : 3 / (20 * c) - 4 / (21 * c) + 3 + 5 * CLog < 0 := by
    rw [hcoeffMain, hcinv]
    nlinarith [hCLog]
  have hCOut : 0 < COut := by dsimp [COut]; positivity
  let Lfun : ℝ → ℝ := fun x ↦ Real.log x
  let Tfun : ℝ → ℝ := fun x ↦ Real.log (Real.log x)
  let rfun : ℝ → ℝ := fun x ↦ (Tfun x) ^ 4 / Lfun x
  let δfun : ℝ → ℝ := fun x ↦ 20 * c * (Tfun x) ^ 2 / Lfun x
  have hTlim : Tendsto Tfun atTop atTop := by
    simpa [Tfun, Function.comp_def] using
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hr4 : Tendsto rfun atTop (𝓝 0) := by
    simpa [rfun, Tfun, Lfun, Function.comp_def] using
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp
        Real.tendsto_log_atTop)
  have hr2 : Tendsto (fun x : ℝ ↦ (Tfun x) ^ 2 / Lfun x) atTop (𝓝 0) := by
    simpa [Tfun, Lfun, Function.comp_def] using
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
        Real.tendsto_log_atTop)
  have hδlim : Tendsto δfun atTop (𝓝 0) := by
    have hδfunEq : δfun = fun x ↦ 20 * c * ((Tfun x) ^ 2 / Lfun x) := by
      funext x
      simp [δfun]
      ring
    rw [hδfunEq]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ 20 * c) atTop (𝓝 (20 * c))).mul hr2
  have hTevent : ∀ᶠ x : ℝ in atTop, 1 ≤ Tfun x :=
    hTlim.eventually (eventually_ge_atTop (1 : ℝ))
  have hrSmall : ∀ᶠ x : ℝ in atTop, rfun x < 1 / 16 :=
    hr4.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hδSmall : ∀ᶠ x : ℝ in atTop, δfun x < εζ :=
    hδlim.eventually (Iio_mem_nhds hεζ)
  have hr2Small : ∀ᶠ x : ℝ in atTop,
      (Tfun x) ^ 2 / Lfun x < 1 / (Kζ + 1) :=
    hr2.eventually (Iio_mem_nhds (by positivity))
  have hLarge : ∀ᶠ x : ℝ in atTop,
      xLog ≤ x ∧ 2 < x ∧ 1 ≤ Tfun x ∧ rfun x < 1 / 16 ∧
        δfun x < εζ ∧ (Tfun x) ^ 2 / Lfun x < 1 / (Kζ + 1) := by
    filter_upwards [eventually_ge_atTop xLog, eventually_gt_atTop (2 : ℝ),
      hTevent, hrSmall, hδSmall, hr2Small] with x hxLogX hx2 hxT hhr hδ hr2x
    exact ⟨hxLogX, hx2, hxT, hhr, hδ, hr2x⟩
  obtain ⟨x₀, hx₀large⟩ := Filter.eventually_atTop.1 hLarge
  have hx₀ : 2 < x₀ := (hx₀large x₀ le_rfl).2.1
  refine ⟨c, COut, x₀, hc, hCOut, hx₀, ?_⟩
  intro x hx
  dsimp only
  intro q hq1 hqBound hq χ
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let L : ℝ := Real.log x
  let T : ℝ := Real.log L
  let width : ℝ := c * T ^ 2 / L
  let rstar : ℝ := T ^ 4 / L
  rcases hx₀large x hx with ⟨hxLogX, hx2, hTge, hrSmallX, hδSmallX, hr2SmallX⟩
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hTpos : 0 < T := by linarith
  have hT2pos : 0 < T ^ 2 := by positivity
  have hT2ge1 : 1 ≤ T ^ 2 := by
    nlinarith [sq_nonneg (T - 1)]
  have hT4geT2 : T ^ 2 ≤ T ^ 4 := by
    nlinarith [sq_nonneg (T ^ 2 - 1)]
  have hT4ge1 : 1 ≤ T ^ 4 := le_trans hT2ge1 hT4geT2
  have hrpos : 0 < rstar := by dsimp [rstar]; positivity
  have hrSmallX' : rstar < 1 / 16 := by
    simpa [rstar, L, T, rfun, Tfun, Lfun] using hrSmallX
  have hδpos : 0 < 20 * c * T ^ 2 / L := by positivity
  have hδsmall : 20 * c * T ^ 2 / L < εζ := by
    simpa [L, T, δfun, Tfun, Lfun] using hδSmallX
  have hKratio : Kζ ≤ L / T ^ 2 := by
    have hcross : T ^ 2 * (Kζ + 1) < L := by
      have hratio : T ^ 2 / L < 1 / (Kζ + 1) := by
        simpa [L, T, Tfun, Lfun] using hr2SmallX
      have hstep : T ^ 2 < L / (Kζ + 1) := by
        simpa [div_eq_mul_inv, mul_comm] using (div_lt_iff₀ hLpos).mp hratio
      exact (lt_div_iff₀ (by positivity : 0 < Kζ + 1)).mp hstep
    apply (le_div_iff₀ hT2pos).2
    nlinarith [hcross]
  have h20cle : 20 * c * T ^ 2 ≤ T ^ 4 := by
    calc
      20 * c * T ^ 2 ≤ T ^ 2 := by nlinarith [hc20, hT2pos]
      _ ≤ T ^ 4 := hT4geT2
  have hwidthle : width ≤ rstar := by
    dsimp [width, rstar]
    exact (div_le_div_iff₀ hLpos hLpos).2 (by nlinarith [hc20, hT4geT2])
  have hδle : 20 * c * T ^ 2 / L ≤ rstar := by
    dsimp [rstar]
    exact (div_le_div_iff₀ hLpos hLpos).2
      (mul_le_mul_of_nonneg_right h20cle hLpos.le)
  have hLocalApply (χ' : DirichletCharacter ℂ q) (v' : ℝ)
      (hv'low : 1 ≤ |v'|)
      (hv'high : |v'| ≤ (5 / 2 : ℝ) * Real.rpow x 3) :=
    hLocal x hxLogX q hq1 hqBound hq χ' v' hv'low hv'high
  have hNoZero : ∀ s : ℂ, 1 - width ≤ s.re → 1 ≤ |s.im| →
      |s.im| ≤ Real.rpow x 3 → dirichletLValue q hq χ s ≠ 0 := by
    intro s hsRe hsImLow hsImHigh hsZero
    exfalso
    let β : ℝ := s.re
    let v : ℝ := s.im
    let ρ : ℂ := ⟨β, v⟩
    have hρeq : ρ = s := by
      apply Complex.ext_iff.mpr
      constructor <;> simp [ρ, β, v]
    have hβlower : 1 - width ≤ β := by simpa [β] using hsRe
    have hvlow : 1 ≤ |v| := by simpa [v] using hsImLow
    have hvhigh : |v| ≤ (5 / 2 : ℝ) * Real.rpow x 3 := by
      dsimp [v]
      calc
        |s.im| ≤ Real.rpow x 3 := hsImHigh
        _ ≤ (5 / 2 : ℝ) * Real.rpow x 3 := by
          nlinarith [Real.rpow_nonneg (le_of_lt hxpos) (3 : ℝ)]
    have hvhighActual : |v| ≤ Real.rpow x 3 := by simpa [v] using hsImHigh
    have hzeroρ : dirichletLValue q hq χ ρ = 0 := by
      simpa [ρ, β, v] using hsZero
    have hzeroρL : DirichletCharacter.LFunction χ ρ = 0 := by
      simpa [dirichletLValue] using hzeroρ
    have hβupper : β ≤ 1 := dirichletLFunction_zero_re_le_one χ ρ hzeroρL
    have hdistFormula :
        ‖ρ - (⟨1 + rstar, v⟩ : ℂ)‖ = |β - (1 + rstar)| := by
      exact complex_norm_sub_eq_abs_of_im_eq ρ ⟨1 + rstar, v⟩ (by simp [ρ, v])
    have hdistρ : ‖ρ - (⟨1 + rstar, v⟩ : ℂ)‖ ≤ 2 * rstar := by
      rw [hdistFormula]
      rw [abs_of_nonpos (by nlinarith [hrpos, hβupper])]
      nlinarith [hβlower, hwidthle]
    obtain ⟨R₁, hR₁low, hR₁high, Z₁, hZ₁len, hZ₁mem, hZ₁complete,
      hZ₁boundary, hZ₁formula⟩ := hLocalApply χ v hvlow hvhigh
    have hρdistR : ‖ρ - (⟨1 + rstar, v⟩ : ℂ)‖ < R₁ := by
      calc
        ‖ρ - (⟨1 + rstar, v⟩ : ℂ)‖ ≤ 2 * rstar := hdistρ
        _ < 4 * rstar := by nlinarith [hrpos]
        _ ≤ R₁ := hR₁low
    have hρmem : ρ ∈ Z₁ := hZ₁complete ρ hzeroρ hρdistR
    have hZ₁re : ∀ ρ' ∈ Z₁, ρ'.re ≤ 1 := by
      intro ρ' hρ'mem
      rcases hZ₁mem ρ' hρ'mem with ⟨hρ'zero, _⟩
      have hρ'zeroL : DirichletCharacter.LFunction χ ρ' = 0 := by
        simpa [dirichletLValue] using hρ'zero
      exact dirichletLFunction_zero_re_le_one χ ρ' hρ'zeroL
    have hβgap : 0 < (1 + 20 * c * T ^ 2 / L) - β := by
      have : 1 < 1 + 20 * c * T ^ 2 / L := by linarith [hδpos]
      linarith [hβupper]
    let σ : ℝ := 1 + 20 * c * T ^ 2 / L
    let z₁ : ℂ := ⟨σ, v⟩
    let z₂ : ℂ := ⟨σ, 2 * v⟩
    have hzDist (v' : ℝ) :
        ‖(⟨σ, v'⟩ : ℂ) - (⟨1 + rstar, v'⟩ : ℂ)‖ ≤ 2 * rstar := by
      rw [complex_norm_sub_eq_abs_of_im_eq _ _ (by simp)]
      have hσdiff : σ - (1 + rstar) = 20 * c * T ^ 2 / L - rstar := by
        dsimp [σ]
        ring
      rw [hσdiff, abs_of_nonpos (by linarith [hδle])]
      nlinarith [hrpos, hδle]
    have hz₁dist : ‖z₁ - (⟨1 + rstar, v⟩ : ℂ)‖ ≤ 2 * rstar := by
      simpa [z₁] using hzDist v
    have hz₂dist : ‖z₂ - (⟨1 + rstar, 2 * v⟩ : ℂ)‖ ≤ 2 * rstar := by
      simpa [z₂] using hzDist (2 * v)
    have hσgt : 1 < σ := by dsimp [σ]; linarith [hδpos]
    have hz₁ne1 : z₁ ≠ 1 := by
      intro heq
      have := congrArg Complex.re heq
      simp [z₁] at this
      linarith [hσgt]
    have hz₂ne1 : z₂ ≠ 1 := by
      intro heq
      have := congrArg Complex.re heq
      simp [z₂] at this
      linarith [hσgt]
    have hz₁Lne : DirichletCharacter.LFunction χ z₁ ≠ 0 :=
      χ.LFunction_ne_zero_of_one_le_re (Or.inr hz₁ne1)
        (by simpa [z₁] using le_of_lt hσgt)
    have hz₂Lne : DirichletCharacter.LFunction (χ ^ 2) z₂ ≠ 0 :=
      (χ ^ 2).LFunction_ne_zero_of_one_le_re (Or.inr hz₂ne1)
        (by simpa [z₂] using le_of_lt hσgt)
    have hz₁ne : dirichletLValue q hq χ z₁ ≠ 0 := by
      simpa [dirichletLValue] using hz₁Lne
    have hz₂ne : dirichletLValue q hq (χ ^ 2) z₂ ≠ 0 := by
      simpa [dirichletLValue] using hz₂Lne
    obtain ⟨R₂, hR₂low, hR₂high, Z₂, hZ₂len, hZ₂mem, hZ₂complete,
      hZ₂boundary, hZ₂formula⟩ := hLocalApply (χ ^ 2) (2 * v)
        (by rw [abs_mul]; norm_num; nlinarith [hvlow])
        (by
          calc
            |2 * v| = 2 * |v| := by rw [abs_mul]; norm_num
            _ ≤ 2 * Real.rpow x 3 :=
              mul_le_mul_of_nonneg_left hvhighActual (by norm_num)
            _ ≤ (5 / 2 : ℝ) * Real.rpow x 3 := by
              nlinarith [Real.rpow_nonneg (le_of_lt hxpos) (3 : ℝ)])
    have hZ₂re : ∀ ρ' ∈ Z₂, ρ'.re ≤ 1 := by
      intro ρ' hρ'mem
      rcases hZ₂mem ρ' hρ'mem with ⟨hρ'zero, _⟩
      have hρ'zeroL : DirichletCharacter.LFunction (χ ^ 2) ρ' = 0 := by
        simpa [dirichletLValue] using hρ'zero
      exact dirichletLFunction_zero_re_le_one (χ ^ 2) ρ' hρ'zeroL
    have hsum₂ : 0 ≤ (Z₂.map fun ρ' ↦ (1 : ℂ) / (z₂ - ρ')).sum.re :=
      list_reciprocal_sum_nonneg Z₂ z₂ (by
        intro ρ' hρ'mem
        have hρ' := hZ₂re ρ' hρ'mem
        simpa [z₂] using le_trans hρ' (by linarith [hσgt]))
    have hsum₁ : 1 / (σ - β) ≤
        (Z₁.map fun ρ' ↦ (1 : ℂ) / (z₁ - ρ')).sum.re := by
      rw [list_map_re_sum]
      have hnonneg : ∀ ρ' ∈ Z₁, 0 ≤ ((1 : ℂ) / (z₁ - ρ')).re := by
        intro ρ' hρ'mem
        exact complex_reciprocal_re_nonneg z₁ ρ' (by
          have hρ' := hZ₁re ρ' hρ'mem
          simpa [z₁] using le_trans hρ' (by linarith [hσgt]))
      have hlist := list_sum_ge_mem Z₁ (fun ρ' ↦ ((1 : ℂ) / (z₁ - ρ')).re)
        hnonneg (a := ρ) hρmem
      have him : z₁.im = ρ.im := by simp [z₁, ρ, v]
      have hre : ρ.re < z₁.re := by simpa [z₁, ρ, β] using hβgap
      have hterm : ((1 : ℂ) / (z₁ - ρ)).re = 1 / (σ - β) := by
        simpa [z₁, ρ, β] using complex_reciprocal_re_of_same_im z₁ ρ him hre
      rw [hterm] at hlist
      exact hlist
    let D₁ : ℂ := deriv (dirichletLValue q hq χ) z₁ / dirichletLValue q hq χ z₁
    let S₁ : ℂ := (Z₁.map fun ρ' ↦ (1 : ℂ) / (z₁ - ρ')).sum
    let D₂ : ℂ := deriv (dirichletLValue q hq (χ ^ 2)) z₂ /
      dirichletLValue q hq (χ ^ 2) z₂
    let S₂ : ℂ := (Z₂.map fun ρ' ↦ (1 : ℂ) / (z₂ - ρ')).sum
    have hform₁ : ‖D₁ - S₁‖ ≤ CLog * T ^ 2 / rstar := by
      simpa [D₁, S₁] using hZ₁formula z₁ hz₁dist hz₁ne
    have hform₂ : ‖D₂ - S₂‖ ≤ CLog * T ^ 2 / rstar := by
      simpa [D₂, S₂] using hZ₂formula z₂ hz₂dist hz₂ne
    have hE₁ : -(D₁ - S₁).re ≤ CLog * T ^ 2 / rstar := by
      have habs := (abs_re_le_norm (D₁ - S₁)).trans hform₁
      linarith [(abs_le.mp habs).1]
    have hE₂ : -(D₂ - S₂).re ≤ CLog * T ^ 2 / rstar := by
      have habs := (abs_re_le_norm (D₂ - S₂)).trans hform₂
      linarith [(abs_le.mp habs).1]
    have hminus₁ : (-D₁).re ≤ -1 / (σ - β) + CLog * T ^ 2 / rstar := by
      have hnegRe : (-D₁).re = -D₁.re := by simp
      have herror : S₁.re - D₁.re ≤ CLog * T ^ 2 / rstar := by
        simpa [Complex.sub_re] using hE₁
      have hsum₁' : 1 / (σ - β) ≤ S₁.re := by simpa [S₁] using hsum₁
      have hAminusD : 1 / (σ - β) - D₁.re ≤ CLog * T ^ 2 / rstar := by
        calc
          1 / (σ - β) - D₁.re ≤ S₁.re - D₁.re := sub_le_sub_right hsum₁' D₁.re
          _ ≤ CLog * T ^ 2 / rstar := herror
      rw [hnegRe]
      calc
        -D₁.re = (1 / (σ - β) - D₁.re) - 1 / (σ - β) := by ring
        _ ≤ CLog * T ^ 2 / rstar - 1 / (σ - β) :=
          sub_le_sub_right hAminusD (1 / (σ - β))
        _ = -1 / (σ - β) + CLog * T ^ 2 / rstar := by ring
    have hminus₂ : (-D₂).re ≤ CLog * T ^ 2 / rstar := by
      have hnegRe : (-D₂).re = -D₂.re := by simp
      have herror : S₂.re - D₂.re ≤ CLog * T ^ 2 / rstar := by
        simpa [Complex.sub_re] using hE₂
      have hsum₂' : 0 ≤ S₂.re := by simpa [S₂] using hsum₂
      rw [hnegRe]
      calc
        -D₂.re = (S₂.re - D₂.re) - S₂.re := by ring
        _ ≤ CLog * T ^ 2 / rstar - S₂.re :=
          sub_le_sub_right herror S₂.re
        _ ≤ CLog * T ^ 2 / rstar := by linarith [hsum₂']
    have hζ : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤
        L / (20 * c * T ^ 2) + Kζ := by
      have hζ' := hζBound (20 * c * T ^ 2 / L) hδpos hδsmall
      have hσcast : (σ : ℂ) = 1 + ((20 * c * T ^ 2 / L : ℝ) : ℂ) := by
        dsimp [σ]
        push_cast
        ring
      rw [hσcast]
      have hrecip : 1 / (20 * c * T ^ 2 / L) = L / (20 * c * T ^ 2) := by
        field_simp [hLpos.ne', hc.ne', hTpos.ne']
      rw [hrecip] at hζ'
      exact hζ'
    have hχ₁ :
        (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * v) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * v)).re ≤
            -1 / (σ - β) + CLog * T ^ 2 / rstar := by
      have hfun : dirichletLValue q hq χ = DirichletCharacter.LFunction χ := by
        funext z
        simp [dirichletLValue]
      have hminus₁' := hminus₁
      dsimp [D₁] at hminus₁'
      rw [hfun] at hminus₁'
      have hz₁coord : (⟨σ, v⟩ : ℂ) = (σ : ℂ) + Complex.I * v := by
        apply Complex.ext_iff.mpr
        constructor <;> simp
      dsimp [z₁] at hminus₁'
      rw [hz₁coord] at hminus₁'
      simpa only [neg_div, Complex.neg_re] using hminus₁'
    have hχ₂ :
        (-deriv (DirichletCharacter.LFunction (χ ^ 2))
          ((σ : ℂ) + Complex.I * (2 * v)) /
            DirichletCharacter.LFunction (χ ^ 2)
              ((σ : ℂ) + Complex.I * (2 * v))).re ≤ CLog * T ^ 2 / rstar := by
      have hfun : dirichletLValue q hq (χ ^ 2) = DirichletCharacter.LFunction (χ ^ 2) := by
        funext z
        simp [dirichletLValue]
      have hminus₂' := hminus₂
      dsimp [D₂] at hminus₂'
      rw [hfun] at hminus₂'
      have hz₂coord : (⟨σ, 2 * v⟩ : ℂ) = (σ : ℂ) + Complex.I * (2 * v) := by
        apply Complex.ext_iff.mpr
        constructor <;> simp
      dsimp [z₂] at hminus₂'
      rw [hz₂coord] at hminus₂'
      simpa only [neg_div, Complex.neg_re] using hminus₂'
    have hgap : σ - β ≤ 21 * c * T ^ 2 / L := by
      calc
        σ - β ≤ σ - (1 - width) := sub_le_sub_left hβlower σ
        _ = 21 * c * T ^ 2 / L := by dsimp [σ, width]; ring
    have hrecip : L / (21 * c * T ^ 2) ≤ 1 / (σ - β) := by
      have hgapPos : 0 < σ - β := sub_pos.mpr (lt_of_le_of_lt hβupper hσgt)
      calc
        L / (21 * c * T ^ 2) = 1 / (21 * c * T ^ 2 / L) := by
          field_simp [hLpos.ne', hc.ne', hTpos.ne']
        _ ≤ 1 / (σ - β) := one_div_le_one_div_of_le hgapPos hgap
    have herrorEq : CLog * T ^ 2 / rstar = CLog * (L / T ^ 2) := by
      dsimp [rstar]
      field_simp [hLpos.ne', hTpos.ne']
    have hlead₁ : L / (20 * c * T ^ 2) = (1 / (20 * c)) * (L / T ^ 2) := by
      field_simp [hc.ne', hTpos.ne']
    have hlead₂ : L / (21 * c * T ^ 2) = (1 / (21 * c)) * (L / T ^ 2) := by
      field_simp [hc.ne', hTpos.ne']
    have hratioPos : 0 < L / T ^ 2 := div_pos hLpos hT2pos
    have h341 := three_four_one_logderiv_nonneg (σ := σ) (v := v) χ hσgt
    have hζfinal : (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re ≤
        L / (20 * c * T ^ 2) + L / T ^ 2 := by linarith [hζ, hKratio]
    have hχ₁final :
        (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * v) /
          DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * v)).re ≤
            -L / (21 * c * T ^ 2) + CLog * T ^ 2 / rstar := by
      have hrecipNeg : -1 / (σ - β) ≤ -L / (21 * c * T ^ 2) := by
        simpa only [neg_div] using neg_le_neg hrecip
      calc
        _ ≤ -1 / (σ - β) + CLog * T ^ 2 / rstar := hχ₁
        _ ≤ -L / (21 * c * T ^ 2) + CLog * T ^ 2 / rstar :=
          add_le_add_left hrecipNeg _
    have hlead₂neg : -L / (21 * c * T ^ 2) = -((1 / (21 * c)) * (L / T ^ 2)) := by
      rw [neg_div]
      exact congrArg Neg.neg hlead₂
    have hupper :
        3 * (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re +
          4 * (-deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + Complex.I * v) /
              DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * v)).re +
          (-deriv (DirichletCharacter.LFunction (χ ^ 2))
            ((σ : ℂ) + Complex.I * (2 * v)) /
              DirichletCharacter.LFunction (χ ^ 2)
                ((σ : ℂ) + Complex.I * (2 * v))).re ≤
          (3 / (20 * c) - 4 / (21 * c) + 3 + 5 * CLog) * (L / T ^ 2) := by
      calc
        _ ≤ 3 * (L / (20 * c * T ^ 2) + L / T ^ 2) +
              4 * (-L / (21 * c * T ^ 2) + CLog * T ^ 2 / rstar) +
              CLog * T ^ 2 / rstar := by
          have hA := mul_le_mul_of_nonneg_left hζfinal (by norm_num : 0 ≤ (3 : ℝ))
          have hB := mul_le_mul_of_nonneg_left hχ₁final (by norm_num : 0 ≤ (4 : ℝ))
          have hC := hχ₂
          linarith [hA, hB, hC]
        _ = (3 / (20 * c) - 4 / (21 * c) + 3 + 5 * CLog) * (L / T ^ 2) := by
          rw [herrorEq, hlead₁, hlead₂neg]
          ring
    have hupperneg :
        (3 / (20 * c) - 4 / (21 * c) + 3 + 5 * CLog) * (L / T ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hcoeff hratioPos
    have h341' := h341
    simp only [neg_div] at h341'
    have hupper' := hupper
    simp only [neg_div] at hupper'
    linarith [h341', hupper', hupperneg]
  refine ⟨hNoZero, ?_⟩
  intro s hsReLow hsReHigh hsImLow hsImHigh
  let v : ℝ := s.im
  have hvlow : 1 ≤ |v| := by
    dsimp [v]
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) hsImLow
  have hvActualLow : 2 ≤ |v| := by simpa [v] using hsImLow
  have hvhigh : |v| ≤ (5 / 2 : ℝ) * Real.rpow x 3 := by
    dsimp [v]
    calc
      |s.im| ≤ Real.rpow x 3 / 2 := hsImHigh
      _ ≤ (5 / 2 : ℝ) * Real.rpow x 3 := by
        nlinarith [Real.rpow_nonneg (le_of_lt hxpos) (3 : ℝ)]
  obtain ⟨R, hRlow, hRhigh, Z, hZlen, hZmem, hZcomplete, hRboundary,
    hformula⟩ := hLocalApply χ v hvlow hvhigh
  let s₀ : ℂ := ⟨1 + rstar, v⟩
  have hs₀dist : ‖s - s₀‖ ≤ 2 * rstar := by
    rw [complex_norm_sub_eq_abs_of_im_eq s s₀ (by simp [s₀, v])]
    have hsReHigh' : s.re ≤ 1 + 1 / L := by simpa [L] using hsReHigh
    have hinvL : 1 / L ≤ rstar := by
      dsimp [rstar]
      apply (div_le_div_iff₀ hLpos hLpos).2
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hT4ge1 hLpos.le
    have hsReCenter : s.re ≤ 1 + rstar := by linarith
    rw [abs_of_nonpos (by linarith : s.re - (1 + rstar) ≤ 0)]
    have hsReLow' : 1 - width / 2 ≤ s.re := by simpa [L, T, width] using hsReLow
    have hhalfwidth : width / 2 ≤ rstar / 2 := by linarith [hwidthle]
    linarith
  have hwidthpos : 0 < width := by dsimp [width]; positivity
  have hsReLow' : 1 - width / 2 ≤ s.re := by simpa [L, T, width] using hsReLow
  have hsReNoZero : 1 - width ≤ s.re := by
    have hhalf : 1 - width ≤ 1 - width / 2 := by linarith [hwidthpos]
    exact hhalf.trans hsReLow'
  have hsnonzero : dirichletLValue q hq χ s ≠ 0 :=
    hNoZero s hsReNoZero (le_trans (by norm_num : (1 : ℝ) ≤ 2) hsImLow) (by
      calc
        |s.im| ≤ Real.rpow x 3 / 2 := hsImHigh
        _ ≤ Real.rpow x 3 := by
          nlinarith [Real.rpow_nonneg (le_of_lt hxpos) (3 : ℝ)])
  let D : ℂ := deriv (dirichletLValue q hq χ) s / dirichletLValue q hq χ s
  let S : ℂ := (Z.map fun ρ ↦ (1 : ℂ) / (s - ρ)).sum
  have hform : ‖D - S‖ ≤ CLog * T ^ 2 / rstar := by
    simpa [D, S] using hformula s hs₀dist hsnonzero
  have hZre : ∀ ρ ∈ Z, ρ.re < 1 - width := by
    intro ρ hρmem
    rcases hZmem ρ hρmem with ⟨hρzero, hρdist⟩
    have hρzeroL : DirichletCharacter.LFunction χ ρ = 0 := by
      simpa [dirichletLValue] using hρzero
    have himdiff : |ρ.im - v| ≤ ‖ρ - s₀‖ := by
      simpa [s₀, v, Complex.sub_im] using Complex.abs_im_le_norm (ρ - s₀)
    have hρimagLow : 1 ≤ |ρ.im| := by
      have htri : |v| ≤ |ρ.im| + |v - ρ.im| := by
        calc
          |v| = |(v - ρ.im) + ρ.im| := by congr 1; ring
          _ ≤ |v - ρ.im| + |ρ.im| := abs_add_le _ _
          _ = |ρ.im| + |v - ρ.im| := by ring
      have hdiffSmall : |v - ρ.im| < 1 := by
        have hsmall : ‖ρ - s₀‖ < 1 := by
          calc
            ‖ρ - s₀‖ < R := hρdist
            _ ≤ 5 * rstar := by nlinarith [hRhigh]
            _ < 1 := by nlinarith [hrSmallX']
        have hdiffEq : |v - ρ.im| = |ρ.im - v| := by rw [abs_sub_comm]
        rw [hdiffEq]
        exact lt_of_le_of_lt himdiff hsmall
      nlinarith [hvActualLow, htri]
    have hρimagHigh : |ρ.im| ≤ Real.rpow x 3 := by
      have htri : |ρ.im| ≤ |v| + |ρ.im - v| := by
        calc
          |ρ.im| = |(ρ.im - v) + v| := by congr 1; ring
          _ ≤ |ρ.im - v| + |v| := abs_add_le _ _
          _ = |v| + |ρ.im - v| := by ring
      have hdiffSmall : |ρ.im - v| < 1 := by
        have hsmall : ‖ρ - s₀‖ < 1 := by
          calc
            ‖ρ - s₀‖ < R := hρdist
            _ ≤ 5 * rstar := by nlinarith [hRhigh]
            _ < 1 := by nlinarith [hrSmallX']
        exact lt_of_le_of_lt himdiff hsmall
      have hxCubedge8 : 8 ≤ Real.rpow x 3 := by
        calc
          (8 : ℝ) = Real.rpow 2 3 := by norm_num [Real.rpow_natCast]
          _ ≤ Real.rpow x 3 := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
      have hvActualHigh : |v| ≤ Real.rpow x 3 / 2 := by simpa [v] using hsImHigh
      nlinarith [hvActualHigh, htri, hdiffSmall, hxCubedge8]
    have hρlt : ρ.re < 1 - width := by
      by_contra hnot
      have hρge : 1 - width ≤ ρ.re := le_of_not_gt hnot
      have hnz := hNoZero ρ hρge hρimagLow hρimagHigh
      exact hnz hρzero
    exact hρlt
  have htermBound (ρ : ℂ) (hρ : ρ ∈ Z) :
      ‖(1 : ℂ) / (s - ρ)‖ ≤ 2 / width := by
    have hsep : width / 2 < (s - ρ).re := by
      have hρre := hZre ρ hρ
      have hsReLow' : 1 - width / 2 ≤ s.re := by simpa [L, T, width] using hsReLow
      dsimp [Complex.sub_re]
      linarith
    have hnormlower : width / 2 ≤ ‖s - ρ‖ := by
      calc
        width / 2 ≤ (s - ρ).re := le_of_lt hsep
        _ ≤ |(s - ρ).re| := le_abs_self _
        _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
    calc
      ‖(1 : ℂ) / (s - ρ)‖ = 1 / ‖s - ρ‖ := by simp [norm_div]
      _ ≤ 1 / (width / 2) :=
        one_div_le_one_div_of_le (by positivity : 0 < width / 2) hnormlower
      _ = 2 / width := by field_simp [hwidthpos.ne']
  have hsumNorm : ‖S‖ ≤ 2 * CLog / c * L := by
    calc
      ‖S‖ ≤ (Z.length : ℝ) * (2 / width) := by
        simpa [S] using list_norm_sum_map_le Z (fun ρ ↦ (1 : ℂ) / (s - ρ))
          (2 / width) htermBound
      _ ≤ CLog * T ^ 2 * (2 / width) :=
        mul_le_mul_of_nonneg_right hZlen (by positivity)
      _ = 2 * CLog / c * L := by
        dsimp [width]
        field_simp [hc.ne', hLpos.ne', hTpos.ne']
  have hErrLe : CLog * T ^ 2 / rstar ≤ CLog * L := by
    have hT2ge1 : 1 ≤ T ^ 2 := hT2ge1
    have hEq : CLog * T ^ 2 / rstar = CLog * (L / T ^ 2) := by
      dsimp [rstar]
      field_simp [hLpos.ne', hTpos.ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left (div_le_self hLpos.le hT2ge1) (le_of_lt hCLog)
  have hDnorm : ‖D‖ ≤ (CLog + 2 * CLog / c) * L := by
    calc
      ‖D‖ = ‖(D - S) + S‖ := by congr 1; ring
      _ ≤ ‖D - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ CLog * T ^ 2 / rstar + 2 * CLog / c * L := add_le_add hform hsumNorm
      _ ≤ CLog * L + 2 * CLog / c * L := by linarith [hErrLe]
      _ = (CLog + 2 * CLog / c) * L := by ring
  have hDnormOut : ‖D‖ ≤ COut * L := by
    dsimp [COut]
    nlinarith [hDnorm, hLpos]
  simpa [D, dirichletLValue, COut, L] using hDnormOut

set_option maxHeartbeats 200000
/-- `t2:pp.prime-polynomial` — PP `02-long-prime.tex:8-21, 483-579`, Lemma 3.1; also PD
Lemma 2.3. Correction 5 from review lane `rev-b` requires the prime set to be an interval. -/
theorem prime_polynomial :
    ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          ∀ N : ℝ, Real.rpow x τ / 2 ≤ N → N ≤ Real.rpow x η →
            ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
              ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
                Real.rpow L B₀ ≤ |t| → |t| ≤ Real.rpow x 2 →
                  ∀ I : Set ℕ, IsNatInterval I →
                    I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
                    ‖primeDirichletPolynomial N q χ t I‖ ≤
                      C₀ * Real.rpow L (-A) := by
  sorry

end ArtinPrimitiveRoots.TypeII.PP
