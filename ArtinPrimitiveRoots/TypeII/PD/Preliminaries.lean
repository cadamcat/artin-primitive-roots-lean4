import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.ModeratePhase
import ArtinPrimitiveRoots.TypeII.Proofs.pd0.RoughCounts

/-! Elementary mean-value, rough-count, and moderate-phase estimates from PD
`02-preliminaries.tex:73-235`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

/-- A finite Dirichlet polynomial in logarithmic coordinates, with its zero index excluded as
required by correction 1 from review lane `rev-b`. -/
noncomputable def dirichletPolynomial (Y : ℕ) (coeff : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n),
    coeff n * Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- Integers in a real interval that are rough above `W`. -/
noncomputable def roughIntegersInInterval (lo hi W : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun n => lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W

/-- Rough integers in an interval occupying one specified residue class. -/
noncomputable def roughResidueCount (lo hi W : ℝ) (d : ℕ) (b : ZMod d) : ℝ :=
  (((Finset.range (⌊hi⌋₊ + 1)).filter fun (n : ℕ) =>
    lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi ∧ roughAbove n W ∧ (n : ZMod d) = b).card : ℝ)

/-- `t2:pd.moment-bounds` — PD `02-preliminaries.tex:73-114`, Lemma 2.2. Correction 1 from
review lane `rev-b` excludes the zero index and requires positive polynomial length. -/
theorem moment_bounds :
    (∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧ ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧
      ∀ Y : ℝ, Y₀ ≤ Y →
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k) ≤
            Ck * Y * Real.rpow (Real.log (2 * Y)) Ck ∧
        (∑ n ∈ Finset.range (⌊Y⌋₊ + 1), (tau n : ℝ) ^ k / (n + 1 : ℝ)) ≤
            Ck * Real.rpow (Real.log (2 * Y)) Ck) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ Y : ℕ, 1 ≤ Y → ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∫ t in a..b, ‖dirichletPolynomial Y coeff t‖ ^ 2 ≤
          C₀ * (b - a + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
            ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n), ‖coeff n‖ ^ 2) ∧
    (∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ Y : ℕ, 1 ≤ Y → ∀ coeff : ℕ → ℂ, ∀ a b : ℝ, a ≤ b →
        ∀ T : Finset ℝ,
          (∀ t ∈ T, a ≤ t ∧ t ≤ b) →
          (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → 1 ≤ |t₁ - t₂|) →
            (∑ t ∈ T, ‖dirichletPolynomial Y coeff t‖ ^ 2) ≤
              C₁ * (b - a + 1 + (Y : ℝ) * Real.log (2 * (Y : ℝ))) *
                Real.rpow (Real.log (2 * (Y : ℝ))) 2 *
                ∑ n ∈ (Finset.range (Y + 1)).filter (fun n => 1 ≤ n), ‖coeff n‖ ^ 2) := by
  sorry

private lemma nat_range_floor_le_real (r : ℝ) (hr : 0 ≤ r) {n : ℕ}
    (hn : n ∈ Finset.range (⌊r⌋₊ + 1)) : (n : ℝ) ≤ r := by
  have hnrange : n < ⌊r⌋₊ + 1 := Finset.mem_range.mp hn
  by_cases hn0 : n = 0
  · simp [hn0, hr]
  · have hnfloor : n ≤ ⌊r⌋₊ := by omega
    exact (Nat.le_floor_iff' hn0).mp hnfloor

private lemma rough_interval_residue_filter_eq (l r W : ℝ) (m : ℕ) (b : ZMod m)
    (hr : 0 ≤ r) :
    (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W ∧ (n : ZMod m) = b) =
    (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ roughAbove n W ∧ (n : ZMod m) = b) := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hl, _, hrough, hb⟩
    exact ⟨hn, hl, hrough, hb⟩
  · rintro ⟨hn, hl, hrough, hb⟩
    exact ⟨hn, hl, nat_range_floor_le_real r hr hn, hrough, hb⟩

/-- `t2:pd.rough-counts` — PD `02-preliminaries.tex:175-235`, Lemma 2.5. -/
set_option maxHeartbeats 1000000 in
theorem rough_counts :
    ∀ δ C aExp A : ℝ, 0 < δ → 0 < C → 0 < aExp → aExp < 1 → 0 < A →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          let L := Real.log x
          let W := roughCutoff x
          ∀ H : ℝ, Real.rpow x δ ≤ H → H ≤ Real.rpow x C →
            ∀ l r : ℝ, H ≤ l → l ≤ r → r ≤ 2 * H →
              (|((roughIntegersInInterval l r W).card : ℝ) -
                roughSieveProduct W * (r - l + 1)| ≤ H * Real.rpow L (-A)) ∧
              (∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.exp (Real.rpow L aExp) →
                roughAbove d W →
                ∀ b : ZMod d,
                  |roughResidueCount l r W d b -
                    roughSieveProduct W * (r - l + 1) / (d : ℝ)| ≤
                    (H / d) * Real.rpow L (-A)) ∧
              ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
                ∀ χ : DirichletCharacter ℂ q,
                  ‖(∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
                        l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ roughAbove n W),
                      (χ (n : ZMod q) : ℂ)) -
                    (if χ = 1 then
                      (roughSieveProduct W * (r - l + 1) : ℝ) else 0 : ℂ)‖ ≤
                  H * Real.rpow L (-A) := by
  intro δ C aExp A hδ hC haExp haExp1 hA
  let aMod : ℝ := max aExp (1 / 2)
  have haModPos : 0 < aMod := by dsimp [aMod]; positivity
  have haModLt : aMod < 1 := by
    dsimp [aMod]
    exact max_lt_iff.mpr ⟨haExp1, by norm_num⟩
  let B : ℝ := A + C + 4
  have hBpos : 0 < B := by dsimp [B]; linarith
  have hB_A : A + 4 ≤ B := by dsimp [B]; linarith
  have hA_B : A ≤ B := by linarith [hB_A]
  obtain ⟨L₀, hL₀, hPrecision⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.exists_sieve_precision
      δ aMod B hδ haModPos haModLt (le_of_lt hBpos)
  let Lcut : ℝ := max 2 L₀
  let x₀ : ℝ := max 2 (Real.exp Lcut)
  refine ⟨1, x₀, by norm_num, le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro H hHx hHX l r hl hlr hr
  let L : ℝ := Real.log x
  let W : ℝ := roughCutoff x
  let N : ℕ := ⌊r⌋₊ + 1
  let u : ℝ := N
  let P : Finset ℕ := primesUpTo W
  let S : ℝ := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth L
  let V : ℝ := roughSieveProduct W
  let natResidueSet : (m : ℕ) → ZMod m → Finset ℕ := fun m b =>
    (Finset.range N).filter fun n =>
      l ≤ (n : ℝ) ∧ roughAbove n W ∧ (n : ZMod m) = b
  have hx0 : x₀ ≤ x := hx
  have hExpLe : Real.exp Lcut ≤ x :=
    (le_max_right 2 (Real.exp Lcut)).trans hx0
  have hLcutx : Lcut ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos Lcut) hExpLe
    simpa [L] using hh
  have hL₀x' : L₀ ≤ Real.log x := by
    exact (le_max_right 2 L₀).trans hLcutx
  have hPrecisionNow := hPrecision (Real.log x) hL₀x'
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx0
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hL2 : 2 ≤ L := (le_max_left 2 L₀).trans hLcutx
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hHone : 1 ≤ H := by
    have hxpow : 1 ≤ Real.rpow x δ := Real.one_le_rpow hx1 hδ.le
    exact hxpow.trans hHx
  have hHpos : 0 < H := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hLpow24 : 1 ≤ Real.rpow L (24 / 100 : ℝ) :=
    Real.one_le_rpow hL1 (by norm_num)
  have hW2 : 2 ≤ W := by
    change 2 ≤ Real.exp (Real.rpow L (24 / 100 : ℝ))
    calc
      (2 : ℝ) = Real.exp (Real.log 2) :=
        (Real.exp_log (show (0 : ℝ) < 2 by norm_num)).symm
      _ ≤ Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hh := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
        norm_num at hh ⊢
        exact hh
      _ ≤ Real.exp (Real.rpow L (24 / 100 : ℝ)) :=
        Real.exp_le_exp.mpr hLpow24
    have hSdepth : 480024 ≤ S := by
    dsimp [S, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hLpos.le _)
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    have hp' : p ∈ (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime := by
      simpa [P, primesUpTo] using hp
    exact (Finset.mem_filter.mp hp').2
  have hPsize : ∀ p ∈ P, (p : ℝ) ≤ W := by
    intro p hp
    have hp' : p ∈ (Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime := by
      simpa [P, primesUpTo] using hp
    obtain ⟨hpRange, hpPrime⟩ := Finset.mem_filter.mp hp'
    have hpfloor : p ≤ ⌊W⌋₊ := by
      have := Finset.mem_range.mp hpRange
      omega
    exact (Nat.le_floor_iff' hpPrime.ne_zero).mp hpfloor
  have hVfactor (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := by
    have hpPrime := hPprime p hp
    have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hpPrime.one_le
    have hpPos : 0 < (p : ℝ) := by linarith
    have hInv0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
    have hInv1 : (p : ℝ)⁻¹ ≤ 1 := by
      rw [← one_div]
      exact (div_le_one hpPos).2 hpR
    exact ⟨by linarith, by linarith⟩
  have hVfactor' (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
    simpa only [one_div] using hVfactor p hp
  have hV0 : 0 ≤ V := by
    dsimp [V, roughSieveProduct]
    exact Finset.prod_nonneg fun p hp => (hVfactor' p hp).1
  have hV1 : V ≤ 1 := by
    dsimp [V, roughSieveProduct]
    exact Finset.prod_le_one₀
      (fun p hp => (hVfactor' p hp).1)
      (fun p hp => (hVfactor' p hp).2)
  have hWpowEq : W ^ S =
      Real.exp (480024 * L ^ (24 / 100 : ℝ) + L ^ (94 / 100 : ℝ)) := by
    have hprod : L ^ (24 / 100 : ℝ) * L ^ (7 / 10 : ℝ) =
        L ^ (94 / 100 : ℝ) := by
      calc
        _ = L ^ ((24 / 100 : ℝ) + 7 / 10) :=
          (Real.rpow_add hLpos _ _).symm
        _ = L ^ (94 / 100 : ℝ) := by congr 1 <;> norm_num
    change (Real.exp (L ^ (24 / 100 : ℝ))) ^
      (480024 + L ^ (7 / 10 : ℝ)) = _
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [mul_add, hprod]
    congr 1
    ring
  have hPrecisionTail : 8 * W ^ S * Real.exp (L ^ aMod) * L ^ B ≤ H := by
    calc
      _ = 8 * (W ^ S * Real.exp (L ^ aMod)) * L ^ B := by ring
      _ = 8 * Real.exp (480024 * L ^ (24 / 100 : ℝ) +
          L ^ (94 / 100 : ℝ) + L ^ aMod) * L ^ B := by
        rw [hWpowEq]
        calc
          _ = 8 * (Real.exp (480024 * L ^ (24 / 100 : ℝ) +
              L ^ (94 / 100 : ℝ)) * Real.exp (L ^ aMod)) * L ^ B := by ring
          _ = _ := by rw [← Real.exp_add]
      _ ≤ Real.exp (δ * L) := hPrecisionNow.2.1
      _ ≤ H := by
        have hxrpow : Real.rpow x δ = Real.exp (δ * L) := by
          calc
            Real.rpow x δ = Real.exp (Real.log x * δ) :=
              Real.rpow_def_of_pos hxpos δ
            _ = Real.exp (δ * L) := by simp [L, mul_comm]
        rw [← hxrpow]
        exact hHx
  have hLengthLower : 0 ≤ u - l := by
    apply sub_nonneg.mpr
    dsimp [u, N]
    have hrFloor := (Nat.lt_floor_add_one r).le
    have hrFloor' : r ≤ ((⌊r⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hrFloor
    linarith
  have hrLtU : r < u := by
    dsimp [u, N]
    exact_mod_cast Nat.lt_floor_add_one r
  have huUpper : u ≤ r + 1 := by
    dsimp [u, N]
    have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
    push_cast
    linarith
  have hLenUpper : u - l ≤ 2 * H := by linarith
  have hlu : l ≤ u := sub_nonneg.mp hLengthLower
  have hPcopOne : ∀ p ∈ P, Nat.Coprime 1 p := by
    intro p hp
    exact Nat.coprime_one_left p
  have hRaw (m : ℕ) (b : ZMod m) (hm : 0 < m)
      (hcop : ∀ p ∈ P, Nat.Coprime m p) :
      |((natResidueSet m b).card : ℝ) - ((u - l) / (m : ℝ)) * V| ≤
        ((u - l) / (m : ℝ)) * V * Real.exp (-S / 96) + 4 * W ^ S := by
    have hImage := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.nat_rough_residue_image
      N m b W l hl0
    have hci : ((natResidueSet m b).image (fun n : ℕ => (n : ℤ))).card =
        (natResidueSet m b).card := by
      apply Finset.card_image_of_injective
      intro n₁ n₂ h
      exact Int.ofNat.inj h
    have hCard : ((natResidueSet m b).card : ℝ) =
        (((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
          1 m {b} l u).filter
          (fun z : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ z)).card : ℝ) := by
      have hNat : (natResidueSet m b).card =
          ((OAI.Erdos970.ErdosCoprimeResidueInterval.realCoprimeResidues
            1 m {b} l u).filter
            (fun z : ℤ => ∀ p ∈ P, ¬ (p : ℤ) ∣ z)).card := by
        calc
          _ = ((natResidueSet m b).image (fun n : ℕ => (n : ℤ))).card := hci.symm
          _ = _ := congrArg Finset.card hImage
      exact_mod_cast hNat
    have hsieve := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.rough_sieve_residue_class_bound
      m b P W S l u hm hl0 hlu hW2 hSdepth hPprime hPsize hcop
    rw [hCard]
    simpa [V, P, roughSieveProduct, primesUpTo] using hsieve
  have hFinalCount (m : ℕ) (b : ZMod m) (hm0 : 0 < m) (hm1 : 1 ≤ m)
      (hcop : ∀ p ∈ P, Nat.Coprime m p)
      (hmexp : (m : ℝ) ≤ Real.exp (L ^ aMod)) :
      |((natResidueSet m b).card : ℝ) - V * (r - l + 1) / (m : ℝ)| ≤
        (H / (m : ℝ)) * L ^ (-A) := by
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm0
    have hLnegPos : 0 < L ^ (-A) := Real.rpow_pos_of_pos hLpos _
    let E : ℝ := (H / (m : ℝ)) * L ^ (-A)
    have hEpos : 0 < E := by dsimp [E]; positivity
    have hModLog : (m : ℝ) * L ^ A ≤ Real.exp (L ^ aMod) * L ^ B := by
      calc
        _ ≤ Real.exp (L ^ aMod) * L ^ A :=
          mul_le_mul_of_nonneg_right hmexp (Real.rpow_nonneg hLpos.le A)
        _ ≤ Real.exp (L ^ aMod) * L ^ B :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL1 hA_B) (Real.exp_pos _).le
    have hTailStrength : 8 * W ^ S * (m : ℝ) * L ^ A ≤ H := by
      calc
        _ = 8 * W ^ S * ((m : ℝ) * L ^ A) := by ring
        _ ≤ 8 * W ^ S * (Real.exp (L ^ aMod) * L ^ B) :=
          mul_le_mul_of_nonneg_left hModLog (by positivity)
        _ ≤ H := by
          convert hPrecisionTail using 1 <;> ring
    have hWpow1 : 1 ≤ W ^ S := Real.one_le_rpow (by linarith) (by
      dsimp [S, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.sieveDepth]
      positivity)
    have hTailDen : 8 * (m : ℝ) * L ^ A ≤ H := by
      calc
        _ = 8 * (1 * ((m : ℝ) * L ^ A)) := by ring
        _ ≤ 8 * (W ^ S * ((m : ℝ) * L ^ A)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hWpow1 (mul_nonneg (by exact_mod_cast (Nat.cast_nonneg m))
              (Real.rpow_nonneg hLpos.le A))) (by norm_num)
        _ ≤ H := by
          convert hTailStrength using 1 <;> ring
    have hDenPos : 0 < (m : ℝ) * L ^ A := mul_pos hmpos (Real.rpow_pos_of_pos hLpos _)
    have hPowApos : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
    have hElarge : 8 ≤ E := by
      have hTailDen' : 8 * ((m : ℝ) * L ^ A) ≤ H := by
        convert hTailDen using 1 <;> ring
      have hdiv := (le_div_iff₀ hDenPos).2 hTailDen'
      have heq : H / ((m : ℝ) * L ^ A) = E := by
        dsimp [E]
        rw [Real.rpow_neg hLpos.le A]
        field_simp [ne_of_gt hmpos, ne_of_gt hPowApos]
        ring
      rw [heq] at hdiv
      exact hdiv
    have hTailSmall : 4 * W ^ S ≤ E / 2 := by
      have heq : H / ((m : ℝ) * L ^ A) = E := by
        dsimp [E]
        rw [Real.rpow_neg hLpos.le A]
        field_simp [ne_of_gt hmpos, ne_of_gt hPowApos]
        ring
      have hTailStrength' : (8 * W ^ S) * ((m : ℝ) * L ^ A) ≤ H := by
        convert hTailStrength using 1 <;> ring
      have hdiv8 := (le_div_iff₀ hDenPos).2 hTailStrength'
      rw [heq] at hdiv8
      nlinarith [hdiv8]
    have hPowA : L ^ (-B) ≤ (1 / 16 : ℝ) * L ^ (-A) := by
      have hExpLe : -B ≤ -(A + 4) := by dsimp [B]; linarith
      have hpowCmp : L ^ (-B) ≤ L ^ (-(A + 4)) :=
        Real.rpow_le_rpow_of_exponent_le hL1 hExpLe
      have hpowMul : L ^ (-(A + 4)) = L ^ (-A) * L ^ (-4) := by
        calc
          L ^ (-(A + 4)) = L ^ ((-A) + (-4)) := by congr 1 <;> ring
          _ = L ^ (-A) * L ^ (-4) := Real.rpow_add hLpos _ _
      have hfour : L ^ (-4 : ℝ) ≤ (1 / 16 : ℝ) := by
        calc
          L ^ (-4 : ℝ) ≤ (2 : ℝ) ^ (-4 : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) hL2 (by norm_num)
          _ = 1 / 16 := by norm_num
      calc
        _ ≤ L ^ (-A) * L ^ (-4) := hpowCmp.trans_eq hpowMul
        _ ≤ L ^ (-A) * (1 / 16) :=
          mul_le_mul_of_nonneg_left hfour (Real.rpow_nonneg hLpos.le _)
        _ = (1 / 16) * L ^ (-A) := by ring
    have hExpSmall : 2 * Real.exp (-S / 96) ≤ (1 / 16 : ℝ) * L ^ (-A) :=
      hPrecisionNow.1.trans hPowA
    have hLenBound : (u - l) / (m : ℝ) ≤ 2 * (H / (m : ℝ)) := by
      calc
        _ ≤ (2 * H) / (m : ℝ) :=
          div_le_div_of_nonneg_right hLenUpper hmpos.le
        _ = 2 * (H / (m : ℝ)) := by ring
    have hDensBound : ((u - l) / (m : ℝ)) * V ≤ 2 * (H / (m : ℝ)) := by
      calc
        _ ≤ ((u - l) / (m : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hV1 (div_nonneg hLengthLower hmpos.le)
        _ = (u - l) / (m : ℝ) := by ring
        _ ≤ 2 * (H / (m : ℝ)) := hLenBound
    have hExpPart :
        ((u - l) / (m : ℝ)) * V * Real.exp (-S / 96) ≤ E / 16 := by
      calc
        _ ≤ (2 * (H / (m : ℝ))) * Real.exp (-S / 96) :=
          mul_le_mul_of_nonneg_right hDensBound (Real.exp_pos _).le
        _ = (H / (m : ℝ)) * (2 * Real.exp (-S / 96)) := by ring
        _ ≤ (H / (m : ℝ)) * ((1 / 16 : ℝ) * L ^ (-A)) :=
          mul_le_mul_of_nonneg_left hExpSmall (by positivity)
        _ = E / 16 := by dsimp [E]; ring
    have hraw := hRaw m b hm hcop
    have hRawSmall : |((natResidueSet m b).card : ℝ) - ((u - l) / (m : ℝ)) * V| ≤
        E / 16 + E / 2 := by
      exact hraw.trans (add_le_add hExpPart hTailSmall)
    have hLenErr : |(u - l) - (r - l + 1)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hRatioErr :
        |(u - l) / (m : ℝ) - (r - l + 1) / (m : ℝ)| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hmpos]
      apply (div_le_one hmpos).2
      have hmCast : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
      exact hLenErr.trans_le hmCast
    have hMainErr :
        |((u - l) / (m : ℝ)) * V - V * (r - l + 1) / (m : ℝ)| ≤ 1 := by
      have heq : ((u - l) / (m : ℝ)) * V - V * (r - l + 1) / (m : ℝ) =
          V * ((u - l) / (m : ℝ) - (r - l + 1) / (m : ℝ)) := by ring
      rw [heq, abs_mul, abs_of_nonneg hV0]
      calc
        _ ≤ 1 * 1 := mul_le_mul hV1 hRatioErr (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    calc
      _ = |(((natResidueSet m b).card : ℝ) - ((u - l) / (m : ℝ)) * V) +
          (((u - l) / (m : ℝ)) * V - V * (r - l + 1) / (m : ℝ))| := by congr 1 <;> ring
      _ ≤ |((natResidueSet m b).card : ℝ) - ((u - l) / (m : ℝ)) * V| +
          |((u - l) / (m : ℝ)) * V - V * (r - l + 1) / (m : ℝ)| := abs_add _ _
      _ ≤ E / 16 + E / 2 + 1 := add_le_add hRawSmall hMainErr
      _ ≤ E := by nlinarith [hElarge]
  constructor
  · have hOne : |((natResidueSet 1 0).card : ℝ) -
        V * (r - l + 1) / (1 : ℝ)| ≤ (H / (1 : ℝ)) * L ^ (-A) :=
      hFinalCount 1 0 (by norm_num) (by norm_num) hPcopOne (by positivity)
    have hFirstSet : roughIntegersInInterval l r W = natResidueSet 1 0 := by
      unfold roughIntegersInInterval natResidueSet
      ext n
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hn, hl, hnr, hrough⟩
        exact ⟨hn, hl, hrough, Subsingleton.elim _ _⟩
      · rintro ⟨hn, hl, hrough, _⟩
        exact ⟨hn, hl, nat_range_floor_le_real r hr0 hn, hrough⟩
    rw [← hFirstSet] at hOne
    simpa [V, roughSieveProduct] using hOne
  constructor
  · intro d hd1 hdexp hroughD b
    have hcopD : ∀ p ∈ P, Nat.Coprime d p := by
      intro p hp
      have hpPrime := hPprime p hp
      have hpSize := hPsize p hp
      apply (hpPrime.coprime_iff_not_dvd.mpr ?_).symm
      intro hpd
      have hrough := hroughD p hpPrime hpd
      exact (not_lt_of_ge hpSize) hrough
    have hmodD : (d : ℝ) ≤ Real.exp (L ^ aMod) := by
      apply le_trans hdexp
      exact Real.exp_le_exp.mpr
        (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left aExp (1 / 2)))
    have hD := hFinalCount d b (by exact_mod_cast hd1) hd1 hcopD hmodD
    have hCountEq : roughResidueCount l r W d b = ((natResidueSet d b).card : ℝ) := by
      unfold roughResidueCount natResidueSet
      rw [rough_interval_residue_filter_eq l r W d b hr0]
    rw [hCountEq] at hD
    simpa [V, roughSieveProduct] using hD
  · intro q hq hqBound χ
    sorry

/-- The residue-restricted sum in the moderate-frequency estimate. -/
noncomputable def integerResiduePhaseSum (q : ℕ) (a : ZMod q)
    (t : ℝ) (l r : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (n : ℕ) =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a),
    Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- `t2:pd.moderate-phase` — PD `02-preliminaries.tex:160-173` and `05-major-arcs.tex:89-104`.
-/
theorem moderate_phase (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        let L := Real.log x
        let T := Real.exp (L / Real.log L ^ 2)
        ∀ N : ℝ, Real.rpow x δ ≤ N →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
            ∀ a : ZMod q, ∀ t : ℝ, 1 ≤ |t| → |t| ≤ T →
              ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
                ‖integerResiduePhaseSum q a t l r -
                  ((1 / (q : ℂ)) *
                    ∫ y in l..r, Complex.exp (Complex.I * t * Real.log y))‖ ≤
                  C₀ * (1 + |t|) ∧
                ‖∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤
                  C₀ * N / |t| ∧
              ((q : ℝ) / N) *
                    ‖integerResiduePhaseSum q a t l r‖ ≤
                  C₀ * (|t|⁻¹ + Real.rpow x (-cδ)) := by
  obtain ⟨xA, hxA, hAbsorb⟩ :=
    ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.exists_moderate_absorption δ C hδ hC
  refine ⟨4, δ / 2, max 2 xA, by norm_num, by positivity, le_max_left _ _, ?_⟩
  intro x hx
  dsimp
  intro N hN q hq hqBound a t ht hT l r hl hlr hr
  let L : ℝ := Real.log x
  let T : ℝ := Real.exp (L / Real.log L ^ 2)
  have hxA' : xA ≤ x := (le_max_right 2 xA).trans hx
  have hx2 : 2 ≤ x := (le_max_left 2 xA).trans hx
  have hxpos : 0 < x := by linarith
  have hAbsRaw := hAbsorb x hxA'
  have hAbs : Real.rpow L C * (1 + T) ≤ Real.rpow x (δ / 2) := by
    simpa [L, T] using hAbsRaw
  have hNpos : 0 < N := by
    have : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
    exact lt_of_lt_of_le this hN
  have hqpos : 0 < q := Nat.zero_lt_of_lt hq
  have hlogPos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith)
  have hfac : 1 ≤ 1 + T := by
    have hTpos : 0 < T := by dsimp [T]; positivity
    linarith
  have hlogpow : Real.rpow L C ≤ Real.rpow x (δ / 2) := by
    calc
      Real.rpow L C = Real.rpow L C * 1 := by ring
      _ ≤ Real.rpow L C * (1 + T) :=
        mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hlogPos.le C)
      _ ≤ Real.rpow x (δ / 2) := hAbs
  have hxone : 1 ≤ x := by linarith
  have hhalfLe : Real.rpow x (δ / 2) ≤ Real.rpow x δ :=
    Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
  have hqN : (q : ℝ) ≤ N := by
    calc
      (q : ℝ) ≤ Real.rpow L C := hqBound
      _ ≤ Real.rpow x (δ / 2) := hlogpow
      _ ≤ Real.rpow x δ := hhalfLe
      _ ≤ N := hN
  have hEst := ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.phase_residue_interval_bounds
    t N l r q a hNpos hl hlr hr hqpos hqN ht
  have hEst' :
      ‖integerResiduePhaseSum q a t l r -
        (1 / (q : ℂ)) * ∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤
        4 * (1 + |t|) ∧
      ‖∫ y in l..r, Complex.exp (Complex.I * t * Real.log y)‖ ≤ 4 * N / |t| ∧
      ((q : ℝ) / N) * ‖integerResiduePhaseSum q a t l r‖ ≤
        4 / |t| + 4 * ((q : ℝ) / N) * (1 + |t|) := by
    simpa [integerResiduePhaseSum, ArtinPrimitiveRoots.TypeII.PD.Proofs.pd0.phase] using hEst
  have hqT : (q : ℝ) * (1 + |t|) ≤ Real.rpow x (δ / 2) := by
    calc
      (q : ℝ) * (1 + |t|) ≤ Real.rpow L C * (1 + |t|) :=
        mul_le_mul_of_nonneg_right hqBound (by positivity)
      _ ≤ Real.rpow L C * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith [hT])
          (Real.rpow_nonneg hlogPos.le C)
      _ ≤ Real.rpow x (δ / 2) := hAbs
  have hhalfPos : 0 < Real.rpow x (δ / 2) := Real.rpow_pos_of_pos hxpos _
  have hhalfSq : (Real.rpow x (δ / 2)) ^ 2 = Real.rpow x δ := by
    calc
      (Real.rpow x (δ / 2)) ^ 2 = Real.rpow x ((δ / 2) * 2) :=
        (Real.rpow_mul_natCast hxpos.le (δ / 2) 2).symm
      _ = Real.rpow x δ := by congr 1 <;> ring
  have hprodN : ((q : ℝ) * (1 + |t|)) * Real.rpow x (δ / 2) ≤ N := by
    calc
      _ ≤ (Real.rpow x (δ / 2)) ^ 2 := by
        have hhalfNN : 0 ≤ Real.rpow x (δ / 2) := Real.rpow_nonneg hxpos.le (δ / 2)
        have hprod := mul_nonneg (sub_nonneg.mpr hqT) hhalfNN
        nlinarith [hprod]
      _ = Real.rpow x δ := hhalfSq
      _ ≤ N := hN
  have hratio : ((q : ℝ) * (1 + |t|)) / N ≤ (Real.rpow x (δ / 2))⁻¹ := by
    apply (div_le_iff₀ hNpos).2
    simpa [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hhalfPos).2 hprodN
  have hratio' : ((q : ℝ) / N) * (1 + |t|) ≤ Real.rpow x (-δ / 2) := by
    have heq : ((q : ℝ) / N) * (1 + |t|) = ((q : ℝ) * (1 + |t|)) / N := by ring
    calc
      ((q : ℝ) / N) * (1 + |t|) = ((q : ℝ) * (1 + |t|)) / N := heq
      _ ≤ (Real.rpow x (δ / 2))⁻¹ := hratio
      _ = Real.rpow x (-(δ / 2)) := (Real.rpow_neg hxpos.le (δ / 2)).symm
      _ = Real.rpow x (-δ / 2) := by congr 1 <;> ring
  constructor
  · exact hEst'.1
  constructor
  · simpa [mul_comm] using hEst'.2.1
  · calc
      _ ≤ 4 / |t| + 4 * Real.rpow x (-δ / 2) := by
        nlinarith [hEst'.2.2, hratio', abs_nonneg t]
      _ = 4 * (|t|⁻¹ + Real.rpow x (-(δ / 2))) := by ring_nf

end ArtinPrimitiveRoots.TypeII.PD
