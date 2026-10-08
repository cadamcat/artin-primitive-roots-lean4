import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_fixed_system_abs_estimate
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_rank_support_mass

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pd5_high_tail_large_log (K : ℕ) (aAtom : ℝ) (haAtom : 0 < aAtom) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      4 ≤ L ∧ 10 * (K : ℝ) ≤ L ∧ aAtom ≤ L ∧
        Real.log L / Real.rpow L (1 / 10 : ℝ) < 1 / 26 := by
  have hRatio : Filter.Tendsto
      (fun L : ℝ => Real.log L / Real.rpow L (1 / 10 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).tendsto_div_nhds_zero
  have hSmall : ∀ᶠ L : ℝ in atTop,
      Real.log L / Real.rpow L (1 / 10 : ℝ) < 1 / 26 :=
    (tendsto_order.1 hRatio).2 _ (by norm_num)
  let lower : ℝ := max 4 (max (10 * (K : ℝ)) aAtom)
  have hLower : ∀ᶠ L : ℝ in atTop, lower ≤ L :=
    Filter.eventually_ge_atTop lower
  have hAll := hSmall.and hLower
  rcases Filter.eventually_atTop.mp hAll with ⟨L₀, hL₀⟩
  refine ⟨L₀, ?_⟩
  intro L hL
  have h := hL₀ L hL
  have hlow := h.2
  have h4 : 4 ≤ lower := le_max_left _ _
  have h10₀ : 10 * (K : ℝ) ≤ max (10 * (K : ℝ)) aAtom := le_max_left _ _
  have hAtom₀ : aAtom ≤ max (10 * (K : ℝ)) aAtom := le_max_right _ _
  have h10 : 10 * (K : ℝ) ≤ lower :=
    le_trans h10₀ (le_max_right _ _)
  have hAtom : aAtom ≤ lower :=
    le_trans hAtom₀ (le_max_right _ _)
  exact ⟨h4.trans hlow, h10.trans hlow, hAtom.trans hlow, h.1⟩

/-- Finite rank grouping, geometric tail and the exact frozen exponent; the existing 3r mass
bound replaces the guide's proposed 2r decoration proof without changing the conclusion.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:456–493`; uses pd5_scale_facts,
pd5_rank_support_mass and the supplied fixed-system bound; feeds frozen history_rank_high. -/
theorem pd5_high_rank_tail (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁)
    (K : ℕ) (F : PDFix K) (hF : F.Valid) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (E₀ : ℝ) (hE₀ : 0 < E₀)
    (hfixed : ∃ Cabs aAtom x₀ : ℝ, 0 < Cabs ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
        ∀ C ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
            Real.rpow S.L (Cabs * ((S.N : ℝ) + 1)) *
              (aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))) ^ constraintRank C) :
    ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
      ∀ w : ArchRoot, w.InRegion S →
        (∑ C ∈ (constraintSystems (birthAddresses S.x K (memoryCutoff S))).filter
          (fun C => ⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊ ≤
            constraintRank C),
          |(constraintCoeff C : ℝ)| *
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖) ≤
          Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
  rcases hfixed with ⟨Cabs, aAtom, xFix, hCabs, hAtom, hxFix, hFixed⟩
  rcases pd5_scale_facts K F hF with ⟨xScale, hxScale, hScaleFacts⟩
  rcases pd5_high_tail_large_log K aAtom hAtom with ⟨L₀, hL₀⟩
  let C' : ℝ := 4 * Cabs + 2 * E₀ + 12
  let x₀ : ℝ := max xFix (max xScale (max 2 (Real.exp L₀)))
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    calc
      2 ≤ max 2 (Real.exp L₀) := le_max_left _ _
      _ ≤ max xScale (max 2 (Real.exp L₀)) := le_max_right _ _
      _ ≤ max xFix (max xScale (max 2 (Real.exp L₀))) := le_max_right _ _
  refine ⟨C', x₀, hC', hx₀, ?_⟩
  intro S hS hx₀S w hw
  have hxFixS : xFix ≤ S.x := (le_max_left _ _).trans hx₀S
  have hxScaleS : xScale ≤ S.x :=
    (le_trans (le_max_left _ _) (le_max_right xFix _)).trans hx₀S
  have hexpS : Real.exp L₀ ≤ S.x :=
    (le_trans (le_trans (le_max_right 2 (Real.exp L₀))
      (le_max_right xScale (max 2 (Real.exp L₀))))
      (le_max_right xFix (max xScale (max 2 (Real.exp L₀))))) |>.trans hx₀S
  have hlogS : L₀ ≤ S.L := by
    have h := Real.log_le_log (Real.exp_pos L₀) hexpS
    simpa [PDScale.L] using h
  rcases hL₀ S.L hlogS with ⟨hL4, hLK, hAtomL, hRatio⟩
  rcases hScaleFacts S hxScaleS with
    ⟨hLone, hN2, hNlower, hNupper, hMbound, hBbound, hMleN, hBandFacts⟩
  let A : Finset (BirthAddress K) := birthAddresses S.x K (memoryCutoff S)
  let Q : ℝ := (max 1 A.card : ℝ)
  let u : ℝ := Real.rpow S.L (1 / 10 : ℝ)
  have hLpos : 0 < S.L := by linarith
  have hLroot : 2 ≤ Real.rpow S.L (1 / 2 : ℝ) := by
    calc
      2 = Real.rpow 4 (1 / 2 : ℝ) := by norm_num
      _ ≤ Real.rpow S.L (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hL4 (by norm_num)
  have hrootLeL : Real.rpow S.L (1 / 2 : ℝ) ≤ S.L := by
    calc
      Real.rpow S.L (1 / 2 : ℝ) ≤ Real.rpow S.L 1 :=
        Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
      _ = S.L := Real.rpow_one _
  have hNreal : (S.N : ℝ) ≤ 2 * Real.rpow S.L (1 / 2 : ℝ) := by
    have hupper : (S.N : ℝ) < Real.rpow S.L (1 / 2 : ℝ) + 2 := by
      exact_mod_cast hNupper
    nlinarith [hLroot]
  have hNle2L : (S.N : ℝ) ≤ 2 * S.L := by
    exact hNreal.trans (mul_le_mul_of_nonneg_left hrootLeL (by norm_num))
  have hNplus : (S.N : ℝ) + 1 ≤ 3 * S.L := by
    have hNleL : (S.N : ℝ) ≤ 2 * S.L := hNreal.trans
      (mul_le_mul_of_nonneg_left hrootLeL (by norm_num))
    nlinarith [hL4]
  have hMreal : (S.M : ℝ) ≤ 2 * S.L := by
    have hsmall : Real.rpow S.L (1 / 100 : ℝ) ≤ S.L := by
      calc
        Real.rpow S.L (1 / 100 : ℝ) ≤ Real.rpow S.L 1 :=
          Real.rpow_le_rpow_of_exponent_le hLone
            (by norm_num : (1 / 100 : ℝ) ≤ 1)
        _ = S.L := Real.rpow_one _
    calc
      (S.M : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) := hMbound
      _ ≤ 2 * S.L := mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have hBreal : (memoryCutoff S : ℝ) ≤ 2 * S.L ^ 2 := hBbound
  have hCardNat := pd5_birthAddresses_card_le (x := S.x) K (memoryCutoff S)
  have hCardCast : (A.card : ℝ) ≤
      (K : ℝ) * (S.M : ℝ) + (K : ℝ) * (S.N : ℝ) +
        (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) := by
    dsimp [A]
    simpa [PDScale.M, PDScale.N] using (show
      ((birthAddresses S.x K (memoryCutoff S)).card : ℝ) ≤
        ((K * slotCount S.x + K * pathLength S.x +
          K * (pathLength S.x + 1) * memoryCutoff S : ℕ) : ℝ) by
            exact_mod_cast hCardNat)
  have hCard : (A.card : ℝ) ≤ 10 * (K : ℝ) * S.L ^ 3 := by
    calc
      (A.card : ℝ) ≤
          (K : ℝ) * (S.M : ℝ) + (K : ℝ) * (S.N : ℝ) +
            (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) := hCardCast
      _ ≤ (K : ℝ) * (2 * S.L) + (K : ℝ) * (2 * S.L) +
            (K : ℝ) * (3 * S.L) * (2 * S.L ^ 2) := by
          gcongr
      _ ≤ 10 * (K : ℝ) * S.L ^ 3 := by
          have hLpow : S.L ≤ S.L ^ 3 := by
            have hp := pow_le_pow_right₀ hLone (by norm_num : 1 ≤ 3)
            simpa using hp
          have hKnonneg : 0 ≤ (K : ℝ) := by positivity
          nlinarith [hLpow]
  have hQ : Q ≤ S.L ^ 4 := by
    dsimp [Q]
    apply max_le
    · have hLpow4 : 1 ≤ S.L ^ 4 := by
        calc
          1 = (1 : ℝ) ^ 4 := by norm_num
          _ ≤ S.L ^ 4 := pow_le_pow_left₀ (by norm_num) hLone _
      exact hLpow4
    · calc
        (A.card : ℝ) ≤ 10 * (K : ℝ) * S.L ^ 3 := hCard
        _ ≤ S.L ^ 4 := by
          have hmul := mul_le_mul_of_nonneg_right hLK (by positivity : 0 ≤ S.L ^ 3)
          nlinarith [hmul]
  have hRatioBound : 13 * Real.log S.L ≤ u / 2 := by
    have hu : 0 < u := by dsimp [u]; positivity
    have hmul := (div_lt_iff₀ hu).1 hRatio
    have hscaled := mul_lt_mul_of_pos_left hmul (by norm_num : 0 < (13 : ℝ))
    have hEq : 13 * (1 / 26 * u) = u / 2 := by ring
    rw [hEq] at hscaled
    exact hscaled.le
  have hLpow13 : S.L ^ 13 = Real.exp (13 * Real.log S.L) := by
    calc
      S.L ^ 13 = (Real.exp (Real.log S.L)) ^ 13 := by rw [Real.exp_log hLpos]
      _ = Real.exp (13 * Real.log S.L) := (Real.exp_nat_mul (Real.log S.L) 13).symm
  have hCoeffBeta : aAtom * Q ^ 3 ≤ Real.exp (u / 2) := by
    have hQpow : Q ^ 3 ≤ S.L ^ 12 := by
      calc
        Q ^ 3 ≤ (S.L ^ 4) ^ 3 := pow_le_pow_left₀ (by positivity) hQ _
        _ = S.L ^ 12 := by rw [← pow_mul]
    have hCoeff : aAtom * Q ^ 3 ≤ S.L ^ 13 := by
      calc
        _ ≤ S.L * S.L ^ 12 :=
          mul_le_mul hAtomL hQpow (pow_nonneg (by positivity) _) hLpos.le
        _ = S.L ^ 13 := by rw [pow_succ]; ring
    calc
      aAtom * Q ^ 3 ≤ S.L ^ 13 := hCoeff
      _ = Real.exp (13 * Real.log S.L) := hLpow13
      _ ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr hRatioBound
  have hBeta : aAtom * Q ^ 3 * Real.exp (-u) ≤ Real.exp (-u / 2) := by
    calc
      _ ≤ Real.exp (u / 2) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hCoeffBeta (Real.exp_nonneg _)
      _ = Real.exp (-u / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hu : 0 < u := by dsimp [u]; positivity
  have hBetaOne : aAtom * Q ^ 3 * Real.exp (-u) ≤ 1 := by
    calc
      _ ≤ Real.exp (-u / 2) := hBeta
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := by simp
  let r₀ : ℕ := ⌈C' * (S.N : ℝ) * Real.log S.L / u⌉₊
  let systems := constraintSystems A
  let highSystems := systems.filter (fun C => r₀ ≤ constraintRank C)
  let pref : ℝ := Real.rpow S.L (Cabs * ((S.N : ℝ) + 1))
  let atom : ℝ := aAtom * Real.exp (-u)
  let beta : ℝ := aAtom * Q ^ 3 * Real.exp (-u)
  let summand : Finset (Finset (BirthAddress K)) → ℝ := fun C =>
    |(constraintCoeff C : ℝ)| *
      ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖
  have hRankFacts := pd5_rank_support_mass A
  have hRankLe {C : Finset (Finset (BirthAddress K))} (hC : C ∈ systems) :
      constraintRank C ≤ A.card := (hRankFacts.1 C hC).2
  have hMass (r : ℕ) :
      (∑ C ∈ systems.filter (fun C => constraintRank C = r),
        |(constraintCoeff C : ℝ)|) ≤ Q ^ (3 * r) := by
    simpa [systems, Q, A] using hRankFacts.2 r
  have hNorm {C : Finset (Finset (BirthAddress K))} (hC : C ∈ systems) :
      ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
        pref * atom ^ constraintRank C := by
    exact hFixed S hS hxFixS w hw C (by simpa [systems, A] using hC)
  have hR₀ceil : C' * (S.N : ℝ) * Real.log S.L / u ≤ (r₀ : ℝ) := by
    dsimp [r₀]
    exact Nat.le_ceil _
  have hR₀exp : Real.exp (-u / 2 * (r₀ : ℝ)) ≤
      Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by
    have hmul := (div_le_iff₀ hu).1 hR₀ceil
    have hmul' : C' * (S.N : ℝ) * Real.log S.L ≤ u * (r₀ : ℝ) := by
      simpa [mul_comm] using hmul
    have hscaled :
        (C' / 2) * (S.N : ℝ) * Real.log S.L ≤
          (u / 2) * (r₀ : ℝ) := by
      calc
        _ = (C' * (S.N : ℝ) * Real.log S.L) / 2 := by ring
        _ ≤ (u * (r₀ : ℝ)) / 2 := div_le_div_of_nonneg_right hmul' (by norm_num)
        _ = (u / 2) * (r₀ : ℝ) := by ring
    have hExponent :
        -u / 2 * (r₀ : ℝ) ≤ -(C' / 2) * (S.N : ℝ) * Real.log S.L := by
      have hscaled' :
          (C' / 2) * (S.N : ℝ) * Real.log S.L ≤ (u / 2) * (r₀ : ℝ) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
      calc
        -u / 2 * (r₀ : ℝ) = -((u / 2) * (r₀ : ℝ)) := by ring
        _ ≤ -((C' / 2) * (S.N : ℝ) * Real.log S.L) := by
          rw [neg_le_neg_iff]
          exact hscaled'
        _ = -(C' / 2) * (S.N : ℝ) * Real.log S.L := by ring
    calc
      Real.exp (-u / 2 * (r₀ : ℝ)) ≤
          Real.exp (-(C' / 2) * (S.N : ℝ) * Real.log S.L) :=
        Real.exp_le_exp.mpr hExponent
      _ = Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by
        calc
          _ = Real.exp (Real.log S.L * (-(C' / 2) * (S.N : ℝ))) := by
            congr 1
            ring
          _ = Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) :=
            (Real.rpow_def_of_pos hLpos _).symm
  have hBetaR₀ :
      beta ^ r₀ ≤ Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by
    calc
      beta ^ r₀ ≤ (Real.exp (-u / 2)) ^ r₀ :=
        pow_le_pow_left₀ (by positivity) (by simpa [beta] using hBeta) _
      _ = Real.exp (-u / 2 * (r₀ : ℝ)) :=
        by simpa [mul_comm] using (Real.exp_nat_mul (-u / 2) r₀).symm
      _ ≤ Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := hR₀exp
  have hMaps : ∀ C ∈ highSystems, constraintRank C ∈ Finset.range (A.card + 1) := by
    intro C hC
    have hSys : C ∈ systems := (Finset.mem_filter.mp hC).1
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hRankLe hSys))
  have hGrouped :
      (∑ C ∈ highSystems, summand C) =
        ∑ r ∈ Finset.range (A.card + 1),
          ∑ C ∈ highSystems.filter (fun C => constraintRank C = r), summand C := by
    rw [← Finset.sum_fiberwise_of_maps_to hMaps (fun C => summand C)]
  have hGroupBound (r : ℕ) :
      (∑ C ∈ highSystems.filter (fun C => constraintRank C = r), summand C) ≤
        pref * beta ^ r₀ := by
    by_cases hr : r₀ ≤ r
    · have hGroup :
          highSystems.filter (fun C => constraintRank C = r) =
            systems.filter (fun C => constraintRank C = r) := by
          ext C
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hhigh, hrank⟩
            change C ∈ systems.filter (fun C => r₀ ≤ constraintRank C) at hhigh
            have hC := (Finset.mem_filter.mp hhigh).1
            exact ⟨hC, hrank⟩
          · rintro ⟨hC, hrank⟩
            refine ⟨Finset.mem_filter.mpr ⟨hC, ?_⟩, hrank⟩
            rw [hrank]
            exact hr
      rw [hGroup]
      let R := systems.filter (fun C => constraintRank C = r)
      have hBound :
          (∑ C ∈ R, summand C) ≤ pref * atom ^ r * (Q ^ (3 * r)) := by
        calc
          (∑ C ∈ R, summand C) ≤
              ∑ C ∈ R, |(constraintCoeff C : ℝ)| * (pref * atom ^ r) := by
                apply Finset.sum_le_sum
                intro C hCR
                have hCS : C ∈ systems := (Finset.mem_filter.mp hCR).1
                have hrank : constraintRank C = r := (Finset.mem_filter.mp hCR).2
                have hN := hNorm hCS
                have hNr : ‖memHistory F S ρ w (some (memoryCutoff S)) none
                    (constraintWeight C)‖ ≤ pref * atom ^ r := by
                  simpa [hrank] using hN
                exact mul_le_mul_of_nonneg_left hNr (abs_nonneg _)
          _ = pref * atom ^ r * ∑ C ∈ R, |(constraintCoeff C : ℝ)| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro C hC
                ring
          _ ≤ pref * atom ^ r * (Q ^ (3 * r)) := by
            have hpref : 0 ≤ pref := Real.rpow_nonneg hLpos.le _
            have hatom : 0 ≤ atom := by
              dsimp [atom]
              positivity
            exact mul_le_mul_of_nonneg_left (hMass r)
              (mul_nonneg hpref (pow_nonneg hatom _))
      have hpow : atom ^ r * Q ^ (3 * r) = beta ^ r := by
        have hQpow : Q ^ (3 * r) = (Q ^ 3) ^ r := pow_mul Q 3 r
        calc
          atom ^ r * Q ^ (3 * r) = atom ^ r * (Q ^ 3) ^ r := by rw [hQpow]
          _ = (atom * Q ^ 3) ^ r := (mul_pow _ _ _).symm
          _ = beta ^ r := by simp [atom, beta, mul_assoc, mul_comm, mul_left_comm]
      have hBetaNonneg : 0 ≤ beta := by dsimp [beta]; positivity
      have hbetaR : beta ^ r ≤ beta ^ r₀ :=
        pow_le_pow_of_le_one hBetaNonneg hBetaOne (by exact_mod_cast hr)
      calc
        _ ≤ pref * atom ^ r * Q ^ (3 * r) := hBound
        _ = pref * (atom ^ r * Q ^ (3 * r)) := by ring
        _ = pref * beta ^ r := by
          exact congrArg (fun x : ℝ => pref * x) hpow
        _ ≤ pref * beta ^ r₀ :=
          mul_le_mul_of_nonneg_left hbetaR (Real.rpow_nonneg hLpos.le _)
    · have hsumzero :
          (∑ C ∈ highSystems.filter (fun C => constraintRank C = r), summand C) = 0 := by
        apply Finset.sum_eq_zero
        intro C hC
        rcases Finset.mem_filter.mp hC with ⟨hHighSys, hrank⟩
        change C ∈ systems.filter (fun C => r₀ ≤ constraintRank C) at hHighSys
        have hhigh := (Finset.mem_filter.mp hHighSys).2
        exact (hr (by simpa [hrank] using hhigh)).elim
      rw [hsumzero]
      have hpref : 0 ≤ pref := Real.rpow_nonneg hLpos.le _
      have hbeta' : 0 ≤ beta := by dsimp [beta]; positivity
      exact mul_nonneg hpref (pow_nonneg hbeta' _)
  have hTailGrouped :
      (∑ C ∈ highSystems, summand C) ≤
        (A.card + 1 : ℝ) * (pref * beta ^ r₀) := by
    rw [hGrouped]
    calc
      _ ≤ ∑ r ∈ Finset.range (A.card + 1), pref * beta ^ r₀ := by
        apply Finset.sum_le_sum
        intro r hr
        exact hGroupBound r
      _ = _ := by simp
  have hCount : (A.card + 1 : ℝ) ≤ 2 * S.L ^ 4 := by
    have hAcard : (A.card : ℝ) ≤ S.L ^ 4 := by
      calc
        (A.card : ℝ) ≤ 10 * (K : ℝ) * S.L ^ 3 := hCard
        _ ≤ S.L * S.L ^ 3 :=
          mul_le_mul_of_nonneg_right hLK (by positivity)
        _ = S.L ^ 4 := by rw [pow_succ]; ring
    have hOne : 1 ≤ S.L ^ 4 := by
      calc
        1 = (1 : ℝ) ^ 4 := by norm_num
        _ ≤ S.L ^ 4 := pow_le_pow_left₀ (by norm_num) hLone _
    push_cast
    linarith
  have hCountL : 2 * S.L ^ 4 ≤ S.L ^ 5 := by
    calc
      2 * S.L ^ 4 ≤ S.L * S.L ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith : 2 ≤ S.L) (by positivity)
      _ = S.L ^ 5 := by rw [pow_succ]; ring
  have hTailFactor :
      (A.card + 1 : ℝ) * (pref * beta ^ r₀) ≤
        S.L ^ 5 * pref * Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by
    have hpref0 : 0 ≤ pref := Real.rpow_nonneg hLpos.le _
    have hbeta0 : 0 ≤ beta ^ r₀ := pow_nonneg (by positivity) _
    have hfactor0 : 0 ≤ pref * beta ^ r₀ := mul_nonneg hpref0 hbeta0
    calc
      _ ≤ (2 * S.L ^ 4) * (pref * beta ^ r₀) :=
        mul_le_mul_of_nonneg_right hCount hfactor0
      _ ≤ S.L ^ 5 * (pref * beta ^ r₀) :=
        mul_le_mul_of_nonneg_right hCountL hfactor0
      _ ≤ S.L ^ 5 * (pref * Real.rpow S.L (-(C' / 2) * (S.N : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBetaR₀ (Real.rpow_nonneg hLpos.le _))
          (pow_nonneg hLpos.le _)
      _ = _ := by ring
  have hExponent :
      5 + Cabs * ((S.N : ℝ) + 1) - (C' / 2) * (S.N : ℝ) ≤
        -(E₀ + 3) * (S.N : ℝ) := by
    have hN : 2 ≤ (S.N : ℝ) := by exact_mod_cast hN2
    have hmul : 2 * (Cabs + 3) ≤ (Cabs + 3) * (S.N : ℝ) := by
      calc
        2 * (Cabs + 3) ≤ (S.N : ℝ) * (Cabs + 3) :=
          mul_le_mul_of_nonneg_right hN (show 0 ≤ Cabs + 3 by positivity)
        _ = (Cabs + 3) * (S.N : ℝ) := by ring
    have hsmall : 5 + Cabs ≤ 2 * (Cabs + 3) := by linarith [hCabs]
    have hdiff : 5 + Cabs - (Cabs + 3) * (S.N : ℝ) ≤ 0 := by
      linarith [hsmall, hmul]
    have hEq :
        (5 + Cabs * ((S.N : ℝ) + 1) - (C' / 2) * (S.N : ℝ)) -
            (-(E₀ + 3) * (S.N : ℝ)) =
          5 + Cabs - (Cabs + 3) * (S.N : ℝ) := by
      dsimp [C']
      ring
    linarith [hEq, hdiff]
  calc
    (∑ C ∈ highSystems, summand C) ≤
        S.L ^ 5 * pref * Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) :=
      hTailGrouped.trans hTailFactor
    _ = Real.rpow S.L
        (5 + Cabs * ((S.N : ℝ) + 1) - (C' / 2) * (S.N : ℝ)) := by
          have hpow5 : S.L ^ 5 = Real.rpow S.L (5 : ℝ) :=
            (Real.rpow_natCast S.L 5).symm
          calc
            _ = (Real.rpow S.L 5 * pref) *
                Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by rw [hpow5]
            _ = (Real.rpow S.L 5 *
                  Real.rpow S.L (Cabs * ((S.N : ℝ) + 1))) *
                Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) := by
                  dsimp [pref]
            _ = Real.rpow S.L (5 + Cabs * ((S.N : ℝ) + 1)) *
                  Real.rpow S.L (-(C' / 2) * (S.N : ℝ)) :=
                congrArg (fun x : ℝ => x * Real.rpow S.L (-(C' / 2) * (S.N : ℝ)))
                  (Real.rpow_add hLpos 5 _).symm
            _ = Real.rpow S.L
                  (5 + Cabs * ((S.N : ℝ) + 1) + (-(C' / 2) * (S.N : ℝ))) :=
                (Real.rpow_add hLpos _ _).symm
            _ = Real.rpow S.L
                  (5 + Cabs * ((S.N : ℝ) + 1) - (C' / 2) * (S.N : ℝ)) := by
                congr 1
                ring
    _ ≤ Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hLone hExponent

end
end ArtinPrimitiveRoots.TypeII.PD
