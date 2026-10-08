import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_truncation_choice_majorant
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_doubled_lifespan_bound

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 5000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Sum the fixed-path majorant using root_budget and absorb the exponential tail at
B=ceil(L squared). Constants are uniform in the archimedean root.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:504–523. Uses
pd_truncation_choice_majorant, pd_doubled_lifespan_bound and root_budget; feeds the frozen
truncation_adjoint. Choose C_A=1 after increasing the threshold. -/
theorem pd_truncation_tail_absorb (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
            C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  classical
  intro K F hF ρ hρ A hA
  obtain ⟨xChoice, hxChoice, hChoice⟩ :=
    pd_truncation_choice_majorant δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xDouble, hxDouble, hDouble⟩ :=
    pd_doubled_lifespan_bound δ c₁ c₂ hδ hc₁ K F hF
  obtain ⟨Cb, xRoot, hCb, hxRoot, hRoot⟩ := root_budget δ c₁ c₂ hδ hc₁ K F hF
  rcases hF with ⟨hBands, hqpos, hqdlt, hA0, hEta, hPsi⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtlt : Real.sqrt F.q_d < 1 := by
    have h := Real.sqrt_lt_sqrt (le_of_lt hqpos) hqdlt
    simpa using h
  have hden : 0 < 1 - Real.sqrt F.q_d := by linarith
  let qTail : ℝ := 8 * (K : ℝ) * Real.log 2 / (1 - Real.sqrt F.q_d)
  have hqTail : 0 ≤ qTail := by dsimp [qTail]; positivity
  let CLog : ℝ := Real.log 50 + 5
  have hCLog : 0 < CLog := by
    dsimp [CLog]
    have h50 : 0 < Real.log 50 := Real.log_pos (by norm_num)
    linarith
  let Ctotal : ℝ := 4 * (K : ℝ) * Real.log 2 +
    6 * (K : ℝ) * CLog + 4 * qTail + Cb + 20 * A
  have hCtotal : 0 < Ctotal := by
    dsimp [Ctotal]
    positivity
  let L₀ : ℝ := max 1 (max (4 * (K : ℝ) + 1) (Ctotal / Real.log 2))
  have hL₀ : 1 ≤ L₀ := by dsimp [L₀]; exact le_max_left _ _
  have hL₀K : 4 * (K : ℝ) + 1 ≤ L₀ := by
    dsimp [L₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hL₀Tot : Ctotal / Real.log 2 ≤ L₀ := by
    dsimp [L₀]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  let x₀ : ℝ := max xChoice (max xDouble (max xRoot (Real.exp L₀)))
  have hx₀ : 2 ≤ x₀ := by
    calc
      2 ≤ xRoot := hxRoot
      _ ≤ max xRoot (Real.exp L₀) := le_max_left _ _
      _ ≤ max xDouble (max xRoot (Real.exp L₀)) := le_max_right _ _
      _ ≤ x₀ := le_max_right _ _
  have hxChoice₀ : xChoice ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have hxDouble₀ : xDouble ≤ x₀ := by
    calc
      xDouble ≤ max xDouble (max xRoot (Real.exp L₀)) := le_max_left _ _
      _ ≤ x₀ := le_max_right _ _
  have hxRoot₀ : xRoot ≤ x₀ := by
    calc
      xRoot ≤ max xRoot (Real.exp L₀) := le_max_left _ _
      _ ≤ max xDouble (max xRoot (Real.exp L₀)) := le_max_right _ _
      _ ≤ x₀ := le_max_right _ _
  have hexp₀ : Real.exp L₀ ≤ x₀ := by
    calc
      Real.exp L₀ ≤ max xRoot (Real.exp L₀) := le_max_right _ _
      _ ≤ max xDouble (max xRoot (Real.exp L₀)) := le_max_right _ _
      _ ≤ x₀ := le_max_right _ _
  refine ⟨1, x₀, by norm_num, hx₀, ?_⟩
  intro S hS hx w hw
  have hxChoice' : xChoice ≤ S.x := hxChoice₀.trans hx
  have hxDouble' : xDouble ≤ S.x := hxDouble₀.trans hx
  have hxRoot' : xRoot ≤ S.x := hxRoot₀.trans hx
  have hexp' : Real.exp L₀ ≤ S.x := hexp₀.trans hx
  let L : ℝ := S.L
  let N : ℕ := pathLength S.x
  let M : ℕ := slotCount S.x
  let B : ℕ := memoryCutoff S
  let tailFactor : ℝ := (2 : ℝ) ^ (-(B : ℤ) + (K * pathLength S.x : ℤ))
  have hL₀x : L₀ ≤ Real.log S.x := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) hexp'
  have hL : 1 ≤ L := by dsimp [L]; exact le_trans hL₀ hL₀x
  have hLpos : 0 < L := by linarith
  have hSorig : S.Valid K δ c₁ c₂ := hS
  rcases hS with ⟨hxS, hHm, hHn, hlow, hupp, hY, hpad⟩
  have hrootHalf : 1 ≤ Real.rpow L (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have hrootSmall : 1 ≤ Real.rpow L (1 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 100)
    simpa using h
  have hceilN : (momentR S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) / 2 + 1 := by
    dsimp [momentR, L, PDScale.L]
    exact Nat.ceil_lt_add_one (by positivity)
  have hNsharpCore : 2 * (momentR S.x : ℝ) <
      Real.rpow L (1 / 2 : ℝ) + 2 := by
    calc
      _ < 2 * (Real.rpow L (1 / 2 : ℝ) / 2 + 1) :=
        mul_lt_mul_of_pos_left hceilN (by norm_num)
      _ = _ := by ring
  have hNsharp : (N : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := by
    simpa [N, pathLength] using hNsharpCore
  have hNplus : (N : ℝ) + 1 ≤ 4 * Real.rpow L (1 / 2 : ℝ) := by
    nlinarith [hNsharp, hrootHalf]
  have hN : (N : ℝ) ≤ 4 * Real.rpow L (1 / 2 : ℝ) := by linarith
  have hNplus2 : (N : ℝ) + 2 ≤ 5 * Real.rpow L (1 / 2 : ℝ) := by
    nlinarith [hNsharp, hrootHalf]
  have hfloorM : (momentJ S.x : ℝ) ≤ Real.rpow L (1 / 100 : ℝ) := by
    dsimp [momentJ, L, PDScale.L]
    exact Nat.floor_le (by positivity)
  have hM' : (momentJ S.x : ℝ) + 1 ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by
    calc
      _ ≤ Real.rpow L (1 / 100 : ℝ) + 1 := by linarith [hfloorM]
      _ ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by linarith [hrootSmall]
  have hM : (M : ℝ) ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by
    simpa [M, slotCount] using hM'
  have hMhalf : (M : ℝ) ≤ 2 * Real.rpow L (1 / 2 : ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (1 / 100 : ℝ) ≤ 1 / 2)
    have hp' : Real.rpow L (1 / 100 : ℝ) ≤ Real.rpow L (1 / 2 : ℝ) := hp
    nlinarith [hM, hp']
  have hMN : (K * (M + N) : ℝ) ≤ 6 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    have hsum : (M : ℝ) + (N : ℝ) ≤ 6 * Real.rpow L (1 / 2 : ℝ) := by
      nlinarith [hMhalf, hN]
    push_cast
    calc
      _ ≤ (K : ℝ) * (6 * Real.rpow L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg K)
      _ = 6 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) := by ring
  have hNPlus2Root : (N : ℝ) + 2 ≤ 5 * Real.rpow L (1 / 2 : ℝ) := hNplus2
  have hApathPos : 0 < 2 * ((N : ℝ) + 2) ^ 2 := by positivity
  let Apath : ℝ := 2 * ((N : ℝ) + 2) ^ 2
  have hrootSq : (Real.rpow L (1 / 2 : ℝ)) ^ 2 = L := by
    calc
      (Real.rpow L (1 / 2 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow L (1 / 2 : ℝ)) (2 : ℝ) :=
            (Real.rpow_natCast _ _).symm
      _ = Real.rpow L ((1 / 2 : ℝ) * 2) := (Real.rpow_mul hLpos.le _ _).symm
      _ = L := by norm_num [Real.rpow_one]
  have hApathBound : Apath ≤ 50 * L := by
    have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ (N : ℝ) + 2) hNPlus2Root
    have hsquare' : (N : ℝ) + 2 ^ 2 ≤ 25 * L := by
      nlinarith [hsquare, hrootSq]
    dsimp [Apath]
    nlinarith [hsquare']
  have hLogLRaw := Real.log_le_rpow_div hLpos.le (by norm_num : (0 : ℝ) < 1 / 5)
  have hLogL : Real.log L ≤ 5 * Real.rpow L (1 / 5 : ℝ) := by
    calc
      Real.log L ≤ Real.rpow L (1 / 5 : ℝ) / (1 / 5 : ℝ) := hLogLRaw
      _ = 5 * Real.rpow L (1 / 5 : ℝ) := by field_simp <;> ring
  have hpowL05 : 1 ≤ Real.rpow L (1 / 5 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 5)
    simpa using h
  have hLogA : Real.log Apath ≤ CLog * Real.rpow L (1 / 5 : ℝ) := by
    have hLogA' : Real.log Apath ≤ Real.log (50 * L) :=
      Real.log_le_log hApathPos (by simpa [Apath] using hApathBound)
    have hLogMul : Real.log (50 * L) = Real.log 50 + Real.log L := by
      rw [Real.log_mul (by norm_num : (50 : ℝ) ≠ 0) (ne_of_gt hLpos)]
    have hlog50 : 0 ≤ Real.log 50 := Real.log_nonneg (by norm_num)
    calc
      Real.log Apath ≤ Real.log (50 * L) := hLogA'
      _ = Real.log 50 + Real.log L := hLogMul
      _ ≤ Real.log 50 * Real.rpow L (1 / 5 : ℝ) +
            5 * Real.rpow L (1 / 5 : ℝ) := by
          have h50mul : Real.log 50 ≤ Real.log 50 * Real.rpow L (1 / 5 : ℝ) := by
            nlinarith [mul_le_mul_of_nonneg_left hpowL05 hlog50]
          linarith [hLogL, h50mul]
      _ = CLog * Real.rpow L (1 / 5 : ℝ) := by ring
  let Bcut : ℕ := B
  have hBReal : Real.rpow L 2 ≤ (Bcut : ℝ) := by
    dsimp [Bcut, B, memoryCutoff, PDScale.L, L]
    exact Nat.le_ceil _
  have h4K : 4 * (K : ℝ) ≤ L := by
    have h4KL₀ : 4 * (K : ℝ) ≤ L₀ := by linarith [hL₀K]
    dsimp [L, PDScale.L]
    exact h4KL₀.trans hL₀x
  have hsqrtLeL : Real.rpow L (1 / 2 : ℝ) ≤ L := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simpa [Real.rpow_one] using h
  have hKNreal : (K : ℝ) * (N : ℝ) ≤ Real.rpow L 2 := by
    calc
      (K : ℝ) * (N : ℝ) ≤ 4 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) :=
        calc
          _ ≤ (K : ℝ) * (4 * Real.rpow L (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg K)
          _ = _ := by ring
      _ ≤ L * Real.rpow L (1 / 2 : ℝ) := by
        calc
          _ = (4 * (K : ℝ)) * Real.rpow L (1 / 2 : ℝ) := by ring
          _ ≤ L * Real.rpow L (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right h4K (Real.rpow_nonneg hLpos.le _)
      _ ≤ L * L := mul_le_mul_of_nonneg_left hsqrtLeL hLpos.le
      _ = L ^ 2 := by ring
      _ = Real.rpow L (2 : ℝ) := (Real.rpow_natCast L 2).symm
  have hKN : K * N ≤ Bcut := by
    have hreal : (K * N : ℝ) ≤ (Bcut : ℝ) := hKNreal.trans hBReal
    exact_mod_cast hreal
  obtain ⟨hDecomp, hPathBound⟩ := hChoice S hSorig hxChoice' w hw Bcut hKN
  obtain ⟨hFinite, hCoeffBudget, _⟩ := hRoot S hSorig hxRoot'
  let T : Finset (EnvPath S.x K) := hFinite.toFinset
  have hmemT (γ : EnvPath S.x K) : γ ∈ T ↔ IsContributingPath F S γ := by
    simp [T, Set.Finite.mem_toFinset]
  have hCoeffIndicator :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) =
        ∑ γ ∈ T,
          if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    have hNot : ¬ IsContributingPath F S γ := by
      intro hC
      exact hγ ((hmemT γ).2 hC)
    simp [hNot]
  have hCoeffT :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) =
        ∑ γ ∈ T, ‖pathCoefficient F S γ‖ := by
    rw [hCoeffIndicator]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp [(hmemT γ).1 hγ]
  have hCoeffSum :
      ∑ γ ∈ T, ‖pathCoefficient F S γ‖ ≤ Real.exp (Cb * Real.rpow L (73 / 100 : ℝ)) := by
    rw [← hCoeffT]
    exact hCoeffBudget
  have hArchNonneg (γ : EnvPath S.x K) : 0 ≤ pathArch F S w γ := by
    unfold pathArch
    exact Finset.prod_nonneg fun j hj => by split_ifs <;> norm_num
  have hArchLeOne (γ : EnvPath S.x K) : pathArch F S w γ ≤ 1 := by
    unfold pathArch
    apply Finset.prod_le_one₀
    · intro j hj
      split_ifs <;> norm_num
    · intro j hj
      split_ifs <;> norm_num
  have hLifeNonneg (γ : EnvPath S.x K) : 0 ≤ doubledLifeMajorant F S γ := by
    unfold doubledLifeMajorant
    apply Finset.prod_nonneg
    intro i hi
    apply Finset.prod_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro life hl
    split_ifs <;> positivity
  let qTail := 8 * (K : ℝ) * Real.log 2 / (1 - Real.sqrt F.q_d)
  let lifeBound := Apath ^ (K * (M + N)) *
    Real.exp (qTail * ((N : ℝ) + 1))
  have hDiffIndicator :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then
          memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some Bcut) (some γ) distinctWeight else 0) =
        ∑ γ ∈ T,
          if IsContributingPath F S γ then
            memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some Bcut) (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    have hNot : ¬ IsContributingPath F S γ := by
      intro hC
      exact hγ ((hmemT γ).2 hC)
    simp [hNot]
  have hErrFinite :
      historyDistinct F S ρ w - historyDistinctTrunc F S ρ w =
        ∑ γ ∈ T,
          (memHistory F S ρ w none (some γ) distinctWeight -
            memHistory F S ρ w (some Bcut) (some γ) distinctWeight) := by
    calc
      _ = ∑' γ : EnvPath S.x K,
            if IsContributingPath F S γ then
              memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some Bcut) (some γ) distinctWeight else 0 := hDecomp
      _ = ∑ γ ∈ T,
            if IsContributingPath F S γ then
              memHistory F S ρ w none (some γ) distinctWeight -
                memHistory F S ρ w (some Bcut) (some γ) distinctWeight else 0 := hDiffIndicator
      _ = _ := by
            apply Finset.sum_congr rfl
            intro γ hγ
            simp [(hmemT γ).1 hγ]
  have hErrNorm :
      ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
        tailFactor * lifeBound * Real.exp (Cb * Real.rpow L (73 / 100 : ℝ)) := by
    rw [hErrFinite]
    calc
      _ ≤ ∑ γ ∈ T,
            ‖memHistory F S ρ w none (some γ) distinctWeight -
              memHistory F S ρ w (some Bcut) (some γ) distinctWeight‖ := norm_sum_le _ _
      _ ≤ ∑ γ ∈ T, tailFactor * lifeBound * ‖pathCoefficient F S γ‖ := by
        apply Finset.sum_le_sum
        intro γ hγ
        have hC : IsContributingPath F S γ := (hmemT γ).1 hγ
        have hDbl := hDouble S hSorig hxDouble' γ hC
        have hArchLife :
            pathArch F S w γ * doubledLifeMajorant F S γ ≤ lifeBound := by
          calc
            _ ≤ 1 * doubledLifeMajorant F S γ :=
              mul_le_mul_of_nonneg_right (hArchLeOne γ) (hLifeNonneg γ)
            _ = doubledLifeMajorant F S γ := by ring
            _ ≤ lifeBound := by
              dsimp [lifeBound, Apath, qTail]
              exact hDbl
        calc
          _ ≤ tailFactor * ‖pathCoefficient F S γ‖ * pathArch F S w γ *
                doubledLifeMajorant F S γ := hPathBound γ hC.1
          _ = tailFactor * ‖pathCoefficient F S γ‖ *
                (pathArch F S w γ * doubledLifeMajorant F S γ) := by ring
          _ ≤ tailFactor * ‖pathCoefficient F S γ‖ * lifeBound := by
                apply mul_le_mul_of_nonneg_left hArchLife
                exact mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (norm_nonneg _)
          _ = tailFactor * lifeBound * ‖pathCoefficient F S γ‖ := by ring
      _ = tailFactor * lifeBound * ∑ γ ∈ T, ‖pathCoefficient F S γ‖ := by
        rw [Finset.mul_sum]
      _ ≤ tailFactor * lifeBound * Real.exp (Cb * Real.rpow L (73 / 100 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hCoeffSum
        exact mul_nonneg (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by positivity)
  let z : ℤ := -(B : ℤ) + (K * pathLength S.x : ℤ)
  let E : ℝ := (z : ℝ) * Real.log 2 +
    Real.log Apath * ((K * (M + N) : ℕ) : ℝ) +
    qTail * ((N : ℝ) + 1) + Cb * Real.rpow L (73 / 100 : ℝ)
  have hzCast : (z : ℝ) = -(Bcut : ℝ) + (K : ℝ) * (N : ℝ) := by
    dsimp [z, Bcut, B, N]
    push_cast
    ring
  have hTailFactor : tailFactor = Real.exp ((z : ℝ) * Real.log 2) := by
    change (2 : ℝ) ^ z = Real.exp ((z : ℝ) * Real.log 2)
    rw [← Real.rpow_intCast (2 : ℝ) z,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hLifeBound : lifeBound = Real.exp
      (Real.log Apath * ((K * (M + N) : ℕ) : ℝ) + qTail * ((N : ℝ) + 1)) := by
    dsimp [lifeBound]
    rw [← Real.rpow_natCast Apath (K * (M + N))]
    rw [Real.rpow_def_of_pos hApathPos]
    rw [← Real.exp_add]
  have hBoundExp :
      tailFactor * lifeBound * Real.exp (Cb * Real.rpow L (73 / 100 : ℝ)) =
        Real.exp E := by
    dsimp [E]
    rw [hTailFactor, hLifeBound, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpow05le09 : Real.rpow L (1 / 2 : ℝ) ≤ Real.rpow L (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hpow02le09 : Real.rpow L (1 / 5 : ℝ) ≤ Real.rpow L (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hpow07 : Real.rpow L (7 / 10 : ℝ) =
      Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    have hadd := Real.rpow_add hLpos (1 / 5 : ℝ) (1 / 2 : ℝ)
    convert hadd using 1 <;> norm_num
  have hpow07le09 : Real.rpow L (7 / 10 : ℝ) ≤ Real.rpow L (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hpow073le09 : Real.rpow L (73 / 100 : ℝ) ≤ Real.rpow L (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hpow09leL : Real.rpow L (9 / 10 : ℝ) ≤ L := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (9 / 10 : ℝ) ≤ 1)
    simpa [Real.rpow_one] using hp
  have hcount : ((K * (M + N) : ℕ) : ℝ) ≤
      6 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_add] using hMN
  have hApathTerm : Real.log Apath * ((K * (M + N) : ℕ) : ℝ) ≤
      6 * (K : ℝ) * CLog * Real.rpow L (9 / 10 : ℝ) := by
    have hcountNonneg : 0 ≤ ((K * (M + N) : ℕ) : ℝ) := Nat.cast_nonneg _
    calc
      _ ≤ CLog * Real.rpow L (1 / 5 : ℝ) * ((K * (M + N) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hLogA hcountNonneg
      _ ≤ CLog * Real.rpow L (1 / 5 : ℝ) *
          (6 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcount
          (mul_nonneg hCLog.le (Real.rpow_nonneg (le_trans (by norm_num) hL) _))
      _ = 6 * (K : ℝ) * CLog * Real.rpow L (7 / 10 : ℝ) := by
        calc
          _ = 6 * (K : ℝ) * CLog *
              (Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 2 : ℝ)) := by ring
          _ = _ := congrArg (fun t : ℝ => 6 * (K : ℝ) * CLog * t) hpow07.symm
      _ ≤ 6 * (K : ℝ) * CLog * Real.rpow L (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow07le09 (by positivity)
  have hNplus09 : (N : ℝ) + 1 ≤ 4 * Real.rpow L (9 / 10 : ℝ) := by
    calc
      _ ≤ 4 * Real.rpow L (1 / 2 : ℝ) := hNplus
      _ ≤ 4 * Real.rpow L (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow05le09 (by norm_num)
  have hqTerm : qTail * ((N : ℝ) + 1) ≤
      4 * qTail * Real.rpow L (9 / 10 : ℝ) := by
    calc
      _ ≤ qTail * (4 * Real.rpow L (9 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hNplus09 hqTail
      _ = 4 * qTail * Real.rpow L (9 / 10 : ℝ) := by ring
  have hCbTerm : Cb * Real.rpow L (73 / 100 : ℝ) ≤
      Cb * Real.rpow L (9 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow073le09 hCb.le
  have hNlog : (N : ℝ) * Real.log L ≤ 20 * Real.rpow L (7 / 10 : ℝ) := by
    have hlogNonneg : 0 ≤ Real.log L := Real.log_nonneg hL
    calc
      _ ≤ (4 * Real.rpow L (1 / 2 : ℝ)) *
          (5 * Real.rpow L (1 / 5 : ℝ)) :=
        mul_le_mul hN hLogL hlogNonneg (by positivity)
      _ = 20 * Real.rpow L (7 / 10 : ℝ) := by
        calc
          _ = 20 * (Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 2 : ℝ)) := by ring
          _ = _ := congrArg (fun t : ℝ => 20 * t) hpow07.symm
  have hAterm : A * (N : ℝ) * Real.log L ≤
      20 * A * Real.rpow L (9 / 10 : ℝ) := by
    calc
      _ = A * ((N : ℝ) * Real.log L) := by ring
      _ ≤ A * (20 * Real.rpow L (7 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hNlog hA.le
      _ ≤ 20 * A * Real.rpow L (9 / 10 : ℝ) := by
        calc
          _ = 20 * A * Real.rpow L (7 / 10 : ℝ) := by ring
          _ ≤ 20 * A * Real.rpow L (9 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow07le09 (by positivity)
  have hKNsmall : (K : ℝ) * (N : ℝ) ≤
      4 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    calc
      _ ≤ (K : ℝ) * (4 * Real.rpow L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg K)
      _ = _ := by ring
  have hKterm : (K : ℝ) * (N : ℝ) * Real.log 2 ≤
      4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ) := by
    calc
      _ ≤ (4 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hKNsmall hlog2.le
      _ = 4 * (K : ℝ) * Real.log 2 * Real.rpow L (1 / 2 : ℝ) := by ring
      _ ≤ 4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow05le09 (by positivity)
  have hBKN : -(Bcut : ℝ) + (K : ℝ) * (N : ℝ) ≤
      -Real.rpow L (2 : ℝ) + 4 * (K : ℝ) * Real.rpow L (1 / 2 : ℝ) := by
    linarith [hBReal, hKNsmall]
  have hzTerm : (z : ℝ) * Real.log 2 ≤
      -Real.rpow L (2 : ℝ) * Real.log 2 +
        4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ) := by
    rw [hzCast]
    calc
      _ ≤ (-Real.rpow L (2 : ℝ) + 4 * (K : ℝ) *
            Real.rpow L (1 / 2 : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hBKN hlog2.le
      _ = -Real.rpow L (2 : ℝ) * Real.log 2 +
            4 * (K : ℝ) * Real.log 2 * Real.rpow L (1 / 2 : ℝ) := by ring
      _ ≤ -Real.rpow L (2 : ℝ) * Real.log 2 +
            4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ) := by
        have hscale := mul_le_mul_of_nonneg_left hpow05le09
          (by positivity : 0 ≤ 4 * (K : ℝ) * Real.log 2)
        calc
          _ = -Real.rpow L (2 : ℝ) * Real.log 2 +
              4 * (K : ℝ) * Real.log 2 * Real.rpow L (1 / 2 : ℝ) := by rfl
          _ ≤ -Real.rpow L (2 : ℝ) * Real.log 2 +
              4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ) :=
            add_le_add_right hscale (-Real.rpow L (2 : ℝ) * Real.log 2)
  have hResidual :
      Real.log Apath * ((K * (M + N) : ℕ) : ℝ) +
      qTail * ((N : ℝ) + 1) +
      Cb * Real.rpow L (73 / 100 : ℝ) + A * (N : ℝ) * Real.log L ≤
        (6 * (K : ℝ) * CLog + 4 * qTail + Cb + 20 * A) *
          Real.rpow L (9 / 10 : ℝ) := by
    calc
      _ = (Real.log Apath * ((K * (M + N) : ℕ) : ℝ) +
          qTail * ((N : ℝ) + 1)) +
          (Cb * Real.rpow L (73 / 100 : ℝ) + A * (N : ℝ) * Real.log L) := by ring
      _ ≤ (6 * (K : ℝ) * CLog * Real.rpow L (9 / 10 : ℝ) +
          4 * qTail * Real.rpow L (9 / 10 : ℝ)) +
          (Cb * Real.rpow L (9 / 10 : ℝ) +
            20 * A * Real.rpow L (9 / 10 : ℝ)) := by
        exact add_le_add (add_le_add hApathTerm hqTerm)
          (add_le_add hCbTerm hAterm)
      _ = _ := by ring
  have hL₀L : L₀ ≤ L := by simpa [L, PDScale.L] using hL₀x
  have hCtotalL : Ctotal ≤ Real.log 2 * L := by
    have hratio := hL₀Tot.trans hL₀L
    have hmul := (div_le_iff₀ hlog2).mp hratio
    simpa [mul_comm] using hmul
  have hCtotalPow : Ctotal * Real.rpow L (9 / 10 : ℝ) ≤
      Real.log 2 * Real.rpow L (2 : ℝ) := by
    calc
      _ ≤ Ctotal * L := mul_le_mul_of_nonneg_left hpow09leL hCtotal.le
      _ ≤ (Real.log 2 * L) * L :=
        mul_le_mul_of_nonneg_right hCtotalL hLpos.le
      _ = Real.log 2 * L ^ 2 := by ring
      _ = Real.log 2 * Real.rpow L (2 : ℝ) := by
        congr 1
        exact (Real.rpow_natCast L 2).symm
  have hEAbsorb : E + A * (N : ℝ) * Real.log L ≤ 0 := by
    calc
      _ = (z : ℝ) * Real.log 2 +
            (Real.log Apath * ((K * (M + N) : ℕ) : ℝ) +
              qTail * ((N : ℝ) + 1) + Cb * Real.rpow L (73 / 100 : ℝ) +
              A * (N : ℝ) * Real.log L) := by dsimp [E]; ring
      _ ≤ (-Real.rpow L (2 : ℝ) * Real.log 2 +
          4 * (K : ℝ) * Real.log 2 * Real.rpow L (9 / 10 : ℝ)) +
          (6 * (K : ℝ) * CLog + 4 * qTail + Cb + 20 * A) *
            Real.rpow L (9 / 10 : ℝ) := add_le_add hzTerm hResidual
      _ = -Real.rpow L (2 : ℝ) * Real.log 2 +
          Ctotal * Real.rpow L (9 / 10 : ℝ) := by dsimp [Ctotal]; ring
      _ ≤ 0 := by nlinarith [hCtotalPow]
  have hExpBound : Real.exp E ≤ Real.rpow L (-A * (N : ℝ)) := by
    calc
      Real.exp E ≤ Real.exp (Real.log L * (-A * (N : ℝ))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hEAbsorb]
      _ = Real.rpow L (-A * (N : ℝ)) :=
        (Real.rpow_def_of_pos hLpos _).symm
  calc
    ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
        tailFactor * lifeBound * Real.exp (Cb * Real.rpow L (73 / 100 : ℝ)) := hErrNorm
    _ = Real.exp E := hBoundExp
    _ ≤ Real.rpow L (-A * (N : ℝ)) := hExpBound
    _ = 1 * Real.rpow S.L (-A * (S.N : ℝ)) := by
      simp [L, N, PDScale.N]

end
end ArtinPrimitiveRoots.TypeII.PD
