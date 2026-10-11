import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C2b
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C3
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S2

/-!
# A2-QS-CANCEL, part C4: the residual block bound (assembly)

Columns in `(n, 2n]` with `n ≥ 1` exclude `⊤`, so every coprime pair has `c d ≠ ⊤` and S2
applies; sum S2 over pairs (`qsPairSum` is linear in the kernel), replace the main difference by
the boundary kernel (C1), bound it by C2b, `qs_norm_symm_M0` and `HasExponent α`
(`√(M/κ) (2n + κ^α) ≪ n√(M/κ) + √M κ^{α-1/2}`), and the remainders by C3a-C3d with one common
`η ≤ min(η₀'s, θ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

private theorem qsPairSum_congr_of_coprime (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (Φ Ψ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (h : ∀ c d, c ∈ cols → d ∈ cols → IsCoprime c d → Φ c d = Ψ c d) :
    qsPairSum cols z Φ = qsPairSum cols z Ψ := by
  classical
  unfold qsPairSum
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcd : IsCoprime c d
  · simp [hcd, h c d hc hd hcd]
  · simp [hcd]

private theorem qsPairSum_add (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (Φ Ψ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    qsPairSum cols z (fun c d => Φ c d + Ψ c d) =
      qsPairSum cols z Φ + qsPairSum cols z Ψ := by
  classical
  unfold qsPairSum
  have hp (c d : Ideal (𝓞 K)) :
      (if IsCoprime c d then z c * conj (z d) * (Φ c d + Ψ c d) else 0) =
        (if IsCoprime c d then z c * conj (z d) * Φ c d else 0) +
          (if IsCoprime c d then z c * conj (z d) * Ψ c d else 0) := by
    by_cases hcd : IsCoprime c d <;> simp [hcd, mul_add]
  simp_rw [hp, Finset.sum_add_distrib]

private theorem qsPairSum_sub (cols : Finset (Ideal (𝓞 K)))
    (z : Ideal (𝓞 K) → ℂ) (Φ Ψ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    qsPairSum cols z (fun c d => Φ c d - Ψ c d) =
      qsPairSum cols z Φ - qsPairSum cols z Ψ := by
  classical
  unfold qsPairSum
  have hp (c d : Ideal (𝓞 K)) :
      (if IsCoprime c d then z c * conj (z d) * (Φ c d - Ψ c d) else 0) =
        (if IsCoprime c d then z c * conj (z d) * Φ c d else 0) -
          (if IsCoprime c d then z c * conj (z d) * Ψ c d else 0) := by
    by_cases hcd : IsCoprime c d <;> simp [hcd, mul_sub]
  simp_rw [hp, Finset.sum_sub_distrib]

/-- C4 (IMPL): residual block bound
`‖Σ₃‖ ≪ (N𝔮)^8 (Mn)^δ (M + n + √M κ^{α-1/2} + n√(M/κ)) ‖z‖²`. -/
theorem qs_residual_block_bound_C4 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hexp : QSHasExponent F α)
    (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M n κ : ℝ) (𝔮 : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
        1 ≤ n → 1 ≤ κ → 2 * κ ≤ M → QSBlockCols m qS 𝔮 n cols →
      qsN 𝔮 * n ^ 2 * (M * n) ^ θ ≤ κ * M →
        ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
          C * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  classical
  obtain ⟨ηa, hηa, ha⟩ := qs_orig_remainders_C3a F hrf hqS W hW α hα1 hα2 hexp δ hδ
  obtain ⟨ηb, hηb, hb⟩ := qs_dual_main_remainders_C3b F hrf hqS W hW α hα1 hα2 hexp δ hδ
  obtain ⟨ηc, hηc, hc⟩ := qs_dual_transition_C3c F hrf hqS W hW α hα1 hα2 hexp δ hδ
  let η : ℝ := min (min ηa ηb) (min ηc (δ / 4))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hηa' : η ≤ ηa := by dsimp [η]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hηb' : η ≤ ηb := by dsimp [η]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hηc' : η ≤ ηc := by dsimp [η]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηδ : η ≤ δ / 4 := by dsimp [η]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨Ca, hCa, ha⟩ := ha η hη hηa'
  obtain ⟨Cb, hCb, hb⟩ := hb η hη hηb'
  obtain ⟨Cc, hCc, hc⟩ := hc η hη hηc'
  obtain ⟨Ct, hCt, ht⟩ := qs_tails_C3d F hrf hqS W hW θ hθ η hη
  obtain ⟨Cm, hCm, hm⟩ := qs_paired_main_bound_C2b F hrf hqS W hW η hη
  have hε : 0 < δ / 4 := by positivity
  obtain ⟨Cn, hCn, hn⟩ := hexp (δ / 4) hε
  refine ⟨Ca + Cb + Cc + Ct + 2 * Cm * Cn * 2 ^ (δ / 4), by positivity, ?_⟩
  intro M n κ 𝔮 cols z hn0 hκ hM hcols hmargin
  have hMpos : 0 < M := by nlinarith
  have hnpos : 0 < n := by linarith
  have hκpos : 0 < κ := by linarith
  have hκM : κ ≤ M := by linarith
  have hX : 1 ≤ M * n := by nlinarith
  have hXpos : 0 < M * n := by positivity
  have hshape : 1 ≤ qsBlockShape M n κ α := by
    have hsqrt : 0 ≤ Real.sqrt M * κ ^ (α - 1 / 2) := by positivity
    have hlast : 0 ≤ n * Real.sqrt (M / κ) := by positivity
    dsimp [qsBlockShape]
    nlinarith
  have henergy : 0 ≤ ∑ c ∈ cols, ‖z c‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hn2 : 1 ≤ 2 * n := by nlinarith
  have hκ1 : 1 ≤ κ := hκ
  have hnorm := hn (2 * n) κ hn2 hκ1
  have hsymm := qs_norm_symm_M0 F hrf (2 * n) κ
  have hnorm' : qsNorm F κ (2 * n) ≤ Cn * ((2 * n) * κ) ^ (δ / 4) * (2 * n + κ ^ α) := by
    rw [← hsymm]
    exact hnorm
  have hMmain := hm M κ n 𝔮 cols z hMpos hκ hn0 hcols
  obtain ⟨hqs, hbad, hcol, hclass⟩ := hcols
  have hqnorm : 0 ≤ qsN 𝔮 := by positivity
  have hqpow : qsN 𝔮 ^ 2 ≤ qsN 𝔮 ^ 8 := by
    by_cases hq0 : 𝔮 = ⊥
    · simp [qsN, hq0]
    · have hnat : 0 < Ideal.absNorm 𝔮 := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero hq0)
      have hqpos : 0 < qsN 𝔮 := by exact_mod_cast hnat
      have hqone : 1 ≤ qsN 𝔮 := by
        have hnat : (1 : ℕ) ≤ Ideal.absNorm 𝔮 := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnat)
        exact_mod_cast hnat
      nlinarith [sq_nonneg (qsN 𝔮 ^ 2 - 1)]
  have hpowM : (n * κ) ^ η ≤ (M * n) ^ η := by
    apply Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
  have hpowN : ((2 * n) * κ) ^ (δ / 4) ≤ (2 * (M * n)) ^ (δ / 4) := by
    apply Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hpowScale : (n * κ) ^ η * ((2 * n) * κ) ^ (δ / 4) ≤
      2 ^ (δ / 4) * (M * n) ^ δ := by
    calc
      (n * κ) ^ η * ((2 * n) * κ) ^ (δ / 4) ≤
          (M * n) ^ η * (2 * (M * n)) ^ (δ / 4) :=
            mul_le_mul hpowM hpowN (by positivity) (by positivity)
      _ = 2 ^ (δ / 4) * (M * n) ^ (η + δ / 4) := by
            rw [Real.mul_rpow (by norm_num) (le_of_lt hXpos)]
            calc
              (M * n) ^ η * (2 ^ (δ / 4) * (M * n) ^ (δ / 4)) =
                  2 ^ (δ / 4) * ((M * n) ^ η * (M * n) ^ (δ / 4)) := by ring
              _ = 2 ^ (δ / 4) * (M * n) ^ (η + δ / 4) := by
                    rw [← Real.rpow_add hXpos η (δ / 4)]
      _ ≤ 2 ^ (δ / 4) * (M * n) ^ δ := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hX (by linarith))
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have hbaseMain :
      (n * κ) ^ η * Real.sqrt (M / κ) * qsNorm F κ (2 * n) ≤
        2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ * qsBlockShape M n κ α := by
    calc
      (n * κ) ^ η * Real.sqrt (M / κ) * qsNorm F κ (2 * n) ≤
          (n * κ) ^ η * Real.sqrt (M / κ) *
            (Cn * ((2 * n) * κ) ^ (δ / 4) * (2 * n + κ ^ α)) :=
              mul_le_mul_of_nonneg_left hnorm' (by positivity)
      _ ≤ 2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ * qsBlockShape M n κ α := by
        have hterm : Real.sqrt (M / κ) * (2 * n + κ ^ α) ≤
            2 * n * Real.sqrt (M / κ) + Real.sqrt M * κ ^ (α - 1 / 2) := by
          rw [mul_add]
          have hsquare : Real.sqrt (M / κ) * κ ^ α =
              Real.sqrt M * κ ^ (α - 1 / 2) := by
            rw [Real.sqrt_div (by positivity)]
            simp only [Real.sqrt_eq_rpow]
            rw [Real.rpow_sub hκpos α (1 / 2)]
            field_simp
          rw [hsquare]
          exact le_of_eq (by ring)
        have hshape' : 2 * n * Real.sqrt (M / κ) +
            Real.sqrt M * κ ^ (α - 1 / 2) ≤ 2 * qsBlockShape M n κ α := by
          dsimp [qsBlockShape]
          have hterms : 0 ≤ M + n := by positivity
          have hterm1 : 0 ≤ Real.sqrt M * κ ^ (α - 1 / 2) := by positivity
          have hterm2 : 0 ≤ n * Real.sqrt (M / κ) := by positivity
          have hMnonneg : 0 ≤ M := le_of_lt hMpos
          have hnnonneg : 0 ≤ n := le_of_lt hnpos
          nlinarith
        calc
          _ = Cn * ((n * κ) ^ η * ((2 * n) * κ) ^ (δ / 4)) *
                (Real.sqrt (M / κ) * (2 * n + κ ^ α)) := by ring
          _ ≤ Cn * ((n * κ) ^ η * ((2 * n) * κ) ^ (δ / 4)) *
                (2 * qsBlockShape M n κ α) := by
                  exact mul_le_mul_of_nonneg_left (le_trans hterm hshape') (by positivity)
          _ ≤ Cn * (2 ^ (δ / 4) * (M * n) ^ δ) *
                (2 * qsBlockShape M n κ α) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  apply mul_le_mul_of_nonneg_left hpowScale (by positivity)
          _ = 2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ * qsBlockShape M n κ α := by ring
  have hmainBound :
      ‖qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)‖ ≤
        (2 * Cm * Cn * 2 ^ (δ / 4)) * qsN 𝔮 ^ 8 * (M * n) ^ δ *
          qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ ≤ Cm * qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
            qsNorm F κ (2 * n) * ∑ c ∈ cols, ‖z c‖ ^ 2 := hMmain
      _ ≤ 2 * Cm * Cn * 2 ^ (δ / 4) * qsN 𝔮 ^ 8 * (M * n) ^ δ *
            qsBlockShape M n κ α * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
              calc
                Cm * qsN 𝔮 ^ 2 * (n * κ) ^ η * Real.sqrt (M / κ) *
                    qsNorm F κ (2 * n) * ∑ c ∈ cols, ‖z c‖ ^ 2
                  ≤ Cm * qsN 𝔮 ^ 2 *
                      (2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ * qsBlockShape M n κ α) *
                        ∑ c ∈ cols, ‖z c‖ ^ 2 := by
                    have hp := mul_le_mul_of_nonneg_right hbaseMain henergy
                    have hp' := mul_le_mul_of_nonneg_left hp
                      (by positivity : 0 ≤ Cm * qsN 𝔮 ^ 2)
                    convert hp' using 1 <;> ring
                _ ≤ Cm * qsN 𝔮 ^ 8 *
                      (2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ * qsBlockShape M n κ α) *
                        ∑ c ∈ cols, ‖z c‖ ^ 2 := by
                    have hp := mul_le_mul_of_nonneg_right hqpow
                      (by positivity : 0 ≤ 2 * Cn * 2 ^ (δ / 4) * (M * n) ^ δ *
                        qsBlockShape M n κ α)
                    have hp' := mul_le_mul_of_nonneg_left hp
                      (by positivity : 0 ≤ Cm * ∑ c ∈ cols, ‖z c‖ ^ 2)
                    convert hp' using 1 <;> ring
                _ = _ := by ring
  have hcols' : QSBlockCols m qS 𝔮 n cols := ⟨hqs, hbad, hcol, hclass⟩
  have hC3a := ha M n κ 𝔮 cols z hn0 hκ hM hcols'
  have hC3b := hb M n κ 𝔮 cols z hn0 hκ hM hcols'
  have hC3c := hc M n κ 𝔮 cols z hn0 hκ hM hcols'
  have hC3d := ht M n κ 𝔮 cols z hn0 hκ hM hcols' hmargin
  have hXnonneg : 0 ≤ M * n := le_of_lt hXpos
  have hshape0 : 0 ≤ qsBlockShape M n κ α := by linarith
  have htailScale : (M * n) ^ (-1 : ℝ) ≤ (M * n) ^ δ * qsBlockShape M n κ α := by
    have hpow : (M * n) ^ (-1 : ℝ) ≤ (M * n) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    calc
      (M * n) ^ (-1 : ℝ) ≤ (M * n) ^ δ := hpow
      _ ≤ (M * n) ^ δ * qsBlockShape M n κ α := by
            nlinarith [mul_nonneg (Real.rpow_nonneg hXnonneg δ) (by linarith :
              0 ≤ qsBlockShape M n κ α - 1)]
  have htailBound :
      ‖qsPairSum cols z (fun c d =>
          qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
            qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
            qsDualHighKernel F W M κ 𝔮 c d)‖ ≤
        Ct * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    calc
      _ ≤ Ct * qsN 𝔮 ^ 8 * (M * n) ^ (-1 : ℝ) *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := hC3d
      _ ≤ Ct * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
              have := mul_le_mul_of_nonneg_left htailScale (by positivity :
                0 ≤ Ct * qsN 𝔮 ^ 8)
              nlinarith [henergy]
  let Bmain : ℂ := qsPairSum cols z (qsBoundaryKernel F W M κ 𝔮)
  let Bdual : ℂ := qsPairSum cols z (fun c d =>
    qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮 c d -
      qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮 c d)
  let Btrans : ℂ := qsPairSum cols z (fun c d =>
    qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮 c d)
  let Borig : ℂ := qsPairSum cols z (fun c d =>
    qsOrigKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) 𝔮 c d -
      qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) 𝔮 c d -
      qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) 𝔮 c d)
  let Btail : ℂ := qsPairSum cols z (fun c d =>
    qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
      qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
      qsDualHighKernel F W M κ 𝔮 c d)
  have hΛ : 1 ≤ (M * n) ^ η := by
    simpa using Real.rpow_le_rpow (by norm_num) hX (le_of_lt hη)
  have hdecomp : qsResidualBlock F W M κ 𝔮 cols z = Bmain + Bdual + Btrans + Borig + Btail := by
    change qsPairSum cols z (fun c d =>
      qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d)) = Bmain + Bdual + Btrans + Borig + Btail
    have hkernel (c d : Ideal (𝓞 K)) (hc : c ∈ cols) (hd : d ∈ cols)
        (hcop : IsCoprime c d) :
        qsHigh (fun x => (W x : ℂ)) M κ 𝔮 (qsPairChar F c d) =
          qsBoundaryKernel F W M κ 𝔮 c d +
            (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮 c d -
              qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮 c d) +
            qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮 c d +
            (qsOrigKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) 𝔮 c d -
              qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) 𝔮 c d -
              qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) 𝔮 c d) +
            (qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
              qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
              qsDualHighKernel F W M κ 𝔮 c d) := by
      have hcc := hcol c hc
      have hdd := hcol d hd
      have hcl := hclass c hc d hd
      have hcd1 : c * d ≠ ⊤ := by
        intro htop
        have hNc : 1 < qsN c := lt_of_le_of_lt hn0 hcc.2.2.1
        have hNd : 1 < qsN d := lt_of_le_of_lt hn0 hdd.2.2.1
        have hmul : qsN (c * d) = qsN c * qsN d := by
          dsimp [qsN]
          exact_mod_cast (map_mul (Ideal.absNorm) c d)
        rw [htop] at hmul
        simp [qsN] at hmul
        nlinarith [mul_pos (show 0 < qsN c - 1 by linarith)
          (show 0 < qsN d - 1 by linarith)]
      have hpair := qs_pair_error_tuple_S2 F hrf hqS W hW M κ ((M * n) ^ η) n
        hMpos hΛ hnpos 𝔮 c d hqs hbad hcc.1 hdd.1 hcop hcd1 hcl hcc.2.1 hdd.2.1
      have hboundary := qs_difference_exact_support_C1 F hrf hqS W hW M κ
        ((M * n) ^ η) n hMpos 𝔮 c d hqs hbad hcc.1 hdd.1 hcop hcl hcc.2.1 hdd.2.1
      rw [hboundary] at hpair
      calc
        _ = _ := hpair
        _ = _ := by ring
    calc
      _ = qsPairSum cols z (fun c d =>
            qsBoundaryKernel F W M κ 𝔮 c d +
              (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮 c d -
                qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮 c d) +
              qsDualKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) n 𝔮 c d +
              (qsOrigKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) 𝔮 c d -
                qsOrigKernel (qsInnerRes K) F W M κ ((M * n) ^ η) 𝔮 c d -
                qsOrigKernel (qsInnerTrans K) F W M κ ((M * n) ^ η) 𝔮 c d) +
              (qsDualKernel (qsInnerTail K) F W M κ ((M * n) ^ η) n 𝔮 c d -
                qsOrigKernel (qsInnerTail K) F W M κ ((M * n) ^ η) 𝔮 c d +
                qsDualHighKernel F W M κ 𝔮 c d)) :=
              qsPairSum_congr_of_coprime cols z _ _ hkernel
      _ = Bmain + Bdual + Btrans + Borig + Btail := by
            unfold Bmain Bdual Btrans Borig Btail
            simp only [qsPairSum_add]
  have hnormDecomp : ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
      ‖Bmain‖ + ‖Bdual‖ + ‖Btrans‖ + ‖Borig‖ + ‖Btail‖ := by
    rw [hdecomp]
    have h1 := norm_add_le (Bmain + Bdual + Btrans + Borig) Btail
    have h2 := norm_add_le (Bmain + Bdual + Btrans) Borig
    have h3 := norm_add_le (Bmain + Bdual) Btrans
    have h4 := norm_add_le Bmain Bdual
    nlinarith [h1, h2, h3, h4]
  have hdualGroup : ‖Bdual‖ ≤
      ‖qsPairSum cols z (fun c d => qsDualKernel (qsInnerHighDiv K) F W M κ
        ((M * n) ^ η) n 𝔮 c d)‖ +
      ‖qsPairSum cols z (fun c d => qsDualKernel (qsInnerRes K) F W M κ
        ((M * n) ^ η) n 𝔮 c d)‖ := by
    have heq : Bdual = qsPairSum cols z (fun c d =>
        qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮 c d -
          qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮 c d) := rfl
    rw [heq, qsPairSum_sub]
    simpa [add_comm] using norm_sub_le
      (qsPairSum cols z (qsDualKernel (qsInnerRes K) F W M κ ((M * n) ^ η) n 𝔮))
      (qsPairSum cols z (qsDualKernel (qsInnerHighDiv K) F W M κ ((M * n) ^ η) n 𝔮))
  have hOrigGroup : ‖Borig‖ ≤
      ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerHighDiv K) F W M κ
        ((M * n) ^ η) 𝔮 c d)‖ +
      ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerRes K) F W M κ
        ((M * n) ^ η) 𝔮 c d)‖ +
      ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerTrans K) F W M κ
        ((M * n) ^ η) 𝔮 c d)‖ := by
    dsimp [Borig]
    let A := qsPairSum cols z (fun c d => qsOrigKernel (qsInnerHighDiv K) F W M κ
      ((M * n) ^ η) 𝔮 c d)
    let B := qsPairSum cols z (fun c d => qsOrigKernel (qsInnerRes K) F W M κ
      ((M * n) ^ η) 𝔮 c d)
    let C := qsPairSum cols z (fun c d => qsOrigKernel (qsInnerTrans K) F W M κ
      ((M * n) ^ η) 𝔮 c d)
    have hAB := norm_sub_le A B
    have hABC := norm_sub_le (A - B) C
    rw [qsPairSum_sub, qsPairSum_sub]
    change ‖(A - B) - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖
    linarith
  have hsumBd :
      ‖qsResidualBlock F W M κ 𝔮 cols z‖ ≤
        (Ca + Cb + Cc + Ct + 2 * Cm * Cn * 2 ^ (δ / 4)) *
          qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
            ∑ c ∈ cols, ‖z c‖ ^ 2 := by
    have hDualBound : ‖Bdual‖ ≤
        Cb * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      calc
        ‖Bdual‖ ≤
            ‖qsPairSum cols z (fun c d => qsDualKernel (qsInnerHighDiv K) F W M κ
              ((M * n) ^ η) n 𝔮 c d)‖ +
              ‖qsPairSum cols z (fun c d => qsDualKernel (qsInnerRes K) F W M κ
              ((M * n) ^ η) n 𝔮 c d)‖ := hdualGroup
        _ ≤ _ := hC3b
    have hOrigBound : ‖Borig‖ ≤
        Ca * qsN 𝔮 ^ 8 * (M * n) ^ δ * qsBlockShape M n κ α *
          ∑ c ∈ cols, ‖z c‖ ^ 2 := by
      calc
        ‖Borig‖ ≤
            ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerHighDiv K) F W M κ
              ((M * n) ^ η) 𝔮 c d)‖ +
              ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerRes K) F W M κ
              ((M * n) ^ η) 𝔮 c d)‖ +
              ‖qsPairSum cols z (fun c d => qsOrigKernel (qsInnerTrans K) F W M κ
              ((M * n) ^ η) 𝔮 c d)‖ := hOrigGroup
        _ ≤ _ := hC3a
    nlinarith [hnormDecomp, hmainBound, hDualBound, hC3c, hOrigBound, htailBound]
  exact hsumBd

end ArtinPrimitiveRoots.A2
