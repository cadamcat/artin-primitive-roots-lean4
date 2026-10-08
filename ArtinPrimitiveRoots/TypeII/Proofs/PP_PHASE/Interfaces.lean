import ArtinPrimitiveRoots.TypeII.PP.Defs
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.LogPhaseLow
import ArtinPrimitiveRoots.TypeII.Proofs.PP_PHASE.PhaseReindex

/-! Exact interfaces for the PP-PHASE decomposition. -/

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open MeasureTheory
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

def phaseMeanValueInput : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ k : ℕ, 2 ≤ k →
      ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧
        ∀ M : ℕ, 1 ≤ M →
          (vinogradovCount s k M : ℝ) ≤
            Real.exp (C₁ * Real.rpow (k : ℝ) C₂) *
              Real.rpow (M : ℝ)
                (2 * (s : ℝ) - ((k : ℝ) * ((k : ℝ) + 1)) / 2 + 1 / 100 : ℝ)

noncomputable def phaseCoefficient (v θ : ℝ) (b j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * v /
    (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * ((b : ℝ) + θ) ^ (j + 1))

noncomputable def phasePolynomialSum (v θ : ℝ) (b k M : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    additiveCharacter
      (∑ j : Fin k, phaseCoefficient v θ b j.val * (h : ℝ) ^ (j.val + 1))

/-- Shift averaging and the Taylor remainder on a dyadic natural interval. -/
theorem phase_shift_average {H y θ v : ℝ} {l u k M : ℕ}
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y)
    (hv : |v| ≤ Real.rpow H y) (hk : 4 * y + 8 ≤ k)
    (hM : 1 ≤ M) (hMupper : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hcard : ((Finset.Icc l u).card : ℝ) ≤ 2 * H)
    (hinterval : ∀ b ∈ Finset.Icc l u,
      H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H) :
    ‖∑ b ∈ Finset.Icc l u,
        Complex.exp (Complex.I * v * Real.log ((b : ℝ) + θ))‖ ≤
      (1 / (M : ℝ)) *
        ∑ b ∈ Finset.Icc l u, ‖phasePolynomialSum v θ b k M‖ +
        4 * M + 8 / H := by
  sorry

abbrev PhaseBoxIndex (k M : ℕ) := ∀ j : Fin k, Fin (M ^ (j.val + 1))

noncomputable def phaseAlphaVector (H y θ : ℝ) (b : ℕ) (k : ℕ) : Fin k → ℝ :=
  fun j => phaseCoefficient (Real.rpow H y) θ b j.val

def phaseInBox {k M : ℕ} (r : PhaseBoxIndex k M) (α : Fin k → ℝ) : Prop :=
  ∀ j : Fin k,
    ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ Int.fract (α j) ∧
      Int.fract (α j) < ((r j).val + 1 : ℝ) / (M : ℝ) ^ (j.val + 1)

noncomputable def phaseBoxMembers {H y θ : ℝ} {k M : ℕ} (B : Finset ℕ)
    (r : PhaseBoxIndex k M) : Finset ℕ := by
  classical
  exact B.filter fun b => phaseInBox r (phaseAlphaVector H y θ b k)

/-- Every coefficient box contains few quotient indices. -/
theorem phase_box_occupancy {H y θ : ℝ} {k M : ℕ} (B : Finset ℕ)
    (hH : 16 ≤ H) (hy : 4 / 5 ≤ y)
    (hklo : 4 * y + 8 ≤ k) (hkhi : (k : ℝ) ≤ 4 * y + 9)
    (hM : 0 < M)
    (hMlo : Real.rpow H (3 / 4) / 2 ≤ (M : ℝ))
    (hMhi : (M : ℝ) ≤ Real.rpow H (3 / 4))
    (hB : ∀ b ∈ B, H ≤ (b : ℝ) + θ ∧ (b : ℝ) + θ ≤ 2 * H)
    (r : PhaseBoxIndex k M) :
    ((phaseBoxMembers (H := H) (y := y) (θ := θ) B r).card : ℝ) ≤
      Real.exp (10 * k) * Real.rpow H (4 / 5) := by
  sorry

noncomputable def phaseWeylSum (k M : ℕ) (a : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    additiveCharacter (∑ j : Fin k, a j * (h : ℝ) ^ (j.val + 1))

/-- Exact weighted torus moment for the Vinogradov mean-value count. -/
theorem phase_torus_moment {s k M : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (c : ℕ → ℂ) (hc : ∀ h ∈ Finset.Icc 1 M, ‖c h‖ ≤ D) :
    ∫ a : Fin k → ℝ,
      Set.indicator {a | ∀ j, 0 ≤ a j ∧ a j ≤ 1}
        (fun a => ‖∑ h ∈ Finset.Icc 1 M,
          c h * additiveCharacter
            (∑ j : Fin k, a j * (h : ℝ) ^ (j.val + 1))‖ ^ (2 * s)) a ≤
      D ^ (2 * s) * (vinogradovCount s k M : ℝ) := by
  sorry

def phaseClosedBox {k M : ℕ} (r : PhaseBoxIndex k M) : Set (Fin k → ℝ) :=
  {a | ∀ j : Fin k,
    ((r j).val : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ a j ∧
      a j ≤ ((r j).val + 1 : ℝ) / (M : ℝ) ^ (j.val + 1)}

noncomputable def phaseBoxExponent (k : ℕ) : ℕ :=
  ∑ j : Fin k, (j.val + 1)

/-- Sum of the suprema over all closed coefficient boxes. -/
theorem phase_box_suprema (s k M : ℕ) (hM : 0 < M) :
    ∑ r : PhaseBoxIndex k M,
      (sSup {z : ℝ | ∃ a : Fin k → ℝ, a ∈ phaseClosedBox r ∧
        z = ‖phaseWeylSum k M a‖}) ^ (2 * s) ≤
      (4 * Real.pi : ℝ) ^ (2 * s * k) *
        (M : ℝ) ^ phaseBoxExponent k * (vinogradovCount s k M : ℝ) := by
  sorry

/-- The common target window restricted to a given frequency regime. -/
def phaseWindowBound (freq : ℝ → ℝ → Prop) (C C₀ x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x →
    let L := Real.log x
    let T := Real.log L
    ∀ N' : ℝ, Real.exp (L / T ^ 2) ≤ N' → N' ≤ 2 * Real.rpow x 5 →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.rpow L C →
        ∀ a : ZMod q, ∀ v : ℝ,
          Real.exp (L / (2 * T ^ 2)) ≤ |v| → |v| ≤ 4 * Real.rpow x 3 →
            freq (N' / (q : ℝ)) v →
              ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
                ‖residuePhaseSum N' q a v
                    {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                  C₀ * (N' / q) * Real.exp (-L / Real.rpow T 11)

def phaseLogPhaseStatement : Prop :=
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
                    ‖residuePhaseSum N' q a v
                        {n : ℕ | N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂}‖ ≤
                      C₀ * (N' / q) * Real.exp (-L / Real.rpow T C₃)

/-- Combine the easy and growing-degree frequency ranges. -/
theorem phase_from_regimes (hMV : phaseMeanValueInput)
    (hLow : ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => |v| < Real.rpow H (4 / 5)) C C₀ x₀)
    (hHigh : phaseMeanValueInput → ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => Real.rpow H (4 / 5) ≤ |v|) C C₀ x₀) :
    phaseLogPhaseStatement := by
  classical
  unfold phaseLogPhaseStatement
  refine ⟨11, by norm_num, ?_⟩
  intro C hC
  obtain ⟨C₀L, x₀L, hC₀L, hx₀L, hLowC⟩ := hLow C hC
  obtain ⟨C₀H, x₀H, hC₀H, hx₀H, hHighC⟩ := hHigh hMV C hC
  refine ⟨max C₀L C₀H, max x₀L x₀H, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hC₀L (le_max_left _ _)
  · exact lt_of_lt_of_le hx₀L (le_max_left _ _)
  · intro x hx
    dsimp only
    intro N' hNlo hNhi q hq hqC a v hvlo hvhi N₁ N₂ hN₁ hN₂
    have hxL : x₀L ≤ x := (le_max_left _ _).trans hx
    have hxH : x₀H ≤ x := (le_max_right _ _).trans hx
    let H := N' / (q : ℝ)
    by_cases hfreq : Real.rpow H (4 / 5) ≤ |v|
    · have hest := hHighC x hxH N' hNlo hNhi q hq hqC a v hvlo hvhi
        (by simpa [H] using hfreq) N₁ N₂ hN₁ hN₂
      have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hNpos : 0 < N' := lt_of_lt_of_le (Real.exp_pos _) hNlo
      have hfac : 0 ≤ (N' / (q : ℝ)) * Real.exp
          (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) :=
        mul_nonneg (div_nonneg hNpos.le hqR.le) (Real.exp_pos _).le
      calc
        _ ≤ C₀H * (N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := hest
        _ = C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) := by ring
        _ ≤ max C₀L C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hfac
        _ = max C₀L C₀H * (N' / q) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := by ring
    · have hfreq' : |v| < Real.rpow H (4 / 5) := lt_of_not_ge hfreq
      have hest := hLowC x hxL N' hNlo hNhi q hq hqC a v hvlo hvhi
        (by simpa [H] using hfreq') N₁ N₂ hN₁ hN₂
      have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hNpos : 0 < N' := lt_of_lt_of_le (Real.exp_pos _) hNlo
      have hfac : 0 ≤ (N' / (q : ℝ)) * Real.exp
          (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) :=
        mul_nonneg (div_nonneg hNpos.le hqR.le) (Real.exp_pos _).le
      calc
        _ ≤ C₀L * (N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := hest
        _ = C₀L * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) := by ring
        _ ≤ max C₀L C₀H * ((N' / (q : ℝ)) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hfac
        _ = max C₀L C₀H * (N' / q) * Real.exp
              (-Real.log x / Real.rpow (Real.log (Real.log x)) 11) := by ring

/-- Low frequencies use the first-derivative estimate and quotient reindexing. -/
theorem phase_low_regime_bound :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => |v| < Real.rpow H (4 / 5)) C C₀ x₀ := by
  sorry

/-- High frequencies use the Taylor polynomial and Vinogradov mean value. -/
theorem phase_high_regime_bound (hMV : phaseMeanValueInput) :
    ∀ C : ℝ, 0 < C →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧
        phaseWindowBound (fun H v => Real.rpow H (4 / 5) ≤ |v|) C C₀ x₀ := by
  sorry

end ArtinPrimitiveRoots.Proofs.pp_phase_p
