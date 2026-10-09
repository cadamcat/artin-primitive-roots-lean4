import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeDenominators

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The normalized finite residue coefficients have square mass O(1/Y), uniformly
over all bounded residue factors on the contributing denominator support. -/
theorem probe_additive_mass {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) (f : ℝ → ℂ)
    (hcompact : HasCompactSupport f) (hpositive : tsupport f ⊆ Set.Ioi 0)
    (hcontinuous : Continuous f) (hnonzero : ∃ v, f v ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∃ P : Finset S.ExtIdeal,
        (∀ s : S.ExtIdeal, s ∈ P ↔ f (qI s.1 / Y) ≠ 0) ∧
        ∀ ρ : ∀ s : S.ExtIdeal, ResidueRing E s → ℂ,
          (∀ s d, ‖ρ s d‖ ≤ 1) →
          (∑ s ∈ P, ∑ᶠ d : ResidueRing E s,
            ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d‖ ^ 2)
            ≤ C / Y := by
  obtain ⟨L, B, C, hL, hB, hC, hinterval, hdenominators⟩ :=
    probe_denominator_control S f hcompact hpositive hcontinuous hnonzero
  refine ⟨C, hC, ?_⟩
  intro Y hY
  have hYpos : 0 < Y := by linarith
  obtain ⟨P, hP, hcard, _⟩ := hdenominators Y hY
  refine ⟨P, hP, ?_⟩
  intro ρ hρ
  have hresidue (s : S.ExtIdeal) (hs : s ∈ P) :
      (∑ᶠ d : ResidueRing E s,
        ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d‖ ^ 2)
        ≤ (Y⁻¹) ^ 2 := by
    letI : Fintype (ResidueRing E s) := E.residueFinite s
    have hsSupport : qI s.1 / Y ∈ tsupport f :=
      subset_closure (Function.mem_support.mpr ((hP s).mp hs))
    have hq : 0 < qI s.1 := by
      have hlow : L ≤ qI s.1 / Y := (hinterval _ hsSupport).1
      have hqLower : L * Y ≤ qI s.1 := (le_div_iff₀ hYpos).mp hlow
      exact (mul_pos hL hYpos).trans_le hqLower
    have hcardRes : (Fintype.card (ResidueRing E s) : ℝ) = qI s.1 := by
      change (Fintype.card (ResidueRing E s) : ℝ) = (Ideal.absNorm s.1 : ℝ)
      exact_mod_cast E.residue_card s
    have hhalfSquare : (qI s.1 ^ (-(1 / 2 : ℝ))) ^ (2 : ℕ) = (qI s.1)⁻¹ := by
      calc
        _ = qI s.1 ^ ((-(1 / 2 : ℝ)) * 2) := by
          rw [Real.rpow_mul hq.le, Real.rpow_two]
        _ = _ := by norm_num [Real.rpow_neg_one]
    have hfactor : ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 =
        (Y⁻¹) ^ 2 * (qI s.1)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hYpos,
        abs_of_pos (Real.rpow_pos_of_pos hq _), mul_pow, hhalfSquare]
    have hterm (d : ResidueRing E s) :
        ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ρ s d‖ ^ 2 ≤
          (Y⁻¹) ^ 2 * (qI s.1)⁻¹ := by
      have hnorm : ‖ρ s d‖ ^ 2 ≤ 1 := by nlinarith [hρ s d, norm_nonneg (ρ s d)]
      calc
        _ = ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 * ‖ρ s d‖ ^ 2 := by
          rw [norm_mul, mul_pow]
        _ ≤ ‖(Y : ℂ)⁻¹ * ((qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
        _ = _ := by rw [mul_one, hfactor]
    rw [finsum_eq_sum_of_fintype]
    calc
      _ ≤ ∑ _ : ResidueRing E s, (Y⁻¹) ^ 2 * (qI s.1)⁻¹ :=
        Finset.sum_le_sum fun d _ => hterm d
      _ = (Fintype.card (ResidueRing E s) : ℝ) * ((Y⁻¹) ^ 2 * (qI s.1)⁻¹) := by simp
      _ = (Y⁻¹) ^ 2 := by rw [hcardRes]; field_simp
  calc
    _ ≤ ∑ _s ∈ P, (Y⁻¹) ^ 2 := Finset.sum_le_sum hresidue
    _ = (P.card : ℝ) * (Y⁻¹) ^ 2 := by simp
    _ ≤ (C * Y) * (Y⁻¹) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = C / Y := by field_simp

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
