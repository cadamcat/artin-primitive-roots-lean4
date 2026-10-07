import DedekindResidue.CompletedZeta.FEPair
import ArtinPrimitiveRoots.Hecke.Theta.FiniteFEPair

/-!
# Class-group character theta pairs

This is the ordinary ideal-class specialization of the ray-class theta route. It packages the
class theta functions from AINTLIB into a character-weighted functional-equation pair.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Filter Asymptotics
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField Topology Real

noncomputable section

namespace ArtinPrimitiveRoots.Hecke.Theta

open DedekindResidue

variable (K : Type*) [Field K] [NumberField K]

private theorem heckeGClass_sub_const_isBigO (C : ClassGroup (𝓞 K)) (r : ℝ) :
    (fun x : ℝ => heckeGClass K C x -
      (torsionOrder K : ℝ)⁻¹ * unitBoxVol K) =O[atTop] (fun x => x ^ r) := by
  obtain ⟨A, c, x₀, hA, hc, hx₀, hdev⟩ := exists_heckeGClass_dev_bound K C
  have hp : (0 : ℝ) < 1 / (Module.finrank ℚ K : ℝ) :=
    div_pos one_pos (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)))
  refine IsBigO.trans ?_ (isBigO_exp_neg_rpow hc hp r)
  rw [isBigO_iff]
  refine ⟨A, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hdev hx

/-- The half-weight functional-equation pair attached to one ordinary ideal class. -/
def classCharacterPair (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ where
  f := fun x => (heckeGClass K C x : ℂ)
  g := fun x => (heckeGClass K (dualClass K C) x : ℂ)
  k := 1 / 2
  ε := 1
  f₀ := (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)
  g₀ := (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeGClass K C)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_heckeGClass K (dualClass K C))).locallyIntegrableOn measurableSet_Ioi
  hk := by norm_num
  hε := one_ne_zero
  h_feq x hx := by
    have h := heckeGClass_inversion K C hx
    rw [Real.sqrt_eq_rpow] at h
    change (heckeGClass K C (1 / x) : ℂ) = _
    rw [h, smul_eq_mul]
    push_cast
    ring
  hf_top r := by
    have hbase := heckeGClass_sub_const_isBigO K C r
    rw [isBigO_iff] at hbase ⊢
    obtain ⟨A, hA⟩ := hbase
    refine ⟨A, ?_⟩
    filter_upwards [hA] with x hx
    calc
      ‖(heckeGClass K C x : ℂ) -
          (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)‖
          = ‖((heckeGClass K C x -
              (torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)‖ := by push_cast; ring_nf
      _ = ‖heckeGClass K C x -
          (torsionOrder K : ℝ)⁻¹ * unitBoxVol K‖ := Complex.norm_real _
      _ ≤ A * ‖x ^ r‖ := hx
  hg_top r := by
    have hbase := heckeGClass_sub_const_isBigO K (dualClass K C) r
    rw [isBigO_iff] at hbase ⊢
    obtain ⟨A, hA⟩ := hbase
    refine ⟨A, ?_⟩
    filter_upwards [hA] with x hx
    calc
      ‖(heckeGClass K (dualClass K C) x : ℂ) -
          (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)‖
          = ‖((heckeGClass K (dualClass K C) x -
              (torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)‖ := by push_cast; ring_nf
      _ = ‖heckeGClass K (dualClass K C) x -
          (torsionOrder K : ℝ)⁻¹ * unitBoxVol K‖ := Complex.norm_real _
      _ ≤ A * ‖x ^ r‖ := hx

/-- A nontrivial ordinary class-group character gives an entire completed theta combination. -/
theorem classCharacter_completed_entire (χ : ClassGroup (𝓞 K) →* ℂˣ) (hχ : χ ≠ 1) :
    Differentiable ℂ
      (finiteFEPair (1 / 2) (by norm_num)
        (classCharacterPair K) (fun _ => rfl) (fun C => (χ C : ℂ))).Λ := by
  apply finiteFEPair_character_differentiable χ hχ (classCharacterPair K)
    (1 / 2) (by norm_num) (fun _ => rfl)
    (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)
    (((torsionOrder K : ℝ)⁻¹ * unitBoxVol K : ℝ) : ℂ)
  · intro C
    simp [classCharacterPair]
  · intro C
    simp [classCharacterPair]

end ArtinPrimitiveRoots.Hecke.Theta

end
