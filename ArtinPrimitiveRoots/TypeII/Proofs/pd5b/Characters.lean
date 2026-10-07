import ArtinPrimitiveRoots.TypeII.PD.Memory
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Finite additive-character orthogonality, with natural representatives below the modulus.
This lets a finite family of phases express equality of two prime birth labels exactly. -/
theorem pd5b_finite_birth_orthogonality {T p q : ℕ} [NeZero T]
    (hp : p < T) (hq : q < T) :
    (T : ℂ)⁻¹ * ∑ θ : ZMod T,
      ZMod.stdAddChar (θ * ((p : ZMod T) - (q : ZMod T))) =
        if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [NeZero.ne T]
  · have hd : (p : ZMod T) - (q : ZMod T) ≠ 0 := by
      intro hd
      have heq := sub_eq_zero.mp hd
      have hval := congrArg (fun z : ZMod T => z.val) heq
      rw [ZMod.val_natCast_of_lt hp, ZMod.val_natCast_of_lt hq] at hval
      exact hpq hval
    have hs : (∑ θ : ZMod T,
        ZMod.stdAddChar (((p : ZMod T) - (q : ZMod T)) * θ)) = 0 :=
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar T hd)
    simp_rw [mul_comm] at hs
    rw [hs]
    simp [hpq]

/-- The additive character takes values on the unit circle. -/
theorem pd5b_finite_birth_character_norm {T : ℕ} [NeZero T] (t : ZMod T) :
    ‖ZMod.stdAddChar t‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle t).norm_coe

/-- A coordinatewise finite sum factors over a finite product of choices. -/
private theorem pd5b_sum_pi_prod {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (g : ι → α → ℂ) :
    (∑ f : ι → α, ∏ i, g i (f i)) = ∏ i, ∑ a, g i a := by
  classical
  rw [← Fintype.piFinset_univ]
  exact Finset.sum_prod_piFinset Finset.univ g

/-- Independent additive phases enforce a finite list of exact equalities. -/
theorem pd5b_product_character_average {ι : Type*} {T : ℕ}
    [Fintype ι] [DecidableEq ι] [NeZero T] (d : ι → ZMod T) :
    ((Fintype.card (ι → ZMod T) : ℂ)⁻¹) *
      ∑ θ : ι → ZMod T,
        ∏ i, ZMod.stdAddChar (θ i * d i) =
      ∏ i, if d i = 0 then (1 : ℂ) else 0 := by
  classical
  have hsum :
      (∑ θ : ι → ZMod T,
        ∏ i, ZMod.stdAddChar (θ i * d i)) =
        ∏ i, ∑ t : ZMod T, ZMod.stdAddChar (t * d i) := by
    exact pd5b_sum_pi_prod (fun i t => ZMod.stdAddChar (t * d i))
  have hcoord (i : ι) :
      (∑ t : ZMod T, ZMod.stdAddChar (t * d i)) =
        (T : ℂ) * (if d i = 0 then 1 else 0) := by
    by_cases hd : d i = 0
    · simp [hd, NeZero.ne T]
    · have hzero := AddChar.sum_eq_zero_of_ne_one
        (ZMod.isPrimitive_stdAddChar T hd)
      simpa [hd, AddChar.mulShift_apply, mul_comm] using hzero
  have hT : (T : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne T
  have hCard : (Fintype.card (ι → ZMod T) : ℂ) =
      (T : ℂ) ^ Fintype.card ι := by
    simp
  have hprod (f : ι → ℂ) :
      (∏ i, (T : ℂ) * f i) = (T : ℂ) ^ Fintype.card ι * ∏ i, f i := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [hsum]
  simp_rw [hcoord]
  rw [hprod]
  rw [← hCard]
  have hpow : (Fintype.card (ι → ZMod T) : ℂ) ≠ 0 := by
    rw [hCard]
    exact pow_ne_zero _ hT
  field_simp [hpow]

/-- The same product orthogonality when a missing coordinate makes its phase zero. -/
theorem pd5b_product_character_average_option {ι : Type*} {T : ℕ}
    [Fintype ι] [DecidableEq ι] [NeZero T] (d : ι → Option (ZMod T)) :
    ((Fintype.card (ι → ZMod T) : ℂ)⁻¹) *
      ∑ θ : ι → ZMod T,
        ∏ i, (match d i with
          | some t => ZMod.stdAddChar (θ i * t)
          | none => 0) =
      ∏ i, if d i = some 0 then (1 : ℂ) else 0 := by
  classical
  by_cases hMissing : ∃ i, d i = none
  · obtain ⟨i, hi⟩ := hMissing
    have hsumZero :
        (∑ θ : ι → ZMod T,
          ∏ j, (match d j with
            | some t => ZMod.stdAddChar (θ j * t)
            | none => 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro θ hθ
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    have hprodZero :
        (∏ j, if d j = some 0 then (1 : ℂ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    simp [hsumZero, hprodZero]
  · have hsome (i : ι) : ∃ t, d i = some t := by
      cases hdi : d i with
      | none => exact (hMissing ⟨i, hdi⟩).elim
      | some t => exact ⟨t, rfl⟩
    choose q hq using hsome
    have hsum :
        (∑ θ : ι → ZMod T,
          ∏ i, (match d i with
            | some t => ZMod.stdAddChar (θ i * t)
            | none => 0)) =
          ∑ θ : ι → ZMod T,
            ∏ i, ZMod.stdAddChar (θ i * q i) := by
      apply Finset.sum_congr rfl
      intro θ hθ
      apply Finset.prod_congr rfl
      intro i hi
      rw [hq i]
    have hprod :
        (∏ i, if d i = some 0 then (1 : ℂ) else 0) =
          ∏ i, if q i = 0 then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hq i]
      simp
    calc
      _ = ((Fintype.card (ι → ZMod T) : ℂ)⁻¹) *
          ∑ θ : ι → ZMod T, ∏ i, ZMod.stdAddChar (θ i * q i) := by rw [hsum]
      _ = ∏ i, if q i = 0 then (1 : ℂ) else 0 :=
        pd5b_product_character_average q
      _ = _ := hprod.symm

end

end ArtinPrimitiveRoots.TypeII.PD
