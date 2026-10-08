import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.CharacterExpansion
import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.MajorArcArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

lemma pd7d_additiveCharacter_add (u v : ℝ) :
    additiveCharacter (u + v) = additiveCharacter u * additiveCharacter v := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma pd7d_additiveCharacter_int (d : ℤ) : additiveCharacter (d : ℝ) = 1 := by
  unfold additiveCharacter
  have harg : Complex.I * (2 * Real.pi * (d : ℝ)) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [harg]
  exact Complex.exp_int_mul_two_pi_mul_I d

lemma pd7d_integer_phase_period (theta : ℝ) (z d : ℤ) :
    additiveCharacter ((theta + (z : ℝ)) * (d : ℝ)) = additiveCharacter (theta * (d : ℝ)) := by
  rw [add_mul, pd7d_additiveCharacter_add]
  have hh : additiveCharacter ((z : ℝ) * (d : ℝ)) = 1 := by
    simpa only [Int.cast_mul] using pd7d_additiveCharacter_int (z * d)
  rw [hh, mul_one]

lemma pd7d_integer_residue_phase (h d : ℤ) (k : ℕ) [NeZero k] :
    additiveCharacter ((h : ℝ) * (d : ℝ) / k) =
      additiveCharacter ((h : ℝ) * ((d : ZMod k).val : ℝ) / k) := by
  have hkp : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hrepInt : ((d : ZMod k).val : ℤ) + (k : ℤ) * (d / (k : ℤ)) = d := by
    rw [ZMod.val_intCast]
    exact Int.emod_add_mul_ediv d (k : ℤ)
  have hrep : ((d : ZMod k).val : ℝ) + (k : ℝ) * ((d / (k : ℤ) : ℤ) : ℝ) = (d : ℝ) := by
    exact_mod_cast hrepInt
  have harg : (h : ℝ) * (d : ℝ) / k =
      (h : ℝ) * ((d : ZMod k).val : ℝ) / k + ((h * (d / (k : ℤ)) : ℤ) : ℝ) := by
    rw [← hrep]
    push_cast
    field_simp
    <;> ring
  rw [harg, pd7d_additiveCharacter_add, pd7d_additiveCharacter_int, mul_one]

noncomputable def pd7dMajorResidue (k : ℕ) (u : Fin 6 → (ZMod k)ˣ) : ZMod k :=
  (u 0 : ZMod k) * u 1 * u 2 - (u 3 : ZMod k) * u 4 * u 5 - u 0 + u 3

noncomputable def pd7dMajorResiduePhase (h : ℤ) (k : ℕ) (u : Fin 6 → (ZMod k)ˣ) : ℂ :=
  additiveCharacter ((h : ℝ) * (pd7dMajorResidue k u).val / k)

lemma pd7dMajorResiduePhase_norm (h : ℤ) (k : ℕ) (u : Fin 6 → (ZMod k)ˣ) :
    ‖pd7dMajorResiduePhase h k u‖ = 1 := by
  unfold pd7dMajorResiduePhase additiveCharacter
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_re, Complex.div_im,
    zero_mul, mul_zero, zero_sub, sub_zero, zero_add, add_zero, Real.exp_zero]
  norm_num

lemma pd7d_major_residue_character_expansion (h : ℤ) (k : ℕ) [NeZero k]
    (u : Fin 6 → (ZMod k)ˣ) :
    pd7dMajorResiduePhase h k u = ∑ χ : Fin 6 → DirichletCharacter ℂ k,
      pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ * ∏ i : Fin 6, χ i (u i : ZMod k) :=
  pd7d_character_expansion k 6 (Nat.pos_of_ne_zero (NeZero.ne k)) _ u

lemma pd7d_major_residue_character_mass (h : ℤ) (k : ℕ) [NeZero k] :
    (∑ χ : Fin 6 → DirichletCharacter ℂ k,
      ‖pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ‖) ≤ (k : ℝ) ^ 6 :=
  pd7dCharacterCoeff_mass_le k 6 _ (fun u => (pd7dMajorResiduePhase_norm h k u).le)

end ArtinPrimitiveRoots.TypeII.PD
