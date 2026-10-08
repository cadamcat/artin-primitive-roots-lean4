import ArtinPrimitiveRoots.TypeII.Proofs.pd7d.MajorArcPhase

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

lemma pd7d_natural_residue_character_expansion (h : ℤ) (k : ℕ) [NeZero k]
    (z : Fin 6 → ℕ) (hz : ∀ i, IsUnit (z i : ZMod k)) :
    additiveCharacter ((h : ℝ) *
      (((z 0 : ℤ) * z 1 * z 2 - (z 3 : ℤ) * z 4 * z 5 - z 0 + z 3 : ℤ) : ℝ) / k) =
      ∑ χ : Fin 6 → DirichletCharacter ℂ k,
        pd7dCharacterCoeff k 6 (pd7dMajorResiduePhase h k) χ *
          ∏ i : Fin 6, χ i (z i : ZMod k) := by
  let u (i : Fin 6) : (ZMod k)ˣ := (hz i).unit
  have hu (i : Fin 6) : (u i : ZMod k) = (z i : ZMod k) := (hz i).unit_spec
  have hr : pd7dMajorResidue k u =
      (((z 0 : ℤ) * z 1 * z 2 - (z 3 : ℤ) * z 4 * z 5 - z 0 + z 3 : ℤ) : ZMod k) := by
    unfold pd7dMajorResidue
    simp only [hu, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [pd7d_integer_residue_phase]
  rw [← hr]
  change pd7dMajorResiduePhase h k u = _
  rw [pd7d_major_residue_character_expansion]
  simp only [hu]

lemma pd7d_six_character_product {k : ℕ} (χ : Fin 6 → DirichletCharacter ℂ k) (z : Fin 6 → ℕ) :
    (∏ i : Fin 6, χ i (z i : ZMod k)) =
      χ 0 (z 0 : ZMod k) * χ 1 (z 1 : ZMod k) * χ 2 (z 2 : ZMod k) *
        χ 3 (z 3 : ZMod k) * χ 4 (z 4 : ZMod k) * χ 5 (z 5 : ZMod k) := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero, Fin.val_succ,
    Fin.succ_zero_eq_one, mul_one]
  norm_num
  ring

end ArtinPrimitiveRoots.TypeII.PD
