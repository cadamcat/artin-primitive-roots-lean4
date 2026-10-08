import ArtinPrimitiveRoots.Ext.TypeIIInputs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

noncomputable def pd7dCharacterCoeff (k d : ℕ) [NeZero k]
    (f : (Fin d → (ZMod k)ˣ) → ℂ) (χ : Fin d → DirichletCharacter ℂ k) : ℂ :=
  (1 / (Nat.totient k : ℂ)) ^ d * ∑ u : Fin d → (ZMod k)ˣ,
    f u * ∏ i : Fin d, star (χ i (u i : ZMod k))

lemma pd7d_character_tensor_delta (k d : ℕ) [NeZero k] (hk : 0 < k)
    (u v : Fin d → (ZMod k)ˣ) :
    (∑ χ : Fin d → DirichletCharacter ℂ k,
      ∏ i : Fin d, (1 / (Nat.totient k : ℂ)) * star (χ i (u i : ZMod k)) * χ i (v i : ZMod k)) =
      if v = u then (1 : ℂ) else 0 := by
  rw [← Fintype.prod_sum (fun (i : Fin d) (χ : DirichletCharacter ℂ k) =>
    (1 / (Nat.totient k : ℂ)) * star (χ (u i : ZMod k)) * χ (v i : ZMod k))]
  have hcoord (i : Fin d) :
      (∑ χ : DirichletCharacter ℂ k,
        (1 / (Nat.totient k : ℂ)) * star (χ (u i : ZMod k)) * χ (v i : ZMod k)) =
      if v i = u i then (1 : ℂ) else 0 := by
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    have hh := ArtinPrimitiveRoots.Ext.TypeIIInputs.dirichlet_orthogonality k hk
      (u i : ZMod k) (v i : ZMod k) (u i).isUnit
    simpa only [Units.val_inj, mul_assoc] using hh.symm
  simp_rw [hcoord]
  by_cases hv : v = u
  · simp [hv]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ u i := by
      by_contra h
      apply hv
      funext i
      exact not_not.mp (not_exists.mp h i)
    rw [if_neg hv]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

lemma pd7d_character_expansion (k d : ℕ) [NeZero k] (hk : 0 < k)
    (f : (Fin d → (ZMod k)ˣ) → ℂ) (v : Fin d → (ZMod k)ˣ) :
    f v = ∑ χ : Fin d → DirichletCharacter ℂ k,
      pd7dCharacterCoeff k d f χ * ∏ i : Fin d, χ i (v i : ZMod k) := by
  have hscale : (1 / (Nat.totient k : ℂ)) ^ d =
      ∏ i : Fin d, (1 / (Nat.totient k : ℂ)) := by simp
  symm
  calc
    _ = ∑ χ : Fin d → DirichletCharacter ℂ k, ∑ u : Fin d → (ZMod k)ˣ,
        f u * ∏ i : Fin d,
          (1 / (Nat.totient k : ℂ)) * star (χ i (u i : ZMod k)) * χ i (v i : ZMod k) := by
      simp only [pd7dCharacterCoeff, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro u hu
      rw [hscale]
      simp only [Finset.prod_mul_distrib]
      ring
    _ = ∑ u : Fin d → (ZMod k)ˣ,
        f u * ∑ χ : Fin d → DirichletCharacter ℂ k, ∏ i : Fin d,
          (1 / (Nat.totient k : ℂ)) * star (χ i (u i : ZMod k)) * χ i (v i : ZMod k) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ u : Fin d → (ZMod k)ˣ, f u * (if v = u then (1 : ℂ) else 0) := by
      simp_rw [pd7d_character_tensor_delta k d hk]
    _ = f v := by simp [eq_comm]

lemma pd7dCharacterCoeff_norm_le_one (k d : ℕ) [NeZero k]
    (f : (Fin d → (ZMod k)ˣ) → ℂ) (χ : Fin d → DirichletCharacter ℂ k)
    (hf : ∀ u, ‖f u‖ ≤ 1) : ‖pd7dCharacterCoeff k d f χ‖ ≤ 1 := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have htot : 0 < (Nat.totient k : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk
  have hterm (u : Fin d → (ZMod k)ˣ) : ‖f u * ∏ i : Fin d, star (χ i (u i : ZMod k))‖ ≤ 1 := by
    have hp : ‖∏ i : Fin d, star (χ i (u i : ZMod k))‖ ≤ 1 := by
      rw [norm_prod]
      apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)).trans_eq
        (by simp : (∏ i : Fin d, (1 : ℝ)) = 1)
      simpa using (χ i).norm_le_one (u i : ZMod k)
    rw [norm_mul]
    exact (mul_le_mul (hf u) hp (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hcard : Fintype.card (Fin d → (ZMod k)ˣ) = (Nat.totient k) ^ d := by
    simp [Fintype.card_fun, ZMod.card_units_eq_totient]
  have hsum : ‖∑ u : Fin d → (ZMod k)ˣ, f u * ∏ i : Fin d, star (χ i (u i : ZMod k))‖ ≤
      (Nat.totient k : ℝ) ^ d := by
    calc
      _ ≤ ∑ u : Fin d → (ZMod k)ˣ, ‖f u * ∏ i : Fin d, star (χ i (u i : ZMod k))‖ := norm_sum_le _ _
      _ ≤ ∑ u : Fin d → (ZMod k)ˣ, (1 : ℝ) := Finset.sum_le_sum (fun u _ => hterm u)
      _ = _ := by simp [hcard]
  have hscale : ‖(1 / (Nat.totient k : ℂ)) ^ d‖ = (1 / (Nat.totient k : ℝ)) ^ d := by
    rw [norm_pow, norm_div, norm_one, Complex.norm_natCast]
  rw [pd7dCharacterCoeff, norm_mul, hscale]
  calc
    _ ≤ (1 / (Nat.totient k : ℝ)) ^ d * (Nat.totient k : ℝ) ^ d :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by rw [← mul_pow]; field_simp; simp

lemma pd7dCharacterCoeff_mass_le (k d : ℕ) [NeZero k]
    (f : (Fin d → (ZMod k)ˣ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    (∑ χ : Fin d → DirichletCharacter ℂ k, ‖pd7dCharacterCoeff k d f χ‖) ≤ (k : ℝ) ^ d := by
  have hcard : Fintype.card (DirichletCharacter ℂ k) = Nat.totient k := by
    simpa only [Nat.card_eq_fintype_card] using DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k
  calc
    _ ≤ ∑ χ : Fin d → DirichletCharacter ℂ k, (1 : ℝ) :=
      Finset.sum_le_sum (fun χ _ => pd7dCharacterCoeff_norm_le_one k d f χ hf)
    _ = (Nat.totient k : ℝ) ^ d := by simp [Fintype.card_fun, hcard]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.totient_le k) d

end ArtinPrimitiveRoots.TypeII.PD
