import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
set_option autoImplicit false

lemma pd7d_weighted_prod_difference (D e : ℝ) (hD : 1 ≤ D) (he : 0 ≤ e) :
    ∀ n : ℕ, ∀ a b w : Fin n → ℝ,
      (∀ i, 0 ≤ w i) → (∀ i, |a i| ≤ D * w i) → (∀ i, |b i| ≤ D * w i) →
      (∀ i, |a i - b i| ≤ e * w i) →
      |(∏ i : Fin n, a i) - ∏ i : Fin n, b i| ≤ (n : ℝ) * e * D ^ n * ∏ i : Fin n, w i := by
  have hD0 : 0 ≤ D := by linarith
  intro n
  induction n with
  | zero => intro a b w hw ha hb hd; simp
  | succ n ih =>
    intro a b w hw ha hb hd
    let W := ∏ i : Fin n, w i.succ
    have hW : 0 ≤ W := Finset.prod_nonneg (fun i _ => hw i.succ)
    have htail : |(∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ| ≤
        (n : ℝ) * e * D ^ n * W :=
      ih (Fin.tail a) (Fin.tail b) (Fin.tail w) (fun i => hw i.succ)
        (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hd i.succ)
    have hprodA : |∏ i : Fin n, a i.succ| ≤ D ^ n * W := by
      rw [← Real.norm_eq_abs, norm_prod]
      calc
        _ ≤ ∏ i : Fin n, D * w i.succ := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i hi
          simpa only [Real.norm_eq_abs] using ha i.succ
        _ = _ := by rw [Finset.prod_mul_distrib]; simp [W]
    have hpow : D ^ n ≤ D ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hD0 n]
    have hfirst : |a 0 - b 0| * |∏ i : Fin n, a i.succ| ≤
        e * D ^ (n + 1) * (w 0 * W) := by
      calc
        _ ≤ (e * w 0) * (D ^ n * W) :=
          mul_le_mul (hd 0) hprodA (abs_nonneg _) (mul_nonneg he (hw 0))
        _ ≤ (e * w 0) * (D ^ (n + 1) * W) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hW) (mul_nonneg he (hw 0))
        _ = _ := by ring
    have hsecond : |b 0| * |(∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ| ≤
        (n : ℝ) * e * D ^ (n + 1) * (w 0 * W) := by
      calc
        _ ≤ (D * w 0) * ((n : ℝ) * e * D ^ n * W) :=
          mul_le_mul (hb 0) htail (abs_nonneg _) (mul_nonneg hD0 (hw 0))
        _ = _ := by rw [pow_succ]; ring
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
    have hsplit : a 0 * (∏ i : Fin n, a i.succ) - b 0 * (∏ i : Fin n, b i.succ) =
        (a 0 - b 0) * (∏ i : Fin n, a i.succ) +
          b 0 * ((∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ) := by ring
    rw [hsplit]
    calc
      _ ≤ |(a 0 - b 0) * (∏ i : Fin n, a i.succ)| +
          |b 0 * ((∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ)| := by
        simpa only [Real.norm_eq_abs] using norm_add_le
          ((a 0 - b 0) * (∏ i : Fin n, a i.succ))
          (b 0 * ((∏ i : Fin n, a i.succ) - ∏ i : Fin n, b i.succ))
      _ ≤ e * D ^ (n + 1) * (w 0 * W) + (n : ℝ) * e * D ^ (n + 1) * (w 0 * W) := by
        rw [abs_mul, abs_mul]
        exact add_le_add hfirst hsecond
      _ = _ := by push_cast; dsimp [W]; ring

end ArtinPrimitiveRoots.TypeII.PD
