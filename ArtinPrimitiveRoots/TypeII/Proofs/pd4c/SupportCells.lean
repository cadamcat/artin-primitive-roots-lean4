import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SlopeCells
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.SignedMultiplier

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Pad-edge cell distances depend linearly on the fixed determinant-support radius. -/
theorem env_edge_cell_distance_bound (S : PDScale) (w : ArchRoot)
    (z z' : ℤ × ℤ) (D : ℕ) (Rpsi : ℝ) (hRpsi : 0 ≤ Rpsi)
    (hU : 0 < S.U) (hw : w.InRegion S) (hz : envBox S w z) (hz' : envBox S w z')
    (hY : 0 < S.Y) (hd₀ : 0 < S.d₀)
    (hpad : IsPadAdmissible S.d₀ D (det2 z z'))
    (hsupport : |((det2 z z'/(D : ℤ) : ℤ) : ℝ)| ≤ Rpsi*S.Y) :
    |((⌊((z'.2 : ℝ)/w.tau z')/((S.d₀ : ℝ)*S.Y)⌋-
        ⌊((z.2 : ℝ)/w.tau z)/((S.d₀ : ℝ)*S.Y)⌋ : ℤ) : ℝ)| ≤ 512*Rpsi+1 := by
  have hu : 0 < w.u := hU.trans_le hw.1
  have htau (u : ℤ × ℤ) (hbox : envBox S w u) : (1/16 : ℝ) ≤ w.tau u := by
    apply (mul_le_mul_iff_right₀ hu).mp
    have hlow : w.u*(1/16 : ℝ) ≤ S.U := by linarith [hw.2.1]
    exact hlow.trans hbox.1
  have htz : 0 < w.tau z := lt_of_lt_of_le (by norm_num) (htau z hz)
  have htz' : 0 < w.tau z' := lt_of_lt_of_le (by norm_num) (htau z' hz')
  have hprod : (1/256 : ℝ) ≤ w.tau z*w.tau z' := by
    calc
      _ = (1/16 : ℝ)*(1/16 : ℝ) := by norm_num
      _ ≤ _ := mul_le_mul (htau z hz) (htau z' hz') (by norm_num) htz.le
  have hprodpos : 0 < w.tau z*w.tau z' := mul_pos htz htz'
  have hd₀r : 0 < (S.d₀ : ℝ) := by exact_mod_cast hd₀
  have hDr : 0 < (D : ℝ) := hd₀r.trans_le hpad.1
  have hH : 0 < (S.d₀ : ℝ)*S.Y := mul_pos hd₀r hY
  have hcast := congrArg (fun n : ℤ => (n : ℝ)) (Int.mul_ediv_cancel' hpad.2.2)
  push_cast at hcast
  have hdet : |(det2 z z' : ℝ)| ≤ (2*Rpsi)*((S.d₀ : ℝ)*S.Y) := by
    calc
      _ = (D : ℝ)*|((det2 z z'/(D : ℤ) : ℤ) : ℝ)| := by
        rw [← hcast, abs_mul, abs_of_pos hDr]
      _ ≤ (D : ℝ)*(Rpsi*S.Y) := mul_le_mul_of_nonneg_left hsupport hDr.le
      _ ≤ (2*(S.d₀ : ℝ))*(Rpsi*S.Y) :=
        mul_le_mul_of_nonneg_right hpad.2.1.le (by positivity)
      _ = _ := by ring
  have hid : (det2 z z' : ℝ) = (w.tau z*w.tau z')*
      ((z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z) := by
    calc
      _ = w.tau z*(z'.2 : ℝ)-w.tau z'*(z.2 : ℝ) := by
        dsimp only [det2, ArchRoot.tau]
        push_cast
        ring
      _ = _ := by field_simp [htz.ne', htz'.ne'] <;> ring
  have hsep : |(z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z| ≤
      (512*Rpsi)*((S.d₀ : ℝ)*S.Y) := by
    calc
      _ = |(det2 z z' : ℝ)|/(w.tau z*w.tau z') := by
        rw [hid, abs_mul, abs_of_pos hprodpos]
        field_simp [hprodpos.ne']
      _ ≤ |(det2 z z' : ℝ)|/(1/256 : ℝ) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hprod
      _ = 256*|(det2 z z' : ℝ)| := by ring
      _ ≤ 256*((2*Rpsi)*((S.d₀ : ℝ)*S.Y)) := mul_le_mul_of_nonneg_left hdet (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ |(z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z|/((S.d₀ : ℝ)*S.Y)+1 :=
      (floor_cell_distance_comparison ((S.d₀ : ℝ)*S.Y)
        ((z'.2 : ℝ)/w.tau z') ((z.2 : ℝ)/w.tau z) hH).1
    _ ≤ 512*Rpsi+1 := by
      have hquot := (div_le_iff₀ hH).mpr hsep
      linarith only [hquot]
    _ = _ := by norm_num


/-- Actual clean multipliers have a fixed cell radius for every valid compact arc cutoff. -/
theorem geometric_multiplier_cell_distance_bound {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ Ccell : ℝ, 0 ≤ Ccell ∧
      ∀ (S : PDScale) (w : ArchRoot) (z z' : ℤ × ℤ) (D aa bb : ℕ),
      0 < S.U → w.InRegion S → envBox S w z → envBox S w z' →
      0 < S.Y → 0 < S.d₀ → IsPadAdmissible S.d₀ D (det2 z z') →
      geometricMultiplier F S D aa bb (det2 z z'/(D : ℤ)) ≠ 0 →
      |((⌊((z'.2 : ℝ)/w.tau z')/((S.d₀ : ℝ)*S.Y)⌋-
          ⌊((z.2 : ℝ)/w.tau z)/((S.d₀ : ℝ)*S.Y)⌋ : ℤ) : ℝ)| ≤ Ccell := by
  obtain ⟨Rpsi, hRpsi, hpsi⟩ := pd1c_arc_cutoff_support_bound F hF
  have hRpsi0 : 0 ≤ Rpsi := (by norm_num : (0 : ℝ) ≤ 4).trans hRpsi
  refine ⟨512*Rpsi+1, by positivity, ?_⟩
  intro S w z z' D aa bb hU hw hz hz' hY hd₀ hpad hne
  have hnonzero : F.psi (((det2 z z'/(D : ℤ) : ℤ) : ℝ)/S.Y) ≠ 0 := by
    intro hzero
    apply hne
    rw [geometric_multiplier_minor_formula, hzero]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul]
  have hnormal := hpsi _ hnonzero
  rw [abs_div, abs_of_pos hY] at hnormal
  have hsupport : |((det2 z z'/(D : ℤ) : ℤ) : ℝ)| ≤ Rpsi*S.Y :=
    (div_le_iff₀ hY).mp hnormal
  exact env_edge_cell_distance_bound S w z z' D Rpsi hRpsi0 hU hw hz hz' hY hd₀ hpad hsupport

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
