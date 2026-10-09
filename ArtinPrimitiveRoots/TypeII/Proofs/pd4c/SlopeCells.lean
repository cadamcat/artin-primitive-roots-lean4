import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Geometry

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Floor-cell separation and normalized real separation differ by at most one. -/
theorem floor_cell_distance_comparison (H s t : ℝ) (hH : 0 < H) :
    |((⌊s/H⌋-⌊t/H⌋ : ℤ) : ℝ)| ≤ |s-t|/H+1 ∧
      |s-t| ≤ (|((⌊s/H⌋-⌊t/H⌋ : ℤ) : ℝ)|+1)*H := by
  have hslo := Int.floor_le (s/H)
  have hshi := Int.lt_floor_add_one (s/H)
  have htlo := Int.floor_le (t/H)
  have hthi := Int.lt_floor_add_one (t/H)
  have hquot : |s/H-t/H| = |s-t|/H := by rw [← sub_div, abs_div, abs_of_pos hH]
  have hleft : |(⌊s/H⌋ : ℝ)-(⌊t/H⌋ : ℝ)| ≤ |s/H-t/H|+1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self (s/H-t/H), neg_abs_le (s/H-t/H)]
  have hright : |s/H-t/H| ≤ |(⌊s/H⌋ : ℝ)-(⌊t/H⌋ : ℝ)|+1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self ((⌊s/H⌋ : ℝ)-(⌊t/H⌋ : ℝ)),
      neg_abs_le ((⌊s/H⌋ : ℝ)-(⌊t/H⌋ : ℝ))]
  rw [hquot] at hleft hright
  push_cast
  exact ⟨hleft, (div_le_iff₀ hH).mp hright⟩

/-- Bounded slope-cell separation gives a uniform pad-coordinate determinant bound. -/
theorem env_cell_pad_quotient_bound (S : PDScale) (w : ArchRoot)
    (z z' : ℤ × ℤ) (D : ℕ)
    (hU : 0 < S.U) (hw : w.InRegion S) (hz : envBox S w z) (hz' : envBox S w z')
    (hY : 0 < S.Y) (hd₀ : 0 < S.d₀) (hD : (S.d₀ : ℝ) ≤ (D : ℝ))
    (hdiv : (D : ℤ) ∣ det2 z z') (C : ℝ) (hC : 0 ≤ C)
    (hcell : |((⌊((z'.2 : ℝ)/w.tau z')/((S.d₀ : ℝ)*S.Y)⌋-
        ⌊((z.2 : ℝ)/w.tau z)/((S.d₀ : ℝ)*S.Y)⌋ : ℤ) : ℝ)| ≤ C) :
    |((det2 z z'/(D : ℤ) : ℤ) : ℝ)| ≤ 256*(C+1)*S.Y := by
  have hu : 0 < w.u := hU.trans_le hw.1
  have htau (u : ℤ × ℤ) (hbox : envBox S w u) : 0 < w.tau u ∧ w.tau u ≤ 16 := by
    have hpos : 0 < w.tau u := (mul_pos_iff_of_pos_left hu).mp (hU.trans_le hbox.1)
    refine ⟨hpos, (mul_le_mul_iff_right₀ hU).mp ?_⟩
    calc
      S.U*w.tau u ≤ w.u*w.tau u := mul_le_mul_of_nonneg_right hw.1 hpos.le
      _ ≤ S.U*16 := by simpa only [mul_comm] using hbox.2.1
  have htz := htau z hz
  have htz' := htau z' hz'
  have hd₀r : 0 < (S.d₀ : ℝ) := by exact_mod_cast hd₀
  have hDr : 0 < (D : ℝ) := hd₀r.trans_le hD
  have hH : 0 < (S.d₀ : ℝ)*S.Y := mul_pos hd₀r hY
  have hsep : |(z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z| ≤
      (C+1)*((S.d₀ : ℝ)*S.Y) := by
    calc
      _ ≤ _ := (floor_cell_distance_comparison ((S.d₀ : ℝ)*S.Y)
        ((z'.2 : ℝ)/w.tau z') ((z.2 : ℝ)/w.tau z) hH).2
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hcell]) hH.le
  have hid : (det2 z z' : ℝ) = (w.tau z*w.tau z')*
      ((z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z) := by
    calc
      _ = w.tau z*(z'.2 : ℝ)-w.tau z'*(z.2 : ℝ) := by
        dsimp only [det2, ArchRoot.tau]
        push_cast
        ring
      _ = _ := by field_simp [htz.1.ne', htz'.1.ne'] <;> ring
  have hprod : w.tau z*w.tau z' ≤ 256 := by
    calc
      _ ≤ (16 : ℝ)*16 := mul_le_mul htz.2 htz'.2 htz'.1.le (by norm_num)
      _ = _ := by norm_num
  have hdet : |(det2 z z' : ℝ)| ≤ (256*(C+1)*S.Y)*(D : ℝ) := by
    calc
      _ = (w.tau z*w.tau z')*|(z'.2 : ℝ)/w.tau z'-(z.2 : ℝ)/w.tau z| := by
        rw [hid, abs_mul, abs_of_pos (mul_pos htz.1 htz'.1)]
      _ ≤ 256*((C+1)*((S.d₀ : ℝ)*S.Y)) :=
        mul_le_mul hprod hsep (abs_nonneg _) (by norm_num)
      _ ≤ 256*((C+1)*((D : ℝ)*S.Y)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hY.le)
            (by linarith : 0 ≤ C+1)) (by norm_num)
      _ = _ := by ring
  have hcast := congrArg (fun n : ℤ => (n : ℝ)) (Int.mul_ediv_cancel' hdiv)
  push_cast at hcast
  have hquot : ((det2 z z'/(D : ℤ) : ℤ) : ℝ) = (det2 z z' : ℝ)/(D : ℝ) :=
    (eq_div_iff hDr.ne').mpr (by simpa only [mul_comm] using hcast)
  rw [hquot, abs_div, abs_of_pos hDr]
  exact (div_le_iff₀ hDr).mpr hdet

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
