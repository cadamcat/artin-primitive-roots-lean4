import ArtinPrimitiveRoots.TypeII.PD.RootReplacement
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PhysicalCoordinates

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

/-- Coordinates in the determinant-one completion matrix of the source state. -/
def physicalInverseCoordinates {K : ℕ} {F : PDFix K} {S : PDScale}
    (P : PState F S) (z : ℤ × ℤ) : ℤ × ℤ :=
  (P.completionD * z.1 - P.completionC * z.2,
    -(P.second : ℤ) * z.1 + (P.first : ℤ) * z.2)

def edgeCoordinates {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) : ℤ × ℤ := physicalInverseCoordinates P Q.pos

def archRootOfState {K : ℕ} {F : PDFix K} {S : PDScale} (P : PState F S) : ArchRoot :=
  ⟨(P.first : ℝ), (P.second : ℝ), stateRoot P⟩

theorem physicalInverseCoordinates_det {K : ℕ} {F : PDFix K} {S : PDScale}
    (P : PState F S) (z w : ℤ × ℤ) :
    det2 (physicalInverseCoordinates P z) (physicalInverseCoordinates P w) = det2 z w := by
  unfold physicalInverseCoordinates det2
  calc
    _ = ((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) *
        (z.1 * w.2 - z.2 * w.1) := by ring
    _ = _ := by rw [P.det_one, one_mul]

theorem edgeCoordinates_first_row {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) :
    (P.first : ℤ) * (edgeCoordinates P Q).1 +
      P.completionC * (edgeCoordinates P Q).2 = (Q.first : ℤ) := by
  unfold edgeCoordinates physicalInverseCoordinates PhysicalState.pos
  calc
    _ = ((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) *
        (Q.first : ℤ) := by ring
    _ = _ := by rw [P.det_one, one_mul]

theorem edgeCoordinates_second_row {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) :
    (P.second : ℤ) * (edgeCoordinates P Q).1 +
      P.completionD * (edgeCoordinates P Q).2 = (Q.second : ℤ) := by
  unfold edgeCoordinates physicalInverseCoordinates PhysicalState.pos
  calc
    _ = ((P.first : ℤ) * P.completionD - (P.second : ℤ) * P.completionC) *
        (Q.second : ℤ) := by ring
    _ = _ := by rw [P.det_one, one_mul]

theorem edgeCoordinates_second_eq_det {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) : (edgeCoordinates P Q).2 = det2 P.pos Q.pos := by
  simp only [edgeCoordinates, physicalInverseCoordinates, PhysicalState.pos, det2]
  ring

/-- Unimodular coordinate transport preserves primitivity. -/
theorem edgeCoordinates_primitive {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) : Int.gcd (edgeCoordinates P Q).1 (edgeCoordinates P Q).2 = 1 := by
  let z := edgeCoordinates P Q
  let w := physicalInverseCoordinates P (Q.completionC, Q.completionD)
  have hdet : det2 z w = 1 := by
    change det2 (physicalInverseCoordinates P Q.pos)
      (physicalInverseCoordinates P (Q.completionC, Q.completionD)) = 1
    rw [physicalInverseCoordinates_det]
    exact Q.det_one
  have hdiv : (Int.gcd z.1 z.2 : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left z.1 z.2) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right z.1 z.2) _)
  have hdivNat : Int.gcd z.1 z.2 ∣ 1 := by exact_mod_cast hdiv
  exact Nat.dvd_one.mp hdivNat

/-- A source's normalized root lies in the advertised root region. -/
theorem archRootOfState_inRegion {K : ℕ} {F : PDFix K} {S : PDScale}
    (P : PState F S) : (archRootOfState P).InRegion S := by
  have hPu : 0 < (P.first : ℝ) := by
    have h : (0 : ℤ) < P.first := lt_of_le_of_lt P.completion_range.1 P.completion_range.2
    exact_mod_cast h
  refine ⟨P.first_lower, ?_, P.second_lower, P.second_upper, ?_, ?_⟩
  · simpa only [archRootOfState, PDScale.U, mul_assoc] using P.first_upper
  · exact div_nonneg (Int.cast_nonneg P.completion_range.1) hPu.le
  · apply (div_le_one₀ hPu).mpr
    have h : (P.completionC : ℝ) < P.first := by exact_mod_cast P.completion_range.2
    exact h.le

/-- The target physical box is exactly the environment box in source coordinates. -/
theorem envBox_edgeCoordinates {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) : envBox S (archRootOfState P) (edgeCoordinates P Q) := by
  have hPu : 0 < (P.first : ℝ) := by
    have h : (0 : ℤ) < P.first := lt_of_le_of_lt P.completion_range.1 P.completion_range.2
    exact_mod_cast h
  have hfirst : (P.first : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) =
      (Q.first : ℝ) := by
    have hrow : (P.first : ℝ) * ((edgeCoordinates P Q).1 : ℝ) +
        (P.completionC : ℝ) * ((edgeCoordinates P Q).2 : ℝ) = (Q.first : ℝ) := by
      exact_mod_cast edgeCoordinates_first_row P Q
    dsimp only [archRootOfState, ArchRoot.tau, stateRoot]
    calc
      _ = (P.first : ℝ) * ((edgeCoordinates P Q).1 : ℝ) +
          (P.completionC : ℝ) * ((edgeCoordinates P Q).2 : ℝ) := by
        field_simp [hPu.ne']
        <;> ring
      _ = _ := hrow
  have hsecond :
      (P.second : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) +
          ((edgeCoordinates P Q).2 : ℝ) / (P.first : ℝ) = (Q.second : ℝ) := by
    have hrow : (P.second : ℝ) * ((edgeCoordinates P Q).1 : ℝ) +
        (P.completionD : ℝ) * ((edgeCoordinates P Q).2 : ℝ) = (Q.second : ℝ) := by
      exact_mod_cast edgeCoordinates_second_row P Q
    have hdet : (P.first : ℝ) * (P.completionD : ℝ) -
        (P.second : ℝ) * (P.completionC : ℝ) = 1 := by exact_mod_cast P.det_one
    dsimp only [archRootOfState, ArchRoot.tau, stateRoot]
    field_simp [hPu.ne']
    linear_combination (P.first : ℝ) * hrow - ((edgeCoordinates P Q).2 : ℝ) * hdet
  change S.U ≤ (P.first : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) ∧
    (P.first : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) ≤ 16 * S.U ∧
    S.V ≤ (P.second : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) +
        ((edgeCoordinates P Q).2 : ℝ) / (P.first : ℝ) ∧
    (P.second : ℝ) * ((archRootOfState P).tau (edgeCoordinates P Q)) +
        ((edgeCoordinates P Q).2 : ℝ) / (P.first : ℝ) ≤ 2 * S.V
  rw [hfirst, hsecond]
  refine ⟨Q.first_lower, ?_, Q.second_lower, Q.second_upper⟩
  simpa only [PDScale.U, mul_assoc] using Q.first_upper

private theorem pd6b_zmod_coords_not_both_zero (p : ℕ) (hp : p.Prime) (z : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) :
    (z.1 : ZMod p) ≠ 0 ∨ (z.2 : ZMod p) ≠ 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra h
  push_neg at h
  have hdiv1 : (p : ℤ) ∣ z.1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.1
  have hdiv2 : (p : ℤ) ∣ z.2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.2
  have hg : (p : ℤ) ∣ Int.gcd z.1 z.2 := dvd_gcd hdiv1 hdiv2
  have hzCast : ((Int.gcd z.1 z.2 : ℕ) : ℤ) = 1 := by exact_mod_cast hz
  have hdiv : (p : ℤ) ∣ 1 := by
    exact hzCast ▸ hg
  apply hp.not_dvd_one
  exact_mod_cast hdiv

theorem projectiveLine_eq_of_det_dvd (p : ℕ) (hp : p.Prime) (z z' : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hdet : (p : ℤ) ∣ det2 z z') : projLine p z = projLine p z' := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hdetmod :
      (z.1 : ZMod p) * (z'.2 : ZMod p) -
        (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
    rcases hdet with ⟨n, hn⟩
    have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hn
    simpa [det2] using hcast
  have hdetEq :
      (z.1 : ZMod p) * (z'.2 : ZMod p) =
        (z.2 : ZMod p) * (z'.1 : ZMod p) := sub_eq_zero.mp hdetmod
  by_cases hz2 : (z.2 : ZMod p) = 0
  · have hz1ne : (z.1 : ZMod p) ≠ 0 := by
      rcases pd6b_zmod_coords_not_both_zero p hp z hz with h1 | h2
      · exact h1
      · exact (h2 hz2).elim
    have hz'2 : (z'.2 : ZMod p) = 0 := by
      have hprod : (z.1 : ZMod p) * (z'.2 : ZMod p) = 0 := by
        simpa [hz2] using hdetmod
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact (hz1ne h1).elim
      · exact h2
    simp [projLine, hz2, hz'2]
  · have hz2ne : (z.2 : ZMod p) ≠ 0 := hz2
    have hz'2ne : (z'.2 : ZMod p) ≠ 0 := by
      intro hzero
      have hprod : (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
        have h := hdetEq
        rw [hzero] at h
        simpa using h.symm
      rcases mul_eq_zero.mp hprod with h2 | h1
      · exact (hz2ne h2).elim
      · have hcoords := pd6b_zmod_coords_not_both_zero p hp z' hz'
        rcases hcoords with hleft | hright
        · exact (hleft h1).elim
        · exact (hright hzero).elim
    have hratio :
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
          (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
      calc
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
            ((z.1 : ZMod p) * (z'.2 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
        _ = ((z.2 : ZMod p) * (z'.1 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by rw [hdetEq]
        _ = (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
    simp [projLine, hz2, hz'2ne, hratio]

/-- The first-row kernel vector is primitive because its complementary row has determinant one. -/
theorem physicalKernel_primitive {K : ℕ} {F : PDFix K} {S : PDScale}
    (P : PState F S) : Int.gcd P.completionC (-(P.first : ℤ)) = 1 := by
  let z : ℤ × ℤ := (P.completionC, -(P.first : ℤ))
  let w : ℤ × ℤ := (P.completionD, -(P.second : ℤ))
  have hdet : det2 z w = 1 := by
    dsimp [det2, z, w]
    nlinarith [P.det_one]
  have hdiv : (Int.gcd z.1 z.2 : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_left (Int.gcd_dvd_left z.1 z.2) _)
      (dvd_mul_of_dvd_left (Int.gcd_dvd_right z.1 z.2) _)
  have hdivNat : Int.gcd z.1 z.2 ∣ 1 := by exact_mod_cast hdiv
  exact Nat.dvd_one.mp hdivNat

/-- A prime dividing the target first coordinate prescribes its line in source coordinates. -/
theorem physicalKernel_eq_target_projection {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q : PState F S) (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Q.first) :
    projLine p (P.completionC, -(P.first : ℤ)) = projLine p (edgeCoordinates P Q) := by
  apply projectiveLine_eq_of_det_dvd p hp _ _ (physicalKernel_primitive P)
    (edgeCoordinates_primitive P Q)
  have hdet : det2 (P.completionC, -(P.first : ℤ)) (edgeCoordinates P Q) = Q.first := by
    unfold det2
    calc
      _ = (P.first : ℤ) * (edgeCoordinates P Q).1 +
          P.completionC * (edgeCoordinates P Q).2 := by ring
      _ = _ := edgeCoordinates_first_row P Q
  rw [hdet]
  exact_mod_cast hdiv

/-- The source is the fixed vector e₁ in its own completion coordinates. -/
theorem transportedRatio_e1 (w : ArchRoot) : transportedRatio w (1, 0) = w.r := by
  have hA : Int.gcdA (1 : ℤ) 0 = 1 := by
    simpa [Int.gcdA] using (Nat.gcdA_zero_right (s := 1) (by norm_num))
  have hB : Int.gcdB (1 : ℤ) 0 = 0 := by
    simpa [Int.gcdB] using (Nat.gcdB_zero_right (s := 1) (by norm_num))
  simp [transportedRatio, complementVec, ArchRoot.tau, hA, hB]

theorem envBox_e1 (S : PDScale) (w : ArchRoot) :
    envBox S w (1, 0) ↔ S.U ≤ w.u ∧ w.u ≤ 16 * S.U ∧ S.V ≤ w.v ∧ w.v ≤ 2 * S.V := by
  simp [envBox, ArchRoot.tau]

theorem envGood_e1 {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (p : PrimeLists S.x K) :
    envGood F S w ((1, 0), p) ↔ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a p w.r := by
  simp only [envGood, transportedRatio_e1]

/-- A target position is uniquely determined by its source and inverse coordinates. -/
theorem physicalTarget_eq_of_edgeCoordinates {K : ℕ} {F : PDFix K} {S : PDScale}
    (P Q Q' : PState F S) (hcoords : edgeCoordinates P Q = edgeCoordinates P Q')
    (hlabels : Q.labels = Q'.labels) : Q = Q' := by
  have hfirst : Q.first = Q'.first := by
    have hQ := edgeCoordinates_first_row P Q
    have hQ' := edgeCoordinates_first_row P Q'
    rw [hcoords] at hQ
    have hZ : (Q.first : ℤ) = Q'.first := hQ.symm.trans hQ'
    exact_mod_cast hZ
  have hsecond : Q.second = Q'.second := by
    have hQ := edgeCoordinates_second_row P Q
    have hQ' := edgeCoordinates_second_row P Q'
    rw [hcoords] at hQ
    have hZ : (Q.second : ℤ) = Q'.second := hQ.symm.trans hQ'
    exact_mod_cast hZ
  exact physicalState_eq_of_coordinates Q Q' hfirst hsecond hlabels


end
end ArtinPrimitiveRoots.TypeII.PD
