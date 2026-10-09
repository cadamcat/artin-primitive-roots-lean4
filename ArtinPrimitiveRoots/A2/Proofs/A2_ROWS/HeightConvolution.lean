import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Measure
import ArtinPrimitiveRoots.A2.Poisson.Missing

set_option autoImplicit false

open MeasureTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2Rows

open Real Set Filter

private lemma integrable_gaussian_height_moment (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun x : ℝ => exp (-x ^ 2) * (1 + |x|) ^ p) := by
  let g : ℝ → ℝ := fun x => exp (-x ^ 2) * (1 + |x|) ^ p
  have hgauss : IntegrableOn (fun x : ℝ => exp (-x ^ 2)) (Ioi 0) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ))).integrableOn
  have hpowgauss : IntegrableOn (fun x : ℝ => x ^ p * exp (-x ^ 2)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1)
      (by norm_num : 0 < (1 : ℝ)) (s := p) (by linarith : -1 < p))
  have hbase : IntegrableOn (fun x : ℝ => exp (-x ^ 2) * (1 + x ^ p)) (Ioi 0) := by
    have h := hgauss.add hpowgauss
    have heq : (fun x : ℝ => exp (-x ^ 2) * (1 + x ^ p)) =
        (fun x => exp (-x ^ 2)) + (fun x => x ^ p * exp (-x ^ 2)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    exact heq ▸ h
  have hpow (x : ℝ) : (1 + |x|) ^ p ≤ 2 ^ p * (1 + |x| ^ p) := by
    by_cases hx : |x| ≤ 1
    · calc
        (1 + |x|) ^ p ≤ 2 ^ p :=
          Real.rpow_le_rpow (by positivity) (by linarith) hp
        _ ≤ 2 ^ p * (1 + |x| ^ p) := by
          calc
            2 ^ p = 2 ^ p * 1 := by ring
            _ ≤ 2 ^ p * (1 + |x| ^ p) :=
              mul_le_mul_of_nonneg_left
                (by nlinarith [Real.rpow_nonneg (abs_nonneg x) p])
                (Real.rpow_nonneg (by norm_num) p)
    · have hx1 : 1 ≤ |x| := le_of_not_ge hx
      calc
        (1 + |x|) ^ p ≤ (2 * |x|) ^ p :=
          Real.rpow_le_rpow (by positivity) (by linarith) hp
        _ = 2 ^ p * |x| ^ p := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg x)]
        _ ≤ 2 ^ p * (1 + |x| ^ p) :=
          mul_le_mul_of_nonneg_left (by nlinarith [Real.rpow_nonneg (abs_nonneg x) p])
            (Real.rpow_nonneg (by norm_num) p)
  have hbase' : IntegrableOn
      (fun x : ℝ => 2 ^ p * (exp (-x ^ 2) * (1 + x ^ p))) (Ioi 0) := by
    change Integrable (fun x : ℝ => 2 ^ p * (exp (-x ^ 2) * (1 + x ^ p)))
      (volume.restrict (Ioi 0))
    simpa only [smul_eq_mul] using hbase.const_mul (2 ^ p)
  have hmajor : IntegrableOn
      (fun x : ℝ => 2 ^ p * (exp (-x ^ 2) * (1 + |x| ^ p))) (Ioi 0) := by
    apply hbase'.congr_fun
    · intro x hx
      have hxpos : 0 < x := mem_Ioi.mp hx
      change 2 ^ p * (exp (-x ^ 2) * (1 + x ^ p)) =
        2 ^ p * (exp (-x ^ 2) * (1 + |x| ^ p))
      rw [abs_of_pos hxpos]
    · exact measurableSet_Ioi
  have hpos : IntegrableOn g (Ioi 0) := by
    refine Integrable.mono' hmajor ?_ ?_
    · exact (by fun_prop : Continuous g).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hpoint : exp (-x ^ 2) * (1 + |x|) ^ p ≤
          2 ^ p * (exp (-x ^ 2) * (1 + |x| ^ p)) := by
        calc
          exp (-x ^ 2) * (1 + |x|) ^ p ≤ exp (-x ^ 2) * (2 ^ p * (1 + |x| ^ p)) :=
            mul_le_mul_of_nonneg_left (hpow x) (exp_pos _).le
          _ = 2 ^ p * (exp (-x ^ 2) * (1 + |x| ^ p)) := by ring
      have hleft : 0 ≤ g x := by positivity
      have hright : 0 ≤ 2 ^ p * (exp (-x ^ 2) * (1 + |x| ^ p)) := by positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hpoint
  have hneg : IntegrableOn g (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa [g, Function.comp_def] using hpos
  have hpos0 : IntegrableOn g (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos
  have hall : Integrable g := by
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    exact ⟨hneg, hpos0⟩
  simpa [g] using hall

private lemma gaussian_height_transfer (p T v : ℝ) (hp : 0 < p) :
    (1 + |v|) ^ (-p) ≤ (1 + |T|) ^ (-p) * (1 + |T + v|) ^ p := by
  have htriangle : 1 + |T| ≤ (1 + |T + v|) * (1 + |v|) := by
    have hT : |T| ≤ |T + v| + |v| := by
      calc
        |T| = |(T + v) + (-v)| := by congr 1 <;> ring
        _ ≤ |T + v| + |-v| := abs_add_le _ _
        _ = |T + v| + |v| := by rw [abs_neg]
    nlinarith [mul_nonneg (abs_nonneg (T + v)) (abs_nonneg v)]
  have hpow := Real.rpow_le_rpow (by positivity) htriangle hp.le
  rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |v|) p,
    Real.rpow_neg (by positivity : 0 ≤ 1 + |T|) p]
  have hTpos : 0 < (1 + |T|) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hbpos : 0 < (1 + |T + v|) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hvpos : 0 < (1 + |v|) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hinv : 1 / ((1 + |T + v|) ^ p * (1 + |v|) ^ p) ≤
      1 / (1 + |T|) ^ p :=
    (one_div_le_one_div (mul_pos hbpos hvpos) hTpos).2 hpow
  have hscaled := mul_le_mul_of_nonneg_left hinv hbpos.le
  have hcancel : ((1 + |v|) ^ p)⁻¹ =
      (1 + |T + v|) ^ p * ((1 + |T + v|) ^ p * (1 + |v|) ^ p)⁻¹ := by
    field_simp [ne_of_gt hbpos, ne_of_gt hvpos]
  calc
    ((1 + |v|) ^ p)⁻¹ =
        (1 + |T + v|) ^ p * ((1 + |T + v|) ^ p * (1 + |v|) ^ p)⁻¹ := hcancel
    _ ≤ (1 + |T + v|) ^ p * (1 / (1 + |T|) ^ p) := by simpa [one_div] using hscaled
    _ = ((1 + |T|) ^ p)⁻¹ * (1 + |T + v|) ^ p := by rw [one_div]; ring

theorem zf_height_convolution_proof : ∀ A1 : ℝ, 0 < A1 → ∃ A0 C : ℝ, 1 < A0 ∧ 0 < C ∧ ∀ T : ℝ,
  (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)) ≤ C * (1 + |T|) ^ (-A1) := by
  intro A1 hA1
  let A0 : ℝ := A1 + 2
  let G : ℝ := ∫ x : ℝ, exp (-x ^ 2) * (1 + |x|) ^ A1
  let C : ℝ := G + 1
  have hA0 : 1 < A0 := by dsimp [A0]; linarith
  have hG : 0 ≤ G := by
    dsimp [G]
    exact integral_nonneg (fun x => by positivity)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨A0, C, hA0, hC, ?_⟩
  intro T
  let f : ℝ → ℝ := fun x => exp (-x ^ 2) * (1 + |x|) ^ A1
  let K : ℝ := (1 + |T|) ^ (-A1)
  have hmoment : Integrable f := by
    simpa [f] using integrable_gaussian_height_moment A1 (le_of_lt hA1)
  have hshift : Integrable (fun v : ℝ => f (T + v)) := by
    have h := (measurePreserving_add_left (volume : Measure ℝ) T).integrable_comp_of_integrable hmoment
    simpa [Function.comp_def] using h
  have hgauss : Integrable (fun v : ℝ => exp (-(T + v) ^ 2)) := by
    have hg := (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ)))
    have h := (measurePreserving_add_left (volume : Measure ℝ) T).integrable_comp_of_integrable hg
    simpa [Function.comp_def] using h
  have hK : 0 < K := by dsimp [K]; positivity
  have hKnonneg : 0 ≤ K := hK.le
  have hRHS : Integrable (fun v : ℝ => K * f (T + v)) := by
    simpa [smul_eq_mul] using hshift.const_mul K
  have hLHS : Integrable (fun v : ℝ => exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0)) := by
    refine Integrable.mono' hgauss ?_ ?_
    · fun_prop
    · filter_upwards with v
      have hvbase : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
      have hvpow : 0 ≤ (1 + |v|) ^ (-A0) := by positivity
      have hvle : (1 + |v|) ^ (-A0) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hvbase (by linarith [hA0])
      have hpoint : exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0) ≤
          exp (-(T + v) ^ 2) := by
        calc
          exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0) ≤
              exp (-(T + v) ^ 2) * 1 := mul_le_mul_of_nonneg_left hvle (exp_pos _).le
          _ = exp (-(T + v) ^ 2) := by ring
      have hExp : 0 ≤ exp (-(T + v) ^ 2) := (exp_pos _).le
      simpa [Real.norm_eq_abs, abs_of_nonneg hvpow, abs_of_nonneg hExp] using hpoint
  have hpoint (v : ℝ) :
      exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0) ≤ K * f (T + v) := by
    have hv2 : (1 + |v|) ^ (-2 : ℝ) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v]) (by norm_num)
    have hsplit : (1 + |v|) ^ (-A0) =
        (1 + |v|) ^ (-A1) * (1 + |v|) ^ (-2 : ℝ) := by
      rw [show -A0 = -A1 + (-2 : ℝ) by dsimp [A0]; ring,
        Real.rpow_add (by positivity)]
    calc
      exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0) =
          exp (-(T + v) ^ 2) * ((1 + |v|) ^ (-A1) * (1 + |v|) ^ (-2 : ℝ)) := by rw [hsplit]
      _ ≤ exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A1) := by
        have hfactor : 0 ≤ (1 + |v|) ^ (-A1) := by positivity
        simpa using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv2 hfactor)
          (exp_pos _).le
      _ ≤ K * (exp (-(T + v) ^ 2) * (1 + |T + v|) ^ A1) := by
        calc
          _ ≤ exp (-(T + v) ^ 2) * (K * (1 + |T + v|) ^ A1) :=
            mul_le_mul_of_nonneg_left (gaussian_height_transfer A1 T v hA1)
              (exp_pos _).le
          _ = K * (exp (-(T + v) ^ 2) * (1 + |T + v|) ^ A1) := by ring
      _ = K * f (T + v) := by rfl
  have hmono := integral_mono hLHS hRHS hpoint
  have htranslate : (∫ v : ℝ, f (T + v)) = G := by
    calc
      (∫ v : ℝ, f (T + v)) = ∫ x : ℝ, f x :=
        (measurePreserving_add_left (volume : Measure ℝ) T).integral_comp
          (Homeomorph.addLeft T).measurableEmbedding f
      _ = G := by rfl
  calc
    (∫ v : ℝ, exp (-(T + v) ^ 2) * (1 + |v|) ^ (-A0)) ≤
        ∫ v : ℝ, K * f (T + v) := hmono
    _ = K * G := by rw [integral_const_mul, htranslate]
    _ ≤ C * K := by
      dsimp [C]
      calc
        K * G ≤ K * (G + 1) := mul_le_mul_of_nonneg_left (by linarith [hG]) hKnonneg
        _ = (G + 1) * K := by ring
    _ = C * (1 + |T|) ^ (-A1) := by rfl

end ArtinPrimitiveRoots.Proofs.A2Rows
