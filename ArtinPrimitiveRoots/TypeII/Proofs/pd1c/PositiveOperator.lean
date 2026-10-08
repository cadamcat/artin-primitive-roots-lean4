import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalities

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

set_option maxHeartbeats 1000000

lemma pd1c_weighted_power_mean {ι : Type*} (s : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (R : ℕ) (hR : 1 ≤ R) :
    (∑ i ∈ s, w i * t i) ^ R ≤
      (∑ i ∈ s, w i) ^ (R - 1) * ∑ i ∈ s, w i * t i ^ R := by
  let W := ∑ i ∈ s, w i
  let A := ∑ i ∈ s, w i * t i
  let B := ∑ i ∈ s, w i * t i ^ R
  have hWnonneg : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hW0 : W = 0
  · have hz : ∀ i ∈ s, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW0
    have hA : A = 0 := Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
    have hB : B = 0 := Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
    change A ^ R ≤ W ^ (R - 1) * B
    simp [hA, hB, Nat.ne_of_gt (by omega : 0 < R)]
  have hW : 0 < W := lt_of_le_of_ne hWnonneg (Ne.symm hW0)
  have hn : (∑ i ∈ s, w i / W) = 1 := by
    rw [← Finset.sum_div]
    exact div_self hW0
  have hJ := (convexOn_rpow (p := (R : ℝ)) (by exact_mod_cast hR)).map_sum_le
    (t := s) (w := fun i => w i / W) (p := t)
    (fun i hi => div_nonneg (hw i hi) hW.le) hn ht
  have hJ' : (A / W) ^ R ≤ B / W := by
    simpa only [smul_eq_mul, Real.rpow_natCast, div_mul_eq_mul_div,
      ← Finset.sum_div] using hJ
  have hmul := mul_le_mul_of_nonneg_left hJ' (pow_nonneg hW.le R)
  have hleft : W ^ R * (A / W) ^ R = A ^ R := by
    rw [← mul_pow, mul_div_cancel₀ _ hW0]
  have hright : W ^ R * (B / W) = W ^ (R - 1) * B := by
    rw [show R = (R - 1) + 1 by omega, pow_succ]
    field_simp [hW0]
    simp [mul_comm]
  change A ^ R ≤ W ^ (R - 1) * B
  rwa [hleft, hright] at hmul


lemma pd1c_diagonal_inner {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : ι → ℂ) (hμ : ∀ i, T (b i) = μ i • b i) (x : E) :
    (inner ℂ x (T x)).re =
      ∑ i, (star (b.repr x i) * (μ i * b.repr x i)).re := by
  have hTx : T x = ∑ i, (μ i * b.repr x i) • b i := by
    calc
      T x = T (∑ i, b.repr x i • b i) := congrArg T (b.sum_repr x).symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, hμ, smul_smul]
        congr 1
        ring
  have hinner := congrArg Complex.re
    (b.orthonormal.inner_sum (fun i => b.repr x i)
      (fun i => μ i * b.repr x i) Finset.univ)
  rw [b.sum_repr, ← hTx] at hinner
  simpa only [Complex.re_sum, Complex.star_def] using hinner

lemma pd1c_real_diagonal_inner {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E)
    (eigenVals : ι → ℝ) (heigenVals : ∀ i, T (b i) = (eigenVals i : ℂ) • b i) (x : E) :
    (inner ℂ x (T x)).re = ∑ i, ‖b.repr x i‖ ^ 2 * eigenVals i := by
  rw [pd1c_diagonal_inner b T (fun i => (eigenVals i : ℂ)) heigenVals x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.normSq_apply]
  ring

lemma pd1c_spectral_power_mean {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hNonneg : ∀ x : E, 0 ≤ (inner ℂ x (T x)).re)
    (R : ℕ) (hR : 1 ≤ R) (x : E) :
    (inner ℂ x (T x)).re ^ R ≤
      (‖x‖ ^ 2) ^ (R - 1) * (inner ℂ x ((T ^ R) x)).re := by
  let n := Module.finrank ℂ E
  let hn : Module.finrank ℂ E = n := rfl
  let b := hT.eigenvectorBasis hn
  let eigenVals := hT.eigenvalues hn
  have heigenVals : ∀ i : Fin n, 0 ≤ eigenVals i := by
    intro i
    exact eigenvalue_nonneg_of_nonneg (hT.hasEigenvalue_eigenvalues hn i) hNonneg
  have hLin : (inner ℂ x (T x)).re = ∑ i : Fin n, ‖b.repr x i‖ ^ 2 * eigenVals i :=
    pd1c_real_diagonal_inner b T eigenVals (hT.apply_eigenvectorBasis hn) x
  have hPow : (inner ℂ x ((T ^ R) x)).re =
      ∑ i : Fin n, ‖b.repr x i‖ ^ 2 * (eigenVals i) ^ R := by
    apply pd1c_real_diagonal_inner b (T ^ R) (fun i => (eigenVals i) ^ R)
    intro i
    have hv := (hT.hasEigenvector_eigenvectorBasis hn i).pow_apply R
    convert hv using 1 <;> simp only [b, eigenVals, Complex.ofReal_pow]
    congr 1
  have hNorm : (∑ i : Fin n, ‖b.repr x i‖ ^ 2) = ‖x‖ ^ 2 := by
    simp only [b.repr_apply_apply]
    exact b.sum_sq_norm_inner_right x
  have hmean := pd1c_weighted_power_mean (Finset.univ : Finset (Fin n))
    (fun i => ‖b.repr x i‖ ^ 2) eigenVals (fun i hi => sq_nonneg _) (fun i hi => heigenVals i) R hR
  rwa [← hLin, hNorm, ← hPow] at hmean


lemma pd1c_finite_vector_cauchy {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (s : Finset ι) (c : ι → ℂ) (v : ι → E) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, c i • v i‖ ≤ ∑ i ∈ s, ‖c i‖ * ‖v i‖ := by
    simpa only [norm_smul] using norm_sum_le s (fun i => c i • v i)
  calc
    _ ≤ (∑ i ∈ s, ‖c i‖ * ‖v i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖c i‖) (fun i => ‖v i‖)

lemma pd1c_gram_trace_bound {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (c : ι → ℂ) (v : ι → E) (T : E →ₗ[ℂ] E)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i ∈ s, ‖c i‖ ≤ M) :
    ‖T (∑ i ∈ s, c i • v i)‖ ^ 2 ≤
      (s.card : ℝ) * M ^ 2 * ∑ i ∈ s, ‖T (v i)‖ ^ 2 := by
  have hcoeff : (∑ i ∈ s, ‖c i‖ ^ 2) ≤ (s.card : ℝ) * M ^ 2 := by
    calc
      _ ≤ ∑ i ∈ s, M ^ 2 :=
        Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (norm_nonneg _) (hc i hi) 2
      _ = _ := by simp
  rw [map_sum]
  simp only [map_smul]
  calc
    _ ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖T (v i)‖ ^ 2 :=
      pd1c_finite_vector_cauchy s c (fun i => T (v i))
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (Finset.sum_nonneg fun i hi => sq_nonneg _)


lemma pd1c_power_bound_to_rpow (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (R : ℕ) (hR : 1 ≤ R) (hbound : a ^ R ≤ b ^ (R - 1) * c) :
    a ≤ Real.rpow b (1 - 1 / (R : ℝ)) * Real.rpow c (1 / (R : ℝ)) := by
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
  have hroot := Real.rpow_le_rpow (pow_nonneg ha R) hbound
    (by positivity : 0 ≤ (1 / (R : ℝ)))
  have hLeft : (a ^ R : ℝ) ^ (1 / (R : ℝ)) = a := by
    rw [← Real.rpow_natCast a R, ← Real.rpow_mul ha]
    rw [show (R : ℝ) * (1 / (R : ℝ)) = 1 by field_simp, Real.rpow_one]
  have hRight : (b ^ (R - 1) * c : ℝ) ^ (1 / (R : ℝ)) =
      b ^ (1 - 1 / (R : ℝ)) * c ^ (1 / (R : ℝ)) := by
    rw [Real.mul_rpow (pow_nonneg hb _) hc, ← Real.rpow_natCast b (R - 1),
      ← Real.rpow_mul hb]
    congr 2
    rw [Nat.cast_sub hR, Nat.cast_one]
    field_simp
  simp only [Real.rpow_eq_pow]
  rwa [hLeft, hRight] at hroot


lemma pd1c_finite_mixed_power_sum {ι : Type*} (s : Finset ι) (a d : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hd : ∀ i ∈ s, 0 ≤ d i) (R : ℕ) (hR : 2 ≤ R) :
    (∑ i ∈ s, (a i) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (R : ℝ))) ≤
      (∑ i ∈ s, a i) ^ (1 - 1 / (R : ℝ)) * (∑ i ∈ s, d i) ^ (1 / (R : ℝ)) := by
  have hRgt : 1 < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hRne : (R : ℝ) ≠ 0 := by linarith
  have hRmne : (R : ℝ) - 1 ≠ 0 := by linarith
  let p : ℝ := (R : ℝ) / ((R : ℝ) - 1)
  have hpq : p.HolderConjugate (R : ℝ) := (Real.HolderConjugate.conjExponent hRgt).symm
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (f := fun i => (a i) ^ (1 - 1 / (R : ℝ)))
    (g := fun i => (d i) ^ (1 / (R : ℝ))) hpq
    (fun i hi => Real.rpow_nonneg (ha i hi) _) (fun i hi => Real.rpow_nonneg (hd i hi) _)
  have hfp : (∑ i ∈ s, ((a i) ^ (1 - 1 / (R : ℝ))) ^ p) = ∑ i ∈ s, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (ha i hi)]
    have hexp : (1 - 1 / (R : ℝ)) * p = 1 := by
      dsimp only [p]
      field_simp [hRne, hRmne] <;> ring
    rw [hexp, Real.rpow_one]
  have hgq : (∑ i ∈ s, ((d i) ^ (1 / (R : ℝ))) ^ (R : ℝ)) = ∑ i ∈ s, d i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hd i hi), one_div_mul_cancel hRne, Real.rpow_one]
  have hpinv : 1 / p = 1 - 1 / (R : ℝ) := by
    dsimp only [p]
    field_simp [hRne, hRmne] <;> ring
  rwa [hfp, hgq, hpinv] at h

lemma pd1c_finite_three_factor_holder_sq {ι : Type*} (s : Finset ι) (g f d : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hf : ∀ i ∈ s, 0 ≤ f i) (hd : ∀ i ∈ s, 0 ≤ d i)
    (R : ℕ) (hR : 2 ≤ R) :
    (∑ i ∈ s, g i * (f i) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (2 * (R : ℝ)))) ^ 2 ≤
      (∑ i ∈ s, (g i) ^ 2) * (∑ i ∈ s, (f i) ^ 2) ^ (1 - 1 / (R : ℝ)) *
        (∑ i ∈ s, d i) ^ (1 / (R : ℝ)) := by
  have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s g
    (fun i => (f i) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (2 * (R : ℝ))))
  have hterms : (∑ i ∈ s,
      ((f i) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (2 * (R : ℝ)))) ^ 2) =
        ∑ i ∈ s, ((f i) ^ 2 : ℝ) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (R : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, ← Real.rpow_mul_natCast (hf i hi), ← Real.rpow_mul_natCast (hd i hi)]
    rw [← Real.rpow_natCast (f i) 2, ← Real.rpow_mul (hf i hi)]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      field_simp [hRne]
  have hmix := pd1c_finite_mixed_power_sum s (fun i => (f i) ^ 2) d
    (fun i hi => sq_nonneg _) hd R hR
  rw [hterms] at hcs
  calc
    _ = (∑ i ∈ s, g i * ((f i) ^ (1 - 1 / (R : ℝ)) * (d i) ^ (1 / (2 * (R : ℝ))))) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := hcs
    _ ≤ (∑ i ∈ s, (g i) ^ 2) *
        ((∑ i ∈ s, (f i) ^ 2) ^ (1 - 1 / (R : ℝ)) * (∑ i ∈ s, d i) ^ (1 / (R : ℝ))) :=
      mul_le_mul_of_nonneg_left hmix (Finset.sum_nonneg fun i hi => sq_nonneg _)
    _ = _ := by ring


lemma pd1c_rpow_half_sq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num


lemma pd1c_moment_scalar_bound (L X H B W K C Ce E n G F D : ℝ) (R : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (hH : 0 < H) (hB : 1 ≤ B) (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hC : 0 < C) (hCe : 0 < Ce) (hn : 0 ≤ n) (hG : 0 ≤ G) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hR : 2 ≤ R)
    (hHR : H ^ (1 / (2 * (R : ℝ))) ≤ W)
    (hGbound : G ≤ X * B ^ 2 * L ^ (2 * Ce))
    (hFbound : F ≤ X * B ^ 2 * L ^ (2 * Ce))
    (hDbound : D ≤ L ^ (-2 * E * (R : ℝ)))
    (hPair : n ^ 2 ≤ K * G * F ^ (1 - 1 / (R : ℝ)) *
      (9000 * H * (L ^ (2 * C)) ^ 2 * (X * D)) ^ (1 / (R : ℝ))) :
    n ≤ 100 * K ^ (1 / 2 : ℝ) * B ^ 2 * W * X * L ^ (-E + 2 * Ce + 2 * C) := by
  let p : ℝ := 1 / (R : ℝ)
  let θ : ℝ := 1 - p
  let NB := X * B ^ 2 * L ^ (2 * Ce)
  let T := 9000 * H * L ^ (4 * C)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hRge : 1 ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hRpos : 0 < (R : ℝ) := lt_of_lt_of_le (by norm_num) hRge
  have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hp₁ : p ≤ 1 := (div_le_iff₀ hRpos).mpr (by simpa using hRge)
  have hθ : 0 ≤ θ := sub_nonneg.mpr hp₁
  have hθ₁ : θ ≤ 1 := by dsimp only [θ]; linarith
  have hNB : 0 ≤ NB := by dsimp only [NB]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hMpow : (L ^ (2 * C)) ^ 2 = L ^ (4 * C) := by
    rw [← Real.rpow_mul_natCast hLpos.le]
    congr 1
    push_cast
    ring
  rw [hMpow] at hPair
  have hFpow : F ^ θ ≤ NB ^ θ := Real.rpow_le_rpow hF hFbound hθ
  have hGF : K * G * F ^ θ ≤ K * NB * NB ^ θ := by
    have h := mul_le_mul hGbound hFpow (Real.rpow_nonneg hF _) hNB
    simpa only [NB, mul_assoc] using mul_le_mul_of_nonneg_left h hK
  have hDPow : (T * (X * D)) ^ p ≤ (T * (X * L ^ (-2 * E * (R : ℝ)))) ^ p := by
    apply Real.rpow_le_rpow (by positivity) _ hp
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDbound hX.le) hT
  have hRaw : n ^ 2 ≤ K * NB * NB ^ θ * (T * (X * L ^ (-2 * E * (R : ℝ)))) ^ p := by
    exact hPair.trans (mul_le_mul hGF hDPow (Real.rpow_nonneg (by positivity) _) (by positivity))
  have hNBpow : NB ^ θ = X ^ θ * (B ^ 2) ^ θ * L ^ (2 * Ce * θ) := by
    dsimp only [NB]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hX.le (sq_nonneg B),
      ← Real.rpow_mul hLpos.le]
  have hMomentPow : (L ^ (-2 * E * (R : ℝ))) ^ p = L ^ (-2 * E) := by
    rw [← Real.rpow_mul hLpos.le]
    congr 1
    dsimp only [p]
    field_simp [hRne]
  have hTPow : (T * (X * L ^ (-2 * E * (R : ℝ)))) ^ p =
      (9000 : ℝ) ^ p * H ^ p * L ^ (4 * C * p) * X ^ p * L ^ (-2 * E) := by
    dsimp only [T]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by norm_num) hH.le, Real.mul_rpow hX.le (by positivity),
      ← Real.rpow_mul hLpos.le, hMomentPow]
    ring
  have hXpow : X * X ^ θ * X ^ p = X ^ 2 := by
    calc
      _ = X ^ (1 : ℝ) * X ^ θ * X ^ p := by rw [Real.rpow_one]
      _ = X ^ (1 + θ + p) := by rw [← Real.rpow_add hX, ← Real.rpow_add hX]
      _ = X ^ 2 := by
        have heq : 1 + θ + p = 2 := by dsimp only [θ]; ring
        rw [heq]
        norm_num
  have hBpow : B ^ 2 * (B ^ 2) ^ θ = (B ^ 2) ^ (1 + θ) := by
    rw [Real.rpow_add (sq_pos_of_pos hBpos), Real.rpow_one]
  let e := 2 * Ce * (1 + θ) + 4 * C * p - 2 * E
  have hLpow : L ^ (2 * Ce) * L ^ (2 * Ce * θ) * L ^ (4 * C * p) * L ^ (-2 * E) = L ^ e := by
    rw [← Real.rpow_add hLpos, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    congr 1
    dsimp only [e]
    ring
  have hRecombine : K * NB * NB ^ θ * (T * (X * L ^ (-2 * E * (R : ℝ)))) ^ p =
      K * (B ^ 2) ^ (1 + θ) * (9000 : ℝ) ^ p * H ^ p * X ^ 2 * L ^ e := by
    rw [hNBpow, hTPow]
    dsimp only [NB]
    calc
      _ = K * (B ^ 2 * (B ^ 2) ^ θ) * (9000 : ℝ) ^ p * H ^ p *
          (X * X ^ θ * X ^ p) * (L ^ (2 * Ce) * L ^ (2 * Ce * θ) * L ^ (4 * C * p) * L ^ (-2 * E)) := by ring
      _ = _ := by rw [hXpow, hBpow, hLpow]
  have hBs : 1 ≤ B ^ 2 := by nlinarith
  have hBsmall : (B ^ 2) ^ (1 + θ) ≤ B ^ 4 := by
    calc
      _ ≤ (B ^ 2) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hBs (by linarith)
      _ = B ^ 4 := by norm_num [← pow_mul]
  have h9000 : (9000 : ℝ) ^ p ≤ 9000 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9000) hp₁
  have hHpow : H ^ p = (H ^ (1 / (2 * (R : ℝ)))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hH.le]
    congr 1
    dsimp only [p]
    push_cast
    field_simp [hRne]
  have hHsmall : H ^ p ≤ W ^ 2 := by
    rw [hHpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hH.le _) hHR 2
  have he : e ≤ 2 * (-E + 2 * Ce + 2 * C) := by
    have hCeT := mul_le_mul_of_nonneg_left (show 1 + θ ≤ 2 by linarith) (show 0 ≤ 2 * Ce by positivity)
    have hCT := mul_le_mul_of_nonneg_left hp₁ (show 0 ≤ 4 * C by positivity)
    dsimp only [e]
    linarith
  have hLsmall : L ^ e ≤ L ^ (2 * (-E + 2 * Ce + 2 * C)) :=
    Real.rpow_le_rpow_of_exponent_le hL he
  have hAll : n ^ 2 ≤ K * B ^ 4 * 9000 * W ^ 2 * X ^ 2 * L ^ (2 * (-E + 2 * Ce + 2 * C)) := by
    rw [hRecombine] at hRaw
    refine hRaw.trans ?_
    gcongr
  have hLsq : (L ^ (-E + 2 * Ce + 2 * C)) ^ 2 = L ^ (2 * (-E + 2 * Ce + 2 * C)) := by
    rw [← Real.rpow_mul_natCast hLpos.le]
    congr 1
    push_cast
    ring
  have hSquare : (100 * K ^ (1 / 2 : ℝ) * B ^ 2 * W * X * L ^ (-E + 2 * Ce + 2 * C)) ^ 2 =
      10000 * K * B ^ 4 * W ^ 2 * X ^ 2 * L ^ (2 * (-E + 2 * Ce + 2 * C)) := by
    simp only [mul_pow, pd1c_rpow_half_sq K hK]
    rw [hLsq]
    ring
  apply (sq_le_sq₀ hn (by positivity)).mp
  rw [hSquare]
  refine hAll.trans ?_
  have hFactor : 0 ≤ K * B ^ 4 * W ^ 2 * X ^ 2 * L ^ (2 * (-E + 2 * Ce + 2 * C)) := by positivity
  calc
    _ = 9000 * (K * B ^ 4 * W ^ 2 * X ^ 2 * L ^ (2 * (-E + 2 * Ce + 2 * C))) := by ring
    _ ≤ 10000 * (K * B ^ 4 * W ^ 2 * X ^ 2 * L ^ (2 * (-E + 2 * Ce + 2 * C))) :=
      mul_le_mul_of_nonneg_right (by norm_num : (9000 : ℝ) ≤ 10000) hFactor
    _ = _ := by ring

end ArtinPrimitiveRoots.TypeII.PD
