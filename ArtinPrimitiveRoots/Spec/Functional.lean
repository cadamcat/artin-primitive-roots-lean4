import ArtinPrimitiveRoots.Spec.Defs
import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent

/-! Functional-analysis nodes F1--F2. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open Filter
open scoped MatrixGroups ContDiff BoundedContinuousFunction Topology
open scoped NNReal

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem faEnergy_inner (D : FAEnergySpace H G) (x y : D.V) :
    inner ℂ x y = inner ℂ (D.M x) (D.M y) + inner ℂ (D.Gr x) (D.Gr y) := by
  change inner ℂ (x : WithLp 2 (H × G)) (y : WithLp 2 (H × G)) = _
  rw [WithLp.prod_inner_apply]
  simp [FAEnergySpace.M, FAEnergySpace.Gr]

theorem faEnergy_norm_sq (D : FAEnergySpace H G) (x : D.V) :
    ‖x‖ ^ 2 = ‖D.M x‖ ^ 2 + ‖D.Gr x‖ ^ 2 := by
  have h := WithLp.prod_norm_sq_eq_of_L2 (x : WithLp 2 (H × G))
  simpa [FAEnergySpace.M, FAEnergySpace.Gr] using h

theorem faT_inner (D : FAEnergySpace H G) (x y : D.V) :
    inner ℂ x (D.T y) = inner ℂ (D.M x) (D.M y) := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  change inner ℂ x ((D.M).adjoint (D.M y)) = _
  exact ContinuousLinearMap.adjoint_inner_right (D.M) x (D.M y)

theorem faT_selfAdjoint (D : FAEnergySpace H G) : IsSelfAdjoint (D.T) := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  change ((D.M).adjoint.comp D.M).adjoint = (D.M).adjoint.comp D.M
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

theorem faA_inner (D : FAEnergySpace H G) (z : ℂ) (x : D.V) :
    inner ℂ x (D.A z x) = (‖D.Gr x‖ ^ 2 : ℂ) - z * (‖D.M x‖ ^ 2 : ℂ) := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  change inner ℂ x (x - (z + 1) • D.T x) = _
  rw [inner_sub_right]
  rw [inner_smul_right x (D.T x) (z + 1)]
  rw [faT_inner]
  have hx := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
  have hm := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (D.M x)
  have hgr := faEnergy_norm_sq D x
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow] at hx hm ⊢
  have hgrc : ((‖x‖ ^ 2 : ℝ) : ℂ) =
      ((‖D.M x‖ ^ 2 : ℝ) : ℂ) + ((‖D.Gr x‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast hgr
  rw [hx, hm, hgrc]
  ring

theorem faA_inner_polarized (D : FAEnergySpace H G) (z : ℂ) (x y : D.V) :
    inner ℂ x (D.A z y) = inner ℂ (D.Gr x) (D.Gr y) -
      z * inner ℂ (D.M x) (D.M y) := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  change inner ℂ x (y - (z + 1) • D.T y) = _
  rw [inner_sub_right]
  rw [inner_smul_right x (D.T y) (z + 1)]
  rw [faT_inner]
  rw [faEnergy_inner D x y]
  ring

theorem faA_real_selfAdjoint (D : FAEnergySpace H G) (lam : ℝ) :
    IsSelfAdjoint (D.A (lam : ℂ)) := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (x - ((lam : ℂ) + 1) • D.T x) y =
    inner ℂ x (y - ((lam : ℂ) + 1) • D.T y)
  rw [inner_sub_left, inner_sub_right]
  rw [inner_smul_left (D.T x) y ((lam : ℂ) + 1)]
  rw [inner_smul_right x (D.T y) ((lam : ℂ) + 1)]
  have hstar : starRingEnd ℂ ((lam : ℂ) + 1) = (lam : ℂ) + 1 := by simp
  have hs : inner ℂ (D.T x) y = inner ℂ x (D.T y) := by
    simpa only [ContinuousLinearMap.coe_coe] using (faT_selfAdjoint D).isSymmetric x y
  rw [hstar, hs]

/-- The inverse of the spectral pencil where it is a unit, extended by zero elsewhere. -/
noncomputable def faInverse (D : FAEnergySpace H G) (z : ℂ) : D.V →L[ℂ] D.V := by
  classical
  exact if h : IsUnit (D.A z) then (↑((h.unit)⁻¹) : D.V →L[ℂ] D.V) else 0

/-- The resolvent of the mass form on a closed energy graph. -/
noncomputable def faResolvent (D : FAEnergySpace H G) (z : ℂ) : H →L[ℂ] H := by
  letI : CompleteSpace D.V := D.closedV.completeSpace_coe
  exact D.M.comp ((faInverse D z).comp D.M.adjoint)

theorem faInverse_eq_ringInverse (D : FAEnergySpace H G) (z : ℂ)
    (hz : IsUnit (D.A z)) : faInverse D z = Ring.inverse (D.A z) := by
  classical
  unfold faInverse
  simp only [dif_pos hz, Ring.inverse_of_isUnit hz]

theorem faA_analyticAt (D : FAEnergySpace H G) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => D.A w) z := by
  let S : D.V →L[ℂ] D.V := D.T
  have hscale : AnalyticAt ℂ (fun w : ℂ => w • S) (z + 1) := by
    simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := D.V →L[ℂ] D.V)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) S) (z + 1))
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z :=
    analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hscale.comp_of_eq hshift rfl)

theorem faInverse_analyticAt_of_isUnit (D : FAEnergySpace H G) (z : ℂ)
    (hz : IsUnit (D.A z)) : AnalyticAt ℂ (faInverse D) z := by
  have hinv := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := D.V →L[ℂ] D.V)) (D.A z) hz
  have han : AnalyticAt ℂ (fun w : ℂ => Ring.inverse (D.A w)) z :=
    hinv.comp_of_eq (faA_analyticAt D z) rfl
  have hnear : ∀ᶠ w : ℂ in 𝓝 z, IsUnit (D.A w) :=
    (faA_analyticAt D z).continuousAt.eventually
      ((Units.isOpen (R := D.V →L[ℂ] D.V)).mem_nhds hz)
  have heq : faInverse D =ᶠ[𝓝 z] fun w : ℂ => Ring.inverse (D.A w) := by
    filter_upwards [hnear] with w hw
    exact faInverse_eq_ringInverse D w hw
  exact han.congr heq.symm

theorem faA_real_negative_isUnit (D : FAEnergySpace H G) (lam : ℝ) (hlam : lam < 0) :
    IsUnit (D.A (lam : ℂ)) := by
  let δ : ℝ := min 1 (-lam)
  let δNN : ℝ≥0 := ⟨δ, le_of_lt (lt_min one_pos (neg_pos.mpr hlam))⟩
  have hδ : 0 < δ := lt_min one_pos (neg_pos.mpr hlam)
  have hunitδ : 0 < δNN := by exact_mod_cast hδ
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (D.A (lam : ℂ)) hunitδ
  intro x
  have hq : 0 ≤ ‖D.Gr x‖ ^ 2 - lam * ‖D.M x‖ ^ 2 := by
    have hl : 0 ≤ -lam := le_of_lt (neg_pos.mpr hlam)
    nlinarith [sq_nonneg ‖D.M x‖, sq_nonneg ‖D.Gr x‖,
      mul_nonneg hl (sq_nonneg ‖D.M x‖)]
  have hqLower : δ * ‖x‖ ^ 2 ≤ ‖D.Gr x‖ ^ 2 - lam * ‖D.M x‖ ^ 2 := by
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδlam : δ ≤ -lam := min_le_right _ _
    rw [faEnergy_norm_sq]
    nlinarith [sq_nonneg ‖D.M x‖, sq_nonneg ‖D.Gr x‖]
  have hs : inner ℂ (D.A (lam : ℂ) x) x = inner ℂ x (D.A (lam : ℂ) x) := by
    simpa only [ContinuousLinearMap.coe_coe] using (faA_real_selfAdjoint D lam).isSymmetric x x
  have hinner : inner ℂ (D.A (lam : ℂ) x) x =
      ((‖D.Gr x‖ ^ 2 - lam * ‖D.M x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hs, faA_inner]
    push_cast
    ring
  have hnorm : ‖inner ℂ (D.A (lam : ℂ) x) x‖ =
      ‖D.Gr x‖ ^ 2 - lam * ‖D.M x‖ ^ 2 := by
    rw [hinner]
    exact (RCLike.norm_ofReal _).trans (abs_of_nonneg hq)
  have hqNN : (‖x‖ ^ 2) * (δNN : ℝ) ≤ ‖inner ℂ (D.A (lam : ℂ) x) x‖ := by
    rw [hnorm]
    change ‖x‖ ^ 2 * δ ≤ ‖D.Gr x‖ ^ 2 - lam * ‖D.M x‖ ^ 2
    simpa [mul_comm] using hqLower
  exact hqNN

theorem faA_off_cut_isUnit (D : FAEnergySpace H G) (z : ℂ)
    (hz : ¬ (z.im = 0 ∧ 0 ≤ z.re)) : IsUnit (D.A z) := by
  by_cases him : z.im = 0
  · have hre : z.re < 0 := by
      by_contra h
      exact hz ⟨him, le_of_not_gt h⟩
    have hzeq : z = (z.re : ℂ) := by
      exact Complex.ext rfl (by simpa [him])
    rw [hzeq]
    exact faA_real_negative_isUnit D z.re hre
  · have hunit := OAI.CubicEisenstein.selfAdjoint_pencil_isUnit_nonreal
      D.T (faT_selfAdjoint D) (z + 1) (by simpa using him)
    have hEq : (1 - (z + 1) • D.T : D.V →L[ℂ] D.V) = D.A z := by
      ext x
      simp [FAEnergySpace.A]
    rw [← hEq]
    exact hunit

theorem faA_kernel_T_eigen (D : FAEnergySpace H G) (lam : ℝ) (hlam : 0 ≤ lam)
    (x : D.V) (hx : x ∈ (D.A (lam : ℂ)).toLinearMap.ker) :
    D.T x = (((lam + 1)⁻¹ : ℝ) : ℂ) • x := by
  have hLamPos : 0 < lam + 1 := by linarith
  have hcoef : ((lam + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLamPos.ne'
  have hzero : x - ((lam : ℂ) + 1) • D.T x = 0 := by
    change D.A (lam : ℂ) x = 0 at hx
    change x - ((lam : ℂ) + 1) • D.T x = 0 at hx
    exact hx
  have hEq : ((lam + 1 : ℝ) : ℂ) • D.T x = x := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using (sub_eq_zero.mp hzero).symm
  calc
    D.T x = (((lam + 1 : ℝ) : ℂ)⁻¹) •
        (((lam + 1 : ℝ) : ℂ) • D.T x) := by
          rw [smul_smul, inv_mul_cancel₀ hcoef, one_smul]
    _ = (((lam + 1 : ℝ) : ℂ)⁻¹) • x := by rw [hEq]
    _ = (((lam + 1)⁻¹ : ℝ) : ℂ) • x := by simp

theorem faT_preserves_kernel_orthogonal (D : FAEnergySpace H G) (lam : ℝ)
    (hlam : 0 ≤ lam) (v : D.V)
    (hv : v ∈ (D.A (lam : ℂ)).toLinearMap.kerᗮ) :
    D.T v ∈ (D.A (lam : ℂ)).toLinearMap.kerᗮ := by
  intro n hn
  have hs : inner ℂ n (D.T v) = inner ℂ (D.T n) v := by
    simpa only [ContinuousLinearMap.coe_coe] using
      ((faT_selfAdjoint D).isSymmetric n v).symm
  rw [hs, faA_kernel_T_eigen D lam hlam n hn,
    inner_smul_left n v (((lam + 1)⁻¹ : ℝ) : ℂ)]
  simp [hv n hn]

private def faContinuousLinearSandwich {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) (B : F →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (F →L[ℂ] F) :=
  (ContinuousLinearMap.compL ℂ F E F A).comp
    ((ContinuousLinearMap.compL ℂ F E E).flip B)

private abbrev faEndNormedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    NormedSpace ℂ (E →L[ℂ] E) := inferInstance

private def faRegularSubmodule (D : FAEnergySpace H G) (lam : ℝ) : Submodule ℂ D.V :=
  (D.A (lam : ℂ)).toLinearMap.kerᗮ

private instance faRegularSubmoduleNormedSpace (D : FAEnergySpace H G) (lam : ℝ) :
    NormedSpace ℂ (faRegularSubmodule D lam) where
  toModule := (faRegularSubmodule D lam).module
  norm_smul_le a x := by
    change ‖a • (x : D.V)‖ ≤ ‖a‖ * ‖(x : D.V)‖
    exact norm_smul_le a (x : D.V)

private instance faRegularSubmoduleSMulCommClass (D : FAEnergySpace H G) (lam : ℝ) :
    SMulCommClass ℂ ℂ (faRegularSubmodule D lam) := ⟨fun a b x => by
      simp only [smul_smul]
      rw [mul_comm]⟩

private instance faRegularSubmoduleCompleteSpace (D : FAEnergySpace H G) (lam : ℝ) :
    CompleteSpace (faRegularSubmodule D lam) := by
  let N : Submodule ℂ D.V := (D.A (lam : ℂ)).toLinearMap.ker
  have hN : IsClosed (N : Set D.V) := by
    change IsClosed ((D.A (lam : ℂ)).toLinearMap.ker : Set D.V)
    exact (D.A (lam : ℂ)).isClosed_ker
  have hR : IsClosed (Nᗮ : Set D.V) := N.isClosed_orthogonal
  change CompleteSpace (Nᗮ)
  exact hR.completeSpace_coe

private instance faRegularSubmoduleEndNormedSpace (D : FAEnergySpace H G) (lam : ℝ) :
    NormedSpace ℂ (faRegularSubmodule D lam →L[ℂ] faRegularSubmodule D lam) :=
  faEndNormedSpace (faRegularSubmodule D lam)

/-- F1 `spec:fa-fredholm` — P-SPEC.md:235, 370–377. The form identity, self-adjointness on the
real axis, and Fredholm property below the coercivity threshold for the abstract energy graph. -/
theorem F1_fredholm (D : FAEnergySpace H G) (K : D.V →L[ℂ] H)
    (hK : IsCompactOperator K) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hest : ∀ x : D.V, ‖D.M x‖ ^ 2 ≤ c * ‖D.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2) :
    (∀ z : ℂ, ∀ x : D.V,
      inner ℂ x (D.A z x) = (‖D.Gr x‖ ^ 2 : ℂ) - z * (‖D.M x‖ ^ 2 : ℂ)) ∧
    (∀ lam : ℝ,
      IsSelfAdjoint (D.A (lam : ℂ)) ∧
      (lam < 1 / c → (D.A (lam : ℂ)).IsFredholm)) := by
  refine ⟨?_, ?_⟩
  · intro z x
    exact faA_inner D z x
  · intro lam
    refine ⟨faA_real_selfAdjoint D lam, ?_⟩
    intro hlam
    let a : ℝ := max lam 0
    let d : ℝ := 1 - a * c
    let L : ℝ := (1 + c) / d
    let B : ℝ := (1 + a) * C / d
    have ha : 0 ≤ a := by simp [a]
    have hlam_a : lam ≤ a := by simp [a]
    have hd : 0 < d := by
      by_cases hnonpos : lam ≤ 0
      · simp [d, a, max_eq_right hnonpos]
      · have hlampos : 0 < lam := lt_of_not_ge hnonpos
        have hlamc : lam * c < 1 := (lt_div_iff₀ hc).mp hlam
        have hac : a * c < 1 := by simpa [a, max_eq_left hlampos.le] using hlamc
        dsimp [d]
        linarith
    have hL : 0 < L := by dsimp [L]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    apply OAI.CubicEisenstein.selfAdjoint_fredholm_of_compact_estimate
      (D.A (lam : ℂ)) (faA_real_selfAdjoint D lam) K hK (L ^ 2) (2 * B)
    intro x
    let m : ℝ := ‖D.M x‖
    let g : ℝ := ‖D.Gr x‖
    let k : ℝ := ‖K x‖
    let n : ℝ := ‖x‖
    let t : ℝ := ‖D.A (lam : ℂ) x‖
    let q : ℝ := (inner ℂ x (D.A (lam : ℂ) x)).re
    have hm0 : 0 ≤ m := by dsimp [m]; positivity
    have hg0 : 0 ≤ g := by dsimp [g]; positivity
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    have hn0 : 0 ≤ n := by dsimp [n]; positivity
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have hnorm : n ^ 2 = m ^ 2 + g ^ 2 := by
      dsimp [n, m, g]
      exact faEnergy_norm_sq D x
    have hcore : m ^ 2 ≤ c * g ^ 2 + C * k ^ 2 := by
      dsimp [m, g, k]
      exact hest x
    have hq : q = g ^ 2 - lam * m ^ 2 := by
      change (inner ℂ x (D.A (lam : ℂ) x)).re = _
      rw [faA_inner]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, ← Complex.ofReal_pow]
      simp [g, m]
    have hgrad : g ^ 2 ≤ q + a * m ^ 2 := by
      rw [hq]
      nlinarith [sq_nonneg m]
    have hmass : d * m ^ 2 ≤ c * q + C * k ^ 2 := by
      rw [hq]
      dsimp [d, a]
      nlinarith [hcore]
    have hbase : d * n ^ 2 ≤ (1 + c) * q + (1 + a) * C * k ^ 2 := by
      have hnorm' : n ^ 2 ≤ q + (1 + a) * m ^ 2 := by nlinarith [hnorm, hgrad]
      have hnorm'' := mul_le_mul_of_nonneg_left hnorm' hd.le
      have hmass' := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 1 + a)
      dsimp [d]
      nlinarith
    have hbase' : n ^ 2 ≤ L * q + B * k ^ 2 := by
      calc
        n ^ 2 ≤ ((1 + c) * q + (1 + a) * C * k ^ 2) / d :=
          (le_div_iff₀ hd).2 (by simpa only [mul_comm] using hbase)
        _ = L * q + B * k ^ 2 := by dsimp [L, B]; ring
    have hqnorm : q ≤ n * t := by
      dsimp [q, n, t]
      simpa using (re_inner_le_norm (𝕜 := ℂ) x (D.A (lam : ℂ) x))
    have hbase'' : n ^ 2 ≤ L * n * t + B * k ^ 2 := by
      calc
        n ^ 2 ≤ L * q + B * k ^ 2 := hbase'
        _ ≤ L * n * t + B * k ^ 2 := by
          have hLq := mul_le_mul_of_nonneg_left hqnorm hL.le
          nlinarith [hLq]
    have hsquare : 0 ≤ (n - L * t) ^ 2 := sq_nonneg _
    have hfinal : n ^ 2 ≤ L ^ 2 * t ^ 2 + 2 * B * k ^ 2 := by nlinarith [hbase'', hsquare]
    simpa [n, t, k] using hfinal

set_option maxHeartbeats 1000000 in
/-- F2 `spec:fa-resolvent` — P-SPEC.md:236, 370–377. The pencil is invertible and analytically
invertible off the nonnegative real axis; its finite-dimensional kernel gives the local simple-pole
expansion; weak solutions are represented by the mass resolvent; and the kernel projection obeys
the stated norm identity. -/
theorem F2_resolvent (D : FAEnergySpace H G) (K : D.V →L[ℂ] H)
    (hK : IsCompactOperator K) (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hest : ∀ x : D.V, ‖D.M x‖ ^ 2 ≤ c * ‖D.Gr x‖ ^ 2 + C * ‖K x‖ ^ 2) :
    (∀ z : ℂ, ∀ x : D.V,
      inner ℂ x (D.A z x) = (‖D.Gr x‖ ^ 2 : ℂ) - z * (‖D.M x‖ ^ 2 : ℂ)) ∧
    (∀ lam : ℝ,
      IsSelfAdjoint (D.A (lam : ℂ)) ∧
      (lam < 1 / c → (D.A (lam : ℂ)).IsFredholm)) ∧
    (∀ z : ℂ, ¬ (z.im = 0 ∧ 0 ≤ z.re) → IsUnit (D.A z)) ∧
    (AnalyticOnNhd ℂ (faInverse D)
      {z : ℂ | ¬ (z.im = 0 ∧ 0 ≤ z.re)}) ∧
    (∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ < 1 / c →
      let N : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
      FiniteDimensional ℂ N ∧
      (∀ x ∈ N, D.T x = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) • x) ∧
      ∃ (P : D.V →L[ℂ] D.V) (δ : ℝ) (B : ℂ → D.V →L[ℂ] D.V),
        0 < δ ∧ P.comp P = P ∧ P.range = N ∧ IsSelfAdjoint P ∧
        AnalyticOnNhd ℂ B (Metric.ball (lam₁ : ℂ) δ) ∧
        ∀ z ∈ Metric.ball (lam₁ : ℂ) δ, z ≠ (lam₁ : ℂ) →
          IsUnit (D.A z) ∧
          faInverse D z =
            (((lam₁ + 1 : ℝ) : ℂ) * (lam₁ - z)⁻¹) • P + B z) ∧
    (∀ (S : Set D.V), Dense S → ∀ z : ℂ, IsUnit (D.A z) →
      ∀ (x : D.V) (f : H),
        (∀ v ∈ S,
          inner ℂ (D.Gr v) (D.Gr x) - z * inner ℂ (D.M v) (D.M x) =
            inner ℂ (D.M v) f) →
        D.M x = faResolvent D z f) ∧
    (∀ lam₁ : ℝ, 0 ≤ lam₁ → lam₁ < 1 / c →
      let N : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
      ∃ P : D.V →L[ℂ] D.V,
        P.comp P = P ∧ P.range = N ∧ IsSelfAdjoint P ∧
        ∀ G₀ : H,
      (‖D.M (P (D.M.adjoint G₀))‖ ^ 2 : ℂ) =
            (((lam₁ + 1)⁻¹ : ℝ) : ℂ) *
              inner ℂ G₀ (D.M (P (D.M.adjoint G₀)))) := by
  have hF1 := F1_fredholm D K hK c C hc hC hest
  refine ⟨hF1.1, hF1.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact faA_off_cut_isUnit D z hz
  · intro z hz
    exact faInverse_analyticAt_of_isUnit D z (faA_off_cut_isUnit D z hz)
  · intro lam₁ hlam₁ hlt₁
    let N₀ : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
    have hfred : (D.A (lam₁ : ℂ)).IsFredholm := (hF1.2 lam₁).2 hlt₁
    have hNclosed : IsClosed (N₀ : Set D.V) := by
      change IsClosed ((D.A (lam₁ : ℂ)).toLinearMap.ker : Set D.V)
      exact (D.A (lam₁ : ℂ)).isClosed_ker
    letI : CompleteSpace N₀ := hNclosed.completeSpace_coe
    letI : N₀.HasOrthogonalProjection := inferInstance
    let R₀ : Submodule ℂ D.V := faRegularSubmodule D lam₁
    letI : CompleteSpace R₀ := faRegularSubmoduleCompleteSpace D lam₁
    letI : R₀.HasOrthogonalProjection := inferInstance
    letI : SeminormedAddCommGroup R₀ := Submodule.seminormedAddCommGroup R₀
    letI : NormedAddCommGroup R₀ := Submodule.normedAddCommGroup R₀
    letI hRnorm : NormedSpace ℂ R₀ := {
      toModule := R₀.module
      norm_smul_le := fun a x => by
        change ‖a • (x : D.V)‖ ≤ ‖a‖ * ‖(x : D.V)‖
        exact norm_smul_le a (x : D.V) }
    letI : Module ℂ R₀ := hRnorm.toModule
    letI : SMulCommClass ℂ ℂ R₀ := ⟨fun a b x => by
      simp only [smul_smul]
      rw [mul_comm]⟩
    letI : NormedSpace ℂ (R₀ →L[ℂ] R₀) := faEndNormedSpace R₀
    letI : NormedSpace ℂ (faRegularSubmodule D lam₁) :=
      faRegularSubmoduleNormedSpace D lam₁
    letI : SMulCommClass ℂ ℂ (faRegularSubmodule D lam₁) :=
      faRegularSubmoduleSMulCommClass D lam₁
    have hfd : FiniteDimensional ℂ N₀ := by
      change FiniteDimensional ℂ ((D.A (lam₁ : ℂ)).toLinearMap.ker)
      exact hfred.finite_ker
    have heigen : ∀ x ∈ N₀, D.T x = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) • x := by
      intro x hx
      exact faA_kernel_T_eigen D lam₁ hlam₁ x hx
    refine ⟨hfd, heigen, ?_⟩
    let P₀ : D.V →L[ℂ] D.V := N₀.starProjection
    let Treg₀ : R₀ →L[ℂ] R₀ :=
      R₀.orthogonalProjectionOnto.comp (D.T.comp R₀.subtypeL)
    let Areg₀ : ℂ → R₀ →L[ℂ] R₀ :=
      fun z => ContinuousLinearMap.id ℂ R₀ - (z + 1) • Treg₀
    have hTregCo (v : R₀) : ((Treg₀ v : R₀) : D.V) = D.T v := by
      change R₀.starProjection (D.T v) = D.T v
      exact R₀.starProjection_eq_self_iff.mpr
        (faT_preserves_kernel_orthogonal D lam₁ hlam₁ v v.2)
    have hAregCo (z : ℂ) (v : R₀) : ((Areg₀ z v : R₀) : D.V) = D.A z v := by
      change (v : D.V) - (z + 1) • ((Treg₀ v : R₀) : D.V) = _
      rw [hTregCo]
      rfl
    have hAregAnalytic (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => Areg₀ w) z := by
      have hscale : AnalyticAt ℂ (fun w : ℂ => w • Treg₀) (z + 1) := by
        simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] using!
          (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
            (F := R₀ →L[ℂ] R₀)
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) Treg₀) (z + 1))
      have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1) z :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_const.sub (hscale.comp_of_eq hshift rfl)
    have hregCenter : IsUnit (Areg₀ (lam₁ : ℂ)) := by
      apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := R₀)).mpr
      constructor
      · intro v w hvw
        apply Subtype.ext
        have hfull : D.A (lam₁ : ℂ) (v : D.V) = D.A (lam₁ : ℂ) (w : D.V) := by
          calc
            _ = ((Areg₀ (lam₁ : ℂ) v : R₀) : D.V) := (hAregCo _ _).symm
            _ = ((Areg₀ (lam₁ : ℂ) w : R₀) : D.V) := congrArg Subtype.val hvw
            _ = _ := hAregCo _ _
        have hker : (v.1 - w.1) ∈ N₀ := by
          change (D.A (lam₁ : ℂ)).toLinearMap (v.1 - w.1) = 0
          have hfullLin : (D.A (lam₁ : ℂ)).toLinearMap v.1 =
              (D.A (lam₁ : ℂ)).toLinearMap w.1 := hfull
          rw [map_sub, hfullLin, sub_self]
        have horth : (v.1 - w.1) ∈ R₀ := R₀.sub_mem v.2 w.2
        have hzero : inner ℂ (v.1 - w.1) (v.1 - w.1) = 0 := horth _ hker
        exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hzero)
      · intro y
        have hrange : (D.A (lam₁ : ℂ)).range = R₀ := by
          exact OAI.CubicEisenstein.selfAdjoint_range_eq_ker_orthogonal
            (D.A (lam₁ : ℂ)) (faA_real_selfAdjoint D lam₁) hfred.isClosed_range
        have hy : (y : D.V) ∈ (D.A (lam₁ : ℂ)).range := by
          rw [hrange]
          exact y.2
        obtain ⟨x, hx⟩ := hy
        have hxCLM : D.A (lam₁ : ℂ) x = y := by
          simpa only [ContinuousLinearMap.coe_coe] using hx
        let x' : R₀ := ⟨x - P₀ x, N₀.sub_starProjection_mem_orthogonal x⟩
        have hPx : P₀ x ∈ N₀ := N₀.starProjection_apply_mem x
        have hkill : D.A (lam₁ : ℂ) (P₀ x) = 0 := hPx
        have hx' : D.A (lam₁ : ℂ) (x - P₀ x) = y := by
          rw [map_sub, hxCLM, hkill, sub_zero]
        refine ⟨x', ?_⟩
        apply Subtype.ext
        calc
          ((Areg₀ (lam₁ : ℂ) x' : R₀) : D.V) = D.A (lam₁ : ℂ) x' := hAregCo _ _
          _ = y := by exact hx'
    have hAregContinuous : Continuous (fun z : ℂ => Areg₀ z) :=
      continuous_iff_continuousAt.mpr (fun z => (hAregAnalytic z).continuousAt)
    have hUnitOpen : IsOpen {z : ℂ | IsUnit (Areg₀ z)} :=
      (Units.isOpen (R := R₀ →L[ℂ] R₀)).preimage hAregContinuous
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hUnitOpen (lam₁ : ℂ) hregCenter
    let inclusion : R₀ →L[ℂ] D.V := {
      toLinearMap := {
        toFun := fun x => (x : D.V)
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
      cont := continuous_subtype_val }
    let projection : D.V →L[ℂ] R₀ := {
      toLinearMap := {
        toFun := fun x => R₀.orthogonalProjectionOnto x
        map_add' := by
          intro x y
          apply Subtype.ext
          change R₀.starProjection (x + y) = R₀.starProjection x + R₀.starProjection y
          simp [map_add]
        map_smul' := by
          intro a x
          apply Subtype.ext
          change R₀.starProjection (a • x) = a • R₀.starProjection x
          simp [map_smul] }
      cont := R₀.orthogonalProjectionOnto.continuous }
    let lift : (faRegularSubmodule D lam₁ →L[ℂ] faRegularSubmodule D lam₁) →L[ℂ]
        (D.V →L[ℂ] D.V) :=
      @faContinuousLinearSandwich R₀ D.V (inferInstance) hRnorm (inferInstance) (inferInstance)
        inclusion projection
    let B₀ : ℂ → D.V →L[ℂ] D.V := fun z => lift (Ring.inverse (Areg₀ z))
    have hBinvAt (z : ℂ) (hz : IsUnit (Areg₀ z)) :
        AnalyticAt ℂ (fun w : ℂ => Ring.inverse (Areg₀ w)) z := by
      have hinv := (analyticOnNhd_inverse (𝕜 := ℂ)
        (A := R₀ →L[ℂ] R₀)) (Areg₀ z) hz
      exact hinv.comp_of_eq (hAregAnalytic z) rfl
    have hBanalyticAt (z : ℂ) (hz : IsUnit (Areg₀ z)) : AnalyticAt ℂ B₀ z := by
      exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
        (E := R₀ →L[ℂ] R₀) (F := D.V →L[ℂ] D.V) lift
        (Ring.inverse (Areg₀ z))).comp_of_eq (hBinvAt z hz) rfl
    have hBanalytic : AnalyticOnNhd ℂ B₀ (Metric.ball (lam₁ : ℂ) δ) := by
      intro z hz
      exact hBanalyticAt z (hball hz)
    have hdecomp (x : D.V) : P₀ x + R₀.starProjection x = x := by
      change N₀.starProjection x + N₀ᗮ.starProjection x = x
      exact N₀.starProjection_add_starProjection_orthogonal x
    have hLam1Pos : 0 < lam₁ + 1 := by linarith
    have hden : ((lam₁ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLam1Pos.ne'
    have hscalar (z : ℂ) :
        1 - (z + 1) * (((lam₁ + 1)⁻¹ : ℝ) : ℂ) =
          (((lam₁ : ℂ) - z) / ((lam₁ + 1 : ℝ) : ℂ)) := by
      have hinv : (((lam₁ + 1)⁻¹ : ℝ) : ℂ) = (((lam₁ + 1 : ℝ) : ℂ)⁻¹) := by simp
      rw [hinv]
      field_simp [hden]
      simp only [Complex.ofReal_add, Complex.ofReal_one]
      ring
    have hAonP (z : ℂ) (x : D.V) :
        D.A z (P₀ x) = (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x := by
      change P₀ x - (z + 1) • D.T (P₀ x) = _
      rw [faA_kernel_T_eigen D lam₁ hlam₁ (P₀ x) (N₀.starProjection_apply_mem x)]
      rw [smul_smul]
      let b : ℂ := (z + 1) * (((lam₁ + 1)⁻¹ : ℝ) : ℂ)
      change P₀ x - b • P₀ x = (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x
      calc
        P₀ x - b • P₀ x = (1 - b) • P₀ x := by
          calc
            _ = (1 : ℂ) • P₀ x - b • P₀ x := by simp
            _ = _ := by rw [← sub_smul]
        _ = (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x := by
          simpa [b] using congrArg (fun a : ℂ => a • P₀ x) (hscalar z)
    have hPzero (x : D.V) (hx : x ∈ R₀) : P₀ x = 0 := by
      change (N₀.orthogonalProjectionOnto x : D.V) = 0
      exact congrArg Subtype.val (N₀.orthogonalProjectionOnto_apply_of_mem_orthogonal hx)
    have hAqmem (z : ℂ) (x : D.V) : D.A z (R₀.starProjection x) ∈ R₀ := by
      change D.A z ((R₀.orthogonalProjectionOnto x : R₀) : D.V) ∈ R₀
      rw [← hAregCo z (R₀.orthogonalProjectionOnto x)]
      exact SetLike.coe_mem _
    have hPA (z : ℂ) (x : D.V) :
        P₀ (D.A z x) = (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x := by
      calc
        P₀ (D.A z x) = P₀ (D.A z (P₀ x + R₀.starProjection x)) := by
          exact congrArg (fun y : D.V => P₀ (D.A z y)) (hdecomp x).symm
        _ = P₀ (D.A z (P₀ x) + D.A z (R₀.starProjection x)) := by rw [map_add]
        _ = P₀ (D.A z (P₀ x)) + P₀ (D.A z (R₀.starProjection x)) := by rw [map_add]
        _ = (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x := by
          have hPfirst : P₀ (D.A z (P₀ x)) =
              (((lam₁ : ℂ) - z) / (lam₁ + 1)) • P₀ x := by
            rw [hAonP z x, map_smul,
              N₀.starProjection_eq_self_iff.mpr (N₀.starProjection_apply_mem x)]
          have hPsecond : P₀ (D.A z (R₀.starProjection x)) = 0 :=
            hPzero _ (hAqmem z x)
          rw [hPfirst, hPsecond, add_zero]
    have hprojA (z : ℂ) (x : D.V) :
        R₀.starProjection (D.A z x) =
          ((Areg₀ z (R₀.orthogonalProjectionOnto x) : R₀) : D.V) := by
      have hAsplit : D.A z x = D.A z (P₀ x) + D.A z (R₀.starProjection x) := by
        calc
          D.A z x = D.A z (P₀ x + R₀.starProjection x) :=
            congrArg (D.A z) (hdecomp x).symm
          _ = D.A z (P₀ x) + D.A z (R₀.starProjection x) := map_add _ _ _
      have hAPmem : D.A z (P₀ x) ∈ N₀ := by
        rw [hAonP z x]
        exact N₀.smul_mem _ (N₀.starProjection_apply_mem x)
      have hAPorth : D.A z (P₀ x) ∈ R₀ᗮ :=
        N₀.le_orthogonal_orthogonal hAPmem
      have hRprojAP : R₀.starProjection (D.A z (P₀ x)) = 0 := by
        have h := R₀.orthogonalProjectionOnto_apply_of_mem_orthogonal hAPorth
        exact congrArg Subtype.val h
      have hRprojAq : R₀.starProjection (D.A z (R₀.starProjection x)) =
          D.A z (R₀.starProjection x) :=
        R₀.starProjection_eq_self_iff.mpr (hAqmem z x)
      calc
        R₀.starProjection (D.A z x) =
            R₀.starProjection (D.A z (P₀ x) + D.A z (R₀.starProjection x)) :=
              congrArg R₀.starProjection hAsplit
        _ = D.A z (R₀.starProjection x) := by rw [map_add, hRprojAP, hRprojAq, zero_add]
        _ = ((Areg₀ z (R₀.orthogonalProjectionOnto x) : R₀) : D.V) := by
          change D.A z ((R₀.orthogonalProjectionOnto x : R₀) : D.V) = _
          exact (hAregCo z (R₀.orthogonalProjectionOnto x)).symm
    refine ⟨P₀, δ, B₀, hδ, ?_, ?_, ?_, hBanalytic, ?_⟩
    · ext x
      simpa [P₀, ContinuousLinearMap.comp_apply] using
        N₀.starProjection_eq_self_iff.mpr (N₀.starProjection_apply_mem x)
    · change N₀.starProjection.range = N₀
      exact N₀.range_starProjection
    · simpa [P₀] using isSelfAdjoint_starProjection N₀
    · intro z hzball hzne
      have hzreg : IsUnit (Areg₀ z) := hball hzball
      have hBapply (x : D.V) :
          B₀ z x = inclusion (Ring.inverse (Areg₀ z) (projection x)) := by
        rfl
      have hregRight (v : R₀) :
          Areg₀ z (Ring.inverse (Areg₀ z) v) = v := by
        have h := congrArg (fun f : R₀ →L[ℂ] R₀ => f v)
          (Ring.mul_inverse_cancel (Areg₀ z) hzreg)
        exact h
      have hregLeft (v : R₀) :
          Ring.inverse (Areg₀ z) (Areg₀ z v) = v := by
        have h := congrArg (fun f : R₀ →L[ℂ] R₀ => f v)
          (Ring.inverse_mul_cancel (Areg₀ z) hzreg)
        exact h
      have hAB (x : D.V) : D.A z (B₀ z x) = R₀.starProjection x := by
        calc
          D.A z (B₀ z x) = D.A z (inclusion (Ring.inverse (Areg₀ z) (projection x))) :=
            congrArg (D.A z) (hBapply x)
          _ = ((Areg₀ z (Ring.inverse (Areg₀ z) (projection x)) : R₀) : D.V) :=
            (hAregCo z _).symm
          _ = (projection x : D.V) := congrArg Subtype.val (hregRight (projection x))
          _ = R₀.starProjection x := rfl
      have hprojA' (x : D.V) : projection (D.A z x) = Areg₀ z (projection x) := by
        apply Subtype.ext
        exact hprojA z x
      have hBA (x : D.V) : B₀ z (D.A z x) = R₀.starProjection x := by
        calc
          B₀ z (D.A z x) = inclusion (Ring.inverse (Areg₀ z) (projection (D.A z x))) :=
            hBapply _
          _ = inclusion (Ring.inverse (Areg₀ z) (Areg₀ z (projection x))) := by rw [hprojA']
          _ = inclusion (projection x) := congrArg inclusion (hregLeft (projection x))
          _ = R₀.starProjection x := rfl
      let qcoef : ℂ := (((lam₁ + 1 : ℝ) : ℂ) * (lam₁ - z)⁻¹)
      have hcoef : qcoef * (((lam₁ : ℂ) - z) / (lam₁ + 1)) = 1 := by
        dsimp [qcoef]
        push_cast
        have hden' : (lam₁ : ℂ) + 1 ≠ 0 := by exact_mod_cast hLam1Pos.ne'
        field_simp [hden', sub_ne_zero.mpr hzne]
      let Qz : D.V →L[ℂ] D.V := qcoef • P₀ + B₀ z
      have hAQ (x : D.V) : D.A z (Qz x) = x := by
        change D.A z (qcoef • P₀ x + B₀ z x) = x
        rw [map_add, map_smul, hAonP z x, smul_smul, hcoef, one_smul, hAB]
        exact hdecomp x
      have hQA (x : D.V) : Qz (D.A z x) = x := by
        change qcoef • P₀ (D.A z x) + B₀ z (D.A z x) = x
        rw [hPA z x, smul_smul, hcoef, one_smul, hBA]
        exact hdecomp x
      have hAunit : IsUnit (D.A z) := by
        apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := D.V)).mpr
        refine ⟨?_, ?_⟩
        · intro x y hxy
          have hQ := congrArg Qz hxy
          calc
            x = Qz (D.A z x) := (hQA x).symm
            _ = Qz (D.A z y) := hQ
            _ = y := hQA y
        · intro y
          exact ⟨Qz y, hAQ y⟩
      have hInvEq : Ring.inverse (D.A z) = Qz := by
        apply ContinuousLinearMap.ext
        intro x
        have h := congrArg (fun f : D.V →L[ℂ] D.V => f (Qz x))
          (Ring.inverse_mul_cancel (D.A z) hAunit)
        have hApp : Ring.inverse (D.A z) (D.A z (Qz x)) = Qz x := by
          simpa using h
        calc
          Ring.inverse (D.A z) x = Ring.inverse (D.A z) (D.A z (Qz x)) :=
            congrArg (fun y : D.V => Ring.inverse (D.A z) y) (hAQ x).symm
          _ = Qz x := hApp
      refine ⟨hAunit, ?_⟩
      rw [faInverse_eq_ringInverse D z hAunit]
      simpa [Qz, qcoef] using hInvEq
  · intro S hS z hz x f hweak
    let w : D.V := D.A z x - D.M.adjoint f
    have hzeroOn : ∀ v ∈ S, inner ℂ v w = 0 := by
      intro v hv
      change inner ℂ v (D.A z x - D.M.adjoint f) = 0
      rw [inner_sub_right, faA_inner_polarized, D.M.adjoint_inner_right, hweak v hv]
      ring
    let Z : Set D.V := {v | inner ℂ v w = 0}
    have hZclosed : IsClosed Z := by
      change IsClosed ((fun v : D.V => inner ℂ v w) ⁻¹' ({0} : Set ℂ))
      have hconst : Continuous (fun _ : D.V => w) := continuous_const
      exact isClosed_singleton.preimage <| continuous_inner.comp
        ((continuous_id : Continuous fun x : D.V => x).prodMk hconst)
    have hSsub : S ⊆ Z := fun v hv => hzeroOn v hv
    have hwmem : w ∈ closure S := by
      rw [hS.closure_eq]
      simp
    have hwzero : inner ℂ w w = 0 :=
      (hZclosed.closure_subset_iff.mpr hSsub) hwmem
    have hw : w = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hwzero
    have hAx : D.A z x = D.M.adjoint f := by
      have h : D.A z x - D.M.adjoint f = 0 := by simpa [w] using hw
      exact sub_eq_zero.mp h
    have hinv : faInverse D z (D.A z x) = x := by
      rw [faInverse_eq_ringInverse D z hz]
      exact congrArg (fun T : D.V →L[ℂ] D.V => T x)
        (Ring.inverse_mul_cancel (D.A z) hz)
    change D.M x = D.M (faInverse D z (D.M.adjoint f))
    rw [← hAx, hinv]
  · intro lam₁ hlam₁ hlt₁
    let N₁ : Submodule ℂ D.V := (D.A (lam₁ : ℂ)).toLinearMap.ker
    have hNclosed : IsClosed (N₁ : Set D.V) := by
      change IsClosed ((D.A (lam₁ : ℂ)).toLinearMap.ker : Set D.V)
      exact (D.A (lam₁ : ℂ)).isClosed_ker
    letI : CompleteSpace N₁ := hNclosed.completeSpace_coe
    letI : N₁.HasOrthogonalProjection := inferInstance
    let P₁ : D.V →L[ℂ] D.V := N₁.starProjection
    refine ⟨P₁, ?_, ?_, ?_, ?_⟩
    · ext x
      simpa [P₁, ContinuousLinearMap.comp_apply] using
        N₁.starProjection_eq_self_iff.mpr (N₁.starProjection_apply_mem x)
    · change N₁.starProjection.range = N₁
      exact N₁.range_starProjection
    · simpa [P₁] using isSelfAdjoint_starProjection N₁
    · intro G₀
      let x : D.V := P₁ (D.M.adjoint G₀)
      have hxN : x ∈ N₁ := by dsimp [x, P₁]; exact N₁.starProjection_apply_mem _
      have hT : D.T x = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) • x :=
        faA_kernel_T_eigen D lam₁ hlam₁ x hxN
      have hmNorm : inner ℂ (D.M x) (D.M x) = (‖D.M x‖ ^ 2 : ℂ) :=
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (D.M x)
      have hxNorm : inner ℂ x x = (‖x‖ ^ 2 : ℂ) :=
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
      have hmass : (‖D.M x‖ ^ 2 : ℂ) =
          (((lam₁ + 1)⁻¹ : ℝ) : ℂ) * (‖x‖ ^ 2 : ℂ) := by
        calc
          (‖D.M x‖ ^ 2 : ℂ) = inner ℂ (D.M x) (D.M x) := hmNorm.symm
          _ = inner ℂ x (D.T x) := (faT_inner D x x).symm
          _ = inner ℂ x ((((lam₁ + 1)⁻¹ : ℝ) : ℂ) • x) := by rw [hT]
          _ = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) * inner ℂ x x := by
            rw [inner_smul_right x x (((lam₁ + 1)⁻¹ : ℝ) : ℂ)]
          _ = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) * (‖x‖ ^ 2 : ℂ) := by rw [hxNorm]
      have hPx : N₁.starProjection x = x :=
        N₁.starProjection_eq_self_iff.mpr hxN
      have hProjInner : inner ℂ G₀ (D.M x) = (‖x‖ ^ 2 : ℂ) := by
        have hProjSymm : inner ℂ x x = inner ℂ (D.M.adjoint G₀) x := by
          have h := N₁.inner_starProjection_left_eq_right (D.M.adjoint G₀) x
          simpa [x, P₁, hPx] using h
        calc
          inner ℂ G₀ (D.M x) = inner ℂ (D.M.adjoint G₀) x := by
            simpa only [ContinuousLinearMap.coe_coe] using
              (ContinuousLinearMap.adjoint_inner_left D.M x G₀).symm
          _ = inner ℂ x x := hProjSymm.symm
          _ = (‖x‖ ^ 2 : ℂ) := hxNorm
      calc
        (‖D.M x‖ ^ 2 : ℂ) = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) * (‖x‖ ^ 2 : ℂ) := hmass
        _ = (((lam₁ + 1)⁻¹ : ℝ) : ℂ) * inner ℂ G₀ (D.M x) := by rw [← hProjInner]

end ArtinPrimitiveRoots.A1.Spec
