import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.LocalParameterNorms
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol.e_d
open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private def termExponent (i : Fin 2 × ℕ × ℕ × ℕ) (p : Triple) : ℂ :=
  -(i.1.1 : ℂ) * (1 / 2 + p 0) - (i.2.1 : ℂ) * (1 + 3 * p 0) -
    (i.2.2.1 : ℂ) * p 1 - 6 * (i.2.2.2 : ℂ) * p 2

private def termExponentReal (i : Fin 2 × ℕ × ℕ × ℕ) (p : Triple) : ℝ :=
  -(i.1.1 : ℝ) * (1 / 2 + (p 0).re) - (i.2.1 : ℝ) * (1 + 3 * (p 0).re) -
    (i.2.2.1 : ℝ) * (p 1).re - 6 * (i.2.2.2 : ℝ) * (p 2).re

private def termCoefficient (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  let e := i.1.1
  let l := i.2.1
  let k := i.2.2.1
  let m := i.2.2.2
  let j := frequencyValuation η U u v
  gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e * ϑ.primeValue v ^ (e + 3 * l) *
    chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^ ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
      localC R v hv (e + 3 * l) k (j + 6 * m)

private lemma term_eq (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (i : Fin 2 × ℕ × ℕ × ℕ) (p : Triple) :
    localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i =
      termCoefficient R η U u v hv i *
        (qI v.asIdeal : ℂ) ^ termExponent i p := by
  simp [localEulerTerm, termCoefficient, termExponent]

private lemma termExponent_re (i : Fin 2 × ℕ × ℕ × ℕ) (p : Triple) :
    (termExponent i p).re = termExponentReal i p := by
  simp [termExponent, termExponentReal]

private lemma termExponentReal_antitone (i : Fin 2 × ℕ × ℕ × ℕ)
    {p₀ p : Triple} (hξ : (p₀ 0).re ≤ (p 0).re)
    (hw : (p₀ 1).re ≤ (p 1).re) (hz : (p₀ 2).re ≤ (p 2).re) :
    termExponentReal i p ≤ termExponentReal i p₀ := by
  have he : 0 ≤ (i.1.1 : ℝ) := by positivity
  have hl : 0 ≤ (i.2.1 : ℝ) := by positivity
  have hk : 0 ≤ (i.2.2.1 : ℝ) := by positivity
  have hm : 0 ≤ (i.2.2.2 : ℝ) := by positivity
  have heArg : 1 / 2 + (p₀ 0).re ≤ 1 / 2 + (p 0).re := by linarith
  have hlArg : 1 + 3 * (p₀ 0).re ≤ 1 + 3 * (p 0).re := by linarith
  have heTerm : -(i.1.1 : ℝ) * (1 / 2 + (p 0).re) ≤
      -(i.1.1 : ℝ) * (1 / 2 + (p₀ 0).re) :=
    mul_le_mul_of_nonpos_left heArg (by linarith)
  have hlTerm : -(i.2.1 : ℝ) * (1 + 3 * (p 0).re) ≤
      -(i.2.1 : ℝ) * (1 + 3 * (p₀ 0).re) :=
    mul_le_mul_of_nonpos_left hlArg (by linarith)
  have hkTerm : -(i.2.2.1 : ℝ) * (p 1).re ≤
      -(i.2.2.1 : ℝ) * (p₀ 1).re :=
    mul_le_mul_of_nonpos_left hw (by linarith)
  have hmTerm : -(6 * (i.2.2.2 : ℝ)) * (p 2).re ≤
      -(6 * (i.2.2.2 : ℝ)) * (p₀ 2).re :=
    mul_le_mul_of_nonpos_left hz (by nlinarith [show 0 ≤ (i.2.2.2 : ℝ) by positivity])
  dsimp [termExponentReal]
  linarith

private lemma term_norm_eq (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (i : Fin 2 × ℕ × ℕ × ℕ) (p : Triple) :
    ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖ =
      ‖termCoefficient R η U u v hv i‖ * qI v.asIdeal ^ termExponentReal i p := by
  rw [term_eq, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
    (by linarith [qI_prime_gt_one v] : 0 < qI v.asIdeal), termExponent_re]

private theorem term_differentiable (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    Differentiable ℂ (fun p : Triple =>
      localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i) := by
  have hq : (qI v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (lt_trans (by norm_num : (0 : ℝ) < 1) (qI_prime_gt_one v)))
  have hExp : Differentiable ℂ (termExponent i) := by
    change Differentiable ℂ (fun p : Triple =>
      -(i.1.1 : ℂ) * (1 / 2 + p 0) - (i.2.1 : ℂ) * (1 + 3 * p 0) -
        (i.2.2.1 : ℂ) * p 1 - 6 * (i.2.2.2 : ℂ) * p 2)
    fun_prop
  have hPow : Differentiable ℂ (fun p : Triple =>
      (qI v.asIdeal : ℂ) ^ termExponent i p) :=
    hExp.const_cpow (Or.inl hq)
  have hfun : (fun p : Triple => localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i) =
      fun p => termCoefficient R η U u v hv i *
        (qI v.asIdeal : ℂ) ^ termExponent i p := by
    funext p
    exact term_eq R η U u v hv i p
  rw [hfun]
  exact (differentiable_const _).mul hPow

private lemma term_norm_mono (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (i : Fin 2 × ℕ × ℕ × ℕ) {p₀ p : Triple}
    (hξ : (p₀ 0).re ≤ (p 0).re) (hw : (p₀ 1).re ≤ (p 1).re)
    (hz : (p₀ 2).re ≤ (p 2).re) :
    ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖ ≤
      ‖localEulerTerm R η U u v hv (p₀ 0) (p₀ 1) (p₀ 2) i‖ := by
  rw [term_norm_eq, term_norm_eq]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le
    (by linarith [qI_prime_gt_one v]) (termExponentReal_antitone i hξ hw hz)

private lemma real_coord_lower {p q : Triple} {r : ℝ} (hr : dist q p < r)
    (j : Fin 3) : (p j).re - r < (q j).re := by
  have hcoord : |(q j).re - (p j).re| ≤ dist q p := by
    calc
      |(q j).re - (p j).re| = |(q j - p j).re| := by simp
      _ ≤ ‖q j - p j‖ := Complex.abs_re_le_norm _
      _ ≤ ‖q - p‖ := norm_le_pi_norm (q - p) j
      _ = dist q p := (dist_eq_norm q p).symm
  have hleft := (abs_le.mp hcoord).1
  linarith

private lemma eulerNeighborhood_isOpen : IsOpen {p : Triple | eulerNeighborhood p} := by
  have h0 : Continuous fun p : Triple => (p 0).re :=
    Complex.continuous_re.comp (continuous_apply 0)
  have h1 : Continuous fun p : Triple => (p 1).re :=
    Complex.continuous_re.comp (continuous_apply 1)
  have h2 : Continuous fun p : Triple => (p 2).re :=
    Complex.continuous_re.comp (continuous_apply 2)
  have hξ₁ : IsOpen {p : Triple | (998 / 1000 - 1 / 100000 : ℝ) < (p 0).re} :=
    isOpen_lt continuous_const h0
  have hw₁ : IsOpen {p : Triple | (3 / 1000 - 1 / 100000 : ℝ) < (p 1).re} :=
    isOpen_lt continuous_const h1
  have hz₁ : IsOpen {p : Triple | (4 / 10 - 1 / 100000 : ℝ) < (p 2).re} :=
    isOpen_lt continuous_const h2
  have hξ₂ : IsOpen {p : Triple | (998 / 1000 - 1 / 100000 : ℝ) < (p 0).re} :=
    isOpen_lt continuous_const h0
  have hw₂ : IsOpen {p : Triple | (95 / 100 - 1 / 100000 : ℝ) < (p 1).re} :=
    isOpen_lt continuous_const h1
  have hz₂ : IsOpen {p : Triple | (16 / 100 - 1 / 100000 : ℝ) < (p 2).re} :=
    isOpen_lt continuous_const h2
  unfold eulerNeighborhood
  simpa only [Set.ofPred_and, Set.ofPred_or, Set.inter_assoc] using
    ((hξ₁.inter hw₁).inter hz₁).union ((hξ₂.inter hw₂).inter hz₂)

private theorem localEuler_differentiableAt (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (hs : ∀ p, eulerNeighborhood p → Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖))
    (p : Triple) (hp : eulerNeighborhood p) :
    DifferentiableAt ℂ (fun q : Triple => localEuler R η U u v hv (q 0) (q 1) (q 2)) p := by
  let f : (Fin 2 × ℕ × ℕ × ℕ) → Triple → ℂ := fun i q =>
    localEulerTerm R η U u v hv (q 0) (q 1) (q 2) i
  have hf : ∀ i, Differentiable ℂ (f i) := by
    intro i
    exact term_differentiable R η U u v hv i
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp eulerNeighborhood_isOpen p hp
  let ρ : ℝ := ε / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let p₀ : Triple := fun j => p j - ((ε / 2 : ℝ) : ℂ)
  have hshift : dist p₀ p ≤ ε / 2 := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ε / 2)).2
    intro j
    simp [p₀]
    rw [abs_of_pos hε]
  have hp₀ : eulerNeighborhood p₀ := by
    apply hball
    apply Metric.mem_ball.mpr
    linarith
  have hM : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ => ‖f i p₀‖) := by
    simpa [f] using hs p₀ hp₀
  let B : ℝ := 4 / ρ
  have hsumDeriv : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ => B * ‖f i p₀‖) :=
    hM.mul_left B
  have hderivBound (i : Fin 2 × ℕ × ℕ × ℕ) (x : Triple)
      (hx : x ∈ Metric.ball p (ρ / 2)) : ‖fderiv ℂ (f i) x‖ ≤ B * ‖f i p₀‖ := by
    have hxDist : dist x p < ρ / 2 := Metric.mem_ball.mp hx
    have hcoordX : ∀ j : Fin 3, (p₀ j).re ≤ (x j).re := by
      intro j
      have hj := real_coord_lower hxDist j
      have hshift' : ε / 2 = 2 * ρ := by dsimp [ρ]; ring
      dsimp [p₀]
      linarith
    have hxBound : ‖f i x‖ ≤ ‖f i p₀‖ := by
      exact term_norm_mono R η U u v hv i (hcoordX 0) (hcoordX 1) (hcoordX 2)
    have hmaps : Set.MapsTo (f i) (Metric.ball x (ρ / 2))
        (Metric.closedBall (f i x) (2 * ‖f i p₀‖)) := by
      intro y hy
      have hyDist : dist y x < ρ / 2 := Metric.mem_ball.mp hy
      have hyBig : dist y p < ρ := by
        have htri := dist_triangle y x p
        dsimp [ρ] at *
        linarith
      have hcoordY : ∀ j : Fin 3, (p₀ j).re ≤ (y j).re := by
        intro j
        have hj := real_coord_lower hyBig j
        have hshift' : ε / 2 = 2 * ρ := by dsimp [ρ]; ring
        dsimp [p₀]
        linarith
      have hyBound : ‖f i y‖ ≤ ‖f i p₀‖ := by
        exact term_norm_mono R η U u v hv i (hcoordY 0) (hcoordY 1) (hcoordY 2)
      apply Metric.mem_closedBall.mpr
      rw [dist_eq_norm]
      calc
        ‖f i y - f i x‖ ≤ ‖f i y‖ + ‖f i x‖ := norm_sub_le _ _
        _ ≤ ‖f i p₀‖ + ‖f i p₀‖ := add_le_add hyBound hxBound
        _ = 2 * ‖f i p₀‖ := by ring
    have hschwarz := Complex.norm_fderiv_le_div_of_mapsTo_ball
      (fun y _ => (hf i y).differentiableWithinAt) hmaps (by positivity : 0 < ρ / 2)
    calc
      ‖fderiv ℂ (f i) x‖ ≤ (2 * ‖f i p₀‖) / (ρ / 2) := hschwarz
      _ = B * ‖f i p₀‖ := by dsimp [B]; field_simp; ring
  let s : Set Triple := Metric.ball p (ρ / 2)
  have hsOpen : IsOpen s := Metric.isOpen_ball
  have hsumUniform : TendstoUniformlyOn
      (fun t : Finset (Fin 2 × ℕ × ℕ × ℕ) => fun q => ∑ i ∈ t, fderiv ℂ (f i) q)
      (fun q => ∑' i, fderiv ℂ (f i) q) atTop s :=
    tendstoUniformlyOn_tsum hsumDeriv hderivBound
  have hdom : ∀ q, q ∈ s → eulerNeighborhood q := by
    intro q hq
    apply hball
    apply Metric.mem_ball.mpr
    have hdist := Metric.mem_ball.mp hq
    dsimp [ρ] at *
    linarith
  have hpoint : ∀ q, q ∈ s →
      Tendsto (fun t : Finset (Fin 2 × ℕ × ℕ × ℕ) => ∑ i ∈ t, f i q) atTop
        (𝓝 (∑' i, f i q)) := by
    intro q hq
    exact ((hs q (hdom q hq)).of_norm).hasSum
  have hFD : HasFDerivAt (fun q : Triple => ∑' i, f i q)
      (∑' i, fderiv ℂ (f i) p) p := by
    apply hasFDerivAt_of_tendstoUniformlyOn hsOpen hsumUniform
      (fun t q hq => HasFDerivAt.fun_sum fun i hi => (hf i q).hasFDerivAt)
      hpoint
    exact Metric.mem_ball_self (by positivity : 0 < ρ / 2)
  change DifferentiableAt ℂ (fun q : Triple => ∑' i, f i q) p
  exact hFD.differentiableAt

theorem normalizedLocal_differentiableAt (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf)
    (hE : EulerHypotheses R η)
    (hs : ∀ p, eulerNeighborhood p → Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖))
    (p : Triple) (hp : eulerNeighborhood p) :
    DifferentiableAt ℂ (fun q : Triple =>
      normalizedLocal R η U u v hv (q 0) (q 1) (q 2)) p := by
  have hq : (qI v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (lt_trans (by norm_num : (0 : ℝ) < 1) (qI_prime_gt_one v)))
  have hVarg : DifferentiableAt ℂ (fun q : Triple => -6 * q 2) p := by
    fun_prop
  have hV : DifferentiableAt ℂ (fun q : Triple => localV v (q 2)) p := by
    change DifferentiableAt ℂ (fun q : Triple => (qI v.asIdeal : ℂ) ^ (-6 * q 2)) p
    exact hVarg.const_cpow (Or.inl hq)
  have hWarg : DifferentiableAt ℂ (fun q : Triple => -(q 1)) p := by
    fun_prop
  have hWpow : DifferentiableAt ℂ (fun q : Triple =>
      (qI v.asIdeal : ℂ) ^ (-(q 1))) p := hWarg.const_cpow (Or.inl hq)
  have hW : DifferentiableAt ℂ (fun q : Triple =>
      localWvar η U u v (q 1)) p := by
    simpa only [localWvar] using hWpow.const_mul (chi D v (U.repr u : F))
  have hDarg : DifferentiableAt ℂ (fun q : Triple => -(q 0)) p := by
    fun_prop
  have hDpow : DifferentiableAt ℂ (fun q : Triple =>
      (qI v.asIdeal : ℂ) ^ (-(q 0))) p := hDarg.const_cpow (Or.inl hq)
  have hD : DifferentiableAt ℂ (fun q : Triple =>
      localDvar η U u v (q 0)) p := by
    simpa only [localDvar] using hDpow.const_mul
      (η.primeValue v * star (chi D v (U.repr u : F)))
  have hξpos : 0 < (p 0).re := by
    rcases hp with ⟨hξ, _, _⟩ | ⟨hξ, _, _⟩ <;>
      exact lt_trans (by norm_num : (0 : ℝ) < 998 / 1000 - 1 / 100000) hξ
  have hparam := local_parameter_norms R η U hE u v hv (p 0) (p 1) (p 2)
  have hDsmall : ‖localDvar η U u v (p 0)‖ < 1 := by
    apply lt_of_le_of_lt hparam.2.2.1
    exact Real.rpow_lt_one_of_one_lt_of_neg (qI_prime_gt_one v) (by linarith)
  have hDne : 1 - localDvar η U u v (p 0) ≠ 0 := by
    intro hz
    have heq : localDvar η U u v (p 0) = 1 := (sub_eq_zero.mp hz).symm
    have hnorm : ‖localDvar η U u v (p 0)‖ = 1 := by rw [heq]; norm_num
    linarith
  have hnum : DifferentiableAt ℂ (fun q : Triple =>
      (1 - localV v (q 2)) * (1 - localWvar η U u v (q 1))) p := by
    exact ((differentiableAt_const (1 : ℂ)).sub hV).mul
      ((differentiableAt_const (1 : ℂ)).sub hW)
  have hden : DifferentiableAt ℂ (fun q : Triple => 1 - localDvar η U u v (q 0)) p :=
    (differentiableAt_const (1 : ℂ)).sub hD
  have hdenInv : DifferentiableAt ℂ (fun q : Triple =>
      (1 - localDvar η U u v (q 0))⁻¹) p := hden.inv hDne
  have hquotMul : DifferentiableAt ℂ (fun q : Triple =>
      ((1 - localV v (q 2)) * (1 - localWvar η U u v (q 1))) *
        (1 - localDvar η U u v (q 0))⁻¹) p := hnum.mul hdenInv
  have hquot : DifferentiableAt ℂ (fun q : Triple =>
      ((1 - localV v (q 2)) * (1 - localWvar η U u v (q 1))) /
        (1 - localDvar η U u v (q 0))) p := by
    simpa only [div_eq_mul_inv] using hquotMul
  have hEuler := localEuler_differentiableAt R η U u v hv hs p hp
  change DifferentiableAt ℂ (fun q : Triple =>
    ((1 - localV v (q 2)) * (1 - localWvar η U u v (q 1)) /
      (1 - localDvar η U u v (q 0))) *
      localEuler R η U u v hv (q 0) (q 1) (q 2)) p
  exact hquot.mul hEuler

end ArtinPrimitiveRoots.Proofs.a2_euler_sol.e_d
