import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.Lead.Contracts
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open ArtinPrimitiveRoots A1 A2
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.pr_e

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : a2_probe_sol.ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

lemma pow_id_X (X : ℝ) (hX : 0 < X) (z : ℂ) :
    (X : ℂ) ^ (1 / 2 : ℂ) * (X : ℂ) ^ (-z) = (X : ℂ) ^ (1 / 2 - z) := by
  have hXpos : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [← Complex.cpow_add _ _ hXpos, sub_eq_add_neg]

lemma pow_id_Y (Y : ℝ) (hY : 0 < Y) (w : ℂ) :
    (Y : ℂ)⁻¹ * (Y : ℂ) ^ w = (Y : ℂ) ^ (w - 1) := by
  have hYpos : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [← Complex.cpow_neg_one, mul_comm, ← Complex.cpow_add _ _ hYpos, sub_eq_add_neg]

lemma pow_id_div (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a / b : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (b : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg ha.le hb.le,
    div_eq_mul_inv, Complex.cpow_neg (Complex.ofReal b) s, inv_inv]

lemma pow_id_qr (qr : ℝ) (hqr : 0 < qr) (z : ℂ) :
    ((qr ^ 6 : ℝ) : ℂ) ^ (-z) = (qr : ℂ) ^ (-6 * z) := by
  have h1 : ((qr ^ 6 : ℝ) : ℂ) = (qr : ℂ) ^ 6 := by
    push_cast; rfl
  rw [h1]
  have harg : (qr : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hqr.le
  have hlt : -Real.pi < (6 : ℝ) * (qr : ℂ).arg := by rw [harg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos
  have hle : (6 : ℝ) * (qr : ℂ).arg ≤ Real.pi := by rw [harg, mul_zero]; exact Real.pi_pos.le
  have hmul := Complex.cpow_nat_mul' (x := (qr : ℂ)) (n := 6) hlt hle (-z)
  rw [← hmul]
  congr 1
  ring

lemma pow_id_qc (qc : ℝ) (hqc : 0 < qc) (ξ : ℂ) :
    ((qc ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (qc : ℂ) ^ (-ξ) = (qc : ℂ) ^ (-1 / 2 - ξ) := by
  have hqcpos : (qc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqc.ne'
  have h1 : ((qc ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (qc : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [Complex.ofReal_cpow hqc.le]
    push_cast; rfl
  rw [h1, ← Complex.cpow_add _ _ hqcpos, sub_eq_add_neg]
  congr 1
  ring

lemma pow_id_qn (qn : ℝ) (hqn : 0 < qn) (ξ : ℂ) :
    (qn : ℂ)⁻¹ * (qn : ℂ) ^ (-3 * ξ) = (qn : ℂ) ^ (-1 - 3 * ξ) := by
  have hqnpos : (qn : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqn.ne'
  rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hqnpos, sub_eq_add_neg]
  congr 1
  ring

lemma pow_id_qA (qc qn : ℝ) (hqc : 0 < qc) (hqn : 0 < qn) (ξ z : ℂ) :
    let qA : ℝ := qc * qn ^ 3
    (qA : ℂ)⁻¹ * (qA : ℂ) ^ (-(ξ + z - 1)) * (qA : ℂ) ^ z =
      (qc : ℂ) ^ (-ξ) * (qn : ℂ) ^ (-3 * ξ) := by
  intro qA
  have hqA : 0 < qA := by dsimp [qA]; positivity
  have hqApos : (qA : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqA.ne'
  rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hqApos, ← Complex.cpow_add _ _ hqApos]
  have h_exp : (-1 : ℂ) + -(ξ + z - 1) + z = -ξ := by ring
  rw [h_exp]
  dsimp [qA]
  have h1 : ((qc * qn ^ 3 : ℝ) : ℂ) = (qc : ℂ) * ((qn ^ 3 : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, Complex.mul_cpow_ofReal_nonneg hqc.le (by positivity)]
  congr 1
  have h2 : ((qn ^ 3 : ℝ) : ℂ) = (qn : ℂ) ^ 3 := by push_cast; rfl
  rw [h2]
  have harg : (qn : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hqn.le
  have hlt : -Real.pi < (3 : ℝ) * (qn : ℂ).arg := by rw [harg, mul_zero]; exact neg_lt_zero.mpr Real.pi_pos
  have hle : (3 : ℝ) * (qn : ℂ).arg ≤ Real.pi := by rw [harg, mul_zero]; exact Real.pi_pos.le
  have hmul := Complex.cpow_nat_mul' (x := (qn : ℂ)) (n := 3) hlt hle (-ξ)
  rw [← hmul]
  congr 1
  ring

lemma pow_id_3mul (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (s : ℂ) :
    ((a * b * c : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (b : ℂ) ^ (-s) * (c : ℂ) ^ (-s) := by
  have hab : 0 < a * b := mul_pos ha hb
  have h1 : ((a * b * c : ℝ) : ℂ) = ((a * b : ℝ) : ℂ) * (c : ℂ) := by push_cast; rfl
  rw [h1, Complex.mul_cpow_ofReal_nonneg hab.le hc.le]
  have h2 : ((a * b : ℝ) : ℂ) = (a : ℂ) * (b : ℂ) := by push_cast; rfl
  rw [h2, Complex.mul_cpow_ofReal_nonneg ha.le hb.le]

lemma pow_id_XY (X Y : ℝ) (hX : 0 < X) :
    ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) = (X : ℂ) ^ (1 / 2 : ℂ) * (Y : ℂ)⁻¹ := by
  have h1 : ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) = ((X ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (Y : ℂ)⁻¹ := by
    push_cast; rfl
  rw [h1, Complex.ofReal_cpow hX.le]
  push_cast; rfl

lemma div_div_cast (a b c : ℝ) :
    ((a / b / c : ℝ) : ℂ) = (a : ℂ) * (b : ℂ)⁻¹ * (c : ℂ)⁻¹ := by
  push_cast
  ring

lemma qI_pos_of_ne_bot (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : 0 < qI I := by
  dsimp [qI]
  exact_mod_cast (Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)))

lemma qI_Aideal (c : S.SqfExtIdeal) (n : S.ExtIdeal) :
    qI (Aideal R c n).1 = qI c.1 * qI n.1 ^ 3 := by
  dsimp [Aideal]
  rw [R.exterior.mul_val, R.exterior.ofSqf_val, R.exterior.pow_val]
  dsimp [qI]
  rw [map_mul, map_pow]
  push_cast
  rfl

lemma integral_shear_swap (k g : ℝ → ℂ)
    (hInt : Integrable (fun p : ℝ × ℝ => k (p.1 + p.2) * g p.2) (volume.prod volume)) :
    (∫ tξ : ℝ, ∫ tz : ℝ, k (tξ + tz) * g tz) = (∫ s : ℝ, k s) * (∫ tz : ℝ, g tz) := by
  rw [integral_integral_swap hInt]
  have hinner (tz : ℝ) : (∫ tξ : ℝ, k (tξ + tz) * g tz) = (∫ s : ℝ, k s) * g tz := by
    rw [integral_mul_const, integral_add_right_eq_self k tz]
  simp_rw [hinner, integral_const_mul]

lemma leadVertical_shear (K G : ℂ → ℂ)
    (hInt : Integrable (fun p : ℝ × ℝ =>
      K (((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) *
        G (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)) (volume.prod volume)) :
    a2_probe_sol.leadVertical 4 (fun ξ => a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) =
      a2_probe_sol.leadVertical 5 K * a2_probe_sol.leadVertical 2 G := by
  unfold a2_probe_sol.leadVertical
  simp_rw [integral_const_mul]
  have hpt (tξ tz : ℝ) :
      (((4 : ℝ) : ℂ) + (tξ : ℂ) * Complex.I + (((2 : ℝ) : ℂ) + (tz : ℂ) * Complex.I) - 1) =
        ((5 : ℝ) : ℂ) + ((tξ + tz : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp_rw [hpt]
  have hshear := integral_shear_swap
    (fun s => K (((5 : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I))
    (fun tz => G (((2 : ℝ) : ℂ) + ((tz : ℝ) : ℂ) * Complex.I)) hInt
  rw [mul_assoc, hshear]
  ring

lemma gaussian_shear_2d_integrable (C : ℝ) :
    Integrable (fun p : ℝ × ℝ => C * Real.exp (-(p.1 + p.2) ^ 2) * (1 + |p.2|) ^ (-2 : ℝ))
      (volume.prod volume) := by
  let tail : ℝ → ℝ := fun x => (1 + |x|) ^ (-2 : ℝ)
  let gauss : ℝ → ℝ := fun x => Real.exp (-x ^ 2)
  have htail : Integrable tail volume := by
    simpa [tail, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume)
        (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2))
  have hgauss : Integrable gauss volume := by
    simpa [gauss] using
      (integrable_exp_neg_mul_sq (b := 1) (by norm_num : (0 : ℝ) < 1))
  let E := ℝ × ℝ
  let μ : Measure E := volume.prod volume
  let f : Module.Dual ℝ E := LinearMap.snd ℝ ℝ ℝ
  let v : E := (1, 0)
  have hfv : f v = 0 := rfl
  let L : E ≃ₗ[ℝ] E := LinearEquiv.transvection hfv
  have hdetUnit : LinearEquiv.det L = 1 := by
    simp [L, LinearEquiv.transvection.det_eq_one]
  have hdet : LinearMap.det L.toLinearMap = 1 := by
    rw [← LinearEquiv.coe_det]
    exact congrArg (fun u : ℝˣ => (u : ℝ)) hdetUnit
  have hdet0 : LinearMap.det L.toLinearMap ≠ 0 := by
    rw [hdet]
    norm_num
  have hmap : Measure.map L.toLinearMap μ = μ := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := μ) (f := L.toLinearMap) hdet0]
    simp [hdet]
  have hL_apply (t : E) : L t = (t.1 + t.2, t.2) := by
    rw [LinearEquiv.transvection.apply hfv t]
    change t + t.2 • (1, (0 : ℝ)) = (t.1 + t.2, t.2)
    apply Prod.ext
    · change t.1 + t.2 • (1 : ℝ) = _
      simp
    · change t.2 + t.2 • (0 : ℝ) = _
      simp
  have hLfun : (fun t : E => L t) = fun t => (t.1 + t.2, t.2) :=
    funext hL_apply
  have hLmeas : Measurable L.toLinearMap := by
    change Measurable (fun t : E => L t)
    rw [hLfun]
    fun_prop
  have hMP : MeasurePreserving L.toLinearMap μ μ := ⟨hLmeas, hmap⟩
  have hbase : Integrable (fun t : E => gauss t.1 * tail t.2) μ :=
    hgauss.mul_prod htail
  have hshear : Integrable (fun t : E => gauss (t.1 + t.2) * tail t.2) μ := by
    have hcomp := hMP.integrable_comp_of_integrable hbase
    convert hcomp using 1
    ext t
    simp [Function.comp_apply, hL_apply, gauss, tail]
  simpa [gauss, tail, mul_assoc] using hshear.const_mul C

lemma leadKG_integrable (hdecay : a2_probe_sol.LeadWeightDecay R sd W)
    {T_ξ T_z : ℝ} (hTξ : 0 < T_ξ) (hTz : 0 < T_z) :
    Integrable (fun p : ℝ × ℝ =>
      (Complex.exp ((((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2) *
        (T_ξ : ℂ) ^ (-(((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I))) *
      (a2_probe_sol.leadM R sd W (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) *
        (T_z : ℂ) ^ (-(((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)))) (volume.prod volume) := by
  rcases hdecay with ⟨hDM, -, hMdecay, -⟩
  obtain ⟨CM, hCMpos, hMbound⟩ := hMdecay 2 2 2 (by norm_num) le_rfl (by norm_num)
  let C0 : ℝ := Real.exp 25 * T_ξ ^ (-5 : ℝ) * (CM * T_z ^ (-2 : ℝ))
  have hmajor := gaussian_shear_2d_integrable C0
  have hMcont : Continuous (fun p : ℝ × ℝ => a2_probe_sol.leadM R sd W (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    apply continuousOn_univ.mp
    apply hDM.continuousOn.comp
    · fun_prop
    · intro p _
      simp
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      (Complex.exp ((((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2) *
        (T_ξ : ℂ) ^ (-(((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I))) *
      (a2_probe_sol.leadM R sd W (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I) *
        (T_z : ℂ) ^ (-(((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)))) := by
    have h1 : Measurable (fun p : ℝ × ℝ => Complex.exp ((((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2)) := by
      fun_prop
    have h2 : Measurable (fun p : ℝ × ℝ => (T_ξ : ℂ) ^ (-(((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I))) := by
      fun_prop (disch := positivity)
    have h3 : Measurable (fun p : ℝ × ℝ => (T_z : ℂ) ^ (-(((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I))) := by
      fun_prop (disch := positivity)
    exact (h1.mul h2).mul (hMcont.measurable.mul h3)
  apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
  filter_upwards with p
  have hExpNorm : ‖Complex.exp ((((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2)‖ =
      Real.exp (25 - (p.1 + p.2) ^ 2) := by
    rw [Complex.norm_exp]
    have hsq : ((((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2).re =
        25 - (p.1 + p.2) ^ 2 := by
      have : (((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) ^ 2 =
          ((25 - (p.1 + p.2) ^ 2 : ℝ) : ℂ) + ((10 * (p.1 + p.2) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [this, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hsq]
  have hExpSplit : Real.exp (25 - (p.1 + p.2) ^ 2) = Real.exp 25 * Real.exp (-(p.1 + p.2) ^ 2) := by
    rw [show 25 - (p.1 + p.2) ^ 2 = 25 + (-(p.1 + p.2) ^ 2) by ring, Real.exp_add]
  have hTξNorm : ‖(T_ξ : ℂ) ^ (-(((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I))‖ =
      T_ξ ^ (-5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTξ]
    simp
  have hTzNorm : ‖(T_z : ℂ) ^ (-(((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I))‖ =
      T_z ^ (-2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTz]
    simp
  have hMNorm : ‖a2_probe_sol.leadM R sd W (2 + (p.2 : ℂ) * Complex.I)‖ ≤
      CM * (1 + |p.2|) ^ (-2 : ℝ) := by
    have := hMbound 2 p.2 le_rfl le_rfl
    exact_mod_cast this
  simp only [norm_mul, hExpNorm, hExpSplit, hTξNorm, hTzNorm]
  dsimp [C0]
  calc
    _ ≤ (Real.exp 25 * Real.exp (-(p.1 + p.2) ^ 2) * T_ξ ^ (-5 : ℝ)) *
        ((CM * (1 + |p.2|) ^ (-2 : ℝ)) * T_z ^ (-2 : ℝ)) := by
      gcongr
    _ = (Real.exp 25 * T_ξ ^ (-5 : ℝ) * (CM * T_z ^ (-2 : ℝ))) *
        Real.exp (-(p.1 + p.2) ^ 2) * (1 + |p.2|) ^ (-2 : ℝ) := by ring

lemma leadVertical_const_mul (σ : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    a2_probe_sol.leadVertical σ (fun s => c * f s) = c * a2_probe_sol.leadVertical σ f := by
  dsimp [a2_probe_sol.leadVertical]
  rw [integral_const_mul]
  ring

lemma leadTripleVertical_shear_factor (C : ℂ) (fw K G : ℂ → ℂ)
    (hInt : Integrable (fun p : ℝ × ℝ =>
      K (((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) *
        G (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)) (volume.prod volume)) :
    a2_probe_sol.leadTripleVertical 4 4 2 (fun ξ w z => C * fw w * (K (ξ + z - 1) * G z)) =
      C * a2_probe_sol.leadVertical 4 fw * (a2_probe_sol.leadVertical 5 K * a2_probe_sol.leadVertical 2 G) := by
  dsimp [a2_probe_sol.leadTripleVertical]
  have hinner (ξ w : ℂ) :
      a2_probe_sol.leadVertical 2 (fun z => C * fw w * (K (ξ + z - 1) * G z)) =
        (C * fw w) * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z) := by
    rw [← leadVertical_const_mul]
  simp_rw [hinner]
  have hmid (ξ : ℂ) :
      a2_probe_sol.leadVertical 4 (fun w => C * fw w * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) =
        C * a2_probe_sol.leadVertical 4 fw * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z) := by
    have : (fun w => C * fw w * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) =
        fun w => (C * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) * fw w := by
      ext w; ring
    rw [this, leadVertical_const_mul]
    ring
  simp_rw [hmid]
  have houter :
      a2_probe_sol.leadVertical 4 (fun ξ => C * a2_probe_sol.leadVertical 4 fw * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) =
        C * a2_probe_sol.leadVertical 4 fw * a2_probe_sol.leadVertical 4 (fun ξ => a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) := by
    have : (fun ξ => C * a2_probe_sol.leadVertical 4 fw * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z)) =
        fun ξ => (C * a2_probe_sol.leadVertical 4 fw) * a2_probe_sol.leadVertical 2 (fun z => K (ξ + z - 1) * G z) := by
      ext ξ; ring
    rw [this, leadVertical_const_mul]
  rw [houter, leadVertical_shear K G hInt]

end ArtinPrimitiveRoots.Proofs.pr_e

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol
open ArtinPrimitiveRoots.Proofs.pr_e
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
variable (W : ProbeWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)

/-- IMPL: three pointwise inversions with the Gaussian height shear. -/
theorem mellin_term_inversion
    (hinv : LeadInversionsContract R sd W)
    (hdecay : LeadWeightDecay R sd W)
    (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) :
    ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) * leadOrbitTerm R sd W η U X Y Z p =
      leadTripleVertical 4 4 2 (fun ξ w z => leadMellinTerm R sd W η U X Y Z ξ w z p) := by
  let c := p.1
  let n := p.2.1
  let s := p.2.2.1
  let u := p.2.2.2.1
  let r := p.2.2.2.2
  have hc : 0 < qI c.1 := qI_pos_of_ne_bot c.1 c.2.1.1
  have hn : 0 < qI n.1 := qI_pos_of_ne_bot n.1 n.2.1
  have hs : 0 < qI s.1 := qI_pos_of_ne_bot s.1 s.2.1
  have hr : 0 < qI r.1 := qI_pos_of_ne_bot r.1 r.2.1
  have hu : 0 < U.q u := U.q_pos u
  have hqA : 0 < qI (Aideal R c n).1 := qI_pos_of_ne_bot (Aideal R c n).1 (Aideal R c n).2.1

  let Tw : ℝ := qI s.1 / Y
  have hTw : 0 < Tw := div_pos hs hY
  have h_inv_w : W.W1 Tw = leadVertical 4 (fun w => leadW1hat W w * (Tw : ℂ) ^ (-w)) :=
    hinv.2.1 Tw hTw

  let Tξ : ℝ := qI (Aideal R c n).1 / Z
  have hTξ : 0 < Tξ := div_pos hqA hZ
  have h_inv_ξ : (PG Tξ : ℂ) = leadVertical 5 (fun sG => Complex.exp (sG ^ 2) * (Tξ : ℂ) ^ (-sG)) :=
    hinv.2.2 Tξ hTξ

  let Tz : ℝ := X * U.q u * qI r.1 ^ 6 / qI (Aideal R c n).1
  have hTz : 0 < Tz := div_pos (mul_pos (mul_pos hX hu) (pow_pos hr 6)) hqA
  have h_inv_z : leadV0 R sd W Tz =
      leadVertical 2 (fun z => leadM R sd W z * (Tz : ℂ) ^ (-z)) :=
    hinv.1 Tz hTz

  let fw : ℂ → ℂ := fun w => leadW1hat W w * (Tw : ℂ) ^ (-w)
  let K : ℂ → ℂ := fun sG => Complex.exp (sG ^ 2) * (Tξ : ℂ) ^ (-sG)
  let G : ℂ → ℂ := fun z => leadM R sd W z * (Tz : ℂ) ^ (-z)
  have hInt : Integrable (fun p : ℝ × ℝ =>
      K (((5 : ℝ) : ℂ) + ((p.1 + p.2 : ℝ) : ℂ) * Complex.I) *
        G (((2 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)) (volume.prod volume) :=
    leadKG_integrable R sd W hdecay hTξ hTz

  let C : ℂ := ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) *
    (gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
     (qI c.1 ^ (-(1 / 2 : ℝ)) / qI n.1 / qI (Aideal R c n).1 : ℝ) *
     leadFiniteFactor R s (Aideal R c n) (Agen R c n) ((U.repr u : F) * (bc.gen r : F) ^ 6))

  have hLHS : ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) * leadOrbitTerm R sd W η U X Y Z p =
      C * leadVertical 4 fw *
        (leadVertical 5 K * leadVertical 2 G) := by
    dsimp [leadOrbitTerm, c, n, s, u, r, Tw, Tξ, Tz]
    rw [h_inv_w, h_inv_ξ, h_inv_z]
    dsimp [C, fw, K, G]
    ring
  rw [hLHS]
  rw [← leadTripleVertical_shear_factor C fw K G hInt]
  apply congr_arg (leadTripleVertical 4 4 2)
  ext ξ w z
  dsimp [leadMellinTerm, leadMellinWeight, leadCalFTerm,
    c, n, s, u, r, C, fw, K, G, Tw, Tξ, Tz]

  have h_XY := pow_id_XY X Y hX
  have h_div_cast := div_div_cast (qI c.1 ^ (-(1 / 2 : ℝ))) (qI n.1) (qI (Aideal R c n).1)
  have h_pw := pow_id_div (qI s.1) Y hs hY w
  have h_pξ := pow_id_div (qI (Aideal R c n).1) Z hqA hZ (ξ + z - 1)
  have hpos_num : 0 < X * U.q u * qI r.1 ^ 6 := mul_pos (mul_pos hX hu) (pow_pos hr 6)
  have h_pz := pow_id_div (X * U.q u * qI r.1 ^ 6) (qI (Aideal R c n).1) hpos_num hqA z
  have h_p3 := pow_id_3mul X (U.q u) (qI r.1 ^ 6) hX hu (pow_pos hr 6) z
  have h_pqr := pow_id_qr (qI r.1) hr z

  rw [h_XY, h_div_cast, h_pw, h_pξ, h_pz, h_p3, h_pqr]

  have h_X := pow_id_X X hX z
  have h_Y := pow_id_Y Y hY w
  have h_qc := pow_id_qc (qI c.1) hc ξ
  have h_qn := pow_id_qn (qI n.1) hn ξ
  have h_qA := pow_id_qA (qI c.1) (qI n.1) hc hn ξ z
  have hqA_eq : qI (Aideal R c n).1 = qI c.1 * qI n.1 ^ 3 := qI_Aideal R c n

  rw [← h_X, ← h_Y, ← h_qc, ← h_qn, hqA_eq]
  dsimp at h_qA

  let Rest : ℂ :=
    (X : ℂ) ^ (1 / 2 : ℂ) * (X : ℂ) ^ (-z) * (Z : ℂ) ^ (ξ + z - 1) *
    ((Y : ℂ)⁻¹ * (Y : ℂ) ^ w) * Complex.exp ((ξ + z - 1) ^ 2) *
    leadM R sd W z * leadW1hat W w *
    (U.q u : ℂ) ^ (-z) *
    gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
    leadFiniteFactor R s (Aideal R c n) (Agen R c n)
      ((U.repr u : F) * (bc.gen r : F) ^ 6) *
    ((qI c.1 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (qI n.1 : ℂ)⁻¹ *
    (qI s.1 : ℂ) ^ (-w) * (qI r.1 : ℂ) ^ (-6 * z)

  calc
    _ = Rest * (((qI c.1 * qI n.1 ^ 3 : ℝ) : ℂ)⁻¹ * ((qI c.1 * qI n.1 ^ 3 : ℝ) : ℂ) ^ (-(ξ + z - 1)) * ((qI c.1 * qI n.1 ^ 3 : ℝ) : ℂ) ^ z) := by
      dsimp [Rest]; ring
    _ = Rest * ((qI c.1 : ℂ) ^ (-ξ) * (qI n.1 : ℂ) ^ (-3 * ξ)) := by
      rw [h_qA]
    _ = _ := by
      dsimp [Rest]; ring

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
