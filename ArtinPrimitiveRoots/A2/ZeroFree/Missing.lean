import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.ZeroFree.Density
import ArtinPrimitiveRoots.A2.Poisson.Missing
import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE_ASYM.FiniteContour
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE_ASYM.SignalEndpoints
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

section ZeroFree
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U)

def frequencyDyad (U0 : ℝ) : Set U.U := {u | U0 ≤ U.q u ∧ U.q u < 2 * U0}
def rowTwist (u : U.U) : HeckeChar F := η * (U.kummer u)⁻¹

/-- A single fixed choice of exceptional sets, with constants uniform over all growing dyads. -/
structure ZeroDensityData where
  ρ : ℝ
  ρ_pos : 0 < ρ
  U0 : ℝ
  U0_two : 2 ≤ U0
  Cexc : ℝ
  Cexc_pos : 0 < Cexc
  E : ℝ → Finset U.U
  E_sub : ∀ T, U0 ≤ T → ∀ u ∈ E T, u ∈ frequencyDyad η U T
  E_count : ∀ T, U0 ≤ T → ((E T).card : ℝ) ≤ Cexc * T ^ (1 / 2 : ℝ)
  covers : ∀ T, U0 ≤ T → ∀ u ∈ frequencyDyad η U T,
    (rowTwist η U u = 1 ∨ ∃ s : ℂ, 996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * T ^ ρ ∧ HA.L (rowTwist η U u) s = 0) →
      u ∈ E T
  reciprocal : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T, U0 ≤ T →
    ∀ u ∈ frequencyDyad η U T, u ∉ E T → ∀ s : ℂ, 998 / 1000 ≤ s.re → |s.im| ≤ 2 * T ^ ρ →
      HA.LS S (rowTwist η U u) s ≠ 0 ∧ ‖(HA.LS S (rowTwist η U u) s)⁻¹‖ ≤ C * T ^ ε

/-- zf:height-decay, 06:389–411. Real strips are fixed, with positive lower z endpoint. -/
theorem zf_height_decay : ∀ lξ rξ lw rw lz rz A0 : ℝ,
  lξ ≤ rξ → lw ≤ rw → 0 < lz → lz ≤ rz → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ ξ w z : ℂ, lξ ≤ ξ.re → ξ.re ≤ rξ → lw ≤ w.re → w.re ≤ rw → lz ≤ z.re → z.re ≤ rz →
      ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
        C * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
  sorry
/-- zf:height-decay, 06:389-411. Gaussian convolution preserves arbitrary polynomial decay. -/
theorem zf_height_convolution : ∀ A1 : ℝ, 0 < A1 → ∃ A0 C : ℝ, 1 < A0 ∧ 0 < C ∧ ∀ T : ℝ,
  (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)) ≤ C * (1 + |T|) ^ (-A1) := by
  sorry
/-- def:zf-principal-mellin, 06:458–476: the exact residue scalar in the chosen normalization. -/
def principalConstant : ℂ := HA.RS S ^ 2 / 6 * weightM R sd W (1 / 6) * weightW1hat W 1
def principalSignal (Z : ℝ) : ℂ := fEta (Heta R η U HC) (HA.LS S η) Z

def rowKernel (u : U.U) (Z : ℝ) (ξ w z : ℂ) : ℂ :=
  mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
    HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] / HA.LS S (rowTwist η U u) ξ

def rowContribution (C : Finset U.U) (Z : ℝ) : ℂ :=
  tripleVertical 4 4 2 (fun ξ w z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
    ∑ u ∈ C, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z)

def principalRw (Z : ℝ) : ℂ := tripleVertical (1 + δ1) (95 / 100) (1 / 6 + δ1) (rowKernel R sd W η U HA HC U.one Z)
def principalRz (Z : ℝ) : ℂ := HA.RS S * weightW1hat W 1 *
  vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z =>
    (Z : ℂ) ^ ((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z) * Complex.exp ((ξ + z - 1) ^ 2) *
      weightM R sd W z * HA.LS S 1 (6 * z) * HC.H U.one ![ξ,1,z] / HA.LS S η ξ))

/-- zf:principal-row, 06:413–477. The residue at z=1/6 carries R_S/6, accounted for in c₀. -/
theorem zf_principal_row : EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W →
  principalConstant R sd W HA ≠ 0 ∧ ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
    rowContribution R sd W η U {U.one} Z = principalConstant R sd W HA * principalSignal R η U HA HC Z +
      principalRw R sd W η U HA HC Z + principalRz R sd W η U HA HC Z ∧
    ‖principalRw R sd W η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) ∧
    ‖principalRz R sd W η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) := by
  sorry
/-- zf:small-rows, 06:479–551: any subset of a nonprincipal dyad, with explicit cardinal cost. -/
theorem zf_small_rows : EulerHypotheses R η → ∀ α B ε : ℝ, 0 ≤ α → 0 < B → 0 < ε → ∃ C : ℝ, 0 < C ∧
  ∀ T Z : ℝ, 1 ≤ T → 2 ≤ Z → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T) → (rows.card : ℝ) ≤ B * T ^ α →
      rowContribution R sd W η U rows Z = tripleVertical (1 + δ1) (3 / 1000) (4 / 10)
        (fun ξ w z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) ∧
      ‖rowContribution R sd W η U rows Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + 1 / 2 - 4 / 10 + ε) := by
  sorry
variable (ZD : ZeroDensityData η U HA)
/-- Actual central part of the good rows after the truncated ξ shift. -/
def goodCentral (rows : Finset U.U) (T Z : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t in Set.Icc (-(T ^ ZD.ρ)) (T ^ ZD.ρ),
    vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z =>
      ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (998 / 1000 + t * Complex.I) w z))

private theorem mellinWeight_norm_exact (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) :
    ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ =
      Z ^ Estar ξ.re w.re z.re *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ := by
  let p₁ : ℂ := ((Z ^ a : ℝ) : ℂ) ^ (1 / 2 - z)
  let p₂ : ℂ := (Z : ℂ) ^ (ξ + z - 1)
  let p₃ : ℂ := ((Z ^ b : ℝ) : ℂ) ^ (w - 1)
  let p₄ : ℂ := Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w
  have hprod : ‖((p₁ * p₂) * p₃) * p₄‖ = ((‖p₁‖ * ‖p₂‖) * ‖p₃‖) * ‖p₄‖ := by
    calc
      _ = ‖(p₁ * p₂) * p₃‖ * ‖p₄‖ := norm_mul _ _
      _ = (‖p₁ * p₂‖ * ‖p₃‖) * ‖p₄‖ := by rw [norm_mul]
      _ = ((‖p₁‖ * ‖p₂‖) * ‖p₃‖) * ‖p₄‖ := by rw [norm_mul]
  have hp₁ : ‖p₁‖ = (Z ^ a) ^ (1 / 2 - z.re) := by
    dsimp [p₁]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (Real.rpow_pos_of_pos hZ a) (1 / 2 - z)
  have hp₂ : ‖p₂‖ = Z ^ (ξ.re + z.re - 1) := by
    dsimp [p₂]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hZ (ξ + z - 1)
  have hp₃ : ‖p₃‖ = (Z ^ b) ^ (w.re - 1) := by
    dsimp [p₃]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (Real.rpow_pos_of_pos hZ b) (w - 1)
  have hpow : (Z ^ a) ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) *
      (Z ^ b) ^ (w.re - 1) = Z ^ Estar ξ.re w.re z.re := by
    rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
      ← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    dsimp [Estar, h0]
    ring
  calc
    ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ = ‖((p₁ * p₂) * p₃) * p₄‖ := by
      unfold mellinWeight
      congr 1
      simp only [p₁, p₂, p₃, p₄]
      ring
    _ = Z ^ Estar ξ.re w.re z.re * ‖p₄‖ := by
      rw [hprod, hp₁, hp₂, hp₃, hpow]

private theorem absorb_kummer_height (AF Adec t : ℝ) (hAF : 0 ≤ AF)
    (hGap : AF + 3 ≤ Adec) :
    (1 + |t|) ^ (-Adec) * (2 + |t|) ^ AF ≤
      2 ^ AF * (1 + |t|) ^ (-3 : ℝ) := by
  have hbase : 1 ≤ 1 + |t| := by nlinarith [abs_nonneg t]
  have htwopow : (2 + |t|) ^ AF ≤ (2 * (1 + |t|)) ^ AF := by
    apply Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) hAF
  rw [Real.mul_rpow (by norm_num) (by positivity)] at htwopow
  calc
    _ ≤ (1 + |t|) ^ (-Adec) *
        (2 ^ AF * (1 + |t|) ^ AF) :=
      mul_le_mul_of_nonneg_left htwopow (Real.rpow_nonneg (by positivity) _)
    _ = 2 ^ AF * ((1 + |t|) ^ (-Adec) * (1 + |t|) ^ AF) := by ring
    _ = 2 ^ AF * (1 + |t|) ^ (-Adec + AF) := by
      rw [← Real.rpow_add (by positivity)]
    _ ≤ 2 ^ AF * (1 + |t|) ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hbase (by linarith))
        (Real.rpow_nonneg (by norm_num) _)

private theorem gaussian_shift_bound (x t : ℝ) :
    Real.exp (-((x + t) ^ 2)) ≤ Real.exp (x ^ 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  have hquad : t ^ 2 / 2 - x ^ 2 ≤ (x + t) ^ 2 := by
    nlinarith [sq_nonneg (t + 2 * x)]
  calc
    Real.exp (-((x + t) ^ 2)) ≤ Real.exp (x ^ 2 - (1 / 2 : ℝ) * t ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hquad]
    _ = Real.exp (x ^ 2) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem rowKernel_norm_exact (u : U.U) (Z : ℝ) (ξ w z : ℂ) :
    ‖rowKernel R sd W η U HA HC u Z ξ w z‖ =
      ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ *
        (U.q u) ^ (-z.re) * ‖HA.LS S 1 (6 * z)‖ *
          ‖HA.LS S (U.kummer u) w‖ * ‖HC.H u ![ξ, w, z]‖ *
            ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ := by
  have hnum :
      ‖(((mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
          (U.q u : ℂ) ^ (-z)) * HA.LS S 1 (6 * z)) *
          HA.LS S (U.kummer u) w) * HC.H u ![ξ, w, z]‖ =
        ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ *
          ‖(U.q u : ℂ) ^ (-z)‖ * ‖HA.LS S 1 (6 * z)‖ *
          ‖HA.LS S (U.kummer u) w‖ * ‖HC.H u ![ξ, w, z]‖ := by
    simp only [norm_mul]
  unfold rowKernel
  rw [norm_div, hnum,
    Complex.norm_cpow_eq_rpow_re_of_pos (U.q_pos u)]
  rw [div_eq_mul_inv, norm_inv]
  simp only [Complex.neg_re]

private theorem exists_minimal_conductor (χ : HeckeChar F) (m : Ideal (𝓞 F))
    (hm0 : m ≠ ⊥) (hmc : χ.ConductorDvd m) :
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor χ f ∧ Ideal.absNorm f ≤ Ideal.absNorm m := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : Ideal (𝓞 F), f ≠ ⊥ ∧ χ.ConductorDvd f ∧ Ideal.absNorm f = n
  have hP : ∃ n, P n := ⟨Ideal.absNorm m, m, hm0, hmc, rfl⟩
  let n₀ := Nat.find hP
  have h₀ : P n₀ := Nat.find_spec hP
  obtain ⟨f, hf0, hfc, hfn⟩ := h₀
  refine ⟨f, ⟨hf0, hfc, ?_⟩, ?_⟩
  · intro g hg0 hgc
    have hmin := Nat.find_min' hP ⟨g, hg0, hgc, rfl⟩
    omega
  · have hmin := Nat.find_min' hP ⟨m, hm0, hmc, rfl⟩
    omega

private theorem kummer_finiteOrder (u : U.U) (hη : IsOfFinOrder η) :
    IsOfFinOrder (U.kummer u) := by
  obtain ⟨m, hm, hηpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hη)
  obtain ⟨n, hn, hωpow⟩ :=
    (isOfFinOrder_iff_pow_eq_one.mp (U.omega_finiteOrder u))
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  ext x
  have hηx : (η x) ^ m = 1 := by
    simpa using congrArg (fun f : HeckeChar F => f x) hηpow
  have hωx : (U.omega u x) ^ n = 1 := by
    simpa using congrArg (fun f : HeckeChar F => f x) hωpow
  have hrel : U.omega u x = η x * (U.kummer u x)⁻¹ :=
    congrArg (fun f : HeckeChar F => f x) (U.omega_induces_twist u)
  have hηxn : (η x) ^ (m * n) = 1 := by
    rw [pow_mul, hηx, one_pow]
  have hωxn : (U.omega u x) ^ (m * n) = 1 := by
    rw [Nat.mul_comm m n, pow_mul, hωx, one_pow]
  have hprod : (U.omega u x) ^ (m * n) =
      (η x) ^ (m * n) * ((U.kummer u x) ^ (m * n))⁻¹ := by
    rw [hrel, mul_pow, inv_pow]
  have hκinv : ((U.kummer u x) ^ (m * n))⁻¹ = 1 := by
    have h := hprod
    rw [hωxn, hηxn] at h
    simpa using h.symm
  have hκpow : (U.kummer u x) ^ (m * n) = 1 := inv_eq_one.mp hκinv
  change ((U.kummer u ^ (m * n)) x : ℂ) = 1
  rw [ContinuousMonoidHom.pow_apply]
  exact congrArg (fun y : ℂˣ => (y : ℂ)) hκpow

private theorem complexUnit_norm_one_of_finiteOrder {z : ℂˣ}
    (hz : IsOfFinOrder z) : ‖(z : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hz)
  have hcomplex : (z : ℂ) ^ n = 1 := by
    have h := congrArg (fun y : ℂˣ => (y : ℂ)) hpow
    simpa using h
  exact Complex.norm_eq_one_of_pow_eq_one hcomplex (Nat.ne_of_gt hn)

private theorem primeValue_norm_le_one (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hram
  · let y := Units.mk0 (unif v) (unif_ne_zero v)
    let g : IdeleClassGroup (𝓞 F) F :=
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v (toLoc v y)
    have hfin : IsOfFinOrder (χ g) := by
      obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨n, hn, ?_⟩
      have h := congrArg (fun f : HeckeChar F => f g) hpow
      simpa using h
    have heval : χ.loc v (toLoc v y) = χ g := rfl
    simpa [y, heval] using (complexUnit_norm_one_of_finiteOrder hfin).le
  · simp

private theorem omittedEulerFactors_norm_le (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (s : ℂ) (hs : 0 < s.re) :
    ‖∏ v ∈ S.Sf, (1 - χ.primeValue v *
      (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ ≤ 2 ^ S.Sf.card := by
  have hfactor (v : FinPlace F) (hv : v ∈ S.Sf) :
      ‖1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ 2 := by
    have hq : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))
    have hpow : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hsmall : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith [hs])
    have hprime : ‖χ.primeValue v‖ ≤ 1 := primeValue_norm_le_one χ hχ v
    have hpowerNorm : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [hpow]
      exact hsmall
    have hmul : ‖χ.primeValue v‖ *
        ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤ 1 := by
      calc
        _ ≤ 1 * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hprime (norm_nonneg _)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowerNorm (by norm_num)
        _ = 1 := by norm_num
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖χ.primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ‖χ.primeValue v‖ *
          ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := by simp
      _ ≤ 1 + 1 := by nlinarith [hmul]
      _ = 2 := by norm_num
  calc
    _ ≤ ∏ v ∈ S.Sf, ‖1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro v hv
        positivity
      · intro v hv
        exact hfactor v hv
    _ = 2 ^ S.Sf.card := by simp

private theorem omittedEulerFactors_differentiable (χ : HeckeChar F) :
    Differentiable ℂ (fun s : ℂ => ∏ v ∈ S.Sf,
      (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
  refine Differentiable.fun_finsetProd ?_
  intro v hv
  have hNnat : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNnat
  have hpow : Differentiable ℂ
      (fun s : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    intro s
    exact (differentiableAt_id.neg).const_cpow (Or.inl hN)
  exact (differentiable_const (1 : ℂ)).sub
    ((differentiable_const (χ.primeValue v)).mul hpow)

private def omittedEulerFactorsInverseConstant : ℝ :=
  (∏ v ∈ S.Sf,
    (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 + δ1))))⁻¹

private theorem omittedEulerFactors_inv_bound (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
    0 < omittedEulerFactorsInverseConstant (S := S) ∧ ∀ s : ℂ, 1 + δ1 ≤ s.re →
      (∏ v ∈ S.Sf, (1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ≠ 0 ∧
        ‖(∏ v ∈ S.Sf, (1 - χ.primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹‖ ≤
            omittedEulerFactorsInverseConstant (S := S) := by
  let β : ℝ := 1 + δ1
  let d : FinPlace F → ℝ := fun v =>
    1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-β)
  let C : ℝ := omittedEulerFactorsInverseConstant (S := S)
  have hd (v : FinPlace F) (hv : v ∈ S.Sf) : 0 < d v := by
    dsimp [d]
    have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hβ : 0 < β := by dsimp [β, δ1]; norm_num
    have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-β) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    linarith
  have hprodPos : 0 < ∏ v ∈ S.Sf, d v := Finset.prod_pos fun v hv => hd v hv
  refine ⟨?_, ?_⟩
  · dsimp [C, omittedEulerFactorsInverseConstant, d, β]
    exact inv_pos.mpr hprodPos
  intro s hs
  have hden (v : FinPlace F) (hv : v ∈ S.Sf) :
      d v ≤ ‖1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := by
    let q : ℝ := Ideal.absNorm v.asIdeal
    have hq : 1 ≤ q := by
      dsimp [q]
      exact_mod_cast (le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))
    have hpow : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
        q ^ (-s.re) := by
      dsimp [q]
      exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hpowle : q ^ (-s.re) ≤ q ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hq (by dsimp [β]; linarith)
    have hz : ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ ≤
        q ^ (-β) := by
      calc
        _ = ‖χ.primeValue v‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_mul _ _
        _ ≤ 1 * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (primeValue_norm_le_one χ hχ v) (norm_nonneg _)
        _ ≤ 1 * q ^ (-β) := mul_le_mul_of_nonneg_left (by rw [hpow]; exact hpowle) (by norm_num)
        _ = q ^ (-β) := one_mul _
    have htriangle : 1 ≤ ‖1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ +
          ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := by
      calc
        1 = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) +
            χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    dsimp [d, q]
    linarith
  have hprodLower : (∏ v ∈ S.Sf, d v) ≤
      ‖∏ v ∈ S.Sf, (1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ := by
    calc
      _ ≤ ∏ v ∈ S.Sf, ‖1 - χ.primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := by
            apply Finset.prod_le_prod₀
            · intro v hv
              exact (hd v hv).le
            · intro v hv
              exact hden v hv
      _ = ‖∏ v ∈ S.Sf, (1 - χ.primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ := by rw [norm_prod]
  have hnormPos : 0 < ‖∏ v ∈ S.Sf,
      (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ :=
    lt_of_lt_of_le hprodPos hprodLower
  have hbound : ‖(∏ v ∈ S.Sf,
      (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹‖ ≤ C := by
    rw [norm_inv]
    dsimp [C]
    exact (inv_le_inv₀ hnormPos hprodPos).2 hprodLower
  constructor
  · exact norm_pos_iff.mp hnormPos
  · simpa [C, omittedEulerFactorsInverseConstant, d, β] using hbound

private theorem kummer_incomplete_convexity_bound (hEuler : EulerHypotheses R η) :
    ∃ A_F : ℝ, 0 < A_F ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ u, u ≠ U.one → ∀ w : ℂ,
        3 / 1000 ≤ w.re → w.re ≤ 4 →
          ‖HA.LS S (U.kummer u) w‖ ≤ C * (U.q u) ^ (1 / 2 + ε) *
            (2 + |w.im|) ^ A_F := by
  obtain ⟨A_F, hAF, hconv⟩ := zf_convexity (F := F)
  refine ⟨A_F, hAF, ?_⟩
  intro ε hε
  obtain ⟨Cconv, hCconv, hconvε⟩ := hconv ε hε
  obtain ⟨Ck, hCk, hmod⟩ := U.kummer_twist_conductor_bound hEuler.1 hEuler.2.1
  let e : ℝ := 1 / 2 + ε
  let CS : ℝ := 2 ^ S.Sf.card
  let C : ℝ := Cconv * Ck ^ e * CS + 1
  refine ⟨C, by positivity, ?_⟩
  intro u hu w hwlo hwhi
  have hk : IsOfFinOrder (U.kummer u) :=
    kummer_finiteOrder (η := η) (U := U) (u := u) hEuler.1
  have hknon : U.kummer u ≠ 1 := by
    intro h
    exact hu ((U.kummer_principal_iff u).mp h)
  obtain ⟨m, hm0, hmdvd, hmbound⟩ := (hmod u).1
  obtain ⟨f, hprim, hfnorm⟩ :=
    exists_minimal_conductor (U.kummer u) m hm0 hmdvd
  have hfnormReal : (Ideal.absNorm f : ℝ) ≤ Ck * U.q u := by
    calc
      (Ideal.absNorm f : ℝ) ≤ Ideal.absNorm m := by exact_mod_cast hfnorm
      _ ≤ Ck * U.q u := hmbound
  let Lk : HeckeLContinuation (U.kummer u) :=
    (HA.2.2.1 (U.kummer u) hk hknon).choose
  have hLk : Lk.value = HA.L (U.kummer u) :=
    (HA.2.2.1 (U.kummer u) hk hknon).choose_spec
  have hconvK := hconvε (U.kummer u) hk hknon f hprim Lk.value
    ⟨Lk.differentiable, Lk.agrees⟩
  have hLbound : ‖HA.L (U.kummer u) w‖ ≤
      Cconv * (Ideal.absNorm f : ℝ) ^ e * (2 + |w.im|) ^ A_F := by
    rw [← hLk]
    exact hconvK.1 w hwlo hwhi
  have hfactor := omittedEulerFactors_norm_le (S := S) (χ := U.kummer u) hk w
    (by linarith : 0 < w.re)
  have hnormLS : ‖HA.LS S (U.kummer u) w‖ =
      ‖HA.L (U.kummer u) w‖ *
        ‖∏ v ∈ S.Sf, (1 - (U.kummer u).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-w))‖ := by
    change ‖HA.L (U.kummer u) w *
      ∏ v ∈ S.Sf, (1 - (U.kummer u).primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-w))‖ = _
    rw [norm_mul]
  have hnormfPow : (Ideal.absNorm f : ℝ) ^ e ≤ (Ck * U.q u) ^ e := by
    apply Real.rpow_le_rpow (by positivity) hfnormReal
    dsimp [e]
    positivity
  have hsplit : (Ck * U.q u) ^ e = Ck ^ e * (U.q u) ^ e :=
    Real.mul_rpow (le_of_lt hCk) (le_of_lt (U.q_pos u))
  have hqpow : 0 ≤ (U.q u) ^ e := Real.rpow_nonneg (U.q_pos u).le e
  have hheight : 0 ≤ (2 + |w.im|) ^ A_F := by positivity
  calc
    ‖HA.LS S (U.kummer u) w‖ =
        ‖HA.L (U.kummer u) w‖ *
          ‖∏ v ∈ S.Sf, (1 - (U.kummer u).primeValue v *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-w))‖ := hnormLS
    _ ≤ (Cconv * (Ideal.absNorm f : ℝ) ^ e * (2 + |w.im|) ^ A_F) * CS := by
      exact mul_le_mul hLbound hfactor (norm_nonneg _) (by positivity)
    _ ≤ (Cconv * (Ck * U.q u) ^ e * (2 + |w.im|) ^ A_F) * CS := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hnormfPow (le_of_lt hCconv)
        · exact hheight
      · positivity
    _ = (Cconv * Ck ^ e * CS) * (U.q u) ^ e * (2 + |w.im|) ^ A_F := by
      rw [hsplit]
      ring
    _ ≤ C * (U.q u) ^ e * (2 + |w.im|) ^ A_F := by
      dsimp [C]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hqpow) hheight

private theorem primitive_heckeLSeries_eq_ray (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor χ f) :
    ∃ (m : ClassFieldTheory.RayClassModulus F)
      (ψ : ClassFieldTheory.RayClassGroup m →* ℂˣ),
      ArtinPrimitiveRoots.Dictionary.modulusIdeal m = f ∧
      ∀ s : ℂ, 1 < s.re → heckeLSeries χ s = Hecke.LSeriesRay ψ s := by
  obtain ⟨m, ψ, hmod, _hInf, hψ⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_rayClass_of_heckeChar χ hχ f hf.1 hf.2.1
  have hψ' : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = Hecke.charValue ψ v.asIdeal := by
    intro v hv
    have hexp : ArtinPrimitiveRoots.A1.idealExp v f = 0 := by
      rw [← hmod, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
      exact Finsupp.notMem_support_iff.mp hv
    exact ⟨qsa_unramifiedAt_of_conductorDvd χ f hf.2.1 v hexp, (hψ v hv).symm⟩
  have hideal : ∀ I : Ideal (𝓞 F), I ≠ ⊥ → χ.idealValue I = Hecke.charValue ψ I := by
    intro I hI
    by_cases hcop : Hecke.IsCoprimeTo m I
    · exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ψ χ hψ' I hcop
    · have hnotmem :
          Hecke.idealUnit I hI ∉ ClassFieldTheory.rayClassPrimeToIdeals m := by
        intro hmem
        exact hcop ⟨hI, hmem⟩
      change ¬ (∀ v : FinPlace F, v ∈ m.finitePart.support →
        FractionalIdeal.count F v
          (Hecke.idealUnit I hI : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0) at hnotmem
      push_neg at hnotmem
      obtain ⟨v, hv, hcountNe⟩ := hnotmem
      have hcount : FractionalIdeal.count F v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
        simpa [Hecke.idealUnit] using hcountNe
      rw [FractionalIdeal.count_coe F v hI,
        Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot] at hcount
      have hcountPos : 0 < Multiset.count v.asIdeal
          (UniqueFactorizationMonoid.normalizedFactors I) := by
        have hne : Multiset.count v.asIdeal
            (UniqueFactorizationMonoid.normalizedFactors I) ≠ 0 := by exact_mod_cast hcount
        exact Nat.pos_of_ne_zero hne
      have hdivI : v.asIdeal ∣ I := by
        have hmem := (Ideal.mem_normalizedFactors_iff hI).mp
          (Multiset.count_pos.mp hcountPos)
        exact Ideal.dvd_iff_le.mpr hmem.2
      have hexp : ArtinPrimitiveRoots.A1.idealExp v f ≠ 0 := by
        rw [← hmod, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
        exact Finsupp.mem_support_iff.mp hv
      have hdivf : v.asIdeal ∣ f := by
        unfold ArtinPrimitiveRoots.A1.idealExp at hexp
        exact (Associates.count_ne_zero_iff_dvd hf.1 v.irreducible).mp hexp
      have hzero := qs_idealValue_eq_zero_of_conductor_M0
        χ f hf v.asIdeal I v.isPrime v.ne_bot hdivf hI hdivI
      simp [Hecke.charValue, hcop, hzero]
  refine ⟨m, ψ, hmod, ?_⟩
  intro s hs
  exact qsa_heckeLSeries_eq_LSeriesRay χ ψ hideal hs

private theorem rowTwist_right_inverse_bound (u : U.U) :
    ∀ s : ℂ, s.re = 1 + δ1 →
      ‖(HA.LS S (rowTwist η U u) s)⁻¹‖ ≤
        (NumberField.dedekindZeta F (1 + δ1)).re *
          omittedEulerFactorsInverseConstant (S := S) + 1 := by
  obtain ⟨f, hf⟩ := U.omega_primitive u
  obtain ⟨m, ψ, hmod, hseries⟩ :=
    primitive_heckeLSeries_eq_ray (U.omega u) (U.omega_finiteOrder u) f hf
  have hF := omittedEulerFactors_inv_bound (S := S) (U.omega u) (U.omega_finiteOrder u)
  let Cζ : ℝ := (NumberField.dedekindZeta F (1 + δ1)).re
  let s₀ : ℂ := (1 + δ1 : ℝ)
  have hζpos : 0 ≤ Cζ := by
    have hs₀ : 1 < s₀.re := by norm_num [s₀, δ1]
    have hray := Hecke.norm_LSeriesRay_le (K := F) (s := s₀) ψ hs₀
    dsimp [Cζ]
    have hnonneg : 0 ≤ (NumberField.dedekindZeta F s₀.re).re :=
      le_trans (norm_nonneg ((Hecke.LSeriesRay ψ s₀)⁻¹)) hray.2.2
    simpa [s₀] using hnonneg
  intro s hsEq
  have hs : 1 < s.re := by rw [hsEq]; norm_num [δ1]
  have hRay := Hecke.norm_LSeriesRay_le (K := F) ψ hs
  have hcompleteRay : HA.L (U.omega u) s = Hecke.LSeriesRay ψ s := by
    calc
      HA.L (U.omega u) s = heckeLSeries (U.omega u) s := HA.2.1 (U.omega u) s hs
      _ = Hecke.LSeriesRay ψ s := hseries s hs
  have hfactorBound := hF.2 s (by rw [hsEq])
  have hLSfactor : HA.LS S (U.omega u) s = Hecke.LSeriesRay ψ s *
      ∏ v ∈ S.Sf, (1 - (U.omega u).primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    unfold HeckeAnalysis.LS
    rw [hcompleteRay]
  have hInvEq : ‖(HA.LS S (U.omega u) s)⁻¹‖ =
      ‖(Hecke.LSeriesRay ψ s)⁻¹‖ *
        ‖(∏ v ∈ S.Sf, (1 - (U.omega u).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹‖ := by
    rw [hLSfactor, mul_inv_rev, norm_mul]
    ring
  have hζ : (NumberField.dedekindZeta F s.re).re = Cζ := by
    simp [Cζ, hsEq]
  have hRayInv := hRay.2.2
  rw [hζ] at hRayInv
  calc
    ‖(HA.LS S (rowTwist η U u) s)⁻¹‖ = ‖(HA.LS S (U.omega u) s)⁻¹‖ := by
      congr 1
      rw [rowTwist, ← U.omega_induces_twist u]
    _ = ‖(Hecke.LSeriesRay ψ s)⁻¹‖ *
        ‖(∏ v ∈ S.Sf, (1 - (U.omega u).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹‖ := hInvEq
    _ ≤ Cζ * omittedEulerFactorsInverseConstant (S := S) :=
      mul_le_mul hRayInv hfactorBound.2 (norm_nonneg _) hζpos
    _ ≤ (NumberField.dedekindZeta F (1 + δ1)).re *
        omittedEulerFactorsInverseConstant (S := S) + 1 := by
      dsimp [Cζ]
      linarith

private theorem one_finiteOrder : IsOfFinOrder (1 : HeckeChar F) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨1, by norm_num, by simp⟩

private theorem one_primitiveConductor : IsPrimitiveConductor (1 : HeckeChar F) ⊤ := by
  refine ⟨by simp, ?_, ?_⟩
  · intro v x hx hxinv hval
    change (1 : HeckeChar F).loc v x = 1
    simp [HeckeChar.loc]
  · intro g hg hgc
    have hnorm : Ideal.absNorm g ≠ 0 := by
      intro h
      exact hg (Ideal.absNorm_eq_zero_iff.mp h)
    simpa using (Nat.one_le_iff_ne_zero.mpr hnorm)

private theorem principal_incomplete_LS_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = 12 / 5 → ‖HA.LS S 1 s‖ ≤ C := by
  obtain ⟨m, ψ, hmod, hseries⟩ :=
    primitive_heckeLSeries_eq_ray (1 : HeckeChar F) one_finiteOrder ⊤ one_primitiveConductor
  let CS : ℝ := 2 ^ S.Sf.card
  let s₀ : ℂ := (12 / 5 : ℝ)
  let Cζ : ℝ := (NumberField.dedekindZeta F s₀.re).re
  let C : ℝ := Cζ * CS + 1
  have hs₀ : 1 < s₀.re := by norm_num [s₀]
  have hray0 := Hecke.norm_LSeriesRay_le (K := F) (s := s₀) ψ hs₀
  have hζpos : 0 ≤ Cζ := by
    dsimp [Cζ]
    exact le_trans (norm_nonneg (Hecke.LSeriesRay ψ s₀)) hray0.1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s hs
  have hsone : 1 < s.re := by rw [hs]; norm_num
  have hray := Hecke.norm_LSeriesRay_le (K := F) (s := s) ψ hsone
  have hcomplete : HA.L 1 s = Hecke.LSeriesRay ψ s := by
    calc
      HA.L 1 s = heckeLSeries (1 : HeckeChar F) s := HA.2.1 1 s hsone
      _ = Hecke.LSeriesRay ψ s := hseries s hsone
  have hfactor := omittedEulerFactors_norm_le (S := S)
    (χ := (1 : HeckeChar F)) one_finiteOrder s (by rw [hs]; norm_num)
  have hLS : HA.LS S 1 s = Hecke.LSeriesRay ψ s *
      ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    unfold HeckeAnalysis.LS
    rw [hcomplete]
  have hζ : (NumberField.dedekindZeta F s.re).re = Cζ := by
    simp [Cζ, s₀, hs]
  have hCS : (2 ^ S.Sf.card : ℝ) = CS := rfl
  have hRayUpper : ‖Hecke.LSeriesRay ψ s‖ ≤ Cζ := by
    have h := hray.1
    rw [hζ] at h
    exact h
  have hFactorUpper :
      ‖∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ ≤ CS := by
    rw [← hCS]
    exact hfactor
  calc
    ‖HA.LS S 1 s‖ = ‖Hecke.LSeriesRay ψ s‖ *
        ‖∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ := by
      rw [hLS, norm_mul]
    _ ≤ Cζ * CS := mul_le_mul hRayUpper hFactorUpper (norm_nonneg _) hζpos
    _ ≤ C := by dsimp [C]; linarith

private theorem rowKernel_height_majorant (u : U.U) (Z : ℝ) (ξ w z : ℂ)
    (hZ : 0 < Z) {CD CP CK CH B eK eH AF Adec : ℝ}
    (hCD : 0 ≤ CD) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK) (hCH : 0 ≤ CH)
    (hDecay : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
      CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (1 + |w.im|) ^ (-Adec))
    (hPrincipal : ‖HA.LS S 1 (6 * z)‖ ≤ CP)
    (hKummer : ‖HA.LS S (U.kummer u) w‖ ≤
      CK * (U.q u) ^ (1 / 2 + eK) * (2 + |w.im|) ^ AF)
    (hH : ‖HC.H u ![ξ, w, z]‖ ≤ CH * (U.q u) ^ eH)
    (hInv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B) :
    ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
      Z ^ Estar ξ.re w.re z.re * (CD * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-Adec)) *
        (U.q u) ^ (-z.re) * CP *
        (CK * (U.q u) ^ (1 / 2 + eK) * (2 + |w.im|) ^ AF) *
        (CH * (U.q u) ^ eH) * B := by
  have hZfac : 0 ≤ Z ^ Estar ξ.re w.re z.re := Real.rpow_nonneg hZ.le _
  have hqfac : 0 ≤ (U.q u) ^ (-z.re) := Real.rpow_nonneg (U.q_pos u).le _
  have hExp : 0 ≤ Real.exp (-((ξ.im + z.im) ^ 2)) := (Real.exp_pos _).le
  have hzpoly : 0 ≤ (1 + |z.im|) ^ (-Adec) := Real.rpow_nonneg (by positivity) _
  have hwpoly : 0 ≤ (1 + |w.im|) ^ (-Adec) := Real.rpow_nonneg (by positivity) _
  have hkpoly : 0 ≤ (2 + |w.im|) ^ AF := Real.rpow_nonneg (by positivity) _
  have hkq : 0 ≤ (U.q u) ^ (1 / 2 + eK) := Real.rpow_nonneg (U.q_pos u).le _
  have hhq : 0 ≤ (U.q u) ^ eH := Real.rpow_nonneg (U.q_pos u).le _
  rw [rowKernel_norm_exact, mellinWeight_norm_exact]
  gcongr
  exact hZ

private theorem rowKernel_height_absorbed (u : U.U) (Z : ℝ) (ξ w z : ℂ)
    (hZ : 0 < Z) {CD CP CK CH B eK eH AF Adec : ℝ}
    (hCD : 0 ≤ CD) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK) (hCH : 0 ≤ CH) (hB : 0 ≤ B)
    (hAF : 0 ≤ AF) (hGap : AF + 3 ≤ Adec)
    (hDecay : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
      CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (1 + |w.im|) ^ (-Adec))
    (hPrincipal : ‖HA.LS S 1 (6 * z)‖ ≤ CP)
    (hKummer : ‖HA.LS S (U.kummer u) w‖ ≤
      CK * (U.q u) ^ (1 / 2 + eK) * (2 + |w.im|) ^ AF)
    (hH : ‖HC.H u ![ξ, w, z]‖ ≤ CH * (U.q u) ^ eH)
    (hInv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B)
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10) :
    ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
      (CD * CP * CK * CH * B * 2 ^ AF) * Z ^ Estar ξ.re w.re z.re *
        (U.q u) ^ (1 / 10 + eK + eH) * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-3 : ℝ) := by
  have hAbsorb := absorb_kummer_height AF Adec w.im hAF hGap
  have hqpow : (U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH =
      (U.q u) ^ (1 / 10 + eK + eH) := by
    calc
      _ = (U.q u) ^ ((-z.re) + (1 / 2 + eK) + eH) := by
        rw [← Real.rpow_add (U.q_pos u), ← Real.rpow_add (U.q_pos u)]
      _ = _ := by rw [hz]; congr 1 <;> ring_nf
  have hmajor := rowKernel_height_majorant (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) u Z ξ w z hZ
    hCD hCP hCK hCH hDecay hPrincipal hKummer hH hInv
  have hcoef0 : 0 ≤ (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
      Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) := by positivity
  have hq0 : 0 ≤ (U.q u) ^ (-z.re) *
      (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH := by
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (U.q_pos u).le _) 
      (Real.rpow_nonneg (U.q_pos u).le _)) (Real.rpow_nonneg (U.q_pos u).le _)
  calc
    _ ≤ Z ^ Estar ξ.re w.re z.re *
        (CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
          (1 + |w.im|) ^ (-Adec)) *
        (U.q u) ^ (-z.re) * CP *
        (CK * (U.q u) ^ (1 / 2 + eK) * (2 + |w.im|) ^ AF) *
        (CH * (U.q u) ^ eH) * B := hmajor
    _ = (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        ((1 + |w.im|) ^ (-Adec) * (2 + |w.im|) ^ AF) *
        ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH) := by ring
    _ ≤ (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (2 ^ AF * (1 + |w.im|) ^ (-3 : ℝ)) *
        ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH) := by
      calc
        _ = (((CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
            Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec)) *
            ((1 + |w.im|) ^ (-Adec) * (2 + |w.im|) ^ AF)) *
            ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH) := by ring
        _ ≤ (((CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
            Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec)) *
            (2 ^ AF * (1 + |w.im|) ^ (-3 : ℝ))) *
            ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + eK) * (U.q u) ^ eH) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hAbsorb hcoef0) hq0
        _ = _ := by ring
    _ = (CD * CP * CK * CH * B * 2 ^ AF) * Z ^ Estar ξ.re w.re z.re *
        (U.q u) ^ (1 / 10 + eK + eH) * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-3 : ℝ) := by
      rw [hqpow]
      ring

private theorem rowKernel_shell_height_bound (u : U.U) (Z T ε : ℝ)
    (ξ w z : ℂ) (hZ : 0 < Z) (hT : 0 < T) (hε : 0 < ε)
    (hqUpper : U.q u ≤ 2 * T)
    {CD CP CK CH B AF Adec : ℝ}
    (hCD : 0 ≤ CD) (hCP : 0 ≤ CP) (hCK : 0 ≤ CK) (hCH : 0 ≤ CH) (hB : 0 ≤ B)
    (hAF : 0 ≤ AF) (hGap : AF + 3 ≤ Adec)
    (hDecay : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
      CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (1 + |w.im|) ^ (-Adec))
    (hPrincipal : ‖HA.LS S 1 (6 * z)‖ ≤ CP)
    (hKummer : ‖HA.LS S (U.kummer u) w‖ ≤
      CK * (U.q u) ^ (1 / 2 + ε / 3) * (2 + |w.im|) ^ AF)
    (hH : ‖HC.H u ![ξ, w, z]‖ ≤ CH * (U.q u) ^ (ε / 3))
    (hInv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B * T ^ (ε / 3))
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10) :
    ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
      (CD * CP * CK * CH * B * 2 ^ AF * 2 ^ (1 / 10 + ε / 3 + ε / 3)) *
        Z ^ Estar ξ.re w.re z.re * T ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
            (1 + |w.im|) ^ (-3 : ℝ) := by
  let α : ℝ := 1 / 10 + ε / 3 + ε / 3
  let Cbase : ℝ := CD * CP * CK * CH * B * 2 ^ AF
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hqpower : (U.q u) ^ α ≤ (2 * T) ^ α :=
    Real.rpow_le_rpow (U.q_pos u).le hqUpper hα0
  have hQ : T ^ (ε / 3) * (U.q u) ^ α ≤
      2 ^ α * T ^ (1 / 10 + ε) := by
    calc
      _ ≤ T ^ (ε / 3) * (2 * T) ^ α :=
        mul_le_mul_of_nonneg_left hqpower (Real.rpow_nonneg hT.le _)
      _ = 2 ^ α * (T ^ (ε / 3) * T ^ α) := by
        rw [Real.mul_rpow (by norm_num) hT.le]
        ring
      _ = 2 ^ α * T ^ (ε / 3 + α) := by
        rw [← Real.rpow_add hT]
      _ = _ := by
        congr 1
        dsimp [α]
        ring
  have hmain := rowKernel_height_absorbed (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) u Z ξ w z hZ
    hCD hCP hCK hCH (by positivity : 0 ≤ B * T ^ (ε / 3)) hAF hGap
    hDecay hPrincipal hKummer hH hInv hw hz
  have hpref0 : 0 ≤ Cbase * Z ^ Estar ξ.re w.re z.re := by
    dsimp [Cbase]
    positivity
  have hdecay0 : 0 ≤ Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-3 : ℝ) := by positivity
  calc
    _ ≤ (CD * CP * CK * CH * B * T ^ (ε / 3) * 2 ^ AF) *
        Z ^ Estar ξ.re w.re z.re * (U.q u) ^ α *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
            (1 + |w.im|) ^ (-3 : ℝ) := by
      simpa [Cbase, α, mul_assoc, mul_left_comm, mul_comm] using hmain
    _ ≤ (Cbase * Z ^ Estar ξ.re w.re z.re) *
        (2 ^ α * T ^ (1 / 10 + ε)) *
          (Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
            (1 + |w.im|) ^ (-3 : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hQ hpref0
      calc
        _ = (Cbase * Z ^ Estar ξ.re w.re z.re) *
            (T ^ (ε / 3) * (U.q u) ^ α) *
              (Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
                (1 + |w.im|) ^ (-3 : ℝ)) := by dsimp [Cbase]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmul hdecay0
    _ = (CD * CP * CK * CH * B * 2 ^ AF * 2 ^ α) *
        Z ^ Estar ξ.re w.re z.re * T ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
            (1 + |w.im|) ^ (-3 : ℝ) := by dsimp [Cbase]; ring
    _ = _ := by dsimp [α]

private theorem rowKernel_good_constants (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    ∃ AF Ac Adec Cconv CD CP CK CH : ℝ,
      0 < AF ∧ 1 < Ac ∧ AF + 3 ≤ Adec ∧ Ac ≤ Adec ∧
      0 < Cconv ∧ 0 < CD ∧ 0 < CP ∧ 0 < CK ∧ 0 < CH ∧
      (∀ t : ℝ, ∫ v : ℝ, Real.exp (-((t + v) ^ 2)) * (1 + |v|) ^ (-Ac) ≤
        Cconv * (1 + |t|) ^ (-(A1 + 2))) ∧
      (∀ ξ w z : ℂ, 998 / 1000 ≤ ξ.re → ξ.re ≤ 1 + δ1 →
        w.re = 3 / 1000 → z.re = 4 / 10 →
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
          CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
            (1 + |w.im|) ^ (-Adec)) ∧
      (∀ z : ℂ, z.re = 4 / 10 → ‖HA.LS S 1 (6 * z)‖ ≤ CP) ∧
      (∀ u, u ≠ U.one → ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
        ‖HA.LS S (U.kummer u) w‖ ≤ CK * (U.q u) ^ (1 / 2 + ε / 3) *
          (2 + |w.im|) ^ AF) ∧
      (∀ u p, eulerNeighborhood p →
        ‖HC.H u p‖ ≤ CH * (U.q u) ^ (ε / 3)) := by
  obtain ⟨AF, hAF, hconvK⟩ := kummer_incomplete_convexity_bound (R := R) (S := S)
    (η := η) (U := U) (HA := HA) hEuler
  obtain ⟨CK, hCK, hK⟩ := hconvK (ε / 3) (by linarith)
  have hA1pos : 0 < A1 := by
    have hrho : 0 < 1 / ZD.ρ := one_div_pos.mpr ZD.ρ_pos
    linarith
  obtain ⟨Ac, Cconv, hAc, hCconv, hconv⟩ := zf_height_convolution (A1 + 2) (by linarith)
  let Adec : ℝ := max (AF + 3) Ac
  have hGap : AF + 3 ≤ Adec := le_max_left _ _
  have hAcAdec : Ac ≤ Adec := le_max_right _ _
  have hAdec : 0 < Adec := by
    have : 0 < AF + 3 := by linarith
    exact lt_of_lt_of_le this hGap
  obtain ⟨CD, hCD, hDecay⟩ := zf_height_decay (R := R) (sd := sd) (W := W)
    (998 / 1000) (1 + δ1) (3 / 1000) (3 / 1000) (4 / 10) (4 / 10) Adec
    (by norm_num [δ1]) (by norm_num) (by norm_num) (by norm_num) hAdec
  obtain ⟨CP, hCP, hPrincipal⟩ := principal_incomplete_LS_bound (S := S) (HA := HA)
  have hHprod := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  obtain ⟨CH, hCH, hH⟩ := hHprod.2.2.2 (ε / 3) (by linarith)
  refine ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
    hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hconv t
  · intro ξ w z hξlo hξhi hw hz
    exact hDecay ξ w z hξlo hξhi (by rw [hw]) (by rw [hw]) (by rw [hz]) (by rw [hz])
  · intro z hz
    have hz6 : (6 * z).re = 12 / 5 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz]
      norm_num
    exact hPrincipal (6 * z) hz6
  · intro u hu w hwlo hwhi
    exact hK u hu w hwlo hwhi
  · exact hH

private theorem rowKernel_continuous_wz (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ)
    (hξ : 998 / 1000 ≤ ξ.re) :
    Continuous (fun t : ℝ × ℝ => rowKernel R sd W η U HA HC u Z ξ
      ((3 / 1000 : ℂ) + t.1 * Complex.I) ((4 / 10 : ℂ) + t.2 * Complex.I)) := by
  let wLine : ℝ → ℂ := fun t => (3 / 1000 : ℂ) + t * Complex.I
  let zLine : ℝ → ℂ := fun t => (4 / 10 : ℂ) + t * Complex.I
  have hwLine : Continuous wLine := by fun_prop
  have hzLine : Continuous zLine := by fun_prop
  have hWeight := (po_weights_exist (R := R) (sd := sd)).2 W
  have hM : DifferentiableOn ℂ (weightM R sd W) {z | 0 < z.re} := hWeight.1
  have hW : Differentiable ℂ (weightW1hat W) := hWeight.2.1
  have hMLine : Continuous (fun t : ℝ => weightM R sd W (zLine t)) := by
    apply hM.continuousOn.comp_continuous hzLine
    intro t
    simp [zLine]
  have hMpair : Continuous (fun t : ℝ × ℝ => weightM R sd W (zLine t.2)) :=
    hMLine.comp continuous_snd
  have hWLine : Continuous (fun t : ℝ => weightW1hat W (wLine t)) :=
    hW.continuous.comp hwLine
  have hWpair : Continuous (fun t : ℝ × ℝ => weightW1hat W (wLine t.1)) :=
    hWLine.comp continuous_fst
  have hbaseX : ((Z ^ a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ a).ne'
  have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hbaseY : ((Z ^ b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZ b).ne'
  have hXexp : Continuous (fun t : ℝ × ℝ => (1 / 2 : ℂ) - zLine t.2) := by fun_prop
  have hZexp : Continuous (fun t : ℝ × ℝ => ξ + zLine t.2 - 1) := by fun_prop
  have hYexp : Continuous (fun t : ℝ × ℝ => wLine t.1 - 1) := by fun_prop
  have hXpow : Continuous (fun t : ℝ × ℝ => ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - zLine t.2)) :=
    hXexp.const_cpow (Or.inl hbaseX)
  have hZpow : Continuous (fun t : ℝ × ℝ => (Z : ℂ) ^ (ξ + zLine t.2 - 1)) :=
    hZexp.const_cpow (Or.inl hbaseZ)
  have hYpow : Continuous (fun t : ℝ × ℝ => ((Z ^ b : ℝ) : ℂ) ^ (wLine t.1 - 1)) :=
    hYexp.const_cpow (Or.inl hbaseY)
  have hExpLine : Continuous (fun t : ℝ × ℝ =>
      Complex.exp ((ξ + zLine t.2 - 1) ^ 2)) := by fun_prop
  have hMellin : Continuous (fun t : ℝ × ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ (wLine t.1) (zLine t.2)) := by
    unfold mellinWeight
    exact (((((hXpow.mul hZpow).mul hYpow).mul hExpLine).mul hMpair).mul hWpair)
  have hK : IsOfFinOrder (U.kummer u) := kummer_finiteOrder (η := η) (U := U) u hEuler.1
  have hKne : U.kummer u ≠ 1 := by
    intro h
    exact hu ((U.kummer_principal_iff u).mp h)
  let LK : HeckeLContinuation (U.kummer u) :=
    (HA.2.2.1 (U.kummer u) hK hKne).choose
  have hLK : LK.value = HA.L (U.kummer u) :=
    (HA.2.2.1 (U.kummer u) hK hKne).choose_spec
  have hDiffK : Differentiable ℂ (HA.L (U.kummer u)) := by
    rw [← hLK]
    exact LK.differentiable
  have hDiffKS : Differentiable ℂ (HA.LS S (U.kummer u)) := by
    unfold HeckeAnalysis.LS
    exact hDiffK.mul (omittedEulerFactors_differentiable (S := S) (U.kummer u))
  have hKLine : Continuous (fun t : ℝ => HA.LS S (U.kummer u) (wLine t)) :=
    hDiffKS.continuous.comp hwLine
  have hDiff1 : DifferentiableOn ℂ (HA.LS S 1) {s | s ≠ 1} := by
    have hL1 : DifferentiableOn ℂ (HA.L 1) {s | s ≠ 1} := HA.2.2.2.1
    unfold HeckeAnalysis.LS
    exact hL1.mul (omittedEulerFactors_differentiable (S := S) (1 : HeckeChar F)).differentiableOn
  have hSLine : Continuous (fun t : ℝ => 6 * zLine t) := by fun_prop
  have hSNe : ∀ t : ℝ, 6 * zLine t ≠ 1 := by
    intro t ht
    have hre : (6 * zLine t).re = 12 / 5 := by simp [zLine]; norm_num
    have := congrArg Complex.re ht
    rw [hre] at this
    norm_num at this
  have hL1Line : Continuous (fun t : ℝ => HA.LS S 1 (6 * zLine t)) :=
    hDiff1.continuousOn.comp_continuous hSLine hSNe
  have hL1Pair : Continuous (fun t : ℝ × ℝ => HA.LS S 1 (6 * zLine t.2)) :=
    hL1Line.comp continuous_snd
  have hHproduct := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  have hHdiff : DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := hHproduct.2.1 u
  let pLine : ℝ × ℝ → Triple := fun t => ![ξ, wLine t.1, zLine t.2]
  have hpLine : Continuous pLine := by fun_prop
  have hELine : ∀ t : ℝ × ℝ, eulerNeighborhood (pLine t) := by
    intro t
    left
    constructor
    · dsimp [pLine]
      simp
      linarith
    · constructor <;> dsimp [pLine, wLine, zLine] <;> simp <;> norm_num
  have hHLine : Continuous (fun t : ℝ × ℝ => HC.H u (pLine t)) :=
    hHdiff.continuousOn.comp_continuous hpLine hELine
  have hKPair : Continuous (fun t : ℝ × ℝ =>
      HA.LS S (U.kummer u) (wLine t.1)) := hKLine.comp continuous_fst
  have hqBase : (U.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (U.q_pos u).ne'
  have hqExp : Continuous (fun t : ℝ × ℝ => -(zLine t.2)) := by fun_prop
  have hqLine : Continuous (fun t : ℝ × ℝ => (U.q u : ℂ) ^ (-(zLine t.2))) :=
    hqExp.const_cpow (Or.inl hqBase)
  unfold rowKernel
  simp only [div_eq_mul_inv]
  exact (((((hMellin.mul hqLine).mul hL1Pair).mul hKPair).mul hHLine).mul
    continuous_const)

private theorem rowKernel_continuous_xi (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10) :
    ContinuousOn (fun ξ => rowKernel R sd W η U HA HC u Z ξ w z)
      {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
        |ξ.im| ≤ 2 * T ^ ZD.ρ} := by
  let Ξ : Set ℂ := {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
    |ξ.im| ≤ 2 * T ^ ZD.ρ}
  have hrow : rowTwist η U u ≠ 1 := by
    intro heq
    exact hGood (ZD.covers T hT u hShell (Or.inl heq))
  have hrowEq : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have hrowFin : IsOfFinOrder (rowTwist η U u) := by
    rw [hrowEq]
    exact U.omega_finiteOrder u
  let Lr : HeckeLContinuation (rowTwist η U u) :=
    (HA.2.2.1 (rowTwist η U u) hrowFin hrow).choose
  have hLr : Lr.value = HA.L (rowTwist η U u) :=
    (HA.2.2.1 (rowTwist η U u) hrowFin hrow).choose_spec
  have hDiffLr : Differentiable ℂ (HA.L (rowTwist η U u)) := by
    rw [← hLr]
    exact Lr.differentiable
  have hDiffLSr : Differentiable ℂ (HA.LS S (rowTwist η U u)) := by
    unfold HeckeAnalysis.LS
    exact hDiffLr.mul (omittedEulerFactors_differentiable (S := S) (rowTwist η U u))
  have hLSCont : ContinuousOn (fun ξ => HA.LS S (rowTwist η U u) ξ) Ξ :=
    hDiffLSr.continuous.continuousOn
  obtain ⟨Crec, hCrec, hrec⟩ := ZD.reciprocal 1 (by norm_num)
  have hLSNe : ∀ ξ ∈ Ξ, HA.LS S (rowTwist η U u) ξ ≠ 0 := by
    intro ξ hξ
    exact (hrec T hT u hShell hGood ξ hξ.1 hξ.2.2).1
  have hLSInv : ContinuousOn (fun ξ => (HA.LS S (rowTwist η U u) ξ)⁻¹) Ξ :=
    hLSCont.inv₀ hLSNe
  have hHP := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  have hHdiff : DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := hHP.2.1 u
  let pLine : ℂ → Triple := fun ξ => ![ξ, w, z]
  have hpLine : ContinuousOn pLine Ξ := by fun_prop
  have hELine : ∀ ξ ∈ Ξ, eulerNeighborhood (pLine ξ) := by
    intro ξ hξ
    left
    refine ⟨?_, ?_, ?_⟩
    · dsimp [pLine]
      simp
      linarith [hξ.1]
    · dsimp [pLine]
      simp [hw]
    · dsimp [pLine]
      simp [hz]
  have hHLine : ContinuousOn (fun ξ => HC.H u ![ξ, w, z]) Ξ := by
    have hTmp : ContinuousOn (fun ξ => HC.H u (pLine ξ)) Ξ :=
      hHdiff.continuousOn.comp hpLine hELine
    convert hTmp using 1
  have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hExpo : ContinuousOn (fun ξ => ξ + z - 1) Ξ := by fun_prop
  have hCpow : ContinuousOn (fun ξ => (Z : ℂ) ^ (ξ + z - 1)) Ξ :=
    hExpo.const_cpow (Or.inl hbaseZ)
  have hExp : ContinuousOn (fun ξ => Complex.exp ((ξ + z - 1) ^ 2)) Ξ := by fun_prop
  have hMellin : ContinuousOn (fun ξ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) Ξ := by
    unfold mellinWeight
    exact ((((continuousOn_const.mul hCpow).mul continuousOn_const).mul hExp).mul
      continuousOn_const).mul continuousOn_const
  have hNum : ContinuousOn (fun ξ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
        (U.q u : ℂ) ^ (-z) * HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
          HC.H u ![ξ, w, z] * (HA.LS S (rowTwist η U u) ξ)⁻¹) Ξ := by
    fun_prop
  unfold rowKernel
  simp only [div_eq_mul_inv]
  exact hNum

private theorem rowKernel_differentiable_xi (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10)
    (ξ : ℂ) (hξ : 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
      |ξ.im| ≤ 2 * T ^ ZD.ρ) :
    DifferentiableAt ℂ (fun ξ => rowKernel R sd W η U HA HC u Z ξ w z) ξ := by
  have hrow : rowTwist η U u ≠ 1 := by
    intro heq
    exact hGood (ZD.covers T hT u hShell (Or.inl heq))
  have hrowEq : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have hrowFin : IsOfFinOrder (rowTwist η U u) := by
    rw [hrowEq]
    exact U.omega_finiteOrder u
  let Lr : HeckeLContinuation (rowTwist η U u) :=
    (HA.2.2.1 (rowTwist η U u) hrowFin hrow).choose
  have hLr : Lr.value = HA.L (rowTwist η U u) :=
    (HA.2.2.1 (rowTwist η U u) hrowFin hrow).choose_spec
  have hDiffLr : Differentiable ℂ (HA.L (rowTwist η U u)) := by
    rw [← hLr]
    exact Lr.differentiable
  have hDiffLSr : Differentiable ℂ (HA.LS S (rowTwist η U u)) := by
    unfold HeckeAnalysis.LS
    exact hDiffLr.mul (omittedEulerFactors_differentiable (S := S) (rowTwist η U u))
  obtain ⟨Crec, hCrec, hrec⟩ := ZD.reciprocal 1 (by norm_num)
  have hden : HA.LS S (rowTwist η U u) ξ ≠ 0 :=
    (hrec T hT u hShell hGood ξ hξ.1 hξ.2.2).1
  have hInv : DifferentiableAt ℂ
      (fun ξ => (HA.LS S (rowTwist η U u) ξ)⁻¹) ξ :=
    hDiffLSr.differentiableAt.inv hden
  have hHprod := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  have hHdiff : DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := hHprod.2.1 u
  have hcoord0 : Continuous fun p : Triple => (p 0).re := by fun_prop
  have hcoord1 : Continuous fun p : Triple => (p 1).re := by fun_prop
  have hcoord2 : Continuous fun p : Triple => (p 2).re := by fun_prop
  have hO0 : IsOpen {p : Triple | 998 / 1000 - 1 / 100000 < (p 0).re} :=
    isOpen_lt continuous_const hcoord0
  have hO1 : IsOpen {p : Triple | 3 / 1000 - 1 / 100000 < (p 1).re} :=
    isOpen_lt continuous_const hcoord1
  have hO2 : IsOpen {p : Triple | 4 / 10 - 1 / 100000 < (p 2).re} :=
    isOpen_lt continuous_const hcoord2
  have hO3 : IsOpen {p : Triple | 95 / 100 - 1 / 100000 < (p 1).re} :=
    isOpen_lt continuous_const hcoord1
  have hO4 : IsOpen {p : Triple | 16 / 100 - 1 / 100000 < (p 2).re} :=
    isOpen_lt continuous_const hcoord2
  have hEopen : IsOpen {p : Triple | eulerNeighborhood p} := by
    change IsOpen
      ({p : Triple | 998 / 1000 - 1 / 100000 < (p 0).re ∧
        3 / 1000 - 1 / 100000 < (p 1).re ∧ 4 / 10 - 1 / 100000 < (p 2).re} ∪
       {p : Triple | 998 / 1000 - 1 / 100000 < (p 0).re ∧
        95 / 100 - 1 / 100000 < (p 1).re ∧ 16 / 100 - 1 / 100000 < (p 2).re})
    exact (hO0.inter (hO1.inter hO2)).union (hO0.inter (hO3.inter hO4))
  have hE : eulerNeighborhood ![ξ, w, z] := by
    have hξ' : 998 / 1000 - 1 / 100000 < ξ.re := by
      have hlt : ((998 / 1000 : ℝ) - 1 / 100000) < (998 / 1000 : ℝ) := by norm_num
      exact hlt.trans_le hξ.1
    have hw' : 3 / 1000 - 1 / 100000 < w.re := by rw [hw]; norm_num
    have hz' : 4 / 10 - 1 / 100000 < z.re := by rw [hz]; norm_num
    left
    exact ⟨by simpa using hξ', by simpa using hw', by simpa using hz'⟩
  have hHAt : DifferentiableAt ℂ (HC.H u) ![ξ, w, z] :=
    hHdiff.differentiableAt (hEopen.mem_nhds hE)
  have hPLine : DifferentiableAt ℂ (fun ξ : ℂ => ![ξ, w, z]) ξ := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hHline : DifferentiableAt ℂ (fun ξ => HC.H u ![ξ, w, z]) ξ := by
    have hcomp : DifferentiableAt ℂ ((HC.H u) ∘ fun ξ : ℂ => ![ξ, w, z]) ξ :=
      (hHAt.hasFDerivAt.comp ξ hPLine.hasFDerivAt).differentiableAt
    simpa only [Function.comp_def] using hcomp
  have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hExpo : DifferentiableAt ℂ (fun ξ : ℂ => ξ + z - 1) ξ := by fun_prop
  have hCpow : DifferentiableAt ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ + z - 1)) ξ :=
    hExpo.const_cpow (Or.inl hbaseZ)
  have hExp : DifferentiableAt ℂ
      (fun ξ : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) ξ := by fun_prop
  have hMellin : DifferentiableAt ℂ
      (fun ξ : ℂ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) ξ := by
    unfold mellinWeight
    exact (((((differentiableAt_const _).mul hCpow).mul
      (differentiableAt_const _)).mul hExp).mul
      (differentiableAt_const _)).mul (differentiableAt_const _)
  have hqPow : DifferentiableAt ℂ (fun ξ : ℂ => (U.q u : ℂ) ^ (-z)) ξ :=
    differentiableAt_const _
  have hLS1 : DifferentiableAt ℂ (fun ξ : ℂ => HA.LS S 1 (6 * z)) ξ :=
    differentiableAt_const _
  have hKummer : DifferentiableAt ℂ
      (fun ξ : ℂ => HA.LS S (U.kummer u) w) ξ := differentiableAt_const _
  have hnum : DifferentiableAt ℂ (fun ξ : ℂ =>
      (((mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z)) *
        HA.LS S 1 (6 * z)) * HA.LS S (U.kummer u) w) * HC.H u ![ξ, w, z]) ξ :=
    (((hMellin.mul hqPow).mul hLS1).mul hKummer).mul hHline
  unfold rowKernel
  simp only [div_eq_mul_inv]
  exact hnum.mul hInv

private theorem rowKernel_rectangle_difference (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10) :
    let H := T ^ ZD.ρ
    Complex.I • ((∫ y : ℝ in -H..H,
          rowKernel R sd W η U HA HC u Z ((1 + δ1 : ℝ) + y * Complex.I) w z) -
        ∫ y : ℝ in -H..H,
          rowKernel R sd W η U HA HC u Z ((998 / 1000 : ℝ) + y * Complex.I) w z) =
      (∫ x : ℝ in (998 / 1000)..(1 + δ1),
          rowKernel R sd W η U HA HC u Z (x + H * Complex.I) w z) -
        ∫ x : ℝ in (998 / 1000)..(1 + δ1),
          rowKernel R sd W η U HA HC u Z (x + (-H) * Complex.I) w z := by
  dsimp
  let a : ℝ := 998 / 1000
  let b : ℝ := 1 + δ1
  let H : ℝ := T ^ ZD.ρ
  have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
  have hH : 0 < H := Real.rpow_pos_of_pos (by linarith) _
  have hab : a ≤ b := by norm_num [a, b, δ1]
  have hLeftRe : ((a : ℂ) - H * Complex.I).re = a := by simp
  have hRightRe : ((b : ℂ) + H * Complex.I).re = b := by simp
  have hLeftIm : ((a : ℂ) - H * Complex.I).im = -H := by simp
  have hRightIm : ((b : ℂ) + H * Complex.I).im = H := by simp
  let G : ℂ → ℂ := fun ξ => rowKernel R sd W η U HA HC u Z ξ w z
  have hcontξ := rowKernel_continuous_xi (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
    hShell hGood Z hZ w z hw hz
  have hcont : ContinuousOn G
      (Set.uIcc ((a : ℂ) - H * Complex.I).re ((b : ℂ) + H * Complex.I).re ×ℂ
        Set.uIcc ((a : ℂ) - H * Complex.I).im ((b : ℂ) + H * Complex.I).im) := by
    apply hcontξ.mono
    intro ξ hξ
    rw [Complex.mem_reProdIm, hLeftRe, hRightRe, Set.uIcc_of_le hab,
      hLeftIm, hRightIm, Set.uIcc_of_le (by linarith : -H ≤ H)] at hξ
    rcases hξ with ⟨⟨hξlo, hξhi⟩, ⟨hξimlo, hξimhi⟩⟩
    have him : |ξ.im| ≤ H := abs_le.mpr ⟨hξimlo, hξimhi⟩
    have hξrange : 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
        |ξ.im| ≤ 2 * T ^ ZD.ρ := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [a] using hξlo
      · simpa [b] using hξhi
      · dsimp [H] at him ⊢
        nlinarith [hH.le, him]
    exact hξrange
  have hrect : ArtinPrimitiveRoots.A2.QSP2.rectInt G
      ((a : ℂ) - H * Complex.I) ((b : ℂ) + H * Complex.I) = 0 := by
    apply ArtinPrimitiveRoots.A2.QSP2.rectInt_eq_zero
      (s := (∅ : Set ℂ)) Set.countable_empty hcont
    intro ξ hξ
    have hcoords := hξ.1
    rw [Complex.mem_reProdIm, hLeftRe, hRightRe, hLeftIm, hRightIm,
      min_eq_left hab, max_eq_right hab,
      min_eq_left (by linarith : -H ≤ H), max_eq_right (by linarith : -H ≤ H)] at hcoords
    rcases hcoords with ⟨⟨hξlo, hξhi⟩, ⟨hξimlo, hξimhi⟩⟩
    have him : |ξ.im| ≤ H := abs_le.mpr ⟨hξimlo.le, hξimhi.le⟩
    have hξrange : 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
        |ξ.im| ≤ 2 * T ^ ZD.ρ := by
      refine ⟨?_, ?_, ?_⟩
      · exact le_of_lt (by simpa [a] using hξlo)
      · exact le_of_lt (by simpa [b] using hξhi)
      · dsimp [H] at him ⊢
        nlinarith [hH.le, him]
    exact rowKernel_differentiable_xi (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
      hShell hGood Z hZ w z hw hz ξ hξrange
  have hdiff := ArtinPrimitiveRoots.A2.ProbeAsym.rectangle_vertical_difference hrect
  simpa [G, a, b, H] using hdiff

private theorem vertical_pair_eq_integral_prod_aux {σw σz : ℝ} (f : ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ =>
      f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)) (volume.prod volume)) :
    vertical σw (fun w => vertical σz (fun z => f w z)) =
      (1 / (2 * Real.pi) : ℂ) ^ 2 *
        ∫ t : ℝ × ℝ, f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I) := by
  unfold vertical
  rw [integral_const_mul, integral_integral hf]
  let J : ℂ := ∫ t : ℝ × ℝ,
    f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)
  change (1 / (2 * Real.pi) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * J) =
    (1 / (2 * Real.pi) : ℂ) ^ 2 * J
  ring

private def rowKernelAt (u : U.U) (Z : ℝ) (ξ w z : ℂ) : ℂ :=
  rowKernel R sd W η U HA HC u Z ξ w z

private def rowKernelHeightFiber (u : U.U) (Z : ℝ) (ξ : ℂ) : ℝ × ℝ → ℂ :=
  fun t => rowKernelAt R sd W η U HA HC u Z ξ (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
    (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I)

private def rowKernelHeightPair (u : U.U) (Z : ℝ) (ξ : ℂ) : ℂ :=
  vertical (3 / 1000) (fun w => vertical (4 / 10)
    (fun z => rowKernelAt R sd W η U HA HC u Z ξ w z))

private theorem rowKernel_pair_continuousOn (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z ε A1 : ℝ) (hZ : 1 ≤ Z) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1)
    (Sξ : Set ℂ)
    (hSsubset : Sξ ⊆ {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
      |ξ.im| ≤ 2 * T ^ ZD.ρ})
    (hSheight : ∀ ξ ∈ Sξ, |ξ.im| ≤ T ^ ZD.ρ) :
    (∀ ξ ∈ Sξ, Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume)) ∧
      ContinuousOn (rowKernelHeightPair R sd W η U HA HC u Z) Sξ := by
  obtain ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
      hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH,
      hconv, hDecay, hPrincipal, hKummer, hHbound⟩ :=
    rowKernel_good_constants (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  have hTpos : 0 < T := by
    have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
    linarith
  have hAdecPos : 0 < Adec := by
    have : 0 < AF + 3 := by linarith
    exact lt_of_lt_of_le this hGap
  have hqUpper : U.q u ≤ 2 * T := by
    have hq : T ≤ U.q u ∧ U.q u < 2 * T := by
      change u ∈ {u | T ≤ U.q u ∧ U.q u < 2 * T} at hShell
      exact hShell
    exact le_of_lt hq.2
  obtain ⟨Brec, hBrec, hrec⟩ := ZD.reciprocal (ε / 3) (by linarith)
  let Ht : ℝ := T ^ ZD.ρ
  let wLine : ℝ → ℂ := fun t => ((3 / 1000 : ℝ) : ℂ) + t * Complex.I
  let zLine : ℝ → ℂ := fun t => ((4 / 10 : ℝ) : ℂ) + t * Complex.I
  have hwLine (t : ℝ) : (wLine t).re = 3 / 1000 := by simp [wLine]
  have hzLine (t : ℝ) : (zLine t).re = 4 / 10 := by simp [zLine]
  let Etop : ℝ := Estar (1 + δ1) (3 / 1000) (4 / 10)
  let Ckernel : ℝ := CD * CP * CK * CH * Brec * 2 ^ AF *
    2 ^ (1 / 10 + ε / 3 + ε / 3)
  let Bdom : ℝ := Ckernel * Z ^ Etop * T ^ (1 / 10 + ε) * Real.exp (Ht ^ 2)
  have hEtop : ∀ ξ ∈ Sξ, Estar ξ.re (3 / 1000) (4 / 10) ≤ Etop := by
    intro ξ hξ
    have hξhi := (hSsubset hξ).2.1
    dsimp [Etop, Estar]
    linarith
  have hBdom : 0 ≤ Bdom := by positivity
  have hW : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hh : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hh)
  have hG : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hProd : Integrable (fun t : ℝ × ℝ =>
      (1 + |t.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) :=
    hW.mul_prod hG
  have hMajorant : Integrable (fun t : ℝ × ℝ =>
      Bdom * ((1 + |t.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2))) :=
    hProd.const_mul Bdom
  let Fξ : ℂ → ℝ × ℝ → ℂ := rowKernelHeightFiber R sd W η U HA HC u Z
  have hFmeas : ∀ ξ ∈ Sξ, AEStronglyMeasurable (Fξ ξ) (volume.prod volume) := by
    intro ξ hξ
    have hξlo := (hSsubset hξ).1
    have hcont := rowKernel_continuous_wz (R := R) (sd := sd) (W := W) (η := η)
      (U := U) (HA := HA) (HC := HC) hEuler u hu Z (by linarith) ξ hξlo
    have hcontF : Continuous (Fξ ξ) := by
      change Continuous (fun t : ℝ × ℝ => rowKernel R sd W η U HA HC u Z ξ
        (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
        (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I))
      simpa [Complex.ofReal_div] using hcont
    exact hcontF.aestronglyMeasurable
  have hFbound : ∀ ξ ∈ Sξ, ∀ t : ℝ × ℝ, ‖Fξ ξ t‖ ≤
      Bdom * ((1 + |t.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) := by
    intro ξ hξ t
    have hxi := hSsubset hξ
    have hInv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ Brec * T ^ (ε / 3) :=
      (hrec T hT u hShell hGood ξ hxi.1 hxi.2.2).2
    have hpEuler : eulerNeighborhood ![ξ, wLine t.1, zLine t.2] := by
      left
      refine ⟨?_, ?_, ?_⟩
      · have hlt : (998 / 1000 : ℝ) - 1 / 100000 < (998 / 1000 : ℝ) := by norm_num
        exact hlt.trans_le hxi.1
      · have hlt : (3 / 1000 : ℝ) - 1 / 100000 < (3 / 1000 : ℝ) := by norm_num
        simpa [wLine] using hlt
      · have hlt : (4 / 10 : ℝ) - 1 / 100000 < (4 / 10 : ℝ) := by norm_num
        simpa [zLine] using hlt
    have hdec := hDecay ξ (wLine t.1) (zLine t.2) hxi.1 hxi.2.1
      (hwLine t.1) (hzLine t.2)
    have hp := hPrincipal (zLine t.2) (hzLine t.2)
    have hk := hKummer u hu (wLine t.1) (by rw [hwLine]) (by rw [hwLine]; norm_num)
    have hh := hHbound u ![ξ, wLine t.1, zLine t.2] hpEuler
    have hrow := rowKernel_shell_height_bound (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) u Z T ε ξ (wLine t.1) (zLine t.2)
      (by linarith) hTpos hε hqUpper hCD.le hCP.le hCK.le hCH.le hBrec.le hAF.le hGap
      hdec hp hk hh hInv (hwLine t.1) (hzLine t.2)
    have hZpow : Z ^ Estar ξ.re (3 / 1000) (4 / 10) ≤ Z ^ Etop :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (hEtop ξ hξ)
    have hCtop0 : 0 ≤ Ckernel * Z ^ Etop * T ^ (1 / 10 + ε) := by
      dsimp [Ckernel]
      positivity
    have himsq : ξ.im ^ 2 ≤ Ht ^ 2 := by
      have himabs : |ξ.im| ≤ Ht := hSheight ξ hξ
      have hHnonneg : 0 ≤ Ht := le_of_lt (Real.rpow_pos_of_pos hTpos _)
      have habssq : |ξ.im| ^ 2 ≤ Ht ^ 2 :=
        (sq_le_sq₀ (abs_nonneg ξ.im) hHnonneg).2 himabs
      simpa only [sq_abs] using habssq
    have hExpCoeff : Real.exp (ξ.im ^ 2) ≤ Real.exp (Ht ^ 2) :=
      Real.exp_le_exp.mpr himsq
    have hPolyZ : (1 + |(zLine t.2).im|) ^ (-Adec) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · nlinarith [abs_nonneg (zLine t.2).im]
      · linarith [hAdecPos]
    have hGauss := gaussian_shift_bound ξ.im t.2
    have hPolyT : (1 + |t.2|) ^ (-Adec) ≤ 1 := by
      simpa [zLine] using hPolyZ
    have hExpGauss : Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) ≤
        Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) :=
      mul_le_mul_of_nonneg_right hExpCoeff (Real.exp_pos _).le
    have hPolyZnn : 0 ≤ (1 + |t.2|) ^ (-Adec) := Real.rpow_nonneg (by positivity) _
    have hPolyWnn : 0 ≤ (1 + |t.1|) ^ (-3 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hTailGrouped : Real.exp (-((ξ.im + t.2) ^ 2)) *
        ((1 + |t.2|) ^ (-Adec) * (1 + |t.1|) ^ (-3 : ℝ)) ≤
        (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) *
          (1 + |t.1|) ^ (-3 : ℝ) := by
      calc
        _ ≤ (Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) *
            ((1 + |t.2|) ^ (-Adec) * (1 + |t.1|) ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hGauss (mul_nonneg hPolyZnn hPolyWnn)
        _ ≤ (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) *
            ((1 + |t.2|) ^ (-Adec) * (1 + |t.1|) ^ (-3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hExpGauss (mul_nonneg hPolyZnn hPolyWnn)
        _ ≤ (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) *
            (1 + |t.1|) ^ (-3 : ℝ) := by
          have hG0 : 0 ≤ Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) := by positivity
          calc
            _ = ((Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) *
                (1 + |t.2|) ^ (-Adec)) * (1 + |t.1|) ^ (-3 : ℝ) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hPolyT hG0) hPolyWnn
            _ = _ := by ring
    have hTail : Real.exp (-((ξ.im + t.2) ^ 2)) *
        (1 + |t.2|) ^ (-Adec) * (1 + |t.1|) ^ (-3 : ℝ) ≤
        Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) *
          (1 + |t.1|) ^ (-3 : ℝ) := by
      simpa [mul_assoc] using hTailGrouped
    calc
      _ ≤ Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + t.2) ^ 2)) * (1 + |t.2|) ^ (-Adec) *
            (1 + |t.1|) ^ (-3 : ℝ) := by
        simpa [Fξ, rowKernelHeightFiber, rowKernelAt, wLine, zLine, Ckernel] using hrow
      _ ≤ Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
          (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) *
            (1 + |t.1|) ^ (-3 : ℝ)) := by
        calc
          _ = (Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)) *
              (Real.exp (-((ξ.im + t.2) ^ 2)) *
                (1 + |t.2|) ^ (-Adec) * (1 + |t.1|) ^ (-3 : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hTail (by positivity)
          _ = _ := by ring
      _ ≤ Bdom * ((1 + |t.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) := by
        have hpref0 : 0 ≤ Ckernel * T ^ (1 / 10 + ε) *
            (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) *
              (1 + |t.1|) ^ (-3 : ℝ)) := by
          dsimp [Ckernel]
          positivity
        calc
          _ = (Ckernel * T ^ (1 / 10 + ε) *
              (Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) *
                (1 + |t.1|) ^ (-3 : ℝ))) * Z ^ Estar ξ.re (3 / 1000) (4 / 10) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hZpow hpref0
          _ = _ := by dsimp [Bdom, Ht]; ring

  have hFiber : ∀ ξ ∈ Sξ, Integrable (Fξ ξ) (volume.prod volume) := by
    intro ξ hξ
    exact hMajorant.mono' (hFmeas ξ hξ)
      (Filter.Eventually.of_forall (hFbound ξ hξ))
  have hIntegralCont : ContinuousOn (fun ξ => ∫ t : ℝ × ℝ, Fξ ξ t) Sξ :=
    continuousOn_of_dominated hFmeas
      (fun ξ hξ => Filter.Eventually.of_forall (hFbound ξ hξ))
      hMajorant
      (Filter.Eventually.of_forall fun t =>
        (rowKernel_continuous_xi (R := R) (sd := sd) (W := W) (η := η)
          (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT hShell hGood
          Z (by linarith) (wLine t.1) (zLine t.2) (hwLine t.1) (hzLine t.2)).mono
          hSsubset)
  refine ⟨hFiber, ?_⟩
  have hPairEq : ∀ ξ ∈ Sξ,
      rowKernelHeightPair R sd W η U HA HC u Z ξ =
        (1 / (2 * Real.pi) : ℂ) ^ 2 * ∫ t : ℝ × ℝ, Fξ ξ t := by
    intro ξ hξ
    have hF : Integrable (fun t : ℝ × ℝ =>
        rowKernelAt R sd W η U HA HC u Z ξ (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I)) (volume.prod volume) := by
      change Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume)
      exact hFiber ξ hξ
    change vertical (3 / 1000) (fun w => vertical (4 / 10)
        (fun z => rowKernelAt R sd W η U HA HC u Z ξ w z)) =
      (1 / (2 * Real.pi) : ℂ) ^ 2 * ∫ t : ℝ × ℝ,
        rowKernelAt R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I)
    unfold vertical
    rw [integral_const_mul]
    have hIntEq :
        (∫ tw : ℝ, ∫ tz : ℝ,
          (fun z : ℂ => rowKernelAt R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + tw * Complex.I) z)
            (((4 / 10 : ℝ) : ℂ) + tz * Complex.I)) =
        ∫ t : ℝ × ℝ, rowKernelAt R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I) := by
      simpa only [Measure.volume_eq_prod ℝ ℝ] using
        (MeasureTheory.integral_integral
        (f := fun tw tz : ℝ =>
          (fun z : ℂ => rowKernelAt R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + tw * Complex.I) z)
            (((4 / 10 : ℝ) : ℂ) + tz * Complex.I)) hF)
    calc
      _ = (1 / (2 * Real.pi) : ℂ) * ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ × ℝ, rowKernelAt R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + t.1 * Complex.I)
            (((4 / 10 : ℝ) : ℂ) + t.2 * Complex.I)) := by
        exact congrArg (fun J : ℂ => (1 / (2 * Real.pi) : ℂ) *
          ((1 / (2 * Real.pi) : ℂ) * J)) hIntEq
      _ = _ := by ring
  have hScalar : ContinuousOn (fun ξ : ℂ =>
      (1 / (2 * Real.pi) : ℂ) ^ 2 * ∫ t : ℝ × ℝ, Fξ ξ t) Sξ :=
    continuousOn_const.mul hIntegralCont
  apply hScalar.congr
  intro ξ hξ
  exact hPairEq ξ hξ

private theorem rowKernel_integrable_of_gaussian_bound (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (Z : ℝ) (hZ : 0 < Z) (ξ : ℂ)
    (hξ : 998 / 1000 ≤ ξ.re) (B0 : ℝ)
    (hBound : ∀ t : ℝ × ℝ,
      ‖rowKernel R sd W η U HA HC u Z ξ
        ((3 / 1000 : ℂ) + t.1 * Complex.I) ((4 / 10 : ℂ) + t.2 * Complex.I)‖ ≤
          B0 * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) * (1 + |t.1|) ^ (-3 : ℝ)) :
    Integrable (fun t : ℝ × ℝ => rowKernel R sd W η U HA HC u Z ξ
      ((3 / 1000 : ℂ) + t.1 * Complex.I) ((4 / 10 : ℂ) + t.2 * Complex.I)) := by
  have hW : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hh : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hh)
  have hG : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hProd : Integrable (fun t : ℝ × ℝ =>
      (1 + |t.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2)) :=
    hW.mul_prod hG
  have hMajorant : Integrable (fun t : ℝ × ℝ =>
      B0 * Real.exp (-(1 / 2 : ℝ) * t.2 ^ 2) * (1 + |t.1|) ^ (-3 : ℝ)) := by
    have h := hProd.const_mul B0
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hCont := rowKernel_continuous_wz (R := R) (sd := sd) (W := W) (η := η)
    (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZ ξ hξ
  refine hMajorant.mono' hCont.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall hBound

private theorem vertical_pair_eq_integral_prod {σw σz : ℝ} (f : ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ =>
      f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I))) :
    vertical σw (fun w => vertical σz (fun z => f w z)) =
      (1 / (2 * Real.pi) : ℂ) ^ 2 *
        ∫ t : ℝ × ℝ, f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I) := by
  unfold vertical
  rw [integral_const_mul, integral_integral hf]
  let J : ℂ := ∫ t : ℝ × ℝ,
    f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)
  change (1 / (2 * Real.pi) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * J) =
    (1 / (2 * Real.pi) : ℂ) ^ 2 * J
  ring

private theorem vertical_pair_norm_le_integral_norm {σw σz : ℝ} (f : ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ =>
      f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I))) :
    ‖vertical σw (fun w => vertical σz (fun z => f w z))‖ ≤
      ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ *
        ∫ t : ℝ × ℝ, ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ := by
  rw [vertical_pair_eq_integral_prod f hf, norm_mul]
  have hnorm := norm_integral_le_integral_norm
    (μ := volume.prod volume)
    (fun t : ℝ × ℝ => f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I))
  exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)

private theorem double_height_integral_bound {σw σz : ℝ} (f : ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ =>
      f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)) (volume.prod volume))
    (A0 Ac A1 C0 Cc T : ℝ) (hA0 : 0 < A0) (hAc : 0 < Ac) (hAcA0 : Ac ≤ A0)
    (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc)
    (hbound : ∀ t : ℝ × ℝ,
      ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ ≤
        C0 * Real.exp (-((T + t.2) ^ 2)) * (1 + |t.2|) ^ (-A0) *
          (1 + |t.1|) ^ (-3 : ℝ))
    (hconv : ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-Ac) ≤
      Cc * (1 + |T|) ^ (-A1)) :
    ∫ t : ℝ × ℝ, ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ ≤
      C0 * (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * Cc * (1 + |T|) ^ (-A1) := by
  have hW : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hh : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hh)
  let fz (v : ℝ) := Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)
  let fzc (v : ℝ) := Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-Ac)
  have hGauss : Integrable (fun v : ℝ => Real.exp (-(1 / 2 : ℝ) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hshift (v : ℝ) : Real.exp (-((T + v) ^ 2)) ≤
      Real.exp (T ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2) :=
    gaussian_shift_bound T v
  have hFz : Integrable fz := by
    have hmajorant := hGauss.const_mul (Real.exp (T ^ 2))
    refine hmajorant.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with v
      dsimp [fz]
      have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
      have hpow0 : (-A0 : ℝ) ≤ 0 := by linarith
      calc
        _ ≤ Real.exp (-((T + v) ^ 2)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          calc
            _ ≤ Real.exp (-((T + v) ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_one_of_one_le_of_nonpos hv hpow0)
                (Real.exp_pos (-(T + v) ^ 2)).le
            _ = _ := by ring
        _ ≤ _ := hshift v
  have hFzc : Integrable fzc := by
    have hmajorant := hGauss.const_mul (Real.exp (T ^ 2))
    refine hmajorant.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with v
      dsimp [fzc]
      have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
      have hpow0 : (-Ac : ℝ) ≤ 0 := by linarith
      calc
        _ ≤ Real.exp (-((T + v) ^ 2)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          calc
            _ ≤ Real.exp (-((T + v) ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_one_of_one_le_of_nonpos hv hpow0)
                (Real.exp_pos (-(T + v) ^ 2)).le
            _ = _ := by ring
        _ ≤ _ := hshift v
  have hfzle : ∀ v, fz v ≤ fzc v := by
    intro v
    dsimp [fz, fzc]
    have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
    have hexp : (-A0 : ℝ) ≤ -Ac := neg_le_neg hAcA0
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hv hexp)
      (Real.exp_pos _).le
  have hIle : (∫ v : ℝ, fz v) ≤ Cc * (1 + |T|) ^ (-A1) := by
    exact (integral_mono hFz hFzc hfzle).trans hconv
  have hProd : Integrable (fun t : ℝ × ℝ =>
      (1 + |t.1|) ^ (-3 : ℝ) * fz t.2) := hW.mul_prod hFz
  have hProdBound :
      ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2 ≤
        (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * (Cc * (1 + |T|) ^ (-A1)) := by
    calc
      _ = (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * ∫ v : ℝ, fz v := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact MeasureTheory.integral_prod_mul
          (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) fz
      _ ≤ _ := mul_le_mul_of_nonneg_left hIle
        (integral_nonneg (fun _ => by positivity))
  have hMajorant : Integrable (fun t : ℝ × ℝ =>
      C0 * ((1 + |t.1|) ^ (-3 : ℝ) * fz t.2)) := hProd.const_mul C0
  calc
    _ ≤ ∫ t : ℝ × ℝ, C0 * ((1 + |t.1|) ^ (-3 : ℝ) * fz t.2) :=
      integral_mono (hf.norm) hMajorant (fun t => by
        simpa [fz, mul_assoc, mul_left_comm, mul_comm] using hbound t)
    _ = C0 * ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2 := by
      rw [integral_const_mul]
    _ ≤ C0 * ((∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) *
        (Cc * (1 + |T|) ^ (-A1))) :=
          mul_le_mul_of_nonneg_left hProdBound (by positivity)
    _ = _ := by ring

private theorem vertical_pair_height_bound {σw σz : ℝ} (f : ℂ → ℂ → ℂ)
    (hf : Integrable (fun t : ℝ × ℝ =>
      f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)) (volume.prod volume))
    (A0 Ac A1 C0 Cc T : ℝ) (hA0 : 0 < A0) (hAc : 0 < Ac) (hAcA0 : Ac ≤ A0)
    (hC0 : 0 ≤ C0) (hCc : 0 ≤ Cc)
    (hbound : ∀ t : ℝ × ℝ,
      ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ ≤
        C0 * Real.exp (-((T + t.2) ^ 2)) * (1 + |t.2|) ^ (-A0) *
          (1 + |t.1|) ^ (-3 : ℝ))
    (hconv : ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-Ac) ≤
      Cc * (1 + |T|) ^ (-A1)) :
    ‖vertical σw (fun w => vertical σz (fun z => f w z))‖ ≤
      ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * C0 *
        (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * Cc * (1 + |T|) ^ (-A1) := by
  have hW : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hh : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hh)
  let fz (v : ℝ) := Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)
  let fzc (v : ℝ) := Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-Ac)
  have hGauss : Integrable (fun v : ℝ => Real.exp (-(1 / 2 : ℝ) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hshift (v : ℝ) : Real.exp (-((T + v) ^ 2)) ≤
      Real.exp (T ^ 2) * Real.exp (-(1 / 2 : ℝ) * v ^ 2) :=
    gaussian_shift_bound T v
  have hFz : Integrable fz := by
    have hmajorant := hGauss.const_mul (Real.exp (T ^ 2))
    refine hmajorant.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with v
      dsimp [fz]
      have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
      have hpow0 : (-A0 : ℝ) ≤ 0 := by linarith
      calc
        _ ≤ Real.exp (-((T + v) ^ 2)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          calc
            _ ≤ Real.exp (-((T + v) ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_one_of_one_le_of_nonpos hv hpow0)
                (Real.exp_pos (-(T + v) ^ 2)).le
            _ = _ := by ring
        _ ≤ _ := hshift v
  have hFzc : Integrable fzc := by
    have hmajorant := hGauss.const_mul (Real.exp (T ^ 2))
    refine hmajorant.mono' ?_ ?_
    · fun_prop
    · filter_upwards [] with v
      dsimp [fzc]
      have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
      have hpow0 : (-Ac : ℝ) ≤ 0 := by linarith
      calc
        _ ≤ Real.exp (-((T + v) ^ 2)) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
          calc
            _ ≤ Real.exp (-((T + v) ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_one_of_one_le_of_nonpos hv hpow0)
                (Real.exp_pos (-(T + v) ^ 2)).le
            _ = _ := by ring
        _ ≤ _ := hshift v
  have hfzle : ∀ v, fz v ≤ fzc v := by
    intro v
    dsimp [fz, fzc]
    have hv : 1 ≤ 1 + |v| := by nlinarith [abs_nonneg v]
    have hexp : (-A0 : ℝ) ≤ -Ac := neg_le_neg hAcA0
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hv hexp)
      (Real.exp_pos _).le
  have hIle : (∫ v : ℝ, fz v) ≤ Cc * (1 + |T|) ^ (-A1) := by
    have h := integral_mono hFz hFzc hfzle
    exact h.trans hconv
  have hProd : Integrable (fun t : ℝ × ℝ =>
      (1 + |t.1|) ^ (-3 : ℝ) * fz t.2) := hW.mul_prod hFz
  have hProdBound :
      ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2 ≤
        (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * (Cc * (1 + |T|) ^ (-A1)) := by
    calc
      _ = (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * ∫ v : ℝ, fz v := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact MeasureTheory.integral_prod_mul
          (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) fz
      _ ≤ _ := mul_le_mul_of_nonneg_left hIle
        (integral_nonneg (fun _ => by positivity))
  have hMajorant : Integrable (fun t : ℝ × ℝ =>
      C0 * ((1 + |t.1|) ^ (-3 : ℝ) * fz t.2)) := hProd.const_mul C0
  have hsumInt :
      ∫ t : ℝ × ℝ, ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ ≤
        C0 * ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2 := by
    calc
      _ ≤ ∫ t : ℝ × ℝ, C0 * ((1 + |t.1|) ^ (-3 : ℝ) * fz t.2) :=
        integral_mono (hf.norm) hMajorant (fun t => by
          simpa [fz, mul_assoc, mul_left_comm, mul_comm] using hbound t)
      _ = C0 * ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2 := by
        rw [integral_const_mul]
  have hvert := vertical_pair_norm_le_integral_norm f hf
  calc
    ‖vertical σw (fun w => vertical σz (fun z => f w z))‖ ≤
        ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ *
          ∫ t : ℝ × ℝ, ‖f (σw + t.1 * Complex.I) (σz + t.2 * Complex.I)‖ := hvert
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ *
        (C0 * ∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2) :=
          mul_le_mul_of_nonneg_left hsumInt (norm_nonneg _)
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * C0 *
        (∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * Cc * (1 + |T|) ^ (-A1) := by
      calc
        _ = (‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * C0) *
            (∫ t : ℝ × ℝ, (1 + |t.1|) ^ (-3 : ℝ) * fz t.2) := by ring
        _ ≤ (‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * C0) *
            ((∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)) * (Cc * (1 + |T|) ^ (-A1))) :=
              mul_le_mul_of_nonneg_left hProdBound (by positivity)
        _ = _ := by ring

/-- zf:intermediate-rows, 06:552–605. The good reciprocal is used only in its rectangle.
The remainder is defined by subtraction so the conclusion bounds the entire contour remainder. -/
theorem zf_intermediate_rows : EulerHypotheses R η → ∀ ε A1 : ℝ, 0 < ε → 1 / ZD.ρ < A1 →
  ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z T, Z0 ≤ Z → Z ^ (9 / 100 : ℝ) < T →
    T ≤ Z ^ (10001 / 100000 : ℝ) → ZD.U0 ≤ T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T ∧ u ∉ ZD.E T) →
      ‖goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
        C * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε) ∧
      ‖rowContribution R sd W η U rows Z - goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε - ZD.ρ * A1) := by
  sorry
/-- zf:far-rows, 06:607–630. Large but fixed z-line; constants independent of T,Z. -/
theorem zf_far_rows : EulerHypotheses R η → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z T, 2 ≤ Z →
  Z ^ (10001 / 100000 : ℝ) < T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T) →
    ‖rowContribution R sd W η U rows Z‖ ≤ C * Z ^ (3849 / 1000 + (1 / 10 : ℝ) * 350000) *
      T ^ (1 - (350000 : ℝ) + ε) := by
  sorry
/-- Finite dyad enumeration is arithmetic input, not a total-tsum surrogate for finiteness. -/
structure DyadEnumeration where
  rows : ℝ → Finset U.U
  mem_rows : ∀ T, 1 ≤ T → ∀ u, u ∈ rows T ↔ u ≠ U.one ∧ u ∈ frequencyDyad η U T
variable (DE : DyadEnumeration η U)
def nonprincipalDyad (T Z : ℝ) : ℂ := rowContribution R sd W η U (DE.rows T) Z

/-- zf:row-sum, 06:632–645: complex sum bound plus absolute convergence of the dyadic series. -/
theorem zf_row_sum : EulerHypotheses R η → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  Summable (fun j : ℕ => ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖) ∧
  ‖∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤ C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  sorry
/-- `zf:probe-asymptotic`, 06:647–681, for the actual probe and exact principal scalar. The
corrected probe-low route consumes the split Gauss data from `sol-gate-a2b`. -/
theorem zf_probe_asymptotic
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  ‖probe R W (Z ^ a) (Z ^ b) Z - principalConstant R sd W HA * principalSignal R η U HA HC Z‖ ≤
    C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  sorry
/-- `zf:f-bounds`, 06:682–707. Both endpoints and continuity are included. The corrected
`prop:probe-low` dependency carries `GaussSplit` (`sol-gate-a2b`). -/
theorem zf_f_bounds
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W →
  ContinuousOn (principalSignal R η U HA HC) (Set.Ioi 0) ∧
  (∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
    ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) ∧
  ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z, 0 < Z → Z ≤ 1 →
    ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ A0 := by
  sorry
end ZeroFree

section ZeroFreeSupplement
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U) (ZD : ZeroDensityData η U HA)
/-- zf:intermediate-rows, 06:552-605. Exceptional subsets use the original low-w contour and α=1/2. -/
theorem zf_intermediate_exceptional_rows : EulerHypotheses R η → ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧ ∀ Z T, 2 ≤ Z → Z ^ (9 / 100 : ℝ) < T →
    T ≤ Z ^ (10001 / 100000 : ℝ) → ZD.U0 ≤ T → ∀ rows : Finset U.U,
    (∀ u ∈ rows, u ≠ U.one ∧ u ∈ ZD.E T) →
      ‖rowContribution R sd W η U rows Z‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (6 / 10 + ε) := by
  intro hEuler ε hε
  let HC0 : EulerCorrection R η U := canonicalEulerCorrection R η U
  obtain ⟨C, hC, hsmall⟩ :=
    zf_small_rows (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC0) hEuler (1 / 2) ZD.Cexc ε (by norm_num) ZD.Cexc_pos hε
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hTlo hThi hU0 rows hrows
  have hT : 1 ≤ T := le_trans (by norm_num : 1 ≤ (2 : ℝ))
    (le_trans ZD.U0_two hU0)
  have hsubset : rows ⊆ ZD.E T := by
    intro u hu
    exact (hrows u hu).2
  have hcard : (rows.card : ℝ) ≤ ZD.Cexc * T ^ (1 / 2 : ℝ) := by
    calc
      (rows.card : ℝ) ≤ ((ZD.E T).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ ZD.Cexc * T ^ (1 / 2 : ℝ) := ZD.E_count T hU0
  have hgood : ∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T := by
    intro u hu
    exact ⟨(hrows u hu).1, ZD.E_sub T hU0 u ((hrows u hu).2)⟩
  have hbound := hsmall T Z hT hZ rows hgood hcard
  have hexp : (1 / 2 : ℝ) + 1 / 2 - 4 / 10 + ε = 6 / 10 + ε := by ring
  rw [hexp] at hbound
  exact hbound.2
end ZeroFreeSupplement

/-! ## Continuation dictionary and fixed exceptional-set conversion -/

section DensityCoherence
variable {D : FieldData F} {S : SData F CE condη} (η : HeckeChar F)
  (fd : FrequencyData S D η) (HA : HeckeAnalysis F)

def completeFromAnalysis (u : fd.U) (h : fd.omega u ≠ 1) :
    HeckeLContinuation (fd.omega u) :=
  (HA.2.2.1 (fd.omega u) (fd.omega_finiteOrder u) h).choose

theorem completeFromAnalysis_eq (u : fd.U) (h : fd.omega u ≠ 1) :
    (completeFromAnalysis η fd HA u h).value = HA.L (fd.omega u) :=
  (HA.2.2.1 (fd.omega u) (fd.omega_finiteOrder u) h).choose_spec

/-- Finite omitted Euler factors in the complete-to-incomplete dictionary (06:165–185). -/
def omittedFactors (χ : HeckeChar F) (s : ℂ) : ℂ :=
  ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

/-- The canonical complete and incomplete continuations plus the finite-deletion identity needed
by zero density and the Euler product. Producer obligation, `sol-gate-a2b` (06:165–185). -/
structure IncompleteDictionary where
  complete : ∀ u : fd.U, fd.omega u ≠ 1 → HeckeLContinuation (fd.omega u)
  complete_eq : ∀ u h, (complete u h).value = HA.L (fd.omega u)
  incomplete : ∀ u : fd.U, fd.omega u ≠ 1 →
    IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹)
  incomplete_eq : ∀ u h s, 997 / 1000 < s.re →
    (incomplete u h).value s = HA.LS S (η * (fd.kummer u)⁻¹) s
  factors_nonzero : ∀ χ : HeckeChar F, IsOfFinOrder χ → ∀ s : ℂ,
    0 < s.re → omittedFactors (S := S) χ s ≠ 0

/-- Analytic producer obligation for `IncompleteDictionary`; continuation and deletion uniqueness
are not consequences of aggregate `HeckeAnalysis` fields alone (`prop:euler-product`, 05:407–433;
`prop:zero-density`, 06:165–185). -/
theorem incompleteDictionary_exists : Nonempty (IncompleteDictionary η fd HA) := by
  sorry

/-- Exact output required to populate the unchanged `ZeroDensityData` record. Its single `E T`
also covers the trivial row and the complete continuation zeros (06:165–185). -/
structure DensityOutput (K : IncompleteDictionary η fd HA) where
  ρ : ℝ
  ρ_pos : 0 < ρ
  U0 : ℝ
  U0_two : 2 ≤ U0
  Cexc : ℝ
  Cexc_pos : 0 < Cexc
  E : ℝ → Finset fd.U
  sub : ∀ T, U0 ≤ T → ∀ u ∈ E T, T ≤ fd.q u ∧ fd.q u < 2 * T
  count : ∀ T, U0 ≤ T → ((E T).card : ℝ) ≤ Cexc * T ^ (1 / 2 : ℝ)
  covers : ∀ T, U0 ≤ T → ∀ u, T ≤ fd.q u → fd.q u < 2 * T →
    (fd.omega u = 1 ∨ ∃ h : fd.omega u ≠ 1, ∃ s : ℂ,
      996 / 1000 ≤ s.re ∧ |s.im| ≤ 4 * T ^ ρ ∧ (K.complete u h).value s = 0) → u ∈ E T
  reciprocal : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ T, U0 ≤ T →
    ∀ u, T ≤ fd.q u → fd.q u < 2 * T → u ∉ E T → ∀ h : fd.omega u ≠ 1,
      ∀ s : ℂ, 998 / 1000 ≤ s.re → |s.im| ≤ 2 * T ^ ρ →
        ‖((K.incomplete u h).value s)⁻¹‖ ≤ C * T ^ ε

/-- Corrected producer contract for `prop:zero-density`; its exponent respects the actual
conductor-height exponent used by the detector (06:165–185). -/
def densityProducerStatement (K : IncompleteDictionary η fd HA) : Prop :=
  IsOfFinOrder η → (∀ v, v ∉ S.Sf → η.UnramifiedAt v) →
    ∀ AF : ℝ, 0 < AF → ConductorHeightBound (F := F) AF →
      ∃ O : DensityOutput η fd HA K, O.ρ < min (1 / 10) (1 / (AF + 1))

/-- Zero-density producer obligation with the corrected fixed-`E` and continuation dictionary.
The analytic theorem remains to be proved (06:165–185). -/
theorem prop_zero_density_dictionary (K : IncompleteDictionary η fd HA) :
    densityProducerStatement η fd HA K := by
  intro hη _ AF hAF hG
  obtain ⟨ρ, U₀, Cexc, E, hρ0, hρ1, hU₀, hC, hmain, hrec⟩ :=
    Proofs.A2ZeroDetect.zero_density_core S D η hη fd K.complete K.incomplete AF hAF AF hAF hG
  refine ⟨⟨ρ, hρ0, U₀, hU₀, Cexc, hC, E, ?_, ?_, ?_, ?_⟩, hρ1⟩
  · intro T hT u hu
    exact (hmain T hT).1 u hu
  · intro T hT
    simpa only [Real.rpow_eq_pow] using (hmain T hT).2.1
  · intro T hT u hu1 hu2 hbad
    apply (hmain T hT).2.2 u hu1 hu2
    simpa only [Real.rpow_eq_pow] using hbad
  · intro ε hε
    obtain ⟨C, hC, hb⟩ := hrec ε hε
    refine ⟨C, hC, ?_⟩
    intro T hT u hu1 hu2 hgood h s hs ht
    simpa only [Real.rpow_eq_pow] using
      hb T hT u hu1 hu2 hgood h s hs (by simpa only [Real.rpow_eq_pow] using ht)

/-- The corrected producer's complete-zero coverage supplies nonvanishing for the unchanged
`ZeroDensityData` consumer; finite deleted factors are explicit. This adapter for `prop:zero-density`
is proved (06:165–185). -/
def density_to_consumer (K : IncompleteDictionary η fd HA)
    (O : DensityOutput η fd HA K) : ZeroDensityData η fd HA where
  ρ := O.ρ
  ρ_pos := O.ρ_pos
  U0 := O.U0
  U0_two := O.U0_two
  Cexc := O.Cexc
  Cexc_pos := O.Cexc_pos
  E := O.E
  E_sub := by
    intro T hT u hu
    exact ⟨(O.sub T hT u hu).1, (O.sub T hT u hu).2⟩
  E_count := O.count
  covers := by
    intro T hT u hu hbad
    have heq := fd.omega_induces_twist u
    apply O.covers T hT u hu.1 hu.2
    rcases hbad with hp | ⟨s, hs, ht, hz⟩
    · exact Or.inl (heq.trans hp)
    · by_cases hn : fd.omega u = 1
      · exact Or.inl hn
      · refine Or.inr ⟨hn, s, hs, ht, ?_⟩
        rw [K.complete_eq u hn, heq]
        exact hz
  reciprocal := by
    intro ε hε
    obtain ⟨C, hC, hb⟩ := O.reciprocal ε hε
    refine ⟨C, hC, ?_⟩
    intro T hT u hu hgood s hs ht
    have heq := fd.omega_induces_twist u
    have hn : fd.omega u ≠ 1 := by
      intro hp
      exact hgood (O.covers T hT u hu.1 hu.2 (Or.inl hp))
    have hl : HA.L (fd.omega u) s ≠ 0 := by
      intro hz
      apply hgood
      apply O.covers T hT u hu.1 hu.2
      refine Or.inr ⟨hn, s, by linarith, ?_, ?_⟩
      · have hpow : 0 ≤ T ^ O.ρ := Real.rpow_nonneg (by linarith [O.U0_two]) _
        nlinarith
      · rw [K.complete_eq u hn]
        exact hz
    refine ⟨?_, ?_⟩
    · change HA.L (η * (fd.kummer u)⁻¹) s *
        omittedFactors (S := S) (η * (fd.kummer u)⁻¹) s ≠ 0
      rw [← heq]
      exact mul_ne_zero hl (K.factors_nonzero _ (fd.omega_finiteOrder u) s (by linarith))
    · have hh := hb T hT u hu.1 hu.2 hgood hn s hs ht
      rwa [K.incomplete_eq u hn s (by linarith)] at hh

end DensityCoherence

/-! ## Frequency dictionary adapters for §6 row families -/

section FrequencyRowCoherence
variable {D : FieldData F} {S : SData F CE condη} (η : HeckeChar F)
  (fd : FrequencyData S D η)

/-- Complete-shell form of the stored frequency count and conductor data; the fixed local
component set and idelic induction are retained (06:13–30). -/
def rowFamilyStatement : Prop :=
  ∃ Ccount Ccond : ℝ, 0 < Ccount ∧ 0 < Ccond ∧ ∃ LS : Finset (SLocalCharacter S),
    ∀ T : ℝ, 2 ≤ T → {u : fd.U | T ≤ fd.q u ∧ fd.q u < 2 * T}.Finite ∧
      (Set.ncard {u : fd.U | T ≤ fd.q u ∧ fd.q u < 2 * T} : ℝ) ≤ Ccount * T ∧
      (∀ u, T ≤ fd.q u → fd.q u < 2 * T → ∃ f : Ideal (𝓞 F),
        IsPrimitiveConductor (fd.omega u) f ∧ (Ideal.absNorm f : ℝ) ≤ Ccond * T ∧
          SComponent S (fd.omega u) ∈ LS) ∧
      Function.Injective fd.omega ∧ (∀ u, fd.kummer u = 1 ↔ u = fd.one) ∧
      (∀ u, fd.omega u = η * (fd.kummer u)⁻¹)

/-- Proved adapter from `FrequencyData` to the complete finite-shell row dictionary consumed by
`zf:row-conductor-family`; the low shell is separate below (06:13–30). -/
theorem rowFamily_from_data : rowFamilyStatement η fd := by
  obtain ⟨Cc, hCc, hc⟩ := fd.dyadic_count
  obtain ⟨Cf, hCf, hf⟩ := fd.conductor_bound
  obtain ⟨LS, hLS⟩ := fd.local_components_finite
  refine ⟨Cc, 2 * Cf, hCc, by positivity, LS, ?_⟩
  intro T hT
  obtain ⟨hfin, hcount⟩ := hc T hT
  refine ⟨hfin, hcount, ?_, fd.omega_injective, fd.kummer_principal_iff,
    fd.omega_induces_twist⟩
  intro u hu hul
  obtain ⟨f, hprim, hb⟩ := hf u
  refine ⟨f, hprim, ?_, hLS u⟩
  nlinarith

/-- The initial shell is finite by `FrequencyData.low_shell_bound`, producing the dyad
enumeration consumed by `zf:row-sum` (06:13–30). -/
theorem dyadEnumeration_nonempty : Nonempty (DyadEnumeration η fd) := by
  have hfin (T : ℝ) (hT : 1 ≤ T) :
      {u : fd.U | u ≠ fd.one ∧ T ≤ fd.q u ∧ fd.q u < 2 * T}.Finite := by
    by_cases hT2 : 2 ≤ T
    · exact (fd.dyadic_count.choose_spec.2 T hT2).1.subset (by intro u hu; exact hu.2)
    · apply fd.low_shell_bound.choose_spec.2.1.subset
      intro u hu
      exact ⟨le_trans hT hu.2.1, lt_trans hu.2.2 (by linarith)⟩
  refine ⟨⟨fun T => if hT : 1 ≤ T then (hfin T hT).toFinset else ∅, ?_⟩⟩
  intro T hT u
  simp [hT, frequencyDyad]

end FrequencyRowCoherence

end ArtinPrimitiveRoots.A2
