import DedekindResidue.CompletedZeta.Existence
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

private theorem goodCentral_bound (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 2 ≤ Z → ZD.U0 ≤ T →
      ∀ rows : Finset U.U,
      (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T ∧ u ∉ ZD.E T) →
      ‖goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
        C * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε) := by
  obtain ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
      hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH,
      hconv, hDecay, hPrincipal, hKummer, hHbound⟩ :=
    rowKernel_good_constants (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Brec, hBrec, hrec⟩ := ZD.reciprocal (ε / 3) (by linarith)
  obtain ⟨Ccount, hCcount, hcount⟩ := U.dyadic_count
  let Ckernel : ℝ := CD * CP * CK * CH * Brec * 2 ^ AF *
    2 ^ (1 / 10 + ε / 3 + ε / 3)
  let Iw : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)
  let Iξ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(A1 + 2))
  let K : ℝ := ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * Ckernel * Iw * Cconv
  let Ctot : ℝ := ‖(1 / (2 * Real.pi) : ℂ)‖ * K * Iξ * Ccount
  have hIw : 0 ≤ Iw := integral_nonneg (fun _ => by positivity)
  have hIξ : 0 ≤ Iξ := integral_nonneg (fun _ => by positivity)
  have hCkernel : 0 ≤ Ckernel := by dsimp [Ckernel]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCtot : 0 ≤ Ctot := by dsimp [Ctot]; positivity
  have hA1pos : 0 < A1 := lt_trans (one_div_pos.mpr ZD.ρ_pos) hA1
  have hAdec : 0 < Adec := by linarith
  have hξintegrable : Integrable (fun t : ℝ => (1 + |t|) ^ (-(A1 + 2))) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < A1 + 2 := by simp; linarith
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hdim)
  refine ⟨Ctot + 1, by linarith, ?_⟩
  intro Z T hZ hT rows hrows
  have hZpos : 0 < Z := by linarith
  have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
  have hTpos : 0 < T := by linarith
  let Ht : ℝ := T ^ ZD.ρ
  have hHt : 0 ≤ Ht := (Real.rpow_pos_of_pos hTpos _).le
  let ξLine : ℝ → ℂ := fun t => ((998 / 1000 : ℝ) : ℂ) + t * Complex.I
  have hξre (t : ℝ) : (ξLine t).re = 998 / 1000 := by simp [ξLine]
  have hξim (t : ℝ) : (ξLine t).im = t := by simp [ξLine]
  let Sξ : Set ℂ := {ξ | ξ.re = 998 / 1000 ∧ |ξ.im| ≤ Ht}
  have hSsubset : Sξ ⊆ {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
      |ξ.im| ≤ 2 * T ^ ZD.ρ} := by
    intro ξ hξ
    refine ⟨le_of_eq hξ.1.symm, ?_, ?_⟩
    · rw [hξ.1]; norm_num [δ1]
    · dsimp [Ht] at hξ hHt
      linarith [hξ.2]
  have hmem (t : ℝ) (ht : t ∈ Set.Icc (-Ht) Ht) : ξLine t ∈ Sξ := by
    refine ⟨hξre t, ?_⟩
    rw [hξim]
    exact abs_le.mpr ht
  let f : ℝ → ℂ := fun t => vertical (3 / 1000) (fun w => vertical (4 / 10)
    (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (ξLine t) w z))
  have hpairbound : ∀ t ∈ Set.Icc (-Ht) Ht,
      ‖f t‖ ≤ K * (rows.card : ℝ) * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
        T ^ (1 / 10 + ε) * (1 + |t|) ^ (-(A1 + 2)) := by
    intro t ht
    have hξ : ξLine t ∈ Sξ := hmem t ht
    have hfiber : ∀ u ∈ rows, Integrable (fun v : ℝ × ℝ =>
        rowKernel R sd W η U HA HC u Z (ξLine t)
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) (volume.prod volume) := by
      intro u hu
      obtain ⟨hne, hShell, hGood⟩ := hrows u hu
      have hdata := rowKernel_pair_continuousOn (R := R) (sd := sd) (W := W)
        (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hne T hT
        hShell hGood Z ε A1 (by linarith) hε hA1 Sξ hSsubset (fun ξ hξ => hξ.2)
      exact hdata.1 (ξLine t) hξ
    have hsumfiber : Integrable (fun v : ℝ × ℝ =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (ξLine t)
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) (volume.prod volume) :=
      integrable_finset_sum rows hfiber
    let C0 : ℝ := (rows.card : ℝ) * Ckernel *
      Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)
    have hpoint : ∀ v : ℝ × ℝ,
        ‖∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (ξLine t)
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)‖ ≤
        C0 * Real.exp (-((t + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
          (1 + |v.1|) ^ (-3 : ℝ) := by
      intro v
      let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I
      let z : ℂ := ((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I
      have hw : w.re = 3 / 1000 := by simp [w]
      have hz : z.re = 4 / 10 := by simp [z]
      have hrow : ∀ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z (ξLine t) w z‖ ≤
          Ckernel * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
            Real.exp (-((t + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
              (1 + |v.1|) ^ (-3 : ℝ) := by
        intro u hu
        obtain ⟨hne, hShell, hGood⟩ := hrows u hu
        have hqUpper : U.q u ≤ 2 * T := hShell.2.le
        have hpEuler : eulerNeighborhood ![ξLine t, w, z] := by
          left
          refine ⟨?_, ?_, ?_⟩
          · change 998 / 1000 - 1 / 100000 < (ξLine t).re
            rw [hξre]; norm_num
          · change 3 / 1000 - 1 / 100000 < w.re
            rw [hw]; norm_num
          · change 4 / 10 - 1 / 100000 < z.re
            rw [hz]; norm_num
        have hxi := hSsubset hξ
        have hinv := (hrec T hT u hShell hGood (ξLine t) hxi.1 hxi.2.2).2
        have hbound := rowKernel_shell_height_bound (R := R) (sd := sd) (W := W)
          (η := η) (U := U) (HA := HA) (HC := HC) u Z T ε (ξLine t) w z
          hZpos hTpos hε hqUpper hCD.le hCP.le hCK.le hCH.le hBrec.le hAF.le hGap
          (hDecay (ξLine t) w z hxi.1 hxi.2.1 hw hz) (hPrincipal z hz)
          (hKummer u hne w (by rw [hw]) (by rw [hw]; norm_num))
          (hHbound u ![ξLine t, w, z] hpEuler) hinv hw hz
        simpa [Ckernel, w, z, ξLine] using hbound
      calc
        _ ≤ ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z (ξLine t) w z‖ :=
          norm_sum_le rows _
        _ ≤ ∑ _u ∈ rows, Ckernel * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
            T ^ (1 / 10 + ε) * Real.exp (-((t + v.2) ^ 2)) *
              (1 + |v.2|) ^ (-Adec) * (1 + |v.1|) ^ (-3 : ℝ) :=
          Finset.sum_le_sum hrow
        _ = _ := by simp [C0, Finset.sum_const, nsmul_eq_mul]; ring
    have hbound := vertical_pair_height_bound
      (σw := 3 / 1000) (σz := 4 / 10)
      (fun w z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (ξLine t) w z)
      hsumfiber Adec Ac (A1 + 2) C0 Cconv t hAdec (by linarith) hAcAdec
      (by dsimp [C0]; positivity) hCconv.le hpoint (hconv t)
    simpa [f, C0, K, Iw, mul_assoc, mul_left_comm, mul_comm] using hbound
  let pref : ℝ := K * (rows.card : ℝ) *
    Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)
  have hpref : 0 ≤ pref := by dsimp [pref]; positivity
  have hint : ‖∫ t in Set.Icc (-Ht) Ht, f t‖ ≤ pref * Iξ := by
    have hdom := hξintegrable.const_mul pref
    have hnorm := norm_integral_le_of_norm_le hdom.integrableOn
      (show ∀ᵐ t ∂volume.restrict (Set.Icc (-Ht) Ht),
        ‖f t‖ ≤ pref * (1 + |t|) ^ (-(A1 + 2)) from by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hpairbound t ht)
    have hwhole : (∫ t in Set.Icc (-Ht) Ht, pref * (1 + |t|) ^ (-(A1 + 2))) ≤
        ∫ t : ℝ, pref * (1 + |t|) ^ (-(A1 + 2)) :=
      setIntegral_le_integral hdom (Filter.Eventually.of_forall fun _ => by positivity)
    simpa [Iξ, integral_const_mul] using hnorm.trans hwhole
  obtain ⟨hfinite, hcard⟩ := hcount T hT2
  have hsub : rows ⊆ hfinite.toFinset := by
    intro u hu
    exact hfinite.mem_toFinset.mpr (hrows u hu).2.1
  have hrowsCard : (rows.card : ℝ) ≤ Ccount * T := by
    calc
      _ ≤ (hfinite.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ Ccount * T := by
        simpa only [Set.ncard_eq_toFinset_card _ hfinite] using hcard
  have hpower : T * T ^ (1 / 10 + ε) = T ^ (11 / 10 + ε) := by
    calc
      _ = T ^ (1 : ℝ) * T ^ (1 / 10 + ε) := by rw [Real.rpow_one]
      _ = T ^ (1 + (1 / 10 + ε)) := (Real.rpow_add hTpos 1 (1 / 10 + ε)).symm
      _ = _ := by congr 1; ring
  have hcoeff : 0 ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ * K * Iξ *
      Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) := by positivity
  calc
    ‖goodCentral R sd W η U HA HC ZD rows T Z‖ =
        ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ t in Set.Icc (-Ht) Ht, f t‖ := by
      simp only [goodCentral, f, Ht, ξLine, Complex.ofReal_div,
        Complex.ofReal_ofNat, norm_mul]
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ * (pref * Iξ) :=
      mul_le_mul_of_nonneg_left hint (norm_nonneg _)
    _ = (‖(1 / (2 * Real.pi) : ℂ)‖ * K * Iξ *
        Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)) *
          (rows.card : ℝ) := by dsimp [pref]; ring
    _ ≤ (‖(1 / (2 * Real.pi) : ℂ)‖ * K * Iξ *
        Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)) *
          (Ccount * T) := mul_le_mul_of_nonneg_left hrowsCard hcoeff
    _ = Ctot * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε) := by
      calc
        _ = Ctot * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
            (T * T ^ (1 / 10 + ε)) := by dsimp [Ctot]; ring
        _ = _ := by rw [hpower]
    _ ≤ (Ctot + 1) * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
        T ^ (11 / 10 + ε) := by
      gcongr
      linarith

private theorem rowKernel_compact_path_integrable (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z ε A1 : ℝ) (hZ : 1 ≤ Z) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1)
    (l r : ℝ) (hlr : l ≤ r) (γ : ℝ → ℂ)
    (hγ : ContinuousOn γ (Set.Icc l r))
    (hrange : ∀ t ∈ Set.Icc l r,
      998 / 1000 ≤ (γ t).re ∧ (γ t).re ≤ 1 + δ1 ∧ |(γ t).im| ≤ T ^ ZD.ρ) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      rowKernelHeightFiber R sd W η U HA HC u Z (γ p.1) p.2)
      ((volume.restrict (Set.Icc l r)).prod volume) := by
  obtain ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
      hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH,
      hconv, hDecay, hPrincipal, hKummer, hHbound⟩ :=
    rowKernel_good_constants (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Brec, hBrec, hrec⟩ := ZD.reciprocal (ε / 3) (by linarith)
  have hTpos : 0 < T := by linarith [ZD.U0_two]
  have hZpos : 0 < Z := by linarith
  have hAdec : 0 < Adec := by linarith
  let Ht : ℝ := T ^ ZD.ρ
  have hHt : 0 ≤ Ht := (Real.rpow_pos_of_pos hTpos _).le
  let clip : ℝ → ℝ := fun t => max l (min r t)
  have hclip : ∀ t, clip t ∈ Set.Icc l r := by
    intro t
    exact ⟨le_max_left _ _, max_le hlr (min_le_left _ _)⟩
  have hclipcont : Continuous clip := by fun_prop
  let path : ℝ → ℂ := γ ∘ clip
  have hpathcont : Continuous path := hγ.comp_continuous hclipcont hclip
  have hpathrange (t : ℝ) : 998 / 1000 ≤ (path t).re ∧
      (path t).re ≤ 1 + δ1 ∧ |(path t).im| ≤ Ht := hrange (clip t) (hclip t)
  let kernel : ℝ → ℝ × ℝ → ℂ := fun t v =>
    rowKernelHeightFiber R sd W η U HA HC u Z (path t) v
  have hcontξ : ∀ v : ℝ × ℝ, Continuous (fun t => kernel t v) := by
    intro v
    have hw : ((((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)).re = 3 / 1000 := by simp
    have hz : ((((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)).re = 4 / 10 := by simp
    have hc := rowKernel_continuous_xi (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
      hShell hGood Z hZpos
      (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
      (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) hw hz
    apply hc.comp_continuous hpathcont
    intro t
    obtain ⟨hlo, hhi, him⟩ := hpathrange t
    exact ⟨hlo, hhi, by dsimp [Ht] at him hHt; linarith⟩
  have hcontfiber : ∀ t : ℝ, Continuous (kernel t) := by
    intro t
    have hc := rowKernel_continuous_wz (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZpos (path t)
      (hpathrange t).1
    simpa [kernel, rowKernelHeightFiber, rowKernelAt, Complex.ofReal_div] using hc
  have hmeas : StronglyMeasurable (Function.uncurry kernel) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcontξ
      (fun t => (hcontfiber t).stronglyMeasurable)
  let Etop : ℝ := Estar (1 + δ1) (3 / 1000) (4 / 10)
  let Ckernel : ℝ := CD * CP * CK * CH * Brec * 2 ^ AF *
    2 ^ (1 / 10 + ε / 3 + ε / 3)
  let Bdom : ℝ := Ckernel * Z ^ Etop * T ^ (1 / 10 + ε) * Real.exp (Ht ^ 2)
  have hCkernel : 0 ≤ Ckernel := by dsimp [Ckernel]; positivity
  have hBdom : 0 ≤ Bdom := by dsimp [Bdom]; positivity
  have hbound : ∀ p : ℝ × (ℝ × ℝ), ‖kernel p.1 p.2‖ ≤
      Bdom * ((1 + |p.2.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * p.2.2 ^ 2)) := by
    intro p
    let ξ : ℂ := path p.1
    let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + p.2.1 * Complex.I
    let z : ℂ := ((4 / 10 : ℝ) : ℂ) + p.2.2 * Complex.I
    have hw : w.re = 3 / 1000 := by simp [w]
    have hz : z.re = 4 / 10 := by simp [z]
    obtain ⟨hξlo, hξhi, hξim⟩ := hpathrange p.1
    have hξheight : |ξ.im| ≤ 2 * T ^ ZD.ρ := by
      dsimp [ξ, Ht] at *
      linarith
    have hinv := (hrec T hT u hShell hGood ξ hξlo hξheight).2
    have hpEuler : eulerNeighborhood ![ξ, w, z] := by
      left
      refine ⟨?_, ?_, ?_⟩
      · change 998 / 1000 - 1 / 100000 < ξ.re
        linarith
      · change 3 / 1000 - 1 / 100000 < w.re
        rw [hw]; norm_num
      · change 4 / 10 - 1 / 100000 < z.re
        rw [hz]; norm_num
    have hrow := rowKernel_shell_height_bound (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) u Z T ε ξ w z hZpos hTpos hε
      hShell.2.le hCD.le hCP.le hCK.le hCH.le hBrec.le hAF.le hGap
      (hDecay ξ w z hξlo hξhi hw hz) (hPrincipal z hz)
      (hKummer u hu w (by rw [hw]) (by rw [hw]; norm_num))
      (hHbound u ![ξ, w, z] hpEuler) hinv hw hz
    have hE : Estar ξ.re (3 / 1000) (4 / 10) ≤ Etop := by
      dsimp [Etop, Estar]
      linarith
    have hZpow := Real.rpow_le_rpow_of_exponent_le hZ hE
    have hExp : Real.exp (ξ.im ^ 2) ≤ Real.exp (Ht ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hsq := (sq_le_sq₀ (abs_nonneg ξ.im) hHt).2 hξim
      simpa only [sq_abs] using hsq
    have hpoly : (1 + |p.2.2|) ^ (-Adec) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg p.2.2]) (by linarith)
    have htail : Real.exp (-((ξ.im + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Adec) ≤
        Real.exp (Ht ^ 2) * Real.exp (-(1 / 2 : ℝ) * p.2.2 ^ 2) := by
      calc
        _ ≤ Real.exp (-((ξ.im + p.2.2) ^ 2)) :=
          mul_le_of_le_one_right (Real.exp_pos _).le hpoly
        _ ≤ Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * p.2.2 ^ 2) :=
          gaussian_shift_bound ξ.im p.2.2
        _ ≤ _ := mul_le_mul_of_nonneg_right hExp (Real.exp_pos _).le
    have hprod := mul_le_mul hZpow htail (by positivity)
      (Real.rpow_nonneg hZpos.le Etop)
    have hscaled := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ Ckernel * T ^ (1 / 10 + ε) * (1 + |p.2.1|) ^ (-3 : ℝ) by positivity)
    calc
      _ ≤ Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Adec) *
            (1 + |p.2.1|) ^ (-3 : ℝ) := by
        simpa [kernel, rowKernelHeightFiber, rowKernelAt, ξ, w, z, Ckernel] using hrow
      _ ≤ Bdom * ((1 + |p.2.1|) ^ (-3 : ℝ) *
          Real.exp (-(1 / 2 : ℝ) * p.2.2 ^ 2)) := by
        simpa [Bdom, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hW : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using integrable_one_add_norm (E := ℝ) hdim
  have hG : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  have hProd : Integrable (fun v : ℝ × ℝ =>
      (1 + |v.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2)) := hW.mul_prod hG
  have hmajorant : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      Bdom * ((1 + |p.2.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * p.2.2 ^ 2)))
      ((volume.restrict (Set.Icc l r)).prod volume) :=
    (integrable_const Bdom).mul_prod hProd
  have hkernel : Integrable (Function.uncurry kernel)
      ((volume.restrict (Set.Icc l r)).prod volume) :=
    hmajorant.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hfst : ∀ᵐ p : ℝ × (ℝ × ℝ) ∂(volume.restrict (Set.Icc l r)).prod volume,
      p.1 ∈ Set.Icc l r := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  apply hkernel.congr
  filter_upwards [hfst] with p hp
  have heq : clip p.1 = p.1 := by
    simp only [clip, min_eq_right hp.2, max_eq_right hp.1]
  simp only [Function.uncurry, kernel, path, Function.comp_apply, heq]

private theorem rowKernel_pair_rectangle_difference (hEuler : EulerHypotheses R η)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z ε A1 : ℝ) (hZ : 1 ≤ Z) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    let H := T ^ ZD.ρ
    Complex.I • ((∫ y : ℝ in -H..H,
        rowKernelHeightPair R sd W η U HA HC u Z
          ((1 + δ1 : ℝ) + y * Complex.I)) -
      ∫ y : ℝ in -H..H,
        rowKernelHeightPair R sd W η U HA HC u Z
          ((998 / 1000 : ℝ) + y * Complex.I)) =
    (∫ x : ℝ in (998 / 1000)..(1 + δ1),
        rowKernelHeightPair R sd W η U HA HC u Z (x + H * Complex.I)) -
      ∫ x : ℝ in (998 / 1000)..(1 + δ1),
        rowKernelHeightPair R sd W η U HA HC u Z (x + (-H) * Complex.I) := by
  let Ht : ℝ := T ^ ZD.ρ
  let aξ : ℝ := 998 / 1000
  let bξ : ℝ := 1 + δ1
  have hTpos : 0 < T := by linarith [ZD.U0_two]
  have hHt : 0 ≤ Ht := (Real.rpow_pos_of_pos hTpos _).le
  have hab : aξ ≤ bξ := by norm_num [aξ, bξ, δ1]
  have hHH : -Ht ≤ Ht := by linarith
  let Sξ : Set ℂ := {ξ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧ |ξ.im| ≤ Ht}
  have hSsubset : Sξ ⊆ {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
      |ξ.im| ≤ 2 * T ^ ZD.ρ} := by
    intro ξ hξ
    exact ⟨hξ.1, hξ.2.1, by dsimp [Ht] at hξ hHt; linarith [hξ.2.2]⟩
  have hdata := rowKernel_pair_continuousOn (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
    hShell hGood Z ε A1 hZ hε hA1 Sξ hSsubset (fun ξ hξ => hξ.2.2)
  let J : ℂ → ℝ × ℝ → ℂ := rowKernelHeightFiber R sd W η U HA HC u Z
  let P : ℂ → ℂ := rowKernelHeightPair R sd W η U HA HC u Z
  let κ₂ : ℂ := (1 / (2 * Real.pi) : ℂ) ^ 2
  have hPairEq : ∀ ξ ∈ Sξ, P ξ = κ₂ * ∫ v : ℝ × ℝ, J ξ v := by
    intro ξ hξ
    have hf : Integrable (fun v : ℝ × ℝ => rowKernelAt R sd W η U HA HC u Z ξ
        (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
        (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) := hdata.1 ξ hξ
    exact vertical_pair_eq_integral_prod
      (σw := 3 / 1000) (σz := 4 / 10)
      (fun w z => rowKernelAt R sd W η U HA HC u Z ξ w z) hf
  have hPath : ∀ l r : ℝ, l ≤ r → ∀ γ : ℝ → ℂ,
      ContinuousOn γ (Set.Icc l r) → (∀ x ∈ Set.Icc l r, γ x ∈ Sξ) →
      (∫ x : ℝ in l..r, P (γ x)) = κ₂ * ∫ v : ℝ × ℝ,
        (∫ x : ℝ in l..r, J (γ x) v) ∧
      Integrable (fun v : ℝ × ℝ => ∫ x : ℝ in l..r, J (γ x) v) := by
    intro l r hlr γ hγ hrange
    have hJoint := rowKernel_compact_path_integrable (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
      hShell hGood Z ε A1 hZ hε hA1 l r hlr γ hγ hrange
    have hJointIoc : Integrable (fun p : ℝ × (ℝ × ℝ) => J (γ p.1) p.2)
        ((volume.restrict (Set.uIoc l r)).prod volume) := by
      simpa only [J, Set.uIoc_of_le hlr, restrict_Ioc_eq_restrict_Icc] using hJoint
    refine ⟨?_, ?_⟩
    · calc
        _ = ∫ x : ℝ in l..r, κ₂ * ∫ v : ℝ × ℝ, J (γ x) v := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact hPairEq (γ x) (hrange x (by simpa only [Set.uIcc_of_le hlr] using hx))
        _ = κ₂ * (∫ x : ℝ in l..r, ∫ v : ℝ × ℝ, J (γ x) v) :=
          intervalIntegral.integral_const_mul _ _
        _ = _ := congrArg (fun q : ℂ => κ₂ * q)
          (intervalIntegral_integral_swap hJointIoc)
    · simpa only [Set.uIoc_of_le hlr, intervalIntegral.integral_of_le hlr] using
        hJointIoc.integral_prod_right
  let γR : ℝ → ℂ := fun y => (bξ : ℂ) + y * Complex.I
  let γL : ℝ → ℂ := fun y => (aξ : ℂ) + y * Complex.I
  let γTop : ℝ → ℂ := fun x => (x : ℂ) + Ht * Complex.I
  let γBot : ℝ → ℂ := fun x => (x : ℂ) + (-Ht) * Complex.I
  have hR := hPath (-Ht) Ht hHH γR (by fun_prop) (by
    intro y hy
    simpa [Sξ, γR, aξ, bξ] using
      (show aξ ≤ bξ ∧ bξ ≤ bξ ∧ |y| ≤ Ht from ⟨hab, le_rfl, abs_le.mpr hy⟩))
  have hL := hPath (-Ht) Ht hHH γL (by fun_prop) (by
    intro y hy
    simpa [Sξ, γL, aξ, bξ] using
      (show aξ ≤ aξ ∧ aξ ≤ bξ ∧ |y| ≤ Ht from ⟨le_rfl, hab, abs_le.mpr hy⟩))
  have hTop := hPath aξ bξ hab γTop (by fun_prop) (by
    intro x hx
    simpa [Sξ, γTop, aξ, bξ, abs_of_nonneg hHt] using
      (show aξ ≤ x ∧ x ≤ bξ ∧ Ht ≤ Ht from ⟨hx.1, hx.2, le_rfl⟩))
  have hBot := hPath aξ bξ hab γBot (by fun_prop) (by
    intro x hx
    simpa [Sξ, γBot, aξ, bξ, abs_of_nonneg hHt] using
      (show aξ ≤ x ∧ x ≤ bξ ∧ Ht ≤ Ht from ⟨hx.1, hx.2, le_rfl⟩))
  have hpoint : ∀ v : ℝ × ℝ,
      Complex.I * ((∫ y : ℝ in -Ht..Ht, J (γR y) v) -
        ∫ y : ℝ in -Ht..Ht, J (γL y) v) =
      (∫ x : ℝ in aξ..bξ, J (γTop x) v) -
        ∫ x : ℝ in aξ..bξ, J (γBot x) v := by
    intro v
    have hd := rowKernel_rectangle_difference (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
      hShell hGood Z (by linarith)
      (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
      (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) (by simp) (by simp)
    simpa [J, rowKernelHeightFiber, rowKernelAt, γR, γL, γTop, γBot,
      Ht, aξ, bξ, smul_eq_mul] using hd
  have hintegral : Complex.I * ((∫ v : ℝ × ℝ,
        ∫ y : ℝ in -Ht..Ht, J (γR y) v) - ∫ v : ℝ × ℝ,
        ∫ y : ℝ in -Ht..Ht, J (γL y) v) =
      (∫ v : ℝ × ℝ, ∫ x : ℝ in aξ..bξ, J (γTop x) v) -
        ∫ v : ℝ × ℝ, ∫ x : ℝ in aξ..bξ, J (γBot x) v := by
    calc
      _ = ∫ v : ℝ × ℝ, Complex.I * ((∫ y : ℝ in -Ht..Ht, J (γR y) v) -
          ∫ y : ℝ in -Ht..Ht, J (γL y) v) := by
        rw [integral_const_mul, integral_sub hR.2 hL.2]
      _ = ∫ v : ℝ × ℝ, ((∫ x : ℝ in aξ..bξ, J (γTop x) v) -
          ∫ x : ℝ in aξ..bξ, J (γBot x) v) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := integral_sub hTop.2 hBot.2
  change Complex.I • ((∫ y : ℝ in -Ht..Ht, P (γR y)) -
      ∫ y : ℝ in -Ht..Ht, P (γL y)) =
    (∫ x : ℝ in aξ..bξ, P (γTop x)) - ∫ x : ℝ in aξ..bξ, P (γBot x)
  simp only [smul_eq_mul]
  rw [hR.1, hL.1, hTop.1, hBot.1]
  linear_combination κ₂ * hintegral

private theorem rowKernel_good_pair_bounds (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 2 ≤ Z → ZD.U0 ≤ T →
      ∀ u : U.U, u ≠ U.one → u ∈ frequencyDyad η U T → u ∉ ZD.E T →
      ∀ ξ : ℂ, 998 / 1000 ≤ ξ.re → ξ.re ≤ 1 + δ1 →
      (ξ.re = 1 + δ1 ∨ |ξ.im| ≤ T ^ ZD.ρ) →
      Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume) ∧
        ‖rowKernelHeightPair R sd W η U HA HC u Z ξ‖ ≤
          C * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
            (1 + |ξ.im|) ^ (-(A1 + 2)) := by
  obtain ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
      hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH,
      hconv, hDecay, hPrincipal, hKummer, hHbound⟩ :=
    rowKernel_good_constants (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Brec, hBrec, hrec⟩ := ZD.reciprocal (ε / 3) (by linarith)
  let Bright : ℝ := (NumberField.dedekindZeta F (1 + δ1)).re *
    omittedEulerFactorsInverseConstant (S := S) + 1
  let B : ℝ := Brec + |Bright| + 1
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg Bright]
  have hBrecB : Brec ≤ B := by dsimp [B]; linarith [abs_nonneg Bright]
  have hBrightB : Bright ≤ B := by
    dsimp [B]
    linarith [le_abs_self Bright]
  let Ckernel : ℝ := CD * CP * CK * CH * B * 2 ^ AF *
    2 ^ (1 / 10 + ε / 3 + ε / 3)
  let Iw : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)
  let Cpair : ℝ := ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * Ckernel * Iw * Cconv
  have hCkernel : 0 ≤ Ckernel := by dsimp [Ckernel]; positivity
  have hIw : 0 ≤ Iw := integral_nonneg (fun _ => by positivity)
  have hCpair : 0 ≤ Cpair := by dsimp [Cpair]; positivity
  have hAdec : 0 < Adec := by linarith
  refine ⟨Cpair + 1, by linarith, ?_⟩
  intro Z T hZ hT u hu hShell hGood ξ hξlo hξhi hregion
  have hZpos : 0 < Z := by linarith
  have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
  have hTpos : 0 < T := by linarith
  have hTp : 1 ≤ T ^ (ε / 3) := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (by linarith : (0 : ℝ) ≤ ε / 3)
    simpa only [Real.rpow_zero] using hp
  have hinv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B * T ^ (ε / 3) := by
    rcases hregion with hright | hheight
    · calc
        _ ≤ Bright := rowTwist_right_inverse_bound (S := S) (η := η) (U := U) (HA := HA) u ξ hright
        _ ≤ B := hBrightB
        _ ≤ B * T ^ (ε / 3) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hTp hB.le
    · have hheight' : |ξ.im| ≤ 2 * T ^ ZD.ρ := by
        have hHnonneg := Real.rpow_nonneg hTpos.le ZD.ρ
        linarith
      exact ((hrec T hT u hShell hGood ξ hξlo hheight').2).trans
        (mul_le_mul_of_nonneg_right hBrecB (Real.rpow_nonneg hTpos.le _))
  let C0 : ℝ := Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hpoint : ∀ v : ℝ × ℝ,
      ‖rowKernelHeightFiber R sd W η U HA HC u Z ξ v‖ ≤
        C0 * Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
          (1 + |v.1|) ^ (-3 : ℝ) := by
    intro v
    let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I
    let z : ℂ := ((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I
    have hw : w.re = 3 / 1000 := by simp [w]
    have hz : z.re = 4 / 10 := by simp [z]
    have hpEuler : eulerNeighborhood ![ξ, w, z] := by
      left
      refine ⟨?_, ?_, ?_⟩
      · change 998 / 1000 - 1 / 100000 < ξ.re
        linarith
      · change 3 / 1000 - 1 / 100000 < w.re
        rw [hw]; norm_num
      · change 4 / 10 - 1 / 100000 < z.re
        rw [hz]; norm_num
    have hrow := rowKernel_shell_height_bound (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) u Z T ε ξ w z hZpos hTpos hε
      hShell.2.le hCD.le hCP.le hCK.le hCH.le hB.le hAF.le hGap
      (hDecay ξ w z hξlo hξhi hw hz) (hPrincipal z hz)
      (hKummer u hu w (by rw [hw]) (by rw [hw]; norm_num))
      (hHbound u ![ξ, w, z] hpEuler) hinv hw hz
    simpa [rowKernelHeightFiber, rowKernelAt, C0, Ckernel, w, z] using hrow
  let B0 : ℝ := C0 * Real.exp (ξ.im ^ 2)
  have hGaussian : ∀ v : ℝ × ℝ,
      ‖rowKernelHeightFiber R sd W η U HA HC u Z ξ v‖ ≤
        B0 * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2) * (1 + |v.1|) ^ (-3 : ℝ) := by
    intro v
    have hpoly : (1 + |v.2|) ^ (-Adec) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v.2]) (by linarith)
    have htail : Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) ≤
        Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2) := by
      exact (mul_le_of_le_one_right (Real.exp_pos _).le hpoly).trans
        (gaussian_shift_bound ξ.im v.2)
    calc
      _ ≤ C0 * Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
          (1 + |v.1|) ^ (-3 : ℝ) := hpoint v
      _ = (C0 * (Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec))) *
          (1 + |v.1|) ^ (-3 : ℝ) := by ring
      _ ≤ (C0 * (Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2))) *
          (1 + |v.1|) ^ (-3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hC0)
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by dsimp [B0]; ring
  have hfKernel := rowKernel_integrable_of_gaussian_bound (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZpos ξ hξlo B0
    (fun v => by simpa [rowKernelHeightFiber, rowKernelAt, Complex.ofReal_div] using hGaussian v)
  have hfiber : Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume) := by
    change Integrable (fun v : ℝ × ℝ => rowKernel R sd W η U HA HC u Z ξ
      (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
      (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) (volume.prod volume)
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat,
      Measure.volume_eq_prod ℝ ℝ] using hfKernel
  have hpair := vertical_pair_height_bound (σw := 3 / 1000) (σz := 4 / 10)
    (fun w z => rowKernelAt R sd W η U HA HC u Z ξ w z) hfiber
    Adec Ac (A1 + 2) C0 Cconv ξ.im hAdec (by linarith) hAcAdec hC0 hCconv.le
    hpoint (hconv ξ.im)
  have hbound : ‖rowKernelHeightPair R sd W η U HA HC u Z ξ‖ ≤
      Cpair * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
        (1 + |ξ.im|) ^ (-(A1 + 2)) := by
    simpa [rowKernelHeightPair, Cpair, C0, Iw, mul_assoc, mul_left_comm, mul_comm] using hpair
  refine ⟨hfiber, hbound.trans ?_⟩
  gcongr
  linarith

private theorem rowKernel_right_pair_integrable (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : ZD.U0 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (hGood : u ∉ ZD.E T)
    (Z : ℝ) (hZ : 2 ≤ Z) :
    Integrable (fun t : ℝ => rowKernelHeightPair R sd W η U HA HC u Z
      ((1 + δ1 : ℝ) + t * Complex.I)) := by
  obtain ⟨C, hC, hbound⟩ := rowKernel_good_pair_bounds (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  have hZpos : 0 < Z := by linarith
  let ξLine : ℝ → ℂ := fun t => ((1 + δ1 : ℝ) : ℂ) + t * Complex.I
  have hξcont : Continuous ξLine := by fun_prop
  have hξre (t : ℝ) : (ξLine t).re = 1 + δ1 := by simp [ξLine]
  have hξlo (t : ℝ) : 998 / 1000 ≤ (ξLine t).re := by rw [hξre]; norm_num [δ1]
  have hdata (t : ℝ) := hbound Z T hZ hT u hu hShell hGood (ξLine t) (hξlo t)
    (by rw [hξre]) (Or.inl (hξre t))
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
  have hInvMeas : Measurable (fun t : ℝ => (HA.LS S (rowTwist η U u) (ξLine t))⁻¹) :=
    (hDiffLSr.continuous.comp hξcont).measurable.inv
  have hHP := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  have hHdiff : DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := hHP.2.1 u
  let J : ℝ → ℝ × ℝ → ℂ := fun t => rowKernelHeightFiber R sd W η U HA HC u Z (ξLine t)
  have hMeasRight : ∀ v : ℝ × ℝ, Measurable (fun t : ℝ => J t v) := by
    intro v
    let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I
    let z : ℂ := ((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I
    have hw : w.re = 3 / 1000 := by simp [w]
    have hz : z.re = 4 / 10 := by simp [z]
    let pLine : ℝ → Triple := fun t => ![ξLine t, w, z]
    have hpcont : Continuous pLine := by fun_prop
    have heuler : ∀ t, eulerNeighborhood (pLine t) := by
      intro t
      left
      refine ⟨?_, ?_, ?_⟩
      · change 998 / 1000 - 1 / 100000 < (ξLine t).re
        rw [hξre]; norm_num [δ1]
      · change 3 / 1000 - 1 / 100000 < w.re
        rw [hw]; norm_num
      · change 4 / 10 - 1 / 100000 < z.re
        rw [hz]; norm_num
    have hHLine : Continuous (fun t : ℝ => HC.H u ![ξLine t, w, z]) :=
      hHdiff.continuousOn.comp_continuous hpcont heuler
    have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
    have hExpo : Continuous (fun t : ℝ => ξLine t + z - 1) := by fun_prop
    have hCpow : Continuous (fun t : ℝ => (Z : ℂ) ^ (ξLine t + z - 1)) :=
      hExpo.const_cpow (Or.inl hbaseZ)
    have hExp : Continuous (fun t : ℝ => Complex.exp ((ξLine t + z - 1) ^ 2)) := by fun_prop
    have hMellin : Continuous (fun t : ℝ =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξLine t) w z) := by
      unfold mellinWeight
      exact ((((continuous_const.mul hCpow).mul continuous_const).mul hExp).mul
        continuous_const).mul continuous_const
    have hNum : Continuous (fun t : ℝ =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξLine t) w z *
          (U.q u : ℂ) ^ (-z) * HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
            HC.H u ![ξLine t, w, z]) :=
      (((hMellin.mul continuous_const).mul continuous_const).mul continuous_const).mul hHLine
    change Measurable (fun t : ℝ => rowKernel R sd W η U HA HC u Z (ξLine t) w z)
    unfold rowKernel
    simp only [div_eq_mul_inv]
    exact hNum.measurable.mul hInvMeas
  have hFiberCont : ∀ t : ℝ, Continuous (fun v : ℝ × ℝ => J t v) := by
    intro t
    have hc := rowKernel_continuous_wz (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZpos (ξLine t) (hξlo t)
    simpa [J, rowKernelHeightFiber, rowKernelAt, Complex.ofReal_div] using hc
  have hSwap : Measurable (Function.uncurry (fun v : ℝ × ℝ => fun t : ℝ => J t v)) :=
    measurable_uncurry_of_continuous_of_measurable hFiberCont hMeasRight
  have hJoint : StronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => J p.1 p.2) := by
    have hs : StronglyMeasurable
        ((Function.uncurry (fun v : ℝ × ℝ => fun t : ℝ => J t v)) ∘
          (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)) :=
      hSwap.stronglyMeasurable.comp_measurable measurable_swap
    simpa only [Function.comp_def, Function.uncurry, Prod.swap] using hs
  have hIntMeas : StronglyMeasurable (fun t : ℝ => ∫ v : ℝ × ℝ, J t v) :=
    hJoint.integral_prod_right'
  have hPairEq (t : ℝ) : rowKernelHeightPair R sd W η U HA HC u Z (ξLine t) =
      (1 / (2 * Real.pi) : ℂ) ^ 2 * ∫ v : ℝ × ℝ, J t v := by
    have hf : Integrable (J t) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact (hdata t).1
    exact vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
      (fun w z => rowKernelAt R sd W η U HA HC u Z (ξLine t) w z) hf
  have hPairMeas : StronglyMeasurable (fun t : ℝ =>
      rowKernelHeightPair R sd W η U HA HC u Z (ξLine t)) := by
    have hs : StronglyMeasurable (fun t : ℝ => (1 / (2 * Real.pi) : ℂ) ^ 2 *
        ∫ v : ℝ × ℝ, J t v) := stronglyMeasurable_const.mul hIntMeas
    convert hs using 1
    ext t
    exact hPairEq t
  have hA1pos : 0 < A1 := lt_trans (one_div_pos.mpr ZD.ρ_pos) hA1
  have hTail : Integrable (fun t : ℝ => (1 + |t|) ^ (-(A1 + 2))) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < A1 + 2 := by simp; linarith
    simpa [Real.norm_eq_abs] using integrable_one_add_norm (E := ℝ) hdim
  have hdom := hTail.const_mul (C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
    T ^ (1 / 10 + ε))
  apply hdom.mono' hPairMeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa [ξLine] using (hdata t).2)

private theorem rowKernel_single_remainder_bound (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z T : ℝ, 2 ≤ Z → ZD.U0 ≤ T →
      ∀ u : U.U, u ≠ U.one → u ∈ frequencyDyad η U T → u ∉ ZD.E T →
      ‖vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) -
        (1 / (2 * Real.pi) : ℂ) * ∫ t in Set.Icc (-(T ^ ZD.ρ)) (T ^ ZD.ρ),
          rowKernelHeightPair R sd W η U HA HC u Z
            ((998 / 1000 : ℝ) + t * Complex.I)‖ ≤
        C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (1 / 10 + ε - ZD.ρ * A1) := by
  obtain ⟨Cpair, hCpair, hbound⟩ := rowKernel_good_pair_bounds (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  let I₂ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  let Len : ℝ := (1 + δ1) - 998 / 1000
  let κ : ℂ := (1 / (2 * Real.pi) : ℂ)
  let Ctot : ℝ := ‖κ‖ * Cpair * (I₂ + 2 * Len)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun _ => by positivity)
  have hLen : 0 ≤ Len := by norm_num [Len, δ1]
  have hCtot : 0 ≤ Ctot := by dsimp [Ctot]; positivity
  have hA1pos : 0 < A1 := lt_trans (one_div_pos.mpr ZD.ρ_pos) hA1
  have hTwo : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 := by simp
    simpa [Real.norm_eq_abs] using integrable_one_add_norm (E := ℝ) hdim
  refine ⟨Ctot + 1, by linarith, ?_⟩
  intro Z T hZ hT u hu hShell hGood
  have hZpos : 0 < Z := by linarith
  have hTpos : 0 < T := by linarith [ZD.U0_two]
  let Ht : ℝ := T ^ ZD.ρ
  have hHt : 0 < Ht := Real.rpow_pos_of_pos hTpos _
  have hHH : -Ht ≤ Ht := by linarith
  let aξ : ℝ := 998 / 1000
  let bξ : ℝ := 1 + δ1
  have hab : aξ ≤ bξ := by norm_num [aξ, bξ, δ1]
  let P : ℂ → ℂ := rowKernelHeightPair R sd W η U HA HC u Z
  let Rline : ℝ → ℂ := fun t => P ((bξ : ℂ) + t * Complex.I)
  let Lline : ℝ → ℂ := fun t => P ((aξ : ℂ) + t * Complex.I)
  let Etop : ℝ := Estar (1 + δ1) (3 / 1000) (4 / 10)
  let B0 : ℝ := Cpair * Z ^ Etop * T ^ (1 / 10 + ε)
  let g : ℝ → ℝ := fun t => (1 + |t|) ^ (-(A1 + 2))
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hRight (t : ℝ) : ‖Rline t‖ ≤ B0 * g t := by
    let ξ : ℂ := (bξ : ℂ) + t * Complex.I
    have hξre : ξ.re = 1 + δ1 := by simp [ξ, bξ]
    have hb := hbound Z T hZ hT u hu hShell hGood ξ
      (by rw [hξre]; norm_num [δ1]) (by rw [hξre]) (Or.inl hξre)
    simpa [Rline, P, B0, Etop, g, ξ, bξ] using hb.2
  have hRightInt : Integrable Rline := by
    have hi := rowKernel_right_pair_integrable (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
      u hu T hT hShell hGood Z hZ
    simpa only [Rline, P, bξ] using hi
  have hTailCmp (t : ℝ) (ht : Ht ≤ |t|) :
      g t ≤ Ht ^ (-A1) * (1 + |t|) ^ (-2 : ℝ) := by
    have hbase : 0 < 1 + |t| := by positivity
    calc
      _ = (1 + |t|) ^ (-A1) * (1 + |t|) ^ (-2 : ℝ) := by
        dsimp [g]
        rw [← Real.rpow_add hbase]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hHt (by linarith) (by linarith))
        (Real.rpow_nonneg (by positivity) _)
  have hHeightCmp (t : ℝ) (ht : Ht ≤ |t|) : g t ≤ Ht ^ (-A1) := by
    calc
      _ ≤ Ht ^ (-A1) * (1 + |t|) ^ (-2 : ℝ) := hTailCmp t ht
      _ ≤ Ht ^ (-A1) * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg t]) (by norm_num))
        (Real.rpow_nonneg hHt.le _)
      _ = _ := mul_one _
  have hTail : ‖∫ t in (Set.Icc (-Ht) Ht)ᶜ, Rline t‖ ≤ B0 * Ht ^ (-A1) * I₂ := by
    have hdom := hTwo.const_mul (B0 * Ht ^ (-A1))
    have hnorm := norm_integral_le_of_norm_le hdom.integrableOn
      (show ∀ᵐ t ∂volume.restrict (Set.Icc (-Ht) Ht)ᶜ,
        ‖Rline t‖ ≤ (B0 * Ht ^ (-A1)) * (1 + |t|) ^ (-2 : ℝ) from by
        filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
        have hnot : ¬ |t| ≤ Ht := fun hle => ht (abs_le.mp hle)
        have hge : Ht ≤ |t| := (lt_of_not_ge hnot).le
        calc
          _ ≤ B0 * g t := hRight t
          _ ≤ B0 * (Ht ^ (-A1) * (1 + |t|) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hTailCmp t hge) hB0
          _ = _ := by ring)
    have hwhole : (∫ t in (Set.Icc (-Ht) Ht)ᶜ,
        (B0 * Ht ^ (-A1)) * (1 + |t|) ^ (-2 : ℝ)) ≤
        ∫ t : ℝ, (B0 * Ht ^ (-A1)) * (1 + |t|) ^ (-2 : ℝ) :=
      setIntegral_le_integral hdom (Filter.Eventually.of_forall fun _ => by positivity)
    simpa only [integral_const_mul, I₂] using hnorm.trans hwhole
  have hHorizontal : ∀ Y : ℝ, |Y| = Ht →
      ‖∫ x : ℝ in aξ..bξ, P (x + Y * Complex.I)‖ ≤ B0 * Ht ^ (-A1) * Len := by
    intro Y hY
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := aξ) (b := bξ) (C := B0 * Ht ^ (-A1))
      (f := fun x : ℝ => P (x + Y * Complex.I)) (by
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        have hxlo : 998 / 1000 ≤ x := by simpa [aξ] using hx.1.le
        have hxhi : x ≤ 1 + δ1 := by simpa [bξ] using hx.2
        let ξ : ℂ := (x : ℂ) + Y * Complex.I
        have hξre : ξ.re = x := by simp [ξ]
        have hξim : ξ.im = Y := by simp [ξ]
        have hb := hbound Z T hZ hT u hu hShell hGood ξ
          (by rw [hξre]; exact hxlo) (by rw [hξre]; exact hxhi)
          (Or.inr (by rw [hξim, hY]))
        have hE : Estar ξ.re (3 / 1000) (4 / 10) ≤ Etop := by
          dsimp [Etop, Estar]
          rw [hξre]
          linarith
        have hZpow := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hE
        have hprod := mul_le_mul hZpow (hHeightCmp Y hY.symm.le)
          (show 0 ≤ g Y by dsimp [g]; positivity) (Real.rpow_nonneg hZpos.le Etop)
        have hscaled := mul_le_mul_of_nonneg_left hprod
          (show 0 ≤ Cpair * T ^ (1 / 10 + ε) by positivity)
        calc
          _ ≤ Cpair * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) * g Y := by
            simpa only [P, g, hξim] using hb.2
          _ ≤ _ := by simpa [B0, mul_assoc, mul_left_comm, mul_comm] using hscaled)
    simpa [Len, aξ, bξ, abs_of_nonneg (sub_nonneg.mpr hab)] using hnorm
  let Jright : ℂ := ∫ t in Set.Icc (-Ht) Ht, Rline t
  let Jleft : ℂ := ∫ t in Set.Icc (-Ht) Ht, Lline t
  let Jtop : ℂ := ∫ x : ℝ in aξ..bξ, P (x + Ht * Complex.I)
  let Jbot : ℂ := ∫ x : ℝ in aξ..bξ, P (x + (-Ht) * Complex.I)
  have hIccEq (f : ℝ → ℂ) : (∫ t in Set.Icc (-Ht) Ht, f t) = ∫ t : ℝ in -Ht..Ht, f t := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hHH]
  have hRect : Complex.I • (Jright - Jleft) = Jtop - Jbot := by
    have hr := rowKernel_pair_rectangle_difference (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler u hu T hT
      hShell hGood Z ε A1 (by linarith) hε hA1
    change Complex.I • ((∫ t : ℝ in -Ht..Ht, Rline t) -
        ∫ t : ℝ in -Ht..Ht, Lline t) = Jtop - Jbot at hr
    simpa only [Jright, Jleft, hIccEq] using hr
  have hDifference : ‖Jright - Jleft‖ ≤ 2 * B0 * Ht ^ (-A1) * Len := by
    calc
      _ = ‖Complex.I • (Jright - Jleft)‖ := by simp [norm_smul]
      _ = ‖Jtop - Jbot‖ := congrArg norm hRect
      _ ≤ ‖Jtop‖ + ‖Jbot‖ := norm_sub_le _ _
      _ ≤ (B0 * Ht ^ (-A1) * Len) + (B0 * Ht ^ (-A1) * Len) :=
        add_le_add (hHorizontal Ht (abs_of_nonneg hHt.le))
          (by simpa only [Jbot, Complex.ofReal_neg] using
            hHorizontal (-Ht) (by rw [abs_neg, abs_of_nonneg hHt.le]))
      _ = _ := by ring
  have hSplit : (∫ t : ℝ, Rline t) = Jright + ∫ t in (Set.Icc (-Ht) Ht)ᶜ, Rline t :=
    (integral_add_compl measurableSet_Icc hRightInt).symm
  have hPower : T ^ (1 / 10 + ε) * Ht ^ (-A1) =
      T ^ (1 / 10 + ε - ZD.ρ * A1) := by
    dsimp [Ht]
    rw [← Real.rpow_mul hTpos.le ZD.ρ (-A1), ← Real.rpow_add hTpos]
    congr 1
    ring
  change ‖κ * (∫ t : ℝ, Rline t) - κ * Jleft‖ ≤
    (Ctot + 1) * Z ^ Etop * T ^ (1 / 10 + ε - ZD.ρ * A1)
  calc
    _ = ‖κ * ((∫ t in (Set.Icc (-Ht) Ht)ᶜ, Rline t) + (Jright - Jleft))‖ := by
      rw [hSplit]
      congr 1
      ring
    _ = ‖κ‖ * ‖(∫ t in (Set.Icc (-Ht) Ht)ᶜ, Rline t) + (Jright - Jleft)‖ := norm_mul _ _
    _ ≤ ‖κ‖ * (‖∫ t in (Set.Icc (-Ht) Ht)ᶜ, Rline t‖ + ‖Jright - Jleft‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖κ‖ * (B0 * Ht ^ (-A1) * I₂ + 2 * B0 * Ht ^ (-A1) * Len) :=
      mul_le_mul_of_nonneg_left (add_le_add hTail hDifference) (norm_nonneg _)
    _ = Ctot * Z ^ Etop * (T ^ (1 / 10 + ε) * Ht ^ (-A1)) := by dsimp [B0, Ctot]; ring
    _ = Ctot * Z ^ Etop * T ^ (1 / 10 + ε - ZD.ρ * A1) := by rw [hPower]
    _ ≤ _ := by gcongr; linarith

private theorem goodRemainder_bound (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1) :
    ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z →
      Z ^ (9 / 100 : ℝ) < T → T ≤ Z ^ (10001 / 100000 : ℝ) → ZD.U0 ≤ T →
      ∀ rows : Finset U.U,
      (∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T ∧ u ∉ ZD.E T) →
      ‖rowContribution R sd W η U rows Z -
        goodCentral R sd W η U HA HC ZD rows T Z‖ ≤
          C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
            T ^ (11 / 10 + ε - ZD.ρ * A1) := by
  obtain ⟨Crow, hCrow, hrow⟩ := rowKernel_single_remainder_bound
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Cpair, hCpair, hpairs⟩ := rowKernel_good_pair_bounds
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Ccount, hCcount, hcount⟩ := U.dyadic_count
  obtain ⟨Csmall, hCsmall, hsmall⟩ := zf_small_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    hEuler 1 Ccount ε (by norm_num) hCcount hε
  refine ⟨Ccount * Crow, 2, mul_pos hCcount hCrow, le_rfl, ?_⟩
  intro Z T hZ _ _ hT rows hrows
  have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
  have hTpos : 0 < T := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  let Ht : ℝ := T ^ ZD.ρ
  let κ : ℂ := (1 / (2 * Real.pi) : ℂ)
  let leftLine : ℝ → ℂ := fun t => ((998 / 1000 : ℝ) : ℂ) + t * Complex.I
  let rightLine : ℝ → ℂ := fun t => ((1 + δ1 : ℝ) : ℂ) + t * Complex.I
  have hHt : 0 < Ht := Real.rpow_pos_of_pos hTpos ZD.ρ
  obtain ⟨hfinite, hcard⟩ := hcount T hT2
  have hsub : rows ⊆ hfinite.toFinset := by
    intro u hu
    exact hfinite.mem_toFinset.mpr (hrows u hu).2.1
  have hrowsCard : (rows.card : ℝ) ≤ Ccount * T := by
    calc
      _ ≤ (hfinite.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ Ccount * T := by
        simpa only [Set.ncard_eq_toFinset_card _ hfinite] using hcard
  have hPairSum (ξ : ℂ) (hξlo : 998 / 1000 ≤ ξ.re) (hξhi : ξ.re ≤ 1 + δ1)
      (hregion : ξ.re = 1 + δ1 ∨ |ξ.im| ≤ T ^ ZD.ρ) :
      vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z)) =
        ∑ u ∈ rows, rowKernelHeightPair R sd W η U HA HC u Z ξ := by
    have hf : ∀ u ∈ rows, Integrable (fun v : ℝ × ℝ =>
        rowKernel R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) := by
      intro u hu
      obtain ⟨hne, hShell, hGood⟩ := hrows u hu
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact (hpairs Z T hZ hT u hne hShell hGood ξ hξlo hξhi hregion).1
    have hsum : Integrable (fun v : ℝ × ℝ =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) :=
      integrable_finsetSum rows hf
    calc
      _ = κ ^ 2 * ∫ v : ℝ × ℝ, ∑ u ∈ rows,
          rowKernel R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
            (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) :=
        vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
          (fun w z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) hsum
      _ = ∑ u ∈ rows, κ ^ 2 * ∫ v : ℝ × ℝ,
          rowKernel R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
            (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) := by
        rw [integral_finsetSum rows hf, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
          (fun w z => rowKernelAt R sd W η U HA HC u Z ξ w z) (hf u hu)).symm
  have hRightInt : ∀ u ∈ rows, Integrable (fun t : ℝ =>
      rowKernelHeightPair R sd W η U HA HC u Z (rightLine t)) := by
    intro u hu
    obtain ⟨hne, hShell, hGood⟩ := hrows u hu
    exact rowKernel_right_pair_integrable (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD)
      hEuler ε A1 hε hA1 u hne T hT hShell hGood Z hZ
  have hFull : rowContribution R sd W η U rows Z =
      ∑ u ∈ rows, vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) := by
    have hnonprincipal : ∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T :=
      fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.1⟩
    have hcard1 : (rows.card : ℝ) ≤ Ccount * T ^ (1 : ℝ) := by
      simpa only [Real.rpow_one] using hrowsCard
    rw [(hsmall T Z (by linarith) hZ rows hnonprincipal hcard1).1]
    change κ * (∫ t : ℝ, vertical (3 / 1000) (fun w => vertical (4 / 10)
      (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (rightLine t) w z))) =
        ∑ u ∈ rows, κ * ∫ t : ℝ,
          rowKernelHeightPair R sd W η U HA HC u Z (rightLine t)
    calc
      _ = κ * ∫ t : ℝ, ∑ u ∈ rows,
          rowKernelHeightPair R sd W η U HA HC u Z (rightLine t) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => hPairSum (rightLine t)
          (by simp [rightLine]; norm_num [δ1]) (by simp [rightLine])
          (Or.inl (by simp [rightLine]))
      _ = _ := by rw [integral_finsetSum rows hRightInt, Finset.mul_sum]
  let Sξ : Set ℂ := {ξ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧ |ξ.im| ≤ Ht}
  have hSsubset : Sξ ⊆ {ξ : ℂ | 998 / 1000 ≤ ξ.re ∧ ξ.re ≤ 1 + δ1 ∧
      |ξ.im| ≤ 2 * T ^ ZD.ρ} := by
    intro ξ hξ
    exact ⟨hξ.1, hξ.2.1, by dsimp [Ht] at hξ hHt; linarith [hξ.2.2]⟩
  have hLeftMem (t : ℝ) (ht : t ∈ Set.Icc (-Ht) Ht) : leftLine t ∈ Sξ := by
    have htAbs : |t| ≤ Ht := abs_le.mpr ht
    change 998 / 1000 ≤ (leftLine t).re ∧ (leftLine t).re ≤ 1 + δ1 ∧
      |(leftLine t).im| ≤ Ht
    simpa [leftLine, δ1] using
      (show (998 / 1000 : ℝ) ≤ 998 / 1000 ∧ 998 / 1000 ≤ 1 + δ1 ∧ |t| ≤ Ht
        from ⟨le_rfl, by norm_num [δ1], htAbs⟩)
  have hLeftInt : ∀ u ∈ rows, IntegrableOn (fun t : ℝ =>
      rowKernelHeightPair R sd W η U HA HC u Z (leftLine t)) (Set.Icc (-Ht) Ht) := by
    intro u hu
    obtain ⟨hne, hShell, hGood⟩ := hrows u hu
    have hdata := rowKernel_pair_continuousOn (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) (ZD := ZD)
      hEuler u hne T hT hShell hGood Z ε A1 hZ1 hε hA1 Sξ hSsubset
      (fun ξ hξ => hξ.2.2)
    have hline : ContinuousOn leftLine (Set.Icc (-Ht) Ht) := by
      exact (show Continuous leftLine by fun_prop).continuousOn
    exact (hdata.2.comp hline hLeftMem).integrableOn_Icc
  have hLeft : goodCentral R sd W η U HA HC ZD rows T Z =
      ∑ u ∈ rows, κ * ∫ t in Set.Icc (-Ht) Ht,
        rowKernelHeightPair R sd W η U HA HC u Z (leftLine t) := by
    calc
      _ = κ * (∫ t in Set.Icc (-Ht) Ht, vertical (3 / 1000) (fun w =>
          vertical (4 / 10) (fun z => ∑ u ∈ rows,
            rowKernel R sd W η U HA HC u Z (leftLine t) w z))) := by
        simp only [goodCentral, κ, Ht, leftLine, Complex.ofReal_div, Complex.ofReal_ofNat]
      _ = κ * ∫ t in Set.Icc (-Ht) Ht, ∑ u ∈ rows,
          rowKernelHeightPair R sd W η U HA HC u Z (leftLine t) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have hmem := hLeftMem t ht
        exact hPairSum (leftLine t) hmem.1 hmem.2.1 (Or.inr hmem.2.2)
      _ = _ := by rw [integral_finsetSum rows hLeftInt, Finset.mul_sum]
  have hpower : T * T ^ (1 / 10 + ε - ZD.ρ * A1) =
      T ^ (11 / 10 + ε - ZD.ρ * A1) := by
    calc
      _ = T ^ (1 : ℝ) * T ^ (1 / 10 + ε - ZD.ρ * A1) := by rw [Real.rpow_one]
      _ = T ^ (1 + (1 / 10 + ε - ZD.ρ * A1)) :=
        (Real.rpow_add hTpos _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = ‖∑ u ∈ rows, (vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) -
        κ * ∫ t in Set.Icc (-Ht) Ht,
          rowKernelHeightPair R sd W η U HA HC u Z (leftLine t))‖ := by
      rw [hFull, hLeft, Finset.sum_sub_distrib]
    _ ≤ ∑ u ∈ rows, ‖vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) -
        κ * ∫ t in Set.Icc (-Ht) Ht,
          rowKernelHeightPair R sd W η U HA HC u Z (leftLine t)‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ rows, Crow * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
        T ^ (1 / 10 + ε - ZD.ρ * A1) := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨hne, hShell, hGood⟩ := hrows u hu
      exact hrow Z T hZ hT u hne hShell hGood
    _ = (rows.card : ℝ) * (Crow * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
        T ^ (1 / 10 + ε - ZD.ρ * A1)) := by simp
    _ ≤ (Ccount * T) * (Crow * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
        T ^ (1 / 10 + ε - ZD.ρ * A1)) :=
      mul_le_mul_of_nonneg_right hrowsCard (by positivity)
    _ = (Ccount * Crow) * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
        T ^ (11 / 10 + ε - ZD.ρ * A1) := by
      calc
        _ = (Ccount * Crow) * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          (T * T ^ (1 / 10 + ε - ZD.ρ * A1)) := by ring
        _ = _ := by rw [hpower]

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
  intro hEuler ε A1 hε hA1
  obtain ⟨Cc, hCc, hcentral⟩ := goodCentral_bound
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    (ZD := ZD) hEuler ε A1 hε hA1
  obtain ⟨Cr, Z0, hCr, hZ0, hremainder⟩ := goodRemainder_bound
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    (ZD := ZD) hEuler ε A1 hε hA1
  refine ⟨Cc + Cr, Z0, by linarith, hZ0, ?_⟩
  intro Z T hZ hTlo hThi hT rows hrows
  have hZ2 : 2 ≤ Z := le_trans hZ0 hZ
  have hT2 : 2 ≤ T := le_trans ZD.U0_two hT
  constructor
  · calc
      _ ≤ Cc * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) * T ^ (11 / 10 + ε) :=
        hcentral Z T hZ2 hT rows hrows
      _ ≤ _ := by gcongr; linarith
  · calc
      _ ≤ Cr * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (11 / 10 + ε - ZD.ρ * A1) :=
        hremainder Z T hZ hTlo hThi hT rows hrows
      _ ≤ _ := by gcongr; linarith
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

open scoped nonZeroDivisors in
open ArtinPrimitiveRoots.Hecke.EulerProduct in
private theorem finiteOrder_idealTerm_summable (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (s : ℂ) (hs : 1 < s.re) :
    Summable (idealTerm (K := F)
      (fun I : (Ideal (𝓞 F))⁰ => χ.idealValue I) s) := by
  classical
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  let count : ℕ → ℕ := fun n => Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have hprod (t : Multiset (Ideal (𝓞 F))) (g : Ideal (𝓞 F) → ℂ)
      (hg : ∀ I ∈ t, ‖g I‖ ≤ 1) : ‖(t.map g).prod‖ ≤ 1 := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons I t ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hg I (by simp)) (norm_nonneg _) <|
        ih fun J hJ => hg J (Multiset.mem_cons_of_mem hJ)
  have hfnorm : ∀ I : (Ideal (𝓞 F))⁰, ‖f I‖ ≤ 1 := by
    intro I
    dsimp [f]
    unfold HeckeChar.idealValue
    apply hprod
    intro P hP
    split_ifs with h
    · exact primeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
    · simp
  have hcard (n : ℕ) : (normFiber F n).card ≤ count n := by
    let T := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n
    have hle : (normFiber F n).card ≤ T.toFinset.card := by
      refine Finset.card_le_card_of_injOn (s := normFiber F n) (t := T.toFinset)
        (fun I => (I : Ideal (𝓞 F))) ?_ ?_
      · intro I hI
        have hnorm : Ideal.absNorm (I : Ideal (𝓞 F)) = n := (mem_normFiber F).mp hI
        exact T.mem_toFinset.mpr hnorm
      · intro I hI J hJ hEq
        exact Subtype.ext hEq
    exact hle.trans_eq (Nat.card_eq_card_finite_toFinset T).symm
  have hcount : LSeriesSummable (fun n => (count n : ℂ)) (s.re : ℂ) := by
    exact_mod_cast DedekindResidue.count_LSeriesSummable F hs
  have hcountNorm := hcount.norm
  have hfiber (n : ℕ) :
      ∑ I ∈ normFiber F n, ‖idealTerm f s I‖ ≤
        ‖LSeries.term (fun k => (count k : ℂ)) (s.re : ℂ) n‖ := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [normFiber_zero]
    calc
      _ ≤ ∑ I ∈ normFiber F n, (1 : ℝ) / (n : ℝ) ^ s.re := by
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_idealTerm, (mem_normFiber F).mp hI]
        exact div_le_div_of_nonneg_right (hfnorm I) (by positivity)
      _ = ((normFiber F n).card : ℝ) / (n : ℝ) ^ s.re := by
        rw [← Finset.sum_div]
        simp
      _ ≤ (count n : ℝ) / (n : ℝ) ^ s.re := by
        gcongr
        exact_mod_cast hcard n
      _ = _ := by
        rw [LSeries.norm_term_eq]
        simp [hn, Complex.norm_natCast]
  have hpartition : ∀ I : (Ideal (𝓞 F))⁰,
      ∃! n : ℕ, I ∈ ((fun J : (Ideal (𝓞 F))⁰ =>
        Ideal.absNorm (J : Ideal (𝓞 F))) ⁻¹' {n}) := by
    intro I
    refine ⟨Ideal.absNorm (I : Ideal (𝓞 F)), by simp, ?_⟩
    intro n hn
    simpa using hn.symm
  have hnorm : Summable (fun I : (Ideal (𝓞 F))⁰ => ‖idealTerm f s I‖) := by
    apply (summable_partition (f := fun I : (Ideal (𝓞 F))⁰ => ‖idealTerm f s I‖)
      (fun _ => norm_nonneg _) (s := fun n =>
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n})
      hpartition).2
    constructor
    · intro n
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by
        ext I
        simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      exact Summable.of_finite
    · refine Summable.of_nonneg_of_le
        (f := fun n => ‖LSeries.term (fun k => (count k : ℂ)) (s.re : ℂ) n‖)
        (g := fun n => ∑' I : (fun J : (Ideal (𝓞 F))⁰ =>
          Ideal.absNorm (J : Ideal (𝓞 F))) ⁻¹' {n}, ‖idealTerm f s I‖)
        (fun n => tsum_nonneg fun I => norm_nonneg _) (fun n => ?_) hcountNorm
      let fiber : Set ((Ideal (𝓞 F))⁰) :=
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm (I : Ideal (𝓞 F))) ⁻¹' {n}
      have hEq : fiber = {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm (I : Ideal (𝓞 F)) = n} := by
        ext I
        simp [fiber]
      letI : Fintype fiber := (hEq ▸ finite_normFiber F n).fintype
      rw [← coe_normFiber, Finset.tsum_subtype' (normFiber F n)
        (fun I => ‖idealTerm f s I‖)]
      exact hfiber n
  exact summable_norm_iff.mp hnorm

open scoped nonZeroDivisors in
open ArtinPrimitiveRoots.Hecke.EulerProduct in
private theorem incompleteHeckeLSeries_eq_complete_factors
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (s : ℂ) (hs : 1 < s.re) :
    incompleteHeckeLSeries S χ s = heckeLSeries χ s *
      ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  let f : IdealArithmeticFunction F := fun I => χ.idealValue I
  have hmul (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
      χ.idealValue (I * J) = χ.idealValue I * χ.idealValue J := by
    simp only [HeckeChar.idealValue,
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,
      Multiset.map_add, Multiset.prod_add]
  have hone : χ.idealValue (1 : Ideal (𝓞 F)) = 1 := by
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_one]
    simp
  have hprime (v : FinPlace F) : χ.idealValue v.asIdeal = χ.primeValue v := by
    unfold HeckeChar.idealValue
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible, normalize_eq]
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
    by_cases h : v.asIdeal.IsPrime ∧ v.asIdeal ≠ ⊥
    · simp [h]
    · exact (h ⟨v.isPrime, v.ne_bot⟩).elim
  have hpow (v : FinPlace F) (n : ℕ) :
      χ.idealValue (v.asIdeal ^ n) = χ.primeValue v ^ n := by
    induction n with
    | zero => simpa using hone
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ v.ne_bot) v.ne_bot, ih, hprime, pow_succ]
  have hf : f.IsMultiplicative := by
    refine ⟨hone, ?_⟩
    intro I J hIJ
    change χ.idealValue ((I : Ideal (𝓞 F)) * (J : Ideal (𝓞 F))) = _
    exact hmul _ _ (mem_nonZeroDivisors_iff_ne_zero.mp I.property)
      (mem_nonZeroDivisors_iff_ne_zero.mp J.property)
  have hsum : Summable (idealTerm f s) := finiteOrder_idealTerm_summable χ hχ s hs
  have hratio (P : FinPlace F) :
      ‖χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    have hN : 1 < Ideal.absNorm P.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm P
    have hNreal : 1 < (Ideal.absNorm P.asIdeal : ℝ) := by exact_mod_cast hN
    have hnormPow : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hN)]
      rfl
    rw [norm_mul, hnormPow]
    calc
      _ ≤ 1 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (primeValue_norm_le_one χ hχ P) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hNreal (by linarith)
  have hfactor (P : FinPlace F) : eulerFactor f P s =
      (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹ := by
    rw [eulerFactor_eq_tsum]
    have hpowRatio (n : ℕ) : idealTerm f s (P.primeIdealPow n) =
        (χ.primeValue P / (Ideal.absNorm P.asIdeal : ℂ) ^ s) ^ n := by
      dsimp only [idealTerm, f]
      rw [P.absNorm_primeIdealPow, P.coe_primeIdealPow,
        hpow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.cpow_nat_mul, div_pow]
    have hterm (n : ℕ) : idealTerm f s (P.primeIdealPow n) =
        (χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ n := by
      rw [hpowRatio, div_eq_mul_inv, Complex.cpow_neg]
    rw [tsum_congr hterm]
    exact tsum_geometric_of_norm_lt_one (hratio P)
  let e : (Ideal (𝓞 F))⁰ ≃ {I : Ideal (𝓞 F) // I ≠ ⊥} := {
    toFun := fun I => ⟨(I : Ideal (𝓞 F)), mem_nonZeroDivisors_iff_ne_zero.mp I.property⟩
    invFun := fun I => ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2⟩
    left_inv := fun I => Subtype.ext rfl
    right_inv := fun I => Subtype.ext rfl }
  have hseries : LSeries (normCoeff F f) s = heckeLSeries χ s := by
    rw [LSeries_normCoeff hsum]
    unfold heckeLSeries
    calc
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, idealTerm f s (e.symm I) :=
        Equiv.tsum_eq e (fun I => idealTerm f s (e.symm I))
      _ = _ := by
        apply tsum_congr
        intro I
        change χ.idealValue I.1 / (Ideal.absNorm I.1 : ℂ) ^ s =
          χ.idealValue I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)
        rw [div_eq_mul_inv, Complex.cpow_neg]
  let g := IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
  have hgsum : Summable (idealTerm g s) := summable_idealTerm_supportedPart hsum _
  have hprimeTo (I : Ideal (𝓞 F)) :
      Ideal.IsPrimeTo I (S.Sf : Set (FinPlace F)) ↔
        I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal := by
    simp only [Ideal.isPrimeTo_iff, Finset.mem_coe, Ideal.dvd_iff_le]
  let ep : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F))
      (S.Sf : Set (FinPlace F))} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal} := {
    toFun := fun I => ⟨(I.1 : Ideal (𝓞 F)), (hprimeTo _).mp I.2⟩
    invFun := fun I => ⟨⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr I.2.1⟩,
      (hprimeTo _).mpr I.2⟩
    left_inv := fun I => Subtype.ext (Subtype.ext rfl)
    right_inv := fun I => Subtype.ext rfl }
  have hgseries : LSeries (normCoeff F g) s = incompleteHeckeLSeries S χ s := by
    rw [LSeries_normCoeff hgsum]
    change (∑' I : (Ideal (𝓞 F))⁰, idealTerm
      (IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ) s I) = _
    rw [idealTerm_supportedPart]
    simp only [compl_compl]
    rw [← tsum_subtype]
    unfold incompleteHeckeLSeries
    calc
      _ = ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal},
          idealTerm f s (ep.symm I).1 :=
        Equiv.tsum_eq ep (fun I => idealTerm f s (ep.symm I).1)
      _ = _ := by
        apply tsum_congr
        intro I
        change χ.idealValue I.1 / (Ideal.absNorm I.1 : ℂ) ^ s =
          χ.idealValue I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s)
        rw [div_eq_mul_inv, Complex.cpow_neg]
  have hmask (P : FinPlace F) : eulerFactor g P s =
      if P ∈ S.Sf then 1 else eulerFactor f P s := by
    by_cases hP : P ∈ S.Sf
    · rw [if_pos hP, eulerFactor_eq_tsum]
      have hterm (n : ℕ) : idealTerm g s (P.primeIdealPow n) =
          if n = 0 then 1 else 0 := by
        by_cases hn : n = 0
        · subst n
          have htop : χ.idealValue (⊤ : Ideal (𝓞 F)) = 1 := by
            simpa only [Ideal.one_eq_top] using hone
          simp [idealTerm_def, g, f, htop]
        · rw [if_neg hn, idealTerm_def]
          have hnot : ¬ Ideal.IsPrimeTo (P.asIdeal ^ n) (S.Sf : Set (FinPlace F)) := by
            rw [Ideal.isPrimeTo_pow_iff hn, Ideal.isPrimeTo_asIdeal_iff]
            simpa using hP
          have hnot' : ¬ Ideal.IsPrimeTo
              ((P.primeIdealPow n : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F))
              (S.Sf : Set (FinPlace F))ᶜᶜ := by
            simpa only [P.coe_primeIdealPow, compl_compl] using hnot
          change IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
            (P.primeIdealPow n) / _ = 0
          rw [IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl hnot',
            zero_div]
      rw [tsum_congr hterm]
      simp
    · rw [if_neg hP, eulerFactor_eq_tsum, eulerFactor_eq_tsum]
      apply tsum_congr
      intro n
      have hpt : Ideal.IsPrimeTo (P.asIdeal ^ n) (S.Sf : Set (FinPlace F)) :=
        (Ideal.isPrimeTo_asIdeal_iff.mpr hP).pow n
      rw [idealTerm_def, idealTerm_def]
      change IdealArithmeticFunction.supportedPart f (S.Sf : Set (FinPlace F))ᶜ
        (P.primeIdealPow n) / _ = _
      rw [IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl
        (by simpa only [P.coe_primeIdealPow, compl_compl] using hpt)]
  have hfinite : HasProd ((S.Sf : Set (FinPlace F)).mulIndicator
      (fun P => eulerFactor f P s)) (∏ P ∈ S.Sf, eulerFactor f P s) :=
    hasProd_subtype_iff_mulIndicator.mp (S.Sf.hasProd (fun P => eulerFactor f P s))
  have hmasked := hasProd_eulerFactor g (hf.supportedPart _) hgsum
  have hfull := hasProd_eulerFactor f hf hsum
  have hproduct := hmasked.mul hfinite
  have hid : (fun P : FinPlace F => eulerFactor g P s *
      (S.Sf : Set (FinPlace F)).mulIndicator (fun P => eulerFactor f P s) P) =
      (fun P => eulerFactor f P s) := by
    funext P
    by_cases hP : P ∈ S.Sf
    · simp [hmask, hP, Set.mulIndicator_of_mem]
    · simp [hmask, hP, Set.mulIndicator_of_notMem]
  rw [hid] at hproduct
  have hrel := hfull.unique hproduct
  have hnonzero (P : FinPlace F) :
      1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have hh := hratio P
    rw [← heq] at hh
    norm_num at hh
  have hcancel : (∏ P ∈ S.Sf, eulerFactor f P s) *
      (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro P hP
    rw [hfactor]
    exact inv_mul_cancel₀ (hnonzero P)
  rw [← hgseries, ← hseries]
  calc
    _ = LSeries (normCoeff F g) s * 1 := (mul_one _).symm
    _ = LSeries (normCoeff F g) s * ((∏ P ∈ S.Sf, eulerFactor f P s) *
        (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)))) := by
      rw [hcancel]
    _ = (LSeries (normCoeff F g) s * (∏ P ∈ S.Sf, eulerFactor f P s)) *
        (∏ P ∈ S.Sf, (1 - χ.primeValue P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) :=
      (mul_assoc _ _ _).symm
    _ = _ := by rw [← hrel]

private theorem zeroDensityData_nonempty : Nonempty (ZeroDensityData η U HA) := by
  classical
  have hωη : U.omega U.one = η := by
    rw [U.omega_induces_twist, U.kummer_one]
    apply ContinuousMonoidHom.ext
    intro x
    change η x * ((1 : ℂˣ)⁻¹) = η x
    simp
  have hη : IsOfFinOrder η := by
    rw [← hωη]
    exact U.omega_finiteOrder U.one
  let L : ∀ u : U.U, U.omega u ≠ 1 → HeckeLContinuation (U.omega u) :=
    fun u hn => Classical.choose (HA.2.2.1 (U.omega u) (U.omega_finiteOrder u) hn)
  have hLeq (u : U.U) (hn : U.omega u ≠ 1) : (L u hn).value = HA.L (U.omega u) :=
    Classical.choose_spec (HA.2.2.1 (U.omega u) (U.omega_finiteOrder u) hn)
  let Linc : ∀ u : U.U, U.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (U.kummer u)⁻¹) := fun u hn => {
    value := HA.LS S (η * (U.kummer u)⁻¹)
    differentiableOn := by
      have hc : Differentiable ℂ (HA.L (U.omega u)) := by
        rw [← hLeq u hn]
        exact (L u hn).differentiable
      rw [U.omega_induces_twist] at hc
      unfold HeckeAnalysis.LS
      exact hc.differentiableOn.mul
        (omittedEulerFactors_differentiable (S := S) (η * (U.kummer u)⁻¹)).differentiableOn
    agrees := by
      intro s hs
      have hχ : IsOfFinOrder (η * (U.kummer u)⁻¹) := by
        rw [← U.omega_induces_twist]
        exact U.omega_finiteOrder u
      unfold HeckeAnalysis.LS
      have hraw : HA.L (η * (U.kummer u)⁻¹) s =
          heckeLSeries (η * (U.kummer u)⁻¹) s := HA.2.1 _ s hs
      rw [hraw, ← incompleteHeckeLSeries_eq_complete_factors _ hχ s hs] }
  have hfactor (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (s : ℂ) (hs : 0 < s.re) :
      (∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hqpos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hpow : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hqpos]
      rfl
    have hsmall : ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      calc
        _ = ‖χ.primeValue v‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_mul _ _
        _ ≤ 1 * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (primeValue_norm_le_one χ hχ v) (norm_nonneg _)
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by rw [one_mul, hpow]
        _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hs)
    intro hz
    have heq := congrArg norm (sub_eq_zero.mp hz)
    simp only [norm_one] at heq
    linarith
  obtain ⟨AF, hAF, hGrowth⟩ := zf_convexity_growth_bound (F := F)
  obtain ⟨ρ, U0, Cexc, E, hρ, hρupper, hU0, hCexc, hmain, hrec⟩ :=
    Proofs.A2ZeroDetect.zero_density_core S D η hη U L Linc AF hAF AF hAF hGrowth
  refine ⟨⟨ρ, hρ, U0, hU0, Cexc, hCexc, E, ?_, ?_, ?_, ?_⟩⟩
  · intro T hT u hu
    exact (hmain T hT).1 u hu
  · intro T hT
    simpa only [Real.rpow_eq_pow] using (hmain T hT).2.1
  · intro T hT u hu hbad
    have heq := U.omega_induces_twist u
    apply (hmain T hT).2.2 u hu.1 hu.2
    rcases hbad with hp | ⟨s, hs, ht, hz⟩
    · exact Or.inl (heq.trans hp)
    · by_cases hn : U.omega u = 1
      · exact Or.inl hn
      · refine Or.inr ⟨hn, s, hs, ht, ?_⟩
        rw [hLeq u hn, heq]
        exact hz
  · intro ε hε
    obtain ⟨C, hC, hb⟩ := hrec ε hε
    refine ⟨C, hC, ?_⟩
    intro T hT u hu hgood s hs ht
    have heq := U.omega_induces_twist u
    have hn : U.omega u ≠ 1 := by
      intro hp
      exact hgood ((hmain T hT).2.2 u hu.1 hu.2 (Or.inl hp))
    have hl : HA.L (U.omega u) s ≠ 0 := by
      intro hz
      apply hgood
      apply (hmain T hT).2.2 u hu.1 hu.2
      refine Or.inr ⟨hn, s, by linarith, ?_, ?_⟩
      · have hpow : 0 ≤ T ^ ρ := Real.rpow_nonneg (by linarith) _
        have hheight : |s.im| ≤ 4 * T ^ ρ := by nlinarith
        simpa only [Real.rpow_eq_pow] using hheight
      · rw [hLeq u hn]
        exact hz
    constructor
    · change HA.L (η * (U.kummer u)⁻¹) s *
        (∏ v ∈ S.Sf, (1 - (η * (U.kummer u)⁻¹).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) ≠ 0
      rw [← heq]
      exact mul_ne_zero hl (hfactor _ (U.omega_finiteOrder u) s (by linarith))
    · have hh := hb T hT u hu.1 hu.2 hgood hn s hs ht
      exact hh

private theorem rowKernel_right_integrable_of_shell (hEuler : EulerHypotheses R η)
    (ε A1 : ℝ) (hε : 0 < ε) (hA1 : 1 / ZD.ρ < A1)
    (u : U.U) (hu : u ≠ U.one) (T : ℝ) (hT : 2 ≤ T)
    (hShell : u ∈ frequencyDyad η U T) (Z : ℝ) (hZ : 2 ≤ Z) :
    (∀ ξ : ℂ, ξ.re = 1 + δ1 →
      Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume)) ∧
    Integrable (fun t : ℝ => rowKernelHeightPair R sd W η U HA HC u Z
      ((1 + δ1 : ℝ) + t * Complex.I)) := by
  obtain ⟨AF, Ac, Adec, Cconv, CD, CP, CK, CH,
      hAF, hAc, hGap, hAcAdec, hCconv, hCD, hCP, hCK, hCH,
      hconv, hDecay, hPrincipal, hKummer, hHbound⟩ :=
    rowKernel_good_constants (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) (ZD := ZD) hEuler ε A1 hε hA1
  let Bright : ℝ := (NumberField.dedekindZeta F (1 + δ1)).re *
    omittedEulerFactorsInverseConstant (S := S) + 1
  let B : ℝ := |Bright| + 1
  have hB : 0 < B := by dsimp [B]; linarith [abs_nonneg Bright]
  have hBrightB : Bright ≤ B := by
    dsimp [B]
    linarith [le_abs_self Bright]
  let Ckernel : ℝ := CD * CP * CK * CH * B * 2 ^ AF *
    2 ^ (1 / 10 + ε / 3 + ε / 3)
  let Iw : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)
  let Cpair : ℝ := ‖(1 / (2 * Real.pi) : ℂ) ^ 2‖ * Ckernel * Iw * Cconv
  have hCkernel : 0 ≤ Ckernel := by dsimp [Ckernel]; positivity
  have hIw : 0 ≤ Iw := integral_nonneg (fun _ => by positivity)
  have hCpair : 0 ≤ Cpair := by dsimp [Cpair]; positivity
  have hAdec : 0 < Adec := by linarith
  have hZpos : 0 < Z := by linarith
  have hTpos : 0 < T := by linarith
  have hTp : 1 ≤ T ^ (ε / 3) := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (by linarith : (0 : ℝ) ≤ ε / 3)
    simpa only [Real.rpow_zero] using hp
  have hboundAll (ξ : ℂ) (hξright : ξ.re = 1 + δ1) :
      Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume) ∧
        ‖rowKernelHeightPair R sd W η U HA HC u Z ξ‖ ≤
          Cpair * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
            (1 + |ξ.im|) ^ (-(A1 + 2)) := by
    have hξlo : 998 / 1000 ≤ ξ.re := by rw [hξright]; norm_num [δ1]
    have hξhi : ξ.re ≤ 1 + δ1 := hξright.le
    have hinv : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B * T ^ (ε / 3) := by
      calc
        _ ≤ Bright := rowTwist_right_inverse_bound (S := S) (η := η) (U := U)
          (HA := HA) u ξ hξright
        _ ≤ B := hBrightB
        _ ≤ B * T ^ (ε / 3) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hTp hB.le
    let C0 : ℝ := Ckernel * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε)
    have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
    have hpoint : ∀ v : ℝ × ℝ,
        ‖rowKernelHeightFiber R sd W η U HA HC u Z ξ v‖ ≤
          C0 * Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
            (1 + |v.1|) ^ (-3 : ℝ) := by
      intro v
      let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I
      let z : ℂ := ((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I
      have hw : w.re = 3 / 1000 := by simp [w]
      have hz : z.re = 4 / 10 := by simp [z]
      have hpEuler : eulerNeighborhood ![ξ, w, z] := by
        left
        refine ⟨?_, ?_, ?_⟩
        · change 998 / 1000 - 1 / 100000 < ξ.re
          linarith
        · change 3 / 1000 - 1 / 100000 < w.re
          rw [hw]; norm_num
        · change 4 / 10 - 1 / 100000 < z.re
          rw [hz]; norm_num
      have hrow := rowKernel_shell_height_bound (R := R) (sd := sd) (W := W)
        (η := η) (U := U) (HA := HA) (HC := HC) u Z T ε ξ w z hZpos hTpos hε
        hShell.2.le hCD.le hCP.le hCK.le hCH.le hB.le hAF.le hGap
        (hDecay ξ w z hξlo hξhi hw hz) (hPrincipal z hz)
        (hKummer u hu w (by rw [hw]) (by rw [hw]; norm_num))
        (hHbound u ![ξ, w, z] hpEuler) hinv hw hz
      simpa [rowKernelHeightFiber, rowKernelAt, C0, Ckernel, w, z] using hrow
    let B0 : ℝ := C0 * Real.exp (ξ.im ^ 2)
    have hGaussian : ∀ v : ℝ × ℝ,
        ‖rowKernelHeightFiber R sd W η U HA HC u Z ξ v‖ ≤
          B0 * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2) * (1 + |v.1|) ^ (-3 : ℝ) := by
      intro v
      have hpoly : (1 + |v.2|) ^ (-Adec) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v.2]) (by linarith)
      have htail : Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) ≤
          Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2) := by
        exact (mul_le_of_le_one_right (Real.exp_pos _).le hpoly).trans
          (gaussian_shift_bound ξ.im v.2)
      calc
        _ ≤ C0 * Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec) *
            (1 + |v.1|) ^ (-3 : ℝ) := hpoint v
        _ = (C0 * (Real.exp (-((ξ.im + v.2) ^ 2)) * (1 + |v.2|) ^ (-Adec))) *
            (1 + |v.1|) ^ (-3 : ℝ) := by ring
        _ ≤ (C0 * (Real.exp (ξ.im ^ 2) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2))) *
            (1 + |v.1|) ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hC0)
            (Real.rpow_nonneg (by positivity) _)
        _ = _ := by dsimp [B0]; ring
    have hfKernel := rowKernel_integrable_of_gaussian_bound (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZpos ξ hξlo B0
      (fun v => by simpa [rowKernelHeightFiber, rowKernelAt, Complex.ofReal_div] using hGaussian v)
    have hfiber : Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume) := by
      change Integrable (fun v : ℝ × ℝ => rowKernel R sd W η U HA HC u Z ξ
        (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
        (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) (volume.prod volume)
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat,
        Measure.volume_eq_prod ℝ ℝ] using hfKernel
    have hpair := vertical_pair_height_bound (σw := 3 / 1000) (σz := 4 / 10)
      (fun w z => rowKernelAt R sd W η U HA HC u Z ξ w z) hfiber
      Adec Ac (A1 + 2) C0 Cconv ξ.im hAdec (by linarith) hAcAdec hC0 hCconv.le
      hpoint (hconv ξ.im)
    have hbound : ‖rowKernelHeightPair R sd W η U HA HC u Z ξ‖ ≤
        Cpair * Z ^ Estar ξ.re (3 / 1000) (4 / 10) * T ^ (1 / 10 + ε) *
          (1 + |ξ.im|) ^ (-(A1 + 2)) := by
      simpa [rowKernelHeightPair, Cpair, C0, Iw, mul_assoc, mul_left_comm, mul_comm] using hpair
    exact ⟨hfiber, by simpa only [hξright] using hbound⟩
  refine ⟨fun ξ hξ => (hboundAll ξ hξ).1, ?_⟩
  let ξLine : ℝ → ℂ := fun t => ((1 + δ1 : ℝ) : ℂ) + t * Complex.I
  have hξcont : Continuous ξLine := by fun_prop
  have hξre (t : ℝ) : (ξLine t).re = 1 + δ1 := by simp [ξLine]
  have hξlo (t : ℝ) : 998 / 1000 ≤ (ξLine t).re := by rw [hξre]; norm_num [δ1]
  have hdata (t : ℝ) := hboundAll (ξLine t) (hξre t)
  have hrowEq : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have hrowFin : IsOfFinOrder (rowTwist η U u) := by
    rw [hrowEq]
    exact U.omega_finiteOrder u
  have hDiffLr : DifferentiableOn ℂ (HA.L (rowTwist η U u)) {s : ℂ | 1 < s.re} := by
    by_cases hrow : rowTwist η U u = 1
    · rw [hrow]
      apply HA.2.2.2.1.mono
      intro s hs
      change 1 < s.re at hs
      change s ≠ 1
      intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
      linarith
    · obtain ⟨Lr, hLr⟩ := HA.2.2.1 (rowTwist η U u) hrowFin hrow
      have hEq : Lr.value = HA.L (rowTwist η U u) := hLr
      rw [← hEq]
      exact Lr.differentiable.differentiableOn
  have hDiffLSr : DifferentiableOn ℂ (HA.LS S (rowTwist η U u))
      {s : ℂ | 1 < s.re} := by
    unfold HeckeAnalysis.LS
    exact hDiffLr.mul
      (omittedEulerFactors_differentiable (S := S) (rowTwist η U u)).differentiableOn
  have hLSLine : Continuous (fun t : ℝ => HA.LS S (rowTwist η U u) (ξLine t)) :=
    hDiffLSr.continuousOn.comp_continuous hξcont (by
      intro t
      change 1 < (ξLine t).re
      rw [hξre]
      norm_num [δ1])
  have hInvMeas : Measurable (fun t : ℝ => (HA.LS S (rowTwist η U u) (ξLine t))⁻¹) :=
    hLSLine.measurable.inv
  have hHP := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  have hHdiff : DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p} := hHP.2.1 u
  let J : ℝ → ℝ × ℝ → ℂ := fun t => rowKernelHeightFiber R sd W η U HA HC u Z (ξLine t)
  have hMeasRight : ∀ v : ℝ × ℝ, Measurable (fun t : ℝ => J t v) := by
    intro v
    let w : ℂ := ((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I
    let z : ℂ := ((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I
    have hw : w.re = 3 / 1000 := by simp [w]
    have hz : z.re = 4 / 10 := by simp [z]
    let pLine : ℝ → Triple := fun t => ![ξLine t, w, z]
    have hpcont : Continuous pLine := by fun_prop
    have heuler : ∀ t, eulerNeighborhood (pLine t) := by
      intro t
      left
      refine ⟨?_, ?_, ?_⟩
      · change 998 / 1000 - 1 / 100000 < (ξLine t).re
        rw [hξre]; norm_num [δ1]
      · change 3 / 1000 - 1 / 100000 < w.re
        rw [hw]; norm_num
      · change 4 / 10 - 1 / 100000 < z.re
        rw [hz]; norm_num
    have hHLine : Continuous (fun t : ℝ => HC.H u ![ξLine t, w, z]) :=
      hHdiff.continuousOn.comp_continuous hpcont heuler
    have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
    have hExpo : Continuous (fun t : ℝ => ξLine t + z - 1) := by fun_prop
    have hCpow : Continuous (fun t : ℝ => (Z : ℂ) ^ (ξLine t + z - 1)) :=
      hExpo.const_cpow (Or.inl hbaseZ)
    have hExp : Continuous (fun t : ℝ => Complex.exp ((ξLine t + z - 1) ^ 2)) := by fun_prop
    have hMellin : Continuous (fun t : ℝ =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξLine t) w z) := by
      unfold mellinWeight
      exact ((((continuous_const.mul hCpow).mul continuous_const).mul hExp).mul
        continuous_const).mul continuous_const
    have hNum : Continuous (fun t : ℝ =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξLine t) w z *
          (U.q u : ℂ) ^ (-z) * HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w *
            HC.H u ![ξLine t, w, z]) :=
      (((hMellin.mul continuous_const).mul continuous_const).mul continuous_const).mul hHLine
    change Measurable (fun t : ℝ => rowKernel R sd W η U HA HC u Z (ξLine t) w z)
    unfold rowKernel
    simp only [div_eq_mul_inv]
    exact hNum.measurable.mul hInvMeas
  have hFiberCont : ∀ t : ℝ, Continuous (fun v : ℝ × ℝ => J t v) := by
    intro t
    have hc := rowKernel_continuous_wz (R := R) (sd := sd) (W := W)
      (η := η) (U := U) (HA := HA) (HC := HC) hEuler u hu Z hZpos (ξLine t) (hξlo t)
    simpa [J, rowKernelHeightFiber, rowKernelAt, Complex.ofReal_div] using hc
  have hSwap : Measurable (Function.uncurry (fun v : ℝ × ℝ => fun t : ℝ => J t v)) :=
    measurable_uncurry_of_continuous_of_measurable hFiberCont hMeasRight
  have hJoint : StronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => J p.1 p.2) := by
    have hs : StronglyMeasurable
        ((Function.uncurry (fun v : ℝ × ℝ => fun t : ℝ => J t v)) ∘
          (Prod.swap : ℝ × (ℝ × ℝ) → (ℝ × ℝ) × ℝ)) :=
      hSwap.stronglyMeasurable.comp_measurable measurable_swap
    simpa only [Function.comp_def, Function.uncurry, Prod.swap] using hs
  have hIntMeas : StronglyMeasurable (fun t : ℝ => ∫ v : ℝ × ℝ, J t v) :=
    hJoint.integral_prod_right'
  have hPairEq (t : ℝ) : rowKernelHeightPair R sd W η U HA HC u Z (ξLine t) =
      (1 / (2 * Real.pi) : ℂ) ^ 2 * ∫ v : ℝ × ℝ, J t v := by
    have hf : Integrable (J t) := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact (hdata t).1
    exact vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
      (fun w z => rowKernelAt R sd W η U HA HC u Z (ξLine t) w z) hf
  have hPairMeas : StronglyMeasurable (fun t : ℝ =>
      rowKernelHeightPair R sd W η U HA HC u Z (ξLine t)) := by
    have hs : StronglyMeasurable (fun t : ℝ => (1 / (2 * Real.pi) : ℂ) ^ 2 *
        ∫ v : ℝ × ℝ, J t v) := stronglyMeasurable_const.mul hIntMeas
    convert hs using 1
    ext t
    exact hPairEq t
  have hA1pos : 0 < A1 := lt_trans (one_div_pos.mpr ZD.ρ_pos) hA1
  have hTail : Integrable (fun t : ℝ => (1 + |t|) ^ (-(A1 + 2))) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < A1 + 2 := by simp; linarith
    simpa [Real.norm_eq_abs] using integrable_one_add_norm (E := ℝ) hdim
  have hdom := hTail.const_mul (Cpair * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
    T ^ (1 / 10 + ε))
  apply hdom.mono' hPairMeas.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa [ξLine] using (hdata t).2)


include HA HC in
private theorem rowContribution_eq_sum (hEuler : EulerHypotheses R η)
    (T Z : ℝ) (hT : 2 ≤ T) (hZ : 2 ≤ Z) (rows : Finset U.U)
    (hrows : ∀ u ∈ rows, u ≠ U.one ∧ u ∈ frequencyDyad η U T) :
    rowContribution R sd W η U rows Z =
      ∑ u ∈ rows, rowContribution R sd W η U {u} Z := by
  obtain ⟨ZD⟩ := zeroDensityData_nonempty (η := η) (U := U) (HA := HA)
  let A1 : ℝ := 2 / ZD.ρ
  have hA1 : 1 / ZD.ρ < A1 := by
    dsimp [A1]
    exact (div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) ZD.ρ_pos)
  let κ : ℂ := (1 / (2 * Real.pi) : ℂ)
  let rightLine : ℝ → ℂ := fun t => ((1 + δ1 : ℝ) : ℂ) + t * Complex.I
  have hInts (u : U.U) (hu : u ∈ rows) :
      (∀ ξ : ℂ, ξ.re = 1 + δ1 →
        Integrable (rowKernelHeightFiber R sd W η U HA HC u Z ξ) (volume.prod volume)) ∧
      Integrable (fun t : ℝ => rowKernelHeightPair R sd W η U HA HC u Z
        ((1 + δ1 : ℝ) + t * Complex.I)) :=
    rowKernel_right_integrable_of_shell (R := R) (sd := sd) (W := W) (η := η)
      (U := U) (HA := HA) (HC := HC) (ZD := ZD) hEuler 1 A1 (by norm_num) hA1
      u (hrows u hu).1 T hT (hrows u hu).2 Z hZ
  obtain ⟨Csmall, hCsmall, hsmall⟩ := zf_small_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    hEuler 0 ((rows.card : ℝ) + 1) 1 (by norm_num) (by positivity) (by norm_num)
  have hshift (C : Finset U.U) (hsub : C ⊆ rows) :
      rowContribution R sd W η U C Z = tripleVertical (1 + δ1) (3 / 1000) (4 / 10)
        (fun ξ w z => ∑ u ∈ C, rowKernel R sd W η U HA HC u Z ξ w z) := by
    have hcard : (C.card : ℝ) ≤ ((rows.card : ℝ) + 1) * T ^ (0 : ℝ) := by
      rw [Real.rpow_zero, mul_one]
      have hle : (C.card : ℝ) ≤ rows.card := by exact_mod_cast Finset.card_le_card hsub
      linarith
    exact (hsmall T Z (by linarith) hZ C (fun u hu => hrows u (hsub hu)) hcard).1
  have hPairSum (ξ : ℂ) (hξright : ξ.re = 1 + δ1) :
      vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z)) =
        ∑ u ∈ rows, rowKernelHeightPair R sd W η U HA HC u Z ξ := by
    have hf : ∀ u ∈ rows, Integrable (fun v : ℝ × ℝ =>
        rowKernel R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) := by
      intro u hu
      rw [Measure.volume_eq_prod ℝ ℝ]
      exact (hInts u hu).1 ξ hξright
    have hsum : Integrable (fun v : ℝ × ℝ =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ
          (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
          (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I)) :=
      integrable_finsetSum rows hf
    calc
      _ = κ ^ 2 * ∫ v : ℝ × ℝ, ∑ u ∈ rows,
          rowKernel R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
            (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) :=
        vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
          (fun w z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) hsum
      _ = ∑ u ∈ rows, κ ^ 2 * ∫ v : ℝ × ℝ,
          rowKernel R sd W η U HA HC u Z ξ
            (((3 / 1000 : ℝ) : ℂ) + v.1 * Complex.I)
            (((4 / 10 : ℝ) : ℂ) + v.2 * Complex.I) := by
        rw [integral_finsetSum rows hf, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (vertical_pair_eq_integral_prod (σw := 3 / 1000) (σz := 4 / 10)
          (fun w z => rowKernelAt R sd W η U HA HC u Z ξ w z) (hf u hu)).symm
  have hRightInt : ∀ u ∈ rows, Integrable (fun t : ℝ =>
      rowKernelHeightPair R sd W η U HA HC u Z (rightLine t)) := by
    intro u hu
    exact (hInts u hu).2
  have hFull : rowContribution R sd W η U rows Z =
      ∑ u ∈ rows, vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) := by
    rw [hshift rows (by intro u hu; exact hu)]
    change κ * (∫ t : ℝ, vertical (3 / 1000) (fun w => vertical (4 / 10)
      (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z (rightLine t) w z))) =
        ∑ u ∈ rows, κ * ∫ t : ℝ,
          rowKernelHeightPair R sd W η U HA HC u Z (rightLine t)
    calc
      _ = κ * ∫ t : ℝ, ∑ u ∈ rows,
          rowKernelHeightPair R sd W η U HA HC u Z (rightLine t) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => hPairSum (rightLine t)
          (by simp [rightLine])
      _ = _ := by rw [integral_finsetSum rows hRightInt, Finset.mul_sum]
  have hsingle (u : U.U) (hu : u ∈ rows) :
      rowContribution R sd W η U {u} Z =
        vertical (1 + δ1) (rowKernelHeightPair R sd W η U HA HC u Z) := by
    rw [hshift {u} (by
      intro v hv
      rcases Finset.mem_singleton.mp hv with rfl
      exact hu)]
    simp only [Finset.sum_singleton]
    rfl
  calc
    _ = ∑ u ∈ rows, vertical (1 + δ1)
        (rowKernelHeightPair R sd W η U HA HC u Z) := hFull
    _ = _ := Finset.sum_congr rfl fun u hu => (hsingle u hu).symm

private theorem dyadic_power_small_sum (p x : ℝ) (hp : 0 < p) (hx : 1 ≤ x) :
    Summable (fun j : ℕ => if (2 : ℝ) ^ j ≤ x then ((2 : ℝ) ^ j) ^ p else 0) ∧
      (∑' j : ℕ, if (2 : ℝ) ^ j ≤ x then ((2 : ℝ) ^ j) ^ p else 0) ≤
        ((2 : ℝ) ^ p / ((2 : ℝ) ^ p - 1)) * x ^ p := by
  classical
  obtain ⟨N, hNlo, hNhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  let r : ℝ := (2 : ℝ) ^ p
  let g : ℕ → ℝ := fun j => if (2 : ℝ) ^ j ≤ x then ((2 : ℝ) ^ j) ^ p else 0
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hp
  have hpower (j : ℕ) : ((2 : ℝ) ^ j) ^ p = r ^ j :=
    (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) p j).symm
  have hcut (j : ℕ) : (2 : ℝ) ^ j ≤ x ↔ j ∈ Finset.range (N + 1) := by
    constructor
    · intro hj
      apply Finset.mem_range.mpr
      by_contra hge
      have hNj : N + 1 ≤ j := Nat.le_of_not_gt hge
      have hle : (2 : ℝ) ^ (N + 1) ≤ (2 : ℝ) ^ j :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hNj
      linarith
    · intro hj
      have hJN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJN).trans hNlo
  have hzero : ∀ j ∉ Finset.range (N + 1), g j = 0 := by
    intro j hj
    have hnot : ¬ (2 : ℝ) ^ j ≤ x := mt (hcut j).mp hj
    simp [g, hnot]
  have hsum : Summable g := summable_of_ne_finset_zero hzero
  have hpartial : (∑' j, g j) = ∑ j ∈ Finset.range (N + 1), r ^ j := by
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [g, if_pos ((hcut j).mpr hj), hpower j]
  have hpowLe : r ^ N ≤ x ^ p := by
    rw [← hpower N]
    exact Real.rpow_le_rpow (by positivity) hNlo hp.le
  refine ⟨hsum, ?_⟩
  change (∑' j, g j) ≤ (r / (r - 1)) * x ^ p
  calc
    _ = (r ^ (N + 1) - 1) / (r - 1) := by
      rw [hpartial, geom_sum_eq (ne_of_gt hr)]
    _ ≤ r ^ (N + 1) / (r - 1) :=
      div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ = (r * r ^ N) / (r - 1) := by rw [pow_succ, mul_comm (r ^ N) r]
    _ ≤ (r * x ^ p) / (r - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowLe (by linarith)) (by linarith)
    _ = _ := by ring

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
include U in
private theorem principalLS_half_plane_inputs (hEuler : EulerHypotheses R η) :
    DifferentiableOn ℂ (HA.LS S η) {s : ℂ | 1 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → HA.LS S η s ≠ 0) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, 2 ≤ s.re → ‖(HA.LS S η s)⁻¹‖ ≤ B := by
  have hcomplete : DifferentiableOn ℂ (HA.L η) {s : ℂ | 1 < s.re} := by
    by_cases hη1 : η = 1
    · subst η
      apply HA.2.2.2.1.mono
      intro s hs
      change 1 < s.re at hs
      change s ≠ 1
      intro hEq
      have hRe := congrArg Complex.re hEq
      norm_num at hRe
      linarith
    · obtain ⟨C, hC⟩ := HA.2.2.1 η hEuler.1 hη1
      have hEq : C.value = HA.L η := hC
      rw [← hEq]
      exact C.differentiable.differentiableOn.mono fun s hs => Set.mem_univ s
  have hdiff : DifferentiableOn ℂ (HA.LS S η) {s : ℂ | 1 < s.re} := by
    unfold HeckeAnalysis.LS
    exact hcomplete.mul (omittedEulerFactors_differentiable (S := S) η).differentiableOn
  obtain ⟨f, hf⟩ := U.omega_primitive U.one
  have hωη : U.omega U.one = η := by
    rw [U.omega_induces_twist, U.kummer_one]
    apply ContinuousMonoidHom.ext
    intro x
    change η x * ((1 : ℂˣ)⁻¹) = η x
    simp
  rw [hωη] at hf
  obtain ⟨m, ψ, hmod, hseries⟩ :=
    primitive_heckeLSeries_eq_ray η hEuler.1 f hf
  have hraw (s : ℂ) (hs : 1 < s.re) : HA.L η s = Hecke.LSeriesRay ψ s :=
    (HA.2.1 η s hs).trans (hseries s hs)
  have hfactor (s : ℂ) (hs : 1 < s.re) (v : FinPlace F) :
      1 - η.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
    have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hpow : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
    have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hnorm : ‖η.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      calc
        _ = ‖η.primeValue v‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_mul _ _
        _ ≤ 1 * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (primeValue_norm_le_one η hEuler.1 v) (norm_nonneg _)
        _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by rw [one_mul, hpow]
        _ < 1 := hlt
    intro hzero
    have heq := sub_eq_zero.mp hzero
    have heqnorm := congrArg norm heq
    simp only [norm_one] at heqnorm
    linarith
  have hnonzero (s : ℂ) (hs : 1 < s.re) : HA.LS S η s ≠ 0 := by
    unfold HeckeAnalysis.LS
    apply mul_ne_zero
    · rw [hraw s hs]
      exact (Hecke.norm_LSeriesRay_le ψ hs).2.1
    · exact Finset.prod_ne_zero_iff.mpr fun v hv => hfactor s hs v
  let ψ0 : ClassFieldTheory.RayClassGroup
      (⟨0, ∅⟩ : ClassFieldTheory.RayClassModulus F) →* ℂˣ := 1
  let Cζ : ℝ := ∑' n : ℕ, ‖LSeries.term (Hecke.coeff ψ0) (2 : ℂ) n‖
  have hCζ : 0 ≤ Cζ := tsum_nonneg fun n => norm_nonneg _
  have hζbound (σ : ℝ) (hσ : 2 ≤ σ) : (NumberField.dedekindZeta F σ).re ≤ Cζ := by
    have hσ1 : 1 < (σ : ℂ).re := by simpa using lt_of_lt_of_le (by norm_num) hσ
    have hsum2 := (Hecke.LSeriesSummable_coeff (K := F) ψ0 (s := (2 : ℂ)) (by norm_num)).norm
    have hsumσ := (Hecke.LSeriesSummable_coeff (K := F) ψ0 (s := (σ : ℂ)) hσ1).norm
    calc
      (NumberField.dedekindZeta F σ).re ≤ ‖NumberField.dedekindZeta F σ‖ := Complex.re_le_norm _
      _ = ‖Hecke.LSeriesRay ψ0 (σ : ℂ)‖ := by
        rw [Hecke.LSeriesRay_trivial_eq_dedekindZeta]
      _ ≤ ∑' n : ℕ, ‖LSeries.term (Hecke.coeff ψ0) (σ : ℂ) n‖ := norm_tsum_le_tsum_norm hsumσ
      _ ≤ Cζ := by
        apply hsumσ.tsum_le_tsum _ hsum2
        intro n
        exact LSeries.norm_term_le_of_re_le_re (Hecke.coeff ψ0) (by simpa using hσ) n
  obtain ⟨hCF, hFbound⟩ := omittedEulerFactors_inv_bound (S := S) η hEuler.1
  refine ⟨hdiff, hnonzero, Cζ * omittedEulerFactorsInverseConstant (S := S) + 1,
    by positivity, ?_⟩
  intro s hs
  have hs1 : 1 < s.re := by linarith
  have hsδ : 1 + δ1 ≤ s.re :=
    (by norm_num [δ1] : 1 + δ1 ≤ (2 : ℝ)).trans hs
  have hfactorInv := (hFbound s hsδ).2
  have hRayInv : ‖(Hecke.LSeriesRay ψ s)⁻¹‖ ≤ Cζ :=
    (Hecke.norm_LSeriesRay_le ψ hs1).2.2.trans (hζbound s.re hs)
  have hLSfactor : HA.LS S η s = Hecke.LSeriesRay ψ s *
      ∏ v ∈ S.Sf, (1 - η.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    unfold HeckeAnalysis.LS
    rw [hraw s hs1]
  calc
    ‖(HA.LS S η s)⁻¹‖ = ‖(Hecke.LSeriesRay ψ s)⁻¹‖ *
        ‖(∏ v ∈ S.Sf, (1 - η.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹‖ := by
      rw [hLSfactor, mul_inv, norm_mul]
    _ ≤ Cζ * omittedEulerFactorsInverseConstant (S := S) :=
      mul_le_mul hRayInv hfactorInv (norm_nonneg _) hCζ
    _ ≤ Cζ * omittedEulerFactorsInverseConstant (S := S) + 1 := by linarith

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
  intro hEuler hloc hWeight
  have hH := po_H_eta_properties (R := R) (η := η) (U := U) (HC := HC) hEuler hloc
  have hHdiff : DifferentiableOn ℂ (Heta R η U HC) {s : ℂ | 998 / 1000 < s.re} :=
    hH.1.mono (by intro s hs; change 998 / 1000 < s.re at hs; change 998 / 1000 - 1 / 100000 < s.re; linarith)
  obtain ⟨BH, hBH, hHbound⟩ := hH.2.2
  have hHb : ∃ B : ℝ, ∀ s : ℂ, 998 / 1000 < s.re → ‖Heta R η U HC s‖ ≤ B :=
    ⟨BH, fun s hs => hHbound s (by linarith)⟩
  have hL := principalLS_half_plane_inputs (R := R) (η := η) (U := U) (HA := HA) hEuler
  obtain ⟨BL, hBL, hLbound⟩ := hL.2.2
  have hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(HA.LS S η s)⁻¹‖ ≤ B := ⟨BL, hLbound⟩
  have hcont : ContinuousOn (principalSignal R η U HA HC) (Set.Ioi 0) :=
    fEta_continuousOn_of_bounds _ _ hHdiff hL.1 hL.2.1 hHb hLb
  have hsmall : ∀ A0 : ℝ, 0 < A0 → ∃ C : ℝ, 0 < C ∧ ∀ Z,
      0 < Z → Z ≤ 1 → ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ A0 :=
    ArtinPrimitiveRoots.Proofs.a2_pasym_sol.fEta_small_bounds_of_bounds
      _ _ hHdiff hL.1 hL.2.1 hHb hLb
  have hc0 : principalConstant R sd W HA ≠ 0 :=
    (zf_principal_row (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) hEuler hloc hWeight).1
  have hc0norm : 0 < ‖principalConstant R sd W HA‖ := norm_pos_iff.mpr hc0
  obtain ⟨CL, hCL, hLow⟩ := prop_probe_low (R := R) (W := W) η hSplit
    (1 / 100000) (by norm_num)
  obtain ⟨CErr, Z0, hCErr, hZ0, hErr⟩ :=
    zf_probe_asymptotic (R := R) (sd := sd) (W := W) (η := η) (U := U)
      (HA := HA) (HC := HC) hSplit hEuler hloc hWeight
  have hlarge : ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
      ‖principalSignal R η U HA HC Z‖ ≤ C * Z ^ ((7 / 15 - 1 / 20000 : ℝ)) := by
    refine ⟨(CL + CErr) / ‖principalConstant R sd W HA‖, Z0,
      div_pos (add_pos hCL hCErr) hc0norm, hZ0, ?_⟩
    intro Z hZ
    have hZ2 : 2 ≤ Z := hZ0.trans hZ
    have hZ1 : 1 ≤ Z := (by norm_num : (1 : ℝ) ≤ 2).trans hZ2
    have hLowPower : Z ^ ((933 / 2000 : ℝ) + 1 / 100000) ≤
        Z ^ ((7 / 15 - 1 / 20000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    have hErrPower : Z ^ ((7 / 15 - 4 / 10000 : ℝ)) ≤
        Z ^ ((7 / 15 - 1 / 20000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
    have hprod : ‖principalConstant R sd W HA‖ * ‖principalSignal R η U HA HC Z‖ ≤
        (CL + CErr) * Z ^ ((7 / 15 - 1 / 20000 : ℝ)) := by
      calc
        _ = ‖principalConstant R sd W HA * principalSignal R η U HA HC Z‖ :=
          (norm_mul _ _).symm
        _ ≤ ‖probe R W (Z ^ a) (Z ^ b) Z‖ +
            ‖probe R W (Z ^ a) (Z ^ b) Z -
              principalConstant R sd W HA * principalSignal R η U HA HC Z‖ := by
          exact norm_le_insert (probe R W (Z ^ a) (Z ^ b) Z)
            (principalConstant R sd W HA * principalSignal R η U HA HC Z)
        _ ≤ CL * Z ^ ((933 / 2000 : ℝ) + 1 / 100000) +
            CErr * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) :=
          add_le_add (hLow Z hZ2) (hErr Z hZ)
        _ ≤ CL * Z ^ ((7 / 15 - 1 / 20000 : ℝ)) +
            CErr * Z ^ ((7 / 15 - 1 / 20000 : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hLowPower hCL.le)
            (mul_le_mul_of_nonneg_left hErrPower hCErr.le)
        _ = _ := by ring
    have hdiv : ‖principalSignal R η U HA HC Z‖ ≤
        ((CL + CErr) * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) /
          ‖principalConstant R sd W HA‖ :=
      (le_div_iff₀ hc0norm).2 (by simpa only [mul_comm] using hprod)
    calc
      ‖principalSignal R η U HA HC Z‖ ≤
          ((CL + CErr) * Z ^ ((7 / 15 - 1 / 20000 : ℝ))) /
            ‖principalConstant R sd W HA‖ := hdiv
      _ = _ := by ring
  exact ⟨hcont, hlarge, hsmall⟩
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
