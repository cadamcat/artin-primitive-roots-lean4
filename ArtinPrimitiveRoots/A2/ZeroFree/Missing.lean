import DedekindResidue.CompletedZeta.Existence
import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.ZeroFree.Density
import ArtinPrimitiveRoots.A2.Poisson.Missing
import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE_ASYM.FiniteContour
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE_ASYM.SignalEndpoints
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.A2.Proofs.A2_ROWS.HeightConvolution
import ArtinPrimitiveRoots.A2.Proofs.A2_ROWS.SimplePole
import ArtinPrimitiveRoots.A1.Coeff.IdealSummable
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict
import ArtinPrimitiveRoots.Hecke.Convexity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open NumberField IsDedekindDomain MeasureTheory ClassFieldTheory Filter Asymptotics
open scoped ComplexOrder Topology
open Set
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
  intro lξ rξ lw rw lz rz A0 hlξrξ hlwrw hlz hlzrz hA0
  obtain ⟨_, _, hM, hW, _⟩ := (po_weights_exist R sd).2 W
  obtain ⟨CM, hCM, hM⟩ := hM lz rz A0 hlz hlzrz hA0
  obtain ⟨CW, hCW, hW⟩ := hW lw rw A0 hlwrw hA0
  let B : ℝ := max |lξ| |rξ| + max |lz| |rz| + 1
  have hB : 0 ≤ B := by positivity
  have hξabs (ξ : ℂ) (hξl : lξ ≤ ξ.re) (hξr : ξ.re ≤ rξ) :
      |ξ.re| ≤ max |lξ| |rξ| := by
    by_cases hξ0 : 0 ≤ ξ.re
    · rw [abs_of_nonneg hξ0]
      exact (hξr.trans (le_trans (le_abs_self rξ) (le_max_right |lξ| |rξ|)))
    · have hξn : ξ.re ≤ 0 := le_of_not_ge hξ0
      rw [abs_of_nonpos hξn]
      have hlow : -|lξ| ≤ ξ.re := (neg_abs_le lξ).trans hξl
      nlinarith [le_abs_self lξ, le_max_left |lξ| |rξ|]
  have hzabs (z : ℂ) (hzl : lz ≤ z.re) (hzr : z.re ≤ rz) :
      |z.re| ≤ max |lz| |rz| := by
    by_cases hz0 : 0 ≤ z.re
    · rw [abs_of_nonneg hz0]
      exact (hzr.trans (le_trans (le_abs_self rz) (le_max_right |lz| |rz|)))
    · have hzn : z.re ≤ 0 := le_of_not_ge hz0
      rw [abs_of_nonpos hzn]
      have hlow : -|lz| ≤ z.re := (neg_abs_le lz).trans hzl
      nlinarith [le_abs_self lz, le_max_left |lz| |rz|]
  refine ⟨Real.exp (B ^ 2) * CM * CW, by positivity, ?_⟩
  intro ξ w z hξl hξr hwl hwr hzl hzr
  have hheight : |ξ.re + z.re - 1| ≤ B := by
    calc
      |ξ.re + z.re - 1| ≤ |ξ.re| + |z.re| + 1 := by
        calc
          |ξ.re + z.re - 1| = |(ξ.re + z.re) + (-1)| := by congr 1 <;> ring
          _ ≤ |ξ.re + z.re| + |-1| := abs_add_le _ _
          _ ≤ |ξ.re| + |z.re| + 1 := by
            have habs : |ξ.re + z.re| ≤ |ξ.re| + |z.re| := abs_add_le _ _
            rw [abs_neg, abs_one]
            linarith
      _ ≤ B := by dsimp [B]; gcongr <;> first | exact hξabs ξ hξl hξr | exact hzabs z hzl hzr
  have hsq : ((ξ + z - 1) ^ 2).re = (ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2 := by
    have hsq' (q : ℂ) : (q ^ 2).re = q.re ^ 2 - q.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    calc
      ((ξ + z - 1) ^ 2).re = (ξ + z - 1).re ^ 2 - (ξ + z - 1).im ^ 2 := hsq' _
      _ = (ξ.re + z.re - 1) ^ 2 - (ξ.im + z.im) ^ 2 := by simp <;> ring
  have hexp_eq : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ =
      Real.exp ((ξ.re + z.re - 1) ^ 2) * Real.exp (-((ξ.im + z.im) ^ 2)) := by
    rw [Complex.norm_exp, hsq, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  have hsqle : (ξ.re + z.re - 1) ^ 2 ≤ B ^ 2 := by
    have hnonneg : 0 ≤ B - |ξ.re + z.re - 1| := sub_nonneg.mpr hheight
    have hplus : 0 ≤ B + |ξ.re + z.re - 1| := by positivity
    nlinarith [mul_nonneg hnonneg hplus, sq_abs (ξ.re + z.re - 1)]
  have hexp : ‖Complex.exp ((ξ + z - 1) ^ 2)‖ ≤
      Real.exp (B ^ 2) * Real.exp (-((ξ.im + z.im) ^ 2)) := by
    rw [hexp_eq]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsqle) (Real.exp_pos _).le
  have hMbound : ‖weightM R sd W z‖ ≤ CM * (1 + |z.im|) ^ (-A0) := by
    have h := hM z.re z.im hzl hzr
    simpa only [Complex.re_add_im] using h
  have hWbound : ‖weightW1hat W w‖ ≤ CW * (1 + |w.im|) ^ (-A0) := by
    have h := hW w.re w.im hwl hwr
    simpa only [Complex.re_add_im] using h
  have hPz : 0 ≤ (1 + |z.im|) ^ (-A0) := by positivity
  have hPw : 0 ≤ (1 + |w.im|) ^ (-A0) := by positivity
  calc
    ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ =
        ‖Complex.exp ((ξ + z - 1) ^ 2)‖ * ‖weightM R sd W z‖ * ‖weightW1hat W w‖ := by
          simp [norm_mul, mul_assoc]
    _ ≤ (Real.exp (B ^ 2) * Real.exp (-((ξ.im + z.im) ^ 2))) *
          (CM * (1 + |z.im|) ^ (-A0)) * (CW * (1 + |w.im|) ^ (-A0)) := by
          gcongr
    _ = (Real.exp (B ^ 2) * CM * CW) * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by ring
/-- zf:height-decay, 06:389-411. Gaussian convolution preserves arbitrary polynomial decay. -/
theorem zf_height_convolution : ∀ A1 : ℝ, 0 < A1 → ∃ A0 C : ℝ, 1 < A0 ∧ 0 < C ∧ ∀ T : ℝ,
  (∫ v : ℝ, Real.exp (-((T + v) ^ 2)) * (1 + |v|) ^ (-A0)) ≤ C * (1 + |T|) ^ (-A1) := by
  exact ArtinPrimitiveRoots.Proofs.A2Rows.zf_height_convolution_proof
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

/-- Finite-order Hecke characters take unit-modulus values on ideles. -/
private theorem rows_char_unitary (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
    ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hp⟩ := (isOfFinOrder_iff_pow_eq_one.mp hχ)
  intro x
  have hx : (χ x : ℂˣ) ^ n = 1 := by
    have h := congrArg (fun f : HeckeChar F => f x) hp
    simpa using h
  have hx' : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    exact congrArg (fun z : ℂˣ => (z : ℂ)) hx
  have hfin : IsOfFinOrder ((χ x : ℂˣ) : ℂ) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, hx'⟩
  exact hfin.norm_eq_one

private theorem rows_multiset_prod_norm_le_one {α : Type} (s : Multiset α)
    (f : α → ℂ) (hf : ∀ x, x ∈ s → ‖f x‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hf a (by simp)) (norm_nonneg _) <| ih fun x hx =>
        hf x (Multiset.mem_cons_of_mem hx)

private theorem rows_primeValue_norm_le_one (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (v : FinPlace F) : ‖χ.primeValue v‖ ≤ 1 := by
  classical
  unfold HeckeChar.primeValue
  split_ifs with hv
  · have h := rows_char_unitary χ hχ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
      (toLoc v (Units.mk0 (unif v) (unif_ne_zero v))))
    simpa [HeckeChar.loc] using le_of_eq h
  · simp

private theorem rows_idealValue_norm_le_one (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (I : Ideal (𝓞 F)) : ‖χ.idealValue I‖ ≤ 1 := by
  unfold HeckeChar.idealValue
  apply rows_multiset_prod_norm_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using rows_primeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
  · simp [h]

private def rows_absNorm_majorant : ℝ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-(12 / 5 : ℝ))

private theorem rows_absNorm_majorant_summable :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-(12 / 5 : ℝ))) := by
  have h := ArtinPrimitiveRoots.A1.Coeff.summable_absNorm_rpow (F := F)
    (12 / 5 : ℝ) (by norm_num)
  exact h.comp_injective Subtype.val_injective

private theorem rows_absNorm_majorant_nonneg : 0 ≤ rows_absNorm_majorant (F := F) := by
  unfold rows_absNorm_majorant
  exact tsum_nonneg fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem rows_absNorm_nat_pos (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
    0 < Ideal.absNorm I.1 := by
  have hI0 : I.1 ≠ 0 := by
    simpa [Ideal.zero_eq_bot] using I.2
  exact Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩

private theorem rows_kummer_finiteOrder (hEuler : EulerHypotheses R η) (u : U.U) :
    IsOfFinOrder (U.kummer u) := by
  have hProd : IsOfFinOrder (η⁻¹ * U.omega u) :=
    IsOfFinOrder.mul (IsOfFinOrder.inv hEuler.1) (U.omega_finiteOrder u)
  have hInv : IsOfFinOrder ((η⁻¹ * U.omega u)⁻¹) := IsOfFinOrder.inv hProd
  have heq : U.kummer u = (η⁻¹ * U.omega u)⁻¹ := by
    rw [U.omega_induces_twist u]
    have hinner : η⁻¹ * (η * (U.kummer u)⁻¹) = (U.kummer u)⁻¹ := by
      simp [mul_assoc]
    rw [hinner]
    exact (inv_inv (U.kummer u)).symm
  rw [heq]
  exact hInv

private theorem rows_exists_primitive_conductor (χ : HeckeChar F)
    (hmod : ∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ χ.ConductorDvd m) :
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor χ f := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : Ideal (𝓞 F), f ≠ ⊥ ∧ χ.ConductorDvd f ∧ Ideal.absNorm f = n
  obtain ⟨m, hm0, hmc⟩ := hmod
  have hP : ∃ n, P n := ⟨Ideal.absNorm m, m, hm0, hmc, rfl⟩
  obtain ⟨f, hf0, hfc, hfn⟩ := Nat.find_spec hP
  refine ⟨f, hf0, hfc, ?_⟩
  intro g hg0 hgc
  calc
    Ideal.absNorm f = Nat.find hP := hfn
    _ ≤ Ideal.absNorm g := Nat.find_min' hP ⟨g, hg0, hgc, rfl⟩

private theorem rows_eta_primitive_conductor (U : FrequencyData S D η)
    (hEuler : EulerHypotheses R η) :
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor η f := by
  obtain ⟨f, hf⟩ := FrequencyData.omega_primitive U U.one
  have honeInv : (1 : HeckeChar F)⁻¹ = 1 := by
    ext x
    change (((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ) = (1 : ℂ)
    simp
  have hmulOne : η * (1 : HeckeChar F) = η := by
    ext x
    change (((η x : ℂˣ) * (1 : ℂˣ) : ℂˣ) : ℂ) = ((η x : ℂˣ) : ℂ)
    simp
  have hEq : U.omega U.one = η := by
    rw [FrequencyData.omega_induces_twist U U.one, FrequencyData.kummer_one U, honeInv]
    exact hmulOne
  refine ⟨f, ?_⟩
  rw [← hEq]
  exact hf

private theorem rows_complete_L_norm_bound (HA : HeckeAnalysis F) (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 12 / 5 ≤ s.re) :
    ‖HA.L χ s‖ ≤ rows_absNorm_majorant (F := F) := by
  classical
  let f : {I : Ideal (𝓞 F) // I ≠ ⊥} → ℂ := fun I =>
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
  have hNpos (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : 0 < (Ideal.absNorm I.1 : ℝ) := by
    exact_mod_cast rows_absNorm_nat_pos I
  have hNone (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      1 ≤ (Ideal.absNorm I.1 : ℝ) := by
    have hn : 1 ≤ Ideal.absNorm I.1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (rows_absNorm_nat_pos I))
    exact_mod_cast hn
  have hbound (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :
      ‖f I‖ ≤ (Ideal.absNorm I.1 : ℝ) ^ (-(12 / 5 : ℝ)) := by
    have hpow : ‖((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm I.1 : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast rows_absNorm_nat_pos I)]
      rfl
    have hpowle : (Ideal.absNorm I.1 : ℝ) ^ (-s.re) ≤
        (Ideal.absNorm I.1 : ℝ) ^ (-(12 / 5 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (hNone I) (by linarith)
    rw [norm_mul, hpow]
    calc
      ‖χ.idealValue I.1‖ * (Ideal.absNorm I.1 : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm I.1 : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (rows_idealValue_norm_le_one χ hχ I.1)
          (Real.rpow_nonneg (hNpos I).le _)
      _ ≤ (Ideal.absNorm I.1 : ℝ) ^ (-(12 / 5 : ℝ)) := by
        simpa only [one_mul] using hpowle
  have hnorm : Summable (fun I => ‖f I‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound rows_absNorm_majorant_summable
  have hseries : HA.L χ s = ∑' I, f I := by
    have hs' : 1 < s.re := by linarith
    change HA.1.1 χ s = heckeLSeries χ s
    rw [HA.2.1 χ s hs']
  calc
    ‖HA.L χ s‖ = ‖∑' I, f I‖ := by rw [hseries]
    _ ≤ ∑' I, ‖f I‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ rows_absNorm_majorant (F := F) := by
      unfold rows_absNorm_majorant
      exact hnorm.tsum_le_tsum hbound rows_absNorm_majorant_summable

private theorem rows_LS_norm_bound (HA : HeckeAnalysis F) (S : SData F CE condη)
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 12 / 5 ≤ s.re) :
    ‖HA.LS S χ s‖ ≤ rows_absNorm_majorant (F := F) * 2 ^ S.Sf.card := by
  have hfactor (v : FinPlace F) :
      ‖1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 2 := by
    have hn : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hnreal : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    have hpow : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn)]
      rfl
    have hpowle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnreal (by linarith)
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖χ.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ‖χ.primeValue v‖ *
          ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by simp [norm_mul]
      _ ≤ 1 + 1 * 1 := by
        have hχv := rows_primeValue_norm_le_one χ hχ v
        have hpow' : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [hpow]
          exact hpowle
        nlinarith [norm_nonneg (χ.primeValue v), norm_nonneg
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))]
      _ = 2 := by norm_num
  have hprodNorm : ∀ t : Finset (FinPlace F),
      ‖∏ v ∈ t, (1 - χ.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ =
        ∏ v ∈ t, ‖1 - χ.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert v t hv ih => simp [Finset.prod_insert, hv, norm_mul, ih]
  have hprod :
      ‖∏ v ∈ S.Sf, (1 - χ.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ ≤ 2 ^ S.Sf.card := by
    rw [hprodNorm]
    calc
      _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro v hv
          exact norm_nonneg _
        · intro v hv
          exact hfactor v
      _ = 2 ^ S.Sf.card := by simp
  change ‖HA.L χ s * ∏ v ∈ S.Sf,
    (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (rows_complete_L_norm_bound HA χ hχ hs) hprod
    (norm_nonneg _) (rows_absNorm_majorant_nonneg (F := F))

private theorem rows_heckeLSeries_eq_ray (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor χ f) :
    ∃ m : RayClassModulus F, ∃ ψ : RayClassGroup m →* ℂˣ,
      ∀ s : ℂ, 1 < s.re → heckeLSeries χ s = Hecke.LSeriesRay ψ s := by
  obtain ⟨m, ψ, hm, _, hval⟩ :=
    Dictionary.exists_rayClass_of_heckeChar χ hχ f hf.1 hf.2.1
  have hcop (v : HeightOneSpectrum (𝓞 F))
      (hv : v ∉ m.finitePart.support) : Hecke.IsCoprimeTo m v.asIdeal := by
    refine ⟨v.ne_bot, ?_⟩
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    simpa [Hecke.idealUnit] using
      FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv)
  have hunr (v : HeightOneSpectrum (𝓞 F))
      (hv : v ∉ m.finitePart.support) : χ.UnramifiedAt v := by
    refine qsa_unramifiedAt_of_conductorDvd χ f hf.2.1 v ?_
    rw [← hm, Dictionary.idealExp_modulusIdeal]
    exact Finsupp.notMem_support_iff.mp hv
  have hχoff : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v = Hecke.charValue ψ v.asIdeal := by
    intro v hv
    exact ⟨hunr v hv, (hval v hv).symm⟩
  have hideal : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      χ.idealValue I = Hecke.charValue ψ I := by
    intro I hI
    by_cases hc : Hecke.IsCoprimeTo m I
    · exact Dictionary.idealValue_eq_charValue ψ χ hχoff I hc
    · rw [Hecke.charValue, dif_neg hc]
      have hex : ∃ v : HeightOneSpectrum (𝓞 F),
          v ∈ m.finitePart.support ∧ v.asIdeal ∣ I := by
        by_contra hnot
        push_neg at hnot
        apply hc
        refine ⟨hI, ?_⟩
        intro v hv
        simp only [Hecke.idealUnit, Units.val_mk0]
        rw [FractionalIdeal.count_coe F v hI]
        have hcount := (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr
          (hnot v hv)
        push_neg at hcount
        exact_mod_cast hcount
      obtain ⟨v, hv, hvI⟩ := hex
      have hvf : v.asIdeal ∣ f := by
        rw [← hm]
        unfold Dictionary.modulusIdeal
        have hpos : m.finitePart v ≠ 0 := Finsupp.mem_support_iff.mp hv
        exact (dvd_pow_self v.asIdeal hpos).trans <| by
          simpa only [Finsupp.prod] using
            (Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ m.finitePart w) hv)
      exact qs_idealValue_eq_zero_of_conductor_M0
        χ f hf v.asIdeal I v.isPrime v.ne_bot hvf hI hvI
  refine ⟨m, ψ, ?_⟩
  intro s hs
  exact qsa_heckeLSeries_eq_LSeriesRay χ ψ hideal hs

private theorem rows_omitted_factor_inverse_bound (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) (v : FinPlace F) :
    (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0) ∧
      ‖(1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ 2 := by
  have hnNat : 2 ≤ Ideal.absNorm v.asIdeal := by
    have hn := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  have hn0 : 0 < Ideal.absNorm v.asIdeal := by omega
  have hnreal : 2 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hnNat
  have hpow : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn0)]
    rfl
  have hpowle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have hbase : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by linarith
    have hexp : -s.re ≤ (-1 : ℝ) := by linarith
    calc
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ = 1 / (Ideal.absNorm v.asIdeal : ℝ) := by
        rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num,
          Real.rpow_neg (by positivity : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ)),
          Real.rpow_one]
        simp [one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hnreal
  let α : ℂ := χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)
  have hα : ‖α‖ ≤ 1 / 2 := by
    dsimp [α]
    rw [norm_mul, hpow]
    calc
      _ ≤ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (rows_primeValue_norm_le_one χ hχ v)
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_left hpowle (by norm_num)
      _ = 1 / 2 := by ring
  have htriangle : (1 : ℝ) ≤ ‖(1 : ℂ) - α‖ + ‖α‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖((1 : ℂ) - α) + α‖ := by congr 1 <;> ring
      _ ≤ ‖(1 : ℂ) - α‖ + ‖α‖ := norm_add_le _ _
  have hlower : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - α‖ := by linarith
  constructor
  · intro hzero
    have hnorm : ‖(1 : ℂ) - α‖ = 0 := by rw [hzero]; simp
    rw [hnorm] at hlower
    norm_num at hlower
  · have hpos : 0 < ‖(1 : ℂ) - α‖ := by linarith
    change ‖((1 : ℂ) - α)⁻¹‖ ≤ 2
    rw [norm_inv]
    calc
      _ ≤ ((1 / 2 : ℝ))⁻¹ :=
        (inv_le_inv₀ hpos (by norm_num : 0 < (1 / 2 : ℝ))).2 hlower
      _ = 2 := by norm_num

private theorem rows_LS_inverse_bound (HA : HeckeAnalysis F) (S : SData F CE condη)
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (f : Ideal (𝓞 F))
    (hf : IsPrimitiveConductor χ f) {s : ℂ} (hs : 1 < s.re) :
    HA.LS S χ s ≠ 0 ∧
      ‖(HA.LS S χ s)⁻¹‖ ≤ (NumberField.dedekindZeta F s.re).re * 2 ^ S.Sf.card := by
  obtain ⟨m, ψ, hseries⟩ := rows_heckeLSeries_eq_ray χ hχ f hf
  have hRay := Hecke.norm_LSeriesRay_le ψ hs
  have hcompleteEq : HA.L χ s = Hecke.LSeriesRay ψ s := by
    calc
      HA.L χ s = heckeLSeries χ s := HA.2.1 χ s hs
      _ = Hecke.LSeriesRay ψ s := hseries s hs
  have hcompleteNe : HA.L χ s ≠ 0 := by
    rw [hcompleteEq]
    exact hRay.2.1
  let P : ℂ := ∏ v ∈ S.Sf,
    (1 - χ.primeValue v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
  have hPne : P ≠ 0 := by
    dsimp [P]
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact (rows_omitted_factor_inverse_bound χ hχ hs v).1
  have hPInv : ‖P⁻¹‖ ≤ 2 ^ S.Sf.card := by
    dsimp [P]
    rw [← Finset.prod_inv_distrib]
    calc
      _ ≤ ∏ v ∈ S.Sf, ‖(1 - χ.primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro v hv
          exact norm_nonneg _
        · intro v hv
          exact (rows_omitted_factor_inverse_bound χ hχ hs v).2
      _ = 2 ^ S.Sf.card := by simp
  have hLS_eq : HA.LS S χ s = HA.L χ s * P := rfl
  constructor
  · rw [hLS_eq]
    exact mul_ne_zero hcompleteNe hPne
  · rw [hLS_eq, mul_inv, norm_mul]
    have hcompleteInv : ‖(HA.L χ s)⁻¹‖ ≤ (NumberField.dedekindZeta F s.re).re := by
      rw [hcompleteEq]
      exact hRay.2.2
    have hzetaNonneg : 0 ≤ (NumberField.dedekindZeta F s.re).re :=
      le_trans (norm_nonneg _) hcompleteInv
    exact mul_le_mul hcompleteInv hPInv (norm_nonneg _) hzetaNonneg

private theorem rows_mellinWeight_norm (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) :
    ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ =
      Z ^ Estar ξ.re w.re z.re *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ := by
  have hXpos : 0 < Z ^ a := Real.rpow_pos_of_pos hZ a
  have hYpos : 0 < Z ^ b := Real.rpow_pos_of_pos hZ b
  have hXnorm : ‖((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)‖ =
      (Z ^ a) ^ (1 / 2 - z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    simp
  have hZnorm : ‖(Z : ℂ) ^ (ξ + z - 1)‖ = Z ^ (ξ.re + z.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    simp
  have hYnorm : ‖((Z ^ b : ℝ) : ℂ) ^ (w - 1)‖ =
      (Z ^ b) ^ (w.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp
  have hExponent :
      (Z ^ a) ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) *
        (Z ^ b) ^ (w.re - 1) = Z ^ Estar ξ.re w.re z.re := by
    calc
      (Z ^ a) ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) *
          (Z ^ b) ^ (w.re - 1) =
          Z ^ (a * (1 / 2 - z.re)) * Z ^ (ξ.re + z.re - 1) *
            Z ^ (b * (w.re - 1)) := by
              rw [Real.rpow_mul hZ.le, Real.rpow_mul hZ.le]
      _ = Z ^ (a * (1 / 2 - z.re) + (ξ.re + z.re - 1)) *
            Z ^ (b * (w.re - 1)) := by rw [← Real.rpow_add hZ]
      _ = Z ^ (a * (1 / 2 - z.re) + (ξ.re + z.re - 1) + b * (w.re - 1)) :=
            by rw [← Real.rpow_add hZ]
      _ = Z ^ Estar ξ.re w.re z.re := by
        congr 1
        simp [Estar, a, b, h0]
        ring_nf
  calc
    ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z‖ =
        ((Z ^ a) ^ (1 / 2 - z.re) * Z ^ (ξ.re + z.re - 1) *
          (Z ^ b) ^ (w.re - 1)) *
          ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ := by
            unfold mellinWeight
            simp only [norm_mul, hXnorm, hZnorm, hYnorm]
            ring
    _ = Z ^ Estar ξ.re w.re z.re *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ := by
          rw [hExponent]

private theorem rows_rowKernel_norm_eq (Z : ℝ) (hZ : 0 < Z) (u : U.U)
    (ξ w z : ℂ) :
    ‖rowKernel R sd W η U HA HC u Z ξ w z‖ =
      Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ *
        ‖HA.LS S 1 (6 * z)‖ * ‖HA.LS S (U.kummer u) w‖ *
        ‖HC.H u ![ξ, w, z]‖ * ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ := by
  unfold rowKernel
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  rw [rows_mellinWeight_norm R sd W Z hZ ξ w z,
    Complex.norm_cpow_eq_rpow_re_of_pos (U.q_pos u)]
  simp only [Complex.neg_re]
  simp only [norm_mul]
  ring

private theorem rows_integrable_poly_decay {p : ℝ} (hp : 1 < p) :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-p)) := by
  let g : ℝ → ℝ := fun t => (1 + |t|) ^ (-p)
  have hposBase : IntegrableOn (fun t : ℝ => (1 + t) ^ (-p)) (Set.Ioi 0) := by
    simpa [add_comm] using
      (integrableOn_add_rpow_Ioi_of_lt (a := -p) (c := 0) (m := 1)
        (by linarith) (by norm_num))
  have hpos : IntegrableOn g (Set.Ioi 0) := by
    apply hposBase.congr_fun
    · intro t ht
      have htpos : 0 < t := Set.mem_Ioi.mp ht
      change (1 + t) ^ (-p) = (1 + |t|) ^ (-p)
      rw [abs_of_pos htpos]
    · exact measurableSet_Ioi
  have hneg : IntegrableOn g (Set.Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa [g, Function.comp_def] using hpos
  have hpos0 : IntegrableOn g (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hpos
  have hall : Integrable g := by
    rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union]
    exact ⟨hneg, hpos0⟩
  simpa [g] using hall

private theorem rows_integrable_shifted_gaussian_poly (p T : ℝ) (hp : 1 < p) :
    Integrable (fun t : ℝ => Real.exp (-((T + t) ^ 2)) * (1 + |t|) ^ (-p)) := by
  have hgauss0 : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ)))
  have hgauss : Integrable (fun t : ℝ => Real.exp (-((T + t) ^ 2))) := by
    have h := (measurePreserving_add_left (volume : Measure ℝ) T).integrable_comp_of_integrable hgauss0
    simpa [Function.comp_def] using h
  refine Integrable.mono' hgauss ?_ ?_
  · fun_prop
  · filter_upwards with t
    have hpoly : (1 + |t|) ^ (-p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg t])
        (by linarith [hp])
    have hleft0 : 0 ≤ Real.exp (-((T + t) ^ 2)) * (1 + |t|) ^ (-p) := by
      positivity
    have hpoint : Real.exp (-((T + t) ^ 2)) * (1 + |t|) ^ (-p) ≤
        Real.exp (-((T + t) ^ 2)) := by
      calc
        _ ≤ Real.exp (-((T + t) ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
        _ = _ := by ring
    have hright0 : 0 ≤ Real.exp (-((T + t) ^ 2)) := (Real.exp_pos _).le
    have hnormLeft :
        ‖Real.exp (-((T + t) ^ 2)) * (1 + |t|) ^ (-p)‖ =
          Real.exp (-((T + t) ^ 2)) * (1 + |t|) ^ (-p) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hleft0]
    have hnormRight : ‖Real.exp (-((T + t) ^ 2))‖ =
        Real.exp (-((T + t) ^ 2)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hright0]
    simpa only [hnormLeft, hnormRight] using hpoint

private theorem rows_vertical_norm_le_integral (σ : ℝ) (f : ℂ → ℂ) (g : ℝ → ℝ)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hbound : ∀ t : ℝ, ‖f (σ + t * Complex.I)‖ ≤ g t) :
    ‖vertical σ f‖ ≤ ∫ t : ℝ, g t := by
  unfold vertical
  have hint := norm_integral_le_of_norm_le hg (ae_of_all _ hbound)
  have hden : 1 ≤ ‖(2 * Real.pi : ℂ)‖ := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hcoef : ‖(1 / (2 * Real.pi) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
    simpa using h
  calc
    ‖(1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (σ + t * Complex.I)‖ =
        ‖(1 / (2 * Real.pi) : ℂ)‖ *
          ‖∫ t : ℝ, f (σ + t * Complex.I)‖ := norm_mul _ _
    _ ≤ 1 * ∫ t : ℝ, g t := mul_le_mul hcoef hint (norm_nonneg _) (by norm_num)
    _ = ∫ t : ℝ, g t := one_mul _

private theorem rows_LS_trivial_differentiableOn (HA : HeckeAnalysis F)
    (S : SData F CE condη) :
    DifferentiableOn ℂ (HA.LS S (1 : HeckeChar F)) {s | 1 < s.re} := by
  have hcomplete : DifferentiableOn ℂ (HA.L (1 : HeckeChar F)) {s | 1 < s.re} := by
    apply (HA.2.2.2.1).mono
    intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    intro heq
    have hRe := congrArg Complex.re heq
    simp at hRe
    linarith
  have hfactor : Differentiable ℂ (fun s : ℂ =>
      ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    refine Differentiable.fun_finsetProd ?_
    intro v hv
    have hn0 : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hn : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn0)
    have hpow : Differentiable ℂ (fun s : ℂ =>
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro s
      exact (differentiableAt_id.neg).const_cpow (Or.inl hn)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const ((1 : HeckeChar F).primeValue v)).mul hpow)
  change DifferentiableOn ℂ (fun s => HA.L (1 : HeckeChar F) s *
    ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) _
  exact hcomplete.mul hfactor.differentiableOn

private theorem rows_rowKernel_differentiableOn_z (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 0 < Z) (u : U.U) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    DifferentiableOn ℂ (fun z => rowKernel R sd W η U HA HC u Z ξ w z)
      {z | 2 ≤ z.re ∧ z.re ≤ 350000} := by
  let strip : Set ℂ := {z | 2 ≤ z.re ∧ z.re ≤ 350000}
  obtain ⟨hMdiff, _, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hMstrip : DifferentiableOn ℂ (weightM R sd W) strip := by
    apply hMdiff.mono
    intro z hz
    exact lt_of_lt_of_le (by norm_num) hz.1
  have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ a))
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ b))
  have hXexp : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) :=
    (differentiable_const _).sub differentiable_id
  have hX : Differentiable ℂ (fun z : ℂ => ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := by
    intro z
    exact (hXexp z).const_cpow (Or.inl hXbase)
  have hZexp : Differentiable ℂ (fun z : ℂ => ξ + z - 1) := by fun_prop
  have hZpow : Differentiable ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) := by
    intro z
    exact (hZexp z).const_cpow (Or.inl hZbase)
  have hY : Differentiable ℂ (fun z : ℂ => ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) :=
    differentiable_const _
  have hGauss : Differentiable ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) := by
    fun_prop
  have hW : Differentiable ℂ (fun z : ℂ => weightW1hat W w) := differentiable_const _
  have hMellin : DifferentiableOn ℂ
      (fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) strip := by
    unfold mellinWeight
    exact (((((hX.differentiableOn.mul hZpow.differentiableOn).mul
      hY.differentiableOn).mul hGauss.differentiableOn).mul hMstrip).mul
      hW.differentiableOn)
  have hqbase : (U.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (U.q_pos u))
  have hqpow : Differentiable ℂ (fun z : ℂ => (U.q u : ℂ) ^ (-z)) := by
    intro z
    exact (differentiable_id.neg z).const_cpow (Or.inl hqbase)
  have hLz : DifferentiableOn ℂ (fun z : ℂ => HA.LS S 1 (6 * z)) strip := by
    apply (rows_LS_trivial_differentiableOn HA S).comp
      ((show Differentiable ℂ (fun z : ℂ => 6 * z) by fun_prop).differentiableOn)
    intro z hz
    change 1 < (6 * z).re
    have hre : (6 * z).re = 6 * z.re := by simp
    rw [hre]
    nlinarith [hz.1]
  have hHCprod := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun z => ![ξ, w, z]
  have hpmap : Differentiable ℂ pmap := by
    intro z
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hMaps : MapsTo pmap strip {p | eulerNeighborhood p} := by
    intro z hz
    left
    change (998 / 1000 - 1 / 100000 < ξ.re ∧
      3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
    refine ⟨?_, ?_, ?_⟩
    · rw [hξ]
      norm_num
    · rw [hw]
      norm_num
    · linarith [hz.1]
  have hHC : DifferentiableOn ℂ (fun z => HC.H u ![ξ, w, z]) strip := by
    have h := (hHCprod.2.1 u).comp hpmap.differentiableOn hMaps
    exact h
  have hK : DifferentiableOn ℂ (fun z : ℂ => HA.LS S (U.kummer u) w) strip := by
    fun_prop
  have hInv : DifferentiableOn ℂ
      (fun z : ℂ => (HA.LS S (rowTwist η U u) ξ)⁻¹) strip := by fun_prop
  change DifferentiableOn ℂ (fun z =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z] *
          (HA.LS S (rowTwist η U u) ξ)⁻¹) strip
  exact (((((hMellin.mul hqpow.differentiableOn).mul hLz).mul hK).mul hHC).mul hInv)

private theorem rows_far_kernel_control (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A0 C0 Cconv : ℝ, 1 < A0 ∧ 0 < C0 ∧ 0 < Cconv ∧
      (∀ T : ℝ, ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) *
        (1 + |v|) ^ (-A0) ≤ Cconv * (1 + |T|) ^ (-2 : ℝ)) ∧
      ∀ Z, 2 ≤ Z → ∀ u ξ w z,
      ξ.re = 4 → w.re = 4 → 2 ≤ z.re → z.re ≤ 350000 →
      ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
        C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) * (U.q u) ^ ε *
          Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
  obtain ⟨A0, Cconv, hA0, hCconv, hconv⟩ :=
    zf_height_convolution (2 : ℝ) (by norm_num)
  obtain ⟨Cht, hCht, hheight⟩ := zf_height_decay R sd W
    4 4 4 4 2 350000 A0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by linarith)
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  obtain ⟨CH, hCH, hCHbound⟩ := hHP.2.2.2 ε hε
  let KLS : ℝ := rows_absNorm_majorant (F := F) * 2 ^ S.Sf.card
  let Cinv : ℝ := (NumberField.dedekindZeta F 4).re * 2 ^ S.Sf.card
  let Cbase : ℝ := Cht * KLS * KLS * CH * Cinv
  let C0 : ℝ := Cbase + 1
  have hKLS : 0 ≤ KLS := by
    dsimp [KLS]
    exact mul_nonneg (rows_absNorm_majorant_nonneg (F := F)) (by positivity)
  have hCinv : 0 ≤ Cinv := by
    have hu1 : IsOfFinOrder (U.omega U.one) := U.omega_finiteOrder U.one
    obtain ⟨f, hf⟩ := U.omega_primitive U.one
    have htw : rowTwist η U U.one = U.omega U.one := by
      simpa [rowTwist] using (U.omega_induces_twist U.one).symm
    have hfin : IsOfFinOrder (rowTwist η U U.one) := by rw [htw]; exact hu1
    have hprim : IsPrimitiveConductor (rowTwist η U U.one) f := by rw [htw]; exact hf
    have hinv := (rows_LS_inverse_bound HA S (rowTwist η U U.one) hfin f hprim
      (s := (4 : ℂ)) (by norm_num)).2
    have hnonneg : 0 ≤ (NumberField.dedekindZeta F 4).re := by
      have hnorm : 0 ≤ ‖(HA.LS S (rowTwist η U U.one) (4 : ℂ))⁻¹‖ := norm_nonneg _
      have hval : ‖(HA.LS S (rowTwist η U U.one) (4 : ℂ))⁻¹‖ ≤
          (NumberField.dedekindZeta F 4).re * 2 ^ S.Sf.card := by simpa using hinv
      have hpow : 0 < (2 : ℝ) ^ S.Sf.card := by positivity
      by_contra hnot
      have hzeta : (NumberField.dedekindZeta F 4).re < 0 := lt_of_not_ge hnot
      have hprod : (NumberField.dedekindZeta F 4).re * 2 ^ S.Sf.card < 0 :=
        mul_neg_of_neg_of_pos hzeta hpow
      linarith
    dsimp [Cinv]
    positivity
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith
  refine ⟨A0, C0, Cconv, hA0, hC0, hCconv, hconv, ?_⟩
  intro Z hZ u ξ w z hξ hw hzlo hzhi
  obtain ⟨f, hf⟩ := U.omega_primitive u
  have htw : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have htwFin : IsOfFinOrder (rowTwist η U u) := by rw [htw]; exact U.omega_finiteOrder u
  have htwPrim : IsPrimitiveConductor (rowTwist η U u) f := by rw [htw]; exact hf
  obtain ⟨_, hrecip⟩ := rows_LS_inverse_bound HA S (rowTwist η U u) htwFin f htwPrim
    (by rw [hξ]; norm_num)
  have hrecip' : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ Cinv := by
    simpa [Cinv, hξ] using hrecip
  have hKummer : IsOfFinOrder (U.kummer u) := rows_kummer_finiteOrder R η U hEuler u
  have hKumL : ‖HA.LS S (U.kummer u) w‖ ≤ KLS :=
    rows_LS_norm_bound HA S (U.kummer u) hKummer (by rw [hw]; norm_num)
  have hOne : IsOfFinOrder (1 : HeckeChar F) := by simp
  have hZetaL : ‖HA.LS S 1 (6 * z)‖ ≤ KLS :=
    rows_LS_norm_bound HA S 1 hOne (by
      have hmul : (6 * z).re = 6 * z.re := by simp
      rw [hmul]
      nlinarith [hzlo])
  have hp : eulerNeighborhood ![ξ, w, z] := by
    left
    change (998 / 1000 - 1 / 100000 < ξ.re ∧
      3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
    refine ⟨by rw [hξ]; norm_num, by rw [hw]; norm_num, by linarith [hzlo]⟩
  have hHCval : ‖HC.H u ![ξ, w, z]‖ ≤ CH * (U.q u) ^ ε := hCHbound u ![ξ, w, z] hp
  have hHt := hheight ξ w z (by simpa [hξ]) (by simpa [hξ])
    (by simpa [hw]) (by simpa [hw]) hzlo hzhi
  have hqpos := U.q_pos u
  have hqpow : 0 ≤ (U.q u) ^ (-z.re) := Real.rpow_nonneg hqpos.le _
  have hqε : 0 ≤ (U.q u) ^ ε := Real.rpow_nonneg hqpos.le _
  have hZpos : 0 < Z := by linarith
  have hZpow : 0 ≤ Z ^ Estar ξ.re w.re z.re := Real.rpow_nonneg hZpos.le _
  have hGauss : 0 ≤ Real.exp (-((ξ.im + z.im) ^ 2)) := (Real.exp_pos _).le
  have hPz : 0 ≤ (1 + |z.im|) ^ (-A0) := by positivity
  have hPw : 0 ≤ (1 + |w.im|) ^ (-A0) := by positivity
  rw [rows_rowKernel_norm_eq R sd W η U HA HC Z hZpos u ξ w z]
  calc
    _ ≤ Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
        (Cht * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) *
        KLS * KLS * (CH * (U.q u) ^ ε) * Cinv := by
          gcongr
    _ = Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
        (U.q u) ^ ε * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
          dsimp [Cbase]
          ring
    _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
        (U.q u) ^ ε * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
          have hRest : 0 ≤ Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
              (U.q u) ^ ε * Real.exp (-((ξ.im + z.im) ^ 2)) *
                (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by positivity
          have hCbasele : Cbase ≤ C0 := by dsimp [C0]; linarith
          calc
            _ = Cbase * (Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
                (U.q u) ^ ε * Real.exp (-((ξ.im + z.im) ^ 2)) *
                  (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) := by ring
            _ ≤ C0 * (Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
                (U.q u) ^ ε * Real.exp (-((ξ.im + z.im) ^ 2)) *
                  (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) :=
              mul_le_mul_of_nonneg_right hCbasele hRest
            _ = _ := by ring

private theorem rows_far_z_shift (hEuler : EulerHypotheses R η) (ε : ℝ) (hε : 0 < ε)
    (Z : ℝ) (hZ : 2 ≤ Z) (rows : Finset U.U) (ξ w : ℂ)
    (hξ : ξ.re = 4) (hw : w.re = 4) :
    vertical 2 (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) =
      vertical 350000 (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) := by
  let strip : Set ℂ := {z | 2 ≤ z.re ∧ z.re ≤ 350000}
  let G : ℂ → ℂ := fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z
  let trans : ℂ → ℂ := fun z => z - ξ.im * Complex.I
  let Fcont : ℂ → ℂ := fun z => G (trans z)
  obtain ⟨A0, C0, _, hA0, hC0, _, _, hcontrol⟩ :=
    rows_far_kernel_control R sd W η U HA HC hEuler ε hε
  let Cshift : ℝ := C0 * Z ^ Estar 4 4 350000 *
    ∑ u ∈ rows, (U.q u) ^ ε
  have hGdiff : DifferentiableOn ℂ G strip := by
    change DifferentiableOn ℂ
      (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) strip
    apply DifferentiableOn.fun_sum
    intro u hu
    exact rows_rowKernel_differentiableOn_z R sd W η U HA HC hEuler Z
      (by positivity) u ξ w hξ hw
  have hTransDiff : Differentiable ℂ trans := by fun_prop
  have hTransOn : DifferentiableOn ℂ trans strip := hTransDiff.differentiableOn
  have hMaps : MapsTo trans strip strip := by
    intro z hz
    constructor
    · have hreal : (trans z).re = z.re := by simp [trans]
      rw [hreal]
      exact hz.1
    · have hreal : (trans z).re = z.re := by simp [trans]
      rw [hreal]
      exact hz.2
  have hFdiff : DifferentiableOn ℂ Fcont strip := by
    have h := hGdiff.comp hTransOn hMaps
    simpa only [Fcont, Function.comp_def] using h
  have hFbound : ∀ x ∈ Set.Icc (2 : ℝ) 350000, ∀ y : ℝ,
      ‖Fcont ((x : ℂ) + y * Complex.I)‖ ≤ Cshift * Real.exp (-y ^ 2) := by
    intro x hx y
    have hxlo : 2 ≤ x := hx.1
    have hxhi : x ≤ 350000 := hx.2
    let z : ℂ := (x : ℂ) + (y - ξ.im) * Complex.I
    have htrans : trans ((x : ℂ) + y * Complex.I) = z := by
      dsimp [trans, z]
      apply Complex.ext
      · simp
      · simp
    have hzre : z.re = x := by simp [z]
    have hzim : z.im = y - ξ.im := by simp [z]
    have hZexp : Estar ξ.re w.re z.re ≤ Estar 4 4 350000 := by
      rw [hξ, hw, hzre]
      norm_num [Estar, a, b, h0]
      nlinarith [hxhi]
    have hZrpow : Z ^ Estar ξ.re w.re z.re ≤ Z ^ Estar 4 4 350000 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hZexp
    have hpolyZ : (1 + |z.im|) ^ (-A0) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [abs_nonneg z.im]) (by linarith [hA0])
    have hpolyW : (1 + |w.im|) ^ (-A0) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [abs_nonneg w.im]) (by linarith [hA0])
    have hgauss : Real.exp (-((ξ.im + z.im) ^ 2)) = Real.exp (-y ^ 2) := by
      rw [hzim]
      congr 1
      ring
    have hkernel' (u : U.U) (hu : u ∈ rows) :
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) := by
      have hqpow : (U.q u) ^ (-z.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (U.q_ge_one u) (by linarith [hxlo])
      have hqpowNon : 0 ≤ (U.q u) ^ (-z.re) :=
        Real.rpow_nonneg (le_of_lt (U.q_pos u)) _
      have hkernel := hcontrol Z hZ u ξ w z hξ hw (by rw [hzre]; exact hxlo)
        (by rw [hzre]; exact hxhi)
      rw [hgauss] at hkernel
      have hqεpos : 0 < (U.q u) ^ ε := Real.rpow_pos_of_pos (U.q_pos u) ε
      have hZfarpos : 0 < Z ^ Estar 4 4 350000 :=
        Real.rpow_pos_of_pos (by linarith : 0 < Z) _
      have hA : 0 ≤ C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε *
          Real.exp (-y ^ 2) * (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
        positivity
      have hB : 0 ≤ C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε *
          Real.exp (-y ^ 2) * (1 + |w.im|) ^ (-A0) := by positivity
      have hC : 0 ≤ C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) := by
        positivity
      have hD : 0 ≤ C0 * (U.q u) ^ (-z.re) * (U.q u) ^ ε *
          Real.exp (-y ^ 2) * (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
        positivity
      calc
        _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
            (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := hkernel
        _ = (C0 * (U.q u) ^ (-z.re) * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) *
              Z ^ Estar ξ.re w.re z.re := by ring
        _ ≤ (C0 * (U.q u) ^ (-z.re) * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) *
              Z ^ Estar 4 4 350000 :=
                mul_le_mul_of_nonneg_left hZrpow hD
        _ = (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) * (U.q u) ^ (-z.re) := by ring
        _ ≤ (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) * 1 :=
                mul_le_mul_of_nonneg_left hqpow hA
        _ = (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) := by rw [mul_one]
        _ = (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |w.im|) ^ (-A0)) * (1 + |z.im|) ^ (-A0) := by ring
        _ ≤ (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |w.im|) ^ (-A0)) * 1 := mul_le_mul_of_nonneg_left hpolyZ hB
        _ = C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) *
              (1 + |w.im|) ^ (-A0) := by rw [mul_one]
        _ = (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2)) *
              (1 + |w.im|) ^ (-A0) := by ring
        _ ≤ (C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left hpolyW hC
        _ = C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) := by rw [mul_one]
    have hsumNorm := norm_sum_le rows
      (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hsumBound : ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
        ∑ u ∈ rows, C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2) :=
      Finset.sum_le_sum fun u hu => hkernel' u hu
    have hsumEq :
        (∑ u ∈ rows, C0 * Z ^ Estar 4 4 350000 * (U.q u) ^ ε * Real.exp (-y ^ 2)) =
          Cshift * Real.exp (-y ^ 2) := by
      dsimp [Cshift]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    change ‖G (trans ((x : ℂ) + y * Complex.I))‖ ≤ _
    rw [htrans]
    calc
      ‖G z‖ ≤ ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
        simpa [G] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
  have hcontour := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    Fcont (a := 2) (b := 350000) (C := Cshift) (by norm_num) hFdiff hFbound
  have htranslate (σ : ℝ) :
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
    have hcomp : (∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) (-ξ.im)).integral_comp
        (Homeomorph.addLeft (-ξ.im)).measurableEmbedding
        (fun t : ℝ => G ((σ : ℂ) + t * Complex.I))
      simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have harg (t : ℝ) :
        ((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I =
          (σ : ℂ) + (t - ξ.im) * Complex.I := by
      apply Complex.ext
      · simp
      · simp
    calc
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
          ∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change G (((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I) =
          G ((σ : ℂ) + (t - ξ.im) * Complex.I)
        rw [harg]
      _ = ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := hcomp
  have hshiftV : vertical 2 Fcont = vertical 350000 Fcont := by
    unfold vertical
    rw [hcontour]
  calc
    vertical 2 G = vertical 2 Fcont := by
      unfold vertical
      rw [← htranslate 2]
    _ = vertical 350000 Fcont := hshiftV
    _ = vertical 350000 G := by
      unfold vertical
      rw [htranslate 350000]

private theorem rows_vertical_congr (σ : ℝ) (f g : ℂ → ℂ)
    (h : ∀ t : ℝ, f (σ + t * Complex.I) = g (σ + t * Complex.I)) :
    vertical σ f = vertical σ g := by
  unfold vertical
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact h t

private theorem rows_tripleVertical_congr_lines
    (σξ σw σz : ℝ) (f g : ℂ → ℂ → ℂ → ℂ)
    (h : ∀ tξ tw tz : ℝ,
      f (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I) =
        g (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)) :
    tripleVertical σξ σw σz f = tripleVertical σξ σw σz g := by
  unfold tripleVertical
  apply rows_vertical_congr
  intro tξ
  apply rows_vertical_congr
  intro tw
  apply rows_vertical_congr
  intro tz
  exact h tξ tw tz

private theorem rows_far_qpower_bound (T q ε : ℝ) (hT : 1 ≤ T)
    (hqT : T ≤ q) (hqU : q < 2 * T) (hε : 0 < ε) :
    q ^ (-(350000 : ℝ)) * q ^ ε ≤ 2 ^ ε * T ^ (-(350000 : ℝ) + ε) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hqpos : 0 < q := by linarith [hTpos, hqT]
  have hbase : T ^ (350000 : ℝ) ≤ q ^ (350000 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hqT (by norm_num)
  have hTpowpos : 0 < T ^ (350000 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hqpowpos : 0 < q ^ (350000 : ℝ) := Real.rpow_pos_of_pos hqpos _
  have hinv : (q ^ (350000 : ℝ))⁻¹ ≤ (T ^ (350000 : ℝ))⁻¹ :=
    (inv_le_inv₀ hqpowpos hTpowpos).2 hbase
  have hqneg : q ^ (-(350000 : ℝ)) = (q ^ (350000 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hqpos.le]
  have hTneg : T ^ (-(350000 : ℝ)) = (T ^ (350000 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hTpos.le]
  have hneg : q ^ (-(350000 : ℝ)) ≤ T ^ (-(350000 : ℝ)) := by
    rw [hqneg, hTneg]
    exact hinv
  have hεpow : q ^ ε ≤ (2 * T) ^ ε :=
    Real.rpow_le_rpow (by positivity) hqU.le hε.le
  have hprod : (2 * T) ^ ε = 2 ^ ε * T ^ ε :=
    Real.mul_rpow (by norm_num) (by linarith)
  calc
    q ^ (-(350000 : ℝ)) * q ^ ε ≤ T ^ (-(350000 : ℝ)) * (2 * T) ^ ε :=
      mul_le_mul hneg hεpow (Real.rpow_nonneg hqpos.le _) (Real.rpow_nonneg (by linarith) _)
    _ = T ^ (-(350000 : ℝ)) * (2 ^ ε * T ^ ε) := by rw [hprod]
    _ = 2 ^ ε * (T ^ (-(350000 : ℝ)) * T ^ ε) := by ring
    _ = 2 ^ ε * T ^ (-(350000 : ℝ) + ε) := by rw [← Real.rpow_add hTpos]

private theorem rows_initial_rowContribution_eq (hEuler : EulerHypotheses R η)
    (Z : ℝ) (rows : Finset U.U) :
    rowContribution R sd W η U rows Z =
      tripleVertical 4 4 2 (fun ξ w z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) := by
  apply rows_tripleVertical_congr_lines
  intro tξ tw tz
  let ξ : ℂ := 4 + tξ * Complex.I
  let w : ℂ := 4 + tw * Complex.I
  let z : ℂ := 2 + tz * Complex.I
  have hinit : initialRegion ξ w z := by
    norm_num [initialRegion, ξ, w, z]
  have hrow (u : U.U) (hu : u ∈ rows) :
      rowKernel R sd W η U HA HC u Z ξ w z =
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
          ((U.q u : ℂ) ^ (-z) * calF R η U u ξ w z) := by
    have hEulerRow := (prop_euler_product R η U HC HA hEuler).2.1 u ξ w z hinit
    unfold rowKernel
    rw [hEulerRow]
    unfold rowTwist
    ring_nf
  have hsum :
      (∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) =
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
          ∑ u ∈ rows, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z := by
    calc
      _ = ∑ u ∈ rows, (mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
          ((U.q u : ℂ) ^ (-z) * calF R η U u ξ w z)) :=
            Finset.sum_congr rfl (fun u hu => hrow u hu)
      _ = _ := by rw [Finset.mul_sum]
  exact hsum.symm

private theorem rows_small_LS_differentiable (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (hχne : χ ≠ 1) :
    Differentiable ℂ (HA.LS S χ) := by
  obtain ⟨L, hL⟩ := HA.2.2.1 χ hχ hχne
  have hcomplete : Differentiable ℂ (HA.L χ) := by
    change Differentiable ℂ (HA.1.1 χ)
    rw [← hL]
    exact L.differentiable
  have hfactor : Differentiable ℂ (fun s : ℂ =>
      ∏ v ∈ S.Sf, (1 - χ.primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    refine Differentiable.fun_finsetProd ?_
    intro v hv
    have hn : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt
        (NumberField.HeightOneSpectrum.one_lt_absNorm v)))
    have hpow : Differentiable ℂ (fun s : ℂ =>
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
      intro s
      exact (differentiable_id.neg s).const_cpow (Or.inl hn)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (χ.primeValue v)).mul hpow)
  change Differentiable ℂ (HA.L χ * fun s : ℂ =>
    ∏ v ∈ S.Sf, (1 - χ.primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))
  exact hcomplete.mul hfactor

private theorem rows_small_LS_differentiableOn (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) :
    DifferentiableOn ℂ (HA.LS S χ) {s | 1 < s.re} := by
  by_cases hχne : χ = 1
  · subst χ
    exact rows_LS_trivial_differentiableOn HA S
  · exact (rows_small_LS_differentiable (HA := HA) (S := S) χ hχ hχne).differentiableOn

private theorem rows_small_kernel_differentiableOn_xi
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 0 < Z)
    (u : U.U) (w z : ℂ)
    (hw : 3 / 1000 - 1 / 100000 < w.re)
    (hz : 4 / 10 - 1 / 100000 < z.re) :
    DifferentiableOn ℂ (fun ξ => rowKernel R sd W η U HA HC u Z ξ w z)
      {ξ | 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4} := by
  let strip : Set ℂ := {ξ | 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4}
  obtain ⟨hMdiff, _, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hMellin : Differentiable ℂ
      (fun ξ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) := by
    unfold mellinWeight
    have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have hZexp : Differentiable ℂ (fun ξ : ℂ => ξ + z - 1) := by fun_prop
    have hZpow : Differentiable ℂ (fun ξ : ℂ => (Z : ℂ) ^ (ξ + z - 1)) := by
      intro ξ
      exact (hZexp ξ).const_cpow (Or.inl hZbase)
    have hX : Differentiable ℂ (fun _ξ : ℂ =>
        ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := differentiable_const _
    have hY : Differentiable ℂ (fun _ξ : ℂ =>
        ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := differentiable_const _
    have hG : Differentiable ℂ (fun ξ : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) := by
      fun_prop
    have hM : Differentiable ℂ (fun _ξ : ℂ => weightM R sd W z) := differentiable_const _
    have hW : Differentiable ℂ (fun _ξ : ℂ => weightW1hat W w) := differentiable_const _
    have h₁ := hX.mul hZpow
    have h₂ := h₁.mul hY
    have h₃ := h₂.mul hG
    have h₄ := h₃.mul hM
    exact h₄.mul hW
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun ξ => ![ξ, w, z]
  have hpmap : Differentiable ℂ pmap := by
    intro ξ
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hMaps : MapsTo pmap strip {p | eulerNeighborhood p} := by
    intro ξ hξ
    left
    change (998 / 1000 - 1 / 100000 < ξ.re ∧
      3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
    refine ⟨?_, hw, hz⟩
    · exact lt_of_lt_of_le (by norm_num [δ1]) hξ.1
  have hHC : DifferentiableOn ℂ (fun ξ => HC.H u ![ξ, w, z]) strip := by
    exact (hHP.2.1 u).comp hpmap.differentiableOn hMaps
  have htw : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have htwfin : IsOfFinOrder (rowTwist η U u) := by
    rw [htw]
    exact U.omega_finiteOrder u
  obtain ⟨f, hf⟩ := U.omega_primitive u
  have htwprim : IsPrimitiveConductor (rowTwist η U u) f := by
    rw [htw]
    exact hf
  have hLdiff := rows_small_LS_differentiableOn (HA := HA) (S := S)
    (rowTwist η U u) htwfin
  have hLdiff' : DifferentiableOn ℂ (HA.LS S (rowTwist η U u)) strip := by
    apply hLdiff.mono
    intro ξ hξ
    change 1 < ξ.re
    have hδ : 0 < δ1 := by norm_num [δ1]
    linarith [hξ.1]
  have hLne : ∀ ξ ∈ strip, HA.LS S (rowTwist η U u) ξ ≠ 0 := by
    intro ξ hξ
    have hξone : 1 < ξ.re := by
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith [hξ.1]
    exact (rows_LS_inverse_bound HA S (rowTwist η U u) htwfin f htwprim hξone).1
  have hInv : DifferentiableOn ℂ
      (fun ξ => (HA.LS S (rowTwist η U u) ξ)⁻¹) strip := by
    exact hLdiff'.inv hLne
  have hLz : Differentiable ℂ (fun _ξ : ℂ => HA.LS S 1 (6 * z)) :=
    differentiable_const _
  have hK : Differentiable ℂ (fun _ξ : ℂ => HA.LS S (U.kummer u) w) :=
    differentiable_const _
  have hq : Differentiable ℂ (fun _ξ : ℂ => (U.q u : ℂ) ^ (-z)) :=
    differentiable_const _
  unfold rowKernel
  change DifferentiableOn ℂ (fun ξ =>
      (mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z]) /
          HA.LS S (rowTwist η U u) ξ) strip
  simp only [div_eq_mul_inv]
  have hMellinOn : DifferentiableOn ℂ
      (fun ξ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) strip :=
    hMellin.differentiableOn
  have hqOn : DifferentiableOn ℂ (fun ξ => (U.q u : ℂ) ^ (-z)) strip :=
    hq.differentiableOn
  have hLzOn : DifferentiableOn ℂ (fun ξ => HA.LS S 1 (6 * z)) strip :=
    hLz.differentiableOn
  have hKOn : DifferentiableOn ℂ (fun ξ => HA.LS S (U.kummer u) w) strip :=
    hK.differentiableOn
  have hprod₁ : DifferentiableOn ℂ
      (fun ξ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z)) strip :=
    hMellinOn.mul hqOn
  have hprod₂ : DifferentiableOn ℂ
      (fun ξ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
        HA.LS S 1 (6 * z)) strip := hprod₁.mul hLzOn
  have hprod₃ : DifferentiableOn ℂ
      (fun ξ => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
        HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w) strip := hprod₂.mul hKOn
  have hprod₄ := hprod₃.mul hHC
  exact hprod₄.mul hInv

private theorem rows_small_kernel_differentiableOn_z
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 0 < Z)
    (u : U.U) (ξ w : ℂ)
    (hξ : 998 / 1000 - 1 / 100000 < ξ.re)
    (hw : 3 / 1000 - 1 / 100000 < w.re) :
    DifferentiableOn ℂ (fun z => rowKernel R sd W η U HA HC u Z ξ w z)
      {z | 4 / 10 ≤ z.re ∧ z.re ≤ 2} := by
  let strip : Set ℂ := {z | 4 / 10 ≤ z.re ∧ z.re ≤ 2}
  obtain ⟨hMdiff, _, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hMstrip : DifferentiableOn ℂ (weightM R sd W) strip := by
    apply hMdiff.mono
    intro z hz
    exact lt_of_lt_of_le (by norm_num) hz.1
  have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ a))
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ b))
  have hXexp : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) := by fun_prop
  have hX : Differentiable ℂ (fun z : ℂ =>
      ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := by
    intro z
    exact (hXexp z).const_cpow (Or.inl hXbase)
  have hZexp : Differentiable ℂ (fun z : ℂ => ξ + z - 1) := by fun_prop
  have hZpow : Differentiable ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) := by
    intro z
    exact (hZexp z).const_cpow (Or.inl hZbase)
  have hY : Differentiable ℂ (fun _z : ℂ =>
      ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := differentiable_const _
  have hGauss : Differentiable ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) := by
    fun_prop
  have hW : Differentiable ℂ (fun z : ℂ => weightW1hat W w) := differentiable_const _
  have hMellin : DifferentiableOn ℂ
      (fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) strip := by
    unfold mellinWeight
    exact (((((hX.differentiableOn.mul hZpow.differentiableOn).mul
      hY.differentiableOn).mul hGauss.differentiableOn).mul hMstrip).mul
        hW.differentiableOn)
  have hqbase : (U.q u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (U.q_pos u))
  have hqpow : Differentiable ℂ (fun z : ℂ => (U.q u : ℂ) ^ (-z)) := by
    intro z
    exact (differentiable_id.neg z).const_cpow (Or.inl hqbase)
  have hLz : DifferentiableOn ℂ (fun z => HA.LS S 1 (6 * z)) strip := by
    apply (rows_LS_trivial_differentiableOn HA S).comp
      ((show Differentiable ℂ (fun z : ℂ => 6 * z) by fun_prop).differentiableOn)
    intro z hz
    change 1 < (6 * z).re
    have hre : (6 * z).re = 6 * z.re := by simp
    rw [hre]
    nlinarith [hz.1]
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun z => ![ξ, w, z]
  have hpmap : Differentiable ℂ pmap := by
    intro z
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hMaps : MapsTo pmap strip {p | eulerNeighborhood p} := by
    intro z hz
    left
    change (998 / 1000 - 1 / 100000 < ξ.re ∧
      3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
    exact ⟨hξ, hw, lt_of_lt_of_le (by norm_num) hz.1⟩
  have hHC : DifferentiableOn ℂ (fun z => HC.H u ![ξ, w, z]) strip :=
    (hHP.2.1 u).comp hpmap.differentiableOn hMaps
  have hK : Differentiable ℂ (fun _z : ℂ => HA.LS S (U.kummer u) w) :=
    differentiable_const _
  have hInv : Differentiable ℂ (fun _z : ℂ =>
      (HA.LS S (rowTwist η U u) ξ)⁻¹) := differentiable_const _
  have hq : DifferentiableOn ℂ (fun z => (U.q u : ℂ) ^ (-z)) strip :=
    hqpow.differentiableOn
  have hK' : DifferentiableOn ℂ (fun z => HA.LS S (U.kummer u) w) strip :=
    hK.differentiableOn
  have hInv' : DifferentiableOn ℂ (fun z => (HA.LS S (rowTwist η U u) ξ)⁻¹) strip :=
    hInv.differentiableOn
  unfold rowKernel
  change DifferentiableOn ℂ
    (fun z => (mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
      HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z]) /
        HA.LS S (rowTwist η U u) ξ) strip
  simp only [div_eq_mul_inv]
  have h₁ := hMellin.mul hq
  have h₂ := h₁.mul hLz
  have h₃ := h₂.mul hK'
  have h₄ := h₃.mul hHC
  exact h₄.mul hInv'

private theorem rows_small_kernel_differentiableOn_w
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 0 < Z)
    (u : U.U) (ξ z : ℂ) (hu : u ≠ U.one)
    (hξ : 998 / 1000 - 1 / 100000 < ξ.re)
    (hz : 4 / 10 - 1 / 100000 < z.re) :
    DifferentiableOn ℂ (fun w => rowKernel R sd W η U HA HC u Z ξ w z)
      {w | 3 / 1000 ≤ w.re ∧ w.re ≤ 4} := by
  let strip : Set ℂ := {w | 3 / 1000 ≤ w.re ∧ w.re ≤ 4}
  have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ b))
  have hYexp : Differentiable ℂ (fun w : ℂ => w - 1) := by fun_prop
  have hY : Differentiable ℂ (fun w : ℂ =>
      ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := by
    intro w
    exact (hYexp w).const_cpow (Or.inl hYbase)
  have hG : Differentiable ℂ (fun w : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) :=
    differentiable_const _
  have hMellin : Differentiable ℂ
      (fun w => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) := by
    obtain ⟨_, hWdiff, _, _, _⟩ := (po_weights_exist R sd).2 W
    unfold mellinWeight
    have hX : Differentiable ℂ (fun _w : ℂ =>
        ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := differentiable_const _
    have hZpow : Differentiable ℂ (fun _w : ℂ =>
        (Z : ℂ) ^ (ξ + z - 1)) := differentiable_const _
    have hY' : Differentiable ℂ (fun w : ℂ =>
        ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := hY
    have hG' : Differentiable ℂ (fun _w : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) :=
      differentiable_const _
    have hM : Differentiable ℂ (fun _w : ℂ => weightM R sd W z) :=
      differentiable_const _
    exact (((((hX.mul hZpow).mul hY').mul hG').mul hM).mul hWdiff)
  have hKfin : IsOfFinOrder (U.kummer u) := rows_kummer_finiteOrder R η U hEuler u
  have hKne : U.kummer u ≠ 1 := by
    intro h
    exact hu ((U.kummer_principal_iff u).mp h)
  have hK : Differentiable ℂ (HA.LS S (U.kummer u)) :=
    rows_small_LS_differentiable (HA := HA) (S := S)
      (U.kummer u) hKfin hKne
  have hK' : DifferentiableOn ℂ (fun w => HA.LS S (U.kummer u) w) strip :=
    hK.differentiableOn
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun w => ![ξ, w, z]
  have hpmap : Differentiable ℂ pmap := by
    intro w
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hMaps : MapsTo pmap strip {p | eulerNeighborhood p} := by
    intro w hw
    left
    change (998 / 1000 - 1 / 100000 < ξ.re ∧
      3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
    exact ⟨hξ, lt_of_lt_of_le (by norm_num) hw.1, hz⟩
  have hHC : DifferentiableOn ℂ (fun w => HC.H u ![ξ, w, z]) strip :=
    (hHP.2.1 u).comp hpmap.differentiableOn hMaps
  have hq : Differentiable ℂ (fun _w : ℂ => (U.q u : ℂ) ^ (-z)) :=
    differentiable_const _
  have hLz : Differentiable ℂ (fun _w : ℂ => HA.LS S 1 (6 * z)) :=
    differentiable_const _
  have hInv : Differentiable ℂ (fun _w : ℂ =>
      (HA.LS S (rowTwist η U u) ξ)⁻¹) := differentiable_const _
  unfold rowKernel
  change DifferentiableOn ℂ (fun w =>
    (mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * (U.q u : ℂ) ^ (-z) *
      HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ, w, z]) /
        HA.LS S (rowTwist η U u) ξ) strip
  simp only [div_eq_mul_inv]
  have hq' : DifferentiableOn ℂ (fun _w : ℂ => (U.q u : ℂ) ^ (-z)) strip :=
    hq.differentiableOn
  have hLz' : DifferentiableOn ℂ (fun _w : ℂ => HA.LS S 1 (6 * z)) strip :=
    hLz.differentiableOn
  have hInv' : DifferentiableOn ℂ (fun _w : ℂ =>
      (HA.LS S (rowTwist η U u) ξ)⁻¹) strip := hInv.differentiableOn
  have hMellin' : DifferentiableOn ℂ
      (fun w => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) strip :=
    hMellin.differentiableOn
  have h₁ := hMellin'.mul hq'
  have h₂ := h₁.mul hLz'
  have h₃ := h₂.mul hK'
  have h₄ := h₃.mul hHC
  exact h₄.mul hInv'

private theorem rows_small_kummer_LS_bound (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ AF C : ℝ, 0 < AF ∧ 0 < C ∧
      ∀ u, u ≠ U.one → ∀ w : ℂ, 3 / 1000 ≤ w.re → w.re ≤ 4 →
        ‖HA.LS S (U.kummer u) w‖ ≤
          C * (U.q u) ^ (1 / 2 + ε) * (1 + |w.im|) ^ AF := by
  obtain ⟨AF, hAF, hconvex⟩ := zf_convexity (F := F)
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨CK, hCK, hconvex⟩ := hconvex (ε / 4) hδ
  obtain ⟨Ccond, hCcond, hcond⟩ :=
    U.kummer_twist_conductor_bound hEuler.1 hEuler.2.1
  let γ : ℝ := 1 / 2 + ε / 4
  let Cpre : ℝ := CK * Ccond ^ γ * 2 ^ AF * 2 ^ S.Sf.card
  let C : ℝ := Cpre + 1
  have hCpre : 0 ≤ Cpre := by dsimp [Cpre]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨AF, C, hAF, hC, ?_⟩
  intro u hu w hwlo hwhi
  have hKfin : IsOfFinOrder (U.kummer u) := rows_kummer_finiteOrder R η U hEuler u
  have hKne : U.kummer u ≠ 1 := by
    intro h
    exact hu ((U.kummer_principal_iff u).mp h)
  obtain ⟨m, hm0, hmdvd, hmnorm⟩ := (hcond u).1
  obtain ⟨f, hf⟩ := rows_exists_primitive_conductor
    (U.kummer u) ⟨m, hm0, hmdvd⟩
  have hfnorm : (Ideal.absNorm f : ℝ) ≤ Ccond * U.q u := by
    calc
      (Ideal.absNorm f : ℝ) ≤ Ideal.absNorm m := by
        exact_mod_cast hf.2.2 m hm0 hmdvd
      _ ≤ Ccond * U.q u := hmnorm
  obtain ⟨L, hL⟩ := HA.2.2.1 (U.kummer u) hKfin hKne
  have hconv := hconvex (U.kummer u) hKfin hKne f hf L.value
    ⟨L.differentiable, L.agrees⟩
  have hLbound : ‖HA.L (U.kummer u) w‖ ≤
      CK * (Ideal.absNorm f : ℝ) ^ γ * (2 + |w.im|) ^ AF := by
    change ‖HA.1.1 (U.kummer u) w‖ ≤ _
    rw [← hL]
    exact hconv.1 w hwlo hwhi
  have hfactor (v : FinPlace F) :
      ‖1 - (U.kummer u).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ ≤ 2 := by
    have hn : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hnNat : 2 ≤ Ideal.absNorm v.asIdeal := by
      have hv := NumberField.HeightOneSpectrum.one_lt_absNorm v
      exact_mod_cast hv
    have hnreal : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    have hpow : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn)]
      rfl
    have hpowle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-w.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnreal (by linarith)
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(U.kummer u).primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ := norm_sub_le _ _
      _ = 1 + ‖(U.kummer u).primeValue v‖ *
          ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ := by simp [norm_mul]
      _ ≤ 2 := by
        have hprime := rows_primeValue_norm_le_one (U.kummer u) hKfin v
        have hprodle := mul_le_one₀ hprime (norm_nonneg
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))) (by rw [hpow]; exact hpowle)
        linarith
  have hprod : ‖∏ v ∈ S.Sf,
      (1 - (U.kummer u).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ ≤ 2 ^ S.Sf.card := by
    calc
      _ ≤ ∏ v ∈ S.Sf, ‖1 - (U.kummer u).primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro v hv
          exact norm_nonneg _
        · intro v hv
          exact hfactor v
      _ = 2 ^ S.Sf.card := by simp
  have hLS : ‖HA.LS S (U.kummer u) w‖ ≤
      CK * (Ideal.absNorm f : ℝ) ^ γ * (2 + |w.im|) ^ AF * 2 ^ S.Sf.card := by
    change ‖HA.L (U.kummer u) w * ∏ v ∈ S.Sf,
      (1 - (U.kummer u).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hLbound hprod (norm_nonneg _) (by positivity)
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hqpos := U.q_pos u
  have hfnormPow : (Ideal.absNorm f : ℝ) ^ γ ≤ (Ccond * U.q u) ^ γ :=
    Real.rpow_le_rpow (by positivity) hfnorm hγ
  have hsplit : (Ccond * U.q u) ^ γ = Ccond ^ γ * (U.q u) ^ γ :=
    Real.mul_rpow (le_of_lt hCcond) (le_of_lt hqpos)
  have himBase : 2 + |w.im| ≤ 2 * (1 + |w.im|) := by
    have := abs_nonneg w.im
    linarith
  have himPow : (2 + |w.im|) ^ AF ≤ 2 ^ AF * (1 + |w.im|) ^ AF := by
    calc
      _ ≤ (2 * (1 + |w.im|)) ^ AF := Real.rpow_le_rpow (by positivity) himBase hAF.le
      _ = 2 ^ AF * (1 + |w.im|) ^ AF := Real.mul_rpow (by norm_num) (by positivity)
  calc
    _ ≤ CK * (Ccond ^ γ * (U.q u) ^ γ) *
        (2 ^ AF * (1 + |w.im|) ^ AF) * 2 ^ S.Sf.card := by
      calc
        _ ≤ CK * (Ideal.absNorm f : ℝ) ^ γ *
            (2 + |w.im|) ^ AF * 2 ^ S.Sf.card := hLS
        _ ≤ CK * (Ccond * U.q u) ^ γ *
            (2 + |w.im|) ^ AF * 2 ^ S.Sf.card := by gcongr
        _ ≤ CK * (Ccond ^ γ * (U.q u) ^ γ) *
            (2 ^ AF * (1 + |w.im|) ^ AF) * 2 ^ S.Sf.card := by
          rw [hsplit]
          gcongr
    _ = Cpre * (U.q u) ^ γ * (1 + |w.im|) ^ AF := by
      dsimp [Cpre]
      ring
    _ ≤ C * (U.q u) ^ γ * (1 + |w.im|) ^ AF := by
      have hrest : 0 ≤ (U.q u) ^ γ * (1 + |w.im|) ^ AF := by positivity
      have hCprele : Cpre ≤ C := by dsimp [C]; linarith
      calc
        _ = Cpre * ((U.q u) ^ γ * (1 + |w.im|) ^ AF) := by ring
        _ ≤ C * ((U.q u) ^ γ * (1 + |w.im|) ^ AF) :=
          mul_le_mul_of_nonneg_right hCprele hrest
        _ = _ := by ring
    _ ≤ C * (U.q u) ^ (1 / 2 + ε) * (1 + |w.im|) ^ AF := by
      have hqpow : (U.q u) ^ γ ≤ (U.q u) ^ (1 / 2 + ε) := by
        apply Real.rpow_le_rpow_of_exponent_le (U.q_ge_one u)
        dsimp [γ]
        linarith
      have hcoeff : C * (U.q u) ^ γ ≤ C * (U.q u) ^ (1 / 2 + ε) :=
        mul_le_mul_of_nonneg_left hqpow hC.le
      have hheight : 0 ≤ (1 + |w.im|) ^ AF := by positivity
      calc
        _ = (C * (U.q u) ^ γ) * (1 + |w.im|) ^ AF := by ring
        _ ≤ (C * (U.q u) ^ (1 / 2 + ε)) * (1 + |w.im|) ^ AF :=
          mul_le_mul_of_nonneg_right hcoeff hheight
        _ = _ := by ring

private def rows_small_idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

private theorem rows_small_idealCount_sum_eq (n : ℕ) :
    Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n} =
      ∑ k ∈ Finset.Icc 0 n, rows_small_idealCount (F := F) k := by
  classical
  unfold rows_small_idealCount
  rw [← Finset.card_preimage_eq_sum_card_image_eq
    (fun k _ => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) k)]
  simp [Set.coe_eq_subtype]

private theorem rows_small_idealCount_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (rows_small_idealCount (F := F) n : ℂ)) s := by
  have hcountLim : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ)) atTop (𝓝 (NumberField.dedekindZeta_residue F)) := by
    have h := (Ideal.tendsto_norm_le_div_atTop F).comp tendsto_natCast_atTop_atTop
    convert h using 1
    · funext n
      congr 1
      exact_mod_cast (Nat.card_congr
        (Equiv.subtypeEquivRight (fun _ => by norm_cast)))
    · simp [NumberField.dedekindZeta_residue]
  have hcountLim' : Tendsto
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n} : ℝ) /
        (n : ℝ) ^ (1 : ℝ)) atTop (𝓝 (NumberField.dedekindZeta_residue F)) := by
    simpa only [Real.rpow_one] using hcountLim
  have hcount : (fun n : ℕ =>
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (r := 1) hcountLim'
  have hpartial : (fun n : ℕ =>
      ∑ k ∈ Finset.Icc 1 n, (rows_small_idealCount (F := F) k : ℝ)) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    apply (isBigO_of_le (l := atTop) ?_).trans hcount
    intro n
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k hk => Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      ∑ k ∈ Finset.Icc 1 n, (rows_small_idealCount (F := F) k : ℝ) ≤
          ∑ k ∈ Finset.Icc 0 n, (rows_small_idealCount (F := F) k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc (by omega) le_rfl)
        intro k hk hk'
        exact Nat.cast_nonneg _
      _ = (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n} : ℝ) := by
        exact_mod_cast (rows_small_idealCount_sum_eq (F := F) n).symm
  have hO : (fun n : ℕ =>
      ∑ k ∈ Finset.Icc 1 n,
        ‖(rows_small_idealCount (F := F) k : ℂ)‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    simpa only [Complex.norm_natCast] using hpartial
  exact LSeriesSummable_of_sum_norm_bigO hO zero_le_one (by simpa using hs)

private theorem rows_small_idealCount_abscissa_le_one :
    LSeries.abscissaOfAbsConv (fun n => (rows_small_idealCount (F := F) n : ℂ)) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact rows_small_idealCount_summable (F := F) (s := (y : ℂ)) (by simpa using hy)

private theorem rows_small_dedekindZeta_re_eq_tsum_norm {σ : ℝ} (hσ : 1 < σ) :
    (NumberField.dedekindZeta F (σ : ℂ)).re =
      ∑' n, ‖LSeries.term
        (fun n => (rows_small_idealCount (F := F) n : ℂ)) (σ : ℂ) n‖ := by
  have hsum := rows_small_idealCount_summable (F := F) (s := (σ : ℂ)) (by simpa using hσ)
  have hterm (n : ℕ) :
      0 ≤ LSeries.term (fun n => (rows_small_idealCount (F := F) n : ℂ))
        (σ : ℂ) n := by
    exact LSeries.term_nonneg (by positivity) σ
  calc
    (NumberField.dedekindZeta F (σ : ℂ)).re =
        (∑' n, LSeries.term
          (fun n => (rows_small_idealCount (F := F) n : ℂ)) (σ : ℂ) n).re := by
            rfl
    _ = ∑' n, (LSeries.term
        (fun n => (rows_small_idealCount (F := F) n : ℂ)) (σ : ℂ) n).re :=
          Complex.re_tsum hsum
    _ = _ := by
      apply tsum_congr
      intro n
      exact congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hterm n))

private theorem rows_small_dedekindZeta_real_antitone {s t : ℝ}
    (hs : 1 < s) (hst : s ≤ t) :
    (NumberField.dedekindZeta F (t : ℂ)).re ≤
      (NumberField.dedekindZeta F (s : ℂ)).re := by
  have hsummableS := rows_small_idealCount_summable (F := F) (s := (s : ℂ)) (by simpa using hs)
  have hsummableT := rows_small_idealCount_summable (F := F) (s := (t : ℂ))
    (by have ht : 1 < t := lt_of_lt_of_le hs hst; simpa using ht)
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n => (rows_small_idealCount (F := F) n : ℂ)) (t : ℂ) n‖ ≤
        ‖LSeries.term (fun n => (rows_small_idealCount (F := F) n : ℂ)) (s : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · rfl
    · simp only [Complex.norm_natCast]
      have hn1 : 1 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hden : (n : ℝ) ^ s ≤ (n : ℝ) ^ t :=
        Real.rpow_le_rpow_of_exponent_le hn1 hst
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.rpow_pos_of_pos
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s) hden
  calc
    _ = ∑' n, ‖LSeries.term
        (fun n => (rows_small_idealCount (F := F) n : ℂ)) (t : ℂ) n‖ :=
          rows_small_dedekindZeta_re_eq_tsum_norm (F := F) (show 1 < t by linarith)
    _ ≤ ∑' n, ‖LSeries.term
        (fun n => (rows_small_idealCount (F := F) n : ℂ)) (s : ℂ) n‖ :=
          hsummableT.norm.tsum_le_tsum hterm hsummableS.norm
    _ = _ := (rows_small_dedekindZeta_re_eq_tsum_norm (F := F) hs).symm

private theorem rows_small_dedekindZeta_real_nonneg (s : ℝ) (hs : 1 < s) :
    0 ≤ (NumberField.dedekindZeta F (s : ℂ)).re := by
  rw [rows_small_dedekindZeta_re_eq_tsum_norm (F := F) hs]
  exact tsum_nonneg fun _ => norm_nonneg _

set_option maxHeartbeats 2000000 in
private theorem rows_small_kernel_control (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ AF Adec Aconv C0 Cconv : ℝ, 0 < AF ∧ 1 < Aconv ∧
      Adec = Aconv + AF + 2 ∧ 0 < Adec ∧ 0 < C0 ∧ 0 < Cconv ∧
      (∀ T : ℝ, ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) *
        (1 + |v|) ^ (-Aconv) ≤ Cconv * (1 + |T|) ^ (-2 : ℝ)) ∧
      ∀ Z, 2 ≤ Z → ∀ u, u ≠ U.one → ∀ ξ w z,
        1 + δ1 ≤ ξ.re → ξ.re ≤ 4 →
        3 / 1000 ≤ w.re → w.re ≤ 4 →
        4 / 10 ≤ z.re → z.re ≤ 2 →
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
  obtain ⟨Aconv, Cconv, hAconv, hCconv, hconv⟩ :=
    zf_height_convolution (2 : ℝ) (by norm_num)
  obtain ⟨AF, Ck, hAF, hCk, hKbound⟩ :=
    rows_small_kummer_LS_bound R η U HA hEuler (ε / 4) (by linarith)
  obtain ⟨CH, hCHpos, hHbound⟩ := (po_H_product R η U HC hEuler).2.2.2 (ε / 4) (by linarith)
  obtain ⟨Cht, hCht, hheight⟩ := zf_height_decay R sd W
    (1 + δ1) 4 (3 / 1000) 4 (4 / 10) 2 (Aconv + AF + 2)
    (by norm_num [δ1]) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  let Adec : ℝ := Aconv + AF + 2
  let KLS : ℝ := rows_absNorm_majorant (F := F) * 2 ^ S.Sf.card
  have hKLS : 0 ≤ KLS := by
    dsimp [KLS]
    exact mul_nonneg (rows_absNorm_majorant_nonneg (F := F)) (by positivity)
  let Cinv : ℝ := (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re * 2 ^ S.Sf.card
  let Cbase : ℝ := Cht * KLS * Ck * CH * Cinv
  let C0 : ℝ := Cbase + 1
  have hAdec : 1 < Adec := by dsimp [Adec]; linarith
  have hCinv : 0 ≤ Cinv := by
    change 0 ≤ (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re * 2 ^ S.Sf.card
    obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
    have hηinv := rows_LS_inverse_bound HA S η hEuler.1 fη hfη
      (s := (1 + δ1 : ℂ)) (by norm_num [δ1])
    have hprod : 0 ≤ (NumberField.dedekindZeta F ((1 + δ1 : ℝ) : ℂ)).re * 2 ^ S.Sf.card :=
      le_trans (norm_nonneg _) hηinv.2
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using hprod
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith
  have hCconv' : 0 < Cconv := hCconv
  have hconv' : ∀ T : ℝ, ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) *
      (1 + |v|) ^ (-Aconv) ≤ Cconv * (1 + |T|) ^ (-2 : ℝ) := hconv
  have hbound : ∀ Z, 2 ≤ Z → ∀ u, u ≠ U.one → ∀ ξ w z,
      1 + δ1 ≤ ξ.re → ξ.re ≤ 4 →
      3 / 1000 ≤ w.re → w.re ≤ 4 →
      4 / 10 ≤ z.re → z.re ≤ 2 →
      ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
        C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
    intro Z hZ u hu ξ w z hξlo hξhi hwlo hwhi hzlo hzhi
    have hZpos : 0 < Z := by linarith
    have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
    have hHCbound := hHbound u ![ξ, w, z] (by
      left
      change (998 / 1000 - 1 / 100000 < ξ.re ∧
        3 / 1000 - 1 / 100000 < w.re ∧ 4 / 10 - 1 / 100000 < z.re)
      refine ⟨?_, ?_, ?_⟩
      · have hδ : 0 < δ1 := by norm_num [δ1]
        linarith
      · linarith
      · linarith)
    have hheight := hheight ξ w z hξlo hξhi hwlo hwhi hzlo hzhi
    have hK := hKbound u hu w hwlo hwhi
    have hOne : IsOfFinOrder (1 : HeckeChar F) := by simp
    have hZeta : ‖HA.LS S 1 (6 * z)‖ ≤ KLS := by
      have hreal : (6 * z).re = 6 * z.re := by simp
      have h := rows_LS_norm_bound HA S 1 hOne (s := 6 * z) (by
        rw [hreal]
        nlinarith [hzlo])
      simpa [KLS] using h
    have htw : rowTwist η U u = U.omega u := by
      simpa [rowTwist] using (U.omega_induces_twist u).symm
    have htwfin : IsOfFinOrder (rowTwist η U u) := by
      rw [htw]
      exact U.omega_finiteOrder u
    obtain ⟨fω, hfω⟩ := U.omega_primitive u
    have htwprim : IsPrimitiveConductor (rowTwist η U u) fω := by
      rw [htw]
      exact hfω
    have hξone : 1 < ξ.re := by
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith
    obtain ⟨_, hrecip⟩ := rows_LS_inverse_bound HA S
      (rowTwist η U u) htwfin fω htwprim hξone
    have hζmono : (NumberField.dedekindZeta F (ξ.re : ℂ)).re ≤
        (NumberField.dedekindZeta F ((1 + δ1 : ℝ) : ℂ)).re :=
      rows_small_dedekindZeta_real_antitone (F := F) (by norm_num [δ1]) hξlo
    have hζmono' : (NumberField.dedekindZeta F (ξ.re : ℂ)).re ≤
        (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re := by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using hζmono
    have hCinvbound : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ Cinv := by
      calc
        _ ≤ (NumberField.dedekindZeta F ξ.re).re * 2 ^ S.Sf.card := hrecip
        _ ≤ (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re * 2 ^ S.Sf.card :=
          mul_le_mul_of_nonneg_right hζmono' (by positivity)
        _ = Cinv := by rfl
    have hqneg : (U.q u) ^ (-z.re) ≤ (U.q u) ^ (-(4 / 10 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (U.q_ge_one u) (by linarith)
    have hqpos := U.q_pos u
    have hqprod : (U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) *
        (U.q u) ^ (ε / 4) ≤ (U.q u) ^ (1 / 10 + ε) := by
      have h₁ : (U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) ≤
          (U.q u) ^ (-(4 / 10 : ℝ)) * (U.q u) ^ (1 / 2 + ε / 4) :=
        mul_le_mul_of_nonneg_right hqneg (Real.rpow_nonneg hqpos.le _)
      calc
        _ ≤ (U.q u) ^ (-(4 / 10 : ℝ)) * (U.q u) ^ (1 / 2 + ε / 4) *
            (U.q u) ^ (ε / 4) :=
              mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg hqpos.le _)
        _ = (U.q u) ^ (-(4 / 10 : ℝ) + (1 / 2 + ε / 4) + ε / 4) := by
              rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
        _ ≤ (U.q u) ^ (1 / 10 + ε) := by
              apply Real.rpow_le_rpow_of_exponent_le (U.q_ge_one u)
              ring_nf
              linarith
    have hpolyZ : (1 + |z.im|) ^ (-Adec) ≤
        (1 + |z.im|) ^ (-Aconv) := by
      apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg z.im])
      dsimp [Adec]
      linarith
    have hpolyW : (1 + |w.im|) ^ (-Adec) *
        (1 + |w.im|) ^ AF ≤ (1 + |w.im|) ^ (-2 : ℝ) := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + |w.im|)]
      apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg w.im])
      dsimp [Adec]
      linarith [hAconv]
    have hkernel := rows_rowKernel_norm_eq R sd W η U HA HC Z hZpos u ξ w z
    rw [hkernel]
    have hnormBound :
        Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
          ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ *
          ‖HA.LS S 1 (6 * z)‖ * ‖HA.LS S (U.kummer u) w‖ *
          ‖HC.H u ![ξ, w, z]‖ * ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤
        Cbase * Z ^ Estar ξ.re w.re z.re *
          ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) * (U.q u) ^ (ε / 4)) *
            Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by
      have hZpow : 0 ≤ Z ^ Estar ξ.re w.re z.re := Real.rpow_nonneg hZpos.le _
      have hqpow : 0 ≤ (U.q u) ^ (-z.re) := Real.rpow_nonneg hqpos.le _
      have hKP : 0 ≤ KLS := hKLS
      have hCP : 0 ≤ Ck := le_of_lt hCk
      have hHT : 0 ≤ CH := hCHpos.le
      have hIP : 0 ≤ Cinv := hCinv
      calc
        _ ≤ Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (-z.re) *
            (Cht * Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-Adec)) *
            KLS * (Ck * (U.q u) ^ (1 / 2 + ε / 4) * (1 + |w.im|) ^ AF) *
            (CH * (U.q u) ^ (ε / 4)) * Cinv := by
              gcongr
        _ = Cbase * Z ^ Estar ξ.re w.re z.re *
            ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) * (U.q u) ^ (ε / 4)) *
              Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by
                dsimp [Cbase]
                ring
    have hrest : 0 ≤ Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) *
          (1 + |w.im|) ^ (-2 : ℝ) := by positivity
    have hCbasele : Cbase ≤ C0 := by dsimp [C0]; linarith
    calc
      _ ≤ Cbase * Z ^ Estar ξ.re w.re z.re *
          ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) * (U.q u) ^ (ε / 4)) *
            Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-Adec) * (1 + |w.im|) ^ (-Adec) *
              (1 + |w.im|) ^ AF := hnormBound
      _ ≤ Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
        calc
          _ ≤ Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
                (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by
                  have hrestQ : 0 ≤ Cbase * Z ^ Estar ξ.re w.re z.re *
                      Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
                        (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by positivity
                  calc
                    _ = (Cbase * Z ^ Estar ξ.re w.re z.re *
                        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
                          (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF) *
                          ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + ε / 4) * (U.q u) ^ (ε / 4)) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left hqprod hrestQ
                    _ = _ := by ring
          _ ≤ Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) *
                (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by
                  have hrestZ : 0 ≤ Cbase * Z ^ Estar ξ.re w.re z.re *
                      (U.q u) ^ (1 / 10 + ε) * Real.exp (-((ξ.im + z.im) ^ 2)) *
                        (1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF := by positivity
                  calc
                    _ = (Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
                        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |w.im|) ^ (-Adec) *
                          (1 + |w.im|) ^ AF) * (1 + |z.im|) ^ (-Adec) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left hpolyZ hrestZ
                    _ = _ := by ring
          _ ≤ Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) *
                (1 + |w.im|) ^ (-2 : ℝ) := by
                  have hrestW : 0 ≤ Cbase * Z ^ Estar ξ.re w.re z.re *
                      (U.q u) ^ (1 / 10 + ε) * Real.exp (-((ξ.im + z.im) ^ 2)) *
                        (1 + |z.im|) ^ (-Aconv) := by positivity
                  calc
                    _ = (Cbase * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
                        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv)) *
                          ((1 + |w.im|) ^ (-Adec) * (1 + |w.im|) ^ AF) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left hpolyW hrestW
                    _ = _ := by ring
      _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
        calc
          _ = Cbase * (Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) *
                (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by ring
          _ ≤ C0 * _ := mul_le_mul_of_nonneg_right hCbasele hrest
          _ = _ := by ring
  refine ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, rfl, by linarith, hC0,
    hCconv', hconv', hbound⟩

private theorem rows_small_real_majorant_integrable (Aconv Cconv : ℝ)
    (hAconv : 1 < Aconv) (hCconv : 0 < Cconv)
    (hconv : ∀ T : ℝ, ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) *
      (1 + |v|) ^ (-Aconv) ≤ Cconv * (1 + |T|) ^ (-2 : ℝ)) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ)) (volume.prod (volume.prod volume)) := by
  let fW : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  let fZ : ℝ → ℝ → ℝ := fun x z =>
    Real.exp (-((x + z) ^ 2)) * (1 + |z|) ^ (-Aconv)
  let g : ℝ × (ℝ × ℝ) → ℝ := fun p => fZ p.1 p.2.2 * fW p.2.1
  have hWint : Integrable fW := by
    simpa [fW] using rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hWnonneg : ∀ t, 0 ≤ fW t := by intro t; dsimp [fW]; positivity
  have hZint (x : ℝ) : Integrable (fZ x) := by
    simpa [fZ] using rows_integrable_shifted_gaussian_poly Aconv x hAconv
  have hpowcont (q : ℝ) : Continuous (fun t : ℝ => (1 + |t|) ^ q) := by
    have hbase : Continuous (fun t : ℝ => 1 + |t|) := by fun_prop
    apply hbase.rpow_const
    intro t
    exact Or.inl (ne_of_gt (by positivity))
  have hgauss : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      Real.exp (-((p.1 + p.2.2) ^ 2))) := by fun_prop
  have hpolyZ : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (1 + |p.2.2|) ^ (-Aconv)) := by
    have hmap : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) := by fun_prop
    exact (hpowcont (-Aconv)).comp hmap
  have hpolyW : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      (1 + |p.2.1|) ^ (-2 : ℝ)) := by
    have hmap : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.1) := by fun_prop
    exact (hpowcont (-2 : ℝ)).comp hmap
  have hGcont : Continuous g := by
    dsimp [g, fW, fZ]
    exact (hgauss.mul hpolyZ).mul hpolyW
  have hGmeas : AEStronglyMeasurable g (volume.prod (volume.prod volume)) :=
    hGcont.aestronglyMeasurable
  have hsection (x : ℝ) :
      Integrable (fun p : ℝ × ℝ => fW p.1 * fZ x p.2) (volume.prod volume) :=
    hWint.mul_prod (hZint x)
  let Iw : ℝ := ∫ t : ℝ, fW t
  have hIw : 0 ≤ Iw := by
    dsimp [Iw]
    exact integral_nonneg fun t => hWnonneg t
  have hsectionNormEq (x : ℝ) :
      (∫ p : ℝ × ℝ, ‖fW p.1 * fZ x p.2‖) =
        ∫ p : ℝ × ℝ, fW p.1 * fZ x p.2 := by
    apply integral_congr_ae
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have hsectionIntegral (x : ℝ) :
      (∫ p : ℝ × ℝ, fW p.1 * fZ x p.2) = Iw * ∫ z : ℝ, fZ x z := by
    calc
      _ = ∫ t : ℝ, ∫ z : ℝ, fW t * fZ x z :=
        integral_prod _ (hsection x)
      _ = ∫ t : ℝ, fW t * (∫ z : ℝ, fZ x z) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [integral_const_mul]
      _ = Iw * ∫ z : ℝ, fZ x z := by
        rw [integral_mul_const]
  have hsectionBound (x : ℝ) :
      (∫ p : ℝ × ℝ, ‖fW p.1 * fZ x p.2‖) ≤
        (Iw * Cconv) * (1 + |x|) ^ (-2 : ℝ) := by
    rw [hsectionNormEq, hsectionIntegral]
    calc
      _ ≤ Iw * (Cconv * (1 + |x|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hconv x) hIw
      _ = _ := by ring
  have hpolyInt : Integrable (fun x : ℝ => (1 + |x|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  let gout : ℝ → ℝ := fun x => (Iw * Cconv) * (1 + |x|) ^ (-2 : ℝ)
  have hgout : Integrable gout := by
    simpa [gout, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
      hpolyInt.const_mul (Iw * Cconv)
  have hnormMeas : AEStronglyMeasurable
      (fun x : ℝ => ∫ p : ℝ × ℝ, ‖g (x, p)‖) volume :=
    hGmeas.norm.integral_prod_right'
  have hnormFunction : Integrable
      (fun x : ℝ => ∫ p : ℝ × ℝ, ‖g (x, p)‖) := by
    apply hgout.mono' hnormMeas
    filter_upwards [] with x
    have hnon : 0 ≤ ∫ p : ℝ × ℝ, ‖g (x, p)‖ :=
      integral_nonneg fun p => norm_nonneg _
    have houter : 0 ≤ gout x := by dsimp [gout]; positivity
    have hboundG : (∫ p : ℝ × ℝ, ‖g (x, p)‖) ≤ gout x := by
      calc
        _ = ∫ p : ℝ × ℝ, ‖fW p.1 * fZ x p.2‖ := by
          apply integral_congr_ae
          filter_upwards [] with p
          simp [g, fW, fZ, mul_comm]
        _ ≤ _ := by simpa [gout] using hsectionBound x
    have hnormBound :
        ‖∫ p : ℝ × ℝ, ‖g (x, p)‖‖ ≤ gout x := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      exact hboundG
    exact hnormBound
  exact (integrable_prod_iff hGmeas).2
    ⟨ae_of_all _ (fun x => by simpa [g, mul_comm] using hsection x), hnormFunction⟩

private theorem rows_small_kernel_line_continuous (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 0 < Z) (u : U.U) (hu : u ≠ U.one)
    (σξ σw σz : ℝ)
    (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4)
    (hwlo : 3 / 1000 ≤ σw) (hwhi : σw ≤ 4)
    (hzlo : 4 / 10 ≤ σz) (hzhi : σz ≤ 2) :
    Continuous (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel R sd W η U HA HC u Z
        (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I)) := by
  let ξp : ℝ × (ℝ × ℝ) → ℂ := fun p => σξ + p.1 * Complex.I
  let wp : ℝ × (ℝ × ℝ) → ℂ := fun p => σw + p.2.1 * Complex.I
  let zp : ℝ × (ℝ × ℝ) → ℂ := fun p => σz + p.2.2 * Complex.I
  have hξcont : Continuous ξp := by fun_prop
  have hwcont : Continuous wp := by fun_prop
  have hzcont : Continuous zp := by fun_prop
  have hξre (p : ℝ × (ℝ × ℝ)) : (ξp p).re = σξ := by simp [ξp]
  have hwre (p : ℝ × (ℝ × ℝ)) : (wp p).re = σw := by simp [wp]
  have hzre (p : ℝ × (ℝ × ℝ)) : (zp p).re = σz := by simp [zp]
  obtain ⟨hMdiff, hWdiff, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hMlineOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => weightM R sd W (zp p)) Set.univ := by
    apply hMdiff.continuousOn.comp hzcont.continuousOn
    intro p hp
    change 0 < (zp p).re
    rw [hzre]
    exact lt_of_lt_of_le (by norm_num) hzlo
  have hMline : Continuous (fun p : ℝ × (ℝ × ℝ) => weightM R sd W (zp p)) :=
    continuousOn_univ.mp hMlineOn
  have hWline : Continuous (fun p : ℝ × (ℝ × ℝ) => weightW1hat W (wp p)) :=
    hWdiff.continuous.comp hwcont
  have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ a))
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ b))
  have hMellin : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξp p) (wp p) (zp p)) := by
    unfold mellinWeight
    have hXexp : Continuous (fun p : ℝ × (ℝ × ℝ) => (1 / 2 : ℂ) - zp p) := by fun_prop
    have hZexp : Continuous (fun p : ℝ × (ℝ × ℝ) => ξp p + zp p - 1) := by fun_prop
    have hYexp : Continuous (fun p : ℝ × (ℝ × ℝ) => wp p - 1) := by fun_prop
    have hX : Continuous (fun p => ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - zp p)) := by
      exact hXexp.const_cpow (Or.inl hXbase)
    have hZ : Continuous (fun p => (Z : ℂ) ^ (ξp p + zp p - 1)) := by
      exact hZexp.const_cpow (Or.inl hZbase)
    have hY : Continuous (fun p => ((Z ^ b : ℝ) : ℂ) ^ (wp p - 1)) := by
      exact hYexp.const_cpow (Or.inl hYbase)
    have hG : Continuous (fun p => Complex.exp ((ξp p + zp p - 1) ^ 2)) := by fun_prop
    exact (((((hX.mul hZ).mul hY).mul hG).mul hMline).mul hWline)
  have hKfin : IsOfFinOrder (U.kummer u) := rows_kummer_finiteOrder R η U hEuler u
  have hKne : U.kummer u ≠ 1 := by
    intro h
    exact hu ((U.kummer_principal_iff u).mp h)
  have hKdiff : Differentiable ℂ (HA.LS S (U.kummer u)) :=
    rows_small_LS_differentiable (HA := HA) (S := S) (U.kummer u) hKfin hKne
  have hKline : Continuous (fun p : ℝ × (ℝ × ℝ) => HA.LS S (U.kummer u) (wp p)) :=
    hKdiff.continuous.comp hwcont
  have hLzDiff : DifferentiableOn ℂ (HA.LS S (1 : HeckeChar F)) {s | 1 < s.re} :=
    rows_LS_trivial_differentiableOn HA S
  let zsix : ℝ × (ℝ × ℝ) → ℂ := fun p => 6 * zp p
  have hzsixCont : Continuous zsix := by fun_prop
  have hzsixMaps : MapsTo zsix Set.univ {s | 1 < s.re} := by
    intro p hp
    change 1 < (6 * zp p).re
    rw [show (6 * zp p).re = 6 * (zp p).re by simp, hzre]
    nlinarith [hzlo]
  have hLzOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (zsix p)) Set.univ := by
    apply hLzDiff.continuousOn.comp hzsixCont.continuousOn
    exact hzsixMaps
  have hLzline : Continuous (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (zsix p)) :=
    continuousOn_univ.mp hLzOn
  have htw : rowTwist η U u = U.omega u := by
    simpa [rowTwist] using (U.omega_induces_twist u).symm
  have htwfin : IsOfFinOrder (rowTwist η U u) := by rw [htw]; exact U.omega_finiteOrder u
  obtain ⟨fω, hfω⟩ := U.omega_primitive u
  have htwprim : IsPrimitiveConductor (rowTwist η U u) fω := by rw [htw]; exact hfω
  have hInvDiff : DifferentiableOn ℂ (HA.LS S (rowTwist η U u)) {s | 1 < s.re} :=
    rows_small_LS_differentiableOn (HA := HA) (S := S) (rowTwist η U u) htwfin
  have hInvNe : ∀ s, 1 < s.re → HA.LS S (rowTwist η U u) s ≠ 0 := by
    intro s hs
    exact (rows_LS_inverse_bound HA S (rowTwist η U u) htwfin fω htwprim hs).1
  have hInvOn : DifferentiableOn ℂ
      (fun s => (HA.LS S (rowTwist η U u) s)⁻¹) {s | 1 < s.re} := by
    apply hInvDiff.inv
    intro s hs
    exact hInvNe s hs
  have hξMaps : MapsTo ξp Set.univ {s | 1 < s.re} := by
    intro p hp
    change 1 < (ξp p).re
    rw [hξre]
    have hδ : 0 < δ1 := by norm_num [δ1]
    linarith [hξlo]
  have hInvOnLine : ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) => (HA.LS S (rowTwist η U u) (ξp p))⁻¹) Set.univ := by
    apply hInvOn.continuousOn.comp hξcont.continuousOn
    exact hξMaps
  have hInvLine : Continuous
      (fun p : ℝ × (ℝ × ℝ) => (HA.LS S (rowTwist η U u) (ξp p))⁻¹) :=
    continuousOn_univ.mp hInvOnLine
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℝ × (ℝ × ℝ) → Triple := fun p => ![ξp p, wp p, zp p]
  have hpmap : Continuous pmap := by fun_prop
  have hMaps : MapsTo pmap Set.univ {p | eulerNeighborhood p} := by
    intro p hp
    left
    change (998 / 1000 - 1 / 100000 < (ξp p).re ∧
      3 / 1000 - 1 / 100000 < (wp p).re ∧ 4 / 10 - 1 / 100000 < (zp p).re)
    refine ⟨?_, ?_, ?_⟩
    · rw [hξre]
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith [hξlo]
    · rw [hwre]
      linarith [hwlo]
    · rw [hzre]
      linarith [hzlo]
  have hHCOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => HC.H u (pmap p)) Set.univ := by
    apply (hHP.2.1 u).continuousOn.comp hpmap.continuousOn
    exact hMaps
  have hHCline : Continuous (fun p : ℝ × (ℝ × ℝ) => HC.H u ![ξp p, wp p, zp p]) := by
    have h := continuousOn_univ.mp hHCOn
    simpa [pmap] using h
  have hqbase : (U.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (U.q_pos u))
  have hqexp : Continuous (fun p : ℝ × (ℝ × ℝ) => -zp p) := by fun_prop
  have hqline : Continuous (fun p : ℝ × (ℝ × ℝ) => (U.q u : ℂ) ^ (-zp p)) := by
    exact hqexp.const_cpow (Or.inl hqbase)
  change Continuous (fun p : ℝ × (ℝ × ℝ) =>
    (mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξp p) (wp p) (zp p) *
      (U.q u : ℂ) ^ (-zp p) * HA.LS S 1 (zsix p) * HA.LS S (U.kummer u) (wp p) *
        HC.H u ![ξp p, wp p, zp p]) / HA.LS S (rowTwist η U u) (ξp p))
  simp only [div_eq_mul_inv]
  have h₁ := hMellin.mul hqline
  have h₂ := h₁.mul hLzline
  have h₃ := h₂.mul hKline
  have h₄ := h₃.mul hHCline
  exact h₄.mul hInvLine

set_option maxHeartbeats 2000000 in
private theorem rows_small_kernel_sum_integrable (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) (Z : ℝ) (hZ : 2 ≤ Z) (rows : Finset U.U)
    (huRows : ∀ u ∈ rows, u ≠ U.one)
    (σξ σw σz : ℝ)
    (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4)
    (hwlo : 3 / 1000 ≤ σw) (hwhi : σw ≤ 4)
    (hzlo : 4 / 10 ≤ σz) (hzhi : σz ≤ 2) :
    Integrable
      (fun p : ℝ × (ℝ × ℝ) =>
        ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z
          (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I))
      (volume.prod (volume.prod volume)) := by
  obtain ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, hAeq, hAdecPos,
      hC0, hCconv, hconv, hkernel⟩ :=
    rows_small_kernel_control R sd W η U HA HC hEuler ε hε
  have hmajor := rows_small_real_majorant_integrable Aconv Cconv hAconv hCconv hconv
  let M : ℝ := ∑ u ∈ rows,
    C0 * Z ^ Estar σξ σw σz * (U.q u) ^ (1 / 10 + ε)
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg
      (mul_nonneg hC0.le (Real.rpow_nonneg (by linarith : 0 ≤ Z) _))
      (Real.rpow_nonneg (le_of_lt (U.q_pos u)) _)
  let f : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z
      (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I)
  have hfcont : Continuous f := by
    dsimp [f]
    classical
    exact continuous_finsetSum rows fun u hu =>
      rows_small_kernel_line_continuous R sd W η U HA HC hEuler Z (by linarith)
        u (huRows u hu) σξ σw σz hξlo hξhi hwlo hwhi hzlo hzhi
  have hpoint (p : ℝ × (ℝ × ℝ)) : ‖f p‖ ≤ M *
      (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ)) := by
    let ξ : ℂ := σξ + p.1 * Complex.I
    let w : ℂ := σw + p.2.1 * Complex.I
    let z : ℂ := σz + p.2.2 * Complex.I
    have hξre : ξ.re = σξ := by simp [ξ]
    have hwre : w.re = σw := by simp [w]
    have hzre : z.re = σz := by simp [z]
    have hξim : ξ.im = p.1 := by simp [ξ]
    have hwim : w.im = p.2.1 := by simp [w]
    have hzim : z.im = p.2.2 := by simp [z]
    have hsumNorm := norm_sum_le rows
      (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hsumBound : (∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖) ≤
        ∑ u ∈ rows, C0 * Z ^ Estar σξ σw σz * (U.q u) ^ (1 / 10 + ε) *
          (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
            (1 + |p.2.1|) ^ (-2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      have h := hkernel Z hZ u (huRows u hu) ξ w z
        (by rw [hξre]; exact hξlo) (by rw [hξre]; exact hξhi)
        (by rw [hwre]; exact hwlo) (by rw [hwre]; exact hwhi)
        (by rw [hzre]; exact hzlo) (by rw [hzre]; exact hzhi)
      simpa [ξ, w, z, hξre, hwre, hzre, hξim, hwim, hzim,
        mul_assoc, mul_left_comm, mul_comm] using h
    have hsumEq :
        (∑ u ∈ rows, C0 * Z ^ Estar σξ σw σz * (U.q u) ^ (1 / 10 + ε) *
          (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
            (1 + |p.2.1|) ^ (-2 : ℝ))) = M *
          (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
            (1 + |p.2.1|) ^ (-2 : ℝ)) := by
      dsimp [M]
      rw [← Finset.sum_mul]
    calc
      ‖f p‖ ≤ ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
        simpa [f] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
  have hdom : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      M * (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ))) (volume.prod (volume.prod volume)) := by
    simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hmajor.const_mul M
  exact hdom.mono' hfcont.aestronglyMeasurable (ae_of_all _ hpoint)

private theorem rows_small_raw_swap_wz (f : ℝ → ℝ → ℂ)
    (hf : Integrable (Function.uncurry f) (volume.prod volume)) :
    ∫ tw : ℝ, ∫ tz : ℝ, f tw tz = ∫ tz : ℝ, ∫ tw : ℝ, f tw tz :=
  integral_integral_swap hf

private theorem rows_small_raw_swap_outer (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))) :
    ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f tξ tw tz =
      ∫ tw : ℝ, ∫ tz : ℝ, ∫ tξ : ℝ, f tξ tw tz := by
  let F : ℝ → (ℝ × ℝ) → ℂ := fun tξ p => f tξ p.1 p.2
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.prod volume)) := by
    change Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))
    exact hf
  have hSections := hF.prod_right_ae
  have hInner :
      (∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f tξ tw tz) =
        ∫ tξ : ℝ, MeasureTheory.integral (volume.prod volume) (fun p : ℝ × ℝ => F tξ p) := by
    apply integral_congr_ae
    filter_upwards [hSections] with tξ hsec
    simpa [F] using (integral_prod (fun p : ℝ × ℝ => F tξ p) hsec).symm
  calc
    _ = ∫ tξ : ℝ, MeasureTheory.integral (volume.prod volume)
        (fun p : ℝ × ℝ => F tξ p) := hInner
    _ = MeasureTheory.integral (volume.prod volume)
        (fun p : ℝ × ℝ => ∫ tξ : ℝ, F tξ p) := integral_integral_swap hF
    _ = ∫ tw : ℝ, ∫ tz : ℝ, ∫ tξ : ℝ, f tξ tw tz := by
      simpa [F] using integral_prod _ hF.integral_prod_right

private theorem rows_small_raw_swap_wz_outer (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))) :
    ∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f tξ tw tz =
      ∫ tξ : ℝ, ∫ tz : ℝ, ∫ tw : ℝ, f tξ tw tz := by
  let F : ℝ → (ℝ × ℝ) → ℂ := fun tξ p => f tξ p.1 p.2
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.prod volume)) := by
    change Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))
    exact hf
  have hSections := hF.prod_right_ae
  apply integral_congr_ae
  filter_upwards [hSections] with tξ hsec
  exact rows_small_raw_swap_wz (fun tw tz => f tξ tw tz) hsec

private theorem rows_small_triple_swap_wz
    (σξ σw σz : ℝ) (f : ℝ → ℝ → ℝ → ℂ)
    (hInt : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))) :
    tripleVertical σξ σw σz
      (fun ξ w z => f ξ.im w.im z.im) =
    tripleVertical σξ σz σw
      (fun ξ z w => f ξ.im w.im z.im) := by
  unfold tripleVertical vertical
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one, integral_const_mul]
  exact congrArg
    (fun q : ℂ => (1 / (2 * Real.pi) : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * q)))
    (rows_small_raw_swap_wz_outer f hInt)

private theorem rows_small_triple_swap_outer
    (σξ σw σz : ℝ) (f : ℝ → ℝ → ℝ → ℂ)
    (hInt : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))) :
    tripleVertical σξ σw σz (fun ξ w z => f ξ.im w.im z.im) =
      vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => f ξ.im w.im z.im))) := by
  unfold tripleVertical vertical
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, zero_add, add_zero, mul_one, integral_const_mul]
  exact congrArg
    (fun q : ℂ => (1 / (2 * Real.pi) : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) * ((1 / (2 * Real.pi) : ℂ) * q)))
    (rows_small_raw_swap_outer f hInt)

set_option maxHeartbeats 1600000 in
private theorem rows_small_shift_z (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) (Z : ℝ) (hZ : 2 ≤ Z) (rows : Finset U.U)
    (huRows : ∀ u ∈ rows, u ≠ U.one) (ξ w : ℂ)
    (hξlo : 1 + δ1 ≤ ξ.re) (hξhi : ξ.re ≤ 4)
    (hw : w.re = 4) :
    vertical 2 (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) =
      vertical (4 / 10) (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) := by
  let strip : Set ℂ := {z | 4 / 10 ≤ z.re ∧ z.re ≤ 2}
  let G : ℂ → ℂ := fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z
  obtain ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, hAeq, hAdecPos,
      hC0, hCconv, hconv, hcontrol⟩ :=
    rows_small_kernel_control R sd W η U HA HC hEuler ε hε
  have hGdiff : DifferentiableOn ℂ G strip := by
    change DifferentiableOn ℂ
      (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) strip
    apply DifferentiableOn.fun_sum
    intro u hu
    have hξhp : 998 / 1000 - 1 / 100000 < ξ.re := by
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith
    have hwhp : 3 / 1000 - 1 / 100000 < w.re := by rw [hw]; norm_num
    exact rows_small_kernel_differentiableOn_z R sd W η U HA HC hEuler
      Z (by positivity) u ξ w hξhp hwhp
  let Cshift : ℝ := ∑ u ∈ rows,
    C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)
  have hCshift : 0 ≤ Cshift := by
    dsimp [Cshift]
    apply Finset.sum_nonneg
    intro u hu
    exact mul_nonneg
      (mul_nonneg hC0.le (Real.rpow_nonneg (by linarith : 0 ≤ Z) _))
      (Real.rpow_nonneg (le_of_lt (U.q_pos u)) _)
  have hline (x : ℝ) (hx : x ∈ Set.Icc (4 / 10 : ℝ) 2) (y : ℝ) :
      ‖G ((x : ℂ) + y * Complex.I)‖ ≤
        Cshift * Real.exp (-((ξ.im + y) ^ 2)) := by
    have hxlo : 4 / 10 ≤ x := hx.1
    have hxhi : x ≤ 2 := hx.2
    let z : ℂ := (x : ℂ) + y * Complex.I
    have hzre : z.re = x := by simp [z]
    have hzim : z.im = y := by simp [z]
    have hEstar : Estar ξ.re w.re z.re ≤ Estar ξ.re 4 2 := by
      rw [hw, hzre]
      norm_num [Estar, a, b, h0]
      nlinarith [hxhi]
    have hZpow : Z ^ Estar ξ.re w.re z.re ≤ Z ^ Estar ξ.re 4 2 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hEstar
    have hpolyZ : (1 + |z.im|) ^ (-Aconv) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg z.im])
        (by linarith [hAconv])
    have hpolyW : (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg w.im]) (by norm_num)
    have hpoly : (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      mul_le_one₀ hpolyZ (Real.rpow_nonneg (by nlinarith [abs_nonneg w.im]) _) hpolyW
    have hcoef (u : U.U) :
        C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) ≤
          C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε) := by
      have hqnon : 0 ≤ (U.q u) ^ (1 / 10 + ε) :=
        Real.rpow_nonneg (U.q_pos u).le _
      calc
        _ = (C0 * Z ^ Estar ξ.re w.re z.re) * (U.q u) ^ (1 / 10 + ε) := by ring
        _ ≤ (C0 * Z ^ Estar ξ.re 4 2) * (U.q u) ^ (1 / 10 + ε) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hZpow hC0.le) hqnon
        _ = _ := by ring
    have hrow (u : U.U) (hu : u ∈ rows) :
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          (C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)) *
            Real.exp (-((ξ.im + y) ^ 2)) := by
      have h := hcontrol Z hZ u (huRows u hu) ξ w z hξlo hξhi
        (by norm_num [hw]) (by norm_num [hw])
        (by rw [hzre]; exact hxlo) (by rw [hzre]; exact hxhi)
      have hcoeffnon : 0 ≤ C0 * Z ^ Estar ξ.re w.re z.re *
          (U.q u) ^ (1 / 10 + ε) := by
        exact mul_nonneg
          (mul_nonneg hC0.le (Real.rpow_nonneg (by linarith : 0 ≤ Z) _))
          (Real.rpow_nonneg (le_of_lt (U.q_pos u)) _)
      have hcoeffgauss : 0 ≤ C0 * Z ^ Estar ξ.re w.re z.re *
          (U.q u) ^ (1 / 10 + ε) * Real.exp (-((ξ.im + y) ^ 2)) :=
        mul_nonneg hcoeffnon (Real.exp_pos _).le
      rw [show Real.exp (-((ξ.im + z.im) ^ 2)) =
        Real.exp (-((ξ.im + y) ^ 2)) by rw [hzim]] at h
      calc
        _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            Real.exp (-((ξ.im + y) ^ 2)) *
              ((1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by
                simpa [mul_assoc, mul_left_comm, mul_comm] using h
        _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            Real.exp (-((ξ.im + y) ^ 2)) * 1 :=
              mul_le_mul_of_nonneg_left hpoly hcoeffgauss
        _ ≤ (C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)) *
            Real.exp (-((ξ.im + y) ^ 2)) := by
              have hExp : 0 ≤ Real.exp (-((ξ.im + y) ^ 2)) := (Real.exp_pos _).le
              calc
                _ = (C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε)) *
                    Real.exp (-((ξ.im + y) ^ 2)) := by ring
                _ ≤ (C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)) *
                    Real.exp (-((ξ.im + y) ^ 2)) :=
                      mul_le_mul_of_nonneg_right (hcoef u) hExp
    have hsumNorm := norm_sum_le rows
      (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hsumBound :
        (∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖) ≤
          ∑ u ∈ rows,
            (C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)) *
              Real.exp (-((ξ.im + y) ^ 2)) :=
      Finset.sum_le_sum fun u hu => hrow u hu
    have hsumEq :
        (∑ u ∈ rows,
          (C0 * Z ^ Estar ξ.re 4 2 * (U.q u) ^ (1 / 10 + ε)) *
            Real.exp (-((ξ.im + y) ^ 2))) = Cshift * Real.exp (-((ξ.im + y) ^ 2)) := by
      dsimp [Cshift]
      rw [← Finset.sum_mul]
    calc
      ‖G ((x : ℂ) + y * Complex.I)‖ ≤
          ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
            simpa [G] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
  let trans : ℂ → ℂ := fun z => z - ξ.im * Complex.I
  let Fcont : ℂ → ℂ := fun z => G (trans z)
  have hTransDiff : Differentiable ℂ trans := by fun_prop
  have hTransOn : DifferentiableOn ℂ trans strip := hTransDiff.differentiableOn
  have hTransMaps : MapsTo trans strip strip := by
    intro z hz
    have hreal : (trans z).re = z.re := by simp [trans]
    constructor
    · rw [hreal]
      exact hz.1
    · rw [hreal]
      exact hz.2
  have hFdiff : DifferentiableOn ℂ Fcont strip := by
    have h := hGdiff.comp hTransOn hTransMaps
    simpa only [Fcont, Function.comp_def] using h
  have hFbound : ∀ x ∈ Set.Icc (4 / 10 : ℝ) 2, ∀ y : ℝ,
      ‖Fcont ((x : ℂ) + y * Complex.I)‖ ≤ Cshift * Real.exp (-y ^ 2) := by
    intro x hx y
    have hz : trans ((x : ℂ) + y * Complex.I) = (x : ℂ) + (y - ξ.im) * Complex.I := by
      dsimp [trans]
      apply Complex.ext <;> simp <;> ring
    have h := hline x hx (y - ξ.im)
    change ‖G (trans ((x : ℂ) + y * Complex.I))‖ ≤ Cshift * Real.exp (-y ^ 2)
    rw [hz]
    rw [Complex.ofReal_sub] at h
    have hy : ξ.im + (y - ξ.im) = y := by ring
    rw [hy] at h
    exact h
  have hcontour := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    Fcont (a := 4 / 10) (b := 2) (C := Cshift) (by norm_num) hFdiff hFbound
  have htranslate (σ : ℝ) :
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
    have hcomp : (∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) (-ξ.im)).integral_comp
        (Homeomorph.addLeft (-ξ.im)).measurableEmbedding
        (fun t : ℝ => G ((σ : ℂ) + t * Complex.I))
      simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have harg (t : ℝ) :
        ((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I =
          (σ : ℂ) + (t - ξ.im) * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    calc
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
          ∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change G (((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I) =
          G ((σ : ℂ) + (t - ξ.im) * Complex.I)
        rw [harg]
      _ = ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := hcomp
  have hshiftV : vertical (4 / 10) Fcont = vertical 2 Fcont := by
    unfold vertical
    rw [hcontour]
  calc
    vertical 2 G = vertical 2 Fcont := by
      unfold vertical
      rw [← htranslate 2]
    _ = vertical (4 / 10) Fcont := hshiftV.symm
    _ = vertical (4 / 10) G := by
      unfold vertical
      rw [htranslate (4 / 10)]


set_option maxHeartbeats 4000000 in
private theorem rows_small_shift_w (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) (Z : ℝ) (hZ : 2 ≤ Z) (rows : Finset U.U)
    (huRows : ∀ u ∈ rows, u ≠ U.one) (ξ z : ℂ)
    (hξlo : 1 + δ1 ≤ ξ.re) (hξhi : ξ.re ≤ 4)
    (hz : z.re = 4 / 10) :
    vertical 4 (fun w => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) =
      vertical (3 / 1000) (fun w => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) := by
  let strip : Set ℂ := {w | 3 / 1000 ≤ w.re ∧ w.re ≤ 4}
  let G : ℂ → ℂ := fun w => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z
  obtain ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, hAeq, hAdecPos,
      hC0, hCconv, hconv, hcontrol⟩ := rows_small_kernel_control R sd W η U HA HC hEuler ε hε
  have hGdiff : DifferentiableOn ℂ G strip := by
    change DifferentiableOn ℂ
      (fun w => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) strip
    apply DifferentiableOn.fun_sum
    intro u hu
    have hξhp : 998 / 1000 - 1 / 100000 < ξ.re := by
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith
    have hzhp : 4 / 10 - 1 / 100000 < z.re := by rw [hz]; norm_num
    exact rows_small_kernel_differentiableOn_w R sd W η U HA HC hEuler
      Z (by positivity) u ξ z (huRows u hu) hξhp hzhp
  let Cshift : ℝ := ∑ u ∈ rows,
    C0 * Z ^ Estar ξ.re 4 z.re * (U.q u) ^ (1 / 10 + ε) *
      Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv)
  have hCshift : 0 ≤ Cshift := by
    dsimp [Cshift]
    apply Finset.sum_nonneg
    intro u hu
    have hcoef : 0 ≤ C0 * Z ^ Estar ξ.re 4 z.re * (U.q u) ^ (1 / 10 + ε) :=
      mul_nonneg
        (mul_nonneg hC0.le (Real.rpow_nonneg (by linarith : 0 ≤ Z) _))
        (Real.rpow_nonneg (le_of_lt (U.q_pos u)) _)
    exact mul_nonneg
      (mul_nonneg hcoef (Real.exp_pos _).le)
      (Real.rpow_nonneg (by positivity) _)
  have hline (x : ℝ) (hx : x ∈ Set.Icc (3 / 1000 : ℝ) 4) (t : ℝ) :
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤ Cshift * (1 + |t|) ^ (-2 : ℝ) := by
    have hxlo : 3 / 1000 ≤ x := hx.1
    have hxhi : x ≤ 4 := hx.2
    let w : ℂ := (x : ℂ) + t * Complex.I
    have hwre : w.re = x := by simp [w]
    have hwim : w.im = t := by simp [w]
    have hEstar : Estar ξ.re w.re z.re ≤ Estar ξ.re 4 z.re := by
      rw [hwre]
      norm_num [Estar, a, b, h0]
      nlinarith [hxhi]
    have hZpow : Z ^ Estar ξ.re w.re z.re ≤ Z ^ Estar ξ.re 4 z.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hEstar
    have hcoef (u : U.U) :
        C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) ≤
        C0 * Z ^ Estar ξ.re 4 z.re * (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) := by
      have hrest : 0 ≤ (U.q u) ^ (1 / 10 + ε) *
          Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv) := by
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (U.q_pos u).le _) (Real.exp_pos _).le)
          (Real.rpow_nonneg (by positivity) _)
      calc
        _ = (C0 * Z ^ Estar ξ.re w.re z.re) *
            ((U.q u) ^ (1 / 10 + ε) * Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Aconv)) := by ring
        _ ≤ (C0 * Z ^ Estar ξ.re 4 z.re) *
            ((U.q u) ^ (1 / 10 + ε) * Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Aconv)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hZpow hC0.le) hrest
        _ = _ := by ring
    have hsumNorm := norm_sum_le rows
      (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hsumBound :
        (∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖) ≤
          ∑ u ∈ rows,
            (C0 * Z ^ Estar ξ.re 4 z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv)) *
              (1 + |t|) ^ (-2 : ℝ) := by
      exact Finset.sum_le_sum fun u hu => by
        have h := hcontrol Z hZ u (huRows u hu) ξ w z hξlo hξhi
          (by rw [hwre]; exact hxlo) (by rw [hwre]; exact hxhi)
          (by norm_num [hz]) (by norm_num [hz])
        rw [hwim] at h
        calc
          _ ≤ (C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv)) *
                (1 + |t|) ^ (-2 : ℝ) := by simpa [mul_assoc] using h
          _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef u) (Real.rpow_nonneg (by positivity) _)
    have hsumEq :
        (∑ u ∈ rows,
          (C0 * Z ^ Estar ξ.re 4 z.re * (U.q u) ^ (1 / 10 + ε) *
            Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Aconv)) *
              (1 + |t|) ^ (-2 : ℝ)) = Cshift * (1 + |t|) ^ (-2 : ℝ) := by
      dsimp [Cshift]
      rw [← Finset.sum_mul]
    calc
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤
          ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
            simpa [G] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
  let E : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  have hEint : Integrable E := by
    simpa [E] using rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hEven : ∀ t : ℝ, E (-t) = E t := by intro t; simp [E, abs_neg]
  have hineq : ∀ t : ℝ, t ≤ 1 + |t| := by
    intro t
    calc
      t ≤ |t| := le_abs_self _
      _ ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hBase : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop :=
    tendsto_atTop_mono hineq tendsto_id
  have hLim : Tendsto E atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp hBase
    have hpow' : Tendsto (fun t : ℝ => ((1 + |t|) ^ (2 : ℝ))⁻¹) atTop (𝓝 0) := by
      convert hpow using 1
      funext t
      change ((1 + |t|) ^ (2 : ℝ))⁻¹ = (1 + |t|) ^ (-(2 : ℝ))
      exact (Real.rpow_neg (by positivity : 0 ≤ 1 + |t|) (2 : ℝ)).symm
    have hEq : (fun t : ℝ => E t) = fun t => ((1 + |t|) ^ (2 : ℝ))⁻¹ := by
      funext t
      dsimp [E]
      rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |t|)]
    change Tendsto (fun t : ℝ => E t) atTop (𝓝 0)
    rw [hEq]
    exact hpow'
  have hab : (3 / 1000 : ℝ) ≤ 4 := by norm_num
  have hLineContinuous (x : ℝ) (hx : x ∈ Set.Icc (3 / 1000 : ℝ) 4) :
      Continuous (fun t : ℝ => G ((x : ℂ) + t * Complex.I)) := by
    apply continuousOn_univ.mp
    apply hGdiff.continuousOn.comp
      (by fun_prop : ContinuousOn (fun t : ℝ => (x : ℂ) + t * Complex.I) Set.univ)
    intro t ht
    have hre : ((x : ℂ) + t * Complex.I).re = x := by simp
    change 3 / 1000 ≤ ((x : ℂ) + t * Complex.I).re ∧
      ((x : ℂ) + t * Complex.I).re ≤ 4
    rw [hre]
    exact hx
  have hEndpoint (x : ℝ) (hx : x ∈ Set.Icc (3 / 1000 : ℝ) 4) :
      Integrable (fun t : ℝ => G ((x : ℂ) + t * Complex.I)) := by
    apply (hEint.const_mul Cshift).mono' (hLineContinuous x hx).aestronglyMeasurable
    filter_upwards [] with t
    exact hline x hx t
  have hIntervalBound (T : ℝ) :
      ‖∫ x in (3 / 1000)..4, G ((x : ℂ) + T * Complex.I)‖ ≤
        Cshift * E T * |4 - 3 / 1000| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (3 / 1000 : ℝ) 4 := by
      simpa [uIcc_of_le hab] using uIoc_subset_uIcc hx
    exact hline x hx' T
  have hTop : Tendsto
      (fun T : ℝ => ∫ x in (3 / 1000)..4, G ((x : ℂ) + T * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hIntervalBound
      (by simpa [E] using (hLim.const_mul Cshift).mul_const |4 - 3 / 1000|)
  have hBottom : Tendsto
      (fun T : ℝ => ∫ x in (3 / 1000)..4, G ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hbound (T : ℝ) :
        ‖∫ x in (3 / 1000)..4, G ((x : ℂ) + (-T) * Complex.I)‖ ≤
          Cshift * E T * |4 - 3 / 1000| := by
      calc
        _ ≤ Cshift * E (-T) * |4 - 3 / 1000| := by
          simpa [Complex.ofReal_neg] using hIntervalBound (-T)
        _ = _ := by rw [hEven]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound
      (by simpa [E] using (hLim.const_mul Cshift).mul_const |4 - 3 / 1000|)
  have hshift := OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish
    G hab hGdiff (hEndpoint (3 / 1000) ⟨le_rfl, by norm_num⟩)
    (hEndpoint 4 ⟨by norm_num, le_rfl⟩) hBottom hTop
  unfold vertical
  exact congrArg (fun v : ℂ => (1 / (2 * Real.pi) : ℂ) * v) hshift.symm

private theorem rows_small_shift_xi (hEuler : EulerHypotheses R η)
    (ε : ℝ) (hε : 0 < ε) (Z : ℝ) (hZ : 2 ≤ Z) (rows : Finset U.U)
    (huRows : ∀ u ∈ rows, u ≠ U.one) (w z : ℂ)
    (hw : w.re = 3 / 1000) (hz : z.re = 4 / 10) :
    vertical 4 (fun ξ => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) =
      vertical (1 + δ1) (fun ξ => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) := by
  let strip : Set ℂ := {ξ | 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4}
  let G : ℂ → ℂ := fun ξ => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z
  obtain ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, hAeq, hAdecPos,
      hC0, hCconv, hconv, hcontrol⟩ := rows_small_kernel_control R sd W η U HA HC hEuler ε hε
  have hGdiff : DifferentiableOn ℂ G strip := by
    change DifferentiableOn ℂ
      (fun ξ => ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z) strip
    apply DifferentiableOn.fun_sum
    intro u hu
    have hwhp : 3 / 1000 - 1 / 100000 < w.re := by rw [hw]; norm_num
    have hzhp : 4 / 10 - 1 / 100000 < z.re := by rw [hz]; norm_num
    exact rows_small_kernel_differentiableOn_xi R sd W η U HA HC hEuler
      Z (by positivity) u w z hwhp hzhp
  let Cshift : ℝ := ∑ u ∈ rows,
    C0 * Z ^ Estar 4 w.re z.re * (U.q u) ^ (1 / 10 + ε) *
      (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)
  have hCshift : 0 ≤ Cshift := by
    dsimp [Cshift]
    apply Finset.sum_nonneg
    intro u hu
    have hCZ : 0 ≤ C0 * Z ^ Estar 4 w.re z.re :=
      mul_nonneg hC0.le (Real.rpow_nonneg (by linarith : 0 ≤ Z) _)
    have hq : 0 ≤ (U.q u) ^ (1 / 10 + ε) :=
      Real.rpow_nonneg (le_of_lt (U.q_pos u)) _
    have hpz : 0 ≤ (1 + |z.im|) ^ (-Aconv) :=
      Real.rpow_nonneg (by positivity) _
    have hpw : 0 ≤ (1 + |w.im|) ^ (-2 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_nonneg (mul_nonneg (mul_nonneg hCZ hq) hpz) hpw
  have hline (x : ℝ) (hx : x ∈ Set.Icc (1 + δ1 : ℝ) 4) (t : ℝ) :
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤
        Cshift * Real.exp (-((t + z.im) ^ 2)) := by
    have hxlo : 1 + δ1 ≤ x := hx.1
    have hxhi : x ≤ 4 := hx.2
    let ξ : ℂ := (x : ℂ) + t * Complex.I
    have hξre : ξ.re = x := by simp [ξ]
    have hξim : ξ.im = t := by simp [ξ]
    have hEstar : Estar ξ.re w.re z.re ≤ Estar 4 w.re z.re := by
      rw [hξre]
      norm_num [Estar, a, b, h0]
      nlinarith [hxhi]
    have hZpow : Z ^ Estar ξ.re w.re z.re ≤ Z ^ Estar 4 w.re z.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hEstar
    have hcoef (u : U.U) :
        C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) ≤
        C0 * Z ^ Estar 4 w.re z.re * (U.q u) ^ (1 / 10 + ε) *
          (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
      have hrest : 0 ≤ (U.q u) ^ (1 / 10 + ε) *
          (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) :=
        mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (U.q_pos u).le _) (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _)
      calc
        _ = (C0 * Z ^ Estar ξ.re w.re z.re) *
            ((U.q u) ^ (1 / 10 + ε) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by ring
        _ ≤ (C0 * Z ^ Estar 4 w.re z.re) *
            ((U.q u) ^ (1 / 10 + ε) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hZpow hC0.le) hrest
        _ = _ := by ring
    have hrow (u : U.U) (hu : u ∈ rows) :
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          (C0 * Z ^ Estar 4 w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) *
              Real.exp (-((t + z.im) ^ 2)) := by
      have h := hcontrol Z hZ u (huRows u hu) ξ w z
        (by rw [hξre]; exact hxlo) (by rw [hξre]; exact hxhi)
        (by norm_num [hw]) (by norm_num [hw])
        (by norm_num [hz]) (by norm_num [hz])
      rw [hξim] at h
      calc
        _ ≤ C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            Real.exp (-((t + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
                simpa [mul_assoc] using h
        _ = (C0 * Z ^ Estar ξ.re w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) *
              Real.exp (-((t + z.im) ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hcoef u) (Real.exp_pos _).le
    have hsumNorm := norm_sum_le rows
      (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hsumBound :
        (∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖) ≤
          ∑ u ∈ rows,
            (C0 * Z ^ Estar 4 w.re z.re * (U.q u) ^ (1 / 10 + ε) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) *
                Real.exp (-((t + z.im) ^ 2)) :=
      Finset.sum_le_sum fun u hu => hrow u hu
    have hsumEq :
        (∑ u ∈ rows,
          (C0 * Z ^ Estar 4 w.re z.re * (U.q u) ^ (1 / 10 + ε) *
            (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) *
              Real.exp (-((t + z.im) ^ 2))) =
          Cshift * Real.exp (-((t + z.im) ^ 2)) := by
      dsimp [Cshift]
      rw [← Finset.sum_mul]
    calc
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤
          ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
            simpa [G] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
  let trans : ℂ → ℂ := fun ξ => ξ - z.im * Complex.I
  let Fcont : ℂ → ℂ := fun ξ => G (trans ξ)
  have hTransDiff : Differentiable ℂ trans := by fun_prop
  have hTransOn : DifferentiableOn ℂ trans strip := hTransDiff.differentiableOn
  have hTransMaps : MapsTo trans strip strip := by
    intro ξ hξ
    change 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4 at hξ
    have hreal : (trans ξ).re = ξ.re := by simp [trans]
    constructor
    · rw [hreal]
      exact hξ.1
    · rw [hreal]
      exact hξ.2
  have hFdiff : DifferentiableOn ℂ Fcont strip := by
    have h := hGdiff.comp hTransOn hTransMaps
    simpa only [Fcont, Function.comp_def] using h
  have hFbound : ∀ x ∈ Set.Icc (1 + δ1 : ℝ) 4, ∀ y : ℝ,
      ‖Fcont ((x : ℂ) + y * Complex.I)‖ ≤ Cshift * Real.exp (-y ^ 2) := by
    intro x hx y
    have harg : trans ((x : ℂ) + y * Complex.I) =
        (x : ℂ) + (y - z.im) * Complex.I := by
      dsimp [trans]
      apply Complex.ext <;> simp <;> ring
    have h := hline x hx (y - z.im)
    change ‖G (trans ((x : ℂ) + y * Complex.I))‖ ≤ Cshift * Real.exp (-y ^ 2)
    rw [harg]
    rw [Complex.ofReal_sub] at h
    have hy : (y - z.im) + z.im = y := by ring
    rw [hy] at h
    exact h
  have hcontour := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    Fcont (a := 1 + δ1) (b := 4) (C := Cshift) (by norm_num [δ1]) hFdiff hFbound
  have htranslate (σ : ℝ) :
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
    have hcomp : (∫ t : ℝ, G ((σ : ℂ) + (t - z.im) * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) (-z.im)).integral_comp
        (Homeomorph.addLeft (-z.im)).measurableEmbedding
        (fun t : ℝ => G ((σ : ℂ) + t * Complex.I))
      simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have harg (t : ℝ) :
        ((σ : ℂ) + t * Complex.I) - z.im * Complex.I =
          (σ : ℂ) + (t - z.im) * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    calc
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
          ∫ t : ℝ, G ((σ : ℂ) + (t - z.im) * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change G (((σ : ℂ) + t * Complex.I) - z.im * Complex.I) =
          G ((σ : ℂ) + (t - z.im) * Complex.I)
        rw [harg]
      _ = ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := hcomp
  have hshiftV : vertical (1 + δ1) Fcont = vertical 4 Fcont := by
    unfold vertical
    rw [hcontour]
  calc
    vertical 4 G = vertical 4 Fcont := by
      unfold vertical
      rw [← htranslate 4]
    _ = vertical (1 + δ1) Fcont := hshiftV.symm
    _ = vertical (1 + δ1) G := by
      unfold vertical
      rw [htranslate (1 + δ1)]

private theorem rows_heckeLSeries_one_eq_dedekindZeta (s : ℂ) (hs : 1 < s.re) :
    heckeLSeries (1 : HeckeChar F) s = NumberField.dedekindZeta F s := by
  classical
  let Ideals := {I : Ideal (𝓞 F) // I ≠ ⊥}
  let norm : Ideals → ℕ := fun I => Ideal.absNorm I.1
  let fiber : ℕ → Type := fun n => {I : Ideals // norm I = n}
  have hfiberFinite (n : ℕ) : Finite (fiber n) := by
    let full : Type := {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
    letI : Finite full := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
    apply Finite.of_injective (fun I : fiber n => (⟨I.1.1, I.2⟩ : full))
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun X : full => X.1) h
  letI (n : ℕ) : Fintype (fiber n) := by
    classical
    by_cases hn : n = 0
    · subst n
      letI : IsEmpty (fiber 0) := ⟨fun I => by
        have hnorm : Ideal.absNorm I.1.1 = 0 := by simpa [norm] using I.2
        exact I.1.2 (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
      exact Fintype.ofIsEmpty
    · let full : Type := {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
      letI : Fintype full := (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).fintype
      have hnot (I : Ideal (𝓞 F)) (hI : Ideal.absNorm I = n) : I ≠ ⊥ := by
        intro hbot
        apply hn
        exact (by simpa [hbot] using hI.symm)
      let e : fiber n ≃ full := {
        toFun := fun I => ⟨I.1.1, I.2⟩
        invFun := fun I => ⟨⟨I.1, hnot I.1 I.2⟩, by simpa [norm] using I.2⟩
        left_inv := by
          intro I
          cases I with
          | mk I hI => cases I with | mk I hI' => rfl
        right_inv := by intro I; cases I; rfl
      }
      exact Fintype.ofEquiv full e.symm
  have hFiberCard (n : ℕ) (hn : n ≠ 0) : Fintype.card (fiber n) =
      rows_small_idealCount (F := F) n := by
    let full : Type := {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
    have hnot (I : Ideal (𝓞 F)) (hI : Ideal.absNorm I = n) : I ≠ ⊥ := by
      intro hbot
      apply hn
      exact (by simpa [hbot] using hI.symm)
    let e : fiber n ≃ full := {
      toFun := fun I => ⟨I.1.1, I.2⟩
      invFun := fun I => ⟨⟨I.1, hnot I.1 I.2⟩, by simpa [norm] using I.2⟩
      left_inv := by
        intro I
        cases I with
        | mk I hI => cases I with | mk I hI' => rfl
      right_inv := by intro I; cases I; rfl
    }
    simpa [rows_small_idealCount, full] using (Nat.card_congr e)
  have hzero : s ≠ 0 := by
    intro hz
    have hRe := congrArg Complex.re hz
    simp at hRe
    linarith
  have hFiberSumNorm (n : ℕ) :
      (∑' I : fiber n, ‖(n : ℂ) ^ (-s)‖) =
        ‖LSeries.term (fun k => (rows_small_idealCount (F := F) k : ℂ)) s n‖ := by
    by_cases hn : n = 0
    · subst n
      letI : IsEmpty (fiber 0) := ⟨fun I => by
        have hnorm : Ideal.absNorm I.1.1 = 0 := by simpa [norm] using I.2
        exact I.1.2 (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
      simp [LSeries.term]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hpow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
        rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hnpos)]
        rfl
      have hrpow : (n : ℝ) ^ (-s.re) = ((n : ℝ) ^ s.re)⁻¹ :=
        Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) s.re
      rw [tsum_fintype]
      calc
        _ = (Fintype.card (fiber n) : ℝ) * ‖(n : ℂ) ^ (-s)‖ := by simp
        _ = ‖LSeries.term (fun k => (rows_small_idealCount (F := F) k : ℂ)) s n‖ := by
          rw [hFiberCard n hn, hpow, hrpow, LSeries.norm_term_eq]
          simp only [hn, ↓reduceIte, Complex.norm_natCast]
          rw [div_eq_mul_inv]
  have houter : Summable (fun n : ℕ => ∑' I : fiber n, ‖(n : ℂ) ^ (-s)‖) := by
    have hcoeff := (rows_small_idealCount_summable (F := F) (s := s) hs).norm
    exact hcoeff.congr fun n => (hFiberSumNorm n).symm
  have hSigmaNorm : Summable (fun p : Σ n : ℕ, fiber n =>
      ‖(p.1 : ℂ) ^ (-s)‖) := by
    apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · exact houter
  have hSigma : Summable (fun p : Σ n : ℕ, fiber n => (p.1 : ℂ) ^ (-s)) :=
    Summable.of_norm hSigmaNorm
  have hFiberSum (n : ℕ) :
      (∑' I : fiber n, (n : ℂ) ^ (-s)) =
        (rows_small_idealCount (F := F) n : ℂ) * (n : ℂ) ^ (-s) := by
    by_cases hn : n = 0
    · subst n
      letI : IsEmpty (fiber 0) := ⟨fun I => by
        have hnorm : Ideal.absNorm I.1.1 = 0 := by simpa [norm] using I.2
        exact I.1.2 (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩
      simp [hzero]
    · rw [tsum_fintype]
      have hcard : (Fintype.card (fiber n) : ℂ) =
          (rows_small_idealCount (F := F) n : ℂ) := by
        exact_mod_cast hFiberCard n hn
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  have hSigmaTsum :
      (∑' p : Σ n : ℕ, fiber n, (p.1 : ℂ) ^ (-s)) =
        ∑' n : ℕ, (rows_small_idealCount (F := F) n : ℂ) * (n : ℂ) ^ (-s) := by
    calc
      _ = ∑' n : ℕ, ∑' I : fiber n, (n : ℂ) ^ (-s) := hSigma.tsum_sigma
      _ = _ := by
        apply tsum_congr
        intro n
        exact hFiberSum n
  have hReindex :
      (∑' p : Σ n : ℕ, fiber n, (p.1 : ℂ) ^ (-s)) =
        ∑' I : Ideals, (norm I : ℂ) ^ (-s) := by
    let e : (Σ n : ℕ, fiber n) ≃ Ideals := Equiv.sigmaFiberEquiv norm
    have h := e.tsum_eq (fun I : Ideals => (norm I : ℂ) ^ (-s))
    calc
      _ = ∑' p : Σ n : ℕ, fiber n, (norm (e p) : ℂ) ^ (-s) := by
        apply tsum_congr
        intro p
        have hn : norm (e p) = p.1 := by
          change Ideal.absNorm (p.2.1.1) = p.1
          exact p.2.2
        rw [hn]
      _ = _ := h
  have hZeta : NumberField.dedekindZeta F s =
      ∑' n : ℕ, (rows_small_idealCount (F := F) n : ℂ) * (n : ℂ) ^ (-s) := by
    unfold NumberField.dedekindZeta
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [LSeries.term, hzero]
    · rw [LSeries.term_of_ne_zero hn]
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      simp [rows_small_idealCount]
  have hHecke : heckeLSeries (1 : HeckeChar F) s =
      ∑' I : Ideals, (norm I : ℂ) ^ (-s) := by
    unfold heckeLSeries
    apply tsum_congr
    intro I
    simp [Ideals, norm, HeckeChar.idealValue, HeckeChar.primeValue,
      HeckeChar.UnramifiedAt, HeckeChar.loc]
  calc
    heckeLSeries (1 : HeckeChar F) s = ∑' I : Ideals, (norm I : ℂ) ^ (-s) := hHecke
    _ = ∑' p : Σ n : ℕ, fiber n, (p.1 : ℂ) ^ (-s) := hReindex.symm
    _ = ∑' n : ℕ, (rows_small_idealCount (F := F) n : ℂ) * (n : ℂ) ^ (-s) := hSigmaTsum
    _ = NumberField.dedekindZeta F s := hZeta.symm

private def rows_principalRegularizedLS (s : ℂ) : ℂ :=
  HA.1.2 s * ∏ v ∈ S.Sf,
    (1 - (1 : HeckeChar F).primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))

private theorem rows_principalRegularizedLS_eq (s : ℂ) (hs : s ≠ 1) :
    rows_principalRegularizedLS (HA := HA) (S := S) s =
      (s - 1) * HA.LS S 1 s := by
  rcases HA.2 with ⟨hAgreement, hrest⟩
  rcases hrest with ⟨hContinuation, hrest⟩
  rcases hrest with ⟨hPrincipalDiff, hrest⟩
  rcases hrest with ⟨hRegDiff, hrest⟩
  rcases hrest with ⟨hRegularization, hrest⟩
  unfold rows_principalRegularizedLS HeckeAnalysis.LS HeckeAnalysis.L
  rw [hRegularization s hs]
  ring

private theorem rows_principalRegularizedLS_at_one :
    rows_principalRegularizedLS (HA := HA) (S := S) 1 = HA.RS S := by
  simp [rows_principalRegularizedLS, HeckeAnalysis.RS, HeckeChar.primeValue,
    HeckeChar.UnramifiedAt, HeckeChar.loc, Complex.cpow_neg_one]

private theorem rows_principal_omittedFactors_norm_le (s : ℂ) (hs : 0 < s.re) :
    ‖∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ ≤ 2 ^ S.Sf.card := by
  have hOne : IsOfFinOrder (1 : HeckeChar F) := by simp
  have hfactor (v : FinPlace F) :
      ‖1 - (1 : HeckeChar F).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 2 := by
    have hn : 0 < Ideal.absNorm v.asIdeal :=
      Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
    have hnreal : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
    have hpow : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn)]
      rfl
    have hpowle : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnreal (by linarith)
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(1 : HeckeChar F).primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ‖(1 : HeckeChar F).primeValue v‖ *
          ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by simp [norm_mul]
      _ ≤ 1 + 1 * 1 := by
        have hpv := rows_primeValue_norm_le_one (1 : HeckeChar F) hOne v
        have hpow' : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
          rw [hpow]
          exact hpowle
        nlinarith [norm_nonneg ((1 : HeckeChar F).primeValue v)]
      _ = 2 := by norm_num
  rw [norm_prod]
  calc
    _ ≤ ∏ _v ∈ S.Sf, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro v hv
        positivity
      · intro v hv
        exact hfactor v
    _ = 2 ^ S.Sf.card := by simp

private theorem rows_principalRegularizedLS_growth :
    ∃ AF C : ℝ, 0 ≤ AF ∧ 0 < C ∧
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 →
        ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ ≤
          C * (2 + |s.im|) ^ AF := by
  rcases HA.2 with ⟨hAgreement, hrest⟩
  rcases hrest with ⟨hContinuation, hrest⟩
  rcases hrest with ⟨hPrincipalDiff, hrest⟩
  rcases hrest with ⟨hRegDiff, hrest⟩
  rcases hrest with ⟨hRegularization, hrest⟩
  let m0 : ClassFieldTheory.RayClassModulus F := ⟨0, ∅⟩
  let ψ0 : ClassFieldTheory.RayClassGroup m0 →* ℂˣ := 1
  obtain ⟨AF, hAF, hGrowth⟩ := Hecke.LSeriesRay_trivial_growth (K := F)
  have hAgreementRay : ∀ s : ℂ, 1 < s.re →
      HA.1.2 s = (s - 1) * Hecke.LSeriesRay ψ0 s := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    have hHecke : HA.1.1 1 s = heckeLSeries (1 : HeckeChar F) s :=
      hAgreement 1 s hs
    have hZeta := rows_heckeLSeries_one_eq_dedekindZeta (F := F) s hs
    have hRay : heckeLSeries (1 : HeckeChar F) s = Hecke.LSeriesRay ψ0 s := by
      calc
        _ = NumberField.dedekindZeta F s := hZeta
        _ = Hecke.LSeriesRay ψ0 s :=
          (Hecke.LSeriesRay_trivial_eq_dedekindZeta (K := F) s).symm
    calc
      HA.1.2 s = (s - 1) * HA.1.1 1 s := hRegularization s hsne
      _ = (s - 1) * heckeLSeries (1 : HeckeChar F) s := by rw [hHecke]
      _ = (s - 1) * Hecke.LSeriesRay ψ0 s := by rw [hRay]
  obtain ⟨CG, hCG, hGrowthBound⟩ := hGrowth 1 (by norm_num) (3 / 1000) (by norm_num)
  have hG := hGrowthBound m0 (fun s => HA.1.2 s) hRegDiff (by simpa [ψ0] using hAgreementRay)
  let C : ℝ := CG * 2 ^ S.Sf.card
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨AF, C, hAF, hC, ?_⟩
  intro s hslo hshi
  have hGbound : ‖HA.1.2 s‖ ≤ CG * (2 + |s.im|) ^ AF := by
    have h := hG s hslo hshi
    simpa [m0, Hecke.modulusNorm] using h
  have hFactor := rows_principal_omittedFactors_norm_le (S := S) s
    (by linarith [hslo])
  calc
    ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ =
        ‖HA.1.2 s‖ *
          ‖∏ v ∈ S.Sf,
            (1 - (1 : HeckeChar F).primeValue v *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ := by
          simp [rows_principalRegularizedLS, norm_mul]
    _ ≤ (CG * (2 + |s.im|) ^ AF) * 2 ^ S.Sf.card :=
      mul_le_mul hGbound hFactor (norm_nonneg _) (by positivity)
    _ = C * (2 + |s.im|) ^ AF := by dsimp [C]; ring

private theorem rows_principalLS_growth_off_one :
    ∃ AF C : ℝ, 0 ≤ AF ∧ 0 < C ∧
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 → s.re ≠ 1 →
        ‖HA.LS S 1 s‖ ≤ C * (2 + |s.im|) ^ AF / |s.re - 1| := by
  obtain ⟨AF, C, hAF, hC, hGrowth⟩ := rows_principalRegularizedLS_growth (HA := HA) (S := S)
  refine ⟨AF, C, hAF, hC, ?_⟩
  intro s hslo hshi hsne
  have hsne' : s ≠ (1 : ℂ) := by
    intro h
    apply hsne
    simpa using congrArg Complex.re h
  have hLS : HA.LS S 1 s =
      rows_principalRegularizedLS (HA := HA) (S := S) s / (s - 1) := by
    rw [rows_principalRegularizedLS_eq (HA := HA) (S := S) s hsne']
    field_simp [sub_ne_zero.mpr hsne']
  have hGbound := hGrowth s hslo hshi
  have hgap : 0 < |s.re - 1| := abs_pos.mpr (sub_ne_zero.mpr hsne)
  have hgapLE : |s.re - 1| ≤ ‖s - 1‖ := by
    calc
      |s.re - 1| = |(s - 1).re| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
  have hnum : 0 ≤ C * (2 + |s.im|) ^ AF := by positivity
  calc
    ‖HA.LS S 1 s‖ =
        ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ / ‖s - 1‖ := by
      rw [hLS, norm_div]
    _ ≤ C * (2 + |s.im|) ^ AF / ‖s - 1‖ :=
      div_le_div_of_nonneg_right hGbound (norm_nonneg _)
    _ ≤ C * (2 + |s.im|) ^ AF / |s.re - 1| :=
      div_le_div_of_nonneg_left hnum hgap hgapLE

private theorem rows_principalLS_growth_high_height :
    ∃ AF C : ℝ, 0 ≤ AF ∧ 0 < C ∧
      ∀ s : ℂ, 3 / 1000 ≤ s.re → s.re ≤ 4 → 1 ≤ |s.im| →
        ‖HA.LS S 1 s‖ ≤ C * (2 + |s.im|) ^ AF := by
  obtain ⟨AF, C, hAF, hC, hGrowth⟩ := rows_principalRegularizedLS_growth (HA := HA) (S := S)
  refine ⟨AF, C, hAF, hC, ?_⟩
  intro s hslo hshi him
  have hsne : s ≠ (1 : ℂ) := by
    intro h
    have himEq := congrArg Complex.im h
    simp at himEq
    have hpos : 0 < |s.im| := lt_of_lt_of_le (by norm_num) him
    rw [himEq] at hpos
    norm_num at hpos
  have hLS : HA.LS S 1 s =
      rows_principalRegularizedLS (HA := HA) (S := S) s / (s - 1) := by
    rw [rows_principalRegularizedLS_eq (HA := HA) (S := S) s hsne]
    field_simp [sub_ne_zero.mpr hsne]
  have hden : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hGbound := hGrowth s hslo hshi
  calc
    ‖HA.LS S 1 s‖ =
        ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ / ‖s - 1‖ := by
      rw [hLS, norm_div]
    _ ≤ ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ / 1 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ = ‖rows_principalRegularizedLS (HA := HA) (S := S) s‖ := by simp
    _ ≤ C * (2 + |s.im|) ^ AF := hGbound

private theorem rows_laplace_reciprocal (x : ℝ) (hx : 0 < x) (t : ℝ) :
    (∫ v : ℝ in Set.Ioi 0, Complex.exp (-((x : ℂ) + t * Complex.I) * v)) =
      ((x : ℂ) + t * Complex.I)⁻¹ := by
  have hs : (x : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hneg : (-((x : ℂ) + t * Complex.I)).re < 0 := by simp; linarith
  rw [integral_exp_mul_complex_Ioi (a := -((x : ℂ) + t * Complex.I)) hneg (0 : ℝ)]
  field_simp [hs] <;> simp

set_option maxHeartbeats 3000000 in
private theorem rows_vertical_gaussian_pole_pos (x : ℝ) (hx : 0 < x) :
    vertical x (fun z : ℂ => Complex.exp (z ^ 2) / z) = (1 / 2 : ℂ) := by
  let line : ℝ → ℂ := fun t => (x : ℂ) + t * Complex.I
  let F : ℝ × ℝ → ℂ := fun p => Complex.exp (line p.1 ^ 2 - line p.1 * p.2)
  let g : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-p.1 ^ 2) * Real.exp (-x * p.2)
  have hT : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ)))
  have hV : Integrable (fun v : ℝ => Real.exp (-x * v))
      (volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hg : Integrable g (volume.prod (volume.restrict (Set.Ioi 0))) := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using hT.mul_prod hV
  have line_re (t : ℝ) : (line t).re = x := by simp [line]
  have line_im (t : ℝ) : (line t).im = t := by simp [line]
  have hReal (p : ℝ × ℝ) :
      (line p.1 ^ 2 - line p.1 * p.2).re = x ^ 2 - p.1 ^ 2 - x * p.2 := by
    calc
      _ = (line p.1).re ^ 2 - (line p.1).im ^ 2 - (line p.1).re * p.2 := by
        simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, pow_two]
      _ = _ := by rw [line_re, line_im] <;> ring
  have hFnorm (p : ℝ × ℝ) :
      ‖F p‖ = Real.exp (x ^ 2) *
        (Real.exp (-p.1 ^ 2) * Real.exp (-x * p.2)) := by
    dsimp [F]
    rw [Complex.norm_exp, hReal]
    calc
      Real.exp (x ^ 2 - p.1 ^ 2 - x * p.2) =
          Real.exp ((x ^ 2 + -(p.1 ^ 2)) + -(x * p.2)) := by
        congr 1 <;> ring
      _ = Real.exp (x ^ 2) *
          (Real.exp (-p.1 ^ 2) * Real.exp (-x * p.2)) := by
        rw [Real.exp_add, Real.exp_add]
        ring
  have hFcont : Continuous F := by fun_prop
  have hFdom : Integrable
      (fun p : ℝ × ℝ => Real.exp (x ^ 2) * g p)
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
      hg.const_mul (Real.exp (x ^ 2))
  have hFint : Integrable F (volume.prod (volume.restrict (Set.Ioi 0))) := by
    apply hFdom.mono' hFcont.aestronglyMeasurable
    filter_upwards [] with p
    rw [hFnorm p]
  have hPoint (t : ℝ) :
      Complex.exp (line t ^ 2) / line t = ∫ v : ℝ in Set.Ioi 0, F (t, v) := by
    calc
      _ = Complex.exp (line t ^ 2) *
          ∫ v : ℝ in Set.Ioi 0, Complex.exp (-line t * v) := by
            rw [rows_laplace_reciprocal x hx t]
            ring
      _ = ∫ v : ℝ in Set.Ioi 0,
          Complex.exp (line t ^ 2) * Complex.exp (-line t * v) := by
            rw [← integral_const_mul]
      _ = ∫ v : ℝ in Set.Ioi 0, F (t, v) := by
            apply integral_congr_ae
            filter_upwards [] with v
            dsimp [F]
            calc
              _ = Complex.exp (line t ^ 2 + (-line t) * v) := by
                rw [← Complex.exp_add]
              _ = Complex.exp (line t ^ 2 - line t * v) := by
                congr 1
                ring_nf
  let c (v : ℝ) : ℂ := Complex.I * ((2 * x - v : ℝ) : ℂ)
  let d (v : ℝ) : ℂ := ((x ^ 2 - x * v : ℝ) : ℂ)
  have hLeftRe (t v : ℝ) :
      (line t ^ 2 - line t * v).re = x ^ 2 - t ^ 2 - x * v := by
    calc
      _ = (line t).re ^ 2 - (line t).im ^ 2 - (line t).re * v := by
        simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, pow_two]
      _ = _ := by rw [line_re, line_im] <;> ring
  have hLeftIm (t v : ℝ) :
      (line t ^ 2 - line t * v).im = (2 * x - v) * t := by
    calc
      _ = ((line t).re * (line t).im + (line t).im * (line t).re) -
          (line t).im * v := by
        simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, pow_two]
      _ = _ := by rw [line_re, line_im] <;> ring
  have hcRe (v : ℝ) : (c v).re = 0 := by simp [c, Complex.mul_re]
  have hcIm (v : ℝ) : (c v).im = 2 * x - v := by simp [c, Complex.mul_im]
  have hdRe (v : ℝ) : (d v).re = x ^ 2 - x * v := by
    dsimp [d]
  have hdIm (v : ℝ) : (d v).im = 0 := by
    dsimp [d]
  have hpowRe (t : ℝ) : ((t : ℂ) ^ 2).re = t ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpowIm (t : ℝ) : ((t : ℂ) ^ 2).im = 0 := by
    rw [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hRightRe (t v : ℝ) :
      ((-1 : ℂ) * (t : ℂ) ^ 2 + c v * (t : ℂ) + d v).re =
        -t ^ 2 + (x ^ 2 - x * v) := by
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hcRe, hcIm, hdRe, hdIm, hpowRe]
  have hRightIm (t v : ℝ) :
      ((-1 : ℂ) * (t : ℂ) ^ 2 + c v * (t : ℂ) + d v).im =
        (2 * x - v) * t := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hcRe, hcIm, hdRe, hdIm, hpowIm]
  have hArg (t v : ℝ) :
      line t ^ 2 - line t * v =
        (-1 : ℂ) * (t : ℂ) ^ 2 + c v * (t : ℂ) + d v := by
    apply Complex.ext
    · rw [hLeftRe, hRightRe]
      ring
    · rw [hLeftIm, hRightIm]
  have hc (v : ℝ) : c v = ((2 * x - v : ℝ) : ℂ) * Complex.I := by
    dsimp [c]
    ring
  have hcSq (v : ℝ) : c v ^ 2 = (-((2 * x - v) ^ 2 : ℝ) : ℂ) := by
    rw [hc v, mul_pow, Complex.I_sq]
    simp [Complex.ofReal_pow]
  have hRoot : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    calc
      (Real.pi : ℂ) ^ (1 / 2 : ℂ) =
          (Real.pi : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by rw [hhalf]
      _ = ((Real.pi ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
      _ = (Real.sqrt Real.pi : ℂ) := by rw [Real.sqrt_eq_rpow]
  have hInner (v : ℝ) :
      (∫ t : ℝ, F (t, v)) =
        (Real.sqrt Real.pi : ℂ) * Real.exp (-(v ^ 2) / 4) := by
    have hfun : (fun t : ℝ => F (t, v)) = fun t : ℝ =>
        Complex.exp ((-1 : ℂ) * (t : ℂ) ^ 2 + c v * (t : ℂ) + d v) := by
      funext t
      dsimp [F]
      rw [hArg]
    rw [hfun]
    have hquad := integral_cexp_quadratic (b := (-1 : ℂ)) (by norm_num) (c v) (d v)
    calc
      _ = ((Real.pi : ℂ) / -(-1 : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (d v - (c v) ^ 2 / (4 * (-1 : ℂ))) := hquad
      _ = (Real.sqrt Real.pi : ℂ) * Real.exp (-(v ^ 2) / 4) := by
        have hroot' : (Real.pi : ℂ) / -(-1 : ℂ) = (Real.pi : ℂ) := by norm_num
        have harg : d v - (c v) ^ 2 / (4 * (-1 : ℂ)) =
            ((-(v ^ 2) / 4 : ℝ) : ℂ) := by
          rw [hcSq v]
          have hden : (4 : ℂ) * (-1) = ((-4 : ℝ) : ℂ) := by norm_num
          rw [hden]
          change ((x ^ 2 - x * v : ℝ) : ℂ) -
            ((-((2 * x - v) ^ 2 : ℝ) : ℂ) / ((-4 : ℝ) : ℂ)) =
              ((-(v ^ 2) / 4 : ℝ) : ℂ)
          rw [← Complex.ofReal_neg]
          rw [← Complex.ofReal_div, ← Complex.ofReal_sub]
          apply congrArg Complex.ofReal
          field_simp <;> ring
        rw [hroot', hRoot, harg, Complex.ofReal_exp]
  have hGauss :
      (∫ v : ℝ in Set.Ioi 0, Real.exp (-(1 / 4 : ℝ) * v ^ 2)) = Real.sqrt Real.pi := by
    calc
      _ = Real.sqrt (Real.pi / (1 / 4 : ℝ)) / 2 := integral_gaussian_Ioi (1 / 4 : ℝ)
      _ = Real.sqrt (4 * Real.pi) / 2 := by
        have harg : Real.pi / (1 / 4 : ℝ) = 4 * Real.pi := by field_simp <;> ring
        rw [harg]
      _ = Real.sqrt 4 * Real.sqrt Real.pi / 2 := by
        rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
      _ = Real.sqrt Real.pi := by
        have hsqrt : Real.sqrt 4 = 2 := by norm_num
        rw [hsqrt]
        ring
  have hGauss' :
      (∫ v : ℝ in Set.Ioi 0, Real.exp (-(v ^ 2) / 4)) = Real.sqrt Real.pi := by
    calc
      _ = ∫ v : ℝ in Set.Ioi 0, Real.exp (-(1 / 4 : ℝ) * v ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with v
        congr 1
        ring
      _ = Real.sqrt Real.pi := hGauss
  have hIntegral :
      (∫ t : ℝ, Complex.exp (line t ^ 2) / line t) = (Real.pi : ℂ) := by
    calc
      _ = ∫ t : ℝ, ∫ v : ℝ in Set.Ioi 0, F (t, v) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hPoint t
      _ = ∫ v : ℝ in Set.Ioi 0, ∫ t : ℝ, F (t, v) := integral_integral_swap hFint
      _ = ∫ v : ℝ in Set.Ioi 0,
          (Real.sqrt Real.pi : ℂ) * Real.exp (-(v ^ 2) / 4) := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact hInner v
      _ = (Real.sqrt Real.pi : ℂ) *
          ∫ v : ℝ in Set.Ioi 0, Real.exp (-(v ^ 2) / 4) := by
        rw [integral_const_mul, integral_complex_ofReal]
      _ = (Real.sqrt Real.pi : ℂ) * (Real.sqrt Real.pi : ℂ) := by rw [hGauss']
      _ = (Real.pi : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        calc
          Real.sqrt Real.pi * Real.sqrt Real.pi = Real.sqrt Real.pi ^ 2 := by ring
          _ = Real.pi := Real.sq_sqrt Real.pi_pos.le
  unfold vertical
  rw [hIntegral]
  field_simp [Real.pi_ne_zero] <;> ring

private theorem rows_vertical_gaussian_pole_neg (x : ℝ) (hx : x < 0) :
    vertical x (fun z : ℂ => Complex.exp (z ^ 2) / z) = (-1 / 2 : ℂ) := by
  let y : ℝ := -x
  have hy : 0 < y := by dsimp [y]; linarith
  let f : ℝ → ℂ := fun t =>
    Complex.exp (((y : ℂ) + t * Complex.I) ^ 2) / ((y : ℂ) + t * Complex.I)
  have hreflect : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding f
    simpa [Function.comp_def] using h
  have hpoint (t : ℝ) :
      Complex.exp (((x : ℂ) + t * Complex.I) ^ 2) / ((x : ℂ) + t * Complex.I) =
        -f (-t) := by
    have hline : (x : ℂ) + t * Complex.I = -((y : ℂ) + (-t) * Complex.I) := by
      apply Complex.ext <;> simp [y] <;> ring
    calc
      _ = Complex.exp ((-((y : ℂ) + (-t) * Complex.I)) ^ 2) /
          -((y : ℂ) + (-t) * Complex.I) := by rw [hline]
      _ = - (Complex.exp (((y : ℂ) + (-t) * Complex.I) ^ 2) /
          ((y : ℂ) + (-t) * Complex.I)) := by
            rw [neg_sq, div_neg]
      _ = -f (-t) := by simp [f, Complex.ofReal_neg]
  have hIntegral :
      (∫ t : ℝ, Complex.exp (((x : ℂ) + t * Complex.I) ^ 2) /
        ((x : ℂ) + t * Complex.I)) =
          -(∫ t : ℝ, Complex.exp (((y : ℂ) + t * Complex.I) ^ 2) /
            ((y : ℂ) + t * Complex.I)) := by
    calc
      _ = ∫ t : ℝ, -f (-t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hpoint t
      _ = -(∫ t : ℝ, f (-t)) := by rw [integral_neg]
      _ = -(∫ t : ℝ, f t) := by rw [hreflect]
      _ = _ := by rfl
  have hpos := rows_vertical_gaussian_pole_pos y hy
  have hpos' :
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, Complex.exp (((y : ℂ) + t * Complex.I) ^ 2) /
          ((y : ℂ) + t * Complex.I) = (1 / 2 : ℂ) := by
    simpa [vertical] using hpos
  unfold vertical
  rw [hIntegral]
  calc
    (1 / (2 * Real.pi) : ℂ) *
        -(∫ t : ℝ, Complex.exp (((y : ℂ) + t * Complex.I) ^ 2) /
          ((y : ℂ) + t * Complex.I)) =
        -((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, Complex.exp (((y : ℂ) + t * Complex.I) ^ 2) /
            ((y : ℂ) + t * Complex.I)) := by ring
    _ = (-1 / 2 : ℂ) := by rw [hpos']; norm_num

private theorem rows_gaussian_pole_line_integrable (x : ℝ) (hx : x ≠ 0) :
    Integrable (fun t : ℝ => Complex.exp (((x : ℂ) + t * Complex.I) ^ 2) /
      ((x : ℂ) + t * Complex.I)) := by
  let line : ℝ → ℂ := fun t => (x : ℂ) + t * Complex.I
  have hLineRe (t : ℝ) : (line t).re = x := by simp [line]
  have hLineIm (t : ℝ) : (line t).im = t := by simp [line]
  have hLineNe (t : ℝ) : line t ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    rw [hLineRe t] at hRe
    exact hx (by simpa using hRe)
  have hLineCont : Continuous line := by fun_prop
  have hExpCont : Continuous (fun t : ℝ => Complex.exp ((line t) ^ 2)) := by fun_prop
  have hcont : Continuous (fun t : ℝ => Complex.exp ((line t) ^ 2) / line t) := by
    have hInv : Continuous (fun t : ℝ => (line t)⁻¹) := hLineCont.inv₀ hLineNe
    change Continuous ((fun t : ℝ => Complex.exp ((line t) ^ 2)) *
      (fun t : ℝ => (line t)⁻¹))
    exact hExpCont.mul hInv
  have hsq (t : ℝ) : ((line t) ^ 2).re = x ^ 2 - t ^ 2 := by
    rw [pow_two, Complex.mul_re, hLineRe, hLineIm]
    ring
  have hnorm (t : ℝ) :
      ‖Complex.exp ((line t) ^ 2) / line t‖ =
        Real.exp (x ^ 2) * Real.exp (-t ^ 2) / ‖line t‖ := by
    rw [norm_div, Complex.norm_exp, hsq, Real.exp_sub, Real.exp_neg]
    simp [div_eq_mul_inv]
  have hden (t : ℝ) : |x| ≤ ‖line t‖ := by
    simpa only [hLineRe] using (Complex.abs_re_le_norm (line t))
  have hmajorant (t : ℝ) :
      ‖Complex.exp ((line t) ^ 2) / line t‖ ≤
        (Real.exp (x ^ 2) / |x|) * Real.exp (-t ^ 2) := by
    rw [hnorm]
    have hxabs : 0 < |x| := abs_pos.mpr hx
    calc
      _ ≤ Real.exp (x ^ 2) * Real.exp (-t ^ 2) / |x| :=
        div_le_div_of_nonneg_left (by positivity) hxabs (hden t)
      _ = _ := by ring
  have hgauss : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ)))
  have hbound : Integrable
      (fun t : ℝ => (Real.exp (x ^ 2) / |x|) * Real.exp (-t ^ 2)) :=
    hgauss.const_mul (Real.exp (x ^ 2) / |x|)
  apply hbound.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  exact hmajorant t

private theorem rows_vertical_simple_pole_decomp (a b : ℝ) (res : ℂ)
    (F G K : ℂ → ℂ)
    (hab : a ≤ b)
    (hGdiff : DifferentiableOn ℂ G {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hGA : Integrable (fun t : ℝ => G ((a : ℂ) + t * Complex.I)))
    (hGB : Integrable (fun t : ℝ => G ((b : ℂ) + t * Complex.I)))
    (hKA : Integrable (fun t : ℝ => K ((a : ℂ) + t * Complex.I)))
    (hKB : Integrable (fun t : ℝ => K ((b : ℂ) + t * Complex.I)))
    (hbot : Tendsto (fun T : ℝ =>
      ∫ x : ℝ in a..b, G ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ =>
      ∫ x : ℝ in a..b, G ((x : ℂ) + T * Complex.I)) atTop (𝓝 0))
    (hFA : ∀ t : ℝ, F ((a : ℂ) + t * Complex.I) =
      G ((a : ℂ) + t * Complex.I) + res * K ((a : ℂ) + t * Complex.I))
    (hFB : ∀ t : ℝ, F ((b : ℂ) + t * Complex.I) =
      G ((b : ℂ) + t * Complex.I) + res * K ((b : ℂ) + t * Complex.I))
    (hKvalueA : vertical a K = (-1 / 2 : ℂ))
    (hKvalueB : vertical b K = (1 / 2 : ℂ)) :
    vertical b F = vertical a F + res := by
  have hshift := OAI.SevenEighths.Continuation.vertical_integral_eq_of_horizontal_vanish
    G hab hGdiff hGA hGB hbot htop
  have hGvertical : vertical b G = vertical a G := by
    unfold vertical
    rw [hshift.symm]
  have hlineA :
      (∫ t : ℝ, F ((a : ℂ) + t * Complex.I)) =
        (∫ t : ℝ, G ((a : ℂ) + t * Complex.I)) +
          res * ∫ t : ℝ, K ((a : ℂ) + t * Complex.I) := by
    calc
      _ = ∫ t : ℝ,
          G ((a : ℂ) + t * Complex.I) + res * K ((a : ℂ) + t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hFA t
      _ = _ := by
        rw [integral_add hGA (hKA.const_mul res), integral_const_mul]
  have hlineB :
      (∫ t : ℝ, F ((b : ℂ) + t * Complex.I)) =
        (∫ t : ℝ, G ((b : ℂ) + t * Complex.I)) +
          res * ∫ t : ℝ, K ((b : ℂ) + t * Complex.I) := by
    calc
      _ = ∫ t : ℝ,
          G ((b : ℂ) + t * Complex.I) + res * K ((b : ℂ) + t * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hFB t
      _ = _ := by
        rw [integral_add hGB (hKB.const_mul res), integral_const_mul]
  have hVdecompA : vertical a F = vertical a G + res * vertical a K := by
    unfold vertical
    rw [hlineA]
    ring
  have hVdecompB : vertical b F = vertical b G + res * vertical b K := by
    unfold vertical
    rw [hlineB]
    ring
  calc
    vertical b F = vertical b G + res * vertical b K := hVdecompB
    _ = vertical a G + res * vertical a K + res := by
      rw [hGvertical, hKvalueB, hKvalueA]
      norm_num
      ring
    _ = vertical a F + res := by rw [← hVdecompA]

private theorem rows_regularize_simple_pole (a b p : ℝ) (A F : ℂ → ℂ)
    (hap : a < p) (hpb : p < b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ p → F z = A z / (z - p)) :
    ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G {z : ℂ | a ≤ z.re ∧ z.re ≤ b} ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ p →
        F z = G z + A p * Complex.exp ((z - p) ^ 2) / (z - p) := by
  let strip : Set ℂ := {z : ℂ | a ≤ z.re ∧ z.re ≤ b}
  let E : ℂ → ℂ := fun z => Complex.exp ((z - p) ^ 2)
  let N : ℂ → ℂ := fun z => A z - A p * E z
  let G : ℂ → ℂ := dslope N p
  have hEdiff : Differentiable ℂ E := by fun_prop
  have hNdiff : DifferentiableOn ℂ N strip := by
    change DifferentiableOn ℂ (fun z => A z - A p * E z) strip
    exact hA.sub (hEdiff.differentiableOn.const_mul (A p))
  have hstripN : strip ∈ 𝓝 (p : ℂ) := by
    apply Filter.mem_of_superset
      (((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
          (show a < (p : ℂ).re ∧ (p : ℂ).re < b by simpa using ⟨hap, hpb⟩))
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hGdiff : DifferentiableOn ℂ G strip := by
    exact (Complex.differentiableOn_dslope hstripN).2 hNdiff
  have hNp : N p = 0 := by simp [N, E]
  have hGform (z : ℂ) (hz : z ≠ p) : G z = (N z - N p) / (z - p) := by
    dsimp [G]
    rw [dslope_of_ne N hz, slope_def_field]
  refine ⟨G, ?_, ?_⟩
  · simpa [strip] using hGdiff
  · intro z hzl hzr hzp
    rw [hF z hzl hzr hzp, hGform z hzp, hNp]
    dsimp [N, E]
    field_simp [sub_ne_zero.mpr hzp]
    ring

private theorem rows_weightW1hat_one_ne_zero : weightW1hat W 1 ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := W.W1_nonzero
  have him := (W.W1_nonnegative t).1
  have htsupport : t ∈ tsupport W.W1 := subset_tsupport W.W1 ht
  have htpos : 0 < t := W.W1_positive_support htsupport
  let f : ℝ → ℝ := fun x => (W.W1 x).re
  have hfcont : Continuous f := by
    exact Complex.continuous_re.comp W.W1_smooth.continuous
  have hfcompact : HasCompactSupport f := by
    change HasCompactSupport (fun x => Complex.re (W.W1 x))
    exact W.W1_compact.comp_left (by simp)
  have hfnonneg : ∀ x, 0 ≤ f x := fun x => (W.W1_nonnegative x).2
  have hfne : f t ≠ 0 := by
    intro hzero
    apply ht
    apply Complex.ext
    · simpa [f] using hzero
    · exact him
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfcompact
  have hIntegralPos : 0 < (∫ x : ℝ, f x) :=
    hfcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hfcompact hfnonneg hfne
  have hfzero (x : ℝ) (hx : x ≤ 0) : f x = 0 := by
    by_contra hzero
    have hW : W.W1 x ≠ 0 := by
      intro hW
      apply hzero
      simp [f, hW]
    have hxSupport : x ∈ tsupport W.W1 := subset_tsupport W.W1 hW
    have hxpos := Set.mem_Ioi.mp (W.W1_positive_support hxSupport)
    exact (not_lt_of_ge hx) hxpos
  have hComplement : (∫ x : ℝ in (Set.Ioi 0)ᶜ, f x) = 0 := by
    calc
      _ = ∫ x : ℝ in (Set.Ioi 0)ᶜ, (0 : ℝ) := by
        apply setIntegral_congr_ae (measurableSet_Ioi.compl)
        exact Eventually.of_forall fun x hx => hfzero x (by simpa using hx)
      _ = 0 := by simp
  have hIoiEq :
      (∫ x : ℝ in Set.Ioi 0, f x) = (∫ x : ℝ, f x) := by
    have h := integral_add_compl (μ := volume) (s := Set.Ioi (0 : ℝ))
      measurableSet_Ioi hfint
    rw [hComplement, add_zero] at h
    exact h
  have hIntegralIoiPos : 0 < (∫ x : ℝ in Set.Ioi 0, f x) := by
    rw [hIoiEq]
    exact hIntegralPos
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi 0) :
      W.W1 x * (x : ℂ) ^ (1 : ℂ) / (x : ℂ) = (f x : ℂ) := by
    have hW : W.W1 x = (f x : ℂ) := by
      apply Complex.ext
      · simp [f]
      · exact (W.W1_nonnegative x).1
    have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hx).ne'
    rw [hW]
    simp only [Complex.cpow_one]
    field_simp [hxne]
  have hWeight : weightW1hat W 1 = ∫ x : ℝ in Set.Ioi 0, (f x : ℂ) := by
    unfold weightW1hat
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  rw [hWeight]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr hIntegralIoiPos.ne'

private theorem rows_principalRS_ne_zero : HA.RS S ≠ 0 := by
  classical
  rcases HA.2 with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hrest⟩
  rcases hrest with ⟨_, hpositive⟩
  have hRegular : HA.1.2 1 ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hFactor (v : FinPlace F) :
      1 - (Ideal.absNorm v.asIdeal : ℂ)⁻¹ ≠ 0 := by
    intro h
    have hinv : (Ideal.absNorm v.asIdeal : ℂ)⁻¹ = 1 :=
      (sub_eq_zero.mp h).symm
    have hcast : (Ideal.absNorm v.asIdeal : ℂ) = 1 := inv_eq_one.mp hinv
    have hNat : Ideal.absNorm v.asIdeal = 1 := by exact_mod_cast hcast
    have hlarge := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  unfold HeckeAnalysis.RS
  exact mul_ne_zero hRegular (Finset.prod_ne_zero_iff.mpr fun v hv => hFactor v)

private theorem rows_principalConstant_ne_zero (hWeight : WeightSpec R sd W) :
    principalConstant R sd W HA ≠ 0 := by
  rcases hWeight with ⟨_, hM⟩
  have hRS := rows_principalRS_ne_zero (S := S) (HA := HA)
  have hW := rows_weightW1hat_one_ne_zero (W := W)
  unfold principalConstant
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (pow_ne_zero 2 hRS) (by norm_num)) hM) hW

private theorem rows_principalKernel_eq (Z : ℝ) (ξ w z : ℂ) :
    rowKernel R sd W η U HA HC U.one Z ξ w z =
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
        HA.LS S 1 (6 * z) * HA.LS S 1 w * HC.H U.one ![ξ, w, z] /
          HA.LS S η ξ := by
  have honeInv : (1 : HeckeChar F)⁻¹ = 1 := by
    ext x
    change (((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ) = (1 : ℂ)
    simp
  have hk : U.kummer U.one = 1 := FrequencyData.kummer_one U
  have hmulOne : η * (1 : HeckeChar F) = η := by
    ext x
    change (((η x : ℂˣ) * (1 : ℂˣ) : ℂˣ) : ℂ) = ((η x : ℂˣ) : ℂ)
    simp
  simp [rowKernel, rowTwist, U.q_one, hk, honeInv, hmulOne]
  <;> ring

private theorem rows_principalKernel_norm_bound_of_factors (Z : ℝ) (hZ : 0 < Z)
    (ξ w z : ℂ) (CM CZ CW CH CI : ℝ)
    (hCM : 0 ≤ CM) (hCZ : 0 ≤ CZ) (hCW : 0 ≤ CW) (hCH : 0 ≤ CH) (hCI : 0 ≤ CI)
    (hM : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤ CM)
    (hZeta : ‖HA.LS S 1 (6 * z)‖ ≤ CZ)
    (hW : ‖HA.LS S 1 w‖ ≤ CW)
    (hH : ‖HC.H U.one ![ξ, w, z]‖ ≤ CH)
    (hInv : ‖(HA.LS S η ξ)⁻¹‖ ≤ CI) :
    ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
      Z ^ Estar ξ.re w.re z.re * CM * CZ * CW * CH * CI := by
  have hk : U.kummer U.one = 1 := FrequencyData.kummer_one U
  have honeInv : (1 : HeckeChar F)⁻¹ = 1 := by
    ext x
    change (((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ) = (1 : ℂ)
    simp
  have hmulOne : η * (1 : HeckeChar F) = η := by
    ext x
    change (((η x : ℂˣ) * (1 : ℂˣ) : ℂˣ) : ℂ) = ((η x : ℂˣ) : ℂ)
    simp
  have htw : rowTwist η U U.one = η := by
    simp [rowTwist, hk, honeInv, hmulOne]
  rw [rows_rowKernel_norm_eq R sd W η U HA HC Z hZ U.one ξ w z]
  rw [U.q_one, hk, htw]
  simp only [Real.one_rpow, one_mul, mul_one]
  have hprod :
      ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ *
        ‖HA.LS S 1 (6 * z)‖ * ‖HA.LS S 1 w‖ *
        ‖HC.H U.one ![ξ, w, z]‖ * ‖(HA.LS S η ξ)⁻¹‖ ≤
          CM * CZ * CW * CH * CI := by
    gcongr
  calc
    _ = Z ^ Estar ξ.re w.re z.re *
        (‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ *
          ‖HA.LS S 1 (6 * z)‖ * ‖HA.LS S 1 w‖ *
          ‖HC.H U.one ![ξ, w, z]‖ * ‖(HA.LS S η ξ)⁻¹‖) := by ring
    _ ≤ Z ^ Estar ξ.re w.re z.re * (CM * CZ * CW * CH * CI) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ.le _)
    _ = Z ^ Estar ξ.re w.re z.re * CM * CZ * CW * CH * CI := by ring

private theorem rows_principal_kernel_bound_of_height_bounds
    (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) (AF pZ pW : ℝ)
    (CM CZ CW CH CI : ℝ)
    (hCM : 0 ≤ CM) (hCZ : 0 ≤ CZ) (hCW : 0 ≤ CW) (hCH : 0 ≤ CH) (hCI : 0 ≤ CI)
    (hM : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
      CM * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-pZ) *
        (1 + |w.im|) ^ (-pW))
    (hZeta : ‖HA.LS S 1 (6 * z)‖ ≤ CZ * (2 + |z.im|) ^ AF)
    (hW : ‖HA.LS S 1 w‖ ≤ CW * (2 + |w.im|) ^ AF)
    (hH : ‖HC.H U.one ![ξ, w, z]‖ ≤ CH)
    (hInv : ‖(HA.LS S η ξ)⁻¹‖ ≤ CI) :
    ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
      Z ^ Estar ξ.re w.re z.re * CM * CZ * CW * CH * CI *
        Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-pZ) * (1 + |w.im|) ^ (-pW) *
            (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF := by
  have hMnonneg : 0 ≤ CM * Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-pZ) * (1 + |w.im|) ^ (-pW) := by positivity
  let CZ' : ℝ := CZ * (2 + |z.im|) ^ AF
  let CW' : ℝ := CW * (2 + |w.im|) ^ AF
  have hCZ' : 0 ≤ CZ' := by dsimp [CZ']; positivity
  have hCW' : 0 ≤ CW' := by dsimp [CW']; positivity
  have hfactor := rows_principalKernel_norm_bound_of_factors R sd W η U HA HC Z hZ ξ w z
    (CM * Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-pZ) * (1 + |w.im|) ^ (-pW)) CZ' CW' CH CI
    hMnonneg hCZ' hCW' hCH hCI hM hZeta hW hH hInv
  calc
    _ ≤ Z ^ Estar ξ.re w.re z.re *
        (CM * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-pZ) *
          (1 + |w.im|) ^ (-pW)) * CZ' * CW' * CH * CI := hfactor
    _ = Z ^ Estar ξ.re w.re z.re * CM * CZ * CW * CH * CI *
        Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-pZ) * (1 + |w.im|) ^ (-pW) *
            (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF := by
      dsimp [CZ', CW']
      ring

private theorem rows_principal_absorb_poly (t AF A : ℝ)
    (hAF : 0 ≤ AF) :
    (1 + |t|) ^ (-(AF + A)) * (2 + |t|) ^ AF ≤
      2 ^ AF * (1 + |t|) ^ (-A) := by
  have hx : 1 ≤ 1 + |t| := by nlinarith [abs_nonneg t]
  have hxpos : 0 < 1 + |t| := by positivity
  have hbase : 2 + |t| ≤ 2 * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hpow : (2 + |t|) ^ AF ≤ (2 * (1 + |t|)) ^ AF :=
    Real.rpow_le_rpow (by positivity) hbase hAF
  have hmul : (2 * (1 + |t|)) ^ AF = 2 ^ AF * (1 + |t|) ^ AF := by
    rw [Real.mul_rpow (by norm_num) hxpos.le]
  calc
    _ ≤ (1 + |t|) ^ (-(AF + A)) * (2 * (1 + |t|)) ^ AF :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)
    _ = 2 ^ AF * (1 + |t|) ^ (-A) := by
      rw [hmul]
      calc
        _ = 2 ^ AF *
            ((1 + |t|) ^ (-(AF + A)) * (1 + |t|) ^ AF) := by ring
        _ = 2 ^ AF * (1 + |t|) ^ (-A) := by
          rw [← Real.rpow_add hxpos]
          congr 1
          congr 1
          ring
    _ = _ := rfl

private theorem rows_principalRw_exponent_bound :
    Estar (1 + δ1) (95 / 100) (1 / 6 + δ1) ≤ 7 / 15 - 5 / 10000 := by
  norm_num [Estar, a, b, h0, δ1]

private theorem rows_principalRz_exponent_bound :
    Estar (1 + δ1) 1 (16 / 100) ≤ 7 / 15 - 5 / 10000 := by
  norm_num [Estar, a, b, h0, δ1]

private theorem rows_principal_initial_rowContribution_eq (hEuler : EulerHypotheses R η)
    (Z : ℝ) :
    rowContribution R sd W η U {U.one} Z =
      tripleVertical 4 4 2 (fun ξ w z => rowKernel R sd W η U HA HC U.one Z ξ w z) := by
  have h := rows_initial_rowContribution_eq R sd W η U HA HC hEuler Z {U.one}
  simpa using h

private theorem rows_principal_kernel_control (hEuler : EulerHypotheses R η) :
    ∃ AF Aconv C0 Cconv : ℝ, 0 ≤ AF ∧ 1 < Aconv ∧ 0 < C0 ∧ 0 < Cconv ∧
      (∀ T : ℝ, ∫ v : ℝ, Real.exp (-((T + v) ^ 2)) *
        (1 + |v|) ^ (-Aconv) ≤ Cconv * (1 + |T|) ^ (-2 : ℝ)) ∧
      ∀ Z : ℝ, 2 ≤ Z → ∀ ξ w z : ℂ,
        1 + δ1 ≤ ξ.re → ξ.re ≤ 4 → w.re = 95 / 100 →
        z.re = 1 / 6 + δ1 →
        ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
          C0 * Z ^ Estar ξ.re w.re z.re *
            Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by
  obtain ⟨Aconv, Cconv, hAconv, hCconv, hconv⟩ :=
    zf_height_convolution (2 : ℝ) (by norm_num)
  obtain ⟨AF, CG, hAF, hCG, hGrowth⟩ :=
    rows_principalLS_growth_off_one (HA := HA) (S := S)
  let Aheight : ℝ := Aconv + AF + 2
  obtain ⟨Cht, hCht, hheight⟩ := zf_height_decay R sd W
    (1 + δ1) 4 (95 / 100) (95 / 100) (1 / 6 + δ1) (1 / 6 + δ1) Aheight
    (by norm_num [δ1]) (by norm_num) (by norm_num [δ1]) (by norm_num [δ1])
    (by dsimp [Aheight]; linarith [hAconv, hAF])
  obtain ⟨CH, hCH, hHbound⟩ := (po_H_product R η U HC hEuler).2.2.2
    (1 : ℝ) (by norm_num)
  obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
  let Cinv : ℝ := (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re * 2 ^ S.Sf.card
  have hCinv : 0 ≤ Cinv := by
    have hζ := rows_small_dedekindZeta_real_nonneg (F := F) (1 + δ1)
      (by norm_num [δ1])
    have hζ' : 0 ≤ (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re := by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using hζ
    dsimp [Cinv]
    exact mul_nonneg hζ' (by positivity)
  let Cz : ℝ := CG * 6 ^ AF / (6 * δ1)
  let Cw : ℝ := CG / (1 / 20 : ℝ)
  have hCz : 0 < Cz := by
    dsimp [Cz]
    have hδ : 0 < δ1 := by norm_num [δ1]
    exact div_pos (mul_pos hCG
      (Real.rpow_pos_of_pos (by norm_num : 0 < (6 : ℝ)) AF)) (mul_pos (by norm_num) hδ)
  have hCw : 0 < Cw := by dsimp [Cw]; positivity
  let Cbase : ℝ := Cht * Cz * Cw * CH * Cinv * 2 ^ (2 * AF)
  let C0 : ℝ := Cbase + 1
  have hCbase : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith
  have hAheight : Aheight = AF + (Aconv + 2) := by dsimp [Aheight]; ring
  refine ⟨AF, Aconv, C0, Cconv, hAF, hAconv, hC0, hCconv, hconv, ?_⟩
  intro Z hZ ξ w z hξlo hξhi hwre hzre
  have hZpos : 0 < Z := by linarith
  have hLSz : ‖HA.LS S 1 (6 * z)‖ ≤ Cz * (2 + |z.im|) ^ AF := by
    have h := hGrowth (6 * z) (by rw [show (6 * z).re = 6 * z.re by simp, hzre]; norm_num [δ1])
      (by rw [show (6 * z).re = 6 * z.re by simp, hzre]; norm_num [δ1])
      (by rw [show (6 * z).re = 6 * z.re by simp, hzre]; norm_num [δ1])
    have him : |(6 * z).im| = 6 * |z.im| := by simp [abs_mul]
    rw [him, show (6 * z).re = 6 * z.re by simp, hzre] at h
    have hgap : |6 * (1 / 6 + δ1) - 1| = 6 * δ1 := by norm_num [δ1]
    rw [hgap] at h
    have hbase : 2 + 6 * |z.im| ≤ 6 * (2 + |z.im|) := by nlinarith [abs_nonneg z.im]
    have hpow : (2 + 6 * |z.im|) ^ AF ≤
        (6 : ℝ) ^ AF * (2 + |z.im|) ^ AF := by
      calc
        _ ≤ (6 * (2 + |z.im|)) ^ AF :=
          Real.rpow_le_rpow (by positivity) hbase hAF
        _ = (6 : ℝ) ^ AF * (2 + |z.im|) ^ AF := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
    calc
      _ ≤ CG * (2 + 6 * |z.im|) ^ AF / (6 * δ1) := by
        simpa [Cz] using h
      _ ≤ CG * ((6 : ℝ) ^ AF * (2 + |z.im|) ^ AF) / (6 * δ1) := by
        apply div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hCG.le)
          (by nlinarith [show 0 < δ1 by norm_num [δ1]])
      _ = Cz * (2 + |z.im|) ^ AF := by dsimp [Cz]; ring
  have hLSw : ‖HA.LS S 1 w‖ ≤ Cw * (2 + |w.im|) ^ AF := by
    have h := hGrowth w (by rw [hwre] <;> norm_num) (by rw [hwre] <;> norm_num)
      (by rw [hwre] <;> norm_num)
    rw [hwre] at h
    rw [show |(95 / 100 : ℝ) - 1| = (1 / 20 : ℝ) by norm_num] at h
    calc
      _ ≤ CG * (2 + |w.im|) ^ AF / (1 / 20 : ℝ) := h
      _ = Cw * (2 + |w.im|) ^ AF := by dsimp [Cw]; ring
  have hH : ‖HC.H U.one ![ξ, w, z]‖ ≤ CH := by
    have hregion : eulerNeighborhood ![ξ, w, z] := by
      right
      change (998 / 1000 - 1 / 100000 < ξ.re ∧
        95 / 100 - 1 / 100000 < w.re ∧ 16 / 100 - 1 / 100000 < z.re)
      refine ⟨?_, ?_, ?_⟩
      · have hδ : 0 < δ1 := by norm_num [δ1]
        linarith [hξlo]
      · rw [hwre]
        norm_num
      · rw [hzre]
        norm_num [δ1]
    have h := hHbound U.one ![ξ, w, z] hregion
    simpa [U.q_one] using h
  have hInv : ‖(HA.LS S η ξ)⁻¹‖ ≤ Cinv := by
    have hξone : 1 < ξ.re := by
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith [hξlo]
    obtain ⟨_, hrecip⟩ := rows_LS_inverse_bound HA S η hEuler.1 fη hfη hξone
    have hζmono : (NumberField.dedekindZeta F ξ.re).re ≤
        (NumberField.dedekindZeta F ((1 + δ1 : ℝ) : ℂ)).re :=
      rows_small_dedekindZeta_real_antitone (F := F) (by norm_num [δ1]) hξlo
    have hζmono' : (NumberField.dedekindZeta F ξ.re).re ≤
        (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re := by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using hζmono
    dsimp [Cinv]
    exact hrecip.trans (mul_le_mul_of_nonneg_right hζmono' (by positivity))
  have hM := hheight ξ w z hξlo hξhi (by rw [hwre] <;> norm_num)
    (by rw [hwre] <;> norm_num) (by rw [hzre] <;> norm_num) (by rw [hzre] <;> norm_num)
  have hPoint := rows_principal_kernel_bound_of_height_bounds R sd W η U HA HC
    Z hZpos ξ w z AF Aheight Aheight Cht Cz Cw CH Cinv
    hCht.le hCz.le hCw.le hCH.le hCinv hM hLSz hLSw hH hInv
  have hpolyZ := rows_principal_absorb_poly z.im AF (Aconv + 2) hAF
  have hpolyW := rows_principal_absorb_poly w.im AF (Aconv + 2) hAF
  have hbaseZ : 1 ≤ 1 + |z.im| := by nlinarith [abs_nonneg z.im]
  have hbaseW : 1 ≤ 1 + |w.im| := by nlinarith [abs_nonneg w.im]
  have hweakZ : (1 + |z.im|) ^ (-(Aconv + 2)) ≤ (1 + |z.im|) ^ (-Aconv) :=
    Real.rpow_le_rpow_of_exponent_le hbaseZ (by linarith [hAconv])
  have hweakW : (1 + |w.im|) ^ (-(Aconv + 2)) ≤ (1 + |w.im|) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbaseW (by linarith [hAconv])
  have hpolyZ' : (1 + |z.im|) ^ (-Aheight) * (2 + |z.im|) ^ AF ≤
      2 ^ AF * (1 + |z.im|) ^ (-Aconv) := by
    rw [hAheight]
    calc
      _ ≤ 2 ^ AF * (1 + |z.im|) ^ (-(Aconv + 2)) := hpolyZ
      _ ≤ 2 ^ AF * (1 + |z.im|) ^ (-Aconv) := by
        exact mul_le_mul_of_nonneg_left hweakZ (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
  have hpolyW' : (1 + |w.im|) ^ (-Aheight) * (2 + |w.im|) ^ AF ≤
      2 ^ AF * (1 + |w.im|) ^ (-2 : ℝ) := by
    rw [hAheight]
    calc
      _ ≤ 2 ^ AF * (1 + |w.im|) ^ (-(Aconv + 2)) := hpolyW
      _ ≤ 2 ^ AF * (1 + |w.im|) ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hweakW (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
  let B0 : ℝ := Z ^ Estar ξ.re w.re z.re * Cht * Cz * Cw * CH * Cinv *
    Real.exp (-((ξ.im + z.im) ^ 2))
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hpolyBoth :
      (1 + |z.im|) ^ (-Aheight) * (1 + |w.im|) ^ (-Aheight) *
        (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF ≤
      (2 ^ AF * (1 + |z.im|) ^ (-Aconv)) *
        (2 ^ AF * (1 + |w.im|) ^ (-2 : ℝ)) := by
    calc
      _ = ((1 + |z.im|) ^ (-Aheight) * (2 + |z.im|) ^ AF) *
          ((1 + |w.im|) ^ (-Aheight) * (2 + |w.im|) ^ AF) := by ring
      _ ≤ _ := mul_le_mul hpolyZ' hpolyW'
        (by positivity) (by positivity)
  have hscaled :
      ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
        B0 * ((1 + |z.im|) ^ (-Aheight) * (1 + |w.im|) ^ (-Aheight) *
          (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF) := by
    calc
      _ ≤ Z ^ Estar ξ.re w.re z.re * Cht * Cz * Cw * CH * Cinv *
          Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-Aheight) * (1 + |w.im|) ^ (-Aheight) *
            (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF := hPoint
      _ = _ := by dsimp [B0]; ring
  have htargetNonneg : 0 ≤
      Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ) := by positivity
  have hCbasele : Cbase ≤ C0 := by dsimp [C0]; linarith
  calc
    ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
        B0 * ((1 + |z.im|) ^ (-Aheight) * (1 + |w.im|) ^ (-Aheight) *
          (2 + |z.im|) ^ AF * (2 + |w.im|) ^ AF) := hscaled
    _ ≤ B0 * ((2 ^ AF * (1 + |z.im|) ^ (-Aconv)) *
        (2 ^ AF * (1 + |w.im|) ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hpolyBoth hB0
    _ = Cbase * (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by
          have htwo : (2 : ℝ) ^ AF * (2 : ℝ) ^ AF = (2 : ℝ) ^ (2 * AF) := by
            rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
            congr 1
            ring
          calc
            _ = Cht * Cz * Cw * CH * Cinv *
                (2 ^ AF * 2 ^ AF) *
                (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
                  (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by
                    dsimp [B0]
                    ring
            _ = Cht * Cz * Cw * CH * Cinv * (2 : ℝ) ^ (2 * AF) *
                (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
                  (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) := by
                    rw [htwo]
            _ = _ := by dsimp [Cbase] <;> ring
    _ ≤ C0 * (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-Aconv) * (1 + |w.im|) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hCbasele htargetNonneg
    _ = _ := by ring

private theorem rows_principalRw_bound (hEuler : EulerHypotheses R η) (Z : ℝ)
    (hZ : 2 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧
      ‖principalRw R sd W η U HA HC Z‖ ≤ C * Z ^ (7 / 15 - 5 / 10000 : ℝ) := by
  obtain ⟨AF, Aconv, C0, Cconv, hAF, hAconv, hC0, hCconv, hconv, hcontrol⟩ :=
    rows_principal_kernel_control R sd W η U HA HC hEuler
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hIint : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hI0 : 0 ≤ I := by dsimp [I]; exact integral_nonneg fun t => by positivity
  have hZpos : 0 < Z := by linarith
  let M : ℝ := C0 * Z ^ Estar (1 + δ1) (95 / 100) (1 / 6 + δ1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let K : ℂ → ℂ → ℂ → ℂ := rowKernel R sd W η U HA HC U.one Z
  have hline (tξ tw tz : ℝ) :
      ‖K ((1 + δ1 : ℝ) + tξ * Complex.I)
          ((95 / 100 : ℝ) + tw * Complex.I)
          ((1 / 6 + δ1 : ℝ) + tz * Complex.I)‖ ≤
        M * Real.exp (-((tξ + tz) ^ 2)) *
          (1 + |tz|) ^ (-Aconv) * (1 + |tw|) ^ (-2 : ℝ) := by
    let ξ : ℂ := (1 + δ1 : ℝ) + tξ * Complex.I
    let w : ℂ := (95 / 100 : ℝ) + tw * Complex.I
    let z : ℂ := (1 / 6 + δ1 : ℝ) + tz * Complex.I
    have hξre : ξ.re = 1 + δ1 := by simp [ξ]
    have hwre : w.re = 95 / 100 := by simp [w]
    have hzre : z.re = 1 / 6 + δ1 := by simp [z]
    have hξim : ξ.im = tξ := by simp [ξ]
    have hwim : w.im = tw := by simp [w]
    have hzim : z.im = tz := by simp [z]
    have h := hcontrol Z hZ ξ w z
      (by simpa [hξre]) (by norm_num [hξre, δ1])
      (by simpa [hwre]) (by simpa [hzre])
    simpa [K, ξ, w, z, M, hξre, hwre, hzre, hξim, hwim, hzim,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hinnerZ (tξ tw : ℝ) :
      ‖vertical (1 / 6 + δ1) (fun z => K
        ((1 + δ1 : ℝ) + tξ * Complex.I) ((95 / 100 : ℝ) + tw * Complex.I) z)‖ ≤
        M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-2 : ℝ) := by
    let gZ : ℝ → ℝ := fun tz =>
      (M * (1 + |tw|) ^ (-2 : ℝ)) *
        (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv))
    have hgZ : Integrable gZ := by
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        (rows_integrable_shifted_gaussian_poly Aconv tξ hAconv).const_mul
          (M * (1 + |tw|) ^ (-2 : ℝ))
    have hgZ0 : ∀ tz, 0 ≤ gZ tz := by intro tz; dsimp [gZ]; positivity
    have hboundZ : ∀ tz : ℝ,
        ‖(fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I)
          ((95 / 100 : ℝ) + tw * Complex.I) z)
            ((1 / 6 + δ1 : ℝ) + tz * Complex.I)‖ ≤ gZ tz := by
      intro tz
      have h := hline tξ tw tz
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (1 / 6 + δ1)
      (fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I)
        ((95 / 100 : ℝ) + tw * Complex.I) z) gZ hgZ hgZ0 hboundZ
    calc
      _ ≤ ∫ tz : ℝ, gZ tz := hv
      _ = (M * (1 + |tw|) ^ (-2 : ℝ)) *
          ∫ tz : ℝ, Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by
            dsimp [gZ]
            rw [integral_const_mul]
      _ ≤ (M * (1 + |tw|) ^ (-2 : ℝ)) *
          (Cconv * (1 + |tξ|) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hconv tξ) (by positivity)
      _ = M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-2 : ℝ) := by ring
  have hinnerW (tξ : ℝ) :
      ‖vertical (95 / 100) (fun w => vertical (1 / 6 + δ1) (fun z =>
        K ((1 + δ1 : ℝ) + tξ * Complex.I) w z))‖ ≤
          M * Cconv * I * (1 + |tξ|) ^ (-2 : ℝ) := by
    let fW : ℂ → ℂ := fun w => vertical (1 / 6 + δ1) (fun z =>
      K ((1 + δ1 : ℝ) + tξ * Complex.I) w z)
    let gW : ℝ → ℝ := fun tw =>
      (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * (1 + |tw|) ^ (-2 : ℝ)
    have hgW : Integrable gW := by
      simpa [gW, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIint.const_mul (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ))
    have hgW0 : ∀ tw, 0 ≤ gW tw := by intro tw; dsimp [gW]; positivity
    have hboundW : ∀ tw : ℝ,
        ‖fW ((95 / 100 : ℝ) + tw * Complex.I)‖ ≤ gW tw := by
      intro tw
      have h := hinnerZ tξ tw
      simpa [fW, gW, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (95 / 100) fW gW hgW hgW0 hboundW
    calc
      _ ≤ ∫ tw : ℝ, gW tw := hv
      _ = (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * I := by
        dsimp [gW, I]
        rw [integral_const_mul]
      _ = M * Cconv * I * (1 + |tξ|) ^ (-2 : ℝ) := by ring
  have htriple :
      ‖tripleVertical (1 + δ1) (95 / 100) (1 / 6 + δ1) K‖ ≤ M * Cconv * I * I := by
    let fξ : ℂ → ℂ := fun ξ => vertical (95 / 100) (fun w =>
      vertical (1 / 6 + δ1) (fun z => K ξ w z))
    let gξ : ℝ → ℝ := fun tξ => (M * Cconv * I) * (1 + |tξ|) ^ (-2 : ℝ)
    have hgξ : Integrable gξ := by
      simpa [gξ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIint.const_mul (M * Cconv * I)
    have hgξ0 : ∀ tξ, 0 ≤ gξ tξ := by intro tξ; dsimp [gξ]; positivity
    have hboundξ : ∀ tξ : ℝ,
        ‖fξ ((1 + δ1 : ℝ) + tξ * Complex.I)‖ ≤ gξ tξ := by
      intro tξ
      have h := hinnerW tξ
      simpa [fξ, gξ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (1 + δ1) fξ gξ hgξ hgξ0 hboundξ
    calc
      _ ≤ ∫ tξ : ℝ, gξ tξ := hv
      _ = (M * Cconv * I) * I := by
        dsimp [gξ, I]
        rw [integral_const_mul]
      _ = M * Cconv * I * I := by ring
  let Cpre : ℝ := C0 * Cconv * I * I
  let C : ℝ := Cpre + 1
  have hCpre : 0 ≤ Cpre := by dsimp [Cpre]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hscale : M * Cconv * I * I =
      Cpre * Z ^ Estar (1 + δ1) (95 / 100) (1 / 6 + δ1) := by
    dsimp [M, Cpre]
    ring
  have htarget : 0 ≤ Z ^ (7 / 15 - 5 / 10000 : ℝ) :=
    Real.rpow_nonneg (by linarith : 0 ≤ Z) _
  have hCprele : Cpre ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  unfold principalRw
  change ‖tripleVertical (1 + δ1) (95 / 100) (1 / 6 + δ1) K‖ ≤
    C * Z ^ (7 / 15 - 5 / 10000 : ℝ)
  calc
    _ ≤ M * Cconv * I * I := htriple
    _ = Cpre * Z ^ Estar (1 + δ1) (95 / 100) (1 / 6 + δ1) := hscale
    _ ≤ Cpre * Z ^ (7 / 15 - 5 / 10000 : ℝ) := by
      apply mul_le_mul_of_nonneg_left ?_ hCpre
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z)
        rows_principalRw_exponent_bound
    _ ≤ C * Z ^ (7 / 15 - 5 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_right hCprele htarget

private theorem rows_vertical_const_mul (σ : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    vertical σ (fun z => c * f z) = c * vertical σ f := by
  unfold vertical
  rw [integral_const_mul]
  ring

private theorem rows_doubleVertical_const_mul (σξ σz : ℝ) (c : ℂ)
    (f : ℂ → ℂ → ℂ) :
    vertical σξ (fun ξ => vertical σz (fun z => c * f ξ z)) =
      c * vertical σξ (fun ξ => vertical σz (fun z => f ξ z)) := by
  have hfun : (fun ξ => vertical σz (fun z => c * f ξ z)) =
      fun ξ => c * vertical σz (fun z => f ξ z) := by
    funext ξ
    exact rows_vertical_const_mul σz c (f ξ)
  rw [hfun]
  exact rows_vertical_const_mul σξ c (fun ξ => vertical σz (fun z => f ξ z))

private theorem rows_principalRz_bound (hEuler : EulerHypotheses R η) (Z : ℝ)
    (hZ : 2 ≤ Z) :
    ∃ C : ℝ, 0 < C ∧
      ‖principalRz R sd W η U HA HC Z‖ ≤ C * Z ^ (7 / 15 - 5 / 10000 : ℝ) := by
  have hZpos : 0 < Z := by linarith
  obtain ⟨AF, CG, hAF, hCG, hGrowth⟩ := rows_principalLS_growth_off_one (HA := HA) (S := S)
  obtain ⟨Aconv, Cconv, hAconv, hCconv, hconv⟩ := zf_height_convolution
    (2 : ℝ) (by norm_num)
  let Aheight : ℝ := Aconv + AF + 2
  obtain ⟨Cht, hCht, hheight⟩ := zf_height_decay R sd W
    (1 + δ1) (1 + δ1) 1 1 (16 / 100) (16 / 100) Aheight
    (by norm_num [δ1]) (by norm_num) (by norm_num [δ1]) (by rfl)
    (by dsimp [Aheight]; linarith [hAF, hAconv])
  obtain ⟨CH, hCH, hHbound⟩ := (po_H_product R η U HC hEuler).2.2.2
    (1 : ℝ) (by norm_num)
  obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
  let Cinv : ℝ := (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re * 2 ^ S.Sf.card
  have hCinv : 0 ≤ Cinv := by
    have hζ := rows_small_dedekindZeta_real_nonneg (F := F) (1 + δ1) (by norm_num [δ1])
    have hζ' : 0 ≤ (NumberField.dedekindZeta F (1 + (δ1 : ℂ))).re := by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using hζ
    dsimp [Cinv]
    exact mul_nonneg hζ' (by positivity)
  let Cz : ℝ := CG * 6 ^ AF / (1 / 25 : ℝ)
  have hCz : 0 < Cz := by
    dsimp [Cz]
    exact div_pos (mul_pos hCG (Real.rpow_pos_of_pos (by norm_num : 0 < (6 : ℝ)) AF))
      (by norm_num)
  let B : ℝ := Cht * Cz * CH * Cinv * 2 ^ AF
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hIint : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hI0 : 0 ≤ I := by dsimp [I]; exact integral_nonneg fun t => by positivity
  have hxi (t : ℝ) : ((1 + δ1 : ℝ) + t * Complex.I).re = 1 + δ1 := by simp
  have hz (t : ℝ) : ((16 / 100 : ℝ) + t * Complex.I).re = 16 / 100 := by simp
  have hLSz (t : ℝ) :
      ‖HA.LS S 1 (6 * ((16 / 100 : ℝ) + t * Complex.I))‖ ≤
        Cz * (2 + |t|) ^ AF := by
    let z : ℂ := (16 / 100 : ℝ) + t * Complex.I
    have hzr : z.re = 16 / 100 := by simp [z]
    have h := hGrowth (6 * z) (by norm_num [hzr]) (by norm_num [hzr]) (by norm_num [hzr])
    have hre : (6 * z).re = 6 * z.re := by simp
    have him : |(6 * z).im| = 6 * |t| := by simp [z, abs_mul]
    rw [hre, hzr, him] at h
    have hgap : |6 * (16 / 100 : ℝ) - 1| = 1 / 25 := by norm_num
    rw [hgap] at h
    have hbase : 2 + 6 * |t| ≤ 6 * (2 + |t|) := by nlinarith [abs_nonneg t]
    have hpow : (2 + 6 * |t|) ^ AF ≤ (6 : ℝ) ^ AF * (2 + |t|) ^ AF := by
      calc
        _ ≤ (6 * (2 + |t|)) ^ AF := Real.rpow_le_rpow (by positivity) hbase hAF
        _ = (6 : ℝ) ^ AF * (2 + |t|) ^ AF := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
    calc
      _ ≤ CG * (2 + 6 * |t|) ^ AF / (1 / 25 : ℝ) := by simpa [z] using h
      _ ≤ CG * ((6 : ℝ) ^ AF * (2 + |t|) ^ AF) / (1 / 25 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCG.le) (by norm_num)
      _ = Cz * (2 + |t|) ^ AF := by dsimp [Cz]; ring
  have hH (tξ tz : ℝ) :
      ‖HC.H U.one ![(1 + δ1 : ℝ) + tξ * Complex.I, 1,
        (16 / 100 : ℝ) + tz * Complex.I]‖ ≤ CH := by
    have hregion : eulerNeighborhood ![(1 + δ1 : ℝ) + tξ * Complex.I, 1,
        (16 / 100 : ℝ) + tz * Complex.I] := by
      right
      change (998 / 1000 - 1 / 100000 < ((1 + δ1 : ℝ) + tξ * Complex.I).re ∧
        95 / 100 - 1 / 100000 < (1 : ℂ).re ∧
        16 / 100 - 1 / 100000 < ((16 / 100 : ℝ) + tz * Complex.I).re)
      constructor
      · have hδ : 0 < δ1 := by norm_num [δ1]
        rw [hxi tξ]
        linarith
      · constructor
        · norm_num
        · rw [hz tz]
          norm_num [δ1]
    have h := hHbound U.one ![(1 + δ1 : ℝ) + tξ * Complex.I, 1,
      (16 / 100 : ℝ) + tz * Complex.I] hregion
    simpa [U.q_one] using h
  have hInv (tξ : ℝ) :
      ‖(HA.LS S η ((1 + δ1 : ℝ) + tξ * Complex.I))⁻¹‖ ≤ Cinv := by
    have hs : 1 < ((1 + δ1 : ℝ) + tξ * Complex.I).re := by rw [hxi tξ]; norm_num [δ1]
    obtain ⟨_, hrecip⟩ := rows_LS_inverse_bound HA S η hEuler.1 fη hfη hs
    have hre : ((1 + δ1 : ℝ) + tξ * Complex.I).re = 1 + δ1 := hxi tξ
    rw [hre] at hrecip
    simpa [Cinv] using hrecip
  let F0 : ℂ → ℂ → ℂ := fun ξ z =>
    (Z : ℂ) ^ ((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z) *
      Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z *
        HA.LS S 1 (6 * z) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ
  let K : ℂ → ℂ → ℂ := fun ξ z => weightW1hat W 1 * F0 ξ z
  have hPow (ξ z : ℂ) :
      ‖(Z : ℂ) ^ ((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z)‖ =
        Z ^ (a / 2 + ξ.re - 1 + h0 * z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZpos]
    have hre : (((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z).re) =
        a / 2 + ξ.re - 1 + h0 * z.re := by
      simp <;> ring
    rw [hre]
  have hEstar (ξ z : ℂ) :
      a / 2 + ξ.re - 1 + h0 * z.re = Estar ξ.re 1 z.re := by
    simp [Estar] <;> ring
  have hKnorm (ξ z : ℂ) :
      ‖K ξ z‖ = Z ^ Estar ξ.re 1 z.re *
        ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W 1‖ *
        ‖HA.LS S 1 (6 * z)‖ * ‖HC.H U.one ![ξ, 1, z]‖ *
        ‖(HA.LS S η ξ)⁻¹‖ := by
    dsimp [K, F0]
    rw [div_eq_mul_inv]
    simp only [norm_mul, norm_inv]
    rw [hPow, hEstar]
    ring
  have hKline (tξ tz : ℝ) :
      ‖K ((1 + δ1 : ℝ) + tξ * Complex.I)
          ((16 / 100 : ℝ) + tz * Complex.I)‖ ≤
        B * Z ^ Estar (1 + δ1) 1 (16 / 100) *
          Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by
    let ξ : ℂ := (1 + δ1 : ℝ) + tξ * Complex.I
    let z : ℂ := (16 / 100 : ℝ) + tz * Complex.I
    have hξr : ξ.re = 1 + δ1 := by simp [ξ]
    have hzr : z.re = 16 / 100 := by simp [z]
    have hξim : ξ.im = tξ := by simp [ξ]
    have hzim : z.im = tz := by simp [z]
    have hh : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W 1‖ ≤
        Cht * Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aheight) := by
      have h := hheight ξ (1 : ℂ) z (by rw [hξr]) (by rw [hξr])
        (by norm_num) (by norm_num) (by rw [hzr] <;> norm_num)
        (by rw [hzr] <;> norm_num)
      simpa [hξr, hzr, hξim, hzim] using h
    have hZeta := hLSz tz
    have hH' := hH tξ tz
    have hInv' := hInv tξ
    have hAeq : Aheight = AF + (Aconv + 2) := by dsimp [Aheight]; ring
    have hpoly := rows_principal_absorb_poly tz AF (Aconv + 2) hAF
    have hpoly' : (1 + |tz|) ^ (-Aheight) * (2 + |tz|) ^ AF ≤
        2 ^ AF * (1 + |tz|) ^ (-Aconv) := by
      rw [hAeq]
      calc
        _ ≤ 2 ^ AF * (1 + |tz|) ^ (-(Aconv + 2)) := hpoly
        _ ≤ 2 ^ AF * (1 + |tz|) ^ (-Aconv) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by nlinarith [abs_nonneg tz]) (by linarith [hAconv]))
            (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)
    have hbound : ‖K ξ z‖ ≤
        Z ^ Estar ξ.re 1 z.re *
          (Cht * Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aheight)) *
          (Cz * (2 + |tz|) ^ AF) * CH * Cinv := by
      rw [hKnorm]
      rw [hξr, hzr]
      gcongr
    have htargetPow : Z ^ Estar ξ.re 1 z.re =
        Z ^ Estar (1 + δ1) 1 (16 / 100) := by
      rw [hξr, hzr]
    rw [htargetPow] at hbound
    have hB : B = Cht * Cz * CH * Cinv * 2 ^ AF := by rfl
    calc
      _ ≤ Z ^ Estar (1 + δ1) 1 (16 / 100) *
          (Cht * Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aheight)) *
          (Cz * (2 + |tz|) ^ AF) * CH * Cinv := hbound
      _ ≤ B * Z ^ Estar (1 + δ1) 1 (16 / 100) *
          Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by
        rw [hB]
        have hpoint : (1 + |tz|) ^ (-Aheight) * (2 + |tz|) ^ AF ≤
            2 ^ AF * (1 + |tz|) ^ (-Aconv) := hpoly'
        have hrest : 0 ≤ Z ^ Estar (1 + δ1) 1 (16 / 100) *
            Real.exp (-((tξ + tz) ^ 2)) * (Cht * Cz * CH * Cinv) := by positivity
        calc
          _ = (Z ^ Estar (1 + δ1) 1 (16 / 100) *
              Real.exp (-((tξ + tz) ^ 2)) * (Cht * Cz * CH * Cinv)) *
                ((1 + |tz|) ^ (-Aheight) * (2 + |tz|) ^ AF) := by ring
          _ ≤ (Z ^ Estar (1 + δ1) 1 (16 / 100) *
                Real.exp (-((tξ + tz) ^ 2)) * (Cht * Cz * CH * Cinv)) *
              (2 ^ AF * (1 + |tz|) ^ (-Aconv)) :=
                mul_le_mul_of_nonneg_left hpoint hrest
          _ = B * Z ^ Estar (1 + δ1) 1 (16 / 100) *
              Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by rw [hB]; ring
  let M : ℝ := B * Z ^ Estar (1 + δ1) 1 (16 / 100)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hinnerZ (tξ : ℝ) :
      ‖vertical (16 / 100) (fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I) z)‖ ≤
        M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) := by
    let gZ : ℝ → ℝ := fun tz => M * (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv))
    have hgZ : Integrable gZ := by
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm] using
        (rows_integrable_shifted_gaussian_poly Aconv tξ hAconv).const_mul M
    have hgZ0 : ∀ tz, 0 ≤ gZ tz := by intro tz; dsimp [gZ]; positivity
    have hboundZ : ∀ tz : ℝ, ‖(fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I) z)
        ((16 / 100 : ℝ) + tz * Complex.I)‖ ≤ gZ tz := by
      intro tz
      simpa [gZ, M, mul_assoc, mul_left_comm, mul_comm] using hKline tξ tz
    have hv := rows_vertical_norm_le_integral (16 / 100)
      (fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I) z) gZ hgZ hgZ0 hboundZ
    calc
      _ ≤ ∫ tz : ℝ, gZ tz := hv
      _ = M * ∫ tz : ℝ, Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by
        dsimp [gZ]
        rw [integral_const_mul]
      _ ≤ M * (Cconv * (1 + |tξ|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hconv tξ) (by positivity)
      _ = M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) := by ring
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hIint : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hI0 : 0 ≤ I := by dsimp [I]; exact integral_nonneg fun t => by positivity
  have hDoubleNorm :
      ‖vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z => K ξ z))‖ ≤
        M * Cconv * I := by
    let fξ : ℂ → ℂ := fun ξ => vertical (16 / 100) (fun z => K ξ z)
    let gξ : ℝ → ℝ := fun tξ => M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)
    have hgξ : Integrable gξ := by
      simpa [gξ, mul_assoc, mul_left_comm, mul_comm] using hIint.const_mul (M * Cconv)
    have hgξ0 : ∀ tξ, 0 ≤ gξ tξ := by intro tξ; dsimp [gξ]; positivity
    have hboundξ : ∀ tξ : ℝ, ‖fξ ((1 + δ1 : ℝ) + tξ * Complex.I)‖ ≤ gξ tξ := by
      intro tξ
      simpa [fξ, gξ, mul_assoc, mul_left_comm, mul_comm] using hinnerZ tξ
    have hv := rows_vertical_norm_le_integral (1 + δ1) fξ gξ hgξ hgξ0 hboundξ
    calc
      _ ≤ ∫ tξ : ℝ, gξ tξ := hv
      _ = M * Cconv * I := by dsimp [gξ, I]; rw [integral_const_mul]
  have hRzEq :
      principalRz R sd W η U HA HC Z =
        HA.RS S * vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z => K ξ z)) := by
    have hD := rows_doubleVertical_const_mul (1 + δ1) (16 / 100)
      (weightW1hat W 1) F0
    unfold principalRz
    calc
      _ = HA.RS S * (weightW1hat W 1 *
          vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z => F0 ξ z))) := by ring
      _ = _ := by rw [← hD]
  have hnormRz :
      ‖principalRz R sd W η U HA HC Z‖ ≤ ‖HA.RS S‖ * M * Cconv * I := by
    calc
      _ = ‖HA.RS S‖ *
          ‖vertical (1 + δ1) (fun ξ => vertical (16 / 100) (fun z => K ξ z))‖ := by
            rw [hRzEq, norm_mul]
      _ ≤ ‖HA.RS S‖ * (M * Cconv * I) :=
        mul_le_mul_of_nonneg_left hDoubleNorm (norm_nonneg _)
      _ = ‖HA.RS S‖ * M * Cconv * I := by ring
  let Cpre : ℝ := ‖HA.RS S‖ * B * Cconv * I
  let C : ℝ := Cpre + 1
  have hCpre : 0 ≤ Cpre := by dsimp [Cpre]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hscale : ‖HA.RS S‖ * M * Cconv * I =
      Cpre * Z ^ Estar (1 + δ1) 1 (16 / 100) := by
    dsimp [Cpre, M]
    ring
  have htarget : 0 ≤ Z ^ (7 / 15 - 5 / 10000 : ℝ) :=
    Real.rpow_nonneg (by linarith : 0 ≤ Z) _
  have hCprele : Cpre ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  calc
    _ ≤ Cpre * Z ^ Estar (1 + δ1) 1 (16 / 100) := by rw [← hscale]; exact hnormRz
    _ ≤ Cpre * Z ^ (7 / 15 - 5 / 10000 : ℝ) := by
      apply mul_le_mul_of_nonneg_left ?_ hCpre
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z)
      exact rows_principalRz_exponent_bound
    _ ≤ C * Z ^ (7 / 15 - 5 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_right hCprele htarget

private theorem rows_sol_simple_pole_shift (a b p : ℝ) (A F : ℂ → ℂ)
    (hap : a < p) (hpb : p < b)
    (hA : DifferentiableOn ℂ A {z : ℂ | a ≤ z.re ∧ z.re ≤ b})
    (hF : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → z ≠ p → F z = A z / (z - p))
    (ha : Integrable (fun t : ℝ => F ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => F ((b : ℂ) + t * Complex.I)))
    (hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      F ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b,
      F ((x : ℂ) + T * Complex.I)) atTop (𝓝 0)) :
    vertical b F = vertical a F + A p := by
  obtain ⟨G, hG, hreg⟩ := rows_regularize_simple_pole a b p A F hap hpb hA hF
  have hLine (x t : ℝ) :
      ((x : ℂ) + t * Complex.I) - p = ((x - p : ℝ) : ℂ) + t * Complex.I := by
    rw [Complex.ofReal_sub]
    ring
  have hKa : Integrable (fun t : ℝ =>
      Complex.exp ((((a : ℂ) + t * Complex.I) - p) ^ 2) /
        (((a : ℂ) + t * Complex.I) - p)) := by
    simpa only [hLine] using rows_gaussian_pole_line_integrable (a - p)
      (sub_ne_zero.mpr (ne_of_lt hap))
  have hKb : Integrable (fun t : ℝ =>
      Complex.exp ((((b : ℂ) + t * Complex.I) - p) ^ 2) /
        (((b : ℂ) + t * Complex.I) - p)) := by
    simpa only [hLine] using rows_gaussian_pole_line_integrable (b - p)
      (sub_ne_zero.mpr (ne_of_gt hpb))
  have hVa : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
      Complex.exp ((((a : ℂ) + t * Complex.I) - p) ^ 2) /
        (((a : ℂ) + t * Complex.I) - p)) = (-1 / 2 : ℂ) := by
    simpa only [vertical, hLine] using
      rows_vertical_gaussian_pole_neg (a - p) (sub_neg.mpr hap)
  have hVb : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ,
      Complex.exp ((((b : ℂ) + t * Complex.I) - p) ^ 2) /
        (((b : ℂ) + t * Complex.I) - p)) = (1 / 2 : ℂ) := by
    simpa only [vertical, hLine] using
      rows_vertical_gaussian_pole_pos (b - p) (sub_pos.mpr hpb)
  simpa only [vertical] using
    ArtinPrimitiveRoots.Proofs.a2_rows_sol.simple_pole_shift_of_regularization
      a b p F G (A p) (1 / (2 * Real.pi) : ℂ) hap hpb hG hreg
      ha hb hKa hKb hVa hVb hbot htop

private theorem rows_sol_principal_w_residue (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ z : ℂ)
    (hξlo : 1 + δ1 ≤ ξ.re) (hξhi : ξ.re ≤ 4)
    (hz : z.re = 1 / 6 + δ1) :
    vertical 4 (fun w => rowKernel R sd W η U HA HC U.one Z ξ w z) =
      vertical (95 / 100) (fun w => rowKernel R sd W η U HA HC U.one Z ξ w z) +
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
          HA.LS S 1 (6 * z) * HA.RS S * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ := by
  let strip : Set ℂ := {w | 95 / 100 ≤ w.re ∧ w.re ≤ 4}
  let GS : ℂ → ℂ := rows_principalRegularizedLS (HA := HA) (S := S)
  let K : ℂ → ℂ := fun w => rowKernel R sd W η U HA HC U.one Z ξ w z
  let Num : ℂ → ℂ := fun w =>
    mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * HA.LS S 1 (6 * z) *
      GS w * HC.H U.one ![ξ, w, z] / HA.LS S η ξ
  have hZpos : 0 < Z := by linarith
  obtain ⟨_, hWdiff, _, hWdecay, _⟩ := (po_weights_exist R sd).2 W
  have hGSdiff : Differentiable ℂ GS := by
    have hfactor : Differentiable ℂ (fun s : ℂ => ∏ v ∈ S.Sf,
        (1 - (1 : HeckeChar F).primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
      refine Differentiable.fun_finsetProd ?_
      intro v hv
      have hn : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt
          (NumberField.HeightOneSpectrum.one_lt_absNorm v)))
      have hpow : Differentiable ℂ (fun s : ℂ => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
        intro s
        exact (differentiable_id.neg s).const_cpow (Or.inl hn)
      exact (differentiable_const (1 : ℂ)).sub
        ((differentiable_const ((1 : HeckeChar F).primeValue v)).mul hpow)
    change Differentiable ℂ (HA.1.2 * fun s : ℂ => ∏ v ∈ S.Sf,
      (1 - (1 : HeckeChar F).primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    exact HA.2.2.2.2.1.mul hfactor
  have hMellin : Differentiable ℂ (fun w =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) := by
    have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZpos b).ne'
    have hY : Differentiable ℂ (fun w : ℂ => ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := by
      intro w
      exact ((differentiable_id.sub_const (1 : ℂ)) w).const_cpow (Or.inl hYbase)
    unfold mellinWeight
    exact (((((differentiable_const _).mul (differentiable_const _)).mul hY).mul
      (differentiable_const _)).mul (differentiable_const _)).mul hWdiff
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun w => ![ξ, w, z]
  have hpmap : Differentiable ℂ pmap := by
    intro w
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hregion (w : ℂ) (hw : w ∈ strip) : eulerNeighborhood ![ξ, w, z] := by
    right
    change 998 / 1000 - 1 / 100000 < ξ.re ∧
      95 / 100 - 1 / 100000 < w.re ∧ 16 / 100 - 1 / 100000 < z.re
    refine ⟨lt_of_lt_of_le (by norm_num [δ1]) hξlo,
      lt_of_lt_of_le (by norm_num) hw.1, ?_⟩
    rw [hz]
    norm_num [δ1]
  have hHC : DifferentiableOn ℂ (fun w => HC.H U.one ![ξ, w, z]) strip :=
    (hHP.2.1 U.one).comp hpmap.differentiableOn (fun w hw => hregion w hw)
  have hNumdiff : DifferentiableOn ℂ Num strip := by
    dsimp only [Num]
    simp only [div_eq_mul_inv]
    exact (((hMellin.differentiableOn.mul (differentiable_const _).differentiableOn).mul
      hGSdiff.differentiableOn).mul hHC).mul (differentiable_const _).differentiableOn
  have hGSquot (w : ℂ) (hw : w ≠ 1) : GS w / (w - 1) = HA.LS S 1 w := by
    apply (div_eq_iff (sub_ne_zero.mpr hw)).mpr
    change rows_principalRegularizedLS (HA := HA) (S := S) w = HA.LS S 1 w * (w - 1)
    rw [rows_principalRegularizedLS_eq (HA := HA) (S := S) w hw]
    ring
  have hrep (w : ℂ) (_ : 95 / 100 ≤ w.re) (_ : w.re ≤ 4) (hw : w ≠ 1) :
      K w = Num w / (w - 1) := by
    dsimp only [K]
    rw [rows_principalKernel_eq R sd W η U HA HC]
    calc
      _ = mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z * HA.LS S 1 (6 * z) *
          (GS w / (w - 1)) * HC.H U.one ![ξ, w, z] / HA.LS S η ξ := by rw [hGSquot w hw]
      _ = _ := by dsimp only [Num]; simp only [div_eq_mul_inv]; ring
  obtain ⟨AF, CG, hAF, hCG, hGrowth⟩ := rows_principalRegularizedLS_growth (HA := HA) (S := S)
  obtain ⟨CW, hCW, hWeight⟩ := hWdecay (95 / 100) 4 (AF + 2)
    (by norm_num) (by linarith)
  obtain ⟨CH, hCH, hHbound⟩ := hHP.2.2.2 (1 : ℝ) (by norm_num)
  let P : ℝ := ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z‖
  let CZ : ℝ := ‖HA.LS S 1 (6 * z)‖
  let CI : ℝ := ‖(HA.LS S η ξ)⁻¹‖
  let B0 : ℝ := Z ^ Estar ξ.re 4 z.re * P * CW * CZ * (20 * CG) * CH * CI
  let C0 : ℝ := B0 * 2 ^ AF
  let E : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  have hB0 : 0 ≤ B0 := by dsimp [B0, P, CZ, CI]; positivity
  have hLS (w : ℂ) (hw : w ∈ strip) (hgap : 1 / 20 ≤ ‖w - 1‖) :
      ‖HA.LS S 1 w‖ ≤ (20 * CG) * (2 + |w.im|) ^ AF := by
    have hwne : w ≠ 1 := by
      intro h
      norm_num [h] at hgap
    rw [← hGSquot w hwne, norm_div]
    have hgrow := hGrowth w (le_trans (by norm_num) hw.1) hw.2
    calc
      _ ≤ (CG * (2 + |w.im|) ^ AF) / ‖w - 1‖ :=
        div_le_div_of_nonneg_right hgrow (norm_nonneg _)
      _ ≤ (CG * (2 + |w.im|) ^ AF) / (1 / 20 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hgap
      _ = _ := by ring
  have hGapEnd (x t : ℝ) (hx : x = 95 / 100 ∨ x = 4) :
      1 / 20 ≤ ‖((x : ℂ) + t * Complex.I) - 1‖ := by
    calc
      _ ≤ |x - 1| := by rcases hx with rfl | rfl <;> norm_num
      _ ≤ _ := by simpa using Complex.abs_re_le_norm (((x : ℂ) + t * Complex.I) - 1)
  have hGapHigh (x t : ℝ) (ht : 1 ≤ |t|) :
      1 / 20 ≤ ‖((x : ℂ) + t * Complex.I) - 1‖ := by
    calc
      _ ≤ |t| := by linarith
      _ ≤ _ := by simpa using Complex.abs_im_le_norm (((x : ℂ) + t * Complex.I) - 1)
  have hpoint (x t : ℝ) (hx : x ∈ Icc (95 / 100 : ℝ) 4)
      (hgap : 1 / 20 ≤ ‖((x : ℂ) + t * Complex.I) - 1‖) :
      ‖K ((x : ℂ) + t * Complex.I)‖ ≤ C0 * E t := by
    let w : ℂ := (x : ℂ) + t * Complex.I
    have hwre : w.re = x := by simp [w]
    have hwim : w.im = t := by simp [w]
    have hw : w ∈ strip := by change 95 / 100 ≤ w.re ∧ w.re ≤ 4; simpa [hwre] using hx
    have hM : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
        (P * CW) * (1 + |t|) ^ (-(AF + 2)) := by
      rw [norm_mul]
      calc
        _ ≤ P * (CW * (1 + |t|) ^ (-(AF + 2))) :=
          mul_le_mul_of_nonneg_left (hWeight x t hx.1 hx.2) (norm_nonneg _)
        _ = _ := by ring
    have hHw : ‖HC.H U.one ![ξ, w, z]‖ ≤ CH := by
      simpa [U.q_one] using hHbound U.one ![ξ, w, z] (hregion w hw)
    have hLs := hLS w hw hgap
    rw [hwim] at hLs
    have hbound := rows_principalKernel_norm_bound_of_factors R sd W η U HA HC Z hZpos ξ w z
      ((P * CW) * (1 + |t|) ^ (-(AF + 2))) CZ
      ((20 * CG) * (2 + |t|) ^ AF) CH CI
      (by dsimp [P]; positivity) (norm_nonneg _) (by positivity) hCH.le (norm_nonneg _)
      hM le_rfl hLs hHw le_rfl
    have hPow : Z ^ Estar ξ.re w.re z.re ≤ Z ^ Estar ξ.re 4 z.re := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z)
      rw [hwre]
      norm_num [Estar, a, b, h0]
      nlinarith [hx.2]
    calc
      _ ≤ Z ^ Estar ξ.re w.re z.re * ((P * CW) * (1 + |t|) ^ (-(AF + 2))) *
          CZ * ((20 * CG) * (2 + |t|) ^ AF) * CH * CI := hbound
      _ ≤ Z ^ Estar ξ.re 4 z.re * ((P * CW) * (1 + |t|) ^ (-(AF + 2))) *
          CZ * ((20 * CG) * (2 + |t|) ^ AF) * CH * CI := by gcongr
      _ = B0 * ((1 + |t|) ^ (-(AF + 2)) * (2 + |t|) ^ AF) := by dsimp only [B0]; ring
      _ ≤ B0 * (2 ^ AF * (1 + |t|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rows_principal_absorb_poly t AF 2 hAF) hB0
      _ = C0 * E t := by dsimp only [C0, E]; ring
  have hEint : Integrable E := rows_integrable_poly_decay (p := 2) (by norm_num)
  have hEndpoint (x : ℝ) (hx : x ∈ Icc (95 / 100 : ℝ) 4) (hxe : x = 95 / 100 ∨ x = 4) :
      Integrable (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) := by
    have hNline : Continuous (fun t : ℝ => Num ((x : ℂ) + t * Complex.I)) := by
      apply continuousOn_univ.mp
      apply hNumdiff.continuousOn.comp
        (by fun_prop : ContinuousOn (fun t : ℝ => (x : ℂ) + t * Complex.I) univ)
      intro t ht
      change 95 / 100 ≤ ((x : ℂ) + t * Complex.I).re ∧ ((x : ℂ) + t * Complex.I).re ≤ 4
      simpa using hx
    have hden (t : ℝ) : ((x : ℂ) + t * Complex.I) - 1 ≠ 0 := by
      intro h
      have hg := hGapEnd x t hxe
      rw [h] at hg
      norm_num at hg
    have hEq : (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) =
        fun t : ℝ => Num ((x : ℂ) + t * Complex.I) / (((x : ℂ) + t * Complex.I) - 1) := by
      funext t
      exact hrep _ (by simpa using hx.1) (by simpa using hx.2) (sub_ne_zero.mp (hden t))
    have hCont : Continuous (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) := by
      rw [hEq]
      exact hNline.div (by fun_prop) hden
    apply (hEint.const_mul C0).mono' hCont.aestronglyMeasurable
    filter_upwards [] with t
    exact hpoint x t hx (hGapEnd x t hxe)
  have hbase : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop := by
    have hineq (t : ℝ) : t ≤ 1 + |t| := by linarith [le_abs_self t]
    exact tendsto_atTop_mono hineq tendsto_id
  have hElim : Tendsto E atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp hbase
  have hLim : Tendsto (fun T : ℝ => C0 * E T * |4 - (95 / 100 : ℝ)|) atTop (𝓝 0) := by
    simpa using (hElim.const_mul C0).mul_const |4 - (95 / 100 : ℝ)|
  have hBound (T : ℝ) (hT : 1 ≤ |T|) :
      ‖∫ x : ℝ in (95 / 100)..4, K ((x : ℂ) + T * Complex.I)‖ ≤
        C0 * E T * |4 - (95 / 100 : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc (95 / 100 : ℝ) 4 := by
      simpa [uIcc_of_le (by norm_num : (95 / 100 : ℝ) ≤ 4)] using uIoc_subset_uIcc hx
    exact hpoint x T hx' (hGapHigh x T hT)
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in (95 / 100)..4,
      K ((x : ℂ) + T * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact hBound T (by rwa [abs_of_nonneg (by linarith)])
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in (95 / 100)..4,
      K ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hb := hBound (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT)
    simpa only [Complex.ofReal_neg, E, abs_neg] using hb
  have hshift := rows_sol_simple_pole_shift (95 / 100) 4 1 Num K
    (by norm_num) (by norm_num) hNumdiff hrep
    (hEndpoint (95 / 100) ⟨le_rfl, by norm_num⟩ (Or.inl rfl))
    (hEndpoint 4 ⟨by norm_num, le_rfl⟩ (Or.inr rfl)) hbot htop
  have hNumone : Num 1 = mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
      HA.LS S 1 (6 * z) * HA.RS S * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ := by
    change mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z * HA.LS S 1 (6 * z) *
      rows_principalRegularizedLS (HA := HA) (S := S) 1 * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ = _
    rw [rows_principalRegularizedLS_at_one]
  simpa only [K, Complex.ofReal_one, hNumone] using hshift

private theorem rows_sol_principal_z_residue (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ : ℂ)
    (hξlo : 1 + δ1 ≤ ξ.re) (hξhi : ξ.re ≤ 4) :
    vertical (1 / 6 + δ1) (fun z =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
        HA.LS S 1 (6 * z) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ) =
      vertical (16 / 100) (fun z =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
          HA.LS S 1 (6 * z) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ) +
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 (1 / 6) *
          (HA.RS S / 6) * HC.H U.one ![ξ, 1, 1 / 6] / HA.LS S η ξ := by
  let strip : Set ℂ := {z | 16 / 100 ≤ z.re ∧ z.re ≤ 1 / 6 + δ1}
  let GS : ℂ → ℂ := rows_principalRegularizedLS (HA := HA) (S := S)
  let K : ℂ → ℂ := fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
    HA.LS S 1 (6 * z) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ
  let Num : ℂ → ℂ := fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
    (GS (6 * z) / 6) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ
  have hZpos : 0 < Z := by linarith
  obtain ⟨hMdiff, _, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hGSdiff : Differentiable ℂ GS := by
    have hfactor : Differentiable ℂ (fun s : ℂ => ∏ v ∈ S.Sf,
        (1 - (1 : HeckeChar F).primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) := by
      refine Differentiable.fun_finsetProd ?_
      intro v hv
      have hn : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt
          (NumberField.HeightOneSpectrum.one_lt_absNorm v)))
      have hpow : Differentiable ℂ (fun s : ℂ => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
        intro s
        exact (differentiable_id.neg s).const_cpow (Or.inl hn)
      exact (differentiable_const (1 : ℂ)).sub
        ((differentiable_const ((1 : HeckeChar F).primeValue v)).mul hpow)
    change Differentiable ℂ (HA.1.2 * fun s : ℂ => ∏ v ∈ S.Sf,
      (1 - (1 : HeckeChar F).primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    exact HA.2.2.2.2.1.mul hfactor
  have hMstrip : DifferentiableOn ℂ (weightM R sd W) strip := by
    apply hMdiff.mono
    intro z hz
    exact lt_of_lt_of_le (by norm_num) hz.1
  have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZpos a).ne'
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
  have hXexp : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) := by fun_prop
  have hX : Differentiable ℂ (fun z : ℂ =>
      ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := by
    intro z
    exact (hXexp z).const_cpow (Or.inl hXbase)
  have hZexp : Differentiable ℂ (fun z : ℂ => ξ + z - 1) := by fun_prop
  have hZpow : Differentiable ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) := by
    intro z
    exact (hZexp z).const_cpow (Or.inl hZbase)
  have hGauss : Differentiable ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) := by fun_prop
  have hMellin : DifferentiableOn ℂ (fun z =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z) strip := by
    unfold mellinWeight
    exact (((((hX.differentiableOn.mul hZpow.differentiableOn).mul
      (differentiable_const _).differentiableOn).mul hGauss.differentiableOn).mul
      hMstrip).mul (differentiable_const _).differentiableOn)
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℂ → Triple := fun z => ![ξ, 1, z]
  have hpmap : Differentiable ℂ pmap := by
    intro z
    apply differentiableAt_pi.2
    intro j
    fin_cases j <;> simp [pmap] <;> fun_prop
  have hregion (z : ℂ) (hz : z ∈ strip) : eulerNeighborhood ![ξ, 1, z] := by
    right
    change 998 / 1000 - 1 / 100000 < ξ.re ∧
      95 / 100 - 1 / 100000 < (1 : ℂ).re ∧ 16 / 100 - 1 / 100000 < z.re
    exact ⟨lt_of_lt_of_le (by norm_num [δ1]) hξlo, by norm_num,
      lt_of_lt_of_le (by norm_num) hz.1⟩
  have hHC : DifferentiableOn ℂ (fun z => HC.H U.one ![ξ, 1, z]) strip :=
    (hHP.2.1 U.one).comp hpmap.differentiableOn (fun z hz => hregion z hz)
  have hGSscale : Differentiable ℂ (fun z : ℂ => GS (6 * z) / 6) :=
    (hGSdiff.comp (by fun_prop)).div_const 6
  have hNumdiff : DifferentiableOn ℂ Num strip := by
    dsimp only [Num]
    simp only [div_eq_mul_inv]
    exact ((hMellin.mul hGSscale.differentiableOn).mul hHC).mul
      (differentiable_const _).differentiableOn
  have hGSquot (z : ℂ) (hz : z ≠ 1 / 6) :
      (GS (6 * z) / 6) / (z - 1 / 6) = HA.LS S 1 (6 * z) := by
    have hsne : 6 * z ≠ 1 := by
      intro h
      apply hz
      linear_combination (1 / 6 : ℂ) * h
    apply (div_eq_iff (sub_ne_zero.mpr hz)).mpr
    change rows_principalRegularizedLS (HA := HA) (S := S) (6 * z) / 6 = _
    rw [rows_principalRegularizedLS_eq (HA := HA) (S := S) (6 * z) hsne]
    ring
  have hrep (z : ℂ) (_ : 16 / 100 ≤ z.re) (_ : z.re ≤ 1 / 6 + δ1)
      (hz : z ≠ (1 / 6 : ℝ)) : K z = Num z / (z - (1 / 6 : ℝ)) := by
    have hz' : z ≠ 1 / 6 := by simpa using hz
    calc
      K z = mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
          ((GS (6 * z) / 6) / (z - 1 / 6)) * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ := by
        dsimp only [K]
        rw [hGSquot z hz']
      _ = _ := by
        dsimp only [Num]
        rw [show ((1 / 6 : ℝ) : ℂ) = (1 / 6 : ℂ) by norm_num]
        simp only [div_eq_mul_inv]
        ring
  obtain ⟨AF, CG, hAF, hCG, hGrowth⟩ := rows_principalRegularizedLS_growth (HA := HA) (S := S)
  obtain ⟨CM, hCM, hWeight⟩ := zf_height_decay R sd W
    (1 + δ1) 4 1 1 (16 / 100) (1 / 6 + δ1) (AF + 2)
    (by norm_num [δ1]) le_rfl (by norm_num) (by norm_num [δ1]) (by linarith)
  obtain ⟨CH, hCH, hHbound⟩ := hHP.2.2.2 (1 : ℝ) (by norm_num)
  let CI : ℝ := ‖(HA.LS S η ξ)⁻¹‖
  let CL : ℝ := CG / δ1 * 6 ^ AF
  let B0 : ℝ := Z ^ Estar ξ.re 1 (1 / 6 + δ1) * CM * CL * CH * CI
  let C0 : ℝ := B0 * 2 ^ AF
  let E : ℝ → ℝ := fun t => (1 + |t|) ^ (-2 : ℝ)
  have hδ : 0 < δ1 := by norm_num [δ1]
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0, CI]; positivity
  have hLS (z : ℂ) (hz : z ∈ strip) (hgap : δ1 ≤ ‖6 * z - 1‖) :
      ‖HA.LS S 1 (6 * z)‖ ≤ CL * (2 + |z.im|) ^ AF := by
    have hsne : 6 * z ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hgap
      linarith
    have hquot : GS (6 * z) / (6 * z - 1) = HA.LS S 1 (6 * z) := by
      apply (div_eq_iff (sub_ne_zero.mpr hsne)).mpr
      change rows_principalRegularizedLS (HA := HA) (S := S) (6 * z) = _
      rw [rows_principalRegularizedLS_eq (HA := HA) (S := S) (6 * z) hsne]
      ring
    have hslo : 3 / 1000 ≤ (6 * z).re := by simp; nlinarith [hz.1]
    have hshi : (6 * z).re ≤ 4 := by simp; nlinarith [hz.2, (show δ1 < 1 / 6 by norm_num [δ1])]
    have hgrow := hGrowth (6 * z) hslo hshi
    have hscale : (2 + |(6 * z).im|) ^ AF ≤ 6 ^ AF * (2 + |z.im|) ^ AF := by
      calc
        _ ≤ (6 * (2 + |z.im|)) ^ AF := by
          apply Real.rpow_le_rpow (by positivity) ?_ hAF
          have him : (6 * z).im = 6 * z.im := by simp
          rw [him, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
          linarith
        _ = _ := Real.mul_rpow (by norm_num) (by positivity)
    rw [← hquot, norm_div]
    calc
      _ ≤ (CG * (2 + |(6 * z).im|) ^ AF) / ‖6 * z - 1‖ :=
        div_le_div_of_nonneg_right hgrow (norm_nonneg _)
      _ ≤ (CG * (2 + |(6 * z).im|) ^ AF) / δ1 :=
        div_le_div_of_nonneg_left (by positivity) hδ hgap
      _ ≤ (CG * (6 ^ AF * (2 + |z.im|) ^ AF)) / δ1 := by gcongr
      _ = _ := by dsimp only [CL]; ring
  have hGapEnd (x t : ℝ) (hx : x = 16 / 100 ∨ x = 1 / 6 + δ1) :
      δ1 ≤ ‖6 * ((x : ℂ) + t * Complex.I) - 1‖ := by
    calc
      _ ≤ |6 * x - 1| := by rcases hx with rfl | rfl <;> norm_num [δ1]
      _ ≤ _ := by simpa using Complex.abs_re_le_norm (6 * ((x : ℂ) + t * Complex.I) - 1)
  have hGapHigh (x t : ℝ) (ht : 1 ≤ |t|) :
      δ1 ≤ ‖6 * ((x : ℂ) + t * Complex.I) - 1‖ := by
    calc
      _ ≤ |6 * t| := by rw [abs_mul]; norm_num; linarith [show δ1 ≤ 1 by norm_num [δ1]]
      _ ≤ _ := by simpa using Complex.abs_im_le_norm (6 * ((x : ℂ) + t * Complex.I) - 1)
  have hpoint (x t : ℝ) (hx : x ∈ Icc (16 / 100 : ℝ) (1 / 6 + δ1))
      (hgap : δ1 ≤ ‖6 * ((x : ℂ) + t * Complex.I) - 1‖) :
      ‖K ((x : ℂ) + t * Complex.I)‖ ≤ C0 * E t := by
    let z : ℂ := (x : ℂ) + t * Complex.I
    have hzre : z.re = x := by simp [z]
    have hzim : z.im = t := by simp [z]
    have hz : z ∈ strip := by change 16 / 100 ≤ z.re ∧ z.re ≤ 1 / 6 + δ1; simpa [hzre] using hx
    have hM : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W 1‖ ≤
        CM * (1 + |t|) ^ (-(AF + 2)) := by
      have hw := hWeight ξ 1 z hξlo hξhi (by norm_num) (by norm_num) hz.1 hz.2
      simp only [Complex.one_im, abs_zero, add_zero, Real.one_rpow, mul_one, hzim] at hw
      calc
        _ ≤ CM * Real.exp (-((ξ.im + t) ^ 2)) * (1 + |t|) ^ (-(AF + 2)) := hw
        _ ≤ CM * 1 * (1 + |t|) ^ (-(AF + 2)) := by
          gcongr
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
        _ = _ := by ring
    have hHz : ‖HC.H U.one ![ξ, 1, z]‖ ≤ CH := by
      simpa [U.q_one] using hHbound U.one ![ξ, 1, z] (hregion z hz)
    have hLs := hLS z hz hgap
    rw [hzim] at hLs
    have hPow : Z ^ Estar ξ.re 1 z.re ≤ Z ^ Estar ξ.re 1 (1 / 6 + δ1) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z)
      rw [hzre]
      norm_num [Estar, a, b, h0]
      nlinarith [hx.2]
    calc
      ‖K z‖ = Z ^ Estar ξ.re 1 z.re *
          ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W 1‖ *
          ‖HA.LS S 1 (6 * z)‖ * ‖HC.H U.one ![ξ, 1, z]‖ * CI := by
        dsimp only [K, CI]
        rw [div_eq_mul_inv]
        simp only [norm_mul, rows_mellinWeight_norm R sd W Z hZpos, Complex.one_re]
      _ ≤ Z ^ Estar ξ.re 1 (1 / 6 + δ1) * (CM * (1 + |t|) ^ (-(AF + 2))) *
          (CL * (2 + |t|) ^ AF) * CH * CI := by gcongr
      _ = B0 * ((1 + |t|) ^ (-(AF + 2)) * (2 + |t|) ^ AF) := by dsimp only [B0]; ring
      _ ≤ B0 * (2 ^ AF * (1 + |t|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rows_principal_absorb_poly t AF 2 hAF) hB0
      _ = C0 * E t := by dsimp only [C0, E]; ring
  have hEint : Integrable E := rows_integrable_poly_decay (p := 2) (by norm_num)
  have hEndpoint (x : ℝ) (hx : x ∈ Icc (16 / 100 : ℝ) (1 / 6 + δ1)) (hxe : x = 16 / 100 ∨ x = 1 / 6 + δ1) :
      Integrable (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) := by
    have hNline : Continuous (fun t : ℝ => Num ((x : ℂ) + t * Complex.I)) := by
      apply continuousOn_univ.mp
      apply hNumdiff.continuousOn.comp
        (by fun_prop : ContinuousOn (fun t : ℝ => (x : ℂ) + t * Complex.I) univ)
      intro t ht
      change 16 / 100 ≤ ((x : ℂ) + t * Complex.I).re ∧ ((x : ℂ) + t * Complex.I).re ≤ 1 / 6 + δ1
      simpa using hx
    have hden (t : ℝ) : ((x : ℂ) + t * Complex.I) - (1 / 6 : ℂ) ≠ 0 := by
      intro h
      have hs : 6 * ((x : ℂ) + t * Complex.I) - 1 = 0 := by
        linear_combination (6 : ℂ) * h
      have hg := hGapEnd x t hxe
      rw [hs, norm_zero] at hg
      norm_num [δ1] at hg
    have hEq : (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) =
        fun t : ℝ => Num ((x : ℂ) + t * Complex.I) / (((x : ℂ) + t * Complex.I) - (1 / 6 : ℂ)) := by
      funext t
      simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
        hrep _ (by simpa using hx.1) (by simpa using hx.2)
          (by simpa using sub_ne_zero.mp (hden t))
    have hCont : Continuous (fun t : ℝ => K ((x : ℂ) + t * Complex.I)) := by
      rw [hEq]
      exact hNline.div (by fun_prop) hden
    apply (hEint.const_mul C0).mono' hCont.aestronglyMeasurable
    filter_upwards [] with t
    exact hpoint x t hx (hGapEnd x t hxe)
  have hbase : Tendsto (fun t : ℝ => 1 + |t|) atTop atTop := by
    have hineq (t : ℝ) : t ≤ 1 + |t| := by linarith [le_abs_self t]
    exact tendsto_atTop_mono hineq tendsto_id
  have hElim : Tendsto E atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 : ℝ))).comp hbase
  have hLim : Tendsto (fun T : ℝ => C0 * E T * |(1 / 6 + δ1) - (16 / 100 : ℝ)|) atTop (𝓝 0) := by
    simpa using (hElim.const_mul C0).mul_const |(1 / 6 + δ1) - (16 / 100 : ℝ)|
  have hBound (T : ℝ) (hT : 1 ≤ |T|) :
      ‖∫ x : ℝ in (16 / 100)..(1 / 6 + δ1), K ((x : ℂ) + T * Complex.I)‖ ≤
        C0 * E T * |(1 / 6 + δ1) - (16 / 100 : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Icc (16 / 100 : ℝ) (1 / 6 + δ1) := by
      have hxmem := uIoc_subset_uIcc hx
      rw [uIcc_of_le (by norm_num [δ1] : (16 / 100 : ℝ) ≤ 1 / 6 + δ1)] at hxmem
      exact hxmem
    exact hpoint x T hx' (hGapHigh x T hT)
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in (16 / 100)..(1 / 6 + δ1),
      K ((x : ℂ) + T * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact hBound T (by rwa [abs_of_nonneg (by linarith)])
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in (16 / 100)..(1 / 6 + δ1),
      K ((x : ℂ) + (-T) * Complex.I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hLim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hb := hBound (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT)
    simpa only [Complex.ofReal_neg, E, abs_neg] using hb
  have hshift := rows_sol_simple_pole_shift (16 / 100) (1 / 6 + δ1) (1 / 6) Num K
    (by norm_num) (by norm_num [δ1]) hNumdiff hrep
    (hEndpoint (16 / 100) ⟨le_rfl, by norm_num [δ1]⟩ (Or.inl rfl))
    (hEndpoint (1 / 6 + δ1) ⟨by norm_num [δ1], le_rfl⟩ (Or.inr rfl)) hbot htop
  have hNumpole : Num (1 / 6) = mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 (1 / 6) *
      (HA.RS S / 6) * HC.H U.one ![ξ, 1, 1 / 6] / HA.LS S η ξ := by
    dsimp only [Num, GS]
    norm_num only [show (6 : ℂ) * (1 / 6) = 1 by norm_num]
    rw [rows_principalRegularizedLS_at_one]
  simpa only [K, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, hNumpole] using hshift

private theorem rows_sol_mellin_w_one (Z : ℝ) (hZ : 0 < Z) (ξ z : ℂ) :
    mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z =
      (Z : ℂ) ^ ((a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z) *
        Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W 1 := by
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hlog : (Complex.log (Z : ℂ) * (a : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hZ.le]
    simp
  have hXpow : ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z) =
      (Z : ℂ) ^ ((a : ℂ) * ((1 / 2 : ℂ) - z)) := by
    rw [Complex.ofReal_cpow hZ.le a]
    exact (Complex.cpow_mul (x := (Z : ℂ)) (y := (a : ℂ)) ((1 / 2 : ℂ) - z)
      (by rw [hlog]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hlog]; exact Real.pi_pos.le)).symm
  have hExponent : (a : ℂ) * ((1 / 2 : ℂ) - z) + (ξ + z - 1) =
      (a : ℂ) / 2 + ξ - 1 + (h0 : ℂ) * z := by
    simp only [h0, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  unfold mellinWeight
  rw [hXpow]
  simp only [sub_self, Complex.cpow_zero, mul_one]
  rw [← Complex.cpow_add _ _ hZbase, hExponent]

private theorem rows_sol_principal_right_kernel_control
    (hEuler : EulerHypotheses R η) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ ξ w z : ℂ,
      1 + δ1 ≤ ξ.re → ξ.re ≤ 4 → w.re = 4 →
      1 / 6 + δ1 ≤ z.re → z.re ≤ 2 →
        ‖rowKernel R sd W η U HA HC U.one Z ξ w z‖ ≤
          C * Z ^ Estar ξ.re w.re z.re *
            Real.exp (-((ξ.im + z.im) ^ 2)) *
              (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by
  let σ : ℝ := 1 + 6 * δ1
  have hσ : 1 < σ := by norm_num [σ, δ1]
  let CS : ℝ := 2 ^ S.Sf.card
  let Cζ : ℝ := (NumberField.dedekindZeta F (σ : ℂ)).re
  let CZ : ℝ := Cζ * CS
  have hCζ : 0 ≤ Cζ := rows_small_dedekindZeta_real_nonneg (F := F) σ hσ
  have hCZ : 0 ≤ CZ := by dsimp [CZ, CS]; positivity
  have hOne : IsOfFinOrder (1 : HeckeChar F) := by simp
  have hOnePrim : IsPrimitiveConductor (1 : HeckeChar F) ⊤ := by
    refine ⟨by simp, ?_, ?_⟩
    · intro v x hx hxinv hval
      change (1 : HeckeChar F).loc v x = 1
      simp [HeckeChar.loc]
    · intro g hg hgc
      have hnorm : Ideal.absNorm g ≠ 0 := by
        intro h
        exact hg (Ideal.absNorm_eq_zero_iff.mp h)
      simpa using (Nat.one_le_iff_ne_zero.mpr hnorm)
  obtain ⟨m, ψ, hseries⟩ :=
    rows_heckeLSeries_eq_ray (1 : HeckeChar F) hOne ⊤ hOnePrim
  have hPrincipal (s : ℂ) (hs : σ ≤ s.re) : ‖HA.LS S 1 s‖ ≤ CZ := by
    have hsone : 1 < s.re := lt_of_lt_of_le hσ hs
    have hRay := Hecke.norm_LSeriesRay_le (K := F) (s := s) ψ hsone
    have hcomplete : HA.L 1 s = Hecke.LSeriesRay ψ s := by
      calc
        HA.L 1 s = heckeLSeries (1 : HeckeChar F) s := HA.2.1 1 s hsone
        _ = Hecke.LSeriesRay ψ s := hseries s hsone
    have hfactor := rows_principal_omittedFactors_norm_le (S := S) s
      (by linarith : 0 < s.re)
    have hLS : HA.LS S 1 s = Hecke.LSeriesRay ψ s *
        ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
      unfold HeckeAnalysis.LS
      rw [hcomplete]
    have hζ : (NumberField.dedekindZeta F (s.re : ℂ)).re ≤ Cζ :=
      rows_small_dedekindZeta_real_antitone (F := F) hσ hs
    have hRayUpper : ‖Hecke.LSeriesRay ψ s‖ ≤ Cζ := hRay.1.trans hζ
    calc
      _ = ‖Hecke.LSeriesRay ψ s‖ *
          ‖∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))‖ := by rw [hLS, norm_mul]
      _ ≤ Cζ * CS := mul_le_mul hRayUpper hfactor (norm_nonneg _) hCζ
      _ = CZ := rfl
  let CW : ℝ := rows_absNorm_majorant (F := F) * CS
  have hCW : 0 ≤ CW := by
    exact mul_nonneg rows_absNorm_majorant_nonneg (by dsimp [CS]; positivity)
  obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
  let CI : ℝ := (NumberField.dedekindZeta F ((1 + δ1 : ℝ) : ℂ)).re * CS
  have hCI : 0 ≤ CI := by
    exact mul_nonneg
      (rows_small_dedekindZeta_real_nonneg (F := F) (1 + δ1) (by norm_num [δ1]))
      (by dsimp [CS]; positivity)
  have hInv (ξ : ℂ) (hξ : 1 + δ1 ≤ ξ.re) : ‖(HA.LS S η ξ)⁻¹‖ ≤ CI := by
    have hsone : 1 < ξ.re := lt_of_lt_of_le (by norm_num [δ1]) hξ
    have hrecip := (rows_LS_inverse_bound HA S η hEuler.1 fη hfη hsone).2
    have hmono := rows_small_dedekindZeta_real_antitone (F := F)
      (by norm_num [δ1] : 1 < 1 + δ1) hξ
    calc
      _ ≤ (NumberField.dedekindZeta F (ξ.re : ℂ)).re * CS := hrecip
      _ ≤ (NumberField.dedekindZeta F ((1 + δ1 : ℝ) : ℂ)).re * CS :=
        mul_le_mul_of_nonneg_right hmono (by dsimp [CS]; positivity)
      _ = CI := rfl
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  obtain ⟨CH, hCH, hHbound⟩ := hHP.2.2.2 (1 : ℝ) (by norm_num)
  obtain ⟨CM, hCM, hHeight⟩ := zf_height_decay R sd W
    (1 + δ1) 4 4 4 (1 / 6 + δ1) 2 A0
    (by norm_num [δ1]) le_rfl (by norm_num [δ1]) (by norm_num [δ1]) hA0
  let D0 : ℝ := CM * CZ * CW * CH * CI
  have hD0 : 0 ≤ D0 := by dsimp [D0]; positivity
  refine ⟨D0 + 1, by positivity, ?_⟩
  intro Z hZ ξ w z hξlo hξhi hw hzlo hzhi
  have hZpos : 0 < Z := by linarith
  have hsZ : σ ≤ (6 * z).re := by
    have hre : (6 * z).re = 6 * z.re := by simp
    rw [hre]
    dsimp only [σ]
    nlinarith [hzlo]
  have hLsZ := hPrincipal (6 * z) hsZ
  have hLsW : ‖HA.LS S 1 w‖ ≤ CW :=
    rows_LS_norm_bound HA S 1 hOne (by rw [hw]; norm_num)
  have hregion : eulerNeighborhood ![ξ, w, z] := by
    right
    change 998 / 1000 - 1 / 100000 < ξ.re ∧
      95 / 100 - 1 / 100000 < w.re ∧ 16 / 100 - 1 / 100000 < z.re
    refine ⟨lt_of_lt_of_le (by norm_num [δ1]) hξlo, ?_,
      lt_of_lt_of_le (by norm_num [δ1]) hzlo⟩
    rw [hw]
    norm_num
  have hH : ‖HC.H U.one ![ξ, w, z]‖ ≤ CH := by
    simpa only [U.q_one, Real.one_rpow, mul_one] using hHbound U.one ![ξ, w, z] hregion
  have hM := hHeight ξ w z hξlo hξhi (by rw [hw]) (by rw [hw]) hzlo hzhi
  have hMnonneg : 0 ≤ CM * Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by positivity
  have hbound := rows_principalKernel_norm_bound_of_factors R sd W η U HA HC Z hZpos ξ w z
    (CM * Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) CZ CW CH CI
    hMnonneg hCZ hCW hCH.le hCI hM hLsZ hLsW hH (hInv ξ hξlo)
  have hTail : 0 ≤ Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
      (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0) := by positivity
  calc
    _ ≤ Z ^ Estar ξ.re w.re z.re *
        (CM * Real.exp (-((ξ.im + z.im) ^ 2)) *
          (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) * CZ * CW * CH * CI := hbound
    _ = D0 * (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) := by dsimp only [D0]; ring
    _ ≤ (D0 + 1) * (Z ^ Estar ξ.re w.re z.re * Real.exp (-((ξ.im + z.im) ^ 2)) *
        (1 + |z.im|) ^ (-A0) * (1 + |w.im|) ^ (-A0)) :=
      mul_le_mul_of_nonneg_right (by linarith) hTail
    _ = _ := by ring

private theorem rows_sol_principal_line_continuous
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 0 < Z)
    (σξ σw σz : ℝ) (hξ : 1 + δ1 ≤ σξ)
    (hw : 95 / 100 ≤ σw) (hz : 16 / 100 ≤ σz)
    (hwne : σw ≠ 1) (hzne : 6 * σz ≠ 1) :
    Continuous (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel R sd W η U HA HC U.one Z
        (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I)) := by
  let ξp : ℝ × (ℝ × ℝ) → ℂ := fun p => σξ + p.1 * Complex.I
  let wp : ℝ × (ℝ × ℝ) → ℂ := fun p => σw + p.2.1 * Complex.I
  let zp : ℝ × (ℝ × ℝ) → ℂ := fun p => σz + p.2.2 * Complex.I
  have hξcont : Continuous ξp := by fun_prop
  have hwcont : Continuous wp := by fun_prop
  have hzcont : Continuous zp := by fun_prop
  have hξre (p : ℝ × (ℝ × ℝ)) : (ξp p).re = σξ := by simp [ξp]
  have hwre (p : ℝ × (ℝ × ℝ)) : (wp p).re = σw := by simp [wp]
  have hzre (p : ℝ × (ℝ × ℝ)) : (zp p).re = σz := by simp [zp]
  obtain ⟨hMdiff, hWdiff, _, _, _⟩ := (po_weights_exist R sd).2 W
  have hMlineOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => weightM R sd W (zp p)) Set.univ := by
    apply hMdiff.continuousOn.comp hzcont.continuousOn
    intro p hp
    change 0 < (zp p).re
    rw [hzre]
    exact lt_of_lt_of_le (by norm_num) hz
  have hMline : Continuous (fun p : ℝ × (ℝ × ℝ) => weightM R sd W (zp p)) :=
    continuousOn_univ.mp hMlineOn
  have hWline : Continuous (fun p : ℝ × (ℝ × ℝ) => weightW1hat W (wp p)) :=
    hWdiff.continuous.comp hwcont
  have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ a))
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hYbase : ((Z ^ b : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZ b))
  have hMellin : Continuous (fun p : ℝ × (ℝ × ℝ) =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξp p) (wp p) (zp p)) := by
    unfold mellinWeight
    have hXexp : Continuous (fun p : ℝ × (ℝ × ℝ) => (1 / 2 : ℂ) - zp p) := by fun_prop
    have hZexp : Continuous (fun p : ℝ × (ℝ × ℝ) => ξp p + zp p - 1) := by fun_prop
    have hYexp : Continuous (fun p : ℝ × (ℝ × ℝ) => wp p - 1) := by fun_prop
    have hX : Continuous (fun p => ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - zp p)) := by
      exact hXexp.const_cpow (Or.inl hXbase)
    have hZ : Continuous (fun p => (Z : ℂ) ^ (ξp p + zp p - 1)) := by
      exact hZexp.const_cpow (Or.inl hZbase)
    have hY : Continuous (fun p => ((Z ^ b : ℝ) : ℂ) ^ (wp p - 1)) := by
      exact hYexp.const_cpow (Or.inl hYbase)
    have hG : Continuous (fun p => Complex.exp ((ξp p + zp p - 1) ^ 2)) := by fun_prop
    exact (((((hX.mul hZ).mul hY).mul hG).mul hMline).mul hWline)
  have hPLdiff : DifferentiableOn ℂ (HA.LS S (1 : HeckeChar F)) {s | s ≠ 1} := by
    have hfactor : Differentiable ℂ (fun s : ℂ =>
        ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) := by
      refine Differentiable.fun_finsetProd ?_
      intro v hv
      have hn0 : 0 < Ideal.absNorm v.asIdeal :=
        Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v)
      have hn : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn0)
      have hpow : Differentiable ℂ (fun s : ℂ =>
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
        intro s
        exact (differentiableAt_id.neg).const_cpow (Or.inl hn)
      exact (differentiable_const (1 : ℂ)).sub
        ((differentiable_const ((1 : HeckeChar F).primeValue v)).mul hpow)
    change DifferentiableOn ℂ (fun s => HA.L (1 : HeckeChar F) s *
      ∏ v ∈ S.Sf, (1 - (1 : HeckeChar F).primeValue v *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) _
    exact HA.2.2.2.1.mul hfactor.differentiableOn
  have hwMaps : MapsTo wp Set.univ {s | s ≠ 1} := by
    intro p hp
    change wp p ≠ 1
    intro heq
    apply hwne
    have hre := congrArg Complex.re heq
    simpa [wp] using hre
  have hLwOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (wp p)) Set.univ :=
    hPLdiff.continuousOn.comp hwcont.continuousOn hwMaps
  have hLwline : Continuous (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (wp p)) :=
    continuousOn_univ.mp hLwOn
  let zsix : ℝ × (ℝ × ℝ) → ℂ := fun p => 6 * zp p
  have hzsixCont : Continuous zsix := by fun_prop
  have hzsixMaps : MapsTo zsix Set.univ {s | s ≠ 1} := by
    intro p hp
    change 6 * zp p ≠ 1
    intro heq
    apply hzne
    have hre := congrArg Complex.re heq
    simpa [zp] using hre
  have hLzOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (zsix p)) Set.univ :=
    hPLdiff.continuousOn.comp hzsixCont.continuousOn hzsixMaps
  have hLzline : Continuous (fun p : ℝ × (ℝ × ℝ) => HA.LS S 1 (zsix p)) :=
    continuousOn_univ.mp hLzOn
  obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
  have hInvDiff : DifferentiableOn ℂ (HA.LS S η) {s | 1 < s.re} :=
    rows_small_LS_differentiableOn (HA := HA) (S := S) η hEuler.1
  have hInvNe : ∀ s, 1 < s.re → HA.LS S η s ≠ 0 := by
    intro s hs
    exact (rows_LS_inverse_bound HA S η hEuler.1 fη hfη hs).1
  have hInvOn : DifferentiableOn ℂ (fun s => (HA.LS S η s)⁻¹) {s | 1 < s.re} := by
    apply hInvDiff.inv
    intro s hs
    exact hInvNe s hs
  have hξMaps : MapsTo ξp Set.univ {s | 1 < s.re} := by
    intro p hp
    change 1 < (ξp p).re
    rw [hξre]
    have hδ : 0 < δ1 := by norm_num [δ1]
    linarith [hξ]
  have hInvOnLine : ContinuousOn
      (fun p : ℝ × (ℝ × ℝ) => (HA.LS S η (ξp p))⁻¹) Set.univ :=
    hInvOn.continuousOn.comp hξcont.continuousOn hξMaps
  have hInvLine : Continuous (fun p : ℝ × (ℝ × ℝ) => (HA.LS S η (ξp p))⁻¹) :=
    continuousOn_univ.mp hInvOnLine
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℝ × (ℝ × ℝ) → Triple := fun p => ![ξp p, wp p, zp p]
  have hpmap : Continuous pmap := by fun_prop
  have hMaps : MapsTo pmap Set.univ {p | eulerNeighborhood p} := by
    intro p hp
    right
    change 998 / 1000 - 1 / 100000 < (ξp p).re ∧
      95 / 100 - 1 / 100000 < (wp p).re ∧ 16 / 100 - 1 / 100000 < (zp p).re
    refine ⟨?_, ?_, ?_⟩
    · rw [hξre]
      have hδ : 0 < δ1 := by norm_num [δ1]
      linarith [hξ]
    · rw [hwre]
      linarith [hw]
    · rw [hzre]
      linarith [hz]
  have hHCOn : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => HC.H U.one (pmap p)) Set.univ :=
    (hHP.2.1 U.one).continuousOn.comp hpmap.continuousOn hMaps
  have hHCline : Continuous (fun p : ℝ × (ℝ × ℝ) => HC.H U.one ![ξp p, wp p, zp p]) := by
    simpa only [pmap] using continuousOn_univ.mp hHCOn
  change Continuous (fun p : ℝ × (ℝ × ℝ) =>
    rowKernel R sd W η U HA HC U.one Z (ξp p) (wp p) (zp p))
  have hKernelEq : (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel R sd W η U HA HC U.one Z (ξp p) (wp p) (zp p)) =
      fun p => mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξp p) (wp p) (zp p) *
        HA.LS S 1 (zsix p) * HA.LS S 1 (wp p) * HC.H U.one ![ξp p, wp p, zp p] /
          HA.LS S η (ξp p) := by
    funext p
    exact rows_principalKernel_eq R sd W η U HA HC Z (ξp p) (wp p) (zp p)
  rw [hKernelEq]
  simp only [div_eq_mul_inv]
  exact (((hMellin.mul hLzline).mul hLwline).mul hHCline).mul hInvLine

private theorem rows_sol_principal_right_integrable
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 2 ≤ Z)
    (σξ σz : ℝ) (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4)
    (hzlo : 1 / 6 + δ1 ≤ σz) (hzhi : σz ≤ 2) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel R sd W η U HA HC U.one Z
        (σξ + p.1 * Complex.I) (4 + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I))
      (volume.prod (volume.prod volume)) := by
  obtain ⟨Aconv, Cconv, hAconv, hCconv, hconv⟩ :=
    zf_height_convolution (2 : ℝ) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := rows_sol_principal_right_kernel_control
    R sd W η U HA HC hEuler (Aconv + 2) (by linarith)
  have hmajor := rows_small_real_majorant_integrable Aconv Cconv hAconv hCconv hconv
  let M : ℝ := C * Z ^ Estar σξ 4 σz
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let f : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    rowKernel R sd W η U HA HC U.one Z
      (σξ + p.1 * Complex.I) (4 + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I)
  have hfcont : Continuous f := rows_sol_principal_line_continuous
    R sd W η U HA HC hEuler Z (by linarith) σξ 4 σz hξlo (by norm_num)
      (by norm_num [δ1] at hzlo ⊢; linarith) (by norm_num)
      (by norm_num [δ1] at hzlo ⊢; linarith)
  have hpoint (p : ℝ × (ℝ × ℝ)) : ‖f p‖ ≤ M *
      (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ)) := by
    have hkernel := hbound Z hZ (σξ + p.1 * Complex.I)
      (4 + p.2.1 * Complex.I) (σz + p.2.2 * Complex.I)
      (by simpa using hξlo) (by simpa using hξhi) (by simp)
      (by simpa using hzlo) (by simpa using hzhi)
    have hZpow : (1 + |p.2.2|) ^ (-(Aconv + 2)) ≤
        (1 + |p.2.2|) ^ (-Aconv) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2.2]) (by linarith)
    have hWpow : (1 + |p.2.1|) ^ (-(Aconv + 2)) ≤
        (1 + |p.2.1|) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg p.2.1]) (by linarith)
    calc
      ‖f p‖ ≤ M * Real.exp (-((p.1 + p.2.2) ^ 2)) *
          (1 + |p.2.2|) ^ (-(Aconv + 2)) *
            (1 + |p.2.1|) ^ (-(Aconv + 2)) := by
        simpa [f, M] using hkernel
      _ ≤ M * Real.exp (-((p.1 + p.2.2) ^ 2)) *
          (1 + |p.2.2|) ^ (-Aconv) * (1 + |p.2.1|) ^ (-2 : ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hZpow (mul_nonneg hM (Real.exp_pos _).le)
        · exact hWpow
        · positivity
        · positivity
      _ = _ := by ring
  have hdom : Integrable (fun p : ℝ × (ℝ × ℝ) => M *
      (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ))) (volume.prod (volume.prod volume)) := by
    simpa only [smul_eq_mul] using hmajor.const_mul M
  exact hdom.mono' hfcont.aestronglyMeasurable (ae_of_all _ hpoint)

private theorem rows_sol_principal_initial_xi (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) (w z : ℂ) (hw : w.re = 4) (hz : z.re = 2) :
    vertical 4 (fun ξ => rowKernel R sd W η U HA HC U.one Z ξ w z) =
      vertical (1 + δ1) (fun ξ => rowKernel R sd W η U HA HC U.one Z ξ w z) := by
  let strip : Set ℂ := {ξ | 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4}
  let G : ℂ → ℂ := fun ξ => rowKernel R sd W η U HA HC U.one Z ξ w z
  have hZpos : 0 < Z := by linarith
  obtain ⟨C, hC, hcontrol⟩ := rows_sol_principal_right_kernel_control
    R sd W η U HA HC hEuler (2 : ℝ) (by norm_num)
  have hGdiff : DifferentiableOn ℂ G strip :=
    rows_small_kernel_differentiableOn_xi R sd W η U HA HC hEuler Z hZpos U.one w z
      (by rw [hw]; norm_num) (by rw [hz]; norm_num)
  let Cshift : ℝ := C * Z ^ Estar 4 4 2
  have hline (x : ℝ) (hx : x ∈ Set.Icc (1 + δ1 : ℝ) 4) (t : ℝ) :
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤
        Cshift * Real.exp (-((t + z.im) ^ 2)) := by
    have hkernel := hcontrol Z hZ ((x : ℂ) + t * Complex.I) w z
      (by simpa using hx.1) (by simpa using hx.2) hw
      (by rw [hz]; norm_num [δ1]) hz.le
    have hEstar : Estar x 4 2 ≤ Estar 4 4 2 := by
      norm_num [Estar, a, b, h0]
      nlinarith [hx.2]
    have hZpow : Z ^ Estar x 4 2 ≤ Z ^ Estar 4 4 2 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hEstar
    have hpolyZ : (1 + |z.im|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z.im]) (by norm_num)
    have hpolyW : (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg w.im]) (by norm_num)
    have hpoly : (1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      mul_le_one₀ hpolyZ (Real.rpow_nonneg (by positivity) _) hpolyW
    calc
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤ C * Z ^ Estar x 4 2 *
          Real.exp (-((t + z.im) ^ 2)) *
            (1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) := by
        simpa [G, hw, hz] using hkernel
      _ = (C * Z ^ Estar x 4 2 * Real.exp (-((t + z.im) ^ 2))) *
          ((1 + |z.im|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ)) := by ring
      _ ≤ (C * Z ^ Estar x 4 2 * Real.exp (-((t + z.im) ^ 2))) * 1 :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ ≤ Cshift * Real.exp (-((t + z.im) ^ 2)) := by
        simpa only [mul_one, Cshift] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZpow hC.le)
            (Real.exp_pos (-((t + z.im) ^ 2))).le
  let trans : ℂ → ℂ := fun ξ => ξ - z.im * Complex.I
  let Fcont : ℂ → ℂ := fun ξ => G (trans ξ)
  have hTransDiff : Differentiable ℂ trans := by fun_prop
  have hTransMaps : MapsTo trans strip strip := by
    intro ξ hξ
    change 1 + δ1 ≤ ξ.re ∧ ξ.re ≤ 4 at hξ
    have hreal : (trans ξ).re = ξ.re := by simp [trans]
    constructor
    · rw [hreal]
      exact hξ.1
    · rw [hreal]
      exact hξ.2
  have hFdiff : DifferentiableOn ℂ Fcont strip := by
    have h := hGdiff.comp hTransDiff.differentiableOn hTransMaps
    simpa only [Fcont, Function.comp_def] using h
  have hFbound : ∀ x ∈ Set.Icc (1 + δ1 : ℝ) 4, ∀ y : ℝ,
      ‖Fcont ((x : ℂ) + y * Complex.I)‖ ≤ Cshift * Real.exp (-y ^ 2) := by
    intro x hx y
    have harg : trans ((x : ℂ) + y * Complex.I) =
        (x : ℂ) + (y - z.im) * Complex.I := by
      dsimp [trans]
      apply Complex.ext <;> simp <;> ring
    have h := hline x hx (y - z.im)
    change ‖G (trans ((x : ℂ) + y * Complex.I))‖ ≤ Cshift * Real.exp (-y ^ 2)
    rw [harg]
    rw [Complex.ofReal_sub] at h
    have hy : (y - z.im) + z.im = y := by ring
    rw [hy] at h
    exact h
  have hcontour := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    Fcont (a := 1 + δ1) (b := 4) (C := Cshift) (by norm_num [δ1]) hFdiff hFbound
  have htranslate (σ : ℝ) :
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
    have hcomp : (∫ t : ℝ, G ((σ : ℂ) + (t - z.im) * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) (-z.im)).integral_comp
        (Homeomorph.addLeft (-z.im)).measurableEmbedding
        (fun t : ℝ => G ((σ : ℂ) + t * Complex.I))
      simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have harg (t : ℝ) :
        ((σ : ℂ) + t * Complex.I) - z.im * Complex.I =
          (σ : ℂ) + (t - z.im) * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    calc
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
          ∫ t : ℝ, G ((σ : ℂ) + (t - z.im) * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change G (((σ : ℂ) + t * Complex.I) - z.im * Complex.I) =
          G ((σ : ℂ) + (t - z.im) * Complex.I)
        rw [harg]
      _ = ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := hcomp
  have hshiftV : vertical (1 + δ1) Fcont = vertical 4 Fcont := by
    unfold vertical
    rw [hcontour]
  calc
    vertical 4 G = vertical 4 Fcont := by
      unfold vertical
      rw [← htranslate 4]
    _ = vertical (1 + δ1) Fcont := hshiftV.symm
    _ = vertical (1 + δ1) G := by
      unfold vertical
      rw [htranslate (1 + δ1)]

private theorem rows_sol_principal_initial_z (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) (ξ w : ℂ)
    (hξlo : 1 + δ1 ≤ ξ.re) (hξhi : ξ.re ≤ 4) (hw : w.re = 4) :
    vertical 2 (fun z => rowKernel R sd W η U HA HC U.one Z ξ w z) =
      vertical (1 / 6 + δ1) (fun z => rowKernel R sd W η U HA HC U.one Z ξ w z) := by
  let strip : Set ℂ := {z | 1 / 6 + δ1 ≤ z.re ∧ z.re ≤ 2}
  let G : ℂ → ℂ := fun z => rowKernel R sd W η U HA HC U.one Z ξ w z
  have hZpos : 0 < Z := by linarith
  have hδ : 0 < δ1 := by norm_num [δ1]
  obtain ⟨C, hC, hcontrol⟩ := rows_sol_principal_right_kernel_control
    R sd W η U HA HC hEuler (2 : ℝ) (by norm_num)
  have hGdiff : DifferentiableOn ℂ G strip := by
    obtain ⟨hMdiff, _, _, _, _⟩ := (po_weights_exist R sd).2 W
    have hMstrip : DifferentiableOn ℂ (weightM R sd W) strip := by
      apply hMdiff.mono
      intro z hz
      exact lt_of_lt_of_le (by norm_num [δ1]) hz.1
    have hXbase : ((Z ^ a : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hZpos a))
    have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
    have hXexp : Differentiable ℂ (fun z : ℂ => (1 / 2 : ℂ) - z) := by fun_prop
    have hX : Differentiable ℂ (fun z : ℂ =>
        ((Z ^ a : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) := by
      intro z
      exact (hXexp z).const_cpow (Or.inl hXbase)
    have hZexp : Differentiable ℂ (fun z : ℂ => ξ + z - 1) := by fun_prop
    have hZpow : Differentiable ℂ (fun z : ℂ => (Z : ℂ) ^ (ξ + z - 1)) := by
      intro z
      exact (hZexp z).const_cpow (Or.inl hZbase)
    have hY : Differentiable ℂ (fun _z : ℂ =>
        ((Z ^ b : ℝ) : ℂ) ^ (w - 1)) := differentiable_const _
    have hGauss : Differentiable ℂ (fun z : ℂ => Complex.exp ((ξ + z - 1) ^ 2)) := by
      fun_prop
    have hW : Differentiable ℂ (fun _z : ℂ => weightW1hat W w) := differentiable_const _
    have hMellin : DifferentiableOn ℂ
        (fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z) strip := by
      unfold mellinWeight
      exact (((((hX.differentiableOn.mul hZpow.differentiableOn).mul
        hY.differentiableOn).mul hGauss.differentiableOn).mul hMstrip).mul
          hW.differentiableOn)
    have hLz : DifferentiableOn ℂ (fun z => HA.LS S 1 (6 * z)) strip := by
      apply (rows_LS_trivial_differentiableOn HA S).comp
        ((show Differentiable ℂ (fun z : ℂ => 6 * z) by fun_prop).differentiableOn)
      intro z hz
      change 1 < (6 * z).re
      have hre : (6 * z).re = 6 * z.re := by simp
      rw [hre]
      nlinarith [hz.1]
    have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
    let pmap : ℂ → Triple := fun z => ![ξ, w, z]
    have hpmap : Differentiable ℂ pmap := by
      intro z
      apply differentiableAt_pi.2
      intro j
      fin_cases j <;> simp [pmap] <;> fun_prop
    have hMaps : MapsTo pmap strip {p | eulerNeighborhood p} := by
      intro z hz
      right
      change 998 / 1000 - 1 / 100000 < ξ.re ∧
        95 / 100 - 1 / 100000 < w.re ∧ 16 / 100 - 1 / 100000 < z.re
      refine ⟨lt_of_lt_of_le (by norm_num [δ1]) hξlo, ?_,
        lt_of_lt_of_le (by norm_num [δ1]) hz.1⟩
      rw [hw]
      norm_num
    have hHC : DifferentiableOn ℂ (fun z => HC.H U.one ![ξ, w, z]) strip :=
      (hHP.2.1 U.one).comp hpmap.differentiableOn hMaps
    have hLw : DifferentiableOn ℂ (fun _z : ℂ => HA.LS S 1 w) strip :=
      (differentiable_const _).differentiableOn
    have hInv : DifferentiableOn ℂ (fun _z : ℂ => (HA.LS S η ξ)⁻¹) strip :=
      (differentiable_const _).differentiableOn
    have hGeq : G = fun z => mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
        HA.LS S 1 (6 * z) * HA.LS S 1 w * HC.H U.one ![ξ, w, z] / HA.LS S η ξ := by
      funext z
      exact rows_principalKernel_eq R sd W η U HA HC Z ξ w z
    rw [hGeq]
    simp only [div_eq_mul_inv]
    exact (((hMellin.mul hLz).mul hLw).mul hHC).mul hInv
  let Cshift : ℝ := C * Z ^ Estar ξ.re 4 2
  have hline (x : ℝ) (hx : x ∈ Set.Icc (1 / 6 + δ1 : ℝ) 2) (t : ℝ) :
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤
        Cshift * Real.exp (-((ξ.im + t) ^ 2)) := by
    have hkernel := hcontrol Z hZ ξ w ((x : ℂ) + t * Complex.I) hξlo hξhi hw
      (by simpa using hx.1) (by simpa using hx.2)
    have hEstar : Estar ξ.re 4 x ≤ Estar ξ.re 4 2 := by
      norm_num [Estar, a, b, h0]
      nlinarith [hx.2]
    have hZpow : Z ^ Estar ξ.re 4 x ≤ Z ^ Estar ξ.re 4 2 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z) hEstar
    have hpolyZ : (1 + |t|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
    have hpolyW : (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg w.im]) (by norm_num)
    have hpoly : (1 + |t|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) ≤ 1 :=
      mul_le_one₀ hpolyZ (Real.rpow_nonneg (by positivity) _) hpolyW
    calc
      ‖G ((x : ℂ) + t * Complex.I)‖ ≤ C * Z ^ Estar ξ.re 4 x *
          Real.exp (-((ξ.im + t) ^ 2)) *
            (1 + |t|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ) := by
        simpa [G, hw] using hkernel
      _ = (C * Z ^ Estar ξ.re 4 x * Real.exp (-((ξ.im + t) ^ 2))) *
          ((1 + |t|) ^ (-2 : ℝ) * (1 + |w.im|) ^ (-2 : ℝ)) := by ring
      _ ≤ (C * Z ^ Estar ξ.re 4 x * Real.exp (-((ξ.im + t) ^ 2))) * 1 :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ ≤ Cshift * Real.exp (-((ξ.im + t) ^ 2)) := by
        simpa only [mul_one, Cshift] using
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZpow hC.le)
            (Real.exp_pos (-((ξ.im + t) ^ 2))).le
  let trans : ℂ → ℂ := fun z => z - ξ.im * Complex.I
  let Fcont : ℂ → ℂ := fun z => G (trans z)
  have hTransDiff : Differentiable ℂ trans := by fun_prop
  have hTransMaps : MapsTo trans strip strip := by
    intro z hz
    change 1 / 6 + δ1 ≤ z.re ∧ z.re ≤ 2 at hz
    have hreal : (trans z).re = z.re := by simp [trans]
    constructor
    · rw [hreal]
      exact hz.1
    · rw [hreal]
      exact hz.2
  have hFdiff : DifferentiableOn ℂ Fcont strip := by
    have h := hGdiff.comp hTransDiff.differentiableOn hTransMaps
    simpa only [Fcont, Function.comp_def] using h
  have hFbound : ∀ x ∈ Set.Icc (1 / 6 + δ1 : ℝ) 2, ∀ y : ℝ,
      ‖Fcont ((x : ℂ) + y * Complex.I)‖ ≤ Cshift * Real.exp (-y ^ 2) := by
    intro x hx y
    have harg : trans ((x : ℂ) + y * Complex.I) =
        (x : ℂ) + (y - ξ.im) * Complex.I := by
      dsimp [trans]
      apply Complex.ext <;> simp <;> ring
    have h := hline x hx (y - ξ.im)
    change ‖G (trans ((x : ℂ) + y * Complex.I))‖ ≤ Cshift * Real.exp (-y ^ 2)
    rw [harg]
    rw [Complex.ofReal_sub] at h
    have hy : ξ.im + (y - ξ.im) = y := by ring
    rw [hy] at h
    exact h
  have hcontour := OAI.SevenEighths.Continuation.vertical_integral_eq_of_gaussian_bound
    Fcont (a := 1 / 6 + δ1) (b := 2) (C := Cshift) (by norm_num [δ1]) hFdiff hFbound
  have htranslate (σ : ℝ) :
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
    have hcomp : (∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I)) =
        ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := by
      have h := (measurePreserving_add_left (volume : Measure ℝ) (-ξ.im)).integral_comp
        (Homeomorph.addLeft (-ξ.im)).measurableEmbedding
        (fun t : ℝ => G ((σ : ℂ) + t * Complex.I))
      simpa [Function.comp_def, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have harg (t : ℝ) :
        ((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I =
          (σ : ℂ) + (t - ξ.im) * Complex.I := by
      apply Complex.ext <;> simp <;> ring
    calc
      (∫ t : ℝ, Fcont ((σ : ℂ) + t * Complex.I)) =
          ∫ t : ℝ, G ((σ : ℂ) + (t - ξ.im) * Complex.I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change G (((σ : ℂ) + t * Complex.I) - ξ.im * Complex.I) =
          G ((σ : ℂ) + (t - ξ.im) * Complex.I)
        rw [harg]
      _ = ∫ t : ℝ, G ((σ : ℂ) + t * Complex.I) := hcomp
  have hshiftV : vertical (1 / 6 + δ1) Fcont = vertical 2 Fcont := by
    unfold vertical
    rw [hcontour]
  calc
    vertical 2 G = vertical 2 Fcont := by
      unfold vertical
      rw [← htranslate 2]
    _ = vertical (1 / 6 + δ1) Fcont := hshiftV.symm
    _ = vertical (1 / 6 + δ1) G := by
      unfold vertical
      rw [htranslate (1 / 6 + δ1)]

private theorem rows_sol_principal_initial_shift (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) :
    rowContribution R sd W η U {U.one} Z =
      tripleVertical (1 + δ1) 4 (1 / 6 + δ1)
        (rowKernel R sd W η U HA HC U.one Z) := by
  let K : ℂ → ℂ → ℂ → ℂ := rowKernel R sd W η U HA HC U.one Z
  have hSwapOuter (σξ σw σz : ℝ)
      (hInt : Integrable (fun q : ℝ × (ℝ × ℝ) =>
        K (σξ + q.1 * Complex.I) (σw + q.2.1 * Complex.I)
          (σz + q.2.2 * Complex.I)) (volume.prod (volume.prod volume))) :
      tripleVertical σξ σw σz K =
        vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => K ξ w z))) := by
    let f : ℝ → ℝ → ℝ → ℂ := fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)
    have hleft : tripleVertical σξ σw σz K =
        tripleVertical σξ σw σz (fun ξ w z => f ξ.im w.im z.im) := by
      apply rows_tripleVertical_congr_lines
      intro tξ tw tz
      simp [f]
    have hf : Integrable (fun q : ℝ × (ℝ × ℝ) => f q.1 q.2.1 q.2.2)
        (volume.prod (volume.prod volume)) := by
      simpa [f] using hInt
    have hmid := rows_small_triple_swap_outer σξ σw σz f hf
    have hright :
        vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => f ξ.im w.im z.im))) =
          vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => K ξ w z))) := by
      apply rows_vertical_congr σw
      intro tw
      apply rows_vertical_congr σz
      intro tz
      apply rows_vertical_congr σξ
      intro tξ
      simp [f]
    exact hleft.trans (hmid.trans hright)
  have hIntStart := rows_sol_principal_right_integrable R sd W η U HA HC hEuler Z hZ
    4 2 (by norm_num [δ1]) le_rfl (by norm_num [δ1]) le_rfl
  have hIntEnd := rows_sol_principal_right_integrable R sd W η U HA HC hEuler Z hZ
    (1 + δ1) 2 le_rfl (by norm_num [δ1]) (by norm_num [δ1]) le_rfl
  have hSwapStart := hSwapOuter 4 4 2 hIntStart
  have hSwapEnd := hSwapOuter (1 + δ1) 4 2 hIntEnd
  have hShiftXiNested :
      vertical 4 (fun w => vertical 2 (fun z => vertical 4 (fun ξ => K ξ w z))) =
        vertical 4 (fun w => vertical 2 (fun z => vertical (1 + δ1) (fun ξ => K ξ w z))) := by
    apply rows_vertical_congr 4
    intro tw
    let w : ℂ := 4 + tw * Complex.I
    apply rows_vertical_congr 2
    intro tz
    let z : ℂ := 2 + tz * Complex.I
    simpa [K, w, z] using
      (rows_sol_principal_initial_xi R sd W η U HA HC hEuler Z hZ w z
        (by simp [w]) (by simp [z]))
  have hShiftXi : tripleVertical 4 4 2 K = tripleVertical (1 + δ1) 4 2 K :=
    hSwapStart.trans (hShiftXiNested.trans hSwapEnd.symm)
  have hShiftZ : tripleVertical (1 + δ1) 4 2 K =
      tripleVertical (1 + δ1) 4 (1 / 6 + δ1) K := by
    unfold tripleVertical
    apply rows_vertical_congr (1 + δ1)
    intro tξ
    let ξ : ℂ := (1 + δ1 : ℝ) + tξ * Complex.I
    apply rows_vertical_congr 4
    intro tw
    let w : ℂ := 4 + tw * Complex.I
    simpa [K, ξ, w] using
      (rows_sol_principal_initial_z R sd W η U HA HC hEuler Z hZ ξ w
        (by simp [ξ]) (by norm_num [ξ, δ1]) (by simp [w]))
  simpa only [K] using
    (rows_principal_initial_rowContribution_eq R sd W η U HA HC hEuler Z).trans
      (hShiftXi.trans hShiftZ)

private theorem rows_sol_principalRw_integrable
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 2 ≤ Z)
    (σξ : ℝ) (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4) :
    Integrable (fun p : ℝ × (ℝ × ℝ) =>
      rowKernel R sd W η U HA HC U.one Z
        (σξ + p.1 * Complex.I) ((95 / 100 : ℝ) + p.2.1 * Complex.I)
          ((1 / 6 + δ1 : ℝ) + p.2.2 * Complex.I))
      (volume.prod (volume.prod volume)) := by
  obtain ⟨AF, Aconv, C0, Cconv, hAF, hAconv, hC0, hCconv, hconv, hbound⟩ :=
    rows_principal_kernel_control R sd W η U HA HC hEuler
  have hmajor := rows_small_real_majorant_integrable Aconv Cconv hAconv hCconv hconv
  let M : ℝ := C0 * Z ^ Estar σξ (95 / 100) (1 / 6 + δ1)
  let f : ℝ × (ℝ × ℝ) → ℂ := fun p =>
    rowKernel R sd W η U HA HC U.one Z
      (σξ + p.1 * Complex.I) ((95 / 100 : ℝ) + p.2.1 * Complex.I)
        ((1 / 6 + δ1 : ℝ) + p.2.2 * Complex.I)
  have hfcont : Continuous f := rows_sol_principal_line_continuous
    R sd W η U HA HC hEuler Z (by linarith) σξ (95 / 100) (1 / 6 + δ1) hξlo
      le_rfl (by norm_num [δ1]) (by norm_num) (by norm_num [δ1])
  have hpoint (p : ℝ × (ℝ × ℝ)) : ‖f p‖ ≤ M *
      (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ)) := by
    have hkernel := hbound Z hZ (σξ + p.1 * Complex.I)
      ((95 / 100 : ℝ) + p.2.1 * Complex.I)
        ((1 / 6 + δ1 : ℝ) + p.2.2 * Complex.I)
      (by simpa using hξlo) (by simpa using hξhi) (by simp) (by simp)
    simpa [f, M, mul_assoc] using hkernel
  have hdom : Integrable (fun p : ℝ × (ℝ × ℝ) => M *
      (Real.exp (-((p.1 + p.2.2) ^ 2)) * (1 + |p.2.2|) ^ (-Aconv) *
        (1 + |p.2.1|) ^ (-2 : ℝ))) (volume.prod (volume.prod volume)) := by
    simpa only [smul_eq_mul] using hmajor.const_mul M
  exact hdom.mono' hfcont.aestronglyMeasurable (ae_of_all _ hpoint)

private theorem rows_sol_integrable_w_projection (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
      (volume.prod (volume.prod volume))) :
    Integrable (fun p : ℝ × ℝ => ∫ tw : ℝ, f p.1 tw p.2) (volume.prod volume) := by
  have hId : MeasurePreserving (id : ℝ → ℝ) (volume : Measure ℝ) volume :=
    ⟨measurable_id, by simp⟩
  have hperm : MeasurePreserving
      (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.2, p.1.2)))
      ((volume.prod volume).prod volume) (volume.prod (volume.prod volume)) := by
    exact (hId.prod (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))).comp
      (measurePreserving_prodAssoc (volume : Measure ℝ) volume volume)
  have hRearranged : Integrable (fun p : (ℝ × ℝ) × ℝ => f p.1.1 p.2 p.1.2)
      ((volume.prod volume).prod volume) :=
    hperm.integrable_comp_of_integrable hf
  exact hRearranged.integral_prod_left

private theorem rows_sol_principal_w_integrated
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 2 ≤ Z) :
    rowContribution R sd W η U {U.one} Z =
      principalRw R sd W η U HA HC Z +
        vertical (1 + δ1) (fun ξ => vertical (1 / 6 + δ1) (fun z =>
          mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
            HA.LS S 1 (6 * z) * HA.RS S * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ)) := by
  let σξ : ℝ := 1 + δ1
  let σz : ℝ := 1 / 6 + δ1
  let c : ℂ := 1 / (2 * Real.pi)
  let K : ℂ → ℂ → ℂ → ℂ := rowKernel R sd W η U HA HC U.one Z
  let Q : ℂ → ℂ → ℂ := fun ξ z =>
    mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ 1 z *
      HA.LS S 1 (6 * z) * HA.RS S * HC.H U.one ![ξ, 1, z] / HA.LS S η ξ
  let J : ℝ → (ℝ × ℝ) → ℂ := fun σw p =>
    vertical σw (fun w => K (σξ + p.1 * Complex.I) w (σz + p.2 * Complex.I))
  have hJInt (σw : ℝ)
      (hInt : Integrable (fun p : ℝ × (ℝ × ℝ) =>
        K (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I)
          (σz + p.2.2 * Complex.I)) (volume.prod (volume.prod volume))) :
      Integrable (J σw) (volume.prod volume) := by
    have hraw := rows_sol_integrable_w_projection (fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)) hInt
    simpa only [J, vertical, c] using hraw.const_mul c
  have hInt4 : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      K (σξ + p.1 * Complex.I) (4 + p.2.1 * Complex.I)
        (σz + p.2.2 * Complex.I)) (volume.prod (volume.prod volume)) := by
    exact rows_sol_principal_right_integrable R sd W η U HA HC hEuler Z hZ
      σξ σz le_rfl (by norm_num [σξ, δ1]) le_rfl (by norm_num [σz, δ1])
  have hInt95 : Integrable (fun p : ℝ × (ℝ × ℝ) =>
      K (σξ + p.1 * Complex.I) ((95 / 100 : ℝ) + p.2.1 * Complex.I)
        (σz + p.2.2 * Complex.I)) (volume.prod (volume.prod volume)) := by
    exact rows_sol_principalRw_integrable R sd W η U HA HC hEuler Z hZ
      σξ le_rfl (by norm_num [σξ, δ1])
  have hJ4 := hJInt 4 hInt4
  have hJ95 := hJInt (95 / 100) hInt95
  have hResidue (p : ℝ × ℝ) :
      J 4 p = J (95 / 100) p + Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I) := by
    exact rows_sol_principal_w_residue R sd W η U HA HC hEuler Z hZ
      (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)
      (by simp [σξ]) (by norm_num [σξ, δ1]) (by simp [σz])
  have hQInt : Integrable (fun p : ℝ × ℝ =>
      Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)) (volume.prod volume) := by
    apply (hJ4.sub hJ95).congr
    exact ae_of_all _ fun p => by
      change J 4 p - J (95 / 100) p = Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)
      rw [hResidue]
      ring
  have hTriple (σw : ℝ)
      (hInt : Integrable (fun p : ℝ × (ℝ × ℝ) =>
        K (σξ + p.1 * Complex.I) (σw + p.2.1 * Complex.I)
          (σz + p.2.2 * Complex.I)) (volume.prod (volume.prod volume))) :
      tripleVertical σξ σw σz K =
        c * c * MeasureTheory.integral (volume.prod volume) (J σw) := by
    let f : ℝ → ℝ → ℝ → ℂ := fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)
    have hf : Integrable (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)
        (volume.prod (volume.prod volume)) := hInt
    have hleft : tripleVertical σξ σw σz K =
        c * (c * (c * (∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f tξ tw tz))) := by
      simp only [tripleVertical, vertical, integral_const_mul]
      rfl
    have hright : c * c * MeasureTheory.integral (volume.prod volume) (J σw) =
        c * (c * (c * (∫ tξ : ℝ, ∫ tz : ℝ, ∫ tw : ℝ, f tξ tw tz))) := by
      change c * c * (∫ p : ℝ × ℝ, c * (∫ tw : ℝ, f p.1 tw p.2)
        ∂(volume.prod volume)) = _
      rw [integral_const_mul,
        integral_prod _ (rows_sol_integrable_w_projection f hf)]
      ring
    calc
      tripleVertical σξ σw σz K =
          c * (c * (c * (∫ tξ : ℝ, ∫ tw : ℝ, ∫ tz : ℝ, f tξ tw tz))) := hleft
      _ = c * (c * (c * (∫ tξ : ℝ, ∫ tz : ℝ, ∫ tw : ℝ, f tξ tw tz))) :=
        congrArg (fun q : ℂ => c * (c * (c * q))) (rows_small_raw_swap_wz_outer f hf)
      _ = c * c * MeasureTheory.integral (volume.prod volume) (J σw) := hright.symm
  have hDoubleQ :
      vertical σξ (fun ξ => vertical σz (fun z => Q ξ z)) =
        c * c * MeasureTheory.integral (volume.prod volume)
          (fun p : ℝ × ℝ => Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)) := by
    simp only [vertical, integral_const_mul]
    rw [integral_prod _ hQInt]
    change c * (c * _) = c * c * _
    ring
  have hAdd : MeasureTheory.integral (volume.prod volume) (J 4) =
      MeasureTheory.integral (volume.prod volume) (J (95 / 100)) +
        MeasureTheory.integral (volume.prod volume)
          (fun p : ℝ × ℝ => Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)) := by
    calc
      _ = MeasureTheory.integral (volume.prod volume)
          (fun p : ℝ × ℝ => J (95 / 100) p +
            Q (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)) :=
        integral_congr_ae (ae_of_all _ hResidue)
      _ = _ := integral_add hJ95 hQInt
  have hAssemble : tripleVertical σξ 4 σz K =
      tripleVertical σξ (95 / 100) σz K +
        vertical σξ (fun ξ => vertical σz (fun z => Q ξ z)) := by
    rw [hTriple 4 hInt4, hTriple (95 / 100) hInt95, hDoubleQ, hAdd, mul_add]
  simpa only [σξ, σz, K, Q, principalRw] using
    (rows_sol_principal_initial_shift R sd W η U HA HC hEuler Z hZ).trans hAssemble

private theorem rows_sol_principal_w_residue_integrable
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 2 ≤ Z)
    (σξ : ℝ) (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4) :
    Integrable (fun p : ℝ × ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z
        (σξ + p.1 * Complex.I) 1 ((1 / 6 + δ1 : ℝ) + p.2 * Complex.I) *
      HA.LS S 1 (6 * ((1 / 6 + δ1 : ℝ) + p.2 * Complex.I)) * HA.RS S *
      HC.H U.one ![σξ + p.1 * Complex.I, 1,
        (1 / 6 + δ1 : ℝ) + p.2 * Complex.I] /
      HA.LS S η (σξ + p.1 * Complex.I)) (volume.prod volume) := by
  let σz : ℝ := 1 / 6 + δ1
  let c : ℂ := 1 / (2 * Real.pi)
  let K : ℂ → ℂ → ℂ → ℂ := rowKernel R sd W η U HA HC U.one Z
  let J : ℝ → (ℝ × ℝ) → ℂ := fun σw p =>
    vertical σw (fun w => K (σξ + p.1 * Complex.I) w (σz + p.2 * Complex.I))
  have hInt4 := rows_sol_principal_right_integrable R sd W η U HA HC hEuler Z hZ
    σξ σz hξlo hξhi le_rfl (by norm_num [σz, δ1])
  have hInt95 := rows_sol_principalRw_integrable R sd W η U HA HC hEuler Z hZ
    σξ hξlo hξhi
  have hJ4 : Integrable (J 4) (volume.prod volume) := by
    have hraw := rows_sol_integrable_w_projection (fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (4 + tw * Complex.I) (σz + tz * Complex.I)) hInt4
    simpa only [J, vertical, c, Complex.ofReal_ofNat] using hraw.const_mul c
  have hJ95 : Integrable (J (95 / 100)) (volume.prod volume) := by
    have hraw := rows_sol_integrable_w_projection (fun tξ tw tz =>
      K (σξ + tξ * Complex.I) ((95 / 100 : ℝ) + tw * Complex.I)
        (σz + tz * Complex.I)) hInt95
    simpa only [J, vertical, c] using hraw.const_mul c
  apply (hJ4.sub hJ95).congr
  exact ae_of_all _ fun p => by
    change J 4 p - J (95 / 100) p = _
    have hResidue := rows_sol_principal_w_residue R sd W η U HA HC hEuler Z hZ
      (σξ + p.1 * Complex.I) (σz + p.2 * Complex.I)
      (by simpa using hξlo) (by simpa using hξhi) (by simp [σz])
    change J 4 p = J (95 / 100) p + _ at hResidue
    rw [hResidue]
    ring

private theorem rows_sol_principal_z_residue_integrable
    (hEuler : EulerHypotheses R η) (Z : ℝ) (hZ : 2 ≤ Z)
    (σξ : ℝ) (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4) :
    Integrable (fun t : ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (σξ + t * Complex.I) 1 (1 / 6) *
        (HA.RS S ^ 2 / 6) * HC.H U.one ![σξ + t * Complex.I, 1, 1 / 6] /
          HA.LS S η (σξ + t * Complex.I)) := by
  have hZpos : 0 < Z := by linarith
  have hσ : 1 < σξ := by
    have hδ : 0 < δ1 := by norm_num [δ1]
    linarith
  let ξline : ℝ → ℂ := fun t => (σξ : ℂ) + t * Complex.I
  let Ares : ℂ := HA.RS S ^ 2 / 6
  let f : ℝ → ℂ := fun t =>
    mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6) *
      Ares * HC.H U.one ![ξline t, 1, 1 / 6] / HA.LS S η (ξline t)
  have hξre (t : ℝ) : (ξline t).re = σξ := by simp [ξline]
  have hξcont : Continuous ξline := by fun_prop
  have hZbase : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
  have hMellinCont : Continuous (fun t : ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6)) := by
    have hEq : (fun t : ℝ =>
        mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6)) =
        fun t => (Z : ℂ) ^ ((a : ℂ) / 2 + ξline t - 1 + (h0 : ℂ) * (1 / 6)) *
          Complex.exp ((ξline t + 1 / 6 - 1) ^ 2) *
            weightM R sd W (1 / 6) * weightW1hat W 1 := by
      funext t
      exact rows_sol_mellin_w_one R sd W Z hZpos (ξline t) (1 / 6)
    rw [hEq]
    have hExp : Continuous (fun t : ℝ =>
        (a : ℂ) / 2 + ξline t - 1 + (h0 : ℂ) * (1 / 6)) := by fun_prop
    have hPow : Continuous (fun t : ℝ =>
        (Z : ℂ) ^ ((a : ℂ) / 2 + ξline t - 1 + (h0 : ℂ) * (1 / 6))) :=
      hExp.const_cpow (Or.inl hZbase)
    have hG : Continuous (fun t : ℝ => Complex.exp ((ξline t + 1 / 6 - 1) ^ 2)) := by
      fun_prop
    exact ((hPow.mul hG).mul continuous_const).mul continuous_const
  have hHP : HasPoHProduct R η U HC := po_H_product R η U HC hEuler
  let pmap : ℝ → Triple := fun t => ![ξline t, 1, 1 / 6]
  have hpmap : Continuous pmap := by fun_prop
  have hMaps : MapsTo pmap Set.univ {p | eulerNeighborhood p} := by
    intro t ht
    right
    change 998 / 1000 - 1 / 100000 < (ξline t).re ∧
      95 / 100 - 1 / 100000 < (1 : ℂ).re ∧
      16 / 100 - 1 / 100000 < (1 / 6 : ℂ).re
    refine ⟨?_, by norm_num, by norm_num⟩
    rw [hξre]
    linarith
  have hHOn : ContinuousOn (fun t : ℝ => HC.H U.one (pmap t)) Set.univ :=
    (hHP.2.1 U.one).continuousOn.comp hpmap.continuousOn hMaps
  have hHCont : Continuous (fun t : ℝ => HC.H U.one ![ξline t, 1, 1 / 6]) := by
    simpa only [pmap] using continuousOn_univ.mp hHOn
  obtain ⟨fη, hfη⟩ := rows_eta_primitive_conductor R η U hEuler
  have hInvDiff : DifferentiableOn ℂ (HA.LS S η) {s | 1 < s.re} :=
    rows_small_LS_differentiableOn (HA := HA) (S := S) η hEuler.1
  have hInvOn : DifferentiableOn ℂ (fun s => (HA.LS S η s)⁻¹) {s | 1 < s.re} := by
    apply hInvDiff.inv
    intro s hs
    exact (rows_LS_inverse_bound HA S η hEuler.1 fη hfη hs).1
  have hξMaps : MapsTo ξline Set.univ {s | 1 < s.re} := by
    intro t ht
    change 1 < (ξline t).re
    rw [hξre]
    exact hσ
  have hInvOnLine : ContinuousOn (fun t : ℝ => (HA.LS S η (ξline t))⁻¹) Set.univ :=
    hInvOn.continuousOn.comp hξcont.continuousOn hξMaps
  have hInvCont : Continuous (fun t : ℝ => (HA.LS S η (ξline t))⁻¹) :=
    continuousOn_univ.mp hInvOnLine
  have hfcont : Continuous f := by
    change Continuous (fun t : ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6) *
        Ares * HC.H U.one ![ξline t, 1, 1 / 6] / HA.LS S η (ξline t))
    simp only [div_eq_mul_inv]
    exact (((hMellinCont.mul continuous_const).mul hHCont).mul hInvCont)
  obtain ⟨Cht, hCht, hheight⟩ := zf_height_decay R sd W
    σξ σξ 1 1 (1 / 6) (1 / 6) 1 le_rfl le_rfl (by norm_num) le_rfl (by norm_num)
  obtain ⟨CH, hCH, hHbound⟩ := hHP.2.2.2 (1 : ℝ) (by norm_num)
  let Cinv : ℝ := (NumberField.dedekindZeta F (σξ : ℂ)).re * 2 ^ S.Sf.card
  have hCinv : 0 ≤ Cinv := by
    dsimp [Cinv]
    exact mul_nonneg (rows_small_dedekindZeta_real_nonneg (F := F) σξ hσ) (by positivity)
  have hMellinBound (t : ℝ) :
      ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6)‖ ≤
        (Z ^ Estar σξ 1 (1 / 6) * Cht) * Real.exp (-t ^ 2) := by
    rw [rows_mellinWeight_norm R sd W Z hZpos]
    have hh := hheight (ξline t) (1 : ℂ) (1 / 6 : ℂ)
      (by simp [ξline]) (by simp [ξline]) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hh' : ‖Complex.exp ((ξline t + 1 / 6 - 1) ^ 2) *
        weightM R sd W (1 / 6) * weightW1hat W 1‖ ≤ Cht * Real.exp (-t ^ 2) := by
      simpa [ξline] using hh
    simpa [ξline, mul_assoc] using mul_le_mul_of_nonneg_left hh'
      (Real.rpow_nonneg hZpos.le (Estar σξ 1 (1 / 6)))
  have hHline (t : ℝ) : ‖HC.H U.one ![ξline t, 1, 1 / 6]‖ ≤ CH := by
    have hp : eulerNeighborhood (pmap t) := hMaps (mem_univ t)
    simpa [pmap, U.q_one] using hHbound U.one (pmap t) hp
  have hInvline (t : ℝ) : ‖(HA.LS S η (ξline t))⁻¹‖ ≤ Cinv := by
    have hs : 1 < (ξline t).re := by rw [hξre]; exact hσ
    obtain ⟨_, hrecip⟩ := rows_LS_inverse_bound HA S η hEuler.1 fη hfη hs
    rw [hξre] at hrecip
    simpa only [Cinv] using hrecip
  let B : ℝ := Z ^ Estar σξ 1 (1 / 6) * Cht * ‖Ares‖ * CH * Cinv
  have hpoint (t : ℝ) : ‖f t‖ ≤ B * Real.exp (-t ^ 2) := by
    have hm := hMellinBound t
    have hH := hHline t
    have hi := hInvline t
    calc
      ‖f t‖ = ‖mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξline t) 1 (1 / 6)‖ *
          ‖Ares‖ * ‖HC.H U.one ![ξline t, 1, 1 / 6]‖ * ‖(HA.LS S η (ξline t))⁻¹‖ := by
        simp only [f, div_eq_mul_inv, norm_mul]
      _ ≤ ((Z ^ Estar σξ 1 (1 / 6) * Cht) * Real.exp (-t ^ 2)) * ‖Ares‖ * CH * Cinv := by
        gcongr
      _ = B * Real.exp (-t ^ 2) := by dsimp [B]; ring
  have hGauss : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num : 0 < (1 : ℝ)))
  have hdom : Integrable (fun t : ℝ => B * Real.exp (-t ^ 2)) := hGauss.const_mul B
  exact hdom.mono' hfcont.aestronglyMeasurable (ae_of_all _ hpoint)

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
  intro hEuler α B ε hα hB hε
  obtain ⟨AF, Adec, Aconv, C0, Cconv, hAF, hAconv, hAeq, hAdecPos,
      hC0, hCconv, hconv, hcontrol⟩ :=
    rows_small_kernel_control R sd W η U HA HC hEuler ε hε
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hIint : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (p := (2 : ℝ)) (by norm_num)
  have hI0 : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun t => by positivity
  let p : ℝ := 1 / 10 + ε
  have hp : 0 < p := by dsimp [p]; linarith
  let Cpre : ℝ := C0 * Cconv * I * I * B * 2 ^ p
  let C : ℝ := Cpre + 1
  have hCpre : 0 ≤ Cpre := by dsimp [Cpre]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro T Z hT hZ rows hrows hcard
  have hTpos : 0 < T := by linarith
  have hZpos : 0 < Z := by linarith
  let K : ℂ → ℂ → ℂ → ℂ := fun ξ w z =>
    ∑ u ∈ rows, rowKernel R sd W η U HA HC u Z ξ w z
  have huRows : ∀ u ∈ rows, u ≠ U.one := fun u hu => (hrows u hu).1
  have hIntAt (σξ σw σz : ℝ)
      (hξlo : 1 + δ1 ≤ σξ) (hξhi : σξ ≤ 4)
      (hwlo : 3 / 1000 ≤ σw) (hwhi : σw ≤ 4)
      (hzlo : 4 / 10 ≤ σz) (hzhi : σz ≤ 2) :
      Integrable (fun q : ℝ × (ℝ × ℝ) =>
        K (σξ + q.1 * Complex.I) (σw + q.2.1 * Complex.I)
          (σz + q.2.2 * Complex.I)) (volume.prod (volume.prod volume)) := by
    simpa [K] using rows_small_kernel_sum_integrable R sd W η U HA HC hEuler ε hε Z hZ
      rows huRows σξ σw σz hξlo hξhi hwlo hwhi hzlo hzhi
  have hSwapWZ (σξ σw σz : ℝ)
      (hInt : Integrable (fun q : ℝ × (ℝ × ℝ) =>
        K (σξ + q.1 * Complex.I) (σw + q.2.1 * Complex.I)
          (σz + q.2.2 * Complex.I)) (volume.prod (volume.prod volume))) :
      tripleVertical σξ σw σz K =
        tripleVertical σξ σz σw (fun ξ z w => K ξ w z) := by
    let f : ℝ → ℝ → ℝ → ℂ := fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)
    have hleft : tripleVertical σξ σw σz K =
        tripleVertical σξ σw σz (fun ξ w z => f ξ.im w.im z.im) := by
      apply rows_tripleVertical_congr_lines
      intro tξ tw tz
      simp [f]
    have hf : Integrable (fun q : ℝ × (ℝ × ℝ) => f q.1 q.2.1 q.2.2)
        (volume.prod (volume.prod volume)) := by
      simpa [f] using hInt
    have hmid := rows_small_triple_swap_wz σξ σw σz f hf
    have hright : tripleVertical σξ σz σw (fun ξ z w => f ξ.im w.im z.im) =
        tripleVertical σξ σz σw (fun ξ z w => K ξ w z) := by
      apply rows_tripleVertical_congr_lines
      intro tξ tz tw
      simp [f]
    exact hleft.trans (hmid.trans hright)
  have hSwapOuter (σξ σw σz : ℝ)
      (hInt : Integrable (fun q : ℝ × (ℝ × ℝ) =>
        K (σξ + q.1 * Complex.I) (σw + q.2.1 * Complex.I)
          (σz + q.2.2 * Complex.I)) (volume.prod (volume.prod volume))) :
      tripleVertical σξ σw σz K =
        vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => K ξ w z))) := by
    let f : ℝ → ℝ → ℝ → ℂ := fun tξ tw tz =>
      K (σξ + tξ * Complex.I) (σw + tw * Complex.I) (σz + tz * Complex.I)
    have hleft : tripleVertical σξ σw σz K =
        tripleVertical σξ σw σz (fun ξ w z => f ξ.im w.im z.im) := by
      apply rows_tripleVertical_congr_lines
      intro tξ tw tz
      simp [f]
    have hf : Integrable (fun q : ℝ × (ℝ × ℝ) => f q.1 q.2.1 q.2.2)
        (volume.prod (volume.prod volume)) := by
      simpa [f] using hInt
    have hmid := rows_small_triple_swap_outer σξ σw σz f hf
    have hright :
        vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => f ξ.im w.im z.im))) =
          vertical σw (fun w => vertical σz (fun z => vertical σξ (fun ξ => K ξ w z))) := by
      apply rows_vertical_congr σw
      intro tw
      apply rows_vertical_congr σz
      intro tz
      apply rows_vertical_congr σξ
      intro tξ
      simp [f]
    exact hleft.trans (hmid.trans hright)
  have hI44z := hIntAt 4 4 (4 / 10)
    (by norm_num [δ1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hI4wz := hIntAt 4 (3 / 1000) (4 / 10)
    (by norm_num [δ1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hI1wz := hIntAt (1 + δ1) (3 / 1000) (4 / 10)
    (by rfl) (by norm_num [δ1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hShiftZ : tripleVertical 4 4 2 K = tripleVertical 4 4 (4 / 10) K := by
    unfold tripleVertical
    apply rows_vertical_congr 4
    intro tξ
    let ξ : ℂ := 4 + tξ * Complex.I
    have hξ : ξ.re = 4 := by simp [ξ]
    apply rows_vertical_congr 4
    intro tw
    let w : ℂ := 4 + tw * Complex.I
    have hw : w.re = 4 := by simp [w]
    simpa [K, ξ, w] using
      (rows_small_shift_z R sd W η U HA HC hEuler ε hε Z hZ rows
        huRows ξ w (by norm_num [hξ, δ1]) (by norm_num [hξ]) hw)
  have hShiftWswap :
      tripleVertical 4 (4 / 10) 4 (fun ξ z w => K ξ w z) =
        tripleVertical 4 (4 / 10) (3 / 1000) (fun ξ z w => K ξ w z) := by
    unfold tripleVertical
    apply rows_vertical_congr 4
    intro tξ
    let ξ : ℂ := 4 + tξ * Complex.I
    have hξ : ξ.re = 4 := by simp [ξ]
    apply rows_vertical_congr (4 / 10)
    intro tz
    let z : ℂ := (4 / 10 : ℝ) + tz * Complex.I
    have hz : z.re = 4 / 10 := by simp [z]
    simpa [K, ξ, z] using
      (rows_small_shift_w R sd W η U HA HC hEuler ε hε Z hZ rows
        huRows ξ z (by norm_num [hξ, δ1]) (by norm_num [hξ]) hz)
  have hSwapStart := hSwapWZ 4 4 (4 / 10) hI44z
  have hSwapEnd := hSwapWZ 4 (3 / 1000) (4 / 10) hI4wz
  have hShiftW : tripleVertical 4 4 (4 / 10) K =
      tripleVertical 4 (3 / 1000) (4 / 10) K := by
    exact hSwapStart.trans (hShiftWswap.trans hSwapEnd.symm)
  have hSwapOuterStart := hSwapOuter 4 (3 / 1000) (4 / 10) hI4wz
  have hShiftXiNested :
      vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z => vertical 4 (fun ξ => K ξ w z))) =
        vertical (3 / 1000) (fun w =>
          vertical (4 / 10) (fun z => vertical (1 + δ1) (fun ξ => K ξ w z))) := by
    apply rows_vertical_congr (3 / 1000)
    intro tw
    let w : ℂ := (3 / 1000 : ℝ) + tw * Complex.I
    have hw : w.re = 3 / 1000 := by simp [w]
    apply rows_vertical_congr (4 / 10)
    intro tz
    let z : ℂ := (4 / 10 : ℝ) + tz * Complex.I
    have hz : z.re = 4 / 10 := by simp [z]
    simpa [K, w, z] using
      (rows_small_shift_xi R sd W η U HA HC hEuler ε hε Z hZ rows huRows w z hw hz)
  have hSwapOuterEnd := hSwapOuter (1 + δ1) (3 / 1000) (4 / 10) hI1wz
  have hShiftXi : tripleVertical 4 (3 / 1000) (4 / 10) K =
      tripleVertical (1 + δ1) (3 / 1000) (4 / 10) K := by
    exact hSwapOuterStart.trans (hShiftXiNested.trans hSwapOuterEnd.symm)
  have hinitial := rows_initial_rowContribution_eq R sd W η U HA HC hEuler Z rows
  have hrowEq : rowContribution R sd W η U rows Z =
      tripleVertical (1 + δ1) (3 / 1000) (4 / 10) K := by
    simpa [K] using hinitial.trans (hShiftZ.trans (hShiftW.trans hShiftXi))
  have hqsum :
      (∑ u ∈ rows, (U.q u) ^ p) ≤ B * 2 ^ p * T ^ (α + p) := by
    calc
      _ ≤ ∑ _u ∈ rows, (2 * T) ^ p := by
        apply Finset.sum_le_sum
        intro u hu
        have hfreq := (hrows u hu).2
        change T ≤ U.q u ∧ U.q u < 2 * T at hfreq
        exact Real.rpow_le_rpow (U.q_pos u).le hfreq.2.le (by linarith [hp])
      _ = (rows.card : ℝ) * (2 * T) ^ p := by simp
      _ ≤ (B * T ^ α) * (2 * T) ^ p :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)
      _ = B * 2 ^ p * T ^ (α + p) := by
        have hmul : (2 * T) ^ p = 2 ^ p * T ^ p :=
          Real.mul_rpow (by norm_num) (by linarith)
        rw [hmul]
        calc
          _ = B * 2 ^ p * (T ^ α * T ^ p) := by ring
          _ = _ := by rw [← Real.rpow_add hTpos]
  let M : ℝ := C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
    (B * 2 ^ p * T ^ (α + p))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hline (tξ tw tz : ℝ) :
      ‖K ((1 + δ1 : ℝ) + tξ * Complex.I)
          ((3 / 1000 : ℝ) + tw * Complex.I) ((4 / 10 : ℝ) + tz * Complex.I)‖ ≤
        M * (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) *
          (1 + |tw|) ^ (-2 : ℝ)) := by
    let ξ : ℂ := (1 + δ1 : ℝ) + tξ * Complex.I
    let w : ℂ := (3 / 1000 : ℝ) + tw * Complex.I
    let z : ℂ := (4 / 10 : ℝ) + tz * Complex.I
    have hξre : ξ.re = 1 + δ1 := by simp [ξ]
    have hwre : w.re = 3 / 1000 := by simp [w]
    have hzre : z.re = 4 / 10 := by simp [z]
    have hξim : ξ.im = tξ := by simp [ξ]
    have hwim : w.im = tw := by simp [w]
    have hzim : z.im = tz := by simp [z]
    let H : ℝ := Real.exp (-((tξ + tz) ^ 2)) *
      (1 + |tz|) ^ (-Aconv) * (1 + |tw|) ^ (-2 : ℝ)
    have hsumNorm := norm_sum_le rows (fun u => rowKernel R sd W η U HA HC u Z ξ w z)
    have hrow (u : U.U) (hu : u ∈ rows) :
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * (U.q u) ^ p * H := by
      have h := hcontrol Z hZ u (huRows u hu) ξ w z
        (by simpa [hξre]) (by norm_num [hξre, δ1])
        (by simpa [hwre]) (by norm_num [hwre])
        (by simpa [hzre]) (by norm_num [hzre])
      have hpq : p = 1 / 10 + ε := by rfl
      simpa [ξ, w, z, H, hξre, hwre, hzre, hξim, hwim, hzim, hpq,
        mul_assoc, mul_left_comm, mul_comm] using h
    have hsumBound :
        (∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖) ≤
          ∑ u ∈ rows,
            C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * (U.q u) ^ p * H :=
      Finset.sum_le_sum fun u hu => hrow u hu
    have hsumEq :
        (∑ u ∈ rows,
          C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * (U.q u) ^ p * H) =
            (C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * H) *
              ∑ u ∈ rows, (U.q u) ^ p := by
      calc
        _ = ∑ u ∈ rows,
            (C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * H) * (U.q u) ^ p := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hleft : 0 ≤ C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * H := by
      dsimp [H]
      positivity
    have hcoeff :
        (C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * H) *
            ∑ u ∈ rows, (U.q u) ^ p ≤ M * H := by
      calc
        _ ≤ (C0 * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * H) *
            (B * 2 ^ p * T ^ (α + p)) := mul_le_mul_of_nonneg_left hqsum hleft
        _ = M * H := by dsimp [M]; ring
    calc
      ‖K ξ w z‖ ≤ ∑ u ∈ rows, ‖rowKernel R sd W η U HA HC u Z ξ w z‖ := by
        simpa [K] using hsumNorm
      _ ≤ _ := hsumBound
      _ = _ := hsumEq
      _ ≤ _ := hcoeff
      _ = _ := by simp [H, mul_assoc, mul_left_comm, mul_comm]
  have hinnerZ (tξ tw : ℝ) :
      ‖vertical (4 / 10) (fun z => K
          ((1 + δ1 : ℝ) + tξ * Complex.I) ((3 / 1000 : ℝ) + tw * Complex.I) z)‖ ≤
        M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-2 : ℝ) := by
    let gZ : ℝ → ℝ := fun tz =>
      (M * (1 + |tw|) ^ (-2 : ℝ)) *
        (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv))
    have hgZ : Integrable gZ := by
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        (rows_integrable_shifted_gaussian_poly Aconv tξ hAconv).const_mul
          (M * (1 + |tw|) ^ (-2 : ℝ))
    have hgZ0 : ∀ tz, 0 ≤ gZ tz := by intro tz; dsimp [gZ]; positivity
    have hboundZ : ∀ tz : ℝ, ‖(fun z => K
        ((1 + δ1 : ℝ) + tξ * Complex.I) ((3 / 1000 : ℝ) + tw * Complex.I) z)
          ((4 / 10 : ℝ) + tz * Complex.I)‖ ≤ gZ tz := by
      intro tz
      have h := hline tξ tw tz
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (4 / 10)
      (fun z => K ((1 + δ1 : ℝ) + tξ * Complex.I) ((3 / 1000 : ℝ) + tw * Complex.I) z)
      gZ hgZ hgZ0 hboundZ
    calc
      _ ≤ ∫ tz : ℝ, gZ tz := hv
      _ = (M * (1 + |tw|) ^ (-2 : ℝ)) *
          ∫ tz : ℝ, Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-Aconv) := by
            dsimp [gZ]
            rw [integral_const_mul]
      _ ≤ (M * (1 + |tw|) ^ (-2 : ℝ)) *
          (Cconv * (1 + |tξ|) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hconv tξ) (by positivity)
      _ = M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-2 : ℝ) := by ring
  have hinnerW (tξ : ℝ) :
      ‖vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z => K
          ((1 + δ1 : ℝ) + tξ * Complex.I) w z))‖ ≤
        M * Cconv * I * (1 + |tξ|) ^ (-2 : ℝ) := by
    let fW : ℂ → ℂ := fun w => vertical (4 / 10) (fun z => K
      ((1 + δ1 : ℝ) + tξ * Complex.I) w z)
    let gW : ℝ → ℝ := fun tw =>
      (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * (1 + |tw|) ^ (-2 : ℝ)
    have hgW : Integrable gW := by
      simpa [gW, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIint.const_mul (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ))
    have hgW0 : ∀ tw, 0 ≤ gW tw := by intro tw; dsimp [gW]; positivity
    have hboundW : ∀ tw : ℝ, ‖fW ((3 / 1000 : ℝ) + tw * Complex.I)‖ ≤ gW tw := by
      intro tw
      have h := hinnerZ tξ tw
      simpa [fW, gW, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (3 / 1000) fW gW hgW hgW0 hboundW
    calc
      _ ≤ ∫ tw : ℝ, gW tw := hv
      _ = (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * I := by
        dsimp [gW, I]
        rw [integral_const_mul]
      _ = M * Cconv * I * (1 + |tξ|) ^ (-2 : ℝ) := by ring
  have htriple :
      ‖tripleVertical (1 + δ1) (3 / 1000) (4 / 10) K‖ ≤ M * Cconv * I * I := by
    let fξ : ℂ → ℂ := fun ξ => vertical (3 / 1000) (fun w => vertical (4 / 10) (fun z =>
      K ξ w z))
    let gξ : ℝ → ℝ := fun tξ => (M * Cconv * I) * (1 + |tξ|) ^ (-2 : ℝ)
    have hgξ : Integrable gξ := by
      simpa [gξ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIint.const_mul (M * Cconv * I)
    have hgξ0 : ∀ tξ, 0 ≤ gξ tξ := by intro tξ; dsimp [gξ]; positivity
    have hboundξ : ∀ tξ : ℝ,
        ‖fξ ((1 + δ1 : ℝ) + tξ * Complex.I)‖ ≤ gξ tξ := by
      intro tξ
      have h := hinnerW tξ
      simpa [fξ, gξ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral (1 + δ1) fξ gξ hgξ hgξ0 hboundξ
    change ‖vertical (1 + δ1) fξ‖ ≤ M * Cconv * I * I
    calc
      _ ≤ ∫ tξ : ℝ, gξ tξ := hv
      _ = (M * Cconv * I) * I := by
        dsimp [gξ, I]
        rw [integral_const_mul]
      _ = M * Cconv * I * I := by ring
  have hMbound : M * Cconv * I * I =
      Cpre * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + p) := by
    dsimp [M, Cpre]
    ring
  have hbaseNonneg :
      0 ≤ Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + p) := by
    positivity
  have hCprele : Cpre ≤ C := by dsimp [C]; linarith
  have htargetExp : α + p = α + 1 / 2 - 4 / 10 + ε := by
    dsimp [p]
    ring
  refine ⟨?_, ?_⟩
  · exact hrowEq
  · calc
      ‖rowContribution R sd W η U rows Z‖ =
          ‖tripleVertical (1 + δ1) (3 / 1000) (4 / 10) K‖ := by rw [hrowEq]
      _ ≤ M * Cconv * I * I := htriple
      _ = Cpre * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + p) := hMbound
      _ ≤ C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) * T ^ (α + p) := by
        calc
          _ = (Cpre * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10)) * T ^ (α + p) := by ring
          _ ≤ (C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10)) * T ^ (α + p) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hCprele (Real.rpow_nonneg hZpos.le _))
              (Real.rpow_nonneg hTpos.le _)
          _ = _ := by ring
      _ = C * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (α + 1 / 2 - 4 / 10 + ε) := by rw [htargetExp]
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
  intro hEuler ε hε
  let HA0 : HeckeAnalysis F := Classical.choice (heckeAnalysis_exists F)
  let HC0 : EulerCorrection R η U := {
    H := fun u p => ∏' v : {v : FinPlace F // v ∉ S.Sf},
      normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)
    H_eq := by intro u p; rfl
  }
  obtain ⟨A0, C0, Cconv, hA0, hC0, hCconv, hconv, hcontrol⟩ :=
    rows_far_kernel_control R sd W η U HA0 HC0 hEuler ε hε
  obtain ⟨_, _, Ccount, hCcount, hcount⟩ := frequency_norm_count_from_data S D η U
  let Iw : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-A0)
  let Iξ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hIwInt : Integrable (fun t : ℝ => (1 + |t|) ^ (-A0)) := rows_integrable_poly_decay hA0
  have hIξInt : Integrable (fun t : ℝ => (1 + |t|) ^ (-2 : ℝ)) :=
    rows_integrable_poly_decay (by norm_num)
  have hIw : 0 ≤ Iw := by
    dsimp [Iw]
    exact integral_nonneg fun t => by positivity
  have hIξ : 0 ≤ Iξ := by
    dsimp [Iξ]
    exact integral_nonneg fun t => by positivity
  let Cpre : ℝ := C0 * Ccount * (2 : ℝ) ^ ε * Cconv * Iw * Iξ
  let C : ℝ := Cpre + 1
  have hCpre : 0 ≤ Cpre := by dsimp [Cpre]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Z T hZ hT rows hrows
  have hZpos : 1 < Z := by linarith
  have hTpow : 1 < Z ^ (10001 / 100000 : ℝ) :=
    Real.one_lt_rpow hZpos (by norm_num)
  have hTgt : 1 < T := lt_trans hTpow hT
  have hTge : 1 ≤ T := hTgt.le
  obtain ⟨hfinite, hcountBound⟩ := hcount T hTge
  let shell : Set U.U := {u | T ≤ U.q u ∧ U.q u < 2 * T}
  have hsubset : (rows : Set U.U) ⊆ shell := by
    intro u hu
    have hmem := hrows u hu
    simpa [shell, frequencyDyad] using hmem.2
  have hcardNat : rows.card ≤ shell.ncard := by
    calc
      rows.card = (rows : Set U.U).ncard := (Set.ncard_coe_finset rows).symm
      _ ≤ shell.ncard := Set.ncard_le_ncard hsubset hfinite
  have hcard : (rows.card : ℝ) ≤ Ccount * T := by
    calc
      (rows.card : ℝ) ≤ (shell.ncard : ℝ) := by exact_mod_cast hcardNat
      _ ≤ Ccount * T := hcountBound
  have hqsum :
      (∑ u ∈ rows, (U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε) ≤
        Ccount * 2 ^ ε * T ^ (1 - (350000 : ℝ) + ε) := by
    calc
      _ ≤ ∑ _u ∈ rows, 2 ^ ε * T ^ (-(350000 : ℝ) + ε) := by
        apply Finset.sum_le_sum
        intro u hu
        have hmem := hrows u hu
        have hfreq := hmem.2
        change T ≤ U.q u ∧ U.q u < 2 * T at hfreq
        exact rows_far_qpower_bound T (U.q u) ε hTge
          hfreq.1 hfreq.2 hε
      _ = (rows.card : ℝ) * (2 ^ ε * T ^ (-(350000 : ℝ) + ε)) := by simp
      _ ≤ (Ccount * T) * (2 ^ ε * T ^ (-(350000 : ℝ) + ε)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Ccount * 2 ^ ε * T ^ (1 - (350000 : ℝ) + ε) := by
        have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTge
        have hTcombine : T * T ^ (-(350000 : ℝ) + ε) =
            T ^ (1 + (-(350000 : ℝ) + ε)) := by
          calc
            _ = T ^ (1 : ℝ) * T ^ (-(350000 : ℝ) + ε) := by
              congr 1
              exact (Real.rpow_one T).symm
            _ = T ^ (1 + (-(350000 : ℝ) + ε)) := by rw [← Real.rpow_add hTpos]
        calc
          _ = Ccount * 2 ^ ε * (T * T ^ (-(350000 : ℝ) + ε)) := by ring
          _ = Ccount * 2 ^ ε * T ^ (1 + (-(350000 : ℝ) + ε)) := by rw [hTcombine]
          _ = _ := by ring_nf
  let Zpow : ℝ := Z ^ Estar 4 4 350000
  let Tpow : ℝ := T ^ (1 - (350000 : ℝ) + ε)
  let M : ℝ := C0 * Ccount * (2 : ℝ) ^ ε * Zpow * Tpow
  have hM : 0 ≤ M := by dsimp [M, Zpow, Tpow]; positivity
  have hline (tξ tw tz : ℝ) :
      ‖∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z
        (4 + tξ * Complex.I) (4 + tw * Complex.I) (350000 + tz * Complex.I)‖ ≤
        M * Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) *
          (1 + |tw|) ^ (-A0) := by
    let ξ : ℂ := 4 + tξ * Complex.I
    let w : ℂ := 4 + tw * Complex.I
    let z : ℂ := 350000 + tz * Complex.I
    have hξ : ξ.re = 4 := by simp [ξ]
    have hw : w.re = 4 := by simp [w]
    have hzre : z.re = 350000 := by simp [z]
    have hzim : z.im = tz := by simp [z]
    have hξim : ξ.im = tξ := by simp [ξ]
    have hwin : w.im = tw := by simp [w]
    have hrow (u : U.U) (hu : u ∈ rows) :
        ‖rowKernel R sd W η U HA0 HC0 u Z ξ w z‖ ≤
          C0 * Zpow * ((U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε) *
            (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) *
              (1 + |tw|) ^ (-A0)) := by
      have h := hcontrol Z hZ u ξ w z hξ hw
        (by rw [hzre]; norm_num) (by rw [hzre])
      simpa [Zpow, ξ, w, z, hzre, hzim, hξim, hwin, mul_assoc, mul_left_comm, mul_comm]
        using h
    have hheight : 0 ≤ Real.exp (-((tξ + tz) ^ 2)) *
        (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0) := by positivity
    have hsumNorm := norm_sum_le rows (fun u => rowKernel R sd W η U HA0 HC0 u Z ξ w z)
    have hsumBound :
        (∑ u ∈ rows, ‖rowKernel R sd W η U HA0 HC0 u Z ξ w z‖) ≤
          ∑ u ∈ rows, C0 * Zpow *
            ((U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε) *
              (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) :=
      Finset.sum_le_sum fun u hu => hrow u hu
    have hsumEq :
        (∑ u ∈ rows, C0 * Zpow *
          ((U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε) *
            (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0))) =
        (C0 * Zpow * (Real.exp (-((tξ + tz) ^ 2)) *
          (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0))) *
          ∑ u ∈ rows, (U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε := by
      calc
        _ = ∑ u ∈ rows, ((C0 * Zpow * (Real.exp (-((tξ + tz) ^ 2)) *
              (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0))) *
            ((U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε)) := by
              apply Finset.sum_congr rfl
              intro u hu
              ring
        _ = _ := by rw [Finset.mul_sum]
    have hcoeff : C0 * Zpow *
        (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) *
          ∑ u ∈ rows, (U.q u) ^ (-(350000 : ℝ)) * (U.q u) ^ ε ≤ M *
            (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) := by
      have hq : 0 ≤ C0 * Z ^ Estar 4 4 350000 *
          (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) := by
        positivity
      calc
        _ ≤ C0 * Zpow *
            (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) *
              (Ccount * 2 ^ ε * Tpow) := by
          simpa [Tpow] using mul_le_mul_of_nonneg_left hqsum hq
        _ = M * (Real.exp (-((tξ + tz) ^ 2)) *
            (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) := by
          dsimp [M, Zpow, Tpow]
          ring
    calc
      _ ≤ _ := hsumNorm.trans hsumBound
      _ = _ := hsumEq
      _ ≤ M * (Real.exp (-(tξ + tz) ^ 2) *
          (1 + |tz|) ^ (-A0) * (1 + |tw|) ^ (-A0)) := hcoeff
      _ = _ := by ring
  have hinnerZ (tξ tw : ℝ) :
      ‖vertical 350000 (fun z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z
          (4 + tξ * Complex.I) (4 + tw * Complex.I) z)‖ ≤
        M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-A0) := by
    let gZ : ℝ → ℝ := fun tz =>
      (M * (1 + |tw|) ^ (-A0)) *
        (Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0))
    have hgZ : Integrable gZ := by
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        (rows_integrable_shifted_gaussian_poly A0 tξ hA0).const_mul
          (M * (1 + |tw|) ^ (-A0))
    have hgZ0 : ∀ tz, 0 ≤ gZ tz := by intro tz; dsimp [gZ]; positivity
    have hboundZ : ∀ tz : ℝ, ‖(fun z => ∑ u ∈ rows,
        rowKernel R sd W η U HA0 HC0 u Z (4 + tξ * Complex.I)
          (4 + tw * Complex.I) z) (350000 + tz * Complex.I)‖ ≤ gZ tz := by
      intro tz
      have h := hline tξ tw tz
      simpa [gZ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral 350000
      (fun z => ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z
        (4 + tξ * Complex.I) (4 + tw * Complex.I) z) gZ hgZ hgZ0 hboundZ
    calc
      _ ≤ ∫ tz : ℝ, gZ tz := hv
      _ = (M * (1 + |tw|) ^ (-A0)) *
          ∫ tz : ℝ, Real.exp (-((tξ + tz) ^ 2)) * (1 + |tz|) ^ (-A0) := by
            dsimp [gZ]
            rw [integral_const_mul]
      _ ≤ (M * (1 + |tw|) ^ (-A0)) *
          (Cconv * (1 + |tξ|) ^ (-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hconv tξ) (by positivity)
      _ = M * Cconv * (1 + |tξ|) ^ (-2 : ℝ) * (1 + |tw|) ^ (-A0) := by ring
  have hinnerW (tξ : ℝ) :
      ‖vertical 4 (fun w => vertical 350000 (fun z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z
          (4 + tξ * Complex.I) w z))‖ ≤
        M * Cconv * Iw * (1 + |tξ|) ^ (-2 : ℝ) := by
    let fW : ℂ → ℂ := fun w => vertical 350000 (fun z =>
      ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z (4 + tξ * Complex.I) w z)
    let gW : ℝ → ℝ := fun tw =>
      (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * (1 + |tw|) ^ (-A0)
    have hgW : Integrable gW := by
      simpa [gW, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIwInt.const_mul (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ))
    have hgW0 : ∀ tw, 0 ≤ gW tw := by intro tw; dsimp [gW]; positivity
    have hboundW : ∀ tw : ℝ, ‖fW (4 + tw * Complex.I)‖ ≤ gW tw := by
      intro tw
      have h := hinnerZ tξ tw
      simpa [fW, gW, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral 4 fW gW hgW hgW0 hboundW
    calc
      _ ≤ ∫ tw : ℝ, gW tw := hv
      _ = (M * Cconv * (1 + |tξ|) ^ (-2 : ℝ)) * Iw := by
        dsimp [gW, Iw]
        rw [integral_const_mul]
      _ = M * Cconv * Iw * (1 + |tξ|) ^ (-2 : ℝ) := by ring
  have htriple :
      ‖tripleVertical 4 4 350000 (fun ξ w z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z)‖ ≤
        M * Cconv * Iw * Iξ := by
    let fξ : ℂ → ℂ := fun ξ => vertical 4 (fun w => vertical 350000 (fun z =>
      ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z))
    let gξ : ℝ → ℝ := fun tξ => (M * Cconv * Iw) * (1 + |tξ|) ^ (-2 : ℝ)
    have hgξ : Integrable gξ := by
      simpa [gξ, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul] using
        hIξInt.const_mul (M * Cconv * Iw)
    have hgξ0 : ∀ tξ, 0 ≤ gξ tξ := by intro tξ; dsimp [gξ]; positivity
    have hboundξ : ∀ tξ : ℝ, ‖fξ (4 + tξ * Complex.I)‖ ≤ gξ tξ := by
      intro tξ
      have h := hinnerW tξ
      simpa [fξ, gξ, mul_assoc, mul_left_comm, mul_comm] using h
    have hv := rows_vertical_norm_le_integral 4 fξ gξ hgξ hgξ0 hboundξ
    change ‖vertical 4 fξ‖ ≤ M * Cconv * Iw * Iξ
    calc
      _ ≤ ∫ tξ : ℝ, gξ tξ := hv
      _ = (M * Cconv * Iw) * Iξ := by
        dsimp [gξ, Iξ]
        rw [integral_const_mul]
      _ = M * Cconv * Iw * Iξ := by ring
  have hinitial := rows_initial_rowContribution_eq R sd W η U HA0 HC0 hEuler Z rows
  have hshift :
      tripleVertical 4 4 2 (fun ξ w z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z) =
      tripleVertical 4 4 350000 (fun ξ w z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z) := by
    unfold tripleVertical
    apply rows_vertical_congr 4
    intro tξ
    let ξ : ℂ := 4 + tξ * Complex.I
    have hξ : ξ.re = 4 := by simp [ξ]
    apply rows_vertical_congr 4
    intro tw
    let w : ℂ := 4 + tw * Complex.I
    have hw : w.re = 4 := by simp [w]
    exact rows_far_z_shift R sd W η U HA0 HC0 hEuler ε hε Z hZ
      rows ξ w hξ hw
  have hrowEq : rowContribution R sd W η U rows Z =
      tripleVertical 4 4 350000 (fun ξ w z =>
        ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z) := hinitial.trans hshift
  have hEfar : Estar 4 4 350000 =
      3849 / 1000 + (1 / 10 : ℝ) * 350000 := by
    norm_num [Estar, a, b, h0]
  have hMbound : M * Cconv * Iw * Iξ =
      Cpre * Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε) := by
    dsimp [M, Cpre, Zpow, Tpow]
    ring
  have hbaseNonneg : 0 ≤ Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε) := by
    positivity
  have hCprele : Cpre ≤ C := by dsimp [C]; linarith
  calc
    ‖rowContribution R sd W η U rows Z‖ =
        ‖tripleVertical 4 4 350000 (fun ξ w z =>
          ∑ u ∈ rows, rowKernel R sd W η U HA0 HC0 u Z ξ w z)‖ := by rw [hrowEq]
    _ ≤ M * Cconv * Iw * Iξ := htriple
    _ = Cpre * Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε) := hMbound
    _ ≤ C * Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε) := by
      calc
        _ = Cpre * (Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε)) := by ring
        _ ≤ C * (Z ^ Estar 4 4 350000 * T ^ (1 - (350000 : ℝ) + ε)) :=
          mul_le_mul_of_nonneg_right hCprele hbaseNonneg
        _ = _ := by ring
    _ = C * Z ^ (3849 / 1000 + (1 / 10 : ℝ) * 350000) *
        T ^ (1 - (350000 : ℝ) + ε) := by rw [hEfar]
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

private theorem dyadic_power_tail_sum (p x : ℝ) (hp : p < 0) (hx : 1 ≤ x) :
    Summable (fun j : ℕ => if x < (2 : ℝ) ^ j then ((2 : ℝ) ^ j) ^ p else 0) ∧
      (∑' j : ℕ, if x < (2 : ℝ) ^ j then ((2 : ℝ) ^ j) ^ p else 0) ≤
        x ^ p / (1 - (2 : ℝ) ^ p) := by
  classical
  obtain ⟨N, hNlo, hNhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  let J : ℕ := N + 1
  let r : ℝ := (2 : ℝ) ^ p
  let g : ℕ → ℝ := fun j => if x < (2 : ℝ) ^ j then ((2 : ℝ) ^ j) ^ p else 0
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hp
  have hpower (j : ℕ) : ((2 : ℝ) ^ j) ^ p = r ^ j :=
    (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) p j).symm
  have hcut (j : ℕ) : x < (2 : ℝ) ^ j ↔ J ≤ j := by
    constructor
    · intro hj
      by_contra hnot
      have hjN : j ≤ N := by dsimp [J] at hnot; omega
      have hle : (2 : ℝ) ^ j ≤ x :=
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjN).trans hNlo
      linarith
    · intro hj
      have hle : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ j :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
      exact lt_of_lt_of_le hNhi hle
  have hshift (n : ℕ) : g (n + J) = ((2 : ℝ) ^ J) ^ p * r ^ n := by
    have hmem : x < (2 : ℝ) ^ (n + J) := (hcut (n + J)).mpr (by omega)
    simp only [g, if_pos hmem]
    rw [pow_add, Real.mul_rpow (by positivity) (by positivity), hpower n]
    ring
  have hsumShift : Summable (fun n : ℕ => g (n + J)) := by
    exact ((summable_geometric_of_lt_one hrpos.le hr).mul_left (((2 : ℝ) ^ J) ^ p)).congr
      fun n => (hshift n).symm
  have hsum : Summable g := (summable_nat_add_iff J).mp hsumShift
  have hprefix : ∑ j ∈ Finset.range J, g j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : ¬ x < (2 : ℝ) ^ j := by
      rw [hcut]
      exact Nat.not_le.mpr (Finset.mem_range.mp hj)
    simp [g, hnot]
  have htsum : (∑' j, g j) = ∑' n, g (n + J) := by
    have heq := hsum.sum_add_tsum_nat_add J
    rw [hprefix, zero_add] at heq
    exact heq.symm
  have hpowLe : ((2 : ℝ) ^ J) ^ p ≤ x ^ p :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hNhi.le hp.le
  refine ⟨hsum, ?_⟩
  change (∑' j, g j) ≤ x ^ p / (1 - r)
  calc
    _ = ((2 : ℝ) ^ J) ^ p * (1 - r)⁻¹ := by
      rw [htsum]
      simp_rw [hshift]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hrpos.le hr]
    _ ≤ x ^ p * (1 - r)⁻¹ :=
      mul_le_mul_of_nonneg_right hpowLe (inv_nonneg.mpr (by linarith))
    _ = _ := (div_eq_mul_inv _ _).symm

include HA HC ZD in
private theorem nonprincipalDyad_range_bounds (hEuler : EulerHypotheses R η) :
    ∃ Cs Ce Cg Cf Z0 : ℝ, 0 < Cs ∧ 0 < Ce ∧ 0 < Cg ∧ 0 < Cf ∧ 2 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T →
      (T ≤ Z ^ (9 / 100 : ℝ) →
        ‖nonprincipalDyad R sd W η U DE T Z‖ ≤
          Cs * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
            T ^ (11 / 10 + 1 / 100000 : ℝ)) ∧
      (Z ^ (9 / 100 : ℝ) < T → T ≤ Z ^ (10001 / 100000 : ℝ) →
        ‖nonprincipalDyad R sd W η U DE T Z‖ ≤
          Ce * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
            T ^ (6 / 10 + 1 / 100000 : ℝ) +
          Cg * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
            T ^ (11 / 10 + 1 / 100000 : ℝ) +
          Cg * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
            T ^ (-9 / 10 + 1 / 100000 : ℝ)) ∧
      (Z ^ (10001 / 100000 : ℝ) < T →
        ‖nonprincipalDyad R sd W η U DE T Z‖ ≤
          Cf * Z ^ (3849 / 1000 + (1 / 10 : ℝ) * 350000) *
            T ^ (1 - (350000 : ℝ) + 1 / 100000)) := by
  classical
  obtain ⟨Ccount, hCcount, hcount⟩ :=
    (frequency_norm_count_from_data S D η U).2.2
  obtain ⟨Cs, hCs, hsmall⟩ := zf_small_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    hEuler 1 Ccount (1 / 100000) (by norm_num) hCcount (by norm_num)
  obtain ⟨Ce, hCe, hexc⟩ := zf_small_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    hEuler (1 / 2) ZD.Cexc (1 / 100000) (by norm_num) ZD.Cexc_pos (by norm_num)
  let A1 : ℝ := 2 / ZD.ρ
  have hA1 : 1 / ZD.ρ < A1 := by
    dsimp [A1]
    exact div_lt_div_of_pos_right (by norm_num : (1 : ℝ) < 2) ZD.ρ_pos
  have hρA1 : ZD.ρ * A1 = 2 := by
    dsimp [A1]
    field_simp [ne_of_gt ZD.ρ_pos]
  obtain ⟨Cg, Zg, hCg, hZg, hgood⟩ := zf_intermediate_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
    (ZD := ZD) hEuler (1 / 100000) A1 (by norm_num) hA1
  obtain ⟨Cf, hCf, hfar⟩ := zf_far_rows
    (R := R) (sd := sd) (W := W) (η := η) (U := U)
    hEuler (1 / 100000) (by norm_num)
  let Z0 : ℝ := max Zg (ZD.U0 ^ (100 / 9 : ℝ))
  refine ⟨Cs, Ce, Cg, Cf, Z0, hCs, hCe, hCg, hCf,
    hZg.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT
  have hZZg : Zg ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2 ≤ Z := hZg.trans hZZg
  have hZpos : 0 < Z := by linarith
  have hTpos : 0 < T := by linarith
  have hOnset : ZD.U0 ≤ Z ^ (9 / 100 : ℝ) := by
    have hbase : ZD.U0 ^ (100 / 9 : ℝ) ≤ Z := (le_max_right _ _).trans hZ
    calc
      ZD.U0 = (ZD.U0 ^ (100 / 9 : ℝ)) ^ (9 / 100 : ℝ) := by
        rw [← Real.rpow_mul (by linarith [ZD.U0_two])]
        norm_num
      _ ≤ Z ^ (9 / 100 : ℝ) := Real.rpow_le_rpow
        (Real.rpow_nonneg (by linarith [ZD.U0_two]) _) hbase (by norm_num)
  have hrows : ∀ u ∈ DE.rows T, u ≠ U.one ∧ u ∈ frequencyDyad η U T :=
    fun u hu => (DE.mem_rows T hT u).1 hu
  have hcard : ((DE.rows T).card : ℝ) ≤ Ccount * T ^ (1 : ℝ) := by
    obtain ⟨hfin, hbound⟩ := hcount T hT
    have hsub : DE.rows T ⊆ hfin.toFinset := by
      intro u hu
      exact hfin.mem_toFinset.mpr (hrows u hu).2
    calc
      _ ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ Ccount * T := by
        simpa only [Set.ncard_eq_toFinset_card _ hfin] using hbound
      _ = _ := by rw [Real.rpow_one]
  refine ⟨?_, ?_, ?_⟩
  · intro hsmallRange
    have hs := (hsmall T Z hT hZ2 (DE.rows T) hrows hcard).2
    convert hs using 1 <;> congr 1 <;> ring
  · intro hTlo hThi
    have hU0 : ZD.U0 ≤ T := hOnset.trans hTlo.le
    have hT2 : 2 ≤ T := ZD.U0_two.trans hU0
    let bad : Finset U.U := (DE.rows T).filter (fun u => u ∈ ZD.E T)
    let good : Finset U.U := (DE.rows T).filter (fun u => u ∉ ZD.E T)
    have hbadSub : bad ⊆ DE.rows T := Finset.filter_subset _ _
    have hgoodSub : good ⊆ DE.rows T := Finset.filter_subset _ _
    have hbadRows : ∀ u ∈ bad, u ≠ U.one ∧ u ∈ frequencyDyad η U T :=
      fun u hu => hrows u (hbadSub hu)
    have hgoodRows : ∀ u ∈ good,
        u ≠ U.one ∧ u ∈ frequencyDyad η U T ∧ u ∉ ZD.E T := by
      intro u hu
      exact ⟨(hrows u (hgoodSub hu)).1, (hrows u (hgoodSub hu)).2,
        (Finset.mem_filter.mp hu).2⟩
    have hbadCard : (bad.card : ℝ) ≤ ZD.Cexc * T ^ (1 / 2 : ℝ) := by
      have hsub : bad ⊆ ZD.E T := by
        intro u hu
        exact (Finset.mem_filter.mp hu).2
      calc
        _ ≤ ((ZD.E T).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
        _ ≤ _ := ZD.E_count T hU0
    have hbadBound : ‖rowContribution R sd W η U bad Z‖ ≤
        Ce * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (6 / 10 + 1 / 100000 : ℝ) := by
      have hb := (hexc T Z hT hZ2 bad hbadRows hbadCard).2
      convert hb using 1 <;> congr 1 <;> ring
    have hg := hgood Z T hZZg hTlo hThi hU0 good hgoodRows
    have hrem : ‖rowContribution R sd W η U good Z -
        goodCentral R sd W η U HA HC ZD good T Z‖ ≤
        Cg * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (-9 / 10 + 1 / 100000 : ℝ) := by
      have hr := hg.2
      rw [hρA1] at hr
      convert hr using 1 <;> congr 1 <;> ring
    have hgoodBound : ‖rowContribution R sd W η U good Z‖ ≤
        Cg * Z ^ Estar (998 / 1000) (3 / 1000) (4 / 10) *
          T ^ (11 / 10 + 1 / 100000 : ℝ) +
        Cg * Z ^ Estar (1 + δ1) (3 / 1000) (4 / 10) *
          T ^ (-9 / 10 + 1 / 100000 : ℝ) := by
      calc
        _ ≤ ‖goodCentral R sd W η U HA HC ZD good T Z‖ +
            ‖rowContribution R sd W η U good Z -
              goodCentral R sd W η U HA HC ZD good T Z‖ := by
          simpa only [norm_sub_rev] using
            norm_le_insert (goodCentral R sd W η U HA HC ZD good T Z)
              (rowContribution R sd W η U good Z)
        _ ≤ _ := add_le_add hg.1 hrem
    have hsplit : rowContribution R sd W η U (DE.rows T) Z =
        rowContribution R sd W η U bad Z + rowContribution R sd W η U good Z := by
      rw [rowContribution_eq_sum (R := R) (sd := sd) (W := W) (η := η)
        (U := U) (HA := HA) (HC := HC) hEuler T Z hT2 hZ2 (DE.rows T) hrows,
        rowContribution_eq_sum (R := R) (sd := sd) (W := W) (η := η)
          (U := U) (HA := HA) (HC := HC) hEuler T Z hT2 hZ2 bad hbadRows,
        rowContribution_eq_sum (R := R) (sd := sd) (W := W) (η := η)
          (U := U) (HA := HA) (HC := HC) hEuler T Z hT2 hZ2 good
            (fun u hu => hrows u (hgoodSub hu))]
      exact (Finset.sum_filter_add_sum_filter_not (DE.rows T)
        (fun u => u ∈ ZD.E T) (fun u => rowContribution R sd W η U {u} Z)).symm
    change ‖rowContribution R sd W η U (DE.rows T) Z‖ ≤ _
    rw [hsplit]
    calc
      _ ≤ ‖rowContribution R sd W η U bad Z‖ + ‖rowContribution R sd W η U good Z‖ :=
        norm_add_le _ _
      _ ≤ _ := by simpa only [add_assoc] using add_le_add hbadBound hgoodBound
  · intro hfarRange
    exact hfar Z T hZ2 hfarRange (DE.rows T) hrows

/-- zf:row-sum, 06:632–645: complex sum bound plus absolute convergence of the dyadic series. -/
theorem zf_row_sum : EulerHypotheses R η → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  Summable (fun j : ℕ => ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖) ∧
  ‖∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤ C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  intro hEuler
  obtain ⟨HA⟩ := heckeAnalysis_exists F
  let HC : EulerCorrection R η U := canonicalEulerCorrection R η U
  obtain ⟨ZD⟩ := zeroDensityData_nonempty (η := η) (U := U) (HA := HA)
  obtain ⟨Cs, Ce, Cg, Cf, Z0, hCs, hCe, hCg, hCf, hZ0, hRanges⟩ :=
    nonprincipalDyad_range_bounds (R := R) (sd := sd) (W := W) (η := η)
      (U := U) (HA := HA) (HC := HC) (ZD := ZD) (DE := DE) hEuler
  let ps : ℝ := 11 / 10 + 1 / 100000
  let pe : ℝ := 6 / 10 + 1 / 100000
  let pr : ℝ := -9 / 10 + 1 / 100000
  generalize hpf_eq : (1 - (350000 : ℝ) + 1 / 100000) = pf
  let el : ℝ := Estar (1 + δ1) (3 / 1000) (4 / 10)
  let eg : ℝ := Estar (998 / 1000) (3 / 1000) (4 / 10)
  let ef : ℝ := 3849 / 1000 + (1 / 10 : ℝ) * 350000
  let target : ℝ := 7 / 15 - 4 / 10000
  let Ks : ℝ := (2 : ℝ) ^ ps / ((2 : ℝ) ^ ps - 1)
  let Ke : ℝ := (2 : ℝ) ^ pe / ((2 : ℝ) ^ pe - 1)
  let Kr : ℝ := (1 - (2 : ℝ) ^ pr)⁻¹
  let Kf : ℝ := (1 - (2 : ℝ) ^ pf)⁻¹
  have hps : 0 < ps := by norm_num [ps]
  have hpe : 0 < pe := by norm_num [pe]
  have hpr : pr < 0 := by norm_num [pr]
  have hpf : pf < 0 := by rw [← hpf_eq]; norm_num
  have hKs : 0 < Ks := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hps))
  have hKe : 0 < Ke := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hpe))
  have hKr : 0 < Kr := inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hpr))
  have hKf : 0 < Kf := inv_pos.mpr (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hpf))
  let C : ℝ := Cs * Ks + Ce * Ke + Cg * Ks + Cg * Kr + Cf * Kf
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos
      (add_pos (add_pos (add_pos (mul_pos hCs hKs) (mul_pos hCe hKe))
        (mul_pos hCg hKs)) (mul_pos hCg hKr)) (mul_pos hCf hKf)
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z hZ
  have hZ2 : 2 ≤ Z := hZ0.trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZpos : 0 < Z := by linarith
  let xlo : ℝ := Z ^ (9 / 100 : ℝ)
  let xhi : ℝ := Z ^ (10001 / 100000 : ℝ)
  have hxlo : 1 ≤ xlo := Real.one_le_rpow hZ1 (by norm_num)
  have hxhi : 1 ≤ xhi := Real.one_le_rpow hZ1 (by norm_num)
  let s : ℕ → ℝ := fun j => if (2 : ℝ) ^ j ≤ xlo then ((2 : ℝ) ^ j) ^ ps else 0
  let e : ℕ → ℝ := fun j => if (2 : ℝ) ^ j ≤ xhi then ((2 : ℝ) ^ j) ^ pe else 0
  let g : ℕ → ℝ := fun j => if (2 : ℝ) ^ j ≤ xhi then ((2 : ℝ) ^ j) ^ ps else 0
  let r : ℕ → ℝ := fun j => if xlo < (2 : ℝ) ^ j then ((2 : ℝ) ^ j) ^ pr else 0
  let f : ℕ → ℝ := fun j => if xhi < (2 : ℝ) ^ j then ((2 : ℝ) ^ j) ^ pf else 0
  obtain ⟨hss, hsbound⟩ := dyadic_power_small_sum ps xlo hps hxlo
  obtain ⟨hes, hebound⟩ := dyadic_power_small_sum pe xhi hpe hxhi
  obtain ⟨hgs, hgbound⟩ := dyadic_power_small_sum ps xhi hps hxhi
  obtain ⟨hrs, hrbound⟩ := dyadic_power_tail_sum pr xlo hpr hxlo
  obtain ⟨hfs, hfbound⟩ := dyadic_power_tail_sum pf xhi hpf hxhi
  have hS : Summable (fun j => Cs * Z ^ el * s j) := hss.mul_left (Cs * Z ^ el)
  have hE : Summable (fun j => Ce * Z ^ el * e j) := hes.mul_left (Ce * Z ^ el)
  have hG : Summable (fun j => Cg * Z ^ eg * g j) := hgs.mul_left (Cg * Z ^ eg)
  have hR : Summable (fun j => Cg * Z ^ el * r j) := hrs.mul_left (Cg * Z ^ el)
  have hF : Summable (fun j => Cf * Z ^ ef * f j) := hfs.mul_left (Cf * Z ^ ef)
  let M : ℕ → ℝ := fun j => Cs * Z ^ el * s j + Ce * Z ^ el * e j +
    Cg * Z ^ eg * g j + Cg * Z ^ el * r j + Cf * Z ^ ef * f j
  have hM : Summable M := (((hS.add hE).add hG).add hR).add hF
  have hSpos (j : ℕ) : 0 ≤ Cs * Z ^ el * s j := by
    dsimp [s]; split_ifs <;> positivity
  have hEpos (j : ℕ) : 0 ≤ Ce * Z ^ el * e j := by
    dsimp [e]; split_ifs <;> positivity
  have hGpos (j : ℕ) : 0 ≤ Cg * Z ^ eg * g j := by
    dsimp [g]; split_ifs <;> positivity
  have hRpos (j : ℕ) : 0 ≤ Cg * Z ^ el * r j := by
    dsimp [r]; split_ifs <;> positivity
  have hFpos (j : ℕ) : 0 ≤ Cf * Z ^ ef * f j := by
    dsimp [f]; split_ifs <;> positivity
  have hmajor (j : ℕ) : ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤ M j := by
    have hT1 : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hb := hRanges Z ((2 : ℝ) ^ j) hZ hT1
    by_cases hsmall : (2 : ℝ) ^ j ≤ xlo
    · have hs : ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤
          Cs * Z ^ el * s j := by
        simpa only [s, if_pos hsmall] using hb.1 hsmall
      exact hs.trans (by dsimp [M]; linarith [hEpos j, hGpos j, hRpos j, hFpos j])
    · have hTlo : xlo < (2 : ℝ) ^ j := lt_of_not_ge hsmall
      by_cases hmid : (2 : ℝ) ^ j ≤ xhi
      · have hm : ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤
            Ce * Z ^ el * e j + Cg * Z ^ eg * g j + Cg * Z ^ el * r j := by
          simpa only [e, g, r, if_pos hmid, if_pos hTlo] using hb.2.1 hTlo hmid
        exact hm.trans (by dsimp [M]; linarith [hSpos j, hFpos j])
      · have hThi : xhi < (2 : ℝ) ^ j := lt_of_not_ge hmid
        have hf : ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ ≤
            Cf * Z ^ ef * f j := by
          simpa only [f, if_pos hThi, ← hpf_eq] using hb.2.2 hThi
        exact hf.trans (by dsimp [M]; linarith [hSpos j, hEpos j, hGpos j, hRpos j])
  have hnorm : Summable (fun j : ℕ =>
      ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hmajor hM
  have hPower (v β p : ℝ) : Z ^ v * (Z ^ β) ^ p = Z ^ (v + β * p) := by
    rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  have hweight (C0 K v β p Bsum : ℝ) (hC0 : 0 ≤ C0) (hK : 0 ≤ K)
      (hB : Bsum ≤ K * (Z ^ β) ^ p) (hm : v + β * p ≤ target) :
      C0 * Z ^ v * Bsum ≤ C0 * K * Z ^ target := by
    calc
      _ ≤ C0 * Z ^ v * (K * (Z ^ β) ^ p) :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hC0 (Real.rpow_nonneg hZpos.le _))
      _ = C0 * K * (Z ^ v * (Z ^ β) ^ p) := by ring
      _ = C0 * K * Z ^ (v + β * p) := by rw [hPower]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ1 hm) (mul_nonneg hC0 hK)
  have hsW : Cs * Z ^ el * (∑' j, s j) ≤ Cs * Ks * Z ^ target :=
    hweight Cs Ks el (9 / 100) ps (∑' j, s j) hCs.le hKs.le hsbound
      (by norm_num [el, ps, target, Estar, a, b, h0, δ1])
  have heW : Ce * Z ^ el * (∑' j, e j) ≤ Ce * Ke * Z ^ target :=
    hweight Ce Ke el (10001 / 100000) pe (∑' j, e j) hCe.le hKe.le hebound
      (by norm_num [el, pe, target, Estar, a, b, h0, δ1])
  have hgW : Cg * Z ^ eg * (∑' j, g j) ≤ Cg * Ks * Z ^ target :=
    hweight Cg Ks eg (10001 / 100000) ps (∑' j, g j) hCg.le hKs.le hgbound
      (by norm_num [eg, ps, target, Estar, a, b, h0, δ1])
  have hrB : (∑' j, r j) ≤ Kr * (Z ^ (9 / 100 : ℝ)) ^ pr := by
    simpa only [r, Kr, xlo, div_eq_mul_inv, mul_comm] using hrbound
  have hrW : Cg * Z ^ el * (∑' j, r j) ≤ Cg * Kr * Z ^ target :=
    hweight Cg Kr el (9 / 100) pr (∑' j, r j) hCg.le hKr.le hrB
      (by norm_num [el, pr, target, Estar, a, b, h0, δ1])
  have hfB : (∑' j, f j) ≤ Kf * (Z ^ (10001 / 100000 : ℝ)) ^ pf := by
    simpa only [f, Kf, xhi, div_eq_mul_inv, mul_comm] using hfbound
  have hfW : Cf * Z ^ ef * (∑' j, f j) ≤ Cf * Kf * Z ^ target :=
    hweight Cf Kf ef (10001 / 100000) pf (∑' j, f j) hCf.le hKf.le hfB
      (by norm_num [ef, target, ← hpf_eq])
  have htotal : (∑' j, M j) ≤ C * Z ^ target := by
    have hsplit : (∑' j, M j) =
        Cs * Z ^ el * (∑' j, s j) + Ce * Z ^ el * (∑' j, e j) +
        Cg * Z ^ eg * (∑' j, g j) + Cg * Z ^ el * (∑' j, r j) +
        Cf * Z ^ ef * (∑' j, f j) := by
      dsimp only [M]
      rw [(((hS.add hE).add hG).add hR).tsum_add hF,
        ((hS.add hE).add hG).tsum_add hR,
        (hS.add hE).tsum_add hG, hS.tsum_add hE]
      simp only [tsum_mul_left]
    rw [hsplit]
    calc
      _ ≤ Cs * Ks * Z ^ target + Ce * Ke * Z ^ target + Cg * Ks * Z ^ target +
          Cg * Kr * Z ^ target + Cf * Kf * Z ^ target := by linarith [hsW, heW, hgW, hrW, hfW]
      _ = _ := by dsimp [C]; ring
  refine ⟨hnorm, ?_⟩
  calc
    _ ≤ ∑' j, ‖nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j, M j := hnorm.tsum_le_tsum hmajor hM
    _ ≤ C * Z ^ target := htotal
/-- Absolute L-series bounds on the initial probe contours. -/
private theorem initial_contour_LS_bounds :
    ∃ CP CK B : ℝ, 0 < CP ∧ 0 < CK ∧ 0 < B ∧
      (∀ s : ℂ, s.re = 12 → ‖HA.LS S 1 s‖ ≤ CP) ∧
      (∀ s : ℂ, s.re = 4 → ‖HA.LS S 1 s‖ ≤ CK) ∧
      (∀ u : U.U, ∀ s : ℂ, s.re = 4 →
        ‖(HA.LS S (rowTwist η U u) s)⁻¹‖ ≤ B) := by
  have hPrincipal (σ : ℝ) (hσ : 1 < σ) :
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re = σ → ‖HA.LS S 1 s‖ ≤ C := by
    obtain ⟨m, ψ, hmod, hseries⟩ :=
      primitive_heckeLSeries_eq_ray (1 : HeckeChar F) one_finiteOrder ⊤ one_primitiveConductor
    let CS : ℝ := 2 ^ S.Sf.card
    let s₀ : ℂ := (σ : ℝ)
    let Cζ : ℝ := (NumberField.dedekindZeta F s₀.re).re
    let C : ℝ := Cζ * CS + 1
    have hs₀ : 1 < s₀.re := by simpa [s₀] using hσ
    have hray0 := Hecke.norm_LSeriesRay_le (K := F) (s := s₀) ψ hs₀
    have hζpos : 0 ≤ Cζ := by
      dsimp [Cζ]
      exact le_trans (norm_nonneg (Hecke.LSeriesRay ψ s₀)) hray0.1
    refine ⟨C, by dsimp [C]; positivity, ?_⟩
    intro s hs
    have hsone : 1 < s.re := by rw [hs]; exact hσ
    have hray := Hecke.norm_LSeriesRay_le (K := F) (s := s) ψ hsone
    have hcomplete : HA.L 1 s = Hecke.LSeriesRay ψ s := by
      calc
        HA.L 1 s = heckeLSeries (1 : HeckeChar F) s := HA.2.1 1 s hsone
        _ = Hecke.LSeriesRay ψ s := hseries s hsone
    have hfactor := omittedEulerFactors_norm_le (S := S)
      (χ := (1 : HeckeChar F)) one_finiteOrder s (by rw [hs]; linarith)
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
  obtain ⟨CP, hCP, hCPbound⟩ := hPrincipal 12 (by norm_num)
  obtain ⟨CK, hCK, hCKbound⟩ := hPrincipal 4 (by norm_num)
  let B : ℝ := (NumberField.dedekindZeta F (4 : ℂ)).re *
    omittedEulerFactorsInverseConstant (S := S) + 1
  have hζpos : 0 ≤ (NumberField.dedekindZeta F (4 : ℂ)).re := by
    obtain ⟨m, ψ, hmod, hseries⟩ :=
      primitive_heckeLSeries_eq_ray (1 : HeckeChar F) one_finiteOrder ⊤ one_primitiveConductor
    exact le_trans (norm_nonneg (Hecke.LSeriesRay ψ (4 : ℂ)))
      (by simpa using (Hecke.norm_LSeriesRay_le (K := F) (s := (4 : ℂ)) ψ (by norm_num)).1)
  have hB : 0 < B := by
    have hCF := (omittedEulerFactors_inv_bound (S := S) (1 : HeckeChar F) one_finiteOrder).1
    dsimp [B]
    positivity
  refine ⟨CP, CK, B, hCP, hCK, hB, hCPbound, hCKbound, ?_⟩
  intro u
  obtain ⟨f, hf⟩ := U.omega_primitive u
  obtain ⟨m, ψ, hmod, hseries⟩ :=
    primitive_heckeLSeries_eq_ray (U.omega u) (U.omega_finiteOrder u) f hf
  have hF := omittedEulerFactors_inv_bound (S := S) (U.omega u) (U.omega_finiteOrder u)
  let Cζ : ℝ := (NumberField.dedekindZeta F (4)).re
  let s₀ : ℂ := (4 : ℝ)
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
  have hfactorBound := hF.2 s (by rw [hsEq]; norm_num [δ1])
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
    _ ≤ (NumberField.dedekindZeta F (4)).re *
        omittedEulerFactorsInverseConstant (S := S) + 1 := by
      dsimp [Cζ]
      linarith

/-- Absolute frequency summability and unique finite dyadic shells. -/
private theorem frequency_absolute_dyads :
    Summable (fun u : U.U => (U.q u) ^ (-5 / 4 : ℝ)) ∧
      Countable U.U ∧ Nonempty (DyadEnumeration η U) ∧
        ∀ u : U.U, ∃! j : ℕ, u ∈ frequencyDyad η U ((2 : ℝ) ^ j) := by
  classical
  obtain ⟨Cc, hCc, hcount⟩ := (frequency_norm_count_from_data S D η U).2.2
  let shell : ℕ → Set U.U := fun j => frequencyDyad η U ((2 : ℝ) ^ j)
  have hT1 (j : ℕ) : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hfin (j : ℕ) : (shell j).Finite := (hcount ((2 : ℝ) ^ j) (hT1 j)).1
  have hpartition : ∀ u : U.U, ∃! j : ℕ, u ∈ shell j := by
    intro u
    obtain ⟨N, hNlo, hNhi⟩ := exists_nat_pow_near (U.q_ge_one u)
      (by norm_num : (1 : ℝ) < 2)
    have hN : u ∈ shell N := by
      exact ⟨hNlo, by simpa [pow_succ, mul_comm] using hNhi⟩
    refine ⟨N, hN, ?_⟩
    intro k hk
    change (2 : ℝ) ^ k ≤ U.q u ∧ U.q u < 2 * (2 : ℝ) ^ k at hk
    rcases lt_trichotomy k N with hlt | heq | hgt
    · have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ N :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hle : 2 * (2 : ℝ) ^ k ≤ U.q u := by
        simpa [pow_succ, mul_comm] using hp.trans hNlo
      exact False.elim ((not_lt_of_ge hle) hk.2)
    · exact heq
    · have hp : (2 : ℝ) ^ (N + 1) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      exact False.elim ((not_lt_of_ge (hp.trans hk.1)) hNhi)
  have hsumShell (j : ℕ) : Summable (fun u : shell j => (U.q u) ^ (-5 / 4 : ℝ)) := by
    letI : Fintype (shell j) := (hfin j).fintype
    exact Summable.of_finite
  let ratio : ℝ := (2 : ℝ) ^ (-1 / 4 : ℝ)
  have hratio0 : 0 ≤ ratio := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hratio1 : ratio < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeom : Summable (fun j : ℕ => Cc * ratio ^ j) :=
    (summable_geometric_of_lt_one hratio0 hratio1).mul_left Cc
  have hbound (j : ℕ) : (∑' u : shell j, (U.q u) ^ (-5 / 4 : ℝ)) ≤ Cc * ratio ^ j := by
    let T : ℝ := (2 : ℝ) ^ j
    have hTpos : 0 < T := by dsimp [T]; positivity
    have hcard : ((hfin j).toFinset.card : ℝ) ≤ Cc * T := by
      rw [← Set.ncard_eq_toFinset_card _ (hfin j)]
      exact (hcount T (hT1 j)).2
    have hsum : (∑' u : shell j, (U.q u) ^ (-5 / 4 : ℝ)) =
        ∑ u ∈ (hfin j).toFinset, (U.q u) ^ (-5 / 4 : ℝ) := by
      conv_lhs => rw [← Set.Finite.coe_toFinset (hfin j)]
      exact Finset.tsum_subtype' (hfin j).toFinset
        (fun u : U.U => (U.q u) ^ (-5 / 4 : ℝ))
    calc
      _ = ∑ u ∈ (hfin j).toFinset, (U.q u) ^ (-5 / 4 : ℝ) := hsum
      _ ≤ ∑ _u ∈ (hfin j).toFinset, T ^ (-5 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        have hShell : u ∈ shell j := (hfin j).mem_toFinset.mp hu
        exact Real.rpow_le_rpow_of_nonpos hTpos hShell.1 (by norm_num)
      _ = ((hfin j).toFinset.card : ℝ) * T ^ (-5 / 4 : ℝ) := by simp
      _ ≤ (Cc * T) * T ^ (-5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hTpos.le _)
      _ = Cc * T ^ (-1 / 4 : ℝ) := by
        rw [mul_assoc]
        nth_rw 1 [← Real.rpow_one T]
        rw [← Real.rpow_add hTpos]
        norm_num
      _ = Cc * ratio ^ j := by
        dsimp [T, ratio]
        rw [Real.rpow_pow_comm (by norm_num)]
  have hqsum : Summable (fun u : U.U => (U.q u) ^ (-5 / 4 : ℝ)) := by
    apply (summable_partition (fun u => Real.rpow_nonneg (U.q_pos u).le _)
      hpartition).2
    refine ⟨hsumShell, ?_⟩
    exact Summable.of_nonneg_of_le (fun j => tsum_nonneg fun u =>
      Real.rpow_nonneg (U.q_pos u).le _) hbound hgeom
  have hsupport : Function.support (fun u : U.U => (U.q u) ^ (-5 / 4 : ℝ)) = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (U.q_pos u) _).ne'
  have hCountable : Countable U.U := by
    have hs := hqsum.countable_support
    rw [hsupport] at hs
    exact Set.countable_univ_iff.mp hs
  let rows : ℝ → Finset U.U := fun T =>
    if hT : 1 ≤ T then (hcount T hT).1.toFinset.erase U.one else ∅
  have hDE : Nonempty (DyadEnumeration η U) := by
    refine ⟨⟨rows, ?_⟩⟩
    intro T hT u
    simp only [rows, dif_pos hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    rfl
  exact ⟨hqsum, hCountable, hDE, hpartition⟩

/-- A summable frequency and height majorant on the initial probe contours. -/
private theorem initial_rowKernel_majorant (hEuler : EulerHypotheses R η) :
    ∃ Ac Adec C Cconv : ℝ, 1 < Ac ∧ Ac ≤ Adec ∧ 0 < C ∧ 0 < Cconv ∧
      (∀ t : ℝ, ∫ v : ℝ, Real.exp (-((t + v) ^ 2)) * (1 + |v|) ^ (-Ac) ≤
        Cconv * (1 + |t|) ^ (-3 : ℝ)) ∧
      ∀ u : U.U, ∀ Z : ℝ, 2 ≤ Z → ∀ ξ w z : ℂ,
        ξ.re = 4 → w.re = 4 → z.re = 2 →
        ‖rowKernel R sd W η U HA HC u Z ξ w z‖ ≤
          C * Z ^ Estar 4 4 2 * (U.q u) ^ (-5 / 4 : ℝ) *
            Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
              (1 + |w.im|) ^ (-3 : ℝ) := by
  obtain ⟨AF, hAF, hconvK⟩ := kummer_incomplete_convexity_bound
    (R := R) (η := η) (U := U) (HA := HA) hEuler
  obtain ⟨CK0, hCK0, hK⟩ := hconvK (1 / 8) (by norm_num)
  obtain ⟨CP, CK1, B, hCP, hCK1, hB, hPbound, hK1bound, hInv⟩ :=
    initial_contour_LS_bounds (η := η) (U := U) (HA := HA)
  let CK : ℝ := CK0 + CK1
  have hCK : 0 < CK := add_pos hCK0 hCK1
  have hKall (u : U.U) (w : ℂ) (hw : w.re = 4) :
      ‖HA.LS S (U.kummer u) w‖ ≤ CK * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) *
        (2 + |w.im|) ^ AF := by
    have hqpos : 0 < U.q u := U.q_pos u
    by_cases hu : u = U.one
    · subst u
      rw [U.kummer_one, U.q_one, Real.one_rpow, mul_one]
      have hpoly : 1 ≤ (2 + |w.im|) ^ AF :=
        Real.one_le_rpow (by nlinarith [abs_nonneg w.im]) hAF.le
      calc
        _ ≤ CK1 := hK1bound w hw
        _ = CK1 * 1 := by ring
        _ ≤ CK * (2 + |w.im|) ^ AF :=
          mul_le_mul (by dsimp [CK]; linarith) hpoly (by norm_num) hCK.le
    · calc
        _ ≤ CK0 * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) * (2 + |w.im|) ^ AF :=
          hK u hu w (by rw [hw]; norm_num) (by rw [hw])
        _ ≤ _ := by gcongr; dsimp [CK]; linarith
  obtain ⟨Ac, Cconv, hAc, hCconv, hConvolution⟩ := zf_height_convolution 3 (by norm_num)
  let Adec : ℝ := max Ac (AF + 3)
  have hAcA : Ac ≤ Adec := le_max_left _ _
  have hGap : AF + 3 ≤ Adec := le_max_right _ _
  have hA : 0 < Adec := lt_of_lt_of_le (by linarith : 0 < Ac) hAcA
  obtain ⟨CD, hCD, hDecay⟩ := zf_height_decay (R := R) (sd := sd) (W := W)
    4 4 4 4 2 2 Adec (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA
  have hHP := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  obtain ⟨CH, hCH, hHbound⟩ := hHP.2.2.2 (1 / 8) (by norm_num)
  let C : ℝ := CD * CP * CK * CH * B * 2 ^ AF
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨Ac, Adec, C, Cconv, hAc, hAcA, hC, hCconv, hConvolution, ?_⟩
  intro u Z hZ ξ w z hξ hw hz
  have hZpos : 0 < Z := by linarith
  have hqpos : 0 < U.q u := U.q_pos u
  have hD : ‖Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w‖ ≤
      CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (1 + |w.im|) ^ (-Adec) := hDecay ξ w z
      (by rw [hξ]) (by rw [hξ]) (by rw [hw]) (by rw [hw]) (by rw [hz]) (by rw [hz])
  have hP : ‖HA.LS S 1 (6 * z)‖ ≤ CP := hPbound (6 * z) (by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz]
    norm_num)
  have hNeighborhood : eulerNeighborhood ![ξ,w,z] := by
    left
    refine ⟨?_, ?_, ?_⟩
    · change 998 / 1000 - 1 / 100000 < ξ.re
      rw [hξ]; norm_num
    · change 3 / 1000 - 1 / 100000 < w.re
      rw [hw]; norm_num
    · change 4 / 10 - 1 / 100000 < z.re
      rw [hz]; norm_num
  have hH : ‖HC.H u ![ξ,w,z]‖ ≤ CH * (U.q u) ^ (1 / 8 : ℝ) :=
    hHbound u ![ξ,w,z] hNeighborhood
  have hI : ‖(HA.LS S (rowTwist η U u) ξ)⁻¹‖ ≤ B := hInv u ξ hξ
  have hAbsorb := absorb_kummer_height AF Adec w.im hAF.le hGap
  have hqpow : (U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) *
      (U.q u) ^ (1 / 8 : ℝ) = (U.q u) ^ (-5 / 4 : ℝ) := by
    rw [← Real.rpow_add (U.q_pos u), ← Real.rpow_add (U.q_pos u), hz]
    norm_num
  have hmajor := rowKernel_height_majorant (R := R) (sd := sd) (W := W)
    (η := η) (U := U) (HA := HA) (HC := HC) u Z ξ w z hZpos
    hCD.le hCP.le hCK.le hCH.le hD hP (hKall u w hw) hH hI
  have hcoef0 : 0 ≤ (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
      Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) := by positivity
  have hq0 : 0 ≤ (U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) *
      (U.q u) ^ (1 / 8 : ℝ) := by positivity
  calc
    _ ≤ Z ^ Estar ξ.re w.re z.re *
        (CD * Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
          (1 + |w.im|) ^ (-Adec)) * (U.q u) ^ (-z.re) * CP *
        (CK * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) * (2 + |w.im|) ^ AF) *
        (CH * (U.q u) ^ (1 / 8 : ℝ)) * B := hmajor
    _ = (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        ((1 + |w.im|) ^ (-Adec) * (2 + |w.im|) ^ AF) *
        ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) *
          (U.q u) ^ (1 / 8 : ℝ)) := by ring
    _ ≤ (CD * CP * CK * CH * B) * Z ^ Estar ξ.re w.re z.re *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
        (2 ^ AF * (1 + |w.im|) ^ (-3 : ℝ)) *
        ((U.q u) ^ (-z.re) * (U.q u) ^ (1 / 2 + 1 / 8 : ℝ) *
          (U.q u) ^ (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAbsorb hcoef0) hq0
    _ = C * Z ^ Estar 4 4 2 * (U.q u) ^ (-5 / 4 : ℝ) *
        Real.exp (-((ξ.im + z.im) ^ 2)) * (1 + |z.im|) ^ (-Adec) *
          (1 + |w.im|) ^ (-3 : ℝ) := by
      rw [hqpow, hξ, hw, hz]
      dsimp [C]
      ring

/-- Initial-contour row integrability and summability of the L1 row norms. -/
private theorem initial_row_integrals_summable (hEuler : EulerHypotheses R η)
    (Z : ℝ) (hZ : 2 ≤ Z) :
    (∀ u : U.U, Integrable (fun t : ℝ × ℝ × ℝ =>
      rowKernel R sd W η U HA HC u Z
        (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I))) ∧
      Summable (fun u : U.U => ∫ t : ℝ × ℝ × ℝ,
        ‖rowKernel R sd W η U HA HC u Z
          (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)‖) := by
  obtain ⟨hqsum, hCountable, hDE, hPart⟩ := frequency_absolute_dyads (η := η) (U := U)
  obtain ⟨Ac, Adec, C, Cconv, hAc, hAcA, hC, hCconv, hConvolution, hPoint⟩ :=
    initial_rowKernel_majorant (R := R) (sd := sd) (W := W) (η := η)
      (U := U) (HA := HA) (HC := HC) hEuler
  have hZpos : 0 < Z := by linarith
  have hAdec : 0 < Adec := by linarith
  have hAcpos : 0 < Ac := by linarith
  let ξLine : ℝ × ℝ × ℝ → ℂ := fun t => 4 + t.1 * Complex.I
  let wLine : ℝ × ℝ × ℝ → ℂ := fun t => 4 + t.2.1 * Complex.I
  let zLine : ℝ × ℝ × ℝ → ℂ := fun t => 2 + t.2.2 * Complex.I
  let J (u : U.U) (t : ℝ × ℝ × ℝ) : ℂ :=
    rowKernel R sd W η U HA HC u Z (ξLine t) (wLine t) (zLine t)
  let CZ : ℝ := C * Z ^ Estar 4 4 2
  have hCZ : 0 < CZ := mul_pos hC (Real.rpow_pos_of_pos hZpos _)
  have hξcont : Continuous ξLine := by fun_prop
  have hwcont : Continuous wLine := by fun_prop
  have hzcont : Continuous zLine := by fun_prop
  have hξre (t : ℝ × ℝ × ℝ) : (ξLine t).re = 4 := by simp [ξLine]
  have hwre (t : ℝ × ℝ × ℝ) : (wLine t).re = 4 := by simp [wLine]
  have hzre (t : ℝ × ℝ × ℝ) : (zLine t).re = 2 := by simp [zLine]
  have hLScont (χ : HeckeChar F) (hχ : IsOfFinOrder χ) :
      ContinuousOn (HA.LS S χ) {s : ℂ | 1 < s.re} := by
    have hDiff : DifferentiableOn ℂ (HA.L χ) {s : ℂ | 1 < s.re} := by
      by_cases hχ1 : χ = 1
      · rw [hχ1]
        apply HA.2.2.2.1.mono
        intro s hs
        change 1 < s.re at hs
        change s ≠ 1
        intro heq
        have hre := congrArg Complex.re heq
        norm_num at hre
        linarith
      · obtain ⟨Lc, hLc⟩ := HA.2.2.1 χ hχ hχ1
        have hEq : Lc.value = HA.L χ := hLc
        rw [← hEq]
        exact Lc.differentiable.differentiableOn
    unfold HeckeAnalysis.LS
    exact (hDiff.mul (omittedEulerFactors_differentiable (S := S) χ).differentiableOn).continuousOn
  have hWeights := (po_weights_exist (R := R) (sd := sd)).2 W
  have hM : DifferentiableOn ℂ (weightM R sd W) {s : ℂ | 0 < s.re} := hWeights.1
  have hW : Differentiable ℂ (weightW1hat W) := hWeights.2.1
  have hMline : Continuous (fun t : ℝ × ℝ × ℝ => weightM R sd W (zLine t)) :=
    hM.continuousOn.comp_continuous hzcont (by intro t; change 0 < (zLine t).re; rw [hzre]; norm_num)
  have hWline : Continuous (fun t : ℝ × ℝ × ℝ => weightW1hat W (wLine t)) :=
    hW.continuous.comp hwcont
  have hbaseX : ((Z ^ a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZpos a).ne'
  have hbaseZ : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZpos.ne'
  have hbaseY : ((Z ^ b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hZpos b).ne'
  have hXexp : Continuous (fun t : ℝ × ℝ × ℝ => (1 / 2 : ℂ) - zLine t) := by fun_prop
  have hZexp : Continuous (fun t : ℝ × ℝ × ℝ => ξLine t + zLine t - 1) := by fun_prop
  have hYexp : Continuous (fun t : ℝ × ℝ × ℝ => wLine t - 1) := by fun_prop
  have hXpow := hXexp.const_cpow (Or.inl hbaseX)
  have hZpow := hZexp.const_cpow (Or.inl hbaseZ)
  have hYpow := hYexp.const_cpow (Or.inl hbaseY)
  have hExp : Continuous (fun t : ℝ × ℝ × ℝ =>
      Complex.exp ((ξLine t + zLine t - 1) ^ 2)) := by fun_prop
  have hMellin : Continuous (fun t : ℝ × ℝ × ℝ =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z (ξLine t) (wLine t) (zLine t)) := by
    unfold mellinWeight
    exact (((((hXpow.mul hZpow).mul hYpow).mul hExp).mul hMline).mul hWline)
  have hHP := po_H_product (R := R) (η := η) (U := U) (HC := HC) hEuler
  let pLine : ℝ × ℝ × ℝ → Triple := fun t => ![ξLine t, wLine t, zLine t]
  have hpcont : Continuous pLine := by fun_prop
  have heuler (t : ℝ × ℝ × ℝ) : eulerNeighborhood (pLine t) := by
    left
    refine ⟨?_, ?_, ?_⟩
    · change 998 / 1000 - 1 / 100000 < (ξLine t).re
      rw [hξre]; norm_num
    · change 3 / 1000 - 1 / 100000 < (wLine t).re
      rw [hwre]; norm_num
    · change 4 / 10 - 1 / 100000 < (zLine t).re
      rw [hzre]; norm_num
  have hJmeas (u : U.U) : Measurable (J u) := by
    have hqbase : (U.q u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (U.q_pos u).ne'
    have hqexp : Continuous (fun t : ℝ × ℝ × ℝ => -(zLine t)) := by fun_prop
    have hqpow := hqexp.const_cpow (Or.inl hqbase)
    have hKfin := kummer_finiteOrder (η := η) (U := U) u hEuler.1
    have hKline : Continuous (fun t : ℝ × ℝ × ℝ => HA.LS S (U.kummer u) (wLine t)) :=
      (hLScont (U.kummer u) hKfin).comp_continuous hwcont
        (by intro t; change 1 < (wLine t).re; rw [hwre]; norm_num)
    have hScont : Continuous (fun t : ℝ × ℝ × ℝ => 6 * zLine t) := by fun_prop
    have hPline : Continuous (fun t : ℝ × ℝ × ℝ => HA.LS S 1 (6 * zLine t)) :=
      (hLScont 1 one_finiteOrder).comp_continuous hScont (by
        intro t
        change 1 < (6 * zLine t).re
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre]
        norm_num)
    have hHline : Continuous (fun t : ℝ × ℝ × ℝ => HC.H u (pLine t)) :=
      (hHP.2.1 u).continuousOn.comp_continuous hpcont heuler
    have hrowEq : rowTwist η U u = U.omega u := by
      simpa [rowTwist] using (U.omega_induces_twist u).symm
    have hrowFin : IsOfFinOrder (rowTwist η U u) := by
      rw [hrowEq]; exact U.omega_finiteOrder u
    have hRline : Continuous (fun t : ℝ × ℝ × ℝ => HA.LS S (rowTwist η U u) (ξLine t)) :=
      (hLScont _ hrowFin).comp_continuous hξcont
        (by intro t; change 1 < (ξLine t).re; rw [hξre]; norm_num)
    dsimp [J, rowKernel]
    exact ((((hMellin.measurable.mul hqpow.measurable).mul hPline.measurable).mul
      hKline.measurable).mul hHline.measurable).div hRline.measurable
  have hpoint (u : U.U) (t : ℝ × ℝ × ℝ) : ‖J u t‖ ≤
      CZ * (U.q u) ^ (-5 / 4 : ℝ) * Real.exp (-((t.1 + t.2.2) ^ 2)) *
        (1 + |t.2.2|) ^ (-Adec) * (1 + |t.2.1|) ^ (-3 : ℝ) := by
    simpa [J, CZ, ξLine, wLine, zLine, mul_assoc] using
      hPoint u Z hZ (ξLine t) (wLine t) (zLine t) (hξre t) (hwre t) (hzre t)
  have hWpoly : Integrable (fun t : ℝ => (1 + |t|) ^ (-3 : ℝ)) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 := by simp
    simpa [Real.norm_eq_abs] using (integrable_one_add_norm (E := ℝ) hdim)
  have hGaussian : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  let Iw : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-3 : ℝ)
  have hIw : 0 ≤ Iw := integral_nonneg (fun _ => by positivity)
  let CInt : ℝ := CZ * Iw * Cconv * Iw
  have hCInt : 0 ≤ CInt := by dsimp [CInt]; positivity
  have hFiber (u : U.U) (t : ℝ) :
      Integrable (fun v : ℝ × ℝ => J u (t, v)) (volume.prod volume) := by
    have hqpos : 0 < U.q u := U.q_pos u
    let D0 : ℝ := CZ * (U.q u) ^ (-5 / 4 : ℝ) * Real.exp (t ^ 2)
    have hDom : Integrable (fun v : ℝ × ℝ =>
        D0 * ((1 + |v.1|) ^ (-3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2)))
        (volume.prod volume) := (hWpoly.mul_prod hGaussian).const_mul D0
    have hMeas : AEStronglyMeasurable (fun v : ℝ × ℝ => J u (t, v)) (volume.prod volume) :=
      ((hJmeas u).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
    apply hDom.mono' hMeas
    exact Filter.Eventually.of_forall (fun v => by
      have hzpoly : (1 + |v.2|) ^ (-Adec) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg v.2]) (by linarith)
      calc
        _ ≤ CZ * (U.q u) ^ (-5 / 4 : ℝ) * Real.exp (-((t + v.2) ^ 2)) *
            (1 + |v.2|) ^ (-Adec) * (1 + |v.1|) ^ (-3 : ℝ) := hpoint u (t, v)
        _ ≤ CZ * (U.q u) ^ (-5 / 4 : ℝ) *
            (Real.exp (t ^ 2) * Real.exp (-(1 / 2 : ℝ) * v.2 ^ 2)) * 1 *
              (1 + |v.1|) ^ (-3 : ℝ) := by
          gcongr
          · exact gaussian_shift_bound t v.2
        _ = _ := by dsimp [D0]; ring)
  have hDouble (u : U.U) (t : ℝ) :
      (∫ v : ℝ × ℝ, ‖J u (t, v)‖) ≤
        (CZ * (U.q u) ^ (-5 / 4 : ℝ)) * Iw * Cconv * (1 + |t|) ^ (-3 : ℝ) := by
    have hqpos : 0 < U.q u := U.q_pos u
    have hd := double_height_integral_bound (σw := 4) (σz := 2)
      (fun w z => rowKernel R sd W η U HA HC u Z (4 + t * Complex.I) w z)
      (hFiber u t) Adec Ac 3 (CZ * (U.q u) ^ (-5 / 4 : ℝ)) Cconv t
      hAdec hAcpos hAcA (by positivity) hCconv.le
      (fun v => by simpa [J, ξLine, wLine, zLine] using hpoint u (t, v))
      (hConvolution t)
    simpa [J, ξLine, wLine, zLine, Iw] using hd
  have hOuter (u : U.U) : Integrable (fun t : ℝ => ∫ v : ℝ × ℝ, ‖J u (t, v)‖) := by
    have hs : StronglyMeasurable (fun t : ℝ => ∫ v : ℝ × ℝ, ‖J u (t, v)‖) :=
      (hJmeas u).norm.stronglyMeasurable.integral_prod_right'
    have hd := hWpoly.const_mul ((CZ * (U.q u) ^ (-5 / 4 : ℝ)) * Iw * Cconv)
    apply hd.mono' hs.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun v => norm_nonneg _))]
      exact hDouble u t)
  have hTriple (u : U.U) : Integrable (J u) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    apply (integrable_prod_iff (hJmeas u).stronglyMeasurable.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (fun t => ?_), hOuter u⟩
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact hFiber u t
  have hL1 (u : U.U) : (∫ t : ℝ × ℝ × ℝ, ‖J u t‖) ≤ CInt * (U.q u) ^ (-5 / 4 : ℝ) := by
    have hProd : Integrable (fun t : ℝ × (ℝ × ℝ) => ‖J u t‖) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
      exact (hTriple u).norm
    calc
      _ = ∫ t : ℝ, ∫ v : ℝ × ℝ, ‖J u (t, v)‖ := by
        rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
        exact integral_prod (fun t : ℝ × (ℝ × ℝ) => ‖J u t‖) hProd
      _ ≤ ∫ t : ℝ, ((CZ * (U.q u) ^ (-5 / 4 : ℝ)) * Iw * Cconv) *
          (1 + |t|) ^ (-3 : ℝ) :=
        integral_mono (hOuter u)
          (hWpoly.const_mul ((CZ * (U.q u) ^ (-5 / 4 : ℝ)) * Iw * Cconv))
          (hDouble u)
      _ = ((CZ * (U.q u) ^ (-5 / 4 : ℝ)) * Iw * Cconv) * Iw := by
        rw [integral_const_mul]
      _ = _ := by dsimp [CInt]; ring
  have hRowsum : Summable (fun u : U.U => ∫ t : ℝ × ℝ × ℝ, ‖J u t‖) :=
    Summable.of_nonneg_of_le (fun u => integral_nonneg (fun t => norm_nonneg _))
      hL1 (hqsum.mul_left CInt)
  exact ⟨hTriple, hRowsum⟩

include HA HC in
/-- Exact initial probe decomposition, with absolute interchange and dyad regrouping. -/
private theorem probe_eq_principal_add_dyads (hEuler : EulerHypotheses R η)
    (hWeight : WeightSpec R sd W) (Z : ℝ) (hZ : 2 ≤ Z) :
    probe R W (Z ^ a) (Z ^ b) Z =
      rowContribution R sd W η U {U.one} Z +
        ∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z := by
  classical
  obtain ⟨hqsum, hCountable, hDE, hPart⟩ := frequency_absolute_dyads (η := η) (U := U)
  letI : Countable U.U := hCountable
  obtain ⟨hRowInt, hRowNormSum⟩ := initial_row_integrals_summable
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC) hEuler Z hZ
  let κ : ℂ := 1 / (2 * Real.pi)
  let J (u : U.U) (t : ℝ × ℝ × ℝ) : ℂ := rowKernel R sd W η U HA HC u Z
    (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)
  have hTriple (f : ℂ → ℂ → ℂ → ℂ)
      (hf : Integrable (fun t : ℝ × ℝ × ℝ =>
        f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I))) :
      tripleVertical 4 4 2 f = κ ^ 3 * ∫ t : ℝ × ℝ × ℝ,
        f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) := by
    let G (t : ℝ × (ℝ × ℝ)) : ℂ :=
      f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)
    have hp : Integrable G (volume.prod volume) := by
      rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
      exact hf
    have hPair : ∀ᵐ t : ℝ, vertical 4 (fun w => vertical 2 (fun z =>
        f (4 + t * Complex.I) w z)) = κ ^ 2 * ∫ v : ℝ × ℝ, G (t, v) := by
      filter_upwards [hp.prod_right_ae] with t ht
      exact vertical_pair_eq_integral_prod (σw := 4) (σz := 2)
        (fun w z => f (4 + t * Complex.I) w z) ht
    change κ * (∫ t : ℝ, vertical 4 (fun w => vertical 2 (fun z =>
      f (4 + t * Complex.I) w z))) = _
    calc
      _ = κ * ∫ t : ℝ, κ ^ 2 * ∫ v : ℝ × ℝ, G (t, v) := by
        congr 1
        exact integral_congr_ae hPair
      _ = κ ^ 3 * ∫ t : ℝ, ∫ v : ℝ × ℝ, G (t, v) := by
        rw [integral_const_mul]
        ring
      _ = _ := by
        change κ ^ 3 * (∫ t : ℝ, ∫ v : ℝ × ℝ, G (t, v)) =
          κ ^ 3 * ∫ p : ℝ × (ℝ × ℝ), G p
        rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
        exact congrArg (fun x : ℂ => κ ^ 3 * x) (integral_prod G hp).symm
  have hRaw := (prop_euler_product (R := R) (η := η) (U := U) (HA := HA) (HC := HC) hEuler).2.1
  have hInitial (t : ℝ × ℝ × ℝ) : initialRegion
      (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) := by
    norm_num [initialRegion]
  have hRowEq (u : U.U) (t : ℝ × ℝ × ℝ) :
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z
        (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) *
      ((U.q u : ℂ) ^ (-(2 + t.2.2 * Complex.I)) *
        calF R η U u (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I)
          (2 + t.2.2 * Complex.I)) = J u t := by
    rw [hRaw u _ _ _ (hInitial t)]
    dsimp [J, rowKernel, rowTwist]
    simp only [div_eq_mul_inv]
    ring
  have hFinite (rows : Finset U.U) : rowContribution R sd W η U rows Z =
      ∑ u ∈ rows, κ ^ 3 * ∫ t : ℝ × ℝ × ℝ, J u t := by
    let f : ℂ → ℂ → ℂ → ℂ := fun ξ w z =>
      mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
        ∑ u ∈ rows, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z
    have heq : (fun t : ℝ × ℝ × ℝ =>
        f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)) =
        fun t : ℝ × ℝ × ℝ => ∑ u ∈ rows, J u t := by
      funext t
      dsimp [f]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun u hu => hRowEq u t)
    have hf : Integrable (fun t : ℝ × ℝ × ℝ =>
        f (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)) := by
      rw [heq]
      exact integrable_finsetSum rows (fun u hu => hRowInt u)
    change tripleVertical 4 4 2 f = _
    rw [hTriple f hf, heq, integral_finsetSum rows (fun u hu => hRowInt u), Finset.mul_sum]
  have hsingle (u : U.U) : rowContribution R sd W η U {u} Z =
      κ ^ 3 * ∫ t : ℝ × ℝ × ℝ, J u t := by
    simpa only [Finset.sum_singleton] using hFinite {u}
  have hFiniteAdd (rows : Finset U.U) : rowContribution R sd W η U rows Z =
      ∑ u ∈ rows, rowContribution R sd W η U {u} Z := by
    rw [hFinite]
    exact Finset.sum_congr rfl (fun u hu => (hsingle u).symm)
  have hIntegralSum : Summable (fun u : U.U => ∫ t : ℝ × ℝ × ℝ, J u t) :=
    (hasSum_integral_of_summable_integral_norm hRowInt hRowNormSum).summable
  have hSumRow : Summable (fun u : U.U => rowContribution R sd W η U {u} Z) :=
    (hIntegralSum.mul_left (κ ^ 3)).congr (fun u => (hsingle u).symm)
  have hZpos : 0 < Z := by linarith
  obtain ⟨hAbsolute, hTotalInt, hProbe⟩ := po_mellin_triple
    (R := R) (sd := sd) (W := W) (η := η) (U := U) hWeight (Z ^ a) (Z ^ b) Z
      (Real.rpow_pos_of_pos hZpos a) (Real.rpow_pos_of_pos hZpos b) hZpos
  let total : ℂ → ℂ → ℂ → ℂ := fun ξ w z =>
    mellinWeight R sd W (Z ^ a) (Z ^ b) Z ξ w z *
      ∑' u : U.U, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z
  have hTotalEq : (fun t : ℝ × ℝ × ℝ => total
      (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)) =
      fun t : ℝ × ℝ × ℝ => ∑' u : U.U, J u t := by
    funext t
    dsimp [total]
    rw [← tsum_mul_left]
    exact tsum_congr (fun u => hRowEq u t)
  have hMain : probe R W (Z ^ a) (Z ^ b) Z =
      ∑' u : U.U, rowContribution R sd W η U {u} Z := by
    calc
      _ = tripleVertical 4 4 2 total := hProbe
      _ = κ ^ 3 * ∫ t : ℝ × ℝ × ℝ, total
          (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) :=
        hTriple total hTotalInt
      _ = κ ^ 3 * ∫ t : ℝ × ℝ × ℝ, ∑' u : U.U, J u t := by rw [hTotalEq]
      _ = κ ^ 3 * ∑' u : U.U, ∫ t : ℝ × ℝ × ℝ, J u t := by
        rw [← integral_tsum_of_summable_integral_norm hRowInt hRowNormSum]
      _ = _ := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun u => (hsingle u).symm)
  let NU := {u : U.U // u ∉ ({U.one} : Finset U.U)}
  let index : NU → ℕ := fun u => (hPart u.1).choose
  have hNonSum : Summable (fun u : NU => rowContribution R sd W η U {u.1} Z) :=
    hSumRow.subtype (fun u => u ∉ ({U.one} : Finset U.U))
  have hIndexShell (u : NU) : u.1 ∈ frequencyDyad η U ((2 : ℝ) ^ (index u)) :=
    (hPart u.1).choose_spec.1
  let fiberEquiv (j : ℕ) : (index ⁻¹' {j}) ≃ (DE.rows ((2 : ℝ) ^ j) : Set U.U) := {
    toFun := fun v => by
      have hidx : index v.1 = j := v.2
      have hShell := hIndexShell v.1
      rw [hidx] at hShell
      exact ⟨v.1.1, (DE.mem_rows _ (one_le_pow₀ (by norm_num)) _).2
        ⟨by simpa only [Finset.mem_singleton] using v.1.2, hShell⟩⟩
    invFun := fun u => by
      have hm := (DE.mem_rows _ (one_le_pow₀ (by norm_num)) u.1).1 u.2
      have hnot : u.1 ∉ ({U.one} : Finset U.U) := by
        simpa only [Finset.mem_singleton] using hm.1
      refine ⟨⟨u.1, hnot⟩, ?_⟩
      change index ⟨u.1, hnot⟩ = j
      exact ((hPart u.1).choose_spec.2 j hm.2).symm
    left_inv := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro u
      apply Subtype.ext
      rfl }
  have hFiber (j : ℕ) :
      (∑' v : index ⁻¹' {j}, rowContribution R sd W η U {v.1.1} Z) =
        nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z := by
    calc
      _ = ∑' u : (DE.rows ((2 : ℝ) ^ j) : Set U.U),
          rowContribution R sd W η U {u.1} Z := by
        simpa [fiberEquiv] using (fiberEquiv j).tsum_eq
          (fun u : (DE.rows ((2 : ℝ) ^ j) : Set U.U) => rowContribution R sd W η U {u.1} Z)
      _ = ∑ u ∈ DE.rows ((2 : ℝ) ^ j), rowContribution R sd W η U {u} Z :=
        Finset.tsum_subtype' (DE.rows ((2 : ℝ) ^ j))
          (fun u : U.U => rowContribution R sd W η U {u} Z)
      _ = rowContribution R sd W η U (DE.rows ((2 : ℝ) ^ j)) Z :=
        (hFiniteAdd (DE.rows ((2 : ℝ) ^ j))).symm
      _ = _ := rfl
  have hRegroup : (∑' u : NU, rowContribution R sd W η U {u.1} Z) =
      ∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z := by
    have hs := hNonSum.hasSum.tsum_fiberwise index
    calc
      _ = ∑' j : ℕ, ∑' v : index ⁻¹' {j}, rowContribution R sd W η U {v.1.1} Z :=
        hs.tsum_eq.symm
      _ = _ := tsum_congr hFiber
  have hSplit : rowContribution R sd W η U {U.one} Z +
      (∑' u : NU, rowContribution R sd W η U {u.1} Z) =
        ∑' u : U.U, rowContribution R sd W η U {u} Z := by
    simpa only [Finset.sum_singleton] using
      hSumRow.sum_add_tsum_subtype_compl ({U.one} : Finset U.U)
  calc
    _ = ∑' u : U.U, rowContribution R sd W η U {u} Z := hMain
    _ = rowContribution R sd W η U {U.one} Z +
        (∑' u : NU, rowContribution R sd W η U {u.1} Z) := hSplit.symm
    _ = _ := by rw [hRegroup]

/-- `zf:probe-asymptotic`, 06:647–681, for the actual probe and exact principal scalar. The
corrected probe-low route consumes the split Gauss data from `sol-gate-a2b`. -/
theorem zf_probe_asymptotic
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  EulerHypotheses R η → (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) → WeightSpec R sd W → ∃ C Z0 : ℝ, 0 < C ∧ 2 ≤ Z0 ∧ ∀ Z, Z0 ≤ Z →
  ‖probe R W (Z ^ a) (Z ^ b) Z - principalConstant R sd W HA * principalSignal R η U HA HC Z‖ ≤
    C * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) := by
  intro hEuler hloc hWeight
  obtain ⟨hqsum, hCountable, hDE, hPart⟩ := frequency_absolute_dyads (η := η) (U := U)
  obtain ⟨DE⟩ := hDE
  obtain ⟨Cr, Zr, hCr, hZr, hRows⟩ := zf_row_sum
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (DE := DE) hEuler
  obtain ⟨hc0, Cp, Zp, hCp, hZp, hPrincipal⟩ := zf_principal_row
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
      hEuler hloc hWeight
  let Z0 : ℝ := max Zp Zr
  refine ⟨2 * Cp + Cr, Z0, by linarith, hZp.trans (le_max_left _ _), ?_⟩
  intro Z hZ
  have hZZp : Zp ≤ Z := (le_max_left _ _).trans hZ
  have hZZr : Zr ≤ Z := (le_max_right _ _).trans hZ
  have hZ2 : 2 ≤ Z := hZp.trans hZZp
  have hZ1 : 1 ≤ Z := by linarith
  have hp := hPrincipal Z hZZp
  have hr := (hRows Z hZZr).2
  have hExact := probe_eq_principal_add_dyads
    (R := R) (sd := sd) (W := W) (η := η) (U := U) (HA := HA) (HC := HC)
      (DE := DE) hEuler hWeight Z hZ2
  have hSubtract : probe R W (Z ^ a) (Z ^ b) Z -
      principalConstant R sd W HA * principalSignal R η U HA HC Z =
        principalRw R sd W η U HA HC Z + principalRz R sd W η U HA HC Z +
          ∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z := by
    rw [hExact, hp.1]
    ring
  have hPower : Z ^ ((7 / 15 - 5 / 10000 : ℝ)) ≤
      Z ^ ((7 / 15 - 4 / 10000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
  rw [hSubtract]
  calc
    _ ≤ ‖principalRw R sd W η U HA HC Z‖ + ‖principalRz R sd W η U HA HC Z‖ +
        ‖∑' j : ℕ, nonprincipalDyad R sd W η U DE ((2 : ℝ) ^ j) Z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ Cp * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) +
        Cp * Z ^ ((7 / 15 - 5 / 10000 : ℝ)) + Cr * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) :=
      add_le_add (add_le_add hp.2.1 hp.2.2) hr
    _ ≤ Cp * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) +
        Cp * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) + Cr * Z ^ ((7 / 15 - 4 / 10000 : ℝ)) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hPower hCp.le)
        (mul_le_mul_of_nonneg_left hPower hCp.le)) (le_refl _)
    _ = _ := by ring
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

section A2DeletionProofs
open ClassFieldTheory
open scoped nonZeroDivisors

private theorem a2del_heckeCoprime_iff_isPrimeTo
    (m : RayClassModulus F) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I ↔
      Ideal.IsPrimeTo I (m.finitePart.support : Set (FinPlace F)) := by
  have hcount (v : FinPlace F) :
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 ↔
        ¬ v.asIdeal ∣ I := by
    have hcount' :
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 ↔
          ¬ v.asIdeal ∣ I := by
      simpa using not_congr (Associates.count_ne_zero_iff_dvd hI v.irreducible)
    simpa [FractionalIdeal.count_coe F v hI] using hcount'
  constructor
  · rintro ⟨hI', hp⟩
    have hp' : ∀ v, v ∈ m.finitePart.support →
        FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      intro v hv
      simpa [ArtinPrimitiveRoots.Hecke.idealUnit] using hp v hv
    rw [Ideal.isPrimeTo_iff]
    refine ⟨hI, ?_⟩
    intro v hv hdiv
    exact (hcount v).mp (hp' v hv) hdiv
  · intro hp
    refine ⟨hI, ?_⟩
    change ∀ v, v ∈ m.finitePart.support →
      FractionalIdeal.count F v
        ((ArtinPrimitiveRoots.Hecke.idealUnit I hI : NumberFieldFractionalIdealGroup F) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
    intro v hv
    apply (hcount v).mpr
    exact (Ideal.isPrimeTo_iff.mp hp).2 v hv

private theorem a2del_unramified_of_conductorDvd
    (χ : HeckeChar F) (f : Ideal (𝓞 F)) (hχ : χ.ConductorDvd f)
    (v : FinPlace F) (hexp : A1.idealExp v f = 0) : χ.UnramifiedAt v := by
  exact qsa_unramifiedAt_of_conductorDvd χ f hχ v hexp

private theorem a2del_modulusSupport_divides
    (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∈ m.finitePart.support) :
    v.asIdeal ∣ ArtinPrimitiveRoots.Dictionary.modulusIdeal m := by
  have hpos : 0 < m.finitePart v :=
    Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
  have hpow : ArtinPrimitiveRoots.Dictionary.modulusIdeal m ≤
      v.asIdeal ^ m.finitePart v := by
    change (∏ w ∈ m.finitePart.support, w.asIdeal ^ m.finitePart w) ≤ _
    exact (Ideal.prod_le_inf (s := m.finitePart.support)
      (f := fun w => w.asIdeal ^ m.finitePart w)).trans (Finset.inf_le hv)
  exact Ideal.dvd_iff_le.mpr
    (hpow.trans (Ideal.pow_le_self (Nat.ne_of_gt hpos)))

private noncomputable def a2del_modulusEnlarge
    (S : SData F CE condη) (m : RayClassModulus F) : RayClassModulus F :=
  let eS := Finsupp.onFinset S.Sf (fun v => if v ∈ S.Sf then 1 else 0)
    (by
      intro v hv
      by_contra hnot
      simp [hnot] at hv)
  ⟨m.finitePart ⊔ eS, m.infinitePart⟩

private theorem a2del_modulusEnlarge_support
    (S : SData F CE condη) (m : RayClassModulus F) :
    (a2del_modulusEnlarge S m).finitePart.support = m.finitePart.support ∪ S.Sf := by
  classical
  ext v
  simp [a2del_modulusEnlarge, Finsupp.support_sup, Finsupp.mem_support_iff,
    Finsupp.onFinset_apply]

private def a2del_rayLocalIntegralValue
    (v : FinPlace F) (y : (v.adicCompletionIntegers F).units) :
    v.adicCompletionIntegers F :=
  ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers F)ˣ).1

private theorem a2del_rayLocalHigherUnitMap_eq_one_iff_local
    (v : FinPlace F) (k : ℕ) (y : (v.adicCompletionIntegers F).units) :
    ClassFieldTheory.rayLocalHigherUnitMap v k y = 1 ↔
      a2del_rayLocalIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ k := by
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) ^ k
  change Units.map (Ideal.Quotient.mk I).toMonoidHom
      ((v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType y) = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (a2del_rayLocalIntegralValue v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _

private theorem a2del_rayLocalHigherUnitGroup_antitone
    (v : FinPlace F) {k l : ℕ} (hkl : k ≤ l) :
    ClassFieldTheory.rayLocalHigherUnitGroup v l ≤
      ClassFieldTheory.rayLocalHigherUnitGroup v k := by
  intro x hx
  change x ∈ Subgroup.map (v.adicCompletionIntegers F).units.subtype
    (ClassFieldTheory.rayLocalHigherUnitMap v l).ker at hx
  change x ∈ Subgroup.map (v.adicCompletionIntegers F).units.subtype
    (ClassFieldTheory.rayLocalHigherUnitMap v k).ker
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  change ClassFieldTheory.rayLocalHigherUnitMap v l y = 1 at hy
  change ClassFieldTheory.rayLocalHigherUnitMap v k y = 1
  rw [a2del_rayLocalHigherUnitMap_eq_one_iff_local v l y] at hy
  rw [a2del_rayLocalHigherUnitMap_eq_one_iff_local v k y]
  exact Ideal.pow_le_pow_right hkl hy

private theorem a2del_rayCongruent_le
    {m n : RayClassModulus F} (hmn : m ≤ n) {x : Fˣ}
    (hx : ClassFieldTheory.IsRayCongruent n x) : ClassFieldTheory.IsRayCongruent m x := by
  constructor
  · intro v hv
    have hvn : v ∈ n.finitePart.support := by
      apply Finsupp.mem_support_iff.mpr
      have hpos : 0 < m.finitePart v :=
        Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
      exact Nat.ne_of_gt (lt_of_lt_of_le hpos (hmn.1 v))
    exact a2del_rayLocalHigherUnitGroup_antitone v (hmn.1 v) (hx.1 v hvn)
  · intro v hv
    exact hx.2 v (hmn.2 hv)

private theorem a2del_rayPrincipalIdeals_antitone
    {m n : RayClassModulus F} (hmn : m ≤ n) :
    ClassFieldTheory.rayPrincipalIdealSubgroup n ≤
      ClassFieldTheory.rayPrincipalIdealSubgroup m := by
  apply Subgroup.closure_mono
  rintro I ⟨x, hx, hIx⟩
  exact ⟨x, a2del_rayCongruent_le hmn hx, hIx⟩

private noncomputable def a2del_rayClassProjection
    {m n : RayClassModulus F} (hmn : m ≤ n) :
    RayClassGroup n →* RayClassGroup m := by
  let hI : ClassFieldTheory.rayClassPrimeToIdeals n ≤
      ClassFieldTheory.rayClassPrimeToIdeals m := by
    intro I hI v hv
    exact hI v (Finsupp.support_mono hmn.1 hv)
  letI : (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo m).Normal :=
    Subgroup.normal_of_isMulCommutative _
  refine QuotientGroup.map (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo n)
    (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo m) (Subgroup.inclusion hI) ?_
  intro I hI'
  change (I : NumberFieldFractionalIdealGroup F) ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup n at hI'
  change (I : NumberFieldFractionalIdealGroup F) ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup m
  exact a2del_rayPrincipalIdeals_antitone hmn hI'

private theorem a2del_primeCoprimeTo
    (m : RayClassModulus F) (v : FinPlace F)
    (hv : v ∉ m.finitePart.support) :
    ArtinPrimitiveRoots.Hecke.IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  change ∀ w, w ∈ m.finitePart.support →
    FractionalIdeal.count F w
      ((ArtinPrimitiveRoots.Hecke.idealUnit v.asIdeal v.ne_bot :
        NumberFieldFractionalIdealGroup F) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
  intro w hw
  have hwv : w ≠ v := by
    intro h
    exact hv (h ▸ hw)
  simpa [ArtinPrimitiveRoots.Hecke.idealUnit] using
    (FractionalIdeal.count_maximal_coprime F w (Ne.symm hwv))

private theorem a2del_liftedChar_prime_eq
    {m n : RayClassModulus F} (hmn : m ≤ n)
    (ψ : RayClassGroup m →* ℂˣ) (v : FinPlace F)
    (hv : v ∉ n.finitePart.support) :
    ArtinPrimitiveRoots.Hecke.charValue
        (ψ.comp (a2del_rayClassProjection hmn)) v.asIdeal =
      ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal := by
  classical
  have hvM : v ∉ m.finitePart.support := by
    intro h
    exact hv (Finsupp.support_mono hmn.1 h)
  have hcopM := a2del_primeCoprimeTo m v hvM
  have hcopN := a2del_primeCoprimeTo n v hv
  have hproj : a2del_rayClassProjection hmn
      (ArtinPrimitiveRoots.Hecke.rayClass n v.asIdeal hcopN) =
        ArtinPrimitiveRoots.Hecke.rayClass m v.asIdeal hcopM := by
    simp [a2del_rayClassProjection, ArtinPrimitiveRoots.Hecke.rayClass, hcopN]
    rfl
  simp only [ArtinPrimitiveRoots.Hecke.charValue, dif_pos hcopN, dif_pos hcopM,
    MonoidHom.comp_apply]
  rw [hproj]

private theorem a2del_idealValue_prime (χ : HeckeChar F) (v : FinPlace F) :
    χ.idealValue v.asIdeal = χ.primeValue v := by
  classical
  have hirr : Irreducible v.asIdeal :=
    (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible
  unfold HeckeChar.idealValue
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
    normalize_eq]
  simp [v.isPrime, v.ne_bot]

private theorem a2del_idealValue_eq_charValue
    (χ : HeckeChar F) (f : Ideal (𝓞 F))
    (hf : IsPrimitiveConductor χ f)
    {m : RayClassModulus F} (ψ : RayClassGroup m →* ℂˣ)
    (hmod : ArtinPrimitiveRoots.Dictionary.modulusIdeal m = f)
    (hprime : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal = χ.primeValue v) :
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      χ.idealValue I = ArtinPrimitiveRoots.Hecke.charValue ψ I := by
  intro I hI
  by_cases hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m I
  · have hprimeFull : ∀ v : FinPlace F, v ∉ m.finitePart.support →
        χ.UnramifiedAt v ∧ χ.primeValue v =
          ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal := by
      intro v hv
      have hexp : A1.idealExp v f = 0 := by
        rw [← hmod, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
        exact Finsupp.notMem_support_iff.mp hv
      exact ⟨a2del_unramified_of_conductorDvd χ f hf.2.1 v hexp,
        (hprime v hv).symm⟩
    exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ψ χ hprimeFull I hc
  · have hex : ∃ v ∈ m.finitePart.support, v.asIdeal ∣ I := by
      by_contra hnot
      push_neg at hnot
      apply hc
      refine ⟨hI, ?_⟩
      intro v hv
      change FractionalIdeal.count F v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
      rw [FractionalIdeal.count_coe F v hI]
      have hcnt := (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr
        (hnot v hv)
      push_neg at hcnt
      exact_mod_cast hcnt
    obtain ⟨v, hv, hdiv⟩ := hex
    have hdivf : v.asIdeal ∣ f := by
      have hdivm := a2del_modulusSupport_divides m v hv
      rw [hmod] at hdivm
      exact hdivm
    have hzero := qs_idealValue_eq_zero_of_conductor_M0 χ f hf
      v.asIdeal I v.isPrime v.ne_bot hdivf hI hdiv
    have hchar : ArtinPrimitiveRoots.Hecke.charValue ψ I = 0 := by
      simp [ArtinPrimitiveRoots.Hecke.charValue, hc]
    rw [hzero, hchar]

private theorem a2del_norm_multiset_map_prod_le_one
    {α : Type*} (s : Multiset α) (g : α → ℂ)
    (hg : ∀ a ∈ s, ‖g a‖ ≤ 1) : ‖(s.map g).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact mul_le_one₀ (hg a (by simp)) (norm_nonneg _)
        (ih fun x hx => hg x (Multiset.mem_cons_of_mem hx))

private theorem a2del_idealValue_norm_le_one
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) (I : Ideal (𝓞 F)) :
    ‖χ.idealValue I‖ ≤ 1 := by
  unfold HeckeChar.idealValue
  apply a2del_norm_multiset_map_prod_le_one
  intro P hP
  by_cases h : P.IsPrime ∧ P ≠ ⊥
  · simpa [h] using primeValue_norm_le_one χ hχ ⟨P, h.1, h.2⟩
  · simp [h]

private noncomputable def a2del_heckeIdealWeight (χ : HeckeChar F) :
    Hecke.EulerProduct.IdealArithmeticFunction F :=
  fun I => χ.idealValue (I : Ideal (𝓞 F))

private theorem a2del_heckeIdealWeight_summable
    (χ : HeckeChar F) (hχ : IsOfFinOrder χ) {s : ℂ} (hs : 1 < s.re) :
    Summable (Hecke.EulerProduct.idealTerm (a2del_heckeIdealWeight χ) s) := by
  let f := a2del_heckeIdealWeight χ
  have hbase : Summable (fun I : (Ideal (𝓞 F))⁰ =>
      Hecke.idealNormRpowTerm s.re (I : Ideal (𝓞 F))) := by
    have h := (Hecke.summable_idealNormRpow (K := F) hs).comp_injective
      (i := fun I : (Ideal (𝓞 F))⁰ => (I : Ideal (𝓞 F))) Subtype.val_injective
    convert h using 1
    funext I
    rfl
  have hnorm : Summable (fun I : (Ideal (𝓞 F))⁰ =>
      ‖Hecke.EulerProduct.idealTerm f s I‖) := by
    refine Summable.of_nonneg_of_le (by intro I; positivity) ?_ hbase
    intro I
    rw [Hecke.EulerProduct.norm_idealTerm]
    have hNpos : 0 < (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) := by
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hNne : Ideal.absNorm (I : Ideal (𝓞 F)) ≠ 0 :=
      (Ideal.absNorm_pos_of_nonZeroDivisors I).ne'
    have hcoeff := a2del_idealValue_norm_le_one χ hχ (I : Ideal (𝓞 F))
    calc
      _ ≤ 1 / (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ^ s.re := by
        exact div_le_div_of_nonneg_right hcoeff (by positivity)
      _ = Hecke.idealNormRpowTerm s.re (I : Ideal (𝓞 F)) := by
        simp [Hecke.idealNormRpowTerm, hNne, Real.rpow_neg (le_of_lt hNpos)]
  exact Summable.of_norm hnorm

private theorem a2del_incompleteRaySeries_eq_incompleteHeckeLSeries
    (S : SData F CE condη) (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    {m : RayClassModulus F} (ψ : RayClassGroup m →* ℂˣ)
    (hvalue : ∀ I : (Ideal (𝓞 F))⁰,
      Hecke.EulerProduct.IdealArithmeticFunction.supportedPart
        (a2del_heckeIdealWeight χ) ((S.Sf : Set (FinPlace F))ᶜ) I =
          ArtinPrimitiveRoots.Hecke.charValue ψ (I : Ideal (𝓞 F)))
    {s : ℂ} (hs : 1 < s.re) :
    ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s = incompleteHeckeLSeries S χ s := by
  classical
  let f := a2del_heckeIdealWeight χ
  let Sset : Set (FinPlace F) := S.Sf
  let fS := Hecke.EulerProduct.IdealArithmeticFunction.supportedPart f Ssetᶜ
  have hvalue' : ∀ I : (Ideal (𝓞 F))⁰,
      fS I = ArtinPrimitiveRoots.Hecke.charValue ψ (I : Ideal (𝓞 F)) := hvalue
  have hχsum := a2del_heckeIdealWeight_summable χ hχ hs
  have hχsumS := Hecke.EulerProduct.summable_idealTerm_supportedPart hχsum Ssetᶜ
  have hcoeff (N : ℕ) :
      Hecke.EulerProduct.normCoeff F fS N = ArtinPrimitiveRoots.Hecke.coeff ψ N := by
    rw [Hecke.EulerProduct.normCoeff_eq_sum_normFiber]
    by_cases hN : N = 0
    · subst N
      rw [Hecke.EulerProduct.normFiber_zero]
      unfold ArtinPrimitiveRoots.Hecke.coeff
      simp only [Finset.sum_empty]
      symm
      apply Finset.sum_eq_zero
      intro I hI
      have hnorm : Ideal.absNorm I = 0 := by
        simpa only [Set.mem_setOf_eq] using
          (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) 0).mem_toFinset.mp hI
      have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
      subst I
      simp [ArtinPrimitiveRoots.Hecke.charValue, ArtinPrimitiveRoots.Hecke.IsCoprimeTo]
    · let F0 := Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) N
      change (∑ I ∈ Hecke.EulerProduct.normFiber F N, fS I) =
        ∑ I ∈ F0.toFinset, ArtinPrimitiveRoots.Hecke.charValue ψ I
      refine Finset.sum_bij (fun I _ => (I : Ideal (𝓞 F))) ?_ ?_ ?_ ?_
      · intro I hI
        exact F0.mem_toFinset.mpr
          ((Hecke.EulerProduct.mem_normFiber F).mp hI)
      · intro I hI J hJ hEq
        exact Subtype.ext hEq
      · intro J hJ
        have hnorm : Ideal.absNorm J = N := by
          simpa only [Set.mem_setOf_eq] using F0.mem_toFinset.mp hJ
        have hJ0 : J ≠ ⊥ := by
          intro hJbot
          subst J
          simp at hnorm
          exact hN hnorm.symm
        refine ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩,
          (Hecke.EulerProduct.mem_normFiber F).mpr hnorm, rfl⟩
      · intro I hI
        exact hvalue' I
  have hcoeffFun :
      Hecke.EulerProduct.normCoeff F fS = ArtinPrimitiveRoots.Hecke.coeff ψ :=
    funext hcoeff
  have hLcoeff : ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s =
      LSeries (Hecke.EulerProduct.normCoeff F fS) s := by
    unfold ArtinPrimitiveRoots.Hecke.LSeriesRay
    rw [← hcoeffFun]
  have hSupport : Function.support
      (fun I : (Ideal (𝓞 F))⁰ => Hecke.EulerProduct.idealTerm fS s I) ⊆
        {I : (Ideal (𝓞 F))⁰ | Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset} := by
    intro I hI
    have hval : fS I ≠ 0 := by
      intro hzero
      apply hI
      simp [Hecke.EulerProduct.idealTerm, hzero]
    simpa using
      (Hecke.EulerProduct.IdealArithmeticFunction.isPrimeTo_compl_of_supportedPart_apply_ne_zero hval)
  have hsubtype :
      (∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset},
        Hecke.EulerProduct.idealTerm fS s I.1) =
      ∑' I : (Ideal (𝓞 F))⁰, Hecke.EulerProduct.idealTerm fS s I :=
    tsum_subtype_eq_of_support_subset hSupport
  let T : Type := {I : Ideal (𝓞 F) //
    I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal}
  let e : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset} ≃ T := {
    toFun := fun I => ⟨(I.1 : Ideal (𝓞 F)),
      ⟨nonZeroDivisors.coe_ne_zero I.1, fun v hv hdiv =>
        (Ideal.isPrimeTo_iff.mp I.2).2 v hv (Ideal.dvd_iff_le.mpr hdiv)⟩⟩
    invFun := fun I => ⟨⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩,
      (Ideal.isPrimeTo_iff).2 ⟨I.2.1, fun v hv hdiv =>
        I.2.2 v hv (Ideal.dvd_iff_le.mp hdiv)⟩⟩
    left_inv := by intro I; cases I; rfl
    right_inv := by intro I; cases I; rfl }
  let g : T → ℂ := fun I => χ.idealValue I.1 *
    ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)
  have hterm (I : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset}) :
      g (e I) = Hecke.EulerProduct.idealTerm fS s I.1 := by
    have hcop : Ideal.IsPrimeTo (I.1 : Ideal (𝓞 F)) Sset := I.2
    have hcop' : Ideal.IsPrimeTo (I.1 : Ideal (𝓞 F)) Ssetᶜᶜ := by
      simpa using hcop
    have hfSχ : fS I.1 = χ.idealValue (I.1 : Ideal (𝓞 F)) := by
      change Hecke.EulerProduct.IdealArithmeticFunction.supportedPart f Ssetᶜ
        I.1 = _
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hcop']
      rfl
    change χ.idealValue (I.1 : Ideal (𝓞 F)) *
        ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) =
      Hecke.EulerProduct.idealTerm fS s I.1
    rw [Hecke.EulerProduct.idealTerm_def, Complex.cpow_neg,
      div_eq_mul_inv, ← hfSχ]
  calc
    ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s =
        LSeries (Hecke.EulerProduct.normCoeff F fS) s := hLcoeff
    _ = ∑' I : (Ideal (𝓞 F))⁰, Hecke.EulerProduct.idealTerm fS s I :=
      Hecke.EulerProduct.LSeries_normCoeff hχsumS
    _ = ∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset},
        Hecke.EulerProduct.idealTerm fS s I.1 := hsubtype.symm
    _ = ∑' I : T, g I := by
      calc
        _ = ∑' I : {I : (Ideal (𝓞 F))⁰ // Ideal.IsPrimeTo (I : Ideal (𝓞 F)) Sset},
            g (e I) := tsum_congr fun I => (hterm I).symm
        _ = ∑' I : T, g I := Equiv.tsum_eq e g
    _ = incompleteHeckeLSeries S χ s := by
      simp [T, g, incompleteHeckeLSeries]

private theorem a2del_LS_eq_incompleteHeckeLSeries
    (S : SData F CE condη) (HA : HeckeAnalysis F) (χ : HeckeChar F)
    (hχ : IsOfFinOrder χ) (f : Ideal (𝓞 F)) (hf : IsPrimitiveConductor χ f)
    {s : ℂ} (hs : 1 < s.re) :
    HA.LS S χ s = incompleteHeckeLSeries S χ s := by
  classical
  obtain ⟨m, ψ, hmod, _, hprime⟩ :=
    ArtinPrimitiveRoots.Dictionary.exists_rayClass_of_heckeChar χ hχ f hf.1 hf.2.1
  let mS := a2del_modulusEnlarge S m
  have hsup : mS.finitePart.support = m.finitePart.support ∪ S.Sf :=
    a2del_modulusEnlarge_support S m
  have hmn : m ≤ mS := by
    refine ⟨le_sup_left, ?_⟩
    intro v hv
    exact hv
  let ψS : RayClassGroup mS →* ℂˣ := ψ.comp (a2del_rayClassProjection hmn)
  have hprimeFull : ∀ v : FinPlace F, v ∉ m.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v =
        ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal := by
    intro v hv
    have hexp : A1.idealExp v f = 0 := by
      rw [← hmod, ArtinPrimitiveRoots.Dictionary.idealExp_modulusIdeal]
      exact Finsupp.notMem_support_iff.mp hv
    exact ⟨a2del_unramified_of_conductorDvd χ f hf.2.1 v hexp,
      (hprime v hv).symm⟩
  have hvalueFull := a2del_idealValue_eq_charValue χ f hf ψ hmod hprime
  have hfull : heckeLSeries χ s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s :=
    qsa_heckeLSeries_eq_LSeriesRay χ ψ hvalueFull hs
  have hHA : HA.L χ s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := by
    calc
      HA.L χ s = heckeLSeries χ s := HA.property.1 χ s hs
      _ = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s := hfull
  have hcharLift : ∀ v : FinPlace F, v ∉ mS.finitePart.support →
      ArtinPrimitiveRoots.Hecke.charValue ψS v.asIdeal =
        ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal := by
    intro v hv
    simpa [ψS] using a2del_liftedChar_prime_eq hmn ψ v hv
  have hchange := ArtinPrimitiveRoots.Hecke.LSeriesRay_change_modulus
    (m := mS) (n := m) ψS ψ hcharLift hs
  have hprimeZero : ∀ v : FinPlace F, v ∈ m.finitePart.support → χ.primeValue v = 0 := by
    intro v hv
    have hdivf := a2del_modulusSupport_divides m v hv
    rw [hmod] at hdivf
    have hzero := qs_idealValue_eq_zero_of_conductor_M0 χ f hf
      v.asIdeal v.asIdeal v.isPrime v.ne_bot hdivf v.ne_bot dvd_rfl
    rw [a2del_idealValue_prime] at hzero
    exact hzero
  let A := m.finitePart.support
  let B := S.Sf \ A
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    exact (Finset.mem_sdiff.mp hvB).2 hvA
  have hunion : A ∪ B = mS.finitePart.support := by
    have hAB : A ∪ B = A ∪ S.Sf := by
      ext v
      simp [B]
    have hAS : A ∪ S.Sf = mS.finitePart.support := by
      change m.finitePart.support ∪ S.Sf = mS.finitePart.support
      exact hsup.symm
    exact hAB.trans hAS
  have hprodA :
      (∏ v ∈ A, (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    rw [ArtinPrimitiveRoots.Dictionary.charValue_eq_zero_of_mem_support ψ hv]
    simp
  have hprodB :
      (∏ v ∈ B, (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
      ∏ v ∈ B, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    apply Finset.prod_congr rfl
    intro v hv
    rw [hprime v (Finset.mem_sdiff.mp hv).2]
  have hdisjS : Disjoint B (S.Sf ∩ A) := by
    rw [Finset.disjoint_left]
    intro v hvB hvI
    exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_inter.mp hvI).2
  have hunionS : B ∪ (S.Sf ∩ A) = S.Sf := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hB | hI
      · exact (Finset.mem_sdiff.mp hB).1
      · exact (Finset.mem_inter.mp hI).1
    · intro hvS
      by_cases hvA : v ∈ A
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvS, hvA⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvS, hvA⟩)
  have hprodIntersect :
      ∏ v ∈ S.Sf ∩ A, (1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    rw [hprimeZero v (Finset.mem_inter.mp hv).2]
    simp
  have hprodS :
      (∏ v ∈ S.Sf, (1 - χ.primeValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) =
      ∏ v ∈ B, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
    calc
      _ = ∏ v ∈ B ∪ (S.Sf ∩ A),
          (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
        rw [hunionS]
      _ = (∏ v ∈ B, (1 - χ.primeValue v *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) *
          ∏ v ∈ S.Sf ∩ A, (1 - χ.primeValue v *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
        rw [Finset.prod_union hdisjS]
      _ = _ := by rw [hprodIntersect]; simp
  have hfactor :
      (∏ v ∈ mS.finitePart.support,
        (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) = omittedFactors (S := S) χ s := by
    unfold omittedFactors
    calc
      _ = ∏ v ∈ A ∪ B,
          (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by rw [← hunion]
      _ = (∏ v ∈ A, (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) *
          ∏ v ∈ B, (1 - ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by rw [Finset.prod_union hdisj]
      _ = ∏ v ∈ B, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
        rw [hprodA, hprodB]
        simp
      _ = ∏ v ∈ S.Sf, (1 - χ.primeValue v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := hprodS.symm
  have hchange' : ArtinPrimitiveRoots.Hecke.LSeriesRay ψS s =
      ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s * omittedFactors (S := S) χ s := by
    rw [hfactor] at hchange
    exact hchange
  have hLSray : HA.LS S χ s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψS s := by
    calc
      HA.LS S χ s = HA.L χ s * omittedFactors (S := S) χ s := rfl
      _ = ArtinPrimitiveRoots.Hecke.LSeriesRay ψ s * omittedFactors (S := S) χ s := by
        rw [hHA]
      _ = ArtinPrimitiveRoots.Hecke.LSeriesRay ψS s := hchange'.symm
  have hχS : ∀ v : FinPlace F, v ∉ mS.finitePart.support →
      χ.UnramifiedAt v ∧ χ.primeValue v =
        ArtinPrimitiveRoots.Hecke.charValue ψS v.asIdeal := by
    intro v hv
    have hvM : v ∉ m.finitePart.support := by
      intro hvM
      exact hv (by rw [hsup]; exact Finset.mem_union_left _ hvM)
    refine ⟨(hprimeFull v hvM).1, ?_⟩
    calc
      χ.primeValue v = ArtinPrimitiveRoots.Hecke.charValue ψ v.asIdeal :=
        (hprimeFull v hvM).2
      _ = ArtinPrimitiveRoots.Hecke.charValue ψS v.asIdeal :=
        (hcharLift v hv).symm
  have hvalueS (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
      Hecke.EulerProduct.IdealArithmeticFunction.supportedPart
          (a2del_heckeIdealWeight χ) ((S.Sf : Set (FinPlace F))ᶜ)
          ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ =
        ArtinPrimitiveRoots.Hecke.charValue ψS I := by
    by_cases hcS : Ideal.IsPrimeTo I (S.Sf : Set (FinPlace F))
    · have hcS' : Ideal.IsPrimeTo I ((S.Sf : Set (FinPlace F))ᶜᶜ) := by
        simpa using hcS
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_isPrimeTo_compl hcS']
      by_cases hcM : ArtinPrimitiveRoots.Hecke.IsCoprimeTo mS I
      · exact ArtinPrimitiveRoots.Dictionary.idealValue_eq_charValue ψS χ hχS I hcM
      · have hex : ∃ v ∈ mS.finitePart.support, v.asIdeal ∣ I := by
          by_contra hnot
          push_neg at hnot
          apply hcM
          refine ⟨hI, ?_⟩
          intro v hv
          change FractionalIdeal.count F v
            (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
          rw [FractionalIdeal.count_coe F v hI]
          have hcnt := (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr
            (hnot v hv)
          push_neg at hcnt
          exact_mod_cast hcnt
        obtain ⟨v, hv, hdiv⟩ := hex
        have hvS : v ∉ S.Sf := by
          intro hvS
          exact (Ideal.isPrimeTo_iff.mp hcS).2 v hvS hdiv
        have hvM : v ∈ m.finitePart.support := by
          rw [hsup] at hv
          exact (Finset.mem_union.mp hv).resolve_right hvS
        have hdivf := a2del_modulusSupport_divides m v hvM
        rw [hmod] at hdivf
        have hzero := qs_idealValue_eq_zero_of_conductor_M0 χ f hf
          v.asIdeal I v.isPrime v.ne_bot hdivf hI hdiv
        have hchar : ArtinPrimitiveRoots.Hecke.charValue ψS I = 0 := by
          simp [ArtinPrimitiveRoots.Hecke.charValue, hcM]
        exact hzero.trans hchar.symm
    · have hcM : ¬ ArtinPrimitiveRoots.Hecke.IsCoprimeTo mS I := by
        intro hcM
        have hprimeToM : Ideal.IsPrimeTo I (mS.finitePart.support : Set (FinPlace F)) :=
          (a2del_heckeCoprime_iff_isPrimeTo mS I hI).mp hcM
        apply hcS
        apply (Ideal.isPrimeTo_iff).2
        refine ⟨hI, ?_⟩
        intro v hvS hdiv
        have hvM : v ∈ mS.finitePart.support := by
          rw [hsup]
          exact Finset.mem_union_right _ hvS
        exact (Ideal.isPrimeTo_iff.mp hprimeToM).2 v hvM hdiv
      have hcS' : ¬ Ideal.IsPrimeTo I ((S.Sf : Set (FinPlace F))ᶜᶜ) := by
        simpa using hcS
      rw [Hecke.EulerProduct.IdealArithmeticFunction.supportedPart_apply_of_not_isPrimeTo_compl hcS']
      simp [ArtinPrimitiveRoots.Hecke.charValue, hcM]
  have hvalueS' : ∀ I : (Ideal (𝓞 F))⁰,
      Hecke.EulerProduct.IdealArithmeticFunction.supportedPart
        (a2del_heckeIdealWeight χ) ((S.Sf : Set (FinPlace F))ᶜ) I =
          ArtinPrimitiveRoots.Hecke.charValue ψS (I : Ideal (𝓞 F)) := by
    intro I
    exact hvalueS (I : Ideal (𝓞 F)) (nonZeroDivisors.coe_ne_zero I)
  have hinc := a2del_incompleteRaySeries_eq_incompleteHeckeLSeries
    S χ hχ ψS hvalueS' hs
  calc
    HA.LS S χ s = ArtinPrimitiveRoots.Hecke.LSeriesRay ψS s := hLSray
    _ = incompleteHeckeLSeries S χ s := hinc

private theorem a2del_omittedFactors_nonzero
    (S : SData F CE condη) (χ : HeckeChar F) (hχ : IsOfFinOrder χ)
    {s : ℂ} (hs : 0 < s.re) : omittedFactors (S := S) χ s ≠ 0 := by
  classical
  unfold omittedFactors
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  apply sub_ne_zero.mpr
  intro heq
  have hterm : χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) = 1 := heq.symm
  have htermNorm :
      ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ = 1 := by
    rw [hterm]
    norm_num
  have hq : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hpow : ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity) _
  have hsmall : ‖χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hpow]
    calc
      ‖χ.primeValue v‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
          1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (primeValue_norm_le_one χ hχ v) (by positivity)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hs)
  exact (ne_of_lt hsmall) htermNorm

/-- Analytic producer obligation for `IncompleteDictionary`; continuation and deletion uniqueness
are not consequences of aggregate `HeckeAnalysis` fields alone (`prop:euler-product`, 05:407–433;
`prop:zero-density`, 06:165–185). -/
theorem incompleteDictionary_exists : Nonempty (IncompleteDictionary η fd HA) := by
  classical
  let inc : ∀ u : fd.U, fd.omega u ≠ 1 →
      IncompleteHeckeLContinuation S (η * (fd.kummer u)⁻¹) := by
    intro u h
    let χ : HeckeChar F := rowTwist η fd u
    have hω : fd.omega u = χ := by
      dsimp [χ, rowTwist]
      exact fd.omega_induces_twist u
    have hχ : IsOfFinOrder χ := by
      rw [← hω]
      exact fd.omega_finiteOrder u
    let C := completeFromAnalysis η fd HA u h
    have hC : C.value = HA.L χ := by
      calc
        C.value = HA.L (fd.omega u) := completeFromAnalysis_eq η fd HA u h
        _ = HA.L χ := by rw [hω]
    have hLdiff : Differentiable ℂ (HA.L χ) := by
      rw [← hC]
      exact C.differentiable
    have hFactorDiff : Differentiable ℂ (omittedFactors (S := S) χ) := by
      change Differentiable ℂ (fun s =>
        ∏ v ∈ S.Sf, (1 - χ.primeValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
      exact omittedEulerFactors_differentiable (S := S) χ
    have hLSdiff : Differentiable ℂ (HA.LS S χ) := by
      have hmul : Differentiable ℂ
          (fun s => HA.L χ s * omittedFactors (S := S) χ s) := hLdiff.mul hFactorDiff
      have heq : HA.LS S χ =
          (fun s => HA.L χ s * omittedFactors (S := S) χ s) := by
        funext s
        rfl
      rw [heq]
      exact hmul
    let f : Ideal (𝓞 F) := Classical.choose (fd.omega_primitive u)
    have hf : IsPrimitiveConductor (fd.omega u) f :=
      Classical.choose_spec (fd.omega_primitive u)
    have hfχ : IsPrimitiveConductor χ f := by
      rw [← hω]
      exact hf
    refine ⟨HA.LS S χ, hLSdiff.differentiableOn, ?_⟩
    intro s hs
    exact a2del_LS_eq_incompleteHeckeLSeries S HA χ hχ f hfχ hs
  refine ⟨{
    complete := completeFromAnalysis η fd HA
    complete_eq := completeFromAnalysis_eq η fd HA
    incomplete := inc
    incomplete_eq := ?_
    factors_nonzero := ?_
  }⟩
  · intro u h s hs
    simp [inc, rowTwist]
  · intro χ hχ s hs
    exact a2del_omittedFactors_nonzero S χ hχ hs
end A2DeletionProofs

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
