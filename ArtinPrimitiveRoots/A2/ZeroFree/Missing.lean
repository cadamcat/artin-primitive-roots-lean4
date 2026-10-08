import ArtinPrimitiveRoots.A2.ZeroFree.Nodes
import ArtinPrimitiveRoots.A2.ZeroFree.Density
import ArtinPrimitiveRoots.A2.Poisson.Missing
import ArtinPrimitiveRoots.A2.Interface
import ArtinPrimitiveRoots.A2.Proofs.A2_ROWS.HeightConvolution
import ArtinPrimitiveRoots.A1.Coeff.IdealSummable
import ArtinPrimitiveRoots.A2.Proofs.QS_ANALYTIC.RNDict

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
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
