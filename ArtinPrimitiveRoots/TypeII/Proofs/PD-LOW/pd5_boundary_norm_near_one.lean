import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».pd5_scale_facts

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

private theorem pd5_boundary_exponential_tail (K : ℕ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      16 * (K : ℝ) * (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ 6 *
        Real.exp (-(Real.rpow (Real.log x) (1 / 10 : ℝ))) ≤ Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let u : ℝ → ℝ := fun x => Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hu : Tendsto u atTop atTop := by
    dsimp [u]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hratio : Tendsto (fun x : ℝ => Real.exp (u x) / (u x) ^ 6) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 6).comp hu
  let C : ℝ := (16 * (K : ℝ) + 1) / Real.log 2
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have huEventually : ∀ᶠ x : ℝ in atTop, 1 ≤ u x :=
    (Filter.tendsto_atTop.1 hu) 1
  have hratioEventually : ∀ᶠ x : ℝ in atTop, C ≤ Real.exp (u x) / (u x) ^ 6 :=
    (Filter.tendsto_atTop.1 hratio) C
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 (huEventually.and hratioEventually)
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  have hx₁' : x₁ ≤ x := le_trans (le_max_right _ _) hx
  have hu1 : 1 ≤ u x := (hx₁ x hx₁').1
  have hratio' : C ≤ Real.exp (u x) / (u x) ^ 6 := (hx₁ x hx₁').2
  have huPos : 0 < u x := lt_of_lt_of_le (by norm_num) hu1
  have hpowPos : 0 < (u x) ^ 6 := pow_pos huPos _
  have hratioMul : C * (u x) ^ 6 ≤ Real.exp (u x) :=
    (le_div_iff₀ hpowPos).mp hratio'
  have hcoef : 16 * (K : ℝ) ≤ C * Real.log 2 := by
    dsimp [C]
    rw [div_mul_cancel₀ _ (ne_of_gt hlog2)]
    nlinarith
  have huPowNonneg : 0 ≤ (u x) ^ 6 := le_of_lt hpowPos
  have hscaled : (16 * (K : ℝ)) * (u x) ^ 6 ≤
      Real.log 2 * Real.exp (u x) := by
    calc
      (16 * (K : ℝ)) * (u x) ^ 6 ≤
          (C * Real.log 2) * (u x) ^ 6 :=
            mul_le_mul_of_nonneg_right hcoef huPowNonneg
      _ = (C * (u x) ^ 6) * Real.log 2 := by ring
      _ ≤ Real.exp (u x) * Real.log 2 :=
            mul_le_mul_of_nonneg_right hratioMul hlog2.le
      _ = Real.log 2 * Real.exp (u x) := by ring
  have hdiv := (div_le_iff₀ (Real.exp_pos (u x))).2 hscaled
  simpa [u, Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

private theorem pd5_primeBand_mem {x a : ℝ} {p : ℕ} (hp : p ∈ primeBand x a) :
    p.Prime ∧ Real.exp (Real.rpow (Real.log x) a) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * Real.rpow (Real.log x) a) := by
  unfold primeBand at hp
  exact (Finset.mem_filter.mp hp).2

private theorem pd5_boundary_full_active_sum {K : ℕ} (F : PDFix K) (S : PDScale) :
    ∑ p ∈ Fintype.piFinset (fun i : Fin K =>
      Fintype.piFinset (fun _ : Fin (slotCount S.x) => primeBand S.x (F.a i))),
      ∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i (p i j) =
      ∏ i : Fin K,
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ^ slotCount S.x := by
  classical
  let Q : ∀ i : Fin K, Finset (Fin (slotCount S.x) → ℕ) := fun i =>
    Fintype.piFinset (fun _ : Fin (slotCount S.x) => primeBand S.x (F.a i))
  have hgroup (i : Fin K) :
      ∑ q ∈ Q i, ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (q j) =
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ^ slotCount S.x := by
    dsimp [Q]
    rw [Finset.sum_prod_piFinset]
    simp
  calc
    _ = ∏ i : Fin K,
          ∑ q ∈ Q i, ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (q j) := by
      rw [← Finset.prod_univ_sum (t := Q)
        (f := fun i q => ∏ j : Fin (slotCount S.x),
          memoryNu S.x K F.a F.q_d i (q j))]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hgroup i

/-- Uniform boundary squared norm at most two and nonnegative measure.
Guide `runs/lanes/sol-thin-pd5/PROOFS.md:502–536`; uses pd5_scale_facts and b-prime bounds;
feeds low-rank norm iteration, with no dependence on G. -/
theorem pd5_boundary_norm_near_one (δ c₁ c₂ : ℝ) (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    PD5BoundaryAvailable δ c₁ c₂ F := by
  classical
  obtain ⟨xScale, hxScale, hScale⟩ := pd5_scale_facts K F hF
  obtain ⟨xTail, hxTail, hTail⟩ := pd5_boundary_exponential_tail K
  obtain ⟨xEps, hxEps, hEps⟩ := pd5_pathLength_exponential_small
  refine ⟨max xScale (max xTail xEps), ?_, ?_⟩
  · exact le_trans hxScale (le_max_left _ _)
  · intro S hS hx₀
    let L : ℝ := S.L
    let u : ℝ := Real.rpow L (1 / 10 : ℝ)
    let ε : ℝ := ((S.N + 1 : ℕ) : ℝ) * Real.exp (-u)
    obtain ⟨hLone, hNlow, hNroot, hNupper, hM, hB, hMN, hMass⟩ :=
      hScale S (le_trans (le_max_left _ _) hx₀)
    have hxTailS : max xTail xEps ≤ S.x :=
      le_trans (le_max_right xScale _) hx₀
    have hxTailS' : xTail ≤ S.x := le_trans (le_max_left _ _) hxTailS
    have hxEpsS : xEps ≤ S.x := le_trans (le_max_right _ _) hxTailS
    have huBound : 16 * (K : ℝ) * u ^ 6 * Real.exp (-u) ≤ Real.log 2 := by
      have ht := hTail S.x hxTailS'
      simpa [L, u, PDScale.L] using ht
    have hεHalf : ε ≤ 1 / 2 := by
      have ht := hEps S.x hxEpsS
      have huEq : u = Real.rpow (Real.log S.x) (1 / 10 : ℝ) := by rfl
      have hpath : ((S.N + 1 : ℕ) : ℝ) ≤ Real.exp u / 2 := by
        simpa [u, L, PDScale.N, PDScale.L] using ht
      have hExpPos : 0 < Real.exp u := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hpath (Real.exp_pos (-u)).le
      have hexp : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add]
        simp
      dsimp [ε]
      calc
        ((S.N + 1 : ℕ) : ℝ) * Real.exp (-u) ≤
            (Real.exp u / 2) * Real.exp (-u) := hmul
        _ = 1 / 2 := by rw [div_mul_eq_mul_div, hexp]
    have hεNonneg : 0 ≤ ε := by positivity
    have hrecPos : 0 < (1 - ε)⁻¹ := inv_pos.mpr (by linarith)
    have hrecExp : (1 - ε)⁻¹ ≤ Real.exp (2 * ε) := by
      have hlog := Real.log_le_sub_one_of_pos hrecPos
      have hfrac : (1 - ε)⁻¹ - 1 ≤ 2 * ε := by
        have hden : 0 < 1 - ε := by linarith
        have hfrac' : ε / (1 - ε) ≤ 2 * ε := by
          apply (div_le_iff₀ hden).2
          nlinarith
        have hid : (1 - ε)⁻¹ - 1 = ε / (1 - ε) := by
          field_simp
          ring
        rw [hid]
        exact hfrac'
      calc
        (1 - ε)⁻¹ = Real.exp (Real.log ((1 - ε)⁻¹)) :=
          (Real.exp_log hrecPos).symm
        _ ≤ Real.exp (2 * ε) := Real.exp_le_exp.mpr (le_trans hlog hfrac)
    have hmassPos : ∀ i : Fin K, 0 < bandMass S.x (F.a i) := by
      intro i
      exact lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.log 2 / 2) (hMass i).1
    have hnuNonneg : ∀ i : Fin K, ∀ p ∈ primeBand S.x (F.a i),
        0 ≤ memoryNu S.x K F.a F.q_d i p := by
      intro i p hp
      exact (hMass i).2.2.2 p hp |>.1
    have hprimeBase : ∀ i : Fin K, ∀ p ∈ primeBand S.x (F.a i),
        1 - ε ≤ memoryBPrime S.x F.q_d p := by
      intro i p hp
      have hpLower : Real.exp (Real.rpow L (1 / 10 : ℝ)) ≤ (p : ℝ) := by
        have hband := pd5_primeBand_mem hp
        have ha : (1 / 10 : ℝ) ≤ F.a i := (hF.1.2.1 i).1.le
        have hpow : Real.rpow L (1 / 10 : ℝ) ≤ Real.rpow L (F.a i) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [hLone]) ha
        exact (Real.exp_le_exp.mpr (by simpa [L, PDScale.L] using hpow)).trans hband.2.1
      have hpathOver : ((S.N + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) ≤ ε := by
        have hden : 0 < (p : ℝ) + 1 := by positivity
        have hfactor : 1 ≤ Real.exp (-u) * ((p : ℝ) + 1) := by
          have hdiv : 1 ≤ ((p : ℝ) + 1) / Real.exp u :=
            (le_div_iff₀ (Real.exp_pos u)).2 (by linarith [hpLower])
          simpa [Real.exp_neg, div_eq_mul_inv, mul_comm] using hdiv
        rw [div_le_iff₀ hden]
        dsimp [ε]
        calc
          ((S.N + 1 : ℕ) : ℝ) = ((S.N + 1 : ℕ) : ℝ) * 1 := by ring
          _ ≤ ((S.N + 1 : ℕ) : ℝ) * (Real.exp (-u) * ((p : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hfactor (by positivity)
          _ = (((S.N + 1 : ℕ) : ℝ) * Real.exp (-u)) * ((p : ℝ) + 1) := by ring
      have hb := pd5_memoryBPrime_lower (x := S.x) hF.2.1 hF.2.2.1 p
      have hpathOver' :
          ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) ≤ ε := by
        simpa [ε, u, L, PDScale.N, PDScale.L] using hpathOver
      calc
        1 - ε ≤ 1 - ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
          linarith
        _ ≤ memoryBPrime S.x F.q_d p := hb
    have hnuUpper : ∀ i : Fin K, ∀ p ∈ primeBand S.x (F.a i),
        memoryNu S.x K F.a F.q_d i p ≤
          (1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹ * (p : ℝ)⁻¹ := by
      intro i p hp
      have hV := hmassPos i
      have hpPrime : p.Prime := (pd5_primeBand_mem hp).1
      have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
      have hb := hprimeBase i p hp
      have hbPos : 0 < memoryBPrime S.x F.q_d p := by linarith
      have hden₁ : 0 < bandMass S.x (F.a i) * ((p : ℝ) + 1) *
          memoryBPrime S.x F.q_d p := mul_pos (mul_pos hV (by positivity)) hbPos
      have hden₂ : 0 < (1 - ε) * bandMass S.x (F.a i) * (p : ℝ) :=
        mul_pos (mul_pos (by linarith : 0 < 1 - ε) hV) hpPos
      have hdenOrder : (1 - ε) * bandMass S.x (F.a i) * (p : ℝ) ≤
          bandMass S.x (F.a i) * ((p : ℝ) + 1) * memoryBPrime S.x F.q_d p := by
        have hpOne : (p : ℝ) ≤ (p : ℝ) + 1 := by linarith
        have hfirst' := mul_le_mul_of_nonneg_right hpOne
          (show 0 ≤ 1 - ε by linarith)
        have hfirst : (1 - ε) * (p : ℝ) ≤ ((p : ℝ) + 1) * (1 - ε) := by
          simpa [mul_comm] using hfirst'
        have hsecond : ((p : ℝ) + 1) * (1 - ε) ≤
            ((p : ℝ) + 1) * memoryBPrime S.x F.q_d p :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        calc
          (1 - ε) * bandMass S.x (F.a i) * (p : ℝ) =
              bandMass S.x (F.a i) * ((1 - ε) * (p : ℝ)) := by ring
          _ ≤ bandMass S.x (F.a i) * (((p : ℝ) + 1) * (1 - ε)) :=
            mul_le_mul_of_nonneg_left hfirst hV.le
          _ ≤ bandMass S.x (F.a i) * (((p : ℝ) + 1) *
                memoryBPrime S.x F.q_d p) := mul_le_mul_of_nonneg_left hsecond hV.le
          _ = _ := by ring
      rw [memoryNu]
      have hinv := one_div_le_one_div_of_le hden₂ hdenOrder
      have hform : 1 / ((1 - ε) * bandMass S.x (F.a i) * (p : ℝ)) =
          (1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹ * (p : ℝ)⁻¹ := by
        field_simp
      rw [← hform]
      exact hinv
    have hsumNu : ∀ i : Fin K,
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ (1 - ε)⁻¹ := by
      intro i
      have hpoint := Finset.sum_le_sum fun p hp => hnuUpper i p hp
      have hfactor :
          (∑ p ∈ primeBand S.x (F.a i),
            (1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹ * (p : ℝ)⁻¹) = (1 - ε)⁻¹ := by
        have hrecipSum :
            (∑ p ∈ primeBand S.x (F.a i), (p : ℝ)⁻¹) = bandMass S.x (F.a i) := by
          simp [bandMass, one_div]
        calc
          _ = ∑ p ∈ primeBand S.x (F.a i),
                ((1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹) * (p : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro p hp
              ring
          _ = ((1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹) *
                ∑ p ∈ primeBand S.x (F.a i), (p : ℝ)⁻¹ := by
              rw [Finset.mul_sum]
          _ = ((1 - ε)⁻¹ * (bandMass S.x (F.a i))⁻¹) *
                bandMass S.x (F.a i) := by rw [hrecipSum]
          _ = (1 - ε)⁻¹ *
                ((bandMass S.x (F.a i))⁻¹ * bandMass S.x (F.a i)) := by ring
          _ = (1 - ε)⁻¹ := by
              rw [inv_mul_cancel₀ (ne_of_gt (hmassPos i))]
              ring
      exact hpoint.trans_eq hfactor
    have hfactorBound (i : Fin K) :
        (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ^ slotCount S.x ≤
          Real.exp (2 * ε * (slotCount S.x : ℝ)) := by
      have hsNonneg : 0 ≤ ∑ p ∈ primeBand S.x (F.a i),
          memoryNu S.x K F.a F.q_d i p := by
        apply Finset.sum_nonneg
        intro p hp
        exact hnuNonneg i p hp
      calc
        _ ≤ ((1 - ε)⁻¹) ^ slotCount S.x :=
          pow_le_pow_left₀ hsNonneg (hsumNu i) _
        _ ≤ Real.exp (2 * ε) ^ slotCount S.x :=
          pow_le_pow_left₀ (by positivity) hrecExp _
        _ = Real.exp (2 * ε * (slotCount S.x : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    have hsumNonneg (i : Fin K) : 0 ≤
        ∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p := by
      apply Finset.sum_nonneg
      intro p hp
      exact hnuNonneg i p hp
    have hfullNonneg : ∀ p ∈ Fintype.piFinset (fun i : Fin K =>
        Fintype.piFinset (fun _ : Fin (slotCount S.x) => primeBand S.x (F.a i))),
        0 ≤ ∏ i : Fin K, ∏ j : Fin (slotCount S.x),
          memoryNu S.x K F.a F.q_d i (p i j) := by
      intro p hp
      apply Finset.prod_nonneg
      intro i hi
      apply Finset.prod_nonneg
      intro j hj
      have hmem := Fintype.mem_piFinset.mp hp i
      have hmem' := Fintype.mem_piFinset.mp hmem j
      exact hnuNonneg i (p i j) hmem'
    let Full : Finset (PrimeLists S.x K) := Fintype.piFinset (fun i : Fin K =>
      Fintype.piFinset (fun _ : Fin (slotCount S.x) => primeBand S.x (F.a i)))
    let Awt : PrimeLists S.x K → ℝ := fun p =>
      ∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i (p i j)
    have hfullEq : (∑ p ∈ Full, Awt p) =
        ∏ i : Fin K,
          (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ^ slotCount S.x := by
      simpa [Full, Awt] using pd5_boundary_full_active_sum F S
    have hfullBound : (∑ p ∈ Full, Awt p) ≤
        Real.exp (2 * ε * (slotCount S.x : ℝ) * (K : ℝ)) := by
      rw [hfullEq]
      calc
        _ ≤ ∏ i : Fin K, Real.exp (2 * ε * (slotCount S.x : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact pow_nonneg (hsumNonneg i) _
          · intro i hi
            exact hfactorBound i
        _ = Real.exp (2 * ε * (slotCount S.x : ℝ) * (K : ℝ)) := by
          rw [← Real.exp_sum]
          simp
          push_cast
          ring
    have hMle : (slotCount S.x : ℝ) ≤ 2 * u := by
      have hpow : Real.rpow L (1 / 100 : ℝ) ≤ u :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hLone])
          (by norm_num : (1 / 100 : ℝ) ≤ 1 / 10)
      exact hM.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
    have hu5 : u ^ 5 = Real.rpow L (1 / 2 : ℝ) := by
      dsimp [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hLone] : 0 ≤ L)]
      norm_num
    have hNplus : ((S.N + 1 : ℕ) : ℝ) ≤ 4 * u ^ 5 := by
      have hu1 : 1 ≤ u := by
        dsimp [u]
        exact Real.one_le_rpow (by linarith [hLone]) (by norm_num)
      have hNu5 : 1 ≤ u ^ 5 := one_le_pow₀ hu1
      have hN : (S.N : ℝ) < u ^ 5 + 2 := by
        calc
          (S.N : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := by simpa [L] using hNupper
          _ = u ^ 5 + 2 := by rw [hu5]
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hExponent : 2 * ε * (slotCount S.x : ℝ) * (K : ℝ) ≤ Real.log 2 := by
      have hKnonneg : 0 ≤ (K : ℝ) := by positivity
      have huNonneg : 0 ≤ u := by
        dsimp [u]
        exact Real.rpow_nonneg (by linarith [hLone]) _
      have hcoef : 2 * ε * (slotCount S.x : ℝ) * (K : ℝ) ≤
          16 * (K : ℝ) * u ^ 6 * Real.exp (-u) := by
        dsimp [ε]
        have hNcast : 0 ≤ ((S.N + 1 : ℕ) : ℝ) := by positivity
        have h2N : 2 * ((S.N + 1 : ℕ) : ℝ) ≤ 8 * u ^ 5 := by
          nlinarith [hNplus]
        have hexpNonneg : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
        calc
          2 * (((S.N + 1 : ℕ) : ℝ) * Real.exp (-u)) *
                (slotCount S.x : ℝ) * (K : ℝ) =
              (2 * ((S.N + 1 : ℕ) : ℝ)) * (slotCount S.x : ℝ) *
                ((K : ℝ) * Real.exp (-u)) := by ring
          _ ≤ (8 * u ^ 5) * (slotCount S.x : ℝ) *
                ((K : ℝ) * Real.exp (-u)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h2N (by positivity))
                (mul_nonneg (by positivity) hexpNonneg)
          _ ≤ (8 * u ^ 5) * (2 * u) * ((K : ℝ) * Real.exp (-u)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hMle (by positivity))
                (mul_nonneg hKnonneg hexpNonneg)
          _ = 16 * (K : ℝ) * u ^ 6 * Real.exp (-u) := by ring
      exact hcoef.trans huBound
    have hboundaryMeasure : ∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s := by
      intro s
      by_cases hs : MemValid F S s
      · unfold memMeasure
        rw [if_pos hs]
        apply mul_nonneg
        · apply Finset.prod_nonneg
          intro i hi
          apply Finset.prod_nonneg
          intro j hj
          exact hnuNonneg i (s.2.1 i j) (hs.2.1 i j)
        · apply Finset.prod_nonneg
          intro i hi
          apply div_nonneg
          · apply List.prod_nonneg
            intro e he
            rcases List.mem_map.mp he with ⟨e', he', rfl⟩
            exact (hnuNonneg i e'.1 (hs.2.2 i e' he').1)
          · positivity
      · simp [memMeasure, hs]
    refine ⟨hboundaryMeasure, ?_⟩
    intro T
    let IsBoundaryValid : MemPoint S.x K → Prop := fun s =>
      (s.1 = (1, 0) ∧ ∀ i, s.2.2 i = []) ∧ MemValid F S s
    let V : Finset (MemPoint S.x K) := T.filter IsBoundaryValid
    have hterms (s : MemPoint S.x K) :
        memMeasure F S s * ‖memBoundary s‖ ^ 2 =
          if IsBoundaryValid s then Awt s.2.1 else 0 := by
      by_cases hb : IsBoundaryValid s
      · have hvalid := hb.2
        have hempty := hb.1.2
        have hmu : memMeasure F S s = Awt s.2.1 := by
          simp [memMeasure, hvalid, hempty, Awt]
        rw [if_pos hb]
        simp [memBoundary, hb.1, hmu]
      · by_cases hB : s.1 = (1, 0) ∧ ∀ i, s.2.2 i = []
        · have hnotvalid : ¬ MemValid F S s := by
            intro hv
            exact hb ⟨hB, hv⟩
          simp [memBoundary, hB, memMeasure, hnotvalid, hb]
        · simp [memBoundary, hB, hb]
    have hinj : ∀ s ∈ V, ∀ t ∈ V, s.2.1 = t.2.1 → s = t := by
      intro s hs t ht hLists
      have hsb := (Finset.mem_filter.mp hs).2.1
      have htb := (Finset.mem_filter.mp ht).2.1
      rcases s with ⟨zs, ps, ms⟩
      rcases t with ⟨zt, pt, mt⟩
      dsimp at hLists
      subst pt
      have hz : zs = zt := hsb.1.trans htb.1.symm
      have hm : ms = mt := by
        funext i
        exact (hsb.2 i).trans (htb.2 i).symm
      subst zt
      subst mt
      rfl
    let P : Finset (PrimeLists S.x K) := V.image fun s => s.2.1
    have hPsub : P ⊆ Full := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨s, hs, rfl⟩
      have hvalid := (Finset.mem_filter.mp hs).2.2
      change s.2.1 ∈ Fintype.piFinset (fun i : Fin K =>
        Fintype.piFinset (fun _ : Fin (slotCount S.x) => primeBand S.x (F.a i)))
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Fintype.mem_piFinset.mpr
      intro j
      exact hvalid.2.1 i j
    have hAwtNonneg : ∀ p ∈ Full, 0 ≤ Awt p := by
      intro p hp
      apply Finset.prod_nonneg
      intro i hi
      apply Finset.prod_nonneg
      intro j hj
      have hpi := Fintype.mem_piFinset.mp hp i
      have hpij := Fintype.mem_piFinset.mp hpi j
      exact hnuNonneg i (p i j) hpij
    calc
      memNormSqOn F S T memBoundary = ∑ s ∈ T, if IsBoundaryValid s then Awt s.2.1 else 0 := by
        unfold memNormSqOn
        apply Finset.sum_congr rfl
        intro s hs
        exact hterms s
      _ = ∑ s ∈ V, Awt s.2.1 := by
        rw [Finset.sum_filter]
      _ = ∑ p ∈ P, Awt p := by
        rw [Finset.sum_image hinj]
      _ ≤ ∑ p ∈ Full, Awt p :=
        Finset.sum_le_sum_of_subset_of_nonneg hPsub (fun p hp _ => hAwtNonneg p hp)
      _ ≤ Real.exp (2 * ε * (slotCount S.x : ℝ) * (K : ℝ)) := hfullBound
      _ ≤ 2 := by
        calc
          Real.exp (2 * ε * (slotCount S.x : ℝ) * (K : ℝ)) ≤
              Real.exp (Real.log 2) := Real.exp_le_exp.mpr hExponent
          _ = 2 := Real.exp_log (by norm_num)

end
end ArtinPrimitiveRoots.TypeII.PD
