import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_exterior_dyad_bound

set_option autoImplicit false
set_option maxHeartbeats 600000
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductorExteriorCutoff_nat_norm_le
    (S : A1.SData F CE condη) (N : ℝ) (q : S.ExtIdeal)
    (hq : q ∈ conductorExteriorCutoff S N) :
    Ideal.absNorm q.1 ≤ ⌊N⌋₊ := by
  classical
  unfold conductorExteriorCutoff at hq
  rcases Finset.mem_map.mp hq with ⟨I, hI, hEq⟩
  have hcut : I.1 ∈ conductorIdealCutoff F N :=
    (Finset.mem_filter.mp I.2).1
  have hnat : Ideal.absNorm I.1 ≤ ⌊N⌋₊ := by
    change I.1 ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).toFinset at hcut
    exact (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).mem_toFinset.mp hcut
  have hval : I.1 = q.1 := congrArg (fun x : S.ExtIdeal => x.1) hEq
  rw [← hval]
  exact hnat

private theorem conductorExtIdeal_norm_pos
    (S : A1.SData F CE condη) (I : S.ExtIdeal) :
    0 < Ideal.absNorm I.1 := by
  have hn : Ideal.absNorm I.1 ≠ 0 := by
    intro hzero
    exact I.2.1 (Ideal.absNorm_eq_zero_iff.mp hzero)
  exact Nat.pos_of_ne_zero hn

/-- Split the finite exterior cutoff into disjoint dyads and apply
Cauchy–Schwarz, paying one logarithm. Guide: sol-thin-a2zf/PROOFS.md:733–737.
Uses conductor_exterior_dyad_bound; feeds conductor_sieve_assemble. -/
theorem conductor_exterior_sieve_bound (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ N U : ℝ, 2 ≤ N → 2 ≤ U →
      ∀ (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
        (𝓧 : Finset (A1.HeckeChar F)), ConductorGroup S C₀ U ℓ τ 𝓧 →
        ∀ b : S.ExtIdeal → ℂ,
          (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorExteriorCutoff S N, b I * ω.idealValue I.1‖ ^ 2) ≤
            C * (N + U ^ 2) * (1 + Real.log N) *
              ∑ I ∈ conductorExteriorCutoff S N, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨Cdyad, hCdyad, hdyad⟩ := conductor_exterior_dyad_bound S C₀ hC₀
  refine ⟨2 * Cdyad, by positivity, ?_⟩
  intro N U hN hU ℓ τ 𝓧 h𝓧 b
  let A := conductorExteriorCutoff S N
  let K : ℕ := Nat.log 2 ⌊N⌋₊
  let J : Finset ℕ := Finset.range (K + 1)
  let Fib (j : ℕ) : Finset S.ExtIdeal :=
    A.filter (fun I => Nat.log 2 (Ideal.absNorm I.1) = j)
  have hNnonneg : 0 ≤ N := by linarith
  have hNlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hfloor2 : 2 ≤ ⌊N⌋₊ :=
    (Nat.le_floor_iff hNnonneg).2 (by exact_mod_cast hN)
  have hKpow : 2 ^ K ≤ ⌊N⌋₊ := by
    dsimp [K]
    exact Nat.pow_log_le_self 2 (by omega)
  have hfloor_le : (⌊N⌋₊ : ℝ) ≤ N := Nat.floor_le hNnonneg
  have hpowReal : (2 : ℝ) ^ K ≤ N := by
    calc
      (2 : ℝ) ^ K = ((2 : ℕ) ^ K : ℕ) := by norm_cast
      _ ≤ ⌊N⌋₊ := by exact_mod_cast hKpow
      _ ≤ N := hfloor_le
  have hlogPow : (K : ℝ) * Real.log 2 ≤ Real.log N := by
    have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ K) hpowReal
    rw [Real.log_pow] at hlog
    simpa [mul_comm] using hlog
  have hKle : (K : ℝ) ≤ 2 * Real.log N := by
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    have hmul := mul_le_mul_of_nonneg_left hlog2 hKnonneg
    nlinarith [hmul, hlogPow]
  have hJcard : (J.card : ℝ) ≤ 2 * (1 + Real.log N) := by
    have hJ : J.card = K + 1 := by simp [J]
    rw [hJ]
    push_cast
    linarith [hKle, hNlog]
  have hmap : (A : Set S.ExtIdeal).MapsTo
      (fun I => Nat.log 2 (Ideal.absNorm I.1)) J := by
    intro I hI
    have hnorm := conductorExteriorCutoff_nat_norm_le S N I (by simpa [A] using hI)
    have hlogle : Nat.log 2 (Ideal.absNorm I.1) ≤ Nat.log 2 ⌊N⌋₊ :=
      Nat.log_mono_right hnorm
    apply Finset.mem_range.mpr
    dsimp [J, K]
    exact Nat.lt_succ_of_le hlogle
  have hpartition (ω : A1.HeckeChar F) :
      (∑ I ∈ A, b I * ω.idealValue I.1) =
        ∑ j ∈ J, ∑ I ∈ Fib j, b I * ω.idealValue I.1 := by
    have h := (Finset.sum_fiberwise_of_maps_to hmap
      (fun I => b I * ω.idealValue I.1)).symm
    simpa [Fib] using h
  have hmassPartition :
      (∑ j ∈ J, ∑ I ∈ Fib j, ‖b I‖ ^ 2) =
        ∑ I ∈ A, ‖b I‖ ^ 2 := by
    simpa [Fib] using
      (Finset.sum_fiberwise_of_maps_to hmap (fun I => ‖b I‖ ^ 2))
  let z (ω : A1.HeckeChar F) (j : ℕ) : ℂ :=
    ∑ I ∈ Fib j, b I * ω.idealValue I.1
  have hCauchy (ω : A1.HeckeChar F) :
      ‖∑ j ∈ J, z ω j‖ ^ 2 ≤ (J.card : ℝ) * ∑ j ∈ J, ‖z ω j‖ ^ 2 := by
    have htriangle := norm_sum_le J (fun j => z ω j)
    have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ))
      (fun j => ‖z ω j‖)
    have hcauchy' : (∑ j ∈ J, ‖z ω j‖) ^ 2 ≤
        (J.card : ℝ) * ∑ j ∈ J, ‖z ω j‖ ^ 2 := by
      simpa using hcauchy
    exact ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      htriangle).trans hcauchy'
  have hCauchySum :
      (∑ ω ∈ 𝓧, ‖∑ I ∈ A, b I * ω.idealValue I.1‖ ^ 2) ≤
        (J.card : ℝ) * ∑ j ∈ J, ∑ ω ∈ 𝓧, ‖z ω j‖ ^ 2 := by
    calc
      _ ≤ ∑ ω ∈ 𝓧, (J.card : ℝ) * ∑ j ∈ J, ‖z ω j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        rw [hpartition ω]
        exact hCauchy ω
      _ = (J.card : ℝ) * ∑ j ∈ J, ∑ ω ∈ 𝓧, ‖z ω j‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
  have hFiberSubset (j : ℕ) : Fib j ⊆ conductorExteriorDyad S ((2 : ℕ) ^ j) := by
    intro I hI
    have hcut : I ∈ A := (Finset.mem_filter.mp hI).1
    have hlog : Nat.log 2 (Ideal.absNorm I.1) = j := (Finset.mem_filter.mp hI).2
    have hnpos := conductorExtIdeal_norm_pos S I
    have hlowNat := Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos)
    rw [hlog] at hlowNat
    have hhighNat := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Ideal.absNorm I.1)
    rw [hlog] at hhighNat
    have hlow : ((2 : ℕ) ^ j : ℝ) ≤ idealNorm I.1 := by
      change ((2 : ℕ) ^ j : ℝ) ≤ (Ideal.absNorm I.1 : ℝ)
      exact_mod_cast hlowNat
    have hhigh : idealNorm I.1 ≤ 2 * ((2 : ℕ) ^ j : ℝ) := by
      change (Ideal.absNorm I.1 : ℝ) ≤ 2 * ((2 : ℕ) ^ j : ℝ)
      calc
        (Ideal.absNorm I.1 : ℝ) ≤ ((2 : ℕ) ^ Nat.succ j : ℝ) := by
          exact_mod_cast hhighNat.le
        _ = 2 * ((2 : ℕ) ^ j : ℝ) := by
          norm_cast
          rw [Nat.pow_succ]
          ring
    simp only [conductorExteriorDyad, Finset.mem_filter]
    exact ⟨conductorExteriorCutoff_mem_of_norm S (2 * ((2 : ℕ) ^ j : ℝ))
      (by positivity) I hhigh, hlow⟩
  have hTj (j : ℕ) : 1 ≤ ((2 : ℕ) ^ j : ℝ) := by
    exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)) : 1 ≤ (2 : ℕ) ^ j)
  have hTleN (j : ℕ) (hj : j ∈ J) : ((2 : ℕ) ^ j : ℝ) ≤ N := by
    have hjK : j ≤ K := by
      have hj' : j < K + 1 := by simpa [J] using Finset.mem_range.mp hj
      omega
    have hpow : (2 : ℕ) ^ j ≤ ⌊N⌋₊ := by
      exact (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hjK).trans hKpow
    calc
      ((2 : ℕ) ^ j : ℝ) ≤ ⌊N⌋₊ := by exact_mod_cast hpow
      _ ≤ N := hfloor_le
  let bFiber (j : ℕ) (I : S.ExtIdeal) : ℂ := if I ∈ Fib j then b I else 0
  have hfilter (j : ℕ) :
      (conductorExteriorDyad S ((2 : ℕ) ^ j)).filter (fun I => I ∈ Fib j) = Fib j := by
    apply Finset.Subset.antisymm
    · intro I hI
      exact (Finset.mem_filter.mp hI).2
    · intro I hI
      exact Finset.mem_filter.mpr ⟨hFiberSubset j hI, hI⟩
  have hsumFiberRep (j : ℕ) (ω : A1.HeckeChar F) :
      (∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j),
        bFiber j I * ω.idealValue I.1) = z ω j := by
    calc
      _ = ∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j),
            if I ∈ Fib j then b I * ω.idealValue I.1 else 0 := by
          apply Finset.sum_congr rfl
          intro I hI
          simp [bFiber]
      _ = ∑ I ∈ (conductorExteriorDyad S ((2 : ℕ) ^ j)).filter (fun I => I ∈ Fib j),
            b I * ω.idealValue I.1 := by
          rw [← Finset.sum_filter]
      _ = z ω j := by rw [hfilter j]
  have hmassFiberRep (j : ℕ) :
      (∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j), ‖bFiber j I‖ ^ 2) =
        ∑ I ∈ Fib j, ‖b I‖ ^ 2 := by
    calc
      _ = ∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j),
            if I ∈ Fib j then ‖b I‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro I hI
          by_cases hIF : I ∈ Fib j <;> simp [bFiber, hIF]
      _ = ∑ I ∈ (conductorExteriorDyad S ((2 : ℕ) ^ j)).filter (fun I => I ∈ Fib j),
            ‖b I‖ ^ 2 := by rw [← Finset.sum_filter]
      _ = _ := by rw [hfilter j]
  have hFiberBound (j : ℕ) (hj : j ∈ J) :
      (∑ ω ∈ 𝓧, ‖z ω j‖ ^ 2) ≤
        Cdyad * (N + U ^ 2) * ∑ I ∈ Fib j, ‖b I‖ ^ 2 := by
    have h := hdyad ((2 : ℕ) ^ j) U (hTj j) hU ℓ τ 𝓧 h𝓧 (bFiber j)
    have hcoef : ((2 : ℕ) ^ j : ℝ) + U ^ 2 ≤ N + U ^ 2 := by
      linarith [hTleN j hj]
    calc
      _ = ∑ ω ∈ 𝓧,
            ‖∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j),
              bFiber j I * ω.idealValue I.1‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [hsumFiberRep j ω]
      _ ≤ Cdyad * (((2 : ℕ) ^ j : ℝ) + U ^ 2) *
            ∑ I ∈ conductorExteriorDyad S ((2 : ℕ) ^ j), ‖bFiber j I‖ ^ 2 := h
      _ ≤ Cdyad * (N + U ^ 2) * ∑ I ∈ Fib j, ‖b I‖ ^ 2 := by
            rw [hmassFiberRep j]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef hCdyad.le) (by positivity)
  have hFiberTotal :
      (∑ j ∈ J, ∑ ω ∈ 𝓧, ‖z ω j‖ ^ 2) ≤
        Cdyad * (N + U ^ 2) * ∑ I ∈ A, ‖b I‖ ^ 2 := by
    calc
      _ ≤ ∑ j ∈ J, Cdyad * (N + U ^ 2) * ∑ I ∈ Fib j, ‖b I‖ ^ 2 :=
        Finset.sum_le_sum (fun j hj => hFiberBound j hj)
      _ = Cdyad * (N + U ^ 2) * ∑ j ∈ J, ∑ I ∈ Fib j, ‖b I‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ = Cdyad * (N + U ^ 2) * ∑ I ∈ A, ‖b I‖ ^ 2 := by rw [hmassPartition]
  calc
    (∑ ω ∈ 𝓧, ‖∑ I ∈ A, b I * ω.idealValue I.1‖ ^ 2) ≤
        (J.card : ℝ) * ∑ j ∈ J, ∑ ω ∈ 𝓧, ‖z ω j‖ ^ 2 := hCauchySum
    _ ≤ (J.card : ℝ) *
          (Cdyad * (N + U ^ 2) * ∑ I ∈ A, ‖b I‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hFiberTotal (Nat.cast_nonneg _)
    _ ≤ (2 * (1 + Real.log N)) *
          (Cdyad * (N + U ^ 2) * ∑ I ∈ A, ‖b I‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right hJcard
        positivity
    _ = (2 * Cdyad) * (N + U ^ 2) * (1 + Real.log N) *
          ∑ I ∈ A, ‖b I‖ ^ 2 := by ring

end ArtinPrimitiveRoots.A2
