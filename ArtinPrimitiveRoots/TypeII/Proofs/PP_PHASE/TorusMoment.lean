import ArtinPrimitiveRoots.TypeII.PP.Defs

namespace ArtinPrimitiveRoots.Proofs.pp_phase_p

open MeasureTheory
open Complex
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP
open scoped ComplexConjugate

theorem torus_char_interval_integral (m : ℤ) :
    ∫ x : ℝ in (0 : ℝ)..1,
      Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ) * x)) =
        if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hc : (Complex.I * (2 * Real.pi * (m : ℝ)) : ℂ) ≠ 0 := by
      apply mul_ne_zero Complex.I_ne_zero
      exact_mod_cast (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
        Real.pi_ne_zero) (Int.cast_ne_zero.mpr hm))
    have hI :
        (∫ x in (0 : ℝ)..1,
          Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ) * x))) =
        ∫ x in (0 : ℝ)..1,
          Complex.exp ((Complex.I * (2 * Real.pi * (m : ℝ))) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      congr 2
      noncomm_ring
    rw [hI, integral_exp_mul_complex hc]
    have hperiod : Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ))) = 1 := by
      rw [show Complex.I * (2 * Real.pi * (m : ℝ)) = (m : ℤ) * (2 * Real.pi * Complex.I) by
        push_cast
        ring]
      simp [Complex.exp_int_mul, Complex.exp_mul_I]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero,
      Complex.exp_zero, if_neg hm]
    rw [hperiod]
    simp [hm]

theorem torus_char_Icc_integral (m : ℤ) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ) * x)) =
        if m = 0 then 1 else 0 := by
  calc
    _ = ∫ x in Set.Ioc (0 : ℝ) 1,
        Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ) * x)) :=
      integral_Icc_eq_integral_Ioc
    _ = ∫ x in (0 : ℝ)..1,
        Complex.exp (Complex.I * (2 * Real.pi * (m : ℝ) * x)) :=
      (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
    _ = _ := torus_char_interval_integral m

theorem torus_integral_linear_character {k : ℕ} (r : Fin k → ℤ) :
    ∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
      additiveCharacter (∑ j : Fin k, a j * (r j : ℝ)) ∂(volume : Measure (Fin k → ℝ)) =
        ∏ j : Fin k, if r j = 0 then (1 : ℂ) else 0 := by
  classical
  let cube : Set (Fin k → ℝ) := Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1)
  have hcube : MeasurableSet cube := by
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hfactor (a : Fin k → ℝ) :
      additiveCharacter (∑ j : Fin k, a j * (r j : ℝ)) =
        ∏ j : Fin k, Complex.exp
          (Complex.I * (2 * Real.pi * (r j : ℝ) * a j)) := by
    calc
      _ = Complex.exp (∑ j : Fin k,
          Complex.I * (2 * Real.pi * (a j * (r j : ℝ)))) := by
        simp only [additiveCharacter]
        congr 1
        push_cast
        calc
          Complex.I * (2 * Real.pi * ∑ j : Fin k, ↑(a j) * ↑(r j)) =
              (Complex.I * (2 * Real.pi)) * ∑ j : Fin k, ↑(a j) * ↑(r j) := by ring
          _ = ∑ j : Fin k, (Complex.I * (2 * Real.pi)) *
                (↑(a j) * ↑(r j)) := Finset.mul_sum _ _ _
          _ = ∑ j : Fin k, Complex.I * (2 * Real.pi *
                (↑(a j) * ↑(r j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∏ j : Fin k, Complex.exp
          (Complex.I * (2 * Real.pi * (r j : ℝ) * a j)) := by
        rw [Complex.exp_sum]
        apply Finset.prod_congr rfl
        intro j hj
        congr 1
        ring
  calc
    _ = ∫ a in cube, ∏ j : Fin k, Complex.exp
        (Complex.I * (2 * Real.pi * (r j : ℝ) * a j)) ∂(volume : Measure (Fin k → ℝ)) := by
      apply setIntegral_congr_fun hcube
      intro a ha
      exact hfactor a
    _ = ∫ a, ∏ j : Fin k, Complex.exp
        (Complex.I * (2 * Real.pi * (r j : ℝ) * a j))
          ∂Measure.pi (fun _ : Fin k => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      simp only [cube]
      rw [volume_pi, Measure.restrict_pi_pi]
    _ = ∏ j : Fin k, ∫ x,
        Complex.exp (Complex.I * (2 * Real.pi * (r j : ℝ) * x))
          ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      by
        simpa only using
          (MeasureTheory.integral_fintype_prod_eq_prod
            (E := fun _ : Fin k => ℝ)
            (μ := fun _ : Fin k =>
              (volume.restrict (Set.Icc (0 : ℝ) 1) : Measure ℝ))
            (f := fun j x => Complex.exp
              (Complex.I * (2 * Real.pi * (r j : ℝ) * x))))
    _ = ∏ j : Fin k, if r j = 0 then (1 : ℂ) else 0 := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa using torus_char_Icc_integral (r j)

theorem torus_integral_linear_character_eq {k : ℕ} (r : Fin k → ℤ) :
    ∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
      additiveCharacter (∑ j : Fin k, a j * (r j : ℝ)) ∂(volume : Measure (Fin k → ℝ)) =
        if ∀ j, r j = 0 then 1 else 0 := by
  rw [torus_integral_linear_character]
  by_cases h : ∀ j, r j = 0
  · simp [h]
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    have hp : (∏ j : Fin k, if r j = 0 then (1 : ℂ) else 0) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])]
    have hn : ¬ ∀ j, r j = 0 := by
      intro hz
      exact hj (hz j)
    simp [hn, hp]

noncomputable def phaseWeightedWeylSum {k M : ℕ} (c : ℕ → ℂ)
    (a : Fin k → ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 M,
    c h * additiveCharacter (∑ j : Fin k, a j * (h : ℝ) ^ (j.val + 1))

def phaseTupleFinset (s M : ℕ) : Finset (Fin s → ℕ) :=
  Fintype.piFinset fun _ : Fin s => Finset.Icc 1 M

def phaseTupleWeight {s : ℕ} (c : ℕ → ℂ) (t : Fin s → ℕ) : ℂ :=
  ∏ i : Fin s, c (t i)

noncomputable def phaseTupleCharacter {s k : ℕ} (a : Fin k → ℝ)
    (t : Fin s → ℕ) : ℂ :=
  ∏ i : Fin s,
    additiveCharacter (∑ j : Fin k, a j * (t i : ℝ) ^ (j.val + 1))

def phasePowerSum {s k : ℕ} (t : Fin s → ℕ) (j : Fin k) : ℕ :=
  ∑ i : Fin s, t i ^ (j.val + 1)

theorem additiveCharacter_sum {ι : Type*} (A : Finset ι) (f : ι → ℝ) :
    additiveCharacter (∑ i ∈ A, f i) = ∏ i ∈ A, additiveCharacter (f i) := by
  simp only [additiveCharacter]
  have hArg : Complex.I * (2 * Real.pi * ∑ i ∈ A, f i) =
      ∑ i ∈ A, Complex.I * (2 * Real.pi * f i) := by
    push_cast
    calc
      Complex.I * (2 * Real.pi * ∑ i ∈ A, (f i : ℂ)) =
          (Complex.I * (2 * Real.pi)) * ∑ i ∈ A, (f i : ℂ) := by ring
      _ = ∑ i ∈ A, (Complex.I * (2 * Real.pi)) * (f i : ℂ) :=
        Finset.mul_sum _ _ _
      _ = ∑ i ∈ A, Complex.I * (2 * Real.pi * (f i : ℂ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hArg, Complex.exp_sum]

theorem phaseTupleCharacter_eq {s k : ℕ} (a : Fin k → ℝ)
    (t : Fin s → ℕ) :
    phaseTupleCharacter a t =
      additiveCharacter (∑ j : Fin k, a j * ∑ i : Fin s, (t i : ℝ) ^ (j.val + 1)) := by
  unfold phaseTupleCharacter
  rw [← additiveCharacter_sum Finset.univ
    (fun i : Fin s => ∑ j : Fin k, a j * (t i : ℝ) ^ (j.val + 1))]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]

theorem additiveCharacter_add (x y : ℝ) :
    additiveCharacter (x + y) = additiveCharacter x * additiveCharacter y := by
  unfold additiveCharacter
  simp only [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem additiveCharacter_conj (x : ℝ) :
    conj (additiveCharacter x) = additiveCharacter (-x) := by
  unfold additiveCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, conj_I, conj_ofReal, ofReal_neg, map_ofNat]
  ring

theorem phaseTupleCharacter_eq_powerSum {s k : ℕ} (a : Fin k → ℝ)
    (t : Fin s → ℕ) :
    phaseTupleCharacter a t =
      additiveCharacter (∑ j : Fin k, a j * (phasePowerSum t j : ℝ)) := by
  rw [phaseTupleCharacter_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [phasePowerSum, Nat.cast_sum]

theorem phaseTuplePairCharacter_eq {s k : ℕ} (a : Fin k → ℝ)
    (u v : Fin s → ℕ) :
    phaseTupleCharacter a u * conj (phaseTupleCharacter a v) =
      additiveCharacter (∑ j : Fin k,
        a j * (((phasePowerSum u j : ℤ) - phasePowerSum v j : ℤ) : ℝ)) := by
  rw [phaseTupleCharacter_eq_powerSum, phaseTupleCharacter_eq_powerSum]
  let U : Fin k → ℕ := phasePowerSum u
  let V : Fin k → ℕ := phasePowerSum v
  calc
    _ = additiveCharacter (∑ j : Fin k, a j * (U j : ℝ) +
          -(∑ j : Fin k, a j * (V j : ℝ))) := by
      rw [additiveCharacter_conj, ← additiveCharacter_add]
    _ = additiveCharacter (∑ j : Fin k,
          a j * (((U j : ℤ) - V j : ℤ) : ℝ)) := by
      congr 1
      rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      ring

theorem phaseTuplePairIntegral {s k : ℕ} (u v : Fin s → ℕ) :
    ∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
      phaseTupleCharacter a u * conj (phaseTupleCharacter a v)
        ∂(volume : Measure (Fin k → ℝ)) =
      if ∀ j : Fin k, phasePowerSum u j = phasePowerSum v j then 1 else 0 := by
  let r : Fin k → ℤ := fun j => (phasePowerSum u j : ℤ) - phasePowerSum v j
  calc
    _ = ∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
        additiveCharacter (∑ j : Fin k,
          a j * (((phasePowerSum u j : ℤ) - phasePowerSum v j : ℤ) : ℝ))
          ∂(volume : Measure (Fin k → ℝ)) := by
      apply setIntegral_congr_fun
        (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      intro a ha
      exact phaseTuplePairCharacter_eq a u v
    _ = ∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
        additiveCharacter (∑ j : Fin k, a j * (r j : ℝ))
          ∂(volume : Measure (Fin k → ℝ)) := by
      apply setIntegral_congr_fun
        (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      intro a ha
      congr 1
    _ = if ∀ j, r j = 0 then 1 else 0 :=
      torus_integral_linear_character_eq r
    _ = if ∀ j : Fin k, phasePowerSum u j = phasePowerSum v j then 1 else 0 := by
      by_cases h : ∀ j : Fin k, phasePowerSum u j = phasePowerSum v j
      · have hr : ∀ j, r j = 0 := by
          intro j
          simp [r, h j]
        simp [h, hr]
      · have hr : ¬ ∀ j : Fin k, r j = 0 := by
          intro hz
          apply h
          intro j
          have hj := hz j
          simp [r] at hj
          omega
        simp [h, hr]

theorem phaseWeightedWeylSum_pow_eq {s k M : ℕ} (c : ℕ → ℂ)
    (a : Fin k → ℝ) :
    phaseWeightedWeylSum (M := M) c a ^ s =
      ∑ t ∈ phaseTupleFinset s M,
        phaseTupleWeight c t * phaseTupleCharacter a t := by
  unfold phaseWeightedWeylSum
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro t ht
  simp [phaseTupleFinset, phaseTupleWeight, phaseTupleCharacter,
    Finset.prod_mul_distrib]

theorem phaseWeightedWeylSum_pair_pow_eq {s k M : ℕ} (c : ℕ → ℂ)
    (a : Fin k → ℝ) :
    phaseWeightedWeylSum (M := M) c a ^ s *
        conj (phaseWeightedWeylSum (M := M) c a ^ s) =
      ∑ u ∈ phaseTupleFinset s M, ∑ v ∈ phaseTupleFinset s M,
        (phaseTupleWeight c u * conj (phaseTupleWeight c v)) *
          (phaseTupleCharacter a u * conj (phaseTupleCharacter a v)) := by
  have hconj :
      conj (phaseWeightedWeylSum (M := M) c a ^ s) =
        ∑ t ∈ phaseTupleFinset s M,
          conj (phaseTupleWeight c t) * conj (phaseTupleCharacter a t) := by
    rw [phaseWeightedWeylSum_pow_eq]
    rw [map_sum (starRingEnd ℂ)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_mul]
  rw [hconj, phaseWeightedWeylSum_pow_eq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem phase_norm_power_cast {z : ℂ} (s : ℕ) :
    ((‖z‖ ^ (2 * s) : ℝ) : ℂ) = z ^ s * conj (z ^ s) := by
  rw [Complex.mul_conj']
  simp only [Complex.norm_pow]
  push_cast
  rw [← pow_mul]
  congr 1
  omega

def phaseMomentSolutions (s k M : ℕ) :
    Finset ((Fin s → ℕ) × (Fin s → ℕ)) :=
  (phaseTupleFinset s M).product (phaseTupleFinset s M) |>.filter fun uv =>
    ∀ j : Fin k, phasePowerSum uv.1 j = phasePowerSum uv.2 j

theorem phaseTuple_mem_Icc {s M : ℕ} {t : Fin s → ℕ}
    (ht : t ∈ phaseTupleFinset s M) : ∀ i, t i ∈ Finset.Icc 1 M := by
  simpa [phaseTupleFinset] using (Fintype.mem_piFinset.mp ht)

theorem mem_boundedTuples_of_le {s M : ℕ} (t : Fin s → ℕ)
    (ht : ∀ i, t i ≤ M) : t ∈ boundedTuples s M := by
  classical
  unfold boundedTuples
  refine Finset.mem_image.mpr ⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i)⟩,
    Finset.mem_univ _, ?_⟩
  funext i
  rfl

theorem phaseTupleWeight_norm_le {s M : ℕ} {D : ℝ} (_hD : 0 ≤ D)
    (c : ℕ → ℂ) (hc : ∀ h ∈ Finset.Icc 1 M, ‖c h‖ ≤ D)
    (t : Fin s → ℕ) (ht : t ∈ phaseTupleFinset s M) :
    ‖phaseTupleWeight c t‖ ≤ D ^ s := by
  have hcoord : ∀ i : Fin s, ‖c (t i)‖ ≤ D := by
    intro i
    exact hc (t i) (phaseTuple_mem_Icc ht i)
  calc
    ‖phaseTupleWeight c t‖ = ∏ i : Fin s, ‖c (t i)‖ := by
      simp [phaseTupleWeight]
    _ ≤ ∏ _i : Fin s, D :=
      Finset.prod_le_prod₀ (by intro i hi; exact norm_nonneg _) (by
        intro i hi
        exact hcoord i)
    _ = D ^ s := by simp

theorem phaseMomentSolutions_card_le_vinogradovCount (s k M : ℕ) :
    (phaseMomentSolutions s k M).card ≤ vinogradovCount s k M := by
  classical
  let T := phaseTupleFinset s M
  let P := T.product T
  let Q := (((boundedTuples s M).product (boundedTuples s M)).filter fun uv =>
    (∀ j : Fin k, ∑ i : Fin s, uv.1 i ^ (j.val + 1) =
      ∑ i : Fin s, uv.2 i ^ (j.val + 1)) ∧
    (∀ i, 1 ≤ uv.1 i ∧ uv.1 i ≤ M) ∧
    (∀ i, 1 ≤ uv.2 i ∧ uv.2 i ≤ M))
  have hsub : phaseMomentSolutions s k M ⊆ Q := by
    intro uv huv
    rcases Finset.mem_filter.mp huv with ⟨huv, heq⟩
    rcases Finset.mem_product.mp huv with ⟨hu, hv⟩
    have huIcc := phaseTuple_mem_Icc hu
    have hvIcc := phaseTuple_mem_Icc hv
    have huBound : ∀ i, uv.1 i ≤ M := fun i =>
      (Finset.mem_Icc.mp (huIcc i)).2
    have hvBound : ∀ i, uv.2 i ≤ M := fun i =>
      (Finset.mem_Icc.mp (hvIcc i)).2
    have huMem := mem_boundedTuples_of_le uv.1 huBound
    have hvMem := mem_boundedTuples_of_le uv.2 hvBound
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huMem, hvMem⟩, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [phasePowerSum] using heq
    · intro i
      exact ⟨(Finset.mem_Icc.mp (huIcc i)).1, huBound i⟩
    · intro i
      exact ⟨(Finset.mem_Icc.mp (hvIcc i)).1, hvBound i⟩
  have hcard := Finset.card_le_card hsub
  simpa [Q, vinogradovCount] using hcard

theorem phaseWeightedWeylSum_moment_integral {s k M : ℕ} (c : ℕ → ℂ) :
    (∫ a in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
      ‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s)
        ∂(volume : Measure (Fin k → ℝ)) : ℂ) =
      ∑ uv ∈ phaseMomentSolutions s k M,
        phaseTupleWeight c uv.1 * conj (phaseTupleWeight c uv.2) := by
  classical
  let T := phaseTupleFinset s M
  let pairs := T.product T
  let cube : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  let term (uv : (Fin s → ℕ) × (Fin s → ℕ)) (a : Fin k → ℝ) : ℂ :=
    (phaseTupleWeight c uv.1 * conj (phaseTupleWeight c uv.2)) *
      (phaseTupleCharacter a uv.1 * conj (phaseTupleCharacter a uv.2))
  have hcube : IsCompact cube := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hpoint (a : Fin k → ℝ) :
      phaseWeightedWeylSum (M := M) c a ^ s *
          conj (phaseWeightedWeylSum (M := M) c a ^ s) =
        ∑ uv ∈ pairs, term uv a := by
    rw [phaseWeightedWeylSum_pair_pow_eq]
    rw [← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro uv huv
    simp [term, pairs, phaseTupleFinset]
  have hcont (uv : (Fin s → ℕ) × (Fin s → ℕ)) :
      Continuous (fun a : Fin k → ℝ => term uv a) := by
    dsimp [term, phaseTupleCharacter, additiveCharacter]
    fun_prop
  have hint (uv : (Fin s → ℕ) × (Fin s → ℕ) ) :
      Integrable (fun a : Fin k → ℝ => term uv a)
        ((volume : Measure (Fin k → ℝ)).restrict cube) := by
    exact (hcont uv).continuousOn.integrableOn_compact hcube
  calc
    _ = ∫ a in cube,
        (‖phaseWeightedWeylSum (M := M) c a‖ ^ (2 * s) : ℂ)
          ∂(volume : Measure (Fin k → ℝ)) := by
      rfl
    _ = ∫ a in cube,
        phaseWeightedWeylSum (M := M) c a ^ s *
          conj (phaseWeightedWeylSum (M := M) c a ^ s)
          ∂(volume : Measure (Fin k → ℝ)) := by
      apply setIntegral_congr_fun
        (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      intro a ha
      simpa using phase_norm_power_cast (z := phaseWeightedWeylSum (M := M) c a) s
    _ = ∫ a in cube, ∑ uv ∈ pairs, term uv a
          ∂(volume : Measure (Fin k → ℝ)) := by
      apply setIntegral_congr_fun
        (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
      intro a ha
      exact hpoint a
    _ = ∑ uv ∈ pairs,
        ∫ a in cube, term uv a ∂(volume : Measure (Fin k → ℝ)) := by
      rw [integral_finsetSum]
      intro uv huv
      exact hint uv
    _ = ∑ uv ∈ pairs,
        (phaseTupleWeight c uv.1 * conj (phaseTupleWeight c uv.2)) *
          (if ∀ j : Fin k, phasePowerSum uv.1 j = phasePowerSum uv.2 j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro uv huv
      rw [integral_const_mul, phaseTuplePairIntegral]
    _ = ∑ uv ∈ phaseMomentSolutions s k M,
        phaseTupleWeight c uv.1 * conj (phaseTupleWeight c uv.2) := by
      simp only [phaseMomentSolutions, T, pairs]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]

end ArtinPrimitiveRoots.Proofs.pp_phase_p
