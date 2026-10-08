import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Geometry
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Circle
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Omissions
import Mathlib.Data.Nat.GCD.BigOperators

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_raw_particleHits_line (e : Particle) (he : e.1.Prime) :
    ∃ a b : ZMod e.1, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ z : ℤ × ℤ, particleHits e z →
        a * (z.1 : ZMod e.1) + b * (z.2 : ZMod e.1) = 0 := by
  classical
  letI : Fact e.1.Prime := ⟨he⟩
  letI : NeZero e.1 := ⟨he.ne_zero⟩
  by_cases hinfty : e.2 = e.1
  · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
    intro z hh
    by_cases hz2 : (z.2 : ZMod e.1) = 0
    · simp [hz2]
    · have hval : ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val < e.1 := ZMod.val_lt _
      have hmod : ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val % (e.1 + 1) =
          ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val :=
        Nat.mod_eq_of_lt (by omega)
      have hhit : e.2 = ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val := by
        simpa [particleHits, projLine, hz2, hmod] using hh
      omega
  · refine ⟨1, -(e.2 : ZMod e.1), Or.inl one_ne_zero, ?_⟩
    intro z hh
    by_cases hz2 : (z.2 : ZMod e.1) = 0
    · have hhit : e.2 = e.1 := by simpa [particleHits, projLine, hz2] using hh
      exact (hinfty hhit).elim
    · have hval : ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val < e.1 := ZMod.val_lt _
      have hmod : ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val % (e.1 + 1) =
          ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val :=
        Nat.mod_eq_of_lt (by omega)
      have hhit : e.2 = ((z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹).val := by
        simpa [particleHits, projLine, hz2, hmod] using hh
      have hcast : (e.2 : ZMod e.1) = (z.1 : ZMod e.1) * (z.2 : ZMod e.1)⁻¹ := by
        rw [hhit, ZMod.natCast_zmod_val]
      rw [hcast]
      field_simp [hz2]
      ring

/-- A fixed nonzero determinant residue and projective line fix the other basis coordinate. -/
theorem pd4c_raw_hit_basis_residue (e : Particle) (he : e.1.Prime)
    (z z₁ z₂ : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1) (P : ℤ)
    (hP : (P : ZMod e.1) ≠ 0)
    (hh₁ : particleHits e z₁) (hh₂ : particleHits e z₂)
    (hd₁ : (det2 z z₁ : ZMod e.1) = P) (hd₂ : (det2 z z₂ : ZMod e.1) = P) :
    (e.1 : ℤ) ∣ det2 z₁ (complementVec z) - det2 z₂ (complementVec z) := by
  letI : Fact e.1.Prime := ⟨he⟩
  obtain ⟨a, b, hab, hline⟩ := pd4c_raw_particleHits_line e he
  let A : ZMod e.1 := a * z.1 + b * z.2
  let C : ZMod e.1 := a * (complementVec z).1 + b * (complementVec z).2
  have hdet : (z.1 : ZMod e.1) * (complementVec z).2 -
      (z.2 : ZMod e.1) * (complementVec z).1 = 1 := by
    have hb := Int.gcd_eq_gcd_ab z.1 z.2
    rw [hz] at hb
    have hd : det2 z (complementVec z) = 1 := by
      simpa [det2, complementVec, sub_neg_eq_add] using hb.symm
    have hc := congrArg (fun n : ℤ => (n : ZMod e.1)) hd
    simpa only [det2, Int.cast_sub, Int.cast_mul, Int.cast_one] using hc
  have hAC : A ≠ 0 ∨ C ≠ 0 := pd4c_line_coefficients_nonzero e.1 he
    z.1 z.2 (complementVec z).1 (complementVec z).2 (by rw [hdet]; exact one_ne_zero) a b hab
  have hcoord (t : ℤ × ℤ) (ht : particleHits e t) (hd : (det2 z t : ZMod e.1) = P) :
      A * (det2 t (complementVec z) : ZMod e.1) + C * (P : ZMod e.1) = 0 := by
    have hlin := hline t ht
    have hr := pd4c_primitive_basis_coordinates z t hz
    have hfirst := congrArg (fun v : ℤ × ℤ => (v.1 : ZMod e.1)) hr
    have hsecond := congrArg (fun v : ℤ × ℤ => (v.2 : ZMod e.1)) hr
    dsimp only [Prod.fst, Prod.snd] at hfirst hsecond
    push_cast at hfirst hsecond
    rw [hd] at hfirst hsecond
    dsimp [A, C]
    linear_combination hlin - a * hfirst - b * hsecond
  have h₁ := hcoord z₁ hh₁ hd₁
  have h₂ := hcoord z₂ hh₂ hd₂
  have hA : A ≠ 0 := by
    intro hAzero
    have hC : C ≠ 0 := hAC.resolve_left (by simpa only [not_not] using hAzero)
    rw [hAzero, zero_mul, zero_add] at h₁
    exact (mul_ne_zero hC hP) h₁
  have heq : (det2 z₁ (complementVec z) : ZMod e.1) =
      (det2 z₂ (complementVec z) : ZMod e.1) := by
    apply (mul_left_cancel₀ hA)
    linear_combination h₁ - h₂
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp heq.symm

/-- Two raw neighbors at one promoted anchor give a short circle difference of trial phases. -/
theorem pd4c_raw_anchor_phase_difference (e : Particle) (he : e.1.Prime)
    (z z₁ z₂ : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (P : ℤ) (n₁ n₂ : ℕ) (r : ℝ) (hP : (P : ZMod e.1) ≠ 0)
    (hh₁ : particleHits e z₁) (hh₂ : particleHits e z₂)
    (hd₁ : det2 z z₁ = P - (e.1 : ℤ) * n₁)
    (hd₂ : det2 z z₂ = P - (e.1 : ℤ) * n₂)
    (hb₁ : |(det2 z₁ (complementVec z) : ℝ) + (det2 z z₁ : ℝ) * r| ≤ 16)
    (hb₂ : |(det2 z₂ (complementVec z) : ℝ) + (det2 z z₂ : ℝ) * r| ≤ 16) :
    circleDistance (((n₁ : ℝ) - n₂) * r) ≤ 32 / (e.1 : ℝ) := by
  have hp : 0 < (e.1 : ℝ) := by exact_mod_cast he.pos
  have hd₁' : (det2 z z₁ : ZMod e.1) = P := by simp [hd₁]
  have hd₂' : (det2 z z₂ : ZMod e.1) = P := by simp [hd₂]
  obtain ⟨k, hk⟩ := pd4c_raw_hit_basis_residue e he z z₁ z₂ hz P hP hh₁ hh₂ hd₁' hd₂'
  have hkR := congrArg (fun n : ℤ => (n : ℝ)) hk
  have hd₁R := congrArg (fun n : ℤ => (n : ℝ)) hd₁
  have hd₂R := congrArg (fun n : ℤ => (n : ℝ)) hd₂
  push_cast at hkR hd₁R hd₂R
  have hdiff : |(e.1 : ℝ) * (k - (((n₁ : ℝ) - n₂) * r))| ≤ 32 := by
    calc
      _ = |((det2 z₁ (complementVec z) : ℝ) + (det2 z z₁ : ℝ) * r) -
          ((det2 z₂ (complementVec z) : ℝ) + (det2 z z₂ : ℝ) * r)| := by
        congr 1
        linear_combination -hkR - r * hd₁R + r * hd₂R
      _ ≤ |(det2 z₁ (complementVec z) : ℝ) + (det2 z z₁ : ℝ) * r| +
          |(det2 z₂ (complementVec z) : ℝ) + (det2 z z₂ : ℝ) * r| := abs_sub _ _
      _ ≤ 32 := by linarith
  rw [abs_mul, abs_of_pos hp] at hdiff
  calc
    _ ≤ |((n₁ : ℝ) - n₂) * r - (k : ℝ)| := pd4c_circleDistance_le_abs_sub_int _ k
    _ = |(k : ℝ) - (((n₁ : ℝ) - n₂) * r)| := abs_sub_comm _ _
    _ ≤ 32 / (e.1 : ℝ) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hdiff)

/-- The cross-edge ban leaves a nonzero full-source-product residue at the promoted prime. -/
theorem pd4c_prime_not_dvd_fullProduct {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime) (q : ℕ) (hq : q.Prime)
    (hban : ∀ i j, q ≠ p i j) : ¬ q ∣ pd4c_fullPrimeProduct p := by
  intro hdiv
  rw [pd4c_fullPrimeProduct, hq.prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨i, _, hdiv⟩ := hdiv
  rw [hq.prime.dvd_finsetProd_iff] at hdiv
  obtain ⟨j, _, hdiv⟩ := hdiv
  exact hban i j (((hp i j).dvd_iff_eq hq.ne_one).mp hdiv).symm

/-- Outside the second goodness test's exceptional set, one promoted anchor permits one trial. -/
theorem pd4c_raw_good_trial_unique {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K)
    (fresh : Fin K → ℕ) (S : PDScale) (w : ArchRoot)
    (e : Particle) (he : e.1.Prime) (hband : e.1 ∈ primeBand x (a iStar))
    (z z₁ z₂ : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hU : 0 < S.U) (hw : w.InRegion S)
    (hbox : envBox S w z) (hbox₁ : envBox S w z₁) (hbox₂ : envBox S w z₂)
    (hP : ((pd4c_fullPrimeProduct p : ℤ) : ZMod e.1) ≠ 0)
    (hh₁ : particleHits e z₁) (hh₂ : particleHits e z₂)
    (n₁ n₂ : ℕ)
    (hd₁ : det2 z z₁ = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) * n₁)
    (hd₂ : det2 z z₂ = (pd4c_fullPrimeProduct p : ℤ) - (e.1 : ℤ) * n₂)
    (ht₁ : IsGoodnessTrialValue a p d₀ I iStar fresh n₁)
    (ht₂ : IsGoodnessTrialValue a p d₀ I iStar fresh n₂)
    (hsep : ∀ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ →
      IsGoodnessTrialValue a p d₀ I iStar fresh n₂ → n₁ ≠ n₂ →
        100 * Real.exp (-Real.rpow (Real.log x) (a iStar)) <
          circleDistance (((n₁ : ℝ) - n₂) * transportedRatio w z)) : n₁ = n₂ := by
  have hb₁ := pd4c_env_basis_phase_bound S w z z₁ hU hw hz hbox hbox₁
  have hb₂ := pd4c_env_basis_phase_bound S w z z₂ hU hw hz hbox hbox₂
  have hphase := pd4c_raw_anchor_phase_difference e he z z₁ z₂ hz (pd4c_fullPrimeProduct p)
    n₁ n₂ (transportedRatio w z) hP hh₁ hh₂ hd₁ hd₂ hb₁ hb₂
  have hplower := (Finset.mem_filter.mp hband).2.2.1
  have hinv : 1 / (e.1 : ℝ) ≤ Real.exp (-Real.rpow (Real.log x) (a iStar)) := by
    calc
      _ ≤ 1 / Real.exp (Real.rpow (Real.log x) (a iStar)) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hplower
      _ = _ := by rw [one_div, Real.exp_neg]
  by_contra hne
  have hlow := hsep n₁ n₂ ht₁ ht₂ hne
  have hhi : circleDistance (((n₁ : ℝ) - n₂) * transportedRatio w z) ≤
      100 * Real.exp (-Real.rpow (Real.log x) (a iStar)) := by
    calc
      _ ≤ 32 / (e.1 : ℝ) := hphase
      _ = 32 * (1 / (e.1 : ℝ)) := by ring
      _ ≤ 32 * Real.exp (-Real.rpow (Real.log x) (a iStar)) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ ≤ _ := by nlinarith [Real.exp_pos (-Real.rpow (Real.log x) (a iStar))]
  exact (not_lt_of_ge hhi) hlow

/-- Source prime factors and banned promoted prime factors separate the two numeric products. -/
theorem pd4c_omission_promoted_coprime {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime) (om : Fin K → Fin (slotCount x))
    (I : Finset (Fin K)) (iStar : Fin K) (z : Fin K → ℕ)
    (hz : ∀ i, i ∈ I ∧ i ≠ iStar → (z i).Prime)
    (hban : ∀ i, i ∈ I ∧ i ≠ iStar → ∀ j k, z i ≠ p j k) :
    Nat.Coprime (omissionProduct p om)
      (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1) := by
  unfold omissionProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro j hj
  apply Nat.coprime_prod_left_iff.mpr
  intro k hk
  by_cases hshared : k ≠ om j
  · rw [if_pos hshared]
    apply Nat.coprime_prod_right_iff.mpr
    intro i hi
    by_cases heligible : i ∈ I ∧ i ≠ iStar
    · rw [if_pos heligible]
      exact (Nat.coprime_primes (hp j k) (hz i heligible)).mpr (hban i heligible j k).symm
    · simp only [if_neg heligible, Nat.Coprime, Nat.gcd_one_right]
  · simp only [if_neg hshared, Nat.Coprime, Nat.gcd_one_left]

/-- Coprimality separates D and Z without a factorization data structure. -/
theorem pd4c_separate_trial_products (D₁ D₂ Z₁ Z₂ T : ℕ) (hT : T ≠ 0)
    (h₁ : Nat.Coprime D₁ Z₂) (h₂ : Nat.Coprime D₂ Z₁)
    (hprod : D₁ * Z₁ * T = D₂ * Z₂ * T) : D₁ = D₂ := by
  have heq : D₁ * Z₁ = D₂ * Z₂ := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hT) hprod
  have hd₁ : D₁ ∣ D₂ * Z₂ := by rw [← heq]; exact dvd_mul_right _ _
  have hd₂ : D₂ ∣ D₁ * Z₁ := by rw [heq]; exact dvd_mul_right _ _
  exact Nat.dvd_antisymm ((h₁.dvd_mul_right).mp hd₁) ((h₂.dvd_mul_right).mp hd₂)

/-- A unique numeric good trial determines the source omission tuple. -/
theorem pd4c_trial_omission_unique {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (hp : ∀ i j, (p i j).Prime)
    (hinj : Function.Injective (fun ij : Fin K × Fin (slotCount x) => p ij.1 ij.2))
    (om₁ om₂ : Fin K → Fin (slotCount x)) (Z₁ Z₂ T : ℕ) (hT : T ≠ 0)
    (h₁ : Nat.Coprime (omissionProduct p om₁) Z₂)
    (h₂ : Nat.Coprime (omissionProduct p om₂) Z₁)
    (hprod : omissionProduct p om₁ * Z₁ * T = omissionProduct p om₂ * Z₂ * T) : om₁ = om₂ := by
  apply omissionProduct_injective p hp hinj
  exact pd4c_separate_trial_products _ _ _ _ T hT h₁ h₂ hprod

end

end ArtinPrimitiveRoots.TypeII.PD
