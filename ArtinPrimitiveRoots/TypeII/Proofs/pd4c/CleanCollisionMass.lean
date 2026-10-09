import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical
open scoped BigOperators

noncomputable section

/-- The mass of fresh labels colliding with fixed last labels has a uniform union bound. -/
theorem finite_fresh_collision_mass_le (K : ℕ)
    (P : Fin K → Finset ℕ) (ν : Fin K → ℕ → ℝ) (b : Fin K → ℕ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hν : ∀ i : Fin K, ∀ p ∈ P i, 0 ≤ ν i p)
    (htotal : ∀ i : Fin K, (∑ p ∈ P i, ν i p) ≤ 2)
    (hsup : ∀ i : Fin K, ∀ p ∈ P i, ν i p ≤ ε) :
    (∑ p : (i : Fin K) → P i,
      if ∃ i : Fin K, (p i : ℕ) = b i then ∏ i : Fin K, ν i (p i) else 0) ≤
      (K : ℝ)*ε*(2 : ℝ)^K := by
  classical
  let X := (i : Fin K) → P i
  let W (p : X) : ℝ := ∏ i : Fin K, ν i (p i)
  have hW (p : X) : 0 ≤ W p :=
    Finset.prod_nonneg (fun i hi => hν i (p i) (p i).property)
  have hmarginal (i : Fin K) :
      (∑ p : P i, if (p : ℕ) = b i then ν i p else 0) ≤ ε := by
    by_cases hb : b i ∈ P i
    · let c : P i := ⟨b i, hb⟩
      have hcond (p : P i) : (p : ℕ) = b i ↔ p = c := by
        constructor
        · intro hh
          exact Subtype.ext hh
        · intro hh
          exact congrArg Subtype.val hh
      calc
        _ = ν i (b i) := by simp only [hcond]; simp [c]
        _ ≤ ε := hsup i (b i) hb
    · have hnot (p : P i) : ¬ (p : ℕ) = b i := by
        intro hh
        apply hb
        simpa only [hh] using p.property
      simpa only [hnot, if_false, Finset.sum_const_zero] using hε
  have hfixed (i : Fin K) :
      (∑ p : X, if (p i : ℕ) = b i then W p else 0) ≤ ε*(2 : ℝ)^K := by
    let v (j : Fin K) (p : P j) : ℝ :=
      if j = i then if (p : ℕ) = b i then ν j p else 0 else ν j p
    have hv (j : Fin K) (p : P j) : 0 ≤ v j p := by
      dsimp only [v]
      split_ifs <;> first | exact hν j p p.property | exact le_rfl
    have hpoint (p : X) :
        (if (p i : ℕ) = b i then W p else 0) = ∏ j : Fin K, v j (p j) := by
      by_cases hp : (p i : ℕ) = b i
      · rw [if_pos hp]
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp only [v, if_pos rfl, if_pos hp]
        · simp only [v, if_neg hji]
      · rw [if_neg hp]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [v, if_pos rfl, if_neg hp]
    have hsum (j : Fin K) : (∑ p : P j, v j p) ≤ if j = i then ε else 2 := by
      by_cases hji : j = i
      · subst j
        simpa [v] using hmarginal i
      · simpa only [v, if_neg hji, Finset.sum_coe_sort] using htotal j
    have hprod : (∏ j : Fin K, if j = i then ε else (2 : ℝ)) =
        ε*(∏ j ∈ (Finset.univ : Finset (Fin K)).erase i, (2 : ℝ)) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j : Fin K => if j = i then ε else (2 : ℝ)) (Finset.mem_univ i)]
      rw [if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact if_neg (Finset.mem_erase.mp hj).1
    have hcard : ((Finset.univ : Finset (Fin K)).erase i).card ≤ K := by
      simpa using Finset.card_le_univ ((Finset.univ : Finset (Fin K)).erase i)
    calc
      _ = ∑ p : X, ∏ j : Fin K, v j (p j) :=
        Finset.sum_congr rfl (fun p hp => hpoint p)
      _ = ∏ j : Fin K, ∑ p : P j, v j p := (Fintype.prod_sum v).symm
      _ ≤ ∏ j : Fin K, if j = i then ε else (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact Finset.sum_nonneg (fun p hp => hv j p)
        · intro j hj
          exact hsum j
      _ = ε*(2 : ℝ)^((Finset.univ : Finset (Fin K)).erase i).card := by
        rw [hprod]
        simp only [Finset.prod_const]
      _ ≤ ε*(2 : ℝ)^K :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcard) hε
  have hunion (p : X) :
      (if ∃ i : Fin K, (p i : ℕ) = b i then W p else 0) ≤
        ∑ i : Fin K, if (p i : ℕ) = b i then W p else 0 := by
    by_cases hp : ∃ i : Fin K, (p i : ℕ) = b i
    · rw [if_pos hp]
      obtain ⟨i, hi⟩ := hp
      calc
        W p = (if (p i : ℕ) = b i then W p else 0) := (if_pos hi).symm
        _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (a := i)
          (f := fun j : Fin K => if (p j : ℕ) = b j then W p else 0)
          (fun j hj => by split_ifs <;> first | exact hW p | exact le_rfl)
          (Finset.mem_univ i)
    · rw [if_neg hp]
      exact Finset.sum_nonneg
        (fun i hi => by split_ifs <;> first | exact hW p | exact le_rfl)
  change (∑ p : X, if ∃ i : Fin K, (p i : ℕ) = b i then W p else 0) ≤ _
  calc
    _ ≤ ∑ p : X, ∑ i : Fin K, if (p i : ℕ) = b i then W p else 0 :=
      Finset.sum_le_sum (fun p hp => hunion p)
    _ = ∑ i : Fin K, ∑ p : X, if (p i : ℕ) = b i then W p else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin K, ε*(2 : ℝ)^K :=
      Finset.sum_le_sum (fun i hi => hfixed i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
