import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.PSeries

open NumberField IsDedekindDomain
open Filter Asymptotics LSeries
open scoped Topology

noncomputable section

namespace ArtinPrimitiveRoots.A1.Coeff

theorem summable_absNorm_rpow {F : Type} [Field F] [NumberField F] (s : ℝ)
    (hs : 2 < s) :
    Summable fun I : Ideal (𝓞 F) => (Ideal.absNorm I : ℝ) ^ (-s) := by
  classical
  let B (n : ℕ) := {I : Ideal (𝓞 F) // Ideal.absNorm I ≤ n + 1}
  let C (n : ℕ) : ℝ := Nat.card (B n)
  let A (n : ℕ) := {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  let a (n : ℕ) : ℝ := Nat.card (A n)
  let BR (n : ℕ) := {I : Ideal (𝓞 F) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ) + 1}
  have eBound (n : ℕ) : B n ≃ BR n := by
    exact Equiv.subtypeEquiv (Equiv.refl _) fun I => by
      change (Ideal.absNorm I ≤ n + 1) ↔ (Ideal.absNorm I : ℝ) ≤ (n : ℝ) + 1
      constructor <;> intro h <;> exact_mod_cast h
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => C n / ((n : ℝ) + 1)) atTop
      (𝓝 (NumberField.dedekindZeta_residue F)) := by
    have h := (NumberField.Ideal.tendsto_norm_le_div_atTop F).comp harg
    refine h.congr' ?_
    filter_upwards [] with n
    simp only [Function.comp_apply, C]
    rw [Nat.card_congr (eBound n)]
  have hC : (fun n : ℕ => C n) =O[atTop] fun n => (n : ℝ) + 1 := by
    exact isBigO_of_div_tendsto_nhds (by
      filter_upwards [] with n hn
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact False.elim ((ne_of_gt hp) hn)) (NumberField.dedekindZeta_residue F) hlim
  have hBound (n : ℕ) : a n ≤ C n := by
    letI : Finite (B n) := (Ideal.finite_setOfPred_absNorm_le (n + 1)).to_subtype
    let inc : A n → B n := fun I =>
      ⟨I.1, by rw [I.2]; exact Nat.le_succ n⟩
    have hinj : Function.Injective inc := by
      intro I J h
      have hval : (inc I).1 = (inc J).1 := congrArg (fun x : B n => x.1) h
      dsimp [inc] at hval
      exact Subtype.ext hval
    change (Nat.card (A n) : ℝ) ≤ (Nat.card (B n) : ℝ)
    exact_mod_cast (Nat.card_le_card_of_injective inc hinj)
  have hAC : ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ ‖C n‖ := by
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact hBound n
  have hshift : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n => (n : ℝ) := by
    refine (IsBigOWith.of_bound (c := 2) ?_).isBigO
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1),
      Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    nlinarith
  have haO : (fun n : ℕ => a n) =O[atTop] fun n => (n : ℝ) :=
    (hAC.trans_isBigO hC).trans hshift
  let f : ℕ → ℂ := fun n => (Nat.card (A n) : ℂ)
  have hfO : f =O[atTop] fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1) := by
    obtain ⟨K, hK⟩ := haO.isBigOWith
    refine (IsBigOWith.of_bound (c := K) ?_).isBigO
    filter_upwards [hK.bound] with n hn
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    simpa [f, a] using hn
  have hLS : LSeriesSummable f (s : ℂ) :=
    LSeriesSummable_of_isBigO_rpow (x := 2) (s := (s : ℂ)) (by simpa using hs)
      hfO
  have hTerm : Summable fun n : ℕ => ‖LSeries.term f (s : ℂ) n‖ := hLS.norm
  let normMap : Ideal (𝓞 F) → ℕ := Ideal.absNorm
  let fibEquiv : (Σ n : ℕ, {I : Ideal (𝓞 F) // normMap I = n}) ≃ Ideal (𝓞 F) :=
    Equiv.sigmaFiberEquiv normMap
  let idealTerm : Ideal (𝓞 F) → ℝ := fun I => (Ideal.absNorm I : ℝ) ^ (-s)
  have hsumIdeal : Summable idealTerm := by
    rw [← fibEquiv.summable_iff]
    apply (summable_sigma_of_nonneg (f := fun p : Σ n : ℕ, A n => idealTerm (fibEquiv p))
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2
    refine ⟨?_, ?_⟩
    · intro n
      letI : Finite (B n) := (Ideal.finite_setOfPred_absNorm_le (n + 1)).to_subtype
      let incA : A n → B n := fun I => ⟨I.1, by rw [I.2]; exact Nat.le_succ n⟩
      letI : Finite (A n) := Finite.of_injective incA (by
        intro I J h
        have hval : (incA I).1 = (incA J).1 := congrArg (fun x : B n => x.1) h
        dsimp [incA] at hval
        exact Subtype.ext hval)
      letI : Fintype (A n) := Fintype.ofFinite _
      exact summable_of_hasFiniteSupport <|
        Set.finite_univ.subset (Set.subset_univ _)
    · have hsum_eq (n : ℕ) :
      (∑' I : A n, idealTerm (fibEquiv ⟨n, I⟩)) =
            ‖LSeries.term f (s : ℂ) n‖ := by
        letI : Finite (B n) := (Ideal.finite_setOfPred_absNorm_le (n + 1)).to_subtype
        let incA : A n → B n := fun I => ⟨I.1, by rw [I.2]; exact Nat.le_succ n⟩
        letI : Finite (A n) := Finite.of_injective incA (by
          intro I J h
          have hval : (incA I).1 = (incA J).1 := congrArg (fun x : B n => x.1) h
          dsimp [incA] at hval
          exact Subtype.ext hval)
        letI : Fintype (A n) := Fintype.ofFinite _
        have hconst : ∀ I : A n, idealTerm (fibEquiv ⟨n, I⟩) = (n : ℝ) ^ (-s) := by
          intro I
          simp [idealTerm, fibEquiv, normMap, I.2]
        rw [tsum_fintype]
        simp_rw [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [a, f]
        by_cases hn : n = 0
        · subst n
          have hs0 : -s ≠ 0 := by linarith
          simp [LSeries.term_zero, Real.zero_rpow, hs0]
        · rw [LSeries.norm_term_eq, if_neg hn]
          rw [Real.rpow_neg (Nat.cast_nonneg n) s, div_eq_mul_inv]
          simp [Nat.card_eq_fintype_card, Real.norm_of_nonneg (Nat.cast_nonneg _)]
      simpa only [hsum_eq] using hTerm
  exact hsumIdeal

end ArtinPrimitiveRoots.A1.Coeff
