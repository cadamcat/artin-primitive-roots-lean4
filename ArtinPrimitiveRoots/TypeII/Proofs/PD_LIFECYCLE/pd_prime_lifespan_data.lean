import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.pd_lifecycle_parameters

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical Filter
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- The finite valid endpoint alternatives sum to the exact frozen lifespan expression.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:402–417. Uses only Defs; feeds
pd_prime_lifespan_product and history_path_value. No band or positivity assumption is needed. -/
theorem pd_prime_lifespan_data {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) :
    (∑ life : PrimeLife S γ p, primeLifeCharge F S γ p life) = pdPathLifespan F S γ p := by
  classical
  let J := Fin (pathLength S.x + 1)
  let A : Finset J := Finset.univ.filter (fun j => IsActiveAt γ p j)
  let lam : J → Fin (p + 1) := fun j => projLine p (γ j).1
  let eta : J → ℝ := fun j => memoryEta S.x F.q_d j.val
  let d : ℝ := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  have hA : pdLifeActive S γ p = A := by rfl
  have hSumFilter :
      (∑ life : PrimeLife S γ p, primeLifeCharge F S γ p life) =
        ∑ e : Option J × Option J,
          if hvalid : e ∈ pdLifeEndpoints S γ p then
            primeLifeCharge F S γ p ⟨e, hvalid⟩ else 0 := by
    let f : (Option J × Option J) → ℝ := fun e =>
      if hvalid : e ∈ pdLifeEndpoints S γ p then
        primeLifeCharge F S γ p ⟨e, hvalid⟩ else 0
    change (∑ life : {e // e ∈ pdLifeEndpoints S γ p},
      primeLifeCharge F S γ p life) = _
    let B := {e : Option J × Option J // ¬ e ∈ pdLifeEndpoints S γ p}
    let eSumEquiv : PrimeLife S γ p ⊕ B ≃ (Option J × Option J) :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun e => if h : e ∈ pdLifeEndpoints S γ p then
          Sum.inl ⟨e, h⟩ else Sum.inr ⟨e, h⟩
        left_inv := by
          intro x
          cases x with
          | inl life => simp [life.property]
          | inr life => simp [life.property]
        right_inv := by
          intro x
          by_cases hx : x ∈ pdLifeEndpoints S γ p <;> simp [hx] }
    have hf :
        (∑ life : {e // e ∈ pdLifeEndpoints S γ p},
          primeLifeCharge F S γ p life) = ∑ e : Option J × Option J, f e := by
      calc
        _ = (∑ life : PrimeLife S γ p, f life.1) +
              ∑ life : B, f life.1 := by
          have hcomp : ∑ life : B, f life.1 = 0 := by
            apply Fintype.sum_eq_zero
            intro life
            simp [f, life.property]
          rw [hcomp]
          simp [f]
        _ = ∑ choice : PrimeLife S γ p ⊕ B, f (eSumEquiv choice) := by
              simpa [eSumEquiv] using
                (Fintype.sum_sum_type (fun choice : PrimeLife S γ p ⊕ B =>
                  f (eSumEquiv choice))).symm
        _ = ∑ e : Option J × Option J, f e := Equiv.sum_comp eSumEquiv f
    simpa [f] using hf
  change (∑ life : PrimeLife S γ p, primeLifeCharge F S γ p life) =
    pdLifespanFormula p (pathLength S.x) (fun j => projLine p (γ j).1)
      (IsActiveAt γ p) (fun j => memoryEta S.x F.q_d j.val)
      (memoryBPrime S.x F.q_d p)
  rw [hSumFilter]
  by_cases hANonempty : A.Nonempty
  · let α := A.min' hANonempty
    let ω := A.max' hANonempty
    let ls := lam α
    by_cases hCommon : ∀ j ∈ A, lam j = ls
    · let mid : ℝ :=
        ∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < ω ∧ j ∉ A),
          (1 - eta j * (if lam j = ls then 1 else 0))
      let preTail : J → ℝ := fun a =>
        ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < α),
          (1 - eta j * (if lam j = ls then 1 else 0))
      let postTail : J → ℝ := fun c =>
        ∏ j ∈ Finset.univ.filter (fun j => ω < j ∧ j < c),
          (1 - eta j * (if lam j = ls then 1 else 0))
      let preOK : Option J → Prop := fun e =>
        match e with
        | none => True
        | some a => a < α ∧ lam a = ls
      let postOK : Option J → Prop := fun e =>
        match e with
        | none => True
        | some c => ω < c ∧ lam c = ls
      let preTerm : Option J → ℝ := fun e =>
        match e with
        | none => 1
        | some a => -eta a * preTail a
      let postTerm : Option J → ℝ := fun e =>
        match e with
        | none => 1
        | some c => -eta c * postTail c
      have hMin_irrel (hAct : A.Nonempty) : A.min' hAct = α := by rfl
      have hMax_irrel (hAct : A.Nonempty) : A.max' hAct = ω := by rfl
      have hAnchor : ∀ j ∈ A,
          projLine p (γ j).1 = projLine p (γ α).1 := by
        simpa [lam, ls] using hCommon
      have hValidEq (a c : Option J) :
          pdLifeEndpointValid S γ p (a, c) ↔ preOK a ∧ postOK c := by
        simp only [pdLifeEndpointValid, hA]
        rw [dif_pos hANonempty]
        cases a <;> cases c <;>
          simp only [preOK, postOK] <;> aesop
      have hChargeEq (a c : Option J)
          (hv : pdLifeEndpointValid S γ p (a, c)) :
          primeLifeCharge F S γ p ⟨(a, c),
            (by
              change (a, c) ∈
                (Finset.univ.filter (pdLifeEndpointValid S γ p))
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)⟩ =
            d * preTerm a * mid * postTerm c := by
        have hD : (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹ = d := rfl
        cases a <;> cases c <;>
          simp only [primeLifeCharge, hA, dif_pos hANonempty, hD,
            hMin_irrel, hMax_irrel, preTerm, postTerm, mid, preTail,
            postTail, pdLifeSurvival, eta, lam, ls] <;> rfl
      have hEndpoint :
          (∑ e : Option J × Option J,
            if hvalid : e ∈ pdLifeEndpoints S γ p then
              primeLifeCharge F S γ p ⟨e, hvalid⟩ else 0) =
            ∑ a : Option J, ∑ c : Option J,
              if preOK a ∧ postOK c then
                d * preTerm a * mid * postTerm c else 0 := by
        have hTerm (a : Option J) (c : Option J) :
          (if hvalid : (a, c) ∈ pdLifeEndpoints S γ p then
            primeLifeCharge F S γ p ⟨(a, c), hvalid⟩ else 0) =
              if preOK a ∧ postOK c then
                d * preTerm a * mid * postTerm c else 0 := by
          by_cases hmem : (a, c) ∈ pdLifeEndpoints S γ p
          · have hv : pdLifeEndpointValid S γ p (a, c) := by
              change (a, c) ∈
                (Finset.univ.filter (pdLifeEndpointValid S γ p)) at hmem
              exact (Finset.mem_filter.mp hmem).2
            have hOK := (hValidEq a c).mp hv
            rw [dif_pos hmem, if_pos hOK]
            simpa using hChargeEq a c hv
          · have hv : ¬ pdLifeEndpointValid S γ p (a, c) := by
              intro hv
              apply hmem
              change (a, c) ∈
                (Finset.univ.filter (pdLifeEndpointValid S γ p))
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
            have hNoOK : ¬ (preOK a ∧ postOK c) := by
              intro hOK
              exact hv ((hValidEq a c).mpr hOK)
            rw [dif_neg hmem, if_neg hNoOK]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro c hc
        exact hTerm a c
      have hPre :
          (∑ e : Option J, if preOK e then preTerm e else 0) =
            1 - ∑ a ∈ Finset.univ.filter (fun a : J => a < α),
              eta a * (if lam a = ls then 1 else 0) * preTail a := by
        rw [Fintype.sum_option]
        simp only [preOK, preTerm]
        rw [Finset.sum_filter]
        change
          1 + (∑ a : J, if a < α ∧ lam a = ls then -eta a * preTail a else 0) =
            1 - (∑ a : J, if a < α then
              eta a * (if lam a = ls then 1 else 0) * preTail a else 0)
        have hterms :
            (∑ a : J, if a < α ∧ lam a = ls then -eta a * preTail a else 0) =
              ∑ a : J, -(if a < α then
                eta a * (if lam a = ls then 1 else 0) * preTail a else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hlt : a < α
          · by_cases hline : lam a = ls <;> simp [hlt, hline]
          · simp [hlt]
        rw [hterms, Finset.sum_neg_distrib]
        ring
      have hPost :
          (∑ e : Option J, if postOK e then postTerm e else 0) =
            1 - ∑ c ∈ Finset.univ.filter (fun c : J => ω < c),
              eta c * (if lam c = ls then 1 else 0) * postTail c := by
        rw [Fintype.sum_option]
        simp only [postOK, postTerm]
        rw [Finset.sum_filter]
        change
          1 + (∑ c : J, if ω < c ∧ lam c = ls then -eta c * postTail c else 0) =
            1 - (∑ c : J, if ω < c then
              eta c * (if lam c = ls then 1 else 0) * postTail c else 0)
        have hterms :
            (∑ c : J, if ω < c ∧ lam c = ls then -eta c * postTail c else 0) =
              ∑ c : J, -(if ω < c then
                eta c * (if lam c = ls then 1 else 0) * postTail c else 0) := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hgt : ω < c
          · by_cases hline : lam c = ls <;> simp [hgt, hline]
          · simp [hgt]
        rw [hterms, Finset.sum_neg_distrib]
        ring
      have hFactor :
          (∑ a : Option J, ∑ c : Option J,
            if preOK a ∧ postOK c then
              d * preTerm a * mid * postTerm c else 0) =
            (∑ a : Option J, if preOK a then preTerm a else 0) * d * mid *
              (∑ c : Option J, if postOK c then postTerm c else 0) := by
        calc
          _ = ∑ a : Option J, ∑ c : Option J,
                (if preOK a then preTerm a else 0) *
                  (if postOK c then d * mid * postTerm c else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro c hc
              by_cases hpre : preOK a <;> by_cases hpost : postOK c <;>
                simp [hpre, hpost] <;> ring
          _ = (∑ a : Option J, if preOK a then preTerm a else 0) *
                (∑ c : Option J, if postOK c then d * mid * postTerm c else 0) :=
              (Fintype.sum_mul_sum _ _).symm
          _ = (∑ a : Option J, if preOK a then preTerm a else 0) *
                (d * mid * (∑ c : Option J, if postOK c then postTerm c else 0)) := by
              congr 1
              calc
                (∑ c : Option J, if postOK c then d * mid * postTerm c else 0) =
                    ∑ c : Option J, d * mid * (if postOK c then postTerm c else 0) := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  by_cases hpost : postOK c <;> simp [hpost]
                _ = d * mid * (∑ c : Option J, if postOK c then postTerm c else 0) := by
                  rw [Finset.mul_sum]
          _ = _ := by ring
      have hFormula :
          pdLifespanFormula p (pathLength S.x) (fun j => projLine p (γ j).1)
            (IsActiveAt γ p) (fun j => memoryEta S.x F.q_d j.val)
            (memoryBPrime S.x F.q_d p) =
          d * (1 - ∑ a ∈ Finset.univ.filter (fun a : J => a < α),
                eta a * (if lam a = ls then 1 else 0) * preTail a) * mid *
            (1 - ∑ c ∈ Finset.univ.filter (fun c : J => ω < c),
                eta c * (if lam c = ls then 1 else 0) * postTail c) := by
        have hAFormula :
            (Finset.univ.filter (IsActiveAt γ p)).Nonempty := by
          simpa [A] using hANonempty
        have hCommonFormula :
            ∀ j ∈ Finset.univ.filter (IsActiveAt γ p),
              projLine p (γ j).1 =
                projLine p (γ ((Finset.univ.filter (IsActiveAt γ p)).min' hAFormula)).1 := by
          intro j hj
          have hjA : j ∈ A := by simpa [A] using hj
          simpa [A, α, lam, ls] using hCommon j hjA
        unfold pdLifespanFormula
        rw [dif_pos hAFormula]
        rw [if_pos hCommonFormula]
      rw [hEndpoint, hFactor, hPre, hPost, hFormula]
      ring
    · have hNotValid (e : Option J × Option J) :
          ¬ pdLifeEndpointValid S γ p e := by
        intro he
        have he' := he
        simp [pdLifeEndpointValid, pdLifeActive, A, hANonempty,
          α, ω, ls, lam] at he'
        apply hCommon
        intro j hj
        have hjAct : IsActiveAt γ p j := (Finset.mem_filter.mp hj).2
        simpa [lam, ls] using he'.1 j hjAct
      have hAFormula :
          (Finset.univ.filter (IsActiveAt γ p)).Nonempty := by
        simpa [A] using hANonempty
      have hCommonNotFormula :
          ¬ (∀ j ∈ Finset.univ.filter (IsActiveAt γ p),
              projLine p (γ j).1 =
                projLine p (γ ((Finset.univ.filter (IsActiveAt γ p)).min'
                  hAFormula)).1) := by
        simpa [A, α, lam, ls] using hCommon
      have hFormulaZero :
          pdLifespanFormula p (pathLength S.x)
            (fun j => projLine p (γ j).1) (IsActiveAt γ p)
            (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p) = 0 := by
        unfold pdLifespanFormula
        rw [dif_pos hAFormula]
        rw [if_neg hCommonNotFormula]
      rw [hFormulaZero]
      simp [hNotValid, pdLifeEndpoints]
  · try simp [pdLifeEndpoints, Finset.sum_filter, pdLifeEndpointValid,
      primeLifeCharge, pdLifeActive, pdLifeSurvival, pdLifespanFormula,
      hA, A, hANonempty, lam, eta, d,
      Fintype.sum_prod_type, Fintype.sum_option]
    have hpoint (a c : J) :
        (if a < c ∧ lam c = lam a then
          (memoryBPrime S.x F.q_d p)⁻¹ * ((p : ℝ) + 1)⁻¹ *
            eta a * eta c *
              ∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
                (1 - (if lam j = lam a then eta j else 0))
        else 0) =
          (memoryBPrime S.x F.q_d p)⁻¹ * ((p : ℝ) + 1)⁻¹ *
            (if a < c then
              if lam c = lam a then
                eta a * eta c *
                  ∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
                    (1 - (if lam j = lam a then eta j else 0))
              else 0 else 0) := by
      by_cases hlt : a < c
      · by_cases hline : lam c = lam a <;> simp [hlt, hline] <;> ring
      · simp [hlt]
    calc
      _ = ∑ a : J, ∑ c : J,
            (memoryBPrime S.x F.q_d p)⁻¹ * ((p : ℝ) + 1)⁻¹ *
              (if a < c then
                if lam c = lam a then
                  eta a * eta c *
                    ∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
                      (1 - (if lam j = lam a then eta j else 0))
                else 0 else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro c hc
          exact hpoint a c
      _ = ∑ a : J, (memoryBPrime S.x F.q_d p)⁻¹ * ((p : ℝ) + 1)⁻¹ *
            ∑ c : J,
              (if a < c then
                if lam c = lam a then
                  eta a * eta c *
                    ∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
                      (1 - (if lam j = lam a then eta j else 0))
                else 0 else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
      _ = (memoryBPrime S.x F.q_d p)⁻¹ * ((p : ℝ) + 1)⁻¹ *
            ∑ a : J, ∑ c : J,
              (if a < c then
                if lam c = lam a then
                  eta a * eta c *
                    ∏ j ∈ Finset.univ.filter (fun j : J => a < j ∧ j < c),
                      (1 - (if lam j = lam a then eta j else 0))
                else 0 else 0) := by
          rw [Finset.mul_sum]

/-- Distribute the finite per-prime sums and remove the group tags using disjoint bands.
Guide runs/lanes/sol-thin-pdmem/PROOFS.md:402–417,449. Uses
pd_prime_lifespan_data and pd_lifecycle_parameters; feeds history_path_value. -/
theorem pd_prime_lifespan_product (K : ℕ) (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x → ∀ γ : EnvPath S.x K,
      pdLifeChargeSum F S γ = ∏ p ∈ markedPrimes S.x K F.a, pdPathLifespan F S γ p := by
  classical
  obtain ⟨x₀, hx₀, hParams⟩ := pd_lifecycle_parameters K F hF
  refine ⟨x₀, hx₀, ?_⟩
  intro S hx γ
  have hAtX := hParams S.x hx
  calc
    pdLifeChargeSum F S γ =
        ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), pdPathLifespan F S γ p.1 := by
      unfold pdLifeChargeSum pdLifeAssignmentCharge
      change (∑ H : (i : Fin K) →
          (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1,
          ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
            primeLifeCharge F S γ p.1 (H i p)) = _
      calc
        _ = ∏ i : Fin K,
              ∑ H_i : (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1,
                ∏ p : primeBand S.x (F.a i),
                  primeLifeCharge F S γ p.1 (H_i p) := by
            exact (Fintype.prod_sum
              (ι := Fin K)
              (κ := fun i : Fin K =>
                (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1)
              (R := ℝ)
              (f := fun i H_i =>
                ∏ p : primeBand S.x (F.a i), primeLifeCharge F S γ p.1 (H_i p))).symm
        _ = ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
              ∑ life : PrimeLife S γ p.1, primeLifeCharge F S γ p.1 life := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (Fintype.prod_sum
              (ι := primeBand S.x (F.a i))
              (κ := fun p : primeBand S.x (F.a i) => PrimeLife S γ p.1)
              (R := ℝ)
              (f := fun p life => primeLifeCharge F S γ p.1 life)).symm
        _ = ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
              pdPathLifespan F S γ p.1 := by
            apply Finset.prod_congr rfl
            intro i hi
            apply Finset.prod_congr rfl
            intro p hp
            exact pd_prime_lifespan_data F S γ p.1
    _ = ∏ i ∈ (Finset.univ : Finset (Fin K)),
          ∏ p ∈ primeBand S.x (F.a i), pdPathLifespan F S γ p := by
      simp [Finset.prod_attach]
    _ = ∏ p ∈ markedPrimes S.x K F.a, pdPathLifespan F S γ p := by
      have hPairwise : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin K)))
          (fun i => primeBand S.x (F.a i)) := by
        intro i hi i' hi' hii'
        exact hAtX.2.1 i i' hii'
      rw [show markedPrimes S.x K F.a =
        (Finset.univ : Finset (Fin K)).biUnion (fun i => primeBand S.x (F.a i)) by rfl,
        Finset.prod_biUnion hPairwise]

end
end ArtinPrimitiveRoots.TypeII.PD
