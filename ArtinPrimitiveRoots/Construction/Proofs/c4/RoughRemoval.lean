import ArtinPrimitiveRoots.Construction.Defs
import ArtinPrimitiveRoots.Construction.Proofs.c4.Density

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

set_option maxHeartbeats 1000000

open ArtinPrimitiveRoots.TypeII
open Classical

noncomputable def binPairSum (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ)
    (Ψ : ℝ → ℝ) (γ γ' : ℝ) : ℝ := by
  classical
  let qs : Finset ℕ :=
    ((primesUpTo (Real.rpow x γ') : Finset ℕ).filter
      (fun q => Real.rpow x γ < (q : ℝ)))
  let ms : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  exact ∑ q ∈ qs, ∑ m ∈ ms,
      if roughAbove m (Real.rpow x γ) then
        ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (Nat.mul m q) else 0

noncomputable def binPairUniverse (x e : ℝ) (J : ℕ) (γ : Fin (J + 1) → ℝ) :
    Finset (Fin J × (ℕ × ℕ)) :=
  ((Finset.univ : Finset (Fin J)).product
      ((primesUpTo (Real.rpow x e) : Finset ℕ).product
        (Finset.range (⌊2 * x⌋₊ + 1)))).filter fun v =>
    v.2.1 ∈ ((primesUpTo (Real.rpow x (γ v.1.succ)) : Finset ℕ).filter
      (fun q : ℕ => Real.rpow x (γ v.1.castSucc) < (q : ℝ)))

noncomputable def binPairWeight (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (J : ℕ) (γ : Fin (J + 1) → ℝ)
    (v : Fin J × (ℕ × ℕ)) : ℝ := by
  classical
  exact if roughAbove v.2.2 (Real.rpow x (γ v.1.castSucc)) then
    ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (v.2.2 * v.2.1) else 0

theorem binPairUniverse_sum_eq_bins (x e : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ)
    (a : Fin K → ℝ) (Ψ : ℝ → ℝ) (J : ℕ) (γ : Fin (J + 1) → ℝ)
    (hx : 1 ≤ x) (hγbounds : ∀ i, γ i ≤ e) :
    (∑ v ∈ binPairUniverse x e J γ,
      if roughAbove v.2.2 (Real.rpow x (γ v.1.castSucc)) then
        ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (v.2.2 * v.2.1) else 0) =
      ∑ j : Fin J, binPairSum x M c u K a Ψ (γ j.castSucc) (γ j.succ) := by
  classical
  let Q : Finset ℕ := primesUpTo (Real.rpow x e)
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let qset : Fin J → Finset ℕ := fun j =>
    (primesUpTo (Real.rpow x (γ j.succ))).filter
      (fun q => Real.rpow x (γ j.castSucc) < (q : ℝ))
  have hqsub : ∀ j, qset j ⊆ Q := by
    intro j q hq
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hupperPos : 0 < Real.rpow x (γ j.succ) := Real.rpow_pos_of_pos hxpos _
    have hup : Real.rpow x (γ j.succ) ≤ Real.rpow x e :=
      Real.rpow_le_rpow_of_exponent_le hx (hγbounds j.succ)
    exact primesUpTo_subset_of_le hupperPos.le hup (Finset.mem_filter.mp hq).1
  have hfilter : ∀ j, Q.filter (fun q => q ∈ qset j) = qset j := by
    intro j
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hq⟩
      exact hq
    · intro hq
      exact ⟨hqsub j hq, hq⟩
  have hExpand :
      (∑ v ∈ binPairUniverse x e J γ,
        if roughAbove v.2.2 (Real.rpow x (γ v.1.castSucc)) then
          ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (v.2.2 * v.2.1) else 0) =
      ∑ j : Fin J, ∑ q ∈ Q, ∑ m ∈ R,
        if q ∈ qset j then
          (if roughAbove m (Real.rpow x (γ j.castSucc)) then
            ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0)
        else 0 := by
    simp [binPairUniverse, Q, R, qset, Finset.sum_filter, Finset.sum_product]
  calc
    _ = ∑ j : Fin J, ∑ q ∈ Q.filter (fun q => q ∈ qset j),
        ∑ m ∈ R,
          if roughAbove m (Real.rpow x (γ j.castSucc)) then
            ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0 := by
      rw [hExpand]
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ q ∈ Q, ∑ m ∈ R,
            if q ∈ qset j then
              (if roughAbove m (Real.rpow x (γ j.castSucc)) then
                ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0)
            else 0) =
            ∑ q ∈ Q, (if q ∈ qset j then
              ∑ m ∈ R,
                if roughAbove m (Real.rpow x (γ j.castSucc)) then
                  ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0
              else 0) := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases hqmem : q ∈ qset j <;> simp [hqmem]
        _ = ∑ q ∈ Q.filter (fun q => q ∈ qset j),
              ∑ m ∈ R,
                if roughAbove m (Real.rpow x (γ j.castSucc)) then
                  ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0 := by
                rw [← Finset.sum_filter]
    _ = ∑ j : Fin J, ∑ q ∈ qset j,
        ∑ m ∈ R,
          if roughAbove m (Real.rpow x (γ j.castSucc)) then
            ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hfilter j]
    _ = ∑ j : Fin J, binPairSum x M c u K a Ψ (γ j.castSucc) (γ j.succ) := by
      rfl

theorem roughConstructionMass_le_binPairSums
    (x : ℝ) (M c : ℕ) (u : ℤ) (K : ℕ) (a : Fin K → ℝ) (Ψ : ℝ → ℝ)
    (b e : ℝ) (J : ℕ) (γ : Fin (J + 1) → ℝ)
    (hx : 2 ≤ x) (hb : 0 < b) (hbe : b < e) (he : e < 1 / 2) (hJ : 0 < J)
    (hγ0 : γ 0 = b) (hγend : γ (Fin.last J) = e)
    (hγbounds : ∀ i, b ≤ γ i ∧ γ i ≤ e)
    (hγstrict : ∀ i j, i.val < j.val → γ i < γ j)
    (hweight : ∀ d, 0 ≤ ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ d)
    (hsupport : ∀ d, ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ d ≠ 0 →
      x < (d : ℝ) ∧ (d : ℝ) < 2 * x) :
    ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
        (Real.rpow x b) ≤
      ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
          (Real.rpow x e) +
        ∑ j : Fin J, binPairSum x M c u K a Ψ
          (γ j.castSucc) (γ j.succ) := by
  classical
  let w : ℕ → ℝ := ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ
  let R : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let low : ℕ → Prop := fun d => ArtinPrimitiveRoots.TypeII.roughAbove d (Real.rpow x b)
  let high : ℕ → Prop := fun d => ArtinPrimitiveRoots.TypeII.roughAbove d (Real.rpow x e)
  let badPred : ℕ → Prop := fun d => low d ∧ ¬ high d ∧ 0 < w d
  let Bad : Finset ℕ := R.filter badPred
  have hxone : 1 ≤ x := by linarith
  have hcut : Real.rpow x b ≤ Real.rpow x e :=
    Real.rpow_le_rpow_of_exponent_le hxone hbe.le
  have hhighLow {d : ℕ} (hd : high d) : low d := by
    intro p hp hpd
    exact lt_of_le_of_lt hcut (hd p hp hpd)
  have hbadSum :
      (∑ d ∈ Bad, w d) = ∑ d ∈ R, if badPred d then w d else 0 := by
    unfold Bad
    rw [Finset.sum_filter]
  have hsplit :
      ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
          (Real.rpow x b) ≤
        ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
            (Real.rpow x e) + ∑ d ∈ Bad, w d := by
    rw [ArtinPrimitiveRoots.Construction.roughConstructionMass,
      ArtinPrimitiveRoots.Construction.roughConstructionMass, hbadSum]
    calc
      (∑ d ∈ R, if low d then w d else 0) ≤
          ∑ d ∈ R, ((if high d then w d else 0) + (if badPred d then w d else 0)) := by
            apply Finset.sum_le_sum
            intro d hd
            by_cases hlow : low d
            · by_cases hhi : high d
              · simp [hlow, hhi, badPred]
              · by_cases hpos : 0 < w d
                · simp [hlow, hhi, hpos, badPred]
                · have hzero : w d = 0 := le_antisymm (le_of_not_gt hpos) (hweight d)
                  simp [hlow, hhi, hpos, hzero, badPred]
            · have hhi : ¬ high d := by
                intro hhi
                exact hlow (hhighLow hhi)
              simp [hlow, hhi, badPred]
      _ = (∑ d ∈ R, if high d then w d else 0) +
          (∑ d ∈ R, if badPred d then w d else 0) := by
            rw [Finset.sum_add_distrib]
      _ = _ := by rw [← hbadSum]
  let Q : Finset ℕ := primesUpTo (Real.rpow x e)
  let mRange : Finset ℕ := Finset.range (⌊2 * x⌋₊ + 1)
  let P : Finset (Fin J × (ℕ × ℕ)) := binPairUniverse x e J γ
  let pairW : (Fin J × (ℕ × ℕ)) → ℝ :=
    fun v => binPairWeight x M c u K a Ψ J γ v
  have hpairNonneg : ∀ v ∈ P, 0 ≤ pairW v := by
    intro v hv
    dsimp [pairW, binPairWeight]
    split_ifs
    · exact hweight _
    · exact le_rfl
  have hWitness : ∀ d ∈ Bad, ∃ v : Fin J × (ℕ × ℕ),
      v ∈ P ∧ v.2.2 * v.2.1 = d ∧ pairW v = w d := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    rcases hd' with ⟨hdR, ⟨hLow, hNotHigh, hpos⟩⟩
    have hnotzero : w d ≠ 0 := ne_of_gt hpos
    obtain ⟨hdx, hd2x⟩ := hsupport d (by simpa [w] using hnotzero)
    have hdone : 1 < d := by
      have : (1 : ℝ) < (d : ℝ) := by linarith [hdx, hx]
      exact_mod_cast this
    obtain ⟨j, q, m, hq, hqdvd, hmEq, hfactor, hqlo, hqhi, hmrough⟩ :=
      ArtinPrimitiveRoots.Construction.Proofs.C4.minFac_bin_factorization
        hJ γ x b e (by linarith) hb hbe hγ0 hγend hγstrict d hdone hLow hNotHigh
    have hgamhi : γ j.succ ≤ e := (hγbounds j.succ).2
    have hpowhi : Real.rpow x (γ j.succ) ≤ Real.rpow x e :=
      Real.rpow_le_rpow_of_exponent_le hxone hgamhi
    have hqupperE : (q : ℝ) ≤ Real.rpow x e := hqhi.trans hpowhi
    have hqMemUpper : q ∈
        (ArtinPrimitiveRoots.TypeII.primesUpTo (Real.rpow x (γ j.succ)) : Finset ℕ) := by
      unfold ArtinPrimitiveRoots.TypeII.primesUpTo
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hqFloor : q ≤ ⌊Real.rpow x (γ j.succ)⌋₊ :=
          (Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith) _).le).2 hqhi
        omega
      · exact hq
    have hqSet : q ∈
        (ArtinPrimitiveRoots.TypeII.primesUpTo (Real.rpow x (γ j.succ)) : Finset ℕ).filter
          (fun q : ℕ => Real.rpow x (γ j.castSucc) < (q : ℝ)) :=
      Finset.mem_filter.mpr ⟨hqMemUpper, hqlo⟩
    have hqRpow : Real.rpow x e ≤ x := by
      change x ^ e ≤ x
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hxone (by linarith : e ≤ 1))
    have hq2x : (q : ℝ) ≤ 2 * x := by linarith [hqupperE, hqRpow]
    have hqR : q ∈ mRange := by
      apply Finset.mem_range.mpr
      have hqFloor : q ≤ ⌊2 * x⌋₊ := Nat.le_floor hq2x
      omega
    have hmle : m ≤ d := by rw [hmEq]; exact Nat.div_le_self d q
    have hm2x : (m : ℝ) ≤ 2 * x := by
      exact (Nat.cast_le.mpr hmle).trans (le_of_lt hd2x)
    have hmR : m ∈ mRange := by
      apply Finset.mem_range.mpr
      have hmFloor : m ≤ ⌊2 * x⌋₊ := Nat.le_floor hm2x
      omega
    let v : Fin J × (ℕ × ℕ) := (j, (q, m))
    have hqGlobal : q ∈ Q := by
      apply primesUpTo_subset_of_le
        (Real.rpow_pos_of_pos (by linarith : 0 < x) _).le hpowhi
      exact hqMemUpper
    have hvBase : v ∈ (Finset.univ : Finset (Fin J)).product (Q.product mRange) := by
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_univ j, Finset.mem_product.mpr ⟨hqGlobal, hmR⟩⟩
    have hvP : v ∈ P := by
      change v ∈ binPairUniverse x e J γ
      dsimp only [v]
      unfold binPairUniverse
      apply Finset.mem_filter.mpr
      exact ⟨hvBase, hqSet⟩
    have hvWeight : pairW v = w d := by
      change (if roughAbove m (Real.rpow x (γ j.castSucc)) then
        ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ (m * q) else 0) =
        ArtinPrimitiveRoots.Construction.conWeight x M c u K a Ψ d
      rw [if_pos hmrough, hfactor]
    exact ⟨v, hvP, by simpa [v] using hfactor.symm, hvWeight⟩
  classical
  choose wit hwitMem hwitProd hwitVal using hWitness
  let default : Fin J × (ℕ × ℕ) := (⟨0, hJ⟩, (0, 0))
  let f : ℕ → Fin J × (ℕ × ℕ) := fun d => if hd : d ∈ Bad then wit d hd else default
  have hInj : Set.InjOn f Bad := by
    intro d₁ hd₁ d₂ hd₂ hEq
    have hd₁' : d₁ ∈ Bad := by simpa using hd₁
    have hd₂' : d₂ ∈ Bad := by simpa using hd₂
    have hEq' : wit d₁ hd₁ = wit d₂ hd₂ := by
      simpa only [f, dif_pos hd₁', dif_pos hd₂'] using hEq
    have hprod := congrArg (fun v : Fin J × (ℕ × ℕ) => v.2.2 * v.2.1) hEq'
    rw [hwitProd d₁ hd₁, hwitProd d₂ hd₂] at hprod
    exact hprod
  have hMap : ∀ d ∈ Bad, f d ∈ P := by
    intro d hd
    dsimp [f]
    rw [dif_pos hd]
    exact hwitMem d hd
  have hWeightEq : ∀ d ∈ Bad, w d ≤ pairW (f d) := by
    intro d hd
    dsimp [f]
    rw [dif_pos hd]
    exact (hwitVal d hd).symm.le
  have hBadLePairs : (∑ d ∈ Bad, w d) ≤ ∑ v ∈ P, pairW v :=
    finite_sum_le_superset_of_injective Bad P f w pairW hInj hMap hWeightEq hpairNonneg
  have hPairTotal : (∑ v ∈ P, pairW v) =
      ∑ j : Fin J, binPairSum x M c u K a Ψ (γ j.castSucc) (γ j.succ) := by
    simpa [P, pairW, binPairWeight] using
      binPairUniverse_sum_eq_bins x e M c u K a Ψ J γ hxone (fun i => (hγbounds i).2)
  calc
    ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
        (Real.rpow x b) ≤
        ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
          (Real.rpow x e) + ∑ d ∈ Bad, w d := hsplit
    _ ≤ ArtinPrimitiveRoots.Construction.roughConstructionMass x M c u K a Ψ
          (Real.rpow x e) + ∑ j : Fin J, binPairSum x M c u K a Ψ
            (γ j.castSucc) (γ j.succ) := by rw [← hPairTotal]; linarith [hBadLePairs]

end ArtinPrimitiveRoots.Construction.Proofs.C4
