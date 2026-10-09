import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.TypeII.MarkedTransfer
import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PP.Results
import ArtinPrimitiveRoots.TypeII.Proofs.«R-PRIME».PrimeAdapters
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.SWAdapters
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.LowFrequency
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.WiderWindow
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.LowFrequencyAssembly
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.CountAdapters
import ArtinPrimitiveRoots.TypeII.Proofs.R_LOW.ReciprocalMass
import ArtinPrimitiveRoots.TypeII.Proofs.R_TYPEII.FamilyUniformization
import ArtinPrimitiveRoots.TypeII.Proofs.R_TYPEII.FrequencyGrowth
import ArtinPrimitiveRoots.TypeII.Proofs.R_TYPEII.IntervalEndpoints
import OAI.NumberTheory.PrimeGaps.Main
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveRemainder
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.MertensBounds
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.TruncatedSource
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.PhaseBounds
import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.ProxyAssembly

namespace ArtinPrimitiveRoots.TypeII.RoughProofs

open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PP

noncomputable def tupleFromList {j : ℕ} (l : List ℕ) (h : l.length = j) : Fin j → ℕ :=
  fun i => l.get (Fin.cast h.symm i)

theorem ofFn_tupleFromList {j : ℕ} (l : List ℕ) (h : l.length = j) :
    List.ofFn (tupleFromList l h) = l := by
  cases h
  rw [show tupleFromList l rfl = l.get from by
    funext i
    simp [tupleFromList]]
  exact List.ofFn_get l

theorem mem_boundedTuples_of_forall_le {j B : ℕ} (t : Fin j → ℕ)
    (ht : ∀ i, t i ≤ B) : t ∈ boundedTuples j B := by
  classical
  unfold boundedTuples
  refine Finset.mem_image.mpr ⟨fun i => ⟨t i, Nat.lt_succ_of_le (ht i)⟩,
    Finset.mem_univ _, ?_⟩
  funext i
  rfl

theorem tuple_product_perm_factors {j m : ℕ} (t : Fin j → ℕ)
    (ht : ∀ i, (t i).Prime) (hprod : (∏ i : Fin j, t i) = m) :
    List.Perm (List.ofFn t) m.primeFactorsList := by
  have hlistprod : (List.ofFn t).prod = m := by
    simpa only [List.prod_ofFn] using hprod
  have hprime : ∀ p ∈ List.ofFn t, p.Prime := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ht i
  exact Nat.primeFactorsList_unique hlistprod hprime

noncomputable def primeTupleFiber (j B m : ℕ) : Finset (Fin j → ℕ) :=
  (boundedTuples j B).filter fun t =>
    (∀ i, (t i).Prime) ∧ (∏ i : Fin j, t i) = m

theorem primeTupleFiber_card_le_factorial (j B m : ℕ) :
    (primeTupleFiber j B m).card ≤ j.factorial := by
  classical
  let l := m.primeFactorsList
  by_cases hj : j = l.length
  · subst j
    have himage : (primeTupleFiber l.length B m).image List.ofFn ⊆ l.permutations.toFinset := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨t, ht, rfl⟩
      rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
      have hperm := tuple_product_perm_factors t hprop.1 hprop.2
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
    calc
      _ = ((primeTupleFiber l.length B m).image List.ofFn).card := by
        symm
        exact Finset.card_image_of_injective _ List.ofFn_injective
      _ ≤ l.permutations.toFinset.card := Finset.card_le_card himage
      _ ≤ l.permutations.length := List.toFinset_card_le _
      _ = l.length.factorial := List.length_permutations _
      _ = l.length.factorial := rfl
  · have hempty : primeTupleFiber j B m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
      have hperm := tuple_product_perm_factors t hprop.1 hprop.2
      have hlen : j = l.length := by simpa [l] using hperm.length_eq
      exact hj hlen
    simp [hempty]

theorem primeTupleFiber_eq_empty_of_factor_length_ne {j B m : ℕ}
    (hj : j ≠ m.primeFactorsList.length) : primeTupleFiber j B m = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
  have hperm := tuple_product_perm_factors t hprop.1 hprop.2
  have hlen : j = m.primeFactorsList.length := by simpa using hperm.length_eq
  exact hj hlen

theorem primeTupleFiber_card_eq_factorial_of_squarefree
    (j B m : ℕ) (hm0 : m ≠ 0) (hmSq : Squarefree m)
    (hj : j = m.primeFactorsList.length)
    (hB : ∀ p ∈ m.primeFactorsList, p ≤ B) :
    (primeTupleFiber j B m).card = j.factorial := by
  classical
  subst j
  let l := m.primeFactorsList
  let P := l.permutations.toFinset
  have hn : l.Nodup := by simpa [l] using hmSq.nodup_primeFactorsList
  have hpermNodup : l.permutations.Nodup := List.nodup_permutations l hn
  have himage₁ : (primeTupleFiber l.length B m).image List.ofFn ⊆ P := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨t, ht, rfl⟩
    rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
    have hperm := tuple_product_perm_factors t hprop.1 hprop.2
    exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
  have himage₂ : P ⊆ (primeTupleFiber l.length B m).image List.ofFn := by
    intro q hq
    have hqperm : q ∈ l.permutations := List.mem_toFinset.mp hq
    have hperm : List.Perm q l := List.mem_permutations.mp hqperm
    have hlen : q.length = l.length := hperm.length_eq
    let t := tupleFromList q hlen
    have hlist : List.ofFn t = q := ofFn_tupleFromList q hlen
    have hprimeList : ∀ p ∈ q, p.Prime := by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (hperm.mem_iff.mp hp)
    have hprodList : q.prod = m := by
      calc
        q.prod = l.prod := hperm.prod_eq
        _ = m := by simpa [l] using Nat.prod_primeFactorsList hm0
    have htPrime : ∀ i, (t i).Prime := by
      intro i
      exact hprimeList _ (List.get_mem q (Fin.cast hlen.symm i))
    have htBound : ∀ i, t i ≤ B := by
      intro i
      have hqmem : q.get (Fin.cast hlen.symm i) ∈ q :=
        List.get_mem q (Fin.cast hlen.symm i)
      have hfactor : t i ∈ m.primeFactorsList := by
        simpa [t, tupleFromList, l] using hperm.mem_iff.mp hqmem
      exact hB (t i) hfactor
    have htProd : (∏ i : Fin l.length, t i) = m := by
      rw [← List.prod_ofFn, hlist]
      exact hprodList
    have htMem : t ∈ primeTupleFiber l.length B m := by
      unfold primeTupleFiber
      apply Finset.mem_filter.mpr
      exact ⟨mem_boundedTuples_of_forall_le t htBound, htPrime, htProd⟩
    exact Finset.mem_image.mpr ⟨t, htMem, hlist⟩
  have hImage : (primeTupleFiber l.length B m).image List.ofFn = P :=
    Finset.Subset.antisymm himage₁ himage₂
  calc
    (primeTupleFiber l.length B m).card =
        ((primeTupleFiber l.length B m).image List.ofFn).card := by
          symm
          exact Finset.card_image_of_injective _ List.ofFn_injective
    _ = P.card := congrArg Finset.card hImage
    _ = l.permutations.length := by
      dsimp [P]
      exact List.toFinset_card_of_nodup hpermNodup
    _ = l.length.factorial := List.length_permutations l
    _ = m.primeFactorsList.length.factorial := rfl

theorem prime_square_count_bound (Y M : ℝ) (hY : 2 ≤ Y) (hM : 0 ≤ M) :
    (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
        (fun (p : ℕ) => Y < (p : ℝ)),
      (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤ 4 * M / Y := by
  classical
  let k := ⌊Y⌋₊
  let N := max k (⌊Real.sqrt (2 * M)⌋₊ + 1)
  have hYpos : 0 < Y := by linarith
  have hkCast : (k : ℝ) ≤ Y := by
    dsimp [k]
    exact Nat.floor_le (by linarith)
  have hlt : Y < (k + 1 : ℝ) := by
    dsimp [k]
    exact Nat.lt_floor_add_one Y
  have hk0 : k ≠ 0 := by
    intro hk
    rw [hk] at hlt
    norm_num at hlt
    linarith
  have hsub :
      (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ)) ⊆
        Finset.Ioo k N := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp0, hYp⟩
    rcases Finset.mem_filter.mp hp0 with ⟨hpR, hpPrime⟩
    have hpRange : p < ⌊Real.sqrt (2 * M)⌋₊ + 1 := by
      simpa [primesUpTo] using hpR
    have hkp : k < p := by
      by_contra h
      have hp_le_k : p ≤ k := Nat.le_of_not_gt h
      have hpCast : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast hp_le_k
      linarith
    have hpN : p < N := by
      apply lt_of_lt_of_le hpRange
      exact le_max_right _ _
    exact Finset.mem_Ioo.mpr ⟨hkp, hpN⟩
  let S := (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ))
  let T := Finset.Ioo k N
  have hpoint :
      (∑ p ∈ S, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤
        ∑ p ∈ S, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp0, hYp⟩
    rcases Finset.mem_filter.mp hp0 with ⟨hpR, hpPrime⟩
    have hpPrime' : p.Prime := by simpa [primesUpTo] using hpPrime
    have hpPos : 0 < (p : ℝ) := by exact_mod_cast hpPrime'.pos
    have hden : 0 < (p : ℝ) ^ 2 := by positivity
    have hquot : 0 ≤ 2 * M / (p : ℝ) ^ 2 := by positivity
    have hfloor : (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ 2 * M / (p : ℝ) ^ 2 :=
      Nat.floor_le hquot
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfloor
  have hsubsetSum :
      (∑ p ∈ S, (2 * M) * ((p : ℝ) ^ 2)⁻¹) ≤
        ∑ p ∈ T, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (show S ⊆ T from hsub)
    intro p hp hpT
    positivity
  have hsum :
      (∑ p ∈ S, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) ≤
        ∑ p ∈ T, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := hpoint.trans hsubsetSum
  have htail := sum_Ioo_inv_sq_le (α := ℝ) k N
  have hscaled :
      ∑ p ∈ Finset.Ioo k N, (2 * M) * ((p : ℝ) ^ 2)⁻¹ ≤
        (2 * M) * (2 / (k + 1 : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have hden : (2 : ℝ) / (k + 1 : ℝ) ≤ 2 / Y :=
    div_le_div_of_nonneg_left (by norm_num) hYpos (le_of_lt hlt)
  calc
    _ ≤ ∑ p ∈ Finset.Ioo k N, (2 * M) * ((p : ℝ) ^ 2)⁻¹ := hsum
    _ ≤ (2 * M) * (2 / (k + 1 : ℝ)) := hscaled
    _ ≤ (2 * M) * (2 / Y) := mul_le_mul_of_nonneg_left hden (by positivity)
    _ = 4 * M / Y := by ring

end ArtinPrimitiveRoots.TypeII.RoughProofs

/-! The rough-factor Type II estimate and its coefficient (`08-type-ii.tex:321-536`). -/

namespace ArtinPrimitiveRoots.TypeII.Rough

open Classical
open MeasureTheory
open ContinuousLinearMap
open scoped Pointwise Topology Ring MulOpposite
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII.PP
open ArtinPrimitiveRoots.Proofs.RImplP.RPrime
open ArtinPrimitiveRoots.Proofs.RImplP.RLow

/-- `def:rough-density` — 08-type-ii.tex:253-270. Alias of the shared Buchstab rough density; the
body is exactly the existing `ArtinPrimitiveRoots.Sieve.roughDensity` definition. -/
noncomputable abbrev roughDensity := ArtinPrimitiveRoots.Sieve.roughDensity

/-- The coefficient in equation `eq:rough-type-ii-coefficient`. -/
noncomputable def roughCoefficient (x γ v : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
    (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
        roughDensity γ (Real.log (m : ℝ) / Real.log x) /
          (Real.log x * roughSieveProduct (roughCutoff x)) *
            (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)

/-- The prime-indicator coefficient `1_{P⁻(m)>x^γ}`. -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ :=
  if roughAbove m (Real.rpow x γ) then 1 else 0

/-- The proxy coefficient `D_γ(log m/log x)/(log x V(W))` on `W`-rough integers. -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ :=
  roughDensity γ (Real.log (m : ℝ) / Real.log x) /
    (Real.log x * roughSieveProduct (roughCutoff x)) *
      if roughAbove m (roughCutoff x) then 1 else 0

/-- The finite ordered-prime convolution `T_γ(m)` from `eq:rough-convolution-square-error`. -/
noncomputable def roughConvolutionTerm (x γ M : ℝ) (j m : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
      if (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m then 1 else 0

noncomputable def roughConvolution (x γ wMax M : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M j m

/-- Prime set in a closed real interval, explicitly truncated at the upper endpoint. -/
noncomputable def primesInInterval (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (⌊hi⌋₊ + 1)).filter fun p => p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi

/-- Product-measure integral over ordered `j`-tuples of primes in logarithmic coordinates. -/
noncomputable def roughTupleIntegral (x γ lo hi : ℝ) (j : ℕ) : ℝ :=
  (1 / (j.factorial : ℝ)) *
    ∫ t : Fin j → ℝ,
      if (∀ i, Real.rpow x γ < t i) ∧
          lo ≤ ∏ i : Fin j, t i ∧ (∏ i : Fin j, t i) ≤ hi then
        ∏ i : Fin j, 1 / Real.log (t i) else 0

set_option maxHeartbeats 1000000 in
private theorem roughCoefficient_phase_split
    (x γ v t : ℝ) (m : ℕ) (z : ℂ) :
    roughCoefficient x γ v m * z * Complex.exp (Complex.I * t * Real.log (m : ℝ)) =
      (roughIndicator x γ m : ℂ) * z *
          Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) -
        z * Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) *
          (roughProxy x γ m : ℂ) := by
  simp only [roughCoefficient, roughIndicator, roughProxy, Complex.ofReal_div,
    Complex.ofReal_mul]
  have he : Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
      Complex.exp (Complex.I * t * Real.log (m : ℝ)) =
        Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = ((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0 : ℝ) : ℂ) * z *
        (Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) -
        z * (Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) *
          (((roughDensity γ (Real.log (m : ℝ) / Real.log x) : ℝ) : ℂ) /
            (((Real.log x : ℝ) : ℂ) *
              ((roughSieveProduct (roughCutoff x) : ℝ) : ℂ)) *
                ((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
      ring
    _ = ((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0 : ℝ) : ℂ) * z *
        Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) -
        z * Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) *
          (((roughDensity γ (Real.log (m : ℝ) / Real.log x) : ℝ) : ℂ) /
            (((Real.log x : ℝ) : ℂ) *
              ((roughSieveProduct (roughCutoff x) : ℝ) : ℂ)) *
                ((if roughAbove m (roughCutoff x) then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
      rw [he]

theorem rough_factor_count_le (x γ wMax : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmx : (m : ℝ) ≤ Real.rpow x wMax) :
    m.primeFactorsList.length ≤ ⌊wMax / γ⌋₊ := by
  classical
  let l := m.primeFactorsList
  have hlne : l ≠ [] := by
    intro h
    have hm01 : m = 0 ∨ m = 1 := by
      apply (Nat.primeFactorsList_eq_nil m).mp
      simpa [l] using h
    omega
  have hlpos : 0 < l.length := List.length_pos_of_ne_nil hlne
  have hleft : (∏ i : Fin l.length, Real.rpow x γ) =
      (Real.rpow x γ) ^ l.length := by simp
  have hprodReal : (∏ i : Fin l.length, (l.get i : ℝ)) = (m : ℝ) := by
    calc
      (∏ i : Fin l.length, (l.get i : ℝ)) =
          ((∏ i : Fin l.length, l.get i : ℕ) : ℝ) := by simp
      _ = (l.prod : ℝ) := by
        norm_cast
        rw [← List.prod_ofFn, List.ofFn_get]
      _ = (m : ℝ) := by
        have hnat : l.prod = m := by
          dsimp [l]
          exact Nat.prod_primeFactorsList (by omega)
        exact_mod_cast hnat
  have hprodLower :
      (∏ i : Fin l.length, Real.rpow x γ) <
        ∏ i : Fin l.length, (l.get i : ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro i hi
      exact Real.rpow_pos_of_pos (by linarith) γ
    · intro i hi
      have hmem : l.get i ∈ l := List.get_mem l i
      have hfactor : l.get i ∈ m.primeFactorsList := by exact hmem
      have hpair : (l.get i).Prime ∧ l.get i ∣ m :=
        (Nat.mem_primeFactorsList (by omega : m ≠ 0)).mp hfactor
      exact hrough (l.get i) hpair.1 hpair.2
    · exact ⟨⟨0, hlpos⟩, Finset.mem_univ _⟩
  have hpowLt : (Real.rpow x γ) ^ l.length < Real.rpow x wMax := by
    calc
      _ = ∏ i : Fin l.length, Real.rpow x γ := hleft.symm
      _ < (m : ℝ) := hprodLower.trans_eq hprodReal
      _ ≤ Real.rpow x wMax := hmx
  have hpowEq : Real.rpow x (γ * (l.length : ℝ)) =
      (Real.rpow x γ) ^ l.length := by
    calc
      Real.rpow x (γ * (l.length : ℝ)) =
          (Real.rpow x γ) ^ (l.length : ℝ) := Real.rpow_mul (by positivity) γ _
      _ = (Real.rpow x γ) ^ l.length := Real.rpow_natCast _ _
  have hExp : Real.rpow x (γ * (l.length : ℝ)) < Real.rpow x wMax := by
    rw [hpowEq]
    exact hpowLt
  have hγlen : γ * (l.length : ℝ) < wMax :=
    (Real.rpow_lt_rpow_left_iff hx).mp hExp
  have hlenReal : (l.length : ℝ) < wMax / γ :=
    (lt_div_iff₀ hγ).2 (by nlinarith)
  have hlenNat : l.length ≤ ⌊wMax / γ⌋₊ := Nat.le_floor hlenReal.le
  simpa [l] using hlenNat

theorem roughConvolutionTerm_eq_tupleFiber (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m =
      (1 / (j.factorial : ℝ)) *
        (RoughProofs.primeTupleFiber j (⌊2 * M⌋₊ + 1) m).card := by
  classical
  let B := ⌊2 * M⌋₊ + 1
  let P : (Fin j → ℕ) → Prop := fun t =>
    ((∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
      (∏ i : Fin j, t i) = m)
  let Q : (Fin j → ℕ) → Prop := fun t =>
    (∀ i, (t i).Prime) ∧ (∏ i : Fin j, t i) = m
  have hPQ (t : Fin j → ℕ) : P t ↔ Q t := by
    constructor
    · rintro ⟨hp, hprod⟩
      exact ⟨fun i => (hp i).1, hprod⟩
    · rintro ⟨hp, hprod⟩
      refine ⟨?_, hprod⟩
      intro i
      refine ⟨hp i, ?_⟩
      have hdiv : t i ∣ m := by
        calc
          t i ∣ ∏ k : Fin j, t k :=
            Finset.dvd_prod_of_mem (fun k => t k) (Finset.mem_univ i)
          _ = m := hprod
      exact hrough (t i) (hp i) hdiv
  have hfilter : (boundedTuples j B).filter P =
      RoughProofs.primeTupleFiber j B m := by
    ext t
    simp only [Finset.mem_filter, RoughProofs.primeTupleFiber]
    constructor
    · rintro ⟨hB, hP⟩
      exact ⟨hB, (hPQ t).mp hP⟩
    · rintro ⟨hB, hQ⟩
      exact ⟨hB, (hPQ t).mpr hQ⟩
  unfold roughConvolutionTerm
  change (1 / (j.factorial : ℝ)) *
      (∑ t ∈ boundedTuples j B, if P t then (1 : ℝ) else 0) = _
  calc
    _ = (1 / (j.factorial : ℝ)) *
        ∑ t ∈ (boundedTuples j B).filter P, (1 : ℝ) := by
          congr 1
          exact (Finset.sum_filter (s := boundedTuples j B) P
            (fun _ => (1 : ℝ))).symm
    _ = _ := by rw [hfilter]; simp [B]


theorem roughConvolutionTerm_nonneg (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    0 ≤ roughConvolutionTerm x γ M j m := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  positivity

theorem roughConvolutionTerm_le_one (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m ≤ 1 := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  let F := RoughProofs.primeTupleFiber j (⌊2 * M⌋₊ + 1) m
  have hcard := RoughProofs.primeTupleFiber_card_le_factorial j
    (⌊2 * M⌋₊ + 1) m
  have hcardReal : (F.card : ℝ) ≤ (j.factorial : ℝ) := by
    exact_mod_cast hcard
  have hfact : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  calc
    (1 / (j.factorial : ℝ)) * (F.card : ℝ) =
        (F.card : ℝ) / (j.factorial : ℝ) := by ring
    _ ≤ 1 := (div_le_one hfact).2 hcardReal

theorem roughConvolutionTerm_eq_one_of_squarefree (x γ M : ℝ) (j m : ℕ)
    (hrough : roughAbove m (Real.rpow x γ)) (hm2 : 2 ≤ m)
    (hmSq : Squarefree m) (hj : j = m.primeFactorsList.length)
    (hB : ∀ p ∈ m.primeFactorsList, p ≤ ⌊2 * M⌋₊ + 1) :
    roughConvolutionTerm x γ M j m = 1 := by
  rw [roughConvolutionTerm_eq_tupleFiber x γ M j m hrough]
  rw [RoughProofs.primeTupleFiber_card_eq_factorial_of_squarefree j
    (⌊2 * M⌋₊ + 1) m (by omega) hmSq hj hB]
  field_simp

theorem roughConvolution_eq_one_of_rough_squarefree
    (x γ wMax M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm2 : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmUpper : (m : ℝ) ≤ 2 * M) (hScale : 2 * M ≤ Real.rpow x wMax)
    (hmSq : Squarefree m) :
    roughConvolution x γ wMax M m = 1 := by
  let j := m.primeFactorsList.length
  have hjLower : 1 ≤ j := by
    have hlist : m.primeFactorsList ≠ [] := by
      intro h
      have hm01 : m = 0 ∨ m = 1 := by
        apply (Nat.primeFactorsList_eq_nil m).mp
        exact h
      omega
    exact List.length_pos_of_ne_nil hlist
  have hjUpper : j ≤ ⌊wMax / γ⌋₊ :=
    rough_factor_count_le x γ wMax m hx hγ hm2 hrough (hmUpper.trans hScale)
  have hjMem : j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊) :=
    Finset.mem_Icc.mpr ⟨hjLower, hjUpper⟩
  have hB : ∀ p ∈ m.primeFactorsList, p ≤ ⌊2 * M⌋₊ + 1 := by
    intro p hp
    have hpDvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have hpLe : p ≤ m := Nat.le_of_dvd (by omega) hpDvd
    have hmFloor : m ≤ ⌊2 * M⌋₊ := Nat.le_floor hmUpper
    exact hpLe.trans (hmFloor.trans (Nat.le_succ _))
  have hterm : roughConvolutionTerm x γ M j m = 1 :=
    roughConvolutionTerm_eq_one_of_squarefree x γ M j m hrough hm2 hmSq
      (by rfl) hB
  have hzero : ∀ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), q ≠ j →
      roughConvolutionTerm x γ M q m = 0 := by
    intro q hq hqj
    rw [roughConvolutionTerm_eq_tupleFiber x γ M q m hrough]
    rw [RoughProofs.primeTupleFiber_eq_empty_of_factor_length_ne
      (by simpa [j] using hqj)]
    simp
  calc
    roughConvolution x γ wMax M m =
        ∑ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), roughConvolutionTerm x γ M q m := rfl
    _ = roughConvolutionTerm x γ M j m :=
      Finset.sum_eq_single_of_mem j hjMem hzero
    _ = 1 := hterm


theorem roughConvolutionTerm_eq_zero_of_not_rough (x γ M : ℝ) (j m : ℕ)
    (hnot : ¬ roughAbove m (Real.rpow x γ)) :
    roughConvolutionTerm x γ M j m = 0 := by
  classical
  unfold roughConvolutionTerm
  have hsum :
      (∑ t ∈ boundedTuples j (⌊2 * M⌋₊ + 1),
        if ((∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
            (∏ i : Fin j, t i) = m) then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    by_cases hpred :
        (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          (∏ i : Fin j, t i) = m
    · rcases hpred with ⟨hcoords, hprod⟩
      have hwitness : ∃ p, p.Prime ∧ p ∣ m ∧ ¬ Real.rpow x γ < (p : ℝ) := by
        by_contra h
        apply hnot
        intro p hp hpdiv
        by_contra hpnot
        exact h ⟨p, hp, hpdiv, hpnot⟩
      rcases hwitness with ⟨p, hp, hpdiv, hpnot⟩
      have hpDivProd : p ∣ ∏ i : Fin j, t i := by simpa [hprod] using hpdiv
      rcases (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) (fun i => t i)).mp hpDivProd with
        ⟨i, _, hpi⟩
      have heq : p = t i :=
        (Nat.prime_dvd_prime_iff_eq hp (hcoords i).1).mp hpi
      exact False.elim (hpnot (by simpa [heq] using (hcoords i).2))
    · simp only [if_neg hpred]
  rw [hsum]
  simp

theorem roughConvolution_bounds_of_rough
    (x γ wMax M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hm2 : 2 ≤ m)
    (hrough : roughAbove m (Real.rpow x γ))
    (hmUpper : (m : ℝ) ≤ 2 * M) (hScale : 2 * M ≤ Real.rpow x wMax) :
    0 ≤ roughConvolution x γ wMax M m ∧ roughConvolution x γ wMax M m ≤ 1 := by
  let j := m.primeFactorsList.length
  have hjLower : 1 ≤ j := by
    have hlist : m.primeFactorsList ≠ [] := by
      intro h
      have hm01 : m = 0 ∨ m = 1 := by
        apply (Nat.primeFactorsList_eq_nil m).mp h
      omega
    exact List.length_pos_of_ne_nil hlist
  have hjUpper : j ≤ ⌊wMax / γ⌋₊ :=
    rough_factor_count_le x γ wMax m hx hγ hm2 hrough (hmUpper.trans hScale)
  have hjMem : j ∈ Finset.Icc 1 (⌊wMax / γ⌋₊) :=
    Finset.mem_Icc.mpr ⟨hjLower, hjUpper⟩
  have hzero : ∀ q ∈ Finset.Icc 1 (⌊wMax / γ⌋₊), q ≠ j →
      roughConvolutionTerm x γ M q m = 0 := by
    intro q hq hqj
    rw [roughConvolutionTerm_eq_tupleFiber x γ M q m hrough]
    rw [RoughProofs.primeTupleFiber_eq_empty_of_factor_length_ne
      (by simpa [j] using hqj)]
    simp
  have hsum : roughConvolution x γ wMax M m = roughConvolutionTerm x γ M j m := by
    unfold roughConvolution
    exact Finset.sum_eq_single_of_mem j hjMem hzero
  constructor
  · rw [hsum]
    exact roughConvolutionTerm_nonneg x γ M j m hrough
  · rw [hsum]
    exact roughConvolutionTerm_le_one x γ M j m hrough

theorem dyadic_multiples_card_le_floor (M : ℝ) (hM : 1 ≤ M) (p : ℕ)
    (hp : p.Prime) :
    ((dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m)).card ≤
      ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
  classical
  let K := ⌊2 * M / (p : ℝ) ^ 2⌋₊
  let U := Finset.Ioc 0 K
  let f : ℕ → ℕ := fun n => p ^ 2 * n
  have hsubset :
      (dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m) ⊆ U.image f := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmD, hdiv⟩
    change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
      (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmD
    rcases Finset.mem_filter.mp hmD with ⟨_, ⟨hmLower, hmUpper⟩⟩
    rcases hdiv with ⟨n, hn⟩
    have hnpos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      simp [this] at hn
      have hmpos : 0 < m := by
        have hmcast : (1 : ℝ) ≤ (m : ℝ) := le_trans hM hmLower
        exact_mod_cast hmcast
      omega
    have hnBound : n ≤ K := by
      apply Nat.le_floor
      have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
      have hden : 0 < (p : ℝ) ^ 2 := by positivity
      have hcastEq : (m : ℝ) = (p : ℝ) ^ 2 * (n : ℝ) := by
        rw [hn]
        push_cast
        ring
      apply (le_div_iff₀ hden).2
      nlinarith [hcastEq]
    refine Finset.mem_image.mpr ⟨n, ?_, ?_⟩
    · exact Finset.mem_Ioc.mpr ⟨hnpos, hnBound⟩
    · dsimp [f]
      exact hn.symm
  calc
    ((dyadicIntegers M).filter (fun m => p ^ 2 ∣ m)).card ≤ (U.image f).card :=
      Finset.card_le_card hsubset
    _ ≤ U.card := Finset.card_image_le
    _ = K := by simp [U]

theorem roughBadDyadic_card_le_square_count (x γ M : ℝ) (hM : 1 ≤ M) :
    let Y := Real.rpow x γ
    let Bad := (dyadicIntegers M).filter
      (fun m => roughAbove m Y ∧ ¬ Squarefree m)
    Bad.card ≤
      (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter (fun (p : ℕ) => Y < (p : ℝ)),
        ⌊2 * M / (p : ℝ) ^ 2⌋₊) := by
  classical
  let Y := Real.rpow x γ
  let P : Finset ℕ := (primesUpTo (Real.sqrt (2 * M))).filter
    (fun (p : ℕ) => Y < (p : ℝ))
  let Bad : Finset ℕ := (dyadicIntegers M).filter
    (fun (m : ℕ) => roughAbove m Y ∧ ¬ Squarefree m)
  change Bad.card ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊
  have hsumBad : Bad.card ≤
      ∑ m ∈ Bad, ∑ p ∈ P, if p ^ 2 ∣ m then 1 else 0 := by
    calc
      Bad.card = ∑ m ∈ Bad, 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m hm
        have hmBad := (Finset.mem_filter.mp hm).2
        rcases hmBad with ⟨hmrough, hmnotSq⟩
        obtain ⟨p, hp, hpdiv⟩ : ∃ p, p.Prime ∧ p * p ∣ m := by
          by_contra h
          apply hmnotSq
          apply Nat.squarefree_iff_prime_squarefree.mpr
          intro p hp hdiv
          exact h ⟨p, hp, hdiv⟩
        have hmDy := (Finset.mem_filter.mp hm).1
        change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
          (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmDy
        rcases Finset.mem_filter.mp hmDy with ⟨_, ⟨hmLower, hmUpper⟩⟩
        have hmpos : 0 < m := by
          have hmcast : (1 : ℝ) ≤ (m : ℝ) := le_trans hM hmLower
          exact_mod_cast hmcast
        have hpSqNat : p * p ≤ m := Nat.le_of_dvd hmpos hpdiv
        have hpSqReal : (p : ℝ) ^ 2 ≤ 2 * M := by
          have hcast : ((p * p : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpSqNat
          rw [Nat.cast_mul] at hcast
          nlinarith
        have hpSqrt : (p : ℝ) ≤ Real.sqrt (2 * M) := Real.le_sqrt_of_sq_le hpSqReal
        have hpFloor : p ≤ ⌊Real.sqrt (2 * M)⌋₊ := Nat.le_floor hpSqrt
        have hpPrimeSet : p ∈ primesUpTo (Real.sqrt (2 * M)) := by
          unfold primesUpTo
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp⟩
          omega
        have hpDvd : p ∣ m := dvd_trans (dvd_mul_right p p) hpdiv
        have hpY : Y < (p : ℝ) := hmrough p hp hpDvd
        have hpP : p ∈ P := Finset.mem_filter.mpr ⟨hpPrimeSet, hpY⟩
        have hcount : 1 ≤ (P.filter (fun q => q ^ 2 ∣ m)).card := by
          apply Nat.succ_le_of_lt
          exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr
            ⟨hpP, by simpa [pow_two] using hpdiv⟩⟩
        have hcountsum :
            (∑ q ∈ P, if q ^ 2 ∣ m then 1 else 0) =
              (P.filter (fun q => q ^ 2 ∣ m)).card := by
          symm
          exact Finset.card_filter _ _
        rw [hcountsum]
        exact hcount
  calc
    Bad.card ≤ ∑ m ∈ Bad, ∑ p ∈ P, if p ^ 2 ∣ m then 1 else 0 := hsumBad
    _ = ∑ p ∈ P, ∑ m ∈ Bad, if p ^ 2 ∣ m then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ P, (Bad.filter (fun m => p ^ 2 ∣ m)).card := by
      apply Finset.sum_congr rfl
      intro p hp
      symm
      exact Finset.card_filter (fun m => p ^ 2 ∣ m) Bad
    _ ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := by
        rcases Finset.mem_filter.mp hp with ⟨hp₁, _⟩
        exact (Finset.mem_filter.mp hp₁).2
      have hsub : Bad.filter (fun (m : ℕ) => p ^ 2 ∣ m) ⊆
          (dyadicIntegers M).filter (fun (m : ℕ) => p ^ 2 ∣ m) := by
        intro m hm
        rcases Finset.mem_filter.mp hm with ⟨hmB, hmdiv⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmB).1, hmdiv⟩
      exact (Finset.card_le_card hsub).trans
        (dyadic_multiples_card_le_floor M hM p hpPrime)

theorem rough_square_error_pointwise (x γ wMax δ M : ℝ) (m : ℕ)
    (hx : 1 < x) (hγ : 0 < γ) (hδ : 0 < δ) (hM : 1 ≤ M)
    (hMδ : Real.rpow x δ ≤ M) (hScale : 2 * M ≤ Real.rpow x wMax)
    (hmDy : m ∈ dyadicIntegers M) :
    |roughIndicator x γ m - roughConvolution x γ wMax M m| ≤
      if roughAbove m (Real.rpow x γ) ∧ ¬ Squarefree m then 1 else 0 := by
  have hδpow : 1 < Real.rpow x δ := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx hδ
  have hMgt : 1 < M := lt_of_lt_of_le hδpow hMδ
  change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
    (fun (n : ℕ) => M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * M) at hmDy
  rcases Finset.mem_filter.mp hmDy with ⟨_, ⟨hmLower, hmUpper⟩⟩
  have hm2 : 2 ≤ m := by
    have hmReal : 1 < (m : ℝ) := lt_of_lt_of_le hMgt hmLower
    have hmNat : 1 < m := by exact_mod_cast hmReal
    omega
  by_cases hrough : roughAbove m (Real.rpow x γ)
  · by_cases hSq : Squarefree m
    · have hconv := roughConvolution_eq_one_of_rough_squarefree x γ wMax M m
        hx hγ hm2 hrough hmUpper hScale hSq
      have hind : roughIndicator x γ m = 1 := by
        unfold roughIndicator
        rw [if_pos hrough]
      rw [hind, hconv]
      have hrough' : roughAbove m (x ^ γ) := hrough
      simp [hrough', hSq]
    · have hconv := roughConvolution_bounds_of_rough x γ wMax M m
        hx hγ hm2 hrough hmUpper hScale
      have hdiff : |1 - roughConvolution x γ wMax M m| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hconv.2)]
        exact sub_le_self 1 hconv.1
      have hind : roughIndicator x γ m = 1 := by
        unfold roughIndicator
        rw [if_pos hrough]
      rw [hind]
      have hrough' : roughAbove m (x ^ γ) := hrough
      simpa [hrough', hSq] using hdiff
  · have hconv : roughConvolution x γ wMax M m = 0 := by
      unfold roughConvolution
      apply Finset.sum_eq_zero
      intro j hj
      exact roughConvolutionTerm_eq_zero_of_not_rough x γ M j m hrough
    have hind : roughIndicator x γ m = 0 := by
      unfold roughIndicator
      rw [if_neg hrough]
    rw [hind, hconv]
    have hrough' : ¬ roughAbove m (x ^ γ) := hrough
    simp [hrough']

/-- `t2:square-error` — 08-type-ii.tex:351-371. The dyad lies below `x^{wMax}` (`2M ≤ x^{wMax}`), which bounds the
number of prime factors by `Jγ`; added 2026-10-07 after lane `r2` refuted the form without it. -/
theorem square_error (γ wMax δ : ℝ) (hγ : 0 < γ) (hδ : 0 < δ)
    (hγw : γ < wMax) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 1 ≤ M → Real.rpow x δ ≤ M → 2 * M ≤ Real.rpow x wMax →
          let Jγ := ⌊wMax / γ⌋₊
          (∑ m ∈ dyadicIntegers M,
            |roughIndicator x γ m - roughConvolution x γ wMax M m|) ≤
              (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊) ∧
          (∑ p ∈ (primesUpTo (Real.sqrt (2 * M))).filter
                  (fun p => Real.rpow x γ < (p : ℝ)),
                ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) ≤ C * M * Real.rpow x (-γ) := by
  let x₀ : ℝ := max 2 (Real.exp (Real.log 2 / γ))
  refine ⟨4, x₀, by norm_num, le_max_left _ _, ?_⟩
  intro x hx M hM hMδ hScale
  have hx2 : 2 ≤ x := (le_max_left 2 _).trans hx
  have hx1 : 1 < x := by linarith
  let xCut : ℝ := Real.exp (Real.log 2 / γ)
  have hxCut : xCut ≤ x := (le_max_right 2 _).trans hx
  have hlogCut : Real.log 2 / γ ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hxCut
    simpa [xCut] using h
  have hlogMul : Real.log 2 ≤ γ * Real.log x := by
    have h := (div_le_iff₀ hγ).mp hlogCut
    nlinarith
  have hY2 : 2 ≤ Real.rpow x γ := by
    have hpow : Real.rpow x γ = Real.exp (Real.log x * γ) :=
      Real.rpow_def_of_pos (by linarith : 0 < x) γ
    calc
      2 = Real.exp (Real.log 2) := by rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (γ * Real.log x) := Real.exp_le_exp.mpr hlogMul
      _ = Real.rpow x γ := by rw [hpow]; congr 1; ring
  have hδpow : 1 < Real.rpow x δ := by
    rw [← Real.rpow_zero x]
    exact Real.rpow_lt_rpow_of_exponent_lt hx1 hδ
  have hMgt : 1 < M := lt_of_lt_of_le hδpow hMδ
  let Y := Real.rpow x γ
  let P : Finset ℕ := (primesUpTo (Real.sqrt (2 * M))).filter
    (fun (p : ℕ) => Y < (p : ℝ))
  let Q : Finset ℝ := ((primesUpTo (Real.sqrt (2 * M))).image
      (fun (p : ℕ) => (p : ℝ))).filter (fun p => Y < p)
  have hPMap : P.image (fun (p : ℕ) => (p : ℝ)) = Q := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
      rcases Finset.mem_filter.mp hq with ⟨hqPrime, hqY⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨q, hqPrime, rfl⟩, hqY⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpImage, hpY⟩
      rcases Finset.mem_image.mp hpImage with ⟨q, hqPrime, rfl⟩
      exact Finset.mem_image.mpr
        ⟨q, Finset.mem_filter.mpr ⟨hqPrime, hpY⟩, rfl⟩
  have hsumImage :
      (∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
        (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ)) =
      ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by
    apply Finset.sum_image
    intro a ha b hb hab
    exact Nat.cast_injective hab
  constructor
  · let Bad := (dyadicIntegers M).filter
      (fun m => roughAbove m Y ∧ ¬ Squarefree m)
    have hpoint : ∀ m ∈ dyadicIntegers M,
        |roughIndicator x γ m - roughConvolution x γ wMax M m| ≤
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0 := by
      intro m hm
      exact rough_square_error_pointwise x γ wMax δ M m hx1 hγ hδ hM hMδ hScale hm
    have hsumBad :
        (∑ m ∈ dyadicIntegers M,
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0) =
          (Bad.card : ℝ) := by
      calc
        _ = ∑ m ∈ Bad, (1 : ℝ) := by
          symm
          exact (Finset.sum_filter (s := dyadicIntegers M)
            (fun m => roughAbove m Y ∧ ¬ Squarefree m) (fun _ => (1 : ℝ)))
        _ = _ := by simp [Bad]
    have hbadNat := roughBadDyadic_card_le_square_count x γ M hM
    have hbadNat' : Bad.card ≤ ∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ := by
      simpa [Bad, P, Y] using hbadNat
    have hbadCast : (Bad.card : ℝ) ≤
        ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by
      calc
        _ ≤ ((∑ p ∈ P, ⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast hbadNat'
        _ = _ := by simp
    have hbadReal : (Bad.card : ℝ) ≤
        (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) := by
      calc
        _ ≤ ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hbadCast
        _ = ∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
            (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hsumImage.symm
        _ = _ := by rw [hPMap]
    have hsumQCast : (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) =
        ((∑ p ∈ Q, ⌊2 * M / p ^ 2⌋₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    have hbadRealNat : (Bad.card : ℝ) ≤
        ((∑ p ∈ Q, ⌊2 * M / p ^ 2⌋₊ : ℕ) : ℝ) := by
      calc
        _ ≤ ∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ) := hbadReal
        _ = _ := hsumQCast
    calc
      _ ≤ ∑ m ∈ dyadicIntegers M,
          if roughAbove m Y ∧ ¬ Squarefree m then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro m hm
            exact hpoint m hm
      _ = (Bad.card : ℝ) := hsumBad
      _ ≤ _ := by simpa [Bad, Y, Q] using hbadRealNat
  · have htail := RoughProofs.prime_square_count_bound
      (Real.rpow x γ) M hY2 (by linarith : 0 ≤ M)
    have hneg : Real.rpow x (-γ) = (Real.rpow x γ)⁻¹ := by
      change x ^ (-γ) = (x ^ γ)⁻¹
      exact Real.rpow_neg (by positivity : 0 ≤ x) γ
    have htailQ : (∑ p ∈ Q, (⌊2 * M / p ^ 2⌋₊ : ℝ)) ≤
        4 * M * Real.rpow x (-γ) := by
      calc
        _ = ∑ p ∈ P.image (fun (p : ℕ) => (p : ℝ)),
            (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := by rw [← hPMap]
        _ = ∑ p ∈ P, (⌊2 * M / (p : ℝ) ^ 2⌋₊ : ℝ) := hsumImage
        _ ≤ 4 * M / Real.rpow x γ := htail
        _ = 4 * M * Real.rpow x (-γ) := by rw [hneg]; ring
    simpa [Q, Y] using htailQ

set_option maxHeartbeats 2000000 in
/-- `t2:sw-slot` — 08-type-ii.tex:385-407, `eq:rough-slot-siegel-walfisz`. -/
theorem sw_slot (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₂ : ℝ, 0 < A₀ → 0 < A₂ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                P ≤ l → l ≤ r → r ≤ 2 * P →
                  ‖∑ p ∈ (primesInInterval l r),
                    (χ (p : ZMod k) : ℂ) -
                    (if χ = 1 then (1 : ℂ) else 0) *
                      (∫ y in l..r, (1 / Real.log y : ℝ) : ℂ)‖ ≤
                      C * P * Real.rpow (Real.log x) (-A₂) := by
  intro A₀ A₂ hA₀ hA₂
  let A_SW : ℝ := A₂ + 4
  obtain ⟨C_SW, x_SW, hC_SW, hx_SW, hSW⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.siegel_walfisz A_SW (A₀ + 1)
      (by dsimp [A_SW]; linarith) (by linarith)
  obtain ⟨x₀, hx₀, hthreshold⟩ :=
    ArtinPrimitiveRoots.Proofs.RImplP.RLow.sw_threshold γ A₀ A₂ x_SW hγ hA₀ hA₂
  let C_SW' : ℝ := 8 * C_SW * Real.rpow (γ / 2) (-A_SW) *
    Real.rpow (Real.log 4) (-4)
  let C : ℝ := C_SW' + 2
  refine ⟨C, x₀, ?_, hx₀, ?_⟩
  · dsimp [C, C_SW']
    positivity
  · intro x hx P hPlo hPup k hk hklog χ l r hPl hlr hr
    let L : ℝ := Real.log x
    let c : ℝ := γ / 2
    let d : ℕ := χ.conductor
    let ψ : DirichletCharacter ℂ d := χ.primitiveCharacter
    let ε : ℂ := if χ = 1 then 1 else 0
    let coeff (n : ℕ) : ℂ :=
      (ψ (n : ZMod d) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)
    let f (y : ℝ) : ℂ := ((Real.log y)⁻¹ : ℂ)
    let f' (y : ℝ) : ℂ := ((-y⁻¹ / (Real.log y) ^ 2 : ℝ) : ℂ)
    let E : ℝ := 2 * C_SW * Real.rpow c (-A_SW) * P * Real.rpow L (-A_SW)
    let Q : Finset ℕ := Finset.Ioc ⌊l⌋₊ ⌊r⌋₊
    let Qp : Finset ℕ := Q.filter Nat.Prime
    let Qn : Finset ℕ := Q.filter fun n => ¬ n.Prime
    have hx2 : 2 ≤ x := (hthreshold x hx).1
    have hXpos : 0 < x := by linarith
    have hLpos : 0 < L := by
      dsimp [L]
      exact Real.log_pos (by linarith)
    have hLne : L ≠ 0 := ne_of_gt hLpos
    rcases (hthreshold x hx).2.2.2.2.2.2 with ⟨hLγlog2, hLcInv, hLcPowInv, hL4⟩
    have hscaleData := hthreshold x hx
    rcases hscaleData with ⟨_, hY, hmod, hhalf, htail, hend, _⟩
    have hYleft : 2 * x_SW ≤ Real.rpow x γ := le_trans (le_max_left _ _) hY
    have hYfour : 4 ≤ Real.rpow x γ := le_trans (le_max_right _ _) hY
    have hPtwo : 2 ≤ P := by
      have hlow : 2 ≤ Real.rpow x γ / 2 :=
        (le_div_iff₀ (by norm_num)).2 (by nlinarith [hYfour])
      exact hlow.trans hPlo
    have hxSWP : x_SW ≤ P := by
      have hlow : x_SW ≤ Real.rpow x γ / 2 :=
        (le_div_iff₀ (by norm_num)).2 (by nlinarith [hYleft])
      exact hlow.trans hPlo
    have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
    letI : NeZero k := ⟨ne_of_gt hkpos⟩
    have hLpowlt : Real.rpow x (γ / 4) < Real.rpow x (γ / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    have hhalfSquare :
        Real.rpow x γ = Real.rpow x (γ / 2) * Real.rpow x (γ / 2) := by
      calc
        Real.rpow x γ = Real.rpow x (γ / 2 + γ / 2) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hXpos _ _
    have hhalfLe : Real.rpow x (γ / 2) ≤ Real.rpow x γ / 2 := by
      rw [hhalfSquare]
      nlinarith [hhalf]
    have hkP : (k : ℝ) < P := by
      have hkbound : (k : ℝ) ≤ Real.rpow x (γ / 4) := hklog.trans hmod
      exact (hkbound.trans_lt hLpowlt).trans_le (hhalfLe.trans hPlo)
    have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hPtwo
    have hPltwo : 2 ≤ l := hPtwo.trans hPl
    have hrTwo : 2 ≤ r := hPltwo.trans hlr
    have hrootX : 0 < Real.rpow x γ := Real.rpow_pos_of_pos hXpos γ
    have hscaleLog : Real.log (Real.rpow x γ / 2) = γ * L - Real.log 2 := by
      calc
        Real.log (Real.rpow x γ / 2) = Real.log (Real.rpow x γ) - Real.log 2 :=
          Real.log_div (ne_of_gt hrootX) (by norm_num)
        _ = γ * L - Real.log 2 := by
          have hlogX : Real.log (Real.rpow x γ) = γ * Real.log x :=
            Real.log_rpow hXpos γ
          simpa [L] using congrArg (fun z : ℝ => z - Real.log 2) hlogX
    have hlogP : c * L ≤ Real.log P := by
      have hlogMono := Real.log_le_log (by positivity) hPlo
      rw [hscaleLog] at hlogMono
      have hgammaL : 2 * Real.log 2 ≤ γ * L := by
        have h := (div_le_iff₀ hγ).mp hLγlog2
        simpa [L, mul_comm] using h
      have hhalfLog : c * L ≤ γ * L - Real.log 2 := by
        change (γ / 2) * L ≤ γ * L - Real.log 2
        nlinarith [hgammaL]
      exact hhalfLog.trans hlogMono
    have hcl : 1 ≤ c * L := by
      have hcpos' : 0 < γ / 2 := by positivity
      have h := (div_le_iff₀ hcpos').mp hLcInv
      simpa [L, c, mul_comm] using h
    have hlogBounds (y : ℝ) (hy : y ∈ Set.Icc l r) :
        c * L ≤ Real.log y ∧ 1 ≤ Real.log y ∧ Real.log y ≤ 2 * L := by
      have hPy : P ≤ y := hPl.trans hy.1
      have hy2P : y ≤ 2 * P := hy.2.trans hr
      have hlogPy : Real.log P ≤ Real.log y :=
        Real.log_le_log (by linarith [hPy, hPtwo]) hPy
      have hy4x : y ≤ 4 * x := by nlinarith [hy2P, hPup]
      have hlog4x : Real.log y ≤ Real.log (4 * x) :=
        Real.log_le_log (by linarith [hy4x, hPltwo]) hy4x
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hXpos)] at hlog4x
      have hlogLower := hlogP.trans hlogPy
      constructor
      · exact hlogLower
      constructor
      · exact hcl.trans hlogLower
      · dsimp [L]
        linarith [hlog4x, hL4]
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hLtoLog (y : ℝ) (hy : y ∈ Set.Icc l r) :
        Real.rpow L A₀ ≤ Real.rpow (Real.log y) (A₀ + 1) := by
      have hlogy := hlogBounds y hy
      have hcPowPos : 0 < Real.rpow c (A₀ + 1) := Real.rpow_pos_of_pos hcpos _
      have hfactor : 1 ≤ Real.rpow c (A₀ + 1) * L := by
        have h := (div_le_iff₀ hcPowPos).mp hLcPowInv
        nlinarith [h]
      have hLpowNonneg : 0 ≤ Real.rpow L A₀ := Real.rpow_nonneg hLpos.le _
      have hbase : Real.rpow L A₀ ≤ Real.rpow (c * L) (A₀ + 1) := by
        calc
          Real.rpow L A₀ ≤ Real.rpow L A₀ * (Real.rpow c (A₀ + 1) * L) :=
            by simpa using mul_le_mul_of_nonneg_left hfactor hLpowNonneg
          _ = Real.rpow c (A₀ + 1) * (Real.rpow L A₀ * L) := by ring
          _ = Real.rpow c (A₀ + 1) * Real.rpow L (A₀ + 1) := by
            change Real.rpow c (A₀ + 1) * (L ^ A₀ * L) =
              Real.rpow c (A₀ + 1) * L ^ (A₀ + 1)
            rw [Real.rpow_add hLpos A₀ 1, Real.rpow_one]
          _ = Real.rpow (c * L) (A₀ + 1) := by
            exact (Real.mul_rpow hcpos.le hLpos.le).symm
      exact hbase.trans (Real.rpow_le_rpow (by positivity) hlogy.1 (by linarith))
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.pos_of_dvd_of_pos χ.conductor_dvd_level hkpos
    have hdkNat : d ≤ k := by
      dsimp [d]
      exact Nat.le_of_dvd hkpos χ.conductor_dvd_level
    have hdlog (y : ℝ) (hy : y ∈ Set.Icc l r) :
        (d : ℝ) ≤ Real.rpow (Real.log y) (A₀ + 1) := by
      calc
        (d : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdkNat
        _ ≤ Real.rpow L A₀ := hklog
        _ ≤ Real.rpow (Real.log y) (A₀ + 1) := hLtoLog y hy
    have hψprim : ψ.IsPrimitive := by
      dsimp [ψ, d]
      exact χ.primitiveCharacter_isPrimitive
    have hprincipal (y : ℝ) :
        (if ψ = 1 then (y : ℂ) else 0) = ε * (y : ℂ) := by
      change (if χ.primitiveCharacter = 1 then (y : ℂ) else 0) = _
      rw [ArtinPrimitiveRoots.Proofs.RImplP.RLow.primitive_eq_one_iff k hk χ]
      by_cases hχ : χ = 1 <;> simp [ε, hχ]
    have hEpos : 0 < E := by
      dsimp [E]
      positivity
    have hprefix : ∀ y ∈ Set.Icc l r,
        ‖(∑ n ∈ Finset.Icc 0 ⌊y⌋₊, coeff n) - ε * (y : ℂ)‖ ≤ E := by
      intro y hy
      have hyxSW : x_SW ≤ y := hxSWP.trans (hPl.trans hy.1)
      have hSWy := hSW y hyxSW d hdpos (hdlog y hy) ψ hψprim
      have hIccRange : Finset.Icc 0 ⌊y⌋₊ = Finset.range (⌊y⌋₊ + 1) := by
        ext n
        simp
      have hprefixSW :
          ‖(∑ n ∈ Finset.Icc 0 ⌊y⌋₊, coeff n) - ε * (y : ℂ)‖ ≤
            C_SW * y * Real.rpow (Real.log y) (-A_SW) := by
        simpa only [coeff, hIccRange, hprincipal y] using hSWy
      have hlogy := hlogBounds y hy
      have hpowlog : Real.rpow (Real.log y) (-A_SW) ≤
          Real.rpow c (-A_SW) * Real.rpow L (-A_SW) := by
        calc
          _ ≤ Real.rpow (c * L) (-A_SW) :=
            Real.rpow_le_rpow_of_nonpos (mul_pos hcpos hLpos) hlogy.1 (by linarith [hA₂])
          _ = _ := Real.mul_rpow hcpos.le hLpos.le
      have hy2P : y ≤ 2 * P := hy.2.trans hr
      have hpowNonneg : 0 ≤ Real.rpow (Real.log y) (-A_SW) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith [hPltwo, hy.1])) _
      calc
        _ ≤ C_SW * y * Real.rpow (Real.log y) (-A_SW) := hprefixSW
        _ ≤ C_SW * (2 * P) *
              (Real.rpow c (-A_SW) * Real.rpow L (-A_SW)) := by
                calc
                  _ ≤ C_SW * (2 * P) * Real.rpow (Real.log y) (-A_SW) :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hy2P hC_SW.le) hpowNonneg
                  _ ≤ _ := mul_le_mul_of_nonneg_left hpowlog (by positivity)
        _ = E := by dsimp [E]; ring
    have hf (y : ℝ) (hy : y ∈ Set.Icc l r) : HasDerivAt f (f' y) y := by
      have hy2 : 2 ≤ y := hPltwo.trans hy.1
      simpa [f, f'] using
        ArtinPrimitiveRoots.Proofs.RImplP.RLow.inv_log_complex_hasDerivAt y hy2
    have hf'cont : ContinuousOn f' (Set.Icc l r) := by
      have hlogcont : ContinuousOn Real.log (Set.Icc l r) :=
        Real.continuousOn_log.mono (by
          intro y hy
          exact (ne_of_gt (lt_of_lt_of_le (by positivity) (hPltwo.trans hy.1))))
      have hinv : ContinuousOn (fun y : ℝ => y⁻¹) (Set.Icc l r) :=
        continuousOn_inv₀.mono (by
          intro y hy
          exact (ne_of_gt (lt_of_lt_of_le (by positivity) (hPltwo.trans hy.1))))
      have hlogsq : ContinuousOn (fun y : ℝ => (Real.log y) ^ 2) (Set.Icc l r) :=
        hlogcont.pow 2
      have hquot := hinv.div hlogsq (by
        intro y hy
        exact ne_of_gt (pow_pos (Real.log_pos (by linarith [hPltwo.trans hy.1])) 2))
      have hrealFun : (fun y : ℝ => -y⁻¹ / (Real.log y) ^ 2) =
          (fun y => -(y⁻¹ / (Real.log y) ^ 2)) := by
        funext y
        ring
      have hreal : ContinuousOn (fun y : ℝ => -y⁻¹ / (Real.log y) ^ 2)
          (Set.Icc l r) := by
        rw [hrealFun]
        exact hquot.neg
      change ContinuousOn
        (fun y : ℝ => ((-y⁻¹ / (Real.log y) ^ 2 : ℝ) : ℂ)) (Set.Icc l r)
      exact Complex.continuous_ofReal.comp_continuousOn hreal
    have hfBound (y : ℝ) (hy : y ∈ Set.Icc l r) : ‖f y‖ ≤ 1 := by
      have hlogy := hlogBounds y hy
      have hlogpos : 0 < Real.log y := Real.log_pos (by linarith [hPltwo.trans hy.1])
      have hval : 0 ≤ 1 / Real.log y := by positivity
      have hvalle : 1 / Real.log y ≤ 1 :=
        (div_le_iff₀ hlogpos).2 (by linarith)
      have hnorm : ‖f y‖ = 1 / Real.log y := by
        simp [f, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogpos,
          one_div]
      rw [hnorm]
      exact hvalle
    have hf'Bound (y : ℝ) (hy : y ∈ Set.Icc l r) : ‖f' y‖ ≤ 1 / P := by
      have hlogy := hlogBounds y hy
      have hyP : P ≤ y := hPl.trans hy.1
      have h2y : 2 ≤ y := hPltwo.trans hy.1
      have hypos : 0 < y := by linarith
      have hlogpos : 0 < Real.log y := Real.log_pos (by linarith)
      have hlogsq : 1 ≤ (Real.log y) ^ 2 := by nlinarith [hlogy.2.1]
      have hinvP : y⁻¹ ≤ P⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hPpos hyP
      have hquot : y⁻¹ / (Real.log y) ^ 2 ≤ y⁻¹ := by
        apply (div_le_iff₀ (pow_pos hlogpos 2)).2
        have hyinv : 0 ≤ y⁻¹ := by positivity
        nlinarith [hyinv, hlogsq]
      have hnorm : ‖f' y‖ = y⁻¹ / (Real.log y) ^ 2 := by
        simp only [f', Complex.norm_real, Real.norm_eq_abs]
        have hyInvPos : 0 < y⁻¹ := inv_pos.mpr hypos
        have hdenPos : 0 < (Real.log y) ^ 2 := pow_pos hlogpos 2
        have hnonpos : -y⁻¹ / (Real.log y) ^ 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hyInvPos.le) hdenPos.le
        rw [abs_of_nonpos hnonpos]
        ring
      rw [hnorm]
      exact hquot.trans (by simpa [one_div] using hinvP)
    have hAbel := ArtinPrimitiveRoots.Proofs.RImplP.RLow.complex_partial_summation_error
      coeff f f' ε (by linarith [hPltwo]) hlr hf hf'cont hfBound hf'Bound
      (by norm_num) (by positivity) hprefix
    have hlength : 0 ≤ r - l := sub_nonneg.mpr hlr
    have hlengthDiv : (r - l) / P ≤ 2 := by
      apply (div_le_iff₀ hPpos).2
      nlinarith [hr, hPl]
    have hAbel4 :
        ‖(∑ n ∈ Q, f n * coeff n) - ε * (∫ y in l..r, f y)‖ ≤ 4 * E := by
      have hmain := hAbel
      have hmul : E * (2 * 1 + (1 / P) * (r - l)) ≤ 4 * E := by
        have hterm : (1 / P) * (r - l) ≤ 2 := by
          simpa [div_eq_mul_inv, mul_comm] using hlengthDiv
        nlinarith [hEpos, hterm]
      simpa [Q, one_div, mul_comm, mul_left_comm, mul_assoc] using hAbel.trans hmul
    have hlogR : Real.log r ≤ 2 * L := (hlogBounds r ⟨hlr, le_rfl⟩).2.2
    have htailAll :
        (∑ n ∈ Finset.Ioc 0 ⌊r⌋₊ with ¬n.Prime,
          ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) ≤
          2 * Real.sqrt r * Real.log r / Real.log 2 :=
      ArtinPrimitiveRoots.Proofs.RImplP.RLow.nonprime_vonMangoldt_div_log_bound r hrTwo
    have hQnSubset : Qn ⊆
        (Finset.Ioc 0 ⌊r⌋₊).filter fun n => ¬n.Prime := by
      intro n hn
      rcases Finset.mem_filter.mp hn with ⟨hnQ, hnnp⟩
      rcases Finset.mem_Ioc.mp hnQ with ⟨hnl, hnr⟩
      have hn0 : 0 < n := by omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hn0, hnr⟩, hnnp⟩
    have hratioNonneg (n : ℕ)
        (hn : n ∈ (Finset.Ioc 0 ⌊r⌋₊).filter fun n => ¬n.Prime) :
        0 ≤ ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) := by
      have hnpos : 1 ≤ n := by
        have h := (Finset.mem_filter.mp hn).1
        exact (Finset.mem_Ioc.mp h).1
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.log_nonneg (by exact_mod_cast hnpos))
    have htailQ :
        (∑ n ∈ Qn, ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) ≤
          2 * Real.sqrt r * Real.log r / Real.log 2 := by
      calc
        _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊r⌋₊).filter fun n => ¬n.Prime,
              ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hQnSubset (by
            intro n hn _hn'
            exact hratioNonneg n hn)
        _ ≤ _ := htailAll
    have hQnTerm (n : ℕ) (hn : n ∈ Qn) :
        ‖f n * coeff n‖ ≤ ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) := by
      rcases Finset.mem_filter.mp hn with ⟨hnQ, _⟩
      rcases Finset.mem_Ioc.mp hnQ with ⟨hnl, _⟩
      have hncast : l < (n : ℝ) := by
        have hsucc : ⌊l⌋₊ + 1 ≤ n := Nat.succ_le_of_lt hnl
        have hfloor : l < ((⌊l⌋₊ + 1 : ℕ) : ℝ) := by
          push_cast
          exact Nat.lt_floor_add_one l
        exact hfloor.trans_le (by exact_mod_cast hsucc)
      have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith [hPltwo])
      have hratio : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlogpos.le
      have hlogComplex : (Real.log (n : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hlogpos)
      have heq : f n * coeff n =
          (ψ (n : ZMod d) : ℂ) *
            ((ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ) := by
        simp only [f, coeff]
        rw [← Complex.ofReal_inv, Complex.ofReal_div, div_eq_mul_inv,
          ← Complex.ofReal_inv]
        ac_rfl
      rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hratio]
      calc
        ‖ψ (n : ZMod d)‖ * (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) ≤
            1 * (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one ψ (n : ZMod d))
            hratio
        _ = _ := by ring
    have hnonprimeNorm : ‖∑ n ∈ Qn, f n * coeff n‖ ≤
        2 * Real.sqrt r * Real.log r / Real.log 2 := by
      calc
        _ ≤ ∑ n ∈ Qn, ‖f n * coeff n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Qn, ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) :=
          Finset.sum_le_sum fun n hn => hQnTerm n hn
        _ ≤ _ := htailQ
    have hrootX4 :
        Real.rpow x (γ / 4) * Real.rpow x (γ / 4) = Real.rpow x (γ / 2) := by
      change x ^ (γ / 4) * x ^ (γ / 4) = x ^ (γ / 2)
      rw [← Real.rpow_add hXpos]
      congr 1
      ring
    have hPgeHalf : Real.rpow x (γ / 2) ≤ P := by
      have ha : 0 ≤ Real.rpow x (γ / 2) := Real.rpow_nonneg hXpos.le _
      have hsquare : Real.rpow x (γ / 2) * Real.rpow x (γ / 2) =
          Real.rpow x γ := hhalfSquare.symm
      nlinarith [hhalf, hPlo]
    have hrootP : Real.rpow x (γ / 4) ≤ Real.sqrt P := by
      have hqnonneg : 0 ≤ Real.rpow x (γ / 4) := Real.rpow_nonneg hXpos.le _
      have hsqrt : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
      have hqSq : (Real.rpow x (γ / 4)) ^ 2 = Real.rpow x (γ / 2) := by
        nlinarith [hrootX4]
      have hqSqP : (Real.rpow x (γ / 4)) ^ 2 ≤ P := hqSq ▸ hPgeHalf
      nlinarith [Real.sq_sqrt (le_of_lt hPpos)]
    have htailCoeff :
        (4 * Real.sqrt 2 / Real.log 2) * Real.rpow L (A₂ + 1) ≤ Real.sqrt P := by
      have hpowNonneg : 0 ≤ Real.rpow L (A₂ + 1) := Real.rpow_nonneg hLpos.le _
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcoef : 4 * Real.sqrt 2 / Real.log 2 ≤ Real.sqrt 2 * (8 / Real.log 2) := by
        have hlt : 4 * Real.sqrt 2 ≤ 8 * Real.sqrt 2 := by
          nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
        calc
          4 * Real.sqrt 2 / Real.log 2 ≤ (8 * Real.sqrt 2) / Real.log 2 :=
            div_le_div_of_nonneg_right hlt hlog2pos.le
          _ = Real.sqrt 2 * (8 / Real.log 2) := by ring
      have htail' :
          (Real.sqrt 2 * (8 / Real.log 2)) * Real.rpow L (A₂ + 1) ≤
            Real.rpow x (γ / 4) := by simpa [L] using htail
      exact (mul_le_mul_of_nonneg_right hcoef hpowNonneg).trans (htail'.trans hrootP)
    have htailBound : 2 * Real.sqrt r * Real.log r / Real.log 2 ≤
        P * Real.rpow L (-A₂) := by
      have hrootr : Real.sqrt r ≤ Real.sqrt (2 * P) := Real.sqrt_le_sqrt (by linarith [hr, hPl])
      have hlogrpos : 0 ≤ Real.log r := Real.log_nonneg (by linarith [hrTwo])
      have hlogr : Real.log r ≤ 2 * L := hlogR
      have hLpow : Real.rpow L (A₂ + 1) = Real.rpow L A₂ * L := by
        change L ^ (A₂ + 1) = L ^ A₂ * L
        rw [Real.rpow_add hLpos A₂ 1, Real.rpow_one]
      have hsmall :
          (4 * Real.sqrt 2 / Real.log 2) * Real.rpow L (A₂ + 1) ≤ Real.sqrt P := htailCoeff
      have hweighted :
          (4 * Real.sqrt 2 / Real.log 2) * Real.sqrt P * L ≤
            P * Real.rpow L (-A₂) := by
        have hsmall' := mul_le_mul_of_nonneg_right hsmall
          (mul_nonneg (Real.sqrt_nonneg P) (Real.rpow_nonneg hLpos.le (-A₂)))
        rw [hLpow] at hsmall'
        have hneg : Real.rpow L A₂ * Real.rpow L (-A₂) = 1 := by
          change L ^ A₂ * L ^ (-A₂) = 1
          rw [← Real.rpow_add hLpos]
          norm_num
        have hsqrtP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt (le_of_lt hPpos)
        have hleft :
            (4 * Real.sqrt 2 / Real.log 2) *
              (Real.rpow L A₂ * L) * (Real.sqrt P * Real.rpow L (-A₂)) =
              (4 * Real.sqrt 2 / Real.log 2) * Real.sqrt P * L := by
          calc
            _ = (4 * Real.sqrt 2 / Real.log 2) * Real.sqrt P * L *
                  (Real.rpow L A₂ * Real.rpow L (-A₂)) := by ring
            _ = _ := by rw [hneg]; ring
        calc
          _ = (4 * Real.sqrt 2 / Real.log 2) *
                (Real.rpow L A₂ * L) * (Real.sqrt P * Real.rpow L (-A₂)) := hleft.symm
          _ ≤ Real.sqrt P * (Real.sqrt P * Real.rpow L (-A₂)) := hsmall'
          _ = P * Real.rpow L (-A₂) := by
            calc
              _ = (Real.sqrt P * Real.sqrt P) * Real.rpow L (-A₂) := by ring
              _ = _ := by rw [hsqrtP]
      calc
        _ ≤ 2 * Real.sqrt (2 * P) * (2 * L) / Real.log 2 := by
          gcongr
        _ = (4 * Real.sqrt 2 / Real.log 2) * Real.sqrt P * L := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) P]
          ring
        _ ≤ _ := hweighted
    have hQunion : Qp ∪ Qn = Q := by
      ext n
      by_cases hn : n.Prime <;> simp [Qp, Qn, hn]
    have hQdisj : Disjoint Qp Qn := by
      rw [Finset.disjoint_left]
      intro n hp hn
      exact (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hp).2
    have hdecomp :
        (∑ n ∈ Q, f n * coeff n) =
          (∑ n ∈ Qp, f n * coeff n) + (∑ n ∈ Qn, f n * coeff n) := by
      calc
        _ = ∑ n ∈ Qp ∪ Qn, f n * coeff n := by conv_lhs => rw [← hQunion]
        _ = _ := Finset.sum_union hQdisj
    have hprimeTerm (p : ℕ) (hp : p ∈ Qp) :
        f p * coeff p = (ψ (p : ZMod d) : ℂ) := by
      rcases Finset.mem_filter.mp hp with ⟨hpQ, hprime⟩
      rcases Finset.mem_Ioc.mp hpQ with ⟨hpl, _⟩
      have hfloor : l < (p : ℝ) := by
        have hsucc : ⌊l⌋₊ + 1 ≤ p := Nat.succ_le_of_lt hpl
        have hfloor' : l < ((⌊l⌋₊ + 1 : ℕ) : ℝ) := by
          push_cast
          exact Nat.lt_floor_add_one l
        exact hfloor'.trans_le (by exact_mod_cast hsucc)
      have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith [hPltwo])
      have hlogComplex : ((Real.log (p : ℝ) : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt hlogpos)
      calc
        f p * coeff p =
            (ψ (p : ZMod d) : ℂ) *
              ((Real.log (p : ℝ) : ℂ)⁻¹ * (Real.log (p : ℝ) : ℂ)) := by
          simp only [f, coeff, ArithmeticFunction.vonMangoldt_apply_prime hprime,
            Complex.ofReal_mul]
          ac_rfl
        _ = ψ (p : ZMod d) := by rw [inv_mul_cancel₀ hlogComplex]; simp
    have hprimeOpen :
        (∑ n ∈ Qp, f n * coeff n) =
          ∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
            (ψ (p : ZMod d) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hprimeTerm p hp
    have hopenTransfer :
        (∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
          (ψ (p : ZMod d) : ℂ)) =
        ∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
          (χ (p : ZMod k) : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpI, hpprime⟩
      rcases Finset.mem_Ioc.mp hpI with ⟨hfloorl, _⟩
      have hsucc : ⌊l⌋₊ + 1 ≤ p := Nat.succ_le_of_lt hfloorl
      have hfloor : l < (p : ℝ) := by
        have hlt : l < ((⌊l⌋₊ + 1 : ℕ) : ℝ) := by
          push_cast
          exact Nat.lt_floor_add_one l
        exact hlt.trans_le (by exact_mod_cast hsucc)
      have hkpR : (k : ℝ) < (p : ℝ) :=
        lt_trans (lt_of_lt_of_le hkP hPl) hfloor
      have hkp : k < p := by exact_mod_cast hkpR
      have hcop : Nat.Coprime p k :=
        ArtinPrimitiveRoots.Proofs.RImplP.RLow.prime_coprime_of_lt hpprime hk hkp
      have heval := ArtinPrimitiveRoots.Proofs.RImplP.RLow.primitive_eval_nat k p hk χ hcop
      simpa only [Int.cast_natCast] using heval
    have hopenErr :
        ‖(∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
              (χ (p : ZMod k) : ℂ)) - ε * (∫ y in l..r, f y)‖ ≤
          4 * E + P * Real.rpow L (-A₂) := by
      have hsub :
          ‖((∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
                (χ (p : ZMod k) : ℂ)) - ε * (∫ y in l..r, f y))‖ ≤
            ‖(∑ n ∈ Q, f n * coeff n) - ε * (∫ y in l..r, f y)‖ +
            ‖∑ n ∈ Qn, f n * coeff n‖ := by
        calc
          _ = ‖((∑ n ∈ Q, f n * coeff n) - ε * (∫ y in l..r, f y)) -
                (∑ n ∈ Qn, f n * coeff n)‖ := by
                  congr 1
                  rw [hdecomp, hprimeOpen, hopenTransfer]
                  abel
          _ ≤ _ := norm_sub_le _ _
      have hnonprimeNorm' := hnonprimeNorm.trans htailBound
      exact hsub.trans (add_le_add hAbel4 hnonprimeNorm')
    have hendAbsorb : 1 ≤ P * Real.rpow L (-A₂) := by
      have hpow : Real.rpow L A₂ ≤ P := by
        have hp2 := hPlo
        have : Real.rpow x γ / 2 ≥ Real.rpow L A₂ := by linarith [hend]
        exact this.trans hPlo
      have hinv : Real.rpow L A₂ * Real.rpow L (-A₂) = 1 := by
        change L ^ A₂ * L ^ (-A₂) = 1
        rw [← Real.rpow_add hLpos]
        norm_num
      rw [← hinv]
      exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hLpos.le _)
    have hSWabsorb : 4 * E ≤ C_SW' * P * Real.rpow L (-A₂) := by
      have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
      have hlog4pow :
          Real.rpow L (-4) ≤ Real.rpow (Real.log 4) (-4) :=
        Real.rpow_le_rpow_of_nonpos hlog4pos hL4 (by norm_num)
      have hlog4powPow : L ^ (-4 : ℝ) ≤ (Real.log 4) ^ (-4 : ℝ) := by
        simpa only [Real.rpow_eq_pow] using hlog4pow
      have hpowSplit : Real.rpow L (-A_SW) =
          Real.rpow L (-A₂) * Real.rpow L (-4) := by
        have hexp : (-A_SW : ℝ) = (-A₂ : ℝ) + (-4 : ℝ) := by
          dsimp [A_SW]
          ring
        calc
          _ = Real.rpow L ((-A₂ : ℝ) + (-4 : ℝ)) := by rw [hexp]
          _ = _ := Real.rpow_add hLpos (-A₂) (-4)
      have hpowSplitPow : L ^ (-A_SW : ℝ) =
          L ^ (-A₂ : ℝ) * L ^ (-4 : ℝ) := by
        simpa only [Real.rpow_eq_pow] using hpowSplit
      dsimp [E, C_SW']
      dsimp [c]
      rw [hpowSplitPow]
      calc
        _ = (8 * C_SW * Real.rpow (γ / 2) (-A_SW) * P *
              Real.rpow L (-A₂)) * Real.rpow L (-4) := by
                simp only [Real.rpow_eq_pow]
                ring_nf
        _ ≤ (8 * C_SW * Real.rpow (γ / 2) (-A_SW) * P *
              Real.rpow L (-A₂)) * (Real.log 4) ^ (-4 : ℝ) := by
                apply mul_le_mul_of_nonneg_left hlog4powPow
                have hCpow : 0 ≤ Real.rpow (γ / 2) (-A_SW) :=
                  Real.rpow_nonneg (by positivity) _
                have hLpow : 0 ≤ Real.rpow L (-A₂) := Real.rpow_nonneg hLpos.le _
                exact mul_nonneg
                  (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8)
                    hC_SW.le) hCpow) hPpos.le) hLpow
        _ = _ := by
          simp only [Real.rpow_eq_pow]
          ring_nf
    have hclosedSplit := ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval_sum_split
      (fun p => (χ (p : ZMod k) : ℂ)) l r (by linarith [hrTwo])
    have hclosedBound :
        ‖∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval l r \
            ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
            (χ (p : ZMod k) : ℂ)‖ ≤ 1 := by
      let T := ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval l r \
        ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r
      have hcard := ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval_sdiff_card_le_one
        l r (by linarith [hPltwo]) (by linarith [hrTwo])
      calc
        _ ≤ ∑ p ∈ T, ‖(χ (p : ZMod k) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ T, (1 : ℝ) := Finset.sum_le_sum fun p hp =>
          DirichletCharacter.norm_le_one χ (p : ZMod k)
        _ = (T.card : ℝ) := by simp [T]
        _ ≤ 1 := by exact_mod_cast hcard
    have hclosedError :
        ‖(∑ p ∈ primesInInterval l r, (χ (p : ZMod k) : ℂ)) -
            ε * (∫ y in l..r, f y)‖ ≤
          (C_SW' + 2) * P * Real.rpow L (-A₂) := by
      change ‖(∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval l r,
          (χ (p : ZMod k) : ℂ)) - ε * (∫ y in l..r, f y)‖ ≤ _
      rw [hclosedSplit]
      calc
        _ = ‖((∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
                (χ (p : ZMod k) : ℂ)) - ε * (∫ y in l..r, f y)) +
              (∑ p ∈ ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeInterval l r \
                ArtinPrimitiveRoots.Proofs.RImplP.RLow.swPrimeOpenInterval l r,
                (χ (p : ZMod k) : ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
        _ ≤ (4 * E + P * Real.rpow L (-A₂)) + 1 :=
          add_le_add hopenErr hclosedBound
        _ ≤ (C_SW' * P * Real.rpow L (-A₂) + P * Real.rpow L (-A₂)) +
            P * Real.rpow L (-A₂) :=
          add_le_add (add_le_add hSWabsorb le_rfl) hendAbsorb
        _ = _ := by ring
    simpa [C, C_SW', ε, f, one_div, mul_assoc, mul_left_comm, mul_comm] using hclosedError

/-- The simplex defining a higher density term is empty below its natural support. -/
private theorem roughDensityTerm_eq_zero_of_lt (γ w : ℝ) {j : ℕ} (hγ : 0 < γ)
    (hj : 2 ≤ j) (hw : w < (j : ℝ) * γ) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1]
  have hempty :
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro ht
    have hs : ((j - 1 : ℕ) : ℝ) * γ ≤ ∑ i, t i := by
      calc
        ((j - 1 : ℕ) : ℝ) * γ = ∑ _i : Fin (j - 1), γ := by simp
        _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht.1 i
    have hjcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
    have : (j : ℝ) * γ ≤ w := by nlinarith [ht.2]
    exact (not_lt_of_ge this) hw
  simp [hempty]

/-- Above the support threshold, the defining density series has a finite truncation. -/
private theorem roughDensity_eq_sum_upto (γ w : ℝ) (hγ : 0 < γ) (hw : γ < w) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊w / γ⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊w / γ⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊w / γ⌋₊ + 1 ≤ j := by simpa using hj
    have hwγ : 1 < w / γ := (lt_div_iff₀ hγ).2 (by simpa using hw)
    have hfloor : 1 ≤ ⌊w / γ⌋₊ := Nat.le_floor (by exact_mod_cast hwγ.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : w / γ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (w / γ)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hfloorlt

/-- A common finite truncation works for every `w` in a bounded interval above `γ`. -/
private theorem roughDensity_eq_sum_bounded (γ w W : ℝ) (hγ : 0 < γ)
    (hγW : γ < W) (hwW : w ≤ W) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊W / γ⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊W / γ⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊W / γ⌋₊ + 1 ≤ j := by simpa using hj
    have hWγ : 1 < W / γ := (lt_div_iff₀ hγ).2 (by simpa using hγW)
    have hfloor : 1 ≤ ⌊W / γ⌋₊ := Nat.le_floor (by exact_mod_cast hWγ.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : W / γ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (W / γ)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    have hwr : w / γ ≤ W / γ := div_le_div_of_nonneg_right hwW hγ.le
    have hwγ : w / γ < (j : ℝ) := hwr.trans_lt hfloorlt
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hwγ

/-- A finite truncation uniform over all parameters with `γ` bounded below. -/
private theorem roughDensity_eq_sum_uniform (γ w W γ₀ : ℝ) (hγ : 0 < γ)
    (hγ₀ : 0 < γ₀) (hγ₀γ : γ₀ ≤ γ) (hγW : γ < W) (hwW : w ≤ W) :
    ArtinPrimitiveRoots.Sieve.roughDensity γ w =
      ∑ j ∈ Finset.range (⌊W / γ₀⌋₊ + 1),
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j := by
  classical
  unfold ArtinPrimitiveRoots.Sieve.roughDensity
  exact tsum_eq_sum (s := Finset.range (⌊W / γ₀⌋₊ + 1)) fun j hj => by
    have hjbound : ⌊W / γ₀⌋₊ + 1 ≤ j := by simpa using hj
    have hγ₀W : γ₀ < W := lt_of_le_of_lt hγ₀γ hγW
    have hWγ₀ : 1 < W / γ₀ := (lt_div_iff₀ hγ₀).2 (by simpa using hγ₀W)
    have hfloor : 1 ≤ ⌊W / γ₀⌋₊ := Nat.le_floor (by exact_mod_cast hWγ₀.le)
    have hj2 : 2 ≤ j := by omega
    have hfloorlt : W / γ₀ < (j : ℝ) := by
      have h := Nat.lt_floor_add_one (W / γ₀)
      exact lt_of_lt_of_le h (by exact_mod_cast hjbound)
    have hWpos : 0 < W := hγ₀.trans hγ₀W
    have hWratio : W / γ ≤ W / γ₀ :=
      div_le_div_of_nonneg_left hWpos.le hγ₀ hγ₀γ
    have hwratio : w / γ ≤ W / γ := div_le_div_of_nonneg_right hwW hγ.le
    have hwγ : w / γ < (j : ℝ) := (hwratio.trans hWratio).trans_lt hfloorlt
    apply roughDensityTerm_eq_zero_of_lt γ w hγ hj2
    exact (div_lt_iff₀ hγ).1 hwγ

/-- A finite product preserves a uniform Lipschitz estimate when every factor is bounded. -/
private theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (B K d : ℝ) (hB : 1 ≤ B) (hK : 0 ≤ K) (hd : 0 ≤ d)
    (f g : ι → ℝ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hfg : ∀ i ∈ S, |f i - g i| ≤ K * d) :
    |∏ i ∈ S, f i - ∏ i ∈ S, g i| ≤ (S.card : ℝ) * K * d * B ^ (S.card - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfA := hf a (Finset.mem_insert_self a S)
    have hgA := hg a (Finset.mem_insert_self a S)
    have hfgA := hfg a (Finset.mem_insert_self a S)
    have hfS : ∀ i ∈ S, |f i| ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS : ∀ i ∈ S, |g i| ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfgS : ∀ i ∈ S, |f i - g i| ≤ K * d := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have hprodF : |∏ i ∈ S, f i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        ∏ i ∈ S, |f i| ≤ ∏ _i ∈ S, B :=
          Finset.prod_le_prod₀ (fun i hi => abs_nonneg _) (fun i hi => hfS i hi)
        _ = B ^ S.card := by simp
    calc
      |∏ i ∈ insert a S, f i - ∏ i ∈ insert a S, g i|
          = |(f a - g a) * (∏ i ∈ S, f i) + g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)| := by
              simp only [Finset.prod_insert ha]
              congr 1
              ring
      _ ≤ |f a - g a| * |∏ i ∈ S, f i| + |g a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| := by
          calc
            _ = ‖(f a - g a) * (∏ i ∈ S, f i) + g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ := by
              rw [Real.norm_eq_abs]
            _ ≤ ‖(f a - g a) * (∏ i ∈ S, f i)‖ +
                  ‖g a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)‖ := norm_add_le _ _
            _ = _ := by simp [Real.norm_eq_abs, Finset.abs_prod, abs_mul]
      _ ≤ K * d * B ^ S.card + B * ((S.card : ℝ) * K * d * B ^ (S.card - 1)) := by
          apply add_le_add
          · calc
              _ ≤ K * d * |∏ i ∈ S, f i| := mul_le_mul_of_nonneg_right hfgA (abs_nonneg _)
              _ ≤ K * d * B ^ S.card := by gcongr
          · calc
              _ ≤ B * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| :=
                mul_le_mul_of_nonneg_right hgA (abs_nonneg _)
              _ ≤ B * ((S.card : ℝ) * K * d * B ^ (S.card - 1) : ℝ) := by
                gcongr
                exact ih hfS hgS hfgS
      _ = ((insert a S).card : ℝ) * K * d * B ^ ((insert a S).card - 1) := by
          rw [Finset.card_insert_of_notMem ha]
          by_cases hm : S.card = 0
          · simp [hm]
          · have hmpos : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hm
            have hp : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hmpos
            have hpow : B * B ^ (S.card - 1) = B ^ S.card := by
              calc
                B * B ^ (S.card - 1) = B ^ (S.card - 1) * B := mul_comm _ _
                _ = B ^ (S.card - 1 + 1) := (pow_succ B (S.card - 1)).symm
                _ = B ^ S.card := by rw [hp]
            have hcard : S.card + 1 - 1 = S.card := by omega
            rw [hcard, Nat.cast_add, Nat.cast_one]
            calc
              _ = K * d * B ^ S.card +
                    (S.card : ℝ) * K * d * (B * B ^ (S.card - 1)) := by ring
              _ = K * d * B ^ S.card + (S.card : ℝ) * K * d * B ^ S.card := by rw [hpow]
              _ = ((S.card : ℝ) + 1) * K * d * B ^ S.card := by ring

/-- The standard simplex for the rescaling `tᵢ = γ + s yᵢ`. -/
private def unitSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

private theorem isCompact_unitSimplex (n : ℕ) : IsCompact (unitSimplex n) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hclosed : IsClosed (unitSimplex n) := by
    have h₁ : IsClosed {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i))
    have h₂ : IsClosed {y : Fin n → ℝ | ∑ i, y i ≤ 1} :=
      isClosed_le (by fun_prop) continuous_const
    simpa only [unitSimplex, Set.setOf_and] using h₁.inter h₂
  apply IsCompact.of_isClosed_subset hbox hclosed
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_and, Set.mem_Icc]
  intro i
  intro _
  constructor
  · exact hy.1 i
  · have hsingle : y i ≤ ∑ k, y k :=
      Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ i)
    exact hsingle.trans hy.2

private def affineSimplexMap (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => γ + s * y i

private noncomputable def simplexKernel (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  (γ + s * (1 - ∑ i, y i))⁻¹ * ∏ i, (γ + s * y i)⁻¹

private theorem simplex_affine_image (γ s : ℝ) {n : ℕ} (hs : 0 < s) :
    {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} =
      affineSimplexMap γ s '' unitSimplex n := by
  ext t
  constructor
  · intro ht
    refine ⟨fun i => (t i - γ) / s, ?_, ?_⟩
    · constructor
      · intro i
        exact div_nonneg (sub_nonneg.mpr (ht.1 i)) hs.le
      · have hsum :
            (∑ i : Fin n, (t i - γ) / s) = ((∑ i : Fin n, t i) - (n : ℝ) * γ) / s := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
          simp
        rw [hsum, div_le_iff₀ hs]
        nlinarith [ht.2]
    · funext i
      dsimp [affineSimplexMap]
      field_simp [ne_of_gt hs]
      ring
  · rintro ⟨y, hy, rfl⟩
    constructor
    · intro i
      dsimp [affineSimplexMap]
      nlinarith [mul_nonneg hs.le (hy.1 i)]
    · have hsum :
          (∑ i : Fin n, (γ + s * y i)) = (n : ℝ) * γ + s * ∑ i : Fin n, y i := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      change (∑ i : Fin n, (γ + s * y i)) ≤ (n : ℝ) * γ + s
      rw [hsum]
      nlinarith [mul_le_mul_of_nonneg_left hy.2 hs.le]

/-- Rescale a higher density term onto a fixed unit simplex. -/
private theorem term_affine_simplex (γ s : ℝ) (j : ℕ) (hj : 2 ≤ j) (hs : 0 < s) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ + s) j =
      (1 / (j.factorial : ℝ)) * s ^ (j - 1) *
        ∫ y in unitSimplex (j - 1), simplexKernel γ s y := by
  let n : ℕ := j - 1
  have hn1 : 1 ≤ n := by dsimp [n]; omega
  have hn0 : n ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  let w : ℝ := (j : ℝ) * γ + s
  let S := unitSimplex n
  let F : (Fin n → ℝ) → (Fin n → ℝ) := affineSimplexMap γ s
  let c : Fin n → ℝ := fun _ => γ
  let scale : (Fin n → ℝ) → (Fin n → ℝ) := fun y => s • y
  let trans : (Fin n → ℝ) → (Fin n → ℝ) := fun z => z + c
  have hF : F = trans ∘ scale := by
    funext y
    ext i
    simp [F, affineSimplexMap, trans, scale, c, Pi.smul_apply]
    ring
  have hD : {t : Fin n → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} =
      trans '' (scale '' S) := by
    calc
      _ = F '' S := simplex_affine_image γ s hs
      _ = trans '' (scale '' S) := by
        calc
          _ = (trans ∘ scale) '' S := congrArg (fun f => f '' S) hF
          _ = trans '' (scale '' S) := (Set.image_image trans scale S).symm
  have hjcast : (j : ℝ) = (n : ℝ) + 1 := by
    dsimp [n]
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
  have hupper : (j : ℝ) * γ + s - γ = (n : ℝ) * γ + s := by
    rw [hjcast]
    ring
  have hDmeas : MeasurableSet {t : Fin n → ℝ |
      (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (n : ℝ) * γ + s} := by
    have h₁ : MeasurableSet {t : Fin n → ℝ | ∀ i, γ ≤ t i} := by
      simpa only [Set.iInter_ofPred] using
        (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    have h₂ : MeasurableSet {t : Fin n → ℝ | ∑ i, t i ≤ (n : ℝ) * γ + s} :=
      measurableSet_le (by fun_prop) measurable_const
    simpa only [Set.setOf_and] using h₁.inter h₂
  have hSmeas : MeasurableSet S := by
    have h₁ : MeasurableSet {y : Fin n → ℝ | ∀ i, 0 ≤ y i} := by
      simpa only [Set.iInter_ofPred] using
        (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i))
    have h₂ : MeasurableSet {y : Fin n → ℝ | ∑ i, y i ≤ 1} :=
      measurableSet_le (by fun_prop) measurable_const
    change MeasurableSet ({y : Fin n → ℝ | ∀ i, 0 ≤ y i} ∩
      {y : Fin n → ℝ | ∑ i, y i ≤ 1})
    exact h₁.inter h₂
  have hmp : MeasurePreserving trans volume volume := by
    refine ⟨by fun_prop, ?_⟩
    exact map_add_right_eq_self volume c
  have hemb : MeasurableEmbedding trans :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  let hk : (Fin n → ℝ) → ℝ := fun t => (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1, hupper]
  rw [integral_indicator hDmeas]
  rw [hD]
  simp only [one_div]
  have hshift := hmp.setIntegral_image_emb hemb hk (scale '' S)
  simp only [hk] at hshift
  rw [hshift]
  have hscale := Measure.setIntegral_comp_smul_of_pos volume (fun z => hk (trans z)) S hs
  have hfin : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hfin, smul_eq_mul] at hscale
  have hscaleSet : scale '' S = s • S := by rfl
  have hscale' :
      (∫ z in scale '' S, hk (trans z)) = s ^ n * ∫ y in S, hk (trans (scale y)) := by
    rw [hscaleSet]
    calc
      _ = s ^ n * ((s ^ n)⁻¹ * ∫ z in s • S, hk (trans z)) := by
        field_simp [ne_of_gt (pow_pos hs n)]
      _ = s ^ n * ∫ y in S, hk (trans (scale y)) := by
        rw [hscale]
  rw [hscale']
  have hker : ∀ y ∈ S, hk (trans (scale y)) = simplexKernel γ s y := by
    intro y hy
    have hsum : (∑ i : Fin n, (s * y i + γ)) = (n : ℝ) * γ + s * ∑ i, y i := by
      calc
        _ = ∑ i : Fin n, (γ + s * y i) := Finset.sum_congr rfl fun i _ => by ring
        _ = (n : ℝ) * γ + s * ∑ i, y i := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [hk, trans, scale, c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    dsimp [w]
    rw [hjcast]
    congr 2 <;> ring
  rw [setIntegral_congr_fun hSmeas hker]
  ring

/-- At the support boundary, the defining simplex collapses to a null singleton. -/
private theorem roughDensityTerm_eq_zero_at_support (γ : ℝ) (j : ℕ) (hj : 2 ≤ j) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ) j = 0 := by
  have hj0 : j ≠ 0 := by omega
  have hj1 : j ≠ 1 := by omega
  have hn1 : 1 ≤ j - 1 := by omega
  have hjcast : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega)).symm
  have hupper : (j : ℝ) * γ - γ = ((j - 1 : ℕ) : ℝ) * γ := by
    rw [hjcast]
    ring
  let c : Fin (j - 1) → ℝ := fun _ => γ
  have hD :
      {t : Fin (j - 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ (j : ℝ) * γ - γ} = {c} := by
    ext t
    constructor
    · intro ht
      have hsumLower : ((j - 1 : ℕ) : ℝ) * γ ≤ ∑ i, t i := by
        calc
          ((j - 1 : ℕ) : ℝ) * γ = ∑ _i : Fin (j - 1), γ := by simp
          _ ≤ ∑ i, t i := Finset.sum_le_sum fun i _ => ht.1 i
      have hsumGap : ∑ i : Fin (j - 1), (t i - γ) = 0 := by
        have hsum : ∑ i : Fin (j - 1), (t i - γ) = ∑ i : Fin (j - 1), t i - ((j - 1 : ℕ) : ℝ) * γ := by
          rw [Finset.sum_sub_distrib]
          simp
        rw [hsum]
        rw [hupper] at ht
        nlinarith [ht.2, hsumLower]
      have hcoord : ∀ i, t i = γ := by
        intro i
        have hgap : 0 ≤ t i - γ := sub_nonneg.mpr (ht.1 i)
        have hle : t i - γ ≤ ∑ k : Fin (j - 1), (t k - γ) :=
          Finset.single_le_sum (fun k _ => sub_nonneg.mpr (ht.1 k)) (Finset.mem_univ i)
        nlinarith [hsumGap, hgap, hle]
      ext i
      exact hcoord i
    · intro ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      constructor
      · intro i
        exact le_rfl
      · have hsum : ∑ i : Fin (j - 1), γ = ((j - 1 : ℕ) : ℝ) * γ := by simp
        rw [hupper]
        exact le_of_eq hsum
  have hnull : volume ({c} : Set (Fin (j - 1) → ℝ)) = 0 := by
    haveI : Nonempty (Fin (j - 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin (j - 1) → ℝ) := inferInstance
    simp
  rw [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_neg hj0, if_neg hj1]
  rw [hD]
  rw [integral_indicator (MeasurableSet.singleton c)]
  rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure]
  simp

/-- A globally continuous kernel agreeing with the simplex kernel for nonnegative scale. -/
private noncomputable def simplexSafeFactor (γ a s : ℝ) : ℝ :=
  (max γ (γ + s * a))⁻¹

private noncomputable def simplexKernelSafe (γ s : ℝ) {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  simplexSafeFactor γ (1 - ∑ i, y i) s * ∏ i, simplexSafeFactor γ (y i) s

private theorem simplexSafeFactor_abs_le {γ a s : ℝ} (hγ : 0 < γ) (ha : 0 ≤ a)
    (hs : 0 ≤ s) : |simplexSafeFactor γ a s| ≤ γ⁻¹ := by
  have hd : γ ≤ γ + s * a := by nlinarith [mul_nonneg hs ha]
  rw [simplexSafeFactor, max_eq_right hd, abs_of_pos (by positivity)]
  simpa only [one_div] using one_div_le_one_div_of_le hγ hd

private theorem simplexSafeFactor_sub_le {γ a s t : ℝ} (hγ : 0 < γ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |simplexSafeFactor γ a s - simplexSafeFactor γ a t| ≤ γ⁻¹ ^ 2 * |s - t| := by
  have hds : γ ≤ γ + s * a := by nlinarith [mul_nonneg hs ha0]
  have hdt : γ ≤ γ + t * a := by nlinarith [mul_nonneg ht ha0]
  have hdspos : 0 < γ + s * a := lt_of_lt_of_le hγ hds
  have hdtpos : 0 < γ + t * a := lt_of_lt_of_le hγ hdt
  simp only [simplexSafeFactor]
  rw [max_eq_right hds, max_eq_right hdt]
  have hform : (γ + s * a)⁻¹ - (γ + t * a)⁻¹ =
      a * (t - s) / ((γ + s * a) * (γ + t * a)) := by
    field_simp [ne_of_gt hdspos, ne_of_gt hdtpos]
    ring
  rw [hform, abs_div, abs_mul, abs_of_nonneg ha0,
    abs_of_pos (mul_pos hdspos hdtpos), abs_sub_comm t s]
  have hnum : a * |s - t| ≤ |s - t| :=
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (abs_nonneg (s - t))
  have hden : γ * γ ≤ (γ + s * a) * (γ + t * a) :=
    mul_le_mul hds hdt hγ.le hdspos.le
  calc
    a * |s - t| / ((γ + s * a) * (γ + t * a)) ≤
        |s - t| / ((γ + s * a) * (γ + t * a)) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hdspos.le hdtpos.le)
    _ ≤ |s - t| / (γ * γ) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hγ hγ) hden
    _ = γ⁻¹ ^ 2 * |s - t| := by
      rw [div_eq_mul_inv, mul_comm, mul_inv, ← pow_two]

private theorem simplexKernelSafe_sub_le (n : ℕ) (γ : ℝ) (y : Fin n → ℝ)
    (hγ : 0 < γ) (hy : y ∈ unitSimplex n) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |simplexKernelSafe γ s y - simplexKernelSafe γ t y| ≤
      ((γ⁻¹ ^ 2 * (max 1 γ⁻¹ ^ n)) +
        (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) * |s - t| := by
  simp only [unitSimplex, Set.mem_setOf_eq] at hy
  let B : ℝ := max 1 γ⁻¹
  let K : ℝ := γ⁻¹ ^ 2
  have hB : 1 ≤ B := le_max_left _ _
  have hK : 0 ≤ K := by positivity
  have hlast0 : 0 ≤ 1 - ∑ i, y i := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hy.2, hsum]
  have hlast1 : 1 - ∑ i, y i ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hsum]
  have hlastB_s := simplexSafeFactor_abs_le hγ hlast0 hs
  have hlastB_t := simplexSafeFactor_abs_le hγ hlast0 ht
  have hlastD := simplexSafeFactor_sub_le hγ hlast0 hlast1 hs ht
  have hprefixB_s : ∀ i ∈ Finset.univ, |simplexSafeFactor γ (y i) s| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) hs).trans (le_max_right _ _)
  have hprefixB_t : ∀ i ∈ Finset.univ, |simplexSafeFactor γ (y i) t| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) ht).trans (le_max_right _ _)
  have hprefixD : ∀ i ∈ Finset.univ,
      |simplexSafeFactor γ (y i) s - simplexSafeFactor γ (y i) t| ≤ K * |s - t| := by
    intro i hi
    exact simplexSafeFactor_sub_le hγ (hy.1 i)
      ((Finset.single_le_sum (fun k _ => hy.1 k) (Finset.mem_univ i)).trans hy.2) hs ht
  have hprodD := abs_prod_sub_prod_le (Finset.univ : Finset (Fin n)) B K |s - t| hB hK
    (abs_nonneg _) (fun i => simplexSafeFactor γ (y i) s)
    (fun i => simplexSafeFactor γ (y i) t) hprefixB_s hprefixB_t hprefixD
  have hprodB_s : |∏ i : Fin n, simplexSafeFactor γ (y i) s| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) s| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hprefixB_s
      _ = B ^ n := by simp
  have hprodB_t : |∏ i : Fin n, simplexSafeFactor γ (y i) t| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) t| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hprefixB_t
      _ = B ^ n := by simp
  have hB_nonneg : 0 ≤ B := le_trans (by positivity) hB
  calc
    |simplexKernelSafe γ s y - simplexKernelSafe γ t y| =
        |simplexSafeFactor γ (1 - ∑ i, y i) s *
            (∏ i, simplexSafeFactor γ (y i) s) -
          simplexSafeFactor γ (1 - ∑ i, y i) t *
            (∏ i, simplexSafeFactor γ (y i) t)| := rfl
    _ ≤ |simplexSafeFactor γ (1 - ∑ i, y i) s -
          simplexSafeFactor γ (1 - ∑ i, y i) t| *
          |∏ i, simplexSafeFactor γ (y i) s| +
        |simplexSafeFactor γ (1 - ∑ i, y i) t| *
          |(∏ i, simplexSafeFactor γ (y i) s) -
            ∏ i, simplexSafeFactor γ (y i) t| := by
          have h := norm_add_le
            ((simplexSafeFactor γ (1 - ∑ i, y i) s -
                simplexSafeFactor γ (1 - ∑ i, y i) t) *
              (∏ i, simplexSafeFactor γ (y i) s))
            (simplexSafeFactor γ (1 - ∑ i, y i) t *
              ((∏ i, simplexSafeFactor γ (y i) s) -
                ∏ i, simplexSafeFactor γ (y i) t))
          have heq :
              simplexSafeFactor γ (1 - ∑ i, y i) s *
                (∏ i, simplexSafeFactor γ (y i) s) -
              simplexSafeFactor γ (1 - ∑ i, y i) t *
                (∏ i, simplexSafeFactor γ (y i) t) =
                (simplexSafeFactor γ (1 - ∑ i, y i) s -
                  simplexSafeFactor γ (1 - ∑ i, y i) t) *
                  (∏ i, simplexSafeFactor γ (y i) s) +
                simplexSafeFactor γ (1 - ∑ i, y i) t *
                  ((∏ i, simplexSafeFactor γ (y i) s) -
                    ∏ i, simplexSafeFactor γ (y i) t) := by ring
          rw [← heq, Real.norm_eq_abs] at h
          simpa [Real.norm_eq_abs, abs_mul, Finset.abs_prod] using h
    _ ≤ K * |s - t| * B ^ n + B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) := by
          apply add_le_add
          · calc
              |simplexSafeFactor γ (1 - ∑ i, y i) s -
                  simplexSafeFactor γ (1 - ∑ i, y i) t| *
                  |∏ i, simplexSafeFactor γ (y i) s|
                  ≤ (K * |s - t|) * B ^ n :=
                    mul_le_mul hlastD hprodB_s (abs_nonneg _) (by positivity)
              _ = K * |s - t| * B ^ n := by ring
          · have hlastB : |simplexSafeFactor γ (1 - ∑ i, y i) t| ≤ B :=
              hlastB_t.trans (le_max_right _ _)
            have hprodD' :
                |∏ i, simplexSafeFactor γ (y i) s -
                  ∏ i, simplexSafeFactor γ (y i) t| ≤
                  (n : ℝ) * K * |s - t| * B ^ (n - 1) := by
              simpa [Finset.card_univ] using hprodD
            calc
              |simplexSafeFactor γ (1 - ∑ i, y i) t| *
                  |(∏ i, simplexSafeFactor γ (y i) s) -
                    ∏ i, simplexSafeFactor γ (y i) t|
                  ≤ B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) :=
                    mul_le_mul hlastB hprodD' (abs_nonneg _) (by positivity)
              _ = B * ((n : ℝ) * K * |s - t| * B ^ (n - 1)) := rfl
    _ = (K * B ^ n + B * ((n : ℝ) * K * B ^ (n - 1))) * |s - t| := by ring

private theorem simplexKernelSafe_integral_sub_le (n : ℕ) (γ : ℝ) (hγ : 0 < γ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(∫ y in unitSimplex n, simplexKernelSafe γ s y) -
      ∫ y in unitSimplex n, simplexKernelSafe γ t y| ≤
        (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          |s - t| * (volume (unitSimplex n)).toReal := by
  have hcompact := isCompact_unitSimplex n
  let g : ℝ → ℝ := fun z => (max γ z)⁻¹
  have hg : Continuous g := by
    apply (continuous_const.max continuous_id).inv₀
    intro z
    exact ne_of_gt (lt_of_lt_of_le hγ (le_max_left _ _))
  have hcont (u : ℝ) : Continuous (fun y : Fin n → ℝ => simplexKernelSafe γ u y) := by
    change Continuous (fun y : Fin n → ℝ =>
      g (γ + u * (1 - ∑ i, y i)) * ∏ i, g (γ + u * y i))
    fun_prop
  have his : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ s y)
      (unitSimplex n) volume := (hcont s).continuousOn.integrableOn_compact hcompact
  have hit : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ t y)
      (unitSimplex n) volume := (hcont t).continuousOn.integrableOn_compact hcompact
  have hdiff :
      (∫ y in unitSimplex n, simplexKernelSafe γ s y) -
        ∫ y in unitSimplex n, simplexKernelSafe γ t y =
          ∫ y in unitSimplex n, (simplexKernelSafe γ s y - simplexKernelSafe γ t y) := by
    rw [integral_sub his hit]
  have hbound : ∀ᵐ y ∂volume, y ∈ unitSimplex n →
      ‖simplexKernelSafe γ s y - simplexKernelSafe γ t y‖ ≤
        (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          (max 1 γ⁻¹) * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) * |s - t| :=
    Filter.Eventually.of_forall fun y hy => by
      simpa [Real.norm_eq_abs] using simplexKernelSafe_sub_le n γ y hγ hy hs ht
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae' hcompact.measure_lt_top hbound
  rw [← hdiff, Real.norm_eq_abs] at hnorm
  rw [Measure.real_def] at hnorm
  convert hnorm using 1 <;> ring

private theorem simplexKernelSafe_abs_le (n : ℕ) (γ s : ℝ) (y : Fin n → ℝ)
    (hγ : 0 < γ) (hy : y ∈ unitSimplex n) (hs : 0 ≤ s) :
    |simplexKernelSafe γ s y| ≤ (max 1 γ⁻¹) ^ (n + 1) := by
  simp only [unitSimplex, Set.mem_setOf_eq] at hy
  let B : ℝ := max 1 γ⁻¹
  have hB : 1 ≤ B := le_max_left _ _
  have hlast0 : 0 ≤ 1 - ∑ i, y i := by
    have hsum : 0 ≤ ∑ i : Fin n, y i := Finset.sum_nonneg fun i _ => hy.1 i
    linarith [hy.2, hsum]
  have hlast : |simplexSafeFactor γ (1 - ∑ i, y i) s| ≤ B :=
    (simplexSafeFactor_abs_le hγ hlast0 hs).trans (le_max_right _ _)
  have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      |simplexSafeFactor γ (y i) s| ≤ B := by
    intro i hi
    exact (simplexSafeFactor_abs_le hγ (hy.1 i) hs).trans (le_max_right _ _)
  have hprod : |∏ i : Fin n, simplexSafeFactor γ (y i) s| ≤ B ^ n := by
    rw [Finset.abs_prod]
    calc
      ∏ i : Fin n, |simplexSafeFactor γ (y i) s| ≤ ∏ _i : Fin n, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hcoord
      _ = B ^ n := by simp
  calc
    |simplexKernelSafe γ s y| =
        |simplexSafeFactor γ (1 - ∑ i, y i) s| *
          |∏ i : Fin n, simplexSafeFactor γ (y i) s| := by
          simp [simplexKernelSafe, abs_mul]
    _ ≤ B * B ^ n := mul_le_mul hlast hprod (abs_nonneg _) (by positivity)
    _ = B ^ (n + 1) := by
      rw [pow_succ]
      exact mul_comm _ _

private theorem simplexKernelSafe_integral_abs_le (n : ℕ) (γ s : ℝ)
    (hγ : 0 < γ) (hs : 0 ≤ s) :
    |∫ y in unitSimplex n, simplexKernelSafe γ s y| ≤
      (max 1 γ⁻¹) ^ (n + 1) * (volume (unitSimplex n)).toReal := by
  have hcompact := isCompact_unitSimplex n
  let g : ℝ → ℝ := fun z => (max γ z)⁻¹
  have hg : Continuous g := by
    apply (continuous_const.max continuous_id).inv₀
    intro z
    exact ne_of_gt (lt_of_lt_of_le hγ (le_max_left _ _))
  have hcont : Continuous (fun y : Fin n → ℝ => simplexKernelSafe γ s y) := by
    change Continuous (fun y : Fin n → ℝ =>
      g (γ + s * (1 - ∑ i, y i)) * ∏ i, g (γ + s * y i))
    fun_prop
  have his : IntegrableOn (fun y : Fin n → ℝ => simplexKernelSafe γ s y)
      (unitSimplex n) volume := hcont.continuousOn.integrableOn_compact hcompact
  have hbound : ∀ᵐ y ∂volume, y ∈ unitSimplex n →
      ‖simplexKernelSafe γ s y‖ ≤ (max 1 γ⁻¹) ^ (n + 1) :=
    Filter.Eventually.of_forall fun y hy => by
      simpa [Real.norm_eq_abs] using simplexKernelSafe_abs_le n γ s y hγ hy hs
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae' hcompact.measure_lt_top hbound
  rw [Real.norm_eq_abs, Measure.real_def] at hnorm
  exact hnorm

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  rw [show a * b - c * d = (a - c) * b + c * (b - d) by ring]
  calc
    |(a - c) * b + c * (b - d)| ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]

private theorem simplexKernelSafe_integral_posPart_lipschitz (n : ℕ) (γ c : ℝ)
    (hγ : 0 < γ) :
    LipschitzWith (Real.toNNReal
      ((γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
        max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
        (volume (unitSimplex n)).toReal))
      (fun w : ℝ => ∫ y in unitSimplex n,
        simplexKernelSafe γ (max 0 (w - c)) y) := by
  apply LipschitzWith.of_dist_le'
  intro u v
  let a := max 0 (u - c)
  let b := max 0 (v - c)
  have ha : 0 ≤ a := le_max_left _ _
  have hb : 0 ≤ b := le_max_left _ _
  have hab : |a - b| ≤ |u - v| := by
    dsimp [a, b]
    calc
      |max 0 (u - c) - max 0 (v - c)| ≤ |(u - c) - (v - c)| :=
        by simpa using abs_max_sub_max_le_max 0 (u - c) 0 (v - c)
      _ = |u - v| := by congr 1 <;> ring
  calc
    dist (∫ y in unitSimplex n, simplexKernelSafe γ a y)
        (∫ y in unitSimplex n, simplexKernelSafe γ b y) =
        |(∫ y in unitSimplex n, simplexKernelSafe γ a y) -
          ∫ y in unitSimplex n, simplexKernelSafe γ b y| := by rw [Real.dist_eq]
    _ ≤ (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          |a - b| * (volume (unitSimplex n)).toReal :=
      simplexKernelSafe_integral_sub_le n γ hγ ha hb
    _ ≤ ((γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
          max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
          (volume (unitSimplex n)).toReal) * |u - v| := by
      calc
        _ = (γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ n +
              max 1 γ⁻¹ * ((n : ℝ) * γ⁻¹ ^ 2 * max 1 γ⁻¹ ^ (n - 1))) *
              (volume (unitSimplex n)).toReal * |a - b| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)
    _ = _ := by rw [Real.dist_eq]

private theorem locallyLipschitz_pow (n : ℕ) :
    LocallyLipschitz (fun x : ℝ => x ^ n) := by
  have hpow : ContDiff ℝ 1 (fun x : ℝ => x ^ n) := by fun_prop
  exact hpow.locallyLipschitz

/-- The density term is a positive-part power times a fixed-simplex integral. -/
private theorem roughDensityTerm_eq_safe_simplex (γ w : ℝ) {j : ℕ}
    (hγ : 0 < γ) (hj : 2 ≤ j) :
    ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j =
      (1 / (j.factorial : ℝ)) * (max 0 (w - (j : ℝ) * γ)) ^ (j - 1) *
        ∫ y in unitSimplex (j - 1),
          simplexKernelSafe γ (max 0 (w - (j : ℝ) * γ)) y := by
  let s := w - (j : ℝ) * γ
  have hn1 : 1 ≤ j - 1 := by omega
  have hpow : (0 : ℝ) ^ (j - 1) = 0 := zero_pow (by omega)
  by_cases hsneg : s < 0
  · have hw : w < (j : ℝ) * γ := by dsimp [s] at hsneg; linarith
    rw [roughDensityTerm_eq_zero_of_lt γ w hγ hj hw]
    simp [s, max_eq_left hsneg.le, hpow]
  · by_cases hszero : s = 0
    · have heq : w = (j : ℝ) * γ := by dsimp [s] at hszero; linarith
      rw [heq, roughDensityTerm_eq_zero_at_support γ j hj]
      simp [s, hszero, hpow]
    · have hs : 0 < s := lt_of_le_of_ne (le_of_not_gt hsneg) (Ne.symm hszero)
      have hw : w = (j : ℝ) * γ + s := by dsimp [s]; ring
      have hformula := term_affine_simplex γ s j hj hs
      have hSmeas : MeasurableSet (unitSimplex (j - 1)) := by
        have h₁ : MeasurableSet {y : Fin (j - 1) → ℝ | ∀ i, 0 ≤ y i} := by
          simpa only [Set.iInter_ofPred] using
            (MeasurableSet.iInter fun i =>
              measurableSet_le measurable_const (measurable_pi_apply i))
        have h₂ : MeasurableSet {y : Fin (j - 1) → ℝ | ∑ i, y i ≤ 1} :=
          measurableSet_le (by fun_prop) measurable_const
        simpa only [unitSimplex, Set.setOf_and] using h₁.inter h₂
      have hkernel : ∀ y ∈ unitSimplex (j - 1),
          simplexKernelSafe γ s y = simplexKernel γ s y := by
        intro y hy
        simp only [unitSimplex, Set.mem_setOf_eq] at hy
        have hlast : 0 ≤ 1 - ∑ i, y i := by linarith
        have hlast' : γ ≤ γ + s * (1 - ∑ i, y i) := by
          nlinarith [mul_nonneg hs.le hlast]
        have hcoord : ∀ i, γ ≤ γ + s * y i := by
          intro i
          nlinarith [mul_nonneg hs.le (hy.1 i)]
        have hprod :
            (∏ i, (max γ (γ + s * y i))⁻¹) = ∏ i, (γ + s * y i)⁻¹ := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [max_eq_right (hcoord i)]
        simp only [simplexKernelSafe, simplexSafeFactor, simplexKernel]
        rw [max_eq_right hlast', hprod]
      calc
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j =
            ArtinPrimitiveRoots.Sieve.roughDensityTerm γ ((j : ℝ) * γ + s) j := by rw [hw]
        _ = (1 / (j.factorial : ℝ)) * s ^ (j - 1) *
              ∫ y in unitSimplex (j - 1), simplexKernel γ s y := hformula
        _ = (1 / (j.factorial : ℝ)) * (max 0 s) ^ (j - 1) *
              ∫ y in unitSimplex (j - 1),
                simplexKernelSafe γ (max 0 s) y := by
          rw [max_eq_right hs.le]
          rw [← setIntegral_congr_fun hSmeas hkernel]

private theorem locallyLipschitz_higherDensityTerm (γ : ℝ) (hγ : 0 < γ)
    (j : ℕ) (hj : 2 ≤ j) :
    LocallyLipschitz (fun w : ℝ =>
      ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) := by
  let c : ℝ := (j : ℝ) * γ
  let u : ℝ → ℝ := fun w => max 0 (w - c)
  let J : ℝ → ℝ := fun s =>
    ∫ y in unitSimplex (j - 1), simplexKernelSafe γ s y
  have hshift : LipschitzWith 1 (fun w : ℝ => w - c) := by
    simpa using LipschitzWith.id.sub (LipschitzWith.const c)
  have huLip : LipschitzWith 1 u := by
    simpa [u, Function.comp_def] using
      (LipschitzWith.id.const_max (0 : ℝ)).comp hshift
  have hu : LocallyLipschitz u := huLip.locallyLipschitz
  have hpow : LocallyLipschitz (fun w : ℝ => (u w) ^ (j - 1)) :=
    (locallyLipschitz_pow (j - 1)).comp hu
  have hJ : LocallyLipschitz (fun w : ℝ => J (u w)) := by
    exact (simplexKernelSafe_integral_posPart_lipschitz (j - 1) γ c hγ).locallyLipschitz
  have hpair : LocallyLipschitz (fun w : ℝ => ((u w) ^ (j - 1), J (u w))) :=
    hpow.prodMk hJ
  have hbilin : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      (1 / (j.factorial : ℝ)) * p.1 * p.2) := by fun_prop
  have hmodel : LocallyLipschitz (fun w : ℝ =>
      (1 / (j.factorial : ℝ)) * ((u w) ^ (j - 1) * J (u w))) := by
    simpa [Function.comp_def, mul_assoc] using hbilin.locallyLipschitz.comp hpair
  have heq : (fun w : ℝ => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) =
      (fun w : ℝ => (1 / (j.factorial : ℝ)) * ((u w) ^ (j - 1) * J (u w))) := by
    funext w
    simpa [u, J, c, mul_assoc] using
      roughDensityTerm_eq_safe_simplex γ w hγ hj
  rw [heq]
  exact hmodel

private abbrev PositiveGammaParam := {p : ℝ × ℝ // 0 < p.1}

private instance : LocallyCompactSpace PositiveGammaParam :=
  (isOpen_Ioi.preimage continuous_fst).locallyCompactSpace

private theorem continuous_simplexKernelSafe_integral (n : ℕ) :
    Continuous (fun p : PositiveGammaParam =>
      ∫ y in unitSimplex n, simplexKernelSafe p.1.1 p.1.2 y) := by
  apply continuous_parametric_integral_of_continuous
  · change Continuous (fun q : PositiveGammaParam × (Fin n → ℝ) =>
        (max q.1.1.1 (q.1.1.1 + q.1.1.2 * (1 - ∑ i, q.2 i)))⁻¹ *
          ∏ i, (max q.1.1.1 (q.1.1.1 + q.1.1.2 * q.2 i))⁻¹)
    have hγpos (q : PositiveGammaParam × (Fin n → ℝ)) : 0 < q.1.1.1 := q.1.property
    have hlast (q : PositiveGammaParam × (Fin n → ℝ)) :
        max q.1.1.1 (q.1.1.1 + q.1.1.2 * (1 - ∑ i, q.2 i)) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (hγpos q) (le_max_left _ _))
    have hcoord (q : PositiveGammaParam × (Fin n → ℝ)) (i : Fin n) :
        max q.1.1.1 (q.1.1.1 + q.1.1.2 * q.2 i) ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (hγpos q) (le_max_left _ _))
    fun_prop (disch := aesop)
  · exact isCompact_unitSimplex n

private abbrev GoodDensityParam := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 < p.2}

private theorem continuous_higherDensityTermModel (j : ℕ) (hj : 2 ≤ j) :
    Continuous (fun p : GoodDensityParam =>
      (1 / (j.factorial : ℝ)) *
        (max 0 (p.1.2 - (j : ℝ) * p.1.1)) ^ (j - 1) *
          ∫ y in unitSimplex (j - 1),
            simplexKernelSafe p.1.1 (max 0 (p.1.2 - (j : ℝ) * p.1.1)) y) := by
  let u : GoodDensityParam → ℝ := fun p => max 0 (p.1.2 - (j : ℝ) * p.1.1)
  let q : GoodDensityParam → PositiveGammaParam :=
    fun p => ⟨(p.1.1, u p), p.2.1⟩
  let J : PositiveGammaParam → ℝ := fun p =>
    ∫ y in unitSimplex (j - 1), simplexKernelSafe p.1.1 p.1.2 y
  have hu : Continuous u := by fun_prop
  have hq : Continuous q := by fun_prop
  have hJ : Continuous J := continuous_simplexKernelSafe_integral (j - 1)
  have hJcomp : Continuous (fun p => J (q p)) := hJ.comp hq
  have hfactor : Continuous (fun p : GoodDensityParam => (u p) ^ (j - 1)) := by fun_prop
  have hconst : Continuous (fun _ : GoodDensityParam => (1 / (j.factorial : ℝ))) :=
    continuous_const
  apply (hconst.mul (hfactor.mul hJcomp)).congr
  intro p
  simp [u, q, J]
  ring

private theorem continuousOn_roughDensityTerm (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensityTerm p.1 p.2 j)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun p : GoodDensityParam =>
    ArtinPrimitiveRoots.Sieve.roughDensityTerm p.1.1 p.1.2 j)
  by_cases hj0 : j = 0
  · subst j
    simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_pos (rfl : (0 : ℕ) = 0)]
    exact continuous_const
  · by_cases hj1 : j = 1
    · subst j
      simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm,
        if_neg (by decide : (1 : ℕ) ≠ 0), if_pos (rfl : (1 : ℕ) = 1), one_div]
      have hW : Continuous (fun p : GoodDensityParam => p.1.2) := by fun_prop
      have hWne : ∀ p : GoodDensityParam, p.1.2 ≠ 0 := fun p =>
        ne_of_gt (p.2.1.trans p.2.2)
      exact hW.inv₀ hWne
    · have hj2 : 2 ≤ j := by omega
      apply (continuous_higherDensityTermModel j hj2).congr
      intro p
      exact (roughDensityTerm_eq_safe_simplex p.1.1 p.1.2 p.2.1 hj2).symm

private theorem roughDensity_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
  intro p hp
  let γ₀ : ℝ := p.1 / 2
  let W : ℝ := p.2 + 1
  have hγ₀pos : 0 < γ₀ := by dsimp [γ₀]; linarith [hp.1]
  have hγ₀γ : γ₀ ≤ p.1 := by dsimp [γ₀]; linarith [hp.1]
  have hγ₀W : γ₀ < W := by dsimp [γ₀, W]; linarith [hp.1, hp.2]
  let N : ℕ := ⌊W / γ₀⌋₊ + 1
  let fsum : ℝ × ℝ → ℝ := fun q =>
    ∑ j ∈ Finset.range N, ArtinPrimitiveRoots.Sieve.roughDensityTerm q.1 q.2 j
  have hfsum : ContinuousOn fsum {q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2} := by
    dsimp [fsum]
    exact continuousOn_finsetSum (Finset.range N) fun j hj => continuousOn_roughDensityTerm j
  let U : Set (ℝ × ℝ) := {q | γ₀ < q.1 ∧ q.2 < W}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (isOpen_Ioi.preimage continuous_fst).inter (isOpen_Iio.preimage continuous_snd)
  have hpU : p ∈ U := by
    simp only [U, Set.mem_setOf_eq]
    constructor
    · exact half_lt_self hp.1
    · dsimp [W]
      linarith
  have hUevent : U ∈ 𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2}] p :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hUopen.mem_nhds hpU)
  have hfinite :
      (fun q : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity q.1 q.2) =ᶠ[
        𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ q.1 < q.2}] p] fsum := by
    filter_upwards [self_mem_nhdsWithin, hUevent] with q hq hqU
    rcases hq with ⟨hqγ, hqγw⟩
    rcases hqU with ⟨hγ₀q, hqW⟩
    have hqγW : q.1 < W := hqγw.trans hqW
    simpa [fsum, N] using
      roughDensity_eq_sum_uniform q.1 q.2 W γ₀ hqγ hγ₀pos (le_of_lt hγ₀q) hqγW hqW.le
  have hpoint :
      ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2 = fsum p := by
    have hpγW : p.1 < W := by dsimp [W]; linarith [hp.2]
    have hpW : p.2 ≤ W := by dsimp [W]; linarith
    simpa [fsum, N] using
      roughDensity_eq_sum_uniform p.1 p.2 W γ₀ hp.1 hγ₀pos hγ₀γ hpγW hpW
  exact (hfsum p hp).congr_of_eventuallyEq hfinite hpoint

private theorem locallyLipschitzOn_finsetSum {ι : Type*} [DecidableEq ι]
    (s : Set ℝ) (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ S, LocallyLipschitzOn s (f i)) :
    LocallyLipschitzOn s (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa using (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn
  | @insert a S ha ih =>
      have hfa := hf a (Finset.mem_insert_self a S)
      have hfS : ∀ i ∈ S, LocallyLipschitzOn s (f i) := fun i hi =>
        hf i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert, ha] using hfa.add (ih hfS)

private theorem locallyLipschitzOn_roughDensityTerm (γ : ℝ) (hγ : 0 < γ) (j : ℕ) :
    LocallyLipschitzOn (Set.Ioi γ)
      (fun w => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ w j) := by
  by_cases hj0 : j = 0
  · subst j
    simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm, if_pos rfl]
    exact (LocallyLipschitz.const (0 : ℝ)).locallyLipschitzOn
  · by_cases hj1 : j = 1
    · subst j
      simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm,
        if_neg (by decide : (1 : ℕ) ≠ 0), if_pos (rfl : (1 : ℕ) = 1), one_div]
      have hrec : ContDiffOn ℝ 1 (fun w : ℝ => w⁻¹) (Set.Ioi γ) := by
        exact contDiffOn_id.inv fun w hw => ne_of_gt (lt_trans hγ hw)
      simpa [one_div] using hrec.locallyLipschitzOn (convex_Ioi γ)
    · have hj : 2 ≤ j := by omega
      exact (locallyLipschitz_higherDensityTerm γ hγ j hj).locallyLipschitzOn

private theorem locallyLipschitzOn_roughDensity (γ : ℝ) (hγ : 0 < γ) :
    LocallyLipschitzOn (Set.Ioi γ)
      (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w) := by
  intro w hw
  let W : ℝ := w + 1
  change γ < w at hw
  have hγW : γ < W := by dsimp [W]; linarith
  let N : ℕ := ⌊W / γ⌋₊ + 1
  let f : ℝ → ℝ := fun z =>
    ∑ j ∈ Finset.range N, ArtinPrimitiveRoots.Sieve.roughDensityTerm γ z j
  have hf : LocallyLipschitzOn (Set.Ioi γ) f := by
    dsimp [f]
    exact locallyLipschitzOn_finsetSum (Set.Ioi γ) (Finset.range N)
      (fun j z => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ z j) fun j hj =>
        locallyLipschitzOn_roughDensityTerm γ hγ j
  obtain ⟨K, t, ht, hLip⟩ := hf hw
  have hwW : w < W := by dsimp [W]; linarith
  have hWmem : Set.Iio W ∈ 𝓝[Set.Ioi γ] w :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Iio.mem_nhds hwW)
  let t' := t ∩ Set.Iio W
  have ht' : t' ∈ 𝓝[Set.Ioi γ] w := by
    exact Filter.inter_mem ht hWmem
  refine ⟨K, t', ht', ?_⟩
  intro u hu v hv
  have huEq : ArtinPrimitiveRoots.Sieve.roughDensity γ u = f u := by
    have huW : u ≤ W := le_of_lt hu.2
    simpa [f, N] using roughDensity_eq_sum_bounded γ u W hγ hγW huW
  have hvEq : ArtinPrimitiveRoots.Sieve.roughDensity γ v = f v := by
    have hvW : v ≤ W := le_of_lt hv.2
    simpa [f, N] using roughDensity_eq_sum_bounded γ v W hγ hγW hvW
  change edist (ArtinPrimitiveRoots.Sieve.roughDensity γ u)
    (ArtinPrimitiveRoots.Sieve.roughDensity γ v) ≤ K * edist u v
  rw [huEq, hvEq]
  exact hLip hu.1 hv.1

private theorem roughDensity_lipschitzOnCompact (γ w₀ w₁ : ℝ)
    (hγ : 0 < γ) (hγw₀ : γ < w₀) (hw₀w₁ : w₀ ≤ w₁) :
    ∃ K : NNReal, LipschitzOnWith K (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w)
      (Set.Icc w₀ w₁) := by
  have hdom : Set.Icc w₀ w₁ ⊆ Set.Ioi γ := fun _ hu => hγw₀.trans_le hu.1
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    ((locallyLipschitzOn_roughDensity γ hγ).mono hdom)

/-- The one-factor pushforward identity is the logarithmic integral itself. -/
private theorem roughTupleIntegral_one (γ : ℝ) (hγ : 0 < γ) (x : ℝ) (hx : 2 ≤ x)
    (l r : ℝ) (hl : Real.rpow x γ < l) (hr : l ≤ r) :
    roughTupleIntegral x γ l r 1 =
      (1 / Real.log x) * ∫ y in l..r,
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / Real.log x) 1 := by
  have hx1 : 1 < x := by linarith
  have hxpow : 1 < Real.rpow x γ := Real.one_lt_rpow hx1 hγ
  have hl1 : 1 < l := lt_trans hxpow hl
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  let mp := volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  rw [roughTupleIntegral]
  simp only [Nat.factorial_one, Nat.cast_one, one_div]
  rw [← mp.symm.integral_comp']
  simp only [MeasurableEquiv.piUnique_symm_apply, Finset.univ_unique, Finset.prod_singleton]
  simp [ArtinPrimitiveRoots.Sieve.roughDensityTerm, uniqueElim]
  have hleft :
      (∫ t : ℝ, if Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r then (Real.log t)⁻¹ else 0) =
        ∫ t in Set.Icc l r, (Real.log t)⁻¹ := by
    calc
      _ = ∫ t : ℝ, Set.indicator (Set.Icc l r) (fun t => (Real.log t)⁻¹) t := by
        apply integral_congr_ae
        filter_upwards with t
        have hP : (Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r) ↔ t ∈ Set.Icc l r := by
          constructor
          · rintro ⟨_, hlt, hrt⟩
            exact ⟨hlt, hrt⟩
          · intro ht
            exact ⟨lt_of_lt_of_le hl ht.1, ht.1, ht.2⟩
        simp only [Set.indicator]
        exact if_congr hP rfl rfl
      _ = _ := integral_indicator measurableSet_Icc
  calc
    (∫ t : ℝ, if Real.rpow x γ < t ∧ l ≤ t ∧ t ≤ r then (Real.log t)⁻¹ else 0) =
        ∫ t in Set.Icc l r, (Real.log t)⁻¹ := hleft
    _ = ∫ y in l..r, (Real.log y)⁻¹ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
    _ = (Real.log x)⁻¹ * ∫ y in l..r, Real.log x / Real.log y := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      field_simp [hlogx]

private noncomputable def roughLogProductMap (L : ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = Fin.last n then ∏ k, t k else Real.log (t i) / L

private noncomputable def roughLogProductJac (L : ℝ) {n : ℕ}
    (t : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i k => if i = Fin.last n then
      (((List.finRange (n + 1)).map t).eraseIdx k.val).prod
    else if i = k then (L * t i)⁻¹ else 0

set_option maxHeartbeats 1000000 in
private theorem roughLogProductMap_hasFDerivAt {n : ℕ} {L : ℝ}
    (t : Fin (n + 1) → ℝ) (hL : L ≠ 0) (ht : ∀ i, t i ≠ 0) :
    HasFDerivAt (fun s => roughLogProductMap L s)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (roughLogProductJac L t))) t := by
  classical
  let D := roughLogProductJac L t
  let A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' D)
  change HasFDerivAt (fun s i => roughLogProductMap L s i) A t
  have hA : ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i ∘L A) = A := by
    ext s i
    simp
  rw [← hA]
  apply hasFDerivAt_pi.2
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    have hp := hasFDerivAt_list_prod_finRange' (𝕜 := ℝ) (n := n + 1) (x := t)
    have hp' : HasFDerivAt (fun s : Fin (n + 1) → ℝ => ∏ k, s k)
        (∑ k : Fin (n + 1),
          (((List.finRange (n + 1)).map t).eraseIdx k.val).prod •
            (ContinuousLinearMap.proj k : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)) t := by
      convert hp using 1
      · ext s
        simp [Fin.prod_univ_def]
      · ext h
        simp [List.eraseIdx_eq_take_drop_succ, List.prod_append,
          ContinuousLinearMap.smulRight_apply, smul_eq_mul, op_smul_eq_smul,
          mul_assoc, mul_comm, mul_left_comm]
    have hlin :
        ∑ k : Fin (n + 1),
          (((List.finRange (n + 1)).map t).eraseIdx k.val).prod •
            (ContinuousLinearMap.proj k : (Fin (n + 1) → ℝ) →L[ℝ] ℝ) =
        ContinuousLinearMap.proj (Fin.last n) ∘SL A := by
      ext h
      simp [A, D, roughLogProductJac, Matrix.toLin'_apply, Matrix.mulVec,
        Matrix.mulVec_apply_eq_sum, dotProduct, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    simpa [roughLogProductMap, A, D, roughLogProductJac] using hp'.congr_fderiv hlin
  · have hscalar : HasDerivAt (fun z : ℝ => Real.log z / L)
        ((t i)⁻¹ / L) (t i) := by
      exact (Real.hasDerivAt_log (ht i)).div_const L
    have hid : HasFDerivAt (fun s : Fin (n + 1) → ℝ => s i)
        (ContinuousLinearMap.proj (R := ℝ) i) t := by
      exact hasFDerivAt_apply i t
    have hcomp := HasDerivAt.comp_hasFDerivAt
      (f := fun s : Fin (n + 1) → ℝ => s i) t hscalar hid
    have hlin : ContinuousLinearMap.proj i ∘SL A =
        ((t i)⁻¹ / L) • ContinuousLinearMap.proj i := by
      ext h
      change (∑ k : Fin (n + 1), roughLogProductJac L t i k * h k) =
        (t i)⁻¹ / L * h i
      have hcoef : (L * t i)⁻¹ = (t i)⁻¹ / L := by
        field_simp [hL, ht i]
      simp [roughLogProductJac, hi, hcoef, eq_comm]
    simpa [roughLogProductMap, Function.comp_def, hi, A, D, roughLogProductJac] using
      hcomp.congr_fderiv hlin.symm

private theorem list_finRange_take_prod {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (List.take n ((List.finRange (n + 1)).map t)).prod =
      ∏ i : Fin n, t (Fin.castSucc i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.take_succ_cons, List.prod_cons,
        Fin.prod_univ_succ]
      simp only [List.map_map, Function.comp_def, Fin.castSucc_zero, Fin.castSucc_succ]
      congr 1
      simpa only [List.map_map, Function.comp_def, Fin.castSucc_succ] using
        ih (fun k => t (Fin.succ k))

private theorem roughLogProductJac_abs_det {n : ℕ} {L : ℝ}
    (t : Fin (n + 1) → ℝ) (hL : 0 < L) (ht : ∀ i, 0 < t i) :
    |(roughLogProductJac L t).det| = L⁻¹ ^ n := by
  classical
  let D := roughLogProductJac L t
  have hLower : D.IsLowerTriangular := by
    intro i k hik
    by_cases hi : i = Fin.last n
    · subst i
      exact False.elim ((not_lt_of_ge (Fin.le_last k)) hik)
    · by_cases hik' : i = k
      · subst k
        exact (lt_irrefl i hik).elim
      · simp [D, roughLogProductJac, hi, hik']
  have hlastDiag : D (Fin.last n) (Fin.last n) =
      ∏ i : Fin n, t (Fin.castSucc i) := by
    simp only [D, roughLogProductJac, if_pos rfl, Fin.val_last]
    rw [List.eraseIdx_eq_take_drop_succ, List.prod_append]
    let l : List ℝ := (List.finRange (n + 1)).map t
    have hlen : l.length = n + 1 := by simp [l]
    have hdrop : l.drop (n + 1) = [] := by
      rw [← hlen]
      exact List.drop_length
    rw [hdrop, List.prod_nil, mul_one]
    exact list_finRange_take_prod (n := n) t
  have htopDiag :
      ∏ i : Fin n, D (Fin.castSucc i) (Fin.castSucc i) =
        ∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹ := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [D, roughLogProductJac]
  have hdiag :
      ∏ i : Fin (n + 1), D i i =
        (∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹) *
          ∏ i : Fin n, t (Fin.castSucc i) := by
    rw [Fin.prod_univ_castSucc, htopDiag, hlastDiag]
  have hcancel :
      (∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹) *
        ∏ i : Fin n, t (Fin.castSucc i) = L⁻¹ ^ n := by
    rw [← Finset.prod_mul_distrib]
    calc
      ∏ i : Fin n, (L * t (Fin.castSucc i))⁻¹ * t (Fin.castSucc i) =
          ∏ _i : Fin n, L⁻¹ := by
            apply Finset.prod_congr rfl
            intro i hi
            field_simp [ne_of_gt hL, ne_of_gt (ht (Fin.castSucc i))]
      _ = L⁻¹ ^ n := by simp
  have hdet : D.det = L⁻¹ ^ n := by
    rw [Matrix.det_of_isLowerTriangular D hLower, hdiag]
    exact hcancel
  rw [hdet]
  exact abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hL.le) n)

private def roughTupleSource {n : ℕ} (A l r : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {t | (∀ i, A ≤ t i) ∧ l ≤ ∏ i, t i ∧ (∏ i, t i) ≤ r}

private def roughTupleImage (x γ l r : ℝ) {n : ℕ} : Set (Fin (n + 1) → ℝ) :=
  {q | (∀ i : Fin n, γ ≤ q (Fin.castSucc i)) ∧
    l ≤ q (Fin.last n) ∧ q (Fin.last n) ≤ r ∧
    Real.rpow x γ * (∏ i : Fin n, Real.rpow x (q (Fin.castSucc i))) ≤ q (Fin.last n)}

private theorem roughLogProductMap_image_eq {n : ℕ} (x γ l r : ℝ)
    (hx : 2 ≤ x) (hγ : 0 < γ) :
    Set.image (roughLogProductMap (Real.log x) :
        (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
      (roughTupleSource (Real.rpow x γ) l r) = roughTupleImage x γ l r := by
  classical
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := lt_trans (by norm_num) hx1
  have hxne : x ≠ 1 := ne_of_gt hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hA : 0 < Real.rpow x γ := Real.rpow_pos_of_pos hxpos γ
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨htA, htl, htr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hti := htA (Fin.castSucc i)
      have hlog := Real.log_le_log hA hti
      have hlogA : Real.log (Real.rpow x γ) = γ * Real.log x := Real.log_rpow hxpos γ
      rw [hlogA] at hlog
      simp only [roughLogProductMap, Fin.castSucc_ne_last]
      exact (le_div_iff₀ hL).2 hlog
    · change l ≤ roughLogProductMap (Real.log x) t (Fin.last n)
      simp only [roughLogProductMap, if_pos rfl]
      exact htl
    · change roughLogProductMap (Real.log x) t (Fin.last n) ≤ r
      simp only [roughLogProductMap, if_pos rfl]
      exact htr
    · have hfirst : ∏ i : Fin n,
          Real.rpow x (roughLogProductMap (Real.log x) t (Fin.castSucc i)) =
            ∏ i : Fin n, t (Fin.castSucc i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have htiPos : 0 < t (Fin.castSucc i) := lt_of_lt_of_le hA (htA (Fin.castSucc i))
        have hmapI : roughLogProductMap (Real.log x) t (Fin.castSucc i) =
            Real.log (t (Fin.castSucc i)) / Real.log x := by
          simp [roughLogProductMap, Fin.castSucc_ne_last]
        rw [hmapI]
        simpa [Real.logb] using Real.rpow_logb hxpos hxne htiPos
      have hlast : Real.rpow x γ ≤ t (Fin.last n) := htA (Fin.last n)
      have hPpos : 0 < ∏ i : Fin n, t (Fin.castSucc i) :=
        Finset.prod_pos fun i hi => lt_of_lt_of_le hA (htA (Fin.castSucc i))
      have hprod : ∏ i : Fin (n + 1), t i =
          (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) := Fin.prod_univ_castSucc _
      change Real.rpow x γ *
          ∏ i : Fin n, Real.rpow x (roughLogProductMap (Real.log x) t (Fin.castSucc i)) ≤
        roughLogProductMap (Real.log x) t (Fin.last n)
      rw [hfirst]
      calc
        Real.rpow x γ * (∏ i : Fin n, t (Fin.castSucc i)) ≤
            (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) := by
          calc
            _ = (∏ i : Fin n, t (Fin.castSucc i)) * Real.rpow x γ := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hlast hPpos.le
        _ = roughLogProductMap (Real.log x) t (Fin.last n) := by
          simp only [roughLogProductMap, if_pos rfl]
          exact hprod.symm
  · intro hq
    rcases hq with ⟨hu, hqlo, hqhi, hqprod⟩
    let p : Fin n → ℝ := fun i => Real.rpow x (q (Fin.castSucc i))
    let P : ℝ := ∏ i : Fin n, p i
    let z : ℝ := q (Fin.last n) / P
    let t : Fin (n + 1) → ℝ := Fin.snoc p z
    have hpPos : ∀ i, 0 < p i := fun i => Real.rpow_pos_of_pos hxpos _
    have hPpos : 0 < P := by
      dsimp [P]
      exact Finset.prod_pos fun i hi => hpPos i
    have htFirst : ∀ i : Fin n, Real.rpow x γ ≤ t (Fin.castSucc i) := by
      intro i
      dsimp [t, p]
      rw [Fin.snoc_castSucc]
      exact (Real.rpow_le_rpow_left_iff hx1).2 (hu i)
    have htLast : Real.rpow x γ ≤ t (Fin.last n) := by
      dsimp [t, z]
      rw [Fin.snoc_last]
      exact (le_div_iff₀ hPpos).2 hqprod
    have hprod : ∏ i : Fin (n + 1), t i = q (Fin.last n) := by
      rw [Fin.prod_univ_castSucc]
      simp only [t, Fin.snoc_castSucc, Fin.snoc_last]
      change P * z = q (Fin.last n)
      dsimp [z]
      exact mul_div_cancel₀ _ (ne_of_gt hPpos)
    have htSource : t ∈ roughTupleSource (Real.rpow x γ) l r := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · exact htFirst i'
        · exact htLast
      · rw [hprod]
        exact hqlo
      · rw [hprod]
        exact hqhi
    have hmap : roughLogProductMap (Real.log x) t = q := by
      funext k
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, hk⟩ | hk
      · rw [hk]
        have hlogrpow : Real.log (Real.rpow x (q (Fin.castSucc i))) / Real.log x =
            q (Fin.castSucc i) := by
          have hlog : Real.log (Real.rpow x (q (Fin.castSucc i))) =
              q (Fin.castSucc i) * Real.log x := by
            simpa only [Real.rpow_eq_pow] using Real.log_rpow hxpos (q (Fin.castSucc i))
          calc
            _ = (q (Fin.castSucc i) * Real.log x) / Real.log x := by rw [hlog]
            _ = q (Fin.castSucc i) := by field_simp [ne_of_gt hL]
        have hmapI : roughLogProductMap (Real.log x) t (Fin.castSucc i) =
            q (Fin.castSucc i) := by
          simp only [roughLogProductMap, if_neg (Fin.castSucc_ne_last i)]
          simp only [t, Fin.snoc_castSucc, p]
          exact hlogrpow
        exact hmapI
      · rw [hk]
        simp only [roughLogProductMap, if_true]
        exact hprod
    exact ⟨t, htSource, hmap⟩

private theorem measurableSet_roughTupleSource {n : ℕ} (A l r : ℝ) :
    MeasurableSet (roughTupleSource (n := n) A l r) := by
  have hcoords : MeasurableSet {t : Fin (n + 1) → ℝ | ∀ i, A ≤ t i} := by
    have hconst : Measurable (fun _ : Fin (n + 1) → ℝ => A) := measurable_const
    have h := MeasurableSet.iInter fun i : Fin (n + 1) =>
      measurableSet_le hconst (measurable_pi_apply i)
    simpa only [Set.iInter_ofPred] using h
  have hprod : Measurable (fun t : Fin (n + 1) → ℝ => ∏ i, t i) := by fun_prop
  have hlo : MeasurableSet {t : Fin (n + 1) → ℝ | l ≤ ∏ i, t i} :=
    measurableSet_le measurable_const hprod
  have hhi : MeasurableSet {t : Fin (n + 1) → ℝ | (∏ i, t i) ≤ r} :=
    measurableSet_le hprod measurable_const
  simpa [roughTupleSource, Set.setOf_and] using hcoords.inter (hlo.inter hhi)

private theorem roughTupleIntegral_eq_source (x γ l r : ℝ) {n : ℕ}
    (hx : 2 ≤ x) :
    roughTupleIntegral x γ l r (n + 1) =
      (1 / ((n + 1).factorial : ℝ)) *
        ∫ t in roughTupleSource (n := n) (Real.rpow x γ) l r,
          ∏ i : Fin (n + 1), 1 / Real.log (t i) := by
  classical
  let A := Real.rpow x γ
  have hx1 : 1 < x := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos (by linarith) γ
  have hpi :
      (Set.univ.pi (fun _ : Fin (n + 1) => Set.Ioi A)) =ᵐ[volume]
        Set.Ici (fun _ : Fin (n + 1) => A) := by
    have h := MeasureTheory.Measure.univ_pi_Ioi_ae_eq_Ici
      (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ)) (f := fun _ => A)
    simpa only [← MeasureTheory.volume_pi] using h
  have hcoordsAE : ∀ᵐ t : Fin (n + 1) → ℝ ∂volume,
      (∀ i, A < t i) ↔ ∀ i, A ≤ t i := by
    filter_upwards [hpi] with t ht
    simpa [Set.mem_pi, Set.mem_univ, Set.mem_Ioi, Set.mem_Ici, Pi.le_def] using ht
  have hfun : (fun t : Fin (n + 1) → ℝ =>
        if (∀ i, Real.rpow x γ < t i) ∧ l ≤ ∏ i, t i ∧ (∏ i, t i) ≤ r then
          ∏ i : Fin (n + 1), 1 / Real.log (t i) else 0) =ᵐ[volume]
      (fun t => Set.indicator (roughTupleSource (n := n) A l r)
        (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i)) t) := by
    filter_upwards [hcoordsAE] with t ht
    have hcoord : (∀ i, Real.rpow x γ < t i) ↔ (∀ i, A ≤ t i) := by
      simpa [A] using ht
    simp only [Set.indicator]
    apply if_congr
    · exact and_congr hcoord Iff.rfl
    · rfl
    · rfl
  unfold roughTupleIntegral
  rw [integral_congr_ae hfun, integral_indicator (measurableSet_roughTupleSource A l r)]

private theorem roughLogProductMap_injOn_source {n : ℕ} {L A l r : ℝ}
    (hL : 0 < L) (hA : 0 < A) :
    Set.InjOn (roughLogProductMap L : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
      (roughTupleSource (n := n) A l r) := by
  intro t ht u hu hmap
  have hfirst (i : Fin n) : t (Fin.castSucc i) = u (Fin.castSucc i) := by
    have hm := congrFun hmap (Fin.castSucc i)
    simp only [roughLogProductMap, Fin.castSucc_ne_last] at hm
    have hlog : Real.log (t (Fin.castSucc i)) = Real.log (u (Fin.castSucc i)) := by
      have := congrArg (fun z : ℝ => z * L) hm
      simpa [div_eq_mul_inv, mul_assoc, ne_of_gt hL] using this
    apply Real.log_injOn_pos
      (lt_of_lt_of_le hA (ht.1 (Fin.castSucc i)))
      (lt_of_lt_of_le hA (hu.1 (Fin.castSucc i)))
    exact hlog
  have hfirstProd : ∏ i : Fin n, t (Fin.castSucc i) =
      ∏ i : Fin n, u (Fin.castSucc i) := by
    exact Finset.prod_congr rfl fun i _ => hfirst i
  have hlast : t (Fin.last n) = u (Fin.last n) := by
    have hm :
        (∏ i : Fin n, t (Fin.castSucc i)) * t (Fin.last n) =
          (∏ i : Fin n, u (Fin.castSucc i)) * u (Fin.last n) := by
      simpa [roughLogProductMap, Fin.prod_univ_castSucc] using
        congrFun hmap (Fin.last n)
    have hpos : 0 < ∏ i : Fin n, t (Fin.castSucc i) :=
      Finset.prod_pos fun i _ => lt_of_lt_of_le hA (ht.1 (Fin.castSucc i))
    have hposU : 0 < ∏ i : Fin n, u (Fin.castSucc i) := by
      rw [← hfirstProd]
      exact hpos
    rw [hfirstProd] at hm
    exact mul_left_cancel₀ (ne_of_gt hposU) hm
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · exact hfirst k
  · exact hlast

private theorem roughTupleKernel_integrableOn_source {n : ℕ} {A l r : ℝ}
    (hA1 : 1 < A) (hAl : A < l) (hlr : l ≤ r) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i))
      (roughTupleSource (n := n) A l r) volume := by
  classical
  let K : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun _ => Set.Icc A r
  have hK : IsCompact K := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsubset : roughTupleSource (n := n) A l r ⊆ K := by
    intro t ht
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨ht.1 i, ?_⟩
    have hprodOne (s : Finset (Fin (n + 1))) : 1 ≤ ∏ k ∈ s, t k := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
        rw [Finset.prod_insert hks]
        have hk1 : 1 ≤ t k := le_trans hA1.le (ht.1 k)
        have hA0 : 0 ≤ A := by linarith
        have hs0 : 0 ≤ ∏ q ∈ s, t q :=
          Finset.prod_nonneg fun q _ => le_trans hA0 (ht.1 q)
        nlinarith [mul_le_mul_of_nonneg_left hk1 hs0]
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i, t k := hprodOne _
    have hprodEq : t i * ∏ k ∈ Finset.univ.erase i, t k =
        ∏ k : Fin (n + 1), t k :=
      Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i)
    have hsingle : t i ≤ ∏ k : Fin (n + 1), t k := by
      calc
        t i = t i * 1 := by ring
        _ ≤ t i * ∏ k ∈ Finset.univ.erase i, t k :=
          mul_le_mul_of_nonneg_left hrest
            (le_trans (by norm_num : 0 ≤ (1 : ℝ)) (le_trans hA1.le (ht.1 i)))
        _ = ∏ k : Fin (n + 1), t k := hprodEq
    exact hsingle.trans ht.2.2
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  let F : (Fin (n + 1) → ℝ) → ℝ := fun t =>
    ∏ i : Fin (n + 1), (max (Real.log A) (Real.log (max A (t i))))⁻¹
  have hF : Continuous F := by
    unfold F
    apply continuous_finsetProd Finset.univ
    intro i hi
    have hlog : Continuous (fun t : Fin (n + 1) → ℝ => Real.log (max A (t i))) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hmaxAt : ContinuousAt (fun u : ℝ => max A u) (t i) :=
        (continuous_const.max continuous_id).continuousAt
      have hlogAt : ContinuousAt (fun u : ℝ => Real.log (max A u)) (t i) := by
        have hlogAt' : ContinuousAt Real.log (max A (t i)) :=
          Real.continuousAt_log
            (ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one hA1) (le_max_left A (t i))))
        exact ContinuousAt.comp (f := fun u : ℝ => max A u) (g := Real.log)
          (x := t i) hlogAt' hmaxAt
      have happly : ContinuousAt (fun u : Fin (n + 1) → ℝ => u i) t :=
        (continuous_apply i).continuousAt
      exact ContinuousAt.comp (f := fun u : Fin (n + 1) → ℝ => u i)
        (g := fun u : ℝ => Real.log (max A u)) (x := t) hlogAt happly
    have hden : Continuous (fun t : Fin (n + 1) → ℝ =>
        max (Real.log A) (Real.log (max A (t i)))) := continuous_const.max hlog
    apply hden.inv₀
    intro t
    exact ne_of_gt (lt_of_lt_of_le hlogA (le_max_left _ _))
  have hFeq : ∀ t ∈ K, F t = ∏ i : Fin (n + 1), 1 / Real.log (t i) := by
    intro t ht
    have htcoord : ∀ i, A ≤ t i := by
      have hti : ∀ i, t i ∈ Set.Icc A r := by
        simpa only [K, Set.mem_pi, Set.mem_univ, true_implies] using ht
      intro i
      exact (hti i).1
    unfold F
    apply Finset.prod_congr rfl
    intro i hi
    have hlog : Real.log A ≤ Real.log (t i) :=
      Real.log_le_log (lt_trans zero_lt_one hA1) (htcoord i)
    simp [max_eq_right (htcoord i), max_eq_right hlog]
  have hf : ContinuousOn
      (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i)) K :=
    hF.continuousOn.congr fun t ht => (hFeq t ht).symm
  have hsfinite : volume (roughTupleSource (n := n) A l r) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsubset) hK.measure_lt_top)
  exact hf.integrableOn_of_subset_isCompact hK
    (measurableSet_roughTupleSource A l r) hsubset hsfinite

private theorem roughTupleImage_eq_logSimplex {n : ℕ} (x γ l r : ℝ)
    (hx : 2 ≤ x) (hγ : 0 < γ) (hl : Real.rpow x γ < l) :
    roughTupleImage x γ l r =
      {q | (∀ i : Fin n, γ ≤ q (Fin.castSucc i)) ∧
        l ≤ q (Fin.last n) ∧ q (Fin.last n) ≤ r ∧
        (∑ i : Fin n, q (Fin.castSucc i)) ≤
          Real.log (q (Fin.last n)) / Real.log x - γ} := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hA1 : 1 < Real.rpow x γ := Real.one_lt_rpow hx1 hγ
  have hl1 : 1 < l := lt_trans hA1 hl
  ext q
  constructor
  · rintro ⟨hqγ, hqlo, hqhi, hqprod⟩
    refine ⟨hqγ, hqlo, hqhi, ?_⟩
    have hy : 0 < q (Fin.last n) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hl1 hqlo)
    have hsumPow :
        ∏ i : Fin n, Real.rpow x (q (Fin.castSucc i)) =
          Real.rpow x (∑ i : Fin n, q (Fin.castSucc i)) := by
      simpa using
        (Real.rpow_sum_of_pos hxpos
          (fun i : Fin n => q (Fin.castSucc i)) Finset.univ).symm
    have hpow : Real.rpow x γ *
        ∏ i : Fin n, Real.rpow x (q (Fin.castSucc i)) =
        Real.rpow x (γ + ∑ i : Fin n, q (Fin.castSucc i)) := by
      calc
        _ = Real.rpow x γ * Real.rpow x (∑ i : Fin n, q (Fin.castSucc i)) := by rw [hsumPow]
        _ = Real.rpow x (γ + ∑ i : Fin n, q (Fin.castSucc i)) :=
          (Real.rpow_add hxpos γ _).symm
    have hlog := (Real.rpow_le_iff_le_log hxpos hy).1 (hpow ▸ hqprod)
    have hsum : (∑ i : Fin n, q (Fin.castSucc i)) * Real.log x ≤
        Real.log (q (Fin.last n)) - γ * Real.log x := by
      nlinarith [hlog]
    have hdiv := (le_div_iff₀ hL).2 hsum
    have hquot :
        (Real.log (q (Fin.last n)) - γ * Real.log x) / Real.log x =
          Real.log (q (Fin.last n)) / Real.log x - γ := by
      field_simp [ne_of_gt hL]
    rw [hquot] at hdiv
    exact hdiv
  · rintro ⟨hqγ, hqlo, hqhi, hsimplex⟩
    refine ⟨hqγ, hqlo, hqhi, ?_⟩
    have hy : 0 < q (Fin.last n) :=
      lt_trans zero_lt_one (lt_of_lt_of_le hl1 hqlo)
    have hsumPow :
        ∏ i : Fin n, Real.rpow x (q (Fin.castSucc i)) =
          Real.rpow x (∑ i : Fin n, q (Fin.castSucc i)) := by
      simpa using
        (Real.rpow_sum_of_pos hxpos
          (fun i : Fin n => q (Fin.castSucc i)) Finset.univ).symm
    have hpow : Real.rpow x γ *
        ∏ i : Fin n, Real.rpow x (q (Fin.castSucc i)) =
        Real.rpow x (γ + ∑ i : Fin n, q (Fin.castSucc i)) := by
      calc
        _ = Real.rpow x γ * Real.rpow x (∑ i : Fin n, q (Fin.castSucc i)) := by rw [hsumPow]
        _ = Real.rpow x (γ + ∑ i : Fin n, q (Fin.castSucc i)) :=
          (Real.rpow_add hxpos γ _).symm
    have hquot :
        (Real.log (q (Fin.last n)) - γ * Real.log x) / Real.log x =
          Real.log (q (Fin.last n)) / Real.log x - γ := by
      field_simp [ne_of_gt hL]
    have hsum :
        (γ + ∑ i : Fin n, q (Fin.castSucc i)) * Real.log x ≤
          Real.log (q (Fin.last n)) := by
      have hscaled : (∑ i : Fin n, q (Fin.castSucc i)) * Real.log x ≤
          Real.log (q (Fin.last n)) - γ * Real.log x := by
        calc
          _ ≤ ((Real.log (q (Fin.last n)) - γ * Real.log x) / Real.log x) * Real.log x :=
            mul_le_mul_of_nonneg_right
              (show (∑ i : Fin n, q (Fin.castSucc i)) ≤
                  (Real.log (q (Fin.last n)) - γ * Real.log x) / Real.log x by
                rw [hquot]
                exact hsimplex) hL.le
          _ = Real.log (q (Fin.last n)) - γ * Real.log x := by
            field_simp [ne_of_gt hL]
      nlinarith [hscaled]
    rw [hpow]
    exact (Real.rpow_le_iff_le_log hxpos hy).2 hsum

private theorem roughLogProductMap_kernel_identity {n : ℕ} {L A l r : ℝ}
    (hL : 0 < L) (hA1 : 1 < A) (z : Fin (n + 1) → ℝ)
    (hz : z ∈ roughTupleSource (n := n) A l r) :
    |(LinearMap.toContinuousLinearMap
        (Matrix.toLin' (roughLogProductJac L z))).det| *
      (L⁻¹ *
        ((Real.log (roughLogProductMap L z (Fin.last n)) / L -
            ∑ i : Fin n, roughLogProductMap L z (Fin.castSucc i))⁻¹ *
          ∏ i : Fin n, (roughLogProductMap L z (Fin.castSucc i))⁻¹)) =
      ∏ i : Fin (n + 1), (Real.log (z i))⁻¹ := by
  have hzt : ∀ i, 1 < z i := fun i => lt_of_lt_of_le hA1 (hz.1 i)
  have hzpos : ∀ i, 0 < z i := fun i => lt_trans zero_lt_one (hzt i)
  have hlogpos : ∀ i, 0 < Real.log (z i) := fun i => Real.log_pos (hzt i)
  have hLne : L ≠ 0 := ne_of_gt hL
  have hqfirst (i : Fin n) :
      roughLogProductMap L z (Fin.castSucc i) =
        Real.log (z (Fin.castSucc i)) / L := by
    simp [roughLogProductMap, Fin.castSucc_ne_last]
  have hlogq : Real.log (roughLogProductMap L z (Fin.last n)) =
      ∑ i : Fin (n + 1), Real.log (z i) := by
    rw [show roughLogProductMap L z (Fin.last n) = ∏ i : Fin (n + 1), z i by
      simp [roughLogProductMap]]
    rw [Real.log_prod (fun i hi => ne_of_gt (hzpos i))]
  have hden :
      Real.log (roughLogProductMap L z (Fin.last n)) / L -
        ∑ i : Fin n, roughLogProductMap L z (Fin.castSucc i) =
      Real.log (z (Fin.last n)) / L := by
    rw [hlogq, Fin.sum_univ_castSucc]
    simp_rw [hqfirst]
    rw [← Finset.sum_div]
    field_simp [hLne]
    ring
  let P : ℝ := ∏ i : Fin n, (Real.log (z (Fin.castSucc i)))⁻¹
  have hfirstScale :
      ∏ i : Fin n, (roughLogProductMap L z (Fin.castSucc i))⁻¹ = L ^ n * P := by
    calc
      _ = ∏ i : Fin n, L * (Real.log (z (Fin.castSucc i)))⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hqfirst i]
        field_simp [hLne, ne_of_gt (hlogpos (Fin.castSucc i))]
      _ = (∏ _i : Fin n, L) * P := by
        rw [Finset.prod_mul_distrib]
      _ = L ^ n * P := by simp [P]
  have hlastScale :
      (Real.log (z (Fin.last n)) / L)⁻¹ =
        L * (Real.log (z (Fin.last n)))⁻¹ := by
    field_simp [hLne, ne_of_gt (hlogpos (Fin.last n))]
  have hkernelSplit :
      ∏ i : Fin (n + 1), (Real.log (z i))⁻¹ =
        P * ((Real.log (z (Fin.last n)))⁻¹) := by
    simp [Fin.prod_univ_castSucc, P]
    ring
  have hdet :
      |(LinearMap.toContinuousLinearMap
          (Matrix.toLin' (roughLogProductJac L z))).det| = L⁻¹ ^ n := by
    change |LinearMap.det (Matrix.toLin' (roughLogProductJac L z))| = L⁻¹ ^ n
    rw [LinearMap.det_toLin']
    exact roughLogProductJac_abs_det z hL hzpos
  have hLinvL : L⁻¹ * L = 1 := by field_simp [hLne]
  have hpowL : L⁻¹ ^ n * L ^ n = 1 := by
    rw [← mul_pow, hLinvL]
    simp
  have halgebra :
      (L⁻¹ ^ n) *
        (L⁻¹ * ((L * (Real.log (z (Fin.last n)))⁻¹) * (L ^ n * P))) =
        P * (Real.log (z (Fin.last n)))⁻¹ := by
    calc
      _ = (L⁻¹ ^ n * L ^ n) *
          ((L⁻¹ * L) * ((Real.log (z (Fin.last n)))⁻¹ * P)) := by ring
      _ = P * (Real.log (z (Fin.last n)))⁻¹ := by
        rw [hpowL, hLinvL]
        ring
  rw [hdet, hden, hlastScale, hfirstScale, hkernelSplit]
  exact halgebra

private theorem roughTupleIntegral_higher (x γ l r : ℝ) {n : ℕ}
    (hx : 2 ≤ x) (hγ : 0 < γ) (hl : Real.rpow x γ < l) (hr : l ≤ r)
    (hn : 1 ≤ n) :
    roughTupleIntegral x γ l r (n + 1) =
      (1 / Real.log x) * ∫ y in l..r,
        ArtinPrimitiveRoots.Sieve.roughDensityTerm γ
          (Real.log y / Real.log x) (n + 1) := by
  classical
  let L : ℝ := Real.log x
  let A : ℝ := Real.rpow x γ
  let S : Set (Fin (n + 1) → ℝ) := roughTupleSource A l r
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    roughLogProductMap L
  let J : (Fin (n + 1) → ℝ) →
      ((Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) := fun z =>
    LinearMap.toContinuousLinearMap (Matrix.toLin' (roughLogProductJac L z))
  let G : (Fin (n + 1) → ℝ) → ℝ := fun q =>
    L⁻¹ *
      ((Real.log (q (Fin.last n)) / L -
          ∑ i : Fin n, q (Fin.castSucc i))⁻¹ *
        ∏ i : Fin n, (q (Fin.castSucc i))⁻¹)
  let T : ℝ → Set (Fin n → ℝ) := fun y =>
    {t | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ Real.log y / L - γ}
  let K : ℝ → (Fin n → ℝ) → ℝ := fun y t =>
    (Real.log y / L - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹
  let P : Set (ℝ × (Fin n → ℝ)) :=
    {p | p.1 ∈ Set.Icc l r ∧ p.2 ∈ T p.1}
  let Gpair : ℝ × (Fin n → ℝ) → ℝ := fun p => L⁻¹ * K p.1 p.2
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hx1
  have hLne : L ≠ 0 := ne_of_gt hL
  have hA1 : 1 < A := by
    dsimp [A]
    exact Real.one_lt_rpow hx1 hγ
  have hApos : 0 < A := lt_trans zero_lt_one hA1
  have hSmeas : MeasurableSet S := by
    simpa [S] using measurableSet_roughTupleSource A l r
  have hSourceKernelDiv :
      IntegrableOn (fun z : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (z i)) S volume := by
    simpa [S] using roughTupleKernel_integrableOn_source hA1 hl hr
  have hSourceKernel :
      IntegrableOn (fun z : Fin (n + 1) → ℝ => ∏ i, (Real.log (z i))⁻¹) S volume := by
    exact hSourceKernelDiv.congr
      (Filter.Eventually.of_forall fun z => by simp [one_div])
  have hsourceEq :
      roughTupleIntegral x γ l r (n + 1) =
        (1 / ((n + 1).factorial : ℝ)) *
          ∫ z in S, ∏ i : Fin (n + 1), 1 / Real.log (z i) := by
    simpa [S, A] using roughTupleIntegral_eq_source x γ l r (n := n) hx
  have hImage : f '' S = roughTupleImage x γ l r := by
    dsimp [f, S, A]
    exact roughLogProductMap_image_eq x γ l r hx hγ
  have hInj : Set.InjOn f S := by
    dsimp [f, S]
    exact roughLogProductMap_injOn_source hL hApos
  have hderiv : ∀ z ∈ S, HasFDerivWithinAt f (J z) S z := by
    intro z hz
    have hzA : ∀ i, A ≤ z i := (show z ∈ roughTupleSource A l r from by simpa [S] using hz).1
    have hzne : ∀ i, z i ≠ 0 := fun i => ne_of_gt
      (lt_trans zero_lt_one (lt_of_lt_of_le hA1 (hzA i)))
    simpa [f, J] using
      (roughLogProductMap_hasFDerivAt (L := L) z hLne hzne).hasFDerivWithinAt
  have hkernelPoint (z : Fin (n + 1) → ℝ) (hz : z ∈ S) :
      |(J z).det| • G (f z) = ∏ i : Fin (n + 1), (Real.log (z i))⁻¹ := by
    have hz' : z ∈ roughTupleSource A l r := by simpa [S] using hz
    simpa [f, J, G, smul_eq_mul] using
      roughLogProductMap_kernel_identity hL hA1 z hz'
  have hweighted :
      IntegrableOn (fun z => |(J z).det| • G (f z)) S volume := by
    apply hSourceKernel.congr
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    exact (hkernelPoint z hz).symm
  have hGimage : IntegrableOn G (f '' S) volume :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      volume hSmeas hderiv hInj G).2 hweighted
  have hImageIntegral :
      ∫ q in f '' S, G q ∂volume =
        ∫ z in S, ∏ i : Fin (n + 1), (Real.log (z i))⁻¹ := by
    calc
      ∫ q in f '' S, G q ∂volume =
          ∫ z in S, |(J z).det| • G (f z) ∂volume :=
        MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
          volume hSmeas hderiv hInj G
      _ = ∫ z in S, ∏ i : Fin (n + 1), (Real.log (z i))⁻¹ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hSmeas] with z hz
        exact hkernelPoint z hz
  have hImageIntegralDivision :
      ∫ q in f '' S, G q ∂volume =
        ∫ z in S, ∏ i : Fin (n + 1), 1 / Real.log (z i) := by
    rw [hImageIntegral]
    apply integral_congr_ae
    filter_upwards with z
    simp [one_div]
  have hpre : e ⁻¹' P = f '' S := by
    rw [hImage, roughTupleImage_eq_logSimplex x γ l r hx hγ hl]
    ext q
    have heq : e q =
        (q (Fin.last n), fun i : Fin n => q (Fin.castSucc i)) := by
      apply Prod.ext
      · simp [e]
      · funext i
        simp [e, Fin.init]
    change (e q ∈ P) ↔ q ∈ _
    rw [heq]
    simp [P, T, L, Set.mem_Icc, and_assoc, and_left_comm, and_comm]
  have hGcomp (q : Fin (n + 1) → ℝ) : Gpair (e q) = G q := by
    simp [Gpair, G, K, e, Fin.init, hLne]
  have hGpairPre : IntegrableOn (fun q => Gpair (e q)) (e ⁻¹' P) volume := by
    rw [hpre]
    exact hGimage.congr (Filter.Eventually.of_forall fun q => (hGcomp q).symm)
  have hMP0 : MeasurePreserving e volume volume := by
    simpa [e] using
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
  have hMP : MeasurePreserving e volume (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ (Fin n → ℝ)] using hMP0
  have hGpairInt : IntegrableOn Gpair P (volume.prod volume) :=
    (hMP.integrableOn_comp_preimage e.measurableEmbedding).mp hGpairPre
  have hPairIntegral :
      ∫ p in P, Gpair p ∂(volume.prod volume) = ∫ q in f '' S, G q ∂volume := by
    calc
      ∫ p in P, Gpair p ∂(volume.prod volume) =
          ∫ q in e ⁻¹' P, Gpair (e q) ∂volume :=
        (hMP.setIntegral_preimage_emb e.measurableEmbedding Gpair P).symm
      _ = ∫ q in f '' S, G q ∂volume := by
        rw [hpre]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hGcomp
  have hTmeas (y : ℝ) : MeasurableSet (T y) := by
    have hcoords : MeasurableSet {t : Fin n → ℝ | ∀ i, γ ≤ t i} := by
      have h := MeasurableSet.iInter fun i : Fin n => by
        have hconst : Measurable (fun _ : Fin n → ℝ => γ) := measurable_const
        have happly : Measurable (fun t : Fin n → ℝ => t i) := measurable_pi_apply i
        exact measurableSet_le hconst happly
      simpa only [Set.iInter_ofPred] using h
    have hsum : Measurable (fun t : Fin n → ℝ => ∑ i, t i) := by fun_prop
    have hbound : MeasurableSet {t : Fin n → ℝ | ∑ i, t i ≤ Real.log y / L - γ} :=
      measurableSet_le hsum measurable_const
    simpa [T, Set.setOf_and] using hcoords.inter hbound
  have hPmeas : MeasurableSet P := by
    have hcoords : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ i, γ ≤ p.2 i} := by
      have h := MeasurableSet.iInter fun i : Fin n => by
        have happly : Measurable (fun p : ℝ × (Fin n → ℝ) => p.2 i) := by
          exact (measurable_pi_apply i).comp measurable_snd
        have hconst : Measurable (fun _ : ℝ × (Fin n → ℝ) => γ) := measurable_const
        exact measurableSet_le hconst happly
      simpa only [Set.iInter_ofPred] using h
    have hsum : Measurable (fun p : ℝ × (Fin n → ℝ) => ∑ i, p.2 i) := by fun_prop
    have hbound : Measurable (fun p : ℝ × (Fin n → ℝ) => Real.log p.1 / L - γ) := by fun_prop
    have hsumBound : MeasurableSet
        {p : ℝ × (Fin n → ℝ) | ∑ i, p.2 i ≤ Real.log p.1 / L - γ} :=
      measurableSet_le hsum hbound
    have hinterval : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 ∈ Set.Icc l r} :=
      measurableSet_Icc.preimage measurable_fst
    simpa [P, T, Set.setOf_and] using hinterval.inter (hcoords.inter hsumBound)
  have hGpairWhole : Integrable (P.indicator Gpair) (volume.prod volume) :=
    hGpairInt.integrable_indicator hPmeas
  have hFiber (y : ℝ) :
      ∫ t, P.indicator Gpair (y, t) ∂volume =
        if y ∈ Set.Icc l r then ∫ t in T y, Gpair (y, t) ∂volume else 0 := by
    by_cases hy : y ∈ Set.Icc l r
    · have hfun : (fun t => P.indicator Gpair (y, t)) =
          (T y).indicator (fun t => Gpair (y, t)) := by
        funext t
        have hy' : l ≤ y ∧ y ≤ r := by simpa [Set.mem_Icc] using hy
        have hmem : (y, t) ∈ P ↔ t ∈ T y := by
          simp [P, T, Set.mem_Icc, hy']
        simp only [Set.indicator]
        simp [hmem]
      rw [hfun, integral_indicator (hTmeas y)]
      simp [hy]
    · have hfun : (fun t => P.indicator Gpair (y, t)) = fun _ => 0 := by
        funext t
        have hnot : (y, t) ∉ P := by
          intro hmem
          exact hy hmem.1
        simp only [Set.indicator]
        simp [hnot]
      simp [hfun, hy]
  have hinner (y : ℝ) :
      ∫ t in T y, Gpair (y, t) ∂volume =
        L⁻¹ * ∫ t in T y, K y t ∂volume := by
    change ∫ t in T y, L⁻¹ * K y t ∂volume = _
    rw [integral_const_mul]
  have hPairIterated :
      ∫ p in P, Gpair p ∂(volume.prod volume) =
        L⁻¹ * ∫ y in l..r, ∫ t in T y, K y t ∂volume := by
    calc
      ∫ p in P, Gpair p ∂(volume.prod volume) =
          ∫ p, P.indicator Gpair p ∂(volume.prod volume) := by
        rw [← integral_indicator hPmeas]
      _ = ∫ y, ∫ t, P.indicator Gpair (y, t) ∂volume ∂volume :=
        integral_prod _ hGpairWhole
      _ = ∫ y in Set.Icc l r, ∫ t in T y, Gpair (y, t) ∂volume := by
        calc
          _ = ∫ y, if y ∈ Set.Icc l r then
                ∫ t in T y, Gpair (y, t) ∂volume else 0 := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hFiber
          _ = ∫ y in Set.Icc l r, ∫ t in T y, Gpair (y, t) ∂volume := by
            have hfun : (fun y : ℝ =>
                if y ∈ Set.Icc l r then ∫ t in T y, Gpair (y, t) ∂volume else 0) =
                (Set.Icc l r).indicator
                  (fun y => ∫ t in T y, Gpair (y, t) ∂volume) := by
              funext y
              simp [Set.indicator]
            rw [hfun, integral_indicator measurableSet_Icc]
      _ = ∫ y in Set.Icc l r, L⁻¹ * ∫ t in T y, K y t ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = L⁻¹ * ∫ y in Set.Icc l r, ∫ t in T y, K y t ∂volume := by
        rw [integral_const_mul]
      _ = L⁻¹ * ∫ y in l..r, ∫ t in T y, K y t ∂volume := by
        congr 1
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
  have hterm (y : ℝ) :
      ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / L) (n + 1) =
        (1 / ((n + 1).factorial : ℝ)) * ∫ t in T y, K y t ∂volume := by
    have hj0 : (n + 1 : ℕ) ≠ 0 := by omega
    have hj1 : (n + 1 : ℕ) ≠ 1 := by omega
    simp only [ArtinPrimitiveRoots.Sieve.roughDensityTerm,
      if_neg hj0, if_neg hj1, Nat.succ_sub_one]
    rw [integral_indicator (hTmeas y)]
    simp [T, K, one_div]
  have htermInterval :
      (1 / ((n + 1).factorial : ℝ)) *
          ∫ y in l..r, ∫ t in T y, K y t ∂volume =
        ∫ y in l..r,
          ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / L) (n + 1) := by
    rw [show (fun y => ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / L) (n + 1)) =
        (fun y => (1 / ((n + 1).factorial : ℝ)) * ∫ t in T y, K y t ∂volume) by
      funext y
      exact hterm y]
    rw [intervalIntegral.integral_const_mul]
  calc
    roughTupleIntegral x γ l r (n + 1) =
        (1 / ((n + 1).factorial : ℝ)) *
          ∫ z in S, ∏ i : Fin (n + 1), 1 / Real.log (z i) := hsourceEq
    _ = (1 / ((n + 1).factorial : ℝ)) *
          ∫ q in f '' S, G q ∂volume := by rw [← hImageIntegralDivision]
    _ = (1 / ((n + 1).factorial : ℝ)) *
          ∫ p in P, Gpair p ∂(volume.prod volume) := by rw [hPairIntegral]
    _ = (1 / ((n + 1).factorial : ℝ)) *
          (L⁻¹ * ∫ y in l..r, ∫ t in T y, K y t ∂volume) := by rw [hPairIterated]
    _ = L⁻¹ * ((1 / ((n + 1).factorial : ℝ)) *
          ∫ y in l..r, ∫ t in T y, K y t ∂volume) := by ring
    _ = L⁻¹ * ∫ y in l..r,
          ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / L) (n + 1) := by
      rw [htermInterval]
    _ = (1 / Real.log x) * ∫ y in l..r,
          ArtinPrimitiveRoots.Sieve.roughDensityTerm γ (Real.log y / Real.log x) (n + 1) := by
      simp [L]

/-- `t2:density-pushforward` — 08-type-ii.tex:272-294. -/
theorem density_pushforward (γ : ℝ) (hγ : 0 < γ) :
    ∀ x : ℝ, 2 ≤ x → ∀ j : ℕ, 1 ≤ j → ∀ l r : ℝ,
      Real.rpow x γ < l → l ≤ r →
        roughTupleIntegral x γ l r j =
          (1 / Real.log x) *
            ∫ y in l..r,
              ArtinPrimitiveRoots.Sieve.roughDensityTerm γ
                (Real.log y / Real.log x) j := by
  intro x hx j hj l r hl hr
  by_cases hj₁ : j = 1
  · subst j
    exact roughTupleIntegral_one γ hγ x hx l r hl hr
  · let n := j - 1
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hjEq : j = n + 1 := by dsimp [n]; omega
    rw [hjEq]
    exact roughTupleIntegral_higher x γ l r hx hγ hl hr hn

/-- `t2:density-regularity` — 08-type-ii.tex:296-315. Joint continuity, local Lipschitz
continuity in the second variable, and bounded variation of `w D_γ(w)`. -/
theorem density_regularity :
    ContinuousOn (fun p : ℝ × ℝ => ArtinPrimitiveRoots.Sieve.roughDensity p.1 p.2)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, w₀ ≤ u → u ≤ w₁ → w₀ ≤ v → v ≤ w₁ →
        |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤ C * |u - v|) ∧
    (∀ γ w₀ w₁ : ℝ, 0 < γ → γ < w₀ → w₀ ≤ w₁ →
      BoundedVariationOn (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w)
        (Set.uIcc w₀ w₁)) := by
  refine ⟨roughDensity_continuousOn, ?_, ?_⟩
  · intro γ w₀ w₁ hγ hγw₀ hw₀w₁
    obtain ⟨K, hLip⟩ := roughDensity_lipschitzOnCompact γ w₀ w₁ hγ hγw₀ hw₀w₁
    refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
    intro u v hu₀ hu₁ hv₀ hv₁
    have hdist := hLip.dist_le_mul u (Set.mem_Icc.mpr ⟨hu₀, hu₁⟩)
      v (Set.mem_Icc.mpr ⟨hv₀, hv₁⟩)
    rw [Real.dist_eq, Real.dist_eq] at hdist
    calc
      |ArtinPrimitiveRoots.Sieve.roughDensity γ u -
          ArtinPrimitiveRoots.Sieve.roughDensity γ v| ≤
          (K : ℝ) * |u - v| := hdist
      _ ≤ ((K : ℝ) + 1) * |u - v| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        linarith [show 0 ≤ (K : ℝ) by positivity]
  · intro γ w₀ w₁ hγ hγw₀ hw₀w₁
    obtain ⟨K, hLip⟩ := roughDensity_lipschitzOnCompact γ w₀ w₁ hγ hγw₀ hw₀w₁
    have hId : BoundedVariationOn id (Set.Icc w₀ w₁) :=
      BoundedVariationOn.id_Icc w₀ w₁
    have hDensity : BoundedVariationOn
        (fun w => ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁) := by
      simpa [Function.comp_def] using
        hLip.comp_boundedVariationOn (fun _ hx => hx) hId
    have hProduct : BoundedVariationOn
        (fun w => w * ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁) := by
      have hProduct' := hId.mul hDensity
      change BoundedVariationOn
        (fun w => (id w) * ArtinPrimitiveRoots.Sieve.roughDensity γ w) (Set.Icc w₀ w₁)
      exact hProduct'
    simpa [Set.uIcc_of_le hw₀w₁] using hProduct

/-- Clipped SW slot: a sub-sum missing at most two prime endpoints costs `+2`
over the frozen closed-interval `sw_slot` estimate. Used for half-open dyad
slots in the `low_count` box decomposition. -/
private theorem sw_slot_clipped (γ : ℝ) (hγ : 0 < γ) (A₀ A₂ : ℝ) (hA₀ : 0 < A₀)
    (hA₂ : 0 < A₂) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
          ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
            ∀ χ : DirichletCharacter ℂ k, ∀ a b : ℝ,
              P ≤ a → a ≤ b → b ≤ 2 * P →
                ∀ t : Finset ℕ, t ⊆ primesInInterval a b →
                  ((primesInInterval a b \ t).card ≤ 2) →
                    ‖∑ p ∈ t, (χ (p : ZMod k) : ℂ) -
                      (if χ = 1 then (1 : ℂ) else 0) *
                        (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ)‖ ≤
                        C * P * Real.rpow (Real.log x) (-A₂) + 2 := by
  obtain ⟨C, x₀, hC, hx₀, hbd⟩ := sw_slot γ hγ A₀ A₂ hA₀ hA₂
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x hx P hPlo hPup k hk hklog χ a b hPa hab hbP t hts hcard
  have hclosed : ‖∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ) -
      (if χ = 1 then (1 : ℂ) else 0) *
        (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ)‖ ≤
      C * P * Real.rpow (Real.log x) (-A₂) :=
    hbd x hx P hPlo hPup k hk hklog χ a b hPa hab hbP
  have hf : ∀ n ∈ primesInInterval a b \ t, ‖(χ (n : ZMod k) : ℂ)‖ ≤ 1 :=
    fun n _ => DirichletCharacter.norm_le_one χ (n : ZMod k)
  have hbase := ArtinPrimitiveRoots.Proofs.r_impl_muse.sum_subset_diff_bound
    (primesInInterval a b) t (fun p : ℕ => (χ (p : ZMod k) : ℂ)) 1
    zero_le_one hts hf hcard
  rw [mul_one] at hbase
  have hdiff : ‖∑ p ∈ t, (χ (p : ZMod k) : ℂ) -
      ∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)‖ ≤ 2 := by
    rw [norm_sub_rev]
    exact hbase
  have hsplit : (∑ p ∈ t, (χ (p : ZMod k) : ℂ)) -
      (if χ = 1 then (1 : ℂ) else 0) *
        (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ) =
      ((∑ p ∈ t, (χ (p : ZMod k) : ℂ)) -
        ∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)) +
      ((∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)) -
        (if χ = 1 then (1 : ℂ) else 0) *
          (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ)) := by
    abel
  calc ‖∑ p ∈ t, (χ (p : ZMod k) : ℂ) -
        (if χ = 1 then (1 : ℂ) else 0) *
          (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ)‖
      = ‖((∑ p ∈ t, (χ (p : ZMod k) : ℂ)) -
          ∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)) +
        ((∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)) -
          (if χ = 1 then (1 : ℂ) else 0) *
            (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ))‖ := by
        rw [hsplit]
    _ ≤ ‖(∑ p ∈ t, (χ (p : ZMod k) : ℂ)) -
          ∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)‖ +
        ‖(∑ p ∈ primesInInterval a b, (χ (p : ZMod k) : ℂ)) -
          (if χ = 1 then (1 : ℂ) else 0) *
            (∫ y in a..b, (1 / Real.log y : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ 2 + C * P * Real.rpow (Real.log x) (-A₂) :=
        add_le_add hdiff hclosed
    _ = C * P * Real.rpow (Real.log x) (-A₂) + 2 := add_comm _ _

private theorem nonprincipal_prime_tuple_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ A₀ A₂ : ℝ, 0 < A₀ → 0 < A₂ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, 0 ≤ M → 2 * M ≤ x →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, χ ≠ 1 →
                ∀ n : ℕ, ∀ l r : ℝ,
                  M ≤ l → l ≤ r → r ≤ 2 * M →
                    ‖∑ t ∈ (boundedTuples (n + 1) (⌊2 * M⌋₊ + 1)).filter
                        (fun t =>
                          (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
                          l ≤ ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ∧
                          ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ≤ r),
                      χ ((∏ i : Fin (n + 1), t i : ℕ) : ZMod k)‖ ≤
                      C * M * Real.rpow (Real.log x) (-A₂) *
                        (harmonic (⌊2 * M⌋₊ + 1) : ℝ) ^ n := by
  intro A₀ A₂ hA₀ hA₂
  obtain ⟨Csw, x₀, hCsw, hx₀, hSW⟩ := sw_slot γ hγ A₀ A₂ hA₀ hA₂
  refine ⟨12 * Csw, x₀, by positivity, hx₀, ?_⟩
  intro x hx M hM hMx k hk hkLog χ hχ n l r hl hlr hr
  have hx2 : 2 ≤ x := hx₀.trans hx
  have hxpos : 0 < x := by linarith
  have hY : 0 < Real.rpow x γ := Real.rpow_pos_of_pos hxpos _
  have hD : 0 ≤ Real.rpow (Real.log x) (-A₂) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hB : 2 * M ≤ ((⌊2 * M⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      le_of_lt (Nat.lt_floor_add_one (2 * M))
  have hclosed : ∀ N : ℝ, Real.rpow x γ / 2 ≤ N → N ≤ 2 * x →
      ∀ a b : ℝ, N ≤ a → a ≤ b → b ≤ 2 * N →
        ‖∑ p ∈ (Finset.range (⌊b⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b),
          χ (p : ZMod k)‖ ≤ 6 * N * Csw * Real.rpow (Real.log x) (-A₂) := by
    intro N hNlo hNup a b hNa hab hbN
    have hN : 0 ≤ N := (by positivity : 0 ≤ Real.rpow x γ / 2).trans hNlo
    have hbase : ‖∑ p ∈ (Finset.range (⌊b⌋₊ + 1)).filter
        (fun p : ℕ => p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b),
      χ (p : ZMod k)‖ ≤ Csw * N * Real.rpow (Real.log x) (-A₂) := by
      simpa only [primesInInterval, if_neg hχ, zero_mul, sub_zero] using
        hSW x hx N hNlo hNup k hk hkLog χ a b hNa hab hbN
    have hnonneg : 0 ≤ Csw * N * Real.rpow (Real.log x) (-A₂) :=
      mul_nonneg (mul_nonneg hCsw.le hN) hD
    calc
      _ ≤ Csw * N * Real.rpow (Real.log x) (-A₂) := hbase
      _ ≤ 6 * (Csw * N * Real.rpow (Real.log x) (-A₂)) := by linarith
      _ = 6 * N * Csw * Real.rpow (Real.log x) (-A₂) := by ring
  exact ArtinPrimitiveRoots.Proofs.r_impl_muse.prime_tuple_product_interval_character_bound
    M l r (Real.rpow x γ) (Real.rpow x γ / 2) (2 * x)
    (Real.rpow (Real.log x) (-A₂)) Csw n (⌊2 * M⌋₊ + 1) k χ
    hM hl hlr hr hB hY (by positivity) (by linarith)
    (by linarith) hD hCsw.le hclosed

private theorem roughPrimeTuple_count_reindex
    (x γ M l r : ℝ) (j k : ℕ) (χ : DirichletCharacter ℂ k)
    (hr : 0 ≤ r) :
    (∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
      (roughConvolutionTerm x γ M j m : ℂ) *
        χ (m : ZMod k)) =
      (1 / (j.factorial : ℂ)) *
        ∑ t ∈ (boundedTuples j (⌊2 * M⌋₊ + 1)).filter (fun t =>
          (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          l ≤ (∏ i : Fin j, t i : ℕ) ∧
          ((∏ i : Fin j, t i : ℕ) : ℝ) ≤ r),
          χ ((∏ i : Fin j, t i : ℕ) : ZMod k) := by
  classical
  let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
  let T : Finset (Fin j → ℕ) := boundedTuples j (⌊2 * M⌋₊ + 1)
  let factors (t : Fin j → ℕ) : Prop :=
    ∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)
  let prodN (t : Fin j → ℕ) : ℕ := ∏ i : Fin j, t i
  let c : ℂ := 1 / (j.factorial : ℂ)
  let z (m : ℕ) : ℂ := χ (m : ZMod k)
  have hterm (m : ℕ) : (roughConvolutionTerm x γ M j m : ℂ) =
      c * ∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0 := by
    simp [roughConvolutionTerm, c, T, factors, prodN, map_sum,
      Complex.ofReal_mul]
  have hrewrite :
      (∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m) =
        c * ∑ t ∈ T, ∑ m ∈ S,
          if factors t ∧ prodN t = m then z m else 0 := by
    calc
      _ = ∑ m ∈ S, c *
          (∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact congrArg (fun w : ℂ => w * z m) (hterm m)
      _ = ∑ m ∈ S, c * ∑ t ∈ T,
          (if factors t ∧ prodN t = m then z m else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        calc
          c * (∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m =
              c * ((∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m) := by ring
          _ = c * ∑ t ∈ T, (if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m := by
            rw [Finset.sum_mul]
          _ = c * ∑ t ∈ T, (if factors t ∧ prodN t = m then z m else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            split_ifs <;> simp
      _ = c * ∑ m ∈ S, ∑ t ∈ T,
          (if factors t ∧ prodN t = m then z m else 0) := by
        rw [← Finset.mul_sum]
      _ = c * ∑ t ∈ T, ∑ m ∈ S,
          (if factors t ∧ prodN t = m then z m else 0) := by rw [Finset.sum_comm]
  have hcollapse (t : Fin j → ℕ) :
      (∑ m ∈ S, if factors t ∧ prodN t = m then z m else 0) =
        if factors t ∧ prodN t ∈ S then z (prodN t) else 0 := by
    by_cases hf : factors t
    · simp only [hf, true_and]
      rw [Finset.sum_ite_eq]
    · simp [hf]
  have hS (t : Fin j → ℕ) :
      prodN t ∈ S ↔ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r := by
    constructor
    · intro ht
      exact (Finset.mem_filter.mp ht).2
    · intro h
      have hfloor : prodN t ≤ ⌊r⌋₊ := Nat.le_floor h.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor), h⟩
  have hfilters : T.filter (fun t => factors t ∧ prodN t ∈ S) =
      T.filter (fun t => factors t ∧ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r) := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hf, hmem⟩
      exact ⟨ht, hf, (hS t).mp hmem⟩
    · rintro ⟨ht, hf, hbounds⟩
      exact ⟨ht, hf, (hS t).mpr hbounds⟩
  have hrewriteCollapsed :
      (∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m) =
        c * ∑ t ∈ T,
          (if factors t ∧ prodN t ∈ S then z (prodN t) else 0) := by
    rw [hrewrite]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    exact hcollapse t
  calc
    _ = ∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m := by rfl
    _ = c * ∑ t ∈ T,
          (if factors t ∧ prodN t ∈ S then z (prodN t) else 0) := hrewriteCollapsed
    _ = c * ∑ t ∈ T.filter (fun t => factors t ∧ prodN t ∈ S), z (prodN t) := by
      rw [← Finset.sum_filter]
    _ = c * ∑ t ∈ T.filter
          (fun t => factors t ∧ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r),
          z (prodN t) := by rw [hfilters]
    _ = _ := by simp [c, z, T, factors, prodN]

set_option maxHeartbeats 2000000 in
private theorem nonprincipal_low_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ wMin wMax : ℝ, γ < wMin → wMin < wMax → wMax < 1 →
      ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * M) / Real.log x ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                  ∀ χ : DirichletCharacter ℂ k, χ ≠ 1 → ∀ l r : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M →
                      ‖∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        (roughIndicator x γ m : ℂ) * χ (m : ZMod k)‖ ≤
                        C * M * Real.rpow (Real.log x) (-A₁) := by
  intro wMin wMax hγwMin hww hw A₀ A₁ hA₀ hA₁
  have hγwMax : γ < wMax := hγwMin.trans hww
  have hwpos : 0 < wMax := hγ.trans hγwMax
  let J : ℕ := ⌊wMax / γ⌋₊
  let Ap : ℝ := A₁ + (J : ℝ) + 3
  have hAp : 0 < Ap := by dsimp [Ap]; positivity
  obtain ⟨Ct, xt, hCt, hxt, hTuples⟩ :=
    nonprincipal_prime_tuple_count γ hγ A₀ Ap hA₀ hAp
  obtain ⟨Csq, xSq, hCsq, hxSq, hSquare⟩ :=
    square_error γ wMax γ hγ hγ hγwMax
  obtain ⟨xLogBase, hLogBase⟩ := Filter.eventually_atTop.mp
    (eventually_log_ge_const (Real.log 3 + 1))
  obtain ⟨xLogPow, hLogPow⟩ := Filter.eventually_atTop.mp
    (eventually_log_rpow_le_rpow A₁ γ hγ)
  let xTail₀ := max xLogBase xLogPow
  let xTail₁ := max xSq xTail₀
  let xTail₂ := max xt xTail₁
  let x₀ := max 2 xTail₂
  let H₀ := wMax + 1
  let Cconv := Ct * ((J + 1 : ℕ) : ℝ) * H₀ ^ J
  let C₀ := Csq + Cconv
  have hCconv : 0 < Cconv := by dsimp [Cconv, H₀]; positivity
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀, x₀, hC₀, le_max_left _ _, ?_⟩
  intro x hx M hMlower hMwindow h2Mwindow k hk hmod χ hχ l r hl hlr hr
  let L := Real.log x
  let B : ℕ := ⌊2 * M⌋₊ + 1
  let Jset : Finset ℕ := Finset.Icc 1 J
  let D : ℝ := Real.rpow L (-Ap)
  let Hbar : ℝ := H₀ * L
  let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
  let z : ℕ → ℂ := fun m => χ (m : ZMod k)
  let tupleSum (j : ℕ) : ℂ :=
    ∑ t ∈ (boundedTuples j (⌊2 * M⌋₊ + 1)).filter (fun t =>
      (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
      l ≤ ((∏ i : Fin j, t i : ℕ) : ℝ) ∧
      ((∏ i : Fin j, t i : ℕ) : ℝ) ≤ r),
      χ ((∏ i : Fin j, t i : ℕ) : ZMod k)
  have hx₂ : 2 ≤ x := (le_max_left 2 xTail₂).trans hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hxTail₂ : xTail₂ ≤ x := (le_max_right 2 xTail₂).trans hx
  have hxt' : xt ≤ x := (le_max_left xt xTail₁).trans hxTail₂
  have hxTail₁ : xTail₁ ≤ x := (le_max_right xt xTail₁).trans hxTail₂
  have hxSq' : xSq ≤ x := (le_max_left xSq xTail₀).trans hxTail₁
  have hxTail₀ : xTail₀ ≤ x := (le_max_right xSq xTail₀).trans hxTail₁
  have hxLogBase' : xLogBase ≤ x := (le_max_left xLogBase xLogPow).trans hxTail₀
  have hxLogPow' : xLogPow ≤ x := (le_max_right xLogBase xLogPow).trans hxTail₀
  have hlogLower : Real.log 3 + 1 ≤ L := hLogBase x hxLogBase'
  have hLone : 1 ≤ L := by
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  have hLpos : 0 < L := by linarith
  have hMone : 1 ≤ M :=
    (Real.one_le_rpow hxone hγ.le).trans hMlower
  have hMpos : 0 < M := by linarith
  have hMlog : Real.log M ≤ wMax * L :=
    (div_le_iff₀ hLpos).mp hMwindow.2
  have hMupper : M ≤ Real.rpow x wMax := by
    have hExp := Real.exp_le_exp.mpr hMlog
    rw [Real.exp_log hMpos] at hExp
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hxpos]
    simpa only [L, mul_comm] using hExp
  have hscaleMax : 2 * M ≤ Real.rpow x wMax := by
    have hLog : Real.log (2 * M) ≤ wMax * L :=
      (div_le_iff₀ hLpos).mp h2Mwindow.2
    have hExp := Real.exp_le_exp.mpr hLog
    rw [Real.exp_log (by positivity : 0 < 2 * M)] at hExp
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hxpos]
    simpa only [L, mul_comm] using hExp
  have h2Mx : 2 * M ≤ x := by
    calc
      2 * M ≤ Real.rpow x wMax := hscaleMax
      _ ≤ Real.rpow x 1 := Real.rpow_le_rpow_of_exponent_le hxone hw.le
      _ = x := Real.rpow_one x
  have hBcast : (B : ℝ) ≤ 3 * M := by
    dsimp [B]
    push_cast
    have hf : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
    nlinarith [hf, hMone]
  have hlogM : Real.log M ≤ wMax * L := by
    calc
      Real.log M ≤ Real.log (Real.rpow x wMax) := Real.log_le_log hMpos hMupper
      _ = wMax * L := by simpa [L] using Real.log_rpow hxpos wMax
  have hlogB : Real.log (B : ℝ) ≤ Real.log (3 * M) :=
    Real.log_le_log (by positivity) hBcast
  have hHarm : (harmonic B : ℝ) ≤ Hbar := by
    calc
      (harmonic B : ℝ) ≤ 1 + Real.log (B : ℝ) := harmonic_le_one_add_log B
      _ ≤ 1 + Real.log (3 * M) := by
        calc
          1 + Real.log (B : ℝ) = Real.log (B : ℝ) + 1 := by ring
          _ ≤ Real.log (3 * M) + 1 := add_le_add_left hlogB 1
          _ = 1 + Real.log (3 * M) := by ring
      _ = 1 + Real.log 3 + Real.log M := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hMpos)]
        ring
      _ ≤ 1 + Real.log 3 + wMax * L := by
        calc
          1 + Real.log 3 + Real.log M = Real.log M + (1 + Real.log 3) := by ring
          _ ≤ wMax * L + (1 + Real.log 3) := add_le_add_left hlogM _
          _ = 1 + Real.log 3 + wMax * L := by ring
      _ ≤ L + wMax * L := by
        calc
          1 + Real.log 3 + wMax * L = (Real.log 3 + 1) + wMax * L := by ring
          _ ≤ L + wMax * L := add_le_add_left hlogLower (wMax * L)
      _ = Hbar := by dsimp [Hbar, H₀]; ring
  have hHnonneg : 0 ≤ (harmonic B : ℝ) := by
    have hq : 0 ≤ harmonic B := by
      rw [harmonic_eq_sum_Icc]
      apply Finset.sum_nonneg
      intro p hp
      positivity
    exact_mod_cast hq
  have hHbarOne : 1 ≤ Hbar := by
    dsimp [Hbar, H₀]
    nlinarith [hLone, hwpos]
  have hHpow (n : ℕ) (hn : n ≤ J) :
      (harmonic B : ℝ) ^ n ≤ Hbar ^ J := by
    calc
      (harmonic B : ℝ) ^ n ≤ Hbar ^ n :=
        pow_le_pow_left₀ hHnonneg hHarm n
      _ ≤ Hbar ^ J := pow_le_pow_right₀ hHbarOne hn
  have hDpos : 0 < D := Real.rpow_pos_of_pos hLpos _
  have hDnonneg : 0 ≤ D := hDpos.le
  have hLogPow : Real.rpow L A₁ ≤ Real.rpow x γ := by
    simpa [L] using hLogPow x hxLogPow'
  have hDecay : Real.rpow x (-γ) ≤ Real.rpow L (-A₁) := by
    have hnegx : Real.rpow x (-γ) = (Real.rpow x γ)⁻¹ :=
      Real.rpow_neg (by positivity : 0 ≤ x) γ
    have hnegL : Real.rpow L (-A₁) = (Real.rpow L A₁)⁻¹ :=
      Real.rpow_neg (by positivity : 0 ≤ L) A₁
    rw [hnegx, hnegL]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hxpos γ)
      (Real.rpow_pos_of_pos hLpos A₁)).2 hLogPow
  have hSq := hSquare x hxSq' M hMone hMlower hscaleMax
  have hSqL1 :
      (∑ m ∈ dyadicIntegers M,
        |roughIndicator x γ m - roughConvolution x γ wMax M m|) ≤
          Csq * M * Real.rpow x (-γ) := by
    have hSq' := hSq
    simp only [Nat.cast_sum] at hSq'
    exact hSq'.1.trans hSq'.2
  have hSsubset : S ⊆ dyadicIntegers M := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨_, ⟨hlm, hmr⟩⟩
    have hmUpper : (m : ℝ) ≤ 2 * M := hmr.trans hr
    have hmFloor : m ≤ ⌊2 * M⌋₊ := Nat.le_floor hmUpper
    change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
      (fun q : ℕ => M ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * M)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmFloor), ⟨hl.trans hlm, hmUpper⟩⟩
  have hzNorm (m : ℕ) : ‖z m‖ ≤ 1 := χ.norm_le_one _
  have hErr :
      ‖∑ m ∈ S, (((roughIndicator x γ m - roughConvolution x γ wMax M m : ℝ) : ℂ) * z m)‖ ≤
        Csq * M * Real.rpow (Real.log x) (-A₁) := by
    calc
      _ ≤ ∑ m ∈ S,
          ‖((roughIndicator x γ m - roughConvolution x γ wMax M m : ℝ) : ℂ) * z m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ S, |roughIndicator x γ m - roughConvolution x γ wMax M m| := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hzNorm m)
      _ ≤ ∑ m ∈ dyadicIntegers M,
          |roughIndicator x γ m - roughConvolution x γ wMax M m| :=
        Finset.sum_le_sum_of_subset_of_nonneg hSsubset (by intro m hm hmd; positivity)
      _ ≤ Csq * M * Real.rpow x (-γ) := hSqL1
      _ ≤ Csq * M * Real.rpow (Real.log x) (-A₁) := by
        exact mul_le_mul_of_nonneg_left hDecay (by positivity)
  have hRnonneg : 0 ≤ r := by linarith [hMone, hl, hlr]
  have hConvReindex :
      (∑ m ∈ S, (roughConvolution x γ wMax M m : ℂ) * z m) =
        ∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j := by
    have hcastConv (m : ℕ) : (roughConvolution x γ wMax M m : ℂ) =
        ∑ j ∈ Jset, (roughConvolutionTerm x γ M j m : ℂ) := by
      simp [roughConvolution, Jset, J]
    calc
      _ = ∑ m ∈ S,
          (∑ j ∈ Jset, (roughConvolutionTerm x γ M j m : ℂ)) * z m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact congrArg (fun w : ℂ => w * z m) (hcastConv m)
      _ = ∑ m ∈ S, ∑ j ∈ Jset,
          (roughConvolutionTerm x γ M j m : ℂ) * z m := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.sum_mul]
      _ = ∑ j ∈ Jset, ∑ m ∈ S,
          (roughConvolutionTerm x γ M j m : ℂ) * z m := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        cases j with
        | zero =>
          change 0 ∈ Finset.Icc 1 J at hj
          have h := (Finset.mem_Icc.mp hj).1
          omega
        | succ n =>
          have hRe := roughPrimeTuple_count_reindex x γ M l r (n + 1) k χ hRnonneg
          simpa only [tupleSum, z, Nat.succ_sub_one, mul_assoc] using hRe
  have hCoeffNorm (j : ℕ) : ‖(1 / (j.factorial : ℂ))‖ ≤ 1 := by
    have hjpos : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
    have hjone : 1 ≤ (j.factorial : ℝ) := by
      exact_mod_cast (Nat.one_le_of_lt (Nat.factorial_pos j))
    rw [norm_div, norm_one, show ‖(j.factorial : ℂ)‖ = (j.factorial : ℝ) by simp]
    exact (div_le_one hjpos).2 hjone
  have hOneJ (j : ℕ) (hj : j ∈ Jset) :
      ‖(1 / (j.factorial : ℂ)) * tupleSum j‖ ≤ Ct * M * D * Hbar ^ J := by
    cases j with
    | zero =>
      change 0 ∈ Finset.Icc 1 J at hj
      have h := (Finset.mem_Icc.mp hj).1
      omega
    | succ n =>
      have hnJ : n ≤ J := by
        have hj' := Finset.mem_Icc.mp hj
        omega
      have hTuple := hTuples x hxt' M hMpos.le h2Mx k hk hmod χ hχ n l r hl hlr hr
      have hTuple' : ‖tupleSum (n + 1)‖ ≤ Ct * M * D * (harmonic B : ℝ) ^ n := by
        simpa only [tupleSum, B, D, L] using hTuple
      calc
        ‖(1 / ((Nat.succ n).factorial : ℂ)) * tupleSum (Nat.succ n)‖ =
            ‖(1 / ((Nat.succ n).factorial : ℂ))‖ * ‖tupleSum (Nat.succ n)‖ := norm_mul _ _
        _ ≤ 1 * (Ct * M * D * (harmonic B : ℝ) ^ n) := by
          apply mul_le_mul (hCoeffNorm _) hTuple'
          · exact norm_nonneg _
          · positivity
        _ ≤ Ct * M * D * Hbar ^ J := by
          have hconst : 0 ≤ Ct * M * D := by positivity
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_left (hHpow n hnJ) hconst
  have hconvNorm :
      ‖∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j‖ ≤
        ((J + 1 : ℕ) : ℝ) * (Ct * M * D * Hbar ^ J) := by
    calc
      _ ≤ ∑ j ∈ Jset, ‖(1 / (j.factorial : ℂ)) * tupleSum j‖ := norm_sum_le _ _
      _ ≤ (Jset.card : ℝ) * (Ct * M * D * Hbar ^ J) := by
        simpa [nsmul_eq_mul] using
          (Finset.sum_le_card_nsmul Jset
            (fun j => ‖(1 / (j.factorial : ℂ)) * tupleSum j‖)
            (Ct * M * D * Hbar ^ J) (fun j hj => hOneJ j hj))
      _ ≤ ((J + 1 : ℕ) : ℝ) * (Ct * M * D * Hbar ^ J) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard : Jset.card ≤ J + 1 := by
          have hsubset : Jset ⊆ Finset.range (J + 1) := by
            intro j hj
            have hj' : j ∈ Finset.Icc 1 J := by simpa [Jset] using hj
            have hj'' := Finset.mem_Icc.mp hj'
            exact Finset.mem_range.mpr (by omega)
          calc
            Jset.card ≤ (Finset.range (J + 1)).card := Finset.card_le_card hsubset
            _ = J + 1 := Finset.card_range _
        exact_mod_cast hcard
  have hDpow : D * Hbar ^ J ≤ H₀ ^ J * Real.rpow L (-A₁) := by
    have hExp : -Ap + (J : ℝ) = -A₁ - 3 := by dsimp [Ap]; push_cast; ring
    calc
      D * Hbar ^ J = Real.rpow L (-Ap) * ((H₀ ^ J) * Real.rpow L (J : ℝ)) := by
        dsimp [D, Hbar]
        rw [mul_pow, Real.rpow_natCast]
      _ = H₀ ^ J * (Real.rpow L (-Ap) * Real.rpow L (J : ℝ)) := by ring
      _ = H₀ ^ J * Real.rpow L (-Ap + (J : ℝ)) := by
        congr 1
        exact (Real.rpow_add hLpos (-Ap) (J : ℝ)).symm
      _ = H₀ ^ J * Real.rpow L (-A₁ - 3) := by rw [hExp]
      _ ≤ H₀ ^ J * Real.rpow L (-A₁) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hconvBound :
      ‖∑ m ∈ S, (roughConvolution x γ wMax M m : ℂ) * z m‖ ≤
        Cconv * M * Real.rpow L (-A₁) := by
    calc
      _ = ‖∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j‖ := by rw [hConvReindex]
      _ ≤ ((J + 1 : ℕ) : ℝ) * (Ct * M * D * Hbar ^ J) := hconvNorm
      _ ≤ Cconv * M * Real.rpow L (-A₁) := by
        dsimp [Cconv]
        have hcoef : 0 ≤ ((J + 1 : ℕ) : ℝ) * Ct * M := by positivity
        calc
          ((J + 1 : ℕ) : ℝ) * (Ct * M * D * Hbar ^ J) =
              (((J + 1 : ℕ) : ℝ) * Ct * M) * (D * Hbar ^ J) := by ring
          _ ≤ (((J + 1 : ℕ) : ℝ) * Ct * M) *
                (H₀ ^ J * Real.rpow L (-A₁)) :=
              mul_le_mul_of_nonneg_left hDpow hcoef
          _ = (Ct * ((J + 1 : ℕ) : ℝ) * H₀ ^ J) *
                M * Real.rpow L (-A₁) := by ring
  have hsumIdentity :
      (∑ m ∈ S, (roughIndicator x γ m : ℂ) * z m) =
        (∑ m ∈ S, (roughConvolution x γ wMax M m : ℂ) * z m) +
          ∑ m ∈ S, (((roughIndicator x γ m - roughConvolution x γ wMax M m : ℝ) : ℂ) * z m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Complex.ofReal_sub]
    ring
  have htotal :
      ‖∑ m ∈ S, (roughIndicator x γ m : ℂ) * z m‖ ≤
        C₀ * M * Real.rpow L (-A₁) := by
    rw [hsumIdentity]
    calc
      _ ≤ ‖∑ m ∈ S, (roughConvolution x γ wMax M m : ℂ) * z m‖ +
          ‖∑ m ∈ S,
            (((roughIndicator x γ m - roughConvolution x γ wMax M m : ℝ) : ℂ) * z m)‖ := norm_add_le _ _
      _ ≤ Cconv * M * Real.rpow L (-A₁) + Csq * M * Real.rpow L (-A₁) :=
        add_le_add hconvBound hErr
      _ = C₀ * M * Real.rpow L (-A₁) := by dsimp [C₀]; ring
  simpa only [S, z, L] using htotal

private theorem principal_prime_slot_count (γ : ℝ) (hγ : 0 < γ)
    (A₂ : ℝ) (hA₂ : 0 < A₂) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ P : ℝ, Real.rpow x γ / 2 ≤ P → P ≤ 2 * x →
          ∀ a b : ℝ, P ≤ a → a ≤ b → b ≤ 2 * P →
            ∀ t : Finset ℕ, t ⊆ primesInInterval a b →
              (primesInInterval a b \ t).card ≤ 2 →
                |(t.card : ℝ) - ∫ y in a..b, (1 / Real.log y : ℝ)| ≤
                  C * P * Real.rpow (Real.log x) (-A₂) + 2 := by
  obtain ⟨C, xSW, hC, hxSW, hbd⟩ :=
    sw_slot_clipped γ hγ 1 A₂ (by norm_num) hA₂
  refine ⟨C, max xSW (Real.exp 1), hC, hxSW.trans (le_max_left _ _), ?_⟩
  intro x hx P hPlo hPup a b hPa hab hbP t hsub hmiss
  have hxSW' : xSW ≤ x := (le_max_left xSW (Real.exp 1)).trans hx
  have hxExp : Real.exp 1 ≤ x := (le_max_right xSW (Real.exp 1)).trans hx
  have hLog : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxExp
    simpa only [Real.log_exp] using h
  have hMod : ((1 : ℕ) : ℝ) ≤ Real.rpow (Real.log x) (1 : ℝ) := by
    simpa only [Nat.cast_one, Real.rpow_eq_pow, Real.rpow_one] using hLog
  have hSW := hbd x hxSW' P hPlo hPup 1 (by norm_num) hMod
    (1 : DirichletCharacter ℂ 1) a b hPa hab hbP t hsub hmiss
  have hSum : (∑ p ∈ t, (1 : DirichletCharacter ℂ 1) (p : ZMod 1)) =
      ((t.card : ℝ) : ℂ) := by
    calc
      _ = ∑ _p ∈ t, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpOne : (p : ZMod 1) = 1 := Subsingleton.elim _ _
        rw [hpOne, map_one]
      _ = ((t.card : ℝ) : ℂ) := by simp
  simpa only [hSum, if_pos (rfl : (1 : DirichletCharacter ℂ 1) = 1), ite_true,
    one_mul, intervalIntegral.integral_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hSW

set_option maxHeartbeats 1000000 in
private theorem principal_prime_slice_count (γ : ℝ) (hγ : 0 < γ)
    (A₂ : ℝ) (hA₂ : 0 < A₂) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 0 < M → 2 * M ≤ x →
          ∀ Q : ℝ, 1 ≤ Q → ∀ l r : ℝ,
            M ≤ l → l ≤ r → r ≤ 2 * M →
              |(((primesInInterval (l / Q) (r / Q)).filter
                  (fun p : ℕ => Real.rpow x γ < (p : ℝ))).card : ℝ) -
                ∫ y in Set.Icc (max (Real.rpow x γ) (l / Q)) (r / Q),
                  (1 / Real.log y : ℝ)| ≤
                C * (M / Q) * Real.rpow (Real.log x) (-A₂) := by
  -- A nonempty clipped slice lies in one dyad. An empty cutoff has both sides zero;
  -- do not replace that set integral by a reversed interval integral.
  obtain ⟨Cslot, xSlot, hCslot, hxSlot, hslot⟩ :=
    principal_prime_slot_count γ hγ A₂ hA₂
  obtain ⟨xPow, hPow⟩ := Filter.eventually_atTop.mp
    (eventually_log_rpow_le_rpow A₂ γ hγ)
  let C : ℝ := Cslot + 4
  let x₀ : ℝ := max xSlot xPow
  have hC : 0 < C := by dsimp [C]; linarith
  have hx₀ : 2 ≤ x₀ := hxSlot.trans (le_max_left _ _)
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x hx M hM hMx Q hQ l r hl hlr hr
  have hxSlot' : xSlot ≤ x := (le_max_left xSlot xPow).trans hx
  have hxPow' : xPow ≤ x := (le_max_right xSlot xPow).trans hx
  have hx2 : (2 : ℝ) ≤ x := hx₀.trans hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hscale (z : ℝ) : 2 * (z / Q) * Q = 2 * z := by
    rw [div_eq_mul_inv]
    calc
      2 * (z * Q⁻¹) * Q = 2 * z * (Q⁻¹ * Q) := by ring
      _ = 2 * z * 1 := by rw [inv_mul_cancel₀ (ne_of_gt hQpos)]
      _ = 2 * z := by ring
  let Y : ℝ := Real.rpow x γ
  let L : ℝ := Real.log x
  let D : ℝ := Real.rpow L (-A₂)
  let a : ℝ := max Y (l / Q)
  let b : ℝ := r / Q
  let P : ℝ := b / 2
  let t : Finset ℕ :=
    (primesInInterval (l / Q) (r / Q)).filter (fun p : ℕ => Y < (p : ℝ))
  have hLpos : 0 < L := Real.log_pos (by linarith : (1 : ℝ) < x)
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos γ
  have hDpos : 0 < D := by
    dsimp [D]
    exact Real.rpow_pos_of_pos hLpos (-A₂)
  have hDnonneg : 0 ≤ D := hDpos.le
  by_cases hab : a ≤ b
  · have hYb : Y ≤ b := (le_max_left Y (l / Q)).trans hab
    have hPlo : Y / 2 ≤ P := by
      dsimp [P]
      exact div_le_div_of_nonneg_right hYb (by norm_num)
    have hr2l : r ≤ 2 * l := by
      calc
        r ≤ 2 * M := hr
        _ ≤ 2 * l := mul_le_mul_of_nonneg_left hl (by norm_num)
    have hPa : P ≤ a := by
      have hhalf : b / 2 ≤ l / Q := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        have hcomm : (l / Q) * 2 = 2 * (l / Q) := by ring
        rw [hcomm]
        apply (div_le_iff₀ hQpos).2
        rw [hscale l]
        exact hr2l
      exact hhalf.trans (le_max_right Y (l / Q))
    have hPle : P ≤ M / Q := by
      dsimp [P]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      have hcomm : (M / Q) * 2 = 2 * (M / Q) := by ring
      rw [hcomm]
      apply (div_le_iff₀ hQpos).2
      rw [hscale M]
      exact hr
    have hbP : b = 2 * P := by
      dsimp [P]
      ring
    have hPup : P ≤ 2 * x := by
      dsimp [P]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      apply (div_le_iff₀ hQpos).2
      have hrle : r ≤ x := hr.trans hMx
      have hxle : x ≤ x * Q := by
        calc
          x = x * 1 := (mul_one x).symm
          _ ≤ x * Q := mul_le_mul_of_nonneg_left hQ hxpos.le
      have hxQ : x * Q ≤ (2 * x) * 2 * Q := by
        nlinarith [hxpos.le, hQpos.le]
      exact hrle.trans (hxle.trans hxQ)
    have hsubset : t ⊆ primesInInterval a b := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpI, hpY⟩
      rcases Finset.mem_filter.mp hpI with ⟨hpR, hpPrime, hlo, hhi⟩
      exact Finset.mem_filter.mpr ⟨hpR, hpPrime, max_le (le_of_lt hpY) hlo, hhi⟩
    have hcast (u : ℕ) (hu : u ∈ primesInInterval a b \ t) : (u : ℝ) = Y := by
      rcases Finset.mem_sdiff.mp hu with ⟨huA, huNot⟩
      rcases Finset.mem_filter.mp huA with ⟨huR, huPrime, hua, hub⟩
      have huNotY : ¬ Y < (u : ℝ) := by
        intro huYlt
        have hlo : l / Q ≤ (u : ℝ) := (le_max_right Y (l / Q)).trans hua
        have huI : u ∈ primesInInterval (l / Q) b :=
          Finset.mem_filter.mpr ⟨huR, huPrime, hlo, hub⟩
        exact huNot (Finset.mem_filter.mpr ⟨huI, huYlt⟩)
      exact le_antisymm (le_of_not_gt huNotY) ((le_max_left Y (l / Q)).trans hua)
    have hmiss : (primesInInterval a b \ t).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      apply Nat.cast_injective (R := ℝ)
      exact (hcast p hp).trans (hcast q hq).symm
    have hmiss2 : (primesInInterval a b \ t).card ≤ 2 :=
      le_trans hmiss (Nat.le_succ 1)
    have hslotBound :=
      hslot x hxSlot' P hPlo hPup a b hPa hab hbP.le t hsubset hmiss2
    have hint :
        (∫ y in Set.Icc a b, (1 / Real.log y : ℝ)) =
          ∫ y in a..b, (1 / Real.log y : ℝ) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rw [← hint] at hslotBound
    have hDdef : Real.rpow (Real.log x) (-A₂) = D := by
      dsimp [D, L]
    rw [hDdef] at hslotBound
    have hpow : Real.rpow L A₂ ≤ Y := hPow x hxPow'
    have hYD : (1 : ℝ) ≤ Y * D := by
      have hneg : Real.rpow L (-A₂) = (Real.rpow L A₂)⁻¹ :=
        Real.rpow_neg hLpos.le A₂
      have hinv : Y⁻¹ ≤ (Real.rpow L A₂)⁻¹ :=
        (inv_le_inv₀ hYpos (Real.rpow_pos_of_pos hLpos A₂)).2 hpow
      calc
        (1 : ℝ) = Y * Y⁻¹ := (mul_inv_cancel₀ (ne_of_gt hYpos)).symm
        _ ≤ Y * (Real.rpow L A₂)⁻¹ := mul_le_mul_of_nonneg_left hinv hYpos.le
        _ = Y * D := by rw [← hneg]
    have hhalfMass : (1 : ℝ) / 2 ≤ (M / Q) * D := by
      have hYhalf : Y / 2 ≤ M / Q := hPlo.trans hPle
      have hleft : (1 : ℝ) / 2 ≤ (Y / 2) * D := by
        have hrew : (Y / 2) * D = (Y * D) / 2 := by ring
        rw [hrew]
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith [hYD])
      exact hleft.trans (mul_le_mul_of_nonneg_right hYhalf hDnonneg)
    have htwo : (2 : ℝ) ≤ 4 * (M / Q) * D := by
      nlinarith [hhalfMass]
    have hPmass : Cslot * P * D ≤ Cslot * (M / Q) * D := by
      apply mul_le_mul_of_nonneg_right _ hDnonneg
      exact mul_le_mul_of_nonneg_left hPle hCslot.le
    calc
      |((t.card : ℝ) - ∫ y in Set.Icc a b, (1 / Real.log y : ℝ))| ≤
          Cslot * P * D + 2 := hslotBound
      _ ≤ Cslot * (M / Q) * D + 4 * (M / Q) * D := add_le_add hPmass htwo
      _ = C * (M / Q) * D := by
        dsimp [C]
        ring
  · have hba : b < a := lt_of_not_ge hab
    have hemptyT : t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpI, hpY⟩
      rcases Finset.mem_filter.mp hpI with ⟨_, _, hlo, hhi⟩
      have hge : a ≤ (p : ℝ) := max_le (le_of_lt hpY) hlo
      exact (not_lt_of_ge hge) (lt_of_le_of_lt hhi hba)
    have hint0 : ∫ y in Set.Icc a b, (1 / Real.log y : ℝ) = 0 := by
      rw [Set.Icc_eq_empty_of_lt hba, setIntegral_empty]
    have hRHS : 0 ≤ C * (M / Q) * D := by
      have hCnonneg : 0 ≤ C := hC.le
      have hMQnonneg : 0 ≤ M / Q := div_nonneg hM.le hQpos.le
      exact mul_nonneg (mul_nonneg hCnonneg hMQnonneg) hDnonneg
    calc
      |((t.card : ℝ) - ∫ y in Set.Icc a b, (1 / Real.log y : ℝ))| = 0 := by
        rw [hemptyT, hint0, Finset.card_empty, Nat.cast_zero, sub_zero, abs_zero]
      _ ≤ C * (M / Q) * D := hRHS

set_option maxHeartbeats 1000000 in
private theorem principal_tuple_kernel_integrable {n : ℕ} {A l r : ℝ}
    (hA1 : 1 < A) :
    IntegrableOn (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i))
      (roughTupleSource (n := n) A l r) volume := by
  classical
  let K : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun _ => Set.Icc A r
  have hK : IsCompact K := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsubset : roughTupleSource (n := n) A l r ⊆ K := by
    intro t ht
    simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨ht.1 i, ?_⟩
    have hprodOne (s : Finset (Fin (n + 1))) : 1 ≤ ∏ k ∈ s, t k := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert k s hks ih =>
        rw [Finset.prod_insert hks]
        have hk1 : 1 ≤ t k := le_trans hA1.le (ht.1 k)
        have hA0 : 0 ≤ A := by linarith
        have hs0 : 0 ≤ ∏ q ∈ s, t q :=
          Finset.prod_nonneg fun q _ => le_trans hA0 (ht.1 q)
        nlinarith [mul_le_mul_of_nonneg_left hk1 hs0]
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i, t k := hprodOne _
    have hprodEq : t i * ∏ k ∈ Finset.univ.erase i, t k =
        ∏ k : Fin (n + 1), t k :=
      Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i)
    have hsingle : t i ≤ ∏ k : Fin (n + 1), t k := by
      calc
        t i = t i * 1 := by ring
        _ ≤ t i * ∏ k ∈ Finset.univ.erase i, t k :=
          mul_le_mul_of_nonneg_left hrest
            (le_trans (by norm_num : 0 ≤ (1 : ℝ)) (le_trans hA1.le (ht.1 i)))
        _ = ∏ k : Fin (n + 1), t k := hprodEq
    exact hsingle.trans ht.2.2
  have hlogA : 0 < Real.log A := Real.log_pos hA1
  let F : (Fin (n + 1) → ℝ) → ℝ := fun t =>
    ∏ i : Fin (n + 1), (max (Real.log A) (Real.log (max A (t i))))⁻¹
  have hF : Continuous F := by
    unfold F
    apply continuous_finsetProd Finset.univ
    intro i hi
    have hlog : Continuous (fun t : Fin (n + 1) → ℝ => Real.log (max A (t i))) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      have hmaxAt : ContinuousAt (fun u : ℝ => max A u) (t i) :=
        (continuous_const.max continuous_id).continuousAt
      have hlogAt : ContinuousAt (fun u : ℝ => Real.log (max A u)) (t i) := by
        have hlogAt' : ContinuousAt Real.log (max A (t i)) :=
          Real.continuousAt_log
            (ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one hA1) (le_max_left A (t i))))
        exact ContinuousAt.comp (f := fun u : ℝ => max A u) (g := Real.log)
          (x := t i) hlogAt' hmaxAt
      have happly : ContinuousAt (fun u : Fin (n + 1) → ℝ => u i) t :=
        (continuous_apply i).continuousAt
      exact ContinuousAt.comp (f := fun u : Fin (n + 1) → ℝ => u i)
        (g := fun u : ℝ => Real.log (max A u)) (x := t) hlogAt happly
    have hden : Continuous (fun t : Fin (n + 1) → ℝ =>
        max (Real.log A) (Real.log (max A (t i)))) := continuous_const.max hlog
    apply hden.inv₀
    intro t
    exact ne_of_gt (lt_of_lt_of_le hlogA (le_max_left _ _))
  have hFeq : ∀ t ∈ K, F t = ∏ i : Fin (n + 1), 1 / Real.log (t i) := by
    intro t ht
    have htcoord : ∀ i, A ≤ t i := by
      have hti : ∀ i, t i ∈ Set.Icc A r := by
        simpa only [K, Set.mem_pi, Set.mem_univ, true_implies] using ht
      intro i
      exact (hti i).1
    unfold F
    apply Finset.prod_congr rfl
    intro i hi
    have hlog : Real.log A ≤ Real.log (t i) :=
      Real.log_le_log (lt_trans zero_lt_one hA1) (htcoord i)
    simp [max_eq_right (htcoord i), max_eq_right hlog]
  have hf : ContinuousOn
      (fun t : Fin (n + 1) → ℝ => ∏ i, 1 / Real.log (t i)) K :=
    hF.continuousOn.congr fun t ht => (hFeq t ht).symm
  have hsfinite : volume (roughTupleSource (n := n) A l r) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hsubset) hK.measure_lt_top)
  exact hf.integrableOn_of_subset_isCompact hK
    (measurableSet_roughTupleSource A l r) hsubset hsfinite

/-- The one-factor tuple integral is the logarithmic integral on the closed cutoff. -/
private theorem roughTupleIntegral_one_support (x γ l r : ℝ)
    (hx : 2 ≤ x) (hγ : 0 < γ) :
    roughTupleIntegral x γ l r 1 =
      ∫ y in Set.Icc (max (Real.rpow x γ) l) r, (1 / Real.log y : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hA1 : 1 < Real.rpow x γ := Real.one_lt_rpow hx1 hγ
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hcoord (y : ℝ) (i : Fin 1) : e.symm y i = y := by
    simp [e, MeasurableEquiv.piUnique_symm_apply]
  have hprod (y : ℝ) : ∏ i : Fin 1, e.symm y i = y := by
    rw [Finset.univ_unique, Finset.prod_singleton, hcoord y default]
  have hmem (y : ℝ) :
      e.symm y ∈ roughTupleSource (n := 0) (Real.rpow x γ) l r ↔
        y ∈ Set.Icc (max (Real.rpow x γ) l) r := by
    rw [roughTupleSource, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hall, hlo, hhi⟩
      have hAy : Real.rpow x γ ≤ y := by simpa [hcoord y] using hall 0
      rw [hprod y] at hlo hhi
      exact ⟨max_le hAy hlo, hhi⟩
    · rintro ⟨hmax, hhi⟩
      refine ⟨fun i => ?_, ?_, ?_⟩
      · rw [hcoord y]
        exact le_trans (le_max_left _ _) hmax
      · rw [hprod y]
        exact le_trans (le_max_right _ _) hmax
      · rw [hprod y]
        exact hhi
  have hf (y : ℝ) :
      (∏ i : Fin 1, 1 / Real.log ((e.symm y) i)) = 1 / Real.log y := by
    rw [Finset.univ_unique, Finset.prod_singleton, hcoord y default]
  rw [roughTupleIntegral_eq_source x γ l r (n := 0) hx]
  have hcoef : (1 / ((0 + 1).factorial : ℝ)) = 1 := by
    rw [Nat.zero_add, Nat.factorial_one, Nat.cast_one, div_one]
  rw [hcoef, one_mul]
  let S := roughTupleSource (n := 0) (Real.rpow x γ) l r
  let f : (Fin 1 → ℝ) → ℝ := fun t => ∏ i : Fin 1, 1 / Real.log (t i)
  let T := Set.Icc (max (Real.rpow x γ) l) r
  let g : ℝ → ℝ := fun y => 1 / Real.log y
  calc
    ∫ t in S, f t =
        ∫ t : Fin 1 → ℝ, Set.indicator S f t := by
      exact (integral_indicator (measurableSet_roughTupleSource _ _ _)).symm
    _ = ∫ y : ℝ, Set.indicator S f (e.symm y) := by
      exact ((volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm.integral_comp'
        (Set.indicator S f)).symm
    _ = ∫ y : ℝ, Set.indicator T g y := by
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only [Set.indicator]
      -- `split_ifs` names only the first copy of the second condition.
      split_ifs with hS hT
      · have := hA1
        exact hf y
      · exact absurd ((hmem y).1 hS) hT
      · rename_i hT
        exact absurd ((hmem y).2 hT) hS
      · rfl
    _ = ∫ y in T, g y :=
      integral_indicator measurableSet_Icc

/-- One-factor rough tuples are the primes in the same interval, up to the logarithmic integral. -/
private theorem principal_tuple_count_one (γ : ℝ) (hγ : 0 < γ)
    (A : ℝ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 0 < M → 2 * M ≤ x →
          ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
            |((1 / ((1 : ℕ).factorial : ℝ)) *
                (((boundedTuples 1 (⌊2 * M⌋₊ + 1)).filter (fun t =>
                  (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
                    l ≤ ((∏ i : Fin 1, t i : ℕ) : ℝ) ∧
                    ((∏ i : Fin 1, t i : ℕ) : ℝ) ≤ r)).card : ℝ)) -
              roughTupleIntegral x γ l r 1| ≤
              C * M * Real.rpow (Real.log x) (-A) := by
  obtain ⟨C, x₀, hC, hx₀, hslice⟩ := principal_prime_slice_count γ hγ A hA
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x hx M hM hMx l r hl hlr hr
  classical
  have hx2 : 2 ≤ x := hx₀.trans hx
  let B : ℕ := ⌊2 * M⌋₊ + 1
  let f : ℕ → Fin 1 → ℕ := fun p _ => p
  have hf_inj : Function.Injective f := by
    intro p q h
    exact congr_fun h 0
  have hprod (t : Fin 1 → ℕ) : ∏ i : Fin 1, t i = t 0 := by
    rw [Finset.univ_unique, Finset.prod_singleton, Fin.eq_zero (default : Fin 1)]
  have hforall (t : Fin 1 → ℕ) :
      (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ↔
        (t 0).Prime ∧ Real.rpow x γ < (t 0 : ℝ) := by
    constructor
    · intro h
      exact h 0
    · intro h i
      rw [Fin.eq_zero i]
      exact h
  have hfloor : ⌊r⌋₊ ≤ ⌊2 * M⌋₊ := Nat.floor_mono hr
  have hleB {p : ℕ} (hp : (p : ℝ) ≤ r) : p ≤ B :=
    le_trans (le_trans (Nat.le_floor hp) hfloor) (Nat.le_succ (⌊2 * M⌋₊))
  have hrange {p : ℕ} (hp : (p : ℝ) ≤ r) : p ∈ Finset.range (⌊r⌋₊ + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.le_floor hp)
  let primes := (primesInInterval l r).filter (fun p : ℕ => Real.rpow x γ < (p : ℝ))
  let tuples := (boundedTuples 1 B).filter (fun t : Fin 1 → ℕ =>
    (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
      l ≤ ((∏ i : Fin 1, t i : ℕ) : ℝ) ∧
      ((∏ i : Fin 1, t i : ℕ) : ℝ) ≤ r)
  have himage : tuples = primes.image f := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨_, hprop⟩
      rcases hprop with ⟨hall, hlo, hhi⟩
      rw [hforall t] at hall
      rw [hprod t] at hlo hhi
      refine Finset.mem_image.mpr ⟨t 0, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, hall.2⟩
        rw [primesInInterval]
        exact Finset.mem_filter.mpr ⟨hrange hhi, hall.1, hlo, hhi⟩
      · funext i
        rw [Fin.eq_zero i]
    · intro ht
      rcases Finset.mem_image.mp ht with ⟨p, hp, rfl⟩
      rcases Finset.mem_filter.mp hp with ⟨hpI, hcut⟩
      rw [primesInInterval] at hpI
      rcases Finset.mem_filter.mp hpI with ⟨_, hprime, hlo, hhi⟩
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
      · exact ArtinPrimitiveRoots.TypeII.RoughProofs.mem_boundedTuples_of_forall_le (f p) (fun _ => by
          simp only [f]
          exact hleB hhi)
      · rw [hforall (f p)]
        exact ⟨by simpa [f] using hprime, by simpa [f] using hcut⟩
      · rw [hprod (f p)]
        simpa [f] using hlo
      · rw [hprod (f p)]
        simpa [f] using hhi
  have hcard : tuples.card = primes.card := by
    rw [himage]
    exact Finset.card_image_of_injective _ hf_inj
  have hslice1 := hslice x hx M hM hMx (1 : ℝ) le_rfl l r hl hlr hr
  have hdiv (z : ℝ) : z / (1 : ℝ) = z := div_one z
  rw [hdiv l, hdiv r, hdiv M] at hslice1
  have hsupport := roughTupleIntegral_one_support x γ l r hx2 hγ
  rw [← hcard, ← hsupport] at hslice1
  have hfac :
      (1 / ((1 : ℕ).factorial : ℝ)) * (tuples.card : ℝ) = (tuples.card : ℝ) := by
    rw [Nat.factorial_one, Nat.cast_one, div_one, one_mul]
  simpa [tuples, primes, B, hfac] using hslice1

/-- Filtered ordered tuples split at the last coordinate. -/
private theorem principal_tuple_card_fiber (n B : ℕ) (Y l r : ℝ) :
    (((boundedTuples (n + 1) B).filter (fun t =>
        (∀ i, (t i).Prime ∧ Y < (t i : ℝ)) ∧
          l ≤ ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ∧
          ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ≤ r)).card : ℝ) =
      ∑ p ∈ (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧ Y < (p : ℝ)),
        (((boundedTuples n B).filter (fun s =>
            (∀ i, (s i).Prime ∧ Y < (s i : ℝ)) ∧
              l ≤ (p : ℝ) * ((∏ i : Fin n, s i : ℕ) : ℝ) ∧
              (p : ℝ) * ((∏ i : Fin n, s i : ℕ) : ℝ) ≤ r)).card : ℝ) := by
  classical
  let tuples := (boundedTuples (n + 1) B).filter (fun t =>
    (∀ i, (t i).Prime ∧ Y < (t i : ℝ)) ∧
      l ≤ ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ∧
      ((∏ i : Fin (n + 1), t i : ℕ) : ℝ) ≤ r)
  let primes := (Finset.range (B + 1)).filter (fun p : ℕ => p.Prime ∧ Y < (p : ℝ))
  let fiber (p : ℕ) := (boundedTuples n B).filter (fun s =>
    (∀ i, (s i).Prime ∧ Y < (s i : ℝ)) ∧
      l ≤ (p : ℝ) * ((∏ i : Fin n, s i : ℕ) : ℝ) ∧
      (p : ℝ) * ((∏ i : Fin n, s i : ℕ) : ℝ) ≤ r)
  let lastCoord : (Fin (n + 1) → ℕ) → ℕ := fun t => t (Fin.last n)
  have hcoord {m : ℕ} {u : Fin m → ℕ} (hu : u ∈ boundedTuples m B) (i : Fin m) : u i ≤ B := by
    unfold boundedTuples at hu
    rcases Finset.mem_image.mp hu with ⟨v, _, rfl⟩
    exact Nat.le_of_lt_succ (v i).isLt
  have hmaps : Set.MapsTo lastCoord (tuples : Set (Fin (n + 1) → ℕ)) ↑primes := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨hB, hall, _, _⟩
    have hlast := hall (Fin.last n)
    refine Finset.mem_filter.mpr ⟨?_, hlast⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hcoord hB (Fin.last n))
  have hcard_fiber (p : ℕ) (hp : p ∈ primes) :
      (tuples.filter fun t => lastCoord t = p).card = (fiber p).card := by
    rcases Finset.mem_filter.mp hp with ⟨hpI, hpPrime⟩
    have hple : p ≤ B := by
      rw [Finset.mem_range] at hpI
      exact Nat.le_of_lt_succ hpI
    apply Finset.card_nbij' (fun t => Fin.init t) (fun s => Fin.snoc s p)
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htT, hlast⟩
      rcases Finset.mem_filter.mp htT with ⟨hB, hall, hlo, hhi⟩
      have hlast' : t (Fin.last n) = p := by simpa [lastCoord] using hlast
      have hprodNat : ∏ i, t i = (∏ i : Fin n, Fin.init t i) * p := by
        rw [Fin.prod_univ_castSucc, hlast']
        simp [Fin.init]
      have hprod : ((∏ i, t i : ℕ) : ℝ) =
          (p : ℝ) * ((∏ i : Fin n, Fin.init t i : ℕ) : ℝ) := by
        rw [hprodNat, Nat.cast_mul, mul_comm]
      refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
      · exact ArtinPrimitiveRoots.TypeII.RoughProofs.mem_boundedTuples_of_forall_le
          (Fin.init t) (fun i => hcoord hB i.castSucc)
      · intro i
        exact hall i.castSucc
      · rw [hprod] at hlo
        exact hlo
      · rw [hprod] at hhi
        exact hhi
    · intro s hs
      rcases Finset.mem_filter.mp hs with ⟨hB, hall, hlo, hhi⟩
      have hprodNat :
          ∏ i, (Fin.snoc s p : Fin (n + 1) → ℕ) i = (∏ i, s i) * p :=
        Fin.prod_snoc p s
      have hprod : ((∏ i, (Fin.snoc s p : Fin (n + 1) → ℕ) i : ℕ) : ℝ) =
          (p : ℝ) * ((∏ i, s i : ℕ) : ℝ) := by
        rw [hprodNat, Nat.cast_mul, mul_comm]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, ?_⟩
        · exact ArtinPrimitiveRoots.TypeII.RoughProofs.mem_boundedTuples_of_forall_le
            (Fin.snoc s p) (fun i => by
              cases i using Fin.lastCases with
              | last =>
                rw [Fin.snoc_last]
                exact hple
              | cast j =>
                rw [Fin.snoc_castSucc]
                exact hcoord hB j)
        · intro i
          cases i using Fin.lastCases with
          | last =>
            dsimp
            rw [Fin.snoc_last]
            exact hpPrime
          | cast j =>
            dsimp
            rw [Fin.snoc_castSucc]
            exact hall j
        · dsimp
          rw [hprod]
          exact hlo
        · dsimp
          rw [hprod]
          exact hhi
      · dsimp [lastCoord]
        rw [Fin.snoc_last]
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨_, hlast⟩
      have hlast' : t (Fin.last n) = p := by simpa [lastCoord] using hlast
      rw [← hlast']
      exact Fin.snoc_init_self t
    · intro s _
      simp [Fin.init_snoc]
  have hnat : tuples.card = ∑ p ∈ primes, (fiber p).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact hcard_fiber p hp
  have hreal : (tuples.card : ℝ) = ∑ p ∈ primes, ((fiber p).card : ℝ) := by
    rw [hnat, Nat.cast_sum]
  simpa [tuples, primes, fiber] using hreal

set_option maxHeartbeats 1000000 in
/-- The supported tuple integral splits at its last coordinate. -/
private theorem principal_tuple_integral_fiber (x γ l r : ℝ) (n : ℕ)
    (hx : 2 ≤ x) (hγ : 0 < γ) :
    roughTupleIntegral x γ l r (n + 2) =
      (1 / ((n + 2 : ℕ) : ℝ)) *
        ∫ p in Set.Ioi (Real.rpow x γ),
          (1 / Real.log p) *
            roughTupleIntegral x γ (l / p) (r / p) (n + 1) := by
  classical
  let A := Real.rpow x γ
  let S := roughTupleSource (n := n + 1) A l r
  let K : (Fin (n + 2) → ℝ) → ℝ := fun t => ∏ i, 1 / Real.log (t i)
  let T (p : ℝ) := roughTupleSource (n := n) A (l / p) (r / p)
  let H : (Fin (n + 1) → ℝ) → ℝ := fun s => ∏ i, 1 / Real.log (s i)
  let e : (Fin (n + 2) → ℝ) ≃ᵐ ℝ × (Fin (n + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))
  let F : (Fin (n + 2) → ℝ) → ℝ := S.indicator K
  let G : ℝ × (Fin (n + 1) → ℝ) → ℝ := fun q => F (e.symm q)
  have hx1 : 1 < x := by linarith
  have hA1 : 1 < A := Real.one_lt_rpow hx1 hγ
  have hA0 : 0 < A := lt_trans zero_lt_one hA1
  have hSmeas : MeasurableSet S := measurableSet_roughTupleSource A l r
  have hTmeas (p : ℝ) : MeasurableSet (T p) :=
    measurableSet_roughTupleSource A (l / p) (r / p)
  have hK : IntegrableOn K S volume := principal_tuple_kernel_integrable hA1
  have hF : Integrable F volume := hK.integrable_indicator hSmeas
  have hMP0 : MeasurePreserving e volume volume := by
    simpa [e] using
      volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))
  have hMP : MeasurePreserving e volume (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod ℝ (Fin (n + 1) → ℝ)] using hMP0
  have hG : Integrable G (volume.prod volume) :=
    hMP.symm.integrable_comp_of_integrable hF
  have heSnoc (p : ℝ) (s : Fin (n + 1) → ℝ) :
      e.symm (p, s) = Fin.snoc s p := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Prod.ext
    · simp [e]
    · funext i
      simp [e]
  have hcoords (p : ℝ) (s : Fin (n + 1) → ℝ) :
      (∀ i, A ≤ (Fin.snoc s p : Fin (n + 2) → ℝ) i) ↔
        A ≤ p ∧ ∀ i, A ≤ s i := by
    constructor
    · intro hs
      exact ⟨by simpa using hs (Fin.last (n + 1)),
        fun i => by simpa using hs i.castSucc⟩
    · rintro ⟨hp, hs⟩ i
      cases i using Fin.lastCases with
      | last => simpa using hp
      | cast j => simpa using hs j
  have hmem (p : ℝ) (s : Fin (n + 1) → ℝ) :
      e.symm (p, s) ∈ S ↔ A ≤ p ∧ s ∈ T p := by
    rw [heSnoc]
    change ((∀ i, A ≤ (Fin.snoc s p : Fin (n + 2) → ℝ) i) ∧
      l ≤ ∏ i, Fin.snoc s p i ∧ (∏ i, Fin.snoc s p i) ≤ r) ↔
        A ≤ p ∧ (∀ i, A ≤ s i) ∧ l / p ≤ ∏ i, s i ∧ (∏ i, s i) ≤ r / p
    rw [hcoords, Fin.prod_snoc]
    by_cases hp : A ≤ p
    · have hp0 : 0 < p := lt_of_lt_of_le hA0 hp
      rw [div_le_iff₀ hp0, le_div_iff₀ hp0]
      simp only [hp, true_and]
    · simp only [hp, false_and]
  have hkernel (p : ℝ) (s : Fin (n + 1) → ℝ) :
      K (e.symm (p, s)) = (1 / Real.log p) * H s := by
    rw [heSnoc]
    dsimp [K, H]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_comm]
  have hinner (p : ℝ) :
      ∫ s, G (p, s) =
        if A ≤ p then (1 / Real.log p) * ∫ s in T p, H s else 0 := by
    by_cases hp : A ≤ p
    · have hfun : (fun s => G (p, s)) =
          (fun s => (1 / Real.log p) * (T p).indicator H s) := by
        funext s
        change S.indicator K (e.symm (p, s)) = _
        simp only [Set.indicator, hmem, hp, true_and]
        by_cases hs : s ∈ T p
        · simp only [hs, ite_true, hkernel]
        · simp only [hs, ite_false, mul_zero]
      rw [hfun, integral_const_mul, integral_indicator (hTmeas p)]
      simp only [hp, ite_true]
    · have hfun : (fun s => G (p, s)) = fun _ => 0 := by
        funext s
        change S.indicator K (e.symm (p, s)) = 0
        simp only [Set.indicator, hmem, hp, false_and, ite_false]
      rw [hfun]
      simp only [integral_zero, hp, ite_false]
  have hPair : ∫ q, G q ∂(volume.prod volume) =
      ∫ p in Set.Ioi A, (1 / Real.log p) * ∫ s in T p, H s := by
    calc
      _ = ∫ p, ∫ s, G (p, s) := integral_prod G hG
      _ = ∫ p, if A ≤ p then (1 / Real.log p) * ∫ s in T p, H s else 0 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hinner
      _ = ∫ p in Set.Ici A, (1 / Real.log p) * ∫ s in T p, H s := by
        have hfun : (fun p : ℝ =>
            if A ≤ p then (1 / Real.log p) * ∫ s in T p, H s else 0) =
            (Set.Ici A).indicator (fun p => (1 / Real.log p) * ∫ s in T p, H s) := by
          funext p
          simp only [Set.indicator, Set.mem_Ici]
        rw [hfun, integral_indicator measurableSet_Ici]
      _ = ∫ p in Set.Ioi A, (1 / Real.log p) * ∫ s in T p, H s :=
        integral_Ici_eq_integral_Ioi
  have hSource : ∫ t in S, K t = ∫ q, G q ∂(volume.prod volume) := by
    rw [← integral_indicator hSmeas]
    exact (hMP.symm.integral_comp' F).symm
  have hNormalize :
      (∫ p in Set.Ioi A, (1 / Real.log p) *
          roughTupleIntegral x γ (l / p) (r / p) (n + 1)) =
        (1 / ((n + 1).factorial : ℝ)) *
          ∫ p in Set.Ioi A, (1 / Real.log p) * ∫ s in T p, H s := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => by
      dsimp only
      rw [roughTupleIntegral_eq_source x γ (l / p) (r / p) (n := n) hx]
      change (1 / Real.log p) *
        ((1 / ((n + 1).factorial : ℝ)) * ∫ s in T p, H s) = _
      ring
  have hfac : (n + 2).factorial = (n + 2) * (n + 1).factorial :=
    Nat.factorial_succ (n + 1)
  have hcoef : (1 / ((n + 2).factorial : ℝ)) =
      (1 / ((n + 2 : ℕ) : ℝ)) * (1 / ((n + 1).factorial : ℝ)) := by
    rw [hfac, Nat.cast_mul]
    simp only [one_div, mul_inv_rev, mul_comm]
  rw [roughTupleIntegral_eq_source x γ l r (n := n + 1) hx]
  change (1 / ((n + 2).factorial : ℝ)) * (∫ t in S, K t) = _
  rw [hSource, hPair, hcoef, hNormalize]
  ring

/-- One-factor tuple counts retain the global truncation under a tail scale. -/
private theorem principal_tuple_count_one_scaled (γ : ℝ) (hγ : 0 < γ)
    (A : ℝ) (hA : 0 < A) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        ∀ M : ℝ, 0 < M → 2 * M ≤ x →
          ∀ Q : ℝ, 1 ≤ Q → ∀ l r : ℝ,
            M ≤ l → l ≤ r → r ≤ 2 * M →
              |((1 / ((1 : ℕ).factorial : ℝ)) *
                  (((boundedTuples 1 (⌊2 * M⌋₊ + 1)).filter (fun t =>
                    (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
                      l / Q ≤ ((∏ i : Fin 1, t i : ℕ) : ℝ) ∧
                      ((∏ i : Fin 1, t i : ℕ) : ℝ) ≤ r / Q)).card : ℝ)) -
                roughTupleIntegral x γ (l / Q) (r / Q) 1| ≤
                C * (M / Q) * Real.rpow (Real.log x) (-A) := by
  obtain ⟨C, x₀, hC, hx₀, hCount⟩ := principal_tuple_count_one γ hγ A hA
  refine ⟨C, x₀, hC, hx₀, ?_⟩
  intro x hx M hM hMx Q hQ l r hl hlr hr
  classical
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hMQ : 0 < M / Q := div_pos hM hQ0
  have hScale : 2 * (M / Q) ≤ 2 * M := by
    calc
      2 * (M / Q) = (2 * M) / Q := by ring
      _ ≤ 2 * M := div_le_self (by positivity) hQ
  have hLo : M / Q ≤ l / Q := div_le_div_of_nonneg_right hl hQ0.le
  have hLr : l / Q ≤ r / Q := div_le_div_of_nonneg_right hlr hQ0.le
  have hHi : r / Q ≤ 2 * (M / Q) := by
    calc
      r / Q ≤ (2 * M) / Q := div_le_div_of_nonneg_right hr hQ0.le
      _ = 2 * (M / Q) := by ring
  have hprod (t : Fin 1 → ℕ) : ∏ i : Fin 1, t i = t 0 := by
    rw [Finset.univ_unique, Finset.prod_singleton, Fin.eq_zero (default : Fin 1)]
  have hBounded (t : Fin 1 → ℕ) (R : ℝ)
      (ht : ((∏ i : Fin 1, t i : ℕ) : ℝ) ≤ R) :
      t ∈ boundedTuples 1 (⌊R⌋₊ + 1) := by
    apply ArtinPrimitiveRoots.TypeII.RoughProofs.mem_boundedTuples_of_forall_le
    intro i
    rw [Fin.eq_zero i]
    rw [hprod t] at ht
    exact (Nat.le_floor ht).trans (Nat.le_succ _)
  let P (t : Fin 1 → ℕ) :=
    (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
      l / Q ≤ ((∏ i : Fin 1, t i : ℕ) : ℝ) ∧
      ((∏ i : Fin 1, t i : ℕ) : ℝ) ≤ r / Q
  have hFilters :
      (boundedTuples 1 (⌊2 * M⌋₊ + 1)).filter P =
        (boundedTuples 1 (⌊2 * (M / Q)⌋₊ + 1)).filter P := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨_, htP⟩
      exact Finset.mem_filter.mpr ⟨hBounded t _ (htP.2.2.trans hHi), htP⟩
    · intro ht
      rcases Finset.mem_filter.mp ht with ⟨_, htP⟩
      exact Finset.mem_filter.mpr ⟨hBounded t _ (htP.2.2.trans (hHi.trans hScale)), htP⟩
  have h := hCount x hx (M / Q) hMQ (hScale.trans hMx)
    (l / Q) (r / Q) hLo hLr hHi
  change |((1 / ((1 : ℕ).factorial : ℝ)) *
      (((boundedTuples 1 (⌊2 * (M / Q)⌋₊ + 1)).filter P).card : ℝ)) -
      roughTupleIntegral x γ (l / Q) (r / Q) 1| ≤
        C * (M / Q) * Real.rpow (Real.log x) (-A) at h
  rw [← hFilters] at h
  exact h

/-- `t2:low-count` — 08-type-ii.tex:373-427, `eq:rough-convolution-low-count`. Correction 4
from review lane `rev-b` restricts uniformity to its fixed exponent window. -/
theorem low_count (γ : ℝ) (hγ : 0 < γ) :
    ∀ wMin wMax : ℝ, γ < wMin → wMin < wMax → wMax < 1 →
      ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * M) / Real.log x ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                  ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M →
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          (roughIndicator x γ m : ℂ) * χ (m : ZMod k)) -
                        (if χ = 1 then
                          ((1 / Real.log x) *
                            ∫ y in l..r, ArtinPrimitiveRoots.Sieve.roughDensity γ
                              (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
                        C * M * Real.rpow (Real.log x) (-A₁) := by
  sorry

/-- Uniform rough counts on a bounded exponent window, without an upper bound of one. -/
private theorem low_count_bounded_window (γ vMin vMax : ℝ)
    (hγ : 0 < γ) (hγv : γ < vMin) (hvv : vMin < vMax) :
    ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x γ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc vMin vMax →
            Real.log (2 * M) / Real.log x ∈ Set.Icc vMin vMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ l r : ℝ,
                M ≤ l → l ≤ r → r ≤ 2 * M →
                  ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
                        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                      (roughIndicator x γ m : ℂ) * χ (m : ZMod k)) -
                    (if χ = 1 then
                      ((1 / Real.log x) * ∫ y in l..r,
                        ArtinPrimitiveRoots.Sieve.roughDensity γ
                          (Real.log y / Real.log x) : ℝ) else 0 : ℂ)‖ ≤
                    C * M * Real.rpow (Real.log x) (-A₁) := by
  intro A₀ A₁ hA₀ hA₁
  let c : ℝ := vMax + 1
  have hc : 1 < c := by dsimp [c]; linarith
  have hcpos : 0 < c := lt_trans zero_lt_one hc
  have hγ' : 0 < γ / c := div_pos hγ hcpos
  have hγv' : γ / c < vMin / c := div_lt_div_of_pos_right hγv hcpos
  have hvv' : vMin / c < vMax / c := div_lt_div_of_pos_right hvv hcpos
  have hvMax' : vMax / c < 1 := by
    apply (div_lt_iff₀ hcpos).2
    dsimp [c]
    linarith
  obtain ⟨C, X₀, hC, _, hbase⟩ :=
    low_count (γ / c) hγ' (vMin / c) (vMax / c) hγv' hvv' hvMax' A₀ A₁ hA₀ hA₁
  have hbase' : ArtinPrimitiveRoots.Proofs.r_impl_muse.roughCountBound
      (γ / c) (vMin / c) (vMax / c) A₀ A₁ C X₀ := by
    simpa only [ArtinPrimitiveRoots.Proofs.r_impl_muse.roughCountBound,
      roughIndicator] using hbase
  refine ⟨C, max 2 X₀, hC, le_max_left _ _, ?_⟩
  simpa only [ArtinPrimitiveRoots.Proofs.r_impl_muse.roughCountBound,
    roughIndicator] using
    (ArtinPrimitiveRoots.Proofs.r_impl_muse.rough_count_rescale
      γ vMin vMax A₀ A₁ C X₀ c (le_of_lt hc) (le_of_lt hA₀)
      (le_of_lt hA₁) (le_of_lt hC) hbase')

/-- `t2:low-frequency` — 08-type-ii.tex:439-453. -/
theorem low_frequency (γ wMin wMax C δ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax) (hδ : 0 < δ)
    (hC : 0 < C) :
    ∀ A₀ A B₂ : ℝ, 0 < A₀ → 0 < A → 0 < B₂ →
      ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x δ ≤ M →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
              ∀ v t : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                |t| ≤ Real.rpow (Real.log x) B₂ →
                  ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
                    ∀ χ : DirichletCharacter ℂ k,
                      ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                          roughCoefficient x γ v m * χ (m : ZMod k) *
                            Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                        C₀ * Real.rpow (Real.log x) (-A) := by
  have hwide : wMin < wMax + 1 := by linarith
  have hcounts : ∀ A₀ A₁ : ℝ, 0 < A₀ → 0 < A₁ →
      ∃ Cc xc : ℝ, 0 < Cc ∧ 2 ≤ xc ∧
        ArtinPrimitiveRoots.Proofs.r_impl_muse.roughCountBound
          γ wMin (wMax + 1) A₀ A₁ Cc xc := by
    intro A₀ A₁ hA₀ hA₁
    obtain ⟨Cc, xc, hCc, hxc, hbase⟩ :=
      low_count_bounded_window γ wMin (wMax + 1) hγ hγw hwide A₀ A₁ hA₀ hA₁
    refine ⟨Cc, xc, hCc, hxc, ?_⟩
    simpa only [ArtinPrimitiveRoots.Proofs.r_impl_muse.roughCountBound,
      roughIndicator] using hbase
  have hdensity : ∃ K : ℝ, 0 < K ∧
      ∀ s ∈ Set.Icc wMin (wMax + 1), ∀ t ∈ Set.Icc wMin (wMax + 1),
        |ArtinPrimitiveRoots.Sieve.roughDensity γ s -
          ArtinPrimitiveRoots.Sieve.roughDensity γ t| ≤ K * |s - t| := by
    obtain ⟨K, hK, hLip⟩ := density_regularity.2.1 γ wMin (wMax + 1) hγ hγw hwide.le
    exact ⟨K, hK, fun s hs t ht => hLip s t hs.1 hs.2 ht.1 ht.2⟩
  intro A₀ A B₂ hA₀ hA hB₂
  obtain ⟨C₀, x₀, hC₀, hx₀, hbound⟩ :=
    ArtinPrimitiveRoots.Proofs.r_impl_muse.low_frequency_from_counts
      γ wMin wMax C δ hγ hγw hw hδ hC hcounts hdensity A₀ A B₂ hA₀ hA hB₂
  refine ⟨C₀, x₀, hC₀, hx₀, ?_⟩
  intro x hx M hMx hwM l r hl hlr hr v t hv ht k hk hklog χ
  have hsum :
      (∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter
        (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
        roughCoefficient x γ v m * χ (m : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) =
      ∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter
        (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
        (((if roughAbove m (Real.rpow x γ) then 1 else 0 : ℝ) : ℂ) *
          χ (m : ZMod k) * Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ)) -
          (if roughAbove m (roughCutoff x) then χ (m : ZMod k) else 0) *
            ((ArtinPrimitiveRoots.Sieve.roughDensity γ (Real.log (m : ℝ) / Real.log x) /
              (Real.log x * roughSieveProduct (roughCutoff x)) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (t + v) * Real.log (m : ℝ))) := by
    apply Finset.sum_congr rfl
    intro m _hm
    rw [roughCoefficient_phase_split]
    simp only [roughIndicator, roughProxy, roughDensity]
    by_cases hW : roughAbove m (roughCutoff x)
    · simp only [hW, ite_true, mul_one]
      ring
    · simp only [hW, ite_false, mul_zero, zero_mul, Complex.ofReal_zero, sub_zero]
  rw [hsum]
  exact hbound x hx M hMx hwM l r hl hlr hr v t hv ht k hk hklog χ

private theorem isNatInterval_of_real_bounds (a y b : ℝ) :
    IsNatInterval {p : ℕ | a ≤ (p : ℝ) ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ b} := by
  intro m n k hm hn hmin hmax
  rcases hm with ⟨hma, hmy, hmb⟩
  rcases hn with ⟨hna, hny, hnb⟩
  rcases le_total m n with hmn | hnm
  · have hmk : m ≤ k := by simpa [min_eq_left hmn] using hmin
    have hkn : k ≤ n := by simpa [max_eq_right hmn] using hmax
    have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    exact ⟨hma.trans hmkR, lt_of_lt_of_le hmy hmkR, hknR.trans hnb⟩
  · have hnk : n ≤ k := by simpa [min_eq_right hnm] using hmin
    have hkm : k ≤ m := by simpa [max_eq_left hnm] using hmax
    have hnkR : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    exact ⟨hna.trans hnkR, lt_of_lt_of_le hny hnkR, hkmR.trans hmb⟩

private noncomputable def roughPhase (u : ℝ) (m : ℕ) : ℂ :=
  phaseNat u m

private theorem roughPhase_mul_nat (u : ℝ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    roughPhase u (m * n) = roughPhase u m * roughPhase u n := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold roughPhase ArtinPrimitiveRoots.Proofs.RImplP.RPrime.phaseNat
  rw [← Complex.exp_add]
  congr 1
  rw [Nat.cast_mul, Real.log_mul hmR.ne' hnR.ne']
  push_cast
  ring

private theorem char_roughPhase_mul_nat (k : ℕ) (χ : DirichletCharacter ℂ k)
    (u : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (χ ((m * n : ℕ) : ZMod k) : ℂ) * roughPhase u (m * n) =
      ((χ (m : ZMod k) : ℂ) * roughPhase u m) *
        ((χ (n : ZMod k) : ℂ) * roughPhase u n) := by
  have hχ : χ ((m * n : ℕ) : ZMod k) = χ (m : ZMod k) * χ (n : ZMod k) := by
    rw [Nat.cast_mul, map_mul]
  rw [hχ, roughPhase_mul_nat u m n hm hn]
  ring

private theorem prime_exists_rpow_ge (a K : ℝ) (ha : 0 < a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → K ≤ Real.rpow x a := by
  have hlim : Filter.Tendsto (fun x : ℝ => Real.rpow x a) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop ha
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop K)
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  exact hx₁ x ((le_max_right 2 x₁).trans hx)

private theorem prime_exists_log_rpow_le_const_mul_x_rpow
    (a b K : ℝ) (hb : 0 < b) (hK : 0 < K) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.rpow (Real.log x) a ≤ K * Real.rpow x b := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) a / Real.rpow x b)
      Filter.atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.rpow (Real.log x) a / Real.rpow x b‖ < K := by
    have hball := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hK)
    filter_upwards [hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x₁ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx₁' : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := (le_max_right x₁ 2).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hden : 0 < Real.rpow x b := Real.rpow_pos_of_pos hxpos _
  have hquot := hx₁ x hx₁'
  have hqnonneg : 0 ≤ Real.rpow (Real.log x) a / Real.rpow x b :=
    div_nonneg (Real.rpow_nonneg hlog _) hden.le
  have hquot' : Real.rpow (Real.log x) a / Real.rpow x b < K := by
    have hquotAbs : |Real.rpow (Real.log x) a / Real.rpow x b| < K := by
      simpa only [Real.norm_eq_abs] using hquot
    have hquotAbsDiv : |Real.rpow (Real.log x) a| / |Real.rpow x b| < K := by
      simpa only [abs_div] using hquotAbs
    have hnum : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog _
    simpa only [abs_of_nonneg hnum, abs_of_pos hden] using hquotAbsDiv
  exact le_of_lt ((div_lt_iff₀ hden).mp hquot')

private theorem roughPrimeTuple_interval_reindex
    (x γ M l r : ℝ) (j k : ℕ) (χ : DirichletCharacter ℂ k) (u : ℝ)
    (hr : 0 ≤ r) :
    (∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ =>
        l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
      (roughConvolutionTerm x γ M j m : ℂ) *
        (χ (m : ZMod k) : ℂ) * roughPhase u m) =
      (1 / (j.factorial : ℂ)) *
        ∑ t ∈ (boundedTuples j (⌊2 * M⌋₊ + 1)).filter (fun t =>
          (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          l ≤ (∏ i : Fin j, t i : ℕ) ∧
          ((∏ i : Fin j, t i : ℕ) : ℝ) ≤ r),
          (χ ((∏ i : Fin j, t i : ℕ) : ZMod k) : ℂ) *
            roughPhase u (∏ i : Fin j, t i : ℕ) := by
  classical
  let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
  let T : Finset (Fin j → ℕ) := boundedTuples j (⌊2 * M⌋₊ + 1)
  let factors (t : Fin j → ℕ) : Prop :=
    ∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)
  let prodN (t : Fin j → ℕ) : ℕ := ∏ i : Fin j, t i
  let c : ℂ := 1 / (j.factorial : ℂ)
  let z (m : ℕ) : ℂ := (χ (m : ZMod k) : ℂ) * roughPhase u m
  have hterm (m : ℕ) : (roughConvolutionTerm x γ M j m : ℂ) =
      c * ∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0 := by
    simp [roughConvolutionTerm, c, T, factors, prodN, map_sum,
      Complex.ofReal_mul]
  have hrewrite :
      (∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m) =
        c * ∑ t ∈ T, ∑ m ∈ S,
          if factors t ∧ prodN t = m then z m else 0 := by
    calc
      _ = ∑ m ∈ S, c *
          (∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m := by
        apply Finset.sum_congr rfl
        intro m hm
        exact congrArg (fun w : ℂ => w * z m) (hterm m)
      _ = ∑ m ∈ S, c * ∑ t ∈ T,
          (if factors t ∧ prodN t = m then z m else 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        calc
          c * (∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m =
              c * ((∑ t ∈ T, if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m) := by ring
          _ = c * ∑ t ∈ T, (if factors t ∧ prodN t = m then (1 : ℂ) else 0) * z m := by
            rw [Finset.sum_mul]
          _ = c * ∑ t ∈ T, (if factors t ∧ prodN t = m then z m else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro t ht
            split_ifs <;> simp
      _ = c * ∑ m ∈ S, ∑ t ∈ T,
          (if factors t ∧ prodN t = m then z m else 0) := by
        rw [← Finset.mul_sum]
      _ = c * ∑ t ∈ T, ∑ m ∈ S,
          (if factors t ∧ prodN t = m then z m else 0) := by rw [Finset.sum_comm]
  have hcollapse (t : Fin j → ℕ) :
      (∑ m ∈ S, if factors t ∧ prodN t = m then z m else 0) =
        if factors t ∧ prodN t ∈ S then z (prodN t) else 0 := by
    by_cases hf : factors t
    · simp only [hf, true_and]
      rw [Finset.sum_ite_eq]
    · simp [hf]
  have hS (t : Fin j → ℕ) :
      prodN t ∈ S ↔ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r := by
    constructor
    · intro ht
      exact (Finset.mem_filter.mp ht).2
    · intro h
      have hfloor : prodN t ≤ ⌊r⌋₊ := Nat.le_floor h.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hfloor), h⟩
  have hfilters : T.filter (fun t => factors t ∧ prodN t ∈ S) =
      T.filter (fun t => factors t ∧ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r) := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hf, hmem⟩
      exact ⟨ht, hf, (hS t).mp hmem⟩
    · rintro ⟨ht, hf, hbounds⟩
      exact ⟨ht, hf, (hS t).mpr hbounds⟩
  have hrewriteCollapsed :
      (∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m) =
        c * ∑ t ∈ T,
          (if factors t ∧ prodN t ∈ S then z (prodN t) else 0) := by
    rw [hrewrite]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    exact hcollapse t
  calc
    _ = ∑ m ∈ S, (roughConvolutionTerm x γ M j m : ℂ) * z m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [z]
      ring
    _ = c * ∑ t ∈ T,
          (if factors t ∧ prodN t ∈ S then z (prodN t) else 0) := hrewriteCollapsed
    _ = c * ∑ t ∈ T.filter (fun t => factors t ∧ prodN t ∈ S), z (prodN t) := by
      rw [← Finset.sum_filter]
    _ = c * ∑ t ∈ T.filter
          (fun t => factors t ∧ l ≤ (prodN t : ℝ) ∧ (prodN t : ℝ) ≤ r),
          z (prodN t) := by rw [hfilters]
    _ = _ := by simp [c, z, T, factors, prodN]

set_option maxHeartbeats 4000000 in
/-- `t2:prime-high` — 08-type-ii.tex:455-480. -/
theorem prime_high (γ wMax : ℝ) (hγ : 0 < γ) (hw : wMax < 1) :
    ∀ τ θ A₀ A₃ : ℝ, 0 < τ → τ < γ → wMax < θ → θ < 1 →
      0 < A₀ → 0 < A₃ →
      ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M : ℝ, Real.rpow x τ / 2 ≤ M → M ≤ Real.rpow x θ →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) A₀ →
              ∀ χ : DirichletCharacter ℂ k, ∀ u : ℝ,
                Real.rpow (Real.log x) B₀ ≤ |u| → |u| ≤ Real.rpow x 2 →
                  ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
                          Complex.exp (Complex.I * u * Real.log (m : ℝ)))‖ ≤
                      C₀ * M * Real.rpow (Real.log x) (-A₃) := by
  intro τ θ A₀ A₃ hτ hτγ hwθ hθ hA₀ hA₃
  by_cases hθτ : θ < τ
  · have hgap : 0 < τ - θ := by linarith
    obtain ⟨xgap, hxgap, hgapPow⟩ := prime_exists_rpow_ge (τ - θ) 3 hgap
    let x₀ := max 2 xgap
    refine ⟨1, 1, x₀, by norm_num, by norm_num, le_max_left _ _, ?_⟩
    intro x hx M hMlower hMupper
    have hxgap' : xgap ≤ x := (le_max_right 2 xgap).trans hx
    have hxpos : 0 < x := by linarith [show 2 ≤ x from le_trans (le_max_left 2 xgap) hx]
    have hθpow : 0 < Real.rpow x θ := Real.rpow_pos_of_pos hxpos _
    have hfactor : Real.rpow x τ = Real.rpow x θ * Real.rpow x (τ - θ) := by
      calc
        Real.rpow x τ = Real.rpow x (θ + (τ - θ)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hxpos θ (τ - θ)
    have hgapStrict : 2 * Real.rpow x θ < Real.rpow x τ := by
      rw [hfactor]
      have hmul := mul_le_mul_of_nonneg_left (hgapPow x hxgap')
        (Real.rpow_nonneg hxpos.le θ)
      have htwothree : 2 * Real.rpow x θ < 3 * Real.rpow x θ := by nlinarith [hθpow]
      calc
        2 * Real.rpow x θ < 3 * Real.rpow x θ := htwothree
        _ = Real.rpow x θ * 3 := by ring
        _ ≤ Real.rpow x θ * Real.rpow x (τ - θ) := hmul
    have hscaleLo : Real.rpow x τ ≤ 2 * M := by
      have hpow := Real.rpow_nonneg hxpos.le τ
      nlinarith [hMlower]
    have hscaleHi : 2 * M ≤ 2 * Real.rpow x θ := by nlinarith [hMupper]
    exact False.elim (not_le_of_gt hgapStrict (hscaleLo.trans hscaleHi))
  · have hτθ : τ ≤ θ := le_of_not_gt hθτ
    have hθpos : 0 < θ := lt_of_lt_of_le hτ hτθ
    let E := (θ + 1) / 2
    let η := (E + 1) / 2
    have hθE : θ < E := by dsimp [E]; linarith [hθ]
    have hE1 : E < 1 := by dsimp [E]; linarith [hθ]
    have hEη : E < η := by dsimp [η]; linarith [hE1]
    have hη1 : η < 1 := by dsimp [η]; linarith [hE1]
    have hτslot : 0 < τ / 2 := by positivity
    have hτslotη : τ / 2 < η := by
      have hτhalf : τ / 2 < 1 / 2 := by linarith [hτθ, hθ]
      have hηhalf : (1 / 2 : ℝ) < η := by dsimp [η, E]; linarith [hθpos]
      exact hτhalf.trans hηhalf
    by_cases hEγ : E ≤ γ
    · obtain ⟨xgap, hxgap, hgapPow⟩ :=
        prime_exists_rpow_ge (E - θ) 3 (sub_pos.mpr hθE)
      obtain ⟨xτ, hxτ, hτPow⟩ := prime_exists_rpow_ge τ 4 hτ
      let x₀ := max 2 (max xgap xτ)
      refine ⟨1, 1, x₀, by norm_num, by norm_num, le_max_left _ _, ?_⟩
      intro x hx M hMlower hMupper k hk hmod χ u huLower huUpper l r hl hlr hr
      have hx2 : 2 ≤ x := (le_max_left 2 (max xgap xτ)).trans hx
      have hxpos : 0 < x := by linarith
      have hxone : 1 ≤ x := by linarith
      have hxgap' : xgap ≤ x :=
        (le_max_left xgap xτ).trans ((le_max_right 2 (max xgap xτ)).trans hx)
      have hxτ' : xτ ≤ x :=
        (le_max_right xgap xτ).trans ((le_max_right 2 (max xgap xτ)).trans hx)
      have hfour : (2 : ℝ) * 2 ≤ Real.rpow x τ := by
        nlinarith [hτPow x hxτ']
      have hpowLower : 2 ≤ Real.rpow x τ / 2 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hfour])
      have hMtwo : 2 ≤ M := hpowLower.trans hMlower
      have hpowE : Real.rpow x E = Real.rpow x θ * Real.rpow x (E - θ) := by
        calc
          Real.rpow x E = Real.rpow x (θ + (E - θ)) := by congr 1 <;> ring
          _ = _ := Real.rpow_add hxpos θ (E - θ)
      have hscaleE : 2 * M ≤ Real.rpow x E := by
        have hmul := mul_le_mul_of_nonneg_left (hgapPow x hxgap')
          (Real.rpow_nonneg hxpos.le θ)
        calc
          2 * M ≤ 2 * Real.rpow x θ := mul_le_mul_of_nonneg_left hMupper (by norm_num)
          _ ≤ 3 * Real.rpow x θ := by nlinarith [Real.rpow_nonneg hxpos.le θ]
          _ = Real.rpow x θ * 3 := by ring
          _ ≤ Real.rpow x θ * Real.rpow x (E - θ) := hmul
          _ = Real.rpow x E := hpowE.symm
      have hYup : Real.rpow x E ≤ Real.rpow x γ :=
        Real.rpow_le_rpow_of_exponent_le hxone hEγ
      let S := (Finset.range (⌊r⌋₊ + 1)).filter
        (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
      have hzero : ∀ m ∈ S, roughIndicator x γ m = 0 := by
        intro m hm
        rcases Finset.mem_filter.mp hm with ⟨_, ⟨hlm, hmr⟩⟩
        have hm2 : 2 ≤ m := by
          have hmReal : (2 : ℝ) ≤ (m : ℝ) := by linarith [hMtwo, hl]
          exact_mod_cast hmReal
        have hmUpper : (m : ℝ) ≤ Real.rpow x γ := by
          calc
            (m : ℝ) ≤ r := hmr
            _ ≤ 2 * M := hr
            _ ≤ Real.rpow x E := hscaleE
            _ ≤ Real.rpow x γ := hYup
        have hnot : ¬ roughAbove m (Real.rpow x γ) := by
          intro hrough
          obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
          have hpY := hrough p hp hpdvd
          have hpLe : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpdvd
          have hpUpper : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpLe
          exact (not_lt_of_ge (hpUpper.trans hmUpper)) hpY
        have hnot' : ¬ roughAbove m (x ^ γ) := by
          change ¬ roughAbove m (Real.rpow x γ)
          exact hnot
        simpa [roughIndicator] using hnot'
      have hsum0 :
          (∑ m ∈ S, (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ))) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rw [hzero m hm]
        simp
      rw [hsum0]
      have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hMtwo
      have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hpowPos : 0 < Real.rpow (Real.log x) (-A₃) :=
        Real.rpow_pos_of_pos hLpos _
      have hrhs : 0 ≤ (1 : ℝ) * M * Real.rpow (Real.log x) (-A₃) :=
        mul_nonneg (mul_nonneg (by norm_num) hMpos.le) hpowPos.le
      simpa [hsum0] using hrhs
    · have hγE : γ < E := lt_of_not_ge hEγ
      let J : ℕ := ⌊E / γ⌋₊
      let Ap : ℝ := A₃ + (J : ℝ) + 3
      have hAp : 0 < Ap := by dsimp [Ap]; positivity
      have hJpos : 1 ≤ J := by
        have hratio : (1 : ℝ) ≤ E / γ := (one_le_div hγ).2 hγE.le
        dsimp [J]
        exact Nat.le_floor (by exact_mod_cast hratio)
      obtain ⟨Bp, Cp, xp, hBp, hCp, hxp, hpp⟩ :=
        prime_phase_sum_bound (τ / 2) η A₀ Ap hτslot hτslotη hη1 hA₀ hAp
      obtain ⟨Csq, xSq, hCsq, hxSq, hSquare⟩ :=
        square_error γ E (τ / 2) hγ (by positivity) hγE
      obtain ⟨xgap, hxgap, hgapPow⟩ :=
        prime_exists_rpow_ge (E - θ) 3 (sub_pos.mpr hθE)
      obtain ⟨xτ, hxτ, hτPow⟩ := prime_exists_rpow_ge τ 4 hτ
      let xLogBase := Real.exp (Real.log 3 + 1)
      obtain ⟨xLogPow, hxLogPow, hLogPow⟩ :=
        prime_exists_log_rpow_le_const_mul_x_rpow A₃ γ 1 hγ (by norm_num)
      let xTail₀ := max xgap (max xτ (max xLogBase xLogPow))
      let xTail₁ := max xSq xTail₀
      let xTail₂ := max xp xTail₁
      let x₀ := max 2 xTail₂
      let H₀ := θ + 1
      let Cconv := 12 * Cp * ((J + 1 : ℕ) : ℝ) * H₀ ^ J
      let C₀ := Csq + Cconv
      have hCconv : 0 < Cconv := by dsimp [Cconv, H₀]; positivity
      have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
      refine ⟨Bp, C₀, x₀, hBp, hC₀, le_max_left _ _, ?_⟩
      intro x hx M hMlower hMupper k hk hmod χ u huLower huUpper l r hl hlr hr
      let L := Real.log x
      let Y := Real.rpow x γ
      let B : ℕ := ⌊2 * M⌋₊ + 1
      let Jset : Finset ℕ := Finset.Icc 1 J
      let D : ℝ := Real.rpow L (-Ap)
      let Hbar : ℝ := H₀ * L
      let S : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter
        (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
      let z : ℕ → ℂ := fun m => (χ (m : ZMod k) : ℂ) * roughPhase u m
      let tupleSum (j : ℕ) : ℂ :=
        ∑ t ∈ (boundedTuples j (⌊2 * M⌋₊ + 1)).filter (fun t =>
          (∀ i, (t i).Prime ∧ Real.rpow x γ < (t i : ℝ)) ∧
          l ≤ ((∏ i : Fin j, t i : ℕ) : ℝ) ∧
          ((∏ i : Fin j, t i : ℕ) : ℝ) ≤ r),
          (χ ((∏ i : Fin j, t i : ℕ) : ZMod k) : ℂ) *
            roughPhase u (∏ i : Fin j, t i : ℕ)
      have hx₂ : 2 ≤ x := (le_max_left 2 xTail₂).trans hx
      have hxpos : 0 < x := by linarith
      have hxone : 1 ≤ x := by linarith
      have hxTail₂ : xTail₂ ≤ x := (le_max_right 2 xTail₂).trans hx
      have hxp' : xp ≤ x := (le_max_left xp xTail₁).trans hxTail₂
      have hxTail₁ : xTail₁ ≤ x := (le_max_right xp xTail₁).trans hxTail₂
      have hxSq' : xSq ≤ x := (le_max_left xSq xTail₀).trans hxTail₁
      have hxTail₀ : xTail₀ ≤ x := (le_max_right xSq xTail₀).trans hxTail₁
      have hxGap' : xgap ≤ x := (le_max_left xgap (max xτ (max xLogBase xLogPow))).trans hxTail₀
      have hxRest₀ : max xτ (max xLogBase xLogPow) ≤ x :=
        (le_max_right xgap (max xτ (max xLogBase xLogPow))).trans hxTail₀
      have hxτ' : xτ ≤ x := (le_max_left xτ (max xLogBase xLogPow)).trans hxRest₀
      have hxRest₁ : max xLogBase xLogPow ≤ x :=
        (le_max_right xτ (max xLogBase xLogPow)).trans hxRest₀
      have hxLogBase' : xLogBase ≤ x := (le_max_left xLogBase xLogPow).trans hxRest₁
      have hxLogPow' : xLogPow ≤ x := (le_max_right xLogBase xLogPow).trans hxRest₁
      have hLpos : 0 < L := Real.log_pos (by linarith)
      have hlogLower : Real.log 3 + 1 ≤ L := by
        have hh := Real.log_le_log (Real.exp_pos (Real.log 3 + 1)) hxLogBase'
        simpa [xLogBase, L, Real.log_exp] using hh
      have hLone : 1 ≤ L := by
        have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
        dsimp [L]
        linarith
      have hMpos : 0 < M := lt_of_lt_of_le
        (div_pos (Real.rpow_pos_of_pos hxpos τ) (by norm_num)) hMlower
      have hxTauLarge : 4 ≤ Real.rpow x τ := hτPow x hxτ'
      let a := Real.rpow x (τ / 2)
      have hHalfPowEq : Real.rpow x τ = a * a := by
        calc
          Real.rpow x τ = Real.rpow x (τ / 2 + τ / 2) := by congr 1 <;> ring
          _ = Real.rpow x (τ / 2) * Real.rpow x (τ / 2) :=
            Real.rpow_add hxpos (τ / 2) (τ / 2)
          _ = _ := rfl
      have ha : 0 ≤ a := Real.rpow_nonneg hxpos.le _
      have hHalfLarge : 2 ≤ a := by
        rw [hHalfPowEq] at hxTauLarge
        nlinarith [ha, hxTauLarge]
      have hHalfLower : Real.rpow x (τ / 2) ≤ Real.rpow x τ / 2 := by
        change a ≤ Real.rpow x τ / 2
        rw [hHalfPowEq]
        have hmul : 2 * a ≤ a * a := mul_le_mul_of_nonneg_right hHalfLarge ha
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hmul])
      have hMhalf : Real.rpow x (τ / 2) ≤ M := hHalfLower.trans hMlower
      have hfour : (2 : ℝ) * 2 ≤ Real.rpow x τ := by nlinarith [hxTauLarge]
      have hpowLower : 2 ≤ Real.rpow x τ / 2 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hfour])
      have hMtwo : 2 ≤ M := hpowLower.trans hMlower
      have hMone : 1 ≤ M := (by norm_num : (1 : ℝ) ≤ 2).trans hMtwo
      have hpowE : Real.rpow x E = Real.rpow x θ * Real.rpow x (E - θ) := by
        calc
          Real.rpow x E = Real.rpow x (θ + (E - θ)) := by congr 1 <;> ring
          _ = _ := Real.rpow_add hxpos θ (E - θ)
      have hscaleE : 2 * M ≤ Real.rpow x E := by
        have hmul := mul_le_mul_of_nonneg_left (hgapPow x hxGap')
          (Real.rpow_nonneg hxpos.le θ)
        calc
          2 * M ≤ 2 * Real.rpow x θ := mul_le_mul_of_nonneg_left hMupper (by norm_num)
          _ ≤ 3 * Real.rpow x θ := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 3)
              (Real.rpow_nonneg hxpos.le θ)
          _ = Real.rpow x θ * 3 := by ring
          _ ≤ Real.rpow x θ * Real.rpow x (E - θ) := hmul
          _ = Real.rpow x E := hpowE.symm
      have hscaleη : 2 * M ≤ Real.rpow x η :=
        hscaleE.trans (Real.rpow_le_rpow_of_exponent_le hxone hEη.le)
      have hYpos : 0 < Y := Real.rpow_pos_of_pos hxpos γ
      have hNlow : Real.rpow x (τ / 2) / 2 ≤ Y := by
        calc
          Real.rpow x (τ / 2) / 2 ≤ Real.rpow x (τ / 2) :=
            div_le_self (Real.rpow_nonneg hxpos.le _) (by norm_num)
          _ ≤ Real.rpow x γ := Real.rpow_le_rpow_of_exponent_le hxone (by linarith [hτγ])
      have hBscale : 2 * M ≤ (B : ℝ) := by
        dsimp [B]
        push_cast
        exact le_of_lt (Nat.lt_floor_add_one (2 * M))
      have hBcast : (B : ℝ) ≤ 3 * M := by
        dsimp [B]
        push_cast
        have hf : (⌊2 * M⌋₊ : ℝ) ≤ 2 * M := Nat.floor_le (by positivity)
        nlinarith [hf, hMone]
      have hlogM : Real.log M ≤ θ * L := by
        calc
          Real.log M ≤ Real.log (Real.rpow x θ) := Real.log_le_log hMpos hMupper
          _ = θ * L := by simpa [L] using Real.log_rpow hxpos θ
      have hlogB : Real.log (B : ℝ) ≤ Real.log (3 * M) :=
        Real.log_le_log (by positivity) hBcast
      have hHarm : (harmonic B : ℝ) ≤ Hbar := by
        calc
          (harmonic B : ℝ) ≤ 1 + Real.log (B : ℝ) := harmonic_le_one_add_log B
          _ ≤ 1 + Real.log (3 * M) := by
            calc
              1 + Real.log (B : ℝ) = Real.log (B : ℝ) + 1 := by ring
              _ ≤ Real.log (3 * M) + 1 := add_le_add_left hlogB 1
              _ = 1 + Real.log (3 * M) := by ring
          _ = 1 + Real.log 3 + Real.log M := by
            rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hMpos)]
            ring
          _ ≤ 1 + Real.log 3 + θ * L := by
            calc
              1 + Real.log 3 + Real.log M = Real.log M + (1 + Real.log 3) := by ring
              _ ≤ θ * L + (1 + Real.log 3) := add_le_add_left hlogM _
              _ = 1 + Real.log 3 + θ * L := by ring
          _ ≤ L + θ * L := by
            calc
              1 + Real.log 3 + θ * L = (Real.log 3 + 1) + θ * L := by ring
              _ ≤ L + θ * L := add_le_add_left hlogLower (θ * L)
          _ = Hbar := by dsimp [Hbar, H₀]; ring
      have hHnonneg : 0 ≤ (harmonic B : ℝ) := by
        have hq : 0 ≤ harmonic B := by
          rw [harmonic_eq_sum_Icc]
          apply Finset.sum_nonneg
          intro p hp
          positivity
        exact_mod_cast hq
      have hHbarOne : 1 ≤ Hbar := by
        dsimp [Hbar, H₀]
        nlinarith [hLone, hθpos]
      have hHpow (n : ℕ) (hn : n ≤ J) :
          (harmonic B : ℝ) ^ n ≤ Hbar ^ J := by
        calc
          (harmonic B : ℝ) ^ n ≤ Hbar ^ n :=
            pow_le_pow_left₀ hHnonneg hHarm n
          _ ≤ Hbar ^ J := pow_le_pow_right₀ hHbarOne hn
      have hDpos : 0 < D := Real.rpow_pos_of_pos hLpos _
      have hDnonneg : 0 ≤ D := hDpos.le
      have hLogPow : Real.rpow L A₃ ≤ Real.rpow x γ := by
        simpa [L] using hLogPow x hxLogPow'
      have hDecay : Real.rpow x (-γ) ≤ Real.rpow L (-A₃) := by
        have hnegx : Real.rpow x (-γ) = (Real.rpow x γ)⁻¹ :=
          Real.rpow_neg (by positivity : 0 ≤ x) γ
        have hnegL : Real.rpow L (-A₃) = (Real.rpow L A₃)⁻¹ :=
          Real.rpow_neg (by positivity : 0 ≤ L) A₃
        rw [hnegx, hnegL]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos hxpos γ)
          (Real.rpow_pos_of_pos hLpos A₃)).2 hLogPow
      have hslot : ∀ N : ℝ, Real.rpow x (τ / 2) / 2 ≤ N →
          N ≤ Real.rpow x η → ∀ I : Set ℕ, IsNatInterval I →
            I ⊆ {p : ℕ | N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N} →
              ‖PP.primePhaseSum N k χ u I‖ ≤ 6 * N * Cp * D := by
        intro N hNlow hNup I hI hIsub
        simpa [D, L] using
          hpp x hxp' N hNlow hNup k hk hmod χ u huLower huUpper I hI hIsub
      have hSq := hSquare x hxSq' M hMone hMhalf hscaleE
      have hSqL1 :
          (∑ m ∈ dyadicIntegers M,
            |roughIndicator x γ m - roughConvolution x γ E M m|) ≤
              Csq * M * Real.rpow x (-γ) := by
        have hSq' := hSq
        simp only [Nat.cast_sum] at hSq'
        exact hSq'.1.trans hSq'.2
      have hSsubset : S ⊆ dyadicIntegers M := by
        intro m hm
        rcases Finset.mem_filter.mp hm with ⟨_, ⟨hlm, hmr⟩⟩
        have hmUpper : (m : ℝ) ≤ 2 * M := hmr.trans hr
        have hmFloor : m ≤ ⌊2 * M⌋₊ := Nat.le_floor hmUpper
        change m ∈ (Finset.range (⌊2 * M⌋₊ + 1) : Finset ℕ).filter
          (fun q : ℕ => M ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * M)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hmFloor), ⟨hl.trans hlm, hmUpper⟩⟩
      have hphaseNorm (m : ℕ) : ‖roughPhase u m‖ = 1 := by
        unfold roughPhase ArtinPrimitiveRoots.Proofs.RImplP.RPrime.phaseNat
        have harg : Complex.I * (u : ℂ) * (Real.log (m : ℝ) : ℂ) =
            Complex.I * ((u * Real.log (m : ℝ) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg, Complex.norm_exp_I_mul_ofReal]
      have hzNorm (m : ℕ) : ‖z m‖ ≤ 1 := by
        calc
          ‖z m‖ = ‖(χ (m : ZMod k) : ℂ)‖ * ‖roughPhase u m‖ := by
            dsimp [z]
            rw [norm_mul]
          _ = ‖(χ (m : ZMod k) : ℂ)‖ := by rw [hphaseNorm]; ring
          _ ≤ 1 := χ.norm_le_one _
      have hErr :
          ‖∑ m ∈ S, (((roughIndicator x γ m - roughConvolution x γ E M m : ℝ) : ℂ) * z m)‖ ≤
            Csq * M * Real.rpow (Real.log x) (-A₃) := by
        calc
          _ ≤ ∑ m ∈ S,
              ‖((roughIndicator x γ m - roughConvolution x γ E M m : ℝ) : ℂ) * z m‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ S, |roughIndicator x γ m - roughConvolution x γ E M m| := by
            apply Finset.sum_le_sum
            intro m hm
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_of_le_one_right (abs_nonneg _) (hzNorm m)
          _ ≤ ∑ m ∈ dyadicIntegers M,
              |roughIndicator x γ m - roughConvolution x γ E M m| :=
            Finset.sum_le_sum_of_subset_of_nonneg hSsubset (by intro m hm hmd; positivity)
          _ ≤ Csq * M * Real.rpow x (-γ) := hSqL1
          _ ≤ Csq * M * Real.rpow (Real.log x) (-A₃) := by
            exact mul_le_mul_of_nonneg_left hDecay (by positivity)
      have hRnonneg : 0 ≤ r := by linarith [hMone, hl, hlr]
      have hConvReindex :
          (∑ m ∈ S, (roughConvolution x γ E M m : ℂ) * z m) =
            ∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j := by
        have hcastConv (m : ℕ) : (roughConvolution x γ E M m : ℂ) =
            ∑ j ∈ Jset, (roughConvolutionTerm x γ M j m : ℂ) := by
          simp [roughConvolution, Jset, J]
        calc
          _ = ∑ m ∈ S,
              (∑ j ∈ Jset, (roughConvolutionTerm x γ M j m : ℂ)) * z m := by
            apply Finset.sum_congr rfl
            intro m hm
            exact congrArg (fun w : ℂ => w * z m) (hcastConv m)
          _ = ∑ m ∈ S, ∑ j ∈ Jset,
              (roughConvolutionTerm x γ M j m : ℂ) * z m := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_mul]
          _ = ∑ j ∈ Jset, ∑ m ∈ S,
              (roughConvolutionTerm x γ M j m : ℂ) * z m := by rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            cases j with
            | zero =>
              change 0 ∈ Finset.Icc 1 J at hj
              have h := (Finset.mem_Icc.mp hj).1
              omega
            | succ n =>
              have hRe := roughPrimeTuple_interval_reindex x γ M l r (n + 1) k χ u hRnonneg
              simpa only [tupleSum, z, Nat.succ_sub_one, mul_assoc] using hRe
      have hCoeffNorm (j : ℕ) : ‖(1 / (j.factorial : ℂ))‖ ≤ 1 := by
        have hjpos : 0 < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
        have hjone : 1 ≤ (j.factorial : ℝ) := by
          exact_mod_cast (Nat.one_le_of_lt (Nat.factorial_pos j))
        rw [norm_div, norm_one, show ‖(j.factorial : ℂ)‖ = (j.factorial : ℝ) by simp]
        exact (div_le_one hjpos).2 hjone
      have hOneJ (j : ℕ) (hj : j ∈ Jset) :
          ‖(1 / (j.factorial : ℂ)) * tupleSum j‖ ≤
            12 * Cp * M * D * Hbar ^ J := by
        cases j with
        | zero =>
          change 0 ∈ Finset.Icc 1 J at hj
          have h := (Finset.mem_Icc.mp hj).1
          omega
        | succ n =>
          have hnJ : n ≤ J := by
            have hj' := Finset.mem_Icc.mp hj
            omega
          have hTuple := prime_tuple_product_interval_phase_bound
            M l r Y (Real.rpow x (τ / 2) / 2) (Real.rpow x η) D Cp
            n B k χ u (by linarith : 0 ≤ M) hl hlr hr hBscale hYpos hNlow hscaleη
            hDnonneg hCp.le hslot
          have hTuple' : ‖tupleSum (n + 1)‖ ≤
              12 * Cp * M * D * (harmonic B : ℝ) ^ n := by
            simpa only [tupleSum, B, Y, roughPhase] using hTuple
          calc
            ‖(1 / ((Nat.succ n).factorial : ℂ)) * tupleSum (Nat.succ n)‖ =
                ‖(1 / ((Nat.succ n).factorial : ℂ))‖ * ‖tupleSum (Nat.succ n)‖ := norm_mul _ _
            _ ≤ 1 * (12 * Cp * M * D * (harmonic B : ℝ) ^ n) := by
              apply mul_le_mul (hCoeffNorm _) hTuple'
              · exact norm_nonneg _
              · positivity
            _ ≤ 12 * Cp * M * D * Hbar ^ J := by
              have hconst : 0 ≤ 12 * Cp * M * D := by positivity
              have hpow := hHpow n hnJ
              simpa only [one_mul] using mul_le_mul_of_nonneg_left hpow hconst
      have hconvNorm :
          ‖∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j‖ ≤
            ((J + 1 : ℕ) : ℝ) * (12 * Cp * M * D * Hbar ^ J) := by
        calc
          _ ≤ ∑ j ∈ Jset, ‖(1 / (j.factorial : ℂ)) * tupleSum j‖ := norm_sum_le _ _
          _ ≤ (Jset.card : ℝ) * (12 * Cp * M * D * Hbar ^ J) := by
            simpa [nsmul_eq_mul] using
              (Finset.sum_le_card_nsmul Jset
                (fun j => ‖(1 / (j.factorial : ℂ)) * tupleSum j‖)
                (12 * Cp * M * D * Hbar ^ J) (fun j hj => hOneJ j hj))
          _ ≤ ((J + 1 : ℕ) : ℝ) * (12 * Cp * M * D * Hbar ^ J) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hcard : Jset.card ≤ J + 1 := by
              have hsubset : Jset ⊆ Finset.range (J + 1) := by
                intro j hj
                have hj' : j ∈ Finset.Icc 1 J := by simpa [Jset] using hj
                have hj'' := Finset.mem_Icc.mp hj'
                exact Finset.mem_range.mpr (by omega)
              calc
                Jset.card ≤ (Finset.range (J + 1)).card := Finset.card_le_card hsubset
                _ = J + 1 := Finset.card_range _
            exact_mod_cast hcard
      have hDpow : D * Hbar ^ J ≤ H₀ ^ J * Real.rpow L (-A₃) := by
        have hExp : -Ap + (J : ℝ) = -A₃ - 3 := by dsimp [Ap]; push_cast; ring
        calc
          D * Hbar ^ J = Real.rpow L (-Ap) * ((H₀ ^ J) * Real.rpow L (J : ℝ)) := by
            dsimp [D, Hbar]
            rw [mul_pow, Real.rpow_natCast]
          _ = H₀ ^ J * (Real.rpow L (-Ap) * Real.rpow L (J : ℝ)) := by ring
          _ = H₀ ^ J * Real.rpow L (-Ap + (J : ℝ)) := by
            congr 1
            exact (Real.rpow_add hLpos (-Ap) (J : ℝ)).symm
          _ = H₀ ^ J * Real.rpow L (-A₃ - 3) := by rw [hExp]
          _ ≤ H₀ ^ J * Real.rpow L (-A₃) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
      have hconvBound :
          ‖∑ m ∈ S, (roughConvolution x γ E M m : ℂ) * z m‖ ≤
            Cconv * M * Real.rpow L (-A₃) := by
        calc
          _ = ‖∑ j ∈ Jset, (1 / (j.factorial : ℂ)) * tupleSum j‖ := by rw [hConvReindex]
          _ ≤ ((J + 1 : ℕ) : ℝ) * (12 * Cp * M * D * Hbar ^ J) := hconvNorm
          _ ≤ Cconv * M * Real.rpow L (-A₃) := by
            dsimp [Cconv]
            have hcoef : 0 ≤ ((J + 1 : ℕ) : ℝ) * 12 * Cp * M := by positivity
            calc
              ((J + 1 : ℕ) : ℝ) * (12 * Cp * M * D * Hbar ^ J) =
                  (((J + 1 : ℕ) : ℝ) * 12 * Cp * M) * (D * Hbar ^ J) := by ring
              _ ≤ (((J + 1 : ℕ) : ℝ) * 12 * Cp * M) *
                    (H₀ ^ J * Real.rpow L (-A₃)) :=
                  mul_le_mul_of_nonneg_left hDpow hcoef
              _ = (12 * Cp * ((J + 1 : ℕ) : ℝ) * H₀ ^ J) *
                    M * Real.rpow L (-A₃) := by ring
      have hsumIdentity :
          (∑ m ∈ S, (roughIndicator x γ m : ℂ) * z m) =
            (∑ m ∈ S, (roughConvolution x γ E M m : ℂ) * z m) +
              ∑ m ∈ S, (((roughIndicator x γ m - roughConvolution x γ E M m : ℝ) : ℂ) * z m) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro m hm
        simp only [Complex.ofReal_sub]
        ring
      have htotal :
          ‖∑ m ∈ S, (roughIndicator x γ m : ℂ) * z m‖ ≤
            C₀ * M * Real.rpow L (-A₃) := by
        rw [hsumIdentity]
        calc
          _ ≤ ‖∑ m ∈ S, (roughConvolution x γ E M m : ℂ) * z m‖ +
              ‖∑ m ∈ S,
                (((roughIndicator x γ m - roughConvolution x γ E M m : ℝ) : ℂ) * z m)‖ := norm_add_le _ _
          _ ≤ Cconv * M * Real.rpow L (-A₃) + Csq * M * Real.rpow L (-A₃) :=
            add_le_add hconvBound hErr
          _ = C₀ * M * Real.rpow L (-A₃) := by dsimp [C₀]; ring
      simpa [S, z, L, roughPhase,
        ArtinPrimitiveRoots.Proofs.RImplP.RPrime.phaseNat, mul_assoc] using htotal

set_option maxHeartbeats 2000000 in
/-- `t2:proxy-high` — 08-type-ii.tex:482-516; the source estimate is also the proof of PD
Lemma 5.2 (`05-major-arcs.tex:57-125`). -/
theorem proxy_high :
    ∃ C₃ : ℝ, 0 < C₃ ∧
      ∀ δ γ wMin wMax : ℝ, 0 < δ → 0 < γ → γ < wMin → wMin < wMax → wMax < 1 →
        ∀ A₀ : ℝ, 0 < A₀ →
          ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
            ∀ A₄ : ℝ, 0 < A₄ → ∃ x₀ : ℝ, 2 ≤ x₀ ∧
              ∀ x : ℝ, x₀ ≤ x →
              let L := Real.log x
              let Tstar := Real.exp (L / Real.log L ^ 2)
              ∀ M : ℝ, Real.rpow x δ ≤ M →
                Real.log M / L ∈ Set.Icc wMin wMax →
                Real.log (2 * M) / L ∈ Set.Icc wMin wMax →
                ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow L A₀ →
                  ∀ χ : DirichletCharacter ℂ k, ∀ l r u : ℝ,
                    M ≤ l → l ≤ r → r ≤ 2 * M → 1 ≤ |u| → |u| < Real.rpow x 2 →
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
                            Real.log (m : ℝ)) /
                        (M * roughSieveProduct (roughCutoff x))‖ ≤
                      Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) ∧
                      (‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                            l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧
                              roughAbove m (roughCutoff x)),
                          (χ (m : ZMod k) : ℂ) *
                            Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                            roughProxy x γ m) / M‖ ≤
                        Real.rpow L (-A₄) +
                          C₀ * (if |u| ≤ Tstar then
                            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
                          else Real.rpow L C₀ *
                            Real.exp (-L / Real.rpow (Real.log L) C₃))) := by
  obtain ⟨C₃, hC₃, hHigh⟩ :=
    ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.high_reciprocal_log_residue_bound
  refine ⟨C₃, hC₃, ?_⟩
  intro δ γ wMin wMax hδ hγ hγwMin hMinMax hwMax A₀ hA₀
  have hwMinPos : 0 < wMin := lt_trans hγ hγwMin
  obtain ⟨c₀, K, hc₀, hK, hSourceByAccuracy⟩ :=
    ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.proxy_high_source_bound
      δ A₀ wMin C₃ hδ hA₀ hwMinPos hC₃ hHigh
  obtain ⟨K_D, hK_D, hDensityLip⟩ :=
    density_regularity.2.1 γ wMin wMax hγ hγwMin hMinMax.le
  let B_D : ℝ := |roughDensity γ wMin| + K_D * (wMax - wMin) + 1
  let Q : ℝ → ℝ := fun z => z * roughDensity γ z
  let B_Q : ℝ := wMax * B_D + 1
  let K_Q : ℝ := B_D + wMax * K_D + 1
  let F_Q : ℝ := 2 * (B_Q + K_Q)
  have hwMaxPos : 0 < wMax := lt_trans hwMinPos hMinMax
  have hB_D : 0 < B_D := by
    dsimp [B_D]
    positivity
  have hB_Q : 0 < B_Q := by
    dsimp [B_Q]
    positivity
  have hK_Q : 0 < K_Q := by
    dsimp [K_Q]
    positivity
  have hF_Q : 0 < F_Q := by
    dsimp [F_Q]
    positivity
  have hDensityAbs : ∀ z : ℝ, wMin ≤ z → z ≤ wMax →
      |roughDensity γ z| ≤ B_D := by
    intro z hzlo hzhi
    have hLip := hDensityLip z wMin hzlo hzhi le_rfl hMinMax.le
    have hdist : |z - wMin| ≤ wMax - wMin := by
      rw [abs_of_nonneg (sub_nonneg.mpr hzlo)]
      linarith
    calc
      |roughDensity γ z| =
          |(roughDensity γ z - roughDensity γ wMin) + roughDensity γ wMin| := by
        congr 1 <;> ring
      _ ≤ |roughDensity γ z - roughDensity γ wMin| +
            |roughDensity γ wMin| := abs_add_le _ _
      _ ≤ K_D * |z - wMin| + |roughDensity γ wMin| :=
        add_le_add hLip (le_refl _)
      _ ≤ K_D * (wMax - wMin) + |roughDensity γ wMin| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hdist hK_D.le) (le_refl _)
      _ ≤ B_D := by dsimp [B_D]; linarith
  have hQBound : ∀ z : ℝ, wMin ≤ z → z ≤ wMax → |Q z| ≤ B_Q := by
    intro z hzlo hzhi
    have hzpos : 0 < z := lt_of_lt_of_le hwMinPos hzlo
    have hD := hDensityAbs z hzlo hzhi
    calc
      |Q z| = z * |roughDensity γ z| := by
        simp [Q, abs_of_pos hzpos, abs_mul]
      _ ≤ wMax * |roughDensity γ z| :=
        mul_le_mul_of_nonneg_right hzhi (abs_nonneg _)
      _ ≤ wMax * B_D := mul_le_mul_of_nonneg_left hD hwMaxPos.le
      _ ≤ B_Q := by dsimp [B_Q]; linarith
  have hQLip : ∀ z₁ z₂ : ℝ, wMin ≤ z₁ → z₁ ≤ wMax →
      wMin ≤ z₂ → z₂ ≤ wMax → |Q z₁ - Q z₂| ≤ K_Q * |z₁ - z₂| := by
    intro z₁ z₂ hz₁lo hz₁hi hz₂lo hz₂hi
    have hz₁pos : 0 < z₁ := lt_of_lt_of_le hwMinPos hz₁lo
    have hDdiff := hDensityLip z₁ z₂ hz₁lo hz₁hi hz₂lo hz₂hi
    have hD₂ := hDensityAbs z₂ hz₂lo hz₂hi
    have hQexpand : Q z₁ - Q z₂ =
        z₁ * (roughDensity γ z₁ - roughDensity γ z₂) +
          (z₁ - z₂) * roughDensity γ z₂ := by
      dsimp [Q]
      ring
    have hFirst : |z₁| * |roughDensity γ z₁ - roughDensity γ z₂| ≤
        (wMax * K_D) * |z₁ - z₂| := by
      calc
        _ ≤ wMax * |roughDensity γ z₁ - roughDensity γ z₂| := by
          rw [abs_of_pos hz₁pos]
          exact mul_le_mul_of_nonneg_right hz₁hi (abs_nonneg _)
        _ ≤ wMax * (K_D * |z₁ - z₂|) :=
          mul_le_mul_of_nonneg_left hDdiff hwMaxPos.le
        _ = (wMax * K_D) * |z₁ - z₂| := by ring
    have hSecond : |z₁ - z₂| * |roughDensity γ z₂| ≤
        B_D * |z₁ - z₂| := by
      calc
        _ = |roughDensity γ z₂| * |z₁ - z₂| := by ring
        _ ≤ B_D * |z₁ - z₂| :=
          mul_le_mul_of_nonneg_right hD₂ (abs_nonneg (z₁ - z₂))
    have hCoeff : wMax * K_D + B_D ≤ K_Q := by
      dsimp [K_Q]
      linarith
    calc
      |Q z₁ - Q z₂| =
          |z₁ * (roughDensity γ z₁ - roughDensity γ z₂) +
            (z₁ - z₂) * roughDensity γ z₂| := by rw [hQexpand]
      _ ≤ |z₁ * (roughDensity γ z₁ - roughDensity γ z₂)| +
            |(z₁ - z₂) * roughDensity γ z₂| := abs_add_le _ _
      _ = |z₁| * |roughDensity γ z₁ - roughDensity γ z₂| +
            |z₁ - z₂| * |roughDensity γ z₂| := by rw [abs_mul, abs_mul]
      _ ≤ (wMax * K_D + B_D) * |z₁ - z₂| := by
        calc
          _ ≤ (wMax * K_D) * |z₁ - z₂| + B_D * |z₁ - z₂| :=
            add_le_add hFirst hSecond
          _ = (wMax * K_D + B_D) * |z₁ - z₂| := by ring
      _ ≤ K_Q * |z₁ - z₂| :=
        mul_le_mul_of_nonneg_right hCoeff (abs_nonneg _)
  let C₀ : ℝ := 1 + K + F_Q * K
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC₀K : K ≤ C₀ := by dsimp [C₀]; nlinarith [hK, hF_Q]
  have hC₀FQK : F_Q * K ≤ C₀ := by dsimp [C₀]; nlinarith [hK, hF_Q]
  obtain ⟨_s₀, vMin, xMertens, _hs₀, hvMin, hxMertens, hMertens⟩ :=
    ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.rough_mertens_bounds
  obtain ⟨xSmooth, hSmooth⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop
      (max 1 (max F_Q (1 / wMin))))
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro A₄ hA₄
  let A_s : ℝ := A₄ + 1
  have hA_s : 0 < A_s := by dsimp [A_s]; linarith
  obtain ⟨xSource, hxSource, hSourceA⟩ := hSourceByAccuracy A_s hA_s
  let x₀ := max xSource (max xSmooth xMertens)
  have hx₀two : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxSource (le_max_left _ _)
  refine ⟨x₀, hx₀two, ?_⟩
  intro x hx
  dsimp [x₀] at hx
  rcases max_le_iff.mp hx with ⟨hxSource', hxRest⟩
  rcases max_le_iff.mp hxRest with ⟨hxSmooth', hxMertens'⟩
  dsimp
  intro M hMx hMlogRatio hTwoMlogRatio k hk hkBound χ l r u hMl hlr hr huLower huUpper
  let L : ℝ := Real.log x
  let Tstar : ℝ := Real.exp (L / Real.log L ^ 2)
  let V : ℝ := roughSieveProduct (roughCutoff x)
  let I : Finset ℕ := (Finset.range (⌊r⌋₊ + 1)).filter
    (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r ∧ roughAbove m (roughCutoff x))
  have hx₂ : 2 ≤ x := le_trans hx₀two hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < L := by dsimp [L]; exact Real.log_pos (by linarith)
  have hSmoothX : max 1 (max F_Q (1 / wMin)) ≤ L := by
    simpa [L] using hSmooth x hxSmooth'
  have hLone : 1 ≤ L :=
    le_trans (le_max_left _ _) hSmoothX
  have hFQleL : F_Q ≤ L := by
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hSmoothX)
  have hInvWmin : 1 / wMin ≤ L := by
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hSmoothX)
  have hWminL : 1 ≤ wMin * L := by
    have hmul := mul_le_mul_of_nonneg_left hInvWmin hwMinPos.le
    have hcancel : wMin * (1 / wMin) = 1 := by field_simp [ne_of_gt hwMinPos]
    nlinarith
  have hMpos : 0 < M :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hMx
  have hMlogLower : wMin * L ≤ Real.log M := by
    have hratio := (Set.mem_Icc.mp hMlogRatio).1
    simpa [L] using (le_div_iff₀ hLpos).mp hratio
  have hLog2MUpper : Real.log (2 * M) ≤ wMax * L := by
    have hratio := (Set.mem_Icc.mp hTwoMlogRatio).2
    simpa [L] using (div_le_iff₀ hLpos).mp hratio
  have hlogM : 1 ≤ Real.log M := le_trans hWminL hMlogLower
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by norm_num) hlogM
  have hMgt : 1 < M := (Real.log_pos_iff hMpos.le).mp hlogMpos
  have h2Mpos : 0 < 2 * M := by positivity
  have hLog2MleL : Real.log (2 * M) ≤ Real.log x := by
    calc
      Real.log (2 * M) ≤ wMax * L := hLog2MUpper
      _ ≤ L := by
        have hwMaxOne : wMax ≤ 1 := le_of_lt hwMax
        calc
          wMax * L ≤ 1 * L := mul_le_mul_of_nonneg_right hwMaxOne hLpos.le
          _ = L := by ring
      _ = Real.log x := by rfl
  have h2MleX : 2 * M ≤ x := by
    calc
      2 * M = Real.exp (Real.log (2 * M)) := (Real.exp_log h2Mpos).symm
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hLog2MleL
      _ = x := Real.exp_log hxpos
  have hMleX : M ≤ x := by linarith
  have hxgeone : 1 ≤ x := by linarith
  have hxPow5 : x ≤ Real.rpow x 5 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hxgeone
      (by norm_num : (1 : ℝ) ≤ 5)
    rw [Real.rpow_one] at hpow
    exact hpow
  have hMupper : M ≤ 2 * Real.rpow x 5 := by
    calc
      M ≤ x := hMleX
      _ ≤ Real.rpow x 5 := hxPow5
      _ ≤ 2 * Real.rpow x 5 := by
        nlinarith [Real.rpow_nonneg hxpos.le (5 : ℝ)]
  have hMertensX := hMertens x hxMertens'
  rcases hMertensX with ⟨_, hVlower₀⟩
  have hVlower : vMin * Real.rpow L (-(24 / 100 : ℝ)) ≤ V := by
    simpa [L, V] using hVlower₀
  have hVpos : 0 < V := by
    have hbase : 0 < vMin * Real.rpow L (-(24 / 100 : ℝ)) :=
      mul_pos hvMin (Real.rpow_pos_of_pos hLpos _)
    exact lt_of_lt_of_le hbase hVlower
  let phase : ℝ := if |u| ≤ Tstar then
      |u|⁻¹ + Real.rpow x (-c₀)
    else Real.exp (-L / Real.rpow (Real.log L) C₃)
  let E : ℝ := Real.rpow L (-A_s)
  let Bsrc : ℝ := E + K * phase
  have hPhaseNonneg : 0 ≤ phase := by
    dsimp [phase]
    split_ifs <;> positivity
  have hSourceX := hSourceA x hxSource'
  dsimp [L, Tstar] at hSourceX
  have hSourceIntervals : ∀ l' rr', M ≤ l' → l' ≤ rr' → rr' ≤ 2 * M →
      ‖ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.roughSourceIntervalSum
          x k χ u l' rr' / (M * V)‖ ≤ Bsrc := by
    intro l' rr' hl' hl'r' hr'
    have h := hSourceX M hMx hMlogLower hMupper k hk
      (by simpa [L] using hkBound) χ u huLower (le_of_lt huUpper)
    have h' := h l' rr' hl' hl'r' hr'
    simpa [ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.roughSourceIntervalSum,
      L, Tstar, V, phase, E, Bsrc] using h'
  have hDensityError : F_Q * E ≤ Real.rpow L (-A₄) := by
    have hFQ : F_Q ≤ L := hFQleL
    have hCancel : Real.rpow L (-A_s) * L = Real.rpow L (-A₄) := by
      calc
        _ = Real.rpow L (-A_s) * Real.rpow L (1 : ℝ) := by
          have hOne : Real.rpow L (1 : ℝ) = L := Real.rpow_one L
          exact congrArg (fun z : ℝ => Real.rpow L (-A_s) * z) hOne.symm
        _ = Real.rpow L (-A_s + 1) := (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L (-A₄) := by congr 1 <;> dsimp [A_s] <;> ring
    calc
      _ ≤ L * Real.rpow L (-A_s) :=
        mul_le_mul_of_nonneg_right hFQ (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow L (-A₄) := by rw [mul_comm, hCancel]
  have hPowerDecay : E ≤ Real.rpow L (-A₄) := by
    dsimp [E]
    exact Real.rpow_le_rpow_of_exponent_le hLone (by dsimp [A_s]; linarith)
  have hScaleOsc : K * phase ≤ C₀ * (Real.rpow L C₀ * phase) := by
    have hPowC₀ : 1 ≤ Real.rpow L C₀ := Real.one_le_rpow hLone hC₀.le
    have hPhaseScale : phase ≤ Real.rpow L C₀ * phase := by
      calc
        phase = 1 * phase := by ring
        _ ≤ Real.rpow L C₀ * phase :=
          mul_le_mul_of_nonneg_right hPowC₀ hPhaseNonneg
    calc
      K * phase ≤ C₀ * phase := mul_le_mul_of_nonneg_right hC₀K hPhaseNonneg
      _ ≤ C₀ * (Real.rpow L C₀ * phase) :=
        mul_le_mul_of_nonneg_left hPhaseScale hC₀.le
  have hSourceFinal :
      ‖(∑ m ∈ I,
          (χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ)) /
              Real.log (m : ℝ)) / (M * V)‖ ≤ E + K * phase := by
    have h := hSourceX M hMx hMlogLower hMupper k hk
      (by simpa [L] using hkBound) χ u huLower (le_of_lt huUpper)
      l r hMl hlr hr
    simpa [ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.roughSourceIntervalSum,
      I, V, L, Tstar, phase, E] using h
  have hWeighted :=
    ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.weighted_rough_source_interval_bound
      Q x M V L wMin wMax Bsrc B_Q K_Q k χ u l r hLone hMgt hVpos
      hwMinPos hMinMax hMlogLower hLog2MUpper hB_Q.le hK_Q.le
      hQBound hQLip hSourceIntervals hMl hlr hr
  have hProxyPointwise (m : ℕ) (hm : m ∈ I) :
      ((χ (m : ZMod k) : ℂ) *
          Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
            (roughProxy x γ m : ℂ)) =
        (Q (Real.log (m : ℝ) / L) : ℂ) *
          (((χ (m : ZMod k) : ℂ) *
            Complex.exp (Complex.I * u * Real.log (m : ℝ))) /
              (Real.log (m : ℝ) : ℂ)) /
            (V : ℂ) := by
    have hmBounds := (Finset.mem_filter.mp hm).2
    have hmRough : roughAbove m (roughCutoff x) := hmBounds.2.2
    have hmLower : M ≤ (m : ℝ) := le_trans hMl hmBounds.1
    have hlogmPos : 0 < Real.log (m : ℝ) := by
      apply lt_of_lt_of_le hlogMpos
      exact Real.log_le_log hMpos hmLower
    have hProxyCoeff : roughProxy x γ m =
        Q (Real.log (m : ℝ) / L) /
          (V * Real.log (m : ℝ)) := by
      dsimp [roughProxy]
      simp [hmRough]
      change roughDensity γ (Real.log (m : ℝ) / L) / (L * V) =
        ((Real.log (m : ℝ) / L) *
          roughDensity γ (Real.log (m : ℝ) / L)) /
          (V * Real.log (m : ℝ))
      field_simp [ne_of_gt hLpos, ne_of_gt hVpos, ne_of_gt hlogmPos]
      <;> ring
    rw [show (roughProxy x γ m : ℂ) =
        ((Q (Real.log (m : ℝ) / L) /
          (V * Real.log (m : ℝ))) : ℝ) by exact congrArg Complex.ofReal hProxyCoeff]
    push_cast
    field_simp [ne_of_gt hVpos, ne_of_gt hlogmPos]
    <;> ring
  have hProxySum :
      (∑ m ∈ I,
        (χ (m : ZMod k) : ℂ) *
          Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
            (roughProxy x γ m : ℂ)) / (M : ℂ) =
        (∑ m ∈ I,
          (Q (Real.log (m : ℝ) / L) : ℂ) *
            (((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ))) /
                (Real.log (m : ℝ) : ℂ))) /
          ((M * V : ℝ) : ℂ) := by
    calc
      _ = (∑ m ∈ I,
            ((Q (Real.log (m : ℝ) / L) : ℂ) *
              (((χ (m : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (m : ℝ))) /
                  (Real.log (m : ℝ) : ℂ))) /
              (V : ℂ)) / (M : ℂ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro m hm
        exact hProxyPointwise m hm
      _ = ((∑ m ∈ I,
            (Q (Real.log (m : ℝ) / L) : ℂ) *
              (((χ (m : ZMod k) : ℂ) *
                Complex.exp (Complex.I * u * Real.log (m : ℝ))) /
                  (Real.log (m : ℝ) : ℂ))) /
            (V : ℂ)) / (M : ℂ) := by rw [← Finset.sum_div]
      _ = _ := by
        push_cast
        field_simp [ne_of_gt hVpos, ne_of_gt hMpos]
        <;> ring
  have hWeightedBound :
      ‖(∑ m ∈ I,
          (Q (Real.log (m : ℝ) / L) : ℂ) *
            (((χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ))) /
                (Real.log (m : ℝ) : ℂ))) /
          ((M * V : ℝ) : ℂ)‖ ≤ F_Q * Bsrc := by
    simpa [I, F_Q, Complex.ofReal_mul] using hWeighted
  have hErrorSource :
      Real.rpow L (-A_s) + K * phase ≤
        Real.rpow L (-A₄) + C₀ * (Real.rpow L C₀ * phase) :=
    add_le_add hPowerDecay hScaleOsc
  have hErrorProxy : F_Q * Bsrc ≤
      Real.rpow L (-A₄) + C₀ * (Real.rpow L C₀ * phase) := by
    dsimp [Bsrc]
    calc
      _ = F_Q * Real.rpow L (-A_s) + (F_Q * K) * phase := by ring
      _ ≤ Real.rpow L (-A₄) + C₀ * (Real.rpow L C₀ * phase) := by
        apply add_le_add hDensityError
        calc
          (F_Q * K) * phase ≤ C₀ * phase :=
            mul_le_mul_of_nonneg_right hC₀FQK hPhaseNonneg
          _ ≤ C₀ * (Real.rpow L C₀ * phase) := by
            exact mul_le_mul_of_nonneg_left
              (by
                calc
                  phase = 1 * phase := by ring
                  _ ≤ Real.rpow L C₀ * phase :=
                    mul_le_mul_of_nonneg_right
                      (Real.one_le_rpow hLone hC₀.le) hPhaseNonneg)
              hC₀.le
  constructor
  · calc
      _ ≤ Real.rpow L (-A_s) + K * phase := by
        simpa [ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.roughSourceIntervalSum,
          I, V, L, Tstar, phase, E] using hSourceFinal
      _ ≤ Real.rpow L (-A₄) + C₀ * (Real.rpow L C₀ * phase) := hErrorSource
      _ = Real.rpow L (-A₄) +
          C₀ * (if |u| ≤ Tstar then
            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
          else Real.rpow L C₀ *
            Real.exp (-L / Real.rpow (Real.log L) C₃)) := by
          simp [phase, Tstar]
  · have hProxyBound :
        ‖(∑ m ∈ I,
            (χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                (roughProxy x γ m : ℂ)) / (M : ℂ)‖ ≤ F_Q * Bsrc := by
      rw [hProxySum]
      exact hWeightedBound
    calc
      _ = ‖(∑ m ∈ I,
            (χ (m : ZMod k) : ℂ) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
                (roughProxy x γ m : ℂ)) / (M : ℂ)‖ := by
        simp [I]
      _ ≤ F_Q * Bsrc := hProxyBound
      _ ≤ Real.rpow L (-A₄) + C₀ * (Real.rpow L C₀ * phase) := hErrorProxy
      _ = Real.rpow L (-A₄) +
          C₀ * (if |u| ≤ Tstar then
            Real.rpow L C₀ * (|u|⁻¹ + Real.rpow x (-c₀))
          else Real.rpow L C₀ *
            Real.exp (-L / Real.rpow (Real.log L) C₃)) := by
          simp [phase, Tstar]

set_option maxHeartbeats 2000000 in
private theorem high_frequency_upper_scale
    (γ wMin wMax δ C A c₂ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax)
    (hwMax : wMax < 1) (hδ : 0 < δ) (hC : 0 < C) (hA : 0 < A)
    (hc₂ : 0 < c₂) :
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ M X : ℝ, Real.rpow x δ ≤ M → 0 < X → X ≤ c₂ * x →
            Real.log M / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * M) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * X * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                ∀ l r : ℝ, M ≤ l → l ≤ r → r ≤ 2 * M →
                  ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter
                        (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                      roughCoefficient x γ v m * χ (m : ZMod k) *
                        Complex.exp (Complex.I * t * Real.log (m : ℝ))) / M‖ ≤
                    C₀ * Real.rpow (Real.log x) (-A) := by
  intro B hB
  let τ := min (γ / 2) (δ / 2)
  let θ := (wMax + 1) / 2
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact lt_min (by linarith) (by linarith)
  have hτγ : τ < γ := by
    dsimp [τ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτδ : τ < δ := by
    dsimp [τ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hwθ : wMax < θ := by dsimp [θ]; linarith
  have hθone : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨Bₚ, Cₚ, xₚ, hBₚ, hCₚ, hxₚ, hprime⟩ :=
    prime_high γ wMax hγ hwMax τ θ C (A + 1) hτpos hτγ hwθ hθone hC
      (by linarith : 0 < A + 1)
  obtain ⟨C₃, hC₃, hproxy₀⟩ := proxy_high
  obtain ⟨Cq, cq, hCq, hcq, hproxy₁⟩ :=
    hproxy₀ δ γ wMin wMax hδ hγ hγw hw hwMax C hC
  obtain ⟨xq, hxq, hproxy⟩ := hproxy₁ (A + 1) (by linarith)
  obtain ⟨xB, hxB, hlogB⟩ :=
    ArtinPrimitiveRoots.Proofs.r_typeii_p.log_rpow_le_const_mul_x_rpow
      B 1 (1 / (8 * c₂)) (by norm_num) (by positivity)
  obtain ⟨xC, hxC, hlogC⟩ :=
    ArtinPrimitiveRoots.Proofs.r_typeii_p.log_rpow_le_const_mul_x_rpow
      C 1 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨xD, hxD, hlogD⟩ :=
    ArtinPrimitiveRoots.Proofs.r_typeii_p.log_rpow_le_const_mul_x_rpow
      (A + 1 + Cq) cq 1 hcq (by norm_num)
  obtain ⟨L₀, hL₀, hexpSmall⟩ :=
    ArtinPrimitiveRoots.Proofs.r_typeii_p.exists_log_rpow_mul_exp_phase_small
      C₃ (A + 1 + Cq) hC₃
  let B₂ := C + Bₚ + A + Cq + 10
  let C₀ := Cₚ + 1 + 3 * Cq
  let z₁ := max xₚ xq
  let z₂ := max xB xC
  let z₃ := max xD (Real.exp L₀)
  let z₄ := max z₁ z₂
  let z₅ := max z₄ z₃
  let x₀ := max 2 z₅
  have hB₂ : 0 < B₂ := by dsimp [B₂]; linarith
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hx₀ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have hB₂C : C + 1 ≤ B₂ := by dsimp [B₂]; linarith
  have hB₂Bp : Bₚ + 1 ≤ B₂ := by dsimp [B₂]; linarith
  have hB₂Cq : Cq + 1 ≤ B₂ - (A + 1) := by dsimp [B₂]; linarith
  refine ⟨B₂, C₀, x₀, hB₂, hC₀, hx₀, ?_⟩
  intro x hx M X hM hXpos hX hlogM hlog2 k hk1 hkC χ v t htlo hthi hv l r hl hlr hr
  let L := Real.log x
  let u := t + v
  let Tstar := Real.exp (L / (Real.log L) ^ 2)
  let S := (Finset.range (⌊r⌋₊ + 1)).filter
    (fun (m : ℕ) => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
  let P := ∑ m ∈ S,
    (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
      Complex.exp (Complex.I * u * Real.log (m : ℝ))
  let Q := ∑ m ∈ S,
    χ (m : ZMod k) * Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
      (roughProxy x γ m : ℂ)
  let R := Real.rpow L (-(A + 1))
  have hx₂ : 2 ≤ x := le_trans (le_max_left 2 z₅) hx
  have hxpos : 0 < x := by linarith
  have hxone : (1 : ℝ) ≤ x := by linarith
  have hz₅ : z₅ ≤ x := le_trans (le_max_right 2 z₅) hx
  have hz₄ : z₄ ≤ x := le_trans (le_max_left z₄ z₃) hz₅
  have hz₃ : z₃ ≤ x := le_trans (le_max_right z₄ z₃) hz₅
  have hz₁ : z₁ ≤ x := le_trans (le_max_left z₁ z₂) hz₄
  have hz₂ : z₂ ≤ x := le_trans (le_max_right z₁ z₂) hz₄
  have hxₚ : xₚ ≤ x := le_trans (le_max_left xₚ xq) hz₁
  have hxq' : xq ≤ x := le_trans (le_max_right xₚ xq) hz₁
  have hxB' : xB ≤ x := le_trans (le_max_left xB xC) hz₂
  have hxC' : xC ≤ x := le_trans (le_max_right xB xC) hz₂
  have hxD' : xD ≤ x := le_trans (le_max_left xD (Real.exp L₀)) hz₃
  have hxexp : Real.exp L₀ ≤ x := le_trans (le_max_right xD (Real.exp L₀)) hz₃
  have hLgeL₀ : L₀ ≤ L := by
    dsimp [L]
    have hlog := Real.log_le_log (Real.exp_pos L₀) hxexp
    simpa using hlog
  have hL₂ : 2 ≤ L := le_trans hL₀ hLgeL₀
  have hLpos : 0 < L := by linarith
  have hLnonneg : 0 ≤ L := le_of_lt hLpos
  have hLone : (1 : ℝ) ≤ L := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hM
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogM' : Real.log M ≤ wMax * Real.log x :=
    (div_le_iff₀ hlogxpos).mp hlogM.2
  have hMpow : M ≤ Real.rpow x wMax := by
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (wMax * Real.log x) := Real.exp_le_exp.mpr hlogM'
      _ = Real.rpow x wMax := by
        change Real.exp (wMax * Real.log x) = x ^ wMax
        rw [Real.rpow_def_of_pos hxpos wMax]
        congr 1
        ring
  have hMθ : M ≤ Real.rpow x θ :=
    le_trans hMpow (Real.rpow_le_rpow_of_exponent_le hxone (by dsimp [θ]; linarith))
  have hτδpow := Real.rpow_le_rpow_of_exponent_le hxone (le_of_lt hτδ)
  have hMτ : Real.rpow x τ / 2 ≤ M := by
    have hτnonneg : 0 ≤ Real.rpow x τ := Real.rpow_nonneg (by linarith) _
    calc
      Real.rpow x τ / 2 ≤ Real.rpow x τ := by nlinarith
      _ ≤ Real.rpow x δ := hτδpow
      _ ≤ M := hM
  have hlogB' : Real.rpow L B ≤ x / (8 * c₂) := by
    have h := hlogB x hxB'
    simpa [L, Real.rpow_one, div_eq_mul_inv, mul_comm] using h
  have hlogC' : Real.rpow L C ≤ x / 4 := by
    have h := hlogC x hxC'
    simpa [L, Real.rpow_one, div_eq_mul_inv, mul_comm] using h
  have hpowD : Real.rpow L (A + 1 + Cq) ≤ Real.rpow x cq := by
    have h := hlogD x hxD'
    simpa [L] using h
  have hlogpowD : (A + 1 + Cq) * Real.log L ≤ cq * Real.log x := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hLpos _) hpowD
    rw [Real.rpow_eq_pow, Real.log_rpow hLpos, Real.log_rpow hxpos] at h
    exact h
  have hdecayX : Real.rpow L Cq * Real.rpow x (-cq) ≤ R := by
    have hneg : Real.rpow x (-cq) ≤ Real.rpow L (-(A + 1 + Cq)) := by
      change x ^ (-cq) ≤ L ^ (-(A + 1 + Cq))
      rw [Real.rpow_neg hxpos.le cq, Real.rpow_neg hLpos.le (A + 1 + Cq)]
      have hInv := (inv_le_inv₀ (Real.rpow_pos_of_pos hxpos cq)
        (Real.rpow_pos_of_pos hLpos (A + 1 + Cq))).mpr hpowD
      simpa only [Real.rpow_eq_pow] using hInv
    calc
      Real.rpow L Cq * Real.rpow x (-cq) ≤
          Real.rpow L Cq * Real.rpow L (-(A + 1 + Cq)) :=
        mul_le_mul_of_nonneg_left hneg (Real.rpow_nonneg hLnonneg _)
      _ = R := by
        change L ^ Cq * L ^ (-(A + 1 + Cq)) = L ^ (-(A + 1))
        rw [← Real.rpow_add hLpos Cq (-(A + 1 + Cq))]
        congr 1
        ring
  have hExpProd := hexpSmall L hLgeL₀
  have hexpInv : Real.exp (-L / Real.rpow (Real.log L) C₃) ≤
      Real.rpow L (-(A + 1 + Cq)) := by
    have hpos : 0 < Real.rpow L (A + 1 + Cq) := Real.rpow_pos_of_pos hLpos _
    have hdiv : Real.exp (-L / Real.rpow (Real.log L) C₃) ≤
        1 / Real.rpow L (A + 1 + Cq) :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hExpProd)
    change Real.exp (-L / Real.rpow (Real.log L) C₃) ≤ L ^ (-(A + 1 + Cq))
    rw [Real.rpow_neg hLpos.le (A + 1 + Cq)]
    simpa [one_div, Real.rpow_eq_pow] using hdiv
  have hdecayExp : Real.rpow L Cq *
      Real.exp (-L / Real.rpow (Real.log L) C₃) ≤ R := by
    calc
      Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃) ≤
          Real.rpow L Cq * Real.rpow L (-(A + 1 + Cq)) :=
        mul_le_mul_of_nonneg_left hexpInv (Real.rpow_nonneg hLnonneg _)
      _ = R := by
        change L ^ Cq * L ^ (-(A + 1 + Cq)) = L ^ (-(A + 1))
        rw [← Real.rpow_add hLpos Cq (-(A + 1 + Cq))]
        congr 1
        ring
  have hgapBound : ∀ a b : ℝ, a + 1 ≤ b →
      2 * Real.rpow L a ≤ Real.rpow L b := by
    intro a b hab
    calc
      2 * Real.rpow L a ≤ Real.rpow L a * L := by
        have h := mul_le_mul_of_nonneg_left hL₂ (Real.rpow_nonneg hLnonneg a)
        simpa [mul_comm, Real.rpow_one] using h
      _ = Real.rpow L (a + 1) := by
        change L ^ a * L = L ^ (a + 1)
        rw [Real.rpow_add_one hLpos.ne' a]
      _ ≤ Real.rpow L b :=
        Real.rpow_le_rpow_of_exponent_le hLone hab
  have h2LC : 2 * Real.rpow L C ≤ Real.rpow L B₂ := hgapBound C B₂ hB₂C
  have h2LBₚ : 2 * Real.rpow L Bₚ ≤ Real.rpow L B₂ :=
    hgapBound Bₚ B₂ hB₂Bp
  have h2LCq : 2 * Real.rpow L Cq ≤ Real.rpow L (B₂ - (A + 1)) :=
    hgapBound Cq (B₂ - (A + 1)) hB₂Cq
  have hAbsT : |t| ≤ |u| + |v| := by
    have huEq : t = u + (-v) := by dsimp [u]; ring
    calc
      |t| = |u + (-v)| := by rw [huEq]
      _ ≤ |u| + |v| := by simpa using abs_add_le u (-v)
  have hUhalf : Real.rpow L B₂ / 2 ≤ |u| := by
    have hTsum : Real.rpow L B₂ ≤ |u| + Real.rpow L C := by
      exact le_trans htlo (le_trans hAbsT (add_le_add (le_refl _) hv))
    have hChalf : Real.rpow L C ≤ Real.rpow L B₂ / 2 := by nlinarith [h2LC]
    linarith
  have huBp : Real.rpow L Bₚ ≤ |u| := by
    have hhalf : Real.rpow L Bₚ ≤ Real.rpow L B₂ / 2 := by
      nlinarith [h2LBₚ]
    exact hhalf.trans hUhalf
  have huone : 1 ≤ |u| := by
    have hpowone : 1 ≤ Real.rpow L Bₚ := by
      calc
        1 = Real.rpow L 0 := by simp
        _ ≤ Real.rpow L Bₚ :=
          Real.rpow_le_rpow_of_exponent_le hLone (by linarith [hBₚ])
    exact hpowone.trans huBp
  have hXterm : 2 * X * Real.rpow L B ≤ Real.rpow x 2 / 4 := by
    have hXmul : X * Real.rpow L B ≤ (c₂ * x) * Real.rpow L B :=
      mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hLnonneg B)
    calc
      2 * X * Real.rpow L B = 2 * (X * Real.rpow L B) := by ring
      _ ≤ 2 * ((c₂ * x) * Real.rpow L B) :=
        mul_le_mul_of_nonneg_left hXmul (by norm_num)
      _ ≤ 2 * ((c₂ * x) * (x / (8 * c₂))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlogB' (by positivity)) (by norm_num)
      _ = Real.rpow x 2 / 4 := by
        have hrpow2 : Real.rpow x (2 : ℝ) = x ^ 2 := by
          simp [Real.rpow_eq_pow, Real.rpow_natCast]
        rw [hrpow2]
        field_simp [ne_of_gt hc₂]
        ring
  have hXtermC : Real.rpow L C ≤ Real.rpow x 1 / 4 := by
    simpa [Real.rpow_one] using hlogC'
  have huAbsUpper : |u| ≤ 2 * X * Real.rpow L B + Real.rpow L C := by
    calc
      |u| = |t + v| := by rfl
      _ ≤ |t| + |v| := abs_add_le _ _
      _ ≤ 2 * X * Real.rpow L B + Real.rpow L C := add_le_add hthi hv
  have hxpow2 : Real.rpow x (2 : ℝ) = x ^ 2 := by
    simp [Real.rpow_eq_pow, Real.rpow_natCast]
  have huUpper : |u| < Real.rpow x 2 := by
    rw [hxpow2]
    have hxtermC' : Real.rpow L C ≤ x / 4 := by
      simpa [Real.rpow_one, Real.rpow_eq_pow] using hXtermC
    calc
      |u| ≤ 2 * X * Real.rpow L B + Real.rpow L C := huAbsUpper
      _ ≤ x ^ 2 / 4 + x / 4 := by
        have h1 : 2 * X * Real.rpow L B ≤ x ^ 2 / 4 := by
          simpa [hxpow2] using hXterm
        exact add_le_add h1 hxtermC'
      _ < x ^ 2 := by
        have hsmall : x / 4 < 3 * x ^ 2 / 4 := by nlinarith only [hx₂]
        calc
          x ^ 2 / 4 + x / 4 = x / 4 + x ^ 2 / 4 := by ring
          _ < 3 * x ^ 2 / 4 + x ^ 2 / 4 :=
            by linarith only [hsmall]
          _ = x ^ 2 := by ring
  have hprimeM := hprime x hxₚ M hMτ hMθ k hk1 hkC χ u huBp huUpper.le l r hl hlr hr
  have hPbound : ‖P‖ ≤ Cₚ * M * R := by
    simpa [P, S, L, u, R] using hprimeM
  have hProxyEval := hproxy x hxq' M hM hlogM hlog2 k hk1 hkC χ
    l r u hl hlr hr huone huUpper
  have hQfilter : Q = ∑ m ∈ S.filter
      (fun m => roughAbove m (roughCutoff x)),
      χ (m : ZMod k) * Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
        (roughProxy x γ m : ℂ) := by
    dsimp [Q]
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro m hm hmf
    have hnot : ¬ roughAbove m (roughCutoff x) := by
      intro hrough
      exact hmf (Finset.mem_filter.mpr ⟨hm, hrough⟩)
    simp [roughProxy, hnot]
  have hQraw : ‖Q / (M : ℂ)‖ ≤ R + Cq *
      (if |u| ≤ Tstar then
        Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))
      else Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) := by
    rw [hQfilter]
    simpa [S, L, u, Tstar, R, Finset.filter_filter,
      and_assoc, and_left_comm, and_comm] using hProxyEval.2
  have hUpos : 0 < |u| :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hLpos _) (by norm_num)) hUhalf
  have hpowMul : Real.rpow L (-(A + 1)) * Real.rpow L B₂ =
      Real.rpow L (B₂ - (A + 1)) := by
    change L ^ (-(A + 1)) * L ^ B₂ = L ^ (B₂ - (A + 1))
    rw [← Real.rpow_add hLpos (-(A + 1)) B₂]
    congr 1
    ring
  have hpowProduct : Real.rpow L (-(A + 1)) *
      (Real.rpow L B₂ / 2) = Real.rpow L (B₂ - (A + 1)) / 2 := by
    calc
      _ = (Real.rpow L (-(A + 1)) * Real.rpow L B₂) / 2 := by ring
      _ = _ := by rw [hpowMul]
  have hhalfCq : Real.rpow L Cq ≤
      Real.rpow L (B₂ - (A + 1)) / 2 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (by simpa [mul_comm] using h2LCq)
  have hInvBase : Real.rpow L Cq ≤ R * |u| := by
    calc
      Real.rpow L Cq ≤ Real.rpow L (B₂ - (A + 1)) / 2 := hhalfCq
      _ = Real.rpow L (-(A + 1)) *
          (Real.rpow L B₂ / 2) := hpowProduct.symm
      _ ≤ R * |u| := by
        apply mul_le_mul_of_nonneg_left hUhalf
        exact Real.rpow_nonneg hLnonneg _
  have hInv : Real.rpow L Cq * |u|⁻¹ ≤ R := by
    have hdiv := (div_le_iff₀ hUpos).2 hInvBase
    simpa [R, div_eq_mul_inv] using hdiv
  have hDecaySum : Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq)) ≤ 2 * R := by
    rw [mul_add]
    calc
      Real.rpow L Cq * |u|⁻¹ + Real.rpow L Cq * Real.rpow x (-cq) ≤ R + R :=
        add_le_add hInv (by simpa [R] using hdecayX)
      _ = 2 * R := by ring
  have hQbound : ‖Q / (M : ℂ)‖ ≤ (1 + 3 * Cq) * R := by
    by_cases hsmall : |u| ≤ Tstar
    · rw [if_pos hsmall] at hQraw
      calc
        ‖Q / (M : ℂ)‖ ≤ R + Cq *
            (Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))) := hQraw
        _ ≤ R + Cq * (2 * R) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hDecaySum hCq.le) _
        _ = (1 + 2 * Cq) * R := by ring
        _ ≤ (1 + 3 * Cq) * R := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLnonneg _)
          linarith [hCq]
    · rw [if_neg hsmall] at hQraw
      calc
        ‖Q / (M : ℂ)‖ ≤ R + Cq *
            (Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) := hQraw
        _ ≤ R + Cq * R :=
          add_le_add_right (mul_le_mul_of_nonneg_left hdecayExp hCq.le) _
        _ = (1 + Cq) * R := by ring
        _ ≤ (1 + 3 * Cq) * R := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLnonneg _)
          linarith [hCq]
  have hPnorm : ‖P / (M : ℂ)‖ ≤ Cₚ * R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
    apply (div_le_iff₀ hMpos).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hPbound
  have hRle : R ≤ Real.rpow L (-A) := by
    dsimp [R]
    exact Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hsplit :
      (∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) = P - Q := by
    calc
      _ = ∑ m ∈ S,
          ((roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
              Complex.exp (Complex.I * u * Real.log (m : ℝ)) -
            χ (m : ZMod k) * Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
              (roughProxy x γ m : ℂ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        simpa [u] using roughCoefficient_phase_split x γ v t m (χ (m : ZMod k))
      _ = P - Q := by
        dsimp [P, Q]
        rw [Finset.sum_sub_distrib]
  have hmain :
      ‖(∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / (M : ℂ)‖ ≤
        C₀ * Real.rpow L (-A) := by
    calc
      _ = ‖(P - Q) / (M : ℂ)‖ := by rw [hsplit]
      _ = ‖P / (M : ℂ) - Q / (M : ℂ)‖ := by rw [sub_div]
      _ ≤ ‖P / (M : ℂ)‖ + ‖Q / (M : ℂ)‖ := norm_sub_le _ _
      _ ≤ Cₚ * R + (1 + 3 * Cq) * R := add_le_add hPnorm hQbound
      _ ≤ C₀ * Real.rpow L (-A) := by
        calc
          Cₚ * R + (1 + 3 * Cq) * R = C₀ * R := by dsimp [C₀]; ring
          _ ≤ C₀ * Real.rpow L (-A) :=
            mul_le_mul_of_nonneg_left hRle (le_of_lt hC₀)
  simpa [S, L] using hmain

/-- `t2:high-frequency` — 08-type-ii.tex:513-527. -/
private theorem exists_log_rpow_le_const_mul_x_rpow
    (a b K : ℝ) (hb : 0 < b) (hK : 0 < K) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.rpow (Real.log x) a ≤ K * Real.rpow x b := by
  have hlim : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) a / Real.rpow x b)
      Filter.atTop (𝓝 0) := by
    exact (isLittleO_log_rpow_rpow_atTop a hb).tendsto_div_nhds_zero
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.rpow (Real.log x) a / Real.rpow x b‖ < K := by
    have hball := hlim.eventually
      (Metric.ball_mem_nhds (0 : ℝ) hK)
    filter_upwards [hball] with x hx
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max x₁ 2, le_max_right _ _, ?_⟩
  intro x hx
  have hx₁' : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : 2 ≤ x := (le_max_right x₁ 2).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hden : 0 < Real.rpow x b := Real.rpow_pos_of_pos hxpos _
  have hquot := hx₁ x hx₁'
  have hqnonneg : 0 ≤ Real.rpow (Real.log x) a / Real.rpow x b :=
    div_nonneg (Real.rpow_nonneg hlog _) hden.le
  have hquot' : Real.rpow (Real.log x) a / Real.rpow x b < K := by
    have hquotAbs : |Real.rpow (Real.log x) a / Real.rpow x b| < K := by
      simpa only [Real.norm_eq_abs] using hquot
    have hquotAbsDiv : |Real.rpow (Real.log x) a| / |Real.rpow x b| < K := by
      simpa only [abs_div] using hquotAbs
    have hnum : 0 ≤ Real.rpow (Real.log x) a := Real.rpow_nonneg hlog _
    simpa only [abs_of_nonneg hnum, abs_of_pos hden] using hquotAbsDiv
  exact le_of_lt ((div_lt_iff₀ hden).mp hquot')

private theorem exists_log_rpow_mul_exp_phase_small
    (r a : ℝ) (hr : 0 < r) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L a * Real.exp (-L / Real.rpow (Real.log L) r) ≤ 1 := by
  obtain ⟨L₁, hL₁, hlogPow⟩ :=
    exists_log_rpow_le_const_mul_x_rpow (r + 1) (1 / 2) 1
      (by norm_num) (by norm_num)
  have hsqrtLim : Filter.Tendsto (fun L : ℝ => Real.rpow L (1 / 2))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have hsqrtLarge := Filter.eventually_atTop.mp
    (hsqrtLim.eventually_ge_atTop (a + 1))
  obtain ⟨L₂, hL₂⟩ := hsqrtLarge
  let L₀ := max 2 (max L₁ L₂)
  refine ⟨L₀, le_max_left _ _, ?_⟩
  intro L hL
  have hLge2 : 2 ≤ L := (le_max_left 2 (max L₁ L₂)).trans hL
  have hLbase : max L₁ L₂ ≤ L := (le_max_right 2 (max L₁ L₂)).trans hL
  have hLgeL₁ : L₁ ≤ L := (le_max_left L₁ L₂).trans hLbase
  have hLgeL₂ : L₂ ≤ L := (le_max_right L₁ L₂).trans hLbase
  have hLpos : 0 < L := by linarith
  have hlogPos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogNonneg : 0 ≤ Real.log L := le_of_lt hlogPos
  have hsqrt : a + 1 ≤ Real.rpow L (1 / 2) := hL₂ L hLgeL₂
  have hsqrtNonneg : 0 ≤ Real.rpow L (1 / 2) := Real.rpow_nonneg (by linarith) _
  have hsqrtSq : Real.rpow L (1 / 2) * Real.rpow L (1 / 2) = L := by
    change L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L
    rw [← Real.rpow_add (by linarith : 0 < L) (1 / 2) (1 / 2)]
    norm_num
  have hlogPow' : Real.rpow (Real.log L) r * Real.log L ≤ Real.rpow L (1 / 2) := by
    have heq : Real.rpow (Real.log L) (r + 1) =
        Real.rpow (Real.log L) r * Real.log L := by
      change (Real.log L) ^ (r + 1) = (Real.log L) ^ r * Real.log L
      rw [Real.rpow_add_one hlogPos.ne' r]
    rw [← heq]
    simpa using hlogPow L hLgeL₁
  have hfactorNonneg : 0 ≤ Real.rpow (Real.log L) r * Real.log L :=
    mul_nonneg (Real.rpow_nonneg hlogNonneg _) hlogNonneg
  have hprod : (a + 1) * Real.log L * Real.rpow (Real.log L) r ≤ L := by
    calc
      (a + 1) * Real.log L * Real.rpow (Real.log L) r =
          (a + 1) * (Real.rpow (Real.log L) r * Real.log L) := by ring
      _ ≤ Real.rpow L (1 / 2) *
          (Real.rpow (Real.log L) r * Real.log L) :=
        mul_le_mul_of_nonneg_right hsqrt hfactorNonneg
      _ ≤ Real.rpow L (1 / 2) * Real.rpow L (1 / 2) :=
        mul_le_mul_of_nonneg_left hlogPow' hsqrtNonneg
      _ = L := hsqrtSq
  have hden : 0 < Real.rpow (Real.log L) r := Real.rpow_pos_of_pos hlogPos _
  have harg : (a + 1) * Real.log L ≤ L / Real.rpow (Real.log L) r :=
    (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hprod)
  have hexp : Real.exp (-L / Real.rpow (Real.log L) r) ≤
      Real.rpow L (-(a + 1)) := by
    calc
      Real.exp (-L / Real.rpow (Real.log L) r) ≤
          Real.exp (-((a + 1) * Real.log L)) :=
        Real.exp_le_exp.mpr (by simpa [neg_div] using neg_le_neg harg)
      _ = Real.rpow L (-(a + 1)) := by
        change Real.exp (-((a + 1) * Real.log L)) = L ^ (-(a + 1))
        rw [Real.rpow_def_of_pos hLpos (-(a + 1))]
        congr 1
        ring
  have hmul := mul_le_mul_of_nonneg_left hexp
    (Real.rpow_nonneg (by linarith : 0 ≤ L) a)
  calc
    Real.rpow L a * Real.exp (-L / Real.rpow (Real.log L) r) ≤
        Real.rpow L a * Real.rpow L (-(a + 1)) := hmul
    _ = Real.rpow L (-1) := by
      change L ^ a * L ^ (-(a + 1) : ℝ) = L ^ (-1 : ℝ)
      rw [← Real.rpow_add hLpos a (-(a + 1))]
      congr 1
      ring
    _ ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (by linarith : 1 ≤ L) (by norm_num : (-1 : ℝ) ≤ 0)
      simpa using h

private theorem exists_loglog_ge (R : ℝ) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → R ≤ Real.log (Real.log x) := by
  have hlim : Filter.Tendsto (fun x : ℝ => Real.log (Real.log x))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp (hlim.eventually_ge_atTop R)
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  exact hx₁ x ((le_max_right 2 x₁).trans hx)

set_option maxHeartbeats 5000000 in
theorem high_frequency
    (γ wMin wMax δ C A : ℝ) (hγ : 0 < γ) (hγw : γ < wMin)
    (hw : wMin < wMax) (hwMax : wMax < 1) (hδ : 0 < δ)
    (hC : 0 < C) (hA : 0 < A) :
    ∀ B : ℝ, 0 < B →
      ∃ B₂ C₀ x₀ : ℝ, 0 < B₂ ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          ∀ Hm Hn : ℝ, Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
            x / 2 ≤ Hm * Hn → Hm * Hn ≤ 2 * x →
            Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
            Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
            ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ Real.rpow (Real.log x) C →
              ∀ χ : DirichletCharacter ℂ k, ∀ v t : ℝ,
                Real.rpow (Real.log x) B₂ ≤ |t| →
                |t| ≤ 2 * (Hm * Hn) * Real.rpow (Real.log x) B →
                |v| ≤ Real.rpow (Real.log x) C →
                  ∀ l r : ℝ, Hm ≤ l → l ≤ r → r ≤ 2 * Hm →
                    ‖(∑ m ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun (m : ℕ) =>
                          l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r),
                        roughCoefficient x γ v m * χ (m : ZMod k) *
                          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
                      C₀ * Real.rpow (Real.log x) (-A) := by
  intro B hB
  classical
  let τ := min γ δ / 2
  let θ := (wMax + 1) / 2
  have hmin : 0 < min γ δ := lt_min_iff.mpr ⟨hγ, hδ⟩
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτγ : τ < γ := by
    dsimp [τ]
    have hlt : min γ δ / 2 < min γ δ := by linarith
    exact hlt.trans_le (min_le_left _ _)
  have hτδ : τ < δ := by
    dsimp [τ]
    have hlt : min γ δ / 2 < min γ δ := by linarith
    exact hlt.trans_le (min_le_right _ _)
  have hwθ : wMax < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  obtain ⟨Bp, Cp, xp, hBp, hCp, hxp, hprime⟩ :=
    prime_high γ wMax hγ hwMax τ θ C (A + 1)
      hτ hτγ hwθ hθ1 hC (by linarith)
  obtain ⟨C₃, hC₃, hproxy⟩ := proxy_high
  obtain ⟨Cq, cq, hCq, hcq, hproxy₁⟩ :=
    hproxy δ γ wMin wMax hδ hγ hγw hw hwMax C hC
  obtain ⟨xq, hxq, hproxyA⟩ := hproxy₁ (A + 1) (by linarith)
  obtain ⟨xB, hxB, hlogB⟩ :=
    exists_log_rpow_le_const_mul_x_rpow B (1 / 2) (1 / 8)
      (by norm_num) (by norm_num)
  obtain ⟨xC, hxC, hlogC⟩ :=
    exists_log_rpow_le_const_mul_x_rpow C (1 / 2) (1 / 8)
      (by norm_num) (by norm_num)
  obtain ⟨Ldec, hLdec, hdecay⟩ :=
    exists_log_rpow_mul_exp_phase_small C₃ (A + 1 + Cq) hC₃
  obtain ⟨xtt, hxtt, hloglog⟩ := exists_loglog_ge (1 + 1 / cq)
  let xReq := max xB (max xC (max (Real.exp Ldec) xtt))
  let x₀ := max xp (max xq xReq)
  let B₂ := C + Bp + A + Cq + 4
  let C₀ := Cp + 1 + 2 * Cq
  have hB₂ : 0 < B₂ := by dsimp [B₂]; positivity
  have hB₂C : C + 1 ≤ B₂ := by dsimp [B₂]; linarith
  have hB₂p : Bp + 1 ≤ B₂ := by dsimp [B₂]; linarith
  have hB₂proxy : A + Cq + 1 ≤ B₂ := by dsimp [B₂]; linarith
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxp (le_max_left xp (max xq xReq))
  refine ⟨B₂, C₀, x₀, hB₂, hC₀, hx₀, ?_⟩
  intro x hx Hm Hn hHm hHn hprod₀ hprod₁ hHmLog h2HmLog
    k hk hmod χ v t htlo hthi hv l r hl hlr hr
  let L := Real.log x
  let u := t + v
  have hx2 : 2 ≤ x := le_trans hx₀ hx
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hxp' : xp ≤ x := (le_max_left xp (max xq xReq)).trans hx
  have hxq' : xq ≤ x :=
    (le_max_left xq xReq).trans ((le_max_right xp (max xq xReq)).trans hx)
  have hxinner : max xq xReq ≤ x :=
    (le_max_right xp (max xq xReq)).trans hx
  have hxReq : xReq ≤ x := (le_max_right xq xReq).trans hxinner
  have hxReqInner : max xC (max (Real.exp Ldec) xtt) ≤ x := by
    exact (le_max_right xB (max xC (max (Real.exp Ldec) xtt))).trans hxReq
  have hxB' : xB ≤ x := by
    exact le_trans (le_max_left xB (max xC (max (Real.exp Ldec) xtt))) hxReq
  have hxC' : xC ≤ x := by
    exact (le_max_left xC (max (Real.exp Ldec) xtt)).trans hxReqInner
  have hxdec' : Real.exp Ldec ≤ x := by
    exact (le_max_left (Real.exp Ldec) xtt).trans
      ((le_max_right xC (max (Real.exp Ldec) xtt)).trans hxReqInner)
  have hxtt' : xtt ≤ x := by
    exact (le_max_right (Real.exp Ldec) xtt).trans
      ((le_max_right xC (max (Real.exp Ldec) xtt)).trans hxReqInner)
  have hLdec' : Ldec ≤ L := by
    have hh := Real.log_le_log (Real.exp_pos Ldec) hxdec'
    simpa [L] using hh
  have hLtwo : 2 ≤ L := hLdec.trans hLdec'
  have hLone : 1 ≤ L := by linarith [hLdec, hLdec']
  have hLpowB : Real.rpow L B ≤ (1 / 8 : ℝ) * Real.rpow x (1 / 2) :=
    hlogB x hxB'
  have hLpowC : Real.rpow L C ≤ (1 / 8 : ℝ) * Real.rpow x (1 / 2) :=
    hlogC x hxC'
  have hdecayx : Real.rpow L (A + 1 + Cq) *
      Real.exp (-L / Real.rpow (Real.log L) C₃) ≤ 1 := hdecay L hLdec'
  have hT : 1 + 1 / cq ≤ Real.log L := by
    have hh := hloglog x hxtt'
    simpa [L] using hh
  have hTpos : 0 < Real.log L := by
    have : 0 < 1 + 1 / cq := by positivity
    linarith
  have hcqne : cq ≠ 0 := ne_of_gt hcq
  have hInvPos : 0 < 1 / cq := one_div_pos.mpr hcq
  have hTge1 : 1 ≤ Real.log L := by linarith
  have hcqT : 1 ≤ cq * Real.log L := by
    have hinv : cq * cq⁻¹ = 1 := mul_inv_cancel₀ hcqne
    have hbase : 1 ≤ cq * (1 + cq⁻¹) := by nlinarith [hcq, hinv]
    have hT' : 1 + cq⁻¹ ≤ Real.log L := by simpa [one_div] using hT
    exact hbase.trans (mul_le_mul_of_nonneg_left hT' hcq.le)
  have hcqTsq : 1 ≤ cq * (Real.log L) ^ 2 := by
    have hctpos : 0 < cq * Real.log L := mul_pos hcq hTpos
    calc
      1 ≤ cq * Real.log L := hcqT
      _ ≤ (cq * Real.log L) * Real.log L :=
        by simpa using mul_le_mul_of_nonneg_left hTge1 hctpos.le
      _ = cq * (Real.log L) ^ 2 := by ring
  have hdenT : 0 < (Real.log L) ^ 2 := sq_pos_of_pos hTpos
  have hfracT : 1 / (Real.log L) ^ 2 ≤ cq := (div_le_iff₀ hdenT).2 hcqTsq
  have hargT : L / (Real.log L) ^ 2 ≤ cq * L := by
    calc
      L / (Real.log L) ^ 2 = (1 / (Real.log L) ^ 2) * L := by ring
      _ ≤ cq * L := mul_le_mul_of_nonneg_right hfracT hLpos.le
  have hTstar : Real.exp (L / (Real.log L) ^ 2) ≤ Real.rpow x cq := by
    calc
      Real.exp (L / (Real.log L) ^ 2) ≤ Real.exp (cq * L) := Real.exp_le_exp.mpr hargT
      _ = Real.rpow x cq := by
        change Real.exp (cq * L) = x ^ cq
        rw [Real.rpow_def_of_pos hxpos cq]
        congr 1
        dsimp [L]
        ring
  have hHmpos : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHm
  have hHmLogUp : Real.log Hm / L ≤ wMax := hHmLog.2
  have hlogHm : Real.log Hm ≤ wMax * L := (div_le_iff₀ hLpos).mp hHmLogUp
  have hHmExp : Hm ≤ Real.rpow x wMax := by
    calc
      Hm = Real.exp (Real.log Hm) := by rw [Real.exp_log hHmpos]
      _ ≤ Real.exp (wMax * L) := Real.exp_le_exp.mpr hlogHm
      _ = Real.rpow x wMax := by
        change Real.exp (wMax * L) = x ^ wMax
        rw [Real.rpow_def_of_pos hxpos wMax]
        congr 1
        dsimp [L]
        ring
  have hHmUp : Hm ≤ Real.rpow x θ :=
    hHmExp.trans (Real.rpow_le_rpow_of_exponent_le hxone (by dsimp [θ]; linarith))
  have hτpow : Real.rpow x τ ≤ Real.rpow x δ :=
    Real.rpow_le_rpow_of_exponent_le hxone hτδ.le
  have hHmLow : Real.rpow x τ / 2 ≤ Hm := by
    have hpowNonneg : 0 ≤ Real.rpow x τ := Real.rpow_nonneg (by linarith) _
    calc
      Real.rpow x τ / 2 ≤ Real.rpow x τ := by nlinarith
      _ ≤ Real.rpow x δ := hτpow
      _ ≤ Hm := hHm
  have hBpow : 2 * Real.rpow L C ≤ Real.rpow L B₂ := by
    have hm := Real.rpow_le_rpow_of_exponent_le hLone hB₂C
    have heq : Real.rpow L (C + 1) = Real.rpow L C * L := by
      change L ^ (C + 1) = L ^ C * L
      exact Real.rpow_add_one hLpos.ne' C
    have hpowNonneg : 0 ≤ Real.rpow L C := Real.rpow_nonneg (by linarith) _
    calc
      2 * Real.rpow L C ≤ L * Real.rpow L C :=
        mul_le_mul_of_nonneg_right hLtwo hpowNonneg
      _ = Real.rpow L (C + 1) := by rw [heq]; ring
      _ ≤ Real.rpow L B₂ := hm
  have hBppow : 2 * Real.rpow L Bp ≤ Real.rpow L B₂ := by
    have hm := Real.rpow_le_rpow_of_exponent_le hLone hB₂p
    have heq : Real.rpow L (Bp + 1) = Real.rpow L Bp * L := by
      change L ^ (Bp + 1) = L ^ Bp * L
      exact Real.rpow_add_one hLpos.ne' Bp
    have hpowNonneg : 0 ≤ Real.rpow L Bp := Real.rpow_nonneg (by linarith) _
    calc
      2 * Real.rpow L Bp ≤ L * Real.rpow L Bp :=
        mul_le_mul_of_nonneg_right hLtwo hpowNonneg
      _ = Real.rpow L (Bp + 1) := by rw [heq]; ring
      _ ≤ Real.rpow L B₂ := hm
  have hvBound : |v| ≤ Real.rpow L C := by simpa [L] using hv
  have htBound : Real.rpow L B₂ ≤ |t| := by simpa [L] using htlo
  have huTriangle : |t| ≤ |u| + |v| := by
    dsimp [u]
    calc
      |t| = |(t + v) - v| := by congr 1; ring
      _ ≤ |t + v| + |v| := by simpa using abs_sub_le (t + v) 0 v
  have huStrong : Real.rpow L B₂ / 2 ≤ |u| := by
    have hvHalf : |v| ≤ Real.rpow L B₂ / 2 := by
      calc
        |v| ≤ Real.rpow L C := hvBound
        _ ≤ Real.rpow L B₂ / 2 := by nlinarith [hBpow]
    linarith [huTriangle, htBound, hvHalf]
  have huPrime : Real.rpow L Bp ≤ |u| := by
    have hhalf : Real.rpow L Bp ≤ Real.rpow L B₂ / 2 := by linarith [hBppow]
    exact hhalf.trans huStrong
  have huOne : 1 ≤ |u| := by
    have hone : (1 : ℝ) ≤ Real.rpow L Bp := by
      have h := Real.rpow_le_rpow_of_exponent_le hLone (by positivity : 0 ≤ Bp)
      simpa using h
    exact hone.trans huPrime
  have huX_and_lt : |u| ≤ Real.rpow x 2 ∧ |u| < Real.rpow x 2 := by
    have hsqrt : Real.rpow x (1 / 2) ≤ x := by
      have hh := Real.rpow_le_rpow_of_exponent_le hxone
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
      simpa using hh
    have hsqrt2 : Real.rpow x (1 / 2) ≤ Real.rpow x 2 :=
      Real.rpow_le_rpow_of_exponent_le hxone (by norm_num : (1 / 2 : ℝ) ≤ 2)
    have htmax : |t| ≤ 4 * x * Real.rpow L B := by
      calc
        |t| ≤ 2 * (Hm * Hn) * Real.rpow L B := by simpa [L] using hthi
        _ ≤ 4 * x * Real.rpow L B := by
          have hprod' := mul_le_mul_of_nonneg_right hprod₁
            (Real.rpow_nonneg (by linarith : 0 ≤ L) B)
          nlinarith [hprod']
    have hBsmall : 4 * x * Real.rpow L B ≤ (1 / 2 : ℝ) * x ^ 2 := by
      have h₁ := mul_le_mul_of_nonneg_left hLpowB (by positivity : 0 ≤ 4 * x)
      have h₂ := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ x)
      nlinarith [h₁, h₂]
    have hCsmallR : Real.rpow L C ≤ (1 / 8 : ℝ) * Real.rpow x 2 := by
      exact le_trans hLpowC
        (mul_le_mul_of_nonneg_left hsqrt2 (by norm_num : 0 ≤ (1 / 8 : ℝ)))
    have hpow2Nat : Real.rpow x (2 : ℝ) = x ^ 2 := by
      change x ^ (2 : ℝ) = x ^ 2
      exact Real.rpow_natCast x 2
    have hCsmall : Real.rpow L C ≤ (1 / 8 : ℝ) * x ^ 2 := by
      calc
        Real.rpow L C ≤ (1 / 8 : ℝ) * Real.rpow x 2 := hCsmallR
        _ = (1 / 8 : ℝ) * x ^ 2 := by rw [hpow2Nat]
    have hVsmall : |v| ≤ (1 / 8 : ℝ) * x ^ 2 := by
      calc
        |v| ≤ Real.rpow L C := hvBound
        _ ≤ (1 / 8 : ℝ) * x ^ 2 := hCsmall
    have htotal : |u| ≤ (5 / 8 : ℝ) * x ^ 2 := by
      calc
        |u| = |t + v| := by rfl
        _ ≤ |t| + |v| := by simpa [u] using abs_add_le t v
        _ ≤ 4 * x * Real.rpow L B + (1 / 8 : ℝ) * x ^ 2 :=
          add_le_add htmax hVsmall
        _ ≤ (1 / 2 : ℝ) * x ^ 2 + (1 / 8 : ℝ) * x ^ 2 :=
          add_le_add hBsmall le_rfl
        _ = (5 / 8 : ℝ) * x ^ 2 := by ring
    have hpow2 : x ^ 2 = Real.rpow x 2 := hpow2Nat.symm
    have hxpow : 0 < x ^ 2 := pow_pos hxpos 2
    constructor
    · calc
        |u| ≤ (5 / 8 : ℝ) * x ^ 2 := htotal
        _ ≤ x ^ 2 := by nlinarith
        _ = Real.rpow x 2 := hpow2
    · calc
        |u| ≤ (5 / 8 : ℝ) * x ^ 2 := htotal
        _ < x ^ 2 := by nlinarith
        _ = Real.rpow x 2 := hpow2
  rcases huX_and_lt with ⟨huX, huXlt⟩
  let S := (Finset.range (⌊r⌋₊ + 1)).filter (fun m : ℕ => l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r)
  have hPrimeRaw := hprime x hxp' Hm hHmLow hHmUp k hk hmod χ u huPrime huX l r hl hlr hr
  let P : ℂ := ∑ m ∈ S, (roughIndicator x γ m : ℂ) * χ (m : ZMod k) *
    Complex.exp (Complex.I * u * Real.log (m : ℝ))
  have hPrimeBound : ‖P‖ ≤ Cp * Hm * Real.rpow L (-(A + 1)) := by
    simpa [P, S, L] using hPrimeRaw
  have hHm2Log : Real.log (2 * Hm) / L ∈ Set.Icc wMin wMax := h2HmLog
  have hProxyRaw := hproxyA x hxq' Hm hHm hHmLog hHm2Log k hk hmod χ l r u
    hl hlr hr huOne huXlt
  let Qr : ℂ := ∑ m ∈ S.filter (fun m => roughAbove m (roughCutoff x)),
    (χ (m : ZMod k) : ℂ) * Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
      (roughProxy x γ m : ℂ)
  have hProxyBound : ‖Qr‖ / Hm ≤
      Real.rpow L (-1 + -A) + Cq *
        (if |u| ≤ Real.exp (L / Real.log L ^ 2) then
          Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))
        else Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) := by
    simpa [Qr, S, L, Finset.filter_filter, and_assoc, and_left_comm, and_comm,
      abs_of_pos hHmpos] using hProxyRaw.2
  have hA4 : Real.rpow L (-(A + 1)) ≤ Real.rpow L (-A) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hA4proxy : Real.rpow L (-1 + -A) ≤ Real.rpow L (-A) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by linarith)
  have hAplusCpow : Real.rpow L (A + Cq) ≤ |u| := by
    have hm := Real.rpow_le_rpow_of_exponent_le hLone hB₂proxy
    have heq : Real.rpow L (A + Cq + 1) = Real.rpow L (A + Cq) * L := by
      change L ^ (A + Cq + 1) = L ^ (A + Cq) * L
      exact Real.rpow_add_one hLpos.ne' (A + Cq)
    have hpowNonneg : 0 ≤ Real.rpow L (A + Cq) := Real.rpow_nonneg (by linarith) _
    have hlarge : 2 * Real.rpow L (A + Cq) ≤ Real.rpow L B₂ := by
      calc
        2 * Real.rpow L (A + Cq) ≤ L * Real.rpow L (A + Cq) :=
          mul_le_mul_of_nonneg_right hLtwo hpowNonneg
        _ = Real.rpow L (A + Cq + 1) := by rw [heq]; ring
        _ ≤ Real.rpow L B₂ := hm
    exact le_trans (by nlinarith [huStrong, hlarge]) huStrong
  have hlogCoef : Real.rpow L Cq / |u| ≤ Real.rpow L (-A) := by
    have huPos : 0 < |u| := lt_of_lt_of_le zero_lt_one huOne
    have hApowPos : 0 < Real.rpow L A := Real.rpow_pos_of_pos hLpos A
    have hmulEq : Real.rpow L Cq * Real.rpow L A = Real.rpow L (A + Cq) := by
      simpa [add_comm] using (Real.rpow_add hLpos Cq A).symm
    have hnegA : Real.rpow L (-A) = (Real.rpow L A)⁻¹ := by
      change L ^ (-A) = (L ^ A)⁻¹
      exact Real.rpow_neg hLpos.le A
    rw [hnegA]
    have hcross : Real.rpow L Cq * Real.rpow L A ≤ |u| := by
      calc
        Real.rpow L Cq * Real.rpow L A = Real.rpow L (A + Cq) := hmulEq
        _ ≤ |u| := hAplusCpow
    have hdiv : Real.rpow L Cq / |u| ≤ 1 / Real.rpow L A := by
      exact (div_le_div_iff₀ huPos hApowPos).2 (by simpa using hcross)
    simpa [one_div] using hdiv
  have hxPowPos : 0 < Real.rpow x cq := Real.rpow_pos_of_pos hxpos cq
  have huPos : 0 < |u| := lt_of_lt_of_le zero_lt_one huOne
  have hRoughExpBound : Real.rpow L Cq *
      Real.exp (-L / Real.rpow (Real.log L) C₃) ≤ Real.rpow L (-1 + -A) := by
    have hpowEq : Real.rpow L (A + 1 + Cq) =
        Real.rpow L (A + 1) * Real.rpow L Cq := by
      simpa [add_assoc] using Real.rpow_add hLpos (A + 1) Cq
    have hdenPos : 0 < Real.rpow L (A + 1) := Real.rpow_pos_of_pos hLpos _
    have hprod : (Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) *
        Real.rpow L (A + 1) ≤ 1 := by
      calc
        (Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) *
            Real.rpow L (A + 1) = Real.rpow L (A + 1 + Cq) *
              Real.exp (-L / Real.rpow (Real.log L) C₃) := by rw [hpowEq]; ring
        _ ≤ 1 := hdecayx
    have hdiv : Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃) ≤
        1 / Real.rpow L (A + 1) := (le_div_iff₀ hdenPos).2 hprod
    have hneg : Real.rpow L (-(A + 1)) = (Real.rpow L (A + 1))⁻¹ := by
      change L ^ (-(A + 1)) = (L ^ (A + 1))⁻¹
      exact Real.rpow_neg hLpos.le (A + 1)
    have hdiv' : Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃) ≤
        Real.rpow L (-(A + 1)) := by
      rw [hneg]
      simpa [one_div] using hdiv
    have hexp : -(A + 1) = -1 + -A := by ring
    simpa [hexp] using hdiv'
  have hProxySaving : ‖Qr‖ / Hm ≤ (1 + 2 * Cq) * Real.rpow L (-A) := by
    by_cases hmoderate : |u| ≤ Real.exp (L / Real.log L ^ 2)
    · have hbound := hProxyBound
      simp [hmoderate] at hbound
      have hUleX : |u| ≤ Real.rpow x cq := hmoderate.trans hTstar
      have hnegC : Real.rpow x (-cq) = (Real.rpow x cq)⁻¹ := by
        change x ^ (-cq) = (x ^ cq)⁻¹
        exact Real.rpow_neg hxpos.le cq
      have hXinv : Real.rpow x (-cq) ≤ |u|⁻¹ := by
        rw [hnegC]
        have hdiv : (1 : ℝ) / Real.rpow x cq ≤ 1 / |u| := by
          apply (div_le_div_iff₀ hxPowPos huPos).2
          simpa using hUleX
        simpa [one_div] using hdiv
      have hterms : |u|⁻¹ + Real.rpow x (-cq) ≤ 2 * |u|⁻¹ := by nlinarith [hXinv]
      have hmul : Cq * (Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))) ≤
          2 * Cq * Real.rpow L (-A) := by
        calc
          Cq * (Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))) ≤
              Cq * (Real.rpow L Cq * (2 * |u|⁻¹)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hterms (Real.rpow_nonneg (by linarith) _)) hCq.le
          _ = 2 * Cq * (Real.rpow L Cq / |u|) := by ring
          _ ≤ 2 * Cq * Real.rpow L (-A) :=
            mul_le_mul_of_nonneg_left hlogCoef (by positivity)
      calc
        ‖Qr‖ / Hm ≤ Real.rpow L (-1 + -A) +
            Cq * (Real.rpow L Cq * (|u|⁻¹ + Real.rpow x (-cq))) := hbound
        _ ≤ Real.rpow L (-A) + 2 * Cq * Real.rpow L (-A) :=
          add_le_add hA4proxy hmul
        _ = (1 + 2 * Cq) * Real.rpow L (-A) := by ring
    · have hbound := hProxyBound
      simp [hmoderate] at hbound
      calc
        ‖Qr‖ / Hm ≤ Real.rpow L (-1 + -A) +
            Cq * (Real.rpow L Cq * Real.exp (-L / Real.rpow (Real.log L) C₃)) := hbound
        _ ≤ Real.rpow L (-A) + Cq * Real.rpow L (-1 + -A) :=
          add_le_add hA4proxy (mul_le_mul_of_nonneg_left hRoughExpBound hCq.le)
        _ ≤ Real.rpow L (-A) + Cq * Real.rpow L (-A) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hA4proxy hCq.le)
        _ ≤ (1 + 2 * Cq) * Real.rpow L (-A) := by
          have hnonneg : 0 ≤ Real.rpow L (-A) := Real.rpow_nonneg (by linarith) _
          nlinarith [hCq, hnonneg]
  have hProxyDiv : ‖Qr / Hm‖ ≤ (1 + 2 * Cq) * Real.rpow L (-A) := by
    simpa [norm_div, Real.norm_eq_abs, abs_of_pos hHmpos] using hProxySaving
  let Q : ℂ := ∑ m ∈ S,
    (χ (m : ZMod k) : ℂ) * Complex.exp (Complex.I * u * Real.log (m : ℝ)) *
      (roughProxy x γ m : ℂ)
  have hQeq : Q = Qr := by
    dsimp [Q, Qr, S]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hi : l ≤ (m : ℝ) ∧ (m : ℝ) ≤ r
    · by_cases hrough : roughAbove m (roughCutoff x)
      · simp [hi, hrough]
      · simp [hi, roughProxy, hrough]
    · simp [hi]
  have hdecomp :
      (∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) = P - Q := by
    dsimp [P, Q]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    simpa [u] using roughCoefficient_phase_split x γ v t m (χ (m : ZMod k))
  have hPrimeDiv : ‖P / Hm‖ ≤ Cp * Real.rpow L (-A) := by
    have hdiv : ‖P‖ / Hm ≤ Cp * Real.rpow L (-(A + 1)) := by
      apply (div_le_iff₀ hHmpos).2
      nlinarith [hPrimeBound]
    have hnorm : ‖P / Hm‖ = ‖P‖ / Hm := by
      simp [norm_div, Real.norm_eq_abs, abs_of_pos hHmpos]
    rw [hnorm]
    calc
      ‖P‖ / Hm ≤ Cp * Real.rpow L (-(A + 1)) := hdiv
      _ ≤ Cp * Real.rpow L (-A) :=
        mul_le_mul_of_nonneg_left hA4 hCp.le
  have hsum : ‖(∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
      ‖P / Hm‖ + ‖Qr / Hm‖ := by
    have heq :
        (∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm = P / Hm - Qr / Hm := by
      rw [hdecomp, hQeq]
      ring
    rw [heq]
    exact norm_sub_le _ _
  have htotal : ‖(∑ m ∈ S, roughCoefficient x γ v m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) / Hm‖ ≤
      C₀ * Real.rpow L (-A) := by
    calc
      _ ≤ ‖P / Hm‖ + ‖Qr / Hm‖ := hsum
      _ ≤ Cp * Real.rpow L (-A) + (1 + 2 * Cq) * Real.rpow L (-A) :=
        add_le_add hPrimeDiv hProxyDiv
      _ = C₀ * Real.rpow L (-A) := by simp [C₀]; ring
  simpa [S, L] using htotal

private theorem dyadic_filter_isNatInterval (H : ℝ) (I : Set ℕ)
    (hI : IsNatInterval I) :
    IsNatInterval (((dyadicIntegers H).filter (fun m => m ∈ I)) : Set ℕ) := by
  classical
  intro m n k hm hn hmk hkn
  have hm' : m ∈ (dyadicIntegers H).filter (fun m => m ∈ I) := by simpa using hm
  have hn' : n ∈ (dyadicIntegers H).filter (fun m => m ∈ I) := by simpa using hn
  rcases Finset.mem_filter.mp hm' with ⟨hmD, hmI⟩
  rcases Finset.mem_filter.mp hn' with ⟨hnD, hnI⟩
  have hmDyadic : m ∈ Finset.range (⌊2 * H⌋₊ + 1) ∧
      H ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * H := by
    simpa only [dyadicIntegers, Finset.mem_filter, Finset.mem_range] using hmD
  have hnDyadic : n ∈ Finset.range (⌊2 * H⌋₊ + 1) ∧
      H ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * H := by
    simpa only [dyadicIntegers, Finset.mem_filter, Finset.mem_range] using hnD
  have hkRange : k < ⌊2 * H⌋₊ + 1 := by
    have hmRange : m < ⌊2 * H⌋₊ + 1 := Finset.mem_range.mp hmDyadic.1
    have hnRange : n < ⌊2 * H⌋₊ + 1 := Finset.mem_range.mp hnDyadic.1
    have hmax : max m n < ⌊2 * H⌋₊ + 1 := max_lt_iff.mpr ⟨hmRange, hnRange⟩
    exact lt_of_le_of_lt hkn hmax
  have hkLower : H ≤ (k : ℝ) := by
    rcases le_total m n with hmn | hnm
    · have hmk' : m ≤ k := by simpa [min_eq_left hmn] using hmk
      exact hmDyadic.2.1.trans (by exact_mod_cast hmk')
    · have hnk' : n ≤ k := by simpa [min_eq_right hnm] using hmk
      exact hnDyadic.2.1.trans (by exact_mod_cast hnk')
  have hkUpper : (k : ℝ) ≤ 2 * H := by
    rcases le_total m n with hmn | hnm
    · have hkn' : k ≤ n := by simpa [max_eq_right hmn] using hkn
      have hknCast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn'
      exact hknCast.trans hnDyadic.2.2
    · have hkm' : k ≤ m := by simpa [max_eq_left hnm] using hkn
      have hkmCast : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm'
      exact hkmCast.trans hmDyadic.2.2
  have hkD : k ∈ dyadicIntegers H := by
    simp only [dyadicIntegers, Finset.mem_filter, Finset.mem_range]
    exact ⟨hkRange, hkLower, hkUpper⟩
  exact Finset.mem_filter.mpr ⟨hkD, hI hmI hnI hmk hkn⟩

private theorem rough_family_long_cancellation
    (γ wMin wMax δ C c₁ c₂ : ℝ)
    (hγ : 0 < γ) (hγw : γ < wMin) (hw : wMin < wMax)
    (hwMax : wMax < 1) (hδ : 0 < δ) (hC : 0 < C) (hc₂ : 0 < c₂)
    (family : CoefficientFamily δ C c₁ c₂)
    (hroughData : ∀ x : ℝ, family.xMin ≤ x →
      family.interval x = ∅ ∨
        ∃ v : ℝ, |v| ≤ Real.rpow (Real.log x) C ∧
          Real.log (family.Hm x) / Real.log x ∈ Set.Icc wMin wMax ∧
          Real.log (2 * family.Hm x) / Real.log x ∈ Set.Icc wMin wMax ∧
          ∀ m ∈ family.interval x,
            family.alpha x m = roughCoefficient x γ v m) :
    HasLongCoefficientCancellation family := by
  classical
  intro A₀ B A hA₀ hB hA
  let Cfreq := max C (A₀ + 1)
  have hCfreq : 0 < Cfreq := by dsimp [Cfreq]; positivity
  have hC_Cfreq : C ≤ Cfreq := le_max_left _ _
  have hA₀_Cfreq : A₀ ≤ Cfreq := by
    dsimp [Cfreq]
    exact le_trans (le_of_lt (by linarith : A₀ < A₀ + 1)) (le_max_right _ _)
  obtain ⟨B₂, CH, xH, hB₂, hCH, hxH, hHigh⟩ :=
    high_frequency_upper_scale γ wMin wMax δ Cfreq A c₂
      hγ hγw hw hwMax hδ hCfreq hA hc₂ B hB
  obtain ⟨CL, xL, hCL, hxL, hLow⟩ :=
    low_frequency γ wMin wMax Cfreq δ hγ hγw hw hδ hCfreq
      A₀ A B₂ hA₀ hA hB₂
  let Ctot := CH + CL
  let xinner := max family.xMin (max xH xL)
  let xlog := max (Real.exp 1) xinner
  let x₀ := max 2 xlog
  have hCtot : 0 < Ctot := by dsimp [Ctot]; positivity
  have hx₀two : 2 ≤ x₀ := le_max_left _ _
  have hx₀min : family.xMin ≤ x₀ := by
    dsimp [x₀, xlog, xinner]
    exact le_trans (le_trans (le_max_left family.xMin (max xH xL))
      (le_max_right (Real.exp 1) (max family.xMin (max xH xL))))
      (le_max_right 2 (max (Real.exp 1) (max family.xMin (max xH xL))))
  have hx₀H : xH ≤ x₀ := by
    dsimp [x₀, xlog, xinner]
    exact le_trans (le_trans (le_trans (le_max_left xH xL)
      (le_max_right family.xMin (max xH xL)))
      (le_max_right (Real.exp 1) (max family.xMin (max xH xL))))
      (le_max_right 2 (max (Real.exp 1) (max family.xMin (max xH xL))))
  have hx₀L : xL ≤ x₀ := by
    dsimp [x₀, xlog, xinner]
    exact le_trans (le_trans (le_trans (le_max_right xH xL)
      (le_max_right family.xMin (max xH xL)))
      (le_max_right (Real.exp 1) (max family.xMin (max xH xL))))
      (le_max_right 2 (max (Real.exp 1) (max family.xMin (max xH xL))))
  have hx₀exp : Real.exp 1 ≤ x₀ := by
    dsimp [x₀, xlog]
    exact le_trans (le_max_left (Real.exp 1) xinner)
      (le_max_right 2 (max (Real.exp 1) xinner))
  refine ⟨Ctot, x₀, hCtot, hx₀two, hx₀min, ?_⟩
  intro x hx k hk1 hkA₀ χ t ht
  have hxMin : family.xMin ≤ x := hx₀min.trans hx
  have hxH' : xH ≤ x := hx₀H.trans hx
  have hxL' : xL ≤ x := hx₀L.trans hx
  have hx₂ : 2 ≤ x := le_trans hx₀two hx
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxexp : Real.exp 1 ≤ x := hx₀exp.trans hx
  have hLone : 1 ≤ Real.log x := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hxexp
    simpa using hlog
  have hscale := family.scales x hxMin
  rcases hscale with ⟨hHmδ, hHnδ, hprodLo, hprodHi⟩
  have hHmpos : 0 < family.Hm x :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHmδ
  have hHnpos : 0 < family.Hn x :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHnδ
  have hXpos : 0 < family.Hm x * family.Hn x := mul_pos hHmpos hHnpos
  have hXle : family.Hm x * family.Hn x ≤ c₂ * x := hprodHi
  have hlogxpos : 0 < Real.log x := hLpos
  have hfreqK : (k : ℝ) ≤ Real.rpow (Real.log x) Cfreq := by
    exact le_trans hkA₀ (Real.rpow_le_rpow_of_exponent_le hLone hA₀_Cfreq)
  let S := familyTerms family x
  have hSinterval : IsNatInterval (S : Set ℕ) := by
    simpa [S, familyTerms] using
      dyadic_filter_isNatInterval (family.Hm x) (family.interval x)
        (family.interval_property x)
  by_cases hSempty : S = ∅
  · have hsumzero : (∑ m ∈ S, family.alpha x m * χ (m : ZMod k) *
        Complex.exp (Complex.I * t * Real.log (m : ℝ))) = 0 := by
      simp [hSempty]
    rw [hsumzero]
    simp only [norm_zero, zero_div]
    exact (mul_nonneg (le_of_lt hCtot) (Real.rpow_nonneg (le_of_lt hLpos) _))
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
    obtain ⟨a, b, hab, hSends⟩ :=
      ArtinPrimitiveRoots.Proofs.r_typeii_p.finite_nat_interval_endpoints
        S hSinterval hSne
    rcases hroughData x hxMin with hdata | ⟨v, hv, hlogHm, hlog2Hm, halpha⟩
    · have hSempty' : S = ∅ := by simp [S, familyTerms, hdata]
      exact (hSempty hSempty').elim
    · have hHmLog : Real.log (family.Hm x) / Real.log x ∈ Set.Icc wMin wMax := hlogHm
      have h2HmLog : Real.log (2 * family.Hm x) / Real.log x ∈ Set.Icc wMin wMax := hlog2Hm
      have hvfreq : |v| ≤ Real.rpow (Real.log x) Cfreq :=
        hv.trans (Real.rpow_le_rpow_of_exponent_le hLone hC_Cfreq)
      have haMem : a ∈ S := by rw [hSends]; exact Finset.mem_Icc.mpr ⟨le_rfl, hab⟩
      have hbMem : b ∈ S := by rw [hSends]; exact Finset.mem_Icc.mpr ⟨hab, le_rfl⟩
      have haBounds := (family.interval_bounds x hxMin a
        (Finset.mem_filter.mp haMem).2)
      have hbBounds := (family.interval_bounds x hxMin b
        (Finset.mem_filter.mp hbMem).2)
      have hl : family.Hm x ≤ (a : ℝ) := haBounds.1
      have hr : (b : ℝ) ≤ 2 * family.Hm x := hbBounds.2
      have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hT : (Finset.range (⌊(b : ℝ)⌋₊ + 1)).filter
          (fun m : ℕ => (a : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (b : ℝ)) =
            Finset.Icc a b := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
          Nat.floor_natCast, Nat.cast_le]
        omega
      have hS_eq_T : S = (Finset.range (⌊(b : ℝ)⌋₊ + 1)).filter
          (fun m : ℕ => (a : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (b : ℝ)) := by
        rw [hSends, hT]
      let Poly := ∑ m ∈ (Finset.range (⌊(b : ℝ)⌋₊ + 1)).filter
          (fun m : ℕ => (a : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (b : ℝ)),
          roughCoefficient x γ v m * χ (m : ZMod k) *
            Complex.exp (Complex.I * t * Real.log (m : ℝ))
      have hsumEq : (∑ m ∈ S, family.alpha x m * χ (m : ZMod k) *
          Complex.exp (Complex.I * t * Real.log (m : ℝ))) = Poly := by
        dsimp [Poly]
        rw [← hS_eq_T]
        apply Finset.sum_congr rfl
        intro m hm
        rw [halpha m (Finset.mem_filter.mp hm).2]
      have hFreqBound :
          ‖Poly / (family.Hm x : ℂ)‖ ≤ Ctot * Real.rpow (Real.log x) (-A) := by
        by_cases htLow : |t| ≤ Real.rpow (Real.log x) B₂
        · have h := hLow x hxL' (family.Hm x) hHmδ hHmLog
            (a : ℝ) (b : ℝ) hl habReal hr v t hvfreq htLow k hk1 hkA₀ χ
          have h' : ‖Poly / (family.Hm x : ℂ)‖ ≤ CL * Real.rpow (Real.log x) (-A) := by
            simpa [Poly] using h
          calc
            _ ≤ CL * Real.rpow (Real.log x) (-A) := h'
            _ ≤ Ctot * Real.rpow (Real.log x) (-A) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
              dsimp [Ctot]
              linarith [hCH]
        · have htHigh : Real.rpow (Real.log x) B₂ ≤ |t| := le_of_not_ge htLow
          obtain hscale' := family.scales x hxMin
          rcases hscale' with ⟨hHmδ', hHnδ', hprodLo', hprodHi'⟩
          have h := hHigh x hxH' (family.Hm x)
            (family.Hm x * family.Hn x) hHmδ' hXpos hXle hHmLog h2HmLog
            k hk1 hfreqK χ v t htHigh ht hvfreq (a : ℝ) (b : ℝ) hl habReal hr
          have h' : ‖Poly / (family.Hm x : ℂ)‖ ≤ CH * Real.rpow (Real.log x) (-A) := by
            simpa [Poly] using h
          calc
            _ ≤ CH * Real.rpow (Real.log x) (-A) := h'
            _ ≤ Ctot * Real.rpow (Real.log x) (-A) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
              dsimp [Ctot]
              linarith [hCL]
      have hnormDiv : ‖Poly / (family.Hm x : ℂ)‖ = ‖Poly‖ / family.Hm x := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hHmpos]
      have hPolyNorm : ‖Poly‖ / family.Hm x ≤ Ctot * Real.rpow (Real.log x) (-A) := by
        rw [← hnormDiv]
        exact hFreqBound
      rw [hsumEq]
      exact hPolyNorm

private structure RoughTypeIIData where
  Hm : ℝ
  Hn : ℝ
  interval : Set ℕ
  v : ℝ
  beta : ℕ → ℂ
  F : ℕ → ℂ

/-- `prop:rough-type-ii` — `08-type-ii.tex:321-536`. Fix the parameters in the
paper. Uniformly over admissible dyads, intervals, real twists, rough second-variable coefficients,
and marked-invariant multipliers, the coefficient `roughCoefficient` has the Type II saving once
`K` is sufficiently large. Correction 6 from review lane `rev-b` imposes the interval and ordered
scale hypotheses. -/
theorem rough_type_ii
    (γ wMin wMax δ C Dstar q_d c₁ c₂ : ℝ)
    (hγ : 0 < γ) (hγwMin : γ < wMin) (hwMinMax : wMin < wMax)
    (hwMax : wMax < 1)
    (hδ : 0 < δ) (hC : 0 < C) (hD : 0 < Dstar)
    (hqd₀ : 0 < q_d) (hqd₁ : q_d < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₁₂ : c₁ ≤ c₂) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ a : Fin K → ℝ, ValidBands K a →
        ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x →
            ∀ Hm Hn : ℝ,
              Real.rpow x δ ≤ Hm → Real.rpow x δ ≤ Hn →
              c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
              Real.log Hm / Real.log x ∈ Set.Icc wMin wMax →
              Real.log (2 * Hm) / Real.log x ∈ Set.Icc wMin wMax →
              ∀ I : Set ℕ, IsNatInterval I →
                I ⊆ {m : ℕ | Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * Hm} →
                ∀ v : ℝ, |v| ≤ Real.rpow (Real.log x) C →
                  ∀ beta : ℕ → ℂ,
                    (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers Hn ∧
                      roughAbove n (roughCutoff x)) →
                    (∀ n ∈ dyadicIntegers Hn,
                      ‖beta n‖ ≤ Real.rpow (Real.log x) C) →
                    ∀ F : ℕ → ℂ, IsMarkedInvariant x K a F →
                      ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
                        ∑ n ∈ dyadicIntegers Hn,
                          roughCoefficient x γ v m * beta n * F (m * n - 1) *
                            (markedWeight x K a q_d (m * n - 1) : ℂ)‖ ≤
                        C' * (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by
  classical
  let δ' := min δ (1 / 4 : ℝ)
  have hδ'pos : 0 < δ' := by dsimp [δ']; positivity
  have hδ'δ : δ' ≤ δ := by dsimp [δ']; exact min_le_left _ _
  have hδ'quarter : δ' ≤ 1 / 4 := by dsimp [δ']; exact min_le_right _ _
  have hδ'half : δ' < 1 / 2 := by linarith

  let fillDiff := 1 - 2 * δ'
  have hfillDiff : 0 < fillDiff := by dsimp [fillDiff]; linarith
  obtain ⟨Tfill, hTfill⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hfillDiff).eventually_ge_atTop (1 / c₁))
  have hfill_bound : ∀ x : ℝ, 2 ≤ x → Tfill ≤ x →
      Real.rpow x δ' ≤ Real.sqrt (c₁ * x) := by
    intro x hx₂ hxT
    have hxpos : 0 < x := by linarith
    have hpowlower := hTfill x hxT
    have hfactor : 1 ≤ c₁ * Real.rpow x fillDiff := by
      have h := (div_le_iff₀ hc₁).mp hpowlower
      simpa [mul_comm] using h
    have hpowMul : Real.rpow x fillDiff * Real.rpow x (2 * δ') = x := by
      change x ^ fillDiff * x ^ (2 * δ') = x
      rw [← Real.rpow_add hxpos fillDiff (2 * δ')]
      have he : fillDiff + 2 * δ' = 1 := by dsimp [fillDiff]; ring
      rw [he, Real.rpow_one]
    have hpowSq : (Real.rpow x δ') ^ 2 = Real.rpow x (2 * δ') := by
      calc
        (Real.rpow x δ') ^ 2 = Real.rpow x δ' * Real.rpow x δ' := by ring
        _ = Real.rpow x (δ' + δ') := by
          change x ^ δ' * x ^ δ' = x ^ (δ' + δ')
          exact (Real.rpow_add hxpos δ' δ').symm
        _ = Real.rpow x (2 * δ') := by congr 1 <;> ring
    have hsq : (Real.rpow x δ') ^ 2 ≤ c₁ * x := by
      rw [hpowSq]
      calc
        Real.rpow x (2 * δ') = 1 * Real.rpow x (2 * δ') := by ring
        _ ≤ (c₁ * Real.rpow x fillDiff) * Real.rpow x (2 * δ') :=
          mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by linarith : 0 ≤ x) _)
        _ = c₁ * x := by rw [mul_assoc, hpowMul]
    exact Real.le_sqrt_of_sq_le hsq

  have hL76 : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) (76 / 100 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 76 / 100)).comp
      Real.tendsto_log_atTop
  obtain ⟨Tcut, hTcut⟩ := Filter.eventually_atTop.mp
    (hL76.eventually_ge_atTop (1 / γ))
  have hcut_bound : ∀ x : ℝ, 2 ≤ x → Tcut ≤ x →
      roughCutoff x ≤ Real.rpow x γ := by
    intro x hx₂ hxT
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hLlarge := hTcut x hxT
    have hfactor : 1 ≤ γ * Real.rpow (Real.log x) (76 / 100 : ℝ) := by
      have h := (div_le_iff₀ hγ).mp hLlarge
      simpa [mul_comm] using h
    have hsplit : Real.rpow (Real.log x) (76 / 100 : ℝ) *
        Real.rpow (Real.log x) (24 / 100 : ℝ) = Real.log x := by
      change (Real.log x) ^ (76 / 100 : ℝ) *
        (Real.log x) ^ (24 / 100 : ℝ) = Real.log x
      rw [← Real.rpow_add hLpos]
      rw [show (76 / 100 + 24 / 100 : ℝ) = 1 by norm_num]
      exact Real.rpow_one _
    have hpow24 : Real.rpow (Real.log x) (24 / 100 : ℝ) ≤
        γ * Real.log x := by
      have hmul := mul_le_mul_of_nonneg_right hfactor
        (Real.rpow_nonneg hLpos.le (24 / 100 : ℝ))
      calc
        Real.rpow (Real.log x) (24 / 100 : ℝ) =
            1 * Real.rpow (Real.log x) (24 / 100 : ℝ) := by ring
        _ ≤ (γ * Real.rpow (Real.log x) (76 / 100 : ℝ)) *
            Real.rpow (Real.log x) (24 / 100 : ℝ) := hmul
        _ = γ * Real.log x := by rw [mul_assoc, hsplit]
    calc
      roughCutoff x = Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ)) := rfl
      _ ≤ Real.exp (γ * Real.log x) := Real.exp_le_exp.mpr hpow24
      _ = Real.rpow x γ := by
        calc
          Real.exp (γ * Real.log x) = Real.exp (Real.log x * γ) := by rw [mul_comm]
          _ = Real.rpow x γ := (Real.rpow_def_of_pos hxpos γ).symm

  have hroughCoefficient_support : ∀ x : ℝ, roughCutoff x ≤ Real.rpow x γ →
      ∀ v : ℝ, ∀ m : ℕ, roughCoefficient x γ v m ≠ 0 →
        roughAbove m (roughCutoff x) := by
    intro x hcut v m hcoeff
    by_contra hroughW
    have hbad : ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ (p : ℝ) ≤ roughCutoff x := by
      unfold roughAbove at hroughW
      push_neg at hroughW
      exact hroughW
    rcases hbad with ⟨p, hp, hpdvd, hpW⟩
    have hnotγ : ¬ roughAbove m (Real.rpow x γ) := by
      intro hrough
      have hlt := hrough p hp hpdvd
      have hle : (p : ℝ) ≤ Real.rpow x γ := hpW.trans hcut
      exact (not_lt_of_ge hle) hlt
    have hnotγ' : ¬ roughAbove m (x ^ γ) := by
      change ¬ roughAbove m (Real.rpow x γ)
      exact hnotγ
    apply hcoeff
    unfold roughCoefficient
    simp [hnotγ', hroughW]

  have hcontinuousMap : ContinuousOn (fun w : ℝ => (γ, w)) (Set.Icc wMin wMax) := by
    fun_prop
  have hmaps : Set.MapsTo (fun w : ℝ => (γ, w)) (Set.Icc wMin wMax)
      {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    intro w hw
    exact ⟨hγ, hγwMin.trans_le hw.1⟩
  have hcontinuousDensity : ContinuousOn
      (fun w : ℝ => roughDensity γ w) (Set.Icc wMin wMax) := by
    have h := density_regularity.1.comp' hcontinuousMap hmaps
    simpa using h
  obtain ⟨Ddensity, hDdensity⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcontinuousDensity
  let Bdensity := max Ddensity 1
  have hBdensityPos : 0 < Bdensity := by dsimp [Bdensity]; positivity
  have hDensityAbs : ∀ w : ℝ, w ∈ Set.Icc wMin wMax →
      |roughDensity γ w| ≤ Bdensity := by
    intro w hw
    have h := hDdensity w hw
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  let cM := Real.exp (-Real.eulerMascheroniConstant)
  have hcM : 0 < cM := by dsimp [cM]; positivity
  let coeffBound := 1 + 2 * Bdensity / cM
  have hcoeffBoundPos : 0 < coeffBound := by dsimp [coeffBound]; positivity
  obtain ⟨y₀, hy₀, hMertens⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.2 (cM / 2) (by positivity)
  have hWtendsto : Filter.Tendsto (fun x : ℝ => roughCutoff x)
      Filter.atTop Filter.atTop := by
    have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 24 / 100)).comp
      Real.tendsto_log_atTop
    change Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (24 / 100 : ℝ)))
      Filter.atTop Filter.atTop
    exact Real.tendsto_exp_atTop.comp hL
  obtain ⟨Ty, hTy⟩ := Filter.eventually_atTop.mp
    (hWtendsto.eventually_ge_atTop y₀)
  obtain ⟨Tl, hTl⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))
  have hpowC : Filter.Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) C) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hC).comp Real.tendsto_log_atTop
  obtain ⟨TC, hTC⟩ := Filter.eventually_atTop.mp
    (hpowC.eventually_ge_atTop coeffBound)
  let Tcoeff := max 2 (max Ty (max Tl TC))
  have hcoeff_bound : ∀ x : ℝ, Tcoeff ≤ x → ∀ v : ℝ, ∀ m : ℕ,
      Real.log (m : ℝ) / Real.log x ∈ Set.Icc wMin wMax →
        ‖roughCoefficient x γ v m‖ ≤ Real.rpow (Real.log x) C := by
    intro x hx v m hw
    have hx₂ : 2 ≤ x := le_trans (le_max_left 2 _) hx
    have hTyCoeff : Ty ≤ Tcoeff := by
      dsimp [Tcoeff]
      exact le_trans (le_max_left Ty (max Tl TC)) (le_max_right 2 _)
    have hTlCoeff : Tl ≤ Tcoeff := by
      dsimp [Tcoeff]
      exact le_trans (le_trans (le_max_left Tl TC) (le_max_right Ty _))
        (le_max_right 2 _)
    have hTCCoeff : TC ≤ Tcoeff := by
      dsimp [Tcoeff]
      exact le_trans (le_trans (le_max_right Tl TC) (le_max_right Ty _))
        (le_max_right 2 _)
    have hTyx : Ty ≤ x := hTyCoeff.trans hx
    have hTlx : Tl ≤ x := hTlCoeff.trans hx
    have hTCx : TC ≤ x := hTCCoeff.trans hx
    have hxpos : 0 < x := by linarith
    have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hLone : 1 ≤ Real.log x := hTl x hTlx
    let W := roughCutoff x
    let V := roughSieveProduct W
    have hWlarge : y₀ ≤ W := hTy x hTyx
    have hlogW : Real.log W = Real.rpow (Real.log x) (24 / 100 : ℝ) := by
      simp [W, roughCutoff]
    have hlogWpos : 0 < Real.log W := by
      rw [hlogW]
      exact Real.rpow_pos_of_pos hLpos _
    have hlogWle : Real.log W ≤ Real.log x := by
      rw [hlogW]
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hLone
          (by norm_num : (24 / 100 : ℝ) ≤ 1))
    have hMerr := hMertens W hWlarge
    have hVlog : cM / 2 ≤ V * Real.log W := by
      have h := abs_le.mp hMerr
      dsimp [cM] at h ⊢
      linarith
    have hVpos : 0 < V := by
      by_contra h
      have hVnonpos : V ≤ 0 := le_of_not_gt h
      have hnonpos : Real.log W * V ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlogWpos.le hVnonpos
      have hnonpos' : V * Real.log W ≤ 0 := by simpa [mul_comm] using hnonpos
      linarith [hVlog]
    have hLV : cM / 2 ≤ Real.log x * V := by
      calc
        cM / 2 ≤ V * Real.log W := hVlog
        _ ≤ V * Real.log x := mul_le_mul_of_nonneg_left hlogWle hVpos.le
        _ = Real.log x * V := by ring
    have hLVpos : 0 < Real.log x * V := lt_of_lt_of_le (by positivity) hLV
    have hLVbound :
        |roughDensity γ (Real.log (m : ℝ) / Real.log x) / (Real.log x * V)| ≤
          2 * Bdensity / cM := by
      have hdens := hDensityAbs (Real.log (m : ℝ) / Real.log x) hw
      rw [abs_div, abs_of_pos hLVpos]
      calc
        |roughDensity γ (Real.log (m : ℝ) / Real.log x)| / (Real.log x * V) ≤
            Bdensity / (Real.log x * V) :=
              div_le_div_of_nonneg_right hdens hLVpos.le
        _ ≤ Bdensity / (cM / 2) :=
              div_le_div_of_nonneg_left hBdensityPos.le (by positivity) hLV
        _ = 2 * Bdensity / cM := by field_simp [ne_of_gt hcM] <;> ring
    have hphase : ‖Complex.exp (Complex.I * v * Real.log (m : ℝ))‖ = 1 := by
      have harg : Complex.I * (v : ℂ) * (Real.log (m : ℝ) : ℂ) =
          Complex.I * ((v * Real.log (m : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, Complex.norm_exp_I_mul_ofReal]
    let e₁ : ℝ := if roughAbove m (Real.rpow x γ) then 1 else 0
    let e₂ : ℝ := if roughAbove m W then 1 else 0
    let d : ℝ := roughDensity γ (Real.log (m : ℝ) / Real.log x) /
      (Real.log x * V)
    have he₁ : |e₁| ≤ 1 := by dsimp [e₁]; split_ifs <;> norm_num
    have he₂ : |e₂| ≤ 1 := by dsimp [e₂]; split_ifs <;> norm_num
    have hd : |d| ≤ 2 * Bdensity / cM := by simpa [d] using hLVbound
    have hscalar :
        (if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
          roughDensity γ (Real.log (m : ℝ) / Real.log x) /
            (Real.log x * roughSieveProduct (roughCutoff x)) *
              (if roughAbove m W then (1 : ℝ) else 0) = e₁ - d * e₂ := by
      rfl
    have hEqNorm : ‖roughCoefficient x γ v m‖ = |e₁ - d * e₂| := by
      calc
        ‖roughCoefficient x γ v m‖ =
            ‖Complex.exp (Complex.I * v * Real.log (m : ℝ)) *
              (((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
                roughDensity γ (Real.log (m : ℝ) / Real.log x) /
                  (Real.log x * roughSieveProduct (roughCutoff x)) *
                    (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)‖ := rfl
        _ = ‖Complex.exp (Complex.I * v * Real.log (m : ℝ))‖ *
              ‖(((if roughAbove m (Real.rpow x γ) then (1 : ℝ) else 0) -
                roughDensity γ (Real.log (m : ℝ) / Real.log x) /
                  (Real.log x * roughSieveProduct (roughCutoff x)) *
                    (if roughAbove m (roughCutoff x) then (1 : ℝ) else 0)) : ℂ)‖ :=
                norm_mul _ _
        _ = |e₁ - d * e₂| := by
              rw [hphase, ← Complex.ofReal_mul, ← Complex.ofReal_div,
                ← Complex.ofReal_mul, ← Complex.ofReal_sub,
                Complex.norm_real, Real.norm_eq_abs, one_mul, hscalar]
    have hamp : |e₁ - d * e₂| ≤ coeffBound := by
      calc
        |e₁ - d * e₂| ≤ |e₁| + |d * e₂| := by
          simpa [sub_eq_add_neg, neg_mul] using abs_add_le e₁ (-d * e₂)
        _ ≤ 1 + |d| * |e₂| := add_le_add he₁ (by rw [abs_mul])
        _ ≤ 1 + (2 * Bdensity / cM) * 1 := by
          have hprod : |d| * |e₂| ≤ (2 * Bdensity / cM) * 1 := by
            calc
              |d| * |e₂| ≤ (2 * Bdensity / cM) * |e₂| :=
                mul_le_mul_of_nonneg_right hd (abs_nonneg e₂)
              _ ≤ (2 * Bdensity / cM) * 1 :=
                mul_le_mul_of_nonneg_left he₂ (by positivity)
          nlinarith
        _ = coeffBound := by dsimp [coeffBound]; ring
    calc
      ‖roughCoefficient x γ v m‖ = |e₁ - d * e₂| := hEqNorm
      _ ≤ coeffBound := hamp
      _ ≤ Real.rpow (Real.log x) C := hTC x hTCx

  let T := max 2 (max Tfill (max Tcut Tcoeff))
  have hTtwo : 2 ≤ T := le_max_left _ _
  have hTfillLe : Tfill ≤ T := by
    dsimp [T]
    exact le_trans (le_max_left Tfill (max Tcut Tcoeff)) (le_max_right 2 _)
  have hTcutLe : Tcut ≤ T := by
    dsimp [T]
    exact le_trans (le_trans (le_max_left Tcut Tcoeff) (le_max_right Tfill _))
      (le_max_right 2 _)
  have hTcoeffLe : Tcoeff ≤ T := by
    dsimp [T]
    exact le_trans (le_trans (le_max_right Tcut Tcoeff) (le_max_right Tfill _))
      (le_max_right 2 _)
  have hfill_at : ∀ x : ℝ, T ≤ x → Real.rpow x δ' ≤ Real.sqrt (c₁ * x) := by
    intro x hx
    exact hfill_bound x (le_trans hTtwo hx) (le_trans hTfillLe hx)
  have hcut_at : ∀ x : ℝ, T ≤ x → roughCutoff x ≤ Real.rpow x γ := by
    intro x hx
    exact hcut_bound x (le_trans hTtwo hx) (le_trans hTcutLe hx)
  have hcoef_at : ∀ x : ℝ, T ≤ x → ∀ v : ℝ, ∀ m : ℕ,
      Real.log (m : ℝ) / Real.log x ∈ Set.Icc wMin wMax →
        ‖roughCoefficient x γ v m‖ ≤ Real.rpow (Real.log x) C := by
    intro x hx v m hw
    exact hcoeff_bound x (le_trans hTcoeffLe hx) v m hw

  obtain ⟨K₀, htransfer⟩ :=
    marked_coefficient_transfer δ' C Dstar q_d c₁ c₂
      hδ'pos hC hD hqd₀ hqd₁ hc₁ hc₂ hc₁₂
  refine ⟨K₀, ?_⟩
  intro K hK a ha
  let Good : ℝ → RoughTypeIIData → Prop := fun x d =>
    Real.rpow x δ' ≤ d.Hm ∧
    Real.rpow x δ' ≤ d.Hn ∧
    c₁ * x ≤ d.Hm * d.Hn ∧
    d.Hm * d.Hn ≤ c₂ * x ∧
    (d.interval = ∅ ∨
      (Real.log d.Hm / Real.log x ∈ Set.Icc wMin wMax ∧
        Real.log (2 * d.Hm) / Real.log x ∈ Set.Icc wMin wMax)) ∧
    IsNatInterval d.interval ∧
    d.interval ⊆ {m : ℕ | d.Hm ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * d.Hm} ∧
    |d.v| ≤ Real.rpow (Real.log x) C ∧
    (∀ n, d.beta n ≠ 0 → n ∈ dyadicIntegers d.Hn ∧
      roughAbove n (roughCutoff x)) ∧
    (∀ n ∈ dyadicIntegers d.Hn,
      ‖d.beta n‖ ≤ Real.rpow (Real.log x) C) ∧
    IsMarkedInvariant x K a d.F ∧
    roughCutoff x ≤ Real.rpow x γ
  let default : ℝ → RoughTypeIIData := fun x =>
    { Hm := Real.sqrt (c₁ * x)
      Hn := Real.sqrt (c₁ * x)
      interval := ∅
      v := 0
      beta := fun _ => 0
      F := fun _ => 0 }
  let score : ℝ → RoughTypeIIData → ℝ := fun x d =>
    ‖markedBilinearSum x K a q_d d.F d.Hm d.Hn d.interval
      (fun m => roughCoefficient x γ d.v m) d.beta‖ /
      ((d.Hm * d.Hn) * Real.rpow (Real.log x) (-Dstar))
  have hdefault : ∀ x : ℝ, T ≤ x → Good x (default x) := by
    intro x hx
    dsimp [Good, default]
    have hx₂ : 2 ≤ x := le_trans hTtwo hx
    have hxpos : 0 < x := by linarith
    have hfill := hfill_at x hx
    have hroot : Real.sqrt (c₁ * x) * Real.sqrt (c₁ * x) = c₁ * x := by
      have h := Real.sq_sqrt (by positivity : 0 ≤ c₁ * x)
      simpa [pow_two] using h
    have hprodUpper : c₁ * x ≤ c₂ * x :=
      mul_le_mul_of_nonneg_right hc₁₂ (by linarith)
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    refine ⟨hfill, hfill, ?_, ?_, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, hcut_at x hx⟩
    · rw [hroot]
    · rw [hroot]
      exact hprodUpper
    · intro m n k hm hn hmk hkn
      simp at hm
    · intro m hm
      simp at hm
    · have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      simpa using (Real.rpow_nonneg hlogpos.le C)
    · intro n hn
      simp at hn
    · intro n hn
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      simpa using (Real.rpow_nonneg hlogpos.le C)
    · constructor
      · intro h
        simpa [IsMarkedInvariant]
      · intro p hmem hp hprime
        simp [IsMarkedInvariant]

  have hselection : ∀ f : ℝ → RoughTypeIIData,
      (∀ x : ℝ, T ≤ x → Good x (f x)) →
      ∃ Csel xsel : ℝ, 0 < Csel ∧ T ≤ xsel ∧
        ∀ x : ℝ, xsel ≤ x → score x (f x) ≤ Csel := by
    intro f hf
    let famHm : ℝ → ℝ := fun x => if T ≤ x then (f x).Hm else Real.sqrt (c₁ * x)
    let famHn : ℝ → ℝ := fun x => if T ≤ x then (f x).Hn else Real.sqrt (c₁ * x)
    let famI : ℝ → Set ℕ := fun x => if T ≤ x then (f x).interval else ∅
    let famAlpha : ℝ → ℕ → ℂ := fun x m =>
      if T ≤ x then
        if m ∈ (f x).interval then roughCoefficient x γ (f x).v m else 0
      else 0
    let family : CoefficientFamily δ' C c₁ c₂ :=
      { xMin := T
        xMin_ge_two := hTtwo
        Hm := famHm
        Hn := famHn
        interval := famI
        alpha := famAlpha
        interval_property := by
          intro x m n k hm hn hmk hkn
          by_cases hx : T ≤ x
          · rcases hf x hx with
              ⟨_, _, _, _, _, hIprop, _, _, _, _, _, _⟩
            have hmI : m ∈ (f x).interval := by simpa [famI, hx] using hm
            have hnI : n ∈ (f x).interval := by simpa [famI, hx] using hn
            simpa [famI, hx] using hIprop hmI hnI hmk hkn
          · simp [famI, hx] at hm
        scales := by
          intro x hx
          rcases hf x hx with
            ⟨hHmδ, hHnδ, hprodLo, hprodHi, _, _, _, _, _, _, _, _⟩
          simpa [famHm, famHn, hx] using ⟨hHmδ, hHnδ, hprodLo, hprodHi⟩
        interval_bounds := by
          intro x hx m hm
          rcases hf x hx with
            ⟨_, _, _, _, _, _, hsubset, _, _, _, _, _⟩
          have hmI : m ∈ (f x).interval := by simpa [famI, hx] using hm
          simpa [famHm, famI, hx] using hsubset hmI
        rough_support := by
          intro x hx m hα
          rcases hf x hx with
            ⟨_, _, _, _, _, _, _, _, _, _, _, hcut⟩
          have hmI : m ∈ (f x).interval := by
            by_contra hmI
            have hzero : famAlpha x m = 0 := by simp [famAlpha, hx, hmI]
            exact hα (by simpa [famAlpha, hx, hmI] using hzero)
          have hαrough : roughCoefficient x γ (f x).v m ≠ 0 := by
            simpa [famAlpha, hx, hmI] using hα
          refine ⟨?_, hroughCoefficient_support x hcut (f x).v m hαrough⟩
          simpa [famI, hx] using hmI
        coefficient_bound := by
          intro x hx m hm
          rcases hf x hx with
            ⟨hHmδ, _, _, _, hlogCase, _, hsubset, _, _, _, _, _⟩
          have hmI : m ∈ (f x).interval := by simpa [famI, hx] using hm
          rcases hlogCase with hIempty | ⟨hlogHm, hlog2Hm⟩
          · have : False := by simpa [hIempty] using hmI
            exact this.elim
          · rcases hsubset hmI with ⟨hmlo, hmhi⟩
            have hxpos : 0 < x := by linarith [le_trans hTtwo hx]
            have hHmpos : 0 < (f x).Hm :=
              lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ') hHmδ
            have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le hHmpos hmlo
            have hlogxpos : 0 < Real.log x :=
              Real.log_pos (by linarith [le_trans hTtwo hx])
            have hHmToM : Real.log ((f x).Hm) ≤ Real.log (m : ℝ) :=
              Real.log_le_log hHmpos hmlo
            have hMTo2Hm : Real.log (m : ℝ) ≤ Real.log (2 * (f x).Hm) :=
              Real.log_le_log hmpos hmhi
            have hlowMul := (le_div_iff₀ hlogxpos).mp hlogHm.1
            have hhighMul := (div_le_iff₀ hlogxpos).mp hlog2Hm.2
            have hlogRatio :
                Real.log (m : ℝ) / Real.log x ∈ Set.Icc wMin wMax :=
              ⟨(le_div_iff₀ hlogxpos).2 (hlowMul.trans hHmToM),
                (div_le_iff₀ hlogxpos).2 (hMTo2Hm.trans hhighMul)⟩
            simpa [famAlpha, hx, hmI] using hcoef_at x hx (f x).v m hlogRatio
        }
    have hfamilyData : ∀ x : ℝ, family.xMin ≤ x →
        family.interval x = ∅ ∨
          ∃ v : ℝ, |v| ≤ Real.rpow (Real.log x) C ∧
            Real.log (family.Hm x) / Real.log x ∈ Set.Icc wMin wMax ∧
            Real.log (2 * family.Hm x) / Real.log x ∈ Set.Icc wMin wMax ∧
            ∀ m ∈ family.interval x,
              family.alpha x m = roughCoefficient x γ v m := by
      intro x hx
      have hxT : T ≤ x := by simpa [family] using hx
      rcases hf x hxT with
        ⟨_, _, _, _, hlogCase, _, _, hv, _, _, _, _⟩
      by_cases hIempty : (f x).interval = ∅
      · left
        change (if T ≤ x then (f x).interval else ∅) = ∅
        rw [if_pos hxT, hIempty]
      · rcases hlogCase with hLogEmpty | hlogs
        · exact (hIempty hLogEmpty).elim
        · right
          refine ⟨(f x).v, hv, ?_, ?_, ?_⟩
          · simpa [family, famHm, hxT] using hlogs.1
          · simpa [family, famHm, hxT] using hlogs.2
          · intro m hm
            have hmI : m ∈ (f x).interval := by
              simpa [family, famI, hxT] using hm
            simpa [family, famAlpha, famI, hxT, hmI]
    have hlong := rough_family_long_cancellation γ wMin wMax δ' C c₁ c₂
      hγ hγwMin hwMinMax hwMax hδ'pos hC hc₂ family hfamilyData
    obtain ⟨Ctransfer, xtransfer, hCtransfer, hxtransfer2, htransferBound⟩ :=
      htransfer K hK family hlong a ha
    let xout := max T xtransfer
    have hxoutT : T ≤ xout := le_max_left _ _
    have hxoutTransfer : xtransfer ≤ xout := le_max_right _ _
    refine ⟨Ctransfer, xout, hCtransfer, hxoutT, ?_⟩
    intro x hx
    have hxT : T ≤ x := hxoutT.trans hx
    have hxtr : xtransfer ≤ x := hxoutTransfer.trans hx
    rcases hf x hxT with
      ⟨hHmδ, hHnδ, hprodLo, hprodHi, hlogCase, hIprop, hsubset, hv,
        hβsupport, hβbound, hF, hcut⟩
    have hHmpos : 0 < (f x).Hm :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [le_trans hTtwo hxT]) δ') hHmδ
    have hHnpos : 0 < (f x).Hn :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith [le_trans hTtwo hxT]) δ') hHnδ
    have hdenpos : 0 < ((f x).Hm * (f x).Hn) *
        Real.rpow (Real.log x) (-Dstar) := by
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [le_trans hTtwo hxT])
      exact mul_pos (mul_pos hHmpos hHnpos) (Real.rpow_pos_of_pos hlogpos _)
    have hHmEq : family.Hm x = (f x).Hm := by simp [family, famHm, hxT]
    have hHnEq : family.Hn x = (f x).Hn := by simp [family, famHn, hxT]
    have hIEq : family.interval x = (f x).interval := by simp [family, famI, hxT]
    have hBilinearEq :
        markedBilinearSum x K a q_d (f x).F (family.Hm x) (family.Hn x)
          (family.interval x) (family.alpha x) (f x).beta =
        markedBilinearSum x K a q_d (f x).F (f x).Hm (f x).Hn
          (f x).interval (fun m => roughCoefficient x γ (f x).v m) (f x).beta := by
      rw [hHmEq, hHnEq, hIEq]
      unfold markedBilinearSum
      apply Finset.sum_congr rfl
      intro m hm
      have hmI : m ∈ (f x).interval := (Finset.mem_filter.mp hm).2
      apply Finset.sum_congr rfl
      intro n hn
      have hα : family.alpha x m = roughCoefficient x γ (f x).v m := by
        simp [family, famAlpha, hxT, hmI]
      rw [hα]
    have hβsupportFam : ∀ n, (f x).beta n ≠ 0 →
        n ∈ dyadicIntegers (family.Hn x) ∧ roughAbove n (roughCutoff x) := by
      intro n hn
      simpa [hHnEq] using hβsupport n hn
    have hβboundFam : ∀ n ∈ dyadicIntegers (family.Hn x),
        ‖(f x).beta n‖ ≤ Real.rpow (Real.log x) C := by
      intro n hn
      have hn' : n ∈ dyadicIntegers (f x).Hn := by simpa [hHnEq] using hn
      exact hβbound n hn'
    have hraw := htransferBound x hxtr (f x).beta hβsupportFam hβboundFam (f x).F hF
    rw [hBilinearEq, hHmEq, hHnEq] at hraw
    have hscore : score x (f x) ≤ Ctransfer := by
      dsimp [score]
      apply (div_le_iff₀ hdenpos).2
      calc
        ‖markedBilinearSum x K a q_d (f x).F (f x).Hm (f x).Hn
            (f x).interval (fun m => roughCoefficient x γ (f x).v m) (f x).beta‖ ≤
            Ctransfer * ((f x).Hm * (f x).Hn) * Real.rpow (Real.log x) (-Dstar) := hraw
      _ = Ctransfer * (((f x).Hm * (f x).Hn) *
            Real.rpow (Real.log x) (-Dstar)) := by ring
    exact hscore

  obtain ⟨Cuniform, xuniform, hCuniform, hTuniform, huniform⟩ :=
    ArtinPrimitiveRoots.Proofs.r_typeii_p.familyUniformization
      RoughTypeIIData Good score default T hdefault hselection
  have hxuniform₂ : 2 ≤ xuniform := hTtwo.trans hTuniform
  refine ⟨Cuniform, xuniform, hCuniform, hxuniform₂, ?_⟩
  intro x hx Hm Hn hHmδ hHnδ hprodLo hprodHi hlogHm hlog2Hm
    I hIprop hIbound v hv beta hβsupport hβbound F hF
  have hxT : T ≤ x := hTuniform.trans hx
  have hx₂ : 2 ≤ x := hTtwo.trans hxT
  have hHmδ' : Real.rpow x δ' ≤ Hm :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hδ'δ).trans hHmδ
  have hHnδ' : Real.rpow x δ' ≤ Hn :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hδ'δ).trans hHnδ
  let datum : RoughTypeIIData :=
    { Hm := Hm
      Hn := Hn
      interval := I
      v := v
      beta := beta
      F := F }
  have hGood : Good x datum := by
    refine ⟨hHmδ', hHnδ', hprodLo, hprodHi, Or.inr ⟨hlogHm, hlog2Hm⟩,
      hIprop, hIbound, hv, hβsupport, hβbound, hF, hcut_at x hxT⟩
  have hscore := huniform x hx datum hGood
  have hHmpos : 0 < Hm := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by linarith) δ') hHmδ'
  have hHnpos : 0 < Hn := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by linarith) δ') hHnδ'
  have hdenpos : 0 < (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [hx₂])
    exact mul_pos (mul_pos hHmpos hHnpos) (Real.rpow_pos_of_pos hlogpos _)
  have hratio :
      ‖markedBilinearSum x K a q_d F Hm Hn I
          (fun m => roughCoefficient x γ v m) beta‖ /
        ((Hm * Hn) * Real.rpow (Real.log x) (-Dstar)) ≤ Cuniform := by
    simpa [score, datum] using hscore
  have hnum := (div_le_iff₀ hdenpos).mp hratio
  calc
    ‖∑ m ∈ (dyadicIntegers Hm).filter (fun m => m ∈ I),
        ∑ n ∈ dyadicIntegers Hn,
          roughCoefficient x γ v m * beta n * F (m * n - 1) *
            (markedWeight x K a q_d (m * n - 1) : ℂ)‖
        = ‖markedBilinearSum x K a q_d F Hm Hn I
            (fun m => roughCoefficient x γ v m) beta‖ := by
          simp [markedBilinearSum]
    _ ≤ Cuniform * ((Hm * Hn) * Real.rpow (Real.log x) (-Dstar)) := hnum
    _ = Cuniform * (Hm * Hn) * Real.rpow (Real.log x) (-Dstar) := by ring


end ArtinPrimitiveRoots.TypeII.Rough
