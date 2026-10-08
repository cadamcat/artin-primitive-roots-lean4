import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.LineMass
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadReindexing

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

/-- A separated matrix of distinct prime labels has a squarefree full product. -/
theorem primeMatrixProduct_squarefree {x : ℝ} {K N : ℕ} {a : Fin K → ℝ}
    (p : Fin K → Fin N → ℕ)
    (hp : ∀ i j, (p i j).Prime ∧ p i j ∈ primeBand x (a i))
    (hrow : ∀ i, Function.Injective (p i))
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Squarefree (∏ i : Fin K, ∏ j : Fin N, p i j) := by
  let f : Fin K × Fin N → ℕ := fun ij => p ij.1 ij.2
  have hinj : Function.Injective f := by
    intro ij kl heq
    change p ij.1 ij.2 = p kl.1 kl.2 at heq
    have hgroup : ij.1 = kl.1 := by
      by_contra hne
      have hnot := Finset.disjoint_left.mp (hbands ij.1 kl.1 hne) (hp ij.1 ij.2).2
      exact hnot (by simpa only [heq] using (hp kl.1 kl.2).2)
    have hslot : ij.2 = kl.2 := hrow ij.1 (by simpa only [hgroup] using heq)
    exact Prod.ext hgroup hslot
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin K × Fin N))) (Function.onFun IsRelPrime f) := by
    intro ij hij kl hkl hne
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp ij.1 ij.2).1 (hp kl.1 kl.2).1).mpr (hinj.ne hne))
  have hsf := Finset.squarefree_prod_of_pairwise_isCoprime (s := Finset.univ) hpair
    (fun ij hij => (hp ij.1 ij.2).1.squarefree)
  simpa only [f, Fintype.prod_prod_type] using hsf

/-- The union of two edge lists retains the whole source list and the fresh target label. -/
def edgeUnionLabels {x : ℝ} {K : ℕ} (p q : PrimeLists x K) :
    Fin K → Fin (slotCount x + 1) → ℕ :=
  fun i => Fin.lastCases (q i (lastSlot x)) (p i)

theorem edgeUnionLabels_in_bands {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hq : ValidPrimeLists x K a q) :
    ∀ i j, (edgeUnionLabels p q i j).Prime ∧ edgeUnionLabels p q i j ∈ primeBand x (a i) := by
  intro i j
  refine Fin.lastCases ?_ ?_ j
  · simpa only [edgeUnionLabels, Fin.lastCases_last] using hq.1 i (lastSlot x)
  · intro j
    simpa only [edgeUnionLabels, Fin.lastCases_castSucc] using hp.1 i j

theorem edgeUnionLabels_row_injective {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p) (htrans : IsSlotTransition p q) :
    ∀ i, Function.Injective (edgeUnionLabels p q i) := by
  intro i j j' heq
  induction j using Fin.lastCases with
  | last =>
    induction j' using Fin.lastCases with
    | last => rfl
    | cast j' =>
      have h : q i (lastSlot x) = p i j' := by simpa only [edgeUnionLabels, Fin.lastCases_last,
        Fin.lastCases_castSucc] using heq
      exact ((htrans.2 i i j') h).elim
  | cast j =>
    induction j' using Fin.lastCases with
    | last =>
      have h : q i (lastSlot x) = p i j := by simpa only [edgeUnionLabels, Fin.lastCases_last,
        Fin.lastCases_castSucc] using heq.symm
      exact ((htrans.2 i i j) h).elim
    | cast j' =>
      have h : p i j = p i j' := by simpa only [edgeUnionLabels, Fin.lastCases_castSucc] using heq
      have hj : j = j' := by
        by_contra hne
        exact hp.2 i j j' hne h
      exact congrArg Fin.castSucc hj

/-- Each distinct prime of a physical edge union is charged only once in the residue model. -/
theorem edgeUnionProduct_squarefree {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hq : ValidPrimeLists x K a q)
    (htrans : IsSlotTransition p q)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Squarefree (∏ i : Fin K, ∏ j : Fin (slotCount x + 1), edgeUnionLabels p q i j) :=
  primeMatrixProduct_squarefree (edgeUnionLabels p q) (edgeUnionLabels_in_bands p q hp hq)
    (edgeUnionLabels_row_injective p q hp htrans) hbands

/-- An edge union's full modulus remains subexponential in the logarithmic scale. -/
theorem primeMatrixProduct_le_exp {x : ℝ} {K N : ℕ} {a : Fin K → ℝ}
    (ha : ValidBands K a) (hL : 1 ≤ Real.log x)
    (hN : (N : ℝ) ≤ 3 * Real.rpow (Real.log x) (1 / 100 : ℝ))
    (p : Fin K → Fin N → ℕ) (hp : ∀ i j, p i j ∈ primeBand x (a i)) :
    ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ) ≤
      Real.exp (6 * (K : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL
  have hpos (i : Fin K) (j : Fin N) : 0 < (p i j : ℝ) :=
    Nat.cast_pos.mpr (Finset.mem_filter.mp (hp i j)).2.1.pos
  have hprodPos : 0 < ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ) := by
    apply Nat.cast_pos.mpr
    apply Finset.prod_pos
    intro i hi
    exact Finset.prod_pos (fun j hj => (Finset.mem_filter.mp (hp i j)).2.1.pos)
  have hlog : Real.log ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ) =
      ∑ i : Fin K, ∑ j : Fin N, Real.log (p i j : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_prod, Real.log_prod]
      intro j hj
      exact (hpos i j).ne'
    · intro i hi
      rw [Nat.cast_prod]
      exact (Finset.prod_pos (fun j hj => hpos i j)).ne'
  have hlogp (i : Fin K) (j : Fin N) : Real.log (p i j : ℝ) ≤
      2 * Real.rpow (Real.log x) (1 / 5 : ℝ) := by
    have h := Real.log_le_log (hpos i j) (Finset.mem_filter.mp (hp i j)).2.2.2
    have haPow : Real.rpow (Real.log x) (a i) ≤ Real.rpow (Real.log x) (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (ha.2.1 i).2.le
    have hfirst : Real.log (p i j : ℝ) ≤ 2 * Real.rpow (Real.log x) (a i) := by
      simpa only [Real.log_exp] using h
    exact hfirst.trans (mul_le_mul_of_nonneg_left haPow (by norm_num))
  have hlogUpper : Real.log ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ) ≤
      (K : ℝ) * (N : ℝ) * (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) := by
    rw [hlog]
    calc
      _ ≤ ∑ i : Fin K, ∑ j : Fin N, 2 * Real.rpow (Real.log x) (1 / 5 : ℝ) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hlogp i j))
      _ = _ := by simp [mul_assoc]
  have hJoin : Real.rpow (Real.log x) (1 / 100 : ℝ) * Real.rpow (Real.log x) (1 / 5 : ℝ) =
      Real.rpow (Real.log x) (21 / 100 : ℝ) := by
    calc
      _ = Real.rpow (Real.log x) ((1 / 100 : ℝ) + (1 / 5 : ℝ)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by norm_num
  have htotal : Real.log ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ) ≤
      6 * (K : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) := by
    calc
      _ ≤ (K : ℝ) * (N : ℝ) * (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) := hlogUpper
      _ ≤ (K : ℝ) * (3 * Real.rpow (Real.log x) (1 / 100 : ℝ)) *
          (2 * Real.rpow (Real.log x) (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg K))
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
      _ = _ := by rw [← hJoin]; ring
  calc
    _ = Real.exp (Real.log ((∏ i : Fin K, ∏ j : Fin N, p i j : ℕ) : ℝ)) := (Real.exp_log hprodPos).symm
    _ ≤ _ := Real.exp_le_exp.mpr htotal


/-- The prime factors of a prime-label product are exactly its listed labels. -/
theorem primeMatrixProduct_primeFactors {K N : ℕ} (p : Fin K → Fin N → ℕ)
    (hp : ∀ i j, (p i j).Prime) :
    (∏ i : Fin K, ∏ j : Fin N, p i j).primeFactors =
      (Finset.univ : Finset (Fin K × Fin N)).image (fun ij => p ij.1 ij.2) := by
  have hprodPos : 0 < ∏ i : Fin K, ∏ j : Fin N, p i j :=
    Finset.prod_pos (fun i hi => Finset.prod_pos (fun j hj => (hp i j).pos))
  ext q
  constructor
  · intro hq
    have hprime := Nat.prime_of_mem_primeFactors hq
    have hdiv := Nat.dvd_of_mem_primeFactors hq
    obtain ⟨i, hi, hinner⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hdiv
    obtain ⟨j, hj, hlabel⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hinner
    have heq : q = p i j := (Nat.prime_dvd_prime_iff_eq hprime (hp i j)).mp hlabel
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, heq.symm⟩
  · intro hq
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hq
    have hin : p ij.1 ij.2 ∣ ∏ j : Fin N, p ij.1 j :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ ij.2)
    have hout : (∏ j : Fin N, p ij.1 j) ∣ ∏ i : Fin K, ∏ j : Fin N, p i j :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ ij.1)
    exact Nat.mem_primeFactors.mpr ⟨hp ij.1 ij.2, hin.trans hout, hprodPos.ne'⟩

/-- Independence rewrites the per-address band factors into their grouped normalizer powers. -/
theorem unionLineWeight_factorization {x : ℝ} {K N : ℕ} (a : Fin K → ℝ)
    (t : UnionLineChoice x a N) :
    unionLineWeight x a t =
      (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ N) *
        ∏ q : Fin K × Fin N, (((t q).val : ℝ) + 1)⁻¹ := by
  unfold unionLineWeight unionLineAtom
  rw [Finset.prod_mul_distrib]
  congr 1
  simp [Fintype.prod_prod_type]


/-- A union label matrix determines both endpoint lists whenever shared slots are copied. -/
theorem edgeUnionLabels_injective_on_transitions {x : ℝ} {K : ℕ}
    (p q p' q' : PrimeLists x K) (ht : IsSlotTransition p q) (ht' : IsSlotTransition p' q')
    (heq : edgeUnionLabels p q = edgeUnionLabels p' q') : p = p' ∧ q = q' := by
  have hp : p = p' := by
    funext i j
    have h := congrArg (fun f => f i (Fin.castSucc j)) heq
    simpa only [edgeUnionLabels, Fin.lastCases_castSucc] using h
  have hq : q = q' := by
    apply lists_ext_shared_last
    · intro i j
      calc
        q i (Fin.castSucc j) = p i (Fin.castSucc j) := ht.1 i _ j.isLt
        _ = p' i (Fin.castSucc j) := by rw [hp]
        _ = q' i (Fin.castSucc j) := (ht'.1 i _ j.isLt).symm
    · intro i
      have h := congrArg (fun f => f i (Fin.last (slotCount x))) heq
      simpa only [edgeUnionLabels, Fin.lastCases_last] using h
  exact ⟨hp, hq⟩


/-- Grouped line-normalizer powers and the union-prime probability are the independent-line weight. -/
theorem unionLinePrimeProbability_factorization {x : ℝ} {K N : ℕ} (a : Fin K → ℝ)
    (t : UnionLineChoice x a N) (hinj : Function.Injective (fun q : Fin K × Fin N => (t q).val)) :
    (∏ i : Fin K, (bandMass x (a i))⁻¹ ^ N) *
        (∏ q ∈ (∏ i : Fin K, ∏ j : Fin N, (t (i, j)).val).primeFactors, ((q : ℝ) + 1)⁻¹) =
      unionLineWeight x a t := by
  have hp (i : Fin K) (j : Fin N) : ((t (i, j)).val).Prime :=
    (Finset.mem_filter.mp (t (i, j)).property).2.1
  rw [primeMatrixProduct_primeFactors (fun i j => (t (i, j)).val) hp]
  have hprob :
      (∏ q ∈ (Finset.univ : Finset (Fin K × Fin N)).image (fun q => (t q).val), ((q : ℝ) + 1)⁻¹) =
        ∏ q : Fin K × Fin N, (((t q).val : ℝ) + 1)⁻¹ := by
    rw [Finset.prod_image]
    intro q hq q' hq' heq
    exact hinj heq
  rw [hprob, unionLineWeight_factorization]


/-- Separated edge-union addresses select distinct primes. -/
theorem edgeUnionLabels_address_injective {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p) (hq : ValidPrimeLists x K a q)
    (ht : IsSlotTransition p q)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Function.Injective (fun ij : Fin K × Fin (slotCount x + 1) => edgeUnionLabels p q ij.1 ij.2) := by
  intro ij kl heq
  have hgroup : ij.1 = kl.1 := by
    by_contra hne
    have hb := edgeUnionLabels_in_bands p q hp hq
    have hn := Finset.disjoint_left.mp (hbands ij.1 kl.1 hne) (hb ij.1 ij.2).2
    exact hn (by simpa only [heq] using (hb kl.1 kl.2).2)
  have hslot : ij.2 = kl.2 := (edgeUnionLabels_row_injective p q hp ht ij.1)
    (by simpa only [hgroup] using heq)
  exact Prod.ext hgroup hslot

end
end ArtinPrimitiveRoots.TypeII.PD
