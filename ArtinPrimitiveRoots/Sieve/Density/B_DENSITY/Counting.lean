import Mathlib
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Arithmetic
import ArtinPrimitiveRoots.Sieve.Density.B_DENSITY.Grid

/-! Finite prime-tuple counting and the rough-integer comparison. -/

namespace ArtinPrimitiveRoots.Proofs.b_density_sol

open MeasureTheory Filter
open scoped Topology

/-- Ordered tuples of small prime factors in a rectangular exponent box. -/
noncomputable def primeExponentBoxTuples {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    Finset (Fin k → ℕ) :=
  Fintype.piFinset fun i => primeExponentBand x (a i) (b i)

lemma primeExponentBoxTuples_disjoint_of_gap {k : ℕ} {x : ℝ}
    (hx : 1 ≤ x) {a b c d : Fin k → ℝ} (hgap : ∃ i, b i ≤ c i) :
    Disjoint (primeExponentBoxTuples x a b) (primeExponentBoxTuples x c d) := by
  classical
  obtain ⟨i, hgap⟩ := hgap
  apply Finset.disjoint_left.mpr
  intro q hq₁ hq₂
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hq₁prop := primeExponentBand_mem hxnonneg (Fintype.mem_piFinset.mp hq₁ i)
  have hq₂prop := primeExponentBand_mem hxnonneg (Fintype.mem_piFinset.mp hq₂ i)
  have hpow : Real.rpow x (b i) ≤ Real.rpow x (c i) :=
    Real.rpow_le_rpow_of_exponent_le hx hgap
  have hqle : (q i : ℝ) ≤ Real.rpow x (c i) := by
    calc
      (q i : ℝ) ≤ Real.rpow x (b i) := hq₁prop.2.2
      _ ≤ Real.rpow x (c i) := hpow
  have hlt : Real.rpow x (c i) < Real.rpow x (c i) :=
    lt_of_lt_of_le hq₂prop.2.1 hqle
  exact (lt_irrefl _ hlt).elim

lemma exponentGridBoxTuples_disjoint {k : ℕ} {x γ : ℝ} {n : ℕ}
    (hx : 1 ≤ x) (hn : 0 < n) {u v : Fin k → ℕ} (huv : u ≠ v) :
    Disjoint
      (primeExponentBoxTuples x (exponentGridLower γ n u) (exponentGridUpper γ n u))
      (primeExponentBoxTuples x (exponentGridLower γ n v) (exponentGridUpper γ n v)) := by
  obtain ⟨i, hgap | hgap⟩ := exponentGridBoxUpperSeparated hn huv
  · exact primeExponentBoxTuples_disjoint_of_gap hx ⟨i, hgap⟩
  · exact (primeExponentBoxTuples_disjoint_of_gap hx ⟨i, hgap⟩).symm

/-- Products of a prime tuple in an exponent box lie between the corresponding powers of `x`. -/
lemma primeExponentBoxTuple_prod_bounds {k : ℕ} (x : ℝ) (a b : Fin k → ℝ)
    (hx : 1 ≤ x) (q : Fin k → ℕ) (hq : q ∈ primeExponentBoxTuples x a b) :
    Real.rpow x (∑ i, a i) ≤ ∏ i : Fin k, (q i : ℝ) ∧
      (∏ i : Fin k, (q i : ℝ)) ≤ Real.rpow x (∑ i, b i) := by
  have hxpos : 0 < x := by linarith
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx
  have hband (i : Fin k) : q i ∈ primeExponentBand x (a i) (b i) :=
    Fintype.mem_piFinset.mp hq i
  have hlow (i : Fin k) : Real.rpow x (a i) < (q i : ℝ) :=
    (Finset.mem_filter.mp (hband i)).2
  have hupp (i : Fin k) : (q i : ℝ) ≤ Real.rpow x (b i) := by
    have hp : q i ∈ roughSievePrimes (Real.rpow x (b i)) :=
      (Finset.mem_filter.mp (hband i)).1
    have hpi : q i ≤ ⌊Real.rpow x (b i)⌋₊ := by
      have := (Finset.mem_filter.mp hp).1
      exact (Finset.mem_Icc.mp this).2
    exact (Nat.cast_le.mpr hpi).trans (Nat.floor_le (Real.rpow_nonneg hxnonneg _))
  have hloProd := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i hi => Real.rpow_nonneg hxnonneg _)
    (fun i hi => (le_of_lt (hlow i)))
  have huppProd := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i hi => Nat.cast_nonneg _)
    (fun i hi => hupp i)
  have hsumA : (∏ i : Fin k, Real.rpow x (a i)) = Real.rpow x (∑ i, a i) := by
    simpa using (Real.rpow_sum_of_pos hxpos a Finset.univ).symm
  have hsumB : (∏ i : Fin k, Real.rpow x (b i)) = Real.rpow x (∑ i, b i) := by
    simpa using (Real.rpow_sum_of_pos hxpos b Finset.univ).symm
  constructor
  · rw [← hsumA]
    exact hloProd
  · rw [← hsumB]
    exact huppProd

/-- Pairs consisting of a tuple in an exponent box and a final prime completing its product
to `(x,2x]`. -/
noncomputable def primeExponentBoxPairs {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    Finset (Σ q : Fin k → ℕ, ℕ) :=
  (primeExponentBoxTuples x a b).sigma fun q =>
    primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))

/-- The factor list attached to a box tuple and its final prime. -/
noncomputable def primeExponentBoxList {k : ℕ} (q : Fin k → ℕ) (r : ℕ) : List ℕ :=
  List.ofFn (Fin.snoc q r)

/-- Distinct pairs in an exponent box give distinct ordered factor lists. -/
lemma primeExponentBoxList_injective {k : ℕ} :
    Function.Injective (fun qr : Σ q : Fin k → ℕ, ℕ => primeExponentBoxList qr.1 qr.2) := by
  intro u v huv
  have hfun := List.ofFn_injective huv
  have hq : u.1 = v.1 := by
    have h := congrArg Fin.init hfun
    simpa [primeExponentBoxList] using h
  have hr : u.2 = v.2 := by
    have h := congrFun hfun (Fin.last k)
    simpa [primeExponentBoxList] using h
  exact Sigma.ext hq (heq_of_eq hr)

/-- Cardinality of the list set of an exponent box is the number of completing pairs. -/
lemma primeExponentBoxListSet_card {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    ((primeExponentBoxPairs x a b).image
      (fun qr => primeExponentBoxList qr.1 qr.2)).card =
      (primeExponentBoxPairs x a b).card := by
  exact Finset.card_image_of_injective _ primeExponentBoxList_injective

lemma primeExponentBoxListSet_weight {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    (∑ l ∈ (primeExponentBoxPairs x a b).image
        (fun qr => primeExponentBoxList qr.1 qr.2),
      1 / (l.length.factorial : ℝ)) =
      (primeExponentBoxPairs x a b).card / ((k + 1).factorial : ℝ) := by
  have hlen (qr : Σ q : Fin k → ℕ, ℕ) :
      (primeExponentBoxList qr.1 qr.2).length = k + 1 := by
    simp [primeExponentBoxList]
  calc
    (∑ l ∈ (primeExponentBoxPairs x a b).image
        (fun qr => primeExponentBoxList qr.1 qr.2),
      1 / (l.length.factorial : ℝ)) =
        ∑ l ∈ (primeExponentBoxPairs x a b).image
          (fun qr => primeExponentBoxList qr.1 qr.2),
          1 / ((k + 1).factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro l hl
            obtain ⟨qr, hqr, rfl⟩ := Finset.mem_image.mp hl
            rw [hlen]
    _ = (primeExponentBoxPairs x a b).card / ((k + 1).factorial : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
        primeExponentBoxListSet_card]

lemma exponentGridBoxListSets_disjoint {k : ℕ} {x γ : ℝ} {n : ℕ}
    (hx : 1 ≤ x) (hn : 0 < n) {u v : Fin k → ℕ} (huv : u ≠ v) :
    Disjoint
      ((primeExponentBoxPairs x (exponentGridLower γ n u)
          (exponentGridUpper γ n u)).image (fun qr => primeExponentBoxList qr.1 qr.2))
      ((primeExponentBoxPairs x (exponentGridLower γ n v)
          (exponentGridUpper γ n v)).image (fun qr => primeExponentBoxList qr.1 qr.2)) := by
  classical
  have htuples := exponentGridBoxTuples_disjoint (γ := γ) hx hn huv
  apply Finset.disjoint_left.mpr
  intro l hl₁ hl₂
  rcases Finset.mem_image.mp hl₁ with ⟨qr₁, hqr₁, rfl⟩
  rcases Finset.mem_image.mp hl₂ with ⟨qr₂, hqr₂, hlistEq⟩
  have hqrEq : qr₁ = qr₂ := primeExponentBoxList_injective hlistEq.symm
  subst qr₂
  have hpair₁ : qr₁ ∈ (primeExponentBoxTuples x
      (exponentGridLower γ n u) (exponentGridUpper γ n u)).sigma
      (fun q => primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))) := by
    simpa [primeExponentBoxPairs] using hqr₁
  have hpair₂ : qr₁ ∈ (primeExponentBoxTuples x
      (exponentGridLower γ n v) (exponentGridUpper γ n v)).sigma
      (fun q => primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))) := by
    simpa [primeExponentBoxPairs] using hqr₂
  have hq₁ := (Finset.mem_sigma.mp hpair₁).1
  have hq₂ := (Finset.mem_sigma.mp hpair₂).1
  exact (Finset.disjoint_left.mp htuples) hq₁ hq₂

lemma primeExponentBoxPairs_card {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    ((primeExponentBoxPairs x a b).card : ℝ) =
      ∑ q ∈ primeExponentBoxTuples x a b,
        ((primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))).card : ℝ) := by
  simpa [primeExponentBoxPairs] using
    (show ((primeExponentBoxTuples x a b).sigma
        (fun q => primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ)))).card =
          ∑ q ∈ primeExponentBoxTuples x a b,
            (primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))).card from
      Finset.card_sigma (primeExponentBoxTuples x a b)
        (fun q => primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))))

/-- Reciprocal weights of all tuples in a rectangular exponent box factor into the band masses. -/
lemma primeExponentBoxTuple_reciprocal_sum {k : ℕ} (x : ℝ) (a b : Fin k → ℝ) :
    (∑ q ∈ primeExponentBoxTuples x a b,
      1 / ∏ i : Fin k, (q i : ℝ)) =
      ∏ i : Fin k, primeReciprocalBand x (a i) (b i) := by
  classical
  let bands : Fin k → Finset ℕ := fun i => primeExponentBand x (a i) (b i)
  let weights : Fin k → ℕ → ℝ := fun _ p => 1 / (p : ℝ)
  have hInv (q : Fin k → ℕ) :
      1 / ∏ i : Fin k, (q i : ℝ) = ∏ i : Fin k, (1 / (q i : ℝ)) := by
    simp [one_div, Finset.prod_inv_distrib]
  rw [show primeExponentBoxTuples x a b = Fintype.piFinset bands by rfl]
  simp_rw [hInv]
  calc
    (∑ q ∈ Fintype.piFinset bands, ∏ i : Fin k, (1 / (q i : ℝ))) =
        ∏ i : Fin k, ∑ p ∈ bands i, weights i p := by
          symm
          exact Finset.prod_univ_sum bands weights
    _ = ∏ i : Fin k, primeReciprocalBand x (a i) (b i) := by
          simp [weights, bands, primeExponentBand, primeReciprocalBand,
            roughSievePrimes]

/-- Lower bound for the weighted number of completing prime tuples in one exponent box. -/
lemma eventually_primeExponentBox_weightedCount_lower (hPNT : DyadicPrimeInput) {k : ℕ} {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε < 1)
    (a b : Fin k → ℝ) (ha : ∀ i, γ ≤ a i) (hab : ∀ i, a i < b i)
    (hsa : (∑ i : Fin k, a i) < 1) (hsb : (∑ i : Fin k, b i) < 1 - γ) :
    ∀ᶠ x : ℝ in atTop,
      ((1 - ε) / (1 - ∑ i : Fin k, a i) *
        ∏ i : Fin k, primeReciprocalBand x (a i) (b i)) /
          ((k + 1).factorial : ℝ) ≤
        ((Real.log x / x) * (primeExponentBoxPairs x a b).card) /
          ((k + 1).factorial : ℝ) := by
  let sa : ℝ := ∑ i : Fin k, a i
  let sb : ℝ := ∑ i : Fin k, b i
  let c : ℝ := 1 - sa
  let η : ℝ := 1 - sb
  have hc : 0 < c := by dsimp [c, sa]; linarith
  have hη : 0 < η := by dsimp [η, sb]; linarith
  have hUniform : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, Real.rpow x η ≤ y →
      (1 - ε) * y / Real.log y ≤ primeDyadicCount y :=
    eventually_uniform_primeDyadicCount_lower hPNT hη hε
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hUniform
  have hFact : 0 < ((k + 1).factorial : ℝ) := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop x₀,
      (tendsto_rpow_atTop hη).eventually_ge_atTop x₀] with x hx2 hxLarge hxPow
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsumPow : Real.rpow x sb * Real.rpow x η = x := by
    have hsum : sb + η = 1 := by dsimp [sb, η]; ring
    calc
      Real.rpow x sb * Real.rpow x η = Real.rpow x (sb + η) :=
        (Real.rpow_add hxpos sb η).symm
      _ = Real.rpow x 1 := by rw [hsum]
      _ = x := by simp
  have hper : ∀ q ∈ primeExponentBoxTuples x a b,
      (1 - ε) / c * (1 / (∏ i : Fin k, (q i : ℝ))) ≤
        (Real.log x / x) *
          ((primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))).card : ℝ) := by
    intro q hq
    let Q : ℝ := ∏ i : Fin k, (q i : ℝ)
    let y : ℝ := x / Q
    have hQpos : 0 < Q := by
      dsimp [Q]
      apply Finset.prod_pos
      intro i hi
      have hband := Fintype.mem_piFinset.mp hq i
      have hpP := (Finset.mem_filter.mp hband).1
      have hpPrime := (Finset.mem_filter.mp hpP).2
      exact_mod_cast hpPrime.pos
    have hbox := primeExponentBoxTuple_prod_bounds x a b hxone q hq
    have hyprod : Real.rpow x η * Q ≤ x := by
      calc
        Real.rpow x η * Q ≤ Real.rpow x η * Real.rpow x sb :=
          mul_le_mul_of_nonneg_left hbox.2 (Real.rpow_nonneg (le_of_lt hxpos) _)
        _ = x := by rw [mul_comm, hsumPow]
    have hyLower : Real.rpow x η ≤ y := by
      exact (le_div_iff₀ hQpos).2 hyprod
    have hypos : 0 < y := div_pos hxpos hQpos
    have hygt : 1 < y := by
      have hxgt : 1 < x := by linarith
      exact (Real.one_lt_rpow hxgt hη).trans_le hyLower
    have hlogy : 0 < Real.log y := Real.log_pos hygt
    have hlogQ : sa * Real.log x ≤ Real.log Q := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos sa) hbox.1
      rw [Real.log_rpow hxpos] at h
      exact h
    have hyEq : Real.log y = Real.log x - Real.log Q := by
      dsimp [y]
      rw [Real.log_div hxpos.ne' hQpos.ne']
    have hlogyUpper : Real.log y ≤ c * Real.log x := by
      dsimp [c, sa]
      rw [hyEq]
      linarith
    have hRatio : 1 / c ≤ Real.log x / Real.log y := by
      rw [div_le_div_iff₀ hc hlogy]
      nlinarith [hlogyUpper]
    have hPNT := hx₀ x hxLarge y hyLower
    have hCount :
        (1 - ε) * y / Real.log y ≤ (primeDyadicPrimes y).card := by
      rw [primeDyadicPrimes_card y hypos.le]
      exact hPNT
    have hscale := mul_le_mul_of_nonneg_left hCount
      (le_of_lt (div_pos hlogx hxpos))
    have hcoefNonneg : 0 ≤ (1 - ε) / Q :=
      div_nonneg (by linarith) hQpos.le
    have hratioMul := mul_le_mul_of_nonneg_left hRatio hcoefNonneg
    have hleft : (1 - ε) / c * (1 / Q) = (1 - ε) / Q * (1 / c) := by
      field_simp [ne_of_gt hc, ne_of_gt hQpos]
      <;> ring
    have hright : (1 - ε) / Q * (Real.log x / Real.log y) =
        (Real.log x / x) * ((1 - ε) * y / Real.log y) := by
      dsimp [y]
      field_simp [ne_of_gt hxpos, ne_of_gt hQpos, ne_of_gt hlogy]
      <;> ring
    calc
      (1 - ε) / c * (1 / (∏ i : Fin k, (q i : ℝ))) =
          (1 - ε) / c * (1 / Q) := by rfl
      _ = (1 - ε) / Q * (1 / c) := hleft
      _ ≤ (1 - ε) / Q * (Real.log x / Real.log y) := hratioMul
      _ = (Real.log x / x) * ((1 - ε) * y / Real.log y) := hright
      _ ≤ (Real.log x / x) * (primeDyadicPrimes y).card := hscale
  have hsum :
      (1 - ε) / c *
          (∑ q ∈ primeExponentBoxTuples x a b,
            1 / (∏ i : Fin k, (q i : ℝ))) ≤
        (Real.log x / x) * (primeExponentBoxPairs x a b).card := by
    calc
      _ = ∑ q ∈ primeExponentBoxTuples x a b,
            (1 - ε) / c * (1 / (∏ i : Fin k, (q i : ℝ))) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ q ∈ primeExponentBoxTuples x a b,
            (Real.log x / x) *
              ((primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))).card : ℝ) := by
              apply Finset.sum_le_sum
              intro q hq
              exact hper q hq
      _ = (Real.log x / x) * (primeExponentBoxPairs x a b).card := by
              rw [← Finset.mul_sum, ← primeExponentBoxPairs_card]
  have hmass := primeExponentBoxTuple_reciprocal_sum x a b
  have hdiv := mul_le_mul_of_nonneg_right hsum (inv_nonneg.mpr hFact.le)
  rw [hmass] at hdiv
  simpa [c, sa, div_eq_mul_inv, mul_assoc] using hdiv

/-- The count of integers in `(x,2x]` avoiding all prime divisors up to `z`. -/
noncomputable def roughIntegerCount (x z : ℝ) : ℝ :=
  ∑ n ∈ roughIntegerInterval x with
    ∀ p ∈ roughSievePrimes z, ¬ p ∣ n, (1 : ℝ)

/-- The finite set of rough integers counted by `roughIntegerCount`. -/
noncomputable def roughIntegerSet (x z : ℝ) : Finset ℕ :=
  (roughIntegerInterval x).filter fun n =>
    ∀ p ∈ roughSievePrimes z, ¬ p ∣ n

lemma roughIntegerCount_eq_card (x z : ℝ) :
    roughIntegerCount x z = (roughIntegerSet x z).card := by
  simp [roughIntegerCount, roughIntegerSet]

/-- All orderings of the prime factors of the rough integers in `(x,2x]`. -/
noncomputable def roughPrimeFactorListSet (x z : ℝ) : Finset (List ℕ) :=
  (roughIntegerSet x z).biUnion fun n => n.primeFactorsList.permutations.toFinset

/-- Giving each ordered factor list weight `1/j!` assigns total weight at most one to each
rough integer, even when prime factors repeat. -/
lemma roughPrimeFactorList_weight_le (x z : ℝ) :
    (∑ l ∈ roughPrimeFactorListSet x z,
      1 / (l.length.factorial : ℝ)) ≤ roughIntegerCount x z := by
  classical
  let A := roughIntegerSet x z
  let F := fun n : ℕ => n.primeFactorsList.permutations.toFinset
  have hn0 : ∀ n ∈ A, n ≠ 0 := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    have hnLower := (Finset.mem_Icc.mp hnI).1
    by_contra hzero
    simp [hzero] at hnLower
  have hdisj : (A : Set ℕ).PairwiseDisjoint F := by
    intro n hn m hm hnm
    refine Finset.disjoint_left.mpr ?_
    intro l hln hlm
    have hln' : l ∈ n.primeFactorsList.permutations := List.mem_toFinset.mp hln
    have hlm' : l ∈ m.primeFactorsList.permutations := List.mem_toFinset.mp hlm
    have hpn := List.mem_permutations.mp hln'
    have hpm := List.mem_permutations.mp hlm'
    have hprodN : l.prod = n := by
      calc
        l.prod = n.primeFactorsList.prod := hpn.prod_eq
        _ = n := Nat.prod_primeFactorsList (hn0 n hn)
    have hprodM : l.prod = m := by
      calc
        l.prod = m.primeFactorsList.prod := hpm.prod_eq
        _ = m := Nat.prod_primeFactorsList (hn0 m hm)
    exact hnm (hprodN.symm.trans hprodM)
  have hsum := Finset.sum_biUnion hdisj (f := fun l : List ℕ =>
    1 / (l.length.factorial : ℝ))
  have hinner (n : ℕ) (hn : n ∈ A) :
      (∑ l ∈ F n, 1 / (l.length.factorial : ℝ)) ≤ 1 := by
    let L := n.primeFactorsList
    have hlen : ∀ l ∈ F n, l.length = L.length := by
      intro l hl
      have hl' : l ∈ L.permutations := List.mem_toFinset.mp hl
      exact (List.mem_permutations.mp hl').length_eq
    have hcard : (F n).card ≤ L.length.factorial := by
      change L.permutations.toFinset.card ≤ L.length.factorial
      calc
        L.permutations.toFinset.card ≤ L.permutations.length :=
          List.toFinset_card_le L.permutations
        _ = L.length.factorial := List.length_permutations L
    have hcard' : ((F n).card : ℝ) ≤ (L.length.factorial : ℝ) := by
      exact_mod_cast hcard
    have hfac : 0 < (L.length.factorial : ℝ) := by positivity
    calc
      (∑ l ∈ F n, 1 / (l.length.factorial : ℝ)) =
          ∑ l ∈ F n, 1 / (L.length.factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hlen l hl]
      _ = (F n).card / (L.length.factorial : ℝ) := by
        simp [one_div, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hfac).2 hcard'
  calc
    (∑ l ∈ roughPrimeFactorListSet x z, 1 / (l.length.factorial : ℝ)) =
        ∑ n ∈ A, ∑ l ∈ F n, 1 / (l.length.factorial : ℝ) := by
          simpa [roughPrimeFactorListSet, A, F] using hsum
    _ ≤ ∑ n ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hinner n hn
    _ = (A.card : ℝ) := by simp
    _ = roughIntegerCount x z := by
      calc
        (A.card : ℝ) = (roughIntegerSet x z).card := by simp [A]
        _ = roughIntegerCount x z := (roughIntegerCount_eq_card x z).symm

lemma prime_dvd_list_prod_exists {p : ℕ} (hp : p.Prime) :
    ∀ l : List ℕ, p ∣ l.prod → ∃ q ∈ l, p ∣ q := by
  intro l
  induction l with
  | nil => simp [hp.ne_one]
  | cons q l ih =>
      rw [List.prod_cons]
      intro h
      rcases hp.dvd_mul.mp h with hq | hl
      · exact ⟨q, by simp, hq⟩
      · obtain ⟨r, hr, hpr⟩ := ih hl
        exact ⟨r, by simp [hr], hpr⟩

lemma primeExponentBoxList_mem_roughPrimeFactorListSet {k : ℕ} {x γ : ℝ}
    (hx : 1 < x) (hγ : 0 < γ) (a b : Fin k → ℝ)
    (ha : ∀ i, γ ≤ a i) (hab : ∀ i, a i < b i)
    (hsb : (∑ i : Fin k, b i) < 1 - γ)
    (qr : Σ q : Fin k → ℕ, ℕ)
    (hqr : qr ∈ primeExponentBoxPairs x a b) :
    primeExponentBoxList qr.1 qr.2 ∈ roughPrimeFactorListSet x (Real.rpow x γ) := by
  classical
  let q := qr.1
  let r := qr.2
  let Q : ℝ := ∏ i : Fin k, (q i : ℝ)
  let y : ℝ := x / Q
  let l : List ℕ := primeExponentBoxList q r
  let n : ℕ := l.prod
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := le_of_lt hx
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hxone
  have hpair : qr ∈ (primeExponentBoxTuples x a b).sigma
      (fun q => primeDyadicPrimes (x / ∏ i : Fin k, (q i : ℝ))) := by
    simpa [primeExponentBoxPairs] using hqr
  rcases Finset.mem_sigma.mp hpair with ⟨hq, hr⟩
  have hqband (i : Fin k) : q i ∈ primeExponentBand x (a i) (b i) :=
    Fintype.mem_piFinset.mp hq i
  have hqprops (i : Fin k) := primeExponentBand_mem hxnonneg (hqband i)
  have hqpos (i : Fin k) : 0 < (q i : ℝ) := by
    exact_mod_cast (hqprops i).1.pos
  have hQpos : 0 < Q := by
    dsimp [Q]
    apply Finset.prod_pos
    intro i hi
    exact hqpos i
  have hprodBounds := primeExponentBoxTuple_prod_bounds x a b hxone q hq
  have hsb' : γ + ∑ i : Fin k, b i < 1 := by linarith
  have hpowStrict : Real.rpow x (γ + ∑ i : Fin k, b i) < x := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hx hsb'
    simpa using h
  have hpowMul : Real.rpow x γ * Real.rpow x (∑ i : Fin k, b i) =
      Real.rpow x (γ + ∑ i : Fin k, b i) :=
    (Real.rpow_add hxpos γ _).symm
  have hmulQ : Real.rpow x γ * Q < x := by
    calc
      Real.rpow x γ * Q ≤ Real.rpow x γ * Real.rpow x (∑ i : Fin k, b i) :=
        mul_le_mul_of_nonneg_left hprodBounds.2 (Real.rpow_nonneg hxpos.le _)
      _ = Real.rpow x (γ + ∑ i : Fin k, b i) := hpowMul
      _ < x := hpowStrict
  have hypos : 0 < y := div_pos hxpos hQpos
  have hyLower : Real.rpow x γ < y := by
    dsimp [y]
    exact (lt_div_iff₀ hQpos).2 hmulQ
  have hfinal : r.Prime ∧ y < (r : ℝ) ∧ (r : ℝ) ≤ 2 * y :=
    primeDyadicPrimes_mem hypos.le hr
  have hqLarge (i : Fin k) : Real.rpow x γ < (q i : ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_le hxone (ha i)).trans_lt (hqprops i).2.1
  have hlarge : ∀ u ∈ l, Real.rpow x γ < (u : ℝ) := by
    change ∀ u ∈ List.ofFn (Fin.snoc q r), Real.rpow x γ < (u : ℝ)
    rw [List.forall_mem_ofFn_iff]
    intro i
    cases i using Fin.lastCases with
    | last =>
        simpa using hyLower.trans hfinal.2.1
    | cast i =>
        simpa using hqLarge i
  have hprimes : ∀ u ∈ l, u.Prime := by
    change ∀ u ∈ List.ofFn (Fin.snoc q r), u.Prime
    rw [List.forall_mem_ofFn_iff]
    intro i
    cases i using Fin.lastCases with
    | last => simpa using hfinal.1
    | cast i => simpa using (hqprops i).1
  have hlistProd : (l.prod : ℝ) = Q * (r : ℝ) := by
    change ((List.ofFn (Fin.snoc q r)).prod : ℝ) =
      (∏ i : Fin k, (q i : ℝ)) * (r : ℝ)
    have hprod : (List.ofFn (Fin.snoc q r)).prod =
        (∏ i : Fin k, q i) * r := by
      rw [List.prod_ofFn, Fin.prod_snoc]
    exact_mod_cast hprod
  have hlowN : x < (n : ℝ) := by
    have hrQ : x < (r : ℝ) * Q := by
      exact (div_lt_iff₀ hQpos).1 (by simpa [y] using hfinal.2.1)
    rw [show (n : ℝ) = (l.prod : ℝ) by rfl, hlistProd]
    nlinarith [hrQ]
  have huppN : (n : ℝ) ≤ 2 * x := by
    have hrQ : (r : ℝ) * Q ≤ 2 * x := by
      calc
        (r : ℝ) * Q ≤ (2 * (x / Q)) * Q :=
          mul_le_mul_of_nonneg_right (by simpa [y] using hfinal.2.2) hQpos.le
        _ = 2 * x := by field_simp [ne_of_gt hQpos] <;> ring
    rw [show (n : ℝ) = (l.prod : ℝ) by rfl, hlistProd]
    nlinarith [hrQ]
  have hinterval : n ∈ roughIntegerInterval x := by
    simp only [roughIntegerInterval, Finset.mem_Icc]
    constructor
    · have hfloor : ⌊x⌋₊ < n := (Nat.floor_lt (le_of_lt hxpos)).2 hlowN
      omega
    · exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * x)).2 huppN
  have havoid : ∀ p ∈ roughSievePrimes (Real.rpow x γ), ¬ p ∣ n := by
    intro p hp hpn
    have hps := (Finset.mem_filter.mp hp)
    have hpPrime : p.Prime := hps.2
    have hpLE : (p : ℝ) ≤ Real.rpow x γ := by
      have h := (Finset.mem_Icc.mp hps.1).2
      exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.rpow_nonneg hxpos.le γ))
    obtain ⟨u, hu, hpu⟩ := prime_dvd_list_prod_exists hpPrime (l := l) (by
      simpa [n] using hpn)
    have huPrime := hprimes u hu
    have hpeq : p = u := (Nat.prime_dvd_prime_iff_eq hpPrime huPrime).mp hpu
    subst u
    exact (not_lt_of_ge hpLE) (hlarge p hu)
  have hnset : n ∈ roughIntegerSet x (Real.rpow x γ) := by
    exact Finset.mem_filter.mpr ⟨hinterval, havoid⟩
  have hperm : List.Perm l n.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · exact rfl
    · exact hprimes
  change l ∈ (roughIntegerSet x (Real.rpow x γ)).biUnion
    (fun n => n.primeFactorsList.permutations.toFinset)
  apply Finset.mem_biUnion.mpr
  refine ⟨n, hnset, ?_⟩
  change l ∈ n.primeFactorsList.permutations.toFinset
  rw [List.mem_toFinset, List.mem_permutations]
  exact hperm

lemma primeExponentBoxPairs_weight_le_roughIntegerCount {k : ℕ} {x γ : ℝ}
    (hx : 1 < x) (hγ : 0 < γ) (a b : Fin k → ℝ)
    (ha : ∀ i, γ ≤ a i) (hab : ∀ i, a i < b i)
    (hsb : (∑ i : Fin k, b i) < 1 - γ) :
    ((primeExponentBoxPairs x a b).card : ℝ) / ((k + 1).factorial : ℝ) ≤
      roughIntegerCount x (Real.rpow x γ) := by
  classical
  let S := (primeExponentBoxPairs x a b).image
    (fun qr => primeExponentBoxList qr.1 qr.2)
  have hsubset : S ⊆ roughPrimeFactorListSet x (Real.rpow x γ) := by
    intro l hl
    obtain ⟨qr, hqr, rfl⟩ := Finset.mem_image.mp hl
    exact primeExponentBoxList_mem_roughPrimeFactorListSet hx hγ a b ha hab hsb qr hqr
  calc
    ((primeExponentBoxPairs x a b).card : ℝ) / ((k + 1).factorial : ℝ) =
        ∑ l ∈ S, 1 / (l.length.factorial : ℝ) := by
          simpa [S] using (primeExponentBoxListSet_weight x a b).symm
    _ ≤ ∑ l ∈ roughPrimeFactorListSet x (Real.rpow x γ),
        1 / (l.length.factorial : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro l hl hnot
            positivity)
    _ ≤ roughIntegerCount x (Real.rpow x γ) := roughPrimeFactorList_weight_le _ _

lemma exponentGridBoxes_weight_le_roughPrimeFactorListLength {k : ℕ} {x γ : ℝ} {n : ℕ}
    (hx : 1 < x) (hγ : 0 < γ) (hn : 0 < n) :
    (∑ u ∈ exponentGridBoxes k γ n,
      ((primeExponentBoxPairs x (exponentGridLower γ n u)
        (exponentGridUpper γ n u)).card : ℝ) / ((k + 1).factorial : ℝ)) ≤
      ∑ l ∈ roughPrimeFactorListSet x (Real.rpow x γ) with l.length = k + 1,
        1 / (l.length.factorial : ℝ) := by
  classical
  let boxes := exponentGridBoxes k γ n
  let L : (Fin k → ℕ) → Finset (List ℕ) := fun u =>
    (primeExponentBoxPairs x (exponentGridLower γ n u)
      (exponentGridUpper γ n u)).image (fun qr => primeExponentBoxList qr.1 qr.2)
  have hxone : 1 ≤ x := le_of_lt hx
  have hpairwise : (boxes : Set (Fin k → ℕ)).PairwiseDisjoint L := by
    intro u hu v hv huv
    exact exponentGridBoxListSets_disjoint hxone hn huv
  have hlistLength (qr : Σ q : Fin k → ℕ, ℕ) :
      (primeExponentBoxList qr.1 qr.2).length = k + 1 := by
    simp [primeExponentBoxList]
  have hsubset : boxes.biUnion L ⊆
      (roughPrimeFactorListSet x (Real.rpow x γ)).filter (fun l => l.length = k + 1) := by
    intro l hl
    obtain ⟨u, hu, hlist⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨qr, hqr, rfl⟩ := Finset.mem_image.mp hlist
    have hvalid := exponentGridBox_valid hγ hn hu
    have hrough := primeExponentBoxList_mem_roughPrimeFactorListSet
      (hx := hx) (hγ := hγ)
      (a := exponentGridLower γ n u) (b := exponentGridUpper γ n u)
      (ha := hvalid.1) (hab := hvalid.2.1) (hsb := hvalid.2.2.2) qr hqr
    refine Finset.mem_filter.mpr ⟨hrough, ?_⟩
    exact hlistLength qr
  calc
    (∑ u ∈ boxes,
      ((primeExponentBoxPairs x (exponentGridLower γ n u)
        (exponentGridUpper γ n u)).card : ℝ) / ((k + 1).factorial : ℝ)) =
        ∑ u ∈ boxes, ∑ l ∈ L u, 1 / (l.length.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          simpa [L] using (primeExponentBoxListSet_weight x
            (exponentGridLower γ n u) (exponentGridUpper γ n u)).symm
    _ = ∑ l ∈ boxes.biUnion L, 1 / (l.length.factorial : ℝ) := by
          simpa [L] using (Finset.sum_biUnion hpairwise
            (f := fun l : List ℕ => 1 / (l.length.factorial : ℝ))).symm
    _ ≤ ∑ l ∈ roughPrimeFactorListSet x (Real.rpow x γ) with l.length = k + 1,
        1 / (l.length.factorial : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
            intro l hl hnot
            positivity)

lemma roughPrimeFactorList_lengthFilter_weight_le (x z : ℝ) (K : Finset ℕ) :
    (∑ k ∈ K, ∑ l ∈ (roughPrimeFactorListSet x z).filter
        (fun l => l.length = k + 1), 1 / (l.length.factorial : ℝ)) ≤
      ∑ l ∈ roughPrimeFactorListSet x z, 1 / (l.length.factorial : ℝ) := by
  classical
  let A := roughPrimeFactorListSet x z
  let F : ℕ → Finset (List ℕ) := fun k => A.filter (fun l => l.length = k + 1)
  have hdisj : (K : Set ℕ).PairwiseDisjoint F := by
    intro k hk j hj hkj
    apply Finset.disjoint_left.mpr
    intro l hlk hlj
    have hlenK := (Finset.mem_filter.mp hlk).2
    have hlenJ := (Finset.mem_filter.mp hlj).2
    have hkeq : k = j := Nat.add_right_cancel (hlenK.symm.trans hlenJ)
    exact hkj hkeq
  have hsubset : K.biUnion F ⊆ A := by
    intro l hl
    obtain ⟨k, hk, hlk⟩ := Finset.mem_biUnion.mp hl
    exact (Finset.mem_filter.mp hlk).1
  calc
    (∑ k ∈ K, ∑ l ∈ F k, 1 / (l.length.factorial : ℝ)) =
        ∑ l ∈ K.biUnion F, 1 / (l.length.factorial : ℝ) := by
          simpa [F] using (Finset.sum_biUnion hdisj
            (f := fun l : List ℕ => 1 / (l.length.factorial : ℝ))).symm
    _ ≤ ∑ l ∈ A, 1 / (l.length.factorial : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro l hl hnot
          positivity
    _ = ∑ l ∈ roughPrimeFactorListSet x z, 1 / (l.length.factorial : ℝ) := by
          simp [A]

lemma eventually_forall_finset_real {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → ℝ → Prop) (hP : ∀ i ∈ s, ∀ᶠ x : ℝ in atTop, P i x) :
    ∀ᶠ x : ℝ in atTop, ∀ i ∈ s, P i x := by
  classical
  have aux : ∀ t : Finset ι,
      (∀ i ∈ t, ∀ᶠ x : ℝ in atTop, P i x) →
        ∀ᶠ x : ℝ in atTop, ∀ i ∈ t, P i x := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro ht
        filter_upwards [] with x
        intro i hi
        simp at hi
    | @insert a t hat ih =>
        intro ht
        have ha := ht a (Finset.mem_insert_self a t)
        have ht' : ∀ i ∈ t, ∀ᶠ x : ℝ in atTop, P i x := by
          intro i hi
          exact ht i (Finset.mem_insert_of_mem hi)
        have htail := ih ht'
        filter_upwards [ha, htail] with x hax htx
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hax
        · exact htx i hi
  exact aux s hP

lemma exponentGridFamily_weight_le_roughCount {x γ : ℝ} {n : ℕ}
    (hx : 1 < x) (hγ : 0 < γ) (hn : 0 < n) (K : Finset ℕ) :
    (∑ k ∈ K, ∑ u ∈ exponentGridBoxes k γ n,
      ((primeExponentBoxPairs x (exponentGridLower γ n u)
        (exponentGridUpper γ n u)).card : ℝ) / ((k + 1).factorial : ℝ)) ≤
      roughIntegerCount x (Real.rpow x γ) := by
  classical
  calc
    (∑ k ∈ K, ∑ u ∈ exponentGridBoxes k γ n,
      ((primeExponentBoxPairs x (exponentGridLower γ n u)
        (exponentGridUpper γ n u)).card : ℝ) / ((k + 1).factorial : ℝ)) ≤
      ∑ k ∈ K, ∑ l ∈ (roughPrimeFactorListSet x (Real.rpow x γ)).filter
        (fun l => l.length = k + 1), 1 / (l.length.factorial : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact exponentGridBoxes_weight_le_roughPrimeFactorListLength hx hγ hn
    _ ≤ ∑ l ∈ roughPrimeFactorListSet x (Real.rpow x γ),
        1 / (l.length.factorial : ℝ) := roughPrimeFactorList_lengthFilter_weight_le _ _ K
    _ ≤ roughIntegerCount x (Real.rpow x γ) := roughPrimeFactorList_weight_le _ _

lemma eventually_exponentGridFamily_roughCount_lower (hPNT : DyadicPrimeInput) {γ ε : ℝ} {n : ℕ}
    (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε < 1) (hn : 0 < n) (K : Finset ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ K.sigma (fun k => exponentGridBoxes k γ n),
        ((1 - ε) / (1 - ∑ i : Fin d.1,
            exponentGridLower γ n d.2 i) *
          ∏ i : Fin d.1,
            primeReciprocalBand x (exponentGridLower γ n d.2 i)
              (exponentGridUpper γ n d.2 i)) /
          ((d.1 + 1).factorial : ℝ)) ≤
        (Real.log x / x) * roughIntegerCount x (Real.rpow x γ) := by
  classical
  let S := K.sigma (fun k => exponentGridBoxes k γ n)
  let lowerTerm : (Σ k : ℕ, Fin k → ℕ) → ℝ → ℝ := fun d x =>
    ((1 - ε) / (1 - ∑ i : Fin d.1, exponentGridLower γ n d.2 i) *
      ∏ i : Fin d.1,
        primeReciprocalBand x (exponentGridLower γ n d.2 i)
          (exponentGridUpper γ n d.2 i)) /
        ((d.1 + 1).factorial : ℝ)
  let pairTerm : (Σ k : ℕ, Fin k → ℕ) → ℝ → ℝ := fun d x =>
    ((primeExponentBoxPairs x (exponentGridLower γ n d.2)
      (exponentGridUpper γ n d.2)).card : ℝ) / ((d.1 + 1).factorial : ℝ)
  have hEach (d : Σ k : ℕ, Fin k → ℕ) (hd : d ∈ S) :
      ∀ᶠ x : ℝ in atTop, lowerTerm d x ≤
        (Real.log x / x) * pairTerm d x := by
    have hmem : d.1 ∈ K ∧ d.2 ∈ exponentGridBoxes d.1 γ n :=
      Finset.mem_sigma.mp hd
    have hvalid := exponentGridBox_valid hγ hn hmem.2
    simpa [lowerTerm, pairTerm, mul_div_assoc] using
      (eventually_primeExponentBox_weightedCount_lower hPNT hγ hε hε1
        (exponentGridLower γ n d.2) (exponentGridUpper γ n d.2)
        hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2)
  have hAll := eventually_forall_finset_real S (fun d x =>
    lowerTerm d x ≤ (Real.log x / x) * pairTerm d x) hEach
  filter_upwards [hAll, eventually_ge_atTop (2 : ℝ)] with x hAll hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hscale : 0 ≤ Real.log x / x := div_nonneg hlog hxpos.le
  have hPNTsum :
      (∑ d ∈ S, lowerTerm d x) ≤
        (Real.log x / x) * ∑ d ∈ S, pairTerm d x := by
    calc
      _ ≤ ∑ d ∈ S, (Real.log x / x) * pairTerm d x := by
        apply Finset.sum_le_sum
        intro d hd
        exact hAll d hd
      _ = (Real.log x / x) * ∑ d ∈ S, pairTerm d x := by rw [Finset.mul_sum]
  have hrough : ∑ d ∈ S, pairTerm d x ≤ roughIntegerCount x (Real.rpow x γ) := by
    simpa [S, pairTerm, Finset.sum_sigma] using
      (exponentGridFamily_weight_le_roughCount (x := x) (γ := γ) (n := n)
        (by linarith) hγ hn K)
  calc
    (∑ d ∈ S, lowerTerm d x) ≤
        (Real.log x / x) * ∑ d ∈ S, pairTerm d x := hPNTsum
    _ ≤ (Real.log x / x) * roughIntegerCount x (Real.rpow x γ) :=
      mul_le_mul_of_nonneg_left hrough hscale

lemma eventually_primeExponentBox_roughCount_lower (hPNT : DyadicPrimeInput) {k : ℕ} {γ ε : ℝ}
    (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε < 1)
    (a b : Fin k → ℝ) (ha : ∀ i, γ ≤ a i) (hab : ∀ i, a i < b i)
    (hsa : (∑ i : Fin k, a i) < 1) (hsb : (∑ i : Fin k, b i) < 1 - γ) :
    ∀ᶠ x : ℝ in atTop,
      ((1 - ε) / (1 - ∑ i : Fin k, a i) *
        ∏ i : Fin k, primeReciprocalBand x (a i) (b i)) /
          ((k + 1).factorial : ℝ) ≤
        (Real.log x / x) * roughIntegerCount x (Real.rpow x γ) := by
  have hbox := eventually_primeExponentBox_weightedCount_lower
    hPNT hγ hε hε1 a b ha hab hsa hsb
  filter_upwards [hbox, eventually_ge_atTop (2 : ℝ)] with x hbox hx
  have hwt := primeExponentBoxPairs_weight_le_roughIntegerCount
    (x := x) (γ := γ) (by linarith) hγ a b ha hab hsb
  have hxpos : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hscale : 0 ≤ Real.log x / x := div_nonneg hlog hxpos.le
  calc
    ((1 - ε) / (1 - ∑ i : Fin k, a i) *
        ∏ i : Fin k, primeReciprocalBand x (a i) (b i)) /
          ((k + 1).factorial : ℝ) ≤
        ((Real.log x / x) * (primeExponentBoxPairs x a b).card) /
          ((k + 1).factorial : ℝ) := hbox
    _ = (Real.log x / x) *
          (((primeExponentBoxPairs x a b).card : ℝ) /
            ((k + 1).factorial : ℝ)) := by ring
    _ ≤ (Real.log x / x) * roughIntegerCount x (Real.rpow x γ) :=
      mul_le_mul_of_nonneg_left hwt hscale

end ArtinPrimitiveRoots.Proofs.b_density_sol
