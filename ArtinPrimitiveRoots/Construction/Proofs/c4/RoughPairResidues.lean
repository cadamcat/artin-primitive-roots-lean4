import Mathlib
import OAI.NumberTheory.Jacobsthal.Sieve.RealCoprimeResidueCount
import ArtinPrimitiveRoots.TypeII.Defs
import ArtinPrimitiveRoots.Ext.TypeIIInputs
import ArtinPrimitiveRoots.Construction.Proofs.c4.Density

namespace ArtinPrimitiveRoots.Construction.Proofs.C4

open Classical

/-- A pair with product one modulo `n` is the same as a unit and its inverse. -/
noncomputable def productOneEquivUnits (n : ℕ) :
    {xy : ZMod n × ZMod n // xy.1 * xy.2 = 1} ≃ (ZMod n)ˣ := by
  refine
    { toFun := fun xy => ⟨xy.1.1, xy.1.2, xy.2, by simpa [mul_comm] using xy.2⟩
      invFun := fun u => ⟨(u, u.inv), u.val_inv⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro xy
    cases xy with
    | mk xy hxy => cases xy <;> rfl
  · intro u
    apply Units.ext
    rfl

theorem card_mul_eq_one_zmod {n : ℕ} [NeZero n] [Fintype (ZMod n)ˣ] :
    Fintype.card {xy : ZMod n × ZMod n // xy.1 * xy.2 = 1} = Nat.totient n := by
  rw [Fintype.card_congr (productOneEquivUnits n), ZMod.card_units_eq_totient n]

theorem card_mul_eq_one_zmod_prime {p : ℕ} [NeZero p] [Fact p.Prime]
    [Fintype (ZMod p)ˣ] (hp : p.Prime) :
    Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 1} = p - 1 := by
  classical
  calc
    _ = Nat.totient p := card_mul_eq_one_zmod
    _ = p - 1 := Nat.totient_prime hp

theorem card_nonzero_zmod_prime {p : ℕ} [NeZero p] :
    (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).card = p - 1 := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (ZMod p))) (fun a => a = 0)
  have hzeroSet : (Finset.univ.filter (fun a : ZMod p => a = 0)) = {0} := by
    ext a
    simp
  have hzero : (Finset.univ.filter (fun a : ZMod p => a = 0)).card = 1 := by
    rw [hzeroSet]
    simp
  have hnot : (Finset.univ.filter (fun a : ZMod p => ¬ a = 0)) =
      Finset.univ.filter (fun a : ZMod p => a ≠ 0) := by
    ext a
    simp
  rw [hnot, hzero] at hpart
  have hcard : (Finset.univ : Finset (ZMod p)).card = p := by simp
  omega

theorem card_mul_eq_zero_zmod_prime {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : p.Prime) :
    Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0} = 2 * p - 1 := by
  classical
  let R := ZMod p
  let zeroPairs : Finset (R × R) := Finset.univ.filter (fun xy => xy.1 * xy.2 = 0)
  let nonzeroPairs : Finset (R × R) :=
    Finset.univ.filter (fun xy => xy.1 * xy.2 ≠ 0)
  have hpart : zeroPairs.card + nonzeroPairs.card =
      (Finset.univ : Finset (R × R)).card := by
    dsimp [zeroPairs, nonzeroPairs]
    exact Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (R × R))) (fun xy => xy.1 * xy.2 = 0)
  have hnonzero : nonzeroPairs =
      (Finset.univ.filter (fun a : R => a ≠ 0)).product
        (Finset.univ.filter (fun b : R => b ≠ 0)) := by
    ext ⟨a, b⟩
    simp [nonzeroPairs, Finset.mem_product, mul_ne_zero_iff]
  have hzeroPairs :
      Fintype.card {xy : R × R // xy.1 * xy.2 = 0} = zeroPairs.card :=
    Fintype.card_of_subtype zeroPairs (by intro xy; simp [zeroPairs])
  have hprod :
      ((Finset.univ.filter (fun a : R => a ≠ 0)).product
        (Finset.univ.filter (fun a : R => a ≠ 0))).card = (p - 1) * (p - 1) := by
    change ((Finset.univ.filter (fun a : R => a ≠ 0)) ×ˢ
      (Finset.univ.filter (fun a : R => a ≠ 0))).card = _
    rw [Finset.card_product]
    change (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).card *
      (Finset.univ.filter (fun a : ZMod p => a ≠ 0)).card = _
    rw [card_nonzero_zmod_prime]
  have hpart' := hpart
  rw [hnonzero, hprod, ← hzeroPairs] at hpart'
  have hcard : (Finset.univ : Finset (R × R)).card = p ^ 2 := by simp [R, pow_two]
  have hp2 : 2 ≤ p := hp.two_le
  have hpred : p = (p - 1) + 1 := by omega
  have htwo : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
  have hnatAdd : p ^ 2 = (2 * p - 1) + (p - 1) ^ 2 := by
    calc
      p ^ 2 = ((p - 1) + 1) ^ 2 := congrArg (fun t : ℕ => t ^ 2) hpred
      _ = (2 * (p - 1) + 1) + (p - 1) ^ 2 := by nlinarith
      _ = (2 * p - 1) + (p - 1) ^ 2 := by rw [htwo.symm]
  have hsuble : (p - 1) ^ 2 ≤ p ^ 2 :=
    Nat.pow_le_pow_left (Nat.sub_le p 1) 2
  have hnat : p ^ 2 - (p - 1) ^ 2 = 2 * p - 1 :=
    (Nat.sub_eq_iff_eq_add hsuble).2 hnatAdd
  simp only [pow_two] at hpart' hcard hnatAdd
  nlinarith [hpart', hcard, hnatAdd]

theorem card_bad_product_residues_zmod_prime {p : ℕ} [NeZero p] [Fact p.Prime]
    [Fintype (ZMod p)ˣ] (hp : p.Prime) :
    Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0 ∨ xy.1 * xy.2 = 1} =
      (2 * p - 1) + (p - 1) := by
  classical
  let zeroPairs : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun xy => xy.1 * xy.2 = 0)
  let onePairs : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun xy => xy.1 * xy.2 = 1)
  let badPairs : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter (fun xy => xy.1 * xy.2 = 0 ∨ xy.1 * xy.2 = 1)
  have hUnion : zeroPairs ∪ onePairs = badPairs := by
    ext ⟨a, b⟩
    simp [zeroPairs, onePairs, badPairs, Finset.mem_union]
  have hDisjoint : Disjoint zeroPairs onePairs := by
    rw [Finset.disjoint_left]
    intro xy hzero hone
    have hz := (Finset.mem_filter.mp hzero).2
    have ho := (Finset.mem_filter.mp hone).2
    rw [hz] at ho
    norm_num at ho
  have hzero : Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0} =
      zeroPairs.card :=
    Fintype.card_of_subtype zeroPairs (by intro xy; simp [zeroPairs])
  have hone : Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 1} =
      onePairs.card :=
    Fintype.card_of_subtype onePairs (by intro xy; simp [onePairs])
  have hbad : Fintype.card
      {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0 ∨ xy.1 * xy.2 = 1} =
        badPairs.card :=
    Fintype.card_of_subtype badPairs (by intro xy; simp [badPairs])
  have hcardUnion : (zeroPairs ∪ onePairs).card = zeroPairs.card + onePairs.card :=
    Finset.card_union_of_disjoint hDisjoint
  calc
    _ = badPairs.card := hbad
    _ = (zeroPairs ∪ onePairs).card := by rw [hUnion]
    _ = zeroPairs.card + onePairs.card := hcardUnion
    _ = Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 0} +
        Fintype.card {xy : ZMod p × ZMod p // xy.1 * xy.2 = 1} := by rw [hzero, hone]
    _ = (2 * p - 1) + (p - 1) := by
      rw [card_mul_eq_zero_zmod_prime hp, card_mul_eq_one_zmod_prime hp]

/-- CRT applied coordinatewise to a pair of residues. -/
def pairChineseRemainder {m n : ℕ} (h : Nat.Coprime m n) :
    (ZMod (m * n) × ZMod (m * n)) ≃
      ((ZMod m × ZMod m) × (ZMod n × ZMod n)) := by
  let e := ZMod.chineseRemainder h
  refine
    { toFun := fun ab => (( (e ab.1).1, (e ab.2).1), ((e ab.1).2, (e ab.2).2))
      invFun := fun z => (e.symm (z.1.1, z.2.1), e.symm (z.1.2, z.2.2))
      left_inv := ?_
      right_inv := ?_ }
  · intro ab
    rcases ab with ⟨a, b⟩
    simp [e]
  · intro z
    rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp [e]

/-- Split a subtype with independent coordinate predicates into a product of subtypes. -/
def subtypeAndEquiv {α β : Type*} (P : α → Prop) (Q : β → Prop) :
    {z : α × β // P z.1 ∧ Q z.2} ≃ {a // P a} × {b // Q b} where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun z := ⟨(z.1.1, z.2.1), ⟨z.1.2, z.2.2⟩⟩
  left_inv := by intro z; apply Subtype.ext; rfl
  right_inv := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Transport a subtype predicate through an equivalence. -/
def subtypeEquiv {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    {a : α // P (e a)} ≃ {b : β // P b} where
  toFun a := ⟨e a.1, a.2⟩
  invFun b := ⟨e.symm b.1, by simpa using b.2⟩
  left_inv := by intro a; apply Subtype.ext; simp
  right_inv := by intro b; apply Subtype.ext; simp

def pairChineseRemainder_subtype {m n : ℕ} (h : Nat.Coprime m n)
    (P : ZMod m × ZMod m → Prop) (Q : ZMod n × ZMod n → Prop) :
    {z : ZMod (m * n) × ZMod (m * n) //
      P (pairChineseRemainder h z).1 ∧ Q (pairChineseRemainder h z).2} ≃
      {a : ZMod m × ZMod m // P a} × {b : ZMod n × ZMod n // Q b} := by
  exact (subtypeEquiv (pairChineseRemainder h) (fun z => P z.1 ∧ Q z.2)).trans
    (subtypeAndEquiv P Q)

theorem pairChineseRemainder_card {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : Nat.Coprime m n) (P : ZMod m × ZMod m → Prop)
    (Q : ZMod n × ZMod n → Prop) [DecidablePred P] [DecidablePred Q] :
    Fintype.card {z : ZMod (m * n) × ZMod (m * n) //
      P (pairChineseRemainder h z).1 ∧ Q (pairChineseRemainder h z).2} =
      Fintype.card {a : ZMod m × ZMod m // P a} *
        Fintype.card {b : ZMod n × ZMod n // Q b} := by
  classical
  rw [Fintype.card_congr (pairChineseRemainder_subtype h P Q), Fintype.card_prod]

noncomputable def pairProductEquiv {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) [NeZero (∏ i, m i)] :
    (ZMod (∏ i, m i) × ZMod (∏ i, m i)) ≃ Π i, (ZMod (m i) × ZMod (m i)) where
  toFun xy i := ((ZMod.prodEquivPi m hcop xy.1) i, (ZMod.prodEquivPi m hcop xy.2) i)
  invFun f :=
    ((ZMod.prodEquivPi m hcop).symm (fun i => (f i).1),
      (ZMod.prodEquivPi m hcop).symm (fun i => (f i).2))
  left_inv := by
    intro xy
    rcases xy with ⟨x, y⟩
    apply Prod.ext
    · exact (ZMod.prodEquivPi m hcop).symm_apply_apply x
    · exact (ZMod.prodEquivPi m hcop).symm_apply_apply y
  right_inv := by
    intro f
    funext i
    apply Prod.ext
    · exact congrFun ((ZMod.prodEquivPi m hcop).apply_symm_apply
        (fun j => (f j).1)) i
    · exact congrFun ((ZMod.prodEquivPi m hcop).apply_symm_apply
        (fun j => (f j).2)) i

noncomputable def pairProductSubtypeEquiv {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) [NeZero (∏ i, m i)]
    (P : ∀ i, ZMod (m i) × ZMod (m i) → Prop) :
    {z : ZMod (∏ i, m i) × ZMod (∏ i, m i) //
      ∀ i, P i ((pairProductEquiv m hcop z) i)} ≃
      ∀ i, {v : ZMod (m i) × ZMod (m i) // P i v} := by
  refine
    { toFun := fun z i => ⟨(pairProductEquiv m hcop z.1) i, z.2 i⟩
      invFun := fun f => by
        let e := ZMod.prodEquivPi m hcop
        let x := e.symm (fun i => (f i).1.1)
        let y := e.symm (fun i => (f i).1.2)
        refine ⟨(x, y), ?_⟩
        intro i
        have hx : e x i = (f i).1.1 := congrFun (e.apply_symm_apply _) i
        have hy : e y i = (f i).1.2 := congrFun (e.apply_symm_apply _) i
        change P i (e x i, e y i)
        rw [hx, hy]
        exact (f i).2
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    apply Subtype.ext
    exact (pairProductEquiv m hcop).symm_apply_apply z.1
  · intro f
    funext i
    apply Subtype.ext
    dsimp [pairProductEquiv]
    apply Prod.ext
    · exact congrFun ((ZMod.prodEquivPi m hcop).apply_symm_apply
        (fun j => (f j).1.1)) i
    · exact congrFun ((ZMod.prodEquivPi m hcop).apply_symm_apply
        (fun j => (f j).1.2)) i

theorem pairProductSubtype_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) [NeZero (∏ i, m i)]
    [∀ i, NeZero (m i)] (P : ∀ i, ZMod (m i) × ZMod (m i) → Prop)
    [∀ i, DecidablePred (P i)] :
    Fintype.card {z : ZMod (∏ i, m i) × ZMod (∏ i, m i) //
      ∀ i, P i ((pairProductEquiv m hcop z) i)} =
      ∏ i, Fintype.card {v : ZMod (m i) × ZMod (m i) // P i v} := by
  classical
  rw [Fintype.card_congr (pairProductSubtypeEquiv m hcop P), Fintype.card_pi]

theorem pairProductSubtype_natCard {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) [NeZero (∏ i, m i)]
    [∀ i, NeZero (m i)] (P : ∀ i, ZMod (m i) × ZMod (m i) → Prop) :
    Nat.card {z : ZMod (∏ i, m i) × ZMod (∏ i, m i) //
      ∀ i, P i ((pairProductEquiv m hcop z) i)} =
      ∏ i, Nat.card {v : ZMod (m i) × ZMod (m i) // P i v} := by
  classical
  rw [Nat.card_congr (pairProductSubtypeEquiv m hcop P), Nat.card_pi]

/-- Transport a subtype along a pointwise equivalence of predicates. -/
def subtypeIffEquiv {α : Type*} (P Q : α → Prop) (h : ∀ a, P a ↔ Q a) :
    {a // P a} ≃ {a // Q a} where
  toFun a := ⟨a.1, (h a.1).1 a.2⟩
  invFun a := ⟨a.1, (h a.1).2 a.2⟩
  left_inv := by intro a; apply Subtype.ext; rfl
  right_inv := by intro a; apply Subtype.ext; rfl

/-- The local forbidden residue pairs at a prime `p`: product one, and also product zero when
`p ≤ W`. -/
def localBadProductPredicate (W : ℝ) (p : ℕ) (xy : ZMod p × ZMod p) : Prop :=
  xy.1 * xy.2 = 1 ∨ ((p : ℝ) ≤ W ∧ xy.1 * xy.2 = 0)

theorem card_localBadProduct_zmod_prime {p : ℕ} [NeZero p] [Fact p.Prime]
    [Fintype (ZMod p)ˣ] (hp : p.Prime) (W : ℝ)
    [DecidablePred (localBadProductPredicate W p)] :
    Fintype.card {xy : ZMod p × ZMod p // localBadProductPredicate W p xy} =
      if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
  classical
  by_cases hpW : (p : ℝ) ≤ W
  · have hpred (xy : ZMod p × ZMod p) :
        localBadProductPredicate W p xy ↔ xy.1 * xy.2 = 0 ∨ xy.1 * xy.2 = 1 := by
      simp [localBadProductPredicate, hpW, or_comm]
    rw [if_pos hpW, Fintype.card_congr (subtypeIffEquiv _ _ hpred)]
    exact card_bad_product_residues_zmod_prime hp
  · have hpred (xy : ZMod p × ZMod p) :
        localBadProductPredicate W p xy ↔ xy.1 * xy.2 = 1 := by
      simp [localBadProductPredicate, hpW]
    rw [if_neg hpW, Fintype.card_congr (subtypeIffEquiv _ _ hpred)]
    exact card_mul_eq_one_zmod_prime hp

abbrev PairSieveIndex (D : Finset ℕ) := Option {p : ℕ // p ∈ D}

def pairSieveModulus (k : ℕ) (D : Finset ℕ) (i : PairSieveIndex D) : ℕ :=
  match i with
  | none => k
  | some p => p.val

theorem pairSieveModulus_prod (k : ℕ) (D : Finset ℕ) :
    (∏ i : PairSieveIndex D, pairSieveModulus k D i) =
      k * (∏ p ∈ D, p) := by
  classical
  rw [Fintype.prod_option]
  simp only [pairSieveModulus]
  exact congrArg (Nat.mul k) (Finset.prod_coe_sort D (fun p => p))

def pairSievePredicate (W : ℝ) (k : ℕ) (D : Finset ℕ) (i : PairSieveIndex D)
    (xy : ZMod (pairSieveModulus k D i) × ZMod (pairSieveModulus k D i)) : Prop :=
  match i with
  | none => xy.1 * xy.2 = 1
  | some p => localBadProductPredicate W p.val xy

theorem pairSieveModuli_coprime {k : ℕ} (D : Finset ℕ)
    (hprime : ∀ p ∈ D, p.Prime) (hcopBase : ∀ p ∈ D, Nat.Coprime k p) :
    Pairwise (fun i j : PairSieveIndex D =>
      Nat.Coprime (pairSieveModulus k D i) (pairSieveModulus k D j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some p => exact hcopBase p.val p.property
  | some p =>
    cases j with
    | none => exact (hcopBase p.val p.property).symm
    | some q =>
      have hpq : p.val ≠ q.val := by
        intro heq
        apply hij
        have hsub : p = q := Subtype.ext heq
        rw [hsub]
      exact (Nat.coprime_primes (hprime p.val p.property)
        (hprime q.val q.property)).2 hpq

set_option maxHeartbeats 1000000 in
theorem pairSieveResidue_natCard {k : ℕ} (D : Finset ℕ) (W : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ D, p.Prime)
    (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    [∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i)] :
    Nat.card
      {z : ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) ×
          ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) //
        ∀ i, pairSievePredicate W k D i ((pairProductEquiv
          (pairSieveModulus k D) (pairSieveModuli_coprime D hprime hcopBase)
          z) i)} =
      Nat.totient k * ∏ p ∈ D,
        if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
  classical
  let ι := PairSieveIndex D
  let m : ι → ℕ := pairSieveModulus k D
  let P : ∀ i : ι, ZMod (m i) × ZMod (m i) → Prop := pairSievePredicate W k D
  have hbase : Nat.card {xy : ZMod k × ZMod k // xy.1 * xy.2 = 1} = Nat.totient k := by
    letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
    letI : Fintype (ZMod k)ˣ := Fintype.ofFinite _
    calc
      _ = Nat.card (ZMod k)ˣ := Nat.card_congr (productOneEquivUnits k)
      _ = Fintype.card (ZMod k)ˣ := Nat.card_eq_fintype_card
      _ = Nat.totient k := ZMod.card_units_eq_totient k
  have hlocal (p : {p : ℕ // p ∈ D}) :
      Nat.card {xy : ZMod p.val × ZMod p.val // localBadProductPredicate W p.val xy} =
        if (p.val : ℝ) ≤ W then (2 * p.val - 1) + (p.val - 1) else p.val - 1 := by
    letI : NeZero p.val := ⟨Nat.ne_of_gt (hprime p.val p.property).pos⟩
    letI : Fact p.val.Prime := ⟨hprime p.val p.property⟩
    letI : Fintype (ZMod p.val)ˣ := Fintype.ofFinite _
    letI : DecidablePred (localBadProductPredicate W p.val) := fun _ => Classical.propDecidable _
    rw [Nat.card_eq_fintype_card]
    exact card_localBadProduct_zmod_prime (hprime p.val p.property) W
  have hlocalProd :
      (∏ p : {p : ℕ // p ∈ D},
        Nat.card {xy : ZMod p.val × ZMod p.val // localBadProductPredicate W p.val xy}) =
        ∏ p ∈ D, if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
    let localCard : ℕ → ℕ := fun p =>
      Nat.card {xy : ZMod p × ZMod p // localBadProductPredicate W p xy}
    calc
      _ = ∏ p ∈ D, localCard p := by
        simpa [localCard] using (Finset.prod_coe_sort D localCard)
      _ = ∏ p ∈ D, if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        simpa [localCard] using hlocal ⟨p, hp⟩
  have hcard := pairProductSubtype_natCard m
    (pairSieveModuli_coprime D hprime hcopBase) P
  have hbaseLocal : Nat.card {xy : ZMod (m none) × ZMod (m none) // P none xy} =
      Nat.totient k := by
    exact Nat.card_congr (subtypeIffEquiv (P none)
      (fun xy : ZMod k × ZMod k => xy.1 * xy.2 = 1) (fun _ => Iff.rfl)) |>.trans hbase
  have hoptionProd :
      (∏ i : ι, Nat.card {xy : ZMod (m i) × ZMod (m i) // P i xy}) =
        Nat.card {xy : ZMod (m none) × ZMod (m none) // P none xy} *
          ∏ p : {p : ℕ // p ∈ D},
            Nat.card {xy : ZMod (m (some p)) × ZMod (m (some p)) // P (some p) xy} := by
    dsimp only [ι]
    rw [Fintype.prod_option]
  have hfinalProd :
      (∏ i : ι, Nat.card {xy : ZMod (m i) × ZMod (m i) // P i xy}) =
        Nat.totient k * ∏ p ∈ D,
          if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
    have hlocalP :
        (∏ p : {p : ℕ // p ∈ D},
          Nat.card {xy : ZMod (m (some p)) × ZMod (m (some p)) // P (some p) xy}) =
          ∏ p ∈ D, if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
      simpa [m, P, pairSieveModulus, pairSievePredicate] using hlocalProd
    rw [hoptionProd, hbaseLocal, hlocalP]
  simpa [ι, m, P, pairSievePredicate] using hcard.trans hfinalProd

noncomputable def pairSieveResidues {k : ℕ} (D : Finset ℕ) (W : ℝ)
    (hprime : ∀ p ∈ D, p.Prime) (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)] :
    Finset (ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) ×
      ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i)) := by
  classical
  exact Finset.univ.filter (fun z => ∀ i,
    pairSievePredicate W k D i ((pairProductEquiv (pairSieveModulus k D)
      (pairSieveModuli_coprime D hprime hcopBase) z) i))

theorem pairSieveResidues_card {k : ℕ} (D : Finset ℕ) (W : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ D, p.Prime)
    (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    [∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i)] :
    (pairSieveResidues D W hprime hcopBase).card =
      Nat.totient k * ∏ p ∈ D,
        if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
  classical
  let pred := fun z : ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) ×
      ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) =>
    ∀ i, pairSievePredicate W k D i ((pairProductEquiv (pairSieveModulus k D)
      (pairSieveModuli_coprime D hprime hcopBase) z) i)
  have hFintype : Fintype (ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i) ×
      ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i)) := inferInstance
  letI : DecidablePred pred := fun z => Classical.propDecidable _
  have hcardSubtype : Fintype.card {z // pred z} =
      (pairSieveResidues D W hprime hcopBase).card := by
    exact Fintype.card_of_subtype (pairSieveResidues D W hprime hcopBase)
      (by intro z; simp [pairSieveResidues, pred])
  have hNat : Nat.card {z // pred z} = Fintype.card {z // pred z} :=
    Nat.card_eq_fintype_card
  calc
    (pairSieveResidues D W hprime hcopBase).card = Nat.card {z // pred z} := hcardSubtype.symm.trans hNat.symm
    _ = Nat.totient k * ∏ p ∈ D,
          if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 :=
      pairSieveResidue_natCard D W hk hprime hcopBase

theorem primeProduct_injective_on_powerset (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) P.powerset := by
  intro S hS T hT hST
  have hSsub : S ⊆ P := Finset.mem_powerset.mp hS
  have hTsub : T ⊆ P := Finset.mem_powerset.mp hT
  have hprimeS : ∀ p ∈ S, p.Prime := fun p hp => hP p (hSsub hp)
  have hprimeT : ∀ p ∈ T, p.Prime := fun p hp => hP p (hTsub hp)
  have hfacS : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hprimeS
  have hfacT : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hprimeT
  calc
    S = (∏ p ∈ S, p).primeFactors := hfacS.symm
    _ = (∏ p ∈ T, p).primeFactors := by simpa using congrArg Nat.primeFactors hST
    _ = T := hfacT

theorem mem_pairSieveResidues_iff {k : ℕ} (D : Finset ℕ) (W : ℝ)
    (hprime : ∀ p ∈ D, p.Prime) (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    (m n : ℕ) :
    ((m : ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i)),
      (n : ZMod (∏ i : PairSieveIndex D, pairSieveModulus k D i))) ∈
        pairSieveResidues D W hprime hcopBase ↔
      ((m : ZMod k) * (n : ZMod k) = 1) ∧
        ∀ p ∈ D, localBadProductPredicate W p ((m : ZMod p), (n : ZMod p)) := by
  classical
  let ι := PairSieveIndex D
  let mods : ι → ℕ := pairSieveModulus k D
  let hcop := pairSieveModuli_coprime D hprime hcopBase
  have hcoordOne (i : ι) (t : ℕ) :
      (ZMod.prodEquivPi mods hcop (t : ZMod (∏ j, mods j))) i =
        (t : ZMod (mods i)) := by
    rw [ZMod.prodEquivPi_apply]
    exact map_natCast _ t
  have hcoord (i : ι) :
      (pairProductEquiv mods hcop
        ((m : ZMod (∏ i, mods i)), (n : ZMod (∏ i, mods i)))) i =
      ((m : ZMod (mods i)), (n : ZMod (mods i))) := by
    change ((ZMod.prodEquivPi mods hcop (m : ZMod (∏ j, mods j)) i),
      (ZMod.prodEquivPi mods hcop (n : ZMod (∏ j, mods j)) i)) = _
    exact Prod.ext (hcoordOne i m) (hcoordOne i n)
  simp only [pairSieveResidues, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∀ i : ι, pairSievePredicate W k D i
      ((pairProductEquiv mods hcop
        ((m : ZMod (∏ i, mods i)), (n : ZMod (∏ i, mods i)))) i)) ↔ _
  rw [Option.forall]
  constructor
  · rintro ⟨hbase, hlocal⟩
    refine ⟨?_, ?_⟩
    · rw [hcoord none] at hbase
      exact hbase
    · intro p hp
      have h := hlocal ⟨p, hp⟩
      rw [hcoord (some ⟨p, hp⟩)] at h
      exact h
  · rintro ⟨hbase, hlocal⟩
    refine ⟨?_, ?_⟩
    · have h : pairSievePredicate W k D none
          ((pairProductEquiv mods hcop
            ((m : ZMod (∏ i, mods i)), (n : ZMod (∏ i, mods i)))) none) := by
        rw [hcoord none]
        exact hbase
      exact h
    · intro p
      rcases p with ⟨p, hp⟩
      have h := hlocal p hp
      have h' : pairSievePredicate W k D (some ⟨p, hp⟩)
          ((pairProductEquiv mods hcop
            ((m : ZMod (∏ i, mods i)), (n : ZMod (∏ i, mods i)))) (some ⟨p, hp⟩)) := by
        rw [hcoord (some ⟨p, hp⟩)]
        exact h
      exact h'

theorem card_one_base_and_localBad {k p : ℕ} [NeZero k] [NeZero p] [NeZero (k * p)]
    [Fact p.Prime] [Fintype (ZMod k)ˣ] [Fintype (ZMod p)ˣ]
    (hkp : Nat.Coprime k p) (hp : p.Prime) (W : ℝ) :
    Fintype.card {z : ZMod (k * p) × ZMod (k * p) //
      (pairChineseRemainder hkp z).1.1 * (pairChineseRemainder hkp z).1.2 = 1 ∧
        localBadProductPredicate W p (pairChineseRemainder hkp z).2} =
      Nat.totient k * (if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1) := by
  classical
  let P : ZMod k × ZMod k → Prop := fun xy => xy.1 * xy.2 = 1
  let Q : ZMod p × ZMod p → Prop := localBadProductPredicate W p
  have hCard := pairChineseRemainder_card hkp P Q
  have hBase : Fintype.card {a : ZMod k × ZMod k // P a} = Nat.totient k := by
    exact card_mul_eq_one_zmod (n := k)
  have hLocal : Fintype.card {b : ZMod p × ZMod p // Q b} =
      if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1 := by
    exact card_localBadProduct_zmod_prime hp W
  have hfactor : Fintype.card {a : ZMod k × ZMod k // P a} *
      Fintype.card {b : ZMod p × ZMod p // Q b} =
        Nat.totient k * (if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1) := by
    rw [hBase, hLocal]
  simpa [P, Q] using hCard.trans hfactor

theorem intIcc_zmodClass_count_error (a b : ℤ) (q : ℕ) [NeZero q]
    (r : ZMod q) :
    |(((Finset.Icc a b).filter (fun z : ℤ => (z : ZMod q) = r)).card : ℝ) -
        ((Finset.Icc a b).card : ℝ) / (q : ℝ)| ≤ 1 := by
  classical
  let A : Finset ℤ := {((r.val : ℤ))}
  have hval : ((r.val : ℤ) : ZMod q) = r := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val r
  have hmodiff (z : ℤ) :
      (z : ZMod q) = r ↔ z % (q : ℤ) = (r.val : ℤ) := by
    calc
      (z : ZMod q) = r ↔ (z : ZMod q) = ((r.val : ℤ) : ZMod q) := by rw [hval]
      _ ↔ z % (q : ℤ) = ((r.val : ℤ) % (q : ℤ)) :=
        ZMod.intCast_eq_intCast_iff' z (r.val : ℤ) q
      _ ↔ z % (q : ℤ) = (r.val : ℤ) := by
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.val_lt)]
  have hEq : (Finset.Icc a b).filter (fun z : ℤ => (z : ZMod q) = r) =
      OAI.Erdos970.Erdos66Dependency.ResidueLifts.liftsOn
        (Finset.Icc a b) (q : ℤ) A := by
    ext z
    simp only [Finset.mem_filter,
      OAI.Erdos970.Erdos66Dependency.ResidueLifts.liftsOn, A, Finset.mem_singleton]
    exact and_congr_right fun _ => hmodiff z
  have hA : A ⊆ Finset.Ico 0 (q : ℤ) := by
    intro z hz
    simp only [A, Finset.mem_singleton] at hz
    subst z
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast r.val_lt⟩
  have hQ : 0 < (q : ℤ) := Int.natCast_pos.mpr (NeZero.pos q)
  have h := OAI.Erdos970.Erdos66Dependency.ResidueLifts.count_error_Icc
    a b (q : ℤ) A hQ hA
  rw [← hEq] at h
  simpa [A] using h

theorem dyadicNat_residue_count_error {H : ℝ} (hH : 2 ≤ H) {q : ℕ} [NeZero q]
    (r : ZMod q) :
    |(((ArtinPrimitiveRoots.TypeII.dyadicIntegers H).filter
        (fun n : ℕ => (n : ZMod q) = r)).card : ℝ) - H / (q : ℝ)| ≤ 2 := by
  classical
  let a : ℤ := ⌈H⌉
  let b : ℤ := (⌊2 * H⌋₊ : ℕ)
  let nToZ : ℕ ↪ ℤ := Nat.castEmbedding
  let natClass : Finset ℕ := (ArtinPrimitiveRoots.TypeII.dyadicIntegers H).filter
    (fun n : ℕ => (n : ZMod q) = r)
  let intClass : Finset ℤ := (Finset.Icc a b).filter (fun z : ℤ => (z : ZMod q) = r)
  have hmap : natClass.map nToZ = intClass := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp hz
      rcases Finset.mem_filter.mp hn with ⟨hnDyad, hnResidue⟩
      have hnDyad' : n ∈ ArtinPrimitiveRoots.TypeII.dyadicIntegers H := hnDyad
      unfold ArtinPrimitiveRoots.TypeII.dyadicIntegers at hnDyad'
      rcases Finset.mem_filter.mp hnDyad' with ⟨hnRange, hnBounds⟩
      have hnLe : n ≤ ⌊2 * H⌋₊ := by
        simp only [Finset.mem_range] at hnRange
        omega
      have hLo : a ≤ (n : ℤ) := by
        dsimp [a]
        exact Int.ceil_le.2 hnBounds.1
      have hHi : (n : ℤ) ≤ b := by
        dsimp [b]
        exact_mod_cast hnLe
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hLo, hHi⟩, ?_⟩
      simpa [nToZ, Int.cast_natCast] using hnResidue
    · intro hz
      rcases Finset.mem_filter.mp hz with ⟨hzI, hzResidue⟩
      have hzNonneg : 0 ≤ z := by
        have haNonneg : 0 ≤ a := by
          dsimp [a]
          exact Int.ceil_nonneg_of_neg_one_lt (by linarith [hH])
        exact haNonneg.trans (Finset.mem_Icc.mp hzI).1
      let n : ℕ := z.toNat
      have hnCast : (n : ℤ) = z := by
        dsimp [n]
        exact Int.toNat_of_nonneg hzNonneg
      have hnLe : n ≤ ⌊2 * H⌋₊ := by
        have hzHi : (n : ℤ) ≤ b := by simpa [hnCast] using (Finset.mem_Icc.mp hzI).2
        dsimp [b] at hzHi
        exact_mod_cast hzHi
      have hnRange : n ∈ Finset.range (⌊2 * H⌋₊ + 1) := by
        simp only [Finset.mem_range]
        omega
      have hrealLo : H ≤ (n : ℝ) := by
        have hceil : H ≤ (a : ℝ) := by dsimp [a]; exact Int.le_ceil H
        have hzLo : (a : ℝ) ≤ (z : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hzI).1
        have hnEq : (z : ℝ) = (n : ℝ) := by exact_mod_cast hnCast.symm
        linarith
      have hrealHi : (n : ℝ) ≤ 2 * H := by
        have hfloor : (⌊2 * H⌋₊ : ℝ) ≤ 2 * H := Nat.floor_le (by positivity)
        have hzHi : (z : ℝ) ≤ (⌊2 * H⌋₊ : ℝ) := by
          have hzHi' : z ≤ b := (Finset.mem_Icc.mp hzI).2
          dsimp [b] at hzHi'
          exact_mod_cast hzHi'
        have hnEq : (z : ℝ) = (n : ℝ) := by exact_mod_cast hnCast.symm
        linarith
      have hnDyad : n ∈ ArtinPrimitiveRoots.TypeII.dyadicIntegers H := by
        unfold ArtinPrimitiveRoots.TypeII.dyadicIntegers
        exact Finset.mem_filter.mpr ⟨hnRange, ⟨hrealLo, hrealHi⟩⟩
      have hnResidue : (n : ZMod q) = r := by
        have hnResidue' : ((n : ℤ) : ZMod q) = r := by
          simpa [hnCast] using hzResidue
        simpa [Int.cast_natCast] using hnResidue'
      apply Finset.mem_map.mpr
      refine ⟨n, Finset.mem_filter.mpr ⟨hnDyad, hnResidue⟩, ?_⟩
      exact hnCast
  have hcount :
      |(natClass.card : ℝ) - ((Finset.Icc a b).card : ℝ) / (q : ℝ)| ≤ 1 := by
    have h := intIcc_zmodClass_count_error a b q r
    have h' : |(intClass.card : ℝ) - ((Finset.Icc a b).card : ℝ) / (q : ℝ)| ≤ 1 := by
      simpa [intClass] using h
    rw [← hmap, Finset.card_map] at h'
    exact h'
  have haLo : H ≤ (a : ℝ) := by dsimp [a]; exact Int.le_ceil H
  have haHi : (a : ℝ) < H + 1 := by dsimp [a]; exact Int.ceil_lt_add_one H
  have hbLo : 2 * H - 1 < (b : ℝ) := by
    have hstrict : 2 * H < ((⌊2 * H⌋₊ : ℕ) : ℤ) + 1 := by
      exact_mod_cast (Nat.lt_floor_add_one (2 * H))
    dsimp [b]
    nlinarith [hstrict]
  have hbHi : (b : ℝ) ≤ 2 * H := by
    dsimp [b]
    exact Nat.floor_le (by positivity)
  have hab : a ≤ b := by
    have hreal : (a : ℝ) < (b : ℝ) := by nlinarith [haHi, hbLo, hH]
    exact_mod_cast hreal.le
  have hinterval : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - a + 1 := by
    have hi : ((Finset.Icc a b).card : ℤ) = b + 1 - a :=
      Int.card_Icc_of_le a b (show a ≤ b + 1 by omega)
    have hiReal : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
      exact_mod_cast hi
    calc
      _ = (b : ℝ) + 1 - a := hiReal
      _ = (b : ℝ) - a + 1 := by ring
  have hlen : |((Finset.Icc a b).card : ℝ) - H| ≤ 1 := by
    rw [hinterval, abs_le]
    constructor <;> nlinarith [haLo, haHi, hbLo, hbHi]
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hqOne : 1 ≤ (q : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hlenDiv : |((Finset.Icc a b).card : ℝ) / (q : ℝ) - H / (q : ℝ)| ≤ 1 := by
    calc
      _ = |(((Finset.Icc a b).card : ℝ) - H) / (q : ℝ)| := by rw [← sub_div]
      _ = |((Finset.Icc a b).card : ℝ) - H| / (q : ℝ) := by rw [abs_div, abs_of_pos hqpos]
      _ ≤ 1 / (q : ℝ) := div_le_div_of_nonneg_right hlen hqpos.le
      _ ≤ 1 := (div_le_iff₀ hqpos).2 (by linarith [hqOne])
  have htriangle := abs_sub_le (natClass.card : ℝ)
    (((Finset.Icc a b).card : ℝ) / (q : ℝ)) (H / (q : ℝ))
  have hfinal : |(natClass.card : ℝ) - H / (q : ℝ)| ≤ 2 := by
    calc
      _ ≤ |(natClass.card : ℝ) - ((Finset.Icc a b).card : ℝ) / (q : ℝ)| +
          |((Finset.Icc a b).card : ℝ) / (q : ℝ) - H / (q : ℝ)| := htriangle
      _ ≤ 2 := by linarith [hcount, hlenDiv]
  simpa [natClass] using hfinal

noncomputable def dyadicResidueCount (H : ℝ) (q : ℕ) [NeZero q] (r : ZMod q) : ℕ :=
  (ArtinPrimitiveRoots.TypeII.dyadicIntegers H).filter
    (fun n : ℕ => (n : ZMod q) = r) |>.card

theorem dyadicPairResidueSum_error {H₁ H₂ : ℝ} (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂)
    {q : ℕ} [NeZero q] (A : Finset (ZMod q × ZMod q)) :
    |(∑ v ∈ A, (dyadicResidueCount H₁ q v.1 : ℝ) *
          (dyadicResidueCount H₂ q v.2 : ℝ)) -
        (A.card : ℝ) * ((H₁ / q) * (H₂ / q))| ≤
      (A.card : ℝ) * (2 * (H₁ + H₂) / q + 4) := by
  classical
  let X₁ : ℝ := H₁ / q
  let X₂ : ℝ := H₂ / q
  let c₁ : ZMod q → ℝ := fun r => (dyadicResidueCount H₁ q r : ℝ)
  let c₂ : ZMod q → ℝ := fun r => (dyadicResidueCount H₂ q r : ℝ)
  have hX₁ : 0 ≤ X₁ := by dsimp [X₁]; positivity
  have hX₂ : 0 ≤ X₂ := by dsimp [X₂]; positivity
  have hcount₁ (r : ZMod q) : |c₁ r - X₁| ≤ 2 := by
    simpa [c₁, X₁, dyadicResidueCount] using dyadicNat_residue_count_error hH₁ r
  have hcount₂ (r : ZMod q) : |c₂ r - X₂| ≤ 2 := by
    simpa [c₂, X₂, dyadicResidueCount] using dyadicNat_residue_count_error hH₂ r
  have hcount₁Nonneg (r : ZMod q) : 0 ≤ c₁ r := by
    dsimp [c₁]
    exact Nat.cast_nonneg _
  have hcount₂Nonneg (r : ZMod q) : 0 ≤ c₂ r := by
    dsimp [c₂]
    exact Nat.cast_nonneg _
  have hpoint (v : ZMod q × ZMod q) :
      |c₁ v.1 * c₂ v.2 - X₁ * X₂| ≤ 2 * (X₁ + X₂) + 4 := by
    have h₁ := abs_le.mp (hcount₁ v.1)
    have h₂ := abs_le.mp (hcount₂ v.2)
    have h₂upper : |c₂ v.2| ≤ X₂ + 2 := by
      rw [abs_of_nonneg (hcount₂Nonneg v.2)]
      linarith
    have hterm₁ : |c₁ v.1 - X₁| * |c₂ v.2| ≤ 2 * (X₂ + 2) := by
      exact mul_le_mul (hcount₁ v.1) h₂upper (abs_nonneg _) (by positivity)
    have hterm₂ : X₁ * |c₂ v.2 - X₂| ≤ X₁ * 2 :=
      mul_le_mul_of_nonneg_left (hcount₂ v.2) hX₁
    calc
      _ = |(c₁ v.1 - X₁) * c₂ v.2 + X₁ * (c₂ v.2 - X₂)| := by congr 1 <;> ring
      _ ≤ |c₁ v.1 - X₁| * |c₂ v.2| + X₁ * |c₂ v.2 - X₂| := by
        calc
          _ ≤ |(c₁ v.1 - X₁) * c₂ v.2| +
              |X₁ * (c₂ v.2 - X₂)| := abs_add_le _ _
          _ = |c₁ v.1 - X₁| * |c₂ v.2| +
              X₁ * |c₂ v.2 - X₂| := by rw [abs_mul, abs_mul, abs_of_nonneg hX₁]
      _ ≤ 2 * (X₂ + 2) + X₁ * 2 := add_le_add hterm₁ hterm₂
      _ = 2 * (X₁ + X₂) + 4 := by ring
  have hsumConst : (∑ v ∈ A, X₁ * X₂) = (A.card : ℝ) * (X₁ * X₂) := by simp
  have hsumDiff :
      (∑ v ∈ A, c₁ v.1 * c₂ v.2) - (A.card : ℝ) * (X₁ * X₂) =
        ∑ v ∈ A, (c₁ v.1 * c₂ v.2 - X₁ * X₂) := by
    rw [← hsumConst, Finset.sum_sub_distrib]
  rw [hsumDiff]
  calc
    _ ≤ ∑ v ∈ A, |c₁ v.1 * c₂ v.2 - X₁ * X₂| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ A, (2 * (X₁ + X₂) + 4) :=
      Finset.sum_le_sum fun v hv => hpoint v
    _ = (A.card : ℝ) * (2 * (X₁ + X₂) + 4) := by simp; ring
    _ = (A.card : ℝ) * (2 * (H₁ + H₂) / q + 4) := by
      dsimp [X₁, X₂]
      ring

theorem dyadicPairResidue_count_eq_sum (H₁ H₂ : ℝ) (q : ℕ) [NeZero q]
    (A : Finset (ZMod q × ZMod q)) :
    (( ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
        (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)).filter
          (fun mn => ((mn.1 : ZMod q), (mn.2 : ZMod q)) ∈ A)).card : ℝ) =
      ∑ v ∈ A,
        (dyadicResidueCount H₁ q v.1 : ℝ) * (dyadicResidueCount H₂ q v.2 : ℝ) := by
  classical
  let S := (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
    (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)
  let residue (mn : ℕ × ℕ) : ZMod q × ZMod q := ((mn.1 : ZMod q), (mn.2 : ZMod q))
  have hFiber (v : ZMod q × ZMod q) :
      (S.filter (fun mn => residue mn = v)).card =
        ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).filter
            (fun m : ℕ => (m : ZMod q) = v.1)).card *
          ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂).filter
            (fun n : ℕ => (n : ZMod q) = v.2)).card := by
    have hEq : S.filter (fun mn => residue mn = v) =
        ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).filter
            (fun m : ℕ => (m : ZMod q) = v.1)).product
          ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂).filter
            (fun n : ℕ => (n : ZMod q) = v.2)) := by
      ext ⟨m, n⟩
      simp [S, residue, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨hm, hn⟩, heq⟩
        cases heq
        exact ⟨⟨hm, rfl⟩, hn, rfl⟩
      · rintro ⟨⟨hm, hmr⟩, hn, hnr⟩
        refine ⟨⟨hm, hn⟩, ?_⟩
        exact Prod.ext hmr hnr
    rw [hEq]
    change (((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).filter
        (fun m : ℕ => (m : ZMod q) = v.1)) ×ˢ
      ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂).filter
        (fun n : ℕ => (n : ZMod q) = v.2))).card = _
    rw [Finset.card_product]
  have hsum := Finset.sum_card_fiberwise_eq_card_filter S A residue
  have hNat :
      ((S.filter (fun mn => residue mn ∈ A)).card) =
        ∑ v ∈ A,
          ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).filter
              (fun m : ℕ => (m : ZMod q) = v.1)).card *
            ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂).filter
              (fun n : ℕ => (n : ZMod q) = v.2)).card := by
    calc
      _ = ∑ v ∈ A, (S.filter (fun mn => residue mn = v)).card := hsum.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hFiber v
  have hReal := congrArg (fun n : ℕ => (n : ℝ)) hNat
  push_cast at hReal
  simpa [S, residue, dyadicResidueCount] using hReal

noncomputable def dyadicPairResidueClassCount (H₁ H₂ : ℝ) (q : ℕ)
    (A : Finset (ZMod q × ZMod q)) : ℕ :=
  (((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
      (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)).filter
        (fun mn : ℕ × ℕ => ((mn.1 : ZMod q), (mn.2 : ZMod q)) ∈ A)).card

theorem dyadicPairResidueClassCount_error {H₁ H₂ : ℝ} (hH₁ : 2 ≤ H₁)
    (hH₂ : 2 ≤ H₂) {q : ℕ} [NeZero q] (A : Finset (ZMod q × ZMod q)) :
    |(dyadicPairResidueClassCount H₁ H₂ q A : ℝ) -
        (A.card : ℝ) * ((H₁ / q) * (H₂ / q))| ≤
      (A.card : ℝ) * (2 * (H₁ + H₂) / q + 4) := by
  have hcount := dyadicPairResidue_count_eq_sum H₁ H₂ q A
  have hsum := dyadicPairResidueSum_error hH₁ hH₂ (A := A)
  rw [dyadicPairResidueClassCount, hcount]
  exact hsum

theorem dyadicPairResidueClassCount_error_card_sq {H₁ H₂ : ℝ} (hH₁ : 2 ≤ H₁)
    (hH₂ : 2 ≤ H₂) {q : ℕ} [NeZero q] (A : Finset (ZMod q × ZMod q))
    (hA : A.card ≤ q ^ 2) :
    |(dyadicPairResidueClassCount H₁ H₂ q A : ℝ) -
        (A.card : ℝ) * ((H₁ / q) * (H₂ / q))| ≤
      2 * (H₁ + H₂) * (q : ℝ) + 4 * (q : ℝ) ^ 2 := by
  have hbase := dyadicPairResidueClassCount_error hH₁ hH₂ A
  have hA' : (A.card : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast hA
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hcoef : 0 ≤ 2 * (H₁ + H₂) / (q : ℝ) + 4 := by positivity
  calc
    _ ≤ (A.card : ℝ) * (2 * (H₁ + H₂) / (q : ℝ) + 4) := hbase
    _ ≤ (q : ℝ) ^ 2 * (2 * (H₁ + H₂) / (q : ℝ) + 4) :=
      mul_le_mul_of_nonneg_right hA' hcoef
    _ = 2 * (H₁ + H₂) * (q : ℝ) + 4 * (q : ℝ) ^ 2 := by
      field_simp [ne_of_gt hqpos]
      <;> ring

theorem pairSieveResidues_card_le {k : ℕ} (D : Finset ℕ) (W : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ D, p.Prime)
    (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    [∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i)] :
    (pairSieveResidues D W hprime hcopBase).card ≤
      (∏ i : PairSieveIndex D, pairSieveModulus k D i) ^ 2 := by
  let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
  calc
    (pairSieveResidues D W hprime hcopBase).card ≤ Fintype.card (ZMod q × ZMod q) :=
      Finset.card_le_univ _
    _ = q ^ 2 := by simp [Fintype.card_prod, ZMod.card, q, pow_two]

theorem pairSieveModuli_positive {k : ℕ} (D : Finset ℕ) (hk : 0 < k)
    (hprime : ∀ p ∈ D, p.Prime) :
    (∀ i : PairSieveIndex D, 0 < pairSieveModulus k D i) ∧
      0 < ∏ i : PairSieveIndex D, pairSieveModulus k D i := by
  have hmod : ∀ i : PairSieveIndex D, 0 < pairSieveModulus k D i := by
    intro i
    cases i with
    | none => exact hk
    | some p => exact (hprime p.val p.property).pos
  refine ⟨hmod, ?_⟩
  exact Finset.prod_pos (fun i hi => hmod i)

/-- A crude but uniform bound for summing a linear-quadratic error over subset products.
Distinct subsets of a prime set have distinct products, so the sum embeds into the first
`⌊Y⌋+1` natural numbers. -/
theorem powerset_product_linear_quadratic_sum_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (Y A B : ℝ)
    (hY : 1 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Finset.sum (P.powerset.filter
      (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y))
      (fun D => A * ((∏ p ∈ D, p : ℕ) : ℝ) +
        B * ((∏ p ∈ D, p : ℕ) : ℝ) ^ 2) ≤
      2 * A * Y ^ 2 + 2 * B * Y ^ 3 := by
  classical
  let S := P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y)
  let N : ℕ := ⌊Y⌋₊
  let T : Finset ℕ := Finset.range (N + 1)
  let f : Finset ℕ → ℕ := fun D => ∏ p ∈ D, p
  let wS : Finset ℕ → ℝ := fun D => A * (f D : ℝ) + B * (f D : ℝ) ^ 2
  let wT : ℕ → ℝ := fun n => A * n + B * (n : ℝ) ^ 2
  have hY0 : 0 ≤ Y := le_trans (by norm_num) hY
  have hfloor : (N : ℝ) ≤ Y := by
    dsimp [N]
    exact Nat.floor_le hY0
  have hcount : ((N + 1 : ℕ) : ℝ) ≤ 2 * Y := by
    push_cast
    linarith
  have hcount' : (T.card : ℝ) ≤ 2 * Y := by
    simpa [T, N] using hcount
  have hmap : ∀ D ∈ S, f D ∈ T := by
    intro D hD
    have hD' := (Finset.mem_filter.mp hD).2
    have hprod : f D ≤ N := by
      apply (Nat.le_floor_iff hY0).2
      simpa [f, N] using hD'
    dsimp [T]
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn f S := by
    intro D hD E hE hDE
    exact primeProduct_injective_on_powerset P hprime
      (Finset.mem_filter.mp hD).1 (Finset.mem_filter.mp hE).1 hDE
  have hbound : ∀ D ∈ S, wS D ≤ wT (f D) := by
    intro D hD
    rfl
  have hnonneg : ∀ n ∈ T, 0 ≤ wT n := by
    intro n hn
    dsimp [wT]
    positivity
  have hsum := finite_sum_le_superset_of_injective S T f wS wT hinj hmap hbound hnonneg
  have hterm : ∀ n ∈ T, wT n ≤ A * Y + B * Y ^ 2 := by
    intro n hn
    have hnN : n ≤ N := by
      have hnRange : n ∈ Finset.range (N + 1) := by simpa only [T] using hn
      have hnlt := Finset.mem_range.mp hnRange
      omega
    have hnY : (n : ℝ) ≤ Y := (Nat.cast_le.mpr hnN).trans hfloor
    dsimp [wT]
    gcongr
  have hsumT : (∑ n ∈ T, wT n) ≤ (T.card : ℝ) * (A * Y + B * Y ^ 2) := by
    calc
      _ ≤ ∑ _n ∈ T, (A * Y + B * Y ^ 2) :=
        Finset.sum_le_sum fun n hn => hterm n hn
      _ = _ := by simp; ring
  have hconst : 0 ≤ A * Y + B * Y ^ 2 := by positivity
  have hfinal : Finset.sum S wS ≤ 2 * A * Y ^ 2 + 2 * B * Y ^ 3 := by
    calc
      _ ≤ ∑ n ∈ T, wT n := hsum
      _ ≤ (T.card : ℝ) * (A * Y + B * Y ^ 2) := hsumT
      _ ≤ (2 * Y) * (A * Y + B * Y ^ 2) :=
        mul_le_mul_of_nonneg_right hcount' hconst
      _ = 2 * A * Y ^ 2 + 2 * B * Y ^ 3 := by ring
  simpa [S, wS, f] using hfinal

/-- The per-subset CRT lattice discrepancy for the two-variable sieve. -/
noncomputable def pairSieveLatticeError {k : ℕ} (P D : Finset ℕ) (W H₁ H₂ : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime)
    (hcopBase : ∀ p ∈ P, Nat.Coprime k p) : ℝ := by
  classical
  by_cases hDP : D ⊆ P
  · let hprimeD : ∀ p ∈ D, p.Prime := fun p hp => hprime p (hDP hp)
    let hcopD : ∀ p ∈ D, Nat.Coprime k p := fun p hp => hcopBase p (hDP hp)
    let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
    have hqpos := (pairSieveModuli_positive D hk hprimeD).2
    letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    exact |(dyadicPairResidueClassCount H₁ H₂ q
        (pairSieveResidues D W hprimeD hcopD) : ℝ) -
      ((pairSieveResidues D W hprimeD hcopD).card : ℝ) *
        ((H₁ / (q : ℝ)) * (H₂ / (q : ℝ)))|
  · exact 0

theorem pairSieveLatticeError_le {k : ℕ} (P D : Finset ℕ) (hDP : D ⊆ P)
    (W H₁ H₂ : ℝ) (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂) (hk : 0 < k)
    (hprime : ∀ p ∈ P, p.Prime) (hcopBase : ∀ p ∈ P, Nat.Coprime k p) :
    pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase ≤
      2 * (H₁ + H₂) *
          ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) +
        4 * ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) ^ 2 := by
  classical
  have hprimeD : ∀ p ∈ D, p.Prime := fun p hp => hprime p (hDP hp)
  have hcopD : ∀ p ∈ D, Nat.Coprime k p := fun p hp => hcopBase p (hDP hp)
  let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
  have hpos := pairSieveModuli_positive D hk hprimeD
  letI : NeZero q := ⟨Nat.ne_of_gt hpos.2⟩
  letI : ∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i) :=
    fun i => ⟨Nat.ne_of_gt (hpos.1 i)⟩
  have hA := pairSieveResidues_card_le D W hk hprimeD hcopD
  have hAcast : (pairSieveResidues D W hprimeD hcopD).card ≤ q ^ 2 := by
    exact_mod_cast hA
  have hcount := dyadicPairResidueClassCount_error_card_sq hH₁ hH₂
    (pairSieveResidues D W hprimeD hcopD) hAcast
  simpa [pairSieveLatticeError, hDP, q, hprimeD, hcopD] using hcount

theorem pairSieveLatticeErrors_sum_le {k : ℕ} (P : Finset ℕ) (W H₁ H₂ Y : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ P, p.Prime)
    (hcopBase : ∀ p ∈ P, Nat.Coprime k p)
    (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂) (hY : 1 ≤ Y) :
    Finset.sum (P.powerset.filter
        (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y))
      (fun D => pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase) ≤
      4 * (H₁ + H₂) * (k : ℝ) * Y ^ 2 + 8 * (k : ℝ) ^ 2 * Y ^ 3 := by
  classical
  let S := P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Y)
  let A : ℝ := 2 * (H₁ + H₂) * (k : ℝ)
  let B : ℝ := 4 * (k : ℝ) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsumErr :
      Finset.sum S (fun D => pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase) ≤
        Finset.sum S (fun D =>
          A * ((∏ p ∈ D, p : ℕ) : ℝ) +
            B * ((∏ p ∈ D, p : ℕ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro D hD
    have hDP : D ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hper := pairSieveLatticeError_le P D hDP W H₁ H₂ hH₁ hH₂
      hk hprime hcopBase
    rw [pairSieveModulus_prod] at hper
    have hper' : pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase ≤
        A * ((∏ p ∈ D, p : ℕ) : ℝ) +
          B * ((∏ p ∈ D, p : ℕ) : ℝ) ^ 2 := by
      dsimp [A, B]
      convert hper using 1 <;> push_cast <;> ring
    exact hper'
  have hpoly := powerset_product_linear_quadratic_sum_le P hprime Y A B hY hA hB
  calc
    _ = Finset.sum S (fun D => pairSieveLatticeError P D W H₁ H₂ hk hprime hcopBase) := by rfl
    _ ≤ Finset.sum S (fun D =>
          A * ((∏ p ∈ D, p : ℕ) : ℝ) +
            B * ((∏ p ∈ D, p : ℕ) : ℝ) ^ 2) := hsumErr
    _ ≤ 2 * A * Y ^ 2 + 2 * B * Y ^ 3 := by simpa [S] using hpoly
    _ = 4 * (H₁ + H₂) * (k : ℝ) * Y ^ 2 +
        8 * (k : ℝ) ^ 2 * Y ^ 3 := by dsimp [A, B]; ring

theorem pairSieveIntersection_card_eq {k : ℕ} (D : Finset ℕ) (W H₁ H₂ : ℝ)
    (hprime : ∀ p ∈ D, p.Prime) (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)] :
    (((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
        (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)).filter fun mn : ℕ × ℕ =>
        ((mn.1 : ZMod k) * (mn.2 : ZMod k) = 1) ∧
          ∀ p ∈ D, localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))).card =
      dyadicPairResidueClassCount H₁ H₂
        (∏ i : PairSieveIndex D, pairSieveModulus k D i)
        (pairSieveResidues D W hprime hcopBase) := by
  classical
  let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
  let U := (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
    (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)
  let A : Finset (ℕ × ℕ) := U.filter fun mn =>
    ((mn.1 : ZMod k) * (mn.2 : ZMod k) = 1) ∧
      ∀ p ∈ D, localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))
  let B : Finset (ℕ × ℕ) := U.filter fun mn =>
    ((mn.1 : ZMod q), (mn.2 : ZMod q)) ∈ pairSieveResidues D W hprime hcopBase
  have hsets : A = B := by
    ext mn
    rcases mn with ⟨m, n⟩
    have hmem := mem_pairSieveResidues_iff D W hprime hcopBase m n
    simp only [A, B, Finset.mem_filter]
    constructor
    · rintro ⟨hU, ⟨hbase, hbad⟩⟩
      exact ⟨hU, hmem.mpr ⟨hbase, hbad⟩⟩
    · rintro ⟨hU, hres⟩
      rcases hmem.mp hres with ⟨hbase, hbad⟩
      exact ⟨hU, ⟨hbase, hbad⟩⟩
  calc
    _ = A.card := by rfl
    _ = B.card := congrArg Finset.card hsets
    _ = dyadicPairResidueClassCount H₁ H₂ q (pairSieveResidues D W hprime hcopBase) := by
      rfl

noncomputable def pairSieveRho (W : ℝ) (p : ℕ) : ℕ :=
  if (p : ℝ) ≤ W then (2 * p - 1) + (p - 1) else p - 1

noncomputable def pairSieveG (W : ℝ) (p : ℕ) : ℝ :=
  (pairSieveRho W p : ℝ) / (p : ℝ) ^ 2

theorem pairSieveG_bounds {p : ℕ} (hp : 3 ≤ p) (W : ℝ) :
    0 ≤ pairSieveG W p ∧ pairSieveG W p ≤ 7 / 9 ∧
      pairSieveG W p ≤ 3 / (p : ℝ) := by
  classical
  let t : ℝ := p
  have ht3 : 3 ≤ t := by
    dsimp [t]
    exact_mod_cast hp
  have htpos : 0 < t := by linarith
  by_cases hW : t ≤ W
  · have hRho : (pairSieveRho W p : ℝ) = 3 * t - 2 := by
      dsimp [pairSieveRho]
      rw [if_pos hW]
      have hp1 : 1 ≤ p := by omega
      have hp2 : 1 ≤ 2 * p := by omega
      push_cast [Nat.cast_sub hp1, Nat.cast_sub hp2]
      dsimp [t]
      ring
    have hG : pairSieveG W p = (3 * t - 2) / t ^ 2 := by
      simp [pairSieveG, hRho, t]
    rw [hG]
    have hnum : 0 ≤ 3 * t - 2 := by nlinarith
    have hden : 0 < t ^ 2 := sq_pos_of_pos htpos
    refine ⟨div_nonneg hnum hden.le, ?_, ?_⟩
    · exact (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 9)).2 (by nlinarith)
    · have htcast : (p : ℝ) = t := rfl
      rw [htcast]
      exact (div_le_div_iff₀ hden htpos).2 (by nlinarith)

  · have hRho : (pairSieveRho W p : ℝ) = t - 1 := by
      dsimp [pairSieveRho]
      rw [if_neg hW]
      have hp1 : 1 ≤ p := by omega
      push_cast [Nat.cast_sub hp1]
      dsimp [t]
    have hG : pairSieveG W p = (t - 1) / t ^ 2 := by
      simp [pairSieveG, hRho, t]
    rw [hG]
    have hnum : 0 ≤ t - 1 := by linarith
    have hden : 0 < t ^ 2 := sq_pos_of_pos htpos
    refine ⟨div_nonneg hnum hden.le, ?_, ?_⟩
    · exact (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 9)).2 (by nlinarith)
    · have htcast : (p : ℝ) = t := rfl
      rw [htcast]
      exact (div_le_div_iff₀ hden htpos).2 (by nlinarith)

theorem pairSieveG_block_sum_le {P : Finset ℕ} (W C v : ℝ)
    (hG : ∀ p ∈ P, pairSieveG W p ≤ 3 / (p : ℝ))
    (hRecip : ∑ p ∈ P.filter
      (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), 1 / (p : ℝ) ≤ C)
    (hv : 1 < v) :
    (∑ p ∈ P.filter
      (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), pairSieveG W p) ≤ 3 * C := by
  calc
    _ ≤ ∑ p ∈ P.filter
        (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), 3 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hG p (Finset.mem_filter.mp hp).1
    _ = 3 * ∑ p ∈ P.filter
        (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ 3 * C := mul_le_mul_of_nonneg_left hRecip (by norm_num)

private noncomputable def pairReciprocalPrimeSum (y : ℝ) : ℝ :=
  ∑ p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo y, 1 / (p : ℝ)

private theorem mem_primesUpTo_real {y : ℝ} (hy : 0 ≤ y) {p : ℕ} :
    p ∈ ArtinPrimitiveRoots.TypeII.primesUpTo y ↔ p.Prime ∧ (p : ℝ) ≤ y := by
  simp only [ArtinPrimitiveRoots.TypeII.primesUpTo, Finset.mem_filter,
    Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy]
  exact and_comm

theorem exists_reciprocalPrimeDyadicBlockBound :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 1 < v →
      (∑ p ∈ (ArtinPrimitiveRoots.TypeII.primesUpTo (v ^ 2)).filter
        (fun p : ℕ => v < (p : ℝ)), 1 / (p : ℝ)) ≤ C := by
  classical
  obtain ⟨y₀, hy₀, hMertens⟩ :=
    ArtinPrimitiveRoots.Ext.TypeIIInputs.mertens.1 (1 : ℝ) (by norm_num)
  let Csmall : ℝ := pairReciprocalPrimeSum (y₀ ^ 2)
  let C : ℝ := max 4 Csmall
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall, pairReciprocalPrimeSum]
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (by norm_num) (Nat.cast_nonneg p)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro v hv
  let all : Finset ℕ := ArtinPrimitiveRoots.TypeII.primesUpTo (v ^ 2)
  let high : Finset ℕ := all.filter fun p => v < (p : ℝ)
  let low : Finset ℕ := all.filter fun p => ¬ v < (p : ℝ)
  have hv0 : 0 ≤ v := by linarith
  have hvSq : v ≤ v ^ 2 := by nlinarith
  have hLowEq : low = ArtinPrimitiveRoots.TypeII.primesUpTo v := by
    ext p
    have hv20 : 0 ≤ v ^ 2 := sq_nonneg v
    simp only [low, all, Finset.mem_filter]
    rw [mem_primesUpTo_real hv20, mem_primesUpTo_real hv0]
    simp only [not_lt]
    constructor
    · rintro ⟨⟨hp, hpSq⟩, hpNot⟩
      exact ⟨hp, hpNot⟩
    · rintro ⟨hp, hpv⟩
      exact ⟨⟨hp, hpv.trans hvSq⟩, hpv⟩
  have hsplit : pairReciprocalPrimeSum (v ^ 2) =
      (∑ p ∈ high, 1 / (p : ℝ)) + pairReciprocalPrimeSum v := by
    unfold pairReciprocalPrimeSum
    rw [← hLowEq]
    simpa [all, high, low] using
      (Finset.sum_filter_add_sum_filter_not all (fun p : ℕ => v < (p : ℝ))
        (fun p : ℕ => 1 / (p : ℝ))).symm
  by_cases hvLarge : y₀ ≤ v
  · have hvSqLarge : y₀ ≤ v ^ 2 := by nlinarith [hy₀, hv, hvLarge]
    have hAtV := hMertens v hvLarge
    have hAtSq := hMertens (v ^ 2) hvSqLarge
    have hUpperV : pairReciprocalPrimeSum (v ^ 2) ≤
        Real.log (Real.log (v ^ 2)) +
          ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant + 1 := by
      have h := (abs_le.mp hAtSq).2
      dsimp [pairReciprocalPrimeSum] at h ⊢
      linarith
    have hLowerV :
        Real.log (Real.log v) +
          ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant - 1 ≤
            pairReciprocalPrimeSum v := by
      have h := (abs_le.mp hAtV).1
      dsimp [pairReciprocalPrimeSum] at h ⊢
      linarith
    have hlogv : 0 < Real.log v := Real.log_pos hv
    have hlogDiff :
        Real.log (Real.log (v ^ 2)) - Real.log (Real.log v) = Real.log 2 := by
      have hpow : Real.log (v ^ 2) = (2 : ℝ) * Real.log v := by
        rw [Real.log_pow]
        norm_num
      rw [hpow]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogv)]
      ring
    have hhigh : (∑ p ∈ high, 1 / (p : ℝ)) ≤ 3 := by
      have hdiff :
          (∑ p ∈ high, 1 / (p : ℝ)) ≤
            Real.log (Real.log (v ^ 2)) +
              ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant + 1 -
                (Real.log (Real.log v) +
                  ArtinPrimitiveRoots.Ext.TypeIIInputs.meisselMertensConstant - 1) := by
        linarith [hsplit, hUpperV, hLowerV]
      have hlog2 : Real.log 2 ≤ 1 := by
        have hExp₂ : 2 ≤ Real.exp (1 : ℝ) := by
          have hh := Real.add_one_le_exp (1 : ℝ)
          norm_num at hh ⊢
          linarith
        calc
          Real.log 2 ≤ Real.log (Real.exp 1) :=
            Real.log_le_log (by norm_num) hExp₂
          _ = 1 := Real.log_exp 1
      linarith [hdiff, hlogDiff, hlog2]
    have hC4 : (4 : ℝ) ≤ C := by dsimp [C]; exact le_max_left _ _
    exact le_trans hhigh (by linarith [hC4])
  · have hvSmall : v < y₀ := lt_of_not_ge hvLarge
    have hSqSmall : v ^ 2 ≤ y₀ ^ 2 := by
      nlinarith [hvSmall, hv]
    have hHighSubset : high ⊆ ArtinPrimitiveRoots.TypeII.primesUpTo (y₀ ^ 2) := by
      intro p hp
      have hpall := (Finset.mem_filter.mp hp).1
      exact ArtinPrimitiveRoots.Construction.Proofs.C4.primesUpTo_subset_of_le
        (by positivity) hSqSmall hpall
    have hsumSmall :
        (∑ p ∈ high, 1 / (p : ℝ)) ≤ Csmall := by
      dsimp [Csmall, pairReciprocalPrimeSum]
      apply Finset.sum_le_sum_of_subset_of_nonneg hHighSubset
      intro p hp hpLarge
      exact div_nonneg (by norm_num) (Nat.cast_nonneg p)
    have hCsmallLe : Csmall ≤ C := by dsimp [C]; exact le_max_right _ _
    exact le_trans hsumSmall hCsmallLe

theorem exists_reciprocalPrimeBlockBoundForPrimeSet :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ v : ℝ, 1 < v →
      (∑ p ∈ P.filter
        (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), 1 / (p : ℝ)) ≤ C := by
  obtain ⟨C, hC, hGlobal⟩ := exists_reciprocalPrimeDyadicBlockBound
  refine ⟨C, hC, ?_⟩
  intro P hprime v hv
  have hv20 : 0 ≤ v ^ 2 := sq_nonneg v
  let Q := ArtinPrimitiveRoots.TypeII.primesUpTo (v ^ 2)
  have hsubset : P.filter
      (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2) ⊆
        Q.filter (fun p : ℕ => v < (p : ℝ)) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpP, ⟨hpLo, hpHi⟩⟩
    have hpPrime := hprime p hpP
    have hpQ : p ∈ Q :=
      (mem_primesUpTo_real hv20).2 ⟨hpPrime, hpHi⟩
    exact Finset.mem_filter.mpr ⟨hpQ, hpLo⟩
  calc
    _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => v < (p : ℝ)), 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by
          intro p hp hpnot
          exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
            (show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p))
    _ ≤ C := by simpa [Q] using hGlobal v hv

set_option maxHeartbeats 1000000 in
theorem pairSieveMainTerm_eq {k : ℕ} (D : Finset ℕ) (W H₁ H₂ : ℝ)
    (hk : 0 < k) (hprime : ∀ p ∈ D, p.Prime)
    (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    [∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i)] :
    ((pairSieveResidues D W hprime hcopBase).card : ℝ) *
        (((H₁ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ)) *
          (H₂ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ)))) =
      (H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
        ∏ p ∈ D, pairSieveG W p := by
  classical
  let q := ∏ i : PairSieveIndex D, pairSieveModulus k D i
  let ellReal : ℝ := ∏ p ∈ D, (p : ℝ)
  have hcardNat := pairSieveResidues_card D W hk hprime hcopBase
  have hcardReal : (pairSieveResidues D W hprime hcopBase).card =
      (Nat.totient k : ℝ) * ∏ p ∈ D, (pairSieveRho W p : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcardNat
    push_cast at hcast
    simpa [pairSieveRho] using hcast
  have hqReal : (q : ℝ) = (k : ℝ) * ellReal := by
    have hqNat : q = k * (∏ p ∈ D, p) := by
      dsimp [q]
      exact pairSieveModulus_prod k D
    rw [hqNat]
    push_cast
    rfl
  have hprodG : (∏ p ∈ D, pairSieveG W p) =
      (∏ p ∈ D, (pairSieveRho W p : ℝ)) / ellReal ^ 2 := by
    calc
      _ = ∏ p ∈ D, (pairSieveRho W p : ℝ) / (p : ℝ) ^ 2 := by
        simp [pairSieveG]
      _ = (∏ p ∈ D, (pairSieveRho W p : ℝ)) /
          (∏ p ∈ D, (p : ℝ) ^ 2) := by
            rw [Finset.prod_div_distrib]
      _ = (∏ p ∈ D, (pairSieveRho W p : ℝ)) / ellReal ^ 2 := by
            rw [Finset.prod_pow]
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hellpos : 0 < ellReal := by
    dsimp [ellReal]
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (hprime p hp).pos
  calc
    _ = ((Nat.totient k : ℝ) * ∏ p ∈ D, (pairSieveRho W p : ℝ)) *
          ((H₁ / ((k : ℝ) * ellReal)) *
            (H₂ / ((k : ℝ) * ellReal))) := by
          rw [hcardReal, hqReal]
    _ = (H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
          ((∏ p ∈ D, (pairSieveRho W p : ℝ)) / ellReal ^ 2) := by
          field_simp [hkreal, ne_of_gt hellpos]
          <;> ring
    _ = (H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
          ∏ p ∈ D, pairSieveG W p := by rw [hprodG]

noncomputable def pairSieveIntersectionPairs (H₁ H₂ : ℝ) (k : ℕ)
    (D : Finset ℕ) (W : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((ArtinPrimitiveRoots.TypeII.dyadicIntegers H₁).product
      (ArtinPrimitiveRoots.TypeII.dyadicIntegers H₂)).filter fun mn : ℕ × ℕ =>
        ((mn.1 : ZMod k) * (mn.2 : ZMod k) = 1) ∧
          ∀ p ∈ D, localBadProductPredicate W p ((mn.1 : ZMod p), (mn.2 : ZMod p))

set_option maxHeartbeats 1000000 in
theorem pairSieveIntersection_error_bound {k : ℕ} (D : Finset ℕ)
    (W H₁ H₂ : ℝ) (hk : 0 < k)
    (hprime : ∀ p ∈ D, p.Prime) (hcopBase : ∀ p ∈ D, Nat.Coprime k p)
    (hH₁ : 2 ≤ H₁) (hH₂ : 2 ≤ H₂)
    [NeZero (∏ i : PairSieveIndex D, pairSieveModulus k D i)]
    [∀ i : PairSieveIndex D, NeZero (pairSieveModulus k D i)] :
    |((pairSieveIntersectionPairs H₁ H₂ k D W).card : ℝ) -
        (H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
          ∏ p ∈ D, pairSieveG W p| ≤
      2 * (H₁ + H₂) *
          ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) +
        4 * ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) ^ 2 := by
  classical
  have hCount : (pairSieveIntersectionPairs H₁ H₂ k D W).card =
      dyadicPairResidueClassCount H₁ H₂
        (∏ i : PairSieveIndex D, pairSieveModulus k D i)
        (pairSieveResidues D W hprime hcopBase) := by
    simpa [pairSieveIntersectionPairs] using
      pairSieveIntersection_card_eq D W H₁ H₂ hprime hcopBase
  have hMain := pairSieveMainTerm_eq D W H₁ H₂ hk hprime hcopBase
  have hErr := pairSieveLatticeError_le D D (by intro p hp; exact hp)
    W H₁ H₂ hH₁ hH₂ hk hprime hcopBase
  have hErrForm :
      |(dyadicPairResidueClassCount H₁ H₂
          (∏ i : PairSieveIndex D, pairSieveModulus k D i)
          (pairSieveResidues D W hprime hcopBase) : ℝ) -
        ((pairSieveResidues D W hprime hcopBase).card : ℝ) *
          ((H₁ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ)) *
            (H₂ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ)))| ≤
        2 * (H₁ + H₂) *
            ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) +
          4 * ((∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ) : ℝ) ^ 2 := by
    simpa [pairSieveLatticeError] using hErr
  have hdiff :
      (((pairSieveIntersectionPairs H₁ H₂ k D W).card : ℝ) -
        (H₁ * H₂ * (Nat.totient k : ℝ) / (k : ℝ) ^ 2) *
          ∏ p ∈ D, pairSieveG W p) =
      (dyadicPairResidueClassCount H₁ H₂
          (∏ i : PairSieveIndex D, pairSieveModulus k D i)
          (pairSieveResidues D W hprime hcopBase) : ℝ) -
        ((pairSieveResidues D W hprime hcopBase).card : ℝ) *
          ((H₁ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ)) *
            (H₂ / (∏ i : PairSieveIndex D, pairSieveModulus k D i : ℕ))) := by
    rw [hCount, hMain]
  rw [hdiff]
  exact hErrForm

end ArtinPrimitiveRoots.Construction.Proofs.C4
