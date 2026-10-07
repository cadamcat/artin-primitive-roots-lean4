import ArtinPrimitiveRoots.Sieve.Block.Tail

namespace ArtinPrimitiveRoots.Sieve.Block

/-- The descending square-root thresholds used to divide a finite prime set into blocks. -/
noncomputable def blockThreshold (z : ℝ) (j : ℕ) : ℝ :=
  z ^ ((2 : ℝ) ^ j)⁻¹

@[simp] theorem blockThreshold_zero (z : ℝ) : blockThreshold z 0 = z := by
  simp [blockThreshold]

theorem blockThreshold_succ_sq {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    (blockThreshold z (j + 1)) ^ 2 = blockThreshold z j := by
  unfold blockThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
  congr 1
  have hpow : (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := by
    rw [pow_succ]
  rw [hpow]
  field_simp
  norm_num

/-- Every natural number plus one is bounded by the corresponding power of two. -/
theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    nlinarith

/-- For `z > 1` and `p > 1`, some square-root threshold lies below `p`. -/
theorem exists_blockThreshold_lt {z : ℝ} {p : ℕ} (hz : 1 < z) (hp : 1 < p) :
    ∃ j : ℕ, blockThreshold z (j + 1) < (p : ℝ) := by
  have hzpos : 0 < z := by linarith
  have hpNat : 0 < p := by omega
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hpNat
  have hpone : 1 < (p : ℝ) := by exact_mod_cast hp
  have hzlog : 0 < Real.log z := Real.log_pos hz
  have hplog : 0 < Real.log p := Real.log_pos hpone
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log z / Real.log p)
  have hpowN : (n + 1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast nat_succ_le_two_pow n
  have hpowSucc : (n : ℝ) < (2 : ℝ) ^ (n + 1) := by
    have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
    exact lt_of_lt_of_le (by linarith : (n : ℝ) < n + 1) (hpowN.trans hpow)
  have hratio : Real.log z / Real.log p < (2 : ℝ) ^ (n + 1) :=
    lt_trans hn hpowSucc
  have hlog : Real.log z / (2 : ℝ) ^ (n + 1) < Real.log p := by
    apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ (n + 1))).2
    have hh := (div_lt_iff₀ hplog).1 hratio
    nlinarith
  have hexp : ((2 : ℝ) ^ (n + 1))⁻¹ * Real.log z < Real.log p := by
    simpa [div_eq_mul_inv, mul_comm] using hlog
  refine ⟨n, ?_⟩
  rw [blockThreshold]
  exact (Real.rpow_lt_iff_lt_log hzpos hppos).2 hexp

/-- The least threshold index places a prime in exactly one square-root interval. -/
theorem blockThreshold_find_interval {z : ℝ} {p : ℕ}
    (hz : 1 < z) (hp : 1 < p) (hpz : (p : ℝ) ≤ z) :
    let hExists := exists_blockThreshold_lt hz hp
    let j := Nat.find hExists
    blockThreshold z (j + 1) < (p : ℝ) ∧ (p : ℝ) ≤ blockThreshold z j := by
  classical
  let hExists := exists_blockThreshold_lt hz hp
  let j := Nat.find hExists
  change blockThreshold z (j + 1) < (p : ℝ) ∧ (p : ℝ) ≤ blockThreshold z j
  have hlo := Nat.find_spec hExists
  refine ⟨hlo, ?_⟩
  by_cases hj0 : j = 0
  · simpa [j, hj0, blockThreshold] using hpz
  · have hjpos : 1 ≤ j := Nat.pos_of_ne_zero hj0
    have hnot : ¬ blockThreshold z ((j - 1) + 1) < (p : ℝ) := by
      intro hsmall
      have hmin := Nat.find_min' hExists hsmall
      omega
    have hsub : j - 1 + 1 = j := Nat.sub_add_cancel hjpos
    have hnot' : ¬ blockThreshold z j < (p : ℝ) := by simpa [hsub] using hnot
    exact le_of_not_gt hnot'

/-- Index of a prime by the first square-root threshold below it. -/
noncomputable def powerBlockIndex {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (p : ↥P) : ℕ :=
  Nat.find (exists_blockThreshold_lt hz ((hP p.1 p.2).1.one_lt))

theorem powerBlockIndex_spec {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (p : ↥P) :
    blockThreshold z (powerBlockIndex P hz hP p + 1) < (p.1 : ℝ) ∧
      (p.1 : ℝ) ≤ blockThreshold z (powerBlockIndex P hz hP p) := by
  simpa [powerBlockIndex] using
    (blockThreshold_find_interval hz ((hP p.1 p.2).1.one_lt) (hP p.1 p.2).2)

/-- The finite block of coordinates whose first crossing index is `j`. -/
noncomputable def powerBlock {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (j : ℕ) : Finset ↥P :=
  Finset.univ.filter (fun p => powerBlockIndex P hz hP p = j)

/-- A finite upper bound for all block indices. -/
noncomputable def powerBlockCount {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) : ℕ :=
  ∑ p : ↥P, (powerBlockIndex P hz hP p + 1)

/-- Blocks indexed below `powerBlockCount` partition the finite coordinate type `P`. -/
theorem powerBlocks_partition {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) :
    (∀ p : ↥P, ∃ j : Fin (powerBlockCount P hz hP),
      p ∈ powerBlock P hz hP j.1) ∧
    (∀ j k : Fin (powerBlockCount P hz hP), j ≠ k →
      Disjoint (powerBlock P hz hP j.1) (powerBlock P hz hP k.1)) := by
  classical
  constructor
  · intro p
    have hle : powerBlockIndex P hz hP p + 1 ≤ powerBlockCount P hz hP := by
      unfold powerBlockCount
      change powerBlockIndex P hz hP p + 1 ≤
        ∑ q : ↥P, (powerBlockIndex P hz hP q + 1)
      exact Finset.single_le_sum (f := fun q => powerBlockIndex P hz hP q + 1)
        (fun q hq => Nat.zero_le _) (Finset.mem_univ p)
    refine ⟨⟨powerBlockIndex P hz hP p, by omega⟩, ?_⟩
    simp [powerBlock]
  · intro j k hjk
    rw [Finset.disjoint_left]
    intro p hpj hpk
    simp [powerBlock] at hpj hpk
    exact hjk (Fin.ext (hpj.symm.trans hpk))

/-- Each prime in a threshold block lies in the interval to which the local mean hypothesis
applies. -/
theorem powerBlock_mem_sieve_interval {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z)
    (j : Fin (powerBlockCount P hz hP)) {p : ↥P}
    (hp : p ∈ powerBlock P hz hP j.1) :
    1 < blockThreshold z (j.1 + 1) ∧
      blockThreshold z (j.1 + 1) < (p.1 : ℝ) ∧
      (p.1 : ℝ) ≤ (blockThreshold z (j.1 + 1)) ^ 2 := by
  have hidx : powerBlockIndex P hz hP p = j.1 := by
    simpa [powerBlock] using hp
  have hspec := powerBlockIndex_spec P hz hP p
  rw [hidx] at hspec
  have hlow : 0 < ((2 : ℝ) ^ (j.1 + 1))⁻¹ := inv_pos.mpr (by positivity)
  have hv : 1 < blockThreshold z (j.1 + 1) := by
    exact Real.one_lt_rpow hz hlow
  refine ⟨hv, hspec.1, ?_⟩
  rw [blockThreshold_succ_sq (le_of_lt (by linarith : 0 < z))]
  exact hspec.2

/-- The total mean of a threshold block is bounded by the local interval hypothesis. -/
theorem powerBlock_sum_le {z : ℝ} (P : Finset ℕ) (hz : 1 < z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (j : Fin (powerBlockCount P hz hP))
    (g : ℕ → ℝ) (hg0 : ∀ p ∈ P, 0 ≤ g p) (C : ℝ)
    (hLocal : ∀ v : ℝ, 1 < v →
      (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p) ≤ C) :
    (∑ p ∈ powerBlock P hz hP j.1, g p.1) ≤ C := by
  classical
  let v := blockThreshold z (j.1 + 1)
  let e : ↥P ↪ ℕ := ⟨Subtype.val, fun a b hab => Subtype.ext hab⟩
  let Q := P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2)
  have hv : 1 < v := by
    dsimp [v, blockThreshold]
    exact Real.one_lt_rpow hz (inv_pos.mpr (by positivity))
  have hmap : (powerBlock P hz hP j.1).map e ⊆ Q := by
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    have hi := powerBlock_mem_sieve_interval P hz hP j hq
    simp only [Q, Finset.mem_filter]
    refine ⟨q.2, ?_⟩
    change v < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ v ^ 2
    exact ⟨by simpa [v] using hi.2.1, by simpa [v] using hi.2.2⟩
  have hsumMap :
      (∑ p ∈ powerBlock P hz hP j.1, g p.1) =
        ∑ p ∈ (powerBlock P hz hP j.1).map e, g p := by
    exact (Finset.sum_map (powerBlock P hz hP j.1) e g).symm
  calc
    (∑ p ∈ powerBlock P hz hP j.1, g p.1) =
        ∑ p ∈ (powerBlock P hz hP j.1).map e, g p := hsumMap
    _ ≤ ∑ p ∈ Q, g p :=
      Finset.sum_le_sum_of_subset_of_nonneg hmap
        (fun p hp hnot => hg0 p (Finset.mem_filter.mp hp).1)
    _ ≤ C := hLocal v hv

/-- Tuples choosing a subset from every block of a finite partition. -/
def blockTupleSet {α : Type*} [DecidableEq α] (N : ℕ) (B : Fin N → Finset α) :
    Finset (Fin N → Finset α) :=
  Fintype.piFinset (fun j : Fin N => (B j).powerset)

/-- Union of the subsets selected by a block tuple. -/
def blockTupleUnion {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ}
    (d : Fin N → Finset α) : Finset α :=
  Finset.univ.biUnion d

/-- Under a disjoint partition, selecting one subset from each block is equivalent to selecting
one subset of the whole set. -/
theorem blockTupleUnion_bijective {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k)) :
    (∀ d ∈ blockTupleSet N B, blockTupleUnion d ∈ P.powerset) ∧
      Set.InjOn blockTupleUnion (blockTupleSet N B : Set (Fin N → Finset α)) ∧
      (∀ D ∈ P.powerset, ∃ d ∈ blockTupleSet N B, blockTupleUnion d = D) := by
  classical
  have hDsub : ∀ d ∈ blockTupleSet N B, ∀ j, d j ⊆ B j := by
    intro d hd j
    have hd' : ∀ j, d j ∈ (B j).powerset := by simpa [blockTupleSet] using hd
    have hmem : d j ∈ (B j).powerset := by
      exact hd' j
    exact Finset.mem_powerset.mp hmem
  have hUnionSub : ∀ d ∈ blockTupleSet N B, blockTupleUnion d ⊆ P := by
    intro d hd x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    exact hBsub j (hDsub d hd j hxj)
  have hpiece : ∀ d ∈ blockTupleSet N B, ∀ j,
      d j = blockTupleUnion d ∩ B j := by
    intro d hd j
    ext x
    constructor
    · intro hx
      refine Finset.mem_inter.mpr ⟨?_, hDsub d hd j hx⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxU, hxj⟩
      rcases Finset.mem_biUnion.mp hxU with ⟨k, hk, hxk⟩
      by_cases hkj : k = j
      · simpa [hkj] using hxk
      · exact (Finset.disjoint_left.mp (hdisj k j hkj) (hDsub d hd k hxk) hxj).elim
  have hinj : Set.InjOn blockTupleUnion (blockTupleSet N B : Set (Fin N → Finset α)) := by
    intro d hd d' hd' heq
    funext j
    calc
      d j = blockTupleUnion d ∩ B j := hpiece d hd j
      _ = blockTupleUnion d' ∩ B j := by rw [heq]
      _ = d' j := (hpiece d' hd' j).symm
  refine ⟨?_, hinj, ?_⟩
  · intro d hd
    exact Finset.mem_powerset.mpr (hUnionSub d hd)
  · intro D hD
    have hDs : D ⊆ P := Finset.mem_powerset.mp hD
    let d : Fin N → Finset α := fun j => D ∩ B j
    have hd : d ∈ blockTupleSet N B := by
      simp [blockTupleSet, d, Finset.mem_powerset]
    refine ⟨d, hd, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
      exact (Finset.mem_inter.mp hxj).1
    · intro hx
      rcases hcover x (hDs hx) with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hj⟩⟩

/-- The part chosen from a block is its intersection with the union of the tuple. -/
theorem blockTuple_piece_eq_inter {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (d : Fin N → Finset α) (hd : d ∈ blockTupleSet N B) (j : Fin N) :
    d j = blockTupleUnion d ∩ B j := by
  classical
  have hd' : ∀ j, d j ⊆ B j := by
    simpa [blockTupleSet] using hd
  ext x
  constructor
  · intro hx
    refine Finset.mem_inter.mpr ⟨?_, hd' j hx⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxU, hxj⟩
    rcases Finset.mem_biUnion.mp hxU with ⟨k, hk, hxk⟩
    by_cases hkj : k = j
    · simpa [hkj] using hxk
    · exact (Finset.disjoint_left.mp (hdisj k j hkj) (hd' k hxk) hxj).elim

/-- Products of squarefree monomials over disjoint blocks combine to the monomial on their union. -/
theorem blockTuple_gProduct {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (g : α → ℝ) (d : Fin N → Finset α)
    (hd : d ∈ blockTupleSet N B) :
    (∏ j, ∏ p ∈ d j, g p) = ∏ p ∈ blockTupleUnion d, g p := by
  classical
  have hdsub : ∀ j, d j ⊆ B j := by simpa [blockTupleSet] using hd
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) d := by
    intro j hj k hk hjk
    exact Finset.disjoint_of_subset_left (hdsub j) <|
      Finset.disjoint_of_subset_right (hdsub k) (hdisj j k hjk)
  exact (Finset.prod_biUnion hdis (f := g)).symm

/-- The product of blockwise bad indicators is the indicator that their union is all bad. -/
theorem blockTuple_badIndicator {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α)
    (hBsub : ∀ j, B j ⊆ P) (d : Fin N → Finset α)
    (hd : d ∈ blockTupleSet N B) (x : α → Bool) :
    (∏ j, if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) =
      if blockTupleUnion d ⊆ selectedBadOn P x then (1 : ℝ) else 0 := by
  classical
  have hdsub : ∀ j, d j ⊆ B j := by simpa [blockTupleSet] using hd
  change (∏ j ∈ (Finset.univ : Finset (Fin N)),
    if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) = _
  rw [Finset.prod_boole]
  have hiff : (∀ j, d j ⊆ selectedBadOn (B j) x) ↔
      blockTupleUnion d ⊆ selectedBadOn P x := by
    constructor
    · intro hall y hy
      rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
      have hlocal := hall j hyj
      have hxy : y ∈ B j ∧ x y = true := by simpa [selectedBadOn] using hlocal
      exact Finset.mem_filter.mpr ⟨hBsub j hxy.1, hxy.2⟩
    · intro hglobal j y hy
      have hyU : y ∈ blockTupleUnion d :=
        Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hy⟩
      have hxy : x y = true := (Finset.mem_filter.mp (hglobal hyU)).2
      exact Finset.mem_filter.mpr ⟨hdsub j hy, hxy⟩
  by_cases hall : ∀ j, d j ⊆ selectedBadOn (B j) x
  · have hglobal := hiff.mp hall
    simp [hall, hglobal]
  · have hglobal : ¬ blockTupleUnion d ⊆ selectedBadOn P x := by
      intro h
      exact hall (hiff.mpr h)
    push_neg at hall
    rcases hall with ⟨j, hjnot⟩
    simp [hglobal]
    exact ⟨j, hjnot⟩

/-- A product of local squarefree polynomials expands into one global squarefree polynomial. -/
theorem product_blockPolynomials_eq {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (c : Fin N → Finset α → ℝ) (x : α → Bool) :
    (∏ j, ∑ D ∈ (B j).powerset,
      c j D * (if D ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0)) =
      ∑ D ∈ P.powerset,
        (∏ j, c j (D ∩ B j)) *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
  classical
  have hbij := blockTupleUnion_bijective P B hBsub hcover hdisj
  rcases hbij with ⟨hmap, hinj, hsurj⟩
  calc
    (∏ j, ∑ D ∈ (B j).powerset,
        c j D * (if D ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0)) =
      ∑ d ∈ blockTupleSet N B,
        ∏ j, c j (d j) * (if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) := by
      rw [Finset.prod_univ_sum
        (t := fun j : Fin N => (B j).powerset)
        (f := fun j D => c j D *
          if D ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0)]
      simp [blockTupleSet]
    _ = ∑ D ∈ P.powerset,
        (∏ j, c j (D ∩ B j)) *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
      apply Finset.sum_bij (fun d _ => blockTupleUnion d)
      · intro d hd
        exact hmap d hd
      · intro d hd d' hd' heq
        exact hinj hd hd' heq
      · intro D hD
        rcases hsurj D hD with ⟨d, hd, heq⟩
        exact ⟨d, hd, heq⟩
      · intro d hd
        have hcoeff : (∏ j, c j (d j)) =
            ∏ j, c j (blockTupleUnion d ∩ B j) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [← blockTuple_piece_eq_inter B hdisj d hd j]
        calc
          (∏ j, c j (d j) *
              (if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0)) =
            (∏ j, c j (d j)) *
              (∏ j, if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) := by
                rw [Finset.prod_mul_distrib]
          _ = (∏ j, c j (blockTupleUnion d ∩ B j)) *
              (if blockTupleUnion d ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
                rw [hcoeff, blockTuple_badIndicator P B hBsub d hd x]

/-- A product of local subset sums over a finite disjoint partition reindexes as a sum over
subsets of the whole set. -/
theorem product_block_subset_sums_eq {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (g : α → ℝ) (c : Fin N → Finset α → ℝ) :
    (∏ j, ∑ D ∈ (B j).powerset, c j D * ∏ p ∈ D, g p) =
      ∑ D ∈ P.powerset, (∏ j, c j (D ∩ B j)) * ∏ p ∈ D, g p := by
  classical
  have hbij := blockTupleUnion_bijective P B hBsub hcover hdisj
  rcases hbij with ⟨hmap, hinj, hsurj⟩
  calc
    (∏ j, ∑ D ∈ (B j).powerset, c j D * ∏ p ∈ D, g p) =
      ∑ d ∈ blockTupleSet N B, ∏ j, c j (d j) * ∏ p ∈ d j, g p := by
      rw [Finset.prod_univ_sum
        (t := fun j : Fin N => (B j).powerset)
        (f := fun j D => c j D * ∏ p ∈ D, g p)]
      simp [blockTupleSet]
    _ = ∑ D ∈ P.powerset, (∏ j, c j (D ∩ B j)) * ∏ p ∈ D, g p := by
      apply Finset.sum_bij (fun d _ => blockTupleUnion d)
      · intro d hd
        exact hmap d hd
      · intro d hd d' hd' heq
        exact hinj hd hd' heq
      · intro D hD
        rcases hsurj D hD with ⟨d, hd, heq⟩
        exact ⟨d, hd, heq⟩
      · intro d hd
        calc
          (∏ j, c j (d j) * ∏ p ∈ d j, g p) =
              (∏ j, c j (d j)) * (∏ j, ∏ p ∈ d j, g p) := by
                rw [Finset.prod_mul_distrib]
          _ = (∏ j, c j (d j)) * ∏ p ∈ blockTupleUnion d, g p := by
                rw [blockTuple_gProduct B hdisj g d hd]
          _ = (∏ j, c j ((blockTupleUnion d) ∩ B j)) *
                ∏ p ∈ blockTupleUnion d, g p := by
              congr 1
              apply Finset.prod_congr rfl
              intro j hj
              rw [← blockTuple_piece_eq_inter B hdisj d hd j]

/-- The coefficient of a subset in the product of the block U polynomials. -/
noncomputable def blockUProfileCoefficient {α : Type*} [DecidableEq α]
    {N : ℕ} (B : Fin N → Finset α) (h : Fin N → ℕ) (D : Finset α) : ℝ :=
  ∏ j, if (D ∩ B j).card ≤ h j then (-1 : ℝ) ^ (D ∩ B j).card else 0

/-- The product of the block U polynomials expands as one squarefree polynomial on the union. -/
theorem product_blockU_eq_polynomial {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (P : Finset α) (B : Fin N → Finset α) (h : Fin N → ℕ)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k)) (x : α → Bool) :
    (∏ j, blockU (selectedBadOn (B j) x) (h j)) =
      ∑ D ∈ P.powerset,
        blockUProfileCoefficient B h D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
  classical
  have hbij := blockTupleUnion_bijective P B hBsub hcover hdisj
  rcases hbij with ⟨hmap, hinj, hsurj⟩
  calc
    (∏ j, blockU (selectedBadOn (B j) x) (h j)) =
      ∑ d ∈ blockTupleSet N B,
        ∏ j, (if (d j).card ≤ h j then (-1 : ℝ) ^ (d j).card else 0) *
          (if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) := by
      simp_rw [blockU_selectedOn_support]
      rw [Finset.prod_univ_sum
        (t := fun j : Fin N => (B j).powerset)
        (f := fun j D =>
          if D.card ≤ h j then (-1 : ℝ) ^ D.card *
            (∏ i ∈ D, if x i then (1 : ℝ) else 0) else 0)]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.prod_congr rfl
      intro j hj
      have hd' : ∀ j, d j ⊆ B j := by simpa [blockTupleSet] using hd
      have hD : d j ⊆ B j := hd' j
      have hind : (∏ i ∈ d j, if x i then (1 : ℝ) else 0) =
          if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0 := by
        have hprodEq : (∏ i ∈ d j, if x i then (1 : ℝ) else 0) =
            ∏ i ∈ d j, if i ∈ B j ∧ x i = true then (1 : ℝ) else 0 := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [hD hi]
        have hsel := selectedBadOn_subset_indicator (B j) (d j) x
        rw [← hprodEq] at hsel
        exact hsel.symm
      by_cases hc : (d j).card ≤ h j
      · simp only [if_pos hc]
        simp [hind, mul_comm, mul_left_comm, mul_assoc]
      · simp [hc]
    _ = ∑ D ∈ P.powerset,
        blockUProfileCoefficient B h D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
      apply Finset.sum_bij (fun d _ => blockTupleUnion d)
      · intro d hd
        exact hmap d hd
      · intro d hd d' hd' heq
        exact hinj hd hd' heq
      · intro D hD
        rcases hsurj D hD with ⟨d, hd, heq⟩
        exact ⟨d, hd, heq⟩
      · intro d hd
        have hcoeff :
            (∏ j, if (d j).card ≤ h j then (-1 : ℝ) ^ (d j).card else 0) =
              blockUProfileCoefficient B h (blockTupleUnion d) := by
          unfold blockUProfileCoefficient
          apply Finset.prod_congr rfl
          intro j hj
          rw [← blockTuple_piece_eq_inter B hdisj d hd j]
        have hbool :
            (∏ j, if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) =
              if blockTupleUnion d ⊆ selectedBadOn P x then (1 : ℝ) else 0 := by
          exact blockTuple_badIndicator P B hBsub d hd x
        calc
          (∏ j, (if (d j).card ≤ h j then (-1 : ℝ) ^ (d j).card else 0) *
              (if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0)) =
            (∏ j, if (d j).card ≤ h j then (-1 : ℝ) ^ (d j).card else 0) *
              (∏ j, if d j ⊆ selectedBadOn (B j) x then (1 : ℝ) else 0) := by
                rw [Finset.prod_mul_distrib]
          _ =
            blockUProfileCoefficient B h (blockTupleUnion d) *
              (if blockTupleUnion d ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
                rw [hcoeff, hbool]

/-- Any monomial appearing in a block product or its one-block correction satisfies the frozen
product cutoff. -/
theorem powerBlockTuple_product_cutoff {z : ℝ} (P : Finset ℕ) (hz : 2 ≤ z)
    (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (H : ℕ)
    (d : Fin (powerBlockCount P (by linarith : 1 < z) hP) → Finset (↥P))
    (hd : d ∈ blockTupleSet _ (fun j => powerBlock P (by linarith : 1 < z) hP j.val))
    (hdeg : ∀ j, (d j).card ≤ (j.val + 1) * H + 1) :
    (∏ p ∈ blockTupleUnion d, (p.1 : ℝ)) ≤ z ^ (4 * (H : ℝ) + 2) := by
  classical
  let hz' : 1 < z := by linarith
  let N := powerBlockCount P hz' hP
  let B : Fin N → Finset (↥P) := fun j => powerBlock P hz' hP j.val
  have hpart := powerBlocks_partition P hz' hP
  have hBsub : ∀ j, B j ⊆ (Finset.univ : Finset (↥P)) := fun j => Finset.subset_univ _
  have hcover : ∀ q ∈ (Finset.univ : Finset (↥P)), ∃ j, q ∈ B j := by
    intro q hq
    rcases hpart.1 q with ⟨j, hj⟩
    exact ⟨j, by simpa [B] using hj⟩
  have hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k) := by
    intro j k hjk
    exact hpart.2 j k hjk
  have hdsub : ∀ j, d j ⊆ B j := by simpa [blockTupleSet] using hd
  have hprodUnion := blockTuple_gProduct B hdisj (fun q : ↥P => (q.1 : ℝ)) d hd
  have hlocal : ∀ j, (∏ p ∈ d j, (p.1 : ℝ)) ≤
      (blockThreshold z j.val) ^ ((j.val + 1) * H + 1) := by
    intro j
    let tau := blockThreshold z j.val
    have htau : 1 ≤ tau := by
      dsimp [tau, blockThreshold]
      exact le_of_lt (Real.one_lt_rpow (by linarith) (inv_pos.mpr (by positivity)))
    have hpUpper : ∀ p ∈ d j, (p.1 : ℝ) ≤ tau := by
      intro p hp
      have hmem : p ∈ powerBlock P hz' hP j.val := by simpa [B] using hdsub j hp
      have hi := powerBlock_mem_sieve_interval P hz' hP j hmem
      have hsq := blockThreshold_succ_sq (by linarith : 0 ≤ z) j.val
      dsimp [tau]
      rw [hsq] at hi
      exact hi.2.2
    calc
      (∏ p ∈ d j, (p.1 : ℝ)) ≤ ∏ p ∈ d j, tau := by
        apply Finset.prod_le_prod₀
        · intro p hp
          exact_mod_cast Nat.zero_le p.1
        · exact hpUpper
      _ = tau ^ (d j).card := by simp [tau]
      _ ≤ tau ^ ((j.val + 1) * H + 1) := by
        have hc : ((d j).card : ℝ) ≤ (((j.val + 1) * H + 1 : ℕ) : ℝ) := by
          exact_mod_cast hdeg j
        have hr := Real.rpow_le_rpow_of_exponent_le htau hc
        calc
          tau ^ (d j).card = tau ^ ((d j).card : ℝ) :=
            (Real.rpow_natCast tau (d j).card).symm
          _ ≤ tau ^ (((j.val + 1) * H + 1 : ℕ) : ℝ) := hr
          _ = tau ^ ((j.val + 1) * H + 1) := Real.rpow_natCast tau _
  have hprodBlocks : (∏ j : Fin N, ∏ p ∈ d j, (p.1 : ℝ)) ≤
      ∏ j : Fin N, (blockThreshold z j.val) ^ ((j.val + 1) * H + 1) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      apply Finset.prod_nonneg
      intro p hp
      exact_mod_cast Nat.zero_le p.1
    · intro j hj
      exact hlocal j
  have hterm : ∀ j : Fin N,
      (blockThreshold z j.val) ^ ((j.val + 1) * H + 1) =
        z ^ ((((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) := by
    intro j
    calc
      (blockThreshold z j.val) ^ ((j.val + 1) * H + 1) =
          (blockThreshold z j.val) ^ (((j.val + 1) * H + 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast (blockThreshold z j.val) ((j.val + 1) * H + 1)).symm
      _ = z ^ (((2 : ℝ) ^ j.val)⁻¹ * (((j.val + 1) * H + 1 : ℕ) : ℝ)) := by
        dsimp [blockThreshold]
        rw [← Real.rpow_mul (by linarith : 0 ≤ z)]
      _ = z ^ ((((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) := by
        congr 1
        field_simp
  have hsumExp : (∑ j : Fin N,
      (((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) ≤
        4 * (H : ℝ) + 2 := sum_fin_degree_profile_le
  calc
    (∏ p ∈ blockTupleUnion d, (p.1 : ℝ)) = ∏ j : Fin N, ∏ p ∈ d j, (p.1 : ℝ) := hprodUnion.symm
    _ ≤ ∏ j : Fin N, (blockThreshold z j.val) ^ ((j.val + 1) * H + 1) := hprodBlocks
    _ = ∏ j : Fin N, z ^ ((((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hterm j
    _ = z ^ (∑ j : Fin N,
          (((j.val + 1) * H + 1 : ℕ) : ℝ) / (2 : ℝ) ^ j.val) := by
      exact (Real.rpow_sum_of_nonneg (by linarith : 0 ≤ z)
        (fun j hj => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))).symm
    _ ≤ z ^ (4 * (H : ℝ) + 2) := by
      exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ z) hsumExp

end ArtinPrimitiveRoots.Sieve.Block
