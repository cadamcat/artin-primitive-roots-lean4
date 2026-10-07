import ArtinPrimitiveRoots.Sieve.Block.Profiles
import ArtinPrimitiveRoots.Sieve.Block.SubtypeBridge

set_option maxHeartbeats 1000000

namespace ArtinPrimitiveRoots.Sieve

open Classical
open ArtinPrimitiveRoots.Sieve.Block
open Finset

/-- A subset whose degree in each threshold block is at most `(j+1)H+1` lies in the frozen
product support. -/
theorem subtypeBlockSupportCutoff {P : Finset ℕ} {z : ℝ}
    (hz : 2 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (H : ℕ)
    (D : Finset ↥P)
    (hdeg : ∀ j : Fin (powerBlockCount P (by linarith : 1 < z) hP),
      (D ∩ powerBlock P (by linarith : 1 < z) hP j.1).card ≤ (j.val + 1) * H + 1) :
    ((∏ p ∈ (D.map (subtypeValEmbedding P)), p : ℕ) : ℝ) ≤
      z ^ (4 * H + 2) := by
  classical
  let hz' : 1 < z := by linarith
  let N := powerBlockCount P hz' hP
  let B : Fin N → Finset ↥P := fun j => powerBlock P hz' hP j.val
  let d : Fin N → Finset ↥P := fun j => D ∩ B j
  have hpart := powerBlocks_partition P hz' hP
  have hcover : ∀ p ∈ (Finset.univ : Finset ↥P), ∃ j, p ∈ B j := by
    intro p hp
    rcases hpart.1 p with ⟨j, hj⟩
    exact ⟨j, by simpa [B] using hj⟩
  have hdisj : ∀ j k : Fin N, j ≠ k → Disjoint (B j) (B k) := by
    intro j k hjk
    exact hpart.2 j k hjk
  have hd : d ∈ blockTupleSet N B := by
    simp [blockTupleSet, d, B]
  have hunion : blockTupleUnion d = D := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
      exact (Finset.mem_inter.mp hpj).1
    · intro hpD
      rcases hcover p (Finset.mem_univ p) with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hpD, hj⟩⟩
  have hdeg' : ∀ j : Fin N, (d j).card ≤ (j.val + 1) * H + 1 := by
    intro j
    simpa [d, B] using hdeg j
  have hcut := powerBlockTuple_product_cutoff P hz hP H d hd hdeg'
  rw [hunion] at hcut
  have hmap :
      (∏ p ∈ D, (p.1 : ℝ)) = ∏ p ∈ D.map (subtypeValEmbedding P), (p : ℝ) := by
    exact (Finset.prod_map D (subtypeValEmbedding P) fun p : ℕ => (p : ℝ)).symm
  have hcast :
      ∏ p ∈ D.map (subtypeValEmbedding P), (p : ℝ) =
        ((∏ p ∈ D.map (subtypeValEmbedding P), p : ℕ) : ℝ) := by simp
  calc
    ((∏ p ∈ D.map (subtypeValEmbedding P), p : ℕ) : ℝ) =
        ∏ p ∈ D.map (subtypeValEmbedding P), (p : ℝ) := hcast.symm
    _ = ∏ p ∈ D, (p.1 : ℝ) := hmap.symm
    _ ≤ z ^ ((4 * H + 2 : ℕ) : ℝ) := by
      rw [show ((4 * H + 2 : ℕ) : ℝ) = 4 * (H : ℝ) + 2 by
        norm_num [Nat.cast_mul, Nat.cast_add]]
      exact hcut
    _ = z ^ (4 * H + 2) := Real.rpow_natCast z (4 * H + 2)

/-- The natural-number squarefree products retained by the block degree cutoff. -/
noncomputable def blockCutoffSupportNat (P : Finset ℕ) (z : ℝ) (H : ℕ) :
    Finset (Finset ℕ) :=
  P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2))

/-- The subtype form of the same support, reindexed by the value embedding. -/
noncomputable def blockCutoffSupportSubtype (P : Finset ℕ) (z : ℝ) (H : ℕ) :
    Finset (Finset ↥P) :=
  (blockCutoffSupportNat P z H).preimage
    (fun D : Finset ↥P => D.map (subtypeValEmbedding P))
    (Finset.map_injective (subtypeValEmbedding P)).injOn

/-- Both the U and lower correction coefficients vanish outside the block product support. -/
theorem blockProfileCoefficients_zero_off_cutoff {P : Finset ℕ} {z : ℝ}
    (hz : 2 ≤ z) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) (H : ℕ)
    (D : Finset ↥P)
    (hnot : D ∉ blockCutoffSupportSubtype P z H) :
    (blockUProfileCoefficient
        (fun j : Fin (powerBlockCount P (by linarith : 1 < z) hP) =>
          powerBlock P (by linarith : 1 < z) hP j.1)
        (fun j => (j.val + 1) * H) D = 0) ∧
      (blockLowerProfileCoefficient
        (fun j : Fin (powerBlockCount P (by linarith : 1 < z) hP) =>
          powerBlock P (by linarith : 1 < z) hP j.1)
        (fun j => (j.val + 1) * H) D = 0) := by
  classical
  let hz' : 1 < z := by linarith
  let N := powerBlockCount P hz' hP
  let B : Fin N → Finset ↥P := fun j => powerBlock P hz' hP j.val
  have hmapPow : D.map (subtypeValEmbedding P) ∈ P.powerset := by
    apply Finset.mem_powerset.mpr
    intro p hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact q.2
  have hzeroU : blockUProfileCoefficient B (fun j => (j.val + 1) * H) D = 0 := by
    by_contra hne
    have hdeg := (blockUProfileCoefficient_ne_zero_iff B
      (fun j => (j.val + 1) * H) D).mp hne
    have hdegree : ∀ j, (D ∩ B j).card ≤ (j.val + 1) * H + 1 := by
      intro j
      exact Nat.le_trans (hdeg j) (Nat.le_succ _)
    have hcut := subtypeBlockSupportCutoff hz hP H D hdegree
    apply hnot
    exact Finset.mem_preimage.mpr
      (Finset.mem_filter.mpr ⟨hmapPow, hcut⟩)
  have hzeroL : blockLowerProfileCoefficient B (fun j => (j.val + 1) * H) D = 0 := by
    by_contra hne
    have hdegree : ∀ j, (D ∩ B j).card ≤ (j.val + 1) * H + 1 := by
      intro j
      by_contra hj
      have hbig : (j.val + 1) * H + 1 < (D ∩ B j).card := by omega
      have hz0 := blockLowerProfileCoefficient_eq_zero_of_big_degree
        B (fun j => (j.val + 1) * H) D j hbig
      exact hne (by simpa using hz0)
    have hcut := subtypeBlockSupportCutoff hz hP H D hdegree
    apply hnot
    exact Finset.mem_preimage.mpr
      (Finset.mem_filter.mpr ⟨hmapPow, hcut⟩)
  exact ⟨hzeroU, hzeroL⟩

/-- Evaluation of the lower coefficient polynomial is the product U minus all one-block
corrections. -/
theorem blockLowerProfile_eval_eq {β : Type*} [Fintype β] [DecidableEq β]
    {N : ℕ} (P : Finset β) (B : Fin N → Finset β) (h : Fin N → ℕ)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k)) (x : β → Bool) :
    (∑ D ∈ P.powerset,
      blockLowerProfileCoefficient B h D *
        (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) =
      (∏ j, blockU (selectedBadOn (B j) x) (h j)) -
        ∑ j, blockT (selectedBadOn (B j) x) (h j) *
          ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
  classical
  have hU := product_blockU_eq_polynomial P B h hBsub hcover hdisj x
  have hT : ∀ j,
      (∑ D ∈ P.powerset,
        blockTProfileCoefficient B h j D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) =
        blockT (selectedBadOn (B j) x) (h j) *
          ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
    intro j
    exact (product_blockT_U_eq_polynomial P B h hBsub hcover hdisj j x).symm
  let correctionEval : Finset β → ℝ := fun D =>
    (∑ j, blockTProfileCoefficient B h j D) *
      (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)
  have hterm (D : Finset β) :
      blockLowerProfileCoefficient B h D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) =
        blockUProfileCoefficient B h D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) - correctionEval D := by
    dsimp [blockLowerProfileCoefficient, correctionEval]
    ring
  have hdist :
      (∑ D ∈ P.powerset, correctionEval D) =
        ∑ j, ∑ D ∈ P.powerset,
          blockTProfileCoefficient B h j D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
    calc
      (∑ D ∈ P.powerset, correctionEval D) =
          ∑ D ∈ P.powerset,
            (∑ j, blockTProfileCoefficient B h j D) *
              (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
            rfl
      _ = ∑ D ∈ P.powerset, ∑ j,
          blockTProfileCoefficient B h j D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro D hD
          rw [Finset.sum_mul]
      _ = _ := Finset.sum_comm
  calc
    (∑ D ∈ P.powerset,
      blockLowerProfileCoefficient B h D *
        (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) =
      Finset.sum P.powerset (fun D =>
        blockUProfileCoefficient B h D *
          (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) - correctionEval D) := by
          apply Finset.sum_congr rfl
          intro D hD
          exact hterm D
    _ = (∑ D ∈ P.powerset,
          blockUProfileCoefficient B h D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) -
        ∑ D ∈ P.powerset, correctionEval D :=
      by rw [Finset.sum_sub_distrib]
    _ = (∏ j, blockU (selectedBadOn (B j) x) (h j)) -
        ∑ j, ∑ D ∈ P.powerset,
          blockTProfileCoefficient B h j D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
      rw [← hU, hdist]
    _ = (∏ j, blockU (selectedBadOn (B j) x) (h j)) -
        ∑ j, blockT (selectedBadOn (B j) x) (h j) *
          ∏ k ∈ Finset.univ.erase j, blockU (selectedBadOn (B k) x) (h k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact hT j

/-- Pointwise lower and upper Brun--Hooley polynomial bounds for a finite block partition. -/
theorem blockPolynomialPointwiseBracket {β : Type*} [Fintype β] [DecidableEq β]
    {N : ℕ} (P : Finset β) (B : Fin N → Finset β) (h : Fin N → ℕ)
    (hBsub : ∀ j, B j ⊆ P) (hcover : ∀ x ∈ P, ∃ j, x ∈ B j)
    (hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k))
    (hEven : ∀ j, Even (h j)) (x : β → Bool) :
    ((∑ D ∈ P.powerset,
      blockLowerProfileCoefficient B h D *
        (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) ≤
      (∏ p ∈ P, if x p then (0 : ℝ) else 1)) ∧
      ((∏ p ∈ P, if x p then (0 : ℝ) else 1) ≤
        ∑ D ∈ P.powerset,
          blockUProfileCoefficient B h D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0)) := by
  classical
  let I : Fin N → ℝ := fun j => ∏ p ∈ B j, if x p then (0 : ℝ) else 1
  let U : Fin N → ℝ := fun j => blockU (selectedBadOn (B j) x) (h j)
  let T : Fin N → ℝ := fun j => blockT (selectedBadOn (B j) x) (h j)
  have hIU : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ I j ∧ I j ≤ U j := by
    intro j hj
    have hI0 : 0 ≤ I j := by
      dsimp [I]
      exact Finset.prod_nonneg (fun p hp => by cases x p <;> simp)
    have hIle : I j ≤ U j := by
      dsimp [I, U]
      rw [← selectedBadOn_avoid_indicator (B j) x]
      exact blockU_ge_avoid (selectedBadOn (B j) x) (hEven j)
    exact ⟨hI0, hIle⟩
  have hUT : ∀ j ∈ (Finset.univ : Finset (Fin N)), U j - I j ≤ T j := by
    intro j hj
    dsimp [I, U, T]
    rw [← selectedBadOn_avoid_indicator (B j) x]
    exact blockU_sub_avoid_le_T (selectedBadOn (B j) x) (hEven j)
  have hunion : (Finset.univ : Finset (Fin N)).biUnion B = P := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
      exact hBsub j hpj
    · intro hp
      rcases hcover p hp with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hpair : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin N))) B := by
    intro j hj k hk hjk
    exact hdisj j k hjk
  have hglobalI : (∏ j, I j) =
      (∏ p ∈ P, if x p then (0 : ℝ) else 1) := by
    dsimp [I]
    calc
      (∏ j, ∏ p ∈ B j, if x p then (0 : ℝ) else 1) =
          ∏ p ∈ (Finset.univ : Finset (Fin N)).biUnion B,
            if x p then (0 : ℝ) else 1 :=
        (Finset.prod_biUnion hpair).symm
      _ = (∏ p ∈ P, if x p then (0 : ℝ) else 1) := by rw [hunion]
  have hUeval := product_blockU_eq_polynomial P B h hBsub hcover hdisj x
  have hLeval := blockLowerProfile_eval_eq P B h hBsub hcover hdisj x
  have htel := product_sub_corrections_le Finset.univ I U T hIU hUT
  constructor
  · rw [hLeval]
    calc
      (∏ j, U j) - ∑ j, T j * ∏ k ∈ Finset.univ.erase j, U k ≤ ∏ j, I j := htel
      _ = (∏ p ∈ P, if x p then (0 : ℝ) else 1) := hglobalI
  · calc
      (∏ p ∈ P, if x p then (0 : ℝ) else 1) = ∏ j, I j := hglobalI.symm
      _ ≤ ∏ j, U j := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact (hIU j hj).1
        · intro j hj
          exact (hIU j hj).2
      _ = ∑ D ∈ P.powerset,
          blockUProfileCoefficient B h D *
            (if D ⊆ selectedBadOn P x then (1 : ℝ) else 0) := by
              simpa [U] using hUeval

/-- Transfer the pointwise Brun--Hooley bracket to weighted sums, with the coefficient error
bounded on a prescribed support. -/
theorem weightedBlockPolynomialBracket {α β : Type*} [DecidableEq β]
    (A : Finset α) (wt : α → ℝ) (P : Finset β)
    (bad : β → α → Prop) (X : ℝ) (g : β → ℝ) (E : Finset β → ℝ)
    (Q : Finset (Finset β)) (cLow cUp : Finset β → ℝ)
    (modelLow modelUp : ℝ)
    (avoid : α → ℝ) (S : ℝ)
    (hS : S = ∑ a ∈ A, wt a * avoid a)
    (hmodelLow : modelLow =
      ∑ D ∈ P.powerset, cLow D * ∏ p ∈ D, g p)
    (hmodelUp : modelUp =
      ∑ D ∈ P.powerset, cUp D * ∏ p ∈ D, g p)
    (hwt : ∀ a ∈ A, 0 ≤ wt a)
    (hA : ∀ D ∈ P.powerset,
      weightedIntersection A wt bad D = X * ∏ p ∈ D, g p + E D)
    (hQ : Q ⊆ P.powerset)
    (hcLow : ∀ D ∈ Q, |cLow D| ≤ 1)
    (hzLow : ∀ D ∈ P.powerset, D ∉ Q → cLow D = 0)
    (hcUp : ∀ D ∈ Q, |cUp D| ≤ 1)
    (hzUp : ∀ D ∈ P.powerset, D ∉ Q → cUp D = 0)
    (hpoint : ∀ a, badPolynomial P bad cLow a ≤ avoid a ∧
      avoid a ≤ badPolynomial P bad cUp a) :
    (X * modelLow - ∑ D ∈ Q, |E D| ≤ S) ∧
      (S ≤ X * modelUp + ∑ D ∈ Q, |E D|) := by
  classical
  let WLow : ℝ := ∑ a ∈ A, wt a * badPolynomial P bad cLow a
  let WUp : ℝ := ∑ a ∈ A, wt a * badPolynomial P bad cUp a
  let err : ℝ := ∑ D ∈ Q, |E D|
  have hlowPoint : (∑ a ∈ A, wt a * badPolynomial P bad cLow a) ≤
      ∑ a ∈ A, wt a * avoid a := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hpoint a).1 (hwt a ha)
  have hupPoint : (∑ a ∈ A, wt a * avoid a) ≤
      ∑ a ∈ A, wt a * badPolynomial P bad cUp a := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hpoint a).2 (hwt a ha)
  have hlowTransfer := weightedPolynomial_main_difference A wt P bad cLow X g E hA
  have hupTransfer := weightedPolynomial_main_difference A wt P bad cUp X g E hA
  have hlowErr := supported_coefficient_error_bound P Q cLow E hQ hcLow hzLow
  have hupErr := supported_coefficient_error_bound P Q cUp E hQ hcUp hzUp
  have hlowAbs : |WLow - X * modelLow| ≤ err := by
    rw [show WLow = ∑ a ∈ A, wt a * badPolynomial P bad cLow a by rfl]
    rw [hmodelLow]
    rw [hlowTransfer]
    exact hlowErr
  have hupAbs : |WUp - X * modelUp| ≤ err := by
    rw [show WUp = ∑ a ∈ A, wt a * badPolynomial P bad cUp a by rfl]
    rw [hmodelUp]
    rw [hupTransfer]
    exact hupErr
  constructor
  · rw [hS]
    have hlow := (abs_le.mp hlowAbs).1
    dsimp [WLow, err] at hlow ⊢
    linarith [hlowPoint]
  · rw [hS]
    have hup := (abs_le.mp hupAbs).2
    dsimp [WUp, err] at hup ⊢
    linarith [hupPoint]

/-- Frozen finite block-sieve statement, with the threshold blocks and Brun--Hooley correction
polynomial. -/
theorem lem_block_aux (η₀ C₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ H₀ : ℕ, ∀ (α : Type) (A : Finset α) (wt : α → ℝ),
      (∀ a ∈ A, 0 ≤ wt a) →
      ∀ (z : ℝ), 2 ≤ z → ∀ (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
      ∀ (bad : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ), 0 ≤ X →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
      (∀ v : ℝ, 1 < v →
        (∑ p ∈ P.filter (fun p : ℕ => v < (p : ℝ) ∧ (p : ℝ) ≤ v ^ 2), g p) ≤ C₀) →
      let S : ℝ := ∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a
      let main : ℝ := X * ∏ p ∈ P, (1 - g p)
      let E : Finset ℕ → ℝ := fun D =>
        (∑ a ∈ A with ∀ p ∈ D, bad p a, wt a) - X * ∏ p ∈ D, g p
      (∀ H : ℕ, Even H → H₀ ≤ H →
        |S - main| ≤ K * Real.exp (-(H : ℝ)) * main +
          K * ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2), |E D|) ∧
      S ≤ K * main + K *
        ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10, |E D| := by
  classical
  let tailConstant : ℝ := Real.exp (3 * C₀ + C₀ / η₀)
  let K : ℝ := 1 + Real.exp (2 * tailConstant) + 6 * tailConstant
  have htailConstant : 0 < tailConstant := by positivity [tailConstant]
  have hK : 0 < K := by positivity [K, tailConstant]
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.log (12 * tailConstant))
  let H₀ : ℕ := n + 1
  have hH₀ : 1 ≤ H₀ := by dsimp [H₀]; omega
  refine ⟨K, hK, H₀, ?_⟩
  intro α A wt hwt z hz P hP bad X g hX hg hLocal
  dsimp only
  let hz1 : 1 < z := by linarith
  let N : ℕ := powerBlockCount P hz1 hP
  let Psub : Finset ↥P := Finset.univ
  let B : Fin N → Finset ↥P := fun j => powerBlock P hz1 hP j.val
  let e : ↥P ↪ ℕ := subtypeValEmbedding P
  let gsub : ↥P → ℝ := fun p => g p.1
  let badsub : ↥P → α → Prop := fun p a => bad p.1 a
  let Esub : Finset ↥P → ℝ := fun D =>
    weightedIntersection A wt badsub D - X * ∏ p ∈ D, gsub p
  let Enat : Finset ℕ → ℝ := fun D =>
    weightedIntersection A wt bad D - X * ∏ p ∈ D, g p
  let degree : ℕ → Fin N → ℕ := fun H j => (j.val + 1) * H
  let avoidanceDensity : Fin N → ℝ := fun j => ∏ p ∈ B j, (1 - gsub p)
  let meanU : ℕ → Fin N → ℝ := fun H j =>
    bernoulliBlockUMeanOn (B j) gsub (degree H j)
  let meanT : ℕ → Fin N → ℝ := fun H j =>
    bernoulliBlockTMeanOn (B j) gsub (degree H j)
  let relativeTail : ℕ → Fin N → ℝ := fun H j =>
    tailConstant / (3 : ℝ) ^ (degree H j + 1)
  have hpart := powerBlocks_partition P hz1 hP
  have hBsub : ∀ j, B j ⊆ Psub := fun j => Finset.subset_univ _
  have hcover : ∀ p ∈ Psub, ∃ j, p ∈ B j := by
    intro p hp
    rcases hpart.1 p with ⟨j, hj⟩
    exact ⟨j, by simpa [B, Psub] using hj⟩
  have hdisj : ∀ j k, j ≠ k → Disjoint (B j) (B k) := by
    intro j k hjk
    exact hpart.2 j k hjk
  have hgsub : ∀ p : ↥P, 0 ≤ gsub p ∧ gsub p ≤ 1 := by
    intro p
    have hp := hg p.1 p.2
    constructor
    · exact hp.1
    · have hη : 0 ≤ η₀ := le_of_lt hη₀
      dsimp [gsub]
      linarith
  have hlocalModel : ∀ H : ℕ, Even H → ∀ j : Fin N,
      0 ≤ avoidanceDensity j ∧
      avoidanceDensity j ≤ meanU H j ∧
      meanU H j ≤ avoidanceDensity j * (1 + relativeTail H j) ∧
      0 ≤ meanT H j ∧
      meanT H j ≤ avoidanceDensity j * relativeTail H j ∧
      0 ≤ relativeTail H j := by
    intro H hEven j
    let m : ℕ := degree H j
    have hEvenM : Even m := by
      rcases hEven with ⟨k, hk⟩
      refine ⟨(j.val + 1) * k, ?_⟩
      dsimp [m, degree]
      rw [hk]
      ring
    have hsum : (∑ p ∈ B j, gsub p) ≤ C₀ :=
      powerBlock_sum_le P hz1 hP j g (fun p hp => (hg p hp).1) C₀ hLocal
    have hmeanBounds := bernoulliBlockOn_bounds (B j) gsub m hEvenM hgsub
    have havoid0 : 0 ≤ avoidanceDensity j := by
      apply Finset.prod_nonneg
      intro p hp
      exact sub_nonneg.mpr (by linarith [(hgsub p).2])
    have hmeanT0 : 0 ≤ meanT H j := by
      dsimp [meanT]
      rw [bernoulliBlockTMeanOn_eq_expansion]
      exact Finset.sum_nonneg (fun D hD =>
        Finset.prod_nonneg (fun p hp => (hgsub p).1))
    have htail0 : 0 ≤ relativeTail H j := by positivity [relativeTail, tailConstant]
    have hrel := bernoulliBlockUMeanOn_le_relative (B j) gsub m hEvenM η₀ C₀ hη₀
      hgsub (fun p hp => (hg p.1 p.2).2) hsum
    have htSymmetric : meanT H j ≤ Real.exp (3 * C₀) / (3 : ℝ) ^ (m + 1) := by
      dsimp [meanT]
      rw [bernoulliBlockTMeanOn_eq_expansion]
      exact elementarySymmetric_le_exp_div_three_pow (B j) gsub (m + 1) C₀
        (fun p hp => (hgsub p).1) hsum
    have haExp : Real.exp (-C₀ / η₀) ≤ avoidanceDensity j := by
      exact avoidanceProduct_ge_exp (B j) gsub η₀ C₀ hη₀
        (fun p hp => ⟨(hgsub p).1, (hg p.1 p.2).2⟩) hsum
    have hmul : Real.exp (-C₀ / η₀) * relativeTail H j =
        Real.exp (3 * C₀) / (3 : ℝ) ^ (m + 1) := by
      dsimp [relativeTail, tailConstant, m]
      calc
        Real.exp (-C₀ / η₀) *
            (Real.exp (3 * C₀ + C₀ / η₀) / (3 : ℝ) ^ (degree H j + 1)) =
            (Real.exp (-C₀ / η₀) * Real.exp (3 * C₀ + C₀ / η₀)) /
              (3 : ℝ) ^ (degree H j + 1) := by ring
        _ = Real.exp ((-C₀ / η₀) + (3 * C₀ + C₀ / η₀)) /
              (3 : ℝ) ^ (degree H j + 1) := by rw [← Real.exp_add]
        _ = Real.exp (3 * C₀) / (3 : ℝ) ^ (degree H j + 1) := by
          congr 1 <;> ring_nf
        _ = Real.exp (3 * C₀) / (3 : ℝ) ^ (m + 1) := by
          simp [m, degree]
    have htRel : meanT H j ≤ avoidanceDensity j * relativeTail H j := by
      calc
        meanT H j ≤ Real.exp (3 * C₀) / (3 : ℝ) ^ (m + 1) := htSymmetric
        _ = Real.exp (-C₀ / η₀) * relativeTail H j := hmul.symm
        _ ≤ avoidanceDensity j * relativeTail H j :=
          mul_le_mul_of_nonneg_right haExp htail0
    have hrel' : meanU H j ≤
        avoidanceDensity j * (1 + relativeTail H j) := by
      simpa [meanU, avoidanceDensity, relativeTail, tailConstant, degree, m] using hrel
    have hUlo : avoidanceDensity j ≤ meanU H j := by
      simpa [meanU, avoidanceDensity, degree, m] using hmeanBounds.1
    exact ⟨havoid0, hUlo, hrel', hmeanT0, htRel, htail0⟩
  have hAvoidGlobal :
      (∏ j, avoidanceDensity j) = ∏ p ∈ P, (1 - g p) := by
    have hunion : (Finset.univ : Finset (Fin N)).biUnion B = Psub := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_biUnion.mp hp with ⟨j, hj, hpj⟩
        exact hBsub j hpj
      · intro hp
        rcases hcover p hp with ⟨j, hj⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
    have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) B := by
      intro j hj k hk hjk
      exact hdisj j k hjk
    have hblockProd : (∏ j, avoidanceDensity j) =
        ∏ p ∈ Psub, (1 - gsub p) := by
      calc
        (∏ j, avoidanceDensity j) =
            ∏ p ∈ (Finset.univ : Finset (Fin N)).biUnion B, (1 - gsub p) := by
              dsimp [avoidanceDensity]
              exact (Finset.prod_biUnion hpair).symm
        _ = ∏ p ∈ Psub, (1 - gsub p) := by rw [hunion]
    calc
      (∏ j, avoidanceDensity j) = ∏ p ∈ Psub, (1 - gsub p) := hblockProd
      _ = ∏ p ∈ P, (1 - g p) := by
        dsimp [Psub, gsub]
        calc
          (∏ p ∈ (Finset.univ : Finset ↥P), (1 - g p.1)) =
              ∏ p ∈ (Finset.univ : Finset ↥P).map e, (1 - g p) :=
            (Finset.prod_map (Finset.univ : Finset ↥P) e
              (fun p : ℕ => 1 - g p)).symm
          _ = ∏ p ∈ P, (1 - g p) := by rw [subtypeVal_map_univ]
  let Svalue : ℝ := ∑ a ∈ A with ∀ p ∈ P, ¬ bad p a, wt a
  let modelUp : ℕ → ℝ := fun H => ∏ j, meanU H j
  let modelLow : ℕ → ℝ := fun H =>
    modelUp H - ∑ j, meanT H j * ∏ k ∈ Finset.univ.erase j, meanU H k
  have hSieveForH (H : ℕ) (hEven : Even H) :
      (X * modelLow H -
        ∑ D ∈ blockCutoffSupportNat P z H, |Enat D| ≤ Svalue) ∧
      (Svalue ≤ X * modelUp H +
        ∑ D ∈ blockCutoffSupportNat P z H, |Enat D|) := by
    classical
    let cUp : Finset ↥P → ℝ := blockUProfileCoefficient B (degree H)
    let cLow : Finset ↥P → ℝ := blockLowerProfileCoefficient B (degree H)
    let Qnat : Finset (Finset ℕ) := blockCutoffSupportNat P z H
    let Qsub : Finset (Finset ↥P) := blockCutoffSupportSubtype P z H
    let avoidValue : α → ℝ := fun a =>
      if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0
    have hQsub : Qsub ⊆ Psub.powerset := by
      intro D hD
      exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hcUp : ∀ D ∈ Qsub, |cUp D| ≤ 1 := by
      intro D hD
      exact blockUProfileCoefficient_abs_le B (degree H) D
    have hcLow : ∀ D ∈ Qsub, |cLow D| ≤ 1 := by
      intro D hD
      exact blockLowerProfileCoefficient_abs_le B (degree H) D
    have hzUp : ∀ D ∈ Psub.powerset, D ∉ Qsub → cUp D = 0 := by
      intro D hD hnot
      have hzero := blockProfileCoefficients_zero_off_cutoff hz hP H D hnot
      simpa [cUp, B, degree, N] using hzero.1
    have hzLow : ∀ D ∈ Psub.powerset, D ∉ Qsub → cLow D = 0 := by
      intro D hD hnot
      have hzero := blockProfileCoefficients_zero_off_cutoff hz hP H D hnot
      simpa [cLow, B, degree, N] using hzero.2
    have hE : ∀ D : Finset ↥P, Esub D = Enat (D.map e) := by
      intro D
      simpa [Esub, Enat, e, gsub, badsub] using
        (subtypeError_eq_map A wt P bad X g D)
    have hQnat : Qnat ⊆ P.powerset := Finset.filter_subset _ _
    have hErrMap :
        (∑ D ∈ Qsub, |Esub D|) = ∑ D ∈ Qnat, |Enat D| := by
      simpa [Qsub, Qnat, blockCutoffSupportSubtype, blockCutoffSupportNat, e] using
        (sum_subtype_support_errors_eq (α := α) P Qnat hQnat Esub Enat hE)
    have hA : ∀ D ∈ Psub.powerset,
        weightedIntersection A wt badsub D =
          X * ∏ p ∈ D, gsub p + Esub D := by
      intro D hD
      dsimp [Esub]
      ring
    have huExp (j : Fin N) :
        bernoulliBlockUExpansionOn (B j) gsub (degree H j) = meanU H j := by
      dsimp [meanU]
      exact (bernoulliBlockUMeanOn_eq_expansion (B j) gsub (degree H j)).symm
    have htExp (j : Fin N) :
        bernoulliBlockTExpansionOn (B j) gsub (degree H j) = meanT H j := by
      dsimp [meanT]
      exact (bernoulliBlockTMeanOn_eq_expansion (B j) gsub (degree H j)).symm
    have hmodelUpCoeff :
        (∑ D ∈ Psub.powerset, cUp D * ∏ p ∈ D, gsub p) = modelUp H := by
      have h := blockUProfile_main_eq Psub B (degree H) hBsub hcover hdisj gsub
      calc
        (∑ D ∈ Psub.powerset, cUp D * ∏ p ∈ D, gsub p) =
            ∏ j, bernoulliBlockUExpansionOn (B j) gsub (degree H j) := by
              simpa [cUp] using h
        _ = modelUp H := by
          dsimp [modelUp]
          apply Finset.prod_congr rfl
          intro j hj
          exact huExp j
    have hmodelLowCoeff :
        (∑ D ∈ Psub.powerset, cLow D * ∏ p ∈ D, gsub p) = modelLow H := by
      have h := blockLowerProfile_main_eq Psub B (degree H) hBsub hcover hdisj gsub
      calc
        (∑ D ∈ Psub.powerset, cLow D * ∏ p ∈ D, gsub p) =
            (∏ k, bernoulliBlockUExpansionOn (B k) gsub (degree H k)) -
              ∑ j, bernoulliBlockTExpansionOn (B j) gsub (degree H j) *
                ∏ k ∈ Finset.univ.erase j,
                  bernoulliBlockUExpansionOn (B k) gsub (degree H k) := by
                    simpa [cLow] using h
        _ = modelLow H := by
          dsimp [modelLow, modelUp]
          congr 1
          · apply Finset.prod_congr rfl
            intro k hk
            exact huExp k
          · apply Finset.sum_congr rfl
            intro j hj
            rw [htExp j]
            congr 1
            apply Finset.prod_congr rfl
            intro k hk
            exact huExp k
    have hmainU :
        (∑ D ∈ Psub.powerset, cUp D * ∏ p ∈ D, gsub p) = modelUp H := by
      have h := blockUProfile_main_eq Psub B (degree H) hBsub hcover hdisj gsub
      calc
        (∑ D ∈ Psub.powerset, cUp D * ∏ p ∈ D, gsub p) =
            ∏ j, bernoulliBlockUExpansionOn (B j) gsub (degree H j) := by
              simpa [cUp] using h
        _ = modelUp H := by
          apply Finset.prod_congr rfl
          intro j hj
          dsimp [modelUp, meanU]
          exact (bernoulliBlockUMeanOn_eq_expansion (B j) gsub (degree H j)).symm
    have hmainLow :
        (∑ D ∈ Psub.powerset, cLow D * ∏ p ∈ D, gsub p) = modelLow H := by
      have h := blockLowerProfile_main_eq Psub B (degree H) hBsub hcover hdisj gsub
      have hUexp (j : Fin N) :
          bernoulliBlockUExpansionOn (B j) gsub (degree H j) = meanU H j := by
        dsimp [meanU]
        exact (bernoulliBlockUMeanOn_eq_expansion (B j) gsub (degree H j)).symm
      have hTexp (j : Fin N) :
          bernoulliBlockTExpansionOn (B j) gsub (degree H j) = meanT H j := by
        dsimp [meanT]
        exact (bernoulliBlockTMeanOn_eq_expansion (B j) gsub (degree H j)).symm
      calc
        (∑ D ∈ Psub.powerset, cLow D * ∏ p ∈ D, gsub p) =
            (∏ k, bernoulliBlockUExpansionOn (B k) gsub (degree H k)) -
              ∑ j, bernoulliBlockTExpansionOn (B j) gsub (degree H j) *
                ∏ k ∈ Finset.univ.erase j,
                  bernoulliBlockUExpansionOn (B k) gsub (degree H k) := by
                simpa [cLow] using h
        _ = modelLow H := by
          dsimp [modelLow, modelUp]
          congr 1
          · apply Finset.prod_congr rfl
            intro k hk
            exact hUexp k
          · apply Finset.sum_congr rfl
            intro j hj
            rw [hTexp j]
            congr 1
            apply Finset.prod_congr rfl
            intro k hk
            exact hUexp k
    have hpoint : ∀ a : α,
        badPolynomial Psub badsub cLow a ≤ avoidValue a ∧
          avoidValue a ≤ badPolynomial Psub badsub cUp a := by
      intro a
      let x : ↥P → Bool := fun p => if badsub p a then true else false
      letI : DecidablePred (fun D : Finset ↥P => ∀ p ∈ D, badsub p a) :=
        fun D => Finset.decidableDforallFinset
      have hx (p : ↥P) : x p = true ↔ badsub p a := by
        simp [x]
      have hiff (D : Finset ↥P) :
          (∀ p ∈ D, badsub p a) ↔ D ⊆ selectedBadOn Psub x := by
        constructor
        · intro hbad p hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hx p).2 (hbad p hp)⟩
        · intro hselected p hp
          exact (hx p).1 (Finset.mem_filter.mp (hselected hp)).2
      have hInd (D : Finset ↥P) := by
        show (if ∀ p ∈ D, badsub p a then (1 : ℝ) else 0) =
          (if D ⊆ selectedBadOn Psub x then (1 : ℝ) else 0)
        by_cases hb : ∀ p ∈ D, badsub p a
        · have hs := (hiff D).mp hb
          rw [if_pos hb, if_pos hs]
        · have hs : ¬ D ⊆ selectedBadOn Psub x := fun hs => hb ((hiff D).mpr hs)
          rw [if_neg hb, if_neg hs]
      have hpolyLow : badPolynomial Psub badsub cLow a ≤
          (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) := by
        unfold badPolynomial
        calc
          (∑ D ∈ Psub.powerset,
            cLow D * (if ∀ p ∈ D, badsub p a then (1 : ℝ) else 0)) =
              ∑ D ∈ Psub.powerset,
                cLow D * (if D ⊆ selectedBadOn Psub x then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro D hD
                  rw [hInd D]
          _ ≤ (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) :=
            (blockPolynomialPointwiseBracket Psub B (degree H) hBsub hcover hdisj
              (by
                intro j
                rcases hEven with ⟨k, hk⟩
                refine ⟨(j.val + 1) * k, ?_⟩
                dsimp [degree]
                rw [hk]
                ring) x).1
      have hpolyUp : (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) ≤
          badPolynomial Psub badsub cUp a := by
        unfold badPolynomial
        calc
          (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) ≤
              ∑ D ∈ Psub.powerset,
                cUp D * (if D ⊆ selectedBadOn Psub x then (1 : ℝ) else 0) :=
            (blockPolynomialPointwiseBracket Psub B (degree H) hBsub hcover hdisj
              (by
                intro j
                rcases hEven with ⟨k, hk⟩
                refine ⟨(j.val + 1) * k, ?_⟩
                dsimp [degree]
                rw [hk]
                ring) x).2
          _ = ∑ D ∈ Psub.powerset,
                cUp D * (if ∀ p ∈ D, badsub p a then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro D hD
                  rw [← hInd D]
      have hSelectedEq : selectedBadOn Psub x =
          Psub.filter (fun p => badsub p a) := by
        ext p
        simp [selectedBadOn, hx]
      have hNoCard : (∀ p ∈ Psub, ¬ badsub p a) ↔
          (selectedBadOn Psub x).card = 0 := by
        rw [hSelectedEq]
        simp only [Finset.card_eq_zero]
        constructor
        · intro hno
          ext p
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hp, hbad⟩
            exact False.elim ((hno p hp) hbad)
          · intro hp
            exact False.elim (by simpa using hp)
        · intro hempty p hp hbad
          have hmem : p ∈ Psub.filter (fun p => badsub p a) :=
            Finset.mem_filter.mpr ⟨hp, hbad⟩
          rw [hempty] at hmem
          simpa using hmem
      have hAvoidEq : (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) =
          (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0) := by
        calc
          (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) =
              (if (selectedBadOn Psub x).card = 0 then (1 : ℝ) else 0) :=
            (selectedBadOn_avoid_indicator Psub x).symm
          _ = (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0) := by
            by_cases hz0 : (selectedBadOn Psub x).card = 0
            · have hno := hNoCard.mpr hz0
              rw [if_pos hz0, if_pos hno]
            · have hnot : ¬ ∀ p ∈ Psub, ¬ badsub p a := fun hno =>
                hz0 (hNoCard.mp hno)
              rw [if_neg hz0, if_neg hnot]
      constructor
      · change badPolynomial Psub badsub cLow a ≤
          (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0)
        calc
          badPolynomial Psub badsub cLow a ≤
              (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) := hpolyLow
          _ = (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0) := hAvoidEq
      · change (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0) ≤
          badPolynomial Psub badsub cUp a
        calc
          (if ∀ p ∈ Psub, ¬ badsub p a then (1 : ℝ) else 0) =
              (∏ p ∈ Psub, if x p then (0 : ℝ) else 1) := hAvoidEq.symm
          _ ≤ badPolynomial Psub badsub cUp a := hpolyUp
    have hSbridge :
        (∑ a ∈ A with ∀ p ∈ Psub, ¬ badsub p a, wt a) = Svalue := by
      have halliff (a : α) :
          (∀ p ∈ Psub, ¬ badsub p a) ↔ ∀ p ∈ P, ¬ bad p a := by
        constructor
        · intro hno p hp
          simpa [badsub] using hno ⟨p, hp⟩ (by simp [Psub])
        · intro hno p hp
          exact hno p.1 p.2
      dsimp [Svalue]
      have hFiltered :
          A.filter (fun a => ∀ p ∈ Psub, ¬ badsub p a) =
            A.filter (fun a => ∀ p ∈ P, ¬ bad p a) := by
        ext a
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨ha, hno⟩
          exact ⟨ha, (halliff a).mp hno⟩
        · rintro ⟨ha, hno⟩
          exact ⟨ha, (halliff a).mpr hno⟩
      rw [hFiltered]
    have hFilterAvoid :
        (∑ a ∈ A with ∀ p ∈ Psub, ¬ badsub p a, wt a) =
          ∑ a ∈ A, wt a * avoidValue a := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      change (if ∀ p ∈ Psub, ¬ badsub p a then wt a else 0) =
        wt a * avoidValue a
      by_cases hno : ∀ p ∈ Psub, ¬ badsub p a <;> simp [avoidValue, hno]
    have hSsum : Svalue = ∑ a ∈ A, wt a * avoidValue a :=
      hSbridge.symm.trans hFilterAvoid
    have hbracket := weightedBlockPolynomialBracket A wt Psub badsub X gsub Esub
      Qsub cLow cUp (modelLow H) (modelUp H) avoidValue Svalue hSsum
      hmodelLowCoeff.symm hmodelUpCoeff.symm
      hwt hA hQsub hcLow hzLow hcUp hzUp hpoint
    rw [hErrMap] at hbracket
    exact hbracket
  have hRtail : ∀ H : ℕ, 1 ≤ H →
      (∑ j : Fin N, relativeTail H j) ≤
        2 * tailConstant * Real.exp (-(H : ℝ)) := by
    intro H hH
    calc
      (∑ j : Fin N, relativeTail H j) =
          ∑ j ∈ Finset.range N,
            tailConstant / (3 : ℝ) ^ ((j + 1) * H + 1) := by
              exact Fin.sum_univ_eq_sum_range
                (fun j : ℕ => tailConstant / (3 : ℝ) ^ ((j + 1) * H + 1)) N
      _ ≤ 2 * tailConstant * Real.exp (-(H : ℝ)) :=
        sum_block_relative_tail hH tailConstant (le_of_lt htailConstant)
  have hsmallExp : ∀ H : ℕ, H₀ ≤ H →
      2 * tailConstant * Real.exp (-(H : ℝ)) ≤ 1 / 6 := by
    intro H hH
    have hnH : (n : ℝ) < (H : ℝ) := by
      have hNat : n < H := by dsimp [H₀] at hH; omega
      exact_mod_cast hNat
    have hlogH : Real.log (12 * tailConstant) < (H : ℝ) := lt_trans hn hnH
    have hExpTail : Real.exp (-(H : ℝ)) ≤
        Real.exp (-(Real.log (12 * tailConstant))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hExpLog : Real.exp (-(Real.log (12 * tailConstant))) =
        (12 * tailConstant)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 12 * tailConstant)]
    calc
      2 * tailConstant * Real.exp (-(H : ℝ)) ≤
          2 * tailConstant * Real.exp (-(Real.log (12 * tailConstant))) :=
        mul_le_mul_of_nonneg_left hExpTail (by positivity)
      _ = 1 / 6 := by rw [hExpLog]; field_simp; ring
  have hExpOne : Real.exp 1 ≤ 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := 1) (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hKone : 1 ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (2 * tailConstant), htailConstant]
  have hKfour : 4 * tailConstant ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (2 * tailConstant)]
  have hKsix : 6 * tailConstant ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (2 * tailConstant)]
  have hKexp : Real.exp (2 * tailConstant) ≤ K := by
    dsimp [K]
    linarith [Real.exp_pos (2 * tailConstant)]
  constructor
  · intro H hEven hH
    have hHpos : 1 ≤ H := le_trans hH₀ hH
    let R : ℝ := ∑ j : Fin N, relativeTail H j
    let Dprod : ℝ := ∏ j, avoidanceDensity j
    let M : ℝ := X * Dprod
    let err : ℝ := ∑ D ∈ blockCutoffSupportNat P z H, |Enat D|
    have hSupportEq : blockCutoffSupportNat P z H =
        P.powerset.filter (fun D =>
          ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2)) := by
      unfold blockCutoffSupportNat
      ext D
      simp [Nat.cast_mul, Nat.cast_add]
    have hErrEq : err =
        ∑ D ∈ P.powerset.filter (fun D =>
          ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * H + 2)), |Enat D| := by
      dsimp [err]
      rw [hSupportEq]
    have hRnonneg : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg (fun j hj => (hlocalModel H hEven j).2.2.2.2.2)
    have hRbound : R ≤ 1 / 6 := by
      calc
        R ≤ 2 * tailConstant * Real.exp (-(H : ℝ)) := by
          exact hRtail H hHpos
        _ ≤ 1 / 6 := hsmallExp H hH
    have hRle1 : R ≤ 1 := by linarith
    have hmodelEst := product_local_model_estimates
      avoidanceDensity (meanU H) (meanT H) (relativeTail H)
      (hlocalModel H hEven) hRle1
    have hExpR : Real.exp R ≤ 3 := by
      calc
        Real.exp R ≤ Real.exp 1 := Real.exp_le_exp.mpr hRle1
        _ ≤ 3 := hExpOne
    have hRExp : R * Real.exp R ≤
        6 * tailConstant * Real.exp (-(H : ℝ)) := by
      calc
        R * Real.exp R ≤ R * 3 := mul_le_mul_of_nonneg_left hExpR hRnonneg
        _ ≤ (2 * tailConstant * Real.exp (-(H : ℝ))) * 3 :=
          mul_le_mul_of_nonneg_right (hRtail H hHpos) (by norm_num)
        _ = 6 * tailConstant * Real.exp (-(H : ℝ)) := by ring
    have hDprod0 : 0 ≤ Dprod := by
      dsimp [Dprod]
      exact Finset.prod_nonneg (fun j hj => (hlocalModel H hEven j).1)
    have hDprodEq : Dprod = ∏ p ∈ P, (1 - g p) := by
      exact hAvoidGlobal
    have hModelUp : modelUp H ≤ Dprod *
        (1 + 4 * tailConstant * Real.exp (-(H : ℝ))) := by
      have hsmall := hmodelEst.1
      dsimp [modelUp, Dprod, R] at hsmall ⊢
      calc
        (∏ j, meanU H j) ≤ (∏ j, avoidanceDensity j) * (1 + 2 * R) := hsmall
        _ ≤ (∏ j, avoidanceDensity j) *
              (1 + 4 * tailConstant * Real.exp (-(H : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hDprod0
          have := hRtail H hHpos
          linarith
    have hModelLow : Dprod *
        (1 - 6 * tailConstant * Real.exp (-(H : ℝ))) ≤ modelLow H := by
      have hlower := hmodelEst.2
      have hcoeff :
          Dprod * (1 - 6 * tailConstant * Real.exp (-(H : ℝ))) ≤
            Dprod * (1 - R * Real.exp R) := by
        apply mul_le_mul_of_nonneg_left _ hDprod0
        linarith
      calc
        Dprod * (1 - 6 * tailConstant * Real.exp (-(H : ℝ))) ≤
            Dprod * (1 - R * Real.exp R) := hcoeff
        _ ≤ modelLow H := by
          simpa [modelLow, modelUp, Dprod] using hlower
    have hM0 : 0 ≤ M := mul_nonneg hX hDprod0
    have herr0 : 0 ≤ err := by
      dsimp [err]
      exact Finset.sum_nonneg (fun D hD => abs_nonneg _)
    have he0 : 0 ≤ Real.exp (-(H : ℝ)) := (Real.exp_pos _).le
    have hsieve := hSieveForH H hEven
    rcases hsieve with ⟨hlowS, hupS⟩
    have hupS' : Svalue ≤ X *
        (Dprod * (1 + 4 * tailConstant * Real.exp (-(H : ℝ)))) + err := by
      calc
        Svalue ≤ X * modelUp H + err := hupS
        _ ≤ X * (Dprod *
              (1 + 4 * tailConstant * Real.exp (-(H : ℝ)))) + err :=
          by simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hModelUp hX) err
    have hUpperDiff : Svalue - M ≤
        4 * tailConstant * Real.exp (-(H : ℝ)) * M + err := by
      calc
        Svalue - M ≤ X *
            (Dprod * (1 + 4 * tailConstant * Real.exp (-(H : ℝ)))) + err - M :=
          sub_le_sub_right hupS' M
        _ = 4 * tailConstant * Real.exp (-(H : ℝ)) * M + err := by
          dsimp [M]
          ring
    have hLowS' : M -
        6 * tailConstant * Real.exp (-(H : ℝ)) * M - err ≤ Svalue := by
      calc
        M - 6 * tailConstant * Real.exp (-(H : ℝ)) * M - err =
            X * (Dprod * (1 - 6 * tailConstant * Real.exp (-(H : ℝ)))) - err := by
              dsimp [M]
              ring
        _ ≤ X * modelLow H - err := by
          exact sub_le_sub_right (mul_le_mul_of_nonneg_left hModelLow hX) err
        _ ≤ Svalue := hlowS
    have hLowerDiff : M - Svalue ≤
        6 * tailConstant * Real.exp (-(H : ℝ)) * M + err := by
      linarith [hLowS']
    have hq0 : 0 ≤ Real.exp (-(H : ℝ)) * M := mul_nonneg he0 hM0
    have hupperCoeff :
        4 * tailConstant * Real.exp (-(H : ℝ)) * M + err ≤
          K * Real.exp (-(H : ℝ)) * M + K * err := by
      calc
        4 * tailConstant * Real.exp (-(H : ℝ)) * M + err =
            (4 * tailConstant) * (Real.exp (-(H : ℝ)) * M) + err := by ring
        _ ≤ K * (Real.exp (-(H : ℝ)) * M) + K * err :=
          add_le_add (mul_le_mul_of_nonneg_right hKfour hq0)
            (by simpa using mul_le_mul_of_nonneg_right hKone herr0)
        _ = K * Real.exp (-(H : ℝ)) * M + K * err := by ring
    have hlowerCoeff :
        6 * tailConstant * Real.exp (-(H : ℝ)) * M + err ≤
          K * Real.exp (-(H : ℝ)) * M + K * err := by
      calc
        6 * tailConstant * Real.exp (-(H : ℝ)) * M + err =
            (6 * tailConstant) * (Real.exp (-(H : ℝ)) * M) + err := by ring
        _ ≤ K * (Real.exp (-(H : ℝ)) * M) + K * err :=
          add_le_add (mul_le_mul_of_nonneg_right hKsix hq0)
            (by simpa using mul_le_mul_of_nonneg_right hKone herr0)
        _ = K * Real.exp (-(H : ℝ)) * M + K * err := by ring
    have hAbs : |Svalue - M| ≤
        K * Real.exp (-(H : ℝ)) * M + K * err := by
      apply abs_le.mpr
      constructor <;> linarith [hUpperDiff, hLowerDiff, hupperCoeff, hlowerCoeff]
    dsimp only [M] at hAbs
    rw [hDprodEq] at hAbs
    rw [hErrEq] at hAbs
    simpa [Svalue, Enat, weightedIntersection, K,
      blockCutoffSupportNat, Nat.cast_mul, Nat.cast_add] using hAbs
  · let dprod : ℝ := ∏ p ∈ P, (1 - g p)
    let M : ℝ := X * dprod
    let err : ℝ := ∑ D ∈ blockCutoffSupportNat P z 2, |Enat D|
    have hSupport10 : blockCutoffSupportNat P z 2 =
        P.powerset.filter (fun D =>
          ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10) := by
      unfold blockCutoffSupportNat
      ext D
      norm_num
    have hErr10 : err =
        ∑ D ∈ P.powerset.filter (fun D =>
          ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10), |Enat D| := by
      dsimp [err]
      rw [hSupport10]
    have hEven2 : Even (2 : ℕ) := ⟨1, by norm_num⟩
    have hR2 : (∑ j : Fin N, relativeTail 2 j) ≤ 2 * tailConstant := by
      calc
        (∑ j : Fin N, relativeTail 2 j) ≤
            2 * tailConstant * Real.exp (-(2 : ℝ)) := hRtail 2 (by norm_num)
        _ ≤ 2 * tailConstant := by
          have hexpNeg : Real.exp (-(2 : ℝ)) ≤ 1 := by
            rw [Real.exp_neg]
            have hExpTwo : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp (by norm_num)
            simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hExpTwo)
          have htailNonneg : 0 ≤ 2 * tailConstant := by positivity
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hexpNeg htailNonneg
    have hmodelUp2 : modelUp 2 ≤ dprod * Real.exp (2 * tailConstant) := by
      have hlocal := hlocalModel 2 hEven2
      have hUpper :
          (∏ j : Fin N, meanU 2 j) ≤
            (∏ j : Fin N, avoidanceDensity j) *
              Real.exp (∑ j : Fin N, relativeTail 2 j) := by
        exact product_local_model_upper_exp
          avoidanceDensity (meanU 2) (relativeTail 2)
          (fun j => ⟨hlocal j |>.1, hlocal j |>.2.1, hlocal j |>.2.2.1,
            hlocal j |>.2.2.2.2.2⟩)
      have hRexp : Real.exp (∑ j : Fin N, relativeTail 2 j) ≤
          Real.exp (2 * tailConstant) :=
        Real.exp_le_exp.mpr hR2
      have hD0 : 0 ≤ dprod := by
        dsimp [dprod]
        exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (by linarith [(hg p hp).2]))
      calc
        modelUp 2 = ∏ j : Fin N, meanU 2 j := rfl
        _ ≤ (∏ j : Fin N, avoidanceDensity j) *
            Real.exp (∑ j : Fin N, relativeTail 2 j) := hUpper
        _ ≤ (∏ j, avoidanceDensity j) * Real.exp (2 * tailConstant) :=
          mul_le_mul_of_nonneg_left hRexp (by
            exact Finset.prod_nonneg (fun j hj => (hlocalModel 2 hEven2 j).1))
        _ = dprod * Real.exp (2 * tailConstant) := by rw [hAvoidGlobal]
    have hM0 : 0 ≤ M := by
      dsimp [M]
      exact mul_nonneg hX (Finset.prod_nonneg (fun p hp =>
        sub_nonneg.mpr (by linarith [(hg p hp).2])))
    have herr0 : 0 ≤ err := by
      dsimp [err]
      exact Finset.sum_nonneg (fun D hD => abs_nonneg _)
    have hsieve := hSieveForH 2 hEven2
    rcases hsieve with ⟨hlowS, hupS⟩
    have hUpS' : Svalue ≤ X * (dprod * Real.exp (2 * tailConstant)) + err := by
      calc
        Svalue ≤ X * modelUp 2 + err := hupS
        _ ≤ X * (dprod * Real.exp (2 * tailConstant)) + err :=
          by simpa [add_comm] using
            add_le_add_right (mul_le_mul_of_nonneg_left hmodelUp2 hX) err
    have hModelDom : X * (dprod * Real.exp (2 * tailConstant)) ≤ K * M := by
      calc
        X * (dprod * Real.exp (2 * tailConstant)) = M * Real.exp (2 * tailConstant) := by
          dsimp [M]
          ring
        _ ≤ M * K := mul_le_mul_of_nonneg_left hKexp hM0
        _ = K * M := by ring
    have hErrDom : err ≤ K * err := by
      calc
        err = 1 * err := by ring
        _ ≤ K * err := mul_le_mul_of_nonneg_right hKone herr0
    have hFinal : Svalue ≤ K * M + K * err := by
      calc
        Svalue ≤ X * (dprod * Real.exp (2 * tailConstant)) + err := hUpS'
        _ ≤ K * M + K * err := add_le_add hModelDom hErrDom
    rw [hErr10] at hFinal
    simpa [Svalue, M, dprod, Enat, weightedIntersection, K] using hFinal

end ArtinPrimitiveRoots.Sieve
