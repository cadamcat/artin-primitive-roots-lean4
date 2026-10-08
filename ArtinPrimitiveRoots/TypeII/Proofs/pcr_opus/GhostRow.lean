import ArtinPrimitiveRoots.TypeII.Proofs.pcr_opus.Triangular
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».BatchSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».DeletionSupport
import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».SignSupport

/-! Positive ghost choice rows with prescribed births (guide
`runs/lanes/sol-thin-pd5/PROOFS.md:151–243`). Ported from the checked pd5-lead drafts. -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

abbrev PCRGhostCoordinate (K : ℕ) (l : Fin K → ℕ) := (i : Fin K) × Fin (l i)

def pcr_ghostCoordinateAddress {K : ℕ} (j : ℕ) (l : Fin K → ℕ)
    (a : PCRGhostCoordinate K l) : BirthAddress K := .ghost j a.1 a.2.val

theorem pcr_ghostCoordinateAddress_injective {K : ℕ} (j : ℕ) (l : Fin K → ℕ) :
    Function.Injective (pcr_ghostCoordinateAddress j l) := by
  intro a b h
  rcases a with ⟨i, k⟩
  rcases b with ⟨i', k'⟩
  simp [pcr_ghostCoordinateAddress] at h
  have hi : i = i' := h.1
  cases hi
  have hk : k = k' := Fin.ext h.2
  cases hk
  rfl

theorem pcr_ghostCoordinateKey_injective {K : ℕ} (S : PDScale) (B j : ℕ)
    (l : Fin K → ℕ) (hl : ∀ i, l i ≤ B) :
    Function.Injective (fun a : PCRGhostCoordinate K l =>
      pd5_birthIndex S B (pcr_ghostCoordinateAddress j l a)) := by
  let T := max (slotCount S.x) B + 1
  have hT : 0 < T := Nat.succ_pos _
  have hdiv (a k : ℕ) (hk : k < T) : (a * T + k) / T = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right k a hT, Nat.div_eq_of_lt hk]
    simp
  intro a b he
  rcases a with ⟨i, k⟩
  rcases b with ⟨i', k'⟩
  have hk : k.val < T := lt_of_lt_of_le k.isLt (by dsimp [T]; exact le_trans (hl i) (by omega))
  have hk' : k'.val < T := lt_of_lt_of_le k'.isLt (by dsimp [T]; exact le_trans (hl i') (by omega))
  change (((2 * j + 1) * K + i.val) * T + k.val) =
    (((2 * j + 1) * K + i'.val) * T + k'.val) at he
  have hd := congrArg (fun n : ℕ => n / T) he
  rw [hdiv _ _ hk, hdiv _ _ hk'] at hd
  have hm := congrArg (fun n : ℕ => n % T) he
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at hm
  have hi : i = i' := Fin.ext (by omega)
  cases hi
  have hkEq : k = k' := Fin.ext hm
  cases hkEq
  rfl

noncomputable def pcr_ghostCoordinateList (K : ℕ) (l : Fin K → ℕ) : List (PCRGhostCoordinate K l) :=
  (List.finRange K).flatMap fun i => (List.finRange (l i)).map fun k => ⟨i, k⟩

theorem pcr_ghostCoordinateList_mem {K : ℕ} (l : Fin K → ℕ)
    (a : PCRGhostCoordinate K l) : a ∈ pcr_ghostCoordinateList K l := by
  rcases a with ⟨i, k⟩
  unfold pcr_ghostCoordinateList
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩

theorem pcr_ghostCoordinateList_map_address {K : ℕ} (j : ℕ) (l : Fin K → ℕ) :
    (pcr_ghostCoordinateList K l).map (pcr_ghostCoordinateAddress j l) =
      pd5_ghostAddressList j l := by
  simp [pcr_ghostCoordinateList, pcr_ghostCoordinateAddress, pd5_ghostAddressList,
    List.ofFn_eq_map, List.map_flatMap, List.map_map, Function.comp_def]

theorem pcr_ghostCoordinateList_nodup {K : ℕ} (l : Fin K → ℕ) :
    (pcr_ghostCoordinateList K l).Nodup := by
  apply List.Nodup.of_map (pcr_ghostCoordinateAddress 0 l)
  rw [pcr_ghostCoordinateList_map_address]
  exact pd5_ghostAddressList_nodup 0 l

theorem pcr_ghostCoordinateList_birthLog {K : ℕ} (j : ℕ) (l : Fin K → ℕ)
    (p : (i : Fin K) → Fin (l i) → ℕ) :
    (pcr_ghostCoordinateList K l).map (fun a => (pcr_ghostCoordinateAddress j l a, p a.1 a.2)) =
      pd5_ghostBirthLog j l p := by
  simp [pcr_ghostCoordinateList, pcr_ghostCoordinateAddress, pd5_ghostBirthLog,
    List.ofFn_eq_map, List.map_flatMap, List.map_map, Function.comp_def]


/-- One group's indexed deletion and creation balance, with the actual v weight. -/
theorem pcr_weighted_ghost_group (η q V ρ v b : ℝ)
    (hη : 0 ≤ η) (hq : 0 ≤ q) (hV : 0 ≤ V) (hρ : 0 < ρ) (hv : 0 < v) (hb : 0 ≤ b)
    (n h d l nout : ℕ) (hd : d ≤ h) (hbal : nout + d = n + l) :
    |(-η / ρ) ^ d * (q / ρ ^ 2) ^ (h - d) * (-η * V / ρ) ^ l / (l.factorial : ℝ) * b| *
      v ^ nout =
        v ^ n * (η / (ρ * v)) ^ d * (q / ρ ^ 2) ^ (h - d) *
          (v * η * V / ρ) ^ l / (l.factorial : ℝ) * b := by
  let A : ℝ := (η / ρ) ^ d * (q / ρ ^ 2) ^ (h - d) * (η * V / ρ) ^ l /
    (l.factorial : ℝ) * b
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs : (-η / ρ) ^ d * (q / ρ ^ 2) ^ (h - d) * (-η * V / ρ) ^ l /
      (l.factorial : ℝ) * b = (-1 : ℝ) ^ (d + l) * A := by
    dsimp [A]
    rw [neg_div, neg_mul, neg_div, neg_pow, neg_pow, pow_add]
    ring
  rw [hs]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hA]
  have hpow : v ^ nout = v ^ n * v ^ l / v ^ d := by
    apply (eq_div_iff (pow_ne_zero _ hv.ne')).2
    simpa only [pow_add] using congrArg (fun k : ℕ => v ^ k) hbal
  have hdel : (η / (ρ * v)) ^ d = (η / ρ) ^ d / v ^ d := by
    rw [div_pow, mul_pow, div_pow]
    field_simp
  have hborn : (v * η * V / ρ) ^ l = v ^ l * (η * V / ρ) ^ l := by
    have he : v * η * V / ρ = v * (η * V / ρ) := by ring
    rw [he, mul_pow]
  rw [hpow, hdel, hborn]
  dsimp [A]
  ring


/-- A fixed ragged ghost batch with any prefix-dependent prescription costs Δ per named
nonpivot, regardless of which named indices are missing. Free coordinate mass is at most two. -/
theorem pcr_ghost_batch_prescribed_atoms {K : ℕ} (F : PDFix K) (S : PDScale)
    (B j : ℕ) (l : Fin K → ℕ) (hl : ∀ i, l i ≤ B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2)
    (hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ) :
    (∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
      pd5_prescribedWeight S B U R pick pastLog (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
        ∏ i : Fin K, ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k)) ≤
      Δ ^ R.card * (2 : ℝ) ^ (∑ i : Fin K, l i) := by
  let α := PCRGhostCoordinate K l
  let address : α → BirthAddress K := pcr_ghostCoordinateAddress j l
  let key : α → ℕ := fun a => pd5_birthIndex S B (address a)
  letI : LinearOrder α := LinearOrder.lift' key (pcr_ghostCoordinateKey_injective S B j l hl)
  letI : DecidableEq α := LinearOrder.toDecidableEq
  let L : List α := pcr_ghostCoordinateList K l
  let P : α → Finset ℕ := fun a => primeBand S.x (F.a a.1)
  let ν : α → ℕ → ℝ := fun a p => memoryNu S.x K F.a F.q_d a.1 p
  let e := Equiv.piCurry (fun (i : Fin K) (_k : Fin (l i)) => primeBand S.x (F.a i))
  let wt (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : ℝ :=
    pd5_prescribedWeight S B U R pick pastLog (pd5_ghostBirthLog j l (fun i k => (new i k : ℕ))) *
      ∏ i : Fin K, ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k)
  have heq (b : (a : α) → {p : ℕ // p ∈ P a}) : wt (e b) =
      pd5_prescribedWeight S B U R pick pastLog
        (pcr_coordinateLog L address (fun a => (b a : ℕ))) * ∏ a : α, ν a (b a) := by
    have hlog : pd5_ghostBirthLog j l (fun i k => (e b i k : ℕ)) =
        pcr_coordinateLog L address (fun a => (b a : ℕ)) := by
      simpa [pcr_coordinateLog, e, L, address, Sigma.curry, Sigma.eta] using
        (pcr_ghostCoordinateList_birthLog j l (fun i k => (b ⟨i, k⟩ : ℕ))).symm
    dsimp only [wt]
    rw [hlog]
    congr 1
    rw [Fintype.prod_sigma]
    rfl
  have h := pcr_prescribed_product_uniform_atom S B L
    (pcr_ghostCoordinateList_nodup l) (pcr_ghostCoordinateList_mem l) address
    (pcr_ghostCoordinateAddress_injective j l) (fun a b => Iff.rfl) P ν U R hRU Δ 2 hΔ
    (by norm_num) pick pastLog (fun a p hp => hν a.1 p hp) (fun a => hmass a.1)
    (fun a ha p hp => hatom a.1 p hp)
  calc
    _ = ∑ b : (a : α) → {p : ℕ // p ∈ P a}, wt (e b) := (e.sum_comp wt).symm
    _ = ∑ b : (a : α) → {p : ℕ // p ∈ P a},
        pd5_prescribedWeight S B U R pick pastLog
          (pcr_coordinateLog L address (fun a => (b a : ℕ))) * ∏ a : α, ν a (b a) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact heq b
    _ ≤ Δ ^ R.card * (2 : ℝ) ^ Fintype.card α := h
    _ = _ := by simp [α, PCRGhostCoordinate, Fintype.card_sigma]


noncomputable def pcr_ghostDeleteFactor {K : ℕ} (F : PDFix K) (S : PDScale) (ρ v : ℝ)
    (j : ℕ) (s : MemPoint S.x K) (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (i : Fin K) : ℝ :=
  (memoryEta S.x F.q_d j / (ρ * v)) ^ (D i).card *
    (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hitCount (s.2.2 i) s.1 - (D i).card)

noncomputable def pcr_ghostCreateFactor {K : ℕ} (F : PDFix K) (S : PDScale) (ρ v : ℝ)
    (j : ℕ) (l : Fin K → ℕ) (i : Fin K) : ℝ :=
  (v * memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ (l i) / ((l i).factorial : ℝ)

theorem pcr_ghost_weighted_product {K : ℕ} (F : PDFix K) (S : PDScale) (ρ v : ℝ)
    (hρ : 0 < ρ) (hv : 0 < v) (j : ℕ) (s : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hD : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p) :
    |∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) (D i).card (l i)
      (List.ofFn fun k => (new i k : ℕ))| *
        v ^ memSize (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
          List.ofFn fun k => anchorAt (new i k) s.1) =
      v ^ memSize s * (∏ i : Fin K, pcr_ghostDeleteFactor F S ρ v j s D i) *
        (∏ i : Fin K, pcr_ghostCreateFactor F S ρ v j l i) *
          ∏ i : Fin K, ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k) := by
  let m (i : Fin K) := removeIndices (s.2.2 i) (D i) ++
    List.ofFn fun k => anchorAt (new i k) s.1
  let C (i : Fin K) := ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
    (D i).card (l i) (List.ofFn fun k => (new i k : ℕ))
  have hgroup (i : Fin K) : |C i| * v ^ (m i).length =
      v ^ (s.2.2 i).length * pcr_ghostDeleteFactor F S ρ v j s D i *
        pcr_ghostCreateFactor F S ρ v j l i * ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k) := by
    have hprod : 0 ≤ ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k) :=
      Finset.prod_nonneg fun k hk => hν i _ (new i k).property
    have hbal : (m i).length + (D i).card = (s.2.2 i).length + l i := by
      have h := pd5_removeIndices_length_balance (s.2.2 i) (D i)
      dsimp [m]
      simp only [List.length_append, List.length_ofFn]
      omega
    have hd : (D i).card ≤ hitCount (s.2.2 i) s.1 := Finset.card_le_card (hD i)
    have he := pcr_weighted_ghost_group (memoryEta S.x F.q_d j) (memoryQ S.x F.q_d j)
      (bandMass S.x (F.a i)) ρ v (∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k))
      hη hq (hV i) hρ hv hprod (s.2.2 i).length (hitCount (s.2.2 i) s.1)
      (D i).card (l i) (m i).length hd hbal
    simp only [C, ghostGroupCoeff, pcr_ghostDeleteFactor, pcr_ghostCreateFactor,
      List.map_ofFn, List.prod_ofFn, Function.comp_def]
    convert he using 1 <;> ring
  change |∏ i, C i| * v ^ (∑ i, (m i).length) = _
  rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ i : Fin K, v ^ (s.2.2 i).length * pcr_ghostDeleteFactor F S ρ v j s D i *
        pcr_ghostCreateFactor F S ρ v j l i * ∏ k : Fin (l i), memoryNu S.x K F.a F.q_d i (new i k) :=
      Finset.prod_congr rfl (fun i hi => hgroup i)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, memSize]

/-- Tensor the indexed deletion contraction over all groups, retaining eligibility guards. -/
theorem pcr_ghost_delete_total_le_one {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv : 0 < v)
    (hlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (j : ℕ) (s : MemPoint S.x K) :
    (∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
      if ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then
        ∏ i : Fin K, pcr_ghostDeleteFactor F S ρ v j s D i else 0) ≤ 1 := by
  let g (i : Fin K) (D : Finset (Fin (s.2.2 i).length)) : ℝ :=
    if D ⊆ hitIndices (s.2.2 i) s.1 then
      (memoryEta S.x F.q_d j / (ρ * v)) ^ D.card *
        (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hitCount (s.2.2 i) s.1 - D.card) else 0
  have hterm (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) :
      (if ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then
        ∏ i : Fin K, pcr_ghostDeleteFactor F S ρ v j s D i else 0) = ∏ i : Fin K, g i (D i) := by
    by_cases hd : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
    · rw [if_pos hd]
      apply Finset.prod_congr rfl
      intro i hi
      simp [g, hd i, pcr_ghostDeleteFactor]
    · have hn : ∃ i, ¬ D i ⊆ hitIndices (s.2.2 i) s.1 := by push_neg at hd; exact hd
      obtain ⟨i, hi⟩ := hn
      rw [if_neg hd]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hi]
  have hη := (pd5_memoryEta_bounds (x := S.x) hF.2.1 hF.2.2.1 j).1
  have hq : 0 ≤ memoryQ S.x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have hg (i : Fin K) (D : Finset (Fin (s.2.2 i).length)) : 0 ≤ g i D := by
    dsimp [g]
    split_ifs
    · apply mul_nonneg
      · exact pow_nonneg (div_nonneg hη (mul_nonneg hρ.1.le hv.le)) _
      · exact pow_nonneg (div_nonneg hq (sq_nonneg _)) _
    · exact le_rfl
  have hsum (i : Fin K) : (∑ D : Finset (Fin (s.2.2 i).length), g i D) ≤ 1 := by
    simpa [g, hitCount] using
      pd5_ghost_indexed_deletions_le_one F hF ρ hρ v hv hlarge (x := S.x) j (s.2.2 i) s.1
  calc
    _ = ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length), ∏ i : Fin K, g i (D i) :=
      Finset.sum_congr rfl (fun D hD => hterm D)
    _ = ∏ i : Fin K, ∑ D : Finset (Fin (s.2.2 i).length), g i D := (Fintype.prod_sum g).symm
    _ ≤ ∏ _i : Fin K, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun D hD => hg i D
      · intro i hi
        exact hsum i
    _ = 1 := by simp


/-- The cutoff creation sums tensor into one fixed exponential constant; m=0 of the checked
batch-length lemma is enough once the full Δ^m cost has already been retained. -/
theorem pcr_ghost_create_total_le_exp (K B : ℕ) (c : Fin K → ℝ) (cbar : ℝ)
    (hc : ∀ i, 0 ≤ c i) (hcb : ∀ i, c i ≤ cbar) :
    (∑ l : Fin K → Fin (B + 1), ∏ i : Fin K,
      (c i) ^ (l i).val / (((l i).val).factorial : ℝ) * (2 : ℝ) ^ (l i).val) ≤
        Real.exp (2 * (K : ℝ) * cbar) := by
  let g (i : Fin K) (l : Fin (B + 1)) : ℝ :=
    (c i) ^ l.val / (l.val.factorial : ℝ) * (2 : ℝ) ^ l.val
  have hg (i : Fin K) (l : Fin (B + 1)) : 0 ≤ g i l := by
    have hci := hc i
    dsimp [g]
    positivity
  have hs (i : Fin K) : (∑ l : Fin (B + 1), g i l) ≤ Real.exp (2 * cbar) := by
    have hb := pd5_batch_length_atom_bound B 0 (c i) 1 2 (hc i) (by norm_num) (by norm_num)
    have he : (∑ l : Fin (B + 1), g i l) =
        ∑ l ∈ Finset.range (B + 1), (c i) ^ l * (2 : ℝ) ^ l / (l.factorial : ℝ) := by
      dsimp only [g]
      rw [Fin.sum_univ_eq_sum_range
        (fun n : ℕ => (c i) ^ n / (n.factorial : ℝ) * (2 : ℝ) ^ n) (B + 1)]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [he]
    have hb' : (∑ l ∈ Finset.range (B + 1), (c i) ^ l * (2 : ℝ) ^ l / (l.factorial : ℝ)) ≤
        Real.exp (2 * c i) := by
      simpa [mul_comm] using hb
    exact hb'.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcb i) (by norm_num)))
  calc
    _ = ∏ i : Fin K, ∑ l : Fin (B + 1), g i l := (Fintype.prod_sum g).symm
    _ ≤ ∏ _i : Fin K, Real.exp (2 * cbar) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg fun l hl => hg i l
      · intro i hi
        exact hs i
    _ = Real.exp (2 * cbar) ^ K := by simp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring


/-- Assemble the finite positive ghost row from indexed deletion contraction, creation mass
and the already-proved prescribed prime atom bound. -/
theorem pcr_ghost_prescribed_row {K : ℕ} (F : PDFix K) (S : PDScale) (ρ v : ℝ)
    (hρ : 0 < ρ) (hv : 0 < v) (j B : ℕ) (s : MemPoint S.x K) (hs : memSize s ≤ B)
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K) (Δ Cg : ℝ)
    (hΔ : 0 ≤ Δ) (hCg : 0 ≤ Cg)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i, 0 ≤ bandMass S.x (F.a i))
    (hν : ∀ i p, p ∈ primeBand S.x (F.a i) → 0 ≤ memoryNu S.x K F.a F.q_d i p)
    (hmass : ∀ i, (∑ p ∈ primeBand S.x (F.a i), memoryNu S.x K F.a F.q_d i p) ≤ 2)
    (hatom : ∀ i p, p ∈ primeBand S.x (F.a i) → memoryNu S.x K F.a F.q_d i p ≤ Δ)
    (hdel : (∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
      if ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then ∏ i, pcr_ghostDeleteFactor F S ρ v j s D i else 0) ≤ 1)
    (hcreate : (∑ l : Fin K → Fin (B + 1),
      (∏ i, pcr_ghostCreateFactor F S ρ v j (fun i => (l i).val) i) *
        (2 : ℝ) ^ (∑ i, (l i).val)) ≤ Cg) :
    pd5_ghostAbsChoice F S ρ j B (pd5_prescribedWeight S B U R pick pastLog)
      (fun t => v ^ memSize t) s ≤ Cg * Δ ^ R.card * v ^ memSize s := by
  let E (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) : Prop :=
    ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  let d (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) : ℝ :=
    ∏ i, pcr_ghostDeleteFactor F S ρ v j s D i
  let c (l : Fin K → Fin (B + 1)) : ℝ :=
    ∏ i, pcr_ghostCreateFactor F S ρ v j (fun i => (l i).val) i
  let W := pd5_prescribedWeight S B U R pick pastLog
  have hW (log : BirthLog K) : 0 ≤ W log := by
    dsimp [W, pd5_prescribedWeight]
    split_ifs <;> norm_num
  have hd (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) : 0 ≤ d D := by
    apply Finset.prod_nonneg
    intro i hi
    dsimp [pcr_ghostDeleteFactor]
    exact mul_nonneg (pow_nonneg (div_nonneg hη (mul_nonneg hρ.le hv.le)) _)
      (pow_nonneg (div_nonneg hq (sq_nonneg _)) _)
  have hc (l : Fin K → Fin (B + 1)) : 0 ≤ c l := by
    apply Finset.prod_nonneg
    intro i hi
    have hVi := hV i
    dsimp [pcr_ghostCreateFactor]
    positivity
  have hvpow : 0 ≤ v ^ memSize s := pow_nonneg hv.le _
  have hatomPow : 0 ≤ Δ ^ R.card := pow_nonneg hΔ _
  unfold pd5_ghostAbsChoice
  rw [if_pos hs]
  calc
    _ ≤ ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        if E D then v ^ memSize s * d D * Δ ^ R.card *
          (∑ l : Fin K → Fin (B + 1), c l * (2 : ℝ) ^ (∑ i, (l i).val)) else 0 := by
      apply Finset.sum_le_sum
      intro D hD
      by_cases he : E D
      · rw [if_pos he, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        let lens := fun i => (l i).val
        have hlen : ∀ i, lens i ≤ B := fun i => Nat.le_of_lt_succ (l i).isLt
        let nu (new : (i : Fin K) → Fin (lens i) → primeBand S.x (F.a i)) : ℝ :=
          ∏ i : Fin K, ∏ k : Fin (lens i), memoryNu S.x K F.a F.q_d i (new i k)
        have hnu new : 0 ≤ nu new := Finset.prod_nonneg fun i hi =>
          Finset.prod_nonneg fun k hk => hν i _ (new i k).property
        calc
          _ ≤ ∑ new : (i : Fin K) → Fin (lens i) → primeBand S.x (F.a i),
              (v ^ memSize s * d D * c l) *
                (W (pd5_ghostBirthLog j lens (fun i k => (new i k : ℕ))) * nu new) := by
            apply Finset.sum_le_sum
            intro new hn
            let t : MemPoint S.x K := (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
              List.ofFn fun k => anchorAt (new i k) s.1)
            change (if E D ∧ memSize t ≤ B then
              |∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) (D i).card (lens i)
                (List.ofFn fun k => (new i k : ℕ))| *
                W (pd5_ghostBirthLog j lens (fun i k => (new i k : ℕ))) * v ^ memSize t else 0) ≤ _
            by_cases ht : memSize t ≤ B
            · simp only [if_pos (show E D ∧ memSize t ≤ B from ⟨he, ht⟩)]
              have hw := pcr_ghost_weighted_product F S ρ v hρ hv j s D lens new he hη hq hV hν
              have heq := congrArg (fun z : ℝ => z *
                W (pd5_ghostBirthLog j lens (fun i k => (new i k : ℕ)))) hw
              convert heq.le using 1 <;> dsimp only [d, c, nu, t, lens] <;> ring
            · have hncap : ¬ (E D ∧ memSize t ≤ B) := fun h => ht h.2
              simp only [if_neg hncap]
              exact mul_nonneg (mul_nonneg (mul_nonneg hvpow (hd D)) (hc l))
                (mul_nonneg (hW _) (hnu new))
          _ = (v ^ memSize s * d D * c l) *
              ∑ new : (i : Fin K) → Fin (lens i) → primeBand S.x (F.a i),
                W (pd5_ghostBirthLog j lens (fun i k => (new i k : ℕ))) * nu new := by rw [Finset.mul_sum]
          _ ≤ (v ^ memSize s * d D * c l) * (Δ ^ R.card * (2 : ℝ) ^ (∑ i, lens i)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hvpow (hd D)) (hc l))
            exact pcr_ghost_batch_prescribed_atoms F S B j lens hlen U R hRU pick pastLog Δ hΔ hν hmass hatom
          _ = _ := by ring
      · have hh : ¬ ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 := he
        simp [E, he, hh]
    _ ≤ ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        if E D then v ^ memSize s * d D * Δ ^ R.card * Cg else 0 := by
      apply Finset.sum_le_sum
      intro D hD
      split_ifs
      · exact mul_le_mul_of_nonneg_left hcreate (mul_nonneg (mul_nonneg hvpow (hd D)) hatomPow)
      · exact le_rfl
    _ = (v ^ memSize s * Δ ^ R.card * Cg) *
        (∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length), if E D then d D else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      split_ifs <;> ring
    _ ≤ (v ^ memSize s * Δ ^ R.card * Cg) * 1 :=
      mul_le_mul_of_nonneg_left hdel (mul_nonneg (mul_nonneg hvpow hatomPow) hCg)
    _ = _ := by ring


end
end ArtinPrimitiveRoots.TypeII.PD
