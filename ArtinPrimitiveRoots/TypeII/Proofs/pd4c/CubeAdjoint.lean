import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.MemoryAlphabet

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Separate one group from a finite product of weighted state spaces. -/
theorem pd4c_weighted_pi_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] (μ : (i : ι) → X i → ℂ)
    (i : ι) (f : ((j : ι) → X j) → ℂ) :
    (∑ w : (j : ι) → X j, (∏ j : ι, μ j (w j)) * f w) =
      ∑ u : (j : {j : ι // j ≠ i}) → X j.1,
        (∏ j : {j : ι // j ≠ i}, μ j.1 (u j)) *
          (∑ x : X i, μ i x * f ((Equiv.piSplitAt i X).symm (x, u))) := by
  let E := Equiv.piSplitAt i X
  have hprod (x : X i) (u : (j : {j : ι // j ≠ i}) → X j.1) :
      (∏ j : ι, μ j (E.symm (x, u) j)) =
        μ i x * ∏ j : {j : ι // j ≠ i}, μ j.1 (u j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hpair := E.apply_symm_apply (x, u)
    have hfirst : E.symm (x, u) i = x := congrArg Prod.fst hpair
    have hrest : ∀ j : {j : ι // j ≠ i}, E.symm (x, u) j.1 = u j := by
      intro j
      exact congrFun (congrArg Prod.snd hpair) j
    rw [hfirst]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hrest]
  have hreindex := Equiv.sum_comp E.symm
    (fun w : (j : ι) → X j => (∏ j : ι, μ j (w j)) * f w)
  rw [← hreindex, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod]
  ring

abbrev Pd4cWordCube {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ) :=
  (i : Fin K) → Pd4cBoundedWord (T i) B

def pd4c_cubeMemory {K : ℕ} {T : Fin K → Finset Particle} {B : ℕ}
    (w : Pd4cWordCube T B) : Fin K → List Particle := fun i => pd4c_word (w i).2

/-- A creation in one group transposes to indexed deletion in the finite product measure. -/
theorem pd4c_cube_creation_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hFzero : ∀ l, B < (l i).length → F l = 0) :
    (ν i e : ℂ) *
        (∑ w : Pd4cWordCube T B,
          (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
            G (pd4c_cubeMemory w) *
              F (Function.update (pd4c_cubeMemory w) i ((pd4c_cubeMemory w i) ++ [(e : Particle)]))) =
      ∑ w : Pd4cWordCube T B,
        (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
          F (pd4c_cubeMemory w) *
          (∑ k : Fin (w i).1.val, if ((w i).2 k : Particle) = (e : Particle) then
            G (Function.update (pd4c_cubeMemory w) i
              (removeIndices (pd4c_word (w i).2) {pd4c_wordIndex (w i).2 k})) else 0) := by
  let X (j : Fin K) := Pd4cBoundedWord (T j) B
  let E := Equiv.piSplitAt i X
  let μ (j : Fin K) (x : X j) : ℂ := (pd4c_listDensity (ν j) (pd4c_word x.2) : ℂ)
  let rest (u : (j : {j : Fin K // j ≠ i}) → X j.1) : Fin K → List Particle :=
    fun j => if h : j = i then [] else pd4c_word (u ⟨j, h⟩).2
  have hmem (x : X i) (u : (j : {j : Fin K // j ≠ i}) → X j.1) :
      pd4c_cubeMemory (E.symm (x, u)) = Function.update (rest u) i (pd4c_word x.2) := by
    funext j
    by_cases hj : j = i
    · subst j
      have hfirst : E.symm (x, u) i = x := congrArg Prod.fst (E.apply_symm_apply (x, u))
      simpa only [pd4c_cubeMemory, Function.update_self] using
        congrArg (fun v : X i => pd4c_word v.2) hfirst
    · have hrest : E.symm (x, u) j = u ⟨j, hj⟩ :=
        congrFun (congrArg Prod.snd (E.apply_symm_apply (x, u))) ⟨j, hj⟩
      simpa only [pd4c_cubeMemory, Function.update_of_ne hj, rest, dif_neg hj] using
        congrArg (fun v : X j => pd4c_word v.2) hrest
  have hFi (u : (j : {j : Fin K // j ≠ i}) → X j.1) (l l' : List Particle) (hp : l.Perm l') :
      F (Function.update (rest u) i l) = F (Function.update (rest u) i l') := by
    apply hF
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hp
    · simp [Function.update_of_ne hj]
  have hGi (u : (j : {j : Fin K // j ≠ i}) → X j.1) (l l' : List Particle) (hp : l.Perm l') :
      G (Function.update (rest u) i l) = G (Function.update (rest u) i l') := by
    apply hG
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hp
    · simp [Function.update_of_ne hj]
  have hpair (u : (j : {j : Fin K // j ≠ i}) → X j.1) :=
    pd4c_bounded_creation_pairing (T i) B (ν i) e
      (fun l => F (Function.update (rest u) i l)) (fun l => G (Function.update (rest u) i l))
      (hFi u) (hGi u) (fun l hl => hFzero _ (by simpa using hl))
  simp only [mul_assoc]
  rw [pd4c_weighted_pi_sum X μ i (fun w => G (pd4c_cubeMemory w) *
    F (Function.update (pd4c_cubeMemory w) i ((pd4c_cubeMemory w i) ++ [(e : Particle)])))]
  rw [pd4c_weighted_pi_sum X μ i (fun w => F (pd4c_cubeMemory w) *
    (∑ k : Fin (w i).1.val, if ((w i).2 k : Particle) = (e : Particle) then
      G (Function.update (pd4c_cubeMemory w) i
        (removeIndices (pd4c_word (w i).2) {pd4c_wordIndex (w i).2 k})) else 0))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hfirst (x : X i) : E.symm (x, u) i = x := congrArg Prod.fst (E.apply_symm_apply (x, u))
  have hmem' (x : X i) : pd4c_cubeMemory ((Equiv.piSplitAt i X).symm (x, u)) =
      Function.update (rest u) i (pd4c_word x.2) := hmem x u
  have hfirst' (x : X i) : (Equiv.piSplitAt i X).symm (x, u) i = x := hfirst x
  simp only [hmem', Function.update_self, Function.update_idem, hfirst']
  have hdel (x : X i) :
      (∑ k : Fin ((Equiv.piSplitAt i X).symm (x, u) i).1.val,
        if (((Equiv.piSplitAt i X).symm (x, u) i).2 k : Particle) = (e : Particle) then
          G (Function.update (rest u) i
            (removeIndices (pd4c_word ((Equiv.piSplitAt i X).symm (x, u) i).2)
              {pd4c_wordIndex ((Equiv.piSplitAt i X).symm (x, u) i).2 k})) else 0) =
      (∑ k : Fin x.1.val, if (x.2 k : Particle) = (e : Particle) then
        G (Function.update (rest u) i (removeIndices (pd4c_word x.2) {pd4c_wordIndex x.2 k})) else 0) := by
    exact congrArg (fun a : X i => ∑ k : Fin a.1.val,
      if (a.2 k : Particle) = (e : Particle) then
        G (Function.update (rest u) i (removeIndices (pd4c_word a.2) {pd4c_wordIndex a.2 k})) else 0)
      (hfirst' x)
  simp_rw [hdel]
  have h := hpair u
  change (ν i e : ℂ) * ((∏ j : {j : Fin K // j ≠ i}, μ j.1 (u j)) * _) = _
  calc
    _ = (∏ j : {j : Fin K // j ≠ i}, μ j.1 (u j)) *
        ((ν i e : ℂ) * (∑ x : X i, μ i x * G (Function.update (rest u) i (pd4c_word x.2)) *
          F (Function.update (rest u) i (pd4c_word x.2 ++ [(e : Particle)])))) := by
      simp_rw [Finset.mul_sum]
      ring
    _ = _ := by
      have hscaled := congrArg (fun z : ℂ => (∏ j : {j : Fin K // j ≠ i}, μ j.1 (u j)) * z) h
      simpa only [μ, mul_assoc] using hscaled

/-- The reverse indexed-retrieval identity carries the density factor into creation. -/
theorem pd4c_cube_annihilation_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hGzero : ∀ l, B < (l i).length → G l = 0) :
    (∑ w : Pd4cWordCube T B,
      (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
        G (pd4c_cubeMemory w) *
        (∑ k : Fin (w i).1.val, if ((w i).2 k : Particle) = (e : Particle) then
          F (Function.update (pd4c_cubeMemory w) i
            (removeIndices (pd4c_word (w i).2) {pd4c_wordIndex (w i).2 k})) else 0)) =
      (ν i e : ℂ) *
        (∑ w : Pd4cWordCube T B,
          (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
            F (pd4c_cubeMemory w) *
              G (Function.update (pd4c_cubeMemory w) i ((pd4c_cubeMemory w i) ++ [(e : Particle)]))) :=
  (pd4c_cube_creation_pairing T B ν i e G F hG hF hGzero).symm

def pd4c_create {K : ℕ} (i : Fin K) (e : Particle)
    (f : (Fin K → List Particle) → ℂ) (m : Fin K → List Particle) : ℂ :=
  f (Function.update m i (m i ++ [e]))

def pd4c_retrieve {K : ℕ} (i : Fin K) (e : Particle)
    (f : (Fin K → List Particle) → ℂ) (m : Fin K → List Particle) : ℂ :=
  ∑ k : Fin (m i).length, if (m i).get k = e then
    f (Function.update m i (removeIndices (m i) {k})) else 0

/-- Actual list-indexed retrieval agrees with the finite word-indexed formula. -/
theorem pd4c_retrieve_cubeMemory {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (i : Fin K) (e : Particle) (G : (Fin K → List Particle) → ℂ) (w : Pd4cWordCube T B) :
    pd4c_retrieve i e G (pd4c_cubeMemory w) =
      ∑ k : Fin (w i).1.val, if ((w i).2 k : Particle) = e then
        G (Function.update (pd4c_cubeMemory w) i
          (removeIndices (pd4c_word (w i).2) {pd4c_wordIndex (w i).2 k})) else 0 :=
  pd4c_word_retrieve_sum (w i).2 e (fun l => G (Function.update (pd4c_cubeMemory w) i l))

/-- Creation preserves invariance under all group memory-list permutations. -/
theorem pd4c_create_symmetric {K : ℕ} (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ)
    (hF : ∀ m m', (∀ j, List.Perm (m j) (m' j)) → F m = F m') :
    ∀ m m', (∀ j, List.Perm (m j) (m' j)) → pd4c_create i e F m = pd4c_create i e F m' := by
  intro m m' hm
  apply hF
  intro j
  by_cases hj : j = i
  · subst j
    simpa using (hm i).append_right [e]
  · simpa only [Function.update_of_ne hj] using hm j

/-- The component adjoint identity in the same list representation as the edge definitions. -/
theorem pd4c_create_retrieve_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hFzero : ∀ l, B < (l i).length → F l = 0) :
    (ν i e : ℂ) * (∑ w : Pd4cWordCube T B,
      (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
        G (pd4c_cubeMemory w) * pd4c_create i (e : Particle) F (pd4c_cubeMemory w)) =
      ∑ w : Pd4cWordCube T B,
        (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
          F (pd4c_cubeMemory w) * pd4c_retrieve i (e : Particle) G (pd4c_cubeMemory w) := by
  simp_rw [pd4c_retrieve_cubeMemory]
  exact pd4c_cube_creation_pairing T B ν i e F G hF hG hFzero

/-- Indexed promotion transposes to creation of the promoted particle. -/
theorem pd4c_retrieve_create_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hGzero : ∀ l, B < (l i).length → G l = 0) :
    (∑ w : Pd4cWordCube T B,
      (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
        G (pd4c_cubeMemory w) * pd4c_retrieve i (e : Particle) F (pd4c_cubeMemory w)) =
      (ν i e : ℂ) * (∑ w : Pd4cWordCube T B,
        (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
          F (pd4c_cubeMemory w) * pd4c_create i (e : Particle) G (pd4c_cubeMemory w)) :=
  (pd4c_create_retrieve_pairing T B ν i e G F hG hF hGzero).symm

def pd4c_cubePair {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (F G : (Fin K → List Particle) → ℂ) : ℂ :=
  ∑ w : Pd4cWordCube T B,
    (∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
      F (pd4c_cubeMemory w) * G (pd4c_cubeMemory w)

theorem pd4c_cubePair_comm {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (F G : (Fin K → List Particle) → ℂ) :
    pd4c_cubePair T B ν F G = pd4c_cubePair T B ν G F := by
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- Simultaneous storage and promotion transpose by exchanging their two particles. -/
theorem pd4c_store_promote_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (p q : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hFzero : ∀ l, B < (l i).length → F l = 0)
    (hGzero : ∀ l, B < (l i).length → G l = 0) :
    (ν i p : ℂ) * pd4c_cubePair T B ν G
      (pd4c_retrieve i (q : Particle) (pd4c_create i (p : Particle) F)) =
      (ν i q : ℂ) * pd4c_cubePair T B ν F
        (pd4c_retrieve i (p : Particle) (pd4c_create i (q : Particle) G)) := by
  have h1 : pd4c_cubePair T B ν G
        (pd4c_retrieve i (q : Particle) (pd4c_create i (p : Particle) F)) =
      (ν i q : ℂ) * pd4c_cubePair T B ν (pd4c_create i (p : Particle) F)
        (pd4c_create i (q : Particle) G) :=
    pd4c_retrieve_create_pairing T B ν i q (pd4c_create i (p : Particle) F) G
      (pd4c_create_symmetric i (p : Particle) F hF) hG hGzero
  have h2 : (ν i p : ℂ) * pd4c_cubePair T B ν (pd4c_create i (q : Particle) G)
        (pd4c_create i (p : Particle) F) =
      pd4c_cubePair T B ν F
        (pd4c_retrieve i (p : Particle) (pd4c_create i (q : Particle) G)) :=
    pd4c_create_retrieve_pairing T B ν i p F (pd4c_create i (q : Particle) G)
      hF (pd4c_create_symmetric i (q : Particle) G hG) hFzero
  rw [h1]
  calc
    _ = (ν i q : ℂ) * ((ν i p : ℂ) * pd4c_cubePair T B ν
        (pd4c_create i (q : Particle) G) (pd4c_create i (p : Particle) F)) := by
      rw [pd4c_cubePair_comm T B ν (pd4c_create i (p : Particle) F)]
      ring
    _ = _ := by rw [h2]

/-- Indexed retrieval preserves memory symmetry, with repeated particles counted by positions. -/
theorem pd4c_retrieve_symmetric {K : ℕ} (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ)
    (hF : ∀ m m', (∀ j, (m j).Perm (m' j)) → F m = F m') :
    ∀ m m', (∀ j, (m j).Perm (m' j)) → pd4c_retrieve i e F m = pd4c_retrieve i e F m' := by
  intro m m' hm
  obtain ⟨E, hget⟩ := pd4c_finEquiv_of_list_perm (hm i)
  unfold pd4c_retrieve
  have hsum := Equiv.sum_comp E (fun k : Fin (m i).length => if (m i).get k = e then
    F (Function.update m i (removeIndices (m i) {k})) else 0)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hget k]
  by_cases he : (m' i).get k = e
  · rw [if_pos he, if_pos he]
    apply hF
    intro j
    by_cases hj : j = i
    · subst j
      have hp := pd4c_removeIndices_perm_of_getEquiv E hget {k}
      simpa only [Function.update_self, Finset.image_singleton] using hp.symm
    · simpa only [Function.update_of_ne hj] using hm j
  · rw [if_neg he, if_neg he]

/-- Creation is zero outside the same group cutoff whenever the continuation is. -/
theorem pd4c_create_zero_of_cutoff {K : ℕ} (B : ℕ) (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ)
    (hF : ∀ m, B < (m i).length → F m = 0) :
    ∀ m, B < (m i).length → pd4c_create i e F m = 0 := by
  intro m hm
  apply hF
  simpa only [Function.update_self, List.length_append, List.length_singleton] using
    lt_of_lt_of_le hm (Nat.le_add_right (m i).length 1)

def pd4c_clip {K : ℕ} (B : ℕ) (F : (Fin K → List Particle) → ℂ)
    (m : Fin K → List Particle) : ℂ := if ∀ j, (m j).length ≤ B then F m else 0

theorem pd4c_cubeMemory_lengths {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (w : Pd4cWordCube T B) : ∀ j, (pd4c_cubeMemory w j).length ≤ B := by
  intro j
  have h := (w j).1.isLt
  simpa only [pd4c_cubeMemory, pd4c_word, List.length_ofFn, Nat.lt_succ_iff] using h

theorem pd4c_clip_cubeMemory {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (F : (Fin K → List Particle) → ℂ) (w : Pd4cWordCube T B) :
    pd4c_clip B F (pd4c_cubeMemory w) = F (pd4c_cubeMemory w) :=
  if_pos (pd4c_cubeMemory_lengths T B w)

theorem pd4c_clip_symmetric {K : ℕ} (B : ℕ) (F : (Fin K → List Particle) → ℂ)
    (hF : ∀ m m', (∀ j, (m j).Perm (m' j)) → F m = F m') :
    ∀ m m', (∀ j, (m j).Perm (m' j)) → pd4c_clip B F m = pd4c_clip B F m' := by
  intro m m' hm
  have hbounds : (∀ j, (m j).length ≤ B) ↔ ∀ j, (m' j).length ≤ B :=
    forall_congr' fun j => by rw [(hm j).length_eq]
  by_cases h : ∀ j, (m j).length ≤ B
  · have h' := hbounds.mp h
    simp only [pd4c_clip, if_pos h, if_pos h']
    exact hF m m' hm
  · have h' : ¬ ∀ j, (m' j).length ≤ B := fun h' => h (hbounds.mpr h')
    simp only [pd4c_clip, if_neg h, if_neg h']

theorem pd4c_clip_zero {K : ℕ} (B : ℕ) (F : (Fin K → List Particle) → ℂ) :
    ∀ m i, B < (m i).length → pd4c_clip B F m = 0 := by
  intro m i hi
  exact if_neg (fun h => (not_le_of_gt hi) (h i))

def pd4c_weightedCreate {K : ℕ} (B : ℕ) (ν : Particle → ℝ) (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ) :=
  pd4c_clip B (fun m => (ν e : ℂ) * pd4c_create i e F m)

def pd4c_clippedRetrieve {K : ℕ} (B : ℕ) (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ) := pd4c_clip B (pd4c_retrieve i e F)

/-- The finite cube adjoint pair uses weighted creation and clipped indexed retrieval. -/
theorem pd4c_weightedCreate_adjoint {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ)
    (hF : ∀ l l', (∀ j, (l j).Perm (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, (l j).Perm (l' j)) → G l = G l')
    (hFzero : ∀ l, B < (l i).length → F l = 0) :
    pd4c_cubePair T B ν G (pd4c_weightedCreate B (ν i) i (e : Particle) F) =
      pd4c_cubePair T B ν F (pd4c_clippedRetrieve B i (e : Particle) G) := by
  have h := pd4c_create_retrieve_pairing T B ν i e F G hF hG hFzero
  unfold pd4c_cubePair pd4c_weightedCreate pd4c_clippedRetrieve
  simp_rw [pd4c_clip_cubeMemory]
  rw [Finset.mul_sum] at h
  calc
    _ = ∑ w : Pd4cWordCube T B, (ν i e : ℂ) *
      ((∏ j : Fin K, (pd4c_listDensity (ν j) (pd4c_word (w j).2) : ℂ)) *
        G (pd4c_cubeMemory w) * pd4c_create i (e : Particle) F (pd4c_cubeMemory w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := h

def Pd4cAdmissibleTest {K : ℕ} (B : ℕ) (F : (Fin K → List Particle) → ℂ) : Prop :=
  (∀ m m', (∀ j, (m j).Perm (m' j)) → F m = F m') ∧
    ∀ m j, B < (m j).length → F m = 0

theorem pd4c_weightedCreate_admissible {K : ℕ} (B : ℕ) (ν : Particle → ℝ)
    (i : Fin K) (e : Particle) (F : (Fin K → List Particle) → ℂ)
    (hF : Pd4cAdmissibleTest B F) : Pd4cAdmissibleTest B (pd4c_weightedCreate B ν i e F) := by
  refine ⟨?_, pd4c_clip_zero B _⟩
  apply pd4c_clip_symmetric
  intro m m' hm
  rw [pd4c_create_symmetric i e F hF.1 m m' hm]

theorem pd4c_clippedRetrieve_admissible {K : ℕ} (B : ℕ) (i : Fin K) (e : Particle)
    (F : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) :
    Pd4cAdmissibleTest B (pd4c_clippedRetrieve B i e F) :=
  ⟨pd4c_clip_symmetric B _ (pd4c_retrieve_symmetric i e F hF.1), pd4c_clip_zero B _⟩

/-- Adjoint identities on admissible tests compose in reversed operator order. -/
theorem pd4c_cube_adjoint_compose {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ)
    (A A' R R' : ((Fin K → List Particle) → ℂ) → (Fin K → List Particle) → ℂ)
    (hR : ∀ F, Pd4cAdmissibleTest B F → Pd4cAdmissibleTest B (R F))
    (hA' : ∀ G, Pd4cAdmissibleTest B G → Pd4cAdmissibleTest B (A' G))
    (hAadj : ∀ F G, Pd4cAdmissibleTest B F → Pd4cAdmissibleTest B G →
      pd4c_cubePair T B ν G (A F) = pd4c_cubePair T B ν F (A' G))
    (hRadj : ∀ F G, Pd4cAdmissibleTest B F → Pd4cAdmissibleTest B G →
      pd4c_cubePair T B ν G (R F) = pd4c_cubePair T B ν F (R' G))
    (F G : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) (hG : Pd4cAdmissibleTest B G) :
    pd4c_cubePair T B ν G (A (R F)) = pd4c_cubePair T B ν F (R' (A' G)) := by
  rw [hAadj (R F) G (hR F hF) hG, pd4c_cubePair_comm T B ν (R F)]
  exact hRadj F (A' G) hF (hA' G hG)

theorem pd4c_weightedCreate_adjoint_admissible {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) (hG : Pd4cAdmissibleTest B G) :
    pd4c_cubePair T B ν G (pd4c_weightedCreate B (ν i) i (e : Particle) F) =
      pd4c_cubePair T B ν F (pd4c_clippedRetrieve B i (e : Particle) G) :=
  pd4c_weightedCreate_adjoint T B ν i e F G hF.1 hG.1 (fun m hm => hF.2 m i hm)

theorem pd4c_clippedRetrieve_adjoint_admissible {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (i : Fin K) (e : T i)
    (F G : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) (hG : Pd4cAdmissibleTest B G) :
    pd4c_cubePair T B ν G (pd4c_clippedRetrieve B i (e : Particle) F) =
      pd4c_cubePair T B ν F (pd4c_weightedCreate B (ν i) i (e : Particle) G) :=
  (pd4c_weightedCreate_adjoint_admissible T B ν i e G F hG hF).symm

abbrev Pd4cFockCommand {K : ℕ} (T : Fin K → Finset Particle) := Σ i : Fin K, Bool × T i

def pd4c_commandOp {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (a : Pd4cFockCommand T)
    (F : (Fin K → List Particle) → ℂ) : (Fin K → List Particle) → ℂ :=
  if a.2.1 then pd4c_weightedCreate B (ν a.1) a.1 (a.2.2 : Particle) F
  else pd4c_clippedRetrieve B a.1 (a.2.2 : Particle) F

def pd4c_commandReverse {K : ℕ} {T : Fin K → Finset Particle}
    (a : Pd4cFockCommand T) : Pd4cFockCommand T := ⟨a.1, !a.2.1, a.2.2⟩

def pd4c_commandsOp {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) : List (Pd4cFockCommand T) →
      ((Fin K → List Particle) → ℂ) → (Fin K → List Particle) → ℂ
  | [], F => F
  | a :: l, F => pd4c_commandOp T B ν a (pd4c_commandsOp T B ν l F)

theorem pd4c_command_admissible {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (a : Pd4cFockCommand T)
    (F : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) :
    Pd4cAdmissibleTest B (pd4c_commandOp T B ν a F) := by
  cases a with
  | mk i v =>
    rcases v with ⟨b, e⟩
    cases b
    · exact pd4c_clippedRetrieve_admissible B i (e : Particle) F hF
    · exact pd4c_weightedCreate_admissible B (ν i) i (e : Particle) F hF

theorem pd4c_command_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (a : Pd4cFockCommand T)
    (F G : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) (hG : Pd4cAdmissibleTest B G) :
    pd4c_cubePair T B ν G (pd4c_commandOp T B ν a F) =
      pd4c_cubePair T B ν F (pd4c_commandOp T B ν (pd4c_commandReverse a) G) := by
  cases a with
  | mk i v =>
    rcases v with ⟨b, e⟩
    cases b
    · exact pd4c_clippedRetrieve_adjoint_admissible T B ν i e F G hF hG
    · exact pd4c_weightedCreate_adjoint_admissible T B ν i e F G hF hG

theorem pd4c_commands_admissible {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (l : List (Pd4cFockCommand T))
    (F : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) :
    Pd4cAdmissibleTest B (pd4c_commandsOp T B ν l F) := by
  induction l with
  | nil => exact hF
  | cons a l ih => exact pd4c_command_admissible T B ν a _ ih

theorem pd4c_commands_append {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (l r : List (Pd4cFockCommand T)) (F : (Fin K → List Particle) → ℂ) :
    pd4c_commandsOp T B ν (l ++ r) F = pd4c_commandsOp T B ν l (pd4c_commandsOp T B ν r F) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.cons_append, pd4c_commandsOp, ih]

/-- Any finite sequence of transfers transposes by reversing its commands and exchanging modes. -/
theorem pd4c_commands_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (l : List (Pd4cFockCommand T))
    (F G : (Fin K → List Particle) → ℂ) (hF : Pd4cAdmissibleTest B F) (hG : Pd4cAdmissibleTest B G) :
    pd4c_cubePair T B ν G (pd4c_commandsOp T B ν l F) =
      pd4c_cubePair T B ν F (pd4c_commandsOp T B ν (l.reverse.map pd4c_commandReverse) G) := by
  induction l generalizing F G with
  | nil => exact pd4c_cubePair_comm T B ν G F
  | cons a l ih =>
    rw [pd4c_commandsOp]
    rw [pd4c_command_pairing T B ν a _ G (pd4c_commands_admissible T B ν l F hF) hG]
    rw [pd4c_cubePair_comm T B ν (pd4c_commandsOp T B ν l F)]
    rw [ih F _ hF (pd4c_command_admissible T B ν (pd4c_commandReverse a) G hG)]
    simp only [List.reverse_cons, List.map_append, List.map_singleton, pd4c_commands_append,
      pd4c_commandsOp]

end

end ArtinPrimitiveRoots.TypeII.PD
