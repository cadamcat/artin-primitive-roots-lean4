import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostSubsetSum

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Cancel the ordered batch factorials simultaneously in every group, retaining any
continuation invariant under the separate batch permutations. -/
theorem ghost_birth_subset_sum_pi (K : ℕ) (U : Fin K → Finset ℕ)
    (ν : Fin K → ℕ → ℝ) (a : Fin K → ℝ)
    (f : (Fin K → List ℕ) → ℂ)
    (hf : ∀ l m, (∀ i, (l i).Perm (m i)) → f l = f m) :
    (∑' n : Fin K → ℕ,
      ∑ new : (i : Fin K) → Fin (n i) → U i,
        if ∀ i, Function.Injective (new i) then
          ((∏ i : Fin K,
              (a i ^ n i * ∏ k, ν i (new i k).1) / ((n i).factorial : ℝ) : ℝ) : ℂ) *
            f (fun i => List.ofFn fun k => (new i k).1)
        else 0) =
      ∑ T : (i : Fin K) → (U i).powerset,
        ((∏ i : Fin K, a i ^ (T i).1.card * ∏ p ∈ (T i).1, ν i p : ℝ) : ℂ) *
          f (fun i => (T i).1.toList) := by
  classical
  let I := (i : Fin K) → (U i).powerset
  let v : Fin K → ℕ → ℝ := fun i p => a i * ν i p
  let cardVec (T : I) : Fin K → ℕ := fun i => (T i).1.card
  let image (n : Fin K → ℕ) (new : (i : Fin K) → Fin (n i) → U i) : I :=
    fun i => ⟨Finset.univ.image (fun k => (new i k).1), by
      apply Finset.mem_powerset.mpr
      intro p hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
      exact (new i k).2⟩
  let term (n : Fin K → ℕ) (new : (i : Fin K) → Fin (n i) → U i) : ℂ :=
    ((∏ i : Fin K, (∏ k, v i (new i k).1) / ((n i).factorial : ℝ) : ℝ) : ℂ) *
      f (fun i => List.ofFn fun k => (new i k).1)
  let value (T : I) : ℂ :=
    ((∏ i : Fin K, ∏ p ∈ (T i).1, v i p : ℝ) : ℂ) * f (fun i => (T i).1.toList)
  have hCard (n : Fin K → ℕ) (new : (i : Fin K) → Fin (n i) → U i)
      (hinj : ∀ i, Function.Injective (new i)) (i : Fin K) :
      (image n new i).1.card = n i := by
    have hval : Function.Injective (fun k => (new i k).1) :=
      Subtype.val_injective.comp (hinj i)
    dsimp [image]
    rw [Finset.card_image_of_injective _ hval]
    simp
  have hFiber (n : Fin K → ℕ) (T : I) :
      (∑ new : (i : Fin K) → Fin (n i) → U i,
        if (∀ i, Function.Injective (new i)) ∧ image n new = T then term n new else 0) =
      if n = cardVec T then value T else 0 := by
    by_cases hn : n = cardVec T
    · subst n
      rw [ite_eq_left rfl]
      let P (new : (i : Fin K) → Fin (cardVec T i) → U i) : Prop :=
        (∀ i, Function.Injective (new i)) ∧ image (cardVec T) new = T
      let A := {new : (i : Fin K) → Fin (cardVec T i) → U i // P new}
      let C (i : Fin K) :=
        {new : Fin (T i).1.card → (T i).1 // Function.Bijective new}
      let B := (i : Fin K) → C i
      let restrict (b : A) (i : Fin K) : Fin (T i).1.card → (T i).1 := fun k =>
        ⟨(b.1 i k).1, by
          have hp : (b.1 i k).1 ∈ (image (cardVec T) b.1 i).1 :=
            Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
          exact Eq.mp
            (congrArg (fun R : I => (b.1 i k).1 ∈ (R i).1) b.2.2) hp⟩
      have hRestrict (b : A) (i : Fin K) : Function.Bijective (restrict b i) := by
        constructor
        · intro k k' heq
          apply b.2.1 i
          apply Subtype.ext
          exact congrArg (fun p : (T i).1 => p.1) heq
        · intro p
          have hp : p.1 ∈ (image (cardVec T) b.1 i).1 := by rw [b.2.2]; exact p.2
          obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hp
          exact ⟨k, Subtype.ext heq⟩
      let extend (b : B) (i : Fin K) : Fin (cardVec T i) → U i := fun k =>
        ⟨((b i).1 k).1, (Finset.mem_powerset.mp (T i).2) ((b i).1 k).2⟩
      have hExtend (b : B) : P (extend b) := by
        constructor
        · intro i k k' heq
          apply (b i).2.injective
          apply Subtype.ext
          exact congrArg (fun p : U i => p.1) heq
        · funext i
          apply Subtype.ext
          apply Finset.ext
          intro p
          constructor
          · intro hp
            obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hp
            exact heq ▸ ((b i).1 k).2
          · intro hp
            obtain ⟨k, hk⟩ := (b i).2.surjective ⟨p, hp⟩
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, congrArg Subtype.val hk⟩
      let e : A ≃ B :=
        { toFun := fun b i => ⟨restrict b i, hRestrict b i⟩
          invFun := fun b => ⟨extend b, hExtend b⟩
          left_inv := by
            intro b
            apply Subtype.ext
            funext i k
            apply Subtype.ext
            rfl
          right_inv := by
            intro b
            funext i
            apply Subtype.ext
            funext k
            apply Subtype.ext
            rfl }
      let weight (i : Fin K) (b : C i) : ℝ :=
        (∏ k, v i (b.1 k).1) / ((T i).1.card.factorial : ℝ)
      let termT (b : B) : ℂ :=
        ((∏ i : Fin K, weight i (b i) : ℝ) : ℂ) *
          f (fun i => List.ofFn fun k => ((b i).1 k).1)
      have hSubU :
          (∑ new : (i : Fin K) → Fin (cardVec T i) → U i,
            if P new then term (cardVec T) new else 0) =
          ∑ b : A, term (cardVec T) b.1 := by
        calc
          _ = ∑ new ∈ (Finset.univ : Finset ((i : Fin K) → Fin (cardVec T i) → U i)).filter P,
                term (cardVec T) new := by rw [Finset.sum_filter]
          _ = _ := Finset.sum_subtype (p := P) _
            (fun new => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
            (term (cardVec T))
      have hList (b : B) :
          f (fun i => List.ofFn fun k => ((b i).1 k).1) = f (fun i => (T i).1.toList) := by
        apply hf
        intro i
        have hNodup : (List.ofFn fun k => ((b i).1 k).1).Nodup :=
          List.nodup_ofFn.mpr (Subtype.val_injective.comp (b i).2.injective)
        apply (List.perm_ext_iff_of_nodup hNodup (T i).1.nodup_toList).mpr
        intro p
        constructor
        · intro hp
          obtain ⟨k, hk⟩ := List.mem_ofFn.mp hp
          exact Finset.mem_toList.mpr (hk ▸ ((b i).1 k).2)
        · intro hp
          have hpT : p ∈ (T i).1 := Finset.mem_toList.mp hp
          obtain ⟨k, hk⟩ := (b i).2.surjective ⟨p, hpT⟩
          exact List.mem_ofFn.mpr ⟨k, congrArg Subtype.val hk⟩
      have hScalar :
          (∑ b : B, ∏ i : Fin K, weight i (b i)) =
            ∏ i : Fin K, ∏ p ∈ (T i).1, v i p := by
        calc
          _ = ∏ i : Fin K, ∑ b : C i, weight i b := by
            rw [← Fintype.piFinset_univ]
            simpa using
              (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (C i))) weight).symm
          _ = _ := by
            apply Finset.prod_congr rfl
            intro i _
            have hSubT :
                (∑ new : Fin (T i).1.card → (T i).1,
                  if Function.Bijective new then
                    (∏ k, v i (new k).1) / ((T i).1.card.factorial : ℝ) else 0) =
                ∑ b : C i, weight i b := by
              calc
                _ = ∑ new ∈ (Finset.univ : Finset (Fin (T i).1.card → (T i).1)).filter
                      Function.Bijective,
                      (∏ k, v i (new k).1) / ((T i).1.card.factorial : ℝ) := by
                    rw [Finset.sum_filter]
                _ = _ := Finset.sum_subtype (p := Function.Bijective) _
                  (fun new => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
                  (fun new : Fin (T i).1.card → (T i).1 =>
                    (∏ k, v i (new k).1) / ((T i).1.card.factorial : ℝ))
            rw [← hSubT, pd_ordered_distinct_batch_sum]
      calc
        _ = ∑ b : A, term (cardVec T) b.1 := hSubU
        _ = ∑ b : B, termT b := Fintype.sum_equiv e _ _ (fun b => rfl)
        _ = ∑ b : B, ((∏ i : Fin K, weight i (b i) : ℝ) : ℂ) *
              f (fun i => (T i).1.toList) := by
          apply Finset.sum_congr rfl
          intro b _
          simp only [termT, hList b]
        _ = ((∑ b : B, ∏ i : Fin K, weight i (b i) : ℝ) : ℂ) *
              f (fun i => (T i).1.toList) := by
          push_cast
          rw [Finset.sum_mul]
        _ = value T := by rw [hScalar]
    · rw [ite_eq_right hn]
      apply Finset.sum_eq_zero
      intro new _
      by_cases hnew : (∀ i, Function.Injective (new i)) ∧ image n new = T
      · have heq : n = cardVec T := by
          funext i
          have hc := hCard n new hnew.1 i
          rw [hnew.2] at hc
          exact hc.symm
        exact (hn heq).elim
      · exact ite_eq_right hnew
  have hGrouped (n : Fin K → ℕ) :
      (∑ new : (i : Fin K) → Fin (n i) → U i,
        if ∀ i, Function.Injective (new i) then term n new else 0) =
      ∑ T : I, if n = cardVec T then value T else 0 := by
    let Q : Finset ((i : Fin K) → Fin (n i) → U i) :=
      Finset.univ.filter fun new => ∀ i, Function.Injective (new i)
    have hMaps (new : (i : Fin K) → Fin (n i) → U i) (hnew : new ∈ Q) :
        image n new ∈ (Finset.univ : Finset I) := Finset.mem_univ _
    calc
      _ = ∑ new ∈ Q, term n new := by rw [Finset.sum_filter]
      _ = ∑ T : I, ∑ new ∈ Q.filter (fun new => image n new = T), term n new :=
        (Finset.sum_fiberwise_of_maps_to hMaps (term n)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T _
        dsimp [Q]
        rw [Finset.filter_filter, Finset.sum_filter]
        exact hFiber n T
  let support : Finset (Fin K → ℕ) := Finset.univ.image cardVec
  calc
    _ = ∑' n : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (n i) → U i,
          if ∀ i, Function.Injective (new i) then term n new else 0 := by
      apply tsum_congr
      intro n
      apply Finset.sum_congr rfl
      intro new _
      have hProd (i : Fin K) :
          (∏ k : Fin (n i), v i (new i k).1) = a i ^ n i * ∏ k, ν i (new i k).1 := by
        simp only [v, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
      simp only [term, hProd]
    _ = ∑' n : Fin K → ℕ, ∑ T : I, if n = cardVec T then value T else 0 :=
      tsum_congr hGrouped
    _ = ∑ n ∈ support, ∑ T : I, if n = cardVec T then value T else 0 := by
      apply tsum_eq_sum
      intro n hn
      apply Finset.sum_eq_zero
      intro T _
      apply ite_eq_right
      intro hEq
      exact hn (Finset.mem_image.mpr ⟨T, Finset.mem_univ _, hEq.symm⟩)
    _ = ∑ T : I, ∑ n ∈ support, if n = cardVec T then value T else 0 :=
      Finset.sum_comm
    _ = ∑ T : I, value T := by
      apply Finset.sum_congr rfl
      intro T _
      have hmem : cardVec T ∈ support := Finset.mem_image.mpr ⟨T, Finset.mem_univ _, rfl⟩
      simp only [Finset.sum_ite_eq', hmem, ite_eq_left]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [value, v, Finset.prod_mul_distrib, Finset.prod_const]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
