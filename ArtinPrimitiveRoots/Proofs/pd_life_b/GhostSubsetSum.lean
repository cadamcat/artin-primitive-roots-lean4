import ArtinPrimitiveRoots.Proofs.pd_life_b.OrderedContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical

noncomputable section

/-- Sum distinct ordered ghost births as a finite sum over subsets of the band. Each
image fiber cancels its factorial, and injectivity bounds the batch length. -/
theorem ghost_birth_subset_sum
    (U : Finset ℕ) (ν : ℕ → ℝ) (a : ℝ) (f : List ℕ → ℂ)
    (hf : ∀ l l', List.Perm l l' → f l = f l') :
    (∑' n : ℕ, ∑ new : Fin n → U,
      if Function.Injective new then
        (((a ^ n * ∏ k, ν (new k).1) / (n.factorial : ℝ) : ℝ) : ℂ) *
          f (List.ofFn fun k => (new k).1)
      else 0) =
      ∑ T ∈ U.powerset,
        ((a ^ T.card * ∏ p ∈ T, ν p : ℝ) : ℂ) * f T.toList := by
  classical
  let v : ℕ → ℝ := fun p => a * ν p
  let image (n : ℕ) (new : Fin n → U) : Finset ℕ :=
    Finset.univ.image fun k => (new k).1
  let term (n : ℕ) (new : Fin n → U) : ℂ :=
    (((∏ k, v (new k).1) / (n.factorial : ℝ) : ℝ) : ℂ) *
      f (List.ofFn fun k => (new k).1)
  let value (T : Finset ℕ) : ℂ := ((∏ p ∈ T, v p : ℝ) : ℂ) * f T.toList
  have hImage (n : ℕ) (new : Fin n → U) : image n new ⊆ U := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    exact (new k).2
  have hCard (n : ℕ) (new : Fin n → U) (hinj : Function.Injective new) :
      (image n new).card = n := by
    have hval : Function.Injective (fun k : Fin n => (new k).1) := by
      intro k k' heq
      exact hinj (Subtype.ext heq)
    dsimp [image]
    rw [Finset.card_image_of_injective _ hval]
    simp
  have hFiber (T : Finset ℕ) (hTU : T ⊆ U) :
      (∑ new : Fin T.card → U,
        if Function.Injective new ∧ image T.card new = T then term T.card new else 0) =
        value T := by
    let P (new : Fin T.card → U) : Prop :=
      Function.Injective new ∧ image T.card new = T
    let A := {new : Fin T.card → U // P new}
    let B := {new : Fin T.card → T // Function.Bijective new}
    let restrict (b : A) : Fin T.card → T := fun k =>
      ⟨(b.1 k).1, by
        have hp : (b.1 k).1 ∈ image T.card b.1 :=
          Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
        exact Eq.mp (congrArg (fun R : Finset ℕ => (b.1 k).1 ∈ R) b.2.2) hp⟩
    have hRestrict (b : A) : Function.Bijective (restrict b) := by
      constructor
      · intro k k' heq
        apply b.2.1
        apply Subtype.ext
        exact congrArg (fun p : T => p.1) heq
      · intro p
        have hp : p.1 ∈ image T.card b.1 := by rw [b.2.2]; exact p.2
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hp
        exact ⟨k, Subtype.ext heq⟩
    let extend (b : B) : Fin T.card → U := fun k => ⟨(b.1 k).1, hTU (b.1 k).2⟩
    have hExtend (b : B) : P (extend b) := by
      constructor
      · intro k k' heq
        apply b.2.injective
        apply Subtype.ext
        exact congrArg (fun p : U => p.1) heq
      · apply Finset.ext
        intro p
        constructor
        · intro hp
          obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hp
          exact heq ▸ (b.1 k).2
        · intro hp
          obtain ⟨k, hk⟩ := b.2.surjective ⟨p, hp⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, congrArg Subtype.val hk⟩
    let e : A ≃ B :=
      { toFun := fun b => ⟨restrict b, hRestrict b⟩
        invFun := fun b => ⟨extend b, hExtend b⟩
        left_inv := by
          intro b
          apply Subtype.ext
          funext k
          apply Subtype.ext
          rfl
        right_inv := by
          intro b
          apply Subtype.ext
          funext k
          apply Subtype.ext
          rfl }
    let termT (new : Fin T.card → T) : ℂ :=
      (((∏ k, v (new k).1) / (T.card.factorial : ℝ) : ℝ) : ℂ) *
        f (List.ofFn fun k => (new k).1)
    have hSubU :
        (∑ new : Fin T.card → U, if P new then term T.card new else 0) =
          ∑ b : A, term T.card b.1 := by
      calc
        _ = ∑ new ∈ (Finset.univ : Finset (Fin T.card → U)).filter P,
              term T.card new := by rw [Finset.sum_filter]
        _ = _ := by
          exact Finset.sum_subtype (p := P) _
            (fun new => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
            (term T.card)
    have hSubT :
        (∑ new : Fin T.card → T,
          if Function.Bijective new then termT new else 0) =
          ∑ b : B, termT b.1 := by
      calc
        _ = ∑ new ∈ (Finset.univ : Finset (Fin T.card → T)).filter Function.Bijective,
              termT new := by rw [Finset.sum_filter]
        _ = _ := by
          exact Finset.sum_subtype (p := Function.Bijective) _
            (fun new => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) termT
    calc
      _ = ∑ b : A, term T.card b.1 := hSubU
      _ = ∑ b : B, termT b.1 := Fintype.sum_equiv e _ _ (fun b => rfl)
      _ = ∑ new : Fin T.card → T,
          if Function.Bijective new then termT new else 0 := hSubT.symm
      _ = value T := ordered_batch_sum_of_perm_invariant T v f hf
  have hGrouped (n : ℕ) :
      (∑ new : Fin n → U, if Function.Injective new then term n new else 0) =
        ∑ T ∈ U.powersetCard n, value T := by
    let Q : Finset (Fin n → U) := Finset.univ.filter Function.Injective
    have hMaps (new : Fin n → U) (hnew : new ∈ Q) :
        image n new ∈ U.powersetCard n :=
      Finset.mem_powersetCard.mpr ⟨hImage n new, hCard n new (Finset.mem_filter.mp hnew).2⟩
    calc
      _ = ∑ new ∈ Q, term n new := by rw [Finset.sum_filter]
      _ = ∑ T ∈ U.powersetCard n,
            ∑ new ∈ Q.filter (fun new => image n new = T), term n new :=
        (Finset.sum_fiberwise_of_maps_to hMaps (term n)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T hT
        obtain ⟨hTU, hTcard⟩ := Finset.mem_powersetCard.mp hT
        subst n
        dsimp [Q]
        rw [Finset.filter_filter, Finset.sum_filter]
        exact hFiber T hTU
  have hSupport (n : ℕ) (hn : n ∉ Finset.range (U.card + 1)) :
      (∑ new : Fin n → U, if Function.Injective new then term n new else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro new hnew
    have hNot : ¬ Function.Injective new := by
      intro hinj
      have hle : n ≤ U.card := by
        rw [← hCard n new hinj]
        exact Finset.card_le_card (hImage n new)
      exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    exact if_neg hNot
  calc
    _ = ∑' n : ℕ, ∑ new : Fin n → U,
          if Function.Injective new then term n new else 0 := by
      apply tsum_congr
      intro n
      apply Finset.sum_congr rfl
      intro new hnew
      have hProd : (∏ k : Fin n, v (new k).1) = a ^ n * ∏ k, ν (new k).1 := by
        simp only [v, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
      simp only [term, hProd]
    _ = ∑ n ∈ Finset.range (U.card + 1),
          ∑ new : Fin n → U, if Function.Injective new then term n new else 0 :=
      tsum_eq_sum hSupport
    _ = ∑ n ∈ Finset.range (U.card + 1), ∑ T ∈ U.powersetCard n, value T := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hGrouped n
    _ = ∑ T ∈ U.powerset, value T := by
      rw [Finset.powerset_card_biUnion]
      exact (Finset.sum_biUnion (f := value) (by
        intro i hi j hj hij
        exact Finset.disjoint_powersetCard_of_ne hij U U)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      simp only [value, v, Finset.prod_mul_distrib, Finset.prod_const]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
