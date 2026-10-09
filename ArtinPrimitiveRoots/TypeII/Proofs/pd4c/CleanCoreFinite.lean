import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CleanCore

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD
open scoped BigOperators

noncomputable section

/-- Finite supported clean cores retain exactly the full physical admissibility conditions. -/
theorem clean_core_finite_formula {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ)
    (I : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hf : ∀ t, t ∉ I → f t = 0) (s : MemPoint S.x K) :
    let μ := fun t : MemPoint S.x K =>
      ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))
    let adm := fun t : MemPoint S.x K =>
      s.2.2 = t.2.2 ∧
      ValidPrimeLists S.x K F.a s.2.1 ∧ ValidPrimeLists S.x K F.a t.2.1 ∧
      IsSlotTransition s.2.1 t.2.1 ∧
      IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 t.1) ∧
      Int.gcd t.1.1 t.1.2 = 1 ∧ envBox S w s.1 ∧ envBox S w t.1 ∧
      envGood F S w (s.1, s.2.1) ∧ envGood F S w (t.1, t.2.1)
    let k := fun t : MemPoint S.x K =>
      if decide (j % 2 = 0) then
        geometricMultiplier F S (sharedProduct s.2.1) (lastProduct t.2.1)
          (lastProduct s.2.1) (det2 s.1 t.1/(sharedProduct s.2.1 : ℤ))
      else star (geometricMultiplier F S (sharedProduct s.2.1) (lastProduct s.2.1)
        (lastProduct t.2.1) (det2 t.1 s.1/(sharedProduct s.2.1 : ℤ)))
    plainOp (logEdgePiece F S ρ w j true ∅ ∅) f s -
      plainOp (logEdgePiece F S ρ w j false ∅ ∅) f s =
      (ρ^(∑ i : Fin K, hitCount (s.2.2 i) s.1) : ℂ)*
        (∑ t ∈ I, if adm t then k t*(μ t : ℂ)*
          (ρ^(∑ i : Fin K, hitCount (t.2.2 i) t.1) : ℂ)*f t else 0) := by
  classical
  let μ := fun t : MemPoint S.x K =>
    ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (t.2.1 i (lastSlot S.x))
  let adm := fun t : MemPoint S.x K =>
    s.2.2 = t.2.2 ∧
    ValidPrimeLists S.x K F.a s.2.1 ∧ ValidPrimeLists S.x K F.a t.2.1 ∧
    IsSlotTransition s.2.1 t.2.1 ∧
    IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 t.1) ∧
    Int.gcd t.1.1 t.1.2 = 1 ∧ envBox S w s.1 ∧ envBox S w t.1 ∧
    envGood F S w (s.1, s.2.1) ∧ envGood F S w (t.1, t.2.1)
  let k := fun t : MemPoint S.x K =>
    if decide (j % 2 = 0) then
      geometricMultiplier F S (sharedProduct s.2.1) (lastProduct t.2.1)
        (lastProduct s.2.1) (det2 s.1 t.1/(sharedProduct s.2.1 : ℤ))
    else star (geometricMultiplier F S (sharedProduct s.2.1) (lastProduct s.2.1)
      (lastProduct t.2.1) (det2 t.1 s.1/(sharedProduct s.2.1 : ℤ)))
  let h := fun t : MemPoint S.x K => (ρ^(∑ i : Fin K, hitCount (t.2.2 i) t.1) : ℂ)
  change plainOp (logEdgePiece F S ρ w j true ∅ ∅) f s -
    plainOp (logEdgePiece F S ρ w j false ∅ ∅) f s =
      h s*(∑ t ∈ I, if adm t then k t*(μ t : ℂ)*h t*f t else 0)
  let X := (i : Fin K) → primeBand S.x (F.a i)
  let χ : X → (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i :=
    fun p i => (false, Sum.inr (p i))
  let out : X → (ℤ × ℤ) → MemPoint S.x K :=
    fun p z => (z, edgeTargetLists F S s (χ p), s.2.2)
  have hlast (p : X) (z : ℤ × ℤ) (i : Fin K) :
      (out p z).2.1 i (lastSlot S.x) = (p i : ℕ) := by
    simp only [out, edgeTargetLists, lastSlot, χ, lt_self_iff_false, if_false, edgeNewLabel]
  have hadm (p : X) (z : ℤ × ℤ) :
      EdgeAdmissible F S w s (χ p) z ↔ adm (out p z) := by
    simp [EdgeAdmissible, adm, out, χ]
  have hinj : Function.Injective (fun a : X × (ℤ × ℤ) => out a.1 a.2) := by
    intro a b hab
    apply Prod.ext
    · funext i
      apply Subtype.ext
      have hh := congrArg (fun t : MemPoint S.x K => t.2.1 i (lastSlot S.x)) hab
      simpa only [hlast] using hh
    · exact congrArg (fun t : MemPoint S.x K => t.1) hab
  let Z := I.image (fun t => t.1)
  let A := ((Finset.univ : Finset X).product Z).filter fun a =>
    out a.1 a.2 ∈ I ∧ EdgeAdmissible F S w s (χ a.1) a.2
  let B := I.filter adm
  have hreindex (Φ : MemPoint S.x K → ℂ) (hΦ : ∀ t, t ∉ I → Φ t = 0) :
      (∑ p : X, ∑' z : ℤ × ℤ,
        if EdgeAdmissible F S w s (χ p) z then Φ (out p z) else 0) =
        ∑ t ∈ I, if adm t then Φ t else 0 := by
    calc
      _ = ∑ p : X, ∑ z ∈ Z,
          if EdgeAdmissible F S w s (χ p) z then Φ (out p z) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply tsum_eq_sum
        intro z hz
        by_cases ha : EdgeAdmissible F S w s (χ p) z
        · rw [if_pos ha]
          apply hΦ
          intro ho
          apply hz
          exact Finset.mem_image.mpr ⟨out p z, ho, rfl⟩
        · exact if_neg ha
      _ = ∑ a ∈ (Finset.univ : Finset X).product Z,
          if EdgeAdmissible F S w s (χ a.1) a.2 then Φ (out a.1 a.2) else 0 := by
        exact (Finset.sum_product' _ _ (fun p z =>
          if EdgeAdmissible F S w s (χ p) z then Φ (out p z) else 0)).symm
      _ = ∑ a ∈ A, Φ (out a.1 a.2) := by
        dsimp only [A]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases ho : out a.1 a.2 ∈ I
        · by_cases he : EdgeAdmissible F S w s (χ a.1) a.2 <;> simp only [ho, he, true_and, false_and, if_true, if_false]
        · simp only [ho, false_and, if_false, hΦ _ ho, ite_self]
      _ = ∑ t ∈ B, Φ t := by
        apply Finset.sum_bij (fun a ha => out a.1 a.2)
        · intro a ha
          obtain ⟨_, ho, he⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨ho, (hadm _ _).mp he⟩
        · intro a ha b hb heq
          exact hinj heq
        · intro t ht
          obtain ⟨htI, htadm⟩ := Finset.mem_filter.mp ht
          have htvalid : ValidPrimeLists S.x K F.a t.2.1 := htadm.2.2.1
          have hslot : IsSlotTransition s.2.1 t.2.1 := htadm.2.2.2.1
          let p : X := fun i => ⟨t.2.1 i (lastSlot S.x), (htvalid.1 i (lastSlot S.x)).2⟩
          have hlabels : edgeTargetLists F S s (χ p) = t.2.1 := by
            funext i jj
            by_cases hjj : jj.val < momentJ S.x
            · simp only [edgeTargetLists, if_pos hjj]
              exact (hslot.1 i jj hjj).symm
            · have hjlast : jj = lastSlot S.x := by
                apply Fin.ext
                have hjlt := jj.isLt
                dsimp only [slotCount] at hjlt
                dsimp only [lastSlot]
                omega
              subst jj
              change (out p t.1).2.1 i (lastSlot S.x) = _
              rw [hlast]
          have hout : out p t.1 = t := by
            apply Prod.ext
            · rfl
            · exact Prod.ext hlabels htadm.1
          refine ⟨(p, t.1), ?_, hout⟩
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
            Finset.mem_image.mpr ⟨t, htI, rfl⟩⟩, ?_, ?_⟩
          · simpa only [hout] using htI
          · exact (hadm p t.1).mpr (by simpa only [hout] using htadm)
        · intro a ha
          rfl
      _ = _ := by dsimp only [B]; rw [Finset.sum_filter]
  let Φ := fun (raw : Bool) (t : MemPoint S.x K) =>
    h s*(μ t : ℂ)*h t*edgeMultiplier F S (decide (j % 2 = 0)) raw s.2.1 t.2.1 s.1 t.1*f t
  have hμ (p : X) (z : ℤ × ℤ) :
      μ (out p z) = ∏ i : Fin K, memoryNu S.x K F.a F.q_d i (p i) := by
    dsimp only [μ]
    exact Finset.prod_congr rfl (fun i hi => by rw [hlast])
  have hpart (raw : Bool) : plainOp (logEdgePiece F S ρ w j raw ∅ ∅) f s =
      ∑ t ∈ I, if adm t then Φ raw t else 0 := by
    rw [clean_core_fresh_formula]
    calc
      _ = ∑ p : X, ∑' z : ℤ × ℤ,
          if EdgeAdmissible F S w s (χ p) z then Φ raw (out p z) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply tsum_congr
        intro z
        by_cases he : EdgeAdmissible F S w s (χ p) z
        · rw [if_pos he, if_pos he]
          dsimp only [Φ]
          rw [hμ]
          dsimp only [h, out]
          push_cast
          ring
        · rw [if_neg he, if_neg he]
      _ = _ := hreindex (Φ raw) (fun t ht => by dsimp only [Φ]; rw [hf t ht, mul_zero])
  have hmult (t : MemPoint S.x K) :
      edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1 t.2.1 s.1 t.1 -
      edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1 t.2.1 s.1 t.1 = k t := by
    dsimp only [edgeMultiplier, k, geometricMultiplier]
    cases he : decide (j % 2 = 0) <;> simp only [he, Bool.false_eq_true, if_false, if_true, star_sub]
  rw [hpart true, hpart false, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases ha : adm t
  · simp only [if_pos ha]
    dsimp only [Φ]
    calc
      _ = h s*(μ t : ℂ)*h t*
          (edgeMultiplier F S (decide (j % 2 = 0)) true s.2.1 t.2.1 s.1 t.1 -
           edgeMultiplier F S (decide (j % 2 = 0)) false s.2.1 t.2.1 s.1 t.1)*f t := by ring
      _ = _ := by rw [hmult]; ring
  · simp only [if_neg ha, sub_self, mul_zero]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
