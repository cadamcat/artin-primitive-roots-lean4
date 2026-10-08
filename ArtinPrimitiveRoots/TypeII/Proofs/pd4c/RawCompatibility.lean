import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawOmissionFiber

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A nonzero admissible raw edge supplies the fixed-anchor compatibility data. -/
theorem raw_edge_compatible {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (I : Finset (Fin K)) (iStar : Fin K) (hstar : iStar ∈ I)
    (k : Fin (s.2.2 iStar).length) (hk : (c iStar).2 = Sum.inl k)
    (fresh : Fin K → ℕ) (hfresh : ∀ i, i ∉ I → fresh i = edgeNewLabel (c i))
    (w : ArchRoot) (forward : Bool) (z' : ℤ × ℤ)
    (hadm : EdgeAdmissible F S w (s.1, permuteLists σ s.2.1, s.2.2) c z')
    (hraw : edgeMultiplier F S forward true (permuteLists σ s.2.1)
      (edgeTargetLists F S (s.1, permuteLists σ s.2.1, s.2.2) c) s.1 z' ≠ 0) :
    RawAnchorCompatible S F.a s.2.1 I iStar fresh w
      ((s.2.2 iStar).get k) s.1 (fun i => σ i (lastSlot S.x)) := by
  let t : MemPoint S.x K := (s.1, permuteLists σ s.2.1, s.2.2)
  let q := edgeTargetLists F S t c
  obtain ⟨hHits, hSource, hTarget, hTransition, hPad, hPrimitive,
    hBox, hBox', hGood, hGood'⟩ := hadm
  have hlast (i : Fin K) : q i (lastSlot S.x) = edgeNewLabel (c i) := by
    simp [q, edgeTargetLists, lastSlot]
  have hstarLabel : edgeNewLabel (c iStar) = ((s.2.2 iStar).get k).1 := by
    simp [edgeNewLabel, hk]
  have hslot (j : Fin (slotCount S.x)) : j.val < momentJ S.x ↔ j ≠ lastSlot S.x := by
    have hj := j.isLt
    change j.val < momentJ S.x + 1 at hj
    constructor
    · intro hlt heq
      have heqval := congrArg Fin.val heq
      simp only [lastSlot] at heqval
      omega
    · intro hne
      by_contra hnot
      have heq : j = lastSlot S.x := by
        apply Fin.ext
        simp only [lastSlot]
        omega
      exact hne heq
  have hshared : sharedProduct (permuteLists σ s.2.1) =
      omissionProduct s.2.1 (fun i => σ i (lastSlot S.x)) := by
    rw [← pd4c_omissionProduct_permuteLists s.2.1 σ (fun _ => lastSlot S.x)]
    unfold sharedProduct omissionProduct
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    simp only [hslot]
  let Z := ∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then edgeNewLabel (c i) else 1
  let T := ∏ i : Fin K, if i ∉ I then fresh i else 1
  have hfactor : lastProduct q = ((s.2.2 iStar).get k).1 * Z * T := by
    have hpoint (i : Fin K) : edgeNewLabel (c i) =
        (if i = iStar then ((s.2.2 iStar).get k).1 else 1) *
          (if i ∈ I ∧ i ≠ iStar then edgeNewLabel (c i) else 1) *
          (if i ∉ I then fresh i else 1) := by
      by_cases hi : i = iStar
      · subst i
        simp [hstar, hstarLabel]
      · by_cases hmem : i ∈ I
        · simp [hi, hmem]
        · simp [hi, hmem, hfresh i hmem]
    calc
      _ = ∏ i : Fin K, edgeNewLabel (c i) := by
        unfold lastProduct
        exact Finset.prod_congr rfl (fun i hi => hlast i)
      _ = ∏ i : Fin K,
          (if i = iStar then ((s.2.2 iStar).get k).1 else 1) *
            (if i ∈ I ∧ i ≠ iStar then edgeNewLabel (c i) else 1) *
            (if i ∉ I then fresh i else 1) :=
        Finset.prod_congr rfl (fun i hi => hpoint i)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, Z, T]
  refine ⟨fun i => edgeNewLabel (c i), z', ?_, ?_, ?_, ?_, hBox', hHits iStar k hk, ?_⟩
  · intro i hi
    have h := (hTarget.1 i (lastSlot S.x)).2
    change q i (lastSlot S.x) ∈ primeBand S.x (F.a i) at h
    rwa [hlast] at h
  · intro i hi j jj
    have h := hTransition.2 i j ((σ j).symm jj)
    change q i (lastSlot S.x) ≠ s.2.1 j (σ j ((σ j).symm jj)) at h
    simpa only [hlast, Equiv.apply_symm_apply] using h
  · simpa only [hshared] using hPad.1
  · simpa only [hshared] using hPad.2.1
  · have hd := pd4c_raw_edge_det_full F S forward (permuteLists σ s.2.1) q s.1 z'
      hPad.2.2 hraw
    rw [pd4c_fullPrimeProduct_permute, hshared, hfactor] at hd
    calc
      _ = (pd4c_fullPrimeProduct s.2.1 : ℤ) -
          (omissionProduct s.2.1 (fun i => σ i (lastSlot S.x)) : ℤ) *
            (((s.2.2 iStar).get k).1 * Z * T : ℕ) := hd
      _ = _ := by
        dsimp only [Z, T]
        push_cast
        ring

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
