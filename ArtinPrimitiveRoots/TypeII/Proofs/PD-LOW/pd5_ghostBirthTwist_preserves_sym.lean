import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.Proofs.pd5_low_b.MemoryPermutation

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Indexed deletion choices transport under source memory permutations, while the local
fresh log stays unchanged. Guide `runs/lanes/sol-thin-pd5/PROOFS.md:667–696`; uses
MemoryPermutation, removeIndices and symmetric continuations; feeds modified operation bounds. -/
theorem pd5_ghostBirthTwist_preserves_sym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ)
    (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (pd5_ghostBirthTwist F S ρ j W f) := by
  classical
  intro s τ
  let t := memoryPermute s τ
  let e : (i : Fin K) → Fin (t.2.2 i).length ≃ Fin (s.2.2 i).length := fun i =>
    (finCastEquiv (by simp [t, memoryPermute])).trans (τ i)
  let DEquiv : (∀ i : Fin K, Finset (Fin (t.2.2 i).length)) ≃
      (∀ i : Fin K, Finset (Fin (s.2.2 i).length)) :=
    Equiv.piCongrRight fun i => finsetImageEquiv (e i)
  have hhit (i : Fin K) :
      hitIndices (t.2.2 i) t.1 = (hitIndices (s.2.2 i) s.1).image (e i).symm := by
    change hitIndices (List.ofFn fun j : Fin (s.2.2 i).length => (s.2.2 i).get ((τ i) j)) s.1 =
      (hitIndices (s.2.2 i) s.1).image (e i).symm
    rw [hitIndices_reindex]
    apply Finset.image_congr
    intro a ha
    apply Fin.ext
    rfl
  have hcount (i : Fin K) :
      hitCount (t.2.2 i) t.1 = hitCount (s.2.2 i) s.1 := by
    rw [hitCount, hhit i]
    exact Finset.card_image_of_injective _ (e i).symm.injective
  have hDsrc (D : ∀ i : Fin K, Finset (Fin (t.2.2 i).length)) :
      DEquiv D = fun i => (D i).image (e i) := by
    funext i
    simp [DEquiv, finsetImageEquiv]
  have hDcard (D : ∀ i : Fin K, Finset (Fin (t.2.2 i).length)) (i : Fin K) :
      (DEquiv D i).card = (D i).card := by
    rw [hDsrc]
    exact Finset.card_image_of_injective _ (e i).injective
  have hsubset (D : ∀ i : Fin K, Finset (Fin (t.2.2 i).length)) (i : Fin K) :
      D i ⊆ hitIndices (t.2.2 i) t.1 ↔
        DEquiv D i ⊆ hitIndices (s.2.2 i) s.1 := by
    rw [hhit i, hDsrc D]
    constructor
    · intro h a ha
      rcases Finset.mem_image.mp ha with ⟨b, hb, rfl⟩
      have hbHit : b ∈ (hitIndices (s.2.2 i) s.1).image (e i).symm := h hb
      rcases Finset.mem_image.mp hbHit with ⟨c, hc, hcb⟩
      have hce : c = e i b := by
        calc
          c = e i ((e i).symm c) := by simp
          _ = e i b := congrArg (e i) hcb
      have hbe : e i b ∈ hitIndices (s.2.2 i) s.1 := by rw [← hce]; exact hc
      exact hbe
    · intro h b hb
      have heb : e i b ∈ DEquiv D i := by
        rw [hDsrc D]
        exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
      have hbhit : e i b ∈ hitIndices (s.2.2 i) s.1 := h heb
      exact Finset.mem_image.mpr ⟨e i b, hbhit, (e i).symm_apply_apply b⟩
  have hcondition (D : ∀ i : Fin K, Finset (Fin (t.2.2 i).length)) :
      (∀ i, D i ⊆ hitIndices (t.2.2 i) t.1) ↔
        (∀ i, DEquiv D i ⊆ hitIndices (s.2.2 i) s.1) := by
    constructor
    · intro h i
      exact (hsubset D i).mp (h i)
    · intro h i
      exact (hsubset D i).mpr (h i)
  simp only [pd5_ghostBirthTwist, logGhost, plainOp]
  apply Fintype.sum_equiv DEquiv
  intro D
  apply tsum_congr
  intro l
  apply Fintype.sum_congr
  intro new
  have hD : (∀ i, D i ⊆ hitIndices (t.2.2 i) t.1) ↔
      (∀ i, DEquiv D i ⊆ hitIndices (s.2.2 i) s.1) := hcondition D
  have hrem (i : Fin K) :
      List.Perm (removeIndices (t.2.2 i) (D i))
        (removeIndices (s.2.2 i) (DEquiv D i)) := by
    obtain ⟨D', hrel, hcard', hperm⟩ :=
      removeIndices_reindex_perm (s.2.2 i) (τ i) (DEquiv D i)
    have hD' : D' = D i := by
      ext k
      rw [hrel]
      simp [DEquiv, finsetImageEquiv, e, finCastEquiv]
      constructor
      · rintro ⟨a, ha, hak⟩
        have haval : a.val = k.val := by
          have hval := congrArg Fin.val hak
          simpa using hval
        exact (Fin.ext haval) ▸ ha
      · intro hk
        exact ⟨k, hk, by apply Fin.ext; rfl⟩
    rw [hD'] at hperm
    simpa [t, memoryPermute] using hperm
  let qT : MemPoint S.x K :=
    (t.1, t.2.1, fun i => removeIndices (t.2.2 i) (D i) ++
      List.ofFn fun k : Fin (l i) => anchorAt (new i k) t.1)
  let qS : MemPoint S.x K :=
    (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (DEquiv D i) ++
      List.ofFn fun k : Fin (l i) => anchorAt (new i k) s.1)
  have hq : f qT = f qS := by
    apply memorySymmetric_eq_of_lists_perm f hf qS qT rfl rfl
    intro i
    have happend := (hrem i).append_right
      (List.ofFn fun k : Fin (l i) => anchorAt (new i k) t.1)
    simpa [qT, qS, t, memoryPermute] using happend.symm
  have hcount' (i : Fin K) :
      hitCount ((memoryPermute s τ).2.2 i) (memoryPermute s τ).1 =
        hitCount (s.2.2 i) s.1 := by
    simpa [t] using hcount i
  have hq' :
      f ((memoryPermute s τ).1, (memoryPermute s τ).2.1, fun i =>
        removeIndices ((memoryPermute s τ).2.2 i) (D i) ++
          List.ofFn fun k : Fin (l i) => anchorAt (new i k) (memoryPermute s τ).1) =
      f (s.1, s.2.1, fun i =>
        removeIndices (s.2.2 i) (DEquiv D i) ++
          List.ofFn fun k : Fin (l i) => anchorAt (new i k) s.1) := by
    simpa [qT, qS, t] using hq
  by_cases hvalid : ∀ i, D i ⊆ hitIndices (t.2.2 i) t.1
  · have hvalid' : ∀ i, DEquiv D i ⊆ hitIndices (s.2.2 i) s.1 := hD.mp hvalid
    rw [if_pos hvalid, if_pos hvalid']
    simp_rw [hcount', hDcard, hq']
  · have hvalid' : ¬ ∀ i, DEquiv D i ⊆ hitIndices (s.2.2 i) s.1 :=
      fun h => hvalid (hD.mpr h)
    rw [if_neg hvalid, if_neg hvalid']

end
end ArtinPrimitiveRoots.TypeII.PD
