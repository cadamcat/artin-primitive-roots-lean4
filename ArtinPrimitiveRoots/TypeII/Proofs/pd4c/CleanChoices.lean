import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A clean edge choice is exactly a fresh tuple, with no memory-index multiplicity. -/
theorem clean_choice_sum_reindex {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (s : MemPoint x K)
    (Φ : ((i : Fin K) → EdgeChoice x a (s.2.2 i) i) → ℂ) :
    (∑ c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i,
      if edgeStoredSet (s := s) c = ∅ ∧ edgePromotedSet (s := s) c = ∅ then Φ c else 0) =
      ∑ p : (i : Fin K) → primeBand x (a i),
        Φ (fun i => (false, Sum.inr (p i))) := by
  let E := (i : Fin K) → primeBand x (a i)
  let C : Finset ((i : Fin K) → EdgeChoice x a (s.2.2 i) i) :=
    Finset.univ.filter fun c =>
      edgeStoredSet (s := s) c = ∅ ∧ edgePromotedSet (s := s) c = ∅
  let χ (p : E) : (i : Fin K) → EdgeChoice x a (s.2.2 i) i :=
    fun i => (false, Sum.inr (p i))
  have hpattern (p : E) : χ p ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · ext i
      simp [χ, edgeStoredSet]
    · ext i
      simp [χ, edgePromotedSet]
  have hinj : Function.Injective χ := by
    intro p q heq
    funext i
    have h := congrArg (fun c => (c i).2) heq
    simpa only [χ, Sum.inr.injEq] using h
  have hsurj (c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i) (hc : c ∈ C) :
      ∃ p : E, χ p = c := by
    obtain ⟨hSt, hPr⟩ := (Finset.mem_filter.mp hc).2
    have hbool (i : Fin K) : (c i).1 = false := by
      have hi : i ∉ edgeStoredSet (s := s) c := by rw [hSt]; simp
      cases hb : (c i).1
      · rfl
      · exact (hi (by simp [edgeStoredSet, hb])).elim
    have hright (i : Fin K) : ∃ p : primeBand x (a i), (c i).2 = Sum.inr p := by
      cases heq : (c i).2 with
      | inl k =>
          have hi : i ∉ edgePromotedSet (s := s) c := by rw [hPr]; simp
          exact (hi (by simp [edgePromotedSet, heq])).elim
      | inr p => exact ⟨p, rfl⟩
    refine ⟨fun i => (hright i).choose, ?_⟩
    funext i
    apply Prod.ext
    · exact (hbool i).symm
    · exact (hright i).choose_spec.symm
  have hsum : (∑ p : E, Φ (χ p)) = ∑ c ∈ C, Φ c := by
    apply Finset.sum_bij (fun p hp => χ p)
    · intro p hp
      exact hpattern p
    · intro p hp q hq heq
      exact hinj heq
    · intro c hc
      obtain ⟨p, hp⟩ := hsurj c hc
      exact ⟨p, Finset.mem_univ _, hp⟩
    · intro p hp
      rfl
  calc
    _ = ∑ c ∈ C, Φ c := by simp only [C, Finset.sum_filter]
    _ = ∑ p : E, Φ (χ p) := hsum.symm
    _ = _ := rfl

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
