import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawGrouped

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Fresh labels only in the groups not prescribed for promotion. -/
abbrev RawFreshLabels {K : ℕ} (x : ℝ) (a : Fin K → ℝ) (I : Finset (Fin K)) :=
  (i : (Iᶜ : Finset (Fin K))) → primeBand x (a i.1)

/-- The normalized fresh function used by the second goodness test. -/
def rawFreshFunction {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (I : Finset (Fin K)) (fresh : RawFreshLabels x a I) : Fin K → ℕ :=
  fun i => if hi : i ∈ I then 1 else (fresh ⟨i, Finset.mem_compl.mpr hi⟩).1

/-- Construct a fixed store/promotion pattern with one distinguished indexed promotion. -/
def rawPatternChoice {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (m : Fin K → List Particle) (St I : Finset (Fin K)) (iStar : Fin K)
    (kStar : Fin (m iStar).length) (κ : RawPromotionIndices I iStar m)
    (fresh : RawFreshLabels x a I) : (i : Fin K) → EdgeChoice x a (m i) i :=
  fun i => (decide (i ∈ St), by
    by_cases hi : i ∈ I
    · apply Sum.inl
      by_cases heq : i = iStar
      · subst i
        exact kStar
      · exact κ ⟨i, Finset.mem_erase.mpr ⟨heq, hi⟩⟩
    · exact Sum.inr (fresh ⟨i, Finset.mem_compl.mpr hi⟩))

/-- The fixed-pattern choice sum is exactly a fresh / distinguished / other-index sum.
Store bits are fixed, and empty eligible index types give empty sums on both sides. -/
theorem raw_choice_sum_reindex {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (s : MemPoint x K) (St I : Finset (Fin K))
    (iStar : Fin K) (hstar : iStar ∈ I)
    (Φ : ((i : Fin K) → EdgeChoice x a (s.2.2 i) i) → ℝ) :
    (∑ c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i,
      if edgeStoredSet (s := s) c = St ∧ edgePromotedSet (s := s) c = I then Φ c else 0) =
    ∑ fresh : RawFreshLabels x a I,
      ∑ kStar : Fin (s.2.2 iStar).length,
        ∑ κ : RawPromotionIndices I iStar s.2.2,
          Φ (rawPatternChoice x a s.2.2 St I iStar kStar κ fresh) := by
  let E := RawFreshLabels x a I ×
    (Fin (s.2.2 iStar).length × RawPromotionIndices I iStar s.2.2)
  let C : Finset ((i : Fin K) → EdgeChoice x a (s.2.2 i) i) :=
    Finset.univ.filter (fun c =>
      edgeStoredSet (s := s) c = St ∧ edgePromotedSet (s := s) c = I)
  let f (u : E) := rawPatternChoice x a s.2.2 St I iStar u.2.1 u.2.2 u.1
  have hpattern (u : E) :
      edgeStoredSet (s := s) (f u) = St ∧ edgePromotedSet (s := s) (f u) = I := by
    constructor
    · ext i
      simp [edgeStoredSet, f, rawPatternChoice]
    · ext i
      by_cases hi : i ∈ I
      · by_cases heq : i = iStar
        · subst i
          simp [edgePromotedSet, f, rawPatternChoice, hstar]
        · simp [edgePromotedSet, f, rawPatternChoice, hi, heq]
      · simp [edgePromotedSet, f, rawPatternChoice, hi]
  have hinj : Function.Injective f := by
    intro u v heq
    apply Prod.ext
    · funext i
      have hi : i.1 ∉ I := Finset.mem_compl.mp i.2
      have hc := congrArg (fun c => (c i.1).2) heq
      simpa [f, rawPatternChoice, hi] using hc
    · apply Prod.ext
      · have hc := congrArg (fun c => (c iStar).2) heq
        simpa [f, rawPatternChoice, hstar] using hc
      · funext i
        obtain ⟨hne, hi⟩ := Finset.mem_erase.mp i.2
        have hc := congrArg (fun c => (c i.1).2) heq
        simpa [f, rawPatternChoice, hi, hne] using hc
  have hsurj (c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i) (hc : c ∈ C) :
      ∃ u : E, f u = c := by
    obtain ⟨hSt, hI⟩ := (Finset.mem_filter.mp hc).2
    have hstored (i : Fin K) : (c i).1 = true ↔ i ∈ St := by
      rw [← hSt]
      simp [edgeStoredSet]
    have htag (i : Fin K) : (c i).2.isLeft = true ↔ i ∈ I := by
      rw [← hI]
      simp [edgePromotedSet]
    have hbool (i : Fin K) : (c i).1 = decide (i ∈ St) := by
      by_cases hi : i ∈ St
      · simpa [hi] using (hstored i).mpr hi
      · have hfalse : (c i).1 = false := by
          cases hb : (c i).1
          · rfl
          · exact (hi ((hstored i).mp hb)).elim
        simpa [hi] using hfalse
    have hleft (i : Fin K) (hi : i ∈ I) :
        ∃ k : Fin (s.2.2 i).length, (c i).2 = Sum.inl k := by
      cases heq : (c i).2 with
      | inl k => exact ⟨k, rfl⟩
      | inr p =>
        have h := (htag i).mpr hi
        simp [heq] at h
    have hright (i : Fin K) (hi : i ∉ I) :
        ∃ p : primeBand x (a i), (c i).2 = Sum.inr p := by
      cases heq : (c i).2 with
      | inl k =>
        have h := (htag i).mp (by simp [heq])
        exact (hi h).elim
      | inr p => exact ⟨p, rfl⟩
    let fresh : RawFreshLabels x a I :=
      fun i => (hright i.1 (Finset.mem_compl.mp i.2)).choose
    let kStar : Fin (s.2.2 iStar).length := (hleft iStar hstar).choose
    let κ : RawPromotionIndices I iStar s.2.2 :=
      fun i => (hleft i.1 (Finset.mem_erase.mp i.2).2).choose
    refine ⟨(fresh, kStar, κ), ?_⟩
    change rawPatternChoice x a s.2.2 St I iStar kStar κ fresh = c
    funext i
    apply Prod.ext
    · exact (hbool i).symm
    · by_cases hi : i ∈ I
      · by_cases heq : i = iStar
        · subst i
          have h := (hleft iStar hstar).choose_spec
          simpa [rawPatternChoice, hstar, kStar] using h.symm
        · have h := (hleft i hi).choose_spec
          simpa [rawPatternChoice, hi, heq, κ] using h.symm
      · have h := (hright i hi).choose_spec
        simpa [rawPatternChoice, hi, fresh] using h.symm
  have hsum : (∑ u : E, Φ (f u)) = ∑ c ∈ C, Φ c := by
    apply Finset.sum_bij (fun u hu => f u)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpattern u⟩
    · intro u hu v hv heq
      exact hinj heq
    · intro c hc
      obtain ⟨u, hu⟩ := hsurj c hc
      exact ⟨u, Finset.mem_univ _, hu⟩
    · intro u hu
      rfl
  calc
    _ = ∑ c ∈ C, Φ c := by simp only [C, Finset.sum_filter]
    _ = ∑ u : E, Φ (f u) := hsum.symm
    _ = _ := by simp only [E, f, Fintype.sum_prod_type]

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
