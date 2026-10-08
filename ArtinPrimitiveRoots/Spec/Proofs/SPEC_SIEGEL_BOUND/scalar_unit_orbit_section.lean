import ArtinPrimitiveRoots.Spec.Proofs.SPEC_SIEGEL_BOUND.Defs

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

private lemma scalar_embedding_norm_prod_sq (a : F) :
    (∏ w : InfinitePlace F, ‖w.embedding a‖) ^ 2 = absFieldNorm F a := by
  unfold absFieldNorm
  rw [← Finset.prod_pow]

private lemma scalar_unit_associated_trans (a b c : F)
    (hab : scalarUnitAssociated a b) (hbc : scalarUnitAssociated b c) :
    scalarUnitAssociated a c := by
  rcases hab with ⟨ε, hε⟩
  rcases hbc with ⟨δ, hδ⟩
  refine ⟨ε * δ, ?_⟩
  calc
    a = algebraMap (𝓞 F) F (ε : 𝓞 F) * b := hε
    _ = algebraMap (𝓞 F) F (ε : 𝓞 F) *
        (algebraMap (𝓞 F) F (δ : 𝓞 F) * c) := by rw [hδ]
    _ = algebraMap (𝓞 F) F ((ε * δ : (𝓞 F)ˣ) : 𝓞 F) * c := by
      simp [map_mul, mul_assoc]

private lemma scalar_denominator_bound_unit (D : ℕ) {a : F}
    (ha : HasDenominatorBound F D a) (ε : (𝓞 F)ˣ) :
    HasDenominatorBound F D (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) := by
  rcases ha with ⟨b, hb⟩
  refine ⟨(ε : 𝓞 F) * b, ?_⟩
  change (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
    algebraMap (𝓞 F) F ((ε : 𝓞 F) * b)
  calc
    (D : F) * (algebraMap (𝓞 F) F (ε : 𝓞 F) * a) =
        algebraMap (𝓞 F) F (ε : 𝓞 F) * ((D : F) * a) := by ring
    _ = algebraMap (𝓞 F) F (ε : 𝓞 F) * algebraMap (𝓞 F) F b := by rw [hb]
    _ = algebraMap (𝓞 F) F ((ε : 𝓞 F) * b) := by rw [map_mul]

/-- Choose one balanced nonzero scalar per unit orbit in the denominator lattice.
The covering witness rescales by a unit; its torsion ambiguity is harmless.
Guide: `sol-thin-spec/PROOFS.md:352`. Uses `R4_unit_balance`; feeds
`balanced_denominator_rows_bound`. -/
theorem scalar_unit_orbit_section (D : ℕ) (hD : 0 < D) :
    ∃ (B : ℝ) (S : Set F), 0 ≤ B ∧
      (∀ c ∈ S, c ≠ 0 ∧ HasDenominatorBound F D c ∧
        IsBalancedHeights F B (fun w => ‖w.embedding c‖)) ∧
      (∀ c c', c ∈ S → c' ∈ S → scalarUnitAssociated c c' → c = c') ∧
      (∀ c : F, c ≠ 0 → HasDenominatorBound F D c →
        ∃ ε : (𝓞 F)ˣ, algebraMap (𝓞 F) F (ε : 𝓞 F) * c ∈ S) := by
  classical
  let T := {c : F // c ≠ 0 ∧ HasDenominatorBound F D c}
  have hOneDen : HasDenominatorBound F D (1 : F) := by
    refine ⟨D, ?_⟩
    simp [HasDenominatorBound]
  let tOne : T := ⟨1, one_ne_zero, hOneDen⟩
  letI : Nonempty T := ⟨tOne⟩
  let rel : Setoid T := {
    r := fun a b => scalarUnitAssociated a.1 b.1
    iseqv := ⟨fun {a} => ⟨1, by simp [scalarUnitAssociated]⟩,
      fun {a b} h => by
        rcases h with ⟨ε, hε⟩
        refine ⟨ε⁻¹, ?_⟩
        rw [hε]
        simp [scalarUnitAssociated, map_mul, mul_assoc],
      fun {a b c} h₁ h₂ => by
        rcases h₁ with ⟨ε, hε⟩
        rcases h₂ with ⟨δ, hδ⟩
        refine ⟨ε * δ, ?_⟩
        rw [hε, hδ]
        simp [scalarUnitAssociated, map_mul, mul_assoc]⟩
  }
  let Q := Quotient rel
  let Etop : Subgroup ((𝓞 F)ˣ) := ⊤
  letI : Etop.FiniteIndex := ⟨by dsimp [Etop]; simp⟩
  obtain ⟨B, hB, hbal⟩ := R4_unit_balance (F := F) Etop
  let raw : Q → T := Quotient.out
  let t : Q → InfinitePlace F → ℝ := fun q w => ‖w.embedding (raw q).1‖
  have ht (q : Q) (w : InfinitePlace F) : 0 < t q w := by
    dsimp [t]
    apply norm_pos_iff.mpr
    exact (map_ne_zero_iff _ w.embedding.injective).mpr (raw q).2.1
  let balUnit : Q → (𝓞 F)ˣ := fun q =>
    Classical.choose (hbal (t q) (fun w => ht q w))
  have hbalUnit (q : Q) (w : InfinitePlace F) :
      |Real.log (‖w.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F))‖ * t q w) -
        (placeCount F)⁻¹ * ∑ w' : InfinitePlace F, Real.log (t q w')| ≤ B :=
    (Classical.choose_spec (hbal (t q) (fun w => ht q w))).2 w
  let balanced : Q → F := fun q =>
    algebraMap (𝓞 F) F (balUnit q : 𝓞 F) * (raw q).1
  have hnorm (q : Q) (w : InfinitePlace F) :
      ‖w.embedding (balanced q)‖ =
        ‖w.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F))‖ * t q w := by
    simp [balanced, t, map_mul, norm_mul]
  let S : Set F := Set.range balanced
  refine ⟨B, S, hB, ?_, ?_, ?_⟩
  · intro c hc
    rcases hc with ⟨q, rfl⟩
    have he : algebraMap (𝓞 F) F (balUnit q : 𝓞 F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (𝓞 F) F)
        (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (Units.ne_zero (balUnit q))
    refine ⟨mul_ne_zero he (raw q).2.1,
      scalar_denominator_bound_unit D (raw q).2.2 (balUnit q), ?_⟩
    constructor
    · intro w
      change 0 < ‖w.embedding (balanced q)‖
      rw [hnorm q w]
      have hew : w.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F)) ≠ 0 :=
        (map_ne_zero_iff w.embedding w.embedding.injective).mpr he
      exact mul_pos (norm_pos_iff.mpr hew) (ht q w)
    · intro w
      have hunitPos (w' : InfinitePlace F) :
          0 < ‖w'.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F))‖ := by
        apply norm_pos_iff.mpr
        exact (map_ne_zero_iff w'.embedding w'.embedding.injective).mpr he
      have hunitNorm : absFieldNorm F
          (algebraMap (𝓞 F) F (balUnit q : 𝓞 F)) = 1 := by
        simpa [absFieldNorm_eq_abs_norm] using (NumberField.Units.norm F (balUnit q))
      let U : ℝ := ∏ w' : InfinitePlace F,
        ‖w'.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F))‖
      have hUpos : 0 < U := by
        dsimp [U]
        exact Finset.prod_pos fun w' hw' => hunitPos w'
      have hUsq : U ^ 2 = 1 := by
        dsimp [U]
        rw [scalar_embedding_norm_prod_sq, hunitNorm]
      have hU : U = 1 := by nlinarith [sq_nonneg (U + 1)]
      have hprod (w' : InfinitePlace F) :
          ‖w'.embedding (balanced q)‖ =
            ‖w'.embedding (algebraMap (𝓞 F) F (balUnit q : 𝓞 F))‖ * t q w' :=
        hnorm q w'
      have hprodscaled :
          ∏ w' : InfinitePlace F, ‖w'.embedding (balanced q)‖ =
            ∏ w' : InfinitePlace F, t q w' := by
        calc
          ∏ w' : InfinitePlace F, ‖w'.embedding (balanced q)‖ =
              U * ∏ w' : InfinitePlace F, t q w' := by
            rw [show (fun w' : InfinitePlace F => ‖w'.embedding (balanced q)‖) =
                (fun w' => ‖w'.embedding (algebraMap (𝓞 F) F
                  (balUnit q : 𝓞 F))‖ * t q w') from funext hprod]
            rw [Finset.prod_mul_distrib]
          _ = ∏ w' : InfinitePlace F, t q w' := by rw [hU]; simp
      have hsumlogs :
          (∑ w' : InfinitePlace F, Real.log ‖w'.embedding (balanced q)‖) =
            ∑ w' : InfinitePlace F, Real.log (t q w') := by
        have hlogScaled := Real.log_prod (s := Finset.univ)
          (f := fun w' : InfinitePlace F => ‖w'.embedding (balanced q)‖)
          (fun w' hw' => (norm_pos_iff.mpr
            ((map_ne_zero_iff w'.embedding w'.embedding.injective).mpr
              (mul_ne_zero he (raw q).2.1))).ne')
        have hlogT := Real.log_prod (s := Finset.univ)
          (f := fun w' : InfinitePlace F => t q w')
          (fun w' hw' => (ht q w').ne')
        rw [hprodscaled] at hlogScaled
        exact hlogScaled.symm.trans hlogT
      have hlogfirst : Real.log ‖w.embedding (balanced q)‖ =
          Real.log (‖w.embedding (algebraMap (𝓞 F) F
            (balUnit q : 𝓞 F))‖ * t q w) := by
        rw [hnorm q w, Real.log_mul (hunitPos w).ne' (ht q w).ne']
      change |Real.log ‖w.embedding (balanced q)‖ -
        (Fintype.card (InfinitePlace F) : ℝ)⁻¹ *
          ∑ w' : InfinitePlace F, Real.log ‖w'.embedding (balanced q)‖| ≤ B
      rw [hlogfirst, hsumlogs]
      simpa [placeCount] using hbalUnit q w
  · intro c c' hc hc' hcc
    rcases hc with ⟨q, rfl⟩
    rcases hc' with ⟨q', rfl⟩
    have hraw : scalarUnitAssociated (raw q).1 (raw q').1 := by
      have h₁ : scalarUnitAssociated (raw q).1 (balanced q) := by
        refine ⟨(balUnit q)⁻¹, ?_⟩
        dsimp [balanced]
        simp [map_mul, mul_assoc]
      have h₂ : scalarUnitAssociated (balanced q) (balanced q') := hcc
      have h₃ : scalarUnitAssociated (balanced q') (raw q').1 := by
        refine ⟨balUnit q', ?_⟩
        rfl
      have h12 := scalar_unit_associated_trans (raw q).1 (balanced q) (balanced q') h₁ h₂
      exact scalar_unit_associated_trans (raw q).1 (balanced q') (raw q').1 h12 h₃
    have hq : q = q' := by
      calc
        q = Quotient.mk rel (raw q) := (Quotient.out_eq q).symm
        _ = Quotient.mk rel (raw q') := Quotient.sound hraw
        _ = q' := Quotient.out_eq q'
    simpa [hq]
  · intro c hc0 hcD
    let tc : T := ⟨c, hc0, hcD⟩
    let q : Q := Quotient.mk rel tc
    have hrel : scalarUnitAssociated (raw q).1 c := by
      have hout := Quotient.out_eq q
      change Quotient.mk rel (raw q) = Quotient.mk rel tc at hout
      have h := Quotient.exact hout
      change scalarUnitAssociated (raw q).1 c at h
      exact h
    rcases hrel with ⟨η, hη⟩
    refine ⟨balUnit q * η, ?_⟩
    apply Set.mem_range.mpr
    refine ⟨q, ?_⟩
    simp only [balanced, map_mul]
    rw [hη]
    change algebraMap (𝓞 F) F (balUnit q : 𝓞 F) *
        (algebraMap (𝓞 F) F (η : 𝓞 F) * c) =
      algebraMap (𝓞 F) F ((balUnit q * η : (𝓞 F)ˣ) : 𝓞 F) * c
    have hmap : algebraMap (𝓞 F) F ((balUnit q * η : (𝓞 F)ˣ) : 𝓞 F) =
        algebraMap (𝓞 F) F (balUnit q : 𝓞 F) * algebraMap (𝓞 F) F (η : 𝓞 F) := by
      simp [Units.val_mul, map_mul]
    calc
      _ = (algebraMap (𝓞 F) F (balUnit q : 𝓞 F) *
          algebraMap (𝓞 F) F (η : 𝓞 F)) * c := by ring
      _ = algebraMap (𝓞 F) F ((balUnit q * η : (𝓞 F)ˣ) : 𝓞 F) * c := by rw [hmap]

end ArtinPrimitiveRoots.A1.Spec
