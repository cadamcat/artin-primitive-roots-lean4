import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.primitive_conductor_residue_determines
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_gauss_orthogonality
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_additive_sieve_apply

set_option autoImplicit false
set_option maxHeartbeats 600000
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem conductorExteriorCutoff_mem_of_norm
    (S : A1.SData F CE condη) (N : ℝ) (hN : 0 ≤ N)
    (q : S.ExtIdeal) (hq : idealNorm q.1 ≤ N) :
    q ∈ conductorExteriorCutoff S N := by
  classical
  have hcut : q.1 ∈ conductorIdealCutoff F N := by
    change q.1 ∈ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).toFinset
    apply (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊N⌋₊).mem_toFinset.mpr
    change Ideal.absNorm q.1 ≤ ⌊N⌋₊
    exact (Nat.le_floor_iff hN).2 (by simpa [idealNorm] using hq)
  have hB : q.1 ∈ (conductorIdealCutoff F N).filter S.IsExterior :=
    Finset.mem_filter.mpr ⟨hcut, q.2⟩
  unfold conductorExteriorCutoff
  apply Finset.mem_map.mpr
  refine ⟨⟨q.1, hB⟩, Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  rfl

private theorem conductorCastChar_eq_iff
    (S : A1.SData F CE condη) {q₁ q₂ q : S.ExtIdeal}
    (h₁ : q₁ = q) (h₂ : q₂ = q)
    (χ₁ : MulChar (ConductorResidueRing q₁) ℂ)
    (χ₂ : MulChar (ConductorResidueRing q₂) ℂ) :
    (h₁ ▸ χ₁ = h₂ ▸ χ₂) ↔ χ₁ = h₂.trans h₁.symm ▸ χ₂ := by
  cases h₁
  cases h₂
  rfl

private theorem conductorCastChar_primitive
    (S : A1.SData F CE condη) {q₁ q₂ : S.ExtIdeal} (h : q₁ = q₂)
    (χ : MulChar (ConductorResidueRing q₁) ℂ)
    (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) :
    OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals (h ▸ χ) := by
  cases h
  exact hχ

private theorem conductorCastRealization
    (S : A1.SData F CE condη) (G : ConductorGenerators S)
    (ρ : ConductorResidues S) (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
    {q₁ q₂ : S.ExtIdeal} (h : q₁ = q₂)
    (χ : MulChar (ConductorResidueRing q₁) ℂ) (ω : A1.HeckeChar F)
    (hχ : ConductorResidueRealizes S G ρ ℓ τ q₁ χ ω) :
    ConductorResidueRealizes S G ρ ℓ τ q₂ (h ▸ χ) ω := by
  cases h
  exact hχ

/-- Transport each fixed local group injectively to its conductor/residue pair,
apply the Gauss bound and the dual additive estimate. Constants precede both lengths
and the local components.
Uses primitive_conductor_residue_bridge/determines, conductor_gauss_orthogonality,
and conductor_additive_sieve_apply; feeds the dyadic Cauchy–Schwarz step. -/
theorem conductor_exterior_dyad_bound (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ T U : ℝ, 1 ≤ T → 2 ≤ U →
      ∀ (ℓ : SLocalCharacter S) (τ : ConductorInfiniteLocal F)
        (𝓧 : Finset (A1.HeckeChar F)), ConductorGroup S C₀ U ℓ τ 𝓧 →
        ∀ b : S.ExtIdeal → ℂ,
        (∑ ω ∈ 𝓧, ‖∑ I ∈ conductorExteriorDyad S T, b I * ω.idealValue I.1‖ ^ 2) ≤
            C * (T + U ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨G⟩ := conductor_generators_exists S
  obtain ⟨ρ⟩ := conductor_residues_exists S
  obtain ⟨Ψ⟩ := conductor_additive_characters_exists S
  obtain ⟨Cadd, hCadd, hAdd⟩ := conductor_additive_sieve_apply S G ρ Ψ
  let D : ℝ := max 1 C₀
  let E : ℝ := max 1 (D ^ 2)
  refine ⟨Cadd * E, mul_pos hCadd (by dsimp [E]; positivity), ?_⟩
  intro T U hT hU ℓ τ 𝓧 h𝓧 b
  by_cases h𝓧empty : 𝓧 = ∅
  · subst 𝓧
    simp
    positivity
  · have h𝓧ne : 𝓧.Nonempty := Finset.nonempty_iff_ne_empty.mpr h𝓧empty
    obtain ⟨ω₀, hω₀⟩ := h𝓧ne
    have hgroup₀ := h𝓧 ω₀ hω₀
    change IsOfFinOrder ω₀ ∧ SComponent S ω₀ = ℓ ∧
      conductorInfiniteComponent ω₀ = τ ∧
      ∃ f, IsPrimitiveConductor ω₀ f ∧ idealNorm f ≤ C₀ * U at hgroup₀
    rcases hgroup₀ with ⟨hfin₀, hℓ₀, hτ₀, f₀, hf₀, hfb₀⟩
    have hunit : ∀ a : Fˣ, ‖conductorLambdaS S ℓ τ a‖ = 1 := by
      exact (primitive_conductor_residue_bridge S G ρ ℓ τ ω₀ hfin₀ f₀ hf₀ hℓ₀ hτ₀).1
    have hdata : ∀ w : {ω : A1.HeckeChar F // ω ∈ 𝓧},
        ∃ f, IsPrimitiveConductor w.1 f ∧ idealNorm f ≤ C₀ * U ∧
          (∀ a : Fˣ, ‖conductorLambdaS S ℓ τ a‖ = 1) ∧
          ∃ q, q.1 = conductorExteriorPart S f ∧
            Ideal.absNorm q.1 ≤ Ideal.absNorm f ∧
            ∃ χ : MulChar (ConductorResidueRing q) ℂ,
              OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ ∧
              ConductorResidueRealizes S G ρ ℓ τ q χ w.1 := by
      intro w
      have hg := h𝓧 w.1 w.2
      change IsOfFinOrder w.1 ∧ SComponent S w.1 = ℓ ∧
        conductorInfiniteComponent w.1 = τ ∧
        ∃ f, IsPrimitiveConductor w.1 f ∧ idealNorm f ≤ C₀ * U at hg
      rcases hg with ⟨hfin, hℓ, hτ, f, hf, hfb⟩
      obtain ⟨hu, q, hqpart, hqnorm, χ, hχ, hreal⟩ :=
        primitive_conductor_residue_bridge S G ρ ℓ τ w.1 hfin f hf hℓ hτ
      exact ⟨f, hf, hfb, hu, q, hqpart, hqnorm, χ, hχ, hreal⟩
    choose fω hfω hfb hunitω qω hqpart hqnorm χω hχω hreal using hdata
    let V : ℝ := max 2 (C₀ * U)
    have hV2 : 2 ≤ V := by dsimp [V]; exact le_max_left _ _
    have hVnorm : C₀ * U ≤ V := by dsimp [V]; exact le_max_right _ _
    have hD1 : 1 ≤ D := by dsimp [D]; exact le_max_left _ _
    have hDC₀ : C₀ ≤ D := by dsimp [D]; exact le_max_right _ _
    have hUpos : 0 < U := by linarith
    have hVle : V ≤ D * U := by
      dsimp [V]
      apply max_le
      · calc
          (2 : ℝ) ≤ U := hU
          _ = 1 * U := by ring
          _ ≤ D * U := mul_le_mul_of_nonneg_right hD1 hUpos.le
      · exact mul_le_mul_of_nonneg_right hDC₀ hUpos.le
    have hE1 : 1 ≤ E := by dsimp [E]; exact le_max_left _ _
    have hED : D ^ 2 ≤ E := by dsimp [E]; exact le_max_right _ _
    have hTnonneg : 0 ≤ T := by linarith
    have hVnonneg : 0 ≤ V := le_trans (by norm_num) hV2
    have hDU : 0 ≤ D * U := mul_nonneg (le_trans (by norm_num) hD1) hUpos.le
    have hVpow : V ^ 2 ≤ E * U ^ 2 := by
      have hsq : V ^ 2 ≤ (D * U) ^ 2 := by nlinarith
      calc
        V ^ 2 ≤ (D * U) ^ 2 := hsq
        _ = D ^ 2 * U ^ 2 := by ring
        _ ≤ E * U ^ 2 := mul_le_mul_of_nonneg_right hED (sq_nonneg U)
    have hTpow : T ≤ E * T := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hE1) hTnonneg]
    have hTV : T + V ^ 2 ≤ E * (T + U ^ 2) := by nlinarith
    let c : S.ExtIdeal → ℂ := fun I => b I * conductorLambdaS S ℓ τ (G.unit I)
    have hcNorm (I : S.ExtIdeal) : ‖c I‖ = ‖b I‖ := by
      simp [c, hunit (G.unit I)]
    have hmass :
        (∑ I ∈ conductorExteriorDyad S T, ‖c I‖ ^ 2) =
          ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hcNorm]
    let Q : Finset S.ExtIdeal := 𝓧.attach.image qω
    let Xq (q : S.ExtIdeal) := 𝓧.attach.filter (fun w => qω w = q)
    let χat (q : S.ExtIdeal) (w : {ω : A1.HeckeChar F // ω ∈ 𝓧}) :
        MulChar (ConductorResidueRing q) ℂ :=
      if h : qω w = q then h ▸ χω w else 1
    let Λ (q : S.ExtIdeal) := (Xq q).image (χat q)
    have hQsubset : Q ⊆ conductorExteriorCutoff S V := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨w, hw, rfl⟩
      apply conductorExteriorCutoff_mem_of_norm S V (by positivity) (qω w)
      calc
        idealNorm (qω w).1 ≤ idealNorm (fω w) := by
          change (Ideal.absNorm (qω w).1 : ℝ) ≤ (Ideal.absNorm (fω w) : ℝ)
          exact_mod_cast hqnorm w
        _ ≤ C₀ * U := hfb w
        _ ≤ V := hVnorm
    have hΛprimitive (q : S.ExtIdeal) :
        ∀ χ, χ ∈ Λ q → OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ := by
      intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨w, hw, rfl⟩
      have hq : qω w = q := (Finset.mem_filter.mp hw).2
      simpa [χat, hq] using conductorCastChar_primitive S hq (χω w) (hχω w)
    have hΛinj (q : S.ExtIdeal) :
        Set.InjOn (χat q) (Xq q : Set {ω : A1.HeckeChar F // ω ∈ 𝓧}) := by
      intro w hw w' hw' hχ
      have hq : qω w = q := (Finset.mem_filter.mp hw).2
      have hq' : qω w' = q := (Finset.mem_filter.mp hw').2
      have hcastEq : hq ▸ χω w = hq' ▸ χω w' := by
        simpa [χat, hq, hq'] using hχ
      have hrel : qω w' = qω w := hq'.trans hq.symm
      have hχωeq : χω w = hrel ▸ χω w' :=
        (conductorCastChar_eq_iff S hq hq' (χω w) (χω w')).mp hcastEq
      have hg := h𝓧 w.1 w.2
      have hg' := h𝓧 w'.1 w'.2
      change IsOfFinOrder w.1 ∧ SComponent S w.1 = ℓ ∧
        conductorInfiniteComponent w.1 = τ ∧
        ∃ f, IsPrimitiveConductor w.1 f ∧ idealNorm f ≤ C₀ * U at hg
      change IsOfFinOrder w'.1 ∧ SComponent S w'.1 = ℓ ∧
        conductorInfiniteComponent w'.1 = τ ∧
        ∃ f, IsPrimitiveConductor w'.1 f ∧ idealNorm f ≤ C₀ * U at hg'
      rcases hg with ⟨hfin, hℓ, hτ, f, hf, hfb'⟩
      rcases hg' with ⟨hfin', hℓ', hτ', f', hf', hfb''⟩
      have hreal' :
          ConductorResidueRealizes S G ρ ℓ τ (qω w) (χω w) w'.1 := by
        rw [hχωeq]
        exact conductorCastRealization S G ρ ℓ τ hrel (χω w') w'.1 (hreal w')
      have heq := primitive_conductor_residue_determines S G ρ ℓ τ (qω w)
        (χω w) w.1 w'.1 hfin hfin' f f' hf hf' hℓ hℓ' hτ hτ'
        (hreal w) hreal'
      exact Subtype.ext heq
    have hsumEq (q : S.ExtIdeal) (w : {ω : A1.HeckeChar F // ω ∈ 𝓧})
        (hw : w ∈ Xq q) :
        (∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1) =
          ∑ I ∈ conductorExteriorDyad S T,
            c I * χat q w (ρ.red q (G.gen I)) := by
      have hqw : qω w = q := (Finset.mem_filter.mp hw).2
      cases hqw
      apply Finset.sum_congr rfl
      intro I hI
      rw [hreal w I]
      simp [c, χat]
      ring
    have hsumFiber (q : S.ExtIdeal) :
        (∑ w ∈ Xq q,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2) ≤
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := by
      have hgauss := conductor_gauss_orthogonality (ψ := Ψ.ψ q) (Ψ.primitive q)
        (𝓧 := Λ q) (hΛprimitive q) (B := conductorExteriorDyad S T)
        (r := fun I => ρ.red q (G.gen I)) (b := c)
      have hcard : Fintype.card (ConductorResidueRing q)ˣ ≤
          Fintype.card (ConductorResidueRing q) := by
        exact Fintype.card_le_of_injective (fun u : (ConductorResidueRing q)ˣ => (u : ConductorResidueRing q))
          Units.val_injective
      have hden : 0 < (Fintype.card (ConductorResidueRing q) : ℝ) := by
        haveI : Nonempty (ConductorResidueRing q) := ⟨0⟩
        positivity
      have hfactor :
          ((Fintype.card (ConductorResidueRing q)ˣ : ℝ) /
            (Fintype.card (ConductorResidueRing q) : ℝ)) ≤ 1 := by
        apply (div_le_one₀ hden).2
        exact_mod_cast hcard
      have hfourier :
          (∑ χ ∈ Λ q,
            ‖∑ I ∈ conductorExteriorDyad S T,
              c I * χ (ρ.red q (G.gen I))‖ ^ 2) ≤
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := by
        calc
          _ ≤ ((Fintype.card (ConductorResidueRing q)ˣ : ℝ) /
                (Fintype.card (ConductorResidueRing q) : ℝ)) *
                ∑ d : (ConductorResidueRing q)ˣ,
                  ‖∑ I ∈ conductorExteriorDyad S T,
                    c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := hgauss
          _ ≤ _ := by
            have haddnonneg : 0 ≤
                ∑ d : (ConductorResidueRing q)ˣ,
                  ‖∑ I ∈ conductorExteriorDyad S T,
                    c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := by
              positivity
            nlinarith [mul_le_mul_of_nonneg_right hfactor haddnonneg]
      calc
        _ = ∑ w ∈ Xq q,
              ‖∑ I ∈ conductorExteriorDyad S T,
                c I * χat q w (ρ.red q (G.gen I))‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro w hw
              exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hsumEq q w hw)
        _ = ∑ χ ∈ Λ q,
              ‖∑ I ∈ conductorExteriorDyad S T,
                c I * χ (ρ.red q (G.gen I))‖ ^ 2 := by
              change (∑ w ∈ Xq q,
                  (fun χ : MulChar (ConductorResidueRing q) ℂ =>
                    ‖∑ I ∈ conductorExteriorDyad S T,
                      c I * χ (ρ.red q (G.gen I))‖ ^ 2) (χat q w)) =
                ∑ χ ∈ (Xq q).image (χat q),
                  ‖∑ I ∈ conductorExteriorDyad S T,
                    c I * χ (ρ.red q (G.gen I))‖ ^ 2
              exact (Finset.sum_image (f := fun χ : MulChar (ConductorResidueRing q) ℂ =>
                ‖∑ I ∈ conductorExteriorDyad S T,
                  c I * χ (ρ.red q (G.gen I))‖ ^ 2)
                (g := χat q) (hΛinj q)).symm
        _ ≤ _ := hfourier
    have hpartition :
        (∑ w ∈ 𝓧.attach,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2) =
        ∑ q ∈ Q,
          ∑ w ∈ Xq q,
            ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2 := by
      exact (Finset.sum_fiberwise_of_maps_to
        (fun w hw => Finset.mem_image_of_mem qω hw)
        (fun w => ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2)).symm
    have hsumQ :
        (∑ q ∈ Q,
          ∑ w ∈ Xq q,
            ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2) ≤
        ∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := by
      calc
        _ ≤ ∑ q ∈ Q,
              ∑ d : (ConductorResidueRing q)ˣ,
                ‖∑ I ∈ conductorExteriorDyad S T,
                  c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 :=
            Finset.sum_le_sum (fun q hq => hsumFiber q)
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hQsubset (by
          intro q hq hqnot
          positivity)
    have hAdd' := hAdd T V hT hV2 c
    have hAdd'' :
        (∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) ≤
          Cadd * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖c I‖ ^ 2 := hAdd'
    have hpartition' :
        (∑ ω ∈ 𝓧,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * ω.idealValue I.1‖ ^ 2) =
        ∑ w ∈ 𝓧.attach,
          ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2 := by
      exact (Finset.sum_attach 𝓧 _).symm
    calc
      (∑ ω ∈ 𝓧,
        ‖∑ I ∈ conductorExteriorDyad S T, b I * ω.idealValue I.1‖ ^ 2) =
          ∑ q ∈ Q,
            ∑ w ∈ Xq q,
              ‖∑ I ∈ conductorExteriorDyad S T, b I * w.1.idealValue I.1‖ ^ 2 := by
        rw [hpartition', hpartition]
      _ ≤ ∑ q ∈ conductorExteriorCutoff S V,
            ∑ d : (ConductorResidueRing q)ˣ,
              ‖∑ I ∈ conductorExteriorDyad S T,
                c I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2 := hsumQ
      _ ≤ Cadd * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖c I‖ ^ 2 := hAdd''
      _ = Cadd * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by rw [hmass]
      _ ≤ Cadd * E * (T + U ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
        have hmassnonneg : 0 ≤ ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by positivity
        have hscaled := mul_le_mul_of_nonneg_right hTV (mul_nonneg hCadd.le hmassnonneg)
        nlinarith
      _ = (Cadd * E) * (T + U ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by ring

end ArtinPrimitiveRoots.A2
