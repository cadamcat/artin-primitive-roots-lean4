import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_generators_exists
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.primitive_conductor_residue_determines
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.sComponent_sign_partition
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residue_character_count
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT

set_option autoImplicit false
set_option maxHeartbeats 600000
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

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

private theorem conductor_fixed_group_card_bound
    (S : A1.SData F CE condη) (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      ∀ ℓ : SLocalCharacter S, ∀ τ : ConductorInfiniteLocal F,
        ∀ 𝓧 : Finset (A1.HeckeChar F), ConductorGroup S C₀ U ℓ τ 𝓧 →
          (𝓧.card : ℝ) ≤ C * U ^ 2 := by
  classical
  obtain ⟨G⟩ := conductor_generators_exists S
  obtain ⟨ρ⟩ := conductor_residues_exists S
  obtain ⟨Cideal, hCideal, hcount⟩ := a2_bridge_COUNT S
  let D : ℝ := max 1 C₀
  let C : ℝ := C₀ * Cideal * D
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro U hU ℓ τ 𝓧 h𝓧
  have hdata : ∀ w : {ω : A1.HeckeChar F // ω ∈ 𝓧},
      ∃ f, IsPrimitiveConductor w.1 f ∧ idealNorm f ≤ C₀ * U ∧
        ∃ q, Ideal.absNorm q.1 ≤ Ideal.absNorm f ∧
          ∃ χ : MulChar (ConductorResidueRing q) ℂ,
            OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ ∧
            ConductorResidueRealizes S G ρ ℓ τ q χ w.1 := by
    intro w
    have hg := h𝓧 w.1 w.2
    change IsOfFinOrder w.1 ∧ SComponent S w.1 = ℓ ∧
      conductorInfiniteComponent w.1 = τ ∧
      ∃ f, IsPrimitiveConductor w.1 f ∧ idealNorm f ≤ C₀ * U at hg
    rcases hg with ⟨hfin, hℓ, hτ, f, hf, hfb⟩
    obtain ⟨_, q, _, hqnorm, χ, hχ, hreal⟩ :=
      primitive_conductor_residue_bridge S G ρ ℓ τ w.1 hfin f hf hℓ hτ
    exact ⟨f, hf, hfb, q, hqnorm, χ, hχ, hreal⟩
  choose fω hfω hfb qω hqnorm χω hχω hreal using hdata
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
  let Q : Finset S.ExtIdeal := 𝓧.attach.image qω
  let Xq (q : S.ExtIdeal) := 𝓧.attach.filter (fun w => qω w = q)
  let χat (q : S.ExtIdeal) (w : {ω : A1.HeckeChar F // ω ∈ 𝓧}) :
      MulChar (ConductorResidueRing q) ℂ :=
    if h : qω w = q then h ▸ χω w else 1
  let Λ (q : S.ExtIdeal) := (Xq q).image (χat q)
  have hQnorm (q : S.ExtIdeal) (hq : q ∈ Q) : idealNorm q.1 ≤ C₀ * U := by
    rcases Finset.mem_image.mp hq with ⟨w, hw, rfl⟩
    calc
      idealNorm (qω w).1 ≤ idealNorm (fω w) := by
        change (Ideal.absNorm (qω w).1 : ℝ) ≤ (Ideal.absNorm (fω w) : ℝ)
        exact_mod_cast hqnorm w
      _ ≤ C₀ * U := hfb w
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
    have hreal' : ConductorResidueRealizes S G ρ ℓ τ (qω w) (χω w) w'.1 := by
      rw [hχωeq]
      exact conductorCastRealization S G ρ ℓ τ hrel (χω w') w'.1 (hreal w')
    have heq := primitive_conductor_residue_determines S G ρ ℓ τ (qω w)
      (χω w) w.1 w'.1 hfin hfin' f f' hf hf' hℓ hℓ' hτ hτ'
      (hreal w) hreal'
    exact Subtype.ext heq
  have hfiberCard (q : S.ExtIdeal) : (Xq q).card ≤ Ideal.absNorm q.1 := by
    have hcharCard := conductor_residue_character_count (Λ q)
    have himageCard : (Xq q).card = (Λ q).card :=
      (Finset.card_image_iff.mpr (hΛinj q)).symm
    have hringCard : Fintype.card (ConductorResidueRing q) = Ideal.absNorm q.1 := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    calc
      (Xq q).card = (Λ q).card := himageCard
      _ ≤ Fintype.card (ConductorResidueRing q) := hcharCard.1.trans hcharCard.2
      _ = Ideal.absNorm q.1 := hringCard
  have hcountPart :
      ((𝓧.card : ℕ) : ℝ) ≤ (C₀ * U) * (Q.card : ℝ) := by
    have hcardPart : 𝓧.card = ∑ q ∈ Q, (Xq q).card := by
      simpa [Q, Xq] using Finset.card_eq_sum_card_image qω 𝓧.attach
    have hfiberReal (q : S.ExtIdeal) (hq : q ∈ Q) :
        ((Xq q).card : ℝ) ≤ C₀ * U := by
      calc
        ((Xq q).card : ℝ) ≤ (Ideal.absNorm q.1 : ℝ) := by exact_mod_cast hfiberCard q
        _ ≤ C₀ * U := hQnorm q hq
    have hcardPartReal :
        (𝓧.card : ℝ) = ∑ q ∈ Q, ((Xq q).card : ℝ) := by
      exact_mod_cast hcardPart
    calc
      (𝓧.card : ℝ) = ∑ q ∈ Q, ((Xq q).card : ℝ) := hcardPartReal
      _ ≤ ∑ q ∈ Q, (C₀ * U) := Finset.sum_le_sum (fun q hq => hfiberReal q hq)
      _ = (C₀ * U) * (Q.card : ℝ) := by simp [mul_comm]
  have hfiniteQ := a2_bridge_COUNT_finite S V (by positivity)
  have hQsubset : Q ⊆ bridgeNormFinset S V := by
    intro q hq
    exact (hfiniteQ.2 q).2 ((hQnorm q hq).trans hVnorm)
  have hQtoFin : hfiniteQ.1.toFinset = bridgeNormFinset S V := by
    ext q
    rw [Set.Finite.mem_toFinset]
    exact (hfiniteQ.2 q).symm
  have hQcardNat : Q.card ≤ (bridgeNormFinset S V).card := Finset.card_le_card hQsubset
  have hQncard :
      ({I : S.ExtIdeal | idealNorm I.1 ≤ V}.ncard) = (bridgeNormFinset S V).card := by
    rw [Set.ncard_eq_toFinset_card _ hfiniteQ.1, hQtoFin]
  have hQcardReal : (Q.card : ℝ) ≤ Cideal * V := by
    have hV1 : 1 ≤ V := le_trans (by norm_num) hV2
    have hC := hcount V hV1
    calc
      (Q.card : ℝ) ≤ (bridgeNormFinset S V).card := by exact_mod_cast hQcardNat
      _ = ({I : S.ExtIdeal | idealNorm I.1 ≤ V}.ncard : ℝ) := by exact_mod_cast hQncard.symm
      _ ≤ Cideal * V := hC
  calc
    (𝓧.card : ℝ) ≤ (C₀ * U) * (Q.card : ℝ) := hcountPart
    _ ≤ (C₀ * U) * (Cideal * V) :=
      mul_le_mul_of_nonneg_left hQcardReal (by positivity)
    _ ≤ (C₀ * U) * (Cideal * (D * U)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hVle hCideal.le) (by positivity)
    _ = C * U ^ 2 := by dsimp [C]; ring

/-- Count conductor/residue pairs, then the finite/infinite local groups.
The resulting quadratic count handles the frozen bottom-ideal coefficient.
Guide: sol-thin-a2zf/PROOFS.md:742–747.
Uses the residue bridge/injectivity, unit duality, and ideal norm counting. -/
theorem conductor_family_card_bound (S : A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀) (𝓛S : Finset (SLocalCharacter S)) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 2 ≤ U →
      ∀ 𝓧 : Finset (A1.HeckeChar F), ConductorFamily S C₀ U 𝓛S 𝓧 →
        (𝓧.card : ℝ) ≤ C * U ^ 2 := by
  classical
  obtain ⟨Cgrp, hCgrp, hfixed⟩ := conductor_fixed_group_card_bound S C₀ hC₀
  let C : ℝ := Cgrp * max 1 (𝓛S.card : ℝ) * (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro U hU 𝓧 h𝓧
  have hfinLocal : ∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S := by
    intro ω hω
    have h := h𝓧 ω hω
    change IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
      ∃ f, IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U at h
    exact ⟨h.1, h.2.1⟩
  have hsign := sComponent_sign_partition S 𝓛S 𝓧 hfinLocal
  rcases hsign with ⟨_, hpairCard, _, _⟩
  let pairOf (ω : A1.HeckeChar F) := (SComponent S ω, conductorInfiniteComponent ω)
  let P : Finset (SLocalCharacter S × ConductorInfiniteLocal F) := 𝓧.image pairOf
  let Xp (p : SLocalCharacter S × ConductorInfiniteLocal F) :=
    𝓧.filter (fun ω => pairOf ω = p)
  have hcardPartition : 𝓧.card = ∑ p ∈ P, (Xp p).card := by
    simpa [P, Xp] using Finset.card_eq_sum_card_image pairOf 𝓧
  have hXpGroup (p : SLocalCharacter S × ConductorInfiniteLocal F) :
      ConductorGroup S C₀ U p.1 p.2 (Xp p) := by
    intro ω hω
    have hω' : ω ∈ 𝓧 := (Finset.mem_filter.mp hω).1
    have hp : pairOf ω = p := (Finset.mem_filter.mp hω).2
    have h : IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
        ∃ f, IsPrimitiveConductor ω f ∧ idealNorm f ≤ C₀ * U := h𝓧 ω hω'
    rcases h with ⟨hfin, hlocal, f, hf, hfb⟩
    have hp₁ : SComponent S ω = p.1 := congrArg Prod.fst hp
    have hp₂ : conductorInfiniteComponent ω = p.2 := congrArg Prod.snd hp
    have hpLocal : p.1 ∈ 𝓛S := by rw [← hp₁]; exact hlocal
    exact ⟨hfin, hp₁, hp₂, f, hf, hfb⟩
  have hPcardR : (P.card : ℝ) ≤ (𝓛S.card : ℝ) * (2 : ℝ) ^
      NumberField.InfinitePlace.nrRealPlaces F := by
    exact_mod_cast hpairCard
  have hcardX : (𝓧.card : ℝ) ≤ (Cgrp * U ^ 2) * (P.card : ℝ) := by
    have hcardPartR : (𝓧.card : ℝ) = ∑ p ∈ P, ((Xp p).card : ℝ) := by
      exact_mod_cast hcardPartition
    calc
      (𝓧.card : ℝ) = ∑ p ∈ P, ((Xp p).card : ℝ) := hcardPartR
      _ ≤ ∑ p ∈ P, Cgrp * U ^ 2 :=
        Finset.sum_le_sum (fun p hp => by
          have h := hfixed U hU p.1 p.2 (Xp p) (hXpGroup p)
          exact_mod_cast h)
      _ = (Cgrp * U ^ 2) * (P.card : ℝ) := by simp [mul_comm]
  have hlocalCoeff : (𝓛S.card : ℝ) ≤ max 1 (𝓛S.card : ℝ) := le_max_right _ _
  have hrealSign : 0 ≤ (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F := by positivity
  have hfactor :
      (𝓛S.card : ℝ) * (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F ≤
        max 1 (𝓛S.card : ℝ) * (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F :=
    mul_le_mul_of_nonneg_right hlocalCoeff hrealSign
  calc
    (𝓧.card : ℝ) ≤ (Cgrp * U ^ 2) * (P.card : ℝ) := hcardX
    _ ≤ (Cgrp * U ^ 2) *
        ((𝓛S.card : ℝ) * (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F) :=
      mul_le_mul_of_nonneg_left hPcardR (by positivity)
    _ ≤ (Cgrp * U ^ 2) *
        (max 1 (𝓛S.card : ℝ) * (2 : ℝ) ^ NumberField.InfinitePlace.nrRealPlaces F) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = C * U ^ 2 := by dsimp [C]; ring

end ArtinPrimitiveRoots.A2
