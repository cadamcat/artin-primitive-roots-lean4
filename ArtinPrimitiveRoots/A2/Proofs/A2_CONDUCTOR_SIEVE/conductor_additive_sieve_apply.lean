import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_generators_exists
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_residues_exists
import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_additive_characters_exists
import ArtinPrimitiveRoots.Proofs.a2_cond_b.AdditivePhase
import ArtinPrimitiveRoots.Proofs.a2_cond_b.FiniteLargeSieve

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private theorem conductorSieveIndex_angle_sep (S : A1.SData F CE condη)
    (ρ : ConductorResidues S) (Ψ : ConductorAdditiveCharacters S)
    {V : ℝ} (hV : 2 ≤ V) (D : ℕ)
    (hD : 4 * (Module.finrank ℚ F : ℝ) *
        (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ)) ≤ D) :
    ∀ i j : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
      i ≠ j → ∃ k : Module.Free.ChooseBasisIndex ℤ (𝓞 F), ∀ m : ℤ,
        1 / (D : ℝ) ≤
          |ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
              S Ψ i.1.1 i.1.2 k -
            ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
              S Ψ j.1.1 j.1.2 k - (m : ℝ)| := by
  intro i j hij
  have hphase :
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase S ρ Ψ V i ≠
        ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase S ρ Ψ V j := by
    intro heq
    exact hij
      (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase_injective
        S ρ Ψ V heq)
  obtain ⟨k, hangle⟩ :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndex_angle_separation
      S ρ Ψ hV i j hphase
  let ψ := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralDifferenceChar
    S Ψ i.1.1 j.1.1 i.1.2 j.1.2
  let α := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacterFrequencyVector ψ k
  have hunit (a : 𝓞 F) : ‖ψ a‖ = 1 :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralDifferenceChar_norm
      S Ψ i.1.1 j.1.1 i.1.2 j.1.2 a
  have hα : |α| ≤ 1 / 2 := by
    dsimp [α, ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveCharacterFrequencyVector,
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorUnitAngle]
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 * Real.pi : ℝ))]
    have harg := Complex.abs_arg_le_pi (ψ (RingOfIntegers.basis F k))
    calc
      |(ψ (RingOfIntegers.basis F k)).arg| / (2 * Real.pi) ≤
          Real.pi / (2 * Real.pi) :=
        div_le_div_of_nonneg_right harg (by positivity)
      _ = 1 / 2 := by field_simp
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
            S Ψ i.1.1 i.1.2 k -
            ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
              S Ψ j.1.1 j.1.2 k : ℝ) : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)) := by
    exact (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralDifferenceFrequency_exp
      S Ψ i.1.1 j.1.1 i.1.2 j.1.2 k).symm
  have hd : 0 < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
  have hVpos : 0 < V := by linarith
  have hpowpos : 0 < Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hbound : 0 ≤
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) := by
    unfold ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound
    positivity
  have hApos : 0 <
      4 * (Module.finrank ℚ F : ℝ) *
        (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ)) := by
    have hB : 0 <
        ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1 :=
      by linarith
    exact mul_pos (mul_pos (by positivity) hB) hpowpos
  have hδ : 0 <
      1 / (4 * (Module.finrank ℚ F : ℝ) *
        (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1) *
          Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ))) := one_div_pos.mpr hApos
  refine ⟨k, ?_⟩
  intro m
  have hlower := ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAngle_modInteger_lower
    hα hangle hexp m
  have hrecip :
      1 / (D : ℝ) ≤
        1 / (4 * (Module.finrank ℚ F : ℝ) *
          (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F) + 1) *
            Real.rpow (V ^ 2) (1 / (Module.finrank ℚ F : ℝ))) :=
    one_div_le_one_div_of_le hApos hD
  exact hrecip.trans hlower

private theorem conductorSieveIndex_phase_basisProduct
    (S : A1.SData F CE condη) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (V : ℝ)
    (i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V)
    (a : 𝓞 F) :
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase S ρ Ψ V i
        (algebraMap (𝓞 F) S.R a) =
      ∏ k : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
        OAI.LargePrimeGaps.bvExp
          ((((RingOfIntegers.basis F).repr a k : ℤ) : ℝ) *
            ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
              S Ψ i.1.1 i.1.2 k) := by
  rw [ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase,
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditivePhaseChar_apply,
    ρ.integral]
  rw [← ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralAdditivePhaseChar_apply]
  rw [ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralPhase_basisProduct]

private theorem conductorSieve_sum_chars_eq_sum_indices
    (S : A1.SData F CE condη) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) (V : ℝ)
    (g : AddChar S.R ℂ → ℝ) :
    (∑ χ ∈ ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveFrequencySet
        S ρ Ψ V, g χ) =
      ∑ i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
        g (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase S ρ Ψ V i) := by
  classical
  unfold ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveFrequencySet
  exact Finset.sum_image
    (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase_injective S ρ Ψ V).injOn

set_option maxHeartbeats 1000000

/-- The dual additive large sieve for the exact residue fractions on one exterior
dyad, uniform in the chosen primitive additive characters. Balancing uses the actual
number-field degree and both real and complex places. The norm-one dyad is T=1.
Guide: sol-thin-a2zf/PROOFS.md:720–732 (general-field extension of lem_additive_sieve).
Uses balanced generator compactness and distinct reduced fractions; feeds exterior dyad glue. -/
theorem conductor_additive_sieve_apply (S : A1.SData F CE condη)
    (G : ConductorGenerators S) (ρ : ConductorResidues S)
    (Ψ : ConductorAdditiveCharacters S) :
    ∃ C : ℝ, 0 < C ∧ ∀ T V : ℝ, 1 ≤ T → 2 ≤ V →
      ∀ b : S.ExtIdeal → ℂ,
        (∑ q ∈ conductorExteriorCutoff S V,
          ∑ d : (ConductorResidueRing q)ˣ,
            ‖∑ I ∈ conductorExteriorDyad S T,
              b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) ≤
          C * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
  classical
  obtain ⟨c, hc, hscale, houtside⟩ :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.exists_conductorGenerator_S_unit_scale S G
  obtain ⟨Cbox, hCbox, hbox⟩ :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorGenerators_dyad_coordinate_bound
      S G c hscale
  let dN : ℕ := Module.finrank ℚ F
  let d : ℝ := (Module.finrank ℚ F : ℝ)
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
  have hdim : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) = dN := by
    dsimp [dN]
    exact (Module.finrank_eq_card_basis (NumberField.integralBasis F)).symm
  let Bmul : ℝ :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound (F := F)
  let K : ℝ := Cbox + 8 * d * (Bmul + 1) + 4
  let C : ℝ := (12 : ℝ) ^ dN * K ^ dN * 2 ^ (dN + 1)
  have hBmul : 0 ≤ Bmul := by
    dsimp [Bmul, ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorBasisMultiplicationBound]
    positivity
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by positivity) (pow_pos hK _)) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro T V hT hV b
  let Troot : ℝ := Real.rpow (2 * T) (1 / d)
  let Vroot : ℝ := Real.rpow (V ^ 2) (1 / d)
  let L : ℕ := Nat.ceil (Cbox * Troot)
  let Asep : ℝ := 4 * d * (Bmul + 1) * Vroot
  let D : ℕ := Nat.ceil Asep
  let I := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let β := {J : S.ExtIdeal // J ∈ conductorExteriorDyad S T}
  let aI : S.ExtIdeal → 𝓞 F := fun J =>
    Classical.choose (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorScaledGenerator_integral
      S G c hscale J)
  have haI (J : S.ExtIdeal) :
      algebraMap (𝓞 F) F (aI J) = (c : F) * (G.gen J : F) :=
    Classical.choose_spec
      (ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorScaledGenerator_integral
        S G c hscale J)
  let x : β → I → ℤ := fun J k => (RingOfIntegers.basis F).repr (aI J.1) k
  have hx : ∀ J : β, ∀ k : I, |x J k| ≤ (L : ℤ) := by
    intro J k
    obtain ⟨a', ha', hcoord⟩ := hbox hT J.1 J.2
    have haeq : aI J.1 = a' := by
      apply IsFractionRing.injective (𝓞 F) F
      calc
        algebraMap (𝓞 F) F (aI J.1) = (c : F) * (G.gen J.1 : F) := haI J.1
        _ = algebraMap (𝓞 F) F a' := ha'.symm
    have hreal : |((x J k : ℤ) : ℝ)| ≤ Cbox * Troot := by
      simpa [x, haeq, Troot, d] using hcoord k
    have hrealL : |((x J k : ℤ) : ℝ)| ≤ (L : ℝ) :=
      hreal.trans (Nat.le_ceil (Cbox * Troot))
    exact_mod_cast hrealL
  have hxinj : Function.Injective x := by
    intro J J' hcoords
    have hrepr : (RingOfIntegers.basis F).repr (aI J.1) =
        (RingOfIntegers.basis F).repr (aI J'.1) := by
      simpa [x] using hcoords
    have haeq : aI J.1 = aI J'.1 :=
      (RingOfIntegers.basis F).repr.injective hrepr
    have hscaled :
        (c : F) * (G.gen J.1 : F) = (c : F) * (G.gen J'.1 : F) := by
      calc
        _ = algebraMap (𝓞 F) F (aI J.1) := (haI J.1).symm
        _ = algebraMap (𝓞 F) F (aI J'.1) := congrArg (algebraMap (𝓞 F) F) haeq
        _ = _ := haI J'.1
    have hcF : (c : F) ≠ 0 := by
      intro hz
      exact hc ((IsFractionRing.injective (𝓞 F) F) (by simpa using hz))
    have hgenF : (G.gen J.1 : F) = (G.gen J'.1 : F) :=
      mul_left_cancel₀ hcF hscaled
    have hgen : G.gen J.1 = G.gen J'.1 := by
      apply Subtype.ext
      exact hgenF
    have hJ : J.1 = J'.1 :=
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorGenerators_gen_injective S G hgen
    exact Subtype.ext hJ
  have hAsepPos : 0 < Asep := by
    dsimp [Asep]
    have hdpos : 0 < d := by
      dsimp [d]
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ F)
    exact mul_pos (mul_pos (mul_pos (by norm_num) hdpos)
      (by linarith [hBmul])) (Real.rpow_pos_of_pos (by nlinarith) _)
  have hDpos : 0 < D := Nat.ceil_pos.mpr hAsepPos
  have hDceil : Asep ≤ (D : ℝ) := Nat.le_ceil Asep
  let θ : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V → I → ℝ :=
    fun i k => ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorIntegralFrequencyVector
      S Ψ i.1.1 i.1.2 k
  have hsepIndex :=
    conductorSieveIndex_angle_sep S ρ Ψ hV D (by
      simpa [Asep, d, Bmul, Vroot] using hDceil)
  have hsep : ∀ i ∈ (Finset.univ :
      Finset (ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V)),
      ∀ j ∈ Finset.univ, i ≠ j → ∃ k : I, ∀ m : ℤ,
        1 / (D : ℝ) ≤ |θ i k - θ j k - (m : ℝ)| := by
    intro i hi j hj hij
    exact hsepIndex i j hij
  have hfinite :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorFiniteDimLargeSieve
      (s := (Finset.univ :
        Finset (ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V)))
      θ L D hDpos hsep
      (t := (Finset.univ : Finset β)) x hx hxinj (fun J => b J.1)
  have hscaleGen (J : β) :
      (algebraMap (𝓞 F) S.R c) * G.gen J.1 =
        algebraMap (𝓞 F) S.R (aI J.1) := by
    apply Subtype.ext
    change (c : F) * (G.gen J.1 : F) = algebraMap (𝓞 F) F (aI J.1)
    exact (haI J.1).symm
  have hphaseIndex (i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V)
      (J : β) :
      ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase S ρ Ψ V i
        ((algebraMap (𝓞 F) S.R c) * G.gen J.1) =
        ∏ k : I, OAI.LargePrimeGaps.bvExp
          ((x J k : ℤ) * (θ i k)) := by
    rw [hscaleGen J]
    simpa [x, θ] using
      conductorSieveIndex_phase_basisProduct S ρ Ψ V i (aI J.1)
  have hsampleIndex (i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V) :
      (∑ J : β, b J.1 * ∏ k : I,
        OAI.LargePrimeGaps.bvExp ((x J k : ℤ) * θ i k)) =
        ∑ J ∈ conductorExteriorDyad S T,
          b J * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
            S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J) := by
    calc
      _ = ∑ J : β, b J.1 *
          ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
            S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J.1) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hphaseIndex]
      _ = ∑ J ∈ conductorExteriorDyad S T,
          b J * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
            S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J) := by
        change (∑ J ∈ (conductorExteriorDyad S T).attach,
            b J.1 * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
              S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J.1)) = _
        exact Finset.sum_attach (conductorExteriorDyad S T)
          (fun J => b J *
            ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
              S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J))
  have hindexSum :
      (∑ χ ∈ ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveFrequencySet
          S ρ Ψ V,
        ‖∑ J ∈ conductorExteriorDyad S T,
          b J * χ ((algebraMap (𝓞 F) S.R c) * G.gen J)‖ ^ 2) =
        ∑ i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
          ‖∑ J ∈ conductorExteriorDyad S T,
            b J * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
              S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J)‖ ^ 2 :=
    conductorSieve_sum_chars_eq_sum_indices S ρ Ψ V
      (fun χ => ‖∑ J ∈ conductorExteriorDyad S T,
        b J * χ ((algebraMap (𝓞 F) S.R c) * G.gen J)‖ ^ 2)
  have hcoeff :
      (∑ J : β, ‖b J.1‖ ^ 2) =
        ∑ J ∈ conductorExteriorDyad S T, ‖b J‖ ^ 2 := by
    change (∑ J ∈ (conductorExteriorDyad S T).attach, ‖b J.1‖ ^ 2) = _
    exact Finset.sum_attach (conductorExteriorDyad S T) (fun J => ‖b J‖ ^ 2)
  have hindexBound :
      (∑ i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
        ‖∑ J ∈ conductorExteriorDyad S T,
          b J * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
            S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen J)‖ ^ 2) ≤
        (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I *
          ∑ J ∈ conductorExteriorDyad S T, ‖b J‖ ^ 2 := by
    calc
      _ = ∑ i ∈ (Finset.univ :
            Finset (ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V)),
            ‖∑ J : β, b J.1 * ∏ k : I,
              OAI.LargePrimeGaps.bvExp ((x J k : ℤ) * θ i k)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsampleIndex i]
      _ ≤ (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ Fintype.card I *
          ∑ J : β, ‖b J.1‖ ^ 2 := hfinite
      _ = _ := by rw [hcoeff]
  have hindexBoundNat := hindexBound
  rw [hdim] at hindexBoundNat
  have hscaled :=
    ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditive_reindex_with_scale
      S G ρ Ψ T V b c houtside
  have hmainIndex :
      (∑ q ∈ conductorExteriorCutoff S V,
        ∑ d : (ConductorResidueRing q)ˣ,
          ‖∑ I ∈ conductorExteriorDyad S T,
            b I * Ψ.ψ q (ρ.red q (G.gen I) * (d : ConductorResidueRing q))‖ ^ 2) =
        ∑ i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
          ‖∑ I ∈ conductorExteriorDyad S T,
            b I * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
              S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen I)‖ ^ 2 :=
    hscaled.trans hindexSum
  have hTroot1 : 1 ≤ Troot := by
    dsimp [Troot]
    exact Real.one_le_rpow (by nlinarith) (by positivity)
  have hVroot1 : 1 ≤ Vroot := by
    dsimp [Vroot]
    exact Real.one_le_rpow (by nlinarith) (by positivity)
  have hLupper : ((L + 1 : ℕ) : ℝ) ≤ Cbox * Troot + 2 := by
    have hceil : (L : ℝ) ≤ Cbox * Troot + 1 := by
      dsimp [L]
      exact (Nat.ceil_lt_add_one (show 0 ≤ Cbox * Troot by positivity)).le
    calc
      ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by exact_mod_cast Nat.cast_add L 1
      _ ≤ Cbox * Troot + 2 := by linarith
  have hDupper : (D : ℝ) ≤ Asep + 1 := by
    exact (Nat.ceil_lt_add_one hAsepPos.le).le
  have hRad : ((L + 1 : ℕ) : ℝ) + 2 * (D : ℝ) ≤
      Cbox * Troot + 8 * d * (Bmul + 1) * Vroot + 4 := by
    calc
      _ ≤ (Cbox * Troot + 2) + 2 * (Asep + 1) :=
        add_le_add hLupper (mul_le_mul_of_nonneg_left hDupper (by norm_num))
      _ = Cbox * Troot + 8 * d * (Bmul + 1) * Vroot + 4 := by
        dsimp [Asep]
        ring
  have hcoefT : Cbox + 4 ≤ K := by
    dsimp [K]
    have hnonneg : 0 ≤ 8 * d * (Bmul + 1) := by positivity
    linarith
  have hcoefV : 8 * d * (Bmul + 1) ≤ K := by
    dsimp [K]
    have hnonneg : 0 ≤ Cbox + 4 := by positivity
    linarith
  have hRadK : Cbox * Troot + 8 * d * (Bmul + 1) * Vroot + 4 ≤
      K * (Troot + Vroot) := by
    have hleft : Cbox * Troot + 8 * d * (Bmul + 1) * Vroot + 4 ≤
        (Cbox + 4) * Troot + (8 * d * (Bmul + 1)) * Vroot := by
      nlinarith [hTroot1]
    calc
      _ ≤ (Cbox + 4) * Troot + (8 * d * (Bmul + 1)) * Vroot := hleft
      _ ≤ K * Troot + K * Vroot :=
        add_le_add
          (mul_le_mul_of_nonneg_right hcoefT (by positivity))
          (mul_le_mul_of_nonneg_right hcoefV (by positivity))
      _ = K * (Troot + Vroot) := by ring
  have hsumPow {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
      (X + Y) ^ dN ≤ (2 : ℝ) ^ dN * (X ^ dN + Y ^ dN) := by
    have hmax : X + Y ≤ 2 * max X Y := by
      have hXmax := le_max_left X Y
      have hYmax := le_max_right X Y
      linarith
    have hmaxPow : (max X Y) ^ dN ≤ X ^ dN + Y ^ dN := by
      rcases le_total X Y with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (pow_nonneg hX _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (pow_nonneg hY _)
    calc
      _ ≤ (2 * max X Y) ^ dN := pow_le_pow_left₀ (add_nonneg hX hY) hmax _
      _ = (2 : ℝ) ^ dN * (max X Y) ^ dN := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ dN * (X ^ dN + Y ^ dN) :=
        mul_le_mul_of_nonneg_left hmaxPow (by positivity)
  have hTrootPow : Troot ^ dN = 2 * T := by
    have hpow : Real.rpow (2 * T) (1 / d) ^ (dN : ℝ) = 2 * T := by
      have hexp : (1 / d) = d⁻¹ := by field_simp [ne_of_gt hdpos]
      have hdn : (dN : ℝ) = d := by rfl
      rw [hexp, hdn]
      exact Real.rpow_inv_rpow (by positivity) (ne_of_gt hdpos)
    simpa [Troot, Real.rpow_natCast] using hpow
  have hVrootPow : Vroot ^ dN = V ^ 2 := by
    have hpow : Real.rpow (V ^ 2) (1 / d) ^ (dN : ℝ) = V ^ 2 := by
      have hexp : (1 / d) = d⁻¹ := by field_simp [ne_of_gt hdpos]
      have hdn : (dN : ℝ) = d := by rfl
      rw [hexp, hdn]
      exact Real.rpow_inv_rpow (by positivity) (ne_of_gt hdpos)
    simpa [Vroot, Real.rpow_natCast] using hpow
  have hfactor : (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ dN ≤
      C * (T + V ^ 2) := by
    have hRadK' : ((L + 1 : ℕ) : ℝ) + 2 * D ≤ K * (Troot + Vroot) :=
      hRad.trans hRadK
    calc
      _ ≤ (12 * (K * (Troot + Vroot))) ^ dN :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hRadK' (by norm_num)) _
      _ = (12 : ℝ) ^ dN * K ^ dN * (Troot + Vroot) ^ dN := by
        rw [mul_pow, mul_pow]
        ring
      _ ≤ (12 : ℝ) ^ dN * K ^ dN *
          ((2 : ℝ) ^ dN * (Troot ^ dN + Vroot ^ dN)) := by
        exact mul_le_mul_of_nonneg_left (hsumPow (by positivity) (by positivity))
          (by positivity)
      _ = (12 : ℝ) ^ dN * K ^ dN * (2 : ℝ) ^ dN * (2 * T + V ^ 2) := by
        rw [hTrootPow, hVrootPow]
        ring
      _ ≤ (12 : ℝ) ^ dN * K ^ dN * (2 : ℝ) ^ dN * (2 * (T + V ^ 2)) := by
        gcongr
        nlinarith
      _ = C * (T + V ^ 2) := by
        dsimp [C]
        rw [pow_succ]
        ring
  calc
    _ = ∑ i : ArtinPrimitiveRoots.Proofs.a2_cond_b.ConductorAdditiveIndex S V,
        ‖∑ I ∈ conductorExteriorDyad S T,
          b I * ArtinPrimitiveRoots.Proofs.a2_cond_b.conductorAdditiveIndexPhase
            S ρ Ψ V i ((algebraMap (𝓞 F) S.R c) * G.gen I)‖ ^ 2 := hmainIndex
    _ ≤ (12 * (((L + 1 : ℕ) : ℝ) + 2 * D)) ^ dN *
        ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := hindexBoundNat
    _ ≤ C * (T + V ^ 2) * ∑ I ∈ conductorExteriorDyad S T, ‖b I‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfactor
        (Finset.sum_nonneg fun I hi => sq_nonneg (‖b I‖))

end ArtinPrimitiveRoots.A2
