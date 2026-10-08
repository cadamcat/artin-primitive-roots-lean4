import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.LocalSixthPower
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
open NumberField IsDedekindDomain Filter
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- A common nonzero modulus makes all integral elements small at the prescribed places. -/
theorem exists_small_congruence_ideal (T : Finset (FinPlace F)) (r : FinPlace F → ℝ)
    (hr : ∀ v ∈ T, 0 < r v) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ ∀ v ∈ T, ∀ a ∈ N,
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F a)‖ < r v := by
  let E (v : FinPlace F) : (𝓞 F) →+* v.adicCompletion F :=
    (NumberField.FinitePlace.embedding v).comp (algebraMap (𝓞 F) F)
  have hnorm (v : FinPlace F) (z : 𝓞 F) : ‖E v z‖ ≤ 1 :=
    NumberField.FinitePlace.norm_le_one F v z
  have hex (v : T) : ∃ z : 𝓞 F, z ∈ v.val.asIdeal ∧ z ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.val.ne_bot
  let b : T → 𝓞 F := fun v => Classical.choose (hex v)
  have hbmem (v : T) : b v ∈ v.val.asIdeal := (Classical.choose_spec (hex v)).1
  have hb0 (v : T) : b v ≠ 0 := (Classical.choose_spec (hex v)).2
  have hexn (v : T) : ∃ n : ℕ, ‖E v.val (b v)‖ ^ n < r v.val := by
    apply exists_pow_lt_of_lt_one (hr v.val v.property)
    exact (NumberField.FinitePlace.norm_lt_one_iff_mem F v.val (b v)).mpr (hbmem v)
  let n : T → ℕ := fun v => Classical.choose (hexn v)
  have hn (v : T) : ‖E v.val (b v)‖ ^ n v < r v.val := Classical.choose_spec (hexn v)
  let M : 𝓞 F := ∏ v : T, b v ^ n v
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => pow_ne_zero _ (hb0 v))
  have hMsmall (v : FinPlace F) (hv : v ∈ T) : ‖E v M‖ < r v := by
    let w : T := ⟨v, hv⟩
    have hp : ‖E v M‖₊ ≤ ‖E v (b w ^ n w)‖₊ := by
      dsimp only [M]
      rw [map_prod, nnnorm_prod]
      simpa only [Finset.prod_singleton] using
        (Finset.prod_le_prod_of_subset_of_le_one
          (f := fun i : T => ‖E v (b i ^ n i)‖₊)
          (Finset.subset_univ ({w} : Finset T))
          (fun i _ _ => by exact_mod_cast hnorm v (b i ^ n i)))
    calc
      ‖E v M‖ ≤ ‖E v (b w ^ n w)‖ := by exact_mod_cast hp
      _ = ‖E v (b w)‖ ^ n w := by rw [map_pow, norm_pow]
      _ < r v := hn w
  let N : Ideal (𝓞 F) := Ideal.span {M}
  have hN : N ≠ ⊥ := by
    intro h
    have hmem : M ∈ N := Ideal.subset_span (by simp)
    exact hM0 (by simpa only [h, Submodule.mem_bot] using hmem)
  refine ⟨N, hN, fun v hv a ha => ?_⟩
  change a ∈ Ideal.span {M} at ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
  change ‖E v (M * c)‖ < r v
  calc
    ‖E v (M * c)‖ = ‖E v M‖ * ‖E v c‖ := by rw [map_mul, norm_mul]
    _ ≤ ‖E v M‖ := mul_le_of_le_one_right (norm_nonneg _) (hnorm v c)
    _ < r v := hMsmall v hv

private theorem integral_unit_isLocUnit (v : FinPlace F) (ε : (𝓞 F)ˣ) :
    IsLocUnit v (toLoc v (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε)) := by
  have hint (z : 𝓞 F) : algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F z) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      v.valuedAdicCompletion_eq_valuation'] using v.valuation_le_one z
  constructor
  · exact hint (ε : 𝓞 F)
  · exact hint (↑ε⁻¹ : 𝓞 F)

/-- One congruence level forces every rational cusp diagonal ratio into the global Lagrangian. -/
theorem exists_cusp_lagrangian_congruence (P : CoverPackage D S H A) (G : GlobalDatum P) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ (ArtinPrimitiveRoots.A1.Spec.congrSubgroup F N).FiniteIndex ∧
      ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) F)
        (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
      γ ∈ ArtinPrimitiveRoots.A1.Spec.congrSubgroup F N → ∀ (ε : (𝓞 F)ˣ) (μ : F),
      σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ * σ =
        ArtinPrimitiveRoots.A1.Spec.cuspUnitMatrix F ε μ →
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε) ^ 2 ∈ G.Δ := by
  let r : FinPlace F → ℝ := fun v => Classical.choose (local_sixth_power_threshold v)
  have hr (v : FinPlace F) : 0 < r v :=
    (Classical.choose_spec (local_sixth_power_threshold v)).1
  have hroot (v : FinPlace F) (u : (v.adicCompletion F)ˣ)
      (hu : ‖(u : v.adicCompletion F) - 1‖ < r v) :
      ∃ t : (v.adicCompletion F)ˣ, t ^ 6 = u :=
    (Classical.choose_spec (local_sixth_power_threshold v)).2 u hu
  obtain ⟨N, hN, hsmall⟩ := exists_small_congruence_ideal S.Sf (fun v => r v ^ 2)
    (fun v _ => sq_pos_of_pos (hr v))
  let : Finite (𝓞 F ⧸ N) := N.finiteQuotientOfFreeOfNeBot hN
  have hfinite : (Spec.congrSubgroup F N).FiniteIndex := by
    unfold Spec.congrSubgroup
    infer_instance
  refine ⟨N, hN, hfinite, ?_⟩
  intro σ γ hγ ε μ hconj
  let u : Fˣ := Units.map (algebraMap (𝓞 F) F).toMonoidHom ε
  let t : 𝓞 F := γ 0 0 + γ 1 1 - 2
  have hk : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk N) γ = 1 := hγ
  have hii (i : Fin 2) : Ideal.Quotient.mk N (γ i i) = 1 := by
    have h := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F ⧸ N) => M i i) hk
    simpa using h
  have htmem : t ∈ N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simp only [t, map_add, map_sub, map_ofNat, hii]
    ring
  have htrace : algebraMap (𝓞 F) F t = (u : F) + (u : F)⁻¹ - 2 := by
    have htr : Matrix.trace (Spec.cuspUnitMatrix F ε μ : Matrix (Fin 2) (Fin 2) F) =
        Matrix.trace (Spec.toSLF F γ : Matrix (Fin 2) (Fin 2) F) := by
      rw [← hconj]
      exact Matrix.trace_units_conj' σ.toGL (Spec.toSLF F γ)
    simpa [t, u, Spec.cuspUnitMatrix, Spec.toSLF, Matrix.trace_fin_two,
      map_add, map_sub, map_ofNat] using congrArg (fun x : F => x - 2) htr.symm
  have hid : ((u : F) - 1) ^ 2 = (u : F) * algebraMap (𝓞 F) F t := by
    rw [htrace]
    field_simp
    ring
  have hnorm (v : FinPlace F) :
      ‖NumberField.FinitePlace.embedding v (u : F)‖ = 1 := by
    let E : (𝓞 F) →+* v.adicCompletion F :=
      (NumberField.FinitePlace.embedding v).comp (algebraMap (𝓞 F) F)
    have h1 : ‖E (ε : 𝓞 F)‖ ≤ 1 := NumberField.FinitePlace.norm_le_one F v _
    have h2 : ‖E (↑ε⁻¹ : 𝓞 F)‖ ≤ 1 := NumberField.FinitePlace.norm_le_one F v _
    have hmul : ‖E (ε : 𝓞 F)‖ * ‖E (↑ε⁻¹ : 𝓞 F)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    change ‖E (ε : 𝓞 F)‖ = 1
    have hle : 1 ≤ ‖E (ε : 𝓞 F)‖ := by
      calc
        1 = ‖E (ε : 𝓞 F)‖ * ‖E (↑ε⁻¹ : 𝓞 F)‖ := hmul.symm
        _ ≤ ‖E (ε : 𝓞 F)‖ := mul_le_of_le_one_right (norm_nonneg _) h2
    exact le_antisymm h1 hle
  change u ^ 2 ∈ G.Δ
  rw [GlobalDatum.Δ, Subgroup.mem_iInf]
  intro v
  change toLoc v (u ^ 2) ∈ G.Alag v
  by_cases hv : v ∈ S.Sf
  · have hsq : ‖NumberField.FinitePlace.embedding v (u : F) - 1‖ ^ 2 =
        ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F t)‖ := by
      have h := congrArg (fun x : F => ‖NumberField.FinitePlace.embedding v x‖) hid
      simpa only [map_pow, map_sub, map_one, map_mul, norm_pow, norm_mul,
        hnorm v, one_mul] using h
    have hclose : ‖((toLoc v u : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1‖ < r v := by
      change ‖NumberField.FinitePlace.embedding v (u : F) - 1‖ < r v
      have hlt : ‖NumberField.FinitePlace.embedding v (u : F) - 1‖ ^ 2 < r v ^ 2 :=
        hsq.trans_lt (hsmall v hv t htmem)
      nlinarith [norm_nonneg (NumberField.FinitePlace.embedding v (u : F) - 1), hr v]
    obtain ⟨b, hb⟩ := hroot v (toLoc v u) hclose
    have heq : toLoc v (u ^ 2) = (b ^ 4) ^ 3 := by
      rw [map_pow, ← hb, ← pow_mul, ← pow_mul]
    rw [heq]
    exact G.alag_cubes v (b ^ 4)
  · apply (G.alag_tame v hv _).mpr
    refine ⟨0, toLoc v (u ^ 2), ?_, by simp⟩
    change IsLocUnit v (toLoc v ((Units.map (algebraMap (𝓞 F) F).toMonoidHom ε) ^ 2))
    rw [← map_pow]
    exact integral_unit_isLocUnit v (ε ^ 2)

end ArtinPrimitiveRoots.A1.Theta
