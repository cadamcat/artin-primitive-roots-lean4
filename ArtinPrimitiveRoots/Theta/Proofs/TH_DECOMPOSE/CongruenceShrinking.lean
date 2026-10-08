import ArtinPrimitiveRoots.Theta.Proofs.TH_DECOMPOSE.LocalSixthPower

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

/-- One congruence level forces every rational cusp diagonal ratio into the global Lagrangian. -/
theorem exists_cusp_lagrangian_congruence (P : CoverPackage D S H A) (G : GlobalDatum P) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ (ArtinPrimitiveRoots.A1.Spec.congrSubgroup F N).FiniteIndex ∧
      ∀ (σ : Matrix.SpecialLinearGroup (Fin 2) F)
        (γ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 F)),
      γ ∈ ArtinPrimitiveRoots.A1.Spec.congrSubgroup F N → ∀ (ε : (𝓞 F)ˣ) (μ : F),
      σ⁻¹ * ArtinPrimitiveRoots.A1.Spec.toSLF F γ * σ =
        ArtinPrimitiveRoots.A1.Spec.cuspUnitMatrix F ε μ →
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom ε) ^ 2 ∈ G.Δ := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
