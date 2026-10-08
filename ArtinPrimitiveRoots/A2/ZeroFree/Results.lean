import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_sieve_assemble
import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Hilbert
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Hecke.Defs

/-!
# Section 6: conductor sieve, zero density, and the final A2 theorem
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- The raw complete ideal Dirichlet series associated with an idelic character; its stated
continuation is packaged separately below. Corrected per rev-a2. -/
def heckeLSeries (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- The raw incomplete ideal Dirichlet series with the Euler factors at `S` omitted; its stated
continuation is packaged separately below. Corrected per rev-a2. -/
def incompleteHeckeLSeries (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ ∀ v ∈ S.Sf, ¬ I ≤ v.asIdeal},
    χ.idealValue I.1 * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)

/-- Entire continuation of a complete Hecke Dirichlet series, identified with the raw sum only
where that sum converges absolutely. Added for the rev-a2 continuation correction. -/
structure HeckeLContinuation (χ : ArtinPrimitiveRoots.A1.HeckeChar F) where
  value : ℂ → ℂ
  differentiable : Differentiable ℂ value
  agrees : ∀ s : ℂ, 1 < s.re → value s = heckeLSeries χ s

/-- Analytic continuation of an incomplete Hecke series to the zero-free half-plane, identified
with its raw sum only in the absolute-convergence region. Added per rev-a2. -/
structure IncompleteHeckeLContinuation
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) where
  value : ℂ → ℂ
  differentiableOn : DifferentiableOn ℂ value {s : ℂ | 997 / 1000 < s.re}
  agrees : ∀ s : ℂ, 1 < s.re → value s = incompleteHeckeLSeries S χ s

/-- Uniform convexity growth for primitive finite-order Hecke characters. The exponent `A_F`
is part of the hypothesis, so detector estimates cannot choose it independently of the bound.
Corrected per sol-gate-a2, `zf:detector-shift` and `zf:detector-count` (06:139-153, 249-264). -/
def ConductorHeightBound (A_F : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : ArtinPrimitiveRoots.A1.HeckeChar F), IsOfFinOrder ω → ω ≠ 1 →
      ∀ f : Ideal (𝓞 F), IsPrimitiveConductor ω f →
        ∀ L : HeckeLContinuation ω, ∀ s : ℂ,
          3 / 1000 ≤ s.re → s.re ≤ 4 →
            ‖L.value s‖ ≤ C * Real.rpow (Ideal.absNorm f : ℝ) (1 / 2 + ε) *
              Real.rpow (2 + |s.im|) A_F

/-- **lem:conductor-sieve** (06-zero-free.tex:37-137). Fixed data and `ε` precede both growing
lengths; the constant is uniform over the family and its coefficients. Uses the corrected
nonzero primitive-conductor predicate from rev-a2. -/
theorem lem_conductor_sieve
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (𝓛S : Finset (SLocalCharacter S)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (N U : ℝ), 2 ≤ N → 2 ≤ U →
        ∀ (𝓧 : Finset (ArtinPrimitiveRoots.A1.HeckeChar F)),
          (∀ ω ∈ 𝓧, IsOfFinOrder ω ∧ SComponent S ω ∈ 𝓛S ∧
            ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor ω 𝔣 ∧
              (Ideal.absNorm 𝔣 : ℝ) ≤ C₀ * U) →
          ∀ b : Ideal (𝓞 F) → ℂ,
            (∑ ω ∈ 𝓧,
              ‖∑ I ∈ (Ideal.finite_setOfPred_absNorm_le
                  (S := 𝓞 F) ⌊N⌋₊).toFinset,
                  b I * ω.idealValue I‖ ^ 2) ≤
              C * (N + U ^ 2) * Real.rpow (N * U) ε *
                ∑ I ∈ (Ideal.finite_setOfPred_absNorm_le
                    (S := 𝓞 F) ⌊N⌋₊).toFinset, ‖b I‖ ^ 2 := by
  exact conductor_sieve_assemble S C₀ hC₀ 𝓛S

/-- **MISSING A1 frequency interface**: the sixth-power-free representative set `𝒰`, its norm,
Kummer characters, primitive twists, and the unique factorization map of 02:285-387. Corrected per
rev-a2 to include the quantitative row, conductor, distinctness, and decomposition hypotheses
needed by the zero-density argument. Corrected per sol-gate-a2 to express induction as equality
of full idelic characters, allowing exterior ramification of the Kummer twist. -/
structure FrequencyData (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) where
  U : Type
  q : U → ℝ
  q_pos : ∀ u, 0 < q u
  one : U
  q_one : q one = 1
  repr : U → S.R
  repr_nonzero : ∀ u, (repr u : F) ≠ 0
  q_eq_absS : ∀ u, q u = S.absS (S.diag (repr u : F))
  sixth_power_free : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (repr u : F)) ∧
    FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (repr u : F)) < 6
  decomposition : ∀ x : S.R, (x : F) ≠ 0 →
    ∃! ui : U × ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
      ∃ ε : S.US, ∃ a : Fˣ,
        S.IsGen (a : F) ui.2.1 ∧
        (x : F) = (repr ui.1 : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6
  kummer : U → ArtinPrimitiveRoots.A1.HeckeChar F
  kummer_one : kummer one = 1
  kummer_principal_iff : ∀ u, kummer u = 1 ↔ u = one
  omega : U → ArtinPrimitiveRoots.A1.HeckeChar F
  omega_finiteOrder : ∀ u, IsOfFinOrder (omega u)
  omega_primitive : ∀ u, ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor (omega u) 𝔣
  /-- The primitive induction preserves the full idelic character, including ramified places. -/
  omega_induces_twist : ∀ u, omega u = η * (kummer u)⁻¹
  kummer_local : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    ArtinPrimitiveRoots.A1.residue v (repr u) ≠ 0 →
      (kummer u).UnramifiedAt v ∧
        (kummer u).primeValue v = ArtinPrimitiveRoots.A1.chi D v (repr u)
  /-- Masked exterior Kummer prime values, including positive valuations. The character value is
  zero when the representative is divisible by the prime. Added for `prop:euler-product`
  (05:407–433), following `sol-thin-a2rp/PROOFS.md` 632–640. -/
  kummer_primeValue_masked : ∀ u (v : ArtinPrimitiveRoots.A1.FinPlace F), v ∉ S.Sf →
    (kummer u).primeValue v =
      if ArtinPrimitiveRoots.A1.residue v (repr u) = 0 then 0
      else ArtinPrimitiveRoots.A1.chi D v (repr u)

  q_ge_one : ∀ u, 1 ≤ q u
  dyadic_count : ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
    {u : U | X ≤ q u ∧ q u < 2 * X}.Finite ∧
    (Set.ncard {u : U | X ≤ q u ∧ q u < 2 * X} : ℝ) ≤ C * X
  /-- The compact initial shell needed when the requested dyadic parameter is in [1,2). -/
  low_shell_bound : ∃ C : ℝ, 0 < C ∧
    {u : U | 1 ≤ q u ∧ q u < 4}.Finite ∧
      (Set.ncard {u : U | 1 ≤ q u ∧ q u < 4} : ℝ) ≤ C
  kummer_injective : ∀ u v, kummer u = kummer v → u = v
  omega_injective : ∀ u v, omega u = omega v → u = v
  conductor_bound : ∃ C : ℝ, 0 < C ∧ ∀ u,
    ∃ 𝔣 : Ideal (𝓞 F), IsPrimitiveConductor (omega u) 𝔣 ∧
      (Ideal.absNorm 𝔣 : ℝ) ≤ C * q u
  local_components_finite : ∃ 𝓛S : Finset (SLocalCharacter S),
    ∀ u, SComponent S (omega u) ∈ 𝓛S
  decomposition_surjective : ∀ u : U, ∀ I : ArtinPrimitiveRoots.A1.SData.ExtIdeal S,
    ∃ x : S.R, (x : F) ≠ 0 ∧ ∃ ε : S.US, ∃ a : Fˣ,
      S.IsGen (a : F) I.1 ∧
      (x : F) = (repr u : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6
  /-- S-integer conductor bounds, including the possibly ramified induced twist. -/
  kummer_twist_conductor_bound : IsOfFinOrder η →
    (∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf → η.UnramifiedAt v) →
      ∃ C : ℝ, 0 < C ∧ ∀ u,
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (kummer u).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * q u) ∧
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧ (η * (kummer u)⁻¹).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * q u)

private theorem frequency_absFin_one (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.A1.absFin v 1 = 1 := by
  have hv : (Ideal.absNorm v.asIdeal : NNReal) ≠ 0 :=
    HeightOneSpectrum.absNorm_ne_zero v
  simp [ArtinPrimitiveRoots.A1.absFin, hv]

private theorem frequency_absS_mul (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x y : S.FS) : S.absS (x * y) = S.absS x * S.absS y := by
  have hnorm (v : S.Sf) : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    have hv : (Ideal.absNorm v.1.asIdeal : NNReal) ≠ 0 :=
      HeightOneSpectrum.absNorm_ne_zero v.1
    exact_mod_cast hv
  simp [ArtinPrimitiveRoots.A1.SData.absS, ArtinPrimitiveRoots.A1.absFin,
    hnorm, Finset.prod_mul_distrib, Complex.normSq_mul]
  ring

private theorem frequency_absS_one (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    S.absS (1 : S.FS) = 1 := by
  simp [ArtinPrimitiveRoots.A1.SData.absS, frequency_absFin_one]

private theorem frequency_absS_mul_inv (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (u : S.FSˣ) :
    S.absS (u : S.FS) * S.absS ((u⁻¹ : S.FSˣ) : S.FS) = 1 := by
  calc
    _ = S.absS ((u : S.FS) * ((u⁻¹ : S.FSˣ) : S.FS)) :=
      (frequency_absS_mul S _ _).symm
    _ = S.absS (1 : S.FS) := by
      congr 1
      exact congrArg Units.val (mul_inv_cancel u)
    _ = 1 := frequency_absS_one S

private theorem frequency_diagU_mem_diagR
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (e : S.US) :
    (S.diagU (e : Fˣ) : S.FS) ∈ S.diagR := by
  have heVal : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F ((e : Fˣ) : F) = 1 := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F ((e : Fˣ) : F) = 1
    exact e.2
  have hR : ((e : Fˣ) : F) ∈ S.R := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F ((e : Fˣ) : F) ≤ 1
    intro v hv
    rw [heVal v hv]
  refine ⟨⟨(e : Fˣ), hR⟩, ?_⟩
  simp [ArtinPrimitiveRoots.A1.SData.diagR, ArtinPrimitiveRoots.A1.SData.diagU]

private def frequency_diagRAddSubgroup (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    AddSubgroup S.FS where
  carrier := S.diagR
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp [ArtinPrimitiveRoots.A1.SData.diagR, ArtinPrimitiveRoots.A1.SData.diag]
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    simp [ArtinPrimitiveRoots.A1.SData.diagR, ArtinPrimitiveRoots.A1.SData.diag]
  neg_mem' := by
    rintro x ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    simp [ArtinPrimitiveRoots.A1.SData.diagR, ArtinPrimitiveRoots.A1.SData.diag]

private theorem frequency_diagU_injective (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    Function.Injective (fun e : S.US => S.diagU (e : Fˣ)) := by
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  have hval : S.diag ((a : Fˣ) : F) = S.diag ((b : Fˣ) : F) := by
    simpa [ArtinPrimitiveRoots.A1.SData.diagU] using congrArg Units.val hab
  let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  have hw : w.embedding ((a : Fˣ) : F) = w.embedding ((b : Fˣ) : F) := by
    have h := congrArg (fun z : S.FS => z.2 w) hval
    simpa [ArtinPrimitiveRoots.A1.SData.diag] using h
  exact w.embedding.injective hw

private theorem frequency_diagUS_norm_one (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (e : S.US) :
    S.absS ((S.diagU (e : Fˣ) : S.FSˣ) : S.FS) = 1 := by
  have heR : ((e : Fˣ) : F) ∈ S.R := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F ((e : Fˣ) : F) ≤ 1
    intro v hv
    have hval : v.valuation F ((e : Fˣ) : F) = 1 := by
      change v.valuation F ((e : Fˣ) : F) = 1
      exact e.2 v hv
    rw [hval]
  let z : S.FSˣ := S.diagU (e : Fˣ)
  have hge : 1 ≤ S.absS (z : S.FS) := by
    simpa [z, ArtinPrimitiveRoots.A1.SData.diagU] using
      S.absS_diag_ge_one D ⟨(e : Fˣ), heR⟩ (Units.ne_zero (e : Fˣ))
  have hgeInv : 1 ≤ S.absS ((z⁻¹ : S.FSˣ) : S.FS) := by
    have hRinv : (((e⁻¹ : S.US) : Fˣ) : F) ∈ S.R := by
      change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
        v.valuation F (((e⁻¹ : S.US) : Fˣ) : F) ≤ 1
      intro v hv
      have hval : v.valuation F (((e⁻¹ : S.US) : Fˣ) : F) = 1 := by
        change v.valuation F (((e⁻¹ : S.US) : Fˣ) : F) = 1
        exact (e⁻¹ : S.US).2 v hv
      rw [hval]
    have htmp : 1 ≤ S.absS
        (S.diag (((e⁻¹ : S.US) : Fˣ) : F)) :=
      S.absS_diag_ge_one D ⟨((e⁻¹ : S.US) : Fˣ), hRinv⟩
        (Units.ne_zero ((e⁻¹ : S.US) : Fˣ))
    have hzInv : (z⁻¹ : S.FSˣ) =
        S.diagU ((e⁻¹ : S.US) : Fˣ) := by
      dsimp [z, ArtinPrimitiveRoots.A1.SData.diagU]
      simp
    rw [hzInv]
    exact htmp
  have hmul := frequency_absS_mul_inv S z
  nlinarith

private theorem frequency_unitSix_finite (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    Finite (ArtinPrimitiveRoots.A2.UnitSix S) := by
  classical
  letI : IsTotallyComplex F := D.isTotallyComplex
  obtain ⟨K, hK, hrep⟩ := S.FSOne_quotient_compact D
  let L : Set S.FS := K ∩ S.diagR
  let Radd := frequency_diagRAddSubgroup S
  have hRdisc : IsDiscrete (Radd : Set S.FS) := by
    change IsDiscrete (S.diagR : Set S.FS)
    exact (S.diagR_discrete_cocompact D).1
  letI : DiscreteTopology Radd := SetLike.isDiscrete_iff_discreteTopology.mp hRdisc
  have hRclosed : IsClosed (S.diagR : Set S.FS) := by
    change IsClosed (Radd : Set S.FS)
    exact Radd.isClosed_of_discreteTopology
  have hLcompact : IsCompact L := hK.inter_right hRclosed
  have hLdiscrete : IsDiscrete L :=
    (S.diagR_discrete_cocompact D).1.mono Set.inter_subset_right
  have hLfinite : L.Finite := hLcompact.finite hLdiscrete
  let T : Set S.US := {e | (S.diagU (e : Fˣ) : S.FS) ∈ K}
  have hTfinite : T.Finite := by
    let T' : Set S.US := {e | (S.diagU (e : Fˣ) : S.FS) ∈ L}
    have hT' : T'.Finite := by
      apply hLfinite.preimage
      intro a ha b hb hab
      exact frequency_diagU_injective S (by
        apply Units.ext
        exact congrArg id hab)
    apply hT'.subset
    intro e he
    change (S.diagU (e : Fˣ) : S.FS) ∈ L
    refine ⟨he, ?_⟩
    exact frequency_diagU_mem_diagR S e
  let f : {e : S.US // e ∈ T} → ArtinPrimitiveRoots.A2.UnitSix S :=
    fun e => QuotientGroup.mk e.1
  have hf : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn with
    | _ e =>
      let z : S.FSˣ := S.diagU (e : Fˣ)
      have hz : S.absS (z : S.FS) = 1 := by
        simpa [z] using frequency_diagUS_norm_one D S e
      obtain ⟨y, hyK, hrel⟩ := hrep ⟨z, hz⟩
      rcases hrel with ⟨v, hv⟩
      let e' : S.US := e * v⁻¹ ^ 6
      have hdiag : S.diagU (e' : Fˣ) = y.1 := by
        have heval : (e' : Fˣ) = (e : Fˣ) * ((v : Fˣ)⁻¹) ^ 6 := rfl
        have hv' : S.diagU (e : Fˣ) = S.diagU (v : Fˣ) ^ 6 * y.1 := by
          simpa [z] using hv
        calc
          S.diagU (e' : Fˣ) =
              S.diagU ((e : Fˣ) * ((v : Fˣ)⁻¹) ^ 6) := by rw [heval]
          _ = S.diagU (e : Fˣ) * S.diagU (((v : Fˣ)⁻¹) ^ 6) := map_mul _ _ _
          _ = S.diagU (e : Fˣ) * (S.diagU (v : Fˣ))⁻¹ ^ 6 := by
            rw [map_pow, map_inv]
          _ = y.1 := by
            rw [hv']
            calc
              _ = (S.diagU (v : Fˣ) ^ 6 * (S.diagU (v : Fˣ)) ^ (-6 : ℤ)) * y.1 := by ac_rfl
              _ = y.1 := by
                rw [show S.diagU (v : Fˣ) ^ 6 *
                    (S.diagU (v : Fˣ)) ^ (-6 : ℤ) = 1 by
                      rw [← zpow_natCast, zpow_neg]
                      simp]
                simp
      have he'T : e' ∈ T := by
        change (S.diagU (e' : Fˣ) : S.FS) ∈ K
        rw [hdiag]
        exact hyK
      refine ⟨⟨e', he'T⟩, ?_⟩
      change QuotientGroup.mk (e * (v⁻¹ ^ 6)) = QuotientGroup.mk e
      exact QuotientGroup.mk_mul_of_mem e ⟨v⁻¹, rfl⟩
  haveI : Finite {e : S.US // e ∈ T} := hTfinite.to_subtype
  exact Finite.of_surjective f hf

private def FrequencySixFreeExtIdeal (S : ArtinPrimitiveRoots.A1.SData F CE condη) :=
  {I : S.ExtIdeal // ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
    FractionalIdeal.count F v
      (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) < 6}

private abbrev FrequencyIndex (S : ArtinPrimitiveRoots.A1.SData F CE condη) :=
  FrequencySixFreeExtIdeal S × ArtinPrimitiveRoots.A2.UnitSix S

private theorem frequency_ext_absNorm_pos
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : S.ExtIdeal) : 0 < Ideal.absNorm I.1 :=
  Ideal.absNorm_pos_of_nonZeroDivisors
    ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
      simpa [Ideal.zero_eq_bot] using I.2.1)⟩

private theorem frequency_one_isExterior (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    S.IsExterior (1 : Ideal (𝓞 F)) := by
  refine ⟨by simp, ?_⟩
  intro v hv hle
  have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
    simpa [Ideal.one_eq_top] using hle
  have hneq : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  exact hneq (top_le_iff.mp htop)

private noncomputable def frequencyUnitClassRepresentative
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (u : ArtinPrimitiveRoots.A2.UnitSix S) : S.US := Quotient.out u

private theorem frequency_unitClassRepresentative_spec
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (u : ArtinPrimitiveRoots.A2.UnitSix S) :
    QuotientGroup.mk (frequencyUnitClassRepresentative S u) = u := Quotient.out_eq' u

private noncomputable def frequencyAllowedGenerator
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (I : S.ExtIdeal) : Fˣ :=
  Classical.choose (ArtinPrimitiveRoots.A1.BData.exists_allowed Bd I.1 I.2)

private theorem frequencyAllowedGenerator_spec
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (I : S.ExtIdeal) :
    S.IsGen (frequencyAllowedGenerator D S H Bd I : F) I.1 :=
  (Classical.choose_spec
    (ArtinPrimitiveRoots.A1.BData.exists_allowed Bd I.1 I.2)).1

private theorem frequency_count_spanSingleton_div (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) -
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul F v
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)),
    FractionalIdeal.count_inv]
  ring

private theorem frequency_count_spanSingleton_eq_neg_log_intValuation
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private theorem frequency_count_spanSingleton_eq_neg_log_valuation
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (z : F) (hz : z ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) z) =
      -WithZero.log (HeightOneSpectrum.valuation F v z) := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) z
  have hn : n ≠ 0 := by
    intro hn
    apply hz
    rw [← hnd, IsFractionRing.mk'_eq_div, hn, map_zero, zero_div]
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hmapn : (algebraMap (𝓞 F) F n) ≠ 0 := by
    intro h
    exact hn ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hmapd : (algebraMap (𝓞 F) F (d : 𝓞 F)) ≠ 0 := by
    intro h
    exact hd ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  have hval : HeightOneSpectrum.valuation F v z =
      v.intValuation n / v.intValuation (d : 𝓞 F) := by
    rw [← hnd]
    exact v.valuation_of_mk'
  rw [hval, ← hnd, IsFractionRing.mk'_eq_div,
    frequency_count_spanSingleton_div v
      (algebraMap (𝓞 F) F n) (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    frequency_count_spanSingleton_eq_neg_log_intValuation v n hn,
    frequency_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn)
      (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private theorem frequency_generator_mem_Sintegers
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : S.ExtIdeal) (a : Fˣ)
    (hgen : S.IsGen (a : F) I.1) : (a : F) ∈ S.R := by
  change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
    v.valuation F (a : F) ≤ 1
  intro v hv
  have hcount := hgen.2.2 v hv
  have hnonneg : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
    rw [hcount]
    exact FractionalIdeal.count_coe_nonneg F v I.1
  have hprincipal : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        -WithZero.log (v.valuation F (a : F)) :=
    frequency_count_spanSingleton_eq_neg_log_valuation v _ (Units.ne_zero a)
  have hlog : WithZero.log (v.valuation F (a : F)) ≤ 0 := by
    have : 0 ≤ -WithZero.log (v.valuation F (a : F)) := by
      rw [← hprincipal]
      exact hnonneg
    linarith
  have hvalNe : v.valuation F (a : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).2
    exact Units.ne_zero a
  calc
    _ = WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
      (WithZero.exp_log hvalNe).symm
    _ ≤ WithZero.exp 0 := WithZero.exp_le_exp.mpr hlog
    _ = 1 := WithZero.exp_zero

private theorem frequency_one_count (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    FractionalIdeal.count F v (1 : Ideal (𝓞 F)) = 0 := by
  have hcoe : ((1 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 1 := by
    rw [Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  rw [hcoe, FractionalIdeal.count_one]

private theorem frequency_generator_one_mem_US
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (a : Fˣ)
    (hgen : S.IsGen (a : F) (1 : Ideal (𝓞 F))) : a ∈ S.US := by
  change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
    v.valuation F (a : F) = 1
  intro v hv
  have hcount := hgen.2.2 v hv
  have hprincipal : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        -WithZero.log (v.valuation F (a : F)) :=
    frequency_count_spanSingleton_eq_neg_log_valuation v _ (Units.ne_zero a)
  have hlog : WithZero.log (v.valuation F (a : F)) = 0 := by
    have h0 : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = 0 := by
      rw [hcount, frequency_one_count]
    rw [hprincipal] at h0
    linarith
  have hvalNe : v.valuation F (a : F) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).2
    exact Units.ne_zero a
  calc
    _ = WithZero.exp (WithZero.log (v.valuation F (a : F))) :=
      (WithZero.exp_log hvalNe).symm
    _ = WithZero.exp 0 := by rw [hlog]
    _ = 1 := WithZero.exp_zero

private noncomputable def frequencyOne
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) : FrequencyIndex S := by
  let I : S.ExtIdeal := ⟨1, frequency_one_isExterior S⟩
  let a : Fˣ := frequencyAllowedGenerator D S H Bd I
  let e : S.US := ⟨a⁻¹, (S.US).inv_mem (frequency_generator_one_mem_US S a
    (frequencyAllowedGenerator_spec D S H Bd I))⟩
  exact ⟨⟨I, by
    intro v hv
    change FractionalIdeal.count F v (1 : Ideal (𝓞 F)) < 6
    rw [frequency_one_count]
    norm_num⟩, QuotientGroup.mk e⟩

private theorem frequencyIndex_absNorm_pos
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (u : FrequencyIndex S) :
    0 < Ideal.absNorm u.1.1.1 := frequency_ext_absNorm_pos S u.1.1

private theorem frequencyOne_absNorm
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    Ideal.absNorm (frequencyOne D S H Bd).1.1.1 = 1 := by
  simp [frequencyOne]

private noncomputable def frequencyRepr
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) : S.R := by
  let I : S.ExtIdeal := u.1.1
  let a : Fˣ := frequencyAllowedGenerator D S H Bd I
  let ε : S.US := frequencyUnitClassRepresentative S u.2
  have ha : (a : F) ∈ S.R :=
    frequency_generator_mem_Sintegers S I a
      (frequencyAllowedGenerator_spec D S H Bd I)
  have hε : ((ε : Fˣ) : F) ∈ S.R := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F ((ε : Fˣ) : F) ≤ 1
    intro v hv
    rw [ε.2 v hv]
  exact ⟨(a : F) * ((ε : Fˣ) : F), S.R.mul_mem ha hε⟩

private theorem frequencyRepr_absS
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    S.absS (S.diag (frequencyRepr D S H Bd u : F)) =
      Ideal.absNorm (u.1.1.1 : Ideal (𝓞 F)) := by
  let I : S.ExtIdeal := u.1.1
  let a : Fˣ := frequencyAllowedGenerator D S H Bd I
  let ε : S.US := frequencyUnitClassRepresentative S u.2
  have ha := frequencyAllowedGenerator_spec D S H Bd I
  calc
    S.absS (S.diag (frequencyRepr D S H Bd u : F)) =
        S.absS (S.diag ((a : F) * ((ε : Fˣ) : F))) := by rfl
    _ = S.absS (S.diag (a : F) * S.diag ((ε : Fˣ) : F)) := by rw [map_mul]
    _ = S.absS (S.diag (a : F)) * S.absS (S.diag ((ε : Fˣ) : F)) :=
      frequency_absS_mul S _ _
    _ = Ideal.absNorm I.1 := by
      rw [S.absS_diag_eq_norm_ofFieldData D (a : F) I.1 I.2 ha,
        show S.absS (S.diag ((ε : Fˣ) : F)) = 1 by
          simpa [ArtinPrimitiveRoots.A1.SData.diagU] using
            frequency_diagUS_norm_one D S ε]
      simp

private theorem frequencyRepr_ne_zero
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    (frequencyRepr D S H Bd u : F) ≠ 0 := by
  let I : S.ExtIdeal := u.1.1
  let a : Fˣ := frequencyAllowedGenerator D S H Bd I
  let ε : S.US := frequencyUnitClassRepresentative S u.2
  change (a : F) * ((ε : Fˣ) : F) ≠ 0
  exact mul_ne_zero (Units.ne_zero a) (Units.ne_zero (ε : Fˣ))

private noncomputable def frequencyKummer
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    ArtinPrimitiveRoots.A1.HeckeChar F :=
  Classical.choose (ArtinPrimitiveRoots.A1.kummer_exists D S
    (Units.mk0 (frequencyRepr D S H Bd u : F)
      (frequencyRepr_ne_zero D S H Bd u)))

private theorem frequencyKummer_spec
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    IsOfFinOrder (frequencyKummer D S H Bd u) ∧
      ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
        ArtinPrimitiveRoots.A1.residue v (frequencyRepr D S H Bd u : F) ≠ 0 →
          (frequencyKummer D S H Bd u).UnramifiedAt v ∧
            (frequencyKummer D S H Bd u).primeValue v =
              ArtinPrimitiveRoots.A1.chi D v (frequencyRepr D S H Bd u : F) :=
  Classical.choose_spec (ArtinPrimitiveRoots.A1.kummer_exists D S
    (Units.mk0 (frequencyRepr D S H Bd u : F)
      (frequencyRepr_ne_zero D S H Bd u)))

private noncomputable def frequencyOmega
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (u : FrequencyIndex S) :
    ArtinPrimitiveRoots.A1.HeckeChar F :=
  η * (frequencyKummer D S H Bd u)⁻¹

private theorem frequencyOmega_finiteOrder
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (u : FrequencyIndex S) : IsOfFinOrder (frequencyOmega S D H Bd η u) := by
  dsimp [frequencyOmega]
  exact hη.mul (IsOfFinOrder.inv (frequencyKummer_spec D S H Bd u).1)

/-- A1/Characters producer obligation for the complete corrected frequency dictionary
(02:285-387), including idelic induction, dyadic finiteness, and S-integer conductor bounds.
Corrected by `sol-gate-a2b`: finite order of `η` is required by the unit row. -/
theorem FrequencyData.nonempty
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η) :
    Nonempty (FrequencyData S D η) := by
  sorry

/-- The frozen A/B boundary width `δ₀ = 10⁻⁶`. -/
def a2Delta0 : ℝ := 1 / 10 ^ 6

end ArtinPrimitiveRoots.A2
