import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.conductor_sieve_assemble
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT
import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.Dictionary
import ArtinPrimitiveRoots.A1.Characters
import ArtinPrimitiveRoots.A1.Hilbert
import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Vendor.TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Section 6: conductor sieve, zero density, and the final A2 theorem
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open ClassFieldTheory
open scoped Classical nonZeroDivisors

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
  (05:407–433). -/
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

private theorem frequencyRepr_isGen
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    S.IsGen (frequencyRepr D S H Bd u : F) u.1.1.1 := by
  let a := frequencyAllowedGenerator D S H Bd u.1.1
  let ε := frequencyUnitClassRepresentative S u.2
  have ha := frequencyAllowedGenerator_spec D S H Bd u.1.1
  have hmul := ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit S ε a ha
  simpa [frequencyRepr, a, ε, mul_comm] using hmul

private def frequencyDenominatorIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {d | ∃ a : 𝓞 F, (d : F) * x = (a : F)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro d e ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    push_cast
    rw [add_mul, ha, hb]
  smul_mem' := by
    rintro c d ⟨a, ha⟩
    refine ⟨c * a, ?_⟩
    change ((c : F) * (d : F)) * x = (c : F) * (a : F)
    rw [mul_assoc, ha]

private theorem frequencyDenominatorIdeal_ne_bot (x : F) :
    frequencyDenominatorIdeal x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 F)) x
  have hden : ((b : 𝓞 F) : F) * x = (a : 𝓞 F) := by
    rw [← hab, IsFractionRing.mk'_eq_div]
    have hb : ((b : 𝓞 F) : F) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
    field_simp [hb]
  have hb : (b : 𝓞 F) ∈ frequencyDenominatorIdeal x := ⟨a, hden⟩
  intro h
  have : (b : 𝓞 F) ∈ (⊥ : Ideal (𝓞 F)) := h ▸ hb
  have hbzero : (b : 𝓞 F) = 0 := by simpa using this
  exact (mem_nonZeroDivisors_iff_ne_zero.mp b.property) hbzero

private theorem frequencyDenominatorIdeal_mem (x : F) (d : 𝓞 F) :
    d ∈ frequencyDenominatorIdeal x ↔ ∃ a : 𝓞 F, (d : F) * x = (a : F) := Iff.rfl

private theorem frequencyDenominatorIdeal_pow_principal (I : Ideal (𝓞 F))
    (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, Ideal.span {a} = I ^ Fintype.card (ClassGroup (𝓞 F)) := by
  let p : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  let n := Fintype.card (ClassGroup (𝓞 F))
  have hclass : ClassGroup.mk0 p ^ n = 1 := by
    simpa [n] using (pow_card_eq_one (x := ClassGroup.mk0 p))
  have hn0 : I ^ n ≠ ⊥ := pow_ne_zero _ hI
  have hclassPow : ClassGroup.mk0
      ⟨I ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr hn0⟩ = 1 := by
    change ClassGroup.mk0 (p ^ n) = 1
    rw [map_pow]
    exact hclass
  have hprincipal : (I ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hn0)).mp hclassPow
  obtain ⟨a, ha⟩ := hprincipal.principal
  exact ⟨a, ha.symm⟩

private theorem frequencyDenominatorIdeal_not_le (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x : S.R) (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    ¬ frequencyDenominatorIdeal (x : F) ≤ v.asIdeal := by
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) (x.property v hv)
  have hd : (d : 𝓞 F) ∈ frequencyDenominatorIdeal (x : F) := by
    rw [frequencyDenominatorIdeal_mem]
    refine ⟨n, ?_⟩
    change ((d : 𝓞 F) : F) * (x : F) = (n : 𝓞 F)
    rw [mul_comm]
    exact hnd
  intro hle
  exact d.property (hle hd)

private theorem frequencyDenominatorIdeal_pow_not_le
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (x : S.R)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    ¬ frequencyDenominatorIdeal (x : F) ^ Fintype.card (ClassGroup (𝓞 F)) ≤ v.asIdeal := by
  intro hle
  have hD : frequencyDenominatorIdeal (x : F) ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
  exact frequencyDenominatorIdeal_not_le S x v hv hD

private theorem frequency_sInteger_fraction (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (x : S.R) :
    ∃ a : 𝓞 F, ∃ d : ArtinPrimitiveRoots.Proofs.A1Generators.generatorDenominators S,
      (x : F) * ((d : 𝓞 F) : F) = (a : F) := by
  classical
  let D := frequencyDenominatorIdeal (x : F)
  have hD : D ≠ ⊥ := frequencyDenominatorIdeal_ne_bot (x : F)
  obtain ⟨a, ha⟩ := frequencyDenominatorIdeal_pow_principal D hD
  have hpow : Ideal.span {a} = D ^ Fintype.card (ClassGroup (𝓞 F)) := ha
  have hcard : Fintype.card (ClassGroup (𝓞 F)) ≠ 0 :=
    (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 F))).ne'
  have hpowle : D ^ Fintype.card (ClassGroup (𝓞 F)) ≤ D := Ideal.pow_le_self hcard
  have haDpow : a ∈ D ^ Fintype.card (ClassGroup (𝓞 F)) := by
    rw [← hpow]
    exact Ideal.subset_span (by simp)
  have haD : a ∈ D := hpowle haDpow
  obtain ⟨b, hbx⟩ := (frequencyDenominatorIdeal_mem (x : F) a).mp haD
  have ha0 : a ≠ 0 := by
    intro h
    have hpownz : D ^ Fintype.card (ClassGroup (𝓞 F)) ≠ ⊥ := pow_ne_zero _ hD
    have hbot : D ^ Fintype.card (ClassGroup (𝓞 F)) = (⊥ : Ideal (𝓞 F)) := by
      simpa [h] using hpow.symm
    exact hpownz hbot
  have hfinite (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      v.valuation F (a : F) = 1 := by
    have hnotle := frequencyDenominatorIdeal_pow_not_le S x v hv
    have hnotmem : a ∉ v.asIdeal := by
      intro hamem
      apply hnotle
      rw [← hpow]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hamem)
    exact v.valuation_eq_one_iff_notMem.mpr hnotmem
  refine ⟨b, ⟨a, ⟨ha0, hfinite⟩⟩, ?_⟩
  change (x : F) * ((a : 𝓞 F) : F) = (b : F)
  rw [mul_comm]
  exact hbx

private theorem frequency_sInteger_integral_sixth_multiple
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (x : S.R) :
    ∃ n : 𝓞 F, ∃ d : ArtinPrimitiveRoots.Proofs.A1Generators.generatorDenominators S,
      (n : F) = (x : F) * ((d : 𝓞 F) : F) ^ 6 := by
  obtain ⟨a, d, hxd⟩ := frequency_sInteger_fraction S x
  refine ⟨a * (d : 𝓞 F) ^ 5, d, ?_⟩
  calc
    ((a * (d : 𝓞 F) ^ 5 : 𝓞 F) : F) = (a : F) * ((d : 𝓞 F) : F) ^ 5 := by simp
    _ = ((x : F) * ((d : 𝓞 F) : F)) * ((d : 𝓞 F) : F) ^ 5 := by rw [hxd]
    _ = (x : F) * ((d : 𝓞 F) : F) ^ 6 := by ring

private def frequencyExteriorFactorSet
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    Set (ArtinPrimitiveRoots.A1.FinPlace F) :=
  {v | v ∉ S.Sf ∧ v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I}

private theorem frequencyExteriorFactorSet_finite
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    (frequencyExteriorFactorSet S I).Finite := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors I
  have hM : ({Q : Ideal (𝓞 F) | Q ∈ M} : Set (Ideal (𝓞 F))).Finite := by
    have hEq : (↑M.toFinset : Set (Ideal (𝓞 F))) = {Q | Q ∈ M} := by
      ext Q
      simp
    rw [← hEq]
    exact M.toFinset.finite_toSet
  apply Set.Finite.of_injOn (f := fun v : ArtinPrimitiveRoots.A1.FinPlace F => v.asIdeal)
    (s := frequencyExteriorFactorSet S I) (t := {Q : Ideal (𝓞 F) | Q ∈ M}) ?_ ?_ hM
  · intro v hv
    exact hv.2
  · intro v hv w hw h
    exact HeightOneSpectrum.ext h

private theorem frequency_count_idealProduct
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F)) (e : ArtinPrimitiveRoots.A1.FinPlace F → ℕ) :
    FractionalIdeal.count F v
        ((∏ w ∈ T, w.asIdeal ^ e w : Ideal (𝓞 F)) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
    ∑ w ∈ T, if v = w then (e w : ℤ) else 0 := by
  classical
  have hmap :
      ((∏ w ∈ T, w.asIdeal ^ e w : Ideal (𝓞 F)) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        ∏ w ∈ T, ((w.asIdeal : Ideal (𝓞 F)) :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ e w := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert w T hw ih =>
        simp only [Finset.prod_insert hw, FractionalIdeal.coeIdeal_mul,
          FractionalIdeal.coeIdeal_pow, ih]
  rw [hmap, FractionalIdeal.count_prod]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
    simp [eq_comm]
  · intro w hw
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

private def frequencyIdealFactorExponent (I : Ideal (𝓞 F))
    (v : ArtinPrimitiveRoots.A1.FinPlace F) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal

private noncomputable def frequencyRemainderFactors
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    Finset (ArtinPrimitiveRoots.A1.FinPlace F) :=
  (frequencyExteriorFactorSet_finite S I).toFinset.filter fun v =>
    frequencyIdealFactorExponent I v % 6 ≠ 0

private noncomputable def frequencyQuotientFactors
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    Finset (ArtinPrimitiveRoots.A1.FinPlace F) :=
  (frequencyExteriorFactorSet_finite S I).toFinset.filter fun v =>
    frequencyIdealFactorExponent I v / 6 ≠ 0

private noncomputable def frequencyRemainderIdeal
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ∏ v ∈ frequencyRemainderFactors S I,
    v.asIdeal ^ (frequencyIdealFactorExponent I v % 6)

private noncomputable def frequencyQuotientIdeal
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) : Ideal (𝓞 F) :=
  ∏ v ∈ frequencyQuotientFactors S I,
    v.asIdeal ^ (frequencyIdealFactorExponent I v / 6)

private theorem frequency_idealProduct_not_le
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (T : Finset (ArtinPrimitiveRoots.A1.FinPlace F))
    (e : ArtinPrimitiveRoots.A1.FinPlace F → ℕ)
    (hout : ∀ v ∈ T, v ∉ S.Sf) (hpos : ∀ v ∈ T, e v ≠ 0)
    (w : ArtinPrimitiveRoots.A1.FinPlace F) (hw : w ∈ S.Sf) :
    ¬ (∏ v ∈ T, v.asIdeal ^ e v) ≤ w.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      intro htop
      have htop' : (⊤ : Ideal (𝓞 F)) ≤ w.asIdeal := by
        simpa [Ideal.one_eq_top] using htop
      exact w.isPrime.ne_top (top_le_iff.mp htop')
  | @insert v T hvT ih =>
      have hvout := hout v (Finset.mem_insert_self v T)
      have hvpos := hpos v (Finset.mem_insert_self v T)
      have htailOut : ∀ z ∈ T, z ∉ S.Sf := fun z hz => hout z (Finset.mem_insert_of_mem hz)
      have htailPos : ∀ z ∈ T, e z ≠ 0 := fun z hz => hpos z (Finset.mem_insert_of_mem hz)
      intro hprod
      rw [Finset.prod_insert hvT] at hprod
      rcases w.isPrime.mul_le.mp hprod with hpow | htail
      · have hvle : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hpow
        have heq : v.asIdeal = w.asIdeal :=
          v.isMaximal.eq_of_le w.isPrime.ne_top hvle
        have hvw : v = w := HeightOneSpectrum.ext heq
        exact hvout (hvw ▸ hw)
      · exact ih htailOut htailPos htail

private theorem frequency_count_remainderIdeal
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F))
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    FractionalIdeal.count F v
        (frequencyRemainderIdeal S I :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      ((frequencyIdealFactorExponent I v % 6 : ℕ) : ℤ) := by
  classical
  rw [frequencyRemainderIdeal, frequency_count_idealProduct]
  by_cases hrem : frequencyIdealFactorExponent I v % 6 = 0
  · rw [hrem]
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hvw : v = w
    · subst w
      simp [hrem]
    · simp [hvw]
  · have hcount :
        0 < (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
      by_contra h
      have hzero : (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal = 0 :=
        Nat.eq_zero_of_not_pos h
      exact hrem (by simp [frequencyIdealFactorExponent, hzero])
    have hvfac : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
      Multiset.count_pos.mp hcount
    have hvset : v ∈ frequencyExteriorFactorSet S I := ⟨hv, hvfac⟩
    have hmem : v ∈ frequencyRemainderFactors S I := by
      refine Finset.mem_filter.mpr ⟨?_, hrem⟩
      exact (Set.Finite.mem_toFinset (frequencyExteriorFactorSet_finite S I)).mpr hvset
    rw [Finset.sum_eq_single v]
    · simp [hmem]
    · intro w hw hne
      have hvw : v ≠ w := fun h => hne h.symm
      simp [hvw]
    · intro hvnot
      exact (hvnot hmem).elim

private theorem frequency_count_quotientIdeal
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F))
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    FractionalIdeal.count F v
        (frequencyQuotientIdeal S I :
          FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      ((frequencyIdealFactorExponent I v / 6 : ℕ) : ℤ) := by
  classical
  rw [frequencyQuotientIdeal, frequency_count_idealProduct]
  by_cases hquot : frequencyIdealFactorExponent I v / 6 = 0
  · rw [hquot]
    apply Finset.sum_eq_zero
    intro w hw
    by_cases hvw : v = w
    · subst w
      simp [hquot]
    · simp [hvw]
  · have hcount :
      0 < (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
      have h6le : 6 ≤ frequencyIdealFactorExponent I v := by
        exact (Nat.div_ne_zero_iff.mp hquot).2
      exact lt_of_lt_of_le (by norm_num) h6le
    have hvfac : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
      Multiset.count_pos.mp hcount
    have hvset : v ∈ frequencyExteriorFactorSet S I := ⟨hv, hvfac⟩
    have hmem : v ∈ frequencyQuotientFactors S I := by
      refine Finset.mem_filter.mpr ⟨?_, hquot⟩
      exact (Set.Finite.mem_toFinset (frequencyExteriorFactorSet_finite S I)).mpr hvset
    rw [Finset.sum_eq_single v]
    · simp [hmem]
    · intro w hw hne
      have hvw : v ≠ w := fun h => hne h.symm
      simp [hvw]
    · intro hvnot
      exact (hvnot hmem).elim

private theorem frequency_remainderIdeal_exterior
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    S.IsExterior (frequencyRemainderIdeal S I) := by
  classical
  refine ⟨?_, ?_⟩
  · change (∏ v ∈ frequencyRemainderFactors S I,
      v.asIdeal ^ (frequencyIdealFactorExponent I v % 6)) ≠ ⊥
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ v.ne_bot
  · intro w hw hle
    have hout : ∀ v ∈ frequencyRemainderFactors S I, v ∉ S.Sf := by
      intro v hv
      have hmem := (Finset.mem_filter.mp hv).1
      exact ((Set.Finite.mem_toFinset (frequencyExteriorFactorSet_finite S I)).mp hmem).1
    have hpos : ∀ v ∈ frequencyRemainderFactors S I,
        frequencyIdealFactorExponent I v % 6 ≠ 0 := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    exact frequency_idealProduct_not_le S (frequencyRemainderFactors S I)
      (fun v => frequencyIdealFactorExponent I v % 6) hout hpos w hw hle

private theorem frequency_quotientIdeal_exterior
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F)) :
    S.IsExterior (frequencyQuotientIdeal S I) := by
  classical
  refine ⟨?_, ?_⟩
  · change (∏ v ∈ frequencyQuotientFactors S I,
      v.asIdeal ^ (frequencyIdealFactorExponent I v / 6)) ≠ ⊥
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact pow_ne_zero _ v.ne_bot
  · intro w hw hle
    have hout : ∀ v ∈ frequencyQuotientFactors S I, v ∉ S.Sf := by
      intro v hv
      have hmem := (Finset.mem_filter.mp hv).1
      exact ((Set.Finite.mem_toFinset (frequencyExteriorFactorSet_finite S I)).mp hmem).1
    have hpos : ∀ v ∈ frequencyQuotientFactors S I,
        frequencyIdealFactorExponent I v / 6 ≠ 0 := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    exact frequency_idealProduct_not_le S (frequencyQuotientFactors S I)
      (fun v => frequencyIdealFactorExponent I v / 6) hout hpos w hw hle

private theorem frequency_isExterior_mul
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I J : Ideal (𝓞 F))
    (hI : S.IsExterior I) (hJ : S.IsExterior J) : S.IsExterior (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  intro v hv hle
  rcases v.isPrime.mul_le.mp hle with hIle | hJle
  · exact hI.2 v hv hIle
  · exact hJ.2 v hv hJle

private theorem frequency_isExterior_pow
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (n : ℕ) : S.IsExterior (I ^ n) := by
  refine ⟨pow_ne_zero _ hI.1, ?_⟩
  intro v hv hle
  exact hI.2 v hv (v.isPrime.le_of_pow_le hle)

private theorem frequency_isGen_mul
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {I J : Ideal (𝓞 F)} {a b : Fˣ}
    (ha : S.IsGen (a : F) I) (hb : S.IsGen (b : F) J) :
    S.IsGen ((a * b : Fˣ) : F) (I * J) := by
  refine ⟨frequency_isExterior_mul S I J ha.1 hb.1,
    mul_ne_zero ha.2.1 hb.2.1, ?_⟩
  intro v hv
  have hI : (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr ha.1.1
  have hJ : (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb.1.1
  have ha' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha.2.1
  have hb' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb.2.1
  calc
    _ = FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) +
          FractionalIdeal.count F v
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (b : F)) := by
      rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
      exact FractionalIdeal.count_mul F v ha' hb'
    _ = FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
          FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [ha.2.2 v hv, hb.2.2 v hv]
    _ = FractionalIdeal.count F v
          ((I * J : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.coeIdeal_mul]
      exact (FractionalIdeal.count_mul F v hI hJ).symm

private theorem frequency_isGen_pow
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    {I : Ideal (𝓞 F)} {a : Fˣ} (n : ℕ)
    (ha : S.IsGen (a : F) I) :
    S.IsGen ((a ^ n : Fˣ) : F) (I ^ n) := by
  refine ⟨frequency_isExterior_pow S I ha.1 n,
    pow_ne_zero _ ha.2.1, ?_⟩
  intro v hv
  calc
    _ = n * FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) := by
      rw [Units.val_pow_eq_pow_val, ← FractionalIdeal.spanSingleton_pow,
        FractionalIdeal.count_pow]
    _ = n * FractionalIdeal.count F v
          (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by rw [ha.2.2 v hv]
    _ = FractionalIdeal.count F v
          ((I ^ n : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]

private theorem frequency_sUnit_of_sameGen
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : Ideal (𝓞 F))
    (x y : F) (hx : x ≠ 0) (hy : y ≠ 0)
    (hX : S.IsGen x I) (hY : S.IsGen y I) :
    ∃ ε : S.US, ((ε : Fˣ) : F) = x / y := by
  classical
  let e : Fˣ := Units.mk0 (x / y) (div_ne_zero hx hy)
  have he : e ∈ S.US := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F (x / y) = 1
    intro v hv
    have hcount : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) = 0 := by
      rw [frequency_count_spanSingleton_div v x y hx hy, hX.2.2 v hv, hY.2.2 v hv]
      ring
    have hprincipal : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x / y)) =
          -WithZero.log (v.valuation F (x / y)) :=
      frequency_count_spanSingleton_eq_neg_log_valuation v _ (div_ne_zero hx hy)
    have hlog : WithZero.log (v.valuation F (x / y)) = 0 := by
      rw [hprincipal] at hcount
      linarith
    have hvne : v.valuation F (x / y) ≠ 0 := by
      apply (Valuation.ne_zero_iff _).2
      exact div_ne_zero hx hy
    calc
      v.valuation F (x / y) = WithZero.exp (WithZero.log (v.valuation F (x / y))) :=
        (WithZero.exp_log hvne).symm
      _ = WithZero.exp 0 := by rw [hlog]
      _ = 1 := WithZero.exp_zero
  refine ⟨⟨e, he⟩, ?_⟩
  rfl

private theorem frequency_count_spanSingleton_mul
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (x y : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x * y)) =
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) +
      FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) y) := by
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul F v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

private theorem frequency_count_spanSingleton_pow
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (x : F) (n : ℕ) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x ^ n)) =
      n * FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) := by
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

private theorem frequency_count_spanSingleton_sUnit_zero
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (ε : S.US)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((ε : Fˣ) : F)) = 0 := by
  rw [frequency_count_spanSingleton_eq_neg_log_valuation v _ (Units.ne_zero (ε : Fˣ)),
    ε.property v hv]
  simp

private theorem frequency_decomposition_count
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (J : S.ExtIdeal) (ε : S.US) (a : Fˣ)
    (hgen : S.IsGen (a : F) J.1) (x : S.R)
    (heq : (x : F) =
      (frequencyRepr D S H Bd u : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) =
      FractionalIdeal.count F v
          (u.1.1.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        6 * FractionalIdeal.count F v
          (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  have hreprCount := (frequencyRepr_isGen D S H Bd u).2.2 v hv
  have hεCount := frequency_count_spanSingleton_sUnit_zero S ε v hv
  have hrepr0 := frequencyRepr_ne_zero D S H Bd u
  have hε0 : ((ε : Fˣ) : F) ≠ 0 := Units.ne_zero (ε : Fˣ)
  have ha0 : (a : F) ≠ 0 := Units.ne_zero a
  have hleft0 : (frequencyRepr D S H Bd u : F) * ((ε : Fˣ) : F) ^ 6 ≠ 0 :=
    mul_ne_zero hrepr0 (pow_ne_zero 6 hε0)
  have hright0 : (a : F) ^ 6 ≠ 0 := pow_ne_zero 6 ha0
  calc
    _ = FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          ((frequencyRepr D S H Bd u : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6)) := by
        rw [heq]
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            ((frequencyRepr D S H Bd u : F) * ((ε : Fˣ) : F) ^ 6)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a : F) ^ 6)) :=
      frequency_count_spanSingleton_mul v _ _ hleft0 hright0
    _ = FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (frequencyRepr D S H Bd u : F)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (((ε : Fˣ) : F) ^ 6)) +
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((a : F) ^ 6)) := by
      rw [frequency_count_spanSingleton_mul v _ _ hrepr0 (pow_ne_zero 6 hε0)]
    _ = _ := by
      rw [frequency_count_spanSingleton_pow v ((ε : Fˣ) : F) 6,
        frequency_count_spanSingleton_pow v (a : F) 6, hεCount, hreprCount, hgen.2.2 v hv]
      ring

private theorem frequency_sInteger_exterior_decomposition
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (x : S.R) (hx : (x : F) ≠ 0) :
    ∃ I J : S.ExtIdeal,
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
        0 ≤ FractionalIdeal.count F v
          (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧
        FractionalIdeal.count F v
          (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) < 6) ∧
      S.IsGen (x : F) (I.1 * J.1 ^ 6) := by
  classical
  obtain ⟨a, d, hxd⟩ := frequency_sInteger_fraction S x
  have hdO : (d : 𝓞 F) ≠ 0 := d.property.1
  have hdF : ((d : 𝓞 F) : F) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne hdO
  have haF : (a : F) ≠ 0 := by
    rw [← hxd]
    exact mul_ne_zero hx hdF
  have haO : a ≠ 0 := by
    intro ha
    exact haF (by simp [ha])
  let A : Ideal (𝓞 F) := Ideal.span {a}
  have hA : A ≠ ⊥ := by
    simpa [A, Ideal.span_singleton_eq_bot, Ideal.zero_eq_bot] using haO
  let I₀ := frequencyRemainderIdeal S A
  let J₀ := frequencyQuotientIdeal S A
  have hI₀ : S.IsExterior I₀ := frequency_remainderIdeal_exterior S A
  have hJ₀ : S.IsExterior J₀ := frequency_quotientIdeal_exterior S A
  have hJ₀pow : S.IsExterior (J₀ ^ 6) := frequency_isExterior_pow S J₀ hJ₀ 6
  have hIJ : S.IsExterior (I₀ * J₀ ^ 6) :=
    frequency_isExterior_mul S I₀ (J₀ ^ 6) hI₀ hJ₀pow
  have hdiv : (x : F) = (a : F) / ((d : 𝓞 F) : F) := by
    calc
      (x : F) = (x : F) * ((d : 𝓞 F) : F) / ((d : 𝓞 F) : F) := by
        field_simp [hdF]
      _ = (a : F) / ((d : 𝓞 F) : F) := by rw [hxd]
  have hcountA (v : ArtinPrimitiveRoots.A1.FinPlace F) :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) =
        (frequencyIdealFactorExponent A v : ℤ) := by
    calc
      _ = FractionalIdeal.count F v (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        rw [← FractionalIdeal.coeIdeal_span_singleton]
      _ = (UniqueFactorizationMonoid.normalizedFactors A).count v.asIdeal := by
        rw [FractionalIdeal.count_coe F v hA,
          Ideal.count_associates_factors_eq hA v.isPrime v.ne_bot]
      _ = _ := rfl
  have hcountD (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((d : 𝓞 F) : F)) = 0 := by
    rw [frequency_count_spanSingleton_eq_neg_log_valuation v _ hdF]
    rw [d.property.2 v hv]
    simp
  have hcountX (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) =
        (frequencyIdealFactorExponent A v : ℤ) := by
    rw [hdiv, frequency_count_spanSingleton_div v (a : F) ((d : 𝓞 F) : F) haF hdF,
      hcountA, hcountD v hv, sub_zero]
  have hcountProd (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
      FractionalIdeal.count F v
          ((I₀ * J₀ ^ 6 : Ideal (𝓞 F)) :
            FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        (frequencyIdealFactorExponent A v : ℤ) := by
    have hIfrac : (I₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hI₀.1
    have hJbase : (J₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr hJ₀.1
    have hJfrac : ((J₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ 6) ≠ 0 :=
      pow_ne_zero 6 hJbase
    calc
      _ = FractionalIdeal.count F v
          ((I₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
            (J₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ 6) := by
              rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
      _ = FractionalIdeal.count F v (I₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
            FractionalIdeal.count F v
              ((J₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ 6) :=
          FractionalIdeal.count_mul F v hIfrac hJfrac
      _ = _ := by
        rw [FractionalIdeal.count_pow, frequency_count_remainderIdeal S A v hv,
          frequency_count_quotientIdeal S A v hv]
        exact_mod_cast (Nat.mod_add_div (frequencyIdealFactorExponent A v) 6)
  let I : S.ExtIdeal := ⟨I₀, hI₀⟩
  let J : S.ExtIdeal := ⟨J₀, hJ₀⟩
  refine ⟨I, J, ?_, ?_⟩
  · intro v hv
    constructor
    · exact FractionalIdeal.count_coe_nonneg F v I₀
    · rw [frequency_count_remainderIdeal S A v hv]
      exact_mod_cast Nat.mod_lt (frequencyIdealFactorExponent A v) (by norm_num)
  · refine ⟨hIJ, hx, ?_⟩
    intro v hv
    rw [hcountX v hv, hcountProd v hv]

private theorem frequency_count_coeIdeal_eq_factorCount
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    FractionalIdeal.count F v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
  rw [FractionalIdeal.count_coe F v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]

private theorem frequency_count_extIdeal_zero_of_memS
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I : S.ExtIdeal)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∈ S.Sf) :
    FractionalIdeal.count F v
        (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
  have hnot : v.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors I.1 := by
    intro hfactor
    have hdiv : v.asIdeal ∣ I.1 :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
    exact I.2.2 v hv (Ideal.dvd_iff_le.mp hdiv)
  rw [frequency_count_coeIdeal_eq_factorCount I.1 I.2.1 v]
  exact_mod_cast (Multiset.count_eq_zero.mpr hnot)

private theorem frequency_decomposition_local_exponents_eq
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u₁ u₂ : FrequencyIndex S) (J₁ J₂ : S.ExtIdeal)
    (ε₁ ε₂ : S.US) (a₁ a₂ : Fˣ)
    (hgen₁ : S.IsGen (a₁ : F) J₁.1) (hgen₂ : S.IsGen (a₂ : F) J₂.1)
    (x : S.R)
    (heq₁ : (x : F) = (frequencyRepr D S H Bd u₁ : F) *
      ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6)
    (heq₂ : (x : F) = (frequencyRepr D S H Bd u₂ : F) *
      ((ε₂ : Fˣ) : F) ^ 6 * (a₂ : F) ^ 6)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    (UniqueFactorizationMonoid.normalizedFactors u₁.1.1.1).count v.asIdeal =
        (UniqueFactorizationMonoid.normalizedFactors u₂.1.1.1).count v.asIdeal ∧
      (UniqueFactorizationMonoid.normalizedFactors J₁.1).count v.asIdeal =
      (UniqueFactorizationMonoid.normalizedFactors J₂.1).count v.asIdeal := by
  let I₁ : S.ExtIdeal := u₁.1.1
  let I₂ : S.ExtIdeal := u₂.1.1
  have hcount₁ := frequency_decomposition_count D S H Bd u₁ J₁ ε₁ a₁ hgen₁ x heq₁ v hv
  have hcount₂ := frequency_decomposition_count D S H Bd u₂ J₂ ε₂ a₂ hgen₂ x heq₂ v hv
  have hsum :
      FractionalIdeal.count F v
          (u₁.1.1.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        6 * FractionalIdeal.count F v (J₁.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      FractionalIdeal.count F v
          (u₂.1.1.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) +
        6 * FractionalIdeal.count F v (J₂.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
    hcount₁.symm.trans hcount₂
  have hsumNat :
      ((UniqueFactorizationMonoid.normalizedFactors u₁.1.1.1).count v.asIdeal : ℤ) +
        6 * ((UniqueFactorizationMonoid.normalizedFactors J₁.1).count v.asIdeal : ℤ) =
      ((UniqueFactorizationMonoid.normalizedFactors u₂.1.1.1).count v.asIdeal : ℤ) +
        6 * ((UniqueFactorizationMonoid.normalizedFactors J₂.1).count v.asIdeal : ℤ) := by
    rw [frequency_count_coeIdeal_eq_factorCount I₁.1 I₁.2.1 v,
      frequency_count_coeIdeal_eq_factorCount J₁.1 J₁.2.1 v,
      frequency_count_coeIdeal_eq_factorCount I₂.1 I₂.2.1 v,
      frequency_count_coeIdeal_eq_factorCount J₂.1 J₂.2.1 v] at hsum
    exact hsum
  have hI₁lt :
      ((UniqueFactorizationMonoid.normalizedFactors u₁.1.1.1).count v.asIdeal : ℤ) < 6 := by
    have h := u₁.1.2 v hv
    rw [frequency_count_coeIdeal_eq_factorCount u₁.1.1.1 u₁.1.1.2.1 v] at h
    exact h
  have hI₂lt :
      ((UniqueFactorizationMonoid.normalizedFactors u₂.1.1.1).count v.asIdeal : ℤ) < 6 := by
    have h := u₂.1.2 v hv
    rw [frequency_count_coeIdeal_eq_factorCount u₂.1.1.1 u₂.1.1.2.1 v] at h
    exact h
  constructor <;> omega

private theorem frequency_ideal_eq_of_count_eq
    (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hcount : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :
    I = J := by
  have hmax (v : ArtinPrimitiveRoots.A1.FinPlace F) : v.maxPowDividing I = v.maxPowDividing J := by
    have hcountNat :
        (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal =
          (UniqueFactorizationMonoid.normalizedFactors J).count v.asIdeal := by
      have hcountZ :=
        (frequency_count_coeIdeal_eq_factorCount I hI v).symm.trans
          ((hcount v).trans (frequency_count_coeIdeal_eq_factorCount J hJ v))
      exact_mod_cast hcountZ
    change v.asIdeal ^
        (Associates.mk v.asIdeal).count (Associates.mk I).factors =
      v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk J).factors
    have hcountI :
        (Associates.mk v.asIdeal).count (Associates.mk I).factors =
          (UniqueFactorizationMonoid.normalizedFactors I).count v.asIdeal := by
      rw [Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
    have hcountJ :
        (Associates.mk v.asIdeal).count (Associates.mk J).factors =
          (UniqueFactorizationMonoid.normalizedFactors J).count v.asIdeal := by
      rw [Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot]
    rw [hcountI, hcountJ, hcountNat]
  calc
    I = ⨅ v : ArtinPrimitiveRoots.A1.FinPlace F, v.maxPowDividing I :=
      (Ideal.iInf_maxPowDividing_eq hI).symm
    _ = ⨅ v : ArtinPrimitiveRoots.A1.FinPlace F, v.maxPowDividing J := by
      congr 1
      funext v
      exact hmax v
    _ = J := Ideal.iInf_maxPowDividing_eq hJ

private theorem frequency_extIdeal_eq_of_localCounts
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) (I J : S.ExtIdeal)
    (hcount : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :
    I = J := by
  have hcountAll : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      FractionalIdeal.count F v (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v
    by_cases hv : v ∈ S.Sf
    · rw [frequency_count_extIdeal_zero_of_memS S I v hv,
        frequency_count_extIdeal_zero_of_memS S J v hv]
    · exact hcount v hv
  have hraw := frequency_ideal_eq_of_count_eq I.1 J.1 I.2.1 J.2.1 hcountAll
  exact Subtype.ext hraw

private theorem frequency_decomposition_unique_index
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (ui₁ ui₂ : FrequencyIndex S × S.ExtIdeal)
    (ε₁ ε₂ : S.US) (a₁ a₂ : Fˣ)
    (hgen₁ : S.IsGen (a₁ : F) ui₁.2.1)
    (hgen₂ : S.IsGen (a₂ : F) ui₂.2.1)
    (x : S.R)
    (heq₁ : (x : F) = (frequencyRepr D S H Bd ui₁.1 : F) *
      ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6)
    (heq₂ : (x : F) = (frequencyRepr D S H Bd ui₂.1 : F) *
      ((ε₂ : Fˣ) : F) ^ 6 * (a₂ : F) ^ 6) :
    ui₁ = ui₂ := by
  classical
  let U₁ : FrequencyIndex S := ui₁.1
  let U₂ : FrequencyIndex S := ui₂.1
  let I₁ : S.ExtIdeal := U₁.1.1
  let I₂ : S.ExtIdeal := U₂.1.1
  let J₁ : S.ExtIdeal := ui₁.2
  let J₂ : S.ExtIdeal := ui₂.2
  have hlocal (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :=
    frequency_decomposition_local_exponents_eq D S H Bd U₁ U₂ J₁ J₂ ε₁ ε₂ a₁ a₂
      hgen₁ hgen₂ x (by simpa [U₁, J₁] using heq₁) (by simpa [U₂, J₂] using heq₂) v hv
  have hIcount : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      FractionalIdeal.count F v (I₁.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (I₂.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v hv
    have hn := (hlocal v hv).1
    calc
      FractionalIdeal.count F v (I₁.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          (UniqueFactorizationMonoid.normalizedFactors I₁.1).count v.asIdeal :=
        frequency_count_coeIdeal_eq_factorCount I₁.1 I₁.2.1 v
      _ = (UniqueFactorizationMonoid.normalizedFactors I₂.1).count v.asIdeal := by exact_mod_cast hn
      _ = FractionalIdeal.count F v (I₂.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        (frequency_count_coeIdeal_eq_factorCount I₂.1 I₂.2.1 v).symm
  have hJcount : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      FractionalIdeal.count F v (J₁.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
        FractionalIdeal.count F v (J₂.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v hv
    have hn := (hlocal v hv).2
    calc
      FractionalIdeal.count F v (J₁.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          (UniqueFactorizationMonoid.normalizedFactors J₁.1).count v.asIdeal :=
        frequency_count_coeIdeal_eq_factorCount J₁.1 J₁.2.1 v
      _ = (UniqueFactorizationMonoid.normalizedFactors J₂.1).count v.asIdeal := by exact_mod_cast hn
      _ = FractionalIdeal.count F v (J₂.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
        (frequency_count_coeIdeal_eq_factorCount J₂.1 J₂.2.1 v).symm
  have hIeq : I₁ = I₂ := frequency_extIdeal_eq_of_localCounts S I₁ I₂ hIcount
  have hJeq : J₁ = J₂ := frequency_extIdeal_eq_of_localCounts S J₁ J₂ hJcount
  have hIideal : I₁.1 = I₂.1 := congrArg Subtype.val hIeq
  have hJideal : J₁.1 = J₂.1 := congrArg Subtype.val hJeq
  let g₁ : Fˣ := frequencyAllowedGenerator D S H Bd I₁
  let g₂ : Fˣ := frequencyAllowedGenerator D S H Bd I₂
  have hg : g₁ = g₂ := congrArg (frequencyAllowedGenerator D S H Bd) hIeq
  let e₁ : S.US := frequencyUnitClassRepresentative S U₁.2
  let e₂ : S.US := frequencyUnitClassRepresentative S U₂.2
  have hrepr₁ : (frequencyRepr D S H Bd U₁ : F) = ((g₁ * (e₁ : Fˣ) : Fˣ) : F) := rfl
  have hrepr₂ : (frequencyRepr D S H Bd U₂ : F) = ((g₂ * (e₂ : Fˣ) : Fˣ) : F) := rfl
  have hgen₂' : S.IsGen (a₂ : F) J₁.1 := by
    rw [hJideal]
    exact hgen₂
  obtain ⟨θ, hθ⟩ := frequency_sUnit_of_sameGen S J₁.1
    (a₂ : F) (a₁ : F) (Units.ne_zero a₂) (Units.ne_zero a₁) hgen₂' hgen₁
  let ζ : S.US := (ε₂ / ε₁) * θ
  have hζ : ((ζ : Fˣ) : F) =
      (((ε₂ : Fˣ) : F) / ((ε₁ : Fˣ) : F)) * ((a₂ : F) / (a₁ : F)) := by
    dsimp [ζ]
    rw [hθ]
    simp [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hEq : (frequencyRepr D S H Bd U₁ : F) * ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6 =
      (frequencyRepr D S H Bd U₂ : F) * ((ε₂ : Fˣ) : F) ^ 6 * (a₂ : F) ^ 6 :=
    heq₁.symm.trans heq₂
  have hEq' : ((e₁ : Fˣ) : F) * ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6 =
      ((e₂ : Fˣ) : F) * ((ε₂ : Fˣ) : F) ^ 6 * (a₂ : F) ^ 6 := by
    rw [hrepr₁, hrepr₂, hg] at hEq
    simp only [Units.val_mul, Subgroup.coe_mul] at hEq
    field_simp [Units.ne_zero g₁] at hEq
    exact hEq
  have hratio : ((e₁ : Fˣ) : F) / ((e₂ : Fˣ) : F) = ((ζ : Fˣ) : F) ^ 6 := by
    calc
      _ = (((e₁ : Fˣ) : F) * ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6) /
          (((e₂ : Fˣ) : F) * ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6) := by
            field_simp [Units.ne_zero (e₂ : Fˣ), Units.ne_zero (ε₁ : Fˣ), Units.ne_zero a₁]
      _ = (((e₂ : Fˣ) : F) * ((ε₂ : Fˣ) : F) ^ 6 * (a₂ : F) ^ 6) /
          (((e₂ : Fˣ) : F) * ((ε₁ : Fˣ) : F) ^ 6 * (a₁ : F) ^ 6) := by rw [hEq']
      _ = (((ε₂ : Fˣ) : F) / ((ε₁ : Fˣ) : F)) ^ 6 *
          ((a₂ : F) / (a₁ : F)) ^ 6 := by
          field_simp [Units.ne_zero (e₂ : Fˣ), Units.ne_zero (ε₁ : Fˣ),
              Units.ne_zero (ε₂ : Fˣ), Units.ne_zero a₁, Units.ne_zero a₂]
      _ = ((ζ : Fˣ) : F) ^ 6 := by rw [← mul_pow, hζ]
  have hratioUS : e₁ / e₂ = ζ ^ 6 := by
    apply Subtype.ext
    apply Units.ext
    simpa only [Subgroup.coe_div, Subgroup.coe_pow,
      Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] using hratio
  have hmem : e₁ / e₂ ∈ ArtinPrimitiveRoots.A2.Gamma S := by
    change e₁ / e₂ ∈ (ArtinPrimitiveRoots.A2.sixthPowerOnUS S).range
    exact ⟨ζ, by simpa [ArtinPrimitiveRoots.A2.sixthPowerOnUS] using hratioUS.symm⟩
  have hmk : QuotientGroup.mk e₁ = QuotientGroup.mk e₂ :=
    (QuotientGroup.eq_iff_div_mem (N := ArtinPrimitiveRoots.A2.Gamma S)).2 hmem
  have hclass : U₁.2 = U₂.2 := by
    have he₁ := frequency_unitClassRepresentative_spec S U₁.2
    have he₂ := frequency_unitClassRepresentative_spec S U₂.2
    calc
      U₁.2 = QuotientGroup.mk e₁ := he₁.symm
      _ = QuotientGroup.mk e₂ := hmk
      _ = U₂.2 := he₂
  have hindex : U₁ = U₂ := by
    apply Prod.ext
    · exact Subtype.ext hIeq
    · exact hclass
  exact Prod.ext hindex hJeq

private theorem frequency_index_dyadic_count
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      {u : FrequencyIndex S | X ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧
        (Ideal.absNorm u.1.1.1 : ℝ) < 2 * X}.Finite ∧
      ({u : FrequencyIndex S | X ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧
        (Ideal.absNorm u.1.1.1 : ℝ) < 2 * X}.ncard : ℝ) ≤ C * X := by
  classical
  letI : Finite (ArtinPrimitiveRoots.A2.UnitSix S) := frequency_unitSix_finite D S
  letI : Fintype (ArtinPrimitiveRoots.A2.UnitSix S) := Fintype.ofFinite _
  obtain ⟨C₀, hC₀, hcount⟩ := ArtinPrimitiveRoots.A2.a2_bridge_COUNT S
  let Cunit : ℝ := Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S)
  have hCunit : 0 < Cunit := by
    dsimp [Cunit]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S))
  let C : ℝ := 2 * C₀ * Cunit
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro X hX
  let shell : Set (FrequencyIndex S) :=
    {u | X ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧ (Ideal.absNorm u.1.1.1 : ℝ) < 2 * X}
  let shellI : Set S.ExtIdeal :=
    {I | X ≤ ArtinPrimitiveRoots.A2.idealNorm I.1 ∧ ArtinPrimitiveRoots.A2.idealNorm I.1 < 2 * X}
  let upperI : Set S.ExtIdeal :=
    {I | ArtinPrimitiveRoots.A2.idealNorm I.1 ≤ 2 * X}
  have hupper : upperI.Finite :=
    (ArtinPrimitiveRoots.A2.a2_bridge_COUNT_finite S (2 * X) (by positivity)).1
  have hshellI : shellI.Finite := hupper.subset (by
    intro I hI
    exact hI.2.le)
  let target : Set (S.ExtIdeal × ArtinPrimitiveRoots.A2.UnitSix S) :=
    shellI ×ˢ (Set.univ : Set (ArtinPrimitiveRoots.A2.UnitSix S))
  have htarget : target.Finite := hshellI.prod Set.finite_univ
  let f : FrequencyIndex S → S.ExtIdeal × ArtinPrimitiveRoots.A2.UnitSix S :=
    fun u => (u.1.1, u.2)
  have hf : Set.MapsTo f shell target := by
    intro u hu
    refine ⟨?_, Set.mem_univ _⟩
    exact ⟨hu.1, hu.2⟩
  have hinj : Function.Injective f := by
    intro u v huv
    rcases u with ⟨uI, uε⟩
    rcases v with ⟨vI, vε⟩
    simp only [f, Prod.mk.injEq] at huv
    apply Prod.ext
    · apply Subtype.ext
      exact huv.1
    · exact huv.2
  have hfinite : shell.Finite := Set.Finite.of_injOn hf hinj.injOn htarget
  have hcard : shell.ncard ≤ target.ncard :=
    Set.ncard_le_ncard_of_injOn f hf hinj.injOn htarget
  have hshellCount : (shellI.ncard : ℝ) ≤ C₀ * (2 * X) := by
    have hsub : shellI ⊆ upperI := by
      intro I hI
      exact hI.2.le
    have hncard : shellI.ncard ≤ upperI.ncard := Set.ncard_le_ncard hsub hupper
    have hb := hcount (2 * X) (by linarith)
    dsimp [upperI, ArtinPrimitiveRoots.A2.idealNorm] at hb ⊢
    exact (Nat.cast_le.mpr hncard).trans hb
  have htargetCard : target.ncard = shellI.ncard * Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S) := by
    simp [target, Set.ncard_prod, Set.ncard_univ]
  refine ⟨hfinite, ?_⟩
  dsimp [shell, C, Cunit] at hcard ⊢
  calc
    (shell.ncard : ℝ) ≤ target.ncard := by exact_mod_cast hcard
    _ = (shellI.ncard : ℝ) * Cunit := by
      rw [htargetCard, Nat.cast_mul]
    _ ≤ (C₀ * (2 * X)) * Cunit := by
      exact mul_le_mul_of_nonneg_right hshellCount (le_of_lt hCunit)
    _ = C * X := by dsimp [C, Cunit]; ring

private theorem frequency_index_low_shell_bound
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ∃ C : ℝ, 0 < C ∧
      {u : FrequencyIndex S | 1 ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧
        (Ideal.absNorm u.1.1.1 : ℝ) < 4}.Finite ∧
      ({u : FrequencyIndex S | 1 ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧
        (Ideal.absNorm u.1.1.1 : ℝ) < 4}.ncard : ℝ) ≤ C := by
  classical
  letI : Finite (ArtinPrimitiveRoots.A2.UnitSix S) := frequency_unitSix_finite D S
  letI : Fintype (ArtinPrimitiveRoots.A2.UnitSix S) := Fintype.ofFinite _
  obtain ⟨C₀, hC₀, hcount⟩ := ArtinPrimitiveRoots.A2.a2_bridge_COUNT S
  let Cunit : ℝ := Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S)
  have hCunit : 0 < Cunit := by
    dsimp [Cunit]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S))
  let C : ℝ := 4 * C₀ * Cunit
  let low : Set (FrequencyIndex S) :=
    {u | 1 ≤ (Ideal.absNorm u.1.1.1 : ℝ) ∧ (Ideal.absNorm u.1.1.1 : ℝ) < 4}
  let upperI : Set S.ExtIdeal := {I | ArtinPrimitiveRoots.A2.idealNorm I.1 ≤ 4}
  have hupper : upperI.Finite :=
    (ArtinPrimitiveRoots.A2.a2_bridge_COUNT_finite S 4 (by norm_num)).1
  let target : Set (S.ExtIdeal × ArtinPrimitiveRoots.A2.UnitSix S) :=
    upperI ×ˢ (Set.univ : Set (ArtinPrimitiveRoots.A2.UnitSix S))
  have htarget : target.Finite := hupper.prod Set.finite_univ
  let f : FrequencyIndex S → S.ExtIdeal × ArtinPrimitiveRoots.A2.UnitSix S :=
    fun u => (u.1.1, u.2)
  have hf : Set.MapsTo f low target := by
    intro u hu
    refine ⟨?_, Set.mem_univ _⟩
    change (Ideal.absNorm u.1.1.1 : ℝ) ≤ 4
    exact le_of_lt hu.2
  have hinj : Function.Injective f := by
    intro u v huv
    rcases u with ⟨uI, uε⟩
    rcases v with ⟨vI, vε⟩
    simp only [f, Prod.mk.injEq] at huv
    apply Prod.ext
    · apply Subtype.ext
      exact huv.1
    · exact huv.2
  have hfinite : low.Finite := Set.Finite.of_injOn hf hinj.injOn htarget
  have hcard : low.ncard ≤ target.ncard :=
    Set.ncard_le_ncard_of_injOn f hf hinj.injOn htarget
  have hupperCount : (upperI.ncard : ℝ) ≤ C₀ * 4 := by
    have h := hcount 4 (by norm_num)
    dsimp [upperI, ArtinPrimitiveRoots.A2.idealNorm] at h ⊢
    exact h
  have htargetCard : target.ncard = upperI.ncard * Fintype.card (ArtinPrimitiveRoots.A2.UnitSix S) := by
    simp [target, Set.ncard_prod, Set.ncard_univ]
  refine ⟨C, by dsimp [C]; positivity, hfinite, ?_⟩
  dsimp [C, Cunit] at hcard ⊢
  calc
    (low.ncard : ℝ) ≤ target.ncard := by exact_mod_cast hcard
    _ = (upperI.ncard : ℝ) * Cunit := by
      rw [htargetCard, Nat.cast_mul]
    _ ≤ (C₀ * 4) * Cunit :=
      mul_le_mul_of_nonneg_right hupperCount (le_of_lt hCunit)
    _ = C := by dsimp [C, Cunit]; ring

private theorem frequency_index_eq_of_sixth_ratio
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u v : FrequencyIndex S) (z : Fˣ)
    (hratio : (frequencyRepr D S H Bd u : F) /
        (frequencyRepr D S H Bd v : F) = (z : F) ^ 6) :
    u = v := by
  classical
  have hcountZ (w : ArtinPrimitiveRoots.A1.FinPlace F) (hw : w ∉ S.Sf) :
      FractionalIdeal.count F w
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (z : F)) = 0 := by
    have hcount :
        FractionalIdeal.count F w
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
              ((frequencyRepr D S H Bd u : F) /
                (frequencyRepr D S H Bd v : F))) =
          FractionalIdeal.count F w
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((z : F) ^ 6)) := by
      exact congrArg (fun x : F => FractionalIdeal.count F w
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x)) hratio
    rw [frequency_count_spanSingleton_div w _ _
          (frequencyRepr_ne_zero D S H Bd u)
          (frequencyRepr_ne_zero D S H Bd v),
        frequency_count_spanSingleton_pow w (z : F) 6] at hcount
    have hu := (frequencyRepr_isGen D S H Bd u).2.2 w hw
    have hv := (frequencyRepr_isGen D S H Bd v).2.2 w hw
    rw [hu, hv,
      frequency_count_coeIdeal_eq_factorCount u.1.1.1 u.1.1.2.1 w,
      frequency_count_coeIdeal_eq_factorCount v.1.1.1 v.1.1.2.1 w] at hcount
    have hbu := u.1.2 w hw
    have hbv := v.1.2 w hw
    rw [frequency_count_coeIdeal_eq_factorCount u.1.1.1 u.1.1.2.1 w] at hbu
    rw [frequency_count_coeIdeal_eq_factorCount v.1.1.1 v.1.1.2.1 w] at hbv
    omega
  let I₀ : S.ExtIdeal := ⟨1, frequency_one_isExterior S⟩
  have hgenOne : S.IsGen (1 : F) I₀.1 := by
    refine ⟨I₀.2, one_ne_zero, ?_⟩
    intro w hw
    simp [I₀, FractionalIdeal.spanSingleton_one, frequency_one_count]
  have hgenZ : S.IsGen (z : F) I₀.1 := by
    refine ⟨I₀.2, Units.ne_zero z, ?_⟩
    intro w hw
    rw [hcountZ w hw]
    simpa [I₀] using (frequency_one_count w).symm
  have hreprEq : (frequencyRepr D S H Bd u : F) =
      (frequencyRepr D S H Bd v : F) * (z : F) ^ 6 := by
    calc
      _ = ((frequencyRepr D S H Bd u : F) /
          (frequencyRepr D S H Bd v : F)) *
            (frequencyRepr D S H Bd v : F) := by
          field_simp [frequencyRepr_ne_zero D S H Bd v]
      _ = (z : F) ^ 6 * (frequencyRepr D S H Bd v : F) := by rw [hratio]
      _ = _ := mul_comm _ _
  let ui₁ : FrequencyIndex S × S.ExtIdeal := (u, I₀)
  let ui₂ : FrequencyIndex S × S.ExtIdeal := (v, I₀)
  have heq₁ : (frequencyRepr D S H Bd u : F) =
      (frequencyRepr D S H Bd ui₁.1 : F) * ((1 : S.US) : Fˣ) ^ 6 * (1 : F) ^ 6 := by
    simp [ui₁]
  have heq₂ : (frequencyRepr D S H Bd u : F) =
      (frequencyRepr D S H Bd ui₂.1 : F) * ((1 : S.US) : Fˣ) ^ 6 * (z : F) ^ 6 := by
    simpa [ui₂] using hreprEq
  have hp := frequency_decomposition_unique_index D S H Bd ui₁ ui₂
    (1 : S.US) (1 : S.US) (1 : Fˣ) z hgenOne hgenZ
    (frequencyRepr D S H Bd u) heq₁ heq₂
  simpa [ui₁, ui₂] using congrArg Prod.fst hp

private theorem frequency_rootsOfUnity_eq_one_of_mk_eq_one
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (ζ : rootsOfUnity 6 (𝓞 F))
    (hζ : Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) = 1) :
    ζ = 1 := by
  let z : 𝓞 F := ((ζ : (𝓞 F)ˣ) : 𝓞 F)
  have hpowU : (ζ : (𝓞 F)ˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 _).mp ζ.property
  have hpow : z ^ 6 = 1 := by
    dsimp [z]
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun u : (𝓞 F)ˣ => (u : 𝓞 F)) hpowU
  have hpoly : z ^ 6 - 1 = (z - 1) * (z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1) := by ring
  have hprod : (z - 1) * (z ^ 5 + z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by
    rw [← hpoly, hpow]
    ring
  rcases mul_eq_zero.mp hprod with hz | hsum
  · apply Subtype.ext
    apply Units.ext
    exact sub_eq_zero.mp hz
  · have h6zero : (6 : 𝓞 F ⧸ v.asIdeal) = 0 := by
      have h := congrArg (Ideal.Quotient.mk v.asIdeal) hsum
      have hsum' : (1 : 𝓞 F ⧸ v.asIdeal) + 1 + 1 + 1 + 1 + 1 = 0 := by
        simpa [z, hζ] using h
      calc
        (6 : 𝓞 F ⧸ v.asIdeal) =
            (1 : 𝓞 F ⧸ v.asIdeal) + 1 + 1 + 1 + 1 + 1 := by norm_num
        _ = 0 := hsum'
    exact False.elim (h6 ((Ideal.Quotient.eq_zero_iff_mem).mp h6zero))

private theorem frequency_chi_one
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) :
    ArtinPrimitiveRoots.A1.chi D v (1 : F) = 1 := by
  have hres : ArtinPrimitiveRoots.A1.residue v (1 : F) = 1 := by
    unfold ArtinPrimitiveRoots.A1.residue
    letI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have h : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
        (1 : F) * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := by
      refine ⟨(1, 1), Ideal.IsPrime.one_notMem v.isPrime, ?_⟩
      simp
    rw [dif_pos h]
    have hnum : h.choose.1 = h.choose.2 := by
      apply (FaithfulSMul.algebraMap_injective (𝓞 F) F)
      simpa using h.choose_spec.2.symm
    have hden : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 := by
      intro hz
      exact h.choose_spec.1 (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    rw [hnum]
    exact mul_inv_cancel₀ hden
  have hex : ∃ ζ : rootsOfUnity 6 (𝓞 F),
      Ideal.Quotient.mk v.asIdeal ((ζ : (𝓞 F)ˣ) : 𝓞 F) =
        ArtinPrimitiveRoots.A1.residue v (1 : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    refine ⟨1, ?_⟩
    simp [hres]
  have hspec : Ideal.Quotient.mk v.asIdeal
      (((ArtinPrimitiveRoots.A1.chiAlg v (1 : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
        ArtinPrimitiveRoots.A1.residue v (1 : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) := by
    unfold ArtinPrimitiveRoots.A1.chiAlg
    split_ifs with h
    · exact h.choose_spec
    · exact (h hex).elim
  have hchiAlg : ArtinPrimitiveRoots.A1.chiAlg v (1 : F) = 1 := by
    apply frequency_rootsOfUnity_eq_one_of_mk_eq_one D v h6
    simpa [hres] using hspec
  simp [ArtinPrimitiveRoots.A1.chi, hres, hchiAlg]

private theorem frequency_exists_chi_power_ne_one
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (n : ℕ)
    (hn : 1 ≤ n) (hn6 : n < 6) :
    ∃ b : Fˣ, ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0 ∧
      (ArtinPrimitiveRoots.A1.chi D v (b : F)) ^ n ≠ 1 := by
  classical
  letI : v.asIdeal.IsMaximal := v.isMaximal
  let K := 𝓞 F ⧸ v.asIdeal
  letI : Field K := Ideal.Quotient.field v.asIdeal
  letI : Finite K := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite Kˣ := Finite.of_fintype Kˣ
  letI : Fintype Kˣ := Fintype.ofFinite Kˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardUnits : Nat.card Kˣ = Ideal.absNorm v.asIdeal - 1 := by
    rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have horder : orderOf g = Ideal.absNorm v.asIdeal - 1 := by
    calc
      orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Ideal.absNorm v.asIdeal - 1 := hcardUnits
  have hprim : IsPrimitiveRoot g (Ideal.absNorm v.asIdeal - 1) :=
    IsPrimitiveRoot.iff_orderOf.mpr horder
  have h6div := ArtinPrimitiveRoots.A1.six_dvd_absNorm_sub_one D v h6
  let e : ℕ := (Ideal.absNorm v.asIdeal - 1) / 6
  have heMul : 6 * e = Ideal.absNorm v.asIdeal - 1 := by
    dsimp [e]
    exact Nat.mul_div_cancel' h6div
  have hNzero : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h
    exact v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have hNne1 := (ArtinPrimitiveRoots.A1.coprime_six_of_not_mem_six v h6).2
  have hdivPos : 0 < Ideal.absNorm v.asIdeal - 1 := by omega
  have h6le : 6 ≤ Ideal.absNorm v.asIdeal - 1 := Nat.le_of_dvd hdivPos h6div
  have hePos : 0 < e := by
    dsimp [e]
    omega
  have heDvd : e ∣ Ideal.absNorm v.asIdeal - 1 := by
    refine ⟨6, ?_⟩
    nlinarith [heMul]
  have heQuot : (Ideal.absNorm v.asIdeal - 1) / e = 6 := by
    apply (Nat.div_eq_iff_eq_mul_left hePos heDvd).2
    nlinarith [heMul]
  have hroot : IsPrimitiveRoot (g ^ e) 6 := by
    simpa [heQuot] using hprim.pow_of_dvd hePos.ne' heDvd
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (g : K)
  have hr0 : (algebraMap (𝓞 F) F r) ≠ 0 := by
    intro hrF
    have hrO : r = 0 := (IsFractionRing.injective (𝓞 F) F) (by simpa using hrF)
    have hz : (Ideal.Quotient.mk v.asIdeal r : K) = 0 := by rw [hrO]; simp
    rw [hr] at hz
    exact Units.ne_zero g hz
  let b : Fˣ := Units.mk0 (algebraMap (𝓞 F) F r) hr0
  have hbres : ArtinPrimitiveRoots.A1.residue v (b : F) = (g : K) := by
    dsimp [b]
    rw [ArtinPrimitiveRoots.A2.qs_nq0_residue_algebraMap, hr]
  have hbres0 : ArtinPrimitiveRoots.A1.residue v (b : F) ≠ 0 := by
    rw [hbres]
    exact Units.ne_zero g
  have hchiRed := ArtinPrimitiveRoots.A1.KummerProofs.chiAlg_spec D v h6
    (b : F) hbres0
  let zO : 𝓞 F :=
    (((ArtinPrimitiveRoots.A1.chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)
  let χbar : Kˣ := Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom
    ((ArtinPrimitiveRoots.A1.chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ)
  have hχbar : χbar = g ^ e := by
    apply Units.ext
    change Ideal.Quotient.mk v.asIdeal
        (((ArtinPrimitiveRoots.A1.chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F) =
      (g : K) ^ e
    rw [hchiRed, hbres]
  have hpowχ : (ArtinPrimitiveRoots.A1.chi D v (b : F)) ^ n ≠ 1 := by
    intro hpow
    have hchiEq : ArtinPrimitiveRoots.A1.chi D v (b : F) =
        D.σ0 (algebraMap (𝓞 F) F zO) := by
      simp [ArtinPrimitiveRoots.A1.chi, hbres0, zO]
    have hpowσ : (D.σ0 (algebraMap (𝓞 F) F zO)) ^ n = 1 := by
      rw [← hchiEq, hpow]
    have hpowF : (algebraMap (𝓞 F) F zO) ^ n = 1 := by
      apply D.σ0.injective
      simpa only [map_pow, map_one] using hpowσ
    have hpowO : zO ^ n = 1 := by
      apply (IsFractionRing.injective (𝓞 F) F)
      simpa only [map_pow, map_one] using hpowF
    have hpowbar : χbar ^ n = 1 := by
      apply Units.ext
      change Ideal.Quotient.mk v.asIdeal (zO ^ n) = 1
      rw [hpowO]
      simp
    have hpowg : (g ^ e) ^ n = 1 := by simpa [hχbar] using hpowbar
    have hdivn : 6 ∣ n := hroot.dvd_of_pow_eq_one n hpowg
    omega
  exact ⟨b, hbres0, hpowχ⟩

private theorem frequency_kummer_ramified_of_count
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (hv : v ∉ S.Sf) (n : ℕ) (hn : 1 ≤ n) (hn6 : n < 6)
    (hcount : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (frequencyRepr D S H Bd u : F)) = (n : ℤ)) :
    ¬ (frequencyKummer D S H Bd u).UnramifiedAt v := by
  classical
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := by
    intro h
    exact hv (S.over6 v h)
  obtain ⟨b, hbres, hchi⟩ := frequency_exists_chi_power_ne_one D v h6 n hn hn6
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  obtain ⟨κraw, hκrawpow, hκrawinf, hκrawloc⟩ :=
    ArtinPrimitiveRoots.A1.KummerProofs.kummer_character_exists D H a
  have hκrawfin : IsOfFinOrder κraw := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨6, by decide, hκrawpow⟩
  have hrawGood : ∀ w : ArtinPrimitiveRoots.A1.FinPlace F,
      w ∉ S.Sf → ArtinPrimitiveRoots.A1.residue w (a : F) ≠ 0 →
        ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt κraw w ∧
          ArtinPrimitiveRoots.A1.HeckeChar.primeValue κraw w =
            ArtinPrimitiveRoots.A1.chi D w (a : F) := by
    intro w hw hres
    have h6w : (6 : 𝓞 F) ∉ w.asIdeal := by
      intro hz
      exact hw (S.over6 w hz)
    exact ArtinPrimitiveRoots.A1.KummerProofs.kummer_prime_values D H a κraw
      hκrawloc w h6w hres
  have hselEq : frequencyKummer D S H Bd u = κraw := by
    apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a a
      (frequencyKummer D S H Bd u) κraw
      (frequencyKummer_spec D S H Bd u).2 hrawGood
      (frequencyKummer_spec D S H Bd u).1 hκrawfin).2
    exact ⟨1, by simp⟩
  intro hunram
  have hrawram : ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt κraw v := by
    rw [← hselEq]
    exact hunram
  have hbval : v.valuation F (b : F) = 1 :=
    (ArtinPrimitiveRoots.A2.qs_nq0_residue_ne_zero_iff_valuation_one v (b : F)).mp hbres
  let L := v.adicCompletion F
  have hbvalL : Valued.v ((ArtinPrimitiveRoots.A1.toLoc v b : Lˣ) : L) = 1 := by
    change Valued.v (algebraMap F L (b : F)) = 1
    exact (v.valuedAdicCompletion_eq_valuation' (b : F)).trans hbval
  have hbunit : ArtinPrimitiveRoots.A1.toLoc v b ∈
      (v.adicCompletionIntegers F).units :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hbvalL
  have hrawEval : ArtinPrimitiveRoots.A1.HeckeChar.loc κraw v
      (ArtinPrimitiveRoots.A1.toLoc v b) = 1 :=
    hrawram (ArtinPrimitiveRoots.A1.toLoc v b) hbunit.1 hbunit.2
  have hkummerEval :
      ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v
        (ArtinPrimitiveRoots.A1.toLoc v a) (ArtinPrimitiveRoots.A1.toLoc v b) = 1 := by
    change ArtinPrimitiveRoots.A1.KummerProofs.localComponent κraw v
      (ArtinPrimitiveRoots.A1.toLoc v b) = 1 at hrawEval
    rw [hκrawloc v] at hrawEval
    exact hrawEval
  have hhilbertMap : Units.map D.σ0.toMonoidHom
      (H.hilb v (ArtinPrimitiveRoots.A1.toLoc v a)
        (ArtinPrimitiveRoots.A1.toLoc v b)) = 1 := by
    simpa [ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal] using hkummerEval
  have hhilbert : H.hilb v (ArtinPrimitiveRoots.A1.toLoc v a)
      (ArtinPrimitiveRoots.A1.toLoc v b) = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply RingHom.injective D.σ0
    have hval := congrArg (fun z : ℂˣ => (z : ℂ)) hhilbertMap
    simpa [Units.map] using hval
  have hhilbertRev : H.hilb v (ArtinPrimitiveRoots.A1.toLoc v b)
      (ArtinPrimitiveRoots.A1.toLoc v a) = 1 := by
    have h := H.skew v (ArtinPrimitiveRoots.A1.toLoc v b)
      (ArtinPrimitiveRoots.A1.toLoc v a)
    rw [hhilbert, mul_one] at h
    exact h
  have hcountA : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)) = (n : ℤ) := by
    simpa [a] using hcount
  have htame := H.tame v h6 b a hbres
  rw [hcountA] at htame
  let zO : 𝓞 F :=
    (((ArtinPrimitiveRoots.A1.chiAlg v (b : F) : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)
  have hrootPow : (algebraMap (𝓞 F) F zO) ^ n = 1 := by
    simpa [hhilbertRev, zpow_natCast] using htame.symm
  have hchiPow : (ArtinPrimitiveRoots.A1.chi D v (b : F)) ^ n = 1 := by
    have hchiEq : ArtinPrimitiveRoots.A1.chi D v (b : F) =
        D.σ0 (algebraMap (𝓞 F) F zO) := by
      simp [ArtinPrimitiveRoots.A1.chi, hbres, zO]
    rw [hchiEq, ← map_pow, hrootPow]
    simp
  exact hchi hchiPow

private theorem frequencyKummer_primeValue_masked
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (hv : v ∉ S.Sf) :
    (frequencyKummer D S H Bd u).primeValue v =
      if ArtinPrimitiveRoots.A1.residue v (frequencyRepr D S H Bd u : F) = 0 then 0
      else ArtinPrimitiveRoots.A1.chi D v (frequencyRepr D S H Bd u : F) := by
  classical
  by_cases hres : ArtinPrimitiveRoots.A1.residue v (frequencyRepr D S H Bd u : F) ≠ 0
  · have hspec := (frequencyKummer_spec D S H Bd u).2 v hv hres
    have hspecValue := hspec.2
    rw [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos hspec.1] at hspecValue
    rw [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos hspec.1]
    have hne : ¬ ArtinPrimitiveRoots.A1.residue v
        (frequencyRepr D S H Bd u : F) = 0 := by
      intro hz
      exact hres (by simp [hz])
    rw [if_neg hne]
    exact hspecValue
  · have hres0 : ArtinPrimitiveRoots.A1.residue v (frequencyRepr D S H Bd u : F) = 0 := by
      exact not_ne_iff.mp hres
    have hgen := (frequencyRepr_isGen D S H Bd u).2.2 v hv
    have hbounds : 0 ≤ FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (frequencyRepr D S H Bd u : F)) ∧
        FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (frequencyRepr D S H Bd u : F)) < 6 := by
      constructor
      · rw [hgen]
        exact FractionalIdeal.count_coe_nonneg F v u.1.1.1
      · rw [hgen]
        exact u.1.2 v hv
    have hcountNe : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (frequencyRepr D S H Bd u : F)) ≠ 0 := by
      intro hzero
      exact hres ((ArtinPrimitiveRoots.A1.KummerProofs.residue_ne_zero_iff_ord_zero v
        (frequencyRepr D S H Bd u : F)).2
          ⟨hzero, frequencyRepr_ne_zero D S H Bd u⟩)
    have hcountPos : 0 < FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (frequencyRepr D S H Bd u : F)) := by omega
    let n := (FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
        (frequencyRepr D S H Bd u : F))).toNat
    have hncast : (n : ℤ) = FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (frequencyRepr D S H Bd u : F)) := Int.toNat_of_nonneg hbounds.1
    have hncountPos : (0 : ℤ) < (n : ℤ) := by rw [hncast]; exact hcountPos
    have hn : 1 ≤ n := by exact_mod_cast hncountPos
    have hncount6 : (n : ℤ) < 6 := by rw [hncast]; exact hbounds.2
    have hn6 : n < 6 := by exact_mod_cast hncount6
    have hram := frequency_kummer_ramified_of_count D S H Bd u v hv n hn hn6
      hncast.symm
    simp [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, hres0, hram]

private theorem frequency_kummerLocal_mul_sixth
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
  (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a t : (v.adicCompletion F)ˣ) :
    ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v (a * t ^ 6) =
      ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v a := by
  apply MonoidHom.ext
  intro x
  change Units.map D.σ0.toMonoidHom
      (H.hilb v (a * t ^ 6) x : Fˣ) =
    Units.map D.σ0.toMonoidHom (H.hilb v a x : Fˣ)
  have hh : H.hilb v (a * t ^ 6) x = H.hilb v a x := by
    rw [H.mul_left, H.sixth_power v (t ^ 6) x ⟨t, rfl⟩]
    simp
  rw [hh]

private theorem frequency_kummerLocal_range_finite
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    (Set.range (fun a : (v.adicCompletion F)ˣ =>
      ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v a)).Finite := by
  classical
  letI : Finite (𝓞 F ⧸ v.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : ValuativeRel (v.adicCompletion F) :=
    IsDedekindDomain.HeightOneSpectrum.instValuativeRelAdicCompletion v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    IsDedekindDomain.HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion
      (R := 𝓞 F) (K := F) v
  let pow6 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ := powMonoidHom 6
  have h6K : (6 : v.adicCompletion F) ≠ 0 := by
    intro h
    have hmap : (algebraMap F (v.adicCompletion F)) (6 : F) = 0 := by
      simpa using h
    have hF : (6 : F) = 0 := (RingHom.injective (algebraMap F (v.adicCompletion F))) hmap
    norm_num at hF
  have hpowFinite : pow6.range.FiniteIndex := by
    dsimp [pow6]
    exact TauCeti.finiteIndex_range_powMonoidHom h6K
  have hfiniteQ : Finite ((v.adicCompletion F)ˣ ⧸ pow6.range) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI : Finite ((v.adicCompletion F)ˣ ⧸ pow6.range) := hfiniteQ
  letI : Fintype ((v.adicCompletion F)ˣ ⧸ pow6.range) := Fintype.ofFinite _
  let f : ((v.adicCompletion F)ˣ ⧸ pow6.range) →
      ((v.adicCompletion F)ˣ →* ℂˣ) := fun q =>
    ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v (Quotient.out q)
  have hsub : Set.range (fun a : (v.adicCompletion F)ˣ =>
      ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v a) ⊆ Set.range f := by
    rintro ψ ⟨a, rfl⟩
    let q : (v.adicCompletion F)ˣ ⧸ pow6.range :=
      QuotientGroup.mk (s := pow6.range) a
    have hmk : QuotientGroup.mk (s := pow6.range) (Quotient.out q) = q := by
      simpa [q] using (Quotient.out_eq' q)
    have hmem : Quotient.out q / a ∈ pow6.range :=
      (QuotientGroup.eq_iff_div_mem (N := pow6.range)).mp hmk
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hmem
    have hpow : t ^ 6 = Quotient.out q / a := by
      simpa [pow6, powMonoidHom_apply] using ht
    have hrepr : Quotient.out q = a * t ^ 6 := by
      calc
        Quotient.out q = (Quotient.out q / a) * a := by simp
        _ = t ^ 6 * a := by rw [← hpow]
        _ = a * t ^ 6 := mul_comm _ _
    refine ⟨q, ?_⟩
    dsimp [f]
    rw [hrepr]
    exact frequency_kummerLocal_mul_sixth D H v a t
  exact (Set.finite_range f).subset hsub

private theorem frequencyKummer_loc_eq_kummerLocal
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.A1.HeckeChar.loc (frequencyKummer D S H Bd u) v =
      ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v
        (ArtinPrimitiveRoots.A1.toLoc v
          (Units.mk0 (frequencyRepr D S H Bd u : F)
            (frequencyRepr_ne_zero D S H Bd u))) := by
  classical
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  obtain ⟨κraw, hpow, hinf, hloc⟩ :=
    ArtinPrimitiveRoots.A1.KummerProofs.kummer_character_exists D H a
  have hrawFin : IsOfFinOrder κraw := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨6, by decide, hpow⟩
  have hrawGood : ∀ w : ArtinPrimitiveRoots.A1.FinPlace F,
      w ∉ S.Sf → ArtinPrimitiveRoots.A1.residue w (a : F) ≠ 0 →
        ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt κraw w ∧
          ArtinPrimitiveRoots.A1.HeckeChar.primeValue κraw w =
            ArtinPrimitiveRoots.A1.chi D w (a : F) := by
    intro w hw hres
    have h6w : (6 : 𝓞 F) ∉ w.asIdeal := by
      intro hz
      exact hw (S.over6 w hz)
    exact ArtinPrimitiveRoots.A1.KummerProofs.kummer_prime_values D H a κraw
      hloc w h6w hres
  have hselEq : frequencyKummer D S H Bd u = κraw := by
    apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a a
      (frequencyKummer D S H Bd u) κraw
      (frequencyKummer_spec D S H Bd u).2 hrawGood
      (frequencyKummer_spec D S H Bd u).1 hrawFin).2
    exact ⟨1, by simp⟩
  rw [hselEq]
  simpa [ArtinPrimitiveRoots.A1.HeckeChar.loc,
    ArtinPrimitiveRoots.A1.KummerProofs.localComponent] using hloc v

private theorem frequencyOmega_loc_eq
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F)
    (u : FrequencyIndex S) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.A1.HeckeChar.loc (frequencyOmega S D H Bd η u) v =
      η.loc v *
        (ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v
          (ArtinPrimitiveRoots.A1.toLoc v
            (Units.mk0 (frequencyRepr D S H Bd u : F)
              (frequencyRepr_ne_zero D S H Bd u))))⁻¹ := by
  have hκ := frequencyKummer_loc_eq_kummerLocal D S H Bd u v
  change η.loc v * ((frequencyKummer D S H Bd u).loc v)⁻¹ =
    η.loc v * (ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v
      (ArtinPrimitiveRoots.A1.toLoc v
        (Units.mk0 (frequencyRepr D S H Bd u : F)
          (frequencyRepr_ne_zero D S H Bd u))))⁻¹
  rw [hκ]

private theorem frequency_local_components_finite
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) :
    ∃ LS : Finset (SLocalCharacter S), ∀ u : FrequencyIndex S,
      SComponent S (frequencyOmega S D H Bd η u) ∈ LS := by
  classical
  let T : ∀ v : S.Sf, Set ((v.1.adicCompletion F)ˣ →* ℂˣ) := fun v =>
    Set.range (fun u : FrequencyIndex S =>
      SComponent S (frequencyOmega S D H Bd η u) v)
  have hT : ∀ v : S.Sf, (T v).Finite := by
    intro v
    let φ : ((v.1.adicCompletion F)ˣ →* ℂˣ) →
        ((v.1.adicCompletion F)ˣ →* ℂˣ) :=
      fun ψ => η.loc v.1 * ψ⁻¹
    have hlocal := frequency_kummerLocal_range_finite D H v.1
    have hsub : T v ⊆ φ '' Set.range
        (fun a : (v.1.adicCompletion F)ˣ =>
          ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v.1 a) := by
      rintro ψ ⟨u, rfl⟩
      refine ⟨ArtinPrimitiveRoots.A1.KummerProofs.kummerLocal D H v.1
          (ArtinPrimitiveRoots.A1.toLoc v.1
            (Units.mk0 (frequencyRepr D S H Bd u : F)
              (frequencyRepr_ne_zero D S H Bd u))),
        ⟨ArtinPrimitiveRoots.A1.toLoc v.1
          (Units.mk0 (frequencyRepr D S H Bd u : F)
            (frequencyRepr_ne_zero D S H Bd u)), rfl⟩, ?_⟩
      simpa [φ, ArtinPrimitiveRoots.A2.SComponent] using
        (frequencyOmega_loc_eq S D H Bd η u v.1).symm
    exact (hlocal.image φ).subset hsub
  let all : Set (SLocalCharacter S) :=
    {f | ∀ v : S.Sf, f v ∈ T v}
  have hall : all.Finite := Set.Finite.pi' hT
  refine ⟨hall.toFinset, ?_⟩
  intro u
  apply (Set.Finite.mem_toFinset hall).mpr
  intro v
  exact ⟨u, rfl⟩

private theorem frequency_kummer_eq_one_of_sixth
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S)
    (z : Fˣ)
    (hz : (frequencyRepr D S H Bd u : F) = (z : F) ^ 6) :
    frequencyKummer D S H Bd u = 1 := by
  classical
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  obtain ⟨κ₁, hκ₁fin, hκ₁loc⟩ := ArtinPrimitiveRoots.A1.kummer_exists D S (1 : Fˣ)
  have htrivRam (v : ArtinPrimitiveRoots.A1.FinPlace F) :
      (1 : ArtinPrimitiveRoots.A1.HeckeChar F).UnramifiedAt v := by
    intro x hx hxinv
    simp [ArtinPrimitiveRoots.A1.HeckeChar.UnramifiedAt,
      ArtinPrimitiveRoots.A1.HeckeChar.loc]
  have htrivLoc (v : ArtinPrimitiveRoots.A1.FinPlace F)
      (hvS : v ∉ S.Sf) (hres : ArtinPrimitiveRoots.A1.residue v (1 : F) ≠ 0) :
      (1 : ArtinPrimitiveRoots.A1.HeckeChar F).UnramifiedAt v ∧
        (1 : ArtinPrimitiveRoots.A1.HeckeChar F).primeValue v =
          ArtinPrimitiveRoots.A1.chi D v (1 : F) := by
    have h6 : (6 : 𝓞 F) ∉ v.asIdeal := by
      intro h
      exact hvS (S.over6 v h)
    have hchi := frequency_chi_one D v h6
    refine ⟨htrivRam v, ?_⟩
    rw [ArtinPrimitiveRoots.A1.HeckeChar.primeValue, if_pos (htrivRam v)]
    simp [hchi, ArtinPrimitiveRoots.A1.HeckeChar.loc]
  have h1fin : IsOfFinOrder (1 : ArtinPrimitiveRoots.A1.HeckeChar F) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨1, by decide, by simp⟩
  have hκ₁ : κ₁ = 1 := by
    apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S (1 : Fˣ) (1 : Fˣ)
      κ₁ 1 hκ₁loc htrivLoc hκ₁fin h1fin).2
    exact ⟨1, by simp⟩
  have ha6 : a / (1 : Fˣ) = z ^ 6 := by
    apply Units.ext
    simpa [a] using hz
  have hκa : frequencyKummer D S H Bd u = κ₁ := by
    apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a (1 : Fˣ)
      (frequencyKummer D S H Bd u) κ₁ (frequencyKummer_spec D S H Bd u).2
      hκ₁loc (frequencyKummer_spec D S H Bd u).1 hκ₁fin).2
    exact ⟨z, ha6⟩
  exact hκa.trans hκ₁

private theorem frequency_one_repr_sixth
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    ∃ z : Fˣ,
      (frequencyRepr D S H Bd (frequencyOne D S H Bd) : F) = (z : F) ^ 6 := by
  classical
  let I : S.ExtIdeal := ⟨1, frequency_one_isExterior S⟩
  let g : Fˣ := frequencyAllowedGenerator D S H Bd I
  have hgen : S.IsGen (g : F) (1 : Ideal (𝓞 F)) := by
    dsimp [g]
    simpa [I] using frequencyAllowedGenerator_spec D S H Bd I
  let e : S.US := ⟨g⁻¹, (S.US).inv_mem (frequency_generator_one_mem_US S g hgen)⟩
  let I6 : FrequencySixFreeExtIdeal S := ⟨I, by
    intro v hv
    change FractionalIdeal.count F v (1 : Ideal (𝓞 F)) < 6
    rw [frequency_one_count]
    norm_num⟩
  have hOne : frequencyOne D S H Bd = (I6, QuotientGroup.mk e) := by
    simp [frequencyOne, I6, I, g, e, hgen]
  let eRep : S.US := frequencyUnitClassRepresentative S (frequencyOne D S H Bd).2
  have hmkRep := frequency_unitClassRepresentative_spec S (frequencyOne D S H Bd).2
  have hmkE : QuotientGroup.mk e = (frequencyOne D S H Bd).2 := by
    rw [hOne]
  have hclass : QuotientGroup.mk eRep = QuotientGroup.mk e := hmkRep.trans hmkE.symm
  have hmem : eRep / e ∈ ArtinPrimitiveRoots.A2.Gamma S :=
    (QuotientGroup.eq_iff_div_mem (N := ArtinPrimitiveRoots.A2.Gamma S)).mp hclass
  have hmem' : eRep / e ∈ (ArtinPrimitiveRoots.A2.sixthPowerOnUS S).range := by
    simpa [ArtinPrimitiveRoots.A2.Gamma] using hmem
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hmem'
  have hzpow : z ^ 6 = eRep / e := by
    simpa [ArtinPrimitiveRoots.A2.sixthPowerOnUS] using hz
  have heq : eRep = e * z ^ 6 := by
    calc
      eRep = (eRep / e) * e := by simp
      _ = z ^ 6 * e := by rw [← hzpow]
      _ = e * z ^ 6 := mul_comm _ _
  have hrepr : (frequencyRepr D S H Bd (frequencyOne D S H Bd) : F) =
      ((g * (eRep : Fˣ) : Fˣ) : F) := by
    rw [hOne]
    rfl
  have hge : g * (e : Fˣ) = 1 := by
    apply Units.ext
    simp [e]
  have heqF : ((eRep : Fˣ) : F) = ((e : Fˣ) : F) * ((z : Fˣ) : F) ^ 6 := by
    calc
      ((eRep : Fˣ) : F) = (((e * z ^ 6 : S.US) : Fˣ) : F) :=
        congrArg (fun t : S.US => ((t : Fˣ) : F)) heq
      _ = ((e : Fˣ) : F) * ((z : Fˣ) : F) ^ 6 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
          Units.val_pow_eq_pow_val]
  refine ⟨(z : Fˣ), ?_⟩
  calc
    (frequencyRepr D S H Bd (frequencyOne D S H Bd) : F) =
        ((g * (eRep : Fˣ) : Fˣ) : F) := hrepr
    _ = ((g * (e : Fˣ) : Fˣ) : F) * ((z : Fˣ) : F) ^ 6 := by
      simp only [Units.val_mul, heqF]
      ring
    _ = ((z : Fˣ) : F) ^ 6 := by
      rw [hge]
      simp

private theorem frequencyKummer_injective
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    Function.Injective (frequencyKummer D S H Bd) := by
  intro u v huv
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  let b : Fˣ := Units.mk0 (frequencyRepr D S H Bd v : F)
    (frequencyRepr_ne_zero D S H Bd v)
  obtain ⟨z, hz⟩ := (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a b
    (frequencyKummer D S H Bd u) (frequencyKummer D S H Bd v)
    (frequencyKummer_spec D S H Bd u).2 (frequencyKummer_spec D S H Bd v).2
    (frequencyKummer_spec D S H Bd u).1 (frequencyKummer_spec D S H Bd v).1).mp huv
  have hratio : (frequencyRepr D S H Bd u : F) /
      (frequencyRepr D S H Bd v : F) = (z : F) ^ 6 := by
    have h := congrArg (fun x : Fˣ => (x : F)) hz
    simpa [a, b] using h
  exact frequency_index_eq_of_sixth_ratio D S H Bd u v z hratio

private theorem frequencyOmega_injective
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) :
    Function.Injective (frequencyOmega S D H Bd η) := by
  intro u v huv
  have hk : frequencyKummer D S H Bd u = frequencyKummer D S H Bd v := by
    have hinvChar : (frequencyKummer D S H Bd u)⁻¹ =
        (frequencyKummer D S H Bd v)⁻¹ := by
      ext x
      have hval : (η x : ℂ) *
          ((((frequencyKummer D S H Bd u)⁻¹) x : ℂˣ) : ℂ) =
        (η x : ℂ) * ((((frequencyKummer D S H Bd v)⁻¹) x : ℂˣ) : ℂ) := by
        have h := congrArg (fun χ : ArtinPrimitiveRoots.A1.HeckeChar F => (χ x : ℂ)) huv
        simpa [frequencyOmega, ContinuousMonoidHom.mul_apply] using h
      exact mul_left_cancel₀ (Units.ne_zero (η x)) hval
    exact inv_injective hinvChar
  exact frequencyKummer_injective D S H Bd hk

private theorem frequencyKummer_one
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    frequencyKummer D S H Bd (frequencyOne D S H Bd) = 1 := by
  obtain ⟨z, hz⟩ := frequency_one_repr_sixth D S H Bd
  exact frequency_kummer_eq_one_of_sixth D S H Bd
    (frequencyOne D S H Bd) z hz

private theorem frequencyKummer_eq_one_iff
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) (u : FrequencyIndex S) :
    frequencyKummer D S H Bd u = 1 ↔ u = frequencyOne D S H Bd := by
  constructor
  · intro hu
    have h := hu.trans (frequencyKummer_one D S H Bd).symm
    exact frequencyKummer_injective D S H Bd h
  · intro hu
    rw [hu]
    exact frequencyKummer_one D S H Bd

private theorem frequency_decomposition_exists
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (x : S.R) (hx : (x : F) ≠ 0) :
    ∃ ui : FrequencyIndex S × S.ExtIdeal, ∃ ε : S.US, ∃ a : Fˣ,
      S.IsGen (a : F) ui.2.1 ∧
      (x : F) = (frequencyRepr D S H Bd ui.1 : F) *
        ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6 := by
  classical
  obtain ⟨I, J, hfree, hgenX⟩ := frequency_sInteger_exterior_decomposition S x hx
  let I6 : FrequencySixFreeExtIdeal S := ⟨I, fun v hv => (hfree v hv).2⟩
  let gI : Fˣ := frequencyAllowedGenerator D S H Bd I
  let a₀ : Fˣ := frequencyAllowedGenerator D S H Bd J
  have hgenGI : S.IsGen (gI : F) I.1 := by
    dsimp [gI]
    exact frequencyAllowedGenerator_spec D S H Bd I
  have hgenA₀ : S.IsGen (a₀ : F) J.1 := by
    dsimp [a₀]
    exact frequencyAllowedGenerator_spec D S H Bd J
  have hgenA6 : S.IsGen ((a₀ ^ 6 : Fˣ) : F) (J.1 ^ 6) :=
    frequency_isGen_pow S 6 hgenA₀
  have hgenY : S.IsGen ((gI * a₀ ^ 6 : Fˣ) : F) (I.1 * J.1 ^ 6) :=
    frequency_isGen_mul S hgenGI hgenA6
  obtain ⟨δ, hδ⟩ := frequency_sUnit_of_sameGen S (I.1 * J.1 ^ 6)
    (x : F) ((gI * a₀ ^ 6 : Fˣ) : F) hx (Units.ne_zero _) hgenX hgenY
  let uIndex : FrequencyIndex S := ⟨I6, QuotientGroup.mk δ⟩
  let ui : FrequencyIndex S × S.ExtIdeal := ⟨uIndex, J⟩
  let εui : S.US := frequencyUnitClassRepresentative S uIndex.2
  let b : Fˣ := gI * (εui : Fˣ)
  have hb : (frequencyRepr D S H Bd uIndex : F) = (b : F) := rfl
  have hmkεui := frequency_unitClassRepresentative_spec S uIndex.2
  have hδclass : (QuotientGroup.mk δ : UnitSix S) =
      (QuotientGroup.mk εui : UnitSix S) := by
    change uIndex.2 = (QuotientGroup.mk εui : UnitSix S)
    exact hmkεui.symm
  have hmem : δ / εui ∈ ArtinPrimitiveRoots.A2.Gamma S :=
    (QuotientGroup.eq_iff_div_mem (N := ArtinPrimitiveRoots.A2.Gamma S)).mp hδclass
  have hmem' : δ / εui ∈ (ArtinPrimitiveRoots.A2.sixthPowerOnUS S).range := by
    simpa [ArtinPrimitiveRoots.A2.Gamma] using hmem
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hmem'
  have hzpow : z ^ 6 = δ / εui := by
    simpa [ArtinPrimitiveRoots.A2.sixthPowerOnUS] using hz
  have hδeq : δ = εui * z ^ 6 := by
    calc
      δ = (δ / εui) * εui := by simp
      _ = z ^ 6 * εui := by rw [← hzpow]
      _ = εui * z ^ 6 := mul_comm _ _
  let aw : Fˣ := z * a₀
  have hgenAw : S.IsGen (aw : F) J.1 := by
    simpa [aw] using ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit S z a₀ hgenA₀
  refine ⟨ui, 1, aw, hgenAw, ?_⟩
  have hδF : ((δ : Fˣ) : F) = (x : F) / ((gI * a₀ ^ 6 : Fˣ) : F) := hδ
  have hδeqF' : ((δ : Fˣ) : F) = ((εui : Fˣ) : F) * ((z : Fˣ) : F) ^ 6 := by
    calc
      ((δ : Fˣ) : F) = (((εui * z ^ 6 : S.US) : Fˣ) : F) :=
        congrArg (fun t : S.US => ((t : Fˣ) : F)) hδeq
      _ = ((εui : Fˣ) : F) * (((z ^ 6 : S.US) : Fˣ) : F) := by
        simp only [Subgroup.coe_mul, Units.val_mul]
      _ = ((εui : Fˣ) : F) * ((z : Fˣ) : F) ^ 6 := by
        simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  calc
    (x : F) = ((δ : Fˣ) : F) * ((gI * a₀ ^ 6 : Fˣ) : F) := by
      rw [hδF]
      field_simp
    _ = (((εui : Fˣ) : F) * ((z : Fˣ) : F) ^ 6) *
          ((gI * a₀ ^ 6 : Fˣ) : F) := by rw [hδeqF']
    _ = ((b : Fˣ) : F) * ((aw : Fˣ) : F) ^ 6 := by
      simp only [b, aw, Units.val_mul, Units.val_pow_eq_pow_val]
      ring_nf
    _ = (frequencyRepr D S H Bd uIndex : F) * (aw : F) ^ 6 := by rw [hb]
    _ = (frequencyRepr D S H Bd ui.1 : F) * (1 : F) ^ 6 * (aw : F) ^ 6 := by simp [ui]

private theorem frequency_decomposition_surjective
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (I : S.ExtIdeal) :
    ∃ x : S.R, (x : F) ≠ 0 ∧ ∃ ε : S.US, ∃ a : Fˣ,
      S.IsGen (a : F) I.1 ∧
      (x : F) = (frequencyRepr D S H Bd u : F) * ((ε : Fˣ) : F) ^ 6 * (a : F) ^ 6 := by
  let a : Fˣ := frequencyAllowedGenerator D S H Bd I
  have haGen : S.IsGen (a : F) I.1 := by
    dsimp [a]
    exact frequencyAllowedGenerator_spec D S H Bd I
  have haR : (a : F) ∈ S.R := frequency_generator_mem_Sintegers S I a haGen
  have hpowR : ((a : F) ^ 6) ∈ S.R := S.R.pow_mem haR 6
  have hxR : (frequencyRepr D S H Bd u : F) * (a : F) ^ 6 ∈ S.R :=
    S.R.mul_mem (frequencyRepr D S H Bd u).property hpowR
  let x : S.R := ⟨(frequencyRepr D S H Bd u : F) * (a : F) ^ 6, hxR⟩
  refine ⟨x, mul_ne_zero (frequencyRepr_ne_zero D S H Bd u)
      (pow_ne_zero 6 (Units.ne_zero a)), 1, a, haGen, ?_⟩
  simp [x]

private theorem frequency_exists_minimal_conductor
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (m : Ideal (𝓞 F))
    (hm0 : m ≠ ⊥) (hmc : χ.ConductorDvd m) :
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor χ f ∧
      Ideal.absNorm f ≤ Ideal.absNorm m := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ f : Ideal (𝓞 F), f ≠ ⊥ ∧ χ.ConductorDvd f ∧ Ideal.absNorm f = n
  have hP : ∃ n, P n := ⟨Ideal.absNorm m, m, hm0, hmc, rfl⟩
  let n₀ := Nat.find hP
  have h₀ : P n₀ := Nat.find_spec hP
  obtain ⟨f, hf0, hfc, hfn⟩ := h₀
  refine ⟨f, ⟨hf0, hfc, ?_⟩, ?_⟩
  · intro g hg0 hgc
    have hmin := Nat.find_min' hP ⟨g, hg0, hgc, rfl⟩
    omega
  · have hmin := Nat.find_min' hP ⟨m, hm0, hmc, rfl⟩
    omega

private theorem frequency_conductorDvd_nonbot
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (m : Ideal (𝓞 F))
    (hmc : χ.ConductorDvd m) :
    ∃ m' : Ideal (𝓞 F), m' ≠ ⊥ ∧ χ.ConductorDvd m' := by
  by_cases hm : m = ⊥
  · subst m
    refine ⟨⊤, top_ne_bot, ?_⟩
    intro v z hz hzInv hval
    have hexp : ArtinPrimitiveRoots.A1.idealExp v (⊤ : Ideal (𝓞 F)) =
        ArtinPrimitiveRoots.A1.idealExp v (⊥ : Ideal (𝓞 F)) := by
      have htop : ArtinPrimitiveRoots.A1.idealExp v (⊤ : Ideal (𝓞 F)) = 0 := by
        unfold ArtinPrimitiveRoots.A1.idealExp
        rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
        by_cases hirr : Irreducible (Associates.mk v.asIdeal)
        · exact Associates.count_zero hirr
        · simp [Associates.count, hirr]
      have hbot : ArtinPrimitiveRoots.A1.idealExp v (⊥ : Ideal (𝓞 F)) = 0 := by
        unfold ArtinPrimitiveRoots.A1.idealExp
        rw [← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
        by_cases hirr : Irreducible v.asIdeal <;>
          simp [Associates.count, Associates.bcount, hirr]
      exact htop.trans hbot.symm
    apply hmc v z hz hzInv
    rw [← hexp]
    exact hval
  · exact ⟨m, hm, hmc⟩

private theorem frequency_omega_primitive
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (u : FrequencyIndex S) :
    ∃ f : Ideal (𝓞 F), IsPrimitiveConductor (frequencyOmega S D H Bd η u) f := by
  classical
  obtain ⟨n, d, hnd⟩ := frequency_sInteger_integral_sixth_multiple S
    (frequencyRepr D S H Bd u)
  have hn0 : n ≠ 0 := by
    intro hn
    have hz := congrArg (algebraMap (𝓞 F) F) hn
    rw [map_zero] at hz
    have hprod : (frequencyRepr D S H Bd u : F) * ((d : 𝓞 F) : F) ^ 6 = 0 := by
      rw [← hnd]
      exact hz
    have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
    exact frequencyRepr_ne_zero D S H Bd u
      ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 6 hd0))
  have hnF : (n : F) ≠ 0 := by
    intro h
    exact hn0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  let b : Fˣ := Units.mk0 (n : F) hnF
  let dUnit : Fˣ := Units.mk0 ((d : 𝓞 F) : F) (by exact_mod_cast d.property.1)
  have hdF : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
  obtain ⟨κn, hκnfin, hκnloc⟩ := ArtinPrimitiveRoots.A1.kummer_exists D S b
  have hratio : a / b = dUnit⁻¹ ^ 6 := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    dsimp [a, b, dUnit]
    rw [hnd]
    field_simp [hdF, frequencyRepr_ne_zero D S H Bd u]
  have hκEq : frequencyKummer D S H Bd u = κn := by
    apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a b
      (frequencyKummer D S H Bd u) κn
      (frequencyKummer_spec D S H Bd u).2 hκnloc
      (frequencyKummer_spec D S H Bd u).1 hκnfin).2
    exact ⟨dUnit⁻¹, hratio⟩
  obtain ⟨C, hC⟩ := ArtinPrimitiveRoots.A1.kummer_conductor D S η
  have hmods := hC n hn0 κn hκnloc hκnfin
  obtain ⟨mκ, hmκ, hmκbound⟩ := hmods.1
  obtain ⟨mω, hmω, hmωbound⟩ := hmods.2
  have hmω' : (frequencyOmega S D H Bd η u).ConductorDvd mω := by
    simpa [frequencyOmega, hκEq] using hmω
  obtain ⟨mω', hmω'0, hmω'cond⟩ :=
    frequency_conductorDvd_nonbot (frequencyOmega S D H Bd η u) mω hmω'
  obtain ⟨f, hf, _hfnorm⟩ :=
    frequency_exists_minimal_conductor (frequencyOmega S D H Bd η u)
      mω' hmω'0 hmω'cond
  exact ⟨f, hf⟩

private theorem frequency_integral_sixth_multiple_isGen
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (u : FrequencyIndex S) (n : 𝓞 F)
    (d : ArtinPrimitiveRoots.Proofs.A1Generators.generatorDenominators S)
    (hnd : (n : F) = (frequencyRepr D S H Bd u : F) * ((d : 𝓞 F) : F) ^ 6) :
    S.IsGen (n : F) u.1.1.1 := by
  let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
    (frequencyRepr_ne_zero D S H Bd u)
  have ha : S.IsGen (a : F) u.1.1.1 := by
    simpa [a] using frequencyRepr_isGen D S H Bd u
  let dUnit : Fˣ := Units.mk0 ((d : 𝓞 F) : F) (by exact_mod_cast d.property.1)
  have hdUS : dUnit ∈ S.US := by
    change ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      v.valuation F (dUnit : F) = 1
    intro v hv
    exact d.property.2 v hv
  let dS : S.US := ⟨dUnit, hdUS⟩
  have hgen := ArtinPrimitiveRoots.Proofs.A1Generators.isGen_mul_sUnit
    S (dS ^ 6) a ha
  have hval : (n : F) = ((dS ^ 6 * a : Fˣ) : F) := by
    calc
      (n : F) = (frequencyRepr D S H Bd u : F) * ((d : 𝓞 F) : F) ^ 6 := hnd
      _ = ((d : 𝓞 F) : F) ^ 6 * (frequencyRepr D S H Bd u : F) := mul_comm _ _
      _ = ((dS ^ 6 * a : Fˣ) : F) := by
        simp [dS, dUnit, a, Units.val_pow_eq_pow_val]
  refine ⟨hgen.1, ?_, ?_⟩
  · rw [hval]
    exact hgen.2.1
  · intro v hv
    rw [hval]
    exact hgen.2.2 v hv

private theorem frequency_radical_exp_le_exterior
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : S.ExtIdeal) (n : 𝓞 F) (hn : n ≠ 0)
    (hgen : S.IsGen (n : F) I.1)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (hv : v ∉ S.Sf) :
    ArtinPrimitiveRoots.A1.idealExp v (Ideal.radical (Ideal.span {n})) ≤
      ArtinPrimitiveRoots.A1.idealExp v I.1 := by
  classical
  let N : Ideal (𝓞 F) := Ideal.span {n}
  let J : Ideal (𝓞 F) := Ideal.radical N
  have hN0 : N ≠ ⊥ := by
    intro h
    exact hn (Ideal.span_singleton_eq_bot.mp h)
  have hJ0 : J ≠ ⊥ := by
    intro h
    have hle : N ≤ J := Ideal.le_radical
    rw [h] at hle
    exact hn (Ideal.span_singleton_eq_bot.mp (bot_unique hle))
  have hJrad : J.IsRadical := Ideal.radical_isRadical N
  have hJmon : IsRadical J := by
    intro k L hdiv
    rw [Ideal.dvd_iff_le] at hdiv ⊢
    intro x hx
    exact hJrad ⟨k, hdiv (Ideal.pow_mem_pow hx k)⟩
  have hJnodup : (UniqueFactorizationMonoid.normalizedFactors J).Nodup :=
    UniqueFactorizationMonoid.normalizedFactors_nodup hJmon
  have hExpJ : ArtinPrimitiveRoots.A1.idealExp v J =
      (UniqueFactorizationMonoid.normalizedFactors J).count v.asIdeal := by
    unfold ArtinPrimitiveRoots.A1.idealExp
    rw [Ideal.count_associates_factors_eq hJ0 v.isPrime v.ne_bot]
  have hExpI : ArtinPrimitiveRoots.A1.idealExp v I.1 =
      (UniqueFactorizationMonoid.normalizedFactors I.1).count v.asIdeal := by
    unfold ArtinPrimitiveRoots.A1.idealExp
    rw [Ideal.count_associates_factors_eq I.2.1 v.isPrime v.ne_bot]
  have hExpJle : ArtinPrimitiveRoots.A1.idealExp v J ≤ 1 := by
    rw [hExpJ]
    exact (Multiset.nodup_iff_count_le_one.mp hJnodup) v.asIdeal
  by_cases hExpJne : ArtinPrimitiveRoots.A1.idealExp v J = 0
  · rw [hExpJne]
    exact Nat.zero_le _
  · have hcountJne : (Associates.mk v.asIdeal).count (Associates.mk J).factors ≠ 0 := by
      simpa [ArtinPrimitiveRoots.A1.idealExp] using hExpJne
    have hJdvd : v.asIdeal ∣ J :=
      (Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mp hcountJne
    have hNrad : N ≤ J := Ideal.le_radical
    have hNle : N ≤ v.asIdeal := hNrad.trans (Ideal.dvd_iff_le.mp hJdvd)
    have hNdvd : v.asIdeal ∣ N := Ideal.dvd_iff_le.mpr hNle
    have hfacNassoc : (Associates.mk v.asIdeal).count (Associates.mk N).factors ≠ 0 :=
      (Associates.count_ne_zero_iff_dvd hN0 v.irreducible).2 hNdvd
    have hfacN : (UniqueFactorizationMonoid.normalizedFactors N).count v.asIdeal ≠ 0 := by
      rw [← Ideal.count_associates_factors_eq hN0 v.isPrime v.ne_bot]
      exact hfacNassoc
    have hcountSpan : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (n : F)) =
          (UniqueFactorizationMonoid.normalizedFactors N).count v.asIdeal := by
      rw [← FractionalIdeal.coeIdeal_span_singleton]
      exact frequency_count_coeIdeal_eq_factorCount N hN0 v
    have hcountNpos : 0 < FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (n : F)) := by
      rw [hcountSpan]
      exact_mod_cast (Nat.pos_of_ne_zero hfacN)
    have hcountIpos : 0 < FractionalIdeal.count F v
        (I.1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [← hgen.2.2 v hv]
      exact hcountNpos
    have hfacIpos : 0 < (UniqueFactorizationMonoid.normalizedFactors I.1).count v.asIdeal := by
      have hcoeI := frequency_count_coeIdeal_eq_factorCount I.1 I.2.1 v
      have hcastPos : ((UniqueFactorizationMonoid.normalizedFactors I.1).count v.asIdeal : ℤ) > 0 := by
        rw [← hcoeI]
        exact hcountIpos
      exact_mod_cast hcastPos
    have hExpIpos : 0 < ArtinPrimitiveRoots.A1.idealExp v I.1 := by
      rw [hExpI]
      exact hfacIpos
    have hExpJpos : 0 < ArtinPrimitiveRoots.A1.idealExp v J :=
      Nat.pos_iff_ne_zero.mpr hExpJne
    have hExpJone : ArtinPrimitiveRoots.A1.idealExp v J = 1 :=
      Nat.le_antisymm hExpJle (Nat.one_le_iff_ne_zero.mpr hExpJne)
    have hExpIone : 1 ≤ ArtinPrimitiveRoots.A1.idealExp v I.1 :=
      Nat.succ_le_iff.mpr hExpIpos
    rw [hExpJone]
    exact hExpIone

private theorem frequency_radical_exp_le_one
    (n : 𝓞 F) (hn : n ≠ 0) (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ArtinPrimitiveRoots.A1.idealExp v (Ideal.radical (Ideal.span {n})) ≤ 1 := by
  classical
  let N : Ideal (𝓞 F) := Ideal.span {n}
  let J : Ideal (𝓞 F) := Ideal.radical N
  have hN0 : N ≠ ⊥ := by
    intro h
    exact hn (Ideal.span_singleton_eq_bot.mp h)
  have hJ0 : J ≠ ⊥ := by
    intro h
    have hle : N ≤ J := Ideal.le_radical
    rw [h] at hle
    exact hn (Ideal.span_singleton_eq_bot.mp (bot_unique hle))
  have hJrad : J.IsRadical := Ideal.radical_isRadical N
  have hJmon : IsRadical J := by
    intro k L hdiv
    rw [Ideal.dvd_iff_le] at hdiv ⊢
    intro x hx
    exact hJrad ⟨k, hdiv (Ideal.pow_mem_pow hx k)⟩
  have hJnodup : (UniqueFactorizationMonoid.normalizedFactors J).Nodup :=
    UniqueFactorizationMonoid.normalizedFactors_nodup hJmon
  have hExpJ : ArtinPrimitiveRoots.A1.idealExp v J =
      (UniqueFactorizationMonoid.normalizedFactors J).count v.asIdeal := by
    unfold ArtinPrimitiveRoots.A1.idealExp
    rw [Ideal.count_associates_factors_eq hJ0 v.isPrime v.ne_bot]
  rw [hExpJ]
  exact (Multiset.nodup_iff_count_le_one.mp hJnodup) v.asIdeal

private theorem frequency_radical_absNorm_le
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (I : S.ExtIdeal) (n : 𝓞 F) (hn : n ≠ 0)
    (hgen : S.IsGen (n : F) I.1) :
    (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) ≤
      (∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ)) *
        (Ideal.absNorm I.1 : ℝ) := by
  classical
  let N : Ideal (𝓞 F) := Ideal.span {n}
  let J : Ideal (𝓞 F) := Ideal.radical N
  let g : ArtinPrimitiveRoots.A1.FinPlace F → ℝ := fun v =>
    (Ideal.absNorm (v.maxPowDividing J) : ℝ)
  let f : ArtinPrimitiveRoots.A1.FinPlace F → ℝ := fun v =>
    (Ideal.absNorm (v.maxPowDividing I.1) : ℝ)
  let s : ArtinPrimitiveRoots.A1.FinPlace F → ℝ := fun v =>
    if v ∈ S.Sf then (Ideal.absNorm v.asIdeal : ℝ) else 1
  have hJ0 : J ≠ ⊥ := by
    intro h
    have hle : N ≤ J := Ideal.le_radical
    rw [h] at hle
    exact hn (Ideal.span_singleton_eq_bot.mp (bot_unique hle))
  have hf : Function.HasFiniteMulSupport f :=
    ArtinPrimitiveRoots.A1.hasFiniteMulSupport_absNorm_maxPowDividing I.2.1
  have hg : Function.HasFiniteMulSupport g :=
    ArtinPrimitiveRoots.A1.hasFiniteMulSupport_absNorm_maxPowDividing hJ0
  have hsupp : Function.mulSupport s ⊆ (S.Sf : Set (ArtinPrimitiveRoots.A1.FinPlace F)) := by
    intro v hv
    by_cases hvS : v ∈ S.Sf
    · exact hvS
    · have hvone : s v = 1 := by simp [s, hvS]
      have hvne : s v ≠ 1 := by simpa [Function.mem_mulSupport] using hv
      exact (hvne hvone).elim
  have hs : Function.HasFiniteMulSupport s := S.Sf.finite_toSet.subset hsupp
  have hfs : Function.HasFiniteMulSupport (fun v => f v * s v) := by
    have hsub : Function.mulSupport (fun v => f v * s v) ⊆ f.mulSupport ∪ s.mulSupport := by
      intro v hv
      simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
      by_contra h
      have hnot : ¬ (f v ≠ 1 ∨ s v ≠ 1) := by simpa using h
      have h1 : f v = 1 := by by_contra h1; exact hnot (Or.inl h1)
      have h2 : s v = 1 := by by_contra h2; exact hnot (Or.inr h2)
      exact hv (by rw [h1, h2]; simp)
    exact (hf.union hs).subset hsub
  have hpoint : ∀ v, g v ≤ f v * s v := by
    intro v
    have hExpJle : ArtinPrimitiveRoots.A1.idealExp v J ≤ 1 := by
      simpa [J, N] using frequency_radical_exp_le_one n hn v
    have hpowNormJ : g v = (Ideal.absNorm v.asIdeal : ℝ) ^
        ArtinPrimitiveRoots.A1.idealExp v J := by
      dsimp [g]
      have hmax : v.maxPowDividing J =
          v.asIdeal ^ ArtinPrimitiveRoots.A1.idealExp v J := by
        simp [HeightOneSpectrum.maxPowDividing, ArtinPrimitiveRoots.A1.idealExp]
      rw [hmax, map_pow, Nat.cast_pow]
    have hpowNormI : f v = (Ideal.absNorm v.asIdeal : ℝ) ^
        ArtinPrimitiveRoots.A1.idealExp v I.1 := by
      dsimp [f]
      have hmax : v.maxPowDividing I.1 =
          v.asIdeal ^ ArtinPrimitiveRoots.A1.idealExp v I.1 := by
        simp [HeightOneSpectrum.maxPowDividing, ArtinPrimitiveRoots.A1.idealExp]
      rw [hmax, map_pow, Nat.cast_pow]
    have hNvNat : 1 < Ideal.absNorm v.asIdeal := HeightOneSpectrum.one_lt_absNorm v
    have hNv : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast hNvNat.le
    by_cases hvS : v ∈ S.Sf
    · have hInorm : f v = 1 := by
        dsimp [f]
        rw [ArtinPrimitiveRoots.A1.maxPowDividing_eq_one_of_mem_Sf hgen.1 hvS]
        simp
      have hExpJcases : ArtinPrimitiveRoots.A1.idealExp v J = 0 ∨
          ArtinPrimitiveRoots.A1.idealExp v J = 1 := by omega
      rcases hExpJcases with hzero | hone
      · rw [hpowNormJ, hzero, hInorm]
        simp [s, hvS]
        exact_mod_cast hNv
      · rw [hpowNormJ, hone, hInorm]
        simpa [s, hvS]
    · have hExpCompare : ArtinPrimitiveRoots.A1.idealExp v J ≤
          ArtinPrimitiveRoots.A1.idealExp v I.1 := by
        simpa [J, N] using frequency_radical_exp_le_exterior S I n hn hgen v hvS
      have hExpJcases : ArtinPrimitiveRoots.A1.idealExp v J = 0 ∨
          ArtinPrimitiveRoots.A1.idealExp v J = 1 := by omega
      rcases hExpJcases with hzero | hone
      · rw [hpowNormJ, hzero]
        simp [s, hvS]
        rw [hpowNormI]
        exact one_le_pow₀ hNv
      · have hExpIpos : 0 < ArtinPrimitiveRoots.A1.idealExp v I.1 := by omega
        have hIge : (Ideal.absNorm v.asIdeal : ℝ) ≤ f v := by
          rw [hpowNormI]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hExpIpos.ne'
          rw [hk]
          calc
            (Ideal.absNorm v.asIdeal : ℝ) = 1 * (Ideal.absNorm v.asIdeal : ℝ) := by simp
            _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k * (Ideal.absNorm v.asIdeal : ℝ) :=
              mul_le_mul_of_nonneg_right (one_le_pow₀ hNv) (by positivity)
            _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (k + 1) := by rw [pow_succ]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hExpIpos.ne'
        simpa [hpowNormJ, hone, s, hvS] using hIge
  have hnormJ : (Ideal.absNorm J : ℝ) = ∏ᶠ v, g v := by
    simpa [J, g] using
      (ArtinPrimitiveRoots.A1.absNorm_eq_finprod_absNorm_maxPowDividing hJ0)
  have hnormI : (Ideal.absNorm I.1 : ℝ) = ∏ᶠ v, f v := by
    simpa [f] using
      (ArtinPrimitiveRoots.A1.absNorm_eq_finprod_absNorm_maxPowDividing I.2.1)
  have hsprod : (∏ᶠ v, s v) = ∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [finprod_eq_finsetProd_of_mulSupport_subset s hsupp]
    simp [s]
  have hprod := finprod_le_finprod₀ hg (fun _ => by positivity) hfs hpoint
  rw [← hnormJ, finprod_mul_distrib hf hs, ← hnormI, hsprod] at hprod
  simpa [J, N, mul_comm] using hprod

private theorem frequency_conductorDvd_top
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hmc : χ.ConductorDvd (⊥ : Ideal (𝓞 F))) :
    χ.ConductorDvd (⊤ : Ideal (𝓞 F)) := by
  intro v z hz hzInv hval
  have hexp : ArtinPrimitiveRoots.A1.idealExp v (⊤ : Ideal (𝓞 F)) =
      ArtinPrimitiveRoots.A1.idealExp v (⊥ : Ideal (𝓞 F)) := by
    have htop : ArtinPrimitiveRoots.A1.idealExp v (⊤ : Ideal (𝓞 F)) = 0 := by
      unfold ArtinPrimitiveRoots.A1.idealExp
      rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
      by_cases hirr : Irreducible (Associates.mk v.asIdeal)
      · exact Associates.count_zero hirr
      · simp [Associates.count, hirr]
    have hbot : ArtinPrimitiveRoots.A1.idealExp v (⊥ : Ideal (𝓞 F)) = 0 := by
      unfold ArtinPrimitiveRoots.A1.idealExp
      rw [← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
      by_cases hirr : Irreducible v.asIdeal <;>
        simp [Associates.count, Associates.bcount, hirr]
    exact htop.trans hbot.symm
  apply hmc v z hz hzInv
  rw [← hexp]
  exact hval

private theorem frequency_conductorDvd_replace_bottom
    (χ : ArtinPrimitiveRoots.A1.HeckeChar F) (m : Ideal (𝓞 F))
    (hmc : χ.ConductorDvd m) :
    ∃ m' : Ideal (𝓞 F), m' ≠ ⊥ ∧ χ.ConductorDvd m' ∧ (m' = m ∨ m' = ⊤) := by
  by_cases hm : m = ⊥
  · subst m
    exact ⟨⊤, top_ne_bot, frequency_conductorDvd_top χ hmc, Or.inr rfl⟩
  · exact ⟨m, hm, hmc, Or.inl rfl⟩

private theorem frequency_quantitative_conductor_bounds
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H) :
    ∃ C : ℝ, 0 < C ∧
      (∀ u, ∃ f : Ideal (𝓞 F),
        IsPrimitiveConductor (frequencyOmega S D H Bd η u) f ∧
          (Ideal.absNorm f : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ)) ∧
      (∀ u,
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
          (frequencyKummer D S H Bd u).ConductorDvd m ∧
            (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ)) ∧
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
          (frequencyOmega S D H Bd η u).ConductorDvd m ∧
            (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ))) := by
  classical
  obtain ⟨C₀, hC₀⟩ := ArtinPrimitiveRoots.A1.kummer_conductor D S η
  let C₁ : ℝ := |C₀| + 1
  let C_S : ℝ := ∏ v ∈ S.Sf, (Ideal.absNorm v.asIdeal : ℝ)
  let C : ℝ := C₁ * C_S + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₁nonneg : 0 ≤ C₁ := hC₁.le
  have hC₀le : C₀ ≤ C₁ := by
    dsimp [C₁]
    nlinarith [le_abs_self C₀]
  have hCS : 0 ≤ C_S := by
    dsimp [C_S]
    exact Finset.prod_nonneg (fun v hv => by positivity)
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [mul_nonneg hC₁nonneg hCS]
  have hCge1 : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hC₁nonneg hCS]
  refine ⟨C, hCpos, ?_, ?_⟩
  · intro u
    obtain ⟨n, d, hnd⟩ := frequency_sInteger_integral_sixth_multiple S
      (frequencyRepr D S H Bd u)
    have hn0 : n ≠ 0 := by
      intro hn
      have hz := congrArg (algebraMap (𝓞 F) F) hn
      rw [map_zero] at hz
      have hprod : (frequencyRepr D S H Bd u : F) * ((d : 𝓞 F) : F) ^ 6 = 0 := by
        rw [← hnd]
        exact hz
      have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
      exact frequencyRepr_ne_zero D S H Bd u
        ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 6 hd0))
    have hnF : (n : F) ≠ 0 := by
      intro h
      exact hn0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
    let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
      (frequencyRepr_ne_zero D S H Bd u)
    let b : Fˣ := Units.mk0 (n : F) hnF
    let dUnit : Fˣ := Units.mk0 ((d : 𝓞 F) : F) (by exact_mod_cast d.property.1)
    have hdF : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
    obtain ⟨κn, hκnfin, hκnloc⟩ := ArtinPrimitiveRoots.A1.kummer_exists D S b
    have hratio : a / b = dUnit⁻¹ ^ 6 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      dsimp [a, b, dUnit]
      rw [hnd]
      field_simp [hdF, frequencyRepr_ne_zero D S H Bd u]
    have hκEq : frequencyKummer D S H Bd u = κn := by
      apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a b
        (frequencyKummer D S H Bd u) κn
        (frequencyKummer_spec D S H Bd u).2 hκnloc
        (frequencyKummer_spec D S H Bd u).1 hκnfin).2
      exact ⟨dUnit⁻¹, hratio⟩
    have hgen := frequency_integral_sixth_multiple_isGen D S H Bd u n d hnd
    have hrad := frequency_radical_absNorm_le S u.1.1 n hn0 hgen
    have hq : 1 ≤ (Ideal.absNorm u.1.1.1 : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (frequencyIndex_absNorm_pos S u)
    have hradBound : (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) ≤
        C_S * (Ideal.absNorm u.1.1.1 : ℝ) := by
      simpa [C_S] using hrad
    have hrawBound (m : Ideal (𝓞 F))
        (hm : (Ideal.absNorm m : ℝ) ≤ C₀ *
          (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ)) :
        (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      calc
        (Ideal.absNorm m : ℝ) ≤ C₀ *
            (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) := hm
        _ ≤ C₁ * (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) :=
          mul_le_mul_of_nonneg_right hC₀le (Nat.cast_nonneg _)
        _ ≤ C₁ * (C_S * (Ideal.absNorm u.1.1.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hradBound hC₁nonneg
        _ ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
          dsimp [C]
          calc
            C₁ * (C_S * (Ideal.absNorm u.1.1.1 : ℝ)) =
                (C₁ * C_S) * (Ideal.absNorm u.1.1.1 : ℝ) := by ring
            _ ≤ (C₁ * C_S + 1) * (Ideal.absNorm u.1.1.1 : ℝ) :=
              mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC₁nonneg hCS])
                (by linarith)
    have htopBound : 1 ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      calc
        1 ≤ C := hCge1
        _ = C * 1 := by ring
        _ ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) :=
          mul_le_mul_of_nonneg_left hq (le_of_lt hCpos)
    obtain ⟨mκ, hmκ, hmκbound⟩ :=
      (hC₀ n hn0 κn hκnloc hκnfin).1
    obtain ⟨mω, hmω, hmωbound⟩ :=
      (hC₀ n hn0 κn hκnloc hκnfin).2
    have hmκcond : (frequencyKummer D S H Bd u).ConductorDvd mκ := by
      simpa [hκEq] using hmκ
    have hmωcond : (frequencyOmega S D H Bd η u).ConductorDvd mω := by
      simpa [frequencyOmega, hκEq] using hmω
    obtain ⟨mκ', hmκ'0, hmκ'cond, hmκ'eq⟩ :=
      frequency_conductorDvd_replace_bottom (frequencyKummer D S H Bd u) mκ hmκcond
    obtain ⟨mω', hmω'0, hmω'cond, hmω'eq⟩ :=
      frequency_conductorDvd_replace_bottom (frequencyOmega S D H Bd η u) mω hmωcond
    have hmκ'bound : (Ideal.absNorm mκ' : ℝ) ≤
        C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      rcases hmκ'eq with hmκ'same | hmκ'top
      · rw [hmκ'same]
        exact hrawBound mκ hmκbound
      · rw [hmκ'top]
        simpa using htopBound
    have hmω'bound : (Ideal.absNorm mω' : ℝ) ≤
        C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      rcases hmω'eq with hmω'same | hmω'top
      · rw [hmω'same]
        exact hrawBound mω hmωbound
      · rw [hmω'top]
        simpa using htopBound
    obtain ⟨f, hf, hfnorm⟩ :=
      frequency_exists_minimal_conductor (frequencyOmega S D H Bd η u)
        mω' hmω'0 hmω'cond
    have hfnormR : (Ideal.absNorm f : ℝ) ≤ (Ideal.absNorm mω' : ℝ) := by
      exact_mod_cast hfnorm
    exact ⟨f, hf, hfnormR.trans hmω'bound⟩
  · intro u
    obtain ⟨n, d, hnd⟩ := frequency_sInteger_integral_sixth_multiple S
      (frequencyRepr D S H Bd u)
    have hn0 : n ≠ 0 := by
      intro hn
      have hz := congrArg (algebraMap (𝓞 F) F) hn
      rw [map_zero] at hz
      have hprod : (frequencyRepr D S H Bd u : F) * ((d : 𝓞 F) : F) ^ 6 = 0 := by
        rw [← hnd]
        exact hz
      have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
      exact frequencyRepr_ne_zero D S H Bd u
        ((mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 6 hd0))
    have hnF : (n : F) ≠ 0 := by
      intro h
      exact hn0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using h))
    let a : Fˣ := Units.mk0 (frequencyRepr D S H Bd u : F)
      (frequencyRepr_ne_zero D S H Bd u)
    let b : Fˣ := Units.mk0 (n : F) hnF
    let dUnit : Fˣ := Units.mk0 ((d : 𝓞 F) : F) (by exact_mod_cast d.property.1)
    have hdF : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast d.property.1
    obtain ⟨κn, hκnfin, hκnloc⟩ := ArtinPrimitiveRoots.A1.kummer_exists D S b
    have hratio : a / b = dUnit⁻¹ ^ 6 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val]
      dsimp [a, b, dUnit]
      rw [hnd]
      field_simp [hdF, frequencyRepr_ne_zero D S H Bd u]
    have hκEq : frequencyKummer D S H Bd u = κn := by
      apply (ArtinPrimitiveRoots.A1.kummer_eq_iff D S a b
        (frequencyKummer D S H Bd u) κn
        (frequencyKummer_spec D S H Bd u).2 hκnloc
        (frequencyKummer_spec D S H Bd u).1 hκnfin).2
      exact ⟨dUnit⁻¹, hratio⟩
    have hgen := frequency_integral_sixth_multiple_isGen D S H Bd u n d hnd
    have hrad := frequency_radical_absNorm_le S u.1.1 n hn0 hgen
    have hq : 1 ≤ (Ideal.absNorm u.1.1.1 : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (frequencyIndex_absNorm_pos S u)
    have hradBound : (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) ≤
        C_S * (Ideal.absNorm u.1.1.1 : ℝ) := by
      simpa [C_S] using hrad
    have hrawBound (m : Ideal (𝓞 F))
        (hm : (Ideal.absNorm m : ℝ) ≤ C₀ *
          (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ)) :
        (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      calc
        (Ideal.absNorm m : ℝ) ≤ C₀ *
            (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) := hm
        _ ≤ C₁ * (Ideal.absNorm (Ideal.radical (Ideal.span {n})) : ℝ) :=
          mul_le_mul_of_nonneg_right hC₀le (Nat.cast_nonneg _)
        _ ≤ C₁ * (C_S * (Ideal.absNorm u.1.1.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hradBound hC₁nonneg
        _ ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
          dsimp [C]
          calc
            C₁ * (C_S * (Ideal.absNorm u.1.1.1 : ℝ)) =
                (C₁ * C_S) * (Ideal.absNorm u.1.1.1 : ℝ) := by ring
            _ ≤ (C₁ * C_S + 1) * (Ideal.absNorm u.1.1.1 : ℝ) :=
              mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC₁nonneg hCS])
                (by linarith)
    have htopBound : 1 ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      calc
        1 ≤ C := hCge1
        _ = C * 1 := by ring
        _ ≤ C * (Ideal.absNorm u.1.1.1 : ℝ) :=
          mul_le_mul_of_nonneg_left hq (le_of_lt hCpos)
    obtain ⟨mκ, hmκ, hmκbound⟩ :=
      (hC₀ n hn0 κn hκnloc hκnfin).1
    obtain ⟨mω, hmω, hmωbound⟩ :=
      (hC₀ n hn0 κn hκnloc hκnfin).2
    have hmκcond : (frequencyKummer D S H Bd u).ConductorDvd mκ := by
      simpa [hκEq] using hmκ
    have hmωcond : (frequencyOmega S D H Bd η u).ConductorDvd mω := by
      simpa [frequencyOmega, hκEq] using hmω
    obtain ⟨mκ', hmκ'0, hmκ'cond, hmκ'eq⟩ :=
      frequency_conductorDvd_replace_bottom (frequencyKummer D S H Bd u) mκ hmκcond
    obtain ⟨mω', hmω'0, hmω'cond, hmω'eq⟩ :=
      frequency_conductorDvd_replace_bottom (frequencyOmega S D H Bd η u) mω hmωcond
    have hmκ'bound : (Ideal.absNorm mκ' : ℝ) ≤
        C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      rcases hmκ'eq with hmκ'same | hmκ'top
      · rw [hmκ'same]
        exact hrawBound mκ hmκbound
      · rw [hmκ'top]
        simpa using htopBound
    have hmω'bound : (Ideal.absNorm mω' : ℝ) ≤
        C * (Ideal.absNorm u.1.1.1 : ℝ) := by
      rcases hmω'eq with hmω'same | hmω'top
      · rw [hmω'same]
        exact hrawBound mω hmωbound
      · rw [hmω'top]
        simpa using htopBound
    exact ⟨⟨mκ', hmκ'0, hmκ'cond, hmκ'bound⟩,
      ⟨mω', hmω'0, hmω'cond, hmω'bound⟩⟩

private theorem frequencyData_of_core
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (hconductor : ∃ C : ℝ, 0 < C ∧ ∀ u,
      ∃ f : Ideal (𝓞 F), IsPrimitiveConductor (frequencyOmega S D H Bd η u) f ∧
        (Ideal.absNorm f : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ))
    (htwist : IsOfFinOrder η →
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf → η.UnramifiedAt v) →
      ∃ C : ℝ, 0 < C ∧ ∀ u,
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
          (frequencyKummer D S H Bd u).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ)) ∧
        (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
          (η * (frequencyKummer D S H Bd u)⁻¹).ConductorDvd m ∧
          (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ))) :
    Nonempty (FrequencyData S D η) := by
  classical
  refine ⟨{
    U := FrequencyIndex S
    q := fun u => (Ideal.absNorm u.1.1.1 : ℝ)
    q_pos := fun u => Nat.cast_pos.mpr (frequencyIndex_absNorm_pos S u)
    one := frequencyOne D S H Bd
    q_one := by exact_mod_cast frequencyOne_absNorm D S H Bd
    repr := frequencyRepr D S H Bd
    repr_nonzero := frequencyRepr_ne_zero D S H Bd
    q_eq_absS := fun u => (frequencyRepr_absS D S H Bd u).symm
    sixth_power_free := by
      intro u v hv
      have hgen := (frequencyRepr_isGen D S H Bd u).2.2 v hv
      constructor
      · rw [hgen]
        exact FractionalIdeal.count_coe_nonneg F v u.1.1.1
      · rw [hgen]
        exact u.1.2 v hv
    decomposition := by
      intro x hx
      obtain ⟨ui, ε, a, hgen, heq⟩ := frequency_decomposition_exists D S H Bd x hx
      refine ⟨ui, ⟨ε, a, hgen, heq⟩, ?_⟩
      intro ui' hUi'
      rcases hUi' with ⟨ε', a', hgen', heq'⟩
      exact (frequency_decomposition_unique_index D S H Bd ui ui' ε ε' a a'
        hgen hgen' x heq heq').symm
    kummer := frequencyKummer D S H Bd
    kummer_one := frequencyKummer_one D S H Bd
    kummer_principal_iff := frequencyKummer_eq_one_iff D S H Bd
    omega := frequencyOmega S D H Bd η
    omega_finiteOrder := frequencyOmega_finiteOrder S D H Bd η hη
    omega_primitive := by
      intro u
      exact frequency_omega_primitive D S H Bd η u
    omega_induces_twist := by intro u; rfl
    kummer_local := by
      intro u v hv hres
      exact (frequencyKummer_spec D S H Bd u).2 v hv hres
    kummer_primeValue_masked := by
      intro u v hv
      exact frequencyKummer_primeValue_masked D S H Bd u v hv
    q_ge_one := by
      intro u
      have hpos := frequencyIndex_absNorm_pos S u
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hpos.ne')
    dyadic_count := frequency_index_dyadic_count D S
    low_shell_bound := frequency_index_low_shell_bound D S
    kummer_injective := by
      intro u v huv
      exact frequencyKummer_injective D S H Bd huv
    omega_injective := by
      intro u v huv
      exact frequencyOmega_injective S D H Bd η huv
    conductor_bound := hconductor
    local_components_finite := frequency_local_components_finite S D H Bd η
    decomposition_surjective := frequency_decomposition_surjective D S H Bd
    kummer_twist_conductor_bound := htwist
  }⟩

/-- A1/Characters producer obligation for the complete corrected frequency dictionary
(02:285-387), including idelic induction, dyadic finiteness, and S-integer conductor bounds.
Corrected by `sol-gate-a2b`: finite order of `η` is required by the unit row. -/
theorem FrequencyData.nonempty
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (η : ArtinPrimitiveRoots.A1.HeckeChar F) (hη : IsOfFinOrder η) :
    Nonempty (FrequencyData S D η) := by
  obtain ⟨H⟩ := ArtinPrimitiveRoots.A1.HilbertData.nonempty D
  obtain ⟨Bd⟩ := ArtinPrimitiveRoots.A1.BData.nonempty D S H
  obtain ⟨C, hC, hconductor, htwistBounds⟩ :=
    frequency_quantitative_conductor_bounds S D η hη H Bd
  have htwist : IsOfFinOrder η →
      (∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf → η.UnramifiedAt v) →
        ∃ C : ℝ, 0 < C ∧ ∀ u,
          (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
            (frequencyKummer D S H Bd u).ConductorDvd m ∧
              (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ)) ∧
          (∃ m : Ideal (𝓞 F), m ≠ ⊥ ∧
            (frequencyOmega S D H Bd η u).ConductorDvd m ∧
              (Ideal.absNorm m : ℝ) ≤ C * (Ideal.absNorm u.1.1.1 : ℝ)) := by
    intro _ _
    exact ⟨C, hC, htwistBounds⟩
  exact frequencyData_of_core S D η hη H Bd ⟨C, hC, hconductor⟩ htwist

/-- The frozen A/B boundary width `δ₀ = 10⁻⁶`. -/
def a2Delta0 : ℝ := 1 / 10 ^ 6

end ArtinPrimitiveRoots.A2
