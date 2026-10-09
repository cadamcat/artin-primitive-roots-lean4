import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

set_option autoImplicit false
set_option maxHeartbeats 20000000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

private theorem e_e_product_majorant_exceptions (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (η : HeckeChar F) (U : FrequencyData S D η) (C Q0 : ℝ)
    (u : U.U) (hQ0 : 1 < Q0) :
    Summable (fun v : ExteriorPrime S =>
      C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ)) ∧
    {v : ExteriorPrime S |
      qI v.1.asIdeal ≤ Q0 ∨ frequencyValuation η U u v.1 ≠ 0}.Finite := by
  classical
  let σ : ℝ := 1 + 1 / 4000
  have hsumIdeal : Summable (fun I : S.ExtIdeal =>
      Real.rpow (idealNorm I.1) (-σ)) :=
    a2_bridge_COUNT_summable S σ (by dsimp [σ]; norm_num)
  let primeMap : ExteriorPrime S → S.ExtIdeal := fun v => R.exterior.prime v.1 v.2
  have hprimeMap : Function.Injective primeMap := by
    intro v w hvw
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    have hvw' := congrArg (fun I : S.ExtIdeal => I.1) hvw
    simpa [primeMap, R.exterior.prime_val] using hvw'
  have hIdealNonneg (I : S.ExtIdeal) :
      0 ≤ Real.rpow (idealNorm I.1) (-σ) := by
    apply Real.rpow_nonneg
    dsimp [idealNorm]
    exact_mod_cast Nat.zero_le (Ideal.absNorm I.1)
  have hsumIdealNN : Summable (fun I : S.ExtIdeal =>
      (⟨Real.rpow (idealNorm I.1) (-σ), hIdealNonneg I⟩ : NNReal)) :=
    (NNReal.summable_mk hIdealNonneg).2 hsumIdeal
  have hsumPrime : Summable (fun v : ExteriorPrime S =>
      Real.rpow (qI v.1.asIdeal) (-σ)) := by
    have hbase : Summable (fun v : ExteriorPrime S =>
        ((⟨Real.rpow (idealNorm (primeMap v).1) (-σ),
          hIdealNonneg (primeMap v)⟩ : NNReal) : ℝ)) :=
      (NNReal.summable_coe).2
        (NNReal.summable_comp_injective hsumIdealNN hprimeMap)
    exact hbase.congr fun v => by
      simp [primeMap, idealNorm, qI, R.exterior.prime_val]
  have hexp : -σ = (-1 - 1 / 4000 : ℝ) := by
    dsimp [σ]
    ring
  have hmajor : Summable (fun v : ExteriorPrime S =>
      C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ)) := by
    simpa only [hexp] using hsumPrime.mul_left C

  have hlow : {v : ExteriorPrime S | qI v.1.asIdeal ≤ Q0}.Finite := by
    have hfinite : {I : S.ExtIdeal | idealNorm I.1 ≤ Q0}.Finite :=
      (a2_bridge_COUNT_finite S Q0 (le_of_lt (lt_trans (by norm_num) hQ0))).1
    have hpre := hfinite.preimage_embedding ⟨primeMap, hprimeMap⟩
    simpa [primeMap, idealNorm, qI, R.exterior.prime_val] using hpre
  have hbad : {v : ExteriorPrime S |
      frequencyValuation η U u v.1 ≠ 0}.Finite := by
    let I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F)
    have hcofinite : ∀ᶠ v : FinPlace F in Filter.cofinite,
        FractionalIdeal.count F v I = 0 := FractionalIdeal.finite_factors I
    have hcount : {v : FinPlace F | FractionalIdeal.count F v I ≠ 0}.Finite :=
      (Filter.eventually_cofinite).mp hcofinite
    have hcount' : {v : ExteriorPrime S |
        FractionalIdeal.count F v.1 I ≠ 0}.Finite :=
      hcount.preimage_embedding ⟨fun v : ExteriorPrime S => v.1, Subtype.val_injective⟩
    refine hcount'.subset ?_
    intro v hv
    change frequencyValuation η U u v.1 ≠ 0 at hv
    change FractionalIdeal.count F v.1 I ≠ 0
    intro hzero
    apply hv
    simp [frequencyValuation, I, hzero]
  exact ⟨hmajor, hlow.union hbad⟩

private theorem e_e_product_deviation_bound
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (C Q0 : ℝ)
    (hbnd : ∀ u v hv p, Q0 < qI v.asIdeal → eulerNeighborhood p →
      Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
        ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖) ∧
      ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
        C * qI v.asIdeal ^
          (if frequencyValuation η U u v = 0 then
            (-1 - 1 / 4000 : ℝ) else (-1 / 4000 : ℝ)))
    (u : U.U) (K : Set Triple) (hKsub : K ⊆ {p | eulerNeighborhood p})
    (hexceptional : {v : ExteriorPrime S |
      qI v.1.asIdeal ≤ Q0 ∨ frequencyValuation η U u v.1 ≠ 0}.Finite) :
    ∀ᶠ v : ExteriorPrime S in Filter.cofinite,
      ∀ p ∈ K, ‖normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1‖ ≤
        C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ) := by
  classical
  filter_upwards [hexceptional.eventually_cofinite_notMem] with v hv
  intro p hp
  have hQ : Q0 < qI v.1.asIdeal := lt_of_not_ge (fun h => hv (Or.inl h))
  have hfreq : frequencyValuation η U u v.1 = 0 := by
    by_contra h
    exact hv (Or.inr h)
  have hbound := (hbnd u v.1 v.2 p hQ (hKsub hp)).2
  rw [if_pos hfreq] at hbound
  exact hbound

private theorem e_e_product_uniform_on_compact
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (u : U.U) (K : Set Triple)
    (hbase : HasProdUniformlyOn
      (fun v : ExteriorPrime S => fun p : Triple =>
        1 + (normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1))
      (fun p => ∏' v : ExteriorPrime S,
        (1 + (normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1))) K) :
    HasProdUniformlyOn
      (fun v : ExteriorPrime S => fun p : Triple =>
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2))
      (fun p => ∏' v : ExteriorPrime S,
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) K := by
  classical
  have hfactor (v : ExteriorPrime S) (p : Triple) :
      1 + (normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1) =
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) := by ring
  convert hbase using 1
  · funext v p
    simp only [hfactor]
  · funext p
    exact congrArg (fun g : ExteriorPrime S → ℂ => ∏' v, g v)
      (funext fun v => by simp only [hfactor])

private theorem e_e_product_base_uniform
    (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (C : ℝ) (u : U.U) (K : Set Triple)
    (hK : IsCompact K) (hKsub : K ⊆ {p | eulerNeighborhood p})
    (hdeviationBound : ∀ᶠ v : ExteriorPrime S in Filter.cofinite,
      ∀ p ∈ K, ‖normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1‖ ≤
        C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ))
    (hlocal : ∀ u v hv, DifferentiableOn ℂ (fun p : Triple =>
      normalizedLocal R η U u v hv (p 0) (p 1) (p 2))
        {p | eulerNeighborhood p})
    (hmajor : Summable (fun v : ExteriorPrime S =>
      C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ))) :
    HasProdUniformlyOn
      (fun v : ExteriorPrime S => fun p : Triple =>
        1 + (normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1))
      (fun p => ∏' v : ExteriorPrime S,
        (1 + (normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1))) K := by
  have hcontinuous : ∀ v : ExteriorPrime S,
      ContinuousOn (fun p : Triple =>
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1) K := by
    intro v
    have hcont := (hlocal u v.1 v.2).continuousOn
    exact (hcont.mono hKsub).sub continuousOn_const
  let f : ExteriorPrime S → Triple → ℂ := fun v p =>
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1
  exact Summable.hasProdUniformlyOn_one_add (f := f)
    (u := fun v : ExteriorPrime S => C * Real.rpow (qI v.1.asIdeal) (-1 - 1 / 4000 : ℝ))
    (K := K) hK hmajor hdeviationBound hcontinuous

theorem product_compact (HC : EulerCorrection R η U) (C Q0 : ℝ)
    (hE : EulerHypotheses R η)
    (hb : HasPoHLocalBounds R η U C Q0)
    (hlocal : ∀ u v hv, DifferentiableOn ℂ (fun p : Triple =>
      normalizedLocal R η U u v hv (p 0) (p 1) (p 2)) {p | eulerNeighborhood p}) :
    ∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
      ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F), V ⊆ V' →
        ∀ p ∈ K, ‖(∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
          normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) - HC.H u p‖ < ε := by
  classical
  intro u K hK hKsub ε hε
  rcases hb with ⟨hC, hQ0, hbnd⟩
  obtain ⟨hmajor, hexceptional⟩ :=
    e_e_product_majorant_exceptions R η U C Q0 u hQ0
  have hdeviationBound :=
    e_e_product_deviation_bound R η U C Q0 hbnd u K hKsub hexceptional
  have hbase := e_e_product_base_uniform R η U C u K hK hKsub
    hdeviationBound hlocal hmajor
  have hprod := e_e_product_uniform_on_compact R η U u K hbase

  have hconv := hprod.tendstoUniformlyOn
  have hconv' := (Filter.HasBasis.tendstoUniformlyOn_iff
    (Filter.atTop_basis (α := Finset (ExteriorPrime S)))
    (Metric.uniformity_basis_dist (α := ℂ))).1 hconv
  obtain ⟨W, -, hW⟩ := hconv' ε hε
  let emb : ExteriorPrime S ↪ FinPlace F := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨W.map emb, ?_⟩
  intro V' hVV' p hp
  let W' : Finset (ExteriorPrime S) := V'.subtype (fun v : FinPlace F => v ∉ S.Sf)
  have hWW' : W ⊆ W' := by
    intro v hv
    have hvV : v.1 ∈ V' := hVV' (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    simpa [W', Finset.mem_subtype] using hvV
  have happrox := hW (show W' ∈ Set.Ici W from hWW') p hp
  change dist
    (∏' v : ExteriorPrime S,
      normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2))
    (∏ v ∈ W', normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) < ε at happrox
  have hfiniteProduct :
      (∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
        normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) =
      ∏ v ∈ W', normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) := by
    let g : FinPlace F → ℂ := fun v =>
      if hv : v ∉ S.Sf then normalizedLocal R η U u v hv (p 0) (p 1) (p 2) else 1
    calc
      _ = ∏ v ∈ V'.attach, g v.1 := by
        apply Finset.prod_congr rfl
        intro v hv
        by_cases h : v.1 ∈ S.Sf <;> simp [g, h]
      _ = ∏ v ∈ V', g v := Finset.prod_attach V' g
      _ = ∏ v ∈ V' with v ∉ S.Sf, g v := by
        symm
        rw [Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro v hv
        by_cases h : v ∈ S.Sf <;> simp [g, h]
      _ = ∏ v ∈ W', g v.1 := by
        symm
        simpa [W'] using
          (Finset.prod_subtype_eq_prod_filter (s := V')
            (p := fun v : FinPlace F => v ∉ S.Sf) (f := g))
      _ = ∏ v ∈ W', normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) := by
        apply Finset.prod_congr rfl
        intro v hv
        simp [g, v.2]
  have hH : HC.H u p = ∏' v : ExteriorPrime S,
      normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) := by
    simpa using HC.H_eq u p
  rw [hfiniteProduct, hH]
  simpa [dist_eq_norm, norm_sub_rev] using happrox

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
