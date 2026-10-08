import ArtinPrimitiveRoots.Spec.Energy
import Mathlib.LinearAlgebra.Countable
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

set_option autoImplicit false
open NumberField Matrix MeasureTheory Filter
open scoped MatrixGroups Pointwise Topology
noncomputable section
namespace ArtinPrimitiveRoots.A1.Spec

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]

theorem localLift_countableGamma (Γ : Subgroup SL(2,𝓞 F)) : Countable Γ := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  letI : Finite (Fin 2) := inferInstance
  letI : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) := by
    change Countable (Fin 2 → Fin 2 → 𝓞 F)
    infer_instance
  have hinj : Function.Injective
      (fun γ : SL(2,𝓞 F) => (γ : Matrix (Fin 2) (Fin 2) (𝓞 F))) := by
    intro a b h
    exact Subtype.ext h
  letI : Countable (SL(2,𝓞 F)) := hinj.countable
  exact inferInstance

theorem localLift_action_measurePreserving (Γ : Subgroup SL(2,𝓞 F))
    (γ : Γ) : MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F) := by
  let g : InfinitePlace F → SL(2,ℂ) := toInf F (toSLF F γ)
  have hAct : ∀ z : X F, (γ : SL(2,𝓞 F)) • z = actAtPlaces F g z := by
    intro z
    rfl
  have hm : Measurable (fun z : X F => actAtPlaces F g z) := by
    apply measurable_pi_lambda
    intro w
    dsimp [actAtPlaces]
    exact ((OAI.CubicEisenstein.continuous_hyperbolic_action (g w)).measurable.comp
      (measurable_pi_apply w))
  refine ⟨?_, ?_⟩
  · have heq : (fun z : X F => γ • z) = fun z => actAtPlaces F g z := funext hAct
    rw [heq]
    exact hm
  · change Measure.map (fun z : X F => actAtPlaces F g z) (volX F) = volX F
    exact (G3_volume (F := F)).1 g

theorem localLift_eq_on_D (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (u : L2Space F D) :
    l2Lift F Γ D u =ᵐ[(volX F).restrict D] (u : X F → ℂ) := by
  letI : Countable Γ := localLift_countableGamma Γ
  classical
  have hno' : ∀ᵐ z ∂(volX F), ∀ γ : Γ, z ∈ D → γ ≠ 1 →
      (γ : SL(2,𝓞 F)) • z ∉ D := by
    rw [eventually_countable_forall]
    intro γ
    by_cases hγ : γ = 1
    · simp [hγ]
    · have hi : γ⁻¹ ≠ (1 : Γ) := by
        intro h
        apply hγ
        exact inv_eq_one.mp h
      have hpairwise := hD.aedisjoint
      have hpair := @hpairwise (γ⁻¹ : Γ) (1 : Γ) hi
      have hdis : AEDisjoint (volX F) ((γ⁻¹ : Γ) • D) D := by
        change AEDisjoint (volX F) ((γ⁻¹ : Γ) • D) ((1 : Γ) • D) at hpair
        simpa using hpair
      have hnot : ∀ᵐ z ∂(volX F), z ∉ ((γ⁻¹ : Γ) • D ∩ D) := by
        apply (ae_iff).2
        simpa [Set.mem_inter_iff] using hdis.eq
      filter_upwards [hnot] with z hz
      intro hzD hγ hγD
      apply hz
      constructor
      · exact (Set.mem_inv_smul_set_iff (a := γ) (A := D) (x := z)).2
          (by simpa only [Subgroup.smul_def] using hγD)
      · exact hzD
  have hno : ∀ᵐ z ∂(volX F), z ∈ D → ∀ γ : Γ, γ ≠ 1 →
      (γ : SL(2,𝓞 F)) • z ∉ D := by
    filter_upwards [hno'] with z hz hzD γ hγ
    exact hz γ hzD hγ
  have hnoD : ∀ᵐ z ∂((volX F).restrict D), ∀ γ : Γ, γ ≠ 1 →
      (γ : SL(2,𝓞 F)) • z ∉ D := by
    rw [ae_restrict_iff'₀ hD.1]
    exact hno
  filter_upwards [hnoD, ae_restrict_mem₀ hD.1] with z hzno hzD
  change (∑' γ : Γ, if (γ : SL(2,𝓞 F)) • z ∈ D then
    u ((γ : SL(2,𝓞 F)) • z) else 0) = u z
  rw [tsum_eq_single (1 : Γ) (fun γ hγ => ?_)]
  · simp [hzD]
  · have h := hzno γ hγ
    simp [h]

theorem localLift_invariant_ae_eq_of_D (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (f g : X F → ℂ)
    (hf : ∀ γ : Γ, ∀ z, f (γ • z) = f z)
    (hg : ∀ γ : Γ, ∀ z, g (γ • z) = g z)
    (hfg : f =ᵐ[(volX F).restrict D] g) : f =ᵐ[volX F] g := by
  letI : Countable Γ := localLift_countableGamma Γ
  classical
  have hfgD : ∀ᵐ z ∂(volX F), z ∈ D → f z = g z :=
    (ae_restrict_iff'₀ hD.1).mp hfg
  have hfg0 : (fun z => if z ∈ D then f z else 0) =ᵐ[volX F]
      (fun z => if z ∈ D then g z else 0) := by
    filter_upwards [hfgD] with z hz
    by_cases hmem : z ∈ D
    · simp [hmem, hz hmem]
    · simp [hmem]
  have hcomp : ∀ᵐ z ∂(volX F), ∀ γ : Γ,
      γ • z ∈ D → f (γ • z) = g (γ • z) := by
    rw [eventually_countable_forall]
    intro γ
    have hc := (hMP γ).quasiMeasurePreserving.ae_eq_comp hfg0
    filter_upwards [hc] with z hz
    intro hzD
    have hz' : (if γ • z ∈ D then f (γ • z) else 0) =
        (if γ • z ∈ D then g (γ • z) else 0) := by
      simpa only [Function.comp_apply] using hz
    simpa only [if_pos hzD] using hz'
  filter_upwards [hcomp, hD.ae_covers] with z hz ⟨γ, hγ⟩
  calc
    f z = f (γ • z) := (hf γ z).symm
    _ = g (γ • z) := hz γ hγ
    _ = g z := hg γ z

theorem localLift_add_ae (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (u v : L2Space F D) :
    l2Lift F Γ D (u + v) =ᵐ[volX F] l2Lift F Γ D u + l2Lift F Γ D v := by
  letI : Countable Γ := localLift_countableGamma Γ
  have hT1 := T1_l2 Γ D hD
  have hlocal : l2Lift F Γ D (u + v) =ᵐ[(volX F).restrict D]
      l2Lift F Γ D u + l2Lift F Γ D v := by
    filter_upwards [localLift_eq_on_D Γ D hD (u + v),
      localLift_eq_on_D Γ D hD u, localLift_eq_on_D Γ D hD v,
      Lp.coeFn_add u v] with z hsum hu hv hadd
    calc
      l2Lift F Γ D (u + v) z = (u + v) z := hsum
      _ = u z + v z := hadd
      _ = l2Lift F Γ D u z + l2Lift F Γ D v z := by rw [← hu, ← hv]
  refine localLift_invariant_ae_eq_of_D Γ D hD hMP
    (l2Lift F Γ D (u + v)) (l2Lift F Γ D u + l2Lift F Γ D v) ?_ ?_ hlocal
  · intro γ z
    exact (hT1.1 (u + v)).2 γ γ.property z
  · intro γ z
    have hu : l2Lift F Γ D u (γ • z) = l2Lift F Γ D u z := by
      simpa only [Subgroup.smul_def] using (hT1.1 u).2 (γ : SL(2,𝓞 F)) γ.property z
    have hv : l2Lift F Γ D v (γ • z) = l2Lift F Γ D v z := by
      simpa only [Subgroup.smul_def] using (hT1.1 v).2 (γ : SL(2,𝓞 F)) γ.property z
    change l2Lift F Γ D u (γ • z) + l2Lift F Γ D v (γ • z) =
      l2Lift F Γ D u z + l2Lift F Γ D v z
    rw [hu, hv]

theorem localLift_smul_ae (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (c : ℂ) (u : L2Space F D) :
    l2Lift F Γ D (c • u) =ᵐ[volX F] c • l2Lift F Γ D u := by
  letI : Countable Γ := localLift_countableGamma Γ
  have hT1 := T1_l2 Γ D hD
  have hlocal : l2Lift F Γ D (c • u) =ᵐ[(volX F).restrict D]
      c • l2Lift F Γ D u := by
    filter_upwards [localLift_eq_on_D Γ D hD (c • u),
      localLift_eq_on_D Γ D hD u, Lp.coeFn_smul c u] with z hcu hu hsmul
    calc
      l2Lift F Γ D (c • u) z = (c • u) z := hcu
      _ = c • u z := hsmul
      _ = c • l2Lift F Γ D u z := by rw [← hu]
  refine localLift_invariant_ae_eq_of_D Γ D hD hMP
    (l2Lift F Γ D (c • u)) (c • l2Lift F Γ D u) ?_ ?_ hlocal
  · intro γ z
    exact (hT1.1 (c • u)).2 γ γ.property z
  · intro γ z
    have hu : l2Lift F Γ D u (γ • z) = l2Lift F Γ D u z := by
      simpa only [Subgroup.smul_def] using (hT1.1 u).2 (γ : SL(2,𝓞 F)) γ.property z
    change c • l2Lift F Γ D u (γ • z) = c • l2Lift F Γ D u z
    rw [hu]

theorem localLift_simple_memLp (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (W : Set (X F)) (hW : IsCompact W)
    (f : Lp.simpleFunc ℂ 2 ((volX F).restrict D)) :
    MemLp (l2Lift F Γ D (f : L2Space F D)) 2 ((volX F).restrict W) := by
  letI : Countable Γ := localLift_countableGamma Γ
  classical
  let u : L2Space F D := (f : L2Space F D)
  let s := Lp.simpleFunc.toSimpleFunc f
  let C : ℝ := ∑ c ∈ s.range, ‖c‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun c hc => norm_nonneg c
  have hsBound (z : X F) : ‖s z‖ ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun c hc => norm_nonneg c) (s.mem_range_self z)
  have hT1 := T1_l2 Γ D hD
  have hlocal : ∀ᵐ z ∂((volX F).restrict D), ‖l2Lift F Γ D u z‖ ≤ C := by
    filter_upwards [localLift_eq_on_D Γ D hD u, Lp.simpleFunc.toSimpleFunc_eq_toFun f]
      with z hlift hs
    rw [hlift, ← hs]
    exact hsBound z
  have hlocalAll : ∀ᵐ z ∂(volX F), z ∈ D → ‖l2Lift F Γ D u z‖ ≤ C :=
    (ae_restrict_iff'₀ hD.1).mp hlocal
  have hboundAllGamma : ∀ᵐ z ∂(volX F), ∀ γ : Γ,
      γ • z ∈ D → ‖l2Lift F Γ D u (γ • z)‖ ≤ C := by
    rw [eventually_countable_forall]
    intro γ
    have hc := (hMP γ).quasiMeasurePreserving.ae hlocalAll
    filter_upwards [hc] with z hz
    intro hzD
    exact hz hzD
  have hbound : ∀ᵐ z ∂(volX F), ‖l2Lift F Γ D u z‖ ≤ C := by
    filter_upwards [hboundAllGamma, hD.ae_covers] with z hz ⟨γ, hγ⟩
    have hinv : l2Lift F Γ D u (γ • z) = l2Lift F Γ D u z := by
      simpa only [Subgroup.smul_def] using (hT1.1 u).2 (γ : SL(2,𝓞 F)) γ.property z
    calc
      ‖l2Lift F Γ D u z‖ = ‖l2Lift F Γ D u (γ • z)‖ := by rw [hinv]
      _ ≤ C := hz γ hγ
  have hSM : AEStronglyMeasurable (l2Lift F Γ D u) ((volX F).restrict W) :=
    (hT1.1 u).1.mono_ac Measure.restrict_le_self.absolutelyContinuous
  have hWvol : volX F W < ⊤ := (G3_volume (F := F)).2.2.1 W hW
  letI : IsFiniteMeasure ((volX F).restrict W) := ⟨by
    simpa [Measure.restrict_apply MeasurableSet.univ] using hWvol⟩
  exact MemLp.of_bound hSM C (hbound.filter_mono ae_restrict_le)


theorem localLift_simple_norm_eq_sqrt (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F))
    (W : Set (X F)) (hW : IsCompact W)
    (f : Lp.simpleFunc ℂ 2 ((volX F).restrict D)) :
    ‖MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
      (localLift_simple_memLp Γ D hD hMP W hW f)‖ =
      Real.sqrt (∫ z in W, ‖l2Lift F Γ D (f : L2Space F D) z‖ ^ 2 ∂(volX F)) := by
  letI : Countable Γ := localLift_countableGamma Γ
  have hmem := localLift_simple_memLp Γ D hD hMP W hW f
  rw [Lp.norm_toLp]
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hI : 0 ≤ ∫ z in W, ‖l2Lift F Γ D (f : L2Space F D) z‖ ^ 2 ∂(volX F) := by
    exact integral_nonneg fun z => sq_nonneg _
  rw [ENNReal.toReal_ofReal]
  · rw [Real.sqrt_eq_rpow]
    congr 1
    all_goals
      first | rfl | norm_num [ENNReal.toReal_ofNat]
  · positivity


theorem localLiftCLM_impl (Γ : Subgroup SL(2,𝓞 F)) [Γ.FiniteIndex]
    (D : Set (X F)) (hD : IsFundamentalDomain Γ D (volX F))
    (W : Set (X F)) (hW : IsCompact W) :
    ∃ T : L2Space F D →L[ℂ] Lp ℂ 2 ((volX F).restrict W),
      ‖T‖ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) ∧
        ∀ u, ∀ᵐ z ∂((volX F).restrict W), T u z = l2Lift F Γ D u z := by
  letI : Countable Γ := localLift_countableGamma Γ
  let hMP : ∀ γ : Γ, MeasurePreserving (fun z : X F => γ • z) (volX F) (volX F) :=
    localLift_action_measurePreserving Γ
  letI : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : SMul ℂ (Lp.simpleFunc ℂ 2 ((volX F).restrict D)) :=
    Lp.simpleFunc.smul
  letI : Module ℂ (Lp.simpleFunc ℂ 2 ((volX F).restrict D)) :=
    Lp.simpleFunc.module
  letI : NormedSpace ℂ (Lp.simpleFunc ℂ 2 ((volX F).restrict D)) :=
    Lp.simpleFunc.normedSpace
  let μD := (volX F).restrict D
  let μW := (volX F).restrict W
  let e : Lp.simpleFunc ℂ 2 μD →L[ℂ] Lp ℂ 2 μD :=
    Lp.simpleFunc.coeToLp (X F) ℂ ℂ
  let Tlin : Lp.simpleFunc ℂ 2 μD →ₗ[ℂ] Lp ℂ 2 μW := {
    toFun := fun f => MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
      (localLift_simple_memLp Γ D hD hMP W hW f)
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [
        MemLp.coeFn_toLp (localLift_simple_memLp Γ D hD hMP W hW (f + g)),
        MemLp.coeFn_toLp (localLift_simple_memLp Γ D hD hMP W hW f),
        MemLp.coeFn_toLp (localLift_simple_memLp Γ D hD hMP W hW g),
        Lp.coeFn_add
          (MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
            (localLift_simple_memLp Γ D hD hMP W hW f))
          (MemLp.toLp (l2Lift F Γ D (g : L2Space F D))
            (localLift_simple_memLp Γ D hD hMP W hW g)),
        (localLift_add_ae Γ D hD hMP (f : L2Space F D) (g : L2Space F D)).filter_mono
          ae_restrict_le] with z hsum hf hg haddOut hadd
      calc
        MemLp.toLp (l2Lift F Γ D ((f + g : Lp.simpleFunc ℂ 2 μD) : L2Space F D))
            (localLift_simple_memLp Γ D hD hMP W hW (f + g)) z =
            l2Lift F Γ D ((f + g : Lp.simpleFunc ℂ 2 μD) : L2Space F D) z := hsum
        _ = l2Lift F Γ D (f : L2Space F D) z + l2Lift F Γ D (g : L2Space F D) z := by
          simpa only [AddSubgroup.coe_add, Pi.add_apply] using hadd
        _ = (MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
              (localLift_simple_memLp Γ D hD hMP W hW f) +
            MemLp.toLp (l2Lift F Γ D (g : L2Space F D))
              (localLift_simple_memLp Γ D hD hMP W hW g)) z := by
                rw [← hf, ← hg]
                exact haddOut.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [
        MemLp.coeFn_toLp (localLift_simple_memLp Γ D hD hMP W hW (c • f)),
        MemLp.coeFn_toLp (localLift_simple_memLp Γ D hD hMP W hW f),
        Lp.coeFn_smul c (MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
          (localLift_simple_memLp Γ D hD hMP W hW f)),
        (localLift_smul_ae Γ D hD hMP c (f : L2Space F D)).filter_mono ae_restrict_le]
        with z hcf hf hsmulOut hsmul
      calc
        MemLp.toLp (l2Lift F Γ D ((c • f : Lp.simpleFunc ℂ 2 μD) : L2Space F D))
            (localLift_simple_memLp Γ D hD hMP W hW (c • f)) z =
            l2Lift F Γ D ((c • f : Lp.simpleFunc ℂ 2 μD) : L2Space F D) z := hcf
        _ = c • l2Lift F Γ D (f : L2Space F D) z := by
          simpa only [Lp.simpleFunc.coe_smul, Pi.smul_apply] using hsmul
        _ = (c • MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
              (localLift_simple_memLp Γ D hD hMP W hW f)) z := by
                rw [← hf]
                exact hsmulOut.symm
  }
  have hTlinBound (f : Lp.simpleFunc ℂ 2 μD) :
      ‖Tlin f‖ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖f‖ := by
    change ‖MemLp.toLp (l2Lift F Γ D (f : L2Space F D))
      (localLift_simple_memLp Γ D hD hMP W hW f)‖ ≤ _
    rw [localLift_simple_norm_eq_sqrt Γ D hD hMP W hW f]
    have hT1 := T1_l2 Γ D hD
    have hbound := (hT1.2.1 W hW).2 (f : L2Space F D)
    calc
      Real.sqrt (∫ z in W, ‖l2Lift F Γ D (f : L2Space F D) z‖ ^ 2 ∂(volX F)) ≤
          Real.sqrt ((overlapMultiplicity F Γ W : ℝ) * ‖(f : L2Space F D)‖ ^ 2) :=
        Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (overlapMultiplicity F Γ W : ℝ) * ‖f‖ := by
        simp [Real.sqrt_mul, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)]
  let S : Lp.simpleFunc ℂ 2 μD →L[ℂ] Lp ℂ 2 μW := Tlin.mkContinuous
    (Real.sqrt (overlapMultiplicity F Γ W : ℝ)) hTlinBound
  have hSbound : ‖S‖ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) :=
    LinearMap.mkContinuous_norm_le Tlin (Real.sqrt_nonneg _) hTlinBound
  have heDense : DenseRange e := by
    change DenseRange (fun f : Lp.simpleFunc ℂ 2 μD => (f : Lp ℂ 2 μD))
    exact Lp.simpleFunc.denseRange (by norm_num)
  have heUniform : IsUniformInducing e := by
    change IsUniformInducing (fun f : Lp.simpleFunc ℂ 2 μD => (f : Lp ℂ 2 μD))
    exact Lp.simpleFunc.isUniformInducing
  let T : Lp ℂ 2 μD →L[ℂ] Lp ℂ 2 μW := S.extend e
  have heBound : ∀ f : Lp.simpleFunc ℂ 2 μD,
      ‖f‖ ≤ (1 : NNReal) * ‖e f‖ := by
    intro f
    change ‖f‖ ≤ 1 * ‖(f : Lp ℂ 2 μD)‖
    simp
  have hTbound : ‖T‖ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) := by
    calc
      ‖S.extend e‖ ≤ (1 : NNReal) * ‖S‖ :=
        ContinuousLinearMap.opNorm_extend_le (f := S) (e := e) (N := (1 : NNReal))
          heDense heBound
      _ = ‖S‖ := by simp
      _ ≤ Real.sqrt (overlapMultiplicity F Γ W : ℝ) := hSbound
  refine ⟨T, hTbound, ?_⟩
  intro u
  have happrox (n : ℕ) : ∃ f : Lp.simpleFunc ℂ 2 μD,
      dist u (e f) < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact heDense.exists_dist_lt u hε
  choose fseq hfseq using happrox
  have hseq : Filter.Tendsto (fun n => e (fseq n)) atTop (𝓝 u) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, ?_⟩
    intro n hn
    calc
      dist (e (fseq n)) u = dist u (e (fseq n)) := dist_comm _ _
      _ < 1 / ((n : ℝ) + 1) := hfseq n
      _ ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact_mod_cast Nat.add_le_add_right hn 1
      _ < ε := hN
  have hTseq : Filter.Tendsto (fun n => T (e (fseq n))) atTop (𝓝 (T u)) :=
    (T.continuous.tendsto u).comp hseq
  have hOutIM := tendstoInMeasure_of_tendsto_Lp hTseq
  obtain ⟨ns, hns, hOutAE⟩ := hOutIM.exists_seq_tendsto_ae
  have hInSeq : Filter.Tendsto (fun k => e (fseq (ns k))) atTop (𝓝 u) :=
    hseq.comp hns.tendsto_atTop
  have hInIM := tendstoInMeasure_of_tendsto_Lp hInSeq
  obtain ⟨ms, hms, hInAE⟩ := hInIM.exists_seq_tendsto_ae
  let uSeq : ℕ → L2Space F D := fun j => e (fseq (ns (ms j)))
  have hOutAE' : ∀ᵐ z ∂μW,
      Filter.Tendsto (fun j => T (e (fseq (ns (ms j)))) z) atTop (𝓝 (T u z)) := by
    filter_upwards [hOutAE] with z hz
    exact hz.comp hms.tendsto_atTop
  have hSeqRep : ∀ᵐ z ∂μD, ∀ j, l2Lift F Γ D (uSeq j) z = uSeq j z := by
    rw [eventually_countable_forall]
    intro j
    exact localLift_eq_on_D Γ D hD (uSeq j)
  have hRepU : l2Lift F Γ D u =ᵐ[μD] (u : X F → ℂ) :=
    localLift_eq_on_D Γ D hD u
  have hInputAE : ∀ᵐ z ∂μD,
      Filter.Tendsto (fun j => uSeq j z) atTop (𝓝 ((u : X F → ℂ) z)) := by
    exact hInAE
  have hconvD : ∀ᵐ z ∂μD,
      Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) z) atTop
        (𝓝 (l2Lift F Γ D u z)) := by
    filter_upwards [hSeqRep, hRepU, hInputAE] with z hrep huRep hconv
    have hfun : (fun j => l2Lift F Γ D (uSeq j) z) = fun j => uSeq j z :=
      funext hrep
    rw [hfun, huRep]
    exact hconv
  have hconvCond : ∀ᵐ z ∂(volX F), z ∈ D →
      Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) z) atTop
        (𝓝 (l2Lift F Γ D u z)) :=
    (ae_restrict_iff'₀ hD.1).mp hconvD
  have hT1 := T1_l2 Γ D hD
  have hconvAll : ∀ᵐ z ∂(volX F),
      Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) z) atTop
        (𝓝 (l2Lift F Γ D u z)) := by
    have hconvGamma : ∀ᵐ z ∂(volX F), ∀ γ : Γ,
        γ • z ∈ D →
          Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) (γ • z)) atTop
            (𝓝 (l2Lift F Γ D u (γ • z))) := by
      rw [eventually_countable_forall]
      intro γ
      exact (hMP γ).quasiMeasurePreserving.ae hconvCond
    filter_upwards [hconvGamma, hD.ae_covers] with z hγ ⟨γ, hγD⟩
    have hseq := hγ γ hγD
    have hfun : (fun j => l2Lift F Γ D (uSeq j) z) =
        fun j => l2Lift F Γ D (uSeq j) (γ • z) := by
      funext j
      exact ((hT1.1 (uSeq j)).2 (γ : SL(2,𝓞 F)) γ.property z).symm
    have hlim : l2Lift F Γ D u z = l2Lift F Γ D u (γ • z) :=
      ((hT1.1 u).2 (γ : SL(2,𝓞 F)) γ.property z).symm
    rw [← hfun, ← hlim] at hseq
    exact hseq
  have hconvW : ∀ᵐ z ∂μW,
      Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) z) atTop
        (𝓝 (l2Lift F Γ D u z)) := hconvAll.filter_mono ae_restrict_le
  have hRepOut : ∀ᵐ z ∂μW, ∀ j,
      T (e (fseq (ns (ms j)))) z = l2Lift F Γ D (uSeq j) z := by
    rw [eventually_countable_forall]
    intro j
    let hf := fseq (ns (ms j))
    have hmem := localLift_simple_memLp Γ D hD hMP W hW hf
    have hext := ContinuousLinearMap.extend_eq S heDense heUniform hf
    filter_upwards [MemLp.coeFn_toLp hmem] with z hz
    calc
      T (e (fseq (ns (ms j)))) z = S hf z := congrArg (fun q : Lp ℂ 2 μW => q z) hext
      _ = l2Lift F Γ D (uSeq j) z := by
        simpa [S, Tlin, uSeq, e, Lp.simpleFunc.coeToLp] using hz
  filter_upwards [hOutAE', hconvW, hRepOut] with z hout hconv hrep
  have hEqSeq : (fun j : ℕ => T (e (fseq (ns (ms j)))) z) =ᶠ[atTop]
      fun j => l2Lift F Γ D (uSeq j) z := by
    exact Filter.Eventually.of_forall (fun j => hrep j)
  have houtLift : Filter.Tendsto (fun j => l2Lift F Γ D (uSeq j) z) atTop
      (𝓝 (T u z)) := Filter.Tendsto.congr' hEqSeq hout
  exact tendsto_nhds_unique houtLift hconv

end ArtinPrimitiveRoots.A1.Spec
