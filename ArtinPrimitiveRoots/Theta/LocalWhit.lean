import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.Theta.Proofs.TH_WHITTAKER.Bruhat

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.Proofs.TH_WHITTAKER

variable {F : Type} [Field F] [NumberField F]

/-! ## P-LOCAL-WHIT -/

section LocalWhit

open MeasureTheory Filter MonoidWithZeroHom

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The space of sections of `I(T, s)` (def:ind as a subspace). -/
def sectionSpace (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) :
    Submodule ℂ (L.L → T.V) where
  carrier := {f | IsSection L T s f}
  add_mem' := by
    intro f g hf hg
    change IsSection L T s f at hf
    change IsSection L T s g at hg
    rcases hf with ⟨hf₁, hf₂, mf, hmf, hfr⟩
    rcases hg with ⟨hg₁, hg₂, mg, hmg, hgr⟩
    refine ⟨?_, ?_, max mf mg, le_trans hmf (Nat.le_max_left _ _), ?_⟩
    · intro x y h
      simp only [Pi.add_apply, hf₁, hg₁, map_add, smul_add]
    · intro ζ h
      calc
        (f + g) (L.z ζ * h) = f (L.z ζ * h) + g (L.z ζ * h) := rfl
        _ = ((ζ : ℂˣ) : ℂ) • f h + ((ζ : ℂˣ) : ℂ) • g h := by rw [hf₂, hg₂]
        _ = ((ζ : ℂˣ) : ℂ) • (f h + g h) := (smul_add _ _ _).symm
    · intro h k hk
      have hkf : k ∈ L.Kc mf := L.Kc_anti mf (max mf mg) hmf
        (Nat.le_max_left _ _) hk
      have hkg : k ∈ L.Kc mg := L.Kc_anti mg (max mf mg) hmg
        (Nat.le_max_right _ _) hk
      simp [Pi.add_apply, hfr h k hkf, hgr h k hkg]
  zero_mem' := by
    refine ⟨?_, ?_, L.m0, le_rfl, ?_⟩
    · intro x y g
      simp
    · intro ζ g
      simp
    · intro g k hk
      simp
  smul_mem' := by
    intro c f hf
    change IsSection L T s f at hf
    rcases hf with ⟨hf₁, hf₂, m, hm, hfr⟩
    refine ⟨?_, ?_, m, hm, ?_⟩
    · intro x y g
      change c • f (L.n (Multiplicative.ofAdd x) * L.a y * g) =
        ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (c • f g)
      rw [hf₁, map_smul]
      exact smul_comm c ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) (T.σa y (f g))
    · intro ζ g
      change c • f (L.z ζ * g) = ((ζ : ℂˣ) : ℂ) • (c • f g)
      rw [hf₂]
      exact smul_comm c ((ζ : ℂˣ) : ℂ) (f g)
    · intro g k hk
      simp [Pi.smul_apply, hfr g k hk]

/-- A subspace of functions stable under right translation. -/
def IsRtrStable {L : FinLocalCover D H v} {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (L.L → V)) : Prop :=
  ∀ f ∈ W, ∀ g : L.L, rtr g f ∈ W

/-- **def:whittaker**: a Whittaker functional with character `ψ_v` on a subspace `W`. -/
def IsWhittakerOn (L : FinLocalCover D H v) (A : AddCharData F) {V : Type} [AddCommGroup V]
    [Module ℂ V] (W : Submodule ℂ (L.L → V)) (Λ : (L.L → V) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f ∈ W, ∀ t : v.adicCompletion F, Λ (rtr (L.n (Multiplicative.ofAdd t)) f) = A.ψ v t * Λ f

private theorem wh_ball_subset_nhds (x : v.adicCompletion F) {U : Set (v.adicCompletion F)}
    (hU : U ∈ nhds x) : ∃ m : ℕ, ∀ t ∈ ball v (m : ℤ), x + t ∈ U := by
  let K := v.adicCompletion F
  obtain ⟨γ, hγ⟩ :=
    (Valued.mem_nhds (R := K) (Γ₀ := WithZero (Multiplicative ℤ))).mp hU
  let γv : WithZero (Multiplicative ℤ) :=
    ValueGroup₀.embedding (f := (.ofClass (Valued.v : Valuation K _))) γ.1
  have hγv : γv ≠ 0 := by
    intro h
    have heq : ValueGroup₀.embedding (f := (.ofClass (Valued.v : Valuation K _))) γ.1 =
        ValueGroup₀.embedding (f := (.ofClass (Valued.v : Valuation K _))) 0 := by
      simpa [γv] using h
    exact (Units.ne_zero γ) (ValueGroup₀.embedding_injective heq)
  obtain ⟨m, hm⟩ := WithZero.exists_exp_neg_natCast_lt hγv
  refine ⟨m, ?_⟩
  intro t ht
  apply hγ
  change Valued.v.restrict ((x + t) - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  change Valued.v ((x + t) - x) < γv
  rw [show (x + t) - x = t by abel]
  exact lt_of_le_of_lt (by simpa [ball] using ht) hm

private theorem wh_ball_anti {i j : ℤ} (hij : i ≤ j) {x : v.adicCompletion F}
    (hx : x ∈ ball v j) : x ∈ ball v i := by
  change Valued.v x ≤ WithZero.exp (-j) at hx
  change Valued.v x ≤ WithZero.exp (-i)
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem wh_ball_add {i : ℤ} {x y : v.adicCompletion F}
    (hx : x ∈ ball v i) (hy : y ∈ ball v i) : x + y ∈ ball v i := by
  change Valued.v x ≤ WithZero.exp (-i) at hx
  change Valued.v y ≤ WithZero.exp (-i) at hy
  change Valued.v (x + y) ≤ WithZero.exp (-i)
  exact Valuation.map_add_le _ hx hy

private theorem wh_ball_neg {i : ℤ} {x : v.adicCompletion F}
    (hx : x ∈ ball v i) : -x ∈ ball v i := by
  change Valued.v x ≤ WithZero.exp (-i) at hx
  change Valued.v (-x) ≤ WithZero.exp (-i)
  simpa using hx

private theorem wh_ball_isOpen (i : ℤ) : IsOpen (ball v i) := by
  change IsOpen {x : v.adicCompletion F | Valued.v x ≤ WithZero.exp (-i)}
  exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero

private theorem wh_ball_compact (m : ℕ) : IsCompact (ball v (m : ℤ)) := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let R : ℝ := (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
    (WithZero.exp (-(m : ℤ))) : ℝ)
  have hball : ball v (m : ℤ) = Metric.closedBall (0 : K) R := by
    ext x
    simp only [ball, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [FinitePlace.norm_def]
    simp only [R, NNReal.coe_le_coe]
    simpa using
      ((WithZeroMulInt.toNNReal_strictMono
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le
          (a := Valued.v x) (b := WithZero.exp (-(m : ℤ)))).symm
  rw [hball]
  exact hproper.isCompact_closedBall 0 R

private theorem wh_ball_compact_int (i : ℤ) : IsCompact (ball v i) := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  let R : ℝ := (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
    (WithZero.exp (-i)) : ℝ)
  have hball : ball v i = Metric.closedBall (0 : K) R := by
    ext x
    simp only [ball, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    rw [FinitePlace.norm_def]
    simp only [R, NNReal.coe_le_coe]
    simpa using
      ((WithZeroMulInt.toNNReal_strictMono
        (HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le
          (a := Valued.v x) (b := WithZero.exp (-i))).symm
  rw [hball]
  exact hproper.isCompact_closedBall 0 R

private theorem wh_section_bigcell_coordinate_locallyConstant
    (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (f : L.L → T.V) (hf : IsSection L T s f) (m : ℕ) (hm : L.m0 ≤ m)
    (hright : ∀ g, ∀ k ∈ L.Kc m, f (g * k) = f g) :
    IsLocallyConstant (fun t : v.adicCompletion F =>
      f (L.w * L.n (Multiplicative.ofAdd t))) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let B : Set (v.adicCompletion F) := ball v (m : ℤ)
  let e : (v.adicCompletion F) ≃ₜ (v.adicCompletion F) := Homeomorph.addRight x
  refine ⟨e '' B, e.isOpenMap B (wh_ball_isOpen (v := v) (m : ℤ)), ?_, ?_⟩
  · exact ⟨0, by simp [B, ball], by simp [e, Homeomorph.addRight]⟩
  · rintro y ⟨d, hd, rfl⟩
    have hn : L.n (Multiplicative.ofAdd (d + x)) =
        L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd d) := by
      rw [show d + x = x + d by ring]
      rw [← map_mul]
      congr 1
    calc
      f (L.w * L.n (Multiplicative.ofAdd (d + x))) =
          f ((L.w * L.n (Multiplicative.ofAdd x)) *
            L.n (Multiplicative.ofAdd d)) := by rw [hn]; congr 1 <;> group
      _ = f (L.w * L.n (Multiplicative.ofAdd x)) :=
        hright _ _ (L.n_Kc m hm d (by simpa [B] using hd))

private theorem wh_section_bigcell_coordinate_vanishes
    (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (f : L.L → T.V) (hf : IsSection L T s f) (h1 : f 1 = 0)
    (m : ℕ) (hm : L.m0 ≤ m)
    (hright : ∀ g, ∀ k ∈ L.Kc m, f (g * k) = f g)
    (t : v.adicCompletion F) (ht : t ∉ ball v (-(m : ℤ))) :
    f (L.w * L.n (Multiplicative.ofAdd t)) = 0 := by
  have ht0 : t ≠ 0 := by
    intro ht0
    subst t
    exact ht (by simp [ball])
  have hval : WithZero.exp (m : ℤ) < Valued.v t := by
    have hnot : ¬ Valued.v t ≤ WithZero.exp (m : ℤ) := by
      simpa [ball] using ht
    exact lt_of_not_ge hnot
  have hvne : Valued.v t ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 ht0
  have hvpos : 0 < Valued.v t := pos_iff_ne_zero.mpr hvne
  have hbpos : 0 < WithZero.exp (m : ℤ) :=
    pos_iff_ne_zero.mpr (WithZero.exp_ne_zero)
  have hinv : (Valued.v t)⁻¹ < (WithZero.exp (m : ℤ))⁻¹ :=
    (inv_lt_inv₀ hvpos hbpos).2 hval
  have htinv : (t⁻¹ : v.adicCompletion F) ∈ ball v (m : ℤ) := by
    change Valued.v t⁻¹ ≤ WithZero.exp (-(m : ℤ))
    apply le_of_lt
    calc
      Valued.v t⁻¹ = (Valued.v t)⁻¹ := Valuation.map_inv _ t
      _ < (WithZero.exp (m : ℤ))⁻¹ := hinv
      _ = WithZero.exp (-(m : ℤ)) := by rw [WithZero.exp_neg]
  let u : (v.adicCompletion F)ˣ := Units.mk0 t ht0
  have hBruhat : L.w * L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
        L.a (-(u⁻¹ * u⁻¹)) *
          L.nbar (Multiplicative.ofAdd
            ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by
    simpa [u] using L.lift_wn u
  have hnbar : L.nbar (Multiplicative.ofAdd
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ∈ L.Kc m := by
    apply L.nbar_Kc m hm
    simpa [u] using htinv
  have hzeroNbar : f (L.nbar (Multiplicative.ofAdd
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))) = 0 := by
    have h := hright 1 _ hnbar
    simpa [h1] using h
  calc
    f (L.w * L.n (Multiplicative.ofAdd t)) =
        ((absFin v (-(u⁻¹ * u⁻¹)) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa (-(u⁻¹ * u⁻¹))
            (f (L.nbar (Multiplicative.ofAdd
              ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)))) := by
        rw [hBruhat]
        exact hf.1 _ _ _
    _ = 0 := by rw [hzeroNbar]; simp

private theorem wh_adicIntegers_compact :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  let K := v.adicCompletion F
  letI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  rw [hset]
  exact hproper.isCompact_closedBall 0 1

private theorem wh_ball_subset_integers (m : ℕ) :
    ball v (m : ℤ) ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  intro x hx
  change x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  change Valued.v x ≤ WithZero.exp 0
  change Valued.v x ≤ WithZero.exp (-(m : ℤ)) at hx
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem wh_ball_weighted_indicator_integral (A : AddCharData F) (μ : LocHaar v)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (m : ℕ) (x : V) :
    ∫ t, A.ψ v (-t) • (ball v (m : ℤ)).indicator (fun _ => x) t ∂μ.μ =
      μ.μ.real (ball v (m : ℤ)) • x := by
  let B := ball v (m : ℤ)
  have hBmeas : MeasurableSet B := (wh_ball_isOpen (v := v) (m : ℤ)).measurableSet
  have hψ (t : v.adicCompletion F) (ht : t ∈ B) : A.ψ v (-t) = 1 := by
    apply A.integral
    have htO := wh_ball_subset_integers (v := v) m ht
    exact (v.adicCompletionIntegers F).neg_mem t htO
  have hfun : (fun t => A.ψ v (-t) • B.indicator (fun _ => x) t) =
      B.indicator (fun _ => x) := by
    funext t
    by_cases ht : t ∈ B
    · simp [Set.indicator, ht, hψ t ht]
    · simp [Set.indicator, ht]
  rw [hfun]
  exact MeasureTheory.integral_indicator_const x hBmeas

private def wh_indicatorLinearMap {K V : Type} [AddCommGroup V] [Module ℂ V]
    (S : Set K) : V →ₗ[ℂ] (K → V) where
  toFun x := S.indicator (fun _ => x)
  map_add' x y := by
    funext t
    by_cases ht : t ∈ S <;> simp [Set.indicator, ht]
  map_smul' a x := by
    funext t
    by_cases ht : t ∈ S <;> simp [Set.indicator, ht]

private theorem wh_indicator_isLocallyConstant {K V : Type} [TopologicalSpace K]
    [TopologicalSpace V] [Zero V] (U : Set K) (hU : IsClopen U) (x : V) :
    IsLocallyConstant (U.indicator (fun _ => x)) :=
  ((LocallyConstant.const K x).indicator hU).isLocallyConstant

private theorem wh_indicator_hasCompactSupport {K V : Type} [TopologicalSpace K]
    [R1Space K] [Zero V] (U : Set K) (hU : IsCompact U) (x : V) :
    HasCompactSupport (U.indicator (fun _ => x)) := by
  apply HasCompactSupport.of_support_subset_isCompact hU
  exact Set.support_indicator_subset

private theorem wh_integer_weighted_indicator_integral (A : AddCharData F) (μ : LocHaar v)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (x : V) :
    ∫ t, A.ψ v (-t) •
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => x) t ∂μ.μ = x := by
  let O : Set (v.adicCompletion F) := v.adicCompletionIntegers F
  have hOmeas : MeasurableSet O := Valued.isOpen_valuationSubring _ |>.measurableSet
  have hNorm : μ.μ O = 1 := by simpa [O] using μ.norm_O
  have hψ (t : v.adicCompletion F) (ht : t ∈ O) : A.ψ v (-t) = 1 := by
    apply A.integral
    exact (v.adicCompletionIntegers F).neg_mem t ht
  have hfun : (fun t => A.ψ v (-t) • O.indicator (fun _ => x) t) =
      O.indicator (fun _ => x) := by
    funext t
    by_cases ht : t ∈ O
    · simp [Set.indicator, ht, hψ t ht]
    · simp [Set.indicator, ht]
  rw [hfun]
  calc
    ∫ t, O.indicator (fun _ => x) t ∂μ.μ = μ.μ.real O • x :=
      MeasureTheory.integral_indicator_const x hOmeas
    _ = x := by rw [Measure.real_def, hNorm]; simp

private theorem wh_translated_ball_weighted_indicator_integral (A : AddCharData F)
    (μ : LocHaar v) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] (m : ℕ) (a : v.adicCompletion F) (x : V) :
    ∫ t, A.ψ v (-t) • (ball v (m : ℤ)).indicator (fun _ => x) (t - a) ∂μ.μ =
      A.ψ v (-a) • (μ.μ.real (ball v (m : ℤ)) • x) := by
  let K := v.adicCompletion F
  let B : Set K := ball v (m : ℤ)
  let e : K ≃ₜ K := Homeomorph.addRight a
  let eMeas : K ≃ᵐ K := e.toMeasurableEquiv
  let f : K → V := fun t => A.ψ v (-t) • B.indicator (fun _ => x) t
  let g : K → V := fun t => A.ψ v (-t) • B.indicator (fun _ => x) (t - a)
  have hmap : Measure.map eMeas μ.μ = μ.μ := by
    simpa [eMeas, e, Homeomorph.addRight] using
      (MeasureTheory.measurePreserving_add_right μ.μ a).map_eq
  have hcomp : (fun t => g (eMeas t)) = fun t => A.ψ v (-a) • f t := by
    funext t
    have he : eMeas t = t + a := by simp [eMeas, e, Homeomorph.addRight]
    rw [he]
    simp only [g]
    have harg : (t + a) - a = t := by abel
    rw [harg]
    by_cases ht : t ∈ B
    · simp only [Set.indicator_of_mem ht]
      have hψ : A.ψ v (-(t + a)) = A.ψ v (-a) * A.ψ v (-t) := by
        calc
          A.ψ v (-(t + a)) = A.ψ v (-t + -a) := by congr 1 <;> abel
          _ = A.ψ v (-t) * A.ψ v (-a) := (A.ψ v).map_add_eq_mul _ _
          _ = A.ψ v (-a) * A.ψ v (-t) := mul_comm _ _
      rw [hψ, mul_smul]
      simp [f, B, Set.indicator, ht]
    · simp [f, g, B, Set.indicator, ht]
  calc
    ∫ t, g t ∂μ.μ = ∫ t, g t ∂Measure.map eMeas μ.μ := by rw [hmap]
    _ = ∫ t, g (eMeas t) ∂μ.μ := MeasureTheory.integral_map_equiv eMeas g
    _ = ∫ t, A.ψ v (-a) • f t ∂μ.μ := by rw [hcomp]
    _ = A.ψ v (-a) • ∫ t, f t ∂μ.μ := integral_smul _ _
    _ = A.ψ v (-a) • (μ.μ.real B • x) := by
      change A.ψ v (-a) •
        (∫ t, A.ψ v (-t) • B.indicator (fun _ => x) t ∂μ.μ) = _
      rw [wh_ball_weighted_indicator_integral A μ m x]

private theorem wh_ball_coset_integrand_eq_indicator (A : AddCharData F) (m : ℕ)
    (a : v.adicCompletion F) {V : Type} [AddCommGroup V] [Module ℂ V] (x : V) :
    (fun t => A.ψ v (-t) • (ball v (m : ℤ)).indicator (fun _ => x) (t - a)) =
      ({t | t - a ∈ ball v (m : ℤ)}).indicator (fun _ => A.ψ v (-a) • x) := by
  funext t
  by_cases ht : t - a ∈ ball v (m : ℤ)
  · have hψ : A.ψ v (-t) = A.ψ v (-a) := by
      have huO := wh_ball_subset_integers (v := v) m ht
      have hψu : A.ψ v (-(t - a)) = 1 := by
        apply A.integral
        exact (v.adicCompletionIntegers F).neg_mem (t - a) huO
      calc
        A.ψ v (-t) = A.ψ v (-((t - a) + a)) := by congr 1 <;> abel
        _ = A.ψ v (-(t - a) + -a) := by congr 1 <;> abel
        _ = A.ψ v (-(t - a)) * A.ψ v (-a) := (A.ψ v).map_add_eq_mul _ _
        _ = A.ψ v (-a) := by rw [hψu]; simp
    simp [Set.indicator, ht, hψ]
  · simp [Set.indicator, ht]

private theorem wh_ball_coset_isOpen (m : ℕ) (a : v.adicCompletion F) :
    IsOpen {t | t - a ∈ ball v (m : ℤ)} := by
  exact (wh_ball_isOpen (v := v) (m : ℤ)).preimage
    (continuous_id.sub continuous_const)

private theorem wh_ball_coset_isCompact (m : ℕ) (a : v.adicCompletion F) :
    IsCompact {t | t - a ∈ ball v (m : ℤ)} := by
  let K := v.adicCompletion F
  let e : K ≃ₜ K := Homeomorph.addRight a
  have heq : {t | t - a ∈ ball v (m : ℤ)} = e '' ball v (m : ℤ) := by
    ext t
    constructor
    · intro ht
      refine ⟨t - a, ht, ?_⟩
      simp [e]
    · rintro ⟨u, hu, rfl⟩
      simpa [e] using hu
  rw [heq]
  exact (wh_ball_compact (v := v) m).image e.continuous

private theorem wh_indicator_integrable {K V : Type} [TopologicalSpace K] [T2Space K]
    [MeasurableSpace K] [OpensMeasurableSpace K] [NormedAddCommGroup V] {μ : Measure K}
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (S : Set K) (hS : IsCompact S) (x : V) : Integrable (S.indicator (fun _ => x)) μ := by
  have hmeas : MeasurableSet S := hS.isClosed.measurableSet
  have hfinite : μ S ≠ ⊤ := hS.measure_ne_top
  exact (integrableOn_const hfinite).integrable_indicator hmeas

private def wh_ball_subgroup (m : ℕ) : AddSubgroup (v.adicCompletion F) where
  carrier := ball v (m : ℤ)
  zero_mem' := by
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-(m : ℤ))
    rw [map_zero]
    exact zero_le
  add_mem' := by
    intro x y hx hy
    exact wh_ball_add hx hy
  neg_mem' := by
    intro x hx
    exact wh_ball_neg hx

private def wh_integer_ball (m : ℕ) : AddSubgroup (v.adicCompletionIntegers F) :=
  (wh_ball_subgroup (v := v) m).comap
    (v.adicCompletionIntegers F).subtype.toAddMonoidHom

private theorem wh_integer_ball_quotient_finite (m : ℕ) :
    Finite ((v.adicCompletionIntegers F) ⧸ wh_integer_ball (v := v) m) := by
  classical
  let O := v.adicCompletionIntegers F
  let H := wh_integer_ball (v := v) m
  let U : O → Set (v.adicCompletion F) := fun a => {x | x - a.1 ∈ ball v (m : ℤ)}
  have hUopen (a : O) : IsOpen (U a) := by
    apply (wh_ball_isOpen (v := v) (m : ℤ)).preimage
    exact continuous_id.sub continuous_const
  have hcover : (O : Set (v.adicCompletion F)) ⊆ ⋃ a : O, U a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ ball v (m : ℤ)
    change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  obtain ⟨t, ht⟩ :=
    (wh_adicIntegers_compact (v := v)).elim_finite_subcover U hUopen hcover
  let f : t → O ⧸ H := fun a => QuotientAddGroup.mk' H a.1
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    apply (QuotientAddGroup.mk'_eq_mk' H).2
    have hmem : x - a ∈ H := by
      change (x.1 - a.1 : v.adicCompletion F) ∈ ball v (m : ℤ)
      exact hxa
    exact ⟨x - a, hmem, by abel⟩
  exact Finite.of_surjective f hsurj

private theorem wh_quotient_eq_of_sub_mem {K : Type} [AddCommGroup K]
    (H : AddSubgroup K) {x y : K} (hxy : x - y ∈ H) :
    QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y := by
  apply (QuotientAddGroup.mk'_eq_mk' H).2
  refine ⟨y - x, ?_, by abel⟩
  simpa using H.neg_mem hxy

private theorem wh_sub_mem_of_quotient_eq {K : Type} [AddCommGroup K]
    (H : AddSubgroup K) {x y : K}
    (hxy : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) : x - y ∈ H := by
  obtain ⟨z, hz, hsum⟩ := (QuotientAddGroup.mk'_eq_mk' H).mp hxy
  have hsub : x - y = -z := by rw [← hsum]; abel
  rw [hsub]
  exact H.neg_mem hz

private def wh_coinv_ball_group (i : ℤ) : AddSubgroup (v.adicCompletion F) where
  carrier := ball v i
  zero_mem' := by
    change Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-i)
    rw [map_zero]
    exact zero_le
  add_mem' := by
    intro x y hx hy
    exact wh_ball_add hx hy
  neg_mem' := by
    intro x hx
    exact wh_ball_neg hx

private def wh_coinv_large_ball (k : ℕ) : AddSubgroup (v.adicCompletion F) :=
  wh_coinv_ball_group (v := v) (-(k : ℤ))

private def wh_coinv_small_ball (k m : ℕ) : AddSubgroup (wh_coinv_large_ball (v := v) k) :=
  (wh_coinv_ball_group (v := v) (m : ℤ)).comap
    (wh_coinv_large_ball (v := v) k).subtype

private theorem wh_coinv_quotient_finite (k m : ℕ) :
    Finite (wh_coinv_large_ball (v := v) k ⧸ wh_coinv_small_ball (v := v) k m) := by
  classical
  let U := wh_coinv_large_ball (v := v) k
  let H := wh_coinv_small_ball (v := v) k m
  let Q := U ⧸ H
  let C : Set (v.adicCompletion F) := ball v (-(k : ℤ))
  let V : U → Set (v.adicCompletion F) := fun a => {x | x - a.1 ∈ ball v (m : ℤ)}
  have hVopen (a : U) : IsOpen (V a) := by
    apply (wh_ball_isOpen (v := v) (m : ℤ)).preimage
    exact continuous_id.sub continuous_const
  have hcover : C ⊆ ⋃ a : U, V a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ ball v (m : ℤ)
    change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  obtain ⟨t, ht⟩ := (wh_ball_compact_int (v := v) (-(k : ℤ))).elim_finite_subcover
    V hVopen hcover
  let f : t → Q := fun a => QuotientAddGroup.mk' H a.1
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have hmem : x - a ∈ H := by
      change ((x - a : U) : v.adicCompletion F) ∈ ball v (m : ℤ)
      exact hxa
    exact (wh_quotient_eq_of_sub_mem H hmem).symm
  exact Finite.of_surjective f hsurj

private noncomputable def wh_coinv_rep (k m : ℕ)
    (q : wh_coinv_large_ball (v := v) k ⧸ wh_coinv_small_ball (v := v) k m) :
    wh_coinv_large_ball (v := v) k :=
  Classical.choose (QuotientAddGroup.mk'_surjective
    (wh_coinv_small_ball (v := v) k m) q)

private theorem wh_coinv_rep_class (k m : ℕ)
    (q : wh_coinv_large_ball (v := v) k ⧸ wh_coinv_small_ball (v := v) k m) :
    QuotientAddGroup.mk' (wh_coinv_small_ball (v := v) k m) (wh_coinv_rep (v := v) k m q) = q :=
  Classical.choose_spec (QuotientAddGroup.mk'_surjective
    (wh_coinv_small_ball (v := v) k m) q)

private noncomputable def wh_coinv_average (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (k m : ℕ) :
    (L.L → T.V) →ₗ[ℂ] (L.L → T.V) := by
  classical
  let U := wh_coinv_large_ball (v := v) k
  let H := wh_coinv_small_ball (v := v) k m
  let Q := U ⧸ H
  letI : Finite Q := wh_coinv_quotient_finite (v := v) k m
  letI : Fintype Q := Fintype.ofFinite Q
  refine
    { toFun := fun f => ((Fintype.card Q : ℂ)⁻¹) •
        ∑ q : Q, A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
          rtr (L.n (Multiplicative.ofAdd
            ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F))) f
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext x
    simp [Finset.sum_add_distrib, smul_add, rtr]
  · intro c f
    funext x
    simp [Finset.smul_sum, smul_smul, rtr, mul_comm, mul_left_comm, mul_assoc]

private theorem wh_coinv_rtr_add (L : FinLocalCover D H v) {V : Type}
    (x y : v.adicCompletion F) (f : L.L → V) :
    rtr (L.n (Multiplicative.ofAdd x))
        (rtr (L.n (Multiplicative.ofAdd y)) f) =
      rtr (L.n (Multiplicative.ofAdd (x + y))) f := by
  have hn : L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd y) =
      L.n (Multiplicative.ofAdd (x + y)) := by
    rw [← map_mul]
    congr 1
  funext g
  change f ((g * L.n (Multiplicative.ofAdd x)) * L.n (Multiplicative.ofAdd y)) =
    f (g * L.n (Multiplicative.ofAdd (x + y)))
  rw [mul_assoc, hn]

private theorem wh_coinv_ball_eventually (t : v.adicCompletion F) :
    ∃ k : ℕ, t ∈ ball v (-(k : ℤ)) := by
  by_cases ht0 : t = 0
  · subst t
    exact ⟨0, by simp [ball]⟩
  have hvne : Valued.v t ≠ 0 := (Valuation.ne_zero_iff Valued.v).2 ht0
  have hvinvne : (Valued.v t)⁻¹ ≠ 0 := inv_ne_zero hvne
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hvinvne
  have hposvi : 0 < (Valued.v t)⁻¹ := pos_iff_ne_zero.mpr hvinvne
  have hpose : 0 < WithZero.exp (-(k : ℤ)) :=
    pos_iff_ne_zero.mpr WithZero.exp_ne_zero
  have hbound : Valued.v t < WithZero.exp (k : ℤ) := by
    have h := (inv_lt_inv₀ hposvi hpose).2 hk
    calc
      Valued.v t = ((Valued.v t)⁻¹)⁻¹ := by rw [inv_inv]
      _ < (WithZero.exp (-(k : ℤ)))⁻¹ := h
      _ = WithZero.exp (k : ℤ) := by rw [WithZero.exp_neg, inv_inv]
  refine ⟨k, ?_⟩
  change Valued.v t ≤ WithZero.exp (-(-(k : ℤ)))
  rw [neg_neg]
  exact hbound.le

private theorem wh_coinv_weighted_term_eq (L : FinLocalCover D H v)
    {T : TorusRep D H v} (A : AddCharData F) (k m : ℕ) (f : L.L → T.V)
    (hInv : ∀ u, u ∈ ball v (m : ℤ) →
      rtr (L.n (Multiplicative.ofAdd u)) f = f)
    (a b : wh_coinv_large_ball (v := v) k)
    (hab : QuotientAddGroup.mk' (wh_coinv_small_ball (v := v) k m) a =
      QuotientAddGroup.mk' (wh_coinv_small_ball (v := v) k m) b) :
    A.ψ v (-a.1) • rtr (L.n (Multiplicative.ofAdd a.1)) f =
      A.ψ v (-b.1) • rtr (L.n (Multiplicative.ofAdd b.1)) f := by
  let H := wh_coinv_small_ball (v := v) k m
  have hab' : a - b ∈ H := wh_sub_mem_of_quotient_eq H hab
  have hba' : b - a ∈ H := by simpa using H.neg_mem hab'
  have hba : (b.1 - a.1 : v.adicCompletion F) ∈ ball v (m : ℤ) := hba'
  have hψ : A.ψ v (b.1 - a.1) = 1 := by
    apply A.integral
    exact wh_ball_subset_integers (v := v) m hba
  have hchar : A.ψ v (-a.1) = A.ψ v (-b.1) := by
    have harg : -a.1 = -b.1 + (b.1 - a.1) := by abel
    rw [harg, (A.ψ v).map_add_eq_mul, hψ, mul_one]
  have htrans : rtr (L.n (Multiplicative.ofAdd a.1)) f =
      rtr (L.n (Multiplicative.ofAdd b.1)) f := by
    have habsum : b.1 = a.1 + (b.1 - a.1) := by abel
    calc
      rtr (L.n (Multiplicative.ofAdd a.1)) f =
          rtr (L.n (Multiplicative.ofAdd a.1))
            (rtr (L.n (Multiplicative.ofAdd (b.1 - a.1))) f) := by rw [hInv _ hba]
      _ = rtr (L.n (Multiplicative.ofAdd (a.1 + (b.1 - a.1)))) f :=
            wh_coinv_rtr_add L a.1 (b.1 - a.1) f
      _ = rtr (L.n (Multiplicative.ofAdd b.1)) f :=
            congrArg (fun z => rtr (L.n (Multiplicative.ofAdd z)) f) habsum.symm
  rw [hchar, htrans]

private theorem wh_coinv_average_translate (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (k m : ℕ) (f : L.L → T.V)
    (hInv : ∀ u, u ∈ ball v (m : ℤ) →
      rtr (L.n (Multiplicative.ofAdd u)) f = f)
    (t : v.adicCompletion F) (ht : t ∈ ball v (-(k : ℤ))) :
    wh_coinv_average L T A k m (rtr (L.n (Multiplicative.ofAdd t)) f) =
      A.ψ v t • wh_coinv_average L T A k m f := by
  classical
  let U := wh_coinv_large_ball (v := v) k
  let H := wh_coinv_small_ball (v := v) k m
  let Q := U ⧸ H
  letI : Finite Q := wh_coinv_quotient_finite (v := v) k m
  letI : Fintype Q := Fintype.ofFinite Q
  let tU : U := ⟨t, ht⟩
  let qt : Q := QuotientAddGroup.mk' H tU
  let term : Q → (L.L → T.V) := fun q =>
    A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
      rtr (L.n (Multiplicative.ofAdd
        ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F))) f
  have hclass (q : Q) :
      QuotientAddGroup.mk' H
          (wh_coinv_rep (v := v) k m q + tU) =
        QuotientAddGroup.mk' H (wh_coinv_rep (v := v) k m (q + qt)) := by
    calc
      QuotientAddGroup.mk' H (wh_coinv_rep (v := v) k m q + tU) =
          QuotientAddGroup.mk' H (wh_coinv_rep (v := v) k m q) + qt := by
            simp [qt, map_add]
      _ = q + qt := by rw [wh_coinv_rep_class]
      _ = QuotientAddGroup.mk' H (wh_coinv_rep (v := v) k m (q + qt)) := by
            rw [wh_coinv_rep_class]
  have hterm (q : Q) :
      A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
          rtr (L.n (Multiplicative.ofAdd
            ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)))
            (rtr (L.n (Multiplicative.ofAdd t)) f) =
        A.ψ v t • term (q + qt) := by
    let a := wh_coinv_rep (v := v) k m q
    let b := wh_coinv_rep (v := v) k m (q + qt)
    have hchar : A.ψ v (-a.1) = A.ψ v t * A.ψ v (-(a.1 + t)) := by
      have harg : -a.1 = -(a.1 + t) + t := by abel
      rw [harg, (A.ψ v).map_add_eq_mul, mul_comm]
    have htr := wh_coinv_rtr_add L a.1 t f
    have hweighted := wh_coinv_weighted_term_eq L A k m f hInv
      (a + tU) b (hclass q)
    change A.ψ v (-a.1) •
        rtr (L.n (Multiplicative.ofAdd a.1))
          (rtr (L.n (Multiplicative.ofAdd t)) f) =
      A.ψ v t • (A.ψ v (-b.1) •
        rtr (L.n (Multiplicative.ofAdd b.1)) f)
    rw [htr, hchar]
    rw [mul_smul]
    exact congrArg (fun z => A.ψ v t • z) hweighted
  have hsum :
      (∑ q : Q,
        A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
          rtr (L.n (Multiplicative.ofAdd
            ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)))
            (rtr (L.n (Multiplicative.ofAdd t)) f)) =
      A.ψ v t • ∑ q : Q, term q := by
    calc
      _ = ∑ q : Q, A.ψ v t • term (q + qt) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hterm q
      _ = A.ψ v t • ∑ q : Q, term (q + qt) := by rw [Finset.smul_sum]
      _ = A.ψ v t • ∑ q : Q, term q := by
        congr 1
        exact Fintype.sum_equiv (Equiv.addRight qt) _ _ (by intro q; rfl)
  change ((Fintype.card Q : ℂ)⁻¹) •
      (∑ q : Q,
        A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
          rtr (L.n (Multiplicative.ofAdd
            ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)))
            (rtr (L.n (Multiplicative.ofAdd t)) f)) =
      A.ψ v t • (((Fintype.card Q : ℂ)⁻¹) • ∑ q : Q, term q)
  rw [hsum]
  simp [smul_smul, mul_comm]

private def wh_coinv_relation (L : FinLocalCover D H v) {T : TorusRep D H v}
    (A : AddCharData F)
    (f : L.L → T.V) (t : v.adicCompletion F) : L.L → T.V :=
  rtr (L.n (Multiplicative.ofAdd t)) f - A.ψ v t • f

private def wh_coinv_relation_span (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (E : Submodule ℂ (L.L → T.V)) :
    Submodule ℂ (L.L → T.V) :=
  Submodule.span ℂ (Set.range fun p : E × v.adicCompletion F =>
    wh_coinv_relation L A p.1.1 p.2)

private theorem wh_coinv_average_zero_mem (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (k m : ℕ)
    (E : Submodule ℂ (L.L → T.V)) (f : L.L → T.V) (hf : f ∈ E)
    (havg : wh_coinv_average L T A k m f = 0) :
    f ∈ wh_coinv_relation_span L T A E := by
  classical
  let U := wh_coinv_large_ball (v := v) k
  let H := wh_coinv_small_ball (v := v) k m
  let Q := U ⧸ H
  letI : Finite Q := wh_coinv_quotient_finite (v := v) k m
  letI : Fintype Q := Fintype.ofFinite Q
  let N : ℂ := (Fintype.card Q : ℂ)
  let term : Q → (L.L → T.V) := fun q =>
    A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
      rtr (L.n (Multiplicative.ofAdd
        ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F))) f
  let relterm : Q → (L.L → T.V) := fun q =>
    A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
      wh_coinv_relation L A f ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)
  have hψ (q : Q) :
      A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) *
          A.ψ v ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F) = 1 := by
    rw [← (A.ψ v).map_add_eq_mul]
    simp
  have hsumEq :
      (∑ q : Q, relterm q) = (∑ q : Q, term q) - N • f := by
    calc
      _ = ∑ q : Q,
          (A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
            rtr (L.n (Multiplicative.ofAdd
              ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F))) f -
            A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) •
              (A.ψ v ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F) • f)) := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [relterm, wh_coinv_relation, smul_sub, smul_smul]
      _ = (∑ q : Q, term q) -
          ∑ q : Q,
            (A.ψ v (-((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) *
              A.ψ v ((wh_coinv_rep (v := v) k m q : U) : v.adicCompletion F)) • f := by
        rw [Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        rw [smul_smul]
      _ = (∑ q : Q, term q) - N • f := by
        simp [hψ, N, Nat.cast_smul_eq_nsmul]
  have hNnat : Fintype.card Q ≠ 0 := Fintype.card_ne_zero
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Nat.cast_ne_zero.mpr hNnat
  have hsumZero : (N⁻¹) • (∑ q : Q, term q) = 0 := by
    simpa [wh_coinv_average, term, N] using havg
  have hrawZero : (∑ q : Q, term q) = 0 := by
    rcases smul_eq_zero.mp hsumZero with hzero | hzero
    · exact (inv_ne_zero hN hzero).elim
    · exact hzero
  have hrelSum : (∑ q : Q, relterm q) ∈ wh_coinv_relation_span L T A E := by
    apply Submodule.sum_mem
    intro q hq
    apply (wh_coinv_relation_span L T A E).smul_mem
    apply Submodule.subset_span
    exact ⟨(⟨f, hf⟩, (wh_coinv_rep (v := v) k m q : U)), rfl⟩
  have hscale : (-(N⁻¹)) • (∑ q : Q, relterm q) = f := by
    rw [hsumEq, hrawZero]
    calc
      (-(N⁻¹)) • (0 - N • f) = (-(N⁻¹)) • ((-N) • f) := by simp
      _ = ((-(N⁻¹)) * (-N)) • f := by rw [smul_smul]
      _ = f := by
        have hcoeff : (-(N⁻¹)) * (-N) = 1 := by
          field_simp
        rw [hcoeff, one_smul]
  have := (wh_coinv_relation_span L T A E).smul_mem (-(N⁻¹)) hrelSum
  rw [hscale] at this
  exact this

private theorem wh_coinv_relation_average_zero (L : FinLocalCover D H v)
    (T : TorusRep D H v) (A : AddCharData F) (s : ℂ)
    (E : Submodule ℂ (L.L → T.V)) (hE : ∀ f ∈ E, IsSection L T s f)
    (f : L.L → T.V) (hf : f ∈ wh_coinv_relation_span L T A E) :
    ∃ k m, L.m0 ≤ m ∧ wh_coinv_average L T A k m f = 0 := by
  classical
  obtain ⟨S, hS, hfS⟩ := Submodule.mem_span_finite_of_mem_span hf
  let relGen : E × v.adicCompletion F → (L.L → T.V) := fun p =>
    wh_coinv_relation L A p.1.1 p.2
  let tsub : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))} → E × v.adicCompletion F :=
    fun z => Classical.choose (Set.mem_range.mp (hS z.2))
  have htsub (z : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))}) :
      relGen (tsub z) = z.1 :=
    Classical.choose_spec (Set.mem_range.mp (hS z.2))
  let depth : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))} → ℕ := fun z =>
    Classical.choose (hE (tsub z).1.1 (tsub z).1.2 |>.2.2)
  have hdepth (z : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))}) :
      L.m0 ≤ depth z ∧ ∀ g, ∀ a ∈ L.Kc (depth z),
        (tsub z).1.1 (g * a) = (tsub z).1.1 g :=
    Classical.choose_spec (hE (tsub z).1.1 (tsub z).1.2 |>.2.2)
  let kdepth : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))} → ℕ := fun z =>
    Classical.choose (wh_coinv_ball_eventually (v := v) (tsub z).2)
  have hkdepth (z : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))}) :
      (tsub z).2 ∈ ball v (-(kdepth z : ℤ)) :=
    Classical.choose_spec (wh_coinv_ball_eventually (v := v) (tsub z).2)
  let kfun : (L.L → T.V) → ℕ := fun z =>
    if hz : z ∈ (S : Set (L.L → T.V)) then kdepth ⟨z, hz⟩ else 0
  let depthFun : (L.L → T.V) → ℕ := fun z =>
    if hz : z ∈ (S : Set (L.L → T.V)) then depth ⟨z, hz⟩ else 0
  let k := S.sup kfun
  let m := max L.m0 (S.sup depthFun)
  have hm : L.m0 ≤ m := Nat.le_max_left _ _
  let P := wh_coinv_average L T A k m
  have hSker : (S : Set (L.L → T.V)) ⊆ LinearMap.ker P := by
    intro z hz
    let zS : {z : L.L → T.V // z ∈ (S : Set (L.L → T.V))} := ⟨z, hz⟩
    let p := tsub zS
    have hp : relGen p = z := htsub zS
    have hkz : kdepth zS ≤ k := by
      have hsup : kfun z ≤ k := by
        simpa [k] using (Finset.le_sup (s := S) (f := kfun) hz)
      have hfun : kfun z = kdepth zS := by
        dsimp [kfun]
        rw [dif_pos hz]
      rw [hfun] at hsup
      exact hsup
    have hkzZ : (kdepth zS : ℤ) ≤ (k : ℤ) := by exact_mod_cast hkz
    have hidx : -(k : ℤ) ≤ -(kdepth zS : ℤ) := neg_le_neg hkzZ
    have ht : p.2 ∈ ball v (-(k : ℤ)) := wh_ball_anti hidx (hkdepth zS)
    have hdepthle : depth zS ≤ S.sup depthFun := by
      have hsup : depthFun z ≤ S.sup depthFun :=
        Finset.le_sup (s := S) (f := depthFun) hz
      have hfun : depthFun z = depth zS := by
        dsimp [depthFun]
        rw [dif_pos hz]
      rw [hfun] at hsup
      exact hsup
    have hdepthZ : (depth zS : ℤ) ≤ (m : ℤ) := by
      have hdepthNat : depth zS ≤ m := by
        dsimp [m]
        exact Nat.le_trans hdepthle (Nat.le_max_right _ _)
      exact_mod_cast hdepthNat
    have hInv : ∀ u, u ∈ ball v (m : ℤ) →
        rtr (L.n (Multiplicative.ofAdd u)) p.1.1 = p.1.1 := by
      intro u hu
      have hu' : u ∈ ball v (depth zS : ℤ) := wh_ball_anti hdepthZ hu
      funext g
      change p.1.1 (g * L.n (Multiplicative.ofAdd u)) = p.1.1 g
      exact hdepth zS |>.2 g _ (L.n_Kc (depth zS) (hdepth zS).1 u hu')
    have htrans := wh_coinv_average_translate L T A k m p.1.1 hInv p.2 ht
    have hrelavg : P (relGen p) = 0 := by
      change wh_coinv_average L T A k m
        (rtr (L.n (Multiplicative.ofAdd p.2)) p.1.1 - A.ψ v p.2 • p.1.1) = 0
      rw [map_sub, map_smul, htrans]
      simp
    apply LinearMap.mem_ker.mpr
    rw [← hp]
    exact hrelavg
  have hspan : Submodule.span ℂ (S : Set (L.L → T.V)) ≤ LinearMap.ker P :=
    Submodule.span_le.mpr hSker
  have hP := hspan hfS
  exact ⟨k, m, hm, LinearMap.mem_ker.mp hP⟩

private theorem wh_locallyConstant_compactSupport_invariant {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : v.adicCompletion F → V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ m : ℕ, ∀ x t, t ∈ ball v (m : ℤ) → φ (x + t) = φ x := by
  classical
  let K := v.adicCompletion F
  let S : Set K := tsupport φ
  let I := Σ x : S, {m : ℕ // ∀ t ∈ ball v (m : ℤ), φ (x.1 + t) = φ x.1}
  let U : I → Set K := fun i => {y | y - i.1.1 ∈ ball v (i.2.1 : ℤ)}
  have hex : ∀ x : S, ∃ m : ℕ, ∀ t ∈ ball v (m : ℤ), φ (x.1 + t) = φ x.1 := by
    intro x
    rcases hφ.exists_open x.1 with ⟨W, hWo, hxW, hconst⟩
    obtain ⟨m, hm⟩ := wh_ball_subset_nhds x.1 (hWo.mem_nhds hxW)
    exact ⟨m, fun t ht => hconst (x.1 + t) (hm t ht)⟩
  have hUopen (i : I) : IsOpen (U i) := by
    apply (wh_ball_isOpen (v := v) (i.2.1 : ℤ)).preimage
    exact continuous_id.sub continuous_const
  have hcover : S ⊆ ⋃ i : I, U i := by
    intro x hx
    obtain ⟨m, hm⟩ := hex ⟨x, hx⟩
    refine Set.mem_iUnion.2 ⟨⟨⟨x, hx⟩, ⟨m, hm⟩⟩, ?_⟩
    change Valued.v (x - x) ≤ WithZero.exp (-(m : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hUopen hcover
  let m : ℕ := t.sup fun i => i.2.1
  have hdepth (i : I) (hi : i ∈ t) : i.2.1 ≤ m := by
    dsimp [m]
    exact Finset.le_sup (s := t) (f := fun j : I => j.2.1) hi
  have hsmall (x : K) (hx : x ∈ S) (u : K) (hu : u ∈ ball v (m : ℤ)) :
      φ (x + u) = φ x := by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hmi : (i.2.1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hdepth i hi
    have hu' : u ∈ ball v (i.2.1 : ℤ) := wh_ball_anti hmi hu
    have hxi' : x - i.1.1 ∈ ball v (i.2.1 : ℤ) := hxi
    have hsum : (x - i.1.1) + u ∈ ball v (i.2.1 : ℤ) := wh_ball_add hxi' hu'
    calc
      φ (x + u) = φ (i.1.1 + ((x - i.1.1) + u)) := by congr 1 <;> ring
      _ = φ i.1.1 := i.2.2 ((x - i.1.1) + u) hsum
      _ = φ (i.1.1 + (x - i.1.1)) := (i.2.2 (x - i.1.1) hxi').symm
      _ = φ x := by congr 1 <;> ring
  have hzero (x : K) (hx : x ∉ S) : φ x = 0 := by
    by_contra hne
    apply hx
    change x ∈ closure (Function.support φ)
    have hmem : x ∈ Function.support φ := by
      change φ x ≠ 0
      exact hne
    exact subset_closure hmem
  refine ⟨m, ?_⟩
  intro x u hu
  by_cases hx : x ∈ S
  · exact hsmall x hx u hu
  · by_cases hxu : x + u ∈ S
    · have hneg : -u ∈ ball v (m : ℤ) := wh_ball_neg hu
      have hh := hsmall (x + u) hxu (-u) hneg
      have heq : (x + u) + (-u) = x := by abel
      rw [heq] at hh
      exact hh.symm
    · rw [hzero x hx, hzero (x + u) hxu]

private theorem wh_invariant_compact_support_coset_sum {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : v.adicCompletion F → V) (m : ℕ)
    (hInv : ∀ x t, t ∈ ball v (m : ℤ) → φ (x + t) = φ x) (hc : HasCompactSupport φ) :
    ∃ s : Finset (v.adicCompletion F ⧸ wh_ball_subgroup (v := v) m),
      ∃ rep : {q // q ∈ s} → v.adicCompletion F,
        (∀ q, rep q ∈ tsupport φ) ∧
        (∀ q, QuotientAddGroup.mk' (wh_ball_subgroup (v := v) m) (rep q) = q.1) ∧
        ∀ x, φ x = ∑ q : {q // q ∈ s},
          ({y | y - rep q ∈ ball v (m : ℤ)}).indicator (fun _ => φ (rep q)) x := by
  classical
  let K := v.adicCompletion F
  let S : Set K := tsupport φ
  let U : S → Set K := fun a => {x | x - a.1 ∈ ball v (m : ℤ)}
  have hUopen (a : S) : IsOpen (U a) := by
    apply (wh_ball_isOpen (v := v) (m : ℤ)).preimage
    exact continuous_id.sub continuous_const
  have hcover : S ⊆ ⋃ a : S, U a := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ ball v (m : ℤ)
    rw [sub_self]
    exact (wh_ball_subgroup (v := v) m).zero_mem
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover U hUopen hcover
  let H := wh_ball_subgroup (v := v) m
  let qmap : K → K ⧸ H := QuotientAddGroup.mk' H
  let s : Finset (K ⧸ H) := t.image (fun a : S => qmap a.1)
  let rep : {q // q ∈ s} → K := fun q =>
    (Classical.choose (Finset.mem_image.mp q.2)).1
  have hrep (q : {q // q ∈ s}) : rep q ∈ S ∧ qmap (rep q) = q.1 := by
    constructor
    · change (Classical.choose (Finset.mem_image.mp q.2)).1 ∈ S
      exact (Classical.choose (Finset.mem_image.mp q.2)).2
    · exact (Classical.choose_spec (Finset.mem_image.mp q.2)).2
  have hzero (x : K) (hx : x ∉ S) : φ x = 0 := by
    by_contra hne
    apply hx
    change x ∈ closure (Function.support φ)
    have hmem : x ∈ Function.support φ := by
      change φ x ≠ 0
      exact hne
    exact subset_closure hmem
  refine ⟨s, rep, (fun q => (hrep q).1), (fun q => (hrep q).2), ?_⟩
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hx)
    have hax : a.1 - x ∈ ball v (m : ℤ) := by simpa using wh_ball_neg hxa
    have hclass : qmap a.1 = qmap x := wh_quotient_eq_of_sub_mem H hax
    have hqx : qmap x ∈ s := Finset.mem_image.mpr ⟨a, ha, hclass⟩
    let qx : {q // q ∈ s} := ⟨qmap x, hqx⟩
    have hxrepH : x - rep qx ∈ H :=
      wh_sub_mem_of_quotient_eq H (hrep qx).2.symm
    have hxrep : x - rep qx ∈ ball v (m : ℤ) := hxrepH
    have hvalue : φ x = φ (rep qx) := by
      have h := hInv (rep qx) (x - rep qx) hxrep
      have heq : rep qx + (x - rep qx) = x := by abel
      rw [heq] at h
      exact h
    have hsingle :
        (∑ q : {q // q ∈ s},
          ({y | y - rep q ∈ ball v (m : ℤ)}).indicator (fun _ => φ (rep q)) x) =
          φ (rep qx) := by
      rw [Finset.sum_eq_single_of_mem qx (Finset.mem_univ qx) (by
        intro q _ hne
        have hnot : x ∉ {y | y - rep q ∈ ball v (m : ℤ)} := by
          intro hq
          have hqclass : q.1 = qx.1 := by
            calc
              q.1 = qmap (rep q) := (hrep q).2.symm
              _ = qmap x := (wh_quotient_eq_of_sub_mem H hq).symm
              _ = qx.1 := rfl
          exact hne (Subtype.ext hqclass)
        simp [hnot])]
      simp [Set.indicator, hxrep]
    calc
      φ x = φ (rep qx) := hvalue
      _ = ∑ q : {q // q ∈ s},
        ({y | y - rep q ∈ ball v (m : ℤ)}).indicator (fun _ => φ (rep q)) x := hsingle.symm
  · rw [hzero x hx]
    symm
    apply Finset.sum_eq_zero
    intro q _
    by_cases hq : x - rep q ∈ ball v (m : ℤ)
    · have hvalue : φ (rep q) = 0 := by
        have h := hInv (rep q) (x - rep q) hq
        have heq : rep q + (x - rep q) = x := by abel
        rw [heq] at h
        exact h.symm.trans (hzero x hx)
      simp [Set.indicator, hq, hvalue]
    · simp [hq]

private theorem wh_ball_indicator_factor (A : AddCharData F) (μ : LocHaar v)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Λ : (v.adicCompletion F → V) →ₗ[ℂ] ℂ)
    (hΛ : ∀ φ : v.adicCompletion F → V, IsLocallyConstant φ → HasCompactSupport φ →
      ∀ t, Λ (fun x => φ (x + t)) = A.ψ v t * Λ φ)
    (c : V →ₗ[ℂ] ℂ)
    (hc : ∀ x, c x = Λ ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
      (fun _ => x))) (m : ℕ) (x : V) :
    Λ ((ball v (m : ℤ)).indicator (fun _ => x)) =
      c (((μ.μ.real (ball v (m : ℤ)) : ℝ) : ℂ) • x) := by
  classical
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let B : Set K := ball v (m : ℤ)
  let EB : V → K → V := fun y => B.indicator (fun _ => y)
  let EO : V → K → V := fun y => O.indicator (fun _ => y)
  have hOopen : IsOpen O := by
    change IsOpen (v.adicCompletionIntegers F : Set K)
    exact Valued.isOpen_valuationSubring K
  have hOcompact : IsCompact O := wh_adicIntegers_compact (v := v)
  have hOclopen : IsClopen O := ⟨hOcompact.isClosed, hOopen⟩
  have hOlc (y : V) : IsLocallyConstant (EO y) :=
    wh_indicator_isLocallyConstant O hOclopen y
  have hOcs (y : V) : HasCompactSupport (EO y) :=
    wh_indicator_hasCompactSupport O hOcompact y
  have hBloc : IsClopen B :=
    ⟨(wh_ball_compact (v := v) m).isClosed, wh_ball_isOpen (v := v) (m : ℤ)⟩
  have hBlc (y : V) : IsLocallyConstant (EB y) :=
    wh_indicator_isLocallyConstant B hBloc y
  have hBcs (y : V) : HasCompactSupport (EB y) :=
    wh_indicator_hasCompactSupport B (wh_ball_compact (v := v) m) y
  have hEOinv (y t : K) (ht : t ∈ B) : EO x (y + t) = EO x y := by
    have htO : t ∈ O := wh_ball_subset_integers (v := v) m ht
    have htVal : Valued.v t ≤ 1 := by
      change t ∈ v.adicCompletionIntegers F at htO
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at htO
      exact htO
    by_cases hy : y ∈ O
    · have hyt : y + t ∈ O := by
        have hyVal : Valued.v y ≤ 1 := by
          change y ∈ v.adicCompletionIntegers F at hy
          rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hy
          exact hy
        have hytVal : Valued.v (y + t) ≤ 1 := Valued.v.map_add_le hyVal htVal
        change y + t ∈ v.adicCompletionIntegers F
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hytVal
      simp [EO, Set.indicator, hy, hyt]
    · have hyt : y + t ∉ O := by
        intro hyt
        apply hy
        have hytVal : Valued.v (y + t) ≤ 1 := by
          change y + t ∈ v.adicCompletionIntegers F at hyt
          rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hyt
          exact hyt
        have hnegVal : Valued.v (-t) ≤ 1 := by simpa using htVal
        have hyVal : Valued.v y ≤ 1 := by
          calc
            Valued.v y = Valued.v ((y + t) + (-t)) := by congr 1 <;> abel
            _ ≤ 1 := Valued.v.map_add_le hytVal hnegVal
        change y ∈ v.adicCompletionIntegers F
        rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact hyVal
      simp [EO, Set.indicator, hy, hyt]
  obtain ⟨s, rep, hrepSupport, hrep, hEOsum⟩ :=
    wh_invariant_compact_support_coset_sum (EO x) m (hEOinv) (hOcs x)
  have htsub : tsupport (EO x) ⊆ O := by
    change closure (Function.support (EO x)) ⊆ O
    apply closure_minimal
    · exact Set.support_indicator_subset
    · exact hOcompact.isClosed
  have hrepO (q : {q // q ∈ s}) : rep q ∈ O := htsub (hrepSupport q)
  have hEOrep (q : {q // q ∈ s}) : EO x (rep q) = x := by
    simp [EO, Set.indicator, hrepO q]
  let C : {q // q ∈ s} → K → V := fun q t => EB x (t - rep q)
  have hEOdecomp : EO x = ∑ q : {q // q ∈ s}, C q := by
    funext t
    rw [Finset.sum_apply]
    rw [hEOsum t]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [hEOrep q, Set.indicator]
    change (if t - rep q ∈ ball v (m : ℤ) then x else 0) =
      (if t - rep q ∈ ball v (m : ℤ) then x else 0)
    rfl
  have hψrep (q : {q // q ∈ s}) : A.ψ v (-rep q) = 1 := by
    apply A.integral
    change -rep q ∈ v.adicCompletionIntegers F
    exact (v.adicCompletionIntegers F).neg_mem (rep q) (hrepO q)
  have hΛC (q : {q // q ∈ s}) : Λ (C q) = Λ (EB x) := by
    have h := hΛ (EB x) (hBlc x) (hBcs x) (-rep q)
    rw [hψrep q, one_mul] at h
    simpa [C, EB, sub_eq_add_neg] using h
  have hΛO : c x =
      (Fintype.card {q // q ∈ s} : ℂ) * Λ (EB x) := by
    calc
      c x = Λ (EO x) := hc x
      _ = Λ (∑ q : {q // q ∈ s}, C q) := by rw [hEOdecomp]
      _ = ∑ q : {q // q ∈ s}, Λ (C q) := by
        exact map_sum Λ (fun q => C q) Finset.univ
      _ = (Fintype.card {q // q ∈ s} : ℂ) * Λ (EB x) := by simp [hΛC]
  have hweighted : (fun t => A.ψ v (-t) • EO x t) =
      fun t => ∑ q : {q // q ∈ s}, A.ψ v (-t) • C q t := by
    funext t
    rw [hEOdecomp]
    rw [Finset.sum_apply]
    exact Finset.smul_sum (s := Finset.univ) (f := fun q => C q t)
  have hGint (q : {q // q ∈ s}) :
      Integrable (fun t => A.ψ v (-t) • C q t) μ.μ := by
    change Integrable (fun t => A.ψ v (-t) • EB x (t - rep q)) μ.μ
    rw [wh_ball_coset_integrand_eq_indicator A m (rep q) x]
    exact wh_indicator_integrable _ (wh_ball_coset_isCompact (v := v) m (rep q)) _
  have hGval (q : {q // q ∈ s}) :
      ∫ t, A.ψ v (-t) • C q t ∂μ.μ = μ.μ.real B • x := by
    change ∫ t, A.ψ v (-t) • EB x (t - rep q) ∂μ.μ = _
    rw [wh_translated_ball_weighted_indicator_integral A μ m (rep q) x, hψrep q]
    simp [B]
  have hIntO : x =
      (∑ q : {q // q ∈ s}, μ.μ.real B • x) := by
    calc
      x = ∫ t, A.ψ v (-t) • EO x t ∂μ.μ :=
        (wh_integer_weighted_indicator_integral A μ x).symm
      _ = ∫ t, (∑ q : {q // q ∈ s}, A.ψ v (-t) • C q t) ∂μ.μ := by rw [hweighted]
      _ = ∑ q : {q // q ∈ s}, ∫ t, A.ψ v (-t) • C q t ∂μ.μ := by
        simpa using (MeasureTheory.integral_finsetSum (s := Finset.univ)
          (fun q _ => hGint q))
      _ = ∑ q : {q // q ∈ s}, μ.μ.real B • x := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hGval q
  by_cases hx : x = 0
  · subst x
    have hEB0 : (ball v (m : ℤ)).indicator (fun _ => (0 : V)) = 0 := by
      funext t
      by_cases ht : t ∈ ball v (m : ℤ) <;> simp [Set.indicator, ht]
    rw [hEB0, map_zero]
    simp
  · have hIntConst : x =
        (Fintype.card {q // q ∈ s} : ℝ) • (μ.μ.real B • x) := by
      calc
        x = ∑ q : {q // q ∈ s}, μ.μ.real B • x := hIntO
        _ = (Fintype.card {q // q ∈ s} : ℝ) • (μ.μ.real B • x) := by
          rw [Finset.sum_const, Finset.card_univ]
          exact (Nat.cast_smul_eq_nsmul ℝ (Fintype.card {q // q ∈ s})
            (μ.μ.real B • x)).symm
    have hsmul :
        ((Fintype.card {q // q ∈ s} : ℝ) * μ.μ.real B - 1) • x = 0 := by
      rw [sub_smul]
      have hscaled :
          ((Fintype.card {q // q ∈ s} : ℝ) * μ.μ.real B) • x = x := by
        simpa only [← smul_smul] using hIntConst.symm
      rw [hscaled]
      simp
    have hscale : (Fintype.card {q // q ∈ s} : ℝ) * μ.μ.real B = 1 := by
      rcases smul_eq_zero.mp hsmul with hz | hx0
      · linarith
      · exact (hx hx0).elim
    have hscaleC : (Fintype.card {q // q ∈ s} : ℂ) * (μ.μ.real B : ℂ) = 1 := by
      exact_mod_cast hscale
    have hcoeff : (1 : ℂ) = (μ.μ.real B : ℂ) * (Fintype.card {q // q ∈ s} : ℂ) := by
      calc
        1 = (Fintype.card {q // q ∈ s} : ℂ) * (μ.μ.real B : ℂ) := hscaleC.symm
        _ = (μ.μ.real B : ℂ) * (Fintype.card {q // q ∈ s} : ℂ) := by ring
    calc
      Λ (EB x) = 1 * Λ (EB x) := by simp
      _ = (μ.μ.real B : ℂ) *
          ((Fintype.card {q // q ∈ s} : ℂ) * Λ (EB x)) := by
        calc
          1 * Λ (EB x) =
              ((μ.μ.real B : ℂ) * (Fintype.card {q // q ∈ s} : ℂ)) * Λ (EB x) := by
                rw [hcoeff]
          _ = (μ.μ.real B : ℂ) *
              ((Fintype.card {q // q ∈ s} : ℂ) * Λ (EB x)) := by ring
      _ = (μ.μ.real B : ℂ) * c x := by rw [hΛO]
      _ = c ((μ.μ.real B : ℂ) • x) := (map_smul c _ _).symm

/-- **wh:distribution**: a `ψ`-equivariant linear functional on locally constant compactly
supported `φ : K → V` is `φ ↦ c(∫ ψ(-t) φ(t) dt)`. -/
theorem psi_equivariant_functional (A : AddCharData F) (μ : LocHaar v) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : (v.adicCompletion F → V) →ₗ[ℂ] ℂ)
    (hΛ : ∀ φ : v.adicCompletion F → V, IsLocallyConstant φ → HasCompactSupport φ →
      ∀ t, Λ (fun x => φ (x + t)) = A.ψ v t * Λ φ) :
    ∃ c : V →ₗ[ℂ] ℂ, ∀ φ : v.adicCompletion F → V, IsLocallyConstant φ → HasCompactSupport φ →
      Λ φ = c (∫ t, A.ψ v (-t) • φ t ∂μ.μ) := by
  classical
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let c : V →ₗ[ℂ] ℂ := Λ.comp (wh_indicatorLinearMap O)
  have hc (x : V) : c x = Λ (O.indicator (fun _ => x)) := rfl
  refine ⟨c, ?_⟩
  intro φ hφ hcφ
  obtain ⟨m, hInv⟩ := wh_locallyConstant_compactSupport_invariant (v := v) φ hφ hcφ
  obtain ⟨s, rep, hrepSupport, hrep, hcosetSum⟩ :=
    wh_invariant_compact_support_coset_sum φ m hInv hcφ
  let B : Set K := ball v (m : ℤ)
  let EB : V → K → V := fun x => B.indicator (fun _ => x)
  let C : {q // q ∈ s} → K → V := fun q =>
    ({t | t - rep q ∈ B}).indicator (fun _ => φ (rep q))
  have hBclopen : IsClopen B :=
    ⟨(wh_ball_compact (v := v) m).isClosed, wh_ball_isOpen (v := v) (m : ℤ)⟩
  have hBlc (x : V) : IsLocallyConstant (EB x) :=
    wh_indicator_isLocallyConstant B hBclopen x
  have hBcs (x : V) : HasCompactSupport (EB x) :=
    wh_indicator_hasCompactSupport B (wh_ball_compact (v := v) m) x
  have hCeq (q : {q // q ∈ s}) : C q = fun t => EB (φ (rep q)) (t - rep q) := by
    funext t
    simp [C, EB, B, Set.indicator]
  have hΛC (q : {q // q ∈ s}) :
      Λ (C q) = c (∫ t, A.ψ v (-t) • C q t ∂μ.μ) := by
    let y := φ (rep q)
    have hΛshift : Λ (C q) = A.ψ v (-rep q) * Λ (EB y) := by
      have h := hΛ (EB y) (hBlc y) (hBcs y) (-rep q)
      calc
        Λ (C q) = Λ (fun t => EB y (t - rep q)) := by rw [hCeq q]
        _ = A.ψ v (-rep q) * Λ (EB y) := by
          simpa [sub_eq_add_neg] using h
    have hBall : Λ (EB y) = c (((μ.μ.real B : ℝ) : ℂ) • y) := by
      simpa [EB, B] using wh_ball_indicator_factor A μ Λ hΛ c hc m y
    have hIntegral :
        ∫ t, A.ψ v (-t) • C q t ∂μ.μ =
          A.ψ v (-rep q) • (μ.μ.real B • y) := by
      rw [hCeq q]
      exact wh_translated_ball_weighted_indicator_integral A μ m (rep q) y
    have hreal : μ.μ.real B • y = ((μ.μ.real B : ℝ) : ℂ) • y := by simp
    calc
      Λ (C q) = A.ψ v (-rep q) * Λ (EB y) := hΛshift
      _ = A.ψ v (-rep q) • c (((μ.μ.real B : ℝ) : ℂ) • y) := by
        rw [hBall]
        simp [smul_eq_mul]
      _ = c (A.ψ v (-rep q) • (((μ.μ.real B : ℝ) : ℂ) • y)) := by
        simpa [smul_eq_mul] using
          (map_smul c (A.ψ v (-rep q)) (((μ.μ.real B : ℝ) : ℂ) • y)).symm
      _ = c (∫ t, A.ψ v (-t) • C q t ∂μ.μ) := by
        congr 1
        rw [hIntegral, hreal]
  have hphiSum : φ = ∑ q : {q // q ∈ s}, C q := by
    funext t
    rw [Finset.sum_apply]
    rw [hcosetSum t]
  have hΛsum : Λ φ = ∑ q : {q // q ∈ s}, Λ (C q) := by
    calc
      Λ φ = Λ (∑ q : {q // q ∈ s}, C q) := by rw [hphiSum]
      _ = ∑ q : {q // q ∈ s}, Λ (C q) :=
        map_sum Λ (fun q => C q) Finset.univ
  have hweighted : (fun t => A.ψ v (-t) • φ t) =
      fun t => ∑ q : {q // q ∈ s}, A.ψ v (-t) • C q t := by
    funext t
    rw [hphiSum, Finset.sum_apply]
    exact Finset.smul_sum (s := Finset.univ) (f := fun q => C q t)
  have hGint (q : {q // q ∈ s}) :
      Integrable (fun t => A.ψ v (-t) • C q t) μ.μ := by
    rw [hCeq q, wh_ball_coset_integrand_eq_indicator A m (rep q) (φ (rep q))]
    exact wh_indicator_integrable _ (wh_ball_coset_isCompact (v := v) m (rep q)) _
  have hIntegralSum :
      ∫ t, (∑ q : {q // q ∈ s}, A.ψ v (-t) • C q t) ∂μ.μ =
        ∑ q : {q // q ∈ s}, ∫ t, A.ψ v (-t) • C q t ∂μ.μ := by
    simpa using (MeasureTheory.integral_finsetSum (s := Finset.univ)
      (fun q _ => hGint q))
  calc
    Λ φ = ∑ q : {q // q ∈ s}, Λ (C q) := hΛsum
    _ = ∑ q : {q // q ∈ s}, c (∫ t, A.ψ v (-t) • C q t ∂μ.μ) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hΛC q
    _ = c (∑ q : {q // q ∈ s}, ∫ t, A.ψ v (-t) • C q t ∂μ.μ) :=
      (map_sum c (fun q => ∫ t, A.ψ v (-t) • C q t ∂μ.μ) Finset.univ).symm
    _ = c (∫ t, (∑ q : {q // q ∈ s}, A.ψ v (-t) • C q t) ∂μ.μ) := by
      rw [← hIntegralSum]
    _ = c (∫ t, A.ψ v (-t) • φ t ∂μ.μ) := by rw [← hweighted]

/-- **wh:small-cell**: a section vanishing at `1` is a big-cell section. -/
theorem section_eq_bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (f : L.L → T.V) (hf : IsSection L T s f) (h1 : f 1 = 0) :
    ∃ φ : v.adicCompletion F → T.V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      f = bigCell L T s φ := by
  classical
  obtain ⟨m, hm, hright⟩ := hf.2.2
  let φ : v.adicCompletion F → T.V := fun t =>
    f (L.w * L.n (Multiplicative.ofAdd t))
  have hφ : IsLocallyConstant φ := by
    simpa [φ] using wh_section_bigcell_coordinate_locallyConstant L T s f hf m hm hright
  have hsupport : Function.support φ ⊆ ball v (-(m : ℤ)) := by
    intro t ht
    change φ t ≠ 0 at ht
    by_contra hout
    have hzero := wh_section_bigcell_coordinate_vanishes L T s f hf h1 m hm hright t hout
    exact ht (by simpa [φ] using hzero)
  have hcompact : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (wh_ball_compact_int (v := v) (-(m : ℤ)))
      hsupport
  refine ⟨φ, hφ, hcompact, ?_⟩
  funext g
  rcases cover_bruhat L g with hbig | hsmall
  · rcases hbig with ⟨x, ζ, y, t, rfl⟩
    have hreorder :
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y *
            L.w * L.n (Multiplicative.ofAdd t) =
          L.n (Multiplicative.ofAdd x) * L.a y *
            (L.z ζ * (L.w * L.n (Multiplicative.ofAdd t))) := by
      calc
        _ = L.n (Multiplicative.ofAdd x) *
              (L.z ζ * L.a y) * (L.w * L.n (Multiplicative.ofAdd t)) := by group
        _ = L.n (Multiplicative.ofAdd x) *
              (L.a y * L.z ζ) * (L.w * L.n (Multiplicative.ofAdd t)) := by
                rw [L.z_central ζ (L.a y)]
        _ = _ := by group
    have hvalue :
        f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) =
          ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
            T.σa y (f (L.z ζ * (L.w * L.n (Multiplicative.ofAdd t)))) := by
      rw [hreorder]
      exact hf.1 x y _
    calc
      f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) =
          ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa y (((ζ : ℂˣ) : ℂ) • φ t) := by
        rw [hvalue, hf.2.1 ζ (L.w * L.n (Multiplicative.ofAdd t))]
      _ = ((ζ : ℂˣ) : ℂ) •
          ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
        simp [map_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = bigCell L T s φ
          (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
            L.n (Multiplicative.ofAdd t)) := by
        rw [bigCell_apply]
  · rcases hsmall with ⟨x, ζ, y, rfl⟩
    have hreorder :
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y =
          L.n (Multiplicative.ofAdd x) * L.a y * L.z ζ := by
      calc
        _ = L.n (Multiplicative.ofAdd x) * (L.z ζ * L.a y) := by group
        _ = L.n (Multiplicative.ofAdd x) * (L.a y * L.z ζ) := by
          rw [L.z_central ζ (L.a y)]
        _ = _ := by group
    have hvalue :
        f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) =
          ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
            T.σa y (f (L.z ζ)) := by
      rw [hreorder]
      exact hf.1 x y (L.z ζ)
    have hzero : f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := by
      have hz : f (L.z ζ) = ((ζ : ℂˣ) : ℂ) • f 1 := by
        simpa using hf.2.1 ζ 1
      rw [hvalue, hz, h1]
      simp
    calc
      f (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := hzero
      _ = bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) := by
        rw [bigCell_borel]

private def wh_bigCellLinear (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) :
    (v.adicCompletion F → T.V) →ₗ[ℂ] (L.L → T.V) where
  toFun φ := bigCell L T s φ
  map_add' φ ψ := by
    funext g
    rcases cover_bruhat L g with hbig | hsmall
    · rcases hbig with ⟨x, ζ, y, t, rfl⟩
      calc
        bigCell L T s (φ + ψ)
            (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
              L.n (Multiplicative.ofAdd t)) =
            ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa y ((φ + ψ) t) := bigCell_apply L T s (φ + ψ) x ζ y t
        _ = (((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa y (φ t)) +
            (((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa y (ψ t)) := by simp [map_add, smul_add, smul_smul]
        _ = bigCell L T s φ
              (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
                L.n (Multiplicative.ofAdd t)) +
            bigCell L T s ψ
              (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
                L.n (Multiplicative.ofAdd t)) := by
          rw [bigCell_apply L T s φ x ζ y t, bigCell_apply L T s ψ x ζ y t]
    · rcases hsmall with ⟨x, ζ, y, rfl⟩
      simp [bigCell_borel]
  map_smul' c φ := by
    funext g
    rcases cover_bruhat L g with hbig | hsmall
    · rcases hbig with ⟨x, ζ, y, t, rfl⟩
      calc
        bigCell L T s (c • φ)
            (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
              L.n (Multiplicative.ofAdd t)) =
            ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa y ((c • φ) t) := bigCell_apply L T s (c • φ) x ζ y t
        _ = c • (((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa y (φ t)) := by
          simp only [Pi.smul_apply, map_smul, smul_smul]
          congr 1
          ring
        _ = c • bigCell L T s φ
              (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
                L.n (Multiplicative.ofAdd t)) := by
          rw [bigCell_apply L T s φ x ζ y t]
    · rcases hsmall with ⟨x, ζ, y, rfl⟩
      simp [bigCell_borel]

private theorem wh_bigCell_right_translation (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (φ : v.adicCompletion F → T.V)
    (t : v.adicCompletion F) :
    rtr (L.n (Multiplicative.ofAdd t)) (bigCell L T s φ) =
      bigCell L T s (fun x => φ (x + t)) := by
  funext g
  change bigCell L T s φ (g * L.n (Multiplicative.ofAdd t)) =
    bigCell L T s (fun x => φ (x + t)) g
  rcases cover_bruhat L g with hbig | hsmall
  · rcases hbig with ⟨x, ζ, y, u, rfl⟩
    have hnadd : L.n (Multiplicative.ofAdd u) * L.n (Multiplicative.ofAdd t) =
        L.n (Multiplicative.ofAdd (u + t)) := by
      rw [← map_mul]
      congr 1
    have htranslate :
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd u)) * L.n (Multiplicative.ofAdd t) =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd (u + t)) := by
      calc
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
              (L.n (Multiplicative.ofAdd u) * L.n (Multiplicative.ofAdd t)) := by group
        _ = _ := by rw [hnadd]
    rw [htranslate, bigCell_apply, bigCell_apply]
  · rcases hsmall with ⟨x, ζ, y, rfl⟩
    let yt : v.adicCompletion F := t * (y : v.adicCompletion F)
    have hna : L.a y * L.n (Multiplicative.ofAdd t) =
        L.n (Multiplicative.ofAdd yt) * L.a y := by
      have h := L.lift_na yt y
      have harg : yt * ((y⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = t := by
        dsimp [yt]
        simp
      simpa [yt, harg] using h.symm
    have hnadd : L.n (Multiplicative.ofAdd x) * L.n (Multiplicative.ofAdd yt) =
        L.n (Multiplicative.ofAdd (x + yt)) := by
      rw [← map_mul]
      congr 1
    have htranslate :
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) *
          L.n (Multiplicative.ofAdd t) =
        L.n (Multiplicative.ofAdd (x + yt)) * L.z ζ * L.a y := by
      calc
        _ = L.n (Multiplicative.ofAdd x) *
              (L.z ζ * (L.a y * L.n (Multiplicative.ofAdd t))) := by group
        _ = L.n (Multiplicative.ofAdd x) *
              (L.z ζ * (L.n (Multiplicative.ofAdd yt) * L.a y)) := by rw [hna]
        _ = L.n (Multiplicative.ofAdd x) *
              ((L.z ζ * L.n (Multiplicative.ofAdd yt)) * L.a y) := by group
        _ = L.n (Multiplicative.ofAdd x) *
              ((L.n (Multiplicative.ofAdd yt) * L.z ζ) * L.a y) := by
                rw [L.z_central ζ (L.n (Multiplicative.ofAdd yt))]
        _ = L.n (Multiplicative.ofAdd x) *
              (L.n (Multiplicative.ofAdd yt) * L.z ζ) * L.a y := by group
        _ = _ := by rw [← hnadd]; group
    rw [htranslate, bigCell_borel, bigCell_borel]

/-- **wh:two-cell** (KP Cor. I.3.4/Lemma I.3.2 replaced): every Whittaker functional on `I(T, s)`
is `c ∘ 𝒥` (every `s ∈ ℂ`). -/
theorem whittaker_twoCell (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (Λ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerOn L A (sectionSpace L T s) Λ) :
    ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ sectionSpace L T s, Λ f = c (jacquet L A μ f) := by
  classical
  let bcl := wh_bigCellLinear L T s
  let Λtest : (v.adicCompletion F → T.V) →ₗ[ℂ] ℂ := Λ.comp bcl
  have htestEquiv : ∀ φ : v.adicCompletion F → T.V, IsLocallyConstant φ →
      HasCompactSupport φ → ∀ t,
        Λtest (fun x => φ (x + t)) = A.ψ v t * Λtest φ := by
    intro φ hφ hcompact t
    have hsec : IsSection L T s (bigCell L T s φ) := bigCell_isSection L T s φ hφ hcompact
    have hmem : bigCell L T s φ ∈ sectionSpace L T s := by
      change IsSection L T s (bigCell L T s φ)
      exact hsec
    have h := hΛ (bigCell L T s φ) hmem t
    rw [wh_bigCell_right_translation] at h
    change Λ (bigCell L T s (fun x => φ (x + t))) =
      A.ψ v t * Λ (bigCell L T s φ) at h
    simpa [Λtest, bcl, wh_bigCellLinear] using h
  obtain ⟨c, hc⟩ := psi_equivariant_functional A μ Λtest htestEquiv
  have hbigTest (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
      (hcompact : HasCompactSupport φ) :
      Λ (bigCell L T s φ) = c (∫ t, A.ψ v (-t) • φ t ∂μ.μ) := by
    have h := hc φ hφ hcompact
    change Λ (bigCell L T s φ) = _ at h
    exact h
  have hbigJacquet (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
      (hcompact : HasCompactSupport φ) :
    jacquet L A μ (bigCell L T s φ) = ∫ t, A.ψ v (-t) • φ t ∂μ.μ := by
    have h := jacquet_bigCell L T A μ s φ hφ hcompact 1
    rw [L.a_one] at h
    have hrtr : rtr (1 : L.L) (bigCell L T s φ) = bigCell L T s φ := by
      funext g
      simp [rtr]
    rw [hrtr] at h
    simpa [T.σa_one, absFin_eq_norm] using h
  have hzeroEval : ∀ f : L.L → T.V, IsSection L T s f → f 1 = 0 →
      Λ f = c (jacquet L A μ f) := by
    intro f hf hf1
    obtain ⟨φ, hφ, hcompact, hEq⟩ := section_eq_bigCell L T s f hf hf1
    calc
      Λ f = Λ (bigCell L T s φ) := by rw [hEq]
      _ = c (jacquet L A μ (bigCell L T s φ)) := by
        rw [hbigJacquet φ hφ hcompact]
        exact hbigTest φ hφ hcompact
      _ = c (jacquet L A μ f) := by rw [hEq]
  obtain ⟨d, htrivial, t, ht, hψt⟩ := psi_conductor A v
  have hψne : A.ψ v t - 1 ≠ 0 := sub_ne_zero.mpr hψt
  have hfactor : ∀ f : L.L → T.V, IsSection L T s f →
      Λ f = c (jacquet L A μ f) := by
    intro f hf
    have hfmem : f ∈ sectionSpace L T s := by
      change IsSection L T s f
      exact hf
    have hnt : f (L.n (Multiplicative.ofAdd t)) = f 1 := by
      simpa [L.a_one, T.σa_one, absFin_eq_norm] using hf.1 t 1 1
    let q : L.L → T.V := rtr (L.n (Multiplicative.ofAdd t)) f - f
    have hrtmem : rtr (L.n (Multiplicative.ofAdd t)) f ∈ sectionSpace L T s := by
      change IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f)
      exact IsSection.rtr hf (L.n (Multiplicative.ofAdd t))
    have hqmem : q ∈ sectionSpace L T s :=
      (sectionSpace L T s).sub_mem hrtmem hfmem
    have hqsec : IsSection L T s q := hqmem
    have hq1 : q 1 = 0 := by
      simp [q, rtr, hnt]
    have hzq := hzeroEval q hqsec hq1
    have hΛtr := hΛ f hfmem t
    have hΛq : Λ q = (A.ψ v t - 1) * Λ f := by
      dsimp [q]
      rw [map_sub, hΛtr]
      ring
    have hJtr : jacquet L A μ (rtr (L.n (Multiplicative.ofAdd t)) f) =
        A.ψ v t • jacquet L A μ f := (jacquet_equiv L T A μ s f hf).1 t
    have hJq : jacquet L A μ q = (A.ψ v t - 1) • jacquet L A μ f := by
      calc
        jacquet L A μ q =
            jacquet L A μ (rtr (L.n (Multiplicative.ofAdd t)) f) - jacquet L A μ f := by
              have hlin := jacquet_linear L T A μ s
                (rtr (L.n (Multiplicative.ofAdd t)) f) f
                (IsSection.rtr hf (L.n (Multiplicative.ofAdd t))) hf (-1)
              simpa [q, ← sub_eq_add_neg] using hlin
        _ = (A.ψ v t) • jacquet L A μ f - jacquet L A μ f := by rw [hJtr]
        _ = (A.ψ v t - 1) • jacquet L A μ f := by
              calc
                _ = (A.ψ v t) • jacquet L A μ f -
                    (1 : ℂ) • jacquet L A μ f := by simp
                _ = _ := by rw [← sub_smul]
    have hcq : c (jacquet L A μ q) =
        (A.ψ v t - 1) * c (jacquet L A μ f) := by
      rw [hJq, map_smul]
      simp [smul_eq_mul]
    have heq : (A.ψ v t - 1) * Λ f =
        (A.ψ v t - 1) * c (jacquet L A μ f) := by
      calc
        (A.ψ v t - 1) * Λ f = Λ q := hΛq.symm
        _ = c (jacquet L A μ q) := hzq
        _ = (A.ψ v t - 1) * c (jacquet L A μ f) := hcq
    have hprod : (A.ψ v t - 1) * (Λ f - c (jacquet L A μ f)) = 0 := by
      calc
        _ = (A.ψ v t - 1) * Λ f - (A.ψ v t - 1) * c (jacquet L A μ f) := by ring
        _ = 0 := by rw [heq]; simp
    have hdiff : Λ f - c (jacquet L A μ f) = 0 := by
      rcases mul_eq_zero.mp hprod with hzero | hzero
      · exact (hψne hzero).elim
      · exact hzero
    exact sub_eq_zero.mp hdiff
  refine ⟨c, ?_⟩
  intro f hf
  have hfsec : IsSection L T s f := by
    change f ∈ sectionSpace L T s at hf
    exact hf
  exact hfactor f hfsec

set_option maxHeartbeats 0 in
/-- **wh:coinvariants** (left exactness of `ψ`-twisted coinvariants, Bernstein–Zelevinsky): a
Whittaker functional on an `rtr`-stable subspace of `I(T, s)` extends to `I(T, s)`. -/
theorem whittaker_extend (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (s : ℂ) (W : Submodule ℂ (L.L → T.V)) (hW : W ≤ sectionSpace L T s) (hst : IsRtrStable W)
    (Λ : (L.L → T.V) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerOn L A W Λ) :
    ∃ Λ' : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (sectionSpace L T s) Λ' ∧
      ∀ f ∈ W, Λ' f = Λ f := by
  classical
  let I := sectionSpace L T s
  let RI := wh_coinv_relation_span L T A I
  let RW := wh_coinv_relation_span L T A W
  have hRIle : RI ≤ I := by
    apply Submodule.span_le.mpr
    rintro z ⟨p, rfl⟩
    have hrt : rtr (L.n (Multiplicative.ofAdd p.2)) p.1.1 ∈ I := by
      change IsSection L T s (rtr (L.n (Multiplicative.ofAdd p.2)) p.1.1)
      exact IsSection.rtr p.1.2 (L.n (Multiplicative.ofAdd p.2))
    have hsmul : A.ψ v p.2 • p.1.1 ∈ I := I.smul_mem (A.ψ v p.2) p.1.2
    exact I.sub_mem hrt hsmul
  have hRWleRI : RW ≤ RI := by
    apply Submodule.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact Submodule.subset_span
      ⟨(⟨p.1.1, hW p.1.2⟩, p.2), rfl⟩
  have hΛzeroRW : RW ≤ LinearMap.ker Λ := by
    apply Submodule.span_le.mpr
    rintro z ⟨p, rfl⟩
    have h := hΛ p.1.1 p.1.2 p.2
    change Λ (rtr (L.n (Multiplicative.ofAdd p.2)) p.1.1 - A.ψ v p.2 • p.1.1) = 0
    rw [map_sub, map_smul, h]
    simp
  let R : Submodule ℂ I := Submodule.comap I.subtype RI
  let WI : Submodule ℂ I := Submodule.comap I.subtype W
  letI : AddCommGroup (↥WI) := inferInstance
  letI : Module ℂ (↥WI) := inferInstance
  let qW : WI →ₗ[ℂ] I ⧸ R := R.mkQ.comp WI.subtype
  let lambdaW : WI →ₗ[ℂ] ℂ := Λ.comp (I.subtype.comp WI.subtype)
  have hker : LinearMap.ker qW ≤ LinearMap.ker lambdaW := by
    intro x hx
    have hq : qW x = 0 := LinearMap.mem_ker.mp hx
    have hxR : WI.subtype x ∈ R := by
      have hxker : WI.subtype x ∈ LinearMap.ker R.mkQ := LinearMap.mem_ker.mpr hq
      simpa [Submodule.ker_mkQ] using hxker
    have hxRI : I.subtype (WI.subtype x) ∈ RI := hxR
    let f : L.L → T.V := I.subtype (WI.subtype x)
    have hfW : f ∈ W := x.2
    have hfsec : IsSection L T s f := (WI.subtype x).2
    obtain ⟨k, m, hm, havg⟩ := wh_coinv_relation_average_zero
      L T A s I (by intro g hg; exact hg) f hxRI
    have hfRW : f ∈ RW := wh_coinv_average_zero_mem L T A k m W f hfW havg
    have hΛf : Λ f = 0 := LinearMap.mem_ker.mp (hΛzeroRW hfRW)
    apply LinearMap.mem_ker.mpr
    change Λ f = 0
    exact hΛf
  let lift : WI ⧸ LinearMap.ker qW →ₗ[ℂ] ℂ :=
    Submodule.liftQ (LinearMap.ker qW) lambdaW hker
  let ellRange : LinearMap.range qW →ₗ[ℂ] ℂ :=
    lift.comp qW.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ellQ, hellQ⟩ := LinearMap.exists_extend ellRange
  let ellI : I →ₗ[ℂ] ℂ := ellQ.comp R.mkQ
  have hrestrict (x : WI) : ellI (WI.subtype x) = lambdaW x := by
    let y : LinearMap.range qW := ⟨qW x, LinearMap.mem_range_self qW x⟩
    have hy : qW.quotKerEquivRange.symm y = (LinearMap.ker qW).mkQ x := by
      have hyEq : qW.quotKerEquivRange ((LinearMap.ker qW).mkQ x) = y := by
        apply Subtype.ext
        simp [y, LinearMap.quotKerEquivRange_apply_mk]
      rw [← hyEq]
      exact qW.quotKerEquivRange.symm_apply_apply _
    have hEllRange : ellRange y = lambdaW x := by
      simp [ellRange, hy, lift, Submodule.liftQ_apply]
    have hExtAt : ellQ y = ellRange y := by
      have h := congrArg (fun g : LinearMap.range qW →ₗ[ℂ] ℂ => g y) hellQ
      simpa using h
    calc
      ellI (WI.subtype x) = ellQ (qW x) := by rfl
      _ = ellQ y := rfl
      _ = ellRange y := hExtAt
      _ = lambdaW x := hEllRange
  have hEllWhittaker : ∀ f : I, ∀ t : v.adicCompletion F,
      ellI ⟨rtr (L.n (Multiplicative.ofAdd t)) f.1,
        (by change IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f.1)
            exact IsSection.rtr f.2 (L.n (Multiplicative.ofAdd t)))⟩ =
        A.ψ v t * ellI f := by
    intro f t
    have hrt : rtr (L.n (Multiplicative.ofAdd t)) f.1 ∈ I := by
      change IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f.1)
      exact IsSection.rtr f.2 (L.n (Multiplicative.ofAdd t))
    let fr : I := ⟨rtr (L.n (Multiplicative.ofAdd t)) f.1, hrt⟩
    have hrelsec : wh_coinv_relation L A f.1 t ∈ I := by
      change IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f.1 - A.ψ v t • f.1)
      exact I.sub_mem hrt (I.smul_mem (A.ψ v t) f.2)
    let rel : I := ⟨wh_coinv_relation L A f.1 t, hrelsec⟩
    have hrelRI : rel ∈ R := by
      change I.subtype rel ∈ RI
      apply Submodule.subset_span
      exact ⟨(f, t), rfl⟩
    have hqrel : R.mkQ rel = 0 := by
      have hkerrel : rel ∈ LinearMap.ker R.mkQ := by
        simpa [Submodule.ker_mkQ] using hrelRI
      exact LinearMap.mem_ker.mp hkerrel
    have hEllRel : ellI rel = 0 := by
      simp [ellI, hqrel]
    have hdiff : ellI fr - A.ψ v t * ellI f = 0 := by
      calc
        ellI fr - A.ψ v t * ellI f = ellI fr - ellI (A.ψ v t • f) := by
          rw [map_smul]
          simp
        _ = ellI (fr - A.ψ v t • f) := (map_sub ellI fr (A.ψ v t • f)).symm
        _ = ellI rel := by
          have hrelEq : rel = fr - A.ψ v t • f := by
            apply Subtype.ext
            rfl
          rw [hrelEq]
        _ = 0 := hEllRel
    exact sub_eq_zero.mp hdiff
  obtain ⟨ellExt, hellExt⟩ := LinearMap.exists_extend ellI
  have hellExtAt (f : I) : ellExt f.1 = ellI f := by
    have h := congrArg (fun g : I →ₗ[ℂ] ℂ => g f) hellExt
    simpa using h
  refine ⟨ellExt, ?_, ?_⟩
  · intro f hf t
    let fI : I := ⟨f, hf⟩
    let rtI : I := ⟨rtr (L.n (Multiplicative.ofAdd t)) f,
      (by change IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f)
          exact IsSection.rtr hf (L.n (Multiplicative.ofAdd t)))⟩
    calc
      ellExt (rtr (L.n (Multiplicative.ofAdd t)) f) = ellI rtI := hellExtAt rtI
      _ = A.ψ v t * ellI fI := hEllWhittaker fI t
      _ = A.ψ v t * ellExt f := by rw [← hellExtAt fI]
  · intro f hf
    let fI : I := ⟨f, hW hf⟩
    let fWI : WI := ⟨fI, hf⟩
    calc
      ellExt f = ellI fI := hellExtAt fI
      _ = lambdaW fWI := by simpa [fWI] using hrestrict fWI
      _ = Λ f := rfl

/-- **wh:local-coefficient**: `𝒥 ∘ M(s) = τ(s) ∘ 𝒥` on `I(T, s)`, `Re s > 0`. -/
theorem local_coefficient (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) :
    ∃ τ : T.V →ₗ[ℂ] T.V, ∀ f ∈ sectionSpace L T s,
      jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f) := by
  sorry

/-- The diagonal coefficient `A_k(s) = (1 - q⁻¹) q^{-2 m₀ s}/(1 - q^{-6s})`, `m₀ ≡ -k mod 3`. -/
def tauDiag (v : FinPlace F) (s : ℂ) (k : ZMod 3) : ℂ :=
  (1 - (qv v : ℂ)⁻¹) * (qv v : ℂ) ^ (-2 * (((-k).val : ℕ) : ℂ) * s) / (1 - (qv v : ℂ) ^ (-6 * s))

/-- **wh:tau-tame**: `τ(s) e_k = A_k(s) e_{-k} + q^{2s-1} G(ρ^{k-1}) e_{k+1}` with
`G(ρ^j) = q^{1/2} g_{2j}`. -/
theorem local_coefficient_tame (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (s : ℂ) (hs : 0 < s.re) (τ : T.V →ₗ[ℂ] T.V)
    (hτ : ∀ f ∈ sectionSpace L T s, jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f))
    (k : ZMod 3) :
    τ (B.e k) = tauDiag v s k • B.e (-k) +
      ((qv v : ℂ) ^ (2 * s - 1) * ((qv v : ℂ) ^ ((1 : ℂ) / 2) *
        gaussLoc D A v (2 * ((k.val : ℤ) - 1)))) • B.e (k + 1) := by
  sorry

/-- **wh:tau-rank**: at `s0 = 1/6`, `range τ = ℂ u` with `u = shellVec` of the Weyl basis. -/
theorem local_coefficient_rank_one (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (τ : T.V →ₗ[ℂ] T.V)
    (hτ : ∀ f ∈ sectionSpace L T (1 / 6),
      jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f)) :
    LinearMap.range τ = Submodule.span ℂ {shellVec D A B.weyl} := by
  sorry

/-- The local theta space `Θ_v = M(1/6) I(T, 1/6) ⊆ I(T.weyl, -1/6)`. -/
def thetaSpace (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v) :
    Submodule ℂ (L.L → T.V) :=
  Submodule.span ℂ (intertwine L μ '' {f | IsSection L T (1 / 6) f})

theorem thetaSpace_le (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v) :
    thetaSpace L T μ ≤ sectionSpace L T.weyl (-(1 / 6)) ∧ IsRtrStable (thetaSpace L T μ) := by
  sorry

/-- **wh:theta-unique** (top; replaces KP Cor. I.3.6): on `Θ_v`, `𝒥` takes values in `ℂ u`, and every
Whittaker functional is `c ∘ 𝒥`. -/
theorem whittaker_theta_unique (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) :
    (∀ f ∈ thetaSpace L T μ, jacquet L A μ f ∈ Submodule.span ℂ {shellVec D A B.weyl}) ∧
    ∀ Λ : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (thetaSpace L T μ) Λ →
      ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ thetaSpace L T μ, Λ f = c (jacquet L A μ f) := by
  sorry

/-- **wh:dim-le-one**: `dim Wh(Θ_v) ≤ 1`, in the form used for normalization. -/
theorem whittaker_theta_dim_le_one (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (Λ₁ Λ₂ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (h₁ : IsWhittakerOn L A (thetaSpace L T μ) Λ₁) (h₂ : IsWhittakerOn L A (thetaSpace L T μ) Λ₂) :
    ∀ f ∈ thetaSpace L T μ, ∀ f' ∈ thetaSpace L T μ, Λ₂ f * Λ₁ f' = Λ₂ f' * Λ₁ f := by
  sorry

end LocalWhit

end ArtinPrimitiveRoots.A1.Theta
