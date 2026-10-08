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

/-- **wh:two-cell** (KP Cor. I.3.4/Lemma I.3.2 replaced): every Whittaker functional on `I(T, s)`
is `c ∘ 𝒥` (every `s ∈ ℂ`). -/
theorem whittaker_twoCell (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (Λ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerOn L A (sectionSpace L T s) Λ) :
    ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ sectionSpace L T s, Λ f = c (jacquet L A μ f) := by
  sorry

/-- **wh:coinvariants** (left exactness of `ψ`-twisted coinvariants, Bernstein–Zelevinsky): a
Whittaker functional on an `rtr`-stable subspace of `I(T, s)` extends to `I(T, s)`. -/
theorem whittaker_extend (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (s : ℂ) (W : Submodule ℂ (L.L → T.V)) (hW : W ≤ sectionSpace L T s) (hst : IsRtrStable W)
    (Λ : (L.L → T.V) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerOn L A W Λ) :
    ∃ Λ' : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (sectionSpace L T s) Λ' ∧
      ∀ f ∈ W, Λ' f = Λ f := by
  sorry

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
