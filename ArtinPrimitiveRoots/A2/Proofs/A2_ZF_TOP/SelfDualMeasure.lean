import ArtinPrimitiveRoots.A1.SLattice
import ArtinPrimitiveRoots.Theta.LocalInt
import ArtinPrimitiveRoots.A2.Proofs.A2_ZF_TOP.ArchFourier
import Mathlib.LinearAlgebra.Countable
import Mathlib.Analysis.Distribution.TemperateGrowth

open NumberField IsDedekindDomain
open MeasureTheory
open Filter
open scoped Classical
open scoped Topology
open scoped Valued
open ArtinPrimitiveRoots.A1
open ArtinPrimitiveRoots.A1.Theta
open Valued.integer
open scoped WithZero

namespace ArtinPrimitiveRoots.Proofs.a2_zf_top

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private instance adicCompletion_separableSpace (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    TopologicalSpace.SeparableSpace (v.adicCompletion F) := by
  letI : Countable F := by
    letI : Countable ℚ := inferInstance
    exact Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  exact TopologicalSpace.SeparableSpace.of_denseRange
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap (K := F))

private instance adicCompletion_secondCountable (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    SecondCountableTopology (v.adicCompletion F) :=
  UniformSpace.secondCountable_of_separable (v.adicCompletion F)

private instance adicCompletion_properSpace (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    ProperSpace (v.adicCompletion F) := by
  letI : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).RankOne :=
    HeightOneSpectrum.instRankOneAdicCompletion F v
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  exact (@Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (v.adicCompletion F) ℤᵐ⁰ _ _
      (inferInstance : Valued (v.adicCompletion F) ℤᵐ⁰) inferInstance).mpr
    ⟨inferInstance,
      inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
      inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩

private instance adicCompletion_locallyCompactSpace (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    LocallyCompactSpace (v.adicCompletion F) := by
  letI : ProperSpace (v.adicCompletion F) := adicCompletion_properSpace v
  infer_instance

private instance adicCompletion_sigmaCompact (v : ArtinPrimitiveRoots.A1.FinPlace F) :
    SigmaCompactSpace (v.adicCompletion F) := inferInstance

noncomputable local instance instMeasurableFS (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    MeasurableSpace S.FS := borel S.FS
local instance instBorelFS (S : ArtinPrimitiveRoots.A1.SData F CE condη) : BorelSpace S.FS :=
  ⟨rfl⟩

private theorem sFS_prod_eq_borel (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    (Prod.instMeasurableSpace : MeasurableSpace S.FS) = instMeasurableFS S := by
  change (Prod.instMeasurableSpace : MeasurableSpace S.FS) = borel S.FS
  letI : MeasurableSpace S.FS := Prod.instMeasurableSpace
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq

@[instance_reducible] private noncomputable def sFSProductMeas (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    MeasurableSpace S.FS := Prod.instMeasurableSpace

@[instance_reducible] private noncomputable def sFSBorelMeas (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    MeasurableSpace S.FS := borel S.FS

private theorem sFSProductMeas_eq_borel (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    sFSProductMeas S = sFSBorelMeas S := by
  letI : MeasurableSpace S.FS := sFSProductMeas S
  letI : BorelSpace S.FS := inferInstance
  exact BorelSpace.measurable_eq

/-- A finite local component of the global additive character cannot be trivial: otherwise a
vector supported at that component would lie in the annihilator of the S-integer lattice. -/
private theorem sData_addChar_nontrivial_of_mem (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (v : S.Sf) :
    ∃ x : v.1.adicCompletion F, A.ψ v.1 x ≠ 1 := by
  classical
  by_contra h
  push Not at h
  let y : S.FS := (fun w => if w = v then 1 else 0, fun _ => 0)
  have hyann : y ∈ S.annihilator A S.diagR := by
    intro z hz
    rcases hz with ⟨r, rfl⟩
    have hfin (q : S.Sf) :
        A.ψ q.1 ((S.diag (r : F) * y).1 q) = 1 := by
      by_cases hq : q = v
      · subst q
        simpa [y] using h ((S.diag (r : F)).1 v)
      · simp [y, hq]
    have harch (q : InfinitePlace F) :
        ArtinPrimitiveRoots.A1.psiC ((S.diag (r : F) * y).2 q) = 1 := by
      simp [ArtinPrimitiveRoots.A1.psiC, y]
    change (∏ q : S.Sf, A.ψ q.1 ((S.diag (r : F) * y).1 q)) *
      ∏ q : InfinitePlace F, ArtinPrimitiveRoots.A1.psiC
        ((S.diag (r : F) * y).2 q) = 1
    have hfp : (∏ q : S.Sf, A.ψ q.1 ((S.diag (r : F) * y).1 q)) = 1 :=
      Finset.prod_eq_one (fun q _ => hfin q)
    have hap : (∏ q : InfinitePlace F, ArtinPrimitiveRoots.A1.psiC
        ((S.diag (r : F) * y).2 q)) = 1 :=
      Finset.prod_eq_one (fun q _ => harch q)
    rw [hfp, hap]
    simp
  have hdual := S.diagR_eq_annihilator D A
  have hyr : y ∈ S.diagR := by rw [hdual]; exact hyann
  obtain ⟨r, hr⟩ := hyr
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hrw : w.embedding (r : F) = 0 := by
    have h := congrArg (fun z : S.FS => z.2 w) hr
    simpa [y, ArtinPrimitiveRoots.A1.SData.diag] using h
  have hr0 : (r : F) = 0 := (RingHom.injective w.embedding) (by simpa using hrw)
  have hrv : algebraMap F (v.1.adicCompletion F) (r : F) = 1 := by
    have h := congrArg (fun z : S.FS => z.1 v) hr
    simpa [y, ArtinPrimitiveRoots.A1.SData.diag] using h
  have : (0 : v.1.adicCompletion F) = 1 := by simpa [hr0] using hrv
  exact zero_ne_one this

/-- A nontrivial finite-place character that is trivial on the valuation ring has a last
valuation ball on which it is trivial. -/
private theorem localAddChar_conductor (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (hO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ x = 1)
    (hne : ∃ x : v.adicCompletion F, ψ x ≠ 1) :
    ∃ c : ℤ, 0 ≤ c ∧ (∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1) ∧
      ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1 := by
  let P : ℤ → Prop := fun n => ∀ x : v.adicCompletion F,
    Valued.v x ≤ WithZero.exp n → ψ x = 1
  have hP0 : P 0 := by
    intro x hx
    apply hO
    change Valued.v x ≤ 1
    simpa using hx
  obtain ⟨a, ha⟩ := hne
  have hav : Valued.v a ≠ 0 := by
    intro hv
    have ha0 : a = 0 := (Valuation.zero_iff (Valued.v : Valuation _ _)).mp hv
    exact ha (by simpa [ha0])
  lift Valued.v a to ℤ using hav with k hk
  have hbound : ∃ b : ℤ, ∀ n : ℤ, P n → n ≤ b := by
    refine ⟨k - 1, ?_⟩
    intro n hn
    by_contra hnot
    have hkn : k ≤ n := by omega
    have hball : Valued.v a ≤ WithZero.exp n := by
      rw [← hk]
      exact (WithZero.exp_le_exp).2 hkn
    exact ha (hn a hball)
  obtain ⟨c, hc, hcmax⟩ := Int.exists_greatest_of_bdd hbound ⟨0, hP0⟩
  have hnot : ¬ P (c + 1) := by
    intro hp
    have hle := hcmax (c + 1) hp
    omega
  change ¬ (∀ x : v.adicCompletion F,
    Valued.v x ≤ WithZero.exp (c + 1) → ψ x = 1) at hnot
  push Not at hnot
  obtain ⟨x, hx, hψ⟩ := hnot
  have hc_nonneg : 0 ≤ c := by
    have hzero := hcmax 0 hP0
    omega
  exact ⟨c, hc_nonneg, hc, x, hx, hψ⟩

/-- The annihilator of a valuation ball is the complementary valuation ball determined by the
additive character's conductor. -/
private theorem localAnnBall (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (c n : ℤ)
    (hc : ∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1)
    (hboundary : ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1) :
    {y : v.adicCompletion F | ∀ x, Valued.v x ≤ WithZero.exp n → ψ (x * y) = 1} =
      {y | Valued.v y ≤ WithZero.exp (c - n)} := by
  change {y : v.adicCompletion F | ∀ x, Valued.v x ≤ WithZero.exp n → ψ (x * y) = 1} =
    {y | Valued.v y ≤ WithZero.exp (c - n)}
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyv : Valued.v y ≠ 0 := by simpa using hy0
      lift Valued.v y to ℤ using hyv with k hk
      by_contra hnot
      have hnotExp : ¬ WithZero.exp k ≤ WithZero.exp (c - n) := by
        intro hle
        exact hnot (by simpa [hk] using hle)
      have hkn : c - n < k := by
        have hnk : ¬ k ≤ c - n := by
          intro hle
          exact hnotExp ((WithZero.exp_le_exp).2 hle)
        omega
      obtain ⟨z, hzv, hzψ⟩ := hboundary
      have hz0 : z ≠ 0 := by
        intro hz
        subst z
        exact hzψ ψ.map_zero_eq_one
      have hzv0 : Valued.v z ≠ 0 := by simpa using hz0
      lift Valued.v z to ℤ using hzv0 with j hj
      have hjle : j ≤ c + 1 := by
        apply (WithZero.exp_le_exp).1
        exact hzv
      have hxval : Valued.v (z / y) ≤ WithZero.exp n := by
        have hval : Valued.v (z / y) = WithZero.exp (j - k) := by
          rw [map_div₀, ← hj, ← hk, ← WithZero.exp_sub]
        rw [hval]
        exact (WithZero.exp_le_exp).2 (by omega)
      have hxy : (z / y) * y = z := div_mul_cancel₀ z hy0
      exact hzψ (by simpa [hxy] using hy (z / y) hxval)
  · intro hy x hx
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyv : Valued.v y ≠ 0 := by simpa using hy0
      lift Valued.v y to ℤ using hyv with k hk
      have hval : Valued.v (x * y) ≤ WithZero.exp c := by
        calc
          Valued.v (x * y) = Valued.v x * Valued.v y := by simp
          _ ≤ WithZero.exp n * WithZero.exp k := by
            exact mul_le_mul' hx (by rw [← hk])
          _ = WithZero.exp (n + k) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp c := (WithZero.exp_le_exp).2 (by
            have hybound : k ≤ c - n := by
              have hy' : WithZero.exp k ≤ WithZero.exp (c - n) := by
                rw [hk]
                exact hy
              exact (WithZero.exp_le_exp).1 hy'
            omega)
      exact hc _ hval

/-- The valuation ball of exponent `n` is the image of the valuation ring under the uniformizer
power `π^n`. -/
private theorem local_ball_image (v : ArtinPrimitiveRoots.A1.FinPlace F) (n : ℤ) :
    ball v n = (fun x : v.adicCompletion F =>
      ((unifLoc v ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x) ''
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  let K := v.adicCompletion F
  let π : Kˣ := unifLoc v
  have hπval : Valued.v (π : K) = WithZero.exp (-1 : ℤ) := by
    have hπcoerce : (π : K) = algebraMap F K (unif v) := by
      change ((unif v : F) : v.adicCompletion F) = _
      rfl
    rw [hπcoerce]
    change Valued.v ((unif v : F) : K) = WithZero.exp (-1 : ℤ)
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa [unif] using (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hπpow : Valued.v ((π ^ n : Kˣ) : K) = WithZero.exp (-n) := by
    have hpow : Valued.v ((π ^ n : Kˣ) : K) = Valued.v (π : K) ^ n := by simp
    rw [hpow, hπval, ← WithZero.exp_zsmul]
    congr 1
    simp
  ext x
  constructor
  · intro hx
    refine ⟨((π ^ n : Kˣ)⁻¹ : K) * x, ?_, ?_⟩
    · change Valued.v (((π ^ n : Kˣ)⁻¹ : K) * x) ≤ 1
      rw [map_mul, map_inv₀, hπpow]
      calc
        _ = WithZero.exp n * Valued.v x := by simp
        _ ≤ WithZero.exp n * WithZero.exp (-n) :=
          mul_le_mul_of_nonneg_left hx WithZero.exp_pos.le
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · change ((π ^ n : Kˣ) : K) * (((π ^ n : Kˣ)⁻¹ : K) * x) = x
      have hne : ((π ^ n : Kˣ) : K) ≠ 0 := Units.ne_zero _
      calc
        _ = (((π ^ n : Kˣ) : K) * ((π ^ n : Kˣ) : K)⁻¹) * x := by rw [mul_assoc]
        _ = 1 * x := by rw [mul_inv_cancel₀ hne]
        _ = x := by simp
  · rintro ⟨x, hx, rfl⟩
    change Valued.v (((π ^ n : Kˣ) : K) * x) ≤ WithZero.exp (-n)
    rw [map_mul, hπpow]
    calc
      _ ≤ WithZero.exp (-n) * 1 := by
        have hx' : Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := by
          change Valued.v x ≤ 1 at hx
          exact hx
        exact mul_le_mul_of_nonneg_left hx' WithZero.exp_pos.le
      _ = WithZero.exp (-n) := by simp

/-- Haar measure of a local valuation ball, for Haar measure normalized to give the valuation
ring mass one. -/
private theorem locHaar_real_ball (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (μ : LocHaar v) (n : ℤ) :
    μ.μ.real (ball v n) = absFin v (unifLoc v ^ n) := by
  let K := v.adicCompletion F
  let O : Set K := v.adicCompletionIntegers F
  let u : Kˣ := unifLoc v ^ n
  have hOopen : IsOpen O := Valued.isOpen_valuationSubring K
  have hBopen : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hImage : ball v n = (fun x : K => (u : K) * x) '' O := by
    simpa [u] using local_ball_image v n
  have hpre : (fun x : K => (u : K) * x) ⁻¹' ball v n = O := by
    rw [hImage]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hcancel : y = x := mul_left_cancel₀ (Units.ne_zero u) hxy
      simpa [hcancel] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let f : K → ℝ := Set.indicator (ball v n) 1
  have hf : (fun x : K => f ((u : K) * x)) = Set.indicator O 1 := by
    funext x
    have hxmem : (u : K) * x ∈ ball v n ↔ x ∈ O := by
      change x ∈ (fun x : K => (u : K) * x) ⁻¹' ball v n ↔ x ∈ O
      rw [hpre]
    by_cases hx : x ∈ O <;> simp [f, hx, hxmem]
  have hscale := LocHaar.integral_comp_mul μ u f
  rw [hf] at hscale
  have hOint : ∫ x : K, Set.indicator O 1 x ∂μ.μ = μ.μ.real O :=
    integral_indicator_one (μ := μ.μ) hOopen.measurableSet
  have hBint : ∫ x : K, Set.indicator (ball v n) 1 x ∂μ.μ =
      μ.μ.real (ball v n) :=
    integral_indicator_one (μ := μ.μ) hBopen.measurableSet
  rw [hOint, hBint] at hscale
  have hOvol : μ.μ.real O = 1 := by
    change (μ.μ O).toReal = 1
    rw [μ.norm_O]
    rfl
  change μ.μ.real O = (absFin v u)⁻¹ * μ.μ.real (ball v n) at hscale
  rw [hOvol] at hscale
  have hnonzero : absFin v u ≠ 0 := (absFin_pos (Units.ne_zero u)).ne'
  field_simp [hnonzero] at hscale
  simpa [u] using hscale.symm

/-- The real scale that makes the normalized local Haar measure self-dual for a character of
conductor exponent `d`. -/
private noncomputable def localSelfDualScale (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (d : ℕ) : ℝ :=
  (Real.sqrt (absFin v (unifLoc v ^ (-(d : ℤ)))))⁻¹

private noncomputable def localSelfDualMeasure (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (μ : LocHaar v) (d : ℕ) : Measure (v.adicCompletion F) :=
  ENNReal.ofReal (localSelfDualScale v d) • μ.μ

private theorem localSelfDualScale_pos (v : ArtinPrimitiveRoots.A1.FinPlace F) (d : ℕ) :
    0 < localSelfDualScale v d := by
  have hunit : (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Units.ne_zero (unifLoc v))
  have ha : 0 < absFin v (unifLoc v ^ (-(d : ℤ))) := absFin_pos hunit
  unfold localSelfDualScale
  exact inv_pos.mpr (Real.sqrt_pos.2 ha)

private theorem localSelfDualScale_square (v : ArtinPrimitiveRoots.A1.FinPlace F) (d : ℕ) :
    localSelfDualScale v d ^ 2 * absFin v (unifLoc v ^ (-(d : ℤ))) = 1 := by
  let a : ℝ := absFin v (unifLoc v ^ (-(d : ℤ)))
  have ha : 0 < a := by
    dsimp [a]
    have hunit : (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) ≠ 0 :=
      zpow_ne_zero _ (Units.ne_zero (unifLoc v))
    exact absFin_pos hunit
  change (Real.sqrt a)⁻¹ ^ 2 * a = 1
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtne : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  calc
    (Real.sqrt a)⁻¹ ^ 2 * a = (Real.sqrt a)⁻¹ ^ 2 * Real.sqrt a ^ 2 := by rw [hsq]
    _ = 1 := by field_simp [hsqrtne]

private theorem localSelfDualMeasure_isHaar (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (μ : LocHaar v) (d : ℕ) : Measure.IsAddHaarMeasure (localSelfDualMeasure v μ d) := by
  let c : ENNReal := ENNReal.ofReal (localSelfDualScale v d)
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.ofReal_ne_zero_iff.mpr (localSelfDualScale_pos v d)
  have hctop : c < ⊤ := by
    dsimp [c]
    exact (ENNReal.ofReal_lt_top : ENNReal.ofReal (localSelfDualScale v d) < ⊤)
  change Measure.IsAddHaarMeasure (c • μ.μ)
  exact Measure.IsAddHaarMeasure.smul μ.μ hc0 hctop.ne

private theorem localSelfDualMeasure_real_ball (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (μ : LocHaar v) (d : ℕ) (n : ℤ) :
    (localSelfDualMeasure v μ d).real (ball v n) =
      localSelfDualScale v d * absFin v (unifLoc v ^ n) := by
  simp [localSelfDualMeasure, localSelfDualScale, locHaar_real_ball]

private theorem localSelfDualMeasure_ball_pair (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (μ : LocHaar v) (d : ℕ) (n : ℤ) :
    (localSelfDualMeasure v μ d).real (ball v n) *
      (localSelfDualMeasure v μ d).real (ball v (- (d : ℤ) - n)) = 1 := by
  rw [localSelfDualMeasure_real_ball, localSelfDualMeasure_real_ball]
  have hnorm' : absFin v ((unifLoc v : v.adicCompletion F) ^ n *
      (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)) =
      absFin v ((unifLoc v : v.adicCompletion F) ^ n) *
        absFin v ((unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)) := by
    calc
      _ = ‖(unifLoc v : v.adicCompletion F) ^ n *
          (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)‖ := absFin_eq_norm _ _
      _ = ‖(unifLoc v : v.adicCompletion F) ^ n‖ *
          ‖(unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n)‖ := norm_mul _ _
      _ = _ := by rw [← absFin_eq_norm, ← absFin_eq_norm]
  have hpow : unifLoc v ^ n * unifLoc v ^ (-(d : ℤ) - n) =
      unifLoc v ^ (-(d : ℤ)) := by
    rw [← zpow_add]
    congr 1 <;> ring
  have hpow' : ((unifLoc v ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
      ((unifLoc v ^ (-(d : ℤ) - n) : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        ((unifLoc v ^ (-(d : ℤ)) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
    exact congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hpow
  have hpow'' : (unifLoc v : v.adicCompletion F) ^ n *
      (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ) - n) =
        (unifLoc v : v.adicCompletion F) ^ (-(d : ℤ)) := by
    simpa only [Units.val_zpow_eq_zpow_val] using hpow'
  calc
    _ = localSelfDualScale v d ^ 2 *
        (absFin v (unifLoc v ^ n) * absFin v (unifLoc v ^ (-(d : ℤ) - n))) := by ring
    _ = localSelfDualScale v d ^ 2 * absFin v
        (unifLoc v ^ n * unifLoc v ^ (-(d : ℤ) - n)) := by
          exact congrArg (fun x : ℝ => localSelfDualScale v d ^ 2 * x) hnorm'.symm
    _ = localSelfDualScale v d ^ 2 * absFin v (unifLoc v ^ (-(d : ℤ))) := by rw [hpow'']
    _ = 1 := localSelfDualScale_square v d

private theorem localBall_add (v : ArtinPrimitiveRoots.A1.FinPlace F) (n : ℤ)
    {x y : v.adicCompletion F} (hx : x ∈ ball v n) (hy : y ∈ ball v n) :
    x + y ∈ ball v n := by
  change Valued.v (x + y) ≤ WithZero.exp (-n)
  exact (Valued.v.map_add x y).trans (max_le hx hy)

private theorem localBall_neg (v : ArtinPrimitiveRoots.A1.FinPlace F) (n : ℤ)
    {x : v.adicCompletion F} (hx : x ∈ ball v n) : -x ∈ ball v n := by
  change Valued.v (-x) ≤ WithZero.exp (-n)
  change Valued.v x ≤ WithZero.exp (-n) at hx
  simpa using hx

/-- The annihilator of a local valuation ball, viewed as a set of frequencies. -/
private def localAnnSet (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ) : Set (v.adicCompletion F) :=
  {a | ∀ x, Valued.v x ≤ WithZero.exp (-n) → ψ (a * x) = 1}

/-- Integral of a local additive character over a valuation ball: it is the ball's mass on its
annihilator and zero off it. -/
private theorem localCharIntegral_ball (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (n : ℤ) (a : v.adicCompletion F) :
    ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ =
      (localAnnSet v ψ n).indicator (fun _ => (μ.real (ball v n) : ℂ)) a := by
  classical
  have hBopen : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  by_cases ha : a ∈ localAnnSet v ψ n
  · have hf : (fun x => (ball v n).indicator (fun x => ψ (-(a * x))) x) =
        (ball v n).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ ball v n
      · have hψ : ψ (-(a * x)) = 1 := by
          rw [ψ.map_neg_eq_inv, ha x (by simpa [ball] using hx), inv_one]
        simp [hx, hψ]
      · simp [hx]
    have hmass :
        ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ =
          (μ.real (ball v n) : ℂ) := by
      calc
        _ = ∫ x, (ball v n).indicator (fun _ => (1 : ℂ)) x ∂μ := by rw [hf]
        _ = μ.real (ball v n) • (1 : ℂ) := integral_indicator_const (1 : ℂ)
          hBopen.measurableSet
        _ = (μ.real (ball v n) : ℂ) := by simp
    have hind : (localAnnSet v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a = (μ.real (ball v n) : ℂ) := by
      simp [ha]
    exact hmass.trans hind.symm
  · have hfalse : ¬ (∀ x, Valued.v x ≤ WithZero.exp (-n) → ψ (a * x) = 1) := by
      simpa [localAnnSet] using ha
    push Not at hfalse
    obtain ⟨b, hb, hψb⟩ := hfalse
    have hψbneg : ψ (-(a * b)) ≠ 1 := by
      rw [ψ.map_neg_eq_inv]
      intro h
      exact hψb (inv_eq_one.mp h)
    let f : v.adicCompletion F → ℂ :=
      fun x => (ball v n).indicator (fun x => ψ (-(a * x))) x
    have hcoset (x : v.adicCompletion F) : b + x ∈ ball v n ↔ x ∈ ball v n := by
      constructor
      · intro hbx
        have h := localBall_add v n hbx (localBall_neg v n hb)
        simpa [add_assoc] using h
      · intro hx
        have h := localBall_add v n hb hx
        simpa [add_comm] using h
    have hchar (x : v.adicCompletion F) :
        ψ (-(a * (b + x))) = ψ (-(a * b)) * ψ (-(a * x)) := by
      calc
        ψ (-(a * (b + x))) = ψ (-(a * b) + -(a * x)) := by congr 1 <;> ring
        _ = ψ (-(a * b)) * ψ (-(a * x)) := ψ.map_add_eq_mul _ _
    have htrans (x : v.adicCompletion F) :
        f (b + x) = ψ (-(a * b)) * f x := by
      by_cases hx : x ∈ ball v n
      · have hbx : b + x ∈ ball v n := (hcoset x).2 hx
        simp [f, hx, hbx, hchar x]
      · have hbx : b + x ∉ ball v n := fun h => hx ((hcoset x).1 h)
        simp [f, hx, hbx]
    let I : ℂ := ∫ x, f x ∂μ
    have hI : I = ψ (-(a * b)) * I := by
      calc
        I = ∫ x, f (b + x) ∂μ := (integral_add_left_eq_self f b).symm
        _ = ∫ x, ψ (-(a * b)) * f x ∂μ := by rw [show (fun x => f (b + x)) =
          fun x => ψ (-(a * b)) * f x from funext htrans]
        _ = ψ (-(a * b)) * I := by rw [integral_const_mul]
    have hprod : (ψ (-(a * b)) - 1) * I = 0 := by
      calc
        (ψ (-(a * b)) - 1) * I = ψ (-(a * b)) * I - I := by ring
        _ = I - I := by rw [← hI]
        _ = 0 := by ring
    have hI0 : I = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hψbneg (sub_eq_zero.mp h)).elim
      · exact h
    have hmass : ∫ x, (ball v n).indicator (fun x => ψ (-(a * x))) x ∂μ = 0 := by
      simpa [I, f] using hI0
    have hind : (localAnnSet v ψ n).indicator
        (fun _ => (μ.real (ball v n) : ℂ)) a = 0 := by
      simp [ha]
    exact hmass.trans hind.symm

private noncomputable def localFourier (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F) : ℂ :=
  ∫ y, ψ (-(x * y)) * f y ∂μ

private theorem localFourier_ball_formula (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (n : ℤ) (a : v.adicCompletion F) :
    localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) a =
      (localAnnSet v ψ n).indicator (fun _ => (μ.real (ball v n) : ℂ)) a := by
  have hfun : (fun y => ψ (-(a * y)) * (ball v n).indicator (fun _ => (1 : ℂ)) y) =
      (ball v n).indicator (fun y => ψ (-(a * y))) := by
    funext y
    by_cases hy : y ∈ ball v n <;> simp [hy]
  change ∫ y, ψ (-(a * y)) * (ball v n).indicator (fun _ => (1 : ℂ)) y ∂μ = _
  rw [hfun]
  exact localCharIntegral_ball v ψ μ n a

private theorem localFourier_const_mul (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    (c : ℂ) (f : v.adicCompletion F → ℂ) (x : v.adicCompletion F) :
    localFourier v ψ μ (fun y => c * f y) x = c * localFourier v ψ μ f x := by
  unfold localFourier
  have hfun : (fun y => ψ (-(x * y)) * (c * f y)) =
      fun y => c * (ψ (-(x * y)) * f y) := by
    funext y
    ring
  rw [hfun, integral_const_mul]

private theorem localFourier_finset_sum (ι : Type) (s : Finset ι)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (ψ : AddChar (v.adicCompletion F) ℂ)
    (μ : Measure (v.adicCompletion F)) (g : ι → v.adicCompletion F → ℂ)
    (x : v.adicCompletion F)
    (hint : ∀ i ∈ s, Integrable (fun y => ψ (-(x * y)) * g i y) μ) :
    localFourier v ψ μ (fun y => ∑ i ∈ s, g i y) x =
      ∑ i ∈ s, localFourier v ψ μ (g i) x := by
  unfold localFourier
  calc
    (∫ y, ψ (-(x * y)) * (∑ i ∈ s, g i y) ∂μ) =
        ∫ y, ∑ i ∈ s, ψ (-(x * y)) * g i y ∂μ := by
          congr 1
          funext y
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∫ y, ψ (-(x * y)) * g i y ∂μ :=
      integral_finsetSum s hint

/-- A translate of a valuation ball. -/
private def localTranslateBall (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : v.adicCompletion F) (n : ℤ) : Set (v.adicCompletion F) :=
  {x | x - a ∈ ball v n}

private theorem localTranslateBall_eq_of_intersection (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a b : v.adicCompletion F) (n : ℤ)
    (h : ∃ x, x ∈ localTranslateBall v a n ∧ x ∈ localTranslateBall v b n) :
    localTranslateBall v a n = localTranslateBall v b n := by
  obtain ⟨x, hxa, hxb⟩ := h
  have hba : b - a ∈ ball v n := by
    have hxb' : -(x - b) ∈ ball v n := localBall_neg v n hxb
    have h := localBall_add v n hxa hxb'
    have heq : (x - a) + -(x - b) = b - a := by ring
    simpa only [heq] using h
  have hab : a - b ∈ ball v n := by
    have h := localBall_neg v n hba
    simpa using h
  ext y
  constructor
  · intro hy
    have h := localBall_add v n hy hab
    have heq : (y - a) + (a - b) = y - b := by ring
    change y - b ∈ ball v n
    rw [← heq]
    exact h
  · intro hy
    have h := localBall_add v n hy hba
    have heq : (y - b) + (b - a) = y - a := by ring
    change y - a ∈ ball v n
    rw [← heq]
    exact h

private theorem localTranslateBall_eq_or_disjoint (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a b : v.adicCompletion F) (n : ℤ) :
    localTranslateBall v a n = localTranslateBall v b n ∨
      Disjoint (localTranslateBall v a n) (localTranslateBall v b n) := by
  by_cases h : ∃ x, x ∈ localTranslateBall v a n ∧ x ∈ localTranslateBall v b n
  · exact Or.inl (localTranslateBall_eq_of_intersection v a b n h)
  · right
    rw [Set.disjoint_left]
    intro x hxa hxb
    exact h ⟨x, hxa, hxb⟩

private theorem localTranslateBall_open (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : v.adicCompletion F) (n : ℤ) : IsOpen (localTranslateBall v a n) := by
  have hB : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  change IsOpen ((fun y : v.adicCompletion F => y - a) ⁻¹' ball v n)
  exact hB.preimage (continuous_id.sub continuous_const)

private theorem localTranslateBall_mem_nhds (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : v.adicCompletion F) (n : ℤ) : localTranslateBall v a n ∈ 𝓝 a := by
  letI : Valued (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := inferInstance
  apply (localTranslateBall_open v a n).mem_nhds
  change Valued.v (a - a) ≤ WithZero.exp (-n)
  simpa using (show Valued.v (0 : v.adicCompletion F) ≤ WithZero.exp (-n) by simp)

private theorem exists_localTranslateBall_subset_nhds
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (a : v.adicCompletion F)
    {U : Set (v.adicCompletion F)} (hU : U ∈ 𝓝 a) :
    ∃ n : ℤ, localTranslateBall v a n ⊆ U := by
  letI : Valued (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := inferInstance
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  let γ' : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1
  have hγ' : γ' ≠ 0 := by
    dsimp [γ']
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m < γ' := by
    refine ⟨WithZero.log γ' - 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hγ']
    exact (WithZero.exp_lt_exp).mpr (by omega)
  refine ⟨-m, ?_⟩
  intro y hy
  apply hγ
  change Valued.v.restrict (y - a) < γ.1
  apply (Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
  exact (show Valued.v (y - a) ≤ WithZero.exp m from by
    simpa [localTranslateBall, ball] using hy).trans_lt hm

private theorem localSupport_compact_of_locallyConstant
    {K : Type} [TopologicalSpace K] [Zero ℂ] (f : K → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    IsCompact (Function.support f) := by
  have hclosed : IsClosed (Function.support f) := by
    have hzero : IsOpen (f ⁻¹' ({0} : Set ℂ)) := by
      convert hf.isOpen_fiber (0 : ℂ) using 1
      ext x
      simp
    have hs : Function.support f = (f ⁻¹' ({0} : Set ℂ))ᶜ := by
      ext x
      simp [Function.mem_support]
    rw [hs]
    exact hzero.isClosed_compl
  have hcompact : IsCompact (closure (Function.support f)) := hfc
  exact hcompact.of_isClosed_subset hclosed subset_closure

private theorem localTranslateBall_subset_of_exponent_le
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (a : v.adicCompletion F)
    {n m : ℤ} (hnm : n ≤ m) :
    localTranslateBall v a m ⊆ localTranslateBall v a n := by
  intro x hx
  change Valued.v (x - a) ≤ WithZero.exp (-m) at hx
  change Valued.v (x - a) ≤ WithZero.exp (-n)
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem localBall_subset_of_exponent_le
    (v : ArtinPrimitiveRoots.A1.FinPlace F) {n m : ℤ} (hnm : n ≤ m) :
    ball v m ⊆ ball v n := by
  intro x hx
  change Valued.v x ≤ WithZero.exp (-m) at hx
  change Valued.v x ≤ WithZero.exp (-n)
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

/-- A compactly supported locally constant function is constant on a finite cover by translates
of one common valuation ball. -/
private theorem exists_finset_localTranslateBall_cover
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ n : ℤ, ∃ T : Finset {x // x ∈ Function.support f},
      (∀ y ∈ T, ∀ z, z ∈ localTranslateBall v y.1 n → f z = f y.1) ∧
      Function.support f ⊆ ⋃ y ∈ T, localTranslateBall v y.1 n := by
  let supp : Set (v.adicCompletion F) := Function.support f
  have hcompact : IsCompact supp := localSupport_compact_of_locallyConstant f hf hfc
  let rad (x : v.adicCompletion F) : ℤ :=
    Classical.choose (exists_localTranslateBall_subset_nhds v x
      (U := {y | f y = f x}) (hf.eventually_eq x))
  have hrad (x : v.adicCompletion F) :
      localTranslateBall v x (rad x) ⊆ {y | f y = f x} :=
    Classical.choose_spec (exists_localTranslateBall_subset_nhds v x
      (U := {y | f y = f x}) (hf.eventually_eq x))
  have hcover : supp ⊆ ⋃ x : supp, localTranslateBall v x.1 (rad x.1) := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ ball v (rad x)
    simpa [sub_self, ball]
  obtain ⟨T₀, hT₀⟩ := hcompact.elim_finite_subcover
    (fun x : supp => localTranslateBall v x.1 (rad x.1))
    (fun x => localTranslateBall_open v x.1 (rad x.1)) hcover
  let N : ℤ := if hT : T₀.Nonempty then T₀.sup' hT (fun x => rad x.1) else 0
  have hrad_le (x : supp) (hx : x ∈ T₀) : rad x.1 ≤ N := by
    by_cases hT : T₀.Nonempty
    · have hle := Finset.le_sup' (f := fun y : supp => rad y.1) hx
      simpa only [N, dif_pos hT] using hle
    · have hzero : T₀ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      simp [hzero] at hx
  have hconstN (x : supp) : ∀ z, z ∈ localTranslateBall v x.1 N → f z = f x.1 := by
    intro z hz
    rcases Set.mem_iUnion₂.mp (hT₀ x.2) with ⟨y, hyT, hyx⟩
    have hN : rad y.1 ≤ N := hrad_le y hyT
    have hzy : z - x.1 ∈ ball v N := by simpa [localTranslateBall] using hz
    have hyx' : x.1 - y.1 ∈ ball v (rad y.1) := by
      simpa [localTranslateBall] using hyx
    have hzy' : z - x.1 ∈ ball v (rad y.1) :=
      localBall_subset_of_exponent_le v hN hzy
    have hsum := localBall_add v (rad y.1) hzy' hyx'
    have heq : (z - x.1) + (x.1 - y.1) = z - y.1 := by ring
    have hz_y : z - y.1 ∈ ball v (rad y.1) := by
      rw [← heq]
      exact hsum
    have hzconst := hrad y.1 hz_y
    have hxconst := hrad y.1 hyx
    exact hzconst.trans hxconst.symm
  have hcoverN : supp ⊆ ⋃ x : supp, localTranslateBall v x.1 N := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    change x - x ∈ ball v N
    simpa [sub_self, ball]
  obtain ⟨T, hT⟩ := hcompact.elim_finite_subcover
    (fun x : supp => localTranslateBall v x.1 N)
    (fun x => localTranslateBall_open v x.1 N) hcoverN
  refine ⟨N, T, ?_, ?_⟩
  · intro y hy z hz
    exact hconstN y z hz
  · simpa [supp] using hT

private theorem exists_localFiniteTest_ball_expansion
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (f : v.adicCompletion F → ℂ)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ n : ℤ, ∃ balls : Finset (Set (v.adicCompletion F)),
      ∃ rep : Set (v.adicCompletion F) → v.adicCompletion F,
        (∀ B ∈ balls, B = localTranslateBall v (rep B) n) ∧
        (∀ B ∈ balls, ∀ x ∈ B, f x = f (rep B)) ∧
        (∀ B ∈ balls, rep B ∈ Function.support f) ∧
        (∀ B ∈ balls, ∀ B' ∈ balls, B ≠ B' → Disjoint B B') ∧
        ∀ x, f x = ∑ B ∈ balls, B.indicator (fun _ => f (rep B)) x := by
  classical
  obtain ⟨n, T, hconst, hcover⟩ :=
    exists_finset_localTranslateBall_cover v f hf hfc
  let balls : Finset (Set (v.adicCompletion F)) :=
    T.image (fun y => localTranslateBall v y.1 n)
  let rep : Set (v.adicCompletion F) → v.adicCompletion F := fun B =>
    if hB : B ∈ balls then (Classical.choose (Finset.mem_image.mp hB)).1 else 0
  have hrep_eq (B : Set (v.adicCompletion F)) (hB : B ∈ balls) :
      localTranslateBall v (rep B) n = B := by
    dsimp [rep]
    rw [dif_pos hB]
    exact (Classical.choose_spec (Finset.mem_image.mp hB)).2
  have hrep_support (B : Set (v.adicCompletion F)) (hB : B ∈ balls) :
      rep B ∈ Function.support f := by
    dsimp [rep]
    rw [dif_pos hB]
    exact (Classical.choose (Finset.mem_image.mp hB)).2
  have hball_const (B : Set (v.adicCompletion F)) (hB : B ∈ balls)
      (x : v.adicCompletion F) (hx : x ∈ B) : f x = f (rep B) := by
    let y : {x // x ∈ Function.support f} := Classical.choose (Finset.mem_image.mp hB)
    have hyT : y ∈ T := (Classical.choose_spec (Finset.mem_image.mp hB)).1
    have hyEq : localTranslateBall v y.1 n = B :=
      (Classical.choose_spec (Finset.mem_image.mp hB)).2
    have hrep : rep B = y.1 := by simp [rep, hB, y]
    have hx' : x ∈ localTranslateBall v y.1 n := by simpa [hyEq] using hx
    rw [hrep]
    exact hconst y hyT x hx'
  have hball_subset_support (B : Set (v.adicCompletion F)) (hB : B ∈ balls) :
      B ⊆ Function.support f := by
    intro x hx
    have hrepnz : f (rep B) ≠ 0 := by
      simpa [Function.mem_support] using hrep_support B hB
    have hxne : f x ≠ 0 := by
      rw [hball_const B hB x hx]
      exact hrepnz
    simpa [Function.mem_support] using hxne
  have hballs_disjoint (B B' : Set (v.adicCompletion F))
      (hB : B ∈ balls) (hB' : B' ∈ balls) (hne : B ≠ B') : Disjoint B B' := by
    rcases localTranslateBall_eq_or_disjoint v (rep B) (rep B') n with heq | hdisj
    · have : B = B' := by rw [hrep_eq B hB, hrep_eq B' hB'] at heq; exact heq
      exact (hne this).elim
    · simpa [hrep_eq B hB, hrep_eq B' hB'] using hdisj
  have hballs_cover : Function.support f ⊆ ⋃ B ∈ balls, B := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨y, hyT, hxy⟩
    exact Set.mem_iUnion₂.mpr ⟨localTranslateBall v y.1 n,
      Finset.mem_image.mpr ⟨y, hyT, rfl⟩, hxy⟩
  have hexpand (x : v.adicCompletion F) :
      f x = ∑ B ∈ balls, B.indicator (fun _ => f (rep B)) x := by
    by_cases hx : x ∈ Function.support f
    · obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.mp (hballs_cover hx)
      have hterm : B.indicator (fun _ => f (rep B)) x = f x := by
        simp only [Set.indicator_of_mem hxB]
        exact (hball_const B hB x hxB).symm
      calc
        f x = B.indicator (fun _ => f (rep B)) x := hterm.symm
        _ = ∑ B' ∈ balls, B'.indicator (fun _ => f (rep B')) x := by
          symm
          apply Finset.sum_eq_single_of_mem B hB
          intro B' hB' hne
          have hdisj := hballs_disjoint B' B hB' hB hne
          have hxnot : x ∉ B' := by
            intro hx'
            exact (Set.disjoint_left.mp hdisj) hx' hxB
          simp [hxnot]
    · have hfx : f x = 0 := by
        by_contra hne
        exact hx (by simpa [Function.mem_support] using hne)
      rw [hfx]
      symm
      apply Finset.sum_eq_zero
      intro B hB
      have hxnot : x ∉ B := fun hxB => hx (hball_subset_support B hB hxB)
      simp [hxnot]
  exact ⟨n, balls, rep, (fun B hB => (hrep_eq B hB).symm), hball_const,
    hrep_support, (fun B hB B' hB' hne => hballs_disjoint B B' hB hB' hne), hexpand⟩

private theorem localBall_compact (v : ArtinPrimitiveRoots.A1.FinPlace F) (n : ℤ) :
    IsCompact (ball v n) := by
  let K := v.adicCompletion F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F)),
        inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)))⟩
  have hOcompact : IsCompact (v.adicCompletionIntegers F : Set K) := by
    have hset : (v.adicCompletionIntegers F : Set K) = Metric.closedBall (0 : K) 1 := by
      change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
      exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  rw [local_ball_image v n]
  exact hOcompact.image (by fun_prop)

private theorem localTranslateBall_isClopen (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : v.adicCompletion F) (n : ℤ) : IsClopen (localTranslateBall v a n) := by
  have hball : IsClosed (ball v n) := (localBall_compact v n).isClosed
  have hBopen : IsOpen (ball v n) :=
    v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  exact ⟨(hball.preimage (continuous_id.sub continuous_const)),
    (hBopen.preimage (continuous_id.sub continuous_const))⟩

private theorem localTranslateBall_compact (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (a : v.adicCompletion F) (n : ℤ) : IsCompact (localTranslateBall v a n) := by
  have hEq : localTranslateBall v a n =
      (fun x : v.adicCompletion F => a + x) '' ball v n := by
    ext y
    constructor
    · intro hy
      have hy' : y - a ∈ ball v n := by simpa [localTranslateBall] using hy
      exact ⟨y - a, hy', by ring⟩
    · rintro ⟨x, hx, rfl⟩
      change a + x - a ∈ ball v n
      simpa using hx
  rw [hEq]
  exact (localBall_compact v n).image (continuous_const.add continuous_id)

private theorem localTranslateBall_indicator_locallyConstant
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (a : v.adicCompletion F) (n : ℤ) (c : ℂ) :
    IsLocallyConstant ((localTranslateBall v a n).indicator (fun _ => c)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ localTranslateBall v a n
  · refine ⟨localTranslateBall v a n, (localTranslateBall_isClopen v a n).isOpen, hx, ?_⟩
    intro y hy
    simp [hx, hy]
  · refine ⟨(localTranslateBall v a n)ᶜ,
      (localTranslateBall_isClopen v a n).isClosed.isOpen_compl, hx, ?_⟩
    intro y hy
    have hy' : y ∉ localTranslateBall v a n := hy
    simp [hx, hy']

private theorem localTranslateBall_indicator_hasCompactSupport
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (a : v.adicCompletion F) (n : ℤ) (c : ℂ) :
    HasCompactSupport ((localTranslateBall v a n).indicator (fun _ => c)) := by
  apply HasCompactSupport.intro' (localTranslateBall_compact v a n)
    (localTranslateBall_isClopen v a n).isClosed
  intro x hx
  simp [hx]

private theorem localAddChar_locallyConstant (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (hO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ x = 1)
    (a : v.adicCompletion F) : IsLocallyConstant (fun x => ψ (-(a * x))) := by
  letI : Valued (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := inferInstance
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  let O : Set (v.adicCompletion F) := v.adicCompletionIntegers F
  let U : Set (v.adicCompletion F) := {y | a * (y - x) ∈ O}
  have hOeq : O = ball v 0 := by
    ext y
    simp [O, ball, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hOopen : IsOpen O := by
    rw [hOeq]
    exact v.isOpen_setOf_valued_le (K := F) WithZero.exp_ne_zero
  have hUopen : IsOpen U := by
    change IsOpen ((fun y : v.adicCompletion F => a * (y - x)) ⁻¹' O)
    exact hOopen.preimage (by fun_prop)
  have hxU : x ∈ U := by simp [U, O]
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  have htO : a * (y - x) ∈ v.adicCompletionIntegers F := by simpa [U, O] using hy
  have hnegO : -(a * (y - x)) ∈ v.adicCompletionIntegers F := by
    change Valued.v (-(a * (y - x))) ≤ 1
    change Valued.v (a * (y - x)) ≤ 1 at htO
    simpa using htO
  calc
    ψ (-(a * y)) = ψ (-(a * x) + -(a * (y - x))) := by congr 1 <;> ring
    _ = ψ (-(a * x)) * ψ (-(a * (y - x))) := ψ.map_add_eq_mul _ _
    _ = ψ (-(a * x)) := by rw [hO _ hnegO]; simp

private theorem localChar_mul_integrable (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (hO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ x = 1)
    (μ : Measure (v.adicCompletion F)) (f : v.adicCompletion F → ℂ)
    [Measure.IsAddHaarMeasure μ] (a : v.adicCompletion F)
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ψ (-(a * x)) * f x) μ := by
  have hcont : Continuous (fun x => ψ (-(a * x)) * f x) :=
    (localAddChar_locallyConstant v ψ hO a).continuous.mul hf.continuous
  exact hcont.integrable_of_hasCompactSupport (hfc.mul_left)

/-- Fourier transform of a translated ball, by translation invariance of Haar measure. -/
private theorem localFourier_translate_ball (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (a : v.adicCompletion F) (n : ℤ)
    (y : v.adicCompletion F) :
    localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ))) y =
      ψ (-(y * a)) * localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) y := by
  unfold localFourier
  have hchar (t : v.adicCompletion F) : ψ (-(y * (a + t))) =
      ψ (-(y * a)) * ψ (-(y * t)) := by
    calc
      ψ (-(y * (a + t))) = ψ (-(y * a) + -(y * t)) := by congr 1 <;> ring
      _ = ψ (-(y * a)) * ψ (-(y * t)) := ψ.map_add_eq_mul _ _
  have hind (t : v.adicCompletion F) :
      (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) (a + t) =
        (ball v n).indicator (fun _ => (1 : ℂ)) t := by
    have hmem : a + t ∈ localTranslateBall v a n ↔ t ∈ ball v n := by
      change a + t - a ∈ ball v n ↔ t ∈ ball v n
      simp
    by_cases ht : t ∈ ball v n <;> simp [ht, hmem]
  calc
    (∫ t, ψ (-(y * t)) * (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) t ∂μ) =
        ∫ t, ψ (-(y * (a + t))) *
          (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) (a + t) ∂μ := by
            exact (integral_add_left_eq_self _ a).symm
    _ = ∫ t, (ψ (-(y * a)) * ψ (-(y * t))) *
          (ball v n).indicator (fun _ => (1 : ℂ)) t ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            rw [hchar, hind]
    _ = ∫ t, ψ (-(y * a)) *
          (ψ (-(y * t)) * (ball v n).indicator (fun _ => (1 : ℂ)) t) ∂μ := by
            apply integral_congr_ae
            filter_upwards with t
            ring
    _ = ψ (-(y * a)) *
          ∫ t, ψ (-(y * t)) * (ball v n).indicator (fun _ => (1 : ℂ)) t ∂μ := by
            rw [integral_const_mul]
    _ = ψ (-(y * a)) *
          localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) y := rfl

/-- Fourier inversion for a translated compact-open ball. -/
private theorem localFourier_translate_ball_inversion (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (c n : ℤ)
    (hc : ∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1)
    (hboundary : ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1)
    (hvol : μ.real (ball v n) * μ.real (ball v (-c - n)) = 1)
    (a x : v.adicCompletion F) :
    localFourier v ψ μ
        (localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ)))) x =
      (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) (-x) := by
  let B' : Set (v.adicCompletion F) := ball v (-c - n)
  let mB : ℂ := (μ.real (ball v n) : ℂ)
  have hAnn1Set : localAnnSet v ψ n = B' := by
    have h := localAnnBall v ψ c (-n) hc hboundary
    simpa [localAnnSet, B', ball, mul_comm] using h
  have hAnn2Set : localAnnSet v ψ (-c - n) = ball v n := by
    have h := localAnnBall v ψ c (c + n) hc hboundary
    simpa [localAnnSet, ball, mul_comm] using h
  have hvolC : mB * (μ.real B' : ℂ) = 1 := by
    dsimp [mB, B']
    exact_mod_cast hvol
  have hfirst :
      localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ))) =
        fun y => ψ (-(y * a)) * B'.indicator (fun _ => mB) y := by
    funext y
    rw [localFourier_translate_ball, localFourier_ball_formula, hAnn1Set]
  have hsecond :
      localFourier v ψ μ (fun y => ψ (-(y * a)) * B'.indicator (fun _ => mB) y) x =
        mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) (x + a) := by
    unfold localFourier
    have hchar (y : v.adicCompletion F) :
        ψ (-(x * y)) * ψ (-(y * a)) = ψ (-((x + a) * y)) := by
      calc
        ψ (-(x * y)) * ψ (-(y * a)) = ψ (-(x * y) + -(a * y)) := by
          rw [← ψ.map_add_eq_mul]
          congr 1 <;> ring
        _ = ψ (-((x + a) * y)) := by congr 1 <;> ring
    have hint : (fun y => ψ (-(x * y)) * (ψ (-(y * a)) * B'.indicator (fun _ => mB) y)) =
        fun y => mB * (B'.indicator (fun y => ψ (-((x + a) * y))) y) := by
      funext y
      by_cases hy : y ∈ B'
      · simp only [Set.indicator_of_mem hy]
        calc
          ψ (-(x * y)) * (ψ (-(y * a)) * mB) =
              (ψ (-(x * y)) * ψ (-(y * a))) * mB := by ring
          _ = ψ (-((x + a) * y)) * mB := by rw [hchar]
          _ = mB * ψ (-((x + a) * y)) := by ring
      · simp only [Set.indicator_of_notMem hy, mul_zero, zero_mul]
    rw [hint, integral_const_mul, localCharIntegral_ball, hAnn2Set]
  have hneg : -x ∈ localTranslateBall v a n ↔ x + a ∈ ball v n := by
    change -x - a ∈ ball v n ↔ x + a ∈ ball v n
    have heq : -x - a = -(x + a) := by ring
    rw [heq]
    constructor
    · intro hx
      have hh := localBall_neg v n hx
      simpa only [neg_neg] using hh
    · intro hx
      exact localBall_neg v n hx
  have hresult :
      localFourier v ψ μ
        (localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ)))) x =
          mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) (x + a) := by
    calc
      _ = localFourier v ψ μ
          (fun y => ψ (-(y * a)) * B'.indicator (fun _ => mB) y) x := by rw [hfirst]
      _ = mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) (x + a) := hsecond
  by_cases hx : x + a ∈ ball v n
  · calc
      localFourier v ψ μ
          (localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ)))) x
          = mB * (μ.real B' : ℂ) := by rw [hresult]; simp [hx]
      _ = 1 := hvolC
      _ = (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hneg, hx]
  · calc
      localFourier v ψ μ
          (localFourier v ψ μ ((localTranslateBall v a n).indicator (fun _ => (1 : ℂ)))) x
          = 0 := by rw [hresult]; simp [hx]
      _ = (localTranslateBall v a n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hneg, hx]

/-- Fourier inversion for a finite linear combination of translated valuation balls. -/
private theorem localFourier_finset_translateBall_inversion (ι : Type) (s : Finset ι)
    (v : ArtinPrimitiveRoots.A1.FinPlace F) (ψ : AddChar (v.adicCompletion F) ℂ)
    (hO : ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → ψ y = 1)
    (μ : Measure (v.adicCompletion F)) [Measure.IsAddHaarMeasure μ]
    (c n : ℤ) (hc : ∀ y, Valued.v y ≤ WithZero.exp c → ψ y = 1)
    (hboundary : ∃ y, Valued.v y ≤ WithZero.exp (c + 1) ∧ ψ y ≠ 1)
    (hvol : μ.real (ball v n) * μ.real (ball v (-c - n)) = 1)
    (a : ι → v.adicCompletion F) (coef : ι → ℂ) (x : v.adicCompletion F) :
    localFourier v ψ μ
      (localFourier v ψ μ (fun y => ∑ i ∈ s,
        coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y)) x =
      (fun y => ∑ i ∈ s,
        coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y) (-x) := by
  let B' : Set (v.adicCompletion F) := ball v (-c - n)
  let mB : ℂ := (μ.real (ball v n) : ℂ)
  let g : ι → v.adicCompletion F → ℂ := fun i y =>
    coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y
  let ghat : ι → v.adicCompletion F → ℂ := fun i y =>
    coef i * (ψ (-(y * a i)) * B'.indicator (fun _ => mB) y)
  have hAnn1Set : localAnnSet v ψ n = B' := by
    have h := localAnnBall v ψ c (-n) hc hboundary
    simpa [localAnnSet, B', ball, mul_comm] using h
  have hFirstInt (y : v.adicCompletion F) (i : ι) (hi : i ∈ s) :
      Integrable (fun z => ψ (-(y * z)) * g i z) μ := by
    have hbase := localChar_mul_integrable v ψ hO μ
      ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ))) y
      (localTranslateBall_indicator_locallyConstant v (a i) n 1)
      (localTranslateBall_indicator_hasCompactSupport v (a i) n 1)
    have hmul := hbase.const_mul (coef i)
    have heq : (fun z => ψ (-(y * z)) * g i z) =
        fun z => coef i * (ψ (-(y * z)) *
          (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) z) := by
      funext z
      dsimp [g]
      ring
    rw [heq]
    exact hmul
  have hFirst : localFourier v ψ μ
      (fun y => ∑ i ∈ s,
        coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y) =
      fun y => ∑ i ∈ s, ghat i y := by
    funext y
    rw [localFourier_finset_sum ι s v ψ μ g y (hFirstInt y)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      localFourier v ψ μ (g i) y =
          coef i * localFourier v ψ μ
            ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ))) y := by
              exact localFourier_const_mul v ψ μ (coef i)
                ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ))) y
      _ = ghat i y := by
        dsimp [ghat, B', mB]
        rw [localFourier_translate_ball, localFourier_ball_formula, hAnn1Set]
  have hsecondInt (i : ι) (hi : i ∈ s) :
      Integrable (fun y => ψ (-(x * y)) * ghat i y) μ := by
    let centered : Set (v.adicCompletion F) := localTranslateBall v 0 (-c - n)
    let fcentered : v.adicCompletion F → ℂ :=
      centered.indicator (fun _ => coef i * mB)
    have hbase := localChar_mul_integrable v ψ hO μ fcentered (x + a i)
      (localTranslateBall_indicator_locallyConstant v 0 (-c - n) (coef i * mB))
      (localTranslateBall_indicator_hasCompactSupport v 0 (-c - n) (coef i * mB))
    have hchar (y : v.adicCompletion F) :
        ψ (-(x * y)) * ψ (-(y * a i)) = ψ (-((x + a i) * y)) := by
      calc
        ψ (-(x * y)) * ψ (-(y * a i)) =
            ψ (-(x * y) + -(a i * y)) := by
              rw [← ψ.map_add_eq_mul]
              congr 1 <;> ring
        _ = ψ (-((x + a i) * y)) := by congr 1 <;> ring
    have hfun : (fun y => ψ (-(x * y)) * ghat i y) =
      fun y => ψ (-((x + a i) * y)) * fcentered y := by
      funext y
      by_cases hy : y ∈ B'
      · have hy' : y ∈ centered := by simpa [centered, B', localTranslateBall, ball] using hy
        simp only [ghat, centered, Set.indicator_of_mem hy, Set.indicator_of_mem hy']
        have hfc : fcentered y = coef i * mB := by simp [fcentered, centered, hy']
        rw [hfc]
        calc
          ψ (-(x * y)) * (coef i * (ψ (-(y * a i)) * mB)) =
              (coef i * mB) * (ψ (-(x * y)) * ψ (-(y * a i))) := by ring
          _ = (coef i * mB) * ψ (-((x + a i) * y)) := by rw [hchar]
          _ = ψ (-((x + a i) * y)) * (coef i * mB) := by ring
      · have hy' : y ∉ centered := by
          simpa [centered, B', localTranslateBall, ball] using hy
        simp [ghat, hy, centered, hy', fcentered]
    rw [hfun]
    exact hbase
  calc
    localFourier v ψ μ
        (localFourier v ψ μ (fun y => ∑ i ∈ s,
          coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y)) x
        = localFourier v ψ μ (fun y => ∑ i ∈ s, ghat i y) x := by rw [hFirst]
    _ = ∑ i ∈ s, localFourier v ψ μ (ghat i) x :=
      localFourier_finset_sum ι s v ψ μ ghat x hsecondInt
    _ = ∑ i ∈ s, coef i * (localTranslateBall v (a i) n).indicator
          (fun _ => (1 : ℂ)) (-x) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hfactor (y : v.adicCompletion F) :
                ψ (-(y * a i)) * B'.indicator (fun _ => mB) y =
                  localFourier v ψ μ ((localTranslateBall v (a i) n).indicator
                    (fun _ => (1 : ℂ))) y := by
              calc
                _ = ψ (-(y * a i)) * (localAnnSet v ψ n).indicator
                    (fun _ => mB) y := by rw [← hAnn1Set]
                _ = ψ (-(y * a i)) * localFourier v ψ μ
                    ((ball v n).indicator (fun _ => (1 : ℂ))) y := by
                      rw [← localFourier_ball_formula v ψ μ n y]
                _ = localFourier v ψ μ
                    ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ))) y :=
                      (localFourier_translate_ball v ψ μ (a i) n y).symm
            calc
              localFourier v ψ μ (ghat i) x =
                  coef i * localFourier v ψ μ
                    (localFourier v ψ μ
                      ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)))) x := by
                      have hfun : ghat i = fun y => coef i *
                          localFourier v ψ μ
                            ((localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ))) y := by
                        funext y
                        dsimp [ghat]
                        rw [hfactor]
                      rw [hfun, localFourier_const_mul]
              _ = coef i * (localTranslateBall v (a i) n).indicator
                    (fun _ => (1 : ℂ)) (-x) := by
                      rw [localFourier_translate_ball_inversion v ψ μ c n hc hboundary hvol
                        (a i) x]
    _ = (fun y => ∑ i ∈ s,
          coef i * (localTranslateBall v (a i) n).indicator (fun _ => (1 : ℂ)) y) (-x) := rfl


private theorem localSelfDualMeasure_test_inversion
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (v : S.Sf)
    (μ : LocHaar v.1) (fdata : S.FiniteTest v) (x : v.1.adicCompletion F) :
    let ψ := A.ψ v.1
    let hcond := localAddChar_conductor v.1 ψ (A.integral v.1)
      (sData_addChar_nontrivial_of_mem D S A v)
    let d := (Classical.choose hcond).toNat
    localFourier v.1 ψ (localSelfDualMeasure v.1 μ d)
      (localFourier v.1 ψ (localSelfDualMeasure v.1 μ d) fdata.1) x = fdata.1 (-x) := by
  classical
  let ψ := A.ψ v.1
  have hO : ∀ y : v.1.adicCompletion F,
      y ∈ v.1.adicCompletionIntegers F → ψ y = 1 := A.integral v.1
  let hcond := localAddChar_conductor v.1 ψ hO
    (sData_addChar_nontrivial_of_mem D S A v)
  let c : ℤ := Classical.choose hcond
  have hcSpec := Classical.choose_spec hcond
  have hc0 : 0 ≤ c := hcSpec.1
  have hc : ∀ y, Valued.v y ≤ WithZero.exp c → ψ y = 1 := hcSpec.2.1
  have hboundary : ∃ y, Valued.v y ≤ WithZero.exp (c + 1) ∧ ψ y ≠ 1 := hcSpec.2.2
  let d : ℕ := c.toNat
  have hcd : (d : ℤ) = c := Int.toNat_of_nonneg hc0
  let μsd : Measure (v.1.adicCompletion F) := localSelfDualMeasure v.1 μ d
  haveI : Measure.IsAddHaarMeasure μsd := localSelfDualMeasure_isHaar v.1 μ d
  rcases fdata with ⟨f, ⟨hcont, hcompact, hloc⟩⟩
  obtain ⟨n, balls, rep, hrep, hballconst, hrepSupport, hdisj, hexpand⟩ :=
    exists_localFiniteTest_ball_expansion v.1 f hloc hcompact
  let coef : Set (v.1.adicCompletion F) → ℂ := fun B => f (rep B)
  have hsum : f = fun z => ∑ B ∈ balls,
      coef B * (localTranslateBall v.1 (rep B) n).indicator (fun _ => (1 : ℂ)) z := by
    funext z
    rw [hexpand z]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hz : z ∈ B
    · have hz' : z ∈ localTranslateBall v.1 (rep B) n := by
        rw [← hrep B hB]
        exact hz
      calc
        B.indicator (fun _ => f (rep B)) z = f (rep B) := by simp [hz]
        _ = coef B * (localTranslateBall v.1 (rep B) n).indicator
              (fun _ => (1 : ℂ)) z := by simp [coef, hz']
    · have hz' : z ∉ localTranslateBall v.1 (rep B) n := by
        intro h
        exact hz (by rw [← hrep B hB] at h; exact h)
      calc
        B.indicator (fun _ => f (rep B)) z = 0 := by simp [hz]
        _ = coef B * (localTranslateBall v.1 (rep B) n).indicator
              (fun _ => (1 : ℂ)) z := by simp [coef, hz']
  have hvol : μsd.real (ball v.1 n) * μsd.real (ball v.1 (-c - n)) = 1 := by
    have hp := localSelfDualMeasure_ball_pair v.1 μ d n
    simpa [μsd, hcd] using hp
  have hinv := localFourier_finset_translateBall_inversion
    (Set (v.1.adicCompletion F)) balls v.1 ψ hO μsd c n hc hboundary hvol rep coef x
  calc
    localFourier v.1 ψ μsd (localFourier v.1 ψ μsd f) x =
        localFourier v.1 ψ μsd
          (localFourier v.1 ψ μsd
            (fun z => ∑ B ∈ balls,
              coef B * (localTranslateBall v.1 (rep B) n).indicator (fun _ => (1 : ℂ)) z)) x := by
          rw [hsum]
    _ = (fun z => ∑ B ∈ balls,
          coef B * (localTranslateBall v.1 (rep B) n).indicator (fun _ => (1 : ℂ)) z) (-x) := hinv
    _ = f (-x) := by rw [hsum]

private noncomputable def localConductorExponent
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (v : S.Sf) : ℕ :=
  let ψ := A.ψ v.1
  let hO : ∀ y : v.1.adicCompletion F,
      y ∈ v.1.adicCompletionIntegers F → ψ y = 1 := A.integral v.1
  let hcond := localAddChar_conductor v.1 ψ hO
    (sData_addChar_nontrivial_of_mem D S A v)
  (Classical.choose hcond).toNat

private theorem isLocallyConstant_finset_sum
    {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert f hf
  induction s using Finset.induction_on with
  | empty =>
      intro f hf
      change IsLocallyConstant (fun _ : X => (0 : ℂ))
      exact IsLocallyConstant.const (0 : ℂ)
  | @insert i s hi ih =>
      intro f hf
      simp only [Finset.sum_insert hi]
      exact IsLocallyConstant.comp₂ (hf i (by simp))
        (ih f (fun j hj => hf j (by simp [hj]))) (· + ·)

private theorem hasCompactSupport_finset_sum
    {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  revert f hf
  induction s using Finset.induction_on with
  | empty =>
      intro f hf
      have hz : (fun x : X => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => (0 : ℂ) := by
        funext x
        simp
      rw [hz]
      refine HasCompactSupport.intro' isCompact_empty isClosed_empty ?_
      intro x hx
      simp at hx
      rfl
  | @insert i s hi ih =>
      intro f hf
      simp only [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih f (fun j hj => hf j (by simp [hj])))

private theorem localSelfDualMeasure_fourier_test
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (v : S.Sf)
    (μ : LocHaar v.1) (fdata : S.FiniteTest v) :
    ∃ fhat : S.FiniteTest v,
      fhat.1 = localFourier v.1 (A.ψ v.1)
        (localSelfDualMeasure v.1 μ (localConductorExponent D S A v)) fdata.1 := by
  classical
  let ψ := A.ψ v.1
  have hO : ∀ y : v.1.adicCompletion F,
      y ∈ v.1.adicCompletionIntegers F → ψ y = 1 := A.integral v.1
  let hcond := localAddChar_conductor v.1 ψ hO
    (sData_addChar_nontrivial_of_mem D S A v)
  let c : ℤ := Classical.choose hcond
  have hcSpec := Classical.choose_spec hcond
  have hc0 : 0 ≤ c := hcSpec.1
  have hc : ∀ y, Valued.v y ≤ WithZero.exp c → ψ y = 1 := hcSpec.2.1
  have hboundary : ∃ y, Valued.v y ≤ WithZero.exp (c + 1) ∧ ψ y ≠ 1 := hcSpec.2.2
  let d : ℕ := c.toNat
  have hcd : (d : ℤ) = c := Int.toNat_of_nonneg hc0
  let μsd : Measure (v.1.adicCompletion F) := localSelfDualMeasure v.1 μ d
  haveI : Measure.IsAddHaarMeasure μsd := localSelfDualMeasure_isHaar v.1 μ d
  rcases fdata with ⟨f, ⟨hcont, hcompact, hloc⟩⟩
  obtain ⟨n, balls, rep, hrep, hballconst, hrepSupport, hdisj, hexpand⟩ :=
    exists_localFiniteTest_ball_expansion v.1 f hloc hcompact
  let coef : Set (v.1.adicCompletion F) → ℂ := fun B => f (rep B)
  let bInd : Set (v.1.adicCompletion F) → v.1.adicCompletion F → ℂ := fun B =>
    (localTranslateBall v.1 (rep B) n).indicator (fun _ => (1 : ℂ))
  have hsum : f = fun z => ∑ B ∈ balls, coef B * bInd B z := by
    funext z
    rw [hexpand z]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hz : z ∈ B
    · have hz' : z ∈ localTranslateBall v.1 (rep B) n := by rw [← hrep B hB]; exact hz
      simp [coef, bInd, hz, hz']
    · have hz' : z ∉ localTranslateBall v.1 (rep B) n := by
        intro h
        exact hz (by rw [← hrep B hB] at h; exact h)
      simp [coef, bInd, hz, hz']
  let B' : Set (v.1.adicCompletion F) := ball v.1 (-c - n)
  let mB : ℂ := (μsd.real (ball v.1 n) : ℂ)
  let ghat : Set (v.1.adicCompletion F) → v.1.adicCompletion F → ℂ := fun B y =>
    coef B * (ψ (-(y * rep B)) * B'.indicator (fun _ => mB) y)
  have hAnn : localAnnSet v.1 ψ n = B' := by
    have h := localAnnBall v.1 ψ c (-n) hc hboundary
    simpa [localAnnSet, B', ball, mul_comm] using h
  have hfirstInt (y : v.1.adicCompletion F) (B : Set (v.1.adicCompletion F))
      (hB : B ∈ balls) : Integrable (fun z => ψ (-(y * z)) * (coef B * bInd B z)) μsd := by
    have hbase := localChar_mul_integrable v.1 ψ hO μsd (bInd B) y
      (localTranslateBall_indicator_locallyConstant v.1 (rep B) n 1)
      (localTranslateBall_indicator_hasCompactSupport v.1 (rep B) n 1)
    have hmul : Integrable (fun z => coef B * (ψ (-(y * z)) * bInd B z)) μsd :=
      hbase.const_mul (coef B)
    have heq : (fun z => ψ (-(y * z)) * (coef B * bInd B z)) =
        fun z => coef B * (ψ (-(y * z)) * bInd B z) := by
      funext z
      ring
    rw [heq]
    exact hmul
  have hFT : localFourier v.1 ψ μsd f = fun y => ∑ B ∈ balls, ghat B y := by
    funext y
    rw [hsum, localFourier_finset_sum (Set (v.1.adicCompletion F)) balls v.1 ψ μsd
      (fun B z => coef B * bInd B z) y (fun B hB => hfirstInt y B hB)]
    apply Finset.sum_congr rfl
    intro B hB
    dsimp [ghat, bInd, B', mB]
    rw [localFourier_const_mul, localFourier_translate_ball, localFourier_ball_formula, hAnn]
  have htermLC (B : Set (v.1.adicCompletion F)) : IsLocallyConstant (ghat B) := by
    have hchar : IsLocallyConstant (fun y => ψ (-(y * rep B))) := by
      have h := localAddChar_locallyConstant v.1 ψ hO (rep B)
      convert h using 1
      funext y
      congr 1
      rw [mul_comm]
    have hball : IsLocallyConstant (B'.indicator (fun _ => mB)) := by
      have h := localTranslateBall_indicator_locallyConstant v.1 0 (-c - n) mB
      convert h using 1
      ext y
      simp [B', localTranslateBall, ball]
    exact IsLocallyConstant.comp₂ (IsLocallyConstant.const (coef B))
      (IsLocallyConstant.comp₂ hchar hball (· * ·)) (· * ·)
  have htermCompact (B : Set (v.1.adicCompletion F)) : HasCompactSupport (ghat B) := by
    have hball : HasCompactSupport (B'.indicator (fun _ => mB)) := by
      have h := localTranslateBall_indicator_hasCompactSupport v.1 0 (-c - n) mB
      convert h using 1
      ext y
      simp [B', localTranslateBall, ball]
    exact hball.mul_left.mul_left
  have hsumLC := isLocallyConstant_finset_sum balls ghat (fun B hB => htermLC B)
  have hsumCompact := hasCompactSupport_finset_sum balls ghat (fun B hB => htermCompact B)
  refine ⟨⟨fun y => ∑ B ∈ balls, ghat B y, hsumLC.continuous, hsumCompact, hsumLC⟩, ?_⟩
  exact hFT.symm

/-- Fourier inversion on one compact-open local ball for the self-dual local Haar scaling. -/
private theorem localFourier_ball_inversion (v : ArtinPrimitiveRoots.A1.FinPlace F)
    (ψ : AddChar (v.adicCompletion F) ℂ) (μ : Measure (v.adicCompletion F))
    [Measure.IsAddHaarMeasure μ] (c n : ℤ)
    (hc : ∀ x, Valued.v x ≤ WithZero.exp c → ψ x = 1)
    (hboundary : ∃ x, Valued.v x ≤ WithZero.exp (c + 1) ∧ ψ x ≠ 1)
    (hvol : μ.real (ball v n) * μ.real (ball v (-c - n)) = 1)
    (x : v.adicCompletion F) :
    localFourier v ψ μ (localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x =
      (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by
  let B' : Set (v.adicCompletion F) := ball v (-c - n)
  let mB : ℂ := (μ.real (ball v n) : ℂ)
  have hAnn1Set : localAnnSet v ψ n = B' := by
    have h := localAnnBall v ψ c (-n) hc hboundary
    simpa [localAnnSet, B', ball, mul_comm] using h
  have hAnn2Set : localAnnSet v ψ (-c - n) = ball v n := by
    have h := localAnnBall v ψ c (c + n) hc hboundary
    simpa [localAnnSet, ball, mul_comm] using h
  have hFhat : localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) =
      B'.indicator (fun _ => mB) := by
    funext y
    calc
      localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ))) y =
          (localAnnSet v ψ n).indicator (fun _ => mB) y := by
            exact localFourier_ball_formula v ψ μ n y
      _ = B'.indicator (fun _ => mB) y := by rw [hAnn1Set]
  have htrans (y : v.adicCompletion F) :
      ψ (-(x * y)) * B'.indicator (fun _ => mB) y =
        mB * B'.indicator (fun y => ψ (-(x * y))) y := by
    by_cases hy : y ∈ B' <;> simp [hy, mul_comm]
  have hsecond : localFourier v ψ μ (B'.indicator (fun _ => mB)) x =
      mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := by
    unfold localFourier
    have hloc : (fun y => ψ (-(x * y)) * B'.indicator (fun _ => mB) y) =
        fun y => mB * B'.indicator (fun y => ψ (-(x * y))) y := funext htrans
    rw [hloc, integral_const_mul, localCharIntegral_ball]
    rw [hAnn2Set]
  have hvolC : mB * (μ.real B' : ℂ) = 1 := by
    dsimp [mB]
    exact_mod_cast hvol
  have hxneg : -x ∈ ball v n ↔ x ∈ ball v n := by
    constructor <;> intro hx
    · have h := localBall_neg v n hx
      simpa using h
    · exact localBall_neg v n hx
  have hresult :
      localFourier v ψ μ (localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x =
        mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := by
    calc
      _ = localFourier v ψ μ (B'.indicator (fun _ => mB)) x := by rw [hFhat]
      _ = mB * (ball v n).indicator (fun _ => (μ.real B' : ℂ)) x := hsecond
  by_cases hx : x ∈ ball v n
  · calc
      localFourier v ψ μ (localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x
          = mB * (μ.real B' : ℂ) := by rw [hresult]; simp [hx]
      _ = 1 := hvolC
      _ = (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hxneg, hx]
  · calc
      localFourier v ψ μ (localFourier v ψ μ ((ball v n).indicator (fun _ => (1 : ℂ)))) x
          = 0 := by rw [hresult]; simp [hx]
      _ = (ball v n).indicator (fun _ => (1 : ℂ)) (-x) := by simp [hxneg, hx]

private noncomputable def localSelfDualAt
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) (v : S.Sf) :
    Measure (v.1.adicCompletion F) :=
  localSelfDualMeasure v.1 (μ v.1) (localConductorExponent D S A v)

private theorem localSelfDualAt_sigmaFinite
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) (v : S.Sf) :
    SigmaFinite (localSelfDualAt D S A μ v) := by
  letI : SigmaCompactSpace (v.1.adicCompletion F) := adicCompletion_sigmaCompact v.1
  letI : Measure.IsAddHaarMeasure (localSelfDualAt D S A μ v) :=
    localSelfDualMeasure_isHaar v.1 (μ v.1) (localConductorExponent D S A v)
  infer_instance

private noncomputable def sSelfDualMeasureProd
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) :
    @Measure S.FS Prod.instMeasurableSpace :=
  (Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v).prod
    (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F))

private noncomputable abbrev sFSULiftProductMeas (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    MeasurableSpace (ULift.{0} S.FS) := @ULift.instMeasurableSpace S.FS (sFSProductMeas S)

@[instance_reducible] private noncomputable local instance instMeasurableULiftProd
    (S : ArtinPrimitiveRoots.A1.SData F CE condη) : MeasurableSpace (ULift.{0} S.FS) :=
  sFSULiftProductMeas S

private noncomputable def sFSUpAddEquiv (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    S.FS ≃+ ULift.{0} S.FS where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv := fun x => by cases x; rfl
  map_add' _ _ := rfl

private theorem sFSUp_measurable_prod (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    @Measurable S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S) ULift.up := by
  letI : MeasurableSpace S.FS := sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := sFSULiftProductMeas S
  exact measurable_up

private theorem sFSDown_measurable_prod (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    @Measurable (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S) (sFSProductMeas S) ULift.down := by
  letI : MeasurableSpace S.FS := sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := sFSULiftProductMeas S
  exact measurable_down

private noncomputable def sFSUpProdMeasEquiv (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    @MeasurableEquiv S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S) := by
  letI : MeasurableSpace S.FS := sFSProductMeas S
  letI : MeasurableSpace (ULift.{0} S.FS) := sFSULiftProductMeas S
  exact @MeasurableEquiv.mk S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
    (sFSUpAddEquiv S).toEquiv (sFSUp_measurable_prod S) (sFSDown_measurable_prod S)

private noncomputable def sFSDownAddEquiv (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    ULift.{0} S.FS ≃+ S.FS := (sFSUpAddEquiv S).symm

private noncomputable def sFSDownBorelMeasEquiv (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    @MeasurableEquiv (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S) (sFSBorelMeas S) := by
  letI : MeasurableSpace (ULift.{0} S.FS) := sFSULiftProductMeas S
  letI : MeasurableSpace S.FS := sFSBorelMeas S
  have hProdBorel := sFSProductMeas_eq_borel S
  have hdown : @Measurable (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S)
      (sFSBorelMeas S) ULift.down :=
    @Measurable.of_le_map (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S)
      (sFSBorelMeas S) ULift.down (by
        change sFSBorelMeas S ≤ (sFSULiftProductMeas S).map ULift.down
        calc
          _ = sFSProductMeas S := hProdBorel.symm
          _ ≤ _ := (sFSDown_measurable_prod S).le_map)
  have hup : @Measurable S.FS (ULift.{0} S.FS) (sFSBorelMeas S)
      (sFSULiftProductMeas S) ULift.up :=
    @Measurable.of_le_map S.FS (ULift.{0} S.FS) (sFSBorelMeas S)
      (sFSULiftProductMeas S) ULift.up (by
        change sFSULiftProductMeas S ≤ (sFSBorelMeas S).map ULift.up
        calc
          _ ≤ (sFSProductMeas S).map ULift.up := (sFSUp_measurable_prod S).le_map
          _ = _ := congrArg (fun m : MeasurableSpace S.FS => m.map ULift.up) hProdBorel)
  exact @MeasurableEquiv.mk (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S) (sFSBorelMeas S)
    (sFSDownAddEquiv S).toEquiv hdown hup

private theorem sFSULiftProduct_borel (S : ArtinPrimitiveRoots.A1.SData F CE condη) :
    @BorelSpace (ULift.{0} S.FS) (inferInstance : TopologicalSpace (ULift.{0} S.FS))
      (sFSULiftProductMeas S) := by
  letI : MeasurableSpace S.FS := sFSProductMeas S
  letI : BorelSpace S.FS := ⟨by
    change sFSProductMeas S = borel S.FS
    exact sFSProductMeas_eq_borel S⟩
  letI : MeasurableSpace (ULift.{0} S.FS) := sFSULiftProductMeas S
  exact ULift.instBorelSpace

private noncomputable def sSelfDualMeasureCandidate
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) : Measure S.FS := by
  exact @Measure.map (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S) (sFSBorelMeas S)
    (sFSDownBorelMeasEquiv S) <|
      @Measure.map S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
        (sFSUpProdMeasEquiv S) (sSelfDualMeasureProd D S A μ)

private theorem isAddHaarMeasure_pi {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)]
    [∀ i, SigmaCompactSpace (G i)] [∀ i, MeasurableAdd (G i)]
    (μ : ∀ i, Measure (G i)) (hμ : ∀ i, Measure.IsAddHaarMeasure (μ i)) :
    Measure.IsAddHaarMeasure (Measure.pi μ) := by
  letI : ∀ i, Measure.IsAddHaarMeasure (μ i) := hμ
  letI : ∀ i, SigmaFinite (μ i) := fun i => inferInstance
  refine {
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsAddLeftInvariant := {
      map_add_left_eq_self := by
        intro a
        have hcoord (i : ι) : MeasurePreserving (fun x : G i => a i + x) (μ i) (μ i) :=
          measurePreserving_add_left (μ i) (a i)
        exact (MeasureTheory.measurePreserving_pi μ μ (f := fun i x => a i + x) hcoord).map_eq }
    toIsOpenPosMeasure := inferInstance }

private theorem sSelfDualMeasureCandidate_isHaar
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
  (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) :
  Measure.IsAddHaarMeasure (sSelfDualMeasureCandidate D S A μ) := by
  letI : ∀ v : S.Sf, MeasurableAdd (v.1.adicCompletion F) := fun _ => inferInstance
  have hfin : Measure.IsAddHaarMeasure
      (Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v) :=
    isAddHaarMeasure_pi (fun v : S.Sf => localSelfDualAt D S A μ v)
      (fun v => localSelfDualMeasure_isHaar v.1 (μ v.1) (localConductorExponent D S A v))
  have hprod : @Measure.IsAddHaarMeasure S.FS _ _ Prod.instMeasurableSpace
      (sSelfDualMeasureProd D S A μ) := by
    letI : MeasurableSpace S.FS := Prod.instMeasurableSpace
    letI : Measure.IsAddHaarMeasure
        (Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v) := hfin
    letI : Measure.IsAddHaarMeasure
        (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)) :=
      ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
    dsimp [sSelfDualMeasureProd]
    infer_instance
  have hUp : @Measure.IsAddHaarMeasure (ULift.{0} S.FS) _ _ (sFSULiftProductMeas S)
      (@Measure.map S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
        (sFSUpAddEquiv S) (sSelfDualMeasureProd D S A μ)) := by
    letI : MeasurableSpace S.FS := sFSProductMeas S
    have hBP : @BorelSpace S.FS (inferInstance : TopologicalSpace S.FS)
        (sFSProductMeas S) := inferInstance
    have hBU := sFSULiftProduct_borel S
    exact @AddEquiv.isAddHaarMeasure_map
      S.FS (sFSProductMeas S) _ _ (sSelfDualMeasureProd D S A μ) hprod hBP
      (inferInstance : ContinuousAdd S.FS)
      (ULift.{0} S.FS) _ _ (sFSULiftProductMeas S) hBU (inferInstance)
      (sFSUpAddEquiv S) Homeomorph.ulift.symm.continuous Homeomorph.ulift.continuous
  have hDown : @Measure.IsAddHaarMeasure S.FS _ _ (sFSBorelMeas S)
      (@Measure.map (ULift.{0} S.FS) S.FS (sFSULiftProductMeas S) (sFSBorelMeas S)
        (sFSDownAddEquiv S)
        (@Measure.map S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
          (sFSUpAddEquiv S) (sSelfDualMeasureProd D S A μ))) := by
    letI : Measure.IsAddHaarMeasure
        (@Measure.map S.FS (ULift S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
          (sFSUpAddEquiv S) (sSelfDualMeasureProd D S A μ)) := hUp
    have hBU := sFSULiftProduct_borel S
    have hBTarget : @BorelSpace S.FS (inferInstance : TopologicalSpace S.FS)
        (sFSBorelMeas S) := ⟨rfl⟩
    exact @AddEquiv.isAddHaarMeasure_map
      (ULift.{0} S.FS) (sFSULiftProductMeas S) _ _
      (@Measure.map S.FS (ULift.{0} S.FS) (sFSProductMeas S) (sFSULiftProductMeas S)
        (sFSUpAddEquiv S) (sSelfDualMeasureProd D S A μ)) hUp hBU
      (inferInstance : ContinuousAdd (ULift.{0} S.FS))
      S.FS _ _ (sFSBorelMeas S) hBTarget (inferInstance)
      (sFSDownAddEquiv S) Homeomorph.ulift.continuous Homeomorph.ulift.symm.continuous
  change Measure.IsAddHaarMeasure (sSelfDualMeasureCandidate D S A μ)
  exact hDown

private theorem sFourier_product_formula
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fArch : (InfinitePlace F → ℂ) → ℂ) (x : S.FS) :
    S.fourier A (sSelfDualMeasureCandidate D S A μ)
      (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) * fArch y.2) x =
      (∏ v : S.Sf, localFourier v.1 (A.ψ v.1)
        (localSelfDualAt D S A μ v) (fFin v) (x.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v
  let μArch : Measure (InfinitePlace F → ℂ) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
  have hfinHaar : Measure.IsAddHaarMeasure μFin :=
    isAddHaarMeasure_pi (fun v : S.Sf => localSelfDualAt D S A μ v)
      (fun v => localSelfDualMeasure_isHaar v.1 (μ v.1) (localConductorExponent D S A v))
  letI : ∀ v : S.Sf, SigmaFinite (localSelfDualAt D S A μ v) :=
    fun v => localSelfDualAt_sigmaFinite D S A μ v
  letI : Measure.IsAddHaarMeasure μFin := hfinHaar
  letI : Measure.IsAddHaarMeasure μArch :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  have hFinSigma : SigmaFinite μFin := inferInstance
  letI : SigmaFinite μFin := hFinSigma
  letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
  letI : SigmaFinite μArch := Measure.IsAddHaarMeasure.sigmaFinite μArch
  letI : SFinite μFin := inferInstance
  letI : SFinite μArch := inferInstance
  let finTerm : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun y =>
    ∏ v : S.Sf, fFin v (y v) * A.ψ v.1 (-(x.1 v * y v))
  let archTerm : (InfinitePlace F → ℂ) → ℂ := fun y =>
    fArch y * ∏ w : InfinitePlace F, psiC (-(x.2 w * y w))
  have hintegrand (p : S.FS) :
      (∏ v : S.Sf, fFin v (p.1 v)) * fArch p.2 * S.e A (-(p * x)) =
      finTerm p.1 * archTerm p.2 := by
    rcases p with ⟨pf, pa⟩
    simp only [Prod.fst, Prod.snd]
    simp only [finTerm, archTerm]
    change ((∏ v : S.Sf, fFin v (pf v)) * fArch pa) *
        ((∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
          ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) =
      (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
        (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w)))
    have hswap (v : S.Sf) :
        A.ψ v.1 (-(pf v * x.1 v)) = A.ψ v.1 (-(x.1 v * pf v)) := by
      congr 1
      rw [mul_comm]
    have harchSwap (w : InfinitePlace F) :
        psiC (-(pa w * x.2 w)) = psiC (-(x.2 w * pa w)) := by
      congr 1
      rw [mul_comm]
    calc
      _ = (∏ v : S.Sf, fFin v (pf v)) * (∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) := by ring
      _ = (∏ v : S.Sf, fFin v (pf v)) *
          (∏ v : S.Sf, A.ψ v.1 (-(x.1 v * pf v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
            congr 2
            · exact congrArg _ (funext hswap)
            · exact congrArg _ (funext harchSwap)
      _ = (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
          (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
            congr 1
            simpa only [Finset.prod_mul_distrib]
  have hglobal : S.fourier A (sSelfDualMeasureCandidate D S A μ)
      (fun y : S.FS => (∏ v : S.Sf, fFin v (y.1 v)) * fArch y.2) x =
      ∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch) := by
    unfold ArtinPrimitiveRoots.A1.SData.fourier sSelfDualMeasureCandidate
    rw [MeasureTheory.integral_map_equiv (sFSDownBorelMeasEquiv S)]
    rw [MeasureTheory.integral_map_equiv (sFSUpProdMeasEquiv S)]
    unfold sSelfDualMeasureProd
    apply integral_congr_ae
    filter_upwards with p
    simpa [sFSUpProdMeasEquiv, sFSDownBorelMeasEquiv,
      sFSUpAddEquiv, sFSDownAddEquiv] using hintegrand p
  have hprod : (∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch)) =
      (∫ y, finTerm y ∂μFin) * ∫ y, archTerm y ∂μArch :=
    MeasureTheory.integral_prod_mul (μ := μFin) (ν := μArch) finTerm archTerm
  have hFin : (∫ y, finTerm y ∂μFin) =
      ∏ v : S.Sf, localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v)
        (fFin v) (x.1 v) := by
    dsimp [finTerm, μFin]
    have hPi :
        (∫ y : ∀ v : S.Sf, v.1.adicCompletion F,
          ∏ v : S.Sf, fFin v (y v) * A.ψ v.1 (-(x.1 v * y v))
            ∂(Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v)) =
          ∏ v : S.Sf, ∫ y, fFin v y * A.ψ v.1 (-(x.1 v * y))
            ∂(localSelfDualAt D S A μ v) :=
      MeasureTheory.integral_fintype_prod_eq_prod
        (fun v y => fFin v y * A.ψ v.1 (-(x.1 v * y)))
    calc
      _ = ∏ v : S.Sf, ∫ y, fFin v y * A.ψ v.1 (-(x.1 v * y))
            ∂(localSelfDualAt D S A μ v) := hPi
      _ = ∏ v : S.Sf, localFourier v.1 (A.ψ v.1)
            (localSelfDualAt D S A μ v) (fFin v) (x.1 v) := by
            apply Finset.prod_congr rfl
            intro v hv
            unfold localFourier
            apply integral_congr_ae
            filter_upwards with y
            ring
  have hArch : (∫ y, archTerm y ∂μArch) =
      ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 := by
    unfold ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier
    dsimp [archTerm, μArch]
    apply integral_congr_ae
    filter_upwards with y
    change fArch y * ∏ w : InfinitePlace F, psiC (-(x.2 w * y w)) =
      (∏ w : InfinitePlace F, psiC (-(x.2 w * y w))) * fArch y
    ring
  rw [hglobal]
  calc
    (∫ p, finTerm p.1 * archTerm p.2 ∂(μFin.prod μArch)) =
        (∫ y, finTerm y ∂μFin) * ∫ y, archTerm y ∂μArch := hprod
    _ = _ := by rw [hFin, hArch]

private theorem psiC_continuous : Continuous (ArtinPrimitiveRoots.A1.psiC) := by
  unfold ArtinPrimitiveRoots.A1.psiC
  fun_prop

private theorem psiC_norm_one (z : ℂ) : ‖psiC z‖ = 1 := by
  unfold psiC
  rw [Complex.norm_exp]
  have hre : (-(4 * Real.pi * Complex.I * (z.re : ℂ))).re = 0 := by simp
  rw [hre, Real.exp_zero]

private theorem sTensor_character_factorization
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (fFin : ∀ v : S.Sf, v.1.adicCompletion F → ℂ)
    (fArch : (InfinitePlace F → ℂ) → ℂ) (x p : S.FS) :
    (fArch p.2 * ∏ v : S.Sf, fFin v (p.1 v)) *
      S.e A (-(p * x)) =
      (∏ v : S.Sf, fFin v (p.1 v) * A.ψ v.1 (-(x.1 v * p.1 v))) *
        (fArch p.2 * ∏ w : InfinitePlace F, psiC (-(x.2 w * p.2 w))) := by
  classical
  rcases p with ⟨pf, pa⟩
  simp only [Prod.fst, Prod.snd]
  simp only [ArtinPrimitiveRoots.A1.SData.e]
  change (fArch pa * ∏ v : S.Sf, fFin v (pf v)) *
      ((∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
        ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) =
    (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
      (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w)))
  have hswap (v : S.Sf) :
      A.ψ v.1 (-(pf v * x.1 v)) = A.ψ v.1 (-(x.1 v * pf v)) := by
    congr 1
    rw [mul_comm]
  have harchSwap (w : InfinitePlace F) :
      psiC (-(pa w * x.2 w)) = psiC (-(x.2 w * pa w)) := by
    congr 1
    rw [mul_comm]
  calc
    _ = (∏ v : S.Sf, fFin v (pf v)) *
        (∏ v : S.Sf, A.ψ v.1 (-(pf v * x.1 v))) *
        (fArch pa * ∏ w : InfinitePlace F, psiC (-(pa w * x.2 w))) := by ring
    _ = (∏ v : S.Sf, fFin v (pf v)) *
        (∏ v : S.Sf, A.ψ v.1 (-(x.1 v * pf v))) *
        (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
          congr 2
          · exact congrArg _ (funext hswap)
          · exact congrArg _ (funext harchSwap)
    _ = (∏ v : S.Sf, fFin v (pf v) * A.ψ v.1 (-(x.1 v * pf v))) *
        (fArch pa * ∏ w : InfinitePlace F, psiC (-(x.2 w * pa w))) := by
          rw [← Finset.prod_mul_distrib]

private theorem sTensorFourier_integrable
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (arch : ArtinPrimitiveRoots.A1.SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (x : S.FS) :
    Integrable (fun y : S.FS => S.tensorFunction arch finite y * S.e A (-(y * x)))
      (sSelfDualMeasureCandidate D S A μ) := by
  classical
  let μFin : Measure (∀ v : S.Sf, v.1.adicCompletion F) :=
    Measure.pi fun v : S.Sf => localSelfDualAt D S A μ v
  let μArch : Measure (InfinitePlace F → ℂ) :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar (InfinitePlace F)
  let finTerm : (∀ v : S.Sf, v.1.adicCompletion F) → ℂ := fun y =>
    ∏ v : S.Sf, (finite v).1 (y v) * A.ψ v.1 (-(x.1 v * y v))
  let archTerm : (InfinitePlace F → ℂ) → ℂ := fun y =>
    arch y * ∏ w : InfinitePlace F, psiC (-(x.2 w * y w))
  letI : ∀ v : S.Sf, SigmaFinite (localSelfDualAt D S A μ v) :=
    fun v => localSelfDualAt_sigmaFinite D S A μ v
  letI : Measure.IsAddHaarMeasure μArch :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiSelfDualHaar_isAddHaar
  letI : MeasureTheory.Measure.HasTemperateGrowth μArch := inferInstance
  letI : SigmaCompactSpace (InfinitePlace F → ℂ) := inferInstance
  letI : SFinite μFin := inferInstance
  letI : SFinite μArch := inferInstance
  have hCoord (v : S.Sf) :
      Integrable (fun y => (finite v).1 y * A.ψ v.1 (-(x.1 v * y)))
        (localSelfDualAt D S A μ v) := by
    letI : Measure.IsAddHaarMeasure (localSelfDualAt D S A μ v) :=
      localSelfDualMeasure_isHaar v.1 (μ v.1) (localConductorExponent D S A v)
    have h := localChar_mul_integrable v.1 (A.ψ v.1) (A.integral v.1)
      (localSelfDualAt D S A μ v) (finite v).1 (x.1 v)
      (finite v).2.2.2 (finite v).2.2.1
    have hcomm : (fun y => (finite v).1 y * A.ψ v.1 (-(x.1 v * y))) =
        fun y => A.ψ v.1 (-(x.1 v * y)) * (finite v).1 y := by
      funext y
      ring
    rw [hcomm]
    exact h
  have hFin : Integrable finTerm μFin := by
    dsimp [finTerm, μFin]
    exact Integrable.fintype_prod_dep hCoord
  have hArchBase : Integrable (arch : (InfinitePlace F → ℂ) → ℂ) μArch :=
    arch.integrable
  let archChar : (InfinitePlace F → ℂ) → ℂ := fun y =>
    ∏ w : InfinitePlace F, psiC (-(x.2 w * y w))
  have hCharCont : Continuous archChar := by
    dsimp [archChar]
    apply continuous_finset_prod
    intro w hw
    apply psiC_continuous.comp
    exact continuous_neg.comp (continuous_const.mul (continuous_apply w))
  have hCharNorm (y : InfinitePlace F → ℂ) : ‖archChar y‖ ≤ 1 := by
    simp [archChar, psiC_norm_one]
  have hArch : Integrable archTerm μArch := by
    dsimp [archTerm, archChar]
    exact hArchBase.mul_bdd hCharCont.aestronglyMeasurable
      (Filter.Eventually.of_forall hCharNorm)
  have hprod : Integrable (fun p => finTerm p.1 * archTerm p.2) (μFin.prod μArch) :=
    hFin.mul_prod hArch
  unfold sSelfDualMeasureCandidate
  rw [MeasureTheory.integrable_map_equiv (sFSDownBorelMeasEquiv S)]
  rw [MeasureTheory.integrable_map_equiv (sFSUpProdMeasEquiv S)]
  apply hprod.congr
  filter_upwards with p
  symm
  exact sTensor_character_factorization D S A
    (fun v y => (finite v).1 y) (fun y => arch y) x p

private theorem sFourier_tensor_inversion
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (arch : ArtinPrimitiveRoots.A1.SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) (x : S.FS) :
    (S.fourier A (sSelfDualMeasureCandidate D S A μ)
      (S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite))) x =
      S.tensorFunction arch finite (-x) := by
  let fLoc : ∀ v : S.Sf, v.1.adicCompletion F → ℂ := fun v y =>
    localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v) (finite v).1 y
  let fArch : (InfinitePlace F → ℂ) → ℂ :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier arch
  have hinner (z : S.FS) :
      S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite) z =
        (∏ v : S.Sf, fLoc v (z.1 v)) * fArch z.2 := by
    calc
      S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite) z =
          S.fourier A (sSelfDualMeasureCandidate D S A μ)
            (fun y : S.FS => (∏ v : S.Sf, (finite v).1 (y.1 v)) * arch y.2) z := by
              unfold ArtinPrimitiveRoots.A1.SData.fourier
              apply integral_congr_ae
              filter_upwards with y
              simp [ArtinPrimitiveRoots.A1.SData.tensorFunction,
                mul_comm, mul_left_comm, mul_assoc]
      _ = (∏ v : S.Sf, fLoc v (z.1 v)) * fArch z.2 := by
            exact sFourier_product_formula D S A μ
              (fun v y => (finite v).1 y) arch z
  have hinnerFun :
      S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite) =
        fun z : S.FS => (∏ v : S.Sf, fLoc v (z.1 v)) * fArch z.2 := funext hinner
  calc
    (S.fourier A (sSelfDualMeasureCandidate D S A μ)
        (S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite))) x =
        S.fourier A (sSelfDualMeasureCandidate D S A μ)
          (fun z : S.FS => (∏ v : S.Sf, fLoc v (z.1 v)) * fArch z.2) x := by
            rw [hinnerFun]
    _ = (∏ v : S.Sf, localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v)
          (fLoc v) (x.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 := by
          exact sFourier_product_formula D S A μ fLoc fArch x
    _ = S.tensorFunction arch finite (-x) := by
          have hlocal (v : S.Sf) :
              localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v)
                (fLoc v) (x.1 v) = (finite v).1 (-x.1 v) := by
            dsimp [fLoc, localSelfDualAt]
            simpa [localConductorExponent] using
              localSelfDualMeasure_test_inversion D S A v (μ v.1) (finite v) (x.1 v)
          have harch : ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier fArch x.2 =
              arch (-x.2) := by
            simpa [fArch] using
              ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier_inversion arch x.2
          have hlocalProd :
              (∏ v : S.Sf, localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v)
                (fLoc v) (x.1 v)) = ∏ v : S.Sf, (finite v).1 (-x.1 v) := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hlocal v
          rw [hlocalProd, harch]
          change (∏ v : S.Sf, (finite v).1 (-x.1 v)) * arch (-x.2) =
            arch (-x.2) * ∏ v : S.Sf, (finite v).1 (-x.1 v)
          ring

private theorem sFourier_add_of_integrable
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (μ : Measure S.FS)
    (f g : S.FS → ℂ) (x : S.FS)
    (hf : Integrable (fun y => f y * S.e A (-(y * x))) μ)
    (hg : Integrable (fun y => g y * S.e A (-(y * x))) μ) :
    S.fourier A μ (f + g) x = S.fourier A μ f x + S.fourier A μ g x := by
  unfold ArtinPrimitiveRoots.A1.SData.fourier
  have hsum : (fun y => (f + g) y * S.e A (-(y * x))) =
      fun y => f y * S.e A (-(y * x)) + g y * S.e A (-(y * x)) := by
    funext y
    simp [Pi.add_apply, add_mul]
  rw [hsum, integral_add hf hg]

private theorem sFourier_smul_of_integrable
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F) (μ : Measure S.FS)
    (c : ℂ) (f : S.FS → ℂ) (x : S.FS)
    (hf : Integrable (fun y => f y * S.e A (-(y * x))) μ) :
    S.fourier A μ (c • f) x = c • S.fourier A μ f x := by
  unfold ArtinPrimitiveRoots.A1.SData.fourier
  have hmul : (fun y => (c • f) y * S.e A (-(y * x))) =
      fun y => c * (f y * S.e A (-(y * x))) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hmul, integral_const_mul]
  simp only [smul_eq_mul]

private theorem sBruhat_fourier_integrable
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (f : S.FS → ℂ) (hf : f ∈ S.BruhatSchwartz) (x : S.FS) :
    Integrable (fun y => f y * S.e A (-(y * x)))
      (sSelfDualMeasureCandidate D S A μ) := by
  classical
  refine Submodule.span_induction
    (p := fun f _ => ∀ x, Integrable (fun y => f y * S.e A (-(y * x)))
      (sSelfDualMeasureCandidate D S A μ)) ?_ ?_ ?_ ?_ hf x
  · rintro f ⟨p, rfl⟩
    rcases p with ⟨arch, finite⟩
    exact fun x => sTensorFourier_integrable D S A μ arch finite x
  · simp
  · intro f g hf hg hfi hgi x
    have heq : (fun y => (f + g) y * S.e A (-(y * x))) =
        fun y => f y * S.e A (-(y * x)) + g y * S.e A (-(y * x)) := by
      funext y
      simp [Pi.add_apply, add_mul]
    rw [heq]
    exact (hfi x).add (hgi x)
  · intro c f hf hfi x
    have heq : (fun y => (c • f) y * S.e A (-(y * x))) =
        fun y => c * (f y * S.e A (-(y * x))) := by
      funext y
      simp [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [heq]
    exact (hfi x).const_mul c

private theorem sFourier_tensor_eq
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (arch : ArtinPrimitiveRoots.A1.SData.ArchSchwartz F)
    (finite : ∀ v : S.Sf, S.FiniteTest v) :
    S.fourier A (sSelfDualMeasureCandidate D S A μ) (S.tensorFunction arch finite) =
      S.tensorFunction (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourierSchwartz arch)
        (fun v => Classical.choose
          (localSelfDualMeasure_fourier_test D S A v (μ v.1) (finite v))) := by
  classical
  let fhat : ∀ v : S.Sf, S.FiniteTest v := fun v =>
    Classical.choose (localSelfDualMeasure_fourier_test D S A v (μ v.1) (finite v))
  let ahat : ArtinPrimitiveRoots.A1.SData.ArchSchwartz F :=
    ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourierSchwartz arch
  have hfhat (v : S.Sf) :
      (fhat v).1 = localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v) (finite v).1 := by
    simpa [fhat, localSelfDualAt] using
      (Classical.choose_spec
        (localSelfDualMeasure_fourier_test D S A v (μ v.1) (finite v)))
  have hin : S.tensorFunction arch finite =
      (fun y : S.FS => (∏ v : S.Sf, (finite v).1 (y.1 v)) * arch y.2) := by
    funext y
    simp [ArtinPrimitiveRoots.A1.SData.tensorFunction, mul_comm]
  funext x
  rw [hin]
  calc
    S.fourier A (sSelfDualMeasureCandidate D S A μ)
        (fun y : S.FS => (∏ v : S.Sf, (finite v).1 (y.1 v)) * arch y.2) x =
      (∏ v : S.Sf, localFourier v.1 (A.ψ v.1) (localSelfDualAt D S A μ v)
        (finite v).1 (x.1 v)) *
        ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier arch x.2 :=
          sFourier_product_formula D S A μ (fun v y => (finite v).1 y) arch x
    _ = (∏ v : S.Sf, (fhat v).1 (x.1 v)) * ahat x.2 := by
      congr 1
      · apply Finset.prod_congr rfl
        intro v hv
        rw [hfhat v]
      · exact ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourier_eq_schwartz arch x.2
    _ = S.tensorFunction ahat fhat x := by
      simp [ArtinPrimitiveRoots.A1.SData.tensorFunction, ahat]
      ring

private theorem sFourier_mem_of_mem
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (f : S.FS → ℂ) (hf : f ∈ S.BruhatSchwartz) :
    S.fourier A (sSelfDualMeasureCandidate D S A μ) f ∈ S.BruhatSchwartz := by
  classical
  change S.fourier A (sSelfDualMeasureCandidate D S A μ) f ∈
    Submodule.span ℂ (Set.range fun p : SData.ArchSchwartz F ×
      (∀ v : S.Sf, S.FiniteTest v) => S.tensorFunction p.1 p.2)
  refine Submodule.span_induction
    (p := fun f _ => S.fourier A (sSelfDualMeasureCandidate D S A μ) f ∈
      S.BruhatSchwartz) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨p, rfl⟩
    rcases p with ⟨arch, finite⟩
    rw [sFourier_tensor_eq D S A μ arch finite]
    exact Submodule.subset_span ⟨
      (ArtinPrimitiveRoots.Proofs.a2_zf_top.complexPiFourierSchwartz arch,
        fun v => Classical.choose
          (localSelfDualMeasure_fourier_test D S A v (μ v.1) (finite v))), rfl⟩
  · have hz : S.fourier A (sSelfDualMeasureCandidate D S A μ) 0 = 0 := by
      funext x
      simp [ArtinPrimitiveRoots.A1.SData.fourier]
    rw [hz]
    exact S.BruhatSchwartz.zero_mem
  · intro f g hf hg hfm hgm
    have heq : S.fourier A (sSelfDualMeasureCandidate D S A μ) (f + g) =
        S.fourier A (sSelfDualMeasureCandidate D S A μ) f +
          S.fourier A (sSelfDualMeasureCandidate D S A μ) g := by
      funext x
      exact sFourier_add_of_integrable S A (sSelfDualMeasureCandidate D S A μ) f g x
        (sBruhat_fourier_integrable D S A μ f hf x)
        (sBruhat_fourier_integrable D S A μ g hg x)
    rw [heq]
    exact S.BruhatSchwartz.add_mem hfm hgm
  · intro c f hf hfm
    have heq : S.fourier A (sSelfDualMeasureCandidate D S A μ) (c • f) =
        c • S.fourier A (sSelfDualMeasureCandidate D S A μ) f := by
      funext x
      exact sFourier_smul_of_integrable S A (sSelfDualMeasureCandidate D S A μ)
        c f x (sBruhat_fourier_integrable D S A μ f hf x)
    rw [heq]
    exact S.BruhatSchwartz.smul_mem c hfm

private theorem sBruhat_fourier_inversion
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v)
    (f : S.FS → ℂ) (hf : f ∈ S.BruhatSchwartz) (x : S.FS) :
    S.fourier A (sSelfDualMeasureCandidate D S A μ)
      (S.fourier A (sSelfDualMeasureCandidate D S A μ) f) x = f (-x) := by
  classical
  let μsd := sSelfDualMeasureCandidate D S A μ
  have hInv (f : S.FS → ℂ) (hf : f ∈ S.BruhatSchwartz) :
      ∀ x, S.fourier A μsd (S.fourier A μsd f) x = f (-x) := by
    refine Submodule.span_induction
      (p := fun f _ => ∀ x, S.fourier A μsd (S.fourier A μsd f) x = f (-x))
      ?_ ?_ ?_ ?_ hf
    · rintro f ⟨p, rfl⟩
      rcases p with ⟨arch, finite⟩
      exact sFourier_tensor_inversion D S A μ arch finite
    · intro x
      simp [ArtinPrimitiveRoots.A1.SData.fourier]
    · intro f g hf hg hfi hgi x
      have hInner : S.fourier A μsd (f + g) =
          S.fourier A μsd f + S.fourier A μsd g := by
        funext y
        exact sFourier_add_of_integrable S A μsd f g y
          (sBruhat_fourier_integrable D S A μ f hf y)
          (sBruhat_fourier_integrable D S A μ g hg y)
      have hOuter : S.fourier A μsd
          (S.fourier A μsd f + S.fourier A μsd g) =
          S.fourier A μsd (S.fourier A μsd f) +
            S.fourier A μsd (S.fourier A μsd g) := by
        funext y
        exact sFourier_add_of_integrable S A μsd
          (S.fourier A μsd f) (S.fourier A μsd g) y
          (sBruhat_fourier_integrable D S A μ (S.fourier A μsd f)
            (sFourier_mem_of_mem D S A μ f hf) y)
          (sBruhat_fourier_integrable D S A μ (S.fourier A μsd g)
            (sFourier_mem_of_mem D S A μ g hg) y)
      rw [hInner, hOuter]
      simp only [Pi.add_apply, hfi x, hgi x]
    · intro c f hf hfi x
      have hInner : S.fourier A μsd (c • f) = c • S.fourier A μsd f := by
        funext y
        exact sFourier_smul_of_integrable S A μsd c f y
          (sBruhat_fourier_integrable D S A μ f hf y)
      have hOuter : S.fourier A μsd (c • S.fourier A μsd f) =
          c • S.fourier A μsd (S.fourier A μsd f) := by
        funext y
        exact sFourier_smul_of_integrable S A μsd c (S.fourier A μsd f) y
          (sBruhat_fourier_integrable D S A μ (S.fourier A μsd f)
            (sFourier_mem_of_mem D S A μ f hf) y)
      rw [hInner, hOuter]
      simp only [Pi.smul_apply, hfi x]
  exact hInv f hf x

theorem sDataSelfDualMeasure_exists
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (μ : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, LocHaar v) :
    Nonempty (S.SelfDualMeasure A) := by
  refine ⟨⟨sSelfDualMeasureCandidate D S A μ,
    sSelfDualMeasureCandidate_isHaar D S A μ, ?_⟩⟩
  intro f x
  exact sBruhat_fourier_inversion D S A μ (f : S.FS → ℂ) f.property x

end ArtinPrimitiveRoots.Proofs.a2_zf_top
