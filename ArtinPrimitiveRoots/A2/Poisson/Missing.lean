import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Interface

/-! A2 statement interfaces derived from the design lane. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

section Poisson
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)

/-- def:po-weights, 05:24–36,84–90. Support is compact inside the unit locus, not merely away
from the single zero point of the product ring. -/
structure PoissonWeights where
  W1 : ℝ → ℂ
  W1_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W1
  W1_compact : HasCompactSupport W1
  W1_positive_support : tsupport W1 ⊆ Set.Ioi 0
  W1_nonnegative : ∀ t, (W1 t).im = 0 ∧ 0 ≤ (W1 t).re
  W1_nonzero : ∃ t, W1 t ≠ 0
  arch : InfinitePlace F → SchwartzMap ℂ ℂ
  finite : ∀ v : S.Sf, S.FiniteTest v
  W0 : S.FS → ℂ
  W0_tensor : ∀ y, W0 y = (∏ v : S.Sf, (finite v).1 (y.1 v)) * ∏ w : InfinitePlace F, arch w (y.2 w)
  W0_Bruhat : W0 ∈ S.BruhatSchwartz
  W0_compact : HasCompactSupport W0
  W0_units : ∀ y ∈ tsupport W0, IsUnit y

variable (W : PoissonWeights (S := S))
def weightFourier : S.FS → ℂ := S.fourier A sd.measure W.W0
def weightM (z : ℂ) : ℂ := ∫ y, weightFourier sd W y * (S.absS y : ℂ) ^ z ∂(R.sheets.mul)
def weightW1hat (w : ℂ) : ℂ := ∫ t in Set.Ioi (0 : ℝ), W.W1 t * (t : ℂ) ^ w / (t : ℂ)
def weightV0 (T : ℝ) : ℂ :=
  ∫ y, weightFourier sd W y ∂(R.sheets.sheet T)

def WeightSpec : Prop := weightFourier sd W 0 = 0 ∧ weightM R sd W (1 / 6) ≠ 0

def WeightDecay : Prop :=
  DifferentiableOn ℂ (weightM R sd W) {z | 0 < z.re} ∧ Differentiable ℂ (weightW1hat W) ∧
  (∀ l r A0 : ℝ, 0 < l → l ≤ r → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ σ τ : ℝ, l ≤ σ → σ ≤ r →
      ‖weightM R sd W (σ + τ * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-A0)) ∧
  (∀ l r A0 : ℝ, l ≤ r → 0 < A0 → ∃ C : ℝ, 0 < C ∧
    ∀ σ τ : ℝ, l ≤ σ → σ ≤ r →
      ‖weightW1hat W (σ + τ * Complex.I)‖ ≤ C * (1 + |τ|) ^ (-A0)) ∧
  (∀ σ : ℝ, 0 < σ → Integrable (fun y =>
    ‖weightFourier sd W y‖ * S.absS y ^ σ) R.sheets.mul)

/-- po:weights-exist, 05:37–75. The existence and universal analytic conclusions are separate. -/
theorem po_weights_exist :
  (∃ W : PoissonWeights (S := S), WeightSpec R sd W) ∧
    ∀ W : PoissonWeights (S := S), WeightDecay R sd W := by
  sorry
/-- ext:tate-local-FE, finite-place version at the actual completion and frozen additive sign.
A scalar c_v(s) is independent of the test function; the strip is open. -/
theorem ext_tate_local_FE_fin (v : FinPlace F) :
  ∃ c : ℂ → ℂ, c (1 / 6) ≠ 0 ∧ ∀ f : v.adicCompletion F → ℂ,
    Continuous f → HasCompactSupport f → IsLocallyConstant f → ∀ s : ℂ, 0 < s.re → s.re < 1 →
      (∫ y, (∫ x, f x * A.ψ v (-(x * y)) ∂(μ v).μ) * (absFin v y : ℂ) ^ s
        ∂Theta.mulHaarFin (μ v)) =
      c s * ∫ y, f y * (absFin v y : ℂ) ^ (1 - s) ∂Theta.mulHaarFin (μ v) := by
  sorry
/-- ext:tate-local-FE, complex-place version. Haar scalings are absorbed in c_v. -/
theorem ext_tate_local_FE_complex :
  ∃ c : ℂ → ℂ, c (1 / 6) ≠ 0 ∧ ∀ f : SchwartzMap ℂ ℂ, ∀ s : ℂ, 0 < s.re → s.re < 1 →
    (∫ y : ℂ, (∫ x : ℂ, f x * psiC (-(x * y))) * (Complex.normSq y : ℂ) ^ s ∂Theta.mulHaarC) =
      c s * ∫ y : ℂ, f y * (Complex.normSq y : ℂ) ^ (1 - s) ∂Theta.mulHaarC := by
  sorry
/-- def:po-finite-factor: Gauss sum over the actual R/(I), with an explicit allowed generator. -/
def finiteGaussAt (I : S.ExtIdeal) (a : Fˣ) (k : F) : ℂ :=
  ∑ᶠ x : ResidueRing R.exterior I, chiIdealPow D I.1 (x.out : F) 1 * S.e A (S.diag (k * (x.out : F) / (a : F)))
def finiteGauss (I : S.ExtIdeal) (k : F) : ℂ := finiteGaussAt R I (bc.gen I) k

def finiteFactor (s I : S.ExtIdeal) (a : Fˣ) (h : F) : ℂ :=
  ∑ᶠ d : ResidueRing R.exterior s,
    if ∃ x : S.R, h - (a : F) * (d.out : F) = (bc.gen s : F) * (x : F) then
      chiIdealPow D s.1 (d.out : F) 1 * finiteGaussAt R I a ((h - (a : F) * (d.out : F)) / (bc.gen s : F))
    else 0

/-- def:po-probe, 05:77–101. Quotient integration is implemented by the fixed Ω₁. -/
def probeIntegrand (X Y Z : ℝ) (t : S.FSˣ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑' s : S.ExtIdeal, W.W1 (qI s.1 / Y) * ((qI s.1 * X) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑' m : S.R, (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m : F)) *
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val) *
        Bm D S A ϑ (cgen R) (m : F) Z

def probe (X Y Z : ℝ) : ℂ := omegaInt R 1 (probeIntegrand R W X Y Z)

/-- `po:probe-well-defined`, 05:82–112. Finiteness means finite support, not `tsum` definedness.
The generator-independence frequency is restricted to `k : S.R` per `sol-thin-a2rp`, since its
residue phase needs integrality. -/
theorem po_probe_well_defined :
  (∀ I (a b : Fˣ), S.IsGen (a : F) I.1 → Bd.Allowed a → S.IsGen (b : F) I.1 → Bd.Allowed b →
    ∀ k : S.R, finiteGaussAt R I a (k : F) = finiteGaussAt R I b (k : F)) ∧
  (∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
    (∀ γ : Gamma S, ∀ t, probeIntegrand R W X Y Z (S.diagU (γ.1 : Fˣ) * t) = probeIntegrand R W X Y Z t) ∧
    (∀ t (s : S.ExtIdeal), (Function.support (fun m : S.R =>
      W.W0 (S.diag (m : F) * ((t * R.sheets.ellU (qI s.1 * X))⁻¹ : S.FSˣ).val))).Finite) ∧
    IntegrableOn (onUnits (probeIntegrand R W X Y Z)) (omegaAt R 1) (R.sheets.sheet 1) ∧
    (∀ O, IsFundamentalAt (S := S) O 1 →
      (∫ y in O, onUnits (probeIntegrand R W X Y Z) y ∂(R.sheets.sheet 1)) = probe R W X Y Z)) ∧
  W.W0 0 = 0 := by
  sorry
/-- Corrected `prop:probe-low` consumer, `sol-gate-a2b` (05:194–246): the legacy reflection
route receives the split Gauss characters, including the angular datum used by the admissible
row-character producer. -/
def probeLowStatement (η : HeckeChar F) : Prop :=
  GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
    ‖probe R W (Z ^ a) (Z ^ b) Z‖ ≤ C * Z ^ (933 / 2000 + ε)

/-- `prop:probe-low`, 05:194–246, with the corrected split-character input from `sol-gate-a2b`. -/
theorem prop_probe_low (η : HeckeChar F)
    (hSplit : GaussSplit (D := D) (S := S) (H := H) (Bd := Bd) (A := A) (ϑ := ϑ) η) :
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
    ‖probe R W (Z ^ a) (Z ^ b) Z‖ ≤ C * Z ^ (933 / 2000 + ε) := by
  sorry
/-- po:finite-poisson-transform, 05:267–282: no coprimality hypothesis on s,I. -/
theorem po_finite_poisson_transform : ∀ (s I : S.ExtIdeal) (a : Fˣ),
  S.IsGen (a : F) I.1 → Bd.Allowed a → ∀ h : S.R,
    (∑ᶠ m : ResidueRing R.exterior (R.exterior.mul s I),
      (qI s.1 ^ (-(1 / 2 : ℝ)) : ℝ) * finiteGauss R s (-(m.out : F)) *
        chiIdealPow D I.1 (m.out : F) 1 *
          S.e A (S.diag ((h : F) * (m.out : F) / ((bc.gen s : F) * (a : F))))) =
      (qI s.1 ^ (1 / 2 : ℝ) : ℝ) * finiteFactor R s I a (h : F) ∧
    ‖finiteFactor R s I a (h : F)‖ ≤ qI s.1 * qI I.1 ∧
    ∀ γ : Gamma S, finiteFactor R s I a (((γ.1 : Fˣ) : F) * (h : F)) = finiteFactor R s I a (h : F) := by
  sorry
variable (η : HeckeChar F) (U : FrequencyData S D η)
def poissonOrbitTerm (X Y Z : ℝ)
    (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × U.U × S.ExtIdeal) : ℂ :=
  let c := p.1
  let n := p.2.1
  let s := p.2.2.1
  let u := p.2.2.2.1
  let r := p.2.2.2.2
  gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
    (qI c.1 ^ (-(1 / 2 : ℝ)) / qI n.1 / qI (Aideal R c n).1 : ℝ) *
      (PG (qI (Aideal R c n).1 / Z) : ℂ) * W.W1 (qI s.1 / Y) *
        finiteFactor R s (Aideal R c n) (Agen R c n) ((U.repr u : F) * (bc.gen r : F) ^ 6) *
          weightV0 R sd W (X * U.q u * qI r.1 ^ 6 / qI (Aideal R c n).1)

/-- Vertical integrals include the 1/(2π) after parametrizing s=σ+it. -/
def vertical (σ : ℝ) (f : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, f (σ + t * Complex.I)
def tripleVertical (σξ σw σz : ℝ) (f : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  vertical σξ (fun ξ => vertical σw (fun w => vertical σz (fun z => f ξ w z)))
/-- po:poisson-orbits, 05:284–350, including the V₀ Mellin dictionary. -/
theorem po_poisson_orbits : WeightSpec R sd W →
  (ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (weightV0 R sd W) (Set.Ioi 0)) ∧
  (∀ z : ℂ, 0 < z.re → mellin (weightV0 R sd W) z = weightM R sd W z) ∧
  (∀ σ T : ℝ, 0 < σ → 0 < T →
    weightV0 R sd W T = vertical σ (fun z => weightM R sd W z * (T : ℂ) ^ (-z))) ∧
  ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
    Summable (fun p => ‖poissonOrbitTerm R sd W η U X Y Z p‖) ∧
    probe R W X Y Z = ((X ^ (1 / 2 : ℝ) / Y : ℝ) : ℂ) * ∑' p, poissonOrbitTerm R sd W η U X Y Z p := by
  sorry
/-- def:calF within po:mellin-triple, 05:353–389; all four ideal indices are actual exterior ideals. -/
def calFTerm (u : U.U) (ξ w z : ℂ) (p : S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal) : ℂ :=
  let c := p.1
  let n := p.2.1
  let s := p.2.2.1
  let r := p.2.2.2
  gamma D S A 2 c.1 (cgen R c) * ϑ.idealValue (Aideal R c n).1 *
    finiteFactor R s (Aideal R c n) (Agen R c n) ((U.repr u : F) * (bc.gen r : F) ^ 6) *
      (qI c.1 : ℂ) ^ (-1 / 2 - ξ) * (qI n.1 : ℂ) ^ (-1 - 3 * ξ) *
        (qI s.1 : ℂ) ^ (-w) * (qI r.1 : ℂ) ^ (-6 * z)
def calF (u : U.U) (ξ w z : ℂ) : ℂ := ∑' p, calFTerm R η U u ξ w z p

def mellinWeight (X Y Z : ℝ) (ξ w z : ℂ) : ℂ :=
  (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (ξ + z - 1) * (Y : ℂ) ^ (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * weightM R sd W z * weightW1hat W w

/-- po:mellin-triple, 05:353–389. `Summable` prevents interpreting a divergent total tsum as 0. -/
theorem po_mellin_triple : WeightSpec R sd W → ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
  (∀ ξ w z : ℂ, ξ.re = 4 → w.re = 4 → z.re = 2 →
    (∀ u, Summable (fun p => ‖calFTerm R η U u ξ w z p‖)) ∧
      Summable (fun u => ‖(U.q u : ℂ) ^ (-z) * calF R η U u ξ w z‖)) ∧
  Integrable (fun t : ℝ × ℝ × ℝ =>
    mellinWeight R sd W X Y Z (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I) *
      ∑' u, (U.q u : ℂ) ^ (-(2 + t.2.2 * Complex.I)) * calF R η U u
        (4 + t.1 * Complex.I) (4 + t.2.1 * Complex.I) (2 + t.2.2 * Complex.I)) ∧
  probe R W X Y Z = tripleVertical 4 4 2 (fun ξ w z =>
    mellinWeight R sd W X Y Z ξ w z * ∑' u, (U.q u : ℂ) ^ (-z) * calF R η U u ξ w z) := by
  sorry
/-- Stripped local C uses the negative exterior additive sign (05:444–550). -/
def localC (v : FinPlace F) (hv : v ∉ S.Sf) (t k J : ℕ) : ℂ :=
  let pi := R.exterior.prime v hv
  ∑ᶠ d : ResidueRing R.exterior (R.exterior.pow pi k),
    if ∃ x : S.R, (primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F) =
      (primeGen R v : F) ^ k * (x : F) then
      (if k = 0 then 1 else chiPow D v (d.out : F) k) *
      ∑ᶠ x : ResidueRing R.exterior (R.exterior.pow pi t),
        (if t = 0 then 1 else chiPow D v (x.out : F) t) * A.ψ v (algebraMap F _
          (-(((primeGen R v : F) ^ J - (primeGen R v : F) ^ t * (d.out : F)) *
            (x.out : F) / (primeGen R v : F) ^ (k + t))))
    else 0

def localT (v : FinPlace F) (e : ℤ) (y : F) : ℂ :=
  ∑ᶠ x : 𝓞 F ⧸ v.asIdeal, chiPow D v (algebraMap (𝓞 F) F x.out) e *
    A.ψ v (algebraMap F _ (-(y * algebraMap (𝓞 F) F x.out / (primeGen R v : F))))

/-- po:C-local-values, 05:552–595. At J=t-1 use J+1-t, not saturated J-t+1. -/
theorem po_C_local_values : ∀ v (hv : v ∉ S.Sf) J,
  localC R v hv 0 0 J = 1 ∧
  (∀ k : ℕ, 0 < k → localC R v hv 0 k J = if J = 0 then 1 else 0) ∧
  (∀ t : ℕ, 0 < t →
    localC R v hv t 0 J = (if t - 1 ≤ J then
      (qI v.asIdeal : ℂ) ^ (t - 1) * localT R v t ((primeGen R v : F) ^ (J + 1 - t)) else 0) ∧
    localC R v hv t 1 J = (if t ≤ J then localT R v 1 1 * (qI v.asIdeal : ℂ) ^ (t - 1) *
      localT R v ((t : ℤ) - 1) ((primeGen R v : F) ^ (J - t)) else 0) ∧
    (∀ k : ℕ, 2 ≤ k → localC R v hv t k J = 0) ∧
    ‖localC R v hv t 0 J‖ ≤ qI v.asIdeal ^ (t : ℝ) ∧
    ‖localC R v hv t 1 J‖ ≤ qI v.asIdeal ^ ((t : ℝ) + 1 / 2)) := by
  sorry
def frequencyValuation (u : U.U) (v : FinPlace F) : ℕ :=
  (FractionalIdeal.count F v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F))).toNat

def localEulerTerm (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ)
    (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  let e := i.1.1
  let l := i.2.1
  let k := i.2.2.1
  let m := i.2.2.2
  let j := frequencyValuation η U u v
  gamma D S A 2 v.asIdeal (primeGen R v : F) ^ e * ϑ.primeValue v ^ (e + 3 * l) *
    chi D v ((U.repr u : F) / (primeGen R v : F) ^ j) ^ ((k : ℤ) - (e : ℤ) - 3 * (l : ℤ)) *
      localC R v hv (e + 3 * l) k (j + 6 * m) *
        (qI v.asIdeal : ℂ) ^ (-(e : ℂ) * (1 / 2 + ξ) - (l : ℂ) * (1 + 3 * ξ) - (k : ℂ) * w - 6 * (m : ℂ) * z)

def localEuler (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ) : ℂ :=
  ∑' i, localEulerTerm R η U u v hv ξ w z i

def initialRegion (ξ w z : ℂ) : Prop := 3 / 2 < ξ.re ∧ 2 < w.re ∧ 1 / 6 < z.re

/-- po:euler-local-factorization, 05:444–550. Product convergence uses HasProd, never finprod. -/
theorem po_euler_local_factorization : ∀ u ξ w z, initialRegion ξ w z →
  Summable (fun p => ‖calFTerm R η U u ξ w z p‖) ∧
  (∀ v hv, Summable (fun i => ‖localEulerTerm R η U u v hv ξ w z i‖)) ∧
  HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} => localEuler R η U u v.1 v.2 ξ w z) (calF R η U u ξ w z) := by
  sorry
/-- Exact arithmetic input from A1 gauss-characters/vartheta-S, including finite order of η. -/
def EulerHypotheses : Prop := IsOfFinOrder η ∧ (∀ v, v ∉ S.Sf → η.UnramifiedAt v) ∧
  ∀ v, v ∉ S.Sf → gamma D S A 1 v.asIdeal (primeGen R v : F) *
    gamma D S A 2 v.asIdeal (primeGen R v : F) * ϑ.primeValue v = -η.primeValue v

def localV (v : FinPlace F) (z : ℂ) : ℂ := (qI v.asIdeal : ℂ) ^ (-6 * z)
def localWvar (u : U.U) (v : FinPlace F) (w : ℂ) : ℂ := chi D v (U.repr u : F) * (qI v.asIdeal : ℂ) ^ (-w)
def localDvar (u : U.U) (v : FinPlace F) (ξ : ℂ) : ℂ :=
  η.primeValue v * star (chi D v (U.repr u : F)) * (qI v.asIdeal : ℂ) ^ (-ξ)
def localEvar (v : FinPlace F) (ξ z : ℂ) : ℂ :=
  ϑ.primeValue v ^ 6 * (qI v.asIdeal : ℂ) ^ (4 - 6 * ξ) * localV v z

def normalizedLocal (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (ξ w z : ℂ) : ℂ :=
  (1 - localV v z) * (1 - localWvar η U u v w) / (1 - localDvar η U u v ξ) *
    localEuler R η U u v hv ξ w z

/-- po:euler-good-closed, 05:596-659. The zero-valuation local series is the frozen closed factor. -/
theorem po_euler_good_closed : EulerHypotheses R η → ∀ u v hv ξ w z, initialRegion ξ w z → frequencyValuation η U u v = 0 →
  localEuler R η U u v hv ξ w z = eulerGoodClosed (qI v.asIdeal) (localV v z)
    (localWvar η U u v w) (localDvar η U u v ξ) (localEvar (ϑ := ϑ) v ξ z) := by
  sorry
abbrev Triple := Fin 3 → ℂ

def eulerNeighborhood (p : Triple) : Prop :=
  (998 / 1000 - 1 / 100000 < (p 0).re ∧ 3 / 1000 - 1 / 100000 < (p 1).re ∧
    4 / 10 - 1 / 100000 < (p 2).re) ∨
  (998 / 1000 - 1 / 100000 < (p 0).re ∧ 95 / 100 - 1 / 100000 < (p 1).re ∧
    16 / 100 - 1 / 100000 < (p 2).re)

/-- po:H-local-bounds, 05:660–729, for supplied numerical constants. The separate absolute
uniformity obligation below places those constants before all arithmetic data. -/
def HasPoHLocalBounds (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
    (η : HeckeChar F) (U : FrequencyData S D η) (C Q0 : ℝ) : Prop :=
  0 < C ∧ 1 < Q0 ∧ ∀ u v hv p,
  Q0 < qI v.asIdeal → eulerNeighborhood p →
  Summable (fun i => ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖) ∧
  ‖normalizedLocal R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
    C * qI v.asIdeal ^ (if frequencyValuation η U u v = 0 then (-1 - 1 / 4000 : ℝ) else (-1 / 4000 : ℝ))

/-- Corrected by `sol-gate-a2b`: the constants are outputs of the local estimate, not arbitrary
inputs (`po:H-local-bounds`, 05:660–729). -/
theorem po_H_local_bounds :
  EulerHypotheses R η → ∃ C Q0 : ℝ, 0 < C ∧ 1 < Q0 ∧ HasPoHLocalBounds R η U C Q0 := by
  sorry
/-- H_u is a proposed limit object; its HasProd law is an explicit node conclusion below. -/
structure EulerCorrection (η : HeckeChar F) (U : FrequencyData S D η) where
  H : U.U → Triple → ℂ
  H_eq : ∀ u p, H u p = ∏' v : {v : FinPlace F // v ∉ S.Sf},
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)

variable (HC : EulerCorrection R η U)
def Heta (s : ℂ) : ℂ := HC.H U.one ![s, 1, 1 / 6]

/-- po:H-product, 05:731–755: normal convergence and holomorphy in three complex variables. -/
def HasPoHProduct (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (η : HeckeChar F)
    (U : FrequencyData S D η) (HC : EulerCorrection R η U) : Prop :=
  (∀ u p, eulerNeighborhood p →
    HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} =>
      normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) (HC.H u p)) ∧
  (∀ u, DifferentiableOn ℂ (HC.H u) {p | eulerNeighborhood p}) ∧
  (∀ u (K : Set Triple), IsCompact K → K ⊆ {p | eulerNeighborhood p} →
    ∀ ε : ℝ, 0 < ε → ∃ V : Finset (FinPlace F), ∀ V' : Finset (FinPlace F), V ⊆ V' →
      ∀ p ∈ K, ‖(∏ v ∈ V'.attach, if hv : v.1 ∉ S.Sf then
        normalizedLocal R η U u v.1 hv (p 0) (p 1) (p 2) else 1) - HC.H u p‖ < ε) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ u p, eulerNeighborhood p → ‖HC.H u p‖ ≤ C * U.q u ^ ε

theorem po_H_product : EulerHypotheses R η → HasPoHProduct R η U HC := by
  sorry
variable (HA : HeckeAnalysis F)
/-- prop:euler-product, 05:407–433: analytic continuations, masked exterior values retained. -/
theorem prop_euler_product : EulerHypotheses R η →
  HasPoHProduct R η U HC ∧ (∀ u ξ w z, initialRegion ξ w z →
    calF R η U u ξ w z = HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
      HA.LS S (η * (U.kummer u)⁻¹) ξ) ∧
  ((∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
      ∀ p, eulerNeighborhood p → HC.H U.one p ≠ 0) := by
  sorry
/-- def:po-H-eta, 05:757–765: the larger open half-plane includes the closed .998 boundary. -/
theorem po_H_eta_properties : EulerHypotheses R η →
  (∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2) →
  DifferentiableOn ℂ (Heta R η U HC) {s | 998 / 1000 - 1 / 100000 < s.re} ∧
  (∀ s, 998 / 1000 - 1 / 100000 < s.re → Heta R η U HC s ≠ 0) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ s, 998 / 1000 - 1 / 100000 < s.re → ‖Heta R η U HC s‖ ≤ C := by
  sorry
end Poisson


section PoissonSupplementary
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
/-- po:weights-exist: local absolute weighted derivatives (05:56–65). -/
theorem po_weights_local_integrability :
  (∀ v : S.Sf, ∀ σ : ℝ, 0 < σ → Integrable (fun y =>
    ‖∫ x, (W.finite v).1 x * A.ψ v.1 (-(x * y)) ∂(μ v.1).μ‖ * absFin v.1 y ^ σ)
      (Theta.mulHaarFin (μ v.1))) ∧
  ∀ w : InfinitePlace F, ∀ j : ℕ, ∀ σ : ℝ, 0 < σ →
    Integrable (fun y : ℂ => ‖normDeriv j (fun y => ∫ x : ℂ, W.arch w x * psiC (-(x * y))) y‖ *
      Complex.normSq y ^ σ) Theta.mulHaarC := by
  sorry
/-- po:probe-well-defined: finite outer support and absolute B_m series for every row. -/
theorem po_probe_absolute : ∀ X Y Z, 0 < X → 0 < Y → 0 < Z →
  (Function.support (fun I : S.ExtIdeal => W.W1 (qI I.1 / Y))).Finite ∧
  (∀ m : S.R, Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
    ‖gamma D S A 2 p.1.1 (cgen R p.1) * (qI p.1.1 ^ (-(1 / 2 : ℝ)) / qI p.2.1 : ℝ) *
      ϑ.idealValue (Aideal R p.1 p.2).1 * chiIdealPow D (Aideal R p.1 p.2).1 (m : F) 1 *
        (PG (qI (Aideal R p.1 p.2).1 / Z) : ℂ)‖)) := by
  sorry
private instance eulerResidueMaximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
private noncomputable instance eulerResidueField (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private lemma euler_count_spanSingleton_div (v : FinPlace F) (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) :
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

private lemma euler_count_spanSingleton_eq_neg_log_intValuation (v : FinPlace F)
    (r : 𝓞 F) (hr : r ≠ 0) :
    FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F r)) = -WithZero.log (v.intValuation r) := by
  have hspan : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    simpa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using hr
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe F v hspan,
    v.intValuation_if_neg hr, WithZero.log_exp]
  ring

private lemma euler_count_spanSingleton_eq_neg_log_valuation (v : FinPlace F)
    (z : F) (hz : z ≠ 0) :
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
    euler_count_spanSingleton_div v (algebraMap (𝓞 F) F n)
      (algebraMap (𝓞 F) F (d : 𝓞 F)) hmapn hmapd,
    euler_count_spanSingleton_eq_neg_log_intValuation v n hn,
    euler_count_spanSingleton_eq_neg_log_intValuation v (d : 𝓞 F) hd,
    WithZero.log_div (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero (d : 𝓞 F) hd)]
  ring

private lemma euler_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

/-- po:C-local-values: the one-prime T_v table, including the masked v≡0 case. -/
theorem po_C_local_T_values : ∀ v, v ∉ S.Sf → ∀ e : ℤ, ∀ y : S.R,
  localT R v e (y : F) =
    (if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e * localT R v e 1
      else if e % 6 = 0 then qI v.asIdeal - 1 else 0) ∧
  (e % 6 ≠ 0 → ‖localT R v e 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ)) ∧ localT R v 0 1 = -1 := by
  intro v hv e y
  classical
  letI := bridgeResidueField v
  letI := bridgeResidueFintype v
  let SB := a2_bridge_SYMBOL D S
  let p : Fˣ := primeGen R v
  have hp0 : S.IsGen (p : F) v.asIdeal := by
    have h := (bc.gen_spec (R.exterior.prime v hv)).1
    simpa [p, primeGen, hv, R.exterior.prime_val] using h
  have hcountP : FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) = 1 := by
    calc
      FractionalIdeal.count F v
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (p : F)) =
        FractionalIdeal.count F v (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
          hp0.2.2 v hv
      _ = 1 := FractionalIdeal.count_self F v
  have hlogP : WithZero.log (HeightOneSpectrum.valuation F v (p : F)) = -1 := by
    have h := euler_count_spanSingleton_eq_neg_log_valuation v (p : F) hp0.2.1
    rw [hcountP] at h
    linarith
  have hvalP : HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-1 : ℤ) := by
    have hpvalne : HeightOneSpectrum.valuation F v (p : F) ≠ 0 :=
      (v.valuation F).ne_zero_iff.mpr hp0.2.1
    calc
      HeightOneSpectrum.valuation F v (p : F) =
          WithZero.exp (WithZero.log (HeightOneSpectrum.valuation F v (p : F))) :=
        (WithZero.exp_log hpvalne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlogP]
  obtain ⟨hchars, hchiSix, hpsi⟩ := a2_bridge_FINITE_CHAR D S A v hv p hp0
  obtain ⟨χ₁, hχ₁order, hχ₁eval⟩ := hchiSix
  obtain ⟨ψ, hψprim, hψeval⟩ := hpsi
  obtain ⟨χe, hχeeval⟩ := hchars e
  have hresAlg (x : 𝓞 F ⧸ v.asIdeal) :
      residue v (algebraMap (𝓞 F) F x.out) = x := by
    simpa using SB.residue_algebraMap v x.out
  have hmulchar_zpow (χ : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
      (u : (𝓞 F ⧸ v.asIdeal)ˣ) : χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = χ u ^ e := by
    have h := χ.toUnitHom.map_zpow u e
    calc
      χ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) = (χ.toUnitHom (u ^ e) : ℂ) :=
        (MulChar.coe_toUnitHom χ (u ^ e)).symm
      _ = (χ.toUnitHom u : ℂ) ^ e := by
        simpa only [Units.val_zpow_eq_zpow_val] using congrArg Units.val h
      _ = χ u ^ e := by rw [MulChar.coe_toUnitHom]
  have hχpow_eq : χe = χ₁ ^ e := by
    apply MulChar.ext
    intro u
    have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
      rw [hresAlg]
      exact u.ne_zero
    calc
      χe (u : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
      _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
        SB.chiPow_nonzero v _ e hu
      _ = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) 1 ^ e := by
        rw [SB.chiPow_nonzero v _ 1 hu, zpow_one]
      _ = χ₁ (u : 𝓞 F ⧸ v.asIdeal) ^ e := by rw [hχ₁eval]
      _ = χ₁ (u ^ e : (𝓞 F ⧸ v.asIdeal)ˣ) := (hmulchar_zpow χ₁ u).symm
      _ = (χ₁ ^ e) (u : 𝓞 F ⧸ v.asIdeal) :=
        (MulChar.zpow_apply_coe χ₁ e u).symm
  have hχe_one : e % 6 = 0 → χe = 1 := by
    intro he
    have hdvd : (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.mpr he
    have horderDvd : (orderOf χ₁ : ℤ) ∣ e := by rw [hχ₁order]; exact hdvd
    have hpow : χ₁ ^ e = 1 := (orderOf_dvd_iff_zpow_eq_one).mp horderDvd
    rw [hχpow_eq, hpow]
  have hχe_ne_one : e % 6 ≠ 0 → χe ≠ 1 := by
    intro he hχ
    have hpow : χ₁ ^ e = 1 := hχpow_eq.symm.trans hχ
    have hdvd : (orderOf χ₁ : ℤ) ∣ e := (orderOf_dvd_iff_zpow_eq_one).mpr hpow
    rw [hχ₁order] at hdvd
    exact he (Int.dvd_iff_emod_eq_zero.mp hdvd)
  have hphaseErr (z : F)
      (hz : HeightOneSpectrum.valuation F v z ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z / (p : F))) = 1 := by
    have hvalDiv : HeightOneSpectrum.valuation F v (z / (p : F)) ≤ 1 := by
      rw [map_div₀, hvalP]
      have hexpPos : 0 < WithZero.exp (-1 : ℤ) :=
        lt_of_le_of_ne zero_le (Ne.symm WithZero.exp_ne_zero)
      exact (div_le_one₀ hexpPos).2 hz
    have hlocal : algebraMap F (v.adicCompletion F) (z / (p : F)) ∈
        v.adicCompletionIntegers F := by
      change ((z / (p : F) : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hvalDiv
    exact A.integral v _ hlocal
  have hphaseCongr (z₁ z₂ : F)
      (hz : HeightOneSpectrum.valuation F v (z₁ - z₂) ≤ WithZero.exp (-1 : ℤ)) :
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
        A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
    have harg : algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F)) =
        algebraMap F (v.adicCompletion F) (z₁ / (p : F)) -
          algebraMap F (v.adicCompletion F) (z₂ / (p : F)) := by
      have hF : (z₁ - z₂) / (p : F) = z₁ / (p : F) - z₂ / (p : F) := by
        field_simp [Units.ne_zero p]
      rw [hF, map_sub]
    have hdiv := (A.ψ v).map_sub_eq_div
      (algebraMap F (v.adicCompletion F) (z₁ / (p : F)))
      (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))
    have hz₂ : A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) ≠ 0 :=
      (AddChar.val_isUnit (A.ψ v)
        (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))).ne_zero
    calc
      A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) =
          (A.ψ v (algebraMap F (v.adicCompletion F) (z₁ / (p : F))) /
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F)))) *
              A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) :=
        (div_mul_cancel₀ _ hz₂).symm
      _ = A.ψ v (algebraMap F (v.adicCompletion F) ((z₁ - z₂) / (p : F))) *
            A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [← hdiv, ← harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F) (z₂ / (p : F))) := by
        rw [hphaseErr (z₁ - z₂) hz, one_mul]
  have hphase (y : S.R) (x : 𝓞 F ⧸ v.asIdeal) :
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
        ψ (-(residue v (y : F)) * x) := by
    have hyval : HeightOneSpectrum.valuation F v (y : F) ≤ 1 := y.property v hv
    obtain ⟨ay, dy, hdy⟩ := v.exists_primeCompl_mul_eq_of_integer (y : F) hyval
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have hdyNot : dy.1 ∉ v.asIdeal := by
      exact Ideal.mem_primeCompl_iff.mp dy.2
    have hresY : residue v (y : F) =
        Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy :=
      euler_residue_rep v (y : F) ay dy.1 hdyNot hdy
    let b : 𝓞 F := (-a).out
    have hdq : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
      intro hzero
      exact hdyNot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
    have hmkB : Ideal.Quotient.mk v.asIdeal b = -a := by
      simp [b]
    have hmk : Ideal.Quotient.mk v.asIdeal (ay + b * dy) = 0 := by
      calc
        Ideal.Quotient.mk v.asIdeal (ay + b * dy) =
            Ideal.Quotient.mk v.asIdeal ay +
              Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by simp
        _ = (Ideal.Quotient.mk v.asIdeal ay / Ideal.Quotient.mk v.asIdeal dy +
              Ideal.Quotient.mk v.asIdeal b) * Ideal.Quotient.mk v.asIdeal dy := by
          have hcancel : (Ideal.Quotient.mk v.asIdeal ay /
              Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy =
                Ideal.Quotient.mk v.asIdeal ay := div_mul_cancel₀ _ hdq
          calc
            _ = (Ideal.Quotient.mk v.asIdeal ay /
                Ideal.Quotient.mk v.asIdeal dy) * Ideal.Quotient.mk v.asIdeal dy +
                  Ideal.Quotient.mk v.asIdeal b * Ideal.Quotient.mk v.asIdeal dy := by rw [hcancel]
            _ = _ := by ring
        _ = (residue v (y : F) + Ideal.Quotient.mk v.asIdeal b) *
              Ideal.Quotient.mk v.asIdeal dy := by rw [hresY]
        _ = 0 := by rw [hmkB]; ring
    have hmem : ay + b * dy ∈ v.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk
    have hvalNum : HeightOneSpectrum.valuation F v
        (algebraMap (𝓞 F) F (ay + b * dy)) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      apply (v.intValuation_le_pow_iff_mem (ay + b * dy) 1).2
      simpa using hmem
    have hvalDy : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_eq_one_iff_mem_primeCompl dy.1).2 dy.2
    have hmul : ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
        algebraMap (𝓞 F) F (ay + b * dy) := by
      calc
        ((y : F) + (b : F)) * algebraMap (𝓞 F) F dy =
            (y : F) * algebraMap (𝓞 F) F dy +
              (b : F) * algebraMap (𝓞 F) F dy := by ring
        _ = algebraMap (𝓞 F) F ay + algebraMap (𝓞 F) F (b * dy) := by
          rw [hdy, map_mul]
        _ = algebraMap (𝓞 F) F (ay + b * dy) := by rw [map_add]
    have hvalYb : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) ≤
        WithZero.exp (-1 : ℤ) := by
      have heq : HeightOneSpectrum.valuation F v ((y : F) + (b : F)) =
          HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F (ay + b * dy)) := by
        calc
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) * 1 := by simp
          _ = HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
                HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F dy) := by rw [hvalDy]
          _ = HeightOneSpectrum.valuation F v
                (((y : F) + (b : F)) * algebraMap (𝓞 F) F dy) := by
            rw [(v.valuation F).map_mul]
          _ = _ := by rw [hmul]
      rw [heq]
      exact hvalNum
    have hvalErr : HeightOneSpectrum.valuation F v
        (-(y : F) * algebraMap (𝓞 F) F x.out - (b : F) * algebraMap (𝓞 F) F x.out) ≤
          WithZero.exp (-1 : ℤ) := by
      have hident : -(y : F) * algebraMap (𝓞 F) F x.out -
          (b : F) * algebraMap (𝓞 F) F x.out =
            -(((y : F) + (b : F)) * algebraMap (𝓞 F) F x.out) := by ring
      rw [hident, (v.valuation F).map_neg, (v.valuation F).map_mul]
      have hxval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤ 1 :=
        v.valuation_le_one x.out
      calc
        HeightOneSpectrum.valuation F v ((y : F) + (b : F)) *
            HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F x.out) ≤
            WithZero.exp (-1 : ℤ) * 1 :=
          mul_le_mul hvalYb hxval (zero_le) (zero_le)
        _ = WithZero.exp (-1 : ℤ) := mul_one _
    have hphase' := hphaseCongr
      (-(y : F) * algebraMap (𝓞 F) F x.out)
      ((b : F) * algebraMap (𝓞 F) F x.out) hvalErr
    have harg : -((y : F) * algebraMap (𝓞 F) F x.out / (p : F)) =
        (-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F) := by ring
    calc
      A.ψ v (algebraMap F (v.adicCompletion F)
        (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) =
          A.ψ v (algebraMap F (v.adicCompletion F)
            ((-(y : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := by rw [harg]
      _ = A.ψ v (algebraMap F (v.adicCompletion F)
            (((b : F) * algebraMap (𝓞 F) F x.out) / (p : F))) := hphase'
      _ = ψ (-(residue v (y : F)) * x) := by
        symm
        simpa [a, b, mul_comm] using hψeval (-a) x
  have hfiniteT (y : S.R) : localT R v e (y : F) =
      ∑ x : 𝓞 F ⧸ v.asIdeal,
        χe x * ψ (-(residue v (y : F)) * x) := by
    unfold localT
    rw [a2_bridge_FINITE_CHAR_finsum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      _ = χe x * A.ψ v (algebraMap F (v.adicCompletion F)
          (-((y : F) * algebraMap (𝓞 F) F x.out / (p : F)))) := by
        rw [← hχeeval x]
      _ = _ := by rw [hphase y x]
  have hresOne : residue v (1 : F) = 1 := by
    simpa using SB.residue_algebraMap v (1 : 𝓞 F)
  have hresZero : residue v (0 : F) = 0 := by
    simpa using SB.residue_algebraMap v (0 : 𝓞 F)
  have hfiniteShift (y : S.R) : localT R v e (y : F) =
      gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
    calc
      localT R v e (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
          χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
      _ = gaussSum χe (ψ.mulShift (-(residue v (y : F)))) := by
        simp [gaussSum, AddChar.mulShift_apply]
  have hfiniteOne : localT R v e 1 = gaussSum χe (ψ.mulShift (-1)) := by
    simpa [hresOne] using hfiniteShift (1 : S.R)
  have hχ₁minus : χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hres : residue v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) = -1 := by
      simpa using hresAlg (-1 : 𝓞 F ⧸ v.asIdeal)
    have hresNeg : residue v (-1 : F) = -1 := by
      simpa using SB.residue_algebraMap v (-1 : 𝓞 F)
    calc
      χ₁ (-1 : 𝓞 F ⧸ v.asIdeal) =
          chiPow D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) 1 := hχ₁eval _
      _ = chi D v (algebraMap (𝓞 F) F ((-1 : 𝓞 F ⧸ v.asIdeal).out)) :=
        by simpa [pow_one] using
          SB.chiPow_nonzero v _ 1 (by rw [hres]; exact neg_ne_zero.mpr one_ne_zero)
      _ = chi D v (-1 : F) := SB.chi_congr v _ _ (hres.trans hresNeg.symm)
      _ = 1 := SB.chi_minus_one v hv
  have hχeminus : χe (-1 : 𝓞 F ⧸ v.asIdeal) = 1 := by
    have hχ₁unit : χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχ₁minus
    calc
      χe (-1 : 𝓞 F ⧸ v.asIdeal) = χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by simp
      _ = (χ₁ ^ e) (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) := by rw [hχpow_eq]
      _ = χ₁ ((↑((-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e) : 𝓞 F ⧸ v.asIdeal)) :=
        MulChar.zpow_apply_coe χ₁ e (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
      _ = χ₁ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) ^ e := hmulchar_zpow χ₁ (-1)
      _ = 1 := by rw [hχ₁unit]; simp
  have hshiftGauss : gaussSum χe (ψ.mulShift (-1)) = gaussSum χe ψ := by
    have h := gaussSum_mulShift_eq χe ψ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ)
    have hχeunit : χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      simpa using hχeminus
    have hinvχ : χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) = 1 := by
      calc
        χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) =
            (χe (-1 : (𝓞 F ⧸ v.asIdeal)ˣ))⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = 1 := by rw [hχeunit]; simp
    calc
      gaussSum χe (ψ.mulShift (-1)) = χe⁻¹ (-1 : (𝓞 F ⧸ v.asIdeal)ˣ) *
          gaussSum χe ψ := h
      _ = gaussSum χe ψ := by rw [hinvχ, one_mul]
  have hfiniteOneGauss : localT R v e 1 = gaussSum χe ψ := hfiniteOne.trans hshiftGauss
  have hscale : residue v (y : F) ≠ 0 →
      localT R v e (y : F) =
        star (chi D v (y : F)) ^ e * localT R v e 1 := by
    intro hy
    let a : 𝓞 F ⧸ v.asIdeal := residue v (y : F)
    have ha : a ≠ 0 := by simpa [a] using hy
    let u : (𝓞 F ⧸ v.asIdeal)ˣ := (isUnit_iff_ne_zero.mpr ha).unit
    have hu : (u : 𝓞 F ⧸ v.asIdeal) = a :=
      (isUnit_iff_ne_zero.mpr ha).unit_spec
    have hshift : ψ.mulShift (-a) = (ψ.mulShift (-1)).mulShift (u : 𝓞 F ⧸ v.asIdeal) := by
      ext x
      simp [AddChar.mulShift_apply, hu, mul_assoc]
    have hsum := gaussSum_mulShift_eq χe (ψ.mulShift (-1)) u
    have hunitGauss : gaussSum χe (ψ.mulShift (-a)) =
        χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := by
      rw [hshift]
      exact hsum
    have hchiA : χe u = chi D v (y : F) ^ e := by
      have hresu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) =
          residue v (y : F) := by rw [hresAlg, hu]
      have hresu_ne : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresu]
        exact hy
      calc
        χe u = chiPow D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) e := hχeeval u
        _ = chi D v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ^ e :=
          SB.chiPow_nonzero v _ e hresu_ne
        _ = chi D v (y : F) ^ e := by rw [SB.chi_congr v _ _ hresu]
    have hnormChi : ‖chi D v (y : F)‖ = 1 := SB.chi_norm v _ hy
    have hnormPow : ‖chi D v (y : F) ^ e‖ = 1 := by
      rw [Complex.norm_zpow, hnormChi]
      norm_num
    have hinv : (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F)) ^ e := by
      calc
        (chi D v (y : F) ^ e)⁻¹ = star (chi D v (y : F) ^ e) :=
          Complex.inv_eq_conj hnormPow
        _ = star (chi D v (y : F)) ^ e := by simp
    have hχinv : χe⁻¹ u = star (chi D v (y : F)) ^ e := by
      calc
        χe⁻¹ u = (χe u)⁻¹ := MulChar.inv_apply_eq_inv' χe _
        _ = star (chi D v (y : F)) ^ e := by rw [hchiA, hinv]
    calc
      localT R v e (y : F) = gaussSum χe (ψ.mulShift (-a)) := by
        simpa [a] using hfiniteShift y
      _ = χe⁻¹ u * gaussSum χe (ψ.mulShift (-1)) := hunitGauss
      _ = star (chi D v (y : F)) ^ e * localT R v e 1 := by
        rw [hχinv, ← hfiniteOne]
  have hzeroSum : localT R v e (0 : F) =
      (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
    have hsum : localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := by
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χe x * ψ (-(residue v (0 : F)) * x) := by
          simpa [hresZero] using hfiniteT (0 : S.R)
        _ = _ := by simp [hresZero]
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hcardPos : 1 ≤ Ideal.absNorm v.asIdeal := by
      have h : 1 ≤ Fintype.card (𝓞 F ⧸ v.asIdeal) := by
        exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨0⟩)
      rw [hcard] at h
      exact h
    by_cases he : e % 6 = 0
    · have hunitCard : Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Ideal.absNorm v.asIdeal - 1 := by
        calc
          Nat.card (𝓞 F ⧸ v.asIdeal)ˣ = Fintype.card (𝓞 F ⧸ v.asIdeal)ˣ :=
          Nat.card_eq_fintype_card
          _ = Fintype.card (𝓞 F ⧸ v.asIdeal) - 1 := Fintype.card_units (α := 𝓞 F ⧸ v.asIdeal)
          _ = Ideal.absNorm v.asIdeal - 1 := by rw [hcard]
      have hunitReal : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℝ) = qI v.asIdeal - 1 := by
        rw [hunitCard]
        dsimp [qI]
        rw [Nat.cast_sub hcardPos]
        norm_num
      have hunitComplex : (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) =
          (qI v.asIdeal : ℂ) - 1 := by exact_mod_cast hunitReal
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = ∑ x : 𝓞 F ⧸ v.asIdeal,
              (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ) x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hχe_one he]
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (1 : AddChar (𝓞 F ⧸ v.asIdeal) ℂ) := by simp [gaussSum]
        _ = (Nat.card (𝓞 F ⧸ v.asIdeal)ˣ : ℂ) := by rw [gaussSum_one_one]
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by
          simpa [he] using hunitComplex
    ·
      have hsumZero : (∑ x : 𝓞 F ⧸ v.asIdeal, χe x) = 0 := by
        simpa [gaussSum] using (MulChar.sum_eq_zero_of_ne_one (hχe_ne_one he))
      calc
        localT R v e (0 : F) = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x := hsum
        _ = 0 := hsumZero
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := by simp [he]
  constructor
  · by_cases hy : residue v (y : F) ≠ 0
    · simpa [hy] using hscale hy
    · have hresY0 : residue v (y : F) = 0 := by simpa using hy
      have hfiniteTzero : localT R v e (0 : F) =
          ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
        simpa using hfiniteT (0 : S.R)
      have hlocalY0 : localT R v e (y : F) = localT R v e (0 : F) := by
        calc
          localT R v e (y : F) =
              ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (y : F)) * x) := hfiniteT y
          _ = ∑ x : 𝓞 F ⧸ v.asIdeal, χe x * ψ (-(residue v (0 : F)) * x) := by
            rw [hresY0, hresZero]
          _ = localT R v e (0 : F) := hfiniteTzero.symm
      calc
        localT R v e (y : F) = localT R v e (0 : F) := hlocalY0
        _ = (if e % 6 = 0 then qI v.asIdeal - 1 else 0) := hzeroSum
        _ = if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e *
              localT R v e 1 else if e % 6 = 0 then qI v.asIdeal - 1 else 0 := by
          have hdiv : (e % 6 = 0) ↔ (6 : ℤ) ∣ e := Int.dvd_iff_emod_eq_zero.symm
          have hresNot : ¬(residue v (y : F) ≠ 0) := by simp [hresY0]
          by_cases h : (6 : ℤ) ∣ e
          · rw [if_pos (hdiv.mpr h), if_pos (hdiv.mpr h)]
            rw [if_neg hresNot]
            exact Complex.ofReal_sub _ _
          · rw [if_neg (fun he => h (hdiv.mp he)), if_neg (fun he => h (hdiv.mp he))]
            rw [if_neg hresNot]
            rfl
  constructor
  · intro he
    have hχne := hχe_ne_one he
    have hlocalEq : localT R v e 1 = gaussSum χe ψ := hfiniteOneGauss
    have hprod : gaussSum χe ψ * star (gaussSum χe ψ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        gaussSum χe ψ * star (gaussSum χe ψ) =
            gaussSum χe ψ * gaussSum χe⁻¹ ψ⁻¹ := by rw [star_gaussSum_eq]
        _ = _ := gaussSum_mul_gaussSum_eq_card hχne hψprim
    have hnormSqC : (Complex.normSq (gaussSum χe ψ) : ℂ) =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℂ) := by
      calc
        (Complex.normSq (gaussSum χe ψ) : ℂ) =
            gaussSum χe ψ * star (gaussSum χe ψ) := (Complex.mul_conj _).symm
        _ = _ := hprod
    have hnormSq : ‖gaussSum χe ψ‖ ^ 2 =
        (Fintype.card (𝓞 F ⧸ v.asIdeal) : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast hnormSqC
    have hcard : Fintype.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    have hnormSqQ : ‖gaussSum χe ψ‖ ^ 2 = qI v.asIdeal := by
      rw [hnormSq, hcard]
      rfl
    have hnormG : ‖gaussSum χe ψ‖ = qI v.asIdeal ^ (1 / 2 : ℝ) := by
      calc
        ‖gaussSum χe ψ‖ = Real.sqrt (‖gaussSum χe ψ‖ ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        _ = Real.sqrt (qI v.asIdeal) := by rw [hnormSqQ]
        _ = qI v.asIdeal ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    simpa [hlocalEq] using hnormG
  · obtain ⟨χ0, hχ0eval⟩ := hchars (0 : ℤ)
    have hχ0one : χ0 = 1 := by
      apply MulChar.ext
      intro u
      have hu : residue v (algebraMap (𝓞 F) F (u : 𝓞 F ⧸ v.asIdeal).out) ≠ 0 := by
        rw [hresAlg]
        exact u.ne_zero
      rw [hχ0eval u, SB.chiPow_nonzero v _ 0 hu, zpow_zero]
      simp
    have hfiniteT0 (y : S.R) : localT R v 0 (y : F) =
        ∑ x : 𝓞 F ⧸ v.asIdeal, χ0 x * ψ (-(residue v (y : F)) * x) := by
      unfold localT
      rw [a2_bridge_FINITE_CHAR_finsum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← hχ0eval x, hphase y x]
    have hfiniteShift0 (y : S.R) : localT R v 0 (y : F) =
        gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
      calc
        localT R v 0 (y : F) = ∑ x : 𝓞 F ⧸ v.asIdeal,
            χ0 x * ψ (-(residue v (y : F)) * x) := hfiniteT0 y
        _ = gaussSum χ0 (ψ.mulShift (-(residue v (y : F)))) := by
          simp [gaussSum, AddChar.mulShift_apply]
    have hlocalZero : localT R v 0 1 =
        gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
          (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)) := by
      calc
        localT R v 0 1 = gaussSum χ0 (ψ.mulShift (-1)) := by
          simpa [hresOne] using hfiniteShift0 (1 : S.R)
        _ = gaussSum (1 : MulChar (𝓞 F ⧸ v.asIdeal) ℂ)
              (ψ.mulShift (-1)) := by rw [hχ0one]
    have hψshiftPrim : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).IsPrimitive := by
      intro a ha htriv
      have hnonzero : (-1 : 𝓞 F ⧸ v.asIdeal) * a ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha
      have htriv' : ψ.mulShift ((-1 : 𝓞 F ⧸ v.asIdeal) * a) = 1 := by
        simpa only [AddChar.mulShift_mulShift] using htriv
      exact (hψprim hnonzero) htriv'
    have hψshiftNe : ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal) ≠ 1 := by
      intro h
      have h' : (ψ.mulShift (-1 : 𝓞 F ⧸ v.asIdeal)).mulShift 1 = 1 := by
        simpa using h
      exact (hψshiftPrim one_ne_zero) h'
    rw [hlocalZero]
    exact gaussSum_one_left hψshiftNe
/-- po:euler-local-factorization, 05:444-550. Cross-prime exponents cancel modulo six. -/
theorem cross_prime_exponent_cancel (e e' l l' : ℕ) :
    6 ∣ 2 * (e + 3 * l) * (e' + 3 * l') + 4 * e * e' := by
  refine ⟨e * e' + e * l' + l * e' + 3 * l * l', ?_⟩
  ring

/-- po:H-local-bounds: C,Q0 chosen before the field, set S, phases, or frequency.
This is the absolute-cutoff obligation used when choosing S in A1. -/
theorem po_H_local_bounds_absolute :
  ∃ C Q0 : ℝ, 0 < C ∧ 1 < Q0 ∧
  ∀ (F' : Type) [Field F'] [NumberField F'] (CE' : ℕ) (cond' : Ideal (𝓞 F'))
    (D' : FieldData F') (S' : SData F' CE' cond') (H' : HilbertData F') (Bd' : BData S' H')
    (A' : AddCharData F') (ϑ' : HeckeChar F') (bc' : BalancedChoices D' S' H' Bd')
    (μ' : ∀ v : FinPlace F', Theta.LocHaar v) (v0' : InfinitePlace F')
    (R' : ReflectionSetup D' S' H' Bd' A' ϑ' bc' μ' v0') (η' : HeckeChar F')
    (U' : FrequencyData S' D' η'),
      EulerHypotheses R' η' → HasPoHLocalBounds R' η' U' C Q0 := by
  sorry
/-- po:H-local-bounds, 05:660-729. The numerical Q1 cutoff is fixed independently of arithmetic data. -/
theorem po_H_cutoff_from_constants (C Q0 : ℝ) : ∃ Q1 : ℕ,
  Q0 < (Q1 : ℝ) ∧ ∀ Q : ℝ, (Q1 : ℝ) < Q → C * Q ^ (-(1 + 1 / 4000 : ℝ)) < 1 / 2 := by
  let M : ℝ := max Q0 (max 1 (2 * C))
  obtain ⟨Q1, hQ1⟩ := exists_nat_gt M
  refine ⟨Q1, ?_, ?_⟩
  · exact lt_of_le_of_lt (le_max_left _ _) hQ1
  · intro Q hQ
    have hMQ : M < Q := lt_trans hQ1 hQ
    have hQone : 1 < Q := lt_of_le_of_lt
      (le_trans (le_max_left 1 (2 * C)) (le_max_right Q0 (max 1 (2 * C)))) hMQ
    have hQpos : 0 < Q := by linarith
    by_cases hC : C ≤ 0
    · have hp : 0 < Q ^ (-(1 + 1 / 4000 : ℝ)) := Real.rpow_pos_of_pos hQpos _
      have hle : C * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC hp.le
      linarith
    · have hCpos : 0 < C := lt_of_not_ge hC
      have hQ2C : 2 * C < Q := lt_of_le_of_lt
        (le_trans (le_max_right 1 (2 * C)) (le_max_right Q0 (max 1 (2 * C)))) hMQ
      have hpow : Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ Q ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hQone.le
        norm_num
      rw [Real.rpow_neg_one] at hpow
      have hdiv : C / Q < 1 / 2 := (div_lt_iff₀ hQpos).2 (by nlinarith)
      calc
        C * Q ^ (-(1 + 1 / 4000 : ℝ)) ≤ C * Q⁻¹ :=
          mul_le_mul_of_nonneg_left hpow hCpos.le
        _ < 1 / 2 := by simpa [div_eq_mul_inv] using hdiv
/-- Named refutation gate: saturated subtraction changes the J=t-1 boundary in a naive translation. -/
theorem localC_natural_subtraction_gate : (0 - 1 + 1 : ℕ) = 1 ∧ (0 + 1 - 1 : ℕ) = 0 := by decide

/-- Named refutation gate: ordinary zeroth powers cannot implement the masked nonunit value. -/
theorem zeroth_power_mask_gate : (0 : ℂ) ^ (0 : ℕ) ≠ 0 := by norm_num

end PoissonSupplementary

section FinalPoissonClauses
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0) (sd : S.SelfDualMeasure A)
  (W : PoissonWeights (S := S)) (η : HeckeChar F) (U : FrequencyData S D η)
  (HA : HeckeAnalysis F) (HC : EulerCorrection R η U)

def continuedCalF (u : U.U) (ξ w z : ℂ) : ℂ :=
  HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
    HA.LS S (η * (U.kummer u)⁻¹) ξ

/-- po:H-product / prop:euler-product: continuation identity with coordinatewise meromorphy.
The raw calF tsum is only compared in its convergence domain. -/
theorem po_euler_meromorphic_identity : EulerHypotheses R η →
  (∀ u ξ w z, initialRegion ξ w z → continuedCalF R η U HA HC u ξ w z = calF R η U u ξ w z) ∧
  (∀ u w z, MeromorphicOn (fun ξ => continuedCalF R η U HA HC u ξ w z)
    {ξ | eulerNeighborhood ![ξ,w,z]}) ∧
  (∀ u ξ z, MeromorphicOn (fun w => continuedCalF R η U HA HC u ξ w z)
    {w | eulerNeighborhood ![ξ,w,z]}) ∧
  (∀ u ξ w, MeromorphicOn (fun z => continuedCalF R η U HA HC u ξ w z)
    {z | eulerNeighborhood ![ξ,w,z]}) := by
  sorry
end FinalPoissonClauses
section CanonicalEulerObject
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

/-- Actual infinite-product definition; it assumes no convergence or nonvanishing result. -/
def canonicalEulerCorrection : EulerCorrection R η U where
  H u p := ∏' v : {v : FinPlace F // v ∉ S.Sf},
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)
  H_eq _ _ := rfl

private lemma euler_frequency_valuation_one_eq_zero (v : FinPlace F) (hv : v ∉ S.Sf)
    (hcount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr U.one : F))) :
    frequencyValuation η U U.one v = 0 := by
  classical
  let x : S.R := U.repr U.one
  have hx : (x : F) ≠ 0 := U.repr_nonzero U.one
  have hxnorm : S.absS (S.diag (x : F)) = 1 := by
    rw [← U.q_eq_absS U.one, U.q_one]
  letI : IsTotallyComplex F := D.isTotallyComplex
  have hprod := prod_abs_eq_one hx
  have hf_supp : (Function.mulSupport fun w => ‖FinitePlace.embedding w (x : F)‖).Finite :=
    finitePlace_mk_hasFiniteMulSupport hx
  have h_split : (∏ᶠ w : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding w (x : F)‖) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ := by
    have h_union := finprod_mem_union' (hst := disjoint_compl_right)
      (hs := S.Sf.finite_toSet.inter_of_left _)
      (ht := Set.Finite.subset hf_supp Set.inter_subset_right)
      (f := fun w => ‖FinitePlace.embedding w (x : F)‖)
    rw [Set.union_compl_self, finprod_mem_univ] at h_union
    rw [finprod_mem_coe_finset] at h_union
    exact h_union
  have h_prod_decomp : (∏ᶠ w : FinitePlace F, w (x : F)) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    change (∏ᶠ w : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding w (x : F)‖) = _
    exact h_split
  rw [h_prod_decomp] at hprod
  have h_absS : S.absS (S.diag (x : F)) =
      (∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
        ∏ w : InfinitePlace F, w (x : F) ^ w.mult := absS_diag_eq S (x : F)
  have h_prod_absS : S.absS (S.diag (x : F)) *
      (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) = 1 := by
    rw [h_absS]
    calc
      ((∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
          ∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
          (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖)
        = (∏ w : InfinitePlace F, w (x : F) ^ w.mult) *
            ((∏ w ∈ S.Sf, ‖FinitePlace.embedding w (x : F)‖) *
              ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) := by ring
      _ = 1 := hprod
  have hext : ∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ = 1 := by
    simpa [hxnorm] using h_prod_absS
  have h_eq : (∏ᶠ w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖) =
      ∏ w ∈ hf_supp.toFinset with w ∉ S.Sf, ‖FinitePlace.embedding w (x : F)‖ :=
    finprod_mem_eq_prod_filter (fun w => ‖FinitePlace.embedding w (x : F)‖)
      ((S.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) hf_supp
  have hprod_fin : (∏ w ∈ hf_supp.toFinset with w ∉ S.Sf,
      ‖FinitePlace.embedding w (x : F)‖) = 1 := by
    rw [← h_eq]
    exact hext
  have hle : ∀ w ∈ hf_supp.toFinset.filter (fun w => w ∉ S.Sf),
      ‖FinitePlace.embedding w (x : F)‖₊ ≤ 1 := by
    intro w hw
    have hws := Finset.mem_filter.mp hw
    exact_mod_cast norm_embedding_le_one_of_valuation_le_one w (x : F)
      (x.property w hws.2)
  have hprod_fin_nn : (∏ w ∈ hf_supp.toFinset with w ∉ S.Sf,
      ‖FinitePlace.embedding w (x : F)‖₊) = 1 := by
    apply NNReal.coe_injective
    simpa using hprod_fin
  have hterms := (Finset.prod_eq_one_iff_of_le_one hle).mp hprod_fin_nn
  have hnorm_v : ‖FinitePlace.embedding v (x : F)‖ = 1 := by
    by_cases hmem : v ∈ hf_supp.toFinset
    · have hterm := hterms v (Finset.mem_filter.mpr ⟨hmem, hv⟩)
      have htermR : (‖FinitePlace.embedding v (x : F)‖₊ : ℝ) = 1 := by
        exact_mod_cast hterm
      simpa using htermR
    · have hnot : v ∉ Function.mulSupport
          (fun w => ‖FinitePlace.embedding w (x : F)‖) := by
        intro h
        apply hmem
        simpa using h
      have hnot' : ¬ ‖FinitePlace.embedding v (x : F)‖ ≠ 1 := by
        intro hne
        exact hnot ((Function.mem_mulSupport).2 hne)
      exact not_not.mp hnot'
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^
      (-FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))) = 1 := by
    rw [← norm_embedding_eq_absNorm_zpow v (x : F) hx, hnorm_v]
  have hq : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have htoNat : (FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))).toNat = 0 := by
    by_contra hn
    let n := (FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F))).toNat
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hncast : (n : ℤ) = FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (x : F)) :=
      Int.toNat_of_nonneg hcount
    have hpow' : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) = 1 := by
      rw [hncast]
      exact hpow
    have hgt : 1 < (Ideal.absNorm v.asIdeal : ℝ) ^
        n :=
      one_lt_pow₀ hq hnpos.ne'
    have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) < 1 := by
      rw [zpow_neg, zpow_natCast]
      exact (inv_lt_one₀ (pow_pos (by positivity) _)).2 hgt
    linarith
  simpa [frequencyValuation, x] using htoNat

/-- po:H-local-bounds: installing the numerical cutoff in the frozen CE parameter implies
small principal factors on the entire enlarged neighborhoods. -/
theorem po_H_principal_cutoff (C Q0 : ℝ) (Q1 : ℕ) :
  EulerHypotheses R η → HasPoHLocalBounds R η U C Q0 → Q0 < (Q1 : ℝ) → Q1 ≤ CE →
  (∀ Q : ℝ, (Q1 : ℝ) < Q → C * Q ^ (-(1 + 1 / 4000 : ℝ)) < 1 / 2) →
  ∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2 := by
  intro hEuler hBounds hQ0 hQ1 hCut v hv p hp
  have hreprCount : 0 ≤ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr U.one : F)) :=
    (U.sixth_power_free U.one v hv).1
  have hfreq := euler_frequency_valuation_one_eq_zero (D := D) (S := S)
    (η := η) (U := U) v hv hreprCount
  have hnorm : (Q1 : ℝ) < qI v.asIdeal := by
    have hnot : ¬ Ideal.absNorm v.asIdeal ≤ CE := by
      intro hle
      exact hv (S.euler_mem v hle)
    have hCE : CE < Ideal.absNorm v.asIdeal := Nat.lt_of_not_ge hnot
    have hqCE : (CE : ℝ) < qI v.asIdeal := by
      change (CE : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
      exact_mod_cast hCE
    have hQ1CE : (Q1 : ℝ) ≤ (CE : ℝ) := by exact_mod_cast hQ1
    exact lt_of_le_of_lt hQ1CE hqCE
  have hnorm0 : Q0 < qI v.asIdeal := lt_trans hQ0 hnorm
  rcases hBounds with ⟨hC, hQ0pos, hLocal⟩
  have hlocal := (hLocal U.one v hv p hnorm0 hp).2
  have hcut := hCut (qI v.asIdeal) hnorm
  have hexp : (-1 - 1 / 4000 : ℝ) = -(1 + 1 / 4000 : ℝ) := by ring
  have hlocal' : ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ ≤
      C * qI v.asIdeal ^ (-(1 + 1 / 4000 : ℝ)) := by
    rw [if_pos hfreq] at hlocal
    rw [hexp] at hlocal
    exact hlocal
  exact lt_of_le_of_lt hlocal' hcut
end CanonicalEulerObject
end ArtinPrimitiveRoots.A2
