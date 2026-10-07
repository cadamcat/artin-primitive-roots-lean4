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
/-- po:C-local-values: the one-prime T_v table, including the masked v≡0 case. -/
theorem po_C_local_T_values : ∀ v, v ∉ S.Sf → ∀ e : ℤ, ∀ y : S.R,
  localT R v e (y : F) =
    (if residue v (y : F) ≠ 0 then star (chi D v (y : F)) ^ e * localT R v e 1
      else if e % 6 = 0 then qI v.asIdeal - 1 else 0) ∧
  (e % 6 ≠ 0 → ‖localT R v e 1‖ = qI v.asIdeal ^ (1 / 2 : ℝ)) ∧ localT R v 0 1 = -1 := by
  sorry
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
  sorry
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

/-- po:H-local-bounds: installing the numerical cutoff in the frozen CE parameter implies
small principal factors on the entire enlarged neighborhoods. -/
theorem po_H_principal_cutoff (C Q0 : ℝ) (Q1 : ℕ) :
  EulerHypotheses R η → HasPoHLocalBounds R η U C Q0 → Q0 < (Q1 : ℝ) → Q1 ≤ CE →
  (∀ Q : ℝ, (Q1 : ℝ) < Q → C * Q ^ (-(1 + 1 / 4000 : ℝ)) < 1 / 2) →
  ∀ v hv p, eulerNeighborhood p →
    ‖normalizedLocal R η U U.one v hv (p 0) (p 1) (p 2) - 1‖ < 1 / 2 := by
  sorry
end CanonicalEulerObject
end ArtinPrimitiveRoots.A2
