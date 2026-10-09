import ArtinPrimitiveRoots.A2.Reflection.Missing
import ArtinPrimitiveRoots.A2.Interface

set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.A2
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
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

def WeightSpec : Prop := weightFourier sd W 0 = 0 ∧ weightM R sd W (1 / 6) ≠ 0

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


variable (η : HeckeChar F) (U : FrequencyData S D η)

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

/-- H_u is a proposed limit object; its HasProd law is an explicit node conclusion below. -/
structure EulerCorrection (η : HeckeChar F) (U : FrequencyData S D η) where
  H : U.U → Triple → ℂ
  H_eq : ∀ u p, H u p = ∏' v : {v : FinPlace F // v ∉ S.Sf},
    normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)

variable (HC : EulerCorrection R η U)

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

end ArtinPrimitiveRoots.A2

namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
def eulerGoodTermModel (Q V W D1 E1 : ℂ) (e l k m : ℕ) : ℂ :=
  if e = 0 then
    if l = 0 then
      if k = 0 then V ^ m else if m = 0 then W ^ k else 0
    else if l % 2 = 0 then
      if k = 0 then
        if l / 2 ≤ m then E1 ^ (l / 2) * (1 - Q⁻¹) * V ^ (m - l / 2) else 0
      else if k = 1 then
        if m = l / 2 then E1 ^ (l / 2) * W else 0
      else 0
    else 0
  else if l % 2 = 0 then
    if k = 0 then
      if m = l / 2 then -D1 * E1 ^ (l / 2) else 0
    else if k = 1 then
      if l / 2 < m then -(Q - 1) * D1 * E1 ^ (l / 2) * W * V ^ (m - l / 2) else 0
    else 0
  else 0
end ArtinPrimitiveRoots.Proofs.a2_euler_sol
