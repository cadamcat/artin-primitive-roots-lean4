import ArtinPrimitiveRoots.TypeII.Marked
import ArtinPrimitiveRoots.Ext.TypeIIInputs

/-! Shared definitions for the Poisson–Dirichlet determinant chain.
Sources: PD `02-preliminaries.tex:73-235`, `03-determinant.tex:7-268`,
and `05-major-arcs.tex:9-20`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

/-- `def:pd-physical` — the growing moment parameter `J=⌊L^.01⌋`. -/
noncomputable def momentJ (x : ℝ) : ℕ :=
  ⌊Real.rpow (Real.log x) (1 / 100 : ℝ)⌋₊

/-- `def:pd-physical` — `M_J=J+1` prime slots in each group. -/
noncomputable def slotCount (x : ℝ) : ℕ := momentJ x + 1

/-- `def:pd-physical` — the path length parameter `R=⌈L^.5/2⌉`. -/
noncomputable def momentR (x : ℝ) : ℕ :=
  ⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊

/-- `def:pd-physical` — `N_R=2R`. -/
noncomputable def pathLength (x : ℝ) : ℕ := 2 * momentR x

/-- The set of relevant dyadic scales `Y=2^k`; the logarithmic bounds include all products of
one prime from each fixed marked group. -/
noncomputable def dyadicScales (x : ℝ) (K : ℕ) : Finset ℝ :=
  ((Finset.range (⌊((K + 1 : ℕ) : ℝ) *
      Real.rpow (Real.log x) (21 / 100 : ℝ) / Real.log 2⌋₊ + 1)).image
      (fun k => (2 : ℝ) ^ k)).filter fun Y =>
        (1 / 20 : ℝ) * Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ Real.log Y ∧
          Real.log Y ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)

/-- One prime label from each group, used for the products `a` and `b`. -/
def IsMarkedPrimeTuple (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (t : Fin K → ℕ) : Prop :=
  ∀ i, t i ∈ primeBand x (a i)

/-- Full `M_J`-slot prime lists in the marked groups. -/
abbrev PrimeLists (x : ℝ) (K : ℕ) := Fin K → Fin (slotCount x) → ℕ

/-- Validity of the distinct prime labels attached to a physical position. -/
def ValidPrimeLists (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (p : PrimeLists x K) : Prop :=
  (∀ i j, (p i j).Prime ∧ p i j ∈ primeBand x (a i)) ∧
    ∀ i j j', j ≠ j' → p i j ≠ p i j'

/-- The product left after omitting one label in each group. -/
noncomputable def omissionProduct {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (omitted : Fin K → Fin (slotCount x)) : ℕ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount x), if j ≠ omitted i then p i j else 1

/-- Distance to the nearest integer, i.e. the norm on `ℝ/ℤ`. -/
noncomputable def circleDistance (t : ℝ) : ℝ :=
  sInf (Set.range fun z : ℤ => |t - (z : ℝ)|)

/-- First goodness test of PD `03-determinant.tex:242-248`. -/
def goodTestOne (x Y d₀ : ℝ) {K : ℕ} (p : PrimeLists x K) (r : ℝ) : Prop :=
  ∀ omitted : Fin K → Fin (slotCount x),
    d₀ ≤ (omissionProduct p omitted : ℝ) →
    (omissionProduct p omitted : ℝ) < 2 * d₀ →
      ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
        Real.rpow Y (-(7 / 10 : ℝ)) <
          circleDistance ((l : ℝ) * (omissionProduct p omitted : ℝ) * r)

/-- A trial product `D Z T_f` for the second goodness test of PD
`03-determinant.tex:249-257`. -/
def IsGoodnessTrialValue {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (d₀ : ℝ) (I : Finset (Fin K))
    (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ) : Prop :=
  ∃ omitted : Fin K → Fin (slotCount x), ∃ z : Fin K → ℕ,
    n = omissionProduct p omitted *
      (∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1) *
      (∏ i : Fin K, if i ∉ I then fresh i else 1) ∧
    d₀ ≤ (omissionProduct p omitted : ℝ) ∧
      (omissionProduct p omitted : ℝ) < 2 * d₀ ∧
      ∀ i, i ∈ I ∧ i ≠ iStar → z i ∈ primeBand x (a i)

/-- Fresh prime choices outside `I`, with product probability `μ_i(p)=1/(p V_i)`. -/
def IsFreshChoice (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (I : Finset (Fin K)) (fresh : Fin K → ℕ) : Prop :=
  (∀ i, i ∈ I → fresh i = 1) ∧
    ∀ i, i ∉ I → fresh i ∈ primeBand x (a i)

/-- The probability of a fresh-prime choice. -/
noncomputable def freshChoiceWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (I : Finset (Fin K)) (fresh : Fin K → ℕ) : ℝ :=
  if IsFreshChoice x a I fresh then
    ∏ i : Fin K, if i ∉ I then
      1 / (bandMass x (a i) * (fresh i : ℝ)) else 1
  else 0

/-- Second goodness test of PD `03-determinant.tex:249-257`. -/
noncomputable def goodTestTwo (x d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (r : ℝ) : Prop :=
  ∀ I : Finset (Fin K), ∀ hI : I.Nonempty,
    let iStar := I.max' hI
    (∑' fresh : Fin K → ℕ,
      if IsFreshChoice x a I fresh ∧
          ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r) ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a iStar))
      then freshChoiceWeight x a I fresh else 0) ≤
        Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a iStar))

/-- A physical ratio is good when it passes both deterministic and probabilistic tests. -/
def IsGoodRatio (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (r : ℝ) : Prop :=
  goodTestOne x Y d₀ p r ∧ goodTestTwo x d₀ K a p r

/-- A smooth dyadic partition of unity as used in the Cauchy decomposition. -/
def IsDyadicPartition (eta : ℝ → ℝ) : Prop :=
  ∀ y : ℝ, 0 < y → ∑' k : ℤ, eta (y / (2 : ℝ) ^ k) = 1

/-- The product of a marked prime tuple. -/
noncomputable def tupleProduct {K : ℕ} (t : Fin K → ℕ) : ℕ :=
  ∏ i : Fin K, t i

/-- Number of distinct prime factors of an integer. -/
noncomputable def omega (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p => p.Prime ∧ p ∣ n).card

/-- Divisor-counting function `τ(n)`, represented by its finite divisor set. -/
noncomputable def tau (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun d => d ∣ n).card

/-- The Kloosterman sum `K_m(h,k)` over reduced residue classes modulo `m`. -/
noncomputable def kloostermanSum (m h k : ℕ) : ℂ :=
  ∑ y ∈ (Finset.range m).filter (fun y => Nat.Coprime y m),
    additiveCharacter
      ((((h * y + k * ((y : ZMod m)⁻¹).val : ℕ) : ℝ) / (m : ℝ)))

/-- The original bilinear sum for a coefficient family. -/
noncomputable def coefficientBilinearSum (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (F : ℕ → ℂ) : ℂ :=
  markedBilinearSum x K a q_d F (family.Hm x) (family.Hn x)
    (family.interval x) (family.alpha x) beta

/-- The dyadic piece `S_Y` from the Cauchy expansion in PD `03-determinant.tex:77-104`. -/
noncomputable def dyadicCauchyPiece (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q_d Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (F : ℕ → ℂ) (eta : ℝ → ℝ) : ℂ :=
  ∑' h : ℕ,
    if 0 < h then
      (F h) * (q_d ^ markedOmega x K a h : ℂ) *
        ∑' t : Fin K → ℕ,
          if IsMarkedPrimeTuple x K a t then
            ((∏ i : Fin K, ((bandMass x (a i))⁻¹ : ℝ)) : ℂ) *
              (eta ((tupleProduct t : ℕ) / Y) : ℂ) *
              ∑ m ∈ familyTerms family x,
                ∑ n ∈ dyadicIntegers (family.Hn x),
                  if m * n - 1 = tupleProduct t * h then
                    family.alpha x m * beta n else 0
          else 0
    else 0

/-- The Cauchy square `Q_Y` in `det:cauchy-square`, with its real value obtained by taking real
parts of the symmetric expanded sum. -/
noncomputable def cauchySquare (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) : ℝ :=
  ∑' ta : Fin K → ℕ, ∑' tb : Fin K → ℕ,
    if IsMarkedPrimeTuple x K a ta ∧ IsMarkedPrimeTuple x K a tb then
      (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 *
        (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
          ∑ r ∈ familyTerms family x, ∑ s ∈ dyadicIntegers (family.Hn x),
            if ∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                r * s - 1 = tupleProduct tb * h then
              eta ((tupleProduct ta : ℕ) / Y) *
                eta ((tupleProduct tb : ℕ) / Y) *
                Complex.re (family.alpha x m * star (family.alpha x r) *
                  beta n * star (beta s))
            else 0)
    else 0

/-- The coprime part of `Q_Y`, restricting the two marked products to coprime integers. -/
noncomputable def coprimeCauchySquare (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta : ℝ → ℝ) : ℝ :=
  ∑' ta : Fin K → ℕ, ∑' tb : Fin K → ℕ,
    if IsMarkedPrimeTuple x K a ta ∧ IsMarkedPrimeTuple x K a tb ∧
        Nat.Coprime (tupleProduct ta) (tupleProduct tb) then
      (∏ i : Fin K, (bandMass x (a i))⁻¹) ^ 2 *
        (∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
          ∑ r ∈ familyTerms family x, ∑ s ∈ dyadicIntegers (family.Hn x),
            if ∃ h : ℕ, m * n - 1 = tupleProduct ta * h ∧
                r * s - 1 = tupleProduct tb * h then
              eta ((tupleProduct ta : ℕ) / Y) *
                eta ((tupleProduct tb : ℕ) / Y) *
                Complex.re (family.alpha x m * star (family.alpha x r) *
                  beta n * star (beta s))
            else 0)
    else 0

/-- `def:pd-physical` — the major-arc set on the real circle, written using its integer lifts. -/
def majorArc (x Y A₀ : ℝ) (theta : ℝ) : Prop :=
  ∃ h : ℤ, ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ Real.rpow (Real.log x) A₀ ∧
    Int.gcd h k = 1 ∧
      ∃ z : ℤ, |theta - (h : ℝ) / k - z| ≤
        2 * Real.rpow (Real.log x) A₀ / Y

/-- `def:pd-physical` — the smoothed major-arc kernel `ℋ_𝔐(t;a,b)`. -/
noncomputable def majorKernel (x Y A₀ t : ℝ) (a b : ℕ) (psi : ℝ → ℝ) : ℂ :=
  (psi (t / Y) : ℂ) *
    ∫ theta in (0 : ℝ)..1,
      if majorArc x Y A₀ theta then
        additiveCharacter (theta * (t - (b : ℝ) + (a : ℝ))) else 0

/-- `def:pd-physical` — PD `05-major-arcs.tex:11-20`, the unrestricted major-arc sum
`maj:sum`. -/
noncomputable def majorArcSum (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (Y A₀ : ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) (eta psi : ℝ → ℝ) : ℂ :=
  ∑' ta : Fin K → ℕ, ∑' tb : Fin K → ℕ,
    if IsMarkedPrimeTuple x K a ta ∧ IsMarkedPrimeTuple x K a tb then
      ((∏ i : Fin K, ((bandMass x (a i))⁻¹ : ℝ)) : ℂ) ^ 2 *
        ∑ m ∈ familyTerms family x, ∑ n ∈ dyadicIntegers (family.Hn x),
          ∑ r ∈ familyTerms family x, ∑ s ∈ dyadicIntegers (family.Hn x),
            let aa := tupleProduct ta
            let bb := tupleProduct tb
            (eta ((aa : ℝ) / Y) : ℂ) * (eta ((bb : ℝ) / Y) : ℂ) *
              family.alpha x m * star (family.alpha x r) * beta n * star (beta s) *
                majorKernel x Y A₀
                  ((bb : ℝ) * m * n - (aa : ℝ) * r * s) aa bb psi
    else 0

/-- `def:pd-physical` — the pad dyads for auxiliary products with `J` primes per group. -/
noncomputable def padScales (x : ℝ) (K : ℕ) : Finset ℕ :=
  ((Finset.range (⌊((K + 1 : ℕ) : ℝ) *
      Real.rpow (Real.log x) (21 / 100 : ℝ)⌋₊ + 1)).image (fun k => 2 ^ k))

/-- `def:pd-physical` — PD `03-determinant.tex:153-268`. A physical position includes a primitive lattice vector and one ordered list of `M_J`
distinct marked primes in each group, all dividing its first coordinate. -/
structure PhysicalState (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (H' Hm Hn : ℝ) where
  first : ℕ
  second : ℕ
  completionC : ℤ
  completionD : ℤ
  labels : Fin K → Fin (slotCount x) → ℕ
  primitive : Nat.Coprime first second
  first_lower : H' * Hm ≤ (first : ℝ)
  first_upper : (first : ℝ) ≤ 16 * H' * Hm
  second_lower : Hn ≤ (second : ℝ)
  second_upper : (second : ℝ) ≤ 2 * Hn
  det_one : (first : ℤ) * completionD - (second : ℤ) * completionC = 1
  completion_range : 0 ≤ completionC ∧ completionC < first
  label_prime : ∀ i j, (labels i j).Prime
  label_in_band : ∀ i j, labels i j ∈ primeBand x (a i)
  label_divides : ∀ i j, labels i j ∣ first
  label_distinct : ∀ i j j', j ≠ j' → labels i j ≠ labels i j'

/-- The product of all marked labels in a physical state's first coordinate. -/
noncomputable def groupLabelProduct {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn) : ℕ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount x), P.labels i j

/-- The counting measure on physical states, normalized by `∏_i V_i^{-M_J}`. -/
noncomputable def physicalMeasure (x : ℝ) (K : ℕ) (a : Fin K → ℝ) : ℝ :=
  ∏ i : Fin K, Real.rpow (bandMass x (a i)) (-(slotCount x : ℝ))

/-- Weighted Hilbert norm on functions of physical states. -/
noncomputable def physicalNormSq (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {Hm Hn H' : ℝ} (f : PhysicalState x K a H' Hm Hn → ℂ) : ℝ :=
  physicalMeasure x K a * ∑' P : PhysicalState x K a H' Hm Hn, ‖f P‖ ^ 2

/-- Supremum norm on physical-state functions. -/
noncomputable def physicalSupNorm (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {Hm Hn H' : ℝ} (f : PhysicalState x K a H' Hm Hn → ℂ) : ℝ :=
  sSup (Set.range fun P : PhysicalState x K a H' Hm Hn => ‖f P‖)

/-- Pointwise endpoint vectors from PD `03-determinant.tex:313-318`. -/
noncomputable def endpointF (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) {Hm Hn H' : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : ℂ :=
  let G := groupLabelProduct P
  if Squarefree G then
    family.alpha x (P.first / G) * star (beta P.second)
  else 0

/-- Pointwise endpoint vector `g` from PD `03-determinant.tex:313-318`. -/
noncomputable def endpointG (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (beta : ℕ → ℂ) {Hm Hn H' : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : ℂ :=
  let G := groupLabelProduct P
  if Squarefree G then
    star (family.alpha x (P.first / G)) * beta P.second
  else 0

/-- Endpoint vector `f` as a function on the physical state space. -/
noncomputable def endpointFVector (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (H' Hm Hn : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    PhysicalState x K a H' Hm Hn → ℂ :=
  fun P => endpointF x K a family beta P

/-- Endpoint vector `g` as a function on the physical state space. -/
noncomputable def endpointGVector (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (H' Hm Hn : ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    PhysicalState x K a H' Hm Hn → ℂ :=
  fun P => endpointG x K a family beta P

/-- Euclidean inner product and norm used in the finite-dimensional endpoint estimate. -/
noncomputable def vectorInner {n : ℕ} (f g : Fin n → ℂ) : ℂ :=
  ∑ i : Fin n, f i * star (g i)

noncomputable def vectorNorm {n : ℕ} (f : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ‖f i‖ ^ 2)

/-- The root parameter of a physical state. -/
noncomputable def stateRoot {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : ℝ :=
  (P.completionC : ℝ) / P.first

/-- `lem:root-residue` — the size of `SL₂(ℤ/Sℤ)`. -/
noncomputable def sl2Card (S : ℕ) (hS : 0 < S) : ℕ := by
  letI : NeZero S := ⟨Nat.ne_of_gt hS⟩
  exact Fintype.card {g : Matrix (Fin 2) (Fin 2) (ZMod S) // Matrix.det g = 1}

/-- Primitive lattice roots counted in a box and a residue class, as in
`lem:root-residue`. -/
noncomputable def rootResidueCount (U V : ℝ) (modulus : ℕ)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod modulus))
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) : ℝ :=
  Set.ncard {uv : ℕ × ℕ |
    Nat.Coprime uv.1 uv.2 ∧ l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
      ∃ c d : ℤ, (uv.1 : ℤ) * d - (uv.2 : ℤ) * c = 1 ∧
        0 ≤ c ∧ c < uv.1 ∧ l₃ ≤ (c : ℝ) / uv.1 ∧ (c : ℝ) / uv.1 ≤ r₃ ∧
        g₀ 0 0 = (uv.1 : ZMod modulus) ∧ g₀ 0 1 = (c : ZMod modulus) ∧
          g₀ 1 0 = (uv.2 : ZMod modulus) ∧ g₀ 1 1 = (d : ZMod modulus)}

end ArtinPrimitiveRoots.TypeII.PD
