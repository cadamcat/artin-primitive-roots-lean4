import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Visits at which a numeric prime occurs in the external active lists. -/
def pdLifeActive {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) :
    Finset (Fin (pathLength S.x + 1)) := Finset.univ.filter (IsActiveAt γ p)

/-- The number of maximal active runs; starts are indexed, including visit zero. -/
def pdActiveRuns {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin (pathLength S.x + 1) =>
    IsActiveAt γ p j ∧ ¬ ∃ k : Fin (pathLength S.x + 1),
      k.val + 1 = j.val ∧ IsActiveAt γ p k).card

/-- Optional ghost birth and deletion endpoints. Active lifespans have optional extensions;
inactive lifespans are empty or have two strictly ordered, matching endpoints. -/
def pdLifeEndpointValid {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) : Prop :=
  let A := pdLifeActive S γ p
  if hA : A.Nonempty then
    let α := A.min' hA
    let ω := A.max' hA
    (∀ j ∈ A, projLine p (γ j).1 = projLine p (γ α).1) ∧
      (match e.1 with
       | none => True
       | some a => a < α ∧ projLine p (γ a).1 = projLine p (γ α).1) ∧
      (match e.2 with
       | none => True
       | some c => ω < c ∧ projLine p (γ c).1 = projLine p (γ α).1)
  else match e with
    | (none, none) => True
    | (some a, some c) => a < c ∧ projLine p (γ c).1 = projLine p (γ a).1
    | _ => False

def pdLifeEndpoints {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) :=
  Finset.univ.filter (pdLifeEndpointValid S γ p)

/-- Finite, valid endpoint alternatives; inconsistent active anchors give an empty type. -/
abbrev PrimeLife {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) :=
  {e // e ∈ pdLifeEndpoints S γ p}

/-- Literal survival factor at a hit, with the two neighboring edge factors. -/
def pdRawSurvival {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (p : ℕ) (lam : Fin (p + 1))
    (j : Fin (pathLength S.x + 1)) : ℝ :=
  if projLine p (γ j).1 = lam then
    ρ * (memoryQ S.x F.q_d j.val / ρ ^ 2) * ρ else 1

/-- Survival after rho cancellation. -/
def pdLifeSurvival {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (lam : Fin (p + 1))
    (j : Fin (pathLength S.x + 1)) : ℝ :=
  1 - memoryEta S.x F.q_d j.val * (if projLine p (γ j).1 = lam then 1 else 0)

/-- Signed prime lifespan charge, before the active V normalizations. -/
def primeLifeCharge {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (life : PrimeLife S γ p) : ℝ :=
  let A := pdLifeActive S γ p
  let d := (((p : ℝ) + 1) * memoryBPrime S.x F.q_d p)⁻¹
  if hA : A.Nonempty then
    let α := A.min' hA
    let ω := A.max' hA
    let lam := projLine p (γ α).1
    d * (match life.1.1 with
      | none => 1
      | some a => -memoryEta S.x F.q_d a.val *
          ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < α),
            pdLifeSurvival F S γ p lam j) *
      (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < ω ∧ j ∉ A),
        pdLifeSurvival F S γ p lam j) *
      (match life.1.2 with
       | none => 1
       | some c => -memoryEta S.x F.q_d c.val *
           ∏ j ∈ Finset.univ.filter (fun j => ω < j ∧ j < c),
             pdLifeSurvival F S γ p lam j)
  else match life.1 with
    | (none, none) => 1
    | (some a, some c) => d * memoryEta S.x F.q_d a.val * memoryEta S.x F.q_d c.val *
        ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
          pdLifeSurvival F S γ p (projLine p (γ a).1) j
    | _ => 0

/-- Literal scalar contribution of a lifespan after cancelling its batch factorial by
the ordered-batch count. Initial/fresh active births pay nu; subsequent entries pay V inverse.
Ghost births and deletions retain their rho denominators and adjoining edge factors. -/
def pdRawPrimeLifeCharge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (life : PrimeLife S γ p) : ℝ :=
  let A := pdLifeActive S γ p
  let V := bandMass S.x (F.a i)
  let ν := memoryNu S.x K F.a F.q_d i p
  let r := pdActiveRuns S γ p
  if hA : A.Nonempty then
    let α := A.min' hA
    let ω := A.max' hA
    let lam := projLine p (γ α).1
    (match life.1.1 with
     | none => ν * (V⁻¹) ^ (r - 1)
     | some a => (-memoryEta S.x F.q_d a.val * V / ρ) * ρ * ν * (V⁻¹) ^ r *
         ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < α),
           pdRawSurvival F S ρ γ p lam j) *
      (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < ω ∧ j ∉ A),
        pdRawSurvival F S ρ γ p lam j) *
      (match life.1.2 with
       | none => 1
       | some c => (-memoryEta S.x F.q_d c.val / ρ) * ρ *
           ∏ j ∈ Finset.univ.filter (fun j => ω < j ∧ j < c),
             pdRawSurvival F S ρ γ p lam j)
  else match life.1 with
    | (none, none) => 1
    | (some a, some c) =>
        (-memoryEta S.x F.q_d a.val * V / ρ) * ρ * ν *
          ((-memoryEta S.x F.q_d c.val / ρ) * ρ) *
          ∏ j ∈ Finset.univ.filter (fun j => a < j ∧ j < c),
            pdRawSurvival F S ρ γ p (projLine p (γ a).1) j
    | _ => 0

/-- COPY of the frozen lifespanSum body, to keep the new files below MemoryResults in the
dependency graph. The consumer bridges this expression by definitional equality. -/
def pdLifespanFormula (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1))
    (act : Fin (N + 1) → Prop) (eta : Fin (N + 1) → ℝ) (bp : ℝ) : ℝ :=
  let A : Finset (Fin (N + 1)) := Finset.univ.filter act
  let hit (j : Fin (N + 1)) (l : Fin (p + 1)) : ℝ := if lam j = l then 1 else 0
  if hA : A.Nonempty then
    let α := A.min' hA
    let ω := A.max' hA
    let ls := lam α
    if ∀ j ∈ A, lam j = ls then
      (((p : ℝ) + 1) * bp)⁻¹ *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => h < α),
          eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => h < j ∧ j < α),
            (1 - eta j * hit j ls)) *
        (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < ω ∧ j ∉ A),
          (1 - eta j * hit j ls)) *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => ω < h),
          eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => ω < j ∧ j < h),
            (1 - eta j * hit j ls))
    else 0
  else
    1 + (((p : ℝ) + 1) * bp)⁻¹ *
      ∑ ac ∈ Finset.univ.filter (fun ac : Fin (N + 1) × Fin (N + 1) => ac.1 < ac.2),
        eta ac.1 * eta ac.2 * hit ac.2 (lam ac.1) *
          ∏ j ∈ Finset.univ.filter (fun j => ac.1 < j ∧ j < ac.2),
            (1 - eta j * hit j (lam ac.1))

def pdPathLifespan {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) : ℝ :=
  pdLifespanFormula p (pathLength S.x) (fun j => projLine p (γ j).1) (IsActiveAt γ p)
    (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p)

/-- A finite lifespan assignment over the band primes, retaining their group. -/
abbrev PDLifeAssignment {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :=
  (i : Fin K) → (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1

def pdLifeAssignmentCharge {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) : ℝ := ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), primeLifeCharge F S γ p.1 (H i p)

def pdRawAssignmentCharge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ) : ℝ :=
  ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), pdRawPrimeLifeCharge F S ρ γ i p.1 (H i p)

def pdActiveNormalization {K : ℕ} (F : PDFix K) (S : PDScale) : ℝ :=
  physicalMeasure S.x K F.a * (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) ^ pathLength S.x

/-- Pending status before/after the ghost. Before includes its deletion endpoint; after
includes its birth endpoint. Active visits carry no pending particle. -/
def pdLifePending {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (life : PrimeLife S γ p) (afterGhost : Bool) (j : Fin (pathLength S.x + 1)) : Prop :=
  let A := pdLifeActive S γ p
  if hA : A.Nonempty then
    let α := A.min' hA
    let ω := A.max' hA
    ¬ IsActiveAt γ p j ∧
      (if j < α then match life.1.1 with
        | none => False
        | some a => if afterGhost then a ≤ j else a < j
       else if ω < j then match life.1.2 with
        | none => False
        | some c => if afterGhost then j < c else j ≤ c
       else True)
  else match life.1 with
    | (some a, some c) => if afterGhost then a ≤ j ∧ j < c else a < j ∧ j ≤ c
    | _ => False

def pdLifeMemorySize {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (afterGhost : Bool) (j : Fin (pathLength S.x + 1)) : ℕ :=
  ∑ i : Fin K, ∑ p : primeBand S.x (F.a i), if pdLifePending S γ p.1 (H i p) afterGhost j then 1 else 0

def pdLifeMaxMemory {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) : ℕ :=
  Finset.univ.sup fun j => max (pdLifeMemorySize F S γ H false j)
    (pdLifeMemorySize F S γ H true j)

def pdLifeGhostBirths {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) : ℕ :=
  ∑ i : Fin K, ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0

def pdRawHistorySum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (B : Option ℕ) : ℝ :=
  ∑ H : PDLifeAssignment F S γ,
    (match B with
     | none => pdRawAssignmentCharge F S ρ γ H
     | some b => if pdLifeMaxMemory F S γ H ≤ b then pdRawAssignmentCharge F S ρ γ H else 0)

def pdLifeChargeSum {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) : ℝ :=
  ∑ H : PDLifeAssignment F S γ, pdLifeAssignmentCharge F S γ H

/-- One factor of two per ghost-born lifespan, with absolute prime charges. -/
def doubledLifeMajorant {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) : ℝ :=
  ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), ∑ life : PrimeLife S γ p.1,
    (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p.1 life|

end
end ArtinPrimitiveRoots.TypeII.PD
