import ArtinPrimitiveRoots.TypeII.Proofs.pd5.HistoryPartition
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Ranks
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Atoms
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.HistoryPhases
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.FiniteChoices

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Chronological code on the finite address set. The last radix exceeds every newLog index. -/
def pd5_birthIndex {K : ℕ} (S : PDScale) (B : ℕ) : BirthAddress K → ℕ
  | .initial i k => i.val * (max (slotCount S.x) B + 1) + k
  | .ghost j i k => ((2 * j + 1) * K + i.val) * (max (slotCount S.x) B + 1) + k
  | .edge j i => ((2 * j + 2) * K + i.val) * (max (slotCount S.x) B + 1)

/-- All possible births of one ghost visit, with the actual cutoff bound on batch indices. -/
def pd5_ghostAddresses (K j B : ℕ) : Finset (BirthAddress K) :=
  (Finset.univ ×ˢ Finset.range B).image fun p => .ghost j p.1 p.2

/-- All possible births of one edge. Promotions are deliberately absent from its actual log. -/
def pd5_edgeAddresses (K j : ℕ) : Finset (BirthAddress K) :=
  Finset.univ.image fun i => .edge j i

/-- Initial birth addresses. -/
def pd5_initialAddresses (x : ℝ) (K : ℕ) : Finset (BirthAddress K) :=
  (Finset.univ ×ˢ Finset.range (slotCount x)).image fun p => .initial p.1 p.2

/-- Local performed-birth flags and triangular instructions. A forced value reads only the
strict chronological pastLog; absent required coordinates give zero. -/
def pd5_prescribedWeight {K : ℕ} (S : PDScale) (B : ℕ)
    (U R : Finset (BirthAddress K)) (pick : BirthAddress K → BirthLog K → ℕ)
    (pastLog newLog : BirthLog K) : ℝ :=
  if ∀ a ∈ U, ∃ p, pd5b_label newLog a = some p ∧
      (a ∈ R → p = pick a ((pastLog ++ newLog).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) then 1 else 0

/-- Real active-slot average, normalized exactly as `logSym`. -/
def pd5_activeAverage {K : ℕ} (S : PDScale) (f : MemPoint S.x K → ℝ)
    (s : MemPoint S.x K) : ℝ :=
  (permCount S.x K : ℝ)⁻¹ * ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
    f (s.1, permuteLists σ s.2.1, s.2.2)

/-- Finite positive ghost choice sum with both cutoff guards. No signed kernel is collected. -/
def pd5_ghostAbsChoice {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j B : ℕ)
    (W : BirthLog K → ℝ) (f : MemPoint S.x K → ℝ) (s : MemPoint S.x K) : ℝ :=
  if memSize s ≤ B then
    ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
      ∑ l : Fin K → Fin (B + 1),
        ∑ new : (i : Fin K) → Fin (l i).val → primeBand S.x (F.a i),
          let t : MemPoint S.x K := (s.1, s.2.1, fun i =>
            removeIndices (s.2.2 i) (D i) ++ List.ofFn fun k => anchorAt (new i k) s.1)
          if (∀ i, D i ⊆ hitIndices (s.2.2 i) s.1) ∧ memSize t ≤ B then
            |∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
                (D i).card (l i).val (List.ofFn fun k => (new i k : ℕ))| *
              W (pd5_ghostBirthLog j (fun i => (l i).val) (fun i k => (new i k : ℕ))) * f t
          else 0
  else 0

/-- Finite raw-plus-comparison edge choice sum, including both active probability averages.
`Z` must contain the box in statements using this definition. -/
def pd5_edgeAbsChoice {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j B : ℕ) (Z : Finset (ℤ × ℤ)) (W : BirthLog K → ℝ)
    (f : MemPoint S.x K → ℝ) (s : MemPoint S.x K) : ℝ :=
  if memSize s ≤ B then pd5_activeAverage S (fun r =>
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (r.2.2 i) i,
      ∑ z' ∈ Z,
        let t : MemPoint S.x K := (z', edgeTargetLists F S r c, edgeNewMemory F S r c)
        if EdgeAdmissible F S w r c z' ∧ memSize t ≤ B then
          |ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
            (∏ i : Fin K, pd5_edgeChoiceMass F S r c i) *
              ρ ^ (∑ i : Fin K, hitCount (t.2.2 i) z')| *
            (‖edgeMultiplier F S (decide (j % 2 = 0)) true r.2.1 t.2.1 r.1 z'‖ +
              ‖edgeMultiplier F S (decide (j % 2 = 0)) false r.2.1 t.2.1 r.1 z'‖) *
            W (edgeBirths F S j r c) * pd5_activeAverage S f t
        else 0) s else 0

/-- The cutoff plain ghost with a multiplier depending on its fresh newLog log. -/
def pd5_ghostBirthTwist {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ) : MemPoint S.x K → ℂ :=
  fun s => logGhost F S ρ j (fun tL => W tL.2 * f tL.1) (s, [])

/-- The plain full edge with a multiplier depending on its fresh newLog log. -/
def pd5_edgeBirthTwist {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (j : ℕ) (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ) : MemPoint S.x K → ℂ :=
  fun s => logEdge F S ρ w .full j (fun tL => W tL.2 * f tL.1) (s, [])

/-- Plain cutoff, used on each side of every operation. -/
def pd5_plainTrunc {x : ℝ} {K : ℕ} (B : ℕ) (f : MemPoint x K → ℂ) : MemPoint x K → ℂ :=
  fun s => if memSize s ≤ B then f s else 0

/-- The finite invariant state region. Initial position is included explicitly. -/
def pd5_stateRegion {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (B : ℕ)
    (s : MemPoint S.x K) : Prop :=
  MemValid F S s ∧ memSize s ≤ B ∧ (s.1 = (1, 0) ∨ envBox S w s.1)

/-- Quantitative positive choice rows, uniform in all pastLog instructions and roots. -/
def PD5PositiveRows {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ v Cghost Cedge cmax aAtom x₀ : ℝ) : Prop :=
  ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
    let B := memoryCutoff S
    let Δ := aAtom * Real.exp (-Real.rpow S.L (1 / 10 : ℝ))
    ∀ s : MemPoint S.x K, pd5_stateRegion F S w B s →
      (∀ j : ℕ, j ≤ S.N → ∀ U R : Finset (BirthAddress K),
        R ⊆ U → U ⊆ pd5_ghostAddresses K j B →
        ∀ pick : BirthAddress K → BirthLog K → ℕ, ∀ pastLog : BirthLog K,
          pd5_ghostAbsChoice F S ρ j B (pd5_prescribedWeight S B U R pick pastLog)
            (fun t => v ^ memSize t) s ≤ Cghost * (cmax * Δ) ^ R.card * v ^ memSize s) ∧
      (∀ j : ℕ, j < S.N → ∀ U R : Finset (BirthAddress K),
        R ⊆ U → U ⊆ pd5_edgeAddresses K j →
        ∀ pick : BirthAddress K → BirthLog K → ℕ, ∀ pastLog : BirthLog K,
        ∀ Z : Finset (ℤ × ℤ), (∀ z, envBox S w z → z ∈ Z) →
          pd5_edgeAbsChoice F S ρ w j B Z (pd5_prescribedWeight S B U R pick pastLog)
            (fun t => v ^ memSize t) s ≤
              Cedge * ((B + 1 : ℕ) : ℝ) ^ K * Real.rpow S.L (3 * F.A₀) *
                Δ ^ R.card * v ^ memSize s)

/-- Fixed-data availability of the rows. Constants precede the moving scale and all choices. -/
def PD5PositiveRowsAvailable {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ) : Prop :=
  ∃ v Cghost Cedge cmax aAtom x₀ : ℝ,
    1 < v ∧ 0 < Cghost ∧ 0 < Cedge ∧ 1 ≤ cmax ∧ 0 < aAtom ∧ 2 ≤ x₀ ∧
      PD5PositiveRows δ c₁ c₂ F ρ v Cghost Cedge cmax aAtom x₀

end
end ArtinPrimitiveRoots.TypeII.PD
