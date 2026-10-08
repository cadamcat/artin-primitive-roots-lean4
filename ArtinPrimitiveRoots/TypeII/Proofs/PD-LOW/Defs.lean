import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs
import ArtinPrimitiveRoots.TypeII.Proofs.pd5b.LocalPhases

set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Per-address performed phase; missing required births contribute zero. -/
def pd5_addressPhase {K : ℕ} (φ : BirthAddress K → ℕ → ℂ)
    (log : BirthLog K) (a : BirthAddress K) : ℂ :=
  match pd5b_label log a with
  | none => 0
  | some p => φ a p

/-- A product of performed phases on a fixed finite support of addresses. -/
def pd5_birthPhaseWeight {K : ℕ} (U : Finset (BirthAddress K))
    (φ : BirthAddress K → ℕ → ℂ) (log : BirthLog K) : ℂ :=
  ∏ a ∈ U, pd5_addressPhase φ log a

/-- Local phase restricted to the possible addresses of an operation. -/
def pd5_operationPhase {K : ℕ} (U Ops : Finset (BirthAddress K))
    (φ : BirthAddress K → ℕ → ℂ) (log : BirthLog K) : ℂ :=
  pd5_birthPhaseWeight (U ∩ Ops) φ log

/-- Plain history after phases have been attached to their birth operations. -/
def pd5_phaseHistoryFn {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : ℕ) (U : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ) :
    ℕ → MemPoint S.x K → ℂ
  | 0 => pd5_plainTrunc B (pd5_ghostBirthTwist F S ρ S.N
      (pd5_operationPhase U (pd5_ghostAddresses K S.N B) φ) (pd5_plainTrunc B memBoundary))
  | k + 1 =>
      let j := S.N - (k + 1)
      pd5_plainTrunc B (pd5_ghostBirthTwist F S ρ j
        (pd5_operationPhase U (pd5_ghostAddresses K j B) φ) (pd5_plainTrunc B
          (pd5_edgeBirthTwist F S ρ w j (pd5_operationPhase U (pd5_edgeAddresses K j) φ)
            (pd5_plainTrunc B (pd5_phaseHistoryFn F S ρ w B U φ k)))))

/-- The weighted plain pairing. Its initial multiplier has the orientation of the original
logged pairing; the corresponding input vector is its conjugate times `memBoundary`. -/
def pd5_phaseHistory {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : ℕ) (U : Finset (BirthAddress K)) (φ : BirthAddress K → ℕ → ℂ) : ℂ :=
  ∑' s : MemPoint S.x K, (memMeasure F S s : ℂ) * star (memBoundary s) *
    pd5_operationPhase U (pd5_initialAddresses S.x K) φ (initialLog s) *
      pd5_phaseHistoryFn F S ρ w B U φ S.N s

/-- The repaired upstream ghost Schur bounds, passed explicitly to avoid an import cycle
with MemoryResults, where the frozen ghost_edge_crude declaration lives. -/
def PD5GhostCrudeAvailable {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ) : Prop :=
  ∃ v C_K x₀ : ℝ, 1 < v ∧ 0 < C_K ∧ 2 ≤ x₀ ∧
    ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
      ∀ j : ℕ, j ≤ S.N →
        MemRowSchurLE_sym F S (memoryCutoff S) (memGhost F S ρ j) v C_K ∧
        MemColSchurLE_sym F S (memoryCutoff S) (memGhost F S ρ j) v C_K

/-- Birth-twisted operation bounds and preservation needed by low-rank norm iteration. -/
def PD5ModifiedBounds {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ C_K Ccr x₀ : ℝ) : Prop :=
  ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
    ∀ W : BirthLog K → ℂ, (∀ log, ‖W log‖ ≤ 1) →
      (∀ j : ℕ, j ≤ S.N →
        MemOpNormLE_sym F S (memoryCutoff S) (pd5_ghostBirthTwist F S ρ j W) C_K ∧
        ∀ f : MemPoint S.x K → ℂ, IsMemorySymmetric f →
          IsMemorySymmetric (pd5_ghostBirthTwist F S ρ j W f)) ∧
      (∀ j : ℕ, j < S.N →
        MemOpNormLE_sym F S (memoryCutoff S) (pd5_edgeBirthTwist F S ρ w j W)
          (Real.rpow S.L Ccr) ∧
        ∀ f : MemPoint S.x K → ℂ, IsMemorySymmetric f →
          IsMemorySymmetric (pd5_edgeBirthTwist F S ρ w j W f))

/-- Availability of modified bounds, with the threshold independent of the signed exponent. -/
def PD5ModifiedBoundsAvailable {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) (ρ : ℝ) : Prop :=
  ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
    PD5ModifiedBounds δ c₁ c₂ F ρ C_K Ccr x₀

/-- The boundary and measure estimates supplied before choosing the signed exponent. -/
def PD5BoundaryAvailable {K : ℕ} (δ c₁ c₂ : ℝ) (F : PDFix K) : Prop :=
  ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
    (∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s) ∧
      ∀ T : Finset (MemPoint S.x K), memNormSqOn F S T memBoundary ≤ 2

end
end ArtinPrimitiveRoots.TypeII.PD
