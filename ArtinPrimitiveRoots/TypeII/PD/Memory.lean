import ArtinPrimitiveRoots.TypeII.PD.Defs

/-! Memory-space data and theorem interfaces from PD `04-memory.tex:43-1117`. -/

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII

/-- `def:pd-memory` — PD `04-memory.tex:43-274`; baseline damping sequence `q_j`. -/
noncomputable def memoryQ (x q_d : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = pathLength x then Real.sqrt q_d else q_d

/-- `def:pd-memory` — `η'_j=1-q_j`. -/
noncomputable def memoryEta (x q_d : ℝ) (j : ℕ) : ℝ :=
  1 - memoryQ x q_d j

/-- `def:pd-memory` — the prime factor `b'_p` from `mem:baseline`. -/
noncomputable def memoryBPrime (x q_d : ℝ) (p : ℕ) : ℝ :=
  1 - ∑ j ∈ Finset.range (pathLength x + 1),
    memoryEta x q_d j / ((p : ℝ) + 1)

/-- `def:pd-memory` — the memory measure of a particle in group `i`. -/
noncomputable def memoryNu (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) (i : Fin K) (p : ℕ) : ℝ :=
  1 / (bandMass x (a i) * ((p : ℝ) + 1) * memoryBPrime x q_d p)

/-- `def:pd-memory` — PD `04-memory.tex:122-157`. A particle is a marked prime together with one of the `p+1` lines in `ℙ¹(𝔽_p)`,
represented by a finite set of size `p+1`. -/
structure MemoryParticle (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (i : Fin K) where
  prime : ℕ
  line : Fin (prime + 1)
  prime_mem : prime ∈ primeBand x (a i)

/-- `def:pd-memory` — the memory configuration, an unordered particle multiset in each group. -/
abbrev MemoryConfiguration (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :=
  ∀ i : Fin K, Multiset (MemoryParticle x K a i)

/-- Total number of stored particles. -/
noncomputable def memorySize {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (S : MemoryConfiguration x K a) : ℕ :=
  ∑ i : Fin K, (S i).card

/-- `def:pd-memory` — weight of a memory configuration under the product measure `ν_i(p)`. -/
noncomputable def memoryMeasure (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) (S : MemoryConfiguration x K a) : ℝ :=
  ∏ i : Fin K,
    ((S i).map fun particle => memoryNu x K a q_d i particle.prime).prod

/-- `def:pd-memory` — PD `04-memory.tex:196-232`. Finite-dimensional operator package for the memory proof. The matrices are the ghost
operations, edge operations, their truncations, and the boundary/history data associated with the
physical construction. -/
structure MemoryModel (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (q_d : ℝ) where
  dimension : ℕ
  ghost : Fin (pathLength x + 1) → Matrix (Fin dimension) (Fin dimension) ℂ
  edge : Fin (pathLength x) → Matrix (Fin dimension) (Fin dimension) ℂ
  ghostAdjoint : Fin (pathLength x + 1) → Matrix (Fin dimension) (Fin dimension) ℂ
  edgeAdjoint : Fin (pathLength x) → Matrix (Fin dimension) (Fin dimension) ℂ
  cutoff : ℕ → Matrix (Fin dimension) (Fin dimension) ℂ
  boundary : Fin dimension → ℂ
  pathVector : Fin dimension → Fin dimension → ℂ
  independentLineExpansion : ℂ
  sizeIndex : Fin dimension → ℕ
  goodState : Fin dimension → Prop
  targetVectors : Fin (pathLength x) → Fin dimension → Finset (ℤ × ℤ)
  edgeClean : Fin (pathLength x) → Matrix (Fin dimension) (Fin dimension) ℂ
  edgeDirtyRaw : Fin (pathLength x) → Matrix (Fin dimension) (Fin dimension) ℂ
  edgeComparison : Fin (pathLength x) → Matrix (Fin dimension) (Fin dimension) ℂ

/-- The ordered ghost-edge history matrix `𝒢₀ℰ₀𝒢₁⋯ℰ_{N_R−1}𝒢_{N_R}`. -/
noncomputable def historyOperatorAt {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {q_d : ℝ}
    (M : MemoryModel x K a q_d) (k : Fin (2 * pathLength x + 1)) :
    Matrix (Fin M.dimension) (Fin M.dimension) ℂ :=
  if hEven : k.val % 2 = 0 then
    M.ghost ⟨k.val / 2, by omega⟩
  else
    have hmod : k.val % 2 = 1 := by omega
    have hneq : k.val ≠ 2 * pathLength x := by
      intro heq
      simp [heq] at hmod
    have hlt : k.val < 2 * pathLength x := by omega
    have hlt' : k.val < pathLength x * 2 := by simpa [Nat.mul_comm] using hlt
    M.edge ⟨k.val / 2,
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 hlt'⟩

noncomputable def historyMatrix {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {q_d : ℝ}
    (M : MemoryModel x K a q_d) : Matrix (Fin M.dimension) (Fin M.dimension) ℂ :=
  (List.ofFn (historyOperatorAt M)).foldl (fun A B => A * B) 1

/-- The boundary pairing of the history matrix. -/
noncomputable def historyValue {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {q_d : ℝ}
    (M : MemoryModel x K a q_d) : ℂ :=
  vectorInner M.boundary (Matrix.mulVec (historyMatrix M) M.boundary)

/-- Trace moment of the path vectors for the history operator. -/
noncomputable def memoryMoment {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {q_d : ℝ}
    (M : MemoryModel x K a q_d) (R : ℕ) : ℝ :=
  ∑ i : Fin M.dimension,
    Complex.re (vectorInner (M.pathVector i)
      (Matrix.mulVec ((historyMatrix M * Matrix.conjTranspose (historyMatrix M)) ^ R)
        (M.pathVector i)))

/-- The cutoff `Π_B` inserted around each operation. -/
noncomputable def truncatedHistoryMatrix {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {q_d : ℝ}
    (M : MemoryModel x K a q_d) (B : ℕ) : Matrix (Fin M.dimension) (Fin M.dimension) ℂ :=
  (List.ofFn (historyOperatorAt M)).foldl
    (fun A op => A * M.cutoff B * op * M.cutoff B) 1

/-- The induced operator norm on the finite memory vector space. -/
noncomputable def matrixOperatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin n → ℂ,
    vectorNorm v = 1 ∧ r = vectorNorm (Matrix.mulVec A v)}

/-- Schur row sum with the memory weight `v₀^{k_tot}`. -/
noncomputable def schurRowSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (size : Fin n → ℕ) (v₀ : ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ‖A i j‖ * Real.rpow v₀ (size j) /
    Real.rpow v₀ (size i)

/-- Schur column sum with the memory weight `v₀^{k_tot}`. -/
noncomputable def schurColumnSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (size : Fin n → ℕ) (v₀ : ℝ) (j : Fin n) : ℝ :=
  ∑ i : Fin n, ‖A i j‖ * Real.rpow v₀ (size i) /
    Real.rpow v₀ (size j)

/-- Primewise denominator `b'_p` product in `mem:prime-factor`. -/
noncomputable def memoryNormalization (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) : ℝ :=
  ∏ p ∈ markedPrimes x K a, memoryBPrime x q_d p

end ArtinPrimitiveRoots.TypeII.PD
