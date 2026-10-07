import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Partition
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §5 Memory results (PD 04:11-966) -/

/-- The lifespan expansion of one prime (mem:orphan-identity, mem:prefix, mem:suffix,
mem:run-charge before the `V_i` factors), PD 04:82-132.  `lam j = [z_j]_p`, `act j` = active at
visit `j`, `eta j = η'_j`, `bp = b'_p`.  No active visit: `1 +` orphan lifespans; active visits
with a common line `λ*`: one lifespan through `[α,γ] = [min A, max A]` with optional ghost
extensions at both ends; disagreeing active lines: `0`. -/
def lifespanSum (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1)) (act : Fin (N + 1) → Prop)
    (eta : Fin (N + 1) → ℝ) (bp : ℝ) : ℝ :=
  let A : Finset (Fin (N + 1)) := Finset.univ.filter act
  let hit (j : Fin (N + 1)) (l : Fin (p + 1)) : ℝ := if lam j = l then 1 else 0
  if hA : A.Nonempty then
    let α := A.min' hA
    let γ := A.max' hA
    let ls := lam α
    if ∀ j ∈ A, lam j = ls then
      (((p : ℝ) + 1) * bp)⁻¹ *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => h < α),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => h < j ∧ j < α),
              (1 - eta j * hit j ls)) *
        (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < γ ∧ j ∉ A), (1 - eta j * hit j ls)) *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => γ < h),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => γ < j ∧ j < h),
              (1 - eta j * hit j ls))
    else 0
  else
    1 + (((p : ℝ) + 1) * bp)⁻¹ *
      ∑ ac ∈ Finset.univ.filter (fun ac : Fin (N + 1) × Fin (N + 1) => ac.1 < ac.2),
        eta ac.1 * eta ac.2 * hit ac.2 (lam ac.1) *
          ∏ j ∈ Finset.univ.filter (fun j => ac.1 < j ∧ j < ac.2), (1 - eta j * hit j (lam ac.1))

/-- `t2:pd.prime-lifespan` (new node, general) — PD 04:68-115.  The primewise identity:
the independent-line factor of one prime equals `b'_p` times its lifespan expansion.  Proof:
expand the product; singletons give `b'_p`; for larger sets fix first and last index (orphan
case); for active primes only the common line survives and the outer products telescope. -/
theorem prime_lifespan (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1))
    (act : Fin (N + 1) → Prop) (eta : Fin (N + 1) → ℝ) (bp : ℝ)
    (hbp : bp = 1 - ∑ j : Fin (N + 1), eta j / ((p : ℝ) + 1)) (hbp0 : bp ≠ 0) :
    ((p : ℝ) + 1)⁻¹ * ∑ l : Fin (p + 1), ∏ j : Fin (N + 1),
        (if act j then (if lam j = l then (1 : ℝ) else 0)
          else 1 - eta j * (if lam j = l then 1 else 0)) =
      bp * lifespanSum p N lam act eta bp := by
  sorry

/-- The lifespan expansion of a group prime along a line-model path. -/
def pathLifespan {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) : ℝ :=
  lifespanSum p (pathLength S.x) (fun j => projLine p (γ j).1) (IsActiveAt γ p)
    (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p)

/-- `t2:pd.history-paths` (new node) — PD 04:234-246.  Exact decomposition of the distinct
history by the sequence of positions and active lists at the visits (ghosts do not move them;
the edges move along the path; distinct initial entries make every visit list valid). -/
theorem history_paths (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          historyDistinct F S ρ w =
            ∑' γ : EnvPath S.x K,
              if IsEnvPathAdmissible F S γ then memHistory F S ρ w none (some γ) distinctWeight else 0 := by
  sorry

/-- `t2:pd.history-path-value` (new node) — PD 04:234-274.  Along a fixed admissible path the
sum over memory choices with global birth distinctness factorizes over primes into lifespans:
store on leaving a nonfinal active run, promote on entering the next, ghost births/deletions at
the optional ghost endpoints; `ρ·(q_j/ρ²)·ρ = q_j` at pending hits; an active birth has measure
`ν_i(p) = ((p+1)b'_p)⁻¹V_i⁻¹`, a ghost birth `V_iν_i(p)` after cancellation, a promotion `V_i⁻¹`
(mem:run-charge); the symmetrization averages and `V_i⁻¹` weights are those of
`pathCoefficient`. -/
theorem history_path_value (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ →
          memHistory F S ρ w none (some γ) distinctWeight =
            pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
  sorry

/-- `t2:pd.memory-identity` — PD 04:43-274.  For every root of the region: the independent-line average of the
line-model moment equals the baseline `∏_p b'_p` times the distinct history value.  Proof:
`env_path_form`; the line average of a product over primes is the product of the per-prime
averages; `prime_lifespan`; `history_paths`; `history_path_value`. -/
theorem memory_identity (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          lineAverage (envMomentC F S w) =
            (memoryBaseline F S : ℂ) * historyDistinct F S ρ w := by
  sorry

/-- `t2:pd.truncation-adjoint` — PD 04:276-308.  REPLACES the frozen `truncation_adjoint`.
Inserting `Π_B`, `B = ⌈L²⌉`, around every operation changes the distinct history by
`O_A(L^{-AN})`: a history of memory size `> B` has `≥ B - KN` ghost births; with a factor `2` per
ghost birth the absolute ghost-only cost is `exp(O_K(N+1))`, the baseline and the path budget
`exp(O_K(L^{0.74}))`, so the omitted part is `2^{-B+KN} exp(O_K(L^{0.74}))`.  The adjoint rules
(mem:ghost-factorial), (mem:edge-factorial) of PD 04:310-363 are used in `ghost_edge_crude`
(column sums) and are not stated separately. -/
theorem truncation_adjoint (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
            C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  sorry

/-- `t2:pd.ghost-edge-crude` — PD 04:365-435.  REPLACES the frozen `ghost_edge_crude`.  On
`ℋ_B`, with the Schur weight `v₀^{k_tot}`: ghost row and column sums (mem:ghost-row),
(mem:ghost-column) are `≤ C_K` once `v₀` makes both parentheses `≤ 1` (uses `ρ² > √q_d`), so
`‖𝒢_j‖ ≤ C_K` (mem:ghost-norm); edge rows and columns are `≤ C_K B^K (1+L^{3A₀}) ≤ L^{C}`
(mem:edge-crude; columns via the adjoint rules, PD 04:310-348). -/
theorem ghost_edge_crude (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K Cexp x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < Cexp ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j ≤ S.N →
            MemRowSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemColSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemOpNormLE F S (memoryCutoff S) (memGhost F S ρ j) C_K ∧
            (j < S.N →
              MemRowSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp) ∧
              MemColSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp)) := by
  sorry

/-- `t2:pd.lattice-clean` (a) — PD 04:439-497.  Lattice box at a source passing good test (i):
in the coordinates `(h,l)` of `z' = h z + l D w_z`, the region `|l| ≤ C₁ Y`, `|h + lα| ≤ C₁`
(`α = D τ(w_z)/τ(z)`, from cell separation and the box) is covered, after a unimodular change of
coordinates, by a centered box with sides `A', B'`, `A'B' ≪ Y`, `Y^{0.1} ≤ A',B' ≤ Y^{0.9}`
(mem:lattice-shape).  Pure geometry of numbers: shortest vector `≥ Y^{-0.8}` by test (i),
`≪ Y^{-1/2}` by Dirichlet. -/
theorem lattice_shape (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₂ Y₀ : ℝ, 0 < C₂ ∧ 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ α : ℝ,
      (∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
        Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) →
      ∃ (a₀ b₀ c₀ d₀ : ℤ) (A' B' : ℝ), a₀ * d₀ - b₀ * c₀ = 1 ∧ A' * B' ≤ C₂ * Y ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ A' ∧ A' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ B' ∧ B' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y → |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
          |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧ |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
  sorry

/-- `t2:pd.lattice-clean` (b) — PD 04:499-603.  REPLACES the frozen `lattice_clean`.  For every
`G` there is `A₀` with `‖ℰ_j^{clean}‖_{ℋ_B} ≤ L^{-G}` (mem:clean-bound): condition on shared list
and memory, drop the extra ban (cost `C_K M sup ν`), reduce by `lattice_shape` to the
determinant-exponential matrix on the box (mem:clean-kernel), Fourier-diagonalize the product
variable, Dirichlet approximation on `𝕋 ∖ 𝔐` (mem:dirichlet-minor) and the Gram bound
(mem:bilinear-gram) give `L^{0.2-A₀} + Y^{-0.1} log Y`; `A₀` independent of `K`. -/
theorem lattice_clean (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ (K : ℕ) (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.clean j)
                (Real.rpow S.L (-G)) := by
  sorry

/-- `t2:pd.dirty-raw` — PD 04:605-714.  REPLACES the frozen `dirty_raw`.  With
`ε_K = C_K(B/M_J^K + B^K e^{-cL^{0.1}})`: every raw piece with `(St,Pr) ≠ (∅,∅)` has weighted row
sum `≤ ε_K` if `Pr ≠ ∅` (one compatible omission tuple by test (ii), mass `M_J^{-K}`,
(mem:anchor-congruence)) and `≤ C_K` otherwise, column sum `≤ ε_K` if `St ≠ ∅` and `≤ C_K`
otherwise (reversal); weighted Schur gives `‖dirty raw‖ ≤ C_K √ε_K ≤ C_K L^{1-K/200}` for large
`x` (mem:raw-dirty-norm).  Stated for `K ≥ 201`, where `ε_K ≤ 1` eventually. -/
theorem dirty_raw (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ), 201 ≤ K → ∀ (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K c x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < c ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
            let B := memoryCutoff S
            let εK := C_K * ((B : ℝ) / (S.M : ℝ) ^ K +
              (B : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)))
            (∀ St Pr : Finset (Fin K), ¬ (St = ∅ ∧ Pr = ∅) →
              MemRowSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if Pr.Nonempty then εK else C_K) ∧
                MemColSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if St.Nonempty then εK else C_K)) ∧
            MemOpNormLE F S B (memEdge F S ρ w EdgeKind.dirtyRaw j)
              (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := by
  sorry

/-- `t2:pd.dirty-comparison` — PD 04:716-770.  REPLACES the frozen `dirty_comparison`.
Comparison pieces with `(St,Pr) ≠ (∅,∅)`: a promoted index needs one prescribed line at the
target, one nonzero linear congruence in the lattice box (mem:line-count), row sum
`ζ_K = C_K L^{3A₀} B^K (p_min^{-1} + Y^{-0.1}) = O_A(L^{-A})`; the opposite side is `≤ L^C`
(mem:edge-crude); weighted Schur gives every fixed negative power of `L`. -/
theorem dirty_comparison (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
          MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyCmp j)
            (C_A * Real.rpow S.L (-A)) := by
  sorry

/-- `t2:pd.signed-edge` (new assembly node) — PD 04:772-782 (mem:signed-edge).  Choose `A₀`
from `lattice_clean` for `G+1`, then `K₀` with `K₀/200 > G+2`: `‖ℰ_j‖_{ℋ_B} ≤ L^{-G}`
(`ℰ_j = clean + dirtyRaw - dirtyCmp` by definition). -/
theorem signed_edge (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G)) := by
  sorry

/-- `t2:pd.birth-partition` (new node, general) — PD 04:807-823 (mem:partition-identity).  For a
log whose addresses are distinct and lie in `A`, the distinctness weight is the signed sum of the
constraint weights: `Σ_π sgn π` over value-preserving permutations of the performed addresses,
grouped by nontrivial cycles (`(|C|-1)!` cyclic orders of sign `(-1)^{|C|-1}` on each block). -/
theorem birth_partition {K : ℕ} (A : Finset (BirthAddress K)) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) (hA : ∀ e ∈ log, e.1 ∈ A) :
    distinctWeight log =
      ∑ 𝒞 ∈ constraintSystems A, (constraintCoeff 𝒞 : ℂ) * constraintWeight 𝒞 log := by
  exact birth_partition_from_labels A log hnodup hA

/-- `t2:pd.history-rank-high` (new node) — PD 04:825-904.  High-rank constraint systems are
negligible in absolute value: with `r₀ = ⌈C' N log L / L^{0.1}⌉` (`C'` large after the crude
exponent), `Σ_{r(𝒞) ≥ r₀} |coef 𝒞| · |H_𝒞| ≤ L^{-(E₀+3)N}`, where `H_𝒞` is the truncated history
with final weight `constraintWeight 𝒞`.  Proof: coefficient mass `Q_birth^{2r}` (mem:rank-coefficients);
a fixed system costs `L^{C(N+1)} (C_K e^{-L^{0.1}})^r` by chronological conditioning on pivots, an
atom `Δ ≤ C_K e^{-L^{0.1}}` per nonpivot birth (mem:edge-atoms), (mem:ghost-atoms); geometric
series (mem:high-rank). -/
theorem history_rank_high (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ E₀ : ℝ, 0 < E₀ →
      ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          (∑ 𝒞 ∈ (constraintSystems (birthAddresses S.x K (memoryCutoff S))).filter
              (fun 𝒞 => (⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊ ≤
                constraintRank 𝒞)),
            |(constraintCoeff 𝒞 : ℝ)| *
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖) ≤
            Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
  sorry

/-- `t2:pd.history-rank-low` (new node) — PD 04:906-956.  A constraint system of rank `r` changes at
most `2r` operations: write each block indicator by circle orthogonality (mem:local-phases), attach
every phase at the operation where its prime is born (an equivariant multiplier of modulus `≤ 1`);
if every edge satisfies the signed bound `L^{-G}`, then
`|H_𝒞| ≤ C_K^{N+1} ‖𝐛‖² L^{-G(N-2r)} L^{2Cr}` (mem:low-rank-term) with the crude exponent `C` of
`ghost_edge_crude` and `‖𝐛‖² ≤ 2` (mem:boundary-norm). -/
theorem history_rank_low (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
          ∀ G : ℝ, 0 < G →
            (∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G))) →
            ∀ 𝒞 ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖ ≤
                2 * C_K ^ (S.N + 1) *
                  Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank 𝒞 : ℝ))) *
                  Real.rpow S.L (2 * Ccr * (constraintRank 𝒞 : ℝ)) := by
  sorry

/-- `t2:pd.birth-distinctness` — PD 04:784-966.  REPLACES the frozen `birth_distinctness`.
Assembly: the truncated distinct history is `≤ L^{-(E₀+2)N}` uniformly in the root.
`birth_partition` (logs of truncated histories have distinct addresses in `birthAddresses`),
`history_rank_high`, and `history_rank_low` with `signed_edge` for `G > E₀ + 3`; since
`r₀/N = O(log L / L^{0.1})`, the low ranks sum to `L^{(-G+o(1))N}` (mem:low-rank). -/
theorem birth_distinctness (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ)
    (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S →
              ‖historyDistinctTrunc F S ρ w‖ ≤ Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
  sorry

/-! ## §6 Removing goodness, stripping pads, Proposition 4.1 (PD 04:968-1117, 11-35) -/

/-- The scale of a coefficient family at `x` with selected-product scale `Y` and pad `d₀`. -/
def familyScale {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x Y : ℝ) (d₀ : ℕ) :
    PDScale := ⟨x, family.Hm x, family.Hn x, Y, d₀⟩

/-- `β` hypotheses at the family's second dyad. -/
def IsFamilySecondCoefficient {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    (beta : ℕ → ℂ) : Prop :=
  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧ roughAbove n (roughCutoff x)) ∧
    ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C

/-- `t2:pd.goodness-removal` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:970-1008.
Removing both good-state projections from the pairing costs `O_A(UV L^{-A})`: majorize the bad
parts absolutely with log-power endpoint suprema; single-edge root replacement (the general
sub-lemmas `root_lines`, `root_arch_boundary`, `root_bonferroni`); one-edge label mass
(mem:one-edge-label-mass) `≤ 1`; `O(1)` raw / `O(Y)` comparison targets; bad ratios of measure
`e^{-cL^{0.1}}` by `good_state`. -/
theorem goodness_removal (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ family : CoefficientFamily δ C c₁ c₂, FamilyAtScale family S →
          ∀ beta : ℕ → ℂ, IsSecondCoefficient S C beta →
            ‖detPairing F S family beta - detPairingNoGood F S family beta‖ ≤
              C_A * S.U * S.V * Real.rpow S.L (-A) := by
  sorry

/-- `t2:pd.pad-stripping` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:1010-1101.
Summed over pad dyads with weight `1/d₀`, the pairing without goodness is the coprime Cauchy
square minus the unrestricted major sum up to `O_A(XY L^{-A})`: pad measure identity
(mem:pad-measure) (pads are independent ordered harmonic draws, total mass one), raw part =
coprime pairs `(a,b)` (the cross-edge ban), pad collisions (mem:pad-collisions) against the
absolute squares (mem:raw-absolute-square), (mem:comparison-absolute-square), and restoration of
non-disjoint `(a,b)` in the comparison (mem:unshared-collisions). -/
theorem pad_stripping (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ‖(∑ d₀ ∈ padScales x K,
                ((d₀ : ℂ))⁻¹ * detPairingNoGood F (familyScale family x Y d₀) family beta) -
              ((coprimeCauchySquare x K F.a Y family beta F.eta : ℂ) -
                majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi)‖ ≤
              C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:pd.strip-goodness-pads` — PD 04:968-1117.  REPLACES the frozen `strip_goodness_pads`
(which asserted the replacement for every `K` and `A₀` without the pairing hypothesis).  From
pairing bounds at every pad dyad to the replacement of the Cauchy square: `goodness_removal`,
`pad_stripping`, and part (iii) of the frozen `cauchy_decomposition` (`Q_Y` vs `Q_Y^{cop}`);
`UV/d₀ = XY`. -/
theorem strip_goodness_pads (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ∀ E₀ Ce Cp : ℝ,
              (∀ d₀ ∈ padScales x K,
                ‖detPairing F (familyScale family x Y d₀) family beta‖ ≤
                  Cp * (familyScale family x Y d₀).U * (familyScale family x Y d₀).V *
                    Real.rpow (Real.log x) (-E₀ + Ce)) →
              ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                  majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                ((padScales x K).card : ℝ) * Cp * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-E₀ + Ce) +
                  C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `prop:minor-moment` (moment part) — PD 04:11-22, Proposition 4.1.  REPLACES the first
conjunct of the frozen `minor_moment`.  For every `E₀` choose `A₀`, then `K₀` (independent of the
band exponents): the determinant moment is `≤ L^{-E₀N}`.  Proof: `path_expansion`,
`root_replacement` (`A = E₀+1`), `memory_identity`, `truncation_adjoint`, `birth_distinctness`
with `ρ = q_d^{1/8}`, `0 ≤ b'_p ≤ 1`, root region of volume `15`. -/
theorem minor_moment (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          detMoment F S ≤ Real.rpow S.L (-E₀ * (S.N : ℝ)) := by
  sorry

/-- `prop:minor-moment` (replacement part, mem:replacement-interface) — PD 04:22-34.  REPLACES the
second conjunct of the frozen `minor_moment`.  For every `A` choose `E₀ > A + C_e + 3`, then
`A₀, K₀` from `minor_moment`: `|Q_Y - Q_Y^{maj}| ≪_A XY L^{-A}`.  Only the coefficient bounds of
the family enter (no long-coefficient hypothesis).  Proof: `minor_moment`,
`moment_to_pairing`, `strip_goodness_pads`, `#padScales ≪_K L^{0.21}`. -/
theorem minor_replacement (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ ≤ c₂) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ family : CoefficientFamily δ C c₁ c₂,
          ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ, IsFamilySecondCoefficient family x beta →
              ∀ Y ∈ dyadicScales x K,
                ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                    majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                  C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry


end

end ArtinPrimitiveRoots.TypeII.PD
