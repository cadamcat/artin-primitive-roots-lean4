import ArtinPrimitiveRoots.TypeII.PD.RootReplacement
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §4 `def:pd-memory` — the memory model (PD 04:43-274)

The list-based state and operator definitions below replace the abstract skeleton interface.

States: position `z`, ordered active lists (repetitions allowed in the space; distinctness is
imposed by the edges, PD 04:150-155), and per group an ordered list of memory particles
`(p, anchor)`.  Ordered lists with measure `λ^{⊗k}/k!` represent the symmetric spaces of
(mem:hilbert-space); all deletion and promotion choices are choices of indices (PD 04:313-316).
All memory operators are taken at a fixed archimedean root `w` (lines are integrated out). -/

/-- A memory particle `(p, ℓ)`: a group prime and its anchor, the `ℙ¹(𝔽_p)` point encoded as
in `projLine` (so `ℓ ≤ p`). -/
abbrev Particle := ℕ × ℕ

/-- Memory-model states: position, active lists, memory lists. -/
abbrev MemPoint (x : ℝ) (K : ℕ) := (ℤ × ℤ) × PrimeLists x K × (Fin K → List Particle)

/-- Validity of a memory state. -/
def MemValid {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) : Prop :=
  Int.gcd s.1.1 s.1.2 = 1 ∧ (∀ i j, s.2.1 i j ∈ primeBand S.x (F.a i)) ∧
    ∀ i, ∀ e ∈ s.2.2 i, e.1 ∈ primeBand S.x (F.a i) ∧ e.2 ≤ e.1

/-- The state measure of (mem:hilbert-space): counting in `z`, `⊗ ν_i^{⊗M_J}` on active lists,
`λ_i^{⊗k}/k!` on memory (anchors with counting measure, PD 04:157-166). -/
def memMeasure {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) : ℝ :=
  if MemValid F S s then
    (∏ i : Fin K, ∏ j : Fin (slotCount S.x), memoryNu S.x K F.a F.q_d i (s.2.1 i j)) *
      ∏ i : Fin K, (((s.2.2 i).map fun e => memoryNu S.x K F.a F.q_d i e.1).prod /
        ((s.2.2 i).length.factorial : ℝ))
  else 0

/-- Total memory size `k_tot`. -/
def memSize {x : ℝ} {K : ℕ} (s : MemPoint x K) : ℕ := ∑ i : Fin K, (s.2.2 i).length

/-- A particle hits `z` when its anchor is `[z]_p`. -/
def particleHits (e : Particle) (z : ℤ × ℤ) : Prop := e.2 = (projLine e.1 z).val

/-- The particle anchored at the current line of `z`. -/
def anchorAt (p : ℕ) (z : ℤ × ℤ) : Particle := (p, (projLine p z).val)

/-- Indices of particles of a list hitting `z`. -/
def hitIndices (l : List Particle) (z : ℤ × ℤ) : Finset (Fin l.length) :=
  Finset.univ.filter fun k => particleHits (l.get k) z

/-- Number of particles of a list hitting `z`. -/
def hitCount (l : List Particle) (z : ℤ × ℤ) : ℕ := (hitIndices l z).card

/-- Remove the particles with the given indices, keeping the order of the others. -/
def removeIndices (l : List Particle) (D : Finset (Fin l.length)) : List Particle :=
  (List.finRange l.length).filterMap fun k => if k ∈ D then none else some (l.get k)

/-- Birth addresses (PD 04:791-799): the `K M_J` initial slots, the canonical target slot of
group `i` at edge `step`, and index `k` of the ghost batch of group `i` at visit `step`. -/
inductive BirthAddress (K : ℕ) where
  | initial (i : Fin K) (j : ℕ)
  | edge (step : ℕ) (i : Fin K)
  | ghost (step : ℕ) (i : Fin K) (k : ℕ)
  deriving DecidableEq

/-- The birth log of a history: performed births with their prime values (an address occurs at
most once).  Global birth distinctness (mem:operator-history) is the final weight `distinctWeight`;
the equality-constraint weights of PD 04:807-823 are `constraintWeight`. -/
abbrev BirthLog (K : ℕ) := List (BirthAddress K × ℕ)

/-- Memory states with their birth log. -/
abbrev LogPoint (x : ℝ) (K : ℕ) := MemPoint x K × BirthLog K

/-- The ghost coefficient of one group (PD 04:196-205): `(-η'_j/ρ)` per deletion, `q_j/ρ²` per
surviving hit, `(-η'_j V_i/ρ)^l / l!` for a batch of `l` with `∏ ν_i`. -/
def ghostGroupCoeff {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ) (i : Fin K)
    (hits deleted l : ℕ) (batch : List ℕ) : ℝ :=
  (-memoryEta S.x F.q_d j / ρ) ^ deleted *
    (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hits - deleted) *
    (-memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ l / (l.factorial : ℝ) *
    (batch.map fun p => memoryNu S.x K F.a F.q_d i p).prod

/-- Ghost operation `𝒢_j` (PD 04:196-205), row convention.  In each group: delete a subset `D`
of the hitting particles, then append an ordered batch of `l` new primes anchored at the current
lines; the batch is logged at addresses `ghost j i k`. -/
def logGhost {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  fun σL =>
    let s := σL.1
    ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
      ∑' l : Fin K → ℕ,
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
          if ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then
            ((∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) (D i).card (l i)
                (List.ofFn fun k => ((new i k : ℕ))) : ℝ) : ℂ) *
              f ((s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
                  List.ofFn fun k => anchorAt (new i k) s.1),
                σL.2 ++ (List.finRange K).flatMap fun i =>
                  List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, ((new i k : ℕ))))
          else 0

/-- Per-group edge choice: store the source unshared slot or not, and fill the target unshared
slot by promoting an old particle (index) or by a fresh prime (PD 04:213-223). -/
abbrev EdgeChoice (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (l : List Particle) (i : Fin K) :=
  Bool × (Fin l.length ⊕ primeBand x (a i))

/-- The prime filling the target unshared slot. -/
def edgeNewLabel {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {l : List Particle} {i : Fin K}
    (c : EdgeChoice x a l i) : ℕ :=
  match c.2 with
  | Sum.inl k => (l.get k).1
  | Sum.inr p => p

/-- Target lists: shared slots copied, unshared slot from the choice. -/
def edgeTargetLists {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) : PrimeLists S.x K :=
  fun i jj => if jj.val < momentJ S.x then s.2.1 i jj else edgeNewLabel (c i)

/-- Memory after the edge: promoted particles removed, stored source slots appended with the
source anchor. -/
def edgeNewMemory {K : ℕ} (F : PDFix K) (S : PDScale) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) : Fin K → List Particle :=
  fun i =>
    removeIndices (s.2.2 i)
        (match (c i).2 with
          | Sum.inl k => {k}
          | Sum.inr _ => ∅) ++
      (if (c i).1 then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else [])

/-- Fresh births of edge `step` (target unshared slots filled freshly), logged at `edge step i`. -/
def edgeBirths {K : ℕ} (F : PDFix K) (S : PDScale) (step : ℕ) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) : BirthLog K :=
  (List.finRange K).flatMap fun i =>
    match (c i).2 with
    | Sum.inl _ => []
    | Sum.inr p => [(BirthAddress.edge step i, (p : ℕ))]

/-- Stored and promoted group sets of a choice. -/
def edgeStoredSet {K : ℕ} {x : ℝ} {a : Fin K → ℝ} {s : MemPoint x K}
    (c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i) : Finset (Fin K) :=
  Finset.univ.filter fun i => (c i).1 = true

def edgePromotedSet {K : ℕ} {x : ℝ} {a : Fin K → ℝ} {s : MemPoint x K}
    (c : (i : Fin K) → EdgeChoice x a (s.2.2 i) i) : Finset (Fin K) :=
  Finset.univ.filter fun i => (c i).2.isLeft = true

/-- The local restrictions of an edge (PD 04:218-228): promoted particles hit the target;
physical endpoint list restrictions (distinct primes from the bands at both ends); slot rule and
cross-edge ban; pad dyad and integrality; box and good tests at both ends; `z'` primitive. -/
def EdgeAdmissible {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (s : MemPoint S.x K)
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : Prop :=
  (∀ i, ∀ k, (c i).2 = Sum.inl k → particleHits ((s.2.2 i).get k) z') ∧
    ValidPrimeLists S.x K F.a s.2.1 ∧ ValidPrimeLists S.x K F.a (edgeTargetLists F S s c) ∧
    IsSlotTransition s.2.1 (edgeTargetLists F S s c) ∧
    IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 z') ∧
    Int.gcd z'.1 z'.2 = 1 ∧ envBox S w s.1 ∧ envBox S w z' ∧
    envGood F S w (s.1, s.2.1) ∧ envGood F S w (z', edgeTargetLists F S s c)

/-- The geometric multiplier of an edge, raw (`raw = true`) or comparison part, forward (`𝒜`)
or adjoint (`𝒜*`, conjugate with the roles of source and target exchanged). -/
def edgeMultiplier {K : ℕ} (F : PDFix K) (S : PDScale) (forward raw : Bool)
    (p q : PrimeLists S.x K) (z z' : ℤ × ℤ) : ℂ :=
  let D := sharedProduct p
  if forward then
    (if raw then rawMultiplier F S D (lastProduct q) (lastProduct p) (det2 z z' / (D : ℤ))
      else comparisonMultiplier F S D (lastProduct q) (lastProduct p) (det2 z z' / (D : ℤ)))
  else
    star (if raw then rawMultiplier F S D (lastProduct p) (lastProduct q) (det2 z' z / (D : ℤ))
      else comparisonMultiplier F S D (lastProduct p) (lastProduct q) (det2 z' z / (D : ℤ)))

/-- One piece of the core edge operation `step` (PD 04:207-232) with prescribed stored set `St`,
promoted set `Pr` and multiplier part `raw`: `ρ` per old hit at the source, `V_i^{-1}` per
promotion, `ν_i` per fresh prime, `ρ` per memory particle hitting the target, and the
geometric multiplier (no damping, no active divisibility).  Edge `step` is forward for even
`step` (alternating physical path). -/
def logEdgePiece {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (raw : Bool) (St Pr : Finset (Fin K)) (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  fun σL =>
    let s := σL.1
    ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑' z' : ℤ × ℤ,
        if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z' then
          let mem' := edgeNewMemory F S s c
          ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
              (∏ i : Fin K,
                match (c i).2 with
                | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
                | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
              ρ ^ (∑ i : Fin K, hitCount (mem' i) z') : ℝ) : ℂ) *
            edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1 (edgeTargetLists F S s c) s.1 z' *
            f ((z', edgeTargetLists F S s c, mem'), σL.2 ++ edgeBirths F S step s c)
        else 0

/-- Slot symmetrization of the active lists. -/
def logSym {K : ℕ} (F : PDFix K) (S : PDScale) (f : LogPoint S.x K → ℂ) :
    LogPoint S.x K → ℂ :=
  fun σL => ((permCount S.x K : ℂ))⁻¹ *
    ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      f ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2)

/-- Which edge pieces an edge operator contains. -/
inductive EdgeKind
  | full        -- all pieces: `ℰ_j`
  | clean       -- no store, no promotion, raw minus comparison (PD 04:367-371)
  | dirtyRaw    -- `(St,Pr) ≠ (∅,∅)`, raw part (PD 04:605-714)
  | dirtyCmp    -- `(St,Pr) ≠ (∅,∅)`, comparison part (PD 04:716-770)

/-- The edge operator `ℰ_step` (or one of its parts) between the endpoint slot symmetrizations. -/
def logEdge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (kind : EdgeKind) (step : ℕ) (f : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  let g := logSym F S f
  logSym F S fun σL =>
    match kind with
    | EdgeKind.full => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr g σL - logEdgePiece F S ρ w step false St Pr g σL)
    | EdgeKind.clean =>
        logEdgePiece F S ρ w step true ∅ ∅ g σL - logEdgePiece F S ρ w step false ∅ ∅ g σL
    | EdgeKind.dirtyRaw => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        if St = ∅ ∧ Pr = ∅ then 0 else logEdgePiece F S ρ w step true St Pr g σL
    | EdgeKind.dirtyCmp => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        if St = ∅ ∧ Pr = ∅ then 0 else logEdgePiece F S ρ w step false St Pr g σL

/-- The memory cutoff `Π_B` (PD 04:278-279): restrict to total memory size `≤ B`. -/
def logTrunc {x : ℝ} {K : ℕ} (B : Option ℕ) (f : LogPoint x K → ℂ) : LogPoint x K → ℂ :=
  fun σL => match B with
    | none => f σL
    | some b => if memSize σL.1 ≤ b then f σL else 0

/-- Boundary vector `𝐛` (PD 04:183-185): one at `z = e₁` with empty memory, any active lists. -/
def memBoundary {x : ℝ} {K : ℕ} (s : MemPoint x K) : ℂ :=
  if s.1 = (1, 0) ∧ ∀ i, s.2.2 i = [] then 1 else 0

/-- The initial log: the `K M_J` initial active entries are births. -/
def initialLog {x : ℝ} {K : ℕ} (s : MemPoint x K) : BirthLog K :=
  (List.finRange K).flatMap fun i =>
    (List.finRange (slotCount x)).map fun j => (BirthAddress.initial i j.val, s.2.1 i j)

/-- Left boundary: `𝐛` with the initial log. -/
def logBoundaryIn {x : ℝ} {K : ℕ} (σL : LogPoint x K) : ℂ :=
  if σL.2 = initialLog σL.1 then memBoundary σL.1 else 0

/-- Right boundary `𝐛` weighted by a function of the final log. -/
def logBoundaryOut {x : ℝ} {K : ℕ} (W : BirthLog K → ℂ) (σL : LogPoint x K) : ℂ :=
  memBoundary σL.1 * W σL.2

/-- Weighted inner product on logged states (logs with counting measure). -/
def logInner {K : ℕ} (F : PDFix K) (S : PDScale) (f g : LogPoint S.x K → ℂ) : ℂ :=
  ∑' σL : LogPoint S.x K, (memMeasure F S σL.1 : ℂ) * star (f σL) * g σL

/-- Optional restriction to a prescribed path of positions and active lists at the visits
(`γ = none`: no restriction). -/
def logPathRestrict {K : ℕ} {x : ℝ} (γ : Option (EnvPath x K)) (j : ℕ)
    (f : LogPoint x K → ℂ) : LogPoint x K → ℂ :=
  fun σL => match γ with
    | none => f σL
    | some path =>
        if h : j < pathLength x + 1 then
          (if (σL.1.1, σL.1.2.1) = path ⟨j, h⟩ then f σL else 0)
        else 0

/-- The history function `𝒢_{N-k}ℰ_{N-k}⋯ℰ_{N-1}𝒢_N 𝐛_out` (row convention), with optional
cutoff `Π_B` around every operation and optional path restriction at every visit. -/
def logHistoryFn {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : Option (EnvPath S.x K)) (W : BirthLog K → ℂ) :
    ℕ → LogPoint S.x K → ℂ
  | 0 => logTrunc B (logPathRestrict γ (pathLength S.x)
      (logGhost F S ρ (pathLength S.x) (logTrunc B (logBoundaryOut W))))
  | k + 1 =>
      let j := pathLength S.x - (k + 1)
      logTrunc B (logPathRestrict γ j (logGhost F S ρ j (logTrunc B
        (logEdge F S ρ w EdgeKind.full j (logTrunc B
          (logHistoryFn F S ρ w B γ W k))))))

/-- The history value `⟨𝐛, 𝒢₀ℰ₀𝒢₁⋯ℰ_{N-1}𝒢_N 𝐛⟩` with final log weight `W`. -/
def memHistory {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : Option (EnvPath S.x K)) (W : BirthLog K → ℂ) : ℂ :=
  logInner F S logBoundaryIn (logHistoryFn F S ρ w B γ W (pathLength S.x))

/-- Global birth distinctness: the logged prime values are pairwise distinct. -/
def distinctWeight {K : ℕ} (log : BirthLog K) : ℂ :=
  if (log.map Prod.snd).Nodup then 1 else 0

/-- The value with global birth distinctness and no cutoff, (mem:operator-history). -/
def historyDistinct {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) : ℂ :=
  memHistory F S ρ w none none distinctWeight

/-- The memory cutoff `B = ⌈L²⌉` (PD 04:278). -/
def memoryCutoff (S : PDScale) : ℕ := ⌈Real.rpow S.L 2⌉₊

/-- The value with global birth distinctness and the cutoff `Π_B`. -/
def historyDistinctTrunc {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) : ℂ :=
  memHistory F S ρ w (some (memoryCutoff S)) none distinctWeight

/-- The finite set of potential birth addresses under the cutoff `B` (mem:address-count). -/
def birthAddresses (x : ℝ) (K : ℕ) (B : ℕ) : Finset (BirthAddress K) :=
  ((Finset.univ ×ˢ Finset.range (slotCount x)).image fun p => BirthAddress.initial p.1 p.2) ∪
    ((Finset.range (pathLength x) ×ˢ Finset.univ).image fun p => BirthAddress.edge p.1 p.2) ∪
    ((Finset.range (pathLength x + 1) ×ˢ (Finset.univ ×ˢ Finset.range B)).image
      fun p => BirthAddress.ghost p.1 p.2.1 p.2.2)

/-- Equality-constraint systems: disjoint nonsingleton blocks of addresses (PD 04:807-810). -/
def IsConstraintSystem {K : ℕ} (A : Finset (BirthAddress K))
    (𝒞 : Finset (Finset (BirthAddress K))) : Prop :=
  (∀ C ∈ 𝒞, C ⊆ A ∧ 2 ≤ C.card) ∧ ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → Disjoint C C'

/-- All constraint systems on an address set. -/
def constraintSystems {K : ℕ} (A : Finset (BirthAddress K)) :
    Finset (Finset (Finset (BirthAddress K))) :=
  A.powerset.powerset.filter (IsConstraintSystem A)

/-- Weight `∏_C 1_{E_C}`: every address of each block performed, with a common value. -/
def constraintWeight {K : ℕ} (𝒞 : Finset (Finset (BirthAddress K))) (log : BirthLog K) : ℂ :=
  ∏ C ∈ 𝒞, if ∃ v : ℕ, ∀ ad ∈ C, (ad, v) ∈ log then 1 else 0

/-- Rank `r(𝒞) = Σ_C (|C| - 1)` (mem:rank-definition). -/
def constraintRank {K : ℕ} (𝒞 : Finset (Finset (BirthAddress K))) : ℕ :=
  ∑ C ∈ 𝒞, (C.card - 1)

/-- Coefficient `∏_C (-1)^{|C|-1} (|C|-1)!` of (mem:partition-identity). -/
def constraintCoeff {K : ℕ} (𝒞 : Finset (Finset (BirthAddress K))) : ℤ :=
  ∏ C ∈ 𝒞, (-1 : ℤ) ^ (C.card - 1) * ((C.card - 1).factorial : ℤ)

/-- The extracted baseline `∏_p b'_p` over all group primes (PD 04:116). -/
def memoryBaseline {K : ℕ} (F : PDFix K) (S : PDScale) : ℝ :=
  ∏ p ∈ markedPrimes S.x K F.a, memoryBPrime S.x F.q_d p

/-- The fixed memory parameter `ρ` (mem:rho): `0 < ρ < 1`, `ρ² > √q_d`. -/
def IsMemoryRho (q_d ρ : ℝ) : Prop := 0 < ρ ∧ ρ < 1 ∧ Real.sqrt q_d < ρ ^ 2

/-! ### Operators on `ℋ_B` without distinctness: plain test functions, norms, Schur sums -/

/-- Plain (log-free) version of an operator on logged states: the test function ignores the
log, so the log is carried but never constrains (this is `ℋ` without birth distinctness). -/
def plainOp {K : ℕ} {x : ℝ}
    (op : (LogPoint x K → ℂ) → LogPoint x K → ℂ) (f : MemPoint x K → ℂ) : MemPoint x K → ℂ :=
  fun s => op (fun σL => f σL.1) (s, [])

/-- `𝒢_j` on `ℋ` (no distinctness). -/
def memGhost {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ) :
    (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ :=
  plainOp (logGhost F S ρ j)

/-- `ℰ_j` (or a part) on `ℋ` (no distinctness). -/
def memEdge {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (kind : EdgeKind)
    (j : ℕ) : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ :=
  plainOp (logEdge F S ρ w kind j)

/-- Kernel of an operator in the row convention: `K(s,s') = (Op δ_{s'})(s)`. -/
def memKernel {x : ℝ} {K : ℕ} (op : (MemPoint x K → ℂ) → MemPoint x K → ℂ)
    (s s' : MemPoint x K) : ℂ :=
  op (fun t => if t = s' then 1 else 0) s

/-- Squared norm on a finite set of states. -/
def memNormSqOn {K : ℕ} (F : PDFix K) (S : PDScale) (T : Finset (MemPoint S.x K))
    (f : MemPoint S.x K → ℂ) : ℝ :=
  ∑ s ∈ T, memMeasure F S s * ‖f s‖ ^ 2

/-- Permutations of the coordinates within each memory list. -/
abbrev MemoryPermutation {x : ℝ} {K : ℕ} (s : MemPoint x K) :=
  (i : Fin K) → Equiv.Perm (Fin (s.2.2 i).length)

/-- Reorder each memory list by a permutation of its slots. -/
def memoryPermute {x : ℝ} {K : ℕ} (s : MemPoint x K) (σ : MemoryPermutation s) :
    MemPoint x K :=
  (s.1, s.2.1, fun i => List.ofFn (fun j => (s.2.2 i).get (σ i j)))

/-- The source Hilbert space identifies reorderings of each memory list. Correction from
refutation lane `sol-gate-b` implements this by averaging over all such reorderings. -/
noncomputable def memorySym {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) (s : MemPoint x K) : ℂ :=
  (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
    ∑ σ : MemoryPermutation s, f (memoryPermute s σ)

/-- A function is memory-symmetric when reordering list coordinates does not change it. -/
def IsMemorySymmetric {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) : Prop :=
  ∀ s σ, f (memoryPermute s σ) = f s

/-- Symmetrizing twice has the same effect as symmetrizing once. -/
theorem memorySym_idempotent {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) :
    memorySym (memorySym f) = memorySym f := by
  funext s
  sorry

/-- Averaging over memory permutations contracts the weighted norm on permutation-closed sets. -/
theorem memorySym_contraction {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hT : ∀ s ∈ T, ∀ σ, memoryPermute s σ ∈ T) :
    memNormSqOn F S T (memorySym f) ≤ memNormSqOn F S T f := by
  sorry

/-- The averaged function is invariant under memory-list permutations. -/
theorem memorySym_isMemorySymmetric {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) :
    IsMemorySymmetric (memorySym f) := by
  sorry

/-- `‖Π_B Op Π_B‖_{ℋ→ℋ} ≤ c`, tested on finitely supported functions and finite output sets. -/
def MemOpNormLE {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ℝ) : Prop :=
  ∀ (T T' : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ),
    (∀ s, s ∉ T → f s = 0) → (∀ s ∈ T, memSize s ≤ B) → (∀ s ∈ T', memSize s ≤ B) →
      memNormSqOn F S T' (op f) ≤ c ^ 2 * memNormSqOn F S T f

/-- Weighted Schur row bound with weight `v₀^{k_tot}` on `ℋ_B` (PD 04:374-384). -/
def MemRowSchurLE {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v₀ R : ℝ) : Prop :=
  ∀ s : MemPoint S.x K, MemValid F S s → memSize s ≤ B → ∀ T : Finset (MemPoint S.x K),
    (∀ s' ∈ T, memSize s' ≤ B) →
      ∑ s' ∈ T, ‖memKernel op s s'‖ * v₀ ^ memSize s' ≤ R * v₀ ^ memSize s

/-- Weighted Schur column bound (row bound of the measure adjoint). -/
def MemColSchurLE {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v₀ Cc : ℝ) : Prop :=
  ∀ s' : MemPoint S.x K, MemValid F S s' → memSize s' ≤ B → ∀ T : Finset (MemPoint S.x K),
    (∀ s ∈ T, memSize s ≤ B) →
      ∑ s ∈ T, memMeasure F S s * ‖memKernel op s s'‖ * v₀ ^ memSize s ≤
        Cc * memMeasure F S s' * v₀ ^ memSize s'

/-- Operator norm after projecting the input to the symmetric memory space. Correction from
refutation lane `sol-gate-b` gives the Hilbert-space interface used by the PD memory bounds. -/
noncomputable def MemOpNormLE_sym {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ℝ) : Prop :=
  MemOpNormLE F S B (fun f => op (memorySym f)) c

/-- Row Schur bound after projecting the input to the symmetric memory space. -/
noncomputable def MemRowSchurLE_sym {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v₀ R : ℝ) : Prop :=
  MemRowSchurLE F S B (fun f => op (memorySym f)) v₀ R

/-- Column Schur bound after projecting the input to the symmetric memory space. -/
noncomputable def MemColSchurLE_sym {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v₀ Cc : ℝ) : Prop :=
  MemColSchurLE F S B (fun f => op (memorySym f)) v₀ Cc

/-- One piece of `ℰ_j` on `ℋ` (no distinctness): prescribed stored set `St`, promoted set `Pr`,
raw or comparison multiplier, between the endpoint symmetrizations. -/
def memEdgePiece {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (raw : Bool)
    (St Pr : Finset (Fin K)) (j : ℕ) : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ :=
  plainOp fun f => logSym F S (logEdgePiece F S ρ w j raw St Pr (logSym F S f))

/-- Ghost operators preserve memory symmetry. -/
theorem memGhost_preserves_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (memGhost F S ρ j f) := by
  sorry

/-- Edge operators preserve memory symmetry. -/
theorem memEdge_preserves_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (kind : EdgeKind) (j : ℕ)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (memEdge F S ρ w kind j f) := by
  sorry

/-- Each raw or comparison edge piece preserves memory symmetry. -/
theorem memEdgePiece_preserves_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (memEdgePiece F S ρ w raw St Pr j f) := by
  sorry

/-- Fixed data with prescribed `q_d, A₀, η, ψ` (the bands and `K` remain free). -/
def PDFix.Has {K : ℕ} (F : PDFix K) (q_d A₀ : ℝ) (eta psi : ℝ → ℝ) : Prop :=
  F.q_d = q_d ∧ F.A₀ = A₀ ∧ F.eta = eta ∧ F.psi = psi


end

end ArtinPrimitiveRoots.TypeII.PD
