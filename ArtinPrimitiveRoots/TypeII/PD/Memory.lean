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

private def memoryFinCast {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K) :
    Fin ((memoryPermute s σ).2.2 i).length ≃ Fin (s.2.2 i).length :=
  finCongr (by simp [memoryPermute])

private def memoryPermutationReindexFun {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (τ : MemoryPermutation (memoryPermute s σ)) :
    MemoryPermutation s :=
  fun i => ((memoryFinCast s σ i).permCongr (τ i)).trans (σ i)

private def memoryPermutationReindex {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) :
    MemoryPermutation (memoryPermute s σ) ≃ MemoryPermutation s where
  toFun := memoryPermutationReindexFun s σ
  invFun := fun τ i =>
    (memoryFinCast s σ i).symm.permCongr ((τ i).trans (σ i).symm)
  left_inv := by
    intro τ
    funext i
    apply Equiv.ext
    intro j
    simp [memoryPermutationReindexFun, Equiv.permCongr_apply, Equiv.trans]
  right_inv := by
    intro τ
    funext i
    apply Equiv.ext
    intro j
    simp [memoryPermutationReindexFun, Equiv.permCongr_apply, Equiv.trans]

private theorem memoryPermute_get {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K)
    (j : Fin ((memoryPermute s σ).2.2 i).length) :
    ((memoryPermute s σ).2.2 i).get j =
      (s.2.2 i).get (σ i (memoryFinCast s σ i j)) := by
  let j' : Fin (s.2.2 i).length :=
    ⟨j.val, by simpa [memoryPermute] using j.isLt⟩
  have hj' : j' = memoryFinCast s σ i j := by
    apply Fin.ext
    simp [j', memoryFinCast, finCongr_apply_coe]
  change (List.ofFn (fun k : Fin (s.2.2 i).length =>
      (s.2.2 i).get (σ i k)))[j.val]'(by simpa [memoryPermute] using j.isLt) = _
  rw [List.getElem_ofFn]
  exact congrArg (fun k : Fin (s.2.2 i).length =>
    (s.2.2 i).get (σ i k)) hj'

private theorem memoryPermute_index_comp {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (τ : MemoryPermutation (memoryPermute s σ))
    (i : Fin K)
    (j₁ : Fin ((memoryPermute (memoryPermute s σ) τ).2.2 i).length)
    (j₂ : Fin ((memoryPermute s (memoryPermutationReindex s σ τ)).2.2 i).length)
    (hj : (j₁ : ℕ) = j₂) :
    (σ i) (memoryFinCast s σ i
      (τ i (memoryFinCast (memoryPermute s σ) τ i j₁))) =
      (memoryPermutationReindex s σ τ i)
        (memoryFinCast s (memoryPermutationReindex s σ τ) i j₂) := by
  have harg : (memoryFinCast s σ i).symm
      (memoryFinCast s (memoryPermutationReindex s σ τ) i j₂) =
      memoryFinCast (memoryPermute s σ) τ i j₁ := by
    apply Fin.ext
    simp [memoryFinCast, finCongr_apply_coe, finCongr_symm_apply_coe, hj]
  rw [← harg]
  rfl

private theorem memoryPermute_reindex {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (τ : MemoryPermutation (memoryPermute s σ)) :
    memoryPermute (memoryPermute s σ) τ = memoryPermute s (memoryPermutationReindex s σ τ) := by
  classical
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      apply List.ext_get
      · simp [memoryPermute]
      · intro n hn₁ hn₂
        change ((memoryPermute (memoryPermute s σ) τ).2.2 i).get ⟨n, hn₁⟩ =
          ((memoryPermute s (memoryPermutationReindex s σ τ)).2.2 i).get ⟨n, hn₂⟩
        calc
          _ = (s.2.2 i).get (σ i (memoryFinCast s σ i
              (τ i (memoryFinCast (memoryPermute s σ) τ i ⟨n, hn₁⟩)))) := by
                rw [memoryPermute_get, memoryPermute_get]
          _ = (s.2.2 i).get ((memoryPermutationReindex s σ τ i)
              (memoryFinCast s (memoryPermutationReindex s σ τ) i ⟨n, hn₂⟩)) := by
                exact congrArg (fun k : Fin (s.2.2 i).length => (s.2.2 i).get k)
                  (memoryPermute_index_comp s σ τ i ⟨n, hn₁⟩ ⟨n, hn₂⟩ rfl)
          _ = _ := by rw [memoryPermute_get]

private theorem memoryPermute_list_perm {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K) :
    List.Perm ((memoryPermute s σ).2.2 i) (s.2.2 i) := by
  simpa [memoryPermute, Function.comp_def] using
    (Equiv.Perm.ofFn_comp_perm (σ i) (fun j => (s.2.2 i).get j)).trans
      (List.Perm.of_eq (List.ofFn_get (s.2.2 i)))

private theorem memValid_memoryPermute_iff {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s) :
    MemValid F S (memoryPermute s σ) ↔ MemValid F S s := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i e he
    exact h.2.2 i e ((memoryPermute_list_perm s σ i).mem_iff.mpr he)
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro i e he
    exact h.2.2 i e ((memoryPermute_list_perm s σ i).mem_iff.mp he)

private theorem memMeasure_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s) :
    memMeasure F S (memoryPermute s σ) = memMeasure F S s := by
  classical
  by_cases hs : MemValid F S s
  · have ht : MemValid F S (memoryPermute s σ) :=
      (memValid_memoryPermute_iff F S s σ).2 hs
    simp only [memMeasure, if_pos ht, if_pos hs]
    simp only [memoryPermute]
    apply congrArg (fun r : ℝ =>
      (∏ i : Fin K, ∏ j : Fin (slotCount S.x),
        memoryNu S.x K F.a F.q_d i (s.2.1 i j)) * r)
    · apply Finset.prod_congr rfl
      intro i hi
      have hprod := (memoryPermute_list_perm s σ i).map
        (fun e => memoryNu S.x K F.a F.q_d i e.1)
      simp only [memoryPermute] at hprod
      rw [hprod.prod_eq]
      simp [memoryPermute]
  · have ht : ¬ MemValid F S (memoryPermute s σ) := by
      intro ht
      exact hs ((memValid_memoryPermute_iff F S s σ).1 ht)
    simp [memMeasure, hs, ht]

private theorem memSize_memoryPermute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) : memSize (memoryPermute s σ) = memSize s := by
  simp [memSize, memoryPermute]

private theorem memorySym_card_pos {x : ℝ} {K : ℕ} (s : MemPoint x K) :
    0 < Fintype.card (MemoryPermutation s) := by
  exact Fintype.card_pos

private theorem memorySym_reindex {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (f : MemPoint x K → ℂ) :
    ∑ τ : MemoryPermutation (memoryPermute s σ), f (memoryPermute s (memoryPermutationReindex s σ τ)) =
      ∑ τ : MemoryPermutation s, f (memoryPermute s τ) := by
  exact Equiv.sum_comp (memoryPermutationReindex s σ)
    (fun τ => f (memoryPermute s τ))

private theorem memorySym_isMemorySymmetric_aux {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) : IsMemorySymmetric (memorySym f) := by
  intro s σ
  change (Fintype.card (MemoryPermutation (memoryPermute s σ)) : ℂ)⁻¹ *
      ∑ τ : MemoryPermutation (memoryPermute s σ),
        f (memoryPermute (memoryPermute s σ) τ) =
    (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
      ∑ τ : MemoryPermutation s, f (memoryPermute s τ)
  have hcard := Fintype.card_congr (memoryPermutationReindex s σ)
  calc
    _ = (Fintype.card (MemoryPermutation (memoryPermute s σ)) : ℂ)⁻¹ *
        ∑ τ : MemoryPermutation (memoryPermute s σ),
          f (memoryPermute s (memoryPermutationReindex s σ τ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [memoryPermute_reindex]
    _ = (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
        ∑ τ : MemoryPermutation s, f (memoryPermute s τ) := by
            rw [hcard, memorySym_reindex]

private theorem memorySym_idempotent_aux {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) :
    memorySym (memorySym f) = memorySym f := by
  funext s
  have hsym := memorySym_isMemorySymmetric_aux f s
  change (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
      ∑ σ : MemoryPermutation s, memorySym f (memoryPermute s σ) = memorySym f s
  rw [show (∑ σ : MemoryPermutation s, memorySym f (memoryPermute s σ)) =
      ∑ σ : MemoryPermutation s, memorySym f s from
        Finset.sum_congr rfl (fun σ hσ => hsym σ)]
  have hcard : (Fintype.card (MemoryPermutation s) : ℂ) ≠ 0 := by
    exact_mod_cast (memorySym_card_pos s).ne'
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

theorem memorySym_idempotent {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) :
    memorySym (memorySym f) = memorySym f := by
  exact memorySym_idempotent_aux f

private abbrev MemoryShape (K : ℕ) := Fin K → ℕ

private def memoryShape {x : ℝ} {K : ℕ} (s : MemPoint x K) : MemoryShape K :=
  fun i => (s.2.2 i).length

private abbrev MemoryShapePermutation {K : ℕ} (n : MemoryShape K) :=
  (i : Fin K) → Equiv.Perm (Fin (n i))

private abbrev MemoryShapePoint {x : ℝ} {K : ℕ} (n : MemoryShape K) :=
  {s : MemPoint x K // memoryShape s = n}

private def memoryShapeToPerm {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (s : MemPoint x K) (h : memoryShape s = n) :
    MemoryShapePermutation n ≃ MemoryPermutation s where
  toFun g i := (finCongr (congrFun h i).symm).permCongr (g i)
  invFun σ i := ((finCongr (congrFun h i).symm).permCongr).symm (σ i)
  left_inv := by
    intro g
    funext i
    exact (finCongr (congrFun h i).symm).permCongr.symm_apply_apply (g i)
  right_inv := by
    intro σ
    funext i
    exact (finCongr (congrFun h i).symm).permCongr.apply_symm_apply (σ i)

private theorem memoryShape_eq_memoryPermute {x : ℝ} {K : ℕ}
    (s : MemPoint x K) (σ : MemoryPermutation s) :
    memoryShape (memoryPermute s σ) = memoryShape s := by
  funext i
  simp [memoryShape, memoryPermute]

private def memoryShapeAction {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (s : MemoryShapePoint (x := x) n) (g : MemoryShapePermutation n) :
    MemoryShapePoint (x := x) n :=
  ⟨memoryPermute s.1 (memoryShapeToPerm s.1 s.2 g), by
    rw [memoryShape_eq_memoryPermute]
    exact s.2⟩

private theorem memoryShapeAction_inverse {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (s : MemoryShapePoint (x := x) n) (g : MemoryShapePermutation n) :
    memoryShapeAction (memoryShapeAction s g) (fun i => (g i).symm) = s := by
  let σ := memoryShapeToPerm s.1 s.2 g
  let t := memoryPermute s.1 σ
  have ht : memoryShape t = n := by simpa [t, σ, memoryShape_eq_memoryPermute] using s.2
  let τ := memoryShapeToPerm t ht (fun i => (g i).symm)
  have hcomp : memoryPermutationReindex s.1 σ τ = 1 := by
    funext i
    apply Equiv.ext
    intro j
    let es : Fin (n i) ≃ Fin (s.1.2.2 i).length :=
      finCongr (congrFun s.2 i).symm
    let et : Fin (n i) ≃ Fin (t.2.2 i).length :=
      finCongr (congrFun ht i).symm
    let c := memoryFinCast s.1 σ i
    have hc (k : Fin (n i)) : c (et k) = es k := by
      apply Fin.ext
      rfl
    have hcinv (k : Fin (s.1.2.2 i).length) :
        et.symm (c.symm k) = es.symm k := by
      apply es.injective
      have hh := hc (et.symm (c.symm k))
      simpa using hh.symm
    have hsApp (k : Fin (s.1.2.2 i).length) :
        (σ i) k = es ((g i) (es.symm k)) := by
      change (es.permCongr (g i)) k = es ((g i) (es.symm k))
      rw [Equiv.permCongr_apply]
    have htApp (k : Fin (t.2.2 i).length) :
        (τ i) k = et ((g i).symm (et.symm k)) := by
      change (et.permCongr ((g i).symm)) k = et ((g i).symm (et.symm k))
      rw [Equiv.permCongr_apply]
    change (σ i) (c ((τ i) (c.symm j))) = j
    rw [htApp, hsApp, hc, hcinv]
    simp
  apply Subtype.ext
  change memoryPermute t τ = s.1
  rw [memoryPermute_reindex, hcomp]
  simp [memoryPermute]

private def memoryShapeActionEquiv {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (g : MemoryShapePermutation n) :
    MemoryShapePoint (x := x) n ≃ MemoryShapePoint (x := x) n where
  toFun s := memoryShapeAction s g
  invFun s := memoryShapeAction s (fun i => (g i).symm)
  left_inv s := memoryShapeAction_inverse s g
  right_inv s := memoryShapeAction_inverse s (fun i => (g i).symm)

private theorem memoryMeasure_memoryShapeAction {K : ℕ} {n : MemoryShape K}
    (F : PDFix K) (S : PDScale) (s : MemoryShapePoint (x := S.x) n)
    (g : MemoryShapePermutation n) :
    memMeasure F S (memoryShapeAction s g).1 = memMeasure F S s.1 := by
  exact memMeasure_memoryPermute F S s.1 (memoryShapeToPerm s.1 s.2 g)

private theorem memorySym_eq_shapeAverage {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (f : MemPoint x K → ℂ) (s : MemoryShapePoint (x := x) n) :
    memorySym f s.1 =
      (Fintype.card (MemoryShapePermutation n) : ℂ)⁻¹ *
        ∑ g : MemoryShapePermutation n, f (memoryShapeAction s g).1 := by
  classical
  let e := memoryShapeToPerm s.1 s.2
  have hcard : Fintype.card (MemoryShapePermutation n) =
      Fintype.card (MemoryPermutation s.1) := Fintype.card_congr e
  have hcardC : (Fintype.card (MemoryPermutation s.1) : ℂ) =
      (Fintype.card (MemoryShapePermutation n) : ℂ) := by
    exact_mod_cast hcard.symm
  have hsum := Equiv.sum_comp e (fun σ : MemoryPermutation s.1 => f (memoryPermute s.1 σ))
  unfold memorySym
  rw [hcardC, hsum.symm]
  simp [memoryShapeAction, e]

private abbrev MemoryShapeStratum {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (n : MemoryShape K) :=
  {s : MemPoint x K // s ∈ T ∧ memoryShape s = n}

private noncomputable instance memoryShapeStratumFintype {x : ℝ} {K : ℕ}
    (T : Finset (MemPoint x K)) (n : MemoryShape K) : Fintype (MemoryShapeStratum T n) := by
  classical
  letI : Fintype {s : MemPoint x K // s ∈ T} := Finset.fintypeCoeSort T
  refine Fintype.ofInjective (fun s : MemoryShapeStratum T n =>
    (⟨s.1, s.2.1⟩ : {s : MemPoint x K // s ∈ T})) ?_
  intro a b hab
  have hval : a.1 = b.1 :=
    congrArg (fun q : {s : MemPoint x K // s ∈ T} => q.1) hab
  apply Subtype.ext
  exact hval

private def memoryShapeStratumEquiv {x : ℝ} {K : ℕ} {n : MemoryShape K}
    (T : Finset (MemPoint x K))
    (hT : ∀ s ∈ T, ∀ σ, memoryPermute s σ ∈ T)
    (g : MemoryShapePermutation n) : MemoryShapeStratum T n ≃ MemoryShapeStratum T n where
  toFun q :=
    let s : MemoryShapePoint (x := x) n := ⟨q.1, q.2.2⟩
    let σ := memoryShapeToPerm q.1 q.2.2 g
    ⟨(memoryShapeAction s g).1, hT q.1 q.2.1 σ, (memoryShapeAction s g).2⟩
  invFun q :=
    let s : MemoryShapePoint (x := x) n := ⟨q.1, q.2.2⟩
    let σ := memoryShapeToPerm q.1 q.2.2 (fun i => (g i).symm)
    ⟨(memoryShapeAction s (fun i => (g i).symm)).1,
      hT q.1 q.2.1 σ, (memoryShapeAction s (fun i => (g i).symm)).2⟩
  left_inv q := by
    apply Subtype.ext
    change (memoryShapeAction (memoryShapeAction ⟨q.1, q.2.2⟩ g)
      (fun i => (g i).symm)).1 = q.1
    exact congrArg Subtype.val (memoryShapeAction_inverse ⟨q.1, q.2.2⟩ g)
  right_inv q := by
    apply Subtype.ext
    change (memoryShapeAction (memoryShapeAction ⟨q.1, q.2.2⟩ (fun i => (g i).symm))
      g).1 = q.1
    exact congrArg Subtype.val
      (memoryShapeAction_inverse ⟨q.1, q.2.2⟩ (fun i => (g i).symm))

private theorem finite_average_norm_sq {G : Type*} [Fintype G] [Nonempty G] (a : G → ℂ) :
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, a g‖ ^ 2 ≤
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖a g‖ ^ 2 := by
  classical
  let n : ℝ := Fintype.card G
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hn : n ≠ 0 := hn0.ne'
  have htriangle : ‖∑ g : G, a g‖ ≤ ∑ g : G, ‖a g‖ := norm_sum_le Finset.univ a
  have htriangleSq : ‖∑ g : G, a g‖ ^ 2 ≤ (∑ g : G, ‖a g‖) ^ 2 := by
    have hdiff : 0 ≤ (∑ g : G, ‖a g‖) - ‖∑ g : G, a g‖ := sub_nonneg.mpr htriangle
    have hsum : 0 ≤ (∑ g : G, ‖a g‖) + ‖∑ g : G, a g‖ := by positivity
    nlinarith [mul_nonneg hdiff hsum]
  have hcs : (∑ g : G, ‖a g‖) ^ 2 ≤
      n * ∑ g : G, ‖a g‖ ^ 2 := by
    simpa [n] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun g : G => ‖a g‖))
  calc
    ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, a g‖ ^ 2 =
        n⁻¹ ^ 2 * ‖∑ g : G, a g‖ ^ 2 := by
          rw [norm_mul]
          have hnorm : ‖(Fintype.card G : ℂ)⁻¹‖ = n⁻¹ := by
            simp [n]
          rw [hnorm]
          ring
    _ ≤ n⁻¹ ^ 2 * (∑ g : G, ‖a g‖) ^ 2 := by
        gcongr
    _ ≤ n⁻¹ ^ 2 * (n * ∑ g : G, ‖a g‖ ^ 2) := by
        gcongr
    _ = n⁻¹ * ∑ g : G, ‖a g‖ ^ 2 := by
        field_simp [hn] <;> ring

private theorem finite_equiv_average_contraction {α G : Type*} [DecidableEq α]
    [Fintype G] [Nonempty G] (T : Finset α) (e : G → α ≃ α)
    (hT : ∀ g x, x ∈ T ↔ e g x ∈ T) (μ : α → ℝ)
    (hμ : ∀ x ∈ T, ∀ g, μ (e g x) = μ x)
    (hμ0 : ∀ x ∈ T, 0 ≤ μ x) (f : α → ℂ) :
    (∑ x ∈ T, μ x * ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, f (e g x)‖ ^ 2) ≤
      ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
  classical
  have hsum (g : G) :
      (∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2) =
        ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
    calc
      _ = ∑ x ∈ T, μ (e g x) * ‖f (e g x)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hμ x hx g]
      _ = ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        apply Finset.sum_bij (fun x hx => e g x)
        · intro x hx
          exact (hT g x).mp hx
        · intro x₁ hx₁ x₂ hx₂ heq
          exact (e g).injective heq
        · intro y hy
          refine ⟨(e g).symm y, (hT g ((e g).symm y)).mpr ?_, ?_⟩
          · simpa using hy
          · simp
        · intro x hx
          rfl
  have hdouble :
      (∑ x ∈ T, μ x * ((Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ‖f (e g x)‖ ^ 2)) =
        (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
    calc
      _ = ∑ x ∈ T, ∑ g : G,
            (Fintype.card G : ℝ)⁻¹ * (μ x * ‖f (e g x)‖ ^ 2) := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            μ x * ((Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖f (e g x)‖ ^ 2) =
                (Fintype.card G : ℝ)⁻¹ *
                  (μ x * ∑ g : G, ‖f (e g x)‖ ^ 2) := by ring
            _ = (Fintype.card G : ℝ)⁻¹ *
                  ∑ g : G, μ x * ‖f (e g x)‖ ^ 2 := by rw [Finset.mul_sum]
            _ = ∑ g : G, (Fintype.card G : ℝ)⁻¹ *
                  (μ x * ‖f (e g x)‖ ^ 2) := by rw [Finset.mul_sum]
      _ = ∑ g : G, ∑ x ∈ T,
            (Fintype.card G : ℝ)⁻¹ * (μ x * ‖f (e g x)‖ ^ 2) := by
          rw [Finset.sum_comm]
      _ = (Fintype.card G : ℝ)⁻¹ *
            ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
          calc
            _ = ∑ g : G, (Fintype.card G : ℝ)⁻¹ *
                  ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro g hg
              rw [← Finset.mul_sum]
            _ = (Fintype.card G : ℝ)⁻¹ *
                  ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := by
              rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ T, μ x * ((Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ‖f (e g x)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left
          (finite_average_norm_sq (fun g => f (e g x))) (hμ0 x hx)
    _ = (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f (e g x)‖ ^ 2 := hdouble
    _ = (Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro g hg
        exact hsum g
    _ = ∑ x ∈ T, μ x * ‖f x‖ ^ 2 := by
        have hcard : (Fintype.card G : ℝ) ≠ 0 := by
          exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G).ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [hcard]

private theorem finset_sum_attach_eq {α M : Type*} [DecidableEq α]
    [AddCommMonoid M] (T : Finset α) (f : α → M) :
    (∑ x ∈ T, f x) = ∑ x : {x // x ∈ T}, f x.1 := by
  classical
  rw [← Finset.sum_attach]
  simp

private theorem memorySym_contraction_shape {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (hT : ∀ s ∈ T, ∀ σ, memoryPermute s σ ∈ T)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (f : MemPoint S.x K → ℂ)
    (n : MemoryShape K) :
    (∑ s : MemoryShapeStratum T n,
        memMeasure F S s.1 * ‖memorySym f s.1‖ ^ 2) ≤
      ∑ s : MemoryShapeStratum T n, memMeasure F S s.1 * ‖f s.1‖ ^ 2 := by
  classical
  let G := MemoryShapePermutation n
  let e : G → MemoryShapeStratum T n ≃ MemoryShapeStratum T n :=
    fun g => memoryShapeStratumEquiv T hT g
  let μ : MemoryShapeStratum T n → ℝ := fun s => memMeasure F S s.1
  let f' : MemoryShapeStratum T n → ℂ := fun s => f s.1
  have hμe (s : MemoryShapeStratum T n) (g : G) : μ (e g s) = μ s := by
    simpa [μ, e, memoryShapeStratumEquiv] using
      (memoryMeasure_memoryShapeAction F S ⟨s.1, s.2.2⟩ g)
  have havg (s : MemoryShapeStratum T n) :
      memorySym f s.1 = (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, f' (e g s) := by
    rw [memorySym_eq_shapeAverage f ⟨s.1, s.2.2⟩]
    rfl
  have hcontract := finite_equiv_average_contraction
    (α := MemoryShapeStratum T n) (G := G)
    Finset.univ e (by intro g s; simp) μ
    (by intro s hs g; exact hμe s g)
    (by intro s hs; exact hμ s.1) f'
  have hleft :
      (∑ s : MemoryShapeStratum T n, μ s *
          ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, f' (e g s)‖ ^ 2) =
        ∑ s : MemoryShapeStratum T n,
          memMeasure F S s.1 * ‖memorySym f s.1‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [← havg s]
  calc
    _ = ∑ s : MemoryShapeStratum T n,
          μ s * ‖(Fintype.card G : ℂ)⁻¹ * ∑ g : G, f' (e g s)‖ ^ 2 := hleft.symm
    _ ≤ ∑ s : MemoryShapeStratum T n, μ s * ‖f' s‖ ^ 2 := hcontract
    _ = ∑ s : MemoryShapeStratum T n, memMeasure F S s.1 * ‖f s.1‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro s hs
          rfl

private abbrev MemoryShapeIndex {x : ℝ} {K : ℕ} (T : Finset (MemPoint x K)) :=
  Σ n : {n : MemoryShape K // n ∈ T.image memoryShape}, MemoryShapeStratum T n.1

private def memoryShapeIndexEquiv {x : ℝ} {K : ℕ} (T : Finset (MemPoint x K)) :
    {s : MemPoint x K // s ∈ T} ≃ MemoryShapeIndex T where
  toFun s :=
    let n := memoryShape s.1
    ⟨⟨n, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩,
      ⟨s.1, s.2, rfl⟩⟩
  invFun q := ⟨q.2.1, q.2.2.1⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv q := by
    rcases q with ⟨⟨n, hn⟩, ⟨s, hsT, hsN⟩⟩
    cases hsN
    rfl


/-- Averaging over memory permutations contracts the weighted norm on permutation-closed sets.  The hypothesis `0 ≤ memMeasure` was added on 2026-10-07: for arbitrary data the measure can be negative and the inequality fails (lane `sol-gate-b2`). -/
theorem memorySym_contraction {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hT : ∀ s ∈ T, ∀ σ, memoryPermute s σ ∈ T) :
    memNormSqOn F S T (memorySym f) ≤ memNormSqOn F S T f := by
  classical
  have hsumShape (g : MemPoint S.x K → ℂ) :
      memNormSqOn F S T g =
        ∑ q : MemoryShapeIndex T, memMeasure F S q.2.1 * ‖g q.2.1‖ ^ 2 := by
    unfold memNormSqOn
    rw [finset_sum_attach_eq]
    simpa [memoryShapeIndexEquiv] using
      (Equiv.sum_comp (memoryShapeIndexEquiv T)
        (fun q : MemoryShapeIndex T => memMeasure F S q.2.1 * ‖g q.2.1‖ ^ 2))
  have hsplit (g : MemPoint S.x K → ℂ) :
      (∑ q : MemoryShapeIndex T, memMeasure F S q.2.1 * ‖g q.2.1‖ ^ 2) =
    ∑ n : {n : MemoryShape K // n ∈ T.image memoryShape},
          ∑ s : MemoryShapeStratum T n.1, memMeasure F S s.1 * ‖g s.1‖ ^ 2 := by
    change (∑ q : (Σ n : {n : MemoryShape K // n ∈ T.image memoryShape},
        MemoryShapeStratum T n.1), memMeasure F S q.2.1 * ‖g q.2.1‖ ^ 2) = _
    exact Fintype.sum_sigma'
      (fun (n : {n : MemoryShape K // n ∈ T.image memoryShape})
        (s : MemoryShapeStratum T n.1) => memMeasure F S s.1 * ‖g s.1‖ ^ 2)
  rw [hsumShape (memorySym f), hsumShape f, hsplit (memorySym f), hsplit f]
  apply Finset.sum_le_sum
  intro n hn
  exact memorySym_contraction_shape F S T hT hμ f n.1

/-- The averaged function is invariant under memory-list permutations. -/
theorem memorySym_isMemorySymmetric {x : ℝ} {K : ℕ} (f : MemPoint x K → ℂ) :
    IsMemorySymmetric (memorySym f) := by
  exact memorySym_isMemorySymmetric_aux f

private theorem memorySym_eq_self_of_isMemorySymmetric {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) (hf : IsMemorySymmetric f) : memorySym f = f := by
  funext s
  unfold memorySym
  have hsum :
      (∑ σ : MemoryPermutation s, f (memoryPermute s σ)) =
        ∑ σ : MemoryPermutation s, f s := by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact hf s σ
  rw [hsum]
  have hcard : (Fintype.card (MemoryPermutation s) : ℂ) ≠ 0 := by
    exact_mod_cast (memorySym_card_pos s).ne'
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

private def memoryFinSuccCongr {n m : ℕ} (e : Fin n ≃ Fin m) : Fin (n + 1) ≃ Fin (m + 1) :=
  let en := finSuccEquiv' (0 : Fin (n + 1))
  let em := finSuccEquiv' (0 : Fin (m + 1))
  (en.trans (Equiv.optionCongr e)).trans em.symm

private theorem memoryFinSuccCongr_zero {n m : ℕ} (e : Fin n ≃ Fin m) :
    memoryFinSuccCongr e 0 = 0 := by
  simp [memoryFinSuccCongr]

private theorem memoryFinSuccCongr_succ {n m : ℕ} (e : Fin n ≃ Fin m) (j : Fin n) :
    memoryFinSuccCongr e j.succ = (e j).succ := by
  simp [memoryFinSuccCongr, Equiv.trans_apply, finSuccEquiv'_above]

private theorem exists_finEquiv_of_list_perm {α : Type*} {l l' : List α} (h : l.Perm l') :
    ∃ e : Fin l'.length ≃ Fin l.length, ∀ j, l'.get j = l.get (e j) := by
  classical
  induction h using List.Perm.recOnSwap' with
  | nil =>
      refine ⟨Equiv.refl _, ?_⟩
      intro j
      exact Fin.elim0 j
  | cons a h ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨memoryFinSuccCongr e, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => simp [memoryFinSuccCongr]
      | succ j => simpa [memoryFinSuccCongr_succ] using he j
  | swap' a b h ih =>
      obtain ⟨e, he⟩ := ih
      let lift := memoryFinSuccCongr (memoryFinSuccCongr e)
      let q := lift.trans (Equiv.swap 0 1)
      have hq0 : q 0 = 1 := by
        have hlift : lift (0 : Fin _) = 0 := by
          simp [lift, memoryFinSuccCongr_zero]
        change Equiv.swap 0 1 (lift 0) = 1
        rw [hlift]
        exact Equiv.swap_apply_left _ _
      have hq1 : q 1 = 0 := by
        have hlift : lift (1 : Fin _) = 1 := by
          change memoryFinSuccCongr (memoryFinSuccCongr e) (Fin.succ 0) = Fin.succ 0
          rw [memoryFinSuccCongr_succ, memoryFinSuccCongr_zero]
        change Equiv.swap 0 1 (lift 1) = 0
        rw [hlift]
        exact Equiv.swap_apply_right _ _
      have hqt (j : _) : q j.succ.succ = (e j).succ.succ := by
        have hlift : lift j.succ.succ = (e j).succ.succ := by
          simp [lift, memoryFinSuccCongr_succ]
        change Equiv.swap 0 1 (lift j.succ.succ) = (e j).succ.succ
        rw [hlift]
        exact Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)
      refine ⟨q, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => simp [hq0]
      | succ j =>
          cases j using Fin.cases with
          | zero => simp [hq1]
          | succ j => simpa [hqt] using he j
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨e₁, he₁⟩ := ih₁
      obtain ⟨e₂, he₂⟩ := ih₂
      refine ⟨e₂.trans e₁, ?_⟩
      intro j
      calc
        _ = _ := he₂ j
        _ = _ := he₁ (e₂ j)
        _ = _ := rfl

private theorem exists_memoryPerm_of_list_perm {x : ℝ} {K : ℕ}
    (s t : MemPoint x K) (hpos : s.1 = t.1) (hactive : s.2.1 = t.2.1)
    (hmem : ∀ i, List.Perm (s.2.2 i) (t.2.2 i)) :
    ∃ σ : MemoryPermutation s, memoryPermute s σ = t := by
  classical
  let e : (i : Fin K) → Fin (t.2.2 i).length ≃ Fin (s.2.2 i).length := fun i =>
    Classical.choose (exists_finEquiv_of_list_perm (hmem i))
  have he (i : Fin K) (j : Fin (t.2.2 i).length) :
      (t.2.2 i).get j = (s.2.2 i).get (e i j) :=
    Classical.choose_spec (exists_finEquiv_of_list_perm (hmem i)) j
  let c (i : Fin K) : Fin (s.2.2 i).length ≃ Fin (t.2.2 i).length :=
    finCongr (hmem i).length_eq
  let σ : MemoryPermutation s := fun i => (c i).trans (e i)
  refine ⟨σ, ?_⟩
  apply Prod.ext
  · exact hpos
  · apply Prod.ext
    · exact hactive
    · funext i
      apply List.ext_get
      · simpa [memoryPermute] using (hmem i).length_eq
      · intro n hn₁ hn₂
        change ((memoryPermute s σ).2.2 i).get ⟨n, hn₁⟩ =
          (t.2.2 i).get ⟨n, hn₂⟩
        rw [memoryPermute_get, he i ⟨n, hn₂⟩]
        have hidx : (σ i) (memoryFinCast s σ i ⟨n, hn₁⟩) =
            e i ⟨n, hn₂⟩ := by
          change (e i) ((c i) (memoryFinCast s σ i ⟨n, hn₁⟩)) = _
          apply congrArg (e i)
          apply Fin.ext
          simp [c, memoryFinCast, finCongr_apply_coe]
        exact congrArg (fun k : Fin (s.2.2 i).length => (s.2.2 i).get k) hidx

private theorem memorySymmetric_eq_of_list_perm {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) (hf : IsMemorySymmetric f) (s t : MemPoint x K)
    (hpos : s.1 = t.1) (hactive : s.2.1 = t.2.1)
    (hmem : ∀ i, List.Perm (s.2.2 i) (t.2.2 i)) : f s = f t := by
  obtain ⟨σ, hσ⟩ := exists_memoryPerm_of_list_perm s t hpos hactive hmem
  rw [← hσ]
  exact (hf s σ).symm

private theorem memoryLogSymmetric_eq_of_list_perm {x : ℝ} {K : ℕ}
    (g : LogPoint x K → ℂ)
    (hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log))
    (s t : MemPoint x K) (hpos : s.1 = t.1) (hactive : s.2.1 = t.2.1)
    (hmem : ∀ i, List.Perm (s.2.2 i) (t.2.2 i)) (log : BirthLog K) :
    g (t, log) = g (s, log) := by
  obtain ⟨σ, hσ⟩ := exists_memoryPerm_of_list_perm s t hpos hactive hmem
  rw [← hσ]
  exact hg s log σ

private theorem logSym_plain_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f)
    (s : MemPoint S.x K) (σ : MemoryPermutation s) (log : BirthLog K) :
    logSym F S (fun u => f u.1) (memoryPermute s σ, log) =
      logSym F S (fun u => f u.1) (s, log) := by
  classical
  let t := memoryPermute s σ
  unfold logSym
  congr 1
  apply Finset.sum_congr rfl
  intro δ hδ
  change f (t.1, permuteLists δ t.2.1, t.2.2) =
    f (s.1, permuteLists δ s.2.1, s.2.2)
  exact memorySymmetric_eq_of_list_perm f hf
    (t.1, permuteLists δ t.2.1, t.2.2)
    (s.1, permuteLists δ s.2.1, s.2.2) rfl rfl
    (fun i => memoryPermute_list_perm s σ i)

private theorem hitCount_perm {l l' : List Particle} (h : List.Perm l l')
    (z : ℤ × ℤ) : hitCount l z = hitCount l' z := by
  classical
  obtain ⟨e, he⟩ := exists_finEquiv_of_list_perm h
  have himage : (hitIndices l' z).image e = hitIndices l z := by
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hhit := (Finset.mem_filter.mp hj).2
        unfold particleHits at hhit ⊢
        rw [he j] at hhit
        exact hhit
    · intro hk
      obtain ⟨j, hj⟩ := e.surjective k
      refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hhit := (Finset.mem_filter.mp hk).2
        unfold particleHits at hhit ⊢
        rw [he j, hj]
        exact hhit
  unfold hitCount
  have hcard := Finset.card_image_of_injective (hitIndices l' z) e.injective
  rw [himage] at hcard
  exact hcard

private def memoryGhostBody {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) : ℂ :=
  ∑' l : Fin K → ℕ,
    ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
      if ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then
        ((∏ i : Fin K,
          ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) (D i).card (l i)
            (List.ofFn fun k => ((new i k : ℕ))) : ℝ) : ℂ) *
          f (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (D i) ++
            List.ofFn fun k => anchorAt (new i k) s.1)
      else 0

private theorem memGhost_eq_sum_body {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : MemPoint S.x K → ℂ) (s : MemPoint S.x K) :
    memGhost F S ρ j f s =
      ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        memoryGhostBody F S ρ j f s D := rfl

private theorem removeIndices_eq_filter_map {l : List Particle}
    (D : Finset (Fin l.length)) :
    removeIndices l D = ((List.finRange l.length).filter (fun k => k ∉ D)).map l.get := by
  classical
  unfold removeIndices
  calc
    _ = (List.finRange l.length).filterMap
        (fun k => if decide (k ∉ D) then some (l.get k) else none) := by
          apply List.filterMap_congr
          intro k hk
          by_cases h : k ∈ D <;> simp [h]
    _ = ((List.finRange l.length).filter (fun k => k ∉ D)).map l.get := by
          rw [← List.filterMap_filter (p := fun k => decide (k ∉ D))
            (f := fun k => some (l.get k))]
          simp [List.filterMap_eq_map]

private theorem removeIndices_perm_of_getEquiv {l l' : List Particle}
    (e : Fin l'.length ≃ Fin l.length)
    (hget : ∀ j, l'.get j = l.get (e j)) (D : Finset (Fin l'.length)) :
    List.Perm (removeIndices l' D) (removeIndices l (D.image e)) := by
  classical
  let D' := D.image e
  have hmn : l'.length = l.length := by
    have h := Fintype.card_congr e
    simpa using h
  let c : Fin l'.length ≃ Fin l.length := finCongr hmn
  let p : Equiv.Perm (Fin l'.length) := e.trans c.symm
  have hp : p.trans c = e := by
    ext j
    simp [p, Equiv.trans_apply]
  have hc : (List.finRange l'.length).map c = List.finRange l.length := by
    apply List.ext_get
    · simp [hmn]
    · intro n hn₁ hn₂
      simp [c, finCongr_apply_coe]
  have heq : (List.finRange l'.length).map e =
      ((List.finRange l'.length).map p).map c := by
    calc
      _ = (List.finRange l'.length).map (fun j => c (p j)) := by
        apply List.map_congr_left
        intro j hj
        simpa [Equiv.trans_apply] using
          (congrArg (fun q : Fin l'.length ≃ Fin l.length => q j) hp).symm
      _ = ((List.finRange l'.length).map p).map c := by
        simpa [Function.comp_def] using
          (List.map_map (g := c) (f := p) (l := List.finRange l'.length)).symm
  have hfin' := (Equiv.Perm.map_finRange_perm p).map c
  have hfin : List.Perm ((List.finRange l'.length).map e) (List.finRange l.length) := by
    rw [heq]
    exact hfin'.trans (List.Perm.of_eq hc)
  have hpred (k : Fin l.length) :
      (∃ j : Fin l'.length, j ∉ D ∧ e j = k) ↔ k ∉ D' := by
    constructor
    · rintro ⟨j, hj, rfl⟩ hk
      rcases Finset.mem_image.mp hk with ⟨j', hj', hj'e⟩
      exact hj ((e.injective (hj'e.symm)).symm ▸ hj')
    · intro hk
      refine ⟨e.symm k, ?_, e.apply_symm_apply k⟩
      intro hD
      exact hk (Finset.mem_image.mpr ⟨e.symm k, hD, e.apply_symm_apply k⟩)
  have hmapFilter :
      ((List.finRange l'.length).filter (fun j => j ∉ D)).map e =
        ((List.finRange l'.length).map e).filter (fun k => k ∉ D') := by
    simpa [hpred] using
      (List.map_filter (f := e) e.injective (List.finRange l'.length)
        (p := fun j => j ∉ D))
  have hidx :
      List.Perm (((List.finRange l'.length).filter (fun j => j ∉ D)).map e)
        ((List.finRange l.length).filter (fun k => k ∉ D')) := by
    rw [hmapFilter]
    exact hfin.filter _
  have hleft : removeIndices l' D =
      ((List.finRange l'.length).filter (fun j => j ∉ D)).map (fun j => l.get (e j)) := by
    rw [removeIndices_eq_filter_map]
    apply List.map_congr_left
    intro j hj
    exact hget j
  have hright : removeIndices l D' =
      ((List.finRange l.length).filter (fun k => k ∉ D')).map l.get :=
    removeIndices_eq_filter_map (l := l) D'
  have hmap : ((List.finRange l'.length).filter (fun j => j ∉ D)).map
        (fun j => l.get (e j)) =
      (((List.finRange l'.length).filter (fun j => j ∉ D)).map e).map l.get := by
    simpa [Function.comp_def] using
      (List.map_map (g := l.get) (f := e)
        (l := (List.finRange l'.length).filter (fun j => j ∉ D))).symm
  exact (List.Perm.of_eq hleft).trans <| (List.Perm.of_eq hmap).trans <|
    (hidx.map l.get).trans (List.Perm.of_eq hright.symm)

private def memoryIndexSourceEquiv {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K) :
    Fin ((memoryPermute s σ).2.2 i).length ≃ Fin (s.2.2 i).length :=
  (memoryFinCast s σ i).trans (σ i)

private theorem memoryPermute_get_source {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K)
    (j : Fin ((memoryPermute s σ).2.2 i).length) :
    ((memoryPermute s σ).2.2 i).get j =
      (s.2.2 i).get (memoryIndexSourceEquiv s σ i j) := by
  simpa [memoryIndexSourceEquiv, Equiv.trans_apply] using memoryPermute_get s σ i j

private theorem memoryPermute_particleHits {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K)
    (j : Fin ((memoryPermute s σ).2.2 i).length) (z : ℤ × ℤ) :
    particleHits (((memoryPermute s σ).2.2 i).get j) z ↔
      particleHits ((s.2.2 i).get (memoryIndexSourceEquiv s σ i j)) z := by
  simp only [particleHits]
  rw [memoryPermute_get_source]

private theorem memoryHitSubset_image_iff {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K)
    (D : Finset (Fin ((memoryPermute s σ).2.2 i).length)) :
    D ⊆ hitIndices ((memoryPermute s σ).2.2 i) (memoryPermute s σ).1 ↔
      D.image (memoryIndexSourceEquiv s σ i) ⊆ hitIndices (s.2.2 i) s.1 := by
  constructor
  · intro h k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · exact (memoryPermute_particleHits s σ i j (memoryPermute s σ).1).mp
        ((Finset.mem_filter.mp (h hj)).2)
  · intro h j hj
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · apply (memoryPermute_particleHits s σ i j s.1).mpr
      exact (Finset.mem_filter.mp
        (h (Finset.mem_image.mpr ⟨j, hj, rfl⟩))).2

private noncomputable def memoryDeletionEquiv {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) :
    ((i : Fin K) → Finset (Fin ((memoryPermute s σ).2.2 i).length)) ≃
      ((i : Fin K) → Finset (Fin (s.2.2 i).length)) := by
  classical
  refine {
    toFun := fun D i => (D i).image (memoryIndexSourceEquiv s σ i)
    invFun := fun D i => (D i).image (memoryIndexSourceEquiv s σ i).symm
    left_inv := ?_
    right_inv := ?_ }
  · intro D
    funext i
    ext k
    simp [memoryIndexSourceEquiv, Finset.mem_image]
  · intro D
    funext i
    ext k
    simp [memoryIndexSourceEquiv, Finset.mem_image]

private theorem memoryDeletionEquiv_card {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s)
    (D : (i : Fin K) → Finset (Fin ((memoryPermute s σ).2.2 i).length)) (i : Fin K) :
    (memoryDeletionEquiv s σ D i).card = (D i).card := by
  classical
  exact Finset.card_image_of_injective (D i) (memoryIndexSourceEquiv s σ i).injective

private theorem memoryHitCount_permute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) (i : Fin K) :
    hitCount ((memoryPermute s σ).2.2 i) (memoryPermute s σ).1 =
      hitCount (s.2.2 i) s.1 := by
  classical
  let e := memoryIndexSourceEquiv s σ i
  have himage :
      (hitIndices ((memoryPermute s σ).2.2 i) (memoryPermute s σ).1).image e =
        hitIndices (s.2.2 i) s.1 := by
    ext k
    constructor
    · intro hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hhit := (Finset.mem_filter.mp hj).2
        unfold particleHits at hhit ⊢
        rw [memoryPermute_get_source] at hhit
        simpa [memoryPermute] using hhit
    · intro hk
      obtain ⟨j, hj⟩ := e.surjective k
      refine Finset.mem_image.mpr ⟨j, ?_, hj⟩
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hhit := (Finset.mem_filter.mp hk).2
        unfold particleHits at hhit ⊢
        rw [← hj] at hhit
        rw [memoryPermute_get_source]
        simpa [e, memoryIndexSourceEquiv, memoryPermute, Equiv.trans_apply] using hhit
  unfold hitCount
  rw [← himage]
  exact (Finset.card_image_of_injective _ e.injective).symm

private def memoryEdgeChoiceEquiv {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {l l' : Fin K → List Particle} (e : (i : Fin K) → Fin (l' i).length ≃ Fin (l i).length)
    (i : Fin K) :
    EdgeChoice x a (l' i) i ≃ EdgeChoice x a (l i) i :=
  Equiv.prodCongr (Equiv.refl Bool)
    (Equiv.sumCongr (e i) (Equiv.refl (primeBand x (a i))))

private def memoryEdgeChoicePiEquiv {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {l l' : Fin K → List Particle}
    (e : (i : Fin K) → Fin (l' i).length ≃ Fin (l i).length) :
    ((i : Fin K) → EdgeChoice x a (l' i) i) ≃
      ((i : Fin K) → EdgeChoice x a (l i) i) where
  toFun c i := memoryEdgeChoiceEquiv e i (c i)
  invFun c i := (memoryEdgeChoiceEquiv e i).symm (c i)
  left_inv := by
    intro c
    funext i
    cases hci : c i with
    | mk b choice =>
      cases choice <;>
        simp [memoryEdgeChoiceEquiv, Equiv.sumCongr, Equiv.prodCongr, Prod.map, Sum.map,
          Equiv.apply_symm_apply, Function.comp_def, hci]
  right_inv := by
    intro c
    funext i
    cases hci : c i with
    | mk b choice =>
      cases choice <;>
        simp [memoryEdgeChoiceEquiv, Equiv.sumCongr, Equiv.prodCongr, Prod.map, Sum.map,
          Equiv.apply_symm_apply, Function.comp_def, hci]

private def memoryEdgeChoiceMap {x : ℝ} {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i) :
    (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i :=
  memoryEdgeChoicePiEquiv (fun i => memoryIndexSourceEquiv s σ i) c

private theorem edgeTargetLists_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i) :
    edgeTargetLists F S (memoryPermute s σ) c =
      edgeTargetLists F S s (memoryEdgeChoiceMap (x := S.x) F S s σ c) := by
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ c
  funext i j
  by_cases hslot : j.val < momentJ S.x
  · simp [edgeTargetLists, hslot, memoryPermute]
  · cases hchoice : (c i).2 with
    | inl k =>
        have hc' : (c' i).2 = Sum.inl (memoryIndexSourceEquiv s σ i k) := by
          simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
            hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
        simp only [edgeTargetLists, if_neg hslot, edgeNewLabel, c', hchoice, hc']
        exact congrArg Prod.fst (memoryPermute_get_source s σ i k)
    | inr p =>
        have hc' : (c' i).2 = Sum.inr p := by
          simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
            hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
        simp [edgeTargetLists, hslot, edgeNewLabel, c', hchoice, hc']

private theorem edgeNewMemory_perm_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i)
    (i : Fin K) :
    List.Perm (edgeNewMemory F S (memoryPermute s σ) c i)
      (edgeNewMemory F S s (memoryEdgeChoiceMap (x := S.x) F S s σ c) i) := by
  classical
  let e := memoryIndexSourceEquiv s σ i
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ c
  cases hci : c i with
  | mk store choice =>
      cases choice with
      | inl k =>
          have hcs : c' i = (store, Sum.inl (e k)) := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci,
              e]
          have hrem := removeIndices_perm_of_getEquiv e
            (memoryPermute_get_source s σ i) ({k} : Finset (Fin ((memoryPermute s σ).2.2 i).length))
          rw [Finset.image_singleton] at hrem
          simpa [edgeNewMemory, c', hci, hcs, memoryIndexSourceEquiv, memoryPermute] using
            hrem.append_right
              (if store then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else [])
      | inr p =>
          have hcs : c' i = (store, Sum.inr p) := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci,
              e]
          have hrem := removeIndices_perm_of_getEquiv e
            (memoryPermute_get_source s σ i) (∅ : Finset (Fin ((memoryPermute s σ).2.2 i).length))
          rw [Finset.image_empty] at hrem
          simpa [edgeNewMemory, c', hci, hcs, memoryIndexSourceEquiv, memoryPermute] using
            hrem.append_right
              (if store then [anchorAt (s.2.1 i (lastSlot S.x)) s.1] else [])

private theorem edgeAdmissible_memoryPermute_iff {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i)
    (z' : ℤ × ℤ) :
    EdgeAdmissible F S w (memoryPermute s σ) c z' ↔
      EdgeAdmissible F S w s (memoryEdgeChoiceMap (x := S.x) F S s σ c) z' := by
  classical
  let t := memoryPermute s σ
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ c
  have htarget : edgeTargetLists F S t c = edgeTargetLists F S s c' :=
    edgeTargetLists_memoryPermute F S s σ c
  constructor
  · intro h
    rcases h with ⟨hprom, hsource, htargetValid, hslot, hpad, hgcd,
      hboxSource, hboxTarget, hgoodSource, hgoodTarget⟩
    have hprom' : ∀ i k, (c' i).2 = Sum.inl k →
        particleHits ((s.2.2 i).get k) z' := by
      intro i k hk
      cases hchoice : (c i).2 with
      | inl k₀ =>
          have hmapped : (c' i).2 = Sum.inl (memoryIndexSourceEquiv s σ i k₀) := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
              hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
          have hindex : memoryIndexSourceEquiv s σ i k₀ = k := by
            injection hmapped.symm.trans hk
          simpa [hindex] using
            (memoryPermute_particleHits s σ i k₀ z').mp (hprom i k₀ hchoice)
      | inr p =>
          have hmapped : (c' i).2 = Sum.inr p := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
              hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
          simp [hmapped] at hk
    have hsource' : ValidPrimeLists S.x K F.a s.2.1 := by
      simpa [memoryPermute] using hsource
    have htargetValid' : ValidPrimeLists S.x K F.a (edgeTargetLists F S s c') := by
      simpa [htarget, t, c'] using htargetValid
    have hslot' : IsSlotTransition s.2.1 (edgeTargetLists F S s c') := by
      have hslot'' := hslot
      rw [htarget] at hslot''
      simpa [t, memoryPermute] using hslot''
    have hpad' : IsPadAdmissible S.d₀ (sharedProduct s.2.1) (det2 s.1 z') := by
      simpa [memoryPermute] using hpad
    have hboxSource' : envBox S w s.1 := by simpa [memoryPermute] using hboxSource
    have hgoodSource' : envGood F S w (s.1, s.2.1) := by
      simpa [memoryPermute] using hgoodSource
    have hgoodTarget' : envGood F S w (z', edgeTargetLists F S s c') := by
      simpa [htarget, t, c'] using hgoodTarget
    exact ⟨hprom', hsource', htargetValid', hslot', hpad', hgcd,
      hboxSource', hboxTarget, hgoodSource', hgoodTarget'⟩
  · intro h
    rcases h with ⟨hprom, hsource, htargetValid, hslot, hpad, hgcd,
      hboxSource, hboxTarget, hgoodSource, hgoodTarget⟩
    have hprom' : ∀ i k, (c i).2 = Sum.inl k →
        particleHits ((t.2.2 i).get k) z' := by
      intro i k₀ hk
      cases hchoice : (c i).2 with
      | inl k =>
          have hmapped : (c' i).2 = Sum.inl (memoryIndexSourceEquiv s σ i k) := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
              hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
          have hindex : k = k₀ := by
            injection hchoice.symm.trans hk
          have hh := hprom i (memoryIndexSourceEquiv s σ i k) hmapped
          simpa [hindex] using (memoryPermute_particleHits s σ i k z').mpr hh
      | inr p =>
          have hmapped : (c' i).2 = Sum.inr p := by
            simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv,
              hchoice, Equiv.prodCongr, Equiv.sumCongr, Prod.map, Sum.map]
          simp [hchoice] at hk
    have hsource' : ValidPrimeLists S.x K F.a t.2.1 := by
      simpa [t, memoryPermute] using hsource
    have htargetValid' : ValidPrimeLists S.x K F.a (edgeTargetLists F S t c) := by
      simpa [htarget, t, c'] using htargetValid
    have hslot' : IsSlotTransition t.2.1 (edgeTargetLists F S t c) := by
      have hslot'' := hslot
      rw [← htarget] at hslot''
      simpa [t, memoryPermute] using hslot''
    have hpad' : IsPadAdmissible S.d₀ (sharedProduct t.2.1) (det2 t.1 z') := by
      simpa [t, memoryPermute] using hpad
    have hboxSource' : envBox S w t.1 := by simpa [t, memoryPermute] using hboxSource
    have hgoodSource' : envGood F S w (t.1, t.2.1) := by
      simpa [t, memoryPermute] using hgoodSource
    have hgoodTarget' : envGood F S w (z', edgeTargetLists F S t c) := by
      simpa [htarget, t, c'] using hgoodTarget
    exact ⟨hprom', hsource', htargetValid', hslot', hpad', hgcd,
      hboxSource', hboxTarget, hgoodSource', hgoodTarget'⟩


private theorem edgeBirths_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (step : ℕ) (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i) :
    edgeBirths F S step (memoryPermute s σ) c =
      edgeBirths F S step s (memoryEdgeChoiceMap (x := S.x) F S s σ c) := by
  classical
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ c
  unfold edgeBirths
  apply List.flatMap_congr
  intro i hi
  cases hci : (c i).2 with
  | inl k =>
      simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci]
  | inr p =>
      simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci]

private theorem edgeWeight_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (c : (i : Fin K) → EdgeChoice S.x F.a ((memoryPermute s σ).2.2 i) i)
    (z' : ℤ × ℤ) :
    ρ ^ (∑ i : Fin K, hitCount ((memoryPermute s σ).2.2 i) (memoryPermute s σ).1) *
        (∏ i : Fin K,
          match (c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S (memoryPermute s σ) c i) z') =
      ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
        (∏ i : Fin K,
          match (memoryEdgeChoiceMap (x := S.x) F S s σ c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
        ρ ^ (∑ i : Fin K,
          hitCount (edgeNewMemory F S s
            (memoryEdgeChoiceMap (x := S.x) F S s σ c) i) z') := by
  classical
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ c
  have hsource :
      (∑ i : Fin K, hitCount ((memoryPermute s σ).2.2 i) (memoryPermute s σ).1) =
        ∑ i : Fin K, hitCount (s.2.2 i) s.1 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact memoryHitCount_permute s σ i
  have hchoice :
      (∏ i : Fin K, match (c i).2 with
        | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
        | Sum.inr p => memoryNu S.x K F.a F.q_d i p) =
      ∏ i : Fin K, match (c' i).2 with
        | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
        | Sum.inr p => memoryNu S.x K F.a F.q_d i p := by
    apply Finset.prod_congr rfl
    intro i hi
    cases hci : (c i).2 with
    | inl k =>
        simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci]
    | inr p =>
        simp [c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv, memoryEdgeChoiceEquiv, hci]
  have htarget :
      (∑ i : Fin K, hitCount (edgeNewMemory F S (memoryPermute s σ) c i) z') =
        ∑ i : Fin K, hitCount (edgeNewMemory F S s c' i) z' := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hitCount_perm (edgeNewMemory_perm_memoryPermute F S s σ c i) z'
  rw [hsource, hchoice, htarget]

private theorem logEdgePiece_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (g : LogPoint S.x K → ℂ)
    (hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log))
    (s : MemPoint S.x K) (σ : MemoryPermutation s) (log : BirthLog K) :
    logEdgePiece F S ρ w step raw St Pr g (memoryPermute s σ, log) =
      logEdgePiece F S ρ w step raw St Pr g (s, log) := by
  classical
  let t := memoryPermute s σ
  let e : ((i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) ≃
      ((i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) :=
    memoryEdgeChoicePiEquiv (x := S.x) (a := F.a) (l := s.2.2) (l' := t.2.2)
      (fun i => memoryIndexSourceEquiv s σ i)
  let c' := memoryEdgeChoiceMap (x := S.x) F S s σ
  have hstored (c : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) :
      edgeStoredSet c = edgeStoredSet (c' c) := by
    ext i
    simp [edgeStoredSet, c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv,
      memoryEdgeChoiceEquiv]
  have hpromoted (c : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) :
      edgePromotedSet c = edgePromotedSet (c' c) := by
    ext i
    simp [edgePromotedSet, c', memoryEdgeChoiceMap, memoryEdgeChoicePiEquiv,
      memoryEdgeChoiceEquiv]
  have hpred (c : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i) (z' : ℤ × ℤ) :
      (edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w t c z') ↔
        (edgeStoredSet (c' c) = St ∧ edgePromotedSet (c' c) = Pr ∧
          EdgeAdmissible F S w s (c' c) z') := by
    constructor
    · rintro ⟨hs, hp, ha⟩
      exact ⟨(hstored c).symm.trans hs, (hpromoted c).symm.trans hp,
        (edgeAdmissible_memoryPermute_iff F S w s σ c z').mp ha⟩
    · rintro ⟨hs, hp, ha⟩
      exact ⟨(hstored c).trans hs, (hpromoted c).trans hp,
        (edgeAdmissible_memoryPermute_iff F S w s σ c z').mpr ha⟩
  unfold logEdgePiece
  change
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i, ∑' z' : ℤ × ℤ,
      if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w t c z' then
        ((ρ ^ (∑ i : Fin K, hitCount (t.2.2 i) t.1) *
          (∏ i : Fin K, match (c i).2 with
            | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
            | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S t c i) z') : ℝ) : ℂ) *
          edgeMultiplier F S (decide (step % 2 = 0)) raw t.2.1
            (edgeTargetLists F S t c) t.1 z' *
          g ((z', edgeTargetLists F S t c, edgeNewMemory F S t c),
            log ++ edgeBirths F S step t c)
      else 0) = _
  calc
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (t.2.2 i) i, ∑' z' : ℤ × ℤ,
        if edgeStoredSet (c' c) = St ∧ edgePromotedSet (c' c) = Pr ∧
            EdgeAdmissible F S w s (c' c) z' then
          ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
            (∏ i : Fin K, match ((c' c) i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s (c' c) i) z') : ℝ) : ℂ) *
            edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
              (edgeTargetLists F S s (c' c)) s.1 z' *
            g ((z', edgeTargetLists F S s (c' c), edgeNewMemory F S s (c' c)),
              log ++ edgeBirths F S step s (c' c))
        else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply tsum_congr
          intro z'
          by_cases hp : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
              EdgeAdmissible F S w t c z'
          · have hp' := (hpred c z').mp hp
            simp only [if_pos hp, if_pos hp']
            have hweight := edgeWeight_memoryPermute F S ρ s σ c z'
            have hweight' :
                ρ ^ (∑ i : Fin K, hitCount (t.2.2 i) t.1) *
                    (∏ i : Fin K, match (c i).2 with
                      | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
                      | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
                    ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S t c i) z') =
                  ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                    (∏ i : Fin K, match ((c' c) i).2 with
                      | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
                      | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
                    ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s (c' c) i) z') := by
              convert hweight using 1 <;> simp only [t, c']
              congr 2
              apply Finset.prod_congr rfl
              intro i hi
              cases hci : (c i).2 <;> simp [hci]
            have htarget := edgeTargetLists_memoryPermute F S s σ c
            have hmem := fun i =>
              (edgeNewMemory_perm_memoryPermute F S s σ c i).symm
            have hbirth := edgeBirths_memoryPermute F S step s σ c
            have hmult :
                edgeMultiplier F S (decide (step % 2 = 0)) raw t.2.1
                    (edgeTargetLists F S t c) t.1 z' =
                  edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
                    (edgeTargetLists F S s (c' c)) s.1 z' := by
              rw [htarget]
              rfl
            have hout :
                g ((z', edgeTargetLists F S t c, edgeNewMemory F S t c),
                    log ++ edgeBirths F S step t c) =
                  g ((z', edgeTargetLists F S s (c' c), edgeNewMemory F S s (c' c)),
                    log ++ edgeBirths F S step s (c' c)) := by
              rw [hbirth]
              apply memoryLogSymmetric_eq_of_list_perm g hg
                (z', edgeTargetLists F S s (c' c), edgeNewMemory F S s (c' c))
                (z', edgeTargetLists F S t c, edgeNewMemory F S t c) rfl
                htarget.symm hmem (log ++ edgeBirths F S step s (c' c))
            rw [hweight', hmult, hout]
          · have hp' : ¬ (edgeStoredSet (c' c) = St ∧ edgePromotedSet (c' c) = Pr ∧
                EdgeAdmissible F S w s (c' c) z') := fun h => hp ((hpred c z').mpr h)
            simp [hp, hp']
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i, ∑' z' : ℤ × ℤ,
        if edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z' then
          ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
            (∏ i : Fin K, match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ) *
            edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
              (edgeTargetLists F S s c) s.1 z' *
            g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
              log ++ edgeBirths F S step s c)
        else 0 := by
          simpa [c', memoryEdgeChoiceMap, e] using Equiv.sum_comp e (fun c => ∑' z', if
            edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z' then
              ((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
                (∏ i : Fin K, match (c i).2 with
                  | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
                  | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
                ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ) *
                edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
                  (edgeTargetLists F S s c) s.1 z' *
                g ((z', edgeTargetLists F S s c, edgeNewMemory F S s c),
                  log ++ edgeBirths F S step s c)
            else 0)

private theorem logSym_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (g : LogPoint S.x K → ℂ)
    (hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log))
    (s : MemPoint S.x K) (σ : MemoryPermutation s) (log : BirthLog K) :
    logSym F S g (memoryPermute s σ, log) = logSym F S g (s, log) := by
  unfold logSym
  congr 1
  apply Finset.sum_congr rfl
  intro τ hτ
  simpa [memoryPermute] using
    hg (s.1, permuteLists τ s.2.1, s.2.2) log σ

private def logEdgeBody {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (kind : EdgeKind) (step : ℕ) (g : LogPoint S.x K → ℂ) : LogPoint S.x K → ℂ :=
  fun σL =>
    match kind with
    | EdgeKind.full => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr g σL -
          logEdgePiece F S ρ w step false St Pr g σL)
    | EdgeKind.clean =>
        logEdgePiece F S ρ w step true ∅ ∅ g σL -
          logEdgePiece F S ρ w step false ∅ ∅ g σL
    | EdgeKind.dirtyRaw => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        if St = ∅ ∧ Pr = ∅ then 0 else logEdgePiece F S ρ w step true St Pr g σL
    | EdgeKind.dirtyCmp => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        if St = ∅ ∧ Pr = ∅ then 0 else logEdgePiece F S ρ w step false St Pr g σL

private theorem logEdgeBody_memoryPermute {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (kind : EdgeKind) (step : ℕ)
    (g : LogPoint S.x K → ℂ)
    (hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log))
    (s : MemPoint S.x K) (σ : MemoryPermutation s) (log : BirthLog K) :
    logEdgeBody F S ρ w kind step g (memoryPermute s σ, log) =
      logEdgeBody F S ρ w kind step g (s, log) := by
  classical
  cases kind with
  | full =>
      simp only [logEdgeBody, EdgeKind.full]
      apply Finset.sum_congr rfl
      intro St hSt
      apply Finset.sum_congr rfl
      intro Pr hPr
      rw [logEdgePiece_memoryPermute F S ρ w step true St Pr g hg s σ log,
        logEdgePiece_memoryPermute F S ρ w step false St Pr g hg s σ log]
  | clean =>
      simp only [logEdgeBody, EdgeKind.clean]
      rw [logEdgePiece_memoryPermute F S ρ w step true ∅ ∅ g hg s σ log,
        logEdgePiece_memoryPermute F S ρ w step false ∅ ∅ g hg s σ log]
  | dirtyRaw =>
      simp only [logEdgeBody, EdgeKind.dirtyRaw]
      apply Finset.sum_congr rfl
      intro St hSt
      apply Finset.sum_congr rfl
      intro Pr hPr
      by_cases hempty : St = ∅ ∧ Pr = ∅ <;>
        simp [hempty, logEdgePiece_memoryPermute F S ρ w step true St Pr g hg s σ log]
  | dirtyCmp =>
      simp only [logEdgeBody, EdgeKind.dirtyCmp]
      apply Finset.sum_congr rfl
      intro St hSt
      apply Finset.sum_congr rfl
      intro Pr hPr
      by_cases hempty : St = ∅ ∧ Pr = ∅ <;>
        simp [hempty, logEdgePiece_memoryPermute F S ρ w step false St Pr g hg s σ log]
private theorem memoryGhostBody_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : MemPoint S.x K → ℂ)
    (hf : IsMemorySymmetric f) (s : MemPoint S.x K) (σ : MemoryPermutation s)
    (D : (i : Fin K) → Finset (Fin ((memoryPermute s σ).2.2 i).length)) :
    memoryGhostBody F S ρ j f (memoryPermute s σ) D =
      memoryGhostBody F S ρ j f s (memoryDeletionEquiv s σ D) := by
  classical
  let t := memoryPermute s σ
  have hcond :
      (∀ i, D i ⊆ hitIndices (t.2.2 i) t.1) ↔
        (∀ i, (memoryDeletionEquiv s σ D) i ⊆ hitIndices (s.2.2 i) s.1) := by
    constructor
    · intro h i
      simpa [memoryDeletionEquiv] using
        (memoryHitSubset_image_iff s σ i (D i)).mp (h i)
    · intro h i
      simpa [memoryDeletionEquiv] using
        (memoryHitSubset_image_iff s σ i (D i)).mpr (h i)
  unfold memoryGhostBody
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hD : ∀ i, D i ⊆ hitIndices (t.2.2 i) t.1
  · have hD_t : ∀ i, D i ⊆ hitIndices ((memoryPermute s σ).2.2 i)
        (memoryPermute s σ).1 := by simpa [t] using hD
    have hD' : ∀ i, (memoryDeletionEquiv s σ D) i ⊆ hitIndices (s.2.2 i) s.1 :=
      hcond.mp hD
    simp only [if_pos hD_t, if_pos hD']
    have hcoeff :
        (∏ i : Fin K, ghostGroupCoeff F S ρ j i
          (hitCount (t.2.2 i) t.1) (D i).card (l i)
          (List.ofFn fun k => ((new i k : ℕ)))) =
        ∏ i : Fin K, ghostGroupCoeff F S ρ j i
          (hitCount (s.2.2 i) s.1) ((memoryDeletionEquiv s σ D i).card) (l i)
          (List.ofFn fun k => ((new i k : ℕ))) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [memoryHitCount_permute s σ i]
      rw [← memoryDeletionEquiv_card s σ D i]
    have hcoeffC := congrArg (fun r : ℝ => (r : ℂ)) hcoeff
    let outT : MemPoint S.x K :=
      (t.1, t.2.1, fun i => removeIndices (t.2.2 i) (D i) ++
        List.ofFn fun k => anchorAt (new i k) t.1)
    let outS : MemPoint S.x K :=
      (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (memoryDeletionEquiv s σ D i) ++
        List.ofFn fun k => anchorAt (new i k) s.1)
    have hmemout (i : Fin K) : List.Perm (outT.2.2 i) (outS.2.2 i) := by
      dsimp [outT, outS]
      change List.Perm
        (removeIndices (t.2.2 i) (D i) ++ List.ofFn fun k => anchorAt (new i k) t.1)
        (removeIndices (s.2.2 i) ((D i).image (memoryIndexSourceEquiv s σ i)) ++
          List.ofFn fun k => anchorAt (new i k) s.1)
      simpa [t, memoryDeletionEquiv, memoryIndexSourceEquiv, memoryPermute] using
        (removeIndices_perm_of_getEquiv (memoryIndexSourceEquiv s σ i)
          (memoryPermute_get_source s σ i) (D i)).append_right
            (List.ofFn fun k => anchorAt (new i k) s.1)
    have hout : f outT = f outS :=
      memorySymmetric_eq_of_list_perm f hf outT outS rfl rfl hmemout
    have hout' : f outT =
        f (s.1, s.2.1, fun i => removeIndices (s.2.2 i) (memoryDeletionEquiv s σ D i) ++
          List.ofFn fun k => anchorAt (new i k) s.1) := by
      simpa [outS] using hout
    rw [hcoeffC, hout']
  · have hD' : ¬ (∀ i, (memoryDeletionEquiv s σ D) i ⊆ hitIndices (s.2.2 i) s.1) := by
      intro h
      exact hD (hcond.mpr h)
    have hD_t : ¬ (∀ i, D i ⊆ hitIndices ((memoryPermute s σ).2.2 i)
        (memoryPermute s σ).1) := by simpa [t] using hD
    simp [hD_t, hD']

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
  classical
  intro s σ
  let eD := memoryDeletionEquiv s σ
  change memGhost F S ρ j f (memoryPermute s σ) = memGhost F S ρ j f s
  rw [memGhost_eq_sum_body F S ρ j f (memoryPermute s σ),
    memGhost_eq_sum_body F S ρ j f s]
  calc
    (∑ D : (i : Fin K) → Finset (Fin ((memoryPermute s σ).2.2 i).length),
        memoryGhostBody F S ρ j f (memoryPermute s σ) D) =
      ∑ D : (i : Fin K) → Finset (Fin ((memoryPermute s σ).2.2 i).length),
        memoryGhostBody F S ρ j f s (eD D) := by
          apply Finset.sum_congr rfl
          intro D hD
          exact memoryGhostBody_permute F S ρ j f hf s σ D
    _ = ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
          memoryGhostBody F S ρ j f s D :=
        Equiv.sum_comp eD (fun D => memoryGhostBody F S ρ j f s D)

/-- Edge operators preserve memory symmetry. -/
theorem memEdge_preserves_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (kind : EdgeKind) (j : ℕ)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (memEdge F S ρ w kind j f) := by
  classical
  intro s σ
  let g : LogPoint S.x K → ℂ := logSym F S (fun u => f u.1)
  have hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log) := by
    intro s log σ
    exact logSym_plain_memorySym F S f hf s σ log
  change logSym F S (logEdgeBody F S ρ w kind j g) (memoryPermute s σ, []) =
    logSym F S (logEdgeBody F S ρ w kind j g) (s, [])
  exact logSym_memoryPermute F S (logEdgeBody F S ρ w kind j g)
    (fun s log σ => logEdgeBody_memoryPermute F S ρ w kind j g hg s σ log) s σ []

/-- Each raw or comparison edge piece preserves memory symmetry. -/
theorem memEdgePiece_preserves_memorySym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (raw : Bool) (St Pr : Finset (Fin K)) (j : ℕ)
    (f : MemPoint S.x K → ℂ) (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (memEdgePiece F S ρ w raw St Pr j f) := by
  classical
  intro s σ
  let g : LogPoint S.x K → ℂ := logSym F S (fun u => f u.1)
  have hg : ∀ s log σ, g (memoryPermute s σ, log) = g (s, log) := by
    intro s log σ
    exact logSym_plain_memorySym F S f hf s σ log
  let h : LogPoint S.x K → ℂ := logEdgePiece F S ρ w j raw St Pr g
  have hh : ∀ s log σ, h (memoryPermute s σ, log) = h (s, log) := by
    intro s log σ
    exact logEdgePiece_memoryPermute F S ρ w j raw St Pr g hg s σ log
  change logSym F S h (memoryPermute s σ, []) = logSym F S h (s, [])
  exact logSym_memoryPermute F S h hh s σ []

/-- Fixed data with prescribed `q_d, A₀, η, ψ` (the bands and `K` remain free). -/
def PDFix.Has {K : ℕ} (F : PDFix K) (q_d A₀ : ℝ) (eta psi : ℝ → ℝ) : Prop :=
  F.q_d = q_d ∧ F.A₀ = A₀ ∧ F.eta = eta ∧ F.psi = psi


end

end ArtinPrimitiveRoots.TypeII.PD
