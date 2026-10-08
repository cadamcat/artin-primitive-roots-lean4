import ArtinPrimitiveRoots.Proofs.pd_life_b.FiniteHistoryValidity
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs

set_option autoImplicit false

/-!
Route of lane `pd-birth-opus` for `pd_ordered_birth_bijection`.

Instead of reindexing complete traces by lifespans, fix one lifespan assignment `H` and sum
only the traces *guided* by `H`: at every ghost the deleted and born primes are exactly the
`H`-endpoints at that visit, and at every edge the store bit of the leaving prime is the
`H`-pending status at the next visit. The guided sum is computed by induction along the
suffix recursion of `FiniteHistoryTrace`, one step at a time, with per-prime local factors.
-/

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

noncomputable section

/-- The anchor line of a lifespan: the common active line, or the ghost-birth line. -/
def lifeLine {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1))) :
    Fin (p + 1) :=
  if hA : (pdLifeActive S γ p).Nonempty then
    projLine p (γ ((pdLifeActive S γ p).min' hA)).1
  else match e.1 with
    | some a => projLine p (γ a).1
    | none => 0

/-- The external position at visit `j` hits the anchor line of the lifespan. -/
def lifeHit {K : ℕ} (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (e : Option (Fin (pathLength S.x + 1)) × Option (Fin (pathLength S.x + 1)))
    (j : Fin (pathLength S.x + 1)) : Prop :=
  projLine p (γ j).1 = lifeLine S γ p e

/-- Factor of one prime at the ghost of visit `j`: survival or deletion of its pending particle,
and its ghost birth. -/
def lifeGhostLocal {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (j : Fin (pathLength S.x + 1)) : ℝ :=
  (if pdLifePending S γ p e false j ∧ lifeHit S γ p e.1 j then
      (if e.1.2 = some j then -memoryEta S.x F.q_d j.val / ρ
        else memoryQ S.x F.q_d j.val / ρ ^ 2)
    else 1) *
  (if e.1.1 = some j then
      -memoryEta S.x F.q_d j.val * bandMass S.x (F.a i) / ρ *
        memoryNu S.x K F.a F.q_d i p
    else 1)

/-- Factor of one prime at edge `j` (from visit `j` to `j+1`): source hit, entry by promotion
or fresh birth, and target hit. -/
def lifeEdgeLocal {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) (e : PrimeLife S γ p)
    (j : Fin (pathLength S.x)) : ℝ :=
  (if pdLifePending S γ p e true j.castSucc ∧ lifeHit S γ p e.1 j.castSucc then ρ else 1) *
  (if IsActiveAt γ p j.succ ∧ ¬ IsActiveAt γ p j.castSucc then
      (if pdLifePending S γ p e true j.castSucc then (bandMass S.x (F.a i))⁻¹
        else memoryNu S.x K F.a F.q_d i p)
    else 1) *
  (if pdLifePending S γ p e false j.succ ∧ lifeHit S γ p e.1 j.succ then ρ else 1)

/-- Initial active measure of one prime. -/
def lifeInitLocal {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (i : Fin K) (p : ℕ) : ℝ :=
  if IsActiveAt γ p 0 then memoryNu S.x K F.a F.q_d i p else 1

/-- `p` belongs to group `i` and its `H`-lifespan is pending at visit `j`. -/
def lifePendingIn {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (p : ℕ) (afterGhost : Bool)
    (j : Fin (pathLength S.x + 1)) : Prop :=
  ∃ hp : p ∈ primeBand S.x (F.a i), pdLifePending S γ p (H i ⟨p, hp⟩) afterGhost j

/-- `p` belongs to group `i` and its `H`-lifespan has its ghost deletion at visit `j`. -/
def lifeDeletedAt {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (p : ℕ)
    (j : Fin (pathLength S.x + 1)) : Prop :=
  ∃ hp : p ∈ primeBand S.x (F.a i), (H i ⟨p, hp⟩).1.2 = some j

/-- `p` belongs to group `i` and its `H`-lifespan has its ghost birth at visit `j`. -/
def lifeBornAt {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (i : Fin K) (p : ℕ)
    (j : Fin (pathLength S.x + 1)) : Prop :=
  ∃ hp : p ∈ primeBand S.x (F.a i), (H i ⟨p, hp⟩).1.1 = some j

/-- `p` was born (logged) before the ghost of visit `j`: active at some earlier-or-equal visit,
or ghost-born strictly earlier. -/
def lifeBornBefore {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (p : ℕ) (j : Fin (pathLength S.x + 1)) : Prop :=
  (∃ j' : Fin (pathLength S.x + 1), j' ≤ j ∧ IsActiveAt γ p j') ∨
    ∃ i : Fin K, ∃ a : Fin (pathLength S.x + 1), a < j ∧ lifeBornAt F S γ H i p a

/-- The ghost choice at visit `j` prescribed by `H`. -/
def GhostGuided {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1))
    (σ : LogPoint S.x K) (g : GhostTraceChoice F S σ) : Prop :=
  ∀ i : Fin K,
    g.1 i = Finset.univ.filter (fun r => lifeDeletedAt F S γ H i ((σ.1.2.2 i).get r).1 j) ∧
    (g.2 i).1 = (primeBand S.x (F.a i)).filter (fun p => lifeBornAt F S γ H i p j)

/-- The store bits at edge `j` prescribed by `H`: the prime in the permuted source last slot is
stored exactly when its lifespan is pending before the next ghost. -/
def EdgeGuided {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x))
    (σ : LogPoint S.x K) (e : EdgeTraceChoice F S σ) : Prop :=
  ∀ i : Fin K,
    (e.2.1 i).1 = decide (lifePendingIn F S γ H i
      ((permuteLogPoint e.1 σ).1.2.1 i (lastSlot S.x)) false j.succ)

/-- A trace guided by `H` at every ghost and every edge. -/
def TraceGuided {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) :
    (k : ℕ) → (σ : LogPoint S.x K) → FiniteHistoryTrace F S γ k σ → Prop
  | 0, σ, t => GhostGuided F S γ H (Fin.last (pathLength S.x)) σ t
  | k + 1, σ, t =>
      let j := pathLength S.x - (k + 1)
      let τ := ghostTraceOutput F S j σ t.1
      let z' := (γ ⟨pathLength S.x - k,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩).1
      let υ := edgeTraceOutput F S j z' τ t.2.1
      GhostGuided F S γ H ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ σ t.1 ∧
        (∀ hj : j < pathLength S.x, EdgeGuided F S γ H ⟨j, hj⟩ τ t.2.1) ∧
        TraceGuided F S γ H k υ t.2.2

/-- The logged state at visit `j` (before its ghost) determined by `H`: external point,
pending particles with their anchors, and the born primes, each without repetition. -/
def IsLifeState {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (H : PDLifeAssignment F S γ) (j : Fin (pathLength S.x + 1))
    (σ : LogPoint S.x K) : Prop :=
  (σ.1.1, σ.1.2.1) = γ j ∧
    (∀ i, ((σ.1.2.2 i).map Prod.fst).Nodup) ∧
    (∀ i (q : Particle), q ∈ σ.1.2.2 i ↔
      ∃ hp : q.1 ∈ primeBand S.x (F.a i),
        pdLifePending S γ q.1 (H i ⟨q.1, hp⟩) false j ∧
          q.2 = (lifeLine S γ q.1 (H i ⟨q.1, hp⟩).1).val) ∧
    (σ.2.map Prod.snd).Nodup ∧
    ∀ p, p ∈ σ.2.map Prod.snd ↔ lifeBornBefore F S γ H p j

/-- The sum of the literal weights of the traces guided by `H`. -/
def guidedTraceSum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (B : Option ℕ) (γ : EnvPath S.x K) (H : PDLifeAssignment F S γ)
    (k : ℕ) (σ : LogPoint S.x K) : ℂ :=
  ∑ t : FiniteHistoryTrace F S γ k σ,
    if TraceGuided F S γ H k σ t then finiteHistoryTraceWeight F S ρ w B γ k σ t else 0

/-- The geometric part of edge `j`: both slot symmetrizations, the memory-free admissibility
tests, and the signed raw-minus-comparison multiplier, between the external visits. -/
def edgeGeo {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot)
    (γ : EnvPath S.x K) (j : Fin (pathLength S.x)) : ℂ :=
  ((permCount S.x K : ℂ)⁻¹) ^ 2 *
    ∑ π : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      ∑ π' : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        let P := permuteLists π (γ j.castSucc).2
        let Q := permuteLists (fun i => (π' i)⁻¹) (γ j.succ).2
        let z := (γ j.castSucc).1
        let z' := (γ j.succ).1
        if ValidPrimeLists S.x K F.a P ∧ ValidPrimeLists S.x K F.a Q ∧
            IsSlotTransition P Q ∧ IsPadAdmissible S.d₀ (sharedProduct P) (det2 z z') ∧
            Int.gcd z'.1 z'.2 = 1 ∧ envBox S w z ∧ envBox S w z' ∧
            envGood F S w (z, P) ∧ envGood F S w (z', Q) then
          edgeMultiplier F S (decide (j.val % 2 = 0)) true P Q z z' -
            edgeMultiplier F S (decide (j.val % 2 = 0)) false P Q z z'
        else 0

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
