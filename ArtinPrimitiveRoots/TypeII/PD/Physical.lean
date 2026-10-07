import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PD.Determinant
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §1 Fixed data, moving scales, cutoffs -/

/-- The fixed cutoff `η` of the Cauchy decomposition (PD 03:90-95): smooth, nonnegative,
supported in `[1,4]`, a dyadic partition of unity. -/
def IsCauchyCutoff (eta : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) eta ∧ Function.support eta ⊆ Set.Icc 1 4 ∧ (∀ y, 0 ≤ eta y) ∧
    IsDyadicPartition eta

/-- The fixed cutoff `ψ` of the major-arc replacement (PD 03:153-154): smooth, compactly
supported, equal to one on `[-4,4]`. -/
def IsArcCutoff (psi : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧ HasCompactSupport psi ∧ ∀ t ∈ Set.Icc (-4 : ℝ) 4, psi t = 1

/-- Data fixed before `x → ∞` in PD §§3-4 (the number `K` of groups is the type index):
band exponents `a`, damping `q_d`, arc exponent `A₀`, cutoffs `η, ψ`. -/
structure PDFix (K : ℕ) where
  a : Fin K → ℝ
  q_d : ℝ
  A₀ : ℝ
  eta : ℝ → ℝ
  psi : ℝ → ℝ

/-- Validity of the fixed data (N4 and PD 03:7-35, 153-160). -/
def PDFix.Valid {K : ℕ} (F : PDFix K) : Prop :=
  ValidBands K F.a ∧ 0 < F.q_d ∧ F.q_d < 1 ∧ 0 < F.A₀ ∧ IsCauchyCutoff F.eta ∧
    IsArcCutoff F.psi

/-- Moving scales: `x`, the two Type II dyads `H_m, H_n`, the selected-product scale `Y`
(PD 03:90-95) and the pad dyad `d₀` (PD 03:179-185). -/
structure PDScale where
  x : ℝ
  Hm : ℝ
  Hn : ℝ
  Y : ℝ
  d₀ : ℕ

/-- Scale hypotheses (N6, PD 03:37-50, 93-94, 179-181) for fixed `δ, c₁, c₂`. -/
def PDScale.Valid (K : ℕ) (δ c₁ c₂ : ℝ) (S : PDScale) : Prop :=
  2 ≤ S.x ∧ Real.rpow S.x δ ≤ S.Hm ∧ Real.rpow S.x δ ≤ S.Hn ∧
    c₁ * S.x ≤ S.Hm * S.Hn ∧ S.Hm * S.Hn ≤ c₂ * S.x ∧
    S.Y ∈ dyadicScales S.x K ∧ S.d₀ ∈ padScales S.x K

/-- `L = log x`. -/
def PDScale.L (S : PDScale) : ℝ := Real.log S.x
/-- `H = d₀ Y` (PD 03:183). -/
def PDScale.H (S : PDScale) : ℝ := (S.d₀ : ℝ) * S.Y
/-- `U = H H_m` (PD 03:183). -/
def PDScale.U (S : PDScale) : ℝ := S.H * S.Hm
/-- `V = H_n` (PD 03:183). -/
def PDScale.V (S : PDScale) : ℝ := S.Hn
/-- `X = H_m H_n`. -/
def PDScale.X (S : PDScale) : ℝ := S.Hm * S.Hn
/-- Number of slots `M_J = J+1`. -/
def PDScale.M (S : PDScale) : ℕ := slotCount S.x
/-- Path length `N = 2R`. -/
def PDScale.N (S : PDScale) : ℕ := pathLength S.x
/-- `R`. -/
def PDScale.R (S : PDScale) : ℕ := momentR S.x

/-- The physical state type at given data (PD 03:187-190). -/
abbrev PState {K : ℕ} (F : PDFix K) (S : PDScale) :=
  PhysicalState S.x K F.a S.H S.Hm S.Hn

/-! ## §2 `def:pd-physical` — the physical determinant operator (PD 03:171-268) -/

/-- PD 03:199-202. Index `J` of the unshared slot (the last of the `M_J = J+1` slots). -/
def lastSlot (x : ℝ) : Fin (slotCount x) := ⟨momentJ x, Nat.lt_succ_self _⟩

/-- Product `D` of the copied (shared) slots `1,…,J` of every group. -/
def sharedProduct {x : ℝ} {K : ℕ} (p : PrimeLists x K) : ℕ :=
  ∏ i : Fin K, ∏ j : Fin (slotCount x), if j.val < momentJ x then p i j else 1

/-- Product of the last (unshared) slots: `b` at a source, `a` at a target. -/
def lastProduct {x : ℝ} {K : ℕ} (p : PrimeLists x K) : ℕ :=
  ∏ i : Fin K, p i (lastSlot x)

/-- PD 03:199-208. Slot rule of one edge from source lists `p` to target lists `q`: the shared
slots are copied, and the new target label of every group differs from every source label in every
group (the cross-edge ban; together with distinctness within lists this makes all unshared labels
distinct from one another and from all shared labels). -/
def IsSlotTransition {x : ℝ} {K : ℕ} (p q : PrimeLists x K) : Prop :=
  (∀ i j, j.val < momentJ x → q i j = p i j) ∧
    ∀ (i i' : Fin K) (j : Fin (slotCount x)), q i (lastSlot x) ≠ p i' j

/-- Pad dyad and integrality: `D ∈ [d₀,2d₀)` and `D ∣ det` (PD 03:208-209). -/
def IsPadAdmissible (d₀ : ℕ) (D : ℕ) (det : ℤ) : Prop :=
  (d₀ : ℝ) ≤ (D : ℝ) ∧ (D : ℝ) < 2 * (d₀ : ℝ) ∧ (D : ℤ) ∣ det

/-- Permutation of the slots of each group (PD 03:196-197). -/
def permuteLists {x : ℝ} {K : ℕ} (σ : Fin K → Equiv.Perm (Fin (slotCount x)))
    (p : PrimeLists x K) : PrimeLists x K :=
  fun i j => p i (σ i j)

/-- Raw part of the multiplier of (eq:det-kernel), PD 03:210-219, without damping:
`(d₀/D) η(b/Y) η(a/Y) ψ(t/Y) 1_{t=b-a}`. -/
def rawMultiplier {K : ℕ} (F : PDFix K) (S : PDScale) (D aa bb : ℕ) (t : ℤ) : ℂ :=
  (((S.d₀ : ℝ) / (D : ℝ) : ℝ) : ℂ) * (F.eta ((bb : ℝ) / S.Y) : ℂ) *
    (F.eta ((aa : ℝ) / S.Y) : ℂ) *
      (if t = (bb : ℤ) - aa then (F.psi ((t : ℝ) / S.Y) : ℂ) else 0)

/-- Comparison (major-arc) part of the multiplier of (eq:det-kernel):
`(d₀/D) η(b/Y) η(a/Y) ψ(t/Y) ∫_𝔐 e(θ(t-b+a)) dθ` (`majorKernel` contains `ψ(t/Y)`). -/
def comparisonMultiplier {K : ℕ} (F : PDFix K) (S : PDScale) (D aa bb : ℕ) (t : ℤ) : ℂ :=
  (((S.d₀ : ℝ) / (D : ℝ) : ℝ) : ℂ) * (F.eta ((bb : ℝ) / S.Y) : ℂ) *
    (F.eta ((aa : ℝ) / S.Y) : ℂ) * majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi

/-- The full geometric multiplier, raw minus comparison. -/
def geometricMultiplier {K : ℕ} (F : PDFix K) (S : PDScale) (D aa bb : ℕ) (t : ℤ) : ℂ :=
  rawMultiplier F S D aa bb t - comparisonMultiplier F S D aa bb t

/-- The determinant of two integer vectors. -/
def det2 (z w : ℤ × ℤ) : ℤ := z.1 * w.2 - z.2 * w.1

/-- PD 03:199-219. The undamped edge kernel from source lists `p` to target lists `q`, at
determinant `dt = det(P,Q)` (in position coordinates): slot rule, pad dyad, the new-slot weights
`∏_i V_i^{-1}`, and the geometric multiplier with `D = sharedProduct p`, `b = lastProduct p`,
`a = lastProduct q`, `t = dt / D`. -/
def slotKernel {K : ℕ} (F : PDFix K) (S : PDScale) (p q : PrimeLists S.x K) (dt : ℤ) : ℂ :=
  if IsSlotTransition p q ∧ IsPadAdmissible S.d₀ (sharedProduct p) dt then
    ((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ) : ℂ) *
      geometricMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
        (dt / (sharedProduct p : ℤ))
  else 0

/-- The damping half-factor `q_d^{(ω(P₁) - K M_J)/2}` of (eq:det-kernel), with `ω` the number of
group primes dividing `P₁` (PD 03:22-24 `ω = Σ ω_i`). -/
def dampingHalf {K : ℕ} (F : PDFix K) (S : PDScale) (n : ℕ) : ℝ :=
  Real.rpow F.q_d (((markedOmega S.x K F.a n - K * slotCount S.x : ℕ) : ℝ) / 2)

/-- Permuting the lists of a physical state (PD 03:196-197). -/
def PhysicalState.permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (P : PhysicalState x K a H' Hm Hn) :
    PhysicalState x K a H' Hm Hn :=
  { P with
    labels := fun i j => P.labels i (σ i j)
    label_prime := fun i j => P.label_prime i (σ i j)
    label_in_band := fun i j => P.label_in_band i (σ i j)
    label_divides := fun i j => P.label_divides i (σ i j)
    label_distinct := fun i j j' h => P.label_distinct i (σ i j) (σ i j') ((σ i).injective.ne h) }

/-- Position of a physical state as an integer vector. -/
def PhysicalState.pos {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : ℤ × ℤ := ((P.first : ℤ), (P.second : ℤ))

/-- PD 03:199-219. The row kernel `𝒯(P,Q)`: undamped slot kernel at `det(P,Q)` times the two
damping half-factors. -/
def physRowKernel {K : ℕ} (F : PDFix K) (S : PDScale) (P Q : PState F S) : ℂ :=
  slotKernel F S P.labels Q.labels (det2 P.pos Q.pos) *
    ((dampingHalf F S P.first * dampingHalf F S Q.first : ℝ) : ℂ)

/-- Number of slot-permutation tuples, `(M_J!)^K`. -/
def permCount (x : ℝ) (K : ℕ) : ℕ := Fintype.card (Fin K → Equiv.Perm (Fin (slotCount x)))

/-- Slot symmetrization `𝒮` (PD 03:196-197): average over permutations of each list. -/
def physSym {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => ((permCount S.x K : ℂ))⁻¹ *
    ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (P.permute σ)

/-- Row operation `𝒯` (PD 03:199-220): `(𝒯f)(P) = Σ_Q 𝒯(P,Q) f(Q)`; target positions with
counting measure, the new-slot weights `V_i^{-1}` are inside the kernel. -/
def physRow {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => ∑' Q : PState F S, physRowKernel F S P Q * f Q

/-- Adjoint of `𝒯` for the (constant) state measure: kernel `conj 𝒯(Q,P)` (PD 03:221-225). -/
def physRowAdj {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => ∑' Q : PState F S, star (physRowKernel F S Q P) * f Q

/-- The good-state projection `𝒢` (PD 03:238-268): multiplication by the indicator that the
position with its lists passes tests (i) and (ii) at the ratio `r_P`. -/
def physGood {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) then f P else 0

/-- `𝒜 = 𝒢𝒮𝒯𝒮𝒢` (PD 03:261-263). -/
def detOp {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  physGood F S (physSym F S (physRow F S (physSym F S (physGood F S f))))

/-- `𝒜* = 𝒢𝒮𝒯*𝒮𝒢`. -/
def detOpAdj {K : ℕ} (F : PDFix K) (S : PDScale) (f : PState F S → ℂ) : PState F S → ℂ :=
  physGood F S (physSym F S (physRowAdj F S (physSym F S (physGood F S f))))

/-- Weighted inner product on `ℋ` with measure `∏_i V_i^{-M_J}` times counting (PD 03:191-195). -/
def physInner {K : ℕ} (F : PDFix K) (S : PDScale) (f g : PState F S → ℂ) : ℂ :=
  (physicalMeasure S.x K F.a : ℂ) * ∑' P : PState F S, star (f P) * g P

/-- The vector `𝐮_P`: one on every list at position `(u,v)`, zero elsewhere (PD 03:345-347). -/
def positionVector {K : ℕ} (F : PDFix K) (S : PDScale) (u v : ℕ) : PState F S → ℂ :=
  fun P => if P.first = u ∧ P.second = v then 1 else 0

/-- Primitive positions of `Ω = [U,16U] × [V,2V]`. -/
def IsOmegaPosition (S : PDScale) (u v : ℕ) : Prop :=
  Nat.Coprime u v ∧ S.U ≤ (u : ℝ) ∧ (u : ℝ) ≤ 16 * S.U ∧ S.V ≤ (v : ℝ) ∧ (v : ℝ) ≤ 2 * S.V

/-- The determinant moment (eq:det-moment), PD 03:349-354:
`(1/UV) Σ_{P∈Ω primitive} ⟨𝐮_P, (𝒜𝒜*)^R 𝐮_P⟩` (real part; the summand is real). -/
def detMoment {K : ℕ} (F : PDFix K) (S : PDScale) : ℝ :=
  (S.U * S.V)⁻¹ * ∑' uv : ℕ × ℕ,
    if IsOmegaPosition S uv.1 uv.2 then
      (physInner F S (positionVector F S uv.1 uv.2)
        ((fun f => detOp F S (detOpAdj F S f))^[S.R] (positionVector F S uv.1 uv.2))).re
    else 0

/-- The endpoint pairing `⟨f, 𝒜 g⟩` of PD 03:357-361.  The frozen `endpointF` is the paper's `f̄`
(PD 03:300), so it enters without conjugation. -/
def detPairing {K : ℕ} (F : PDFix K) (S : PDScale) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) : ℂ :=
  (physicalMeasure S.x K F.a : ℂ) *
    ∑' P : PState F S,
      endpointF S.x K F.a family beta P *
        detOp F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) P

/-- The same pairing without the good-state projections, `⟨f, 𝒮𝒯𝒮 g⟩` (PD 04:970-1009). -/
def detPairingNoGood {K : ℕ} (F : PDFix K) (S : PDScale) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) : ℂ :=
  (physicalMeasure S.x K F.a : ℂ) *
    ∑' P : PState F S,
      endpointF S.x K F.a family beta P *
        physSym F S (physRow F S (physSym F S
          (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta))) P

/-- Coefficient hypotheses on `β` used throughout (PD 03:48-50). -/
def IsSecondCoefficient (S : PDScale) (C : ℝ) (beta : ℕ → ℂ) : Prop :=
  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers S.Hn ∧ roughAbove n (roughCutoff S.x)) ∧
    ∀ n ∈ dyadicIntegers S.Hn, ‖beta n‖ ≤ Real.rpow (Real.log S.x) C

/-- A coefficient family is at scale `S` when its dyads are those of `S`. -/
def FamilyAtScale {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂)
    (S : PDScale) : Prop :=
  family.Hm S.x = S.Hm ∧ family.Hn S.x = S.Hn

/-- `t2:pd.moment-to-pairing` — PD 03:343-411.  REPLACES the frozen `moment_to_pairing`
(whose `∃ Cpair` stood after all data and was vacuous).  `C_e` is the exponent of
`endpoint_bounds`; `Cpair` depends only on the fixed data.
Proof sketch: partition positions into slope intervals of length `H/U²`; an edge with nonzero
kernel has `|det| ≪ H` and joins boundedly many neighbouring intervals; each interval has `O(H)`
primitive positions (fix a pivot, the determinant with it is `O(H)`, solutions differ by
multiples of the pivot).  PSD trace bound (03:380-389), spectral Hölder for `B₀ = 𝒜𝒜*`,
Hölder in the intervals with exponents `2, 2R/(R-1), 2R`, and `H^{1/N} = O(1)` (`log H ≪ L^{0.21}`). -/
theorem moment_to_pairing (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ ≤ c₂) :
    ∃ C_e : ℝ, 0 < C_e ∧
      ∀ (K : ℕ) (F : PDFix K), F.Valid →
        ∃ Cpair x₀ : ℝ, 0 < Cpair ∧ 2 ≤ x₀ ∧
          ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ family : CoefficientFamily δ C c₁ c₂, FamilyAtScale family S →
              family.xMin ≤ S.x →
              ∀ beta : ℕ → ℂ, IsSecondCoefficient S C beta →
                ∀ E₀ : ℝ, 0 < E₀ →
                  detMoment F S ≤ Real.rpow S.L (-E₀ * (S.N : ℝ)) →
                    ‖detPairing F S family beta‖ ≤
                      Cpair * S.U * S.V * Real.rpow S.L (-E₀ + C_e) := by
  sorry


end

end ArtinPrimitiveRoots.TypeII.PD
