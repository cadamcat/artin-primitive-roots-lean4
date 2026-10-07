import ArtinPrimitiveRoots.TypeII.PD.Defs
import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.PositiveOperator
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.PositionGeometry
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.EndpointPosition
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

lemma pd1c_permute_mul {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn)
    (σ τ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    (P.permute σ).permute τ = P.permute (σ * τ) := by
  rfl

lemma pd1c_permute_one {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) : P.permute 1 = P := by
  cases P
  rfl

noncomputable def pd1c_permuteEquiv {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : PState F S ≃ PState F S where
  toFun P := P.permute σ
  invFun P := P.permute σ⁻¹
  left_inv P := by
    change (P.permute σ).permute σ⁻¹ = P
    rw [pd1c_permute_mul, mul_inv_cancel, pd1c_permute_one]
  right_inv P := by
    change (P.permute σ⁻¹).permute σ = P
    rw [pd1c_permute_mul, inv_mul_cancel, pd1c_permute_one]

lemma pd1c_physSym_invariant {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) (P : PState F S)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    physSym F S f (P.permute σ) = physSym F S f P := by
  unfold physSym
  congr 1
  simp only [pd1c_permute_mul]
  apply Fintype.sum_equiv (Equiv.mulLeft σ)
  intro τ
  rfl

lemma pd1c_physSym_idempotent {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : physSym F S (physSym F S f) = physSym F S f := by
  funext P
  change (permCount S.x K : ℂ)⁻¹ *
    (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      physSym F S f (P.permute σ)) = physSym F S f P
  simp only [pd1c_physSym_invariant]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (permCount S.x K : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 <
      Fintype.card (Fin K → Equiv.Perm (Fin (slotCount S.x)))))
  change (permCount S.x K : ℂ)⁻¹ *
    ((permCount S.x K : ℂ) * physSym F S f P) = _
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma pd1c_physSym_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (physSym F S g) = physInner F S (physSym F S f) g := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  have hreindex : (∑ P : PState F S, ∑ σ : G, star (f P) * g (P.permute σ)) =
      ∑ P : PState F S, ∑ σ : G, star (f (P.permute σ)) * g P := by
    rw [Finset.sum_comm, Finset.sum_comm (f := fun P σ => star (f (P.permute σ)) * g P)]
    calc
      _ = ∑ σ : G, ∑ P : PState F S, star (f (P.permute σ⁻¹)) * g P := by
        apply Finset.sum_congr rfl
        intro σ hσ
        apply Fintype.sum_equiv (pd1c_permuteEquiv F S σ)
        intro P
        simp only [pd1c_permuteEquiv, Equiv.coe_fn_mk, pd1c_permute_mul,
          mul_inv_cancel, pd1c_permute_one]
      _ = _ := by
        apply Fintype.sum_equiv (Equiv.inv G)
        intro σ
        simp
  unfold physInner
  apply congrArg (fun z : ℂ => (physicalMeasure S.x K F.a : ℂ) * z)
  have hnstar : star (permCount S.x K : ℂ) = (permCount S.x K : ℂ) := by
    simp [Complex.star_def]
  unfold physSym
  simp only [tsum_fintype, star_mul, star_sum, star_inv₀, hnstar]
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = (permCount S.x K : ℂ)⁻¹ *
        (∑ P : PState F S, ∑ σ : G, star (f P) * g (P.permute σ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = (permCount S.x K : ℂ)⁻¹ *
        (∑ P : PState F S, ∑ σ : G, star (f (P.permute σ)) * g P) := by rw [hreindex]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

lemma pd1c_physRow_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (physRow F S g) = physInner F S (physRowAdj F S f) g := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  unfold physInner
  apply congrArg (fun z : ℂ => (physicalMeasure S.x K F.a : ℂ) * z)
  unfold physRow physRowAdj
  simp only [tsum_fintype, star_sum, star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

lemma pd1c_physGood_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (physGood F S g) = physInner F S (physGood F S f) g := by
  unfold physInner physGood
  congr 1
  apply tsum_congr
  intro P
  split_ifs <;> simp

lemma pd1c_physGood_idempotent {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : physGood F S (physGood F S f) = physGood F S f := by
  funext P
  unfold physGood
  split_ifs <;> rfl

lemma pd1c_detOp_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (detOp F S g) = physInner F S (detOpAdj F S f) g := by
  unfold detOp detOpAdj
  rw [pd1c_physGood_adjoint, pd1c_physSym_adjoint, pd1c_physRow_adjoint,
    pd1c_physSym_adjoint, pd1c_physGood_adjoint]

lemma pd1c_physicalMeasure_nonneg (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :
    0 ≤ physicalMeasure x K a := by
  unfold physicalMeasure
  apply Finset.prod_nonneg
  intro i hi
  apply Real.rpow_nonneg
  unfold bandMass
  exact Finset.sum_nonneg fun p hp => by positivity

lemma pd1c_physInner_self {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    (physInner F S f f).re = physicalNormSq S.x K F.a f := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  unfold physInner physicalNormSq
  simp only [tsum_fintype, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.star_def, Complex.mul_re, Complex.normSq_apply]

lemma pd1c_physInner_self_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : 0 ≤ (physInner F S f f).re := by
  rw [pd1c_physInner_self]
  unfold physicalNormSq
  apply mul_nonneg (pd1c_physicalMeasure_nonneg _ _ _)
  exact tsum_nonneg fun P => sq_nonneg _

lemma pd1c_physInner_conj {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : star (physInner F S f g) = physInner F S g f := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  unfold physInner
  simp only [tsum_fintype, star_mul, star_sum, star_star]
  rw [show star ((physicalMeasure S.x K F.a : ℝ) : ℂ) =
      (physicalMeasure S.x K F.a : ℂ) by simp [Complex.star_def]]
  rw [mul_comm]

lemma pd1c_detOpAdj_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (detOpAdj F S g) = physInner F S (detOp F S f) g := by
  have h := congrArg star (pd1c_detOp_adjoint F S g f)
  simpa only [pd1c_physInner_conj] using h.symm

lemma pd1c_positiveOperator_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    physInner F S f (detOp F S (detOpAdj F S g)) =
      physInner F S (detOp F S (detOpAdj F S f)) g := by
  rw [pd1c_detOp_adjoint, pd1c_detOpAdj_adjoint]

lemma pd1c_positiveOperator_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    0 ≤ (physInner F S f (detOp F S (detOpAdj F S f))).re := by
  rw [pd1c_detOp_adjoint]
  exact pd1c_physInner_self_nonneg F S _

lemma pd1c_positiveOperator_iterate_adjoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (n : ℕ) (f g : PState F S → ℂ) :
    physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[n] g) =
      physInner F S ((fun h => detOp F S (detOpAdj F S h))^[n] f) g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', pd1c_positiveOperator_adjoint, ih,
        ← Function.iterate_succ_apply]

lemma pd1c_positiveOperator_iterate_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (n : ℕ) (f : PState F S → ℂ) :
    0 ≤ (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[n] f)).re := by
  have hsplit : n = n / 2 + n / 2 + n % 2 := by omega
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have hn : n = n / 2 + n / 2 := by omega
    rw [hn, Function.iterate_add_apply, pd1c_positiveOperator_iterate_adjoint]
    exact pd1c_physInner_self_nonneg F S _
  · have hn : n = n / 2 + (n / 2 + 1) := by omega
    rw [hn, Function.iterate_add_apply, pd1c_positiveOperator_iterate_adjoint,
      Function.iterate_succ_apply']
    exact pd1c_positiveOperator_nonneg F S _

lemma pd1c_detMoment_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (hUV : 0 ≤ S.U * S.V) : 0 ≤ detMoment F S := by
  unfold detMoment
  apply mul_nonneg (inv_nonneg.mpr hUV)
  apply tsum_nonneg
  intro uv
  split_ifs
  · exact pd1c_positiveOperator_iterate_nonneg F S _ _
  · rfl

lemma pd1c_physGood_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : physGood F S (f + g) = physGood F S f + physGood F S g := by
  funext P
  unfold physGood
  split_ifs <;> simp_all

lemma pd1c_physGood_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : physGood F S (c • f) = c • physGood F S f := by
  funext P
  unfold physGood
  split_ifs <;> simp_all

lemma pd1c_physSym_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : physSym F S (f + g) = physSym F S f + physSym F S g := by
  funext P
  simp [physSym, Finset.sum_add_distrib, mul_add]

lemma pd1c_physSym_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : physSym F S (c • f) = c • physSym F S f := by
  funext P
  simp only [physSym, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma pd1c_physRow_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : physRow F S (f + g) = physRow F S f + physRow F S g := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  funext P
  simp [physRow, tsum_fintype, Finset.sum_add_distrib, mul_add]

lemma pd1c_physRow_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : physRow F S (c • f) = c • physRow F S f := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  funext P
  simp only [physRow, tsum_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

lemma pd1c_physRowAdj_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : physRowAdj F S (f + g) = physRowAdj F S f + physRowAdj F S g := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  funext P
  simp [physRowAdj, tsum_fintype, Finset.sum_add_distrib, mul_add]

lemma pd1c_physRowAdj_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : physRowAdj F S (c • f) = c • physRowAdj F S f := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  funext P
  simp only [physRowAdj, tsum_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  ring

lemma pd1c_detOp_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : detOp F S (f + g) = detOp F S f + detOp F S g := by
  simp only [detOp, pd1c_physGood_add, pd1c_physSym_add, pd1c_physRow_add]

lemma pd1c_detOp_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : detOp F S (c • f) = c • detOp F S f := by
  simp only [detOp, pd1c_physGood_smul, pd1c_physSym_smul, pd1c_physRow_smul]

lemma pd1c_detOpAdj_add {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) : detOpAdj F S (f + g) = detOpAdj F S f + detOpAdj F S g := by
  simp only [detOpAdj, pd1c_physGood_add, pd1c_physSym_add, pd1c_physRowAdj_add]

lemma pd1c_detOpAdj_smul {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℂ) (f : PState F S → ℂ) : detOpAdj F S (c • f) = c • detOpAdj F S f := by
  simp only [detOpAdj, pd1c_physGood_smul, pd1c_physSym_smul, pd1c_physRowAdj_smul]

noncomputable def pd1c_detLinearMap {K : ℕ} (F : PDFix K) (S : PDScale) :
    (PState F S → ℂ) →ₗ[ℂ] (PState F S → ℂ) where
  toFun := detOp F S
  map_add' := pd1c_detOp_add F S
  map_smul' := pd1c_detOp_smul F S

noncomputable def pd1c_detAdjLinearMap {K : ℕ} (F : PDFix K) (S : PDScale) :
    (PState F S → ℂ) →ₗ[ℂ] (PState F S → ℂ) where
  toFun := detOpAdj F S
  map_add' := pd1c_detOpAdj_add F S
  map_smul' := pd1c_detOpAdj_smul F S

lemma pd1c_physInner_euclidean {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (x y : EuclideanSpace ℂ (PState F S)) :
    physInner F S (WithLp.ofLp x) (WithLp.ofLp y) =
      (physicalMeasure S.x K F.a : ℂ) * inner ℂ x y := by
  unfold physInner
  rw [tsum_fintype, EuclideanSpace.inner_eq_star_dotProduct]
  apply congrArg (fun z : ℂ => (physicalMeasure S.x K F.a : ℂ) * z)
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro P hP
  simp only [Pi.star_apply]
  ring

lemma pd1c_physical_spectral_power_mean {K : ℕ} (F : PDFix K) (S : PDScale)
    (R : ℕ) (hR : 1 ≤ R) (f : PState F S → ℂ) :
    (physInner F S f (detOp F S (detOpAdj F S f))).re ^ R ≤
      (physicalNormSq S.x K F.a f) ^ (R - 1) *
        (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[R] f)).re := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  let w := physicalMeasure S.x K F.a
  by_cases hw : w = 0
  · simp [physInner, physicalNormSq, show physicalMeasure S.x K F.a = 0 from hw,
      Nat.ne_of_gt (by omega : 0 < R)]
  have hwpos : 0 < w := lt_of_le_of_ne (pd1c_physicalMeasure_nonneg _ _ _) (Ne.symm hw)
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  let e : EuclideanSpace ℂ (PState F S) ≃ₗ[ℂ] (PState F S → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : PState F S => ℂ)).toLinearEquiv
  let B := (pd1c_detLinearMap F S).comp (pd1c_detAdjLinearMap F S)
  let T : EuclideanSpace ℂ (PState F S) →ₗ[ℂ] EuclideanSpace ℂ (PState F S) :=
    e.symm.toLinearMap.comp (B.comp e.toLinearMap)
  have happly (x : EuclideanSpace ℂ (PState F S)) : e (T x) = B (e x) := by
    change e (e.symm (B (e x))) = B (e x)
    exact e.apply_symm_apply _
  have hBridge (x y : EuclideanSpace ℂ (PState F S)) :
      physInner F S (e x) (e y) = (w : ℂ) * inner ℂ x y := by
    change physInner F S (WithLp.ofLp x) (WithLp.ofLp y) = _
    exact pd1c_physInner_euclidean F S x y
  have hSym : T.IsSymmetric := by
    intro x y
    have h := pd1c_positiveOperator_adjoint F S (e x) (e y)
    change physInner F S (e x) (B (e y)) = physInner F S (B (e x)) (e y) at h
    rw [← happly y, ← happly x, hBridge, hBridge] at h
    exact (mul_left_cancel₀ hwC h).symm
  have hNonneg : ∀ x : EuclideanSpace ℂ (PState F S), 0 ≤ (inner ℂ x (T x)).re := by
    intro x
    have h := pd1c_positiveOperator_nonneg F S (e x)
    change 0 ≤ (physInner F S (e x) (B (e x))).re at h
    rw [← happly x, hBridge, Complex.re_ofReal_mul] at h
    exact (mul_nonneg_iff_of_pos_left hwpos).mp h
  have hpow (n : ℕ) (x : EuclideanSpace ℂ (PState F S)) :
      e ((T ^ n) x) = (B : (PState F S → ℂ) → (PState F S → ℂ))^[n] (e x) := by
    induction n generalizing x with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, ih, happly, Function.iterate_succ_apply]
  let x := e.symm f
  have hfx : e x = f := e.apply_symm_apply f
  have hFirst : (physInner F S f (B f)).re = w * (inner ℂ x (T x)).re := by
    have h := congrArg Complex.re (hBridge x (T x))
    simpa only [happly, hfx, Complex.re_ofReal_mul] using h
  have hLast : (physInner F S f
      ((B : (PState F S → ℂ) → (PState F S → ℂ))^[R] f)).re =
        w * (inner ℂ x ((T ^ R) x)).re := by
    have h := congrArg Complex.re (hBridge x ((T ^ R) x))
    simpa only [hpow, hfx, Complex.re_ofReal_mul] using h
  have hNorm : physicalNormSq S.x K F.a f = w * ‖x‖ ^ 2 := by
    have h := congrArg Complex.re (hBridge x x)
    have hSelf : (inner ℂ x x).re = ‖x‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    simpa only [hfx, pd1c_physInner_self, Complex.re_ofReal_mul, hSelf] using h
  have hmean := pd1c_spectral_power_mean T hSym hNonneg R hR x
  have hmul := mul_le_mul_of_nonneg_left hmean (pow_nonneg hwpos.le R)
  have hLeft : w ^ R * (inner ℂ x (T x)).re ^ R =
      (w * (inner ℂ x (T x)).re) ^ R := (mul_pow _ _ _).symm
  have hwPow : w ^ R = w ^ (R - 1) * w := by
    calc
      w ^ R = w ^ ((R - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ _ _
  have hRight : w ^ R * ((‖x‖ ^ 2) ^ (R - 1) * (inner ℂ x ((T ^ R) x)).re) =
      (w * ‖x‖ ^ 2) ^ (R - 1) * (w * (inner ℂ x ((T ^ R) x)).re) := by
    rw [hwPow, mul_pow]
    ring
  rw [hLeft, hRight, ← hFirst, ← hNorm, ← hLast] at hmul
  exact hmul

lemma pd1c_physical_spectral_power_inner_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (R : ℕ) (hR : 1 ≤ R) (f : PState F S → ℂ) :
    (physInner F S f (detOp F S (detOpAdj F S f))).re ≤
      Real.rpow (physicalNormSq S.x K F.a f) (1 - 1 / (R : ℝ)) *
        Real.rpow
          (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[R] f)).re
          (1 / (R : ℝ)) := by
  apply pd1c_power_bound_to_rpow
  · exact pd1c_positiveOperator_nonneg F S f
  · rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S f
  · exact pd1c_positiveOperator_iterate_nonneg F S R f
  · exact hR
  · exact pd1c_physical_spectral_power_mean F S R hR f

lemma pd1c_physicalNormSq_euclidean {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (x : EuclideanSpace ℂ (PState F S)) :
    physicalNormSq S.x K F.a (WithLp.ofLp x) = physicalMeasure S.x K F.a * ‖x‖ ^ 2 := by
  have h := congrArg Complex.re (pd1c_physInner_euclidean F S x x)
  have hSelf : (inner ℂ x x).re = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [pd1c_physInner_self, Complex.re_ofReal_mul, hSelf] using h

lemma pd1c_physicalNormSq_sum_bound {ι : Type*} {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : Finset ι) (c : ι → ℂ) (u : ι → PState F S → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i ∈ s, ‖c i‖ ≤ M) :
    physicalNormSq S.x K F.a (∑ i ∈ s, c i • u i) ≤
      (s.card : ℝ) * M ^ 2 * ∑ i ∈ s, physicalNormSq S.x K F.a (u i) := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  let e : EuclideanSpace ℂ (PState F S) ≃ₗ[ℂ] (PState F S → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : PState F S => ℂ)).toLinearEquiv
  have hNorm (x : EuclideanSpace ℂ (PState F S)) :
      physicalNormSq S.x K F.a (e x) = physicalMeasure S.x K F.a * ‖x‖ ^ 2 := by
    exact pd1c_physicalNormSq_euclidean F S x
  have hsum : (∑ i ∈ s, c i • u i) = e (∑ i ∈ s, c i • e.symm (u i)) := by
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
  have hNorms : (∑ i ∈ s, physicalNormSq S.x K F.a (u i)) =
      physicalMeasure S.x K F.a * ∑ i ∈ s, ‖e.symm (u i)‖ ^ 2 := by
    calc
      _ = ∑ i ∈ s, physicalNormSq S.x K F.a (e (e.symm (u i))) := by simp
      _ = ∑ i ∈ s, physicalMeasure S.x K F.a * ‖e.symm (u i)‖ ^ 2 := by simp only [hNorm]
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hRaw := pd1c_gram_trace_bound s c (fun i => e.symm (u i))
    (LinearMap.id : EuclideanSpace ℂ (PState F S) →ₗ[ℂ] EuclideanSpace ℂ (PState F S)) M hM hc
  simp only [LinearMap.id_apply] at hRaw
  calc
    _ = physicalMeasure S.x K F.a * ‖∑ i ∈ s, c i • e.symm (u i)‖ ^ 2 := by rw [hsum, hNorm]
    _ ≤ physicalMeasure S.x K F.a *
        ((s.card : ℝ) * M ^ 2 * ∑ i ∈ s, ‖e.symm (u i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hRaw (pd1c_physicalMeasure_nonneg _ _ _)
    _ = _ := by rw [hNorms]; ring

lemma pd1c_iterate_trace_factor {K : ℕ} (F : PDFix K) (S : PDScale) (R : ℕ) :
    ∃ T : (PState F S → ℂ) →ₗ[ℂ] (PState F S → ℂ),
      ∀ f : PState F S → ℂ,
        (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[R] f)).re =
          physicalNormSq S.x K F.a (T f) := by
  let k := R / 2
  let B := (pd1c_detLinearMap F S).comp (pd1c_detAdjLinearMap F S)
  have hmod : R % 2 = 0 ∨ R % 2 = 1 := by omega
  rcases hmod with hmod | hmod
  · have hR : R = k + k := by dsimp only [k]; omega
    refine ⟨B ^ k, ?_⟩
    intro f
    rw [hR, Function.iterate_add_apply, pd1c_positiveOperator_iterate_adjoint,
      pd1c_physInner_self, Module.End.pow_apply]
    rfl
  · have hR : R = k + (k + 1) := by dsimp only [k]; omega
    refine ⟨(pd1c_detAdjLinearMap F S).comp (B ^ k), ?_⟩
    intro f
    rw [hR, Function.iterate_add_apply, pd1c_positiveOperator_iterate_adjoint,
      Function.iterate_succ_apply', pd1c_detOp_adjoint, pd1c_physInner_self,
      LinearMap.comp_apply, Module.End.pow_apply]
    rfl

lemma pd1c_physical_trace_compression {ι : Type*} {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : Finset ι) (c : ι → ℂ) (u : ι → PState F S → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ i ∈ s, ‖c i‖ ≤ M) (R : ℕ) :
    (physInner F S (∑ i ∈ s, c i • u i)
      ((fun h => detOp F S (detOpAdj F S h))^[R] (∑ i ∈ s, c i • u i))).re ≤
        (s.card : ℝ) * M ^ 2 *
          ∑ i ∈ s, (physInner F S (u i)
            ((fun h => detOp F S (detOpAdj F S h))^[R] (u i))).re := by
  obtain ⟨T, hT⟩ := pd1c_iterate_trace_factor F S R
  rw [hT, map_sum]
  simp only [map_smul]
  have h := pd1c_physicalNormSq_sum_bound F S s c (fun i => T (u i)) M hM hc
  simpa only [← hT] using h

lemma pd1c_sharedProduct_pos {K : ℕ} (F : PDFix K) (S : PDScale) (P : PState F S) :
    0 < sharedProduct P.labels := by
  unfold sharedProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  split_ifs
  · exact (P.label_prime i j).pos
  · norm_num

lemma pd1c_geometricMultiplier_psi_zero {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (hψ : F.psi ((t : ℝ) / S.Y) = 0) :
    geometricMultiplier F S D aa bb t = 0 := by
  simp [geometricMultiplier, rawMultiplier, comparisonMultiplier, majorKernel, hψ]

lemma pd1c_physRowKernel_support {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℝ) (hB : 0 ≤ B) (hψ : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B)
    (hY : 0 < S.Y) (P Q : PState F S) (hK : physRowKernel F S P Q ≠ 0) :
    |(det2 P.pos Q.pos : ℝ)| ≤ 2 * B * S.H := by
  have hslot : slotKernel F S P.labels Q.labels (det2 P.pos Q.pos) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hK).1
  unfold slotKernel at hslot
  split_ifs at hslot with hEdge
  · let D := sharedProduct P.labels
    let dt := det2 P.pos Q.pos
    have hpad : IsPadAdmissible S.d₀ D dt := hEdge.2
    have hgeom : geometricMultiplier F S D (lastProduct Q.labels) (lastProduct P.labels)
        (dt / (D : ℤ)) ≠ 0 := (mul_ne_zero_iff.mp hslot).2
    have hψne : F.psi (((dt / (D : ℤ) : ℤ) : ℝ) / S.Y) ≠ 0 := by
      intro hz
      exact hgeom (pd1c_geometricMultiplier_psi_zero F S _ _ _ _ hz)
    have hbound := hψ _ hψne
    rw [abs_div, abs_of_pos hY] at hbound
    have htBound : |((dt / (D : ℤ) : ℤ) : ℝ)| ≤ B * S.Y :=
      (div_le_iff₀ hY).mp hbound
    have hD : 0 < D := pd1c_sharedProduct_pos F S P
    have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
    have hDiv : dt = (D : ℤ) * (dt / (D : ℤ)) :=
      (Int.mul_ediv_cancel' hpad.2.2).symm
    have hDivReal : (dt : ℝ) = (D : ℝ) * ((dt / (D : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hDiv
    change |(dt : ℝ)| ≤ _
    rw [hDivReal, abs_mul, abs_of_pos hDR]
    calc
      _ ≤ (D : ℝ) * (B * S.Y) := mul_le_mul_of_nonneg_left htBound hDR.le
      _ ≤ (2 * (S.d₀ : ℝ)) * (B * S.Y) :=
        mul_le_mul_of_nonneg_right hpad.2.1.le (mul_nonneg hB hY.le)
      _ = _ := by unfold PDScale.H; ring
  · simp at hslot

lemma pd1c_detOp_local {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℝ) (hB : 0 ≤ B) (hψ : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B) (hY : 0 < S.Y)
    (P : PState F S) (f : PState F S → ℂ)
    (hfar : ∀ Q : PState F S, |(det2 P.pos Q.pos : ℝ)| ≤ 2 * B * S.H → f Q = 0) :
    detOp F S f P = 0 := by
  have hRow : ∀ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      physRow F S (physSym F S (physGood F S f)) (P.permute σ) = 0 := by
    intro σ
    unfold physRow
    trans ∑' Q : PState F S, (0 : ℂ)
    · apply tsum_congr
      intro Q
      by_cases hK : physRowKernel F S (P.permute σ) Q = 0
      · simp [hK]
      · have hsupport := pd1c_physRowKernel_support F S B hB hψ hY (P.permute σ) Q hK
        have hInner : physSym F S (physGood F S f) Q = 0 := by
          unfold physSym
          have hAll : ∀ τ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              physGood F S f (Q.permute τ) = 0 := by
            intro τ
            have hZero : f (Q.permute τ) = 0 := hfar _ hsupport
            simp only [physGood, hZero, ite_self]
          simp only [hAll, Finset.sum_const_zero, mul_zero]
        rw [hInner, mul_zero]
    · simp only [tsum_zero]
  have hSym : physSym F S (physRow F S (physSym F S (physGood F S f))) P = 0 := by
    simp only [physSym, hRow, Finset.sum_const_zero, mul_zero]
  change (if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) then
    physSym F S (physRow F S (physSym F S (physGood F S f))) P else 0) = 0
  simp only [hSym, ite_self]

lemma pd1c_physical_cauchy_schwarz {K : ℕ} (F : PDFix K) (S : PDScale)
    (f g : PState F S → ℂ) :
    ‖physInner F S f g‖ ^ 2 ≤ physicalNormSq S.x K F.a f * physicalNormSq S.x K F.a g := by
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  let x : EuclideanSpace ℂ (PState F S) := WithLp.toLp 2 f
  let y : EuclideanSpace ℂ (PState F S) := WithLp.toLp 2 g
  let w := physicalMeasure S.x K F.a
  have hw : 0 ≤ w := pd1c_physicalMeasure_nonneg _ _ _
  have hInner : physInner F S f g = (w : ℂ) * inner ℂ x y :=
    pd1c_physInner_euclidean F S x y
  have hf : physicalNormSq S.x K F.a f = w * ‖x‖ ^ 2 :=
    pd1c_physicalNormSq_euclidean F S x
  have hg : physicalNormSq S.x K F.a g = w * ‖y‖ ^ 2 :=
    pd1c_physicalNormSq_euclidean F S y
  rw [hInner, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw, hf, hg]
  have hCS : ‖inner ℂ x y‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hsquare := pow_le_pow_left₀ (norm_nonneg (inner ℂ x y)) hCS 2
  nlinarith [mul_le_mul_of_nonneg_left hsquare (sq_nonneg w)]

lemma pd1c_physical_spectral_pairing_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (R : ℕ) (hR : 1 ≤ R) (f g : PState F S → ℂ) :
    ‖physInner F S f (detOp F S g)‖ ≤
      (physicalNormSq S.x K F.a g) ^ (1 / 2 : ℝ) *
        (physicalNormSq S.x K F.a f) ^ ((1 - 1 / (R : ℝ)) / 2) *
        (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[R] f)).re ^
          (1 / (2 * (R : ℝ))) := by
  let a := ‖physInner F S f (detOp F S g)‖
  let b := physicalNormSq S.x K F.a g
  let c := physicalNormSq S.x K F.a f
  let t := (physInner F S f ((fun h => detOp F S (detOpAdj F S h))^[R] f)).re
  have hb : 0 ≤ b := by
    dsimp only [b]
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S g
  have hc : 0 ≤ c := by
    dsimp only [c]
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S f
  have ht : 0 ≤ t := pd1c_positiveOperator_iterate_nonneg F S R f
  have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  have hCS : a ^ 2 ≤ b * (c ^ (1 - 1 / (R : ℝ)) * t ^ (1 / (R : ℝ))) := by
    have h := pd1c_physical_cauchy_schwarz F S (detOpAdj F S f) g
    have hSpec := pd1c_physical_spectral_power_inner_le F S R hR f
    have hAdjNorm : physicalNormSq S.x K F.a (detOpAdj F S f) =
        (physInner F S f (detOp F S (detOpAdj F S f))).re := by
      rw [pd1c_detOp_adjoint, pd1c_physInner_self]
    rw [← pd1c_detOp_adjoint, hAdjNorm] at h
    calc
      _ ≤ (physInner F S f (detOp F S (detOpAdj F S f))).re * b := h
      _ ≤ (c ^ (1 - 1 / (R : ℝ)) * t ^ (1 / (R : ℝ))) * b :=
        mul_le_mul_of_nonneg_right hSpec hb
      _ = _ := by ring
  have hRoot := pd1c_power_bound_to_rpow a b
    (c ^ (1 - 1 / (R : ℝ)) * t ^ (1 / (R : ℝ))) (norm_nonneg _) hb
    (mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg ht _)) 2 (by norm_num) (by simpa using hCS)
  simp only [Nat.cast_ofNat, Real.rpow_eq_pow] at hRoot
  norm_num only at hRoot
  calc
    _ ≤ b ^ (1 / 2 : ℝ) * (c ^ (1 - 1 / (R : ℝ)) * t ^ (1 / (R : ℝ))) ^ (1 / 2 : ℝ) := by simpa only [a, one_div] using hRoot
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_nonneg hc _) (Real.rpow_nonneg ht _),
        ← Real.rpow_mul hc, ← Real.rpow_mul ht, ← mul_assoc]
      have he₁ : (1 - 1 / (R : ℝ)) * (1 / 2 : ℝ) = (1 - 1 / (R : ℝ)) / 2 := by ring
      have he₂ : (1 / (R : ℝ)) * (1 / 2 : ℝ) = 1 / (2 * (R : ℝ)) := by field_simp [hRne]
      rw [he₁, he₂]

noncomputable def pd1c_positionSet {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] : Finset (ℕ × ℕ) :=
  Finset.univ.image fun P : PState F S => (P.first, P.second)

noncomputable def pd1c_positionValue {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) (uv : ℕ × ℕ) : ℂ :=
  if h : ∃ P : PState F S, P.first = uv.1 ∧ P.second = uv.2 then f (Classical.choose h) else 0

lemma pd1c_position_mem {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (P : PState F S) : (P.first, P.second) ∈ pd1c_positionSet F S :=
  Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩

lemma pd1c_positionValue_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q)
    (uv : ℕ × ℕ) (P : PState F S) (hP : P.first = uv.1 ∧ P.second = uv.2) :
    pd1c_positionValue F S f uv = f P := by
  have hex : ∃ Q : PState F S, Q.first = uv.1 ∧ Q.second = uv.2 := ⟨P, hP⟩
  rw [pd1c_positionValue, dif_pos hex]
  have hQ := Classical.choose_spec hex
  exact hConst _ P (hQ.1.trans hP.1.symm) (hQ.2.trans hP.2.symm)

lemma pd1c_position_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (f : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q) :
    f = ∑ uv ∈ pd1c_positionSet F S, pd1c_positionValue F S f uv • positionVector F S uv.1 uv.2 := by
  funext P
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, positionVector]
  rw [Finset.sum_eq_single (P.first, P.second)]
  · rw [pd1c_positionValue_eq F S f hConst _ P ⟨rfl, rfl⟩]
    simp
  · intro uv huv hne
    have hnot : ¬(P.first = uv.1 ∧ P.second = uv.2) := by
      rintro ⟨h₁, h₂⟩
      apply hne
      exact (Prod.ext h₁ h₂).symm
    simp [hnot]
  · intro hnot
    exact (hnot (pd1c_position_mem F S P)).elim

lemma pd1c_position_absent_vector {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (uv : ℕ × ℕ) (h : uv ∉ pd1c_positionSet F S) :
    positionVector F S uv.1 uv.2 = 0 := by
  funext P
  have hnot : ¬(P.first = uv.1 ∧ P.second = uv.2) := by
    rintro ⟨h₁, h₂⟩
    apply h
    have hp := pd1c_position_mem F S P
    simpa only [h₁, h₂, Prod.mk.eta] using hp
  simp only [positionVector, hnot, ite_false, Pi.zero_apply]

lemma pd1c_state_position_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (P : PState F S) : IsOmegaPosition S P.first P.second := by
  refine ⟨P.primitive, P.first_lower, ?_, P.second_lower, P.second_upper⟩
  simpa only [PDScale.U, mul_assoc] using P.first_upper

lemma pd1c_detMoment_finite_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] :
    detMoment F S = (S.U * S.V)⁻¹ *
      ∑ uv ∈ pd1c_positionSet F S,
        (physInner F S (positionVector F S uv.1 uv.2)
          ((fun h => detOp F S (detOpAdj F S h))^[S.R]
            (positionVector F S uv.1 uv.2))).re := by
  unfold detMoment
  congr 1
  rw [tsum_eq_sum (s := pd1c_positionSet F S)]
  · apply Finset.sum_congr rfl
    intro uv huv
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp huv
    simp only [pd1c_state_position_valid F S P, ite_true]
  · intro uv huv
    have hZero := pd1c_position_absent_vector F S uv huv
    simp [hZero, physInner]

lemma pd1c_detMoment_trace_identity {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (hUV : S.U * S.V ≠ 0) :
    (∑ uv ∈ pd1c_positionSet F S,
        (physInner F S (positionVector F S uv.1 uv.2)
          ((fun h => detOp F S (detOpAdj F S h))^[S.R]
            (positionVector F S uv.1 uv.2))).re) =
      S.U * S.V * detMoment F S := by
  rw [pd1c_detMoment_finite_sum, ← mul_assoc, mul_inv_cancel₀ hUV, one_mul]

noncomputable def pd1c_cell (S : PDScale) (uv : ℕ × ℕ) : ℤ :=
  ⌊((uv.2 : ℝ) / uv.1) / (S.H / S.U ^ 2)⌋

noncomputable def pd1c_cellSet {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)] :
    Finset ℤ := (pd1c_positionSet F S).image (pd1c_cell S)

noncomputable def pd1c_cellVector {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℤ) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => if pd1c_cell S (P.first, P.second) = j then f P else 0

noncomputable def pd1c_neighborVector {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℤ) (m : ℕ) (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => if |pd1c_cell S (P.first, P.second) - j| ≤ (m : ℤ) then f P else 0

lemma pd1c_cell_positions_card {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (hU : 0 < S.U) (hH : 1 ≤ S.H) (j : ℤ) :
    (((pd1c_positionSet F S).filter fun uv => pd1c_cell S uv = j).card : ℝ) ≤ 9000 * S.H := by
  apply pd1c_slope_cell_card _ S.U S.H hU hH
  · intro uv huv
    obtain ⟨hp, hj⟩ := Finset.mem_filter.mp huv
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hp
    have hValid := pd1c_state_position_valid F S P
    exact ⟨hValid.1, hValid.2.1, hValid.2.2.1⟩
  · intro uv huv w hw
    have hc : pd1c_cell S uv = pd1c_cell S w :=
      (Finset.mem_filter.mp huv).2.trans (Finset.mem_filter.mp hw).2.symm
    let Δ := S.H / S.U ^ 2
    have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
    have hNorm := pd1c_equal_floor_distance
      (((uv.2 : ℝ) / uv.1) / Δ) (((w.2 : ℝ) / w.1) / Δ) hc
    rw [← sub_div, abs_div, abs_of_pos hΔ] at hNorm
    have h := (div_le_iff₀ hΔ).mp hNorm
    simpa only [one_mul] using h

lemma pd1c_cells_near_of_detbound {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hH : 1 ≤ S.H) (B : ℝ) (hB : 0 ≤ B)
    (P Q : PState F S)
    (hdet : |(det2 P.pos Q.pos : ℝ)| ≤ 2 * B * S.H) :
    |pd1c_cell S (P.first, P.second) - pd1c_cell S (Q.first, Q.second)| ≤
      ((⌈2 * B⌉₊ + 2 : ℕ) : ℤ) := by
  let Δ := S.H / S.U ^ 2
  have hHpos : 0 < S.H := lt_of_lt_of_le (by norm_num) hH
  have hΔ : 0 < Δ := by dsimp only [Δ]; positivity
  have hP : 0 < (P.first : ℝ) := hU.trans_le P.first_lower
  have hQ : 0 < (Q.first : ℝ) := hU.trans_le Q.first_lower
  have hProd : S.U ^ 2 ≤ (P.first : ℝ) * (Q.first : ℝ) := by
    simpa only [PDScale.U, pow_two] using mul_le_mul P.first_lower Q.first_lower hU.le hP.le
  have hDen : S.H ≤ ((P.first : ℝ) * (Q.first : ℝ)) * Δ := by
    have h := mul_le_mul_of_nonneg_right hProd hΔ.le
    have heq : S.U ^ 2 * Δ = S.H := by
      dsimp only [Δ]
      field_simp [hU.ne']
    rwa [heq] at h
  have hDenPos : 0 < ((P.first : ℝ) * (Q.first : ℝ)) * Δ := by positivity
  have heq : (((P.second : ℝ) / P.first) / Δ) - (((Q.second : ℝ) / Q.first) / Δ) =
      -(det2 P.pos Q.pos : ℝ) / (((P.first : ℝ) * (Q.first : ℝ)) * Δ) := by
    simp only [det2, PhysicalState.pos]
    push_cast
    field_simp [hP.ne', hQ.ne', hΔ.ne'] <;> ring
  have hNorm : |(((P.second : ℝ) / P.first) / Δ) - (((Q.second : ℝ) / Q.first) / Δ)| ≤ 2 * B := by
    rw [heq, abs_div, abs_neg, abs_of_pos hDenPos, div_le_iff₀ hDenPos]
    exact hdet.trans (mul_le_mul_of_nonneg_left hDen (by positivity))
  have hFloor := pd1c_floor_distance_le
    (((P.second : ℝ) / P.first) / Δ) (((Q.second : ℝ) / Q.first) / Δ)
  have hCeil : 2 * B ≤ (⌈2 * B⌉₊ : ℝ) := Nat.le_ceil _
  have hResult : |((pd1c_cell S (P.first, P.second) - pd1c_cell S (Q.first, Q.second) : ℤ) : ℝ)| ≤
      ((⌈2 * B⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    push_cast at hFloor
    dsimp only [pd1c_cell, Δ] at *
    linarith
  exact_mod_cast hResult

lemma pd1c_cell_mem {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (P : PState F S) : pd1c_cell S (P.first, P.second) ∈ pd1c_cellSet F S :=
  Finset.mem_image.mpr ⟨_, pd1c_position_mem F S P, rfl⟩

lemma pd1c_cell_expansion {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (f : PState F S → ℂ) : f = ∑ j ∈ pd1c_cellSet F S, pd1c_cellVector F S j f := by
  funext P
  simp only [Finset.sum_apply, pd1c_cellVector]
  rw [Finset.sum_eq_single (pd1c_cell S (P.first, P.second))]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (pd1c_cell_mem F S P)).elim

lemma pd1c_cell_norm_sum {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (f : PState F S → ℂ) :
    (∑ j ∈ pd1c_cellSet F S, physicalNormSq S.x K F.a (pd1c_cellVector F S j f)) =
      physicalNormSq S.x K F.a f := by
  simp only [physicalNormSq, tsum_fintype]
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply congrArg (fun z : ℝ => physicalMeasure S.x K F.a * z)
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_eq_single (pd1c_cell S (P.first, P.second))]
  · simp [pd1c_cellVector]
  · intro j hj hne
    simp [pd1c_cellVector, Ne.symm hne]
  · intro hnot
    exact (hnot (pd1c_cell_mem F S P)).elim

lemma pd1c_neighbor_norm_sum {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (f : PState F S → ℂ) (m : ℕ) :
    (∑ j ∈ pd1c_cellSet F S, physicalNormSq S.x K F.a (pd1c_neighborVector F S j m f)) ≤
      ((2 * m + 1 : ℕ) : ℝ) * physicalNormSq S.x K F.a f := by
  let J := pd1c_cellSet F S
  have hPoint : ∀ P : PState F S,
      (∑ j ∈ J, ‖pd1c_neighborVector F S j m f P‖ ^ 2) ≤
        ((2 * m + 1 : ℕ) : ℝ) * ‖f P‖ ^ 2 := by
    intro P
    have hCount := pd1c_integer_neighbors_card J (pd1c_cell S (P.first, P.second)) m
    have hCountR :
        ((J.filter fun j => |pd1c_cell S (P.first, P.second) - j| ≤ (m : ℤ)).card : ℝ) ≤
          ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hCount
    have hsum : (∑ j ∈ J, ‖pd1c_neighborVector F S j m f P‖ ^ 2) =
        ((J.filter fun j => |pd1c_cell S (P.first, P.second) - j| ≤ (m : ℤ)).card : ℝ) * ‖f P‖ ^ 2 := by
      have hterm : ∀ j : ℤ, ‖pd1c_neighborVector F S j m f P‖ ^ 2 =
          if |pd1c_cell S (P.first, P.second) - j| ≤ (m : ℤ) then ‖f P‖ ^ 2 else 0 := by
        intro j
        by_cases h : |pd1c_cell S (P.first, P.second) - j| ≤ (m : ℤ)
        · simp [pd1c_neighborVector, h]
        · simp [pd1c_neighborVector, h]
      simp only [hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hCountR (sq_nonneg _)
  simp only [physicalNormSq, tsum_fintype]
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    _ ≤ physicalMeasure S.x K F.a *
        (∑ P : PState F S, ((2 * m + 1 : ℕ) : ℝ) * ‖f P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P hP => hPoint P)
        (pd1c_physicalMeasure_nonneg _ _ _)
    _ = _ := by rw [← Finset.mul_sum]; ring

lemma pd1c_arc_cutoff_support_bound {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ B : ℝ, 4 ≤ B ∧ ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B := by
  obtain ⟨hBands, hqd₀, hqd₁, hA₀, hEta, hPsi⟩ := hF
  have hcomp : HasCompactSupport F.psi := hPsi.2.1
  obtain ⟨C, hC⟩ := hcomp.isCompact.isBounded.exists_norm_le
  refine ⟨max 4 C, le_max_left _ _, ?_⟩
  intro t ht
  have h := hC t (subset_tsupport F.psi ht)
  have hAbs : |t| ≤ C := by simpa only [Real.norm_eq_abs] using h
  exact hAbs.trans (le_max_right _ _)

lemma pd1c_positionValue_bound {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (f : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q)
    (M : ℝ) (hBound : ∀ P, ‖f P‖ ≤ M) (uv : ℕ × ℕ) (huv : uv ∈ pd1c_positionSet F S) :
    ‖pd1c_positionValue F S f uv‖ ≤ M := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp huv
  rw [pd1c_positionValue_eq F S f hConst _ P ⟨rfl, rfl⟩]
  exact hBound P

lemma pd1c_cell_position_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (f : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q) (j : ℤ) :
    pd1c_cellVector F S j f =
      ∑ uv ∈ (pd1c_positionSet F S).filter (fun uv => pd1c_cell S uv = j),
        pd1c_positionValue F S f uv • positionVector F S uv.1 uv.2 := by
  funext P
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, positionVector, pd1c_cellVector]
  by_cases hPj : pd1c_cell S (P.first, P.second) = j
  · rw [if_pos hPj, Finset.sum_eq_single (P.first, P.second)]
    · rw [pd1c_positionValue_eq F S f hConst _ P ⟨rfl, rfl⟩]
      simp
    · intro uv huv hne
      have hnot : ¬(P.first = uv.1 ∧ P.second = uv.2) := by
        rintro ⟨h₁, h₂⟩
        exact hne (Prod.ext h₁ h₂).symm
      simp [hnot]
    · intro hnot
      exact (hnot (Finset.mem_filter.mpr ⟨pd1c_position_mem F S P, hPj⟩)).elim
  · rw [if_neg hPj]
    symm
    apply Finset.sum_eq_zero
    intro uv huv
    have hnot : ¬(P.first = uv.1 ∧ P.second = uv.2) := by
      rintro ⟨h₁, h₂⟩
      apply hPj
      have heq : (P.first, P.second) = uv := Prod.ext h₁ h₂
      rw [heq]
      exact (Finset.mem_filter.mp huv).2
    simp [hnot]

noncomputable def pd1c_cellTrace {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (R : ℕ) (j : ℤ) : ℝ :=
  ∑ uv ∈ (pd1c_positionSet F S).filter (fun uv => pd1c_cell S uv = j),
    (physInner F S (positionVector F S uv.1 uv.2)
      ((fun h => detOp F S (detOpAdj F S h))^[R] (positionVector F S uv.1 uv.2))).re

lemma pd1c_cellTrace_nonneg {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (R : ℕ) (j : ℤ) : 0 ≤ pd1c_cellTrace F S R j := by
  apply Finset.sum_nonneg
  intro uv huv
  exact pd1c_positiveOperator_iterate_nonneg F S R _

lemma pd1c_cellTrace_sum {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (hUV : S.U * S.V ≠ 0) :
    (∑ j ∈ pd1c_cellSet F S, pd1c_cellTrace F S S.R j) = S.U * S.V * detMoment F S := by
  simp only [pd1c_cellTrace, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [← pd1c_detMoment_trace_identity F S hUV]
  apply Finset.sum_congr rfl
  intro uv huv
  rw [Finset.sum_eq_single (pd1c_cell S uv)]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]
  · intro hnot
    exact (hnot (Finset.mem_image.mpr ⟨uv, huv, rfl⟩)).elim

lemma pd1c_cell_trace_bound {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (hU : 0 < S.U) (hH : 1 ≤ S.H) (f : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ P, ‖f P‖ ≤ M) (R : ℕ) (j : ℤ) :
    (physInner F S (pd1c_cellVector F S j f)
      ((fun h => detOp F S (detOpAdj F S h))^[R] (pd1c_cellVector F S j f))).re ≤
        9000 * S.H * M ^ 2 * pd1c_cellTrace F S R j := by
  let s := (pd1c_positionSet F S).filter (fun uv => pd1c_cell S uv = j)
  have hComp := pd1c_physical_trace_compression F S s
    (pd1c_positionValue F S f) (fun uv => positionVector F S uv.1 uv.2) M hM
    (fun uv huv => pd1c_positionValue_bound F S f hConst M hBound uv (Finset.mem_filter.mp huv).1) R
  rw [pd1c_cell_position_expansion F S f hConst j]
  calc
    _ ≤ (s.card : ℝ) * M ^ 2 * pd1c_cellTrace F S R j := hComp
    _ ≤ 9000 * S.H * M ^ 2 * pd1c_cellTrace F S R j := by
      have hCard := pd1c_cell_positions_card F S hU hH j
      have h := mul_le_mul_of_nonneg_right hCard
        (mul_nonneg (sq_nonneg M) (pd1c_cellTrace_nonneg F S R j))
      simpa only [mul_assoc] using h

lemma pd1c_cell_pairing_localization {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hH : 1 ≤ S.H) (hY : 0 < S.Y) (B : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B) (j : ℤ) (f g : PState F S → ℂ) :
    physInner F S (pd1c_cellVector F S j f) (detOp F S g) =
      physInner F S (pd1c_cellVector F S j f)
        (detOp F S (pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g)) := by
  unfold physInner
  apply congrArg (fun z : ℂ => (physicalMeasure S.x K F.a : ℂ) * z)
  apply tsum_congr
  intro P
  by_cases hPj : pd1c_cell S (P.first, P.second) = j
  · have hZero := pd1c_detOp_local F S B hB hψ hY P
      (g - pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g) (by
        intro Q hDet
        have hNear := pd1c_cells_near_of_detbound F S hU hH B hB P Q hDet
        rw [hPj] at hNear
        have hQj : |pd1c_cell S (Q.first, Q.second) - j| ≤ ((⌈2 * B⌉₊ + 2 : ℕ) : ℤ) := by
          simpa only [abs_sub_comm] using hNear
        simp only [Nat.cast_add, Nat.cast_ofNat] at hQj
        simp [pd1c_neighborVector, hQj])
    have hSub := congrFun ((pd1c_detLinearMap F S).map_sub g
      (pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g)) P
    change detOp F S (g - pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g) P =
      detOp F S g P - detOp F S (pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g) P at hSub
    rw [hSub] at hZero
    rw [sub_eq_zero.mp hZero]
  · simp [pd1c_cellVector, hPj]

lemma pd1c_physInner_sum_left {ι : Type*} {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (s : Finset ι) (f : ι → PState F S → ℂ) (g : PState F S → ℂ) :
    physInner F S (∑ i ∈ s, f i) g = ∑ i ∈ s, physInner F S (f i) g := by
  simp only [physInner, tsum_fintype, Finset.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

lemma pd1c_cell_pairing_sum {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (hU : 0 < S.U) (hH : 1 ≤ S.H) (hY : 0 < S.Y) (B : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B) (f g : PState F S → ℂ) :
    physInner F S f (detOp F S g) =
      ∑ j ∈ pd1c_cellSet F S, physInner F S (pd1c_cellVector F S j f)
        (detOp F S (pd1c_neighborVector F S j (⌈2 * B⌉₊ + 2) g)) := by
  calc
    _ = physInner F S (∑ j ∈ pd1c_cellSet F S, pd1c_cellVector F S j f) (detOp F S g) :=
      congrArg (fun u => physInner F S u (detOp F S g)) (pd1c_cell_expansion F S f)
    _ = ∑ j ∈ pd1c_cellSet F S, physInner F S (pd1c_cellVector F S j f) (detOp F S g) :=
      pd1c_physInner_sum_left F S _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact pd1c_cell_pairing_localization F S hU hH hY B hB hψ j f g

lemma pd1c_one_cell_trace_pairing {K : ℕ} (F : PDFix K) (S : PDScale) [Fintype (PState F S)]
    (hU : 0 < S.U) (hH : 1 ≤ S.H) (f g : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ P, ‖f P‖ ≤ M) (R : ℕ) (hR : 1 ≤ R)
    (j : ℤ) (m : ℕ) :
    ‖physInner F S (pd1c_cellVector F S j f) (detOp F S (pd1c_neighborVector F S j m g))‖ ≤
      (physicalNormSq S.x K F.a (pd1c_neighborVector F S j m g)) ^ (1 / 2 : ℝ) *
        (physicalNormSq S.x K F.a (pd1c_cellVector F S j f)) ^ ((1 - 1 / (R : ℝ)) / 2) *
        (9000 * S.H * M ^ 2 * pd1c_cellTrace F S R j) ^ (1 / (2 * (R : ℝ))) := by
  have hSpec := pd1c_physical_spectral_pairing_bound F S R hR
    (pd1c_cellVector F S j f) (pd1c_neighborVector F S j m g)
  have hTrace := pd1c_cell_trace_bound F S hU hH f hConst M hM hBound R j
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hPow := Real.rpow_le_rpow (pd1c_positiveOperator_iterate_nonneg F S R _)
    hTrace (by positivity : 0 ≤ (1 / (2 * (R : ℝ))))
  refine hSpec.trans (mul_le_mul_of_nonneg_left hPow ?_)
  exact mul_nonneg
    (Real.rpow_nonneg (by rw [← pd1c_physInner_self]; exact pd1c_physInner_self_nonneg F S _) _)
    (Real.rpow_nonneg (by rw [← pd1c_physInner_self]; exact pd1c_physInner_self_nonneg F S _) _)

lemma pd1c_physical_moment_pairing_sq {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (hU : 0 < S.U) (hH : 1 ≤ S.H) (hY : 0 < S.Y)
    (hUV : 0 < S.U * S.V) (hR : 2 ≤ S.R) (B : ℝ) (hB : 0 ≤ B)
    (hψ : ∀ t : ℝ, F.psi t ≠ 0 → |t| ≤ B) (f g : PState F S → ℂ)
    (hConst : ∀ P Q, P.first = Q.first → P.second = Q.second → f P = f Q)
    (M : ℝ) (hM : 0 ≤ M) (hBound : ∀ P, ‖f P‖ ≤ M) :
    ‖physInner F S f (detOp F S g)‖ ^ 2 ≤
      (((2 * (⌈2 * B⌉₊ + 2) + 1 : ℕ) : ℝ) * physicalNormSq S.x K F.a g) *
        (physicalNormSq S.x K F.a f) ^ (1 - 1 / (S.R : ℝ)) *
        (9000 * S.H * M ^ 2 * (S.U * S.V * detMoment F S)) ^ (1 / (S.R : ℝ)) := by
  let J := pd1c_cellSet F S
  let m := ⌈2 * B⌉₊ + 2
  let Q := 9000 * S.H * M ^ 2
  let gn (j : ℤ) := (physicalNormSq S.x K F.a (pd1c_neighborVector F S j m g)) ^ (1 / 2 : ℝ)
  let fn (j : ℤ) := (physicalNormSq S.x K F.a (pd1c_cellVector F S j f)) ^ (1 / 2 : ℝ)
  let d := pd1c_cellTrace F S S.R
  let z (j : ℤ) := physInner F S (pd1c_cellVector F S j f)
    (detOp F S (pd1c_neighborVector F S j m g))
  let θ : ℝ := 1 - 1 / (S.R : ℝ)
  let τ : ℝ := 1 / (2 * (S.R : ℝ))
  have hRpos : 0 < (S.R : ℝ) := by exact_mod_cast (by omega : 0 < S.R)
  have hRne : (S.R : ℝ) ≠ 0 := hRpos.ne'
  have hθ : 0 ≤ θ := by
    have hge : 1 ≤ (S.R : ℝ) := by exact_mod_cast (by omega : 1 ≤ S.R)
    exact sub_nonneg.mpr ((div_le_iff₀ hRpos).mpr (by simpa using hge))
  have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hgn : ∀ j, 0 ≤ gn j := by
    intro j
    apply Real.rpow_nonneg
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S _
  have hfn : ∀ j, 0 ≤ fn j := by
    intro j
    apply Real.rpow_nonneg
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S _
  have hd : ∀ j, 0 ≤ d j := pd1c_cellTrace_nonneg F S S.R
  have hPoint : ∀ j ∈ J, ‖z j‖ ≤ Q ^ τ * (gn j * (fn j) ^ θ * (d j) ^ τ) := by
    intro j hj
    have h := pd1c_one_cell_trace_pairing F S hU hH f g hConst M hM hBound S.R (by omega) j m
    have hFnonneg : 0 ≤ physicalNormSq S.x K F.a (pd1c_cellVector F S j f) := by
      rw [← pd1c_physInner_self]
      exact pd1c_physInner_self_nonneg F S _
    have hFpow : (physicalNormSq S.x K F.a (pd1c_cellVector F S j f)) ^ (θ / 2) =
        (fn j) ^ θ := by
      dsimp only [fn]
      rw [← Real.rpow_mul hFnonneg]
      congr 1
      ring
    calc
      ‖z j‖ ≤ gn j * (physicalNormSq S.x K F.a (pd1c_cellVector F S j f)) ^ (θ / 2) *
          (Q * d j) ^ τ := h
      _ = _ := by
        rw [hFpow, Real.mul_rpow hQ (hd j)]
        ring
  have hTriangle : ‖physInner F S f (detOp F S g)‖ ≤
      Q ^ τ * (∑ j ∈ J, gn j * (fn j) ^ θ * (d j) ^ τ) := by
    rw [pd1c_cell_pairing_sum F S hU hH hY B hB hψ]
    calc
      _ ≤ ∑ j ∈ J, ‖z j‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, Q ^ τ * (gn j * (fn j) ^ θ * (d j) ^ τ) := Finset.sum_le_sum hPoint
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hHolder := pd1c_finite_three_factor_holder_sq J gn fn d
    (fun j hj => hgn j) (fun j hj => hfn j) (fun j hj => hd j) S.R hR
  have hgnSq : ∀ j, (gn j) ^ 2 = physicalNormSq S.x K F.a (pd1c_neighborVector F S j m g) := by
    intro j
    apply pd1c_rpow_half_sq
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S _
  have hfnSq : ∀ j, (fn j) ^ 2 = physicalNormSq S.x K F.a (pd1c_cellVector F S j f) := by
    intro j
    apply pd1c_rpow_half_sq
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S _
  have hGsum := pd1c_neighbor_norm_sum F S g m
  have hFsum := pd1c_cell_norm_sum F S f
  have hDsum := pd1c_cellTrace_sum F S hUV.ne'
  simp only [hgnSq, hfnSq] at hHolder
  rw [hFsum, hDsum] at hHolder
  have hQpow : (Q ^ τ) ^ 2 = Q ^ (1 / (S.R : ℝ)) := by
    rw [← Real.rpow_mul_natCast hQ]
    congr 1
    dsimp only [τ]
    push_cast
    field_simp [hRne]
  have hFDnonneg : 0 ≤
      (physicalNormSq S.x K F.a f) ^ θ * (S.U * S.V * detMoment F S) ^ (1 / (S.R : ℝ)) := by
    have hDnonneg : 0 ≤ S.U * S.V * detMoment F S := by rw [← hDsum]; exact Finset.sum_nonneg fun j hj => hd j
    exact mul_nonneg (Real.rpow_nonneg (by rw [← pd1c_physInner_self]; exact pd1c_physInner_self_nonneg F S _) _)
      (Real.rpow_nonneg hDnonneg _)
  calc
    _ ≤ (Q ^ τ * (∑ j ∈ J, gn j * (fn j) ^ θ * (d j) ^ τ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hTriangle 2
    _ = Q ^ (1 / (S.R : ℝ)) * (∑ j ∈ J, gn j * (fn j) ^ θ * (d j) ^ τ) ^ 2 := by rw [mul_pow, hQpow]
    _ ≤ Q ^ (1 / (S.R : ℝ)) *
        ((∑ j ∈ J, physicalNormSq S.x K F.a (pd1c_neighborVector F S j m g)) *
          (physicalNormSq S.x K F.a f) ^ θ * (S.U * S.V * detMoment F S) ^ (1 / (S.R : ℝ))) :=
      mul_le_mul_of_nonneg_left hHolder (Real.rpow_nonneg hQ _)
    _ ≤ Q ^ (1 / (S.R : ℝ)) *
        ((((2 * m + 1 : ℕ) : ℝ) * physicalNormSq S.x K F.a g) *
          (physicalNormSq S.x K F.a f) ^ θ * (S.U * S.V * detMoment F S) ^ (1 / (S.R : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hQ _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hGsum hFDnonneg
    _ = _ := by
      have hDnonneg : 0 ≤ S.U * S.V * detMoment F S := by rw [← hDsum]; exact Finset.sum_nonneg fun j hj => hd j
      rw [Real.mul_rpow hQ hDnonneg]
      dsimp only [Q, m, θ]
      ring

lemma pd1c_scale_basic {K : ℕ} {δ c₁ c₂ : ℝ} (S : PDScale)
    (hS : S.Valid K δ c₁ c₂) :
    1 ≤ S.H ∧ 0 < S.Y ∧ 0 < S.Hm ∧ 0 < S.Hn ∧ 0 < S.U ∧ 0 < S.U * S.V := by
  obtain ⟨hx, hm, hn, hX₀, hX₁, hY, hd⟩ := hS
  obtain ⟨k, hk, hYeq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hY).1
  have hYone : 1 ≤ S.Y := by
    rw [← hYeq]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨j, hj, hdeq⟩ := Finset.mem_image.mp hd
  have hdOne : (1 : ℝ) ≤ S.d₀ := by
    have hdNat : 1 ≤ S.d₀ := by rw [← hdeq]; exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    exact_mod_cast hdNat
  have hHone : 1 ≤ S.H := by
    change 1 ≤ (S.d₀ : ℝ) * S.Y
    simpa only [one_mul] using mul_le_mul hdOne hYone (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg S.d₀)
  have hxpos : 0 < S.x := lt_of_lt_of_le (by norm_num) hx
  have hmpos : 0 < S.Hm := (Real.rpow_pos_of_pos hxpos δ).trans_le hm
  have hnpos : 0 < S.Hn := (Real.rpow_pos_of_pos hxpos δ).trans_le hn
  have hHpos : 0 < S.H := lt_of_lt_of_le (by norm_num) hHone
  have hUpos : 0 < S.U := mul_pos hHpos hmpos
  exact ⟨hHone, lt_of_lt_of_le (by norm_num) hYone, hmpos, hnpos, hUpos, mul_pos hUpos hnpos⟩

lemma pd1c_scale_H_root_bound {K : ℕ} {δ c₁ c₂ : ℝ} (S : PDScale)
    (hS : S.Valid K δ c₁ c₂) (hL : 16 ≤ S.L) :
    2 ≤ S.R ∧ S.H ^ (1 / (2 * (S.R : ℝ))) ≤
      Real.exp (((K + 1 : ℕ) : ℝ) * (1 + Real.log 2)) := by
  have hBasic := pd1c_scale_basic S hS
  have hHpos : 0 < S.H := lt_of_lt_of_le (by norm_num) hBasic.1
  have hLone : 1 ≤ S.L := by linarith
  have hLpos : 0 < S.L := lt_of_lt_of_le (by norm_num) hLone
  have hCeil : S.L ^ (1 / 2 : ℝ) / 2 ≤ (S.R : ℝ) := Nat.le_ceil _
  have hHalf : 4 ≤ S.L ^ (1 / 2 : ℝ) := by
    have hsq := pd1c_rpow_half_sq S.L hLpos.le
    have hnonneg := Real.rpow_nonneg hLpos.le (1 / 2 : ℝ)
    nlinarith
  have hR : 2 ≤ S.R := by
    have hRReal : (2 : ℝ) ≤ S.R := by linarith
    exact_mod_cast hRReal
  have hRpos : 0 < (S.R : ℝ) := by exact_mod_cast (by omega : 0 < S.R)
  let C := ((K + 1 : ℕ) : ℝ) * (1 + Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hYlog : Real.log S.Y ≤ ((K + 1 : ℕ) : ℝ) * S.L ^ (1 / 5 : ℝ) :=
    (pd1c_dyadicScale_log_bounds hS.2.2.2.2.2.1).2
  obtain ⟨j, hj, hdeq⟩ := Finset.mem_image.mp hS.2.2.2.2.2.2
  have hjFloor : j ≤ ⌊((K + 1 : ℕ) : ℝ) * S.L ^ (21 / 100 : ℝ)⌋₊ := by
    have h : j < ⌊((K + 1 : ℕ) : ℝ) * S.L ^ (21 / 100 : ℝ)⌋₊ + 1 := Finset.mem_range.mp hj
    omega
  have hjReal : (j : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * S.L ^ (21 / 100 : ℝ) :=
    (Nat.cast_le.mpr hjFloor).trans (Nat.floor_le (by positivity))
  have hdReal : (S.d₀ : ℝ) = (2 : ℝ) ^ j := by exact_mod_cast hdeq.symm
  have hdPos : 0 < (S.d₀ : ℝ) := by rw [hdReal]; positivity
  have hdLog : Real.log (S.d₀ : ℝ) ≤
      ((K + 1 : ℕ) : ℝ) * S.L ^ (21 / 100 : ℝ) * Real.log 2 := by
    rw [hdReal, Real.log_pow]
    exact mul_le_mul_of_nonneg_right hjReal hlog2.le
  have hLow : S.L ^ (1 / 5 : ℝ) ≤ S.L ^ (21 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hLogH : Real.log S.H ≤ C * S.L ^ (21 / 100 : ℝ) := by
    rw [PDScale.H, Real.log_mul hdPos.ne' hBasic.2.1.ne']
    have hterm := mul_le_mul_of_nonneg_left hLow (show 0 ≤ ((K + 1 : ℕ) : ℝ) by positivity)
    dsimp only [C]
    nlinarith [hterm]
  have hPowN : S.L ^ (21 / 100 : ℝ) ≤ 2 * (S.R : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hLone
      (by norm_num : (21 / 100 : ℝ) ≤ 1 / 2)
    linarith
  have hLogN : Real.log S.H ≤ C * (2 * (S.R : ℝ)) :=
    hLogH.trans (mul_le_mul_of_nonneg_left hPowN hC)
  refine ⟨hR, ?_⟩
  rw [Real.rpow_def_of_pos hHpos]
  apply Real.exp_le_exp.mpr
  have hDiv : Real.log S.H / (2 * (S.R : ℝ)) ≤ C :=
    (div_le_iff₀ (by positivity : 0 < 2 * (S.R : ℝ))).mpr hLogN
  simpa only [mul_one_div] using hDiv

lemma pd1c_endpointF_conj {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (P : PState F S) :
    star (endpointF S.x K F.a family beta P) = endpointG S.x K F.a family beta P := by
  by_cases hSq : Squarefree (groupLabelProduct P)
  · simp [endpointF, endpointG, hSq, star_mul, mul_comm]
  · simp [endpointF, endpointG, hSq]

lemma pd1c_detPairing_inner {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ) :
    detPairing F S family beta =
      physInner F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)
        (detOp F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) := by
  unfold detPairing physInner
  congr 1
  apply tsum_congr
  intro P
  have h := congrArg star (pd1c_endpointF_conj F S family beta P)
  simp only [star_star] at h
  simpa only [endpointGVector] using congrArg
    (fun z : ℂ => z * detOp F S
      (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) P) h

lemma pd1c_endpointG_norm_sq_congr
    (x : ℝ) (K : ℕ) (a : Fin K → ℝ) {δ C c₁ c₂ : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (H' Hm Hn Hm' Hn' : ℝ) (hHm : Hm = Hm') (hHn : Hn = Hn') :
    physicalNormSq x K a (endpointGVector x K a H' Hm Hn family beta) =
      physicalNormSq x K a (endpointGVector x K a H' Hm' Hn' family beta) := by
  subst Hm' Hn'
  rfl

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
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  obtain ⟨Ce, Be, hCe, hBe, hEndpoints⟩ := endpoint_bounds δ C c₁ c₂ hδ hC hc₁ hc₂
  let CePair := 2 * Ce + 2 * C
  refine ⟨CePair, by dsimp only [CePair]; positivity, ?_⟩
  intro K F hF
  obtain ⟨xBands, hxBands, hBandsAt⟩ := pd1c_eventual_bands_separated K F.a hF.1
  obtain ⟨Bψ, hBψ, hψ⟩ := pd1c_arc_cutoff_support_bound F hF
  let nb : ℝ := ((2 * (⌈2 * Bψ⌉₊ + 2) + 1 : ℕ) : ℝ)
  let W := Real.exp (((K + 1 : ℕ) : ℝ) * (1 + Real.log 2))
  let Bstar := Be + 1
  let Cp := 100 * nb ^ (1 / 2 : ℝ) * Bstar ^ 2 * W
  let x₀ := max 2 (max xBands (Real.exp 16))
  have hnb : 0 < nb := by dsimp only [nb]; exact_mod_cast (by omega : 0 < 2 * (⌈2 * Bψ⌉₊ + 2) + 1)
  have hW : 0 < W := Real.exp_pos _
  have hBstar : 1 ≤ Bstar := by dsimp only [Bstar]; linarith
  have hBstarpos : 0 < Bstar := lt_of_lt_of_le (by norm_num) hBstar
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  refine ⟨Cp, x₀, hCp, le_max_left _ _, ?_⟩
  intro S hS hx family hScale hMin beta hBeta E₀ hE₀ hMoment
  letI : Finite (PState F S) := pd1c_physicalState_finite S.x K F.a S.H S.Hm S.Hn
  letI := Fintype.ofFinite (PState F S)
  have hxBands' : xBands ≤ S.x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxExp : Real.exp 16 ≤ S.x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hL : 16 ≤ S.L := by simpa only [PDScale.L, Real.log_exp] using Real.log_le_log (Real.exp_pos 16) hxExp
  have hLone : 1 ≤ S.L := by linarith
  have hLpos : 0 < S.L := lt_of_lt_of_le (by norm_num) hLone
  obtain ⟨hSep, hBelow⟩ := hBandsAt S.x hxBands'
  have hBasic := pd1c_scale_basic S hS
  have hH := hBasic.1
  have hY := hBasic.2.1
  have hU := hBasic.2.2.2.2.1
  have hUV := hBasic.2.2.2.2.2
  obtain ⟨hR, hHR⟩ := pd1c_scale_H_root_bound S hS hL
  let f := endpointGVector S.x K F.a S.H S.Hm S.Hn family beta
  have hfConst : ∀ P Q : PState F S, P.first = Q.first → P.second = Q.second → f P = f Q := by
    intro P Q hfirst hsecond
    exact pd1c_endpoint_position_constant family hMin beta hSep hBelow P Q hfirst hsecond
  let M := S.L ^ (2 * C)
  have hM : 0 ≤ M := Real.rpow_nonneg hLpos.le _
  have hfBound : ∀ P : PState F S, ‖f P‖ ≤ M := by
    intro P
    exact pd1c_endpointG_pointwise_general family hS.1 hMin beta hBeta.2 P
  have hHm : family.Hm S.x = S.Hm := hScale.1
  have hHn : family.Hn S.x = S.Hn := hScale.2
  have hEnds := hEndpoints K F.a hF.1 family S.x hS.1 hMin S.d₀ hS.2.2.2.2.2.2
    S.Y hS.2.2.2.2.2.1 beta
    (by simpa only [hHn] using hBeta.1)
    (by simpa only [hHn] using hBeta.2)
  have hfRoot : Real.sqrt (physicalNormSq S.x K F.a f) ≤
      (S.U * S.V) ^ (1 / 2 : ℝ) * (Be * S.L ^ Ce) := by
    have h := hEnds.2.1
    rw [pd1c_endpointG_norm_sq_congr S.x K F.a family beta ((S.d₀ : ℝ) * S.Y)
      (family.Hm S.x) (family.Hn S.x) S.Hm S.Hn hHm hHn] at h
    simpa only [hHm, hHn, PDScale.H, PDScale.U, PDScale.V, PDScale.L, f, mul_assoc,
      Real.rpow_eq_pow] using h
  have hfNonneg : 0 ≤ physicalNormSq S.x K F.a f := by
    rw [← pd1c_physInner_self]
    exact pd1c_physInner_self_nonneg F S f
  have hfRoot' : Real.sqrt (physicalNormSq S.x K F.a f) ≤
      (S.U * S.V) ^ (1 / 2 : ℝ) * (Bstar * S.L ^ Ce) := by
    refine hfRoot.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hUV.le _))
    exact mul_le_mul_of_nonneg_right (show Be ≤ Bstar by dsimp only [Bstar]; linarith)
      (Real.rpow_nonneg hLpos.le _)
  have hCePow : (S.L ^ Ce) ^ 2 = S.L ^ (2 * Ce) := by
    rw [← Real.rpow_mul_natCast hLpos.le]
    congr 1
    push_cast
    ring
  have hfSq : physicalNormSq S.x K F.a f ≤ S.U * S.V * Bstar ^ 2 * S.L ^ (2 * Ce) := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hfRoot' 2
    rw [Real.sq_sqrt hfNonneg, mul_pow, mul_pow, pd1c_rpow_half_sq _ hUV.le, hCePow] at h
    simpa only [mul_assoc] using h
  have hSq := pd1c_physical_moment_pairing_sq F S hU hH hY hUV hR Bψ
    (by linarith : 0 ≤ Bψ) hψ f f hfConst M hM hfBound
  have hD : 0 ≤ detMoment F S := pd1c_detMoment_nonneg F S hUV.le
  have hMoment' : detMoment F S ≤ S.L ^ (-2 * E₀ * (S.R : ℝ)) := by
    convert hMoment using 1
    simp only [Real.rpow_eq_pow]
    congr 1
    dsimp only [PDScale.N, PDScale.R, pathLength]
    push_cast
    ring
  have hScalar := pd1c_moment_scalar_bound S.L (S.U * S.V) S.H Bstar W nb C Ce E₀
    ‖physInner F S f (detOp F S f)‖
    (physicalNormSq S.x K F.a f) (physicalNormSq S.x K F.a f) (detMoment F S) S.R
    hLone hUV (by linarith : 0 < S.H) hBstar hW.le hnb.le hC hCe (norm_nonneg _)
    hfNonneg hfNonneg hD hR hHR hfSq hfSq hMoment' hSq
  rw [pd1c_detPairing_inner]
  calc
    _ ≤ 100 * nb ^ (1 / 2 : ℝ) * Bstar ^ 2 * W * (S.U * S.V) * S.L ^ (-E₀ + 2 * Ce + 2 * C) := hScalar
    _ = _ := by
      dsimp only [Cp, CePair]
      rw [show -E₀ + 2 * Ce + 2 * C = -E₀ + (2 * Ce + 2 * C) by ring]
      simp only [Real.rpow_eq_pow]
      ring



end

end ArtinPrimitiveRoots.TypeII.PD
