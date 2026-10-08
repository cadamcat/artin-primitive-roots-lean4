import ArtinPrimitiveRoots.TypeII.PD.Physical
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.MoebiusSeries
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.SL2Fibers
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.SL2CRT
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.GridIntegration
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.BoundedIntegral
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Nat.Choose.Bounds
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §3 Root parametrization, independent lines, root replacement (PD 03:413-737)

`def:pd-env` (new definitional node).  In the basis `g` of (det:root-matrix) every position is
`g z`; since `det(gz,gz') = det(z,z')`, the undamped kernel `𝒯₀` is root-independent, and all
root dependence sits in a diagonal factor `D_env` (box, good tests, active divisibility,
damping).  `𝒜 = (𝒢·Damp^{1/2}) 𝒮 𝒯₀ 𝒮 (Damp^{1/2}·𝒢)` because `𝒢` and the damping commute with
`𝒮`; this is what `path_expansion` records. -/

/-- COPY (moved from `PD/Memory.lean`, unchanged): visit damping `q_j` (mem:baseline). -/
noncomputable def memoryQ (x q_d : ℝ) (j : ℕ) : ℝ :=
  if j = 0 ∨ j = pathLength x then Real.sqrt q_d else q_d

/-- COPY (moved from `PD/Memory.lean`, unchanged): `η'_j = 1 - q_j`. -/
noncomputable def memoryEta (x q_d : ℝ) (j : ℕ) : ℝ :=
  1 - memoryQ x q_d j

/-- COPY (moved from `PD/Memory.lean`, unchanged): `b'_p` (mem:baseline). -/
noncomputable def memoryBPrime (x q_d : ℝ) (p : ℕ) : ℝ :=
  1 - ∑ j ∈ Finset.range (pathLength x + 1),
    memoryEta x q_d j / ((p : ℝ) + 1)

/-- COPY (moved from `PD/Memory.lean`, unchanged): `ν_i(p) = 1/(V_i (p+1) b'_p)`. -/
noncomputable def memoryNu (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (q_d : ℝ) (i : Fin K) (p : ℕ) : ℝ :=
  1 / (bandMass x (a i) * ((p : ℝ) + 1) * memoryBPrime x q_d p)

/-- The point of `ℙ¹(𝔽_p)` of the residue of `z = (z₁,z₂)`, encoded in `Fin (p+1)`:
`Fin.last p` encodes `(1:0)`; otherwise the value of `z₁ z₂⁻¹` in `𝔽_p`.  For a prime `p` and a
primitive `z` this is the projective line `[z]_p` of PD 03:607-609. -/
def projLine (p : ℕ) (z : ℤ × ℤ) : Fin (p + 1) :=
  if ((z.2 : ZMod p) = 0) then Fin.last p
  else ⟨((z.1 : ZMod p) * (z.2 : ZMod p)⁻¹).val % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩

/-- Line data: one point of `ℙ¹(𝔽_p)` for every group prime (PD 03:617-619). -/
abbrev LineData (x : ℝ) (K : ℕ) (a : Fin K → ℝ) :=
  (p : {p : ℕ // p ∈ markedPrimes x K a}) → Fin (p.1 + 1)

/-- In the line model, `p ∣ (gz)₁` means `[z]_p` equals the prescribed kernel line
(PD 03:607-609).  False for non-group primes. -/
def lineHit {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (ℓ : LineData x K a) (p : ℕ) (z : ℤ × ℤ) : Prop :=
  ∃ h : p ∈ markedPrimes x K a, ℓ ⟨p, h⟩ = projLine p z

/-- An archimedean root `(u,v,r)` with real matrix `g = (u, ur; v, vr + 1/u)` (PD 03:620-622). -/
structure ArchRoot where
  u : ℝ
  v : ℝ
  r : ℝ

/-- The root region `[U,16U] × [V,2V] × [0,1]`. -/
def ArchRoot.InRegion (S : PDScale) (w : ArchRoot) : Prop :=
  S.U ≤ w.u ∧ w.u ≤ 16 * S.U ∧ S.V ≤ w.v ∧ w.v ≤ 2 * S.V ∧ 0 ≤ w.r ∧ w.r ≤ 1

/-- `τ(z) = z₁ + r z₂` (PD 03:599). -/
def ArchRoot.tau (w : ArchRoot) (z : ℤ × ℤ) : ℝ := (z.1 : ℝ) + w.r * (z.2 : ℝ)

/-- Box condition `g z ∈ Ω`, using `(gz)₁ = u τ(z)`, `(gz)₂ = v τ(z) + z₂/u` (PD 03:697-701). -/
def envBox (S : PDScale) (w : ArchRoot) (z : ℤ × ℤ) : Prop :=
  S.U ≤ w.u * w.tau z ∧ w.u * w.tau z ≤ 16 * S.U ∧
    S.V ≤ w.v * w.tau z + (z.2 : ℝ) / w.u ∧ w.v * w.tau z + (z.2 : ℝ) / w.u ≤ 2 * S.V

/-- An integral complement `w` of `z` with `det(z,w) = gcd(z₁,z₂)` (Bezout). -/
def complementVec (z : ℤ × ℤ) : ℤ × ℤ := (-(Int.gcdB z.1 z.2), Int.gcdA z.1 z.2)

/-- Transported ratio `r_{gz} = τ(w)/τ(z) mod 1` (det:transported-ratio, PD 03:681-686);
both good tests are invariant under integer shifts of the ratio. -/
def transportedRatio (w : ArchRoot) (z : ℤ × ℤ) : ℝ :=
  w.tau (complementVec z) / w.tau z

/-- Points of the line model: a position `z` and full ordered lists. -/
abbrev EnvPoint (x : ℝ) (K : ℕ) := (ℤ × ℤ) × PrimeLists x K

/-- Validity: `z` primitive, lists of distinct primes from the bands. -/
def EnvValid {K : ℕ} (F : PDFix K) (S : PDScale) (s : EnvPoint S.x K) : Prop :=
  Int.gcd s.1.1 s.1.2 = 1 ∧ ValidPrimeLists S.x K F.a s.2

/-- Number of group primes `p` with `p ∣ (gz)₁` in the line model. -/
def envOmega {K : ℕ} (F : PDFix K) (S : PDScale) (ℓ : LineData S.x K F.a) (z : ℤ × ℤ) : ℕ :=
  ((markedPrimes S.x K F.a).filter (fun p => lineHit ℓ p z)).card

/-- The good tests at a line-model point, at the transported ratio. -/
def envGood {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (s : EnvPoint S.x K) : Prop :=
  IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a s.2 (transportedRatio w s.1)

/-- The diagonal factor `D_env(s)`: box, good tests, active divisibility (every label hits), and
the damping half-factor `q_d^{(ω-KM)/2}`. -/
def envDiag {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (s : EnvPoint S.x K) : ℝ :=
  if EnvValid F S s ∧ envBox S w s.1 ∧ envGood F S w s ∧ ∀ i j, lineHit ℓ (s.2 i j) s.1 then
    Real.rpow F.q_d (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2)
  else 0

/-- Slot symmetrization in the line model. -/
def envSym {K : ℕ} (F : PDFix K) (S : PDScale) (f : EnvPoint S.x K → ℂ) :
    EnvPoint S.x K → ℂ :=
  fun s => ((permCount S.x K : ℂ))⁻¹ *
    ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (s.1, permuteLists σ s.2)

/-- Undamped row operation `𝒯₀` in `z`-coordinates (root-independent). -/
def envRow {K : ℕ} (F : PDFix K) (S : PDScale) (f : EnvPoint S.x K → ℂ) :
    EnvPoint S.x K → ℂ :=
  fun s => ∑' s' : EnvPoint S.x K,
    (if EnvValid F S s' then slotKernel F S s.2 s'.2 (det2 s.1 s'.1) else 0) * f s'

/-- Its adjoint `𝒯₀*`. -/
def envRowAdj {K : ℕ} (F : PDFix K) (S : PDScale) (f : EnvPoint S.x K → ℂ) :
    EnvPoint S.x K → ℂ :=
  fun s => ∑' s' : EnvPoint S.x K,
    (if EnvValid F S s' then star (slotKernel F S s'.2 s.2 (det2 s'.1 s.1)) else 0) * f s'

/-- Multiplication by `D_env`. -/
def envMul {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (f : EnvPoint S.x K → ℂ) : EnvPoint S.x K → ℂ :=
  fun s => (envDiag F S w ℓ s : ℂ) * f s

/-- `𝒜_env = D_env 𝒮 𝒯₀ 𝒮 D_env`. -/
def envOp {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (f : EnvPoint S.x K → ℂ) : EnvPoint S.x K → ℂ :=
  envMul F S w ℓ (envSym F S (envRow F S (envSym F S (envMul F S w ℓ f))))

/-- `𝒜_env* = D_env 𝒮 𝒯₀* 𝒮 D_env`. -/
def envOpAdj {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (f : EnvPoint S.x K → ℂ) : EnvPoint S.x K → ℂ :=
  envMul F S w ℓ (envSym F S (envRowAdj F S (envSym F S (envMul F S w ℓ f))))

/-- Weighted inner product on line-model points (measure `∏ V_i^{-M_J}` times counting). -/
def envInner {K : ℕ} (F : PDFix K) (S : PDScale) (f g : EnvPoint S.x K → ℂ) : ℂ :=
  (physicalMeasure S.x K F.a : ℂ) *
    ∑' s : EnvPoint S.x K, if EnvValid F S s then star (f s) * g s else 0

/-- `𝐮_{e₁}`: one on every list at `z = e₁ = (1,0)`. -/
def e1Vector {x : ℝ} {K : ℕ} : EnvPoint x K → ℂ := fun s => if s.1 = (1, 0) then 1 else 0

/-- The line-model moment `⟨𝐮_{e₁}, (𝒜_env 𝒜_env*)^R 𝐮_{e₁}⟩` at a root and line data. -/
def envMomentC {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℂ :=
  envInner F S e1Vector ((fun f => envOp F S w ℓ (envOpAdj F S w ℓ f))^[S.R] e1Vector)

/-- The completion entry `c ∈ [0,u)` of (det:root-matrix) at a primitive `(u,v)`:
`c ≡ -v⁻¹ (mod u)`, so that `ud - vc = 1` with `d = (1+vc)/u`. -/
def rootC (u v : ℕ) : ℕ := (-((v : ZMod u)⁻¹)).val

/-- Kernel line of the first row `(u,c)` of `g` at `p`: the point `(c : -u)` of `ℙ¹(𝔽_p)`. -/
def kernelLine (p u c : ℕ) : Fin (p + 1) := projLine p ((c : ℤ), -(u : ℤ))

/-- The actual line data of the integer root `(u,v)`. -/
def rootLines {K : ℕ} (F : PDFix K) (S : PDScale) (u v : ℕ) : LineData S.x K F.a :=
  fun p => kernelLine p.1 u (rootC u v)

/-- The normalized physical root average of the line-model moment (PD 03:595-609). -/
def physicalRootAverage {K : ℕ} (F : PDFix K) (S : PDScale) : ℝ :=
  (S.U * S.V)⁻¹ * ∑' uv : ℕ × ℕ,
    if IsOmegaPosition S uv.1 uv.2 then
      (envMomentC F S ⟨(uv.1 : ℝ), (uv.2 : ℝ), (rootC uv.1 uv.2 : ℝ) / (uv.1 : ℝ)⟩
        (rootLines F S uv.1 uv.2)).re
    else 0

/-- Expectation over independent uniform lines at all group primes (PD 03:617-619). -/
def lineAverage {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (G : LineData x K a → ℂ) : ℂ :=
  ((∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1) : ℝ) : ℂ)⁻¹ * ∑ ℓ : LineData x K a, G ℓ

/-- The model: `(1/ζ(2)) ∫ d(u/U) d(v/V) dr` of the line average (PD 03:613-622). -/
def modelRootAverage {K : ℕ} (F : PDFix K) (S : PDScale) : ℝ :=
  (6 / Real.pi ^ 2) *
    ∫ uu in (1 : ℝ)..16, ∫ vv in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      (lineAverage (fun ℓ => envMomentC F S ⟨S.U * uu, S.V * vv, r⟩ ℓ)).re

private lemma rootC_lt_of_pos (u v : ℕ) (hu : 0 < u) : rootC u v < u := by
  letI : NeZero u := ⟨Nat.ne_of_gt hu⟩
  dsimp [rootC]
  exact ZMod.val_lt _

private lemma rootC_modular_completion (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) :
    u ∣ v * rootC u v + 1 := by
  letI : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hinv : (v : ZMod u) * (v : ZMod u)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one v hcop.symm
  have hroot : (rootC u v : ZMod u) = -((v : ZMod u)⁻¹) := by
    dsimp [rootC]
    rw [ZMod.natCast_zmod_val]
  have hz : ((v * rootC u v + 1 : ℕ) : ZMod u) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul, hroot, mul_neg, hinv]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

private lemma rootC_completion_exists (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) :
    ∃ c d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧ 0 ≤ c ∧ c < u := by
  let c := rootC u v
  let d := (v * c + 1) / u
  have hdiv : u ∣ v * c + 1 := by
    simpa [c] using rootC_modular_completion u v hu hcop
  have hmul : d * u = v * c + 1 := by
    dsimp [d]
    exact Nat.div_mul_cancel hdiv
  refine ⟨c, d, ?_, ?_, ?_⟩
  · have hmulZ : (d : ℤ) * (u : ℤ) = (v : ℤ) * (c : ℤ) + 1 := by
      exact_mod_cast hmul
    dsimp [c]
    nlinarith [hmulZ]
  · exact Int.ofNat_nonneg _
  · dsimp [c]
    exact Int.ofNat_lt.mpr (rootC_lt_of_pos u v hu)

private lemma rootC_eq_of_bezout (u v c : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) (hc : c < u)
    (d : ℤ) (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) :
    c = rootC u v := by
  letI : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hinv : (v : ZMod u) * (v : ZMod u)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one v hcop.symm
  have hroot : (rootC u v : ZMod u) = -((v : ZMod u)⁻¹) := by
    dsimp [rootC]
    rw [ZMod.natCast_zmod_val]
  have hInt : (v : ℤ) * c + 1 = (u : ℤ) * d := by
    nlinarith [hdet]
  have hcast := congrArg (fun z : ℤ => (z : ZMod u)) hInt
  have hmul : (v : ZMod u) * (c : ZMod u) + 1 = 0 := by
    simpa [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self] using hcast
  have hinv' : (v : ZMod u)⁻¹ * (v : ZMod u) = 1 := by
    simpa [mul_comm] using hinv
  have hz : (c : ZMod u) = (rootC u v : ZMod u) := by
    have hv_mul_c : (v : ZMod u) * (c : ZMod u) = -1 := by
      linear_combination hmul
    calc
      (c : ZMod u) = 1 * (c : ZMod u) := by simp
      _ = ((v : ZMod u)⁻¹ * (v : ZMod u)) * (c : ZMod u) := by rw [hinv']
      _ = (v : ZMod u)⁻¹ * ((v : ZMod u) * (c : ZMod u)) := by ac_rfl
      _ = (v : ZMod u)⁻¹ * (-1) := by rw [hv_mul_c]
      _ = (rootC u v : ZMod u) := by rw [hroot]; ring
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast_of_lt hc,
    ZMod.val_natCast_of_lt (rootC_lt_of_pos u v hu)] at hval
  exact hval

private lemma root_completion_unique (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) (c d : ℤ) (hc : 0 ≤ c ∧ c < u)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) :
    c = rootC u v ∧ d = ((v * rootC u v + 1) / u : ℕ) := by
  let cn := c.toNat
  have hcn : (cn : ℤ) = c := Int.toNat_of_nonneg hc.1
  have hcnLt : cn < u := (Int.toNat_lt hc.1).2 hc.2
  have hdet' := hdet
  rw [← hcn] at hdet'
  have hcnEq : cn = rootC u v :=
    rootC_eq_of_bezout u v cn hu hcop hcnLt d hdet'
  constructor
  · calc
      c = (cn : ℤ) := hcn.symm
      _ = rootC u v := by exact_mod_cast hcnEq
  · let dn := (v * rootC u v + 1) / u
    have hdiv : u ∣ v * rootC u v + 1 := rootC_modular_completion u v hu hcop
    have hmul : dn * u = v * rootC u v + 1 := by
      dsimp [dn]
      exact Nat.div_mul_cancel hdiv
    have hmulZ : (dn : ℤ) * (u : ℤ) = (v : ℤ) * (rootC u v : ℤ) + 1 := by
      exact_mod_cast hmul
    have hmulInt : (u : ℤ) * (dn : ℤ) = (v : ℤ) * (rootC u v : ℤ) + 1 := by
      simpa [mul_comm] using hmulZ
    have hcnEqInt : (cn : ℤ) = (rootC u v : ℤ) := by exact_mod_cast hcnEq
    have hcEqInt : c = (rootC u v : ℤ) := hcn.symm.trans hcnEqInt
    have hdetRoot : (u : ℤ) * d - (v : ℤ) * (rootC u v : ℤ) = 1 := by
      rw [← hcEqInt]
      exact hdet
    have hdetInt : (u : ℤ) * d = (v : ℤ) * (rootC u v : ℤ) + 1 := by
      linarith [hdetRoot]
    have huInt : (u : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
    have hmulEq : (u : ℤ) * d = (u : ℤ) * (dn : ℤ) := hdetInt.trans hmulInt.symm
    exact mul_left_cancel₀ huInt hmulEq

private noncomputable def rootD (u v : ℕ) : ℕ :=
  (v * rootC u v + 1) / u

private noncomputable def rootCompletionMatrix (Sq u v : ℕ) :
    Matrix (Fin 2) (Fin 2) (ZMod Sq) :=
  !![(u : ZMod Sq), (rootC u v : ZMod Sq); (v : ZMod Sq), (rootD u v : ZMod Sq)]

private lemma rootCompletionMatrix_det (Sq u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) : (rootCompletionMatrix Sq u v).det = 1 := by
  have hdiv : u ∣ v * rootC u v + 1 := rootC_modular_completion u v hu hcop
  have hmul : u * rootD u v = v * rootC u v + 1 := by
    dsimp [rootD]
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hmulMod : (u : ZMod Sq) * (rootD u v : ZMod Sq) =
      (v : ZMod Sq) * (rootC u v : ZMod Sq) + 1 := by
    calc
      (u : ZMod Sq) * (rootD u v : ZMod Sq) =
          ((u * rootD u v : ℕ) : ZMod Sq) := by simp
      _ = ((v * rootC u v + 1 : ℕ) : ZMod Sq) :=
        congrArg (fun n : ℕ => (n : ZMod Sq)) hmul
      _ = (v : ZMod Sq) * (rootC u v : ZMod Sq) + 1 := by simp
  rw [Matrix.det_fin_two]
  change (u : ZMod Sq) * (rootD u v : ZMod Sq) -
    (rootC u v : ZMod Sq) * (v : ZMod Sq) = 1
  rw [hmulMod]
  ring

private def rootTransport (u v c d : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (u * z.1 + c * z.2, v * z.1 + d * z.2)

private def rootTransportInv (u v c d : ℤ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (d * z.1 - c * z.2, -v * z.1 + u * z.2)

private lemma rootTransport_left_inv (u v c d : ℤ) (hdet : u * d - v * c = 1)
    (z : ℤ × ℤ) : rootTransportInv u v c d (rootTransport u v c d z) = z := by
  apply Prod.ext
  · change d * (u * z.1 + c * z.2) - c * (v * z.1 + d * z.2) = z.1
    calc
      d * (u * z.1 + c * z.2) - c * (v * z.1 + d * z.2) =
          (u * d - v * c) * z.1 := by ring
      _ = z.1 := by rw [hdet]; ring
  · change -v * (u * z.1 + c * z.2) + u * (v * z.1 + d * z.2) = z.2
    calc
      -v * (u * z.1 + c * z.2) + u * (v * z.1 + d * z.2) =
          (u * d - v * c) * z.2 := by ring
      _ = z.2 := by rw [hdet]; ring

private lemma rootTransport_right_inv (u v c d : ℤ) (hdet : u * d - v * c = 1)
    (z : ℤ × ℤ) : rootTransport u v c d (rootTransportInv u v c d z) = z := by
  apply Prod.ext
  · change u * (d * z.1 - c * z.2) + c * (-v * z.1 + u * z.2) = z.1
    calc
      u * (d * z.1 - c * z.2) + c * (-v * z.1 + u * z.2) =
          (u * d - v * c) * z.1 := by ring
      _ = z.1 := by rw [hdet]; ring
  · change v * (d * z.1 - c * z.2) + d * (-v * z.1 + u * z.2) = z.2
    calc
      v * (d * z.1 - c * z.2) + d * (-v * z.1 + u * z.2) =
          (u * d - v * c) * z.2 := by ring
      _ = z.2 := by rw [hdet]; ring

private lemma det2_rootTransport (u v c d : ℤ) (hdet : u * d - v * c = 1)
    (z z' : ℤ × ℤ) :
    det2 (rootTransport u v c d z) (rootTransport u v c d z') = det2 z z' := by
  unfold det2 rootTransport
  calc
    (u * z.1 + c * z.2) * (v * z'.1 + d * z'.2) -
        (v * z.1 + d * z.2) * (u * z'.1 + c * z'.2) =
      (u * d - v * c) * (z.1 * z'.2 - z.2 * z'.1) := by ring
    _ = z.1 * z'.2 - z.2 * z'.1 := by rw [hdet]; ring

private lemma gcd_rootTransport (u v c d : ℤ) (hdet : u * d - v * c = 1)
    (z : ℤ × ℤ) :
    Int.gcd (rootTransport u v c d z).1 (rootTransport u v c d z).2 =
      Int.gcd z.1 z.2 := by
  apply Nat.dvd_antisymm
  · have h1 := Int.gcd_dvd_left (rootTransport u v c d z).1
      (rootTransport u v c d z).2
    have h2 := Int.gcd_dvd_right (rootTransport u v c d z).1
      (rootTransport u v c d z).2
    have hinv := rootTransport_left_inv u v c d hdet z
    have hinv1 : d * (rootTransport u v c d z).1 -
        c * (rootTransport u v c d z).2 = z.1 := by
      simpa [rootTransportInv] using congrArg Prod.fst hinv
    have hinv2 : -v * (rootTransport u v c d z).1 +
        u * (rootTransport u v c d z).2 = z.2 := by
      simpa [rootTransportInv] using congrArg Prod.snd hinv
    have hz1 : ((Int.gcd (rootTransport u v c d z).1
        (rootTransport u v c d z).2 : ℕ) : ℤ) ∣ z.1 := by
      simpa only [hinv1] using
        (dvd_sub (dvd_mul_of_dvd_right h1 d) (dvd_mul_of_dvd_right h2 c))
    have hz2 : ((Int.gcd (rootTransport u v c d z).1
        (rootTransport u v c d z).2 : ℕ) : ℤ) ∣ z.2 := by
      have hneg : ((Int.gcd (rootTransport u v c d z).1
          (rootTransport u v c d z).2 : ℕ) : ℤ) ∣
          -v * (rootTransport u v c d z).1 := by
        simpa [mul_comm] using dvd_mul_of_dvd_left h1 (-v)
      simpa only [hinv2] using dvd_add hneg (dvd_mul_of_dvd_right h2 u)
    exact Nat.dvd_gcd (Int.natCast_dvd.mp hz1) (Int.natCast_dvd.mp hz2)
  · have h1 := Int.gcd_dvd_left z.1 z.2
    have h2 := Int.gcd_dvd_right z.1 z.2
    have ht1 : ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣
        (rootTransport u v c d z).1 := by
      change ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣ u * z.1 + c * z.2
      exact dvd_add (dvd_mul_of_dvd_right h1 u) (dvd_mul_of_dvd_right h2 c)
    have ht2 : ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣
        (rootTransport u v c d z).2 := by
      change ((Int.gcd z.1 z.2 : ℕ) : ℤ) ∣ v * z.1 + d * z.2
      exact dvd_add (dvd_mul_of_dvd_right h1 v) (dvd_mul_of_dvd_right h2 d)
    exact Nat.dvd_gcd (Int.natCast_dvd.mp ht1) (Int.natCast_dvd.mp ht2)

private lemma rootD_completion_identity (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) :
    (u : ℤ) * (rootD u v : ℤ) - (v : ℤ) * (rootC u v : ℤ) = 1 := by
  have hdiv : u ∣ v * rootC u v + 1 := rootC_modular_completion u v hu hcop
  have hmul : u * rootD u v = v * rootC u v + 1 := by
    dsimp [rootD]
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdiv
  have hmulZ : (u : ℤ) * (rootD u v : ℤ) =
      (v : ℤ) * (rootC u v : ℤ) + 1 := by exact_mod_cast hmul
  rw [hmulZ]
  ring

private lemma rootTransport_first_real (u v : ℕ) (hu : 0 < u)
    (z : ℤ × ℤ) :
    ((rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ) z).1 : ℝ) =
      (u : ℝ) * ((z.1 : ℝ) + ((rootC u v : ℝ) / (u : ℝ)) * (z.2 : ℝ)) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  unfold rootTransport
  push_cast
  field_simp [huR]

private lemma rootTransport_second_real (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) (z : ℤ × ℤ) :
    ((rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ) z).2 : ℝ) =
      (v : ℝ) * ((z.1 : ℝ) + ((rootC u v : ℝ) / (u : ℝ)) * (z.2 : ℝ)) +
        (z.2 : ℝ) / (u : ℝ) := by
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  have hdet := rootD_completion_identity u v hu hcop
  have hdetR : (u : ℝ) * (rootD u v : ℝ) -
      (v : ℝ) * (rootC u v : ℝ) = 1 := by exact_mod_cast hdet
  have hmulR : (u : ℝ) * (rootD u v : ℝ) =
      (v : ℝ) * (rootC u v : ℝ) + 1 := by linarith [hdetR]
  have hzmul := congrArg (fun t : ℝ => t * (z.2 : ℝ)) hmulR
  unfold rootTransport
  push_cast
  field_simp [huR]
  nlinarith [hzmul]

private lemma circleDistance_int_shift (t : ℝ) (k : ℤ) :
    circleDistance (t + (k : ℝ)) = circleDistance t := by
  have hrange :
      Set.range (fun n : ℤ => |(t + (k : ℝ)) - (n : ℝ)|) =
        Set.range (fun n : ℤ => |t - (n : ℝ)|) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n - k, ?_⟩
      congr 1
      push_cast
      ring
    · rintro ⟨n, rfl⟩
      refine ⟨n + k, ?_⟩
      congr 1
      push_cast
      ring
  unfold circleDistance
  rw [hrange]

private lemma circleDistance_intMul_shift (m : ℤ) (t : ℝ) (k : ℤ) :
    circleDistance ((m : ℝ) * (t + (k : ℝ))) =
      circleDistance ((m : ℝ) * t) := by
  rw [mul_add]
  have hmk : (m : ℝ) * (k : ℝ) = ((m * k : ℤ) : ℝ) := by simp
  rw [hmk, circleDistance_int_shift]

private lemma goodTestOne_int_shift (x Y d₀ : ℝ) {K : ℕ}
    (p : PrimeLists x K) (r : ℝ) (k : ℤ) :
    goodTestOne x Y d₀ p (r + (k : ℝ)) ↔ goodTestOne x Y d₀ p r := by
  unfold goodTestOne
  constructor <;> intro h omitted hD hD' l hl hly
  · have hh := h omitted hD hD' l hl hly
    have hm : (((l * omissionProduct p omitted : ℕ) : ℤ) : ℝ) =
        (l : ℝ) * (omissionProduct p omitted : ℝ) := by norm_num
    rw [← hm, circleDistance_intMul_shift] at hh
    simpa [hm] using hh
  · have hh := h omitted hD hD' l hl hly
    have hm : (((l * omissionProduct p omitted : ℕ) : ℤ) : ℝ) =
        (l : ℝ) * (omissionProduct p omitted : ℝ) := by norm_num
    rw [← hm, circleDistance_intMul_shift]
    simpa [hm] using hh

private lemma circleDistance_natSub_int_shift (n₁ n₂ : ℕ) (r : ℝ) (k : ℤ) :
    circleDistance (((n₁ : ℝ) - (n₂ : ℝ)) * (r + (k : ℝ))) =
      circleDistance (((n₁ : ℝ) - (n₂ : ℝ)) * r) := by
  convert circleDistance_intMul_shift ((n₁ : ℤ) - (n₂ : ℤ)) r k using 1 <;> norm_cast

private lemma goodTestTwo_int_shift (x d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) (r : ℝ) (k : ℤ) :
    goodTestTwo x d₀ K a p (r + (k : ℝ)) ↔ goodTestTwo x d₀ K a p r := by
  unfold goodTestTwo
  constructor <;> intro h I hI
  · simpa only [circleDistance_natSub_int_shift] using h I hI
  · simpa only [circleDistance_natSub_int_shift] using h I hI

private lemma isGoodRatio_int_shift (x Y d₀ : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (r : ℝ) (k : ℤ) :
    IsGoodRatio x Y d₀ K a p (r + (k : ℝ)) ↔ IsGoodRatio x Y d₀ K a p r := by
  unfold IsGoodRatio
  rw [goodTestOne_int_shift, goodTestTwo_int_shift]

private lemma complements_differ_by_root (u v c₁ d₁ c₂ d₂ : ℤ)
    (hu : u ≠ 0) (hcop : Int.gcd u v = 1)
    (h₁ : u * d₁ - v * c₁ = 1) (h₂ : u * d₂ - v * c₂ = 1) :
    ∃ k : ℤ, c₂ = c₁ + k * u ∧ d₂ = d₁ + k * v := by
  let x := c₂ - c₁
  let y := d₂ - d₁
  have hxy : u * y = v * x := by
    dsimp [x, y]
    linear_combination h₂ - h₁
  have hdiv : u ∣ x := by
    apply Int.dvd_of_dvd_mul_left_of_gcd_one _ hcop
    have huxv : u ∣ v * x := by
      rw [← hxy]
      exact dvd_mul_right u y
    simpa [mul_comm] using huxv
  let k := x / u
  have hx : x = u * k := by
    dsimp [k]
    simpa [mul_comm] using (Int.ediv_mul_cancel hdiv).symm
  have hy' : u * y = u * (v * k) := by
    calc
      u * y = v * x := hxy
      _ = v * (u * k) := by rw [hx]
      _ = u * (v * k) := by ring
  have hy : y = v * k := mul_left_cancel₀ hu hy'
  refine ⟨k, ?_, ?_⟩
  · dsimp [x] at hx
    linear_combination hx
  · dsimp [y] at hy
    linear_combination hy

private lemma rootTransport_e1 (u v : ℕ) :
    rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ) (1, 0) =
      ((u : ℤ), (v : ℤ)) := by
  simp [rootTransport]

private lemma projLine_ne_last_of_snd_ne_zero (p : ℕ) (hp : p.Prime)
    (z : ℤ × ℤ) (hz : (z.2 : ZMod p) ≠ 0) :
    projLine p z ≠ Fin.last p := by
  letI : Fact p.Prime := ⟨hp⟩
  intro h
  let s : ZMod p := (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹
  have hslt : s.val < p := ZMod.val_lt s
  have hmod : s.val % (p + 1) = s.val :=
    Nat.mod_eq_of_lt (lt_trans hslt (Nat.lt_succ_self p))
  have hval := congrArg Fin.val h
  simp only [projLine, if_neg hz, Fin.val_mk, Fin.val_last] at hval
  change s.val % (p + 1) = p at hval
  rw [hmod] at hval
  omega

private lemma projLine_eq_last_iff (p : ℕ) (hp : p.Prime) (z : ℤ × ℤ) :
    projLine p z = Fin.last p ↔ (z.2 : ZMod p) = 0 := by
  by_cases hz : (z.2 : ZMod p) = 0
  · simp [projLine, hz]
  · constructor
    · intro h
      exact (projLine_ne_last_of_snd_ne_zero p hp z hz) h |>.elim
    · intro h
      exact (hz h).elim

private lemma projLine_eq_finite_cross_iff (p : ℕ) (hp : p.Prime)
    (z w : ℤ × ℤ) (hz : (z.2 : ZMod p) ≠ 0) (hw : (w.2 : ZMod p) ≠ 0) :
    projLine p z = projLine p w ↔
      (z.1 : ZMod p) * (w.2 : ZMod p) =
        (w.1 : ZMod p) * (z.2 : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  let a : ZMod p := (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹
  let b : ZMod p := (w.1 : ZMod p) * (w.2 : ZMod p)⁻¹
  have ha : a.val % (p + 1) = a.val :=
    Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt a) (Nat.lt_succ_self p))
  have hb : b.val % (p + 1) = b.val :=
    Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt b) (Nat.lt_succ_self p))
  have hza : (projLine p z).val = a.val := by
    simp [projLine, hz, a, ha]
  have hwb : (projLine p w).val = b.val := by
    simp [projLine, hw, b, hb]
  have hproj : projLine p z = projLine p w ↔ a = b := by
    constructor
    · intro h
      apply ZMod.val_injective p
      simpa [hza, hwb] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      rw [hza, hwb]
      exact congrArg ZMod.val h
  rw [hproj]
  constructor
  · intro h
    dsimp [a, b] at h
    calc
      (z.1 : ZMod p) * (w.2 : ZMod p) =
          ((z.1 : ZMod p) * (z.2 : ZMod p)⁻¹) *
            ((z.2 : ZMod p) * (w.2 : ZMod p)) := by field_simp [hz, hw]
      _ = ((w.1 : ZMod p) * (w.2 : ZMod p)⁻¹) *
            ((z.2 : ZMod p) * (w.2 : ZMod p)) := by rw [h]
      _ = (w.1 : ZMod p) * (z.2 : ZMod p) := by field_simp [hz, hw]
  · intro h
    dsimp [a, b]
    calc
      (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
          ((z.1 : ZMod p) * (w.2 : ZMod p)) *
            ((z.2 : ZMod p) * (w.2 : ZMod p))⁻¹ := by field_simp [hz, hw]
      _ = ((w.1 : ZMod p) * (z.2 : ZMod p)) *
            ((z.2 : ZMod p) * (w.2 : ZMod p))⁻¹ := by rw [h]
      _ = (w.1 : ZMod p) * (w.2 : ZMod p)⁻¹ := by field_simp [hz, hw]

private lemma primitive_pair_not_zero_mod (p : ℕ) (hp : p.Prime)
    (z : ℤ × ℤ) (hprim : Int.gcd z.1 z.2 = 1) :
    (z.1 : ZMod p) ≠ 0 ∨ (z.2 : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hz₁ : (z.1 : ZMod p) = 0
  · by_cases hz₂ : (z.2 : ZMod p) = 0
    · have hgcd : ((Int.gcd z.1 z.2 : ℕ) : ℤ) = 1 := by exact_mod_cast hprim
      have hbez := Int.gcd_eq_gcd_ab z.1 z.2
      rw [hgcd] at hbez
      have hcast := congrArg (fun n : ℤ => (n : ZMod p)) hbez
      simp [hz₁, hz₂] at hcast
    · exact Or.inr hz₂
  · exact Or.inl hz₁

private lemma projLine_eq_kernel_iff (p u c : ℕ) (z : ℤ × ℤ)
    (hp : p.Prime) (hprim : Int.gcd z.1 z.2 = 1)
    (hrow : (u : ZMod p) ≠ 0 ∨ (c : ZMod p) ≠ 0) :
    projLine p z = kernelLine p u c ↔
      (u : ZMod p) * (z.1 : ZMod p) + (c : ZMod p) * (z.2 : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hzvec := primitive_pair_not_zero_mod p hp z hprim
  by_cases hu : (u : ZMod p) = 0
  · have hc : (c : ZMod p) ≠ 0 := by
      rcases hrow with hrow | hrow
      · exact (hrow hu).elim
      · exact hrow
    have hkernel : kernelLine p u c = Fin.last p := by
      simp [kernelLine, projLine, hu]
    have hline := projLine_eq_last_iff p hp z
    have hdot : (u : ZMod p) * (z.1 : ZMod p) +
        (c : ZMod p) * (z.2 : ZMod p) = 0 ↔ (z.2 : ZMod p) = 0 := by
      rw [hu]
      simp [hc]
    rw [hkernel]
    exact hline.trans hdot.symm
  · have hkernelSecond : (((c : ℤ), -(u : ℤ)).2 : ZMod p) ≠ 0 := by
      simpa using (neg_ne_zero.mpr hu)
    by_cases hz₂ : (z.2 : ZMod p) = 0
    · have hz₁ : (z.1 : ZMod p) ≠ 0 := by
        rcases hzvec with hz₁ | hz₂'
        · exact hz₁
        · exact (hz₂' hz₂).elim
      have hlast : projLine p z = Fin.last p := (projLine_eq_last_iff p hp z).2 hz₂
      have hkernelNe : kernelLine p u c ≠ Fin.last p :=
        projLine_ne_last_of_snd_ne_zero p hp ((c : ℤ), -(u : ℤ)) hkernelSecond
      have hleft : ¬ projLine p z = kernelLine p u c := by
        intro h
        exact hkernelNe (h.symm.trans hlast)
      have hright :
          ¬((u : ZMod p) * (z.1 : ZMod p) + (c : ZMod p) * (z.2 : ZMod p) = 0) := by
        have hmul : (u : ZMod p) * (z.1 : ZMod p) ≠ 0 := mul_ne_zero hu hz₁
        simpa [hz₂] using hmul
      constructor
      · intro h
        exact False.elim (hleft h)
      · intro h
        exact False.elim (hright h)
    · have hcross := projLine_eq_finite_cross_iff p hp z
        ((c : ℤ), -(u : ℤ)) hz₂ hkernelSecond
      have hcross' : projLine p z = kernelLine p u c ↔
          (z.1 : ZMod p) * (-(u : ZMod p)) =
            (c : ZMod p) * (z.2 : ZMod p) := by
        simpa [kernelLine, Int.cast_neg] using hcross
      rw [hcross']
      have halg : (z.1 : ZMod p) * (-(u : ZMod p)) =
          (c : ZMod p) * (z.2 : ZMod p) ↔
          (u : ZMod p) * (z.1 : ZMod p) +
            (c : ZMod p) * (z.2 : ZMod p) = 0 := by
        constructor
        · intro h
          have h' : -((u : ZMod p) * (z.1 : ZMod p)) =
              (c : ZMod p) * (z.2 : ZMod p) := by
            simpa [mul_comm] using h
          rw [← h']
          ring
        · intro h
          have h' : -((u : ZMod p) * (z.1 : ZMod p)) =
              (c : ZMod p) * (z.2 : ZMod p) := by
            rw [eq_comm, eq_neg_iff_add_eq_zero]
            simpa [add_comm] using h
          simpa [mul_comm] using h'
      rw [halg]

private lemma rootLineHit_iff_dvd (K : ℕ) (F : PDFix K) (S : PDScale)
    (u v p : ℕ) (z : ℤ × ℤ) (hpMem : p ∈ markedPrimes S.x K F.a)
    (hp : p.Prime) (hu : 0 < u) (hcop : Nat.Coprime u v)
    (hprim : Int.gcd z.1 z.2 = 1) :
    lineHit (rootLines F S u v) p z ↔
      (p : ℤ) ∣ (rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ)
        (rootD u v : ℤ) z).1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdet := rootD_completion_identity u v hu hcop
  have hdetCast : (u : ZMod p) * (rootD u v : ZMod p) -
      (v : ZMod p) * (rootC u v : ZMod p) = 1 := by
    simpa [Int.cast_sub, Int.cast_mul] using
      congrArg (fun n : ℤ => (n : ZMod p)) hdet
  have hrow : (u : ZMod p) ≠ 0 ∨ (rootC u v : ZMod p) ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (u : ZMod p) * (rootD u v : ZMod p) -
        (v : ZMod p) * (rootC u v : ZMod p) = 0 := by simp [h.1, h.2]
    have h01 : (0 : ZMod p) = 1 := hzero.symm.trans hdetCast
    exact zero_ne_one h01
  have hline : lineHit (rootLines F S u v) p z ↔
      projLine p z = kernelLine p u (rootC u v) := by
    constructor
    · rintro ⟨hmem, hval⟩
      have hval' := hval.symm
      simpa [rootLines] using hval'
    · intro hval
      refine ⟨hpMem, ?_⟩
      simpa [rootLines] using hval.symm
  have hproj := projLine_eq_kernel_iff p u (rootC u v) z hp hprim hrow
  have hcoordinate :
      (u : ZMod p) * (z.1 : ZMod p) + (rootC u v : ZMod p) * (z.2 : ZMod p) =
        ((rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ)
          (rootD u v : ℤ) z).1 : ZMod p) := by
    simp [rootTransport, Int.cast_add, Int.cast_mul]
  calc
    lineHit (rootLines F S u v) p z ↔ projLine p z = kernelLine p u (rootC u v) := hline
    _ ↔ (u : ZMod p) * (z.1 : ZMod p) +
          (rootC u v : ZMod p) * (z.2 : ZMod p) = 0 := hproj
    _ ↔ ((rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ)
          (rootD u v : ℤ) z).1 : ZMod p) = 0 := by rw [hcoordinate]
    _ ↔ (p : ℤ) ∣ (rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ)
          (rootD u v : ℤ) z).1 := ZMod.intCast_zmod_eq_zero_iff_dvd _ _

private lemma rootCompletionMatrix_kernelLine (Sq p u v : ℕ) (hSq : 0 < Sq)
    (hp : p ∣ Sq) :
    kernelLine p ((rootCompletionMatrix Sq u v 0 0).val % p)
        ((rootCompletionMatrix Sq u v 0 1).val % p) = kernelLine p u (rootC u v) := by
  have hU : (rootCompletionMatrix Sq u v 0 0).val % p = u % p := by
    simp [rootCompletionMatrix, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hp]
  have hC : (rootCompletionMatrix Sq u v 0 1).val % p = rootC u v % p := by
    simp [rootCompletionMatrix, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hp]
  rw [hU, hC]
  simp [kernelLine, projLine]


/-! ### Path terms of the line-model moment -/

/-- A path of `N+1` line-model points (visits `0,…,N`). -/
abbrev EnvPath (x : ℝ) (K : ℕ) := Fin (pathLength x + 1) → EnvPoint x K

/-- Kernel of `𝒮𝒯₀𝒮` (`forward = true`) or `𝒮𝒯₀*𝒮` between two points. -/
def symKernel {K : ℕ} (F : PDFix K) (S : PDScale) (forward : Bool)
    (s s' : EnvPoint S.x K) : ℂ :=
  ((permCount S.x K : ℂ))⁻¹ ^ 2 *
    ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        if forward then
          slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
        else star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2) (det2 s'.1 s.1))

/-- Admissible paths: valid points, `z₀ = z_N = e₁`. -/
def IsEnvPathAdmissible {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) : Prop :=
  (∀ j, EnvValid F S (γ j)) ∧ (γ 0).1 = (1, 0) ∧ (γ (Fin.last _)).1 = (1, 0)

/-- Root- and line-independent path coefficient: measure times the `N` symmetrized kernels,
alternating `𝒜` (even edges) and `𝒜*` (odd edges). -/
def pathCoefficient {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) : ℂ :=
  (physicalMeasure S.x K F.a : ℂ) *
    ∏ j : Fin (pathLength S.x), symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)

/-- Archimedean factor: box and good tests at every visit. -/
def pathArch {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K) : ℝ :=
  ∏ j, if envBox S w (γ j).1 ∧ envGood F S w (γ j) then 1 else 0

/-- `p` is active at visit `j` (it occurs in the lists). -/
def IsActiveAt {x : ℝ} {K : ℕ} (γ : EnvPath x K) (p : ℕ) (j : Fin (pathLength x + 1)) : Prop :=
  ∃ i jj, (γ j).2 i jj = p

/-- The factor of one group prime at line `λ` (mem:prime-factor, PD 04:68-80):
`∏_{j active} 1[λ=[z_j]_p] · ∏_{j inactive} (1 - η'_j 1[λ=[z_j]_p])`. -/
def pathPrimeFactor {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (lam : Fin (p + 1)) : ℝ :=
  ∏ j : Fin (pathLength S.x + 1),
    if IsActiveAt γ p j then (if lam = projLine p (γ j).1 then 1 else 0)
    else 1 - memoryEta S.x F.q_d j.val * (if lam = projLine p (γ j).1 then 1 else 0)

private lemma envBoxValid_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) :
    {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1}.Finite := by
  classical
  by_cases hu : w.u = 0
  · have hempty :
        {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨_, hbox⟩
        have hUle : S.U ≤ 0 := by simpa [envBox, hu] using hbox.1
        exact (not_le_of_gt hU) hUle
      · intro h
        exact h.elim
    simpa [hempty]
  · have huAbs : 0 < |w.u| := abs_pos.mpr hu
    let Bτ : ℝ := (16 * S.U) / |w.u|
    let B₂ : ℝ := 2 * |w.u| * S.V + 16 * |w.v| * S.U
    let B₁ : ℝ := Bτ + |w.r| * B₂
    have hcoords (s : EnvPoint S.x K) (hs : EnvValid F S s ∧ envBox S w s.1) :
        |(s.1.1 : ℝ)| ≤ B₁ ∧ |(s.1.2 : ℝ)| ≤ B₂ := by
      rcases hs.2 with ⟨hbox₁, hbox₂, hbox₃, hbox₄⟩
      have hprodNonneg : 0 ≤ w.u * w.tau s.1 := hU.le.trans hbox₁
      have hτMul : |w.u| * |w.tau s.1| ≤ 16 * S.U := by
        have hEq : |w.u| * |w.tau s.1| = w.u * w.tau s.1 := by
          rw [← abs_mul, abs_of_nonneg hprodNonneg]
        rw [hEq]
        exact hbox₂
      have hτ : |w.tau s.1| ≤ Bτ := by
        dsimp [Bτ]
        apply (le_div_iff₀ huAbs).2
        calc
          |w.tau s.1| * |w.u| = |w.u| * |w.tau s.1| := by ring
          _ ≤ 16 * S.U := hτMul
      have hyPos : 0 < w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u := hV.trans_le hbox₃
      have hyAbs : |w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u| ≤ 2 * S.V := by
        rw [abs_of_nonneg hyPos.le]
        exact hbox₄
      have hz₂div : |(s.1.2 : ℝ) / w.u| ≤ 2 * S.V + |w.v| * Bτ := by
        have hEq : (s.1.2 : ℝ) / w.u =
            (w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u) - w.v * w.tau s.1 := by ring
        have hAbsEq := congrArg (fun x : ℝ => |x|) hEq
        calc
          |(s.1.2 : ℝ) / w.u| =
              |(w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u) - w.v * w.tau s.1| := hAbsEq
          _ ≤ |w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u| + |w.v * w.tau s.1| := by
            calc
              |w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u - w.v * w.tau s.1| ≤
                  |w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u - 0| +
                    |0 - w.v * w.tau s.1| := abs_sub_le _ _ _
              _ = |w.v * w.tau s.1 + (s.1.2 : ℝ) / w.u| + |w.v * w.tau s.1| := by simp
          _ ≤ 2 * S.V + |w.v| * Bτ := by
            rw [abs_mul]
            exact add_le_add hyAbs
              (mul_le_mul_of_nonneg_left hτ (abs_nonneg _))
      have hz₂eq : (s.1.2 : ℝ) = ((s.1.2 : ℝ) / w.u) * w.u := by
        field_simp [hu]
      have hz₂ : |(s.1.2 : ℝ)| ≤ B₂ := by
        rw [hz₂eq, abs_mul]
        calc
          |(s.1.2 : ℝ) / w.u| * |w.u| ≤
              (2 * S.V + |w.v| * Bτ) * |w.u| :=
            mul_le_mul_of_nonneg_right hz₂div (abs_nonneg _)
          _ = B₂ := by
            dsimp [B₂, Bτ]
            have huAbsNe : |w.u| ≠ 0 := ne_of_gt huAbs
            field_simp [huAbsNe]
      have hz₁eq : (s.1.1 : ℝ) = w.tau s.1 - w.r * (s.1.2 : ℝ) := by
        simp [ArchRoot.tau]
      have hz₁ : |(s.1.1 : ℝ)| ≤ B₁ := by
        calc
          |(s.1.1 : ℝ)| = |w.tau s.1 - w.r * (s.1.2 : ℝ)| := by rw [hz₁eq]
          _ ≤ |w.tau s.1| + |w.r * (s.1.2 : ℝ)| := by
            calc
              |w.tau s.1 - w.r * (s.1.2 : ℝ)| ≤
                  |w.tau s.1 - 0| + |0 - w.r * (s.1.2 : ℝ)| := abs_sub_le _ _ _
              _ = |w.tau s.1| + |w.r * (s.1.2 : ℝ)| := by simp
          _ = |w.tau s.1| + |w.r| * |(s.1.2 : ℝ)| := by rw [abs_mul]
          _ ≤ B₁ := by
            dsimp [B₁]
            exact add_le_add hτ (mul_le_mul_of_nonneg_left hz₂ (abs_nonneg _))
      exact ⟨hz₁, hz₂⟩
    have hB₂ : 0 ≤ B₂ := by dsimp [B₂]; positivity
    have hB₁ : 0 ≤ B₁ := by dsimp [B₁]; positivity
    let q₁ : ℕ := ⌊B₁⌋₊ + 1
    let q₂ : ℕ := ⌊B₂⌋₊ + 1
    have hq₁Real : B₁ < (q₁ : ℝ) := by
      dsimp [q₁]
      have h := Nat.lt_floor_add_one B₁
      push_cast at h ⊢
      exact h
    have hq₂Real : B₂ < (q₂ : ℝ) := by
      dsimp [q₂]
      have h := Nat.lt_floor_add_one B₂
      push_cast at h ⊢
      exact h
    have hcoord_mem (q : ℕ) (B : ℝ) (hB : B < (q : ℝ))
        (z : ℤ) (hz : |(z : ℝ)| ≤ B) : z ∈ Finset.Icc (-q : ℤ) q := by
      have hq : B ≤ (q : ℝ) := hB.le
      have hz' := abs_le.mp hz
      apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (show -(q : ℝ) ≤ (z : ℝ) by linarith)
      · exact_mod_cast (show (z : ℝ) ≤ (q : ℝ) by linarith)
    let Labels : Type := {p : ℕ // p ∈ markedPrimes S.x K F.a}
    let Code : Type :=
      ((↥(Finset.Icc (-q₁ : ℤ) q₁) × ↥(Finset.Icc (-q₂ : ℤ) q₂)) ×
        (Fin K → Fin (slotCount S.x) → Labels))
    let encode : {s : EnvPoint S.x K // EnvValid F S s ∧ envBox S w s.1} → Code :=
      fun s =>
        ((⟨s.1.1.1, hcoord_mem q₁ B₁ hq₁Real _ (hcoords s.1 s.2).1⟩,
          ⟨s.1.1.2, hcoord_mem q₂ B₂ hq₂Real _ (hcoords s.1 s.2).2⟩),
          fun i j =>
            ⟨s.1.2 i j, by
              have hBand := s.2.1.2.1 i j
              have hmem : s.1.2 i j ∈ primeBand S.x (F.a i) := hBand.2
              change s.1.2 i j ∈ Finset.univ.biUnion (fun i => primeBand S.x (F.a i))
              exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩⟩)
    have hencode : Function.Injective encode := by
      intro s s' heq
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · exact congrArg (fun c => c.1.1.val) heq
        · exact congrArg (fun c => c.1.2.val) heq
      · funext i j
        exact congrArg Subtype.val (congrArg (fun c => c.2 i j) heq)
    exact Finite.of_injective encode hencode

private lemma envDiag_support_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V) :
    (Function.support (envDiag F S w ℓ)).Finite := by
  apply (envBoxValid_finite F S w hU hV).subset
  intro s hs
  have hdiag : envDiag F S w ℓ s ≠ 0 := by
    simpa [Function.mem_support] using hs
  by_contra h
  have hnot : ¬ (EnvValid F S s ∧ envBox S w s.1) := by
    simpa only [Set.mem_setOf_eq] using h
  have hcond : ¬ (EnvValid F S s ∧ envBox S w s.1 ∧ envGood F S w s ∧
      (∀ i j, lineHit ℓ (s.2 i j) s.1)) := by
    intro hc
    exact hnot ⟨hc.1, hc.2.1⟩
  apply hdiag
  unfold envDiag
  rw [if_neg hcond]

private lemma envMul_support_subset {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ) :
    Function.support (envMul F S w ℓ f) ⊆
      {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1} := by
  intro s hs
  have hmul : envMul F S w ℓ f s ≠ 0 := by
    simpa [Function.mem_support] using hs
  have hdiag : envDiag F S w ℓ s ≠ 0 := by
    by_contra hzero
    apply hmul
    simp [envMul, hzero]
  have hbox : EnvValid F S s ∧ envBox S w s.1 := by
    by_contra h
    have hnot : ¬ (EnvValid F S s ∧ envBox S w s.1) := by
      simpa only [Set.mem_setOf_eq] using h
    have hcond : ¬ (EnvValid F S s ∧ envBox S w s.1 ∧ envGood F S w s ∧
        (∀ i j, lineHit ℓ (s.2 i j) s.1)) := by
      intro hc
      exact hnot ⟨hc.1, hc.2.1⟩
    apply hdiag
    unfold envDiag
    rw [if_neg hcond]
  exact hbox

private lemma omissionProduct_permuteLists {x : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (omitted : Fin K → Fin (slotCount x)) :
    omissionProduct (permuteLists σ p) omitted =
      omissionProduct p (fun i => σ i (omitted i)) := by
  classical
  unfold omissionProduct
  apply Finset.prod_congr rfl
  intro i hi
  change (∏ j : Fin (slotCount x),
      if j ≠ omitted i then p i (σ i j) else 1) =
    ∏ j : Fin (slotCount x), if j ≠ σ i (omitted i) then p i j else 1
  apply Fintype.prod_equiv (σ i)
  intro j
  by_cases h : j = omitted i
  · subst j
    simp
  · have hmap : σ i j ≠ σ i (omitted i) := by
      intro heq
      exact h ((σ i).injective heq)
    simp [h, hmap]

private lemma validPrimeLists_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (hp : ValidPrimeLists x K a p) : ValidPrimeLists x K a (permuteLists σ p) := by
  rcases hp with ⟨hband, hdistinct⟩
  constructor
  · intro i j
    simpa [permuteLists] using hband i (σ i j)
  · intro i j j' hj
    apply hdistinct i (σ i j) (σ i j')
    intro heq
    exact hj ((σ i).injective heq)

private lemma goodnessTrialValue_permute {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (d₀ : ℝ) (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ) :
    IsGoodnessTrialValue a (permuteLists σ p) d₀ I iStar fresh n ↔
      IsGoodnessTrialValue a p d₀ I iStar fresh n := by
  constructor
  · rintro ⟨omitted, z, hn, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    refine ⟨omitted', z, ?_, ?_, ?_, hz⟩
    · simpa [omitted', omissionProduct_permuteLists] using hn
    · simpa [omitted', omissionProduct_permuteLists] using hlo
    · simpa [omitted', omissionProduct_permuteLists] using hhi
  · rintro ⟨omitted, z, hn, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    refine ⟨omitted', z, ?_, ?_, ?_, hz⟩
    · simpa [omitted', omissionProduct_permuteLists] using hn
    · simpa [omitted', omissionProduct_permuteLists] using hlo
    · simpa [omitted', omissionProduct_permuteLists] using hhi

private lemma goodTestOne_permute {x Y d₀ : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestOne x Y d₀ (permuteLists σ p) r ↔ goodTestOne x Y d₀ p r := by
  constructor
  · intro h omitted hlo hhi l hl₀ hl₁
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    have hprod : omissionProduct (permuteLists σ p) omitted' = omissionProduct p omitted := by
      simpa [omitted', omissionProduct_permuteLists]
    have hlo' : d₀ ≤ (omissionProduct (permuteLists σ p) omitted' : ℝ) := by
      rw [hprod]
      exact hlo
    have hhi' : (omissionProduct (permuteLists σ p) omitted' : ℝ) < 2 * d₀ := by
      rw [hprod]
      exact hhi
    have h := h omitted' hlo' hhi' l hl₀ hl₁
    simpa [hprod] using h
  · intro h omitted hlo hhi l hl₀ hl₁
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    have hprod : omissionProduct (permuteLists σ p) omitted = omissionProduct p omitted' := by
      simpa [omitted', omissionProduct_permuteLists]
    have hlo' : d₀ ≤ (omissionProduct p omitted' : ℝ) := by
      rw [← hprod]
      exact hlo
    have hhi' : (omissionProduct p omitted' : ℝ) < 2 * d₀ := by
      rw [← hprod]
      exact hhi
    have h := h omitted' hlo' hhi' l hl₀ hl₁
    simpa [hprod] using h

private lemma goodTestTwo_permute {x d₀ : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestTwo x d₀ K a (permuteLists σ p) r ↔ goodTestTwo x d₀ K a p r := by
  constructor
  · intro h I hI
    simpa [goodTestTwo, goodnessTrialValue_permute] using h I hI
  · intro h I hI
    simpa [goodTestTwo, goodnessTrialValue_permute] using h I hI

private lemma isGoodRatio_permute {x Y d₀ : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    IsGoodRatio x Y d₀ K a (permuteLists σ p) r ↔ IsGoodRatio x Y d₀ K a p r := by
  exact and_congr (goodTestOne_permute σ p r) (goodTestTwo_permute a σ p r)

private lemma envGood_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (s : EnvPoint S.x K) :
    envGood F S w (s.1, permuteLists σ s.2) ↔ envGood F S w s := by
  exact isGoodRatio_permute F.a σ s.2 (transportedRatio w s.1)

private lemma envValid_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (s : EnvPoint S.x K) :
    EnvValid F S (s.1, permuteLists σ s.2) ↔ EnvValid F S s := by
  constructor
  · rintro ⟨hz, hp⟩
    have hp' := validPrimeLists_permute (fun i => (σ i).symm) (permuteLists σ s.2) hp
    have hperm : permuteLists (fun i => (σ i).symm) (permuteLists σ s.2) = s.2 := by
      funext i j
      simp [permuteLists]
    exact ⟨hz, hperm ▸ hp'⟩
  · rintro ⟨hz, hp⟩
    exact ⟨hz, validPrimeLists_permute σ s.2 hp⟩

private abbrev EnvBoxPoints {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) :=
  {s : EnvPoint S.x K // EnvValid F S s ∧ envBox S w s.1}

private noncomputable def envPermEquiv {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    EnvBoxPoints F S w ≃ EnvBoxPoints F S w where
  toFun s :=
    ⟨(s.1.1, permuteLists σ s.1.2),
      ⟨(envValid_permute F S σ s.1).2 s.2.1, by simpa using s.2.2⟩⟩
  invFun s :=
    ⟨(s.1.1, permuteLists (fun i => (σ i).symm) s.1.2),
      ⟨(envValid_permute F S (fun i => (σ i).symm) s.1).2 s.2.1, by simpa using s.2.2⟩⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i j
      simp [permuteLists]
  right_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i j
      simp [permuteLists]

private noncomputable def envPointPermEquiv {x : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) : EnvPoint x K ≃ EnvPoint x K where
  toFun s := (s.1, permuteLists σ s.2)
  invFun s := (s.1, permuteLists (fun i => (σ i).symm) s.2)
  left_inv s := by
    apply Prod.ext
    · rfl
    · funext i j
      simp [permuteLists]
  right_inv s := by
    apply Prod.ext
    · rfl
    · funext i j
      simp [permuteLists]

@[simp] private lemma envPointPermEquiv_apply {x : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (s : EnvPoint x K) :
    envPointPermEquiv σ s = (s.1, permuteLists σ s.2) := rfl

private def envPermTupleInverse {K M : ℕ} :
    (Fin K → Equiv.Perm (Fin M)) ≃ (Fin K → Equiv.Perm (Fin M)) where
  toFun σ i := (σ i).symm
  invFun σ i := (σ i).symm
  left_inv σ := by
    funext i
    simp
  right_inv σ := by
    funext i
    simp

private lemma finset_sum_envPointPerm {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (T : Finset (EnvPoint S.x K))
    (hT : ∀ s, s ∈ T ↔ EnvValid F S s ∧ envBox S w s.1)
    (f g : EnvPoint S.x K → ℂ)
    (hfg : ∀ s ∈ T, f s = g (envPointPermEquiv σ s)) :
    (∑ s ∈ T, f s) = ∑ s ∈ T, g s := by
  apply Finset.sum_bijective (envPointPermEquiv σ) (Equiv.bijective _)
  · intro s
    rw [hT s, hT (envPointPermEquiv σ s)]
    constructor
    · rintro ⟨hv, hb⟩
      exact ⟨(envValid_permute F S σ s).2 hv, by simpa [envPointPermEquiv] using hb⟩
    · rintro ⟨hv, hb⟩
      exact ⟨(envValid_permute F S σ s).1 hv, by simpa [envPointPermEquiv] using hb⟩
  · intro s hs
    exact hfg s hs

private lemma envSym_envMul_support_subset {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ) :
    Function.support (envSym F S (envMul F S w ℓ f)) ⊆
      {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1} := by
  classical
  intro s hs
  by_contra hnot
  have hzero (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      envMul F S w ℓ f (s.1, permuteLists σ s.2) = 0 := by
    by_contra hne
    have hmem : EnvValid F S (s.1, permuteLists σ s.2) ∧
        envBox S w (s.1, permuteLists σ s.2).1 :=
      envMul_support_subset F S w ℓ f
        (by simpa [Function.mem_support] using hne)
    have hvalid := (envValid_permute F S σ s).mp hmem.1
    exact hnot ⟨hvalid, hmem.2⟩
  apply hs
  simp [envSym, hzero]

private lemma envSym_envMul_support_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) :
    (Function.support (envSym F S (envMul F S w ℓ f))).Finite :=
  (envBoxValid_finite F S w hU hV).subset
    (envSym_envMul_support_subset F S w ℓ f)

private lemma envRow_symEnvMul_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (s : EnvPoint S.x K) (hU : 0 < S.U) (hV : 0 < S.V) :
    envRow F S (envSym F S (envMul F S w ℓ f)) s =
      ∑ t ∈ (envBoxValid_finite F S w hU hV).toFinset,
        slotKernel F S s.2 t.2 (det2 s.1 t.1) *
          envSym F S (envMul F S w ℓ f) t := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  have hTmem (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        slotKernel F S s.2 t.2 (det2 s.1 t.1) else 0) *
        envSym F S (envMul F S w ℓ f) t = 0 := by
    have hnot : ¬(EnvValid F S t ∧ envBox S w t.1) := by
      intro ht'
      exact ht ((hTmem t).2 ht')
    have hsymZero : envSym F S (envMul F S w ℓ f) t = 0 := by
      by_contra hne
      have htSupport : t ∈ Function.support (envSym F S (envMul F S w ℓ f)) := by
        simpa [Function.mem_support] using hne
      exact hnot (envSym_envMul_support_subset F S w ℓ f htSupport)
    simp [hsymZero]
  unfold envRow
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro t ht
  have htValid := (hTmem t).1 ht
  simp [htValid.1]

private lemma envRowAdj_symEnvMul_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (s : EnvPoint S.x K) (hU : 0 < S.U) (hV : 0 < S.V) :
    envRowAdj F S (envSym F S (envMul F S w ℓ f)) s =
      ∑ t ∈ (envBoxValid_finite F S w hU hV).toFinset,
        star (slotKernel F S t.2 s.2 (det2 t.1 s.1)) *
          envSym F S (envMul F S w ℓ f) t := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  have hTmem (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        star (slotKernel F S t.2 s.2 (det2 t.1 s.1)) else 0) *
        envSym F S (envMul F S w ℓ f) t = 0 := by
    have hnot : ¬(EnvValid F S t ∧ envBox S w t.1) := by
      intro ht'
      exact ht ((hTmem t).2 ht')
    have hsymZero : envSym F S (envMul F S w ℓ f) t = 0 := by
      by_contra hne
      have htSupport : t ∈ Function.support (envSym F S (envMul F S w ℓ f)) := by
        simpa [Function.mem_support] using hne
      exact hnot (envSym_envMul_support_subset F S w ℓ f htSupport)
    simp [hsymZero]
  unfold envRowAdj
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro t ht
  have htValid := (hTmem t).1 ht
  simp [htValid.1]

private lemma allLineHits_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (s : EnvPoint S.x K) :
    (∀ i j, lineHit ℓ (permuteLists σ s.2 i j) s.1) ↔
      (∀ i j, lineHit ℓ (s.2 i j) s.1) := by
  constructor
  · intro h i j
    have := h i ((σ i).symm j)
    simpa [permuteLists] using this
  · intro h i j
    simpa [permuteLists] using h i (σ i j)

private lemma envDiag_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (s : EnvPoint S.x K) :
    envDiag F S w ℓ (s.1, permuteLists σ s.2) = envDiag F S w ℓ s := by
  have hcond :
      (EnvValid F S (s.1, permuteLists σ s.2) ∧ envBox S w s.1 ∧
        envGood F S w (s.1, permuteLists σ s.2) ∧
          (∀ i j, lineHit ℓ (permuteLists σ s.2 i j) s.1)) ↔
      (EnvValid F S s ∧ envBox S w s.1 ∧ envGood F S w s ∧
        (∀ i j, lineHit ℓ (s.2 i j) s.1)) := by
    simp [envValid_permute, envGood_permute, allLineHits_permute]
  unfold envDiag
  by_cases h : EnvValid F S s ∧ envBox S w s.1 ∧ envGood F S w s ∧
      (∀ i j, lineHit ℓ (s.2 i j) s.1)
  · have h' := hcond.mpr h
    simp [h, h']
  · have h' : ¬(EnvValid F S (s.1, permuteLists σ s.2) ∧ envBox S w s.1 ∧
        envGood F S w (s.1, permuteLists σ s.2) ∧
          (∀ i j, lineHit ℓ (permuteLists σ s.2 i j) s.1)) := by
      intro hp
      exact h (hcond.mp hp)
    simp [h, h']

private lemma envTargetPerm_reindex {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (T : Finset (EnvPoint S.x K))
    (hT : ∀ t, t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1)
    (s : EnvPoint S.x K) (α β : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (f : EnvPoint S.x K → ℂ) :
    ∑ t ∈ T,
        slotKernel F S (permuteLists α s.2) t.2 (det2 s.1 t.1) *
          (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
          f (t.1, permuteLists β t.2) =
    ∑ t ∈ T,
        slotKernel F S (permuteLists α s.2)
            (permuteLists (fun i => (β i).symm) t.2) (det2 s.1 t.1) *
          (envDiag F S w ℓ t : ℂ) * f t := by
  classical
  apply finset_sum_envPointPerm F S w β T hT
    (fun t => slotKernel F S (permuteLists α s.2) t.2 (det2 s.1 t.1) *
      (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
      f (t.1, permuteLists β t.2))
    (fun t => slotKernel F S (permuteLists α s.2)
      (permuteLists (fun i => (β i).symm) t.2) (det2 s.1 t.1) *
      (envDiag F S w ℓ t : ℂ) * f t)
  intro t ht
  have hperm :
      permuteLists (fun i => (β i).symm) (permuteLists β t.2) = t.2 := by
    funext i j
    simp [permuteLists]
  rw [envPointPermEquiv_apply]
  rw [hperm, envDiag_permute F S w ℓ β t]

private lemma envTargetAdjPerm_reindex {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (T : Finset (EnvPoint S.x K))
    (hT : ∀ t, t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1)
    (s : EnvPoint S.x K) (α β : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (f : EnvPoint S.x K → ℂ) :
    ∑ t ∈ T,
        star (slotKernel F S t.2 (permuteLists α s.2) (det2 t.1 s.1)) *
          (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
          f (t.1, permuteLists β t.2) =
      ∑ t ∈ T,
        star (slotKernel F S
            (permuteLists (fun i => (β i).symm) t.2) (permuteLists α s.2)
            (det2 t.1 s.1)) *
          (envDiag F S w ℓ t : ℂ) * f t := by
  classical
  apply finset_sum_envPointPerm F S w β T hT
    (fun t => star (slotKernel F S t.2 (permuteLists α s.2) (det2 t.1 s.1)) *
      (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
      f (t.1, permuteLists β t.2))
    (fun t => star (slotKernel F S
        (permuteLists (fun i => (β i).symm) t.2) (permuteLists α s.2)
        (det2 t.1 s.1)) *
      (envDiag F S w ℓ t : ℂ) * f t)
  intro t ht
  rw [envPointPermEquiv_apply]
  have hperm :
      permuteLists (fun i => (β i).symm) (permuteLists β t.2) = t.2 := by
    funext i j
    simp [permuteLists]
  rw [hperm, envDiag_permute F S w ℓ β t]

private lemma envPermTupleInverse_sum {K M : ℕ}
    (g : (Fin K → Equiv.Perm (Fin M)) → ℂ) :
    (∑ σ, g (envPermTupleInverse σ)) = ∑ σ, g σ := by
  classical
  apply Finset.sum_bijective envPermTupleInverse (Equiv.bijective _)
  · simp
  · intro σ hσ
    rfl

private lemma envOp_oneEdge_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (s : EnvPoint S.x K) :
    envOp F S w ℓ f s =
      ∑' t : EnvPoint S.x K,
        if EnvValid F S t then
          (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
            (envDiag F S w ℓ t : ℂ) * f t
        else 0 := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  let P : ℂ := (permCount S.x K : ℂ)⁻¹
  let edge (α : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (t : EnvPoint S.x K) : ℂ :=
    slotKernel F S (permuteLists α s.2) t.2 (det2 s.1 t.1)
  let value (β : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (t : EnvPoint S.x K) : ℂ :=
    (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
      f (t.1, permuteLists β t.2)
  let G (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
    ∑ t ∈ T,
      slotKernel F S (permuteLists α s.2)
        (permuteLists (fun i => (β i).symm) t.2) (det2 s.1 t.1) *
        (envDiag F S w ℓ t : ℂ) * f t
  have hT (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
          (envDiag F S w ℓ t : ℂ) * f t
       else 0) = 0 := by
    by_cases hv : EnvValid F S t
    · have hbox : ¬envBox S w t.1 := by
        intro hb
        exact ht ((hT t).2 ⟨hv, hb⟩)
      simp [hv, envDiag, hbox]
    · simp [hv]
  have hsum :
      (∑' t : EnvPoint S.x K,
        if EnvValid F S t then
          (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
            (envDiag F S w ℓ t : ℂ) * f t
        else 0) =
      ∑ t ∈ T,
        (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
          (envDiag F S w ℓ t : ℂ) * f t := by
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro t ht
    have hv := (hT t).1 ht
    simp [hv]
  have hrow (q : EnvPoint S.x K) :
      envRow F S (envSym F S (envMul F S w ℓ f)) q =
        ∑ t ∈ T,
          slotKernel F S q.2 t.2 (det2 q.1 t.1) *
            envSym F S (envMul F S w ℓ f) t :=
    envRow_symEnvMul_sum F S w ℓ f q hU hV
  have hleft : envOp F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ t ∈ T, edge α t *
            (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t)) := by
    change (envDiag F S w ℓ s : ℂ) *
      ((permCount S.x K : ℂ)⁻¹ *
        ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          envRow F S (envSym F S (envMul F S w ℓ f))
            (s.1, permuteLists α s.2)) = _
    simp_rw [hrow]
    simp only [envSym, envMul, P, edge, value]
  have hreindex (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ t ∈ T, edge α t * value β t = G α β := by
    simpa [edge, value, G, mul_assoc] using
      (envTargetPerm_reindex F S w ℓ T hT s α β f)
  have hpoint (α : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ t ∈ T, edge α t *
          (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t) =
        P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β := by
    calc
      _ = P * ∑ t ∈ T, edge α t *
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
      _ = P * ∑ t ∈ T,
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), edge α t * value β t := by
          apply congrArg (fun q : ℂ => P * q)
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
      _ = P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ t ∈ T, edge α t * value β t := by
          apply congrArg (fun q : ℂ => P * q)
          simpa using
            (Finset.sum_comm (s := T)
              (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))))
              (f := fun t β => edge α t * value β t))
      _ = P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β := by
          apply congrArg (fun q : ℂ => P * q)
          apply Finset.sum_congr rfl
          intro β hβ
          exact hreindex α β
  have hfactor (g : (Fin K → Equiv.Perm (Fin (slotCount S.x))) → ℂ) :
      P * ∑ α, P * g α = P ^ 2 * ∑ α, g α := by
    calc
      P * ∑ α, P * g α = ∑ α, P * (P * g α) := by rw [Finset.mul_sum]
      _ = ∑ α, P ^ 2 * g α := by
        apply Finset.sum_congr rfl
        intro α hα
        ring
      _ = P ^ 2 * ∑ α, g α := by rw [Finset.mul_sum]
  have hExpanded : envOp F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
    calc
      _ = (envDiag F S w ℓ s : ℂ) *
            (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T, edge α t *
                (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t)) := hleft
      _ = (envDiag F S w ℓ s : ℂ) *
            (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P * q))
          apply Finset.sum_congr rfl
          intro α hα
          exact hpoint α
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * q)
          exact hfactor (fun α => ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β)
  have hG (α : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β =
        ∑ β, ∑ t ∈ T,
          slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
            (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t := by
    simpa [G, envPermTupleInverse] using
      (envPermTupleInverse_sum (g := fun β =>
        ∑ t ∈ T,
          slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
            (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t))
  have hExpanded' : envOp F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ t ∈ T,
              slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t) := by
    calc
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := hExpanded
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ t ∈ T,
                  slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                    (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P ^ 2 * q))
          apply Finset.sum_congr rfl
          intro α hα
          exact hG α
  have hTargetExpand :
      ∑ t ∈ T,
        (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
          (envDiag F S w ℓ t : ℂ) * f t =
        (envDiag F S w ℓ s : ℂ) *
          (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T,
                slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                  (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t) := by
    let term (t : EnvPoint S.x K)
        (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
      slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
        (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t
    have hdist (t : EnvPoint S.x K) :
        (∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
              (det2 s.1 t.1)) * (envDiag F S w ℓ t : ℂ) * f t =
          ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
      simp_rw [Finset.sum_mul]
      rfl
    calc
      _ = ∑ t ∈ T,
            (envDiag F S w ℓ s : ℂ) * (P ^ 2 *
              ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                    (det2 s.1 t.1)) *
              (envDiag F S w ℓ t : ℂ) * f t := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [symKernel, P]
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ t ∈ T,
              ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β) := by
          calc
            _ = ∑ t ∈ T,
                  (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                    ((∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                          (det2 s.1 t.1)) *
                      (envDiag F S w ℓ t : ℂ) * f t) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
            _ = (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                  ∑ t ∈ T,
                    (∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                          (det2 s.1 t.1)) *
                      (envDiag F S w ℓ t : ℂ) * f t := by
                rw [Finset.mul_sum]
            _ = (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                  ∑ t ∈ T,
                    ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
                congr 1
                apply Finset.sum_congr rfl
                intro t ht
                exact hdist t
            _ = (envDiag F S w ℓ s : ℂ) *
                  (P ^ 2 *
                    ∑ t ∈ T,
                      ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β) := by
                ring
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ t ∈ T, term t α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P ^ 2 * q))
          calc
            _ = ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  ∑ t ∈ T, ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
                simpa using
                  (Finset.sum_comm (s := T)
                    (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))) )
                    (f := fun t α => ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β))
            _ = ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), ∑ t ∈ T, term t α β := by
                apply Finset.sum_congr rfl
                intro α hα
                simpa using
                  (Finset.sum_comm (s := T)
                    (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))))
                    (f := fun t β => term t α β))
  calc
    envOp F S w ℓ f s =
        (envDiag F S w ℓ s : ℂ) *
          (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T,
                slotKernel F S (permuteLists α s.2) (permuteLists β t.2)
                  (det2 s.1 t.1) * (envDiag F S w ℓ t : ℂ) * f t) := hExpanded'
    _ = ∑ t ∈ T,
          (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
            (envDiag F S w ℓ t : ℂ) * f t := hTargetExpand.symm
    _ = ∑' t : EnvPoint S.x K,
          if EnvValid F S t then
            (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
              (envDiag F S w ℓ t : ℂ) * f t
          else 0 := hsum.symm


private lemma envOpAdj_oneEdge_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (s : EnvPoint S.x K) :
    envOpAdj F S w ℓ f s =
      ∑' t : EnvPoint S.x K,
        if EnvValid F S t then
          (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
            (envDiag F S w ℓ t : ℂ) * f t
        else 0 := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  let P : ℂ := (permCount S.x K : ℂ)⁻¹
  let edge (α : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (t : EnvPoint S.x K) : ℂ :=
    star (slotKernel F S t.2 (permuteLists α s.2) (det2 t.1 s.1))
  let value (β : Fin K → Equiv.Perm (Fin (slotCount S.x)))
      (t : EnvPoint S.x K) : ℂ :=
    (envDiag F S w ℓ (t.1, permuteLists β t.2) : ℂ) *
      f (t.1, permuteLists β t.2)
  let G (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
    ∑ t ∈ T,
      star (slotKernel F S (permuteLists (fun i => (β i).symm) t.2)
        (permuteLists α s.2) (det2 t.1 s.1)) *
        (envDiag F S w ℓ t : ℂ) * f t
  have hT (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
          (envDiag F S w ℓ t : ℂ) * f t
       else 0) = 0 := by
    by_cases hv : EnvValid F S t
    · have hbox : ¬envBox S w t.1 := by
        intro hb
        exact ht ((hT t).2 ⟨hv, hb⟩)
      simp [hv, envDiag, hbox]
    · simp [hv]
  have hsum :
      (∑' t : EnvPoint S.x K,
        if EnvValid F S t then
          (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
            (envDiag F S w ℓ t : ℂ) * f t
        else 0) =
      ∑ t ∈ T,
        (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
          (envDiag F S w ℓ t : ℂ) * f t := by
    rw [tsum_eq_sum hzero]
    apply Finset.sum_congr rfl
    intro t ht
    have hv := (hT t).1 ht
    simp [hv]
  have hrow (q : EnvPoint S.x K) :
      envRowAdj F S (envSym F S (envMul F S w ℓ f)) q =
        ∑ t ∈ T,
          star (slotKernel F S t.2 q.2 (det2 t.1 q.1)) *
            envSym F S (envMul F S w ℓ f) t :=
    envRowAdj_symEnvMul_sum F S w ℓ f q hU hV
  have hleft : envOpAdj F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ t ∈ T, edge α t *
            (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t)) := by
    change (envDiag F S w ℓ s : ℂ) *
      ((permCount S.x K : ℂ)⁻¹ *
        ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          envRowAdj F S (envSym F S (envMul F S w ℓ f))
            (s.1, permuteLists α s.2)) = _
    simp_rw [hrow]
    simp only [envSym, envMul, P, edge, value]
  have hreindex (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ t ∈ T, edge α t * value β t = G α β := by
    simpa [edge, value, G, mul_assoc] using
      (envTargetAdjPerm_reindex F S w ℓ T hT s α β f)
  have hpoint (α : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ t ∈ T, edge α t *
          (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t) =
        P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β := by
    calc
      _ = P * ∑ t ∈ T, edge α t *
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
      _ = P * ∑ t ∈ T,
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), edge α t * value β t := by
          apply congrArg (fun q : ℂ => P * q)
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
      _ = P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ t ∈ T, edge α t * value β t := by
          apply congrArg (fun q : ℂ => P * q)
          simpa using
            (Finset.sum_comm (s := T)
              (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))))
              (f := fun t β => edge α t * value β t))
      _ = P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β := by
          apply congrArg (fun q : ℂ => P * q)
          apply Finset.sum_congr rfl
          intro β hβ
          exact hreindex α β
  have hfactor (g : (Fin K → Equiv.Perm (Fin (slotCount S.x))) → ℂ) :
      P * ∑ α, P * g α = P ^ 2 * ∑ α, g α := by
    calc
      P * ∑ α, P * g α = ∑ α, P * (P * g α) := by rw [Finset.mul_sum]
      _ = ∑ α, P ^ 2 * g α := by
        apply Finset.sum_congr rfl
        intro α hα
        ring
      _ = P ^ 2 * ∑ α, g α := by rw [Finset.mul_sum]
  have hExpanded : envOpAdj F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
    calc
      _ = (envDiag F S w ℓ s : ℂ) *
            (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T, edge α t *
                (P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), value β t)) := hleft
      _ = (envDiag F S w ℓ s : ℂ) *
            (P * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              P * ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P * q))
          apply Finset.sum_congr rfl
          intro α hα
          exact hpoint α
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * q)
          exact hfactor (fun α => ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β)
  have hG (α : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β =
        ∑ β, ∑ t ∈ T,
          star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2)
            (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t := by
    simpa [G, envPermTupleInverse] using
      (envPermTupleInverse_sum (g := fun β =>
        ∑ t ∈ T,
          star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2)
            (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t))
  have hExpanded' : envOpAdj F S w ℓ f s =
      (envDiag F S w ℓ s : ℂ) *
        (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ t ∈ T,
              star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t) := by
    calc
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), G α β) := hExpanded
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ t ∈ T,
                  star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P ^ 2 * q))
          apply Finset.sum_congr rfl
          intro α hα
          exact hG α
  have hTargetExpand :
      ∑ t ∈ T,
        (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
          (envDiag F S w ℓ t : ℂ) * f t =
        (envDiag F S w ℓ s : ℂ) *
          (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T,
                star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2)
                  (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t) := by
    let term (t : EnvPoint S.x K)
        (α β : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
      star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t
    have hdist (t : EnvPoint S.x K) :
        (∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1))) * (envDiag F S w ℓ t : ℂ) * f t =
          ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
      simp_rw [Finset.sum_mul]
      rfl
    calc
      _ = ∑ t ∈ T,
            (envDiag F S w ℓ s : ℂ) * (P ^ 2 *
              ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1))) *
              (envDiag F S w ℓ t : ℂ) * f t := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [symKernel, P]
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ t ∈ T,
              ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β) := by
          calc
            _ = ∑ t ∈ T,
                  (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                    ((∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1))) *
                      (envDiag F S w ℓ t : ℂ) * f t) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
            _ = (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                  ∑ t ∈ T,
                    (∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2) (det2 t.1 s.1))) *
                      (envDiag F S w ℓ t : ℂ) * f t := by
                rw [Finset.mul_sum]
            _ = (envDiag F S w ℓ s : ℂ) * P ^ 2 *
                  ∑ t ∈ T,
                    ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                      ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
                congr 1
                apply Finset.sum_congr rfl
                intro t ht
                exact hdist t
            _ = (envDiag F S w ℓ s : ℂ) *
                  (P ^ 2 *
                    ∑ t ∈ T,
                      ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                        ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β) := by
                ring
      _ = (envDiag F S w ℓ s : ℂ) *
            (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                ∑ t ∈ T, term t α β) := by
          apply congrArg (fun q : ℂ => (envDiag F S w ℓ s : ℂ) * (P ^ 2 * q))
          calc
            _ = ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  ∑ t ∈ T, ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β := by
                simpa using
                  (Finset.sum_comm (s := T)
                    (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))) )
                    (f := fun t α => ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), term t α β))
            _ = ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
                  ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)), ∑ t ∈ T, term t α β := by
                apply Finset.sum_congr rfl
                intro α hα
                simpa using
                  (Finset.sum_comm (s := T)
                    (t := (Finset.univ : Finset (Fin K → Equiv.Perm (Fin (slotCount S.x)))))
                    (f := fun t β => term t α β))
  calc
    envOpAdj F S w ℓ f s =
        (envDiag F S w ℓ s : ℂ) *
          (P ^ 2 * ∑ α : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ β : Fin K → Equiv.Perm (Fin (slotCount S.x)),
              ∑ t ∈ T,
                star (slotKernel F S (permuteLists β t.2) (permuteLists α s.2)
                  (det2 t.1 s.1)) * (envDiag F S w ℓ t : ℂ) * f t) := hExpanded'
    _ = ∑ t ∈ T,
          (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
            (envDiag F S w ℓ t : ℂ) * f t := hTargetExpand.symm
    _ = ∑' t : EnvPoint S.x K,
          if EnvValid F S t then
            (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
              (envDiag F S w ℓ t : ℂ) * f t
          else 0 := hsum.symm

private lemma envOp_finset_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (s : EnvPoint S.x K) :
    envOp F S w ℓ f s =
      ∑ t ∈ (envBoxValid_finite F S w hU hV).toFinset,
        (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
          (envDiag F S w ℓ t : ℂ) * f t := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  have hT (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        (envDiag F S w ℓ s : ℂ) * symKernel F S true s t *
          (envDiag F S w ℓ t : ℂ) * f t
       else 0) = 0 := by
    by_cases hv : EnvValid F S t
    · have hbox : ¬envBox S w t.1 := by
        intro hb
        exact ht ((hT t).2 ⟨hv, hb⟩)
      simp [hv, envDiag, hbox]
    · simp [hv]
  rw [envOp_oneEdge_sum F S w ℓ f hU hV s]
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro t ht
  have hv := (hT t).1 ht
  simp [hv]

private lemma envOpAdj_finset_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (s : EnvPoint S.x K) :
    envOpAdj F S w ℓ f s =
      ∑ t ∈ (envBoxValid_finite F S w hU hV).toFinset,
        (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
          (envDiag F S w ℓ t : ℂ) * f t := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  have hT (t : EnvPoint S.x K) :
      t ∈ T ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simpa [T] using (Set.Finite.mem_toFinset hfinite)
  have hzero (t : EnvPoint S.x K) (ht : t ∉ T) :
      (if EnvValid F S t then
        (envDiag F S w ℓ s : ℂ) * symKernel F S false s t *
          (envDiag F S w ℓ t : ℂ) * f t
       else 0) = 0 := by
    by_cases hv : EnvValid F S t
    · have hbox : ¬envBox S w t.1 := by
        intro hb
        exact ht ((hT t).2 ⟨hv, hb⟩)
      simp [hv, envDiag, hbox]
    · simp [hv]
  rw [envOpAdj_oneEdge_sum F S w ℓ f hU hV s]
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro t ht
  have hv := (hT t).1 ht
  simp [hv]

private lemma sum_finset_subtype {α : Type*} {β : Type*} [AddCommMonoid β]
    (T : Finset α) (f : α → β) :
    (∑ x : {x // x ∈ T}, f x.1) = ∑ x ∈ T, f x := by
  classical
  change (∑ x ∈ T.attach, f x.1) = ∑ x ∈ T, f x
  exact Finset.sum_attach (s := T) (f := f)


private abbrev EnvBoxSubtype {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) :=
  {t : EnvPoint S.x K // t ∈ (envBoxValid_finite F S w hU hV).toFinset}

private def envBoxKernel {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (forward : Bool) (s t : EnvBoxSubtype F S w hU hV) : ℂ :=
  (envDiag F S w ℓ s.1 : ℂ) * symKernel F S forward s.1 t.1 *
    (envDiag F S w ℓ t.1 : ℂ)

private lemma envOp_subtype_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (q : EnvBoxSubtype F S w hU hV) :
    envOp F S w ℓ f q.1 =
      ∑ r : EnvBoxSubtype F S w hU hV,
        (envDiag F S w ℓ q.1 : ℂ) * symKernel F S true q.1 r.1 *
          (envDiag F S w ℓ r.1 : ℂ) * f r.1 := by
  let T := (envBoxValid_finite F S w hU hV).toFinset
  calc
    envOp F S w ℓ f q.1 =
        ∑ t ∈ T,
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S true q.1 t *
            (envDiag F S w ℓ t : ℂ) * f t := by
      simpa [T] using envOp_finset_sum F S w ℓ f hU hV q.1
    _ = ∑ r : EnvBoxSubtype F S w hU hV,
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S true q.1 r.1 *
            (envDiag F S w ℓ r.1 : ℂ) * f r.1 := by
      simpa [EnvBoxSubtype, T] using
        (sum_finset_subtype T (fun t =>
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S true q.1 t *
            (envDiag F S w ℓ t : ℂ) * f t)).symm

private lemma envOpAdj_subtype_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (f : EnvPoint S.x K → ℂ)
    (hU : 0 < S.U) (hV : 0 < S.V) (q : EnvBoxSubtype F S w hU hV) :
    envOpAdj F S w ℓ f q.1 =
      ∑ r : EnvBoxSubtype F S w hU hV,
        (envDiag F S w ℓ q.1 : ℂ) * symKernel F S false q.1 r.1 *
          (envDiag F S w ℓ r.1 : ℂ) * f r.1 := by
  let T := (envBoxValid_finite F S w hU hV).toFinset
  calc
    envOpAdj F S w ℓ f q.1 =
        ∑ t ∈ T,
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S false q.1 t *
            (envDiag F S w ℓ t : ℂ) * f t := by
      simpa [T] using envOpAdj_finset_sum F S w ℓ f hU hV q.1
    _ = ∑ r : EnvBoxSubtype F S w hU hV,
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S false q.1 r.1 *
            (envDiag F S w ℓ r.1 : ℂ) * f r.1 := by
      simpa [EnvBoxSubtype, T] using
        (sum_finset_subtype T (fun t =>
          (envDiag F S w ℓ q.1 : ℂ) * symKernel F S false q.1 t *
            (envDiag F S w ℓ t : ℂ) * f t)).symm

private def pathKernelForward (b : Bool) (j : ℕ) : Bool :=
  if j % 2 = 0 then b else !b

private lemma pathKernelForward_zero (b : Bool) : pathKernelForward b 0 = b := by
  simp [pathKernelForward]

private lemma pathKernelForward_succ (b : Bool) (j : ℕ) :
    pathKernelForward b (j + 1) = pathKernelForward (!b) j := by
  have hmod : j % 2 = 0 ∨ j % 2 = 1 := by
    have := Nat.mod_lt j (by decide : 0 < 2)
    omega
  rcases hmod with hmod | hmod
  · have hs : (j + 1) % 2 = 1 := by omega
    simp [pathKernelForward, hmod, hs]
  · have hs : (j + 1) % 2 = 0 := by omega
    simp [pathKernelForward, hmod, hs]

private def finitePathProduct {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (b : Bool) (n : ℕ)
    (γ : Fin (n + 1) → Q) : ℂ :=
  ∏ j : Fin n,
    κ (pathKernelForward b j.val) (γ j.castSucc) (γ j.succ)

private def finitePathSum {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (n : ℕ) (b : Bool)
    (f : Q → ℂ) (x : Q) : ℂ :=
  ∑ γ : Fin (n + 1) → Q,
    if γ 0 = x then finitePathProduct κ b n γ * f (γ (Fin.last n)) else 0

private def finiteKernelIter {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) : ℕ → Bool → (Q → ℂ) → Q → ℂ
  | 0, _, f, x => f x
  | n + 1, b, f, x => ∑ y : Q, κ b x y * finiteKernelIter κ n (!b) f y

private lemma envPairOp_subtype_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : EnvPoint S.x K → ℂ) (q : EnvBoxSubtype F S w hU hV) :
    envOp F S w ℓ (envOpAdj F S w ℓ f) q.1 =
      finiteKernelIter (envBoxKernel F S w ℓ hU hV) 2 true
        (fun t : EnvBoxSubtype F S w hU hV => f t.1) q := by
  rw [envOp_subtype_sum F S w ℓ (envOpAdj F S w ℓ f) hU hV q]
  apply Finset.sum_congr rfl
  intro r hr
  rw [envOpAdj_subtype_sum F S w ℓ f hU hV r]
  simp [finiteKernelIter, envBoxKernel, mul_assoc]


private def prependTwoEquiv {Q : Type*} (n : ℕ) :
    Q × (Q × (Fin n → Q)) ≃ (Fin (n + 2) → Q) :=
  (Equiv.prodCongr (Equiv.refl Q)
    (Fin.consEquiv (fun _ : Fin (n + 1) => Q))).trans
      (Fin.consEquiv (fun _ : Fin (n + 2) => Q))

private lemma finitePathSum_cons {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (n : ℕ) (b : Bool) (f : Q → ℂ) (y : Q) :
    finitePathSum κ n b f y =
      ∑ ρ : Fin n → Q,
        finitePathProduct κ b n (Fin.cons y ρ) *
          f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Q)
  unfold finitePathSum
  calc
    _ = ∑ pair : Q × (Fin n → Q),
          (if pair.1 = y then
            finitePathProduct κ b n (Fin.cons pair.1 pair.2) *
              f ((Fin.cons pair.1 pair.2 : Fin (n + 1) → Q) (Fin.last n)) else 0) := by
        symm
        simpa [e, Fin.consEquiv] using (Equiv.sum_comp e (fun γ =>
          if γ 0 = y then finitePathProduct κ b n γ * f (γ (Fin.last n)) else 0))
    _ = ∑ ρ : Fin n → Q,
          finitePathProduct κ b n (Fin.cons y ρ) *
            f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
        rw [Fintype.sum_prod_type]
        simp [e]

private lemma finitePathSum_succ {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (n : ℕ) (b : Bool) (f : Q → ℂ) (x : Q) :
    finitePathSum κ (n + 1) b f x =
      ∑ y : Q, κ b x y * finitePathSum κ n (!b) f y := by
  classical
  let e := prependTwoEquiv (Q := Q) n
  unfold finitePathSum
  calc
    _ = ∑ pair : Q × (Q × (Fin n → Q)),
          (if pair.1 = x then
            κ b pair.1 pair.2.1 *
              finitePathProduct κ (!b) n (Fin.cons pair.2.1 pair.2.2) *
                f ((Fin.cons pair.2.1 pair.2.2 : Fin (n + 1) → Q) (Fin.last n))
           else 0) := by
      symm
      simpa [e, prependTwoEquiv, Fin.consEquiv, finitePathProduct,
        Fin.prod_univ_succ, pathKernelForward_zero,
        pathKernelForward_succ] using
        (Equiv.sum_comp e (fun γ =>
          if γ 0 = x then finitePathProduct κ b (n + 1) γ *
            f (γ (Fin.last (n + 1))) else 0))
    _ = ∑ y : Q,
          κ b x y *
            ∑ ρ : Fin n → Q,
              finitePathProduct κ (!b) n (Fin.cons y ρ) *
                f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
      conv_lhs => rw [Fintype.sum_prod_type]
      calc
        _ = ∑ head : Q,
              if head = x then
                ∑ tail : Q × (Fin n → Q),
                  κ b x tail.1 *
                    finitePathProduct κ (!b) n (Fin.cons tail.1 tail.2) *
                      f ((Fin.cons tail.1 tail.2 : Fin (n + 1) → Q) (Fin.last n))
              else 0 := by
          apply Finset.sum_congr rfl
          intro head hhead
          by_cases hh : head = x <;> simp [hh]
        _ = ∑ tail : Q × (Fin n → Q),
              κ b x tail.1 *
                finitePathProduct κ (!b) n (Fin.cons tail.1 tail.2) *
              f ((Fin.cons tail.1 tail.2 : Fin (n + 1) → Q) (Fin.last n)) := by
          rw [Fintype.sum_ite_eq']
        _ = ∑ y : Q,
              κ b x y *
                ∑ ρ : Fin n → Q,
                  finitePathProduct κ (!b) n (Fin.cons y ρ) *
                    f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
          calc
            _ = ∑ tail : Q × (Fin n → Q),
                  κ b x tail.1 *
                    finitePathProduct κ (!b) n (Fin.cons tail.1 tail.2) *
                      f ((Fin.cons tail.1 tail.2 : Fin (n + 1) → Q) (Fin.last n)) := rfl
            _ = ∑ y : Q, ∑ ρ : Fin n → Q,
                  κ b x y *
                    finitePathProduct κ (!b) n (Fin.cons y ρ) *
                      f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
                simpa using
                  (Fintype.sum_prod_type (fun tail : Q × (Fin n → Q) =>
                    κ b x tail.1 *
                      finitePathProduct κ (!b) n (Fin.cons tail.1 tail.2) *
                        f ((Fin.cons tail.1 tail.2 : Fin (n + 1) → Q) (Fin.last n))))
            _ = ∑ y : Q,
                  κ b x y *
                    ∑ ρ : Fin n → Q,
                      finitePathProduct κ (!b) n (Fin.cons y ρ) *
                        f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)) := by
                apply Finset.sum_congr rfl
                intro y hy
                change (∑ ρ : Fin n → Q,
                    κ b x y * finitePathProduct κ (!b) n (Fin.cons y ρ) *
                      f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n))) = _
                simpa [mul_assoc] using
                  (Finset.mul_sum (Finset.univ : Finset (Fin n → Q))
                    (fun ρ => finitePathProduct κ (!b) n (Fin.cons y ρ) *
                      f ((Fin.cons y ρ : Fin (n + 1) → Q) (Fin.last n)))
                    (κ b x y)).symm
    _ = ∑ y : Q, κ b x y * finitePathSum κ n (!b) f y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← finitePathSum_cons]

private lemma finiteKernelIter_pathSum {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (n : ℕ) (b : Bool) (f : Q → ℂ) (x : Q) :
    finiteKernelIter κ n b f x = finitePathSum κ n b f x := by
  induction n generalizing b f x with
  | zero =>
      rw [finiteKernelIter, finitePathSum_cons]
      simp [finitePathProduct]
  | succ n ih =>
      rw [finiteKernelIter]
      simp_rw [ih]
      exact (finitePathSum_succ κ n b f x).symm

private lemma envIterate_box_subtype {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (R : ℕ) (f : EnvPoint S.x K → ℂ) :
    ∀ q : EnvBoxSubtype F S w hU hV,
      (((fun g => envOp F S w ℓ (envOpAdj F S w ℓ g))^[R]) f) q.1 =
        finiteKernelIter (envBoxKernel F S w ℓ hU hV) (2 * R) true
          (fun t : EnvBoxSubtype F S w hU hV => f t.1) q := by
  classical
  let H : (EnvPoint S.x K → ℂ) → (EnvPoint S.x K → ℂ) :=
    fun g => envOp F S w ℓ (envOpAdj F S w ℓ g)
  let κ := envBoxKernel F S w ℓ hU hV
  induction R with
  | zero =>
      intro q
      simp [H, finiteKernelIter]
  | succ R ih =>
      intro q
      rw [Function.iterate_succ_apply']
      rw [envPairOp_subtype_sum F S w ℓ hU hV (H^[R] f) q]
      have hrestr :
          (fun t : EnvBoxSubtype F S w hU hV => (H^[R] f) t.1) =
            (fun t => finiteKernelIter κ (2 * R) true
              (fun u : EnvBoxSubtype F S w hU hV => f u.1) t) := by
        funext t
        exact ih t
      rw [hrestr]
      have hN : 2 * (R + 1) = 2 * R + 2 := by omega
      rw [hN]
      simp [finiteKernelIter, κ]

private lemma rpow_pair_gap_threshold {a b : ℝ} (hab : a < b) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → 2 < Real.rpow L (b - a) := by
  have hdiff : 0 < b - a := sub_pos.mpr hab
  obtain ⟨L₀, hL₀⟩ := Filter.tendsto_atTop_atTop.mp
    (_root_.tendsto_rpow_atTop hdiff) 3
  refine ⟨L₀, ?_⟩
  intro L hL
  exact lt_of_lt_of_le (by norm_num : (2 : ℝ) < 3) (hL₀ L hL)

private lemma markedBands_eventually_disjoint {K : ℕ} (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
  classical
  rcases ha with ⟨hK, hrange, horder⟩
  let B : Fin K → Fin K → ℝ := fun i j =>
    if h : i.val < j.val then
      max 1 (Classical.choose (rpow_pair_gap_threshold (horder i j h)))
    else 1
  have hBge : ∀ i j, 0 ≤ B i j := by
    intro i j
    dsimp [B]
    split <;> positivity
  have hBworks : ∀ i j, i.val < j.val →
      ∀ L : ℝ, B i j ≤ L → 2 < Real.rpow L (a j - a i) := by
    intro i j hij L hL
    have hmax : max 1 (Classical.choose (rpow_pair_gap_threshold (horder i j hij))) ≤ L := by
      simpa only [B, dif_pos hij] using hL
    have hchoose : Classical.choose (rpow_pair_gap_threshold (horder i j hij)) ≤ L :=
      (le_max_right 1 _).trans hmax
    exact Classical.choose_spec (rpow_pair_gap_threshold (horder i j hij)) L hchoose
  let Btot : ℝ := ∑ i : Fin K, ∑ j : Fin K, B i j
  have hBbound : ∀ i j, B i j ≤ Btot := by
    intro i j
    dsimp [Btot]
    have hj : B i j ≤ ∑ j : Fin K, B i j := by
      exact Finset.single_le_sum (fun k hk => hBge i k) (Finset.mem_univ j)
    have hi : (∑ j : Fin K, B i j) ≤ ∑ i : Fin K, ∑ j : Fin K, B i j := by
      exact Finset.single_le_sum (fun k hk => Finset.sum_nonneg fun j _ => hBge k j)
        (Finset.mem_univ i)
    exact hj.trans hi
  let L₀ : ℝ := 1 + Btot
  let x₀ : ℝ := max 2 (Real.exp L₀)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro x hx i j hij
  have hxexp : Real.exp L₀ ≤ x := le_trans (le_max_right _ _) hx
  have hlog : L₀ ≤ Real.log x := by
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos L₀) hxexp
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos L₀) hxexp
  have hL₀ : 1 ≤ L₀ := by
    dsimp [L₀]
    have : 0 ≤ Btot := Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hBge i j
    linarith
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) (le_trans hL₀ hlog)
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hpow : 2 < Real.rpow (Real.log x) (a j - a i) := by
      apply hBworks i j hlt
      dsimp [L₀] at hlog ⊢
      have hBtot : B i j ≤ Btot := hBbound i j
      linarith
    have haiPos : 0 < Real.rpow (Real.log x) (a i) := Real.rpow_pos_of_pos hLpos _
    have hsplit : Real.rpow (Real.log x) (a j) =
        Real.rpow (Real.log x) (a i) * Real.rpow (Real.log x) (a j - a i) := by
      calc
        Real.rpow (Real.log x) (a j) =
            Real.rpow (Real.log x) (a i + (a j - a i)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hLpos _ _
    have hgap : 2 * Real.rpow (Real.log x) (a i) < Real.rpow (Real.log x) (a j) := by
      rw [hsplit]
      nlinarith
    have hexp : Real.exp (2 * Real.rpow (Real.log x) (a i)) <
        Real.exp (Real.rpow (Real.log x) (a j)) := Real.exp_lt_exp.mpr hgap
    apply Finset.disjoint_left.2
    intro p hpi hpj
    have hpi' := hpi
    have hpj' := hpj
    simp only [primeBand, Finset.mem_filter] at hpi' hpj'
    rcases hpi' with ⟨_, ⟨_, _, hhi⟩⟩
    rcases hpj' with ⟨_, ⟨_, hlo, _⟩⟩
    linarith
  · have hpow : 2 < Real.rpow (Real.log x) (a i - a j) := by
      apply hBworks j i hgt
      dsimp [L₀] at hlog ⊢
      have hBtot : B j i ≤ Btot := hBbound j i
      linarith
    have hajPos : 0 < Real.rpow (Real.log x) (a j) := Real.rpow_pos_of_pos hLpos _
    have hsplit : Real.rpow (Real.log x) (a i) =
        Real.rpow (Real.log x) (a j) * Real.rpow (Real.log x) (a i - a j) := by
      calc
        Real.rpow (Real.log x) (a i) =
            Real.rpow (Real.log x) (a j + (a i - a j)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hLpos _ _
    have hgap : 2 * Real.rpow (Real.log x) (a j) < Real.rpow (Real.log x) (a i) := by
      rw [hsplit]
      nlinarith
    have hexp : Real.exp (2 * Real.rpow (Real.log x) (a j)) <
        Real.exp (Real.rpow (Real.log x) (a i)) := Real.exp_lt_exp.mpr hgap
    apply Finset.disjoint_left.2
    intro p hpi hpj
    have hpi' := hpi
    have hpj' := hpj
    simp only [primeBand, Finset.mem_filter] at hpi' hpj'
    rcases hpi' with ⟨_, ⟨_, hlo, _⟩⟩
    rcases hpj' with ⟨_, ⟨_, _, hhi⟩⟩
    linarith

private def envPointLabels {K : ℕ} (S : PDScale) (s : EnvPoint S.x K) : Finset ℕ :=
  Finset.univ.image fun ij : Fin K × Fin (slotCount S.x) => s.2 ij.1 ij.2

private lemma envPointLabels_subset_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : EnvPoint S.x K) (hv : EnvValid F S s) :
    envPointLabels S s ⊆ markedPrimes S.x K F.a := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨ij, -, hpeq⟩
  have hband := (hv.2.1 ij.1 ij.2).2
  have hband' : p ∈ primeBand S.x (F.a ij.1) := by
    rw [← hpeq]
    exact hband
  exact Finset.mem_biUnion.mpr ⟨ij.1, Finset.mem_univ _, hband'⟩

private lemma envPointLabels_card {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : EnvPoint S.x K) (hv : EnvValid F S s)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) :
    (envPointLabels S s).card = K * slotCount S.x := by
  classical
  have hinj : Function.Injective (fun ij : Fin K × Fin (slotCount S.x) => s.2 ij.1 ij.2) := by
    intro ij ij' heq
    rcases ij with ⟨i, j⟩
    rcases ij' with ⟨i', j'⟩
    change s.2 i j = s.2 i' j' at heq
    apply Prod.ext
    · change i = i'
      by_contra hne
      change i ≠ i' at hne
      have hp := (hv.2.1 i j).2
      have hp' := (hv.2.1 i' j').2
      have hnot := Finset.disjoint_left.mp (hBands i i' hne) hp
      have hp'' := hp'
      rw [← heq] at hp''
      exact hnot hp''
    · change j = j'
      by_contra hne
      by_cases hgroup : i = i'
      · subst i'
        exact (hv.2.2 i j j' hne) heq
      · have hp := (hv.2.1 i j).2
        have hp' := (hv.2.1 i' j').2
        have hnot := Finset.disjoint_left.mp (hBands i i' hgroup) hp
        have hp'' := hp'
        rw [← heq] at hp''
        exact hnot hp''
  rw [envPointLabels, Finset.card_image_of_injective _ hinj]
  simp

private lemma momentR_pos_of_two {x : ℝ} (hx : 2 ≤ x) : 0 < momentR x := by
  rw [momentR, Nat.ceil_pos]
  have hxgt : 1 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hxgt
  have hpow : 0 < Real.rpow (Real.log x) (1 / 2 : ℝ) := Real.rpow_pos_of_pos hlog _
  exact div_pos hpow (by norm_num)

private lemma envIterate_zero_of_not_box {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (R : ℕ) (hR : 0 < R)
    (f : EnvPoint S.x K → ℂ) (s : EnvPoint S.x K) (hbox : ¬ envBox S w s.1) :
    (((fun g => envOp F S w ℓ (envOpAdj F S w ℓ g))^[R]) f) s = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hR)
  have hdiag : envDiag F S w ℓ s = 0 := by simp [envDiag, hbox]
  rw [Function.iterate_succ_apply']
  simp [envOp, envMul, hdiag]

private lemma lineHit_mem_iff {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (ℓ : LineData x K a) (p : ℕ) (hmem : p ∈ markedPrimes x K a) (z : ℤ × ℤ) :
    lineHit ℓ p z ↔ ℓ ⟨p, hmem⟩ = projLine p z := by
  constructor
  · rintro ⟨h, hh⟩
    have heq : (⟨p, h⟩ : {p : ℕ // p ∈ markedPrimes x K a}) = ⟨p, hmem⟩ :=
      Subtype.ext rfl
    simpa [heq] using hh
  · intro hh
    exact ⟨hmem, hh⟩

private lemma activeAt_iff_envPointLabels {K : ℕ} (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (j : Fin (pathLength S.x + 1)) :
    IsActiveAt γ p j ↔ p ∈ envPointLabels S (γ j) := by
  classical
  unfold IsActiveAt envPointLabels
  constructor
  · rintro ⟨i, jj, h⟩
    exact Finset.mem_image.mpr ⟨(i, jj), Finset.mem_univ _, h⟩
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨ij, -, h⟩
    exact ⟨ij.1, ij.2, h⟩

private def envHitPrimes {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (z : ℤ × ℤ) : Finset ℕ :=
  (markedPrimes S.x K F.a).filter fun p => lineHit ℓ p z

private def envVisitPrimeFactor {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (j : ℕ) (s : EnvPoint S.x K) : ℝ :=
  ∏ p ∈ markedPrimes S.x K F.a,
    if p ∈ envPointLabels S s then
      if lineHit ℓ p s.1 then 1 else 0
    else
      1 - memoryEta S.x F.q_d j * (if lineHit ℓ p s.1 then 1 else 0)

private lemma envVisitPrimeFactor_allHit {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (j : ℕ) (s : EnvPoint S.x K) (hv : EnvValid F S s)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (hAll : ∀ i jj, lineHit ℓ (s.2 i jj) s.1) :
    envVisitPrimeFactor F S ℓ j s =
      memoryQ S.x F.q_d j ^
        (envHitPrimes F S ℓ s.1 \ envPointLabels S s).card := by
  classical
  let P := markedPrimes S.x K F.a
  let A := envPointLabels S s
  let H := envHitPrimes F S ℓ s.1
  let q := memoryQ S.x F.q_d j
  let f : ℕ → ℝ := fun p =>
    if p ∈ A then if lineHit ℓ p s.1 then 1 else 0
    else 1 - memoryEta S.x F.q_d j * (if lineHit ℓ p s.1 then 1 else 0)
  have hAHit : ∀ p, p ∈ A → lineHit ℓ p s.1 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨ij, -, heq⟩
    simpa only [heq] using hAll ij.1 ij.2
  have hAone : ∀ p, p ∈ A → f p = 1 := by
    intro p hp
    simp [f, hp, hAHit p hp]
  have hremove : (∏ p ∈ P \ A, f p) = ∏ p ∈ P, f p := by
    apply Finset.prod_subset Finset.sdiff_subset
    intro p hp hpn
    have hpA : p ∈ A := by
      by_contra hnot
      exact hpn (Finset.mem_sdiff.mpr ⟨hp, hnot⟩)
    exact hAone p hpA
  have houtside : ∀ p, p ∈ P \ A →
      f p = if p ∈ H then q else 1 := by
    intro p hp
    have hpP := (Finset.mem_sdiff.mp hp).1
    have hpA := (Finset.mem_sdiff.mp hp).2
    by_cases hhit : lineHit ℓ p s.1
    · have hpH : p ∈ H := by
        exact Finset.mem_filter.mpr ⟨hpP, hhit⟩
      simp [f, hpA, hpH, hhit, q, memoryEta] <;> ring
    · have hpH : p ∉ H := by
        intro hh
        exact hhit (Finset.mem_filter.mp hh).2
      simp [f, hpA, hpH, hhit]
  have hHsub : H ⊆ P := Finset.filter_subset _ _
  have hfilter : (P \ A).filter (fun p => p ∈ H) = H \ A := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpP, hpA⟩, hpH⟩
      exact ⟨hpH, hpA⟩
    · rintro ⟨hpH, hpA⟩
      exact ⟨⟨hHsub hpH, hpA⟩, hpH⟩
  calc
    envVisitPrimeFactor F S ℓ j s = ∏ p ∈ P, f p := by
      simp [envVisitPrimeFactor, P, A, f]
    _ = ∏ p ∈ P \ A, f p := hremove.symm
    _ = ∏ p ∈ P \ A, (if p ∈ H then q else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact houtside p hp
    _ = q ^ (H \ A).card := by
      rw [← Finset.prod_filter (fun p => p ∈ H) (fun _ => q)]
      rw [hfilter]
      simp [q, Finset.prod_const]

private lemma prod_finset_subtype {α β : Type*} [CommMonoid β]
    (T : Finset α) (f : α → β) :
    (∏ x : {x // x ∈ T}, f x.1) = ∏ x ∈ T, f x := by
  classical
  change (∏ x ∈ T.attach, f x.1) = ∏ x ∈ T, f x
  exact Finset.prod_attach T f

private lemma envVisitPrimeFactor_subtype {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (j : ℕ) (s : EnvPoint S.x K) :
    envVisitPrimeFactor F S ℓ j s =
      ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
        if p.1 ∈ envPointLabels S s then
          if ℓ p = projLine p.1 s.1 then 1 else 0
        else 1 - memoryEta S.x F.q_d j *
          (if ℓ p = projLine p.1 s.1 then 1 else 0) := by
  classical
  let T := markedPrimes S.x K F.a
  let g : ℕ → ℝ := fun p =>
    if p ∈ envPointLabels S s then if lineHit ℓ p s.1 then 1 else 0
    else 1 - memoryEta S.x F.q_d j * (if lineHit ℓ p s.1 then 1 else 0)
  let h : {p : ℕ // p ∈ T} → ℝ := fun p =>
    if p.1 ∈ envPointLabels S s then
      if ℓ p = projLine p.1 s.1 then 1 else 0
    else 1 - memoryEta S.x F.q_d j *
      (if ℓ p = projLine p.1 s.1 then 1 else 0)
  calc
    envVisitPrimeFactor F S ℓ j s = ∏ p ∈ T, g p := by
      simp [envVisitPrimeFactor, T, g]
    _ = ∏ p : {p : ℕ // p ∈ T}, g p.1 :=
      (prod_finset_subtype T g).symm
    _ = ∏ p : {p : ℕ // p ∈ T}, h p := by
      apply Fintype.prod_congr
      intro p
      have hhit := lineHit_mem_iff ℓ p.1 p.2 s.1
      simp [g, h, hhit]

private lemma envVisitPrimeFactor_zero_of_missed {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (j : ℕ) (s : EnvPoint S.x K) (hv : EnvValid F S s)
    (i : Fin K) (jj : Fin (slotCount S.x)) (hmiss : ¬ lineHit ℓ (s.2 i jj) s.1) :
    envVisitPrimeFactor F S ℓ j s = 0 := by
  classical
  let p := s.2 i jj
  have hpA : p ∈ envPointLabels S s := by
    exact Finset.mem_image.mpr ⟨(i, jj), Finset.mem_univ _, rfl⟩
  have hpP : p ∈ markedPrimes S.x K F.a := envPointLabels_subset_marked F S s hv hpA
  unfold envVisitPrimeFactor
  exact Finset.prod_eq_zero hpP (by simp [p, hpA, hmiss])

private lemma envDiag_visitFactor {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (j : ℕ) (s : EnvPoint S.x K)
    (hv : EnvValid F S s) (hqd : 0 < F.q_d)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (m : ℕ) (hm : m = if j = 0 ∨ j = pathLength S.x then 1 else 2) :
    (envDiag F S w ℓ s : ℝ) ^ m =
      (if envBox S w s.1 ∧ envGood F S w s then 1 else 0) *
        envVisitPrimeFactor F S ℓ j s := by
  classical
  by_cases hbg : envBox S w s.1 ∧ envGood F S w s
  · rcases hbg with ⟨hbox, hgood⟩
    by_cases hAll : ∀ i jj, lineHit ℓ (s.2 i jj) s.1
    · let A := envPointLabels S s
      let H := envHitPrimes F S ℓ s.1
      have hAsubH : A ⊆ H := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨ij, -, heq⟩
        have hpP : p ∈ markedPrimes S.x K F.a :=
          envPointLabels_subset_marked F S s hv hp
        have hhit : lineHit ℓ p s.1 := by simpa only [heq] using hAll ij.1 ij.2
        exact Finset.mem_filter.mpr ⟨hpP, hhit⟩
      have hHcard : H.card = envOmega F S ℓ s.1 := by rfl
      have hcount : (H \ A).card = envOmega F S ℓ s.1 - K * slotCount S.x := by
        rw [Finset.card_sdiff_of_subset hAsubH, hHcard,
          envPointLabels_card F S s hv hBands]
      have hcountReal : ((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) =
          ((H \ A).card : ℝ) := by exact_mod_cast hcount.symm
      have hdiag : envDiag F S w ℓ s =
          Real.rpow F.q_d (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2) := by
        simp [envDiag, hv, hbox, hgood, hAll]
      have hfactor := envVisitPrimeFactor_allHit F S ℓ j s hv hBands hAll
      have hpow :
          (Real.rpow F.q_d
            (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2)) ^ m =
          memoryQ S.x F.q_d j ^ (H \ A).card := by
        by_cases hend : j = 0 ∨ j = pathLength S.x
        · have hm' : m = 1 := hm.trans (if_pos hend)
          rw [hm']
          have hq : memoryQ S.x F.q_d j = Real.rpow F.q_d (1 / 2 : ℝ) := by
            simp [memoryQ, hend, Real.sqrt_eq_rpow]
          calc
            _ = Real.rpow F.q_d
                  (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2) := by simp
            _ = Real.rpow F.q_d ((H \ A).card / 2) := by rw [hcountReal]
            _ = Real.rpow F.q_d ((1 / 2 : ℝ) * ((H \ A).card : ℝ)) := by
              congr 1
              push_cast
              ring
            _ = (Real.rpow F.q_d (1 / 2 : ℝ)) ^ (H \ A).card :=
              Real.rpow_mul_natCast (le_of_lt hqd) (1 / 2 : ℝ) _
            _ = memoryQ S.x F.q_d j ^ (H \ A).card :=
              congrArg (fun y : ℝ => y ^ (H \ A).card) hq.symm
        · have hm' : m = 2 := hm.trans (if_neg hend)
          rw [hm']
          have hq : memoryQ S.x F.q_d j = F.q_d := by simp [memoryQ, hend]
          calc
            _ = Real.rpow F.q_d
                  (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2 * 2) := by
              rw [← Real.rpow_natCast (Real.rpow F.q_d
                (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2)) 2]
              exact (Real.rpow_mul (le_of_lt hqd)
                (((envOmega F S ℓ s.1 - K * slotCount S.x : ℕ) : ℝ) / 2) 2).symm
            _ = Real.rpow F.q_d ((H \ A).card : ℝ) := by
              congr 1
              rw [hcountReal]
              ring
            _ = F.q_d ^ (H \ A).card := by simp [Real.rpow_natCast]
            _ = memoryQ S.x F.q_d j ^ (H \ A).card :=
              congrArg (fun y : ℝ => y ^ (H \ A).card) hq.symm
      rw [hdiag, hpow, hfactor]
      simp [hbox, hgood, A, H]
    · have hmiss : ∃ i jj, ¬ lineHit ℓ (s.2 i jj) s.1 := by
        by_contra hn
        push_neg at hn
        exact hAll hn
      obtain ⟨i, jj, hmiss⟩ := hmiss
      have hcond : ¬ (∀ i jj, lineHit ℓ (s.2 i jj) s.1) := by
        intro hall
        exact hmiss (hall i jj)
      have hdiag : envDiag F S w ℓ s = 0 := by
        simp [envDiag, hv, hbox, hgood, hcond]
      have hfactor := envVisitPrimeFactor_zero_of_missed F S ℓ j s hv i jj hmiss
      have hmpos : 0 < m := by
        rw [hm]
        by_cases hend : j = 0 ∨ j = pathLength S.x <;> simp [hend]
      simp [hbox, hgood, hdiag, hfactor, hmpos.ne']
  · have hdiag : envDiag F S w ℓ s = 0 := by
      rcases not_and_or.mp hbg with hbox | hgood
      · simp [envDiag, hv, hbox]
      · simp [envDiag, hv, hgood]
    have hmpos : 0 < m := by
      rw [hm]
      by_cases hend : j = 0 ∨ j = pathLength S.x <;> simp [hend]
    simp [hbg, hdiag, hmpos.ne']

private def envBoxPathToEnvPath {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V)
    (γ : Fin (pathLength S.x + 1) → EnvBoxSubtype F S w hU hV) : EnvPath S.x K :=
  fun j => (γ j).1

private lemma envPathVisitPrimeProduct {K : ℕ} (F : PDFix K) (S : PDScale)
    (ℓ : LineData S.x K F.a) (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V)
    (γ : Fin (pathLength S.x + 1) → EnvBoxSubtype F S w hU hV) :
    (∏ j : Fin (pathLength S.x + 1),
      envVisitPrimeFactor F S ℓ j.val (γ j).1) =
      ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
        pathPrimeFactor F S (envBoxPathToEnvPath F S w hU hV γ) p.1 (ℓ p) := by
  classical
  let γ' := envBoxPathToEnvPath F S w hU hV γ
  simp_rw [envVisitPrimeFactor_subtype]
  rw [Finset.prod_comm]
  apply Fintype.prod_congr
  intro p
  simp only [pathPrimeFactor]
  apply Fintype.prod_congr
  intro j
  have hactive := activeAt_iff_envPointLabels S
    (envBoxPathToEnvPath F S w hU hV γ) p.1 j
  by_cases hline : ℓ p = projLine p.1 (γ j).1.1
  · simp [γ', envBoxPathToEnvPath, hactive, hline]
  · simp [γ', envBoxPathToEnvPath, hactive, hline]

private lemma envPathDiagonalFactor {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (hqd : 0 < F.q_d)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (γ : Fin (pathLength S.x + 1) → EnvBoxSubtype F S w hU hV) :
    (∏ j : Fin (pathLength S.x + 1),
      (envDiag F S w ℓ (γ j).1) ^
        (if j = 0 ∨ j = Fin.last (pathLength S.x) then 1 else 2)) =
      pathArch F S w (envBoxPathToEnvPath F S w hU hV γ) *
        ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
          pathPrimeFactor F S (envBoxPathToEnvPath F S w hU hV γ) p.1 (ℓ p) := by
  classical
  let γ' := envBoxPathToEnvPath F S w hU hV γ
  let m : Fin (pathLength S.x + 1) → ℕ := fun j =>
    if j = 0 ∨ j = Fin.last (pathLength S.x) then 1 else 2
  have hm : ∀ j, m j =
      if j.val = 0 ∨ j.val = pathLength S.x then 1 else 2 := by
    intro j
    dsimp [m]
    by_cases hzero : j = 0
    · simp [hzero]
    · by_cases hlast : j = Fin.last (pathLength S.x)
      · simp [hzero, hlast]
      · have hvalzero : j.val ≠ 0 := by
          intro h
          exact hzero (Fin.ext h)
        have hvallast : j.val ≠ pathLength S.x := by
          intro h
          exact hlast (Fin.ext h)
        simp [hzero, hlast, hvalzero, hvallast]
  have hvisit (j : Fin (pathLength S.x + 1)) :
      (envDiag F S w ℓ (γ j).1) ^ m j =
        (if envBox S w (γ j).1.1 ∧ envGood F S w (γ j).1 then 1 else 0) *
          envVisitPrimeFactor F S ℓ j.val (γ j).1 := by
    have hvbox := (Set.Finite.mem_toFinset
      (envBoxValid_finite F S w hU hV)).mp (γ j).2
    exact envDiag_visitFactor F S w ℓ j.val (γ j).1 hvbox.1 hqd hBands (m j) (hm j)
  calc
    _ = ∏ j : Fin (pathLength S.x + 1),
          (if envBox S w (γ j).1.1 ∧ envGood F S w (γ j).1 then 1 else 0) *
            envVisitPrimeFactor F S ℓ j.val (γ j).1 := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hvisit j
    _ = (∏ j : Fin (pathLength S.x + 1),
          if envBox S w (γ j).1.1 ∧ envGood F S w (γ j).1 then 1 else 0) *
          ∏ j : Fin (pathLength S.x + 1),
            envVisitPrimeFactor F S ℓ j.val (γ j).1 := by
          rw [Finset.prod_mul_distrib]
    _ = pathArch F S w γ' *
          ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
            pathPrimeFactor F S γ' p.1 (ℓ p) := by
          rw [envPathVisitPrimeProduct F S ℓ w hU hV γ]
          rfl

private lemma envMoment_boxPathSum {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (hR : 0 < S.R) :
    envMomentC F S w ℓ =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ q : EnvBoxSubtype F S w hU hV,
          if q.1.1 = (1, 0) then
            finitePathSum (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
              (fun t => e1Vector t.1) q
          else 0 := by
  classical
  let hfinite := envBoxValid_finite F S w hU hV
  let T := hfinite.toFinset
  let H : (EnvPoint S.x K → ℂ) → (EnvPoint S.x K → ℂ) :=
    fun g => envOp F S w ℓ (envOpAdj F S w ℓ g)
  have hT (s : EnvPoint S.x K) :
      s ∈ T ↔ EnvValid F S s ∧ envBox S w s.1 := by
    simpa [T, hfinite] using Set.Finite.mem_toFinset hfinite
  have hzero (s : EnvPoint S.x K) (hs : s ∉ T) :
      (if EnvValid F S s then
        star (e1Vector s) * ((H^[S.R]) e1Vector) s else 0) = 0 := by
    by_cases hv : EnvValid F S s
    · by_cases he : s.1 = (1, 0)
      · have hbox : ¬ envBox S w s.1 := by
          intro hb
          exact hs ((hT s).2 ⟨hv, hb⟩)
        have hz := envIterate_zero_of_not_box F S w ℓ S.R hR e1Vector s hbox
        simp [e1Vector, he, hv, hz, H]
      · simp [e1Vector, he, hv]
    · simp [hv]
  unfold envMomentC envInner
  rw [tsum_eq_sum hzero]
  have hsub := sum_finset_subtype T (fun s =>
    if EnvValid F S s then star (e1Vector s) * ((H^[S.R]) e1Vector) s else 0)
  rw [← hsub]
  have hpoint (q : EnvBoxSubtype F S w hU hV) :
      (if EnvValid F S q.1 then star (e1Vector q.1) * ((H^[S.R]) e1Vector) q.1 else 0) =
        if q.1.1 = (1, 0) then
          finitePathSum (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
            (fun t => e1Vector t.1) q
        else 0 := by
    have hvbox := (hT q.1).1 q.2
    have hv := hvbox.1
    by_cases he : q.1.1 = (1, 0)
    · have hit₀ := envIterate_box_subtype F S w ℓ hU hV S.R e1Vector q
      have hit : ((H^[S.R]) e1Vector) q.1 =
          finiteKernelIter (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
            (fun t => e1Vector t.1) q := by simpa [H] using hit₀
      have hpath := finiteKernelIter_pathSum
        (envBoxKernel F S w ℓ hU hV) (2 * S.R) true (fun t => e1Vector t.1) q
      have hE : e1Vector q.1 = 1 := by simp [e1Vector, he]
      calc
        (if EnvValid F S q.1 then
            star (e1Vector q.1) * ((H^[S.R]) e1Vector) q.1 else 0) =
            ((H^[S.R]) e1Vector) q.1 := by simp [hv, hE]
        _ = finiteKernelIter (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
              (fun t => e1Vector t.1) q := hit
        _ = finitePathSum (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
              (fun t => e1Vector t.1) q := hpath
        _ = if q.1.1 = (1, 0) then
              finitePathSum (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
                (fun t => e1Vector t.1) q else 0 := by simp [he]
    · simp [e1Vector, he, hv]
  calc
    (physicalMeasure S.x K F.a : ℂ) *
        ∑ q : EnvBoxSubtype F S w hU hV,
          (if EnvValid F S q.1 then
            star (e1Vector q.1) * ((H^[S.R]) e1Vector) q.1 else 0) =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ q : EnvBoxSubtype F S w hU hV,
          if q.1.1 = (1, 0) then
            finitePathSum (envBoxKernel F S w ℓ hU hV) (2 * S.R) true
              (fun t => e1Vector t.1) q
          else 0 := by
      congr 1
      apply Fintype.sum_congr
      intro q
      exact hpoint q

private lemma finitePathSum_sum_start {Q : Type*} [Fintype Q]
    (κ : Bool → Q → Q → ℂ) (n : ℕ) (P : Q → Prop) [DecidablePred P]
    (f : Q → ℂ) :
    (∑ x : Q, if P x then finitePathSum κ n true f x else 0) =
      ∑ γ : Fin (n + 1) → Q,
        if P (γ 0) then
          finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 := by
  classical
  unfold finitePathSum
  let Path := Fin (n + 1) → Q
  let G : Q × Path → ℂ := fun z =>
    if P z.1 then if z.2 0 = z.1 then
      finitePathProduct κ true n z.2 * f (z.2 (Fin.last n)) else 0 else 0
  let e : Path × Q ≃ Q × Path := Equiv.prodComm Path Q
  have houter :
      (∑ x : Q, if P x then
        ∑ γ : Path, if γ 0 = x then
          finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0) =
      ∑ x : Q, ∑ γ : Path,
        if P x then if γ 0 = x then
          finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0 := by
    apply Fintype.sum_congr
    intro x
    by_cases hx : P x <;> simp [hx]
  have hswap : (∑ z : Q × Path, G z) = ∑ z : Path × Q, G (e z) := by
    simpa [G, e, Equiv.prodComm] using (Equiv.sum_comp e G).symm
  have hinner (γ : Path) :
      (∑ x : Q, if P x then if γ 0 = x then
        finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0) =
      if P (γ 0) then finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 := by
    have hterm (x : Q) :
        (if P x then if γ 0 = x then
          finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0) =
          if γ 0 = x then
            (if P (γ 0) then finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0)
          else 0 := by
      by_cases heq : γ 0 = x
      · subst x
        by_cases hp : P (γ 0) <;> simp [hp]
      · simp [heq]
    calc
      _ = ∑ x : Q,
            if γ 0 = x then
              (if P (γ 0) then finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0)
            else 0 := by
          apply Fintype.sum_congr
          intro x
          exact hterm x
      _ = if P (γ 0) then finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 := by simp
  calc
    (∑ x : Q, if P x then
        ∑ γ : Path, if γ 0 = x then
          finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0) =
      ∑ z : Q × Path, G z := by
        rw [houter, ← Fintype.sum_prod_type']
    _ = ∑ z : Path × Q, G (e z) := hswap
    _ = ∑ γ : Path, ∑ x : Q,
          if P x then if γ 0 = x then
            finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 else 0 := by
        rw [Fintype.sum_prod_type]
        apply Fintype.sum_congr
        intro γ
        apply Fintype.sum_congr
        intro x
        simp [G, e, Equiv.prodComm]
    _ = ∑ γ : Path,
          if P (γ 0) then finitePathProduct κ true n γ * f (γ (Fin.last n)) else 0 := by
        apply Fintype.sum_congr
        intro γ
        exact hinner γ

private lemma finitePathEdgeDiagProduct {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n)
    (D : Fin (n + 1) → M) :
    (∏ j : Fin n, D j.castSucc * D j.succ) =
      ∏ j : Fin (n + 1),
        if j = 0 ∨ j = Fin.last n then D j else D j ^ 2 := by
  classical
  let fStart : Fin (n + 1) → M := fun j => if j = Fin.last n then 1 else D j
  let fEnd : Fin (n + 1) → M := fun j => if j = 0 then 1 else D j
  have hzeroLast : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hlastZero : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hstart : (∏ j : Fin n, D j.castSucc) = ∏ j : Fin (n + 1), fStart j := by
    symm
    rw [Fin.prod_univ_castSucc]
    simp [fStart]
  have hend : (∏ j : Fin n, D j.succ) = ∏ j : Fin (n + 1), fEnd j := by
    symm
    rw [Fin.prod_univ_succ]
    simp [fEnd]
  calc
    (∏ j : Fin n, D j.castSucc * D j.succ) =
        (∏ j : Fin n, D j.castSucc) * ∏ j : Fin n, D j.succ := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ j : Fin (n + 1), fStart j) * ∏ j : Fin (n + 1), fEnd j := by
          rw [hstart, hend]
    _ = ∏ j : Fin (n + 1), fStart j * fEnd j := by rw [Finset.prod_mul_distrib]
    _ = ∏ j : Fin (n + 1),
          if j = 0 ∨ j = Fin.last n then D j else D j ^ 2 := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases h0 : j = 0
          · subst j
            simp [fStart, fEnd, hzeroLast]
          · by_cases hlast : j = Fin.last n
            · subst j
              simp [fStart, fEnd, h0, hlastZero]
            · simp [fStart, fEnd, h0, hlast, pow_two]

private lemma finitePathEdgeDiagProductPow {M : Type*} [CommMonoid M] {n : ℕ}
    (hn : 0 < n) (D : Fin (n + 1) → M) :
    (∏ j : Fin n, D j.castSucc * D j.succ) =
      ∏ j : Fin (n + 1), D j ^ (if j = 0 ∨ j = Fin.last n then 1 else 2) := by
  rw [finitePathEdgeDiagProduct hn D]
  apply Fintype.prod_congr
  intro j
  by_cases hj : j = 0 ∨ j = Fin.last n <;> simp [hj]

private lemma envBoxPath_product {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (hN : 0 < pathLength S.x) (hqd : 0 < F.q_d)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (γ : Fin (pathLength S.x + 1) → EnvBoxSubtype F S w hU hV) :
    (physicalMeasure S.x K F.a : ℂ) *
      finitePathProduct (envBoxKernel F S w ℓ hU hV) true (pathLength S.x) γ =
      pathCoefficient F S (envBoxPathToEnvPath F S w hU hV γ) *
        (pathArch F S w (envBoxPathToEnvPath F S w hU hV γ) : ℂ) *
        ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
          pathPrimeFactor F S (envBoxPathToEnvPath F S w hU hV γ) p.1 (ℓ p) : ℝ) : ℂ) := by
  classical
  let D : Fin (pathLength S.x + 1) → ℝ := fun j => envDiag F S w ℓ (γ j).1
  let k : Fin (pathLength S.x) → ℂ := fun j =>
    symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc).1 (γ j.succ).1
  have hparity (j : Fin (pathLength S.x)) :
      pathKernelForward true j.val = decide (j.val % 2 = 0) := by
    by_cases hj : j.val % 2 = 0 <;> simp [pathKernelForward, hj]
  have hedge : finitePathProduct (envBoxKernel F S w ℓ hU hV) true (pathLength S.x) γ =
      (∏ j, k j) * ∏ j : Fin (pathLength S.x), ((D j.castSucc : ℂ) * (D j.succ : ℂ)) := by
    rw [← Finset.prod_mul_distrib]
    apply Fintype.prod_congr
    intro j
    dsimp [finitePathProduct, envBoxKernel, k, D]
    rw [hparity]
    ring
  have hdiag := envPathDiagonalFactor F S w ℓ hU hV hqd hBands γ
  have hdiagC := congrArg (fun t : ℝ => (t : ℂ)) hdiag
  have hpair := congrArg (fun t : ℝ => (t : ℂ)) (finitePathEdgeDiagProductPow hN D)
  push_cast at hpair hdiagC
  rw [hedge, hpair, hdiagC]
  change (physicalMeasure S.x K F.a : ℂ) *
      ((∏ j, k j) *
        ((pathArch F S w (envBoxPathToEnvPath F S w hU hV γ) : ℂ) * _)) = _
  dsimp [pathCoefficient, envBoxPathToEnvPath, k]
  push_cast
  ring

private lemma envBoxPathToEnvPath_injective {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) :
    Function.Injective (envBoxPathToEnvPath F S w hU hV) := by
  intro γ γ' h
  funext j
  apply Subtype.ext
  exact congrFun h j

private lemma envPathSummand_support {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V) :
    Function.support (fun γ : EnvPath S.x K =>
      if IsEnvPathAdmissible F S γ then
        pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
          ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
            pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
      else 0) ⊆ Set.range (envBoxPathToEnvPath F S w hU hV) := by
  classical
  intro γ hγ
  have hnz : (if IsEnvPathAdmissible F S γ then
        pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
          ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
            pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
      else 0) ≠ 0 := hγ
  have hadm : IsEnvPathAdmissible F S γ := by
    by_contra h
    simp [h] at hnz
  have harch : pathArch F S w γ ≠ 0 := by
    intro h
    simp [hadm, h] at hnz
  have hbox (j : Fin (pathLength S.x + 1)) : envBox S w (γ j).1 := by
    by_contra h
    apply harch
    unfold pathArch
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [h]
  let γ' : Fin (pathLength S.x + 1) → EnvBoxSubtype F S w hU hV := fun j =>
    ⟨γ j, (Set.Finite.mem_toFinset (envBoxValid_finite F S w hU hV)).2
      ⟨hadm.1 j, hbox j⟩⟩
  exact ⟨γ', rfl⟩

private lemma env_path_form_of_pos {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) (hU : 0 < S.U) (hV : 0 < S.V)
    (hR : 0 < S.R) (hqd : 0 < F.q_d)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) :
    envMomentC F S w ℓ =
      ∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
            ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
              pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
        else 0 := by
  classical
  let G : EnvPath S.x K → ℂ := fun γ =>
    if IsEnvPathAdmissible F S γ then
      pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
        ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
          pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
    else 0
  let Q := EnvBoxSubtype F S w hU hV
  let κ := envBoxKernel F S w ℓ hU hV
  have hN : 0 < pathLength S.x := by
    change 0 < 2 * S.R
    omega
  have hsum := (envBoxPathToEnvPath_injective F S w hU hV).tsum_eq
    (envPathSummand_support F S w ℓ hU hV)
  rw [tsum_fintype] at hsum
  have hM := envMoment_boxPathSum F S w ℓ hU hV hR
  change envMomentC F S w ℓ = (physicalMeasure S.x K F.a : ℂ) *
    ∑ q : Q, if q.1.1 = (1, 0) then
      finitePathSum κ (pathLength S.x) true (fun t => e1Vector t.1) q else 0 at hM
  rw [finitePathSum_sum_start] at hM
  rw [hM, ← hsum, Finset.mul_sum]
  apply Fintype.sum_congr
  intro γ
  have hv : ∀ j, EnvValid F S (envBoxPathToEnvPath F S w hU hV γ j) := by
    intro j
    exact ((Set.Finite.mem_toFinset (envBoxValid_finite F S w hU hV)).1 (γ j).2).1
  have hfactor := envBoxPath_product F S w ℓ hU hV hN hqd hBands γ
  by_cases h0 : (γ 0).1.1 = (1, 0)
  · by_cases hlast : (γ (Fin.last (pathLength S.x))).1.1 = (1, 0)
    · have hadm : IsEnvPathAdmissible F S (envBoxPathToEnvPath F S w hU hV γ) :=
        ⟨hv, h0, hlast⟩
      simpa [κ, e1Vector, h0, hlast, hadm] using hfactor
    · have hadm : ¬ IsEnvPathAdmissible F S (envBoxPathToEnvPath F S w hU hV γ) := by
        intro h
        exact hlast h.2.2
      simp [G, hadm, e1Vector, h0, hlast]
  · have hadm : ¬ IsEnvPathAdmissible F S (envBoxPathToEnvPath F S w hU hV γ) := by
      intro h
      exact h0 h.2.1
    simp [G, hadm, h0]

/-- `t2:pd.env-path-form` (new node) — PD 03:595-609, 04:68-80.  Expansion of the line-model
moment into path terms: `D_env(s_j)^{m_j}` (`m_j = 1` at the ends, `2` inside) splits into the
archimedean factor and the per-prime factors (the damping `q_d^{m_j(ω-KM)/2}` is
`∏_{p inactive} q_j^{1[hit]}`, `q_j = memoryQ`). -/
theorem env_path_form (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ (w : ArchRoot) (ℓ : LineData S.x K F.a),
          envMomentC F S w ℓ =
            ∑' γ : EnvPath S.x K,
              if IsEnvPathAdmissible F S γ then
                pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
                  ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
                    pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
              else 0 := by
  classical
  intro K F hF
  obtain ⟨x₀, hx₀, hBands⟩ := markedBands_eventually_disjoint F.a hF.1
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx w ℓ
  have hxpos : 0 < S.x := by linarith [hS.1]
  have hV : 0 < S.V := (Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.2.1
  have hY : 0 < S.Y := by
    rcases Finset.mem_filter.mp hS.2.2.2.2.2.1 with ⟨hm, _⟩
    rcases Finset.mem_image.mp hm with ⟨n, _, hn⟩
    rw [← hn]
    exact pow_pos (by norm_num : (0 : ℝ) < 2) n
  have hd : 0 < S.d₀ := by
    rcases Finset.mem_image.mp hS.2.2.2.2.2.2 with ⟨n, _, hn⟩
    rw [← hn]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) n
  have hU : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos (by exact_mod_cast hd) hY)
      ((Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.1)
  exact env_path_form_of_pos F S w ℓ hU hV (momentR_pos_of_two hS.1) hF.2.1
    (hBands S.x hx)


private def rootArch (u v : ℕ) : ArchRoot :=
  ⟨(u : ℝ), (v : ℝ), (rootC u v : ℝ) / (u : ℝ)⟩

private def rootEnvPoint {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (P : PState F S) : EnvPoint S.x K :=
  (rootTransportInv (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ) P.pos,
    P.labels)

private def RootEnvCondition {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (s : EnvPoint S.x K) : Prop :=
  EnvValid F S s ∧ envBox S (rootArch u v) s.1 ∧
    ∀ i j, lineHit (rootLines F S u v) (s.2 i j) s.1

private lemma rootEnvPoint_transport {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P : PState F S) :
    rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
      (rootEnvPoint F S u v P).1 = P.pos :=
  rootTransport_right_inv _ _ _ _ (rootD_completion_identity u v hu hc) P.pos

private lemma rootEnvPoint_valid {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P : PState F S) :
    EnvValid F S (rootEnvPoint F S u v P) := by
  have ht := rootEnvPoint_transport F S u v hu hc P
  have hg := gcd_rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
    (rootD_completion_identity u v hu hc) (rootEnvPoint F S u v P).1
  rw [ht] at hg
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rw [← hg]
    simpa [PhysicalState.pos] using P.primitive
  · exact fun i j => ⟨P.label_prime i j, P.label_in_band i j⟩
  · exact P.label_distinct

private lemma rootEnvPoint_box {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P : PState F S) :
    envBox S (rootArch u v) (rootEnvPoint F S u v P).1 := by
  have ht := rootEnvPoint_transport F S u v hu hc P
  have hfirst := rootTransport_first_real u v hu (rootEnvPoint F S u v P).1
  have hsecond := rootTransport_second_real u v hu hc (rootEnvPoint F S u v P).1
  rw [ht] at hfirst hsecond
  have h1 : (P.first : ℝ) = (u : ℝ) *
      (rootArch u v).tau (rootEnvPoint F S u v P).1 := by
    simpa [PhysicalState.pos, rootArch, ArchRoot.tau] using hfirst
  have h2 : (P.second : ℝ) = (v : ℝ) *
      (rootArch u v).tau (rootEnvPoint F S u v P).1 +
        ((rootEnvPoint F S u v P).1.2 : ℝ) / (u : ℝ) := by
    simpa [PhysicalState.pos, rootArch, ArchRoot.tau] using hsecond
  change S.U ≤ (u : ℝ) * (rootArch u v).tau (rootEnvPoint F S u v P).1 ∧
    (u : ℝ) * (rootArch u v).tau (rootEnvPoint F S u v P).1 ≤ 16 * S.U ∧
    S.V ≤ (v : ℝ) * (rootArch u v).tau (rootEnvPoint F S u v P).1 +
      ((rootEnvPoint F S u v P).1.2 : ℝ) / (u : ℝ) ∧
    (v : ℝ) * (rootArch u v).tau (rootEnvPoint F S u v P).1 +
      ((rootEnvPoint F S u v P).1.2 : ℝ) / (u : ℝ) ≤ 2 * S.V
  rw [← h1, ← h2]
  exact ⟨P.first_lower, by simpa [PDScale.U, mul_assoc] using P.first_upper,
    P.second_lower, P.second_upper⟩

private lemma rootEnvPoint_condition {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P : PState F S) :
    RootEnvCondition F S u v (rootEnvPoint F S u v P) := by
  have hv := rootEnvPoint_valid F S u v hu hc P
  refine ⟨hv, rootEnvPoint_box F S u v hu hc P, ?_⟩
  intro i j
  have hp : P.labels i j ∈ markedPrimes S.x K F.a :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, P.label_in_band i j⟩
  apply (rootLineHit_iff_dvd K F S u v (P.labels i j)
    (rootEnvPoint F S u v P).1 hp (P.label_prime i j) hu hc hv.1).2
  rw [rootEnvPoint_transport F S u v hu hc P]
  change (P.labels i j : ℤ) ∣ (P.first : ℤ)
  exact_mod_cast P.label_divides i j

private lemma physicalState_fields_ext {K : ℕ} (F : PDFix K) (S : PDScale)
    (P Q : PState F S) (hp : P.first = Q.first) (hq : P.second = Q.second)
    (hl : P.labels = Q.labels) : P = Q := by
  have hPpos : 0 < P.first := by
    have h : 0 ≤ P.completionC ∧ P.completionC < (P.first : ℤ) := P.completion_range
    omega
  have hQpos : 0 < Q.first := by omega
  obtain ⟨hPc, hPd⟩ := root_completion_unique P.first P.second hPpos P.primitive
    P.completionC P.completionD P.completion_range P.det_one
  obtain ⟨hQc, hQd⟩ := root_completion_unique Q.first Q.second hQpos Q.primitive
    Q.completionC Q.completionD Q.completion_range Q.det_one
  have hc : P.completionC = Q.completionC := by
    rw [hp, hq] at hPc
    exact hPc.trans hQc.symm
  have hd : P.completionD = Q.completionD := by
    rw [hp, hq] at hPd
    exact hPd.trans hQd.symm
  cases P
  cases Q
  cases hp
  cases hq
  cases hc
  cases hd
  cases hl
  rfl

private lemma rootEnvPoint_injective {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) :
    Function.Injective (rootEnvPoint F S u v) := by
  intro P Q h
  have ht : P.pos = Q.pos := by
    rw [← rootEnvPoint_transport F S u v hu hc P,
      ← rootEnvPoint_transport F S u v hu hc Q, h]
  change ((P.first : ℤ), (P.second : ℤ)) = ((Q.first : ℤ), (Q.second : ℤ)) at ht
  apply physicalState_fields_ext F S P Q
  · have h1 : (P.first : ℤ) = (Q.first : ℤ) := congrArg Prod.fst ht
    exact_mod_cast h1
  · have h2 : (P.second : ℤ) = (Q.second : ℤ) := congrArg Prod.snd ht
    exact_mod_cast h2
  · exact congrArg Prod.snd h

private lemma rootEnvPoint_surjective {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (s : EnvPoint S.x K) (hs : RootEnvCondition F S u v s) :
    ∃ P : PState F S, rootEnvPoint F S u v P = s := by
  let z := rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ) s.1
  have hdet := rootD_completion_identity u v hu hc
  have h1 : (z.1 : ℝ) = (rootArch u v).u * (rootArch u v).tau s.1 :=
    rootTransport_first_real u v hu s.1
  have h2 : (z.2 : ℝ) = (rootArch u v).v * (rootArch u v).tau s.1 +
      (s.1.2 : ℝ) / (rootArch u v).u := rootTransport_second_real u v hu hc s.1
  have hz1 : 0 < z.1 := by
    have hr : (0 : ℝ) < z.1 := lt_of_lt_of_le hU (h1.symm ▸ hs.2.1.1)
    exact_mod_cast hr
  have hz2 : 0 < z.2 := by
    have hr : (0 : ℝ) < z.2 := lt_of_lt_of_le hV (h2.symm ▸ hs.2.1.2.2.1)
    exact_mod_cast hr
  have hcast1 : (z.1.toNat : ℤ) = z.1 := Int.toNat_of_nonneg hz1.le
  have hcast2 : (z.2.toNat : ℤ) = z.2 := Int.toNat_of_nonneg hz2.le
  have hcast1R : (z.1.toNat : ℝ) = (z.1 : ℝ) := by exact_mod_cast hcast1
  have hcast2R : (z.2.toNat : ℝ) = (z.2 : ℝ) := by exact_mod_cast hcast2
  have hcop : Nat.Coprime z.1.toNat z.2.toNat := by
    have hg := gcd_rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
      hdet s.1
    have hg' : Int.gcd z.1 z.2 = 1 := hg.trans hs.1.1
    have hg'' : Int.gcd (z.1.toNat : ℤ) (z.2.toNat : ℤ) = 1 := by
      rw [hcast1, hcast2]
      exact hg'
    change Nat.gcd z.1.toNat z.2.toNat = 1
    simpa only [Int.gcd_natCast_natCast] using hg''
  have hp : 0 < z.1.toNat := by omega
  have hrange : 0 ≤ (rootC z.1.toNat z.2.toNat : ℤ) ∧
      (rootC z.1.toNat z.2.toNat : ℤ) < (z.1.toNat : ℤ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast rootC_lt_of_pos _ _ hp⟩
  let P : PState F S :=
    { first := z.1.toNat
      second := z.2.toNat
      completionC := (rootC z.1.toNat z.2.toNat : ℤ)
      completionD := (rootD z.1.toNat z.2.toNat : ℤ)
      labels := s.2
      primitive := hcop
      first_lower := by rw [hcast1R, h1]; exact hs.2.1.1
      first_upper := by
        rw [hcast1R, h1]
        simpa [PDScale.U, mul_assoc] using hs.2.1.2.1
      second_lower := by rw [hcast2R, h2]; exact hs.2.1.2.2.1
      second_upper := by rw [hcast2R, h2]; exact hs.2.1.2.2.2
      det_one := rootD_completion_identity _ _ hp hcop
      completion_range := hrange
      label_prime := fun i j => (hs.1.2.1 i j).1
      label_in_band := fun i j => (hs.1.2.1 i j).2
      label_divides := by
        intro i j
        have hmem : s.2 i j ∈ markedPrimes S.x K F.a :=
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (hs.1.2.1 i j).2⟩
        have hdvd := (rootLineHit_iff_dvd K F S u v (s.2 i j) s.1 hmem
          (hs.1.2.1 i j).1 hu hc hs.1.1).1 (hs.2.2 i j)
        change (s.2 i j : ℤ) ∣ z.1 at hdvd
        rw [← hcast1] at hdvd
        exact_mod_cast hdvd
      label_distinct := hs.1.2.2 }
  refine ⟨P, ?_⟩
  have hpos : P.pos = z := by
    apply Prod.ext
    · exact hcast1
    · exact hcast2
  apply Prod.ext
  · change rootTransportInv _ _ _ _ P.pos = s.1
    rw [hpos]
    exact rootTransport_left_inv _ _ _ _ hdet s.1
  · rfl

private def rootStateEquiv {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V) :
    PState F S ≃ {s : EnvPoint S.x K // RootEnvCondition F S u v s} :=
  Equiv.ofBijective
    (fun P => ⟨rootEnvPoint F S u v P, rootEnvPoint_condition F S u v hu hc P⟩)
    ⟨by
      intro P Q h
      exact rootEnvPoint_injective F S u v hu hc (congrArg Subtype.val h),
     by
      intro s
      obtain ⟨P, hp⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s.1 s.2
      exact ⟨P, Subtype.ext hp⟩⟩

private lemma physicalState_finite_of_pos {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) : Finite (PState F S) := by
  let f : PState F S → EnvBoxSubtype F S (rootArch 1 0) hU hV := fun P =>
    ⟨rootEnvPoint F S 1 0 P,
      (Set.Finite.mem_toFinset (envBoxValid_finite F S (rootArch 1 0) hU hV)).2
        ⟨rootEnvPoint_valid F S 1 0 (by decide) (by decide) P,
          rootEnvPoint_box F S 1 0 (by decide) (by decide) P⟩⟩
  apply Finite.of_injective f
  intro P Q h
  exact rootEnvPoint_injective F S 1 0 (by decide) (by decide) (congrArg Subtype.val h)

private lemma complementVec_det {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) :
    det2 z (complementVec z) = 1 := by
  have h := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at h
  simpa [det2, complementVec, sub_neg_eq_add, mul_comm, add_comm] using h.symm

private lemma rootEnvPoint_good {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U)
    (P : PState F S) :
    envGood F S (rootArch u v) (rootEnvPoint F S u v P) ↔
      IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) := by
  let z := (rootEnvPoint F S u v P).1
  let t := rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
    (complementVec z)
  have hv := rootEnvPoint_valid F S u v hu hc P
  have ht := rootEnvPoint_transport F S u v hu hc P
  have hdet := det2_rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ)
    (rootD u v : ℤ) (rootD_completion_identity u v hu hc) z (complementVec z)
  have hcomp : (P.first : ℤ) * t.2 - (P.second : ℤ) * t.1 = 1 := by
    change det2 P.pos t = 1
    rw [← ht]
    exact hdet.trans (complementVec_det hv.1)
  have hPpos : 0 < P.first := by
    have hh : (0 : ℝ) < P.first := hU.trans_le P.first_lower
    exact_mod_cast hh
  have hprim : Int.gcd (P.first : ℤ) (P.second : ℤ) = 1 := by
    simpa using P.primitive
  obtain ⟨k, hck, hdk⟩ := complements_differ_by_root (P.first : ℤ) (P.second : ℤ)
    t.1 t.2 P.completionC P.completionD (by exact_mod_cast hPpos.ne')
    hprim hcomp P.det_one
  have hfirst := rootTransport_first_real u v hu z
  rw [ht] at hfirst
  have hfirst' : (P.first : ℝ) = (u : ℝ) * (rootArch u v).tau z := by
    simpa [PhysicalState.pos, rootArch, ArchRoot.tau] using hfirst
  have hcompfirst : (t.1 : ℝ) = (u : ℝ) * (rootArch u v).tau (complementVec z) :=
    rootTransport_first_real u v hu (complementVec z)
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have htau : (rootArch u v).tau z ≠ 0 := by
    intro hh
    have hzero : (P.first : ℝ) = 0 := by simpa [hh] using hfirst'
    have hpR : (0 : ℝ) < P.first := by exact_mod_cast hPpos
    linarith
  have hratio : stateRoot P = transportedRatio (rootArch u v) z + (k : ℝ) := by
    have hckR : (P.completionC : ℝ) = (t.1 : ℝ) + (k : ℝ) * (P.first : ℝ) := by
      exact_mod_cast hck
    unfold stateRoot transportedRatio
    rw [hckR, hcompfirst, hfirst']
    field_simp [huR, htau]
  change IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels
    (transportedRatio (rootArch u v) z) ↔ _
  rw [hratio]
  exact (isGoodRatio_int_shift S.x S.Y (S.d₀ : ℝ) F.a P.labels
    (transportedRatio (rootArch u v) z) k).symm

private lemma markedOmega_eq_union_card {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (n : ℕ)
    (hBands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    markedOmega x K a n = ((markedPrimes x K a).filter (fun p => p ∣ n)).card := by
  classical
  unfold markedOmega bandOmega markedPrimes
  rw [Finset.filter_biUnion]
  symm
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact (hBands i j hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

private lemma rootEnvPoint_omega {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) (P : PState F S) :
    envOmega F S (rootLines F S u v) (rootEnvPoint F S u v P).1 =
      markedOmega S.x K F.a P.first := by
  classical
  rw [markedOmega_eq_union_card P.first hBands]
  unfold envOmega
  congr 1
  apply Finset.filter_congr
  intro p hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  have hprime : p.Prime := (Finset.mem_filter.mp hpi).2.1
  have hline := rootLineHit_iff_dvd K F S u v p (rootEnvPoint F S u v P).1 hp
    hprime hu hc (rootEnvPoint_valid F S u v hu hc P).1
  rw [rootEnvPoint_transport F S u v hu hc P] at hline
  change lineHit (rootLines F S u v) p (rootEnvPoint F S u v P).1 ↔
    (p : ℤ) ∣ (P.first : ℤ) at hline
  exact_mod_cast hline

private def physRootDiag {K : ℕ} (F : PDFix K) (S : PDScale) (P : PState F S) : ℝ :=
  if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) then
    dampingHalf F S P.first else 0

private lemma rootEnvPoint_diag {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) (P : PState F S) :
    envDiag F S (rootArch u v) (rootLines F S u v) (rootEnvPoint F S u v P) =
      physRootDiag F S P := by
  classical
  have hcond := rootEnvPoint_condition F S u v hu hc P
  have hgood := rootEnvPoint_good F S u v hu hc hU P
  by_cases hp : IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
  · have he := hgood.2 hp
    simp [envDiag, physRootDiag, hcond.1, hcond.2.1, hcond.2.2, he, hp,
      rootEnvPoint_omega F S u v hu hc hBands, dampingHalf]
  · have he : ¬ envGood F S (rootArch u v) (rootEnvPoint F S u v P) :=
      fun h => hp (hgood.1 h)
    simp [envDiag, physRootDiag, he, hp]

private lemma rootEnvPoint_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (P : PState F S)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    rootEnvPoint F S u v (P.permute σ) =
      ((rootEnvPoint F S u v P).1, permuteLists σ (rootEnvPoint F S u v P).2) := rfl

private lemma rootEnvCondition_permute {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (s : EnvPoint S.x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
    RootEnvCondition F S u v (s.1, permuteLists σ s.2) ↔ RootEnvCondition F S u v s := by
  unfold RootEnvCondition
  apply and_congr (envValid_permute F S σ s)
  apply and_congr Iff.rfl
  constructor
  · intro h i j
    simpa [permuteLists] using h i ((σ i).symm j)
  · intro h i j
    exact h i (σ i j)

private def rootExtend {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) (s : EnvPoint S.x K) : ℂ :=
  if hs : RootEnvCondition F S u v s then
    f ((rootStateEquiv F S u v hu hc hU hV).symm ⟨s, hs⟩) else 0

private lemma rootExtend_apply {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) (P : PState F S) :
    rootExtend F S u v hu hc hU hV f (rootEnvPoint F S u v P) = f P := by
  have hs := rootEnvPoint_condition F S u v hu hc P
  rw [rootExtend, dif_pos hs]
  have he : (⟨rootEnvPoint F S u v P, hs⟩ :
      {s : EnvPoint S.x K // RootEnvCondition F S u v s}) =
      rootStateEquiv F S u v hu hc hU hV P := rfl
  rw [he, Equiv.symm_apply_apply]

private lemma envDiag_zero_of_not_rootCondition {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (s : EnvPoint S.x K) (hs : ¬ RootEnvCondition F S u v s) :
    envDiag F S (rootArch u v) (rootLines F S u v) s = 0 := by
  unfold envDiag
  split_ifs with h
  · exact (hs ⟨h.1, h.2.1, h.2.2.2⟩).elim
  · rfl

private def physRootMul {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => (physRootDiag F S P : ℂ) * f P

private lemma rootExtend_mul {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) :
    rootExtend F S u v hu hc hU hV (physRootMul F S f) =
      envMul F S (rootArch u v) (rootLines F S u v)
        (rootExtend F S u v hu hc hU hV f) := by
  funext s
  by_cases hs : RootEnvCondition F S u v s
  · obtain ⟨P, rfl⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s hs
    rw [rootExtend_apply]
    simp only [envMul, rootExtend_apply, rootEnvPoint_diag F S u v hu hc hU hBands,
      physRootMul]
  · simp [rootExtend, hs, envMul, envDiag_zero_of_not_rootCondition F S u v s hs]

private lemma rootExtend_sym {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) :
    rootExtend F S u v hu hc hU hV (physSym F S f) =
      envSym F S (rootExtend F S u v hu hc hU hV f) := by
  funext s
  by_cases hs : RootEnvCondition F S u v s
  · obtain ⟨P, rfl⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s hs
    rw [rootExtend_apply]
    unfold physSym envSym
    congr 1
    apply Fintype.sum_congr
    intro σ
    rw [← rootEnvPoint_permute, rootExtend_apply]
  · have hz (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
        rootExtend F S u v hu hc hU hV f (s.1, permuteLists σ s.2) = 0 := by
      have hn : ¬ RootEnvCondition F S u v (s.1, permuteLists σ s.2) :=
        fun h => hs ((rootEnvCondition_permute F S u v s σ).1 h)
      simp [rootExtend, hn]
    rw [rootExtend, dif_neg hs]
    simp only [envSym, hz, Finset.sum_const_zero, mul_zero]

private def physRawRow {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => ∑' Q : PState F S,
    slotKernel F S P.labels Q.labels (det2 P.pos Q.pos) * f Q

private def physRawRowAdj {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => ∑' Q : PState F S,
    star (slotKernel F S Q.labels P.labels (det2 Q.pos P.pos)) * f Q

private lemma rootEnvPoint_det {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P Q : PState F S) :
    det2 (rootEnvPoint F S u v P).1 (rootEnvPoint F S u v Q).1 = det2 P.pos Q.pos := by
  have h := det2_rootTransport (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
    (rootD_completion_identity u v hu hc) (rootEnvPoint F S u v P).1
    (rootEnvPoint F S u v Q).1
  rw [rootEnvPoint_transport F S u v hu hc P,
    rootEnvPoint_transport F S u v hu hc Q] at h
  exact h.symm

private lemma rootExtend_row {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) (P : PState F S) :
    envRow F S (rootExtend F S u v hu hc hU hV f) (rootEnvPoint F S u v P) =
      physRawRow F S f P := by
  classical
  let G : EnvPoint S.x K → ℂ := fun s =>
    (if EnvValid F S s then slotKernel F S P.labels s.2
      (det2 (rootEnvPoint F S u v P).1 s.1) else 0) *
      rootExtend F S u v hu hc hU hV f s
  have hsupp : Function.support G ⊆ Set.range (rootEnvPoint F S u v) := by
    intro s hs
    have hcond : RootEnvCondition F S u v s := by
      by_contra h
      have hz : G s = 0 := by simp [G, rootExtend, h]
      exact hs hz
    exact rootEnvPoint_surjective F S u v hu hc hU hV s hcond
  have hsum := (rootEnvPoint_injective F S u v hu hc).tsum_eq hsupp
  change (∑' s, G s) = _
  rw [← hsum]
  apply tsum_congr
  intro Q
  have hv := rootEnvPoint_valid F S u v hu hc Q
  simp only [G, if_pos hv, rootExtend_apply, rootEnvPoint_det F S u v hu hc]
  rfl

private lemma rootExtend_rowAdj {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) (P : PState F S) :
    envRowAdj F S (rootExtend F S u v hu hc hU hV f) (rootEnvPoint F S u v P) =
      physRawRowAdj F S f P := by
  classical
  let G : EnvPoint S.x K → ℂ := fun s =>
    (if EnvValid F S s then star (slotKernel F S s.2 P.labels
      (det2 s.1 (rootEnvPoint F S u v P).1)) else 0) *
      rootExtend F S u v hu hc hU hV f s
  have hsupp : Function.support G ⊆ Set.range (rootEnvPoint F S u v) := by
    intro s hs
    have hcond : RootEnvCondition F S u v s := by
      by_contra h
      have hz : G s = 0 := by simp [G, rootExtend, h]
      exact hs hz
    exact rootEnvPoint_surjective F S u v hu hc hU hV s hcond
  have hsum := (rootEnvPoint_injective F S u v hu hc).tsum_eq hsupp
  change (∑' s, G s) = _
  rw [← hsum]
  apply tsum_congr
  intro Q
  have hv := rootEnvPoint_valid F S u v hu hc Q
  simp only [G, if_pos hv, rootExtend_apply, rootEnvPoint_det F S u v hu hc]
  rfl

private def physDampMul {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) : PState F S → ℂ :=
  fun P => (dampingHalf F S P.first : ℂ) * f P

private lemma physSym_damp {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    physSym F S (physDampMul F S f) = physDampMul F S (physSym F S f) := by
  funext P
  change ((permCount S.x K : ℂ))⁻¹ *
      (∑ σ, (dampingHalf F S P.first : ℂ) * f (P.permute σ)) =
    (dampingHalf F S P.first : ℂ) *
      (((permCount S.x K : ℂ))⁻¹ * ∑ σ, f (P.permute σ))
  rw [← Finset.mul_sum]
  ring

private lemma physDamp_good {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    physDampMul F S (physGood F S f) = physRootMul F S f := by
  funext P
  by_cases h : IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) <;>
    simp [physDampMul, physGood, physRootMul, physRootDiag, h]

private lemma physGood_damp {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    physGood F S (physDampMul F S f) = physRootMul F S f := by
  funext P
  by_cases h : IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P) <;>
    simp [physDampMul, physGood, physRootMul, physRootDiag, h]

private lemma physRow_factor {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    physRow F S f = physDampMul F S (physRawRow F S (physDampMul F S f)) := by
  funext P
  unfold physRow physDampMul physRawRow physRowKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro Q
  push_cast
  ring

private lemma physRowAdj_factor {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    physRowAdj F S f = physDampMul F S (physRawRowAdj F S (physDampMul F S f)) := by
  funext P
  unfold physRowAdj physDampMul physRawRowAdj physRowKernel
  rw [← tsum_mul_left]
  apply tsum_congr
  intro Q
  simp only [Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private lemma detOp_factor {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    detOp F S f = physRootMul F S
      (physSym F S (physRawRow F S (physSym F S (physRootMul F S f)))) := by
  unfold detOp
  rw [physRow_factor, physSym_damp, physGood_damp]
  have hinner : physDampMul F S (physSym F S (physGood F S f)) =
      physSym F S (physRootMul F S f) := by
    rw [← physSym_damp, physDamp_good]
  rw [hinner]

private lemma detOpAdj_factor {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) :
    detOpAdj F S f = physRootMul F S
      (physSym F S (physRawRowAdj F S (physSym F S (physRootMul F S f)))) := by
  unfold detOpAdj
  rw [physRowAdj_factor, physSym_damp, physGood_damp]
  have hinner : physDampMul F S (physSym F S (physGood F S f)) =
      physSym F S (physRootMul F S f) := by
    rw [← physSym_damp, physDamp_good]
  rw [hinner]

private lemma rootExtend_op_at {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) (P : PState F S) :
    envOp F S (rootArch u v) (rootLines F S u v)
      (rootExtend F S u v hu hc hU hV f) (rootEnvPoint F S u v P) = detOp F S f P := by
  unfold envOp
  rw [← rootExtend_mul F S u v hu hc hU hV hBands f, ← rootExtend_sym]
  rw [detOp_factor]
  change (envDiag F S (rootArch u v) (rootLines F S u v) (rootEnvPoint F S u v P) : ℂ) *
      (((permCount S.x K : ℂ))⁻¹ *
        ∑ σ, envRow F S (rootExtend F S u v hu hc hU hV
          (physSym F S (physRootMul F S f)))
            (rootEnvPoint F S u v (P.permute σ))) =
    (physRootDiag F S P : ℂ) * (((permCount S.x K : ℂ))⁻¹ *
      ∑ σ, physRawRow F S (physSym F S (physRootMul F S f)) (P.permute σ))
  rw [rootEnvPoint_diag F S u v hu hc hU hBands]
  congr 1
  congr 1
  apply Fintype.sum_congr
  intro σ
  exact rootExtend_row F S u v hu hc hU hV _ (P.permute σ)

private lemma rootExtend_opAdj_at {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) (P : PState F S) :
    envOpAdj F S (rootArch u v) (rootLines F S u v)
      (rootExtend F S u v hu hc hU hV f) (rootEnvPoint F S u v P) = detOpAdj F S f P := by
  unfold envOpAdj
  rw [← rootExtend_mul F S u v hu hc hU hV hBands f, ← rootExtend_sym]
  rw [detOpAdj_factor]
  change (envDiag F S (rootArch u v) (rootLines F S u v) (rootEnvPoint F S u v P) : ℂ) *
      (((permCount S.x K : ℂ))⁻¹ *
        ∑ σ, envRowAdj F S (rootExtend F S u v hu hc hU hV
          (physSym F S (physRootMul F S f)))
            (rootEnvPoint F S u v (P.permute σ))) =
    (physRootDiag F S P : ℂ) * (((permCount S.x K : ℂ))⁻¹ *
      ∑ σ, physRawRowAdj F S (physSym F S (physRootMul F S f)) (P.permute σ))
  rw [rootEnvPoint_diag F S u v hu hc hU hBands]
  congr 1
  congr 1
  apply Fintype.sum_congr
  intro σ
  exact rootExtend_rowAdj F S u v hu hc hU hV _ (P.permute σ)

private lemma rootExtend_op {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) :
    envOp F S (rootArch u v) (rootLines F S u v)
      (rootExtend F S u v hu hc hU hV f) =
      rootExtend F S u v hu hc hU hV (detOp F S f) := by
  funext s
  by_cases hs : RootEnvCondition F S u v s
  · obtain ⟨P, rfl⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s hs
    rw [rootExtend_apply]
    exact rootExtend_op_at F S u v hu hc hU hV hBands f P
  · simp [envOp, envMul, rootExtend, hs, envDiag_zero_of_not_rootCondition F S u v s hs]

private lemma rootExtend_opAdj {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) :
    envOpAdj F S (rootArch u v) (rootLines F S u v)
      (rootExtend F S u v hu hc hU hV f) =
      rootExtend F S u v hu hc hU hV (detOpAdj F S f) := by
  funext s
  by_cases hs : RootEnvCondition F S u v s
  · obtain ⟨P, rfl⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s hs
    rw [rootExtend_apply]
    exact rootExtend_opAdj_at F S u v hu hc hU hV hBands f P
  · simp [envOpAdj, envMul, rootExtend, hs, envDiag_zero_of_not_rootCondition F S u v s hs]

private lemma envMul_eq_extend_of_restriction {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (f : PState F S → ℂ) (g : EnvPoint S.x K → ℂ)
    (hfg : ∀ P, g (rootEnvPoint F S u v P) = f P) :
    envMul F S (rootArch u v) (rootLines F S u v) g =
      envMul F S (rootArch u v) (rootLines F S u v)
        (rootExtend F S u v hu hc hU hV f) := by
  funext s
  by_cases hs : RootEnvCondition F S u v s
  · obtain ⟨P, rfl⟩ := rootEnvPoint_surjective F S u v hu hc hU hV s hs
    simp only [envMul, rootExtend_apply, hfg]
  · simp [envMul, envDiag_zero_of_not_rootCondition F S u v s hs]

private lemma envOpAdj_eq_extend_of_restriction {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (f : PState F S → ℂ) (g : EnvPoint S.x K → ℂ)
    (hfg : ∀ P, g (rootEnvPoint F S u v P) = f P) :
    envOpAdj F S (rootArch u v) (rootLines F S u v) g =
      rootExtend F S u v hu hc hU hV (detOpAdj F S f) := by
  have hm := envMul_eq_extend_of_restriction F S u v hu hc hU hV f g hfg
  calc
    _ = envOpAdj F S (rootArch u v) (rootLines F S u v)
          (rootExtend F S u v hu hc hU hV f) := by
      unfold envOpAdj
      rw [hm]
    _ = _ := rootExtend_opAdj F S u v hu hc hU hV hBands f

private lemma rootEnvPoint_e1 {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (P : PState F S) :
    e1Vector (rootEnvPoint F S u v P) = positionVector F S u v P := by
  have he : (rootEnvPoint F S u v P).1 = (1, 0) ↔ P.first = u ∧ P.second = v := by
    constructor
    · intro h
      have ht := rootEnvPoint_transport F S u v hu hc P
      rw [h, rootTransport_e1] at ht
      change ((u : ℤ), (v : ℤ)) = ((P.first : ℤ), (P.second : ℤ)) at ht
      constructor
      · have h1 : (P.first : ℤ) = (u : ℤ) := (congrArg Prod.fst ht).symm
        exact_mod_cast h1
      · have h2 : (P.second : ℤ) = (v : ℤ) := (congrArg Prod.snd ht).symm
        exact_mod_cast h2
    · rintro ⟨h1, h2⟩
      have hp : P.pos = ((u : ℤ), (v : ℤ)) := by simp [PhysicalState.pos, h1, h2]
      have h := rootTransport_left_inv (u : ℤ) (v : ℤ) (rootC u v : ℤ) (rootD u v : ℤ)
        (rootD_completion_identity u v hu hc) (1, 0)
      rw [rootTransport_e1] at h
      simpa [rootEnvPoint, hp] using h
  simp only [e1Vector, positionVector, he]

private lemma rootEnvIter_restriction {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) (R : ℕ) :
    ∀ P : PState F S,
      (((fun f => envOp F S (rootArch u v) (rootLines F S u v)
        (envOpAdj F S (rootArch u v) (rootLines F S u v) f))^[R]) e1Vector)
          (rootEnvPoint F S u v P) =
        (((fun f => detOp F S (detOpAdj F S f))^[R]) (positionVector F S u v)) P := by
  let HE := fun f => envOp F S (rootArch u v) (rootLines F S u v)
    (envOpAdj F S (rootArch u v) (rootLines F S u v) f)
  let HP := fun f => detOp F S (detOpAdj F S f)
  induction R with
  | zero =>
      intro P
      exact rootEnvPoint_e1 F S u v hu hc P
  | succ R ih =>
      intro P
      have hAdj := envOpAdj_eq_extend_of_restriction F S u v hu hc hU hV hBands
        ((HP^[R]) (positionVector F S u v)) ((HE^[R]) e1Vector) ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change envOp F S (rootArch u v) (rootLines F S u v)
        (envOpAdj F S (rootArch u v) (rootLines F S u v) ((HE^[R]) e1Vector))
          (rootEnvPoint F S u v P) =
        detOp F S (detOpAdj F S ((HP^[R]) (positionVector F S u v))) P
      rw [hAdj]
      exact rootExtend_op_at F S u v hu hc hU hV hBands _ P

private lemma rootEnvIter_extend {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) (R : ℕ) (hR : 0 < R) :
    (((fun f => envOp F S (rootArch u v) (rootLines F S u v)
        (envOpAdj F S (rootArch u v) (rootLines F S u v) f))^[R]) e1Vector) =
      rootExtend F S u v hu hc hU hV
        (((fun f => detOp F S (detOpAdj F S f))^[R]) (positionVector F S u v)) := by
  obtain ⟨R, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hR.ne'
  let HE := fun f => envOp F S (rootArch u v) (rootLines F S u v)
    (envOpAdj F S (rootArch u v) (rootLines F S u v) f)
  let HP := fun f => detOp F S (detOpAdj F S f)
  have hAdj := envOpAdj_eq_extend_of_restriction F S u v hu hc hU hV hBands
    ((HP^[R]) (positionVector F S u v)) ((HE^[R]) e1Vector)
      (rootEnvIter_restriction F S u v hu hc hU hV hBands R)
  rw [Function.iterate_succ_apply']
  change envOp F S (rootArch u v) (rootLines F S u v)
      (envOpAdj F S (rootArch u v) (rootLines F S u v) ((HE^[R]) e1Vector)) = _
  rw [hAdj, rootExtend_op F S u v hu hc hU hV hBands]
  simp only [Function.iterate_succ_apply']
  rfl

private lemma rootMoment_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (u v : ℕ) (hu : 0 < u) (hc : Nat.Coprime u v) (hU : 0 < S.U) (hV : 0 < S.V)
    (hR : 0 < S.R)
    (hBands : ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j))) :
    envMomentC F S (rootArch u v) (rootLines F S u v) =
      physInner F S (positionVector F S u v)
        (((fun f => detOp F S (detOpAdj F S f))^[S.R]) (positionVector F S u v)) := by
  let HE := fun f => envOp F S (rootArch u v) (rootLines F S u v)
    (envOpAdj F S (rootArch u v) (rootLines F S u v) f)
  let HP := fun f => detOp F S (detOpAdj F S f)
  let G : EnvPoint S.x K → ℂ := fun s =>
    if EnvValid F S s then star (e1Vector s) * ((HE^[S.R]) e1Vector) s else 0
  have hiter := rootEnvIter_extend F S u v hu hc hU hV hBands S.R hR
  have hsupp : Function.support G ⊆ Set.range (rootEnvPoint F S u v) := by
    intro s hs
    have hcond : RootEnvCondition F S u v s := by
      by_contra hn
      have hz : G s = 0 := by
        dsimp [G, HE]
        rw [hiter]
        simp [rootExtend, hn]
      exact hs hz
    exact rootEnvPoint_surjective F S u v hu hc hU hV s hcond
  have hsum := (rootEnvPoint_injective F S u v hu hc).tsum_eq hsupp
  unfold envMomentC envInner physInner
  change (physicalMeasure S.x K F.a : ℂ) * (∑' s, G s) = _
  rw [← hsum]
  congr 1
  apply tsum_congr
  intro P
  have hv := rootEnvPoint_valid F S u v hu hc P
  simp only [G, if_pos hv, rootEnvPoint_e1 F S u v hu hc]
  congr 1
  exact rootEnvIter_restriction F S u v hu hc hU hV hBands S.R P

/-- `t2:pd.path-expansion` (new node) — PD 03:595-609.  Exact identity: the determinant moment is
the physical root average of the line-model moment.  Proof: `P ↦ z = g_P⁻¹ P` is a bijection of
primitive vectors with `det(gz,gz') = det(z,z')`; for integer `g`, `p ∣ (gz)₁ ⇔ [z]_p` equals the
kernel line of `(u,c)`; `r_{gz} = τ(w)/τ(z) mod 1` (03:683-685); `𝒢` and the damping commute
with `𝒮`.  The threshold makes the bands disjoint (so `markedOmega = envOmega`). -/
theorem path_expansion (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        detMoment F S = physicalRootAverage F S := by
  classical
  intro K F hF
  obtain ⟨x₀, hx₀, hBands⟩ := markedBands_eventually_disjoint F.a hF.1
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx
  have hxpos : 0 < S.x := by linarith [hS.1]
  have hV : 0 < S.V := (Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.2.1
  have hY : 0 < S.Y := by
    rcases Finset.mem_filter.mp hS.2.2.2.2.2.1 with ⟨hm, _⟩
    rcases Finset.mem_image.mp hm with ⟨n, _, hn⟩
    rw [← hn]
    exact pow_pos (by norm_num : (0 : ℝ) < 2) n
  have hd : 0 < S.d₀ := by
    rcases Finset.mem_image.mp hS.2.2.2.2.2.2 with ⟨n, _, hn⟩
    rw [← hn]
    exact pow_pos (by norm_num : (0 : ℕ) < 2) n
  have hU : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos (by exact_mod_cast hd) hY)
      ((Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.1)
  have hR : 0 < S.R := momentR_pos_of_two hS.1
  unfold detMoment physicalRootAverage
  congr 1
  apply tsum_congr
  intro uv
  by_cases hp : IsOmegaPosition S uv.1 uv.2
  · have hu : 0 < uv.1 := by
      have hr : (0 : ℝ) < uv.1 := hU.trans_le hp.2.1
      exact_mod_cast hr
    simp only [if_pos hp]
    exact congrArg Complex.re
      (rootMoment_eq F S uv.1 uv.2 hu hp.1 hU hV hR (hBands S.x hx)).symm
  · simp [hp]


/-! ### Sub-nodes of the root replacement -/

private lemma rootLift_canonical_iff (m u v : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod m))
    (hu : 0 < u) (hc : Nat.Coprime u v) (l r : ℝ) :
    (∃ c d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧
      0 ≤ c ∧ c < u ∧ l ≤ (c : ℝ) / u ∧ (c : ℝ) / u ≤ r ∧
      g 0 0 = (u : ZMod m) ∧ g 0 1 = (c : ZMod m) ∧
        g 1 0 = (v : ZMod m) ∧ g 1 1 = (d : ZMod m)) ↔
      (l ≤ (rootC u v : ℝ) / u ∧ (rootC u v : ℝ) / u ≤ r ∧
        g = rootCompletionMatrix m u v) := by
  constructor
  · rintro ⟨c, d, hdet, hc0, hclt, hl, hr, h00, h01, h10, h11⟩
    obtain ⟨hcEq, hdEq⟩ := root_completion_unique u v hu hc c d ⟨hc0, hclt⟩ hdet
    change d = (rootD u v : ℤ) at hdEq
    rw [hdEq] at h11
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcEq, Int.cast_natCast] using hl
    · simpa only [hcEq, Int.cast_natCast] using hr
    · apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j
      · simpa [rootCompletionMatrix] using h00
      · simpa [rootCompletionMatrix, hcEq] using h01
      · simpa [rootCompletionMatrix] using h10
      · simpa [rootCompletionMatrix] using h11
  · rintro ⟨hl, hr, hg⟩
    refine ⟨(rootC u v : ℤ), (rootD u v : ℤ), rootD_completion_identity u v hu hc,
      Nat.cast_nonneg _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast rootC_lt_of_pos u v hu
    · simpa only [Int.cast_natCast] using hl
    · simpa only [Int.cast_natCast] using hr
    · simp [hg, rootCompletionMatrix]
    · simp [hg, rootCompletionMatrix]
    · simp [hg, rootCompletionMatrix]
    · simp [hg, rootCompletionMatrix]

private lemma rootResidueCount_canonical (U V : ℝ) (hU : 0 < U)
    (m : ℕ) (g : Matrix (Fin 2) (Fin 2) (ZMod m))
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hl₁ : 1 ≤ l₁) :
    rootResidueCount U V m g l₁ r₁ l₂ r₂ l₃ r₃ =
      (Set.ncard {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
        l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
        l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
        l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃ ∧
        g = rootCompletionMatrix m uv.1 uv.2} : ℝ) := by
  unfold rootResidueCount
  apply congrArg (fun A : Set (ℕ × ℕ) => (A.ncard : ℝ))
  ext uv
  constructor
  · rintro ⟨hc, hl, hr, hlv, hrv, hlift⟩
    have huR : 0 < (uv.1 : ℝ) := by
      have hlow : 1 ≤ (uv.1 : ℝ) / U := hl₁.trans hl
      have hm := (le_div_iff₀ hU).1 hlow
      linarith
    have hu : 0 < uv.1 := by exact_mod_cast huR
    obtain ⟨hlc, hrc, hg⟩ := (rootLift_canonical_iff m uv.1 uv.2 g hu hc l₃ r₃).1 hlift
    exact ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc, hg⟩
  · rintro ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc, hg⟩
    exact ⟨hc, hl, hr, hlv, hrv, (rootLift_canonical_iff m uv.1 uv.2 g hu hc l₃ r₃).2
      ⟨hlc, hrc, hg⟩⟩

private lemma root_box_finite (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (r₁ r₂ : ℝ) (hr₁ : r₁ ≤ 16) (hr₂ : r₂ ≤ 2) :
    {uv : ℕ × ℕ | (uv.1 : ℝ) / U ≤ r₁ ∧ (uv.2 : ℝ) / V ≤ r₂}.Finite := by
  let T := Finset.range (⌈16 * U⌉₊ + 1) ×ˢ Finset.range (⌈2 * V⌉₊ + 1)
  apply T.finite_toSet.subset
  intro uv huv
  have hu : (uv.1 : ℝ) ≤ 16 * U :=
    (div_le_iff₀ hU).1 (huv.1.trans hr₁)
  have hv : (uv.2 : ℝ) ≤ 2 * V :=
    (div_le_iff₀ hV).1 (huv.2.trans hr₂)
  have hu' : uv.1 ≤ ⌈16 * U⌉₊ := by exact_mod_cast hu.trans (Nat.le_ceil _)
  have hv' : uv.2 ≤ ⌈2 * V⌉₊ := by exact_mod_cast hv.trans (Nat.le_ceil _)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩

private lemma root_residue_matrix_partition (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (m : ℕ) (T : Finset (Matrix (Fin 2) (Fin 2) (ZMod m)))
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hl₁ : 1 ≤ l₁) (hr₁ : r₁ ≤ 16) (hr₂ : r₂ ≤ 2) :
    (Set.ncard {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
      l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
      l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃ ∧
      rootCompletionMatrix m uv.1 uv.2 ∈ T} : ℝ) =
      ∑ g ∈ T, rootResidueCount U V m g l₁ r₁ l₂ r₂ l₃ r₃ := by
  classical
  let R : Set (ℕ × ℕ) := {uv | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
    l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
    l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
    l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃}
  have hR : R.Finite := (root_box_finite U V hU hV r₁ r₂ hr₁ hr₂).subset
    (fun uv huv => ⟨huv.2.2.2.1, huv.2.2.2.2.2.1⟩)
  let A := hR.toFinset
  let M := fun uv : ℕ × ℕ => rootCompletionMatrix m uv.1 uv.2
  let F := A.filter fun uv => M uv ∈ T
  have hA (uv : ℕ × ℕ) : uv ∈ A ↔ uv ∈ R := Set.Finite.mem_toFinset hR
  have hselected : {uv : ℕ × ℕ | uv ∈ R ∧ M uv ∈ T} = (F : Set (ℕ × ℕ)) := by
    ext uv
    simp only [Set.mem_setOf_eq, Finset.mem_coe, F, Finset.mem_filter, hA]
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := M) (s := F) (t := T) (fun uv huv => (Finset.mem_filter.mp huv).2)
  have hcount (g : Matrix (Fin 2) (Fin 2) (ZMod m)) (hg : g ∈ T) :
      rootResidueCount U V m g l₁ r₁ l₂ r₂ l₃ r₃ =
        ((F.filter fun uv => M uv = g).card : ℝ) := by
    rw [rootResidueCount_canonical U V hU m g l₁ r₁ l₂ r₂ l₃ r₃ hl₁]
    have he : {uv : ℕ × ℕ | uv ∈ R ∧ g = M uv} =
        ((F.filter fun uv => M uv = g) : Set (ℕ × ℕ)) := by
      ext uv
      constructor
      · rintro ⟨huv, hgm⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨(hA uv).2 huv, ?_⟩, hgm.symm⟩
        simpa only [hgm] using hg
      · intro huv
        obtain ⟨huv, hmg⟩ := Finset.mem_filter.mp huv
        exact ⟨(hA uv).1 (Finset.mem_filter.mp huv).1, hmg.symm⟩
    have hcountEq := congrArg (fun A : Set (ℕ × ℕ) => (A.ncard : ℝ)) he
    rw [Set.ncard_coe_finset] at hcountEq
    simpa only [R, M, Set.mem_setOf_eq, and_assoc] using hcountEq
  have hmain : (Set.ncard {uv : ℕ × ℕ | uv ∈ R ∧ M uv ∈ T} : ℝ) =
      ∑ g ∈ T, rootResidueCount U V m g l₁ r₁ l₂ r₂ l₃ r₃ := by
    rw [hselected, Set.ncard_coe_finset, hcard]
    push_cast
    apply Finset.sum_congr rfl
    intro g hg
    exact (hcount g hg).symm
  simpa only [R, M, Set.mem_setOf_eq, and_assoc] using hmain

private def matrixLineCondition (m : ℕ) (lam : (p : ℕ) → Fin (p + 1))
    (g : Matrix (Fin 2) (Fin 2) (ZMod m)) : Prop :=
  g.det = 1 ∧ ∀ p ∈ m.primeFactors, kernelLine p (g 0 0).val (g 0 1).val = lam p

private lemma kernelLine_mod (p a b : ℕ) :
    kernelLine p (a % p) (b % p) = kernelLine p a b := by
  simp [kernelLine, projLine]

private lemma root_matrix_line_condition (m u v : ℕ) (hm : 0 < m) (hu : 0 < u)
    (hc : Nat.Coprime u v) (lam : (p : ℕ) → Fin (p + 1)) :
    matrixLineCondition m lam (rootCompletionMatrix m u v) ↔
      ∀ p ∈ m.primeFactors, kernelLine p u (rootC u v) = lam p := by
  have hdet := rootCompletionMatrix_det m u v hu hc
  have he (p : ℕ) (hp : p ∈ m.primeFactors) :
      kernelLine p (rootCompletionMatrix m u v 0 0).val (rootCompletionMatrix m u v 0 1).val =
        kernelLine p u (rootC u v) :=
    (kernelLine_mod p _ _).symm.trans
      (rootCompletionMatrix_kernelLine m p u v hm (Nat.dvd_of_mem_primeFactors hp))
  constructor
  · intro h p hp
    rw [← he p hp]
    exact h.2 p hp
  · intro h
    refine ⟨hdet, ?_⟩
    intro p hp
    rw [he p hp]
    exact h p hp

private lemma root_lines_residue_partition (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (m : ℕ) (hm : 0 < m) (lam : (p : ℕ) → Fin (p + 1))
    (T : Finset (Matrix (Fin 2) (Fin 2) (ZMod m)))
    (hT : ∀ g, g ∈ T ↔ matrixLineCondition m lam g)
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hl₁ : 1 ≤ l₁) (hr₁ : r₁ ≤ 16) (hr₂ : r₂ ≤ 2) :
    (Set.ncard {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
      l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
      l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃ ∧
      ∀ p ∈ m.primeFactors, kernelLine p uv.1 (rootC uv.1 uv.2) = lam p} : ℝ) =
      ∑ g ∈ T, rootResidueCount U V m g l₁ r₁ l₂ r₂ l₃ r₃ := by
  have hpartition := root_residue_matrix_partition U V hU hV m T
    l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hr₁ hr₂
  rw [← hpartition]
  apply congrArg (fun A : Set (ℕ × ℕ) => (A.ncard : ℝ))
  ext uv
  constructor
  · rintro ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc, hlines⟩
    exact ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc,
      (hT _).2 ((root_matrix_line_condition m uv.1 uv.2 hm hu hc lam).2 hlines)⟩
  · rintro ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc, hmatrix⟩
    exact ⟨hc, hu, hl, hr, hlv, hrv, hlc, hrc,
      (root_matrix_line_condition m uv.1 uv.2 hm hu hc lam).1 ((hT _).1 hmatrix)⟩

private lemma matrix_kernel_infinity (p : ℕ) (hp : p.Prime)
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    kernelLine p (g 0 0).val (g 0 1).val = Fin.last p ↔ g 0 0 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := projLine_eq_last_iff p hp ((g 0 1).val, -((g 0 0).val : ℤ))
  simpa only [kernelLine, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val, neg_eq_zero] using h

private lemma matrix_kernel_finite (p : ℕ) (hp : p.Prime)
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) (lam : Fin (p + 1)) (hlam : lam ≠ Fin.last p)
    (ha : g 0 0 ≠ 0) :
    kernelLine p (g 0 0).val (g 0 1).val = lam ↔
      g 0 1 = -(lam.val : ZMod p) * g 0 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlt : lam.val < p := by
    have hb := lam.isLt
    have hn : lam.val ≠ p := fun h => hlam (Fin.ext h)
    omega
  let z : ℤ × ℤ := ((g 0 1).val, -((g 0 0).val : ℤ))
  let w : ℤ × ℤ := ((lam.val : ℤ), 1)
  have hz : (z.2 : ZMod p) ≠ 0 := by
    simpa only [z, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] using neg_ne_zero.mpr ha
  have hw : (w.2 : ZMod p) ≠ 0 := by simp [w]
  have hproj : projLine p w = lam := by
    apply Fin.ext
    simp [projLine, w, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt lam.isLt]
  have hc := projLine_eq_finite_cross_iff p hp z w hz hw
  rw [hproj] at hc
  simpa [z, w, kernelLine, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val,
    mul_neg, neg_mul] using hc

private lemma prime_kernel_fiber_card (p : ℕ) (hp : p.Prime) (lam : Fin (p + 1)) :
    Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p) //
      g.det = 1 ∧ kernelLine p (g 0 0).val (g 0 1).val = lam} = (p - 1) * p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hlast : lam = Fin.last p
  · have he : {g : Matrix (Fin 2) (Fin 2) (ZMod p) //
        g.det = 1 ∧ kernelLine p (g 0 0).val (g 0 1).val = lam} ≃
        {g : Matrix (Fin 2) (Fin 2) (ZMod p) // g.det = 1 ∧ g 0 0 = 0} :=
      Equiv.subtypeEquivRight (fun g => and_congr Iff.rfl (by
        rw [hlast]
        exact matrix_kernel_infinity p hp g))
    exact (Nat.card_congr he).trans (by simpa only [ZMod.card] using infinite_kernel_fiber_card (ZMod p))
  · have hpoint (g : Matrix (Fin 2) (Fin 2) (ZMod p)) :
        (g.det = 1 ∧ kernelLine p (g 0 0).val (g 0 1).val = lam) ↔
          (g.det = 1 ∧ g 0 0 ≠ 0 ∧ g 0 1 = -(lam.val : ZMod p) * g 0 0) := by
      by_cases ha : g 0 0 = 0
      · have hi := (matrix_kernel_infinity p hp g).2 ha
        have hn : ¬ kernelLine p (g 0 0).val (g 0 1).val = lam := by
          intro hh
          exact hlast (hh.symm.trans hi)
        constructor
        · intro h
          exact (hn h.2).elim
        · intro h
          exact (h.2.1 ha).elim
      · constructor
        · intro h
          exact ⟨h.1, ha, (matrix_kernel_finite p hp g lam hlast ha).1 h.2⟩
        · intro h
          exact ⟨h.1, (matrix_kernel_finite p hp g lam hlast ha).2 h.2.2⟩
    have he := Equiv.subtypeEquivRight hpoint
    exact (Nat.card_congr he).trans
      (by simpa only [ZMod.card] using finite_kernel_fiber_card (ZMod p) (lam.val : ZMod p))

private lemma prime_kernel_fiber_density (p : ℕ) (hp : p.Prime) (lam : Fin (p + 1)) :
    (Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p) //
      g.det = 1 ∧ kernelLine p (g 0 0).val (g 0 1).val = lam} : ℝ) =
        (sl2Card p hp.pos : ℝ) * ((p : ℝ) + 1)⁻¹ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have ht := sl2_matrix_card_by_kernel_lines (ZMod p)
  have htR : (sl2Card p hp.pos : ℝ) =
      ((p : ℝ) + 1) * (((p - 1) * p : ℕ) : ℝ) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) ht
    simpa only [sl2Card, Nat.card_eq_fintype_card, ZMod.card, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one] using hc
  rw [prime_kernel_fiber_card p hp lam, htR]
  have hn : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

private lemma matrix_kernel_cast (m p : ℕ) (hm : 0 < m) (hp : p.Prime) (hpm : p ∣ m)
    (g : Matrix (Fin 2) (Fin 2) (ZMod m)) :
    kernelLine p (g 0 0).val (g 0 1).val =
      kernelLine p ((ZMod.castHom hpm (ZMod p)) (g 0 0)).val
        ((ZMod.castHom hpm (ZMod p)) (g 0 1)).val := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : Fact p.Prime := ⟨hp⟩
  have he (x : ZMod m) : ZMod.castHom hpm (ZMod p) x = (x.val : ZMod p) := by
    rw [← ZMod.natCast_zmod_val x]
    simp
  rw [he, he, ZMod.val_natCast, ZMod.val_natCast]
  exact (kernelLine_mod p _ _).symm

private lemma matrix_line_fiber_density (m : ℕ) (hm : Squarefree m) (hpos : 0 < m)
    (lam : (p : ℕ) → Fin (p + 1)) :
    (Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod m) // matrixLineCondition m lam g} : ℝ) =
      (sl2Card m hpos : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) + 1)⁻¹ := by
  classical
  letI : NeZero m := ⟨hpos.ne'⟩
  letI : ∀ p : ModulusPrimes m, NeZero p.1 := fun p =>
    ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  let P := fun (p : ModulusPrimes m) (g : Matrix (Fin 2) (Fin 2) (ZMod p.1)) =>
    kernelLine p.1 (g 0 0).val (g 0 1).val = lam p.1
  have hpoint (g : Matrix (Fin 2) (Fin 2) (ZMod m)) :
      matrixLineCondition m lam g ↔ g.det = 1 ∧
        ∀ p : ModulusPrimes m,
          P p (fun a b => ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2) (ZMod p.1) (g a b)) := by
    constructor
    · intro h
      refine ⟨h.1, ?_⟩
      intro p
      exact (matrix_kernel_cast m p.1 hpos (Nat.prime_of_mem_primeFactors p.2)
        (Nat.dvd_of_mem_primeFactors p.2) g).symm.trans (h.2 p.1 p.2)
    · intro h
      refine ⟨h.1, ?_⟩
      intro p hp
      exact (matrix_kernel_cast m p hpos (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp) g).trans (h.2 ⟨p, hp⟩)
  have hcardNat : Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod m) // matrixLineCondition m lam g} =
      ∏ p : ModulusPrimes m, Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p.1) // g.det = 1 ∧ P p g} :=
    (Nat.card_congr (Equiv.subtypeEquivRight hpoint)).trans (sl2_squarefree_crt_card m hm hpos P)
  have htotalNat := sl2_squarefree_crt_card m hm hpos
    (fun (p : ModulusPrimes m) (_ : Matrix (Fin 2) (Fin 2) (ZMod p.1)) => True)
  have htotal : (sl2Card m hpos : ℝ) =
      ∏ p : ModulusPrimes m, (sl2Card p.1 (Nat.prime_of_mem_primeFactors p.2).pos : ℝ) := by
    have htrue : (∀ p : ModulusPrimes m, True) ↔ True := ⟨fun _ => True.intro, fun _ _ => True.intro⟩
    simp only [htrue, and_true] at htotalNat
    have hc := congrArg (fun n : ℕ => (n : ℝ)) htotalNat
    simpa only [sl2Card, Nat.card_eq_fintype_card, Nat.cast_prod] using hc
  have hprod : (∏ p : ModulusPrimes m, ((p.1 : ℝ) + 1)⁻¹) =
      ∏ p ∈ m.primeFactors, ((p : ℝ) + 1)⁻¹ := by
    change (∏ p ∈ m.primeFactors.attach, ((p.1 : ℝ) + 1)⁻¹) = _
    exact Finset.prod_attach (s := m.primeFactors) (f := fun p : ℕ => ((p : ℝ) + 1)⁻¹)
  have hcardReal : (Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod m) // matrixLineCondition m lam g} : ℝ) =
      ∏ p : ModulusPrimes m,
        (Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p.1) // g.det = 1 ∧ P p g} : ℝ) := by
    exact_mod_cast hcardNat
  calc
    _ = ∏ p : ModulusPrimes m,
        (Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p.1) // g.det = 1 ∧ P p g} : ℝ) := hcardReal
    _ = ∏ p : ModulusPrimes m,
        (sl2Card p.1 (Nat.prime_of_mem_primeFactors p.2).pos : ℝ) * ((p.1 : ℝ) + 1)⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact prime_kernel_fiber_density p.1 (Nat.prime_of_mem_primeFactors p.2) (lam p.1)
    _ = (∏ p : ModulusPrimes m, (sl2Card p.1 (Nat.prime_of_mem_primeFactors p.2).pos : ℝ)) *
        ∏ p : ModulusPrimes m, ((p.1 : ℝ) + 1)⁻¹ := Finset.prod_mul_distrib
    _ = _ := by rw [← htotal, hprod]

/-- `t2:pd.root-lines` (new node) — corollary of `lem:root-residue` (frozen `root_residue`),
PD 03:667-678.  Counting primitive roots in a box with prescribed kernel lines at the primes of a
squarefree `S`: the number of `g₀ ∈ SL₂(ℤ/S)` with prescribed first-row kernel lines is
`|SL₂(ℤ/S)| ∏_{p∣S} (p+1)⁻¹` (CRT; at each prime the kernel is uniform on the `p+1` lines). -/
theorem root_lines (δ C_K : ℝ) (hδ : 0 < δ) (hCK : 0 < C_K) :
    ∃ cδ C₀ x₀ : ℝ, cδ = δ / 1000 ∧ 0 < C₀ ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ U V : ℝ, Real.rpow x δ ≤ U → Real.rpow x δ ≤ V →
        ∀ Sq : ℕ, Squarefree Sq → 0 < Sq →
          (Sq : ℝ) ≤ Real.exp (C_K * Real.rpow (Real.log x) (98 / 100 : ℝ)) →
          ∀ lam : (p : ℕ) → Fin (p + 1),
          ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
            1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 16 → 1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 2 →
            0 ≤ l₃ → l₃ ≤ r₃ → r₃ ≤ 1 →
              |(Set.ncard {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
                  l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
                  l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
                  l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃ ∧
                  ∀ p ∈ Sq.primeFactors, kernelLine p uv.1 (rootC uv.1 uv.2) = lam p} : ℝ) -
                U * V * (r₁ - l₁) * (r₂ - l₂) * (r₃ - l₃) * (6 / Real.pi ^ 2) *
                  ∏ p ∈ Sq.primeFactors, ((p : ℝ) + 1)⁻¹| ≤
                C₀ * U * V * Real.rpow x (-cδ) := by
  sorry

/-- Closed grid cube of side `h` with integer index `k`, in the normalized root coordinates
`(u/U, v/V, r)`. -/
def gridCube (h : ℝ) (k : ℤ × ℤ × ℤ) : Set (ℝ × ℝ × ℝ) :=
  {y | (k.1 : ℝ) * h ≤ y.1 ∧ y.1 ≤ ((k.1 : ℝ) + 1) * h ∧
    (k.2.1 : ℝ) * h ≤ y.2.1 ∧ y.2.1 ≤ ((k.2.1 : ℝ) + 1) * h ∧
    (k.2.2 : ℝ) * h ≤ y.2.2 ∧ y.2.2 ≤ ((k.2.2 : ℝ) + 1) * h}

/-- Indices of the grid cubes meeting `[1,16] × [1,2] × [0,1]`. -/
def gridIndices (h : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉ ×ˢ (Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉ ×ˢ
    Finset.Icc (-1) ⌈1 / h⌉)

/-- A predicate is nonconstant on a set. -/
def IsNonconstantOn (P : ℝ × ℝ × ℝ → Prop) (A : Set (ℝ × ℝ × ℝ)) : Prop :=
  ∃ y ∈ A, ∃ y' ∈ A, P y ∧ ¬ P y'

private lemma small_integral_complement (z : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1) :
    ∃ t : ℤ × ℤ, det2 z t = 1 ∧
      |(t.1 : ℝ)| ≤ 1 + max |(z.1 : ℝ)| |(z.2 : ℝ)| ∧
      |(t.2 : ℝ)| ≤ 1 + max |(z.1 : ℝ)| |(z.2 : ℝ)| := by
  by_cases hzero : z.1 = 0
  · have habs : z.2.natAbs = 1 := by simpa [hzero] using hz
    have habsR : |(z.2 : ℝ)| = 1 := by
      have h : (z.2.natAbs : ℝ) = 1 := by exact_mod_cast habs
      simpa only [Nat.cast_natAbs, Int.cast_abs] using h
    have hsqR : (z.2 : ℝ) * (z.2 : ℝ) = 1 := by nlinarith [sq_abs (z.2 : ℝ)]
    have hsq : z.2 * z.2 = 1 := by exact_mod_cast hsqR
    refine ⟨(-z.2, 0), ?_, ?_, ?_⟩
    · simpa [det2, hzero] using hsq
    · simp only [Int.cast_neg, abs_neg]
      linarith [le_max_right |(z.1 : ℝ)| |(z.2 : ℝ)|]
    · simp only [Int.cast_zero, abs_zero]
      positivity
  · let u := z.1.natAbs
    let v := z.2.natAbs
    have hu : 0 < u := Int.natAbs_pos.mpr hzero
    have hcop : Nat.Coprime u v := hz
    let c := rootC u v
    let d := rootD u v
    have hc : c < u := rootC_lt_of_pos u v hu
    have hdet : (u : ℤ) * (d : ℤ) - (v : ℤ) * (c : ℤ) = 1 :=
      rootD_completion_identity u v hu hcop
    have hmul : u * d = v * c + 1 := by
      have hi : (u : ℤ) * (d : ℤ) = (v : ℤ) * (c : ℤ) + 1 := by linarith
      exact_mod_cast hi
    have hd : d ≤ v + 1 := by
      have hcu : v * c ≤ v * u := Nat.mul_le_mul_left v hc.le
      nlinarith
    let t : ℤ × ℤ := (z.2.sign * (c : ℤ), z.1.sign * (d : ℤ))
    have hsign (n : ℤ) : n.sign.natAbs ≤ 1 := by
      rw [Int.natAbs_sign]
      split_ifs <;> omega
    have ht1 : t.1.natAbs ≤ u := by
      dsimp [t]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      calc
        z.2.sign.natAbs * c ≤ c := by nlinarith [hsign z.2]
        _ ≤ u := hc.le
    have ht2 : t.2.natAbs ≤ v + 1 := by
      dsimp [t]
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      calc
        z.1.sign.natAbs * d ≤ d := by nlinarith [hsign z.1]
        _ ≤ v + 1 := hd
    have huR : (u : ℝ) = |(z.1 : ℝ)| := by simp [u, Nat.cast_natAbs]
    have hvR : (v : ℝ) = |(z.2 : ℝ)| := by simp [v, Nat.cast_natAbs]
    have ht1R : |(t.1 : ℝ)| ≤ (u : ℝ) := by
      have hh : (t.1.natAbs : ℝ) ≤ (u : ℝ) := by exact_mod_cast ht1
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have ht2R : |(t.2 : ℝ)| ≤ (v : ℝ) + 1 := by
      have hh : (t.2.natAbs : ℝ) ≤ ((v + 1 : ℕ) : ℝ) := by exact_mod_cast ht2
      simpa only [Nat.cast_natAbs, Int.cast_abs, Nat.cast_add, Nat.cast_one] using hh
    refine ⟨t, ?_, ?_, ?_⟩
    · change z.1 * (z.1.sign * (d : ℤ)) - z.2 * (z.2.sign * (c : ℤ)) = 1
      simpa only [← mul_assoc, Int.mul_sign_self] using hdet
    · rw [huR] at ht1R
      linarith [le_max_left |(z.1 : ℝ)| |(z.2 : ℝ)|]
    · rw [hvR] at ht2R
      linarith [le_max_right |(z.1 : ℝ)| |(z.2 : ℝ)|]

private lemma envBox_normalized (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V)
    (uu vv r : ℝ) (huu : 0 < uu) (z : ℤ × ℤ) :
    envBox S ⟨S.U * uu, S.V * vv, r⟩ z ↔
      1 ≤ uu * ((z.1 : ℝ) + r * (z.2 : ℝ)) ∧
      uu * ((z.1 : ℝ) + r * (z.2 : ℝ)) ≤ 16 ∧
      1 ≤ vv * ((z.1 : ℝ) + r * (z.2 : ℝ)) + (z.2 : ℝ) / (S.U * S.V * uu) ∧
      vv * ((z.1 : ℝ) + r * (z.2 : ℝ)) + (z.2 : ℝ) / (S.U * S.V * uu) ≤ 2 := by
  let tau := (z.1 : ℝ) + r * (z.2 : ℝ)
  let b := vv * tau + (z.2 : ℝ) / (S.U * S.V * uu)
  have h1 : (S.U * uu) * tau = S.U * (uu * tau) := by ring
  have h2 : (S.V * vv) * tau + (z.2 : ℝ) / (S.U * uu) = S.V * b := by
    dsimp [b]
    field_simp [hU.ne', hV.ne', huu.ne']
  change S.U ≤ (S.U * uu) * tau ∧ (S.U * uu) * tau ≤ 16 * S.U ∧
    S.V ≤ (S.V * vv) * tau + (z.2 : ℝ) / (S.U * uu) ∧
    (S.V * vv) * tau + (z.2 : ℝ) / (S.U * uu) ≤ 2 * S.V ↔
    1 ≤ uu * tau ∧ uu * tau ≤ 16 ∧ 1 ≤ b ∧ b ≤ 2
  rw [h1, h2]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨(mul_le_mul_iff_right₀ hU).mp (by simpa using h1),
      (mul_le_mul_iff_right₀ hU).mp (by simpa only [mul_comm S.U 16] using h2),
      (mul_le_mul_iff_right₀ hV).mp (by simpa using h3),
      (mul_le_mul_iff_right₀ hV).mp (by simpa only [mul_comm S.V 2] using h4)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by simpa using (mul_le_mul_iff_right₀ hU).mpr h1,
      by simpa only [mul_comm S.U 16] using (mul_le_mul_iff_right₀ hU).mpr h2,
      by simpa using (mul_le_mul_iff_right₀ hV).mpr h3,
      by simpa only [mul_comm S.V 2] using (mul_le_mul_iff_right₀ hV).mpr h4⟩

private lemma envGood_normalized {K : ℕ} (F : PDFix K) (S : PDScale)
    (uu vv r : ℝ) (s : EnvPoint S.x K) :
    envGood F S ⟨S.U * uu, S.V * vv, r⟩ s ↔ envGood F S ⟨1, 1, r⟩ s := Iff.rfl

private lemma circleDistance_eq_infDist (t : ℝ) :
    circleDistance t = Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ))) := by
  let A := Set.range (fun n : ℤ => (n : ℝ))
  have hA : A.Nonempty := ⟨0, ⟨0, by simp⟩⟩
  have himage : (dist t ·) '' A = Set.range (fun n : ℤ => |t - (n : ℝ)|) := by
    ext y
    constructor
    · rintro ⟨x, ⟨n, rfl⟩, h⟩
      exact ⟨n, by simpa only [Real.dist_eq] using h⟩
    · rintro ⟨n, h⟩
      exact ⟨(n : ℝ), ⟨n, rfl⟩, by simpa only [Real.dist_eq] using h⟩
  unfold circleDistance
  rw [← himage]
  exact (Metric.isGLB_infDist (x := t) hA).csInf_eq (hA.image _)

private lemma circleDistance_continuous : Continuous circleDistance := by
  have h : circleDistance = fun t : ℝ =>
      Metric.infDist t (Set.range (fun n : ℤ => (n : ℝ))) :=
    funext circleDistance_eq_infDist
  rw [h]
  exact Metric.continuous_infDist_pt _

private lemma circleDistance_nearest (t : ℝ) :
    ∃ n : ℤ, circleDistance t = |t - (n : ℝ)| := by
  have hclosed : IsClosed (Set.range (fun n : ℤ => (n : ℝ))) :=
    Int.isClosedEmbedding_coe_real.isClosed_range
  have hne : (Set.range (fun n : ℤ => (n : ℝ))).Nonempty := ⟨0, ⟨0, by simp⟩⟩
  obtain ⟨y, ⟨n, rfl⟩, hh⟩ := hclosed.exists_infDist_eq_dist hne t
  refine ⟨n, ?_⟩
  rw [circleDistance_eq_infDist, hh, Real.dist_eq]

private lemma circleDistance_level (t b : ℝ) (h : circleDistance t = b) :
    ∃ n : ℤ, t = (n : ℝ) + b ∨ t = (n : ℝ) - b := by
  obtain ⟨n, hn⟩ := circleDistance_nearest t
  refine ⟨n, ?_⟩
  rw [h] at hn
  rcases le_total 0 (t - (n : ℝ)) with hp | hp
  · rw [abs_of_nonneg hp] at hn
    exact Or.inl (by linarith)
  · rw [abs_of_nonpos hp] at hn
    exact Or.inr (by linarith)

private lemma continuousOn_le_iff_of_avoid_level {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (havoid : ∀ t ∈ Set.Icc a b, f t ≠ c) :
    (f a ≤ c ↔ f b ≤ c) := by
  constructor
  · intro ha
    by_contra hb
    have hc : c ∈ Set.Icc (f a) (f b) := ⟨ha, le_of_lt (lt_of_not_ge hb)⟩
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hf hc
    exact havoid t ht he
  · intro hb
    by_contra ha
    have hc : c ∈ Set.Icc (f b) (f a) := ⟨hb, le_of_lt (lt_of_not_ge ha)⟩
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hab hf hc
    exact havoid t ht he

private def fractionalRatio (z t : ℤ × ℤ) (r : ℝ) : ℝ :=
  ((t.1 : ℝ) + r * (t.2 : ℝ)) / ((z.1 : ℝ) + r * (z.2 : ℝ))

private lemma fractionalRatio_bound (z t : ℤ × ℤ) (Z r : ℝ)
    (hZ : 1 ≤ Z) (ht1 : |(t.1 : ℝ)| ≤ Z + 1) (ht2 : |(t.2 : ℝ)| ≤ Z + 1)
    (hr : -1 ≤ r ∧ r ≤ 2) (htau : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r * (z.2 : ℝ)) :
    |fractionalRatio z t r| ≤ 102 * (Z + 1) := by
  have hrabs : |r| ≤ 2 := abs_le.mpr ⟨by linarith [hr.1], hr.2⟩
  have hden : 0 < (z.1 : ℝ) + r * (z.2 : ℝ) := by linarith
  have hnum : |(t.1 : ℝ) + r * (t.2 : ℝ)| ≤ 3 * (Z + 1) := by
    calc
      _ ≤ |(t.1 : ℝ)| + |r * (t.2 : ℝ)| := abs_add_le _ _
      _ = |(t.1 : ℝ)| + |r| * |(t.2 : ℝ)| := by rw [abs_mul]
      _ ≤ (Z + 1) + 2 * (Z + 1) := by
        exact add_le_add ht1 (mul_le_mul hrabs ht2 (abs_nonneg _) (by norm_num))
      _ = 3 * (Z + 1) := by ring
  rw [fractionalRatio, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  nlinarith

private lemma fractionalRatio_level (z t : ℤ × ℤ) (hdet : det2 z t = 1)
    (m : ℤ) (hm : m ≠ 0) (r y : ℝ)
    (hden : (z.1 : ℝ) + r * (z.2 : ℝ) ≠ 0)
    (hlevel : (m : ℝ) * fractionalRatio z t r = y) :
    r = (y * (z.1 : ℝ) - (m : ℝ) * (t.1 : ℝ)) /
      ((m : ℝ) * (t.2 : ℝ) - y * (z.2 : ℝ)) := by
  have hdetR : (z.1 : ℝ) * (t.2 : ℝ) - (z.2 : ℝ) * (t.1 : ℝ) = 1 := by
    exact_mod_cast hdet
  have hlin : (m : ℝ) * ((t.1 : ℝ) + r * (t.2 : ℝ)) =
      y * ((z.1 : ℝ) + r * (z.2 : ℝ)) := by
    dsimp [fractionalRatio] at hlevel
    field_simp [hden] at hlevel
    simpa only [mul_comm y] using hlevel
  have hcoef : (m : ℝ) * (t.2 : ℝ) - y * (z.2 : ℝ) ≠ 0 := by
    intro hc
    have hconst : (m : ℝ) * (t.1 : ℝ) - y * (z.1 : ℝ) = 0 := by
      linear_combination hlin - r * hc
    have hmR : (m : ℝ) = 0 := by
      calc
        (m : ℝ) = (m : ℝ) *
          ((z.1 : ℝ) * (t.2 : ℝ) - (z.2 : ℝ) * (t.1 : ℝ)) := by rw [hdetR]; ring
        _ = (z.1 : ℝ) * ((m : ℝ) * (t.2 : ℝ) - y * (z.2 : ℝ)) -
          (z.2 : ℝ) * ((m : ℝ) * (t.1 : ℝ) - y * (z.1 : ℝ)) := by ring
        _ = 0 := by rw [hc, hconst]; ring
    exact hm (by exact_mod_cast hmR)
  apply (eq_div_iff hcoef).2
  linear_combination hlin

private def fractionalBreakpoint (z t : ℤ × ℤ) (i : ℤ × ℤ × ℝ × Bool) : ℝ :=
  let y := (i.2.1 : ℝ) + if i.2.2.2 then i.2.2.1 else -i.2.2.1
  (y * (z.1 : ℝ) - (i.1 : ℝ) * (t.1 : ℝ)) /
    ((i.1 : ℝ) * (t.2 : ℝ) - y * (z.2 : ℝ))

private def fractionalBreakpoints (z t : ℤ × ℤ) (Q T : ℕ) (B : Finset ℝ) : Finset ℝ :=
  ((Finset.Icc (-2 * (Q : ℤ)) (2 * (Q : ℤ))) ×ˢ
    ((Finset.Icc (-(T : ℤ)) (T : ℤ)) ×ˢ (B ×ˢ Finset.univ))).image
      (fractionalBreakpoint z t)

private lemma fractionalBreakpoints_card (z t : ℤ × ℤ) (Q T : ℕ) (B : Finset ℝ) :
    (fractionalBreakpoints z t Q T B).card ≤ (4 * Q + 1) * (2 * T + 1) * B.card * 2 := by
  have hQ : (Finset.Icc (-2 * (Q : ℤ)) (2 * (Q : ℤ))).card = 4 * Q + 1 := by
    rw [Int.card_Icc]
    omega
  have hT : (Finset.Icc (-(T : ℤ)) (T : ℤ)).card = 2 * T + 1 := by
    rw [Int.card_Icc]
    omega
  unfold fractionalBreakpoints
  calc
    _ ≤ _ := Finset.card_image_le
    _ = _ := by
      rw [Finset.card_product, Finset.card_product, Finset.card_product,
        hQ, hT, Finset.card_univ, Fintype.card_bool]
      ring

private lemma fractionalBreakpoints_level_mem (z t : ℤ × ℤ) (hdet : det2 z t = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) (ht1 : |(t.1 : ℝ)| ≤ Z + 1) (ht2 : |(t.2 : ℝ)| ≤ Z + 1)
    (Q T : ℕ) (hT : 204 * (Q : ℝ) * (Z + 1) + 101 ≤ (T : ℝ))
    (B : Finset ℝ) (b : ℝ) (hb : b ∈ B) (hb0 : 0 ≤ b) (hb100 : b ≤ 100)
    (m : ℤ) (hm : m ≠ 0) (hmQ : |m| ≤ 2 * (Q : ℤ)) (r : ℝ)
    (hr : -1 ≤ r ∧ r ≤ 2) (htau : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r * (z.2 : ℝ))
    (hlevel : circleDistance ((m : ℝ) * fractionalRatio z t r) = b) :
    r ∈ fractionalBreakpoints z t Q T B := by
  have hden : (z.1 : ℝ) + r * (z.2 : ℝ) ≠ 0 := by linarith
  have hratio := fractionalRatio_bound z t Z r hZ ht1 ht2 hr htau
  have hmQreal : |(m : ℝ)| ≤ 2 * (Q : ℝ) := by exact_mod_cast hmQ
  have hmbound : |(m : ℝ) * fractionalRatio z t r| ≤ 204 * (Q : ℝ) * (Z + 1) := by
    rw [abs_mul]
    have hh := mul_le_mul hmQreal hratio (abs_nonneg _) (by positivity : 0 ≤ 2 * (Q : ℝ))
    nlinarith
  obtain ⟨k, hk⟩ := circleDistance_level _ b hlevel
  have hkBound : |(k : ℝ)| ≤ (T : ℝ) := by
    have hbabs : |b| ≤ 100 := by simpa [abs_of_nonneg hb0] using hb100
    rcases hk with hk | hk
    · have he : (k : ℝ) = (m : ℝ) * fractionalRatio z t r - b := by linarith
      rw [he]
      have ha : |(m : ℝ) * fractionalRatio z t r - b| ≤
          |(m : ℝ) * fractionalRatio z t r| + |b| := by
        simpa using abs_sub_le ((m : ℝ) * fractionalRatio z t r) 0 b
      linarith
    · have he : (k : ℝ) = (m : ℝ) * fractionalRatio z t r + b := by linarith
      rw [he]
      have ha := abs_add_le ((m : ℝ) * fractionalRatio z t r) b
      linarith
  have hkT : |k| ≤ (T : ℤ) := by exact_mod_cast hkBound
  have hmMem : m ∈ Finset.Icc (-2 * (Q : ℤ)) (2 * (Q : ℤ)) := by
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp hmQ
    constructor <;> linarith
  have hkMem : k ∈ Finset.Icc (-(T : ℤ)) (T : ℤ) := Finset.mem_Icc.mpr (abs_le.mp hkT)
  rcases hk with hk | hk
  · have hs := fractionalRatio_level z t hdet m hm r ((k : ℝ) + b) hden hk
    apply Finset.mem_image.mpr
    refine ⟨(m, k, b, true), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hmMem,
        Finset.mem_product.mpr ⟨hkMem, Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩⟩⟩
    · simpa [fractionalBreakpoint] using hs.symm
  · have hs := fractionalRatio_level z t hdet m hm r ((k : ℝ) - b) hden hk
    apply Finset.mem_image.mpr
    refine ⟨(m, k, b, false), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hmMem,
        Finset.mem_product.mpr ⟨hkMem, Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩⟩⟩
    · simpa [fractionalBreakpoint, sub_eq_add_neg] using hs.symm

private lemma fractionalBreakpoints_circle_constant (z t : ℤ × ℤ) (hdet : det2 z t = 1)
    (Z : ℝ) (hZ : 1 ≤ Z) (ht1 : |(t.1 : ℝ)| ≤ Z + 1) (ht2 : |(t.2 : ℝ)| ≤ Z + 1)
    (Q T : ℕ) (hT : 204 * (Q : ℝ) * (Z + 1) + 101 ≤ (T : ℝ))
    (B : Finset ℝ) (b : ℝ) (hb : b ∈ B) (hb0 : 0 ≤ b) (hb100 : b ≤ 100)
    (m : ℤ) (hm : m ≠ 0) (hmQ : |m| ≤ 2 * (Q : ℤ))
    (a c : ℝ) (ha : -1 ≤ a) (hac : a ≤ c) (hc : c ≤ 2)
    (hsafe : ∀ r ∈ Set.Icc a c,
      (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r * (z.2 : ℝ) ∧
        r ∉ fractionalBreakpoints z t Q T B) :
    (circleDistance ((m : ℝ) * fractionalRatio z t a) ≤ b ↔
      circleDistance ((m : ℝ) * fractionalRatio z t c) ≤ b) := by
  have hden : ∀ r ∈ Set.Icc a c, (z.1 : ℝ) + r * (z.2 : ℝ) ≠ 0 := by
    intro r hr
    have hh := (hsafe r hr).1
    linarith
  have hratio : ContinuousOn (fractionalRatio z t) (Set.Icc a c) := by
    unfold fractionalRatio
    exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn.div
      (continuous_const.add (continuous_id.mul continuous_const)).continuousOn hden
  have hcircle : ContinuousOn (fun r => circleDistance ((m : ℝ) * fractionalRatio z t r))
      (Set.Icc a c) := circleDistance_continuous.comp_continuousOn
        (continuous_const.continuousOn.mul hratio)
  apply continuousOn_le_iff_of_avoid_level hac hcircle
  intro r hr hlevel
  exact (hsafe r hr).2 (fractionalBreakpoints_level_mem z t hdet Z hZ ht1 ht2 Q T hT
    B b hb hb0 hb100 m hm hmQ r ⟨ha.trans hr.1, hr.2.trans hc⟩ (hsafe r hr).1 hlevel)

private lemma complements_differ_by_primitive (z t t' : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (ht : det2 z t = 1) (ht' : det2 z t' = 1) :
    ∃ k : ℤ, t'.1 = t.1 + k * z.1 ∧ t'.2 = t.2 + k * z.2 := by
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by
      intro h
      simpa [h1, h] using hz
    have hcop : Int.gcd z.2 (-z.1) = 1 := by simpa [Int.gcd_comm] using hz
    have hdet : z.2 * (-t.1) - (-z.1) * t.2 = 1 := by
      change z.1 * t.2 - z.2 * t.1 = 1 at ht
      linear_combination ht
    have hdet' : z.2 * (-t'.1) - (-z.1) * t'.2 = 1 := by
      change z.1 * t'.2 - z.2 * t'.1 = 1 at ht'
      linear_combination ht'
    obtain ⟨k, hk2, hk1⟩ := complements_differ_by_root z.2 (-z.1) t.2 (-t.1)
      t'.2 (-t'.1) h2 hcop hdet hdet'
    exact ⟨k, by linear_combination -hk1, hk2⟩
  · exact complements_differ_by_root z.1 z.2 t.1 t.2 t'.1 t'.2 h1 hz ht ht'

private lemma envGood_fractionalRatio {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : EnvPoint S.x K) (hs : EnvValid F S s) (t : ℤ × ℤ) (ht : det2 s.1 t = 1)
    (r : ℝ) (hden : (s.1.1 : ℝ) + r * (s.1.2 : ℝ) ≠ 0) :
    envGood F S ⟨1, 1, r⟩ s ↔
      IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a s.2 (fractionalRatio s.1 t r) := by
  obtain ⟨k, hk1, hk2⟩ := complements_differ_by_primitive s.1 (complementVec s.1) t
    hs.1 (complementVec_det hs.1) ht
  have hratio : fractionalRatio s.1 t r = transportedRatio ⟨1, 1, r⟩ s.1 + (k : ℝ) := by
    have h1 : (t.1 : ℝ) = ((complementVec s.1).1 : ℝ) + (k : ℝ) * (s.1.1 : ℝ) := by
      exact_mod_cast hk1
    have h2 : (t.2 : ℝ) = ((complementVec s.1).2 : ℝ) + (k : ℝ) * (s.1.2 : ℝ) := by
      exact_mod_cast hk2
    unfold fractionalRatio transportedRatio ArchRoot.tau
    rw [h1, h2]
    field_simp [hden]
    ring
  rw [hratio]
  exact (isGoodRatio_int_shift S.x S.Y (S.d₀ : ℝ) F.a s.2
    (transportedRatio ⟨1, 1, r⟩ s.1) k).symm

private lemma primeBand_uniform_upper {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (hL : 1 ≤ S.L) (i : Fin K) (p : ℕ)
    (hp : p ∈ primeBand S.x (F.a i)) :
    (p : ℝ) ≤ Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by
  have h := (Finset.mem_filter.mp hp).2.2.2
  have ha : F.a i ≤ 1 / 5 := (hF.1.2.1 i).2.le
  exact h.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ha) (by norm_num)))

private lemma goodnessTrialValue_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (hL : 1 ≤ S.L) (p : PrimeLists S.x K)
    (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ)
    (hfresh : IsFreshChoice S.x F.a I fresh)
    (hn : IsGoodnessTrialValue F.a p (S.d₀ : ℝ) I iStar fresh n) :
    (n : ℝ) ≤ 2 * (S.d₀ : ℝ) *
      Real.exp (4 * (K : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) := by
  classical
  obtain ⟨omitted, z, hneq, hDlow, hDhi, hz⟩ := hn
  let P := Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))
  have hP : 1 ≤ P := Real.one_le_exp_iff.mpr (by dsimp [P]; positivity)
  have hZprod : ((∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1 : ℕ) : ℝ) ≤ P ^ K := by
    push_cast
    calc
      _ ≤ ∏ i : Fin K, P := by
        apply Finset.prod_le_prod₀
        · intro i hi
          split_ifs <;> positivity
        · intro i hi
          split_ifs with hh
          · exact primeBand_uniform_upper F S hF hL i (z i) (hz i hh)
          · exact hP
      _ = P ^ K := by simp
  have hFprod : ((∏ i : Fin K, if i ∉ I then fresh i else 1 : ℕ) : ℝ) ≤ P ^ K := by
    push_cast
    calc
      _ ≤ ∏ i : Fin K, P := by
        apply Finset.prod_le_prod₀
        · intro i hi
          split_ifs <;> positivity
        · intro i hi
          split_ifs with hh
          · exact hP
          · exact primeBand_uniform_upper F S hF hL i (fresh i) (hfresh.2 i hh)
      _ = P ^ K := by simp
  have hprodnonneg : 0 ≤ ((∏ i : Fin K, if i ∉ I then fresh i else 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hZnonneg : 0 ≤ P ^ K := by positivity
  have hprods :
      ((∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1 : ℕ) : ℝ) *
        ((∏ i : Fin K, if i ∉ I then fresh i else 1 : ℕ) : ℝ) ≤ P ^ K * P ^ K :=
    mul_le_mul hZprod hFprod hprodnonneg hZnonneg
  have hPpower : P ^ K * P ^ K =
      Real.exp (4 * (K : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) := by
    dsimp [P]
    simp_rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hneq]
  push_cast
  calc
    _ ≤ (2 * (S.d₀ : ℝ)) *
        (((∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1 : ℕ) : ℝ) *
          ((∏ i : Fin K, if i ∉ I then fresh i else 1 : ℕ) : ℝ)) := by
      have hDn : 0 ≤ (omissionProduct p omitted : ℝ) := Nat.cast_nonneg _
      have hprod0 : 0 ≤
          ((∏ i : Fin K, if i ∈ I ∧ i ≠ iStar then z i else 1 : ℕ) : ℝ) *
          ((∏ i : Fin K, if i ∉ I then fresh i else 1 : ℕ) : ℝ) := by positivity
      have hh := mul_le_mul_of_nonneg_right hDhi.le hprod0
      push_cast at hh
      convert hh using 1 <;> push_cast <;> ring
    _ ≤ (2 * (S.d₀ : ℝ)) * (P ^ K * P ^ K) :=
      mul_le_mul_of_nonneg_left hprods (by positivity)
    _ = _ := by rw [hPpower]

private def goodThresholds {K : ℕ} (F : PDFix K) (S : PDScale) : Finset ℝ :=
  insert (Real.rpow S.Y (-(7 / 10 : ℝ)))
    (Finset.univ.image fun i : Fin K => 100 * Real.exp (-Real.rpow S.L (F.a i)))

private lemma goodThresholds_card {K : ℕ} (F : PDFix K) (S : PDScale) :
    (goodThresholds F S).card ≤ K + 1 := by
  unfold goodThresholds
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans (by simp)) 1)

private lemma goodThresholds_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hY : 1 ≤ S.Y) (hL : 1 ≤ S.L) (b : ℝ) (hb : b ∈ goodThresholds F S) :
    0 ≤ b ∧ b ≤ 100 := by
  rcases Finset.mem_insert.mp hb with rfl | hb
  · constructor
    · exact Real.rpow_nonneg (by linarith) _
    · exact (Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)).trans (by norm_num)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    constructor
    · positivity
    · have he : Real.exp (-Real.rpow S.L (F.a i)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (by linarith) _))
      linarith

private lemma goodTestTwo_congr_of_atoms (x d₀ : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (r r' : ℝ)
    (hAtoms : ∀ I : Finset (Fin K), ∀ hI : I.Nonempty, ∀ fresh : Fin K → ℕ,
      IsFreshChoice x a I fresh → ∀ n₁ n₂ : ℕ,
      IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ →
      IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ → n₁ ≠ n₂ →
      (circleDistance (((n₁ : ℝ) - n₂) * r) ≤
        100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI))) ↔
       circleDistance (((n₁ : ℝ) - n₂) * r') ≤
        100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI))))) :
    goodTestTwo x d₀ K a p r ↔ goodTestTwo x d₀ K a p r' := by
  classical
  have hvalue (I : Finset (Fin K)) (hI : I.Nonempty) :
      (∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
          ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r) ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
        then freshChoiceWeight x a I fresh else 0) =
      (∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
          ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r') ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
        then freshChoiceWeight x a I fresh else 0) := by
    apply tsum_congr
    intro fresh
    by_cases hfresh : IsFreshChoice x a I fresh
    · have hpairs :
          (∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r) ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))) ↔
          (∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r') ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))) := by
        constructor
        · rintro ⟨n₁, n₂, hn₁, hn₂, hne, hc⟩
          exact ⟨n₁, n₂, hn₁, hn₂, hne, (hAtoms I hI fresh hfresh n₁ n₂ hn₁ hn₂ hne).1 hc⟩
        · rintro ⟨n₁, n₂, hn₁, hn₂, hne, hc⟩
          exact ⟨n₁, n₂, hn₁, hn₂, hne, (hAtoms I hI fresh hfresh n₁ n₂ hn₁ hn₂ hne).2 hc⟩
      simp only [hfresh, true_and, hpairs]
    · simp [hfresh]
  unfold goodTestTwo
  constructor
  · intro h I hI
    dsimp only
    rw [← hvalue I hI]
    exact h I hI
  · intro h I hI
    dsimp only
    rw [hvalue I hI]
    exact h I hI

private lemma envGood_breakpoints {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (s : EnvPoint S.x K) (hs : EnvValid F S s)
    (Z : ℝ) (hZ : 1 ≤ Z) (hz1 : |(s.1.1 : ℝ)| ≤ Z) (hz2 : |(s.1.2 : ℝ)| ≤ Z)
    (hY : 1 ≤ S.Y) (hD : 1 ≤ S.d₀) (Q T : ℕ)
    (hQ1 : 2 * (S.d₀ : ℝ) * Real.rpow S.Y (1 / 5 : ℝ) ≤ (Q : ℝ))
    (hQ2 : 2 * (S.d₀ : ℝ) *
      Real.exp (4 * (K : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) ≤ (Q : ℝ))
    (hT : 204 * (Q : ℝ) * (Z + 1) + 101 ≤ (T : ℝ)) (hL : 1 ≤ S.L) :
    ∃ B : Finset ℝ, B.card ≤ 2 * (K + 1) * (4 * Q + 1) * (2 * T + 1) ∧
      ∀ r r' : ℝ, -1 ≤ r → r ≤ r' → r' ≤ 2 →
        (∀ v ∈ Set.Icc r r', (1 / 34 : ℝ) ≤ (v * (s.1.2 : ℝ) + s.1.1) ∧
          (v * (s.1.2 : ℝ) + s.1.1) ≤ 34 ∧ v ∉ B) →
        (envGood F S ⟨1, 1, r⟩ s ↔ envGood F S ⟨1, 1, r'⟩ s) := by
  classical
  obtain ⟨t, ht, ht1, ht2⟩ := small_integral_complement s.1 hs.1
  have ht1' : |(t.1 : ℝ)| ≤ Z + 1 := by
    have hm : max |(s.1.1 : ℝ)| |(s.1.2 : ℝ)| ≤ Z := max_le hz1 hz2
    linarith
  have ht2' : |(t.2 : ℝ)| ≤ Z + 1 := by
    have hm : max |(s.1.1 : ℝ)| |(s.1.2 : ℝ)| ≤ Z := max_le hz1 hz2
    linarith
  let B := fractionalBreakpoints s.1 t Q T (goodThresholds F S)
  refine ⟨B, ?_, ?_⟩
  · calc
      B.card ≤ (4 * Q + 1) * (2 * T + 1) * (goodThresholds F S).card * 2 :=
        fractionalBreakpoints_card _ _ _ _ _
      _ ≤ (4 * Q + 1) * (2 * T + 1) * (K + 1) * 2 := by
        gcongr
        exact goodThresholds_card F S
      _ = 2 * (K + 1) * (4 * Q + 1) * (2 * T + 1) := by ring
  · intro r r' hr hrr hr' hsafe
    have hden (v : ℝ) (hv : v ∈ Set.Icc r r') :
        (s.1.1 : ℝ) + v * (s.1.2 : ℝ) ≠ 0 := by
      have hh := (hsafe v hv).1
      linarith
    have hAtomic (m : ℤ) (hm : m ≠ 0) (hmQ : |m| ≤ 2 * (Q : ℤ))
        (b : ℝ) (hb : b ∈ goodThresholds F S) :
        (circleDistance ((m : ℝ) * fractionalRatio s.1 t r) ≤ b ↔
          circleDistance ((m : ℝ) * fractionalRatio s.1 t r') ≤ b) := by
      have hbb := goodThresholds_bounds F S hY hL b hb
      apply fractionalBreakpoints_circle_constant s.1 t ht Z hZ ht1' ht2' Q T hT
        (goodThresholds F S) b hb hbb.1 hbb.2 m hm hmQ r r' hr hrr hr'
      intro v hv
      refine ⟨?_, (hsafe v hv).2.2⟩
      simpa [add_comm] using (hsafe v hv).1
    rw [envGood_fractionalRatio F S s hs t ht r (hden r (Set.left_mem_Icc.mpr hrr)),
      envGood_fractionalRatio F S s hs t ht r' (hden r' (Set.right_mem_Icc.mpr hrr))]
    apply and_congr
    · have hOneAtom (omitted : Fin K → Fin (slotCount S.x))
          (hlo : (S.d₀ : ℝ) ≤ (omissionProduct s.2 omitted : ℝ))
          (hhi : (omissionProduct s.2 omitted : ℝ) < 2 * (S.d₀ : ℝ))
          (l : ℕ) (hl : 1 ≤ l) (hly : (l : ℝ) ≤ Real.rpow S.Y (1 / 5 : ℝ)) :
          (Real.rpow S.Y (-(7 / 10 : ℝ)) <
            circleDistance ((l : ℝ) * (omissionProduct s.2 omitted : ℝ) * fractionalRatio s.1 t r) ↔
           Real.rpow S.Y (-(7 / 10 : ℝ)) <
            circleDistance ((l : ℝ) * (omissionProduct s.2 omitted : ℝ) * fractionalRatio s.1 t r')) := by
        let m : ℤ := (l : ℤ) * (omissionProduct s.2 omitted : ℤ)
        have hDpos : 0 < omissionProduct s.2 omitted := by
          have hdreal : (1 : ℝ) ≤ S.d₀ := by exact_mod_cast hD
          have hh : (1 : ℝ) ≤ omissionProduct s.2 omitted := hdreal.trans hlo
          have hnat : 1 ≤ omissionProduct s.2 omitted := by exact_mod_cast hh
          omega
        have hm : m ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : l ≠ 0))
          (by exact_mod_cast hDpos.ne')
        have hmReal : (m : ℝ) = (l : ℝ) * (omissionProduct s.2 omitted : ℝ) := by simp [m]
        have hm0 : 0 ≤ (m : ℝ) := by rw [hmReal]; positivity
        have hmBound : (m : ℝ) ≤ (Q : ℝ) := by
          rw [hmReal]
          have hh := mul_le_mul hly hhi.le (by positivity : 0 ≤ (omissionProduct s.2 omitted : ℝ))
            (Real.rpow_nonneg (by linarith : 0 ≤ S.Y) _)
          have hh' : (l : ℝ) * (omissionProduct s.2 omitted : ℝ) ≤
              2 * (S.d₀ : ℝ) * Real.rpow S.Y (1 / 5 : ℝ) := by
            simpa [mul_comm] using hh
          exact hh'.trans hQ1
        have hmAbs : |m| ≤ 2 * (Q : ℤ) := by
          have hh : |(m : ℝ)| ≤ 2 * (Q : ℝ) := by rw [abs_of_nonneg hm0]; linarith
          exact_mod_cast hh
        have hc := not_congr (hAtomic m hm hmAbs (Real.rpow S.Y (-(7 / 10 : ℝ)))
          (Finset.mem_insert_self _ _))
        simpa only [not_le, hmReal] using hc
      unfold goodTestOne
      constructor
      · intro h omitted hlo hhi l hl hly
        exact (hOneAtom omitted hlo hhi l hl hly).1 (h omitted hlo hhi l hl hly)
      · intro h omitted hlo hhi l hl hly
        exact (hOneAtom omitted hlo hhi l hl hly).2 (h omitted hlo hhi l hl hly)
    · apply goodTestTwo_congr_of_atoms
      intro I hI fresh hfresh n₁ n₂ hn₁ hn₂ hne
      let m : ℤ := (n₁ : ℤ) - (n₂ : ℤ)
      have hm : m ≠ 0 := by
        intro hh
        have he : (n₁ : ℤ) = (n₂ : ℤ) := sub_eq_zero.mp hh
        exact hne (by exact_mod_cast he)
      have hmReal : (m : ℝ) = (n₁ : ℝ) - (n₂ : ℝ) := by simp [m]
      have hn₁Bound : (n₁ : ℝ) ≤ (Q : ℝ) :=
        (goodnessTrialValue_bound F S hF hL s.2 I (I.max' hI) fresh n₁ hfresh hn₁).trans hQ2
      have hn₂Bound : (n₂ : ℝ) ≤ (Q : ℝ) :=
        (goodnessTrialValue_bound F S hF hL s.2 I (I.max' hI) fresh n₂ hfresh hn₂).trans hQ2
      have hmAbs : |m| ≤ 2 * (Q : ℤ) := by
        have hh : |(m : ℝ)| ≤ 2 * (Q : ℝ) := by
          rw [hmReal]
          apply abs_le.mpr
          constructor <;> nlinarith
            [show (0 : ℝ) ≤ (n₁ : ℝ) from Nat.cast_nonneg _,
              show (0 : ℝ) ≤ (n₂ : ℝ) from Nat.cast_nonneg _]
        exact_mod_cast hh
      have hb : 100 * Real.exp (-Real.rpow S.L (F.a (I.max' hI))) ∈ goodThresholds F S :=
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨I.max' hI, Finset.mem_univ _, rfl⟩)
      simpa only [hmReal, PDScale.L] using hAtomic m hm hmAbs _ hb

private lemma grid_axis_bounds (h l r : ℝ) (hh : 0 < h) (k : ℤ) (y : ℝ)
    (hk : k ∈ Finset.Icc (⌊l / h⌋ - 1) ⌈r / h⌉)
    (hy : (k : ℝ) * h ≤ y ∧ y ≤ ((k : ℝ) + 1) * h) :
    l - 2 * h ≤ y ∧ y ≤ r + 2 * h := by
  have hkm := Finset.mem_Icc.mp hk
  have hklo : (⌊l / h⌋ : ℝ) - 1 ≤ (k : ℝ) := by exact_mod_cast hkm.1
  have hkhi : (k : ℝ) ≤ (⌈r / h⌉ : ℝ) := by exact_mod_cast hkm.2
  have hf := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (l / h)) hh
  have hc := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r / h)) hh
  rw [div_mul_cancel₀ l hh.ne'] at hf
  rw [add_mul, div_mul_cancel₀ r hh.ne', one_mul] at hc
  have hkl := mul_le_mul_of_nonneg_right hklo hh.le
  have hkh := mul_le_mul_of_nonneg_right hkhi hh.le
  constructor <;> nlinarith [hy.1, hy.2]

private lemma grid_cube_domain_bounds (h : ℝ) (hh : 0 < h) (hhsmall : h ≤ 1 / 8)
    (k : ℤ × ℤ × ℤ) (hk : k ∈ gridIndices h) (y : ℝ × ℝ × ℝ)
    (hy : y ∈ gridCube h k) :
    (1 / 2 : ℝ) ≤ y.1 ∧ y.1 ≤ 17 ∧
      (1 / 2 : ℝ) ≤ y.2.1 ∧ y.2.1 ≤ 3 ∧ -1 ≤ y.2.2 ∧ y.2.2 ≤ 2 := by
  have hk' := Finset.mem_product.mp hk
  have hk'' := Finset.mem_product.mp hk'.2
  have h1 := grid_axis_bounds h 1 16 hh k.1 y.1 hk'.1 ⟨hy.1, hy.2.1⟩
  have h2 := grid_axis_bounds h 1 2 hh k.2.1 y.2.1 hk''.1 ⟨hy.2.2.1, hy.2.2.2.1⟩
  have hk3 : k.2.2 ∈ Finset.Icc (⌊(0 : ℝ) / h⌋ - 1) ⌈1 / h⌉ := by
    simpa using hk''.2
  have h3 := grid_axis_bounds h 0 1 hh k.2.2 y.2.2 hk3 ⟨hy.2.2.2.2.1, hy.2.2.2.2.2⟩
  exact ⟨by linarith [h1.1], by linarith [h1.2], by linarith [h2.1],
    by linarith [h2.2], by linarith [h3.1], by linarith [h3.2]⟩

private lemma grid_cube_coordinate_diff (h : ℝ) (k : ℤ × ℤ × ℤ)
    (y y' : ℝ × ℝ × ℝ) (hy : y ∈ gridCube h k) (hy' : y' ∈ gridCube h k) :
    |y.1 - y'.1| ≤ h ∧ |y.2.1 - y'.2.1| ≤ h ∧ |y.2.2 - y'.2.2| ≤ h := by
  constructor
  · apply abs_le.mpr
    constructor <;> nlinarith [hy.1, hy.2.1, hy'.1, hy'.2.1]
  · constructor
    · apply abs_le.mpr
      constructor <;> nlinarith [hy.2.2.1, hy.2.2.2.1, hy'.2.2.1, hy'.2.2.2.1]
    · apply abs_le.mpr
      constructor <;> nlinarith [hy.2.2.2.2.1, hy.2.2.2.2.2,
        hy'.2.2.2.2.1, hy'.2.2.2.2.2]

private lemma grid_axis_card_le (h l r : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hlr : l ≤ r) :
    ((Finset.Icc (⌊l / h⌋ - 1) ⌈r / h⌉).card : ℝ) ≤ (r - l + 4) / h := by
  have hfl : (⌊l / h⌋ : ℝ) ≤ (⌈r / h⌉ : ℝ) :=
    (Int.floor_le _).trans ((div_le_div_of_nonneg_right hlr hh.le).trans (Int.le_ceil _))
  have hflZ : ⌊l / h⌋ ≤ ⌈r / h⌉ := by exact_mod_cast hfl
  have hcardZ := Int.card_Icc_of_le _ _ (by omega : ⌊l / h⌋ - 1 ≤ ⌈r / h⌉ + 1)
  have hcardR : ((Finset.Icc (⌊l / h⌋ - 1) ⌈r / h⌉).card : ℝ) =
      (⌈r / h⌉ : ℝ) + 1 - ((⌊l / h⌋ : ℝ) - 1) := by exact_mod_cast hcardZ
  have hcardH := congrArg (fun a : ℝ => a * h) hcardR
  have hf := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (l / h)) hh
  have hc := mul_lt_mul_of_pos_right (Int.ceil_lt_add_one (r / h)) hh
  rw [div_mul_cancel₀ l hh.ne'] at hf
  rw [add_mul, div_mul_cancel₀ r hh.ne', one_mul] at hc
  apply (le_div_iff₀ hh).2
  nlinarith

private lemma grid_vertical_index (h b : ℝ) (hh : 0 < h) (k : ℤ)
    (hk : (k : ℝ) * h ≤ b ∧ b ≤ ((k : ℝ) + 1) * h) :
    k ∈ Finset.Icc (⌊b / h⌋ - 1) ⌊b / h⌋ := by
  have hkl : (k : ℝ) ≤ b / h := (le_div_iff₀ hh).2 hk.1
  have hku : b / h ≤ (k : ℝ) + 1 := (div_le_iff₀ hh).2 hk.2
  have hkle : k ≤ ⌊b / h⌋ := Int.le_floor.mpr hkl
  have hfloor : (⌊b / h⌋ : ℝ) ≤ (k : ℝ) + 1 := (Int.floor_le _).trans hku
  have hfloorZ : ⌊b / h⌋ ≤ k + 1 := by exact_mod_cast hfloor
  exact Finset.mem_Icc.mpr ⟨by omega, hkle⟩

private lemma grid_breakpoint_cubes_card (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (B : Finset ℝ) :
    (((gridIndices h).filter fun k =>
      ∃ b ∈ B, (k.2.2 : ℝ) * h ≤ b ∧ b ≤ ((k.2.2 : ℝ) + 1) * h).card : ℝ) ≤
      200 * (B.card : ℝ) / h ^ 2 := by
  classical
  let A := Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉
  let C := Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉
  let R := B.biUnion fun b => Finset.Icc (⌊b / h⌋ - 1) ⌊b / h⌋
  have hR : R.card ≤ 2 * B.card := by
    calc
      R.card ≤ ∑ b ∈ B, (Finset.Icc (⌊b / h⌋ - 1) ⌊b / h⌋).card := Finset.card_biUnion_le
      _ = 2 * B.card := by
        have htwo (b : ℝ) : (Finset.Icc (⌊b / h⌋ - 1) ⌊b / h⌋).card = 2 := by
          rw [Int.card_Icc]
          omega
        simp only [htwo, Finset.sum_const, smul_eq_mul]
        ring
  have hsub : ((gridIndices h).filter fun k =>
      ∃ b ∈ B, (k.2.2 : ℝ) * h ≤ b ∧ b ≤ ((k.2.2 : ℝ) + 1) * h) ⊆ A ×ˢ (C ×ˢ R) := by
    intro k hk
    obtain ⟨hgrid, b, hb, hlo, hhi⟩ := Finset.mem_filter.mp hk
    have hg := Finset.mem_product.mp hgrid
    have hg' := Finset.mem_product.mp hg.2
    apply Finset.mem_product.mpr
    refine ⟨hg.1, Finset.mem_product.mpr ⟨hg'.1, ?_⟩⟩
    exact Finset.mem_biUnion.mpr ⟨b, hb, grid_vertical_index h b hh k.2.2 ⟨hlo, hhi⟩⟩
  have hA : (A.card : ℝ) ≤ 19 / h := by
    have hd := grid_axis_card_le h 1 16 hh hh1 (by norm_num)
    norm_num only at hd
    simpa only [A] using hd
  have hC : (C.card : ℝ) ≤ 5 / h := by
    have hd := grid_axis_card_le h 1 2 hh hh1 (by norm_num)
    norm_num only at hd
    simpa only [C] using hd
  have hRreal : (R.card : ℝ) ≤ 2 * (B.card : ℝ) := by exact_mod_cast hR
  calc
    _ ≤ ((A ×ˢ (C ×ˢ R)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (A.card : ℝ) * ((C.card : ℝ) * (R.card : ℝ)) := by
      simp only [Finset.card_product, Nat.cast_mul]
    _ ≤ (19 / h) * ((5 / h) * (2 * (B.card : ℝ))) := by gcongr
    _ = 190 * (B.card : ℝ) / h ^ 2 := by field_simp; ring
    _ ≤ 200 * (B.card : ℝ) / h ^ 2 := by gcongr <;> norm_num

private lemma reciprocal_variation_bound {a b : ℝ}
    (ha : (1 / 34 : ℝ) ≤ a) (hb : (1 / 34 : ℝ) ≤ b) :
    |1 / a - 1 / b| ≤ 1156 * |a - b| := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have he : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp <;> ring
  have hab : (1 / 1156 : ℝ) ≤ a * b := by nlinarith
  rw [he, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).2
  have hm := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 1156 * |a - b|)
  nlinarith

private lemma first_box_face_variation (z : ℤ × ℤ) (Z h u u' r r' c : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 < h) (hz : |(z.2 : ℝ)| ≤ Z)
    (hc0 : 0 ≤ c) (hc16 : c ≤ 16) (hr : |r - r'| ≤ h)
    (htau : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r * (z.2 : ℝ))
    (htau' : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r' * (z.2 : ℝ))
    (hface : u * ((z.1 : ℝ) + r * (z.2 : ℝ)) = c)
    (hface' : u' * ((z.1 : ℝ) + r' * (z.2 : ℝ)) = c) :
    |u - u'| ≤ 18496 * Z * h := by
  let a := (z.1 : ℝ) + r * (z.2 : ℝ)
  let b := (z.1 : ℝ) + r' * (z.2 : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hu : u = c / a := (eq_div_iff ha.ne').mpr hface
  have hu' : u' = c / b := (eq_div_iff hb.ne').mpr hface'
  have hab : |a - b| ≤ Z * h := by
    have he : a - b = (r - r') * (z.2 : ℝ) := by dsimp [a, b]; ring
    rw [he, abs_mul]
    exact (mul_le_mul hr hz (abs_nonneg _) hh.le).trans_eq (mul_comm h Z)
  have hinv := reciprocal_variation_bound htau htau'
  have hinv' : |1 / a - 1 / b| ≤ 1156 * (Z * h) :=
    hinv.trans (mul_le_mul_of_nonneg_left hab (by norm_num))
  have he : u - u' = c * (1 / a - 1 / b) := by rw [hu, hu']; ring
  rw [he, abs_mul, abs_of_nonneg hc0]
  have hm := mul_le_mul hc16 hinv' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16)
  nlinarith

private lemma intFinset_card_le_diameter (A : Finset ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hdiam : ∀ k ∈ A, ∀ k' ∈ A, |(k : ℝ) - (k' : ℝ)| ≤ B) :
    (A.card : ℝ) ≤ 2 * B + 3 := by
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨k₀, hk₀⟩ := hA
    have hceilR : (0 : ℝ) ≤ (⌈B⌉ : ℝ) := hB.trans (Int.le_ceil B)
    have hceilZ : 0 ≤ ⌈B⌉ := by exact_mod_cast hceilR
    have hsub : A ⊆ Finset.Icc (k₀ - ⌈B⌉) (k₀ + ⌈B⌉) := by
      intro k hk
      have hd := abs_le.mp (hdiam k hk k₀ hk₀)
      have hc : B ≤ (⌈B⌉ : ℝ) := Int.le_ceil B
      have hlo : (k₀ : ℝ) - (⌈B⌉ : ℝ) ≤ (k : ℝ) := by linarith [hd.1]
      have hhi : (k : ℝ) ≤ (k₀ : ℝ) + (⌈B⌉ : ℝ) := by linarith [hd.2]
      exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    have hcardZ := Int.card_Icc_of_le _ _ (by omega : k₀ - ⌈B⌉ ≤ k₀ + ⌈B⌉ + 1)
    have hcardR : ((Finset.Icc (k₀ - ⌈B⌉) (k₀ + ⌈B⌉)).card : ℝ) =
        ((k₀ : ℝ) + (⌈B⌉ : ℝ)) + 1 - ((k₀ : ℝ) - (⌈B⌉ : ℝ)) := by
      exact_mod_cast hcardZ
    have hcard : (A.card : ℝ) ≤ ((Finset.Icc (k₀ - ⌈B⌉) (k₀ + ⌈B⌉)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    rw [hcardR] at hcard
    linarith [Int.ceil_lt_add_one B]
  · have hAz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp only [hAz, Finset.card_empty, Nat.cast_zero]
    linarith

private lemma card_product_filter_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α → β → Prop) [DecidablePred (fun p : α × β => P p.1 p.2)]
    [∀ b, DecidablePred (fun a => P a b)] :
    ((A ×ˢ B).filter (fun p => P p.1 p.2)).card =
      ∑ b ∈ B, (A.filter (fun a => P a b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  exact Finset.sum_comm

private lemma card_product_filter_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α → β → Prop) [DecidablePred (fun p : α × β => P p.1 p.2)]
    [∀ b, DecidablePred (fun a => P a b)] (C : ℝ)
    (hC : ∀ b ∈ B, ((A.filter (fun a => P a b)).card : ℝ) ≤ C) :
    (((A ×ˢ B).filter (fun p => P p.1 p.2)).card : ℝ) ≤ (B.card : ℝ) * C := by
  rw [card_product_filter_sum]
  push_cast
  calc
    _ ≤ ∑ b ∈ B, C := Finset.sum_le_sum hC
    _ = (B.card : ℝ) * C := by simp

private lemma grid_first_face_card (h Z : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hZ : 1 ≤ Z)
    (z : ℤ × ℤ) (hz : |(z.2 : ℝ)| ≤ Z) (c : ℝ) (hc0 : 0 ≤ c) (hc16 : c ≤ 16) :
    (((gridIndices h).filter fun k => ∃ y ∈ gridCube h k,
      (1 / 34 : ℝ) ≤ (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ∧
        y.1 * ((z.1 : ℝ) + y.2.2 * (z.2 : ℝ)) = c).card : ℝ) ≤
      1000000 * (Z + 1) / h ^ 2 := by
  classical
  let A := Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉
  let V := Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉
  let R := Finset.Icc (-1) ⌈1 / h⌉
  let P : ℤ → ℤ × ℤ → Prop := fun a q => ∃ y ∈ gridCube h (a, q),
    (1 / 34 : ℝ) ≤ (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ∧
      y.1 * ((z.1 : ℝ) + y.2.2 * (z.2 : ℝ)) = c
  have hfiber (q : ℤ × ℤ) : ((A.filter (fun a => P a q)).card : ℝ) ≤ 36992 * Z + 5 := by
    have hdiam : ∀ k ∈ A.filter (fun a => P a q),
        ∀ k' ∈ A.filter (fun a => P a q),
          |(k : ℝ) - (k' : ℝ)| ≤ 18496 * Z + 1 := by
      intro k hk k' hk'
      obtain ⟨_, y, hy, htau, hface⟩ := Finset.mem_filter.mp hk
      obtain ⟨_, y', hy', htau', hface'⟩ := Finset.mem_filter.mp hk'
      have hrdiff : |y.2.2 - y'.2.2| ≤ h := by
        apply abs_le.mpr
        constructor <;> nlinarith [hy.2.2.2.2.1, hy.2.2.2.2.2,
          hy'.2.2.2.2.1, hy'.2.2.2.2.2]
      have hudiff := first_box_face_variation z Z h y.1 y'.1 y.2.2 y'.2.2 c
        hZ hh hz hc0 hc16 hrdiff htau htau' hface hface'
      have hdiff := abs_le.mp hudiff
      apply (mul_le_mul_iff_left₀ hh).mp
      have he : |(k : ℝ) - (k' : ℝ)| * h = |((k : ℝ) - (k' : ℝ)) * h| := by
        rw [abs_mul, abs_of_pos hh]
      rw [he, sub_mul]
      apply abs_le.mpr
      constructor <;> nlinarith [hy.1, hy.2.1, hy'.1, hy'.2.1, hdiff.1, hdiff.2]
    have hc := intFinset_card_le_diameter (A.filter (fun a => P a q))
      (18496 * Z + 1) (by linarith) hdiam
    linarith
  have hVR : ((V ×ˢ R).card : ℝ) ≤ 25 / h ^ 2 := by
    have hV : (V.card : ℝ) ≤ 5 / h := by
      have hd := grid_axis_card_le h 1 2 hh hh1 (by norm_num)
      norm_num only at hd
      simpa only [V] using hd
    have hR : (R.card : ℝ) ≤ 5 / h := by
      have hd := grid_axis_card_le h 0 1 hh hh1 (by norm_num)
      norm_num only at hd
      simpa [R] using hd
    calc
      _ = (V.card : ℝ) * (R.card : ℝ) := by simp only [Finset.card_product, Nat.cast_mul]
      _ ≤ (5 / h) * (5 / h) := by gcongr
      _ = _ := by field_simp; ring
  have hcard := card_product_filter_le A (V ×ˢ R) P (36992 * Z + 5)
    (fun q hq => hfiber q)
  change (((A ×ˢ (V ×ˢ R)).filter (fun k => P k.1 k.2)).card : ℝ) ≤ _
  calc
    _ ≤ ((V ×ˢ R).card : ℝ) * (36992 * Z + 5) := hcard
    _ ≤ (25 / h ^ 2) * (36992 * Z + 5) := by gcongr
    _ ≤ 1000000 * (Z + 1) / h ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hh)).2
      have hcancel : ((25 / h ^ 2) * (36992 * Z + 5)) * h ^ 2 =
          25 * (36992 * Z + 5) := by field_simp [hh.ne'] <;> ring
      rw [hcancel]
      nlinarith

private lemma reciprocal_variation_bound68 {a b : ℝ}
    (ha : (1 / 68 : ℝ) ≤ a) (hb : (1 / 68 : ℝ) ≤ b) :
    |1 / a - 1 / b| ≤ 4624 * |a - b| := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have he : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp <;> ring
  have hab : (1 / 4624 : ℝ) ≤ a * b := by nlinarith
  rw [he, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).2
  have hm := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 4624 * |a - b|)
  nlinarith

private lemma second_box_face_variation (z : ℤ × ℤ) (Z h E u u' v v' r r' c : ℝ)
    (hZ : 1 ≤ Z) (hh : 0 < h) (hz : |(z.2 : ℝ)| ≤ Z)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (hu : (1 / 2 : ℝ) ≤ u) (hu17 : u ≤ 17) (hu' : (1 / 2 : ℝ) ≤ u')
    (hudiff : |u - u'| ≤ h) (hr : |r - r'| ≤ h)
    (htau : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r * (z.2 : ℝ))
    (htau' : (1 / 34 : ℝ) ≤ (z.1 : ℝ) + r' * (z.2 : ℝ))
    (htau34' : (z.1 : ℝ) + r' * (z.2 : ℝ) ≤ 34)
    (hface : v * ((z.1 : ℝ) + r * (z.2 : ℝ)) + (z.2 : ℝ) * E / u = c)
    (hface' : v' * ((z.1 : ℝ) + r' * (z.2 : ℝ)) + (z.2 : ℝ) * E / u' = c) :
    |v - v'| ≤ 1000000 * (Z + 1) ^ 2 * h := by
  let a := (z.1 : ℝ) + r * (z.2 : ℝ)
  let b := (z.1 : ℝ) + r' * (z.2 : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hu0 : 0 < u := by linarith
  have hu0' : 0 < u' := by linarith
  have hprod : (1 / 68 : ℝ) ≤ u * a := by nlinarith
  have hprod' : (1 / 68 : ℝ) ≤ u' * b := by nlinarith
  have hab : |a - b| ≤ Z * h := by
    have he : a - b = (r - r') * (z.2 : ℝ) := by dsimp [a, b]; ring
    rw [he, abs_mul]
    exact (mul_le_mul hr hz (abs_nonneg _) hh.le).trans_eq (mul_comm h Z)
  have hdenvar : |u * a - u' * b| ≤ (17 * Z + 34) * h := by
    have he : u * a - u' * b = u * (a - b) + (u - u') * b := by ring
    rw [he]
    calc
      _ ≤ |u * (a - b)| + |(u - u') * b| := abs_add_le _ _
      _ = u * |a - b| + |u - u'| * b := by
        rw [abs_mul, abs_mul, abs_of_pos hu0, abs_of_pos hb]
      _ ≤ 17 * (Z * h) + h * 34 := by
        exact add_le_add (mul_le_mul hu17 hab (abs_nonneg _) (by norm_num))
          (mul_le_mul hudiff htau34' hb.le hh.le)
      _ = _ := by ring
  have hinv1 : |1 / a - 1 / b| ≤ 1156 * (Z * h) :=
    (reciprocal_variation_bound htau htau').trans
      (mul_le_mul_of_nonneg_left hab (by norm_num))
  have hinv2 : |1 / (u * a) - 1 / (u' * b)| ≤ 4624 * ((17 * Z + 34) * h) :=
    (reciprocal_variation_bound68 hprod hprod').trans
      (mul_le_mul_of_nonneg_left hdenvar (by norm_num))
  have hv : v = c / a - (z.2 : ℝ) * E / (u * a) := by
    calc
      v = (c - (z.2 : ℝ) * E / u) / a := (eq_div_iff ha.ne').mpr (by linarith [hface])
      _ = _ := by field_simp [hu0.ne', ha.ne'] <;> ring
  have hv' : v' = c / b - (z.2 : ℝ) * E / (u' * b) := by
    calc
      v' = (c - (z.2 : ℝ) * E / u') / b := (eq_div_iff hb.ne').mpr (by linarith [hface'])
      _ = _ := by field_simp [hu0'.ne', hb.ne'] <;> ring
  have he : v - v' = c * (1 / a - 1 / b) -
      ((z.2 : ℝ) * E) * (1 / (u * a) - 1 / (u' * b)) := by rw [hv, hv']; ring
  have hEabs : |(z.2 : ℝ) * E| ≤ Z := by
    rw [abs_mul, abs_of_nonneg hE0]
    have hh' := mul_le_mul hz hE1 hE0 (by linarith : 0 ≤ Z)
    simpa using hh'
  rw [he]
  calc
    _ ≤ |c * (1 / a - 1 / b)| + |((z.2 : ℝ) * E) * (1 / (u * a) - 1 / (u' * b))| := by
      simpa using abs_sub_le (c * (1 / a - 1 / b)) 0
        (((z.2 : ℝ) * E) * (1 / (u * a) - 1 / (u' * b)))
    _ = c * |1 / a - 1 / b| + |(z.2 : ℝ) * E| * |1 / (u * a) - 1 / (u' * b)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc0]
    _ ≤ 2 * (1156 * (Z * h)) + Z * (4624 * ((17 * Z + 34) * h)) :=
      add_le_add (mul_le_mul hc2 hinv1 (abs_nonneg _) (by norm_num))
        (mul_le_mul hEabs hinv2 (abs_nonneg _) (by linarith))
    _ ≤ 1000000 * (Z + 1) ^ 2 * h := by
      have hbnd : 2 * (1156 * Z) + Z * (4624 * (17 * Z + 34)) ≤
          1000000 * (Z + 1) ^ 2 := by nlinarith [sq_nonneg Z]
      nlinarith [mul_le_mul_of_nonneg_right hbnd hh.le]

private lemma grid_second_face_card (h Z E : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hZ : 1 ≤ Z)
    (z : ℤ × ℤ) (hz : |(z.2 : ℝ)| ≤ Z) (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (c : ℝ) (hc0 : 0 ≤ c) (hc2 : c ≤ 2) :
    (((gridIndices h).filter fun k => ∃ y ∈ gridCube h k,
      ((1 / 2 : ℝ) ≤ y.1 ∧ y.1 ≤ 17) ∧
      ((1 / 34 : ℝ) ≤ (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ∧
        (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ≤ 34) ∧
      y.2.1 * ((z.1 : ℝ) + y.2.2 * (z.2 : ℝ)) + (z.2 : ℝ) * E / y.1 = c).card : ℝ) ≤
      200000000 * (Z + 1) ^ 2 / h ^ 2 := by
  classical
  let A := Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉
  let V := Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉
  let R := Finset.Icc (-1) ⌈1 / h⌉
  let P : ℤ → ℤ × ℤ → Prop := fun v q => ∃ y ∈ gridCube h (q.1, v, q.2),
    ((1 / 2 : ℝ) ≤ y.1 ∧ y.1 ≤ 17) ∧
      ((1 / 34 : ℝ) ≤ (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ∧
        (z.1 : ℝ) + y.2.2 * (z.2 : ℝ) ≤ 34) ∧
      y.2.1 * ((z.1 : ℝ) + y.2.2 * (z.2 : ℝ)) + (z.2 : ℝ) * E / y.1 = c
  have hfiber (q : ℤ × ℤ) : ((V.filter (fun v => P v q)).card : ℝ) ≤
      2000000 * (Z + 1) ^ 2 + 5 := by
    have hdiam : ∀ k ∈ V.filter (fun v => P v q), ∀ k' ∈ V.filter (fun v => P v q),
        |(k : ℝ) - (k' : ℝ)| ≤ 1000000 * (Z + 1) ^ 2 + 1 := by
      intro k hk k' hk'
      obtain ⟨_, y, hy, hu, htau, hface⟩ := Finset.mem_filter.mp hk
      obtain ⟨_, y', hy', hu', htau', hface'⟩ := Finset.mem_filter.mp hk'
      have hudiff : |y.1 - y'.1| ≤ h := by
        apply abs_le.mpr
        constructor <;> nlinarith [hy.1, hy.2.1, hy'.1, hy'.2.1]
      have hrdiff : |y.2.2 - y'.2.2| ≤ h := by
        apply abs_le.mpr
        constructor <;> nlinarith [hy.2.2.2.2.1, hy.2.2.2.2.2,
          hy'.2.2.2.2.1, hy'.2.2.2.2.2]
      have hvdiff := second_box_face_variation z Z h E y.1 y'.1 y.2.1 y'.2.1 y.2.2 y'.2.2 c
        hZ hh hz hE0 hE1 hc0 hc2 hu.1 hu.2 hu'.1 hudiff hrdiff
        htau.1 htau'.1 htau'.2 hface hface'
      have hdiff := abs_le.mp hvdiff
      apply (mul_le_mul_iff_left₀ hh).mp
      have he : |(k : ℝ) - (k' : ℝ)| * h = |((k : ℝ) - (k' : ℝ)) * h| := by
        rw [abs_mul, abs_of_pos hh]
      rw [he, sub_mul]
      apply abs_le.mpr
      constructor <;> nlinarith [hy.2.2.1, hy.2.2.2.1, hy'.2.2.1, hy'.2.2.2.1,
        hdiff.1, hdiff.2]
    have hc := intFinset_card_le_diameter (V.filter (fun v => P v q))
      (1000000 * (Z + 1) ^ 2 + 1) (by positivity) hdiam
    linarith
  have hAR : ((A ×ˢ R).card : ℝ) ≤ 95 / h ^ 2 := by
    have hA : (A.card : ℝ) ≤ 19 / h := by
      have hd := grid_axis_card_le h 1 16 hh hh1 (by norm_num)
      norm_num only at hd
      simpa only [A] using hd
    have hR : (R.card : ℝ) ≤ 5 / h := by
      have hd := grid_axis_card_le h 0 1 hh hh1 (by norm_num)
      norm_num only at hd
      simpa [R] using hd
    calc
      _ = (A.card : ℝ) * (R.card : ℝ) := by simp only [Finset.card_product, Nat.cast_mul]
      _ ≤ (19 / h) * (5 / h) := by gcongr
      _ = _ := by field_simp <;> ring
  have he : ((A ×ˢ (V ×ˢ R)).filter (fun k => P k.2.1 (k.1, k.2.2))).card =
      ((V ×ˢ (A ×ˢ R)).filter (fun k => P k.1 k.2)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_comm
  have hcard := card_product_filter_le V (A ×ˢ R) P (2000000 * (Z + 1) ^ 2 + 5)
    (fun q hq => hfiber q)
  change (((A ×ˢ (V ×ˢ R)).filter (fun k => P k.2.1 (k.1, k.2.2))).card : ℝ) ≤ _
  rw [he]
  calc
    _ ≤ ((A ×ˢ R).card : ℝ) * (2000000 * (Z + 1) ^ 2 + 5) := hcard
    _ ≤ (95 / h ^ 2) * (2000000 * (Z + 1) ^ 2 + 5) := by gcongr
    _ ≤ 200000000 * (Z + 1) ^ 2 / h ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hh)).2
      have hcancel : ((95 / h ^ 2) * (2000000 * (Z + 1) ^ 2 + 5)) * h ^ 2 =
          95 * (2000000 * (Z + 1) ^ 2 + 5) := by field_simp [hh.ne'] <;> ring
      rw [hcancel]
      nlinarith [sq_nonneg Z]

private lemma gridCube_preconnected (h : ℝ) (k : ℤ × ℤ × ℤ) : IsPreconnected (gridCube h k) := by
  have he : gridCube h k =
      Set.Icc ((k.1 : ℝ) * h) (((k.1 : ℝ) + 1) * h) ×ˢ
        (Set.Icc ((k.2.1 : ℝ) * h) (((k.2.1 : ℝ) + 1) * h) ×ˢ
          Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h)) := by
    ext y
    simp only [gridCube, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, and_assoc]
  rw [he]
  exact isPreconnected_Icc.prod (isPreconnected_Icc.prod isPreconnected_Icc)

private lemma arch_boundary_card_of_breakpoints {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (hUV : 1 ≤ S.U * S.V)
    (s : EnvPoint S.x K) (Z h : ℝ) (hZ : 1 ≤ Z) (hh : 0 < h) (hhsmall : h ≤ 1 / 8)
    (hz : |(s.1.2 : ℝ)| ≤ Z) (hZh : Z * h ≤ 1 / 68) (B : Finset ℝ)
    (hB : ∀ r r' : ℝ, -1 ≤ r → r ≤ r' → r' ≤ 2 →
      (∀ v ∈ Set.Icc r r', (1 / 34 : ℝ) ≤ (v * (s.1.2 : ℝ) + s.1.1) ∧
        (v * (s.1.2 : ℝ) + s.1.1) ≤ 34 ∧ v ∉ B) →
      (envGood F S ⟨1, 1, r⟩ s ↔ envGood F S ⟨1, 1, r'⟩ s)) :
    (((gridIndices h).filter fun k => IsNonconstantOn
      (fun y => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s.1 ∧
        envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s) (gridCube h k)).card : ℝ) ≤
      (500000000 * (Z + 1) ^ 2 + 200 * (B.card : ℝ)) / h ^ 2 := by
  classical
  let tau : ℝ × ℝ × ℝ → ℝ := fun y => (s.1.1 : ℝ) + y.2.2 * (s.1.2 : ℝ)
  let E := 1 / (S.U * S.V)
  let f : ℝ × ℝ × ℝ → ℝ := fun y => y.1 * tau y
  let g : ℝ × ℝ × ℝ → ℝ := fun y => y.2.1 * tau y + (s.1.2 : ℝ) * E / y.1
  let A : ℝ → Finset (ℤ × ℤ × ℤ) := fun c => (gridIndices h).filter fun k =>
    ∃ y ∈ gridCube h k, (1 / 34 : ℝ) ≤ tau y ∧ f y = c
  let C : ℝ → Finset (ℤ × ℤ × ℤ) := fun c => (gridIndices h).filter fun k =>
    ∃ y ∈ gridCube h k, ((1 / 2 : ℝ) ≤ y.1 ∧ y.1 ≤ 17) ∧
      ((1 / 34 : ℝ) ≤ tau y ∧ tau y ≤ 34) ∧ g y = c
  let G := (gridIndices h).filter fun k =>
    ∃ b ∈ B, (k.2.2 : ℝ) * h ≤ b ∧ b ≤ ((k.2.2 : ℝ) + 1) * h
  let T := (gridIndices h).filter fun k => IsNonconstantOn
    (fun y => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s.1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s) (gridCube h k)
  have hfrac (u : ℝ) (hu : 0 < u) : (s.1.2 : ℝ) / (S.U * S.V * u) =
      (s.1.2 : ℝ) * E / u := by
    dsimp [E]
    field_simp [hU.ne', hV.ne', hu.ne'] <;> ring
  have hnorm (y : ℝ × ℝ × ℝ) (hy : (1 / 2 : ℝ) ≤ y.1) :
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s.1 ↔
        1 ≤ f y ∧ f y ≤ 16 ∧ 1 ≤ g y ∧ g y ≤ 2 := by
    have hu : 0 < y.1 := by linarith
    rw [envBox_normalized S hU hV y.1 y.2.1 y.2.2 hu s.1, hfrac y.1 hu]
  have hsub : T ⊆ A 1 ∪ A 16 ∪ C 1 ∪ C 2 ∪ G := by
    intro k hk
    obtain ⟨hkgrid, y₀, hy₀, y₁, hy₁, hygood, hybad⟩ := Finset.mem_filter.mp hk
    have hd₀ := grid_cube_domain_bounds h hh hhsmall k hkgrid y₀ hy₀
    have hd₁ := grid_cube_domain_bounds h hh hhsmall k hkgrid y₁ hy₁
    have hb₀ := (hnorm y₀ hd₀.1).1 hygood.1
    have htau₀pos : 0 < tau y₀ := by
      by_contra hn
      have hh' := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ y₀.1) (le_of_not_gt hn)
      dsimp [f] at hb₀
      linarith [hb₀.1]
    have htau₀lo : (1 / 17 : ℝ) ≤ tau y₀ := by
      have hm := mul_le_mul_of_nonneg_right hd₀.2.1 htau₀pos.le
      dsimp [f] at hb₀
      nlinarith [hb₀.1]
    have htau₀hi : tau y₀ ≤ 32 := by
      have hm := mul_le_mul_of_nonneg_right hd₀.1 htau₀pos.le
      dsimp [f] at hb₀
      nlinarith [hb₀.2.1]
    have hsafe (y : ℝ × ℝ × ℝ) (hy : y ∈ gridCube h k) :
        (1 / 34 : ℝ) ≤ tau y ∧ tau y ≤ 34 := by
      have hr := (grid_cube_coordinate_diff h k y y₀ hy hy₀).2.2
      have he : tau y - tau y₀ = (y.2.2 - y₀.2.2) * (s.1.2 : ℝ) := by dsimp [tau]; ring
      have hdiff : |tau y - tau y₀| ≤ Z * h := by
        rw [he, abs_mul]
        exact (mul_le_mul hr hz (abs_nonneg _) hh.le).trans_eq (mul_comm h Z)
      have hd := abs_le.mp hdiff
      constructor <;> nlinarith [hd.1, hd.2]
    by_cases hG : ∃ b ∈ B, (k.2.2 : ℝ) * h ≤ b ∧ b ≤ ((k.2.2 : ℝ) + 1) * h
    · have hkG : k ∈ G := Finset.mem_filter.mpr ⟨hkgrid, hG⟩
      simp only [Finset.mem_union]
      exact Or.inr hkG
    · have hgoodsafe (r r' : ℝ) (hr : r ∈ Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h))
          (hr' : r' ∈ Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h))
          (hrr : r ≤ r') :
          envGood F S ⟨1, 1, r⟩ s ↔ envGood F S ⟨1, 1, r'⟩ s := by
        have hy (v : ℝ) (hv : v ∈ Set.Icc r r') : (y₀.1, y₀.2.1, v) ∈ gridCube h k :=
          ⟨hy₀.1, hy₀.2.1, hy₀.2.2.1, hy₀.2.2.2.1,
            hr.1.trans hv.1, hv.2.trans hr'.2⟩
        have hrD := grid_cube_domain_bounds h hh hhsmall k hkgrid
          (y₀.1, y₀.2.1, r) ⟨hy₀.1, hy₀.2.1, hy₀.2.2.1, hy₀.2.2.2.1, hr.1, hr.2⟩
        have hrD' := grid_cube_domain_bounds h hh hhsmall k hkgrid
          (y₀.1, y₀.2.1, r') ⟨hy₀.1, hy₀.2.1, hy₀.2.2.1, hy₀.2.2.2.1, hr'.1, hr'.2⟩
        apply hB r r' hrD.2.2.2.2.1 hrr hrD'.2.2.2.2.2
        intro v hv
        have hst := hsafe (y₀.1, y₀.2.1, v) (hy v hv)
        refine ⟨by simpa [tau, add_comm] using hst.1,
          by simpa [tau, add_comm] using hst.2, ?_⟩
        intro hvB
        exact hG ⟨v, hvB, hr.1.trans hv.1, hv.2.trans hr'.2⟩
      have hg₁ : envGood F S ⟨S.U * y₁.1, S.V * y₁.2.1, y₁.2.2⟩ s := by
        have hg₀ := (envGood_normalized F S y₀.1 y₀.2.1 y₀.2.2 s).1 hygood.2
        have hr₀ : y₀.2.2 ∈ Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h) :=
          ⟨hy₀.2.2.2.2.1, hy₀.2.2.2.2.2⟩
        have hr₁ : y₁.2.2 ∈ Set.Icc ((k.2.2 : ℝ) * h) (((k.2.2 : ℝ) + 1) * h) :=
          ⟨hy₁.2.2.2.2.1, hy₁.2.2.2.2.2⟩
        apply (envGood_normalized F S y₁.1 y₁.2.1 y₁.2.2 s).2
        rcases le_total y₀.2.2 y₁.2.2 with hrr | hrr
        · exact (hgoodsafe _ _ hr₀ hr₁ hrr).1 hg₀
        · exact (hgoodsafe _ _ hr₁ hr₀ hrr).2 hg₀
      have hb₁ : ¬ (1 ≤ f y₁ ∧ f y₁ ≤ 16 ∧ 1 ≤ g y₁ ∧ g y₁ ≤ 2) := by
        intro hb
        exact hybad ⟨(hnorm y₁ hd₁.1).2 hb, hg₁⟩
      have hcontf : ContinuousOn f (gridCube h k) := by
        exact (continuous_fst.mul
          (continuous_const.add ((continuous_snd.comp continuous_snd).mul continuous_const))).continuousOn
      have hcontg : ContinuousOn g (gridCube h k) := by
        apply (((continuous_fst.comp continuous_snd).mul
          (continuous_const.add ((continuous_snd.comp continuous_snd).mul continuous_const))).continuousOn).add
        apply continuous_const.continuousOn.div continuous_fst.continuousOn
        intro y hy
        have hd := grid_cube_domain_bounds h hh hhsmall k hkgrid y hy
        linarith [hd.1]
      have hconn := gridCube_preconnected h k
      have hcases : f y₁ < 1 ∨ 16 < f y₁ ∨ g y₁ < 1 ∨ 2 < g y₁ := by
        by_cases h1 : 1 ≤ f y₁
        · by_cases h2 : f y₁ ≤ 16
          · by_cases h3 : 1 ≤ g y₁
            · have h4 : ¬ g y₁ ≤ 2 := fun h => hb₁ ⟨h1, h2, h3, h⟩
              exact Or.inr (Or.inr (Or.inr (lt_of_not_ge h4)))
            · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge h3)))
          · exact Or.inr (Or.inl (lt_of_not_ge h2))
        · exact Or.inl (lt_of_not_ge h1)
      rcases hcases with hb₁ | hb₁ | hb₁ | hb₁
      · obtain ⟨y, hy, he⟩ := hconn.intermediate_value hy₁ hy₀ hcontf ⟨hb₁.le, hb₀.1⟩
        have hm : k ∈ A 1 := Finset.mem_filter.mpr ⟨hkgrid, y, hy, (hsafe y hy).1, he⟩
        simp only [Finset.mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inl hm)))
      · obtain ⟨y, hy, he⟩ := hconn.intermediate_value hy₀ hy₁ hcontf ⟨hb₀.2.1, hb₁.le⟩
        have hm : k ∈ A 16 := Finset.mem_filter.mpr ⟨hkgrid, y, hy, (hsafe y hy).1, he⟩
        simp only [Finset.mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inr hm)))
      · obtain ⟨y, hy, he⟩ := hconn.intermediate_value hy₁ hy₀ hcontg ⟨hb₁.le, hb₀.2.2.1⟩
        have hd := grid_cube_domain_bounds h hh hhsmall k hkgrid y hy
        have hm : k ∈ C 1 := Finset.mem_filter.mpr
          ⟨hkgrid, y, hy, ⟨hd.1, hd.2.1⟩, hsafe y hy, he⟩
        simp only [Finset.mem_union]
        exact Or.inl (Or.inl (Or.inr hm))
      · obtain ⟨y, hy, he⟩ := hconn.intermediate_value hy₀ hy₁ hcontg ⟨hb₀.2.2.2, hb₁.le⟩
        have hd := grid_cube_domain_bounds h hh hhsmall k hkgrid y hy
        have hm : k ∈ C 2 := Finset.mem_filter.mpr
          ⟨hkgrid, y, hy, ⟨hd.1, hd.2.1⟩, hsafe y hy, he⟩
        simp only [Finset.mem_union]
        exact Or.inl (Or.inr hm)
  have hcard : T.card ≤ (A 1).card + (A 16).card + (C 1).card + (C 2).card + G.card := by
    have h0 := Finset.card_le_card hsub
    have h1 := Finset.card_union_le (A 1) (A 16)
    have h2 := Finset.card_union_le (A 1 ∪ A 16) (C 1)
    have h3 := Finset.card_union_le (A 1 ∪ A 16 ∪ C 1) (C 2)
    have h4 := Finset.card_union_le (A 1 ∪ A 16 ∪ C 1 ∪ C 2) G
    omega
  have hcardR : (T.card : ℝ) ≤ ((A 1).card : ℝ) + ((A 16).card : ℝ) +
      ((C 1).card : ℝ) + ((C 2).card : ℝ) + (G.card : ℝ) := by exact_mod_cast hcard
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp [E]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hUV
  have hh1 : h ≤ 1 := by linarith
  have hA1 := grid_first_face_card h Z hh hh1 hZ s.1 hz 1 (by norm_num) (by norm_num)
  have hA16 := grid_first_face_card h Z hh hh1 hZ s.1 hz 16 (by norm_num) (by norm_num)
  have hC1 := grid_second_face_card h Z E hh hh1 hZ s.1 hz hE0 hE1 1 (by norm_num) (by norm_num)
  have hC2 := grid_second_face_card h Z E hh hh1 hZ s.1 hz hE0 hE1 2 (by norm_num) (by norm_num)
  have hG := grid_breakpoint_cubes_card h hh hh1 B
  change (T.card : ℝ) ≤ _
  change ((A 1).card : ℝ) ≤ _ at hA1
  change ((A 16).card : ℝ) ≤ _ at hA16
  change ((C 1).card : ℝ) ≤ _ at hC1
  change ((C 2).card : ℝ) ≤ _ at hC2
  change (G.card : ℝ) ≤ _ at hG
  have hh2 := sq_pos_of_pos hh
  have ht := mul_le_mul_of_nonneg_right hcardR hh2.le
  have ha1 := (le_div_iff₀ hh2).1 hA1
  have ha16 := (le_div_iff₀ hh2).1 hA16
  have hc1 := (le_div_iff₀ hh2).1 hC1
  have hc2 := (le_div_iff₀ hh2).1 hC2
  have hg := (le_div_iff₀ hh2).1 hG
  apply (le_div_iff₀ hh2).2
  nlinarith [sq_nonneg Z]

/-- Truncated inclusion–exclusion `Σ_{T' ⊆ T, |T'| ≤ m} (-1)^{|T'|} ∏_{i∈T'} X_i`. -/
def bonferroniTrunc {ι : Type*} (T : Finset ι) (X : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ T' ∈ T.powerset.filter (fun T' => T'.card ≤ m), (-1 : ℝ) ^ T'.card * ∏ i ∈ T', X i

private lemma bonferroniTrunc_insert {ι : Type*} [DecidableEq ι] (T : Finset ι) (i : ι)
    (hi : i ∉ T) (X : ι → ℝ) (m : ℕ) :
    bonferroniTrunc (insert i T) X (m + 1) =
      bonferroniTrunc T X (m + 1) - X i * bonferroniTrunc T X m := by
  classical
  unfold bonferroniTrunc
  rw [Finset.powerset_insert, Finset.filter_union]
  have hdis : Disjoint
      (T.powerset.filter (fun t => t.card ≤ m + 1))
      ((T.powerset.image (insert i)).filter (fun t => t.card ≤ m + 1)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    have hit : i ∈ t := by
      rcases Finset.mem_image.mp (Finset.mem_filter.mp ht').1 with ⟨u, hu, rfl⟩
      simp
    exact hi ((Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1) hit)
  rw [Finset.sum_union hdis]
  have hfilter :
      (T.powerset.image (insert i)).filter (fun t => t.card ≤ m + 1) =
        (T.powerset.filter (fun t => t.card ≤ m)).image (insert i) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hcard⟩
      have hui : i ∉ u := Finset.notMem_of_mem_powerset_of_notMem hu hi
      refine ⟨u, ⟨hu, ?_⟩, rfl⟩
      rw [Finset.card_insert_of_notMem hui] at hcard
      omega
    · rintro ⟨u, ⟨hu, hcard⟩, rfl⟩
      have hui : i ∉ u := Finset.notMem_of_mem_powerset_of_notMem hu hi
      refine ⟨⟨u, hu, rfl⟩, ?_⟩
      rw [Finset.card_insert_of_notMem hui]
      omega
  have hinj : Set.InjOn (insert i)
      (↑(T.powerset.filter (fun s => s.card ≤ m)) : Set (Finset ι)) := by
    intro s hs t ht hst
    ext j
    have hmem := congrArg (fun q : Finset ι => j ∈ q) hst
    by_cases hji : j = i
    · subst j
      have hs' : s ∈ T.powerset.filter (fun s => s.card ≤ m) := by simpa using hs
      have ht' : t ∈ T.powerset.filter (fun s => s.card ≤ m) := by simpa using ht
      have his : i ∉ s :=
        Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp hs').1 hi
      have hit : i ∉ t :=
        Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp ht').1 hi
      simp [his, hit]
    · simpa [hji] using hmem
  rw [hfilter, Finset.sum_image hinj]
  have hterm (s : Finset ι) (hs : s ∈ T.powerset.filter (fun s => s.card ≤ m)) :
      (-1 : ℝ) ^ (insert i s).card * ∏ j ∈ insert i s, X j =
        -X i * ((-1 : ℝ) ^ s.card * ∏ j ∈ s, X j) := by
    have his : i ∉ s :=
      Finset.notMem_of_mem_powerset_of_notMem (Finset.mem_filter.mp hs).1 hi
    rw [Finset.card_insert_of_notMem his, Finset.prod_insert his, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

private lemma bonferroniTrunc_zero {ι : Type*} [DecidableEq ι] (T : Finset ι) (X : ι → ℝ) :
    bonferroniTrunc T X 0 = 1 := by
  classical
  unfold bonferroniTrunc
  have hfilter : T.powerset.filter (fun s => s.card ≤ 0) = {∅} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hcard⟩
      have hc : s.card = 0 := by omega
      exact Finset.card_eq_zero.mp hc
    · rintro rfl
      simp
  rw [hfilter]
  simp

private lemma bonferroniTrunc_bounds {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (X : ι → ℝ) (hX : ∀ i ∈ T, 0 ≤ X i ∧ X i ≤ 1) (m : ℕ) :
    (Even m → ∏ i ∈ T, (1 - X i) ≤ bonferroniTrunc T X m) ∧
      (Odd m → bonferroniTrunc T X m ≤ ∏ i ∈ T, (1 - X i)) := by
  classical
  induction T using Finset.induction_on generalizing X m with
  | empty =>
      have hB : bonferroniTrunc (∅ : Finset ι) X m = 1 := by
        simp [bonferroniTrunc, Finset.filter_singleton]
      simp [hB]
  | @insert i T hi ih =>
      have hXi := hX i (by simp)
      have hXT : ∀ j ∈ T, 0 ≤ X j ∧ X j ≤ 1 := by
        intro j hj
        exact hX j (by simp [hj])
      constructor
      · intro hm
        cases m with
        | zero =>
            have hprod : ∏ j ∈ insert i T, (1 - X j) ≤ 1 := by
              apply Finset.prod_le_one₀
              · intro j hj
                have hjX := hX j hj
                linarith
              · intro j hj
                have hjX := hX j hj
                linarith
            have hzero := bonferroniTrunc_zero (insert i T) X
            simpa [hzero] using hprod
        | succ n =>
            have hn : Odd n := by
              rcases hm with ⟨k, hk⟩
              cases k with
              | zero => simp at hk
              | succ k => refine ⟨k, ?_⟩; omega
            have hprev := (ih X hXT n).2 hn
            have hnext := (ih X hXT (n + 1)).1 hm
            rw [bonferroniTrunc_insert T i hi X n, Finset.prod_insert hi]
            nlinarith [mul_nonneg hXi.1 (show 0 ≤ ∏ j ∈ T, (1 - X j) - bonferroniTrunc T X n by linarith)]
      · intro hm
        cases m with
        | zero =>
            have hfalse : ¬ Odd 0 := by simp
            exact (hfalse hm).elim
        | succ n =>
            have hn : Even n := by
              rcases hm with ⟨k, hk⟩
              refine ⟨k, ?_⟩
              omega
            have hprev := (ih X hXT n).1 hn
            have hnext := (ih X hXT (n + 1)).2 hm
            rw [bonferroniTrunc_insert T i hi X n, Finset.prod_insert hi]
            nlinarith [mul_nonneg hXi.1 (show 0 ≤ bonferroniTrunc T X n - ∏ j ∈ T, (1 - X j) by linarith)]

private lemma bonferroniTrunc_gap {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (X : ι → ℝ) (m : ℕ) (hm : Even m) :
    bonferroniTrunc T X m - bonferroniTrunc T X (m + 1) =
      ∑ U ∈ T.powerset.filter (fun U => U.card = m + 1), ∏ i ∈ U, X i := by
  classical
  have hfilter :
      T.powerset.filter (fun U => U.card ≤ m + 1) =
        T.powerset.filter (fun U => U.card ≤ m) ∪
          T.powerset.filter (fun U => U.card = m + 1) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hU, hcard⟩
      by_cases hle : U.card ≤ m
      · exact Or.inl ⟨hU, hle⟩
      · right
        exact ⟨hU, by omega⟩
    · rintro (⟨hU, hle⟩ | ⟨hU, heq⟩)
      · exact ⟨hU, by omega⟩
      · exact ⟨hU, by omega⟩
  have hdis : Disjoint
      (T.powerset.filter (fun U => U.card ≤ m))
      (T.powerset.filter (fun U => U.card = m + 1)) := by
    apply Finset.disjoint_left.mpr
    intro U hU hU'
    have hle := (Finset.mem_filter.mp hU).2
    have heq := (Finset.mem_filter.mp hU').2
    omega
  have hmOdd : Odd (m + 1) := by
    rcases hm with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  unfold bonferroniTrunc
  rw [hfilter, Finset.sum_union hdis]
  have hterm (U : Finset ι) (hU : U ∈ T.powerset.filter (fun U => U.card = m + 1)) :
      (-1 : ℝ) ^ U.card * ∏ i ∈ U, X i = - ∏ i ∈ U, X i := by
    rw [(Finset.mem_filter.mp hU).2]
    rw [hmOdd.neg_one_pow]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
  ring

private lemma lineAverage_prod {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (T : Finset {p : ℕ // p ∈ markedPrimes x K a})
    (X : (p : {p : ℕ // p ∈ markedPrimes x K a}) → Fin (p.1 + 1) → ℝ) :
    lineAverage (fun ℓ : LineData x K a =>
        ((∏ p ∈ T, X p (ℓ p) : ℝ) : ℂ)) =
      ((∏ p ∈ T, ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam : ℝ) : ℂ) := by
  classical
  let D : ℝ := ∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1)
  let g : (p : {p : ℕ // p ∈ markedPrimes x K a}) → Fin (p.1 + 1) → ℝ :=
    fun p lam => (if p ∈ T then X p lam else 1) / ((p.1 : ℝ) + 1)
  have hD_attach :
      (∏ p ∈ (markedPrimes x K a).attach, ((p.1 : ℝ) + 1)) = D := by
    simpa [D] using
      (Finset.prod_attach (markedPrimes x K a) (fun q : ℕ => (q : ℝ) + 1))
  have hnum (ℓ : LineData x K a) :
      (∏ p : {p : ℕ // p ∈ markedPrimes x K a},
        (if p ∈ T then X p (ℓ p) else 1)) = ∏ p ∈ T, X p (ℓ p) := by
    symm
    apply Finset.prod_subset_one_on_sdiff (Finset.subset_univ T)
    · intro p hp
      have hnot : p ∉ T := (Finset.mem_sdiff.mp hp).2
      simp [hnot]
    · intro p hp
      simp [hp]
  have hnum_attach (ℓ : LineData x K a) :
      (∏ p ∈ (markedPrimes x K a).attach, (if p ∈ T then X p (ℓ p) else 1)) =
        ∏ p ∈ T, X p (ℓ p) := by
    simpa only [Finset.univ_eq_attach] using hnum ℓ
  have hline (ℓ : LineData x K a) :
      (∏ p : {p : ℕ // p ∈ markedPrimes x K a}, g p (ℓ p)) =
        D⁻¹ * ∏ p ∈ T, X p (ℓ p) := by
    dsimp [g]
    rw [Finset.prod_div_distrib, hnum_attach ℓ, hD_attach, div_eq_mul_inv]
    ring
  have hmean_out (p : {p : ℕ // p ∈ markedPrimes x K a})
      (hp : p ∈ (Finset.univ : Finset {p : ℕ // p ∈ markedPrimes x K a}) \ T) :
      (∑ lam : Fin (p.1 + 1), g p lam) = 1 := by
    have hnot : p ∉ T := (Finset.mem_sdiff.mp hp).2
    have hc : ((p.1 : ℝ) + 1) ≠ 0 := by positivity
    simpa [g, hnot, Finset.sum_const, Fintype.card_fin] using (mul_inv_cancel₀ hc)
  have hmean_in (p : {p : ℕ // p ∈ markedPrimes x K a}) (hp : p ∈ T) :
      (∑ lam : Fin (p.1 + 1), g p lam) =
        ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam := by
    simp only [g, if_pos hp, div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact mul_comm _ _
  have hmeans :
      (∏ p : {p : ℕ // p ∈ markedPrimes x K a}, ∑ lam : Fin (p.1 + 1), g p lam) =
        ∏ p ∈ T, ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam := by
    symm
    apply Finset.prod_subset_one_on_sdiff (Finset.subset_univ T)
    · exact hmean_out
    · intro p hp
      exact (hmean_in p hp).symm
  have hreal :
      D⁻¹ * (∑ ℓ : LineData x K a, ∏ p ∈ T, X p (ℓ p)) =
        ∏ p ∈ T, ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam := by
    calc
      D⁻¹ * (∑ ℓ : LineData x K a, ∏ p ∈ T, X p (ℓ p)) =
          ∑ ℓ : LineData x K a, ∏ p : {p : ℕ // p ∈ markedPrimes x K a}, g p (ℓ p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        exact (hline ℓ).symm
      _ = ∏ p : {p : ℕ // p ∈ markedPrimes x K a}, ∑ lam : Fin (p.1 + 1), g p lam :=
        (Fintype.prod_sum g).symm
      _ = ∏ p ∈ T, ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam := hmeans
  simpa [lineAverage, D, map_sum] using congrArg (fun y : ℝ => (y : ℂ)) hreal

private lemma lineAverage_sum {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {ι : Type*}
    (s : Finset ι) (f : ι → LineData x K a → ℝ) :
    lineAverage (fun ℓ => ((∑ i ∈ s, f i ℓ : ℝ) : ℂ)) =
      ∑ i ∈ s, lineAverage (fun ℓ => ((f i ℓ : ℝ) : ℂ)) := by
  classical
  unfold lineAverage
  simp only [Complex.ofReal_sum]
  have hcomm :
      (∑ ℓ : LineData x K a, ∑ i ∈ s, (f i ℓ : ℂ)) =
        ∑ i ∈ s, ∑ ℓ : LineData x K a, (f i ℓ : ℂ) := by
    simpa using
      (Finset.sum_comm (s := (Finset.univ : Finset (LineData x K a))) (t := s)
        (f := fun ℓ i => (f i ℓ : ℂ)))
  rw [hcomm, Finset.mul_sum]

private def elemSymm {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ U ∈ T.powersetCard k, ∏ i ∈ U, μ i

private lemma elemSymm_insert {ι : Type*} [DecidableEq ι] (T : Finset ι) (i : ι)
    (hi : i ∉ T) (μ : ι → ℝ) (n : ℕ) :
    elemSymm (insert i T) μ (n + 1) =
      elemSymm T μ (n + 1) + μ i * elemSymm T μ n := by
  classical
  unfold elemSymm
  rw [Finset.powersetCard_succ_insert hi n]
  have hdis : Disjoint (T.powersetCard (n + 1))
      ((T.powersetCard n).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro U hU hU'
    have hiU : i ∈ U := by
      rcases Finset.mem_image.mp hU' with ⟨s, hs, rfl⟩
      simp
    exact hi ((Finset.mem_powersetCard.mp hU).1 hiU)
  rw [Finset.sum_union hdis]
  have hinj : Set.InjOn (insert i)
      (↑(T.powersetCard n) : Set (Finset ι)) := by
    intro s hs t ht hst
    ext j
    have hmem := congrArg (fun q : Finset ι => j ∈ q) hst
    have hs' : s ∈ T.powersetCard n := by simpa using hs
    have ht' : t ∈ T.powersetCard n := by simpa using ht
    have his : i ∉ s := fun h => hi ((Finset.mem_powersetCard.mp hs').1 h)
    have hit : i ∉ t := fun h => hi ((Finset.mem_powersetCard.mp ht').1 h)
    by_cases hji : j = i
    · subst j
      simp [his, hit]
    · simpa [hji] using hmem
  rw [Finset.sum_image hinj]
  have hterm (s : Finset ι) (hs : s ∈ T.powersetCard n) :
      ∏ j ∈ insert i s, μ j = μ i * ∏ j ∈ s, μ j := by
    have his : i ∉ s := fun h => hi ((Finset.mem_powersetCard.mp hs).1 h)
    simp [Finset.prod_insert, his]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

private lemma pow_add_coeff (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (n : ℕ) :
    s ^ (n + 1) + (n + 1 : ℝ) * a * s ^ n ≤ (s + a) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsa : 0 ≤ s + a := add_nonneg hs ha
      have hextra : 0 ≤ (n + 1 : ℝ) * a ^ 2 * s ^ n := by positivity
      have hident :
          (s ^ (n + 1) + (n + 1 : ℝ) * a * s ^ n) * (s + a) =
            (s ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * a * s ^ (n + 1)) +
              (n + 1 : ℝ) * a ^ 2 * s ^ n := by
        rw [pow_succ s n, pow_succ s (n + 1)]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      calc
        s ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * a * s ^ (n + 1)
            ≤ (s ^ (n + 1 + 1) + (((n + 1 : ℕ) : ℝ) + 1) * a * s ^ (n + 1)) +
                (n + 1 : ℝ) * a ^ 2 * s ^ n := le_add_of_nonneg_right hextra
        _ = (s ^ (n + 1) + (n + 1 : ℝ) * a * s ^ n) * (s + a) := hident.symm
        _ ≤ (s + a) ^ (n + 1) * (s + a) := mul_le_mul_of_nonneg_right ih hsa
        _ = (s + a) ^ (n + 1 + 1) := by simp [pow_succ, Nat.add_assoc]

private lemma elemSymm_le_pow_div_factorial {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (μ : ι → ℝ) (hμ : ∀ i ∈ T, 0 ≤ μ i) :
    ∀ k, elemSymm T μ k ≤ (∑ i ∈ T, μ i) ^ k / (k.factorial : ℝ) := by
  classical
  induction T using Finset.induction_on generalizing μ with
  | empty =>
      intro k
      cases k with
      | zero => simp [elemSymm]
      | succ n =>
          have hcard : Finset.powersetCard (n + 1) (∅ : Finset ι) = ∅ := by
            rw [Finset.powersetCard_eq_empty]
            simp
          simp [elemSymm, hcard]
  | @insert i T hi ih =>
      intro k
      have hμi := hμ i (by simp)
      have hμT : ∀ j ∈ T, 0 ≤ μ j := by
        intro j hj
        exact hμ j (by simp [hj])
      cases k with
      | zero => simp [elemSymm]
      | succ n =>
          let s : ℝ := ∑ j ∈ T, μ j
          have hs : 0 ≤ s := Finset.sum_nonneg hμT
          have hnext := ih μ hμT (n + 1)
          have hprev := ih μ hμT n
          have hfact : ((n + 1).factorial : ℝ) =
              (n + 1 : ℝ) * (n.factorial : ℝ) := by
            simp [Nat.factorial_succ, Nat.cast_mul]
          have hfpos : 0 < ((n + 1).factorial : ℝ) := by positivity
          have hfnz : (n.factorial : ℝ) ≠ 0 := by positivity
          have hsecond :
              μ i * s ^ n / (n.factorial : ℝ) =
                ((n + 1 : ℝ) * μ i * s ^ n) / ((n + 1).factorial : ℝ) := by
            rw [hfact]
            field_simp
          have hfrac :
              s ^ (n + 1) / ((n + 1).factorial : ℝ) +
                μ i * s ^ n / (n.factorial : ℝ) ≤
              (s + μ i) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
            rw [hsecond, ← add_div]
            exact (div_le_div_iff_of_pos_right hfpos).2
              (pow_add_coeff s (μ i) hs hμi n)
          rw [elemSymm_insert T i hi μ n]
          calc
            elemSymm T μ (n + 1) + μ i * elemSymm T μ n
                ≤ s ^ (n + 1) / ((n + 1).factorial : ℝ) +
                    μ i * (s ^ n / (n.factorial : ℝ)) :=
                  add_le_add hnext (mul_le_mul_of_nonneg_left hprev hμi)
            _ = s ^ (n + 1) / ((n + 1).factorial : ℝ) +
                  μ i * s ^ n / (n.factorial : ℝ) := by ring
            _ ≤ (s + μ i) ^ (n + 1) / ((n + 1).factorial : ℝ) := hfrac
            _ = (∑ j ∈ insert i T, μ j) ^ (n + 1) /
                  ((n + 1).factorial : ℝ) := by
                rw [Finset.sum_insert hi]
                simp [s, add_comm]

/-- `t2:pd.root-bonferroni` (new node, general) — PD 03:643-665.  Pointwise Bonferroni sandwich
for numbers in `[0,1]` and the gap bound under independent uniform lines:
`E[B_m - B_{m+1}] = Σ_{|T'|=m+1} ∏ E X_p ≤ (Σ_p E X_p)^{m+1}/(m+1)!`. -/
theorem root_bonferroni {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (T : Finset {p : ℕ // p ∈ markedPrimes x K a})
    (X : (p : {p : ℕ // p ∈ markedPrimes x K a}) → Fin (p.1 + 1) → ℝ)
    (hX : ∀ p lam, 0 ≤ X p lam ∧ X p lam ≤ 1) (m : ℕ) (hm : Even m) :
    (∀ ℓ : LineData x K a,
      bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1) ≤ ∏ p ∈ T, (1 - X p (ℓ p)) ∧
        ∏ p ∈ T, (1 - X p (ℓ p)) ≤ bonferroniTrunc T (fun p => X p (ℓ p)) m) ∧
        (lineAverage (fun ℓ : LineData x K a =>
        ((bonferroniTrunc T (fun p => X p (ℓ p)) m -
          bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1) : ℝ) : ℂ))).re ≤
      (∑ p ∈ T, (((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam)) ^ (m + 1) /
        ((m + 1).factorial : ℝ) := by
  classical
  constructor
  · intro ℓ
    have hXℓ : ∀ p ∈ T, 0 ≤ X p (ℓ p) ∧ X p (ℓ p) ≤ 1 := by
      intro p hp
      exact hX p (ℓ p)
    have hb := bonferroniTrunc_bounds T (fun p => X p (ℓ p)) hXℓ m
    have hm' : Odd (m + 1) := by
      rcases hm with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have hbp := bonferroniTrunc_bounds T (fun p => X p (ℓ p)) hXℓ (m + 1)
    exact ⟨hbp.2 hm', hb.1 hm⟩
  ·
    let μ : {p : ℕ // p ∈ markedPrimes x K a} → ℝ := fun p =>
      ((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam
    let U := T.powerset.filter (fun W => W.card = m + 1)
    have hμ : ∀ p ∈ T, 0 ≤ μ p := by
      intro p hp
      dsimp [μ]
      apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg
        intro lam hlam
        exact (hX p lam).1
    have hgapfun :
        (fun ℓ : LineData x K a =>
          bonferroniTrunc T (fun p => X p (ℓ p)) m -
            bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1)) =
          (fun ℓ => ∑ W ∈ U, ∏ p ∈ W, X p (ℓ p)) := by
      funext ℓ
      exact bonferroniTrunc_gap T (fun p => X p (ℓ p)) m hm
    have hgapcast :
        (fun ℓ : LineData x K a =>
          ((bonferroniTrunc T (fun p => X p (ℓ p)) m -
            bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1) : ℝ) : ℂ)) =
          (fun ℓ => ((∑ W ∈ U, ∏ p ∈ W, X p (ℓ p) : ℝ) : ℂ)) := by
      funext ℓ
      exact congrArg (fun y : ℝ => (y : ℂ)) (congrFun hgapfun ℓ)
    have hlinear :
        lineAverage (fun ℓ : LineData x K a =>
          ((bonferroniTrunc T (fun p => X p (ℓ p)) m -
            bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1) : ℝ) : ℂ)) =
          ∑ W ∈ U, lineAverage (fun ℓ : LineData x K a =>
            ((∏ p ∈ W, X p (ℓ p) : ℝ) : ℂ)) := by
      rw [hgapcast, lineAverage_sum]
    have haverage :
        (lineAverage (fun ℓ : LineData x K a =>
          ((bonferroniTrunc T (fun p => X p (ℓ p)) m -
            bonferroniTrunc T (fun p => X p (ℓ p)) (m + 1) : ℝ) : ℂ))).re =
          ∑ W ∈ U, ∏ p ∈ W,
            (((p.1 : ℝ) + 1)⁻¹ * ∑ lam : Fin (p.1 + 1), X p lam) := by
      rw [hlinear, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro W hW
      rw [lineAverage_prod]
      exact Complex.ofReal_re _
    rw [haverage]
    have hbound := elemSymm_le_pow_div_factorial T μ hμ (m + 1)
    simpa [elemSymm, U, μ, Finset.powersetCard_eq_filter] using hbound

/-- A path contributes when it is admissible, has nonzero coefficient, and its archimedean factor
is not identically zero on the root region. -/
def IsContributingPath {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) : Prop :=
  IsEnvPathAdmissible F S γ ∧ pathCoefficient F S γ ≠ 0 ∧
    ∃ w : ArchRoot, w.InRegion S ∧ pathArch F S w γ ≠ 0

/-- The primes active somewhere on a path. -/
def pathActivePrimes {x : ℝ} {K : ℕ} (γ : EnvPath x K) : Finset ℕ :=
  Finset.univ.biUnion fun j : Fin (pathLength x + 1) =>
    Finset.univ.biUnion fun i : Fin K => Finset.univ.image fun jj => (γ j).2 i jj

private lemma one_sub_prod_le_sum_one_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have h0i := h0 i (by simp)
      have h1i := h1 i (by simp)
      have h0s : ∀ j ∈ s, 0 ≤ f j := by
        intro j hj
        exact h0 j (by simp [hj])
      have h1s : ∀ j ∈ s, f j ≤ 1 := by
        intro j hj
        exact h1 j (by simp [hj])
      have hprod0 : 0 ≤ ∏ j ∈ s, f j := Finset.prod_nonneg fun j hj => h0s j hj
      have hprod1 : ∏ j ∈ s, f j ≤ 1 := Finset.prod_le_one₀ h0s h1s
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hid : 1 - f i * ∏ j ∈ s, f j = (1 - f i) + f i * (1 - ∏ j ∈ s, f j) := by ring
      rw [hid]
      calc
        (1 - f i) + f i * (1 - ∏ j ∈ s, f j)
            ≤ (1 - f i) + (1 - ∏ j ∈ s, f j) := by
                have hsub : 0 ≤ 1 - ∏ j ∈ s, f j := by linarith [hprod1]
                have hmul : f i * (1 - ∏ j ∈ s, f j) ≤ 1 - ∏ j ∈ s, f j := by
                  calc
                    f i * (1 - ∏ j ∈ s, f j) ≤ 1 * (1 - ∏ j ∈ s, f j) :=
                      mul_le_mul_of_nonneg_right h1i hsub
                    _ = 1 - ∏ j ∈ s, f j := by ring
                simpa [add_comm] using add_le_add_left hmul (1 - f i)
        _ ≤ (1 - f i) + ∑ j ∈ s, (1 - f j) := by
              simpa [add_comm] using add_le_add_left (ih h0s h1s) (1 - f i)

private lemma root_inactive_prime_excess_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (p : ℕ) (hq₀ : 0 < F.q_d) (hq₁ : F.q_d < 1)
    (hp : p ∉ pathActivePrimes γ) :
    ((p : ℝ) + 1)⁻¹ * ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam) ≤
      ((p : ℝ) + 1)⁻¹ * ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := by
  classical
  have hnot : ∀ j : Fin (pathLength S.x + 1), ¬ IsActiveAt γ p j := by
    intro j hj
    rcases hj with ⟨i, jj, hij⟩
    apply hp
    simp only [pathActivePrimes, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    exact ⟨j, i, jj, hij⟩
  have heta (j : Fin (pathLength S.x + 1)) :
      0 ≤ memoryEta S.x F.q_d j.val ∧ memoryEta S.x F.q_d j.val ≤ 1 := by
    have hq : 0 ≤ memoryQ S.x F.q_d j.val ∧ memoryQ S.x F.q_d j.val ≤ 1 := by
      dsimp [memoryQ]
      split_ifs with h
      · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hq₁.le⟩
      · exact ⟨le_of_lt hq₀, hq₁.le⟩
    dsimp [memoryEta]
    constructor <;> linarith
  have hfactor (lam : Fin (p + 1)) :
      pathPrimeFactor F S γ p lam =
        ∏ j : Fin (pathLength S.x + 1),
          (1 - memoryEta S.x F.q_d j.val *
            (if lam = projLine p (γ j).1 then 1 else 0)) := by
    simp [pathPrimeFactor, hnot]
  have hpoint (lam : Fin (p + 1)) :
      1 - pathPrimeFactor F S γ p lam ≤
        ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val *
          (if lam = projLine p (γ j).1 then 1 else 0) := by
    rw [hfactor]
    have h₀ : ∀ j : Fin (pathLength S.x + 1),
        0 ≤ 1 - memoryEta S.x F.q_d j.val *
          (if lam = projLine p (γ j).1 then 1 else 0) := by
      intro j
      by_cases heq : lam = projLine p (γ j).1 <;> simp [heq, (heta j).1, (heta j).2]
    have h₁ : ∀ j : Fin (pathLength S.x + 1),
        1 - memoryEta S.x F.q_d j.val *
          (if lam = projLine p (γ j).1 then 1 else 0) ≤ 1 := by
      intro j
      by_cases heq : lam = projLine p (γ j).1 <;> simp [heq, (heta j).1, (heta j).2]
    have hprod := one_sub_prod_le_sum_one_sub Finset.univ
      (fun j => 1 - memoryEta S.x F.q_d j.val *
        (if lam = projLine p (γ j).1 then 1 else 0))
      (by intro j hj; exact h₀ j) (by intro j hj; exact h₁ j)
    simpa using hprod
  have hsum₀ :
      ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam) ≤
        ∑ lam : Fin (p + 1),
          ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val *
            (if lam = projLine p (γ j).1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro lam hlam
    exact hpoint lam
  have hcollapse :
      ∑ j : Fin (pathLength S.x + 1),
          ∑ lam : Fin (p + 1), memoryEta S.x F.q_d j.val *
            (if lam = projLine p (γ j).1 then 1 else 0) =
        ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp
  have hsum :
      ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam) ≤
        ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := by
    calc
      ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam) ≤
          ∑ lam : Fin (p + 1),
            ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val *
              (if lam = projLine p (γ j).1 then 1 else 0) := hsum₀
      _ = ∑ j : Fin (pathLength S.x + 1),
            ∑ lam : Fin (p + 1), memoryEta S.x F.q_d j.val *
              (if lam = projLine p (γ j).1 then 1 else 0) := by rw [Finset.sum_comm]
      _ = ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := hcollapse
  have hden : 0 ≤ ((p : ℝ) + 1)⁻¹ := by positivity
  calc
    ((p : ℝ) + 1)⁻¹ * ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam)
        ≤ ((p : ℝ) + 1)⁻¹ * ∑ j : Fin (pathLength S.x + 1),
            memoryEta S.x F.q_d j.val := mul_le_mul_of_nonneg_left hsum hden

private lemma root_inactive_total_excess_le {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hq₀ : 0 < F.q_d) (hq₁ : F.q_d < 1)
    (B : ℝ) (hB : 0 ≤ B)
    (hMass : (∑ p ∈ markedPrimes S.x K F.a, ((p : ℝ) + 1)⁻¹) ≤ B) :
    (∑ p ∈ (markedPrimes S.x K F.a).filter
        (fun p => p ∉ pathActivePrimes γ),
      ((p : ℝ) + 1)⁻¹ *
        ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam)) ≤
      B * ((S.N : ℝ) + 1) := by
  classical
  let P := markedPrimes S.x K F.a
  let I := P.filter (fun p => p ∉ pathActivePrimes γ)
  have hmassI : (∑ p ∈ I, ((p : ℝ) + 1)⁻¹) ≤ B := by
    have hsub : (∑ p ∈ I, ((p : ℝ) + 1)⁻¹) ≤
        ∑ p ∈ P, ((p : ℝ) + 1)⁻¹ := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro p hp
      by_cases hin : p ∉ pathActivePrimes γ <;> simp [hin] <;> positivity
    exact hsub.trans (by simpa [P] using hMass)
  have heta (j : Fin (pathLength S.x + 1)) :
      0 ≤ memoryEta S.x F.q_d j.val ∧ memoryEta S.x F.q_d j.val ≤ 1 := by
    have hq : 0 ≤ F.q_d ∧ F.q_d ≤ 1 := ⟨le_of_lt hq₀, hq₁.le⟩
    have hQ : 0 ≤ memoryQ S.x F.q_d j.val ∧ memoryQ S.x F.q_d j.val ≤ 1 := by
      dsimp [memoryQ]
      split_ifs with h
      · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hq.2⟩
      · exact hq
    dsimp [memoryEta]
    constructor <;> linarith
  have hEta0 :
      0 ≤ ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val :=
    Finset.sum_nonneg fun j _ => (heta j).1
  have hEtaSum :
      (∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val) ≤
        ((S.N : ℝ) + 1) := by
    have hle :
        (∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val) ≤
          ∑ j : Fin (pathLength S.x + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (heta j).2
    calc
      _ ≤ ∑ j : Fin (pathLength S.x + 1), (1 : ℝ) := hle
      _ = ((S.N : ℝ) + 1) := by simp [PDScale.N]
  calc
    (∑ p ∈ I, ((p : ℝ) + 1)⁻¹ *
        ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam)) ≤
        ∑ p ∈ I, ((p : ℝ) + 1)⁻¹ *
          ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := by
            apply Finset.sum_le_sum
            intro p hp
            exact root_inactive_prime_excess_le F S γ p hq₀ hq₁
              (Finset.mem_filter.mp hp).2
    _ = (∑ p ∈ I, ((p : ℝ) + 1)⁻¹) *
          ∑ j : Fin (pathLength S.x + 1), memoryEta S.x F.q_d j.val := by
            rw [Finset.sum_mul]
    _ ≤ B * ((S.N : ℝ) + 1) := by
          exact (mul_le_mul hmassI hEtaSum hEta0 hB)

private lemma sum_union_le_sum_add {ι : Type*} [DecidableEq ι] (s t : Finset ι)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ s ∪ t, f i) ≤ (∑ i ∈ s, f i) + (∑ i ∈ t, f i) := by
  classical
  have hsub : (∑ i ∈ s \ t, f i) ≤ ∑ i ∈ s, f i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (by intro i hi hnot; exact hf i)
  have hEq : s \ t ∪ t = s ∪ t := by
    ext i
    simp [Finset.mem_sdiff]
  rw [← hEq, Finset.sum_union disjoint_sdiff_self_left]
  simpa [add_comm] using add_le_add_right hsub (∑ i ∈ t, f i)

private lemma sum_biUnion_le_sum_sum {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : ι → Finset κ) (f : κ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ k ∈ s.biUnion t, f k) ≤ ∑ i ∈ s, ∑ k ∈ t i, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert]
      calc
        (∑ k ∈ t i ∪ s.biUnion t, f k) ≤
            (∑ k ∈ t i, f k) + (∑ k ∈ s.biUnion t, f k) :=
          sum_union_le_sum_add (t i) (s.biUnion t) f hf
        _ ≤ (∑ k ∈ t i, f k) + ∑ j ∈ s, ∑ k ∈ t j, f k := by
          simpa [add_comm] using add_le_add_left ih (∑ k ∈ t i, f k)
        _ = ∑ j ∈ insert i s, ∑ k ∈ t j, f k := by rw [Finset.sum_insert hi]

private lemma marked_reciprocal_mass_bound {K : ℕ} (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ B x₀ : ℝ, 0 < B ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (∑ p ∈ markedPrimes x K a, ((p : ℝ) + 1)⁻¹) ≤ B := by
  classical
  rcases ha with ⟨hK, ha, horder⟩
  have hband : ∀ i : Fin K, ∃ xi : ℝ, 2 ≤ xi ∧
      ∀ x : ℝ, xi ≤ x → bandMass x (a i) ≤ 2 := by
    intro i
    have hai := ha i
    obtain ⟨xi, hxi, hmass⟩ := band_mass (a i)
      (by linarith [hai.1]) (by linarith [hai.2]) 1 (by norm_num)
    refine ⟨xi, hxi, ?_⟩
    intro x hx
    have habs := (hmass x hx).1
    have hlog : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hupper := (abs_le.mp habs).2
    linarith
  choose X hX using hband
  let x₀ : ℝ := ∑ i : Fin K, X i
  let B : ℝ := 2 * K
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_of_lt hK)
  have hx₀ : 2 ≤ x₀ := by
    have hsum : (∑ i : Fin K, (2 : ℝ)) ≤ ∑ i : Fin K, X i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hX i).1
    have hsum' : (K : ℝ) * 2 ≤ x₀ := by
      dsimp [x₀]
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
    nlinarith [hsum', hKreal]
  have hXi (i : Fin K) : X i ≤ x₀ := by
    dsimp [x₀]
    exact Finset.single_le_sum (fun j hj => le_trans (by norm_num) (hX j).1)
      (Finset.mem_univ i)
  refine ⟨B, x₀, ?_, hx₀, ?_⟩
  · dsimp [B]
    exact mul_pos (by norm_num) (by exact_mod_cast (Nat.pos_of_ne_zero (by omega : K ≠ 0)))
  · intro x hx
    have hbandmass (i : Fin K) : bandMass x (a i) ≤ 2 :=
      (hX i).2 x (le_trans (hXi i) hx)
    have hsumUnion :
        (∑ p ∈ markedPrimes x K a, ((p : ℝ) + 1)⁻¹) ≤
          ∑ i : Fin K, ∑ p ∈ primeBand x (a i), ((p : ℝ) + 1)⁻¹ := by
      simpa [markedPrimes] using
        (sum_biUnion_le_sum_sum (Finset.univ : Finset (Fin K))
          (fun i => primeBand x (a i)) (fun p => ((p : ℝ) + 1)⁻¹)
          (by intro p; positivity))
    have hbandSum (i : Fin K) :
        (∑ p ∈ primeBand x (a i), ((p : ℝ) + 1)⁻¹) ≤ bandMass x (a i) := by
      rw [bandMass]
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
      simpa [one_div] using
        one_div_le_one_div_of_le (a := (p : ℝ)) (b := (p : ℝ) + 1)
          hpPos (by linarith)
    have hsumMass :
        (∑ i : Fin K, ∑ p ∈ primeBand x (a i), ((p : ℝ) + 1)⁻¹) ≤
          ∑ i : Fin K, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hbandSum i).trans (hbandmass i)
    calc
      (∑ p ∈ markedPrimes x K a, ((p : ℝ) + 1)⁻¹) ≤
          ∑ i : Fin K, ∑ p ∈ primeBand x (a i), ((p : ℝ) + 1)⁻¹ := hsumUnion
      _ ≤ ∑ i : Fin K, (2 : ℝ) := hsumMass
      _ = B := by simp [B, Finset.sum_const, nsmul_eq_mul, mul_comm]

private lemma pathActivePrimes_card_le {x : ℝ} {K : ℕ} (γ : EnvPath x K) :
    (pathActivePrimes γ).card ≤ (pathLength x + 1) * K * slotCount x := by
  classical
  unfold pathActivePrimes
  calc
    (Finset.univ.biUnion fun j : Fin (pathLength x + 1) =>
        Finset.univ.biUnion fun i : Fin K =>
          Finset.univ.image fun jj => (γ j).2 i jj).card ≤
      ∑ j : Fin (pathLength x + 1),
        (Finset.univ.biUnion fun i : Fin K =>
          Finset.univ.image fun jj => (γ j).2 i jj).card := Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (pathLength x + 1),
        ∑ i : Fin K, (Finset.univ.image fun jj => (γ j).2 i jj).card := by
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (pathLength x + 1), ∑ i : Fin K, slotCount x := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro i hi
          calc
            (Finset.univ.image fun jj => (γ j).2 i jj).card ≤
                (Finset.univ : Finset (Fin (slotCount x))).card := Finset.card_image_le
            _ = slotCount x := by simp
    _ = (pathLength x + 1) * K * slotCount x := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

private lemma real_exp_pow_nat (t : ℝ) (n : ℕ) :
    Real.exp t ^ n = Real.exp (t * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

private lemma compactSupport_abs_bound {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, f t ≠ 0 → |t| ≤ B := by
  classical
  have hbounded : Bornology.IsBounded (tsupport f) := hf.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hbounded
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro t ht
  have htSupport : t ∈ tsupport f := by
    apply subset_tsupport
    simpa [Function.support] using ht
  have htBall : dist t 0 ≤ R := Metric.mem_closedBall.mp (hR htSupport)
  have htAbs : |t| ≤ R := by simpa [Real.dist_eq] using htBall
  exact htAbs.trans (le_max_left _ _)

private lemma pdfix_psi_abs_bound {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, F.psi t ≠ 0 → |t| ≤ B := by
  rcases hF with ⟨_, _, _, _, _, hArc⟩
  exact compactSupport_abs_bound hArc.2.1

private lemma geometricMultiplier_psi_ne_zero {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ)
    (hgeom : geometricMultiplier F S D aa bb t ≠ 0) :
    F.psi ((t : ℝ) / S.Y) ≠ 0 := by
  intro hpsi
  apply hgeom
  simp [geometricMultiplier, rawMultiplier, comparisonMultiplier, majorKernel, hpsi]

private lemma slotKernel_nonzero_structure {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (dt : ℤ) (h : slotKernel F S p q dt ≠ 0) :
    IsSlotTransition p q ∧ IsPadAdmissible S.d₀ (sharedProduct p) dt ∧
      geometricMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
        (dt / (sharedProduct p : ℤ)) ≠ 0 := by
  by_cases hcond : IsSlotTransition p q ∧ IsPadAdmissible S.d₀ (sharedProduct p) dt
  · have hmul :
        ((∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ : ℝ) : ℂ) *
          geometricMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
            (dt / (sharedProduct p : ℤ)) ≠ 0 := by
      simpa [slotKernel, hcond] using h
    exact ⟨hcond.1, hcond.2, (mul_ne_zero_iff.mp hmul).2⟩
  · simp [slotKernel, hcond] at h

private lemma slotKernel_det_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (dt : ℤ) (B : ℝ) (hB : 0 ≤ B)
    (hpsiBound : ∀ t, F.psi t ≠ 0 → |t| ≤ B) (hY : 0 < S.Y)
    (hkernel : slotKernel F S p q dt ≠ 0) :
    |(dt : ℝ)| ≤ 2 * B * (S.d₀ : ℝ) * S.Y := by
  classical
  rcases slotKernel_nonzero_structure F S p q dt hkernel with ⟨_, hpad, hgeom⟩
  let D := sharedProduct p
  have hpsi := geometricMultiplier_psi_ne_zero F S D (lastProduct q) (lastProduct p)
    (dt / (D : ℤ)) hgeom
  have hquotient :
      |((dt / (D : ℤ) : ℤ) : ℝ)| ≤ B * S.Y := by
    have hratio := hpsiBound (((dt / (D : ℤ) : ℤ) : ℝ) / S.Y) hpsi
    rw [abs_div, abs_of_pos hY] at hratio
    exact (div_le_iff₀ hY).mp hratio
  have hdiv : (D : ℤ) ∣ dt := by simpa [D] using hpad.2.2
  have hdetInt : (dt / (D : ℤ)) * (D : ℤ) = dt := Int.ediv_mul_cancel hdiv
  have hdetReal : (dt : ℝ) =
      ((dt / (D : ℤ) : ℤ) : ℝ) * (D : ℝ) := by
    exact_mod_cast hdetInt.symm
  have hDnonneg : 0 ≤ (D : ℝ) := by positivity
  have hDupper : (D : ℝ) ≤ 2 * (S.d₀ : ℝ) := by
    dsimp [D]
    exact hpad.2.1.le
  have hBY : 0 ≤ B * S.Y := mul_nonneg hB hY.le
  calc
    |(dt : ℝ)| =
        |((dt / (D : ℤ) : ℤ) : ℝ)| * (D : ℝ) := by
          rw [hdetReal, abs_mul, abs_of_nonneg hDnonneg]
    _ ≤ (B * S.Y) * (2 * (S.d₀ : ℝ)) :=
          mul_le_mul hquotient hDupper hDnonneg hBY
    _ = 2 * B * (S.d₀ : ℝ) * S.Y := by ring

private lemma det2_swap (z z' : ℤ × ℤ) : det2 z' z = -det2 z z' := by
  unfold det2
  ring

private lemma symKernel_nonzero_term {K : ℕ} (F : PDFix K) (S : PDScale)
    (forward : Bool) (s s' : EnvPoint S.x K)
    (hsym : symKernel F S forward s s' ≠ 0) :
    ∃ σ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)),
      (if forward then
        slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
      else
        star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2)
          (det2 s'.1 s.1))) ≠ 0 := by
  classical
  let A (σ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x))) : ℂ :=
    if forward then
      slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
    else
      star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2)
        (det2 s'.1 s.1))
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)), A σ σ') ≠ 0 := by
    have hmul :
        ((permCount S.x K : ℂ))⁻¹ ^ 2 *
          (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ σ' : Fin K → Equiv.Perm (Fin (slotCount S.x)), A σ σ') ≠ 0 := by
      simpa [symKernel, A] using hsym
    exact (mul_ne_zero_iff.mp hmul).2
  obtain ⟨σ, hσ, hinner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  obtain ⟨σ', hσ', hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  exact ⟨σ, σ', by simpa [A] using hterm⟩

private lemma pathCoefficient_edge_det_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hcoef : pathCoefficient F S γ ≠ 0)
    (j : Fin (pathLength S.x)) (B : ℝ) (hB : 0 ≤ B)
    (hpsiBound : ∀ t, F.psi t ≠ 0 → |t| ≤ B) (hY : 0 < S.Y) :
    |det2 (γ j.castSucc).1 (γ j.succ).1| ≤ 2 * B * (S.d₀ : ℝ) * S.Y := by
  classical
  have hsym :
      symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ) ≠ 0 := by
    intro hz
    apply hcoef
    unfold pathCoefficient
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz]
    simp
  obtain ⟨σ, σ', hterm⟩ := symKernel_nonzero_term F S
    (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ) hsym
  cases hfwd : decide (j.val % 2 = 0) with
  | true =>
      have hslot :
          slotKernel F S (permuteLists σ (γ j.castSucc).2)
            (permuteLists σ' (γ j.succ).2)
            (det2 (γ j.castSucc).1 (γ j.succ).1) ≠ 0 := by
        simpa [hfwd] using hterm
      simpa [Int.cast_abs] using
        (slotKernel_det_bound F S _ _ _ B hB hpsiBound hY hslot)
  | false =>
      have hstar : star (slotKernel F S (permuteLists σ' (γ j.succ).2)
          (permuteLists σ (γ j.castSucc).2)
          (det2 (γ j.succ).1 (γ j.castSucc).1)) ≠ 0 := by
        simpa [hfwd] using hterm
      have hslot : slotKernel F S (permuteLists σ' (γ j.succ).2)
          (permuteLists σ (γ j.castSucc).2)
          (det2 (γ j.succ).1 (γ j.castSucc).1) ≠ 0 := by
        simpa using hstar
      have hb := slotKernel_det_bound F S _ _ _ B hB hpsiBound hY hslot
      have hswap := det2_swap (γ j.castSucc).1 (γ j.succ).1
      rw [hswap, Int.cast_neg, abs_neg] at hb
      simpa [Int.cast_abs] using hb

private lemma pathArch_box_good {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (γ : EnvPath S.x K) (harch : pathArch F S w γ ≠ 0) :
    ∀ j : Fin (pathLength S.x + 1),
      envBox S w (γ j).1 ∧ envGood F S w (γ j) := by
  intro j
  have hprod :
      (∏ j : Fin (pathLength S.x + 1),
        if envBox S w (γ j).1 ∧ envGood F S w (γ j) then (1 : ℝ) else 0) ≠ 0 := harch
  have hfactor :
      (if envBox S w (γ j).1 ∧ envGood F S w (γ j) then (1 : ℝ) else 0) ≠ 0 := by
    intro hz
    exact hprod (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  by_contra hn
  simp [hn] at hfactor

private lemma envBox_tau_bounds {K : ℕ} (S : PDScale) (w : ArchRoot)
    (z : ℤ × ℤ) (hw : w.InRegion S) (hU : 0 < S.U)
    (hbox : envBox S w z) :
    (1 / 16 : ℝ) ≤ w.tau z ∧ w.tau z ≤ 16 := by
  rcases hw with ⟨huL, huU, hvL, hvU, hrL, hrU⟩
  rcases hbox with ⟨hboxL, hboxU, _, _⟩
  have huPos : 0 < w.u := hU.trans_le huL
  have hratioL : S.U / w.u ≤ w.tau z := (div_le_iff₀ huPos).2 (by
    simpa [mul_comm] using hboxL)
  have hratioL' : (1 / 16 : ℝ) ≤ S.U / w.u :=
    (le_div_iff₀ huPos).2 (by nlinarith)
  have hratioU : w.tau z ≤ (16 * S.U) / w.u :=
    (le_div_iff₀ huPos).2 (by simpa [mul_comm] using hboxU)
  have hratioU' : (16 * S.U) / w.u ≤ 16 :=
    (div_le_iff₀ huPos).2 (by nlinarith [huL])
  exact ⟨hratioL'.trans hratioL, hratioU.trans hratioU'⟩

private lemma det2_archCoord (w : ArchRoot) (hu : w.u ≠ 0) (z z' : ℤ × ℤ) :
    det2 z z' =
      (w.u * w.tau z) * (w.v * w.tau z' + (z'.2 : ℝ) / w.u) -
        (w.v * w.tau z + (z.2 : ℝ) / w.u) * (w.u * w.tau z') := by
  unfold det2 ArchRoot.tau
  push_cast
  field_simp [hu]
  ring

private def archRootCoordX (w : ArchRoot) (z : ℤ × ℤ) : ℝ := w.u * w.tau z

private def archRootCoordY (w : ArchRoot) (z : ℤ × ℤ) : ℝ :=
  w.v * w.tau z + (z.2 : ℝ) / w.u

private def archRootSlope (w : ArchRoot) (z : ℤ × ℤ) : ℝ :=
  archRootCoordY w z / archRootCoordX w z

private lemma archRootSlope_step (w : ArchRoot) (hu : w.u ≠ 0) (z z' : ℤ × ℤ)
    (hx : 0 < archRootCoordX w z) (hx' : 0 < archRootCoordX w z') :
    archRootSlope w z' - archRootSlope w z =
      det2 z z' / (archRootCoordX w z * archRootCoordX w z') := by
  have hprod : w.u * w.tau z ≠ 0 := by
    exact ne_of_gt (by simpa [archRootCoordX] using hx)
  have hprod' : w.u * w.tau z' ≠ 0 := by
    exact ne_of_gt (by simpa [archRootCoordX] using hx')
  have htau : w.tau z ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  have htau' : w.tau z' ≠ 0 := (mul_ne_zero_iff.mp hprod').2
  rw [archRootSlope, archRootSlope, archRootCoordX, archRootCoordX,
    archRootCoordY, archRootCoordY, det2_archCoord w hu z z']
  field_simp [hu, htau, htau']

private lemma abs_fin_path_variation_le {N : ℕ} (f : Fin (N + 1) → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hstep : ∀ j : Fin N, |f j.succ - f j.castSucc| ≤ B) :
    ∀ j : Fin (N + 1), |f j - f 0| ≤ (j.val : ℝ) * B := by
  have hbound : ∀ n (hn : n ≤ N),
      |f ⟨n, Nat.lt_succ_of_le hn⟩ - f 0| ≤ (n : ℝ) * B := by
    intro n
    induction n with
    | zero =>
        intro hn
        simp
    | succ n ih =>
        intro hn
        have hnle : n ≤ N := Nat.le_of_succ_le hn
        have hprev := ih hnle
        let e : Fin N := ⟨n, Nat.lt_of_succ_le hn⟩
        have hnext := hstep e
        have hnext' :
            |f ⟨n + 1, Nat.lt_succ_of_le hn⟩ - f ⟨n, Nat.lt_succ_of_le hnle⟩| ≤ B := by
          simpa [e] using hnext
        have hprev' :
            |f ⟨n, Nat.lt_succ_of_le hnle⟩ - f 0| ≤ (n : ℝ) * B := by
          simpa using hprev
        calc
          |f ⟨n + 1, Nat.lt_succ_of_le hn⟩ - f 0| =
              |(f ⟨n + 1, Nat.lt_succ_of_le hn⟩ -
                  f ⟨n, Nat.lt_succ_of_le hnle⟩) +
                (f ⟨n, Nat.lt_succ_of_le hnle⟩ - f 0)| := by congr 1 <;> ring
          _ ≤ |f ⟨n + 1, Nat.lt_succ_of_le hn⟩ -
                f ⟨n, Nat.lt_succ_of_le hnle⟩| +
              |f ⟨n, Nat.lt_succ_of_le hnle⟩ - f 0| := abs_add_le _ _
          _ ≤ B + (n : ℝ) * B := add_le_add hnext' hprev'
          _ = ((n + 1 : ℕ) : ℝ) * B := by rw [Nat.cast_add]; ring
  intro j
  exact hbound j.val (Nat.le_of_lt_succ j.isLt)

private lemma path_second_coordinate_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (w : ArchRoot)
    (hPath : IsEnvPathAdmissible F S γ) (hw : w.InRegion S) (hU : 0 < S.U)
    (harch : pathArch F S w γ ≠ 0) (hcoef : pathCoefficient F S γ ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) (hpsiBound : ∀ t, F.psi t ≠ 0 → |t| ≤ B)
    (hY : 0 < S.Y) :
    ∀ j : Fin (pathLength S.x + 1),
      |((γ j).1.2 : ℝ)| ≤ 256 * (j.val : ℝ) *
        (2 * B * (S.d₀ : ℝ) * S.Y) := by
  classical
  have hboxes := pathArch_box_good F S w γ harch
  have huPos : 0 < w.u := hU.trans_le hw.1
  have hu : w.u ≠ 0 := ne_of_gt huPos
  let E : ℝ := 2 * B * (S.d₀ : ℝ) * S.Y
  let bstep : ℝ := E / S.U ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hstepNonneg : 0 ≤ bstep := by
    dsimp [bstep]
    exact div_nonneg hE (sq_nonneg _)
  have hU2 : 0 < S.U ^ 2 := sq_pos_of_pos hU
  have hSlopeStep : ∀ k : Fin (pathLength S.x),
      |archRootSlope w ((γ k.succ).1) - archRootSlope w ((γ k.castSucc).1)| ≤ bstep := by
    intro k
    have hbox₀ := (hboxes k.castSucc).1
    have hbox₁ := (hboxes k.succ).1
    have hbox₀L : S.U ≤ archRootCoordX w (γ k.castSucc).1 := by
      simpa [archRootCoordX] using hbox₀.1
    have hbox₁L : S.U ≤ archRootCoordX w (γ k.succ).1 := by
      simpa [archRootCoordX] using hbox₁.1
    have hx₀ : 0 < archRootCoordX w (γ k.castSucc).1 := hU.trans_le hbox₀L
    have hx₁ : 0 < archRootCoordX w (γ k.succ).1 := hU.trans_le hbox₁L
    have hprodPos :
        0 < archRootCoordX w (γ k.castSucc).1 * archRootCoordX w (γ k.succ).1 :=
      mul_pos hx₀ hx₁
    have hprodLower : S.U ^ 2 ≤
        archRootCoordX w (γ k.castSucc).1 * archRootCoordX w (γ k.succ).1 := by
      calc
        S.U ^ 2 = S.U * S.U := by rw [pow_two]
        _ ≤ archRootCoordX w (γ k.castSucc).1 * S.U :=
          mul_le_mul_of_nonneg_right hbox₀L (le_of_lt hU)
        _ ≤ archRootCoordX w (γ k.castSucc).1 * archRootCoordX w (γ k.succ).1 :=
          mul_le_mul_of_nonneg_left hbox₁L (le_of_lt hx₀)
    have hdet := pathCoefficient_edge_det_bound F S γ hcoef k B hB hpsiBound hY
    have hnum :
        |det2 (γ k.castSucc).1 (γ k.succ).1| * S.U ^ 2 ≤
          E * (archRootCoordX w (γ k.castSucc).1 * archRootCoordX w (γ k.succ).1) :=
      mul_le_mul hdet hprodLower (sq_nonneg S.U) hE
    have hfrac :
        |det2 (γ k.castSucc).1 (γ k.succ).1| /
            (archRootCoordX w (γ k.castSucc).1 * archRootCoordX w (γ k.succ).1) ≤
          E / S.U ^ 2 := (div_le_div_iff₀ hprodPos hU2).2 hnum
    rw [archRootSlope_step w hu _ _ hx₀ hx₁, abs_div, abs_of_pos hprodPos]
    simpa [bstep] using hfrac
  have hvariation := abs_fin_path_variation_le
    (fun j => archRootSlope w (γ j).1) bstep hstepNonneg hSlopeStep
  intro j
  let z₀ := (γ 0).1
  let zj := (γ j).1
  have hzstart : z₀ = (1, 0) := hPath.2.1
  have hbox₀ := (hboxes 0).1
  have hboxj := (hboxes j).1
  have hbox₀L : S.U ≤ archRootCoordX w z₀ := by simpa [archRootCoordX] using hbox₀.1
  have hboxjL : S.U ≤ archRootCoordX w zj := by simpa [archRootCoordX] using hboxj.1
  have hx₀pos : 0 < archRootCoordX w z₀ := hU.trans_le hbox₀L
  have hxjpos : 0 < archRootCoordX w zj := hU.trans_le hboxjL
  have hx₀upper : archRootCoordX w z₀ ≤ 16 * S.U := by
    simpa [archRootCoordX] using hbox₀.2.1
  have hxjupper : archRootCoordX w zj ≤ 16 * S.U := by
    simpa [archRootCoordX] using hboxj.2.1
  have hprod0 : 0 ≤ archRootCoordX w z₀ * archRootCoordX w zj :=
    mul_nonneg (le_of_lt hx₀pos) (le_of_lt hxjpos)
  have hprodUpper : archRootCoordX w z₀ * archRootCoordX w zj ≤ 256 * S.U ^ 2 := by
    calc
      archRootCoordX w z₀ * archRootCoordX w zj ≤
          (16 * S.U) * (16 * S.U) :=
        mul_le_mul hx₀upper hxjupper (le_of_lt hxjpos) (by positivity)
      _ = 256 * S.U ^ 2 := by ring
  have hdetArch := det2_archCoord w hu z₀ zj
  have hdetStart : det2 z₀ zj = zj.2 := by
    rw [hzstart]
    simp [det2]
  have hdetStartCast := congrArg (fun d : ℤ => (d : ℝ)) hdetStart
  rw [hdetStartCast] at hdetArch
  change (zj.2 : ℝ) =
    archRootCoordX w z₀ * archRootCoordY w zj -
      archRootCoordY w z₀ * archRootCoordX w zj at hdetArch
  have hcoordSlope :
      archRootCoordX w z₀ * archRootCoordY w zj -
          archRootCoordY w z₀ * archRootCoordX w zj =
        archRootCoordX w z₀ * archRootCoordX w zj *
          (archRootSlope w zj - archRootSlope w z₀) := by
    have hτ₀ : w.tau z₀ ≠ 0 :=
      (mul_ne_zero_iff.mp (ne_of_gt (by simpa [archRootCoordX] using hx₀pos))).2
    have hτj : w.tau zj ≠ 0 :=
      (mul_ne_zero_iff.mp (ne_of_gt (by simpa [archRootCoordX] using hxjpos))).2
    dsimp [archRootCoordX, archRootCoordY, archRootSlope]
    field_simp [hu, hτ₀, hτj]
  rw [hcoordSlope] at hdetArch
  have hcoordAbs :
      |(zj.2 : ℝ)| =
        archRootCoordX w z₀ * archRootCoordX w zj *
          |archRootSlope w zj - archRootSlope w z₀| := by
    rw [hdetArch, abs_mul, abs_of_nonneg hprod0]
  have hvarj := hvariation j
  calc
    |(zj.2 : ℝ)| ≤ 256 * S.U ^ 2 * ((j.val : ℝ) * bstep) := by
      rw [hcoordAbs]
      exact mul_le_mul hprodUpper hvarj (abs_nonneg _) (by positivity)
    _ = 256 * (j.val : ℝ) * E := by
      dsimp [bstep]
      field_simp [ne_of_gt hU]
    _ = 256 * (j.val : ℝ) * (2 * B * (S.d₀ : ℝ) * S.Y) := by rfl

private lemma path_first_coordinate_bound {K : ℕ} (S : PDScale) (γ : EnvPath S.x K)
    (w : ArchRoot) (hw : w.InRegion S) (hU : 0 < S.U)
    (hboxes : ∀ j : Fin (pathLength S.x + 1), envBox S w (γ j).1) :
    ∀ j : Fin (pathLength S.x + 1),
      |((γ j).1.1 : ℝ)| ≤ 16 + |((γ j).1.2 : ℝ)| := by
  have hwRegion := hw
  rcases hw with ⟨_, _, _, _, hr₀, hr₁⟩
  intro j
  have htau := envBox_tau_bounds (K := K) S w (γ j).1 hwRegion hU (hboxes j)
  have htauAbs : |w.tau (γ j).1| ≤ 16 := by
    rw [abs_of_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 16) htau.1)]
    exact htau.2
  have hrAbs : |w.r| ≤ 1 := abs_le.mpr ⟨by linarith [hr₀], hr₁⟩
  have hidentity : ((γ j).1.1 : ℝ) =
      w.tau (γ j).1 - w.r * ((γ j).1.2 : ℝ) := by
    dsimp [ArchRoot.tau]
    ring
  calc
    |((γ j).1.1 : ℝ)| ≤ |w.tau (γ j).1| + |w.r * ((γ j).1.2 : ℝ)| := by
      rw [hidentity]
      calc
        |w.tau (γ j).1 - w.r * ((γ j).1.2 : ℝ)| =
            |w.tau (γ j).1 + -(w.r * ((γ j).1.2 : ℝ))| := by congr 1
        _ ≤ |w.tau (γ j).1| + |-(w.r * ((γ j).1.2 : ℝ))| := abs_add_le _ _
        _ = |w.tau (γ j).1| + |w.r * ((γ j).1.2 : ℝ)| := by rw [abs_neg]
    _ ≤ 16 + |((γ j).1.2 : ℝ)| := by
      rw [abs_mul]
      exact add_le_add htauAbs
        (calc
          |w.r| * |((γ j).1.2 : ℝ)| ≤ 1 * |((γ j).1.2 : ℝ)| :=
            mul_le_mul_of_nonneg_right hrAbs (abs_nonneg _)
          _ = |((γ j).1.2 : ℝ)| := by ring)

private lemma root_active_product_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hF : F.Valid)
    (hPath : IsEnvPathAdmissible F S γ) (hL : 1 ≤ S.L) :
    (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤
      Real.exp (16 * (K : ℝ) * Real.rpow S.L (72 / 100 : ℝ)) := by
  classical
  rcases hF.1 with ⟨_, hband, _⟩
  have hLpow : 1 ≤ Real.rpow S.L (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have hLpowJ : 1 ≤ Real.rpow S.L (1 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 100)
    simpa using h
  have hLpowPos : 0 < S.L := lt_of_lt_of_le zero_lt_one hL
  have hN : (pathLength S.x : ℝ) + 1 ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := by
    have hceil : (momentR S.x : ℝ) < Real.rpow S.L (1 / 2 : ℝ) / 2 + 1 := by
      dsimp [momentR]
      exact Nat.ceil_lt_add_one (by positivity)
    have hN' : 2 * (momentR S.x : ℝ) + 1 <
        Real.rpow S.L (1 / 2 : ℝ) + 3 := by nlinarith [hceil]
    have hN'' : Real.rpow S.L (1 / 2 : ℝ) + 3 ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) := by nlinarith [hLpow]
    have hN''' : 2 * (momentR S.x : ℝ) + 1 ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) := hN'.le.trans hN''
    simpa [pathLength] using hN'''
  have hM : (slotCount S.x : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) := by
    have hfloor : (momentJ S.x : ℝ) ≤ Real.rpow S.L (1 / 100 : ℝ) := by
      dsimp [momentJ]
      exact Nat.floor_le (by positivity)
    have hM' : (momentJ S.x : ℝ) + 1 ≤
        2 * Real.rpow S.L (1 / 100 : ℝ) := by nlinarith [hfloor, hLpowJ]
    simpa [slotCount] using hM'
  have hActivePrimeBound : ∀ p ∈ pathActivePrimes γ,
      (p : ℝ) ≤ Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by
    intro p hp
    have hrepr : ∃ j i jj, (γ j).2 i jj = p := by
      simpa [pathActivePrimes] using hp
    rcases hrepr with ⟨j, i, jj, rfl⟩
    have hValid := hPath.1 j
    have hPrimeBand := hValid.2.1 i jj
    have ha_i := hband i
    have hpow := Real.rpow_le_rpow_of_exponent_le hL ha_i.2.le
    have hbandUpper :
        ((γ j).2 i jj : ℝ) ≤ Real.exp (2 * Real.rpow S.L (F.a i)) :=
      (Finset.mem_filter.mp hPrimeBand.2).2.2.2
    have hpow2 := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2)
    exact hbandUpper.trans (Real.exp_le_exp.mpr hpow2)
  have hprod₀ := Finset.prod_le_prod₀
    (s := pathActivePrimes γ) (f := fun p : ℕ => (p : ℝ))
    (g := fun _ : ℕ => Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)))
    (by intro p hp; exact Nat.cast_nonneg p) hActivePrimeBound
  have hprod : (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤
      Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) ^ (pathActivePrimes γ).card := by
    calc
      (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤
          ∏ p ∈ pathActivePrimes γ, Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := hprod₀
      _ = Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) ^ (pathActivePrimes γ).card := by simp
  have hcardNat := pathActivePrimes_card_le γ
  have hcardReal :
      ((pathActivePrimes γ).card : ℝ) ≤
        ((pathLength S.x + 1) * K * slotCount S.x : ℕ) := by exact_mod_cast hcardNat
  have hcardReal' :
      ((pathActivePrimes γ).card : ℝ) ≤
        8 * (K : ℝ) * Real.rpow S.L (51 / 100 : ℝ) := by
    calc
      ((pathActivePrimes γ).card : ℝ) ≤
          ((pathLength S.x + 1) * K * slotCount S.x : ℕ) := hcardReal
      _ = ((pathLength S.x : ℝ) + 1) * (K : ℝ) * (slotCount S.x : ℝ) := by norm_num
      _ ≤ (4 * Real.rpow S.L (1 / 2 : ℝ)) * (K : ℝ) *
            (2 * Real.rpow S.L (1 / 100 : ℝ)) := by
              calc
                ((pathLength S.x : ℝ) + 1) * (K : ℝ) * (slotCount S.x : ℝ) =
                    ((pathLength S.x : ℝ) + 1) * ((K : ℝ) * (slotCount S.x : ℝ)) := by ring
                _ ≤ (4 * Real.rpow S.L (1 / 2 : ℝ)) *
                    ((K : ℝ) * (slotCount S.x : ℝ)) :=
                      mul_le_mul_of_nonneg_right hN (by positivity)
                _ = ((4 * Real.rpow S.L (1 / 2 : ℝ)) * (K : ℝ)) *
                      (slotCount S.x : ℝ) := by ring
                _ ≤ ((4 * Real.rpow S.L (1 / 2 : ℝ)) * (K : ℝ)) *
                      (2 * Real.rpow S.L (1 / 100 : ℝ)) :=
                        mul_le_mul_of_nonneg_left hM (by positivity)
                _ = (4 * Real.rpow S.L (1 / 2 : ℝ)) * (K : ℝ) *
                      (2 * Real.rpow S.L (1 / 100 : ℝ)) := by ring
      _ = 8 * (K : ℝ) * Real.rpow S.L (51 / 100 : ℝ) := by
            have hpowMul : Real.rpow S.L (1 / 2 : ℝ) *
                Real.rpow S.L (1 / 100 : ℝ) = Real.rpow S.L (51 / 100 : ℝ) := by
              calc
                Real.rpow S.L (1 / 2 : ℝ) * Real.rpow S.L (1 / 100 : ℝ) =
                    Real.rpow S.L ((1 / 2 : ℝ) + 1 / 100) :=
                  (Real.rpow_add hLpowPos (1 / 2 : ℝ) (1 / 100 : ℝ)).symm
                _ = Real.rpow S.L (51 / 100 : ℝ) := by congr 1 <;> norm_num
            calc
              (4 * Real.rpow S.L (1 / 2 : ℝ)) * (K : ℝ) *
                  (2 * Real.rpow S.L (1 / 100 : ℝ)) =
                8 * (K : ℝ) * (Real.rpow S.L (1 / 2 : ℝ) *
                  Real.rpow S.L (1 / 100 : ℝ)) := by ring
              _ = 8 * (K : ℝ) * Real.rpow S.L (51 / 100 : ℝ) := by rw [hpowMul]
  have hExpo :
      (2 * Real.rpow S.L (1 / 5 : ℝ)) * ((pathActivePrimes γ).card : ℝ) ≤
        16 * (K : ℝ) * Real.rpow S.L (72 / 100 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (71 / 100 : ℝ) ≤ 72 / 100)
    have hfactorNonneg : 0 ≤ 2 * Real.rpow S.L (1 / 5 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hLpowPos) _)
    calc
      (2 * Real.rpow S.L (1 / 5 : ℝ)) * ((pathActivePrimes γ).card : ℝ) ≤
        (2 * Real.rpow S.L (1 / 5 : ℝ)) *
            (8 * (K : ℝ) * Real.rpow S.L (51 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcardReal' hfactorNonneg
      _ = 16 * (K : ℝ) * Real.rpow S.L (71 / 100 : ℝ) := by
            have hpowMul : Real.rpow S.L (1 / 5 : ℝ) *
                Real.rpow S.L (51 / 100 : ℝ) = Real.rpow S.L (71 / 100 : ℝ) := by
              calc
                Real.rpow S.L (1 / 5 : ℝ) * Real.rpow S.L (51 / 100 : ℝ) =
                    Real.rpow S.L ((1 / 5 : ℝ) + 51 / 100) :=
                  (Real.rpow_add hLpowPos (1 / 5 : ℝ) (51 / 100 : ℝ)).symm
                _ = Real.rpow S.L (71 / 100 : ℝ) := by congr 1 <;> norm_num
            calc
              (2 * Real.rpow S.L (1 / 5 : ℝ)) *
                  (8 * (K : ℝ) * Real.rpow S.L (51 / 100 : ℝ)) =
                16 * (K : ℝ) * (Real.rpow S.L (1 / 5 : ℝ) *
                  Real.rpow S.L (51 / 100 : ℝ)) := by ring
              _ = 16 * (K : ℝ) * Real.rpow S.L (71 / 100 : ℝ) := by rw [hpowMul]
      _ ≤ 16 * (K : ℝ) * Real.rpow S.L (72 / 100 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg (by norm_num) (Nat.cast_nonneg K))
  calc
    (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤
        Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) ^ (pathActivePrimes γ).card := hprod
    _ = Real.exp ((2 * Real.rpow S.L (1 / 5 : ℝ)) * (pathActivePrimes γ).card) :=
          real_exp_pow_nat _ _
    _ ≤ Real.exp (16 * (K : ℝ) * Real.rpow S.L (72 / 100 : ℝ)) :=
          Real.exp_le_exp.mpr hExpo

private lemma pdScale_positive {K : ℕ} (S : PDScale) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hS : PDScale.Valid K δ c₁ c₂ S) :
    0 < S.Y ∧ 0 < S.U ∧ 1 ≤ S.d₀ := by
  rcases hS with ⟨hx, hHm, _, _, _, hY, hd₀⟩
  have hxpos : 0 < S.x := by linarith
  have hYpos : 0 < S.Y := by
    rcases Finset.mem_filter.mp hY with ⟨hmem, _⟩
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact pow_pos (by norm_num : (0 : ℝ) < 2) n
  have hd₀pos : 1 ≤ S.d₀ := by
    rcases Finset.mem_image.mp hd₀ with ⟨n, _, hn⟩
    rw [← hn]
    exact Nat.one_le_pow n 2 (by decide)
  have hHmpos : 0 < S.Hm := by
    exact (Real.rpow_pos_of_pos hxpos δ).trans_le hHm
  have hUpos : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hd₀pos)) hYpos) hHmpos
  exact ⟨hYpos, hUpos, hd₀pos⟩

private lemma contributing_coordinate_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (δ c₁ c₂ Bψ : ℝ) (hδ : 0 < δ) (hBψ : 0 ≤ Bψ)
    (hpsi : ∀ t, F.psi t ≠ 0 → |t| ≤ Bψ)
    (hS : S.Valid K δ c₁ c₂) :
    ∃ B : ℝ, B = 16 + 512 * (pathLength S.x : ℝ) *
        Bψ * (S.d₀ : ℝ) * S.Y ∧
      0 ≤ B ∧ ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
      ∀ j : Fin (pathLength S.x + 1),
        |((γ j).1.1 : ℝ)| ≤ B ∧ |((γ j).1.2 : ℝ)| ≤ B := by
  obtain ⟨hY, hU, _⟩ := pdScale_positive S δ c₁ c₂ hδ hS
  let B : ℝ := 16 + 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y
  have hB : 0 ≤ B := by
    dsimp [B]
    have hN : 0 ≤ (pathLength S.x : ℝ) := Nat.cast_nonneg _
    have hd : 0 ≤ (S.d₀ : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ 512 * (pathLength S.x : ℝ) := mul_nonneg (by norm_num) hN
    have h2 : 0 ≤ 512 * (pathLength S.x : ℝ) * Bψ := mul_nonneg h1 hBψ
    have h3 : 0 ≤ 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) :=
      mul_nonneg h2 hd
    exact add_nonneg (by norm_num) (mul_nonneg h3 hY.le)
  refine ⟨B, rfl, hB, ?_⟩
  intro γ hγ j
  rcases hγ with ⟨hPath, hcoef, w, hw, harch⟩
  have hboxes := pathArch_box_good F S w γ harch
  have hsecond := path_second_coordinate_bound F S γ w hPath hw hU harch hcoef
    Bψ hBψ hpsi hY j
  have hj : (j.val : ℝ) ≤ (pathLength S.x : ℝ) := by
    exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
  have hmult_nonneg : 0 ≤ 2 * Bψ * (S.d₀ : ℝ) * S.Y := by positivity
  have hsecond' : |((γ j).1.2 : ℝ)| ≤
      512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by
    calc
      |((γ j).1.2 : ℝ)| ≤
          256 * (j.val : ℝ) * (2 * Bψ * (S.d₀ : ℝ) * S.Y) := hsecond
      _ ≤ 256 * (pathLength S.x : ℝ) * (2 * Bψ * (S.d₀ : ℝ) * S.Y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by norm_num)) hmult_nonneg
      _ = 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by ring
  have hfirst := path_first_coordinate_bound S γ w hw hU (fun k => (hboxes k).1) j
  refine ⟨?_, ?_⟩
  · calc
      |((γ j).1.1 : ℝ)| ≤ 16 + |((γ j).1.2 : ℝ)| := hfirst
      _ ≤ B := by dsimp [B]; linarith
  · calc
      |((γ j).1.2 : ℝ)| ≤ 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := hsecond'
      _ ≤ B := by dsimp [B]; linarith

private lemma contributing_paths_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℝ) (hB : 0 ≤ B)
    (hcoords : ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
      ∀ j : Fin (pathLength S.x + 1),
        |((γ j).1.1 : ℝ)| ≤ B ∧ |((γ j).1.2 : ℝ)| ≤ B) :
    ∃ q : ℕ,
      (q : ℝ) ≤ B + 1 ∧
      {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite ∧
      ({γ : EnvPath S.x K | IsContributingPath F S γ}.ncard ≤
        ((2 * q + 1) ^ 2 *
          ((markedPrimes S.x K F.a).card ^ (slotCount S.x)) ^ K) ^
            (pathLength S.x + 1)) := by
  classical
  let q : ℕ := ⌊B⌋₊ + 1
  have hqReal : B < (q : ℝ) := by
    dsimp [q]
    have h := Nat.lt_floor_add_one B
    push_cast at h ⊢
    exact h
  have hcoord_mem (z : ℤ) (hz : |(z : ℝ)| ≤ B) : z ∈ Finset.Icc (-q : ℤ) q := by
    have hq : B ≤ (q : ℝ) := hqReal.le
    have hz' := abs_le.mp hz
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show -(q : ℝ) ≤ (z : ℝ) by linarith)
    · exact_mod_cast (show (z : ℝ) ≤ (q : ℝ) by linarith)
  let Labels : Type := {p : ℕ // p ∈ markedPrimes S.x K F.a}
  let Code : Type :=
    ((↥(Finset.Icc (-q : ℤ) q) × ↥(Finset.Icc (-q : ℤ) q)) ×
      (Fin K → Fin (slotCount S.x) → Labels))
  let encode : {γ : EnvPath S.x K // IsContributingPath F S γ} →
      (Fin (pathLength S.x + 1) → Code) := fun γ j =>
    let hc := hcoords γ.1 γ.2 j
    ((⟨(γ.1 j).1.1, hcoord_mem _ hc.1⟩,
      ⟨(γ.1 j).1.2, hcoord_mem _ hc.2⟩), fun i k =>
        ⟨(γ.1 j).2 i k, by
          have hEnv := γ.2.1.1 j
          have hBand := hEnv.2.1 i k
          have hmem : (γ.1 j).2 i k ∈ primeBand S.x (F.a i) := hBand.2
          change (γ.1 j).2 i k ∈ Finset.univ.biUnion (fun i => primeBand S.x (F.a i))
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩⟩)
  have hencode : Function.Injective encode := by
    intro γ γ' heq
    apply Subtype.ext
    funext j
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun f => ((f j).1.1).val) heq
      · exact congrArg (fun f => ((f j).1.2).val) heq
    · funext i k
      exact congrArg Subtype.val (congrArg (fun f => (f j).2 i k) heq)
  have hfinite : {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite :=
    Finite.of_injective encode hencode
  have hqle : (q : ℝ) ≤ B + 1 := by
    dsimp [q]
    have hfloor := Nat.floor_le hB
    push_cast
    linarith
  have hfiniteSubtype : Finite {γ : EnvPath S.x K // IsContributingPath F S γ} :=
    Finite.of_injective encode hencode
  letI : Finite {γ : EnvPath S.x K // IsContributingPath F S γ} := hfiniteSubtype
  letI : Fintype {γ : EnvPath S.x K // IsContributingPath F S γ} := Fintype.ofFinite _
  letI : Fintype ↑({γ : EnvPath S.x K | IsContributingPath F S γ}) := hfinite.fintype
  have hIcc : (Finset.Icc (- (q : ℤ)) (q : ℤ)).card = 2 * q + 1 := by
    have hz := Int.card_Icc_of_le (a := -(q : ℤ)) (b := (q : ℤ)) (by omega)
    have hz' : ((Finset.Icc (- (q : ℤ)) (q : ℤ)).card : ℤ) =
        ((2 * q + 1 : ℕ) : ℤ) := by
      rw [hz]
      push_cast
      omega
    exact_mod_cast hz'
  have hCodeCard : Fintype.card Code =
      (2 * q + 1) ^ 2 *
        ((markedPrimes S.x K F.a).card ^ (slotCount S.x)) ^ K := by
    simp only [Code, Labels, Fintype.card_prod, Fintype.card_pi_const,
      Fintype.card_fin, Fintype.card_coe, hIcc]
    ring_nf
  have hcard := Fintype.card_le_of_injective encode hencode
  have hcardCode : Fintype.card (Fin (pathLength S.x + 1) → Code) =
      Fintype.card Code ^ (pathLength S.x + 1) := by simp [Fintype.card_fun]
  have hcardSet :
      {γ : EnvPath S.x K | IsContributingPath F S γ}.ncard =
        Fintype.card {γ : EnvPath S.x K // IsContributingPath F S γ} := by
    exact (Set.fintypeCard_eq_ncard (s := {γ : EnvPath S.x K | IsContributingPath F S γ})).symm
  refine ⟨q, hqle, hfinite, ?_⟩
  rw [hcardSet]
  calc
    Fintype.card {γ : EnvPath S.x K // IsContributingPath F S γ} ≤
        Fintype.card (Fin (pathLength S.x + 1) → Code) := hcard
    _ = Fintype.card Code ^ (pathLength S.x + 1) := hcardCode
    _ = ((2 * q + 1) ^ 2 *
          ((markedPrimes S.x K F.a).card ^ (slotCount S.x)) ^ K) ^
            (pathLength S.x + 1) := by rw [hCodeCard]

private lemma pdfix_cutoff_abs_bounds {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ Eη Eψ : ℝ, 1 ≤ Eη ∧ 1 ≤ Eψ ∧
      (∀ t, |F.eta t| ≤ Eη) ∧ (∀ t, |F.psi t| ≤ Eψ) := by
  rcases hF with ⟨_, _, _, _, heta, hpsi⟩
  rcases heta with ⟨hetaCont, hetaSupport, _, _⟩
  rcases hpsi with ⟨hpsiCont, hpsiSupport, _⟩
  have hetaBounded : BddAbove (|F.eta| '' Set.Icc (1 : ℝ) 4) :=
    isCompact_Icc.bddAbove_image (continuous_abs.comp hetaCont.continuous).continuousOn
  obtain ⟨Bη, hBη⟩ := hetaBounded
  obtain ⟨Bψ, hBψ⟩ := hpsiCont.continuous.bounded_above_of_compact_support hpsiSupport
  let Eη : ℝ := max 1 Bη
  let Eψ : ℝ := max 1 Bψ
  refine ⟨Eη, Eψ, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Set.Icc (1 : ℝ) 4
    · exact (hBη ⟨t, ht, rfl⟩).trans (le_max_right _ _)
    · have hzero : F.eta t = 0 := by
        by_contra hne
        have hsupp : t ∈ Function.support F.eta := by
          simpa [Function.mem_support] using hne
        exact ht (hetaSupport hsupp)
      simp [hzero, Eη]
  · intro t
    calc
      |F.psi t| = ‖F.psi t‖ := (Real.norm_eq_abs _).symm
      _ ≤ Bψ := hBψ t
      _ ≤ Eψ := le_max_right _ _

private lemma additiveCharacter_norm_one (t : ℝ) : ‖additiveCharacter t‖ = 1 := by
  unfold additiveCharacter
  have harg : Complex.I * (2 * Real.pi * t) = (2 * Real.pi * t : ℝ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

private lemma majorKernel_norm_le_psi (x Y A₀ t : ℝ) (a b : ℕ) (psi : ℝ → ℝ) :
    ‖majorKernel x Y A₀ t a b psi‖ ≤ |psi (t / Y)| := by
  have hpoint : ∀ θ ∈ Set.uIoc (0 : ℝ) 1,
      ‖if majorArc x Y A₀ θ then additiveCharacter (θ * (t - (b : ℝ) + (a : ℝ))) else 0‖ ≤ 1 := by
    intro θ hθ
    by_cases h : majorArc x Y A₀ θ
    · simp [h, additiveCharacter_norm_one]
    · simp [h]
  have hintegral :
      ‖∫ θ in (0 : ℝ)..1,
        if majorArc x Y A₀ θ then additiveCharacter (θ * (t - (b : ℝ) + (a : ℝ))) else 0‖ ≤ 1 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    simpa using h
  unfold majorKernel
  rw [norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |psi (t / Y)| *
        ‖∫ θ in (0 : ℝ)..1,
          if majorArc x Y A₀ θ then additiveCharacter (θ * (t - (b : ℝ) + (a : ℝ))) else 0‖
        ≤ |psi (t / Y)| * 1 :=
      mul_le_mul_of_nonneg_left hintegral (abs_nonneg _)
    _ = |psi (t / Y)| := by ring

private lemma rawMultiplier_norm_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (Eη Eψ : ℝ)
    (hη : ∀ r, |F.eta r| ≤ Eη) (hψ : ∀ r, |F.psi r| ≤ Eψ)
    (hr₀ : 0 ≤ (S.d₀ : ℝ) / (D : ℝ)) (hr₁ : (S.d₀ : ℝ) / (D : ℝ) ≤ 1) :
    ‖rawMultiplier F S D aa bb t‖ ≤ Eη ^ 2 * Eψ := by
  have hEη : 0 ≤ Eη := le_trans (abs_nonneg _) (hη 0)
  have hEψ : 0 ≤ Eψ := le_trans (abs_nonneg _) (hψ 0)
  by_cases hdet : t = (bb : ℤ) - aa
  · subst t
    simp [rawMultiplier, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr₀]
    have hηb := hη ((bb : ℝ) / S.Y)
    have hηa := hη ((aa : ℝ) / S.Y)
    have hψt := hψ (((bb : ℝ) - aa) / S.Y)
    calc
      (S.d₀ : ℝ) / (D : ℝ) * |F.eta ((bb : ℝ) / S.Y)| *
          |F.eta ((aa : ℝ) / S.Y)| * |F.psi (((bb : ℝ) - aa) / S.Y)| ≤
        1 * Eη * Eη * Eψ := by
          gcongr
      _ = Eη ^ 2 * Eψ := by ring
  · simp [rawMultiplier, hdet]
    positivity

private lemma comparisonMultiplier_norm_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (D aa bb : ℕ) (t : ℤ) (Eη Eψ : ℝ)
    (hη : ∀ r, |F.eta r| ≤ Eη) (hψ : ∀ r, |F.psi r| ≤ Eψ)
    (hr₀ : 0 ≤ (S.d₀ : ℝ) / (D : ℝ)) (hr₁ : (S.d₀ : ℝ) / (D : ℝ) ≤ 1) :
    ‖comparisonMultiplier F S D aa bb t‖ ≤ Eη ^ 2 * Eψ := by
  have hmaj := majorKernel_norm_le_psi S.x S.Y F.A₀ (t : ℝ) aa bb F.psi
  unfold comparisonMultiplier
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hr₀]
  have hηb := hη ((bb : ℝ) / S.Y)
  have hηa := hη ((aa : ℝ) / S.Y)
  have hψt := hψ ((t : ℝ) / S.Y)
  have hEη : 0 ≤ Eη := le_trans (abs_nonneg _) hηb
  have hEψ : 0 ≤ Eψ := le_trans (abs_nonneg _) hψt
  calc
    (S.d₀ : ℝ) / (D : ℝ) * |F.eta ((bb : ℝ) / S.Y)| *
        |F.eta ((aa : ℝ) / S.Y)| *
        ‖majorKernel S.x S.Y F.A₀ (t : ℝ) aa bb F.psi‖ ≤
      1 * Eη * Eη * Eψ := by
        gcongr
        exact le_trans hmaj hψt
    _ = Eη ^ 2 * Eψ := by ring

private lemma bandMass_lower_eventually {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass x (F.a i) := by
  rcases hF with ⟨hbands, _, _, _, _, _⟩
  rcases hbands with ⟨hK, ha, _⟩
  have hband : ∀ i : Fin K, ∃ xi : ℝ, 2 ≤ xi ∧
      ∀ x : ℝ, xi ≤ x → (Real.log 2) / 2 ≤ bandMass x (F.a i) := by
    intro i
    have hai := ha i
    have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨xi, hxi, hmass⟩ := band_mass (F.a i)
      (by linarith [hai.1]) (by linarith [hai.2]) ((Real.log 2) / 2) (by positivity)
    refine ⟨xi, hxi, ?_⟩
    intro x hx
    have habs := (hmass x hx).1
    have hlow := (abs_le.mp habs).1
    linarith
  choose X hX using hband
  let x₀ : ℝ := ∑ i : Fin K, X i
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_of_lt hK)
  have hx₀ : 2 ≤ x₀ := by
    have hsum : (∑ i : Fin K, (2 : ℝ)) ≤ ∑ i : Fin K, X i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hX i).1
    have hsum' : (K : ℝ) * 2 ≤ x₀ := by
      dsimp [x₀]
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
    nlinarith [hsum', hKreal]
  have hXi (i : Fin K) : X i ≤ x₀ := by
    dsimp [x₀]
    exact Finset.single_le_sum (fun j hj => le_trans (by norm_num) (hX j).1)
      (Finset.mem_univ i)
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx i
  exact (hX i).2 x (le_trans (hXi i) hx)

private lemma physicalMeasure_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (hMass : ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass S.x (F.a i)) :
    let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
    0 ≤ physicalMeasure S.x K F.a ∧
      physicalMeasure S.x K F.a ≤ b ^ (K * slotCount S.x) := by
  classical
  let v₀ : ℝ := (Real.log 2) / 2
  let b : ℝ := max 1 (v₀⁻¹)
  have hv₀ : 0 < v₀ := by
    dsimp [v₀]
    positivity
  have hM : (0 : ℝ) ≤ (slotCount S.x : ℝ) := Nat.cast_nonneg _
  have hExp : -(slotCount S.x : ℝ) ≤ 0 := by linarith
  have hfactor (i : Fin K) :
      0 ≤ Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) ∧
      Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) ≤ b ^ slotCount S.x := by
    have hmass := hMass i
    have hmassPos : 0 < bandMass S.x (F.a i) := hv₀.trans_le hmass
    have hmono := Real.rpow_le_rpow_of_nonpos hv₀ hmass hExp
    have hv₀pow :
        Real.rpow v₀ (-(slotCount S.x : ℝ)) = (v₀⁻¹) ^ slotCount S.x := by
      calc
        Real.rpow v₀ (-(slotCount S.x : ℝ)) = Real.rpow (v₀⁻¹) (slotCount S.x : ℝ) :=
          Real.rpow_neg_eq_inv_rpow v₀ (slotCount S.x : ℝ)
        _ = (v₀⁻¹) ^ slotCount S.x := Real.rpow_natCast _ _
    have hpow : (v₀⁻¹) ^ slotCount S.x ≤ b ^ slotCount S.x := by
      apply pow_le_pow_left₀
      · positivity
      · exact le_max_right _ _
    constructor
    · exact (Real.rpow_pos_of_pos hmassPos _).le
    · calc
        Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) ≤
            Real.rpow v₀ (-(slotCount S.x : ℝ)) := hmono
        _ = (v₀⁻¹) ^ slotCount S.x := hv₀pow
        _ ≤ b ^ slotCount S.x := hpow
  have hprodNonneg :
      0 ≤ ∏ i : Fin K, Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) :=
    Finset.prod_nonneg fun i hi => (hfactor i).1
  have hprodBound :
      (∏ i : Fin K, Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ))) ≤
        ∏ i : Fin K, b ^ slotCount S.x := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (hfactor i).1
    · intro i hi
      exact (hfactor i).2
  have hconst : (∏ i : Fin K, b ^ slotCount S.x) = b ^ (K * slotCount S.x) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul]
    congr 1
    ring
  change 0 ≤ ∏ i : Fin K, Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) ∧
      ∏ i : Fin K, Real.rpow (bandMass S.x (F.a i)) (-(slotCount S.x : ℝ)) ≤
        b ^ (K * slotCount S.x)
  exact ⟨hprodNonneg, hprodBound.trans_eq hconst⟩

private lemma slotKernel_norm_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (p q : PrimeLists S.x K) (dt : ℤ) (Eη Eψ W : ℝ)
    (hη : ∀ r, |F.eta r| ≤ Eη) (hψ : ∀ r, |F.psi r| ≤ Eψ)
    (hweight :
      0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ∧
      ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ≤ W)
    (hd₀ : 0 < (S.d₀ : ℝ)) (hW : 0 ≤ W) :
    ‖slotKernel F S p q dt‖ ≤ W * (2 * Eη ^ 2 * Eψ) := by
  have hEη : 0 ≤ Eη := le_trans (abs_nonneg _) (hη 0)
  have hEψ : 0 ≤ Eψ := le_trans (abs_nonneg _) (hψ 0)
  have hC : 0 ≤ 2 * Eη ^ 2 * Eψ := by positivity
  by_cases hcond : IsSlotTransition p q ∧ IsPadAdmissible S.d₀ (sharedProduct p) dt
  · rcases hcond.2 with ⟨hD₀, hD₁, hdiv⟩
    have hDpos : 0 < (sharedProduct p : ℝ) := lt_of_lt_of_le hd₀ hD₀
    have hr₀ : 0 ≤ (S.d₀ : ℝ) / (sharedProduct p : ℝ) := div_nonneg hd₀.le hDpos.le
    have hr₁ : (S.d₀ : ℝ) / (sharedProduct p : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hDpos).2
      simpa using hD₀
    have hraw := rawMultiplier_norm_bound F S (sharedProduct p) (lastProduct q)
      (lastProduct p) (dt / (sharedProduct p : ℤ)) Eη Eψ hη hψ hr₀ hr₁
    have hcomp := comparisonMultiplier_norm_bound F S (sharedProduct p) (lastProduct q)
      (lastProduct p) (dt / (sharedProduct p : ℤ)) Eη Eψ hη hψ hr₀ hr₁
    have hgeo : ‖geometricMultiplier F S (sharedProduct p) (lastProduct q)
        (lastProduct p) (dt / (sharedProduct p : ℤ))‖ ≤ 2 * Eη ^ 2 * Eψ := by
      unfold geometricMultiplier
      calc
        ‖rawMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
            (dt / (sharedProduct p : ℤ)) -
          comparisonMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
            (dt / (sharedProduct p : ℤ))‖ ≤
          ‖rawMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
              (dt / (sharedProduct p : ℤ))‖ +
            ‖comparisonMultiplier F S (sharedProduct p) (lastProduct q) (lastProduct p)
              (dt / (sharedProduct p : ℤ))‖ := norm_sub_le _ _
        _ ≤ Eη ^ 2 * Eψ + Eη ^ 2 * Eψ := add_le_add hraw hcomp
        _ = 2 * Eη ^ 2 * Eψ := by ring
    rw [slotKernel, if_pos hcond, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hweight.1]
    exact mul_le_mul hweight.2 hgeo (norm_nonneg _) hW
  · simp [slotKernel, hcond]
    positivity

private lemma symKernel_norm_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℝ) (hB : 0 ≤ B)
    (hslot : ∀ p q dt, ‖slotKernel F S p q dt‖ ≤ B)
    (forward : Bool) (s s' : EnvPoint S.x K) :
    ‖symKernel F S forward s s'‖ ≤ B := by
  classical
  let Perms := Fin K → Equiv.Perm (Fin (slotCount S.x))
  have hcount : 0 < permCount S.x K := by
    unfold permCount
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ => Equiv.refl _⟩
  let P : ℝ := permCount S.x K
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast hcount
  let term (σ σ' : Perms) : ℂ :=
    if forward then
      slotKernel F S (permuteLists σ s.2) (permuteLists σ' s'.2) (det2 s.1 s'.1)
    else
      star (slotKernel F S (permuteLists σ' s'.2) (permuteLists σ s.2)
        (det2 s'.1 s.1))
  have hterm (σ σ' : Perms) : ‖term σ σ'‖ ≤ B := by
    by_cases hf : forward
    · simp [term, hf]
      exact hslot _ _ _
    · simp [term, hf]
      exact hslot _ _ _
  have hinner (σ : Perms) :
      ‖∑ σ' : Perms, term σ σ'‖ ≤ P * B := by
    calc
      ‖∑ σ' : Perms, term σ σ'‖ ≤ ∑ σ' : Perms, ‖term σ σ'‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ σ' : Perms, B := Finset.sum_le_sum fun σ' hσ' => hterm σ σ'
      _ = P * B := by simp [P, permCount, Perms]
  have hdouble :
      ‖∑ σ : Perms, ∑ σ' : Perms, term σ σ'‖ ≤ P ^ 2 * B := by
    calc
      ‖∑ σ : Perms, ∑ σ' : Perms, term σ σ'‖ ≤
          ∑ σ : Perms, ‖∑ σ' : Perms, term σ σ'‖ := norm_sum_le Finset.univ _
      _ ≤ ∑ σ : Perms, P * B := Finset.sum_le_sum fun σ hσ => hinner σ
      _ = P ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_univ, show Fintype.card Perms = permCount S.x K by
          rfl]
        simp [P]
        ring
  have hcoef : ‖((permCount S.x K : ℂ)⁻¹) ^ 2‖ = (P ^ 2)⁻¹ := by
    simp [P, norm_pow, norm_inv]
  unfold symKernel
  rw [norm_mul, hcoef]
  calc
    (P ^ 2)⁻¹ * ‖∑ σ : Perms, ∑ σ' : Perms, term σ σ'‖ ≤
        (P ^ 2)⁻¹ * (P ^ 2 * B) :=
      mul_le_mul_of_nonneg_left hdouble (by positivity)
    _ = B := by
      have hP2 : P ^ 2 ≠ 0 := (sq_pos_of_pos hP).ne'
      field_simp [hP2]

private lemma inverseBandProduct_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (hMass : ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass S.x (F.a i)) :
    let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
    0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ∧
      ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ≤ b ^ K := by
  classical
  let v₀ : ℝ := (Real.log 2) / 2
  let b : ℝ := max 1 (v₀⁻¹)
  have hv₀ : 0 < v₀ := by dsimp [v₀]; positivity
  have hfactor (i : Fin K) :
      0 ≤ (bandMass S.x (F.a i))⁻¹ ∧ (bandMass S.x (F.a i))⁻¹ ≤ b := by
    have hm := hMass i
    have hmpos := hv₀.trans_le hm
    have hinv : (bandMass S.x (F.a i))⁻¹ ≤ v₀⁻¹ := by
      have h := one_div_le_one_div_of_le hv₀ hm
      simpa [one_div] using h
    exact ⟨inv_nonneg.mpr hmpos.le, hinv.trans (le_max_right _ _)⟩
  have hprod0 : 0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ :=
    Finset.prod_nonneg fun i hi => (hfactor i).1
  have hprod1 :
      (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) ≤ ∏ i : Fin K, b := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (hfactor i).1
    · intro i hi
      exact (hfactor i).2
  have hconst : (∏ i : Fin K, b) = b ^ K := by simp
  change 0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ∧
    ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ≤ b ^ K
  exact ⟨hprod0, hprod1.trans_eq hconst⟩

private lemma pathCoefficient_norm_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (Eη Eψ : ℝ)
    (hη : ∀ r, |F.eta r| ≤ Eη) (hψ : ∀ r, |F.psi r| ≤ Eψ)
    (hMass : ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass S.x (F.a i))
    (hd₀ : 0 < (S.d₀ : ℝ)) :
    let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
    ‖pathCoefficient F S γ‖ ≤
      b ^ (K * slotCount S.x) * (b ^ K * (2 * Eη ^ 2 * Eψ)) ^ pathLength S.x := by
  classical
  let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
  let W : ℝ := b ^ K
  let Bslot : ℝ := W * (2 * Eη ^ 2 * Eψ)
  have hMassBound := physicalMeasure_bound F S hMass
  have hμ₀ : 0 ≤ physicalMeasure S.x K F.a := hMassBound.1
  have hμ₁ : physicalMeasure S.x K F.a ≤ b ^ (K * slotCount S.x) := by
    simpa [b] using hMassBound.2
  have hweight0 :
      0 ≤ ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ :=
    (inverseBandProduct_bound F S hMass).1
  have hweight1 :
      (∏ i : Fin K, (bandMass S.x (F.a i))⁻¹) ≤ W := by
    simpa [W, b] using (inverseBandProduct_bound F S hMass).2
  have hWnonneg : 0 ≤ W := by dsimp [W, b]; positivity
  have hslot : ∀ p q dt, ‖slotKernel F S p q dt‖ ≤ Bslot := by
    intro p q dt
    have h := slotKernel_norm_bound F S p q dt Eη Eψ W hη hψ
      ⟨hweight0, hweight1⟩ hd₀ hWnonneg
    simpa [Bslot] using h
  have hEη : 0 ≤ Eη := le_trans (abs_nonneg _) (hη 0)
  have hEψ : 0 ≤ Eψ := le_trans (abs_nonneg _) (hψ 0)
  have hBslot : 0 ≤ Bslot := by
    dsimp [Bslot, W, b]
    positivity
  have hsym : ∀ j : Fin (pathLength S.x),
      ‖symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)‖ ≤ Bslot := by
    intro j
    exact symKernel_norm_bound F S Bslot hBslot hslot _ _ _
  have hkernelProd :
      ‖∏ j : Fin (pathLength S.x),
        symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)‖ ≤
        Bslot ^ pathLength S.x := by
    rw [norm_prod]
    calc
      ∏ j : Fin (pathLength S.x),
          ‖symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)‖ ≤
        ∏ j : Fin (pathLength S.x), Bslot :=
          Finset.prod_le_prod₀ (fun j hj => norm_nonneg _) (fun j hj => hsym j)
      _ = Bslot ^ pathLength S.x := by simp
  unfold pathCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hμ₀]
  calc
    physicalMeasure S.x K F.a *
        ‖∏ j : Fin (pathLength S.x),
          symKernel F S (decide (j.val % 2 = 0)) (γ j.castSucc) (γ j.succ)‖ ≤
      b ^ (K * slotCount S.x) * Bslot ^ pathLength S.x :=
        mul_le_mul hμ₁ hkernelProd (norm_nonneg _) (by positivity)
    _ = b ^ (K * slotCount S.x) *
        (b ^ K * (2 * Eη ^ 2 * Eψ)) ^ pathLength S.x := by rfl

private lemma budget_scale_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (δ c₁ c₂ : ℝ) (hF : F.Valid) (hS : PDScale.Valid K δ c₁ c₂ S)
    (hL : 1 ≤ S.L) :
    (pathLength S.x : ℝ) + 1 ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) ∧
    (slotCount S.x : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) ∧
    (S.d₀ : ℝ) ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) ∧
    S.Y ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) ∧
    (markedPrimes S.x K F.a).card ≤
      ⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ + 1 := by
  classical
  rcases hS with ⟨hx, hHm, hHn, hlow, hupp, hYmem, hd₀mem⟩
  rcases hF.1 with ⟨_, ha, _⟩
  have hLpos : 0 < S.L := lt_of_lt_of_le zero_lt_one hL
  have hLpow : 1 ≤ Real.rpow S.L (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have hLpowJ : 1 ≤ Real.rpow S.L (1 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (0 : ℝ) ≤ 1 / 100)
    simpa using h
  have hN : (pathLength S.x : ℝ) + 1 ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := by
    have hceil : (momentR S.x : ℝ) < Real.rpow S.L (1 / 2 : ℝ) / 2 + 1 := by
      dsimp [momentR]
      exact Nat.ceil_lt_add_one (by positivity)
    have hN' : 2 * (momentR S.x : ℝ) + 1 < Real.rpow S.L (1 / 2 : ℝ) + 3 := by
      nlinarith [hceil]
    have hN'' : Real.rpow S.L (1 / 2 : ℝ) + 3 ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) := by nlinarith [hLpow]
    have hN''' : 2 * (momentR S.x : ℝ) + 1 ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) := hN'.le.trans hN''
    simpa [pathLength] using hN'''
  have hM : (slotCount S.x : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) := by
    have hfloor : (momentJ S.x : ℝ) ≤ Real.rpow S.L (1 / 100 : ℝ) := by
      dsimp [momentJ]
      exact Nat.floor_le (by positivity)
    have hM' : (momentJ S.x : ℝ) + 1 ≤
        2 * Real.rpow S.L (1 / 100 : ℝ) := by nlinarith [hfloor, hLpowJ]
    simpa [slotCount] using hM'
  have hpowexp (n : ℕ) :
      (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by rw [pow_succ]
          _ = Real.exp ((n : ℝ) * Real.log 2) * Real.exp (Real.log 2) := by
                rw [ih, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp ((n : ℝ) * Real.log 2 + Real.log 2) := by rw [← Real.exp_add]
          _ = Real.exp (((n + 1 : ℕ) : ℝ) * Real.log 2) := by
                congr 1
                push_cast
                ring
  have hd₀ : (S.d₀ : ℝ) ≤
      Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
    rcases Finset.mem_image.mp hd₀mem with ⟨k, hk, hEq⟩
    have hk' : k ≤ ⌊((K + 1 : ℕ) : ℝ) *
        Real.rpow S.L (21 / 100 : ℝ)⌋₊ :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hfloor := Nat.floor_le (show 0 ≤
        ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ) by
          exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hLpos.le _))
    have hkReal : (k : ℝ) ≤
        ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ) := by
      exact (Nat.cast_le.mpr hk').trans hfloor
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hklog : (k : ℝ) * Real.log 2 ≤
        ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ) := by
      calc
        (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2le (Nat.cast_nonneg k)
        _ ≤ ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ) := by simpa using hkReal
    calc
      (S.d₀ : ℝ) = (2 : ℝ) ^ k := by exact_mod_cast hEq.symm
      _ = Real.exp ((k : ℝ) * Real.log 2) := hpowexp k
      _ ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) :=
        Real.exp_le_exp.mpr hklog
  have hY : S.Y ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) := by
    rcases Finset.mem_filter.mp hYmem with ⟨hbase, hspec⟩
    rcases Finset.mem_image.mp hbase with ⟨n, _, hEq⟩
    have hYpos : 0 < S.Y := by rw [← hEq]; positivity
    calc
      S.Y = Real.exp (Real.log S.Y) := (Real.exp_log hYpos).symm
      _ ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) :=
        Real.exp_le_exp.mpr hspec.2
  have hPrimeBound : ∀ p ∈ markedPrimes S.x K F.a,
      (p : ℝ) ≤ Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨i, _, hbandmem⟩
    have hband := (Finset.mem_filter.mp hbandmem).2.2.2
    have hai := ha i
    have hpow := Real.rpow_le_rpow_of_exponent_le hL hai.2.le
    exact hband.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hPrimesSubset : markedPrimes S.x K F.a ⊆
      Finset.range (⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ + 1) := by
    intro p hp
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le <|
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (hPrimeBound p hp)
  refine ⟨hN, hM, hd₀, hY, ?_⟩
  calc
    (markedPrimes S.x K F.a).card ≤
        (Finset.range (⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ + 1)).card :=
      Finset.card_le_card hPrimesSubset
    _ = ⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ + 1 := by simp

private lemma budget_path_q_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (δ c₁ c₂ Bψ : ℝ) (hδ : 0 < δ) (hBψ : 0 ≤ Bψ) (hF : F.Valid)
    (hS : PDScale.Valid K δ c₁ c₂ S) (hL : 1 ≤ S.L)
    (q : ℕ) (hq : (q : ℝ) ≤
      17 + 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y) :
    (2 * q + 1 : ℝ) ≤
      Real.exp ((2 * ((K + 1 : ℕ) : ℝ) + 6 + 3 * (20 + 2048 * Bψ)) *
        Real.rpow S.L (23 / 100 : ℝ)) := by
  have hscale := budget_scale_bounds F S δ c₁ c₂ hF hS hL
  rcases hscale with ⟨hN, _, hd₀, hY, _⟩
  have hLpos : 0 < S.L := lt_of_lt_of_le zero_lt_one hL
  have hp21 : Real.rpow S.L (21 / 100 : ℝ) ≤ Real.rpow S.L (23 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hY21 : S.Y ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (1 / 5 : ℝ) ≤ 21 / 100)
    exact hY.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)))
  let A : ℝ := ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hroots : 1 ≤ Real.rpow S.L (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa using h
  have hd₀nonneg : 0 ≤ (S.d₀ : ℝ) := Nat.cast_nonneg _
  have hYnonneg : 0 ≤ S.Y := le_of_lt (pdScale_positive S δ c₁ c₂ hδ hS).1
  have hdyadprod :
      (S.d₀ : ℝ) * S.Y ≤ Real.exp A * Real.exp A :=
    mul_le_mul hd₀ hY21 hYnonneg (Real.exp_pos A).le
  have hdyadprod' : (S.d₀ : ℝ) * S.Y ≤ Real.exp (2 * A) := by
    calc
      (S.d₀ : ℝ) * S.Y ≤ Real.exp A * Real.exp A := hdyadprod
      _ = Real.exp (2 * A) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hNcast : (pathLength S.x : ℝ) ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := by linarith [hN]
  have htube :
      (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * Real.exp (2 * A) := by
    calc
      (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y ≤
          4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by
            have hNB : (pathLength S.x : ℝ) * Bψ ≤
                4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ :=
              mul_le_mul_of_nonneg_right hNcast hBψ
            calc
              (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y =
                  ((pathLength S.x : ℝ) * Bψ) * ((S.d₀ : ℝ) * S.Y) := by ring
              _ ≤ (4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ) * ((S.d₀ : ℝ) * S.Y) :=
                mul_le_mul_of_nonneg_right hNB (mul_nonneg hd₀nonneg hYnonneg)
              _ = 4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by ring
      _ ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ *
            (Real.exp A * Real.exp A) := by
              have hleft : 0 ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ := by positivity
              calc
                4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y =
                    (4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ) *
                      ((S.d₀ : ℝ) * S.Y) := by ring
                _ ≤ (4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ) *
                      (Real.exp A * Real.exp A) :=
                    mul_le_mul_of_nonneg_left hdyadprod hleft
      _ = 4 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * Real.exp (2 * A) := by
            rw [← Real.exp_add]
            congr 3 <;> ring
  have hlarge : 1 ≤ Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) := by
    have hexp : 1 ≤ Real.exp (2 * A) := by
      exact Real.one_le_exp_iff.mpr (by positivity)
    nlinarith [mul_le_mul hroots hexp (by norm_num) (by positivity)]
  have hq' : (2 * q + 1 : ℝ) ≤
      3 * (20 + 2048 * Bψ) * Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) := by
    have hq' : (2 * q + 1 : ℝ) ≤
        35 + 1024 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by
      have hqcast := hq
      push_cast at hqcast
      nlinarith
    calc
      (2 * q + 1 : ℝ) ≤
          35 + 1024 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := hq'
      _ ≤ 35 + 4096 * Real.rpow S.L (1 / 2 : ℝ) * Bψ * Real.exp (2 * A) := by
            nlinarith [htube]
      _ ≤ 3 * (20 + 2048 * Bψ) * Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) := by
            have hZnonneg : 0 ≤ Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) := by positivity
            have hBz : 0 ≤ Bψ *
                (Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A)) :=
              mul_nonneg hBψ hZnonneg
            nlinarith [hlarge, hBz]
  have hlogL : Real.log S.L ≤ 5 * Real.rpow S.L (23 / 100 : ℝ) := by
    have hpowpos := Real.rpow_pos_of_pos hLpos (23 / 100 : ℝ)
    have hlogpow := Real.log_le_sub_one_of_pos hpowpos
    rw [Real.log_rpow hLpos (23 / 100 : ℝ)] at hlogpow
    have hlogBound : Real.log S.L ≤ (100 / 23 : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by
      have hmul : (23 / 100 : ℝ) * Real.log S.L ≤
          Real.rpow S.L (23 / 100 : ℝ) :=
        hlogpow.trans (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1))
      have hmul' : Real.log S.L * (23 / 100 : ℝ) ≤
          Real.rpow S.L (23 / 100 : ℝ) := by simpa [mul_comm] using hmul
      have hdiv := (le_div_iff₀ (by norm_num : (0 : ℝ) < 23 / 100)).2 hmul'
      have heq : Real.rpow S.L (23 / 100 : ℝ) / (23 / 100 : ℝ) =
          (100 / 23 : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by field_simp
      rw [heq] at hdiv
      exact hdiv
    exact hlogBound.trans (mul_le_mul_of_nonneg_right
      (by norm_num : (100 / 23 : ℝ) ≤ 5) (Real.rpow_nonneg (le_of_lt hLpos) _))
  have hrootExp : Real.rpow S.L (1 / 2 : ℝ) ≤
      Real.exp (3 * Real.rpow S.L (23 / 100 : ℝ)) := by
    apply (Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hLpos (1 / 2 : ℝ))).mp
    rw [Real.log_rpow hLpos (1 / 2 : ℝ)]
    have hpowpos : 0 < Real.rpow S.L (23 / 100 : ℝ) :=
      Real.rpow_pos_of_pos hLpos _
    have hhalf : (1 / 2 : ℝ) * Real.log S.L ≤
        (5 / 2 : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by
      calc
        (1 / 2 : ℝ) * Real.log S.L ≤ (1 / 2 : ℝ) *
            (5 * Real.rpow S.L (23 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogL (by norm_num)
        _ = (5 / 2 : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by ring
    nlinarith [hhalf, hpowpos]
  let C₀ : ℝ := 3 * (20 + 2048 * Bψ)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₀exp : C₀ ≤ Real.exp (C₀ * Real.rpow S.L (23 / 100 : ℝ)) := by
    have h₁ : C₀ ≤ Real.exp C₀ := by
      have h := Real.add_one_le_exp C₀
      linarith
    have hpow : 1 ≤ Real.rpow S.L (23 / 100 : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 23 / 100)
      simpa using h
    exact h₁.trans (Real.exp_le_exp.mpr (by nlinarith [hC₀, hpow]))
  have hfinal :
      C₀ * Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) ≤
        Real.exp ((C₀ + 3 + 2 * ((K + 1 : ℕ) : ℝ)) *
          Real.rpow S.L (23 / 100 : ℝ)) := by
    calc
      C₀ * Real.rpow S.L (1 / 2 : ℝ) * Real.exp (2 * A) ≤
          Real.exp (C₀ * Real.rpow S.L (23 / 100 : ℝ)) *
            Real.exp (3 * Real.rpow S.L (23 / 100 : ℝ)) * Real.exp (2 * A) := by
              have hprod : C₀ * Real.rpow S.L (1 / 2 : ℝ) ≤
                  Real.exp (C₀ * Real.rpow S.L (23 / 100 : ℝ)) *
                    Real.exp (3 * Real.rpow S.L (23 / 100 : ℝ)) := by
                exact mul_le_mul hC₀exp hrootExp (Real.rpow_nonneg (le_of_lt hLpos) _) 
                  (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
      _ = Real.exp (C₀ * Real.rpow S.L (23 / 100 : ℝ) +
            3 * Real.rpow S.L (23 / 100 : ℝ) + 2 * A) := by
              rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((C₀ + 3 + 2 * ((K + 1 : ℕ) : ℝ)) *
            Real.rpow S.L (23 / 100 : ℝ)) := by
              apply Real.exp_le_exp.mpr
              dsimp [A]
              have hKpos : 0 ≤ ((K + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
              have hpowterm : 2 * ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ) ≤
                  2 * ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (23 / 100 : ℝ) :=
                mul_le_mul_of_nonneg_left hp21 (by positivity)
              calc
                C₀ * Real.rpow S.L (23 / 100 : ℝ) +
                    3 * Real.rpow S.L (23 / 100 : ℝ) +
                    2 * (((K + 1 : ℕ) : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) ≤
                  C₀ * Real.rpow S.L (23 / 100 : ℝ) +
                    3 * Real.rpow S.L (23 / 100 : ℝ) +
                    2 * ((K + 1 : ℕ) : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by
                      nlinarith [hpowterm]
                _ = (C₀ + 3 + 2 * ((K + 1 : ℕ) : ℝ)) *
                    Real.rpow S.L (23 / 100 : ℝ) := by ring
  have hcoeff : C₀ + 3 + 2 * ((K + 1 : ℕ) : ℝ) ≤
      2 * ((K + 1 : ℕ) : ℝ) + 6 + 3 * (20 + 2048 * Bψ) := by
    dsimp [C₀]
    ring_nf
    norm_num
  exact hq'.trans (hfinal.trans (Real.exp_le_exp.mpr (by
    exact mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (le_of_lt hLpos) _))))

private lemma contributing_path_exp_count {K : ℕ} (F : PDFix K) (S : PDScale)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hF : F.Valid)
    (hS : PDScale.Valid K δ c₁ c₂ S) (hL : 1 ≤ S.L)
    (Bψ : ℝ) (hBψ : 0 ≤ Bψ) (hpsi : ∀ t, F.psi t ≠ 0 → |t| ≤ Bψ) :
    {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite ∧
      ({γ : EnvPath S.x K | IsContributingPath F S γ}.ncard : ℝ) ≤
        Real.exp ((4 * (2 * (2 * ((K + 1 : ℕ) : ℝ) + 6 +
          3 * (20 + 2048 * Bψ)) + 6 * (K : ℝ))) *
          Real.rpow S.L (73 / 100 : ℝ)) := by
  classical
  obtain ⟨B, hBeq, hB, hcoords⟩ :=
    contributing_coordinate_bound F S δ c₁ c₂ Bψ hδ hBψ hpsi hS
  obtain ⟨q, hqle, hfinite, hcard⟩ := contributing_paths_finite F S B hB hcoords
  have hq : (q : ℝ) ≤
      17 + 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by
    calc
      (q : ℝ) ≤ B + 1 := hqle
      _ = 17 + 512 * (pathLength S.x : ℝ) * Bψ * (S.d₀ : ℝ) * S.Y := by
        rw [hBeq]
        ring
  have hscale := budget_scale_bounds F S δ c₁ c₂ hF hS hL
  rcases hscale with ⟨hN, hM, _, _, hPcard⟩
  have hLpos : 0 < S.L := lt_of_lt_of_le zero_lt_one hL
  have hqBound := budget_path_q_bound F S δ c₁ c₂ Bψ hδ hBψ hF hS hL q hq
  let P := markedPrimes S.x K F.a
  let M := slotCount S.x
  have hu : 1 ≤ Real.rpow S.L (1 / 5 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (0 : ℝ) ≤ 1 / 5)
    simpa using h
  have hE : 1 ≤ Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hPcast : (P.card : ℝ) ≤ Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ)) := by
    have hfloor := Nat.floor_le (Real.exp_pos (2 * Real.rpow S.L (1 / 5 : ℝ))).le
    have hPnat : P.card ≤ ⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ + 1 := by
      exact hPcard
    have hsmall : (P.card : ℝ) ≤ 2 * Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by
      have hcast : (P.card : ℝ) ≤
          (⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ : ℝ) + 1 := by
        exact_mod_cast hPnat
      calc
        (P.card : ℝ) ≤
            (⌊Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ))⌋₊ : ℝ) + 1 := hcast
        _ ≤ Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) + 1 := by
              simpa [add_comm] using add_le_add_right hfloor 1
        _ ≤ 2 * Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) := by nlinarith [hE]
    have hExpu : 2 ≤ Real.exp (Real.rpow S.L (1 / 5 : ℝ)) := by
      have h := Real.add_one_le_exp (Real.rpow S.L (1 / 5 : ℝ))
      nlinarith [h, hu]
    have h2 : 2 * Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) ≤
        Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ)) := by
      calc
        2 * Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) ≤
            Real.exp (Real.rpow S.L (1 / 5 : ℝ)) *
              Real.exp (2 * Real.rpow S.L (1 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_right hExpu (Real.exp_pos _).le
        _ = Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ)) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
    exact hsmall.trans h2
  have hPM : (P.card : ℝ) ^ M ≤
      Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ)) := by
    have hMreal : (M : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) := by simpa [M] using hM
    have hbaseNonneg : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have hpow : (P.card : ℝ) ^ M ≤
        Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ)) ^ M :=
      pow_le_pow_left₀ hbaseNonneg hPcast M
    have hmul : Real.rpow S.L (1 / 5 : ℝ) * Real.rpow S.L (1 / 100 : ℝ) =
        Real.rpow S.L (21 / 100 : ℝ) := by
      calc
        Real.rpow S.L (1 / 5 : ℝ) * Real.rpow S.L (1 / 100 : ℝ) =
            Real.rpow S.L ((1 / 5 : ℝ) + 1 / 100) :=
          (Real.rpow_add hLpos (1 / 5 : ℝ) (1 / 100 : ℝ)).symm
        _ = Real.rpow S.L (21 / 100 : ℝ) := by congr 1 <;> norm_num
    calc
      (P.card : ℝ) ^ M ≤ Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ)) ^ M := hpow
      _ = Real.exp (3 * Real.rpow S.L (1 / 5 : ℝ) * (M : ℝ)) :=
        real_exp_pow_nat _ _
      _ ≤ Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hterm : 3 * Real.rpow S.L (1 / 5 : ℝ) * (M : ℝ) ≤
            6 * Real.rpow S.L (21 / 100 : ℝ) := by
          calc
            3 * Real.rpow S.L (1 / 5 : ℝ) * (M : ℝ) ≤
                3 * Real.rpow S.L (1 / 5 : ℝ) *
                  (2 * Real.rpow S.L (1 / 100 : ℝ)) := by gcongr
            _ = 6 * Real.rpow S.L (21 / 100 : ℝ) := by rw [← hmul]; ring
        exact hterm
  have hPMK : ((P.card : ℝ) ^ M) ^ K ≤
      Real.exp (6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
    have hbase : 0 ≤ (P.card : ℝ) ^ M := by positivity
    have hpow := pow_le_pow_left₀ hbase hPM K
    calc
      ((P.card : ℝ) ^ M) ^ K ≤
          (Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ))) ^ K := hpow
      _ = Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ) * (K : ℝ)) :=
        real_exp_pow_nat _ _
      _ = Real.exp (6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
        congr 1 <;> ring
  have hPMK23 : ((P.card : ℝ) ^ M) ^ K ≤
      Real.exp (6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (21 / 100 : ℝ) ≤ 23 / 100)
    have hscale : 0 ≤ 6 * (K : ℝ) := by positivity
    have hpowK : ((P.card : ℝ) ^ M) ^ K ≤
        Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ) * (K : ℝ)) := by
      have hbase : 0 ≤ (P.card : ℝ) ^ M := by positivity
      calc
        ((P.card : ℝ) ^ M) ^ K ≤
            (Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ))) ^ K :=
          pow_le_pow_left₀ hbase hPM K
        _ = Real.exp (6 * Real.rpow S.L (21 / 100 : ℝ) * (K : ℝ)) :=
          real_exp_pow_nat _ _
    have hscaled :
        6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ) ≤
          6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hpow hscale
    have hscaled' :
        6 * Real.rpow S.L (21 / 100 : ℝ) * (K : ℝ) ≤
          6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := by
      calc
        6 * Real.rpow S.L (21 / 100 : ℝ) * (K : ℝ) =
            6 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ) := by ring
        _ ≤ 6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ) := hscaled
    exact hpowK.trans (Real.exp_le_exp.mpr hscaled')
  let Cq : ℝ := 2 * ((K + 1 : ℕ) : ℝ) + 6 + 3 * (20 + 2048 * Bψ)
  let Cpath : ℝ := 4 * (2 * Cq + 6 * (K : ℝ))
  have hCode :
      ((2 * q + 1 : ℕ) ^ 2 * (P.card ^ M) ^ K : ℝ) ≤
        Real.exp ((2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ)) := by
    have hqpow : (2 * (q : ℝ) + 1) ^ 2 ≤
        Real.exp (2 * Cq * Real.rpow S.L (23 / 100 : ℝ)) := by
      calc
        (2 * (q : ℝ) + 1) ^ 2 ≤
            Real.exp (Cq * Real.rpow S.L (23 / 100 : ℝ)) ^ 2 := by
              gcongr
        _ = Real.exp (2 * Cq * Real.rpow S.L (23 / 100 : ℝ)) := by
              rw [pow_two, ← Real.exp_add]
              congr 1 <;> ring
    have hcodeCast :
        ((2 * q + 1 : ℕ) ^ 2 * (P.card ^ M) ^ K : ℝ) =
          (2 * (q : ℝ) + 1) ^ 2 * ((P.card : ℝ) ^ M) ^ K := by norm_cast
    rw [hcodeCast]
    have htotal :
      (2 * (q : ℝ) + 1) ^ 2 * ((P.card : ℝ) ^ M) ^ K ≤
          Real.exp (2 * Cq * Real.rpow S.L (23 / 100 : ℝ)) *
            Real.exp (6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ)) := by
      exact mul_le_mul hqpow hPMK23 (by positivity) (by positivity)
    calc
      (2 * (q : ℝ) + 1) ^ 2 * ((P.card : ℝ) ^ M) ^ K ≤
          Real.exp (2 * Cq * Real.rpow S.L (23 / 100 : ℝ)) *
            Real.exp (6 * (K : ℝ) * Real.rpow S.L (23 / 100 : ℝ)) := htotal
      _ = Real.exp ((2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ)) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
  have hCodeNonneg : 0 ≤ ((2 * q + 1 : ℕ) ^ 2 * (P.card ^ M) ^ K : ℝ) := by positivity
  have hcodePow :
      ((2 * q + 1 : ℕ) ^ 2 * (P.card ^ M) ^ K : ℝ) ^ (pathLength S.x + 1) ≤
        Real.exp ((2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ)) ^
          (pathLength S.x + 1) :=
    pow_le_pow_left₀ hCodeNonneg hCode (pathLength S.x + 1)
  have hL73 : Real.rpow S.L (23 / 100 : ℝ) * Real.rpow S.L (1 / 2 : ℝ) =
      Real.rpow S.L (73 / 100 : ℝ) := by
    calc
      Real.rpow S.L (23 / 100 : ℝ) * Real.rpow S.L (1 / 2 : ℝ) =
          Real.rpow S.L ((23 / 100 : ℝ) + 1 / 2) :=
        (Real.rpow_add hLpos (23 / 100 : ℝ) (1 / 2 : ℝ)).symm
      _ = Real.rpow S.L (73 / 100 : ℝ) := by congr 1 <;> norm_num
  have hcountExp :
      Real.exp ((2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ)) ^
          (pathLength S.x + 1) ≤ Real.exp (Cpath * Real.rpow S.L (73 / 100 : ℝ)) := by
    rw [real_exp_pow_nat]
    apply Real.exp_le_exp.mpr
    have hN' : ((pathLength S.x + 1 : ℕ) : ℝ) ≤
        4 * Real.rpow S.L (1 / 2 : ℝ) := by
      calc
        ((pathLength S.x + 1 : ℕ) : ℝ) = (pathLength S.x : ℝ) + 1 := by norm_num
        _ ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := hN
    have hfactor : 0 ≤ (2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ) := by
      dsimp [Cq]
      positivity
    calc
      (2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ) *
          ((pathLength S.x + 1 : ℕ) : ℝ) ≤
        (2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ) *
          (4 * Real.rpow S.L (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hN' hfactor
      _ = Cpath * Real.rpow S.L (73 / 100 : ℝ) := by
            dsimp [Cpath]
            calc
              (2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (23 / 100 : ℝ) *
                  (4 * Real.rpow S.L (1 / 2 : ℝ)) =
                4 * (2 * Cq + 6 * (K : ℝ)) *
                  (Real.rpow S.L (23 / 100 : ℝ) * Real.rpow S.L (1 / 2 : ℝ)) := by ring
              _ = 4 * (2 * Cq + 6 * (K : ℝ)) * Real.rpow S.L (73 / 100 : ℝ) :=
                congrArg (fun x : ℝ => 4 * (2 * Cq + 6 * (K : ℝ)) * x) hL73
  have hcardReal :
      ({γ : EnvPath S.x K | IsContributingPath F S γ}.ncard : ℝ) ≤
        ((2 * q + 1 : ℕ) ^ 2 * (P.card ^ M) ^ K : ℝ) ^ (pathLength S.x + 1) := by
    exact_mod_cast hcard
  exact ⟨hfinite, hcardReal.trans (hcodePow.trans hcountExp)⟩

private lemma pathCoefficient_exp_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (δ c₁ c₂ Eη Eψ : ℝ) (hδ : 0 < δ)
    (hF : F.Valid) (hS : PDScale.Valid K δ c₁ c₂ S) (hL : 1 ≤ S.L)
    (hEη : 1 ≤ Eη) (hEψ : 1 ≤ Eψ)
    (hη : ∀ t, |F.eta t| ≤ Eη) (hψ : ∀ t, |F.psi t| ≤ Eψ)
    (hMass : ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass S.x (F.a i)) :
    let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
    let Bslot : ℝ := b ^ K * (2 * Eη ^ 2 * Eψ)
    ‖pathCoefficient F S γ‖ ≤
      Real.exp ((2 * (K : ℝ) * Real.log b + 4 * Real.log Bslot) *
        Real.rpow S.L (73 / 100 : ℝ)) := by
  classical
  let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
  let Bslot : ℝ := b ^ K * (2 * Eη ^ 2 * Eψ)
  have hb : 1 ≤ b := le_max_left _ _
  have hBslot : 1 ≤ Bslot := by
    dsimp [Bslot]
    have hbase : 1 ≤ 2 * Eη ^ 2 * Eψ := by nlinarith [hEη, hEψ]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hb) hbase
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hBslotpos : 0 < Bslot := lt_of_lt_of_le zero_lt_one hBslot
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlogSlot : 0 ≤ Real.log Bslot := Real.log_nonneg hBslot
  have hscale := budget_scale_bounds F S δ c₁ c₂ hF hS hL
  rcases hscale with ⟨hN, hM, _, _, _⟩
  have hNbound : (pathLength S.x : ℝ) ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := by
    linarith [hN]
  have hKM : (K * slotCount S.x : ℝ) ≤
      2 * (K : ℝ) * Real.rpow S.L (1 / 100 : ℝ) := by
    change (K : ℝ) * (slotCount S.x : ℝ) ≤ _
    calc
      (K : ℝ) * (slotCount S.x : ℝ) ≤
          (K : ℝ) * (2 * Real.rpow S.L (1 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg K)
      _ = 2 * (K : ℝ) * Real.rpow S.L (1 / 100 : ℝ) := by ring
  have hKMcoeff : 0 ≤ 2 * (K : ℝ) * Real.log b := by positivity
  have hNcoeff : 0 ≤ 4 * Real.log Bslot := by positivity
  have hKMBound :
      Real.log b * (K * slotCount S.x : ℝ) ≤
        2 * (K : ℝ) * Real.log b * Real.rpow S.L (73 / 100 : ℝ) := by
    have hLpow : Real.rpow S.L (1 / 100 : ℝ) ≤ Real.rpow S.L (73 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    calc
      Real.log b * (K * slotCount S.x : ℝ) ≤
          Real.log b * (2 * (K : ℝ) * Real.rpow S.L (1 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hKM hlogb
      _ = 2 * (K : ℝ) * Real.log b * Real.rpow S.L (1 / 100 : ℝ) := by ring
      _ ≤ 2 * (K : ℝ) * Real.log b * Real.rpow S.L (73 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hLpow hKMcoeff
  have hNBound :
      Real.log Bslot * (pathLength S.x : ℝ) ≤
        4 * Real.log Bslot * Real.rpow S.L (73 / 100 : ℝ) := by
    have hLpow : Real.rpow S.L (1 / 2 : ℝ) ≤ Real.rpow S.L (73 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    calc
      Real.log Bslot * (pathLength S.x : ℝ) ≤
          Real.log Bslot * (4 * Real.rpow S.L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hNbound hlogSlot
      _ = 4 * Real.log Bslot * Real.rpow S.L (1 / 2 : ℝ) := by ring
      _ ≤ 4 * Real.log Bslot * Real.rpow S.L (73 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hLpow hNcoeff
  have hscalePos := pdScale_positive S δ c₁ c₂ hδ hS
  have hd₀Nat : 0 < S.d₀ := lt_of_lt_of_le Nat.zero_lt_one hscalePos.2.2
  have hd₀Real : 0 < (S.d₀ : ℝ) := by exact_mod_cast hd₀Nat
  have hcoeffBound := pathCoefficient_norm_bound F S γ Eη Eψ hη hψ hMass hd₀Real
  have hcoeffBound' :
      ‖pathCoefficient F S γ‖ ≤ b ^ (K * slotCount S.x) * Bslot ^ pathLength S.x := by
    simpa [b, Bslot] using hcoeffBound
  have hbPower : b ^ (K * slotCount S.x) =
      Real.exp (Real.log b * (K * slotCount S.x : ℝ)) := by
    have hbEq : b = Real.exp (Real.log b) := (Real.exp_log hbpos).symm
    calc
      b ^ (K * slotCount S.x) = (Real.exp (Real.log b)) ^ (K * slotCount S.x) :=
        congrArg (fun x : ℝ => x ^ (K * slotCount S.x)) hbEq
      _ = Real.exp (Real.log b * (K * slotCount S.x : ℝ)) := by
        simpa [Nat.cast_mul] using (real_exp_pow_nat (Real.log b) (K * slotCount S.x))
  have hslotPower : Bslot ^ pathLength S.x =
      Real.exp (Real.log Bslot * (pathLength S.x : ℝ)) := by
    have hBslotEq : Bslot = Real.exp (Real.log Bslot) := (Real.exp_log hBslotpos).symm
    calc
      Bslot ^ pathLength S.x = (Real.exp (Real.log Bslot)) ^ pathLength S.x :=
        congrArg (fun x : ℝ => x ^ pathLength S.x) hBslotEq
      _ = Real.exp (Real.log Bslot * (pathLength S.x : ℝ)) := real_exp_pow_nat _ _
  calc
    ‖pathCoefficient F S γ‖ ≤ b ^ (K * slotCount S.x) * Bslot ^ pathLength S.x := hcoeffBound'
    _ = Real.exp (Real.log b * (K * slotCount S.x : ℝ)) *
          Real.exp (Real.log Bslot * (pathLength S.x : ℝ)) := by rw [hbPower, hslotPower]
    _ = Real.exp (Real.log b * (K * slotCount S.x : ℝ) +
          Real.log Bslot * (pathLength S.x : ℝ)) := by rw [← Real.exp_add]
    _ ≤ Real.exp ((2 * (K : ℝ) * Real.log b + 4 * Real.log Bslot) *
          Real.rpow S.L (73 / 100 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hKMBound, hNBound]

/-- `t2:pd.root-budget` (new node) — PD 03:631-641, 645-652, 667-672.  Budgets of the path
expansion: finitely many contributing paths with `Σ|coefficient| ≤ exp(C L^{0.73})`; on each, the
active primes have product `≤ exp(C L^{0.72})`, and the expected inactive excess
`Σ_{p inactive} E[1 - factor_p] ≤ C (N+1)` (it is `≤ Σ_p Σ_j η'_j/(p+1)`). -/
theorem root_budget (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ Cb x₀ : ℝ, 0 < Cb ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite ∧
        (∑' γ : EnvPath S.x K, if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) ≤
          Real.exp (Cb * Real.rpow S.L (73 / 100 : ℝ)) ∧
        ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
          (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤ Real.exp (Cb * Real.rpow S.L (72 / 100 : ℝ)) ∧
          (∑ p ∈ (markedPrimes S.x K F.a).filter (fun p => p ∉ pathActivePrimes γ),
            ((p : ℝ) + 1)⁻¹ * ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam)) ≤
            Cb * ((S.N : ℝ) + 1) := by
  classical
  intro K F hF
  obtain ⟨Eη, Eψ, hEη, hEψ, hEta, hPsi⟩ := pdfix_cutoff_abs_bounds F hF
  obtain ⟨Bψ, hBψ, hpsi⟩ := pdfix_psi_abs_bound F hF
  obtain ⟨xBand, hxBand, hBand⟩ := bandMass_lower_eventually F hF
  obtain ⟨Bmass, xMass, hBmass, hxMass, hRecipMass⟩ :=
    marked_reciprocal_mass_bound F.a hF.1
  have hF' : F.Valid := hF
  rcases hF with ⟨hBands, hqd, hqdlt, _, _, _⟩
  let b : ℝ := max 1 (((Real.log 2) / 2)⁻¹)
  let Bslot : ℝ := b ^ K * (2 * Eη ^ 2 * Eψ)
  let Cpaths : ℝ := 4 *
    (2 * (2 * ((K + 1 : ℕ) : ℝ) + 6 + 3 * (20 + 2048 * Bψ)) + 6 * (K : ℝ))
  let Ccoef : ℝ := 2 * (K : ℝ) * Real.log b + 4 * Real.log Bslot
  let Cb : ℝ := max 1 (max (Cpaths + Ccoef) (max (16 * (K : ℝ)) Bmass))
  let x₀ : ℝ := max xBand (max xMass (Real.exp 1))
  have hx₀ : 2 ≤ x₀ := le_trans hxBand (le_max_left _ _)
  have hxBand₀ : xBand ≤ x₀ := le_max_left _ _
  have hxMass₀ : xMass ≤ x₀ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hexp₀ : Real.exp 1 ≤ x₀ :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hCb : 0 < Cb := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Cb, x₀, hCb, hx₀, ?_⟩
  intro S hS hx
  have hL : 1 ≤ S.L := by
    apply (Real.le_log_iff_exp_le (by linarith [hS.1] : 0 < S.x)).2
    exact le_trans hexp₀ hx
  have hMass : ∀ i : Fin K, (Real.log 2) / 2 ≤ bandMass S.x (F.a i) :=
    hBand S.x (le_trans hxBand₀ hx)
  have hRecip :
      (∑ p ∈ markedPrimes S.x K F.a, ((p : ℝ) + 1)⁻¹) ≤ Bmass :=
    hRecipMass S.x (le_trans hxMass₀ hx)
  have hScalePos := pdScale_positive S δ c₁ c₂ hδ hS
  have hd₀Nat : 0 < S.d₀ := lt_of_lt_of_le Nat.zero_lt_one hScalePos.2.2
  have hd₀Real : 0 < (S.d₀ : ℝ) := by exact_mod_cast hd₀Nat
  have hcount0 := contributing_path_exp_count F S δ c₁ c₂ hδ hF' hS hL Bψ hBψ hpsi
  have hcount :
      ({γ : EnvPath S.x K | IsContributingPath F S γ}.ncard : ℝ) ≤
        Real.exp (Cpaths * Real.rpow S.L (73 / 100 : ℝ)) := by
    simpa [Cpaths] using hcount0.2
  let T := hcount0.1.toFinset
  have hTcard : (T.card : ℝ) ≤ Real.exp (Cpaths * Real.rpow S.L (73 / 100 : ℝ)) := by
    have hEq := Set.ncard_eq_toFinset_card
      {γ : EnvPath S.x K | IsContributingPath F S γ} hcount0.1
    simpa [T, hEq] using hcount
  have hCoeff (γ : EnvPath S.x K) :
      ‖pathCoefficient F S γ‖ ≤ Real.exp (Ccoef * Real.rpow S.L (73 / 100 : ℝ)) := by
    have h := pathCoefficient_exp_bound F S γ δ c₁ c₂ Eη Eψ hδ hF' hS hL
      hEη hEψ hEta hPsi hMass
    simpa [b, Bslot, Ccoef] using h
  have htsum :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) =
        ∑ γ ∈ T, if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    have hnot : ¬ IsContributingPath F S γ := by
      intro hc
      exact hγ ((Set.Finite.mem_toFinset hcount0.1).2 hc)
    simp [hnot]
  have hsumSimplify :
      (∑ γ ∈ T, if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) =
        ∑ γ ∈ T, ‖pathCoefficient F S γ‖ := by
    apply Finset.sum_congr rfl
    intro γ hγ
    have hc : IsContributingPath F S γ := by
      simpa only [Set.mem_setOf_eq] using (Set.Finite.mem_toFinset hcount0.1).1 hγ
    simp [hc]
  have hMassSum :
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) ≤
        Real.exp (Cb * Real.rpow S.L (73 / 100 : ℝ)) := by
    have hCbpath : Cpaths + Ccoef ≤ Cb := by
      dsimp [Cb]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hsumPath :
        (∑ γ ∈ T, ‖pathCoefficient F S γ‖) ≤
          ∑ γ ∈ T, Real.exp (Ccoef * Real.rpow S.L (73 / 100 : ℝ)) := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact hCoeff γ
    calc
      (∑' γ : EnvPath S.x K,
        if IsContributingPath F S γ then ‖pathCoefficient F S γ‖ else 0) =
          ∑ γ ∈ T, ‖pathCoefficient F S γ‖ := htsum.trans hsumSimplify
      _ ≤ ∑ γ ∈ T, Real.exp (Ccoef * Real.rpow S.L (73 / 100 : ℝ)) := hsumPath
      _ = (T.card : ℝ) * Real.exp (Ccoef * Real.rpow S.L (73 / 100 : ℝ)) := by simp
      _ ≤ Real.exp (Cpaths * Real.rpow S.L (73 / 100 : ℝ)) *
            Real.exp (Ccoef * Real.rpow S.L (73 / 100 : ℝ)) :=
          mul_le_mul_of_nonneg_right hTcard (Real.exp_pos _).le
      _ = Real.exp ((Cpaths + Ccoef) * Real.rpow S.L (73 / 100 : ℝ)) := by
            rw [← Real.exp_add]
            congr 1 <;> ring
      _ ≤ Real.exp (Cb * Real.rpow S.L (73 / 100 : ℝ)) :=
          Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right hCbpath
              (Real.rpow_nonneg (by linarith [hL]) _))
  have hCbActive : 16 * (K : ℝ) ≤ Cb := by
    dsimp [Cb]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCbMass : Bmass ≤ Cb := by
    dsimp [Cb]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨hcount0.1, hMassSum, ?_⟩
  intro γ hγ
  constructor
  · have hActive := root_active_product_bound F S γ hF' hγ.1 hL
    have hpow : Real.rpow S.L (72 / 100 : ℝ) ≤ Real.rpow S.L (73 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    calc
      (∏ p ∈ pathActivePrimes γ, (p : ℝ)) ≤
          Real.exp (16 * (K : ℝ) * Real.rpow S.L (72 / 100 : ℝ)) := hActive
      _ ≤ Real.exp (Cb * Real.rpow S.L (72 / 100 : ℝ)) :=
          Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right hCbActive
              (Real.rpow_nonneg (by linarith [hL]) _))
  · have hInactive := root_inactive_total_excess_le F S γ hqd hqdlt Bmass
      (le_of_lt hBmass) hRecip
    calc
      (∑ p ∈ (markedPrimes S.x K F.a).filter (fun p => p ∉ pathActivePrimes γ),
        ((p : ℝ) + 1)⁻¹ *
          ∑ lam : Fin (p + 1), (1 - pathPrimeFactor F S γ p lam)) ≤
        Bmass * ((S.N : ℝ) + 1) := hInactive
      _ ≤ Cb * ((S.N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hCbMass (by positivity)

private lemma constant_exp_bound (c W : ℝ) (hc : 0 ≤ c) (hW : 1 ≤ W) :
    c ≤ Real.exp ((c + 1) * W) := by
  have hm := mul_le_mul_of_nonneg_left hW (by linarith : 0 ≤ c + 1)
  linarith [Real.add_one_le_exp ((c + 1) * W)]

private lemma sum_exp_bound (a b A B W : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 1 ≤ W)
    (ha : a ≤ Real.exp (A * W)) (hb : b ≤ Real.exp (B * W)) :
    a + b ≤ Real.exp ((A + B + 2) * W) := by
  have hW0 : 0 ≤ W := by linarith
  have htopA : Real.exp (A * W) ≤ Real.exp ((A + B) * W) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have htopB : Real.exp (B * W) ≤ Real.exp ((A + B) * W) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (2 : ℝ) ≤ Real.exp (2 * W) := by linarith [Real.add_one_le_exp (2 * W)]
  calc
    a + b ≤ 2 * Real.exp ((A + B) * W) := by linarith
    _ ≤ Real.exp (2 * W) * Real.exp ((A + B) * W) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring

private lemma ceil_exp_bound (a A W : ℝ) (ha0 : 0 ≤ a) (hA : 0 ≤ A) (hW : 1 ≤ W)
    (ha : a ≤ Real.exp (A * W)) :
    (⌈a⌉₊ : ℝ) ≤ Real.exp ((A + 2) * W) := by
  have hc : (⌈a⌉₊ : ℝ) ≤ a + 1 := (Nat.ceil_lt_add_one ha0).le
  have hs := sum_exp_bound a 1 A 0 W hA (by norm_num) hW ha (by simp)
  simpa using hc.trans hs

private lemma eventually_const_rpow_le (C a b : ℝ) (hab : a < b) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      C * Real.rpow L a ≤ Real.rpow L b := by
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)) C
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := by linarith
  have hpow := hB L ((le_max_right _ _).trans hL)
  calc
    C * Real.rpow L a ≤ Real.rpow L (b - a) * Real.rpow L a :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hLp.le _)
    _ = Real.rpow L ((b - a) + a) := (Real.rpow_add hLp (b - a) a).symm
    _ = Real.rpow L b := by congr 1 <;> ring

private lemma arch_parameter_exp_bound (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L D Y : ℝ, 1 ≤ L → 1 ≤ D → 1 ≤ Y →
      D ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow L (21 / 100 : ℝ)) →
      Y ≤ Real.exp (((K + 1 : ℕ) : ℝ) * Real.rpow L (1 / 5 : ℝ)) →
      let Z := Real.exp (Real.rpow L (1 / 2 : ℝ))
      let Q : ℕ := ⌈max 1 (max (2 * D * Real.rpow Y (1 / 5 : ℝ))
        (2 * D * Real.exp (4 * (K : ℝ) * Real.rpow L (1 / 5 : ℝ))))⌉₊
      let T : ℕ := ⌈204 * (Q : ℝ) * (Z + 1) + 101⌉₊
      500000000 * (Z + 1) ^ 2 +
        200 * (2 * ((K : ℝ) + 1) * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) ≤
          Real.exp (C * Real.rpow L (1 / 2 : ℝ)) := by
  let k : ℝ := (K : ℝ) + 1
  let CQ₀ := 6 * k + 4
  let CQ := CQ₀ + 2
  let CT := CQ + 314
  let CB := 2 * k + 1 + (CQ + 7) + (CT + 5)
  let C := 500000000 + CB + 210
  have hk : 1 ≤ k := by dsimp [k]; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hCQ₀ : 0 ≤ CQ₀ := by dsimp [CQ₀]; linarith
  have hCQ : 0 ≤ CQ := by dsimp [CQ]; linarith
  have hCT : 0 ≤ CT := by dsimp [CT]; linarith
  have hCB : 0 ≤ CB := by dsimp [CB]; linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro L D Y hL hD hY hDupper hYupper
  dsimp only
  let W := Real.rpow L (1 / 2 : ℝ)
  let Z := Real.exp W
  let q := max 1 (max (2 * D * Real.rpow Y (1 / 5 : ℝ))
    (2 * D * Real.exp (4 * (K : ℝ) * Real.rpow L (1 / 5 : ℝ))))
  let Q : ℕ := ⌈q⌉₊
  let t := 204 * (Q : ℝ) * (Z + 1) + 101
  let T : ℕ := ⌈t⌉₊
  change 500000000 * (Z + 1) ^ 2 +
    200 * (2 * k * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) ≤ Real.exp (C * W)
  have hW : 1 ≤ W := by
    simpa [W] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hW0 : 0 ≤ W := by linarith
  have h2 : (2 : ℝ) ≤ Real.exp (2 * W) := by linarith [Real.add_one_le_exp (2 * W)]
  have hDexp : D ≤ Real.exp (k * W) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (21 / 100 : ℝ) ≤ 1 / 2)
    apply hDupper.trans
    apply Real.exp_le_exp.mpr
    simpa [k, W] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ((K + 1 : ℕ) : ℝ))
  have hYexp : Y ≤ Real.exp (k * W) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2)
    apply hYupper.trans
    apply Real.exp_le_exp.mpr
    simpa [k, W] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ ((K + 1 : ℕ) : ℝ))
  have hYpow : Real.rpow Y (1 / 5 : ℝ) ≤ Y := by
    simpa using Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (1 / 5 : ℝ) ≤ 1)
  have htrial : Real.exp (4 * (K : ℝ) * Real.rpow L (1 / 5 : ℝ)) ≤
      Real.exp ((4 * (K : ℝ)) * W) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 5 : ℝ) ≤ 1 / 2))
      (by positivity)
  have h2D : 2 * D ≤ Real.exp (2 * W) * Real.exp (k * W) :=
    mul_le_mul h2 hDexp (by linarith) (Real.exp_pos _).le
  have ha1 : 2 * D * Real.rpow Y (1 / 5 : ℝ) ≤ Real.exp (CQ₀ * W) := by
    calc
      _ ≤ (Real.exp (2 * W) * Real.exp (k * W)) * Real.exp (k * W) :=
        mul_le_mul h2D (hYpow.trans hYexp) (Real.rpow_nonneg (by linarith) _)
          (by positivity)
      _ = Real.exp ((2 + 2 * k) * W) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [CQ₀]; nlinarith)
  have ha2 : 2 * D * Real.exp (4 * (K : ℝ) * Real.rpow L (1 / 5 : ℝ)) ≤
      Real.exp (CQ₀ * W) := by
    calc
      _ ≤ (Real.exp (2 * W) * Real.exp (k * W)) * Real.exp ((4 * (K : ℝ)) * W) :=
        mul_le_mul h2D htrial (Real.exp_pos _).le (by positivity)
      _ = Real.exp ((2 + k + 4 * (K : ℝ)) * W) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [CQ₀, k] at *; nlinarith)
  have hq : q ≤ Real.exp (CQ₀ * W) := by
    apply max_le
    · exact Real.one_le_exp (mul_nonneg hCQ₀ hW0)
    · exact max_le ha1 ha2
  have hQ : (Q : ℝ) ≤ Real.exp (CQ * W) :=
    ceil_exp_bound q CQ₀ W (by dsimp [q]; positivity) hCQ₀ hW hq
  have hZplus : Z + 1 ≤ Real.exp (3 * W) := by
    have hs := sum_exp_bound Z 1 1 0 W (by norm_num) (by norm_num) hW
      (by simp [Z]) (by simp)
    norm_num only at hs
    exact hs
  have htterm : 204 * (Q : ℝ) * (Z + 1) ≤ Real.exp ((CQ + 208) * W) := by
    have h204Q := mul_le_mul (constant_exp_bound 204 W (by norm_num) hW) hQ
      (Nat.cast_nonneg Q) (Real.exp_pos _).le
    norm_num only at h204Q
    calc
      _ ≤ (Real.exp (205 * W) * Real.exp (CQ * W)) * Real.exp (3 * W) :=
        mul_le_mul h204Q hZplus (by dsimp [Z]; positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> ring
  have ht : t ≤ Real.exp ((CQ + 312) * W) := by
    have h101 := constant_exp_bound 101 W (by norm_num) hW
    norm_num only at h101
    have hs := sum_exp_bound _ 101 (CQ + 208) 102 W (by linarith) (by norm_num) hW
      htterm h101
    convert hs using 1 <;> (try dsimp only [t]) <;> congr 1 <;> ring
  have hT : (T : ℝ) ≤ Real.exp (CT * W) := by
    have hc := ceil_exp_bound t (CQ + 312) W (by dsimp [t, Z]; positivity)
      (by linarith) hW ht
    convert hc using 1 <;> simp only [T, CT] <;> congr 1 <;> ring
  have h4Q : 4 * (Q : ℝ) ≤ Real.exp ((CQ + 5) * W) := by
    have hc := mul_le_mul (constant_exp_bound 4 W (by norm_num) hW) hQ
      (Nat.cast_nonneg Q) (Real.exp_pos _).le
    norm_num only at hc
    calc
      _ ≤ Real.exp (5 * W) * Real.exp (CQ * W) := hc
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  have h4Q1 : 4 * (Q : ℝ) + 1 ≤ Real.exp ((CQ + 7) * W) := by
    have hc := sum_exp_bound _ 1 (CQ + 5) 0 W (by linarith) (by norm_num) hW h4Q (by simp)
    convert hc using 1 <;> congr 1 <;> ring
  have h2T : 2 * (T : ℝ) ≤ Real.exp ((CT + 3) * W) := by
    have hc := mul_le_mul (constant_exp_bound 2 W (by norm_num) hW) hT
      (Nat.cast_nonneg T) (Real.exp_pos _).le
    norm_num only at hc
    calc
      _ ≤ Real.exp (3 * W) * Real.exp (CT * W) := hc
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  have h2T1 : 2 * (T : ℝ) + 1 ≤ Real.exp ((CT + 5) * W) := by
    have hc := sum_exp_bound _ 1 (CT + 3) 0 W (by linarith) (by norm_num) hW h2T (by simp)
    convert hc using 1 <;> congr 1 <;> ring
  have hBprod : 2 * k * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1) ≤ Real.exp (CB * W) := by
    have hc1 := mul_le_mul (constant_exp_bound (2 * k) W (by linarith) hW) h4Q1
      (by positivity : 0 ≤ 4 * (Q : ℝ) + 1) (Real.exp_pos _).le
    calc
      _ ≤ (Real.exp ((2 * k + 1) * W) * Real.exp ((CQ + 7) * W)) * Real.exp ((CT + 5) * W) :=
        mul_le_mul hc1 h2T1 (by positivity : 0 ≤ 2 * (T : ℝ) + 1) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> dsimp [CB] <;> ring
  have hZsq : (Z + 1) ^ 2 ≤ Real.exp (6 * W) := by
    have hp := pow_le_pow_left₀ (by dsimp [Z]; positivity : 0 ≤ Z + 1) hZplus 2
    calc
      _ ≤ Real.exp (3 * W) ^ 2 := hp
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1 <;> norm_num <;> ring
  have hFirst : 500000000 * (Z + 1) ^ 2 ≤ Real.exp (500000007 * W) := by
    have hc := mul_le_mul (constant_exp_bound 500000000 W (by norm_num) hW) hZsq
      (sq_nonneg _) (Real.exp_pos _).le
    norm_num only at hc
    calc
      _ ≤ Real.exp (500000001 * W) * Real.exp (6 * W) := hc
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  have hSecond : 200 * (2 * k * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) ≤
      Real.exp ((CB + 201) * W) := by
    have hc := mul_le_mul (constant_exp_bound 200 W (by norm_num) hW) hBprod
      (by positivity : 0 ≤ 2 * k * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) (Real.exp_pos _).le
    norm_num only at hc
    calc
      _ ≤ Real.exp (201 * W) * Real.exp (CB * W) := hc
      _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
  have hc := sum_exp_bound _ _ 500000007 (CB + 201) W (by norm_num) (by linarith) hW hFirst hSecond
  convert hc using 1 <;> simp only [C] <;> congr 1 <;> ring

/-- `t2:pd.root-arch-boundary` (new node) — PD 03:680-711.  For one visit with
`|z₁|,|z₂| ≤ exp(L^{1/2})` (the tube (det:tube) gives `|z| ≪ N d₀ Y = x^{o(1)}`), the
box-and-good indicator, as a function of `(u/U, v/V, r)`, is nonconstant on at most
`exp(L^{0.9}) x^{2ε}` cubes of the grid of side `x^{-ε}` (good tests change only at `exp(o(L))`
values of `r`; box faces have derivatives `exp(o(L))`, bounded below in the transversal variable). -/
theorem root_arch_boundary (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ s : EnvPoint S.x K, EnvValid F S s →
          |(s.1.1 : ℝ)| ≤ Real.exp (Real.rpow S.L (1 / 2 : ℝ)) →
          |(s.1.2 : ℝ)| ≤ Real.exp (Real.rpow S.L (1 / 2 : ℝ)) →
            (((gridIndices (Real.rpow S.x (-ε))).filter fun k =>
              IsNonconstantOn
                (fun y => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s.1 ∧
                  envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s)
                (gridCube (Real.rpow S.x (-ε)) k)).card : ℝ) ≤
              Real.exp (Real.rpow S.L (9 / 10 : ℝ)) * Real.rpow S.x (2 * ε) := by
  classical
  intro K F hF ε hε hε1
  obtain ⟨C, hC, hParameters⟩ := arch_parameter_exp_bound K
  obtain ⟨LC, hLC, hCgap⟩ := eventually_const_rpow_le C (1 / 2) (9 / 10) (by norm_num)
  obtain ⟨LE, hLE, hEgap⟩ := eventually_const_rpow_le (2 / ε) (1 / 2) 1 (by norm_num)
  let L₀ := max 1 (max LC (max LE (2 * Real.log 68 / ε)))
  let x₀ := max 2 (Real.exp L₀)
  refine ⟨x₀, le_max_left _ _, ?_⟩
  intro S hS hx s hs hz1 hz2
  have hxpos : 0 < S.x := by linarith [hS.1]
  have hL₀ : L₀ ≤ S.L :=
    (Real.le_log_iff_exp_le hxpos).2 ((le_max_right 2 (Real.exp L₀)).trans hx)
  have hL1 : 1 ≤ S.L := (le_max_left _ _).trans hL₀
  have hLCle : LC ≤ S.L :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hL₀
  have hLEle : LE ≤ S.L :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hL₀
  have h68le : 2 * Real.log 68 / ε ≤ S.L :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hL₀
  let W := Real.rpow S.L (1 / 2 : ℝ)
  let Z := Real.exp W
  let h := Real.rpow S.x (-ε)
  have hW1 : 1 ≤ W := by
    simpa [W] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hZ : 1 ≤ Z := Real.one_le_exp (by dsimp [W]; positivity)
  have hh : 0 < h := Real.rpow_pos_of_pos hxpos _
  have hgap : (2 / ε) * W ≤ S.L := by simpa [W] using hEgap S.L hLEle
  have hWsmall : W ≤ ε * S.L / 2 := by
    have hm := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ ε / 2)
    have he : (ε / 2) * (2 / ε) = 1 := by field_simp [hε.ne']
    rw [← mul_assoc, he, one_mul] at hm
    nlinarith
  have h68 : Real.log 68 ≤ ε * S.L / 2 := by
    have hm := (div_le_iff₀ hε).1 h68le
    nlinarith
  have hZh : Z * h ≤ 1 / 68 := by
    have he : Z * h = Real.exp (W - ε * S.L) := by
      dsimp [Z, h]
      rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
      congr 1
      dsimp [PDScale.L]
      ring
    rw [he]
    calc
      _ ≤ Real.exp (-Real.log 68) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 68 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 68)]; norm_num
  have hhsmall : h ≤ 1 / 8 := by
    have hm := mul_le_mul_of_nonneg_right hZ hh.le
    nlinarith
  have hscalePos := pdScale_positive S δ c₁ c₂ hδ hS
  have hY1 : 1 ≤ S.Y := by
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hS.2.2.2.2.2.1
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hm
    rw [← hn]
    exact one_le_pow₀ (by norm_num)
  have hD1 : (1 : ℝ) ≤ (S.d₀ : ℝ) := by exact_mod_cast hscalePos.2.2
  have hHm1 : 1 ≤ S.Hm :=
    (Real.one_le_rpow (by linarith [hS.1] : 1 ≤ S.x) hδ.le).trans hS.2.1
  have hV1 : 1 ≤ S.V :=
    (Real.one_le_rpow (by linarith [hS.1] : 1 ≤ S.x) hδ.le).trans hS.2.2.1
  have hH1 : 1 ≤ S.H := by
    have hm := mul_le_mul hD1 hY1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (S.d₀ : ℝ))
    simpa [PDScale.H] using hm
  have hU1 : 1 ≤ S.U := by
    have hm := mul_le_mul hH1 hHm1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ S.H)
    simpa [PDScale.U] using hm
  have hUV : 1 ≤ S.U * S.V := by
    have hm := mul_le_mul hU1 hV1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ S.U)
    simpa using hm
  let q := max 1 (max (2 * (S.d₀ : ℝ) * Real.rpow S.Y (1 / 5 : ℝ))
    (2 * (S.d₀ : ℝ) * Real.exp (4 * (K : ℝ) * Real.rpow S.L (1 / 5 : ℝ))))
  let Q : ℕ := ⌈q⌉₊
  let T : ℕ := ⌈204 * (Q : ℝ) * (Z + 1) + 101⌉₊
  have hqle : q ≤ (Q : ℝ) := Nat.le_ceil _
  have hQ1 : 2 * (S.d₀ : ℝ) * Real.rpow S.Y (1 / 5 : ℝ) ≤ (Q : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hqle
  have hQ2 : 2 * (S.d₀ : ℝ) * Real.exp (4 * (K : ℝ) * Real.rpow S.L (1 / 5 : ℝ)) ≤ (Q : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hqle
  have hT : 204 * (Q : ℝ) * (Z + 1) + 101 ≤ (T : ℝ) := Nat.le_ceil _
  obtain ⟨B, hBcard, hB⟩ := envGood_breakpoints F S hF s hs Z hZ hz1 hz2 hY1
    hscalePos.2.2 Q T hQ1 hQ2 hT hL1
  have hBreal : (B.card : ℝ) ≤
      2 * ((K : ℝ) + 1) * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1) := by exact_mod_cast hBcard
  have hscale := budget_scale_bounds F S δ c₁ c₂ hF hS hL1
  have hcoeffBound := hParameters S.L (S.d₀ : ℝ) S.Y hL1 hD1 hY1 hscale.2.2.1 hscale.2.2.2.1
  change 500000000 * (Z + 1) ^ 2 +
    200 * (2 * ((K : ℝ) + 1) * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) ≤
      Real.exp (C * W) at hcoeffBound
  have hcoeff : 500000000 * (Z + 1) ^ 2 + 200 * (B.card : ℝ) ≤ Real.exp (C * W) := by
    calc
      _ ≤ 500000000 * (Z + 1) ^ 2 +
          200 * (2 * ((K : ℝ) + 1) * (4 * (Q : ℝ) + 1) * (2 * (T : ℝ) + 1)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hBreal (by norm_num))
      _ ≤ _ := hcoeffBound
  have hGeom := arch_boundary_card_of_breakpoints F S hscalePos.2.1 (by linarith : 0 < S.V)
    hUV s Z h hZ hh hhsmall hz2 hZh B hB
  have hCpower : C * W ≤ Real.rpow S.L (9 / 10 : ℝ) := hCgap S.L hLCle
  have hpow : h ^ 2 = Real.rpow S.x (-(2 * ε)) := by
    calc
      h ^ 2 = Real.rpow (Real.rpow S.x (-ε)) (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow S.x ((-ε) * 2) := (Real.rpow_mul hxpos.le (-ε) 2).symm
      _ = _ := by congr 1 <;> ring
  have hinv : (h ^ 2)⁻¹ = Real.rpow S.x (2 * ε) := by
    rw [hpow]
    exact (congrArg (fun r : ℝ => r⁻¹) (Real.rpow_neg hxpos.le (2 * ε))).trans (inv_inv _)
  calc
    _ ≤ (500000000 * (Z + 1) ^ 2 + 200 * (B.card : ℝ)) / h ^ 2 := hGeom
    _ ≤ Real.exp (C * W) / h ^ 2 := div_le_div_of_nonneg_right hcoeff (sq_nonneg h)
    _ ≤ Real.exp (Real.rpow S.L (9 / 10 : ℝ)) / h ^ 2 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCpower) (sq_nonneg h)
    _ = Real.exp (Real.rpow S.L (9 / 10 : ℝ)) * Real.rpow S.x (2 * ε) := by
      rw [div_eq_mul_inv, hinv]


private lemma factorial_lower_bound (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hf : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hp := (div_le_iff₀ hf).1 (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
  rw [div_pow, ← Real.exp_nat_mul, mul_one]
  apply (div_le_iff₀ (Real.exp_pos _)).2
  simpa only [mul_comm] using hp

private lemma factorial_tail_bound (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (hn : 0 < n) :
    B ^ n / (n.factorial : ℝ) ≤ (Real.exp 1 * B / (n : ℝ)) ^ n := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlow : 0 < ((n : ℝ) / Real.exp 1) ^ n := pow_pos (div_pos hnR (Real.exp_pos _)) _
  calc
    B ^ n / (n.factorial : ℝ) ≤ B ^ n / (((n : ℝ) / Real.exp 1) ^ n) :=
      div_le_div_of_nonneg_left (pow_nonneg hB _) hlow (factorial_lower_bound n)
    _ = (B / ((n : ℝ) / Real.exp 1)) ^ n := (div_pow _ _ _).symm
    _ = _ := by congr 1; field_simp [hnR.ne', (Real.exp_pos 1).ne'] <;> ring

private lemma bonferroni_sandwich_transfer (af ap ag bf bp bg : ℝ)
    (ha : 0 ≤ ap - af ∧ ap - af ≤ ag) (hb : 0 ≤ bp - bf ∧ bp - bf ≤ bg) :
    |af - bf| ≤ 2 * bg + |ag - bg| + |ap - bp| := by
  have he : af - bf = (af - ap) + (ap - bp) + (bp - bf) := by ring
  have hgapA : |af - ap| ≤ ag := by rw [abs_of_nonpos (by linarith : af - ap ≤ 0)]; linarith
  have hgapB : |bp - bf| ≤ bg := by rw [abs_of_nonneg hb.1]; exact hb.2
  have hAg : ag ≤ bg + |ag - bg| := by linarith [le_abs_self (ag - bg)]
  rw [he]
  have ht1 := abs_add_le ((af - ap) + (ap - bp)) (bp - bf)
  have ht2 := abs_add_le (af - ap) (ap - bp)
  linarith

private lemma goodTestOne_measurable (x Y d₀ : ℝ) {K : ℕ} (p : PrimeLists x K) :
    Measurable (fun r : ℝ => goodTestOne x Y d₀ p r) := by
  unfold goodTestOne
  apply Measurable.forall
  intro omitted
  apply measurable_const.imp
  apply measurable_const.imp
  apply Measurable.forall
  intro l
  apply measurable_const.imp
  apply measurable_const.imp
  exact (measurableSet_lt measurable_const
    (circleDistance_continuous.measurable.comp (measurable_const.mul measurable_id))).mem

private lemma goodTestTwo_value_measurable (x d₀ : ℝ) {K : ℕ} (a : Fin K → ℝ)
    (p : PrimeLists x K) (I : Finset (Fin K)) (hI : I.Nonempty) :
    Measurable (fun r : ℝ => ∑' fresh : Fin K → ℕ,
      if IsFreshChoice x a I fresh ∧
        ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
          IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
          circleDistance (((n₁ : ℝ) - n₂) * r) ≤
            100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
      then freshChoiceWeight x a I fresh else 0) := by
  classical
  apply Measurable.tsum
  intro fresh
  have hPred : Measurable (fun r : ℝ => IsFreshChoice x a I fresh ∧
      ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
        IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
        circleDistance (((n₁ : ℝ) - n₂) * r) ≤
          100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))) := by
    apply measurable_const.and
    apply Measurable.exists
    intro n₁
    apply Measurable.exists
    intro n₂
    apply measurable_const.and
    apply measurable_const.and
    apply measurable_const.and
    exact (measurableSet_le
      (circleDistance_continuous.measurable.comp (measurable_const.mul measurable_id)) measurable_const).mem
  exact Measurable.ite hPred.setOf measurable_const measurable_const

private lemma goodTestTwo_measurable (x d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) : Measurable (fun r : ℝ => goodTestTwo x d₀ K a p r) := by
  classical
  unfold goodTestTwo
  apply Measurable.forall
  intro I
  by_cases hI : I.Nonempty
  · let G : ℝ → Prop := fun r =>
      (∑' fresh : Fin K → ℕ,
        if IsFreshChoice x a I fresh ∧
          ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₁ ∧
            IsGoodnessTrialValue a p d₀ I (I.max' hI) fresh n₂ ∧ n₁ ≠ n₂ ∧
            circleDistance (((n₁ : ℝ) - n₂) * r) ≤
              100 * Real.exp (-Real.rpow (Real.log x) (a (I.max' hI)))
        then freshChoiceWeight x a I fresh else 0) ≤
          Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a (I.max' hI)))
    have hG : Measurable G :=
      (measurableSet_le (goodTestTwo_value_measurable x d₀ a p I hI) measurable_const).mem
    convert hG using 1
    funext r
    apply propext
    exact ⟨fun h => h hI, fun h _ => h⟩
  · have he : (fun r : ℝ => ∀ h : I.Nonempty,
        let iStar := I.max' h
        (∑' fresh : Fin K → ℕ,
          if IsFreshChoice x a I fresh ∧
            ∃ n₁ n₂, IsGoodnessTrialValue a p d₀ I iStar fresh n₁ ∧
              IsGoodnessTrialValue a p d₀ I iStar fresh n₂ ∧ n₁ ≠ n₂ ∧
              circleDistance (((n₁ : ℝ) - n₂) * r) ≤
                100 * Real.exp (-Real.rpow (Real.log x) (a iStar))
          then freshChoiceWeight x a I fresh else 0) ≤
            Real.exp (-(1 / 4 : ℝ) * Real.rpow (Real.log x) (a iStar))) = fun _ => True := by
      funext r
      apply propext
      exact ⟨fun _ => True.intro, fun _ h => (hI h).elim⟩
    rw [he]
    exact measurable_const

private lemma goodRatio_measurable (x Y d₀ : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (p : PrimeLists x K) : Measurable (fun r : ℝ => IsGoodRatio x Y d₀ K a p r) :=
  (goodTestOne_measurable x Y d₀ p).and (goodTestTwo_measurable x d₀ K a p)

private lemma transportedRatio_measurable (z : ℤ × ℤ) :
    Measurable (fun r : ℝ => transportedRatio ⟨1, 1, r⟩ z) := by
  unfold transportedRatio ArchRoot.tau
  exact (measurable_const.add (measurable_id.mul measurable_const)).div
    (measurable_const.add (measurable_id.mul measurable_const))

private lemma envGood_measurable {K : ℕ} (F : PDFix K) (S : PDScale) (s : EnvPoint S.x K) :
    Measurable (fun y : ℝ × ℝ × ℝ =>
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ s) := by
  exact ((goodRatio_measurable S.x S.Y (S.d₀ : ℝ) K F.a s.2).comp
    (transportedRatio_measurable s.1)).comp (measurable_snd.comp measurable_snd)

private lemma envBox_measurable (S : PDScale) (z : ℤ × ℤ) :
    Measurable (fun y : ℝ × ℝ × ℝ => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ z) := by
  let tau : ℝ × ℝ × ℝ → ℝ := fun y => (z.1 : ℝ) + y.2.2 * (z.2 : ℝ)
  let f : ℝ × ℝ × ℝ → ℝ := fun y => (S.U * y.1) * tau y
  let g : ℝ × ℝ × ℝ → ℝ := fun y => (S.V * y.2.1) * tau y + (z.2 : ℝ) / (S.U * y.1)
  have htau : Measurable tau := measurable_const.add
    ((measurable_snd.comp measurable_snd).mul measurable_const)
  have hf : Measurable f := (measurable_const.mul measurable_fst).mul htau
  have hg : Measurable g := ((measurable_const.mul (measurable_fst.comp measurable_snd)).mul htau).add
    (measurable_const.div (measurable_const.mul measurable_fst))
  change Measurable (fun y => S.U ≤ f y ∧ f y ≤ 16 * S.U ∧ S.V ≤ g y ∧ g y ≤ 2 * S.V)
  exact (measurableSet_le measurable_const hf).mem.and
    ((measurableSet_le hf measurable_const).mem.and
      ((measurableSet_le measurable_const hg).mem.and (measurableSet_le hg measurable_const).mem))

private lemma pathArch_measurable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    Measurable (fun y : ℝ × ℝ × ℝ => pathArch F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ γ) := by
  classical
  unfold pathArch
  apply Finset.measurable_fun_prod
  intro j hj
  have hPred := (envBox_measurable S (γ j).1).and (envGood_measurable F S (γ j))
  exact Measurable.ite hPred.setOf measurable_const measurable_const

private lemma memoryQ_bounds (x q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    0 ≤ memoryQ x q j ∧ memoryQ x q j ≤ 1 := by
  unfold memoryQ
  split_ifs
  · exact ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr hq1.le⟩
  · exact ⟨hq0.le, hq1.le⟩

private lemma pathPrimeFactor_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hq0 : 0 < F.q_d) (hq1 : F.q_d < 1) (γ : EnvPath S.x K) (p : ℕ) (lam : Fin (p + 1)) :
    0 ≤ pathPrimeFactor F S γ p lam ∧ pathPrimeFactor F S γ p lam ≤ 1 := by
  classical
  let f : Fin (pathLength S.x + 1) → ℝ := fun j =>
    if IsActiveAt γ p j then (if lam = projLine p (γ j).1 then 1 else 0)
    else 1 - memoryEta S.x F.q_d j.val * (if lam = projLine p (γ j).1 then 1 else 0)
  have hf (j) : 0 ≤ f j ∧ f j ≤ 1 := by
    rcases memoryQ_bounds S.x F.q_d hq0 hq1 j.val with ⟨hqa, hqb⟩
    by_cases ha : IsActiveAt γ p j <;> by_cases hl : lam = projLine p (γ j).1 <;>
      simp [f, ha, hl, memoryEta] <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun j hj => (hf j).1),
    Finset.prod_le_one₀ (fun j hj => (hf j).1) (fun j hj => (hf j).2)⟩

private lemma pathArch_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K) :
    0 ≤ pathArch F S w γ ∧ pathArch F S w γ ≤ 1 := by
  classical
  unfold pathArch
  constructor
  · apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> norm_num
  · apply Finset.prod_le_one₀
    · intro j hj
      split_ifs <;> norm_num
    · intro j hj
      split_ifs <;> norm_num

private def pathObservable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℝ :=
  pathArch F S w γ * ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
    pathPrimeFactor F S γ p.1 (ℓ p)

private lemma pathObservable_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    0 ≤ pathObservable F S γ w ℓ ∧ pathObservable F S γ w ℓ ≤ 1 := by
  classical
  have ha := pathArch_bounds F S w γ
  have hp0 : 0 ≤ ∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
      pathPrimeFactor F S γ p.1 (ℓ p) :=
    Finset.prod_nonneg (fun p hp => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).1)
  have hp1 : (∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a},
      pathPrimeFactor F S γ p.1 (ℓ p)) ≤ 1 :=
    Finset.prod_le_one₀ (fun p hp => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).1)
      (fun p hp => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).2)
  exact ⟨mul_nonneg ha.1 hp0, by
    have hm := mul_le_mul ha.2 hp1 hp0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [pathObservable, one_mul] using hm⟩

private lemma pathObservable_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (ℓ : LineData S.x K F.a) :
    Measurable (fun y : ℝ × ℝ × ℝ => pathObservable F S γ ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ ℓ) :=
  (pathArch_measurable F S γ).mul measurable_const

private lemma lineAverage_real {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (G : LineData x K a → ℝ) :
    (lineAverage (fun ℓ => (G ℓ : ℂ))).re =
      (∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1))⁻¹ * ∑ ℓ, G ℓ := by
  unfold lineAverage
  have he : (((∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1) : ℝ) : ℂ))⁻¹ * ∑ ℓ, (G ℓ : ℂ) =
      (((∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1))⁻¹ * ∑ ℓ, G ℓ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he]
  rfl

private lemma lineAverage_real_bounds {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (G : LineData x K a → ℝ) (hG : ∀ ℓ, 0 ≤ G ℓ ∧ G ℓ ≤ 1) :
    0 ≤ (lineAverage (fun ℓ => (G ℓ : ℂ))).re ∧ (lineAverage (fun ℓ => (G ℓ : ℂ))).re ≤ 1 := by
  classical
  let D : ℝ := ∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1)
  have hD : 0 < D := Finset.prod_pos fun p hp => by positivity
  have hcard : (Fintype.card (LineData x K a) : ℝ) = D := by
    change (Fintype.card ((p : {p : ℕ // p ∈ markedPrimes x K a}) → Fin (p.1 + 1)) : ℝ) = D
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    push_cast
    change (∏ p ∈ (markedPrimes x K a).attach, ((p.1 : ℝ) + 1)) = D
    exact Finset.prod_attach (s := markedPrimes x K a) (f := fun p : ℕ => (p : ℝ) + 1)
  rw [lineAverage_real]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hD.le) (Finset.sum_nonneg (fun ℓ hℓ => (hG ℓ).1))
  · have hs : (∑ ℓ, G ℓ) ≤ D := by
      calc
        _ ≤ ∑ _ : LineData x K a, (1 : ℝ) := Finset.sum_le_sum (fun ℓ hℓ => (hG ℓ).2)
        _ = D := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]; exact hcard
    calc
      D⁻¹ * ∑ ℓ, G ℓ ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hD.le)
      _ = 1 := inv_mul_cancel₀ hD.ne'

private def physicalFunctional {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ) : ℝ :=
  (S.U * S.V)⁻¹ * ∑' uv : ℕ × ℕ,
    if IsOmegaPosition S uv.1 uv.2 then
      G (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2) else 0

private def modelFunctional {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ) : ℝ :=
  (6 / Real.pi ^ 2) *
    ∫ uu in (1 : ℝ)..16, ∫ vv in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      (lineAverage (fun ℓ => (G ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re

private lemma omega_positions_finite (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V) :
    {uv : ℕ × ℕ | IsOmegaPosition S uv.1 uv.2}.Finite := by
  apply (root_box_finite S.U S.V hU hV 16 2 (by norm_num) (by norm_num)).subset
  intro uv huv
  exact ⟨(div_le_iff₀ hU).2 huv.2.2.1, (div_le_iff₀ hV).2 huv.2.2.2.2⟩

private lemma physicalFunctional_eq_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (G : ArchRoot → LineData S.x K F.a → ℝ) :
    physicalFunctional F S G = (S.U * S.V)⁻¹ *
      ∑ uv ∈ (omega_positions_finite S hU hV).toFinset,
        G (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2) := by
  classical
  unfold physicalFunctional
  have hz (uv : ℕ × ℕ) (huv : uv ∉ (omega_positions_finite S hU hV).toFinset) :
      (if IsOmegaPosition S uv.1 uv.2 then
        G (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2) else 0) = 0 := by
    have hn : ¬ IsOmegaPosition S uv.1 uv.2 := fun h =>
      huv ((Set.Finite.mem_toFinset (omega_positions_finite S hU hV)).2 h)
    simp only [if_neg hn]
  rw [tsum_eq_sum hz]
  congr 1
  apply Finset.sum_congr rfl
  intro uv huv
  have hω : IsOmegaPosition S uv.1 uv.2 :=
    (Set.Finite.mem_toFinset (omega_positions_finite S hU hV)).1 huv
  rw [if_pos hω]

private lemma physicalFunctional_mono {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (G H : ArchRoot → LineData S.x K F.a → ℝ) (hGH : ∀ w ℓ, G w ℓ ≤ H w ℓ) :
    physicalFunctional F S G ≤ physicalFunctional F S H := by
  rw [physicalFunctional_eq_sum F S hU hV, physicalFunctional_eq_sum F S hU hV]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum (fun uv huv => hGH _ _)

private lemma physicalFunctional_sub {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (G H : ArchRoot → LineData S.x K F.a → ℝ) :
    physicalFunctional F S (fun w ℓ => G w ℓ - H w ℓ) =
      physicalFunctional F S G - physicalFunctional F S H := by
  rw [physicalFunctional_eq_sum F S hU hV, physicalFunctional_eq_sum F S hU hV,
    physicalFunctional_eq_sum F S hU hV]
  rw [Finset.sum_sub_distrib]
  ring

private lemma physicalFunctional_finset_sum {K : ℕ} {ι : Type*} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (T : Finset ι)
    (G : ι → ArchRoot → LineData S.x K F.a → ℝ) :
    physicalFunctional F S (fun w ℓ => ∑ i ∈ T, G i w ℓ) =
      ∑ i ∈ T, physicalFunctional F S (G i) := by
  classical
  simp_rw [physicalFunctional_eq_sum F S hU hV]
  rw [Finset.sum_comm, Finset.mul_sum]

private lemma physicalFunctional_mul_const {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (c : ℝ)
    (G : ArchRoot → LineData S.x K F.a → ℝ) :
    physicalFunctional F S (fun w ℓ => c * G w ℓ) = c * physicalFunctional F S G := by
  rw [physicalFunctional_eq_sum F S hU hV, physicalFunctional_eq_sum F S hU hV,
    ← Finset.mul_sum]
  ring

private lemma physical_root_in_region (S : PDScale) (hU : 0 < S.U) (u v : ℕ)
    (huv : IsOmegaPosition S u v) : (rootArch u v).InRegion S := by
  have huR : 0 < (u : ℝ) := hU.trans_le huv.2.1
  have hu : 0 < u := by exact_mod_cast huR
  have hc : (rootC u v : ℝ) ≤ (u : ℝ) := by exact_mod_cast (rootC_lt_of_pos u v hu).le
  exact ⟨huv.2.1, huv.2.2.1, huv.2.2.2.1, huv.2.2.2.2,
    div_nonneg (Nat.cast_nonneg _) huR.le, (div_le_iff₀ huR).2 (by simpa using hc)⟩

private lemma envMoment_contributing_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (hΓ : {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite)
    (w : ArchRoot) (hw : w.InRegion S) (ℓ : LineData S.x K F.a)
    (hform : envMomentC F S w ℓ = ∑' γ : EnvPath S.x K,
      if IsEnvPathAdmissible F S γ then
        pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
          ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a}, pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
      else 0) :
    envMomentC F S w ℓ = ∑ γ ∈ hΓ.toFinset,
      pathCoefficient F S γ * (pathObservable F S γ w ℓ : ℂ) := by
  classical
  have hz (γ : EnvPath S.x K) (hγ : γ ∉ hΓ.toFinset) :
      (if IsEnvPathAdmissible F S γ then
        pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
          ((∏ p : {p : ℕ // p ∈ markedPrimes S.x K F.a}, pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
      else 0) = 0 := by
    by_cases ha : IsEnvPathAdmissible F S γ
    · by_cases hc : pathCoefficient F S γ = 0
      · simp only [if_pos ha, hc, zero_mul]
      · have hb : pathArch F S w γ = 0 := by
          by_contra hn
          exact hγ ((Set.Finite.mem_toFinset hΓ).2 ⟨ha, hc, w, hw, hn⟩)
        simp only [if_pos ha, hb, Complex.ofReal_zero, mul_zero, zero_mul]
    · simp only [if_neg ha]
  rw [hform, tsum_eq_sum hz]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hc : IsContributingPath F S γ := (Set.Finite.mem_toFinset hΓ).1 hγ
  rw [if_pos hc.1]
  unfold pathObservable
  push_cast
  ring

private lemma physicalRootAverage_path_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (hΓ : {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite)
    (hform : ∀ w : ArchRoot, w.InRegion S → ∀ ℓ : LineData S.x K F.a,
      envMomentC F S w ℓ = ∑ γ ∈ hΓ.toFinset,
        pathCoefficient F S γ * (pathObservable F S γ w ℓ : ℂ)) :
    physicalRootAverage F S = ∑ γ ∈ hΓ.toFinset,
      (pathCoefficient F S γ).re * physicalFunctional F S (pathObservable F S γ) := by
  classical
  have hp : physicalRootAverage F S =
      physicalFunctional F S (fun w ℓ => (envMomentC F S w ℓ).re) := rfl
  rw [hp, physicalFunctional_eq_sum F S hU hV]
  have hpoint (uv : ℕ × ℕ) (huv : uv ∈ (omega_positions_finite S hU hV).toFinset) :
      (envMomentC F S (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2)).re =
        ∑ γ ∈ hΓ.toFinset, (pathCoefficient F S γ).re *
          pathObservable F S γ (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2) := by
    have hω : IsOmegaPosition S uv.1 uv.2 :=
      (Set.Finite.mem_toFinset (omega_positions_finite S hU hV)).1 huv
    rw [hform _ (physical_root_in_region S hU uv.1 uv.2 hω), Complex.re_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    _ = (S.U * S.V)⁻¹ * ∑ uv ∈ (omega_positions_finite S hU hV).toFinset,
          ∑ γ ∈ hΓ.toFinset, (pathCoefficient F S γ).re *
            pathObservable F S γ (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2) := by
      congr 1
      exact Finset.sum_congr rfl hpoint
    _ = ∑ γ ∈ hΓ.toFinset, (pathCoefficient F S γ).re *
          ((S.U * S.V)⁻¹ * ∑ uv ∈ (omega_positions_finite S hU hV).toFinset,
            pathObservable F S γ (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2)) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      simp_rw [physicalFunctional_eq_sum F S hU hV]

private lemma pathObservable_average_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) :
    Measurable (fun y : ℝ × ℝ × ℝ => (lineAverage (fun ℓ =>
      (pathObservable F S γ ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ ℓ : ℂ))).re) := by
  classical
  simp_rw [lineAverage_real]
  apply measurable_const.mul
  apply Finset.measurable_fun_sum
  intro ℓ hℓ
  exact pathObservable_measurable F S γ ℓ

private lemma pathObservable_average_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (w : ArchRoot) :
    0 ≤ (lineAverage (fun ℓ => (pathObservable F S γ w ℓ : ℂ))).re ∧
      (lineAverage (fun ℓ => (pathObservable F S γ w ℓ : ℂ))).re ≤ 1 :=
  lineAverage_real_bounds _ (fun ℓ => pathObservable_bounds F S hF γ w ℓ)

private lemma bounded_measurable_intervalIntegrable (f : ℝ → ℝ) (hf : Measurable f)
    (B a b : ℝ) (hB : 0 ≤ B) (hbound : ∀ t, |f t| ≤ B) : IntervalIntegrable f volume a b := by
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
  apply hconst.mono_fun hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound t)

private lemma pathObservable_inner_integrable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (uu vv a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => (lineAverage (fun ℓ =>
      (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re) volume a b := by
  have hmap : Measurable (fun r : ℝ => (uu, vv, r)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  apply bounded_measurable_intervalIntegrable _ ((pathObservable_average_measurable F S γ).comp hmap)
    1 a b (by norm_num)
  intro r
  change |(lineAverage (fun ℓ => (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re| ≤ 1
  have hb := pathObservable_average_bounds F S hF γ ⟨S.U * uu, S.V * vv, r⟩
  simpa only [abs_of_nonneg hb.1] using hb.2

private def pathInnerAverage {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (uu vv : ℝ) : ℝ := ∫ r in (0 : ℝ)..1,
  (lineAverage (fun ℓ => (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re

private def pathMidAverage {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (uu : ℝ) : ℝ := ∫ vv in (1 : ℝ)..2, pathInnerAverage F S γ uu vv

private lemma pathInnerAverage_measurable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    Measurable (fun y : ℝ × ℝ => pathInnerAverage F S γ y.1 y.2) := by
  have hmap : Measurable (fun y : (ℝ × ℝ) × ℝ => (y.1.1, y.1.2, y.2)) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hjoint := (pathObservable_average_measurable F S γ).comp hmap
  have h := hjoint.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  change Measurable (fun y : ℝ × ℝ => ∫ r in (0 : ℝ)..1,
    (lineAverage (fun ℓ => (pathObservable F S γ ⟨S.U * y.1, S.V * y.2, r⟩ ℓ : ℂ))).re)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), Function.comp_def] using h.measurable

private lemma pathInnerAverage_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (uu vv : ℝ) :
    0 ≤ pathInnerAverage F S γ uu vv ∧ pathInnerAverage F S γ uu vv ≤ 1 := by
  have h0 : 0 ≤ pathInnerAverage F S γ uu vv :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
      (fun r => (pathObservable_average_bounds F S hF γ ⟨S.U * uu, S.V * vv, r⟩).1)
  have hnorm : |pathInnerAverage F S γ uu vv| ≤ 1 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1)
      (f := fun r : ℝ => (lineAverage (fun ℓ =>
        (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re)
      (fun r hr => by
        have hb := pathObservable_average_bounds F S hF γ ⟨S.U * uu, S.V * vv, r⟩
        simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
    simpa only [pathInnerAverage, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  exact ⟨h0, by simpa only [abs_of_nonneg h0] using hnorm⟩

section
attribute [local irreducible] pathInnerAverage

private lemma pathInnerAverage_integrable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (uu a b : ℝ) :
    IntervalIntegrable (pathInnerAverage F S γ uu) volume a b := by
  have hmap : Measurable (fun vv : ℝ => (uu, vv)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun vv : ℝ => pathInnerAverage F S γ uu vv) :=
    (pathInnerAverage_measurable F S γ).comp hmap
  apply bounded_measurable_intervalIntegrable _ hm 1 a b (by norm_num)
  intro vv
  change |pathInnerAverage F S γ uu vv| ≤ 1
  have hb := pathInnerAverage_bounds F S hF γ uu vv
  simpa only [abs_of_nonneg hb.1] using hb.2

end

private lemma pathMidAverage_measurable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    Measurable (pathMidAverage F S γ) := by
  have h := (pathInnerAverage_measurable F S γ).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (1 : ℝ) 2))
  change Measurable (fun uu : ℝ => ∫ vv in (1 : ℝ)..2, pathInnerAverage F S γ uu vv)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)] using h.measurable

private lemma pathMidAverage_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (uu : ℝ) :
    0 ≤ pathMidAverage F S γ uu ∧ pathMidAverage F S γ uu ≤ 1 := by
  have h0 : 0 ≤ pathMidAverage F S γ uu :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num : (1 : ℝ) ≤ 2)
      (fun vv => (pathInnerAverage_bounds F S hF γ uu vv).1)
  have hnorm : |pathMidAverage F S γ uu| ≤ 1 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 : ℝ)) (b := 2) (C := 1)
      (f := pathInnerAverage F S γ uu)
      (fun vv hvv => by
        have hb := pathInnerAverage_bounds F S hF γ uu vv
        simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)
    norm_num only [pathMidAverage, Real.norm_eq_abs] at h
    exact h
  exact ⟨h0, by simpa only [abs_of_nonneg h0] using hnorm⟩

private lemma pathMidAverage_integrable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hF : F.Valid) (γ : EnvPath S.x K) (a b : ℝ) :
    IntervalIntegrable (pathMidAverage F S γ) volume a b := by
  apply bounded_measurable_intervalIntegrable _ (pathMidAverage_measurable F S γ) 1 a b (by norm_num)
  intro uu
  have hb := pathMidAverage_bounds F S hF γ uu
  simpa only [abs_of_nonneg hb.1] using hb.2

private lemma lineAverage_re {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (G : LineData x K a → ℂ) :
    (lineAverage G).re = (∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1))⁻¹ * ∑ ℓ, (G ℓ).re := by
  let D : ℝ := ∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1)
  have hinv : ((D : ℂ))⁻¹ = ((D⁻¹ : ℝ) : ℂ) := (Complex.ofReal_inv D).symm
  unfold lineAverage
  change (((D : ℂ))⁻¹ * ∑ ℓ, G ℓ).re = D⁻¹ * ∑ ℓ, (G ℓ).re
  rw [hinv, Complex.mul_re, Complex.re_sum]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]

private lemma normalized_root_in_region (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V)
    (uu vv r : ℝ) (hu : uu ∈ Set.Icc 1 16) (hv : vv ∈ Set.Icc 1 2) (hr : r ∈ Set.Icc 0 1) :
    (⟨S.U * uu, S.V * vv, r⟩ : ArchRoot).InRegion S := by
  exact ⟨by nlinarith [mul_le_mul_of_nonneg_left hu.1 hU.le],
    by nlinarith [mul_le_mul_of_nonneg_left hu.2 hU.le],
    by nlinarith [mul_le_mul_of_nonneg_left hv.1 hV.le],
    by nlinarith [mul_le_mul_of_nonneg_left hv.2 hV.le], hr.1, hr.2⟩

private lemma envMoment_lineAverage_path_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (EnvPath S.x K)) (w : ArchRoot)
    (hform : ∀ ℓ : LineData S.x K F.a,
      envMomentC F S w ℓ = ∑ γ ∈ T, pathCoefficient F S γ * (pathObservable F S γ w ℓ : ℂ)) :
    (lineAverage (fun ℓ => envMomentC F S w ℓ)).re =
      ∑ γ ∈ T, (pathCoefficient F S γ).re *
        (lineAverage (fun ℓ => (pathObservable F S γ w ℓ : ℂ))).re := by
  classical
  have he (ℓ : LineData S.x K F.a) : (envMomentC F S w ℓ).re =
      ∑ γ ∈ T, (pathCoefficient F S γ).re * pathObservable F S γ w ℓ := by
    rw [hform, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro γ hγ
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [lineAverage_re]
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [← Finset.mul_sum, lineAverage_real]
  ring

private lemma tripleIntegral_path_sum {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (T : Finset (EnvPath S.x K)) (c : EnvPath S.x K → ℝ) :
    (∫ uu in (1 : ℝ)..16, ∫ vv in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      ∑ γ ∈ T, c γ * (lineAverage (fun ℓ =>
        (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re) =
      ∑ γ ∈ T, c γ * ∫ uu in (1 : ℝ)..16, pathMidAverage F S γ uu := by
  classical
  have hr (uu vv : ℝ) :
      (∫ r in (0 : ℝ)..1, ∑ γ ∈ T, c γ * (lineAverage (fun ℓ =>
        (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re) =
      ∑ γ ∈ T, c γ * pathInnerAverage F S γ uu vv := by
    rw [intervalIntegral.integral_finsetSum
      (fun γ hγ => (pathObservable_inner_integrable F S hF γ uu vv 0 1).const_mul (c γ))]
    simp only [intervalIntegral.integral_const_mul, pathInnerAverage]
  have hv (uu : ℝ) :
      (∫ vv in (1 : ℝ)..2, ∑ γ ∈ T, c γ * pathInnerAverage F S γ uu vv) =
      ∑ γ ∈ T, c γ * pathMidAverage F S γ uu := by
    rw [intervalIntegral.integral_finsetSum
      (fun γ hγ => (pathInnerAverage_integrable F S hF γ uu 1 2).const_mul (c γ))]
    simp only [intervalIntegral.integral_const_mul, pathMidAverage]
  simp_rw [hr, hv]
  rw [intervalIntegral.integral_finsetSum
    (fun γ hγ => (pathMidAverage_integrable F S hF γ 1 16).const_mul (c γ))]
  simp only [intervalIntegral.integral_const_mul]

private lemma modelRootAverage_path_sum {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hU : 0 < S.U) (hV : 0 < S.V) (T : Finset (EnvPath S.x K))
    (hform : ∀ w : ArchRoot, w.InRegion S → ∀ ℓ : LineData S.x K F.a,
      envMomentC F S w ℓ = ∑ γ ∈ T, pathCoefficient F S γ * (pathObservable F S γ w ℓ : ℂ)) :
    modelRootAverage F S = ∑ γ ∈ T,
      (pathCoefficient F S γ).re * modelFunctional F S (pathObservable F S γ) := by
  classical
  have hpoint (uu vv r : ℝ) (hu : uu ∈ Set.Icc 1 16) (hv : vv ∈ Set.Icc 1 2) (hr : r ∈ Set.Icc 0 1) :
      (lineAverage (fun ℓ => envMomentC F S ⟨S.U * uu, S.V * vv, r⟩ ℓ)).re =
        ∑ γ ∈ T, (pathCoefficient F S γ).re * (lineAverage (fun ℓ =>
          (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re :=
    envMoment_lineAverage_path_sum F S T _
      (hform _ (normalized_root_in_region S hU hV uu vv r hu hv hr))
  have hIntegral :
      (∫ uu in (1 : ℝ)..16, ∫ vv in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
        (lineAverage (fun ℓ => envMomentC F S ⟨S.U * uu, S.V * vv, r⟩ ℓ)).re) =
      ∫ uu in (1 : ℝ)..16, ∫ vv in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
        ∑ γ ∈ T, (pathCoefficient F S γ).re * (lineAverage (fun ℓ =>
          (pathObservable F S γ ⟨S.U * uu, S.V * vv, r⟩ ℓ : ℂ))).re := by
    apply intervalIntegral.integral_congr
    intro uu hu
    apply intervalIntegral.integral_congr
    intro vv hv
    apply intervalIntegral.integral_congr
    intro r hr
    exact hpoint uu vv r (by simpa only [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 16)] using hu)
      (by simpa only [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hv)
      (by simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr)
  unfold modelRootAverage
  rw [hIntegral, tripleIntegral_path_sum F S hF T, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  change (6 / Real.pi ^ 2) * ((pathCoefficient F S γ).re * ∫ uu in (1 : ℝ)..16, pathMidAverage F S γ uu) = _
  unfold modelFunctional pathMidAverage pathInnerAverage
  ring

private lemma rootReplacement_mass_transfer {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (hΓ : {γ : EnvPath S.x K | IsContributingPath F S γ}.Finite)
    (hform : ∀ w : ArchRoot, w.InRegion S → ∀ ℓ : LineData S.x K F.a,
      envMomentC F S w ℓ = ∑ γ ∈ hΓ.toFinset,
        pathCoefficient F S γ * (pathObservable F S γ w ℓ : ℂ))
    (E Cmass : ℝ) (hE : 0 ≤ E)
    (hmass : (∑ γ ∈ hΓ.toFinset, ‖pathCoefficient F S γ‖) ≤ Cmass)
    (htransfer : ∀ γ : EnvPath S.x K, IsContributingPath F S γ →
      |physicalFunctional F S (pathObservable F S γ) -
        modelFunctional F S (pathObservable F S γ)| ≤ E) :
    |physicalRootAverage F S - modelRootAverage F S| ≤ Cmass * E := by
  classical
  rw [physicalRootAverage_path_sum F S hU hV hΓ hform,
    modelRootAverage_path_sum F S hF hU hV hΓ.toFinset hform,
    ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hsum : |∑ γ ∈ hΓ.toFinset, (pathCoefficient F S γ).re *
      (physicalFunctional F S (pathObservable F S γ) -
        modelFunctional F S (pathObservable F S γ))| ≤
      ∑ γ ∈ hΓ.toFinset, |(pathCoefficient F S γ).re *
        (physicalFunctional F S (pathObservable F S γ) -
          modelFunctional F S (pathObservable F S γ))| := by
    simpa only [Real.norm_eq_abs] using norm_sum_le hΓ.toFinset (fun γ =>
      (pathCoefficient F S γ).re *
        (physicalFunctional F S (pathObservable F S γ) - modelFunctional F S (pathObservable F S γ)))
  calc
    _ ≤ ∑ γ ∈ hΓ.toFinset, |(pathCoefficient F S γ).re *
        (physicalFunctional F S (pathObservable F S γ) - modelFunctional F S (pathObservable F S γ))| := hsum
    _ ≤ ∑ γ ∈ hΓ.toFinset, ‖pathCoefficient F S γ‖ * E := by
      apply Finset.sum_le_sum
      intro γ hγ
      rw [abs_mul]
      exact mul_le_mul (Complex.abs_re_le_norm _) (htransfer γ ((Set.Finite.mem_toFinset hΓ).1 hγ))
        (abs_nonneg _) (norm_nonneg _)
    _ = (∑ γ ∈ hΓ.toFinset, ‖pathCoefficient F S γ‖) * E := (Finset.sum_mul _ _ _).symm
    _ ≤ Cmass * E := mul_le_mul_of_nonneg_right hmass hE

private def rootRegion : Set (ℝ × ℝ × ℝ) :=
  Set.Icc 1 16 ×ˢ (Set.Icc 1 2 ×ˢ Set.Icc 0 1)

private lemma pathArch_indicator {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (w : ArchRoot) :
    pathArch F S w γ = if ∀ j, envBox S w (γ j).1 ∧ envGood F S w (γ j) then 1 else 0 := by
  classical
  by_cases h : ∀ j, envBox S w (γ j).1 ∧ envGood F S w (γ j)
  · simp [pathArch, h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    simp only [pathArch, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private lemma path_nonconstant_visit {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (C : Set (ℝ × ℝ × ℝ))
    (h : IsNonconstantOn (fun y => ∀ j,
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) C) :
    ∃ j : Fin (pathLength S.x + 1), IsNonconstantOn (fun y =>
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) C := by
  rcases h with ⟨y, hy, y', hy', hyes, hno⟩
  obtain ⟨j, hj⟩ := not_forall.mp hno
  exact ⟨j, y, hy, y', hy', hyes j, hj⟩

private lemma path_boundary_card {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (h E : ℝ)
    (hvisit : ∀ j : Fin (pathLength S.x + 1),
      (((gridIndices h).filter fun k => IsNonconstantOn (fun y =>
        envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
        envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) (gridCube h k)).card : ℝ) ≤ E) :
    (((gridIndices h).filter fun k => IsNonconstantOn (fun y => ∀ j,
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) (gridCube h k)).card : ℝ) ≤
      ((pathLength S.x : ℝ) + 1) * E := by
  classical
  let B := fun j : Fin (pathLength S.x + 1) => (gridIndices h).filter fun k =>
    IsNonconstantOn (fun y => envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) (gridCube h k)
  have hsub : ((gridIndices h).filter fun k => IsNonconstantOn (fun y => ∀ j,
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) (gridCube h k)) ⊆
      Finset.univ.biUnion B := by
    intro k hk
    obtain ⟨j, hj⟩ := path_nonconstant_visit F S γ _ (Finset.mem_filter.mp hk).2
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hj⟩⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le :
    (Finset.univ.biUnion B).card ≤ ∑ j, (B j).card)
  have hcR : (((gridIndices h).filter fun k => IsNonconstantOn (fun y => ∀ j,
      envBox S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U * y.1, S.V * y.2.1, y.2.2⟩ (γ j)) (gridCube h k)).card : ℝ) ≤
      ∑ j, ((B j).card : ℝ) := by exact_mod_cast hc
  calc
    _ ≤ ∑ j, ((B j).card : ℝ) := hcR
    _ ≤ ∑ _j : Fin (pathLength S.x + 1), E := Finset.sum_le_sum (fun j _ => hvisit j)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add]

private lemma grid_indices_card (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    ((gridIndices h).card : ℝ) ≤ 1000 / h ^ 3 := by
  have h1 := grid_axis_card_le h 1 16 hh hh1 (by norm_num)
  have h2 := grid_axis_card_le h 1 2 hh hh1 (by norm_num)
  have h3 := grid_axis_card_le h 0 1 hh hh1 (by norm_num)
  norm_num only at h1 h2 h3
  simp only [zero_div, Int.floor_zero, zero_sub] at h3
  have hprod := mul_le_mul h1 (mul_le_mul h2 h3 (Nat.cast_nonneg _)
    (by positivity : 0 ≤ (5 : ℝ) / h))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity : 0 ≤ (19 : ℝ) / h)
  change (((Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉).card : ℝ) *
    (((Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉).card : ℝ) *
    ((Finset.Icc (-1) ⌈1 / h⌉).card : ℝ))) ≤ _ at hprod
  have heq : ((gridIndices h).card : ℝ) =
      ((Finset.Icc (⌊1 / h⌋ - 1) ⌈16 / h⌉).card : ℝ) *
      (((Finset.Icc (⌊1 / h⌋ - 1) ⌈2 / h⌉).card : ℝ) *
      ((Finset.Icc (-1) ⌈1 / h⌉).card : ℝ)) := by
    simp only [gridIndices, Finset.card_product, Nat.cast_mul]
  rw [heq]
  calc
    _ ≤ (19 / h) * ((5 / h) * (5 / h)) := hprod
    _ ≤ 1000 / h ^ 3 := by field_simp; nlinarith

private def gridOwner (h : ℝ) (y : ℝ × ℝ × ℝ) : ℤ × ℤ × ℤ :=
  (⌊y.1 / h⌋, ⌊y.2.1 / h⌋, ⌊y.2.2 / h⌋)

private lemma grid_owner_cube (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ) :
    y ∈ gridCube h (gridOwner h y) := by
  have hf (a : ℝ) : (⌊a / h⌋ : ℝ) * h ≤ a ∧ a ≤ ((⌊a / h⌋ : ℝ) + 1) * h := by
    constructor
    · exact (le_div_iff₀ hh).1 (Int.floor_le _)
    · exact (div_le_iff₀ hh).1 (Int.lt_floor_add_one _).le
  exact ⟨(hf y.1).1, (hf y.1).2, (hf y.2.1).1, (hf y.2.1).2,
    (hf y.2.2).1, (hf y.2.2).2⟩

private lemma grid_owner_mem (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ) (hy : y ∈ rootRegion) :
    gridOwner h y ∈ gridIndices h := by
  have hf (l r a : ℝ) (ha : a ∈ Set.Icc l r) :
      ⌊a / h⌋ ∈ Finset.Icc (⌊l / h⌋ - 1) ⌈r / h⌉ := by
    apply Finset.mem_Icc.mpr
    have hl := Int.floor_mono (div_le_div_of_nonneg_right ha.1 hh.le)
    have hr : ⌊a / h⌋ ≤ ⌈r / h⌉ :=
      (Int.floor_mono (div_le_div_of_nonneg_right ha.2 hh.le)).trans (Int.floor_le_ceil _)
    exact ⟨by omega, hr⟩
  exact Finset.mem_product.mpr ⟨hf 1 16 y.1 hy.1,
    Finset.mem_product.mpr ⟨hf 1 2 y.2.1 hy.2.1, by simpa [gridOwner] using hf 0 1 y.2.2 hy.2.2⟩⟩

private def gridCell (h : ℝ) (k : ℤ × ℤ × ℤ) : Set (ℝ × ℝ × ℝ) :=
  {y | y ∈ rootRegion ∧ gridOwner h y = k}

private lemma grid_cell_subset_cube (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ) :
    gridCell h k ⊆ gridCube h k := by
  intro y hy
  rw [← hy.2]
  exact grid_owner_cube h hh y

private lemma grid_cell_partition (h : ℝ) (hh : 0 < h) (y : ℝ × ℝ × ℝ)
    (hy : y ∈ rootRegion) (f : (ℤ × ℤ × ℤ) → ℝ) :
    (∑ k ∈ gridIndices h, if y ∈ gridCell h k then f k else 0) = f (gridOwner h y) := by
  classical
  rw [Finset.sum_eq_single (gridOwner h y)]
  · simp [gridCell, hy]
  · intro k hk hne
    simp [gridCell, Ne.symm hne]
  · exact fun hnot => (hnot (grid_owner_mem h hh y hy)).elim

private lemma grid_owner_of_upper_ne (h a : ℝ) (hh : 0 < h) (k : ℤ)
    (hl : (k : ℝ) * h ≤ a) (hr : a ≤ ((k : ℝ) + 1) * h)
    (hne : a ≠ ((k : ℝ) + 1) * h) : ⌊a / h⌋ = k := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ hh).2 hl, (div_lt_iff₀ hh).2 (lt_of_le_of_ne hr hne)⟩

private lemma grid_cell_excluded_face (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ)
    (y : ℝ × ℝ × ℝ) (hy : y ∈ rootRegion) (hc : y ∈ gridCube h k)
    (hne : y ∉ gridCell h k) :
    y.1 = ((k.1 : ℝ) + 1) * h ∨ y.2.1 = ((k.2.1 : ℝ) + 1) * h ∨
      y.2.2 = ((k.2.2 : ℝ) + 1) * h := by
  by_contra hf
  push_neg at hf
  have h1 := grid_owner_of_upper_ne h y.1 hh k.1 hc.1 hc.2.1 hf.1
  have h2 := grid_owner_of_upper_ne h y.2.1 hh k.2.1 hc.2.2.1 hc.2.2.2.1 hf.2.1
  have h3 := grid_owner_of_upper_ne h y.2.2 hh k.2.2 hc.2.2.2.2.1 hc.2.2.2.2.2 hf.2.2
  apply hne
  exact ⟨hy, by simp [gridOwner, h1, h2, h3]⟩

private lemma grid_closed_clipped (h : ℝ) (k : ℤ × ℤ × ℤ) (y : ℝ × ℝ × ℝ) :
    y ∈ rootRegion ∧ y ∈ gridCube h k ↔
      y.1 ∈ Set.Icc (max 1 ((k.1 : ℝ) * h)) (min 16 (((k.1 : ℝ) + 1) * h)) ∧
      y.2.1 ∈ Set.Icc (max 1 ((k.2.1 : ℝ) * h)) (min 2 (((k.2.1 : ℝ) + 1) * h)) ∧
      y.2.2 ∈ Set.Icc (max 0 ((k.2.2 : ℝ) * h)) (min 1 (((k.2.2 : ℝ) + 1) * h)) := by
  simp only [rootRegion, Set.mem_prod, Set.mem_Icc, gridCube, Set.mem_setOf_eq,
    max_le_iff, le_min_iff]
  tauto

private lemma finite_cell_discrepancy {α : Type*} (A C D₁ D₂ D₃ : Set α)
    (hA : A.Finite) (hC : C ⊆ A) (hfaces : A \ C ⊆ D₁ ∪ D₂ ∪ D₃)
    (hD₁ : D₁.Finite) (hD₂ : D₂.Finite) (hD₃ : D₃.Finite)
    (E M : ℝ) (hE : 0 ≤ E) (hcount : |(A.ncard : ℝ) - M| ≤ E)
    (hf₁ : (D₁.ncard : ℝ) ≤ E) (hf₂ : (D₂.ncard : ℝ) ≤ E)
    (hf₃ : (D₃.ncard : ℝ) ≤ E) : |(C.ncard : ℝ) - M| ≤ 4 * E := by
  have hcard := Set.ncard_le_ncard hfaces ((hD₁.union hD₂).union hD₃)
  have hsum := (Set.ncard_union_le (D₁ ∪ D₂) D₃).trans
    (Nat.add_le_add_right (Set.ncard_union_le D₁ D₂) D₃.ncard)
  have hcR : ((A \ C).ncard : ℝ) ≤ (D₁.ncard : ℝ) + (D₂.ncard : ℝ) + (D₃.ncard : ℝ) := by
    exact_mod_cast hcard.trans hsum
  have heqR : ((A \ C).ncard : ℝ) + (C.ncard : ℝ) = (A.ncard : ℝ) := by
    exact_mod_cast Set.ncard_sdiff_add_ncard_of_subset hC hA
  have hd : |(C.ncard : ℝ) - (A.ncard : ℝ)| ≤ 3 * E := by
    rw [← heqR]
    have he : (C.ncard : ℝ) - (((A \ C).ncard : ℝ) + (C.ncard : ℝ)) =
        -((A \ C).ncard : ℝ) := by ring
    rw [he, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    linarith
  calc
    _ = |((C.ncard : ℝ) - (A.ncard : ℝ)) + ((A.ncard : ℝ) - M)| := by congr 1; ring
    _ ≤ |(C.ncard : ℝ) - (A.ncard : ℝ)| + |(A.ncard : ℝ) - M| := abs_add_le _ _
    _ ≤ 4 * E := by linarith

private def gridCellVolume (h : ℝ) (k : ℤ × ℤ × ℤ) : ℝ :=
  max 0 (min (((k.1 : ℝ) + 1) * h) 16 - max ((k.1 : ℝ) * h) 1) *
    max 0 (min (((k.2.1 : ℝ) + 1) * h) 2 - max ((k.2.1 : ℝ) * h) 1) *
    max 0 (min (((k.2.2 : ℝ) + 1) * h) 1 - max ((k.2.2 : ℝ) * h) 0)

private lemma grid_cell_volume_bound (h : ℝ) (hh : 0 ≤ h) (k : ℤ × ℤ × ℤ) :
    0 ≤ gridCellVolume h k ∧ gridCellVolume h k ≤ h ^ 3 := by
  have haxis (a b : ℝ) (i : ℤ) :
      0 ≤ max 0 (min (((i : ℝ) + 1) * h) b - max ((i : ℝ) * h) a) ∧
      max 0 (min (((i : ℝ) + 1) * h) b - max ((i : ℝ) * h) a) ≤ h := by
    constructor
    · exact le_max_left _ _
    · apply max_le hh
      have hl := le_max_left ((i : ℝ) * h) a
      have hr := min_le_left (((i : ℝ) + 1) * h) b
      nlinarith
  have h1 := haxis 1 16 k.1
  have h2 := haxis 1 2 k.2.1
  have h3 := haxis 0 1 k.2.2
  refine ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1, ?_⟩
  have hm := mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 hh) h3.2 h3.1 (mul_nonneg hh hh)
  simpa only [gridCellVolume, pow_succ, pow_zero, one_mul] using hm

private lemma physicalFunctional_indicator {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (R : ArchRoot → LineData S.x K F.a → Prop) :
    physicalFunctional F S (fun w ℓ => if R w ℓ then 1 else 0) =
      (S.U * S.V)⁻¹ * (Set.ncard {uv : ℕ × ℕ | IsOmegaPosition S uv.1 uv.2 ∧
        R (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2)} : ℝ) := by
  classical
  let A : Set (ℕ × ℕ) := {uv | IsOmegaPosition S uv.1 uv.2 ∧
    R (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2)}
  have hA : A.Finite := (omega_positions_finite S hU hV).subset (fun _ h => h.1)
  have hfilter : (omega_positions_finite S hU hV).toFinset.filter (fun uv =>
      R (rootArch uv.1 uv.2) (rootLines F S uv.1 uv.2)) = hA.toFinset := by
    ext uv
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, A, Set.mem_setOf_eq]
  rw [physicalFunctional_eq_sum F S hU hV]
  change _ = (S.U * S.V)⁻¹ * (A.ncard : ℝ)
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card A hA]

private def archRectangle (S : PDScale) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (w : ArchRoot) : Prop :=
  l₁ ≤ w.u / S.U ∧ w.u / S.U ≤ r₁ ∧ l₂ ≤ w.v / S.V ∧ w.v / S.V ≤ r₂ ∧
    l₃ ≤ w.r ∧ w.r ≤ r₃

private def assignedLines {K : ℕ} (F : PDFix K) (S : PDScale) (J : Finset ℕ)
    (hJ : J ⊆ markedPrimes S.x K F.a) (lam : (p : ℕ) → Fin (p + 1))
    (ℓ : LineData S.x K F.a) : Prop :=
  ∀ p (hp : p ∈ J), ℓ ⟨p, hJ hp⟩ = lam p

private lemma rectangle_root_count {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hr₁ : r₁ ≤ 16) (hl₂ : 1 ≤ l₂) (hr₂ : r₂ ≤ 2)
    (hl₃ : 0 ≤ l₃) (hr₃ : r₃ ≤ 1) :
    physicalFunctional F S (fun w ℓ =>
      if archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) =
      (S.U * S.V)⁻¹ * (Set.ncard {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
        l₁ ≤ (uv.1 : ℝ) / S.U ∧ (uv.1 : ℝ) / S.U ≤ r₁ ∧
        l₂ ≤ (uv.2 : ℝ) / S.V ∧ (uv.2 : ℝ) / S.V ≤ r₂ ∧
        l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃ ∧
        ∀ p ∈ J, kernelLine p uv.1 (rootC uv.1 uv.2) = lam p} : ℝ) := by
  trans (S.U * S.V)⁻¹ * (Set.ncard {uv : ℕ × ℕ | IsOmegaPosition S uv.1 uv.2 ∧
    archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ (rootArch uv.1 uv.2) ∧
      assignedLines F S J hJ lam (rootLines F S uv.1 uv.2)} : ℝ)
  · convert physicalFunctional_indicator F S hU hV (fun w ℓ =>
      archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ) using 1
    congr 1
    funext w ℓ
    by_cases h : archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ <;> simp [h]
  apply congrArg (fun A : Set (ℕ × ℕ) => (S.U * S.V)⁻¹ * (A.ncard : ℝ))
  ext uv
  change (IsOmegaPosition S uv.1 uv.2 ∧
    (l₁ ≤ (uv.1 : ℝ) / S.U ∧ (uv.1 : ℝ) / S.U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / S.V ∧ (uv.2 : ℝ) / S.V ≤ r₂ ∧
      l₃ ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧ (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ r₃) ∧
    ∀ p ∈ J, kernelLine p uv.1 (rootC uv.1 uv.2) = lam p) ↔ _
  constructor
  · rintro ⟨hω, hb, hlines⟩
    have hu : 0 < uv.1 := by exact_mod_cast hU.trans_le hω.2.1
    exact ⟨hω.1, hu, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
      hb.2.2.2.2.1, hb.2.2.2.2.2, hlines⟩
  · rintro ⟨hcop, hu, h1, h2, h3, h4, h5, h6, hlines⟩
    refine ⟨⟨hcop, ?_, ?_, ?_, ?_⟩, ⟨h1, h2, h3, h4, h5, h6⟩, hlines⟩
    · have hm := (le_div_iff₀ hU).1 (hl₁.trans h1)
      simpa only [one_mul] using hm
    · exact (div_le_iff₀ hU).1 (h2.trans hr₁)
    · have hm := (le_div_iff₀ hV).1 (hl₂.trans h3)
      simpa only [one_mul] using hm
    · exact (div_le_iff₀ hV).1 (h4.trans hr₂)

private lemma line_assignment_average {K : ℕ} (F : PDFix K) (S : PDScale)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) :
    (lineAverage (fun ℓ : LineData S.x K F.a =>
      ((if assignedLines F S J hJ lam ℓ then 1 else 0 : ℝ) : ℂ))).re =
      ∏ p ∈ J, ((p : ℝ) + 1)⁻¹ := by
  classical
  let T := (markedPrimes S.x K F.a).attach.filter fun p => p.1 ∈ J
  let X := fun p : {p : ℕ // p ∈ markedPrimes S.x K F.a} =>
    fun z : Fin (p.1 + 1) => if z = lam p.1 then (1 : ℝ) else 0
  have hpoint (ℓ : LineData S.x K F.a) :
      (if assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) = ∏ p ∈ T, X p (ℓ p) := by
    by_cases h : assignedLines F S J hJ lam ℓ
    · simp only [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro p hp
      simp only [X, if_pos (h p.1 (Finset.mem_filter.mp hp).2)]
    · obtain ⟨p, hp⟩ := not_forall.mp h
      obtain ⟨hp, hneq⟩ := not_forall.mp hp
      simp only [if_neg h]
      symm
      apply Finset.prod_eq_zero (i := ⟨p, hJ hp⟩)
      · simp [T, hp]
      · exact if_neg hneq
  have hmean := congrArg Complex.re (lineAverage_prod T X)
  simp only [Complex.ofReal_re] at hmean
  simp_rw [← hpoint] at hmean
  rw [hmean]
  have heach (p : {p : ℕ // p ∈ markedPrimes S.x K F.a}) :
      (∑ z : Fin (p.1 + 1), X p z) = 1 := by
    simp [X]
  simp_rw [heach, mul_one]
  have hT : T = J.attach.map ⟨fun p => ⟨p.1, hJ p.2⟩, by
    intro a b h
    exact Subtype.ext (congrArg (fun p : {p : ℕ // p ∈ markedPrimes S.x K F.a} => p.1) h)⟩ := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_attach, true_and]
    constructor
    · intro hp
      exact Finset.mem_map.mpr ⟨⟨p.1, hp⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
    · intro hp
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hp
      have heq := congrArg (fun p : {p : ℕ // p ∈ markedPrimes S.x K F.a} => p.1) ha
      change a.1 = p.1 at heq
      exact heq ▸ a.2
  rw [hT, Finset.prod_map]
  exact Finset.prod_attach J (fun p : ℕ => ((p : ℝ) + 1)⁻¹)

private lemma normalized_arch_rectangle (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V)
    (l₁ r₁ l₂ r₂ l₃ r₃ u v r : ℝ) :
    archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ ⟨S.U * u, S.V * v, r⟩ ↔
      u ∈ Set.Icc l₁ r₁ ∧ v ∈ Set.Icc l₂ r₂ ∧ r ∈ Set.Icc l₃ r₃ := by
  have hu : S.U * u / S.U = u := by field_simp
  have hv : S.V * v / S.V = v := by field_simp
  simp only [archRectangle, hu, hv, Set.mem_Icc]
  tauto

private lemma line_assignment_with_arch {K : ℕ} (F : PDFix K) (S : PDScale)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (P : Prop) :
    (lineAverage (fun ℓ : LineData S.x K F.a =>
      ((if P ∧ assignedLines F S J hJ lam ℓ then 1 else 0 : ℝ) : ℂ))).re =
      (if P then 1 else 0) * ∏ p ∈ J, ((p : ℝ) + 1)⁻¹ := by
  classical
  by_cases hP : P
  · simp only [hP, true_and, if_true, one_mul]
    exact line_assignment_average F S J hJ lam
  · simp [hP, lineAverage]

private lemma rectangle_model_average {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ)
    (hl₁ : 1 ≤ l₁) (hle₁ : l₁ ≤ r₁) (hr₁ : r₁ ≤ 16)
    (hl₂ : 1 ≤ l₂) (hle₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 2)
    (hl₃ : 0 ≤ l₃) (hle₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    modelFunctional F S (fun w ℓ =>
      if archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) =
      (6 / Real.pi ^ 2) * (r₁-l₁) * (r₂-l₂) * (r₃-l₃) *
        ∏ p ∈ J, ((p : ℝ) + 1)⁻¹ := by
  classical
  unfold modelFunctional
  simp_rw [line_assignment_with_arch F S J hJ lam,
    normalized_arch_rectangle S hU hV,
    intervalIntegral.integral_mul_const]
  rw [triple_rectangle_indicator 1 16 1 2 0 1 l₁ r₁ l₂ r₂ l₃ r₃
    (by norm_num) (by norm_num) (by norm_num)]
  simp only [min_eq_left hr₁, max_eq_left hl₁, min_eq_left hr₂, max_eq_left hl₂,
    min_eq_left hr₃, max_eq_left hl₃, max_eq_right (sub_nonneg.mpr hle₁),
    max_eq_right (sub_nonneg.mpr hle₂), max_eq_right (sub_nonneg.mpr hle₃)]
  ring

private def normalizedArch (S : PDScale) (w : ArchRoot) : ℝ × ℝ × ℝ :=
  (w.u / S.U, w.v / S.V, w.r)

private lemma normalized_arch_point (S : PDScale) (hU : 0 < S.U) (hV : 0 < S.V)
    (u v r : ℝ) : normalizedArch S ⟨S.U * u, S.V * v, r⟩ = (u,v,r) := by
  have hu : S.U * u / S.U = u := by field_simp
  have hv : S.V * v / S.V = v := by field_simp
  simp only [normalizedArch, hu, hv]

private lemma grid_cell_model_average {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (lam : (p : ℕ) → Fin (p + 1)) :
    modelFunctional F S (fun w ℓ =>
      if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then 1 else 0) =
      (6 / Real.pi ^ 2) * gridCellVolume h k * ∏ p ∈ J, ((p : ℝ) + 1)⁻¹ := by
  classical
  have hIntegral :
      (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
        (lineAverage (fun ℓ => ((if normalizedArch S ⟨S.U*u,S.V*v,r⟩ ∈ gridCell h k ∧
          assignedLines F S J hJ lam ℓ then 1 else 0 : ℝ) : ℂ))).re) =
      ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
        (if (⌊u/h⌋,⌊v/h⌋,⌊r/h⌋) = k then (1 : ℝ) else 0) *
          ∏ p ∈ J, ((p : ℝ) + 1)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    apply intervalIntegral.integral_congr
    intro v hv
    apply intervalIntegral.integral_congr
    intro r hr
    have hy : (u,v,r) ∈ rootRegion := by
      simpa only [rootRegion, Set.mem_prod, Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 16),
        Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
        Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using And.intro hu (And.intro hv hr)
    dsimp only
    simp only [line_assignment_with_arch F S J hJ lam]
    simp only [normalized_arch_point S hU hV, gridCell, Set.mem_setOf_eq, hy,
      true_and, gridOwner]
  unfold modelFunctional
  rw [hIntegral]
  simp_rw [intervalIntegral.integral_mul_const]
  rw [triple_floor_indicator h hh k]
  dsimp only [gridCellVolume]
  ring

private lemma lineData_real_card {x : ℝ} {K : ℕ} {a : Fin K → ℝ} :
    (Fintype.card (LineData x K a) : ℝ) = ∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  exact Finset.prod_attach (s := markedPrimes x K a) (f := fun p : ℕ => (p : ℝ) + 1)

private lemma lineAverage_abs_bound {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (G : LineData x K a → ℝ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ ℓ, |G ℓ| ≤ B) :
    |(lineAverage (fun ℓ => (G ℓ : ℂ))).re| ≤ B := by
  rw [lineAverage_real, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1))⁻¹)]
  have hD : 0 < ∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1) :=
    Finset.prod_pos (fun p hp => by positivity)
  have hs : |∑ ℓ, G ℓ| ≤ (∏ p ∈ markedPrimes x K a, ((p : ℝ) + 1)) * B := by
    calc
      _ ≤ ∑ ℓ, |G ℓ| := by simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ G
      _ ≤ ∑ _ℓ : LineData x K a, B := Finset.sum_le_sum (fun ℓ _ => hG ℓ)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, lineData_real_card]
  have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hD.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul] using hm

private lemma lineAverage_mono {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (G H : LineData x K a → ℝ) (hGH : ∀ ℓ, G ℓ ≤ H ℓ) :
    (lineAverage (fun ℓ => (G ℓ : ℂ))).re ≤ (lineAverage (fun ℓ => (H ℓ : ℂ))).re := by
  simp only [lineAverage_real]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun ℓ _ => hGH ℓ)) (by positivity)

private def normalizedObservableMean {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  (lineAverage (fun ℓ => (G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ : ℂ))).re

private lemma normalizedObservableMean_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ ℓ, Measurable (fun y : ℝ × ℝ × ℝ => G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ)) :
    Measurable (normalizedObservableMean F S G) := by
  unfold normalizedObservableMean
  simp_rw [lineAverage_real]
  exact measurable_const.mul (Finset.measurable_sum Finset.univ (fun ℓ _ => hG ℓ))

private lemma normalizedObservableMean_bound {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ w ℓ, |G w ℓ| ≤ B) : ∀ y, |normalizedObservableMean F S G y| ≤ B :=
  fun y => lineAverage_abs_bound _ B hB (fun ℓ => hG _ ℓ)

private lemma modelFunctional_eq_integral {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ ℓ, Measurable (fun y : ℝ × ℝ × ℝ => G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ w ℓ, |G w ℓ| ≤ B) :
    modelFunctional F S G = (6 / Real.pi ^ 2) *
      ∫ y, normalizedObservableMean F S G y ∂rootBoxMeasure := by
  exact congrArg (fun t : ℝ => (6 / Real.pi ^ 2) * t)
    (triple_integral_eq_rootBox _ (normalizedObservableMean_measurable F S G hG)
      B hB (normalizedObservableMean_bound F S G B hB hb))

private lemma modelFunctional_mono {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V)
    (G H : ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ ℓ, Measurable (fun y : ℝ × ℝ × ℝ => G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (hH : ∀ ℓ, Measurable (fun y : ℝ × ℝ × ℝ => H ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (BG BH : ℝ) (hBG : 0 ≤ BG) (hBH : 0 ≤ BH)
    (hbG : ∀ w ℓ, |G w ℓ| ≤ BG) (hbH : ∀ w ℓ, |H w ℓ| ≤ BH)
    (hGH : ∀ w : ArchRoot, w.InRegion S → ∀ ℓ, G w ℓ ≤ H w ℓ) :
    modelFunctional F S G ≤ modelFunctional F S H := by
  rw [modelFunctional_eq_integral F S G hG BG hBG hbG,
    modelFunctional_eq_integral F S H hH BH hBH hbH]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae
    (bounded_integrable _ _ (normalizedObservableMean_measurable F S G hG)
      BG hBG (normalizedObservableMean_bound F S G BG hBG hbG))
    (bounded_integrable _ _ (normalizedObservableMean_measurable F S H hH)
      BH hBH (normalizedObservableMean_bound F S H BH hBH hbH))
  exact rootBoxMeasure_ae_region.mono (fun y hy =>
    lineAverage_mono _ _ (hGH _ (normalized_root_in_region S hU hV _ _ _ hy.1 hy.2.1 hy.2.2)))

private lemma modelFunctional_finset_sum {K : ℕ} {ι : Type*} (F : PDFix K) (S : PDScale)
    (T : Finset ι) (G : ι → ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ i ∈ T, ∀ ℓ, Measurable (fun y : ℝ × ℝ × ℝ => G i ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (B : ι → ℝ) (hB : ∀ i ∈ T, 0 ≤ B i) (hb : ∀ i ∈ T, ∀ w ℓ, |G i w ℓ| ≤ B i) :
    modelFunctional F S (fun w ℓ => ∑ i ∈ T, G i w ℓ) = ∑ i ∈ T, modelFunctional F S (G i) := by
  classical
  have hm (y : ℝ × ℝ × ℝ) :
      normalizedObservableMean F S (fun w ℓ => ∑ i ∈ T, G i w ℓ) y =
        ∑ i ∈ T, normalizedObservableMean F S (G i) y := by
    simpa only [normalizedObservableMean, Complex.re_sum] using
      congrArg Complex.re (lineAverage_sum T (fun i ℓ => G i ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
  unfold modelFunctional
  change (6 / Real.pi ^ 2) * (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2,
    ∫ r in (0 : ℝ)..1, normalizedObservableMean F S (fun w ℓ => ∑ i ∈ T, G i w ℓ) (u,v,r)) = _
  simp_rw [hm]
  rw [triple_integral_finset_sum T (fun i => normalizedObservableMean F S (G i)) B
    (fun i hi => normalizedObservableMean_measurable F S (G i) (hG i hi)) hB
    (fun i hi => normalizedObservableMean_bound F S (G i) (B i) (hB i hi) (hb i hi)), Finset.mul_sum]
  rfl

private def RootBoxEstimate {K : ℕ} (F : PDFix K) (S : PDScale)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (E : ℝ) : Prop :=
  ∀ l₁ r₁ l₂ r₂ l₃ r₃ : ℝ,
    1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 16 → 1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 2 →
    0 ≤ l₃ → l₃ ≤ r₃ → r₃ ≤ 1 →
    |physicalFunctional F S (fun w ℓ =>
      if archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) -
      (6 / Real.pi ^ 2) * (r₁-l₁) * (r₂-l₂) * (r₃-l₃) *
        ∏ p ∈ J, ((p : ℝ) + 1)⁻¹| ≤ E

private lemma physicalFunctional_zero {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) : physicalFunctional F S (fun _ _ => 0) = 0 := by
  rw [physicalFunctional_eq_sum F S hU hV]
  simp

private lemma grid_first_face_mass {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (E c : ℝ) (hE : 0 ≤ E)
    (hbox : RootBoxEstimate F S J hJ lam E) :
    physicalFunctional F S (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
      (normalizedArch S w).1 = c ∧ assignedLines F S J hJ lam ℓ then 1 else 0) ≤ E := by
  classical
  by_cases hc : c ∈ Set.Icc (1 : ℝ) 16
  · have heq (w : ArchRoot) : normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).1 = c ↔
        archRectangle S c c 1 2 0 1 w := by
      let y := normalizedArch S w
      have hr : y ∈ rootRegion ∧ y.1 = c ↔ y.1 ∈ Set.Icc c c ∧ y.2.1 ∈ Set.Icc 1 2 ∧ y.2.2 ∈ Set.Icc 0 1 := by
        by_cases hy : y.1 = c
        · simp only [rootRegion, Set.mem_prod, Set.Icc_self, Set.mem_singleton_iff,
            hy, hc, true_and, and_true]
        · simp only [Set.Icc_self, Set.mem_singleton_iff, hy, and_false, false_and]
      dsimp only [y, normalizedArch] at hr
      simp only [archRectangle, Set.mem_Icc] at hr ⊢
      tauto
    have hfun : (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).1 = c ∧
        assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) =
        (fun w ℓ => if archRectangle S c c 1 2 0 1 w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) := by
      funext w ℓ
      have hp := heq w
      simp only [← and_assoc, hp]
    rw [hfun]
    have hb := hbox c c 1 2 0 1 hc.1 le_rfl hc.2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    simp only [sub_self, mul_zero, zero_mul, sub_zero] at hb
    exact (le_abs_self _).trans hb
  · have hz (w : ArchRoot) (ℓ : LineData S.x K F.a) :
        (if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).1 = c ∧
          assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) = 0 := by
      apply if_neg
      rintro ⟨hy, he, _⟩
      exact hc (he ▸ hy.1)
    simp_rw [hz]
    rw [physicalFunctional_zero F S hU hV]
    exact hE

private lemma grid_second_face_mass {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (E c : ℝ) (hE : 0 ≤ E)
    (hbox : RootBoxEstimate F S J hJ lam E) :
    physicalFunctional F S (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
      (normalizedArch S w).2.1 = c ∧ assignedLines F S J hJ lam ℓ then 1 else 0) ≤ E := by
  classical
  by_cases hc : c ∈ Set.Icc (1 : ℝ) 2
  · have heq (w : ArchRoot) : normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.1 = c ↔
        archRectangle S 1 16 c c 0 1 w := by
      let y := normalizedArch S w
      have hr : y ∈ rootRegion ∧ y.2.1 = c ↔ y.1 ∈ Set.Icc 1 16 ∧ y.2.1 ∈ Set.Icc c c ∧ y.2.2 ∈ Set.Icc 0 1 := by
        by_cases hy : y.2.1 = c
        · simp only [rootRegion, Set.mem_prod, Set.Icc_self, Set.mem_singleton_iff,
            hy, hc, true_and, and_true]
        · simp only [Set.Icc_self, Set.mem_singleton_iff, hy, and_false, false_and]
      dsimp only [y, normalizedArch] at hr
      simp only [archRectangle, Set.mem_Icc] at hr ⊢
      tauto
    have hfun : (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.1 = c ∧
        assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) =
        (fun w ℓ => if archRectangle S 1 16 c c 0 1 w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) := by
      funext w ℓ
      have hp := heq w
      simp only [← and_assoc, hp]
    rw [hfun]
    have hb := hbox 1 16 c c 0 1 (by norm_num) (by norm_num) (by norm_num) hc.1 le_rfl hc.2
      (by norm_num) (by norm_num) (by norm_num)
    simp only [sub_self, mul_zero, zero_mul, sub_zero] at hb
    exact (le_abs_self _).trans hb
  · have hz (w : ArchRoot) (ℓ : LineData S.x K F.a) :
        (if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.1 = c ∧
          assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) = 0 := by
      apply if_neg
      rintro ⟨hy, he, _⟩
      exact hc (he ▸ hy.2.1)
    simp_rw [hz]
    rw [physicalFunctional_zero F S hU hV]
    exact hE

private lemma grid_third_face_mass {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a)
    (lam : (p : ℕ) → Fin (p + 1)) (E c : ℝ) (hE : 0 ≤ E)
    (hbox : RootBoxEstimate F S J hJ lam E) :
    physicalFunctional F S (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
      (normalizedArch S w).2.2 = c ∧ assignedLines F S J hJ lam ℓ then 1 else 0) ≤ E := by
  classical
  by_cases hc : c ∈ Set.Icc (0 : ℝ) 1
  · have heq (w : ArchRoot) : normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.2 = c ↔
        archRectangle S 1 16 1 2 c c w := by
      let y := normalizedArch S w
      have hr : y ∈ rootRegion ∧ y.2.2 = c ↔ y.1 ∈ Set.Icc 1 16 ∧ y.2.1 ∈ Set.Icc 1 2 ∧ y.2.2 ∈ Set.Icc c c := by
        by_cases hy : y.2.2 = c
        · simp only [rootRegion, Set.mem_prod, Set.Icc_self, Set.mem_singleton_iff,
            hy, hc, true_and, and_true]
        · simp only [Set.Icc_self, Set.mem_singleton_iff, hy, and_false, false_and]
      dsimp only [y, normalizedArch] at hr
      simp only [archRectangle, Set.mem_Icc] at hr ⊢
      tauto
    have hfun : (fun w ℓ => if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.2 = c ∧
        assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) =
        (fun w ℓ => if archRectangle S 1 16 1 2 c c w ∧ assignedLines F S J hJ lam ℓ then 1 else 0) := by
      funext w ℓ
      have hp := heq w
      simp only [← and_assoc, hp]
    rw [hfun]
    have hb := hbox 1 16 1 2 c c (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hc.1 le_rfl hc.2
    simp only [sub_self, mul_zero, zero_mul, sub_zero] at hb
    exact (le_abs_self _).trans hb
  · have hz (w : ArchRoot) (ℓ : LineData S.x K F.a) :
        (if normalizedArch S w ∈ rootRegion ∧ (normalizedArch S w).2.2 = c ∧
          assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) = 0 := by
      apply if_neg
      rintro ⟨hy, he, _⟩
      exact hc (he ▸ hy.2.2)
    simp_rw [hz]
    rw [physicalFunctional_zero F S hU hV]
    exact hE

private lemma grid_cell_transfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (lam : (p : ℕ) → Fin (p + 1))
    (E : ℝ) (hE : 0 ≤ E) (hbox : RootBoxEstimate F S J hJ lam E)
    (hc₁ : max 1 ((k.1 : ℝ)*h) ≤ min 16 (((k.1 : ℝ)+1)*h))
    (hc₂ : max 1 ((k.2.1 : ℝ)*h) ≤ min 2 (((k.2.1 : ℝ)+1)*h))
    (hc₃ : max 0 ((k.2.2 : ℝ)*h) ≤ min 1 (((k.2.2 : ℝ)+1)*h)) :
    |physicalFunctional F S (fun w ℓ =>
        if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then 1 else 0) -
      modelFunctional F S (fun w ℓ =>
        if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then 1 else 0)| ≤ 4*E := by
  classical
  let A := fun w ℓ => if normalizedArch S w ∈ rootRegion ∧ normalizedArch S w ∈ gridCube h k ∧
    assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0
  let C := fun w ℓ => if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0
  let D₁ := fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
    (normalizedArch S w).1 = ((k.1 : ℝ)+1)*h ∧ assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0
  let D₂ := fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
    (normalizedArch S w).2.1 = ((k.2.1 : ℝ)+1)*h ∧ assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0
  let D₃ := fun w ℓ => if normalizedArch S w ∈ rootRegion ∧
    (normalizedArch S w).2.2 = ((k.2.2 : ℝ)+1)*h ∧ assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0
  have hd₁ (w ℓ) : 0 ≤ D₁ w ℓ := by dsimp [D₁]; split_ifs <;> norm_num
  have hd₂ (w ℓ) : 0 ≤ D₂ w ℓ := by dsimp [D₂]; split_ifs <;> norm_num
  have hd₃ (w ℓ) : 0 ≤ D₃ w ℓ := by dsimp [D₃]; split_ifs <;> norm_num
  have hdiff (w : ArchRoot) (ℓ : LineData S.x K F.a) :
      0 ≤ A w ℓ-C w ℓ ∧ A w ℓ-C w ℓ ≤ D₁ w ℓ+D₂ w ℓ+D₃ w ℓ := by
    by_cases hl : assignedLines F S J hJ lam ℓ
    · by_cases hc : normalizedArch S w ∈ gridCell h k
      · have hreg := hc.1
        have hcube := grid_cell_subset_cube h hh k hc
        have hz : A w ℓ-C w ℓ = 0 := by simp [A,C,hl,hc,hreg,hcube]
        rw [hz]
        exact ⟨le_rfl, by linarith [hd₁ w ℓ,hd₂ w ℓ,hd₃ w ℓ]⟩
      · by_cases ha : normalizedArch S w ∈ rootRegion ∧ normalizedArch S w ∈ gridCube h k
        · have hz : A w ℓ-C w ℓ = 1 := by simp [A,C,hl,hc,ha.1,ha.2]
          rw [hz]
          refine ⟨by norm_num, ?_⟩
          obtain (hf|hf|hf) := grid_cell_excluded_face h hh k _ ha.1 ha.2 hc
          · have he : D₁ w ℓ=1 := by simp [D₁,ha.1,hf,hl]
            linarith [hd₂ w ℓ,hd₃ w ℓ]
          · have he : D₂ w ℓ=1 := by simp [D₂,ha.1,hf,hl]
            linarith [hd₁ w ℓ,hd₃ w ℓ]
          · have he : D₃ w ℓ=1 := by simp [D₃,ha.1,hf,hl]
            linarith [hd₁ w ℓ,hd₂ w ℓ]
        · have hz : A w ℓ-C w ℓ=0 := by simp [A,C,hl,hc,ha]
          rw [hz]
          exact ⟨le_rfl, by linarith [hd₁ w ℓ,hd₂ w ℓ,hd₃ w ℓ]⟩
    · simp [A,C,D₁,D₂,D₃,hl]
  have hPD₁ : physicalFunctional F S D₁ ≤ E := grid_first_face_mass F S hU hV J hJ lam E _ hE hbox
  have hPD₂ : physicalFunctional F S D₂ ≤ E := grid_second_face_mass F S hU hV J hJ lam E _ hE hbox
  have hPD₃ : physicalFunctional F S D₃ ≤ E := grid_third_face_mass F S hU hV J hJ lam E _ hE hbox
  have hzero := physicalFunctional_mono F S hU hV (fun _ _ => 0) (fun w ℓ => A w ℓ-C w ℓ)
    (fun w ℓ => (hdiff w ℓ).1)
  rw [physicalFunctional_zero F S hU hV, physicalFunctional_sub F S hU hV] at hzero
  have hup := physicalFunctional_mono F S hU hV (fun w ℓ => A w ℓ-C w ℓ)
    (fun w ℓ => D₁ w ℓ+D₂ w ℓ+D₃ w ℓ) (fun w ℓ => (hdiff w ℓ).2)
  have hadd : physicalFunctional F S (fun w ℓ => D₁ w ℓ+D₂ w ℓ+D₃ w ℓ) =
      physicalFunctional F S D₁+physicalFunctional F S D₂+physicalFunctional F S D₃ := by
    simp_rw [physicalFunctional_eq_sum F S hU hV]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    ring
  rw [physicalFunctional_sub F S hU hV,hadd] at hup
  have hdist : |physicalFunctional F S C-physicalFunctional F S A| ≤ 3*E := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  let l₁ := max 1 ((k.1 : ℝ)*h)
  let r₁ := min 16 (((k.1 : ℝ)+1)*h)
  let l₂ := max 1 ((k.2.1 : ℝ)*h)
  let r₂ := min 2 (((k.2.1 : ℝ)+1)*h)
  let l₃ := max 0 ((k.2.2 : ℝ)*h)
  let r₃ := min 1 (((k.2.2 : ℝ)+1)*h)
  have hfun : A = (fun w ℓ => if archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧
      assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) := by
    funext w ℓ
    have hp := grid_closed_clipped h k (normalizedArch S w)
    dsimp only [normalizedArch] at hp
    have he : normalizedArch S w ∈ rootRegion ∧ normalizedArch S w ∈ gridCube h k ↔
        archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w := by
      simp only [archRectangle,Set.mem_Icc] at hp ⊢
      exact hp.trans (by tauto)
    dsimp only [A]
    simp only [← and_assoc,he]
  have hvol : gridCellVolume h k=(r₁-l₁)*(r₂-l₂)*(r₃-l₃) := by
    unfold gridCellVolume
    rw [min_comm (((k.1 : ℝ)+1)*h) 16,max_comm ((k.1 : ℝ)*h) 1,
      min_comm (((k.2.1 : ℝ)+1)*h) 2,max_comm ((k.2.1 : ℝ)*h) 1,
      min_comm (((k.2.2 : ℝ)+1)*h) 1,max_comm ((k.2.2 : ℝ)*h) 0]
    simp only [max_eq_right (sub_nonneg.mpr hc₁),max_eq_right (sub_nonneg.mpr hc₂),
      max_eq_right (sub_nonneg.mpr hc₃)]
    rfl
  have hb := hbox l₁ r₁ l₂ r₂ l₃ r₃ (le_max_left _ _) hc₁ (min_le_left _ _)
    (le_max_left _ _) hc₂ (min_le_left _ _) (le_max_left _ _) hc₃ (min_le_left _ _)
  have hmain : (6/Real.pi^2)*(r₁-l₁)*(r₂-l₂)*(r₃-l₃)*∏ p∈J,((p:ℝ)+1)⁻¹ =
      (6/Real.pi^2)*gridCellVolume h k*∏ p∈J,((p:ℝ)+1)⁻¹ := by rw [hvol]; ring
  have hclosed : |physicalFunctional F S A-(6/Real.pi^2)*gridCellVolume h k*
      ∏ p∈J,((p:ℝ)+1)⁻¹| ≤ E := by rw [hfun,←hmain]; exact hb
  change |physicalFunctional F S C-modelFunctional F S C| ≤ _
  rw [grid_cell_model_average F S hU hV h hh k J hJ lam]
  calc
    _ = |(physicalFunctional F S C-physicalFunctional F S A)+
        (physicalFunctional F S A-(6/Real.pi^2)*gridCellVolume h k*∏ p∈J,((p:ℝ)+1)⁻¹)| := by congr 1; ring
    _ ≤ |physicalFunctional F S C-physicalFunctional F S A|+
        |physicalFunctional F S A-(6/Real.pi^2)*gridCellVolume h k*∏ p∈J,((p:ℝ)+1)⁻¹| := abs_add_le _ _
    _ ≤ 4*E := by linarith

private lemma modelFunctional_zero {K : ℕ} (F : PDFix K) (S : PDScale) :
    modelFunctional F S (fun _ _ => 0)=0 := by simp [modelFunctional,lineAverage]

private lemma grid_cell_transfer_all {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (lam : (p : ℕ) → Fin (p + 1))
    (E : ℝ) (hE : 0 ≤ E) (hbox : RootBoxEstimate F S J hJ lam E) :
    |physicalFunctional F S (fun w ℓ =>
        if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then 1 else 0) -
      modelFunctional F S (fun w ℓ =>
        if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then 1 else 0)| ≤ 4*E := by
  classical
  by_cases hcell : (gridCell h k).Nonempty
  · obtain ⟨y,hy⟩ := hcell
    have hclip := (grid_closed_clipped h k y).1 ⟨hy.1,grid_cell_subset_cube h hh k hy⟩
    exact grid_cell_transfer F S hU hV h hh k J hJ lam E hE hbox
      (hclip.1.1.trans hclip.1.2) (hclip.2.1.1.trans hclip.2.1.2)
      (hclip.2.2.1.trans hclip.2.2.2)
  · have hz : (fun (w : ArchRoot) (ℓ : LineData S.x K F.a) =>
        if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) =
        (fun _ _ => 0) := by
      funext w ℓ
      apply if_neg
      exact fun hc => hcell ⟨_,hc.1⟩
    rw [hz,physicalFunctional_zero F S hU hV,modelFunctional_zero F S]
    simpa using mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hE

private lemma gridOwner_measurable (h : ℝ) : Measurable (gridOwner h) :=
  (Int.measurable_floor.comp (measurable_fst.div_const h)).prodMk
    ((Int.measurable_floor.comp (measurable_fst.comp measurable_snd |>.div_const h)).prodMk
      (Int.measurable_floor.comp (measurable_snd.comp measurable_snd |>.div_const h)))

private lemma gridCell_measurableSet (h : ℝ) (k : ℤ × ℤ × ℤ) : MeasurableSet (gridCell h k) :=
  (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)).inter
    ((measurableSet_singleton k).preimage (gridOwner_measurable h))

private lemma cell_indicator_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (h : ℝ) (k : ℤ × ℤ × ℤ)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (lam : (p : ℕ) → Fin (p + 1))
    (ℓ : LineData S.x K F.a) : Measurable (fun y : ℝ × ℝ × ℝ =>
      if normalizedArch S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ∈ gridCell h k ∧
        assignedLines F S J hJ lam ℓ then (1 : ℝ) else 0) := by
  classical
  simp only [normalized_arch_point S hU hV]
  by_cases hl : assignedLines F S J hJ lam ℓ
  · simp only [hl,and_true]
    exact Measurable.ite (gridCell_measurableSet h k) measurable_const measurable_const
  · simpa only [hl,and_false,if_false] using (measurable_const : Measurable (fun _ : ℝ×ℝ×ℝ => (0:ℝ)))

private abbrev LocalLineData (J : Finset ℕ) := (p : {p : ℕ // p ∈ J}) → Fin (p.1+1)

private def restrictLines {K : ℕ} (F : PDFix K) (S : PDScale) (J : Finset ℕ)
    (hJ : J ⊆ markedPrimes S.x K F.a) (ℓ : LineData S.x K F.a) : LocalLineData J :=
  fun p => ℓ ⟨p.1,hJ p.2⟩

private def extendLines (J : Finset ℕ) (lam : LocalLineData J) : (p : ℕ) → Fin (p+1) :=
  fun p => if hp : p∈J then lam ⟨p,hp⟩ else 0

private lemma assignedLines_extend {K : ℕ} (F : PDFix K) (S : PDScale) (J : Finset ℕ)
    (hJ : J ⊆ markedPrimes S.x K F.a) (lam : LocalLineData J) (ℓ : LineData S.x K F.a) :
    assignedLines F S J hJ (extendLines J lam) ℓ ↔ restrictLines F S J hJ ℓ=lam := by
  constructor
  · intro h
    funext p
    simpa only [extendLines,restrictLines,dif_pos p.2] using h p.1 p.2
  · intro h p hp
    have he := congrFun h ⟨p,hp⟩
    simpa only [extendLines,restrictLines,dif_pos hp] using he

private lemma localLineData_card (J : Finset ℕ) :
    (Fintype.card (LocalLineData J) : ℝ)=∏ p∈J,((p:ℝ)+1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  exact Finset.prod_attach J (fun p : ℕ => (p:ℝ)+1)

private lemma restricted_line_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (f : LocalLineData J → ℝ)
    (ℓ : LineData S.x K F.a) :
    f (restrictLines F S J hJ ℓ) = ∑ lam : LocalLineData J,
      if assignedLines F S J hJ (extendLines J lam) ℓ then f lam else 0 := by
  classical
  simp only [assignedLines_extend]
  simp

private lemma modelFunctional_mul_const {K : ℕ} (F : PDFix K) (S : PDScale)
    (c : ℝ) (G : ArchRoot → LineData S.x K F.a → ℝ) :
    modelFunctional F S (fun w ℓ => c*G w ℓ)=c*modelFunctional F S G := by
  unfold modelFunctional
  simp_rw [lineAverage_real,←Finset.mul_sum]
  have he (u v r : ℝ) : (∏ p∈markedPrimes S.x K F.a,((p:ℝ)+1))⁻¹ *
      (c*∑ ℓ, G ⟨S.U*u,S.V*v,r⟩ ℓ) =
      c*((∏ p∈markedPrimes S.x K F.a,((p:ℝ)+1))⁻¹ *∑ ℓ,G ⟨S.U*u,S.V*v,r⟩ ℓ) := by ring
  simp_rw [he,intervalIntegral.integral_const_mul]
  ring

private lemma weighted_grid_cell_transfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0 < S.U) (hV : 0 < S.V) (h : ℝ) (hh : 0 < h) (k : ℤ × ℤ × ℤ)
    (J : Finset ℕ) (hJ : J ⊆ markedPrimes S.x K F.a) (f : LocalLineData J → ℝ)
    (hf : ∀ lam, 0 ≤ f lam ∧ f lam ≤ 1) (E : ℝ) (hE : 0 ≤ E)
    (hbox : ∀ lam : (p : ℕ) → Fin (p+1), RootBoxEstimate F S J hJ lam E) :
    |physicalFunctional F S (fun w ℓ => if normalizedArch S w ∈ gridCell h k then f (restrictLines F S J hJ ℓ) else 0) -
      modelFunctional F S (fun w ℓ => if normalizedArch S w ∈ gridCell h k then f (restrictLines F S J hJ ℓ) else 0)| ≤
      4*E*∏ p∈J,((p:ℝ)+1) := by
  classical
  let B := fun lam : LocalLineData J => fun w ℓ =>
    if normalizedArch S w ∈ gridCell h k ∧ assignedLines F S J hJ (extendLines J lam) ℓ then (1:ℝ) else 0
  let G := fun lam : LocalLineData J => fun w ℓ => f lam*B lam w ℓ
  have hG (lam) (ℓ) : Measurable (fun y : ℝ×ℝ×ℝ => G lam ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) :=
    measurable_const.mul (cell_indicator_measurable F S hU hV h k J hJ (extendLines J lam) ℓ)
  have hb (lam) (w) (ℓ) : |G lam w ℓ| ≤ 1 := by
    dsimp [G,B]
    split_ifs
    · simpa only [mul_one,abs_of_nonneg (hf lam).1] using (hf lam).2
    · norm_num
  have hfun : (fun w ℓ => if normalizedArch S w ∈ gridCell h k then f (restrictLines F S J hJ ℓ) else 0) =
      (fun w ℓ => ∑ lam : LocalLineData J,G lam w ℓ) := by
    funext w ℓ
    by_cases hc : normalizedArch S w ∈ gridCell h k
    · simp only [if_pos hc,G,B,hc,true_and]
      rw [restricted_line_expansion F S J hJ f ℓ]
      apply Finset.sum_congr rfl
      intro lam hlam
      split_ifs <;> simp
    · simp [G,B,hc]
  rw [hfun,physicalFunctional_finset_sum F S hU hV,
    modelFunctional_finset_sum F S Finset.univ G (fun lam _ => hG lam) (fun _ => 1)
      (fun _ _ => by norm_num) (fun lam _ => hb lam),←Finset.sum_sub_distrib]
  have hterms (lam : LocalLineData J) :
      |physicalFunctional F S (G lam)-modelFunctional F S (G lam)| ≤ 4*E := by
    rw [physicalFunctional_mul_const F S hU hV,modelFunctional_mul_const F S,
      ←mul_sub,abs_mul,abs_of_nonneg (hf lam).1]
    have ht := grid_cell_transfer_all F S hU hV h hh k J hJ (extendLines J lam) E hE (hbox _)
    exact (mul_le_mul_of_nonneg_left ht (hf lam).1).trans
      (by nlinarith [hf lam])
  calc
    _ ≤ ∑ lam : LocalLineData J,|physicalFunctional F S (G lam)-modelFunctional F S (G lam)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (fun lam =>
        physicalFunctional F S (G lam)-modelFunctional F S (G lam))
    _ ≤ ∑ _lam : LocalLineData J,4*E := Finset.sum_le_sum (fun lam _ => hterms lam)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,localLineData_card]; ring

private lemma prime_set_product_squarefree (J : Finset ℕ) (hp : ∀ p∈J,p.Prime) :
    Squarefree (∏ p∈J,p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hpJ q hqJ hpq => ?_)
    (fun p hpJ => (hp p hpJ).squarefree)
  change IsRelPrime p q
  rw [←Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hp p hpJ) (hp q hqJ)).mpr hpq

private lemma root_box_estimate_eventually (δ C_K : ℝ) (hδ : 0<δ) (hCK : 0<C_K) :
    ∃ C_R x₀ : ℝ, 0<C_R ∧ 2≤x₀ ∧
      ∀ (K : ℕ) (F : PDFix K) (S : PDScale) (c₁ c₂ : ℝ),
        S.Valid K δ c₁ c₂ → x₀≤S.x →
        ∀ J : Finset ℕ, ∀ hJ : J⊆markedPrimes S.x K F.a,
          ((∏ p∈J,p : ℕ) : ℝ) ≤ Real.exp (C_K*Real.rpow S.L (98/100:ℝ)) →
          ∀ lam : (p : ℕ) → Fin (p+1),
            RootBoxEstimate F S J hJ lam (C_R*Real.rpow S.x (-(δ/1000))) := by
  classical
  obtain ⟨c,C_R,x₀,hc,hCR,hx₀,hcount⟩ := root_lines δ C_K hδ hCK
  refine ⟨C_R,x₀,hCR,hx₀,?_⟩
  intro K F S c₁ c₂ hS hx J hJ hmod lam
  obtain ⟨hYpos,hUpos,hd⟩ := pdScale_positive S δ c₁ c₂ hδ hS
  have hxpos : 0<S.x := by linarith [hS.1]
  have hHmpos : 0<S.Hm := (Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.1
  have hVpos : 0<S.V := (Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.2.1
  have hY : 1≤S.Y := by
    obtain ⟨hm,_⟩ := Finset.mem_filter.mp hS.2.2.2.2.2.1
    obtain ⟨n,_,hn⟩ := Finset.mem_image.mp hm
    rw [←hn]
    exact one_le_pow₀ (by norm_num)
  have hdR : (1:ℝ)≤S.d₀ := by exact_mod_cast hd
  have hH : 1≤S.H := by
    have hm := mul_le_mul hdR hY (by norm_num : (0:ℝ)≤1) (Nat.cast_nonneg S.d₀)
    simpa only [one_mul,PDScale.H] using hm
  have hU : Real.rpow S.x δ≤S.U := hS.2.1.trans (by
    change S.Hm≤S.H*S.Hm
    have hm := mul_le_mul_of_nonneg_right hH hHmpos.le
    simpa only [one_mul] using hm)
  have hp (p : ℕ) (hpJ : p∈J) : p.Prime := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp (hJ hpJ)
    exact (Finset.mem_filter.mp hpi).2.1
  let Sq := ∏ p∈J,p
  have hSq : Squarefree Sq := prime_set_product_squarefree J hp
  have hSqpos : 0<Sq := Finset.prod_pos (fun p hpJ => (hp p hpJ).pos)
  have hpf : Sq.primeFactors=J := Nat.primeFactors_prod hp
  intro l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hle₁ hr₁ hl₂ hle₂ hr₂ hl₃ hle₃ hr₃
  have hb := hcount S.x hx S.U S.V hU hS.2.2.1 Sq hSq hSqpos hmod lam
    l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hle₁ hr₁ hl₂ hle₂ hr₂ hl₃ hle₃ hr₃
  rw [hpf] at hb
  change |physicalFunctional F S (fun w ℓ =>
    if archRectangle S l₁ r₁ l₂ r₂ l₃ r₃ w ∧ assignedLines F S J hJ lam ℓ then 1 else 0)-
      (6/Real.pi^2)*(r₁-l₁)*(r₂-l₂)*(r₃-l₃)*∏ p∈J,((p:ℝ)+1)⁻¹| ≤ _
  rw [rectangle_root_count F S hUpos hVpos J hJ lam l₁ r₁ l₂ r₂ l₃ r₃ hl₁ hr₁ hl₂ hr₂ hl₃ hr₃]
  have hUV : 0<S.U*S.V := mul_pos hUpos hVpos
  have heq (n : ℝ) : (S.U*S.V)⁻¹*n-(6/Real.pi^2)*(r₁-l₁)*(r₂-l₂)*(r₃-l₃)*∏ p∈J,((p:ℝ)+1)⁻¹ =
      (S.U*S.V)⁻¹*(n-S.U*S.V*(r₁-l₁)*(r₂-l₂)*(r₃-l₃)*(6/Real.pi^2)*∏ p∈J,((p:ℝ)+1)⁻¹) := by
    field_simp [hUpos.ne',hVpos.ne']
    <;> ring
  rw [heq,abs_mul,abs_of_nonneg (inv_nonneg.mpr hUV.le)]
  have hm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hUV.le)
  have hright : (S.U*S.V)⁻¹*(C_R*S.U*S.V*Real.rpow S.x (-c)) =
      C_R*Real.rpow S.x (-(δ/1000)) := by
    rw [hc]
    field_simp [hUpos.ne',hVpos.ne']
    <;> ring
  exact hright ▸ hm

private lemma modelFunctional_sub {K : ℕ} (F : PDFix K) (S : PDScale)
    (G H : ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ ℓ,Measurable (fun y : ℝ×ℝ×ℝ => G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (hH : ∀ ℓ,Measurable (fun y : ℝ×ℝ×ℝ => H ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (BG BH : ℝ) (hBG : 0≤BG) (hBH : 0≤BH)
    (hbG : ∀ w ℓ,|G w ℓ|≤BG) (hbH : ∀ w ℓ,|H w ℓ|≤BH) :
    modelFunctional F S (fun w ℓ => G w ℓ-H w ℓ)=modelFunctional F S G-modelFunctional F S H := by
  have hsub (w ℓ) : |G w ℓ-H w ℓ|≤BG+BH := by
    have ha := abs_add_le (G w ℓ) (-(H w ℓ))
    rw [abs_neg] at ha
    rw [←sub_eq_add_neg] at ha
    linarith [hbG w ℓ,hbH w ℓ]
  have hm : normalizedObservableMean F S (fun w ℓ => G w ℓ-H w ℓ) =
      fun y => normalizedObservableMean F S G y-normalizedObservableMean F S H y := by
    funext y
    unfold normalizedObservableMean
    simp only [lineAverage_real,Finset.sum_sub_distrib,mul_sub]
  rw [modelFunctional_eq_integral F S (fun w ℓ => G w ℓ-H w ℓ)
      (fun ℓ => (hG ℓ).sub (hH ℓ)) (BG+BH) (add_nonneg hBG hBH) hsub,
    modelFunctional_eq_integral F S G hG BG hBG hbG,
    modelFunctional_eq_integral F S H hH BH hBH hbH,hm,
    integral_sub (bounded_integrable _ _ (normalizedObservableMean_measurable F S G hG)
      BG hBG (normalizedObservableMean_bound F S G BG hBG hbG))
      (bounded_integrable _ _ (normalizedObservableMean_measurable F S H hH)
      BH hBH (normalizedObservableMean_bound F S H BH hBH hbH))]
  ring

private lemma physicalFunctional_mono_region {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (G H : ArchRoot → LineData S.x K F.a → ℝ)
    (hGH : ∀ w : ArchRoot,w.InRegion S → ∀ ℓ,G w ℓ≤H w ℓ) :
    physicalFunctional F S G≤physicalFunctional F S H := by
  rw [physicalFunctional_eq_sum F S hU hV,physicalFunctional_eq_sum F S hU hV]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro uv huv
  exact hGH _ (physical_root_in_region S hU uv.1 uv.2
    ((Set.Finite.mem_toFinset (omega_positions_finite S hU hV)).1 huv)) _

private lemma arch_in_region_normalized (S : PDScale) (hU : 0<S.U) (hV : 0<S.V)
    (w : ArchRoot) (hw : w.InRegion S) : normalizedArch S w∈rootRegion := by
  refine ⟨⟨?_,?_⟩,⟨⟨?_,?_⟩,⟨hw.2.2.2.2.1,hw.2.2.2.2.2⟩⟩⟩
  · exact (le_div_iff₀ hU).2 (by simpa using hw.1)
  · exact (div_le_iff₀ hU).2 hw.2.1
  · exact (le_div_iff₀ hV).2 (by simpa using hw.2.2.1)
  · exact (div_le_iff₀ hV).2 hw.2.2.2.1

private def weightedGridFunction {K : ℕ} (F : PDFix K) (S : PDScale) (h : ℝ)
    (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (f : (ℤ×ℤ×ℤ) → LocalLineData J → ℝ) (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℝ :=
  ∑ k∈gridIndices h,if normalizedArch S w∈gridCell h k then f k (restrictLines F S J hJ ℓ) else 0

private lemma weighted_cell_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (k : ℤ×ℤ×ℤ)
    (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a) (f : LocalLineData J → ℝ)
    (ℓ : LineData S.x K F.a) : Measurable (fun y : ℝ×ℝ×ℝ =>
      if normalizedArch S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩∈gridCell h k then f (restrictLines F S J hJ ℓ) else 0) := by
  simp only [normalized_arch_point S hU hV]
  exact Measurable.ite (gridCell_measurableSet h k) measurable_const measurable_const

private lemma weightedGridFunction_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (f : (ℤ×ℤ×ℤ) → LocalLineData J → ℝ) (ℓ : LineData S.x K F.a) :
    Measurable (fun y : ℝ×ℝ×ℝ => weightedGridFunction F S h J hJ f ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) :=
  Finset.measurable_sum (gridIndices h) (fun k _ => weighted_cell_measurable F S hU hV h k J hJ (f k) ℓ)

private lemma weightedGridFunction_eval {K : ℕ} (F : PDFix K) (S : PDScale)
    (h : ℝ) (hh : 0<h) (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (f : (ℤ×ℤ×ℤ) → LocalLineData J → ℝ) (w : ArchRoot) (ℓ : LineData S.x K F.a)
    (hw : normalizedArch S w∈rootRegion) :
    weightedGridFunction F S h J hJ f w ℓ = f (gridOwner h (normalizedArch S w)) (restrictLines F S J hJ ℓ) :=
  grid_cell_partition h hh _ hw (fun k => f k (restrictLines F S J hJ ℓ))

private lemma weightedGridFunction_bounds {K : ℕ} (F : PDFix K) (S : PDScale)
    (h : ℝ) (hh : 0<h) (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (f : (ℤ×ℤ×ℤ) → LocalLineData J → ℝ)
    (hf : ∀ k∈gridIndices h,∀ lam,0≤f k lam ∧ f k lam≤1) :
    ∀ w ℓ,0≤weightedGridFunction F S h J hJ f w ℓ ∧ weightedGridFunction F S h J hJ f w ℓ≤1 := by
  classical
  intro w ℓ
  by_cases hw : normalizedArch S w∈rootRegion
  · rw [weightedGridFunction_eval F S h hh J hJ f w ℓ hw]
    exact hf _ (grid_owner_mem h hh _ hw) _
  · have hz : weightedGridFunction F S h J hJ f w ℓ=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (fun hc => hw hc.1)
    simp only [hz,le_refl,zero_le_one,and_self]

private lemma weighted_grid_sum_transfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (hh : 0<h)
    (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (f : (ℤ×ℤ×ℤ) → LocalLineData J → ℝ)
    (hf : ∀ k∈gridIndices h,∀ lam,0≤f k lam ∧ f k lam≤1)
    (E : ℝ) (hE : 0≤E)
    (hbox : ∀ lam : (p : ℕ) → Fin (p+1),RootBoxEstimate F S J hJ lam E) :
    |physicalFunctional F S (weightedGridFunction F S h J hJ f)-
      modelFunctional F S (weightedGridFunction F S h J hJ f)| ≤
      ((gridIndices h).card : ℝ)*(4*E*∏ p∈J,((p:ℝ)+1)) := by
  classical
  let G := fun k : ℤ×ℤ×ℤ => fun w ℓ =>
    if normalizedArch S w∈gridCell h k then f k (restrictLines F S J hJ ℓ) else 0
  have hm (k) (ℓ) : Measurable (fun y : ℝ×ℝ×ℝ => G k ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) :=
    weighted_cell_measurable F S hU hV h k J hJ (f k) ℓ
  have hb (k) (hk : k∈gridIndices h) (w) (ℓ) : |G k w ℓ|≤1 := by
    dsimp [G]
    split_ifs
    · simpa only [abs_of_nonneg (hf k hk _).1] using (hf k hk _).2
    · norm_num
  unfold weightedGridFunction
  rw [physicalFunctional_finset_sum F S hU hV,
    modelFunctional_finset_sum F S (gridIndices h) G (fun k _ => hm k) (fun _ => 1)
      (fun _ _ => by norm_num) hb,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k∈gridIndices h,|physicalFunctional F S (G k)-modelFunctional F S (G k)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (gridIndices h) (fun k =>
        physicalFunctional F S (G k)-modelFunctional F S (G k))
    _ ≤ ∑ _k∈gridIndices h,4*E*∏ p∈J,((p:ℝ)+1) := Finset.sum_le_sum (fun k hk =>
      weighted_grid_cell_transfer F S hU hV h hh k J hJ (f k) (hf k hk) E hE hbox)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

private lemma expectation_sandwich (a b lP uP lM uM E B : ℝ)
    (hlP : lP≤a) (huP : a≤uP) (hlM : lM≤b) (huM : b≤uM)
    (hl : |lP-lM|≤E) (hu : |uP-uM|≤E) (hgap : uM-lM≤B) : |a-b|≤B+E := by
  obtain ⟨hl₁,hl₂⟩ := abs_le.mp hl
  obtain ⟨hu₁,hu₂⟩ := abs_le.mp hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private lemma contributing_tube_eventually {K : ℕ} (δ c₁ c₂ : ℝ) (hδ : 0<δ)
    (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ,2≤x₀ ∧ ∀ S : PDScale,S.Valid K δ c₁ c₂ → x₀≤S.x →
      ∀ γ : EnvPath S.x K,IsContributingPath F S γ →
      ∀ j : Fin (pathLength S.x+1),
        |((γ j).1.1 : ℝ)|≤Real.exp (Real.rpow S.L (1/2:ℝ)) ∧
        |((γ j).1.2 : ℝ)|≤Real.exp (Real.rpow S.L (1/2:ℝ)) := by
  obtain ⟨Bψ,hBψ,hpsi⟩ := pdfix_psi_abs_bound F hF
  let k : ℝ := ((K+1 : ℕ) : ℝ)
  let C : ℝ := 2048*Bψ+23+2*k
  obtain ⟨L₀,hL₀,hsmall⟩ := eventually_const_rpow_le C (21/100) (1/2) (by norm_num)
  refine ⟨max 2 (Real.exp L₀),le_max_left _ _,?_⟩
  intro S hS hx γ hγ j
  have hxpos : 0<S.x := by linarith [hS.1]
  have hL : L₀≤S.L := (Real.le_log_iff_exp_le hxpos).2 ((le_max_right _ _).trans hx)
  have hL1 : 1≤S.L := hL₀.trans hL
  have hLpos : 0<S.L := by linarith
  let W := Real.rpow S.L (21/100:ℝ)
  have hW : 1≤W := by
    simpa [W] using Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0:ℝ)≤21/100)
  obtain ⟨hN,hM,hd,hY,hP⟩ := budget_scale_bounds F S δ c₁ c₂ hF hS hL1
  have hY' : S.Y≤Real.exp (k*W) := hY.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1/5:ℝ)≤21/100))
      (Nat.cast_nonneg (K+1))))
  have hlog : Real.log S.L≤W/(21/100:ℝ) := Real.log_le_rpow_div hLpos.le (by norm_num)
  have hsqrt : Real.rpow S.L (1/2:ℝ)≤Real.exp (3*W) := by
    calc
      _ = Real.exp (Real.log S.L*(1/2:ℝ)) := Real.rpow_def_of_pos hLpos (1/2)
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hLpos.le (21/100:ℝ)])
  have hN' : (pathLength S.x : ℝ)≤4*Real.exp (3*W) := by nlinarith
  have hYpos : 0<S.Y := (pdScale_positive S δ c₁ c₂ hδ hS).1
  have hprod : 512*(pathLength S.x : ℝ)*Bψ*(S.d₀ : ℝ)*S.Y≤
      Real.exp ((2048*Bψ+4+2*k)*W) := by
    calc
      _ ≤ 512*(4*Real.exp (3*W))*Bψ*Real.exp (k*W)*Real.exp (k*W) := by gcongr
      _ = 2048*Bψ*Real.exp ((3+2*k)*W) := by
        rw [show (3+2*k)*W=3*W+k*W+k*W by ring,Real.exp_add,Real.exp_add]
        ring
      _ ≤ Real.exp ((2048*Bψ+1)*W)*Real.exp ((3+2*k)*W) :=
        mul_le_mul_of_nonneg_right (constant_exp_bound (2048*Bψ) W (by positivity) hW) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have h16 : (16:ℝ)≤Real.exp (17*W) := by
    simpa only [show (16:ℝ)+1=17 by norm_num] using constant_exp_bound 16 W (by norm_num) hW
  have hB := sum_exp_bound 16 (512*(pathLength S.x : ℝ)*Bψ*(S.d₀ : ℝ)*S.Y)
    17 (2048*Bψ+4+2*k) W (by norm_num) (by dsimp [k];positivity) hW h16 hprod
  have hExp : 16+512*(pathLength S.x : ℝ)*Bψ*(S.d₀ : ℝ)*S.Y≤Real.exp (Real.rpow S.L (1/2:ℝ)) := by
    apply hB.trans
    apply Real.exp_le_exp.mpr
    convert hsmall S.L hL using 1 <;> dsimp [C,W] <;> ring
  obtain ⟨B,hBeq,hB0,hcoords⟩ := contributing_coordinate_bound F S δ c₁ c₂ Bψ hδ hBψ hpsi hS
  obtain ⟨hc1,hc2⟩ := hcoords γ hγ j
  rw [hBeq] at hc1 hc2
  exact ⟨hc1.trans hExp,hc2.trans hExp⟩

private lemma contributing_path_boundary_eventually (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hc₁ : 0<c₁)
    {K : ℕ} (F : PDFix K) (hF : F.Valid) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ x₀ : ℝ,2≤x₀ ∧ ∀ S : PDScale,S.Valid K δ c₁ c₂ → x₀≤S.x →
      ∀ γ : EnvPath S.x K,IsContributingPath F S γ →
      (((gridIndices (Real.rpow S.x (-ε))).filter fun k => IsNonconstantOn (fun y =>
        ∀ j,envBox S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ (γ j).1 ∧
          envGood F S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ (γ j))
        (gridCube (Real.rpow S.x (-ε)) k)).card : ℝ) ≤
      ((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (2*ε) := by
  obtain ⟨xT,hxT,hTube⟩ := contributing_tube_eventually δ c₁ c₂ hδ F hF
  obtain ⟨xB,hxB,hBoundary⟩ := root_arch_boundary δ c₁ c₂ hδ hc₁ K F hF ε hε hε1
  refine ⟨max xT xB,hxT.trans (le_max_left _ _),?_⟩
  intro S hS hx γ hγ
  have hcoords := hTube S hS ((le_max_left _ _).trans hx) γ hγ
  have hb := path_boundary_card F S γ (Real.rpow S.x (-ε))
    (Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (2*ε))
    (fun j => hBoundary S hS ((le_max_right _ _).trans hx) (γ j) (hγ.1.1 j)
      (hcoords j).1 (hcoords j).2)
  simpa only [mul_assoc] using hb

private def gridBadCells (h : ℝ) (P : ℝ×ℝ×ℝ → Prop) : Finset (ℤ×ℤ×ℤ) :=
  (gridIndices h).filter fun k => IsNonconstantOn P (gridCube h k)

private def gridTruth (h : ℝ) (P : ℝ×ℝ×ℝ → Prop) (k : ℤ×ℤ×ℤ) : ℝ :=
  if ∃ y∈gridCube h k,P y then 1 else 0

private def gridLowerWeights {J : Finset ℕ} (h : ℝ) (P : ℝ×ℝ×ℝ → Prop)
    (f : LocalLineData J → ℝ) (k : ℤ×ℤ×ℤ) (lam : LocalLineData J) : ℝ :=
  if k∈gridBadCells h P then 0 else gridTruth h P k*f lam

private def gridUpperWeights {J : Finset ℕ} (h : ℝ) (P : ℝ×ℝ×ℝ → Prop)
    (f : LocalLineData J → ℝ) (k : ℤ×ℤ×ℤ) (lam : LocalLineData J) : ℝ :=
  if k∈gridBadCells h P then 1 else gridTruth h P k*f lam

private lemma gridTruth_bounds (h : ℝ) (P : ℝ×ℝ×ℝ → Prop) (k : ℤ×ℤ×ℤ) :
    0≤gridTruth h P k ∧ gridTruth h P k≤1 := by unfold gridTruth;split_ifs <;> norm_num

private lemma gridTruth_eq (h : ℝ) (P : ℝ×ℝ×ℝ → Prop) (k : ℤ×ℤ×ℤ)
    (hk : k∈gridIndices h) (hgood : k∉gridBadCells h P)
    (y : ℝ×ℝ×ℝ) (hy : y∈gridCube h k) : gridTruth h P k=if P y then 1 else 0 := by
  classical
  by_cases hP : P y
  · have hex : ∃ z∈gridCube h k,P z := ⟨y,hy,hP⟩
    simp [gridTruth,hP,hex]
  · have hno : ¬∃ z∈gridCube h k,P z := by
      rintro ⟨z,hz,hPz⟩
      exact hgood (Finset.mem_filter.mpr ⟨hk,z,hz,y,hy,hPz,hP⟩)
    simp [gridTruth,hP,hno]

private lemma grid_weights_bounds {J : Finset ℕ} (h : ℝ) (P : ℝ×ℝ×ℝ → Prop)
    (f : LocalLineData J → ℝ) (hf : ∀ lam,0≤f lam ∧ f lam≤1) (k : ℤ×ℤ×ℤ) (lam : LocalLineData J) :
    (0≤gridLowerWeights h P f k lam ∧ gridLowerWeights h P f k lam≤1) ∧
      (0≤gridUpperWeights h P f k lam ∧ gridUpperWeights h P f k lam≤1) := by
  classical
  have ht := gridTruth_bounds h P k
  have hp : 0≤gridTruth h P k*f lam ∧ gridTruth h P k*f lam≤1 :=
    ⟨mul_nonneg ht.1 (hf lam).1,by simpa only [one_mul] using mul_le_mul ht.2 (hf lam).2 (hf lam).1 (by norm_num : (0:ℝ)≤1)⟩
  by_cases hb : k∈gridBadCells h P <;> simp [gridLowerWeights,gridUpperWeights,hb,hp]

private lemma grid_cell_model_mass {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (hh : 0<h) (k : ℤ×ℤ×ℤ) :
    modelFunctional F S (fun w _ => if normalizedArch S w∈gridCell h k then 1 else 0)=
      (6/Real.pi^2)*gridCellVolume h k := by
  simpa [assignedLines] using grid_cell_model_average F S hU hV h hh k ∅ (by simp) (fun p => 0)

set_option maxHeartbeats 1000000 in
private lemma bounded_grid_transfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (hh : 0<h)
    (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a)
    (P : ℝ×ℝ×ℝ → Prop) (hP : MeasurableSet {y|P y})
    (f : LocalLineData J → ℝ) (hf : ∀ lam,0≤f lam ∧ f lam≤1)
    (E : ℝ) (hE : 0≤E)
    (hbox : ∀ lam : (p : ℕ) → Fin (p+1),RootBoxEstimate F S J hJ lam E) :
    |physicalFunctional F S (fun w ℓ => if P (normalizedArch S w) then f (restrictLines F S J hJ ℓ) else 0)-
      modelFunctional F S (fun w ℓ => if P (normalizedArch S w) then f (restrictLines F S J hJ ℓ) else 0)| ≤
      (6/Real.pi^2)*((gridBadCells h P).card : ℝ)*h^3+
        ((gridIndices h).card : ℝ)*(4*E*∏ p∈J,((p:ℝ)+1)) := by
  classical
  let Bad := gridBadCells h P
  let G := fun w ℓ => if P (normalizedArch S w) then f (restrictLines F S J hJ ℓ) else 0
  let Lo := weightedGridFunction F S h J hJ (gridLowerWeights h P f)
  let Hi := weightedGridFunction F S h J hJ (gridUpperWeights h P f)
  have hLoWeights : ∀ k∈gridIndices h,∀ lam,0≤gridLowerWeights h P f k lam ∧ gridLowerWeights h P f k lam≤1 :=
    fun k _ lam => (grid_weights_bounds h P f hf k lam).1
  have hHiWeights : ∀ k∈gridIndices h,∀ lam,0≤gridUpperWeights h P f k lam ∧ gridUpperWeights h P f k lam≤1 :=
    fun k _ lam => (grid_weights_bounds h P f hf k lam).2
  have hLoMeas := weightedGridFunction_measurable F S hU hV h J hJ (gridLowerWeights h P f)
  have hHiMeas := weightedGridFunction_measurable F S hU hV h J hJ (gridUpperWeights h P f)
  have hLoBounds := weightedGridFunction_bounds F S h hh J hJ (gridLowerWeights h P f) hLoWeights
  have hHiBounds := weightedGridFunction_bounds F S h hh J hJ (gridUpperWeights h P f) hHiWeights
  have hGMeas (ℓ) : Measurable (fun y : ℝ×ℝ×ℝ => G ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) := by
    dsimp only [G]
    simp only [normalized_arch_point S hU hV]
    exact Measurable.ite hP measurable_const measurable_const
  have hGBounds (w) (ℓ) : 0≤G w ℓ ∧ G w ℓ≤1 := by
    dsimp only [G]
    split_ifs
    · exact hf _
    · norm_num
  have hLoAbs (w) (ℓ) : |Lo w ℓ|≤1 := by
    have hb : 0≤Lo w ℓ ∧ Lo w ℓ≤1 := hLoBounds w ℓ
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hHiAbs (w) (ℓ) : |Hi w ℓ|≤1 := by
    have hb : 0≤Hi w ℓ ∧ Hi w ℓ≤1 := hHiBounds w ℓ
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hGAbs (w) (ℓ) : |G w ℓ|≤1 := by simpa only [abs_of_nonneg (hGBounds w ℓ).1] using (hGBounds w ℓ).2
  have hpoint (w : ArchRoot) (hw : w.InRegion S) (ℓ : LineData S.x K F.a) :
      Lo w ℓ≤G w ℓ ∧ G w ℓ≤Hi w ℓ := by
    have hy := arch_in_region_normalized S hU hV w hw
    have hk := grid_owner_mem h hh (normalizedArch S w) hy
    have hc := grid_owner_cube h hh (normalizedArch S w)
    dsimp only [Lo,Hi]
    rw [weightedGridFunction_eval F S h hh J hJ _ w ℓ hy,
      weightedGridFunction_eval F S h hh J hJ _ w ℓ hy]
    by_cases hb : gridOwner h (normalizedArch S w)∈gridBadCells h P
    · simpa only [gridLowerWeights,gridUpperWeights,if_pos hb] using hGBounds w ℓ
    · have ht := gridTruth_eq h P _ hk hb _ hc
      dsimp only [gridLowerWeights,gridUpperWeights]
      rw [if_neg hb,if_neg hb,ht]
      by_cases hp : P (normalizedArch S w) <;> simp [G,hp]
  have hloP := physicalFunctional_mono_region F S hU hV Lo G (fun w hw ℓ => (hpoint w hw ℓ).1)
  have hhiP := physicalFunctional_mono_region F S hU hV G Hi (fun w hw ℓ => (hpoint w hw ℓ).2)
  have hloM := modelFunctional_mono F S hU hV Lo G hLoMeas hGMeas 1 1 (by norm_num) (by norm_num)
    hLoAbs hGAbs (fun w hw ℓ => (hpoint w hw ℓ).1)
  have hhiM := modelFunctional_mono F S hU hV G Hi hGMeas hHiMeas 1 1 (by norm_num) (by norm_num)
    hGAbs hHiAbs (fun w hw ℓ => (hpoint w hw ℓ).2)
  have hLoTransfer := weighted_grid_sum_transfer F S hU hV h hh J hJ (gridLowerWeights h P f) hLoWeights E hE hbox
  have hHiTransfer := weighted_grid_sum_transfer F S hU hV h hh J hJ (gridUpperWeights h P f) hHiWeights E hE hbox
  have hdiff : (fun w ℓ => Hi w ℓ-Lo w ℓ) =
      (fun (w : ArchRoot) (ℓ : LineData S.x K F.a) => ∑ k∈Bad,if normalizedArch S w∈gridCell h k then (1:ℝ) else 0) := by
    funext w ℓ
    dsimp only [Hi,Lo,weightedGridFunction]
    rw [←Finset.sum_sub_distrib]
    have he (k) :
        (if normalizedArch S w∈gridCell h k then gridUpperWeights h P f k (restrictLines F S J hJ ℓ) else 0)-
        (if normalizedArch S w∈gridCell h k then gridLowerWeights h P f k (restrictLines F S J hJ ℓ) else 0) =
        if k∈Bad then (if normalizedArch S w∈gridCell h k then (1:ℝ) else 0) else 0 := by
      by_cases hb : k∈gridBadCells h P <;> by_cases hc : normalizedArch S w∈gridCell h k <;>
        simp [Bad,gridUpperWeights,gridLowerWeights,hb,hc]
    simp_rw [he]
    rw [←Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter,Bad,gridBadCells]
    tauto
  have hMassMeas (k) (ℓ : LineData S.x K F.a) : Measurable (fun y : ℝ×ℝ×ℝ =>
      if normalizedArch S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩∈gridCell h k then (1:ℝ) else 0) := by
    simp only [normalized_arch_point S hU hV]
    exact Measurable.ite (gridCell_measurableSet h k) measurable_const measurable_const
  have hMassBound (k) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
      |if normalizedArch S w∈gridCell h k then (1:ℝ) else 0|≤1 := by split_ifs <;> norm_num
  have hgap : modelFunctional F S Hi-modelFunctional F S Lo≤(6/Real.pi^2)*(Bad.card : ℝ)*h^3 := by
    rw [←modelFunctional_sub F S Hi Lo hHiMeas hLoMeas 1 1 (by norm_num) (by norm_num) hHiAbs hLoAbs,hdiff,
      modelFunctional_finset_sum F S Bad (fun k w _ => if normalizedArch S w∈gridCell h k then (1:ℝ) else 0)
        (fun k _ => hMassMeas k) (fun _ => 1) (fun _ _ => by norm_num) (fun k _ => hMassBound k)]
    simp_rw [grid_cell_model_mass F S hU hV h hh]
    rw [←Finset.mul_sum]
    have hv : (∑ k∈Bad,gridCellVolume h k)≤(Bad.card : ℝ)*h^3 := by
      calc
        _ ≤ ∑ _k∈Bad,h^3 := Finset.sum_le_sum (fun k _ => (grid_cell_volume_bound h hh.le k).2)
        _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
    have hm := mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ)≤6/Real.pi^2)
    simpa only [mul_assoc] using hm
  exact expectation_sandwich _ _ _ _ _ _ _ _ hloP hhiP hloM hhiM hLoTransfer hHiTransfer hgap

private lemma truncated_powerset_card {ι : Type*} (T : Finset ι) (k : ℕ) :
    (T.powerset.filter fun W => W.card≤k).card≤(k+1)*(T.card+1)^k := by
  classical
  have he : (T.powerset.filter fun W => W.card≤k) =
      (Finset.range (k+1)).biUnion (fun r => T.powersetCard r) := by
    ext W
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard]
    constructor
    · rintro ⟨hWT,hcard⟩
      exact ⟨W.card,by omega,hWT,rfl⟩
    · rintro ⟨r,hr,hWT,hcard⟩
      exact ⟨hWT,by omega⟩
  rw [he]
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _r∈Finset.range (k+1),(T.card+1)^k := by
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow T.card r).trans
        ((pow_le_pow_left₀ (Nat.zero_le T.card) (Nat.le_succ T.card) r).trans
          (pow_le_pow_right₀ (by omega : 1≤T.card+1) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))))
    _ = _ := by simp

private lemma normalized_arch_reconstruct (S : PDScale) (hU : 0<S.U) (hV : 0<S.V) (w : ArchRoot) :
    (⟨S.U*(normalizedArch S w).1,S.V*(normalizedArch S w).2.1,(normalizedArch S w).2.2⟩ : ArchRoot)=w := by
  cases w
  congr 1 <;> dsimp only [normalizedArch] <;> field_simp

private def pathPredicate {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    ℝ×ℝ×ℝ → Prop := fun y => ∀ j,envBox S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ (γ j).1 ∧
      envGood F S ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ (γ j)

private lemma pathPredicate_measurable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    MeasurableSet {y|pathPredicate F S γ y} :=
  (Measurable.forall (fun j => (envBox_measurable S (γ j).1).and (envGood_measurable F S (γ j)))).setOf

private lemma pathArch_normalized_indicator {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (γ : EnvPath S.x K) (w : ArchRoot) :
    pathArch F S w γ=if pathPredicate F S γ (normalizedArch S w) then 1 else 0 := by
  rw [pathArch_indicator]
  unfold pathPredicate
  rw [normalized_arch_reconstruct S hU hV]
  split_ifs <;> rfl

private lemma bounded_path_local_transfer {K : ℕ} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (hh : 0<h) (γ : EnvPath S.x K)
    (J : Finset ℕ) (hJ : J⊆markedPrimes S.x K F.a) (f : LocalLineData J → ℝ)
    (hf : ∀ lam,0≤f lam ∧ f lam≤1) (E : ℝ) (hE : 0≤E)
    (hbox : ∀ lam : (p : ℕ) → Fin (p+1),RootBoxEstimate F S J hJ lam E) :
    |physicalFunctional F S (fun w ℓ => pathArch F S w γ*f (restrictLines F S J hJ ℓ))-
      modelFunctional F S (fun w ℓ => pathArch F S w γ*f (restrictLines F S J hJ ℓ))| ≤
      (6/Real.pi^2)*((gridBadCells h (pathPredicate F S γ)).card : ℝ)*h^3+
        ((gridIndices h).card : ℝ)*(4*E*∏ p∈J,((p:ℝ)+1)) := by
  classical
  have hfun : (fun w ℓ => pathArch F S w γ*f (restrictLines F S J hJ ℓ))=
      (fun w ℓ => if pathPredicate F S γ (normalizedArch S w) then f (restrictLines F S J hJ ℓ) else 0) := by
    funext w ℓ
    rw [pathArch_normalized_indicator F S hU hV]
    split_ifs <;> simp
  rw [hfun]
  exact bounded_grid_transfer F S hU hV h hh J hJ (pathPredicate F S γ)
    (pathPredicate_measurable F S γ) f hf E hE hbox

private def activeSubtype {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    Finset {p : ℕ // p∈markedPrimes S.x K F.a} :=
  (markedPrimes S.x K F.a).attach.filter fun p => p.1∈pathActivePrimes γ

private def inactiveSubtype {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    Finset {p : ℕ // p∈markedPrimes S.x K F.a} :=
  (markedPrimes S.x K F.a).attach.filter fun p => p.1∉pathActivePrimes γ

private def monomialPrimes {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) : Finset ℕ :=
  pathActivePrimes γ ∪ W.image Subtype.val

private def monomialLineFunction {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (ℓ : LineData S.x K F.a) : ℝ :=
  (∏ p∈activeSubtype F S γ,pathPrimeFactor F S γ p.1 (ℓ p))*
    ∏ p∈W,(1-pathPrimeFactor F S γ p.1 (ℓ p))

private def monomialObservable {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℝ :=
  pathArch F S w γ*monomialLineFunction F S γ W ℓ

private def monomialLocalFunction {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (lam : LocalLineData (monomialPrimes F S γ W)) : ℝ :=
  (∏ p∈activeSubtype F S γ,pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1))*
    ∏ p∈W,(1-pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1))

private lemma pathActivePrimes_subset_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ) :
    pathActivePrimes γ⊆markedPrimes S.x K F.a := by
  intro p hp
  have hrepr : ∃ j i jj,(γ j).2 i jj=p := by simpa [pathActivePrimes] using hp
  obtain ⟨j,i,jj,rfl⟩ := hrepr
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,(hγ.1 j).2.1 i jj |>.2⟩

private lemma monomialPrimes_subset_marked {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) :
    monomialPrimes F S γ W⊆markedPrimes S.x K F.a := by
  intro p hp
  obtain hp|hp := Finset.mem_union.mp hp
  · exact pathActivePrimes_subset_marked F S γ hγ hp
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact q.2

private lemma monomialLocalFunction_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a})
    (lam : LocalLineData (monomialPrimes F S γ W)) :
    0 ≤ monomialLocalFunction F S γ W lam ∧ monomialLocalFunction F S γ W lam ≤ 1 := by
  unfold monomialLocalFunction
  have hfac (p : {p : ℕ // p∈markedPrimes S.x K F.a}) :=
    pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1)
  have hA0 : 0≤∏ p∈activeSubtype F S γ,pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1) :=
    Finset.prod_nonneg (fun p _ => (hfac p).1)
  have hA1 : (∏ p∈activeSubtype F S γ,pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1))≤1 :=
    Finset.prod_le_one₀ (fun p _ => (hfac p).1) (fun p _ => (hfac p).2)
  have hW0 : 0≤∏ p∈W,(1-pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1)) :=
    Finset.prod_nonneg (fun p _ => sub_nonneg.mpr (hfac p).2)
  have hW1 : (∏ p∈W,(1-pathPrimeFactor F S γ p.1 (extendLines (monomialPrimes F S γ W) lam p.1)))≤1 :=
    Finset.prod_le_one₀ (fun p _ => sub_nonneg.mpr (hfac p).2) (fun p _ => by linarith [hfac p])
  exact ⟨mul_nonneg hA0 hW0,by simpa only [one_mul] using mul_le_mul hA1 hW1 hW0 (by norm_num : (0:ℝ)≤1)⟩

section
attribute [local irreducible] pathPrimeFactor
set_option maxHeartbeats 1000000 in
private lemma monomialLocalFunction_restrict {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a})
    (hJ : monomialPrimes F S γ W⊆markedPrimes S.x K F.a) (ℓ : LineData S.x K F.a) :
    monomialLocalFunction F S γ W (restrictLines F S (monomialPrimes F S γ W) hJ ℓ)=
      monomialLineFunction F S γ W ℓ := by
  have hline (p : {p : ℕ // p∈markedPrimes S.x K F.a}) (hp : p.1∈monomialPrimes F S γ W) :
      extendLines (monomialPrimes F S γ W) (restrictLines F S (monomialPrimes F S γ W) hJ ℓ) p.1=ℓ p := by
    simp only [extendLines,dif_pos hp,restrictLines]
  unfold monomialLocalFunction monomialLineFunction
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    rw [hline p (Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mp hp).2))]
  · apply Finset.prod_congr rfl
    intro p hp
    rw [hline p (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨p,hp,rfl⟩)))]

end

private lemma monomial_primes_disjoint {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (hW : W⊆inactiveSubtype F S γ) :
    Disjoint (pathActivePrimes γ) (W.image Subtype.val) := by
  apply Finset.disjoint_left.mpr
  intro p ha hw
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
  exact (Finset.mem_filter.mp (hW hq)).2 ha

private lemma monomial_line_modulus {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a})
    (hU : 0<S.U) (hV : 0<S.V) (h : ℝ) (hh : 0<h) (E : ℝ) (hE : 0≤E)
    (hbox : ∀ lam : (p : ℕ) → Fin (p+1),RootBoxEstimate F S (monomialPrimes F S γ W)
      (monomialPrimes_subset_marked F S γ hγ W) lam E) :
    |physicalFunctional F S (monomialObservable F S γ W)-modelFunctional F S (monomialObservable F S γ W)| ≤
      (6/Real.pi^2)*((gridBadCells h (pathPredicate F S γ)).card : ℝ)*h^3+
        ((gridIndices h).card : ℝ)*(4*E*∏ p∈monomialPrimes F S γ W,((p:ℝ)+1)) := by
  have hf := bounded_path_local_transfer F S hU hV h hh γ (monomialPrimes F S γ W)
    (monomialPrimes_subset_marked F S γ hγ W) (monomialLocalFunction F S γ W)
    (monomialLocalFunction_bounds F S hF γ W) E hE hbox
  change |physicalFunctional F S (fun w ℓ => pathArch F S w γ*monomialLineFunction F S γ W ℓ)-
    modelFunctional F S (fun w ℓ => pathArch F S w γ*monomialLineFunction F S γ W ℓ)| ≤ _
  simpa only [monomialLocalFunction_restrict] using hf

private lemma monomial_modulus_budget {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (δ c₁ c₂ Cb : ℝ) (hS : S.Valid K δ c₁ c₂) (hL : 1≤S.L) (hCb : 0≤Cb)
    (γ : EnvPath S.x K) (hγ : IsEnvPathAdmissible F S γ)
    (hActive : (∏ p∈pathActivePrimes γ,(p:ℝ))≤Real.exp (Cb*Real.rpow S.L (72/100:ℝ)))
    (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (hW : W⊆inactiveSubtype F S γ)
    (hcard : (W.card : ℝ)≤4*Real.rpow S.L (19/25:ℝ)) :
    (∏ p∈monomialPrimes F S γ W,(p:ℝ))≤Real.exp ((Cb+8)*Real.rpow S.L (24/25:ℝ)) ∧
      (∏ p∈monomialPrimes F S γ W,((p:ℝ)+1))≤
        Real.exp ((Cb+8+(8*(K:ℝ)+4)*Real.log 2)*Real.rpow S.L (24/25:ℝ)) := by
  classical
  let J := monomialPrimes F S γ W
  let WN := W.image Subtype.val
  have hLpos : 0<S.L := by linarith
  have hJsub := monomialPrimes_subset_marked F S γ hγ W
  have hp (p : ℕ) (hpJ : p∈J) : p.Prime := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp (hJsub hpJ)
    exact (Finset.mem_filter.mp hpi).2.1
  have hPrimeBound (p : ℕ) (hpP : p∈markedPrimes S.x K F.a) :
      (p:ℝ)≤Real.exp (2*Real.rpow S.L (1/5:ℝ)) := by
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hpP
    exact primeBand_uniform_upper F S hF hL i p hpi
  have hWNcard : WN.card=W.card := Finset.card_image_of_injective W Subtype.val_injective
  have hWNbound : ∀ p∈WN,(p:ℝ)≤Real.exp (2*Real.rpow S.L (1/5:ℝ)) := by
    intro p hpW
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hpW
    exact hPrimeBound q.1 q.2
  have hWprod : (∏ p∈WN,(p:ℝ))≤Real.exp (8*Real.rpow S.L (24/25:ℝ)) := by
    have hb := Finset.prod_le_prod₀ (fun p hp => Nat.cast_nonneg p) hWNbound
    have he : (∏ _p∈WN,Real.exp (2*Real.rpow S.L (1/5:ℝ))) =
        Real.exp ((2*Real.rpow S.L (1/5:ℝ))*(W.card : ℝ)) := by
      rw [Finset.prod_const,hWNcard]
      exact real_exp_pow_nat _ _
    have hpow : Real.rpow S.L (1/5:ℝ)*Real.rpow S.L (19/25:ℝ)=Real.rpow S.L (24/25:ℝ) := by
      calc
        _ = Real.rpow S.L ((1/5:ℝ)+19/25) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1;norm_num
    calc
      _ ≤ _ := hb
      _ = _ := he
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hnon : (0:ℝ)≤2*Real.rpow S.L (1/5:ℝ) :=
          mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hLpos.le (1/5:ℝ))
        have hm := mul_le_mul_of_nonneg_left hcard hnon
        nlinarith [hpow])
  have hAprod : (∏ p∈pathActivePrimes γ,(p:ℝ))≤Real.exp (Cb*Real.rpow S.L (24/25:ℝ)) :=
    hActive.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (72/100:ℝ)≤24/25)) hCb))
  have hJprod : (∏ p∈J,(p:ℝ))≤Real.exp ((Cb+8)*Real.rpow S.L (24/25:ℝ)) := by
    rw [show J=pathActivePrimes γ∪WN from rfl,Finset.prod_union (monomial_primes_disjoint F S γ W hW)]
    have hm := mul_le_mul hAprod hWprod (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) (Real.exp_pos _).le
    apply hm.trans_eq
    rw [←Real.exp_add]
    congr 1
    ring
  obtain ⟨hN,hM,hd,hY,hP⟩ := budget_scale_bounds F S δ c₁ c₂ hF hS hL
  have hAcard : ((pathActivePrimes γ).card : ℝ)≤8*(K:ℝ)*Real.rpow S.L (51/100:ℝ) := by
    have hc : ((pathActivePrimes γ).card : ℝ)≤((pathLength S.x : ℝ)+1)*(K:ℝ)*(slotCount S.x : ℝ) := by
      exact_mod_cast pathActivePrimes_card_le γ
    have hm := mul_le_mul (mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg K)) hM
      (Nat.cast_nonneg (slotCount S.x))
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) (Real.rpow_nonneg hLpos.le (1/2:ℝ))) (Nat.cast_nonneg K))
    have hpow : Real.rpow S.L (1/2:ℝ)*Real.rpow S.L (1/100:ℝ)=Real.rpow S.L (51/100:ℝ) := by
      calc
        _ = Real.rpow S.L ((1/2:ℝ)+1/100) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1;norm_num
    apply hc.trans
    apply hm.trans_eq
    rw [←hpow]
    ring
  have hJcard : (J.card : ℝ)≤(8*(K:ℝ)+4)*Real.rpow S.L (19/25:ℝ) := by
    have hc : (J.card : ℝ)≤((pathActivePrimes γ).card : ℝ)+(W.card : ℝ) := by
      have hn := Finset.card_union_le (pathActivePrimes γ) WN
      rw [hWNcard] at hn
      exact_mod_cast hn
    have hpow : Real.rpow S.L (51/100:ℝ)≤Real.rpow S.L (19/25:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (51/100:ℝ)≤19/25)
    have hm := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ)≤8*(K:ℝ))
    nlinarith
  have hLineProd : (∏ p∈J,((p:ℝ)+1))≤(2:ℝ)^J.card*(∏ p∈J,(p:ℝ)) := by
    have hm : (∏ p∈J,((p:ℝ)+1))≤∏ p∈J,2*(p:ℝ) := by
      apply Finset.prod_le_prod₀ (fun p _ => by positivity)
      intro p hpJ
      have h1 : (1:ℝ)≤p := by exact_mod_cast (hp p hpJ).one_lt.le
      linarith
    simpa only [Finset.prod_mul_distrib,Finset.prod_const] using hm
  have h2power : (2:ℝ)^J.card=Real.exp (Real.log 2*(J.card : ℝ)) := by
    have he : (2:ℝ)=Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0:ℝ)<2)).symm
    calc
      _ = Real.exp (Real.log 2)^J.card := congrArg (fun t : ℝ => t^J.card) he
      _ = _ := real_exp_pow_nat _ _
  have hlog2 : 0≤Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hcard96 : (J.card : ℝ)≤(8*(K:ℝ)+4)*Real.rpow S.L (24/25:ℝ) :=
    hJcard.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (19/25:ℝ)≤24/25)) (by positivity))
  have h2bound : (2:ℝ)^J.card≤Real.exp (((8*(K:ℝ)+4)*Real.log 2)*Real.rpow S.L (24/25:ℝ)) := by
    rw [h2power]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hcard96 hlog2
    nlinarith
  refine ⟨hJprod,?_⟩
  apply hLineProd.trans
  have hm := mul_le_mul h2bound hJprod (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) (Real.exp_pos _).le
  apply hm.trans_eq
  rw [←Real.exp_add]
  congr 1
  ring

private lemma monomial_transfer_eventually (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hc₁ : 0<c₁)
    {K : ℕ} (F : PDFix K) (hF : F.Valid) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ C_R x₀ : ℝ,0<C_R ∧ 2≤x₀ ∧ ∀ S : PDScale,S.Valid K δ c₁ c₂ → x₀≤S.x →
      ∀ γ : EnvPath S.x K,IsContributingPath F S γ →
      ∀ W : Finset {p : ℕ // p∈markedPrimes S.x K F.a},W⊆inactiveSubtype F S γ →
        (W.card : ℝ)≤4*Real.rpow S.L (19/25:ℝ) →
        |physicalFunctional F S (monomialObservable F S γ W)-modelFunctional F S (monomialObservable F S γ W)| ≤
          (6/Real.pi^2)*((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (-ε)+
            4000*C_R*(∏ p∈monomialPrimes F S γ W,((p:ℝ)+1))*Real.rpow S.x (-(δ/1000)+3*ε) := by
  classical
  obtain ⟨Cb,xCb,hCb,hxCb,hBudget⟩ := root_budget δ c₁ c₂ hδ hc₁ K F hF
  obtain ⟨C_R,xR,hCR,hxR,hBoxes⟩ := root_box_estimate_eventually δ (Cb+8) hδ (by linarith)
  obtain ⟨xB,hxB,hBoundary⟩ := contributing_path_boundary_eventually δ c₁ c₂ hδ hc₁ F hF ε hε hε1
  let x₀ := max (max xCb xR) (max xB (Real.exp 1))
  have hCb₀ : xCb≤x₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hR₀ : xR≤x₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hB₀ : xB≤x₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hE₀ : Real.exp 1≤x₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C_R,x₀,hCR,hxCb.trans hCb₀,?_⟩
  intro S hS hx γ hγ W hW hcard
  have hxpos : 0<S.x := by linarith [hS.1]
  have hL : 1≤S.L := (Real.le_log_iff_exp_le hxpos).2 (hE₀.trans hx)
  have hUpos : 0<S.U := (pdScale_positive S δ c₁ c₂ hδ hS).2.1
  have hVpos : 0<S.V := (Real.rpow_pos_of_pos hxpos δ).trans_le hS.2.2.1
  have hActive := (hBudget S hS (hCb₀.trans hx)).2.2 γ hγ |>.1
  obtain ⟨hMod,hLines⟩ := monomial_modulus_budget F S hF δ c₁ c₂ Cb hS hL hCb.le γ hγ.1 hActive W hW hcard
  have hMod' : ((∏ p∈monomialPrimes F S γ W,p : ℕ) : ℝ)≤
      Real.exp ((Cb+8)*Real.rpow S.L (98/100:ℝ)) := by
    rw [Nat.cast_prod]
    apply hMod.trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (24/25:ℝ)≤98/100)) (by linarith))
  have hbox := hBoxes K F S c₁ c₂ hS (hR₀.trans hx) (monomialPrimes F S γ W)
    (monomialPrimes_subset_marked F S γ hγ.1 W) hMod'
  let h := Real.rpow S.x (-ε)
  have hh : 0<h := Real.rpow_pos_of_pos hxpos _
  have hh1 : h≤1 := by
    have he : h=Real.exp (S.L*(-ε)) := Real.rpow_def_of_pos hxpos (-ε)
    rw [he]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hE0 : 0≤C_R*Real.rpow S.x (-(δ/1000)) :=
    mul_nonneg hCR.le (Real.rpow_nonneg hxpos.le _)
  have hraw := monomial_line_modulus F S hF γ hγ.1 W hUpos hVpos h hh
    (C_R*Real.rpow S.x (-(δ/1000))) hE0 hbox
  have hB := hBoundary S hS (hB₀.trans hx) γ hγ
  change ((gridBadCells h (pathPredicate F S γ)).card : ℝ)≤
    ((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (2*ε) at hB
  have hG := grid_indices_card h hh hh1
  have hpow : h^3=Real.rpow S.x (-(3*ε)) := by
    calc
      _ = Real.rpow h (3:ℝ) := (Real.rpow_natCast h 3).symm
      _ = Real.rpow S.x ((-ε)*3) := (Real.rpow_mul hxpos.le (-ε) 3).symm
      _ = _ := by congr 1;ring
  have hinv : (h^3)⁻¹=Real.rpow S.x (3*ε) := by
    rw [hpow]
    exact (congrArg (fun t : ℝ => t⁻¹) (Real.rpow_neg hxpos.le (3*ε))).trans (inv_inv _)
  have hpowB : Real.rpow S.x (2*ε)*h^3=Real.rpow S.x (-ε) := by
    rw [hpow]
    calc
      _ = Real.rpow S.x (2*ε-(3*ε)) := (Real.rpow_add hxpos _ _).symm
      _ = _ := by congr 1;ring
  have hpowG : Real.rpow S.x (-(δ/1000))*Real.rpow S.x (3*ε)=
      Real.rpow S.x (-(δ/1000)+3*ε) := (Real.rpow_add hxpos _ _).symm
  have hFirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hB (by positivity : (0:ℝ)≤6/Real.pi^2)) (by positivity : (0:ℝ)≤h^3)
  have hFirstEq : (6/Real.pi^2)*
      (((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (2*ε))*h^3 =
      (6/Real.pi^2)*((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ))*Real.rpow S.x (-ε) := by
    calc
      _ = ((6/Real.pi^2)*((pathLength S.x : ℝ)+1)*Real.exp (Real.rpow S.L (9/10:ℝ)))*
        (Real.rpow S.x (2*ε)*h^3) := by ring
      _ = _ := by rw [hpowB]
  rw [hFirstEq] at hFirst
  have hSecondFactor : (0:ℝ)≤4*(C_R*Real.rpow S.x (-(δ/1000)))*
      ∏ p∈monomialPrimes F S γ W,((p:ℝ)+1) :=
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) hE0)
      (Finset.prod_nonneg (fun p _ => add_nonneg (Nat.cast_nonneg p) (by norm_num : (0:ℝ)≤1)))
  have hSecond := mul_le_mul_of_nonneg_right hG hSecondFactor
  have hSecondEq : (1000/h^3)*(4*(C_R*Real.rpow S.x (-(δ/1000)))*
      ∏ p∈monomialPrimes F S γ W,((p:ℝ)+1)) =
      4000*C_R*(∏ p∈monomialPrimes F S γ W,((p:ℝ)+1))*Real.rpow S.x (-(δ/1000)+3*ε) := by
    rw [div_eq_mul_inv,hinv]
    calc
      _ = 4000*C_R*(∏ p∈monomialPrimes F S γ W,((p:ℝ)+1))*
        (Real.rpow S.x (-(δ/1000))*Real.rpow S.x (3*ε)) := by ring
      _ = _ := by rw [hpowG]
  rw [hSecondEq] at hSecond
  exact hraw.trans (add_le_add hFirst hSecond)

private def pathActiveFactor {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (ℓ : LineData S.x K F.a) : ℝ := ∏ p∈activeSubtype F S γ,pathPrimeFactor F S γ p.1 (ℓ p)

private def pathExcess {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (p : {p : ℕ // p∈markedPrimes S.x K F.a}) (lam : Fin (p.1+1)) : ℝ :=
  1-pathPrimeFactor F S γ p.1 lam

private def pathBonferroniUpper {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (m : ℕ) (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℝ :=
  pathArch F S w γ*pathActiveFactor F S γ ℓ*
    bonferroniTrunc (inactiveSubtype F S γ) (fun p => pathExcess F S γ p (ℓ p)) m

private def pathBonferroniGap {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K)
    (m : ℕ) (w : ArchRoot) (ℓ : LineData S.x K F.a) : ℝ :=
  pathArch F S w γ*pathActiveFactor F S γ ℓ*
    (bonferroniTrunc (inactiveSubtype F S γ) (fun p => pathExcess F S γ p (ℓ p)) m-
      bonferroniTrunc (inactiveSubtype F S γ) (fun p => pathExcess F S γ p (ℓ p)) (m+1))

private lemma pathActiveFactor_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (ℓ : LineData S.x K F.a) :
    0 ≤ pathActiveFactor F S γ ℓ ∧ pathActiveFactor F S γ ℓ ≤ 1 :=
  ⟨Finset.prod_nonneg (fun p _ => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).1),
    Finset.prod_le_one₀ (fun p _ => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).1)
      (fun p _ => (pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 (ℓ p)).2)⟩

private lemma pathExcess_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (p : {p : ℕ // p∈markedPrimes S.x K F.a}) (lam : Fin (p.1+1)) :
    0 ≤ pathExcess F S γ p lam ∧ pathExcess F S γ p lam ≤ 1 := by
  have hb := pathPrimeFactor_bounds F S hF.2.1 hF.2.2.1 γ p.1 lam
  unfold pathExcess
  constructor <;> linarith

private lemma pathObservable_active_inactive {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    pathObservable F S γ w ℓ=pathArch F S w γ*pathActiveFactor F S γ ℓ*
      ∏ p∈inactiveSubtype F S γ,(1-pathExcess F S γ p (ℓ p)) := by
  have he := (Finset.prod_filter_mul_prod_filter_not (markedPrimes S.x K F.a).attach
    (fun p => p.1∈pathActivePrimes γ) (fun p => pathPrimeFactor F S γ p.1 (ℓ p))).symm
  have hprod : (∏ p : {p : ℕ // p∈markedPrimes S.x K F.a},pathPrimeFactor F S γ p.1 (ℓ p)) =
      pathActiveFactor F S γ ℓ*∏ p∈inactiveSubtype F S γ,pathPrimeFactor F S γ p.1 (ℓ p) := by
    simpa only [pathActiveFactor,activeSubtype,inactiveSubtype,Finset.univ_eq_attach] using he
  unfold pathObservable pathExcess
  rw [hprod]
  have hs (p : {p : ℕ // p∈markedPrimes S.x K F.a}) :
      1-(1-pathPrimeFactor F S γ p.1 (ℓ p))=pathPrimeFactor F S γ p.1 (ℓ p) := by ring
  simp_rw [hs]
  ring

private lemma pathBonferroni_sandwich {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (m : ℕ) (hm : Even m) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    0 ≤ pathBonferroniUpper F S γ m w ℓ-pathObservable F S γ w ℓ ∧
      pathBonferroniUpper F S γ m w ℓ-pathObservable F S γ w ℓ ≤ pathBonferroniGap F S γ m w ℓ := by
  have hb := (root_bonferroni (inactiveSubtype F S γ) (pathExcess F S γ)
    (pathExcess_bounds F S hF γ) m hm).1 ℓ
  have ha : 0 ≤ pathArch F S w γ*pathActiveFactor F S γ ℓ :=
    mul_nonneg (pathArch_bounds F S w γ).1 (pathActiveFactor_bounds F S hF γ ℓ).1
  have hn := mul_nonneg ha (sub_nonneg.mpr hb.2)
  have hu := mul_le_mul_of_nonneg_left (sub_le_sub_left hb.1
    (bonferroniTrunc (inactiveSubtype F S γ) (fun p => pathExcess F S γ p (ℓ p)) m)) ha
  unfold pathBonferroniUpper pathBonferroniGap
  rw [pathObservable_active_inactive]
  simpa only [mul_sub] using And.intro hn hu

private lemma pathBonferroniUpper_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (m : ℕ) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    pathBonferroniUpper F S γ m w ℓ =
      ∑ W∈(inactiveSubtype F S γ).powerset.filter (fun W => W.card≤ m),
        (-1:ℝ)^W.card*monomialObservable F S γ W w ℓ := by
  unfold pathBonferroniUpper bonferroniTrunc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W hW
  unfold monomialObservable monomialLineFunction pathActiveFactor pathExcess
  ring

private lemma pathBonferroniGap_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (m : ℕ) (hm : Even m) (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    pathBonferroniGap F S γ m w ℓ =
      ∑ W∈(inactiveSubtype F S γ).powerset.filter (fun W => W.card=m+1),monomialObservable F S γ W w ℓ := by
  unfold pathBonferroniGap
  rw [bonferroniTrunc_gap _ _ m hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W hW
  unfold monomialObservable monomialLineFunction pathActiveFactor pathExcess
  ring

private lemma monomialObservable_bounds {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (γ : EnvPath S.x K) (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a})
    (w : ArchRoot) (ℓ : LineData S.x K F.a) :
    0 ≤ monomialObservable F S γ W w ℓ ∧ monomialObservable F S γ W w ℓ ≤ 1 := by
  have hb := pathActiveFactor_bounds F S hF γ ℓ
  have ha := pathArch_bounds F S w γ
  have hW0 : 0 ≤ ∏ p∈W,pathExcess F S γ p (ℓ p) := Finset.prod_nonneg (fun p _ => (pathExcess_bounds F S hF γ p (ℓ p)).1)
  have hW1 : (∏ p∈W,pathExcess F S γ p (ℓ p)) ≤ 1 := Finset.prod_le_one₀
    (fun p _ => (pathExcess_bounds F S hF γ p (ℓ p)).1) (fun p _ => (pathExcess_bounds F S hF γ p (ℓ p)).2)
  have heq : monomialObservable F S γ W w ℓ=
      pathArch F S w γ*pathActiveFactor F S γ ℓ*(∏ p∈W,pathExcess F S γ p (ℓ p)) := by
    unfold monomialObservable monomialLineFunction pathActiveFactor pathExcess
    ring
  rw [heq]
  constructor
  · exact mul_nonneg (mul_nonneg ha.1 hb.1) hW0
  · simpa only [one_mul] using mul_le_mul
      (mul_le_mul ha.2 hb.2 hb.1 (by norm_num : (0:ℝ)≤1)) hW1 hW0 (by norm_num : (0:ℝ)≤1*1)

private lemma monomialObservable_measurable {K : ℕ} (F : PDFix K) (S : PDScale)
    (γ : EnvPath S.x K) (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (ℓ : LineData S.x K F.a) :
    Measurable (fun y : ℝ×ℝ×ℝ => monomialObservable F S γ W ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) :=
  (pathArch_measurable F S γ).mul measurable_const

private lemma finite_observable_transfer {K : ℕ} {ι : Type*} (F : PDFix K) (S : PDScale)
    (hU : 0<S.U) (hV : 0<S.V) (T : Finset ι) (c : ι → ℝ)
    (G : ι → ArchRoot → LineData S.x K F.a → ℝ)
    (hG : ∀ i∈T,∀ ℓ,Measurable (fun y : ℝ×ℝ×ℝ => G i ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ))
    (hb : ∀ i∈T,∀ w ℓ,|G i w ℓ|≤1) (hc : ∀ i∈T,|c i|≤1)
    (E : ℝ) (hE : 0≤E) (he : ∀ i∈T,|physicalFunctional F S (G i)-modelFunctional F S (G i)|≤E) :
    |physicalFunctional F S (fun w ℓ => ∑ i∈T,c i*G i w ℓ)-
      modelFunctional F S (fun w ℓ => ∑ i∈T,c i*G i w ℓ)|≤(T.card : ℝ)*E := by
  classical
  have hSigned (i) (hi : i∈T) (w) (ℓ) : |c i*G i w ℓ|≤1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hc i hi) (hb i hi w ℓ) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  rw [physicalFunctional_finset_sum F S hU hV,
    modelFunctional_finset_sum F S T (fun i w ℓ => c i*G i w ℓ)
      (fun i hi ℓ => measurable_const.mul (hG i hi ℓ)) (fun _ => 1)
      (fun _ _ => by norm_num) hSigned,←Finset.sum_sub_distrib]
  have hterm (i) (hi : i∈T) :
      |physicalFunctional F S (fun w ℓ => c i*G i w ℓ)-modelFunctional F S (fun w ℓ => c i*G i w ℓ)|≤E := by
    rw [physicalFunctional_mul_const F S hU hV,modelFunctional_mul_const F S,←mul_sub,abs_mul]
    simpa only [one_mul] using mul_le_mul (hc i hi) (he i hi) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  calc
    _ ≤ ∑ i∈T,|physicalFunctional F S (fun w ℓ => c i*G i w ℓ)-modelFunctional F S (fun w ℓ => c i*G i w ℓ)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le T (fun i =>
        physicalFunctional F S (fun w ℓ => c i*G i w ℓ)-modelFunctional F S (fun w ℓ => c i*G i w ℓ))
    _ ≤ ∑ _i∈T,E := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

private lemma pathBonferroni_transfer {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hU : 0<S.U) (hV : 0<S.V) (γ : EnvPath S.x K) (m : ℕ) (hm : Even m)
    (E : ℝ) (hE : 0≤E)
    (he : ∀ W : Finset {p : ℕ // p∈markedPrimes S.x K F.a},W⊆inactiveSubtype F S γ → W.card≤ m+1 →
      |physicalFunctional F S (monomialObservable F S γ W)-modelFunctional F S (monomialObservable F S γ W)|≤E) :
    |physicalFunctional F S (pathBonferroniUpper F S γ m)-modelFunctional F S (pathBonferroniUpper F S γ m)|≤
      (((inactiveSubtype F S γ).powerset.filter fun W => W.card≤ m+1).card : ℝ)*E ∧
    |physicalFunctional F S (pathBonferroniGap F S γ m)-modelFunctional F S (pathBonferroniGap F S γ m)|≤
      (((inactiveSubtype F S γ).powerset.filter fun W => W.card≤ m+1).card : ℝ)*E := by
  classical
  let T := inactiveSubtype F S γ
  let B := T.powerset.filter fun W => W.card≤ m+1
  have hReg (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (ℓ) := monomialObservable_measurable F S γ W ℓ
  have hAbs (W : Finset {p : ℕ // p∈markedPrimes S.x K F.a}) (w) (ℓ) :
      |monomialObservable F S γ W w ℓ|≤1 := by
    have hb := monomialObservable_bounds F S hF γ W w ℓ
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hUpperFun : pathBonferroniUpper F S γ m =
      fun w ℓ => ∑ W∈T.powerset.filter (fun W => W.card≤ m),(-1:ℝ)^W.card*monomialObservable F S γ W w ℓ :=
    funext (fun w => funext (fun ℓ => pathBonferroniUpper_expansion F S γ m w ℓ))
  have hGapFun : pathBonferroniGap F S γ m =
      fun w ℓ => ∑ W∈T.powerset.filter (fun W => W.card=m+1),(1:ℝ)*monomialObservable F S γ W w ℓ := by
    funext w ℓ
    simp only [one_mul]
    exact pathBonferroniGap_expansion F S γ m hm w ℓ
  constructor
  · rw [hUpperFun]
    have ht := finite_observable_transfer F S hU hV (T.powerset.filter fun W => W.card≤ m)
      (fun W => (-1:ℝ)^W.card) (monomialObservable F S γ)
      (fun W _ => hReg W) (fun W _ => hAbs W) (fun W _ => by simp)
      E hE (fun W hW => he W (Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1)
        (by have hc := (Finset.mem_filter.mp hW).2;omega))
    have hc : (T.powerset.filter fun W => W.card≤ m).card≤B.card := Finset.card_le_card (by
      intro W hW
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hW).1,by have hc := (Finset.mem_filter.mp hW).2;omega⟩)
    exact ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hE)
  · rw [hGapFun]
    have ht := finite_observable_transfer F S hU hV (T.powerset.filter fun W => W.card=m+1)
      (fun _ => 1) (monomialObservable F S γ)
      (fun W _ => hReg W) (fun W _ => hAbs W) (fun _ _ => by norm_num)
      E hE (fun W hW => he W (Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1)
        (Finset.mem_filter.mp hW).2.le)
    have hc : (T.powerset.filter fun W => W.card=m+1).card≤B.card := Finset.card_le_card (by
      intro W hW
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hW).1,(Finset.mem_filter.mp hW).2.le⟩)
    exact ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hE)

private lemma modelFunctional_line_const {K : ℕ} (F : PDFix K) (S : PDScale)
    (G : LineData S.x K F.a → ℝ) :
    modelFunctional F S (fun _ ℓ => G ℓ)=15*(6/Real.pi^2)*(lineAverage (fun ℓ => (G ℓ : ℂ))).re := by
  unfold modelFunctional
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  ring

private lemma bonferroni_gap_bounds {ι : Type*} (T : Finset ι) (X : ι → ℝ)
    (hX : ∀ p∈T,0 ≤ X p ∧ X p ≤ 1) (m : ℕ) (hm : Even m) :
    0 ≤ bonferroniTrunc T X m-bonferroniTrunc T X (m+1) ∧
      bonferroniTrunc T X m-bonferroniTrunc T X (m+1) ≤
        ((T.powerset.filter fun W => W.card=m+1).card : ℝ) := by
  classical
  rw [bonferroniTrunc_gap T X m hm]
  have hTerm (W : Finset ι) (hW : W∈T.powerset.filter fun W => W.card=m+1) :
      0 ≤ ∏ p∈W,X p ∧ (∏ p∈W,X p) ≤ 1 := by
    have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
    exact ⟨Finset.prod_nonneg (fun p hp => (hX p (hs hp)).1),
      Finset.prod_le_one₀ (fun p hp => (hX p (hs hp)).1) (fun p hp => (hX p (hs hp)).2)⟩
  constructor
  · exact Finset.sum_nonneg (fun W hW => (hTerm W hW).1)
  · calc
      _ ≤ ∑ _W∈T.powerset.filter (fun W => W.card=m+1),(1:ℝ) := Finset.sum_le_sum (fun W hW => (hTerm W hW).2)
      _ = _ := by simp

private lemma inactive_excess_sum {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) :
    (∑ p∈inactiveSubtype F S γ,((p.1 : ℝ)+1)⁻¹*∑ lam : Fin (p.1+1),pathExcess F S γ p lam) =
      ∑ p∈(markedPrimes S.x K F.a).filter (fun p => p∉pathActivePrimes γ),
        ((p:ℝ)+1)⁻¹*∑ lam : Fin (p+1),(1-pathPrimeFactor F S γ p lam) := by
  unfold inactiveSubtype pathExcess
  simp only [Finset.sum_filter]
  exact Finset.sum_attach (markedPrimes S.x K F.a) (fun p =>
    if p∉pathActivePrimes γ then ((p:ℝ)+1)⁻¹*∑ lam : Fin (p+1),(1-pathPrimeFactor F S γ p lam) else 0)

section
attribute [local irreducible] pathPrimeFactor pathActiveFactor pathExcess
set_option maxHeartbeats 1000000 in
private lemma pathBonferroniGap_model_bound {K : ℕ} (F : PDFix K) (S : PDScale) (hF : F.Valid)
    (hU : 0<S.U) (hV : 0<S.V) (γ : EnvPath S.x K) (m : ℕ) (hm : Even m)
    (B : ℝ) (hB : 0 ≤ B)
    (hExcess : (∑ p∈inactiveSubtype F S γ,((p.1 : ℝ)+1)⁻¹*∑ lam : Fin (p.1+1),pathExcess F S γ p lam) ≤ B) :
    modelFunctional F S (pathBonferroniGap F S γ m) ≤
      15*(6/Real.pi^2)*(B^(m+1)/((m+1).factorial : ℝ)) := by
  classical
  let T := inactiveSubtype F S γ
  let X := pathExcess F S γ
  let GapLine := fun ℓ : LineData S.x K F.a =>
    bonferroniTrunc T (fun p => X p (ℓ p)) m-bonferroniTrunc T (fun p => X p (ℓ p)) (m+1)
  let C : ℝ := ((T.powerset.filter fun W => W.card=m+1).card : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hGapLine (ℓ) : 0 ≤ GapLine ℓ ∧ GapLine ℓ ≤ C := bonferroni_gap_bounds T _
    (fun p _ => pathExcess_bounds F S hF γ p (ℓ p)) m hm
  have hActive (w) (ℓ) : 0 ≤ pathArch F S w γ*pathActiveFactor F S γ ℓ ∧
      pathArch F S w γ*pathActiveFactor F S γ ℓ ≤ 1 := by
    constructor
    · exact mul_nonneg (pathArch_bounds F S w γ).1 (pathActiveFactor_bounds F S hF γ ℓ).1
    · simpa only [one_mul] using (mul_le_mul (pathArch_bounds F S w γ).2
        (pathActiveFactor_bounds F S hF γ ℓ).2 (pathActiveFactor_bounds F S hF γ ℓ).1 (by norm_num : (0:ℝ)≤1))
  have hCompare (w) (ℓ) : pathBonferroniGap F S γ m w ℓ ≤ GapLine ℓ := by
    change (pathArch F S w γ*pathActiveFactor F S γ ℓ)*GapLine ℓ ≤ GapLine ℓ
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hActive w ℓ).2 (hGapLine ℓ).1
  have hGapAbs (w) (ℓ) : |pathBonferroniGap F S γ m w ℓ| ≤ C := by
    have hn : 0 ≤ pathBonferroniGap F S γ m w ℓ := mul_nonneg (hActive w ℓ).1 (hGapLine ℓ).1
    rw [abs_of_nonneg hn]
    exact (hCompare w ℓ).trans (hGapLine ℓ).2
  have hLineAbs (w : ArchRoot) (ℓ) : |GapLine ℓ| ≤ C := by
    rw [abs_of_nonneg (hGapLine ℓ).1]
    exact (hGapLine ℓ).2
  have hGapMeas (ℓ) : Measurable (fun y : ℝ×ℝ×ℝ => pathBonferroniGap F S γ m ⟨S.U*y.1,S.V*y.2.1,y.2.2⟩ ℓ) := by
    convert (pathArch_measurable F S γ).mul_const (pathActiveFactor F S γ ℓ*GapLine ℓ) using 1
    funext y
    dsimp only [GapLine,T,X,pathBonferroniGap]
    ring
  have hMean := (root_bonferroni T X (pathExcess_bounds F S hF γ) m hm).2
  have hSum0 : 0 ≤ ∑ p∈T,((p.1 : ℝ)+1)⁻¹*∑ lam : Fin (p.1+1),X p lam := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun lam _ => (pathExcess_bounds F S hF γ p lam).1))
  have hMean' : (lineAverage (fun ℓ => (GapLine ℓ : ℂ))).re ≤ B^(m+1)/((m+1).factorial : ℝ) :=
    hMean.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hSum0 hExcess (m+1)) (by positivity))
  calc
    _ ≤ modelFunctional F S (fun _ ℓ => GapLine ℓ) :=
      modelFunctional_mono F S hU hV _ _ hGapMeas (fun _ => measurable_const)
        C C hC hC hGapAbs hLineAbs (fun w _ ℓ => hCompare w ℓ)
    _ = 15*(6/Real.pi^2)*(lineAverage (fun ℓ => (GapLine ℓ : ℂ))).re := modelFunctional_line_const F S GapLine
    _ ≤ _ := mul_le_mul_of_nonneg_left hMean' (by positivity)
end

private lemma factorial_gap_decay (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∃ L₀ : ℝ,1 ≤ L₀ ∧ ∀ L : ℝ,L₀ ≤ L → ∀ N k : ℕ,
      (N:ℝ)+1 ≤ 4*Real.rpow L (1/2:ℝ) → Real.rpow L (19/25:ℝ) ≤ (k:ℝ) →
      (Cb*((N:ℝ)+1))^k/(k.factorial : ℝ) ≤
        Real.exp (-(1/10:ℝ)*Real.rpow L (19/25:ℝ)*Real.log L) := by
  let D := 4*Real.exp 1*Cb
  obtain ⟨L₀,hL₀,hD⟩ := eventually_const_rpow_le D 0 (4/25) (by norm_num)
  refine ⟨L₀,hL₀,?_⟩
  intro L hL N k hN hk
  have hL1 : 1 ≤ L := hL₀.trans hL
  have hLpos : 0<L := by linarith
  have hkposR : 0<(k:ℝ) := (Real.rpow_pos_of_pos hLpos (19/25:ℝ)).trans_le hk
  have hkpos : 0<k := by exact_mod_cast hkposR
  have hD' : D ≤ Real.rpow L (4/25:ℝ) := by simpa using hD L hL
  have hFrac : Real.rpow L (1/2:ℝ)/Real.rpow L (19/25:ℝ)=Real.rpow L (-13/50:ℝ) := by
    calc
      _ = Real.rpow L ((1/2:ℝ)-19/25) := (Real.rpow_sub hLpos _ _).symm
      _ = _ := by congr 1;norm_num
  have hMul : Real.rpow L (4/25:ℝ)*Real.rpow L (-13/50:ℝ)=Real.rpow L (-1/10:ℝ) := by
    calc
      _ = Real.rpow L ((4/25:ℝ)+(-13/50)) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1;norm_num
  have hnum : Real.exp 1*(Cb*((N:ℝ)+1)) ≤ D*Real.rpow L (1/2:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hN (mul_nonneg (Real.exp_pos 1).le hCb)
    dsimp only [D]
    nlinarith
  have hnum0 : 0 ≤ D*Real.rpow L (1/2:ℝ) :=
    mul_nonneg (by dsimp [D];positivity) (Real.rpow_nonneg hLpos.le _)
  have hratio : Real.exp 1*(Cb*((N:ℝ)+1))/(k:ℝ) ≤ Real.rpow L (-1/10:ℝ) := by
    calc
      _ ≤ D*Real.rpow L (1/2:ℝ)/(k:ℝ) := div_le_div_of_nonneg_right hnum hkposR.le
      _ ≤ D*Real.rpow L (1/2:ℝ)/Real.rpow L (19/25:ℝ) :=
        div_le_div_of_nonneg_left hnum0 (Real.rpow_pos_of_pos hLpos _) hk
      _ = D*Real.rpow L (-13/50:ℝ) := by rw [mul_div_assoc,hFrac]
      _ ≤ Real.rpow L (4/25:ℝ)*Real.rpow L (-13/50:ℝ) :=
        mul_le_mul_of_nonneg_right hD' (Real.rpow_nonneg hLpos.le _)
      _ = _ := hMul
  have heq : (Real.rpow L (-1/10:ℝ))^k=Real.exp ((Real.log L*(-1/10:ℝ))*(k:ℝ)) := by
    calc
      _ = (Real.exp (Real.log L*(-1/10:ℝ)))^k :=
        congrArg (fun t : ℝ => t^k) (Real.rpow_def_of_pos hLpos (-1/10))
      _ = _ := real_exp_pow_nat _ _
  calc
    _ ≤ (Real.exp 1*(Cb*((N:ℝ)+1))/(k:ℝ))^k := factorial_tail_bound _ (by positivity) k hkpos
    _ ≤ (Real.rpow L (-1/10:ℝ))^k := pow_le_pow_left₀ (by positivity) hratio k
    _ = _ := heq
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
      have hm := mul_le_mul_of_nonpos_left hk (by nlinarith : Real.log L*(-1/10:ℝ) ≤ 0)
      nlinarith)

/-- `det:root-replacement` — PD 03:593-737 (Lemma 3.4).  REPLACES the frozen `root_replacement`
(which concerned one observable on `SL₂(ℤ/S)` with few nonzero values).  Proof: keep exact
factors at active primes, sandwich the inactive product by Bonferroni polynomials of degrees near
`T = ⌈L^{0.76}⌉` (`root_bonferroni`, gap `exp(-Ω(L^{0.76} log L))` absorbs the budget of
`root_budget`); each monomial involves a squarefree modulus `log S ≪ L^{0.96}`, counted on the
grid cubes of side `x^{-c_δ/8}` by `root_lines`; cubes meeting a boundary
(`root_arch_boundary`) have volume `x^{-c_δ/8+o(1)}`; total error `x^{-c_δ/8+o(1)}`, which is
`O_A(L^{-AN})` since `N ≍ L^{1/2}`. -/
theorem root_replacement (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        |physicalRootAverage F S - modelRootAverage F S| ≤
          C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  sorry


end

end ArtinPrimitiveRoots.TypeII.PD
