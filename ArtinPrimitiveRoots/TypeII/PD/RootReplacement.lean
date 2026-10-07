import ArtinPrimitiveRoots.TypeII.PD.Physical
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

/-- `t2:pd.path-expansion` (new node) — PD 03:595-609.  Exact identity: the determinant moment is
the physical root average of the line-model moment.  Proof: `P ↦ z = g_P⁻¹ P` is a bijection of
primitive vectors with `det(gz,gz') = det(z,z')`; for integer `g`, `p ∣ (gz)₁ ⇔ [z]_p` equals the
kernel line of `(u,c)`; `r_{gz} = τ(w)/τ(z) mod 1` (03:683-685); `𝒢` and the damping commute
with `𝒮`.  The threshold makes the bands disjoint (so `markedOmega = envOmega`). -/
theorem path_expansion (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        detMoment F S = physicalRootAverage F S := by
  sorry

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
  sorry

/-! ### Sub-nodes of the root replacement -/

/-- `t2:pd.root-lines` (new node) — corollary of `lem:root-residue` (frozen `root_residue`),
PD 03:667-678.  Counting primitive roots in a box with prescribed kernel lines at the primes of a
squarefree `S`: the number of `g₀ ∈ SL₂(ℤ/S)` with prescribed first-row kernel lines is
`|SL₂(ℤ/S)| ∏_{p∣S} (p+1)⁻¹` (CRT; at each prime the kernel is uniform on the `p+1` lines). -/
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

private lemma rootCompletionMatrix_kernelLine (Sq p u v : ℕ) (hSq : 0 < Sq)
    (hp : p ∣ Sq) :
    kernelLine p ((rootCompletionMatrix Sq u v 0 0).val % p)
        ((rootCompletionMatrix Sq u v 0 1).val % p) = kernelLine p u (rootC u v) := by
  have hU : (rootCompletionMatrix Sq u v 0 0).val % p = u % p := by
    simp [rootCompletionMatrix, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hp]
  have hC : (rootCompletionMatrix Sq u v 0 1).val % p = rootC u v % p := by
    simp [rootCompletionMatrix, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hp]
  rw [hU, hC]
  simp [kernelLine, projLine, Nat.cast_mod]

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
  sorry

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
  sorry

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
