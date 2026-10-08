import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.RestrictedComponents
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CocycleQuotient
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.SmallPowers
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.Congruence
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.SubgroupTopology
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CongruenceTopology
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CompletionCompact
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.CongruenceCompact
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.IntegralGL
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.LocalEffective
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.RestrictedCentralQuotient
import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.GlobalPivot


/-!
# P-COVER (route C): the cubic cover of `PGL₂` — top-node statements (design draft)

Blueprint: `research/blueprint/A1-P-COVER.md`. Imports the frozen A1 interface only.

The section `Core` is the **shared theta core**: it is copied verbatim into every route-C draft
(`A1-P-TORUS-IND.lean`, `A1-P-LOCAL-INT.lean`, …) and is to be frozen together with P-COVER.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## Core (shared, frozen with P-COVER) -/

section Core

variable (K : Type) [Field K]

/-- `n(x)`. -/
def upperM (x : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])

/-- `n̄(x)`. -/
def lowerM (x : K) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp [Matrix.det_fin_two])

/-- `a(y) = diag(y,1)`. -/
def diagM (y : Kˣ) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(y : K), 0; 0, 1] (by simp [Matrix.det_fin_two])

/-- `w`. -/
def weylM : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

/-- `PGL₂(K)`. -/
abbrev PGL2 : Type := GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K)

end Core

/-- The ball `𝔭^m` of a completion (valuation `≤ exp(-m)`). -/
def ball (v : FinPlace F) (m : ℤ) : Set (v.adicCompletion F) :=
  {x | Valued.v x ≤ WithZero.exp (-m)}

/-! ## The KP cocycle (`c = 2`) -/

section Cocycle

variable (D : FieldData F) (H : HilbertData F) (v : FinPlace F)

/-- `x(g) = g₂₁` if `g₂₁ ≠ 0`, else `g₂₂` (10:216–220). -/
def xEntry (g : GL (Fin 2) (v.adicCompletion F)) : v.adicCompletion F :=
  if (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 then (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  else (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1

theorem xEntry_ne_zero (g : GL (Fin 2) (v.adicCompletion F)) : xEntry v g ≠ 0 := by
  classical
  unfold xEntry
  split_ifs with h
  · exact h
  · intro h22
    have h10 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
      simpa using h
    have hdet := g.det_ne_zero
    apply hdet
    rw [Matrix.det_fin_two]
    simp [h10, h22]

/-- `x(g)` as a unit. -/
def xU (g : GL (Fin 2) (v.adicCompletion F)) : (v.adicCompletion F)ˣ :=
  Units.mk0 (xEntry v g) (xEntry_ne_zero v g)

/-- `det g` as a unit. -/
def detU (g : GL (Fin 2) (v.adicCompletion F)) : (v.adicCompletion F)ˣ :=
  Matrix.GeneralLinearGroup.det g

private theorem xEntry_scalar_left (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    xEntry v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = c * xEntry v g := by
  classical
  by_cases h10 : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
  · have hp10 :
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
      simp [Matrix.mul_apply, h10]
    have hp11 :
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 =
          (c : v.adicCompletion F) * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
      simp [Matrix.mul_apply]
    simp [xEntry, h10, hp10, hp11]
  · have hp10 :
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
          (c : v.adicCompletion F) * (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
      simp [Matrix.mul_apply]
    simp [xEntry, h10, hp10, c.ne_zero]

private theorem xEntry_scalar_right (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    xEntry v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) c) = c * xEntry v g := by
  rw [← Matrix.GeneralLinearGroup.scalar_commute c g]
  exact xEntry_scalar_left v c g

private theorem xU_scalar_left (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    xU v (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = c * xU v g := by
  apply Units.ext
  simp [xU, xEntry_scalar_left]

private theorem xU_scalar_right (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    xU v (g * Matrix.GeneralLinearGroup.scalar (Fin 2) c) = c * xU v g := by
  rw [← Matrix.GeneralLinearGroup.scalar_commute c g]
  exact xU_scalar_left v c g

private theorem xU_scalar (c : (v.adicCompletion F)ˣ) :
    xU v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = c := by
  apply Units.ext
  simp [xU, xEntry, Matrix.GeneralLinearGroup.scalar]

private theorem detU_scalar (c : (v.adicCompletion F)ˣ) :
    detU v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = c ^ 2 := by
  simp [detU]

/-- The KP cocycle with `c = 2`, read in `μ3(ℂ)` through `ι = σ0⁻¹`:
`σ(g,h) = ι((x(gh)/x(g), x(gh)/(x(h)det g))₃ · (det g, det h)₃²)` with `(a,b)₃ = hilb(a,b)²`;
equivalently `muThree(hilb(x(gh)/(x(h)det g), x(gh)/x(g))) · muThree(hilb(det g, det h))`. -/
def kpCocycle (g h : GL (Fin 2) (v.adicCompletion F)) : rootsOfUnity 3 ℂ :=
  muThree D (H.hilb v (xU v (g * h) / (xU v h * detU v g)) (xU v (g * h) / xU v g)) *
    muThree D (H.hilb v (detU v g) (detU v h))

private theorem muThree_one : muThree D (1 : rootsOfUnity 6 F) = 1 := by
  apply rootsOfUnity.coe_injective
  simp [muThree]

private theorem muThree_mul (ζ ξ : rootsOfUnity 6 F) :
    muThree D (ζ * ξ) = muThree D ζ * muThree D ξ := by
  apply rootsOfUnity.coe_injective
  simp [muThree, map_mul, mul_pow]

private theorem hilb_one_left (b : (v.adicCompletion F)ˣ) : H.hilb v 1 b = 1 := by
  exact H.sixth_power v 1 b ⟨1, by simp⟩

private theorem hilb_one_right (a : (v.adicCompletion F)ˣ) : H.hilb v a 1 = 1 := by
  have h := H.skew v a 1
  rw [hilb_one_left H v a] at h
  simpa using h

private def kpPairing : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ →* rootsOfUnity 3 ℂ where
  toFun a := {
    toFun := fun b => muThree D (H.hilb v a b)
    map_one' := by
      rw [hilb_one_right H v a, muThree_one]
    map_mul' := by
      intro b b'
      rw [H.mul_right, muThree_mul]
  }
  map_one' := by
    apply MonoidHom.ext
    intro b
    change muThree D (H.hilb v 1 b) = 1
    rw [hilb_one_left H v b, muThree_one]
  map_mul' := by
    intro a a'
    apply MonoidHom.ext
    intro b
    change muThree D (H.hilb v (a * a') b) =
      muThree D (H.hilb v a b) * muThree D (H.hilb v a' b)
    rw [H.mul_left, muThree_mul]

private theorem kpPairing_skew (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a b * kpPairing D H v b a = 1 := by
  change muThree D (H.hilb v a b) * muThree D (H.hilb v b a) = 1
  rw [← muThree_mul, H.skew, muThree_one]

private theorem kpPairing_inv_left (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a⁻¹ b = (kpPairing D H v a b)⁻¹ := by
  have h := map_inv (kpPairing D H v) a
  have h' := congrArg (fun f : (v.adicCompletion F)ˣ →* rootsOfUnity 3 ℂ => f b) h
  simpa using h'

private theorem kpPairing_pow_left (a b : (v.adicCompletion F)ˣ) (n : ℕ) :
    kpPairing D H v (a ^ n) b = kpPairing D H v a b ^ n := by
  have h := map_pow (kpPairing D H v) a n
  have h' := congrArg (fun f : (v.adicCompletion F)ˣ →* rootsOfUnity 3 ℂ => f b) h
  simpa using h'

private theorem kpPairing_pow_right (a b : (v.adicCompletion F)ˣ) (n : ℕ) :
    kpPairing D H v a (b ^ n) = kpPairing D H v a b ^ n :=
  map_pow (kpPairing D H v a) b n

private theorem kpPairing_cube (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a b ^ 3 = 1 := by
  apply Subtype.ext
  exact (kpPairing D H v a b).2

private theorem kpPairing_four (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a b ^ 4 = kpPairing D H v a b := by
  have h := kpPairing_cube D H v a b
  calc
    kpPairing D H v a b ^ 4 = kpPairing D H v a b ^ 3 * kpPairing D H v a b := by
      rw [show 4 = 3 + 1 by norm_num, pow_succ]
    _ = kpPairing D H v a b := by rw [h, one_mul]

private theorem kpPairing_inv_square (a b : (v.adicCompletion F)ˣ) :
    (kpPairing D H v a b)⁻¹ ^ 2 = kpPairing D H v a b := by
  have h := kpPairing_cube D H v a b
  have h2 : kpPairing D H v a b ^ 2 * kpPairing D H v a b = 1 := by
    simpa [pow_succ] using h
  have hinv : (kpPairing D H v a b)⁻¹ = kpPairing D H v a b ^ 2 :=
    (eq_inv_of_mul_eq_one_left h2).symm
  calc
    (kpPairing D H v a b)⁻¹ ^ 2 = (kpPairing D H v a b ^ 2) ^ 2 := by rw [hinv]
    _ = kpPairing D H v a b ^ 4 := by rw [← pow_mul]
    _ = kpPairing D H v a b := kpPairing_four D H v a b

private theorem kpPairing_inverse_swap (a b : (v.adicCompletion F)ˣ) :
    (kpPairing D H v a b)⁻¹ = kpPairing D H v b a := by
  exact (eq_inv_of_mul_eq_one_right (kpPairing_skew D H v a b)).symm

private theorem kpPairing_square_swap (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a b ^ 2 = kpPairing D H v b a := by
  have h := kpPairing_skew D H v a b
  have hab : kpPairing D H v a b = (kpPairing D H v b a)⁻¹ :=
    eq_inv_of_mul_eq_one_left h
  rw [hab]
  exact kpPairing_inv_square D H v b a

private theorem kpPairing_div_left (a b c : (v.adicCompletion F)ˣ) :
    kpPairing D H v (a / b) c = kpPairing D H v a c * (kpPairing D H v b c)⁻¹ := by
  simpa [div_eq_mul_inv] using map_div₂ (kpPairing D H v) a b c

private theorem kpCocycle_pairing (g h : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v g h =
      kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) (xU v (g * h) / xU v g) *
        kpPairing D H v (detU v g) (detU v h) := rfl

/-- The Steinberg relation for the sextic symbol at `v`. **Not a field of the frozen
`HilbertData`** (A1 report, interface gap G1); ClassFieldTheory supplies it (`IsSteinberg`). -/
def SteinbergAt : Prop :=
  ∀ a : (v.adicCompletion F)ˣ, ∀ h : (1 : v.adicCompletion F) - a ≠ 0,
    H.hilb v a (Units.mk0 _ h) = 1

end Cocycle

/-- **Local cover at a finite place** (abstract interface; P-COVER constructs it from the KP
cocycle, every later package works over an arbitrary instance). The central `μ3` is `μ3(ℂ)`
through `ι = σ0⁻¹`; the torus law is the frozen `muThree` law. -/
structure FinLocalCover (D : FieldData F) (H : HilbertData F) (v : FinPlace F) where
  L : Type
  [grp : Group L]
  [top : TopologicalSpace L]
  [tg : IsTopologicalGroup L]
  z : rootsOfUnity 3 ℂ →* L
  z_inj : Function.Injective z
  z_central : ∀ ζ g, z ζ * g = g * z ζ
  pr : L →* PGL2 (v.adicCompletion F)
  pr_surj : Function.Surjective pr
  pr_ker : pr.ker = z.range
  pr_cont : Continuous pr
  pr_open : IsOpenMap pr
  n : Multiplicative (v.adicCompletion F) →* L
  nbar : Multiplicative (v.adicCompletion F) →* L
  a : (v.adicCompletion F)ˣ → L
  w : L
  /-- the set-theoretic section `g ↦ (g, 1)` of the KP construction -/
  sec : GL (Fin 2) (v.adicCompletion F) → L
  sec_mul : ∀ g h, sec g * sec h = z (kpCocycle D H v g h) * sec (g * h)
  sec_pr : ∀ g, pr (sec g) = QuotientGroup.mk g
  sec_scalar : ∀ c, sec (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1
  sec_n : ∀ x, n (Multiplicative.ofAdd x) = sec (upperM _ x)
  sec_nbar : ∀ x, nbar (Multiplicative.ofAdd x) = sec (lowerM _ x)
  sec_a : ∀ y, a y = sec (diagM _ y)
  sec_w : w = sec (weylM _)
  pr_n : ∀ x, pr (n (Multiplicative.ofAdd x)) = QuotientGroup.mk (upperM _ x)
  pr_nbar : ∀ x, pr (nbar (Multiplicative.ofAdd x)) = QuotientGroup.mk (lowerM _ x)
  pr_a : ∀ y, pr (a y) = QuotientGroup.mk (diagM _ y)
  pr_w : pr w = QuotientGroup.mk (weylM (v.adicCompletion F))
  a_one : a 1 = 1
  /-- torus law `a(x)a(y) = C(x,y)a(xy)`, `C = muThree ∘ hilb` (10:96–97 with `ι = σ0⁻¹`). -/
  a_mul : ∀ x y, a x * a y = z (muThree D (H.hilb v x y)) * a (x * y)
  /-- exact lift identities (eq:theta-lift-identities, 10:206–248). -/
  lift_na : ∀ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ),
    n (Multiplicative.ofAdd x) * a y = a y * n (Multiplicative.ofAdd (x * ↑y⁻¹))
  lift_wa : ∀ y, w * a y * w⁻¹ = a y⁻¹
  lift_wn : ∀ Hh : (v.adicCompletion F)ˣ,
    w * n (Multiplicative.ofAdd (Hh : v.adicCompletion F)) =
      n (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
        a (-(Hh⁻¹ * Hh⁻¹)) *
          nbar (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))
  w_sq : w * w = 1
  w_n_w : ∀ x, w * n (Multiplicative.ofAdd x) * w = nbar (Multiplicative.ofAdd x)
  /-- small splitting subgroups `κ(K(𝔭^m))`, `m ≥ m0` (node cov:small-splitting). -/
  m0 : ℕ
  Kc : ℕ → Subgroup L
  Kc_open : ∀ m, m0 ≤ m → IsOpen (Kc m : Set L)
  Kc_compact : ∀ m, m0 ≤ m → IsCompact (Kc m : Set L)
  Kc_anti : ∀ m m', m0 ≤ m → m ≤ m' → Kc m' ≤ Kc m
  Kc_nhds : ∀ U ∈ nhds (1 : L), ∃ m, m0 ≤ m ∧ (Kc m : Set L) ⊆ U
  Kc_inj : ∀ m, m0 ≤ m → Set.InjOn pr (Kc m : Set L)
  n_Kc : ∀ m, m0 ≤ m → ∀ x ∈ ball v m, n (Multiplicative.ofAdd x) ∈ Kc m
  nbar_Kc : ∀ m, m0 ≤ m → ∀ x ∈ ball v m, nbar (Multiplicative.ofAdd x) ∈ Kc m
  a_Kc : ∀ m, m0 ≤ m → ∀ u : (v.adicCompletion F)ˣ,
    ((u : v.adicCompletion F) - 1) ∈ ball v m → a u ∈ Kc m

attribute [instance] FinLocalCover.grp FinLocalCover.top FinLocalCover.tg

/-- **Tame compact splitting** at a place `v ∤ 6` (cov:tame-splitting; KP Prop 0.1.3 replaced). -/
structure TameSplitting {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) where
  Kmax : Subgroup L.L
  open_ : IsOpen (Kmax : Set L.L)
  compact : IsCompact (Kmax : Set L.L)
  inj : Set.InjOn L.pr (Kmax : Set L.L)
  /-- `pr(Kmax)` is the image of `GL₂(O_v)`. -/
  image : L.pr '' (Kmax : Set L.L) =
    {g | ∃ k : GL (Fin 2) (v.adicCompletion F),
      (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (k⁻¹ : GL (Fin 2) _).val.det ∈ v.adicCompletionIntegers F ∧ QuotientGroup.mk k = g}
  n_mem : ∀ x ∈ v.adicCompletionIntegers F, L.n (Multiplicative.ofAdd x) ∈ Kmax
  a_mem : ∀ u : (v.adicCompletion F)ˣ, (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F → L.a u ∈ Kmax
  w_mem : L.w ∈ Kmax
  nbar_mem : ∀ x : v.adicCompletion F, Valued.v x < 1 → L.nbar (Multiplicative.ofAdd x) ∈ Kmax

section CocycleThm

variable (D : FieldData F) (H : HilbertData F) (v : FinPlace F)

private theorem kpPairing_one_left (b : (v.adicCompletion F)ˣ) :
    kpPairing D H v 1 b = 1 := by
  change muThree D (H.hilb v 1 b) = 1
  rw [hilb_one_left H v b, muThree_one D]

private theorem kpPairing_one_right (a : (v.adicCompletion F)ˣ) :
    kpPairing D H v a 1 = 1 := by
  change muThree D (H.hilb v a 1) = 1
  rw [hilb_one_right H v a, muThree_one D]

private theorem kpPairing_self (a : (v.adicCompletion F)ˣ) :
    kpPairing D H v a a = 1 := by
  let z := kpPairing D H v a a
  have hz2 : z ^ 2 = 1 := by
    have h := kpPairing_skew D H v a a
    change z * z = 1 at h
    simpa [pow_two, z] using h
  have hz3 : z ^ 3 = 1 := by
    simpa [z] using kpPairing_cube D H v a a
  have hz3' : z ^ 3 = z := by
    calc
      z ^ 3 = z ^ 2 * z := by simpa using (pow_succ z 2)
      _ = z := by rw [hz2]; simp
  calc
    z = z ^ 3 := hz3'.symm
    _ = 1 := hz3

private theorem kpPairing_neg_one_left (b : (v.adicCompletion F)ˣ) :
    kpPairing D H v (-1 : (v.adicCompletion F)ˣ) b = 1 := by
  let z := kpPairing D H v (-1 : (v.adicCompletion F)ˣ) b
  have hsq : ((-1 : (v.adicCompletion F)ˣ) ^ 2) = 1 := by ext; simp
  have hz2 : z ^ 2 = 1 := by
    rw [← kpPairing_pow_left D H v (-1) b 2, hsq, kpPairing_one_left]
  have hz3 : z ^ 3 = 1 := by
    simpa [z] using kpPairing_cube D H v (-1) b
  have hz3' : z ^ 3 = z := by
    calc
      z ^ 3 = z ^ 2 * z := by simpa using (pow_succ z 2)
      _ = z := by rw [hz2]; simp
  calc
    z = z ^ 3 := hz3'.symm
    _ = 1 := hz3

private theorem kpPairing_st (hSt : SteinbergAt H v) (a : (v.adicCompletion F)ˣ)
    (h : (1 : v.adicCompletion F) - a ≠ 0) :
    kpPairing D H v a (Units.mk0 _ h) = 1 := by
  change muThree D (H.hilb v a (Units.mk0 _ h)) = 1
  rw [hSt a h, muThree_one D]

private theorem kpPairing_mul_left (a b c : (v.adicCompletion F)ˣ) :
    kpPairing D H v (a * b) c = kpPairing D H v a c * kpPairing D H v b c := by
  have h := map_mul (kpPairing D H v) a b
  simpa using congrArg (fun q : (v.adicCompletion F)ˣ →* rootsOfUnity 3 ℂ => q c) h

private theorem kpPairing_neg_one_right (a : (v.adicCompletion F)ˣ) :
    kpPairing D H v a (-1) = 1 := by
  have h := kpPairing_skew D H v a (-1)
  rw [kpPairing_neg_one_left] at h
  simpa using h

private theorem kpPairing_neg_mul_left (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v (-a) b = kpPairing D H v a b := by
  have h : -a = (-1 : (v.adicCompletion F)ˣ) * a := by
    ext
    simp
  rw [h, kpPairing_mul_left, kpPairing_neg_one_left, one_mul]

private theorem kpPairing_mul_right (a b c : (v.adicCompletion F)ˣ) :
    kpPairing D H v a (b * c) = kpPairing D H v a b * kpPairing D H v a c := by
  exact map_mul (kpPairing D H v a) b c

private theorem kpPairing_neg_mul_right (a b : (v.adicCompletion F)ˣ) :
    kpPairing D H v a (-b) = kpPairing D H v a b := by
  have h : -b = (-1 : (v.adicCompletion F)ˣ) * b := by
    ext
    simp
  rw [h, kpPairing_mul_right, kpPairing_neg_one_right, one_mul]

private theorem kpPairing_div_right (a b c : (v.adicCompletion F)ˣ) :
    kpPairing D H v a (b / c) = kpPairing D H v a b * (kpPairing D H v a c)⁻¹ := by
  simpa [div_eq_mul_inv] using map_div₂ (kpPairing D H v a) b c

private theorem xU_upperM (t : v.adicCompletion F) :
    xU v (upperM (v.adicCompletion F) t) = 1 := by
  apply Units.ext
  simp [xU, xEntry, upperM]

private theorem detU_upperM (t : v.adicCompletion F) :
    detU v (upperM (v.adicCompletion F) t) = 1 := by
  apply Units.ext
  simp [detU, upperM, Matrix.det_fin_two]

private theorem xU_diagM (y : (v.adicCompletion F)ˣ) :
    xU v (diagM (v.adicCompletion F) y) = 1 := by
  apply Units.ext
  simp [xU, xEntry, diagM]

private theorem detU_diagM (y : (v.adicCompletion F)ˣ) :
    detU v (diagM (v.adicCompletion F) y) = y := by
  apply Units.ext
  simp [detU, diagM, Matrix.det_fin_two]

private theorem xU_mul_upperM (g : GL (Fin 2) (v.adicCompletion F))
    (t : v.adicCompletion F) :
    xU v (g * upperM (v.adicCompletion F) t) = xU v g := by
  classical
  apply Units.ext
  by_cases h : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
  · simp [xU, xEntry, h, upperM, Matrix.mul_apply]
  · simp [xU, xEntry, h, upperM, Matrix.mul_apply]

private theorem xU_mul_diagM (g : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ) :
    xU v (g * diagM (v.adicCompletion F) y) =
      if (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 then
        xU v g * y else xU v g := by
  classical
  apply Units.ext
  by_cases h : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
  · simp [xU, xEntry, h, diagM, Matrix.mul_apply]
  · simp [xU, xEntry, h, diagM, Matrix.mul_apply]

private theorem xU_eq_lowerLeft (g : GL (Fin 2) (v.adicCompletion F))
    (h : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0) :
    xU v g = Units.mk0 _ h := by
  apply Units.ext
  simp [xU, xEntry, h]

private theorem xU_eq_lowerRight (g : GL (Fin 2) (v.adicCompletion F))
    (h : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    xU v g = Units.mk0 _ (xEntry_ne_zero v g) := by
  apply Units.ext
  simp [xU, xEntry, h]

private theorem matrix_mul_21 (g h : GL (Fin 2) (v.adicCompletion F)) :
    ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem matrix_mul_22 (g h : GL (Fin 2) (v.adicCompletion F)) :
    ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem detU_mul (g h : GL (Fin 2) (v.adicCompletion F)) :
    detU v (g * h) = detU v g * detU v h := by
  simp [detU]

private theorem xU_diag_relation_10 (g h : GL (Fin 2) (v.adicCompletion F))
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    xU v (g * h) * xU v h = -(xU v g * detU v h) := by
  have hrow :
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
    simpa [matrix_mul_21] using hgh
  have hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 := by
    intro hc
    have hd : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
      have hz :
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
        simpa [hc] using hrow
      exact (mul_eq_zero.mp hz).resolve_right hh
    have hz : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 0 := by
      rw [Matrix.det_fin_two]
      simp [hc, hd]
    exact g.det_ne_zero hz
  have hprod :
      ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
        -((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 -
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0)) := by
    have hrow' :
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 +
          (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
      have ht := congrArg (fun q : v.adicCompletion F =>
        q * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) hrow
      calc
        _ = ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 +
            (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) *
              (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by ring
        _ = 0 := by simpa only [zero_mul] using ht
    linear_combination hrow'
  apply Units.ext
  simp only [Units.val_mul, Units.val_neg]
  simpa [xU, xEntry, hh, hg, hgh, detU, Matrix.det_fin_two, matrix_mul_22] using hprod

private theorem xU_diag_relation_01 (g h : GL (Fin 2) (v.adicCompletion F))
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0) :
    xU v (g * h) * xU v h = xU v g * detU v h := by
  have hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 := by
    intro hc
    apply hgh
    simp [matrix_mul_21, hc, hh]
  have hα : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 ≠ 0 := by
    intro h0
    apply hgh
    simp [matrix_mul_21, hh, h0]
  have hCval :
      ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 := by
    rw [matrix_mul_21]
    simp [hh]
  apply Units.ext
  simp only [Units.val_mul]
  simp [xU, xEntry, hh, hg, hα, hCval, detU, Matrix.det_fin_two]
  <;> ring

private theorem kpCocycle_upperM (h : GL (Fin 2) (v.adicCompletion F))
    (t : v.adicCompletion F) : kpCocycle D H v h (upperM (v.adicCompletion F) t) = 1 := by
  rw [kpCocycle_pairing]
  rw [xU_mul_upperM, xU_upperM, detU_upperM]
  simp [kpPairing_one_right]

private theorem kpCocycle_mul_upperM (g h : GL (Fin 2) (v.adicCompletion F))
    (t : v.adicCompletion F) :
    kpCocycle D H v g (h * upperM (v.adicCompletion F) t) = kpCocycle D H v g h := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hx : xU v (g * (h * upperM (v.adicCompletion F) t)) = xU v (g * h) := by
    simpa [mul_assoc] using xU_mul_upperM v (g * h) t
  rw [hx, xU_mul_upperM]
  have hdet : detU v (h * upperM (v.adicCompletion F) t) = detU v h := by
    rw [detU_mul, detU_upperM, mul_one]
  rw [hdet]

private theorem kpCocycle_good_upperM (g h : GL (Fin 2) (v.adicCompletion F))
    (t : v.adicCompletion F) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) (upperM (v.adicCompletion F) t) =
      kpCocycle D H v g (h * upperM (v.adicCompletion F) t) *
        kpCocycle D H v h (upperM (v.adicCompletion F) t) := by
  rw [kpCocycle_upperM D H v (g * h) t, kpCocycle_mul_upperM D H v g h t,
    kpCocycle_upperM D H v h t]

private theorem kpCocycle_mul_diagM_11 (g h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ)
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0) :
    kpCocycle D H v g (h * diagM (v.adicCompletion F) y) =
      kpCocycle D H v g h *
        kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) y *
          kpPairing D H v (detU v g) y := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hmul :
      g * (h * diagM (v.adicCompletion F) y) =
        (g * h) * diagM (v.adicCompletion F) y := by
    exact (mul_assoc g h _).symm
  rw [hmul]
  have hghM : ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) 1 0 ≠ 0 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using hgh
  have hxgh :
      xU v ((g * h) * diagM (v.adicCompletion F) y) = xU v (g * h) * y := by
    simpa [hghM] using xU_mul_diagM v (g * h) y
  have hxh : xU v (h * diagM (v.adicCompletion F) y) = xU v h * y := by
    simpa [hh] using xU_mul_diagM v h y
  have hdet : detU v (h * diagM (v.adicCompletion F) y) = detU v h * y := by
    simp [detU_mul, detU_diagM]
  rw [hxgh, hxh, hdet]
  have h₁ :
      (xU v (g * h) * y) / (xU v h * y * detU v g) =
        xU v (g * h) / (xU v h * detU v g) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  have h₂ :
      (xU v (g * h) * y) / xU v g =
        (xU v (g * h) / xU v g) * y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  rw [h₁, h₂, kpPairing_mul_right, kpPairing_mul_right]
  ac_rfl

private theorem kpCocycle_mul_diagM_10 (g h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ)
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    kpCocycle D H v g (h * diagM (v.adicCompletion F) y) =
      kpCocycle D H v g h *
        kpPairing D H v (xU v (g * h) / xU v g) y *
          kpPairing D H v (detU v g) y := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hmul :
      g * (h * diagM (v.adicCompletion F) y) =
        (g * h) * diagM (v.adicCompletion F) y := by
    exact (mul_assoc g h _).symm
  rw [hmul]
  have hghM : ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) 1 0 = 0 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using hgh
  have hxgh :
      xU v ((g * h) * diagM (v.adicCompletion F) y) = xU v (g * h) := by
    simpa [hghM] using xU_mul_diagM v (g * h) y
  have hxh : xU v (h * diagM (v.adicCompletion F) y) = xU v h * y := by
    simpa [hh] using xU_mul_diagM v h y
  have hdet : detU v (h * diagM (v.adicCompletion F) y) = detU v h * y := by
    simp [detU_mul, detU_diagM]
  rw [hxgh, hxh, hdet]
  have h₁ :
      xU v (g * h) / (xU v h * y * detU v g) =
        (xU v (g * h) / (xU v h * detU v g)) / y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  rw [h₁, kpPairing_div_left, kpPairing_mul_right, kpPairing_inverse_swap]
  ac_rfl

private theorem kpCocycle_mul_diagM_01 (g h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ)
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0) :
    kpCocycle D H v g (h * diagM (v.adicCompletion F) y) =
      kpCocycle D H v g h *
        kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) y *
          (kpPairing D H v (xU v (g * h) / xU v g) y)⁻¹ *
          kpPairing D H v (detU v g) y := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hmul :
      g * (h * diagM (v.adicCompletion F) y) =
        (g * h) * diagM (v.adicCompletion F) y := by
    exact (mul_assoc g h _).symm
  rw [hmul]
  have hghM : ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) 1 0 ≠ 0 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using hgh
  have hxgh :
      xU v ((g * h) * diagM (v.adicCompletion F) y) = xU v (g * h) * y := by
    simpa [hghM] using xU_mul_diagM v (g * h) y
  have hxh : xU v (h * diagM (v.adicCompletion F) y) = xU v h := by
    simpa [hh] using xU_mul_diagM v h y
  have hdet : detU v (h * diagM (v.adicCompletion F) y) = detU v h * y := by
    simp [detU_mul, detU_diagM]
  rw [hxgh, hxh, hdet]
  have h₁ :
      (xU v (g * h) * y) / (xU v h * detU v g) =
        (xU v (g * h) / (xU v h * detU v g)) * y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  have h₂ :
      (xU v (g * h) * y) / xU v g =
        (xU v (g * h) / xU v g) * y := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  rw [h₁, h₂, kpPairing_mul_left, kpPairing_mul_right, kpPairing_mul_right,
    kpPairing_self, kpPairing_mul_right]
  rw [← kpPairing_inverse_swap D H v (xU v (g * h) / xU v g) y]
  ac_rfl

private theorem kpCocycle_mul_diagM_00 (g h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ)
    (hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    kpCocycle D H v g (h * diagM (v.adicCompletion F) y) =
      kpCocycle D H v g h * kpPairing D H v (detU v g) y := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hmul :
      g * (h * diagM (v.adicCompletion F) y) =
        (g * h) * diagM (v.adicCompletion F) y := by
    exact (mul_assoc g h _).symm
  rw [hmul]
  have hghM : ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) 1 0 = 0 := by
    simpa only [Matrix.GeneralLinearGroup.coe_mul] using hgh
  have hxgh :
      xU v ((g * h) * diagM (v.adicCompletion F) y) = xU v (g * h) := by
    simpa [hghM] using xU_mul_diagM v (g * h) y
  have hxh : xU v (h * diagM (v.adicCompletion F) y) = xU v h := by
    simpa [hh] using xU_mul_diagM v h y
  have hdet : detU v (h * diagM (v.adicCompletion F) y) = detU v h * y := by
    simp [detU_mul, detU_diagM]
  rw [hxgh, hxh, hdet, kpPairing_mul_right]
  ac_rfl

private theorem kpCocycle_diagM_formula (h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ) :
    kpCocycle D H v h (diagM (v.adicCompletion F) y) =
      if (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 then
        kpPairing D H v (xU v h) y else kpPairing D H v (detU v h) y := by
  classical
  by_cases hc : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0
  · rw [kpCocycle_pairing, xU_mul_diagM, xU_diagM, detU_diagM]
    simp only [if_pos hc]
    have h₁ :
        (xU v h * y) / (1 * detU v h) = (xU v h / detU v h) * y := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul]
      field_simp <;> ring <;> norm_num
    have h₂ : (xU v h * y) / xU v h = y := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul]
      field_simp <;> ring <;> norm_num
    rw [h₁, h₂, kpPairing_mul_left, kpPairing_div_left, kpPairing_self]
    group
  · rw [kpCocycle_pairing, xU_mul_diagM, xU_diagM, detU_diagM]
    simp only [if_neg hc]
    simp [kpPairing_one_right]

private theorem kpCocycle_good_diagM (g h : GL (Fin 2) (v.adicCompletion F))
    (y : (v.adicCompletion F)ˣ) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) (diagM (v.adicCompletion F) y) =
      kpCocycle D H v g (h * diagM (v.adicCompletion F) y) *
        kpCocycle D H v h (diagM (v.adicCompletion F) y) := by
  classical
  by_cases hh : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0
  · by_cases hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0
    · rw [kpCocycle_diagM_formula D H v (g * h) y,
        kpCocycle_diagM_formula D H v h y]
      simp only [if_pos hgh, if_pos hh]
      rw [kpCocycle_mul_diagM_11 D H v g h y hh hgh]
      have hunit :
          (xU v (g * h) / (xU v h * detU v g)) * detU v g * xU v h = xU v (g * h) := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.val_mul]
        field_simp <;> ring
      have hpair : kpPairing D H v (xU v (g * h)) y =
          kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) y *
            kpPairing D H v (detU v g) y * kpPairing D H v (xU v h) y := by
        calc
          _ = kpPairing D H v
              ((xU v (g * h) / (xU v h * detU v g)) * detU v g * xU v h) y := by
            exact congrArg (fun z : (v.adicCompletion F)ˣ => kpPairing D H v z y) hunit.symm
          _ = _ := by rw [kpPairing_mul_left, kpPairing_mul_left]
      rw [hpair]
      ac_rfl
    · rw [kpCocycle_diagM_formula D H v (g * h) y,
        kpCocycle_diagM_formula D H v h y]
      have hghEq : ((g * h : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by simpa using hgh
      simp only [if_neg hgh, if_pos hh]
      rw [kpCocycle_mul_diagM_10 D H v g h y hh hghEq]
      have hrel := xU_diag_relation_10 v g h hh hghEq
      have hunit :
          (xU v (g * h) / xU v g) * detU v g * xU v h =
            -(detU v g * detU v h) := by
        calc
          _ = (xU v (g * h) * xU v h) / xU v g * detU v g := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ac_rfl
          _ = (-(xU v g * detU v h)) / xU v g * detU v g := by rw [hrel]
          _ = -(detU v g * detU v h) := by
            apply Units.ext
            simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg]
            field_simp <;> ring
      have hpair : kpPairing D H v (detU v g * detU v h) y =
          kpPairing D H v (xU v (g * h) / xU v g) y *
            kpPairing D H v (detU v g) y * kpPairing D H v (xU v h) y := by
        calc
          _ = kpPairing D H v (-(detU v g * detU v h)) y := by
            exact (kpPairing_neg_mul_left D H v (detU v g * detU v h) y).symm
          _ = kpPairing D H v
                ((xU v (g * h) / xU v g) * detU v g * xU v h) y := by
            exact congrArg (fun z : (v.adicCompletion F)ˣ => kpPairing D H v z y) hunit.symm
          _ = _ := by rw [kpPairing_mul_left, kpPairing_mul_left]
      rw [detU_mul v]
      rw [hpair]
      ac_rfl
  · by_cases hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0
    · rw [kpCocycle_diagM_formula D H v (g * h) y,
        kpCocycle_diagM_formula D H v h y]
      have hhEq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
        simpa using hh
      simp only [if_pos hgh, if_neg hh]
      rw [kpCocycle_mul_diagM_01 D H v g h y hhEq hgh]
      have hrel := xU_diag_relation_01 v g h hhEq hgh
      have hrel' : detU v h * xU v g = xU v (g * h) * xU v h := by
        calc
          _ = xU v g * detU v h := by ac_rfl
          _ = xU v (g * h) * xU v h := hrel.symm
      have hunit :
          (xU v (g * h) / (xU v h * detU v g)) * detU v g * detU v h /
              (xU v (g * h) / xU v g) = xU v (g * h) := by
        calc
          _ = detU v h * xU v g / xU v h := by
            apply Units.ext
            simp only [Units.val_div_eq_div_val, Units.val_mul]
            field_simp <;> ring
          _ = xU v (g * h) * xU v h / xU v h := by rw [hrel']
          _ = xU v (g * h) := by simp
      have hpair :
          kpPairing D H v (xU v (g * h)) y =
            kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) y *
              (kpPairing D H v (xU v (g * h) / xU v g) y)⁻¹ *
                kpPairing D H v (detU v g) y * kpPairing D H v (detU v h) y := by
        calc
          _ = kpPairing D H v
              ((xU v (g * h) / (xU v h * detU v g)) * detU v g * detU v h /
                (xU v (g * h) / xU v g)) y := by
            exact congrArg (fun z : (v.adicCompletion F)ˣ => kpPairing D H v z y) hunit.symm
          _ = _ := by
            rw [kpPairing_div_left, kpPairing_mul_left, kpPairing_mul_left]
            ac_rfl
      rw [hpair]
      ac_rfl
    · rw [kpCocycle_diagM_formula D H v (g * h) y,
        kpCocycle_diagM_formula D H v h y]
      have hhEq : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
        simpa using hh
      have hghEq : ((g * h : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by simpa using hgh
      simp only [if_neg hh, if_neg hgh]
      rw [kpCocycle_mul_diagM_00 D H v g h y hhEq hghEq, detU_mul v,
        kpPairing_mul_left]
      ac_rfl

set_option maxHeartbeats 5000000 in
private theorem kpPairing_cross_ratio (c gamma delta c' d' det det' :
    (v.adicCompletion F)ˣ) :
    kpPairing D H v (c' / (gamma * det)) (c' / c) *
        kpPairing D H v (d' / (det * det')) (d' / c') =
      kpPairing D H v (d' / (delta * det)) (d' / c) *
        kpPairing D H v (delta / det') (delta / gamma) *
          kpPairing D H v (c' * delta / (c * det'))
            (-(d' * gamma / (c * det'))) := by
  rw [kpPairing_neg_mul_right]
  simp only [kpPairing_div_left, kpPairing_div_right,
    kpPairing_mul_left, kpPairing_mul_right, kpPairing_self, mul_inv, inv_inv]
  rw [← kpPairing_inverse_swap D H v gamma c',
    ← kpPairing_inverse_swap D H v d' c',
    ← kpPairing_inverse_swap D H v det' c',
    ← kpPairing_inverse_swap D H v d' c,
    ← kpPairing_inverse_swap D H v gamma c,
    ← kpPairing_inverse_swap D H v det' delta,
    ← kpPairing_inverse_swap D H v det' c]
  simp only [inv_inv, one_mul, mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

private theorem xU_weylM : xU v (weylM (v.adicCompletion F)) = 1 := by
  apply Units.ext
  simp [xU, xEntry, weylM]

private theorem detU_weylM : detU v (weylM (v.adicCompletion F)) = -1 := by
  apply Units.ext
  simp [detU, weylM, Matrix.det_fin_two]

private theorem kpCocycle_good_weyl_of_symbol (g h : GL (Fin 2) (v.adicCompletion F))
    (hsym : kpPairing D H v
        (xU v (g * h) * xU v (h * weylM (v.adicCompletion F)) /
          (xU v g * detU v h))
        (-(xU v ((g * h) * weylM (v.adicCompletion F)) * xU v h /
          (xU v g * detU v h))) = 1) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) (weylM (v.adicCompletion F)) =
      kpCocycle D H v g (h * weylM (v.adicCompletion F)) *
        kpCocycle D H v h (weylM (v.adicCompletion F)) := by
  let a := xU v g
  let b := xU v h
  let n := xU v (h * weylM (v.adicCompletion F))
  let m := xU v (g * h)
  let q := xU v ((g * h) * weylM (v.adicCompletion F))
  let det := detU v g
  let det' := detU v h
  let p₁ := kpPairing D H v (m / (b * det)) (m / a)
  let p₂ := kpPairing D H v (q / (det * det')) (q / m)
  let p₃ := kpPairing D H v (q / (n * det)) (q / a)
  let p₄ := kpPairing D H v (n / det') (n / b)
  let s := kpPairing D H v det det'
  let x := kpPairing D H v (m * n / (a * det')) (-(q * b / (a * det')))
  have hx : x = 1 := by
    dsimp [x, a, b, n, m, q, det, det']
    exact hsym
  have hratio : p₁ * p₂ = p₃ * p₄ := by
    calc
      p₁ * p₂ = p₃ * p₄ * x := by
        dsimp [p₁, p₂, p₃, p₄, x]
        exact kpPairing_cross_ratio D H v a b n m q det det'
      _ = p₃ * p₄ := by
        rw [hx]
        simp
  have hdetFactor :
      kpPairing D H v (detU v g) (detU v h * (-1)) =
        kpPairing D H v (detU v g) (detU v h) := by
    rw [kpPairing_mul_right, kpPairing_neg_one_right, mul_one]
  have hmul :
      g * (h * weylM (v.adicCompletion F)) =
        (g * h) * weylM (v.adicCompletion F) := by
    exact (mul_assoc g h _).symm
  rw [kpCocycle_pairing, kpCocycle_pairing, kpCocycle_pairing, kpCocycle_pairing,
    hmul]
  rw [xU_weylM]
  simp_rw [detU_mul v]
  rw [detU_weylM]
  simp only [one_mul]
  rw [hdetFactor]
  simp only [kpPairing_neg_one_right, mul_one]
  change (p₁ * s) * p₂ = (p₃ * s) * p₄
  calc
    (p₁ * s) * p₂ = (p₁ * p₂) * s := by ac_rfl
    _ = (p₃ * p₄) * s := by rw [hratio]
    _ = (p₃ * s) * p₄ := by ac_rfl

private theorem xU_weyl_relation_c0 (g h : GL (Fin 2) (v.adicCompletion F))
    (hc : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0) :
    xU v (g * h) * xU v (h * weylM (v.adicCompletion F)) =
      xU v ((g * h) * weylM (v.adicCompletion F)) * xU v h := by
  classical
  have hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 := by
    have hx := xEntry_ne_zero v g
    simpa [xEntry, hc] using hx
  have hC :
      ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
    rw [matrix_mul_21]
    simp [hc]
  have hD :
      ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
    rw [matrix_mul_22]
    simp [hc]
  by_cases hgamma : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0
  · by_cases hdelta : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0
    · have hCne :
          ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 :=
        by rw [hC]; exact mul_ne_zero hg hgamma
      have hDne :
          ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 :=
        by rw [hD]; exact mul_ne_zero hg hdelta
      apply Units.ext
      simp [xU, xEntry, weylM, hc, hg, hgamma, hdelta, hC, hD, hCne, hDne,
        Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring
    · have hdelta0 : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
        simpa using hdelta
      have hCne :
          ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 :=
        by rw [hC]; exact mul_ne_zero hg hgamma
      have hD0 :
          ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
        rw [hD, hdelta0]
        simp
      apply Units.ext
      simp [xU, xEntry, weylM, hc, hg, hgamma, hdelta0, hC, hD, hCne, hD0,
        Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring
  · have hgamma0 : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
      simpa using hgamma
    have hdelta : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 := by
      have hx := xEntry_ne_zero v h
      simpa [xEntry, hgamma0] using hx
    have hC0 :
        ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
      rw [hC, hgamma0]
      simp
    have hDne :
        ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 :=
      by rw [hD]; exact mul_ne_zero hg hdelta
    apply Units.ext
    simp [xU, xEntry, weylM, hc, hg, hgamma0, hdelta, hC0, hD, hDne,
      Matrix.mul_apply, Fin.sum_univ_two]
    <;> ring

private theorem kpCocycle_good_weyl_generic (hSt : SteinbergAt H v)
    (g h : GL (Fin 2) (v.adicCompletion F))
    (hc : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hgamma : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hdelta : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0)
    (hgh : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (hghd : ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) (weylM (v.adicCompletion F)) =
      kpCocycle D H v g (h * weylM (v.adicCompletion F)) *
        kpCocycle D H v h (weylM (v.adicCompletion F)) := by
  classical
  let cU : (v.adicCompletion F)ˣ := Units.mk0 _ hc
  let gammaU : (v.adicCompletion F)ˣ := Units.mk0 _ hgamma
  let deltaU : (v.adicCompletion F)ˣ := Units.mk0 _ hdelta
  let cpU : (v.adicCompletion F)ˣ := Units.mk0 _ hgh
  let dpU : (v.adicCompletion F)ˣ := Units.mk0 _ hghd
  let det := detU v g
  let det' := detU v h
  let X : (v.adicCompletion F)ˣ := cpU * deltaU / (cU * det')
  let Y : (v.adicCompletion F)ˣ := -(dpU * gammaU / (cU * det'))
  have hcross :
      (((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 -
        (((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 *
        ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  have hcval : (cU : v.adicCompletion F) =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
    simp [cU]
  have hgammaval : (gammaU : v.adicCompletion F) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
    simp [gammaU]
  have hdeltaval : (deltaU : v.adicCompletion F) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
    simp [deltaU]
  have hcpval : (cpU : v.adicCompletion F) =
      ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 := by
    simp [cpU]
  have hdpval : (dpU : v.adicCompletion F) =
      ((g * h : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
    simp [dpU]
  have hdetval : (det' : v.adicCompletion F) =
      (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
    rfl
  have hXY : (1 : v.adicCompletion F) - (X : v.adicCompletion F) = (Y : v.adicCompletion F) := by
    dsimp [X, Y]
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg]
    rw [hcval, hgammaval, hdeltaval, hcpval, hdpval, hdetval]
    field_simp [hc, h.det_ne_zero]
    rw [← hcross]
    ring
  have hXne : (1 : v.adicCompletion F) - (X : v.adicCompletion F) ≠ 0 := by
    rw [hXY]
    exact Y.ne_zero
  have hYunit : Y = Units.mk0 _ hXne := by
    apply Units.ext
    exact hXY.symm
  have hStein := kpPairing_st D H v hSt X hXne
  rw [← hYunit] at hStein
  have hxg : xU v g = cU := by simpa [cU] using xU_eq_lowerLeft v g hc
  have hxh : xU v h = gammaU := by simpa [gammaU] using xU_eq_lowerLeft v h hgamma
  have hxgh : xU v (g * h) = cpU := by simpa [cpU] using xU_eq_lowerLeft v (g * h) hgh
  have hxhw : xU v (h * weylM (v.adicCompletion F)) = deltaU := by
    apply Units.ext
    simp [xU, xEntry, weylM, deltaU, hdelta, Matrix.mul_apply, Fin.sum_univ_two]
  have hxghw : xU v ((g * h) * weylM (v.adicCompletion F)) = dpU := by
    apply Units.ext
    change xEntry v ((g * h) * weylM (v.adicCompletion F)) = (dpU : v.adicCompletion F)
    unfold xEntry
    have hentry :
        (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
          (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 =
          ((g * h : GL (Fin 2) (v.adicCompletion F)) :
            Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 := by
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hentry]
    simp only [if_pos hghd]
    simp [dpU]
  have hsym := hStein
  simp only [X, Y] at hsym
  rw [← hxgh, ← hxhw, ← hxg, ← hxh, ← hxghw] at hsym
  simp only [det'] at hsym
  exact kpCocycle_good_weyl_of_symbol D H v g h hsym

private theorem kpCocycle_good_weyl (hSt : SteinbergAt H v)
    (g h : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) (weylM (v.adicCompletion F)) =
      kpCocycle D H v g (h * weylM (v.adicCompletion F)) *
        kpCocycle D H v h (weylM (v.adicCompletion F)) := by
  classical
  let c₀ := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let γ₀ := (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let δ₀ := (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  let C₀ := ((g * h : GL (Fin 2) (v.adicCompletion F)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let D₀ := ((g * h : GL (Fin 2) (v.adicCompletion F)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  let a := xU v g
  let b := xU v h
  let n := xU v (h * weylM (v.adicCompletion F))
  let m := xU v (g * h)
  let q := xU v ((g * h) * weylM (v.adicCompletion F))
  let det' := detU v h
  let X : (v.adicCompletion F)ˣ := m * n / (a * det')
  let Y : (v.adicCompletion F)ˣ := -(q * b / (a * det'))
  have hcross : C₀ * δ₀ - D₀ * γ₀ = c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
    dsimp [C₀, D₀, c₀, γ₀, δ₀]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  have hCformula : C₀ =
      c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 * γ₀ := by
    dsimp [C₀, c₀, γ₀]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hDformula : D₀ =
      c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 +
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 * δ₀ := by
    dsimp [D₀, c₀, δ₀]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hc0 : c₀ = 0
  · have hrel := xU_weyl_relation_c0 v g h hc0
    have hY : Y = -X := by
      dsimp [Y, X]
      rw [← hrel]
    have hsym : kpPairing D H v X Y = 1 := by
      rw [hY, kpPairing_neg_mul_right, kpPairing_self]
    exact kpCocycle_good_weyl_of_symbol D H v g h hsym
  · have hc : c₀ ≠ 0 := by simpa using hc0
    by_cases hgamma0 : γ₀ = 0
    · have hdelta : δ₀ ≠ 0 := by
        have hx := xEntry_ne_zero v h
        simpa [xEntry, γ₀, δ₀, hgamma0] using hx
      have hγ : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
        simpa [γ₀] using hgamma0
      have hδ : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 := by
        simpa [δ₀] using hdelta
      have hα : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 ≠ 0 := by
        intro hα0
        have hz : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 0 := by
          rw [Matrix.det_fin_two]
          simp [hγ, hα0]
        exact h.det_ne_zero hz
      have hCval : C₀ = c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 := by
        rw [hCformula, hgamma0]
        simp
      have hCne : C₀ ≠ 0 := by rw [hCval]; exact mul_ne_zero hc hα
      have hrel := xU_diag_relation_01 v g h hgamma0 hCne
      have hn : n = b := by
        dsimp [n, b]
        apply Units.ext
        simp [xU, xEntry, weylM, hγ, hδ, Matrix.mul_apply, Fin.sum_univ_two]
      have hunit : m * b = a * det' := by
        simpa [m, b, a, det'] using hrel
      have hX : X = 1 := by
        dsimp [X]
        rw [hn, hunit]
        simp
      have hsym : kpPairing D H v X Y = 1 := by
        rw [hX, kpPairing_one_left]
      exact kpCocycle_good_weyl_of_symbol D H v g h hsym
    · have hgamma : γ₀ ≠ 0 := by simpa using hgamma0
      by_cases hdelta0 : δ₀ = 0
      · have hβ : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 ≠ 0 := by
          intro hβ0
          have hz : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 0 := by
            rw [Matrix.det_fin_two]
            have hδ : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
              simpa [δ₀] using hdelta0
            simp [hδ, hβ0]
          exact h.det_ne_zero hz
        have hδ : (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 0 := by
          simpa [δ₀] using hdelta0
        have hDval : D₀ = c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 := by
          rw [hDformula, hdelta0]
          simp
        have hDne : D₀ ≠ 0 := by rw [hDval]; exact mul_ne_zero hc hβ
        have ha : (a : v.adicCompletion F) = c₀ := by simp [a, xU, xEntry, hc, c₀]
        have hb : (b : v.adicCompletion F) = γ₀ := by simp [b, xU, xEntry, hgamma, γ₀]
        have hq : (q : v.adicCompletion F) = D₀ := by
          dsimp [q]
          change xEntry v ((g * h) * weylM (v.adicCompletion F)) = D₀
          unfold xEntry
          have hentry :
              (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
                (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
                Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = D₀ := by
            simp [D₀, weylM, Matrix.mul_apply, Fin.sum_univ_two]
          rw [hentry]
          simp only [if_pos hDne]
        have hdet : (det' : v.adicCompletion F) =
            (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by rfl
        have hrel : q * b = -(a * det') := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_neg]
          rw [hq, hb, ha, hdet, Matrix.det_fin_two, hDval, hδ]
          ring
        have hY : Y = 1 := by
          dsimp [Y]
          rw [hrel]
          simp [div_eq_mul_inv]
        have hsym : kpPairing D H v X Y = 1 := by
          rw [hY, kpPairing_one_right]
        exact kpCocycle_good_weyl_of_symbol D H v g h hsym
      · have hdelta : δ₀ ≠ 0 := by simpa using hdelta0
        by_cases hC0 : C₀ = 0
        · have hDne : D₀ ≠ 0 := by
            have hx := xEntry_ne_zero v (g * h)
            simpa [xEntry, C₀, D₀, hC0] using hx
          have hDrow :
              c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 +
                  (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 * δ₀ ≠ 0 := by
            rw [← hDformula]
            exact hDne
          have hrel := xU_diag_relation_10 v g h hgamma hC0
          have hmq : q = m := by
            apply Units.ext
            change xEntry v ((g * h) * weylM (v.adicCompletion F)) =
              xEntry v (g * h)
            unfold xEntry
            have hentry₁ :
                (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
                  (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
                  Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = D₀ := by
              simp [D₀, weylM, Matrix.mul_apply, Fin.sum_univ_two]
            have hentry₂ :
                (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
                  (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
                  Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = C₀ := by
              simp [C₀, weylM, Matrix.mul_apply, Fin.sum_univ_two]
            rw [hentry₁, hentry₂]
            have hCentry :
                ((g * h : GL (Fin 2) (v.adicCompletion F)) :
                  Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = C₀ := rfl
            have hDentry :
                ((g * h : GL (Fin 2) (v.adicCompletion F)) :
                  Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = D₀ := rfl
            rw [hCentry, hDentry]
            have hCfalse : ¬ C₀ ≠ 0 := by simpa using hC0
            simp only [if_pos hDne, if_neg hCfalse]
          have hunit : q * b = -(a * det') := by rw [hmq]; exact hrel
          have hY : Y = 1 := by
            dsimp [Y]
            rw [hunit]
            simp [div_eq_mul_inv]
          have hsym : kpPairing D H v X Y = 1 := by
            rw [hY, kpPairing_one_right]
          exact kpCocycle_good_weyl_of_symbol D H v g h hsym
        · have hCne : C₀ ≠ 0 := by simpa using hC0
          by_cases hD0 : D₀ = 0
          · have hq : q = m := by
              have hCrow :
                  c₀ * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 +
                      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 * γ₀ ≠ 0 := by
                rw [← hCformula]
                exact hCne
              apply Units.ext
              change xEntry v ((g * h) * weylM (v.adicCompletion F)) =
                xEntry v (g * h)
              unfold xEntry
              have hentry₁ :
                  (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
                    (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
                    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = D₀ := by
                simp [D₀, weylM, Matrix.mul_apply, Fin.sum_univ_two]
              have hentry₂ :
                  (((g * h : GL (Fin 2) (v.adicCompletion F)) * weylM
                    (v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F)) :
                    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = C₀ := by
                simp [C₀, weylM, Matrix.mul_apply, Fin.sum_univ_two]
              rw [hentry₁, hentry₂]
              have hCentry :
                  ((g * h : GL (Fin 2) (v.adicCompletion F)) :
                    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = C₀ := rfl
              have hDentry :
                  ((g * h : GL (Fin 2) (v.adicCompletion F)) :
                    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = D₀ := rfl
              rw [hCentry, hDentry]
              have hDfalse : ¬ D₀ ≠ 0 := by simpa using hD0
              simp only [if_neg hDfalse, if_pos hCne]
            have ha : (a : v.adicCompletion F) = c₀ := by simp [a, xU, xEntry, hc, c₀]
            have hm : (m : v.adicCompletion F) = C₀ := by
              dsimp [m]
              change xEntry v (g * h) = C₀
              unfold xEntry
              have hentry :
                  ((g * h : GL (Fin 2) (v.adicCompletion F)) :
                    Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = C₀ := rfl
              rw [hentry]
              simp only [if_pos hCne]
            have hn : (n : v.adicCompletion F) = δ₀ := by
              simp [n, xU, xEntry, weylM, hdelta, δ₀, Matrix.mul_apply, Fin.sum_univ_two]
            have hdet : (det' : v.adicCompletion F) =
                (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by rfl
            have hunit : m * n = a * det' := by
              apply Units.ext
              simp only [Units.val_mul]
              rw [hm, hn, ha, hdet]
              simpa [hD0, C₀, D₀] using hcross
            have hX : X = 1 := by
              dsimp [X]
              rw [hunit]
              simp
            have hsym : kpPairing D H v X Y = 1 := by
              rw [hX, kpPairing_one_left]
            exact kpCocycle_good_weyl_of_symbol D H v g h hsym
          · have hDne : D₀ ≠ 0 := by simpa using hD0
            exact kpCocycle_good_weyl_generic D H v hSt g h hc hgamma hdelta hCne hDne

private theorem kpCocycle_scalar_right_formula (g : GL (Fin 2) (v.adicCompletion F))
    (c : (v.adicCompletion F)ˣ) :
    kpCocycle D H v g (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      kpPairing D H v (xU v g) c * kpPairing D H v (detU v g) c := by
  rw [kpCocycle_pairing]
  simp only [xU_scalar_right, xU_scalar, detU_scalar]
  have h₁ : (c * xU v g) / (c * detU v g) = xU v g / detU v g := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  have h₂ : (c * xU v g) / xU v g = c := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  rw [h₁, h₂, kpPairing_div_left, kpPairing_pow_right]
  group

private theorem kpCocycle_mul_scalar_formula (g h : GL (Fin 2) (v.adicCompletion F))
    (c : (v.adicCompletion F)ˣ) :
    kpCocycle D H v g (h * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) c *
        kpCocycle D H v g h * kpPairing D H v (detU v g) c ^ 2 := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  have hmul :
      g * (h * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        (g * h) * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    exact (mul_assoc g h _).symm
  rw [hmul, xU_scalar_right, xU_scalar_right]
  have hdet :
      detU v (h * Matrix.GeneralLinearGroup.scalar (Fin 2) c) = detU v h * c ^ 2 := by
    simp [detU, detU_scalar]
  rw [hdet]
  have h₁ :
      (c * xU v (g * h)) / (c * xU v h * detU v g) =
        xU v (g * h) / (xU v h * detU v g) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  have h₂ :
      (c * xU v (g * h)) / xU v g =
        c * (xU v (g * h) / xU v g) := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp <;> ring
  rw [h₁, h₂, kpPairing_mul_right, kpPairing_mul_right, kpPairing_pow_right]
  ac_rfl

private theorem kpPairing_scalar_cancellation (X Y d e c : (v.adicCompletion F)ˣ) :
    kpPairing D H v (X / (Y * d)) c * kpPairing D H v d c ^ 2 *
        kpPairing D H v Y c * kpPairing D H v e c =
      kpPairing D H v X c * kpPairing D H v (d * e) c := by
  calc
    _ = kpPairing D H v X c *
          ((kpPairing D H v Y c)⁻¹ * kpPairing D H v Y c) *
          ((kpPairing D H v d c)⁻¹ * kpPairing D H v d c ^ 2) *
          kpPairing D H v e c := by
      rw [kpPairing_div_left, kpPairing_mul_left]
      simp only [mul_inv]
      ac_rfl
    _ = kpPairing D H v X c * kpPairing D H v d c * kpPairing D H v e c := by
      let z := kpPairing D H v d c
      have hz : z⁻¹ * z ^ 2 = z := by
        calc
          z⁻¹ * z ^ 2 = z⁻¹ * (z * z) := by rw [pow_two]
          _ = (z⁻¹ * z) * z := by rw [mul_assoc]
          _ = z := by simp
      simp [z, hz, mul_assoc]
    _ = kpPairing D H v X c *
          (kpPairing D H v d c * kpPairing D H v e c) := by ac_rfl
    _ = kpPairing D H v X c * kpPairing D H v (d * e) c := by
      exact congrArg (fun z : rootsOfUnity 3 ℂ => kpPairing D H v X c * z)
        (kpPairing_mul_left D H v d e c).symm

private theorem kpCocycle_good_scalar (g h : GL (Fin 2) (v.adicCompletion F))
    (c : (v.adicCompletion F)ˣ) :
    kpCocycle D H v g h *
        kpCocycle D H v (g * h) (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      kpCocycle D H v g (h * Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
        kpCocycle D H v h (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [kpCocycle_scalar_right_formula, kpCocycle_mul_scalar_formula,
    kpCocycle_scalar_right_formula]
  have hdet : detU v (g * h) = detU v g * detU v h := by simp [detU]
  rw [hdet, kpCocycle_pairing]
  have hcancel := kpPairing_scalar_cancellation D H v
    (xU v (g * h)) (xU v h) (detU v g) (detU v h) c
  calc
    _ = (kpPairing D H v (xU v (g * h) / (xU v h * detU v g))
          (xU v (g * h) / xU v g) * kpPairing D H v (detU v g) (detU v h)) *
          (kpPairing D H v (xU v (g * h)) c *
            kpPairing D H v (detU v g * detU v h) c) := by rfl
    _ = (kpPairing D H v (xU v (g * h) / (xU v h * detU v g))
          (xU v (g * h) / xU v g) * kpPairing D H v (detU v g) (detU v h)) *
          (kpPairing D H v (xU v (g * h) / (xU v h * detU v g)) c *
            kpPairing D H v (detU v g) c ^ 2 *
              kpPairing D H v (xU v h) c * kpPairing D H v (detU v h) c) := by
        rw [← hcancel]
    _ = _ := by ac_rfl

private def kpCocycleGood (k : GL (Fin 2) (v.adicCompletion F)) : Prop :=
  ∀ g h, kpCocycle D H v g h * kpCocycle D H v (g * h) k =
    kpCocycle D H v g (h * k) * kpCocycle D H v h k

private theorem kpCocycle_good_mul (k₁ k₂ : GL (Fin 2) (v.adicCompletion F))
    (h₁ : kpCocycleGood D H v k₁) (h₂ : kpCocycleGood D H v k₂) :
    kpCocycleGood D H v (k₁ * k₂) := by
  intro g h
  let σ := kpCocycle D H v
  have hcoc1 := h₁ g h
  have hcoc2 := h₂ (g * h) k₁
  have hcoc3 := h₂ g (h * k₁)
  have hcoc4 := h₂ h k₁
  have hcoc2' :
      σ (g * h) k₁ * σ (g * (h * k₁)) k₂ =
        σ (g * h) (k₁ * k₂) * σ k₁ k₂ := by
    simpa [mul_assoc] using hcoc2
  have hcoc3' :
      σ g (h * k₁) * σ (g * (h * k₁)) k₂ =
        σ g (h * (k₁ * k₂)) * σ (h * k₁) k₂ := by
    simpa [mul_assoc] using hcoc3
  have hmain :
      (σ g h * σ (g * h) (k₁ * k₂)) * σ k₁ k₂ =
        (σ g (h * (k₁ * k₂)) * σ h (k₁ * k₂)) * σ k₁ k₂ := by
    calc
      _ = σ g h * (σ (g * h) (k₁ * k₂) * σ k₁ k₂) := by ac_rfl
      _ = σ g h * (σ (g * h) k₁ * σ (g * (h * k₁)) k₂) := by rw [← hcoc2']
      _ = (σ g h * σ (g * h) k₁) * σ (g * (h * k₁)) k₂ := by ac_rfl
      _ = (σ g (h * k₁) * σ h k₁) * σ (g * (h * k₁)) k₂ := by rw [hcoc1]
      _ = σ h k₁ * (σ g (h * k₁) * σ (g * (h * k₁)) k₂) := by ac_rfl
      _ = σ h k₁ * (σ g (h * (k₁ * k₂)) * σ (h * k₁) k₂) := by rw [hcoc3']
      _ = σ g (h * (k₁ * k₂)) * (σ h k₁ * σ (h * k₁) k₂) := by ac_rfl
      _ = σ g (h * (k₁ * k₂)) * (σ h (k₁ * k₂) * σ k₁ k₂) := by rw [hcoc4]
      _ = _ := by ac_rfl
  calc
    σ g h * σ (g * h) (k₁ * k₂) =
        ((σ g h * σ (g * h) (k₁ * k₂)) * σ k₁ k₂) / σ k₁ k₂ := by
      simp [div_eq_mul_inv, mul_assoc]
    _ = ((σ g (h * (k₁ * k₂)) * σ h (k₁ * k₂)) * σ k₁ k₂) / σ k₁ k₂ := by rw [hmain]
    _ = σ g (h * (k₁ * k₂)) * σ h (k₁ * k₂) := by
      simp [div_eq_mul_inv, mul_assoc]

private theorem gl2_factorization (k : GL (Fin 2) (v.adicCompletion F)) :
    (∃ c : (v.adicCompletion F)ˣ, ∃ y : (v.adicCompletion F)ˣ, ∃ t : v.adicCompletion F,
      k = Matrix.GeneralLinearGroup.scalar (Fin 2) c *
        diagM (v.adicCompletion F) y * upperM (v.adicCompletion F) t) ∨
    (∃ c : (v.adicCompletion F)ˣ, ∃ t : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
      ∃ u : v.adicCompletion F,
      k = Matrix.GeneralLinearGroup.scalar (Fin 2) c * upperM (v.adicCompletion F) t *
        diagM (v.adicCompletion F) y * weylM (v.adicCompletion F) *
          upperM (v.adicCompletion F) u) := by
  classical
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) := k
  let a := M 0 0
  let b := M 0 1
  let c₀ := M 1 0
  let d := M 1 1
  by_cases hc : c₀ = 0
  · have hdet : M.det ≠ 0 := by simpa [M] using k.det_ne_zero
    have ha : a ≠ 0 := by
      intro ha
      apply hdet
      rw [Matrix.det_fin_two]
      simp [a, c₀, d, hc, ha, M]
    have hd : d ≠ 0 := by
      intro hd
      apply hdet
      rw [Matrix.det_fin_two]
      simp [a, c₀, d, hc, hd, M]
    let cU : (v.adicCompletion F)ˣ := Units.mk0 d hd
    let y : (v.adicCompletion F)ˣ := Units.mk0 (a / d) (div_ne_zero ha hd)
    let t : v.adicCompletion F := b / a
    have heq : k = Matrix.GeneralLinearGroup.scalar (Fin 2) cU *
        diagM (v.adicCompletion F) y * upperM (v.adicCompletion F) t := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [M, a, b, c₀, d, cU, y, t, hc,
          Matrix.GeneralLinearGroup.scalar, diagM, upperM, Matrix.mul_apply,
          Fin.sum_univ_two] <;>
        field_simp [ha, hd, M, a, b, c₀, d] <;> ring
    exact Or.inl ⟨cU, y, t, heq⟩
  · have hcne : c₀ ≠ 0 := hc
    have hdet : M.det ≠ 0 := by simpa [M] using k.det_ne_zero
    let cU : (v.adicCompletion F)ˣ := Units.mk0 c₀ hcne
    have hy : -M.det / c₀ ^ 2 ≠ 0 := by
      apply div_ne_zero
      · exact neg_ne_zero.mpr hdet
      · exact pow_ne_zero 2 hcne
    let y : (v.adicCompletion F)ˣ := Units.mk0 (-M.det / c₀ ^ 2) hy
    let t : v.adicCompletion F := a / c₀
    let u : v.adicCompletion F := d / c₀
    have heq : k = Matrix.GeneralLinearGroup.scalar (Fin 2) cU *
        upperM (v.adicCompletion F) t * diagM (v.adicCompletion F) y *
          weylM (v.adicCompletion F) * upperM (v.adicCompletion F) u := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [M, a, b, c₀, d, cU, y, t, u, hcne,
          Matrix.GeneralLinearGroup.scalar, upperM, diagM, weylM,
          Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;>
        field_simp [hcne, M, a, b, c₀, d] <;> ring
    exact Or.inr ⟨cU, t, y, u, heq⟩

/-- **cov:cocycle**: the KP formula is a 2-cocycle (Kubota 1967 / KP §0.1 replaced by the
generator argument of the blueprint). -/
theorem kpCocycle_cocycle (hSt : SteinbergAt H v) (g h k : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) k =
      kpCocycle D H v g (h * k) * kpCocycle D H v h k := by
  classical
  have hall : kpCocycleGood D H v k := by
    rcases gl2_factorization v k with ⟨c, y, t, hk⟩ | ⟨c, t, y, u, hk⟩
    · have hs : kpCocycleGood D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
        intro g h
        exact kpCocycle_good_scalar D H v g h c
      have hd : kpCocycleGood D H v (diagM (v.adicCompletion F) y) := by
        intro g h
        exact kpCocycle_good_diagM D H v g h y
      have hu : kpCocycleGood D H v (upperM (v.adicCompletion F) t) := by
        intro g h
        exact kpCocycle_good_upperM D H v g h t
      have hsd := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (diagM (v.adicCompletion F) y) hs hd
      have hfinal := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * diagM (v.adicCompletion F) y)
        (upperM (v.adicCompletion F) t) hsd hu
      rw [hk]
      exact hfinal
    · have hs : kpCocycleGood D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
        intro g h
        exact kpCocycle_good_scalar D H v g h c
      have hu : kpCocycleGood D H v (upperM (v.adicCompletion F) t) := by
        intro g h
        exact kpCocycle_good_upperM D H v g h t
      have hd : kpCocycleGood D H v (diagM (v.adicCompletion F) y) := by
        intro g h
        exact kpCocycle_good_diagM D H v g h y
      have hw : kpCocycleGood D H v (weylM (v.adicCompletion F)) := by
        intro g h
        exact kpCocycle_good_weyl D H v hSt g h
      have hu' : kpCocycleGood D H v (upperM (v.adicCompletion F) u) := by
        intro g h
        exact kpCocycle_good_upperM D H v g h u
      have h1 := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (upperM (v.adicCompletion F) t) hs hu
      have h2 := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * upperM (v.adicCompletion F) t)
        (diagM (v.adicCompletion F) y) h1 hd
      have h3 := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * upperM (v.adicCompletion F) t *
          diagM (v.adicCompletion F) y) (weylM (v.adicCompletion F)) h2 hw
      have h4 := kpCocycle_good_mul D H v
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c * upperM (v.adicCompletion F) t *
          diagM (v.adicCompletion F) y * weylM (v.adicCompletion F))
        (upperM (v.adicCompletion F) u) h3 hu'
      rw [hk]
      exact h4
  exact hall g h

/-- **cov:center**: for `c = 2` the scalar section is central and multiplicative. -/
theorem kpCocycle_scalar (hSt : SteinbergAt H v) (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) g =
      kpCocycle D H v g (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  simp only [xU_scalar_left, xU_scalar_right, xU_scalar, detU_scalar]
  have h₁ : (c * xU v g) / (xU v g * c ^ 2) = c⁻¹ := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    field_simp <;> ring
  have h₂ : (c * xU v g) / c = xU v g := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp <;> ring
  have h₃ : (c * xU v g) / (c * detU v g) = xU v g / detU v g := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp <;> ring
  have h₄ : (c * xU v g) / xU v g = c := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp <;> ring
  rw [h₁, h₂, h₃, h₄]
  rw [kpPairing_inv_left, kpPairing_inverse_swap, kpPairing_pow_left,
    kpPairing_square_swap, kpPairing_div_left, kpPairing_pow_right]
  group

theorem kpCocycle_scalar_scalar (hSt : SteinbergAt H v) (c c' : (v.adicCompletion F)ˣ) :
    kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c') = 1 := by
  rw [kpCocycle_pairing]
  simp only [xU_scalar_left, xU_scalar, detU_scalar]
  have h₁ : (c * c') / (c' * c ^ 2) = c⁻¹ := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    field_simp <;> ring
  have h₂ : (c * c') / c = c' := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp <;> ring
  rw [h₁, h₂, kpPairing_inv_left, kpPairing_pow_left, kpPairing_pow_right]
  let z := kpPairing D H v c c'
  change z⁻¹ * (z ^ 2) ^ 2 = 1
  calc
    z⁻¹ * (z ^ 2) ^ 2 = z⁻¹ * z ^ 4 := by
      congr 1
      rw [← pow_mul]
    _ = z⁻¹ * z := by rw [show z ^ 4 = z by
      simpa [z] using kpPairing_four D H v c c']
    _ = 1 := inv_mul_cancel z

/-- **cov:tame-splitting** (formula): on `GL₂(O_v)` at `v ∤ 6`,
`s(k) = ι((k₂₁, k₂₂/det k)₃) = muThree(hilb(k₂₂/det k, k₂₁))` if `0 < ‖k₂₁‖ < 1`, else `1`,
satisfies `s(k₁k₂) = s(k₁)s(k₂)σ(k₁,k₂)`, so `k ↦ (k, s(k))` is a splitting. -/
def tameSplit (k : GL (Fin 2) (v.adicCompletion F)) : rootsOfUnity 3 ℂ :=
  if h : ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 ∧
      Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) < 1) ∧ (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0 then
    muThree D (H.hilb v (Units.mk0 ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) h.2 / detU v k)
      (Units.mk0 ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) h.1.1))
  else 1

theorem tameSplit_mul (hv : (6 : 𝓞 F) ∉ v.asIdeal) (k₁ k₂ : GL (Fin 2) (v.adicCompletion F))
    (hk₁ : ∀ i j, (k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk₂ : ∀ i j, (k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hd₁ : Valued.v ((k₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) = 1)
    (hd₂ : Valued.v ((k₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det) = 1) :
    tameSplit D H v (k₁ * k₂) = tameSplit D H v k₁ * tameSplit D H v k₂ * kpCocycle D H v k₁ k₂ := by
  sorry

end CocycleThm

/-! ## Local and global outcome -/

/-- The normalized KP extension modulo its central scalar section, before choosing topology
or the distinguished root and torus maps. -/
theorem kpCocycle_centralQuotient (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    Nonempty (TH_COVER.CocycleQuotient
      (Subgroup.center (GL (Fin 2) (v.adicCompletion F))) (kpCocycle D H v)) := by
  have hx1 : xU v (1 : GL (Fin 2) (v.adicCompletion F)) = 1 := by
    apply Units.ext
    simp [xU, xEntry]
  have hd1 : detU v (1 : GL (Fin 2) (v.adicCompletion F)) = 1 := by
    simp [detU]
  refine TH_COVER.exists_cocycleQuotient _ _ ?_ ?_ ?_ ?_
  · exact {
      one_left := fun g => by
        simp [kpCocycle, hx1, hd1, hilb_one_left, muThree_one]
      one_right := fun g => by
        simp [kpCocycle, hx1, hd1, hilb_one_right, muThree_one]
      assoc := kpCocycle_cocycle D H v hSt
    }
  · intro g hg h hh
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg hh
    obtain ⟨c, rfl⟩ := hg
    obtain ⟨c', rfl⟩ := hh
    exact kpCocycle_scalar_scalar D H v hSt c c'
  · intro g hg h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨c, rfl⟩ := hg
    exact Matrix.GeneralLinearGroup.scalar_commute c h
  · intro g hg h
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨c, rfl⟩ := hg
    exact kpCocycle_scalar D H v hSt c h

/-- The algebraic fields of the finite local cover, before constructing its topology. -/
structure FinLocalAlgebra (D : FieldData F) (H : HilbertData F) (v : FinPlace F) where
  L : Type
  [grp : Group L]
  z : rootsOfUnity 3 ℂ →* L
  z_inj : Function.Injective z
  z_central : ∀ ζ g, z ζ * g = g * z ζ
  pr : L →* PGL2 (v.adicCompletion F)
  pr_surj : Function.Surjective pr
  pr_ker : pr.ker = z.range
  n : Multiplicative (v.adicCompletion F) →* L
  nbar : Multiplicative (v.adicCompletion F) →* L
  a : (v.adicCompletion F)ˣ → L
  w : L
  /-- the set-theoretic section `g ↦ (g, 1)` of the KP construction -/
  sec : GL (Fin 2) (v.adicCompletion F) → L
  sec_mul : ∀ g h, sec g * sec h = z (kpCocycle D H v g h) * sec (g * h)
  sec_pr : ∀ g, pr (sec g) = QuotientGroup.mk g
  sec_scalar : ∀ c, sec (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1
  sec_n : ∀ x, n (Multiplicative.ofAdd x) = sec (upperM _ x)
  sec_nbar : ∀ x, nbar (Multiplicative.ofAdd x) = sec (lowerM _ x)
  sec_a : ∀ y, a y = sec (diagM _ y)
  sec_w : w = sec (weylM _)
  pr_n : ∀ x, pr (n (Multiplicative.ofAdd x)) = QuotientGroup.mk (upperM _ x)
  pr_nbar : ∀ x, pr (nbar (Multiplicative.ofAdd x)) = QuotientGroup.mk (lowerM _ x)
  pr_a : ∀ y, pr (a y) = QuotientGroup.mk (diagM _ y)
  pr_w : pr w = QuotientGroup.mk (weylM (v.adicCompletion F))
  a_one : a 1 = 1
  /-- torus law `a(x)a(y) = C(x,y)a(xy)`, `C = muThree ∘ hilb` (10:96–97 with `ι = σ0⁻¹`). -/
  a_mul : ∀ x y, a x * a y = z (muThree D (H.hilb v x y)) * a (x * y)
  /-- exact lift identities (eq:theta-lift-identities, 10:206–248). -/
  lift_na : ∀ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ),
    n (Multiplicative.ofAdd x) * a y = a y * n (Multiplicative.ofAdd (x * ↑y⁻¹))
  lift_wa : ∀ y, w * a y * w⁻¹ = a y⁻¹
  lift_wn : ∀ Hh : (v.adicCompletion F)ˣ,
    w * n (Multiplicative.ofAdd (Hh : v.adicCompletion F)) =
      n (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *
        a (-(Hh⁻¹ * Hh⁻¹)) *
          nbar (Multiplicative.ofAdd ((Hh⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))
  w_sq : w * w = 1
  w_n_w : ∀ x, w * n (Multiplicative.ofAdd x) * w = nbar (Multiplicative.ofAdd x)

attribute [instance] FinLocalAlgebra.grp

/-- Add the distinguished root, torus, and Weyl lifts to the KP scalar quotient. -/
theorem exists_finLocalAlgebra (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) : Nonempty (FinLocalAlgebra D H v) := by
  classical
  obtain ⟨Q⟩ := kpCocycle_centralQuotient D H v hSt
  let K := v.adicCompletion F
  have upper_zero : upperM K 0 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperM]
  have upper_add : ∀ x y : K, upperM K (x + y) = upperM K x * upperM K y := by
    intro x y
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have diag_one : diagM K 1 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagM]
  have diag_mul : ∀ x y : Kˣ, diagM K (x * y) = diagM K x * diagM K y := by
    intro x y
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [diagM, Matrix.mul_apply, Fin.sum_univ_two]
  have weyl_sq : weylM K * weylM K = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
  have weyl_upper : ∀ x : K, weylM K * upperM K x * weylM K = lowerM K x := by
    intro x
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two]
  have weyl_diag : ∀ y : Kˣ, weylM K * diagM K y * weylM K =
      Matrix.GeneralLinearGroup.scalar (Fin 2) y * diagM K y⁻¹ := by
    intro y
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, diagM, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply,
        Fin.sum_univ_two]
  have upper_diag : ∀ (x : K) (y : Kˣ), upperM K x * diagM K y =
      diagM K y * upperM K (x * (y⁻¹ : Kˣ)) := by
    intro x y
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals
      rw [mul_left_comm]
      have hy : (y : K) * (y : K)⁻¹ = 1 := mul_inv_cancel₀ (a := (y : K)) y.ne_zero
      rw [hy, mul_one]
  have wn_factor : ∀ t : Kˣ, weylM K * upperM K (t : K) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) t *
        (upperM K ((t⁻¹ : Kˣ) : K) * diagM K (-(t⁻¹ * t⁻¹)) *
          lowerM K ((t⁻¹ : Kˣ) : K)) := by
    intro t
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, upperM, diagM, lowerM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] <;> try field_simp <;> ring
  have sec_one : Q.sec (1 : GL (Fin 2) K) = 1 := Q.sec_triv _ (Subgroup.one_mem _)
  have scalar_sec : ∀ c : Kˣ, Q.sec (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
    intro c
    apply Q.sec_triv
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have scalar_cancel : ∀ (c : Kˣ) (g : GL (Fin 2) K),
      kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) g = 1 →
      Q.sec (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = Q.sec g := by
    intro c g hc
    have h := Q.sec_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) c) g
    rw [scalar_sec, one_mul, hc, map_one, one_mul] at h
    exact h.symm
  have pair_inv_right : ∀ a b : Kˣ,
      kpPairing D H v a b⁻¹ = (kpPairing D H v a b)⁻¹ := by
    intro a b
    exact map_inv (kpPairing D H v a) b
  have upper_diag_sigma : ∀ (x : K) (y : Kˣ),
      kpCocycle D H v (upperM K x) (diagM K y) = 1 := by
    intro x y
    rw [kpCocycle_diagM_formula, detU_upperM]
    simp [upperM, kpPairing_one_left]
  have diag_sigma : ∀ x y : Kˣ,
      kpCocycle D H v (diagM K x) (diagM K y) = muThree D (H.hilb v x y) := by
    intro x y
    rw [kpCocycle_diagM_formula, detU_diagM]
    simp [diagM, kpPairing]
  have lower_det : ∀ x : K, detU v (lowerM K x) = 1 := by
    intro x
    apply Units.ext
    simp [detU, lowerM, Matrix.det_fin_two]
  -- The big-cell lift is checked before the remaining root-map assembly.
  have wn_sec : ∀ t : Kˣ, Q.sec (weylM K) * Q.sec (upperM K (t : K)) =
      Q.sec (upperM K ((t⁻¹ : Kˣ) : K)) * Q.sec (diagM K (-(t⁻¹ * t⁻¹))) *
        Q.sec (lowerM K ((t⁻¹ : Kˣ) : K)) := by
    intro t
    let u : Kˣ := t⁻¹
    let Y := upperM K (u : K) * diagM K (-(u * u)) * lowerM K (u : K)
    have hY : weylM K * upperM K (t : K) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) t * Y := wn_factor t
    have hxY : xU v Y = u := by
      have h := congrArg (xU v) hY
      rw [xU_mul_upperM, xU_weylM, xU_scalar_left] at h
      calc
        xU v Y = t⁻¹ * (t * xU v Y) := by simp [mul_assoc]
        _ = t⁻¹ := by rw [← h]; simp
    have hdY : detU v Y = -(u * u) := by
      dsimp [Y]
      rw [detU_mul, detU_mul, detU_upperM, detU_diagM, lower_det]
      simp
    have hxL : xU v (lowerM K (u : K)) = u := by
      apply Units.ext
      simp [xU, xEntry, lowerM, u.ne_zero]
    have hxUA : xU v (upperM K (u : K) * diagM K (-(u * u))) = 1 := by
      rw [xU_mul_diagM, xU_upperM]
      simp [upperM]
    have hdUA : detU v (upperM K (u : K) * diagM K (-(u * u))) = -(u * u) := by
      rw [detU_mul, detU_upperM, detU_diagM, one_mul]
    have hdiv : u / (u * -(u * u)) = -(t * t) := by
      simp [u, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    have hlast : kpCocycle D H v
        (upperM K (u : K) * diagM K (-(u * u))) (lowerM K (u : K)) = 1 := by
      rw [kpCocycle_pairing]
      change kpPairing D H v (xU v Y / (xU v (lowerM K (u : K)) *
          detU v (upperM K (u : K) * diagM K (-(u * u)))))
          (xU v Y / xU v (upperM K (u : K) * diagM K (-(u * u)))) *
        kpPairing D H v (detU v (upperM K (u : K) * diagM K (-(u * u))))
          (detU v (lowerM K (u : K))) = 1
      rw [hxY, hxL, hxUA, hdUA, lower_det, hdiv]
      rw [kpPairing_one_right, mul_one, div_one, kpPairing_neg_mul_left, kpPairing_mul_left]
      change kpPairing D H v t t⁻¹ * kpPairing D H v t t⁻¹ = 1
      have hp : kpPairing D H v t t⁻¹ = 1 := by
        rw [pair_inv_right, kpPairing_self, inv_one]
      simp only [hp, one_mul]
    have hscalar : kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) t) Y = 1 := by
      rw [kpCocycle_scalar D H v hSt, kpCocycle_scalar_right_formula, hxY, hdY]
      rw [kpPairing_neg_mul_left, kpPairing_mul_left]
      change kpPairing D H v t⁻¹ t *
        (kpPairing D H v t⁻¹ t * kpPairing D H v t⁻¹ t) = 1
      have hp : kpPairing D H v t⁻¹ t = 1 := by
        rw [kpPairing_inv_left, kpPairing_self, inv_one]
      simp only [hp, one_mul]
    have hUA : Q.sec (upperM K (u : K)) * Q.sec (diagM K (-(u * u))) =
        Q.sec (upperM K (u : K) * diagM K (-(u * u))) := by
      rw [Q.sec_mul, upper_diag_sigma, map_one, one_mul]
    have hUAL : Q.sec (upperM K (u : K) * diagM K (-(u * u))) *
        Q.sec (lowerM K (u : K)) = Q.sec Y := by
      rw [Q.sec_mul, hlast, map_one, one_mul]
    calc
      _ = Q.sec (weylM K * upperM K (t : K)) := by
        rw [Q.sec_mul, kpCocycle_upperM, map_one, one_mul]
      _ = Q.sec (Matrix.GeneralLinearGroup.scalar (Fin 2) t * Y) := congrArg Q.sec hY
      _ = Q.sec Y := scalar_cancel t Y hscalar
      _ = _ := by rw [← hUAL, ← hUA]
  have hx1 : xU v (1 : GL (Fin 2) K) = 1 := by
    apply Units.ext
    simp [xU, xEntry]
  have w_sigma : kpCocycle D H v (weylM K) (weylM K) = 1 := by
    rw [kpCocycle_pairing, weyl_sq, hx1, xU_weylM, detU_weylM]
    simp [kpPairing_one_right, kpPairing_neg_one_left]
  have ww : Q.sec (weylM K) * Q.sec (weylM K) = 1 := by
    rw [Q.sec_mul, w_sigma, map_one, one_mul, weyl_sq, sec_one]
  have winv : (Q.sec (weylM K))⁻¹ = Q.sec (weylM K) := by
    exact inv_eq_of_mul_eq_one_right ww
  have wupper_sigma : ∀ x : K,
      kpCocycle D H v (weylM K * upperM K x) (weylM K) = 1 := by
    intro x
    rw [kpCocycle_pairing, weyl_upper, xU_mul_upperM, xU_weylM,
      detU_mul, detU_weylM, detU_upperM]
    simp [kpPairing_neg_mul_left, kpPairing_self, kpPairing_neg_one_left]
  have wupper_sec : ∀ x : K,
      Q.sec (weylM K) * Q.sec (upperM K x) * Q.sec (weylM K) = Q.sec (lowerM K x) := by
    intro x
    rw [Q.sec_mul, kpCocycle_upperM, map_one, one_mul, Q.sec_mul,
      wupper_sigma, map_one, one_mul, weyl_upper]
  have wdiag_sigma : ∀ y : Kˣ, kpCocycle D H v (weylM K) (diagM K y) = 1 := by
    intro y
    rw [kpCocycle_diagM_formula, xU_weylM]
    simp [weylM, kpPairing_one_left]
  have wdiag_w_sigma : ∀ y : Kˣ,
      kpCocycle D H v (weylM K * diagM K y) (weylM K) = 1 := by
    intro y
    rw [kpCocycle_pairing, weyl_diag, xU_scalar_left, xU_diagM,
      xU_weylM, detU_mul, detU_weylM, detU_diagM, xU_mul_diagM]
    rw [xU_weylM]
    simp [weylM, kpPairing_one_right, kpPairing_neg_one_right]
  have scalar_diag_sigma : ∀ y : Kˣ,
      kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) y) (diagM K y⁻¹) = 1 := by
    intro y
    rw [kpCocycle_scalar D H v hSt, kpCocycle_scalar_right_formula,
      xU_diagM, detU_diagM]
    simp [kpPairing_one_left, kpPairing_inv_left, kpPairing_self]
  have wdiag_sec : ∀ y : Kˣ,
      Q.sec (weylM K) * Q.sec (diagM K y) * (Q.sec (weylM K))⁻¹ = Q.sec (diagM K y⁻¹) := by
    intro y
    rw [winv, Q.sec_mul, wdiag_sigma, map_one, one_mul, Q.sec_mul,
      wdiag_w_sigma, map_one, one_mul, weyl_diag]
    exact scalar_cancel y (diagM K y⁻¹) (scalar_diag_sigma y)
  let n : Multiplicative K →* Q.E := {
    toFun := fun x => Q.sec (upperM K (Multiplicative.toAdd x))
    map_one' := by
      change Q.sec (upperM K 0) = 1
      rw [upper_zero, sec_one]
    map_mul' := by
      intro x y
      change Q.sec (upperM K (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
      rw [upper_add, Q.sec_mul, kpCocycle_upperM, map_one, one_mul]
  }
  let nbar : Multiplicative K →* Q.E := (MulAut.conj (Q.sec (weylM K))).toMonoidHom.comp n
  have nbar_sec : ∀ x : K, nbar (Multiplicative.ofAdd x) = Q.sec (lowerM K x) := by
    intro x
    change Q.sec (weylM K) * Q.sec (upperM K x) * (Q.sec (weylM K))⁻¹ = _
    rw [winv]
    exact wupper_sec x
  refine ⟨{
    L := Q.E
    grp := Q.grp
    z := Q.z
    z_inj := Q.z_inj
    z_central := Q.z_central
    pr := Q.pr
    pr_surj := Q.pr_surj
    pr_ker := Q.pr_ker
    n := n
    nbar := nbar
    a := fun y => Q.sec (diagM K y)
    w := Q.sec (weylM K)
    sec := Q.sec
    sec_mul := Q.sec_mul
    sec_pr := Q.sec_pr
    sec_scalar := scalar_sec
    sec_n := fun _ => rfl
    sec_nbar := nbar_sec
    sec_a := fun _ => rfl
    sec_w := rfl
    pr_n := fun _ => Q.sec_pr _
    pr_nbar := ?_
    pr_a := fun _ => Q.sec_pr _
    pr_w := Q.sec_pr _
    a_one := by rw [diag_one, sec_one]
    a_mul := ?_
    lift_na := ?_
    lift_wa := wdiag_sec
    lift_wn := ?_
    w_sq := ww
    w_n_w := ?_
  }⟩
  · intro x
    rw [nbar_sec]
    exact Q.sec_pr _
  · intro x y
    rw [Q.sec_mul, diag_sigma, ← diag_mul]
  · intro x y
    change Q.sec (upperM K x) * Q.sec (diagM K y) =
      Q.sec (diagM K y) * Q.sec (upperM K (x * (y⁻¹ : Kˣ)))
    rw [Q.sec_mul, upper_diag_sigma, map_one, one_mul, Q.sec_mul,
      kpCocycle_upperM, map_one, one_mul, upper_diag]
  · intro t
    change Q.sec (weylM K) * Q.sec (upperM K (t : K)) =
      Q.sec (upperM K ((t⁻¹ : Kˣ) : K)) * Q.sec (diagM K (-(t⁻¹ * t⁻¹))) *
        nbar (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K))
    rw [nbar_sec]
    exact wn_sec t
  · intro x
    change Q.sec (weylM K) * Q.sec (upperM K x) * Q.sec (weylM K) =
      nbar (Multiplicative.ofAdd x)
    rw [nbar_sec]
    exact wupper_sec x

private theorem exists_smallCocycle_trivial
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    ∃ m0 : ℕ, 1 ≤ m0 ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g h : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ∈ ball v m) →
        (∀ i j, ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ∈ ball v m) →
        kpCocycle D H v g h = 1 := by
  classical
  obtain ⟨m0, hm0, hpowers⟩ :=
    ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_sixthPowerNeighborhood v
  refine ⟨m0, hm0, ?_⟩
  intro m hm g h hg hh
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hrr : r ≤ WithZero.exp (-(m0 : ℤ)) := by
    apply WithZero.exp_le_exp.mpr
    omega
  have small_pairing (u : Kˣ) (hu : V ((u : K) - 1) ≤ r) (b : Kˣ) :
      kpPairing D H v u b = 1 := by
    change muThree D (H.hilb v u b) = 1
    rw [H.sixth_power v u b (hpowers u (hu.trans hrr)), muThree_one D]
  have right_pairing (u : Kˣ) (hu : ∀ b, kpPairing D H v u b = 1) (b : Kˣ) :
      kpPairing D H v b u = 1 := by
    have hs := kpPairing_skew D H v b u
    rw [hu b, mul_one] at hs
    exact hs
  have entries (k : GL (Fin 2) K)
      (hk : ∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) i j -
        (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m) :
      V ((k : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ≤ r ∧
      V ((k : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ r ∧
      V ((k : Matrix (Fin 2) (Fin 2) K) 0 1) ≤ r ∧
      V ((k : Matrix (Fin 2) (Fin 2) K) 1 0) ≤ r := by
    change ∀ i j, V ((k : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r at hk
    exact ⟨by simpa using hk 0 0, by simpa using hk 1 1,
      by simpa using hk 0 1, by simpa using hk 1 0⟩
  have near_one_bound (x : K) (hx : V (x - 1) ≤ r) : V x ≤ 1 := by
    have hb := V.map_add_le (hx.trans hr.le) (show V (1 : K) ≤ 1 by simp)
    simpa only [sub_add_cancel] using hb
  have near_one_ne (x : K) (hx : V (x - 1) ≤ r) : x ≠ 0 := by
    intro hx0
    have hb : (1 : WithZero (Multiplicative ℤ)) ≤ r := by
      simpa [hx0] using hx
    exact (not_le_of_gt hr) hb
  have small_mul {x y : K} (hx : V x ≤ r) (hy : V y ≤ 1) : V (x * y) ≤ r := by
    rw [map_mul]
    simpa only [mul_one] using mul_le_mul' hx hy
  have det_small (k : GL (Fin 2) K)
      (hk : ∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) i j -
        (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m) :
      V ((detU v k : K) - 1) ≤ r := by
    obtain ⟨ha, hd, hb, hc⟩ := entries k hk
    have heq : (detU v k : K) - 1 =
        ((k : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) *
          (k : Matrix (Fin 2) (Fin 2) K) 1 1 +
        ((k : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) -
          (k : Matrix (Fin 2) (Fin 2) K) 0 1 *
            (k : Matrix (Fin 2) (Fin 2) K) 1 0 := by
      change (k : Matrix (Fin 2) (Fin 2) K).det - 1 = _
      rw [Matrix.det_fin_two]
      ring
    rw [heq]
    exact V.map_sub_le
      (V.map_add_le (small_mul ha (near_one_bound _ hd)) hd)
      (small_mul hb (hc.trans hr.le))
  obtain ⟨hga, hgd, hgb, hgc⟩ := entries g hg
  obtain ⟨hha, hhd, hhb, hhc⟩ := entries h hh
  have product_d_small :
      V (((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ r := by
    have heq : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1 =
        (g : Matrix (Fin 2) (Fin 2) K) 1 0 * (h : Matrix (Fin 2) (Fin 2) K) 0 1 +
        ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) *
          (h : Matrix (Fin 2) (Fin 2) K) 1 1 +
        ((h : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) := by
      rw [matrix_mul_22]
      ring
    rw [heq]
    exact V.map_add_le (V.map_add_le (small_mul hgc (hhb.trans hr.le))
      (small_mul hgd (near_one_bound _ hhd))) hhd
  let Gd : Kˣ := Units.mk0 _ (near_one_ne _ hgd)
  let Ha : Kˣ := Units.mk0 _ (near_one_ne _ hha)
  have hGd : ∀ b, kpPairing D H v Gd b = 1 := small_pairing Gd hgd
  have hHa : ∀ b, kpPairing D H v Ha b = 1 := small_pairing Ha hha
  have hdg : ∀ b, kpPairing D H v (detU v g) b = 1 :=
    small_pairing (detU v g) (det_small g hg)
  have hdh : ∀ b, kpPairing D H v (detU v h) b = 1 :=
    small_pairing (detU v h) (det_small h hh)
  have hσ : kpCocycle D H v g h =
      kpPairing D H v (xU v (g * h) / xU v h) (xU v (g * h) / xU v g) := by
    rw [kpCocycle_pairing, hdg, mul_one]
    have heq : xU v (g * h) / (xU v h * detU v g) =
        (xU v (g * h) / xU v h) / detU v g := div_mul_eq_div_div _ _ _
    rw [heq, kpPairing_div_left, hdg, inv_one, mul_one]
  rw [hσ]
  by_cases hcg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hxgh : xU v (g * h) = Gd * xU v h := by
      apply Units.ext
      change xEntry v (g * h) = (g : Matrix (Fin 2) (Fin 2) K) 1 1 * xEntry v h
      by_cases hch : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
      · have hcgh : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
          simp [matrix_mul_21, hcg, hch]
        rw [xEntry, if_neg (by simpa using hcgh), matrix_mul_22]
        simp [xEntry, hcg, hch]
      · have hcgh : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
          rw [matrix_mul_21, hcg, zero_mul, zero_add]
          exact mul_ne_zero (near_one_ne _ hgd) hch
        rw [xEntry, if_pos hcgh, matrix_mul_21]
        simp [xEntry, hch, hcg]
    have hfirst : xU v (g * h) / xU v h = Gd := by rw [hxgh]; simp
    rw [hfirst]
    exact hGd _
  by_cases hch : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hcgh : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      rw [matrix_mul_21, hch, mul_zero, add_zero]
      exact mul_ne_zero hcg (near_one_ne _ hha)
    have hxgh : xU v (g * h) = xU v g * Ha := by
      apply Units.ext
      change xEntry v (g * h) = xEntry v g * (h : Matrix (Fin 2) (Fin 2) K) 0 0
      rw [xEntry, if_pos hcgh, matrix_mul_21]
      simp [xEntry, hcg, hch]
    have hsecond : xU v (g * h) / xU v g = Ha := by rw [hxgh, mul_div_cancel_left]
    rw [hsecond]
    exact right_pairing Ha hHa _
  by_cases hcgh : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hX : ∀ b, kpPairing D H v (xU v (g * h)) b = 1 := by
      apply small_pairing
      simpa [xU, xEntry, hcgh] using product_d_small
    have hrel := xU_diag_relation_10 v g h hch hcgh
    have hrel' : -xU v g * detU v h = xU v (g * h) * xU v h := by
      simpa only [neg_mul] using hrel.symm
    have hZ : xU v g = -(xU v (g * h) * xU v h / detU v h) := by
      apply neg_injective
      simpa only [neg_neg] using (eq_div_iff_mul_eq').2 hrel'
    have hYZ : kpPairing D H v (xU v h) (xU v g) = 1 := by
      rw [hZ, kpPairing_neg_mul_right, kpPairing_div_right, kpPairing_mul_right,
        right_pairing _ hX, kpPairing_self, right_pairing _ hdh]
      simp
    simp only [kpPairing_div_left, kpPairing_div_right, hX,
      right_pairing _ hX, hYZ, mul_one, inv_one]
  · let X : Kˣ := xU v g * Ha / xU v (g * h)
    let Y : Kˣ := Gd * xU v h / xU v (g * h)
    have hrow : (xU v g : K) * (Ha : K) + (Gd : K) * (xU v h : K) =
        (xU v (g * h) : K) := by
      change xEntry v g * (h : Matrix (Fin 2) (Fin 2) K) 0 0 +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 * xEntry v h = xEntry v (g * h)
      rw [xEntry, if_pos hcg, xEntry, if_pos hch, xEntry, if_pos hcgh]
      exact (matrix_mul_21 v g h).symm
    have hsum : (X : K) + (Y : K) = 1 := by
      change (xU v g : K) * (Ha : K) / (xU v (g * h) : K) +
        (Gd : K) * (xU v h : K) / (xU v (g * h) : K) = 1
      rw [← add_div, hrow, div_self (xU v (g * h)).ne_zero]
    have hXY : (1 : K) - (X : K) = (Y : K) := by
      linear_combination -hsum
    have hXne : (1 : K) - (X : K) ≠ 0 := by rw [hXY]; exact Y.ne_zero
    have hYunit : Y = Units.mk0 _ hXne := by apply Units.ext; exact hXY.symm
    have hStein := kpPairing_st D H v hSt X hXne
    rw [← hYunit] at hStein
    have hXform : X = Ha * (xU v g / xU v (g * h)) := by
      dsimp only [X]
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [hXform, kpPairing_mul_left, hHa, one_mul] at hStein
    dsimp only [Y] at hStein
    have hYform : Gd * xU v h / xU v (g * h) =
        Gd * (xU v h / xU v (g * h)) := mul_div_assoc _ _ _
    rw [hYform, kpPairing_mul_right, right_pairing _ hGd, one_mul] at hStein
    have hZX : xU v g / xU v (g * h) = (xU v (g * h) / xU v g)⁻¹ := by simp
    have hYX : xU v h / xU v (g * h) = (xU v (g * h) / xU v h)⁻¹ := by simp
    have hinv (a b : Kˣ) : kpPairing D H v a⁻¹ b⁻¹ = kpPairing D H v a b := by
      rw [kpPairing_inv_left, map_inv, inv_inv]
    rw [hZX, hYX, hinv] at hStein
    have hs := kpPairing_skew D H v (xU v (g * h) / xU v h) (xU v (g * h) / xU v g)
    simpa only [hStein, mul_one] using hs

private theorem exists_smallSectionHom
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (C : FinLocalAlgebra D H v) :
    ∃ m0 : ℕ, 1 ≤ m0 ∧ ∀ m : ℕ, m0 ≤ m →
      ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion F)),
        (∀ g, g ∈ U ↔ ∀ i j,
          ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ∈ ball v m) ∧
        ∃ s : U →* C.L,
          (∀ g : U, s g = C.sec g) ∧ Set.InjOn C.pr (s.range : Set C.L) := by
  classical
  let K := v.adicCompletion F
  obtain ⟨ms, hms, hsigma⟩ := exists_smallCocycle_trivial D H v hSt
  obtain ⟨mp, _, hpowers⟩ :=
    ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_sixthPowerNeighborhood v
  let m0 := max ms mp
  refine ⟨m0, hms.trans (le_max_left _ _), ?_⟩
  intro m hm
  have hmσ : ms ≤ m := (le_max_left ms mp).trans hm
  have hmp : mp ≤ m := (le_max_right ms mp).trans hm
  have hm1 : 1 ≤ m := hms.trans hmσ
  obtain ⟨U, hUval⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_congruenceSubgroup v m hm1
  have hU : ∀ g, g ∈ U ↔ ∀ i j,
      (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j -
        (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m := fun g => hUval g
  refine ⟨U, hU, ?_⟩
  let s : U →* C.L := {
    toFun := fun g => C.sec (g : GL (Fin 2) K)
    map_one' := by simpa using C.sec_scalar (1 : Kˣ)
    map_mul' := by
      intro g h
      change C.sec ((g : GL (Fin 2) K) * (h : GL (Fin 2) K)) =
        C.sec (g : GL (Fin 2) K) * C.sec (h : GL (Fin 2) K)
      have hσ := hsigma m hmσ (g : GL (Fin 2) K) (h : GL (Fin 2) K)
        ((hU _).mp g.property) ((hU _).mp h.property)
      have heq := C.sec_mul (g : GL (Fin 2) K) (h : GL (Fin 2) K)
      rw [hσ, map_one, one_mul] at heq
      exact heq.symm
  }
  refine ⟨s, fun _ => rfl, ?_⟩
  rintro x ⟨g, rfl⟩ y ⟨h, rfl⟩ hpr
  change C.sec (g : GL (Fin 2) K) = C.sec (h : GL (Fin 2) K)
  change C.pr (C.sec (g : GL (Fin 2) K)) = C.pr (C.sec (h : GL (Fin 2) K)) at hpr
  rw [C.sec_pr, C.sec_pr] at hpr
  have hcent : (g : GL (Fin 2) K) / (h : GL (Fin 2) K) ∈
      Subgroup.center (GL (Fin 2) K) := QuotientGroup.eq_iff_div_mem.mp hpr
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcent
  obtain ⟨c, hc⟩ := hcent
  have hmat : (g : GL (Fin 2) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c * (h : GL (Fin 2) K) := by
    rw [hc]
    simp
  have hentry : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (c : K) * ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    have heq := congrArg (fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) 1 1) hmat
    simpa [Matrix.mul_apply] using heq
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hrr : r ≤ WithZero.exp (-(mp : ℤ)) := by
    apply WithZero.exp_le_exp.mpr
    omega
  have hg := ((hU _).mp g.property) 1 1
  have hh := ((hU _).mp h.property) 1 1
  change V (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ r at hg
  change V (((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ r at hh
  have hHval : V (((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 := by
    simpa using V.map_eq_of_sub_lt (x := 1)
      (y := ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) (by simpa using hh.trans_lt hr)
  have hdiff : V (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 -
      ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1) ≤ r := by
    have heq : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
        (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) -
          (((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) := by ring
    rw [heq]
    exact V.map_sub_le hg hh
  have hmult : ((c : K) - 1) * ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 - ((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [hentry]
    ring
  have hval := congrArg V hmult
  rw [map_mul, hHval, mul_one] at hval
  have hcsmall : V ((c : K) - 1) ≤ r := hval.le.trans hdiff
  have hcpow : ∃ u : Kˣ, c = u ^ 6 := hpowers c (hcsmall.trans hrr)
  have hcleft (b : Kˣ) : kpPairing D H v c b = 1 := by
    change muThree D (H.hilb v c b) = 1
    rw [H.sixth_power v c b hcpow, muThree_one D]
  have hcright (b : Kˣ) : kpPairing D H v b c = 1 := by
    have heq := kpPairing_skew D H v b c
    rw [hcleft b, mul_one] at heq
    exact heq
  have hscalar : kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (h : GL (Fin 2) K) = 1 := by
    rw [kpCocycle_scalar D H v hSt, kpCocycle_scalar_right_formula, hcright, hcright, one_mul]
  have heq := C.sec_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) c) (h : GL (Fin 2) K)
  rw [C.sec_scalar, one_mul, hscalar, map_one, one_mul] at heq
  rw [hmat]
  exact heq.symm

/-- The small splitting subgroups and their algebraic membership properties. -/
private structure FinLocalSmallAlgebra
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (C : FinLocalAlgebra D H v) where
  m0 : ℕ
  one_le_m0 : 1 ≤ m0
  Kc : ℕ → Subgroup C.L
  Kc_eq : ∀ m, m0 ≤ m → (Kc m : Set C.L) =
    C.sec '' {g : GL (Fin 2) (v.adicCompletion F) | ∀ i j,
      ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ∈ ball v m}
  Kc_anti : ∀ m m', m0 ≤ m → m ≤ m' → Kc m' ≤ Kc m
  Kc_inj : ∀ m, m0 ≤ m → Set.InjOn C.pr (Kc m : Set C.L)
  n_Kc : ∀ m, m0 ≤ m → ∀ x ∈ ball v m, C.n (Multiplicative.ofAdd x) ∈ Kc m
  nbar_Kc : ∀ m, m0 ≤ m → ∀ x ∈ ball v m, C.nbar (Multiplicative.ofAdd x) ∈ Kc m
  a_Kc : ∀ m, m0 ≤ m → ∀ u : (v.adicCompletion F)ˣ,
    ((u : v.adicCompletion F) - 1) ∈ ball v m → C.a u ∈ Kc m

private theorem exists_finLocalSmallAlgebra
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (C : FinLocalAlgebra D H v) :
    Nonempty (FinLocalSmallAlgebra C) := by
  classical
  let K := v.adicCompletion F
  obtain ⟨m0, hm0, hfamily⟩ := exists_smallSectionHom D H v hSt C
  let U (m : ℕ) (hm : m0 ≤ m) : Subgroup (GL (Fin 2) K) := (hfamily m hm).choose
  have hU (m : ℕ) (hm : m0 ≤ m) : ∀ g, g ∈ U m hm ↔ ∀ i j,
      ((g : Matrix (Fin 2) (Fin 2) K) i j -
        (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m :=
    (hfamily m hm).choose_spec.1
  let s (m : ℕ) (hm : m0 ≤ m) : U m hm →* C.L :=
    (hfamily m hm).choose_spec.2.choose
  have hs (m : ℕ) (hm : m0 ≤ m) : ∀ g : U m hm, s m hm g = C.sec g :=
    (hfamily m hm).choose_spec.2.choose_spec.1
  have hsinj (m : ℕ) (hm : m0 ≤ m) : Set.InjOn C.pr ((s m hm).range : Set C.L) :=
    (hfamily m hm).choose_spec.2.choose_spec.2
  let Kc (m : ℕ) : Subgroup C.L := if hm : m0 ≤ m then (s m hm).range else ⊥
  have hKc (m : ℕ) (hm : m0 ≤ m) : Kc m = (s m hm).range := dif_pos hm
  have himage (m : ℕ) (hm : m0 ≤ m) : (Kc m : Set C.L) =
      C.sec '' {g : GL (Fin 2) K | ∀ i j,
        ((g : Matrix (Fin 2) (Fin 2) K) i j -
          (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m} := by
    rw [hKc m hm]
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g : GL (Fin 2) K), (hU m hm _).mp g.property, (hs m hm g).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, (hU m hm g).mpr hg⟩, hs m hm ⟨g, (hU m hm g).mpr hg⟩⟩
  have hzero (m : ℕ) : (0 : K) ∈ ball v m := by
    change Valued.v (0 : K) ≤ WithZero.exp (-(m : ℤ))
    rw [map_zero]
    exact zero_le
  refine ⟨{
    m0 := m0
    one_le_m0 := hm0
    Kc := Kc
    Kc_eq := himage
    Kc_anti := ?_
    Kc_inj := ?_
    n_Kc := ?_
    nbar_Kc := ?_
    a_Kc := ?_
  }⟩
  · intro m m' hm hmm' x hx
    have hm' : m0 ≤ m' := hm.trans hmm'
    change x ∈ (Kc m' : Set C.L) at hx
    change x ∈ (Kc m : Set C.L)
    rw [himage m' hm'] at hx
    rw [himage m hm]
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨g, ?_, rfl⟩
    intro i j
    exact (hg i j).trans (WithZero.exp_le_exp.mpr (by omega))
  · intro m hm
    rw [hKc m hm]
    exact hsinj m hm
  · intro m hm x hx
    rw [C.sec_n]
    change C.sec (upperM K x) ∈ (Kc m : Set C.L)
    rw [himage m hm]
    refine ⟨upperM K x, ?_, rfl⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperM] <;> first | exact hx | exact hzero m
  · intro m hm x hx
    rw [C.sec_nbar]
    change C.sec (lowerM K x) ∈ (Kc m : Set C.L)
    rw [himage m hm]
    refine ⟨lowerM K x, ?_, rfl⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerM] <;> first | exact hx | exact hzero m
  · intro m hm u hu
    rw [C.sec_a]
    change C.sec (diagM K u) ∈ (Kc m : Set C.L)
    rw [himage m hm]
    refine ⟨diagM K u, ?_, rfl⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp [diagM] <;> first | exact hu | exact hzero m

/-- Every small lift has a Gauss decomposition with all three parameters small. -/
private theorem finLocalSmallAlgebra_decomposition
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (C : FinLocalAlgebra D H v) (B : FinLocalSmallAlgebra C)
    (m : ℕ) (hm : B.m0 ≤ m) (x : C.L) (hx : x ∈ B.Kc m) :
    ∃ α β : v.adicCompletion F, ∃ u : (v.adicCompletion F)ˣ,
      α ∈ ball v m ∧ β ∈ ball v m ∧ ((u : v.adicCompletion F) - 1) ∈ ball v m ∧
        x = C.n (Multiplicative.ofAdd α) * C.a u * C.nbar (Multiplicative.ofAdd β) := by
  classical
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  have hm1 : 1 ≤ m := B.one_le_m0.trans hm
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hxK := hx
  change x ∈ (B.Kc m : Set C.L) at hx
  rw [B.Kc_eq m hm] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  let M : Matrix (Fin 2) (Fin 2) K := g
  change ∀ i j, V (M i j - (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r at hg
  have ha : V (M 0 0 - 1) ≤ r := by simpa using hg 0 0
  have hd : V (M 1 1 - 1) ≤ r := by simpa using hg 1 1
  have hb : V (M 0 1) ≤ r := by simpa using hg 0 1
  have hc : V (M 1 0) ≤ r := by simpa using hg 1 0
  have hdval : V (M 1 1) = 1 := by
    simpa using V.map_eq_of_sub_lt (x := 1) (y := M 1 1) (by simpa using hd.trans_lt hr)
  have hdne : M 1 1 ≠ 0 := by
    intro h
    simp [h] at hdval
  let α : K := M 0 1 / M 1 1
  let β : K := M 1 0 / M 1 1
  let u : Kˣ := Units.mk0 (M.det / (M 1 1) ^ 2)
    (div_ne_zero g.det_ne_zero (pow_ne_zero 2 hdne))
  let dU : Kˣ := Units.mk0 (M 1 1) hdne
  have hα : α ∈ ball v m := by
    change V (M 0 1 / M 1 1) ≤ r
    rw [map_div₀, hdval, div_one]
    exact hb
  have hβ : β ∈ ball v m := by
    change V (M 1 0 / M 1 1) ≤ r
    rw [map_div₀, hdval, div_one]
    exact hc
  have had : V (M 0 0 - M 1 1) ≤ r := by
    have heq : M 0 0 - M 1 1 = (M 0 0 - 1) - (M 1 1 - 1) := by ring
    rw [heq]
    exact V.map_sub_le ha hd
  have hdetdiff : V (M.det - (M 1 1) ^ 2) ≤ r := by
    have heq : M.det - (M 1 1) ^ 2 =
        (M 0 0 - M 1 1) * M 1 1 - M 0 1 * M 1 0 := by
      rw [Matrix.det_fin_two]
      ring
    rw [heq]
    apply V.map_sub_le
    · rw [map_mul, hdval, mul_one]
      exact had
    · rw [map_mul]
      simpa only [mul_one] using mul_le_mul' hb (hc.trans hr.le)
  have hu : ((u : K) - 1) ∈ ball v m := by
    change V (M.det / (M 1 1) ^ 2 - 1) ≤ r
    have heq : M.det / (M 1 1) ^ 2 - 1 =
        (M.det - (M 1 1) ^ 2) / (M 1 1) ^ 2 := by
      rw [sub_div, div_self (pow_ne_zero 2 hdne)]
    rw [heq, map_div₀, map_pow, hdval, one_pow, div_one]
    exact hdetdiff
  have hmat : g = Matrix.GeneralLinearGroup.scalar (Fin 2) dU *
      (upperM K α * diagM K u * lowerM K β) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperM, diagM, lowerM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two, α, β, u, dU, Matrix.det_fin_two, M] <;>
      field_simp [hdne, M] <;> ring
  have hscalar : (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) dU) : PGL2 K) = 1 := by
    rw [← C.sec_pr, C.sec_scalar, map_one]
  let p : C.L := C.n (Multiplicative.ofAdd α) * C.a u * C.nbar (Multiplicative.ofAdd β)
  have hp : p ∈ B.Kc m :=
    (B.Kc m).mul_mem
      ((B.Kc m).mul_mem (B.n_Kc m hm α hα) (B.a_Kc m hm u hu))
      (B.nbar_Kc m hm β hβ)
  have hpr : C.pr (C.sec g) = C.pr p := by
    rw [C.sec_pr, hmat, QuotientGroup.mk_mul, hscalar, one_mul]
    simp only [p, map_mul, C.pr_n, C.pr_a, C.pr_nbar, QuotientGroup.mk_mul]
    rfl
  exact ⟨α, β, u, hα, hβ, hu, B.Kc_inj m hm hxK hp hpr⟩

/-- Every conjugation sends a sufficiently small splitting subgroup into a given one. -/
private theorem finLocalSmallAlgebra_conjugation
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (C : FinLocalAlgebra D H v)
    (B : FinLocalSmallAlgebra C) :
    ∀ g : C.L, ∀ m : ℕ, B.m0 ≤ m →
      ∃ m' : ℕ, B.m0 ≤ m' ∧
        ∀ x ∈ B.Kc m', g * x * g⁻¹ ∈ B.Kc m := by
  classical
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let conj (g : C.L) : C.L →* C.L := (MulAut.conj g).toMonoidHom
  let Good (g : C.L) : Prop := ∀ m : ℕ, B.m0 ≤ m →
    ∃ n : ℕ, B.m0 ≤ n ∧ ∀ x ∈ B.Kc n, conj g x ∈ B.Kc m
  change ∀ g, Good g
  have monoBall (p q : ℕ) (hpq : p ≤ q) : ball v q ⊆ ball v p := by
    intro x hx
    change V x ≤ WithZero.exp (-(p : ℤ))
    change V x ≤ WithZero.exp (-(q : ℤ)) at hx
    exact hx.trans (WithZero.exp_le_exp.mpr (by omega))
  have scaledBall (a : K) (m : ℕ) :
      ∃ n : ℕ, m ≤ n ∧ ∀ x ∈ ball v n, a * x ∈ ball v m := by
    let c := (WithZero.log (V a)).toNat
    have ha : V a ≤ WithZero.exp (c : ℤ) :=
      WithZero.le_exp_log.trans (WithZero.exp_le_exp.mpr (Int.self_le_toNat _))
    refine ⟨m + c, by omega, ?_⟩
    intro x hx
    change V (a * x) ≤ WithZero.exp (-(m : ℤ))
    change V x ≤ WithZero.exp (-((m + c : ℕ) : ℤ)) at hx
    rw [map_mul]
    calc
      V a * V x ≤ WithZero.exp (c : ℤ) * WithZero.exp (-((m + c : ℕ) : ℤ)) :=
        mul_le_mul' ha hx
      _ = WithZero.exp (-(m : ℤ)) := by
        rw [← WithZero.exp_add]
        congr 1
        omega
  have mulGood {g h : C.L} (hg : Good g) (hh : Good h) : Good (g * h) := by
    intro m hm
    obtain ⟨n, hn, hgn⟩ := hg m hm
    obtain ⟨n', hn', hhn⟩ := hh n hn
    refine ⟨n', hn', ?_⟩
    intro x hx
    have hk := hgn _ (hhn x hx)
    change g * (h * x * h⁻¹) * g⁻¹ ∈ B.Kc m at hk
    change (g * h) * x * (g * h)⁻¹ ∈ B.Kc m
    simpa only [mul_inv_rev, mul_assoc] using hk
  have centralGood (ζ : rootsOfUnity 3 ℂ) : Good (C.z ζ) := by
    intro m hm
    refine ⟨m, hm, ?_⟩
    intro x hx
    change C.z ζ * x * (C.z ζ)⁻¹ ∈ B.Kc m
    rw [C.z_central, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have nInv (t : K) : (C.n (Multiplicative.ofAdd t))⁻¹ =
      C.n (Multiplicative.ofAdd (-t)) := (map_inv C.n (Multiplicative.ofAdd t)).symm
  have upperLeftX (t : K) (g : GL (Fin 2) K) :
      xU v (upperM K t * g) = xU v g := by
    apply Units.ext
    simp [xU, xEntry, upperM, Matrix.mul_apply, Fin.sum_univ_two]
  have upperLeftSigma (t : K) (g : GL (Fin 2) K) :
      kpCocycle D H v (upperM K t) g = 1 := by
    rw [kpCocycle_pairing, upperLeftX, xU_upperM, detU_upperM]
    simp [kpPairing_one_left]
  have nGood (t : K) : Good (C.n (Multiplicative.ofAdd t)) := by
    intro m hm
    obtain ⟨nt, hmt, hscale⟩ := scaledBall t m
    obtain ⟨ntt, hmtt, hscale2⟩ := scaledBall (t * t) m
    let n := max B.m0 (max nt ntt)
    have hn : B.m0 ≤ n := le_max_left _ _
    have hnt : nt ≤ n := (le_max_left nt ntt).trans (le_max_right _ _)
    have hntt : ntt ≤ n := (le_max_right nt ntt).trans (le_max_right _ _)
    have hmn : m ≤ n := hmt.trans hnt
    refine ⟨n, hn, ?_⟩
    intro x hx
    change x ∈ (B.Kc n : Set C.L) at hx
    rw [B.Kc_eq n hn] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    let M : Matrix (Fin 2) (Fin 2) K := g
    have ha : M 0 0 - 1 ∈ ball v n := by simpa using hg 0 0
    have hd : M 1 1 - 1 ∈ ball v n := by simpa using hg 1 1
    have hb : M 0 1 ∈ ball v n := by simpa using hg 0 1
    have hc : M 1 0 ∈ ball v n := by simpa using hg 1 0
    let k : GL (Fin 2) K := upperM K t * g * upperM K (-t)
    have h00 : ((k : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) =
        (M 0 0 - 1) + t * M 1 0 := by
      simp [k, M, upperM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
    have h01 : (k : Matrix (Fin 2) (Fin 2) K) 0 1 =
        M 0 1 + t * (M 1 1 - 1) - t * (M 0 0 - 1) - (t * t) * M 1 0 := by
      simp [k, M, upperM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
    have h10 : (k : Matrix (Fin 2) (Fin 2) K) 1 0 = M 1 0 := by
      simp [k, M, upperM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
    have h11 : ((k : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) =
        (M 1 1 - 1) - t * M 1 0 := by
      simp [k, M, upperM, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
    have hkg : ∀ i j, ((k : Matrix (Fin 2) (Fin 2) K) i j -
        (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v m := by
      have hc1 := hscale _ (monoBall nt n hnt hc)
      have hd1 := hscale _ (monoBall nt n hnt hd)
      have ha1 := hscale _ (monoBall nt n hnt ha)
      have hc2 := hscale2 _ (monoBall ntt n hntt hc)
      intro i j
      fin_cases i <;> fin_cases j
      · change V ((k : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ≤ WithZero.exp (-(m : ℤ))
        rw [h00]
        exact V.map_add_le (monoBall m n hmn ha) hc1
      · have hbound : V ((k : Matrix (Fin 2) (Fin 2) K) 0 1) ≤ WithZero.exp (-(m : ℤ)) := by
          rw [h01]
          exact V.map_sub_le (V.map_sub_le (V.map_add_le (monoBall m n hmn hb) hd1) ha1) hc2
        change V ((k : Matrix (Fin 2) (Fin 2) K) 0 1 - 0) ≤ WithZero.exp (-(m : ℤ))
        simpa only [sub_zero] using hbound
      · simpa [h10] using monoBall m n hmn hc
      · change V ((k : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ WithZero.exp (-(m : ℤ))
        rw [h11]
        exact V.map_sub_le (monoBall m n hmn hd) hc1
    have heq : conj (C.n (Multiplicative.ofAdd t)) (C.sec g) = C.sec k := by
      change C.n (Multiplicative.ofAdd t) * C.sec g *
        (C.n (Multiplicative.ofAdd t))⁻¹ = C.sec k
      rw [nInv, C.sec_n, C.sec_n, C.sec_mul, upperLeftSigma, map_one, one_mul,
        C.sec_mul, kpCocycle_upperM, map_one, one_mul]
    change conj (C.n (Multiplicative.ofAdd t)) (C.sec g) ∈ (B.Kc m : Set C.L)
    rw [B.Kc_eq m hm]
    exact ⟨k, hkg, heq.symm⟩
  have wInv : C.w⁻¹ = C.w := inv_eq_of_mul_eq_one_right C.w_sq
  have wN (α : K) : conj C.w (C.n (Multiplicative.ofAdd α)) =
      C.nbar (Multiplicative.ofAdd α) := by
    change C.w * C.n (Multiplicative.ofAdd α) * C.w⁻¹ = _
    rw [wInv]
    exact C.w_n_w α
  have wNbar (β : K) : conj C.w (C.nbar (Multiplicative.ofAdd β)) =
      C.n (Multiplicative.ofAdd β) := by
    change C.w * C.nbar (Multiplicative.ofAdd β) * C.w⁻¹ = _
    rw [wInv, ← C.w_n_w β]
    calc
      _ = (C.w * C.w) * C.n (Multiplicative.ofAdd β) * (C.w * C.w) := by group
      _ = _ := by simp only [C.w_sq, one_mul, mul_one]
  have inverseSmall (m : ℕ) (hm : B.m0 ≤ m) (u : Kˣ)
      (hu : ((u : K) - 1) ∈ ball v m) :
      (((u⁻¹ : Kˣ) : K) - 1) ∈ ball v m := by
    have hr : WithZero.exp (-(m : ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      have hm1 := B.one_le_m0.trans hm
      omega
    have huval : V (u : K) = 1 := by
      simpa using V.map_eq_of_sub_lt (x := 1) (y := (u : K)) (by simpa using hu.trans_lt hr)
    have hinvval : V ((u⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, huval, inv_one]
    have hform : ((u⁻¹ : Kˣ) : K) - 1 = ((u⁻¹ : Kˣ) : K) * (1 - (u : K)) := by
      simp [Units.val_inv_eq_inv_val, mul_sub, u.ne_zero]
    change V (((u⁻¹ : Kˣ) : K) - 1) ≤ WithZero.exp (-(m : ℤ))
    rw [hform, map_mul, hinvval, one_mul]
    have hneg : (1 : K) - u = -((u : K) - 1) := by ring
    rw [hneg, V.map_neg]
    exact hu
  have wGood : Good C.w := by
    intro m hm
    refine ⟨m, hm, ?_⟩
    intro x hx
    obtain ⟨α, β, u, hα, hβ, hu, heq⟩ := finLocalSmallAlgebra_decomposition C B m hm x hx
    rw [heq, map_mul, map_mul, wN, wNbar]
    have hwa : conj C.w (C.a u) = C.a u⁻¹ := C.lift_wa u
    rw [hwa]
    exact (B.Kc m).mul_mem
      ((B.Kc m).mul_mem (B.nbar_Kc m hm α hα) (B.a_Kc m hm u⁻¹ (inverseSmall m hm u hu)))
      (B.n_Kc m hm β hβ)
  have aInv (y : Kˣ) : (C.a y)⁻¹ = C.a y⁻¹ := by
    have hp : kpPairing D H v y y⁻¹ = 1 := by
      rw [map_inv, kpPairing_self, inv_one]
    change muThree D (H.hilb v y y⁻¹) = 1 at hp
    have hh := C.a_mul y y⁻¹
    rw [hp, map_one, one_mul, mul_inv_cancel, C.a_one] at hh
    exact inv_eq_of_mul_eq_one_right hh
  have aN (y : Kˣ) (α : K) : conj (C.a y) (C.n (Multiplicative.ofAdd α)) =
      C.n (Multiplicative.ofAdd (α * (y : K))) := by
    have hh := C.lift_na (α * (y : K)) y
    have hparam : α * (y : K) * ((y⁻¹ : Kˣ) : K) = α := by
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    rw [hparam] at hh
    change C.a y * C.n (Multiplicative.ofAdd α) * (C.a y)⁻¹ = _
    rw [← hh, mul_assoc, mul_inv_cancel, mul_one]
  have aW (y : Kˣ) : C.a y * C.w = C.w * C.a y⁻¹ := by
    have hh := congrArg (fun x : C.L => x * C.w) (C.lift_wa y⁻¹)
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh.symm
  have aNbar (y : Kˣ) (β : K) : conj (C.a y) (C.nbar (Multiplicative.ofAdd β)) =
      C.nbar (Multiplicative.ofAdd (β * ((y⁻¹ : Kˣ) : K))) := by
    have hh := aN y⁻¹ β
    change C.a y⁻¹ * C.n (Multiplicative.ofAdd β) * (C.a y⁻¹)⁻¹ = _ at hh
    rw [aInv, inv_inv] at hh
    change C.a y * C.nbar (Multiplicative.ofAdd β) * (C.a y)⁻¹ = _
    rw [aInv, ← C.w_n_w β]
    calc
      _ = (C.a y * C.w) * C.n (Multiplicative.ofAdd β) * (C.w * C.a y⁻¹) := by group
      _ = (C.w * C.a y⁻¹) * C.n (Multiplicative.ofAdd β) * (C.a y * C.w) :=
        congrArg₂ (fun p q : C.L => p * C.n (Multiplicative.ofAdd β) * q) (aW y) (aW y).symm
      _ = C.w * (C.a y⁻¹ * C.n (Multiplicative.ofAdd β) * C.a y) * C.w := by group
      _ = C.w * C.n (Multiplicative.ofAdd (β * ((y⁻¹ : Kˣ) : K))) * C.w := by rw [hh]
      _ = _ := C.w_n_w _
  obtain ⟨mp, _, hpowers⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_sixthPowerNeighborhood v
  have aGood (y : Kˣ) : Good (C.a y) := by
    intro m hm
    obtain ⟨ny, hmy, hscale⟩ := scaledBall (y : K) m
    obtain ⟨nyi, hmyi, hscalei⟩ := scaledBall ((y⁻¹ : Kˣ) : K) m
    let n := max B.m0 (max mp (max ny nyi))
    have hn : B.m0 ≤ n := le_max_left _ _
    have hmp : mp ≤ n := (le_max_left mp _).trans (le_max_right _ _)
    have hny : ny ≤ n := ((le_max_left ny nyi).trans (le_max_right mp _)).trans (le_max_right _ _)
    have hnyi : nyi ≤ n := ((le_max_right ny nyi).trans (le_max_right mp _)).trans (le_max_right _ _)
    have hmn : m ≤ n := hmy.trans hny
    refine ⟨n, hn, ?_⟩
    intro x hx
    obtain ⟨α, β, u, hα, hβ, hu, heq⟩ := finLocalSmallAlgebra_decomposition C B n hn x hx
    have hp : kpPairing D H v u y = 1 := by
      change muThree D (H.hilb v u y) = 1
      rw [H.sixth_power v u y (hpowers u (monoBall mp n hmp hu)), muThree_one D]
    have hq := kpPairing_skew D H v y u
    rw [hp, mul_one] at hq
    change muThree D (H.hilb v u y) = 1 at hp
    change muThree D (H.hilb v y u) = 1 at hq
    have hcomm : C.a y * C.a u = C.a u * C.a y := by
      rw [C.a_mul, C.a_mul, hp, hq, map_one, one_mul, mul_comm y u]
      simp only [one_mul]
    have hau : conj (C.a y) (C.a u) = C.a u := by
      change C.a y * C.a u * (C.a y)⁻¹ = _
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [heq, map_mul, map_mul, aN, aNbar, hau]
    exact (B.Kc m).mul_mem
      ((B.Kc m).mul_mem
        (B.n_Kc m hm _ (by simpa only [mul_comm] using hscale α (monoBall ny n hny hα)))
        (B.a_Kc m hm u (monoBall m n hmn hu)))
      (B.nbar_Kc m hm _ (by simpa only [mul_comm] using hscalei β (monoBall nyi n hnyi hβ)))
  have scalarPr (c : Kˣ) :
      (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : PGL2 K) = 1 := by
    rw [← C.sec_pr, C.sec_scalar, map_one]
  have samePrGood (g p : C.L) (hp : Good p) (hpr : C.pr g = C.pr p) : Good g := by
    have hk : g / p ∈ C.pr.ker := by
      change C.pr (g / p) = 1
      rw [map_div, hpr]
      simp
    rw [C.pr_ker] at hk
    obtain ⟨ζ, hζ⟩ := hk
    have hg : g = C.z ζ * p := by
      rw [hζ]
      simp
    rw [hg]
    exact mulGood (centralGood ζ) hp
  intro g
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (C.pr g)
  rcases gl2_factorization v k with ⟨c, y, t, hmat⟩ | ⟨c, t, y, u, hmat⟩
  · have hpr : C.pr (C.a y * C.n (Multiplicative.ofAdd t)) = C.pr g := by
      calc
        _ = QuotientGroup.mk (diagM K y * upperM K t) := by
          simp only [map_mul, C.pr_a, C.pr_n, QuotientGroup.mk_mul] <;> rfl
        _ = QuotientGroup.mk k := by
          rw [hmat]
          simp only [QuotientGroup.mk_mul, scalarPr, one_mul] <;> rfl
        _ = _ := hk
    exact samePrGood g _ (mulGood (aGood y) (nGood t)) hpr.symm
  · have hpr : C.pr (C.n (Multiplicative.ofAdd t) * C.a y * C.w *
        C.n (Multiplicative.ofAdd u)) = C.pr g := by
      calc
        _ = QuotientGroup.mk (upperM K t * diagM K y * weylM K * upperM K u) := by
          simp only [map_mul, C.pr_n, C.pr_a, C.pr_w, QuotientGroup.mk_mul] <;> rfl
        _ = QuotientGroup.mk k := by
          rw [hmat]
          simp only [QuotientGroup.mk_mul, scalarPr, one_mul] <;> rfl
        _ = _ := hk
    exact samePrGood g _ (mulGood (mulGood (mulGood (nGood t) (aGood y)) wGood) (nGood u)) hpr.symm

/-- The small splitting subgroups form an open neighborhood basis for a group topology. -/
private theorem exists_finLocalSmallTopology
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (C : FinLocalAlgebra D H v)
    (B : FinLocalSmallAlgebra C) :
    ∃ t : TopologicalSpace C.L, @IsTopologicalGroup C.L t C.grp ∧
      (∀ m, B.m0 ≤ m → @IsOpen C.L t (B.Kc m : Set C.L)) ∧
      (∀ U ∈ @nhds C.L t (1 : C.L), ∃ m, B.m0 ≤ m ∧ (B.Kc m : Set C.L) ⊆ U) := by
  exact ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_subgroupBasisTopology
    B.m0 B.Kc B.Kc_anti (finLocalSmallAlgebra_conjugation D H v hSt C B)

/-- The small subgroup basis makes the projection to canonical PGL₂ continuous and open. -/
private theorem finLocalSmallTopology_projection
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (C : FinLocalAlgebra D H v) (B : FinLocalSmallAlgebra C)
    (t : TopologicalSpace C.L)
    (htg : @IsTopologicalGroup C.L t C.grp)
    (hKopen : ∀ m, B.m0 ≤ m → @IsOpen C.L t (B.Kc m : Set C.L))
    (hKbasis : ∀ U ∈ @nhds C.L t (1 : C.L),
      ∃ m, B.m0 ≤ m ∧ (B.Kc m : Set C.L) ⊆ U) :
    @Continuous C.L (PGL2 (v.adicCompletion F)) t inferInstance C.pr ∧
      @IsOpenMap C.L (PGL2 (v.adicCompletion F)) t inferInstance C.pr := by
  classical
  letI : TopologicalSpace C.L := t
  letI : IsTopologicalGroup C.L := htg
  let K := v.adicCompletion F
  let Uc : ℕ → Set (GL (Fin 2) K) := fun m => {g | ∀ i j,
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ WithZero.exp (-(m : ℤ))}
  have hcong := ArtinPrimitiveRoots.Proofs.th_cover_sol.congruenceTopology v
  have himage (m : ℕ) (hm : B.m0 ≤ m) :
      C.pr '' (B.Kc m : Set C.L) = QuotientGroup.mk '' Uc m := by
    rw [B.Kc_eq m hm]
    change C.pr '' (C.sec '' Uc m) = QuotientGroup.mk '' Uc m
    ext y
    constructor
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, (C.sec_pr g).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨C.sec g, ⟨g, hg, rfl⟩, C.sec_pr g⟩
  have hpopen (m : ℕ) (hm : B.m0 ≤ m) :
      IsOpen (C.pr '' (B.Kc m : Set C.L)) := by
    rw [himage m hm]
    exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ (hcong.1 m)
  have hKnhds (m : ℕ) (hm : B.m0 ≤ m) : (B.Kc m : Set C.L) ∈ nhds (1 : C.L) :=
    (hKopen m hm).mem_nhds (B.Kc m).one_mem
  refine ⟨continuous_of_tendsto_nhds_one C.pr ?_, ?_⟩
  · change Filter.map C.pr (nhds (1 : C.L)) ≤ nhds (1 : PGL2 K)
    intro U hU
    have hq : QuotientGroup.mk ⁻¹' U ∈ nhds (1 : GL (Fin 2) K) := by
      exact QuotientGroup.continuous_mk.continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, hm, hsmall⟩ := hcong.2 B.m0 _ hq
    change C.pr ⁻¹' U ∈ nhds (1 : C.L)
    apply Filter.mem_of_superset (hKnhds m hm)
    intro x hx
    have hximage : C.pr x ∈ QuotientGroup.mk '' Uc m := by
      rw [← himage m hm]
      exact ⟨x, hx, rfl⟩
    obtain ⟨g, hg, heq⟩ := hximage
    change C.pr x ∈ U
    rw [← heq]
    exact hsmall hg
  · apply IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr
    intro U hU
    obtain ⟨m, hm, hsub⟩ := hKbasis (C.pr ⁻¹' U) (Filter.mem_map.mp hU)
    have hI : C.pr '' (B.Kc m : Set C.L) ∈ nhds (1 : PGL2 K) :=
      (hpopen m hm).mem_nhds ⟨1, (B.Kc m).one_mem, C.pr.map_one⟩
    apply Filter.mem_of_superset hI
    rintro y ⟨x, hx, rfl⟩
    exact hsub hx

/-- The small splitting subgroups are compact in their constructed local topology. -/
private theorem finLocalSmallTopology_compact
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (C : FinLocalAlgebra D H v) (B : FinLocalSmallAlgebra C)
    (t : TopologicalSpace C.L)
    (htg : @IsTopologicalGroup C.L t C.grp)
    (hKopen : ∀ m, B.m0 ≤ m → @IsOpen C.L t (B.Kc m : Set C.L))
    (hKbasis : ∀ U ∈ @nhds C.L t (1 : C.L),
      ∃ m, B.m0 ≤ m ∧ (B.Kc m : Set C.L) ⊆ U) :
    ∀ m, B.m0 ≤ m → @IsCompact C.L t (B.Kc m : Set C.L) := by
  classical
  let : TopologicalSpace C.L := t
  let : IsTopologicalGroup C.L := htg
  obtain ⟨hcont, hopen⟩ := finLocalSmallTopology_projection C B t htg hKopen hKbasis
  intro m hm
  let K := v.adicCompletion F
  let s : Set C.L := B.Kc m
  let r : s → PGL2 K := fun x => C.pr x
  have hrc : Continuous r := hcont.comp continuous_subtype_val
  have hri : Function.Injective r := by
    intro x y h
    exact Subtype.ext (B.Kc_inj m hm x.property y.property h)
  have hro : IsOpenMap r := hopen.comp (hKopen m hm).isOpenMap_subtype_val
  have hremb := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hrc hri hro
  let Uc : Set (GL (Fin 2) K) := {g | ∀ i j,
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ WithZero.exp (-(m : ℤ))}
  have himage : C.pr '' s = QuotientGroup.mk '' Uc := by
    change C.pr '' (B.Kc m : Set C.L) = QuotientGroup.mk '' Uc
    rw [B.Kc_eq m hm]
    change C.pr '' (C.sec '' Uc) = QuotientGroup.mk '' Uc
    ext y
    constructor
    · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, (C.sec_pr g).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨C.sec g, ⟨g, hg, rfl⟩, C.sec_pr g⟩
  have hcompactImage : IsCompact (C.pr '' s) := by
    rw [himage]
    exact (ArtinPrimitiveRoots.Proofs.th_cover_sol.congruenceCompact v m
      (B.one_le_m0.trans hm)).image QuotientGroup.continuous_mk
  have hrange : Set.range r = C.pr '' s := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcu : IsCompact (Set.univ : Set s) := hremb.isEmbedding.isCompact_iff.mpr (by
    rw [Set.image_univ, hrange]
    exact hcompactImage)
  exact isCompact_iff_isCompact_univ.mpr hcu

/-- Assemble the algebraic cover and the compact open small-subgroup topology. -/
private theorem exists_finLocalCoverBase
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) : Nonempty (FinLocalCover D H v) := by
  obtain ⟨C⟩ := exists_finLocalAlgebra D H v hSt
  obtain ⟨B⟩ := exists_finLocalSmallAlgebra D H v hSt C
  obtain ⟨t, htg, hKopen, hKbasis⟩ := exists_finLocalSmallTopology D H v hSt C B
  obtain ⟨hcont, hopen⟩ := finLocalSmallTopology_projection C B t htg hKopen hKbasis
  have hcompact := finLocalSmallTopology_compact C B t htg hKopen hKbasis
  exact ⟨{
    L := C.L
    grp := C.grp
    top := t
    tg := htg
    z := C.z
    z_inj := C.z_inj
    z_central := C.z_central
    pr := C.pr
    pr_surj := C.pr_surj
    pr_ker := C.pr_ker
    pr_cont := hcont
    pr_open := hopen
    n := C.n
    nbar := C.nbar
    a := C.a
    w := C.w
    sec := C.sec
    sec_mul := C.sec_mul
    sec_pr := C.sec_pr
    sec_scalar := C.sec_scalar
    sec_n := C.sec_n
    sec_nbar := C.sec_nbar
    sec_a := C.sec_a
    sec_w := C.sec_w
    pr_n := C.pr_n
    pr_nbar := C.pr_nbar
    pr_a := C.pr_a
    pr_w := C.pr_w
    a_one := C.a_one
    a_mul := C.a_mul
    lift_na := C.lift_na
    lift_wa := C.lift_wa
    lift_wn := C.lift_wn
    w_sq := C.w_sq
    w_n_w := C.w_n_w
    m0 := B.m0
    Kc := B.Kc
    Kc_open := hKopen
    Kc_compact := hcompact
    Kc_anti := B.Kc_anti
    Kc_nhds := hKbasis
    Kc_inj := B.Kc_inj
    n_Kc := B.n_Kc
    nbar_Kc := B.nbar_Kc
    a_Kc := B.a_Kc
  }⟩

/-- The tame splitting correction is trivial on a sufficiently small congruence subgroup. -/
private theorem exists_tameSmallIdentity
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F) :
    ∃ m0 : ℕ, 1 ≤ m0 ∧ ∀ m : ℕ, m0 ≤ m →
      ∀ g : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ∈ ball v m) →
        tameSplit D H v g = 1 := by
  classical
  obtain ⟨m0, hm0, hpowers⟩ :=
    ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_sixthPowerNeighborhood v
  refine ⟨m0, hm0, ?_⟩
  intro m hm g hg
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  let M : Matrix (Fin 2) (Fin 2) K := g
  let Δ : K := M.det
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hrr : r ≤ WithZero.exp (-(m0 : ℤ)) := by
    dsimp [r]
    exact WithZero.exp_le_exp.mpr (by omega)
  change ∀ i j, V (M i j - (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r at hg
  have ha : V (M 0 0 - 1) ≤ r := by simpa using hg 0 0
  have hd : V (M 1 1 - 1) ≤ r := by simpa using hg 1 1
  have hb : V (M 0 1) ≤ r := by simpa using hg 0 1
  have hc : V (M 1 0) ≤ r := by simpa using hg 1 0
  have near_one (x : K) (hx : V (x - 1) ≤ r) : V x = 1 := by
    simpa using V.map_eq_of_sub_lt (x := 1) (y := x) (by simpa using hx.trans_lt hr)
  have small_mul {x y : K} (hx : V x ≤ r) (hy : V y ≤ 1) : V (x * y) ≤ r := by
    rw [map_mul]
    simpa only [mul_one] using mul_le_mul' hx hy
  have hΔsmall : V (Δ - 1) ≤ r := by
    have heq : Δ - 1 = (M 0 0 - 1) * M 1 1 + (M 1 1 - 1) - M 0 1 * M 1 0 := by
      dsimp [Δ]
      rw [Matrix.det_fin_two]
      ring
    rw [heq]
    exact V.map_sub_le (V.map_add_le (small_mul ha (near_one _ hd).le) hd)
      (small_mul hb (hc.trans hr.le))
  have hΔval : V Δ = 1 := near_one Δ hΔsmall
  have hΔne : Δ ≠ 0 := g.det_ne_zero
  have hratio : V (M 1 1 / Δ - 1) ≤ r := by
    have hdiff : V (M 1 1 - Δ) ≤ r := by
      have heq : M 1 1 - Δ = (M 1 1 - 1) - (Δ - 1) := by ring
      rw [heq]
      exact V.map_sub_le hd hΔsmall
    have heq : M 1 1 / Δ - 1 = (M 1 1 - Δ) / Δ := by
      rw [sub_div, div_self hΔne]
    rw [heq, map_div₀, hΔval, div_one]
    exact hdiff
  unfold tameSplit
  split_ifs with h
  · let u : Kˣ := Units.mk0 (M 1 1) h.2 / detU v g
    have hu : V ((u : K) - 1) ≤ r := by
      dsimp only [u]
      rw [Units.val_div_eq_div_val, Units.val_mk0]
      change V (M 1 1 / Δ - 1) ≤ r
      exact hratio
    change muThree D (H.hilb v u (Units.mk0 (M 1 0) h.1.1)) = 1
    rw [H.sixth_power v u _ (hpowers u (hu.trans hrr)), muThree_one D]
  · rfl

/-- The algebraic view of an arbitrary finite local cover. -/
private def finLocalAlgebraOfCover
    {D : FieldData F} {H : HilbertData F} {v : FinPlace F}
    (L : FinLocalCover D H v) : FinLocalAlgebra D H v where
  L := L.L
  grp := L.grp
  z := L.z
  z_inj := L.z_inj
  z_central := L.z_central
  pr := L.pr
  pr_surj := L.pr_surj
  pr_ker := L.pr_ker
  n := L.n
  nbar := L.nbar
  a := L.a
  w := L.w
  sec := L.sec
  sec_mul := L.sec_mul
  sec_pr := L.sec_pr
  sec_scalar := L.sec_scalar
  sec_n := L.sec_n
  sec_nbar := L.sec_nbar
  sec_a := L.sec_a
  sec_w := L.sec_w
  pr_n := L.pr_n
  pr_nbar := L.pr_nbar
  pr_a := L.pr_a
  pr_w := L.pr_w
  a_one := L.a_one
  a_mul := L.a_mul
  lift_na := L.lift_na
  lift_wa := L.lift_wa
  lift_wn := L.lift_wn
  w_sq := L.w_sq
  w_n_w := L.w_n_w

/-- The corrected integral section used for the tame maximal compact. -/
private def tameIntegralLift
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : FinLocalCover D H v)
    (k : GL (Fin 2) (v.adicCompletionIntegers F)) : L.L :=
  L.z (tameSplit D H v
    (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k)) *
      L.sec (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers F).subtype k)

/-- The integral tame lift is continuous at one, independently of the tame hypothesis. -/
private theorem tameIntegralLift_continuousAt_one
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (L : FinLocalCover D H v) :
    ContinuousAt (tameIntegralLift D H v L) 1 := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let j : O →+* K := O.subtype
  let ιM : Matrix (Fin 2) (Fin 2) O →+* Matrix (Fin 2) (Fin 2) K := RingHom.mapMatrix j
  let ι : GL (Fin 2) O →* GL (Fin 2) K := Matrix.GeneralLinearGroup.map j
  have hM : Continuous ιM := continuous_id.matrix_map continuous_subtype_val
  have hι : Continuous ι := hM.units_map ιM.toMonoidHom
  let C := finLocalAlgebraOfCover L
  obtain ⟨B⟩ := exists_finLocalSmallAlgebra D H v hSt C
  obtain ⟨ms, _, hcorrection⟩ := exists_tameSmallIdentity D H v
  have hsecOne : L.sec (1 : GL (Fin 2) K) = 1 := by
    simpa only [map_one] using L.sec_scalar (1 : Kˣ)
  have hOne : tameIntegralLift D H v L 1 = 1 := by
    simp only [tameIntegralLift, map_one]
    rw [show tameSplit D H v (1 : GL (Fin 2) K) = 1 by simp [tameSplit],
      map_one, one_mul, hsecOne]
  rw [ContinuousAt, hOne]
  change Filter.map (tameIntegralLift D H v L) (nhds (1 : GL (Fin 2) O)) ≤ nhds (1 : L.L)
  intro U hU
  obtain ⟨m, hm, hsub⟩ := L.Kc_nhds U hU
  let N := max m (max B.m0 ms)
  have hmn : m ≤ N := le_max_left _ _
  have hBN : B.m0 ≤ N := (le_max_left B.m0 ms).trans (le_max_right _ _)
  have hmsN : ms ≤ N := (le_max_right B.m0 ms).trans (le_max_right _ _)
  let Uc : Set (GL (Fin 2) K) := {g | ∀ i j,
    Valued.v ((g : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ WithZero.exp (-(N : ℤ))}
  have hWopen : IsOpen (ι ⁻¹' Uc) :=
    ((ArtinPrimitiveRoots.Proofs.th_cover_sol.congruenceTopology v).1 N).preimage hι
  have hWone : (1 : GL (Fin 2) O) ∈ ι ⁻¹' Uc := by
    simp only [Set.mem_preimage, map_one]
    simp [Uc]
  have monoBall (x : K) (hx : x ∈ ball v N) : x ∈ ball v m := by
    change Valued.v x ≤ WithZero.exp (-(N : ℤ)) at hx
    change Valued.v x ≤ WithZero.exp (-(m : ℤ))
    exact hx.trans (WithZero.exp_le_exp.mpr (by omega))
  change (tameIntegralLift D H v L) ⁻¹' U ∈ nhds (1 : GL (Fin 2) O)
  apply Filter.mem_of_superset (hWopen.mem_nhds hWone)
  intro k hk
  have hg : ∀ i j, ((ι k : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ∈ ball v N := hk
  have hsecB : C.sec (ι k) ∈ B.Kc N := by
    change C.sec (ι k) ∈ (B.Kc N : Set C.L)
    rw [B.Kc_eq N hBN]
    exact ⟨ι k, hg, rfl⟩
  obtain ⟨α, β, u, hα, hβ, hu, heq⟩ :=
    finLocalSmallAlgebra_decomposition C B N hBN (C.sec (ι k)) hsecB
  have hsecL : L.sec (ι k) ∈ L.Kc m := by
    change C.sec (ι k) ∈ L.Kc m
    rw [heq]
    exact (L.Kc m).mul_mem
      ((L.Kc m).mul_mem (L.n_Kc m hm α (monoBall α hα))
        (L.a_Kc m hm u (monoBall ((u : K) - 1) hu)))
      (L.nbar_Kc m hm β (monoBall β hβ))
  have heval : tameIntegralLift D H v L k = L.sec (ι k) := by
    change L.z (tameSplit D H v (ι k)) * L.sec (ι k) = L.sec (ι k)
    rw [hcorrection N hmsN (ι k) hg, map_one, one_mul]
  change tameIntegralLift D H v L k ∈ U
  rw [heval]
  exact hsub hsecL

/-- At a tame place the integral corrected section is a continuous homomorphism. -/
private theorem exists_tameIntegralLiftHom
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (L : FinLocalCover D H v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    ∃ κ : GL (Fin 2) (v.adicCompletionIntegers F) →* L.L,
      (∀ k, κ k = tameIntegralLift D H v L k) ∧ Continuous κ := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let j : O →+* K := O.subtype
  let ι : GL (Fin 2) O →* GL (Fin 2) K := Matrix.GeneralLinearGroup.map j
  have integral (k : GL (Fin 2) O) :
      ∀ i j, (ι k : Matrix (Fin 2) (Fin 2) K) i j ∈ O := by
    intro i j
    exact ((k : Matrix (Fin 2) (Fin 2) O) i j).property
  have detUnit (k : GL (Fin 2) O) :
      Valued.v ((ι k : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    have hdet : (ι k : Matrix (Fin 2) (Fin 2) K).det =
        j ((k : Matrix (Fin 2) (Fin 2) O).det) :=
      (j.map_det (k : Matrix (Fin 2) (Fin 2) O)).symm
    rw [hdet]
    exact (Valuation.integer.integers (Valued.v : Valuation K _)).valuation_unit
      (Matrix.GeneralLinearGroup.det k)
  have hsecOne : L.sec (1 : GL (Fin 2) K) = 1 := by
    simpa only [map_one] using L.sec_scalar (1 : Kˣ)
  let κ : GL (Fin 2) O →* L.L := {
    toFun := tameIntegralLift D H v L
    map_one' := by
      simp only [tameIntegralLift, map_one]
      rw [show tameSplit D H v (1 : GL (Fin 2) K) = 1 by simp [tameSplit],
        map_one, one_mul, hsecOne]
    map_mul' := by
      intro k₁ k₂
      have hs := tameSplit_mul D H v hv (ι k₁) (ι k₂)
        (integral k₁) (integral k₂) (detUnit k₁) (detUnit k₂)
      change L.z (tameSplit D H v (ι (k₁ * k₂))) * L.sec (ι (k₁ * k₂)) =
        (L.z (tameSplit D H v (ι k₁)) * L.sec (ι k₁)) *
          (L.z (tameSplit D H v (ι k₂)) * L.sec (ι k₂))
      rw [map_mul, hs, map_mul, map_mul]
      rw [mul_assoc, mul_assoc, ← L.sec_mul]
      rw [← mul_assoc (L.z (tameSplit D H v (ι k₂))),
        L.z_central (tameSplit D H v (ι k₂)) (L.sec (ι k₁))]
      simp only [mul_assoc]
  }
  refine ⟨κ, fun _ => rfl, ?_⟩
  exact continuous_of_continuousAt_one κ
    (tameIntegralLift_continuousAt_one D H v hSt L)

/-- The tame integral range has no nontrivial central phase in its projection kernel. -/
private theorem tameIntegralLift_range_inj
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : FinLocalCover D H v)
    (κ : GL (Fin 2) (v.adicCompletionIntegers F) →* L.L)
    (hκ : ∀ k, κ k = tameIntegralLift D H v L k) :
    Set.InjOn L.pr (κ.range : Set L.L) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let ι : GL (Fin 2) O →* GL (Fin 2) K := Matrix.GeneralLinearGroup.map O.subtype
  have hz (ζ : rootsOfUnity 3 ℂ) : L.pr (L.z ζ) = 1 := by
    change L.z ζ ∈ L.pr.ker
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hpr (k : GL (Fin 2) O) : L.pr (κ k) = QuotientGroup.mk (ι k) := by
    rw [hκ]
    change L.pr (L.z (tameSplit D H v (ι k)) * L.sec (ι k)) = QuotientGroup.mk (ι k)
    rw [map_mul, hz, L.sec_pr, one_mul]
  have hker (k : GL (Fin 2) O) (hk : L.pr (κ k) = 1) : κ k = 1 := by
    have hc : ι k ∈ Subgroup.center (GL (Fin 2) K) :=
      (QuotientGroup.eq_one_iff (ι k)).mp (by rw [← hpr]; exact hk)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨c, hc⟩ := hc
    rw [hκ]
    change L.z (tameSplit D H v (ι k)) * L.sec (ι k) = 1
    rw [← hc, L.sec_scalar]
    have hs : tameSplit D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
      simp [tameSplit, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar]
    rw [hs, map_one, one_mul]
  intro x hx y hy hxy
  obtain ⟨kx, rfl⟩ := hx
  obtain ⟨ky, rfl⟩ := hy
  have h := hker (kx * ky⁻¹) (by
    simp only [map_mul, map_inv, hxy, mul_inv_cancel])
  have heq : κ kx * (κ ky)⁻¹ = 1 := by
    simpa only [map_mul, map_inv] using h
  exact mul_inv_eq_one.mp heq

/-- The corrected integral lift range contains an open small splitting neighborhood. -/
private theorem tameIntegralLift_range_open
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (L : FinLocalCover D H v)
    (κ : GL (Fin 2) (v.adicCompletionIntegers F) →* L.L)
    (hκ : ∀ k, κ k = tameIntegralLift D H v L k) :
    IsOpen (κ.range : Set L.L) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let C := finLocalAlgebraOfCover L
  obtain ⟨B⟩ := exists_finLocalSmallAlgebra D H v hSt C
  obtain ⟨ms, _, hcorrection⟩ := exists_tameSmallIdentity D H v
  let N := max 1 (max L.m0 (max B.m0 ms))
  have h1N : 1 ≤ N := le_max_left _ _
  have hN : max L.m0 (max B.m0 ms) ≤ N := le_max_right _ _
  have hmN : L.m0 ≤ N := (le_max_left _ _).trans hN
  have hBN : B.m0 ≤ N := (le_max_left B.m0 ms).trans ((le_max_right _ _).trans hN)
  have hmsN : ms ≤ N := (le_max_right B.m0 ms).trans ((le_max_right _ _).trans hN)
  let Uc : Set (GL (Fin 2) K) := {g | ∀ i j,
    V ((g : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ WithZero.exp (-(N : ℤ))}
  have hr : WithZero.exp (-(N : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have integralEntries (g : GL (Fin 2) K) (hg : g ∈ Uc) :
      ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ O := by
    intro i j
    change V ((g : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1
    have hδ : V ((1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ 1 := by
      fin_cases i <;> fin_cases j <;> simp
    have hb := V.map_add_le ((hg i j).trans hr) hδ
    simpa only [sub_add_cancel] using hb
  obtain ⟨Ug, hUg⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.exists_congruenceSubgroup v N h1N
  have invCongruent (g : GL (Fin 2) K) (hg : g ∈ Uc) : g⁻¹ ∈ Uc :=
    (hUg g⁻¹).mp (Ug.inv_mem ((hUg g).mpr hg))
  have monoBall (x : K) (hx : x ∈ ball v N) : x ∈ ball v L.m0 := by
    change V x ≤ WithZero.exp (-(N : ℤ)) at hx
    change V x ≤ WithZero.exp (-(L.m0 : ℤ))
    exact hx.trans (WithZero.exp_le_exp.mpr (by omega))
  have smallSec (g : GL (Fin 2) K) (hg : g ∈ Uc) : L.sec g ∈ L.Kc L.m0 := by
    have hsecB : C.sec g ∈ B.Kc N := by
      change C.sec g ∈ (B.Kc N : Set C.L)
      rw [B.Kc_eq N hBN]
      exact ⟨g, hg, rfl⟩
    obtain ⟨α, β, u, hα, hβ, hu, heq⟩ :=
      finLocalSmallAlgebra_decomposition C B N hBN (C.sec g) hsecB
    change C.sec g ∈ L.Kc L.m0
    rw [heq]
    exact (L.Kc L.m0).mul_mem
      ((L.Kc L.m0).mul_mem (L.n_Kc L.m0 le_rfl α (monoBall α hα))
        (L.a_Kc L.m0 le_rfl u (monoBall ((u : K) - 1) hu)))
      (L.nbar_Kc L.m0 le_rfl β (monoBall β hβ))
  let q : GL (Fin 2) K → PGL2 K := QuotientGroup.mk
  let W : Set L.L := (L.Kc L.m0 : Set L.L) ∩ L.pr ⁻¹' (q '' Uc)
  have hUcOpen : IsOpen Uc :=
    (ArtinPrimitiveRoots.Proofs.th_cover_sol.congruenceTopology v).1 N
  have hqOpen : IsOpen (q '' Uc) := QuotientGroup.isOpenMap_coe Uc hUcOpen
  have hWopen : IsOpen W :=
    (L.Kc_open L.m0 le_rfl).inter (hqOpen.preimage L.pr_cont)
  have hWone : (1 : L.L) ∈ W := by
    refine ⟨(L.Kc L.m0).one_mem, ?_⟩
    change L.pr (1 : L.L) ∈ q '' Uc
    refine ⟨1, ?_, ?_⟩
    · simp [Uc]
    · simp [q]
  have hsub : W ⊆ (κ.range : Set L.L) := by
    intro x hx
    obtain ⟨g, hg, hgpr⟩ := hx.2
    have hgi := integralEntries g hg
    have hginv := integralEntries g⁻¹ (invCongruent g hg)
    have hd : (g⁻¹ : GL (Fin 2) K).val.det ∈ O := by
      rw [Matrix.det_fin_two]
      exact O.toSubring.sub_mem
        (O.toSubring.mul_mem (hginv 0 0) (hginv 1 1))
        (O.toSubring.mul_mem (hginv 0 1) (hginv 1 0))
    obtain ⟨k, hk⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.integralGL2_lift v g hgi hd
    have hκsec : κ k = L.sec g := by
      rw [hκ]
      change L.z (tameSplit D H v (Matrix.GeneralLinearGroup.map O.subtype k)) *
        L.sec (Matrix.GeneralLinearGroup.map O.subtype k) = L.sec g
      rw [hk, hcorrection N hmsN g hg, map_one, one_mul]
    have heq : κ k = x := by
      apply L.Kc_inj L.m0 le_rfl (by rw [hκsec]; exact smallSec g hg) hx.1
      rw [hκsec, L.sec_pr]
      exact hgpr
    exact ⟨k, heq⟩
  exact κ.range.isOpen_of_mem_nhds
    (Filter.mem_of_superset (hWopen.mem_nhds hWone) hsub)

/-- The compact integral lift range projects exactly onto the integral PGL₂ image. -/
private theorem tameIntegralLift_range_compact_image
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : FinLocalCover D H v)
    (κ : GL (Fin 2) (v.adicCompletionIntegers F) →* L.L)
    (hκ : ∀ k, κ k = tameIntegralLift D H v L k)
    (hκcont : Continuous κ) :
    IsCompact (κ.range : Set L.L) ∧
      L.pr '' (κ.range : Set L.L) =
        {g | ∃ k : GL (Fin 2) (v.adicCompletion F),
          (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
            v.adicCompletionIntegers F) ∧
          (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈
            v.adicCompletionIntegers F ∧ QuotientGroup.mk k = g} := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let : CompactSpace O := ArtinPrimitiveRoots.Proofs.th_cover_sol.compact_adicCompletionIntegers v
  let : CompactSpace (Matrix (Fin 2) (Fin 2) O) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → O))
  let j : O →+* K := O.subtype
  let ι : GL (Fin 2) O →* GL (Fin 2) K := Matrix.GeneralLinearGroup.map j
  have hc : IsCompact (κ.range : Set L.L) := isCompact_range hκcont
  have hz (ζ : rootsOfUnity 3 ℂ) : L.pr (L.z ζ) = 1 := by
    change L.z ζ ∈ L.pr.ker
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hpr (k : GL (Fin 2) O) : L.pr (κ k) = QuotientGroup.mk (ι k) := by
    rw [hκ]
    change L.pr (L.z (tameSplit D H v (ι k)) * L.sec (ι k)) = QuotientGroup.mk (ι k)
    rw [map_mul, hz, L.sec_pr, one_mul]
  have integralDetInv (k : GL (Fin 2) O) : (ι k)⁻¹.val.det ∈ O := by
    have hinv : (ι k)⁻¹ = ι k⁻¹ := (map_inv ι k).symm
    have hdet : (ι k⁻¹ : Matrix (Fin 2) (Fin 2) K).det = j (k⁻¹.val.det) :=
      (j.map_det ((k⁻¹ : GL (Fin 2) O) : Matrix (Fin 2) (Fin 2) O)).symm
    rw [hinv]
    change (ι k⁻¹ : Matrix (Fin 2) (Fin 2) K).det ∈ O
    rw [hdet]
    exact (k⁻¹.val.det).property
  refine ⟨hc, ?_⟩
  ext q
  constructor
  · rintro ⟨x, hx, hqx⟩
    obtain ⟨k, rfl⟩ := hx
    refine ⟨ι k, ?_, integralDetInv k, ?_⟩
    · intro i j
      exact ((k : Matrix (Fin 2) (Fin 2) O) i j).property
    · exact (hpr k).symm.trans hqx
  · rintro ⟨g, hg, hd, hgq⟩
    obtain ⟨k, hk⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.integralGL2_lift v g hg hd
    refine ⟨κ k, ⟨k, rfl⟩, ?_⟩
    rw [hpr, show ι k = g from hk]
    exact hgq

/-- Integral standard generators have trivial tame correction and belong to the lift range. -/
private theorem tameIntegralLift_generators_mem
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : FinLocalCover D H v)
    (κ : GL (Fin 2) (v.adicCompletionIntegers F) →* L.L)
    (hκ : ∀ k, κ k = tameIntegralLift D H v L k) :
    (∀ x ∈ v.adicCompletionIntegers F,
      L.n (Multiplicative.ofAdd x) ∈ κ.range) ∧
    (∀ u : (v.adicCompletion F)ˣ,
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈
        v.adicCompletionIntegers F → L.a u ∈ κ.range) ∧
    L.w ∈ κ.range ∧
    (∀ x : v.adicCompletion F, Valued.v x < 1 →
      L.nbar (Multiplicative.ofAdd x) ∈ κ.range) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  have inverseDet (g : GL (Fin 2) K) :
      g⁻¹.val.det = (((detU v g)⁻¹ : Kˣ) : K) := by
    change ((Matrix.GeneralLinearGroup.det g⁻¹ : Kˣ) : K) =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ) : K)
    rw [map_inv]
  have lowerDet (x : K) : detU v (lowerM K x) = 1 := by
    apply Units.ext
    simp [detU, lowerM, Matrix.det_fin_two]
  have sec_mem (g : GL (Fin 2) K)
      (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) K) i j ∈ O)
      (hd : g⁻¹.val.det ∈ O) (hs : tameSplit D H v g = 1) : L.sec g ∈ κ.range := by
    obtain ⟨k, hk⟩ := ArtinPrimitiveRoots.Proofs.th_cover_sol.integralGL2_lift v g hg hd
    refine ⟨k, ?_⟩
    rw [hκ]
    change L.z (tameSplit D H v (Matrix.GeneralLinearGroup.map O.subtype k)) *
      L.sec (Matrix.GeneralLinearGroup.map O.subtype k) = L.sec g
    rw [hk, hs, map_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [L.sec_n]
    apply sec_mem (upperM K x)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [upperM, O, ValuationSubring.one_mem, ValuationSubring.zero_mem, hx]
    · rw [inverseDet, detU_upperM]
      simpa using O.one_mem
    · simp [tameSplit, upperM]
  · intro u hu huinv
    rw [L.sec_a]
    apply sec_mem (diagM K u)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [diagM, O, ValuationSubring.one_mem, ValuationSubring.zero_mem, hu]
    · rw [inverseDet, detU_diagM]
      exact huinv
    · simp [tameSplit, diagM]
  · rw [L.sec_w]
    apply sec_mem (weylM K)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [weylM, ValuationSubring.one_mem, ValuationSubring.zero_mem]
    · rw [inverseDet, detU_weylM]
      simpa using O.toSubring.neg_mem O.one_mem
    · simp [tameSplit, weylM]
  · intro x hx
    have hxi : x ∈ O := hx.le
    rw [L.sec_nbar]
    apply sec_mem (lowerM K x)
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerM, ValuationSubring.one_mem, ValuationSubring.zero_mem, hxi]
    · rw [inverseDet, lowerDet]
      simpa using O.one_mem
    · unfold tameSplit
      rw [lowerDet]
      simp [lowerM, hilb_one_left, muThree_one]

/-- The corrected integral range supplies all fields of the tame splitting package. -/
private theorem exists_finLocalTameSplitting
    (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (L : FinLocalCover D H v)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) : Nonempty (TameSplitting L) := by
  obtain ⟨κ, hκ, hκcont⟩ := exists_tameIntegralLiftHom D H v hSt L hv
  obtain ⟨hc, himage⟩ := tameIntegralLift_range_compact_image D H v L κ hκ hκcont
  obtain ⟨hn, ha, hw, hnbar⟩ := tameIntegralLift_generators_mem D H v L κ hκ
  exact ⟨{
    Kmax := κ.range
    open_ := tameIntegralLift_range_open D H v hSt L κ hκ
    compact := hc
    inj := tameIntegralLift_range_inj D H v L κ hκ
    image := himage
    n_mem := hn
    a_mem := ha
    w_mem := hw
    nbar_mem := hnbar
  }⟩

/-- **cov:local-cover** (top, local): at every finite place there is a local cover built from
`kpCocycle` (as `GL₂ × μ3` modulo the scalar section) with the interface `FinLocalCover`, and at
every `v ∤ 6` a tame splitting. -/
theorem exists_finLocalCover (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    ∃ L : FinLocalCover D H v, (6 : 𝓞 F) ∉ v.asIdeal → Nonempty (TameSplitting L) := by
  obtain ⟨L⟩ := exists_finLocalCoverBase D H v hSt
  exact ⟨L, fun hv => exists_finLocalTameSplitting D H v hSt L hv⟩

/-- The places of `F`. -/
abbrev Place (F : Type) [Field F] [NumberField F] := FinPlace F ⊕ InfinitePlace F

/-- **cov:adelic (top)**: the adelic cover packaged for route C. `RP` is the restricted product
of the local covers (`L v` at finite places, the trivial cover `PGL₂(ℂ) × μ3(ℂ)` at complex
places) with respect to the tame maximal compacts; `q : RP → G` divides by the
`N0 = {(ζ_v) : Π ζ_v = 1}`; `tc` is the frozen `ThetaCover` on `G = RP ⧸ N0`, and its local data
are the images of the local covers. C2 of `sol-gate-theta` installs the insertion, component,
quotient-topology, and restricted-tuple compatibility identities used by consumers. The topology
correction from `sol-gate-theta2` pins `rpTopology` to the canonical restricted-product topology at
producer boundaries. -/
structure CoverPackage (D : FieldData F) {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (H : HilbertData F) (A : AddCharData F) where
  loc : ∀ v : FinPlace F, FinLocalCover D H v
  tame : ∀ v : FinPlace F, v ∉ S.Sf → TameSplitting (loc v)
  tc : ThetaCover D S H A
  /-- local embeddings `L_v → G` (images commute for distinct places) -/
  emb : ∀ v : FinPlace F, (loc v).L →* tc.G
  emb_inj : ∀ v, Function.Injective (emb v)
  emb_z : ∀ v ζ, emb v ((loc v).z ζ) = tc.z ζ
  emb_n : ∀ v, v ∉ S.Sf → ∀ x, emb v ((loc v).n x) = tc.n v x
  emb_a : ∀ v, v ∉ S.Sf → ∀ y, emb v ((loc v).a y) = tc.a v y
  emb_w : ∀ v, v ∉ S.Sf → emb v (loc v).w = tc.w v
  emb_nbar : ∀ v, v ∉ S.Sf → ∀ x, emb v ((loc v).nbar x) = tc.nbar v x
  emb_Kext : ∀ v (hv : v ∉ S.Sf), ∀ k ∈ (tame v hv).Kmax, emb v k ∈ tc.Kext
  emb_comm : ∀ v v', v ≠ v' → ∀ g h, emb v g * emb v' h = emb v' h * emb v g
  /-- the restricted product before dividing by `N0`, with its components -/
  RP : Type
  [rpGrp : Group RP]
  q : RP →* tc.G
  q_surj : Function.Surjective q
  compF : ∀ v : FinPlace F, RP →* (loc v).L
  compC : InfinitePlace F → RP →* PGL2 ℂ
  /-- The restricted-product topology before quotienting by the central phases. -/
  rpTopology : TopologicalSpace RP
  rpTopGroup : @IsTopologicalGroup RP rpTopology rpGrp
  q_quotient : @IsQuotientMap RP tc.G rpTopology tc.topology q
  compF_cont : ∀ v, @Continuous RP (loc v).L rpTopology (loc v).top (compF v)
  nS_cont : @Continuous (Multiplicative S.FS) tc.G inferInstance tc.topology tc.nS
  aS_cont : @Continuous S.FSˣ tc.G inferInstance tc.topology tc.aS
  /-- an element of `RP` is determined by its components -/
  comp_ext : ∀ x y : RP, (∀ v, compF v x = compF v y) → (∀ w, compC w x = compC w y) → x = y
  /-- restricted-product condition: almost all components in the tame compacts -/
  comp_restricted : ∀ x : RP, Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf, compF v x ∉ (tame v hv).Kmax}
  /-- `q x = q y` iff the components agree up to central `μ3` phases with product `1` -/
  q_eq : ∀ x y : RP, q x = q y ↔ ∃ ζ : FinPlace F → rootsOfUnity 3 ℂ,
    (Function.mulSupport ζ).Finite ∧ (∏ᶠ v, ζ v) = 1 ∧
      (∀ v, compF v x = (loc v).z (ζ v) * compF v y) ∧ ∀ w, compC w x = compC w y
  /-- rational elements: component `(γ, 1)` at every place -/
  ratRP : GL (Fin 2) F → RP
  q_ratRP : ∀ γ, q (ratRP γ) = tc.rat γ
  compF_ratRP : ∀ v γ, compF v (ratRP γ) =
    (loc v).sec (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ)
  compC_ratRP : ∀ w γ, compC w (ratRP γ) =
    QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ)
  /-- Insert one local element into the restricted product. -/
  incl : ∀ v : FinPlace F, (loc v).L →* RP
  incl_compF : ∀ v g, compF v (incl v g) = g
  incl_compF_other : ∀ v v', v ≠ v' → ∀ g, compF v' (incl v g) = 1
  incl_compC : ∀ v g w, compC w (incl v g) = 1
  q_incl : ∀ v g, q (incl v g) = emb v g
  /-- Any compatible local components with tame support come from the restricted product. -/
  comp_surj : ∀ (lf : ∀ v : FinPlace F, (loc v).L) (lc : InfinitePlace F → PGL2 ℂ),
    Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf, lf v ∉ (tame v hv).Kmax} →
      ∃ x : RP, (∀ v, compF v x = lf v) ∧ ∀ w, compC w x = lc w
  emb_Gloc : ∀ v, v ∉ S.Sf → (emb v).range = tc.Gloc v
  emb_Kext_iff : ∀ v (hv : v ∉ S.Sf) g,
    emb v g ∈ tc.Kext ↔ g ∈ (tame v hv).Kmax
  /-- the S-part restricted to a finite place `v ∈ S` is the local cover there -/
  emb_aS : ∀ v : S.Sf, ∀ y : (v.1.adicCompletion F)ˣ, ∃ yS : S.FSˣ,
    S.compU v yS = y ∧ (∀ v' : S.Sf, v' ≠ v → S.compU v' yS = 1) ∧ (∀ w, S.compC w yS = 1) ∧
    tc.aS yS = emb v.1 ((loc v.1).a y)
  /-- The global S-unipotent is represented by its local components. -/
  nS_components : ∀ u : S.FS, ∃ x : RP, q x = tc.nS (Multiplicative.ofAdd u) ∧
    (∀ v : FinPlace F, compF v x = if hv : v ∈ S.Sf then
      (loc v).n (Multiplicative.ofAdd (u.1 ⟨v, hv⟩)) else 1) ∧
    ∀ w, compC w x = QuotientGroup.mk (upperM ℂ (u.2 w))
  /-- The global S-torus is represented by its local components. -/
  aS_components : ∀ u : S.FSˣ, ∃ x : RP, q x = tc.aS u ∧
    (∀ v : FinPlace F, compF v x = if hv : v ∈ S.Sf then
      (loc v).a (S.compU ⟨v, hv⟩ u) else 1) ∧
    ∀ w, compC w x = QuotientGroup.mk (diagM ℂ (S.compC w u))
  /-- The global S-Weyl element is represented by its local components. -/
  wS_components : ∃ x : RP, q x = tc.wS ∧
    (∀ v : FinPlace F, compF v x = if v ∈ S.Sf then (loc v).w else 1) ∧
    ∀ w, compC w x = QuotientGroup.mk (weylM ℂ)
  /-- Every element of the exterior compact `Kext = Π_{v∉S} κ_v(PGL₂(O_v))` is represented by
  components in the tame maximal compacts outside `S`, trivial at the finite places of `S` and at
  the complex places (theta-iface amendment). -/
  Kext_components : ∀ k ∈ tc.Kext, ∃ x : RP, q x = k ∧
    (∀ v (hv : v ∉ S.Sf), compF v x ∈ (tame v hv).Kmax) ∧
    (∀ v, v ∈ S.Sf → compF v x = 1) ∧ ∀ w, compC w x = 1

attribute [instance] CoverPackage.rpGrp

variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}

/-- Archimedean central phases have already been absorbed into the common finite center
in this presentation, consistently with the existing `compC` and `q_eq` fields. -/
def LocalComponent (P : CoverPackage D S H A) : Place F → Type :=
  Sum.elim (fun v => (P.loc v).L) (fun _ => PGL2 ℂ)

instance localComponentTopology (P : CoverPackage D S H A) (p : Place F) :
    TopologicalSpace (LocalComponent P p) := by
  cases p with
  | inl v => exact (P.loc v).top
  | inr w => exact inferInstanceAs (TopologicalSpace (PGL2 ℂ))

/-- All components at S are unrestricted; exterior finite components use their actual
tame compact subgroups. -/
def referenceSubset (P : CoverPackage D S H A) : (p : Place F) → Set (LocalComponent P p)
  | .inl v => if hv : v ∉ S.Sf then ((P.tame v hv).Kmax : Set (P.loc v).L) else Set.univ
  | .inr _ => Set.univ

abbrev CanonicalRP (P : CoverPackage D S H A) :=
  RestrictedProduct (LocalComponent P) (referenceSubset P) cofinite

/-- This pins the topology, rather than merely naming a supplied group topology.
The algebraic component equivalence comes from `comp_ext`, `comp_restricted`, and
`comp_surj`; its homeomorphism property is the missing construction obligation. This is the
restricted-product topology correction from `sol-gate-theta2`. -/
def HasRestrictedProductTopology (P : CoverPackage D S H A) : Prop :=
  ∃ e : @Homeomorph P.RP (CanonicalRP P) P.rpTopology inferInstance,
    (∀ x v, e x (.inl v) = P.compF v x) ∧
    ∀ x w, e x (.inr w) = P.compC w x

/-- The component axioms identify the package's tuples with the canonical restricted product.
Continuity of this equivalence is a separate obligation of the global construction. -/
theorem coverPackage_components_equiv (P : CoverPackage D S H A) :
    ∃ e : P.RP ≃ CanonicalRP P,
      (∀ x v, e x (.inl v) = P.compF v x) ∧
      ∀ x w, e x (.inr w) = P.compC w x := by
  have he := TH_COVER.restrictedSum_componentEquiv S.Sf
    (fun v hv => ((P.tame v hv).Kmax : Set (P.loc v).L))
    (fun v x => P.compF v x) (fun w x => P.compC w x)
    P.comp_ext P.comp_restricted P.comp_surj
  have href :
      (TH_COVER.sumReference S.Sf (fun v hv => ((P.tame v hv).Kmax : Set (P.loc v).L)) :
        (p : Place F) → Set (LocalComponent P p)) = referenceSubset P := by
    funext p
    cases p with
    | inl v =>
      by_cases hv : v ∉ S.Sf <;>
        simp [TH_COVER.sumReference, referenceSubset, LocalComponent, hv]
    | inr w => rfl
  rw [href] at he
  exact he

/-- The effective exterior coefficient agrees with the actual local torus product. -/
private theorem cover_local_effectiveLaw (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (L : FinLocalCover D H v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (x y : (v.adicCompletion F)ˣ) :
    ∃ ζ : rootsOfUnity 3 ℂ, ((ζ : ℂˣ) : ℂ) = extCocycle D v x y ∧
      L.a x * L.a y = L.z ζ * L.a (x * y) := by
  exact ⟨muThree D (H.hilb v x y),
    ArtinPrimitiveRoots.Proofs.th_cover_sol.muThree_hilb_eq_extCocycle D H v hv x y,
    L.a_mul x y⟩

/-- Local factors chosen before constructing their adelic quotient. -/
private structure CoverLocalFamily (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) where
  loc : ∀ v : FinPlace F, FinLocalCover D H v
  tame : ∀ v : FinPlace F, v ∉ S.Sf → TameSplitting (loc v)

private def coverFamilyReference (C : CoverLocalFamily D S H) (v : FinPlace F) :
    Subgroup (C.loc v).L :=
  if hv : v ∉ S.Sf then (C.tame v hv).Kmax else ⊤

private theorem coverFamilyReference_open (C : CoverLocalFamily D S H) (v : FinPlace F) :
    IsOpen (coverFamilyReference C v : Set (C.loc v).L) := by
  by_cases hv : v ∉ S.Sf
  · simpa [coverFamilyReference, hv] using (C.tame v hv).open_
  · simp [coverFamilyReference, hv]

/-- The canonical tuple and quotient foundation for the global producer. -/
private structure CoverQuotientBase (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) where
  family : CoverLocalFamily D S H
  quotient : ArtinPrimitiveRoots.Proofs.th_cover_sol.RestrictedCentral.CentralQuotient
    (H := fun _ : InfinitePlace F => PGL2 ℂ) (coverFamilyReference family)
    (fun v => (family.loc v).z)

private theorem exists_coverQuotientBase (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (hSt : ∀ v, SteinbergAt H v) :
    Nonempty (CoverQuotientBase D S H) := by
  classical
  choose loc hloc using fun v => exists_finLocalCover D H v (hSt v)
  let C : CoverLocalFamily D S H := {
    loc := loc
    tame := fun v hv => Classical.choice (hloc v (fun h => hv (S.over6 v h)))
  }
  obtain ⟨Q⟩ :=
    ArtinPrimitiveRoots.Proofs.th_cover_sol.RestrictedCentral.exists_centralQuotient
      (H := fun _ : InfinitePlace F => PGL2 ℂ)
      (coverFamilyReference C) (coverFamilyReference_open C)
      (fun v => (C.loc v).z) (fun v => (C.loc v).z_inj)
      (fun v => (C.loc v).z_central)
  exact ⟨{ family := C, quotient := Q }⟩

/-- Global reciprocity removes the central discrepancy of rational section tuples. -/
private theorem global_kpCocycle_product (D : FieldData F) (H : HilbertData F)
    (g h : GL (Fin 2) F) :
    (Function.mulSupport fun v : FinPlace F => kpCocycle D H v
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g)
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) h)).Finite ∧
    (∏ᶠ v : FinPlace F, kpCocycle D H v
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g)
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) h)) = 1 := by
  classical
  let X := ArtinPrimitiveRoots.Proofs.th_cover_sol.secondRowUnit (K := F)
  have hx (v : FinPlace F) (k : GL (Fin 2) F) :
      xU v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) k) =
        toLoc v (X k) := by
    change ArtinPrimitiveRoots.Proofs.th_cover_sol.secondRowUnit
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) k) =
        Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom (X k)
    exact (ArtinPrimitiveRoots.Proofs.th_cover_sol.map_secondRowUnit _ k).symm
  have hd (v : FinPlace F) (k : GL (Fin 2) F) :
      detU v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) k) =
        toLoc v (Matrix.GeneralLinearGroup.det k) := by
    exact Matrix.GeneralLinearGroup.map_det _ k
  let p : rootsOfUnity 6 F →* rootsOfUnity 3 ℂ := {
    toFun := muThree D
    map_one' := muThree_one D
    map_mul' := muThree_mul D
  }
  let a : Fˣ := X (g * h) / (X h * Matrix.GeneralLinearGroup.det g)
  let b : Fˣ := X (g * h) / X g
  let r : FinPlace F → rootsOfUnity 6 F := fun v => H.hilb v (toLoc v a) (toLoc v b)
  let s : FinPlace F → rootsOfUnity 6 F := fun v =>
    H.hilb v (toLoc v (Matrix.GeneralLinearGroup.det g))
      (toLoc v (Matrix.GeneralLinearGroup.det h))
  obtain ⟨hr, hrprod⟩ := H.product_formula a b
  obtain ⟨hs, hsprod⟩ := H.product_formula
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.det h)
  have hpr : Function.HasFiniteMulSupport (fun v => p (r v)) :=
    Function.HasFiniteMulSupport.fun_comp hr p.map_one
  have hps : Function.HasFiniteMulSupport (fun v => p (s v)) :=
    Function.HasFiniteMulSupport.fun_comp hs p.map_one
  have hformula :
      (fun v : FinPlace F => kpCocycle D H v
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g)
        (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) h)) =
      (fun v => p (r v) * p (s v)) := by
    funext v
    simp only [kpCocycle, ← Matrix.GeneralLinearGroup.map_mul, hx, hd]
    dsimp [p, r, s, a, b]
    simp only [map_div, map_mul]
  rw [hformula]
  refine ⟨Function.HasFiniteMulSupport.mul hpr hps, ?_⟩
  calc
    (∏ᶠ v, p (r v) * p (s v)) = (∏ᶠ v, p (r v)) * (∏ᶠ v, p (s v)) :=
      finprod_mul_distrib hpr hps
    _ = p (∏ᶠ v, r v) * p (∏ᶠ v, s v) := by
      rw [p.map_finprod hr, p.map_finprod hs]
    _ = 1 := by rw [hrprod, hsprod, p.map_one, mul_one]

/-- **P-COVER main theorem.** Under the Steinberg relation at every finite place, the adelic
cover exists with the component compatibility identities of C2 in `sol-gate-theta`. The
`sol-gate-theta2` correction also certifies its canonical restricted-product topology. -/
theorem exists_coverPackage (D : FieldData F) {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (H : HilbertData F) (A : AddCharData F)
    (hSt : ∀ v, SteinbergAt H v) : ∃ P : CoverPackage D S H A, HasRestrictedProductTopology P := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
