import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import ArtinPrimitiveRoots.A1.ThetaInterface


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

/-- **cov:local-cover** (top, local): at every finite place there is a local cover built from
`kpCocycle` (as `GL₂ × μ3` modulo the scalar section) with the interface `FinLocalCover`, and at
every `v ∤ 6` a tame splitting. -/
theorem exists_finLocalCover (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    ∃ L : FinLocalCover D H v, (6 : 𝓞 F) ∉ v.asIdeal → Nonempty (TameSplitting L) := by
  sorry

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

/-- **P-COVER main theorem.** Under the Steinberg relation at every finite place, the adelic
cover exists with the component compatibility identities of C2 in `sol-gate-theta`. The
`sol-gate-theta2` correction also certifies its canonical restricted-product topology. -/
theorem exists_coverPackage (D : FieldData F) {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (H : HilbertData F) (A : AddCharData F)
    (hSt : ∀ v, SteinbergAt H v) : ∃ P : CoverPackage D S H A, HasRestrictedProductTopology P := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
