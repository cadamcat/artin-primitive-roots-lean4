import ArtinPrimitiveRoots.A1.ThetaInterface


/-!
# P-COVER (route C): the cubic cover of `PGL₂` — top-node statements (design draft)

Blueprint: `research/blueprint/A1-P-COVER.md`. Imports the frozen A1 interface only.

The section `Core` is the **shared theta core**: it is copied verbatim into every route-C draft
(`A1-P-TORUS-IND.lean`, `A1-P-LOCAL-INT.lean`, …) and is to be frozen together with P-COVER.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
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
    ext b
    rw [hilb_one_left H v b, muThree_one]
  map_mul' := by
    intro a a'
    ext b
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

/-- **cov:cocycle**: the KP formula is a 2-cocycle (Kubota 1967 / KP §0.1 replaced by the
generator argument of the blueprint). -/
theorem kpCocycle_cocycle (hSt : SteinbergAt H v) (g h k : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v g h * kpCocycle D H v (g * h) k =
      kpCocycle D H v g (h * k) * kpCocycle D H v h k := by
  sorry

/-- **cov:center**: for `c = 2` the scalar section is central and multiplicative. -/
theorem kpCocycle_scalar (hSt : SteinbergAt H v) (c : (v.adicCompletion F)ˣ)
    (g : GL (Fin 2) (v.adicCompletion F)) :
    kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) g =
      kpCocycle D H v g (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  rw [kpCocycle_pairing, kpCocycle_pairing]
  simp only [xU_scalar_left, xU_scalar_right, xU_scalar, detU_scalar]
  have h₁ : (c * xU v g) / (xU v g * c ^ 2) = c⁻¹ := by abel
  have h₂ : (c * xU v g) / c = xU v g := by abel
  have h₃ : (c * xU v g) / (c * detU v g) = xU v g / detU v g := by abel
  have h₄ : (c * xU v g) / xU v g = c := by abel
  rw [h₁, h₂, h₃, h₄]
  rw [kpPairing_inv_left, kpPairing_inverse_swap, kpPairing_pow_left,
    kpPairing_square_swap, kpPairing_div_left, kpPairing_pow_right]
  group

theorem kpCocycle_scalar_scalar (hSt : SteinbergAt H v) (c c' : (v.adicCompletion F)ˣ) :
    kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c') = 1 := by
  rw [kpCocycle_pairing]
  simp only [xU_scalar_left, xU_scalar, detU_scalar]
  have h₁ : (c * c') / (c' * c ^ 2) = c⁻¹ := by abel
  have h₂ : (c * c') / c = c' := by abel
  rw [h₁, h₂, kpPairing_inv_left, kpPairing_pow_left, kpPairing_pow_right]
  let z := kpPairing D H v c c'
  change z⁻¹ * (z ^ 2) ^ 2 = 1
  calc
    z⁻¹ * (z ^ 2) ^ 2 = z⁻¹ * z ^ 4 := by
      congr 1
      rw [← pow_mul]
      rw [show 2 * 2 = 4 by norm_num]
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
are the images of the local covers. -/
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
  /-- the S-part restricted to a finite place `v ∈ S` is the local cover there -/
  emb_aS : ∀ v : S.Sf, ∀ y : (v.1.adicCompletion F)ˣ, ∃ yS : S.FSˣ,
    S.compU v yS = y ∧ (∀ v' : S.Sf, v' ≠ v → S.compU v' yS = 1) ∧ (∀ w, S.compC w yS = 1) ∧
    tc.aS yS = emb v.1 ((loc v.1).a y)

attribute [instance] CoverPackage.rpGrp

/-- **P-COVER main theorem.** Under the Steinberg relation at every finite place, the adelic
cover exists. -/
theorem exists_coverPackage (D : FieldData F) {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (H : HilbertData F) (A : AddCharData F)
    (hSt : ∀ v, SteinbergAt H v) : Nonempty (CoverPackage D S H A) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
