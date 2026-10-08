import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-TORUS-IND -/

section Torus

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The fixed uniformizer of `K_v` (image of the global `unif v`). -/
def unifLoc (v : FinPlace F) : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))

/-- Local units `O_v^×` as a predicate on `K_v^×`. -/
def IsLocUnit (v : FinPlace F) (u : (v.adicCompletion F)ˣ) : Prop :=
  (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F

/-- Commutator pairing of the covering torus: `[a(x), a(y)] = z(⟨x,y⟩)`. -/
def torusPairing (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) : rootsOfUnity 3 ℂ :=
  muThree D (H.hilb v x y) * (muThree D (H.hilb v y x))⁻¹

private theorem muThree_pow_three_eq_one (D : FieldData F) (ζ : rootsOfUnity 6 F) :
    muThree D (ζ ^ 3) = 1 := by
  have h6 : (ζ : Fˣ) ^ 6 = 1 := (mem_rootsOfUnity 6 (ζ : Fˣ)).mp ζ.2
  apply rootsOfUnity.coe_injective
  change D.σ0 (((((ζ ^ 3) ^ 2 : rootsOfUnity 6 F) : Fˣ) : F)) = 1
  have hz : (((ζ ^ 3) ^ 2 : rootsOfUnity 6 F) : Fˣ) = 1 := by
    change ((ζ : Fˣ) ^ 3) ^ 2 = 1
    calc
      ((ζ : Fˣ) ^ 3) ^ 2 = (ζ : Fˣ) ^ (3 * 2) := by rw [pow_mul]
      _ = (ζ : Fˣ) ^ 6 := by norm_num
      _ = 1 := h6
  rw [hz]
  simp

/-- **tor:pairing**: the commutator formula. -/
theorem torus_commutator (L : FinLocalCover D H v) (x y : (v.adicCompletion F)ˣ) :
    L.a x * L.a y * (L.a x)⁻¹ * (L.a y)⁻¹ = L.z (torusPairing D H v x y) := by
  let cxy := muThree D (H.hilb v x y)
  let cyx := muThree D (H.hilb v y x)
  have hc : L.z cxy * (L.z cyx)⁻¹ = L.z (cxy * cyx⁻¹) := by
    simp [cxy, cyx]
  have hswap : L.a x * L.a y = L.z (cxy * cyx⁻¹) * (L.a y * L.a x) := by
    calc
      L.a x * L.a y = L.z cxy * L.a (x * y) := L.a_mul x y
      _ = (L.z cxy * (L.z cyx)⁻¹) * (L.z cyx * L.a (x * y)) := by group
      _ = (L.z cxy * (L.z cyx)⁻¹) * (L.z cyx * L.a (y * x)) := by rw [mul_comm x y]
      _ = L.z (cxy * cyx⁻¹) * (L.a y * L.a x) := by
        rw [hc, L.a_mul y x]
  calc
    L.a x * L.a y * (L.a x)⁻¹ * (L.a y)⁻¹ =
        (L.z (cxy * cyx⁻¹) * (L.a y * L.a x)) * (L.a x)⁻¹ * (L.a y)⁻¹ := by rw [hswap]
    _ = L.z (cxy * cyx⁻¹) := by group
    _ = L.z (torusPairing D H v x y) := by rfl

/-- **tor:pairing** (nondegeneracy on `K^×/K^{×3}`). -/
theorem torusPairing_nondeg (x : (v.adicCompletion F)ˣ)
    (hx : ∀ y, torusPairing D H v x y = 1) : ∃ t : (v.adicCompletion F)ˣ, x = t ^ 3 := by
  have hfour (y : (v.adicCompletion F)ˣ) : (H.hilb v x y) ^ 4 = 1 := by
    have hskew := H.skew v x y
    rw [mul_comm] at hskew
    have hyx : H.hilb v y x = (H.hilb v x y)⁻¹ :=
      eq_inv_of_mul_eq_one_left hskew
    let a : F := (((H.hilb v x y : rootsOfUnity 6 F) : Fˣ) : F)
    have hval : D.σ0 a ^ 2 * D.σ0 a ^ 2 = 1 := by
      have h := congrArg (fun z : rootsOfUnity 3 ℂ => ((z : ℂˣ) : ℂ)) (hx y)
      simpa [torusPairing, hyx, muThree, a, ← map_pow] using h
    apply rootsOfUnity.coe_injective
    apply D.σ0.injective
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]
    calc
      D.σ0 (a ^ 4) = (D.σ0 a) ^ 4 := by rw [map_pow]
      _ = D.σ0 a ^ 2 * D.σ0 a ^ 2 := by ring
      _ = D.σ0 1 := by simpa [a] using hval
  have hsq (y : (v.adicCompletion F)ˣ) : (H.hilb v x y) ^ 2 = 1 := by
    let z := H.hilb v x y
    have h6 : z ^ 6 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 6 (z : Fˣ)).mp z.2
    have h4 : z ^ 4 = 1 := hfour y
    calc
      z ^ 2 = z ^ 6 * (z ^ 4)⁻¹ := by group
      _ = 1 := by rw [h6, h4]; simp
  have hnondeg : ∀ y, H.hilb v (x ^ 2) y = 1 := by
    intro y
    calc
      H.hilb v (x ^ 2) y = H.hilb v x y * H.hilb v x y := by
        simpa [pow_two] using H.mul_left v x x y
      _ = 1 := by simpa [pow_two] using hsq y
  obtain ⟨c, hc⟩ := H.nondeg v (x ^ 2) hnondeg
  let q : (v.adicCompletion F)ˣ := x / c ^ 3
  have hq : q ^ 2 = 1 := by
    dsimp [q]
    rw [div_pow, hc]
    rw [div_eq_mul_inv, show (c ^ 3) ^ 2 = c ^ 6 by rw [← pow_mul]]
    exact mul_inv_cancel _
  have hqval : ((q : v.adicCompletion F) ^ 2) = 1 := by
    have h := congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) hq
    simpa using h
  rcases sq_eq_one_iff.mp hqval with hqpos | hqneg
  · have hqeq : q = 1 := Units.ext hqpos
    refine ⟨c, ?_⟩
    calc
      x = q * c ^ 3 := by simp [q]
      _ = c ^ 3 := by rw [hqeq]; simp
  · have hqeq : q = -1 := Units.ext hqneg
    refine ⟨-c, ?_⟩
    calc
      x = q * c ^ 3 := by simp [q]
      _ = (-1) * c ^ 3 := by rw [hqeq]
      _ = (-c) ^ 3 := by
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        ring

/-- **tor:center**: `t ↦ a(t³)` is a homomorphism into the centre of the covering torus. -/
theorem a_cube_mul (L : FinLocalCover D H v) (s t : (v.adicCompletion F)ˣ) :
    L.a (s ^ 3) * L.a (t ^ 3) = L.a ((s * t) ^ 3) ∧ ∀ y, L.a (s ^ 3) * L.a y = L.a y * L.a (s ^ 3) := by
  have hmul (x y : (v.adicCompletion F)ˣ) :
      H.hilb v (x ^ 3) (y ^ 3) = (H.hilb v x y) ^ 9 := by
    simp [pow_succ, H.mul_left, H.mul_right] <;> ac_rfl
  have hleft (x y : (v.adicCompletion F)ˣ) :
      H.hilb v (x ^ 3) y = (H.hilb v x y) ^ 3 := by
    simp [pow_succ, H.mul_left]
  have hright (x y : (v.adicCompletion F)ˣ) :
      H.hilb v x (y ^ 3) = (H.hilb v x y) ^ 3 := by
    simp [pow_succ, H.mul_right]
  have hcube (ζ : rootsOfUnity 6 F) : muThree D (ζ ^ 9) = 1 := by
    rw [show ζ ^ 9 = (ζ ^ 3) ^ 3 by group]
    exact muThree_pow_three_eq_one D (ζ ^ 3)
  constructor
  · have hs : muThree D (H.hilb v (s ^ 3) (t ^ 3)) = 1 := by
      rw [hmul]
      exact hcube (H.hilb v s t)
    calc
      L.a (s ^ 3) * L.a (t ^ 3) =
          L.z (muThree D (H.hilb v (s ^ 3) (t ^ 3))) * L.a (s ^ 3 * t ^ 3) :=
        L.a_mul (s ^ 3) (t ^ 3)
      _ = L.a ((s * t) ^ 3) := by rw [hs]; simp [mul_pow]
  · intro y
    have hs : muThree D (H.hilb v (s ^ 3) y) = 1 := by
      rw [hleft]
      exact muThree_pow_three_eq_one D (H.hilb v s y)
    have hy : muThree D (H.hilb v y (s ^ 3)) = 1 := by
      rw [hright]
      exact muThree_pow_three_eq_one D (H.hilb v y s)
    have hpair : torusPairing D H v (s ^ 3) y = 1 := by
      simp [torusPairing, hs, hy]
    have hc := torus_commutator (L := L) (x := s ^ 3) (y := y)
    rw [hpair] at hc
    have hcomm : L.a (s ^ 3) * L.a y = L.a y * L.a (s ^ 3) := by
      calc
        L.a (s ^ 3) * L.a y =
            (L.a (s ^ 3) * L.a y * (L.a (s ^ 3))⁻¹ * (L.a y)⁻¹) *
              (L.a y * L.a (s ^ 3)) := by group
        _ = L.a y * L.a (s ^ 3) := by rw [hc]; simp
    exact hcomm

/-- **def:tor-rep**: a genuine smooth representation of the covering torus with unitary central
character `z(ζ)a(t³) ↦ ζ`, given as a projective representation of `K^×` with the torus cocycle. -/
structure TorusRep (D : FieldData F) (H : HilbertData F) (v : FinPlace F) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [nsp : NormedSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  σa : (v.adicCompletion F)ˣ → V →ₗ[ℂ] V
  σa_one : σa 1 = LinearMap.id
  σa_mul : ∀ x y, (σa x).comp (σa y) = ((muThree D (H.hilb v x y) : ℂˣ) : ℂ) • σa (x * y)
  σa_cube : ∀ t, σa (t ^ 3) = LinearMap.id
  σa_smooth : ∃ m : ℕ, 0 < m ∧ ∀ u : (v.adicCompletion F)ˣ,
    ((u : v.adicCompletion F) - 1) ∈ ball v m → σa u = LinearMap.id
  /-- `σa` takes finitely many values (it factors through `K^×/(K^{×3}(1+𝔭^m))` up to `μ3`);
  this gives the uniform bounds used in P-LOCAL-INT -/
  σa_finite : (Set.range σa).Finite

attribute [instance] TorusRep.nacg TorusRep.nsp TorusRep.fd

private theorem hilb_one_left (H : HilbertData F) (v : FinPlace F)
    (y : (v.adicCompletion F)ˣ) : H.hilb v 1 y = 1 := by
  let z := H.hilb v 1 y
  have h : z * 1 = z * z := by
    simpa [z] using (H.mul_left v 1 1 y)
  exact (mul_left_cancel h).symm

private theorem hilb_one_right (H : HilbertData F) (v : FinPlace F)
    (x : (v.adicCompletion F)ˣ) : H.hilb v x 1 = 1 := by
  let z := H.hilb v x 1
  have h : z * 1 = z * z := by
    simpa [z] using (H.mul_right v x 1 1)
  exact (mul_left_cancel h).symm

private theorem hilb_inv_left (H : HilbertData F) (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) :
    H.hilb v (x⁻¹) y = (H.hilb v x y)⁻¹ := by
  let a := H.hilb v x y
  let b := H.hilb v (x⁻¹) y
  have hab : a * b = 1 := by
    have h := H.mul_left v x x⁻¹ y
    rw [mul_inv_cancel, hilb_one_left H v y] at h
    exact h.symm
  calc
    b = 1 * b := by simp
    _ = (a⁻¹ * a) * b := by simp
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ := by rw [hab]; simp

private theorem hilb_inv_right (H : HilbertData F) (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) :
    H.hilb v x (y⁻¹) = (H.hilb v x y)⁻¹ := by
  let a := H.hilb v x y
  let b := H.hilb v x (y⁻¹)
  have hab : a * b = 1 := by
    have h := H.mul_right v x y y⁻¹
    rw [mul_inv_cancel, hilb_one_right H v x] at h
    exact h.symm
  calc
    b = 1 * b := by simp
    _ = (a⁻¹ * a) * b := by simp
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ := by rw [hab]; simp

private theorem hilb_inv_inv (H : HilbertData F) (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) :
    H.hilb v (x⁻¹) (y⁻¹) = H.hilb v x y := by
  rw [hilb_inv_left H v x (y⁻¹), hilb_inv_right H v x y, inv_inv]

/-- **def:weyl-rep**: the Weyl conjugate `y ↦ σa(y⁻¹)` (same cocycle, since `hilb(x⁻¹,y⁻¹) = hilb(x,y)`);
`I(T.weyl, -s)` is the target of the intertwining operator (P-LOCAL-INT). -/
def TorusRep.weyl (T : TorusRep D H v) : TorusRep D H v where
  V := T.V
  σa y := T.σa y⁻¹
  σa_one := by simpa using T.σa_one
  σa_mul := by
    intro x y
    simpa [hilb_inv_inv H v x y, mul_comm] using T.σa_mul x⁻¹ y⁻¹
  σa_cube := by intro t; simpa [← inv_pow] using T.σa_cube t⁻¹
  σa_smooth := by
    obtain ⟨m, hm, hsmooth⟩ := T.σa_smooth
    refine ⟨m, hm, ?_⟩
    intro u hu
    apply hsmooth u⁻¹
    have huVal : Valued.v ((u : v.adicCompletion F) - 1) < 1 := by
      have hball : Valued.v ((u : v.adicCompletion F) - 1) ≤ WithZero.exp (-(m : ℤ)) := hu
      have hexp : WithZero.exp (-(m : ℤ)) < 1 := by
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        exact_mod_cast (neg_lt_zero.mpr (Nat.cast_pos.mpr hm))
      exact lt_of_le_of_lt hball hexp
    have huNorm : Valued.v (u : v.adicCompletion F) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right
        (v := (Valued.v : Valuation (v.adicCompletion F) _))
        (x := (u : v.adicCompletion F) - 1) (y := (1 : v.adicCompletion F))
        (by simpa using huVal)
      simpa [sub_add_cancel] using h
    have hidentity : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
        -(((u : v.adicCompletion F) - 1) * (u : v.adicCompletion F)⁻¹) := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp
      ring
    have huInvVal : Valued.v (((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) =
        Valued.v ((u : v.adicCompletion F) - 1) := by
      rw [hidentity, Valuation.map_neg, Valuation.map_mul, map_inv₀, huNorm]
      simp
    change Valued.v (((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
      WithZero.exp (-(m : ℤ))
    rw [huInvVal]
    exact hu
  σa_finite := by
    change (Set.range (fun y => T.σa y⁻¹)).Finite
    have hrange : Set.range (fun y => T.σa y⁻¹) = Set.range T.σa := by
      ext f
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y⁻¹, by simp⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y⁻¹, by simp⟩
    rw [hrange]
    exact T.σa_finite

/-- **tor:tame-basis**: at a tame place, the explicit model `e_0, e_1, e_2` with
`σ(a(ϖ^j u)) e_k = ρ(u)^{j+2k} e_{k+j}`, `ρ = localChi²` (10:250–275, unitary normalization). -/
structure TameTorusBasis (T : TorusRep D H v) where
  e : ZMod 3 → T.V
  linIndep : LinearIndependent ℂ e
  spans : Submodule.span ℂ (Set.range e) = ⊤
  act : ∀ (j : ℤ) (u : (v.adicCompletion F)ˣ), IsLocUnit v u → ∀ k : ZMod 3,
    T.σa (unifLoc v ^ j * u) (e k) = (localChi D v u) ^ (2 * (j + 2 * (k.val : ℤ))) • e (k + (j : ZMod 3))

/-- **tor:rep** (top): at every finite place a torus representation exists, of dimension
`√[K^×:K^{×3}]`; at `v ∤ 6` one with the tame basis. The nontrivial-carrier clause is
installed per `sol-thin-thlocal`, since `GlobalDatum.lam_ne` excludes the zero space. -/
theorem exists_torusRep (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    ∃ T : TorusRep D H v, Nontrivial T.V ∧
      ((6 : 𝓞 F) ∉ v.asIdeal → Nonempty (TameTorusBasis T)) := by
  sorry

/-- **tor:K-fixed**: at a tame place, the `a(O^×)`-fixed vectors of `V` are the multiples of `e_0`. -/
theorem tame_unitFixed (T : TorusRep D H v) (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (x : T.V) (hx : ∀ u, IsLocUnit v u → T.σa u x = x) : ∃ c : ℂ, x = c • B.e 0 := by
  sorry

/-- **def:weyl-basis**: `e^w_k := e_{-k}` is a tame basis of the Weyl conjugate `T.weyl`
(uses `localChi(u⁻¹) = localChi(u)⁻¹` and `localChi(u)^6 = 1` on local units). -/
def TameTorusBasis.weyl {T : TorusRep D H v} (B : TameTorusBasis T) : TameTorusBasis T.weyl where
  e k := B.e (-k)
  linIndep := by sorry
  spans := by sorry
  act := by sorry

/-- **def:ind**: sections of the normalized induced representation `I(σ, s)`:
`f(n(x) z(ζ) a(y) g) = ζ |y|^{1/2+s} σ(a(y)) f(g)`, right-invariant under some `Kc m`. -/
def IsSection (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) (f : L.L → T.V) : Prop :=
  (∀ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ) (g : L.L),
    f (L.n (Multiplicative.ofAdd x) * L.a y * g) = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (f g)) ∧
  (∀ ζ g, f (L.z ζ * g) = ((ζ : ℂˣ) : ℂ) • f g) ∧
  (∃ m, L.m0 ≤ m ∧ ∀ g, ∀ k ∈ L.Kc m, f (g * k) = f g)

/-- Right translation `(π(g)f)(h) = f(hg)`. -/
def rtr {G V : Type} [Mul G] (g : G) (f : G → V) : G → V := fun h => f (h * g)

/-- **ind:rtr**: sections are stable under right translation (`g⁻¹ Kc(m') g ⊆ Kc(m)` for large `m'`). -/
theorem IsSection.rtr {L : FinLocalCover D H v} {T : TorusRep D H v} {s : ℂ} {f : L.L → T.V}
    (hf : IsSection L T s f) (g : L.L) : IsSection L T s (rtr g f) := by
  sorry

/-- **ind:iwasawa** (tame): `L = B̃ · Kmax`. -/
theorem iwasawa_tame (L : FinLocalCover D H v) (τ : TameSplitting L) (g : L.L) :
    ∃ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ) (ζ : rootsOfUnity 3 ℂ) (k : L.L),
      k ∈ τ.Kmax ∧ g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by
  sorry

/-- **ind:spherical** (KP Lemma I.1.3 replaced): at a tame place there is a unique
`Kmax`-invariant section with `f°(1) = e_0`, and every `Kmax`-invariant section is a multiple. -/
theorem spherical_section (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) :
    ∃ f0 : L.L → T.V, IsSection L T s f0 ∧ f0 1 = B.e 0 ∧ (∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) ∧
      ∀ f : L.L → T.V, IsSection L T s f → (∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g) →
        ∃ c : ℂ, f = c • f0 := by
  sorry

/-- **def:ind-bigcell**: the big-cell section `f(n(x) z(ζ) a(y) w n(t)) = ζ|y|^{1/2+s} σ(a(y)) φ(t)`
for a locally constant compactly supported `φ : K → V`, zero off the big cell. -/
def bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (g : L.L) : T.V :=
  if h : ∃ (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
      (t : v.adicCompletion F),
      g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)
  then ((h.choose_spec.choose : rootsOfUnity 3 ℂ) : ℂˣ) •
        ((absFin v h.choose_spec.choose_spec.choose : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa h.choose_spec.choose_spec.choose (φ h.choose_spec.choose_spec.choose_spec.choose)
  else 0

/-- **ind:bigcell-section**: `bigCell φ` is a section when `φ` is locally constant with compact
support (the decomposition in the big cell is unique). -/
theorem bigCell_isSection (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    IsSection L T s (bigCell L T s φ) := by
  sorry

/-- **ind:bigcell-apply**: the value of a big-cell section on the big cell (uniqueness of the
decomposition `n(x) z(ζ) a(y) w n(t)`), and its vanishing on the small cell `B̃`. -/
theorem bigCell_apply (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)) =
      ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
  sorry

theorem bigCell_borel (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := by
  sorry

end Torus

/-! ## Complex places -/

/-- Sections of the spherical principal series of `PGL₂(ℂ)` with parameter `s` (normalized
absolute value `|y|_ℂ = |y|²`): `f(n(x) a(y) g) = |y|_ℂ^{1/2+s} f(g)`, smooth. -/
def IsSectionC (s : ℂ) (f : PGL2 ℂ → ℂ) : Prop :=
  ∀ (x : ℂ) (y : ℂˣ) (g : PGL2 ℂ),
    f (QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ y) * g) =
      ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) * f g

/-- **ind:complex-spherical** (03:316–318): `f°(g) = (|det g| / (|g₂₁|²+|g₂₂|²))^{1+2s}` is the
spherical section (invariant under `PU(2)`, value 1 at 1). -/
def sphericalC (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  ((‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) : ℝ) : ℂ) ^
    (1 + 2 * s)

theorem sphericalC_isSection (s : ℂ) :
    ∃ f : PGL2 ℂ → ℂ, IsSectionC s f ∧ ∀ g : GL (Fin 2) ℂ, f (QuotientGroup.mk g) = sphericalC s g := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
