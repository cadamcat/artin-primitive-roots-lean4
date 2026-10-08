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

private theorem muThree_sq_one (D : FieldData F) (ζ : rootsOfUnity 6 F)
    (hζ : ζ ^ 2 = 1) : muThree D ζ = 1 := by
  apply rootsOfUnity.coe_injective
  change D.σ0 ((((ζ ^ 2 : rootsOfUnity 6 F) : Fˣ) : F)) = 1
  rw [hζ]
  simp

private theorem torusRep_sigma_inv (T : TorusRep D H v) (x : (v.adicCompletion F)ˣ) :
    (T.σa x⁻¹).comp (T.σa x) = LinearMap.id := by
  let z := H.hilb v x x
  have hz : z ^ 2 = 1 := by simpa [z, pow_two] using H.skew v x x
  have hzinv : z⁻¹ = z := by
    calc
      z⁻¹ = z⁻¹ * 1 := by simp
      _ = z⁻¹ * (z * z) := by rw [← pow_two, hz]
      _ = z := by group
  have hcoeff : muThree D (H.hilb v (x⁻¹) x) = 1 := by
    rw [hilb_inv_left H v x x, hzinv]
    exact muThree_sq_one D z hz
  have h := T.σa_mul x⁻¹ x
  rw [hcoeff] at h
  simpa [T.σa_one] using h

private theorem torusRep_sigma_injective (T : TorusRep D H v) (x : (v.adicCompletion F)ˣ) :
    Function.Injective (T.σa x) := by
  intro a b hab
  have h := congrArg (T.σa x⁻¹) hab
  have hinv := congrArg (fun f : T.V →ₗ[ℂ] T.V => f a) (torusRep_sigma_inv T x)
  have hinv' : T.σa x⁻¹ (T.σa x a) = a := by
    simpa [LinearMap.comp_apply] using hinv
  rw [hinv'] at h
  have hinvB : T.σa x⁻¹ (T.σa x b) = b := by
    have hB := congrArg (fun f : T.V →ₗ[ℂ] T.V => f b) (torusRep_sigma_inv T x)
    simpa [LinearMap.comp_apply] using hB
  rw [hinvB] at h
  exact h

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

private theorem chi_six_of_residue (D : FieldData F) (v : FinPlace F) (x : F)
    (hx : residue v x ≠ 0) : chi D v x ^ (6 : ℕ) = 1 := by
  have h := congrArg Units.val
    ((mem_rootsOfUnity 6 (chiAlg v x : (𝓞 F)ˣ)).1 (chiAlg v x).property)
  rw [chi, if_neg hx, ← map_pow, ← map_pow]
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using
    congrArg (fun a : 𝓞 F => D.σ0 (algebraMap (𝓞 F) F a)) h

private theorem localChi_six_of_nezero (D : FieldData F) (v : FinPlace F)
    (u : (v.adicCompletion F)ˣ) (hu : localChi D v u ≠ 0) : localChi D v u ^ (6 : ℕ) = 1 := by
  classical
  by_cases h : ∃ a : 𝓞 F, a ∉ v.asIdeal ∧
      Valued.v ((u : v.adicCompletion F) - algebraMap F _ (algebraMap (𝓞 F) F a)) < 1
  · let a := h.choose
    have ha := h.choose_spec.1
    have heq : localChi D v u = chi D v (algebraMap (𝓞 F) F a) := by
      unfold localChi
      rw [dif_pos h]
    have hχ : chi D v (algebraMap (𝓞 F) F a) ≠ 0 := by
      rw [← heq]
      exact hu
    have hres : residue v (algebraMap (𝓞 F) F a) ≠ 0 := by
      intro hr
      exact hχ (by simp [chi, hr])
    rw [heq]
    exact chi_six_of_residue D v _ hres
  · have hzero : localChi D v u = 0 := by
      unfold localChi
      rw [dif_neg h]
    exact False.elim (hu hzero)

private theorem residue_algebraMap_local (v : FinPlace F) (a : 𝓞 F) :
    residue v (algebraMap (𝓞 F) F a) = Ideal.Quotient.mk v.asIdeal a := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let h : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      algebraMap (𝓞 F) F a * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 :=
    ⟨(a, 1), Ideal.IsPrime.one_notMem v.isPrime, by simp⟩
  have hcross : h.choose.1 = a * h.choose.2 := by
    apply (IsFractionRing.injective (𝓞 F) F)
    simpa only [map_mul] using h.choose_spec.2.symm
  have hq : Ideal.Quotient.mk v.asIdeal h.choose.1 =
      Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal h.choose.2 := by
    rw [hcross, map_mul]
  have hcq : Ideal.Quotient.mk v.asIdeal h.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using h.choose_spec.1
  unfold residue
  rw [dif_pos h]
  rw [hq, mul_assoc, mul_inv_cancel₀ hcq, mul_one]

private theorem chi_eq_of_residue_eq (D : FieldData F) (v : FinPlace F) (x y : F)
    (h : residue v x = residue v y) : chi D v x = chi D v y := by
  simp only [chi, chiAlg, h]

private theorem residue_integer_eq_of_valuation_sub_lt_one (v : FinPlace F) (a b : 𝓞 F)
    (h : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F (a - b)) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  have hab : a - b ∈ v.asIdeal := by
    apply (v.valuation_lt_one_iff_mem (K := F) _).1
    exact h
  have hzero := (Ideal.Quotient.eq_zero_iff_mem).2 hab
  have hsub : Ideal.Quotient.mk v.asIdeal a - Ideal.Quotient.mk v.asIdeal b = 0 := by
    simpa only [map_sub] using hzero
  exact sub_eq_zero.mp hsub

private theorem toLoc_isLocUnit_of_valuation_one (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]

private theorem localChi_toLoc_integral (D : FieldData F) (v : FinPlace F)
    (x : Fˣ) (a : 𝓞 F) (ha : a ∉ v.asIdeal)
    (hx : (x : F) = algebraMap (𝓞 F) F a) :
    localChi D v (toLoc v x) = chi D v (x : F) := by
  have hclose : Valued.v (((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F) -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1
    rw [hx]
    simp
  have hex : ∃ b : 𝓞 F, b ∉ v.asIdeal ∧
      Valued.v (((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) -
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b)) < 1 :=
    ⟨a, ha, hclose⟩
  have hchosen : ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (x : F) := rfl
  have hxa : ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := by
    rw [hchosen, hx]
  have hvalSub : Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F a) -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F hex.choose)) < 1 := by
    rw [← hxa]
    exact hex.choose_spec.2
  have hvalSub' : Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (𝓞 F) F (a - hex.choose))) < 1 := by
    simpa only [map_sub] using hvalSub
  have hglobal : HeightOneSpectrum.valuation F v
      (algebraMap (𝓞 F) F (a - hex.choose)) < 1 := by
    change Valued.v ((algebraMap (𝓞 F) F (a - hex.choose) : F) : v.adicCompletion F) < 1 at hvalSub'
    rw [v.valuedAdicCompletion_eq_valuation'] at hvalSub'
    exact hvalSub'
  have hres : residue v (algebraMap (𝓞 F) F a) =
      residue v (algebraMap (𝓞 F) F hex.choose) := by
    rw [residue_algebraMap_local, residue_algebraMap_local]
    exact residue_integer_eq_of_valuation_sub_lt_one v a hex.choose hglobal
  have hchi := chi_eq_of_residue_eq D v _ _ hres
  unfold localChi
  rw [dif_pos hex]
  simpa [hx] using hchi.symm

private theorem exists_localChi_sq_ne_one (D : FieldData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    ∃ u : (v.adicCompletion F)ˣ, IsLocUnit v u ∧
      (localChi D v u) ^ (6 : ℕ) = 1 ∧ (localChi D v u) ^ 2 ≠ 1 := by
  classical
  let κ := 𝓞 F ⧸ v.asIdeal
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field κ := Ideal.Quotient.field v.asIdeal
  letI : Finite κ := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  letI : Fintype κ := Fintype.ofFinite κ
  haveI : IsCyclic κˣ := inferInstance
  let N : ℕ := Ideal.absNorm v.asIdeal - 1
  have hNpos : 0 < N := by
    dsimp [N]
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  have hNdiv6 : 6 ∣ N := by
    simpa [N] using six_dvd_absNorm_sub_one D v hv
  have hNdiv3 : 3 ∣ N := dvd_trans (by norm_num : 3 ∣ 6) hNdiv6
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
  have hcard : Nat.card κˣ = N := by
    dsimp [N, κ]
    rw [Nat.card_units, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  have horder : orderOf g = N := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hgenPowNe : g ^ (N / 3) ≠ 1 := by
    intro hpow
    have hdvd : orderOf g ∣ N / 3 := orderOf_dvd_of_pow_eq_one hpow
    rw [horder] at hdvd
    have hNdiv3pos : 0 < N / 3 := by
      obtain ⟨q, hq⟩ := hNdiv3
      omega
    have hlt : N / 3 < N := Nat.div_lt_self hNpos (by norm_num)
    exact (Nat.not_lt_of_ge (Nat.le_of_dvd hNdiv3pos hdvd)) hlt
  have hmul : N / 3 * 3 = N := by
    obtain ⟨q, hq⟩ := hNdiv3
    omega
  have hgenPow : (g ^ (N / 3)) ^ 3 = 1 := by
    calc
      (g ^ (N / 3)) ^ 3 = g ^ (N / 3 * 3) := by rw [pow_mul]
      _ = g ^ N := by rw [hmul]
      _ = 1 := by rw [← horder]; exact pow_orderOf_eq_one g
  let a : 𝓞 F := Quotient.out (g : κ)
  have hmk : Ideal.Quotient.mk v.asIdeal a = (g : κ) := by
    simpa [a] using (Quotient.out_eq' (g : κ))
  have ha : a ∉ v.asIdeal := by
    intro ha
    have hzero : Ideal.Quotient.mk v.asIdeal a = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 ha
    rw [hmk] at hzero
    exact Units.ne_zero g hzero
  have ha0 : a ≠ 0 := by
    intro ha0
    exact ha (ha0 ▸ Ideal.zero_mem _)
  have hglobalNe : algebraMap (𝓞 F) F a ≠ 0 := by
    intro hzero
    exact ha0 ((IsFractionRing.injective (𝓞 F) F) (by simpa using hzero))
  let x : Fˣ := Units.mk0 (algebraMap (𝓞 F) F a) hglobalNe
  have hxval : HeightOneSpectrum.valuation F v (x : F) = 1 := by
    change HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) = 1
    exact (v.valuation_eq_one_iff_notMem (K := F) (r := a)).2 ha
  let ξ := chiAlg v (x : F)
  have hres : residue v (x : F) ≠ 0 := by
    rw [show (x : F) = algebraMap (𝓞 F) F a by rfl, residue_algebraMap_local]
    rw [hmk]
    exact Units.ne_zero g
  have hcubic := chiAlg_sq_eq_cubic D v (x : F) hv hres
  have hchiSq : (chi D v (x : F)) ^ 2 ≠ 1 := by
    intro hχ
    have hχeq : chi D v (x : F) = D.σ0 (algebraMap (𝓞 F) F ((ξ : (𝓞 F)ˣ) : 𝓞 F)) := by
      simp [chi, hres, ξ]
    have hcoe2 : ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) =
        (((ξ : (𝓞 F)ˣ) : 𝓞 F)) ^ 2 := by
      push_cast
      rfl
    have himage : D.σ0 (algebraMap (𝓞 F) F
        ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F))) = 1 := by
      calc
        D.σ0 (algebraMap (𝓞 F) F
            ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F))) =
            (D.σ0 (algebraMap (𝓞 F) F ((ξ : (𝓞 F)ˣ) : 𝓞 F))) ^ 2 := by
              rw [hcoe2, map_pow, map_pow]
        _ = (chi D v (x : F)) ^ 2 := by rw [hχeq]
        _ = 1 := hχ
    have hF : algebraMap (𝓞 F) F
        ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
      apply D.σ0.injective
      simpa using himage
    have hO : ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) = 1 :=
      (IsFractionRing.injective (𝓞 F) F) hF
    have hred : Ideal.Quotient.mk v.asIdeal
        ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) = 1 := by
      rw [hO]
      simp
    rw [show (x : F) = algebraMap (𝓞 F) F a by rfl, residue_algebraMap_local] at hcubic
    have hgenpow : (g : κ) ^ (N / 3) = 1 := by
      calc
        (g : κ) ^ (N / 3) = (Ideal.Quotient.mk v.asIdeal a) ^ (N / 3) := by rw [hmk]
        _ = Ideal.Quotient.mk v.asIdeal
            ((((ξ ^ 2 : rootsOfUnity 6 (𝓞 F)) : (𝓞 F)ˣ) : 𝓞 F)) := hcubic.symm
        _ = 1 := hred
    exact hgenPowNe (Units.ext hgenpow)
  letI : Nontrivial κ := inferInstance
  have huLoc : IsLocUnit v (toLoc v x) := toLoc_isLocUnit_of_valuation_one v x hxval
  have hlocal : localChi D v (toLoc v x) = chi D v (x : F) :=
    localChi_toLoc_integral D v x a ha rfl
  refine ⟨toLoc v x, huLoc, ?_, ?_⟩
  · rw [hlocal]
    exact chi_six_of_residue D v (x : F) hres
  · rw [hlocal]
    exact hchiSq

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
  obtain ⟨u, hu, hχ6, hχ2⟩ := exists_localChi_sq_ne_one D v hv
  let χ := localChi D v u
  have hχne : χ ≠ 0 := by
    intro hzero
    have hχ6' : χ ^ (6 : ℕ) = 1 := by simpa [χ] using hχ6
    rw [hzero] at hχ6'
    norm_num at hχ6'
  have hχ2' : χ ^ 2 ≠ 1 := by simpa [χ] using hχ2
  have hχ6' : χ ^ (6 : ℕ) = 1 := by simpa [χ] using hχ6
  have hχ4 : χ ^ 4 ≠ 1 := by
    intro h4
    have hpow : χ ^ 6 = χ ^ 4 * χ ^ 2 := by ring
    rw [hχ6', h4] at hpow
    exact hχ2' (by simpa using hpow.symm)
  have hχ8 : χ ^ 8 ≠ 1 := by
    intro h8
    have hpow : χ ^ 8 = χ ^ 6 * χ ^ 2 := by ring
    rw [h8, hχ6'] at hpow
    exact hχ2' (by simpa using hpow.symm)
  let b : Module.Basis (ZMod 3) ℂ T.V := Module.Basis.mk B.linIndep B.spans.ge
  have hbasis (k : ZMod 3) : b k = B.e k := Module.Basis.mk_apply _ _ _
  have hdiag (k : ZMod 3) :
      T.σa u (b k) = χ ^ (4 * (k.val : ℤ)) • b k := by
    rw [hbasis]
    calc
      T.σa u (B.e k) = χ ^ (2 * (0 + 2 * (k.val : ℤ))) • B.e k := by
        simpa [χ] using B.act 0 u hu k
      _ = χ ^ (4 * (k.val : ℤ)) • B.e k := by congr 1 <;> ring
  have hTx : T.σa u x =
      ∑ k : ZMod 3, (χ ^ (4 * (k.val : ℤ)) * b.repr x k) • b k := by
    have hxsum : x = ∑ k : ZMod 3, b.repr x k • b k := (b.sum_repr x).symm
    calc
      T.σa u x = T.σa u (∑ k : ZMod 3, b.repr x k • b k) := by
        exact congrArg (T.σa u) hxsum
      _ = ∑ k : ZMod 3, T.σa u (b.repr x k • b k) := map_sum _ _ _
      _ = ∑ k : ZMod 3, (χ ^ (4 * (k.val : ℤ)) * b.repr x k) • b k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [map_smul, hdiag, smul_smul]
        congr 1
        ring
  have hcoord (k : ZMod 3) :
      (χ ^ (4 * (k.val : ℤ)) - 1) * b.repr x k = 0 := by
    have hfixed := hx u hu
    have h := congrArg (fun y : T.V => b.repr y k) hfixed
    rw [hTx] at h
    simp only [map_sum, map_smul, Module.Basis.repr_self] at h
    change (∑ i : ZMod 3,
      (χ ^ (4 * (i.val : ℤ)) * b.repr x i) • Finsupp.single i (1 : ℂ)) k = b.repr x k at h
    rw [Finsupp.finsetSum_apply] at h
    simp [Finsupp.smul_apply, Finsupp.single_apply] at h
    calc
      (χ ^ (4 * (k.val : ℤ)) - 1) * b.repr x k =
          χ ^ (4 * (k.val : ℤ)) * b.repr x k - b.repr x k := by ring
      _ = 0 := by
        have hp : χ ^ (4 * (k.val : ℤ)) * b.repr x k = b.repr x k := by simpa using h
        rw [hp]
        ring
  have hval1 : (1 : ZMod 3).val = 1 := by
    rw [ZMod.val_one_eq_one_mod]
  have hval2 : (2 : ZMod 3).val = 2 := by
    rw [ZMod.val_two_eq_two_mod]
  have hrepr1 : b.repr x (1 : ZMod 3) = 0 := by
    have h := hcoord (1 : ZMod 3)
    have hf : χ ^ 4 - 1 ≠ 0 := sub_ne_zero.mpr hχ4
    have hs : (χ ^ 4 - 1) * b.repr x 1 = 0 := by simpa [hval1] using h
    exact (mul_eq_zero.mp hs).resolve_left hf
  have hrepr2 : b.repr x (2 : ZMod 3) = 0 := by
    have h := hcoord (2 : ZMod 3)
    have hf : χ ^ 8 - 1 ≠ 0 := sub_ne_zero.mpr hχ8
    have hs : (χ ^ 8 - 1) * b.repr x 2 = 0 := by simpa [hval2] using h
    exact (mul_eq_zero.mp hs).resolve_left hf
  have hrepr : ∀ k : ZMod 3, k ≠ 0 → b.repr x k = 0 := by
    intro k hk
    have hvalne : k.val ≠ 0 := by
      intro hzero
      apply hk
      apply (ZMod.val_injective 3)
      simpa [hzero]
    have hvalCases : k.val = 1 ∨ k.val = 2 := by
      have hklt := k.val_lt
      omega
    rcases hvalCases with hval | hval
    · have hk1 : k = 1 := by
        apply (ZMod.val_injective 3)
        rw [hval1]
        exact hval
      rw [hk1]
      exact hrepr1
    · have hk2 : k = 2 := by
        apply (ZMod.val_injective 3)
        rw [hval2]
        exact hval
      rw [hk2]
      exact hrepr2
  refine ⟨b.repr x 0, ?_⟩
  have hsum : (∑ k : ZMod 3, b.repr x k • b k) = b.repr x 0 • b 0 := by
    rw [Finset.sum_eq_single (0 : ZMod 3)]
    · intro k hk hk0
      simp [hrepr k hk0]
    · intro hnot
      exact (hnot (Finset.mem_univ 0)).elim
  calc
    x = ∑ k : ZMod 3, b.repr x k • b k := (b.sum_repr x).symm
    _ = b.repr x 0 • b 0 := hsum
    _ = b.repr x 0 • B.e 0 := by rw [hbasis]

/-- **def:weyl-basis**: `e^w_k := e_{-k}` is a tame basis of the Weyl conjugate `T.weyl`
(uses `localChi(u⁻¹) = localChi(u)⁻¹` and `localChi(u)^6 = 1` on local units). -/
def TameTorusBasis.weyl {T : TorusRep D H v} (B : TameTorusBasis T) : TameTorusBasis T.weyl where
  e k := B.e (-k)
  linIndep := by
    dsimp [TorusRep.weyl]
    exact B.linIndep.comp (fun k : ZMod 3 => -k) (by
      intro k k' h
      exact neg_injective h)
  spans := by
    simp only [TorusRep.weyl]
    have hrange : Set.range (fun k : ZMod 3 => B.e (-k)) = Set.range B.e := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨-k, by simp⟩
      · rintro ⟨k, rfl⟩
        exact ⟨-k, by simp⟩
    rw [hrange]
    exact B.spans
  act := by
    intro j u hu k
    let χ := localChi D v u
    let i : ZMod 3 := -k - (j : ZMod 3)
    let y : (v.adicCompletion F)ˣ := unifLoc v ^ j * u
    let n : ℤ := 2 * (j + 2 * (i.val : ℤ))
    let m : ℤ := 2 * (j + 2 * (k.val : ℤ))
    have he1 : B.e (1 : ZMod 3) ≠ 0 := B.linIndep.ne_zero 1
    have hact1 := B.act 0 u hu (1 : ZMod 3)
    have hχne : χ ≠ 0 := by
      intro hzero
      have hval1 : (1 : ZMod 3).val = 1 := by
        rw [ZMod.val_one_eq_one_mod]
      have hact1' : T.σa u (B.e (1 : ZMod 3)) =
          χ ^ (2 * (0 + 2 * ((1 : ZMod 3).val : ℤ))) • B.e (1 : ZMod 3) := by
        simpa [hval1] using hact1
      have hzeroAct : T.σa u (B.e (1 : ZMod 3)) = 0 := by
        calc
          T.σa u (B.e (1 : ZMod 3)) =
              χ ^ (2 * (0 + 2 * ((1 : ZMod 3).val : ℤ))) • B.e (1 : ZMod 3) := hact1'
          _ = 0 := by rw [hzero]; norm_num [hval1]
      apply he1
      exact torusRep_sigma_injective T u (by simpa using hzeroAct)
    have hχ6 : χ ^ (6 : ℕ) = 1 := localChi_six_of_nezero D v u hχne
    have hidx : i + (j : ZMod 3) = -k := by
      dsimp [i]
      group
    have hact : T.σa y (B.e i) = χ ^ n • B.e (-k) := by
      simpa [y, χ, n, hidx] using B.act j u hu i
    have hleft : T.σa y⁻¹ (T.σa y (B.e i)) = B.e i := by
      have h := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e i)) (torusRep_sigma_inv T y)
      simpa [LinearMap.comp_apply] using h
    have hscaled : B.e i = χ ^ n • T.σa y⁻¹ (B.e (-k)) := by
      calc
        B.e i = T.σa y⁻¹ (T.σa y (B.e i)) := hleft.symm
        _ = T.σa y⁻¹ (χ ^ n • B.e (-k)) := by rw [hact]
        _ = χ ^ n • T.σa y⁻¹ (B.e (-k)) := map_smul _ _ _
    have hscale : T.σa y⁻¹ (B.e (-k)) = χ ^ (-n) • B.e i := by
      have h := congrArg (fun z : T.V => (χ ^ n)⁻¹ • z) hscaled
      have hcoef : χ ^ n ≠ 0 := zpow_ne_zero _ hχne
      calc
        T.σa y⁻¹ (B.e (-k)) = (χ ^ n)⁻¹ • ((χ ^ n) • T.σa y⁻¹ (B.e (-k))) := by
          rw [smul_smul, inv_mul_cancel₀ hcoef, one_smul]
        _ = (χ ^ n)⁻¹ • B.e i := h.symm
        _ = χ ^ (-n) • B.e i := by rw [← zpow_neg]
    have hsumZval : (i.val : ZMod 3) + (k.val : ZMod 3) + (j : ZMod 3) = 0 := by
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      dsimp [i]
      group
    have hdiv : (3 : ℤ) ∣ (i.val : ℤ) + (k.val : ℤ) + j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      simpa only [Int.cast_add, Int.cast_natCast] using hsumZval
    obtain ⟨r, hr⟩ := hdiv
    have hmn : m + n = 6 * (2 * r) := by
      dsimp [m, n]
      nlinarith [hr]
    have hneg : -n = m - 6 * (2 * r) := by omega
    have hχ6z : χ ^ (6 : ℤ) = 1 := by simpa using hχ6
    have hpower : χ ^ (-n) = χ ^ m := by
      rw [hneg, zpow_sub₀ hχne]
      simp [zpow_mul, hχ6z]
    have hi : i = -(k + (j : ZMod 3)) := by
      dsimp [i]
      group
    change T.σa y⁻¹ (B.e (-k)) = χ ^ m • B.e (-(k + (j : ZMod 3)))
    simpa [χ, y, m, hi, hpower] using hscale

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
