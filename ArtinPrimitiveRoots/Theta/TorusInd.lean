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
  rcases hf with ⟨hN, hZ, ⟨m, hm, hfix⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y u
    change f ((L.n (Multiplicative.ofAdd x) * L.a y * u) * g) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (f (u * g))
    simpa [mul_assoc] using hN x y (u * g)
  · intro ζ u
    change f ((L.z ζ * u) * g) = ((ζ : ℂˣ) : ℂ) • f (u * g)
    simpa [mul_assoc] using hZ ζ (u * g)
  · have hconj : Continuous (fun k : L.L => g⁻¹ * k * g) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hopen : IsOpen {k : L.L | g⁻¹ * k * g ∈ L.Kc m} :=
      IsOpen.preimage hconj (L.Kc_open m hm)
    have hnhds : {k : L.L | g⁻¹ * k * g ∈ L.Kc m} ∈ nhds (1 : L.L) := by
      apply hopen.mem_nhds
      simp
    obtain ⟨m', hm', hsub⟩ := L.Kc_nhds _ hnhds
    refine ⟨m', hm', ?_⟩
    intro u k hk
    change f ((u * k) * g) = f (u * g)
    rw [show (u * k) * g = (u * g) * (g⁻¹ * k * g) by group]
    exact hfix (u * g) (g⁻¹ * k * g) (hsub hk)

private theorem iwasawa_right_denominator (g : GL (Fin 2) (v.adicCompletion F))
    (hd : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0)
    (hcd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) :
    ∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
    ∃ k : GL (Fin 2) (v.adicCompletion F),
        k = lowerM (v.adicCompletion F)
          (((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) /
            ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) ∧
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        Matrix.ProjGenLinGroup.mk g =
          Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
            Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
              Matrix.ProjGenLinGroup.mk k := by
  classical
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) := g
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : M.det ≠ 0 := by simpa [M] using g.det_ne_zero
  have hratioVal : Valued.v (c / d) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (by simpa [c, d, M] using hcd) (bot_le : 0 ≤ Valued.v d)
  have hratio : c / d ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hratioVal
  have hyval : M.det / d ^ 2 ≠ 0 := by
    exact div_ne_zero hdet (pow_ne_zero 2 (by simpa [d, M] using hd))
  let x : v.adicCompletion F := b / d
  let y : (v.adicCompletion F)ˣ := Units.mk0 (M.det / d ^ 2) hyval
  let k : GL (Fin 2) (v.adicCompletion F) := lowerM (v.adicCompletion F) (c / d)
  have heq : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd) *
      upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y * k := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, a, b, c, d, x, y, k, Matrix.GeneralLinearGroup.scalar,
        upperM, diagM, lowerM, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.det_fin_two] <;>
      field_simp [hd, hdet] <;> ring
  have hkentries : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [k, lowerM, hratio]
  have hinv : k⁻¹ = lowerM (v.adicCompletion F) (-(c / d)) := by
    have hmul : k * lowerM (v.adicCompletion F) (-(c / d)) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [k, lowerM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    calc
      k⁻¹ = k⁻¹ * 1 := by simp
      _ = k⁻¹ * (k * lowerM (v.adicCompletion F) (-(c / d))) := by rw [hmul]
      _ = lowerM (v.adicCompletion F) (-(c / d)) := by group
  have hdetinv : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = 1 := by
    rw [hinv]
    simp [lowerM, Matrix.det_fin_two]
  refine ⟨x, y, k, rfl, hkentries, ?_, ?_⟩
  · rw [hdetinv]
    exact (v.adicCompletionIntegers F).one_mem
  · rw [heq]
    change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd) *
        upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y * k) = _
    simp only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

private theorem iwasawa_matrix_decomposition (g : GL (Fin 2) (v.adicCompletion F)) :
    ∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
      ∃ k : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        Matrix.ProjGenLinGroup.mk g =
          Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
            Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
              Matrix.ProjGenLinGroup.mk k := by
  classical
  let c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  have hrow : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≠ 0 := by
      simpa using g.det_ne_zero
    apply hdet
    rw [Matrix.det_fin_two]
    simp [c, d, h.1, h.2]
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      rcases hrow with hc | hd'; exact hc
      exact (hd' hd).elim
    have hleft : (g * weylM (v.adicCompletion F) :
        GL (Fin 2) (v.adicCompletion F)) 1 0 = d := by
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
    have hright : (g * weylM (v.adicCompletion F) :
        GL (Fin 2) (v.adicCompletion F)) 1 1 = c := by
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
    have hval : Valued.v d ≤ Valued.v c := by rw [hd]; simp
    obtain ⟨x, y, k₀, hk₀, hkentries, hdetinv, hq⟩ :=
      iwasawa_right_denominator (g * weylM (v.adicCompletion F)) (by simpa [hright] using hc)
        (by simpa [hleft, hright] using hval)
    subst k₀
    let k : GL (Fin 2) (v.adicCompletion F) :=
      lowerM (v.adicCompletion F) (d / c) * weylM (v.adicCompletion F)
    have hratio : d / c ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hval (by simp)
    have hkentries' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        v.adicCompletionIntegers F := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, hratio]
    have hdetk : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = -1 := by
      simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    have hmul : ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val) *
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
      exact congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
        (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (inv_mul_cancel k)
    have hdetmul : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det *
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
      simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmul
    have hdetinv' : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = -1 := by
      rw [hdetk] at hdetmul
      calc
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det =
            (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * (-1 * -1) := by ring
        _ = ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * -1) * -1 := by ring
        _ = 1 * -1 := by rw [hdetmul]
        _ = -1 := by ring
    have hminus : (-1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp
    have hq' : Matrix.ProjGenLinGroup.mk g =
        Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
          Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
            Matrix.ProjGenLinGroup.mk k := by
      have hw : weylM (v.adicCompletion F) * weylM (v.adicCompletion F) = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
      have hg : g = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) := by
        calc
          g = g * 1 := by simp
          _ = g * (weylM (v.adicCompletion F) * weylM (v.adicCompletion F)) := by rw [hw]
          _ = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) :=
            (mul_assoc _ _ _).symm
      have hq'0 := hq
      rw [hleft, hright] at hq'0
      calc
        Matrix.ProjGenLinGroup.mk g =
            Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
              Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by
                calc
                  Matrix.ProjGenLinGroup.mk g =
                      Matrix.ProjGenLinGroup.mk
                        ((g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F)) :=
                    congrArg Matrix.ProjGenLinGroup.mk hg
                  _ = Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                        Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [map_mul]
        _ = (Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c))) *
              Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [hq'0]
        _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                (Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c)) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F))) := by ac_rfl
        _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk k := by rw [map_mul]
    refine ⟨x, y, k, hkentries', ?_, hq'⟩
    rw [hdetinv']
    exact hminus
  · by_cases hc : c = 0
    · have hval : Valued.v c ≤ Valued.v d := by rw [hc]; simp
      obtain ⟨x, y, k, hkform, hk, hdet, hq⟩ :=
        iwasawa_right_denominator g (by simpa [d] using hd) (by simpa [c, d] using hval)
      exact ⟨x, y, k, hk, hdet, hq⟩
    · by_cases hval : Valued.v c ≤ Valued.v d
      · obtain ⟨x, y, k, hkform, hk, hdet, hq⟩ :=
          iwasawa_right_denominator g (by simpa [d] using hd) (by simpa [c, d] using hval)
        exact ⟨x, y, k, hk, hdet, hq⟩
      · have hdc : Valued.v d ≤ Valued.v c := le_of_not_ge hval
        have hleft : (g * weylM (v.adicCompletion F) :
            GL (Fin 2) (v.adicCompletion F)) 1 0 = d := by
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
        have hright : (g * weylM (v.adicCompletion F) :
            GL (Fin 2) (v.adicCompletion F)) 1 1 = c := by
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
        obtain ⟨x, y, k₀, hk₀, hkentries, hdetinv, hq⟩ :=
          iwasawa_right_denominator (g * weylM (v.adicCompletion F)) (by simpa [hright] using hc)
            (by simpa [hleft, hright] using hdc)
        subst k₀
        let k : GL (Fin 2) (v.adicCompletion F) :=
          lowerM (v.adicCompletion F) (d / c) * weylM (v.adicCompletion F)
        have hratio : d / c ∈ v.adicCompletionIntegers F := by
          rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
          exact div_le_one_of_le₀ hdc (by simp)
        have hkentries' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
            v.adicCompletionIntegers F := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, hratio]
        have hdetk : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = -1 := by
          simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
        have hmul : ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val) *
            (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
          exact congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
            (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (inv_mul_cancel k)
        have hdetmul : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det *
            (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
          simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmul
        have hdetinv' : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = -1 := by
          rw [hdetk] at hdetmul
          calc
            (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det =
                (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * (-1 * -1) := by ring
            _ = ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * -1) * -1 := by ring
            _ = 1 * -1 := by rw [hdetmul]
            _ = -1 := by ring
        have hminus : (-1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
          rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          simp
        have hq' : Matrix.ProjGenLinGroup.mk g =
            Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk k := by
          have hw : weylM (v.adicCompletion F) * weylM (v.adicCompletion F) = 1 := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
          have hg : g = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) := by
            calc
              g = g * 1 := by simp
              _ = g * (weylM (v.adicCompletion F) * weylM (v.adicCompletion F)) := by rw [hw]
              _ = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) :=
                (mul_assoc _ _ _).symm
          have hq'0 := hq
          rw [hleft, hright] at hq'0
          calc
            Matrix.ProjGenLinGroup.mk g =
                Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by
                    calc
                      Matrix.ProjGenLinGroup.mk g =
                          Matrix.ProjGenLinGroup.mk
                            ((g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F)) :=
                        congrArg Matrix.ProjGenLinGroup.mk hg
                      _ = Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                            Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [map_mul]
            _ = (Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c))) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [hq'0]
            _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    (Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c)) *
                      Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F))) := by ac_rfl
            _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    Matrix.ProjGenLinGroup.mk k := by rw [map_mul]
        refine ⟨x, y, k, hkentries', ?_, hq'⟩
        rw [hdetinv']
        exact hminus

/-- **ind:iwasawa** (tame): `L = B̃ · Kmax`. -/
theorem iwasawa_tame (L : FinLocalCover D H v) (τ : TameSplitting L) (g : L.L) :
    ∃ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ) (ζ : rootsOfUnity 3 ℂ) (k : L.L),
      k ∈ τ.Kmax ∧ g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by
  classical
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective (L.pr g)
  obtain ⟨x, y, kMat, hkentries, hkdetinv, hmatrix⟩ := iwasawa_matrix_decomposition G
  have himage : L.pr '' (τ.Kmax : Set L.L) =
      {q | ∃ k : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        QuotientGroup.mk k = q} := τ.image
  have hkmem : Matrix.ProjGenLinGroup.mk kMat ∈ L.pr '' (τ.Kmax : Set L.L) := by
    rw [himage]
    exact ⟨kMat, hkentries, hkdetinv, rfl⟩
  obtain ⟨k, hkK, hkpr⟩ := hkmem
  let b : L.L := L.n (Multiplicative.ofAdd x) * L.a y * k
  have hprB : L.pr b =
      Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
        Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
          Matrix.ProjGenLinGroup.mk kMat := by
    dsimp [b]
    simp only [map_mul, L.pr_n, L.pr_a, hkpr]
    rfl
  have hprdecomp : L.pr g = L.pr b := by
    exact hG.symm.trans (hmatrix.trans hprB.symm)
  let q : L.L := b⁻¹ * g
  have hqker : q ∈ L.pr.ker := by
    change L.pr (b⁻¹ * g) = 1
    calc
      L.pr (b⁻¹ * g) = (L.pr b)⁻¹ * L.pr g := by simp only [map_mul, map_inv]
      _ = 1 := by rw [← hprdecomp]; simp
  rw [L.pr_ker] at hqker
  obtain ⟨ζ, hζ⟩ := hqker
  have hg : g = b * L.z ζ := by
    calc
      g = b * q := by dsimp [q]; group
      _ = b * L.z ζ := by rw [← hζ]
  have horder : b * L.z ζ =
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by
    change (L.n (Multiplicative.ofAdd x) * L.a y * k) * L.z ζ =
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k
    calc
      (L.n (Multiplicative.ofAdd x) * L.a y * k) * L.z ζ =
          (L.n (Multiplicative.ofAdd x) * L.a y) * (k * L.z ζ) := by group
      _ = (L.n (Multiplicative.ofAdd x) * L.a y) * (L.z ζ * k) := by
            rw [← L.z_central ζ k]
      _ = L.n (Multiplicative.ofAdd x) * (L.a y * L.z ζ) * k := by group
      _ = L.n (Multiplicative.ofAdd x) * (L.z ζ * L.a y) * k := by
            rw [← L.z_central ζ (L.a y)]
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by group
  exact ⟨x, y, ζ, k, hkK, hg.trans horder⟩

private def borelElem (L : FinLocalCover D H v) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) : L.L :=
  L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y

private def bigCellMatrix (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
    (t : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F) :=
  upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
    weylM (v.adicCompletion F) * upperM (v.adicCompletion F) t

private theorem bigCell_pr_eq (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t t' : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y' * L.w *
        L.n (Multiplicative.ofAdd t')) :
    (QuotientGroup.mk (bigCellMatrix (F := F) x y t) :
      PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := by
  have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
    intro η
    have hker : L.z η ∈ L.pr.ker := by
      rw [L.pr_ker]
      exact ⟨η, rfl⟩
    exact MonoidHom.mem_ker.mp hker
  have hp := congrArg L.pr h
  change (QuotientGroup.mk (bigCellMatrix (F := F) x y t) :
      PGL2 (v.adicCompletion F)) =
    QuotientGroup.mk (bigCellMatrix (F := F) x' y' t')
  simpa [bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz, mul_assoc] using hp

private theorem bigCell_coords_unique (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t t' : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y' * L.w *
        L.n (Multiplicative.ofAdd t')) :
    x = x' ∧ y = y' ∧ t = t' ∧ ζ = ζ' := by
  have hclass := bigCell_pr_eq L x x' ζ ζ' y y' t t' h
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmat :
      ((bigCellMatrix (F := F) x y t) * Matrix.GeneralLinearGroup.scalar
        (Fin 2) c : GL (Fin 2) (v.adicCompletion F)) =
      bigCellMatrix (F := F) x' y' t' := hc
  have hmatval :
      (((bigCellMatrix (F := F) x y t) * Matrix.GeneralLinearGroup.scalar
        (Fin 2) c : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (bigCellMatrix (F := F) x' y' t' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
    congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
      (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hmat
  have hcval : (c : v.adicCompletion F) = 1 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 0) hmatval
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hmat' : bigCellMatrix (F := F) x y t = bigCellMatrix (F := F) x' y' t' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M i j) hmatval
    fin_cases i <;> fin_cases j <;>
      simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
        hcval] using he
  have hentries := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) =>
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hmat'
  have ht : t = t' := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 1) hentries
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hx : x = x' := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 0 0) hentries
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hy : y = y' := by
    apply Units.ext
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 0 1) hentries
    have he' : (y : v.adicCompletion F) + x * t =
        (y' : v.adicCompletion F) + x' * t' := by
      calc
        (y : v.adicCompletion F) + x * t = x * t + y := by ring
        _ = x' * t' + y' := by
          simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
        _ = (y' : v.adicCompletion F) + x' * t' := by ring
    rw [hx, ht] at he'
    exact add_right_cancel he'
  have hphase : ζ = ζ' := by
    have hcancel := h
    rw [hx, hy, ht] at hcancel
    have hprefix : L.n (Multiplicative.ofAdd x') *
        (L.z ζ * (L.a y' * L.w * L.n (Multiplicative.ofAdd t'))) =
        L.n (Multiplicative.ofAdd x') *
          (L.z ζ' * (L.a y' * L.w * L.n (Multiplicative.ofAdd t'))) := by
      simpa [mul_assoc] using hcancel
    have hmid : L.z ζ * (L.a y' * L.w * L.n (Multiplicative.ofAdd t')) =
        L.z ζ' * (L.a y' * L.w * L.n (Multiplicative.ofAdd t')) :=
      mul_left_cancel hprefix
    have hphase' : L.z ζ = L.z ζ' := mul_right_cancel hmid
    exact L.z_inj hphase'
  exact ⟨hx, hy, ht, hphase⟩

private theorem bigcell_ne_borel (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y') : False := by
  have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
    intro η
    have hker : L.z η ∈ L.pr.ker := by
      rw [L.pr_ker]
      exact ⟨η, rfl⟩
    exact MonoidHom.mem_ker.mp hker
  have hp := congrArg L.pr h
  let A := bigCellMatrix (F := F) x y t
  let B := upperM (v.adicCompletion F) x' * diagM (v.adicCompletion F) y'
  have hclass : (QuotientGroup.mk A : PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk B := by
    simpa [A, B, bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz,
      mul_assoc] using hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmatval :
      (((A * Matrix.GeneralLinearGroup.scalar (Fin 2) c :
        GL (Fin 2) (v.adicCompletion F)) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
    congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
      (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hc
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 0) hmatval
  have hc0 : (c : v.adicCompletion F) = 0 := by
    simpa [A, B, bigCellMatrix, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  exact c.ne_zero hc0

private theorem absFin_eq_norm_ind (v : FinPlace F) (x : v.adicCompletion F) :
    absFin v x = ‖x‖ := by
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

private theorem absFin_mul_ind (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
    absFin v (x * y) = absFin v x * absFin v y := by
  simp only [absFin_eq_norm_ind, norm_mul]

private theorem absFin_one_of_locUnit (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) : absFin v (u : v.adicCompletion F) = 1 := by
  rw [absFin_eq_norm_ind]
  have hu₁ : ‖(u : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    have h := hu.1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hu₂ : ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    have h := hu.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hprod : ‖(u : v.adicCompletion F)‖ *
      ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    calc
      _ = ‖(u : v.adicCompletion F) *
          ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ := (norm_mul _ _).symm
      _ = 1 := by simp
  have huge : 1 ≤ ‖(u : v.adicCompletion F)‖ := by
    calc
      1 = ‖(u : v.adicCompletion F)‖ *
          ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ := hprod.symm
      _ ≤ ‖(u : v.adicCompletion F)‖ * 1 :=
          mul_le_mul_of_nonneg_left hu₂ (norm_nonneg _)
      _ = ‖(u : v.adicCompletion F)‖ := by simp
  exact le_antisymm hu₁ huge

private theorem borel_inter_Kmax (L : FinLocalCover D H v) (τ : TameSplitting L)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (hb : borelElem L x ζ y ∈ τ.Kmax) :
    x ∈ v.adicCompletionIntegers F ∧ IsLocUnit v y ∧ ζ = 1 := by
  classical
  let K := v.adicCompletion F
  let B : GL (Fin 2) K := upperM K x * diagM K y
  have hzker : L.z ζ ∈ L.pr.ker := by
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hprz : L.pr (L.z ζ) = 1 := by
    exact MonoidHom.mem_ker.mp hzker
  have hprB : L.pr (borelElem L x ζ y) = QuotientGroup.mk B := by
    simp [borelElem, B, K, map_mul, L.pr_n, L.pr_a, hprz, mul_assoc]
  have himage : L.pr (borelElem L x ζ y) ∈ L.pr '' (τ.Kmax : Set L.L) :=
    ⟨borelElem L x ζ y, hb, rfl⟩
  rw [τ.image] at himage
  obtain ⟨M, hMentries, hMinvdet, hMclass⟩ := himage
  have hclass : Matrix.ProjGenLinGroup.mk M = Matrix.ProjGenLinGroup.mk B := by
    change QuotientGroup.mk M = QuotientGroup.mk B
    rw [hMclass, hprB]
  obtain ⟨c, hmat⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmatval : (M * Matrix.GeneralLinearGroup.scalar (Fin 2) c :
      GL (Fin 2) K).val = B.val := congrArg (fun q : GL (Fin 2) K => (q : Matrix (Fin 2) (Fin 2) K)) hmat
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hmatval
    have he' : (M : Matrix (Fin 2) (Fin 2) K) 1 0 * (c : K) = 0 := by
      simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using he
    exact (mul_eq_zero.mp he').resolve_right c.ne_zero
  have hMdetO : (M : Matrix (Fin 2) (Fin 2) K).det ∈ v.adicCompletionIntegers F := by
    rw [Matrix.det_fin_two]
    exact (v.adicCompletionIntegers F).sub_mem
      ((v.adicCompletionIntegers F).mul_mem _ _ (hMentries 0 0) (hMentries 1 1))
      ((v.adicCompletionIntegers F).mul_mem _ _ (hMentries 0 1) (hMentries 1 0))
  have hmulM : (M : Matrix (Fin 2) (Fin 2) K) *
      ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    exact congrArg (fun q : GL (Fin 2) K => (q : Matrix (Fin 2) (Fin 2) K)) (mul_inv_cancel M)
  have hdetmul : (M : Matrix (Fin 2) (Fin 2) K).det *
      ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmulM
  have hdetValProd : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) *
      Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    calc
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det *
          ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) := by rw [map_mul]
      _ = 1 := by rw [hdetmul]; simp
  have hdetLE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 := by
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 at hMdetO
    exact hMdetO
  have hMinvLE : Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 := by
    change Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 at hMinvdet
    exact hMinvdet
  have hdetVal : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    apply le_antisymm hdetLE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) *
          Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) := hdetValProd.symm
      _ ≤ Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) * 1 :=
          mul_le_mul_of_nonneg_left hMinvLE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) := by simp
  have hM00LE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) ≤ 1 := by
    have h := hMentries 0 0
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) ≤ 1 at h
    exact h
  have hM11LE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) ≤ 1 := by
    have h := hMentries 1 1
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) ≤ 1 at h
    exact h
  have hdetfactor : (M : Matrix (Fin 2) (Fin 2) K).det =
      (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [Matrix.det_fin_two, hM10]
    ring
  have hdetValfactor : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
      Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 := by
    rw [← map_mul, ← hdetfactor, hdetVal]
  have hM00Val : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) = 1 := by
    apply le_antisymm hM00LE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
          Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := hdetValfactor.symm
      _ ≤ Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) * 1 :=
          mul_le_mul_of_nonneg_left hM11LE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) := by simp
  have hM11Val : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 := by
    apply le_antisymm hM11LE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
          Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := hdetValfactor.symm
      _ ≤ 1 * Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) :=
          mul_le_mul_of_nonneg_right hM00LE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := by simp
  have hM00c : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (c : K) = (y : K) := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM01c : (M : Matrix (Fin 2) (Fin 2) K) 0 1 * (c : K) = x := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM11c : (M : Matrix (Fin 2) (Fin 2) K) 1 1 * (c : K) = 1 := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM11ne : (M : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro hzero
    have hzeroVal : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 0 := by simp [hzero]
    rw [hM11Val] at hzeroVal
    norm_num at hzeroVal
  have hcval : (c : K) = ((M : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hM11c
  have hxformula : x = (M : Matrix (Fin 2) (Fin 2) K) 0 1 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [hcval] at hM01c
    simpa [div_eq_mul_inv] using hM01c.symm
  have hyformula : (y : K) = (M : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [hcval] at hM00c
    simpa [div_eq_mul_inv] using hM00c.symm
  have hxVal : Valued.v x ≤ 1 := by
    rw [hxformula, map_div₀, hM11Val, div_one]
    have hM01LE := hMentries 0 1
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 1) ≤ 1 at hM01LE
    exact hM01LE
  have hyVal : Valued.v (y : K) = 1 := by
    rw [hyformula, map_div₀, hM00Val, hM11Val]
    simp
  have hxO : x ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hxVal
  have hyLoc : IsLocUnit v y := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hyVal]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simpa [map_inv₀, hyVal]
  have hNA : L.n (Multiplicative.ofAdd x) * L.a y ∈ τ.Kmax := by
    exact τ.Kmax.mul_mem (τ.n_mem x hxO) (τ.a_mem y hyLoc.1 hyLoc.2)
  have hprNA : L.pr (L.n (Multiplicative.ofAdd x) * L.a y) =
      QuotientGroup.mk B := by
    simp [B, K, map_mul, L.pr_n, L.pr_a]
  have hprB' : L.pr (borelElem L x ζ y) = L.pr (L.n (Multiplicative.ofAdd x) * L.a y) := by
    rw [hprB, hprNA]
  have heqNA : borelElem L x ζ y = L.n (Multiplicative.ofAdd x) * L.a y :=
    τ.inj hb hNA hprB'
  have hcomm : borelElem L x ζ y = L.z ζ *
      (L.n (Multiplicative.ofAdd x) * L.a y) := by
    dsimp [borelElem]
    calc
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y =
          L.z ζ * L.n (Multiplicative.ofAdd x) * L.a y := by
            rw [← L.z_central ζ (L.n (Multiplicative.ofAdd x))]
      _ = L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) := by rw [mul_assoc]
  have hzNA : L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
      L.n (Multiplicative.ofAdd x) * L.a y := hcomm.symm.trans heqNA
  have hz : L.z ζ = 1 := by
    have hcancel : L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
        1 * (L.n (Multiplicative.ofAdd x) * L.a y) := by simpa using hzNA
    exact (mul_right_cancel hcancel)
  exact ⟨hxO, hyLoc, L.z_inj (by simpa using hz)⟩

private theorem borelElem_mul (L : FinLocalCover D H v)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    borelElem L x₁ ζ₁ y₁ * borelElem L x₂ ζ₂ y₂ =
      borelElem L (x₁ + x₂ * (y₁ : v.adicCompletion F))
        (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) := by
  have hmove : L.a y₁ * L.n (Multiplicative.ofAdd x₂) =
      L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.a y₁ := by
    have h := L.lift_na (x₂ * (y₁ : v.adicCompletion F)) y₁
    simpa using h.symm
  have hn : L.n (Multiplicative.ofAdd x₁) *
      L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) =
      L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) := by
    simpa using (map_mul L.n (Multiplicative.ofAdd x₁)
      (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))))
  calc
    borelElem L x₁ ζ₁ y₁ * borelElem L x₂ ζ₂ y₂ =
        (L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ * L.a y₁) *
          (L.n (Multiplicative.ofAdd x₂) * L.z ζ₂ * L.a y₂) := rfl
    _ = L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ *
          (L.a y₁ * L.n (Multiplicative.ofAdd x₂)) * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ *
          (L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.a y₁) *
          L.z ζ₂ * L.a y₂ := by rw [hmove]
    _ = L.n (Multiplicative.ofAdd x₁) *
          (L.z ζ₁ * L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F)))) *
          L.a y₁ * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          (L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.z ζ₁) *
          L.a y₁ * L.z ζ₂ * L.a y₂ := by rw [L.z_central ζ₁]
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * L.a y₁ * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * (L.a y₁ * L.z ζ₂) * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * (L.z ζ₂ * L.a y₁) * L.a y₂ := by rw [← L.z_central ζ₂ (L.a y₁)]
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          (L.z ζ₁ * L.z ζ₂) * (L.a y₁ * L.a y₂) := by group
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          (L.z ζ₁ * L.z ζ₂) *
            (L.z (muThree D (H.hilb v y₁ y₂)) * L.a (y₁ * y₂)) := by
              rw [hn, L.a_mul]
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          ((L.z ζ₁ * L.z ζ₂) * L.z (muThree D (H.hilb v y₁ y₂))) *
            L.a (y₁ * y₂) := by group
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          L.z (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) * L.a (y₁ * y₂) := by
              rw [← map_mul, ← map_mul]
    _ = borelElem L (x₁ + x₂ * (y₁ : v.adicCompletion F))
          (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) := rfl

private def sphericalBorelAction (T : TorusRep D H v) (s : ℂ)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) :
    T.V →ₗ[ℂ] T.V :=
  ((ζ : ℂˣ) : ℂ) •
    (((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y)

private theorem sphericalBorelAction_mul (T : TorusRep D H v) (s : ℂ)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    sphericalBorelAction T s (x₁ + x₂ * (y₁ : v.adicCompletion F))
        (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) =
      (sphericalBorelAction T s x₁ ζ₁ y₁).comp
        (sphericalBorelAction T s x₂ ζ₂ y₂) := by
  have hpow :
      (absFin v ((y₁ * y₂ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℂ) ^
          ((1 : ℂ) / 2 + s) =
        (absFin v (y₁ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s) *
          (absFin v (y₂ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s) := by
    rw [Units.val_mul, absFin_mul_ind, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg
      (by rw [absFin_eq_norm_ind]; exact norm_nonneg _)
      (by rw [absFin_eq_norm_ind]; exact norm_nonneg _) _
  ext z
  have hσ : T.σa y₁ (T.σa y₂ z) =
      ((muThree D (H.hilb v y₁ y₂) : ℂˣ) : ℂ) • T.σa (y₁ * y₂) z := by
    have h := congrArg (fun f : T.V →ₗ[ℂ] T.V => f z) (T.σa_mul y₁ y₂)
    simpa [LinearMap.comp_apply, LinearMap.smul_apply] using h
  simp only [sphericalBorelAction, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_smul]
  rw [hσ, hpow]
  rw [smul_smul]
  congr 1
  have hroot :
      (((ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂) : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) =
        ((ζ₁ : ℂˣ) : ℂ) * ((ζ₂ : ℂˣ) : ℂ) *
          ((muThree D (H.hilb v y₁ y₂) : ℂˣ) : ℂ) := by simp
  rw [hroot]
  ring

private theorem sphericalBorelAction_unit (T : TorusRep D H v) (B : TameTorusBasis T)
    (s : ℂ) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (hζ : ζ = 1) (hy : IsLocUnit v y) :
    sphericalBorelAction T s x ζ y (B.e 0) = B.e 0 := by
  have hyσ : T.σa y (B.e 0) = B.e 0 := by
    simpa using B.act 0 y hy 0
  simp [sphericalBorelAction, hζ, absFin_one_of_locUnit y hy, hyσ]

private theorem hilb_one_left_ind (b : (v.adicCompletion F)ˣ) : H.hilb v 1 b = 1 := by
  exact H.sixth_power v 1 b ⟨1, by simp⟩

private theorem muThree_mul_ind (ζ ξ : rootsOfUnity 6 F) :
    muThree D (ζ * ξ) = muThree D ζ * muThree D ξ := by
  apply rootsOfUnity.coe_injective
  simp [muThree, map_mul, mul_pow]

private theorem muThree_one_ind : muThree D (1 : rootsOfUnity 6 F) = 1 := by
  apply rootsOfUnity.coe_injective
  simp [muThree]

private theorem muThree_hilb_mul_left_ind (a a' b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v (a * a') b) =
      muThree D (H.hilb v a b) * muThree D (H.hilb v a' b) := by
  rw [H.mul_left, muThree_mul_ind]

private theorem muThree_hilb_mul_right_ind (a b b' : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a (b * b')) =
      muThree D (H.hilb v a b) * muThree D (H.hilb v a b') := by
  rw [H.mul_right, muThree_mul_ind]

private theorem muThree_hilb_inv_left_ind (a b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a⁻¹ b) = (muThree D (H.hilb v a b))⁻¹ := by
  have h := H.mul_left v a a⁻¹ b
  rw [mul_inv_cancel, hilb_one_left_ind] at h
  have hhilb : H.hilb v a b * H.hilb v a⁻¹ b = 1 := h.symm
  have hC : muThree D (H.hilb v a b) * muThree D (H.hilb v a⁻¹ b) = 1 := by
    calc
      _ = muThree D (H.hilb v a b * H.hilb v a⁻¹ b) := (muThree_mul_ind _ _).symm
      _ = muThree D 1 := by rw [hhilb]
      _ = 1 := muThree_one_ind
  exact eq_inv_of_mul_eq_one_right hC

private theorem centralCocycle_coboundary_ind (a b : (v.adicCompletion F)ˣ) :
    (muThree D (H.hilb v a a⁻¹))⁻¹ * muThree D (H.hilb v a⁻¹ b) *
      muThree D (H.hilb v a (a⁻¹ * b)) = 1 := by
  rw [muThree_hilb_inv_left_ind, muThree_hilb_mul_right_ind]
  calc
    (muThree D (H.hilb v a a⁻¹))⁻¹ * (muThree D (H.hilb v a b))⁻¹ *
        (muThree D (H.hilb v a a⁻¹) * muThree D (H.hilb v a b)) =
      (muThree D (H.hilb v a a⁻¹))⁻¹ * muThree D (H.hilb v a a⁻¹) *
        ((muThree D (H.hilb v a b))⁻¹ * muThree D (H.hilb v a b)) := by ac_rfl
    _ = 1 := by simp

private theorem borelElem_inv (L : FinLocalCover D H v) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) :
    (borelElem L x ζ y)⁻¹ =
      borelElem L (-x * (y⁻¹ : v.adicCompletion F))
        (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y⁻¹ := by
  have hx : x + (-x * (y⁻¹ : v.adicCompletion F)) * (y : v.adicCompletion F) = 0 := by
    simp [mul_assoc]
  have hζ : ζ * (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) *
      muThree D (H.hilb v y y⁻¹) = 1 := by group
  have hmul := borelElem_mul L x (-x * (y⁻¹ : v.adicCompletion F)) ζ
    (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y y⁻¹
  have hmul' : borelElem L x ζ y *
      borelElem L (-x * (y⁻¹ : v.adicCompletion F))
        (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y⁻¹ = 1 := by
    rw [hmul]
    simp [borelElem, hx, hζ, mul_assoc, L.a_one]
  exact (eq_inv_of_mul_eq_one_right hmul').symm

private theorem borelElem_inv_mul (L : FinLocalCover D H v)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    (borelElem L x₂ ζ₂ y₂)⁻¹ * borelElem L x₁ ζ₁ y₁ =
      borelElem L ((x₁ - x₂) * (y₂⁻¹ : v.adicCompletion F))
        ((ζ₂⁻¹ * (muThree D (H.hilb v y₂ y₂⁻¹))⁻¹) * ζ₁ *
          muThree D (H.hilb v y₂⁻¹ y₁)) (y₂⁻¹ * y₁) := by
  rw [borelElem_inv, borelElem_mul]
  congr 1
  simp only [Units.val_inv_eq_inv_val]
  ring

private theorem spherical_value_independent (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (s : ℂ) (g : L.L)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) (k₁ k₂ : L.L)
    (hk₁ : k₁ ∈ τ.Kmax) (hg₁ : g = borelElem L x₁ ζ₁ y₁ * k₁)
    (hk₂ : k₂ ∈ τ.Kmax) (hg₂ : g = borelElem L x₂ ζ₂ y₂ * k₂) :
    sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
      sphericalBorelAction T s x₂ ζ₂ y₂ (B.e 0) := by
  let xt : v.adicCompletion F := (x₁ - x₂) * (y₂⁻¹ : v.adicCompletion F)
  let u : (v.adicCompletion F)ˣ := y₂⁻¹ * y₁
  let C₀ := muThree D (H.hilb v y₂ y₂⁻¹)
  let C₁ := muThree D (H.hilb v y₂⁻¹ y₁)
  let C₂ := muThree D (H.hilb v y₂ u)
  let b₁ := borelElem L x₁ ζ₁ y₁
  let b₂ := borelElem L x₂ ζ₂ y₂
  have hrel : b₂⁻¹ * b₁ = k₂ * k₁⁻¹ := by
    calc
      b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * k₁) * k₁⁻¹ := by group
      _ = b₂⁻¹ * g * k₁⁻¹ := by rw [hg₁]
      _ = b₂⁻¹ * (b₂ * k₂) * k₁⁻¹ := by rw [hg₂]
      _ = k₂ * k₁⁻¹ := by group
  have hKrel : b₂⁻¹ * b₁ ∈ τ.Kmax := by
    rw [hrel]
    exact mul_mem hk₂ (inv_mem hk₁)
  have hrelCoords : b₂⁻¹ * b₁ = borelElem L xt
      (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u := by
    simpa [b₁, b₂, xt, u, C₀, C₁, mul_assoc] using
      (borelElem_inv_mul L x₁ x₂ ζ₁ ζ₂ y₁ y₂)
  have hKelem : borelElem L xt (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u ∈ τ.Kmax := by
    rw [← hrelCoords]
    exact hKrel
  obtain ⟨hxt, hu, hξ⟩ :=
    borel_inter_Kmax L τ xt (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u hKelem
  let ξ : rootsOfUnity 3 ℂ := ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁
  have hX : x₂ + xt * (y₂ : v.adicCompletion F) = x₁ := by
    simp [xt, mul_assoc, sub_eq_add_neg]
  have hY : y₂ * u = y₁ := by
    dsimp [u]
    group
  have hcen : C₀⁻¹ * C₁ * C₂ = 1 := by
    simpa [C₀, C₁, C₂, u] using centralCocycle_coboundary_ind y₂ y₁
  have hZ : ζ₂ * ξ * C₂ = ζ₁ := by
    calc
      ζ₂ * ξ * C₂ = (ζ₂ * ζ₂⁻¹) * (C₀⁻¹ * ζ₁ * C₁ * C₂) := by
        dsimp [ξ]
        group
      _ = C₀⁻¹ * ζ₁ * C₁ * C₂ := by simp
      _ = ζ₁ * (C₀⁻¹ * C₁ * C₂) := by
        rw [mul_comm C₀⁻¹ ζ₁]
        group
      _ = ζ₁ := by rw [hcen]; simp
  have hcombined : b₁ = borelElem L (x₂ + xt * (y₂ : v.adicCompletion F))
      (ζ₂ * ξ * C₂) (y₂ * u) := by
    calc
      b₁ = b₂ * (b₂⁻¹ * b₁) := by dsimp [b₁, b₂]; group
      _ = b₂ * borelElem L xt ξ u := by rw [hrelCoords]
      _ = borelElem L (x₂ + xt * (y₂ : v.adicCompletion F)) (ζ₂ * ξ * C₂)
            (y₂ * u) := borelElem_mul L x₂ xt ζ₂ ξ y₂ u
  have hcoords : b₁ = borelElem L x₁ ζ₁ y₁ := by
    simpa only [hX, hZ, hY] using hcombined
  have hactCoords : sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
      sphericalBorelAction T s (x₂ + xt * (y₂ : v.adicCompletion F))
        (ζ₂ * ξ * C₂) (y₂ * u) (B.e 0) := by
    rw [← hX, ← hZ, ← hY]
  have hmul := sphericalBorelAction_mul T s x₂ xt ζ₂ ξ y₂ u
  have hmul0 := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0)) hmul
  calc
    sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
        sphericalBorelAction T s (x₂ + xt * (y₂ : v.adicCompletion F))
          (ζ₂ * ξ * C₂) (y₂ * u) (B.e 0) := hactCoords
    _ = ((sphericalBorelAction T s x₂ ζ₂ y₂).comp
          (sphericalBorelAction T s xt ξ u)) (B.e 0) := hmul0
    _ = sphericalBorelAction T s x₂ ζ₂ y₂
          (sphericalBorelAction T s xt ξ u (B.e 0)) := rfl
    _ = sphericalBorelAction T s x₂ ζ₂ y₂ (B.e 0) := by
          rw [sphericalBorelAction_unit T B s xt ξ u hξ hu]

/-- **ind:spherical** (KP Lemma I.1.3 replaced): at a tame place there is a unique
`Kmax`-invariant section with `f°(1) = e_0`, and every `Kmax`-invariant section is a multiple. -/
theorem spherical_section (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) :
    ∃ f0 : L.L → T.V, IsSection L T s f0 ∧ f0 1 = B.e 0 ∧ (∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) ∧
      ∀ f : L.L → T.V, IsSection L T s f → (∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g) →
        ∃ c : ℂ, f = c • f0 := by
  classical
  choose x y ζ k hk heq using (fun g : L.L => iwasawa_tame L τ g)
  let f0 : L.L → T.V := fun g => sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0)
  have hf0_decomp (g : L.L) (x' : v.adicCompletion F) (ζ' : rootsOfUnity 3 ℂ)
      (y' : (v.adicCompletion F)ˣ) (k' : L.L) (hk' : k' ∈ τ.Kmax)
      (heq' : g = borelElem L x' ζ' y' * k') :
      f0 g = sphericalBorelAction T s x' ζ' y' (B.e 0) := by
    change sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0) = _
    exact spherical_value_independent L τ T B s g (x g) x' (ζ g) ζ' (y g) y' (k g) k'
      (hk g) (heq g) hk' heq'
  have hNcov : ∀ (x₀ : v.adicCompletion F) (y₀ : (v.adicCompletion F)ˣ) (g : L.L),
      f0 (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g) =
        ((absFin v (y₀ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa y₀ (f0 g) := by
    intro x₀ y₀ g
    have hprod : L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
        borelElem L (x g) (ζ g) (y g) =
        borelElem L (x₀ + x g * (y₀ : v.adicCompletion F))
          (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) := by
      simpa [borelElem, L.a_one, mul_assoc] using
        (borelElem_mul L x₀ (x g) 1 (ζ g) y₀ (y g))
    have hdecomp : L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g =
        borelElem L (x₀ + x g * (y₀ : v.adicCompletion F))
          (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) * k g := by
      calc
        L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g =
            L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
              (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) :=
                congrArg (fun q : L.L => L.n (Multiplicative.ofAdd x₀) * L.a y₀ * q) (heq g)
        _ = (L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
              borelElem L (x g) (ζ g) (y g)) * k g := by
                dsimp [borelElem]
                group
        _ = _ := by rw [hprod]
    have hval := hf0_decomp (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g)
      (x₀ + x g * (y₀ : v.adicCompletion F))
      (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (k g) (hk g) hdecomp
    have hact := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0))
      (sphericalBorelAction_mul T s x₀ (x g) 1 (ζ g) y₀ (y g))
    have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
      rw [hilb_one_left_ind]
      exact muThree_one_ind
    have hact' : sphericalBorelAction T s (x₀ + x g * (y₀ : v.adicCompletion F))
        (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (B.e 0) =
      (sphericalBorelAction T s x₀ 1 y₀).comp
        (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := by
      simpa [hmu, mul_assoc] using hact
    calc
      f0 (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g) =
          sphericalBorelAction T s (x₀ + x g * (y₀ : v.adicCompletion F))
            (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (B.e 0) := hval
      _ = (sphericalBorelAction T s x₀ 1 y₀).comp
            (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := hact'
      _ = ((absFin v (y₀ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
            T.σa y₀ (f0 g) := by
              simp [sphericalBorelAction, f0, LinearMap.comp_apply,
                LinearMap.smul_apply, map_smul, smul_smul]
              congr 1
              ring
  have hZcov : ∀ (ζ₀ : rootsOfUnity 3 ℂ) (g : L.L),
      f0 (L.z ζ₀ * g) = ((ζ₀ : ℂˣ) : ℂ) • f0 g := by
    intro ζ₀ g
    have hprod : L.z ζ₀ * borelElem L (x g) (ζ g) (y g) =
        borelElem L (x g) (ζ₀ * ζ g) (y g) := by
      have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
        rw [hilb_one_left_ind]
        exact muThree_one_ind
      simpa [borelElem, L.a_one, hmu, mul_assoc] using
        (borelElem_mul L 0 (x g) ζ₀ (ζ g) 1 (y g))
    have hdecomp : L.z ζ₀ * g = borelElem L (x g) (ζ₀ * ζ g) (y g) * k g := by
      calc
        L.z ζ₀ * g = L.z ζ₀ *
            (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) :=
              congrArg (fun q : L.L => L.z ζ₀ * q) (heq g)
        _ = (L.z ζ₀ * borelElem L (x g) (ζ g) (y g)) * k g := by
              dsimp [borelElem]
              group
        _ = _ := by rw [hprod]
    have hval := hf0_decomp (L.z ζ₀ * g) (x g) (ζ₀ * ζ g) (y g) (k g) (hk g) hdecomp
    have hact := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0))
      (sphericalBorelAction_mul T s 0 (x g) ζ₀ (ζ g) 1 (y g))
    have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
      rw [hilb_one_left_ind]
      exact muThree_one_ind
    have hact' : sphericalBorelAction T s (x g) (ζ₀ * ζ g) (y g) (B.e 0) =
      (sphericalBorelAction T s 0 ζ₀ 1).comp
        (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := by
      simpa [hmu, mul_assoc] using hact
    calc
      f0 (L.z ζ₀ * g) = sphericalBorelAction T s (x g) (ζ₀ * ζ g) (y g) (B.e 0) := hval
      _ = (sphericalBorelAction T s 0 ζ₀ 1).comp
            (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := hact'
      _ = ((ζ₀ : ℂˣ) : ℂ) • f0 g := by
              simp [sphericalBorelAction, f0, LinearMap.comp_apply,
                LinearMap.smul_apply, map_smul, smul_smul, absFin_eq_norm_ind, T.σa_one]
              congr 1
              ring
  have hKfix : ∀ (g : L.L) (k' : L.L), k' ∈ τ.Kmax → f0 (g * k') = f0 g := by
    intro g k' hk'
    have hdecomp : g * k' = borelElem L (x g) (ζ g) (y g) * (k g * k') := by
      calc
        g * k' = (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) * k' :=
          congrArg (fun q : L.L => q * k') (heq g)
        _ = borelElem L (x g) (ζ g) (y g) * (k g * k') := by
          dsimp [borelElem]
          group
    have hknew : k g * k' ∈ τ.Kmax := mul_mem (hk g) hk'
    calc
      f0 (g * k') = sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0) :=
        hf0_decomp (g * k') (x g) (ζ g) (y g) (k g * k') hknew hdecomp
      _ = f0 g := rfl
  have hf0 : IsSection L T s f0 := by
    refine ⟨hNcov, hZcov, ?_⟩
    have hopen : (τ.Kmax : Set L.L) ∈ nhds (1 : L.L) := by
      apply τ.open_.mem_nhds
      simp
    obtain ⟨m, hm, hsub⟩ := L.Kc_nhds _ hopen
    refine ⟨m, hm, ?_⟩
    intro g k' hk'
    exact hKfix g k' (hsub hk')
  have hf01 : f0 1 = B.e 0 := by
    have hdecomp : (1 : L.L) = borelElem L 0 1 1 * 1 := by simp [borelElem, L.a_one]
    calc
      f0 1 = sphericalBorelAction T s 0 1 1 (B.e 0) :=
        hf0_decomp 1 0 1 1 1 (τ.Kmax.one_mem) hdecomp
      _ = B.e 0 := by simp [sphericalBorelAction, absFin_eq_norm_ind, T.σa_one]
  refine ⟨f0, hf0, hf01, hKfix, ?_⟩
  intro f hf hKf
  have hfunit : ∀ u : (v.adicCompletion F)ˣ, IsLocUnit v u → T.σa u (f 1) = f 1 := by
    intro u hu
    have haK : L.a u ∈ τ.Kmax := τ.a_mem u hu.1 hu.2
    have hcov := hf.1 0 u 1
    have hleft : f (L.a u) =
        ((absFin v (u : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa u (f 1) := by simpa using hcov
    have hright : f (L.a u) = f 1 := by simpa using hKf 1 (L.a u) haK
    rw [absFin_one_of_locUnit u hu] at hleft
    simp at hleft
    exact hleft.symm.trans hright
  obtain ⟨c, hc⟩ := tame_unitFixed T B hv (f 1) hfunit
  have hfvalue (g : L.L) : f g =
      sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := by
    have horder : borelElem L (x g) (ζ g) (y g) * k g =
        L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) := by
      dsimp [borelElem]
      calc
        (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g)) * k g =
            (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g)) * (L.a (y g) * k g) := by group
        _ = (L.z (ζ g) * L.n (Multiplicative.ofAdd (x g))) * (L.a (y g) * k g) := by
              rw [← L.z_central (ζ g)]
        _ = L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) := by group
    calc
      f g = f (borelElem L (x g) (ζ g) (y g) * k g) :=
        congrArg f (heq g)
      _ = f (L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g)) := by rw [horder]
      _ = ((ζ g : ℂˣ) : ℂ) • f (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) :=
            hf.2.1 (ζ g) _
      _ = ((ζ g : ℂˣ) : ℂ) •
            (((absFin v (y g : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa (y g) (f (k g))) := by rw [hf.1 (x g) (y g) (k g)]
      _ = sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := by
            have hfk : f (k g) = f 1 := by simpa using hKf 1 (k g) (hk g)
            rw [hfk]
            rfl
  refine ⟨c, funext ?_⟩
  intro g
  calc
    f g = sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := hfvalue g
    _ = sphericalBorelAction T s (x g) (ζ g) (y g) (c • B.e 0) := by rw [hc]
    _ = c • f0 g := by simp [f0, map_smul]

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
  classical
  unfold bigCell
  split
  · rename_i h
    let x₀ := h.choose
    let ζ₀ := h.choose_spec.choose
    let y₀ := h.choose_spec.choose_spec.choose
    let t₀ := h.choose_spec.choose_spec.choose_spec.choose
    have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
    have hcoords := bigCell_coords_unique L x₀ x ζ₀ ζ y₀ y t₀ t hdecomp.symm
    rcases hcoords with ⟨hx, hy, ht, hζ⟩
    let eval : (v.adicCompletion F ×
        (rootsOfUnity 3 ℂ × ((v.adicCompletion F)ˣ × v.adicCompletion F))) → T.V :=
      fun q => ((q.2.1 : ℂˣ) : ℂ) •
        ((absFin v q.2.2.1 : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa q.2.2.1 (φ q.2.2.2)
    have htuple : (x₀, (ζ₀, (y₀, t₀))) = (x, (ζ, (y, t))) := by
      apply Prod.ext
      · exact hx
      · apply Prod.ext
        · exact hζ
        · apply Prod.ext
          · exact hy
          · exact ht
    change eval (x₀, (ζ₀, (y₀, t₀))) = eval (x, (ζ, (y, t)))
    exact congrArg eval htuple
  · rename_i h
    exact False.elim (h ⟨x, ζ, y, t, rfl⟩)

theorem bigCell_borel (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := by
  classical
  unfold bigCell
  split_ifs with h
  · let x₀ := h.choose
    let ζ₀ := h.choose_spec.choose
    let y₀ := h.choose_spec.choose_spec.choose
    let t₀ := h.choose_spec.choose_spec.choose_spec.choose
    have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
    exact (bigcell_ne_borel L x₀ x ζ₀ ζ y₀ y t₀ hdecomp.symm).elim
  · rfl

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
