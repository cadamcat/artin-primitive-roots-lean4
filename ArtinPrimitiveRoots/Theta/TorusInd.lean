import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Cover
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

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

private theorem bigCell_eval_decomp (L : FinLocalCover D H v) (T : TorusRep D H v)
    (s : ℂ) (φ : v.adicCompletion F → T.V) (g : L.L)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (t : v.adicCompletion F)
    (h : g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
      L.n (Multiplicative.ofAdd t)) :
    bigCell L T s φ g =
      ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
  classical
  unfold bigCell
  split
  · rename_i h'
    let x₀ := h'.choose
    let ζ₀ := h'.choose_spec.choose
    let y₀ := h'.choose_spec.choose_spec.choose
    let t₀ := h'.choose_spec.choose_spec.choose_spec.choose
    have hdecomp := h'.choose_spec.choose_spec.choose_spec.choose_spec
    have hcoords := bigCell_coords_unique L x₀ x ζ₀ ζ y₀ y t₀ t (hdecomp.symm.trans h)
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
  · rename_i h'
    exact False.elim (h' ⟨x, ζ, y, t, h⟩)

private theorem adicCompletion_toCompletion_inv_ind (x : v.adicCompletion F) :
    (x⁻¹).toCompletion = x.toCompletion⁻¹ := by
  exact map_inv₀ (HeightOneSpectrum.adicCompletion.equiv F v) x

private theorem adicCompletion_toCompletion_add_ind (x y : v.adicCompletion F) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := by
  exact map_add (HeightOneSpectrum.adicCompletion.equiv F v) x y

private theorem adicCompletion_toCompletion_mul_ind (x y : v.adicCompletion F) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := by
  exact map_mul (HeightOneSpectrum.adicCompletion.equiv F v) x y

private theorem adicCompletion_toCompletion_divUnit_ind (x : v.adicCompletion F)
    (y : (v.adicCompletion F)ˣ) :
    (x / y).toCompletion = x.toCompletion / (y : v.adicCompletion F).toCompletion := by
  simp only [div_eq_mul_inv, adicCompletion_toCompletion_mul_ind,
    adicCompletion_toCompletion_inv_ind]

private theorem adicCompletion_toCompletion_unitMul_ind (x y : (v.adicCompletion F)ˣ) :
    ((x * y : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      (x : v.adicCompletion F).toCompletion * (y : v.adicCompletion F).toCompletion := by
  simpa using adicCompletion_toCompletion_mul_ind (F := F) (v := v)
    (x : v.adicCompletion F) (y : v.adicCompletion F)

private theorem adicCompletion_toCompletion_unitInv_ind (x : (v.adicCompletion F)ˣ) :
    ((x⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      ((x : v.adicCompletion F).toCompletion)⁻¹ := by
  simpa using adicCompletion_toCompletion_inv_ind (F := F) (v := v)
    (x : v.adicCompletion F)

private theorem adicCompletion_toCompletion_unitDiv_ind (x y : (v.adicCompletion F)ˣ) :
    ((x / y : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      (x : v.adicCompletion F).toCompletion / (y : v.adicCompletion F).toCompletion := by
  rw [div_eq_mul_inv, adicCompletion_toCompletion_unitMul_ind,
    adicCompletion_toCompletion_unitInv_ind]
  rfl

private theorem adicCompletion_toCompletion_unitPow_two_ind (x : (v.adicCompletion F)ˣ) :
    ((x ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      ((x : v.adicCompletion F).toCompletion) ^ 2 := by
  rw [pow_two, adicCompletion_toCompletion_unitMul_ind]
  rw [pow_two]

private theorem bigCell_matrix_topRight (a b c d : v.adicCompletion F) (hc : c ≠ 0) :
    b.toCompletion * c.toCompletion⁻¹ =
      (a.toCompletion * c.toCompletion⁻¹) * (d.toCompletion * c.toCompletion⁻¹) +
        (b.toCompletion * c.toCompletion - a.toCompletion * d.toCompletion) *
          (c.toCompletion ^ 2)⁻¹ := by
  have hc' : c.toCompletion ≠ 0 :=
    (map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 hc
  field_simp [hc']
  ring

private theorem gl2_bruhat (G : GL (Fin 2) (v.adicCompletion F)) :
    (∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
      (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
        QuotientGroup.mk (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y)) ∨
    (∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
      ∃ t : v.adicCompletion F,
        (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
          QuotientGroup.mk (bigCellMatrix (F := F) x y t)) := by
  classical
  let K := v.adicCompletion F
  let M : Matrix (Fin 2) (Fin 2) K := G
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      intro hd
      apply G.det_ne_zero
      rw [Matrix.det_fin_two]
      change a * d - b * c = 0
      rw [hc, hd]
      ring
    have ha : a ≠ 0 := by
      intro ha
      apply G.det_ne_zero
      rw [Matrix.det_fin_two]
      change a * d - b * c = 0
      rw [hc, ha]
      ring
    let du : Kˣ := Units.mk0 d hd
    have hdi : d⁻¹ ≠ 0 := inv_ne_zero hd
    let x : K := b * d⁻¹
    let y : Kˣ := Units.mk0 (a * d⁻¹) (mul_ne_zero ha hdi)
    have hmat : G * Matrix.GeneralLinearGroup.scalar (Fin 2) du⁻¹ =
        upperM K x * diagM K y := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [M, a, b, c, d, x, y, du, upperM, diagM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          hc, Units.val_inv_eq_inv_val] <;>
          exact (adicCompletion_toCompletion_mul_ind
            ((G : Matrix (Fin 2) (Fin 2) K) 0 0)
            ((G : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹).symm
      · simp [M, a, b, c, d, x, y, du, upperM, diagM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          hc, Units.val_inv_eq_inv_val] <;>
          exact (adicCompletion_toCompletion_mul_ind
            ((G : Matrix (Fin 2) (Fin 2) K) 0 1)
            ((G : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹).symm
      · simp [M, a, b, c, d, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Fin.sum_univ_two, hc]
      · simp [M, a, b, c, d, du, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Fin.sum_univ_two, hc]
        rw [adicCompletion_toCompletion_inv_ind]
        exact div_self ((map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 hd)
    have hclass : (QuotientGroup.mk G : PGL2 K) =
        QuotientGroup.mk (upperM K x * diagM K y) := by
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      exact ⟨du⁻¹, hmat⟩
    exact Or.inl ⟨x, y, hclass⟩
  · have hcne : c ≠ 0 := hc
    let cu : Kˣ := Units.mk0 c hcne
    let detG : K := M.det
    have hdet : detG ≠ 0 := by
      exact G.det_ne_zero
    have hci : c⁻¹ ≠ 0 := inv_ne_zero (a := c) hcne
    let x : K := a * c⁻¹
    let t : K := d * c⁻¹
    let y : Kˣ := Units.mk0 (-detG * c⁻¹ ^ 2)
      (mul_ne_zero (neg_ne_zero.mpr hdet) (pow_ne_zero 2 hci))
    have hmat : G * Matrix.GeneralLinearGroup.scalar (Fin 2) cu⁻¹ =
        bigCellMatrix (F := F) x y t := by
      ext i j
      fin_cases i <;> fin_cases j
      · try simp [M, a, b, c, d, x, y, t, detG, cu, bigCellMatrix, upperM, diagM, weylM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          Units.val_inv_eq_inv_val, Matrix.det_fin_two]
        try simp only [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
        try exact (adicCompletion_toCompletion_mul_ind a c⁻¹).symm
      · try simp [M, a, b, c, d, x, y, t, detG, cu, bigCellMatrix, upperM, diagM, weylM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          Units.val_inv_eq_inv_val, Matrix.det_fin_two]
        try simp only [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
        try exact bigCell_matrix_topRight a b c d hcne
      · simp [M, a, b, c, d, cu, bigCellMatrix, upperM, diagM, weylM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          Units.val_inv_eq_inv_val, Matrix.det_fin_two]
        rw [adicCompletion_toCompletion_inv_ind]
        exact div_self ((map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 hcne)
      · try simp [M, a, b, c, d, x, y, t, detG, cu, bigCellMatrix, upperM, diagM, weylM,
          Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
          Units.val_inv_eq_inv_val, Matrix.det_fin_two]
        try simp only [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
        try exact (adicCompletion_toCompletion_mul_ind d c⁻¹).symm
    have hclass : (QuotientGroup.mk G : PGL2 K) =
        QuotientGroup.mk (bigCellMatrix (F := F) x y t) := by
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      exact ⟨cu⁻¹, hmat⟩
    exact Or.inr ⟨x, y, t, hclass⟩

private theorem lift_pr_eq (L : FinLocalCover D H v) (g a : L.L)
    (hpr : L.pr g = L.pr a) : ∃ ζ : rootsOfUnity 3 ℂ, g = L.z ζ * a := by
  let q : L.L := a⁻¹ * g
  have hqker : q ∈ L.pr.ker := by
    change L.pr (a⁻¹ * g) = 1
    calc
      L.pr (a⁻¹ * g) = (L.pr a)⁻¹ * L.pr g := by simp only [map_mul, map_inv]
      _ = 1 := by rw [← hpr]; simp
  rw [L.pr_ker] at hqker
  obtain ⟨ζ, hζ⟩ := hqker
  refine ⟨ζ, ?_⟩
  calc
    g = a * q := by dsimp [q]; group
    _ = a * L.z ζ := by rw [← hζ]
    _ = L.z ζ * a := (L.z_central ζ a).symm

private theorem bigCell_bruhat_cover (L : FinLocalCover D H v) (g : L.L) :
    (∃ x ζ y, g = borelElem L x ζ y) ∨
    (∃ x ζ y t, g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
      L.n (Multiplicative.ofAdd t)) := by
  obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective (L.pr g)
  cases gl2_bruhat (F := F) G with
  | inl hsmall =>
    obtain ⟨x, y, hclass⟩ := hsmall
    let b : L.L := L.n (Multiplicative.ofAdd x) * L.a y
    have hprb : L.pr b = QuotientGroup.mk (upperM (v.adicCompletion F) x *
        diagM (v.adicCompletion F) y) := by
      simp [b, map_mul, L.pr_n, L.pr_a]
    have hpr : L.pr g = L.pr b := by
      calc
        L.pr g = QuotientGroup.mk G := hG.symm
        _ = QuotientGroup.mk (upperM (v.adicCompletion F) x *
              diagM (v.adicCompletion F) y) := hclass
        _ = L.pr b := hprb.symm
    obtain ⟨ζ, hg⟩ := lift_pr_eq L g b hpr
    have hnorm : L.z ζ * b = borelElem L x ζ y := by
      dsimp [b, borelElem]
      calc
        L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
            (L.z ζ * L.n (Multiplicative.ofAdd x)) * L.a y := by group
        _ = (L.n (Multiplicative.ofAdd x) * L.z ζ) * L.a y := by
              rw [L.z_central ζ]
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y := by group
    exact Or.inl ⟨x, ζ, y, hg.trans hnorm⟩
  | inr hbig =>
    obtain ⟨x, y, t, hclass⟩ := hbig
    let b : L.L := L.n (Multiplicative.ofAdd x) * L.a y * L.w *
      L.n (Multiplicative.ofAdd t)
    have hprb : L.pr b = QuotientGroup.mk (bigCellMatrix (F := F) x y t) := by
      simp [b, bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w]
    have hpr : L.pr g = L.pr b := by
      calc
        L.pr g = QuotientGroup.mk G := hG.symm
        _ = QuotientGroup.mk (bigCellMatrix (F := F) x y t) := hclass
        _ = L.pr b := hprb.symm
    obtain ⟨ζ, hg⟩ := lift_pr_eq L g b hpr
    have hnorm : L.z ζ * b =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t) := by
      dsimp [b]
      calc
        L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y * L.w *
            L.n (Multiplicative.ofAdd t)) =
            (L.z ζ * L.n (Multiplicative.ofAdd x)) * L.a y * L.w *
              L.n (Multiplicative.ofAdd t) := by group
        _ = (L.n (Multiplicative.ofAdd x) * L.z ζ) * L.a y * L.w *
              L.n (Multiplicative.ofAdd t) := by rw [L.z_central ζ]
        _ = _ := by group
    exact Or.inr ⟨x, ζ, y, t, hg.trans hnorm⟩

private theorem bigCell_leftBorel (L : FinLocalCover D H v) (T : TorusRep D H v)
    (s : ℂ) (φ : v.adicCompletion F → T.V)
    (x₀ : v.adicCompletion F) (ζ₀ : rootsOfUnity 3 ℂ) (y₀ : (v.adicCompletion F)ˣ)
    (g : L.L) :
    bigCell L T s φ (borelElem L x₀ ζ₀ y₀ * g) =
      sphericalBorelAction T s x₀ ζ₀ y₀ (bigCell L T s φ g) := by
  classical
  by_cases hg : ∃ x ζ y t,
      g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)
  · obtain ⟨x, ζ, y, t, hdecomp⟩ := hg
    let x' := x₀ + x * (y₀ : v.adicCompletion F)
    let ζ' := ζ₀ * ζ * muThree D (H.hilb v y₀ y)
    let y' := y₀ * y
    have hprod : borelElem L x₀ ζ₀ y₀ * g =
        L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y' * L.w *
          L.n (Multiplicative.ofAdd t) := by
      calc
        borelElem L x₀ ζ₀ y₀ * g =
            (borelElem L x₀ ζ₀ y₀ * borelElem L x ζ y) * L.w *
              L.n (Multiplicative.ofAdd t) := by rw [hdecomp]; dsimp [borelElem]; group
        _ = borelElem L x' ζ' y' * L.w * L.n (Multiplicative.ofAdd t) := by
              rw [borelElem_mul]
        _ = _ := rfl
    calc
      bigCell L T s φ (borelElem L x₀ ζ₀ y₀ * g) =
          ((ζ' : ℂˣ) : ℂ) • ((absFin v y' : ℂ) ^ ((1 : ℂ) / 2 + s)) •
            T.σa y' (φ t) := bigCell_eval_decomp L T s φ _ x' ζ' y' t hprod
      _ = sphericalBorelAction T s x₀ ζ₀ y₀ (bigCell L T s φ g) := by
          rw [bigCell_eval_decomp L T s φ g x ζ y t hdecomp]
          have hmul := sphericalBorelAction_mul T s x₀ x ζ₀ ζ y₀ y
          have happly := congrArg (fun A : T.V →ₗ[ℂ] T.V => A (φ t)) hmul
          simpa [x', ζ', y', sphericalBorelAction, LinearMap.comp_apply,
            LinearMap.smul_apply, map_smul, smul_smul] using happly
  · have hleft : ¬ ∃ x ζ y t,
        borelElem L x₀ ζ₀ y₀ * g =
          L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
            L.n (Multiplicative.ofAdd t) := by
      intro hnew
      obtain ⟨x, ζ, y, t, hnew⟩ := hnew
      let yi := y₀⁻¹
      let xi := -x₀ * (yi : v.adicCompletion F)
      let ζi := ζ₀⁻¹ * (muThree D (H.hilb v y₀ y₀⁻¹))⁻¹
      have hdecomp : g = borelElem L
          (xi + x * (yi : v.adicCompletion F))
          (ζi * ζ * muThree D (H.hilb v yi y)) (yi * y) *
            L.w * L.n (Multiplicative.ofAdd t) := by
        calc
          g = (borelElem L x₀ ζ₀ y₀)⁻¹ *
              (borelElem L x₀ ζ₀ y₀ * g) := by group
          _ = (borelElem L x₀ ζ₀ y₀)⁻¹ *
              (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
                L.n (Multiplicative.ofAdd t)) := by rw [hnew]
          _ = ((borelElem L x₀ ζ₀ y₀)⁻¹ * borelElem L x ζ y) *
                L.w * L.n (Multiplicative.ofAdd t) := by
                  dsimp [borelElem]
                  group
          _ = borelElem L xi ζi yi * borelElem L x ζ y *
                L.w * L.n (Multiplicative.ofAdd t) := by
                  rw [borelElem_inv]
                  dsimp [xi, ζi, yi]
                  simpa only [Units.val_inv_eq_inv_val]
          _ = borelElem L (xi + x * (yi : v.adicCompletion F))
                (ζi * ζ * muThree D (H.hilb v yi y)) (yi * y) *
                  L.w * L.n (Multiplicative.ofAdd t) := by rw [borelElem_mul]
      exact hg ⟨xi + x * (yi : v.adicCompletion F),
        ζi * ζ * muThree D (H.hilb v yi y), yi * y, t, by
          simpa [borelElem] using hdecomp⟩
    unfold bigCell
    rw [dif_neg hleft, dif_neg hg]
    simp [sphericalBorelAction]

private theorem muThree_hilb_one_of_sigmaa_id
    (T : TorusRep D H v) [Nontrivial T.V] (a u : (v.adicCompletion F)ˣ)
    (hu : T.σa u = LinearMap.id) : muThree D (H.hilb v a u) = 1 := by
  let C₁ := muThree D (H.hilb v a u)
  let C₂ := muThree D (H.hilb v u a)
  have h1 : T.σa a = ((C₁ : ℂˣ) : ℂ) • T.σa (a * u) := by
    simpa [C₁, hu] using T.σa_mul a u
  have h2 : T.σa a = ((C₂ : ℂˣ) : ℂ) • T.σa (a * u) := by
    simpa [C₂, hu, mul_comm u a] using T.σa_mul u a
  have hσa : T.σa a ≠ 0 := by
    intro hz
    obtain ⟨w, hw⟩ := exists_ne (0 : T.V)
    have h := congrArg (fun A : T.V →ₗ[ℂ] T.V => A w) (T.σa_mul a a⁻¹)
    have hc : (((muThree D (H.hilb v a a⁻¹) : ℂˣ) : ℂ)) ≠ 0 := by simp
    have hwzero : ((muThree D (H.hilb v a a⁻¹) : ℂˣ) : ℂ) • w = 0 := by
      simpa [hz, T.σa_one, LinearMap.comp_apply, LinearMap.smul_apply] using h.symm
    exact hw ((smul_eq_zero.mp hwzero).resolve_left hc)
  have hM : T.σa (a * u) ≠ 0 := by
    intro hzero
    apply hσa
    rw [h1, hzero]
    simp
  have hCval : ((C₁ : ℂˣ) : ℂ) = ((C₂ : ℂˣ) : ℂ) := by
    apply (smul_left_injective ℂ hM)
    calc
      ((C₁ : ℂˣ) : ℂ) • T.σa (a * u) = T.σa a := h1.symm
      _ = ((C₂ : ℂˣ) : ℂ) • T.σa (a * u) := h2
  have hC : C₁ = C₂ := by
    apply Subtype.ext
    exact Units.ext hCval
  have hprod : C₁ * C₂ = 1 := by
    calc
      C₁ * C₂ = muThree D (H.hilb v a u * H.hilb v u a) :=
        (muThree_mul_ind _ _).symm
      _ = muThree D 1 := by rw [H.skew]
      _ = 1 := muThree_one_ind
  rw [← hC] at hprod
  have hsq : C₁ ^ 2 = 1 := by simpa [pow_two] using hprod
  have hcubeVal : (C₁ : ℂˣ) ^ 3 = 1 := by
    change (C₁ : ℂˣ) ^ 3 = 1
    exact C₁.property
  have hcube : C₁ ^ 3 = 1 := by
    apply Subtype.ext
    exact hcubeVal
  calc
    C₁ = C₁ ^ 3 * (C₁ ^ 2)⁻¹ := by group
    _ = 1 := by rw [hcube, hsq]; simp

private theorem muThree_hilb_one_left_of_sigmaa_id
    (T : TorusRep D H v) [Nontrivial T.V] (a : (v.adicCompletion F)ˣ)
    (ha : T.σa a = LinearMap.id) (u : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a u) = 1 := by
  have hright := muThree_hilb_one_of_sigmaa_id T u a ha
  have hskew := H.skew v a u
  have hprod : muThree D (H.hilb v a u) * muThree D (H.hilb v u a) = 1 := by
    calc
      _ = muThree D (H.hilb v a u * H.hilb v u a) :=
        (muThree_mul_ind _ _).symm
      _ = muThree D 1 := by rw [hskew]
      _ = 1 := muThree_one_ind
  simpa [hright] using hprod

private theorem muThree_hilb_sq_eq_one_ind (z : rootsOfUnity 6 F)
    (hz : z ^ 2 = 1) : muThree D z = 1 := by
  apply rootsOfUnity.coe_injective
  change D.σ0 ((((z ^ 2 : rootsOfUnity 6 F) : Fˣ) : F)) = 1
  rw [hz]
  simp

private theorem hilb_one_right_ind (a : (v.adicCompletion F)ˣ) :
    H.hilb v a 1 = 1 := by
  have h := H.skew v a 1
  rw [hilb_one_left_ind] at h
  simpa using h

private theorem muThree_hilb_one_right_ind (a : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a 1) = 1 := by
  rw [hilb_one_right_ind, muThree_one_ind]

private theorem muThree_hilb_one_left_ind (b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v 1 b) = 1 := by
  rw [hilb_one_left_ind, muThree_one_ind]

private theorem muThree_hilb_self_one_ind (a : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a a) = 1 := by
  have h := H.skew v a a
  have hsq : H.hilb v a a ^ 2 = 1 := by simpa [pow_two] using h
  exact muThree_hilb_sq_eq_one_ind _ hsq

private theorem muThree_hilb_neg_one_right_ind (a : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a (-1)) = 1 := by
  have h := H.mul_right v a (-1) (-1)
  have hneg : (-1 : (v.adicCompletion F)ˣ) * (-1) = 1 := by
    ext
    simp
  rw [hneg, hilb_one_right_ind a] at h
  have hsq : H.hilb v a (-1) ^ 2 = 1 := by simpa [pow_two] using h.symm
  exact muThree_hilb_sq_eq_one_ind _ hsq

private theorem xU_upperM_ind (x : v.adicCompletion F) :
    xU v (upperM (v.adicCompletion F) x) = 1 := by
  apply Units.ext
  simp [xU, xEntry, upperM]

private theorem xU_lower_upper_ind (x y : v.adicCompletion F) :
    xU v (lowerM (v.adicCompletion F) x * upperM (v.adicCompletion F) y) =
      xU v (lowerM (v.adicCompletion F) x) := by
  apply Units.ext
  by_cases hx : x = 0 <;>
    simp [xU, xEntry, lowerM, upperM, Matrix.mul_apply, Fin.sum_univ_two, hx]

private theorem kpCocycle_lower_upper_ind (x y : v.adicCompletion F) :
    kpCocycle D H v (lowerM (v.adicCompletion F) x) (upperM (v.adicCompletion F) y) = 1 := by
  have hx := xU_lower_upper_ind (F := F) (v := v) x y
  have hy := xU_upperM_ind (F := F) (v := v) y
  have hdx : detU v (lowerM (v.adicCompletion F) x) = 1 := by
    apply Units.ext
    simp [detU, lowerM, Matrix.det_fin_two]
  have hdy : detU v (upperM (v.adicCompletion F) y) = 1 := by
    apply Units.ext
    simp [detU, upperM, Matrix.det_fin_two]
  rw [kpCocycle, hx, hy, hdx, hdy]
  simp [muThree_hilb_one_right_ind]

private theorem kpCocycle_lower_upper_w_ind (T : TorusRep D H v) [Nontrivial T.V]
    (x y : v.adicCompletion F) (A : (v.adicCompletion F)ˣ)
    (hA : (A : v.adicCompletion F) = 1 + x * y)
    (hσ : T.σa A = LinearMap.id) :
    kpCocycle D H v
      (lowerM (v.adicCompletion F) x * upperM (v.adicCompletion F) y)
      (weylM (v.adicCompletion F)) = 1 := by
  have hx : xU v (weylM (v.adicCompletion F)) = 1 := by
    apply Units.ext
    simp [xU, xEntry, weylM]
  have hdet : detU v
      (lowerM (v.adicCompletion F) x * upperM (v.adicCompletion F) y) = 1 := by
    apply Units.ext
    simp [detU, lowerM, upperM, Matrix.det_fin_two]
  have hprod : xU v
      (lowerM (v.adicCompletion F) x * upperM (v.adicCompletion F) y *
        weylM (v.adicCompletion F)) = A := by
    have hAne : x * y + 1 ≠ 0 := by
      have hAne' : 1 + x * y ≠ 0 := by rw [← hA]; exact A.ne_zero
      simpa [add_comm] using hAne'
    apply Units.ext
    simp [xU, xEntry, lowerM, upperM, weylM, Matrix.mul_apply, Fin.sum_univ_two,
      hA, hAne]
    ring
  rw [kpCocycle, hprod, hx, hdet]
  have hfirst := muThree_hilb_one_left_of_sigmaa_id T A hσ
    (A / xU v (lowerM (v.adicCompletion F) x * upperM (v.adicCompletion F) y))
  have hsecond := muThree_hilb_one_left_ind (D := D) (H := H) (v := v)
    (detU v (weylM (v.adicCompletion F)))
  simp only [one_mul, div_one]
  rw [hfirst, hsecond]
  simp

private theorem muThree_hilb_inv_right_ind (a b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a b⁻¹) = (muThree D (H.hilb v a b))⁻¹ := by
  have h := H.mul_right v a b b⁻¹
  rw [mul_inv_cancel, hilb_one_right_ind a] at h
  have hprod : H.hilb v a b * H.hilb v a b⁻¹ = 1 := h.symm
  have hC : muThree D (H.hilb v a b) * muThree D (H.hilb v a b⁻¹) = 1 := by
    calc
      _ = muThree D (H.hilb v a b * H.hilb v a b⁻¹) :=
        (muThree_mul_ind _ _).symm
      _ = muThree D 1 := by rw [hprod]
      _ = 1 := muThree_one_ind
  exact eq_inv_of_mul_eq_one_right hC

private theorem muThree_hilb_square_inv_square_ind (a : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v (a ^ 2) (a⁻¹ * a⁻¹)) = 1 := by
  have hself := muThree_hilb_self_one_ind (D := D) (H := H) (v := v) a
  have hinv : muThree D (H.hilb v a a⁻¹) = 1 := by
    calc
      _ = (muThree D (H.hilb v a a))⁻¹ :=
        muThree_hilb_inv_right_ind (D := D) (H := H) (v := v) a a
      _ = 1 := by simp [hself]
  have hpowleft : muThree D (H.hilb v (a ^ 2) a⁻¹) = 1 := by
    rw [show a ^ 2 = a * a by simp [pow_two], muThree_hilb_mul_left_ind]
    simp [hinv]
  rw [muThree_hilb_mul_right_ind]
  simp [hpowleft]

private theorem kpCocycle_upper_diag_ind (x : v.adicCompletion F)
    (y : (v.adicCompletion F)ˣ) :
    kpCocycle D H v (upperM (v.adicCompletion F) x) (diagM (v.adicCompletion F) y) = 1 := by
  have hx : xU v (upperM (v.adicCompletion F) x) = 1 := xU_upperM_ind x
  have hy : xU v (diagM (v.adicCompletion F) y) = 1 := by
    apply Units.ext
    simp [xU, xEntry, diagM]
  have hxy : xU v (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y) = 1 := by
    apply Units.ext
    simp [xU, xEntry, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdetx : detU v (upperM (v.adicCompletion F) x) = 1 := by
    apply Units.ext
    simp [detU, upperM, Matrix.det_fin_two]
  rw [kpCocycle, hx, hy, hxy, hdetx]
  simp [muThree_hilb_one_left_ind]

private theorem kpCocycle_upper_diag_w_ind (x : v.adicCompletion F)
    (y : (v.adicCompletion F)ˣ) :
    kpCocycle D H v (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y)
      (weylM (v.adicCompletion F)) = 1 := by
  have hx : xU v (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y) = 1 := by
    apply Units.ext
    simp [xU, xEntry, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
  have hy : xU v (weylM (v.adicCompletion F)) = 1 := by
    apply Units.ext
    simp [xU, xEntry, weylM]
  have hxy : xU v
      (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
        weylM (v.adicCompletion F)) = 1 := by
    apply Units.ext
    simp [xU, xEntry, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdetx : detU v (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y) = y := by
    apply Units.ext
    simp [detU, upperM, diagM, Matrix.det_fin_two]
  have hdetw : detU v (weylM (v.adicCompletion F)) = -1 := by
    apply Units.ext
    simp [detU, weylM, Matrix.det_fin_two]
  rw [kpCocycle, hx, hy, hxy]
  rw [hdetx, hdetw]
  simp [muThree_hilb_one_right_ind, muThree_hilb_neg_one_right_ind]

private theorem kpCocycle_upper_diag_w_upper_ind (x : v.adicCompletion F)
    (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F) :
    kpCocycle D H v
      (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
        weylM (v.adicCompletion F))
      (upperM (v.adicCompletion F) t) = 1 := by
  have hx : xU v
      (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
        weylM (v.adicCompletion F)) = 1 := by
    apply Units.ext
    simp [xU, xEntry, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two]
  have hy : xU v (upperM (v.adicCompletion F) t) = 1 := xU_upperM_ind t
  have hxy : xU v
      (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
        weylM (v.adicCompletion F) * upperM (v.adicCompletion F) t) = 1 := by
    apply Units.ext
    simp [xU, xEntry, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdetx : detU v
      (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
        weylM (v.adicCompletion F)) = -y := by
    apply Units.ext
    simp [detU, upperM, diagM, weylM, Matrix.det_fin_two]
  have hdety : detU v (upperM (v.adicCompletion F) t) = 1 := by
    apply Units.ext
    simp [detU, upperM, Matrix.det_fin_two]
  rw [kpCocycle, hx, hy, hxy, hdety]
  simp [hdetx, muThree_hilb_one_right_ind]

private theorem muThree_hilb_square_neg_square_ind (a : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v (a ^ 2) (-(a⁻¹ * a⁻¹))) = 1 := by
  have hneg := muThree_hilb_neg_one_right_ind (D := D) (H := H) (v := v) (a ^ 2)
  have hpow := muThree_hilb_square_inv_square_ind (D := D) (H := H) (v := v) a
  have hmul := muThree_hilb_mul_right_ind (D := D) (H := H) (v := v)
    (a ^ 2) (-1) (a⁻¹ * a⁻¹)
  have hnegmul : (-1 : (v.adicCompletion F)ˣ) * (a⁻¹ * a⁻¹) =
      -(a⁻¹ * a⁻¹) := by simp
  rw [← hnegmul, hmul, hneg, hpow]
  simp

private theorem kpCocycle_scalar_upper_diag_w_upper_ind
    (a : (v.adicCompletion F)ˣ) (b r : v.adicCompletion F) :
    kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) a)
      (upperM (v.adicCompletion F) b * diagM (v.adicCompletion F) (a⁻¹ * a⁻¹) *
        weylM (v.adicCompletion F) * upperM (v.adicCompletion F) r) = 1 := by
  let M := upperM (v.adicCompletion F) b * diagM (v.adicCompletion F) (a⁻¹ * a⁻¹) *
    weylM (v.adicCompletion F) * upperM (v.adicCompletion F) r
  have hx : xU v (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = a := by
    apply Units.ext
    simp [xU, xEntry, Matrix.GeneralLinearGroup.scalar]
  have hxm : xU v M = 1 := by
    apply Units.ext
    simp [M, xU, xEntry, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two]
  have hxprod : xU v (Matrix.GeneralLinearGroup.scalar (Fin 2) a * M) = a := by
    apply Units.ext
    simp [M, xU, xEntry, upperM, diagM, weylM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, a.ne_zero]
  have hdets : detU v (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = a ^ 2 := by
    apply Units.ext
    simp [detU, Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two]
  have hdetm : detU v M = -(a⁻¹ * a⁻¹) := by
    apply Units.ext
    simp [M, detU, upperM, diagM, weylM, Matrix.det_fin_two]
  rw [kpCocycle, hx, hxm, hxprod, hdets, hdetm]
  have hratio : a / a ^ 2 = a⁻¹ := by
    apply Units.ext
    simp [div_eq_mul_inv, pow_two]
  have hratio' : a / a = 1 := by
    rw [div_eq_mul_inv]
    exact mul_inv_cancel a
  simp only [one_mul]
  rw [hratio, hratio']
  rw [muThree_hilb_one_right_ind, muThree_hilb_square_neg_square_ind]
  simp

private theorem lower_upper_w_matrix_gauss (q c : v.adicCompletion F)
    (A : (v.adicCompletion F)ˣ) (hA : (A : v.adicCompletion F) = 1 + q * c) :
    lowerM (v.adicCompletion F) q * upperM (v.adicCompletion F) c *
        weylM (v.adicCompletion F) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) A *
        (upperM (v.adicCompletion F) (c / A) *
          diagM (v.adicCompletion F) (A⁻¹ * A⁻¹) *
          weylM (v.adicCompletion F) * upperM (v.adicCompletion F) (q / A)) := by
  have hAto : (A : v.adicCompletion F).toCompletion =
      1 + q.toCompletion * c.toCompletion := by
    calc
      _ = (1 + q * c).toCompletion := congrArg (fun z : v.adicCompletion F => z.toCompletion) hA
      _ = 1 + q.toCompletion * c.toCompletion := by
        rw [adicCompletion_toCompletion_add_ind, adicCompletion_toCompletion_mul_ind]
        simp
  have hAto_ne : (A : v.adicCompletion F).toCompletion ≠ 0 :=
    (map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 A.ne_zero
  have hden' : 1 + q.toCompletion * c.toCompletion ≠ 0 := by
    rw [← hAto]
    exact hAto_ne
  have hden : 1 + c.toCompletion * q.toCompletion ≠ 0 := by
    have hdenEq : 1 + c.toCompletion * q.toCompletion = (A : v.adicCompletion F).toCompletion := by
      rw [hAto]
      ring
    rw [hdenEq]
    exact (map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 A.ne_zero
  have hb : (c / A).toCompletion = c.toCompletion / (A : v.adicCompletion F).toCompletion :=
    adicCompletion_toCompletion_divUnit_ind c A
  have hr : (q / A).toCompletion = q.toCompletion / (A : v.adicCompletion F).toCompletion :=
    adicCompletion_toCompletion_divUnit_ind q A
  have hb' : (c * (A : v.adicCompletion F)⁻¹).toCompletion =
      c.toCompletion * ((A : v.adicCompletion F).toCompletion)⁻¹ := by
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have hr' : (q * (A : v.adicCompletion F)⁻¹).toCompletion =
      q.toCompletion * ((A : v.adicCompletion F).toCompletion)⁻¹ := by
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have hu₁ : ((A⁻¹ * A⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      ((A⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion *
        ((A⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion :=
    adicCompletion_toCompletion_unitMul_ind A⁻¹ A⁻¹
  have hu₂ : ((A⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F).toCompletion =
      ((A : v.adicCompletion F).toCompletion)⁻¹ :=
    adicCompletion_toCompletion_unitInv_ind A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerM, upperM, diagM, weylM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val,
      adicCompletion_toCompletion_add_ind, adicCompletion_toCompletion_mul_ind,
      adicCompletion_toCompletion_inv_ind, hb, hr, hb', hr', hu₁, hu₂, hAto] <;>
    field_simp [hden, hden'] <;> ring_nf

private theorem weyl_upper_lower_matrix_ind (t c : v.adicCompletion F) :
    weylM (v.adicCompletion F) * upperM (v.adicCompletion F) t *
        lowerM (v.adicCompletion F) c =
      lowerM (v.adicCompletion F) t * upperM (v.adicCompletion F) c *
        weylM (v.adicCompletion F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weylM, upperM, lowerM, Matrix.mul_apply, Fin.sum_univ_two,
      adicCompletion_toCompletion_mul_ind]
  all_goals ring

private theorem diag_upper_matrix_ind (y : (v.adicCompletion F)ˣ)
    (b : v.adicCompletion F) :
    diagM (v.adicCompletion F) y * upperM (v.adicCompletion F) b =
      upperM (v.adicCompletion F) (b * (y : v.adicCompletion F)) *
        diagM (v.adicCompletion F) y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagM, upperM, Matrix.mul_apply, Fin.sum_univ_two,
      adicCompletion_toCompletion_mul_ind, Units.val_mul]
  all_goals ring

private theorem upper_upper_matrix_ind (x y : v.adicCompletion F) :
    upperM (v.adicCompletion F) x * upperM (v.adicCompletion F) y =
      upperM (v.adicCompletion F) (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperM, Matrix.mul_apply, Fin.sum_univ_two,
      adicCompletion_toCompletion_add_ind, adicCompletion_toCompletion_mul_ind]
  all_goals ring

private theorem diag_diag_matrix_ind (y z : (v.adicCompletion F)ˣ) :
    diagM (v.adicCompletion F) y * diagM (v.adicCompletion F) z =
      diagM (v.adicCompletion F) (y * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagM, Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul,
      adicCompletion_toCompletion_mul_ind]
  all_goals ring

private theorem bigCell_right_nbar_projective_ind
    (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
    (t c : v.adicCompletion F) (A : (v.adicCompletion F)ˣ)
    (hA : (A : v.adicCompletion F) = 1 + t * c) :
    (QuotientGroup.mk
        (bigCellMatrix (F := F) x y t * lowerM (v.adicCompletion F) c) :
          PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk (bigCellMatrix (F := F)
        (x + (y : v.adicCompletion F) * (c / (A : v.adicCompletion F)))
        (y * (A⁻¹ * A⁻¹)) (t / (A : v.adicCompletion F))) := by
  let K := v.adicCompletion F
  let b : K := c / (A : K)
  let r : K := t / (A : K)
  let u : Kˣ := A⁻¹ * A⁻¹
  let x' : K := x + (y : K) * b
  let y' : Kˣ := y * u
  let P : GL (Fin 2) K := upperM K x * diagM K y * weylM K * upperM K t * lowerM K c
  let Q : GL (Fin 2) K := upperM K x' * diagM K y' * weylM K * upperM K r
  have hW : weylM K * upperM K t * lowerM K c =
      lowerM K t * upperM K c * weylM K := weyl_upper_lower_matrix_ind t c
  have hGauss := lower_upper_w_matrix_gauss t c A hA
  have hdiagU := diag_upper_matrix_ind y b
  have hUU := upper_upper_matrix_ind x (b * (y : K))
  have hdiagD := diag_diag_matrix_ind y u
  have hcore : upperM K x * diagM K y *
        upperM K b * diagM K u * weylM K * upperM K r = Q := by
    dsimp [Q, x', y']
    calc
      _ = upperM K x *
          (diagM K y * upperM K b) * diagM K u * weylM K * upperM K r := by group
      _ = upperM K x *
          (upperM K (b * (y : K)) * diagM K y) * diagM K u * weylM K * upperM K r := by
            rw [hdiagU]
      _ = (upperM K x * upperM K (b * (y : K))) *
          (diagM K y * diagM K u) * weylM K * upperM K r := by group
      _ = (upperM K x * upperM K (b * (y : K))) *
          diagM K (y * u) * weylM K * upperM K r := by rw [hdiagD]
      _ = upperM K (x + b * (y : K)) * diagM K (y * u) * weylM K * upperM K r := by
            rw [hUU]
      _ = Q := by
            have hx' : x + b * (y : K) = x + (y : K) * (c / (A : K)) := by
              dsimp [b]
              ring
            simp [Q, x', y', b, u, r, hx']
  have hscalar : P = Matrix.GeneralLinearGroup.scalar (Fin 2) A * Q := by
    dsimp [P]
    calc
      _ = upperM K x * diagM K y * (weylM K * upperM K t * lowerM K c) := by group
      _ = upperM K x * diagM K y * (lowerM K t * upperM K c * weylM K) := by rw [hW]
      _ = upperM K x * diagM K y *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) A *
            (upperM K b * diagM K u * weylM K * upperM K r)) := by rw [hGauss]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) A *
          (upperM K x * diagM K y * upperM K b * diagM K u * weylM K * upperM K r) := by
            have hc := Matrix.GeneralLinearGroup.scalar_commute A (upperM K x * diagM K y)
            calc
              _ = (upperM K x * diagM K y * Matrix.GeneralLinearGroup.scalar (Fin 2) A) *
                  (upperM K b * diagM K u * weylM K * upperM K r) := by group
              _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) A *
                  (upperM K x * diagM K y)) *
                  (upperM K b * diagM K u * weylM K * upperM K r) := by rw [← hc]
              _ = _ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) A * Q := by rw [hcore]
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨A⁻¹, ?_⟩
  have hscalarInv : Matrix.GeneralLinearGroup.scalar (Fin 2) A *
      Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  calc
    P * Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹ =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) A * Q) *
          Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹ := by rw [hscalar]
    _ = Q := by
      calc
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) A *
            (Q * Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹) := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) A *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹ * Q) := by
              rw [← Matrix.GeneralLinearGroup.scalar_commute A⁻¹ Q]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) A *
            Matrix.GeneralLinearGroup.scalar (Fin 2) A⁻¹) * Q := by group
        _ = Q := by rw [hscalarInv]; simp

private theorem gl2_class_not_borel_of_lowerleft_ne
    (G : GL (Fin 2) (v.adicCompletion F))
    (h10 : (G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0)
    (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
    (hclass : (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y)) :
    False := by
  obtain ⟨q, hmat⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have he := congrArg (fun g : GL (Fin 2) (v.adicCompletion F) =>
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) hmat
  have hzero :
      ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) * (q : v.adicCompletion F) = 0 := by
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two, upperM, diagM] using he
  exact h10 ((mul_eq_zero.mp hzero).resolve_right q.ne_zero)

private theorem bigCell_gauss_lift (L : FinLocalCover D H v) (T : TorusRep D H v)
    [Nontrivial T.V] (q c : v.adicCompletion F) (A : (v.adicCompletion F)ˣ)
    (hA : (A : v.adicCompletion F) = 1 + q * c)
    (hσ : T.σa A = LinearMap.id) :
    L.nbar (Multiplicative.ofAdd q) * L.n (Multiplicative.ofAdd c) * L.w =
      L.n (Multiplicative.ofAdd (c / A)) * L.a (A⁻¹ * A⁻¹) * L.w *
        L.n (Multiplicative.ofAdd (q / A)) := by
  let K := v.adicCompletion F
  let b : K := c / A
  let u : Kˣ := A⁻¹ * A⁻¹
  let r : K := q / A
  let G₁ := lowerM K q
  let G₂ := upperM K c
  let W := weylM K
  let U := upperM K b
  let Dg := diagM K u
  let Ur := upperM K r
  have hκ₁ := kpCocycle_lower_upper_ind (F := F) (D := D) (H := H) (v := v) q c
  have hκ₂ := kpCocycle_lower_upper_w_ind T q c A hA hσ
  have hκ₃ := kpCocycle_upper_diag_ind (F := F) (D := D) (H := H) (v := v) b u
  have hκ₄ := kpCocycle_upper_diag_w_ind (F := F) (D := D) (H := H) (v := v) b u
  have hκ₅ := kpCocycle_upper_diag_w_upper_ind (F := F) (D := D) (H := H) (v := v) b u r
  have hκ₆ := kpCocycle_scalar_upper_diag_w_upper_ind (F := F) (D := D) (H := H)
    (v := v) A b r
  have hκ₁' : kpCocycle D H v G₁ G₂ = 1 := by simpa [G₁, G₂] using hκ₁
  have hκ₂' : kpCocycle D H v (G₁ * G₂) W = 1 := by simpa [G₁, G₂, W] using hκ₂
  have hκ₃' : kpCocycle D H v U Dg = 1 := by simpa [U, Dg] using hκ₃
  have hκ₄' : kpCocycle D H v (U * Dg) W = 1 := by simpa [U, Dg, W] using hκ₄
  have hκ₅' : kpCocycle D H v (U * Dg * W) Ur = 1 := by
    simpa [U, Dg, W, Ur] using hκ₅
  have hκ₆' : kpCocycle D H v (Matrix.GeneralLinearGroup.scalar (Fin 2) A)
      (U * Dg * W * Ur) = 1 := by simpa [U, Dg, W, Ur, b, u, r] using hκ₆
  have hmat : G₁ * G₂ * W =
      Matrix.GeneralLinearGroup.scalar (Fin 2) A * (U * Dg * W * Ur) := by
    dsimp [G₁, G₂, W, U, Dg, Ur, b, u, r]
    exact lower_upper_w_matrix_gauss q c A hA
  have hleft : L.nbar (Multiplicative.ofAdd q) * L.n (Multiplicative.ofAdd c) * L.w =
      L.sec (G₁ * G₂ * W) := by
    calc
      _ = (L.sec G₁ * L.sec G₂) * L.sec W := by
        simp [G₁, G₂, W, L.sec_nbar, L.sec_n, L.sec_w] <;> rfl
      _ = (L.z (kpCocycle D H v G₁ G₂) * L.sec (G₁ * G₂)) * L.sec W := by
        rw [L.sec_mul]
      _ = L.sec (G₁ * G₂) * L.sec W := by rw [hκ₁']; simp
      _ = L.z (kpCocycle D H v (G₁ * G₂) W) * L.sec (G₁ * G₂ * W) := by
        rw [L.sec_mul]
      _ = L.sec (G₁ * G₂ * W) := by rw [hκ₂']; simp
  have hright :
      L.n (Multiplicative.ofAdd b) * L.a u * L.w * L.n (Multiplicative.ofAdd r) =
        L.sec (U * Dg * W * Ur) := by
    calc
      _ = L.sec U * L.sec Dg * L.sec W * L.sec Ur := by
        simp [U, Dg, W, Ur, b, u, r, L.sec_n, L.sec_a, L.sec_w] <;> rfl
      _ = (L.z (kpCocycle D H v U Dg) * L.sec (U * Dg)) * L.sec W * L.sec Ur := by
        rw [L.sec_mul]
      _ = L.sec (U * Dg) * L.sec W * L.sec Ur := by rw [hκ₃']; simp
      _ = L.z (kpCocycle D H v (U * Dg) W) * L.sec (U * Dg * W) * L.sec Ur := by
        rw [L.sec_mul]
      _ = L.sec (U * Dg * W) * L.sec Ur := by rw [hκ₄']; simp
      _ = L.z (kpCocycle D H v (U * Dg * W) Ur) * L.sec (U * Dg * W * Ur) := by
        rw [L.sec_mul]
      _ = L.sec (U * Dg * W * Ur) := by rw [hκ₅']; simp
  have hscalar :
      L.sec (Matrix.GeneralLinearGroup.scalar (Fin 2) A * (U * Dg * W * Ur)) =
        L.sec (U * Dg * W * Ur) := by
    have hmul := L.sec_mul (Matrix.GeneralLinearGroup.scalar (Fin 2) A) (U * Dg * W * Ur)
    rw [L.sec_scalar, hκ₆'] at hmul
    simpa using hmul.symm
  calc
    _ = L.sec (G₁ * G₂ * W) := hleft
    _ = L.sec (Matrix.GeneralLinearGroup.scalar (Fin 2) A * (U * Dg * W * Ur)) := by
      rw [hmat]
    _ = L.sec (U * Dg * W * Ur) := hscalar
    _ = _ := hright.symm

private theorem compact_support_ball (T : TorusRep D H v) (φ : v.adicCompletion F → T.V)
    (hc : HasCompactSupport φ) :
    ∃ R : ℕ, tsupport φ ⊆ ball v (-(R : ℤ)) := by
  classical
  let K := v.adicCompletion F
  change IsCompact (tsupport φ) at hc
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : K)).mp hc.isBounded
  let qN : NNReal := Ideal.absNorm v.asIdeal
  have hqN : 1 < qN := by
    exact HeightOneSpectrum.one_lt_absNorm_nnreal v
  let q : ℝ := qN
  have hq : 1 < q := by exact_mod_cast hqN
  obtain ⟨R, hR⟩ := (tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop C |>.exists
  have hpowNN :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (R : ℤ)) = qN ^ R := by
    rw [WithZeroMulInt.toNNReal_neg_apply
      (HeightOneSpectrum.absNorm_ne_zero v) (by simp)]
    rw [WithZero.toAdd_unzero_eq_log (by simp)]
    simp [qN]
  have hpow :
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (R : ℤ)) : ℝ) = (q ^ R : ℝ) := by
    simpa [q] using congrArg (fun z : NNReal => (z : ℝ)) hpowNN
  refine ⟨R, ?_⟩
  intro x hx
  have hnorm : ‖x‖ ≤ C := by
    have hball := hC hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  have htoReal :
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (Valued.v x) : ℝ) <
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
        (WithZero.exp (R : ℤ)) : ℝ) := by
    calc
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (Valued.v x) : ℝ) = ‖x‖ := by rw [FinitePlace.norm_def]
      _ ≤ C := hnorm
      _ < (q ^ R : ℝ) := hR
      _ = (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
            (WithZero.exp (R : ℤ)) : ℝ) := hpow.symm
  have hto :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (Valued.v x) <
        WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
          (WithZero.exp (R : ℤ)) := by exact_mod_cast htoReal
  have hval : Valued.v x ≤ WithZero.exp (R : ℤ) :=
    (WithZeroMulInt.toNNReal_strictMono hqN).le_iff_le.mp hto.le
  simpa [ball] using hval

set_option maxHeartbeats 400000 in
private theorem bigCell_phi_add_invariant (T : TorusRep D H v) (φ : v.adicCompletion F → T.V)
    (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    ∃ k : ℕ, ∀ t u, u ∈ ball v (k : ℤ) → φ (t + u) = φ t := by
  classical
  let K := v.adicCompletion F
  let S : Set K := tsupport φ
  have hS : IsCompact S := by exact hc
  let F0 : K × K → T.V := fun p => φ (p.1 + p.2) - φ p.1
  have hsum : IsLocallyConstant (fun p : K × K => φ (p.1 + p.2)) := by
    apply hφ.comp_continuous
    fun_prop
  have hfst : IsLocallyConstant (fun p : K × K => φ p.1) := by
    apply hφ.comp_continuous
    fun_prop
  have hF0 : IsLocallyConstant F0 :=
    hsum.comp₂ hfst (fun a b => a - b)
  let W : Set (K × K) := {p | F0 p = 0}
  have hWopen : IsOpen W := hF0.isOpen_fiber 0
  have hWmem (t : K) : W ∈ nhds (t, 0) := by
    apply hWopen.mem_nhds
    simp [W, F0]
  choose U hU V hV hUV using fun t : K => mem_nhds_prod_iff.mp (hWmem t)
  obtain ⟨fs, hfs, hcover⟩ := hS.elim_nhds_subcover U (fun t _ => hU t)
  have hVevent : ∀ᶠ u in nhds (0 : K), ∀ t ∈ fs, u ∈ V t := by
    rw [Filter.eventually_all_finset]
    intro t ht
    exact hV t
  let W0 : Set K := {u | ∀ t ∈ fs, u ∈ V t}
  have hW0 : W0 ∈ nhds (0 : K) := hVevent
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hW0
  let vHom : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let δ : (WithZero (Multiplicative ℤ))ˣ := Units.map
    (MonoidWithZeroHom.ValueGroup₀.embedding (f := .ofClass vHom)) γ
  let k : ℕ := (-WithZero.log (δ : WithZero (Multiplicative ℤ))).toNat + 1
  have hbound : WithZero.exp (-(k : ℤ)) < (δ : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_log (Units.ne_zero δ), WithZero.exp_lt_exp]
    dsimp only [k]
    omega
  have hball : ball v (k : ℤ) ⊆ W0 := by
    intro u hu
    have huVal : Valued.v u < (δ : WithZero (Multiplicative ℤ)) :=
      lt_of_le_of_lt (by simpa [ball] using hu) hbound
    have huRestrict : Valued.v.restrict u < γ.1 := by
      change Valued.v.restrict u < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact by simpa [δ] using huVal
    exact hγ huRestrict
  have hlocal (t : K) (ht : t ∈ S) (u : K) (hu : u ∈ W0) :
      φ (t + u) = φ t := by
    rcases Set.mem_iUnion.mp (hcover ht) with ⟨t', ht'⟩
    rcases Set.mem_iUnion.mp ht' with ⟨ht'fs, ht'U⟩
    have hFU : F0 (t, u) = 0 := hUV t' ⟨ht'U, hu t' ht'fs⟩
    exact sub_eq_zero.mp hFU
  refine ⟨k, ?_⟩
  intro t u hu
  have huW : u ∈ W0 := hball hu
  by_cases ht : t ∈ S
  · exact hlocal t ht u huW
  · have hzero : φ t = 0 := image_eq_zero_of_notMem_tsupport ht
    by_cases htu : t + u ∈ S
    · have hneg : -u ∈ ball v (k : ℤ) := by
        simpa [ball] using hu
      have hback := hlocal (t + u) htu (-u) (hball hneg)
      have hback' : φ t = φ (t + u) := by simpa [add_assoc] using hback
      exact hback'.symm
    · have hzero' : φ (t + u) = 0 := image_eq_zero_of_notMem_tsupport htu
      simp [hzero, hzero']

private theorem ball_mono_ind {m n : ℤ} (hmn : m ≤ n) {x : v.adicCompletion F}
    (hx : x ∈ ball v n) : x ∈ ball v m := by
  change Valued.v x ≤ WithZero.exp (-n) at hx
  change Valued.v x ≤ WithZero.exp (-m)
  exact hx.trans (WithZero.exp_le_exp.mpr (by omega))

private theorem ball_add_ind {m : ℤ} {x y : v.adicCompletion F}
    (hx : x ∈ ball v m) (hy : y ∈ ball v m) : x + y ∈ ball v m := by
  change Valued.v x ≤ WithZero.exp (-m) at hx
  change Valued.v y ≤ WithZero.exp (-m) at hy
  change Valued.v (x + y) ≤ WithZero.exp (-m)
  exact (Valuation.map_add_le_max' Valued.v x y).trans (max_le hx hy)

private theorem ball_neg_ind {m : ℤ} {x : v.adicCompletion F}
    (hx : x ∈ ball v m) : -x ∈ ball v m := by
  simpa [ball] using hx

private theorem ball_mul_ind {m n : ℤ} {x y : v.adicCompletion F}
    (hx : x ∈ ball v m) (hy : y ∈ ball v n) : x * y ∈ ball v (m + n) := by
  change Valued.v x ≤ WithZero.exp (-m) at hx
  change Valued.v y ≤ WithZero.exp (-n) at hy
  change Valued.v (x * y) ≤ WithZero.exp (-(m + n))
  rw [map_mul]
  calc
    Valued.v x * Valued.v y ≤ WithZero.exp (-m) * Valued.v y :=
      mul_le_mul_of_nonneg_right hx bot_le
    _ ≤ WithZero.exp (-m) * WithZero.exp (-n) :=
      mul_le_mul_of_nonneg_left hy bot_le
    _ = WithZero.exp (-(m + n)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega

private theorem valued_one_add_eq_one_ind (x : v.adicCompletion F)
    (hx : Valued.v x < 1) : Valued.v (1 + x) = 1 := by
  have hneg : Valued.v (-x) < Valued.v (1 : v.adicCompletion F) := by simpa using hx
  have hval : Valued.v (1 - (-x)) = Valued.v (1 : v.adicCompletion F) :=
    Valuation.map_sub_eq_of_lt_left _ hneg
  simpa using hval

private def nearIdMat (N : ℕ) : Set (GL (Fin 2) (v.adicCompletion F)) :=
  {G | (((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) - 1 ∈ ball v N) ∧
    ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1 ∈ ball v N) ∧
    ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ∈ ball v N) ∧
    (((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) - 1 ∈ ball v N)}

private theorem nearIdMat_factor (N : ℕ) (hN : 1 ≤ N)
    (G : GL (Fin 2) (v.adicCompletion F))
    (hG : G ∈ nearIdMat (F := F) (v := v) N) :
    ∃ b c : v.adicCompletion F, ∃ u : (v.adicCompletion F)ˣ,
      b ∈ ball v N ∧ c ∈ ball v N ∧
      ((u : v.adicCompletion F) - 1) ∈ ball v N ∧
      (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
        QuotientGroup.mk (upperM (v.adicCompletion F) b * diagM (v.adicCompletion F) u *
          lowerM (v.adicCompletion F) c) := by
  classical
  let K := v.adicCompletion F
  let M : Matrix (Fin 2) (Fin 2) K := G
  let a : K := M 0 0
  let b₀ : K := M 0 1
  let c₀ : K := M 1 0
  let d : K := M 1 1
  have h00 : a - 1 ∈ ball v N := hG.1
  have h01 : b₀ ∈ ball v N := hG.2.1
  have h10 : c₀ ∈ ball v N := hG.2.2.1
  have h11 : d - 1 ∈ ball v N := hG.2.2.2
  have hN' : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
  have h11one : d - 1 ∈ ball v 1 := ball_mono_ind hN' h11
  have hsmall : Valued.v (d - 1) < 1 := by
    have hb : Valued.v (d - 1) ≤ WithZero.exp (-1 : ℤ) := by
      change Valued.v (d - 1) ≤ WithZero.exp (-1 : ℤ) at h11one
      exact h11one
    exact hb.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
  have hdVal : Valued.v d = 1 := by
    have := valued_one_add_eq_one_ind (d - 1) hsmall
    convert this using 1 <;> ring
  have hd : d ≠ 0 := by
    intro hd0
    rw [hd0, map_zero] at hdVal
    simp at hdVal
  let du : Kˣ := Units.mk0 d hd
  let b : K := b₀ * d⁻¹
  let c : K := c₀ * d⁻¹
  let δ : K := a * d - b₀ * c₀
  have hδ : δ ≠ 0 := by
    intro hδ0
    apply G.det_ne_zero
    rw [Matrix.det_fin_two]
    change a * d - b₀ * c₀ = 0
    exact hδ0
  let δU : Kˣ := Units.mk0 δ hδ
  let u : Kˣ := δU / du ^ 2
  have hInvSquare : d⁻¹ * d⁻¹ = (d ^ 2)⁻¹ := by
    simpa [pow_two] using (inv_pow d 2)
  have hdi : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  have hdInvTwo : d * (d⁻¹) ^ 2 = d⁻¹ := by
    rw [pow_two]
    calc
      d * (d⁻¹ * d⁻¹) = (d * d⁻¹) * d⁻¹ := by ring
      _ = d⁻¹ := by rw [hdi]; simp
  have hdTwoInvTwo : d ^ 2 * (d⁻¹) ^ 2 = 1 := by
    calc
      d ^ 2 * (d⁻¹) ^ 2 = (d * d⁻¹) ^ 2 := by ring
      _ = 1 := by rw [hdi]; simp
  have hdInvVal : Valued.v (d⁻¹) = 1 := by rw [map_inv₀, hdVal]; simp
  have hdInvBall : d⁻¹ ∈ ball v 0 := by
    change Valued.v (d⁻¹) ≤ WithZero.exp (0 : ℤ)
    rw [hdInvVal]
    simp
  have hbmem : b ∈ ball v N := by
    have h := ball_mul_ind h01 hdInvBall
    simpa using h
  have hcmem : c ∈ ball v N := by
    have h := ball_mul_ind h10 hdInvBall
    simpa using h
  have hdmem : d ∈ ball v 0 := by
    change Valued.v d ≤ WithZero.exp (0 : ℤ)
    rw [hdVal]
    simp
  have hdiff : a - d ∈ ball v N := by
    have hneg : -(d - 1) ∈ ball v N := ball_neg_ind h11
    have hsub : a - d = (a - 1) + -(d - 1) := by ring
    rw [hsub]
    exact ball_add_ind h00 hneg
  have hbc : b₀ * c₀ ∈ ball v (N + N) := ball_mul_ind h01 h10
  have hbc' : b₀ * c₀ ∈ ball v N := by
    exact ball_mono_ind (by omega) hbc
  have hnum : (a - d) * d - b₀ * c₀ ∈ ball v N := by
    have hmul : (a - d) * d ∈ ball v N := by
      have h := ball_mul_ind hdiff hdmem
      simpa using h
    have hneg : -(b₀ * c₀) ∈ ball v N := ball_neg_ind hbc'
    have hEq : (a - d) * d - b₀ * c₀ = (a - d) * d + -(b₀ * c₀) := by ring
    rw [hEq]
    exact ball_add_ind hmul hneg
  have hduInvBall : (d⁻¹ * d⁻¹) ∈ ball v 0 := by
    have h := ball_mul_ind hdInvBall hdInvBall
    simpa using h
  have huVal : (u : K) = δ / d ^ 2 := by
    simp [u, δU, du, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  have huMinus : (u : K) - 1 = ((a - d) * d - b₀ * c₀) * (d⁻¹ * d⁻¹) := by
    rw [huVal]
    rw [div_eq_mul_inv, ← hInvSquare, ← hdTwoInvTwo]
    dsimp [δ]
    ring
  have humem : ((u : K) - 1) ∈ ball v N := by
    rw [huMinus]
    have h := ball_mul_ind hnum hduInvBall
    simpa using h
  have hbto : b.toCompletion = b₀.toCompletion * d.toCompletion⁻¹ := by
    dsimp [b]
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have hcto : c.toCompletion = c₀.toCompletion * d.toCompletion⁻¹ := by
    dsimp [c]
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have hduTo : (du : K).toCompletion = d.toCompletion := by simp [du]
  have hInvD : (d⁻¹).toCompletion = d.toCompletion⁻¹ :=
    adicCompletion_toCompletion_inv_ind d
  have huTo : (u : K).toCompletion =
      δ.toCompletion / (d.toCompletion ^ 2) := by
    dsimp [u, δU]
    rw [adicCompletion_toCompletion_unitDiv_ind, adicCompletion_toCompletion_unitPow_two_ind,
      hduTo]
    simp [du]
  have h00field : a * d⁻¹ = δ / d ^ 2 + b * c := by
    symm
    rw [div_eq_mul_inv, ← hInvSquare]
    dsimp [b, c, δ]
    calc
      (a * d - b₀ * c₀) * (d⁻¹ * d⁻¹) +
          (b₀ * d⁻¹) * (c₀ * d⁻¹) = a * d * (d⁻¹ * d⁻¹) := by ring
      _ = a * (d * (d⁻¹ * d⁻¹)) := by ring
      _ = a * d⁻¹ := by
        congr 1
        calc
          d * (d⁻¹ * d⁻¹) = (d * d⁻¹) * d⁻¹ := by ac_rfl
          _ = d⁻¹ := by rw [hdi]; simp
  have h00comp : a.toCompletion * d.toCompletion⁻¹ =
      (δ / d ^ 2 + b * c).toCompletion := by
    calc
      _ = (a * d⁻¹).toCompletion := by
        rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      _ = _ := congrArg (fun z : K => z.toCompletion) h00field
  have h01comp : b₀.toCompletion * d.toCompletion⁻¹ =
      (b₀ * d⁻¹).toCompletion := by
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have h10comp : c₀.toCompletion * d.toCompletion⁻¹ =
      (c₀ * d⁻¹).toCompletion := by
    rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
  have h11comp : d.toCompletion * d.toCompletion⁻¹ = 1 := by
    calc
      _ = (d * d⁻¹).toCompletion := by
        rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      _ = 1 := by
        rw [hdi]
        simp
  have h01field : b₀ * d⁻¹ = b := by rfl
  have h10field : c₀ * d⁻¹ = c := by rfl
  have hmat : G * Matrix.GeneralLinearGroup.scalar (Fin 2) du⁻¹ =
      upperM K b * diagM K u * lowerM K c := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [M, a, b₀, c₀, d, b, c, u, δ, du, δU, upperM, diagM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, hbto, hcto, huTo, hduTo, hInvD,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind] using h00comp
    · simpa [M, a, b₀, c₀, d, b, c, u, δ, du, δU, upperM, diagM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, hbto, hcto, huTo, hduTo, hInvD,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind] using h01comp
    · simpa [M, a, b₀, c₀, d, b, c, u, δ, du, δU, upperM, diagM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, hbto, hcto, huTo, hduTo, hInvD,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind] using h10comp
    · simpa [M, a, b₀, c₀, d, b, c, u, δ, du, δU, upperM, diagM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, hbto, hcto, huTo, hduTo, hInvD,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind] using h11comp
  have hclass : (QuotientGroup.mk G : PGL2 K) =
      QuotientGroup.mk (upperM K b * diagM K u * lowerM K c) := by
    apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
    exact ⟨du⁻¹, hmat⟩
  exact ⟨b, c, u, hbmem, hcmem, humem, hclass⟩

private theorem nearIdMat_isOpen (N : ℕ) :
    IsOpen (nearIdMat (F := F) (v := v) N) := by
  have hball : IsOpen (ball v N) := by
    exact IsDedekindDomain.HeightOneSpectrum.isOpen_setOf_valued_le
      (K := F) (v := v) WithZero.exp_ne_zero
  have h00 : IsOpen {G : GL (Fin 2) (v.adicCompletion F) |
      ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) - 1 ∈ ball v N} := by
    apply hball.preimage
    fun_prop
  have h01 : IsOpen {G : GL (Fin 2) (v.adicCompletion F) |
      ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1) ∈ ball v N} := by
    apply hball.preimage
    fun_prop
  have h10 : IsOpen {G : GL (Fin 2) (v.adicCompletion F) |
      ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ∈ ball v N} := by
    apply hball.preimage
    fun_prop
  have h11 : IsOpen {G : GL (Fin 2) (v.adicCompletion F) |
      (((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) - 1) ∈ ball v N} := by
    apply hball.preimage
    fun_prop
  have hset : nearIdMat (F := F) (v := v) N =
      {G : GL (Fin 2) (v.adicCompletion F) |
        ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0) - 1 ∈ ball v N} ∩
        ({G : GL (Fin 2) (v.adicCompletion F) |
          ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 1) ∈ ball v N} ∩
          ({G : GL (Fin 2) (v.adicCompletion F) |
            ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ∈ ball v N} ∩
            {G : GL (Fin 2) (v.adicCompletion F) |
              (((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) - 1) ∈ ball v N})) := by
    ext G
    simp [nearIdMat]
  rw [hset]
  exact h00.inter (h01.inter (h10.inter h11))

private theorem ball_one_valued_lt_one_ind {x : v.adicCompletion F}
    (hx : x ∈ ball v 1) : Valued.v x < 1 := by
  change Valued.v x ≤ WithZero.exp (-1 : ℤ) at hx
  exact hx.trans_lt (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)

private theorem unit_val_one_of_near_one_ind (N : ℕ) (hN : 1 ≤ N)
    (u : (v.adicCompletion F)ˣ)
    (hu : ((u : v.adicCompletion F) - 1) ∈ ball v N) :
    Valued.v (u : v.adicCompletion F) = 1 := by
  have hu1 : ((u : v.adicCompletion F) - 1) ∈ ball v 1 :=
    ball_mono_ind (by exact_mod_cast hN) hu
  have hsmall := ball_one_valued_lt_one_ind hu1
  have hone := valued_one_add_eq_one_ind ((u : v.adicCompletion F) - 1) hsmall
  calc
    Valued.v (u : v.adicCompletion F) =
        Valued.v (1 + ((u : v.adicCompletion F) - 1)) := by congr 1 <;> ring
    _ = 1 := hone

private theorem isLocUnit_of_valued_one_ind (u : (v.adicCompletion F)ˣ)
    (hu : Valued.v (u : v.adicCompletion F) = 1) : IsLocUnit v u := by
  have huInv : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simpa [hu]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, huInv]

private theorem bigCell_phi_mul_unit_invariant
    (T : TorusRep D H v) (φ : v.adicCompletion F → T.V) (R M k : ℕ)
    (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hadd : ∀ t u, u ∈ ball v (k : ℤ) → φ (t + u) = φ t)
    (hRM : R + k ≤ M) (u : (v.adicCompletion F)ˣ)
    (huVal : Valued.v (u : v.adicCompletion F) = 1)
    (hu : ((u : v.adicCompletion F) - 1) ∈ ball v (M : ℤ)) :
    ∀ t, φ (t * (u : v.adicCompletion F)) = φ t := by
  classical
  intro t
  let S : Set (v.adicCompletion F) := tsupport φ
  have huInvBall : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ ball v 0 := by
    change Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ WithZero.exp 0
    have hInvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
      simpa [huVal]
    rw [hInvVal]
    simp
  have hshift (ht : t ∈ ball v (-(R : ℤ))) :
      t * (u : v.adicCompletion F) - t ∈ ball v (k : ℤ) := by
    have hprod : t * ((u : v.adicCompletion F) - 1) ∈ ball v ((-(R : ℤ)) + (M : ℤ)) :=
      ball_mul_ind ht hu
    have hprod' : t * ((u : v.adicCompletion F) - 1) ∈ ball v (k : ℤ) :=
      ball_mono_ind (by omega) hprod
    have heq : t * (u : v.adicCompletion F) - t =
        t * ((u : v.adicCompletion F) - 1) := by ring
    simpa [heq] using hprod'
  have htranslate (ht : t ∈ ball v (-(R : ℤ))) :
      φ (t * (u : v.adicCompletion F)) = φ t := by
    have h := hadd t (t * (u : v.adicCompletion F) - t) (hshift ht)
    simpa [add_sub_cancel] using h
  by_cases ht : t ∈ S
  · exact htranslate (hS ht)
  · by_cases htu : t * (u : v.adicCompletion F) ∈ S
    · have htBound : t ∈ ball v (-(R : ℤ)) := by
        have hmul := ball_mul_ind (hS htu) huInvBall
        have heq : (t * (u : v.adicCompletion F)) *
            ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = t := by
          simp [mul_assoc]
        simpa [heq] using hmul
      exact htranslate htBound
    · have hzero : φ t = 0 := image_eq_zero_of_notMem_tsupport ht
      have hzero' : φ (t * (u : v.adicCompletion F)) = 0 :=
        image_eq_zero_of_notMem_tsupport htu
      simp [hzero, hzero']

private theorem bigCell_right_n_ind (L : FinLocalCover D H v) (T : TorusRep D H v)
    (s : ℂ) (φ : v.adicCompletion F → T.V) (k : ℕ)
    (hadd : ∀ t u, u ∈ ball v (k : ℤ) → φ (t + u) = φ t)
    (b : v.adicCompletion F) (hb : b ∈ ball v (k : ℤ)) (g : L.L) :
    bigCell L T s φ (g * L.n (Multiplicative.ofAdd b)) = bigCell L T s φ g := by
  classical
  rcases bigCell_bruhat_cover L g with hsmall | hbig
  · obtain ⟨x, ζ, y, rfl⟩ := hsmall
    have hmove : L.a y * L.n (Multiplicative.ofAdd b) =
      L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y)) * L.a y := by
      simpa [Units.val_inv_eq_inv_val] using
        (L.lift_na ((b : v.adicCompletion F) * y) y).symm
    have hnn : L.n (Multiplicative.ofAdd x) *
        L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y)) =
        L.n (Multiplicative.ofAdd (x + (b : v.adicCompletion F) * y)) := by
      rw [← map_mul]
      simp
    have hprod : borelElem L x ζ y * L.n (Multiplicative.ofAdd b) =
        borelElem L (x + (b : v.adicCompletion F) * y) ζ y := by
      dsimp [borelElem]
      calc
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
            (L.a y * L.n (Multiplicative.ofAdd b)) := by group
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
            (L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y)) * L.a y) := by
              rw [hmove]
        _ = L.n (Multiplicative.ofAdd x) *
            (L.z ζ * L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y))) * L.a y := by
              group
        _ = L.n (Multiplicative.ofAdd x) *
            (L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y)) * L.z ζ) * L.a y := by
              rw [L.z_central ζ (L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y)))]
        _ = (L.n (Multiplicative.ofAdd x) *
            L.n (Multiplicative.ofAdd ((b : v.adicCompletion F) * y))) * L.z ζ * L.a y := by
              group
        _ = _ := by
          have harg : Multiplicative.ofAdd x *
              Multiplicative.ofAdd ((b : v.adicCompletion F) * y) =
              Multiplicative.ofAdd (x + (b : v.adicCompletion F) * y) := by simp
          exact congrArg (fun q : L.L => q * L.z ζ * L.a y)
            (hnn.trans (congrArg L.n harg.symm))
    have hzeroB (x' : v.adicCompletion F) :
        bigCell L T s φ (borelElem L x' ζ y) = 0 := by
      classical
      unfold bigCell
      split_ifs with h
      · let x₀ := h.choose
        let ζ₀ := h.choose_spec.choose
        let y₀ := h.choose_spec.choose_spec.choose
        let t₀ := h.choose_spec.choose_spec.choose_spec.choose
        have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
        exact (bigcell_ne_borel L x₀ x' ζ₀ ζ y₀ y t₀ hdecomp.symm).elim
      · rfl
    have h0 := hzeroB x
    have h1 : bigCell L T s φ
        (borelElem L (x + (b : v.adicCompletion F) * y) ζ y) = 0 := hzeroB _
    rw [hprod, h0, h1]
  · obtain ⟨x, ζ, y, t, rfl⟩ := hbig
    have htn : L.n (Multiplicative.ofAdd t) * L.n (Multiplicative.ofAdd b) =
        L.n (Multiplicative.ofAdd (t + b)) := by
      rw [← map_mul]
      simp
    have hprod :
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) * L.n (Multiplicative.ofAdd b) =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd (t + b)) := by
      rw [show (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) * L.n (Multiplicative.ofAdd b) =
          L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
            (L.n (Multiplicative.ofAdd t) * L.n (Multiplicative.ofAdd b)) by group]
      rw [htn]
    rw [hprod]
    rw [bigCell_eval_decomp L T s φ _ x ζ y (t + b) rfl]
    rw [bigCell_eval_decomp L T s φ _ x ζ y t rfl]
    rw [hadd t b hb]

private theorem torus_sigma_inv_square_of_id_ind
    (T : TorusRep D H v) [Nontrivial T.V] (u : (v.adicCompletion F)ˣ)
    (hu : T.σa u = LinearMap.id) :
    T.σa u⁻¹ = LinearMap.id ∧
      T.σa (u⁻¹ * u⁻¹) = LinearMap.id := by
  have hself := muThree_hilb_self_one_ind (D := D) (H := H) (v := v) u
  have hmu : muThree D (H.hilb v u u⁻¹) = 1 := by
    rw [muThree_hilb_inv_right_ind, hself]
    simp
  have hmul := T.σa_mul u u⁻¹
  have hinv : T.σa u⁻¹ = LinearMap.id := by
    simpa [hu, T.σa_one, hmu] using hmul
  have hselfInv := muThree_hilb_self_one_ind (D := D) (H := H) (v := v) u⁻¹
  have hmul' := T.σa_mul u⁻¹ u⁻¹
  have hinvSq : T.σa (u⁻¹ * u⁻¹) = LinearMap.id := by
    simpa [hinv, T.σa_one, hselfInv] using hmul'.symm
  exact ⟨hinv, hinvSq⟩

private theorem unit_inv_sub_one_mem_ball_ind (N : ℕ)
    (u : (v.adicCompletion F)ˣ) (huVal : Valued.v (u : v.adicCompletion F) = 1)
    (hu : ((u : v.adicCompletion F) - 1) ∈ ball v (N : ℤ)) :
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 ∈ ball v (N : ℤ) := by
  have huInvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simpa [huVal]
  have huInvBall : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ ball v 0 := by
    change Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ WithZero.exp 0
    rw [huInvVal]
    simp
  have hprod : ((u : v.adicCompletion F) - 1) *
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ ball v (N : ℤ) := by
    have h := ball_mul_ind hu huInvBall
    simpa using h
  have hneg : -(((u : v.adicCompletion F) - 1) *
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ∈ ball v (N : ℤ) :=
    ball_neg_ind hprod
  have heq : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
      -(((u : v.adicCompletion F) - 1) *
        ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) := by
    have hmul : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
        (u : v.adicCompletion F) = 1 := by simp
    calc
      _ = ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) -
          ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) *
            (u : v.adicCompletion F) := by rw [hmul]
      _ = _ := by ring
  rw [heq]
  exact hneg

private theorem bigCell_right_a_ind (L : FinLocalCover D H v) (T : TorusRep D H v)
    [Nontrivial T.V] (s : ℂ) (φ : v.adicCompletion F → T.V) (R M k : ℕ)
    (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hadd : ∀ t z, z ∈ ball v (k : ℤ) → φ (t + z) = φ t)
    (hRM : R + k ≤ M) (hM1 : 1 ≤ M) (u : (v.adicCompletion F)ˣ)
    (hu : ((u : v.adicCompletion F) - 1) ∈ ball v (M : ℤ))
    (hσ : T.σa u = LinearMap.id) (hσinv : T.σa u⁻¹ = LinearMap.id)
    (huLoc : IsLocUnit v u) :
    ∀ g, bigCell L T s φ (g * L.a u) = bigCell L T s φ g := by
  classical
  have huVal := unit_val_one_of_near_one_ind M hM1 u hu
  have hInvVal : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simpa [huVal]
  have hInvNear := unit_inv_sub_one_mem_ball_ind M u huVal hu
  have huInvLoc : IsLocUnit v u⁻¹ := by
    constructor
    · exact huLoc.2
    · simpa using huLoc.1
  have hphiMul := bigCell_phi_mul_unit_invariant T φ R M k hS hadd hRM u⁻¹
    hInvVal hInvNear
  have hphaseInv (y : (v.adicCompletion F)ˣ) :
      muThree D (H.hilb v y u⁻¹) = 1 :=
    muThree_hilb_one_of_sigmaa_id T y u⁻¹ hσinv
  have hphaseU (y : (v.adicCompletion F)ˣ) :
      muThree D (H.hilb v y u) = 1 :=
    muThree_hilb_one_of_sigmaa_id T y u hσ
  have hact (y : (v.adicCompletion F)ˣ) : T.σa (y * u⁻¹) = T.σa y := by
    have hmul := T.σa_mul y u⁻¹
    rw [hσinv] at hmul
    have hmul' : T.σa y =
        ((muThree D (H.hilb v y u⁻¹) : ℂˣ) : ℂ) • T.σa (y * u⁻¹) := by
      simpa [LinearMap.comp_id] using hmul
    simpa [hphaseInv] using hmul'.symm
  have habs (y : (v.adicCompletion F)ˣ) :
      absFin v (y * u⁻¹ : (v.adicCompletion F)ˣ) = absFin v y := by
    have h := absFin_mul_ind v y u⁻¹
    have h' : absFin v (((y * u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) =
        absFin v (y : v.adicCompletion F) *
          absFin v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simpa using h
    have hInvAbs : absFin v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 :=
      absFin_one_of_locUnit u⁻¹ huInvLoc
    rw [h', hInvAbs]
    simp
  intro g
  rcases bigCell_bruhat_cover L g with hsmall | hbig
  · obtain ⟨x, ζ, y, rfl⟩ := hsmall
    have hprodB : borelElem L x ζ y * L.a u =
        borelElem L x ζ (y * u) := by
      have h0 : borelElem L 0 1 u = L.a u := by simp [borelElem, L.a_one]
      calc
        _ = borelElem L x ζ y * borelElem L 0 1 u := by rw [h0]
        _ = borelElem L (x + 0 * (y : v.adicCompletion F))
            (ζ * 1 * muThree D (H.hilb v y u)) (y * u) :=
          borelElem_mul L x 0 ζ 1 y u
        _ = borelElem L x ζ (y * u) := by simp [hphaseU]
    have hzeroB (x' : v.adicCompletion F) (ζ' : rootsOfUnity 3 ℂ)
        (y' : (v.adicCompletion F)ˣ) :
        bigCell L T s φ (borelElem L x' ζ' y') = 0 := by
      unfold bigCell
      split_ifs with h
      · let x₀ := h.choose
        let ζ₀ := h.choose_spec.choose
        let y₀ := h.choose_spec.choose_spec.choose
        let t₀ := h.choose_spec.choose_spec.choose_spec.choose
        have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
        exact (bigcell_ne_borel L x₀ x' ζ₀ ζ' y₀ y' t₀ hdecomp.symm).elim
      · rfl
    rw [hprodB, hzeroB x ζ (y * u), hzeroB x ζ y]
  · obtain ⟨x, ζ, y, t, rfl⟩ := hbig
    have hna : L.n (Multiplicative.ofAdd t) * L.a u =
        L.a u * L.n (Multiplicative.ofAdd (t / u)) := by
      simpa [div_eq_mul_inv] using L.lift_na t u
    have hwa : L.w * L.a u = L.a u⁻¹ * L.w := by
      calc
        L.w * L.a u = (L.w * L.a u * L.w⁻¹) * L.w := by group
        _ = L.a u⁻¹ * L.w := by rw [L.lift_wa]
    have hmulTor : L.a y * L.a u⁻¹ = L.a (y * u⁻¹) := by
      have h := L.a_mul y u⁻¹
      rw [hphaseInv y] at h
      simpa using h
    have hprod :
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) * L.a u =
        L.n (Multiplicative.ofAdd x) * L.z ζ * L.a (y * u⁻¹) * L.w *
          L.n (Multiplicative.ofAdd (t / u)) := by
      calc
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
              (L.n (Multiplicative.ofAdd t) * L.a u) := by group
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
              (L.a u * L.n (Multiplicative.ofAdd (t / u))) := by rw [hna]
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y *
              (L.w * L.a u) * L.n (Multiplicative.ofAdd (t / u)) := by group
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y *
              (L.a u⁻¹ * L.w) * L.n (Multiplicative.ofAdd (t / u)) := by rw [hwa]
        _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
              (L.a y * L.a u⁻¹) * L.w * L.n (Multiplicative.ofAdd (t / u)) := by group
        _ = _ := by rw [hmulTor]
    rw [hprod]
    rw [bigCell_eval_decomp L T s φ _ x ζ (y * u⁻¹) (t / u) rfl]
    rw [bigCell_eval_decomp L T s φ _ x ζ y t rfl]
    rw [habs y, hact y]
    have hphi : φ (t / u) = φ t := by simpa [div_eq_mul_inv] using hphiMul t
    rw [hphi]

private theorem bigCell_borel_zero_ind (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (φ : v.adicCompletion F → T.V)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (borelElem L x ζ y) = 0 := by
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

private theorem bigCell_right_nbar_nonzero
    (L : FinLocalCover D H v) (T : TorusRep D H v) [Nontrivial T.V]
    (s : ℂ) (φ : v.adicCompletion F → T.V) (R M k mT : ℕ)
    (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hadd : ∀ t z, z ∈ ball v (k : ℤ) → φ (t + z) = φ t)
    (hR2k : 2 * R + k ≤ M) (hRmT : R + mT ≤ M) (hR1 : R + 1 ≤ M)
    (hmT : 0 < mT)
    (hsm : ∀ u : (v.adicCompletion F)ˣ,
      ((u : v.adicCompletion F) - 1) ∈ ball v (mT : ℤ) → T.σa u = LinearMap.id)
    (c : v.adicCompletion F) (hc : c ∈ ball v (M : ℤ))
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (t : v.adicCompletion F) (A : (v.adicCompletion F)ˣ)
    (hA : (A : v.adicCompletion F) = 1 + t * c)
    (t' : v.adicCompletion F) (htcoord : t' = t / (A : v.adicCompletion F))
    (htSupport : t ∈ tsupport φ ∨ t' ∈ tsupport φ) :
    bigCell L T s φ
        ((L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) * L.nbar (Multiplicative.ofAdd c)) =
      bigCell L T s φ
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) := by
  classical
  let K := v.adicCompletion F
  have hAval : Valued.v (A : K) = 1 := by
    rcases htSupport with htS | ht'S
    · have htBound := hS htS
      have htcBound := ball_mul_ind htBound hc
      have htcBound' : t * c ∈ ball v ((M - R : ℕ) : ℤ) := by
        have hexp : -(R : ℤ) + (M : ℤ) = ((M - R : ℕ) : ℤ) := by omega
        simpa [hexp] using htcBound
      have hR1' : (1 : ℤ) ≤ ((M - R : ℕ) : ℤ) := by
        have hR1Nat : 1 ≤ M - R := by omega
        exact_mod_cast hR1Nat
      have htcOne : t * c ∈ ball v 1 := ball_mono_ind hR1' htcBound'
      have hsmall := ball_one_valued_lt_one_ind htcOne
      calc
        Valued.v (A : K) = Valued.v (1 + t * c) := by rw [hA]
        _ = 1 := valued_one_add_eq_one_ind (t * c) hsmall
    · have ht'Bound := hS ht'S
      have htcBound : t' * c ∈ ball v (mT : ℤ) := by
        have h := ball_mul_ind ht'Bound hc
        have hexp : -(R : ℤ) + (M : ℤ) = ((M - R : ℕ) : ℤ) := by omega
        have h' : t' * c ∈ ball v ((M - R : ℕ) : ℤ) := by simpa [hexp] using h
        have hmTNat : mT ≤ M - R := by omega
        exact ball_mono_ind (by exact_mod_cast hmTNat) h'
      have hmT1 : (1 : ℤ) ≤ (mT : ℤ) := by exact_mod_cast (Nat.succ_le_iff.mpr hmT)
      have htcOne : t' * c ∈ ball v 1 := ball_mono_ind hmT1 htcBound
      have hsmall := ball_one_valued_lt_one_ind htcOne
      have htMul : t' * (A : K) = t := by
        calc
          t' * (A : K) = (t / (A : K)) * (A : K) := by rw [htcoord]
          _ = t := by field_simp [A.ne_zero]
      have hrel : (A : K) * (1 - t' * c) = 1 := by
        calc
          (A : K) * (1 - t' * c) = (A : K) - (t' * (A : K)) * c := by ring
          _ = 1 := by rw [htMul, hA]; ring
      have hAinv : ((A⁻¹ : Kˣ) : K) = 1 - t' * c := by
        simpa using (eq_inv_of_mul_eq_one_right hrel).symm
      have hsmallNeg : Valued.v (-(t' * c)) < 1 := by simpa using hsmall
      have hInvVal : Valued.v ((A⁻¹ : Kˣ) : K) = 1 := by
        rw [hAinv]
        simpa [sub_eq_add_neg] using valued_one_add_eq_one_ind (-(t' * c)) hsmallNeg
      calc
        Valued.v (A : K) = Valued.v (A : K) * 1 := by simp
        _ = Valued.v (A : K) * Valued.v ((A⁻¹ : Kˣ) : K) := by rw [hInvVal]
        _ = Valued.v ((A : K) * ((A⁻¹ : Kˣ) : K)) := by rw [← map_mul]
        _ = 1 := by simp
  have htBound : t ∈ ball v (-(R : ℤ)) := by
    rcases htSupport with htS | ht'S
    · exact hS htS
    · have ht'Bound := hS ht'S
      have hABall : (A : K) ∈ ball v 0 := by
        change Valued.v (A : K) ≤ WithZero.exp 0
        rw [hAval]
        simp
      have htMul : t' * (A : K) = t := by
        calc
          t' * (A : K) = (t / (A : K)) * (A : K) := by rw [htcoord]
          _ = t := by field_simp [A.ne_zero]
      rw [← htMul]
      simpa using ball_mul_ind ht'Bound hABall
  have hRM : R ≤ M := by omega
  have hM2R : 2 * R ≤ M := by omega
  have htcBound : t * c ∈ ball v ((M - R : ℕ) : ℤ) := by
    have h := ball_mul_ind htBound hc
    have hexp : -(R : ℤ) + (M : ℤ) = ((M - R : ℕ) : ℤ) := by omega
    simpa [hexp] using h
  have hAminusMR : (A : K) - 1 ∈ ball v ((M - R : ℕ) : ℤ) := by
    have heq : (A : K) - 1 = t * c := by rw [hA]; ring
    rw [heq]
    exact htcBound
  have hAminusMT : (A : K) - 1 ∈ ball v (mT : ℤ) := by
    have hmTNat : mT ≤ M - R := by omega
    have hmTle : (mT : ℤ) ≤ ((M - R : ℕ) : ℤ) := by exact_mod_cast hmTNat
    exact ball_mono_ind hmTle hAminusMR
  have hσA : T.σa A = LinearMap.id := hsm A hAminusMT
  have hσInvSq := torus_sigma_inv_square_of_id_ind T A hσA
  let u : Kˣ := A⁻¹ * A⁻¹
  have hσu : T.σa u = LinearMap.id := by simpa [u] using hσInvSq.2
  have hAinvVal : Valued.v ((A⁻¹ : Kˣ) : K) = 1 := by simpa [hAval]
  have hUVal : Valued.v (u : K) = 1 := by
    change Valued.v (((A⁻¹ : Kˣ) : K) * ((A⁻¹ : Kˣ) : K)) = 1
    rw [map_mul]
    simp [hAval]
  have huLoc : IsLocUnit v u := isLocUnit_of_valued_one_ind u hUVal
  have hphase : muThree D (H.hilb v y u) = 1 :=
    muThree_hilb_one_of_sigmaa_id T y u hσu
  have hact : T.σa (y * u) = T.σa y := by
    have hmul := T.σa_mul y u
    rw [hσu] at hmul
    have hmul' : T.σa y =
        ((muThree D (H.hilb v y u) : ℂˣ) : ℂ) • T.σa (y * u) := by
      simpa [LinearMap.comp_id] using hmul
    simpa [hphase] using hmul'.symm
  have habs : absFin v (y * u) = absFin v y := by
    rw [absFin_mul_ind v y u, absFin_one_of_locUnit u huLoc]
    simp
  have hAinvBall : ((A⁻¹ : Kˣ) : K) ∈ ball v 0 := by
    change Valued.v ((A⁻¹ : Kˣ) : K) ≤ WithZero.exp 0
    have hval : Valued.v ((A⁻¹ : Kˣ) : K) = 1 := by simpa [hAval]
    rw [hval]
    simp
  have ht2cBound : t * (t * c) ∈ ball v ((M - 2 * R : ℕ) : ℤ) := by
    have h := ball_mul_ind htBound htcBound
    have hexp : -(R : ℤ) + ((M - R : ℕ) : ℤ) = ((M - 2 * R : ℕ) : ℤ) := by omega
    simpa [hexp] using h
  have hshiftEq : t / (A : K) - t = -(t * (t * c) * ((A⁻¹ : Kˣ) : K)) := by
    rw [div_eq_mul_inv, Units.val_inv_eq_inv_val]
    field_simp [A.ne_zero]
    rw [hA]
    ring
  have hshiftBound : t / (A : K) - t ∈ ball v ((M - 2 * R : ℕ) : ℤ) := by
    have h := ball_mul_ind ht2cBound hAinvBall
    have hneg := ball_neg_ind h
    have hexp : ((M - 2 * R : ℕ) : ℤ) + 0 = ((M - 2 * R : ℕ) : ℤ) := by omega
    have hneg' : -(t * (t * c) * ((A⁻¹ : Kˣ) : K)) ∈
        ball v ((M - 2 * R : ℕ) : ℤ) := by simpa [hexp] using hneg
    rw [hshiftEq]
    exact hneg'
  have hshiftK : t / (A : K) - t ∈ ball v (k : ℤ) :=
    ball_mono_ind (by omega) hshiftBound
  have hphi : φ (t / (A : K)) = φ t := by
    have h := hadd t (t / (A : K) - t) hshiftK
    calc
      φ (t / (A : K)) = φ (t + (t / (A : K) - t)) := by congr 1 <;> ring
      _ = φ t := h
  let b : K := c / (A : K)
  let r : K := t / (A : K)
  let x' : K := x + b * (y : K)
  let y' : Kˣ := y * u
  have hWbar : L.w * L.nbar (Multiplicative.ofAdd c) =
      L.n (Multiplicative.ofAdd c) * L.w := by
    calc
      L.w * L.nbar (Multiplicative.ofAdd c) = L.w *
          (L.w * L.n (Multiplicative.ofAdd c) * L.w) := by rw [← L.w_n_w c]
      _ = L.n (Multiplicative.ofAdd c) * L.w := by
        calc
          _ = (L.w * L.w) * L.n (Multiplicative.ofAdd c) * L.w := by group
          _ = _ := by rw [L.w_sq]; simp
  have hWtail : L.w * L.n (Multiplicative.ofAdd t) *
      L.nbar (Multiplicative.ofAdd c) =
        L.nbar (Multiplicative.ofAdd t) * L.n (Multiplicative.ofAdd c) * L.w := by
    calc
      _ = L.w * L.n (Multiplicative.ofAdd t) * (L.w * L.w) *
          L.nbar (Multiplicative.ofAdd c) := by rw [L.w_sq]; group
      _ = (L.w * L.n (Multiplicative.ofAdd t) * L.w) *
          (L.w * L.nbar (Multiplicative.ofAdd c)) := by group
      _ = _ := by rw [L.w_n_w t, hWbar]; group
  have hgauss := bigCell_gauss_lift L T t c A hA hσA
  have hmove : L.a y * L.n (Multiplicative.ofAdd b) =
      L.n (Multiplicative.ofAdd (b * (y : K))) * L.a y := by
    simpa [b, Units.val_inv_eq_inv_val] using
      (L.lift_na (b * (y : K)) y).symm
  have hmulN : L.n (Multiplicative.ofAdd x) *
      L.n (Multiplicative.ofAdd (b * (y : K))) =
        L.n (Multiplicative.ofAdd (x + b * (y : K))) := by
    rw [← map_mul]
    simp
  have hmulA : L.a y * L.a u = L.a (y * u) := by
    calc
      L.a y * L.a u = L.z (muThree D (H.hilb v y u)) * L.a (y * u) := L.a_mul y u
      _ = L.a (y * u) := by rw [hphase]; simp
  have hprod : (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
      L.n (Multiplicative.ofAdd t)) * L.nbar (Multiplicative.ofAdd c) =
        L.n (Multiplicative.ofAdd x') * L.z ζ * L.a y' * L.w *
          L.n (Multiplicative.ofAdd r) := by
    calc
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y *
          (L.w * L.n (Multiplicative.ofAdd t) * L.nbar (Multiplicative.ofAdd c)) := by group
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y *
          (L.nbar (Multiplicative.ofAdd t) * L.n (Multiplicative.ofAdd c) * L.w) := by
            rw [hWtail]
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
          (L.a y * L.n (Multiplicative.ofAdd b)) * L.a u * L.w *
            L.n (Multiplicative.ofAdd r) := by rw [hgauss]; dsimp [b, u, r]; group
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
          (L.n (Multiplicative.ofAdd (b * (y : K))) * L.a y) * L.a u * L.w *
            L.n (Multiplicative.ofAdd r) := by rw [hmove]
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
          L.n (Multiplicative.ofAdd (b * (y : K))) *
          (L.a y * L.a u) * L.w * L.n (Multiplicative.ofAdd r) := by
              group
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ *
          L.n (Multiplicative.ofAdd (b * (y : K))) * L.a (y * u) * L.w *
            L.n (Multiplicative.ofAdd r) := by rw [hmulA]
      _ = (L.n (Multiplicative.ofAdd x) *
          L.n (Multiplicative.ofAdd (b * (y : K)))) * L.z ζ * L.a (y * u) *
            L.w * L.n (Multiplicative.ofAdd r) := by
              have hz := L.z_central ζ (L.n (Multiplicative.ofAdd (b * (y : K))))
              calc
                _ = L.n (Multiplicative.ofAdd x) *
                    (L.z ζ * L.n (Multiplicative.ofAdd (b * (y : K)))) *
                      L.a (y * u) * L.w * L.n (Multiplicative.ofAdd r) := by group
                _ = L.n (Multiplicative.ofAdd x) *
                    (L.n (Multiplicative.ofAdd (b * (y : K))) * L.z ζ) *
                      L.a (y * u) * L.w * L.n (Multiplicative.ofAdd r) := by rw [hz]
                _ = _ := by group
      _ = L.n (Multiplicative.ofAdd x') * L.z ζ * L.a y' * L.w *
          L.n (Multiplicative.ofAdd r) := by
            simpa [x', y'] using
              (congrArg (fun q : L.L => q * L.z ζ * L.a (y * u) * L.w *
                L.n (Multiplicative.ofAdd r)) hmulN)
  calc
    bigCell L T s φ _ =
        ((ζ : ℂˣ) : ℂ) • ((absFin v y' : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa y' (φ r) := by
            rw [hprod]
            exact bigCell_eval_decomp L T s φ _ x' ζ y' r rfl
    _ = ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa y (φ t) := by
            dsimp [y']
            rw [habs, hact, hphi]
    _ = bigCell L T s φ _ := (bigCell_eval_decomp L T s φ _ x ζ y t rfl).symm

private theorem bigCell_right_nbar_ind (L : FinLocalCover D H v) (T : TorusRep D H v)
    [Nontrivial T.V] (s : ℂ) (φ : v.adicCompletion F → T.V) (R M k mT : ℕ)
    (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hadd : ∀ t z, z ∈ ball v (k : ℤ) → φ (t + z) = φ t)
    (hR2k : 2 * R + k ≤ M) (hRmT : R + mT ≤ M) (hR1 : R + 1 ≤ M)
    (hmT : 0 < mT)
    (hsm : ∀ u : (v.adicCompletion F)ˣ,
      ((u : v.adicCompletion F) - 1) ∈ ball v (mT : ℤ) → T.σa u = LinearMap.id)
    (c : v.adicCompletion F) (hc : c ∈ ball v (M : ℤ)) :
    ∀ x ζ y t,
      bigCell L T s φ
        ((L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) * L.nbar (Multiplicative.ofAdd c)) =
      bigCell L T s φ
        (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
          L.n (Multiplicative.ofAdd t)) := by
  classical
  intro x ζ y t
  let g₀ : L.L := L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
    L.n (Multiplicative.ofAdd t)
  let g : L.L := g₀ * L.nbar (Multiplicative.ofAdd c)
  let a₀ : v.adicCompletion F := 1 + t * c
  change bigCell L T s φ g = bigCell L T s φ g₀
  by_cases ha₀ : a₀ = 0
  · have hφt : φ t = 0 := by
      by_contra hφt
      have htS : t ∈ tsupport φ := by
        by_contra htS
        exact hφt (image_eq_zero_of_notMem_tsupport htS)
      have htBound := hS htS
      have htc := ball_mul_ind htBound hc
      have htcBound : t * c ∈ ball v ((M - R : ℕ) : ℤ) := by
        have hexp : -(R : ℤ) + (M : ℤ) = ((M - R : ℕ) : ℤ) := by omega
        simpa [hexp] using htc
      have hR1' : (1 : ℤ) ≤ ((M - R : ℕ) : ℤ) := by
        have hR1Nat : 1 ≤ M - R := by omega
        exact_mod_cast hR1Nat
      have htc1 : t * c ∈ ball v 1 := ball_mono_ind hR1' htcBound
      have hsmall := ball_one_valued_lt_one_ind htc1
      have hv := valued_one_add_eq_one_ind (t * c) hsmall
      have ha : 1 + t * c = 0 := by simpa [a₀] using ha₀
      rw [ha] at hv
      simp at hv
    have htne : t ≠ 0 := by
      intro ht0
      simp [a₀, ht0] at ha₀
    let tu : (v.adicCompletion F)ˣ := Units.mk0 t htne
    let ti : v.adicCompletion F := ((tu⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
    let u₀ : (v.adicCompletion F)ˣ := -(tu⁻¹ * tu⁻¹)
    have htc : t * c = -1 := by
      have ha : 1 + t * c = 0 := by simpa [a₀] using ha₀
      linear_combination ha
    have hcinv : c = -ti := by
      calc
        c = ti * t * c := by
          have hmul : ti * t = 1 := by
            dsimp [ti, tu]
            exact inv_mul_cancel₀ htne
          calc
            c = 1 * c := by simp
            _ = (ti * t) * c := by rw [hmul]
            _ = _ := by ring
        _ = ti * (-1) := by rw [show ti * t * c = ti * (t * c) by ring, htc]
        _ = -ti := by ring
    have hLift : L.w * L.n (Multiplicative.ofAdd t) =
        L.n (Multiplicative.ofAdd ti) * L.a u₀ * L.nbar (Multiplicative.ofAdd ti) := by
      simpa [tu, ti, u₀, Units.val_inv_eq_inv_val] using L.lift_wn tu
    have hsum : ti + c = 0 := by rw [hcinv]; simp [ti]
    have hbar : L.nbar (Multiplicative.ofAdd ti) *
        L.nbar (Multiplicative.ofAdd c) = 1 := by
      calc
        _ = L.nbar (Multiplicative.ofAdd ti * Multiplicative.ofAdd c) := by rw [← map_mul]
        _ = L.nbar (Multiplicative.ofAdd (ti + c)) := by simp
        _ = L.nbar (Multiplicative.ofAdd 0) := by rw [hsum]
        _ = 1 := by simp
    have htail : L.w * L.n (Multiplicative.ofAdd t) *
        L.nbar (Multiplicative.ofAdd c) =
        L.n (Multiplicative.ofAdd ti) * L.a u₀ := by
      calc
        _ = (L.w * L.n (Multiplicative.ofAdd t)) *
            L.nbar (Multiplicative.ofAdd c) := rfl
        _ = (L.n (Multiplicative.ofAdd ti) * L.a u₀ *
            L.nbar (Multiplicative.ofAdd ti)) * L.nbar (Multiplicative.ofAdd c) := by rw [hLift]
        _ = L.n (Multiplicative.ofAdd ti) * L.a u₀ *
            (L.nbar (Multiplicative.ofAdd ti) * L.nbar (Multiplicative.ofAdd c)) := by group
        _ = _ := by rw [hbar]; simp
    have htailB : L.n (Multiplicative.ofAdd ti) * L.a u₀ = borelElem L ti 1 u₀ := by
      simp [borelElem]
    have hprod : g = borelElem L (x + ti * (y : v.adicCompletion F))
        (ζ * muThree D (H.hilb v y u₀)) (y * u₀) := by
      dsimp [g, g₀]
      calc
        _ = borelElem L x ζ y * (L.w * L.n (Multiplicative.ofAdd t) *
            L.nbar (Multiplicative.ofAdd c)) := by dsimp [borelElem]; group
        _ = borelElem L x ζ y * borelElem L ti 1 u₀ := by rw [← htailB, htail]
        _ = _ := by simpa using (borelElem_mul L x ti ζ 1 y u₀)
    rw [hprod, bigCell_borel_zero_ind]
    rw [bigCell_eval_decomp L T s φ g₀ x ζ y t rfl]
    simp [hφt]
  · let A : (v.adicCompletion F)ˣ := Units.mk0 a₀ ha₀
    have hAval : (A : v.adicCompletion F) = a₀ := rfl
    let G : GL (Fin 2) (v.adicCompletion F) :=
      bigCellMatrix (F := F) x y t * lowerM (v.adicCompletion F) c
    have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
      intro η
      have hker : L.z η ∈ L.pr.ker := by
        rw [L.pr_ker]
        exact ⟨η, rfl⟩
      exact MonoidHom.mem_ker.mp hker
    have hprG : L.pr g = QuotientGroup.mk (G : GL (Fin 2) (v.adicCompletion F)) := by
      dsimp [g, g₀, G]
      simp [bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, L.pr_nbar, hz, mul_assoc]
    rcases bigCell_bruhat_cover L g with hsmall | hbig
    · obtain ⟨x', ζ', y', hsmallEq⟩ := hsmall
      have hpsmall : L.pr g = QuotientGroup.mk
          (upperM (v.adicCompletion F) x' * diagM (v.adicCompletion F) y') := by
        rw [hsmallEq]
        simp [borelElem, map_mul, L.pr_n, L.pr_a, hz]
      have hclass : (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
          QuotientGroup.mk (upperM (v.adicCompletion F) x' * diagM (v.adicCompletion F) y') :=
        hprG.symm.trans hpsmall
      have hG10 : (G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 ≠ 0 := by
        have hto : ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0).toCompletion =
            (A : v.adicCompletion F).toCompletion := by
          calc
            ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0).toCompletion =
                (1 + t * c).toCompletion := by
                  simp [G, bigCellMatrix, upperM, diagM, weylM, lowerM, Matrix.mul_apply,
                    Fin.sum_univ_two, adicCompletion_toCompletion_add_ind,
                    adicCompletion_toCompletion_mul_ind]
            _ = (A : v.adicCompletion F).toCompletion :=
              congrArg (fun z : v.adicCompletion F => z.toCompletion) hAval.symm
        intro hzero
        have hzto : ((G : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0).toCompletion = 0 := by
          rw [hzero]
          simp
        have hAt : (A : v.adicCompletion F).toCompletion = 0 := hto.symm.trans hzto
        have hA0 : (A : v.adicCompletion F) = 0 :=
          (HeightOneSpectrum.adicCompletion.equiv F v).injective hAt
        exact A.ne_zero hA0
      exact (gl2_class_not_borel_of_lowerleft_ne G hG10 x' y' hclass).elim
    · obtain ⟨x', ζ', y', t', hbigEq⟩ := hbig
      have hprBig : L.pr g = QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := by
        have h := congrArg L.pr hbigEq
        simpa [bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz, mul_assoc] using h
      have hclassBig : (QuotientGroup.mk G : PGL2 (v.adicCompletion F)) =
          QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := hprG.symm.trans hprBig
      have hclassCoord := bigCell_right_nbar_projective_ind x y t c A hAval
      let x₀ := x + (y : v.adicCompletion F) * (c / (A : v.adicCompletion F))
      let y₀ := y * (A⁻¹ * A⁻¹)
      let t₀ := t / (A : v.adicCompletion F)
      let cand : L.L := L.n (Multiplicative.ofAdd x₀) * L.a y₀ * L.w *
        L.n (Multiplicative.ofAdd t₀)
      have hprCand : L.pr cand = QuotientGroup.mk (bigCellMatrix (F := F) x₀ y₀ t₀) := by
        simp [cand, bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w]
      have hpLift : L.pr g = L.pr cand :=
        hprG.trans (hclassCoord.trans hprCand.symm)
      obtain ⟨η, hLift⟩ := lift_pr_eq L g cand hpLift
      have hLiftCanon : g = L.n (Multiplicative.ofAdd x₀) * L.z η * L.a y₀ * L.w *
          L.n (Multiplicative.ofAdd t₀) := by
        calc
          g = L.z η * cand := hLift
          _ = L.n (Multiplicative.ofAdd x₀) * L.z η * L.a y₀ * L.w *
              L.n (Multiplicative.ofAdd t₀) := by
                dsimp [cand]
                calc
                  L.z η * (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * L.w *
                      L.n (Multiplicative.ofAdd t₀)) =
                      (L.z η * L.n (Multiplicative.ofAdd x₀)) * L.a y₀ * L.w *
                        L.n (Multiplicative.ofAdd t₀) := by group
                  _ = (L.n (Multiplicative.ofAdd x₀) * L.z η) * L.a y₀ * L.w *
                        L.n (Multiplicative.ofAdd t₀) := by
                          rw [L.z_central η (L.n (Multiplicative.ofAdd x₀))]
                  _ = _ := by group
      have hcoords := bigCell_coords_unique L x' x₀ ζ' η y' y₀ t' t₀
        (hbigEq.symm.trans hLiftCanon)
      rcases hcoords with ⟨_, _, htcoord, _⟩
      by_cases hφt : φ t ≠ 0
      · have htS : t ∈ tsupport φ := by
          by_contra htS
          exact hφt (image_eq_zero_of_notMem_tsupport htS)
        exact bigCell_right_nbar_nonzero L T s φ R M k mT hS hadd hR2k hRmT hR1 hmT hsm
          c hc x ζ y t A hAval t₀ (by rfl) (Or.inl htS)
      · by_cases ht0 : φ t₀ ≠ 0
        · have ht0S : t₀ ∈ tsupport φ := by
            by_contra hnot
            exact ht0 (image_eq_zero_of_notMem_tsupport hnot)
          exact bigCell_right_nbar_nonzero L T s φ R M k mT hS hadd hR2k hRmT hR1 hmT hsm
            c hc x ζ y t A hAval t₀ (by rfl) (Or.inr ht0S)
        · rw [bigCell_eval_decomp L T s φ g x' ζ' y' t' hbigEq,
            bigCell_eval_decomp L T s φ g₀ x ζ y t rfl]
          have hφt0 : φ t = 0 := not_ne_iff.mp hφt
          have hφt'0 : φ t₀ = 0 := not_ne_iff.mp ht0
          simpa [htcoord, hφt0, hφt'0]

private theorem borel_right_nbar_projective_ind
    (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
    (c : v.adicCompletion F) (C : (v.adicCompletion F)ˣ)
    (hC : (C : v.adicCompletion F) = c) :
    (QuotientGroup.mk (upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
      lowerM (v.adicCompletion F) c) : PGL2 (v.adicCompletion F)) =
    QuotientGroup.mk (bigCellMatrix (F := F)
      (x + (y : v.adicCompletion F) * (C⁻¹ : v.adicCompletion F))
      (-(y * (C⁻¹ * C⁻¹))) (C⁻¹ : v.adicCompletion F)) := by
  let K := v.adicCompletion F
  let G : GL (Fin 2) K := upperM K x * diagM K y * lowerM K c
  let xp : K := x + (y : K) * (C⁻¹ : K)
  let yp : Kˣ := -(y * (C⁻¹ * C⁻¹))
  let tp : K := (C⁻¹ : K)
  have hCto : (C : K).toCompletion = c.toCompletion :=
    congrArg (fun z : K => z.toCompletion) hC
  have hCinvTo : ((C⁻¹ : Kˣ) : K).toCompletion = (c.toCompletion)⁻¹ := by
    rw [adicCompletion_toCompletion_unitInv_ind, hCto]
  have hcne : c ≠ 0 := by rw [← hC]; exact C.ne_zero
  have hcneTo : c.toCompletion ≠ 0 :=
    (map_ne_zero (HeightOneSpectrum.adicCompletion.equiv F v)).2 hcne
  have hmat : G * Matrix.GeneralLinearGroup.scalar (Fin 2) C⁻¹ =
      bigCellMatrix (F := F) xp yp tp := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [G, xp, yp, tp, bigCellMatrix, upperM, diagM, weylM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, adicCompletion_toCompletion_add_ind,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind,
        adicCompletion_toCompletion_unitInv_ind, adicCompletion_toCompletion_unitMul_ind,
        hC, hCto, hCinvTo]
      rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_add_ind,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      field_simp [hcneTo]
      ring_nf
    · simp [G, xp, yp, tp, bigCellMatrix, upperM, diagM, weylM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, adicCompletion_toCompletion_add_ind,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind,
        adicCompletion_toCompletion_unitInv_ind, adicCompletion_toCompletion_unitMul_ind,
        hC, hCto, hCinvTo]
      have hleft : (x * c⁻¹).toCompletion = x.toCompletion * c.toCompletion⁻¹ := by
        rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      have hyc : ((y : K) * c⁻¹).toCompletion = (y : K).toCompletion * c.toCompletion⁻¹ := by
        rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      have hcinv : c⁻¹.toCompletion = c.toCompletion⁻¹ :=
        adicCompletion_toCompletion_inv_ind c
      have hneg : (-((y : K) * (c⁻¹ * c⁻¹))).toCompletion =
          -((y : K).toCompletion * (c.toCompletion⁻¹ * c.toCompletion⁻¹)) := by
        calc
          (-((y : K) * (c⁻¹ * c⁻¹))).toCompletion =
              -(((y : K) * (c⁻¹ * c⁻¹)).toCompletion) := by
                exact map_neg (HeightOneSpectrum.adicCompletion.equiv F v) _
          _ = -((y : K).toCompletion * (c⁻¹ * c⁻¹).toCompletion) := by
                rw [adicCompletion_toCompletion_mul_ind]
          _ = -((y : K).toCompletion * (c.toCompletion⁻¹ * c.toCompletion⁻¹)) := by
                simp [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]
      rw [hleft, hyc, hcinv, hneg]
      field_simp [hcneTo]
      ring_nf
    · simp [G, xp, yp, tp, bigCellMatrix, upperM, diagM, weylM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, adicCompletion_toCompletion_add_ind,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_unitInv_ind,
        adicCompletion_toCompletion_unitMul_ind, hC, hCto, hCinvTo] <;>
        (try rw [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind]) <;>
        field_simp [hcneTo] <;> ring_nf
    all_goals
      simp [G, xp, yp, tp, bigCellMatrix, upperM, diagM, weylM, lowerM,
        Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two,
        Units.val_inv_eq_inv_val, adicCompletion_toCompletion_add_ind,
        adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind,
        adicCompletion_toCompletion_unitInv_ind, adicCompletion_toCompletion_unitMul_ind,
        hC, hCto, hCinvTo] <;>
        (try simp only [adicCompletion_toCompletion_mul_ind, adicCompletion_toCompletion_inv_ind,
          map_neg]) <;>
        (try rw [adicCompletion_toCompletion_inv_ind]) <;>
        field_simp [hcneTo] <;> ring_nf
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨C⁻¹, ?_⟩
  simpa [G, xp, yp, tp] using hmat

private theorem bigCell_right_nbar_small_ind (L : FinLocalCover D H v)
    (T : TorusRep D H v) (s : ℂ) (φ : v.adicCompletion F → T.V)
    (R M : ℕ) (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hR1 : R + 1 ≤ M) (c : v.adicCompletion F) (hc : c ∈ ball v (M : ℤ))
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (borelElem L x ζ y * L.nbar (Multiplicative.ofAdd c)) =
      bigCell L T s φ (borelElem L x ζ y) := by
  classical
  have hbase : bigCell L T s φ (borelElem L x ζ y) = 0 := by
    exact bigCell_borel_zero_ind L T s φ x ζ y
  by_cases hc0 : c = 0
  · simpa [hc0, borelElem] using hbase
  · let K := v.adicCompletion F
    let C : Kˣ := Units.mk0 c hc0
    have hC : (C : K) = c := rfl
    let t₀ : K := (C⁻¹ : Kˣ)
    have ht₀out : t₀ ∉ ball v (-(R : ℤ)) := by
      intro ht₀
      have hprod := ball_mul_ind hc ht₀
      have hprod' : c * t₀ ∈ ball v ((M - R : ℕ) : ℤ) := by
        have hexp : (M : ℤ) + (-(R : ℤ)) = ((M - R : ℕ) : ℤ) := by omega
        simpa [hexp] using hprod
      have hprodEq : c * t₀ = 1 := by
        calc
          c * t₀ = (C : K) * ((C⁻¹ : Kˣ) : K) := by rw [hC]
          _ = 1 := by simp
      have h1ball : (1 : K) ∈ ball v ((M - R : ℕ) : ℤ) := by
        simpa [hprodEq] using hprod'
      have hR1' : (1 : ℤ) ≤ ((M - R : ℕ) : ℤ) := by
        have hR1Nat : 1 ≤ M - R := by omega
        exact_mod_cast hR1Nat
      have h1ball' : (1 : K) ∈ ball v 1 := ball_mono_ind hR1' h1ball
      have hlt := ball_one_valued_lt_one_ind h1ball'
      simp at hlt
    let G : GL (Fin 2) K := upperM K x * diagM K y * lowerM K c
    let g : L.L := borelElem L x ζ y * L.nbar (Multiplicative.ofAdd c)
    have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
      intro η
      have hker : L.z η ∈ L.pr.ker := by
        rw [L.pr_ker]
        exact ⟨η, rfl⟩
      exact MonoidHom.mem_ker.mp hker
    have hprG : L.pr g = QuotientGroup.mk (G : GL (Fin 2) K) := by
      dsimp [g, G, borelElem]
      simp [map_mul, L.pr_n, L.pr_a, L.pr_nbar, hz] <;> rfl
    have hG10 : (G : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      simpa [G, upperM, diagM, lowerM, Matrix.mul_apply, Fin.sum_univ_two] using hc0
    rcases bigCell_bruhat_cover L g with hsmall | hbig
    · obtain ⟨x', ζ', y', hsmallEq⟩ := hsmall
      have hpsmall : L.pr g = QuotientGroup.mk
          (upperM K x' * diagM K y') := by
        rw [hsmallEq]
        simp [borelElem, map_mul, L.pr_n, L.pr_a, hz] <;> rfl
      have hclass : (QuotientGroup.mk G : PGL2 K) =
          QuotientGroup.mk (upperM K x' * diagM K y') := hprG.symm.trans hpsmall
      exact (gl2_class_not_borel_of_lowerleft_ne G hG10 x' y' hclass).elim
    · obtain ⟨x', ζ', y', t', hbigEq⟩ := hbig
      have hprBig : L.pr g = QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := by
        have h := congrArg L.pr hbigEq
        simpa [bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz, mul_assoc] using h
      have hclassBig : (QuotientGroup.mk G : PGL2 K) =
          QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := hprG.symm.trans hprBig
      have hclassCoord := borel_right_nbar_projective_ind x y c C hC
      let x₀ : K := x + (y : K) * (C⁻¹ : K)
      let y₀ : Kˣ := -(y * (C⁻¹ * C⁻¹))
      let cand : L.L := L.n (Multiplicative.ofAdd x₀) * L.a y₀ * L.w *
        L.n (Multiplicative.ofAdd t₀)
      have hprCand : L.pr cand = QuotientGroup.mk (bigCellMatrix (F := F) x₀ y₀ t₀) := by
        simp [cand, bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w]
      have hpLift : L.pr g = L.pr cand := hprG.trans (hclassCoord.trans hprCand.symm)
      obtain ⟨η, hLift⟩ := lift_pr_eq L g cand hpLift
      have hLiftCanon : g = L.n (Multiplicative.ofAdd x₀) * L.z η * L.a y₀ * L.w *
          L.n (Multiplicative.ofAdd t₀) := by
        calc
          g = L.z η * cand := hLift
          _ = L.n (Multiplicative.ofAdd x₀) * L.z η * L.a y₀ * L.w *
              L.n (Multiplicative.ofAdd t₀) := by
                dsimp [cand]
                calc
                  L.z η * (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * L.w *
                      L.n (Multiplicative.ofAdd t₀)) =
                      (L.z η * L.n (Multiplicative.ofAdd x₀)) * L.a y₀ * L.w *
                        L.n (Multiplicative.ofAdd t₀) := by group
                  _ = (L.n (Multiplicative.ofAdd x₀) * L.z η) * L.a y₀ * L.w *
                        L.n (Multiplicative.ofAdd t₀) := by
                          rw [L.z_central η (L.n (Multiplicative.ofAdd x₀))]
                  _ = _ := by group
      have hcoords := bigCell_coords_unique L x' x₀ ζ' η y' y₀ t' t₀
        (hbigEq.symm.trans hLiftCanon)
      rcases hcoords with ⟨_, _, htcoord, _⟩
      have hφt₀ : φ t₀ = 0 := image_eq_zero_of_notMem_tsupport (by
        intro ht
        exact ht₀out (hS ht))
      have hφt' : φ t' = 0 := by simpa [htcoord] using hφt₀
      have hleft : bigCell L T s φ g = 0 := by
        rw [bigCell_eval_decomp L T s φ g x' ζ' y' t' hbigEq]
        simp [hφt']
      rw [hleft, hbase]

private theorem bigCell_right_nbar_all_ind (L : FinLocalCover D H v)
    (T : TorusRep D H v) [Nontrivial T.V] (s : ℂ)
    (φ : v.adicCompletion F → T.V) (R M k mT : ℕ)
    (hS : tsupport φ ⊆ ball v (-(R : ℤ)))
    (hadd : ∀ t z, z ∈ ball v (k : ℤ) → φ (t + z) = φ t)
    (hR2k : 2 * R + k ≤ M) (hRmT : R + mT ≤ M) (hR1 : R + 1 ≤ M)
    (hmT : 0 < mT)
    (hsm : ∀ u : (v.adicCompletion F)ˣ,
      ((u : v.adicCompletion F) - 1) ∈ ball v (mT : ℤ) → T.σa u = LinearMap.id)
    (c : v.adicCompletion F) (hc : c ∈ ball v (M : ℤ)) (g : L.L) :
    bigCell L T s φ (g * L.nbar (Multiplicative.ofAdd c)) = bigCell L T s φ g := by
  classical
  rcases bigCell_bruhat_cover L g with hsmall | hbig
  · obtain ⟨x, ζ, y, rfl⟩ := hsmall
    exact bigCell_right_nbar_small_ind L T s φ R M hS hR1 c hc x ζ y
  · obtain ⟨x, ζ, y, t, rfl⟩ := hbig
    exact bigCell_right_nbar_ind L T s φ R M k mT hS hadd hR2k hRmT hR1 hmT hsm
      c hc x ζ y t

private theorem bigCell_rightKc_invariant (L : FinLocalCover D H v)
    (T : TorusRep D H v) [Nontrivial T.V] (s : ℂ)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) :
    ∃ m, L.m0 ≤ m ∧ ∀ g, ∀ k ∈ L.Kc m,
      bigCell L T s φ (g * k) = bigCell L T s φ g := by
    obtain ⟨R, hR⟩ := compact_support_ball T φ hc
    obtain ⟨k, hadd⟩ := bigCell_phi_add_invariant T φ hφ hc
    obtain ⟨mT, hmT, hsm⟩ := T.σa_smooth
    let N : ℕ := L.m0 + 1 + (2 * R + k) + (R + mT) + (R + 1)
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hm0N : L.m0 ≤ N := by dsimp [N]; omega
    have hkN : k ≤ N := by dsimp [N]; omega
    have hR2k : 2 * R + k ≤ N := by dsimp [N]; omega
    have hRk : R + k ≤ N := by dsimp [N]; omega
    have hRmT : R + mT ≤ N := by dsimp [N]; omega
    have hR1 : R + 1 ≤ N := by dsimp [N]; omega
    let U : Set L.L := L.pr ⁻¹' (QuotientGroup.mk ''
      nearIdMat (F := F) (v := v) N)
    have hchartOpen : IsOpen (QuotientGroup.mk ''
        nearIdMat (F := F) (v := v) N : Set (PGL2 (v.adicCompletion F))) := by
      exact (QuotientGroup.isOpenQuotientMap_mk
        (N := Subgroup.center (GL (Fin 2) (v.adicCompletion F)))).isOpenMap _
          (nearIdMat_isOpen N)
    have hUopen : IsOpen U := hchartOpen.preimage L.pr_cont
    have hUone : (1 : L.L) ∈ U := by
      change L.pr 1 ∈ QuotientGroup.mk '' nearIdMat (F := F) (v := v) N
      rw [map_one]
      refine ⟨1, ?_, ?_⟩
      · simp [nearIdMat, ball]
      · simp
    have hUnhds : U ∈ nhds (1 : L.L) := hUopen.mem_nhds hUone
    obtain ⟨m, hm, hsub⟩ := L.Kc_nhds U hUnhds
    let mFinal : ℕ := max m N
    have hmFinal : L.m0 ≤ mFinal := le_trans hm (le_max_left m N)
    have hmFinal_m : m ≤ mFinal := le_max_left m N
    have hNFinal : N ≤ mFinal := le_max_right m N
    refine ⟨mFinal, hmFinal, ?_⟩
    intro g k' hk'
    have hk_m : k' ∈ L.Kc m := L.Kc_anti m mFinal hm hmFinal_m hk'
    have hkU : k' ∈ U := hsub hk_m
    change L.pr k' ∈ QuotientGroup.mk '' nearIdMat (F := F) (v := v) N at hkU
    obtain ⟨G, hG, hproj⟩ := hkU
    obtain ⟨b, c, u, hb, hc, hu, hclass⟩ := nearIdMat_factor N hN G hG
    let q : L.L := L.n (Multiplicative.ofAdd b) * L.a u *
      L.nbar (Multiplicative.ofAdd c)
    have hnbK : L.n (Multiplicative.ofAdd b) ∈ L.Kc N := L.n_Kc N hm0N b hb
    have haK : L.a u ∈ L.Kc N := L.a_Kc N hm0N u hu
    have hbarK : L.nbar (Multiplicative.ofAdd c) ∈ L.Kc N := L.nbar_Kc N hm0N c hc
    have hqK : q ∈ L.Kc N := by
      dsimp [q]
      exact (L.Kc N).mul_mem ((L.Kc N).mul_mem hnbK haK) hbarK
    have hp : L.pr k' = L.pr q := by
      calc
        L.pr k' = QuotientGroup.mk G := hproj.symm
        _ = QuotientGroup.mk (upperM (v.adicCompletion F) b *
            diagM (v.adicCompletion F) u * lowerM (v.adicCompletion F) c) := hclass
        _ = L.pr q := by
          dsimp [q]
          simp [map_mul, L.pr_n, L.pr_a, L.pr_nbar]
    have hkN' : k' ∈ L.Kc N := L.Kc_anti N mFinal hm0N hNFinal hk'
    have hkEq : k' = q := (L.Kc_inj N hm0N) hkN' hqK hp
    have hbK : b ∈ ball v (k : ℤ) :=
      ball_mono_ind (by exact_mod_cast hkN) hb
    have huVal : Valued.v (u : v.adicCompletion F) = 1 :=
      unit_val_one_of_near_one_ind N hN u hu
    have huLoc : IsLocUnit v u := isLocUnit_of_valued_one_ind u huVal
    have huMT : ((u : v.adicCompletion F) - 1) ∈ ball v (mT : ℤ) :=
      ball_mono_ind (by exact_mod_cast (show mT ≤ N by dsimp [N]; omega)) hu
    have hσu : T.σa u = LinearMap.id := hsm u huMT
    have hσuinv : T.σa u⁻¹ = LinearMap.id :=
      (torus_sigma_inv_square_of_id_ind T u hσu).1
    calc
      bigCell L T s φ (g * k') = bigCell L T s φ (g * q) := by rw [hkEq]
      _ = bigCell L T s φ
          ((g * L.n (Multiplicative.ofAdd b) * L.a u) *
            L.nbar (Multiplicative.ofAdd c)) := by dsimp [q]; group
      _ = bigCell L T s φ (g * L.n (Multiplicative.ofAdd b) * L.a u) :=
        bigCell_right_nbar_all_ind L T s φ R N k mT hR hadd hR2k hRmT hR1 hmT hsm
          c hc (g * L.n (Multiplicative.ofAdd b) * L.a u)
      _ = bigCell L T s φ (g * L.n (Multiplicative.ofAdd b)) :=
        bigCell_right_a_ind L T s φ R N k hR hadd hRk hN u hu hσu hσuinv huLoc
          (g * L.n (Multiplicative.ofAdd b))
      _ = bigCell L T s φ g := bigCell_right_n_ind L T s φ k hadd b hbK g

/-- **ind:bigcell-section**: `bigCell φ` is a section when `φ` is locally constant with compact
support (the decomposition in the big cell is unique). -/
theorem bigCell_isSection (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    IsSection L T s (bigCell L T s φ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x y g
    have h := bigCell_leftBorel L T s φ x 1 y g
    simpa [borelElem, sphericalBorelAction] using h
  · intro ζ g
    have hb : borelElem L 0 ζ 1 = L.z ζ := by
      simp [borelElem, L.a_one]
    calc
      bigCell L T s φ (L.z ζ * g) =
          bigCell L T s φ (borelElem L 0 ζ 1 * g) := by rw [← hb]
      _ = sphericalBorelAction T s 0 ζ 1 (bigCell L T s φ g) :=
        bigCell_leftBorel L T s φ 0 ζ 1 g
      _ = ((ζ : ℂˣ) : ℂ) • bigCell L T s φ g := by
        simp [sphericalBorelAction, T.σa_one, absFin_eq_norm_ind]
  · by_cases hV : Nontrivial T.V
    · letI : Nontrivial T.V := hV
      exact bigCell_rightKc_invariant L T s φ hφ hc
    · letI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV
      refine ⟨L.m0, le_rfl, ?_⟩
      intro g k hk
      exact Subsingleton.elim _ _

/-- **ind:bigcell-apply**: the value of a big-cell section on the big cell (uniqueness of the
decomposition `n(x) z(ζ) a(y) w n(t)`), and its vanishing on the small cell `B̃`. -/
theorem bigCell_apply (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)) =
      ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
  exact bigCell_eval_decomp L T s φ _ x ζ y t rfl

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

private theorem sphericalC_bottomRow_pos (g : GL (Fin 2) ℂ) :
    0 < ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 := by
  by_cases h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
      intro h11
      apply g.det_ne_zero
      rw [Matrix.det_fin_two, h10, h11]
      simp
    positivity
  · positivity

private theorem sphericalC_scalar_invariant (s : ℂ) (c : ℂˣ)
    (g : GL (Fin 2) ℂ) :
    sphericalC s (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = sphericalC s g := by
  let G : Matrix (Fin 2) (Fin 2) ℂ := g
  let r := ‖(c : ℂ)‖ ^ 2
  have hc : r ≠ 0 := by
    have hcn : ‖(c : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr c.ne_zero
    exact pow_ne_zero 2 hcn
  have hdet : ‖((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ =
        r * ‖G.det‖ := by
    simp [G, r, Matrix.det_mul, Matrix.GeneralLinearGroup.scalar, Matrix.det_fin_two,
      norm_mul, pow_two]
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
        (c : ℂ) * G 1 0 := by
    simp [G, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :
      GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
        (c : ℂ) * G 1 1 := by
    simp [G, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  have hden :
      ‖((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :
          GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖((Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :
          GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      r * (‖G 1 0‖ ^ 2 + ‖G 1 1‖ ^ 2) := by
    rw [h10, h11, norm_mul, norm_mul]
    dsimp [r]
    ring
  have hratio :
      (r * ‖G.det‖) / (r * (‖G 1 0‖ ^ 2 + ‖G 1 1‖ ^ 2)) =
        ‖G.det‖ / (‖G 1 0‖ ^ 2 + ‖G 1 1‖ ^ 2) := by
    field_simp [hc, (sphericalC_bottomRow_pos g).ne']
  unfold sphericalC
  rw [hdet, hden, hratio]

private theorem sphericalC_leftBorel (s : ℂ) (x : ℂ) (y : ℂˣ)
    (g : GL (Fin 2) ℂ) :
    sphericalC s (upperM ℂ x * diagM ℂ y * g) =
      ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) * sphericalC s g := by
  let G : Matrix (Fin 2) (Fin 2) ℂ := g
  let B : GL (Fin 2) ℂ := upperM ℂ x * diagM ℂ y
  let r : ℝ := ‖G.det‖ / (‖G 1 0‖ ^ 2 + ‖G 1 1‖ ^ 2)
  have hden : 0 < ‖G 1 0‖ ^ 2 + ‖G 1 1‖ ^ 2 := sphericalC_bottomRow_pos g
  have hy : 0 < ‖(y : ℂ)‖ := norm_pos_iff.mpr y.ne_zero
  have hdetB : (B : Matrix (Fin 2) (Fin 2) ℂ).det = (y : ℂ) := by
    simp [B, upperM, diagM, Matrix.det_fin_two]
  have hdet : ((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det =
      (y : ℂ) * G.det := by
    change ((B : Matrix (Fin 2) (Fin 2) ℂ) * G).det = _
    rw [Matrix.det_mul, hdetB]
  have h10 : ((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = G 1 0 := by
    simp [B, G, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = G 1 1 := by
    simp [B, G, upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two]
  have hratio :
      ‖((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
          (‖((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
            ‖((B * g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) =
        ‖(y : ℂ)‖ * r := by
    rw [hdet, norm_mul, h10, h11]
    dsimp [r]
    ring
  have hfactor :
      ((‖(y : ℂ)‖ * r : ℝ) : ℂ) ^ (1 + 2 * s) =
        ((‖(y : ℂ)‖ : ℝ) : ℂ) ^ (1 + 2 * s) * (r : ℂ) ^ (1 + 2 * s) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (le_of_lt (div_pos (norm_pos_iff.mpr g.det_ne_zero) hden)) _
  have hnormpow :
      ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) =
        ((‖(y : ℂ)‖ : ℝ) : ℂ) ^ (1 + 2 * s) := by
    rw [Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    rw [show (1 + 2 * s : ℂ) = (2 : ℂ) * ((1 : ℂ) / 2 + s) by ring]
    symm
    simpa using Complex.cpow_mul_ofReal_nonneg (norm_nonneg _) 2 ((1 : ℂ) / 2 + s)
  unfold sphericalC
  rw [hratio, hfactor, hnormpow]

theorem sphericalC_isSection (s : ℂ) :
    ∃ f : PGL2 ℂ → ℂ, IsSectionC s f ∧ ∀ g : GL (Fin 2) ℂ, f (QuotientGroup.mk g) = sphericalC s g := by
  classical
  let f : PGL2 ℂ → ℂ := Quotient.lift (sphericalC s) (by
    intro g h hgh
    have hcent : g⁻¹ * h ∈ Subgroup.center (GL (Fin 2) ℂ) :=
      QuotientGroup.leftRel_apply.mp hgh
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcent
    obtain ⟨c, hc⟩ := hcent
    have hmat : h = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g := by
      calc
        h = g * (g⁻¹ * h) := by group
        _ = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by rw [hc]
        _ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g :=
          (Matrix.GeneralLinearGroup.scalar_commute c g).symm
    calc
      sphericalC s g =
          sphericalC s (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) :=
        (sphericalC_scalar_invariant s c g).symm
      _ = sphericalC s h := by rw [hmat])
  refine ⟨f, ?_, ?_⟩
  · intro x y g
    obtain ⟨G, hG⟩ := QuotientGroup.mk_surjective g
    have hquot : QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ y) * g =
        QuotientGroup.mk (upperM ℂ x * diagM ℂ y * G) := by
      rw [← hG]
      simp [map_mul, mul_assoc]
    have hg : f g = sphericalC s G := by
      rw [← hG]
      rfl
    calc
      f (QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ y) * g) =
          f (QuotientGroup.mk (upperM ℂ x * diagM ℂ y * G)) := by rw [hquot]
      _ = sphericalC s (upperM ℂ x * diagM ℂ y * G) := rfl
      _ = ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) *
          sphericalC s G := sphericalC_leftBorel s x y G
      _ = ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) * f g := by rw [hg]
  · intro G
    rfl

end ArtinPrimitiveRoots.A1.Theta
