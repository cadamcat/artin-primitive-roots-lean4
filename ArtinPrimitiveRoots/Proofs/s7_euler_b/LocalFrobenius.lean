import ArtinPrimitiveRoots.Ext.SplittingInputs
import ArtinPrimitiveRoots.Hecke.Defs
import ArtinPrimitiveRoots.Hecke.Elementary
import ArtinPrimitiveRoots.Splitting.Proofs.S7_EULER.prod_one_sub_character
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Pointwise IsMulCommutative
noncomputable section

namespace ArtinPrimitiveRoots.Splitting

open ClassFieldTheory ArtinPrimitiveRoots.Hecke ArtinPrimitiveRoots.Ext.SplittingInputs

/-- A height-one prime outside the finite part of the modulus is coprime to it. -/
theorem rayPrime_coprime_of_not_mem_support {B : Type*} [Field B] [NumberField B]
    (m : RayClassModulus B) (v : HeightOneSpectrum (𝓞 B))
    (hv : v ∉ m.finitePart.support) : IsCoprimeTo m v.asIdeal := by
  refine ⟨v.ne_bot, ?_⟩
  change ∀ u : HeightOneSpectrum (𝓞 B), u ∈ m.finitePart.support →
    FractionalIdeal.count B u
      (idealUnit v.asIdeal v.ne_bot : FractionalIdeal (nonZeroDivisors (𝓞 B)) B) = 0
  intro u hu
  have huv : u ≠ v := by
    intro huv
    exact hv (huv ▸ hu)
  simpa [idealUnit] using (FractionalIdeal.count_maximal_coprime B u huv.symm)

/-- The residue action of an arithmetic Frobenius is finite-field Frobenius, and an unramified
prime has trivial inertia, so the global Frobenius has the residue degree as its order. -/
theorem orderOf_arithFrob_eq_inertiaDeg {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T] [IsAbelianGalois B T]
    {v : HeightOneSpectrum (𝓞 B)} {P : Ideal (𝓞 T)}
    (hP : P ∈ v.asIdeal.primesOver (𝓞 T))
    (hidx : v.asIdeal.ramificationIdxIn (𝓞 T) = 1)
    {σ : T ≃ₐ[B] T} (hσ : IsArithFrobAt (𝓞 B) σ P) :
    orderOf σ = P.inertiaDeg (𝓞 B) := by
  classical
  let G := T ≃ₐ[B] T
  letI : P.IsPrime := hP.1
  letI : P.LiesOver v.asIdeal := hP.2
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  letI : P.IsMaximal := hP.1.isMaximal hPbot
  let baseP := P.under (𝓞 B)
  have hbaseP : baseP = v.asIdeal := Ideal.LiesOver.over
  letI : baseP.IsMaximal := hbaseP ▸ v.isPrime.isMaximal v.ne_bot
  letI : Field (𝓞 B ⧸ baseP) := Ideal.Quotient.field baseP
  letI : Field (𝓞 T ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 B ⧸ baseP) := Fintype.ofFinite _
  let ρ : MulAction.stabilizer G P →*
      ((𝓞 T ⧸ P) ≃ₐ[𝓞 B ⧸ baseP] (𝓞 T ⧸ P)) :=
    Ideal.Quotient.stabilizerHom P baseP G
  let g : MulAction.stabilizer G P := ⟨σ, hσ.mem_stabilizer⟩
  have hres : ρ g =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 B ⧸ baseP) (𝓞 T ⧸ P) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      ← @Nat.card_eq_fintype_card _ (Fintype.ofFinite (𝓞 B ⧸ baseP))]
    simpa [g, MulAction.subgroup_smul_def, MulSemiringAction.toAlgHom_apply] using
      hσ.mk_apply x
  have hresOrder : orderOf (ρ g) = P.inertiaDeg (𝓞 B) := by
    rw [hres, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      ← Ideal.inertiaDeg_eq_of_isMaximal baseP P]
  have hIcard : Nat.card (P.inertia (MulAction.stabilizer G P)) = 1 := by
    calc
      Nat.card (P.inertia (MulAction.stabilizer G P)) =
          Nat.card ((P.inertia G).subgroupOf (MulAction.stabilizer G P)) := by
        simp [AddSubgroup.subgroupOf_inertia]
      _ = Nat.card (P.inertia G) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv
      _ = v.asIdeal.ramificationIdxIn (𝓞 T) :=
        Ideal.card_inertia_eq_ramificationIdxIn (G := G) v.asIdeal P
      _ = 1 := hidx
  have hker : ρ.ker = ⊥ := by
    change (Ideal.Quotient.stabilizerHom P baseP G).ker = ⊥
    rw [Ideal.Quotient.ker_stabilizerHom, Subgroup.eq_bot_iff_card]
    exact hIcard
  have hρinj : Function.Injective ρ := (ρ.ker_eq_bot_iff).mp hker
  calc
    orderOf σ = orderOf g := by
      simpa [g] using (Subgroup.orderOf_coe g)
    _ = orderOf (ρ g) := by
      exact (orderOf_injective ρ hρinj g).symm
    _ = P.inertiaDeg (𝓞 B) := hresOrder

/-- The arithmetic Frobenius supplied by the ray-class Artin map has order equal to the
residue degree at every prime outside the modulus. -/
theorem rayArtin_orderOf_eq_inertiaDegIn {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T] [IsAbelianGalois B T]
    (m : RayClassModulus B) (Art : RayClassGroup m →* (T ≃ₐ[B] T))
    (hFrob : FrobeniusNormalizedArtinMap m Art)
    (v : HeightOneSpectrum (𝓞 B)) (hv : v ∉ m.finitePart.support)
    (P : Ideal (𝓞 T)) (hP : P ∈ v.asIdeal.primesOver (𝓞 T)) :
    orderOf (Art (rayClass m v.asIdeal (rayPrime_coprime_of_not_mem_support m v hv))) =
      v.asIdeal.inertiaDegIn (𝓞 T) := by
  classical
  letI : Algebra (𝓞 B) (𝓞 T) := inferInstance
  letI : IsScalarTower (𝓞 B) (𝓞 T) T := inferInstance
  letI : P.IsPrime := hP.1
  letI : P.LiesOver v.asIdeal := hP.2
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  obtain ⟨σ, hArt, hσ⟩ :=
    hFrob.2 v.asIdeal v.isPrime (rayPrime_coprime_of_not_mem_support m v hv)
      P hP.1 hP.2
  have hArith : IsArithFrobAt (𝓞 B) σ P := by
    change ∀ x : 𝓞 T,
      (σ • x) - x ^ Nat.card (𝓞 B ⧸ P.under (𝓞 B)) ∈ P
    intro x
    obtain ⟨y, hy, hyP⟩ := hσ x
    have hxy : σ • x = y := by
      apply NumberField.RingOfIntegers.ext
      change σ (x : T) = (y : T)
      exact hy.symm
    have hPunder : P.under (𝓞 B) = v.asIdeal := hP.2.over.symm
    have hcard : Nat.card (𝓞 B ⧸ P.under (𝓞 B)) = Ideal.absNorm v.asIdeal := by
      rw [hPunder, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hxy, hcard]
    exact hyP
  have he : v.asIdeal.ramificationIdxIn (𝓞 T) = 1 :=
    hFrob.1 v.asIdeal v.isPrime (rayPrime_coprime_of_not_mem_support m v hv)
  have horder : orderOf σ = P.inertiaDeg (𝓞 B) :=
    orderOf_arithFrob_eq_inertiaDeg hP he hArith
  have hdeg : P.inertiaDeg (𝓞 B) = v.asIdeal.inertiaDegIn (𝓞 T) := by
    symm
    exact Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P (T ≃ₐ[B] T)
  calc
    orderOf (Art (rayClass m v.asIdeal (rayPrime_coprime_of_not_mem_support m v hv))) =
        orderOf σ := by rw [hArt]
    _ = P.inertiaDeg (𝓞 B) := horder
    _ = v.asIdeal.inertiaDegIn (𝓞 T) := hdeg

/-- For a positive integer norm, a natural power of the norm commutes with complex powers. -/
private theorem natCastPow_cpow {n d : ℕ} {s : ℂ} :
    (((n ^ d : ℕ) : ℂ) ^ (-s)) = ((n : ℂ) ^ (-s)) ^ d := by
  calc
    (((n ^ d : ℕ) : ℂ) ^ (-s)) =
        (n : ℂ) ^ ((d : ℂ) * (-s)) := by
          rw [Nat.cast_pow]
          exact (Complex.natCast_cpow_natCast_mul n d (-s)).symm
    _ = (n : ℂ) ^ ((-s) * (d : ℂ)) := by congr 1; ring
    _ = ((n : ℂ) ^ (-s)) ^ d := Complex.cpow_mul_nat (n : ℂ) (-s) d

/-- At a prime outside the ray modulus, the product of the character Euler factors is the
product of the upstairs prime Euler factors. -/
theorem rayCharacterFactor_eq_primeFiberFactor {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T] [IsAbelianGalois B T]
    (m : RayClassModulus B) (Art : RayClassGroup m →* (T ≃ₐ[B] T))
    (hFrob : FrobeniusNormalizedArtinMap m Art)
    (v : HeightOneSpectrum (𝓞 B)) (hv : v ∉ m.finitePart.support) (s : ℂ) :
    (∏ χ : (T ≃ₐ[B] T) →* ℂˣ,
      (1 - charValue (χ.comp Art) v.asIdeal *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) =
    (∏ P : {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)},
      (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹) := by
  classical
  let G := T ≃ₐ[B] T
  let cop := rayPrime_coprime_of_not_mem_support m v hv
  let g : G := Art (rayClass m v.asIdeal cop)
  let z : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)
  let F := {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)}
  letI : Fintype F := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 T)).fintype
  have hvalue (χ : G →* ℂˣ) : charValue (χ.comp Art) v.asIdeal = (χ g : ℂ) := by
    simp [charValue, cop, g]
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    v.asIdeal.nonempty_primesOver (S := 𝓞 T)
  letI : P.IsPrime := hPprime
  letI : P.LiesOver v.asIdeal := hPover
  have horder : orderOf g = v.asIdeal.inertiaDegIn (𝓞 T) := by
    exact rayArtin_orderOf_eq_inertiaDegIn m Art hFrob v hv P ⟨hPprime, hPover⟩
  have he : v.asIdeal.ramificationIdxIn (𝓞 T) = 1 :=
    hFrob.1 v.asIdeal v.isPrime cop
  have hdeg (Q : F) : Q.1.inertiaDeg (𝓞 B) = orderOf g := by
    have hQdeg : Q.1.inertiaDeg (𝓞 B) = v.asIdeal.inertiaDegIn (𝓞 T) := by
      symm
      exact Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q.1 G
    exact hQdeg.trans horder.symm
  have hnorm (Q : F) : Ideal.absNorm Q.1 =
      Ideal.absNorm v.asIdeal ^ orderOf g := by
    letI : Q.1.IsPrime := Q.2.1
    letI : Q.1.LiesOver v.asIdeal := Q.2.2
    calc
      Ideal.absNorm Q.1 = Ideal.absNorm v.asIdeal ^ Q.1.inertiaDeg (𝓞 B) :=
        (Ideal.absNorm_pow_inertiaDeg v.asIdeal Q.1).symm
      _ = Ideal.absNorm v.asIdeal ^ orderOf g := by rw [hdeg Q]
  have hnormCpow (Q : F) :
      ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) = z ^ orderOf g := by
    have hcast : (Ideal.absNorm Q.1 : ℂ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ orderOf g := by
      exact_mod_cast hnorm Q
    calc
      ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s) =
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ orderOf g) ^ (-s) := by rw [hcast]
      _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^
          ((orderOf g : ℂ) * (-s)) :=
        (Complex.natCast_cpow_natCast_mul (Ideal.absNorm v.asIdeal) (orderOf g) (-s)).symm
      _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^
          ((-s) * (orderOf g : ℂ)) := by congr 1; ring
      _ = z ^ orderOf g := Complex.cpow_mul_nat _ _ _
  have hfund : (v.asIdeal.primesOver (𝓞 T)).ncard *
      (v.asIdeal.ramificationIdxIn (𝓞 T) * v.asIdeal.inertiaDegIn (𝓞 T)) = Nat.card G :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := v.asIdeal) (B := 𝓞 T) (G := G)
  have hfiberCard : Nat.card F = Nat.card G / orderOf g := by
    have hmul : Nat.card F * orderOf g = Nat.card G := by
      rw [he, ← horder] at hfund
      simpa [F, Nat.card_coe_set_eq] using hfund
    exact Nat.eq_div_of_mul_eq_right (orderOf_pos g).ne'
      (by simpa [Nat.mul_comm] using hmul)
  have hpoly :
      (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z)) =
        (1 - z ^ orderOf g) ^ (Nat.card G / orderOf g) := by
    exact prod_one_sub_character G g z
  have hfiber :
      (∏ Q : F, (1 - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s))⁻¹) =
        (1 - z ^ orderOf g)⁻¹ ^ Nat.card F := by
    simp_rw [hnormCpow]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]
  calc
    (∏ χ : G →* ℂˣ,
        (1 - charValue (χ.comp Art) v.asIdeal *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) =
        (∏ χ : G →* ℂˣ, (1 - (χ g : ℂ) * z))⁻¹ := by
      rw [Finset.prod_inv_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro χ hχ
      simp [hvalue χ, z]
    _ = (1 - z ^ orderOf g)⁻¹ ^ (Nat.card G / orderOf g) := by
      rw [hpoly, inv_pow]
    _ = (1 - z ^ orderOf g)⁻¹ ^ Nat.card F := by rw [hfiberCard]
    _ = ∏ Q : F, (1 - ((Ideal.absNorm Q.1 : ℕ) : ℂ) ^ (-s))⁻¹ := hfiber.symm
    _ = ∏ P : {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)},
          (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := rfl

/-- Prime ideals above a base height-one prime are the ideals underlying height-one primes
contracting to it. -/
noncomputable def primeFiberEquiv {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T] [IsAbelianGalois B T]
    (v : HeightOneSpectrum (𝓞 B)) :
    {w : HeightOneSpectrum (𝓞 T) // (w.under (𝓞 B)) = v} ≃
      {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)} := by
  classical
  letI : Algebra (𝓞 B) (𝓞 T) := inferInstance
  letI : IsScalarTower (𝓞 B) (𝓞 T) T := inferInstance
  refine
    { toFun := fun w => ?_
      invFun := fun P => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hwunder : (w.1.under (𝓞 B)).asIdeal = v.asIdeal :=
      congrArg HeightOneSpectrum.asIdeal w.2
    refine ⟨w.1.asIdeal, ⟨w.1.isPrime, ?_⟩⟩
    exact ⟨by simpa [HeightOneSpectrum.under_asIdeal] using hwunder.symm⟩
  · have hPbot : P.1 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1
    refine ⟨⟨P.1, P.2.1, hPbot⟩, ?_⟩
    apply HeightOneSpectrum.ext
    exact P.2.2.over.symm
  · intro w
    apply Subtype.ext
    rfl
  · intro P
    apply Subtype.ext
    rfl

theorem s7PrimesAbove_mem_iff {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T]
    (v : HeightOneSpectrum (𝓞 B)) (w : HeightOneSpectrum (𝓞 T)) :
    w ∈ s7PrimesAbove B T v ↔ w.asIdeal ∈ v.asIdeal.primesOver (𝓞 T) := by
  classical
  unfold s7PrimesAbove
  rw [Set.Finite.mem_toFinset]
  rfl

/-- The correction product over deleted upstairs primes is the product of the finite prime-fiber
products over the base support. -/
theorem s7UpstairsCorrection_eq_prod_base_fibers {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T]
    (m : RayClassModulus B) (s : ℂ) :
    s7UpstairsCorrection B T m s =
      ∏ v ∈ m.finitePart.support, ∏ w ∈ s7PrimesAbove B T v,
        (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹ := by
  classical
  let S := m.finitePart.support
  have hdisj : Set.PairwiseDisjoint (S : Set (HeightOneSpectrum (𝓞 B)))
      (fun v => s7PrimesAbove B T v) := by
    intro v hv u hu hne
    refine Finset.disjoint_left.mpr ?_
    intro w hwv hwu
    have hwv' : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 T) := by
      simpa [s7PrimesAbove] using hwv
    have hwu' : w.asIdeal ∈ u.asIdeal.primesOver (𝓞 T) := by
      simpa [s7PrimesAbove] using hwu
    have hbase : v.asIdeal = u.asIdeal :=
      hwv'.2.over.trans hwu'.2.over.symm
    exact hne (HeightOneSpectrum.ext hbase)
  unfold s7UpstairsCorrection s7BadTopPrimes
  change (∏ w ∈ S.biUnion (s7PrimesAbove B T),
      (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹) =
    ∏ v ∈ S, ∏ w ∈ s7PrimesAbove B T v,
      (1 - (Ideal.absNorm w.asIdeal : ℂ) ^ (-s))⁻¹
  exact Finset.prod_biUnion hdisj

private theorem dedekindZeta_eulerProduct (T : Type*) [Field T] [NumberField T]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun w : HeightOneSpectrum (𝓞 T) =>
      (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta T s) := by
  classical
  let m₀ : RayClassModulus T := ⟨0, ∅⟩
  let η₀ : RayClassGroup m₀ →* ℂˣ := 1
  have hL : LSeriesRay η₀ s = NumberField.dedekindZeta T s := by
    simpa [η₀, m₀] using LSeriesRay_trivial_eq_dedekindZeta (K := T) s
  have hcop (w : HeightOneSpectrum (𝓞 T)) : IsCoprimeTo m₀ w.asIdeal := by
    refine ⟨w.ne_bot, ?_⟩
    change ∀ v : HeightOneSpectrum (𝓞 T), v ∈ m₀.finitePart.support → _
    simp [m₀]
  have hvalue (w : HeightOneSpectrum (𝓞 T)) : charValue η₀ w.asIdeal = 1 := by
    simp [charValue, hcop w, η₀]
  have hEuler := LSeriesRay_eulerProduct (K := T) η₀ hs
  have hfun :
      (fun w : HeightOneSpectrum (𝓞 T) =>
        (1 - charValue η₀ w.asIdeal *
          ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) =
      fun w : HeightOneSpectrum (𝓞 T) =>
        (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
    funext w
    simp [hvalue]
  rw [hfun, hL] at hEuler
  exact hEuler

set_option maxHeartbeats 1000000 in
/-- The general abelian right-half-plane Euler factorization, with exactly the upstairs primes
deleted by the chosen ray modulus restored by the finite correction. -/
theorem upstairs_euler_product_identity {B T : Type*} [Field B] [NumberField B]
    [Field T] [NumberField T] [Algebra B T] [IsAbelianGalois B T]
    (m : RayClassModulus B) (Art : RayClassGroup m →* (T ≃ₐ[B] T))
    (hFrob : FrobeniusNormalizedArtinMap m Art) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta T s =
      s7UpstairsCorrection B T m s *
        ∏ χ : (T ≃ₐ[B] T) →* ℂˣ, LSeriesRay (χ.comp Art) s := by
  classical
  let G := T ≃ₐ[B] T
  let S := m.finitePart.support
  let π : HeightOneSpectrum (𝓞 T) → HeightOneSpectrum (𝓞 B) := fun w => w.under (𝓞 B)
  let Fiber (v : HeightOneSpectrum (𝓞 B)) := {w : HeightOneSpectrum (𝓞 T) // π w = v}
  let fTop (w : HeightOneSpectrum (𝓞 T)) : ℂ :=
    (1 - ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  let fRay (χ : G →* ℂˣ) (v : HeightOneSpectrum (𝓞 B)) : ℂ :=
    (1 - charValue (χ.comp Art) v.asIdeal *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
  let rayFactor (v : HeightOneSpectrum (𝓞 B)) : ℂ := ∏ χ : G →* ℂˣ, fRay χ v
  letI (v : HeightOneSpectrum (𝓞 B)) : v.asIdeal.IsMaximal :=
    v.isPrime.isMaximal v.ne_bot
  letI (v : HeightOneSpectrum (𝓞 B)) : Fintype (Fiber v) :=
    Fintype.ofEquiv _ (primeFiberEquiv v).symm
  let topFiber (v : HeightOneSpectrum (𝓞 B)) : ℂ :=
    ∏ w : Fiber v, fTop w.1
  let C (v : HeightOneSpectrum (𝓞 B)) : ℂ := if v ∈ S then topFiber v else 1

  have hTop : HasProd fTop (NumberField.dedekindZeta T s) := by
    simpa [fTop] using dedekindZeta_eulerProduct T hs
  have hTopFib : HasProd topFiber (NumberField.dedekindZeta T s) := by
    let e := Equiv.sigmaFiberEquiv π
    have hSigma : HasProd (fTop ∘ e) (NumberField.dedekindZeta T s) :=
      (e.hasProd_iff).mpr hTop
    refine hSigma.sigma (g := topFiber) ?_
    intro v
    simpa [e, topFiber, Fiber] using hasProd_fintype (fun w : Fiber v => fTop w.1)

  have hRay : HasProd rayFactor (∏ χ : G →* ℂˣ, LSeriesRay (χ.comp Art) s) := by
    have h := hasProd_prod (s := Finset.univ) (f := fun χ : G →* ℂˣ => fRay χ)
      (a := fun χ => LSeriesRay (χ.comp Art) s) (by
        intro χ hχ
        simpa [fRay] using LSeriesRay_eulerProduct (χ.comp Art) hs)
    simpa [rayFactor, fRay] using h

  have hCprod : HasProd C (∏ v ∈ S, topFiber v) := by
    have h : HasProd C (∏ v ∈ S, C v)
        (SummationFilter.unconditional (HeightOneSpectrum (𝓞 B))) :=
      hasProd_prod_of_ne_finset_one (s := S) (f := C)
        (L := SummationFilter.unconditional (HeightOneSpectrum (𝓞 B))) (by
          intro v hv
          simp [C, hv])
    convert h using 1
    apply Finset.prod_congr rfl
    intro v hv
    simp [C, hv]
  have hFiberCorrection (v : HeightOneSpectrum (𝓞 B)) :
      topFiber v = ∏ w ∈ s7PrimesAbove B T v, fTop w := by
    have hmem (w : HeightOneSpectrum (𝓞 T)) :
        π w = v ↔ w ∈ s7PrimesAbove B T v := by
      constructor
      · intro hw
        have hI : v.asIdeal = w.asIdeal.under (𝓞 B) := by
          simpa [π, HeightOneSpectrum.under_asIdeal] using
            (congrArg HeightOneSpectrum.asIdeal hw).symm
        have hP : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 T) := ⟨w.isPrime, ⟨hI⟩⟩
        exact (s7PrimesAbove_mem_iff v w).2 hP
      · intro hw
        have hP : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 T) :=
          (s7PrimesAbove_mem_iff v w).mp hw
        apply HeightOneSpectrum.ext
        simpa [π, HeightOneSpectrum.under_asIdeal] using hP.2.over.symm
    let e := Equiv.subtypeEquivRight hmem
    calc
      ∏ w : Fiber v, fTop w.1 =
          ∏ w : {w : HeightOneSpectrum (𝓞 T) // w ∈ s7PrimesAbove B T v}, fTop w.1 := by
        exact Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = ∏ w ∈ s7PrimesAbove B T v, fTop w := by
        rw [Finset.prod_coe_sort_eq_attach, Finset.prod_attach]
  have hCvalue : (∏ v ∈ S, topFiber v) = s7UpstairsCorrection B T m s := by
    rw [s7UpstairsCorrection_eq_prod_base_fibers]
    apply Finset.prod_congr rfl
    intro v hv
    exact hFiberCorrection v
  rw [hCvalue] at hCprod

  have hpoint (v : HeightOneSpectrum (𝓞 B)) : rayFactor v * C v = topFiber v := by
    by_cases hv : v ∈ S
    · have hnotcop : ¬ IsCoprimeTo m v.asIdeal := by
        rintro ⟨hI0, hI⟩
        have hcount := hI v hv
        have hself := FractionalIdeal.count_self B v
        have hbad : (0 : ℤ) = 1 := by
          simpa [idealUnit] using hcount.symm.trans hself
        omega
      have hzero (χ : G →* ℂˣ) : charValue (χ.comp Art) v.asIdeal = 0 := by
        simp [charValue, hnotcop]
      have hRayOne : rayFactor v = 1 := by
        simp [rayFactor, fRay, hzero]
      simp [C, hv, hRayOne]
    · have hlocal : rayFactor v = topFiber v := by
        have h := rayCharacterFactor_eq_primeFiberFactor m Art hFrob v hv s
        let e := primeFiberEquiv (B := B) (T := T) v
        have hprod : topFiber v =
            ∏ P : {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)},
              (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
          exact Fintype.prod_equiv e (fun w : Fiber v => fTop w.1)
            (fun P => (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹)
            (fun _ => by simp [e, primeFiberEquiv, fTop])
        have hlocal' : rayFactor v =
            ∏ P : {P : Ideal (𝓞 T) // P ∈ v.asIdeal.primesOver (𝓞 T)},
              (1 - ((Ideal.absNorm P.1 : ℕ) : ℂ) ^ (-s))⁻¹ := by
          simpa [rayFactor, fRay] using h
        exact hlocal'.trans hprod.symm
      simp [C, hv, hlocal]

  have hTopReindexed : HasProd (fun v : HeightOneSpectrum (𝓞 B) => rayFactor v * C v)
      (s7UpstairsCorrection B T m s *
        ∏ χ : G →* ℂˣ, LSeriesRay (χ.comp Art) s) := by
    simpa [mul_comm] using hRay.mul hCprod
  have hTarget : HasProd (fun v : HeightOneSpectrum (𝓞 B) => rayFactor v * C v)
      (NumberField.dedekindZeta T s) := by
    exact hTopFib.congr_fun hpoint
  have hEq := hTopReindexed.unique hTarget
  calc
    NumberField.dedekindZeta T s =
        s7UpstairsCorrection B T m s *
          ∏ χ : G →* ℂˣ, LSeriesRay (χ.comp Art) s := by
      simpa [mul_comm] using hEq.symm

end ArtinPrimitiveRoots.Splitting
end
