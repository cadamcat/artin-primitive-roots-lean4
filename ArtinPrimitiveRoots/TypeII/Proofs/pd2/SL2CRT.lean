import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Squarefree
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

noncomputable section

abbrev ModulusPrimes (m : ℕ) := {p : ℕ // p ∈ m.primeFactors}

private lemma modulusPrimes_product (m : ℕ) (hm : Squarefree m) :
    (∏ p : ModulusPrimes m, p.1) = m := by
  change (∏ p ∈ m.primeFactors.attach, p.1) = m
  exact (Finset.prod_attach (s := m.primeFactors) (f := fun n : ℕ => n)).trans
    (Nat.prod_primeFactors_of_squarefree hm)

private lemma modulusPrimes_coprime (m : ℕ) :
    Pairwise (fun p q : ModulusPrimes m => Nat.Coprime p.1 q.1) := by
  intro p q hpq
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.2)
    (Nat.prime_of_mem_primeFactors q.2)).2 (fun h => hpq (Subtype.ext h))

def squarefreeZModCRT (m : ℕ) (hm : Squarefree m) :
    ZMod m ≃+* ((p : ModulusPrimes m) → ZMod p.1) :=
  (ZMod.ringEquivCongr (modulusPrimes_product m hm).symm).trans
    (ZMod.prodEquivPi (fun p : ModulusPrimes m => p.1) (modulusPrimes_coprime m))

lemma squarefreeZModCRT_apply (m : ℕ) (hm : Squarefree m) (x : ZMod m) (p : ModulusPrimes m) :
    squarefreeZModCRT m hm x p = ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2) (ZMod p.1) x := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun p : ModulusPrimes m => ZMod p.1) p).comp (squarefreeZModCRT m hm).toRingHom)
    (ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2) (ZMod p.1))) x

private def matrixPiEquiv {ι : Type*} {R : Type*} [CommRing R]
    {A : ι → Type*} [∀ i, CommRing (A i)] (e : R ≃+* ((i : ι) → A i)) :
    Matrix (Fin 2) (Fin 2) R ≃ ((i : ι) → Matrix (Fin 2) (Fin 2) (A i)) where
  toFun g i a b := e (g a b) i
  invFun g a b := e.symm (fun i => g i a b)
  left_inv g := by
    funext a b
    exact e.symm_apply_apply _
  right_inv g := by
    funext i a b
    exact congrFun (e.apply_symm_apply (fun i => g i a b)) i

private lemma matrixPiEquiv_det {ι : Type*} {R : Type*} [CommRing R]
    {A : ι → Type*} [∀ i, CommRing (A i)] (e : R ≃+* ((i : ι) → A i))
    (g : Matrix (Fin 2) (Fin 2) R) (i : ι) :
    e g.det i = (matrixPiEquiv e g i).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  change e (g 0 0 * g 1 1 - g 0 1 * g 1 0) i =
    e (g 0 0) i * e (g 1 1) i - e (g 0 1) i * e (g 1 0) i
  simp only [map_sub, map_mul, Pi.sub_apply, Pi.mul_apply]

private lemma matrixPiEquiv_det_one {ι : Type*} {R : Type*} [CommRing R]
    {A : ι → Type*} [∀ i, CommRing (A i)] (e : R ≃+* ((i : ι) → A i))
    (g : Matrix (Fin 2) (Fin 2) R) :
    g.det = 1 ↔ ∀ i, (matrixPiEquiv e g i).det = 1 := by
  constructor
  · intro h i
    rw [← matrixPiEquiv_det, h, map_one]
    rfl
  · intro h
    apply e.injective
    funext i
    rw [matrixPiEquiv_det, h i, map_one]
    rfl

private def matrixPiConditionEquiv {ι : Type*} {R : Type*} [CommRing R]
    {A : ι → Type*} [∀ i, CommRing (A i)] (e : R ≃+* ((i : ι) → A i))
    (P : (i : ι) → Matrix (Fin 2) (Fin 2) (A i) → Prop) :
    {g : Matrix (Fin 2) (Fin 2) R // g.det = 1 ∧ ∀ i, P i (matrixPiEquiv e g i)} ≃
      ((i : ι) → {g : Matrix (Fin 2) (Fin 2) (A i) // g.det = 1 ∧ P i g}) where
  toFun g i := ⟨matrixPiEquiv e g.1 i, (matrixPiEquiv_det_one e g.1).1 g.2.1 i, g.2.2 i⟩
  invFun g :=
    ⟨(matrixPiEquiv e).symm (fun i => (g i).1),
      (matrixPiEquiv_det_one e _).2 (by
        intro i
        rw [(matrixPiEquiv e).apply_symm_apply]
        exact (g i).2.1),
      by
        intro i
        rw [(matrixPiEquiv e).apply_symm_apply]
        exact (g i).2.2⟩
  left_inv g := by
    apply Subtype.ext
    exact (matrixPiEquiv e).symm_apply_apply g.1
  right_inv g := by
    funext i
    apply Subtype.ext
    exact congrFun ((matrixPiEquiv e).apply_symm_apply (fun i => (g i).1)) i

lemma sl2_squarefree_crt_card (m : ℕ) (hm : Squarefree m) (hpos : 0 < m)
    (P : (p : ModulusPrimes m) → Matrix (Fin 2) (Fin 2) (ZMod p.1) → Prop) :
    Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod m) // g.det = 1 ∧
      ∀ p : ModulusPrimes m,
        P p (fun a b => ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2) (ZMod p.1) (g a b))} =
      ∏ p : ModulusPrimes m,
        Nat.card {g : Matrix (Fin 2) (Fin 2) (ZMod p.1) // g.det = 1 ∧ P p g} := by
  classical
  letI : NeZero m := ⟨hpos.ne'⟩
  letI : ∀ p : ModulusPrimes m, NeZero p.1 := fun p =>
    ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  let e := squarefreeZModCRT m hm
  have heval (g : Matrix (Fin 2) (Fin 2) (ZMod m)) (p : ModulusPrimes m) :
      matrixPiEquiv e g p =
        (fun a b => ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2) (ZMod p.1) (g a b)) := by
    funext a b
    exact squarefreeZModCRT_apply m hm (g a b) p
  have he := matrixPiConditionEquiv e P
  have hcard := Nat.card_congr he
  simp_rw [heval] at hcard
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [Nat.card_eq_fintype_card]

end
end ArtinPrimitiveRoots.TypeII.PD
