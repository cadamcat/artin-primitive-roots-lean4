import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootArithmetic

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open scoped MatrixGroups
set_option maxHeartbeats 1000000

lemma pd1c_sl2Card_pos (S : ℕ) (hS : 0 < S) : 0 < sl2Card S hS := by
  letI : NeZero S := ⟨hS.ne'⟩
  unfold sl2Card
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨1, by simp⟩⟩

lemma pd1c_sl2Card_one (hS : 0 < (1 : ℕ)) : sl2Card 1 hS = 1 := by
  unfold sl2Card
  letI : Unique {g : Matrix (Fin 2) (Fin 2) (ZMod 1) // Matrix.det g = 1} :=
    { default := ⟨1, by simp⟩
      uniq := fun g => Subtype.ext (Subsingleton.elim _ _) }
  exact Fintype.card_unique

lemma pd1c_sl2Card_prime (p : ℕ) (hp : p.Prime) : sl2Card p hp.pos = p * (p ^ 2 - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let f : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ := Matrix.GeneralLinearGroup.det
  have hmul := f.ker.card_mul_index
  have hidx : f.ker.index = Nat.card (ZMod p)ˣ := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr Matrix.GeneralLinearGroup.det_surjective]
    exact Nat.card_congr (Equiv.Set.univ _)
  have hker : Nat.card f.ker = sl2Card p hp.pos := by
    rw [← Nat.card_congr (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 2) (R := ZMod p)).toEquiv]
    exact Nat.card_eq_fintype_card
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
    simpa [Fin.prod_univ_two, ZMod.card] using (Matrix.card_GL_field (𝔽 := ZMod p) 2)
  have hu : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  rw [hidx, hker, hu, hgl] at hmul
  have hpoly : p ^ 2 - p = p * (p - 1) := by
    simp only [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [hpoly] at hmul
  have hpos : 0 < p - 1 := by have h := hp.two_le; omega
  apply Nat.mul_right_cancel hpos
  nlinarith only [hmul]

def pd1c_sl2RingEquiv {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃ Matrix.SpecialLinearGroup (Fin 2) T where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

def pd1c_sl2ProdEquiv (R T : Type*) [CommRing R] [CommRing T] :
    Matrix.SpecialLinearGroup (Fin 2) (R × T) ≃
      Matrix.SpecialLinearGroup (Fin 2) R × Matrix.SpecialLinearGroup (Fin 2) T where
  toFun g := (Matrix.SpecialLinearGroup.map (RingHom.fst R T) g,
    Matrix.SpecialLinearGroup.map (RingHom.snd R T) g)
  invFun g := ⟨fun i j => (g.1.val i j, g.2.val i j), by
    apply Prod.ext
    · have h := (RingHom.fst R T).map_det (fun i j => (g.1.val i j, g.2.val i j))
      exact h.trans g.1.2
    · have h := (RingHom.snd R T).map_det (fun i j => (g.1.val i j, g.2.val i j))
      exact h.trans g.2.2⟩
  left_inv g := by
    apply Subtype.ext
    ext i j <;> rfl
  right_inv g := by
    apply Prod.ext
    · apply Subtype.ext; ext i j; rfl
    · apply Subtype.ext; ext i j; rfl

lemma pd1c_sl2Card_eq_natCard (S : ℕ) (hS : 0 < S) :
    sl2Card S hS = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) := by
  letI : NeZero S := ⟨hS.ne'⟩
  exact Nat.card_eq_fintype_card.symm

lemma pd1c_sl2NatCard_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (m * n))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod m)) *
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) := by
  let e := (pd1c_sl2RingEquiv (ZMod.chineseRemainder hcop)).trans
    (pd1c_sl2ProdEquiv (ZMod m) (ZMod n))
  rw [Nat.card_congr e, Nat.card_prod]

lemma pd1c_sl2Card_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    sl2Card (m * n) (mul_pos hm hn) = sl2Card m hm * sl2Card n hn := by
  simp only [pd1c_sl2Card_eq_natCard]
  exact pd1c_sl2NatCard_mul m n hm hn hcop

lemma pd1c_sl2Card_squarefree_factors (S : ℕ) (hS : 0 < S) (hSq : Squarefree S) :
    sl2Card S hS = ∏ p ∈ S.primeFactors, p * (p ^ 2 - 1) := by
  have hprod : ∀ t : Finset ℕ, (∀ p ∈ t, p.Prime) →
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ p ∈ t, p))) =
        ∏ p ∈ t, p * (p ^ 2 - 1) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro hPrime
      simpa only [Finset.prod_empty] using (pd1c_sl2Card_eq_natCard 1 (by norm_num)).symm.trans (pd1c_sl2Card_one (by norm_num))
    | @insert p t hp ih =>
      intro hPrime
      have hpp : p.Prime := hPrime p (Finset.mem_insert_self _ _)
      have htPrime : ∀ q ∈ t, q.Prime := fun q hq => hPrime q (Finset.mem_insert_of_mem hq)
      have htpos : 0 < ∏ q ∈ t, q := Finset.prod_pos (fun q hq => (htPrime q hq).pos)
      have hcop : Nat.Coprime p (∏ q ∈ t, q) := Nat.Coprime.prod_right fun q hq => by
        apply hpp.coprime_iff_not_dvd.mpr
        intro hd
        rcases (Nat.dvd_prime (htPrime q hq)).mp hd with heq | heq
        · exact hpp.ne_one heq
        · subst q
          exact hp hq
      rw [Finset.prod_insert hp, pd1c_sl2NatCard_mul p _ hpp.pos htpos hcop,
        ← pd1c_sl2Card_eq_natCard p hpp.pos, pd1c_sl2Card_prime p hpp,
        ih htPrime, Finset.prod_insert hp]
  rw [pd1c_sl2Card_eq_natCard]
  calc
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ p ∈ S.primeFactors, p))) :=
      congrArg (fun n : ℕ => Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod n))) (Nat.prod_primeFactors_of_squarefree hSq).symm
    _ = _ := hprod S.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)

lemma pd1c_sl2Card_squarefree_real (S : ℕ) (hS : 0 < S) (hSq : Squarefree S) :
    (sl2Card S hS : ℝ) = (S : ℝ) ^ 3 *
      ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
  rw [pd1c_sl2Card_squarefree_factors S hS hSq]
  have hSprod : (S : ℝ) = ∏ p ∈ S.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree hSq).symm
  rw [hSprod, Nat.cast_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hPrime := (Nat.mem_primeFactors.mp hp).1
  have h2 : 1 ≤ p ^ 2 := by have h := hPrime.two_le; nlinarith
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hPrime.ne_zero
  rw [Nat.cast_mul, Nat.cast_sub h2, Nat.cast_pow, Nat.cast_one]
  field_simp

end ArtinPrimitiveRoots.TypeII.PD
