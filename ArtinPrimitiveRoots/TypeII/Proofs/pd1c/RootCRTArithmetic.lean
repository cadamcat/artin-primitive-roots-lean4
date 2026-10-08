import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.RootGraph

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd1c_rootShared (u S : ℕ) : ℕ := ∏ p ∈ S.primeFactors.filter (fun p => p ∣ u), p
noncomputable def pd1c_rootUnshared (u S : ℕ) : ℕ := ∏ p ∈ S.primeFactors.filter (fun p => ¬p ∣ u), p

lemma pd1c_rootShared_pos (u S : ℕ) : 0 < pd1c_rootShared u S := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos

lemma pd1c_rootUnshared_pos (u S : ℕ) : 0 < pd1c_rootUnshared u S := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos

lemma pd1c_rootShared_mul_unshared (u S : ℕ) (hSq : Squarefree S) :
    pd1c_rootShared u S * pd1c_rootUnshared u S = S := by
  unfold pd1c_rootShared pd1c_rootUnshared
  rw [Finset.prod_filter_mul_prod_filter_not]
  exact Nat.prod_primeFactors_of_squarefree hSq

lemma pd1c_rootUnshared_coprime (u S : ℕ) : Nat.Coprime u (pd1c_rootUnshared u S) := by
  apply Nat.Coprime.prod_right
  intro p hp
  have hm := Finset.mem_filter.mp hp
  exact ((Nat.mem_primeFactors.mp hm.1).1.coprime_iff_not_dvd.mpr hm.2).symm

lemma pd1c_rootShared_dvd (u S : ℕ) : pd1c_rootShared u S ∣ u := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have hpp := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1
    have hqp := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hq).1).1
    apply Nat.coprime_iff_isRelPrime.mp
    apply hpp.coprime_iff_not_dvd.mpr
    intro hd
    rcases (Nat.dvd_prime hqp).mp hd with h1 | heq
    · exact hpp.ne_one h1
    · exact hpq heq
  · intro p hp
    exact (Finset.mem_filter.mp hp).2

lemma pd1c_rootParts_coprime (u S : ℕ) :
    Nat.Coprime (pd1c_rootShared u S) (pd1c_rootUnshared u S) :=
  (pd1c_rootUnshared_coprime u S).of_dvd_left (pd1c_rootShared_dvd u S)

lemma pd1c_rootCRT_coprime (u S : ℕ) :
    Nat.Coprime (u * pd1c_rootShared u S) (pd1c_rootUnshared u S) :=
  (pd1c_rootUnshared_coprime u S).mul_left (pd1c_rootParts_coprime u S)

lemma pd1c_root_inverse_rhs_unit (u S : ℕ) (hu : 0 < u) (d : ℤ) :
    IsUnit ((((u : ℤ) * d - 1 : ℤ) : ZMod (u * pd1c_rootShared u S))) := by
  let M := u * pd1c_rootShared u S
  have hMpos : 0 < M := mul_pos hu (pd1c_rootShared_pos u S)
  letI : NeZero M := ⟨hMpos.ne'⟩
  apply (ZMod.coe_int_isUnit_iff_isCoprime _ M).mpr
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  have hAbs : Nat.Coprime ((u : ℤ) * d - 1).natAbs M := by
    by_contra hnot
    obtain ⟨p, hp, hpa, hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpu : p ∣ u := by
      rcases hp.dvd_mul.mp hpM with hpu | hps
      · exact hpu
      · exact hps.trans (pd1c_rootShared_dvd u S)
    have hpU : (p : ℤ) ∣ (u : ℤ) := by exact_mod_cast hpu
    have hpA : (p : ℤ) ∣ (u : ℤ) * d - 1 := Int.natCast_dvd.mpr hpa
    have hpOne : (p : ℤ) ∣ 1 := by
      convert dvd_sub (dvd_mul_of_dvd_left hpU d) hpA using 1 <;> ring
    have hNat : p ∣ 1 := by exact_mod_cast hpOne
    exact hp.ne_one (Nat.dvd_one.mp hNat)
  simpa only [Int.gcd_def, Int.natAbs_natCast] using hAbs.symm.gcd_eq_one

lemma pd1c_rootShared_dvd_modulus (u S : ℕ) (hSq : Squarefree S) : pd1c_rootShared u S ∣ S :=
  ⟨pd1c_rootUnshared u S, (pd1c_rootShared_mul_unshared u S hSq).symm⟩

lemma pd1c_root_shared_entry_unit (u S : ℕ) (hS : 0 < S) (hSq : Squarefree S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hdet : Matrix.det g₀ = 1)
    (hu₀ : (u : ZMod S) = g₀ 0 0) :
    IsUnit (((g₀ 0 1).val : ℕ) : ZMod (pd1c_rootShared u S)) := by
  letI : NeZero S := ⟨hS.ne'⟩
  let D := pd1c_rootShared u S
  let f : ZMod S →+* ZMod D := ZMod.castHom (pd1c_rootShared_dvd_modulus u S hSq) (ZMod D)
  have huD : (u : ZMod D) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (pd1c_rootShared_dvd u S)
  have hzero : f (g₀ 0 0) = 0 := by rw [← hu₀, map_natCast]; exact huD
  have hdet' : g₀ 0 0 * g₀ 1 1 - g₀ 0 1 * g₀ 1 0 = 1 := by simpa only [Matrix.det_fin_two] using hdet
  have hf := congrArg f hdet'
  simp only [map_sub, map_mul, map_one, hzero, zero_mul, zero_sub] at hf
  have hc : f (g₀ 0 1) * (-f (g₀ 1 0)) = 1 := by rw [mul_neg]; exact hf
  have hunit : IsUnit (f (g₀ 0 1)) := ⟨Units.mkOfMulEqOne _ _ hc, rfl⟩
  have hcast : (((g₀ 0 1).val : ℕ) : ZMod D) = f (g₀ 0 1) := by
    rw [← map_natCast f (g₀ 0 1).val, ZMod.natCast_zmod_val]
  rw [hcast]
  exact hunit

lemma pd1c_root_totientShared_mul (u S : ℕ) :
    Nat.totient (u * pd1c_rootShared u S) = pd1c_rootShared u S * Nat.totient u := by
  have hprod : ∀ t : Finset ℕ, (∀ p ∈ t, p.Prime ∧ p ∣ u) →
      Nat.totient (u * ∏ p ∈ t, p) = (∏ p ∈ t, p) * Nat.totient u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hp ih =>
      intro hPrime
      have hpp := (hPrime p (Finset.mem_insert_self _ _)).1
      have hpd := (hPrime p (Finset.mem_insert_self _ _)).2
      have hpd' : p ∣ u * ∏ q ∈ t, q := dvd_mul_of_dvd_left hpd _
      rw [Finset.prod_insert hp]
      calc
        _ = Nat.totient (p * (u * ∏ q ∈ t, q)) := by congr 1; ring
        _ = p * Nat.totient (u * ∏ q ∈ t, q) := Nat.totient_mul_of_prime_of_dvd hpp hpd'
        _ = _ := by rw [ih (fun q hq => hPrime q (Finset.mem_insert_of_mem hq))]; ring
  exact hprod _ (fun p hp => ⟨(Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)

end ArtinPrimitiveRoots.TypeII.PD
