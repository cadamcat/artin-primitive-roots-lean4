import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical
open ArtinPrimitiveRoots.TypeII
set_option autoImplicit false

lemma pd7d_rough_coprime (n k : ℕ) (W : ℝ) (hk : 0 < k)
    (hkle : (k : ℝ) ≤ W) (hn : roughAbove n W) : Nat.Coprime n k := by
  by_contra hc
  have hg : Nat.gcd n k ≠ 1 := by
    intro hg
    exact hc hg
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left n k)
  have hpk : p ∣ k := hpg.trans (Nat.gcd_dvd_right n k)
  have hpLe : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_dvd hk hpk
  exact not_lt_of_ge (hpLe.trans hkle) (hn p hp hpn)

lemma pd7d_rough_isUnit (n k : ℕ) (W : ℝ) (hk : 0 < k)
    (hkle : (k : ℝ) ≤ W) (hn : roughAbove n W) : IsUnit (n : ZMod k) :=
  (ZMod.isUnit_iff_coprime n k).2 (pd7d_rough_coprime n k W hk hkle hn)

lemma pd7d_prime_isUnit (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hpk : (k : ℝ) < (p : ℝ)) : IsUnit (p : ZMod k) := by
  apply (ZMod.isUnit_iff_coprime p k).2
  apply hp.coprime_iff_not_dvd.2
  intro hdiv
  have hh : (p : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_dvd hk hdiv
  exact not_lt_of_ge hh hpk

lemma pd7d_marked_tuple_isUnit (x : ℝ) (K : ℕ) (a : Fin K → ℝ)
    (tb : Fin K → ℕ) (k : ℕ) (hk : 0 < k) (htb : IsMarkedPrimeTuple x K a tb)
    (hsmall : ∀ i : Fin K, (k : ℝ) < Real.exp (Real.rpow (Real.log x) (a i))) :
    IsUnit (tupleProduct tb : ZMod k) := by
  apply (ZMod.isUnit_iff_coprime (tupleProduct tb) k).2
  apply Nat.Coprime.prod_left
  intro i hi
  have hpB := (Finset.mem_filter.mp (htb i)).2
  exact (ZMod.isUnit_iff_coprime (tb i) k).1
    (pd7d_prime_isUnit (tb i) k hpB.1 hk ((hsmall i).trans_le hpB.2.1))

end ArtinPrimitiveRoots.TypeII.PD
