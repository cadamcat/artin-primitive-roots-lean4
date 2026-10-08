import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootFourier
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootCardinality

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_rootGraph (u S : ℕ) [NeZero (u * S)]
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) : Finset (ZMod (u * S) × ZMod (u * S)) :=
  Finset.univ.filter fun z =>
    (z.1.val : ZMod S) = g₀ 0 1 ∧ (z.2.val : ZMod S) = g₀ 1 0 ∧
      z.1 * z.2 = (u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1

lemma pd2a_completion_residue_iff (u v S : ℕ) (hu : 0 < u) (c d₀ : ℤ) :
    (∃ d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧ (d : ZMod S) = (d₀ : ZMod S)) ↔
      ((c * (v : ℤ) : ℤ) : ZMod (u * S)) = (((u : ℤ) * d₀ - 1 : ℤ) : ZMod (u * S)) := by
  constructor
  · rintro ⟨d, hdet, hd⟩
    exact (pd2a_root_det_congruence u v S hu c d d₀ hdet).mp hd
  · intro hcong
    have hdiv : ((u * S : ℕ) : ℤ) ∣ (u : ℤ) * d₀ - 1 - c * (v : ℤ) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcong
    have hU : (u : ℤ) ∣ (u : ℤ) * d₀ - 1 - c * (v : ℤ) :=
      (show (u : ℤ) ∣ ((u * S : ℕ) : ℤ) by exact_mod_cast dvd_mul_right u S).trans hdiv
    have hU' : (u : ℤ) ∣ 1 + c * (v : ℤ) := by
      convert dvd_sub (dvd_mul_right (u : ℤ) d₀) hU using 1 <;> ring
    obtain ⟨d, hd⟩ := hU'
    have hdet : (u : ℤ) * d - (v : ℤ) * c = 1 := by nlinarith [hd]
    exact ⟨d, hdet, (pd2a_root_det_congruence u v S hu c d d₀ hdet).mpr hcong⟩

lemma pd2a_det_one_coprime (u v : ℕ) (c d : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) : Nat.Coprime u v := by
  have hU : (Nat.gcd u v : ℤ) ∣ (u : ℤ) := by exact_mod_cast Nat.gcd_dvd_left u v
  have hV : (Nat.gcd u v : ℤ) ∣ (v : ℤ) := by exact_mod_cast Nat.gcd_dvd_right u v
  have h1 : (Nat.gcd u v : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_left hU _) (dvd_mul_of_dvd_left hV _)
  have hn : Nat.gcd u v ∣ 1 := by exact_mod_cast h1
  exact Nat.dvd_one.mp hn

lemma pd2a_root_graph_natural_predicate (u v S : ℕ) (hu : 0 < u) (hS : 0 < S)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₃ r₃ : ℝ) :
    (Nat.Coprime u v ∧ ∃ c d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧
      0 ≤ c ∧ c < u ∧ l₃ ≤ (c : ℝ) / u ∧ (c : ℝ) / u ≤ r₃ ∧
      g₀ 0 0 = (u : ZMod S) ∧ g₀ 0 1 = (c : ZMod S) ∧
      g₀ 1 0 = (v : ZMod S) ∧ g₀ 1 1 = (d : ZMod S)) ↔
    ∃ c : ℕ, c < u ∧ l₃ ≤ (c : ℝ) / u ∧ (c : ℝ) / u ≤ r₃ ∧
      g₀ 0 0 = (u : ZMod S) ∧ g₀ 0 1 = (c : ZMod S) ∧ g₀ 1 0 = (v : ZMod S) ∧
      ((c : ZMod (u * S)) * (v : ZMod (u * S))) =
        (u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1 := by
  letI : NeZero S := ⟨hS.ne'⟩
  constructor
  · rintro ⟨hcop, c, d, hdet, hc0, hcu, hcl, hcr, hgu, hgc, hgv, hgd⟩
    have hcast : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc0
    have hcNat : c.toNat < u := by
      have h := hcast.trans_lt hcu
      exact_mod_cast h
    have hcR : (c.toNat : ℝ) = (c : ℝ) := by exact_mod_cast hcast
    have hcS : (c.toNat : ZMod S) = (c : ZMod S) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod S)) hcast
    have hcM : (c.toNat : ZMod (u * S)) = (c : ZMod (u * S)) := by
      simpa only [Int.cast_natCast] using congrArg (fun j : ℤ => (j : ZMod (u * S))) hcast
    refine ⟨c.toNat, hcNat, by simpa only [hcR] using hcl,
      by simpa only [hcR] using hcr, hgu, by simpa only [hcS] using hgc, hgv, ?_⟩
    have hd₀ : (d : ZMod S) = ((((g₀ 1 1).val : ℕ) : ℤ) : ZMod S) := by simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hgd.symm
    have h := (pd2a_root_det_congruence u v S hu c d (g₀ 1 1).val hdet).mp hd₀
    rw [hcM]
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one] using h
  · rintro ⟨c, hcu, hcl, hcr, hgu, hgc, hgv, hcong⟩
    have hcong' : (((c : ℤ) * (v : ℤ) : ℤ) : ZMod (u * S)) =
        (((u : ℤ) * ((g₀ 1 1).val : ℤ) - 1 : ℤ) : ZMod (u * S)) := by
      simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one] using hcong
    obtain ⟨d, hdet, hd⟩ := (pd2a_completion_residue_iff u v S hu c (g₀ 1 1).val).mpr hcong'
    refine ⟨pd2a_det_one_coprime u v c d hdet, (c : ℤ), d, hdet, by positivity,
      by exact_mod_cast hcu, by simpa using hcl, by simpa using hcr, hgu,
      by simpa using hgc, hgv, ?_⟩
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hd.symm

end ArtinPrimitiveRoots.TypeII.PD
