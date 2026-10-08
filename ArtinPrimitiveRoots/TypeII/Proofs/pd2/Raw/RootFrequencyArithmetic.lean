import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootSpectrum

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_gcd_modular_eq (u a b : ℕ) (hEq : (a : ZMod u) = (b : ZMod u)) :
    Nat.gcd a u = Nat.gcd b u := by
  have hmod := (ZMod.natCast_eq_natCast_iff' a b u).mp hEq
  calc
    Nat.gcd a u = Nat.gcd (a % u) u := by rw [Nat.gcd_comm a u, Nat.gcd_rec]
    _ = Nat.gcd (b % u) u := by rw [hmod]
    _ = Nat.gcd b u := by rw [← Nat.gcd_rec, Nat.gcd_comm]

lemma pd2a_gcd_product_bound (u D H : ℕ) (hu : 0 < u) (hD : 0 < D) :
    Nat.gcd H (u * D) ≤ D * Nat.gcd H u := by
  let g := Nat.gcd H (u * D)
  have hgDiv : g ∣ u * D := Nat.gcd_dvd_right _ _
  have hg : g ∣ Nat.gcd g u * D := dvd_gcd_mul_of_dvd_mul hgDiv
  have hEq : Nat.gcd g u = Nat.gcd H u := by
    dsimp [g]
    rw [Nat.gcd_assoc, Nat.gcd_eq_right (dvd_mul_right u D)]
  rw [hEq] at hg
  have hpos : 0 < Nat.gcd H u := Nat.gcd_pos_of_pos_right H hu
  have hBound := Nat.le_of_dvd (mul_pos hpos hD) hg
  simpa only [mul_comm] using hBound

lemma pd2a_gcd_pair_product_bound_left (u D H K : ℕ) (hu : 0 < u) (hD : 0 < D) :
    Nat.gcd (Nat.gcd H K) (u * D) ≤ D * Nat.gcd H u := by
  have hg : Nat.gcd (Nat.gcd H K) (u * D) ∣ Nat.gcd H (u * D) :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
  have hpos : 0 < Nat.gcd H (u * D) := Nat.gcd_pos_of_pos_right H (mul_pos hu hD)
  exact (Nat.le_of_dvd hpos hg).trans (pd2a_gcd_product_bound u D H hu hD)

lemma pd2a_gcd_pair_product_bound_right (u D H K : ℕ) (hu : 0 < u) (hD : 0 < D) :
    Nat.gcd (Nat.gcd H K) (u * D) ≤ D * Nat.gcd K u := by
  rw [Nat.gcd_comm H K]
  exact pd2a_gcd_pair_product_bound_left u D K H hu hD

lemma pd2a_zmod_divisor_cast_value (m u : ℕ) [NeZero m] (hdiv : u ∣ m) (z : ZMod m) :
    ZMod.castHom hdiv (ZMod u) z = (z.val : ZMod u) := by
  calc
    _ = ZMod.castHom hdiv (ZMod u) (z.val : ZMod m) :=
      congrArg (ZMod.castHom hdiv (ZMod u)) (ZMod.natCast_zmod_val z).symm
    _ = _ := map_natCast _ _

lemma pd2a_unit_frequency_gcd (m u : ℕ) [NeZero m] (hdiv : u ∣ m) (Γ : (ZMod m)ˣ) (h : ℕ) :
    Nat.gcd (((Γ : ZMod m) * (h : ZMod m)).val) u = Nat.gcd h u := by
  have hUnit : Nat.Coprime (Γ : ZMod m).val u := (ZMod.val_coe_unit_coprime Γ).of_dvd_right hdiv
  have hEqM : (((Γ : ZMod m) * (h : ZMod m)).val : ZMod m) =
      (((Γ : ZMod m).val * h : ℕ) : ZMod m) := by simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  have hEqU : (((Γ : ZMod m) * (h : ZMod m)).val : ZMod u) =
      (((Γ : ZMod m).val * h : ℕ) : ZMod u) := by
    have hc := congrArg (ZMod.castHom hdiv (ZMod u)) hEqM
    simpa only [map_natCast] using hc
  rw [pd2a_gcd_modular_eq u _ _ hEqU]
  simpa only [Nat.gcd_comm] using hUnit.gcd_mul_left_cancel_right h

lemma pd2a_shifted_unit_frequency_gcd (u D : ℕ) [NeZero (u * D)]
    (Γ : (ZMod (u * D))ˣ) (h j : ℕ) :
    Nat.gcd (((Γ : ZMod (u * D)) * (h : ZMod (u * D)) +
      (u : ZMod (u * D)) * (j : ZMod (u * D))).val) u = Nat.gcd h u := by
  let q : ZMod (u * D) := (Γ : ZMod (u * D)) * (h : ZMod (u * D))
  have hdiv : u ∣ u * D := dvd_mul_right u D
  have hEq : ((q + (u : ZMod (u * D)) * (j : ZMod (u * D))).val : ZMod u) = (q.val : ZMod u) := by
    rw [← pd2a_zmod_divisor_cast_value (u * D) u hdiv, ← pd2a_zmod_divisor_cast_value (u * D) u hdiv]
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [pd2a_gcd_modular_eq u _ _ hEq]
  exact pd2a_unit_frequency_gcd (u * D) u hdiv Γ h

lemma pd2a_product_unit_frequency_gcd (u D : ℕ) [NeZero (u * D)]
    (Γ α : (ZMod (u * D))ˣ) (k : ℕ) :
    Nat.gcd (((Γ : ZMod (u * D)) * (k : ZMod (u * D)) * (α : ZMod (u * D))).val) u = Nat.gcd k u := by
  have heq : (Γ : ZMod (u * D)) * (k : ZMod (u * D)) * (α : ZMod (u * D)) =
      ((Γ * α : (ZMod (u * D))ˣ) : ZMod (u * D)) * (k : ZMod (u * D)) := by
    simp only [Units.val_mul]
    ring
  rw [heq]
  exact pd2a_unit_frequency_gcd (u * D) u (dvd_mul_right u D) (Γ * α) k

end ArtinPrimitiveRoots.TypeII.PD
