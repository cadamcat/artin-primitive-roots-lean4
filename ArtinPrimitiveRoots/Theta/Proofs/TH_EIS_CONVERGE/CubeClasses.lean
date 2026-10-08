import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

/-- A finite cokernel and finitely many kernel power classes give finitely many
power classes in every shifted power fiber. This is the group step in cubic Selmer finiteness. -/
theorem finite_power_fiber_classes {A B : Type*} [CommGroup A] [CommGroup B]
    (φ : A →* B) (n : ℕ) (r : B) [Finite (B ⧸ φ.range)]
    [Finite (φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range)] :
    Set.Finite ((QuotientGroup.mk' (powMonoidHom n : A →* A).range) ''
      {a : A | ∃ b : B, φ a = b ^ n * r}) := by
  classical
  let Q := B ⧸ φ.range
  let U := φ.ker ⧸ (powMonoidHom n : φ.ker →* φ.ker).range
  let p : A →* A ⧸ (powMonoidHom n : A →* A).range :=
    QuotientGroup.mk' _
  let x : Q → A := fun q =>
    if h : ∃ a : A, φ a = (Quotient.out q) ^ n * r then h.choose else 1
  let f : Q × U → A ⧸ (powMonoidHom n : A →* A).range :=
    fun q => p (x q.1 * (Quotient.out q.2 : φ.ker).val)
  apply (Set.finite_range f).subset
  rintro z ⟨a, ⟨b, hab⟩, rfl⟩
  let q : Q := QuotientGroup.mk b
  have hbq : b / Quotient.out q ∈ φ.range :=
    QuotientGroup.eq_iff_div_mem.mp (Quotient.out_eq q).symm
  obtain ⟨t, ht⟩ := hbq
  have hbt : b = Quotient.out q * φ t := by
    rw [ht, mul_div_cancel]
  have hx : ∃ a : A, φ a = (Quotient.out q) ^ n * r := by
    refine ⟨a / t ^ n, ?_⟩
    rw [map_div, map_pow, hab, hbt, mul_pow]
    rw [mul_right_comm _ (φ t ^ n) r, mul_div_cancel_right]
  have hxt : φ (x q) = (Quotient.out q) ^ n * r := by
    dsimp only [x]
    rw [dite_eq_left hx]
    exact hx.choose_spec
  let u : φ.ker := ⟨a / (t ^ n * x q), by
    apply MonoidHom.mem_ker.mpr
    rw [map_div, map_mul, map_pow, hab, hbt, mul_pow, hxt]
    rw [mul_comm (Quotient.out q ^ n) (φ t ^ n), mul_assoc, div_self']⟩
  let qU : U := QuotientGroup.mk u
  have huq : (Quotient.out qU : φ.ker) / u ∈
      (powMonoidHom n : φ.ker →* φ.ker).range :=
    QuotientGroup.eq_iff_div_mem.mp (Quotient.out_eq qU)
  obtain ⟨v, hv⟩ := huq
  have hv' : (v : A) ^ n = (Quotient.out qU : φ.ker).val / (u : A) :=
    congrArg (fun w : φ.ker => (w : A)) hv
  have hu : (Quotient.out qU : φ.ker).val = (u : A) * (v : A) ^ n := by
    rw [hv', mul_div_cancel]
  have ha : a = t ^ n * (x q * (u : A)) := by
    change a = t ^ n * (x q * (a / (t ^ n * x q)))
    rw [← mul_assoc, mul_div_cancel]
  have hp (t : A) : p (t ^ n) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨t, rfl⟩
  refine ⟨(q, qU), ?_⟩
  change p (x q * (Quotient.out qU : φ.ker).val) = p a
  calc
    _ = p (x q * (u : A)) := by
      rw [hu, ← mul_assoc, map_mul, hp, mul_one]
    _ = p a := by simp only [ha, map_mul, hp, one_mul]

end ArtinPrimitiveRoots.A1.Theta
