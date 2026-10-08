import ArtinPrimitiveRoots.A1.Field

/-! Entrywise congruence subgroups in a finite completion. -/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol

open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Matrices congruent to identity modulo a positive valuation ball form a subgroup. -/
theorem exists_congruenceSubgroup (v : FinPlace F) (m : ℕ) (hm : 1 ≤ m) :
    ∃ U : Subgroup (GL (Fin 2) (v.adicCompletion F)),
      ∀ g, g ∈ U ↔ ∀ i j,
        Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤
          WithZero.exp (-(m : ℤ)) := by
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r := WithZero.exp (-(m : ℤ))
  let P : GL (Fin 2) K → Prop := fun g => ∀ i j,
    V ((g : Matrix (Fin 2) (Fin 2) K) i j - (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r
  have hr : r < 1 := by
    dsimp [r]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have small_mul {x y : K} (hx : V x ≤ r) (hy : V y ≤ 1) : V (x * y) ≤ r := by
    rw [map_mul]
    simpa only [mul_one] using mul_le_mul' hx hy
  have mat_add {A B : Matrix (Fin 2) (Fin 2) K}
      (hA : ∀ i j, V (A i j) ≤ r) (hB : ∀ i j, V (B i j) ≤ r) :
      ∀ i j, V ((A + B) i j) ≤ r := fun i j => V.map_add_le (hA i j) (hB i j)
  have mat_mul {A B : Matrix (Fin 2) (Fin 2) K}
      (hA : ∀ i j, V (A i j) ≤ r) (hB : ∀ i j, V (B i j) ≤ r) :
      ∀ i j, V ((A * B) i j) ≤ r := by
    intro i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact V.map_add_le (small_mul (hA i 0) ((hB 0 j).trans hr.le))
      (small_mul (hA i 1) ((hB 1 j).trans hr.le))
  have one_closed : P 1 := by simp [P]
  have mul_closed (g h : GL (Fin 2) K) (hg : P g) (hh : P h) : P (g * h) := by
    have heq : ((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1 =
        ((g : Matrix (Fin 2) (Fin 2) K) - 1) * ((h : Matrix (Fin 2) (Fin 2) K) - 1) +
        ((g : Matrix (Fin 2) (Fin 2) K) - 1) + ((h : Matrix (Fin 2) (Fin 2) K) - 1) := by
      change (g : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) - 1 = _
      rw [sub_mul, mul_sub, one_mul, mul_one]
      abel
    change ∀ i j, V ((((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) i j) ≤ r
    rw [heq]
    exact mat_add (mat_add (mat_mul hg hh) hg) hh
  have inv_closed (g : GL (Fin 2) K) (hg : P g) : P g⁻¹ := by
    have ha : V ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) ≤ r := by simpa using hg 0 0
    have hd : V ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) ≤ r := by simpa using hg 1 1
    have hb : V ((g : Matrix (Fin 2) (Fin 2) K) 0 1) ≤ r := by simpa using hg 0 1
    have hc : V ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ≤ r := by simpa using hg 1 0
    have near_one (x : K) (hx : V (x - 1) ≤ r) : V x = 1 := by
      simpa using V.map_eq_of_sub_lt (x := 1) (y := x) (by simpa using hx.trans_lt hr)
    let D : K := (g : Matrix (Fin 2) (Fin 2) K).det
    have hDsmall : V (D - 1) ≤ r := by
      have heq : D - 1 =
          ((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * (g : Matrix (Fin 2) (Fin 2) K) 1 1 +
          ((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) -
          (g : Matrix (Fin 2) (Fin 2) K) 0 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
        dsimp [D]
        rw [Matrix.det_fin_two]
        ring
      rw [heq]
      exact V.map_sub_le (V.map_add_le (small_mul ha (near_one _ hd).le) hd)
        (small_mul hb (hc.trans hr.le))
    have hDval : V D = 1 := near_one D hDsmall
    have hDinv : V D⁻¹ = 1 := by rw [map_inv₀, hDval, inv_one]
    have diagonal_bound (x : K) (hx : V (x - 1) ≤ r) : V (D⁻¹ * x - 1) ≤ r := by
      have hxd : V (x - D) ≤ r := by
        have heq : x - D = (x - 1) - (D - 1) := by ring
        rw [heq]
        exact V.map_sub_le hx hDsmall
      have heq : D⁻¹ * x - 1 = D⁻¹ * (x - D) := by
        rw [mul_sub, inv_mul_cancel₀ (a := D) g.det_ne_zero]
      rw [heq, map_mul, hDinv, one_mul]
      exact hxd
    have offdiag_bound (x : K) (hx : V x ≤ r) : V (D⁻¹ * -x) ≤ r := by
      rw [map_mul, V.map_neg, hDinv, one_mul]
      exact hx
    have hinv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        D⁻¹ • !![(g : Matrix (Fin 2) (Fin 2) K) 1 1,
          -(g : Matrix (Fin 2) (Fin 2) K) 0 1;
          -(g : Matrix (Fin 2) (Fin 2) K) 1 0,
          (g : Matrix (Fin 2) (Fin 2) K) 0 0] := by
      rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv,
        Matrix.adjugate_fin_two]
    intro i j
    change V (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j -
      (1 : Matrix (Fin 2) (Fin 2) K) i j) ≤ r
    rw [hinv]
    fin_cases i <;> fin_cases j
    · simpa [Matrix.smul_apply, smul_eq_mul] using diagonal_bound _ hd
    · simpa [Matrix.smul_apply, smul_eq_mul] using offdiag_bound _ hb
    · simpa [Matrix.smul_apply, smul_eq_mul] using offdiag_bound _ hc
    · simpa [Matrix.smul_apply, smul_eq_mul] using diagonal_bound _ ha
  let U : Subgroup (GL (Fin 2) K) := {
    carrier := {g | P g}
    one_mem' := one_closed
    mul_mem' := by intro g h hg hh; exact mul_closed g h hg hh
    inv_mem' := by intro g hg; exact inv_closed g hg
  }
  exact ⟨U, fun _ => Iff.rfl⟩

end ArtinPrimitiveRoots.Proofs.th_cover_sol
