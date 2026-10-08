import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Valuation geometry of the tame Lagrangian, before its Hilbert pairing is considered. -/
structure TameLocalGeometry (v : FinPlace F) where
  Alag : Subgroup (v.adicCompletion F)ˣ
  mem_alag : ∀ y : (v.adicCompletion F)ˣ,
    y ∈ Alag ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ),
      IsLocUnit v u ∧ y = unifLoc v ^ (3 * k) * u
  cubes : ∀ t : (v.adicCompletion F)ˣ, t ^ 3 ∈ Alag
  decomposition : ∀ y : (v.adicCompletion F)ˣ,
    ∃ (j : ℤ) (u : (v.adicCompletion F)ˣ), IsLocUnit v u ∧ y = unifLoc v ^ j * u

/-- Every local element has a unit part, and valuation classes divisible by three form a subgroup. -/
theorem exists_tameLocalGeometry (v : FinPlace F) : Nonempty (TameLocalGeometry v) := by
  classical
  let K := (v.adicCompletion F)ˣ
  let U : Subgroup K := {
    carrier := {u | IsLocUnit v u}
    one_mem' := by
      constructor
      · exact (v.adicCompletionIntegers F).one_mem
      · simpa using (v.adicCompletionIntegers F).one_mem
    mul_mem' := by
      intro a b ha hb
      constructor
      · exact (v.adicCompletionIntegers F).mul_mem _ _ ha.1 hb.1
      · simpa only [mul_inv_rev, Units.val_mul] using
          (v.adicCompletionIntegers F).mul_mem _ _ hb.2 ha.2
    inv_mem' := by
      intro a ha
      exact ⟨ha.2, by simpa using ha.1⟩
  }
  have hdecomp (x : K) : ∃ (j : ℤ) (u : K), IsLocUnit v u ∧ x = unifLoc v ^ j * u := by
    have hx0 : Valued.v (x : v.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr x.ne_zero
    have hxv : Valued.v (x : v.adicCompletion F) = WithZero.exp (-ordv v x) := by
      rw [← WithZero.exp_log hx0]
      simp [ordv, WithZero.toAdd_unzero_eq_log hx0]
    have hπ : Valued.v (unifLoc v : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      change Valued.v ((unif v : F) : v.adicCompletion F) = WithZero.exp (-1 : ℤ)
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
    have hval : Valued.v (unitPart v x : v.adicCompletion F) = 1 := by
      simp only [unitPart, Units.val_mul, Units.val_zpow_eq_zpow_val]
      change Valued.v ((x : v.adicCompletion F) *
        (unifLoc v : v.adicCompletion F) ^ (-ordv v x)) = 1
      rw [map_mul, map_zpow₀, hxv, hπ]
      rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
      congr 1
      simp
    refine ⟨ordv v x, unitPart v x, ?_, ?_⟩
    · constructor
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        have hval' : Valued.v (((unitPart v x)⁻¹ : K) : v.adicCompletion F) = 1 := by
          rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
        rw [hval']
    · symm
      dsimp [unitPart]
      calc
        unifLoc v ^ ordv v x * (x * unifLoc v ^ (-ordv v x)) =
            x * (unifLoc v ^ ordv v x * (unifLoc v ^ ordv v x)⁻¹) := by
          rw [zpow_neg]
          ac_rfl
        _ = x := by simp
  let L : Subgroup K := {
    carrier := {y | ∃ (k : ℤ) (u : K), IsLocUnit v u ∧ y = unifLoc v ^ (3 * k) * u}
    one_mem' := ⟨0, 1, U.one_mem, by simp⟩
    mul_mem' := by
      rintro x y ⟨k, u, hu, rfl⟩ ⟨l, w, hw, rfl⟩
      refine ⟨k + l, u * w, U.mul_mem hu hw, ?_⟩
      rw [mul_add, zpow_add]
      ac_rfl
    inv_mem' := by
      rintro y ⟨k, u, hu, rfl⟩
      refine ⟨-k, u⁻¹, U.inv_mem hu, ?_⟩
      rw [mul_inv_rev, mul_neg, zpow_neg]
      exact mul_comm _ _
  }
  refine ⟨{
    Alag := L
    mem_alag := fun _ => Iff.rfl
    cubes := ?_
    decomposition := hdecomp
  }⟩
  intro t
  obtain ⟨j, u, hu, ht⟩ := hdecomp t
  refine ⟨j, u ^ 3, U.pow_mem hu 3, ?_⟩
  rw [ht, mul_pow]
  congr 1
  calc
    (unifLoc v ^ j) ^ 3 = (unifLoc v ^ j) ^ (3 : ℤ) := (zpow_natCast _ 3).symm
    _ = unifLoc v ^ (j * 3) := (zpow_mul _ j 3).symm
    _ = unifLoc v ^ (3 * j) := by rw [mul_comm j (3 : ℤ)]

end ArtinPrimitiveRoots.A1.Theta
