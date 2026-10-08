import ArtinPrimitiveRoots.A2.Proofs.A2_CONDUCTOR_SIEVE.Defs
import Mathlib.NumberTheory.MulChar.Duality

set_option autoImplicit false
open NumberField IsDedekindDomain ClassFieldTheory
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

private noncomputable def conductorMulCharEquivToUnits {R : Type*} [CommRing R] [Fintype R] :
    MulChar R ℂ ≃ Rˣ := (MulChar.mulEquiv_units (M := R) (R := ℂ)).some.toEquiv

private noncomputable instance conductorMulCharFintype {R : Type*} [CommRing R] [Fintype R] :
    Fintype (MulChar R ℂ) :=
  Fintype.ofEquiv Rˣ (conductorMulCharEquivToUnits (R := R)).symm

private theorem conductor_mulChar_sum_on_unit {R : Type*} [CommRing R] [Fintype R]
    (u : Rˣ) :
    (∑ χ : MulChar R ℂ, χ (u : R)) =
      if u = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  classical
  let e : MulChar R ℂ ≃ Rˣ := conductorMulCharEquivToUnits (R := R)
  have hcard : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := Fintype.card_congr e
  by_cases hu : u = 1
  · subst u
    simp [hcard]
  · have hval : (u : R) ≠ 1 := by
      intro h
      exact hu (Units.ext h)
    obtain ⟨ξ, hξ⟩ :=
      MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (M := R) (R := ℂ) hval
    have hshift : (∑ χ : MulChar R ℂ, χ (u : R)) =
        ∑ χ : MulChar R ℂ, (ξ * χ) (u : R) := by
      symm
      exact Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ (by intro χ; rfl)
    have hfactor : (∑ χ : MulChar R ℂ, (ξ * χ) (u : R)) =
        ξ (u : R) * ∑ χ : MulChar R ℂ, χ (u : R) := by
      simp only [MulChar.mul_apply]
      rw [Finset.mul_sum]
    have hzero : (∑ χ : MulChar R ℂ, χ (u : R)) = 0 := by
      apply eq_zero_of_mul_eq_self_left hξ
      calc
        ξ (u : R) * ∑ χ : MulChar R ℂ, χ (u : R) =
            ∑ χ : MulChar R ℂ, (ξ * χ) (u : R) := hfactor.symm
        _ = ∑ χ : MulChar R ℂ, χ (u : R) := hshift.symm
    simp [hu, hzero]

private theorem conductor_mulChar_orthogonality {R : Type*} [CommRing R] [Fintype R]
    (x y : R) :
    (∑ χ : MulChar R ℂ, χ x * χ⁻¹ y) =
      if x = y ∧ IsUnit x then (Fintype.card Rˣ : ℂ) else 0 := by
  classical
  by_cases hx : IsUnit x
  · by_cases hy : IsUnit y
    · let ux : Rˣ := hx.unit
      let uy : Rˣ := hy.unit
      have hxval : (ux : R) = x := hx.unit_spec
      have hyval : (uy : R) = y := hy.unit_spec
      have hpoint (χ : MulChar R ℂ) :
          χ x * χ⁻¹ y = χ ((ux * uy⁻¹ : Rˣ) : R) := by
        calc
          χ x * χ⁻¹ y = χ (ux : R) * χ⁻¹ (uy : R) := by rw [hxval, hyval]
          _ = χ (ux : R) * χ ((uy⁻¹ : Rˣ) : R) := by
            rw [MulChar.inv_apply, Ring.inverse_unit]
          _ = χ ((ux : R) * ((uy⁻¹ : Rˣ) : R)) := by rw [← map_mul]
          _ = χ ((ux * uy⁻¹ : Rˣ) : R) := rfl
      have hratio : ux * uy⁻¹ = 1 ↔ x = y := by
        constructor
        · intro h
          have huv : ux = uy := (mul_inv_eq_one.mp h)
          rw [← hxval, ← hyval, huv]
        · intro hxy
          apply mul_inv_eq_one.mpr
          apply Units.ext
          simp [hxval, hyval, hxy]
      rw [show (∑ χ : MulChar R ℂ, χ x * χ⁻¹ y) =
          ∑ χ : MulChar R ℂ, χ ((ux * uy⁻¹ : Rˣ) : R) by
            apply Finset.sum_congr rfl
            intro χ _
            exact hpoint χ]
      rw [conductor_mulChar_sum_on_unit]
      by_cases hxy : x = y
      · have huEq : ux * uy⁻¹ = 1 := hratio.mpr hxy
        simp [hxy, hy, huEq]
      · have huNe : ux * uy⁻¹ ≠ 1 := fun h => hxy (hratio.mp h)
        simp [hxy, hx, huNe]
    · have hxy : x ≠ y := by
        intro h
        subst y
        exact hy hx
      simp [MulChar.map_nonunit, hy, hxy]
  · simp [MulChar.map_nonunit, hx]

private theorem conductor_mulChar_parseval {R : Type*} [CommRing R] [Fintype R]
    (g : R → ℂ) :
    (∑ χ : MulChar R ℂ,
        Complex.normSq (∑ x : R, χ⁻¹ x * g x)) =
      (Fintype.card Rˣ : ℝ) * ∑ u : Rˣ, Complex.normSq (g (u : R)) := by
  classical
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  have hexpand (χ : MulChar R ℂ) :
      star (∑ x : R, χ⁻¹ x * g x) * (∑ y : R, χ⁻¹ y * g y) =
        ∑ x : R, ∑ y : R,
          (χ x * χ⁻¹ y) * (star (g x) * g y) := by
    simp only [star_sum, star_mul, MulChar.star_apply', inv_inv]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  calc
    (∑ χ : MulChar R ℂ,
        star (∑ x : R, χ⁻¹ x * g x) * (∑ y : R, χ⁻¹ y * g y)) =
        ∑ χ : MulChar R ℂ, ∑ x : R, ∑ y : R,
          (χ x * χ⁻¹ y) * (star (g x) * g y) := by
      apply Finset.sum_congr rfl
      intro χ _
      exact hexpand χ
    _ = ∑ x : R, ∑ y : R, ∑ χ : MulChar R ℂ,
          (χ x * χ⁻¹ y) * (star (g x) * g y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x : R, ∑ y : R,
          (∑ χ : MulChar R ℂ, χ x * χ⁻¹ y) * (star (g x) * g y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_mul]
    _ = ∑ x : R, ∑ y : R,
          (if x = y ∧ IsUnit x then (Fintype.card Rˣ : ℂ) else 0) *
            (star (g x) * g y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [conductor_mulChar_orthogonality]
    _ = (Fintype.card Rˣ : ℂ) *
          ∑ x : R, if IsUnit x then star (g x) * g x else 0 := by
      have hdiag (x : R) :
          (∑ y : R,
            (if x = y ∧ IsUnit x then (Fintype.card Rˣ : ℂ) else 0) *
              (star (g x) * g y)) =
            if IsUnit x then (Fintype.card Rˣ : ℂ) * (star (g x) * g x) else 0 := by
        by_cases hx : IsUnit x
        · simp [hx]
        · simp [hx]
      calc
        (∑ x : R, ∑ y : R,
            (if x = y ∧ IsUnit x then (Fintype.card Rˣ : ℂ) else 0) *
              (star (g x) * g y)) =
            ∑ x : R, if IsUnit x then
              (Fintype.card Rˣ : ℂ) * (star (g x) * g x) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          exact hdiag x
        _ = ∑ x : R, (Fintype.card Rˣ : ℂ) *
              (if IsUnit x then star (g x) * g x else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : IsUnit x <;> simp [hx]
        _ = (Fintype.card Rˣ : ℂ) *
              ∑ x : R, if IsUnit x then star (g x) * g x else 0 := by
          rw [Finset.mul_sum]
    _ = (Fintype.card Rˣ : ℂ) *
          ∑ u : Rˣ, star (g (u : R)) * g (u : R) := by
      congr 1
      let f : R → ℂ := fun x => if IsUnit x then star (g x) * g x else 0
      have hsplit := Fintype.sum_subtype_add_sum_subtype (fun x : R => IsUnit x) f
      have hfalse :
          (∑ x : {x : R // ¬ IsUnit x}, f x.1) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        simp [f, x.2]
      let toSubtype : Rˣ → {x : R // IsUnit x} := fun u => ⟨(u : R), u.isUnit⟩
      have hbij : Function.Bijective toSubtype := by
        constructor
        · intro u v h
          apply Units.ext
          exact congrArg Subtype.val h
        · intro x
          refine ⟨x.2.unit, ?_⟩
          apply Subtype.ext
          exact x.2.unit_spec
      let hequiv : Rˣ ≃ {x : R // IsUnit x} := Equiv.ofBijective toSubtype hbij
      have htrue :
          (∑ x : {x : R // IsUnit x}, f x.1) =
            ∑ u : Rˣ, star (g (u : R)) * g (u : R) := by
        calc
          (∑ x : {x : R // IsUnit x}, f x.1) =
              ∑ x : {x : R // IsUnit x}, star (g x.1) * g x.1 := by
            apply Finset.sum_congr rfl
            intro x _
            simp [f, x.2]
          _ = ∑ u : Rˣ, star (g (u : R)) * g (u : R) := by
            symm
            exact Fintype.sum_equiv hequiv _ _ (by intro u; rfl)
      calc
        (∑ x : R, f x) =
            (∑ x : {x : R // IsUnit x}, f x.1) +
              ∑ x : {x : R // ¬ IsUnit x}, f x.1 := hsplit.symm
        _ = ∑ u : Rˣ, star (g (u : R)) * g (u : R) := by
          rw [htrue, hfalse, add_zero]

/-- The finite Gauss expansion and ALL unit-character orthogonality bound a
subset of primitive characters. The unit residue ring is included.
Guide: sol-thin-a2zf/PROOFS.md:702–719.
Uses OAI primitive_character_expansion and primitive_gaussSum_norm_sq; feeds dyad glue. -/
theorem conductor_gauss_orthogonality {R ι : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (𝓧 : Finset (MulChar R ℂ))
    (h𝓧 : ∀ χ ∈ 𝓧, OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ)
    (B : Finset ι) (r : ι → R) (b : ι → ℂ) :
    (∑ χ ∈ 𝓧, ‖∑ I ∈ B, b I * χ (r I)‖ ^ 2) ≤
      ((Fintype.card Rˣ : ℝ) / (Fintype.card R : ℝ)) *
        ∑ d : Rˣ, ‖∑ I ∈ B, b I * ψ (r I * (d : R))‖ ^ 2 := by
  classical
  let T : R → ℂ := fun a => ∑ I ∈ B, b I * ψ (r I * a)
  let F : MulChar R ℂ → ℂ := fun χ => ∑ a : R, χ⁻¹ a * T a
  let S : MulChar R ℂ → ℂ := fun χ => ∑ I ∈ B, b I * χ (r I)
  have hexpand (χ : MulChar R ℂ)
      (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) :
      S χ = F χ / gaussSum χ⁻¹ ψ := by
    dsimp [S, F, T]
    calc
      (∑ I ∈ B, b I * χ (r I)) =
          ∑ I ∈ B, b I *
            ((∑ a : R, χ⁻¹ a * ψ (r I * a)) /
              gaussSum χ⁻¹ ψ) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [OAI.SevenEighths.FiniteFourier.primitive_character_expansion
          χ hχ ψ hψ (r I)]
      _ = (∑ I ∈ B, b I * (∑ a : R, χ⁻¹ a * ψ (r I * a))) /
            gaussSum χ⁻¹ ψ := by
        calc
          (∑ I ∈ B, b I * ((∑ a : R, χ⁻¹ a * ψ (r I * a)) / gaussSum χ⁻¹ ψ)) =
              ∑ I ∈ B, (b I * (∑ a : R, χ⁻¹ a * ψ (r I * a))) / gaussSum χ⁻¹ ψ := by
            apply Finset.sum_congr rfl
            intro I hI
            ring
          _ = (∑ I ∈ B, b I * (∑ a : R, χ⁻¹ a * ψ (r I * a))) /
                gaussSum χ⁻¹ ψ := by
            rw [← Finset.sum_div]
      _ = (∑ a : R, χ⁻¹ a * (∑ I ∈ B, b I * ψ (r I * a))) /
            gaussSum χ⁻¹ ψ := by
        congr 1
        calc
          (∑ I ∈ B, b I * (∑ a : R, χ⁻¹ a * ψ (r I * a))) =
              ∑ I ∈ B, ∑ a : R, b I * (χ⁻¹ a * ψ (r I * a)) := by
            apply Finset.sum_congr rfl
            intro I hI
            rw [Finset.mul_sum]
          _ = ∑ a : R, ∑ I ∈ B, b I * (χ⁻¹ a * ψ (r I * a)) := by
            rw [Finset.sum_comm]
          _ = ∑ a : R, χ⁻¹ a * (∑ I ∈ B, b I * ψ (r I * a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            calc
              (∑ I ∈ B, b I * (χ⁻¹ a * ψ (r I * a))) =
                  ∑ I ∈ B, χ⁻¹ a * (b I * ψ (r I * a)) := by
                apply Finset.sum_congr rfl
                intro I hI
                ring
              _ = χ⁻¹ a * (∑ I ∈ B, b I * ψ (r I * a)) := by
                rw [Finset.mul_sum]
  have hnorm (χ : MulChar R ℂ)
      (hχ : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals χ) :
      ‖S χ‖ ^ 2 = ‖F χ‖ ^ 2 / (Fintype.card R : ℝ) := by
    rw [hexpand χ hχ, norm_div, div_pow,
      OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm_sq
        χ⁻¹ hχ.inv ψ hψ]
  have hparseval :
      (∑ χ : MulChar R ℂ, ‖F χ‖ ^ 2) =
        (Fintype.card Rˣ : ℝ) * ∑ d : Rˣ, ‖T (d : R)‖ ^ 2 := by
    simpa only [F, T, Complex.normSq_eq_norm_sq] using
      (conductor_mulChar_parseval (R := R) T)
  have hsubset :
      (∑ χ ∈ 𝓧, ‖F χ‖ ^ 2) ≤ ∑ χ : MulChar R ℂ, ‖F χ‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ 𝓧)
      (by intro χ hχ hχnot; positivity)
  have hcardpos : 0 < (Fintype.card R : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card R)
  calc
    (∑ χ ∈ 𝓧, ‖∑ I ∈ B, b I * χ (r I)‖ ^ 2) =
        (Fintype.card R : ℝ)⁻¹ * ∑ χ ∈ 𝓧, ‖F χ‖ ^ 2 := by
      calc
        (∑ χ ∈ 𝓧, ‖∑ I ∈ B, b I * χ (r I)‖ ^ 2) =
            ∑ χ ∈ 𝓧, ‖F χ‖ ^ 2 / (Fintype.card R : ℝ) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          exact hnorm χ (h𝓧 χ hχ)
        _ = (∑ χ ∈ 𝓧, ‖F χ‖ ^ 2) / (Fintype.card R : ℝ) := by
          rw [Finset.sum_div]
        _ = (Fintype.card R : ℝ)⁻¹ * ∑ χ ∈ 𝓧, ‖F χ‖ ^ 2 := by
          rw [div_eq_mul_inv]
          ring
    _ ≤ (Fintype.card R : ℝ)⁻¹ *
          ((Fintype.card Rˣ : ℝ) *
            ∑ d : Rˣ, ‖T (d : R)‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hsubset.trans_eq hparseval)
        (by positivity)
    _ = ((Fintype.card Rˣ : ℝ) / (Fintype.card R : ℝ)) *
          ∑ d : Rˣ, ‖T (d : R)‖ ^ 2 := by
      rw [div_eq_mul_inv]
      ring
    _ = ((Fintype.card Rˣ : ℝ) / (Fintype.card R : ℝ)) *
          ∑ d : Rˣ, ‖∑ I ∈ B, b I * ψ (r I * (d : R))‖ ^ 2 := by
      rfl

end ArtinPrimitiveRoots.A2
