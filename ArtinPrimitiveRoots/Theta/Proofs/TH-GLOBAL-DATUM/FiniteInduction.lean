import ArtinPrimitiveRoots.Theta.TorusInd

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta.FiniteTorusInduction

/-- The induced finite model, including the evaluation functional needed globally. -/
structure Model (Q : Type) [CommGroup Q] (c : Q →* Q →* ℂˣ) (L : Subgroup Q) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [nsp : NormedSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  σ : Q → V →ₗ[ℂ] V
  σ_one : σ 1 = LinearMap.id
  σ_mul : ∀ x y, (σ x).comp (σ y) = (c x y : ℂ) • σ (x * y)
  σ_finite : (Set.range σ).Finite
  lam : V →ₗ[ℂ] ℂ
  lam_fixed : ∀ y ∈ L, ∀ f, lam (σ y f) = lam f
  lam_ne : lam ≠ 0

attribute [instance] Model.nacg Model.nsp Model.fd

/-- Induce the trivial character on an isotropic subgroup of a finite bicharacter group. -/
theorem exists_model (Q : Type) [CommGroup Q] [Fintype Q]
    (c : Q →* Q →* ℂˣ) (L : Subgroup Q)
    (hiso : ∀ x ∈ L, ∀ y ∈ L, c x y = 1) : Nonempty (Model Q c L) := by
  classical
  let W : Submodule ℂ (Q → ℂ) := {
    carrier := {f | ∀ l ∈ L, ∀ q, f (l * q) = (c l q : ℂ)⁻¹ * f q}
    zero_mem' := by intro l hl q; simp
    add_mem' := by
      intro f g hf hg l hl q
      change f (l * q) + g (l * q) = (c l q : ℂ)⁻¹ * (f q + g q)
      rw [hf l hl q, hg l hl q, mul_add]
    smul_mem' := by
      intro a f hf l hl q
      change a * f (l * q) = (c l q : ℂ)⁻¹ * (a * f q)
      rw [hf l hl q]
      ring
  }
  let σ : Q → W →ₗ[ℂ] W := fun y => {
    toFun := fun f => ⟨fun q => (c q y : ℂ) * f.val (q * y), by
      intro l hl q
      change (c (l * q) y : ℂ) * f.val ((l * q) * y) =
        (c l q : ℂ)⁻¹ * ((c q y : ℂ) * f.val (q * y))
      rw [mul_assoc, f.property l hl (q * y)]
      simp only [map_mul, MonoidHom.mul_apply, Units.val_mul]
      field_simp [(c l q).ne_zero, (c l y).ne_zero]
      <;> ring⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext q
      change (c q y : ℂ) * (f.val (q * y) + g.val (q * y)) =
        (c q y : ℂ) * f.val (q * y) + (c q y : ℂ) * g.val (q * y)
      exact mul_add _ _ _
    map_smul' := by
      intro a f
      apply Subtype.ext
      funext q
      change (c q y : ℂ) * (a * f.val (q * y)) = a * ((c q y : ℂ) * f.val (q * y))
      ring
  }
  let lam : W →ₗ[ℂ] ℂ := {
    toFun := fun f => f.val 1
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
  }
  let f0 : W := ⟨fun q => if q ∈ L then 1 else 0, by
    intro l hl q
    by_cases hq : q ∈ L
    · simp [hq, L.mul_mem hl hq, hiso l hl q hq]
    · have hlq : l * q ∉ L := by
        intro h
        apply hq
        have h' := L.mul_mem (L.inv_mem hl) h
        simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h'
      simp [hq, hlq]⟩
  refine ⟨{
    V := W
    σ := σ
    σ_one := ?_
    σ_mul := ?_
    σ_finite := Set.finite_range σ
    lam := lam
    lam_fixed := ?_
    lam_ne := ?_
  }⟩
  · apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext q
    change (c q 1 : ℂ) * f.val (q * 1) = f.val q
    simp
  · intro x y
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext q
    change (c q x : ℂ) * ((c (q * x) y : ℂ) * f.val ((q * x) * y)) =
      (c x y : ℂ) * ((c q (x * y) : ℂ) * f.val (q * (x * y)))
    simp only [map_mul, MonoidHom.mul_apply, Units.val_mul, mul_assoc]
    ring
  · intro y hy f
    change (c 1 y : ℂ) * f.val (1 * y) = f.val 1
    have hf : f.val y = f.val 1 := by simpa using f.property y hy 1
    simpa using hf
  · intro h
    have hf0 : lam f0 = 1 := by simp [lam, f0]
    have h' := DFunLike.congr_fun h f0
    rw [hf0] at h'
    exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using h')

end ArtinPrimitiveRoots.A1.Theta.FiniteTorusInduction
