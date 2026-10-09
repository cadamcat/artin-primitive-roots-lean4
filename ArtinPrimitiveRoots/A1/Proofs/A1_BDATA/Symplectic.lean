import ArtinPrimitiveRoots.A1.Field
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

set_option autoImplicit false
open LinearMap
open scoped BigOperators
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a1_bdata_sol

/-- An isotropic subspace of half the dimension of an alternating nondegenerate
space has an isotropic complement. The triangular basis adjustment works
in every characteristic. -/
theorem lagrangian_complement {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V]
    (β : LinearMap.BilinForm K V) (ha : β.IsAlt) (hn : β.Nondegenerate)
    (E : Submodule K V) (hE : ∀ x y : E, β x y = 0)
    (hdim : Module.finrank K V = 2 * Module.finrank K E) :
    ∃ B : Submodule K V, (∀ x y : B, β x y = 0) ∧ IsCompl E B := by
  classical
  have hle : E ≤ β.orthogonal E := by
    intro x hx y hy
    exact hE ⟨y, hy⟩ ⟨x, hx⟩
  have hperp : β.orthogonal E = E := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [BilinForm.finrank_orthogonal hn]
    omega
  let φ : V →ₗ[K] Module.Dual K E := E.subtype.dualMap.comp β
  have hker : φ.ker = E := by
    conv_rhs => rw [← hperp]
    ext x
    change (φ x = 0) ↔ ∀ y ∈ E, β y x = 0
    constructor
    · intro hx y hy
      have hxy : β x y = 0 := LinearMap.congr_fun hx ⟨y, hy⟩
      rw [← ha.neg_eq, hxy, neg_zero]
    · intro hx
      apply LinearMap.ext
      intro y
      change β x (y : V) = 0
      rw [← ha.neg_eq, hx y y.property, neg_zero]
  have hsurj : φ.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hfr := φ.finrank_range_add_finrank_ker
    rw [hker] at hfr
    rw [Subspace.dual_finrank_eq]
    omega
  obtain ⟨σ, hσ⟩ := φ.exists_rightInverse_of_surjective hsurj
  let b := Module.finBasis K E
  let f (i : Fin (Module.finrank K E)) : V := σ (b.dualBasis i)
  have hcross (i j : Fin (Module.finrank K E)) :
      β (f i) (b j) = if j = i then 1 else 0 := by
    have h := congrArg
      (fun ρ : Module.Dual K E →ₗ[K] Module.Dual K E => ρ (b.dualBasis i) (b j)) hσ
    change β (f i) (b j) = b.dualBasis i (b j) at h
    exact h.trans (b.dualBasis_apply_self i j)
  let g (i : Fin (Module.finrank K E)) : V :=
    f i + ∑ k : Fin (Module.finrank K E),
      if k < i then β (f i) (f k) • (b k : V) else 0
  have hsum (i j : Fin (Module.finrank K E)) :
      β (∑ k : Fin (Module.finrank K E),
        if k < i then β (f i) (f k) • (b k : V) else 0) (b j) = 0 := by
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k < i
    · rw [if_pos hki, BilinForm.smul_left, hE (b k) (b j), mul_zero]
    · rw [if_neg hki, BilinForm.zero_left]
  have hcrossg (i j : Fin (Module.finrank K E)) :
      β (g i) (b j) = if j = i then 1 else 0 := by
    dsimp only [g]
    rw [BilinForm.add_left, hsum, add_zero]
    exact hcross i j
  have hsumR (i j : Fin (Module.finrank K E)) :
      β (f i) (∑ k : Fin (Module.finrank K E),
        if k < j then β (f j) (f k) • (b k : V) else 0) =
      if i < j then β (f j) (f i) else 0 := by
    rw [map_sum]
    have hterm (k : Fin (Module.finrank K E)) :
        β (f i) (if k < j then β (f j) (f k) • (b k : V) else 0) =
          if k = i then (if i < j then β (f j) (f i) else 0) else 0 := by
      by_cases hki : k = i
      · subst k
        by_cases hij : i < j <;> simp [hij, BilinForm.smul_right, hcross]
      · by_cases hkj : k < j <;> simp [hki, hkj, BilinForm.smul_right, hcross]
    simp only [hterm]
    simp
  have hsumL (i j : Fin (Module.finrank K E)) :
      β (∑ k : Fin (Module.finrank K E),
        if k < i then β (f i) (f k) • (b k : V) else 0) (g j) =
      -(if j < i then β (f i) (f j) else 0) := by
    rw [map_sum, LinearMap.sum_apply]
    have hek (k : Fin (Module.finrank K E)) :
        β (b k) (g j) = -(if k = j then 1 else 0) := by
      rw [← ha.neg_eq, hcrossg]
    have hterm (k : Fin (Module.finrank K E)) :
        β (if k < i then β (f i) (f k) • (b k : V) else 0) (g j) =
          if k = j then -(if j < i then β (f i) (f j) else 0) else 0 := by
      by_cases hkj : k = j
      · subst k
        by_cases hji : j < i <;> simp [hji, BilinForm.smul_left, hek]
      · by_cases hki : k < i <;> simp [hkj, hki, BilinForm.smul_left, hek]
    simp only [hterm]
    simp
  have hgg (i j : Fin (Module.finrank K E)) : β (g i) (g j) = 0 := by
    change β (f i + _) (g j) = 0
    rw [BilinForm.add_left, hsumL]
    change β (f i) (f j + _) + _ = 0
    rw [BilinForm.add_right, hsumR]
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hskew : β (f j) (f i) = -β (f i) (f j) := (ha.neg_eq _ _).symm
      rw [if_pos hij, if_neg (not_lt_of_ge hij.le), hskew]
      simp
    · simp [ha.self_eq_zero]
    · rw [if_neg (not_lt_of_ge hji.le), if_pos hji]
      simp
  let τ : Module.Dual K E →ₗ[K] V := b.dualBasis.constr K g
  have hτ : φ.comp τ = LinearMap.id := by
    apply b.dualBasis.ext
    intro i
    apply b.ext
    intro j
    simpa only [LinearMap.comp_apply, τ, Module.Basis.constr_basis, φ,
      LinearMap.dualMap_apply, Submodule.coe_subtype, LinearMap.id_apply,
      Module.Basis.dualBasis_apply_self]
      using hcrossg i j
  have htau (z : Module.Dual K E) : φ (τ z) = z := LinearMap.congr_fun hτ z
  have hzero : β.compl₁₂ τ τ = 0 := by
    apply b.dualBasis.ext
    intro i
    apply b.dualBasis.ext
    intro j
    simpa only [LinearMap.compl₁₂_apply, τ, Module.Basis.constr_basis, LinearMap.zero_apply]
      using hgg i j
  have hiso : ∀ x y : τ.range, β x y = 0 := by
    intro x y
    obtain ⟨u, hu⟩ := x.property
    obtain ⟨v, hv⟩ := y.property
    rw [← hu, ← hv]
    simpa only [LinearMap.compl₁₂_apply, LinearMap.zero_apply] using
      congrArg (fun γ : LinearMap.BilinForm K (Module.Dual K E) => γ u v) hzero
  have hdisjoint : Disjoint E τ.range := by
    apply Submodule.disjoint_def.mpr
    intro x hx hy
    obtain ⟨z, rfl⟩ := hy
    have hxker : τ z ∈ φ.ker := by simpa only [hker] using hx
    have hz : z = 0 := (htau z).symm.trans (LinearMap.mem_ker.mp hxker)
    rw [hz, map_zero]
  have hcodisjoint : Codisjoint E τ.range := by
    apply codisjoint_iff.mpr
    apply eq_top_iff.mpr
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x - τ (φ x), ?_, τ (φ x), ⟨φ x, rfl⟩, sub_add_cancel _ _⟩
    have hxker : x - τ (φ x) ∈ φ.ker := by
      rw [LinearMap.mem_ker, map_sub, htau, sub_self]
    simpa only [hker] using hxker
  have hcompl : IsCompl E τ.range := ⟨hdisjoint, hcodisjoint⟩
  exact ⟨τ.range, hiso, hcompl⟩

end ArtinPrimitiveRoots.Proofs.a1_bdata_sol
