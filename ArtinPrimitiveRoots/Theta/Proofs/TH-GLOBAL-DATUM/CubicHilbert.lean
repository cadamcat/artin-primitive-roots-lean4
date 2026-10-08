import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».CubicQuotient

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- The quotient map to local multiplicative cube classes. -/
def localCubeMap (v : FinPlace F) : (v.adicCompletion F)ˣ →* LocalCubeQuotient v :=
  QuotientGroup.mk' (powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range

/-- The descended torus cocycle and its trivial restriction to an isotropic subgroup. -/
structure CubeHilbertData (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : Subgroup (v.adicCompletion F)ˣ) where
  c : LocalCubeQuotient v →* LocalCubeQuotient v →* ℂˣ
  c_mk : ∀ x y : (v.adicCompletion F)ˣ,
    c (localCubeMap v x) (localCubeMap v y) = (muThree D (H.hilb v x y) : ℂˣ)
  c_isotropic : ∀ x ∈ L.map (localCubeMap v), ∀ y ∈ L.map (localCubeMap v), c x y = 1

set_option maxHeartbeats 600000 in
/-- Descend the cubic Hilbert bicharacter in both arguments and identify its isotropic restriction. -/
theorem exists_cubeHilbertData (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : Subgroup (v.adicCompletion F)ˣ)
    (hiso : ∀ x ∈ L, ∀ y ∈ L, torusPairing D H v x y = 1) :
    Nonempty (CubeHilbertData D H v L) := by
  classical
  let K := (v.adicCompletion F)ˣ
  let Q := LocalCubeQuotient v
  let C := (powMonoidHom 3 : K →* K).range
  let μ : rootsOfUnity 6 F →* ℂˣ := {
    toFun := fun ζ => (muThree D ζ : ℂˣ)
    map_one' := by
      apply Units.ext
      simp [muThree]
    map_mul' := by
      intro ζ ξ
      apply Units.ext
      simp [muThree, map_mul, mul_pow]
  }
  have h_one_left (y : K) : H.hilb v 1 y = 1 :=
    H.sixth_power v 1 y ⟨1, by simp⟩
  have h_one_right (x : K) : H.hilb v x 1 = 1 := by
    have h := H.skew v x 1
    rw [h_one_left] at h
    simpa using h
  let c0 : K →* K →* ℂˣ := {
    toFun := fun x => {
      toFun := fun y => μ (H.hilb v x y)
      map_one' := by rw [h_one_right, map_one]
      map_mul' := by intro y z; rw [H.mul_right, map_mul]
    }
    map_one' := by
      apply MonoidHom.ext
      intro y
      change μ (H.hilb v 1 y) = 1
      rw [h_one_left, map_one]
    map_mul' := by
      intro x z
      apply MonoidHom.ext
      intro y
      change μ (H.hilb v (x * z) y) = μ (H.hilb v x y) * μ (H.hilb v z y)
      rw [H.mul_left, map_mul]
  }
  have h_cube (x y : K) : c0 x y ^ 3 = 1 := by
    exact (muThree D (H.hilb v x y)).property
  have h_right (x : K) : C ≤ (c0 x).ker := by
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    change c0 x (t ^ 3) = 1
    rw [map_pow]
    exact h_cube x t
  let cR : K →* Q →* ℂˣ := {
    toFun := fun x => QuotientGroup.lift C (c0 x) (h_right x)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      change c0 1 y = 1
      exact MonoidHom.map_one₂ c0 y
    map_mul' := by
      intro x z
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      change c0 (x * z) y = c0 x y * c0 z y
      exact MonoidHom.map_mul₂ c0 x z y
  }
  have hR_mk (x y : K) : cR x (localCubeMap v y) = c0 x y := rfl
  have hπ : Function.Surjective (localCubeMap v) := QuotientGroup.mk'_surjective _
  have h_left : C ≤ cR.ker := by
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    apply MonoidHom.mem_ker.mpr
    apply MonoidHom.ext
    intro q
    obtain ⟨y, hy⟩ := hπ q
    rw [← hy, MonoidHom.one_apply, hR_mk]
    change c0.flip y (t ^ 3) = 1
    rw [map_pow]
    exact h_cube t y
  let c : Q →* Q →* ℂˣ := QuotientGroup.lift C cR h_left
  have h_mk (x y : K) : c (localCubeMap v x) (localCubeMap v y) =
      (muThree D (H.hilb v x y) : ℂˣ) := by
    change (QuotientGroup.lift C cR h_left (QuotientGroup.mk x)) (localCubeMap v y) = _
    rw [QuotientGroup.lift_mk', hR_mk]
    rfl
  have h_iso (x : K) (hx : x ∈ L) (y : K) (hy : y ∈ L) : c0 x y = 1 := by
    have hcomm := congrArg (fun ζ : rootsOfUnity 3 ℂ => (ζ : ℂˣ)) (hiso x hx y hy)
    change c0 x y * (c0 y x)⁻¹ = 1 at hcomm
    have hsym := congrArg (fun z : ℂˣ => z * c0 y x) hcomm
    simp only [mul_assoc, inv_mul_cancel, mul_one, one_mul] at hsym
    have hskew : c0 x y * c0 y x = 1 := by
      change μ (H.hilb v x y) * μ (H.hilb v y x) = 1
      rw [← map_mul, H.skew, map_one]
    have hsq : c0 x y ^ 2 = 1 := by
      simpa only [← hsym, pow_two] using hskew
    calc
      c0 x y = c0 x y ^ 2 * c0 x y := by rw [hsq, one_mul]
      _ = c0 x y ^ 3 := (pow_succ (c0 x y) 2).symm
      _ = 1 := h_cube x y
  refine ⟨{ c := c, c_mk := h_mk, c_isotropic := ?_ }⟩
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
  rw [h_mk]
  exact h_iso x hx y hy

end ArtinPrimitiveRoots.A1.Theta
