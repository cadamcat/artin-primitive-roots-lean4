import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Geometry

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Pad-divisible positions embed injectively in determinant-preserving lattice coordinates. -/
theorem pad_lattice_coordinate_embedding (z : ℤ × ℤ) (D : ℕ) (hD : 0 < D)
    (hz : Int.gcd z.1 z.2 = 1) (a b c d : ℤ) (hmat : a*d-b*c = 1)
    (T : Finset (ℤ × ℤ)) (hdiv : ∀ u ∈ T, (D : ℤ) ∣ det2 z u) :
    let Φ : (ℤ × ℤ) → (ℤ × ℤ) := fun u =>
      (d*det2 u (complementVec z)-b*(det2 z u/(D : ℤ)),
        a*(det2 z u/(D : ℤ))-c*det2 u (complementVec z))
    Set.InjOn Φ (T : Set (ℤ × ℤ)) ∧
      ∀ u ∈ T, ∀ v ∈ T, det2 u v/(D : ℤ) = det2 (Φ u) (Φ v) := by
  let H : (ℤ × ℤ) → ℤ := fun u => det2 u (complementVec z)
  let L : (ℤ × ℤ) → ℤ := fun u => det2 z u/(D : ℤ)
  let Φ : (ℤ × ℤ) → (ℤ × ℤ) := fun u => (d*H u-b*L u, a*L u-c*H u)
  change Set.InjOn Φ (T : Set (ℤ × ℤ)) ∧
    ∀ u ∈ T, ∀ v ∈ T, det2 u v/(D : ℤ) = det2 (Φ u) (Φ v)
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcomp : det2 z (complementVec z) = 1 := by
    have hBez := Int.gcd_eq_gcd_ab z.1 z.2
    rw [hz] at hBez
    simpa [det2, complementVec, sub_neg_eq_add] using hBez.symm
  have hrepr (u : ℤ × ℤ) (hu : u ∈ T) :
      u = (H u*z.1+(D : ℤ)*L u*(complementVec z).1,
        H u*z.2+(D : ℤ)*L u*(complementVec z).2) := by
    have hdl : (D : ℤ)*L u = det2 z u := Int.mul_ediv_cancel' (hdiv u hu)
    rw [hdl]
    exact pd4c_primitive_basis_coordinates z u hz
  have hbackH (u : ℤ × ℤ) : H u = a*(Φ u).1+b*(Φ u).2 := by
    calc
      _ = (a*d-b*c)*H u := by rw [hmat, one_mul]
      _ = _ := by dsimp only [Φ]; ring
  have hbackL (u : ℤ × ℤ) : L u = c*(Φ u).1+d*(Φ u).2 := by
    calc
      _ = (a*d-b*c)*L u := by rw [hmat, one_mul]
      _ = _ := by dsimp only [Φ]; ring
  have hPhi (u v : ℤ × ℤ) : det2 (Φ u) (Φ v) = H u*L v-L u*H v := by
    calc
      _ = (a*d-b*c)*(H u*L v-L u*H v) := by dsimp only [Φ, det2]; ring
      _ = _ := by rw [hmat, one_mul]
  have hphysical (u : ℤ × ℤ) (hu : u ∈ T) (v : ℤ × ℤ) (hv : v ∈ T) :
      det2 u v = (D : ℤ)*(H u*L v-L u*H v) := by
    calc
      _ = det2 (H u*z.1+(D : ℤ)*L u*(complementVec z).1,
            H u*z.2+(D : ℤ)*L u*(complementVec z).2)
          (H v*z.1+(D : ℤ)*L v*(complementVec z).1,
            H v*z.2+(D : ℤ)*L v*(complementVec z).2) :=
        congrArg₂ det2 (hrepr u hu) (hrepr v hv)
      _ = (D : ℤ)*(H u*L v-L u*H v)*det2 z (complementVec z) := by
        dsimp only [det2]
        ring
      _ = _ := by rw [hcomp, mul_one]
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hHeq : H u = H v := by rw [hbackH u, hbackH v, huv]
    have hLeq : L u = L v := by rw [hbackL u, hbackL v, huv]
    calc
      u = (H u*z.1+(D : ℤ)*L u*(complementVec z).1,
        H u*z.2+(D : ℤ)*L u*(complementVec z).2) := hrepr u hu
      _ = (H v*z.1+(D : ℤ)*L v*(complementVec z).1,
        H v*z.2+(D : ℤ)*L v*(complementVec z).2) := by rw [hHeq, hLeq]
      _ = v := (hrepr v hv).symm
  · intro u hu v hv
    rw [hphysical u hu v hv, ← hPhi u v]
    exact Int.mul_ediv_cancel_left _ hD0

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
