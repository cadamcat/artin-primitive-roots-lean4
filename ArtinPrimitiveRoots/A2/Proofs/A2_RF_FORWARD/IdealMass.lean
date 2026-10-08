import ArtinPrimitiveRoots.A2.Proofs.«A2-BRIDGES».COUNT

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A2

theorem spherical_mass_summable {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    (S : SData F CE condη) (σ : ℝ) (hσ : 1 / 2 < σ) :
    Summable (fun p : S.SqfExtIdeal × S.ExtIdeal =>
      idealNorm p.1.1 ^ (-1 / 2 - σ) * idealNorm p.2.1 ^ (-1 - 3 * σ)) := by
  classical
  let a : S.ExtIdeal → ℝ := fun I => idealNorm I.1 ^ (-1 / 2 - σ)
  let b : S.ExtIdeal → ℝ := fun I => idealNorm I.1 ^ (-1 - 3 * σ)
  have haBase := a2_bridge_COUNT_summable S (σ + 1 / 2) (by linarith)
  have hbBase := a2_bridge_COUNT_summable S (3 * σ + 1) (by linarith)
  have ha : Summable a := by
    apply haBase.congr
    intro I
    dsimp [a, idealNorm]
    congr 1
    ring
  have hb : Summable b := by
    apply hbBase.congr
    intro I
    dsimp [b, idealNorm]
    congr 1
    ring
  have ha_nonneg : ∀ I, 0 ≤ a I := by
    intro I
    change 0 ≤ Real.rpow (Ideal.absNorm I.1 : ℝ) _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hb_nonneg : ∀ I, 0 ≤ b I := by
    intro I
    change 0 ≤ Real.rpow (Ideal.absNorm I.1 : ℝ) _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  let incl : S.SqfExtIdeal → S.ExtIdeal := fun I => ⟨I.1, I.2.1⟩
  let aSqf : S.SqfExtIdeal → ℝ := fun I => a (incl I)
  have haSqf : Summable aSqf := by
    let e : S.SqfExtIdeal ≃ {I : S.ExtIdeal // Squarefree I.1} :=
      { toFun := fun I => ⟨incl I, I.2.2⟩
        invFun := fun I => ⟨I.1.1, ⟨I.1.2, I.2⟩⟩
        left_inv := by intro I; apply Subtype.ext; rfl
        right_inv := by intro I; apply Subtype.ext; apply Subtype.ext; rfl }
    have hsub : Summable (fun I : {I : S.ExtIdeal // Squarefree I.1} => a I.1) :=
      ha.subtype (fun I : S.ExtIdeal => Squarefree I.1)
    have heq : aSqf = fun I : S.SqfExtIdeal => a (e I).1 := by
      funext I
      rfl
    rw [heq]
    exact (Equiv.summable_iff e).mpr hsub
  exact haSqf.mul_of_nonneg hb (fun I => ha_nonneg (incl I)) hb_nonneg

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
