import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem nFin_has_finite_only_lift (P : CoverPackage D S H A) (ξ : F) :
    ∃ x : P.RP, P.q x = nFin P ξ ∧
      (∀ v, P.compF v x = (P.loc v).n
        (Multiplicative.ofAdd (algebraMap F (v.adicCompletion F) ξ))) ∧
      ∀ w, P.compC w x = 1 := by
  classical
  let η : S.FS :=
    ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -infEmbA ξ)
  obtain ⟨xInf, hqInf, hcfInf, hccInf⟩ := P.nS_components η
  let x := P.ratRP (upperGL ξ) * xInf
  refine ⟨x, ?_, ?_, ?_⟩
  · change P.q (P.ratRP (upperGL ξ) * xInf) = nFin P ξ
    rw [map_mul, P.q_ratRP, hqInf]
    rfl
  · intro v
    change P.compF v (P.ratRP (upperGL ξ) * xInf) = _
    rw [map_mul, P.compF_ratRP, hcfInf]
    have hmap : Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (upperGL ξ) = upperM (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ξ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    rw [hmap]
    simp [η, FinLocalCover.sec_n]
  · intro w
    change P.compC w (P.ratRP (upperGL ξ) * xInf) = 1
    rw [map_mul, P.compC_ratRP, hccInf]
    have hmap : Matrix.GeneralLinearGroup.map w.embedding (upperGL ξ) =
        upperM ℂ (w.embedding ξ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
    rw [hmap]
    change QuotientGroup.mk (upperM ℂ (w.embedding ξ)) *
      QuotientGroup.mk (upperM ℂ (-w.embedding ξ)) = 1
    rw [← QuotientGroup.mk_mul]
    have hmul : upperM ℂ (w.embedding ξ) * upperM ℂ (-w.embedding ξ) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
    simp [hmul]

theorem finite_only_commutes_with_nInf (P : CoverPackage D S H A) (x : P.RP)
    (hC : ∀ w, P.compC w x = 1) (z : InfinitePlace F → ℂ) :
    P.q x * nInf P z = nInf P z * P.q x := by
  classical
  let η : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F), z)
  obtain ⟨xInf, hqInf, hcfInf, hccInf⟩ := P.nS_components η
  have hEq : x * xInf = xInf * x := by
    apply P.comp_ext
    · intro v
      simp [((P.compF v).map_mul), hcfInf, η]
    · intro w
      simp [((P.compC w).map_mul), hC, hccInf]
  calc
    P.q x * nInf P z = P.q x * P.q xInf := by
      change P.q x * P.tc.nS (Multiplicative.ofAdd η) = _
      exact (congrArg (fun y => P.q x * y) hqInf).symm
    _ = P.q (x * xInf) := (P.q.map_mul x xInf).symm
    _ = P.q (xInf * x) := congrArg P.q hEq
    _ = P.q xInf * P.q x := P.q.map_mul xInf x
    _ = nInf P z * P.q x := by
      change P.q xInf * P.q x = P.tc.nS (Multiplicative.ofAdd η) * P.q x
      exact congrArg (fun y => y * P.q x) hqInf

end ArtinPrimitiveRoots.A1.Theta
