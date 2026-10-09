import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Rational automorphy and fixation by the finite ideal translations
imply periodicity along the left archimedean upper-root orbit. -/
theorem automorphic_ideal_period (P : CoverPackage D S H A)
    (Ψ : P.tc.G → ℂ) (g : P.tc.G)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (hAut : ∀ γ h, Ψ (P.tc.rat γ * h) = Ψ h)
    (hfix : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ h,
      Ψ (h * (g⁻¹ * nFin P ξ * g)) = Ψ h) :
    ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F), ∀ x : InfinitePlace F → ℂ,
      Ψ (nInf P (x + infEmbA ξ) * g) = Ψ (nInf P x * g) := by
  intro ξ hξ x
  have hneg : (-ξ : F) ∈ (𝔞 : Submodule (𝓞 F) F) :=
    (𝔞 : Submodule (𝓞 F) F).neg_mem hξ
  let k := g⁻¹ * nFin P (-ξ) * g
  have hthetaK : ∀ y, Ψ (y * k) = Ψ y :=
    fun y => hfix (-ξ) hneg y
  have hupper : upperGL ξ * upperGL (-ξ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperGL, Matrix.mul_apply]
  have hrat : P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ)) = 1 := by
    rw [← P.tc.rat.map_mul, hupper, map_one]
  have hfactor : nInf P (infEmbA ξ) = P.tc.rat (upperGL ξ) * nFin P (-ξ) := by
    have hnegInf : -infEmbA (-ξ) = infEmbA ξ := by simp
    calc
      nInf P (infEmbA ξ) = 1 * nInf P (infEmbA ξ) := by simp
      _ = (P.tc.rat (upperGL ξ) * P.tc.rat (upperGL (-ξ))) *
          nInf P (infEmbA ξ) := by rw [hrat]
      _ = P.tc.rat (upperGL ξ) *
          (P.tc.rat (upperGL (-ξ)) * nInf P (infEmbA ξ)) := by rw [mul_assoc]
      _ = P.tc.rat (upperGL ξ) * nFin P (-ξ) := by
        dsimp only [nFin]
        rw [hnegInf]
  have hadd : nInf P (x + infEmbA ξ) = nInf P (infEmbA ξ) * nInf P x := by
    have hEta :
        ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + infEmbA ξ) =
          ((0 : ∀ v : S.Sf, v.1.adicCompletion F), infEmbA ξ) +
            ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x) := by
      ext <;> simp [add_comm]
    change P.tc.nS (Multiplicative.ofAdd
      ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x + infEmbA ξ)) = _
    rw [hEta, ofAdd_add, map_mul]
    rfl
  have hcommFin : nFin P (-ξ) * nInf P x = nInf P x * nFin P (-ξ) := by
    let η : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F), -infEmbA (-ξ))
    obtain ⟨xA, hqA, _, hcompA⟩ := P.nS_components η
    let xFin := P.ratRP (upperGL (-ξ)) * xA
    have hqFin : P.q xFin = nFin P (-ξ) := by
      change P.q (P.ratRP (upperGL (-ξ)) * xA) = nFin P (-ξ)
      rw [map_mul, P.q_ratRP, hqA]
      rfl
    have hcompFinC (w : InfinitePlace F) : P.compC w xFin = 1 := by
      change P.compC w (P.ratRP (upperGL (-ξ)) * xA) = 1
      rw [map_mul, P.compC_ratRP, hcompA]
      have hmap : Matrix.GeneralLinearGroup.map w.embedding (upperGL (-ξ)) =
          upperM ℂ (w.embedding (-ξ)) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [upperGL, upperM]
      rw [hmap]
      change QuotientGroup.mk (upperM ℂ (w.embedding (-ξ))) *
        QuotientGroup.mk (upperM ℂ (-w.embedding (-ξ))) = 1
      rw [← QuotientGroup.mk_mul]
      have hmul : upperM ℂ (w.embedding (-ξ)) * upperM ℂ (-w.embedding (-ξ)) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [upperM, Matrix.mul_apply]
      rw [hmul]
      simp
    let u : S.FS := ((0 : ∀ v : S.Sf, v.1.adicCompletion F), x)
    obtain ⟨xInf, hqInf, hcompInfF, hcompInfC⟩ := P.nS_components u
    have hComm : xFin * xInf = xInf * xFin := by
      apply P.comp_ext
      · intro v
        simp [((P.compF v).map_mul), hcompInfF, u]
      · intro w
        simp [((P.compC w).map_mul), hcompFinC]
    calc
      nFin P (-ξ) * nInf P x = P.q xFin * P.q xInf := by
        rw [hqFin, hqInf]
        rfl
      _ = P.q (xFin * xInf) := (P.q.map_mul _ _).symm
      _ = P.q (xInf * xFin) := congrArg P.q hComm
      _ = P.q xInf * P.q xFin := P.q.map_mul _ _
      _ = nInf P x * nFin P (-ξ) := by
        rw [hqFin, hqInf]
        rfl
  have hbase : nInf P (x + infEmbA ξ) * g =
      P.tc.rat (upperGL ξ) * (nInf P x * g * k) := by
    calc
      nInf P (x + infEmbA ξ) * g =
          (nInf P (infEmbA ξ) * nInf P x) * g := by rw [hadd]
      _ = (P.tc.rat (upperGL ξ) * nFin P (-ξ) * nInf P x) * g := by rw [hfactor]
      _ = (P.tc.rat (upperGL ξ) * (nFin P (-ξ) * nInf P x)) * g := by
        exact congrArg (fun z => z * g)
          (mul_assoc (P.tc.rat (upperGL ξ)) (nFin P (-ξ)) (nInf P x))
      _ = (P.tc.rat (upperGL ξ) * (nInf P x * nFin P (-ξ))) * g := by rw [hcommFin]
      _ = P.tc.rat (upperGL ξ) * (nInf P x * g * k) := by simp [k, mul_assoc]
  calc
    Ψ (nInf P (x + infEmbA ξ) * g) =
        Ψ (P.tc.rat (upperGL ξ) * (nInf P x * g * k)) := congrArg Ψ hbase
    _ = Ψ (nInf P x * g * k) := hAut _ _
    _ = Ψ (nInf P x * g) := hthetaK _

end ArtinPrimitiveRoots.A1.Theta
