import ArtinPrimitiveRoots.Theta.Proofs.«TH-RDERIV».RootIntegral

set_option autoImplicit false

open NumberField IsDedekindDomain Module MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_torusf

open ArtinPrimitiveRoots.A1 ArtinPrimitiveRoots.A1.Theta

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

theorem rderiv_torusCoeff (P : CoverPackage D S H A)
    (m : InfinitePlace F → ℤ) (Ψ : P.tc.G → ℂ)
    (hΨ : JointRootSmooth P Ψ) :
    ∀ g Pd ν, Bornology.IsBounded Pd → MeasurableSet Pd →
      torusCoeff P (thetaFamilyDeriv P m Ψ) g Pd ν =
        thetaFamilyDeriv P m (fun h => torusCoeff P Ψ h Pd ν) g := by
  classical
  intro g Pd ν hb hm
  have hfold (ws : List (InfinitePlace F)) :
      JointRootSmooth P (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ∧
        ∀ h, torusCoeff P (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) h Pd ν =
          ws.foldr (fun w acc => thetaRootStep w (m w) acc)
            (fun h => torusCoeff P Ψ h Pd ν) h := by
    induction ws with
    | nil => exact ⟨hΨ, fun _ => rfl⟩
    | cons w ws ih =>
        refine ⟨thetaRootStep_jointRootSmooth w (m w) _ ih.1, ?_⟩
        intro h
        change torusCoeff P
          (thetaRootStep w (m w) (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ))
          h Pd ν =
            thetaRootStep w (m w)
              (ws.foldr (fun w acc => thetaRootStep w (m w) acc)
                (fun h => torusCoeff P Ψ h Pd ν)) h
        rw [root_step_torusCoeff P w (m w)
          (ws.foldr (fun w acc => thetaRootStep w (m w) acc) Ψ) ih.1 h Pd ν hb hm]
        rw [funext ih.2]
  change torusCoeff P
      (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
        (fun w acc => thetaRootStep w (m w) acc) Ψ) g Pd ν =
    (((Finset.univ : Finset (InfinitePlace F)).toList).foldr
      (fun w acc => thetaRootStep w (m w) acc)
        (fun h => torusCoeff P Ψ h Pd ν)) g
  exact (hfold (Finset.univ : Finset (InfinitePlace F)).toList).2 g

end ArtinPrimitiveRoots.Proofs.thsol_torusf
