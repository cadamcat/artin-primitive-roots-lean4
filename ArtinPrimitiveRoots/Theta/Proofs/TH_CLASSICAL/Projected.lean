import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Determinant
import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.StrongApprox

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}

/-- Local projective components admit matrix lifts integral and determinant-unit almost everywhere. -/
theorem th_classical_restricted_matrix_lifts (P : CoverPackage D S H A) (r : P.RP) :
    ∃ (T : Finset (FinPlace F)) (g : ∀ v : FinPlace F, GL (Fin 2) (v.adicCompletion F)),
      S.Sf ⊆ T ∧
      (∀ v, (QuotientGroup.mk (g v) : PGL2 (v.adicCompletion F)) =
        (P.loc v).pr (P.compF v r)) ∧
      ∀ v ∉ T,
        (∀ i j, (g v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        ((g v)⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        Valued.v (g v).val.det = 1 := by
  classical
  let E : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v r ∉ (P.tame v hv).Kmax}
  have hE : E.Finite := P.comp_restricted r
  let T : Finset (FinPlace F) := S.Sf ∪ hE.toFinset
  have hST : S.Sf ⊆ T := Finset.subset_union_left
  have hex (v : FinPlace F) : ∃ g : GL (Fin 2) (v.adicCompletion F),
      (QuotientGroup.mk g : PGL2 (v.adicCompletion F)) = (P.loc v).pr (P.compF v r) ∧
      (v ∉ T →
        (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (g⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F) := by
    by_cases hv : v ∈ T
    · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((P.loc v).pr (P.compF v r))
      exact ⟨g, hg, fun hv' => (hv' hv).elim⟩
    · have hvS : v ∉ S.Sf := fun h => hv (hST h)
      have htame : P.compF v r ∈ (P.tame v hvS).Kmax := by
        by_contra hbad
        exact hv (Finset.mem_union_right S.Sf (hE.mem_toFinset.mpr ⟨hvS, hbad⟩))
      have himage : (P.loc v).pr (P.compF v r) ∈
          (P.loc v).pr '' ((P.tame v hvS).Kmax : Set (P.loc v).L) :=
        ⟨P.compF v r, htame, rfl⟩
      rw [(P.tame v hvS).image] at himage
      obtain ⟨g, hgint, hginv, hg⟩ := himage
      exact ⟨g, hg, fun _ => ⟨hgint, hginv⟩⟩
  choose g hg hgin using hex
  refine ⟨T, g, hST, hg, ?_⟩
  intro v hv
  obtain ⟨hints, hinv⟩ := hgin v hv
  refine ⟨hints, hinv, ?_⟩
  have hdet : (g v).val.det ∈ v.adicCompletionIntegers F := by
    rw [Matrix.det_fin_two]
    exact (v.adicCompletionIntegers F).toSubring.sub_mem
      ((v.adicCompletionIntegers F).toSubring.mul_mem (hints 0 0) (hints 1 1))
      ((v.adicCompletionIntegers F).toSubring.mul_mem (hints 0 1) (hints 1 0))
  have hd : Valued.v (g v).val.det ≤ 1 :=
    (by simpa only [HeightOneSpectrum.mem_adicCompletionIntegers] using hdet)
  have hi : Valued.v ((g v)⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ≤ 1 :=
    (by simpa only [HeightOneSpectrum.mem_adicCompletionIntegers] using hinv)
  have hprod : (g v).val.det * ((g v)⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = 1 :=
    (Matrix.GeneralLinearGroup.det (g v)).val_inv
  apply le_antisymm hd
  calc
    1 = Valued.v (g v).val.det *
        Valued.v ((g v)⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det := by
      rw [← map_mul, hprod, map_one]
    _ ≤ Valued.v (g v).val.det * 1 := mul_le_mul_of_nonneg_left hi zero_le
    _ = Valued.v (g v).val.det := mul_one _

end ArtinPrimitiveRoots.A1.Theta
