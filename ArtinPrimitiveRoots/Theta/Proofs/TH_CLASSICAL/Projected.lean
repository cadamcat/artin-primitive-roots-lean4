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

/-- A rational diagonal makes all exterior local determinants units, retaining integral lifts almost everywhere. -/
theorem th_classical_normalized_matrix_lifts (P : CoverPackage D S H A) (r : P.RP) :
    ∃ (γ : GL (Fin 2) F) (T : Finset (FinPlace F))
      (g : ∀ v : FinPlace F, GL (Fin 2) (v.adicCompletion F)),
      S.Sf ⊆ T ∧
      (∀ v, (QuotientGroup.mk (g v) : PGL2 (v.adicCompletion F)) =
        (P.loc v).pr (P.compF v (P.ratRP γ * r))) ∧
      (∀ v ∉ S.Sf, Valued.v (g v).val.det = 1) ∧
      ∀ v ∉ T, ∀ i j,
        (g v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
  classical
  obtain ⟨T, g, hST, hg, hgin⟩ := th_classical_restricted_matrix_lifts P r
  let f (v : FinPlace F) : ℤ :=
    if v ∈ S.Sf then 0 else WithZero.log (Valued.v (g v).val.det)
  have hf (v : FinPlace F) (hfv : f v ≠ 0) : v ∈ T := by
    by_contra hv
    have hvS : v ∉ S.Sf := fun h => hv (hST h)
    exact hfv (by simp only [f, if_neg hvS, (hgin v hv).2.2, WithZero.log_one])
  let e : FinPlace F →₀ ℤ := Finsupp.onFinset T f hf
  have heS (v : FinPlace F) (hv : v ∈ S.Sf) : e v = 0 := by simp [e, f, hv]
  obtain ⟨α, hα⟩ := th_classical_exterior_divisor_principal D S H e heS
  let γ : GL (Fin 2) F := diagM F α
  let g' (v : FinPlace F) : GL (Fin 2) (v.adicCompletion F) :=
    Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ * g v
  have hdiag (v : FinPlace F) :
      (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      !![algebraMap F (v.adicCompletion F) (α : F), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ, diagM, Matrix.GeneralLinearGroup.map]
  have hdet (v : FinPlace F) : (g' v).val.det =
      algebraMap F (v.adicCompletion F) (α : F) * (g v).val.det := by
    dsimp only [g']
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdiag]
    simp [Matrix.det_fin_two]
  have hαloc (v : FinPlace F) (hv : v ∉ S.Sf) :
      Valued.v (algebraMap F (v.adicCompletion F) (α : F)) = WithZero.exp (-(e v)) := by
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation'] using hα v hv
  refine ⟨γ, T, g', hST, ?_, ?_, ?_⟩
  · intro v
    simp only [g', map_mul, P.compF_ratRP, (P.loc v).sec_pr, QuotientGroup.mk_mul, hg v]
  · intro v hv
    have he : e v = WithZero.log (Valued.v (g v).val.det) := by simp [e, f, hv]
    have hd0 : Valued.v (g v).val.det ≠ 0 := by
      simpa only [ne_eq, Valuation.zero_iff] using Matrix.GeneralLinearGroup.det_ne_zero (g v)
    rw [hdet, map_mul, hαloc v hv, he, WithZero.exp_neg, WithZero.exp_log hd0]
    exact inv_mul_cancel₀ hd0
  · intro v hv i j
    have hvS : v ∉ S.Sf := fun h => hv (hST h)
    have he0 : e v = 0 := by
      simp only [e, Finsupp.onFinset_apply, f, if_neg hvS,
        (hgin v hv).2.2, WithZero.log_one]
    have haint : algebraMap F (v.adicCompletion F) (α : F) ∈ v.adicCompletionIntegers F := by
      change Valued.v (algebraMap F (v.adicCompletion F) (α : F)) ≤ 1
      rw [hαloc v hvS, he0, neg_zero, WithZero.exp_zero]
    change (g' v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ _
    dsimp only [g']
    rw [Matrix.GeneralLinearGroup.coe_mul, hdiag]
    fin_cases i
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using
        (v.adicCompletionIntegers F).toSubring.mul_mem haint ((hgin v hv).1 0 j)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using (hgin v hv).1 1 j

end ArtinPrimitiveRoots.A1.Theta
