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

/-- The prescribed finite level, before applying the global central quotient. -/
def th_classical_finiteLevel (P : CoverPackage D S H A) (T0 : Finset (FinPlace F))
    (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ) (k : P.RP) : Prop :=
  (∀ w, P.compC w k = 1) ∧
    (∀ v ∈ T0, P.compF v k ∈ (P.loc v).Kc (m v)) ∧
    ∀ v (hv : v ∉ T0), P.compF v k ∈ (P.tame v (fun h => hv (hT0 h))).Kmax

set_option maxHeartbeats 400000 in
/-- Finite-adelic reduction after forgetting the central cubic phases. -/
theorem th_classical_projected_finite_components (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) :
    ∃ J : Finset P.RP, (∀ j ∈ J, ∀ w, P.compC w j = 1) ∧
      ∀ r : P.RP, ∃ γ : GL (Fin 2) F, ∃ j ∈ J, ∃ k : P.RP,
        th_classical_finiteLevel P T0 hT0 m k ∧
          ∀ v, (P.loc v).pr (P.compF v (P.ratRP γ * r)) =
            (P.loc v).pr (P.compF v (j * k)) := by
  classical
  choose R hR using fun v : T0 => th_classical_local_determinant_reps D H v.1
    (P.loc v.1) (m v.1) (hm v.1 v.2)
  let Family := ∀ v : T0, {d : (v.1.adicCompletion F)ˣ // d ∈ R v}
  let jf (f : Family) (v : FinPlace F) : (P.loc v).L :=
    if hv : v ∈ T0 then (P.loc v).a (f ⟨v, hv⟩).val else 1
  have hjres (f : Family) : Set.Finite
      {v | ∃ hv : v ∉ S.Sf, jf f v ∉ (P.tame v hv).Kmax} := by
    apply T0.finite_toSet.subset
    intro v hv
    change v ∈ T0
    by_contra hv0
    obtain ⟨hvS, hbad⟩ := hv
    exact hbad (by simpa only [jf, dif_neg hv0] using (P.tame v hvS).Kmax.one_mem)
  choose jOf hjF hjC using fun f : Family => P.comp_surj (jf f) (fun _ => 1) (hjres f)
  let J : Finset P.RP := Finset.univ.image jOf
  refine ⟨J, ?_, ?_⟩
  · intro j hj w
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hj
    exact hjC f w
  · intro r
    obtain ⟨γ0, T, g, hST, hg, hgd, hgi⟩ := th_classical_normalized_matrix_lifts P r
    choose d hd c b hdet hb using fun v : T0 => hR v (Matrix.GeneralLinearGroup.det (g v.1))
    let f : Family := fun v => ⟨d v, hd v⟩
    let j : P.RP := jOf f
    let dF (v : FinPlace F) : (v.adicCompletion F)ˣ :=
      if hv : v ∈ T0 then d ⟨v, hv⟩ else 1
    let cF (v : FinPlace F) : (v.adicCompletion F)ˣ :=
      if hv : v ∈ T0 then c ⟨v, hv⟩ else 1
    let bF (v : FinPlace F) : (v.adicCompletion F)ˣ :=
      if hv : v ∈ T0 then b ⟨v, hv⟩ else Matrix.GeneralLinearGroup.det (g v)
    let K (v : FinPlace F) : Subgroup (P.loc v).L :=
      if hv : v ∈ T0 then (P.loc v).Kc (m v)
      else (P.tame v (fun h => hv (hT0 h))).Kmax
    have hKopen (v : FinPlace F) : IsOpen (K v : Set (P.loc v).L) := by
      dsimp only [K]
      split_ifs with hv
      · exact (P.loc v).Kc_open (m v) (hm v hv)
      · exact (P.tame v (fun h => hv (hT0 h))).open_
    have hbK (v : FinPlace F) : (P.loc v).a (bF v) ∈ K v := by
      by_cases hv : v ∈ T0
      · simpa only [K, bF, dif_pos hv] using hb ⟨v, hv⟩
      · have hvS : v ∉ S.Sf := fun h => hv (hT0 h)
        simp only [K, bF, dif_neg hv]
        apply (P.tame v hvS).a_mem
        · change Valued.v (g v).val.det ≤ 1
          exact (hgd v hvS).le
        · change Valued.v (((Matrix.GeneralLinearGroup.det (g v))⁻¹ :
            (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1
          simp only [Units.val_inv_eq_inv_val, map_inv₀]
          change (Valued.v (g v).val.det)⁻¹ ≤ 1
          rw [hgd v hvS, inv_one]
    have hdetF (v : FinPlace F) :
        Matrix.GeneralLinearGroup.det (g v) = dF v * cF v ^ 2 * bF v := by
      by_cases hv : v ∈ T0
      · simpa only [dF, cF, bF, dif_pos hv] using hdet ⟨v, hv⟩
      · simp only [dF, cF, bF, dif_neg hv, one_pow, one_mul]
    have hdiagdet (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
        Matrix.GeneralLinearGroup.det (diagM (v.adicCompletion F) u) = u := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.det, diagM, Matrix.det_fin_two]
    have hdiagone (v : FinPlace F) :
        (QuotientGroup.mk (diagM (v.adicCompletion F) 1) : PGL2 (v.adicCompletion F)) = 1 := by
      rw [← (P.loc v).pr_a, (P.loc v).a_one, map_one]
    have hjp (v : FinPlace F) : (P.loc v).pr (P.compF v j) =
        QuotientGroup.mk (diagM (v.adicCompletion F) (dF v)) := by
      rw [hjF f v]
      by_cases hv : v ∈ T0
      · simp only [jf, f, dF, dif_pos hv, (P.loc v).pr_a]
      · simp only [jf, dF, dif_neg hv, map_one, hdiagone]
    let s (v : FinPlace F) : GL (Fin 2) (v.adicCompletion F) :=
      diagM (v.adicCompletion F) (dF v) * diagM (v.adicCompletion F) (bF v) *
        Matrix.GeneralLinearGroup.scalar (Fin 2) (cF v) * (g v)⁻¹
    have hsdet (v : FinPlace F) : Matrix.GeneralLinearGroup.det (s v) = 1 := by
      simp only [s, map_mul, map_inv, hdiagdet, Matrix.GeneralLinearGroup.det_scalar,
        Fintype.card_fin, hdetF v]
      have hc : dF v * bF v * cF v ^ 2 = dF v * cF v ^ 2 * bF v := by ac_rfl
      rw [hc, mul_inv_cancel]
    let sSL (v : FinPlace F) : SL(2, v.adicCompletion F) :=
      ⟨(s v).val, by
        change ((Matrix.GeneralLinearGroup.det (s v) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) = 1
        rw [hsdet v, Units.val_one]⟩
    have hsGL (v : FinPlace F) : Matrix.SpecialLinearGroup.toGL (sSL v) = s v := by
      apply Units.ext
      rfl
    have hscalar (v : FinPlace F) (u : (v.adicCompletion F)ˣ) :
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) u) :
          PGL2 (v.adicCompletion F)) = 1 := Matrix.ProjGenLinGroup.mk_scalar u
    have hsp (v : FinPlace F) :
        (QuotientGroup.mk (s v) : PGL2 (v.adicCompletion F)) * QuotientGroup.mk (g v) =
          QuotientGroup.mk (diagM (v.adicCompletion F) (dF v)) *
            (P.loc v).pr ((P.loc v).a (bF v)) := by
      simp [s, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hscalar, (P.loc v).pr_a, mul_assoc]
    let rem (v : FinPlace F) (h : GL (Fin 2) (v.adicCompletion F)) : PGL2 (v.adicCompletion F) :=
      (QuotientGroup.mk (diagM (v.adicCompletion F) (dF v)))⁻¹ *
        QuotientGroup.mk h * QuotientGroup.mk (g v)
    let U (v : FinPlace F) : Set (GL (Fin 2) (v.adicCompletion F)) :=
      rem v ⁻¹' ((P.loc v).pr '' (K v : Set (P.loc v).L))
    have hUopen (v : FinPlace F) : IsOpen (U v) := by
      apply ((P.loc v).pr_open _ (hKopen v)).preimage
      have hmk : Continuous (fun h : GL (Fin 2) (v.adicCompletion F) =>
          (QuotientGroup.mk h : PGL2 (v.adicCompletion F))) := QuotientGroup.continuous_mk
      exact (continuous_const.mul hmk).mul continuous_const
    have hsU (v : FinPlace F) : Matrix.SpecialLinearGroup.toGL (sSL v) ∈ U v := by
      change rem v (Matrix.SpecialLinearGroup.toGL (sSL v)) ∈
        (P.loc v).pr '' (K v : Set (P.loc v).L)
      dsimp only [rem]
      rw [hsGL, mul_assoc, hsp, inv_mul_cancel_left]
      exact ⟨(P.loc v).a (bF v), hbK v, rfl⟩
    let E := T ∪ T0
    obtain ⟨δ, hδdet, hδint, hδU⟩ := th_classical_sl_finite_approx E
      (fun v => sSL v.1) (fun v => U v.1) (fun v => (hUopen v.1).mem_nhds (hsU v.1))
    let δv (v : FinPlace F) : GL (Fin 2) (v.adicCompletion F) :=
      Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) δ
    have hδvd (v : FinPlace F) : Matrix.GeneralLinearGroup.det (δv v) = 1 := by
      simp only [δv, Matrix.GeneralLinearGroup.map_det, hδdet, map_one]
    have hex (v : FinPlace F) : ∃ k : (P.loc v).L, k ∈ K v ∧ (P.loc v).pr k = rem v (δv v) := by
      by_cases hvE : v ∈ E
      · exact hδU ⟨v, hvE⟩
      · have hvT : v ∉ T := fun h => hvE (Finset.mem_union_left T0 h)
        have hv0 : v ∉ T0 := fun h => hvE (Finset.mem_union_right T h)
        have hvS : v ∉ S.Sf := fun h => hvT (hST h)
        let z : GL (Fin 2) (v.adicCompletion F) := δv v * g v
        have hδvi (i j : Fin 2) : (δv v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
            v.adicCompletionIntegers F := by
          change Valued.v (algebraMap F (v.adicCompletion F) ((δ : Matrix (Fin 2) (Fin 2) F) i j)) ≤ 1
          simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
            Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']
            using hδint v hvE i j
        have hzi (i j : Fin 2) : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
            v.adicCompletionIntegers F := by
          change ((δv v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) *
            (g v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) i j ∈ _
          simp only [Matrix.mul_apply, Fin.sum_univ_two]
          exact (v.adicCompletionIntegers F).toSubring.add_mem
            ((v.adicCompletionIntegers F).toSubring.mul_mem (hδvi i 0) (hgi v hvT 0 j))
            ((v.adicCompletionIntegers F).toSubring.mul_mem (hδvi i 1) (hgi v hvT 1 j))
        have hzval : Valued.v z.val.det = 1 := by
          change Valued.v (((Matrix.GeneralLinearGroup.det (z) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F)) = 1
          simp only [z, map_mul, hδvd, one_mul]
          exact hgd v hvS
        have hzinv : (z⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F := by
          change Valued.v (z⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ≤ 1
          have hprod := congrArg (Valued.v : v.adicCompletion F → WithZero (Multiplicative ℤ))
            (Matrix.GeneralLinearGroup.det z).val_inv
          change Valued.v (z.val.det * (z⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det) = Valued.v 1 at hprod
          rw [map_mul, hzval, one_mul, map_one] at hprod
          exact hprod.le
        have hrem : rem v (δv v) = (QuotientGroup.mk z : PGL2 (v.adicCompletion F)) := by
          simp only [rem, dF, dif_neg hv0, hdiagone, inv_one, one_mul, z, QuotientGroup.mk_mul]
        have himage : rem v (δv v) ∈ (P.loc v).pr '' (K v : Set (P.loc v).L) := by
          simp only [K, dif_neg hv0]
          rw [(P.tame v (fun h => hv0 (hT0 h))).image, hrem]
          exact ⟨z, hzi, hzinv, rfl⟩
        exact himage
    choose kF hkF hkp using hex
    have hkres : Set.Finite {v | ∃ hv : v ∉ S.Sf, kF v ∉ (P.tame v hv).Kmax} := by
      apply T0.finite_toSet.subset
      intro v hv
      change v ∈ T0
      by_contra hv0
      obtain ⟨hvS, hbad⟩ := hv
      exact hbad (by simpa only [K, dif_neg hv0] using hkF v)
    obtain ⟨k, hkCpt, hkInf⟩ := P.comp_surj kF (fun _ => 1) hkres
    have hklevel : th_classical_finiteLevel P T0 hT0 m k := by
      refine ⟨hkInf, ?_, ?_⟩
      · intro v hv
        rw [hkCpt]
        simpa only [K, dif_pos hv] using hkF v
      · intro v hv
        rw [hkCpt]
        simpa only [K, dif_neg hv] using hkF v
    refine ⟨δ * γ0, j, Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩, k, hklevel, ?_⟩
    intro v
    have hleft : (P.loc v).pr (P.compF v (P.ratRP (δ * γ0) * r)) =
        (QuotientGroup.mk (δv v) : PGL2 (v.adicCompletion F)) * QuotientGroup.mk (g v) := by
      rw [map_mul, map_mul, P.compF_ratRP, (P.loc v).sec_pr,
        Matrix.GeneralLinearGroup.map_mul, QuotientGroup.mk_mul, mul_assoc]
      apply congrArg (fun z : PGL2 (v.adicCompletion F) => QuotientGroup.mk (δv v) * z)
      simpa only [map_mul, P.compF_ratRP, (P.loc v).sec_pr] using (hg v).symm
    rw [hleft, map_mul, map_mul, hkCpt, hkp, hjp]
    simp [rem, mul_assoc]

end ArtinPrimitiveRoots.A1.Theta
