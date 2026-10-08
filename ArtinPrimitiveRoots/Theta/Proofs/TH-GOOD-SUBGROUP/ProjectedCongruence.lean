import ArtinPrimitiveRoots.Theta.Proofs.TH_CLASSICAL.Helpers

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

set_option maxHeartbeats 400000 in
/-- A principal congruence subgroup lies in all of the conjugated projected local levels. -/
theorem th_good_projected_congruence (P : CoverPackage D S H A)
    (T0 : Finset (FinPlace F)) (hT0 : S.Sf ⊆ T0) (m : FinPlace F → ℕ)
    (hm : ∀ v ∈ T0, (P.loc v).m0 ≤ m v) (j : P.RP) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧
      ∀ γ ∈ Spec.congrSubgroup F N, ∃ k : P.RP,
        th_classical_finiteLevel P T0 hT0 m k ∧
          ∀ v, (P.loc v).pr (P.compF v
            (P.ratRP (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) * j)) =
              (P.loc v).pr (P.compF v (j * k)) := by
  classical
  have hval (v : FinPlace F) (a : 𝓞 F) :
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a) = v.intValuation a := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation',
      v.valuation_of_algebraMap]
  have hcongr (N : Ideal (𝓞 F)) (γ : SL(2, 𝓞 F))
      (hγ : γ ∈ Spec.congrSubgroup F N) (i l : Fin 2) :
      γ i l - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i l ∈ N := by
    have hγ' : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk N) γ = 1 := hγ
    apply Ideal.Quotient.eq.mp
    have he := congrArg
      (fun a : SL(2, 𝓞 F ⧸ N) => (a : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ N)) i l) hγ'
    change Ideal.Quotient.mk N (γ i l) = (1 : Matrix (Fin 2) (Fin 2) (𝓞 F ⧸ N)) i l at he
    simpa [Matrix.one_apply] using he
  have hsmall (v : FinPlace F) (t : ℕ) (ht : (P.loc v).m0 ≤ t)
      (g : SL(2, v.adicCompletion F))
      (hprec : ∀ i l : Fin 2,
        Valued.v (g i l - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i l) ≤
          WithZero.exp (-((max t 1 : ℕ) : ℤ))) :
      ∃ a ∈ (P.loc v).Kc t, (P.loc v).pr a = QuotientGroup.mk (g : GL (Fin 2) _) := by
    have hr : WithZero.exp (-((max t 1 : ℕ) : ℤ)) <
        (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hbnd (i l : Fin 2) :
        Valued.v (g i l - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i l) ≤
          WithZero.exp (-(t : ℤ)) :=
      (hprec i l).trans (WithZero.exp_le_exp.mpr (by omega))
    have ha : Valued.v (g 0 0) = 1 := by
      have hclose : Valued.v (g 0 0 - 1) < 1 := by simpa using (hprec 0 0).trans_lt hr
      simpa only [map_one] using Valued.v.map_eq_of_sub_lt
        (x := (1 : v.adicCompletion F)) (y := g 0 0) (by simpa using hclose)
    have ha0 : g 0 0 ≠ 0 := by
      intro hz
      exact zero_ne_one (by simpa only [hz, map_zero] using ha)
    let u : (v.adicCompletion F)ˣ := Units.mk0 (g 0 0) ha0
    have hc : g 1 0 / g 0 0 ∈ ball v t := by
      change Valued.v (g 1 0 / g 0 0) ≤ WithZero.exp (-(t : ℤ))
      rw [Valuation.map_div, ha, div_one]
      simpa using hbnd 1 0
    have hb : g 0 1 / g 0 0 ∈ ball v t := by
      change Valued.v (g 0 1 / g 0 0) ≤ WithZero.exp (-(t : ℤ))
      rw [Valuation.map_div, ha, div_one]
      simpa using hbnd 0 1
    have hu : ((u ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 ∈ ball v t := by
      change Valued.v (((u ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤
        WithZero.exp (-(t : ℤ))
      have he : ((u ^ 2 : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1 =
          (g 0 0 - 1) * (g 0 0 + 1) := by simp [u]; ring
      rw [he, map_mul]
      have hp : Valued.v (g 0 0 + 1) ≤ 1 := by
        simpa only [ha, map_one, max_self] using Valued.v.map_add (g 0 0) 1
      calc
        Valued.v (g 0 0 - 1) * Valued.v (g 0 0 + 1) ≤
            Valued.v (g 0 0 - 1) * 1 := mul_le_mul_of_nonneg_left hp zero_le
        _ = Valued.v (g 0 0 - 1) := mul_one _
        _ ≤ WithZero.exp (-(t : ℤ)) := by simpa using hbnd 0 0
    let a : (P.loc v).L := (P.loc v).nbar (Multiplicative.ofAdd (g 1 0 / g 0 0)) *
      (P.loc v).a (u ^ 2) * (P.loc v).n (Multiplicative.ofAdd (g 0 1 / g 0 0))
    have hamem : a ∈ (P.loc v).Kc t :=
      ((P.loc v).Kc t).mul_mem
        (((P.loc v).Kc t).mul_mem ((P.loc v).nbar_Kc t ht _ hc) ((P.loc v).a_Kc t ht _ hu))
        ((P.loc v).n_Kc t ht _ hb)
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using g.property
    have hword : (QuotientGroup.mk (g : GL (Fin 2) _) : PGL2 (v.adicCompletion F)) =
        QuotientGroup.mk (lowerM _ (g 1 0 / g 0 0) * diagM _ (u ^ 2) *
          upperM _ (g 0 1 / g 0 0)) := by
      change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
      apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
      refine ⟨u, ?_⟩
      apply Units.ext
      apply Matrix.ext
      intro i l
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      fin_cases i <;> fin_cases l
      all_goals
        simp [u, lowerM, diagM, upperM, Matrix.scalar, Matrix.diagonal,
          Matrix.mul_apply, Fin.sum_univ_two]
        <;> field_simp [ha0]
        <;> linear_combination hdet
    refine ⟨a, hamem, ?_⟩
    rw [hword]
    simp only [a, map_mul, (P.loc v).pr_nbar, (P.loc v).pr_a, (P.loc v).pr_n,
      ← QuotientGroup.mk_mul]
  let K (v : FinPlace F) : Subgroup (P.loc v).L :=
    if hv : v ∈ T0 then (P.loc v).Kc (m v)
    else (P.tame v (fun h => hv (hT0 h))).Kmax
  have hKopen (v : FinPlace F) : IsOpen (K v : Set (P.loc v).L) := by
    dsimp only [K]
    split_ifs with hv
    · exact (P.loc v).Kc_open (m v) (hm v hv)
    · exact (P.tame v (fun h => hv (hT0 h))).open_
  let β (v : FinPlace F) : PGL2 (v.adicCompletion F) := (P.loc v).pr (P.compF v j)
  let U (v : FinPlace F) : Set (P.loc v).L :=
    {a | (β v)⁻¹ * (P.loc v).pr a * β v ∈ (P.loc v).pr '' (K v : Set (P.loc v).L)}
  have hUopen (v : FinPlace F) : IsOpen (U v) := by
    apply ((P.loc v).pr_open _ (hKopen v)).preimage
    exact (continuous_const.mul (P.loc v).pr_cont).mul continuous_const
  have hUone (v : FinPlace F) : (1 : (P.loc v).L) ∈ U v := by
    change (β v)⁻¹ * (P.loc v).pr 1 * β v ∈ (P.loc v).pr '' (K v : Set (P.loc v).L)
    rw [map_one, mul_one, inv_mul_cancel]
    exact ⟨1, (K v).one_mem, map_one _⟩
  choose t ht htU using fun v : FinPlace F =>
    (P.loc v).Kc_nhds (U v) ((hUopen v).mem_nhds (hUone v))
  let E : Set (FinPlace F) :=
    {v | ∃ hv : v ∉ S.Sf, P.compF v j ∉ (P.tame v hv).Kmax}
  have hE : E.Finite := P.comp_restricted j
  let T : Finset (FinPlace F) := T0 ∪ hE.toFinset
  have hT0T : T0 ⊆ T := Finset.subset_union_left
  let N : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ max (t v) 1
  have hN : N ≠ ⊥ := by
    change (∏ v ∈ T, v.asIdeal ^ max (t v) 1 : Ideal (𝓞 F)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun v hv => pow_ne_zero _ v.ne_bot
  have hNle (v : FinPlace F) (hv : v ∈ T) : N ≤ v.asIdeal ^ max (t v) 1 := by
    change (∏ w ∈ T, w.asIdeal ^ max (t w) 1) ≤ v.asIdeal ^ max (t v) 1
    exact Ideal.prod_le_inf.trans (Finset.inf_le hv)
  refine ⟨N, hN, ?_⟩
  intro γ hγ
  let g (v : FinPlace F) : SL(2, v.adicCompletion F) :=
    Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (v.adicCompletion F)) γ
  have hmap (v : FinPlace F) :
      Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F))
        (Matrix.SpecialLinearGroup.toGL (Spec.toSLF F γ)) =
          Matrix.SpecialLinearGroup.toGL (g v) := by
    apply Units.ext
    apply Matrix.ext
    intro i l
    change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (γ i l)) =
      algebraMap (𝓞 F) (v.adicCompletion F) (γ i l)
    exact (IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) (γ i l)).symm
  have hprec (v : FinPlace F) (hv : v ∈ T) (i l : Fin 2) :
      Valued.v (g v i l - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i l) ≤
        WithZero.exp (-((max (t v) 1 : ℕ) : ℤ)) := by
    have hglob : v.intValuation (γ i l - (1 : Matrix (Fin 2) (Fin 2) (𝓞 F)) i l) ≤
        WithZero.exp (-((max (t v) 1 : ℕ) : ℤ)) :=
      (v.intValuation_le_pow_iff_mem _ _).mpr (hNle v hv (hcongr N γ hγ i l))
    rw [← hval v] at hglob
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (γ i l) -
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i l) ≤ _
    simpa [map_sub, Matrix.one_apply] using hglob
  have hints (v : FinPlace F) (i l : Fin 2) :
      (g v : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i l ∈ v.adicCompletionIntegers F := by
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (γ i l)) ≤ 1
    rw [hval]
    exact v.intValuation_le_one _
  have hinv (v : FinPlace F) :
      ((g v : GL (Fin 2) (v.adicCompletion F))⁻¹).val.det ∈ v.adicCompletionIntegers F := by
    have hid : Matrix.GeneralLinearGroup.det ((g v : GL (Fin 2) (v.adicCompletion F))⁻¹) = 1 := by
      rw [map_inv, Matrix.SpecialLinearGroup.coeToGL_det, inv_one]
    change Valued.v (((Matrix.GeneralLinearGroup.det ((g v : GL (Fin 2) (v.adicCompletion F))⁻¹) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F)) ≤ 1
    rw [hid, Units.val_one, map_one]
  have hex (v : FinPlace F) : ∃ k ∈ K v,
      (P.loc v).pr k = (β v)⁻¹ * QuotientGroup.mk (g v : GL (Fin 2) (v.adicCompletion F)) * β v := by
    by_cases hv : v ∈ T
    · obtain ⟨a, ha, hap⟩ := hsmall v (t v) (ht v) (g v) (hprec v hv)
      have hUa := htU v ha
      change (β v)⁻¹ * (P.loc v).pr a * β v ∈ (P.loc v).pr '' (K v : Set (P.loc v).L) at hUa
      rw [hap] at hUa
      exact hUa
    · have hv0 : v ∉ T0 := fun h => hv (hT0T h)
      have hvS : v ∉ S.Sf := fun h => hv0 (hT0 h)
      have hjK : P.compF v j ∈ (P.tame v hvS).Kmax := by
        by_contra hbad
        exact hv (Finset.mem_union_right T0 (hE.mem_toFinset.mpr ⟨hvS, hbad⟩))
      have himage : (QuotientGroup.mk (g v : GL (Fin 2) (v.adicCompletion F)) : PGL2 (v.adicCompletion F)) ∈
          (P.loc v).pr '' ((P.tame v hvS).Kmax : Set (P.loc v).L) := by
        rw [(P.tame v hvS).image]
        exact ⟨(g v : GL (Fin 2) (v.adicCompletion F)), hints v, hinv v, rfl⟩
      obtain ⟨a, ha, hap⟩ := himage
      let k : (P.loc v).L := (P.compF v j)⁻¹ * a * P.compF v j
      refine ⟨k, ?_, ?_⟩
      · simpa only [K, dif_neg hv0] using
          ((P.tame v hvS).Kmax).mul_mem
            (((P.tame v hvS).Kmax).mul_mem (((P.tame v hvS).Kmax).inv_mem hjK) ha) hjK
      · simp only [k, map_mul, map_inv, hap, β]
  choose kF hkF hkp using hex
  have hkres : Set.Finite {v | ∃ hv : v ∉ S.Sf, kF v ∉ (P.tame v hv).Kmax} := by
    apply T0.finite_toSet.subset
    intro v hv
    change v ∈ T0
    by_contra hv0
    obtain ⟨hvS, hbad⟩ := hv
    exact hbad (by simpa only [K, dif_neg hv0] using hkF v)
  obtain ⟨k, hkcomp, hkInf⟩ := P.comp_surj kF (fun _ => 1) hkres
  have hklevel : th_classical_finiteLevel P T0 hT0 m k := by
    refine ⟨hkInf, ?_, ?_⟩
    · intro v hv
      rw [hkcomp]
      simpa only [K, dif_pos hv] using hkF v
    · intro v hv
      rw [hkcomp]
      simpa only [K, dif_neg hv] using hkF v
  refine ⟨k, hklevel, ?_⟩
  intro v
  simp only [map_mul, P.compF_ratRP, (P.loc v).sec_pr, hmap v,
    hkcomp v, hkp v, β, mul_assoc, mul_inv_cancel_left]

end ArtinPrimitiveRoots.A1.Theta
