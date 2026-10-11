import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.continuedEis_component_representatives

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical MatrixGroups
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private noncomputable def continuedEis_conjugateRoot
    (γ : GL (Fin 2) ℂ) (z : ℂ) : SL(2, ℂ) :=
  ⟨((γ⁻¹ * upperM ℂ z * γ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ), by
    have hu : Matrix.GeneralLinearGroup.det (upperM ℂ z) = 1 := by
      apply Units.ext
      simp [upperM, Matrix.det_fin_two]
    have hdet : Matrix.GeneralLinearGroup.det
        (γ⁻¹ * upperM ℂ z * γ : GL (Fin 2) ℂ) = 1 := by
      simp [map_mul, map_inv, hu]
    simpa [Matrix.GeneralLinearGroup.det] using
      congrArg (fun u : ℂˣ => (u : ℂ)) hdet⟩

private theorem continuedEis_slFixBase_unitary (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (g : SL(2, ℂ))
    (hg : g • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  obtain ⟨_, _, _, hherm, _, _, _, _, _, _, _, _⟩ :=
    ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F)
  have hbaseMat : ArtinPrimitiveRoots.A1.Spec.ptMat (0 : ℂ) (1 : ℝ)
      (by norm_num) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ArtinPrimitiveRoots.A1.Spec.ptMat]
  have hpt0 : ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      (QuotientGroup.mk (1 : SL(2, ℂ)) : ArtinPrimitiveRoots.A1.Spec.H3) := by
    simp [ArtinPrimitiveRoots.A1.Spec.pt, hbaseMat]
  have hbase : ArtinPrimitiveRoots.A1.Spec.herm
      (ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) = 1 := by
    rw [hpt0]
    simp [ArtinPrimitiveRoots.A1.Spec.herm]
  have h := congrArg ArtinPrimitiveRoots.A1.Spec.herm hg
  rw [hherm g (ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)), hbase] at h
  exact Matrix.mem_unitaryGroup_iff.mpr (by simpa using h)

private theorem continuedEis_ptMat_smul_base (x : ℂ) (y : ℝ) (hy : 0 < y) :
    ArtinPrimitiveRoots.A1.Spec.ptMat x y hy •
        ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      ArtinPrimitiveRoots.A1.Spec.pt x y := by
  have hbaseMat : ArtinPrimitiveRoots.A1.Spec.ptMat (0 : ℂ) (1 : ℝ)
      (by norm_num) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ArtinPrimitiveRoots.A1.Spec.ptMat]
  have hpt0 : ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
      (QuotientGroup.mk (1 : SL(2, ℂ)) : ArtinPrimitiveRoots.A1.Spec.H3) := by
    simp [ArtinPrimitiveRoots.A1.Spec.pt, hbaseMat]
  rw [hpt0]
  simp [ArtinPrimitiveRoots.A1.Spec.pt, hy]

private theorem continuedEis_ptMat_pgl (x : ℂ) (y : ℝ) (hy : 0 < y) :
    (QuotientGroup.mk
      (ArtinPrimitiveRoots.A1.Spec.ptMat x y hy : GL (Fin 2) ℂ) : PGL2 ℂ) =
      (QuotientGroup.mk
        (upperM ℂ x * diagM ℂ (Units.mk0 (y : ℂ)
          (Complex.ofReal_ne_zero.mpr hy.ne')) : GL (Fin 2) ℂ) : PGL2 ℂ) := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hroot : (Real.sqrt y : ℂ) ≠ 0 := by exact_mod_cast hsqrt.ne'
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨Units.mk0 (Real.sqrt y : ℂ) hroot, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.diagonal, Matrix.scalar, ArtinPrimitiveRoots.A1.Spec.ptMat,
      upperM, diagM, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.coe_scalar, Complex.ofReal_mul,
      Real.mul_self_sqrt hy.le]
    <;> field_simp [hroot]
    <;> norm_num [Real.mul_self_sqrt hy.le]
    <;> rw [pow_two, ← Complex.ofReal_mul, Real.mul_self_sqrt hy.le]

private theorem continuedEis_continuous_coordsX :
    Continuous (ArtinPrimitiveRoots.A1.Spec.coordsX F) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨e, _, he⟩⟩ :=
    ArtinPrimitiveRoots.A1.Spec.G1_h3_basics (F := F)
  have hEq : ArtinPrimitiveRoots.A1.Spec.coordsX F =
      fun z => (e.symm z).1 := by
    funext z
    exact (he z).symm
  rw [hEq]
  exact continuous_subtype_val.comp e.symm.continuous_toFun

private noncomputable def continuedEis_rootRep {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) : P.RP :=
  Classical.choose (P.nS_components ((fun _ : S.Sf => (0 : _), x)))

private theorem continuedEis_rootRep_q {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) :
    P.q (continuedEis_rootRep P x) =
      P.tc.nS (Multiplicative.ofAdd ((fun _ : S.Sf => (0 : _), x))) :=
  (Classical.choose_spec (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).1

private theorem continuedEis_rootRep_nInf {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) :
    P.q (continuedEis_rootRep P x) = nInf P x := by
  rw [continuedEis_rootRep_q]
  unfold nInf
  congr 2

private theorem continuedEis_rootRep_compF {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (v : FinPlace F) :
  P.compF v (continuedEis_rootRep P x) = 1 := by
  change P.compF v (Classical.choose
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))) = 1
  obtain ⟨_, hF, _⟩ := Classical.choose_spec
    (P.nS_components ((fun _ : S.Sf => (0 : _), x)))
  rw [hF v]
  by_cases hv : v ∈ S.Sf <;> simp [hv]

private theorem continuedEis_rootRep_compC {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (x : InfinitePlace F → ℂ) (w : InfinitePlace F) :
    P.compC w (continuedEis_rootRep P x) =
      QuotientGroup.mk (upperM ℂ (x w)) :=
  (Classical.choose_spec (P.nS_components ((fun _ : S.Sf => (0 : _), x)))).2.2 w

private noncomputable def continuedEis_archUnit {F : Type} [Field F] [NumberField F]
    (y : InfinitePlace F → ℝ) (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : ℂˣ :=
  Units.mk0 ((y w : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (hy w).ne')

private theorem continuedEis_compU_atComplex {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (v : S.Sf) (w : InfinitePlace F) (z : ℂˣ) :
    S.compU v (S.atComplex w z) = 1 := by
  apply Units.ext
  simp [SData.compU, SData.atComplex]

private theorem continuedEis_compC_atComplex {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)
    (w w' : InfinitePlace F) (z : ℂˣ) :
    S.compC w (S.atComplex w' z) = if w = w' then z else 1 := by
  by_cases h : w = w'
  · subst w
    apply Units.ext
    simp [SData.compC, SData.atComplex]
  · apply Units.ext
    simp [SData.compC, SData.atComplex, h]

private noncomputable def continuedEis_archLocalRep {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) : P.RP :=
  Classical.choose (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))

private noncomputable def continuedEis_archRep {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) : P.RP :=
  ((Finset.univ : Finset (InfinitePlace F)).toList.map
    (continuedEis_archLocalRep P y hy)).prod

private theorem continuedEis_archLocalRep_q {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F) } {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) :
    P.q (continuedEis_archLocalRep P y hy w) =
      P.tc.aS (S.atComplex w (continuedEis_archUnit y hy w)) :=
  (Classical.choose_spec
    (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))).1

private theorem continuedEis_list_prod_eq_single {α M : Type} [Monoid M] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (a : α) (ha : a ∈ l) (m : M) :
    (l.map fun b => if b = a then m else 1).prod = m := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.nodup_cons.mp hl with ⟨hb, hl⟩
    simp only [List.mem_cons] at ha
    by_cases h : b = a
    · subst b
      simp only [List.map_cons, List.prod_cons, if_pos rfl]
      have htail : (l.map fun b => if b = a then m else 1).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
        have hne : c ≠ a := by
          intro hca
          subst c
          exact hb hc
        simp [hne]
      split_ifs <;> simp [htail]
    · have ha' : a ∈ l := by
        rcases ha with hEq | hmem
        · exact (h hEq.symm).elim
        · exact hmem
      simp only [List.map_cons, List.prod_cons, if_neg h, one_mul]
      exact ih hl ha'

private theorem continuedEis_archRep_q {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) :
    P.q (continuedEis_archRep P y hy) = aInf P y := by
  classical
  unfold continuedEis_archRep aInf
  rw [dif_pos hy, map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w => P.q (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod =
    (List.map (fun w => P.tc.aS (S.atComplex w (continuedEis_archUnit y hy w)))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod
  have hmap : List.map (fun w => P.q (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun w => P.tc.aS (S.atComplex w (continuedEis_archUnit y hy w)))
      (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w hw
    exact continuedEis_archLocalRep_q P y hy w
  rw [hmap]

private theorem continuedEis_archRep_compF {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (v : FinPlace F) :
  P.compF v (continuedEis_archRep P y hy) = 1 := by
  classical
  change P.compF v
      ((List.map (continuedEis_archLocalRep P y hy)
        (Finset.univ : Finset (InfinitePlace F)).toList).prod) = 1
  rw [map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w => P.compF v (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod = 1
  have hmap : List.map (fun w => P.compF v (continuedEis_archLocalRep P y hy w))
      (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun _ => (1 : (P.loc v).L))
      (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w hw
    obtain ⟨_, hF, _⟩ := Classical.choose_spec
      (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))
    change P.compF v (Classical.choose
      (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))) = _
    by_cases hv : v ∈ S.Sf
    · have hF' : P.compF v (Classical.choose
          (P.aS_components (S.atComplex w (continuedEis_archUnit y hy w)))) =
        (P.loc v).a (S.compU ⟨v, hv⟩ (S.atComplex w (continuedEis_archUnit y hy w))) := by
        simpa [hv] using hF v
      have hc := continuedEis_compU_atComplex S ⟨v, hv⟩ w
        (continuedEis_archUnit y hy w)
      rw [hF', hc, (P.loc v).a_one]
    · simpa [hv] using hF v
  rw [hmap]
  simp

private theorem continuedEis_archRep_compC {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (y : InfinitePlace F → ℝ)
    (hy : ∀ w, 0 < y w) (w : InfinitePlace F) :
  P.compC w (continuedEis_archRep P y hy) =
      QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)) := by
  classical
  change P.compC w
      ((List.map (continuedEis_archLocalRep P y hy)
        (Finset.univ : Finset (InfinitePlace F)).toList).prod) =
    QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w))
  rw [map_list_prod]
  simp only [List.map_map]
  change (List.map (fun w' => P.compC w (continuedEis_archLocalRep P y hy w'))
      (Finset.univ : Finset (InfinitePlace F)).toList).prod =
    QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w))
  have hmap : List.map (fun w' => P.compC w (continuedEis_archLocalRep P y hy w'))
      (Finset.univ : Finset (InfinitePlace F)).toList =
    List.map (fun w' => if w' = w then
      QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)) else 1)
      (Finset.univ : Finset (InfinitePlace F)).toList := by
    apply List.map_congr_left
    intro w' hw'
    obtain ⟨_, _, hC⟩ := Classical.choose_spec
      (P.aS_components (S.atComplex w' (continuedEis_archUnit y hy w')))
    change P.compC w (Classical.choose
      (P.aS_components (S.atComplex w' (continuedEis_archUnit y hy w')))) = _
    rw [hC]
    have hunit : S.compC w (S.atComplex w' (continuedEis_archUnit y hy w')) =
        if w' = w then continuedEis_archUnit y hy w else 1 := by
      rw [continuedEis_compC_atComplex]
      by_cases h : w' = w
      · subst w'
        simp
      · have h' : w ≠ w' := fun he => h he.symm
        simp [h, h']
    rw [hunit]
    have hdiag : diagM ℂ (1 : ℂˣ) = (1 : GL (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagM]
    by_cases h : w' = w
    · subst w'
      simp [hdiag]
    · simp [h, hdiag]
  rw [hmap]
  have hprod := continuedEis_list_prod_eq_single
    (α := InfinitePlace F) (M := PGL2 ℂ)
    (Finset.univ : Finset (InfinitePlace F)).toList
    (Finset.nodup_toList (Finset.univ : Finset (InfinitePlace F)))
    w (Finset.mem_toList.mpr (Finset.mem_univ w))
    (QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y hy w)))
  exact hprod

private theorem continuedEis_infCompact_mul {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) {g h : P.tc.G}
    (hg : g ∈ infCompact P) (hh : h ∈ infCompact P) :
    g * h ∈ infCompact P := by
  obtain ⟨x, hqx, hxF, hxC⟩ := hg
  obtain ⟨y, hqy, hyF, hyC⟩ := hh
  refine ⟨x * y, ?_, ?_, ?_⟩
  · simpa [map_mul, hqx, hqy]
  · intro v
    simp [map_mul, hxF v, hyF v]
  · intro w
    obtain ⟨u, hu, huc⟩ := hxC w
    obtain ⟨v, hv, hvc⟩ := hyC w
    refine ⟨u * v, (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem hu hv, ?_⟩
    simp [map_mul, huc, hvc]

private theorem continuedEis_infCompact_commute_rep {F : Type} [Field F] [NumberField F]
    {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
    {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) {g j : P.tc.G}
    (hg : g ∈ infCompact P)
    (hj : ∃ x : P.RP, P.q x = j ∧ ∀ w, P.compC w x = 1) :
    g * j = j * g := by
  obtain ⟨x, hqx, hxF, hxC⟩ := hg
  obtain ⟨y, hqy, hyC⟩ := hj
  have hxy : x * y = y * x := by
    apply P.comp_ext
    · intro v
      simp [hxF v]
    · intro w
      simp [hxC w, hyC w]
  calc
    g * j = P.q x * P.q y := by rw [hqx, hqy]
    _ = P.q (x * y) := by simp
    _ = P.q (y * x) := by rw [hxy]
    _ = j * g := by rw [← hqy, ← hqx]; simp

/-- Keep the finite component fixed along the left archimedean unipotent orbit and express
the orbit in continuous positive classical coordinates. On closure of a bounded parameter
set the coordinate image is compact and its heights have positive minima.
Uses `continuedEis_component_representatives`, reconstructed component formulas and
automorphy/level/compact invariance. No analytic
integral argument is included. Consumed by `continuedEis_laurent_torus`. -/
theorem continuedEis_torus_charts {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} {C : ContinuedEisComponents I}
    (R : ContinuedEisReconstruction C) : ContinuedEisTorusCharts R := by
  classical
  intro g
  obtain ⟨j, γ, x0, y0, kinf, k, hy0, hkinf, hk, hg⟩ :=
    continuedEis_component_representatives C g
  let z0 : ArtinPrimitiveRoots.A1.Spec.X F :=
    ArtinPrimitiveRoots.A1.Spec.ptX' F x0 y0
  let d (t : InfinitePlace F → ℂ) (w : InfinitePlace F) : SL(2, ℂ) :=
    continuedEis_conjugateRoot (Matrix.GeneralLinearGroup.map w.embedding γ) (t w)
  let orbit (t : InfinitePlace F → ℂ) : ArtinPrimitiveRoots.A1.Spec.X F :=
    ArtinPrimitiveRoots.A1.Spec.actAtPlaces F (d t) z0
  let p (t : InfinitePlace F → ℂ) : ArtinPrimitiveRoots.A1.Spec.Coord F :=
    ArtinPrimitiveRoots.A1.Spec.coordsX F (orbit t)
  have hdcont : ∀ w : InfinitePlace F, Continuous (fun z : ℂ =>
      continuedEis_conjugateRoot (Matrix.GeneralLinearGroup.map w.embedding γ) z) := by
    intro w
    fun_prop [continuedEis_conjugateRoot, upperM]
  have hDcont : Continuous (fun t : InfinitePlace F → ℂ => d t) := by
    apply continuous_pi
    intro w
    exact (hdcont w).comp (continuous_apply w)
  have hOrbitCont : Continuous orbit := by
    exact ((ArtinPrimitiveRoots.A1.Spec.G2_x_action (F := F)).2.2.2.2 z0).comp hDcont
  have hpcont : Continuous p := by
    exact continuedEis_continuous_coordsX.comp hOrbitCont
  have hp_pos : ∀ t, p t ∈ ArtinPrimitiveRoots.A1.Spec.posSet F := by
    intro t w
    change 0 < ArtinPrimitiveRoots.A1.Spec.height (orbit t w)
    rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
    exact OAI.CubicEisenstein.hyperbolicHeight_pos (orbit t w)
  let u (t : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
    fun w => (p t w).1
  let v (t : InfinitePlace F → ℂ) : InfinitePlace F → ℝ :=
    fun w => (p t w).2
  have hvpos (t : InfinitePlace F → ℂ) : ∀ w, 0 < v t w := by
    intro w
    exact hp_pos t w
  let δ (t : InfinitePlace F → ℂ) : P.tc.G :=
    (P.tc.rat γ)⁻¹ * nInf P t * P.tc.rat γ
  let b (t : InfinitePlace F → ℂ) : P.tc.G :=
    nInf P (u t) * aInf P (v t)
  let κ (t : InfinitePlace F → ℂ) : P.tc.G :=
    (b t)⁻¹ * δ t * nInf P x0 * aInf P y0
  let rA (t : InfinitePlace F → ℂ) : P.RP :=
    (P.ratRP γ)⁻¹ * continuedEis_rootRep P t * P.ratRP γ *
      continuedEis_rootRep P x0 * continuedEis_archRep P y0 hy0
  let rB (t : InfinitePlace F → ℂ) : P.RP :=
    continuedEis_rootRep P (u t) * continuedEis_archRep P (v t) (hvpos t)
  let rres (t : InfinitePlace F → ℂ) : P.RP := (rB t)⁻¹ * rA t
  have hqres : ∀ t, P.q (rres t) = κ t := by
    intro t
    simp only [rres, rA, rB, κ, b, δ, map_mul, map_inv,
      P.q_ratRP, continuedEis_rootRep_nInf, continuedEis_archRep_q]
    group
  have hresF : ∀ t v', P.compF v' (rres t) = 1 := by
    intro t v'
    simp [rres, rA, rB, map_mul, map_inv,
      continuedEis_rootRep_compF, continuedEis_archRep_compF]
  have hresC : ∀ t w, P.compC w (rres t) =
      (QuotientGroup.mk
        (upperM ℂ (u t w) * diagM ℂ (continuedEis_archUnit (v t) (hvpos t) w)))⁻¹ *
      (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ))⁻¹ *
      QuotientGroup.mk (upperM ℂ (t w)) *
      QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) *
      QuotientGroup.mk (upperM ℂ (x0 w)) *
      QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w)) := by
    intro t w
    simp [rres, rA, rB, map_mul, map_inv, P.compC_ratRP,
      continuedEis_rootRep_compC, continuedEis_archRep_compC]
    group
  let kSL (t : InfinitePlace F → ℂ) (w : InfinitePlace F) : SL(2, ℂ) :=
    (ArtinPrimitiveRoots.A1.Spec.ptMat (u t w) (v t w) (hvpos t w))⁻¹ *
      d t w * ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w)
  have hptcoord (t : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      ArtinPrimitiveRoots.A1.Spec.pt (u t w) (v t w) = orbit t w := by
    change ArtinPrimitiveRoots.A1.Spec.pt
      (ArtinPrimitiveRoots.A1.Spec.horiz (orbit t w))
      (ArtinPrimitiveRoots.A1.Spec.height (orbit t w)) = orbit t w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (orbit t w)
  have hDA (t : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      d t w • (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) •
        ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ)) = orbit t w := by
    rw [continuedEis_ptMat_smul_base]
    rfl
  have hfix (t : InfinitePlace F → ℂ) (w : InfinitePlace F) :
      kSL t w • ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) =
        ArtinPrimitiveRoots.A1.Spec.pt (0 : ℂ) (1 : ℝ) := by
    dsimp [kSL]
    simp only [mul_smul]
    rw [hDA t w, ← hptcoord t w, ← continuedEis_ptMat_smul_base
      (u t w) (v t w) (hvpos t w)]
    simp
  have hκmem : ∀ t, κ t ∈ infCompact P := by
    intro t
    refine ⟨rres t, hqres t, hresF t, ?_⟩
    intro w
    refine ⟨(kSL t w : GL (Fin 2) ℂ),
      continuedEis_slFixBase_unitary F (kSL t w) (hfix t w), ?_⟩
    have hB := continuedEis_ptMat_pgl (u t w) (v t w) (hvpos t w)
    have hA := continuedEis_ptMat_pgl (x0 w) (y0 w) (hy0 w)
    have hBsplit :
        (QuotientGroup.mk
          (ArtinPrimitiveRoots.A1.Spec.ptMat (u t w) (v t w) (hvpos t w) :
            GL (Fin 2) ℂ) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (u t w)) : PGL2 ℂ) *
            (QuotientGroup.mk
              (diagM ℂ (Units.mk0 (v t w : ℂ)
                (Complex.ofReal_ne_zero.mpr (hvpos t w).ne')) : GL (Fin 2) ℂ) : PGL2 ℂ) := by
      simpa [map_mul] using hB
    have hAsplit :
        (QuotientGroup.mk
          (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) :
            GL (Fin 2) ℂ) : PGL2 ℂ) =
          (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
            (QuotientGroup.mk
              (diagM ℂ (Units.mk0 (y0 w : ℂ)
                (Complex.ofReal_ne_zero.mpr (hy0 w).ne')) : GL (Fin 2) ℂ) : PGL2 ℂ) := by
      rw [hA]
      exact (Matrix.ProjGenLinGroup.mk).map_mul _ _
    have hresC' : P.compC w (rres t) =
        (QuotientGroup.mk (upperM ℂ (u t w) * diagM ℂ
            (Units.mk0 (v t w : ℂ) (Complex.ofReal_ne_zero.mpr (hvpos t w).ne')) : GL (Fin 2) ℂ) :
          PGL2 ℂ)⁻¹ *
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ)⁻¹ *
        (QuotientGroup.mk (upperM ℂ (t w)) : PGL2 ℂ) *
        (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) *
        (QuotientGroup.mk (upperM ℂ (x0 w)) : PGL2 ℂ) *
        (QuotientGroup.mk (diagM ℂ
            (Units.mk0 (y0 w : ℂ) (Complex.ofReal_ne_zero.mpr (hy0 w).ne')) : GL (Fin 2) ℂ) :
          PGL2 ℂ) := by
      simpa [continuedEis_archUnit] using hresC t w
    have hmid :
        ((QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ))⁻¹ *
          (QuotientGroup.mk (upperM ℂ (t w)) : PGL2 ℂ) *
          (QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ) : PGL2 ℂ) =
        (QuotientGroup.mk
          ((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ *
            upperM ℂ (t w) * (Matrix.GeneralLinearGroup.map w.embedding γ)) : PGL2 ℂ) := by
      simp [map_mul, map_inv]
    have hdclass :
        (QuotientGroup.mk (d t w : GL (Fin 2) ℂ) : PGL2 ℂ) =
          (QuotientGroup.mk
            ((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ *
              upperM ℂ (t w) * (Matrix.GeneralLinearGroup.map w.embedding γ)) : PGL2 ℂ) := by
      have hGL : (d t w : GL (Fin 2) ℂ) =
          (Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ *
            upperM ℂ (t w) * (Matrix.GeneralLinearGroup.map w.embedding γ) := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change ((continuedEis_conjugateRoot
            (Matrix.GeneralLinearGroup.map w.embedding γ) (t w) : SL(2, ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) i j =
          (((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ *
            upperM ℂ (t w) * (Matrix.GeneralLinearGroup.map w.embedding γ) :
            GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j
        rfl
      exact congrArg (fun g : GL (Fin 2) ℂ => (QuotientGroup.mk g : PGL2 ℂ)) hGL
    let cB : PGL2 ℂ := QuotientGroup.mk
      (upperM ℂ (u t w) * diagM ℂ (continuedEis_archUnit (v t) (hvpos t) w))
    let cGamma : PGL2 ℂ := QuotientGroup.mk (Matrix.GeneralLinearGroup.map w.embedding γ)
    let cN : PGL2 ℂ := QuotientGroup.mk (upperM ℂ (t w))
    let cX : PGL2 ℂ := QuotientGroup.mk (upperM ℂ (x0 w))
    let cD : PGL2 ℂ := QuotientGroup.mk (diagM ℂ (continuedEis_archUnit y0 hy0 w))
    have hresCgroup : P.compC w (rres t) =
        cB⁻¹ * cGamma⁻¹ * cN * cGamma * cX * cD := by
      simpa [cB, cGamma, cN, cX, cD, continuedEis_archUnit] using hresC t w
    have hBclass : cB = QuotientGroup.mk
        (ArtinPrimitiveRoots.A1.Spec.ptMat (u t w) (v t w) (hvpos t w) : GL (Fin 2) ℂ) := by
      dsimp [cB]
      exact hB.symm
    have hMidClass : cGamma⁻¹ * cN * cGamma =
        QuotientGroup.mk (d t w : GL (Fin 2) ℂ) := by
      calc
        cGamma⁻¹ * cN * cGamma =
            QuotientGroup.mk
              ((Matrix.GeneralLinearGroup.map w.embedding γ)⁻¹ *
                upperM ℂ (t w) * (Matrix.GeneralLinearGroup.map w.embedding γ)) := by
          simpa [cGamma, cN] using hmid
        _ = QuotientGroup.mk (d t w : GL (Fin 2) ℂ) := hdclass.symm
    have hXDclass : cX * cD = QuotientGroup.mk
        (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) : GL (Fin 2) ℂ) := by
      dsimp [cX, cD]
      exact hAsplit.symm
    have hlocal :
        P.compC w (rres t) =
          QuotientGroup.mk (kSL t w : GL (Fin 2) ℂ) := by
      calc
        P.compC w (rres t) = cB⁻¹ * cGamma⁻¹ * cN * cGamma * cX * cD := hresCgroup
        _ = (cB⁻¹ * (cGamma⁻¹ * cN * cGamma)) * (cX * cD) := by group
        _ = ((QuotientGroup.mk
              (ArtinPrimitiveRoots.A1.Spec.ptMat (u t w) (v t w) (hvpos t w) :
                GL (Fin 2) ℂ))⁻¹ *
              (QuotientGroup.mk (d t w : GL (Fin 2) ℂ)) *
              QuotientGroup.mk
                (ArtinPrimitiveRoots.A1.Spec.ptMat (x0 w) (y0 w) (hy0 w) :
                  GL (Fin 2) ℂ)) := by
          rw [hBclass, hMidClass, hXDclass]
        _ = QuotientGroup.mk (kSL t w : GL (Fin 2) ℂ) := by
          simp [kSL, Matrix.SpecialLinearGroup.toPGL, map_mul, map_inv]
    simpa [kSL, Matrix.SpecialLinearGroup.toPGL] using hlocal
  have hκcomm : ∀ t, κ t * j = j * κ t := by
    intro t
    apply continuedEis_infCompact_commute_rep P (hκmem t)
    exact C.finite_components j j.property
  have hκkinf : ∀ t, κ t * kinf ∈ infCompact P := by
    intro t
    exact continuedEis_infCompact_mul P (hκmem t) hkinf
  have hfactor (t : InfinitePlace F → ℂ) :
      b t * κ t = δ t * nInf P x0 * aInf P y0 := by
    dsimp [κ]
    group
  have hconj (t : InfinitePlace F → ℂ) :
      nInf P t * P.tc.rat γ = P.tc.rat γ * δ t := by
    dsimp [δ]
    group
  have hOrbitGroup (t : InfinitePlace F → ℂ) :
      nInf P t * g =
        P.tc.rat γ * ((b t * j) * (κ t * kinf) * k) := by
    calc
      nInf P t * g =
          nInf P t * (P.tc.rat γ *
            ((nInf P x0 * aInf P y0 * j) * kinf * k)) := by
        rw [hg]
        group
      _ = P.tc.rat γ *
          (δ t * ((nInf P x0 * aInf P y0 * j) * kinf * k)) := by
        rw [← mul_assoc, hconj, mul_assoc]
      _ = P.tc.rat γ * ((b t * κ t * j) * kinf * k) := by
        congr 1
        rw [show δ t * ((nInf P x0 * aInf P y0 * j) * kinf * k) =
          ((δ t * nInf P x0 * aInf P y0) * j) * kinf * k by group]
        rw [hfactor t]
      _ = P.tc.rat γ * ((b t * j) * (κ t * kinf) * k) := by
        congr 1
        calc
          (b t * κ t) * j * kinf * k =
              b t * (κ t * j) * (kinf * k) := by group
          _ = b t * (j * κ t) * (kinf * k) := by rw [hκcomm t]
          _ = (b t * j) * (κ t * kinf) * k := by group
  have hpt (t : InfinitePlace F → ℂ) :
      ArtinPrimitiveRoots.A1.Spec.ptX F (p t) = orbit t := by
    funext w
    exact ArtinPrimitiveRoots.A1.Spec.pt_horiz_height (orbit t w)
  have hclassical (t : InfinitePlace F → ℂ) (Ψ : P.tc.G → ℂ) :
      classicalOf P Ψ j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) =
        Ψ (b t * j) := by
    simp [ArtinPrimitiveRoots.A1.Theta.classicalOf, hpt t, b, u, v, p,
      ArtinPrimitiveRoots.A1.Spec.coordsX]
  refine ⟨j, 1, p, hpcont, hp_pos, ?_, ?_⟩
  · intro s hs t
    have hval :
        R.E s (b t * j) =
          C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) := by
      calc
        R.E s (b t * j) =
            classicalOf P (R.E s) j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) :=
          (hclassical t (R.E s)).symm
        _ = C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) :=
          congrFun (R.E_component s hs j) (ArtinPrimitiveRoots.A1.Spec.ptX F (p t))
    simpa using (calc
      R.E s (nInf P t * g) =
          R.E s (P.tc.rat γ * ((b t * j) * (κ t * kinf) * k)) :=
        congrArg (R.E s) (hOrbitGroup t)
      _ = R.E s ((b t * j) * (κ t * kinf) * k) :=
        R.E_aut s hs γ ((b t * j) * (κ t * kinf) * k)
      _ = R.E s ((b t * j) * (κ t * kinf)) :=
        R.E_level s hs ((b t * j) * (κ t * kinf)) k hk
      _ = R.E s (b t * j) :=
        R.E_compact s hs (b t * j) (κ t * kinf) (hκkinf t)
      _ = C.componentE j s (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) := hval)
  · intro t
    have hval :
        R.theta (b t * j) =
          C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) := by
      calc
        R.theta (b t * j) =
            classicalOf P R.theta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) :=
          (hclassical t R.theta).symm
        _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) :=
          congrFun (R.theta_component j) (ArtinPrimitiveRoots.A1.Spec.ptX F (p t))
    simpa using (calc
      R.theta (nInf P t * g) =
          R.theta (P.tc.rat γ * ((b t * j) * (κ t * kinf) * k)) :=
        congrArg R.theta (hOrbitGroup t)
      _ = R.theta ((b t * j) * (κ t * kinf) * k) :=
        R.theta_aut γ ((b t * j) * (κ t * kinf) * k)
      _ = R.theta ((b t * j) * (κ t * kinf)) :=
        R.theta_level ((b t * j) * (κ t * kinf)) k hk
      _ = R.theta (b t * j) :=
        R.theta_compact (b t * j) (κ t * kinf) (hκkinf t)
      _ = C.componentTheta j (ArtinPrimitiveRoots.A1.Spec.ptX F (p t)) := hval)

end ArtinPrimitiveRoots.A1.Theta
