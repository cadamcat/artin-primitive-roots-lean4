import ArtinPrimitiveRoots.A2.Reflection.Nodes
import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.A1.AddCharExists

/-!
Local support for the A2 reflection characters producer.
-/

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.A2_PRODUCERS

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

theorem powerUnits_nhds_one (L : Type*) [NontriviallyNormedField L] [CompleteSpace L]
    (n : ℕ) (hn : (n : L) ≠ 0) :
    {u : Lˣ | ∃ b : Lˣ, u = b ^ n} ∈ 𝓝 (1 : Lˣ) := by
  have hnNat : n ≠ 0 := by
    intro h
    apply hn
    simp [h]
  have hd : HasStrictDerivAt (fun x : L => x ^ n) (n : L) 1 := by
    simpa using hasStrictDerivAt_pow n (1 : L)
  have hm : Filter.map (fun x : L => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hd.map_nhds_eq hn
  have hp : {x : L | ∃ y : L, x = y ^ n} ∈
      Filter.map (fun x : L => x ^ n) (𝓝 1) := by
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall fun x => ⟨x, rfl⟩)
  rw [hm] at hp
  filter_upwards [(Units.continuous_val.tendsto (1 : Lˣ)).eventually hp] with u hu
  obtain ⟨y, hy⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h
    apply Units.ne_zero u
    rw [hy, h, zero_pow hnNat]
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  change (u : L) = y ^ n
  exact hy

theorem finitePlace_sixthPower_nhds_one (v : FinPlace F) :
    {u : (v.adicCompletion F)ˣ | ∃ b : (v.adicCompletion F)ˣ, u = b ^ 6} ∈
      𝓝 (1 : (v.adicCompletion F)ˣ) := by
  let L := v.adicCompletion F
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let x : L := NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F t)
  have htK : algebraMap (𝓞 F) F t ≠ 0 :=
    NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ht0
  have hx0 : x ≠ 0 := (NumberField.FinitePlace.embedding v).injective.ne htK
  have hxnorm : ‖x‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) v t).mpr ht
  letI : NontriviallyNormedField L :=
    NontriviallyNormedField.ofNormNeOne ⟨x, hx0, ne_of_lt hxnorm⟩
  have h6 : (6 : L) ≠ 0 := by norm_num
  exact powerUnits_nhds_one L 6 h6

def hilbertLocalHom (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (a : (v.adicCompletion F)ˣ) : (v.adicCompletion F)ˣ →* ℂˣ where
  toFun b := Units.map D.σ0.toMonoidHom ((H.hilb v a b)⁻¹)
  map_one' := by
    have hmul := H.mul_right v a 1 1
    have hh : H.hilb v a 1 * 1 = H.hilb v a 1 * H.hilb v a 1 := by
      simpa using hmul
    have h1 : H.hilb v a 1 = 1 := (mul_left_cancel hh).symm
    simp [h1]
  map_mul' b c := by
    apply Units.ext
    change D.σ0 (((H.hilb v a (b * c))⁻¹ : Fˣ) : F) =
      D.σ0 (((H.hilb v a b)⁻¹ : Fˣ) : F) *
        D.σ0 (((H.hilb v a c)⁻¹ : Fˣ) : F)
    rw [H.mul_right]
    simp [map_mul, mul_inv, mul_comm]

theorem hilbertLocalHom_continuous (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a : (v.adicCompletion F)ˣ) :
    Continuous (hilbertLocalHom D H v a) := by
  let f := hilbertLocalHom D H v a
  apply continuous_of_tendsto_nhds_one f
  have hpow := finitePlace_sixthPower_nhds_one (F := F) v
  have hkill : ∀ b : (v.adicCompletion F)ˣ, f (b ^ 6) = 1 := by
    intro b
    have hleft := H.sixth_power v (b ^ 6) a ⟨b, rfl⟩
    have hskew := H.skew v (b ^ 6) a
    have hright : H.hilb v a (b ^ 6) = 1 := by simpa [hleft] using hskew
    change Units.map D.σ0.toMonoidHom ((H.hilb v a (b ^ 6))⁻¹) = 1
    rw [hright]
    simp
  have heq : (fun u : (v.adicCompletion F)ˣ => f u) =ᶠ[𝓝 1]
      fun _ => (1 : ℂˣ) := by
    filter_upwards [hpow] with u hu
    obtain ⟨b, rfl⟩ := hu
    exact hkill b
  apply (Filter.tendsto_congr' heq).mpr
  exact tendsto_const_nhds

private theorem continuousFiniteAdele_ofAdicCompletion (v : FinPlace F) :
    Continuous (FiniteAdeleRing.ofAdicCompletion F v) := by
  classical
  let ι := FinPlace F
  let R : ι → Type := fun w => w.adicCompletion F
  let A : (w : ι) → ValuationSubring (R w) := fun w => w.adicCompletionIntegers F
  let Aset : (w : ι) → Set (R w) := fun w => A w
  let s : Set ι := {v}ᶜ
  have hs : Filter.cofinite ≤ Filter.principal s := by
    rw [Filter.le_principal_iff]
    simp [s]
  letI : TopologicalSpace (RestrictedProduct R Aset (Filter.principal s)) :=
    TopologicalSpace.induced DFunLike.coe inferInstance
  let f : v.adicCompletion F →
      RestrictedProduct R Aset (Filter.principal s) := fun x => by
        refine ⟨Pi.mulSingle v x, ?_⟩
        rw [Filter.eventually_principal]
        intro w hw
        have hwv : w ≠ v := by
          intro h
          subst w
          exact hw (by simp [s])
        change Pi.mulSingle v x w ∈ Aset w
        rw [Pi.mulSingle_eq_of_ne hwv]
        exact (A w).one_mem
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · subst w
      change Continuous (fun x : v.adicCompletion F => Pi.mulSingle v x v)
      have hfun : (fun x : v.adicCompletion F => Pi.mulSingle v x v) = id := by
        funext x
        exact Pi.mulSingle_eq_same v x
      exact hfun ▸ continuous_id
    · have hconst : (fun x : v.adicCompletion F => (f x : Π w, R w) w) = fun _ => 1 := by
        funext x
        exact Pi.mulSingle_eq_of_ne hw x
      change Continuous (fun x : v.adicCompletion F => (f x : Π w, R w) w)
      rw [hconst]
      exact continuous_const
  have hfun : (FiniteAdeleRing.ofAdicCompletion F v :
      v.adicCompletion F → FiniteAdeleRing (𝓞 F) F) =
      (RestrictedProduct.inclusion R Aset hs) ∘ f := by
    funext x
    ext w
    rfl
  have hinc : Continuous[
      TopologicalSpace.induced DFunLike.coe inferInstance,
      RestrictedProduct.topologicalSpace R Aset Filter.cofinite]
      (RestrictedProduct.inclusion R Aset hs) := by
    rw [← RestrictedProduct.topologicalSpace_eq_of_principal (S := s)]
    exact RestrictedProduct.continuous_inclusion hs
  change Continuous (FiniteAdeleRing.ofAdicCompletion F v :
    v.adicCompletion F → FiniteAdeleRing (𝓞 F) F)
  change Continuous[_, RestrictedProduct.topologicalSpace R Aset Filter.cofinite]
    (FiniteAdeleRing.ofAdicCompletion F v)
  rw [hfun]
  exact hinc.comp hf

private theorem continuousIdeleClass_ofAdicCompletion (v : FinPlace F) :
    Continuous (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  have hAdele : Continuous (AdeleRing.ofAdicCompletion (𝓞 F) F v) := by
    unfold AdeleRing.ofAdicCompletion
    exact continuous_prodMk.mpr ⟨continuous_const, continuousFiniteAdele_ofAdicCompletion v⟩
  have hIdele : Continuous (IdeleGroup.ofAdicCompletion (𝓞 F) F v) := by
    change Continuous (Units.map (AdeleRing.ofAdicCompletion (𝓞 F) F v))
    exact Units.continuous_map hAdele
  unfold IdeleClassGroup.ofAdicCompletion
  exact continuous_quotient_mk'.comp hIdele

private theorem continuousIdeleClass_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  have hAdele : Continuous (AdeleRing.ofCompletion (𝓞 F) F w) := by
    unfold AdeleRing.ofCompletion
    refine continuous_prodMk.mpr ⟨?_, continuous_const⟩
    apply continuous_pi
    intro w'
    by_cases hw : w' = w
    · subst w'
      have hfun : (fun x : w.Completion => Pi.mulSingle w x w) = id := by
        funext x
        exact Pi.mulSingle_eq_same w x
      exact hfun ▸ continuous_id
    · change Continuous fun x : w.Completion => Pi.mulSingle w x w'
      have hfun : (fun x : w.Completion => Pi.mulSingle w x w') = fun _ => 1 := by
        funext x
        exact Pi.mulSingle_eq_of_ne hw x
      exact hfun ▸ continuous_const
  have hIdele : Continuous (IdeleGroup.ofCompletion (𝓞 F) F w) := by
    change Continuous (Units.map (AdeleRing.ofCompletion (𝓞 F) F w))
    exact Units.continuous_map hAdele
  unfold IdeleClassGroup.ofCompletion
  exact continuous_quotient_mk'.comp hIdele

theorem compU_continuous (S : SData F CE condη) (v : S.Sf) :
    Continuous (S.compU v) := by
  unfold SData.compU
  apply Units.continuous_map
  exact (continuous_apply v).comp continuous_fst

def compUContinuousHom (S : SData F CE condη) (v : S.Sf) :
    S.FSˣ →ₜ* (v.1.adicCompletion F)ˣ :=
  ⟨S.compU v, compU_continuous S v⟩

theorem compC_continuous (S : SData F CE condη) (w : InfinitePlace F) :
    Continuous (S.compC w) := by
  unfold SData.compC
  apply Units.continuous_map
  exact (continuous_apply w).comp continuous_snd

def compCContinuousHom (S : SData F CE condη) (w : InfinitePlace F) :
    S.FSˣ →ₜ* ℂˣ :=
  ⟨S.compC w, compC_continuous S w⟩

def completionComplexContinuousMulEquiv (D : FieldData F) (w : InfinitePlace F) :
    w.Completion ≃ₜ* ℂ where
  __ := (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)).toMulEquiv
  continuous_toFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)).isometry_toFun.continuous
  continuous_invFun := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (D.isTotallyComplex.isComplex w)).symm.isometry_toFun.continuous

def compCToCompletionContinuousHom (D : FieldData F) (S : SData F CE condη)
    (w : InfinitePlace F) : S.FSˣ →ₜ* w.Completionˣ := by
  let e := Units.mapContinuousMulEquiv (completionComplexContinuousMulEquiv D w).symm
  let f : ℂˣ →ₜ* w.Completionˣ := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  exact f.comp (compCContinuousHom S w)

theorem heckeLocFin_continuous (ϑ : HeckeChar F) (v : FinPlace F) :
    Continuous (ϑ.loc v) := by
  change Continuous (fun u => ϑ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
  exact ϑ.continuous.comp (continuousIdeleClass_ofAdicCompletion v)

def heckeLocFinContinuousHom (ϑ : HeckeChar F) (v : FinPlace F) :
    (v.adicCompletion F)ˣ →ₜ* ℂˣ :=
  ⟨ϑ.loc v, heckeLocFin_continuous ϑ v⟩

theorem heckeLocInf_continuous (ϑ : HeckeChar F) (w : InfinitePlace F) :
    Continuous (ϑ.locInf w) := by
  change Continuous (fun u => ϑ (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
  exact ϑ.continuous.comp (continuousIdeleClass_ofCompletion w)

def heckeLocInfContinuousHom (ϑ : HeckeChar F) (w : InfinitePlace F) :
    w.Completionˣ →ₜ* ℂˣ :=
  ⟨ϑ.locInf w, heckeLocInf_continuous ϑ w⟩

def heckeFinFSContinuousHom (S : SData F CE condη) (ϑ : HeckeChar F) (v : S.Sf) :
    S.FSˣ →ₜ* ℂˣ :=
  (heckeLocFinContinuousHom ϑ v.1).comp (compUContinuousHom S v)

def heckeInfFSContinuousHom (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (w : InfinitePlace F) : S.FSˣ →ₜ* ℂˣ :=
  (heckeLocInfContinuousHom ϑ w).comp (compCToCompletionContinuousHom D S w)

theorem heckeFinFSContinuousHom_value (S : SData F CE condη) (ϑ : HeckeChar F)
    (v : S.Sf) (y : S.FSˣ) :
    heckeFinFSContinuousHom S ϑ v y = ϑ.loc v.1 (S.compU v y) := rfl

theorem heckeInfFSContinuousHom_value (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (w : InfinitePlace F) (y : S.FSˣ) :
    heckeInfFSContinuousHom D S ϑ w y =
      ϑ.locInf w (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w y)) := by
  rfl

theorem continuousMonoidHom_inv_apply {X : Type*} [Monoid X] [TopologicalSpace X]
    [ContinuousMul X] (f : X →ₜ* ℂˣ) (x : X) :
    (f⁻¹) x = (f x)⁻¹ := rfl

theorem continuousMonoidHom_finsetProd_apply {α X : Type*} [Monoid X]
    [TopologicalSpace X] [ContinuousMul X] {s : Finset α}
    (f : α → X →ₜ* ℂˣ) (x : X) :
    (∏ a ∈ s, f a) x = ∏ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ContinuousMonoidHom.mul_apply, ih]

theorem continuousMonoidHom_fintypeProd_apply {α X : Type*} [Fintype α] [Monoid X]
    [TopologicalSpace X] [ContinuousMul X] (f : α → X →ₜ* ℂˣ) (x : X) :
    (∏ a, f a) x = ∏ a, f a x :=
  continuousMonoidHom_finsetProd_apply (f := f) (s := Finset.univ) x

def lsContinuousHom (D : FieldData F) (S : SData F CE condη) (ϑ : HeckeChar F) :
    S.FSˣ →ₜ* ℂˣ :=
  (∏ v : S.Sf, (heckeFinFSContinuousHom S ϑ v)⁻¹) *
    ∏ w : InfinitePlace F, (heckeInfFSContinuousHom D S ϑ w)⁻¹

theorem lsContinuousHom_value (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (y : S.FSˣ) :
    ((lsContinuousHom D S ϑ y : ℂˣ) : ℂ) = S.LS ϑ y := by
  classical
  unfold lsContinuousHom
  rw [ContinuousMonoidHom.mul_apply]
  rw [continuousMonoidHom_fintypeProd_apply
        (f := fun v : S.Sf => (heckeFinFSContinuousHom S ϑ v)⁻¹) y,
      continuousMonoidHom_fintypeProd_apply
        (f := fun w : InfinitePlace F => (heckeInfFSContinuousHom D S ϑ w)⁻¹) y]
  simp only [continuousMonoidHom_inv_apply, Units.val_mul, Units.val_inv]
  simp [SData.LS, heckeFinFSContinuousHom_value, heckeInfFSContinuousHom_value,
    D.isTotallyComplex.isComplex]

theorem lsContinuousHom_unitary (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (hunit : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1) (y : S.FSˣ) :
    ‖((lsContinuousHom D S ϑ y : ℂˣ) : ℂ)‖ = 1 := by
  have hfin (v : S.Sf) :
      ‖((ϑ.loc v.1 (S.compU v y) : ℂˣ) : ℂ)‖ = 1 := by
    simpa [A1.HeckeChar.loc] using
      hunit (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v.1 (S.compU v y))
  have hinf (w : InfinitePlace F) :
      ‖((ϑ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w y)) : ℂˣ) : ℂ)‖ = 1 := by
    simpa [A1.HeckeChar.locInf] using
      hunit (IdeleClassGroup.ofCompletion (𝓞 F) F w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom (S.compC w y)))
  have hfinProd :
      ‖∏ v : S.Sf, (((ϑ.loc v.1 (S.compU v y))⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_prod]
    simp [norm_inv, hfin]
  have hinfProd :
      ‖∏ w : InfinitePlace F, if hw : w.IsComplex then
        (((ϑ.locInf w (Units.map
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
            (S.compC w y)))⁻¹ : ℂˣ) : ℂ) else 1‖ = 1 := by
    simp_rw [dif_pos (D.isTotallyComplex.isComplex _)]
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro w hw
    simpa [norm_inv] using hinf w
  rw [lsContinuousHom_value]
  unfold SData.LS
  rw [norm_mul, hfinProd, hinfProd]
  norm_num

theorem lsContinuousHom_atComplex_value (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (w : InfinitePlace F) (z : ℂˣ) :
    ((lsContinuousHom D S ϑ (S.atComplex w z) : ℂˣ) : ℂ) =
      (((ϑ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z))⁻¹ : ℂˣ) : ℂ) := by
  rw [lsContinuousHom_value]
  unfold SData.LS
  have hfin : ∏ v : S.Sf,
      (((ϑ.loc v.1 (S.compU v (S.atComplex w z)))⁻¹ : ℂˣ) : ℂ) = 1 := by
    have hcomp (v : S.Sf) : S.compU v (S.atComplex w z) = 1 := by
      apply Units.ext
      simp [SData.compU, SData.atComplex]
    simp [hcomp]
  let g : InfinitePlace F → ℂ := fun w' => if hw' : w'.IsComplex then
    (((ϑ.locInf w' (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm.toMonoidHom
        (S.compC w' (S.atComplex w z))))⁻¹ : ℂˣ) : ℂ) else 1
  have hcomp : S.compC w (S.atComplex w z) = z := by
    apply Units.ext
    simp [SData.compC, SData.atComplex]
  have hprod : (∏ w' : InfinitePlace F, g w') =
      (((ϑ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z))⁻¹ : ℂˣ) : ℂ) := by
    rw [Finset.prod_eq_single w]
    · simp [g, D.isTotallyComplex.isComplex, hcomp]
    · intro w' hw' hne
      have hcomp' : S.compC w' (S.atComplex w z) = 1 := by
        apply Units.ext
        simp [SData.compC, SData.atComplex, hne]
      simp [g, D.isTotallyComplex.isComplex, hcomp']
    · intro hnot
      exact (hnot (Finset.mem_univ w)).elim
  rw [hfin, hprod]
  simp

def lambdaFinFSContinuousHom (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (v : S.Sf) : S.FSˣ →ₜ* ℂˣ := by
  let a := S.compU v (S.diagU (ε : Fˣ))
  let f : (v.1.adicCompletion F)ˣ →ₜ* ℂˣ :=
    ⟨hilbertLocalHom D H v.1 a, hilbertLocalHom_continuous D H v.1 a⟩
  exact f.comp (compUContinuousHom S v)

def lambdaContinuousHom (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) : S.FSˣ →ₜ* ℂˣ :=
  ∏ v : S.Sf, lambdaFinFSContinuousHom D S H ε v

theorem hilbertLocalHom_pow_six (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (a y : (v.adicCompletion F)ˣ) :
    hilbertLocalHom D H v a y ^ 6 = 1 := by
  have hroot : (H.hilb v a y : Fˣ) ^ 6 = 1 :=
    (mem_rootsOfUnity 6 (H.hilb v a y : Fˣ)).mp (H.hilb v a y).property
  have hrootInv : ((H.hilb v a y : Fˣ)⁻¹) ^ 6 = 1 := by
    rw [inv_pow, hroot]
    simp
  change (Units.map D.σ0.toMonoidHom ((H.hilb v a y)⁻¹)) ^ 6 = 1
  rw [← map_pow, hrootInv]
  simp

theorem lambdaFinFSContinuousHom_pow_six (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (v : S.Sf) (y : S.FSˣ) :
    lambdaFinFSContinuousHom D S H ε v y ^ 6 = 1 := by
  simp only [lambdaFinFSContinuousHom, ContinuousMonoidHom.coe_comp,
    Function.comp_apply]
  exact hilbertLocalHom_pow_six D H v.1
    (S.compU v (S.diagU (ε : Fˣ))) (S.compU v y)

theorem lambdaContinuousHom_pow_six (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (y : S.FSˣ) :
    lambdaContinuousHom D S H ε y ^ 6 = 1 := by
  classical
  rw [lambdaContinuousHom,
    continuousMonoidHom_finsetProd_apply (f := fun v => lambdaFinFSContinuousHom D S H ε v)
      (s := Finset.univ) y]
  rw [← Finset.prod_pow]
  simp [lambdaFinFSContinuousHom_pow_six]

theorem lambdaFiniteOrderHom_unitary {ζ : ℂˣ} (hζ : ζ ^ 6 = 1) :
    ‖(ζ : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one
  · exact congrArg (fun z : ℂˣ => (z : ℂ)) hζ
  · norm_num

theorem lambdaContinuousHom_unitary (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (y : S.FSˣ) :
    ‖((lambdaContinuousHom D S H ε y : ℂˣ) : ℂ)‖ = 1 :=
  lambdaFiniteOrderHom_unitary (lambdaContinuousHom_pow_six D S H ε y)

theorem lambdaContinuousHom_atComplex_one (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (w : InfinitePlace F) (z : ℂˣ) :
    lambdaContinuousHom D S H ε (S.atComplex w z) = 1 := by
  classical
  rw [lambdaContinuousHom,
    continuousMonoidHom_fintypeProd_apply
      (f := fun v : S.Sf => lambdaFinFSContinuousHom D S H ε v) (S.atComplex w z)]
  apply Finset.prod_eq_one
  intro v hv
  have hcomp : S.compU v (S.atComplex w z) = 1 := by
    apply Units.ext
    simp [SData.compU, SData.atComplex]
  change hilbertLocalHom D H v.1 (S.compU v (S.diagU (ε : Fˣ)))
      (S.compU v (S.atComplex w z)) = 1
  rw [hcomp]
  exact (hilbertLocalHom D H v.1 (S.compU v (S.diagU (ε : Fˣ)))).map_one

theorem lambdaContinuousHom_value (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (ε : S.US) (y : S.FSˣ) :
    ((lambdaContinuousHom D S H ε y : ℂˣ) : ℂ) = lambdaEpsilon D S H ε y := by
  classical
  rw [lambdaContinuousHom,
    continuousMonoidHom_finsetProd_apply (f := fun v => lambdaFinFSContinuousHom D S H ε v)
      (s := Finset.univ) y]
  simp [lambdaFinFSContinuousHom, hilbertLocalHom, lambdaEpsilon, SData.HS]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  change (((Units.map D.σ0.toMonoidHom
      (H.hilb v.1 (S.compU v (S.diagU (ε : Fˣ))) (S.compU v y)))⁻¹ : ℂˣ) : ℂ) =
    (D.σ0 (((H.hilb v.1 (S.compU v (S.diagU (ε : Fˣ))) (S.compU v y) : Fˣ) : F)))⁻¹
  rw [← map_inv]
  simp

theorem lambdaEpsilon_trivial_diagUS (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (A : AddCharData F)
    (ϑ : HeckeChar F) (houtside : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (ε γ : S.US) : lambdaEpsilon D S H ε (S.diagU (γ : Fˣ)) = 1 := by
  obtain ⟨Λ, G, hGfin, hΛunit, hΛangular, hθB, hGauss⟩ :=
    A1.gauss_characters D S A H Bd
  have hLambdaG : ∀ v : FinPlace F, v ∉ S.Sf → ∀ p : Fˣ,
      S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        gamma D S A 1 v.asIdeal (p : F) * gamma D S A 2 v.asIdeal (p : F) =
          -(Λ.primeValue v * G.primeValue v) := by
    intro v hv p hp hallowed
    exact ((hGauss v hv).2.2 p hp hallowed).2.2
  let η : HeckeChar F := G * Λ * ϑ
  have hvartheta : A1.vartheta Λ G η = ϑ := by
    apply ContinuousMonoidHom.ext
    intro x
    simp only [A1.vartheta, η, ContinuousMonoidHom.mul_apply,
      continuousMonoidHom_inv_apply, Units.val_mul, Units.val_inv]
    simp [mul_assoc]
  have hout : ∀ v : FinPlace F, v ∉ S.Sf → (A1.vartheta Λ G η).UnramifiedAt v := by
    intro v hv
    rw [hvartheta]
    exact houtside v hv
  have hidentity := rf_S_character_identity D S H Bd A Λ G η hLambdaG ε hout
  exact hidentity.2.1 γ

private theorem unit_isGen_top (S : SData F CE condη) (γ : S.US) :
    S.IsGen ((γ : Fˣ) : F) (⊤ : Ideal (𝓞 F)) := by
  have htopbot : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := by simp
  have htopnot (v : FinPlace F) : ¬ (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
    intro hle
    exact v.isPrime.ne_top (top_unique hle)
  refine ⟨⟨htopbot, ?_⟩, Units.ne_zero (γ : Fˣ), ?_⟩
  · intro v hv
    exact htopnot v
  · intro v hv
    have hval : v.valuation F ((γ : Fˣ) : F) = 1 := γ.property v hv
    have hprincipal : FractionalIdeal.count F v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) ((γ : Fˣ) : F)) = 0 := by
      rw [qs_nq0_count_spanSingleton_eq_neg_log_valuation v ((γ : Fˣ) : F)
        (Units.ne_zero (γ : Fˣ)), hval]
      simp
    have htop : FractionalIdeal.count F v
        ((⊤ : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
      rw [show (⊤ : Ideal (𝓞 F)) = 1 by exact Ideal.one_eq_top.symm]
      simpa using FractionalIdeal.count_one F v
    rw [hprincipal, htop]

theorem ls_diagUS_trivial (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (houtside : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (γ : S.US) : S.LS ϑ (S.diagU (γ : Fˣ)) = 1 := by
  have h := rf_heckeChar_idealValue_eq_LS_of_gen D S ϑ houtside
    (⊤ : Ideal (𝓞 F)) (γ : Fˣ) (unit_isGen_top S γ)
  have htop : ϑ.idealValue (⊤ : Ideal (𝓞 F)) = 1 := by
    unfold A1.HeckeChar.idealValue
    have hnf : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 F)) = 0 := by
      rw [← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
    simp [hnf]
  rw [htop] at h
  exact h.symm

theorem lsContinuousHom_diagUS_trivial (D : FieldData F) (S : SData F CE condη)
    (ϑ : HeckeChar F) (houtside : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (γ : S.US) : lsContinuousHom D S ϑ (S.diagU (γ : Fˣ)) = 1 := by
  apply Units.ext
  change ((lsContinuousHom D S ϑ (S.diagU (γ : Fˣ)) : ℂˣ) : ℂ) = 1
  rw [lsContinuousHom_value, ls_diagUS_trivial D S ϑ houtside]

theorem reflectionSChar_exists (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (Bd : BData S H) (A : AddCharData F)
    (ϑ : HeckeChar F) (hunit : ∀ x, ‖((ϑ x : ℂˣ) : ℂ)‖ = 1)
    (houtside : ∀ v, v ∉ S.Sf → ϑ.UnramifiedAt v)
    (hangular : HeckeChar.HasAngularType D ϑ) (ε : S.US) :
    ∃ L : SChar S, ∀ y : S.FSˣ,
      ((L.L y : ℂˣ) : ℂ) = rfSCharacter D S H ϑ ε y := by
  classical
  let χ : S.FSˣ →ₜ* ℂˣ :=
    lsContinuousHom D S ϑ * lambdaContinuousHom D S H ε
  let m₀ : InfinitePlace F → ℤ := fun w => Classical.choose (hangular w)
  have hm₀ (w : InfinitePlace F) : m₀ w = 1 ∨ m₀ w = -1 :=
    (Classical.choose_spec (hangular w)).1
  have hangle (w : InfinitePlace F) (z : ℂˣ) :
      ((ϑ.locInf w (Units.map
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (D.isTotallyComplex.isComplex w)).symm.toMonoidHom z) : ℂˣ) : ℂ) =
        ((z : ℂ) / ‖(z : ℂ)‖) ^ m₀ w :=
    (Classical.choose_spec (hangular w)).2 z
  let m : InfinitePlace F → ℤ := fun w => -m₀ w
  refine ⟨{
    L := χ.toMonoidHom
    cont := Units.continuous_val.comp χ.continuous_toFun
    unitary := ?_
    trivial_US := ?_
    m := m
    hm := ?_
    angular := ?_
  }, ?_⟩
  · intro y
    change ‖((lsContinuousHom D S ϑ y * lambdaContinuousHom D S H ε y : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, lsContinuousHom_unitary D S ϑ hunit y,
      lambdaContinuousHom_unitary D S H ε y]
    norm_num
  · intro γ hγ
    let γ' : S.US := ⟨γ, hγ⟩
    have hLS := lsContinuousHom_diagUS_trivial D S ϑ houtside γ'
    have hlam := lambdaEpsilon_trivial_diagUS D S H Bd A ϑ houtside ε γ'
    have hLSunit : lsContinuousHom D S ϑ (S.diagU (γ : Fˣ)) = 1 := by
      simpa [γ'] using hLS
    have hlamunit : lambdaContinuousHom D S H ε (S.diagU (γ : Fˣ)) = 1 := by
      apply Units.ext
      change ((lambdaContinuousHom D S H ε (S.diagU (γ : Fˣ)) : ℂˣ) : ℂ) = 1
      rw [lambdaContinuousHom_value, hlam]
    change χ (S.diagU γ) = 1
    dsimp [χ]
    rw [ContinuousMonoidHom.mul_apply, hLSunit, hlamunit]
    simp
  · intro w
    rcases hm₀ w with h | h
    · right
      simpa [m, h]
    · left
      simpa [m, h]
  · intro w z
    change ((χ (S.atComplex w z) : ℂˣ) : ℂ) = A1.omegaAng (m w) (z : ℂ)
    change ((lsContinuousHom D S ϑ (S.atComplex w z) : ℂˣ) : ℂ) *
        ((lambdaContinuousHom D S H ε (S.atComplex w z) : ℂˣ) : ℂ) = _
    rw [lambdaContinuousHom_atComplex_one]
    simp only [Units.val_mul, Units.val_one, mul_one]
    rw [lsContinuousHom_atComplex_value]
    rw [Units.val_inv_eq_inv_val, hangle w z]
    simp [A1.omegaAng, m, zpow_neg]
  · intro y
    change ((lsContinuousHom D S ϑ y * lambdaContinuousHom D S H ε y : ℂˣ) : ℂ) = _
    rw [Units.val_mul, lsContinuousHom_value, lambdaContinuousHom_value]
    rfl

end ArtinPrimitiveRoots.Proofs.A2_PRODUCERS
