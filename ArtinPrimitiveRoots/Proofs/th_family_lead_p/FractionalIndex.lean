import ArtinPrimitiveRoots.Proofs.th_family_lead_p.LocalBall

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

abbrev ThetaFractionalIdeal := FractionalIdeal (nonZeroDivisors (𝓞 F)) F

def fractionalIdealAddSubgroup (I : ThetaFractionalIdeal (F := F)) : AddSubgroup F :=
  (I : Submodule (𝓞 F) F).toAddSubgroup

def archFractionalIdealLattice (I : ThetaFractionalIdeal (F := F)) :
    AddSubgroup (InfinitePlace F → ℂ) :=
  (fractionalIdealAddSubgroup I).map infEmbA.toAddMonoidHom

def scalarFractionalIdeal (u : 𝓞 F) (I : ThetaFractionalIdeal (F := F)) :
    ThetaFractionalIdeal (F := F) :=
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F u) * I

theorem finite_archFractionalIdeal_scale_quotient (I : ThetaFractionalIdeal (F := F))
    (u : 𝓞 F) (hu : algebraMap (𝓞 F) F u ≠ 0) :
    Finite (archFractionalIdealLattice I ⧸
      (archFractionalIdealLattice (scalarFractionalIdeal u I)).comap
        (archFractionalIdealLattice I).subtype) := by
  classical
  let f : I →ₗ[ℤ] I := (LinearMap.lsmul (𝓞 F) I u).restrictScalars ℤ
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : I => (z : F)) hxy
    have hmul : (algebraMap (𝓞 F) F u) * (x : F) =
        (algebraMap (𝓞 F) F u) * (y : F) := by
      simpa [f, LinearMap.lsmul_apply, Algebra.smul_def] using h
    exact mul_left_cancel₀ hu hmul
  have hrank : Module.finrank ℤ (LinearMap.range f) = Module.finrank ℤ I :=
    LinearMap.finrank_range_of_inj hf
  let Nsub : Submodule ℤ I := LinearMap.range f
  haveI : Finite (I ⧸ Nsub) := Submodule.finiteQuotientOfFreeOfRankEq Nsub hrank
  let N : AddSubgroup I := Nsub.toAddSubgroup
  haveI : Finite (I ⧸ N) := by
    change Finite (I ⧸ Nsub)
    infer_instance
  let A : AddSubgroup (InfinitePlace F → ℂ) := archFractionalIdealLattice I
  let J : ThetaFractionalIdeal (F := F) := scalarFractionalIdeal u I
  let B : AddSubgroup (InfinitePlace F → ℂ) := archFractionalIdealLattice J
  let B' : AddSubgroup A := B.comap A.subtype
  let φ : I →+ A := {
    toFun := fun x => ⟨infEmbA (x : F), AddSubgroup.mem_map.mpr ⟨(x : F), x.2, rfl⟩⟩
    map_zero' := by ext; simp [infEmbA]
    map_add' := by intro x y; ext; simp [infEmbA]
  }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    exact infEmbA.injective (congrArg (fun z : A => (z : InfinitePlace F → ℂ)) hxy)
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := AddSubgroup.mem_map.mp y.2
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let e : I ≃+ A := AddEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hmap : N.map e.toAddMonoidHom = B' := by
    ext y
    constructor
    · rintro ⟨x, hxN, rfl⟩
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hxN
      change (e (f z) : A) ∈ B'
      change ((e (f z) : A) : InfinitePlace F → ℂ) ∈ B
      apply AddSubgroup.mem_map.mpr
      refine ⟨(f z : F), ?_, ?_⟩
      · change (f z : F) ∈
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
            (algebraMap (𝓞 F) F u) * I
        rw [FractionalIdeal.mem_singleton_mul]
        refine ⟨(z : F), z.2, ?_⟩
        simp [f, LinearMap.lsmul_apply, Algebra.smul_def, mul_comm]
      · rfl
    · intro hy
      change ((y : A) : InfinitePlace F → ℂ) ∈ B at hy
      rcases AddSubgroup.mem_map.mp hy with ⟨x, hxJ, hxy⟩
      have hxJ' : (x : F) ∈ J := hxJ
      change (x : F) ∈
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F))
          (algebraMap (𝓞 F) F u) * I at hxJ'
      rw [FractionalIdeal.mem_singleton_mul] at hxJ'
      obtain ⟨z, hzI, hxEq⟩ := hxJ'
      let zI : I := ⟨z, hzI⟩
      refine ⟨f zI, LinearMap.mem_range.mpr ⟨zI, rfl⟩, ?_⟩
      apply Subtype.ext
      change infEmbA (f zI : F) = (y : A)
      have hfz : (f zI : F) = x := by
        change (algebraMap (𝓞 F) F u) * z = x
        exact hxEq.symm
      calc
        infEmbA (f zI : F) = infEmbA x := congrArg infEmbA hfz
        _ = (y : A) := hxy
  let qEquiv : (I ⧸ N) ≃+ (A ⧸ B') := QuotientAddGroup.congr N B' e hmap
  exact Finite.of_equiv (I ⧸ N) qEquiv

end ArtinPrimitiveRoots.A1.Theta
