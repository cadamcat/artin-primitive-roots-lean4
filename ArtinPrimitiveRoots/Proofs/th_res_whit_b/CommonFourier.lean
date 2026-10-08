import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_adapted_domain_exists
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_FOURIER.theta_fourierCoeff
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs
import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.analyticFamily_rtr
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 500000

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped Classical Pointwise

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

private def lambdaFamilyFourierHyp (Fam : AnalyticFamily P G μ) :
    FourierFamilyHyp μ Fam.sec Fam.T0 where
  T0_eq := Fam.T0_eq
  fC_sph := Fam.fC_sph
  f_analytic := Fam.f_analytic
  M_analytic := Fam.M_analytic
  J_analytic := Fam.J_analytic
  level := Fam.level

/-- A principal subideal of three nonzero fractional ideals, represented as an image of a finite
quotient of the first ideal. -/
private theorem lambda_common_subideal
    (𝔞₀ 𝔞₁ 𝔞₂ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (h₀ : 𝔞₀ ≠ 0) (h₁ : 𝔞₁ ≠ 0) (h₂ : 𝔞₂ ≠ 0) :
    ∃ (I : Ideal (𝓞 F)) (K : Submodule (𝓞 F) 𝔞₀)
      (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F),
      K = I • (⊤ : Submodule (𝓞 F) 𝔞₀) ∧
      (𝔟 : Submodule (𝓞 F) F) = K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)) ∧
      𝔟 ≠ 0 ∧ 𝔟 ≤ 𝔞₀ ∧ 𝔟 ≤ 𝔞₁ ∧ 𝔟 ≤ 𝔞₂ ∧ Finite (𝔞₀ ⧸ K) := by
  classical
  obtain ⟨d, hd, hden⟩ := 𝔞₀.isFractional
  obtain ⟨r₁, hr₁, hr₁mem⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h₁
  obtain ⟨r₂, hr₂, hr₂mem⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger h₂
  let c : 𝓞 F := d * r₁ * r₂
  let cF : F := algebraMap (𝓞 F) F c
  let I : Ideal (𝓞 F) := Ideal.span {c}
  let K : Submodule (𝓞 F) 𝔞₀ := I • (⊤ : Submodule (𝓞 F) 𝔞₀)
  let bSub : Submodule (𝓞 F) F := K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F))
  have hdF : (algebraMap (𝓞 F) F d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hr₁F : algebraMap (𝓞 F) F r₁ ≠ 0 := by
    intro h
    exact hr₁ ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hr₂F : algebraMap (𝓞 F) F r₂ ≠ 0 := by
    intro h
    exact hr₂ ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hcF : cF ≠ 0 := by
    dsimp [cF, c]
    simp only [map_mul]
    exact mul_ne_zero (mul_ne_zero hdF hr₁F) hr₂F
  have hIne : I ≠ ⊥ := by
    intro h
    have hmem : c ∈ (⊥ : Ideal (𝓞 F)) := by
      rw [← h]
      exact Ideal.subset_span (by simp)
    exact hcF (by simpa [cF, c] using hmem)
  have hKle0 : K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)) ≤ 𝔞₀ := by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    ⟨bSub, FractionalIdeal.isFractional_of_le hKle0⟩
  have hbase1 : ∀ x : 𝔞₀, cF * (x : F) ∈ 𝔞₁ := by
    intro x
    obtain ⟨q, hq⟩ := hden (x : F) x.2
    have hq' : algebraMap (𝓞 F) F q = algebraMap (𝓞 F) F d * (x : F) := by
      simpa [Algebra.smul_def] using hq
    have hprod : cF * (x : F) =
        algebraMap (𝓞 F) F r₁ * algebraMap (𝓞 F) F (r₂ * q) := by
      dsimp [cF, c]
      simp only [map_mul]
      calc
        (algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F r₁ *
            algebraMap (𝓞 F) F r₂) * (x : F) =
          algebraMap (𝓞 F) F r₁ *
            (algebraMap (𝓞 F) F r₂ * (algebraMap (𝓞 F) F d * (x : F))) := by ring
        _ = algebraMap (𝓞 F) F r₁ *
            (algebraMap (𝓞 F) F r₂ * algebraMap (𝓞 F) F q) := by rw [← hq']
        _ = algebraMap (𝓞 F) F r₁ * algebraMap (𝓞 F) F (r₂ * q) := by rw [← map_mul]
    rw [hprod]
    have hs := Submodule.smul_mem (𝔞₁ : Submodule (𝓞 F) F) (r₂ * q) hr₁mem
    simpa [Algebra.smul_def, mul_comm] using hs
  have hbase2 : ∀ x : 𝔞₀, cF * (x : F) ∈ 𝔞₂ := by
    intro x
    obtain ⟨q, hq⟩ := hden (x : F) x.2
    have hq' : algebraMap (𝓞 F) F q = algebraMap (𝓞 F) F d * (x : F) := by
      simpa [Algebra.smul_def] using hq
    have hprod : cF * (x : F) =
        algebraMap (𝓞 F) F r₂ * algebraMap (𝓞 F) F (r₁ * q) := by
      dsimp [cF, c]
      simp only [map_mul]
      calc
        (algebraMap (𝓞 F) F d * algebraMap (𝓞 F) F r₁ *
            algebraMap (𝓞 F) F r₂) * (x : F) =
          algebraMap (𝓞 F) F r₂ *
            (algebraMap (𝓞 F) F r₁ * (algebraMap (𝓞 F) F d * (x : F))) := by ring
        _ = algebraMap (𝓞 F) F r₂ *
            (algebraMap (𝓞 F) F r₁ * algebraMap (𝓞 F) F q) := by rw [← hq']
        _ = algebraMap (𝓞 F) F r₂ * algebraMap (𝓞 F) F (r₁ * q) := by rw [← map_mul]
    rw [hprod]
    have hs := Submodule.smul_mem (𝔞₂ : Submodule (𝓞 F) F) (r₁ * q) hr₂mem
    simpa [Algebra.smul_def, mul_comm] using hs
  have hI_le1 : K ≤ (𝔞₁ : Submodule (𝓞 F) F).comap (Submodule.subtype 𝔞₀) := by
    change I • (⊤ : Submodule (𝓞 F) 𝔞₀) ≤ _
    refine Submodule.smul_le.mpr ?_
    intro z hz x hx
    have hz' : z ∈ Ideal.span ({c} : Set (𝓞 F)) := by simpa [I] using hz
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hz'
    have hcx : c • x ∈ (𝔞₁ : Submodule (𝓞 F) F).comap (Submodule.subtype 𝔞₀) := by
      change cF * (x : F) ∈ 𝔞₁
      exact hbase1 x
    have ht' : t * c = z := by simpa using ht
    rw [← ht', mul_smul]
    exact Submodule.smul_mem _ t hcx
  have hI_le2 : K ≤ (𝔞₂ : Submodule (𝓞 F) F).comap (Submodule.subtype 𝔞₀) := by
    change I • (⊤ : Submodule (𝓞 F) 𝔞₀) ≤ _
    refine Submodule.smul_le.mpr ?_
    intro z hz x hx
    have hz' : z ∈ Ideal.span ({c} : Set (𝓞 F)) := by simpa [I] using hz
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hz'
    have hcx : c • x ∈ (𝔞₂ : Submodule (𝓞 F) F).comap (Submodule.subtype 𝔞₀) := by
      change cF * (x : F) ∈ 𝔞₂
      exact hbase2 x
    have ht' : t * c = z := by simpa using ht
    rw [← ht', mul_smul]
    exact Submodule.smul_mem _ t hcx
  have hKle1 : bSub ≤ 𝔞₁ := by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hI_le1 hy
  have hKle2 : bSub ≤ 𝔞₂ := by
    intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hI_le2 hy
  have hcMulMem : ∃ x : F, x ≠ 0 ∧ x ∈ bSub := by
    have h₀bot : (𝔞₀ : Submodule (𝓞 F) F) ≠ ⊥ := by
      intro h
      apply h₀
      exact FractionalIdeal.coeToSubmodule_injective (by simpa using h)
    obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₀bot
    let x₀ : 𝔞₀ := ⟨x, hx⟩
    letI : AddCommGroup 𝔞₀ := Submodule.addCommGroup (𝔞₀ : Submodule (𝓞 F) F)
    letI : Module (𝓞 F) 𝔞₀ := Submodule.module (𝔞₀ : Submodule (𝓞 F) F)
    have hI : c ∈ I := Ideal.subset_span (by simp [I])
    have hK : c • x₀ ∈ K := Submodule.smul_mem_smul hI Submodule.mem_top
    have hcoe : cF * x ≠ 0 := mul_ne_zero hcF hxne
    have hval : (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)) (c • x₀) = cF * x := by
      simp [cF, c, x₀, Algebra.smul_def]
    refine ⟨cF * x, hcoe, ?_⟩
    rw [← hval]
    change (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)) (c • x₀) ∈
      K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F))
    exact Submodule.mem_map.mpr ⟨c • x₀, hK, rfl⟩
  have hbne : 𝔟 ≠ 0 := by
    intro heq
    have hbot : bSub = ⊥ := by
      have hval := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F =>
        (J : Submodule (𝓞 F) F)) heq
      simpa [𝔟] using hval
    rcases hcMulMem with ⟨x, hx, hmem⟩
    rw [hbot] at hmem
    exact hx (by simpa using hmem)
  have hfinite : Finite (𝔞₀ ⧸ K) := by
    letI : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hIne
    letI : Module.Finite (𝓞 F) 𝔞₀ :=
      Module.Finite.of_fg (FractionalIdeal.fg_of_isNoetherianRing (le_rfl) 𝔞₀)
    letI : Finite (𝔞₀ ⧸ (⊤ : Submodule (𝓞 F) 𝔞₀)) := inferInstance
    have htop : (⊤ : Submodule (𝓞 F) 𝔞₀).FG := Module.Finite.fg_top
    simpa [K] using (Submodule.finite_quotient_smul I htop)
  refine ⟨I, K, 𝔟, rfl, rfl, hbne, hKle0, hKle1, hKle2, hfinite⟩

private theorem lambda_infEmbA_injective : Function.Injective (infEmbA (F := F)) := by
  classical
  let w : InfinitePlace F := Classical.choice (inferInstance : Nonempty (InfinitePlace F))
  intro x y h
  apply w.embedding.injective
  exact congrFun h w

/-- Tile one adapted domain over a finite quotient to get a bounded domain for a common
subideal. -/
private theorem lambda_common_domain
    (𝔞₀ : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (K : Submodule (𝓞 F) 𝔞₀)
    (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (h𝔟 : (𝔟 : Submodule (𝓞 F) F) = K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)))
    (hfinite : Finite (𝔞₀ ⧸ K))
    (Pd : Set (InfinitePlace F → ℂ))
    (hPd : IsAddFundamentalDomain
      ((𝔞₀ : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Pd volume)
    (hbPd : Bornology.IsBounded Pd) (hmPd : MeasurableSet Pd) :
    ∃ Qd : Set (InfinitePlace F → ℂ), MeasurableSet Qd ∧ Bornology.IsBounded Qd ∧
      IsAddFundamentalDomain
        ((𝔟 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom) Qd volume := by
  classical
  let Γ : AddSubgroup (InfinitePlace F → ℂ) :=
    (𝔞₀ : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
  let Δ : AddSubgroup (InfinitePlace F → ℂ) :=
    (𝔟 : Submodule (𝓞 F) F).toAddSubgroup.map infEmbA.toAddMonoidHom
  letI : AddCommGroup 𝔞₀ := Submodule.addCommGroup (𝔞₀ : Submodule (𝓞 F) F)
  letI : Module (𝓞 F) 𝔞₀ := Submodule.module (𝔞₀ : Submodule (𝓞 F) F)
  letI : Fintype (𝔞₀ ⧸ K) := Fintype.ofFinite (𝔞₀ ⧸ K)
  let rep : (𝔞₀ ⧸ K) → 𝔞₀ := fun q =>
    Classical.choose ((Submodule.Quotient.mk_surjective K) q)
  have hrep (q : 𝔞₀ ⧸ K) : Submodule.Quotient.mk (rep q) = q :=
    Classical.choose_spec ((Submodule.Quotient.mk_surjective K) q)
  let Qd : Set (InfinitePlace F → ℂ) :=
    ⋃ q : 𝔞₀ ⧸ K, (-(infEmbA (rep q : F)) +ᵥ Pd)
  have htranslate_meas (q : 𝔞₀ ⧸ K) :
      MeasurableSet (-(infEmbA (rep q : F)) +ᵥ Pd) := by
    have heq : (-(infEmbA (rep q : F)) +ᵥ Pd) =
        (fun x => infEmbA (rep q : F) + x) ⁻¹' Pd := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_assoc]
    rw [heq]
    exact hmPd.preimage (measurable_const.add measurable_id)
  have hmeas : MeasurableSet Qd := by
    simpa [Qd] using MeasurableSet.iUnion htranslate_meas
  have htranslate_bound (q : 𝔞₀ ⧸ K) :
      Bornology.IsBounded (-(infEmbA (rep q : F)) +ᵥ Pd) := by
    have hcoordBound (w : InfinitePlace F) :
        Bornology.IsBounded (Function.eval w '' (-(infEmbA (rep q : F)) +ᵥ Pd)) := by
      let t : InfinitePlace F → ℂ := infEmbA (rep q : F)
      let tw : ℂ := t w
      obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp
        (hbPd.image_eval w)
      apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2
      refine ⟨‖tw‖ + R, ?_⟩
      intro z hz
      rcases hz with ⟨x, hx, hxeq⟩
      have hxPd : t + x ∈ Pd := by
        simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx
      have hz' : tw + z ∈ Function.eval w '' Pd := by
        refine ⟨t + x, hxPd, ?_⟩
        simpa [t, tw, Function.eval, Pi.add_apply, hxeq]
      have hn : ‖tw + z‖ ≤ R := by
        have := hR hz'
        simpa [Metric.mem_closedBall, dist_zero_right] using this
      have hzBound : ‖z‖ ≤ ‖tw‖ + R := by
        calc
          ‖z‖ = ‖-tw + (tw + z)‖ := by congr 1 <;> abel
          _ ≤ ‖tw‖ + ‖tw + z‖ := by simpa [norm_neg] using norm_add_le (-tw) (tw + z)
          _ ≤ ‖tw‖ + R := add_le_add_right hn (‖tw‖)
      simpa [Metric.mem_closedBall, dist_zero_right] using hzBound
    have hproduct : Bornology.IsBounded
        (Set.pi Set.univ (fun w => Function.eval w '' (-(infEmbA (rep q : F)) +ᵥ Pd))) :=
      Bornology.IsBounded.pi hcoordBound
    apply hproduct.subset
    intro x hx w hw
    exact ⟨x, hx, rfl⟩
  have hbound : Bornology.IsBounded Qd := by
    change Bornology.IsBounded (⋃ q : 𝔞₀ ⧸ K, -(infEmbA (rep q : F)) +ᵥ Pd)
    rw [Bornology.isBounded_iUnion]
    intro q
    exact htranslate_bound q
  have hΔleΓ : Δ ≤ Γ := by
    intro x hx
    rcases AddSubgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rw [h𝔟] at hy
    rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact AddSubgroup.mem_map.mpr ⟨z, z.2, rfl⟩
  have htranslate_union (δ : Δ) : δ +ᵥ Qd =
      ⋃ q : 𝔞₀ ⧸ K, ((δ : InfinitePlace F → ℂ) - infEmbA (rep q : F)) +ᵥ Pd := by
    ext x
    simp only [Qd, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have hq' := hq
      simp only [AddSubgroup.vadd_def, vadd_eq_add, neg_neg, sub_eq_add_neg] at hq' ⊢
      have hEq : infEmbA (rep q : F) + (-(δ : InfinitePlace F → ℂ) + x) =
          -((δ : InfinitePlace F → ℂ) - infEmbA (rep q : F)) + x := by abel
      exact hEq ▸ hq'
    · rintro ⟨q, hq⟩
      refine ⟨q, ?_⟩
      have hq' := hq
      simp only [AddSubgroup.vadd_def, vadd_eq_add, neg_neg, sub_eq_add_neg] at hq' ⊢
      have hEq : infEmbA (rep q : F) + (-(δ : InfinitePlace F → ℂ) + x) =
          -((δ : InfinitePlace F → ℂ) - infEmbA (rep q : F)) + x := by abel
      exact hEq.symm ▸ hq'
  have hcover : ∀ᵐ x ∂volume, ∃ δ : Δ, δ +ᵥ x ∈ Qd := by
    filter_upwards [hPd.ae_covers] with x hx
    rcases hx with ⟨γ, hγ⟩
    rcases AddSubgroup.mem_map.mp γ.2 with ⟨y, hy, hγeq⟩
    let y₀ : 𝔞₀ := ⟨y, hy⟩
    let q : 𝔞₀ ⧸ K := K.mkQ y₀
    have hquot : K.mkQ y₀ = K.mkQ (rep q) := by
      calc
        K.mkQ y₀ = q := rfl
        _ = K.mkQ (rep q) := (hrep q).symm
    have hdiff : y₀ - rep q ∈ K := (Submodule.Quotient.eq K).mp hquot
    let z : 𝔞₀ := y₀ - rep q
    have hz𝔟 : (z : F) ∈ 𝔟 := by
      change (z : F) ∈ (𝔟 : Submodule (𝓞 F) F)
      rw [h𝔟]
      exact Submodule.mem_map.mpr ⟨z, hdiff, rfl⟩
    let δ : Δ := ⟨infEmbA (z : F), AddSubgroup.mem_map.mpr ⟨z, hz𝔟, rfl⟩⟩
    have hydecomp : y = (rep q : F) + (z : F) := by
      change (y₀ : F) = (rep q : F) + ((y₀ - rep q : 𝔞₀) : F)
      rw [Submodule.coe_sub]
      abel
    have hdecomp : (γ : InfinitePlace F → ℂ) = infEmbA (rep q : F) + δ := by
      have hδval : (δ : InfinitePlace F → ℂ) = infEmbA (z : F) := rfl
      calc
        (γ : InfinitePlace F → ℂ) = infEmbA y := hγeq.symm
        _ = infEmbA ((rep q : F) + (z : F)) := by rw [hydecomp]
        _ = infEmbA (rep q : F) + infEmbA (z : F) := map_add infEmbA _ _
        _ = infEmbA (rep q : F) + δ := by rw [hδval]
    refine ⟨δ, ?_⟩
    change δ +ᵥ x ∈ ⋃ q : 𝔞₀ ⧸ K, -(infEmbA (rep q : F)) +ᵥ Pd
    apply Set.mem_iUnion.mpr ⟨q, ?_⟩
    change ∃ y, y ∈ Pd ∧ -infEmbA (rep q : F) + y = δ + x
    refine ⟨γ + x, hγ, ?_⟩
    have hγval : (γ : InfinitePlace F → ℂ) = infEmbA (rep q : F) + δ := hdecomp
    rw [hγval]
    abel
  have hdisj : Pairwise (fun δ₁ δ₂ : Δ =>
      AEDisjoint volume (δ₁ +ᵥ Qd) (δ₂ +ᵥ Qd)) := by
    intro δ₁ δ₂ hδ
    rw [htranslate_union δ₁, htranslate_union δ₂]
    simp only [AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    intro q₁ q₂
    let γ₁ : Γ := ⟨δ₁ - infEmbA (rep q₂ : F), AddSubgroup.sub_mem _
      (hΔleΓ δ₁.2) (AddSubgroup.mem_map.mpr ⟨rep q₂, (rep q₂).2, rfl⟩)⟩
    let γ₂ : Γ := ⟨δ₂ - infEmbA (rep q₁ : F), AddSubgroup.sub_mem _
      (hΔleΓ δ₂.2) (AddSubgroup.mem_map.mpr ⟨rep q₁, (rep q₁).2, rfl⟩)⟩
    have hγne : γ₁ ≠ γ₂ := by
      intro heq
      have hval : (δ₁ : InfinitePlace F → ℂ) - infEmbA (rep q₂ : F) =
          (δ₂ : InfinitePlace F → ℂ) - infEmbA (rep q₁ : F) := congrArg Subtype.val heq
      have hsum : (δ₁ : InfinitePlace F → ℂ) + infEmbA (rep q₁ : F) =
          (δ₂ : InfinitePlace F → ℂ) + infEmbA (rep q₂ : F) := by
        calc
          (δ₁ : InfinitePlace F → ℂ) + infEmbA (rep q₁ : F) =
              ((δ₁ : InfinitePlace F → ℂ) - infEmbA (rep q₂ : F)) +
                infEmbA (rep q₂ : F) + infEmbA (rep q₁ : F) := by abel
          _ = ((δ₂ : InfinitePlace F → ℂ) - infEmbA (rep q₁ : F)) +
                infEmbA (rep q₂ : F) + infEmbA (rep q₁ : F) := by rw [hval]
          _ = (δ₂ : InfinitePlace F → ℂ) + infEmbA (rep q₂ : F) := by abel
      have hdiff : infEmbA ((rep q₂ : 𝔞₀) - rep q₁ : F) = (δ₁ : _) - δ₂ := by
        rw [map_sub]
        calc
          infEmbA (rep q₂ : F) - infEmbA (rep q₁ : F) =
              (δ₂ + infEmbA (rep q₂ : F)) - δ₂ - infEmbA (rep q₁ : F) := by abel
          _ = (δ₁ + infEmbA (rep q₁ : F)) - δ₂ - infEmbA (rep q₁ : F) := by rw [hsum.symm]
          _ = δ₁ - δ₂ := by abel
      have hdiffΔ : infEmbA ((rep q₂ : 𝔞₀) - rep q₁ : F) ∈ Δ := by
        rw [hdiff]
        exact AddSubgroup.sub_mem _ δ₁.2 δ₂.2
      rcases AddSubgroup.mem_map.mp hdiffΔ with ⟨z, hz, hzeq⟩
      have hzinj : z = ((rep q₂ : 𝔞₀) - rep q₁ : F) :=
        lambda_infEmbA_injective hzeq
      have hdiff𝔟 : ((rep q₂ : 𝔞₀) - rep q₁ : F) ∈ 𝔟 := hzinj ▸ hz
      have hdiffSub : ((rep q₂ : 𝔞₀) - rep q₁) ∈ K := by
        have hdiffB' : ((rep q₂ : 𝔞₀) - rep q₁ : F) ∈
            K.map (Submodule.subtype (𝔞₀ : Submodule (𝓞 F) F)) := by
          rw [← h𝔟]
          exact hdiff𝔟
        rcases Submodule.mem_map.mp hdiffB' with ⟨u, hu, hueq⟩
        have hu' : u = (rep q₂ : 𝔞₀) - rep q₁ := Subtype.ext hueq
        simpa [hu'] using hu
      have hqeq : Submodule.Quotient.mk (rep q₂) = Submodule.Quotient.mk (rep q₁) :=
        (Submodule.Quotient.eq K).mpr hdiffSub
      have hq : q₁ = q₂ := by
        calc
          q₁ = Submodule.Quotient.mk (rep q₁) := (hrep q₁).symm
          _ = Submodule.Quotient.mk (rep q₂) := hqeq.symm
          _ = q₂ := hrep q₂
      subst q₂
      have hδval : (δ₁ : InfinitePlace F → ℂ) = δ₂ := by
        have h := congrArg (fun z : InfinitePlace F → ℂ =>
          z + infEmbA (rep q₁ : F)) hval
        simpa [sub_eq_add_neg, add_assoc] using h
      exact hδ (Subtype.ext hδval)
    exact hPd.aedisjoint hγne
  refine ⟨Qd, hmeas, hbound, ?_⟩
  exact ⟨hmeas.nullMeasurableSet, hcover, hdisj⟩

private theorem lambda_thetaCoeff_integrand_continuous
    {Fam : AnalyticFamily P G μ} (C : ContinuedEis Fam) (g : P.tc.G) :
    Continuous (fun x : InfinitePlace F → ℂ =>
      C.theta (nInf P x * g) * psiInf (-1) x) := by
  have hroot := C.jointRoots g
  have hθ : Continuous (fun x : InfinitePlace F → ℂ => C.theta (nInf P x * g)) := by
    have hcomp : Continuous (fun x : InfinitePlace F → ℂ =>
        C.theta (nInf P x * g * nInf P 0)) :=
      hroot.continuous.comp
        (Continuous.prodMk continuous_id
          (continuous_const : Continuous (fun _ : InfinitePlace F → ℂ => (0 : InfinitePlace F → ℂ))))
    have hn0 : nInf P (0 : InfinitePlace F → ℂ) = 1 := by
      unfold nInf
      change P.tc.nS 1 = 1
      exact map_one _
    simpa [hn0] using hcomp
  have hψ : Continuous (fun x : InfinitePlace F → ℂ => psiInf (-1) x) := by
    fun_prop [psiInf, psiC]
  exact hθ.mul hψ

private theorem lambda_torusCoeff_linear
    {Fam₀ Fam₁ Fam₂ : AnalyticFamily P G μ}
    (C₀ : ContinuedEis Fam₀) (C₁ : ContinuedEis Fam₁) (C₂ : ContinuedEis Fam₂)
    (g : P.tc.G) (Pd : Set (InfinitePlace F → ℂ)) (c : ℂ)
    (hPd : Bornology.IsBounded Pd) (hmPd : MeasurableSet Pd)
    (hθ : C₂.theta = C₀.theta + c • C₁.theta) :
    torusCoeff P C₂.theta g Pd 1 =
      torusCoeff P C₀.theta g Pd 1 + c • torusCoeff P C₁.theta g Pd 1 := by
  have hcompact : IsCompact (closure Pd) := hPd.isCompact_closure
  have hvol : volume Pd < (⊤ : ENNReal) :=
    (measure_mono subset_closure).trans_lt hcompact.measure_lt_top
  have hI₀ : IntegrableOn
      (fun x : InfinitePlace F → ℂ => C₀.theta (nInf P x * g) * psiInf (-1) x) Pd volume := by
    exact (lambda_thetaCoeff_integrand_continuous C₀ g).continuousOn.integrableOn_of_subset_isCompact
      hcompact hmPd subset_closure hvol.ne
  have hI₁ : IntegrableOn
      (fun x : InfinitePlace F → ℂ => C₁.theta (nInf P x * g) * psiInf (-1) x) Pd volume := by
    exact (lambda_thetaCoeff_integrand_continuous C₁ g).continuousOn.integrableOn_of_subset_isCompact
      hcompact hmPd subset_closure hvol.ne
  have hfun : (fun x : InfinitePlace F → ℂ => C₂.theta (nInf P x * g) * psiInf (-1) x) =
      fun x => C₀.theta (nInf P x * g) * psiInf (-1) x +
        c • (C₁.theta (nInf P x * g) * psiInf (-1) x) := by
    funext x
    rw [congrFun hθ (nInf P x * g)]
    simp [smul_eq_mul]
    ring
  let f₀ : (InfinitePlace F → ℂ) → ℂ := fun x => C₀.theta (nInf P x * g) * psiInf (-1) x
  let f₁ : (InfinitePlace F → ℂ) → ℂ := fun x => C₁.theta (nInf P x * g) * psiInf (-1) x
  have hIntegral :
      (∫ x in Pd, C₀.theta (nInf P x * g) * psiInf (-1) x +
          c • (C₁.theta (nInf P x * g) * psiInf (-1) x) ∂volume) =
        (∫ x in Pd, C₀.theta (nInf P x * g) * psiInf (-1) x ∂volume) +
          c • (∫ x in Pd, C₁.theta (nInf P x * g) * psiInf (-1) x ∂volume) := by
    change (∫ x, (f₀ + c • f₁) x ∂ volume.restrict Pd) =
      (∫ x, f₀ x ∂ volume.restrict Pd) + c • (∫ x, f₁ x ∂ volume.restrict Pd)
    have hI₁c : Integrable (c • f₁) (volume.restrict Pd) := hI₁.smul c
    calc
      (∫ x, (f₀ + c • f₁) x ∂ volume.restrict Pd) =
          ∫ x, f₀ x + (c • f₁) x ∂ volume.restrict Pd := rfl
      _ = (∫ x, f₀ x ∂ volume.restrict Pd) +
          ∫ x, (c • f₁) x ∂ volume.restrict Pd := integral_add hI₀ hI₁c
      _ = (∫ x, f₀ x ∂ volume.restrict Pd) + c •
          (∫ x, f₁ x ∂ volume.restrict Pd) := by
            congr 1
            exact MeasureTheory.integral_smul c f₁
  unfold torusCoeff
  rw [hfun, hIntegral]
  simp [smul_eq_mul, mul_add, mul_assoc]
  ring

/-- With one common adapted ideal and fundamental domain, the first residue coefficient is linear
in the continued residue function. -/
theorem thetaWhit_linear_common_domain
    (Fam₀ Fam₁ Fam₂ : AnalyticFamily P G μ)
    (C₀ : ContinuedEis Fam₀) (C₁ : ContinuedEis Fam₁) (C₂ : ContinuedEis Fam₂)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) (c : ℂ)
    (hθ : C₂.theta = C₀.theta + c • C₁.theta) :
    thetaWhit C₂ g = thetaWhit C₀ g + c • thetaWhit C₁ g := by
  classical
  obtain ⟨𝔞₀, Pd₀, hA₀, hm₀⟩ :=
    theta_adapted_domain_exists (lambdaFamilyFourierHyp Fam₀) g
  obtain ⟨𝔞₁, Pd₁, hA₁, _hm₁⟩ :=
    theta_adapted_domain_exists (lambdaFamilyFourierHyp Fam₁) g
  obtain ⟨𝔞₂, Pd₂, hA₂, _hm₂⟩ :=
    theta_adapted_domain_exists (lambdaFamilyFourierHyp Fam₂) g
  rcases hA₀ with ⟨h𝔞₀, hfix₀, hfund₀, hbounded₀, hψ₀⟩
  rcases hA₁ with ⟨h𝔞₁, hfix₁, _hfund₁, _hbounded₁, _hψ₁⟩
  rcases hA₂ with ⟨h𝔞₂, hfix₂, _hfund₂, _hbounded₂, _hψ₂⟩
  obtain ⟨I, K, 𝔟, hK, h𝔟, h𝔟ne, h𝔟₀, h𝔟₁, h𝔟₂, hfin⟩ :=
    lambda_common_subideal 𝔞₀ 𝔞₁ 𝔞₂ h𝔞₀ h𝔞₁ h𝔞₂
  obtain ⟨Qd, hmQ, hboundQ, hfundQ⟩ :=
    lambda_common_domain 𝔞₀ K 𝔟 h𝔟 hfin Pd₀ hfund₀ hbounded₀ hm₀
  have hfix₀Q : ∀ s ξ, ξ ∈ (𝔟 : Submodule (𝓞 F) F) → ∀ h,
      scalarOf P G (Fam₀.sec s).f (Fam₀.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G (Fam₀.sec s).f (Fam₀.sec s).fC h := by
    intro s ξ hξ z
    exact hfix₀ s ξ (h𝔟₀ hξ) z
  have hfix₁Q : ∀ s ξ, ξ ∈ (𝔟 : Submodule (𝓞 F) F) → ∀ h,
      scalarOf P G (Fam₁.sec s).f (Fam₁.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G (Fam₁.sec s).f (Fam₁.sec s).fC h := by
    intro s ξ hξ z
    exact hfix₁ s ξ (h𝔟₁ hξ) z
  have hfix₂Q : ∀ s ξ, ξ ∈ (𝔟 : Submodule (𝓞 F) F) → ∀ h,
      scalarOf P G (Fam₂.sec s).f (Fam₂.sec s).fC
        (h * (g⁻¹ * nFin P ξ * g)) = scalarOf P G (Fam₂.sec s).f (Fam₂.sec s).fC h := by
    intro s ξ hξ z
    exact hfix₂ s ξ (h𝔟₂ hξ) z
  have hψQ : ∀ ξ ∈ (𝔟 : Submodule (𝓞 F) F), psiInf 1 (infEmbA ξ) = 1 := by
    intro ξ hξ
    exact hψ₀ ξ (h𝔟₀ hξ)
  have hθ₀ := laws.fourierCoeff Fam₀ C₀ g 𝔟 h𝔟ne hfix₀Q Qd hfundQ hboundQ 1 hψQ
  have hθ₁ := laws.fourierCoeff Fam₁ C₁ g 𝔟 h𝔟ne hfix₁Q Qd hfundQ hboundQ 1 hψQ
  have hθ₂ := laws.fourierCoeff Fam₂ C₂ g 𝔟 h𝔟ne hfix₂Q Qd hfundQ hboundQ 1 hψQ
  have hdiag : diagGL (1 : Fˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  have hW₀ : thetaWhit C₀ g = torusCoeff P C₀.theta g Qd 1 := by
    simpa [hdiag] using hθ₀.symm
  have hW₁ : thetaWhit C₁ g = torusCoeff P C₁.theta g Qd 1 := by
    simpa [hdiag] using hθ₁.symm
  have hW₂ : thetaWhit C₂ g = torusCoeff P C₂.theta g Qd 1 := by
    simpa [hdiag] using hθ₂.symm
  calc
    thetaWhit C₂ g = torusCoeff P C₂.theta g Qd 1 := hW₂
    _ = torusCoeff P C₀.theta g Qd 1 + c • torusCoeff P C₁.theta g Qd 1 :=
      lambda_torusCoeff_linear C₀ C₁ C₂ g Qd c hboundQ hmQ hθ
    _ = thetaWhit C₀ g + c • thetaWhit C₁ g := by rw [← hW₀, ← hW₁]

theorem thetaWhit_eq_of_theta_eq
    (Fam₀ Fam₁ : AnalyticFamily P G μ) (C₀ : ContinuedEis Fam₀) (C₁ : ContinuedEis Fam₁)
    (g : P.tc.G) (laws : ThetaResidueLaws P G μ) (hθ : C₀.theta = C₁.theta) :
    thetaWhit C₀ g = thetaWhit C₁ g := by
  have hlinear : C₁.theta = C₀.theta + (0 : ℂ) • C₀.theta := by simpa using hθ.symm
  have h := thetaWhit_linear_common_domain Fam₀ Fam₀ Fam₁ C₀ C₀ C₁ g laws 0 hlinear
  simpa using h.symm

private theorem lambda_scalarOf_translate_family
    (Fam Fam' : AnalyticFamily P G μ) (v0 : FinPlace F)
    (h : (P.loc v0).L) (hOff : ∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v)
    (hAt : ∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0))
    (s : ℂ) (x : P.RP) :
    scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC (P.q x) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * P.emb v0 h) := by
  classical
  have hL := scalarOf_q P G (Fam'.sec s) x
  have hR := scalarOf_q P G (Fam.sec s) (x * P.incl v0 h)
  have hprod : (∏ᶠ w : FinPlace F,
      G.lam w ((Fam'.sec s).f w (P.compF w x))) =
      ∏ᶠ w : FinPlace F,
        G.lam w ((Fam.sec s).f w (P.compF w (x * P.incl v0 h))) := by
    apply finprod_congr
    intro w
    by_cases hw : w = v0
    · subst w
      have hcomp : P.compF v0 (x * P.incl v0 h) = P.compF v0 x * h := by
        rw [map_mul, P.incl_compF]
      have hlocal := congrFun (hAt s) (P.compF v0 x)
      simpa [rtr, hcomp] using congrArg (G.lam v0) hlocal
    · have hincl : P.compF w (P.incl v0 h) = 1 := P.incl_compF_other v0 w (Ne.symm hw) h
      have hlocal := hOff s w hw
      simp [map_mul, hincl, hlocal]
  have harch : (∏ w : InfinitePlace F,
      (Fam'.sec s).fC w (P.compC w x)) =
      ∏ w : InfinitePlace F, (Fam.sec s).fC w (P.compC w (x * P.incl v0 h)) := by
    apply Finset.prod_congr rfl
    intro w hw
    have hincl : P.compC w (P.incl v0 h) = 1 := P.incl_compC v0 h w
    have hfc : (Fam'.sec s).fC w = (Fam.sec s).fC w := by
      rw [Fam'.fC_sph s w, Fam.fC_sph s w]
    simp [hfc, map_mul, hincl]
  have hq : P.q (x * P.incl v0 h) = P.q x * P.emb v0 h := by
    rw [map_mul, P.q_incl]
  calc
    scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC (P.q x) =
        (∏ᶠ w : FinPlace F, G.lam w ((Fam'.sec s).f w (P.compF w x))) *
          ∏ w : InfinitePlace F, (Fam'.sec s).fC w (P.compC w x) := hL.2
    _ = (∏ᶠ w : FinPlace F,
          G.lam w ((Fam.sec s).f w (P.compF w (x * P.incl v0 h)))) *
          ∏ w : InfinitePlace F, (Fam.sec s).fC w (P.compC w (x * P.incl v0 h)) := by
            rw [hprod, harch]
    _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * P.emb v0 h) := by
            rw [← hq]
            exact hR.2.symm

/-- A local right translate at an exterior finite place translates the global residue
coefficient on the adelic argument. -/
theorem thetaWhit_translate_family
    (Fam Fam' : AnalyticFamily P G μ) (v0 : FinPlace F)
    (h : (P.loc v0).L)
    (hOff : ∀ s v, v ≠ v0 → (Fam'.sec s).f v = (Fam.sec s).f v)
    (hAt : ∀ s, (Fam'.sec s).f v0 = rtr h ((Fam.sec s).f v0))
    (C : ContinuedEis Fam) (C' : ContinuedEis Fam') (g : P.tc.G)
    (laws : ThetaResidueLaws P G μ) :
    thetaWhit C' g = thetaWhit C (g * P.emb v0 h) := by
  classical
  let E := P.emb v0 h
  have hscalar (s : ℂ) (y : P.tc.G) :
      scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC y =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC (y * E) := by
    obtain ⟨x, hx⟩ := P.q_surj y
    calc
      scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC y =
          scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC (P.q x) := by rw [← hx]
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (P.q x * E) := by
        simpa [E] using lambda_scalarOf_translate_family Fam Fam' v0 h hOff hAt s x
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (y * E) := by rw [hx]
  obtain ⟨𝔞, Pd, hAdapt, hmPd⟩ :=
    theta_adapted_domain_exists (lambdaFamilyFourierHyp Fam) (g * E)
  rcases hAdapt with ⟨h𝔞, hfix, hPd, hb, hψ⟩
  have hfix' : ∀ s, ∀ ξ, ξ ∈ (𝔞 : Submodule (𝓞 F) F) → ∀ k,
      scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC
          (k * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC k := by
    intro s ξ hξ k
    have hgroup : (k * (g⁻¹ * nFin P ξ * g)) * E =
        (k * E) * ((g * E)⁻¹ * nFin P ξ * (g * E)) := by group
    calc
      scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC
          (k * (g⁻¹ * nFin P ξ * g)) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          ((k * (g⁻¹ * nFin P ξ * g)) * E) := hscalar s _
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC
          ((k * E) * ((g * E)⁻¹ * nFin P ξ * (g * E))) := by rw [hgroup]
      _ = scalarOf P G (Fam.sec s).f (Fam.sec s).fC (k * E) := hfix s ξ hξ (k * E)
      _ = scalarOf P G (Fam'.sec s).f (Fam'.sec s).fC k := (hscalar s k).symm
  have hθ : ∀ z : P.tc.G, C'.theta z = C.theta (z * E) :=
    (laws.linearTranslate v0 Fam Fam' Fam' C C' C').2 h hOff hAt
  have hν : ∀ ξ ∈ (𝔞 : Submodule (𝓞 F) F),
      psiInf ((1 : Fˣ) : F) (infEmbA ξ) = 1 := by
    intro ξ hξ
    simpa using hψ ξ hξ
  have hCoeff' := laws.fourierCoeff Fam' C' g 𝔞 h𝔞 hfix' Pd hPd hb (1 : Fˣ) hν
  have hCoeff := laws.fourierCoeff Fam C (g * E) 𝔞 h𝔞 hfix Pd hPd hb (1 : Fˣ) hν
  have hdiag : diagGL (1 : Fˣ) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  have hWhit' : thetaWhit C' g = torusCoeff P C'.theta g Pd 1 := by
    simpa [hdiag] using hCoeff'.symm
  have hWhit : thetaWhit C (g * E) = torusCoeff P C.theta (g * E) Pd 1 := by
    simpa [hdiag] using hCoeff.symm
  have htorus : torusCoeff P C'.theta g Pd 1 = torusCoeff P C.theta (g * E) Pd 1 := by
    unfold torusCoeff
    have hfun : (fun x => C'.theta (nInf P x * g) * psiInf (-1) x) =
        fun x => C.theta (nInf P x * (g * E)) * psiInf (-1) x := by
      funext x
      rw [hθ]
      simp [mul_assoc]
    rw [hfun]
  calc
    thetaWhit C' g = torusCoeff P C'.theta g Pd 1 := hWhit'
    _ = torusCoeff P C.theta (g * E) Pd 1 := htorus
    _ = thetaWhit C (g * E) := hWhit.symm

end ArtinPrimitiveRoots.A1.Theta
