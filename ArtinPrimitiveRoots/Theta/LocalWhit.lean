import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Shared
import ArtinPrimitiveRoots.Theta.LocalInt

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-LOCAL-WHIT -/

section LocalWhit

open MeasureTheory

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

local instance localCoeff_residue_maximal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance localCoeff_residue_field (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

/-- The space of sections of `I(T, s)` (def:ind as a subspace). -/
def sectionSpace (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) :
    Submodule ℂ (L.L → T.V) where
  carrier := {f | IsSection L T s f}
  add_mem' := by
    intro f g hf hg
    change IsSection L T s f at hf
    change IsSection L T s g at hg
    rcases hf with ⟨hf₁, hf₂, mf, hmf, hfr⟩
    rcases hg with ⟨hg₁, hg₂, mg, hmg, hgr⟩
    refine ⟨?_, ?_, max mf mg, le_trans hmf (Nat.le_max_left _ _), ?_⟩
    · intro x y h
      simp only [Pi.add_apply, hf₁, hg₁, map_add, smul_add]
    · intro ζ h
      calc
        (f + g) (L.z ζ * h) = f (L.z ζ * h) + g (L.z ζ * h) := rfl
        _ = ((ζ : ℂˣ) : ℂ) • f h + ((ζ : ℂˣ) : ℂ) • g h := by rw [hf₂, hg₂]
        _ = ((ζ : ℂˣ) : ℂ) • (f h + g h) := (smul_add _ _ _).symm
    · intro h k hk
      have hkf : k ∈ L.Kc mf := L.Kc_anti mf (max mf mg) hmf
        (Nat.le_max_left _ _) hk
      have hkg : k ∈ L.Kc mg := L.Kc_anti mg (max mf mg) hmg
        (Nat.le_max_right _ _) hk
      simp [Pi.add_apply, hfr h k hkf, hgr h k hkg]
  zero_mem' := by
    refine ⟨?_, ?_, L.m0, le_rfl, ?_⟩
    · intro x y g
      simp
    · intro ζ g
      simp
    · intro g k hk
      simp
  smul_mem' := by
    intro c f hf
    change IsSection L T s f at hf
    rcases hf with ⟨hf₁, hf₂, m, hm, hfr⟩
    refine ⟨?_, ?_, m, hm, ?_⟩
    · intro x y g
      change c • f (L.n (Multiplicative.ofAdd x) * L.a y * g) =
        ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (c • f g)
      rw [hf₁, map_smul]
      exact smul_comm c ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) (T.σa y (f g))
    · intro ζ g
      change c • f (L.z ζ * g) = ((ζ : ℂˣ) : ℂ) • (c • f g)
      rw [hf₂]
      exact smul_comm c ((ζ : ℂˣ) : ℂ) (f g)
    · intro g k hk
      simp [Pi.smul_apply, hfr g k hk]

/-- A subspace of functions stable under right translation. -/
def IsRtrStable {L : FinLocalCover D H v} {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ (L.L → V)) : Prop :=
  ∀ f ∈ W, ∀ g : L.L, rtr g f ∈ W

/-- **def:whittaker**: a Whittaker functional with character `ψ_v` on a subspace `W`. -/
def IsWhittakerOn (L : FinLocalCover D H v) (A : AddCharData F) {V : Type} [AddCommGroup V]
    [Module ℂ V] (W : Submodule ℂ (L.L → V)) (Λ : (L.L → V) →ₗ[ℂ] ℂ) : Prop :=
  ∀ f ∈ W, ∀ t : v.adicCompletion F, Λ (rtr (L.n (Multiplicative.ofAdd t)) f) = A.ψ v t * Λ f

/-- **wh:distribution**: a `ψ`-equivariant linear functional on locally constant compactly
supported `φ : K → V` is `φ ↦ c(∫ ψ(-t) φ(t) dt)`. -/
theorem psi_equivariant_functional (A : AddCharData F) (μ : LocHaar v) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (Λ : (v.adicCompletion F → V) →ₗ[ℂ] ℂ)
    (hΛ : ∀ φ : v.adicCompletion F → V, IsLocallyConstant φ → HasCompactSupport φ →
      ∀ t, Λ (fun x => φ (x + t)) = A.ψ v t * Λ φ) :
    ∃ c : V →ₗ[ℂ] ℂ, ∀ φ : v.adicCompletion F → V, IsLocallyConstant φ → HasCompactSupport φ →
      Λ φ = c (∫ t, A.ψ v (-t) • φ t ∂μ.μ) := by
  sorry

/-- **wh:small-cell**: a section vanishing at `1` is a big-cell section. -/
theorem section_eq_bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (f : L.L → T.V) (hf : IsSection L T s f) (h1 : f 1 = 0) :
    ∃ φ : v.adicCompletion F → T.V, IsLocallyConstant φ ∧ HasCompactSupport φ ∧
      f = bigCell L T s φ := by
  sorry

/-- **wh:two-cell** (KP Cor. I.3.4/Lemma I.3.2 replaced): every Whittaker functional on `I(T, s)`
is `c ∘ 𝒥` (every `s ∈ ℂ`). -/
theorem whittaker_twoCell (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (Λ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (hΛ : IsWhittakerOn L A (sectionSpace L T s) Λ) :
    ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ sectionSpace L T s, Λ f = c (jacquet L A μ f) := by
  sorry

/-- **wh:coinvariants** (left exactness of `ψ`-twisted coinvariants, Bernstein–Zelevinsky): a
Whittaker functional on an `rtr`-stable subspace of `I(T, s)` extends to `I(T, s)`. -/
theorem whittaker_extend (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (s : ℂ) (W : Submodule ℂ (L.L → T.V)) (hW : W ≤ sectionSpace L T s) (hst : IsRtrStable W)
    (Λ : (L.L → T.V) →ₗ[ℂ] ℂ) (hΛ : IsWhittakerOn L A W Λ) :
    ∃ Λ' : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (sectionSpace L T s) Λ' ∧
      ∀ f ∈ W, Λ' f = Λ f := by
  sorry

/-- **wh:local-coefficient**: `𝒥 ∘ M(s) = τ(s) ∘ 𝒥` on `I(T, s)`, `Re s > 0`. -/
theorem local_coefficient (L : FinLocalCover D H v) (T : TorusRep D H v) (A : AddCharData F)
    (μ : LocHaar v) (s : ℂ) (hs : 0 < s.re) :
    ∃ τ : T.V →ₗ[ℂ] T.V, ∀ f ∈ sectionSpace L T s,
      jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f) := by
  classical
  have hV : T.weyl.V = T.V := rfl
  cases hV
  have hAdd : T.weyl.nacg.toAddCommMonoid = T.nacg.toAddCommMonoid := rfl
  have hModule : T.weyl.nsp.toModule = T.nsp.toModule := rfl
  cases hAdd
  let P : Submodule ℂ (L.L → T.V) := sectionSpace L T s
  let Q : Submodule ℂ (L.L → T.V) := sectionSpace L T.weyl (-s)
  have hJzero (R : TorusRep D H v) (r : ℂ) :
      jacquet L A μ (0 : L.L → R.V) = 0 := by
    have h0 : IsSection L R r (0 : L.L → R.V) := by
      change (0 : L.L → R.V) ∈ sectionSpace L R r
      exact Submodule.zero_mem _
    have h := jacquet_linear L R A μ r 0 0 h0 h0 1
    have h' : jacquet L A μ (0 : L.L → R.V) + 0 =
        jacquet L A μ (0 : L.L → R.V) + jacquet L A μ (0 : L.L → R.V) := by
      simpa using h
    exact (add_left_cancel h').symm
  let Js : P →ₗ[ℂ] T.V := {
    toFun := fun f => jacquet L A μ f.1
    map_add' := by
      intro f g
      change jacquet L A μ (f.1 + g.1) = jacquet L A μ f.1 + jacquet L A μ g.1
      have hf : IsSection L T s f.1 := by
        change f.1 ∈ sectionSpace L T s
        exact f.2
      have hg : IsSection L T s g.1 := by
        change g.1 ∈ sectionSpace L T s
        exact g.2
      simpa using jacquet_linear L T A μ s f.1 g.1 hf hg 1
    map_smul' := by
      intro c f
      change jacquet L A μ (c • f.1) = c • jacquet L A μ f.1
      have h0 : IsSection L T s (0 : L.L → T.V) := by
        change (0 : L.L → T.V) ∈ sectionSpace L T s
        exact Submodule.zero_mem _
      have hf : IsSection L T s f.1 := by
        change f.1 ∈ sectionSpace L T s
        exact f.2
      have h := jacquet_linear L T A μ s 0 f.1 h0 hf c
      rw [hJzero T s] at h
      simpa using h
  }
  let Jt : Q →ₗ[ℂ] T.V := {
    toFun := fun f => jacquet L A μ f.1
    map_add' := by
      intro f g
      change jacquet L A μ (f.1 + g.1) = jacquet L A μ f.1 + jacquet L A μ g.1
      have hf : IsSection L T.weyl (-s) f.1 := by
        change f.1 ∈ sectionSpace L T.weyl (-s)
        exact f.2
      have hg : IsSection L T.weyl (-s) g.1 := by
        change g.1 ∈ sectionSpace L T.weyl (-s)
        exact g.2
      have h := jacquet_linear L T.weyl A μ (-s) f.1 g.1 hf hg 1
      rw [hModule] at h
      have hfg : f.1 + g.1 = f.1 + (1 : ℂ) • g.1 := by
        rw [one_smul]
      calc
        jacquet L A μ (f.1 + g.1) = jacquet L A μ (f.1 + (1 : ℂ) • g.1) := by rw [hfg]
        _ = jacquet L A μ f.1 + (1 : ℂ) • jacquet L A μ g.1 := h
        _ = jacquet L A μ f.1 + jacquet L A μ g.1 := by rw [one_smul]
    map_smul' := by
      intro c f
      change jacquet L A μ (c • f.1) = c • jacquet L A μ f.1
      have h0 : IsSection L T.weyl (-s) (0 : L.L → T.V) := by
        change (0 : L.L → T.V) ∈ sectionSpace L T.weyl (-s)
        exact Submodule.zero_mem _
      have hf : IsSection L T.weyl (-s) f.1 := by
        change f.1 ∈ sectionSpace L T.weyl (-s)
        exact f.2
      have h := jacquet_linear L T.weyl A μ (-s) 0 f.1 h0 hf c
      rw [zero_add] at h
      rw [hModule] at h
      rw [hJzero T.weyl (-s)] at h
      exact h.trans (zero_add _)
  }
  let M : P →ₗ[ℂ] Q := {
    toFun := fun f => ⟨intertwine L μ f.1,
      (intertwine_isSection L T μ s hs f.1 (by
        change f.1 ∈ sectionSpace L T s
        exact f.2)).2⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext y
      have hf : IsSection L T s f.1 := by
        change f.1 ∈ sectionSpace L T s
        exact f.2
      have hg : IsSection L T s g.1 := by
        change g.1 ∈ sectionSpace L T s
        exact g.2
      have hfI := (intertwine_isSection L T μ s hs f.1 hf).1
      have hgI := (intertwine_isSection L T μ s hs g.1 hg).1
      simp only [intertwine]
      exact integral_add (hfI y) (hgI y)
    map_smul' := by
      intro c f
      apply Subtype.ext
      change intertwine L μ (c • f.1) = c • intertwine L μ f.1
      funext y
      change (∫ x, c • f.1 (L.w * L.n (Multiplicative.ofAdd x) * y) ∂μ.μ) =
        c • ∫ x, f.1 (L.w * L.n (Multiplicative.ofAdd x) * y) ∂μ.μ
      exact integral_smul c _
  }
  let b := Module.finBasis ℂ T.V
  let coordMap (i : Fin (Module.finrank ℂ T.V)) : P →ₗ[ℂ] ℂ :=
    (b.coord i).comp (Jt.comp M)
  let bigLambda : (i : Fin (Module.finrank ℂ T.V)) → (L.L → T.V) →ₗ[ℂ] ℂ :=
    fun i => Classical.choose (LinearMap.exists_extend (coordMap i))
  have hΛext (i : Fin (Module.finrank ℂ T.V)) :
      (bigLambda i).comp P.subtype = coordMap i :=
    Classical.choose_spec (LinearMap.exists_extend (coordMap i))
  have hΛat (i : Fin (Module.finrank ℂ T.V)) (f : P) :
      bigLambda i f.1 = coordMap i f := by
    have h := congrArg (fun g : P →ₗ[ℂ] ℂ => g f) (hΛext i)
    simpa only [LinearMap.comp_apply, Submodule.coe_subtype] using h
  have hWh (i : Fin (Module.finrank ℂ T.V)) : IsWhittakerOn L A P (bigLambda i) := by
    intro f hf t
    have hfS : IsSection L T s f := by
      change f ∈ P
      exact hf
    have hfr : IsSection L T s (rtr (L.n (Multiplicative.ofAdd t)) f) :=
      hfS.rtr (L.n (Multiplicative.ofAdd t))
    have hMf : IsSection L T.weyl (-s) (intertwine L μ f) :=
      (intertwine_isSection L T μ s hs f hfS).2
    have hJ := (jacquet_equiv L T.weyl A μ (-s) (intertwine L μ f) hMf).1 t
    have hJ' : jacquet L A μ (rtr (L.n (Multiplicative.ofAdd t))
        (intertwine L μ f)) = A.ψ v t • jacquet L A μ (intertwine L μ f) := by
      rw [← hModule]
      exact hJ
    have hcoord :
        b.coord i (jacquet L A μ (intertwine L μ (rtr (L.n (Multiplicative.ofAdd t)) f))) =
          A.ψ v t * b.coord i (jacquet L A μ (intertwine L μ f)) := by
      have hcomm := intertwine_rtr L μ f (L.n (Multiplicative.ofAdd t))
      rw [hcomm, hJ']
      simp only [map_smul, smul_eq_mul]
    calc
      bigLambda i (rtr (L.n (Multiplicative.ofAdd t)) f) =
          coordMap i ⟨rtr (L.n (Multiplicative.ofAdd t)) f, hfr⟩ := by
        simpa only [Submodule.coe_subtype] using hΛat i ⟨rtr (L.n (Multiplicative.ofAdd t)) f, hfr⟩
      _ = b.coord i (jacquet L A μ (intertwine L μ (rtr (L.n (Multiplicative.ofAdd t)) f))) := rfl
      _ = A.ψ v t * b.coord i (jacquet L A μ (intertwine L μ f)) := hcoord
      _ = A.ψ v t * coordMap i ⟨f, hfS⟩ := rfl
      _ = A.ψ v t * bigLambda i f := by rw [hΛat i ⟨f, hfS⟩]
  let c : (i : Fin (Module.finrank ℂ T.V)) → T.V →ₗ[ℂ] ℂ := fun i =>
    Classical.choose (whittaker_twoCell L T A μ s (bigLambda i) (hWh i))
  have hc (i : Fin (Module.finrank ℂ T.V)) :
      ∀ f ∈ P, bigLambda i f = c i (jacquet L A μ f) :=
    Classical.choose_spec (whittaker_twoCell L T A μ s (bigLambda i) (hWh i))
  have hcoeff (i : Fin (Module.finrank ℂ T.V)) (f : P) :
      b.coord i (jacquet L A μ (intertwine L μ f.1)) = c i (Js f) := by
    calc
      b.coord i (jacquet L A μ (intertwine L μ f.1)) = coordMap i f := rfl
      _ = bigLambda i f.1 := (hΛat i f).symm
      _ = c i (jacquet L A μ f.1) := hc i f.1 f.2
      _ = c i (Js f) := rfl
  let τ : T.V →ₗ[ℂ] T.V := {
    toFun := fun z => ∑ i, c i z • b i
    map_add' := by
      intro x y
      simp only [map_add, add_smul]
      exact Finset.sum_add_distrib
    map_smul' := by
      intro a x
      simp only [map_smul, smul_eq_mul]
      calc
        (∑ i, (a * c i x) • b i) = ∑ i, a • (c i x • b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [smul_smul]
        _ = a • ∑ i, c i x • b i := (Finset.smul_sum).symm
  }
  have hτcoord (i : Fin (Module.finrank ℂ T.V)) (z : T.V) :
      b.coord i (τ z) = c i z := by
    change b.repr (∑ j, c j z • b j) i = c i z
    exact congrArg (fun a => a i) (b.repr_sum_self fun j => c j z)
  refine ⟨τ, ?_⟩
  intro f hf
  let x : P := ⟨f, hf⟩
  apply b.ext_elem
  intro i
  calc
    b.repr (jacquet L A μ (intertwine L μ f)) i = c i (Js x) := by
      simpa only [b.coord_apply] using hcoeff i x
    _ = b.repr (τ (Js x)) i := by
      symm
      simpa only [b.coord_apply] using hτcoord i (Js x)

/-- The diagonal coefficient `A_k(s) = (1 - q⁻¹) q^{-2 m₀ s}/(1 - q^{-6s})`, `m₀ ≡ -k mod 3`. -/
def tauDiag (v : FinPlace F) (s : ℂ) (k : ZMod 3) : ℂ :=
  (1 - (qv v : ℂ)⁻¹) * (qv v : ℂ) ^ (-2 * (((-k).val : ℕ) : ℂ) * s) / (1 - (qv v : ℂ) ^ (-6 * s))

private theorem tauDiag_sixth_zero (v : FinPlace F) :
    tauDiag v (1 / 6 : ℂ) 0 = 1 := by
  have hq0 : (qv v : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (qv_gt_one v)))
  have hq : (qv v : ℂ) ≠ 1 := by
    intro h
    have h' : qv v = 1 := by exact_mod_cast h
    linarith [qv_gt_one v]
  have hden : 1 - (qv v : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have heq : (qv v : ℂ) = 1 := by
      have h' := congrArg (fun z : ℂ => z⁻¹) h
      simpa [hq0] using h'.symm
    exact hq heq
  unfold tauDiag
  rw [show -6 * (1 / 6 : ℂ) = (-1 : ℂ) by norm_num, Complex.cpow_neg_one]
  rw [show -2 * (((-0 : ZMod 3).val : ℕ) : ℂ) * (1 / 6 : ℂ) = 0 by norm_num]
  simp only [Complex.cpow_zero, one_mul]
  field_simp [hden]

private theorem tauDiag_sixth_one (v : FinPlace F) :
    tauDiag v (1 / 6 : ℂ) 1 = (qv v : ℂ) ^ (-(2 / 3 : ℂ)) := by
  have hq0 : (qv v : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (qv_gt_one v)))
  have hq : (qv v : ℂ) ≠ 1 := by
    intro h
    have h' : qv v = 1 := by exact_mod_cast h
    linarith [qv_gt_one v]
  have hden : 1 - (qv v : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have heq : (qv v : ℂ) = 1 := by
      have h' := congrArg (fun z : ℂ => z⁻¹) h
      simpa [hq0] using h'.symm
    exact hq heq
  unfold tauDiag
  rw [show -6 * (1 / 6 : ℂ) = (-1 : ℂ) by norm_num, Complex.cpow_neg_one]
  have hval : (-1 : ZMod 3).val = 2 := by decide
  rw [show -2 * (((-1 : ZMod 3).val : ℕ) : ℂ) * (1 / 6 : ℂ) = -(2 / 3 : ℂ) by rw [hval]; norm_num]
  field_simp [hden]

private theorem tauDiag_sixth_two (v : FinPlace F) :
    tauDiag v (1 / 6 : ℂ) 2 = (qv v : ℂ) ^ (-(1 / 3 : ℂ)) := by
  have hq0 : (qv v : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (qv_gt_one v)))
  have hq : (qv v : ℂ) ≠ 1 := by
    intro h
    have h' : qv v = 1 := by exact_mod_cast h
    linarith [qv_gt_one v]
  have hden : 1 - (qv v : ℂ)⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have heq : (qv v : ℂ) = 1 := by
      have h' := congrArg (fun z : ℂ => z⁻¹) h
      simpa [hq0] using h'.symm
    exact hq heq
  unfold tauDiag
  rw [show -6 * (1 / 6 : ℂ) = (-1 : ℂ) by norm_num, Complex.cpow_neg_one]
  have hval : (-2 : ZMod 3).val = 1 := by decide
  rw [show -2 * (((-2 : ZMod 3).val : ℕ) : ℂ) * (1 / 6 : ℂ) = -(1 / 3 : ℂ) by rw [hval]; norm_num]
  field_simp [hden]

private theorem localCoeff_residue_rep (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal)
    (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply IsFractionRing.injective (𝓞 F) F
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem localCoeff_residue_int (v : FinPlace F) (a : 𝓞 F) :
    residue v (a : F) = Ideal.Quotient.mk v.asIdeal a := by
  have h := localCoeff_residue_rep v (a : F) a 1
    (Ideal.IsPrime.one_notMem v.isPrime) (by simp)
  simpa using h

private theorem localCoeff_psi_div_ideal (A : AddCharData F) (v : FinPlace F)
    (a : 𝓞 F) (ha : a ∈ v.asIdeal) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) = 1 := by
  let K := v.adicCompletion F
  let π : F := unif v
  have hπ : v.valuation F π = WithZero.exp (-1 : ℤ) := by
    dsimp [π, unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  have hvala : v.valuation F (a : F) ≤ WithZero.exp (-1 : ℤ) := by
    have hlt : v.valuation F (a : F) < 1 :=
      (v.valuation_lt_one_iff_mem (K := F) a).2 ha
    by_cases ha0 : (a : F) = 0
    · simp [ha0]
    · have hne : v.valuation F (a : F) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr ha0
      lift v.valuation F (a : F) to ℤ using hne with n hn
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      have hnlt : n < 0 := hlt
      exact WithZero.exp_le_exp.mpr (by omega)
  have hquot : v.valuation F ((a : F) / π) ≤ 1 := by
    rw [map_div₀, hπ]
    by_cases ha0 : (a : F) = 0
    · simp [ha0]
    · have hne : v.valuation F (a : F) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr ha0
      lift v.valuation F (a : F) to ℤ using hne with n hn
      have hlt : v.valuation F (a : F) < 1 :=
        (v.valuation_lt_one_iff_mem (K := F) a).2 ha
      rw [← hn] at hlt
      simp only [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      have hnlt : n < 0 := hlt
      have hnle : n ≤ -1 := by omega
      calc
        WithZero.exp n / WithZero.exp (-1) = WithZero.exp n * WithZero.exp 1 := by
          rw [div_eq_mul_inv]
          simp
        _ = WithZero.exp (n + 1) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp 0 := by
          rw [WithZero.exp_le_exp]
          omega
  have hmem : algebraMap F K ((a : F) / π) ∈ v.adicCompletionIntegers F := by
    change Valued.v ((((a : F) / π : F) : K)) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hquot
  exact A.integral v _ hmem

private theorem localCoeff_psi_rep_eq (A : AddCharData F) (v : FinPlace F)
    (a b : 𝓞 F) (h : Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b) :
    A.ψ v (algebraMap F (v.adicCompletion F) ((a : F) / unif v)) =
      A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / unif v)) := by
  have hab : a - b ∈ v.asIdeal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk v.asIdeal (a - b) =
          Ideal.Quotient.mk v.asIdeal a - Ideal.Quotient.mk v.asIdeal b := by simp
      _ = 0 := sub_eq_zero.mpr h
  have harg : (a : F) / unif v = (b : F) / unif v + ((a - b : 𝓞 F) : F) / unif v := by
    push_cast
    ring
  rw [harg, map_add, AddChar.map_add_eq_mul,
    localCoeff_psi_div_ideal A v (a - b) hab, mul_one]

private theorem gaussLoc_zero (D : FieldData F) (A : AddCharData F) (v : FinPlace F)
    (hv : (6 : 𝓞 F) ∉ v.asIdeal) (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) :
    gaussLoc D A v 0 = -(((qv v : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  classical
  let Q := 𝓞 F ⧸ v.asIdeal
  have hqpos : 0 < Ideal.absNorm v.asIdeal := by
    have hq := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  letI : Finite Q := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp hqpos.ne'
  letI : Fintype Q := Fintype.ofFinite _
  let π : F := unif v
  have hπ : v.valuation F π = WithZero.exp (-1 : ℤ) := by
    dsimp [π, unif]
    exact (HeightOneSpectrum.valuation_exists_uniformizer F v).choose_spec
  obtain ⟨_, hnontriv⟩ := A.unramified v hd
  obtain ⟨a, haψ⟩ := hnontriv π hπ
  let X : Q := Ideal.Quotient.mk v.asIdeal a
  have he (x : Q) : residue v (algebraMap (𝓞 F) F x.out) = x := by
    rw [localCoeff_residue_int]
    simp
  let ψbar : Q → ℂ := fun x => A.ψ v
    (algebraMap F (v.adicCompletion F) (((x.out : 𝓞 F) : F) / π))
  have hψrep (b c : 𝓞 F)
      (hbc : Ideal.Quotient.mk v.asIdeal b = Ideal.Quotient.mk v.asIdeal c) :
      A.ψ v (algebraMap F (v.adicCompletion F) ((b : F) / π)) =
        A.ψ v (algebraMap F (v.adicCompletion F) ((c : F) / π)) := by
    exact localCoeff_psi_rep_eq A v b c hbc
  have hψadd (x y : Q) : ψbar (x + y) = ψbar x * ψbar y := by
    dsimp [ψbar]
    have hclass : Ideal.Quotient.mk v.asIdeal (x + y).out =
        Ideal.Quotient.mk v.asIdeal (x.out + y.out) := by simp
    rw [localCoeff_psi_rep_eq A v (x + y).out (x.out + y.out) hclass]
    have hargK : algebraMap F (v.adicCompletion F)
        ((((x.out + y.out : 𝓞 F) : F) / π)) =
      algebraMap F (v.adicCompletion F) (((x.out : 𝓞 F) : F) / π) +
        algebraMap F (v.adicCompletion F) (((y.out : 𝓞 F) : F) / π) := by
      simp only [map_div₀, map_add]
      ring
    rw [hargK, AddChar.map_add_eq_mul]
  have hψzero : ψbar 0 = 1 := by
    have hmk0 : Ideal.Quotient.mk v.asIdeal (0 : Q).out = 0 := by simp
    have h0mem : (0 : Q).out ∈ v.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hmk0
    simpa [ψbar, π] using localCoeff_psi_div_ideal A v (0 : Q).out h0mem
  have hXψ : ψbar X ≠ 1 := by
    have hclass : Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal X.out := by
      calc
        Ideal.Quotient.mk v.asIdeal a = X := rfl
        _ = Ideal.Quotient.mk v.asIdeal X.out := by simp
    have hrep := hψrep X.out a hclass.symm
    have hrep' : ψbar X = A.ψ v
        (algebraMap F (v.adicCompletion F) ((a : F) / π)) := by
      simpa [ψbar] using hrep
    rw [hrep']
    exact haψ
  have hsumzero : (∑ x : Q, ψbar x) = 0 := by
    have hshift : (∑ x : Q, ψbar (X + x)) = ∑ x : Q, ψbar x := by
      exact Fintype.sum_equiv (Equiv.addLeft X) (fun x : Q => ψbar (X + x)) ψbar
        (by intro x; rfl)
    have hfactor : (∑ x : Q, ψbar (X + x)) = ψbar X * ∑ x : Q, ψbar x := by
      rw [show (∑ x : Q, ψbar (X + x)) = ∑ x : Q, ψbar X * ψbar x by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hψadd]]
      rw [Finset.mul_sum]
    have hmul : (ψbar X - 1) * ∑ x : Q, ψbar x = 0 := by
      calc
        (ψbar X - 1) * ∑ x : Q, ψbar x =
            ψbar X * ∑ x : Q, ψbar x - ∑ x : Q, ψbar x := by ring
        _ = 0 := by rw [← hfactor, hshift]; ring
    rcases mul_eq_zero.mp hmul with h | h
    · exact (hXψ (sub_eq_zero.mp h)).elim
    · exact h
  have hsumchi : (∑ x : Q, chiPow D v (algebraMap (𝓞 F) F x.out) 0 * ψbar x) = -1 := by
    have hterm (x : Q) : chiPow D v (algebraMap (𝓞 F) F x.out) 0 =
        if x = 0 then 0 else 1 := by
      rw [chiPow]
      rw [he x]
      by_cases hx : x = 0 <;> simp [hx]
    have hsplit : (∑ x : Q, (if x = 0 then 0 else ψbar x)) =
        (∑ x : Q, ψbar x) - ψbar 0 := by
      calc
        _ = ∑ x ∈ Finset.univ.erase (0 : Q), ψbar x := by
          have hsub : Finset.univ.erase (0 : Q) ⊆ Finset.univ := Finset.erase_subset _ _
          have hzero : ∀ x ∈ Finset.univ, x ∉ Finset.univ.erase (0 : Q) →
              (if x = 0 then 0 else ψbar x) = 0 := by
            intro x hx hnot
            have hx0 : x = 0 := by
              by_contra hne
              exact hnot (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
            simp [hx0]
          have hsumE := Finset.sum_subset hsub hzero
          calc
            _ = ∑ x ∈ Finset.univ, (if x = 0 then 0 else ψbar x) := by rfl
            _ = ∑ x ∈ Finset.univ.erase (0 : Q), (if x = 0 then 0 else ψbar x) := hsumE.symm
            _ = _ := by
              apply Finset.sum_congr rfl
              intro x hx
              have hne : x ≠ 0 := (Finset.mem_erase.mp hx).1
              simp [hne]
        _ = (∑ x : Q, ψbar x) - ψbar 0 := by
          have hfull : (∑ x : Q, ψbar x) =
              (∑ x ∈ Finset.univ.erase (0 : Q), ψbar x) + ψbar 0 := by
            simpa using Finset.sum_erase_add Finset.univ ψbar (Finset.mem_univ (0 : Q))
          rw [hfull]
          ring
    simp_rw [hterm, ite_mul, zero_mul, one_mul]
    rw [hsplit, hsumzero, hψzero]
    ring
  have htsum : (∑ᶠ x : Q, chiPow D v (algebraMap (𝓞 F) F x.out) 0 * ψbar x) = -1 := by
    rw [finsum_eq_finsetSum_of_support_subset
      (fun x : Q => chiPow D v (algebraMap (𝓞 F) F x.out) 0 * ψbar x)
      (s := Finset.univ) (by intro x hx; simp)]
    exact hsumchi
  unfold gaussLoc
  change ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
      (∑ᶠ x : Q, chiPow D v (algebraMap (𝓞 F) F x.out) 0 * ψbar x) = _
  rw [htsum]
  simp [qv]

private theorem localCoeff_jacquet_surjective (L : FinLocalCover D H v) (T : TorusRep D H v)
    (A : AddCharData F) (μ : LocHaar v) (s : ℂ) (z : T.V) :
    ∃ f, IsSection L T s f ∧ jacquet L A μ f = z := by
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let _ : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).RankOne := inferInstance
  let _ : NormedField K := inferInstance
  let _ : Finite (IsLocalRing.ResidueField O) :=
    Finite.of_equiv _ (v.residueFieldEquivAdicCompletionIntegers (K := F)).toEquiv
  have hproper : ProperSpace K :=
    (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := K) (Γ₀ := WithZero (Multiplicative ℤ))).mpr
      ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing O),
        inferInstanceAs (Finite (IsLocalRing.ResidueField O))⟩
  have hset : (O : Set K) = Metric.closedBall (0 : K) 1 := by
    change (↑((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer) : Set K) = _
    exact Valued.toNormedField.setOfPred_mem_integer_eq_closedBall (L := K)
  have hcompact : IsCompact (O : Set K) := by
    rw [hset]
    exact hproper.isCompact_closedBall 0 1
  have hopen : IsOpen (O : Set K) := Valued.isOpen_valuationSubring K
  obtain ⟨φ, hφ, hφc, hhat⟩ := exists_fourier_indicator A μ O hcompact hopen z
  have h1O : (1 : K) ∈ O := by
    simp [O]
  refine ⟨bigCell L T s φ, bigCell_isSection L T s φ hφ hφc, ?_⟩
  have hJ := jacquet_bigCell L T A μ s φ hφ hφc (1 : Kˣ)
  rw [L.a_one] at hJ
  have hFourier : ∫ t, A.ψ v (-t) • φ t ∂μ.μ = z := by
    simpa [h1O] using hhat (1 : K)
  simp only [Units.val_one, one_mul] at hJ
  rw [hFourier] at hJ
  have htr : rtr (1 : L.L) (bigCell L T s φ) = bigCell L T s φ := by
    funext g
    simp [rtr]
  rw [htr] at hJ
  simpa [absFin_eq_norm, T.σa_one] using hJ

/-- **wh:tau-tame**: `τ(s) e_k = A_k(s) e_{-k} + q^{2s-1} G(ρ^{k-1}) e_{k+1}` with
`G(ρ^j) = q^{1/2} g_{2j}`. -/
theorem local_coefficient_tame (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (s : ℂ) (hs : 0 < s.re) (τ : T.V →ₗ[ℂ] T.V)
    (hτ : ∀ f ∈ sectionSpace L T s, jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f))
    (k : ZMod 3) :
    τ (B.e k) = tauDiag v s k • B.e (-k) +
      ((qv v : ℂ) ^ (2 * s - 1) * ((qv v : ℂ) ^ ((1 : ℂ) / 2) *
        gaussLoc D A v (2 * ((k.val : ℤ) - 1)))) • B.e (k + 1) := by
  sorry

/-- **wh:tau-rank**: at `s0 = 1/6`, `range τ = ℂ u` with `u = shellVec` of the Weyl basis. -/
theorem local_coefficient_rank_one (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (τ : T.V →ₗ[ℂ] T.V)
    (hτ : ∀ f ∈ sectionSpace L T (1 / 6),
      jacquet L A μ (intertwine L μ f) = τ (jacquet L A μ f)) :
    LinearMap.range τ = Submodule.span ℂ {shellVec D A B.weyl} := by
  classical
  have hAdd : T.weyl.nacg.toAddCommMonoid = T.nacg.toAddCommMonoid := rfl
  have hModule : T.weyl.nsp.toModule = T.nsp.toModule := rfl
  cases hAdd
  cases hModule
  have hs : (0 : ℝ) < (1 / 6 : ℂ).re := by norm_num
  have hmatrix (k : ZMod 3) :=
    local_coefficient_tame L T B A μ hv hd (1 / 6 : ℂ) hs τ hτ k
  let q : ℂ := qv v
  let a : ℂ := q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)
  let b : ℂ := q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v 2
  let u : T.V := shellVec D A (T := T.weyl) B.weyl
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one (qv_gt_one v)))
  have hpow : q ^ (2 * (1 / 6 : ℂ) - 1) * q ^ ((1 : ℂ) / 2) =
      q ^ (-(1 / 6 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  have hpowHalf : (((qv v : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
      (qv v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    simpa using Complex.ofReal_cpow
      (le_of_lt (lt_trans zero_lt_one (qv_gt_one v))) (-(1 / 2 : ℝ))
  have hgauss0 : gaussLoc D A v 0 = -q ^ (-(1 / 2 : ℂ)) := by
    rw [gaussLoc_zero D A v hv hd, hpowHalf]
  have hu : u = B.e 0 + a • B.e 1 := by
    have hidx : (-2 : ZMod 3) = 1 := by decide
    simp [u, a, q, shellVec, TameTorusBasis.weyl, hidx]
    rfl
  have hcol0 : τ (B.e 0) = u := by
    calc
      τ (B.e 0) = B.e 0 + a • B.e 1 := by
        rw [hmatrix 0, tauDiag_sixth_zero]
        have hidx : 2 * (((0 : ZMod 3).val : ℤ) - 1) = -2 := by norm_num
        rw [hidx, ← mul_assoc, show (qv v : ℂ) = q by rfl, hpow]
        simp [a, q]
      _ = u := hu.symm
  have hscalarCancel : q ^ (-(2 / 3 : ℂ)) +
      q ^ (-(1 / 6 : ℂ)) * (-q ^ (-(1 / 2 : ℂ))) = 0 := by
    calc
      q ^ (-(2 / 3 : ℂ)) + q ^ (-(1 / 6 : ℂ)) * (-q ^ (-(1 / 2 : ℂ))) =
          q ^ (-(2 / 3 : ℂ)) - q ^ (-(1 / 6 : ℂ)) * q ^ (-(1 / 2 : ℂ)) := by ring
      _ = q ^ (-(2 / 3 : ℂ)) - q ^ (-(1 / 6 : ℂ) + -(1 / 2 : ℂ)) := by
        rw [← Complex.cpow_add _ _ hq0]
      _ = 0 := by congr 1 <;> norm_num
  have hcol1 : τ (B.e 1) = 0 := by
    rw [hmatrix 1, tauDiag_sixth_one]
    have hv1 : (1 : ZMod 3).val = 1 := by decide
    have hidx : 2 * (((1 : ZMod 3).val : ℤ) - 1) = 0 := by rw [hv1]; norm_num
    rw [hidx, hgauss0]
    rw [show (-1 : ZMod 3) = 2 by decide, show (1 : ZMod 3) + 1 = 2 by decide]
    rw [← mul_assoc, show (qv v : ℂ) = q by rfl, hpow]
    rw [← add_smul, hscalarCancel, zero_smul]
  have hgaussprod : gaussLoc D A v 2 * gaussLoc D A v (-2) = 1 :=
    gaussLoc_mul_neg D A v hv hd 2 (by norm_num)
  have hscalarB : b * a = q ^ (-(1 / 3 : ℂ)) := by
    dsimp [a, b]
    calc
      (q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v 2) *
          (q ^ (-(1 / 6 : ℂ)) * gaussLoc D A v (-2)) =
          (q ^ (-(1 / 6 : ℂ)) * q ^ (-(1 / 6 : ℂ))) *
            (gaussLoc D A v 2 * gaussLoc D A v (-2)) := by ring
      _ = q ^ (-(1 / 3 : ℂ)) := by
        rw [← Complex.cpow_add _ _ hq0, hgaussprod]
        congr 1
        ring
  have hcol2 : τ (B.e 2) = b • u := by
    rw [hmatrix 2, tauDiag_sixth_two]
    have hv2 : (2 : ZMod 3).val = 2 := by decide
    have hidx : 2 * (((2 : ZMod 3).val : ℤ) - 1) = 2 := by rw [hv2]; norm_num
    rw [hidx]
    rw [show (-2 : ZMod 3) = 1 by decide, show (2 : ZMod 3) + 1 = 0 by decide]
    rw [← mul_assoc, show (qv v : ℂ) = q by rfl, hpow]
    rw [hu, smul_add, smul_smul, hscalarB, add_comm]
  have hcol (k : ZMod 3) : τ (B.e k) ∈ Submodule.span ℂ {u} := by
    have hkcases : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by have := k.val_lt; omega
    rcases hkcases with hk0 | hk1 | hk2
    · have hk : k = 0 := ZMod.val_injective 3 (by simpa using hk0)
      rw [hk, hcol0]
      exact Submodule.subset_span (Set.mem_singleton u)
    · have hk : k = 1 := ZMod.val_injective 3 (by
        rw [show (1 : ZMod 3).val = 1 by decide]
        exact hk1)
      rw [hk, hcol1]
      exact Submodule.zero_mem _
    · have hk : k = 2 := ZMod.val_injective 3 (by rw [show (2 : ZMod 3).val = 2 by decide]; exact hk2)
      rw [hk, hcol2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  have himage (x : T.V) : τ x ∈ Submodule.span ℂ {u} := by
    have hx : x ∈ Submodule.span ℂ (Set.range B.e) := by
      rw [B.spans]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun y _ => τ y ∈ Submodule.span ℂ {u}) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨k, rfl⟩
      exact hcol k
    · simpa using (Submodule.zero_mem (Submodule.span ℂ {u}))
    · intro x y hx hy hpx hpy
      rw [map_add]
      exact Submodule.add_mem _ hpx hpy
    · intro c x hx hpx
      rw [map_smul]
      exact Submodule.smul_mem _ c hpx
  have hrange : LinearMap.range τ ≤ Submodule.span ℂ {u} := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact himage x
  have huRange : u ∈ LinearMap.range τ := ⟨B.e 0, hcol0⟩
  have hspanRange : Submodule.span ℂ {u} ≤ LinearMap.range τ :=
    Submodule.span_le.mpr fun x hx => by
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact huRange
  change LinearMap.range τ = Submodule.span ℂ {u}
  exact le_antisymm hrange hspanRange

/-- The local theta space `Θ_v = M(1/6) I(T, 1/6) ⊆ I(T.weyl, -1/6)`. -/
def thetaSpace (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v) :
    Submodule ℂ (L.L → T.V) :=
  Submodule.span ℂ (intertwine L μ '' {f | IsSection L T (1 / 6) f})

theorem thetaSpace_le (L : FinLocalCover D H v) (T : TorusRep D H v) (μ : LocHaar v) :
    thetaSpace L T μ ≤ sectionSpace L T.weyl (-(1 / 6)) ∧ IsRtrStable (thetaSpace L T μ) := by
  have hs : (0 : ℝ) < (1 / 6 : ℂ).re := by norm_num
  constructor
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    change IsSection L T.weyl (-(1 / 6 : ℂ)) (intertwine L μ f)
    exact (intertwine_isSection L T μ (1 / 6) hs f hf).2
  · intro f hf g
    change f ∈ Submodule.span ℂ (intertwine L μ '' {f | IsSection L T (1 / 6) f}) at hf
    change rtr g f ∈ Submodule.span ℂ (intertwine L μ '' {f | IsSection L T (1 / 6) f})
    refine Submodule.span_induction
      (p := fun x _ => rtr g x ∈ Submodule.span ℂ
        (intertwine L μ '' {f | IsSection L T (1 / 6) f})) ?_ ?_ ?_ ?_ hf
    · intro x hx
      rcases hx with ⟨f₀, hf₀, rfl⟩
      rw [← intertwine_rtr]
      exact Submodule.subset_span ⟨rtr g f₀, IsSection.rtr hf₀ g, rfl⟩
    · change (0 : L.L → T.V) ∈ _
      exact Submodule.zero_mem _
    · intro x y hx hy hpx hpy
      change rtr g (x + y) ∈ _
      rw [show rtr g (x + y) = rtr g x + rtr g y by rfl]
      exact Submodule.add_mem _ hpx hpy
    · intro c x hx hpx
      change rtr g (c • x) ∈ _
      rw [show rtr g (c • x) = c • rtr g x by rfl]
      exact Submodule.smul_mem _ c hpx

private noncomputable def weylCarrierEquiv (T : TorusRep D H v) : T.weyl.V ≃ₗ[ℂ] T.V where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := by
    have hAdd : T.weyl.nacg.toAddCommMonoid = T.nacg.toAddCommMonoid := rfl
    cases hAdd
    rfl
  map_smul' c x := by
    have hAdd : T.weyl.nacg.toAddCommMonoid = T.nacg.toAddCommMonoid := rfl
    have hModule : T.weyl.nsp.toModule = T.nsp.toModule := rfl
    cases hAdd
    cases hModule
    rfl

/-- **wh:theta-unique** (top; replaces KP Cor. I.3.6): on `Θ_v`, `𝒥` takes values in `ℂ u`, and every
Whittaker functional is `c ∘ 𝒥`. -/
theorem whittaker_theta_unique (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) :
    (∀ f ∈ thetaSpace L T μ, jacquet L A μ f ∈ Submodule.span ℂ {shellVec D A B.weyl}) ∧
    ∀ Λ : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (thetaSpace L T μ) Λ →
      ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ thetaSpace L T μ, Λ f = c (jacquet L A μ f) := by
  have hAdd : T.weyl.nacg.toAddCommMonoid = T.nacg.toAddCommMonoid := rfl
  have hModule : T.weyl.nsp.toModule = T.nsp.toModule := rfl
  have hs : (0 : ℝ) < (1 / 6 : ℂ).re := by norm_num
  obtain ⟨hsub, hstable⟩ := thetaSpace_le L T μ
  obtain ⟨τ, hτ⟩ := local_coefficient L T A μ (1 / 6) hs
  have hrank := local_coefficient_rank_one L T B A μ hv hd τ hτ
  let e := weylCarrierEquiv T
  let eFun (f : L.L → T.V) : L.L → T.weyl.V := fun g => e.symm (f g)
  let τW : T.weyl.V →ₗ[ℂ] T.weyl.V :=
    e.symm.toLinearMap.comp (τ.comp e.toLinearMap)
  have hJcast (f : L.L → T.V) :
      e.symm (jacquet L A μ f) = jacquet L A μ (eFun f) := by
    rfl
  have hEfun (f : L.L → T.V) : eFun f = f := by
    funext g
    rfl
  have hRangeMap : LinearMap.range τW = (LinearMap.range τ).map e.symm.toLinearMap := by
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨τ (e x), LinearMap.mem_range_self τ (e x), ?_⟩
      simp [τW]
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨x, rfl⟩
      refine ⟨e.symm x, ?_⟩
      simp [τW]
  let uT : T.V := shellVec D A (T := T.weyl) B.weyl
  let uW : T.weyl.V := e.symm.toLinearMap uT
  have huW : uW = shellVec D A B.weyl := rfl
  have hrankT : LinearMap.range τ = Submodule.span ℂ {uT} := by
    cases hAdd
    cases hModule
    change LinearMap.range τ = Submodule.span ℂ {shellVec D A (T := T.weyl) B.weyl}
    exact hrank
  have hrankW : LinearMap.range τW = Submodule.span ℂ {uW} := by
    calc
      LinearMap.range τW = (LinearMap.range τ).map e.symm.toLinearMap := hRangeMap
      _ = (Submodule.span ℂ {uT}).map e.symm.toLinearMap := by rw [hrankT]
      _ = Submodule.span ℂ {uW} := by
        rw [LinearMap.map_span]
        simp [uW, Set.image_singleton]
  have hzeroSectionW : IsSection L T.weyl (-(1 / 6 : ℂ)) (0 : L.L → T.weyl.V) := by
    change (0 : L.L → T.weyl.V) ∈ sectionSpace L T.weyl (-(1 / 6 : ℂ))
    exact Submodule.zero_mem _
  have hzeroW : jacquet L A μ (0 : L.L → T.weyl.V) = 0 := by
    have hlin := jacquet_linear L T.weyl A μ (-(1 / 6 : ℂ)) 0 0
      hzeroSectionW hzeroSectionW (1 : ℂ)
    have heq : jacquet L A μ (0 : L.L → T.weyl.V) =
        jacquet L A μ (0 : L.L → T.weyl.V) + jacquet L A μ (0 : L.L → T.weyl.V) := by
      calc
        jacquet L A μ (0 : L.L → T.weyl.V) =
            jacquet L A μ (0 + (1 : ℂ) • (0 : L.L → T.weyl.V)) := by simp
        _ = jacquet L A μ (0 : L.L → T.weyl.V) +
            (1 : ℂ) • jacquet L A μ (0 : L.L → T.weyl.V) := hlin
        _ = jacquet L A μ (0 : L.L → T.weyl.V) +
            jacquet L A μ (0 : L.L → T.weyl.V) := by simp
    have heq' : jacquet L A μ (0 : L.L → T.weyl.V) + 0 =
        jacquet L A μ (0 : L.L → T.weyl.V) + jacquet L A μ (0 : L.L → T.weyl.V) := by
      simpa using heq
    exact (add_left_cancel heq').symm
  have hImage (x : L.L → T.V) (hx : x ∈ thetaSpace L T μ) :
      jacquet L A μ (eFun x) ∈ Submodule.span ℂ {uW} := by
    change x ∈ Submodule.span ℂ (intertwine L μ '' {f | IsSection L T (1 / 6) f}) at hx
    refine Submodule.span_induction
      (p := fun y _ => jacquet L A μ (eFun y) ∈
        Submodule.span ℂ {uW}) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨f₀, hf₀, rfl⟩
      have hτW : jacquet L A μ (eFun (intertwine L μ f₀)) =
          τW (jacquet L A μ (eFun f₀)) := by
        rw [← hJcast (intertwine L μ f₀), hτ f₀ hf₀, ← hJcast f₀]
        simp [τW]
      rw [hτW, ← hrankW]
      exact LinearMap.mem_range_self τW (jacquet L A μ (eFun f₀))
    · have hz : jacquet L A μ (eFun (0 : L.L → T.V)) = 0 := by
        change jacquet L A μ (0 : L.L → T.weyl.V) = 0
        exact hzeroW
      rw [hz]
      exact Submodule.zero_mem _
    · intro x y hx hy hpx hpy
      have hxs : IsSection L T.weyl (-(1 / 6 : ℂ)) x := hsub hx
      have hys : IsSection L T.weyl (-(1 / 6 : ℂ)) y := hsub hy
      have hxsW : IsSection L T.weyl (-(1 / 6 : ℂ)) (eFun x) := by
        change IsSection L T.weyl (-(1 / 6 : ℂ)) x
        exact hxs
      have hysW : IsSection L T.weyl (-(1 / 6 : ℂ)) (eFun y) := by
        change IsSection L T.weyl (-(1 / 6 : ℂ)) y
        exact hys
      have hsum : eFun (x + y) = eFun x + eFun y := by
        change x + y = x + y
        rfl
      rw [hsum]
      have hlin' : jacquet L A μ (eFun x + eFun y) =
          jacquet L A μ (eFun x) + jacquet L A μ (eFun y) := by
        calc
          jacquet L A μ (eFun x + eFun y) =
              jacquet L A μ (eFun x + (1 : ℂ) • eFun y) := by simp
          _ = jacquet L A μ (eFun x) +
                (1 : ℂ) • jacquet L A μ (eFun y) :=
              jacquet_linear L T.weyl A μ (-(1 / 6 : ℂ))
                (eFun x) (eFun y) hxsW hysW (1 : ℂ)
          _ = jacquet L A μ (eFun x) + jacquet L A μ (eFun y) := by simp
      rw [hlin']
      exact Submodule.add_mem _ hpx hpy
    · intro c x hx hpx
      have hxs : IsSection L T.weyl (-(1 / 6 : ℂ)) x := hsub hx
      have hxsW : IsSection L T.weyl (-(1 / 6 : ℂ)) (eFun x) := by
        change IsSection L T.weyl (-(1 / 6 : ℂ)) x
        exact hxs
      have hsmul : eFun (c • x) = c • eFun x := by
        change c • x = c • x
        rfl
      rw [hsmul]
      have hlin' : jacquet L A μ (c • eFun x) = c • jacquet L A μ (eFun x) := by
        calc
          jacquet L A μ (c • eFun x) = jacquet L A μ (0 + c • eFun x) := by simp
          _ = jacquet L A μ 0 + c • jacquet L A μ (eFun x) :=
            jacquet_linear L T.weyl A μ (-(1 / 6 : ℂ)) 0 (eFun x)
              hzeroSectionW hxsW c
          _ = c • jacquet L A μ (eFun x) := by simp [hzeroW]
      rw [hlin']
      exact Submodule.smul_mem _ c hpx
  constructor
  · intro f hf
    have hfW := hImage f hf
    rw [← huW]
    change jacquet L A μ (eFun f) ∈ Submodule.span ℂ {uW}
    exact hfW
  · intro Λ hΛ
    obtain ⟨Λ', hΛ', hrestrict⟩ :=
      whittaker_extend L T.weyl A (-(1 / 6 : ℂ)) (thetaSpace L T μ) hsub hstable Λ hΛ
    obtain ⟨c, hc⟩ := whittaker_twoCell L T.weyl A μ (-(1 / 6 : ℂ)) Λ' hΛ'
    let c' : T.V →ₗ[ℂ] ℂ := by
      cases hAdd
      cases hModule
      exact c
    refine ⟨c', ?_⟩
    intro f hf
    calc
      Λ f = Λ' f := (hrestrict f hf).symm
      _ = c' (jacquet L A μ f) := by
        cases hAdd
        cases hModule
        exact hc f (hsub hf)

/-- **wh:dim-le-one**: `dim Wh(Θ_v) ≤ 1`, in the form used for normalization. -/
theorem whittaker_theta_dim_le_one (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (Λ₁ Λ₂ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (h₁ : IsWhittakerOn L A (thetaSpace L T μ) Λ₁) (h₂ : IsWhittakerOn L A (thetaSpace L T μ) Λ₂) :
    ∀ f ∈ thetaSpace L T μ, ∀ f' ∈ thetaSpace L T μ, Λ₂ f * Λ₁ f' = Λ₂ f' * Λ₁ f := by
  obtain ⟨himage, hfactor⟩ := whittaker_theta_unique L T B A μ hv hd
  obtain ⟨c₁, hc₁⟩ := hfactor Λ₁ h₁
  obtain ⟨c₂, hc₂⟩ := hfactor Λ₂ h₂
  let e := weylCarrierEquiv T
  let uW : T.weyl.V := shellVec D A B.weyl
  let uT : T.V := e uW
  intro f hf f' hf'
  let jW : T.weyl.V := jacquet L A μ f
  let jW' : T.weyl.V := jacquet L A μ f'
  have hjW : jW ∈ Submodule.span ℂ {uW} := by
    change jacquet L A μ f ∈ Submodule.span ℂ {shellVec D A B.weyl}
    exact himage f hf
  have hjW' : jW' ∈ Submodule.span ℂ {uW} := by
    change jacquet L A μ f' ∈ Submodule.span ℂ {shellVec D A B.weyl}
    exact himage f' hf'
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hjW
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hjW'
  have haT : a • uT = jacquet L A μ f := by
    calc
      a • uT = e (a • uW) := (e.map_smul a uW).symm
      _ = e jW := congrArg e ha
      _ = jacquet L A μ f := rfl
  have hbT : b • uT = jacquet L A μ f' := by
    calc
      b • uT = e (b • uW) := (e.map_smul b uW).symm
      _ = e jW' := congrArg e hb
      _ = jacquet L A μ f' := rfl
  have h₂f : Λ₂ f = a * c₂ uT := by
    rw [hc₂ f hf, ← haT]
    simp only [map_smul, smul_eq_mul]
  have h₁f' : Λ₁ f' = b * c₁ uT := by
    rw [hc₁ f' hf', ← hbT]
    simp only [map_smul, smul_eq_mul]
  have h₂f' : Λ₂ f' = b * c₂ uT := by
    rw [hc₂ f' hf', ← hbT]
    simp only [map_smul, smul_eq_mul]
  have h₁f : Λ₁ f = a * c₁ uT := by
    rw [hc₁ f hf, ← haT]
    simp only [map_smul, smul_eq_mul]
  rw [h₂f, h₁f', h₂f', h₁f]
  ring

end LocalWhit

end ArtinPrimitiveRoots.A1.Theta
