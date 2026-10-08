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

/-- The space of sections of `I(T, s)` (def:ind as a subspace). -/
def sectionSpace (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) :
    Submodule ℂ (L.L → T.V) where
  carrier := {f | IsSection L T s f}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

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
  sorry

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

/-- **wh:theta-unique** (top; replaces KP Cor. I.3.6): on `Θ_v`, `𝒥` takes values in `ℂ u`, and every
Whittaker functional is `c ∘ 𝒥`. -/
theorem whittaker_theta_unique (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) :
    (∀ f ∈ thetaSpace L T μ, jacquet L A μ f ∈ Submodule.span ℂ {shellVec D A B.weyl}) ∧
    ∀ Λ : (L.L → T.V) →ₗ[ℂ] ℂ, IsWhittakerOn L A (thetaSpace L T μ) Λ →
      ∃ c : T.V →ₗ[ℂ] ℂ, ∀ f ∈ thetaSpace L T μ, Λ f = c (jacquet L A μ f) := by
  sorry

/-- **wh:dim-le-one**: `dim Wh(Θ_v) ≤ 1`, in the form used for normalization. -/
theorem whittaker_theta_dim_le_one (L : FinLocalCover D H v) (T : TorusRep D H v)
    (B : TameTorusBasis T) (A : AddCharData F) (μ : LocHaar v) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (hd : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) (Λ₁ Λ₂ : (L.L → T.V) →ₗ[ℂ] ℂ)
    (h₁ : IsWhittakerOn L A (thetaSpace L T μ) Λ₁) (h₂ : IsWhittakerOn L A (thetaSpace L T μ) Λ₂) :
    ∀ f ∈ thetaSpace L T μ, ∀ f' ∈ thetaSpace L T μ, Λ₂ f * Λ₁ f' = Λ₂ f' * Λ₁ f := by
  sorry

end LocalWhit

end ArtinPrimitiveRoots.A1.Theta
