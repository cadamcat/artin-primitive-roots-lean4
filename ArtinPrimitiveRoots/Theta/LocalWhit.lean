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
  sorry

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
  sorry

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
