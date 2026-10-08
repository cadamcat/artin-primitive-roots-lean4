import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

/-- Every adelic point has a classical component representation at the prescribed common
level. This isolates the geometric covering step from the analytic independence proof.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–800`; component input: lines 786–796.
Uses `ContinuedEisComponents.detect` from frozen `exists_classical_components` and
archimedean Iwasawa coordinates. Consumed by component reconstruction and torus charts. -/
theorem continuedEis_component_representatives {P : CoverPackage D S H A} {G : GlobalDatum P}
    {I : ContinuedEisInput P G} (C : ContinuedEisComponents I) :
    ∀ g : P.tc.G, ∃ (j : C.J) (γ : GL (Fin 2) F)
      (x : InfinitePlace F → ℂ) (y : InfinitePlace F → ℝ)
      (kinf k : P.tc.G), (∀ w, 0 < y w) ∧ kinf ∈ infCompact P ∧
        k ∈ levelSet P I.T0 C.hsub C.m ∧
        g = P.tc.rat γ * (nInf P x * aInf P y * j) * kinf * k := by
  classical
  intro g
  let L := levelSet P I.T0 C.hsub C.m
  have L_one : (1 : P.tc.G) ∈ L := by
    change (1 : P.tc.G) ∈ levelSet P I.T0 C.hsub C.m
    refine ⟨1, by simp, ?_, ?_, ?_⟩
    · intro w
      exact map_one (P.compC w)
    · intro v hv
      simpa using (P.loc v).Kc (C.m v) |>.one_mem
    · intro v hv
      simpa using (P.tame v (fun h => hv (C.hsub h))).Kmax.one_mem
  have L_mul {k₁ k₂ : P.tc.G} (h₁ : k₁ ∈ L) (h₂ : k₂ ∈ L) : k₁ * k₂ ∈ L := by
    change k₁ * k₂ ∈ levelSet P I.T0 C.hsub C.m
    rcases h₁ with ⟨x₁, hq₁, hc₁, hf₁, ho₁⟩
    rcases h₂ with ⟨x₂, hq₂, hc₂, hf₂, ho₂⟩
    refine ⟨x₁ * x₂, ?_, ?_, ?_, ?_⟩
    · change P.q (x₁ * x₂) = k₁ * k₂
      rw [(P.q).map_mul, hq₁, hq₂]
    · intro w
      change P.compC w (x₁ * x₂) = 1
      rw [(P.compC w).map_mul, hc₁ w, hc₂ w]
      simp
    · intro v hv
      change P.compF v (x₁ * x₂) ∈ (P.loc v).Kc (C.m v)
      rw [(P.compF v).map_mul]
      exact (P.loc v).Kc (C.m v) |>.mul_mem (hf₁ v hv) (hf₂ v hv)
    · intro v hv
      change P.compF v (x₁ * x₂) ∈ (P.tame v (fun h => hv (C.hsub h))).Kmax
      rw [(P.compF v).map_mul]
      exact (P.tame v (fun h => hv (C.hsub h))).Kmax.mul_mem (ho₁ v hv) (ho₂ v hv)
  have L_inv {k : P.tc.G} (hk : k ∈ L) : k⁻¹ ∈ L := by
    change k⁻¹ ∈ levelSet P I.T0 C.hsub C.m
    rcases hk with ⟨x, hq, hc, hf, ho⟩
    refine ⟨x⁻¹, ?_, ?_, ?_, ?_⟩
    · change P.q x⁻¹ = k⁻¹
      rw [(P.q).map_inv, hq]
    · intro w
      change P.compC w x⁻¹ = 1
      rw [(P.compC w).map_inv, hc w]
      simp
    · intro v hv
      change P.compF v x⁻¹ ∈ (P.loc v).Kc (C.m v)
      rw [(P.compF v).map_inv]
      exact (P.loc v).Kc (C.m v) |>.inv_mem (hf v hv)
    · intro v hv
      change P.compF v x⁻¹ ∈ (P.tame v (fun h => hv (C.hsub h))).Kmax
      rw [(P.compF v).map_inv]
      exact (P.tame v (fun h => hv (C.hsub h))).Kmax.inv_mem (ho v hv)
  have U_one : (1 : P.tc.G) ∈ infCompact P := by
    refine ⟨1, by simp, ?_, ?_⟩
    · intro v
      exact map_one (P.compF v)
    · intro w
      refine ⟨1, (Matrix.unitaryGroup (Fin 2) ℂ).one_mem, ?_⟩
      simp
  have U_mul {u₁ u₂ : P.tc.G} (h₁ : u₁ ∈ infCompact P) (h₂ : u₂ ∈ infCompact P) :
      u₁ * u₂ ∈ infCompact P := by
    rcases h₁ with ⟨x₁, hq₁, hf₁, hc₁⟩
    rcases h₂ with ⟨x₂, hq₂, hf₂, hc₂⟩
    refine ⟨x₁ * x₂, ?_, ?_, ?_⟩
    · change P.q (x₁ * x₂) = u₁ * u₂
      rw [(P.q).map_mul, hq₁, hq₂]
    · intro v
      change P.compF v (x₁ * x₂) = 1
      rw [(P.compF v).map_mul, hf₁ v, hf₂ v]
      simp
    · intro w
      rcases hc₁ w with ⟨k₁, hk₁, he₁⟩
      rcases hc₂ w with ⟨k₂, hk₂, he₂⟩
      refine ⟨k₁ * k₂, (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem hk₁ hk₂, ?_⟩
      change P.compC w (x₁ * x₂) = QuotientGroup.mk (k₁ * k₂)
      rw [(P.compC w).map_mul, he₁, he₂]
      simp
  have unitaryGL_inv (k : GL (Fin 2) ℂ)
      (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
      ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.unitaryGroup (Fin 2) ℂ := by
    have hinv : (k⁻¹ : GL (Fin 2) ℂ) * k = 1 := inv_mul_cancel k
    have hmat :
        ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
          (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      have h := congrArg (fun a : GL (Fin 2) ℂ => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
      simpa using h
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) ∈
      Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk
  have U_inv {u : P.tc.G} (hu : u ∈ infCompact P) : u⁻¹ ∈ infCompact P := by
    rcases hu with ⟨x, hq, hf, hc⟩
    refine ⟨x⁻¹, ?_, ?_, ?_⟩
    · change P.q x⁻¹ = u⁻¹
      rw [(P.q).map_inv, hq]
    · intro v
      change P.compF v x⁻¹ = 1
      rw [(P.compF v).map_inv, hf v]
      simp
    · intro w
      rcases hc w with ⟨k, hk, he⟩
      refine ⟨k⁻¹, unitaryGL_inv k hk, ?_⟩
      change P.compC w x⁻¹ = QuotientGroup.mk k⁻¹
      rw [(P.compC w).map_inv, he]
      simp
  have commute_L_U {k u : P.tc.G} (hk : k ∈ L) (hu : u ∈ infCompact P) : k * u = u * k := by
    rcases hk with ⟨x, hqₖ, hcₖ, hfₖ, hoₖ⟩
    rcases hu with ⟨y, hqᵤ, hfᵤ, hcᵤ⟩
    have hxy : x * y = y * x := by
      apply P.comp_ext
      · intro v
        calc
          P.compF v (x * y) = P.compF v x * P.compF v y := (P.compF v).map_mul x y
          _ = P.compF v x := by rw [hfᵤ v, mul_one]
          _ = P.compF v y * P.compF v x := by rw [hfᵤ v, one_mul]
          _ = P.compF v (y * x) := ((P.compF v).map_mul y x).symm
      · intro w
        calc
          P.compC w (x * y) = P.compC w x * P.compC w y := (P.compC w).map_mul x y
          _ = P.compC w y := by rw [hcₖ w, one_mul]
          _ = P.compC w y * P.compC w x := by rw [hcₖ w, mul_one]
          _ = P.compC w (y * x) := ((P.compC w).map_mul y x).symm
    calc
      k * u = P.q x * P.q y := by rw [hqₖ, hqᵤ]
      _ = P.q (x * y) := ((P.q).map_mul x y).symm
      _ = P.q (y * x) := congrArg P.q hxy
      _ = P.q y * P.q x := (P.q).map_mul y x
      _ = u * k := by rw [hqᵤ, hqₖ]
  let orbit (h : P.tc.G) : Prop :=
    ∃ (γ : GL (Fin 2) F) (k u : P.tc.G), k ∈ L ∧ u ∈ infCompact P ∧
      h = P.tc.rat γ * g * k * u
  let Ψ : P.tc.G → ℂ := fun h => if orbit h then 1 else 0
  have orbit_rat (γ₀ : GL (Fin 2) F) (h : P.tc.G) :
      orbit (P.tc.rat γ₀ * h) ↔ orbit h := by
    constructor
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ₀⁻¹ * γ, k, u, hk, hu, ?_⟩
      calc
        h = (P.tc.rat γ₀)⁻¹ * (P.tc.rat γ₀ * h) := by group
        _ = (P.tc.rat γ₀)⁻¹ * (P.tc.rat γ * g * k * u) := by rw [heq]
        _ = P.tc.rat (γ₀⁻¹ * γ) * g * k * u := by simp [mul_assoc]
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ₀ * γ, k, u, hk, hu, ?_⟩
      calc
        P.tc.rat γ₀ * h = P.tc.rat γ₀ * (P.tc.rat γ * g * k * u) := by rw [heq]
        _ = P.tc.rat (γ₀ * γ) * g * k * u := by simp [mul_assoc]
  have orbit_level (h k₀ : P.tc.G) (hk₀ : k₀ ∈ L) :
      orbit (h * k₀) ↔ orbit h := by
    constructor
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ, k * k₀⁻¹, u, L_mul hk (L_inv hk₀), hu, ?_⟩
      calc
        h = (h * k₀) * k₀⁻¹ := by group
        _ = P.tc.rat γ * g * k * u * k₀⁻¹ := by rw [heq]
        _ = P.tc.rat γ * g * k * (u * k₀⁻¹) := by simp [mul_assoc]
        _ = P.tc.rat γ * g * k * (k₀⁻¹ * u) := by
          rw [(commute_L_U (L_inv hk₀) hu).symm]
        _ = P.tc.rat γ * g * (k * k₀⁻¹) * u := by group
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ, k * k₀, u, L_mul hk hk₀, hu, ?_⟩
      calc
        h * k₀ = P.tc.rat γ * g * k * u * k₀ := by rw [heq]
        _ = P.tc.rat γ * g * k * (u * k₀) := by simp [mul_assoc]
        _ = P.tc.rat γ * g * k * (k₀ * u) := by
          rw [(commute_L_U hk₀ hu).symm]
        _ = P.tc.rat γ * g * (k * k₀) * u := by group
  have orbit_inf (h u₀ : P.tc.G) (hu₀ : u₀ ∈ infCompact P) :
      orbit (h * u₀) ↔ orbit h := by
    constructor
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ, k, u * u₀⁻¹, hk, U_mul hu (U_inv hu₀), ?_⟩
      calc
        h = (h * u₀) * u₀⁻¹ := by group
        _ = P.tc.rat γ * g * k * (u * u₀⁻¹) := by
          calc
            (h * u₀) * u₀⁻¹ = (P.tc.rat γ * g * k * u) * u₀⁻¹ :=
              congrArg (fun z => z * u₀⁻¹) heq
            _ = P.tc.rat γ * g * k * (u * u₀⁻¹) := by group
    · rintro ⟨γ, k, u, hk, hu, heq⟩
      refine ⟨γ, k, u * u₀, hk, U_mul hu hu₀, ?_⟩
      simpa [mul_assoc] using congrArg (fun z => z * u₀) heq
  have hAut : ∀ γ h, Ψ (P.tc.rat γ * h) = Ψ h := by
    intro γ h
    by_cases hh : orbit h
    · have h' := (orbit_rat γ h).2 hh
      simp [Ψ, hh, h']
    · have h' : ¬ orbit (P.tc.rat γ * h) := by
        intro h'
        exact hh ((orbit_rat γ h).1 h')
      simp [Ψ, hh, h']
  have hLevel : ∀ h, ∀ k, k ∈ L → Ψ (h * k) = Ψ h := by
    intro h k hk
    by_cases hh : orbit h
    · have h' := (orbit_level h k hk).2 hh
      simp [Ψ, hh, h']
    · have h' : ¬ orbit (h * k) := by
        intro h'
        exact hh ((orbit_level h k hk).1 h')
      simp [Ψ, hh, h']
  have hInf : ∀ h, ∀ u, u ∈ infCompact P → Ψ (h * u) = Ψ h := by
    intro h u hu
    by_cases hh : orbit h
    · have h' := (orbit_inf h u hu).2 hh
      simp [Ψ, hh, h']
    · have h' : ¬ orbit (h * u) := by
        intro h'
        exact hh ((orbit_inf h u hu).1 h')
      simp [Ψ, hh, h']
  by_contra hnot
  let hr : GL (Fin 2) F := 1
  have hOrbitg : orbit g := by
    refine ⟨hr, 1, 1, L_one, U_one, ?_⟩
    simp [hr]
  have hΨg : Ψ g = 1 := by simp [Ψ, hOrbitg]
  have hClassical : ∀ (j : C.J) (z : ArtinPrimitiveRoots.A1.Spec.X F),
      classicalOf P Ψ j z = 0 := by
    intro j z
    let x : InfinitePlace F → ℂ := fun w => ArtinPrimitiveRoots.A1.Spec.horiz (z w)
    let y : InfinitePlace F → ℝ := fun w => ArtinPrimitiveRoots.A1.Spec.height (z w)
    have hy : ∀ w, 0 < y w := by
      intro w
      change 0 < ArtinPrimitiveRoots.A1.Spec.height (z w)
      rw [ArtinPrimitiveRoots.A1.Spec.height_eq_hyperbolicHeight]
      exact OAI.CubicEisenstein.hyperbolicHeight_pos (z w)
    change Ψ (nInf P x * aInf P y * j) = 0
    by_cases horb : orbit (nInf P x * aInf P y * j)
    · rcases horb with ⟨γ, k, u, hk, hu, heq⟩
      have hrep : g = P.tc.rat γ⁻¹ * (nInf P x * aInf P y * j) * u⁻¹ * k⁻¹ := by
        rw [heq, (P.tc.rat).map_inv]
        group
      exfalso
      exact hnot ⟨j, γ⁻¹, x, y, u⁻¹, k⁻¹, hy, U_inv hu, L_inv hk, hrep⟩
    · simp [Ψ, horb]
  have hclassical : ∀ j, j ∈ C.J → ∀ z : ArtinPrimitiveRoots.A1.Spec.X F,
      classicalOf P Ψ j z = 0 := by
    intro j hj z
    exact hClassical ⟨j, hj⟩ z
  have hzero := C.detect Ψ hAut hLevel hInf hclassical g
  rw [hΨg] at hzero
  norm_num at hzero

end ArtinPrimitiveRoots.A1.Theta
