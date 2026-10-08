import ArtinPrimitiveRoots.Theta.TorusInd
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».CubicQuotient
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».FiniteInduction
import ArtinPrimitiveRoots.Theta.Proofs.«TH-GLOBAL-DATUM».CubicHilbert

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-- Local data with the trivial Lagrangian character, before global assembly. -/
structure GlobalLocalModel (D : FieldData F) (H : HilbertData F)
    (v : FinPlace F) (tame : Prop) where
  T : TorusRep D H v
  B : tame → TameTorusBasis T
  Alag : Subgroup (v.adicCompletion F)ˣ
  cubes : ∀ t : (v.adicCompletion F)ˣ, t ^ 3 ∈ Alag
  lagrangian : ∀ x : (v.adicCompletion F)ˣ,
    x ∈ Alag ↔ ∀ y ∈ Alag, torusPairing D H v x y = 1
  lam : T.V →ₗ[ℂ] ℂ
  lam_fixed : ∀ y ∈ Alag, ∀ x, lam (T.σa y x) = lam x
  lam_ne : lam ≠ 0
  alag_tame : tame → ∀ y : (v.adicCompletion F)ˣ,
    y ∈ Alag ↔ ∃ (k : ℤ) (u : (v.adicCompletion F)ˣ),
      IsLocUnit v u ∧ y = unifLoc v ^ (3 * k) * u
  lam_tame : ∀ h : tame, ∀ k : ZMod 3, lam ((B h).e k) = if k = 0 then 1 else 0

/-- The algebraic Lagrangian used at exceptional places. -/
theorem globalLocal_lagrangian (D : FieldData F) (H : HilbertData F) (v : FinPlace F) :
    ∃ L : Subgroup (v.adicCompletion F)ˣ,
      (∀ t : (v.adicCompletion F)ˣ, t ^ 3 ∈ L) ∧
      ∀ x : (v.adicCompletion F)ˣ,
        x ∈ L ↔ ∀ y ∈ L, torusPairing D H v x y = 1 := by
  classical
  let K := (v.adicCompletion F)ˣ
  let μ : rootsOfUnity 6 F →* rootsOfUnity 3 ℂ := {
    toFun := muThree D
    map_one' := by
      apply rootsOfUnity.coe_injective
      simp [muThree]
    map_mul' := by
      intro ζ ξ
      apply rootsOfUnity.coe_injective
      simp [muThree, map_mul, mul_pow]
  }
  have h_one_left (b : K) : H.hilb v 1 b = 1 :=
    H.sixth_power v 1 b ⟨1, by simp⟩
  have h_one_right (a : K) : H.hilb v a 1 = 1 := by
    have h := H.skew v a 1
    rw [h_one_left] at h
    simpa using h
  let c : K →* K →* rootsOfUnity 3 ℂ := {
    toFun := fun a => {
      toFun := fun b => μ (H.hilb v a b)
      map_one' := by rw [h_one_right, map_one]
      map_mul' := by intro b b'; rw [H.mul_right, map_mul]
    }
    map_one' := by
      apply MonoidHom.ext
      intro b
      change μ (H.hilb v 1 b) = 1
      rw [h_one_left, map_one]
    map_mul' := by
      intro a a'
      apply MonoidHom.ext
      intro b
      change μ (H.hilb v (a * a') b) = μ (H.hilb v a b) * μ (H.hilb v a' b)
      rw [H.mul_left, map_mul]
  }
  let p : K →* K →* rootsOfUnity 3 ℂ := c / c.flip
  have hp (x y : K) : p x y = torusPairing D H v x y := rfl
  have hp_self (x : K) : p x x = 1 := by simp [p]
  have hp_swap (x y : K) : p y x = (p x y)⁻¹ := by simp [p, inv_div]
  let isotropic : Set (Subgroup K) := {L | ∀ x ∈ L, ∀ y ∈ L, p x y = 1}
  obtain ⟨L, hL, hmax⟩ := zorn_le₀ isotropic (by
    intro C hC hchain
    rcases C.eq_empty_or_nonempty with hC0 | hCne
    · refine ⟨⊥, ?_, ?_⟩
      · intro x hx y hy
        have hx1 : x = 1 := Subgroup.mem_bot.mp hx
        simp [hx1]
      · simp [hC0]
    · refine ⟨sSup C, ?_, fun M hM => le_sSup hM⟩
      intro x hx y hy
      obtain ⟨M, hM, hxM⟩ := (Subgroup.mem_sSup_of_directedOn hCne hchain.directedOn).mp hx
      obtain ⟨N, hN, hyN⟩ := (Subgroup.mem_sSup_of_directedOn hCne hchain.directedOn).mp hy
      rcases hchain.total hM hN with hMN | hNM
      · exact hC hN x (hMN hxM) y hyN
      · exact hC hM x hxM y (hNM hyN))
  have hlag (x : K) : x ∈ L ↔ ∀ y ∈ L, p x y = 1 := by
    constructor
    · exact hL x
    · intro hx
      let E : Subgroup K := Subgroup.closure ((L : Set K) ∪ {x})
      have hE : E ∈ isotropic := by
        intro a ha b hb
        apply Subgroup.closure_induction₂ (p := fun a b _ _ => p a b = 1)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
        · intro a b ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact hL a ha b hb
          · have hb1 : b = x := Set.mem_singleton_iff.mp hb
            rw [hb1, hp_swap, hx a ha, inv_one]
          · have ha1 : a = x := Set.mem_singleton_iff.mp ha
            exact ha1 ▸ hx b hb
          · have ha1 : a = x := Set.mem_singleton_iff.mp ha
            have hb1 : b = x := Set.mem_singleton_iff.mp hb
            rw [ha1, hb1, hp_self]
        · intro a ha
          exact MonoidHom.map_one₂ p a
        · intro a ha
          exact map_one (p a)
        · intro a b z ha hb hz hpa hpb
          rw [MonoidHom.map_mul₂, hpa, hpb, one_mul]
        · intro a b z ha hb hz hpa hpb
          rw [map_mul, hpa, hpb, one_mul]
        · intro a b ha hb hab
          rw [MonoidHom.map_inv₂, hab, inv_one]
        · intro a b ha hb hab
          rw [map_inv, hab, inv_one]
      have hLE : L ≤ E := fun y hy => Subgroup.subset_closure (Or.inl hy)
      exact hmax hE hLE (Subgroup.subset_closure (Or.inr (Set.mem_singleton x)))
  refine ⟨L, ?_, ?_⟩
  · intro t
    apply (hlag (t ^ 3)).mpr
    intro y hy
    change p.flip y (t ^ 3) = 1
    rw [map_pow]
    apply Subtype.ext
    exact (p t y).2
  · intro x
    simpa only [hp] using hlag x

/-- Induce the trivial character of a lifted Lagrangian; evaluate at the identity coset. -/
theorem globalLocal_wild_model (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (L : Subgroup (v.adicCompletion F)ˣ)
    (hc : ∀ t : (v.adicCompletion F)ˣ, t ^ 3 ∈ L)
    (hl : ∀ x : (v.adicCompletion F)ˣ,
      x ∈ L ↔ ∀ y ∈ L, torusPairing D H v x y = 1) :
    ∃ M : GlobalLocalModel D H v False, M.Alag = L := by
  classical
  obtain ⟨seed, hseed, _⟩ := exists_torusRep D H v (H.steinberg v)
  letI : Nontrivial seed.V := hseed
  let control := torusRep_cube_control seed
  letI : Finite (LocalCubeQuotient v) := control.finite
  letI : Fintype (LocalCubeQuotient v) := Fintype.ofFinite _
  obtain ⟨B⟩ := exists_cubeHilbertData D H v L (fun x hx y hy => (hl x).mp hx y hy)
  obtain ⟨M⟩ := FiniteTorusInduction.exists_model (LocalCubeQuotient v)
    B.c (L.map (localCubeMap v)) B.c_isotropic
  have hker : (localCubeMap v).ker =
      (powMonoidHom 3 : (v.adicCompletion F)ˣ →* (v.adicCompletion F)ˣ).range :=
    QuotientGroup.ker_mk' _
  have hcube (t : (v.adicCompletion F)ˣ) : localCubeMap v (t ^ 3) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact ⟨t, rfl⟩
  let T : TorusRep D H v := {
    V := M.V
    σa := fun y => M.σ (localCubeMap v y)
    σa_one := by rw [map_one, M.σ_one]
    σa_mul := by
      intro x y
      rw [M.σ_mul, ← map_mul, B.c_mk]
    σa_cube := by intro t; rw [hcube, M.σ_one]
    σa_smooth := by
      obtain ⟨m, hm, hs⟩ := seed.σa_smooth
      refine ⟨m, hm, ?_⟩
      intro u hu
      obtain ⟨t, ht⟩ := control.scalar_cube u ⟨1, by simpa using hs u hu⟩
      rw [ht, hcube, M.σ_one]
    σa_finite := M.σ_finite.subset (by
      rintro _ ⟨y, rfl⟩
      exact ⟨localCubeMap v y, rfl⟩)
  }
  refine ⟨{
    T := T
    B := fun h => False.elim h
    Alag := L
    cubes := hc
    lagrangian := hl
    lam := M.lam
    lam_fixed := ?_
    lam_ne := M.lam_ne
    alag_tame := fun h => False.elim h
    lam_tame := fun h => False.elim h
  }, rfl⟩
  intro y hy x
  exact M.lam_fixed (localCubeMap v y) (Subgroup.mem_map_of_mem _ hy) x

/-- At a tame place use the valuation classes and their coordinate at zero. -/
theorem globalLocal_tame_model (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) (hv : (6 : 𝓞 F) ∉ v.asIdeal) :
    Nonempty (GlobalLocalModel D H v True) := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
