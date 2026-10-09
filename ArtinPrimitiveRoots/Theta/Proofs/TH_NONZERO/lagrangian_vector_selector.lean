import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

private theorem selector_normalized {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) : ∃ x : (G.T v).V, G.lam v x = 1 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (G.lam_ne v)
  have hx' : G.lam v x ≠ 0 := by simpa using hx
  exact ⟨(G.lam v x)⁻¹ • x, by simp [hx']⟩

private theorem selector_omega_ne_zero {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) (a : (v.adicCompletion F)ˣ)
    (ha : a ∈ G.Alag v) : G.ω v a ≠ 0 := by
  obtain ⟨x, hx⟩ := selector_normalized G v
  have h := congrArg (fun f : (G.T v).V →ₗ[ℂ] (G.T v).V => G.lam v (f x))
    ((G.T v).σa_mul a a⁻¹)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    mul_inv_cancel, (G.T v).σa_one, LinearMap.id_apply] at h
  rw [G.lam_equiv v a ha, hx] at h
  intro hz
  have hc := (muThree D (H.hilb v a a⁻¹) : ℂˣ).ne_zero
  apply hc
  simpa [hz] using h.symm

private theorem selector_translate_eigen {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) (a y : (v.adicCompletion F)ˣ)
    (ha : a ∈ G.Alag v) (x : (G.T v).V) :
    G.lam v ((G.T v).σa y ((G.T v).σa a x)) =
      (((torusPairing D H v y a : ℂˣ) : ℂ) * G.ω v a) *
        G.lam v ((G.T v).σa y x) := by
  have hya := congrArg (fun f : (G.T v).V →ₗ[ℂ] (G.T v).V => G.lam v (f x))
    ((G.T v).σa_mul y a)
  have hay := congrArg (fun f : (G.T v).V →ₗ[ℂ] (G.T v).V => G.lam v (f x))
    ((G.T v).σa_mul a y)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul] at hya hay
  rw [G.lam_equiv v a ha, mul_comm a y] at hay
  rw [hya, mul_assoc, hay]
  simp [torusPairing, mul_assoc]

/-- A vector normalized by the Lagrangian functional can annihilate every
translate outside its Lagrangian. Finite torus image makes the polynomial
projections needed for the separating eigencharacters a finite process. -/
theorem lagrangian_vector_selector {P : CoverPackage D S H A}
    (G : GlobalDatum P) (v : FinPlace F) :
    ∃ x : (G.T v).V, G.lam v x = 1 ∧
      ∀ y : (v.adicCompletion F)ˣ, y ∉ G.Alag v →
        G.lam v ((G.T v).σa y x) = 0 := by
  classical
  let K := (v.adicCompletion F)ˣ
  have hfinite (s : Finset K) (hs : ∀ y ∈ s, y ∉ G.Alag v) :
      ∃ x : (G.T v).V, G.lam v x = 1 ∧
        ∀ y ∈ s, G.lam v ((G.T v).σa y x) = 0 := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := selector_normalized G v
      exact ⟨x, hx, by simp⟩
    | @insert y s hys ih =>
      obtain ⟨x, hx, hzero⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
      have hy : y ∉ G.Alag v := hs y (Finset.mem_insert_self y s)
      have hsep : ¬ ∀ a ∈ G.Alag v, torusPairing D H v y a = 1 :=
        fun h => hy ((G.alag_lagrangian v y).mpr h)
      push Not at hsep
      obtain ⟨a, ha, hpair⟩ := hsep
      let p : ℂ := ((torusPairing D H v y a : ℂˣ) : ℂ)
      let ω : ℂ := G.ω v a
      let β : ℂ := p * ω
      have hp : p ≠ 1 := by
        intro hp
        apply hpair
        exact rootsOfUnity.coe_injective (by simpa [p] using hp)
      have hω : ω ≠ 0 := selector_omega_ne_zero G v a ha
      have hdiff : ω - β ≠ 0 := by
        intro h
        have heq : ω = p * ω := sub_eq_zero.mp h
        exact hp ((mul_right_cancel₀ hω (by simpa using heq.symm)) )
      let x' := (ω - β)⁻¹ • ((G.T v).σa a x - β • x)
      refine ⟨x', ?_, ?_⟩
      · simp only [x', map_smul, map_sub, smul_eq_mul, G.lam_equiv v a ha, hx]
        change (ω - β)⁻¹ * (ω * 1 - β * 1) = 1
        simp only [mul_one, inv_mul_cancel₀ hdiff]
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · simp [x', selector_translate_eigen G v a z ha x, p, ω, β]
        · simp [x', selector_translate_eigen G v a z ha x, hzero z hz]
  let R := Set.range (fun y : {y : K // y ∉ G.Alag v} => (G.T v).σa y.1)
  have hR : R.Finite := (G.T v).σa_finite.subset (by
    rintro f ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩)
  let : Fintype R := hR.fintype
  let rep : R → K := fun r => (Classical.choose r.property).1
  let s : Finset K := Finset.univ.image rep
  have hs : ∀ y ∈ s, y ∉ G.Alag v := by
    intro y hy
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hy
    exact (Classical.choose r.property).property
  obtain ⟨x, hx, hzero⟩ := hfinite s hs
  refine ⟨x, hx, ?_⟩
  intro y hy
  let r : R := ⟨(G.T v).σa y, ⟨⟨y, hy⟩, rfl⟩⟩
  have hr : (G.T v).σa (rep r) = (G.T v).σa y := Classical.choose_spec r.property
  rw [← hr]
  exact hzero (rep r) (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)

end ArtinPrimitiveRoots.A1.Theta
