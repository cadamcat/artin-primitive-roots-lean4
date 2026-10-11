import ArtinPrimitiveRoots.Theta.Proofs.TH_RES_WHIT.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}
  {μ : ∀ v : FinPlace F, LocHaar v}

private noncomputable def jacquetSectionLinearMap (v : S.Sf) :
    sectionSpace (P.loc v.1) (G.T v.1) (1 / 6) →ₗ[ℂ] (G.T v.1).V := by
  let L := P.loc v.1
  let T := G.T v.1
  let J0 : (L.L → T.V) → T.V := fun f => jacquet L A (μ v.1) f
  have hzero : J0 0 = 0 := by
    have h := jacquet_linear L T A (μ v.1) (1 / 6) (0 : L.L → T.V) 0
      (by exact (sectionSpace L T (1 / 6)).zero_mem)
      (by exact (sectionSpace L T (1 / 6)).zero_mem) 1
    have h' : J0 0 = J0 0 + J0 0 := by simpa [J0] using h
    have h'' : J0 0 + J0 0 = J0 0 + 0 := by simpa using h'.symm
    exact add_left_cancel h''
  exact {
    toFun := fun f => J0 f.1
    map_add' := by
      intro f g
      have h := jacquet_linear L T A (μ v.1) (1 / 6) f.1 g.1 f.2 g.2 1
      simpa [J0] using h
    map_smul' := by
      intro c f
      have h := jacquet_linear L T A (μ v.1) (1 / 6) (0 : L.L → T.V) f.1
        (by exact (sectionSpace L T (1 / 6)).zero_mem) f.2 c
      simpa [J0, hzero] using h
  }

private theorem jacquetPartialFactor
    (W : MultilinearMap ℂ
      (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ)
    (hW : ∀ (v : S.Sf) (f : ∀ w : S.Sf,
      sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (t : v.1.adicCompletion F),
      W (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
        ((P.loc v.1).n (Multiplicative.ofAdd t)) (f v))) = A.ψ v.1 t * W f)
    (v : S.Sf) (f : ∀ w : S.Sf,
      sectionSpace (P.loc w.1) (G.T w.1) (1 / 6)) :
    ∃ c : (G.T v.1).V →ₗ[ℂ] ℂ, ∀ x : sectionSpace (P.loc v.1) (G.T v.1) (1 / 6),
      W (Function.update f v x) = c (jacquetSectionLinearMap (P := P) (G := G) (A := A)
        (μ := μ) v x) := by
  let L := P.loc v.1
  let T := G.T v.1
  let s : ℂ := 1 / 6
  let ℓ : sectionSpace L T s →ₗ[ℂ] ℂ := {
    toFun := fun x => W (Function.update f v x)
    map_add' := by
      intro x y
      simpa [Function.update_self] using W.map_update_add f v x y
    map_smul' := by
      intro c x
      simpa [Function.update_self] using W.map_update_smul f v c x
  }
  obtain ⟨ℓext, hℓext⟩ := LinearMap.exists_extend ℓ
  have hwhit : IsWhittakerOn L A (sectionSpace L T s) ℓext := by
    intro g hg t
    let x : sectionSpace L T s := ⟨g, hg⟩
    let xn := sectionRtr L T s (L.n (Multiplicative.ofAdd t)) x
    have h1 : ℓext (rtr (L.n (Multiplicative.ofAdd t)) g) = ℓ xn := by
      have h := congrArg (fun q : sectionSpace L T s →ₗ[ℂ] ℂ => q xn) hℓext
      simpa [LinearMap.comp_apply, ℓ, xn, sectionRtr] using h
    have h0 : ℓext g = ℓ x := by
      have h := congrArg (fun q : sectionSpace L T s →ₗ[ℂ] ℂ => q x) hℓext
      simpa [LinearMap.comp_apply, ℓ] using h
    have h := hW v (Function.update f v x) t
    rw [h1, h0]
    simpa [ℓ, Function.update_self, sectionRtr, x, xn] using h
  obtain ⟨c, hc⟩ := whittaker_twoCell L T A (μ v.1) s ℓext hwhit
  refine ⟨c, ?_⟩
  intro x
  have hext : ℓext x.1 = ℓ x := by
    have h := congrArg (fun q : sectionSpace L T s →ₗ[ℂ] ℂ => q x) hℓext
    simpa [LinearMap.comp_apply, ℓ] using h
  have hfactor := hc x.1 x.2
  change W (Function.update f v x) = c (jacquetSectionLinearMap
    (P := P) (G := G) (A := A) (μ := μ) v x)
  simpa [ℓ, jacquetSectionLinearMap, L, T, s] using hext.symm.trans hfactor

/-- A multilinear form on local section spaces, psi-equivariant separately in every
coordinate, factors through the local Jacquet maps. Apply whittaker_twoCell to each partial
functional and descend successively through each Jacquet kernel; complements extend to V.
Uses: whittaker_twoCell, jacquet_linear, whittaker_extend (if extending partial functionals).
Feeds: thetaWhit_multilinear after thetaWhit_section_multilinear. -/
theorem thetaWhit_jacquet_factorization
    (W : MultilinearMap ℂ
      (fun v : S.Sf => sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)) ℂ)
    (hW : ∀ (v : S.Sf) (f : ∀ w : S.Sf, sectionSpace (P.loc w.1) (G.T w.1) (1 / 6))
      (t : v.1.adicCompletion F),
      W (Function.update f v (sectionRtr (P.loc v.1) (G.T v.1) (1 / 6)
        ((P.loc v.1).n (Multiplicative.ofAdd t)) (f v))) = A.ψ v.1 t * W f) :
    ∃ Λ : MultilinearMap ℂ (fun v : S.Sf => (G.T v.1).V) ℂ,
      ∀ f : ∀ v : S.Sf, sectionSpace (P.loc v.1) (G.T v.1) (1 / 6),
        W f = Λ (fun v => jacquet (P.loc v.1) A (μ v.1) (f v)) := by
  classical
  let E : ∀ v : S.Sf, Type := fun v =>
    sectionSpace (P.loc v.1) (G.T v.1) (1 / 6)
  let J : ∀ v : S.Sf, E v →ₗ[ℂ] (G.T v.1).V := fun v =>
    jacquetSectionLinearMap (P := P) (G := G) (A := A) (μ := μ) v
  let R : ∀ v : S.Sf, Submodule ℂ ((G.T v.1).V) := fun v => LinearMap.range (J v)
  have hq_exists : ∀ v : S.Sf, ∃ q : R v →ₗ[ℂ] E v,
      (J v).rangeRestrict.comp q = LinearMap.id := by
    intro v
    exact (J v).rangeRestrict.exists_rightInverse_of_surjective (J v).range_rangeRestrict
  choose q hq using hq_exists
  have hp_exists : ∀ v : S.Sf, ∃ p : (G.T v.1).V →ₗ[ℂ] R v,
      p.comp (R v).subtype = LinearMap.id := by
    intro v
    exact LinearMap.exists_extend (LinearMap.id : R v →ₗ[ℂ] R v)
  choose p hp using hp_exists
  have hq_apply (v : S.Sf) (x : R v) : J v (q v x) = x.1 := by
    have h := congrArg (fun g : R v →ₗ[ℂ] R v => g x) (hq v)
    simpa [LinearMap.comp_apply] using congrArg Subtype.val h
  have hp_apply (v : S.Sf) (x : R v) : p v x.1 = x := by
    have h := congrArg (fun g : R v →ₗ[ℂ] R v => g x) (hp v)
    simpa [LinearMap.comp_apply] using h
  let K : ∀ v : S.Sf, (G.T v.1).V →ₗ[ℂ] E v := fun v => (q v).comp (p v)
  refine ⟨W.compLinearMap K, ?_⟩
  intro f
  let rf : ∀ v : S.Sf, R v := fun v => ⟨J v (f v), ⟨f v, rfl⟩⟩
  let target : ∀ v : S.Sf, E v := fun v => q v (rf v)
  let repl : Finset (S.Sf) → (∀ v : S.Sf, E v) := fun s v =>
    if v ∈ s then target v else f v
  have hstep (s : Finset (S.Sf)) (v : S.Sf) (hv : v ∉ s) :
      W (repl s) = W (repl (insert v s)) := by
    let u := repl s
    obtain ⟨c, hc⟩ := jacquetPartialFactor (P := P) (G := G) (A := A) (μ := μ)
      W hW v u
    have hu : u v = f v := by simp [u, repl, hv]
    have hJ : J v (u v) = J v (target v) := by
      calc
        J v (u v) = J v (f v) := congrArg (J v) hu
        _ = J v (target v) := by
          dsimp [target]
          rw [hq_apply]
    have hrep : repl (insert v s) = Function.update u v (target v) := by
      funext i
      by_cases hi : i = v
      · subst i
        simp [repl, u, hv]
      · simp [repl, u, hi, Finset.mem_insert]
    rw [hrep]
    calc
      W u = c (J v (u v)) := by simpa [u, Function.update_self] using hc (u v)
      _ = c (J v (target v)) := by rw [hJ]
      _ = W (Function.update u v (target v)) := by simpa using (hc (target v)).symm
  have hAll : ∀ s : Finset (S.Sf), W f = W (repl s) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [repl]
    | @insert v s hv ih => exact ih.trans (hstep s v hv)
  have huniv : repl S.Sf.attach = target := by
    funext v
    simp [repl]
  have hWrep : W f = W target :=
    (hAll S.Sf.attach).trans (congrArg W huniv)
  have htarget : target = fun v => K v (J v (f v)) := by
    funext v
    change q v (rf v) = q v (p v (J v (f v)))
    have hproj : p v (J v (f v)) = rf v := by
      simpa [rf] using hp_apply v (rf v)
    rw [← hproj]
  change W f = W (fun v => K v (J v (f v)))
  calc
    W f = W target := hWrep
    _ = W (fun v => K v (J v (f v))) := by rw [← htarget]

end ArtinPrimitiveRoots.A1.Theta
