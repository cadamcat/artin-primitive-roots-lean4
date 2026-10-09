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

set_option backward.isDefEq.respectTransparency false in
/-- The bare intertwined scalar has finite local support and its product formula at every lift. -/
theorem intertwined_scalar_q
    (P : CoverPackage D S H A) (G : GlobalDatum P)
    (μ : ∀ v : FinPlace F, LocHaar v) {s : ℂ} (hs : 0 < s.re)
    (Fs : GlobalSection P G s) (r : P.RP) :
    let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
      if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
      else sphWeyl P G v (fun h => hv (Fs.sub h)) s
    (Function.mulSupport fun v => G.lam v (fM v (P.compF v r))).Finite ∧
    scalarOf P G fM (fun w => intertwineC (Fs.fC w)) (P.q r) =
      (∏ᶠ v, G.lam v (fM v (P.compF v r))) *
        ∏ w, intertwineC (Fs.fC w) (P.compC w r) := by
  let fM : ∀ v : FinPlace F, (P.loc v).L → (G.T v).V := fun v =>
    if hv : v ∈ Fs.T0 then intertwine (P.loc v) (μ v) (Fs.f v)
    else sphWeyl P G v (fun h => hv (Fs.sub h)) s
  change (Function.mulSupport fun v => G.lam v (fM v (P.compF v r))).Finite ∧
    scalarOf P G fM (fun w => intertwineC (Fs.fC w)) (P.q r) =
      (∏ᶠ v, G.lam v (fM v (P.compF v r))) *
        ∏ w, intertwineC (Fs.fC w) (P.compC w r)
  have hfinite (a : P.RP) :
      (Function.mulSupport fun v => G.lam v (fM v (P.compF v a))).Finite :=
    (scalarM_q P G μ hs Fs a).1
  have hgen (v : FinPlace F) (ζ : rootsOfUnity 3 ℂ) (a : (P.loc v).L) :
      fM v ((P.loc v).z ζ * a) = ((ζ : ℂˣ) : ℂ) • fM v a := by
    dsimp only [fM]
    by_cases hv : v ∈ Fs.T0
    · simp only [dite_eq_left hv]
      simpa only [TorusRep.weyl] using
        (intertwine_isSection (P.loc v) (G.T v) (μ v) s hs (Fs.f v)
          (Fs.f_sec v)).2.2.1 ζ a
    · simp only [dite_eq_right hv]
      simpa only [sphWeyl, TorusRep.weyl] using
        ((spherical_section (P.loc v) (P.tame v (fun h => hv (Fs.sub h)))
          (G.T v).weyl (G.B v (fun h => hv (Fs.sub h))).weyl
          (fun h => hv (Fs.sub (S.over6 v h))) (-s)).choose_spec.1).2.1 ζ a
  let y : P.RP := Function.surjInv P.q_surj (P.q r)
  have hq : P.q r = P.q y :=
    (Function.rightInverse_surjInv P.q_surj (P.q r)).symm
  obtain ⟨ζ, hζfin, hζprod, hcomp, hcompC⟩ := (P.q_eq r y).mp hq
  let α : FinPlace F → ℂ := fun v => G.lam v (fM v (P.compF v r))
  let β : FinPlace F → ℂ := fun v => G.lam v (fM v (P.compF v y))
  have hrel : α = fun v => ((ζ v : ℂˣ) : ℂ) * β v := by
    funext v
    dsimp only [α, β]
    rw [hcomp v, hgen v]
    simp
  let eval : rootsOfUnity 3 ℂ →* ℂ :=
    { toFun := fun z => ((z : ℂˣ) : ℂ)
      map_one' := rfl
      map_mul' := by intros; rfl }
  have hζscalarfin : (Function.mulSupport fun v => ((ζ v : ℂˣ) : ℂ)).Finite := by
    apply hζfin.subset
    intro v hv
    change ζ v ≠ 1
    intro h1
    exact hv (by change ((ζ v : ℂˣ) : ℂ) = 1; rw [h1]; rfl)
  have hζscalarprod : (∏ᶠ v, ((ζ v : ℂˣ) : ℂ)) = 1 := by
    calc
      _ = eval (∏ᶠ v, ζ v) := (eval.map_finprod hζfin).symm
      _ = 1 := by rw [hζprod, map_one]
  have hαprod : (∏ᶠ v, α v) = ∏ᶠ v, β v := by
    rw [hrel, finprod_mul_distrib hζscalarfin (hfinite y), hζscalarprod, one_mul]
  refine ⟨hfinite r, ?_⟩
  change (∏ᶠ v, β v) * ∏ w, intertwineC (Fs.fC w) (P.compC w y) =
    (∏ᶠ v, α v) * ∏ w, intertwineC (Fs.fC w) (P.compC w r)
  rw [hαprod]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  exact (congrArg (intertwineC (Fs.fC w)) (hcompC w)).symm

end ArtinPrimitiveRoots.A1.Theta
