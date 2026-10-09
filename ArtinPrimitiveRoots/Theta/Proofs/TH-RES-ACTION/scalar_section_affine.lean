import ArtinPrimitiveRoots.Theta.Eis

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta
open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {H : HilbertData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {A : AddCharData F}
variable {P : CoverPackage D S H A} {G : GlobalDatum P}

/-- The scalar section is linear in one finite-place section when all
other finite factors and the archimedean factors agree. -/
theorem scalar_section_affine {s : ℂ} (v0 : FinPlace F)
    (Fs Fs' Fs'' : GlobalSection P G s) (c : ℂ)
    (hext : ∀ v, v ≠ v0 → Fs'.f v = Fs.f v ∧ Fs''.f v = Fs.f v)
    (hlocal : Fs''.f v0 = Fs.f v0 + c • Fs'.f v0)
    (hC' : Fs'.fC = Fs.fC) (hC'' : Fs''.fC = Fs.fC) :
    ∀ g, scalarOf P G Fs''.f Fs''.fC g =
      scalarOf P G Fs.f Fs.fC g + c * scalarOf P G Fs'.f Fs'.fC g := by
  intro g
  obtain ⟨x, hx⟩ := P.q_surj g
  have hfactor (R : GlobalSection P G s) :
      (∏ᶠ v, G.lam v (R.f v (P.compF v x))) =
        G.lam v0 (R.f v0 (P.compF v0 x)) *
          ∏ᶠ (v) (_ : v ≠ v0), G.lam v (R.f v (P.compF v x)) :=
    (mul_finprod_cond_ne v0 (scalarOf_q P G R x).1).symm
  have hprod' : (∏ᶠ (v) (_ : v ≠ v0), G.lam v (Fs'.f v (P.compF v x))) =
      ∏ᶠ (v) (_ : v ≠ v0), G.lam v (Fs.f v (P.compF v x)) := by
    apply finprod_congr
    intro v
    apply finprod_congr
    intro hv
    rw [(hext v hv).1]
  have hprod'' : (∏ᶠ (v) (_ : v ≠ v0), G.lam v (Fs''.f v (P.compF v x))) =
      ∏ᶠ (v) (_ : v ≠ v0), G.lam v (Fs.f v (P.compF v x)) := by
    apply finprod_congr
    intro v
    apply finprod_congr
    intro hv
    rw [(hext v hv).2]
  have hlocal' : G.lam v0 (Fs''.f v0 (P.compF v0 x)) =
      G.lam v0 (Fs.f v0 (P.compF v0 x)) +
        c * G.lam v0 (Fs'.f v0 (P.compF v0 x)) := by
    rw [hlocal]
    simp
  rw [← hx, (scalarOf_q P G Fs'' x).2, (scalarOf_q P G Fs x).2,
    (scalarOf_q P G Fs' x).2]
  rw [hfactor Fs'', hfactor Fs, hfactor Fs', hprod'', hprod', hC'', hC', hlocal']
  ring

end ArtinPrimitiveRoots.A1.Theta
