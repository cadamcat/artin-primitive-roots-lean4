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

/-- Translating one finite-place section translates the global scalar
section by the corresponding local embedding. -/
theorem scalar_section_translate {s : ℂ} (v0 : FinPlace F)
    (Fs Fs' : GlobalSection P G s) (h : (P.loc v0).L)
    (hext : ∀ v, v ≠ v0 → Fs'.f v = Fs.f v)
    (hlocal : Fs'.f v0 = rtr h (Fs.f v0)) (hC : Fs'.fC = Fs.fC) :
    ∀ g, scalarOf P G Fs'.f Fs'.fC g =
      scalarOf P G Fs.f Fs.fC (g * P.emb v0 h) := by
  intro g
  obtain ⟨x, hx⟩ := P.q_surj g
  have hq : P.q (x * P.incl v0 h) = g * P.emb v0 h := by
    rw [map_mul, hx, P.q_incl]
  rw [← hq, ← hx, (scalarOf_q P G Fs' x).2,
    (scalarOf_q P G Fs (x * P.incl v0 h)).2]
  congr 1
  · apply finprod_congr
    intro v
    by_cases hv : v = v0
    · subst v
      rw [hlocal, map_mul, P.incl_compF]
      rfl
    · rw [hext v hv, map_mul, P.incl_compF_other v0 v (Ne.symm hv), mul_one]
  · apply Finset.prod_congr rfl
    intro w _
    rw [hC, map_mul, P.incl_compC, mul_one]

end ArtinPrimitiveRoots.A1.Theta
