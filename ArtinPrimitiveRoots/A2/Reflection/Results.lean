import ArtinPrimitiveRoots.A2.Defs
import ArtinPrimitiveRoots.A2.QuadraticSieve
import ArtinPrimitiveRoots.A1.Coefficients

/-!
# Section 4: reflected second moment and quadratic large sieve
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- **prop:reflection** (02a-coefficient-family.tex:101-121; 04-reflection.tex:1027-1228).
For the fixed arithmetic data and compact sets, the reflected coefficient family has the stated
dyadic second moment.  The same constant works for every norm-one translate in the fixed compact
set `T`; the total bound is included as the paper's immediate consequence. -/
theorem prop_reflection
    (D : ArtinPrimitiveRoots.A1.FieldData F)
    (S : ArtinPrimitiveRoots.A1.SData F CE condη)
    (H : ArtinPrimitiveRoots.A1.HilbertData F)
    (A : ArtinPrimitiveRoots.A1.AddCharData F)
    (Bd : ArtinPrimitiveRoots.A1.BData S H)
    (η Λ G : ArtinPrimitiveRoots.A1.HeckeChar F)
    (hηfin : IsOfFinOrder η)
    (hηoutsideS : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F,
      v ∉ S.Sf → η.UnramifiedAt v)
    (hΛunit : ∀ x, ‖((Λ x : ℂˣ) : ℂ)‖ = 1)
    (hGfin : IsOfFinOrder G)
    (hGauss : ∀ v : ArtinPrimitiveRoots.A1.FinPlace F, v ∉ S.Sf →
      Λ.UnramifiedAt v ∧ G.UnramifiedAt v ∧
      ∀ p : Fˣ, S.IsGen (p : F) v.asIdeal → Bd.Allowed p →
        ArtinPrimitiveRoots.A1.gamma D S A 1 v.asIdeal p *
          ArtinPrimitiveRoots.A1.gamma D S A 2 v.asIdeal p =
            -(Λ.primeValue v * G.primeValue v))
    (cgen : S.SqfExtIdeal → F)
    (hcgen : ∀ I, ∃ c : Fˣ, (c : F) = cgen I ∧ S.IsGen (c : F) I.1 ∧ Bd.Allowed c)
    (K T : Set S.FSˣ) (hK : IsCompact K) (hT : IsCompact T)
    (hTnorm : ∀ t ∈ T, S.absS (t : S.FS) = 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (Z P Dlen : ℝ), (hZ : 2 ≤ Z) → 1 ≤ P → 1 ≤ Dlen →
        ∀ t ∈ T,
          (∑' r : {r : ReflectionRow S // InReflectionBox D S K t Z (by linarith) r ∧
              P ≤ idealNorm r.h.1 ∧ idealNorm r.h.1 < 2 * P ∧
              Dlen ≤ idealNorm r.d.1 ∧ idealNorm r.d.1 < 2 * Dlen},
            ‖ArtinPrimitiveRoots.A1.Bm D S A
              (ArtinPrimitiveRoots.A1.vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ≤
              C * Real.rpow Z ε * Real.rpow P (1 / 2 : ℝ) *
                (Dlen + Dlen ^ 2 * P / Z) ∧
          (∑' r : {r : ReflectionRow S // InReflectionBox D S K t Z (by linarith) r},
            ‖ArtinPrimitiveRoots.A1.Bm D S A
              (ArtinPrimitiveRoots.A1.vartheta Λ G η) cgen (r.1.m : F) Z‖ ^ 2) ≤
              C * Real.rpow Z (2 * M0 - 1 + ε) := by
  sorry

end ArtinPrimitiveRoots.A2
