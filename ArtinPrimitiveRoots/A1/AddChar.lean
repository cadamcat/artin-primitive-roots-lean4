import ArtinPrimitiveRoots.A1.Hilbert

/-!
# A1 interface, §4: additive character and Gauss sums

Frozen interface of part A1 (paper §§2, 2a, 3, App. 10). Each `sorry` is owned by a package of
`research/design/A1-DESIGN.md` §3, named in its docstring. Design: `research/design/A1-Interface.lean`
(Opus A1 sub-agent, 2026-10-07).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-! ## 4. Additive character (def:ar-psi; resolves D2) and Gauss sums (eq:normalized-gauss) -/

/-- Tate's standard additive character: `ψ_v = ψ_{ℚ_p} ∘ Tr_{F_v/ℚ_p}` with
`ψ_{ℚ_p}(x) = exp(2πi{x}_p)` at finite `v`, and `ψ_w(z) = exp(-2πi·Tr_{ℂ/ℝ} z) = exp(-4πi Re z)`
at complex `w` (independent of which of the two embeddings represents `w`).
Supplied by package P-PSI (local traces); its global consequences are the fields below. -/
structure AddCharData (F : Type) [Field F] [NumberField F] where
  ψ : (v : FinPlace F) → AddChar (v.adicCompletion F) ℂ
  /-- `ψ` is trivial on `F`: the archimedean factor is `exp(-2πi Tr_{F/ℚ} z)`. -/
  trivial_on_F : ∀ z : F, (Function.mulSupport fun v => ψ v (algebraMap F _ z)).Finite ∧
    (∏ᶠ v, ψ v (algebraMap F _ z)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) = 1
  /-- `ψ_v` is trivial on `O_v` at every finite place (Tate's `ψ_v` has conductor `𝔇_v⁻¹ ⊇ O_v`).
  Added 2026-10-07 after lane `a1-psi` showed `SData.e_diag_eq` false without it. -/
  integral : ∀ (v : FinPlace F) (x : v.adicCompletion F), x ∈ v.adicCompletionIntegers F →
    ψ v x = 1
  /-- at `v ∤ 𝔇`, `ψ_v` has conductor `O_v`. -/
  unramified : ∀ v : FinPlace F, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal →
    (∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F → ψ v x = 1) ∧
    ∀ π : F, HeightOneSpectrum.valuation F v π = WithZero.exp (-1) →
      ∃ x : 𝓞 F, ψ v (algebraMap F _ ((x : F) / π)) ≠ 1

/-- Complex component: `ψ_w(z) = exp(-4πi Re z)`. -/
def psiC (z : ℂ) : ℂ := Complex.exp (-(4 * Real.pi * Complex.I * (z.re : ℂ)))

/-- `e(x) = Π_{v∈S} ψ_v(x_v)` on `F_S` (02:50). -/
def SData.e (S : SData F CE condη) (A : AddCharData F) (x : S.FS) : ℂ :=
  (∏ v : S.Sf, A.ψ v.1 (x.1 v)) * ∏ w : InfinitePlace F, psiC (x.2 w)

/-- Global formula for `e` on `F` (derived in A1-DESIGN §2.2): if `z' - z ∈ O_v` at every finite
`v ∉ S` and `z' ∈ O_v` at `v ∈ S_f`, then `e(z) = exp(-2πi Tr_{F/ℚ} z')`. Package P-PSI. -/
theorem SData.e_diag_eq (S : SData F CE condη) (A : AddCharData F) (z z' : F)
    (h1 : ∀ v : FinPlace F, v ∉ S.Sf →
      HeightOneSpectrum.valuation F v (z' - z) ≤ 1)
    (h2 : ∀ v ∈ S.Sf, HeightOneSpectrum.valuation F v z' ≤ 1) :
    S.e A (S.diag z) = Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z' : ℂ))) := by
  sorry

/-- lem:s-lattice (e)/(f) (02:63–108; consumed at 05:152): `‖x‖_S = N(xR)` for `x ∈ F^×`
generating the exterior fractional ideal `I`; in particular `‖x‖_S ≥ 1` for `x ∈ R ∖ 0`.
Package P-ARITH-BASE. -/
theorem SData.absS_diag_eq_norm (S : SData F CE condη) (x : F) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  sorry

/-- lem:s-lattice, the self-duality consequence used at 02:397 and 06:76: for an exterior ideal `I`
with generator `c`, `(n, d) ↦ e(nd/c)` is a perfect pairing on `O_F/I`. Package P-ARITH-BASE. -/
theorem SData.e_pairing_perfect (S : SData F CE condη) (A : AddCharData F) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (c : F) (hc : S.IsGen c I) (n : 𝓞 F)
    (hn : ∀ d : 𝓞 F, S.e A (S.diag (algebraMap (𝓞 F) F (n * d) / c)) = 1) : n ∈ I := by
  sorry

/-- Normalized Gauss sum `γ_j(𝔠) = q_𝔠^{-1/2} Σ_{x mod 𝔠} χ_𝔠(x)^j e(x/c)` for a squarefree
exterior ideal `I = 𝔠` with allowed generator `c` (eq:normalized-gauss, 02:391). The finite sum is a
`finsum` over `O_F/I` (finite for `I ≠ ⊥`). -/
def gamma (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (j : ℤ)
    (I : Ideal (𝓞 F)) (c : F) : ℂ :=
  ((Ideal.absNorm I : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) *
    ∑ᶠ x : 𝓞 F ⧸ I, chiIdealPow D I (algebraMap (𝓞 F) F x.out) j *
      S.e A (S.diag (algebraMap (𝓞 F) F x.out / c))

/-- eq:gauss-crt (02:428–435). Package P-ARITH-GAUSS. -/
theorem gamma_crt (D : FieldData F) (S : SData F CE condη) (A : AddCharData F) (H : HilbertData F)
    (Bd : BData S H) (j : ℤ) (I J : Ideal (𝓞 F)) (hI : S.IsExterior I) (hJ : S.IsExterior J)
    (hIs : Squarefree I) (hJs : Squarefree J) (hIJ : IsCoprime I J) (c d : Fˣ)
    (hc : S.IsGen (c : F) I ∧ Bd.Allowed c) (hd : S.IsGen (d : F) J ∧ Bd.Allowed d) :
    gamma D S A j (I * J) ((c * d : Fˣ) : F) =
      chiIdealPow D I (d : F) j * chiIdealPow D J (c : F) j *
        gamma D S A j I c * gamma D S A j J d := by
  sorry


end ArtinPrimitiveRoots.A1
