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

private theorem trace_eq_pair_sum_re {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      ∑ w : InfinitePlace F, (w.embedding z + ComplexEmbedding.conjugate w.embedding z) := by
  classical
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := ℂ) (x := z)
  have hring :
      (∑ φ : F →+* ℂ, φ z) =
        ∑ σ : F →ₐ[ℚ] ℂ, σ z := by
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hall : (Algebra.trace ℚ F z : ℂ) = ∑ φ : F →+* ℂ, φ z := by
    rw [hring.symm] at htrace
    exact htrace
  rw [hall]
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : F →+* ℂ => InfinitePlace.mk φ) (f := fun φ => φ z)]
  apply Finset.sum_congr rfl
  intro w hw
  have hmk (φ : F →+* ℂ) : InfinitePlace.mk φ = w ↔
      φ = w.embedding ∨ φ = ComplexEmbedding.conjugate w.embedding := by
    constructor
    · intro h
      rw [← InfinitePlace.mk_embedding w] at h
      have h' := InfinitePlace.mk_eq_iff.mp h
      rcases h' with h' | h'
      · exact Or.inl (by simpa using h')
      · right
        have hc := congrArg ComplexEmbedding.conjugate h'
        simpa using hc
    · intro h
      rw [← InfinitePlace.mk_embedding w]
      apply InfinitePlace.mk_eq_iff.mpr
      rcases h with h | h
      · exact Or.inl (by simpa using h)
      · right
        have hc := congrArg ComplexEmbedding.conjugate h
        simpa using hc
  have hneq : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro h
    apply (IsTotallyComplex.complexEmbedding_not_isReal w.embedding)
    rw [ComplexEmbedding.isReal_iff]
    exact h.symm
  have hset : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      ({w.embedding, ComplexEmbedding.conjugate w.embedding} : Finset (F →+* ℂ)) := by
    ext φ
    simp [hmk]
  change (∑ φ ∈ Finset.univ.filter
    (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ z) = _
  rw [hset, Finset.sum_pair hneq]

private theorem trace_eq_two_real_sum {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (Algebra.trace ℚ F z : ℂ) =
      (2 : ℂ) * ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ) := by
  rw [trace_eq_pair_sum_re]
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [Finset.mul_sum]

private theorem arch_exp_eq_trace {F : Type} [Field F] [NumberField F]
    [IsTotallyComplex F] (z : F) :
    (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ))) := by
  rw [← Complex.exp_sum]
  apply congrArg Complex.exp
  calc
    ∑ w : InfinitePlace F,
        -(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)) =
        -(4 * Real.pi * Complex.I *
          ∑ w : InfinitePlace F, ((w.embedding z).re : ℂ)) := by
            rw [Finset.sum_neg_distrib, Finset.mul_sum]
    _ = -(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z : ℂ)) := by
      rw [trace_eq_two_real_sum]
      ring

/-- Global formula for `e` on `F` (derived in A1-DESIGN §2.2): if `z' - z ∈ O_v` at every finite
`v ∉ S` and `z' ∈ O_v` at `v ∈ S_f`, then `e(z) = exp(-2πi Tr_{F/ℚ} z')`. Package P-PSI. -/
theorem SData.e_diag_eq [IsTotallyComplex F] (S : SData F CE condη) (A : AddCharData F) (z z' : F)
    (h1 : ∀ v : FinPlace F, v ∉ S.Sf →
      HeightOneSpectrum.valuation F v (z' - z) ≤ 1)
    (h2 : ∀ v ∈ S.Sf, HeightOneSpectrum.valuation F v z' ≤ 1) :
    S.e A (S.diag z) = Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z' : ℂ))) := by
  classical
  let f : FinPlace F → ℂ := fun v =>
    A.ψ v (algebraMap F (v.adicCompletion F) (z - z'))
  have houtside (v : FinPlace F) (hv : v ∉ S.Sf) : f v = 1 := by
    have hval : v.valuation F (z - z') ≤ 1 := by
      rw [show z - z' = -(z' - z) by ring, Valuation.map_neg]
      exact h1 v hv
    have hmem : (algebraMap F (v.adicCompletion F) (z - z')) ∈
        v.adicCompletionIntegers F := by
      change ((z - z' : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hval
    exact A.integral v _ hmem
  let e : {v : FinPlace F // v ∈ S.Sf} ↪ PLift (FinPlace F) :=
    ⟨fun v => PLift.up v.1, fun a b h => Subtype.ext (congrArg PLift.down h)⟩
  let s : Finset (PLift (FinPlace F)) := S.Sf.attach.map e
  have hsupp : Function.mulSupport (f ∘ PLift.down) ⊆ s := by
    intro x hx
    change f x.down ≠ 1 at hx
    have hxS : x.down ∈ S.Sf := by
      by_contra hnot
      exact hx (houtside x.down hnot)
    apply Finset.mem_map.mpr
    exact ⟨⟨x.down, hxS⟩, Finset.mem_attach _ _, by cases x; rfl⟩
  have hfinprod : (∏ᶠ v, f v) = ∏ v : S.Sf, f v := by
    rw [finprod_eq_prod_plift_of_mulSupport_subset hsupp]
    simp [s, e]
    apply Finset.prod_congr rfl
    intro v hv
    rfl
  have hinside (v : S.Sf) :
      A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z') = 1 := by
    apply A.integral
    change ((z' : F) : v.1.adicCompletion F) ∈ v.1.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact h2 v.1 v.2
  have hlocal (v : S.Sf) :
      f v.1 = A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z) := by
    have hsum :
        algebraMap F (v.1.adicCompletion F) (z - z') +
            algebraMap F (v.1.adicCompletion F) z' =
          algebraMap F (v.1.adicCompletion F) z := by
      rw [← map_add]
      congr 1
      ring
    have hchar := (A.ψ v.1).map_add_eq_mul
      (algebraMap F (v.1.adicCompletion F) (z - z'))
      (algebraMap F (v.1.adicCompletion F) z')
    rw [hsum, hinside v, mul_one] at hchar
    exact hchar.symm
  have hSprod :
      (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) =
        ∏ v : S.Sf, f v := by
    apply Finset.prod_congr rfl
    intro v hv
    exact (hlocal v).symm
  have hglobal := (A.trivial_on_F (z - z')).2
  rw [hfinprod, ← hSprod] at hglobal
  change
    (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F (z - z') : ℂ))) = 1 at hglobal
  have hprod :
      (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) =
        Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ F (z - z') : ℂ)) := by
    have hexp := eq_inv_of_mul_eq_one_right hglobal
    rw [Complex.exp_neg] at hexp
    exact ((inv_inj).mp hexp).symm
  change
    (∏ v : S.Sf, A.ψ v.1 (algebraMap F (v.1.adicCompletion F) z)) *
        ∏ w : InfinitePlace F, psiC (w.embedding z) =
      Complex.exp (-(2 * Real.pi * Complex.I * (Algebra.trace ℚ F z' : ℂ)))
  rw [hprod]
  change Complex.exp (2 * Real.pi * Complex.I *
      (Algebra.trace ℚ F (z - z') : ℂ)) *
      (∏ w : InfinitePlace F,
        Complex.exp (-(4 * Real.pi * Complex.I * ((w.embedding z).re : ℂ)))) = _
  rw [arch_exp_eq_trace]
  rw [← Complex.exp_add]
  congr 1
  simp only [map_sub]
  push_cast
  ring

/-- lem:s-lattice (e)/(f) (02:63–108; consumed at 05:152): `‖x‖_S = N(xR)` for `x ∈ F^×`
generating the exterior fractional ideal `I`; in particular `‖x‖_S ≥ 1` for `x ∈ R ∖ 0`.
Package P-ARITH-BASE. -/
theorem SData.absS_diag_eq_norm [IsTotallyComplex F] (S : SData F CE condη) (x : F) (I : Ideal (𝓞 F))
    (hI : S.IsExterior I) (hx : S.IsGen x I) :
    S.absS (S.diag x) = Ideal.absNorm I := by
  sorry

/-- lem:s-lattice, the self-duality consequence used at 02:397 and 06:76: for an exterior ideal `I`
with generator `c`, `(n, d) ↦ e(nd/c)` is a perfect pairing on `O_F/I`. Package P-ARITH-BASE.
Corrected per rev-theta to state both annihilator directions under fixed field data. -/
theorem SData.e_pairing_perfect (D : FieldData F) (S : SData F CE condη)
    (A : AddCharData F) (I : Ideal (𝓞 F)) (hI : S.IsExterior I) (c : F)
    (hc : S.IsGen c I) :
    (∀ n : 𝓞 F, n ∈ I → ∀ d : 𝓞 F,
      S.e A (S.diag (algebraMap (𝓞 F) F (n * d) / c)) = 1) ∧
    (∀ n : 𝓞 F,
      (∀ d : 𝓞 F, S.e A (S.diag (algebraMap (𝓞 F) F (n * d) / c)) = 1) → n ∈ I) := by
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
