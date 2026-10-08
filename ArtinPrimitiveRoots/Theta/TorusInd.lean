import ArtinPrimitiveRoots.A1.ThetaInterface
import ArtinPrimitiveRoots.Theta.Cover

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]

/-! ## P-TORUS-IND -/

section Torus

variable {D : FieldData F} {H : HilbertData F} {v : FinPlace F}

/-- The fixed uniformizer of `K_v` (image of the global `unif v`). -/
def unifLoc (v : FinPlace F) : (v.adicCompletion F)ˣ := toLoc v (Units.mk0 (unif v) (unif_ne_zero v))

/-- Local units `O_v^×` as a predicate on `K_v^×`. -/
def IsLocUnit (v : FinPlace F) (u : (v.adicCompletion F)ˣ) : Prop :=
  (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F

/-- Commutator pairing of the covering torus: `[a(x), a(y)] = z(⟨x,y⟩)`. -/
def torusPairing (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (x y : (v.adicCompletion F)ˣ) : rootsOfUnity 3 ℂ :=
  muThree D (H.hilb v x y) * (muThree D (H.hilb v y x))⁻¹

/-- **tor:pairing**: the commutator formula. -/
theorem torus_commutator (L : FinLocalCover D H v) (x y : (v.adicCompletion F)ˣ) :
    L.a x * L.a y * (L.a x)⁻¹ * (L.a y)⁻¹ = L.z (torusPairing D H v x y) := by
  sorry

/-- **tor:pairing** (nondegeneracy on `K^×/K^{×3}`). -/
theorem torusPairing_nondeg (x : (v.adicCompletion F)ˣ)
    (hx : ∀ y, torusPairing D H v x y = 1) : ∃ t : (v.adicCompletion F)ˣ, x = t ^ 3 := by
  sorry

/-- **tor:center**: `t ↦ a(t³)` is a homomorphism into the centre of the covering torus. -/
theorem a_cube_mul (L : FinLocalCover D H v) (s t : (v.adicCompletion F)ˣ) :
    L.a (s ^ 3) * L.a (t ^ 3) = L.a ((s * t) ^ 3) ∧ ∀ y, L.a (s ^ 3) * L.a y = L.a y * L.a (s ^ 3) := by
  sorry

/-- **def:tor-rep**: a genuine smooth representation of the covering torus with unitary central
character `z(ζ)a(t³) ↦ ζ`, given as a projective representation of `K^×` with the torus cocycle. -/
structure TorusRep (D : FieldData F) (H : HilbertData F) (v : FinPlace F) where
  V : Type
  [nacg : NormedAddCommGroup V]
  [nsp : NormedSpace ℂ V]
  [fd : FiniteDimensional ℂ V]
  σa : (v.adicCompletion F)ˣ → V →ₗ[ℂ] V
  σa_one : σa 1 = LinearMap.id
  σa_mul : ∀ x y, (σa x).comp (σa y) = ((muThree D (H.hilb v x y) : ℂˣ) : ℂ) • σa (x * y)
  σa_cube : ∀ t, σa (t ^ 3) = LinearMap.id
  σa_smooth : ∃ m : ℕ, 0 < m ∧ ∀ u : (v.adicCompletion F)ˣ,
    ((u : v.adicCompletion F) - 1) ∈ ball v m → σa u = LinearMap.id
  /-- `σa` takes finitely many values (it factors through `K^×/(K^{×3}(1+𝔭^m))` up to `μ3`);
  this gives the uniform bounds used in P-LOCAL-INT -/
  σa_finite : (Set.range σa).Finite

attribute [instance] TorusRep.nacg TorusRep.nsp TorusRep.fd

/-- **def:weyl-rep**: the Weyl conjugate `y ↦ σa(y⁻¹)` (same cocycle, since `hilb(x⁻¹,y⁻¹) = hilb(x,y)`);
`I(T.weyl, -s)` is the target of the intertwining operator (P-LOCAL-INT). -/
def TorusRep.weyl (T : TorusRep D H v) : TorusRep D H v where
  V := T.V
  σa y := T.σa y⁻¹
  σa_one := by simpa using T.σa_one
  σa_mul := by sorry
  σa_cube := by intro t; simpa [← inv_pow] using T.σa_cube t⁻¹
  σa_smooth := by sorry
  σa_finite := by sorry

/-- **tor:tame-basis**: at a tame place, the explicit model `e_0, e_1, e_2` with
`σ(a(ϖ^j u)) e_k = ρ(u)^{j+2k} e_{k+j}`, `ρ = localChi²` (10:250–275, unitary normalization). -/
structure TameTorusBasis (T : TorusRep D H v) where
  e : ZMod 3 → T.V
  linIndep : LinearIndependent ℂ e
  spans : Submodule.span ℂ (Set.range e) = ⊤
  act : ∀ (j : ℤ) (u : (v.adicCompletion F)ˣ), IsLocUnit v u → ∀ k : ZMod 3,
    T.σa (unifLoc v ^ j * u) (e k) = (localChi D v u) ^ (2 * (j + 2 * (k.val : ℤ))) • e (k + (j : ZMod 3))

/-- **tor:rep** (top): at every finite place a torus representation exists, of dimension
`√[K^×:K^{×3}]`; at `v ∤ 6` one with the tame basis. The nontrivial-carrier clause is
installed per `sol-thin-thlocal`, since `GlobalDatum.lam_ne` excludes the zero space. -/
theorem exists_torusRep (D : FieldData F) (H : HilbertData F) (v : FinPlace F)
    (hSt : SteinbergAt H v) :
    ∃ T : TorusRep D H v, Nontrivial T.V ∧
      ((6 : 𝓞 F) ∉ v.asIdeal → Nonempty (TameTorusBasis T)) := by
  sorry

/-- **tor:K-fixed**: at a tame place, the `a(O^×)`-fixed vectors of `V` are the multiples of `e_0`. -/
theorem tame_unitFixed (T : TorusRep D H v) (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal)
    (x : T.V) (hx : ∀ u, IsLocUnit v u → T.σa u x = x) : ∃ c : ℂ, x = c • B.e 0 := by
  sorry

/-- **def:weyl-basis**: `e^w_k := e_{-k}` is a tame basis of the Weyl conjugate `T.weyl`
(uses `localChi(u⁻¹) = localChi(u)⁻¹` and `localChi(u)^6 = 1` on local units). -/
def TameTorusBasis.weyl {T : TorusRep D H v} (B : TameTorusBasis T) : TameTorusBasis T.weyl where
  e k := B.e (-k)
  linIndep := by sorry
  spans := by sorry
  act := by sorry

/-- **def:ind**: sections of the normalized induced representation `I(σ, s)`:
`f(n(x) z(ζ) a(y) g) = ζ |y|^{1/2+s} σ(a(y)) f(g)`, right-invariant under some `Kc m`. -/
def IsSection (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ) (f : L.L → T.V) : Prop :=
  (∀ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ) (g : L.L),
    f (L.n (Multiplicative.ofAdd x) * L.a y * g) = ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (f g)) ∧
  (∀ ζ g, f (L.z ζ * g) = ((ζ : ℂˣ) : ℂ) • f g) ∧
  (∃ m, L.m0 ≤ m ∧ ∀ g, ∀ k ∈ L.Kc m, f (g * k) = f g)

/-- Right translation `(π(g)f)(h) = f(hg)`. -/
def rtr {G V : Type} [Mul G] (g : G) (f : G → V) : G → V := fun h => f (h * g)

/-- **ind:rtr**: sections are stable under right translation (`g⁻¹ Kc(m') g ⊆ Kc(m)` for large `m'`). -/
theorem IsSection.rtr {L : FinLocalCover D H v} {T : TorusRep D H v} {s : ℂ} {f : L.L → T.V}
    (hf : IsSection L T s f) (g : L.L) : IsSection L T s (rtr g f) := by
  rcases hf with ⟨hN, hZ, ⟨m, hm, hfix⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y u
    change f ((L.n (Multiplicative.ofAdd x) * L.a y * u) * g) =
      ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (f (u * g))
    simpa [mul_assoc] using hN x y (u * g)
  · intro ζ u
    change f ((L.z ζ * u) * g) = ((ζ : ℂˣ) : ℂ) • f (u * g)
    simpa [mul_assoc] using hZ ζ (u * g)
  · have hconj : Continuous (fun k : L.L => g⁻¹ * k * g) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hopen : IsOpen {k : L.L | g⁻¹ * k * g ∈ L.Kc m} :=
      IsOpen.preimage hconj (L.Kc_open m hm)
    have hnhds : {k : L.L | g⁻¹ * k * g ∈ L.Kc m} ∈ nhds (1 : L.L) := by
      apply hopen.mem_nhds
      simp
    obtain ⟨m', hm', hsub⟩ := L.Kc_nhds _ hnhds
    refine ⟨m', hm', ?_⟩
    intro u k hk
    change f ((u * k) * g) = f (u * g)
    rw [show (u * k) * g = (u * g) * (g⁻¹ * k * g) by group]
    exact hfix (u * g) (g⁻¹ * k * g) (hsub hk)

private theorem iwasawa_right_denominator (g : GL (Fin 2) (v.adicCompletion F))
    (hd : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 ≠ 0)
    (hcd : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) ≤
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) :
    ∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
    ∃ k : GL (Fin 2) (v.adicCompletion F),
        k = lowerM (v.adicCompletion F)
          (((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) /
            ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1)) ∧
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        Matrix.ProjGenLinGroup.mk g =
          Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
            Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
              Matrix.ProjGenLinGroup.mk k := by
  classical
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) := g
  let a := M 0 0
  let b := M 0 1
  let c := M 1 0
  let d := M 1 1
  have hdet : M.det ≠ 0 := by simpa [M] using g.det_ne_zero
  have hratioVal : Valued.v (c / d) ≤ 1 := by
    rw [map_div₀]
    exact div_le_one_of_le₀ (by simpa [c, d, M] using hcd) (bot_le : 0 ≤ Valued.v d)
  have hratio : c / d ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hratioVal
  have hyval : M.det / d ^ 2 ≠ 0 := by
    exact div_ne_zero hdet (pow_ne_zero 2 (by simpa [d, M] using hd))
  let x : v.adicCompletion F := b / d
  let y : (v.adicCompletion F)ˣ := Units.mk0 (M.det / d ^ 2) hyval
  let k : GL (Fin 2) (v.adicCompletion F) := lowerM (v.adicCompletion F) (c / d)
  have heq : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd) *
      upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y * k := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, a, b, c, d, x, y, k, Matrix.GeneralLinearGroup.scalar,
        upperM, diagM, lowerM, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.det_fin_two] <;>
      field_simp [hd, hdet] <;> ring
  have hkentries : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [k, lowerM, hratio]
  have hinv : k⁻¹ = lowerM (v.adicCompletion F) (-(c / d)) := by
    have hmul : k * lowerM (v.adicCompletion F) (-(c / d)) = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [k, lowerM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    calc
      k⁻¹ = k⁻¹ * 1 := by simp
      _ = k⁻¹ * (k * lowerM (v.adicCompletion F) (-(c / d))) := by rw [hmul]
      _ = lowerM (v.adicCompletion F) (-(c / d)) := by group
  have hdetinv : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = 1 := by
    rw [hinv]
    simp [lowerM, Matrix.det_fin_two]
  refine ⟨x, y, k, rfl, hkentries, ?_, ?_⟩
  · rw [hdetinv]
    exact (v.adicCompletionIntegers F).one_mem
  · rw [heq]
    change Matrix.ProjGenLinGroup.mk
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 d hd) *
        upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y * k) = _
    simp only [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

private theorem iwasawa_matrix_decomposition (g : GL (Fin 2) (v.adicCompletion F)) :
    ∃ x : v.adicCompletion F, ∃ y : (v.adicCompletion F)ˣ,
      ∃ k : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        Matrix.ProjGenLinGroup.mk g =
          Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
            Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
              Matrix.ProjGenLinGroup.mk k := by
  classical
  let c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
  have hrow : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≠ 0 := by
      simpa using g.det_ne_zero
    apply hdet
    rw [Matrix.det_fin_two]
    simp [c, d, h.1, h.2]
  by_cases hd : d = 0
  · have hc : c ≠ 0 := by
      rcases hrow with hc | hd'; exact hc
      exact (hd' hd).elim
    have hleft : (g * weylM (v.adicCompletion F) :
        GL (Fin 2) (v.adicCompletion F)) 1 0 = d := by
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
    have hright : (g * weylM (v.adicCompletion F) :
        GL (Fin 2) (v.adicCompletion F)) 1 1 = c := by
      simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
    have hval : Valued.v d ≤ Valued.v c := by rw [hd]; simp
    obtain ⟨x, y, k₀, hk₀, hkentries, hdetinv, hq⟩ :=
      iwasawa_right_denominator (g * weylM (v.adicCompletion F)) (by simpa [hright] using hc)
        (by simpa [hleft, hright] using hval)
    subst k₀
    let k : GL (Fin 2) (v.adicCompletion F) :=
      lowerM (v.adicCompletion F) (d / c) * weylM (v.adicCompletion F)
    have hratio : d / c ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hval (by simp)
    have hkentries' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        v.adicCompletionIntegers F := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, hratio]
    have hdetk : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = -1 := by
      simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    have hmul : ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val) *
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
      exact congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
        (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (inv_mul_cancel k)
    have hdetmul : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det *
        (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
      simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmul
    have hdetinv' : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = -1 := by
      rw [hdetk] at hdetmul
      calc
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det =
            (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * (-1 * -1) := by ring
        _ = ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * -1) * -1 := by ring
        _ = 1 * -1 := by rw [hdetmul]
        _ = -1 := by ring
    have hminus : (-1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simp
    have hq' : Matrix.ProjGenLinGroup.mk g =
        Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
          Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
            Matrix.ProjGenLinGroup.mk k := by
      have hw : weylM (v.adicCompletion F) * weylM (v.adicCompletion F) = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
      have hg : g = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) := by
        calc
          g = g * 1 := by simp
          _ = g * (weylM (v.adicCompletion F) * weylM (v.adicCompletion F)) := by rw [hw]
          _ = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) :=
            (mul_assoc _ _ _).symm
      have hq'0 := hq
      rw [hleft, hright] at hq'0
      calc
        Matrix.ProjGenLinGroup.mk g =
            Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
              Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by
                calc
                  Matrix.ProjGenLinGroup.mk g =
                      Matrix.ProjGenLinGroup.mk
                        ((g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F)) :=
                    congrArg Matrix.ProjGenLinGroup.mk hg
                  _ = Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                        Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [map_mul]
        _ = (Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c))) *
              Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [hq'0]
        _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                (Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c)) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F))) := by ac_rfl
        _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk k := by rw [map_mul]
    refine ⟨x, y, k, hkentries', ?_, hq'⟩
    rw [hdetinv']
    exact hminus
  · by_cases hc : c = 0
    · have hval : Valued.v c ≤ Valued.v d := by rw [hc]; simp
      obtain ⟨x, y, k, hkform, hk, hdet, hq⟩ :=
        iwasawa_right_denominator g (by simpa [d] using hd) (by simpa [c, d] using hval)
      exact ⟨x, y, k, hk, hdet, hq⟩
    · by_cases hval : Valued.v c ≤ Valued.v d
      · obtain ⟨x, y, k, hkform, hk, hdet, hq⟩ :=
          iwasawa_right_denominator g (by simpa [d] using hd) (by simpa [c, d] using hval)
        exact ⟨x, y, k, hk, hdet, hq⟩
      · have hdc : Valued.v d ≤ Valued.v c := le_of_not_ge hval
        have hleft : (g * weylM (v.adicCompletion F) :
            GL (Fin 2) (v.adicCompletion F)) 1 0 = d := by
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
        have hright : (g * weylM (v.adicCompletion F) :
            GL (Fin 2) (v.adicCompletion F)) 1 1 = c := by
          simp [weylM, Matrix.mul_apply, Fin.sum_univ_two, c, d]
        obtain ⟨x, y, k₀, hk₀, hkentries, hdetinv, hq⟩ :=
          iwasawa_right_denominator (g * weylM (v.adicCompletion F)) (by simpa [hright] using hc)
            (by simpa [hleft, hright] using hdc)
        subst k₀
        let k : GL (Fin 2) (v.adicCompletion F) :=
          lowerM (v.adicCompletion F) (d / c) * weylM (v.adicCompletion F)
        have hratio : d / c ∈ v.adicCompletionIntegers F := by
          rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
          exact div_le_one_of_le₀ hdc (by simp)
        have hkentries' : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
            v.adicCompletionIntegers F := by
          intro i j
          fin_cases i <;> fin_cases j <;>
            simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, hratio]
        have hdetk : (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = -1 := by
          simp [k, lowerM, weylM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
        have hmul : ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val) *
            (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
          exact congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
            (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (inv_mul_cancel k)
        have hdetmul : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det *
            (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
          simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmul
        have hdetinv' : (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det = -1 := by
          rw [hdetk] at hdetmul
          calc
            (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det =
                (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * (-1 * -1) := by ring
            _ = ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det * -1) * -1 := by ring
            _ = 1 * -1 := by rw [hdetmul]
            _ = -1 := by ring
        have hminus : (-1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
          rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          simp
        have hq' : Matrix.ProjGenLinGroup.mk g =
            Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
              Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                Matrix.ProjGenLinGroup.mk k := by
          have hw : weylM (v.adicCompletion F) * weylM (v.adicCompletion F) = 1 := by
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            fin_cases i <;> fin_cases j <;>
              simp [weylM, Matrix.mul_apply, Fin.sum_univ_two]
          have hg : g = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) := by
            calc
              g = g * 1 := by simp
              _ = g * (weylM (v.adicCompletion F) * weylM (v.adicCompletion F)) := by rw [hw]
              _ = (g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F) :=
                (mul_assoc _ _ _).symm
          have hq'0 := hq
          rw [hleft, hright] at hq'0
          calc
            Matrix.ProjGenLinGroup.mk g =
                Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by
                    calc
                      Matrix.ProjGenLinGroup.mk g =
                          Matrix.ProjGenLinGroup.mk
                            ((g * weylM (v.adicCompletion F)) * weylM (v.adicCompletion F)) :=
                        congrArg Matrix.ProjGenLinGroup.mk hg
                      _ = Matrix.ProjGenLinGroup.mk (g * weylM (v.adicCompletion F)) *
                            Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [map_mul]
            _ = (Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c))) *
                  Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F)) := by rw [hq'0]
            _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    (Matrix.ProjGenLinGroup.mk (lowerM (v.adicCompletion F) (d / c)) *
                      Matrix.ProjGenLinGroup.mk (weylM (v.adicCompletion F))) := by ac_rfl
            _ = Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
                  Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
                    Matrix.ProjGenLinGroup.mk k := by rw [map_mul]
        refine ⟨x, y, k, hkentries', ?_, hq'⟩
        rw [hdetinv']
        exact hminus

/-- **ind:iwasawa** (tame): `L = B̃ · Kmax`. -/
theorem iwasawa_tame (L : FinLocalCover D H v) (τ : TameSplitting L) (g : L.L) :
    ∃ (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ) (ζ : rootsOfUnity 3 ℂ) (k : L.L),
      k ∈ τ.Kmax ∧ g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by
  classical
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective (L.pr g)
  obtain ⟨x, y, kMat, hkentries, hkdetinv, hmatrix⟩ := iwasawa_matrix_decomposition G
  have himage : L.pr '' (τ.Kmax : Set L.L) =
      {q | ∃ k : GL (Fin 2) (v.adicCompletion F),
        (∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
          v.adicCompletionIntegers F) ∧
        (k⁻¹ : GL (Fin 2) (v.adicCompletion F)).val.det ∈ v.adicCompletionIntegers F ∧
        QuotientGroup.mk k = q} := τ.image
  have hkmem : Matrix.ProjGenLinGroup.mk kMat ∈ L.pr '' (τ.Kmax : Set L.L) := by
    rw [himage]
    exact ⟨kMat, hkentries, hkdetinv, rfl⟩
  obtain ⟨k, hkK, hkpr⟩ := hkmem
  let b : L.L := L.n (Multiplicative.ofAdd x) * L.a y * k
  have hprB : L.pr b =
      Matrix.ProjGenLinGroup.mk (upperM (v.adicCompletion F) x) *
        Matrix.ProjGenLinGroup.mk (diagM (v.adicCompletion F) y) *
          Matrix.ProjGenLinGroup.mk kMat := by
    dsimp [b]
    simp only [map_mul, L.pr_n, L.pr_a, hkpr]
    rfl
  have hprdecomp : L.pr g = L.pr b := by
    exact hG.symm.trans (hmatrix.trans hprB.symm)
  let q : L.L := b⁻¹ * g
  have hqker : q ∈ L.pr.ker := by
    change L.pr (b⁻¹ * g) = 1
    calc
      L.pr (b⁻¹ * g) = (L.pr b)⁻¹ * L.pr g := by simp only [map_mul, map_inv]
      _ = 1 := by rw [← hprdecomp]; simp
  rw [L.pr_ker] at hqker
  obtain ⟨ζ, hζ⟩ := hqker
  have hg : g = b * L.z ζ := by
    calc
      g = b * q := by dsimp [q]; group
      _ = b * L.z ζ := by rw [← hζ]
  have horder : b * L.z ζ =
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by
    change (L.n (Multiplicative.ofAdd x) * L.a y * k) * L.z ζ =
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k
    calc
      (L.n (Multiplicative.ofAdd x) * L.a y * k) * L.z ζ =
          (L.n (Multiplicative.ofAdd x) * L.a y) * (k * L.z ζ) := by group
      _ = (L.n (Multiplicative.ofAdd x) * L.a y) * (L.z ζ * k) := by
            rw [← L.z_central ζ k]
      _ = L.n (Multiplicative.ofAdd x) * (L.a y * L.z ζ) * k := by group
      _ = L.n (Multiplicative.ofAdd x) * (L.z ζ * L.a y) * k := by
            rw [← L.z_central ζ (L.a y)]
      _ = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * k := by group
  exact ⟨x, y, ζ, k, hkK, hg.trans horder⟩

/-- **ind:spherical** (KP Lemma I.1.3 replaced): at a tame place there is a unique
`Kmax`-invariant section with `f°(1) = e_0`, and every `Kmax`-invariant section is a multiple. -/
theorem spherical_section (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) :
    ∃ f0 : L.L → T.V, IsSection L T s f0 ∧ f0 1 = B.e 0 ∧ (∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) ∧
      ∀ f : L.L → T.V, IsSection L T s f → (∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g) →
        ∃ c : ℂ, f = c • f0 := by
  sorry

/-- **def:ind-bigcell**: the big-cell section `f(n(x) z(ζ) a(y) w n(t)) = ζ|y|^{1/2+s} σ(a(y)) φ(t)`
for a locally constant compactly supported `φ : K → V`, zero off the big cell. -/
def bigCell (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (g : L.L) : T.V :=
  if h : ∃ (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
      (t : v.adicCompletion F),
      g = L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)
  then ((h.choose_spec.choose : rootsOfUnity 3 ℂ) : ℂˣ) •
        ((absFin v h.choose_spec.choose_spec.choose : ℂ) ^ ((1 : ℂ) / 2 + s)) •
        T.σa h.choose_spec.choose_spec.choose (φ h.choose_spec.choose_spec.choose_spec.choose)
  else 0

/-- **ind:bigcell-section**: `bigCell φ` is a section when `φ` is locally constant with compact
support (the decomposition in the big cell is unique). -/
theorem bigCell_isSection (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (hφ : IsLocallyConstant φ) (hc : HasCompactSupport φ) :
    IsSection L T s (bigCell L T s φ) := by
  sorry

/-- **ind:bigcell-apply**: the value of a big-cell section on the big cell (uniqueness of the
decomposition `n(x) z(ζ) a(y) w n(t)`), and its vanishing on the small cell `B̃`. -/
theorem bigCell_apply (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) (t : v.adicCompletion F) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w * L.n (Multiplicative.ofAdd t)) =
      ((ζ : ℂˣ) : ℂ) • ((absFin v y : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y (φ t) := by
  sorry

theorem bigCell_borel (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := by
  sorry

end Torus

/-! ## Complex places -/

/-- Sections of the spherical principal series of `PGL₂(ℂ)` with parameter `s` (normalized
absolute value `|y|_ℂ = |y|²`): `f(n(x) a(y) g) = |y|_ℂ^{1/2+s} f(g)`, smooth. -/
def IsSectionC (s : ℂ) (f : PGL2 ℂ → ℂ) : Prop :=
  ∀ (x : ℂ) (y : ℂˣ) (g : PGL2 ℂ),
    f (QuotientGroup.mk (upperM ℂ x) * QuotientGroup.mk (diagM ℂ y) * g) =
      ((Complex.normSq (y : ℂ) : ℂ) ^ ((1 : ℂ) / 2 + s)) * f g

/-- **ind:complex-spherical** (03:316–318): `f°(g) = (|det g| / (|g₂₁|²+|g₂₂|²))^{1+2s}` is the
spherical section (invariant under `PU(2)`, value 1 at 1). -/
def sphericalC (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  ((‖(g : Matrix (Fin 2) (Fin 2) ℂ).det‖ /
      (‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2) : ℝ) : ℂ) ^
    (1 + 2 * s)

theorem sphericalC_isSection (s : ℂ) :
    ∃ f : PGL2 ℂ → ℂ, IsSectionC s f ∧ ∀ g : GL (Fin 2) ℂ, f (QuotientGroup.mk g) = sphericalC s g := by
  sorry

end ArtinPrimitiveRoots.A1.Theta
