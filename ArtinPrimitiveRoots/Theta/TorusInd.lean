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

private def borelElem (L : FinLocalCover D H v) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) : L.L :=
  L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y

private def bigCellMatrix (x : v.adicCompletion F) (y : (v.adicCompletion F)ˣ)
    (t : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F) :=
  upperM (v.adicCompletion F) x * diagM (v.adicCompletion F) y *
    weylM (v.adicCompletion F) * upperM (v.adicCompletion F) t

private theorem bigCell_pr_eq (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t t' : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y' * L.w *
        L.n (Multiplicative.ofAdd t')) :
    (QuotientGroup.mk (bigCellMatrix (F := F) x y t) :
      PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk (bigCellMatrix (F := F) x' y' t') := by
  have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
    intro η
    have hker : L.z η ∈ L.pr.ker := by
      rw [L.pr_ker]
      exact ⟨η, rfl⟩
    exact MonoidHom.mem_ker.mp hker
  have hp := congrArg L.pr h
  change (QuotientGroup.mk (bigCellMatrix (F := F) x y t) :
      PGL2 (v.adicCompletion F)) =
    QuotientGroup.mk (bigCellMatrix (F := F) x' y' t')
  simpa [bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz, mul_assoc] using hp

private theorem bigCell_coords_unique (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t t' : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y' * L.w *
        L.n (Multiplicative.ofAdd t')) :
    x = x' ∧ y = y' ∧ t = t' ∧ ζ = ζ' := by
  have hclass := bigCell_pr_eq L x x' ζ ζ' y y' t t' h
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmat :
      ((bigCellMatrix (F := F) x y t) * Matrix.GeneralLinearGroup.scalar
        (Fin 2) c : GL (Fin 2) (v.adicCompletion F)) =
      bigCellMatrix (F := F) x' y' t' := hc
  have hmatval :
      (((bigCellMatrix (F := F) x y t) * Matrix.GeneralLinearGroup.scalar
        (Fin 2) c : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (bigCellMatrix (F := F) x' y' t' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
    congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
      (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hmat
  have hcval : (c : v.adicCompletion F) = 1 := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 0) hmatval
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hmat' : bigCellMatrix (F := F) x y t = bigCellMatrix (F := F) x' y' t' := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M i j) hmatval
    fin_cases i <;> fin_cases j <;>
      simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two,
        hcval] using he
  have hentries := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) =>
    (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hmat'
  have ht : t = t' := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 1) hentries
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hx : x = x' := by
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 0 0) hentries
    simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hy : y = y' := by
    apply Units.ext
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 0 1) hentries
    have he' : (y : v.adicCompletion F) + x * t =
        (y' : v.adicCompletion F) + x' * t' := by
      calc
        (y : v.adicCompletion F) + x * t = x * t + y := by ring
        _ = x' * t' + y' := by
          simpa [bigCellMatrix, upperM, diagM, weylM, Matrix.mul_apply, Fin.sum_univ_two] using he
        _ = (y' : v.adicCompletion F) + x' * t' := by ring
    rw [hx, ht] at he'
    exact add_right_cancel he'
  have hphase : ζ = ζ' := by
    have hcancel := h
    rw [hx, hy, ht] at hcancel
    have hprefix : L.n (Multiplicative.ofAdd x') *
        (L.z ζ * (L.a y' * L.w * L.n (Multiplicative.ofAdd t'))) =
        L.n (Multiplicative.ofAdd x') *
          (L.z ζ' * (L.a y' * L.w * L.n (Multiplicative.ofAdd t'))) := by
      simpa [mul_assoc] using hcancel
    have hmid : L.z ζ * (L.a y' * L.w * L.n (Multiplicative.ofAdd t')) =
        L.z ζ' * (L.a y' * L.w * L.n (Multiplicative.ofAdd t')) :=
      mul_left_cancel hprefix
    have hphase' : L.z ζ = L.z ζ' := mul_right_cancel hmid
    exact L.z_inj hphase'
  exact ⟨hx, hy, ht, hphase⟩

private theorem bigcell_ne_borel (L : FinLocalCover D H v)
    (x x' : v.adicCompletion F) (ζ ζ' : rootsOfUnity 3 ℂ)
    (y y' : (v.adicCompletion F)ˣ) (t : v.adicCompletion F)
    (h : L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y * L.w *
        L.n (Multiplicative.ofAdd t) =
      L.n (Multiplicative.ofAdd x') * L.z ζ' * L.a y') : False := by
  have hz : ∀ η : rootsOfUnity 3 ℂ, L.pr (L.z η) = 1 := by
    intro η
    have hker : L.z η ∈ L.pr.ker := by
      rw [L.pr_ker]
      exact ⟨η, rfl⟩
    exact MonoidHom.mem_ker.mp hker
  have hp := congrArg L.pr h
  let A := bigCellMatrix (F := F) x y t
  let B := upperM (v.adicCompletion F) x' * diagM (v.adicCompletion F) y'
  have hclass : (QuotientGroup.mk A : PGL2 (v.adicCompletion F)) =
      QuotientGroup.mk B := by
    simpa [A, B, bigCellMatrix, map_mul, L.pr_n, L.pr_a, L.pr_w, hz,
      mul_assoc] using hp
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmatval :
      (((A * Matrix.GeneralLinearGroup.scalar (Fin 2) c :
        GL (Fin 2) (v.adicCompletion F)) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
    congrArg (fun q : GL (Fin 2) (v.adicCompletion F) =>
      (q : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) hc
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => M 1 0) hmatval
  have hc0 : (c : v.adicCompletion F) = 0 := by
    simpa [A, B, bigCellMatrix, upperM, diagM, weylM,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  exact c.ne_zero hc0

private theorem absFin_eq_norm_ind (v : FinPlace F) (x : v.adicCompletion F) :
    absFin v x = ‖x‖ := by
  unfold absFin
  rw [dif_pos (HeightOneSpectrum.absNorm_ne_zero v)]
  exact (FinitePlace.norm_def v x).symm

private theorem absFin_mul_ind (v : FinPlace F) (x y : (v.adicCompletion F)ˣ) :
    absFin v (x * y) = absFin v x * absFin v y := by
  simp only [absFin_eq_norm_ind, norm_mul]

private theorem absFin_one_of_locUnit (u : (v.adicCompletion F)ˣ)
    (hu : IsLocUnit v u) : absFin v (u : v.adicCompletion F) = 1 := by
  rw [absFin_eq_norm_ind]
  have hu₁ : ‖(u : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    have h := hu.1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hu₂ : ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff]
    have h := hu.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    exact h
  have hprod : ‖(u : v.adicCompletion F)‖ *
      ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    calc
      _ = ‖(u : v.adicCompletion F) *
          ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ := (norm_mul _ _).symm
      _ = 1 := by simp
  have huge : 1 ≤ ‖(u : v.adicCompletion F)‖ := by
    calc
      1 = ‖(u : v.adicCompletion F)‖ *
          ‖((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ := hprod.symm
      _ ≤ ‖(u : v.adicCompletion F)‖ * 1 :=
          mul_le_mul_of_nonneg_left hu₂ (norm_nonneg _)
      _ = ‖(u : v.adicCompletion F)‖ := by simp
  exact le_antisymm hu₁ huge

private theorem borel_inter_Kmax (L : FinLocalCover D H v) (τ : TameSplitting L)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (hb : borelElem L x ζ y ∈ τ.Kmax) :
    x ∈ v.adicCompletionIntegers F ∧ IsLocUnit v y ∧ ζ = 1 := by
  classical
  let K := v.adicCompletion F
  let B : GL (Fin 2) K := upperM K x * diagM K y
  have hzker : L.z ζ ∈ L.pr.ker := by
    rw [L.pr_ker]
    exact ⟨ζ, rfl⟩
  have hprz : L.pr (L.z ζ) = 1 := by
    exact MonoidHom.mem_ker.mp hzker
  have hprB : L.pr (borelElem L x ζ y) = QuotientGroup.mk B := by
    simp [borelElem, B, K, map_mul, L.pr_n, L.pr_a, hprz, mul_assoc]
  have himage : L.pr (borelElem L x ζ y) ∈ L.pr '' (τ.Kmax : Set L.L) :=
    ⟨borelElem L x ζ y, hb, rfl⟩
  rw [τ.image] at himage
  obtain ⟨M, hMentries, hMinvdet, hMclass⟩ := himage
  have hclass : Matrix.ProjGenLinGroup.mk M = Matrix.ProjGenLinGroup.mk B := by
    change QuotientGroup.mk M = QuotientGroup.mk B
    rw [hMclass, hprB]
  obtain ⟨c, hmat⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hclass
  have hmatval : (M * Matrix.GeneralLinearGroup.scalar (Fin 2) c :
      GL (Fin 2) K).val = B.val := congrArg (fun q : GL (Fin 2) K => (q : Matrix (Fin 2) (Fin 2) K)) hmat
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 0) hmatval
    have he' : (M : Matrix (Fin 2) (Fin 2) K) 1 0 * (c : K) = 0 := by
      simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
        Matrix.mul_apply, Fin.sum_univ_two] using he
    exact (mul_eq_zero.mp he').resolve_right c.ne_zero
  have hMdetO : (M : Matrix (Fin 2) (Fin 2) K).det ∈ v.adicCompletionIntegers F := by
    rw [Matrix.det_fin_two]
    exact (v.adicCompletionIntegers F).sub_mem
      ((v.adicCompletionIntegers F).mul_mem _ _ (hMentries 0 0) (hMentries 1 1))
      ((v.adicCompletionIntegers F).mul_mem _ _ (hMentries 0 1) (hMentries 1 0))
  have hmulM : (M : Matrix (Fin 2) (Fin 2) K) *
      ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    exact congrArg (fun q : GL (Fin 2) K => (q : Matrix (Fin 2) (Fin 2) K)) (mul_inv_cancel M)
  have hdetmul : (M : Matrix (Fin 2) (Fin 2) K).det *
      ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hmulM
  have hdetValProd : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) *
      Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    calc
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det *
          ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) := by rw [map_mul]
      _ = 1 := by rw [hdetmul]; simp
  have hdetLE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 := by
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 at hMdetO
    exact hMdetO
  have hMinvLE : Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 := by
    change Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) ≤ 1 at hMinvdet
    exact hMinvdet
  have hdetVal : Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) = 1 := by
    apply le_antisymm hdetLE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) *
          Valued.v (((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det) := hdetValProd.symm
      _ ≤ Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) * 1 :=
          mul_le_mul_of_nonneg_left hMinvLE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K).det) := by simp
  have hM00LE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) ≤ 1 := by
    have h := hMentries 0 0
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) ≤ 1 at h
    exact h
  have hM11LE : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) ≤ 1 := by
    have h := hMentries 1 1
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) ≤ 1 at h
    exact h
  have hdetfactor : (M : Matrix (Fin 2) (Fin 2) K).det =
      (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [Matrix.det_fin_two, hM10]
    ring
  have hdetValfactor : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
      Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 := by
    rw [← map_mul, ← hdetfactor, hdetVal]
  have hM00Val : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) = 1 := by
    apply le_antisymm hM00LE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
          Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := hdetValfactor.symm
      _ ≤ Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) * 1 :=
          mul_le_mul_of_nonneg_left hM11LE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) := by simp
  have hM11Val : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 1 := by
    apply le_antisymm hM11LE
    calc
      1 = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 0) *
          Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := hdetValfactor.symm
      _ ≤ 1 * Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) :=
          mul_le_mul_of_nonneg_right hM00LE (by simp)
      _ = Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) := by simp
  have hM00c : (M : Matrix (Fin 2) (Fin 2) K) 0 0 * (c : K) = (y : K) := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM01c : (M : Matrix (Fin 2) (Fin 2) K) 0 1 * (c : K) = x := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM11c : (M : Matrix (Fin 2) (Fin 2) K) 1 1 * (c : K) = 1 := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 1 1) hmatval
    simpa [B, upperM, diagM, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using he
  have hM11ne : (M : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro hzero
    have hzeroVal : Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 1 1) = 0 := by simp [hzero]
    rw [hM11Val] at hzeroVal
    norm_num at hzeroVal
  have hcval : (c : K) = ((M : Matrix (Fin 2) (Fin 2) K) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hM11c
  have hxformula : x = (M : Matrix (Fin 2) (Fin 2) K) 0 1 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [hcval] at hM01c
    simpa [div_eq_mul_inv] using hM01c.symm
  have hyformula : (y : K) = (M : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (M : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    rw [hcval] at hM00c
    simpa [div_eq_mul_inv] using hM00c.symm
  have hxVal : Valued.v x ≤ 1 := by
    rw [hxformula, map_div₀, hM11Val, div_one]
    have hM01LE := hMentries 0 1
    change Valued.v ((M : Matrix (Fin 2) (Fin 2) K) 0 1) ≤ 1 at hM01LE
    exact hM01LE
  have hyVal : Valued.v (y : K) = 1 := by
    rw [hyformula, map_div₀, hM00Val, hM11Val]
    simp
  have hxO : x ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hxVal
  have hyLoc : IsLocUnit v y := by
    constructor
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, hyVal]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      simpa [map_inv₀, hyVal]
  have hNA : L.n (Multiplicative.ofAdd x) * L.a y ∈ τ.Kmax := by
    exact τ.Kmax.mul_mem (τ.n_mem x hxO) (τ.a_mem y hyLoc.1 hyLoc.2)
  have hprNA : L.pr (L.n (Multiplicative.ofAdd x) * L.a y) =
      QuotientGroup.mk B := by
    simp [B, K, map_mul, L.pr_n, L.pr_a]
  have hprB' : L.pr (borelElem L x ζ y) = L.pr (L.n (Multiplicative.ofAdd x) * L.a y) := by
    rw [hprB, hprNA]
  have heqNA : borelElem L x ζ y = L.n (Multiplicative.ofAdd x) * L.a y :=
    τ.inj hb hNA hprB'
  have hcomm : borelElem L x ζ y = L.z ζ *
      (L.n (Multiplicative.ofAdd x) * L.a y) := by
    dsimp [borelElem]
    calc
      L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y =
          L.z ζ * L.n (Multiplicative.ofAdd x) * L.a y := by
            rw [← L.z_central ζ (L.n (Multiplicative.ofAdd x))]
      _ = L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) := by rw [mul_assoc]
  have hzNA : L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
      L.n (Multiplicative.ofAdd x) * L.a y := hcomm.symm.trans heqNA
  have hz : L.z ζ = 1 := by
    have hcancel : L.z ζ * (L.n (Multiplicative.ofAdd x) * L.a y) =
        1 * (L.n (Multiplicative.ofAdd x) * L.a y) := by simpa using hzNA
    exact (mul_right_cancel hcancel)
  exact ⟨hxO, hyLoc, L.z_inj (by simpa using hz)⟩

private theorem borelElem_mul (L : FinLocalCover D H v)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    borelElem L x₁ ζ₁ y₁ * borelElem L x₂ ζ₂ y₂ =
      borelElem L (x₁ + x₂ * (y₁ : v.adicCompletion F))
        (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) := by
  have hmove : L.a y₁ * L.n (Multiplicative.ofAdd x₂) =
      L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.a y₁ := by
    have h := L.lift_na (x₂ * (y₁ : v.adicCompletion F)) y₁
    simpa using h.symm
  have hn : L.n (Multiplicative.ofAdd x₁) *
      L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) =
      L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) := by
    simpa using (map_mul L.n (Multiplicative.ofAdd x₁)
      (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))))
  calc
    borelElem L x₁ ζ₁ y₁ * borelElem L x₂ ζ₂ y₂ =
        (L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ * L.a y₁) *
          (L.n (Multiplicative.ofAdd x₂) * L.z ζ₂ * L.a y₂) := rfl
    _ = L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ *
          (L.a y₁ * L.n (Multiplicative.ofAdd x₂)) * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) * L.z ζ₁ *
          (L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.a y₁) *
          L.z ζ₂ * L.a y₂ := by rw [hmove]
    _ = L.n (Multiplicative.ofAdd x₁) *
          (L.z ζ₁ * L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F)))) *
          L.a y₁ * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          (L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) * L.z ζ₁) *
          L.a y₁ * L.z ζ₂ * L.a y₂ := by rw [L.z_central ζ₁]
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * L.a y₁ * L.z ζ₂ * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * (L.a y₁ * L.z ζ₂) * L.a y₂ := by group
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          L.z ζ₁ * (L.z ζ₂ * L.a y₁) * L.a y₂ := by rw [← L.z_central ζ₂ (L.a y₁)]
    _ = L.n (Multiplicative.ofAdd x₁) *
          L.n (Multiplicative.ofAdd (x₂ * (y₁ : v.adicCompletion F))) *
          (L.z ζ₁ * L.z ζ₂) * (L.a y₁ * L.a y₂) := by group
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          (L.z ζ₁ * L.z ζ₂) *
            (L.z (muThree D (H.hilb v y₁ y₂)) * L.a (y₁ * y₂)) := by
              rw [hn, L.a_mul]
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          ((L.z ζ₁ * L.z ζ₂) * L.z (muThree D (H.hilb v y₁ y₂))) *
            L.a (y₁ * y₂) := by group
    _ = L.n (Multiplicative.ofAdd (x₁ + x₂ * (y₁ : v.adicCompletion F))) *
          L.z (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) * L.a (y₁ * y₂) := by
              rw [← map_mul, ← map_mul]
    _ = borelElem L (x₁ + x₂ * (y₁ : v.adicCompletion F))
          (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) := rfl

private def sphericalBorelAction (T : TorusRep D H v) (s : ℂ)
    (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) :
    T.V →ₗ[ℂ] T.V :=
  ((ζ : ℂˣ) : ℂ) •
    (((absFin v (y : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa y)

private theorem sphericalBorelAction_mul (T : TorusRep D H v) (s : ℂ)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    sphericalBorelAction T s (x₁ + x₂ * (y₁ : v.adicCompletion F))
        (ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂)) (y₁ * y₂) =
      (sphericalBorelAction T s x₁ ζ₁ y₁).comp
        (sphericalBorelAction T s x₂ ζ₂ y₂) := by
  have hpow :
      (absFin v ((y₁ * y₂ : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℂ) ^
          ((1 : ℂ) / 2 + s) =
        (absFin v (y₁ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s) *
          (absFin v (y₂ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s) := by
    rw [Units.val_mul, absFin_mul_ind, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg
      (by rw [absFin_eq_norm_ind]; exact norm_nonneg _)
      (by rw [absFin_eq_norm_ind]; exact norm_nonneg _) _
  ext z
  have hσ : T.σa y₁ (T.σa y₂ z) =
      ((muThree D (H.hilb v y₁ y₂) : ℂˣ) : ℂ) • T.σa (y₁ * y₂) z := by
    have h := congrArg (fun f : T.V →ₗ[ℂ] T.V => f z) (T.σa_mul y₁ y₂)
    simpa [LinearMap.comp_apply, LinearMap.smul_apply] using h
  simp only [sphericalBorelAction, LinearMap.comp_apply, LinearMap.smul_apply,
    map_smul, smul_smul]
  rw [hσ, hpow]
  rw [smul_smul]
  congr 1
  have hroot :
      (((ζ₁ * ζ₂ * muThree D (H.hilb v y₁ y₂) : rootsOfUnity 3 ℂ) : ℂˣ) : ℂ) =
        ((ζ₁ : ℂˣ) : ℂ) * ((ζ₂ : ℂˣ) : ℂ) *
          ((muThree D (H.hilb v y₁ y₂) : ℂˣ) : ℂ) := by simp
  rw [hroot]
  ring

private theorem sphericalBorelAction_unit (T : TorusRep D H v) (B : TameTorusBasis T)
    (s : ℂ) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ)
    (hζ : ζ = 1) (hy : IsLocUnit v y) :
    sphericalBorelAction T s x ζ y (B.e 0) = B.e 0 := by
  have hyσ : T.σa y (B.e 0) = B.e 0 := by
    simpa using B.act 0 y hy 0
  simp [sphericalBorelAction, hζ, absFin_one_of_locUnit y hy, hyσ]

private theorem hilb_one_left_ind (b : (v.adicCompletion F)ˣ) : H.hilb v 1 b = 1 := by
  exact H.sixth_power v 1 b ⟨1, by simp⟩

private theorem muThree_mul_ind (ζ ξ : rootsOfUnity 6 F) :
    muThree D (ζ * ξ) = muThree D ζ * muThree D ξ := by
  apply rootsOfUnity.coe_injective
  simp [muThree, map_mul, mul_pow]

private theorem muThree_one_ind : muThree D (1 : rootsOfUnity 6 F) = 1 := by
  apply rootsOfUnity.coe_injective
  simp [muThree]

private theorem muThree_hilb_mul_left_ind (a a' b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v (a * a') b) =
      muThree D (H.hilb v a b) * muThree D (H.hilb v a' b) := by
  rw [H.mul_left, muThree_mul_ind]

private theorem muThree_hilb_mul_right_ind (a b b' : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a (b * b')) =
      muThree D (H.hilb v a b) * muThree D (H.hilb v a b') := by
  rw [H.mul_right, muThree_mul_ind]

private theorem muThree_hilb_inv_left_ind (a b : (v.adicCompletion F)ˣ) :
    muThree D (H.hilb v a⁻¹ b) = (muThree D (H.hilb v a b))⁻¹ := by
  have h := H.mul_left v a a⁻¹ b
  rw [mul_inv_cancel, hilb_one_left_ind] at h
  have hhilb : H.hilb v a b * H.hilb v a⁻¹ b = 1 := h.symm
  have hC : muThree D (H.hilb v a b) * muThree D (H.hilb v a⁻¹ b) = 1 := by
    calc
      _ = muThree D (H.hilb v a b * H.hilb v a⁻¹ b) := (muThree_mul_ind _ _).symm
      _ = muThree D 1 := by rw [hhilb]
      _ = 1 := muThree_one_ind
  exact eq_inv_of_mul_eq_one_right hC

private theorem centralCocycle_coboundary_ind (a b : (v.adicCompletion F)ˣ) :
    (muThree D (H.hilb v a a⁻¹))⁻¹ * muThree D (H.hilb v a⁻¹ b) *
      muThree D (H.hilb v a (a⁻¹ * b)) = 1 := by
  rw [muThree_hilb_inv_left_ind, muThree_hilb_mul_right_ind]
  calc
    (muThree D (H.hilb v a a⁻¹))⁻¹ * (muThree D (H.hilb v a b))⁻¹ *
        (muThree D (H.hilb v a a⁻¹) * muThree D (H.hilb v a b)) =
      (muThree D (H.hilb v a a⁻¹))⁻¹ * muThree D (H.hilb v a a⁻¹) *
        ((muThree D (H.hilb v a b))⁻¹ * muThree D (H.hilb v a b)) := by ac_rfl
    _ = 1 := by simp

private theorem borelElem_inv (L : FinLocalCover D H v) (x : v.adicCompletion F)
    (ζ : rootsOfUnity 3 ℂ) (y : (v.adicCompletion F)ˣ) :
    (borelElem L x ζ y)⁻¹ =
      borelElem L (-x * (y⁻¹ : v.adicCompletion F))
        (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y⁻¹ := by
  have hx : x + (-x * (y⁻¹ : v.adicCompletion F)) * (y : v.adicCompletion F) = 0 := by
    simp [mul_assoc]
  have hζ : ζ * (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) *
      muThree D (H.hilb v y y⁻¹) = 1 := by group
  have hmul := borelElem_mul L x (-x * (y⁻¹ : v.adicCompletion F)) ζ
    (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y y⁻¹
  have hmul' : borelElem L x ζ y *
      borelElem L (-x * (y⁻¹ : v.adicCompletion F))
        (ζ⁻¹ * (muThree D (H.hilb v y y⁻¹))⁻¹) y⁻¹ = 1 := by
    rw [hmul]
    simp [borelElem, hx, hζ, mul_assoc, L.a_one]
  exact (eq_inv_of_mul_eq_one_right hmul').symm

private theorem borelElem_inv_mul (L : FinLocalCover D H v)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) :
    (borelElem L x₂ ζ₂ y₂)⁻¹ * borelElem L x₁ ζ₁ y₁ =
      borelElem L ((x₁ - x₂) * (y₂⁻¹ : v.adicCompletion F))
        ((ζ₂⁻¹ * (muThree D (H.hilb v y₂ y₂⁻¹))⁻¹) * ζ₁ *
          muThree D (H.hilb v y₂⁻¹ y₁)) (y₂⁻¹ * y₁) := by
  rw [borelElem_inv, borelElem_mul]
  congr 1
  simp only [Units.val_inv_eq_inv_val]
  ring

private theorem spherical_value_independent (L : FinLocalCover D H v) (τ : TameSplitting L)
    (T : TorusRep D H v) (B : TameTorusBasis T) (s : ℂ) (g : L.L)
    (x₁ x₂ : v.adicCompletion F) (ζ₁ ζ₂ : rootsOfUnity 3 ℂ)
    (y₁ y₂ : (v.adicCompletion F)ˣ) (k₁ k₂ : L.L)
    (hk₁ : k₁ ∈ τ.Kmax) (hg₁ : g = borelElem L x₁ ζ₁ y₁ * k₁)
    (hk₂ : k₂ ∈ τ.Kmax) (hg₂ : g = borelElem L x₂ ζ₂ y₂ * k₂) :
    sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
      sphericalBorelAction T s x₂ ζ₂ y₂ (B.e 0) := by
  let xt : v.adicCompletion F := (x₁ - x₂) * (y₂⁻¹ : v.adicCompletion F)
  let u : (v.adicCompletion F)ˣ := y₂⁻¹ * y₁
  let C₀ := muThree D (H.hilb v y₂ y₂⁻¹)
  let C₁ := muThree D (H.hilb v y₂⁻¹ y₁)
  let C₂ := muThree D (H.hilb v y₂ u)
  let b₁ := borelElem L x₁ ζ₁ y₁
  let b₂ := borelElem L x₂ ζ₂ y₂
  have hrel : b₂⁻¹ * b₁ = k₂ * k₁⁻¹ := by
    calc
      b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * k₁) * k₁⁻¹ := by group
      _ = b₂⁻¹ * g * k₁⁻¹ := by rw [hg₁]
      _ = b₂⁻¹ * (b₂ * k₂) * k₁⁻¹ := by rw [hg₂]
      _ = k₂ * k₁⁻¹ := by group
  have hKrel : b₂⁻¹ * b₁ ∈ τ.Kmax := by
    rw [hrel]
    exact mul_mem hk₂ (inv_mem hk₁)
  have hrelCoords : b₂⁻¹ * b₁ = borelElem L xt
      (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u := by
    simpa [b₁, b₂, xt, u, C₀, C₁, mul_assoc] using
      (borelElem_inv_mul L x₁ x₂ ζ₁ ζ₂ y₁ y₂)
  have hKelem : borelElem L xt (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u ∈ τ.Kmax := by
    rw [← hrelCoords]
    exact hKrel
  obtain ⟨hxt, hu, hξ⟩ :=
    borel_inter_Kmax L τ xt (ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁) u hKelem
  let ξ : rootsOfUnity 3 ℂ := ζ₂⁻¹ * C₀⁻¹ * ζ₁ * C₁
  have hX : x₂ + xt * (y₂ : v.adicCompletion F) = x₁ := by
    simp [xt, mul_assoc, sub_eq_add_neg]
  have hY : y₂ * u = y₁ := by
    dsimp [u]
    group
  have hcen : C₀⁻¹ * C₁ * C₂ = 1 := by
    simpa [C₀, C₁, C₂, u] using centralCocycle_coboundary_ind y₂ y₁
  have hZ : ζ₂ * ξ * C₂ = ζ₁ := by
    calc
      ζ₂ * ξ * C₂ = (ζ₂ * ζ₂⁻¹) * (C₀⁻¹ * ζ₁ * C₁ * C₂) := by
        dsimp [ξ]
        group
      _ = C₀⁻¹ * ζ₁ * C₁ * C₂ := by simp
      _ = ζ₁ * (C₀⁻¹ * C₁ * C₂) := by
        rw [mul_comm C₀⁻¹ ζ₁]
        group
      _ = ζ₁ := by rw [hcen]; simp
  have hcombined : b₁ = borelElem L (x₂ + xt * (y₂ : v.adicCompletion F))
      (ζ₂ * ξ * C₂) (y₂ * u) := by
    calc
      b₁ = b₂ * (b₂⁻¹ * b₁) := by dsimp [b₁, b₂]; group
      _ = b₂ * borelElem L xt ξ u := by rw [hrelCoords]
      _ = borelElem L (x₂ + xt * (y₂ : v.adicCompletion F)) (ζ₂ * ξ * C₂)
            (y₂ * u) := borelElem_mul L x₂ xt ζ₂ ξ y₂ u
  have hcoords : b₁ = borelElem L x₁ ζ₁ y₁ := by
    simpa only [hX, hZ, hY] using hcombined
  have hactCoords : sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
      sphericalBorelAction T s (x₂ + xt * (y₂ : v.adicCompletion F))
        (ζ₂ * ξ * C₂) (y₂ * u) (B.e 0) := by
    rw [← hX, ← hZ, ← hY]
  have hmul := sphericalBorelAction_mul T s x₂ xt ζ₂ ξ y₂ u
  have hmul0 := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0)) hmul
  calc
    sphericalBorelAction T s x₁ ζ₁ y₁ (B.e 0) =
        sphericalBorelAction T s (x₂ + xt * (y₂ : v.adicCompletion F))
          (ζ₂ * ξ * C₂) (y₂ * u) (B.e 0) := hactCoords
    _ = ((sphericalBorelAction T s x₂ ζ₂ y₂).comp
          (sphericalBorelAction T s xt ξ u)) (B.e 0) := hmul0
    _ = sphericalBorelAction T s x₂ ζ₂ y₂
          (sphericalBorelAction T s xt ξ u (B.e 0)) := rfl
    _ = sphericalBorelAction T s x₂ ζ₂ y₂ (B.e 0) := by
          rw [sphericalBorelAction_unit T B s xt ξ u hξ hu]

/-- **ind:spherical** (KP Lemma I.1.3 replaced): at a tame place there is a unique
`Kmax`-invariant section with `f°(1) = e_0`, and every `Kmax`-invariant section is a multiple. -/
theorem spherical_section (L : FinLocalCover D H v) (τ : TameSplitting L) (T : TorusRep D H v)
    (B : TameTorusBasis T) (hv : (6 : 𝓞 F) ∉ v.asIdeal) (s : ℂ) :
    ∃ f0 : L.L → T.V, IsSection L T s f0 ∧ f0 1 = B.e 0 ∧ (∀ g, ∀ k ∈ τ.Kmax, f0 (g * k) = f0 g) ∧
      ∀ f : L.L → T.V, IsSection L T s f → (∀ g, ∀ k ∈ τ.Kmax, f (g * k) = f g) →
        ∃ c : ℂ, f = c • f0 := by
  classical
  choose x y ζ k hk heq using (fun g : L.L => iwasawa_tame L τ g)
  let f0 : L.L → T.V := fun g => sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0)
  have hf0_decomp (g : L.L) (x' : v.adicCompletion F) (ζ' : rootsOfUnity 3 ℂ)
      (y' : (v.adicCompletion F)ˣ) (k' : L.L) (hk' : k' ∈ τ.Kmax)
      (heq' : g = borelElem L x' ζ' y' * k') :
      f0 g = sphericalBorelAction T s x' ζ' y' (B.e 0) := by
    change sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0) = _
    exact spherical_value_independent L τ T B s g (x g) x' (ζ g) ζ' (y g) y' (k g) k'
      (hk g) (heq g) hk' heq'
  have hNcov : ∀ (x₀ : v.adicCompletion F) (y₀ : (v.adicCompletion F)ˣ) (g : L.L),
      f0 (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g) =
        ((absFin v (y₀ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa y₀ (f0 g) := by
    intro x₀ y₀ g
    have hprod : L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
        borelElem L (x g) (ζ g) (y g) =
        borelElem L (x₀ + x g * (y₀ : v.adicCompletion F))
          (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) := by
      simpa [borelElem, L.a_one, mul_assoc] using
        (borelElem_mul L x₀ (x g) 1 (ζ g) y₀ (y g))
    have hdecomp : L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g =
        borelElem L (x₀ + x g * (y₀ : v.adicCompletion F))
          (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) * k g := by
      calc
        L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g =
            L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
              (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) :=
                congrArg (fun q : L.L => L.n (Multiplicative.ofAdd x₀) * L.a y₀ * q) (heq g)
        _ = (L.n (Multiplicative.ofAdd x₀) * L.a y₀ *
              borelElem L (x g) (ζ g) (y g)) * k g := by
                dsimp [borelElem]
                group
        _ = _ := by rw [hprod]
    have hval := hf0_decomp (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g)
      (x₀ + x g * (y₀ : v.adicCompletion F))
      (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (k g) (hk g) hdecomp
    have hact := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0))
      (sphericalBorelAction_mul T s x₀ (x g) 1 (ζ g) y₀ (y g))
    have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
      rw [hilb_one_left_ind]
      exact muThree_one_ind
    have hact' : sphericalBorelAction T s (x₀ + x g * (y₀ : v.adicCompletion F))
        (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (B.e 0) =
      (sphericalBorelAction T s x₀ 1 y₀).comp
        (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := by
      simpa [hmu, mul_assoc] using hact
    calc
      f0 (L.n (Multiplicative.ofAdd x₀) * L.a y₀ * g) =
          sphericalBorelAction T s (x₀ + x g * (y₀ : v.adicCompletion F))
            (ζ g * muThree D (H.hilb v y₀ (y g))) (y₀ * y g) (B.e 0) := hval
      _ = (sphericalBorelAction T s x₀ 1 y₀).comp
            (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := hact'
      _ = ((absFin v (y₀ : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
            T.σa y₀ (f0 g) := by
              simp [sphericalBorelAction, f0, LinearMap.comp_apply,
                LinearMap.smul_apply, map_smul, smul_smul]
              congr 1
              ring
  have hZcov : ∀ (ζ₀ : rootsOfUnity 3 ℂ) (g : L.L),
      f0 (L.z ζ₀ * g) = ((ζ₀ : ℂˣ) : ℂ) • f0 g := by
    intro ζ₀ g
    have hprod : L.z ζ₀ * borelElem L (x g) (ζ g) (y g) =
        borelElem L (x g) (ζ₀ * ζ g) (y g) := by
      have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
        rw [hilb_one_left_ind]
        exact muThree_one_ind
      simpa [borelElem, L.a_one, hmu, mul_assoc] using
        (borelElem_mul L 0 (x g) ζ₀ (ζ g) 1 (y g))
    have hdecomp : L.z ζ₀ * g = borelElem L (x g) (ζ₀ * ζ g) (y g) * k g := by
      calc
        L.z ζ₀ * g = L.z ζ₀ *
            (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) :=
              congrArg (fun q : L.L => L.z ζ₀ * q) (heq g)
        _ = (L.z ζ₀ * borelElem L (x g) (ζ g) (y g)) * k g := by
              dsimp [borelElem]
              group
        _ = _ := by rw [hprod]
    have hval := hf0_decomp (L.z ζ₀ * g) (x g) (ζ₀ * ζ g) (y g) (k g) (hk g) hdecomp
    have hact := congrArg (fun f : T.V →ₗ[ℂ] T.V => f (B.e 0))
      (sphericalBorelAction_mul T s 0 (x g) ζ₀ (ζ g) 1 (y g))
    have hmu : muThree D (H.hilb v 1 (y g)) = 1 := by
      rw [hilb_one_left_ind]
      exact muThree_one_ind
    have hact' : sphericalBorelAction T s (x g) (ζ₀ * ζ g) (y g) (B.e 0) =
      (sphericalBorelAction T s 0 ζ₀ 1).comp
        (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := by
      simpa [hmu, mul_assoc] using hact
    calc
      f0 (L.z ζ₀ * g) = sphericalBorelAction T s (x g) (ζ₀ * ζ g) (y g) (B.e 0) := hval
      _ = (sphericalBorelAction T s 0 ζ₀ 1).comp
            (sphericalBorelAction T s (x g) (ζ g) (y g)) (B.e 0) := hact'
      _ = ((ζ₀ : ℂˣ) : ℂ) • f0 g := by
              simp [sphericalBorelAction, f0, LinearMap.comp_apply,
                LinearMap.smul_apply, map_smul, smul_smul, absFin_eq_norm_ind, T.σa_one]
              congr 1
              ring
  have hKfix : ∀ (g : L.L) (k' : L.L), k' ∈ τ.Kmax → f0 (g * k') = f0 g := by
    intro g k' hk'
    have hdecomp : g * k' = borelElem L (x g) (ζ g) (y g) * (k g * k') := by
      calc
        g * k' = (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g) * k g) * k' :=
          congrArg (fun q : L.L => q * k') (heq g)
        _ = borelElem L (x g) (ζ g) (y g) * (k g * k') := by
          dsimp [borelElem]
          group
    have hknew : k g * k' ∈ τ.Kmax := mul_mem (hk g) hk'
    calc
      f0 (g * k') = sphericalBorelAction T s (x g) (ζ g) (y g) (B.e 0) :=
        hf0_decomp (g * k') (x g) (ζ g) (y g) (k g * k') hknew hdecomp
      _ = f0 g := rfl
  have hf0 : IsSection L T s f0 := by
    refine ⟨hNcov, hZcov, ?_⟩
    have hopen : (τ.Kmax : Set L.L) ∈ nhds (1 : L.L) := by
      apply τ.open_.mem_nhds
      simp
    obtain ⟨m, hm, hsub⟩ := L.Kc_nhds _ hopen
    refine ⟨m, hm, ?_⟩
    intro g k' hk'
    exact hKfix g k' (hsub hk')
  have hf01 : f0 1 = B.e 0 := by
    have hdecomp : (1 : L.L) = borelElem L 0 1 1 * 1 := by simp [borelElem, L.a_one]
    calc
      f0 1 = sphericalBorelAction T s 0 1 1 (B.e 0) :=
        hf0_decomp 1 0 1 1 1 (τ.Kmax.one_mem) hdecomp
      _ = B.e 0 := by simp [sphericalBorelAction, absFin_eq_norm_ind, T.σa_one]
  refine ⟨f0, hf0, hf01, hKfix, ?_⟩
  intro f hf hKf
  have hfunit : ∀ u : (v.adicCompletion F)ˣ, IsLocUnit v u → T.σa u (f 1) = f 1 := by
    intro u hu
    have haK : L.a u ∈ τ.Kmax := τ.a_mem u hu.1 hu.2
    have hcov := hf.1 0 u 1
    have hleft : f (L.a u) =
        ((absFin v (u : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
          T.σa u (f 1) := by simpa using hcov
    have hright : f (L.a u) = f 1 := by simpa using hKf 1 (L.a u) haK
    rw [absFin_one_of_locUnit u hu] at hleft
    simp at hleft
    exact hleft.symm.trans hright
  obtain ⟨c, hc⟩ := tame_unitFixed T B hv (f 1) hfunit
  have hfvalue (g : L.L) : f g =
      sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := by
    have horder : borelElem L (x g) (ζ g) (y g) * k g =
        L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) := by
      dsimp [borelElem]
      calc
        (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g) * L.a (y g)) * k g =
            (L.n (Multiplicative.ofAdd (x g)) * L.z (ζ g)) * (L.a (y g) * k g) := by group
        _ = (L.z (ζ g) * L.n (Multiplicative.ofAdd (x g))) * (L.a (y g) * k g) := by
              rw [← L.z_central (ζ g)]
        _ = L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) := by group
    calc
      f g = f (borelElem L (x g) (ζ g) (y g) * k g) :=
        congrArg f (heq g)
      _ = f (L.z (ζ g) * (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g)) := by rw [horder]
      _ = ((ζ g : ℂˣ) : ℂ) • f (L.n (Multiplicative.ofAdd (x g)) * L.a (y g) * k g) :=
            hf.2.1 (ζ g) _
      _ = ((ζ g : ℂˣ) : ℂ) •
            (((absFin v (y g : v.adicCompletion F) : ℂ) ^ ((1 : ℂ) / 2 + s)) •
              T.σa (y g) (f (k g))) := by rw [hf.1 (x g) (y g) (k g)]
      _ = sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := by
            have hfk : f (k g) = f 1 := by simpa using hKf 1 (k g) (hk g)
            rw [hfk]
            rfl
  refine ⟨c, funext ?_⟩
  intro g
  calc
    f g = sphericalBorelAction T s (x g) (ζ g) (y g) (f 1) := hfvalue g
    _ = sphericalBorelAction T s (x g) (ζ g) (y g) (c • B.e 0) := by rw [hc]
    _ = c • f0 g := by simp [f0, map_smul]

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
  classical
  unfold bigCell
  split
  · rename_i h
    let x₀ := h.choose
    let ζ₀ := h.choose_spec.choose
    let y₀ := h.choose_spec.choose_spec.choose
    let t₀ := h.choose_spec.choose_spec.choose_spec.choose
    have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
    have hcoords := bigCell_coords_unique L x₀ x ζ₀ ζ y₀ y t₀ t hdecomp.symm
    rcases hcoords with ⟨hx, hy, ht, hζ⟩
    let eval : (v.adicCompletion F ×
        (rootsOfUnity 3 ℂ × ((v.adicCompletion F)ˣ × v.adicCompletion F))) → T.V :=
      fun q => ((q.2.1 : ℂˣ) : ℂ) •
        ((absFin v q.2.2.1 : ℂ) ^ ((1 : ℂ) / 2 + s)) • T.σa q.2.2.1 (φ q.2.2.2)
    have htuple : (x₀, (ζ₀, (y₀, t₀))) = (x, (ζ, (y, t))) := by
      apply Prod.ext
      · exact hx
      · apply Prod.ext
        · exact hζ
        · apply Prod.ext
          · exact hy
          · exact ht
    change eval (x₀, (ζ₀, (y₀, t₀))) = eval (x, (ζ, (y, t)))
    exact congrArg eval htuple
  · rename_i h
    exact False.elim (h ⟨x, ζ, y, t, rfl⟩)

theorem bigCell_borel (L : FinLocalCover D H v) (T : TorusRep D H v) (s : ℂ)
    (φ : v.adicCompletion F → T.V) (x : v.adicCompletion F) (ζ : rootsOfUnity 3 ℂ)
    (y : (v.adicCompletion F)ˣ) :
    bigCell L T s φ (L.n (Multiplicative.ofAdd x) * L.z ζ * L.a y) = 0 := by
  classical
  unfold bigCell
  split_ifs with h
  · let x₀ := h.choose
    let ζ₀ := h.choose_spec.choose
    let y₀ := h.choose_spec.choose_spec.choose
    let t₀ := h.choose_spec.choose_spec.choose_spec.choose
    have hdecomp := h.choose_spec.choose_spec.choose_spec.choose_spec
    exact (bigcell_ne_borel L x₀ x ζ₀ ζ y₀ y t₀ hdecomp.symm).elim
  · rfl

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
