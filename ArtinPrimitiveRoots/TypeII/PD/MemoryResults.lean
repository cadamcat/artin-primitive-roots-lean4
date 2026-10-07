import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §5 Memory results (PD 04:11-966) -/

/-- The lifespan expansion of one prime (mem:orphan-identity, mem:prefix, mem:suffix,
mem:run-charge before the `V_i` factors), PD 04:82-132.  `lam j = [z_j]_p`, `act j` = active at
visit `j`, `eta j = η'_j`, `bp = b'_p`.  No active visit: `1 +` orphan lifespans; active visits
with a common line `λ*`: one lifespan through `[α,γ] = [min A, max A]` with optional ghost
extensions at both ends; disagreeing active lines: `0`. -/
def lifespanSum (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1)) (act : Fin (N + 1) → Prop)
    (eta : Fin (N + 1) → ℝ) (bp : ℝ) : ℝ :=
  let A : Finset (Fin (N + 1)) := Finset.univ.filter act
  let hit (j : Fin (N + 1)) (l : Fin (p + 1)) : ℝ := if lam j = l then 1 else 0
  if hA : A.Nonempty then
    let α := A.min' hA
    let γ := A.max' hA
    let ls := lam α
    if ∀ j ∈ A, lam j = ls then
      (((p : ℝ) + 1) * bp)⁻¹ *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => h < α),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => h < j ∧ j < α),
              (1 - eta j * hit j ls)) *
        (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < γ ∧ j ∉ A), (1 - eta j * hit j ls)) *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => γ < h),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => γ < j ∧ j < h),
              (1 - eta j * hit j ls))
    else 0
  else
    1 + (((p : ℝ) + 1) * bp)⁻¹ *
      ∑ ac ∈ Finset.univ.filter (fun ac : Fin (N + 1) × Fin (N + 1) => ac.1 < ac.2),
        eta ac.1 * eta ac.2 * hit ac.2 (lam ac.1) *
          ∏ j ∈ Finset.univ.filter (fun j => ac.1 < j ∧ j < ac.2), (1 - eta j * hit j (lam ac.1))

/-- `t2:pd.prime-lifespan` (new node, general) — PD 04:68-115.  The primewise identity:
the independent-line factor of one prime equals `b'_p` times its lifespan expansion.  Proof:
expand the product; singletons give `b'_p`; for larger sets fix first and last index (orphan
case); for active primes only the common line survives and the outer products telescope. -/
theorem prime_lifespan (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1))
    (act : Fin (N + 1) → Prop) (eta : Fin (N + 1) → ℝ) (bp : ℝ)
    (hbp : bp = 1 - ∑ j : Fin (N + 1), eta j / ((p : ℝ) + 1)) (hbp0 : bp ≠ 0) :
    ((p : ℝ) + 1)⁻¹ * ∑ l : Fin (p + 1), ∏ j : Fin (N + 1),
        (if act j then (if lam j = l then (1 : ℝ) else 0)
          else 1 - eta j * (if lam j = l then 1 else 0)) =
      bp * lifespanSum p N lam act eta bp := by
  sorry

/-- The lifespan expansion of a group prime along a line-model path. -/
def pathLifespan {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) : ℝ :=
  lifespanSum p (pathLength S.x) (fun j => projLine p (γ j).1) (IsActiveAt γ p)
    (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p)

/-- `t2:pd.history-paths` (new node) — PD 04:234-246.  Exact decomposition of the distinct
history by the sequence of positions and active lists at the visits (ghosts do not move them;
the edges move along the path; distinct initial entries make every visit list valid). -/
theorem history_paths (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          historyDistinct F S ρ w =
            ∑' γ : EnvPath S.x K,
              if IsEnvPathAdmissible F S γ then memHistory F S ρ w none (some γ) distinctWeight else 0 := by
  sorry

/-- `t2:pd.history-path-value` (new node) — PD 04:234-274.  Along a fixed admissible path the
sum over memory choices with global birth distinctness factorizes over primes into lifespans:
store on leaving a nonfinal active run, promote on entering the next, ghost births/deletions at
the optional ghost endpoints; `ρ·(q_j/ρ²)·ρ = q_j` at pending hits; an active birth has measure
`ν_i(p) = ((p+1)b'_p)⁻¹V_i⁻¹`, a ghost birth `V_iν_i(p)` after cancellation, a promotion `V_i⁻¹`
(mem:run-charge); the symmetrization averages and `V_i⁻¹` weights are those of
`pathCoefficient`. -/
theorem history_path_value (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ →
          memHistory F S ρ w none (some γ) distinctWeight =
            pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
  sorry

/-- `t2:pd.memory-identity` — PD 04:43-274.  For every root of the region: the independent-line average of the
line-model moment equals the baseline `∏_p b'_p` times the distinct history value.  Proof:
`env_path_form`; the line average of a product over primes is the product of the per-prime
averages; `prime_lifespan`; `history_paths`; `history_path_value`. -/
theorem memory_identity (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          lineAverage (envMomentC F S w) =
            (memoryBaseline F S : ℂ) * historyDistinct F S ρ w := by
  sorry

/-- `t2:pd.truncation-adjoint` — PD 04:276-308.  REPLACES the frozen `truncation_adjoint`.
Inserting `Π_B`, `B = ⌈L²⌉`, around every operation changes the distinct history by
`O_A(L^{-AN})`: a history of memory size `> B` has `≥ B - KN` ghost births; with a factor `2` per
ghost birth the absolute ghost-only cost is `exp(O_K(N+1))`, the baseline and the path budget
`exp(O_K(L^{0.74}))`, so the omitted part is `2^{-B+KN} exp(O_K(L^{0.74}))`.  The adjoint rules
(mem:ghost-factorial), (mem:edge-factorial) of PD 04:310-363 are used in `ghost_edge_crude`
(column sums) and are not stated separately. -/
theorem truncation_adjoint (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
            C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  sorry

/-- `t2:pd.ghost-edge-crude` — PD 04:365-435.  REPLACES the frozen `ghost_edge_crude`.  On
`ℋ_B`, with the Schur weight `v₀^{k_tot}`: ghost row and column sums (mem:ghost-row),
(mem:ghost-column) are `≤ C_K` once `v₀` makes both parentheses `≤ 1` (uses `ρ² > √q_d`), so
`‖𝒢_j‖ ≤ C_K` (mem:ghost-norm); edge rows and columns are `≤ C_K B^K (1+L^{3A₀}) ≤ L^{C}`
(mem:edge-crude; columns via the adjoint rules, PD 04:310-348). -/
theorem ghost_edge_crude (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K Cexp x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < Cexp ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j ≤ S.N →
            MemRowSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemColSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemOpNormLE F S (memoryCutoff S) (memGhost F S ρ j) C_K ∧
            (j < S.N →
              MemRowSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp) ∧
              MemColSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp)) := by
  sorry

/-- `t2:pd.lattice-clean` (a) — PD 04:439-497.  Lattice box at a source passing good test (i):
in the coordinates `(h,l)` of `z' = h z + l D w_z`, the region `|l| ≤ C₁ Y`, `|h + lα| ≤ C₁`
(`α = D τ(w_z)/τ(z)`, from cell separation and the box) is covered, after a unimodular change of
coordinates, by a centered box with sides `A', B'`, `A'B' ≪ Y`, `Y^{0.1} ≤ A',B' ≤ Y^{0.9}`
(mem:lattice-shape).  Pure geometry of numbers: shortest vector `≥ Y^{-0.8}` by test (i),
`≪ Y^{-1/2}` by Dirichlet. -/
private def shearX (α : ℝ) (z : ℤ × ℤ) : ℝ := (z.1 : ℝ) + (z.2 : ℝ) * α

private def shearY (Y : ℝ) (z : ℤ × ℤ) : ℝ := (z.2 : ℝ) / Y

private def shearSize (Y α : ℝ) (z : ℤ × ℤ) : ℝ :=
  max |shearX α z| |shearY Y z|

private theorem circleDistance_le_abs_sub_int (t : ℝ) (z : ℤ) :
    circleDistance t ≤ |t - (z : ℝ)| := by
  unfold circleDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨k, rfl⟩
    exact abs_nonneg _
  · exact ⟨z, rfl⟩

private theorem exists_primitive_shear_vector (Y α : ℝ) (hY : 1 < Y)
    (hbad : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
      Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) :
    ∃ h l : ℤ, Int.gcd h l = 1 ∧
      Real.rpow Y (-(4 / 5 : ℝ)) ≤ shearSize Y α (h, l) ∧
      shearSize Y α (h, l) ≤ 2 / Real.sqrt Y := by
  classical
  have hYpos : 0 < Y := lt_trans zero_lt_one hY
  have hYone : 1 ≤ Y := hY.le
  let s : ℝ := Real.sqrt Y
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact (Real.one_le_sqrt).2 hYone
  let n : ℕ := ⌈s⌉₊
  have hsle : s ≤ (n : ℝ) := by
    dsimp [n]
    exact Nat.le_ceil _
  have hnpos : 0 < n := by
    have hcast : (1 : ℝ) ≤ (n : ℝ) := le_trans hsone hsle
    exact_mod_cast hcast
  obtain ⟨j, k, hkpos, hkn, happrox⟩ :=
    Real.exists_int_int_abs_mul_sub_le α (n := n) hnpos
  let h : ℤ := -j
  let l : ℤ := k
  have hlpos : 0 < l := by simpa [l] using hkpos
  have hfirst : |shearX α (h, l)| ≤ 1 / s := by
    have hnplus : s ≤ (n : ℝ) + 1 := by linarith [hsle]
    have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / s := by
      rw [div_le_div_iff₀ (by positivity) hspos]
      linarith
    have happrox' : |(k : ℝ) * α - j| ≤ 1 / ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using happrox
    calc
      |shearX α (h, l)| = |(k : ℝ) * α - j| := by
        simp [shearX, h, l, sub_eq_add_neg, add_comm]
      _ ≤ 1 / ((n : ℝ) + 1) := happrox'
      _ ≤ 1 / s := hrecip
  have hknCast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hsquare : s ^ 2 = Y := by dsimp [s]; exact Real.sq_sqrt hYpos.le
  have hsqrtLeY : s ≤ Y := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith [hY]
    dsimp [s]
    exact Real.sqrt_le_iff.mpr ⟨hYpos.le, hYsq⟩
  have hsecond : |shearY Y (h, l)| ≤ 2 / s := by
    have hkY : (k : ℝ) * s ≤ 2 * Y := by
      have hkn' : (k : ℝ) ≤ s + 1 := hknCast.trans_lt (Nat.ceil_lt_add_one (by positivity)) |>.le
      have hprod := mul_le_mul_of_nonneg_right hkn' hspos.le
      nlinarith [hprod, hsquare, hsqrtLeY]
    have hquot : (k : ℝ) / Y ≤ 2 / s := by
      rw [div_le_div_iff₀ hYpos hspos]
      exact hkY
    simpa [shearY, h, l, abs_of_pos (by positivity : 0 < (k : ℝ) / Y)] using hquot
  have hgpos : 0 < Int.gcd h l := Int.gcd_pos_of_ne_zero_right h hlpos.ne'
  obtain ⟨g, h', l', hg, hgcd, hh, hl⟩ := Int.exists_gcd_one' hgpos
  have hgcast : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hg)
  have hscaleX : shearX α (h, l) = (g : ℝ) * shearX α (h', l') := by
    dsimp [shearX]
    rw [hh, hl]
    push_cast
    ring
  have hscaleY : shearY Y (h, l) = (g : ℝ) * shearY Y (h', l') := by
    dsimp [shearY]
    rw [hl]
    push_cast
    ring
  have hgAbs : |(g : ℝ)| = (g : ℝ) := abs_of_nonneg (by positivity)
  have hxnorm : |shearX α (h', l')| ≤ |shearX α (h, l)| := by
    rw [hscaleX, abs_mul, hgAbs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgcast) (abs_nonneg (shearX α (h', l')))]
  have hynorm : |shearY Y (h', l')| ≤ |shearY Y (h, l)| := by
    rw [hscaleY, abs_mul, hgAbs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgcast) (abs_nonneg (shearY Y (h', l')))]
  refine ⟨h', l', hgcd, ?_, ?_⟩
  · by_contra hnot
    have hsmall : shearSize Y α (h', l') < Real.rpow Y (-(4 / 5 : ℝ)) := lt_of_not_ge hnot
    have hpowle : Real.rpow Y (-(4 / 5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hYone (by norm_num)
    have hsizeone : shearSize Y α (h', l') < 1 := hsmall.trans_le hpowle
    by_cases hlzero : l' = 0
    · have hhsmall : |(h' : ℝ)| < 1 := by
        have hxle : |shearX α (h', l')| ≤ shearSize Y α (h', l') := le_max_left _ _
        simpa [shearX, hlzero] using lt_of_le_of_lt hxle hsizeone
      have hzcast : -1 < (h' : ℝ) ∧ (h' : ℝ) < 1 := abs_lt.mp hhsmall
      have hz : -1 < h' ∧ h' < 1 := by exact_mod_cast hzcast
      have hhzero : h' = 0 := by omega
      simp [hlzero, hhzero] at hgcd
    · have hmpos : 0 < l'.natAbs := Int.natAbs_pos.mpr hlzero
      have hmcast : (l'.natAbs : ℝ) = |(l' : ℝ)| := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs l')
        simpa using h
      have hcoord : |(l' : ℝ)| / Y ≤ shearSize Y α (h', l') := by
        calc
          |(l' : ℝ)| / Y = |shearY Y (h', l')| := by
            simp [shearY, abs_div, abs_of_pos hYpos]
          _ ≤ shearSize Y α (h', l') := le_max_right _ _
      have hsmallcoord : (l'.natAbs : ℝ) / Y < Real.rpow Y (-(4 / 5 : ℝ)) := by
        rw [hmcast]
        exact lt_of_le_of_lt hcoord hsmall
      have hprod : (l'.natAbs : ℝ) ≤ Real.rpow Y (-(4 / 5 : ℝ)) * Y :=
        (div_le_iff₀ hYpos).mp hsmallcoord.le
      have hpowmul : Real.rpow Y (-(4 / 5 : ℝ)) * Y = Real.rpow Y (1 / 5 : ℝ) := by
        calc
          Real.rpow Y (-(4 / 5 : ℝ)) * Y =
              Real.rpow Y (-(4 / 5 : ℝ)) * Real.rpow Y 1 := by
                exact congrArg (fun q : ℝ => Real.rpow Y (-(4 / 5 : ℝ)) * q)
                  (Real.rpow_one Y).symm
          _ = Real.rpow Y (-(4 / 5 : ℝ) + 1) :=
            (Real.rpow_add hYpos (-(4 / 5 : ℝ)) 1).symm
          _ = Real.rpow Y (1 / 5 : ℝ) := by congr 1 <;> norm_num
      have hmBound : (l'.natAbs : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) := by
        rw [hpowmul] at hprod
        exact hprod
      have hmone : 1 ≤ l'.natAbs := Nat.one_le_iff_ne_zero.mpr (by omega)
      have hdist : circleDistance ((l'.natAbs : ℝ) * α) ≤ |shearX α (h', l')| := by
        have hmcast' : (l'.natAbs : ℝ) = |(l' : ℝ)| := hmcast
        by_cases hlnonneg : 0 ≤ l'
        · have hmcast'' : (l'.natAbs : ℝ) = (l' : ℝ) := by
            rw [hmcast', abs_of_nonneg (by exact_mod_cast hlnonneg)]
          have heq : (l'.natAbs : ℝ) * α - (-(h' : ℝ)) = shearX α (h', l') := by
            simp [shearX, hmcast'']
            ring
          calc
            circleDistance ((l'.natAbs : ℝ) * α) ≤
                |(l'.natAbs : ℝ) * α - (-(h' : ℝ))| :=
                  by simpa only [Int.cast_neg] using circleDistance_le_abs_sub_int _ (-h')
            _ = |shearX α (h', l')| := by rw [heq]
        · have hlneg : (l' : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hlnonneg)
          have hmcast'' : (l'.natAbs : ℝ) = -(l' : ℝ) := by
            rw [hmcast', abs_of_neg hlneg]
          have heq : (l'.natAbs : ℝ) * α - (h' : ℝ) = -shearX α (h', l') := by
            simp [shearX, hmcast'']
            ring
          calc
            circleDistance ((l'.natAbs : ℝ) * α) ≤
                |(l'.natAbs : ℝ) * α - (h' : ℝ)| := circleDistance_le_abs_sub_int _ h'
            _ = |shearX α (h', l')| := by rw [heq, abs_neg]
      have htest := hbad l'.natAbs hmone hmBound
      have hxle : |shearX α (h', l')| ≤ shearSize Y α (h', l') := le_max_left _ _
      have hpowlt : Real.rpow Y (-(4 / 5 : ℝ)) < Real.rpow Y (-(7 / 10 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)
      linarith
  · apply max_le
    · exact hxnorm.trans <| hfirst.trans <| by
        have hsplus : 1 / s ≤ 2 / s :=
          div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hspos.le
        exact hsplus
    · exact hynorm.trans hsecond

private def intDet (z z' : ℤ × ℤ) : ℤ := z.1 * z'.2 - z.2 * z'.1

private theorem shear_det (Y α : ℝ) (hY : 0 < Y) (z z' : ℤ × ℤ) :
    shearX α z * shearY Y z' - shearY Y z * shearX α z' =
      (intDet z z' : ℝ) / Y := by
  rcases z with ⟨h, l⟩
  rcases z' with ⟨h', l'⟩
  simp only [shearX, shearY, intDet]
  field_simp [hY.ne']
  push_cast
  ring

private theorem bound_det_second (Y lam x₁ y₁ x₂ y₂ : ℝ) (hY : 0 < Y) (hlam : 0 < lam)
    (hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y) (hx₁ : |x₁| = lam) (hy₁ : |y₁| ≤ lam)
    (hx₂ : |x₂| ≤ lam / 2) (hlamsq : lam ^ 2 ≤ 4 / Y) :
    |y₂| ≤ 3 / (Y * lam) := by
  have hlamYsq : lam ^ 2 * Y ≤ 4 := by
    calc
      lam ^ 2 * Y ≤ (4 / Y) * Y := mul_le_mul_of_nonneg_right hlamsq hY.le
      _ = 4 := by field_simp [hY.ne']
  have hrel : x₁ * y₂ = 1 / Y + y₁ * x₂ := by linarith [hdet]
  have hprod : |x₁ * y₂| ≤ 3 / Y := by
    calc
      |x₁ * y₂| = |1 / Y + y₁ * x₂| := by rw [hrel]
      _ ≤ |1 / Y| + |y₁ * x₂| := abs_add_le _ _
      _ = 1 / Y + |y₁| * |x₂| := by rw [abs_of_pos (div_pos one_pos hY), abs_mul]
      _ ≤ 1 / Y + lam * (lam / 2) := by
        gcongr
      _ ≤ 3 / Y := by
        have hsum : 1 / Y + lam ^ 2 / 2 ≤ 3 / Y := by
          rw [le_div_iff₀ hY]
          field_simp [hY.ne']
          nlinarith [hlamYsq]
        nlinarith
  have habs : |y₂| = |x₁ * y₂| / lam := by
    rw [abs_mul, hx₁]
    field_simp [hlam.ne']
  rw [habs]
  calc
    |x₁ * y₂| / lam ≤ (3 / Y) / lam := div_le_div_of_nonneg_right hprod hlam.le
    _ = 3 / (Y * lam) := by field_simp [hY.ne', hlam.ne']

private theorem exists_shear_complement (Y α : ℝ) (z : ℤ × ℤ) (hY : 0 < Y)
    (hprim : Int.gcd z.1 z.2 = 1) (hlampos : 0 < shearSize Y α z)
    (hlamsq : shearSize Y α z ^ 2 ≤ 4 / Y) :
    ∃ z' : ℤ × ℤ, intDet z z' = 1 ∧
      shearSize Y α z' ≤ 3 / (Y * shearSize Y α z) := by
  classical
  let lam : ℝ := shearSize Y α z
  let zbase : ℤ × ℤ := (-Int.gcdB z.1 z.2, Int.gcdA z.1 z.2)
  have hlam : 0 < lam := hlampos
  have hlamsq' : lam ^ 2 ≤ 4 / Y := hlamsq
  have hlamYsq : lam ^ 2 * Y ≤ 4 := by
    calc
      lam ^ 2 * Y ≤ (4 / Y) * Y := mul_le_mul_of_nonneg_right hlamsq' hY.le
      _ = 4 := by field_simp [hY.ne']
  have hlamhalf : lam / 2 ≤ 3 / (Y * lam) := by
    rw [le_div_iff₀ (mul_pos hY hlam)]
    field_simp [hY.ne', hlam.ne']
    nlinarith [hlamYsq]
  have hBez : (Int.gcd z.1 z.2 : ℤ) = z.1 * Int.gcdA z.1 z.2 +
      z.2 * Int.gcdB z.1 z.2 := Int.gcd_eq_gcd_ab _ _
  have hzbase : intDet z zbase = 1 := by
    dsimp [intDet, zbase]
    rw [hprim] at hBez
    calc
      z.1 * Int.gcdA z.1 z.2 - z.2 * -Int.gcdB z.1 z.2 =
          z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2 := by ring
      _ = 1 := hBez.symm
  let x₁ : ℝ := shearX α z
  let y₁ : ℝ := shearY Y z
  let x₂ : ℝ := shearX α zbase
  let y₂ : ℝ := shearY Y zbase
  by_cases hdom : |x₁| ≥ |y₁|
  · have hx₁ : |x₁| = lam := by
      dsimp [lam, shearSize, x₁, y₁]
      rw [max_eq_left hdom]
    have hy₁ : |y₁| ≤ lam := by
      dsimp [lam, shearSize, x₁, y₁]
      exact le_max_right _ _
    have hx₁ne : x₁ ≠ 0 := abs_ne_zero.mp (by rw [hx₁]; exact hlam.ne')
    let n : ℤ := round (x₂ / x₁)
    let z' : ℤ × ℤ := (zbase.1 - n * z.1, zbase.2 - n * z.2)
    have hz' : intDet z z' = 1 := by
      have hshift : intDet z (zbase.1 - n * z.1, zbase.2 - n * z.2) = intDet z zbase := by
        dsimp [intDet]
        ring
      simpa [z'] using hshift.trans hzbase
    have hx₂' : shearX α z' = x₂ - (n : ℝ) * x₁ := by
      dsimp [shearX, z', x₁, x₂]
      push_cast
      ring
    have hy₂' : shearY Y z' = y₂ - (n : ℝ) * y₁ := by
      dsimp [shearY, z', y₁, y₂]
      push_cast
      ring
    have hround : |x₂ / x₁ - (n : ℝ)| ≤ 1 / 2 := by
      dsimp [n]
      exact abs_sub_round _
    have hrel : x₂ - (n : ℝ) * x₁ = x₁ * (x₂ / x₁ - (n : ℝ)) := by
      field_simp [hx₁ne]
    have hround' : |x₂ / x₁ - (n : ℝ)| ≤ (2 : ℝ)⁻¹ := by
      convert hround using 1 <;> norm_num
    have hx₂small : |shearX α z'| ≤ lam / 2 := by
      rw [hx₂', hrel, abs_mul, hx₁]
      exact mul_le_mul_of_nonneg_left hround' hlam.le
    have hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y := by
      have h := shear_det Y α hY z zbase
      have hdetCast : (intDet z zbase : ℝ) = 1 := by exact_mod_cast hzbase
      change x₁ * y₂ - y₁ * x₂ = (intDet z zbase : ℝ) / Y at h
      rw [hdetCast] at h
      simpa [x₁, y₁, x₂, y₂] using h
    have hdet' : x₁ * shearY Y z' - y₁ * shearX α z' = 1 / Y := by
      have h := shear_det Y α hY z z'
      have hdetCast : (intDet z z' : ℝ) = 1 := by exact_mod_cast hz'
      change x₁ * shearY Y z' - y₁ * shearX α z' = (intDet z z' : ℝ) / Y at h
      rw [hdetCast] at h
      simpa using h
    have hy₂bound := bound_det_second Y lam x₁ y₁ (shearX α z') (shearY Y z')
      hY hlam hdet' hx₁ hy₁ hx₂small hlamsq'
    refine ⟨z', hz', ?_⟩
    dsimp [shearSize]
    exact max_le (hx₂small.trans hlamhalf) hy₂bound
  · have hdom' : |y₁| ≥ |x₁| := le_of_not_ge hdom
    have hy₁eq : |y₁| = lam := by
      dsimp [lam, shearSize, x₁, y₁]
      rw [max_eq_right hdom']
    have hx₁le : |x₁| ≤ lam := by
      dsimp [lam, shearSize, x₁, y₁]
      exact le_max_left _ _
    have hy₁ne : y₁ ≠ 0 := abs_ne_zero.mp (by rw [hy₁eq]; exact hlam.ne')
    let n : ℤ := round (y₂ / y₁)
    let z' : ℤ × ℤ := (zbase.1 - n * z.1, zbase.2 - n * z.2)
    have hz' : intDet z z' = 1 := by
      have hshift : intDet z (zbase.1 - n * z.1, zbase.2 - n * z.2) = intDet z zbase := by
        dsimp [intDet]
        ring
      simpa [z'] using hshift.trans hzbase
    have hx₂' : shearX α z' = x₂ - (n : ℝ) * x₁ := by
      dsimp [shearX, z', x₁, x₂]
      push_cast
      ring
    have hy₂' : shearY Y z' = y₂ - (n : ℝ) * y₁ := by
      dsimp [shearY, z', y₁, y₂]
      push_cast
      ring
    have hround : |y₂ / y₁ - (n : ℝ)| ≤ 1 / 2 := by
      dsimp [n]
      exact abs_sub_round _
    have hrel : y₂ - (n : ℝ) * y₁ = y₁ * (y₂ / y₁ - (n : ℝ)) := by
      field_simp [hy₁ne]
    have hround' : |y₂ / y₁ - (n : ℝ)| ≤ (2 : ℝ)⁻¹ := by
      convert hround using 1 <;> norm_num
    have hy₂small : |shearY Y z'| ≤ lam / 2 := by
      rw [hy₂', hrel, abs_mul, hy₁eq]
      exact mul_le_mul_of_nonneg_left hround' hlam.le
    have hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y := by
      have h := shear_det Y α hY z zbase
      have hdetCast : (intDet z zbase : ℝ) = 1 := by exact_mod_cast hzbase
      change x₁ * y₂ - y₁ * x₂ = (intDet z zbase : ℝ) / Y at h
      rw [hdetCast] at h
      simpa [x₁, y₁, x₂, y₂] using h
    have hdet' : y₁ * (-shearX α z') - x₁ * (-shearY Y z') = 1 / Y := by
      have h := shear_det Y α hY z z'
      have hdetCast : (intDet z z' : ℝ) = 1 := by exact_mod_cast hz'
      change x₁ * shearY Y z' - y₁ * shearX α z' = (intDet z z' : ℝ) / Y at h
      rw [hdetCast] at h
      nlinarith [h]
    have hx₂bound := bound_det_second Y lam y₁ x₁ (-shearY Y z') (-shearX α z')
      hY hlam hdet' hy₁eq hx₁le (by simpa [abs_neg] using hy₂small) hlamsq'
    refine ⟨z', hz', ?_⟩
    dsimp [shearSize]
    have hx₂small : |shearX α z'| ≤ 3 / (Y * lam) := by simpa [abs_neg] using hx₂bound
    have hy₂bound : |shearY Y z'| ≤ 3 / (Y * lam) := hy₂small.trans hlamhalf
    exact max_le hx₂small hy₂bound

set_option maxHeartbeats 500000 in
theorem lattice_shape (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₂ Y₀ : ℝ, 0 < C₂ ∧ 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ α : ℝ,
      (∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
        Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) →
      ∃ (a₀ b₀ c₀ d₀ : ℤ) (A' B' : ℝ), a₀ * d₀ - b₀ * c₀ = 1 ∧ A' * B' ≤ C₂ * Y ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ A' ∧ A' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ B' ∧ B' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y → |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
          |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧ |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
  let C₂ : ℝ := 12 * C₁ ^ 2
  let Y₀ : ℝ := (8 * C₁) ^ 10
  have hC₂pos : 0 < C₂ := by dsimp [C₂]; positivity
  have h8C : 1 ≤ 8 * C₁ := by nlinarith [hC₁]
  have hY₀one : 1 ≤ Y₀ := by dsimp [Y₀]; exact one_le_pow₀ h8C
  refine ⟨C₂, Y₀, hC₂pos, hY₀one, ?_⟩
  intro Y hY α hbad
  have h8Cgt : 1 < 8 * C₁ := by nlinarith [hC₁]
  have hY₀gt : 1 < Y₀ := by
    dsimp [Y₀]
    have hpow : (1 : ℝ) ^ 10 < (8 * C₁) ^ 10 := by gcongr
    simpa using hpow
  have hYgt : 1 < Y := lt_of_lt_of_le hY₀gt hY
  have hYpos : 0 < Y := lt_trans zero_lt_one hYgt
  have hYone : 1 ≤ Y := hYgt.le
  have hBasePow : (8 * C₁) ^ 10 ≤ Y := by simpa [Y₀] using hY
  have hRootEq : Real.rpow ((8 * C₁) ^ 10) (1 / 10 : ℝ) = 8 * C₁ := by
    simpa [one_div] using
      (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 8 * C₁) (by norm_num : 10 ≠ 0))
  have hRoot : 8 * C₁ ≤ Real.rpow Y (1 / 10 : ℝ) := by
    calc
      8 * C₁ = Real.rpow ((8 * C₁) ^ 10) (1 / 10 : ℝ) := hRootEq.symm
      _ ≤ Real.rpow Y (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hBasePow (by norm_num)
  have hRoot4 : 8 * C₁ ≤ Real.rpow Y (2 / 5 : ℝ) := by
    exact hRoot.trans <| Real.rpow_le_rpow_of_exponent_le hYone (by norm_num)
  obtain ⟨a, c, hprim, hLamLow, hLamUp⟩ := exists_primitive_shear_vector Y α hYgt hbad
  let z₁ : ℤ × ℤ := (a, c)
  let lam : ℝ := shearSize Y α z₁
  have hLamPos : 0 < lam := by
    dsimp [lam, z₁]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hYpos _) hLamLow
  have hLamsq : lam ^ 2 ≤ 4 / Y := by
    have hdiff : 0 ≤ 2 / Real.sqrt Y - lam := sub_nonneg.mpr (by simpa [lam, z₁] using hLamUp)
    have hsum : 0 ≤ 2 / Real.sqrt Y + lam := by positivity
    have hsq : lam ^ 2 ≤ (2 / Real.sqrt Y) ^ 2 := by
      nlinarith [mul_nonneg hdiff hsum]
    have hsquare : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hYpos.le
    have hsqrtNe : Real.sqrt Y ≠ 0 := (Real.sqrt_ne_zero').2 hYpos
    have hdiv : (2 / Real.sqrt Y) ^ 2 = 4 / Y := by
      field_simp [hsqrtNe, hYpos.ne']
      rw [hsquare]
      ring
    rw [hdiv] at hsq
    exact hsq
  obtain ⟨z₂, hdetZ, hZ₂size⟩ := exists_shear_complement Y α z₁ hYpos hprim
    (by simpa [lam] using hLamPos) (by simpa [lam] using hLamsq)
  have hZ₂coords : |shearX α z₂| ≤ 3 / (Y * lam) ∧
      |shearY Y z₂| ≤ 3 / (Y * lam) := by
    simpa [shearSize, lam] using hZ₂size
  let a₀ : ℤ := z₁.1
  let c₀ : ℤ := z₁.2
  let b₀ : ℤ := z₂.1
  let d₀ : ℤ := z₂.2
  let A' : ℝ := 6 * C₁ / lam
  let B' : ℝ := 2 * C₁ * Y * lam
  have hdetFinal : a₀ * d₀ - b₀ * c₀ = 1 := by
    have h := hdetZ
    simpa [intDet, a₀, b₀, c₀, d₀, z₁, mul_comm] using h
  have hProductEq : A' * B' = C₂ * Y := by
    dsimp [A', B', C₂]
    field_simp [hLamPos.ne']
    ring
  have hSqrtEq : Real.sqrt Y = Real.rpow Y (1 / 2 : ℝ) := Real.sqrt_eq_rpow Y
  have hNegSqrt : (Real.sqrt Y)⁻¹ = Real.rpow Y (-(1 / 2 : ℝ)) := by
    calc
      (Real.sqrt Y)⁻¹ = (Real.rpow Y (1 / 2 : ℝ))⁻¹ := by rw [hSqrtEq]
      _ = Real.rpow Y (-(1 / 2 : ℝ)) := (Real.rpow_neg hYpos.le (1 / 2 : ℝ)).symm
  have hLamUpper : lam ≤ 2 * Real.rpow Y (-(1 / 2 : ℝ)) := by
    calc
      lam ≤ 2 / Real.sqrt Y := by simpa [lam, z₁] using hLamUp
      _ = 2 * (Real.sqrt Y)⁻¹ := by ring
      _ = 2 * Real.rpow Y (-(1 / 2 : ℝ)) := by rw [hNegSqrt]
  have hPowMul (u v : ℝ) :
      Real.rpow Y u * Real.rpow Y v = Real.rpow Y (u + v) :=
    (Real.rpow_add hYpos u v).symm
  have hPowA : Real.rpow Y (9 / 10 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) =
      Real.rpow Y (1 / 10 : ℝ) := by
    convert hPowMul (9 / 10 : ℝ) (-(4 / 5 : ℝ)) using 1 <;> norm_num
  have hPowTiny : Real.rpow Y (1 / 10 : ℝ) * Real.rpow Y (-(1 / 2 : ℝ)) =
      Real.rpow Y (-(2 / 5 : ℝ)) := by
    convert hPowMul (1 / 10 : ℝ) (-(1 / 2 : ℝ)) using 1 <;> norm_num
  have hPowB : Real.rpow Y (1 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) =
      Real.rpow Y (1 / 5 : ℝ) := by
    convert hPowMul (1 : ℝ) (-(4 / 5 : ℝ)) using 1 <;> norm_num
  have hPowS : Real.rpow Y (2 / 5 : ℝ) * Real.rpow Y (1 / 2 : ℝ) =
      Real.rpow Y (9 / 10 : ℝ) := by
    convert hPowMul (2 / 5 : ℝ) (1 / 2 : ℝ) using 1 <;> norm_num
  have hNegLeOne : Real.rpow Y (-(2 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hYone (by norm_num)
  have hAUpper : A' ≤ Real.rpow Y (9 / 10 : ℝ) := by
    dsimp [A']
    apply (div_le_iff₀ hLamPos).2
    calc
      6 * C₁ ≤ Real.rpow Y (1 / 10 : ℝ) := by nlinarith [hRoot]
      _ = Real.rpow Y (9 / 10 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) := hPowA.symm
      _ ≤ Real.rpow Y (9 / 10 : ℝ) * lam :=
        mul_le_mul_of_nonneg_left hLamLow (Real.rpow_pos_of_pos hYpos _).le
  have hALower : Real.rpow Y (1 / 10 : ℝ) ≤ A' := by
    dsimp [A']
    apply (le_div_iff₀ hLamPos).2
    have hprod : Real.rpow Y (1 / 10 : ℝ) * lam ≤ 2 := by
      calc
        Real.rpow Y (1 / 10 : ℝ) * lam ≤
            Real.rpow Y (1 / 10 : ℝ) * (2 * Real.rpow Y (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hLamUpper (Real.rpow_pos_of_pos hYpos _).le
        _ = 2 * Real.rpow Y (-(2 / 5 : ℝ)) := by
          calc
            _ = 2 * (Real.rpow Y (1 / 10 : ℝ) * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
            _ = 2 * Real.rpow Y (-(2 / 5 : ℝ)) := by rw [hPowTiny]
        _ ≤ 2 := by nlinarith [hNegLeOne]
    have hsmall : 2 ≤ 6 * C₁ := by nlinarith [hC₁]
    exact hprod.trans hsmall
  have hYlam : Real.rpow Y (1 / 5 : ℝ) ≤ Y * lam := by
    calc
      Real.rpow Y (1 / 5 : ℝ) = Real.rpow Y 1 * Real.rpow Y (-(4 / 5 : ℝ)) := hPowB.symm
      _ = Y * Real.rpow Y (-(4 / 5 : ℝ)) := by
        exact congrArg (fun x : ℝ => x * Real.rpow Y (-(4 / 5 : ℝ))) (Real.rpow_one Y)
      _ ≤ Y * lam := mul_le_mul_of_nonneg_left hLamLow hYpos.le
  have hBLower : Real.rpow Y (1 / 10 : ℝ) ≤ B' := by
    dsimp [B']
    calc
      Real.rpow Y (1 / 10 : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYone (by norm_num)
      _ ≤ 2 * C₁ * Real.rpow Y (1 / 5 : ℝ) := by
        have hcoef : 0 ≤ 2 * C₁ - 1 := by nlinarith [hC₁]
        have hpow : 0 ≤ Real.rpow Y (1 / 5 : ℝ) :=
          (Real.rpow_pos_of_pos hYpos (1 / 5 : ℝ)).le
        have hmul : 0 ≤ (2 * C₁ - 1) * Real.rpow Y (1 / 5 : ℝ) := mul_nonneg hcoef hpow
        nlinarith [hmul]
      _ ≤ 2 * C₁ * (Y * lam) :=
        mul_le_mul_of_nonneg_left hYlam (by positivity)
      _ = 2 * C₁ * Y * lam := by ring
  have hBUpper : B' ≤ Real.rpow Y (9 / 10 : ℝ) := by
    dsimp [B']
    have hYmulNeg : Y * Real.rpow Y (-(1 / 2 : ℝ)) = Real.rpow Y (1 / 2 : ℝ) := by
      calc
      Y * Real.rpow Y (-(1 / 2 : ℝ)) =
            Real.rpow Y 1 * Real.rpow Y (-(1 / 2 : ℝ)) := by
              exact congrArg (fun x : ℝ => x * Real.rpow Y (-(1 / 2 : ℝ))) (Real.rpow_one Y).symm
        _ = Real.rpow Y (1 / 2 : ℝ) := by
          convert hPowMul (1 : ℝ) (-(1 / 2 : ℝ)) using 1 <;> norm_num
    calc
      2 * C₁ * Y * lam ≤ 2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hLamUpper (by positivity : 0 ≤ 2 * C₁ * Y)
        calc
          2 * C₁ * Y * lam = (2 * C₁ * Y) * lam := by ring
          _ ≤ (2 * C₁ * Y) * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := hmul
          _ = 2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
      _ = 4 * C₁ * Real.rpow Y (1 / 2 : ℝ) := by
        calc
          2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) =
              4 * C₁ * (Y * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
          _ = 4 * C₁ * Real.rpow Y (1 / 2 : ℝ) := by rw [hYmulNeg]
      _ ≤ Real.rpow Y (2 / 5 : ℝ) * Real.rpow Y (1 / 2 : ℝ) := by
        have h4C : 4 * C₁ ≤ Real.rpow Y (2 / 5 : ℝ) := by linarith [hRoot4, hC₁]
        exact mul_le_mul_of_nonneg_right h4C (Real.rpow_pos_of_pos hYpos (1 / 2 : ℝ)).le
      _ = Real.rpow Y (9 / 10 : ℝ) := hPowS
  have hdetShear : shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂ = 1 / Y := by
    have h := shear_det Y α hYpos z₁ z₂
    have hdetCast : (intDet z₁ z₂ : ℝ) = 1 := by exact_mod_cast hdetZ
    change shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂ =
      (intDet z₁ z₂ : ℝ) / Y at h
    rw [hdetCast] at h
    exact h
  have hZ₁coords : |shearX α z₁| ≤ lam ∧ |shearY Y z₁| ≤ lam := by
    dsimp [lam, shearSize]
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  have hBox : ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y →
      |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
        |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧
          |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
    intro h l hlBound hhBound
    let ξ : ℤ := d₀ * h - b₀ * l
    let η : ℤ := a₀ * l - c₀ * h
    have hcoordH : a₀ * ξ + b₀ * η = h := by
      dsimp [ξ, η]
      linear_combination h * hdetFinal
    have hcoordL : c₀ * ξ + d₀ * η = l := by
      dsimp [ξ, η]
      linear_combination l * hdetFinal
    have hcoordH' : (a₀ : ℝ) * (ξ : ℝ) + (b₀ : ℝ) * (η : ℝ) = (h : ℝ) := by
      exact_mod_cast hcoordH
    have hcoordL' : (c₀ : ℝ) * (ξ : ℝ) + (d₀ : ℝ) * (η : ℝ) = (l : ℝ) := by
      exact_mod_cast hcoordL
    have hXdecomp : shearX α (h, l) =
        (ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂ := by
      change (h : ℝ) + (l : ℝ) * α =
        (ξ : ℝ) * ((a₀ : ℝ) + (c₀ : ℝ) * α) +
          (η : ℝ) * ((b₀ : ℝ) + (d₀ : ℝ) * α)
      rw [← hcoordH', ← hcoordL']
      ring
    have hYdecomp : shearY Y (h, l) =
        (ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂ := by
      change (l : ℝ) / Y =
        (ξ : ℝ) * ((c₀ : ℝ) / Y) + (η : ℝ) * ((d₀ : ℝ) / Y)
      rw [← hcoordL']
      ring
    have hξFormula : (ξ : ℝ) = Y *
        (shearX α (h, l) * shearY Y z₂ - shearY Y (h, l) * shearX α z₂) := by
      rw [hXdecomp, hYdecomp]
      have hlin :
          ((ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂) * shearY Y z₂ -
          ((ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂) * shearX α z₂ =
            (ξ : ℝ) * (shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂) := by ring
      rw [hlin, hdetShear]
      field_simp [hYpos.ne']
    have hηFormula : (η : ℝ) = Y *
        (shearX α z₁ * shearY Y (h, l) - shearY Y z₁ * shearX α (h, l)) := by
      rw [hXdecomp, hYdecomp]
      have hlin :
          shearX α z₁ * ((ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂) -
          shearY Y z₁ * ((ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂) =
            (η : ℝ) * (shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂) := by ring
      rw [hlin, hdetShear]
      field_simp [hYpos.ne']
    have hTargetX : |shearX α (h, l)| ≤ C₁ := by simpa [shearX] using hhBound
    have hC₁nonneg : 0 ≤ C₁ := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC₁
    have hTargetY : |shearY Y (h, l)| ≤ C₁ := by
      change |(l : ℝ) / Y| ≤ C₁
      rw [abs_div, abs_of_pos hYpos]
      exact (div_le_iff₀ hYpos).2 hlBound
    have hDetX : |shearX α (h, l) * shearY Y z₂ -
        shearY Y (h, l) * shearX α z₂| ≤
          C₁ * |shearY Y z₂| + C₁ * |shearX α z₂| := by
      calc
        _ ≤ |shearX α (h, l) * shearY Y z₂| +
            |shearY Y (h, l) * shearX α z₂| := by
          simpa using abs_sub_le (shearX α (h, l) * shearY Y z₂) 0
            (shearY Y (h, l) * shearX α z₂)
        _ = |shearX α (h, l)| * |shearY Y z₂| +
            |shearY Y (h, l)| * |shearX α z₂| := by rw [abs_mul, abs_mul]
        _ ≤ C₁ * |shearY Y z₂| + C₁ * |shearX α z₂| := by
            gcongr
    have hDetY : |shearX α z₁ * shearY Y (h, l) -
        shearY Y z₁ * shearX α (h, l)| ≤
          |shearX α z₁| * C₁ + |shearY Y z₁| * C₁ := by
      calc
        _ ≤ |shearX α z₁ * shearY Y (h, l)| +
            |shearY Y z₁ * shearX α (h, l)| := by
          simpa using abs_sub_le (shearX α z₁ * shearY Y (h, l)) 0
            (shearY Y z₁ * shearX α (h, l))
        _ = |shearX α z₁| * |shearY Y (h, l)| +
            |shearY Y z₁| * |shearX α (h, l)| := by rw [abs_mul, abs_mul]
        _ ≤ |shearX α z₁| * C₁ + |shearY Y z₁| * C₁ := by
            gcongr
    have hξBound : |(ξ : ℝ)| ≤ A' := by
      rw [hξFormula, abs_mul, abs_of_pos hYpos]
      calc
        Y * |shearX α (h, l) * shearY Y z₂ -
            shearY Y (h, l) * shearX α z₂| ≤
            Y * (C₁ * |shearY Y z₂| + C₁ * |shearX α z₂|) :=
          mul_le_mul_of_nonneg_left hDetX hYpos.le
        _ ≤ Y * (C₁ * (3 / (Y * lam)) + C₁ * (3 / (Y * lam))) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hZ₂coords.2 hC₁nonneg)
              (mul_le_mul_of_nonneg_left hZ₂coords.1 hC₁nonneg)
          · exact hYpos.le
        _ = A' := by dsimp [A']; field_simp [hYpos.ne', hLamPos.ne']; ring
    have hηBound : |(η : ℝ)| ≤ B' := by
      rw [hηFormula, abs_mul, abs_of_pos hYpos]
      calc
        Y * |shearX α z₁ * shearY Y (h, l) -
            shearY Y z₁ * shearX α (h, l)| ≤
            Y * (|shearX α z₁| * C₁ + |shearY Y z₁| * C₁) :=
          mul_le_mul_of_nonneg_left hDetY hYpos.le
        _ ≤ Y * (lam * C₁ + lam * C₁) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_right hZ₁coords.1 hC₁nonneg)
              (mul_le_mul_of_nonneg_right hZ₁coords.2 hC₁nonneg)
          · exact hYpos.le
        _ = B' := by dsimp [B']; ring
    exact ⟨by simpa [ξ] using hξBound, by simpa [η] using hηBound⟩
  have hproduct : A' * B' ≤ C₂ * Y := by
    exact hProductEq.le
  exact ⟨a₀, b₀, c₀, d₀, A', B', hdetFinal, hproduct,
    hALower, hAUpper, hBLower, hBUpper, hBox⟩

/-- `t2:pd.lattice-clean` (b) — PD 04:499-603.  REPLACES the frozen `lattice_clean`.  For every
`G` there is `A₀` with `‖ℰ_j^{clean}‖_{ℋ_B} ≤ L^{-G}` (mem:clean-bound): condition on shared list
and memory, drop the extra ban (cost `C_K M sup ν`), reduce by `lattice_shape` to the
determinant-exponential matrix on the box (mem:clean-kernel), Fourier-diagonalize the product
variable, Dirichlet approximation on `𝕋 ∖ 𝔐` (mem:dirichlet-minor) and the Gram bound
(mem:bilinear-gram) give `L^{0.2-A₀} + Y^{-0.1} log Y`; `A₀` independent of `K`. -/
theorem lattice_clean (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ (K : ℕ) (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.clean j)
                (Real.rpow S.L (-G)) := by
  sorry

/-- `t2:pd.dirty-raw` — PD 04:605-714.  REPLACES the frozen `dirty_raw`.  With
`ε_K = C_K(B/M_J^K + B^K e^{-cL^{0.1}})`: every raw piece with `(St,Pr) ≠ (∅,∅)` has weighted row
sum `≤ ε_K` if `Pr ≠ ∅` (one compatible omission tuple by test (ii), mass `M_J^{-K}`,
(mem:anchor-congruence)) and `≤ C_K` otherwise, column sum `≤ ε_K` if `St ≠ ∅` and `≤ C_K`
otherwise (reversal); weighted Schur gives `‖dirty raw‖ ≤ C_K √ε_K ≤ C_K L^{1-K/200}` for large
`x` (mem:raw-dirty-norm).  Stated for `K ≥ 201`, where `ε_K ≤ 1` eventually. -/
theorem dirty_raw (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ), 201 ≤ K → ∀ (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K c x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < c ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
            let B := memoryCutoff S
            let εK := C_K * ((B : ℝ) / (S.M : ℝ) ^ K +
              (B : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)))
            (∀ St Pr : Finset (Fin K), ¬ (St = ∅ ∧ Pr = ∅) →
              MemRowSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if Pr.Nonempty then εK else C_K) ∧
                MemColSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if St.Nonempty then εK else C_K)) ∧
            MemOpNormLE F S B (memEdge F S ρ w EdgeKind.dirtyRaw j)
              (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := by
  sorry

/-- `t2:pd.dirty-comparison` — PD 04:716-770.  REPLACES the frozen `dirty_comparison`.
Comparison pieces with `(St,Pr) ≠ (∅,∅)`: a promoted index needs one prescribed line at the
target, one nonzero linear congruence in the lattice box (mem:line-count), row sum
`ζ_K = C_K L^{3A₀} B^K (p_min^{-1} + Y^{-0.1}) = O_A(L^{-A})`; the opposite side is `≤ L^C`
(mem:edge-crude); weighted Schur gives every fixed negative power of `L`. -/
theorem dirty_comparison (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
          MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyCmp j)
            (C_A * Real.rpow S.L (-A)) := by
  sorry

private theorem finite_weighted_schur_norm {α : Type*} [DecidableEq α]
    (μ v : α → ℝ) (k : α → α → ℂ) (f : α → ℂ) (T T' : Finset α) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hv : ∀ s, 0 < v s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ s ∈ T', ∑ t ∈ T, ‖k s t‖ * v t ≤ a * v s)
    (hcol : ∀ t ∈ T, ∑ s ∈ T', μ s * ‖k s t‖ * v s ≤ b * μ t * v t) :
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2) ≤
      a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
  classical
  have hpoint (s : α) :
      ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * v t) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t := by
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := T)
      (r := fun t => ‖k s t‖ * ‖f t‖)
      (f := fun t => ‖k s t‖ * v t)
      (g := fun t => ‖k s t‖ * ‖f t‖ ^ 2 / v t)
      (fun t ht => mul_nonneg (norm_nonneg _) (hv t).le)
      (fun t ht => div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le)
      (fun t ht => by
        have hvt := hv t
        have heq : (‖k s t‖ * ‖f t‖) ^ 2 =
            (‖k s t‖ * v t) * (‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          field_simp [hvt.ne']
        exact heq.le)
    have htri :
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by
      calc
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t * f t‖ := norm_sum_le _ _
        _ = ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by simp [norm_mul]
    have hsumNonneg : 0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ :=
      Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr htri)
        (add_nonneg (norm_nonneg (∑ t ∈ T, k s t * f t)) hsumNonneg)
      nlinarith [hprod]
    exact hsq.trans hCS
  have hinnerNonneg (s : α) :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t :=
    Finset.sum_nonneg fun t ht =>
      div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le
  have hrowAll (s : α) (hs : s ∈ T') :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * v t :=
    Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (hv t).le
  have hswap :
      (∑ s ∈ T', μ s * v s *
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) =
        ∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro s hs
    ring
  calc
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2)
        ≤ ∑ s ∈ T', μ s *
          ((∑ t ∈ T, ‖k s t‖ * v t) *
            ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ ≤ ∑ s ∈ T', μ s * ((a * v s) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hrow s hs) (hinnerNonneg s)) (hμ s)
    _ = a * (∑ s ∈ T', μ s * v s *
          (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    _ = a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s)) := by rw [hswap]
    _ ≤ a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) * (b * μ t * v t)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left (hcol t ht)
              (div_nonneg (sq_nonneg _) (hv t).le)
          · exact ha
    _ = a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hvt := hv t
          field_simp [hvt.ne']

private theorem memOpNormLE_fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (ops : ι → (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ι → ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (hc : ∀ i, 0 ≤ c i)
    (hops : ∀ i, MemOpNormLE F S B (ops i) (c i)) :
    MemOpNormLE F S B (fun f s => ∑ i, ops i f s)
      (Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2)) := by
  classical
  intro T T' f hsupp hT hT'
  have hpoint (s : MemPoint S.x K) :
      ‖∑ i, ops i f s‖ ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2 := by
    have htri : ‖∑ i, ops i f s‖ ≤ ∑ i, ‖ops i f s‖ := norm_sum_le _ _
    have hnonneg : 0 ≤ ∑ i, ‖ops i f s‖ := Finset.sum_nonneg fun i hi => norm_nonneg _
    have hcs : (∑ i, ‖ops i f s‖) ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2 := by
      simpa using (_root_.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := fun i => ‖ops i f s‖))
    have hprod := mul_nonneg (sub_nonneg.mpr htri)
      (add_nonneg (norm_nonneg (∑ i, ops i f s)) hnonneg)
    nlinarith [hprod, hcs]
  have hOp (i : ι) := hops i T T' f hsupp hT hT'
  have hsumOp :
      (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) ≤
        (∑ i, c i ^ 2) * memNormSqOn F S T f := by
    calc
      (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) ≤
          ∑ i, c i ^ 2 * memNormSqOn F S T f := by
            apply Finset.sum_le_sum
            intro i hi
            exact hOp i
      _ = (∑ i, c i ^ 2) * memNormSqOn F S T f := by
            rw [← Finset.sum_mul]
  unfold memNormSqOn
  calc
    (∑ s ∈ T', memMeasure F S s * ‖∑ i, ops i f s‖ ^ 2) ≤
        ∑ s ∈ T', memMeasure F S s *
          ((Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro s hs
            exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ = (Fintype.card ι : ℝ) *
          (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro s hs
            ring
    _ ≤ (Fintype.card ι : ℝ) *
          ((∑ i, c i ^ 2) * (∑ s ∈ T, memMeasure F S s * ‖f s‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hsumOp (by positivity)
    _ = (Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2)) ^ 2 *
          (∑ s ∈ T, memMeasure F S s * ‖f s‖ ^ 2) := by
            rw [Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card ι : ℝ) * ∑ i, c i ^ 2)]
            ring

private theorem memOpNormLE_add_sub {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (A D E : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (a d e : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hA : MemOpNormLE F S B A a) (hD : MemOpNormLE F S B D d)
    (hE : MemOpNormLE F S B E e) :
    MemOpNormLE F S B (fun f s => A f s + D f s - E f s)
      (Real.sqrt (3 * (a ^ 2 + d ^ 2 + e ^ 2))) := by
  classical
  intro T T' f hsupp hT hT'
  have hA' := hA T T' f hsupp hT hT'
  have hD' := hD T T' f hsupp hT hT'
  have hE' := hE T T' f hsupp hT hT'
  have hpoint (s : MemPoint S.x K) :
      ‖A f s + D f s - E f s‖ ^ 2 ≤
        3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2) := by
    have htriangle : ‖A f s + D f s - E f s‖ ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ := by
      calc
        ‖A f s + D f s - E f s‖ ≤ ‖A f s + D f s‖ + ‖E f s‖ := norm_sub_le _ _
        _ ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ := by gcongr; exact norm_add_le _ _
    have ha : 0 ≤ ‖A f s‖ := norm_nonneg _
    have hd : 0 ≤ ‖D f s‖ := norm_nonneg _
    have he : 0 ≤ ‖E f s‖ := norm_nonneg _
    have hdiff : 0 ≤ (‖A f s‖ + ‖D f s‖ + ‖E f s‖) - ‖A f s + D f s - E f s‖ := by
      linarith [htriangle]
    have hsum : 0 ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ + ‖A f s + D f s - E f s‖ := by
      positivity
    have hsq : ‖A f s + D f s - E f s‖ ^ 2 ≤
        (‖A f s‖ + ‖D f s‖ + ‖E f s‖) ^ 2 := by
      nlinarith [mul_nonneg hdiff hsum]
    nlinarith [hsq, sq_nonneg (‖A f s‖ - ‖D f s‖),
      sq_nonneg (‖A f s‖ - ‖E f s‖), sq_nonneg (‖D f s‖ - ‖E f s‖)]
  have hsum :
      (∑ s ∈ T', memMeasure F S s * ‖A f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖D f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖E f s‖ ^ 2) ≤
        (a ^ 2 + d ^ 2 + e ^ 2) * memNormSqOn F S T f := by
    unfold memNormSqOn at hA' hD' hE' ⊢
    linarith
  unfold memNormSqOn
  calc
    (∑ s ∈ T', memMeasure F S s * ‖A f s + D f s - E f s‖ ^ 2) ≤
        ∑ s ∈ T', memMeasure F S s *
          (3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ = 3 * ((∑ s ∈ T', memMeasure F S s * ‖A f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖D f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖E f s‖ ^ 2)) := by
      rw [show (fun s => memMeasure F S s *
            (3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2))) =
          (fun s => 3 * (memMeasure F S s * ‖A f s‖ ^ 2) +
            (3 * (memMeasure F S s * ‖D f s‖ ^ 2) +
              3 * (memMeasure F S s * ‖E f s‖ ^ 2))) by
        funext s
        ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ 3 * ((a ^ 2 + d ^ 2 + e ^ 2) * memNormSqOn F S T f) := by
      nlinarith [hsum]
    _ = (Real.sqrt (3 * (a ^ 2 + d ^ 2 + e ^ 2))) ^ 2 * memNormSqOn F S T f := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 3 * (a ^ 2 + d ^ 2 + e ^ 2))]
      ring

private theorem sum_sum_split_empty {γ : Type*} [Fintype γ] [DecidableEq γ]
    (f : Finset γ → Finset γ → ℂ) :
    (∑ x : Finset γ, ∑ y : Finset γ, f x y) = f ∅ ∅ +
      ∑ x : Finset γ, ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y := by
  classical
  let U : Finset (Finset γ) := Finset.univ
  have hempty : (∅ : Finset γ) ∈ U := by simp [U]
  have hraw0 : (∑ y : Finset γ, f ∅ y) = f ∅ ∅ +
      ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U (fun y => f ∅ y) hempty, add_comm]
  have hdirty0 : (∑ y : Finset γ, if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) =
      ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U
      (fun y => if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) hempty]
    have hErase : (∑ y ∈ U.erase ∅,
        if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) =
        ∑ y ∈ U.erase ∅, f ∅ y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyne : y ≠ ∅ := (Finset.mem_erase.mp hy).1
      simp [hyne]
    rw [hErase]
    simp only [true_and, ite_true, add_zero]
  have hoff (x : Finset γ) (hx : x ∈ U.erase ∅) :
      (∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) =
        ∑ y : Finset γ, f x y := by
    have hxne : x ≠ ∅ := (Finset.mem_erase.mp hx).1
    simp [hxne]
  have hraw : (∑ x : Finset γ, ∑ y : Finset γ, f x y) =
      f ∅ ∅ + (∑ x ∈ U.erase ∅, ∑ y : Finset γ, f x y) +
        ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U (fun x => ∑ y : Finset γ, f x y) hempty, hraw0]
    ring
  have hdirty : (∑ x : Finset γ,
      ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) =
      (∑ x ∈ U.erase ∅, ∑ y : Finset γ, f x y) +
        ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U
      (fun x => ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) hempty]
    rw [Finset.sum_congr rfl (fun x hx => hoff x hx), hdirty0]
  rw [hraw, hdirty]
  ring

private theorem memEdge_full_eq_clean_add_dirty {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (f : MemPoint S.x K → ℂ) :
    memEdge F S ρ w EdgeKind.full j f =
      memEdge F S ρ w EdgeKind.clean j f + memEdge F S ρ w EdgeKind.dirtyRaw j f -
        memEdge F S ρ w EdgeKind.dirtyCmp j f := by
  classical
  funext s
  simp only [memEdge, plainOp, logEdge, logSym]
  dsimp [plainOp, logEdge, logSym]
  simp_rw [Finset.sum_sub_distrib]
  have hraw (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :=
    sum_sum_split_empty (fun St Pr =>
      logEdgePiece F S ρ w j true St Pr (logSym F S fun σL => f σL.1)
        ((s.1, permuteLists σ s.2.1, s.2.2), []))
  have hcmp (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :=
    sum_sum_split_empty (fun St Pr =>
      logEdgePiece F S ρ w j false St Pr (logSym F S fun σL => f σL.1)
        ((s.1, permuteLists σ s.2.1, s.2.2), []))
  simp_rw [hraw, hcmp, Finset.sum_add_distrib]
  ring_nf

private theorem memEdge_dirtyRaw_eq_piece_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    memEdge F S ρ w EdgeKind.dirtyRaw j =
      (fun f s => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (if St = ∅ ∧ Pr = ∅ then 0 else
          memEdgePiece F S ρ w true St Pr j f s)) := by
  funext f s
  simp only [memEdge, plainOp, logEdge, memEdgePiece]
  dsimp [logSym]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro St hSt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Pr hPr
  by_cases hempty : St = ∅ ∧ Pr = ∅ <;> simp [hempty]

private theorem memEdge_dirtyCmp_eq_piece_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    memEdge F S ρ w EdgeKind.dirtyCmp j =
      (fun f s => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (if St = ∅ ∧ Pr = ∅ then 0 else
          memEdgePiece F S ρ w false St Pr j f s)) := by
  funext f s
  simp only [memEdge, plainOp, logEdge, memEdgePiece]
  dsimp [logSym]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro St hSt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Pr hPr
  by_cases hempty : St = ∅ ∧ Pr = ∅ <;> simp [hempty]

private theorem memMeasure_eq_zero_of_nonprimitive {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (h : Int.gcd s.1.1 s.1.2 ≠ 1) :
    memMeasure F S s = 0 := by
  have hv : ¬ MemValid F S s := by
    intro hs
    exact h hs.1
  simp [memMeasure, hv]

private theorem memOpNormLE_zero_from_null_source {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℕ) (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ℝ)
    (hOp : MemOpNormLE F S B op c) (s t : MemPoint S.x K)
    (hs : memSize s ≤ B) (ht : memSize t ≤ B)
    (hμs : memMeasure F S s = 0) (hμt : 0 < memMeasure F S t) :
    op (fun u => if u = s then 1 else 0) t = 0 := by
  have hsupport : ∀ u, u ∉ ({s} : Finset (MemPoint S.x K)) →
      (if u = s then (1 : ℂ) else 0) = 0 := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    simp [hu]
  have hT : ∀ u ∈ ({s} : Finset (MemPoint S.x K)), memSize u ≤ B := by
    intro u hu
    simpa [Finset.mem_singleton.mp hu] using hs
  have hT' : ∀ u ∈ ({t} : Finset (MemPoint S.x K)), memSize u ≤ B := by
    intro u hu
    simpa [Finset.mem_singleton.mp hu] using ht
  have h := hOp {s} {t} (fun u => if u = s then 1 else 0) hsupport hT hT'
  simp [memNormSqOn, hμs] at h
  have hnonneg : 0 ≤ memMeasure F S t *
      ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 :=
    mul_nonneg hμt.le (sq_nonneg _)
  have hzero : memMeasure F S t *
      ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 = 0 := le_antisymm h hnonneg
  have hnormsq : ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hμt0 | hnormsq
    · exact (hμt.ne' hμt0).elim
    · exact hnormsq
  have hnorm : ‖op (fun u => if u = s then 1 else 0) t‖ = 0 := by
    nlinarith [sq_nonneg (‖op (fun u => if u = s then 1 else 0) t‖)]
  exact norm_eq_zero.mp hnorm

private theorem memMeasure_nonneg_for_large {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x →
      ∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s := by
  classical
  have hBands : ValidBands K F.a := hF.1
  have hbandExist : ∀ i : Fin K,
      ∃ xᵢ : ℝ, 2 ≤ xᵢ ∧ ∀ x : ℝ, xᵢ ≤ x → 0 < bandMass x (F.a i) := by
    intro i
    have ha₀ : 0 < F.a i := by
      have := hBands.2.1 i
      linarith
    have ha₁ : F.a i < 1 := by
      have := hBands.2.1 i
      linarith
    have hε : 0 < Real.log 2 / 2 := by positivity
    obtain ⟨xᵢ, hxᵢ, hmass⟩ := band_mass (F.a i) ha₀ ha₁ (Real.log 2 / 2) hε
    exact ⟨xᵢ, hxᵢ, fun x hx => (hmass x hx).2⟩
  choose xBand hxBand using hbandExist
  have hK : 0 < K := hBands.1
  let i₀ : Fin K := ⟨0, hK⟩
  have hU : (Finset.univ : Finset (Fin K)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  let xBandMax : ℝ := Finset.univ.sup' hU xBand
  have hxBandMax (i : Fin K) : xBand i ≤ xBandMax :=
    Finset.le_sup' (f := xBand) (Finset.mem_univ i)
  have hxBandMax₂ : 2 ≤ xBandMax := by
    exact le_trans (hxBand i₀).1 (hxBandMax i₀)
  have hratioEv : ∀ᶠ t : ℝ in Filter.atTop, 2 < Real.exp t / t ^ 5 :=
    (Real.tendsto_exp_div_pow_atTop 5).eventually_gt_atTop 2
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 hratioEv
  let T : ℝ := max t₀ 3
  have hT3 : 3 ≤ T := le_max_right _ _
  have hTt₀ : t₀ ≤ T := le_max_left _ _
  let x₀ : ℝ := max xBandMax (Real.exp (T ^ 10))
  refine ⟨x₀, le_trans hxBandMax₂ (le_max_left _ _), ?_⟩
  intro S hx₀ s
  have hxBandS : xBandMax ≤ S.x := le_trans (le_max_left _ _) hx₀
  have hxExp : Real.exp (T ^ 10) ≤ S.x := le_trans (le_max_right _ _) hx₀
  let L : ℝ := Real.log S.x
  have hlog : T ^ 10 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos (T ^ 10)) hxExp
    simpa [L] using h
  have hLpos : 0 < L := by
    have : 0 < T ^ 10 := by positivity
    dsimp [L]
    exact lt_of_lt_of_le this hlog
  have hLone : 1 ≤ L := by
    have hT : (1 : ℝ) ≤ T := by linarith
    have hTpow : (1 : ℝ) ≤ T ^ 10 := one_le_pow₀ hT
    exact hTpow.trans hlog
  let t : ℝ := Real.rpow L (1 / 10 : ℝ)
  have hTle : T ≤ t := by
    calc
      T = Real.rpow (T ^ 10) (1 / 10 : ℝ) := by
        simpa [div_eq_mul_inv] using
          (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ T) (by norm_num : 10 ≠ 0)).symm
      _ ≤ Real.rpow L (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hlog (by norm_num)
  have ht₀t : t₀ ≤ t := hTt₀.trans hTle
  have hratio : 2 < Real.exp t / t ^ 5 := ht₀ t ht₀t
  have htpos : 0 < t := by dsimp [t]; positivity
  have hpowPos : 0 < t ^ 5 := pow_pos htpos _
  have hExpT : 2 * t ^ 5 < Real.exp t := (lt_div_iff₀ hpowPos).mp hratio
  have ht₃ : 3 ≤ t := hT3.trans hTle
  have hpowLower : (3 : ℝ) ^ 5 ≤ t ^ 5 := by gcongr
  have ht5 : t ^ 5 = Real.rpow L (1 / 2 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLpos)]
    norm_num
  have hpath : (pathLength S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := by
    have hceil : (momentR S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) / 2 + 1 := by
      dsimp [momentR]
      exact Nat.ceil_lt_add_one (by positivity)
    have hceil2 := mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 2)
    dsimp [pathLength]
    push_cast
    calc
      2 * (momentR S.x : ℝ) < 2 * (Real.rpow L (1 / 2 : ℝ) / 2 + 1) := hceil2
      _ = Real.rpow L (1 / 2 : ℝ) + 2 := by ring
  have hpathExp : (pathLength S.x : ℝ) < Real.exp t := by
    calc
      (pathLength S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := hpath
      _ = t ^ 5 + 2 := by rw [ht5]
      _ ≤ 2 * t ^ 5 := by nlinarith [hpowLower]
      _ < Real.exp t := hExpT
  have hprimeLarge : ∀ i : Fin K, ∀ p : ℕ, p ∈ primeBand S.x (F.a i) →
      (pathLength S.x : ℝ) < (p : ℝ) := by
    intro i p hp
    have ha : (1 / 10 : ℝ) ≤ F.a i := (hBands.2.1 i).1.le
    have hLp : Real.rpow L (1 / 10 : ℝ) ≤ Real.rpow L (F.a i) :=
      Real.rpow_le_rpow_of_exponent_le hLone ha
    have hExpMono : Real.exp t ≤ Real.exp (Real.rpow L (F.a i)) :=
      Real.exp_le_exp.mpr hLp
    have hpLower : Real.exp (Real.rpow L (F.a i)) ≤ (p : ℝ) :=
      (Finset.mem_filter.mp hp).2.2.1
    exact lt_of_lt_of_le hpathExp (hExpMono.trans hpLower)
  have hmass (i : Fin K) : 0 < bandMass S.x (F.a i) :=
    (hxBand i).2 S.x (le_trans (hxBandMax i) hxBandS)
  have heta (j : ℕ) : memoryEta S.x F.q_d j ≤ 1 := by
    have hqd : 0 < F.q_d := hF.2.1
    have hq : 0 ≤ memoryQ S.x F.q_d j := by
      unfold memoryQ
      split_ifs <;> positivity
    unfold memoryEta
    linarith
  have hnu (i : Fin K) (p : ℕ) (hp : p ∈ primeBand S.x (F.a i)) :
      0 < memoryNu S.x K F.a F.q_d i p := by
    have hpPath : (pathLength S.x : ℝ) < (p : ℝ) := hprimeLarge i p hp
    have hpden : 0 < (p : ℝ) + 1 := by positivity
    have hcount : ((pathLength S.x + 1 : ℕ) : ℝ) < (p : ℝ) + 1 := by
      have h := add_lt_add_right hpPath 1
      simpa [Nat.cast_add] using h
    have hquot : ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) < 1 :=
      (div_lt_one hpden).2 hcount
    have hsum : (∑ j ∈ Finset.range (pathLength S.x + 1),
        memoryEta S.x F.q_d j / ((p : ℝ) + 1)) < 1 := by
      calc
        _ ≤ ∑ j ∈ Finset.range (pathLength S.x + 1), 1 / ((p : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro j hj
          exact div_le_div_of_nonneg_right (heta j) hpden.le
        _ = ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
          simp [Finset.sum_const, Finset.card_range]
          ring
        _ < 1 := hquot
    have hbprime : 0 < memoryBPrime S.x F.q_d p := by
      unfold memoryBPrime
      linarith
    have hmassPos : 0 < bandMass S.x (F.a i) := hmass i
    unfold memoryNu
    positivity
  by_cases hs : MemValid F S s
  · unfold memMeasure
    rw [if_pos hs]
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      apply Finset.prod_nonneg
      intro j hj
      exact (hnu i (s.2.1 i j) (hs.2.1 i j)).le
    · apply Finset.prod_nonneg
      intro i hi
      apply div_nonneg
      · apply List.prod_nonneg
        intro e he
        rcases List.mem_map.mp he with ⟨e', he', rfl⟩
        exact (hnu i e'.1 (hs.2.2 i e' he').1).le
      · positivity
  · simp [memMeasure, hs]

private theorem memNormSqOn_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) :
    0 ≤ memNormSqOn F S T f := by
  classical
  unfold memNormSqOn
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (hμ s) (sq_nonneg _)

private theorem memOpNormLE_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c d : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (h : MemOpNormLE F S B op c)
    (hc : 0 ≤ c) (hcd : c ≤ d) : MemOpNormLE F S B op d := by
  intro T T' f hsupp hT hT'
  have hinput : 0 ≤ memNormSqOn F S T f := memNormSqOn_nonneg F S T f hμ
  have hsq : c ^ 2 ≤ d ^ 2 := by nlinarith
  have hopen := h T T' f hsupp hT hT'
  nlinarith

/-- `t2:pd.signed-edge` (new assembly node) — PD 04:772-782 (mem:signed-edge).  Choose `A₀`
from `lattice_clean` for `G+1`, then `K₀` with `K₀/200 > G+2`: `‖ℰ_j‖_{ℋ_B} ≤ L^{-G}`
(`ℰ_j = clean + dirtyRaw - dirtyCmp` by definition). -/
theorem signed_edge (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G)) := by
  intro G hG
  have hG3 : 0 < G + 3 := by linarith
  obtain ⟨A₀, hA₀, hCleanAll⟩ := lattice_clean δ c₁ c₂ hδ hc₁ q_d eta psi (G + 3) hG3
  let K₀ : ℕ := max 201 ⌈200 * (G + 4)⌉₊
  have hK₀ : 201 ≤ K₀ := le_max_left _ _
  have hKceil : (⌈200 * (G + 4)⌉₊ : ℝ) ≤ K₀ := by
    exact_mod_cast (le_max_right 201 ⌈200 * (G + 4)⌉₊)
  have hceil : 200 * (G + 4) ≤ (⌈200 * (G + 4)⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨A₀, hA₀, K₀, ?_⟩
  intro K hK F hF hHas ρ hρ
  have hKcast : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
  have hKlower : 200 * (G + 4) ≤ (K : ℝ) := le_trans hceil (le_trans hKceil hKcast)
  have hExponent : 1 - (K : ℝ) / 200 ≤ -(G + 3) := by
    have hKlower' : (G + 4) * 200 ≤ (K : ℝ) := by simpa [mul_comm] using hKlower
    have hdiv : G + 4 ≤ (K : ℝ) / 200 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 200)).2 hKlower'
    linarith
  obtain ⟨v₀, C_K, c, xRaw, hv₀, hC_K, hc, hxRaw, hRawAll⟩ :=
    dirty_raw δ c₁ c₂ hδ hc₁ K (le_trans hK₀ hK) F hF ρ hρ
  obtain ⟨Ccmp, xCmp, hCcmp, hxCmp, hCmpAll⟩ :=
    dirty_comparison δ c₁ c₂ hδ hc₁ K F hF ρ hρ (G + 3) hG3
  obtain ⟨xClean, hxClean, hClean⟩ := hCleanAll K F hF hHas ρ hρ
  obtain ⟨xMeasure, hxMeasure, hMeasure⟩ := memMeasure_nonneg_for_large F hF
  let xLarge : ℝ := 3 * (1 + C_K + Ccmp)
  let x₀ : ℝ := max xClean (max xRaw (max xCmp (max xMeasure (Real.exp xLarge))))
  have hx₀₂ : 2 ≤ x₀ := le_trans hxClean (le_max_left _ _)
  refine ⟨x₀, hx₀₂, ?_⟩
  intro S hS hx₀ w hw j hj
  have hxClean₀ : xClean ≤ x₀ := le_max_left _ _
  have hxRaw₀ : xRaw ≤ x₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hxCmp₀ : xCmp ≤ x₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxMeasure₀ : xMeasure ≤ x₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hxExp₀ : Real.exp xLarge ≤ x₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hμ : ∀ s, 0 ≤ memMeasure F S s := hMeasure S (le_trans hxMeasure₀ hx₀)
  have hLlarge : xLarge ≤ S.L := by
    have hexp : Real.exp xLarge ≤ S.x := le_trans hxExp₀ hx₀
    have hlog := Real.log_le_log (Real.exp_pos xLarge) hexp
    simpa [PDScale.L] using hlog
  have hxLarge3 : 3 ≤ xLarge := by
    dsimp [xLarge]
    nlinarith [hC_K, hCcmp]
  have hLone : 1 ≤ S.L := le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_trans hxLarge3 hLlarge)
  have hLpos : 0 < S.L := lt_of_lt_of_le zero_lt_one hLone
  have hLcube : S.L ≤ S.L ^ 3 := by
    calc
      S.L = S.L * 1 := by ring
      _ ≤ S.L * S.L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hLone) hLpos.le
      _ = S.L ^ 3 := by ring
  have hThreeCK : 3 * C_K ≤ S.L := by
    have : 3 * C_K ≤ xLarge := by dsimp [xLarge]; nlinarith [hCcmp]
    exact this.trans hLlarge
  have hThreeCmp : 3 * Ccmp ≤ S.L := by
    have : 3 * Ccmp ≤ xLarge := by dsimp [xLarge]; nlinarith [hC_K]
    exact this.trans hLlarge
  have hThree : 3 ≤ S.L := by
    have : (3 : ℝ) ≤ xLarge := hxLarge3
    exact this.trans hLlarge
  have hCoefOne : 1 ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThree]
  have hCoefRaw : C_K ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThreeCK]
  have hCoefCmp : Ccmp ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThreeCmp]
  have hfac : Real.rpow S.L (-G) = Real.rpow S.L (-(G + 3)) * S.L ^ 3 := by
    calc
      Real.rpow S.L (-G) = Real.rpow S.L (-(G + 3) + 3) := by congr 1 <;> ring
      _ = Real.rpow S.L (-(G + 3)) * Real.rpow S.L 3 := Real.rpow_add hLpos _ _
      _ = Real.rpow S.L (-(G + 3)) * Real.rpow S.L ((3 : ℕ) : ℝ) := by norm_num
      _ = Real.rpow S.L (-(G + 3)) * S.L ^ 3 := by
        exact congrArg (fun q : ℝ => Real.rpow S.L (-(G + 3)) * q)
          (Real.rpow_natCast S.L (3 : ℕ))
  have hthird (C : ℝ) (hC : 0 ≤ C) (hCoef : C ≤ S.L ^ 3 / 3) :
      C * Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 := by
    have hr : 0 < Real.rpow S.L (-(G + 3)) := Real.rpow_pos_of_pos hLpos _
    rw [hfac]
    calc
      C * Real.rpow S.L (-(G + 3)) ≤ (S.L ^ 3 / 3) * Real.rpow S.L (-(G + 3)) :=
        mul_le_mul_of_nonneg_right hCoef hr.le
      _ = (Real.rpow S.L (-(G + 3)) * S.L ^ 3) / 3 := by ring
  have hOneThird : Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 := by
    simpa using hthird 1 (by norm_num) hCoefOne
  have hRawData := hRawAll S hS (le_trans hxRaw₀ hx₀) w hw j hj
  have hRawOld : MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyRaw j)
      (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := hRawData.2
  have hRawCoeffPos : 0 ≤ C_K * Real.rpow S.L (1 - (K : ℝ) / 200) :=
    mul_nonneg hC_K.le (Real.rpow_pos_of_pos hLpos _).le
  have hRpow : Real.rpow S.L (1 - (K : ℝ) / 200) ≤ Real.rpow S.L (-(G + 3)) :=
    Real.rpow_le_rpow_of_exponent_le hLone hExponent
  have hRawCoeff : C_K * Real.rpow S.L (1 - (K : ℝ) / 200) ≤
      C_K * Real.rpow S.L (-(G + 3)) := mul_le_mul_of_nonneg_left hRpow hC_K.le
  have hRawCoeffThird : C_K * Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 :=
    hthird C_K hC_K.le hCoefRaw
  have hCleanOp := hClean S hS (le_trans hxClean₀ hx₀) w hw j hj
  have hCleanOp' := memOpNormLE_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.clean j) (Real.rpow S.L (-(G + 3)))
    (Real.rpow S.L (-G) / 3) hμ hCleanOp
    (Real.rpow_pos_of_pos hLpos _).le hOneThird
  have hRawOp' := memOpNormLE_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyRaw j)
    (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) (C_K * Real.rpow S.L (-(G + 3)))
    hμ hRawOld hRawCoeffPos hRawCoeff
  have hRawOp'' := memOpNormLE_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyRaw j) (C_K * Real.rpow S.L (-(G + 3)))
    (Real.rpow S.L (-G) / 3) hμ hRawOp'
    (mul_nonneg hC_K.le (Real.rpow_pos_of_pos hLpos _).le) hRawCoeffThird
  have hCmpData := hCmpAll S hS (le_trans hxCmp₀ hx₀) w hw j hj
  have hCmpOp := memOpNormLE_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyCmp j)
    (Ccmp * Real.rpow S.L (-(G + 3))) (Real.rpow S.L (-G) / 3) hμ hCmpData
    (mul_nonneg hCcmp.le (Real.rpow_pos_of_pos hLpos _).le)
    (hthird Ccmp hCcmp.le hCoefCmp)
  have hArg : 3 * ((Real.rpow S.L (-G) / 3) ^ 2 +
      (Real.rpow S.L (-G) / 3) ^ 2 + (Real.rpow S.L (-G) / 3) ^ 2) =
      (Real.rpow S.L (-G)) ^ 2 := by ring
  have hRnonneg : 0 ≤ Real.rpow S.L (-G) := (Real.rpow_pos_of_pos hLpos _).le
  have hConst : Real.sqrt (3 * ((Real.rpow S.L (-G) / 3) ^ 2 +
      (Real.rpow S.L (-G) / 3) ^ 2 + (Real.rpow S.L (-G) / 3) ^ 2)) =
      Real.rpow S.L (-G) := by
    rw [hArg, Real.sqrt_sq_eq_abs, abs_of_nonneg hRnonneg]
  have hTriangle := memOpNormLE_add_sub F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.clean j) (memEdge F S ρ w EdgeKind.dirtyRaw j)
    (memEdge F S ρ w EdgeKind.dirtyCmp j) (Real.rpow S.L (-G) / 3)
    (Real.rpow S.L (-G) / 3) (Real.rpow S.L (-G) / 3) hμ hCleanOp' hRawOp'' hCmpOp
  rw [hConst] at hTriangle
  have hEdge : memEdge F S ρ w EdgeKind.full j =
      (fun f s => memEdge F S ρ w EdgeKind.clean j f s +
        memEdge F S ρ w EdgeKind.dirtyRaw j f s - memEdge F S ρ w EdgeKind.dirtyCmp j f s) := by
    funext f s
    exact congrFun (memEdge_full_eq_clean_add_dirty F S ρ w j f) s
  rw [hEdge]
  exact hTriangle

/-- `t2:pd.birth-partition` (new node, general) — PD 04:807-823 (mem:partition-identity).  For a
log whose addresses are distinct and lie in `A`, the distinctness weight is the signed sum of the
constraint weights: `Σ_π sgn π` over value-preserving permutations of the performed addresses,
grouped by nontrivial cycles (`(|C|-1)!` cyclic orders of sign `(-1)^{|C|-1}` on each block). -/
theorem birth_partition {K : ℕ} (A : Finset (BirthAddress K)) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) (hA : ∀ e ∈ log, e.1 ∈ A) :
    distinctWeight log =
      ∑ 𝒞 ∈ constraintSystems A, (constraintCoeff 𝒞 : ℂ) * constraintWeight 𝒞 log := by
  sorry

/-- `t2:pd.history-rank-high` (new node) — PD 04:825-904.  High-rank constraint systems are
negligible in absolute value: with `r₀ = ⌈C' N log L / L^{0.1}⌉` (`C'` large after the crude
exponent), `Σ_{r(𝒞) ≥ r₀} |coef 𝒞| · |H_𝒞| ≤ L^{-(E₀+3)N}`, where `H_𝒞` is the truncated history
with final weight `constraintWeight 𝒞`.  Proof: coefficient mass `Q_birth^{2r}` (mem:rank-coefficients);
a fixed system costs `L^{C(N+1)} (C_K e^{-L^{0.1}})^r` by chronological conditioning on pivots, an
atom `Δ ≤ C_K e^{-L^{0.1}}` per nonpivot birth (mem:edge-atoms), (mem:ghost-atoms); geometric
series (mem:high-rank). -/
theorem history_rank_high (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ E₀ : ℝ, 0 < E₀ →
      ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          (∑ 𝒞 ∈ (constraintSystems (birthAddresses S.x K (memoryCutoff S))).filter
              (fun 𝒞 => (⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊ ≤
                constraintRank 𝒞)),
            |(constraintCoeff 𝒞 : ℝ)| *
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖) ≤
            Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
  sorry

/-- `t2:pd.history-rank-low` (new node) — PD 04:906-956.  A constraint system of rank `r` changes at
most `2r` operations: write each block indicator by circle orthogonality (mem:local-phases), attach
every phase at the operation where its prime is born (an equivariant multiplier of modulus `≤ 1`);
if every edge satisfies the signed bound `L^{-G}`, then
`|H_𝒞| ≤ C_K^{N+1} ‖𝐛‖² L^{-G(N-2r)} L^{2Cr}` (mem:low-rank-term) with the crude exponent `C` of
`ghost_edge_crude` and `‖𝐛‖² ≤ 2` (mem:boundary-norm). -/
theorem history_rank_low (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
          ∀ G : ℝ, 0 < G →
            (∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G))) →
            ∀ 𝒞 ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖ ≤
                2 * C_K ^ (S.N + 1) *
                  Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank 𝒞 : ℝ))) *
                  Real.rpow S.L (2 * Ccr * (constraintRank 𝒞 : ℝ)) := by
  sorry

/-- `t2:pd.birth-distinctness` — PD 04:784-966.  REPLACES the frozen `birth_distinctness`.
Assembly: the truncated distinct history is `≤ L^{-(E₀+2)N}` uniformly in the root.
`birth_partition` (logs of truncated histories have distinct addresses in `birthAddresses`),
`history_rank_high`, and `history_rank_low` with `signed_edge` for `G > E₀ + 3`; since
`r₀/N = O(log L / L^{0.1})`, the low ranks sum to `L^{(-G+o(1))N}` (mem:low-rank). -/
theorem birth_distinctness (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ)
    (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S →
              ‖historyDistinctTrunc F S ρ w‖ ≤ Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
  sorry

/-! ## §6 Removing goodness, stripping pads, Proposition 4.1 (PD 04:968-1117, 11-35) -/

/-- The scale of a coefficient family at `x` with selected-product scale `Y` and pad `d₀`. -/
def familyScale {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x Y : ℝ) (d₀ : ℕ) :
    PDScale := ⟨x, family.Hm x, family.Hn x, Y, d₀⟩

/-- `β` hypotheses at the family's second dyad. -/
def IsFamilySecondCoefficient {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    (beta : ℕ → ℂ) : Prop :=
  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧ roughAbove n (roughCutoff x)) ∧
    ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C

/-- `t2:pd.goodness-removal` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:970-1008.
Removing both good-state projections from the pairing costs `O_A(UV L^{-A})`: majorize the bad
parts absolutely with log-power endpoint suprema; single-edge root replacement (the general
sub-lemmas `root_lines`, `root_arch_boundary`, `root_bonferroni`); one-edge label mass
(mem:one-edge-label-mass) `≤ 1`; `O(1)` raw / `O(Y)` comparison targets; bad ratios of measure
`e^{-cL^{0.1}}` by `good_state`. -/
theorem goodness_removal (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ family : CoefficientFamily δ C c₁ c₂, FamilyAtScale family S →
          ∀ beta : ℕ → ℂ, IsSecondCoefficient S C beta →
            ‖detPairing F S family beta - detPairingNoGood F S family beta‖ ≤
              C_A * S.U * S.V * Real.rpow S.L (-A) := by
  sorry

/-- `t2:pd.pad-stripping` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:1010-1101.
Summed over pad dyads with weight `1/d₀`, the pairing without goodness is the coprime Cauchy
square minus the unrestricted major sum up to `O_A(XY L^{-A})`: pad measure identity
(mem:pad-measure) (pads are independent ordered harmonic draws, total mass one), raw part =
coprime pairs `(a,b)` (the cross-edge ban), pad collisions (mem:pad-collisions) against the
absolute squares (mem:raw-absolute-square), (mem:comparison-absolute-square), and restoration of
non-disjoint `(a,b)` in the comparison (mem:unshared-collisions). -/
theorem pad_stripping (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ‖(∑ d₀ ∈ padScales x K,
                ((d₀ : ℂ))⁻¹ * detPairingNoGood F (familyScale family x Y d₀) family beta) -
              ((coprimeCauchySquare x K F.a Y family beta F.eta : ℂ) -
                majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi)‖ ≤
              C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:pd.strip-goodness-pads` — PD 04:968-1117.  REPLACES the frozen `strip_goodness_pads`
(which asserted the replacement for every `K` and `A₀` without the pairing hypothesis).  From
pairing bounds at every pad dyad to the replacement of the Cauchy square: `goodness_removal`,
`pad_stripping`, and part (iii) of the frozen `cauchy_decomposition` (`Q_Y` vs `Q_Y^{cop}`);
`UV/d₀ = XY`. -/
theorem strip_goodness_pads (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ∀ E₀ Ce Cp : ℝ,
              (∀ d₀ ∈ padScales x K,
                ‖detPairing F (familyScale family x Y d₀) family beta‖ ≤
                  Cp * (familyScale family x Y d₀).U * (familyScale family x Y d₀).V *
                    Real.rpow (Real.log x) (-E₀ + Ce)) →
              ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                  majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                ((padScales x K).card : ℝ) * Cp * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-E₀ + Ce) +
                  C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `prop:minor-moment` (moment part) — PD 04:11-22, Proposition 4.1.  REPLACES the first
conjunct of the frozen `minor_moment`.  For every `E₀` choose `A₀`, then `K₀` (independent of the
band exponents): the determinant moment is `≤ L^{-E₀N}`.  Proof: `path_expansion`,
`root_replacement` (`A = E₀+1`), `memory_identity`, `truncation_adjoint`, `birth_distinctness`
with `ρ = q_d^{1/8}`, `0 ≤ b'_p ≤ 1`, root region of volume `15`. -/
theorem minor_moment (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          detMoment F S ≤ Real.rpow S.L (-E₀ * (S.N : ℝ)) := by
  sorry

/-- `prop:minor-moment` (replacement part, mem:replacement-interface) — PD 04:22-34.  REPLACES the
second conjunct of the frozen `minor_moment`.  For every `A` choose `E₀ > A + C_e + 3`, then
`A₀, K₀` from `minor_moment`: `|Q_Y - Q_Y^{maj}| ≪_A XY L^{-A}`.  Only the coefficient bounds of
the family enter (no long-coefficient hypothesis).  Proof: `minor_moment`,
`moment_to_pairing`, `strip_goodness_pads`, `#padScales ≪_K L^{0.21}`. -/
theorem minor_replacement (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ ≤ c₂) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ family : CoefficientFamily δ C c₁ c₂,
          ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ, IsFamilySecondCoefficient family x beta →
              ∀ Y ∈ dyadicScales x K,
                ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                    majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                  C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry


end

end ArtinPrimitiveRoots.TypeII.PD
