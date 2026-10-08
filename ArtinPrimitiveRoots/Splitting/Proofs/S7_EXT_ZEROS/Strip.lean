import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

open Set Complex Filter Asymptotics
open scoped Topology

noncomputable section
namespace ArtinPrimitiveRoots.Proofs.s7sol_zeros

/-- Polynomial boundary control propagates across a vertical strip of finite order. -/
theorem polynomial_bound_on_vertical_strip
    {f : ℂ → ℂ} {a b d M : ℝ} {m : ℕ}
    (hab : a < b) (hshift : 0 < a + d) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrowth : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖f z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ 2))
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ M * ‖z + (d : ℂ)‖ ^ m)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ M * ‖z + (d : ℂ)‖ ^ m) :
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ M * ‖z + (d : ℂ)‖ ^ m := by
  let S : Set ℂ := Complex.re ⁻¹' Ioo a b
  let q : ℂ → ℂ := fun z => f z / (z + (d : ℂ)) ^ m
  have hcl : closure S ⊆ Complex.re ⁻¹' Icc a b := by
    simpa only [S, closure_Ioo hab.ne] using
      Complex.continuous_re.closure_preimage_subset (Ioo a b)
  have hdennorm (z : ℂ) (hza : a ≤ z.re) : a + d ≤ ‖z + (d : ℂ)‖ := by
    calc
      a + d ≤ z.re + d := by linarith
      _ = (z + (d : ℂ)).re := by simp
      _ ≤ ‖z + (d : ℂ)‖ := Complex.re_le_norm _
  have hdenpos (z : ℂ) (hza : a ≤ z.re) : 0 < ‖z + (d : ℂ)‖ :=
    lt_of_lt_of_le hshift (hdennorm z hza)
  have hdenne (z : ℂ) (hza : a ≤ z.re) : z + (d : ℂ) ≠ 0 :=
    norm_pos_iff.mp (hdenpos z hza)
  have hqdiff : DiffContOnCl ℂ q S := by
    have hpoly : Differentiable ℂ (fun z : ℂ => (z + (d : ℂ)) ^ m) :=
      (differentiable_id.add (differentiable_const _)).pow m
    have hp : DiffContOnCl ℂ (fun z : ℂ => (z + (d : ℂ)) ^ m) S :=
      hpoly.diffContOnCl
    have hi := hp.inv (fun z hz => pow_ne_zero m (hdenne z (hcl hz).1))
    simpa only [q, smul_eq_mul, div_eq_mul_inv, Pi.inv_apply, mul_comm] using hi.smul hf
  obtain ⟨C, hC, hgrowth⟩ := hgrowth
  let c : ℝ := (Real.pi / (b - a)) / 2
  have hwidth : 0 < Real.pi / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hc : 0 < c := div_pos hwidth (by norm_num)
  have hclt : c < Real.pi / (b - a) := by dsimp [c]; linarith
  let A : ℝ := |a| + |b| + 1
  let K : ℝ := 2 / c ^ 2
  let B : ℝ := C * (2 * A ^ 2 + 2 * K)
  let k : ℝ := ((a + d) ^ m)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hTaylor (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ K * Real.exp (c * t) := by
    have htaylor := Real.pow_div_factorial_le_exp (c * t) (mul_nonneg hc.le ht) 2
    norm_num [Nat.factorial] at htaylor
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hc)).mp
    calc
      t ^ 2 * c ^ 2 = (c * t) ^ 2 := by ring
      _ ≤ 2 * Real.exp (c * t) := by nlinarith only [htaylor]
      _ = (K * Real.exp (c * t)) * c ^ 2 := by
        dsimp [K]
        field_simp [hc.ne']
  have hquad (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
      (‖z‖ + 1) ^ 2 ≤ (2 * A ^ 2 + 2 * K) * Real.exp (c * |z.im|) := by
    have hre : |z.re| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor
      · linarith [(abs_le.mp (le_refl |a|)).1, abs_nonneg b]
      · linarith [(abs_le.mp (le_refl |b|)).2, abs_nonneg a]
    have hn : ‖z‖ + 1 ≤ A + |z.im| := by
      dsimp [A]
      linarith [Complex.norm_le_abs_re_add_abs_im z]
    have hsq : (‖z‖ + 1) ^ 2 ≤ (A + |z.im|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hn 2
    have hOne : 1 ≤ Real.exp (c * |z.im|) := by
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (mul_nonneg hc.le (abs_nonneg z.im))
    have hconst : 2 * A ^ 2 ≤ (2 * A ^ 2) * Real.exp (c * |z.im|) := by
      calc
        2 * A ^ 2 = (2 * A ^ 2) * 1 := by ring
        _ ≤ (2 * A ^ 2) * Real.exp (c * |z.im|) :=
          mul_le_mul_of_nonneg_left hOne (by positivity)
    calc
      (‖z‖ + 1) ^ 2 ≤ (A + |z.im|) ^ 2 := hsq
      _ ≤ 2 * A ^ 2 + 2 * |z.im| ^ 2 := by nlinarith [sq_nonneg (A - |z.im|)]
      _ ≤ (2 * A ^ 2) * Real.exp (c * |z.im|) +
          2 * (K * Real.exp (c * |z.im|)) :=
        add_le_add hconst (mul_le_mul_of_nonneg_left (hTaylor _ (abs_nonneg _)) (by norm_num))
      _ = (2 * A ^ 2 + 2 * K) * Real.exp (c * |z.im|) := by ring
  have hfgrowth (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
      ‖f z‖ ≤ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine (hgrowth z hza hzb).trans (Real.exp_le_exp.mpr ?_)
    calc
      C * (‖z‖ + 1) ^ 2 ≤ C * ((2 * A ^ 2 + 2 * K) * Real.exp (c * |z.im|)) :=
        mul_le_mul_of_nonneg_left (hquad z hza hzb) hC.le
      _ = B * Real.exp (c * |z.im|) := by dsimp [B]; ring
  have hqgrowth (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
      ‖q z‖ ≤ k * Real.exp (B * Real.exp (c * |z.im|)) := by
    have hpow : (a + d) ^ m ≤ ‖z + (d : ℂ)‖ ^ m :=
      pow_le_pow_left₀ hshift.le (hdennorm z hza) m
    simp only [q, norm_div, norm_pow]
    calc
      ‖f z‖ / ‖z + (d : ℂ)‖ ^ m ≤ ‖f z‖ / (a + d) ^ m :=
        div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hshift m) hpow
      _ ≤ Real.exp (B * Real.exp (c * |z.im|)) / (a + d) ^ m :=
        div_le_div_of_nonneg_right (hfgrowth z hza hzb) (pow_pos hshift m).le
      _ = k * Real.exp (B * Real.exp (c * |z.im|)) := by dsimp [k]; ring
  have hBigO : ∃ c' < Real.pi / (b - a), ∃ B',
      q =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 S]
        fun z => Real.exp (B' * Real.exp (c' * |z.im|)) := by
    refine ⟨c, hclt, B, IsBigO.of_bound k ?_⟩
    rw [eventually_inf_principal]
    exact Filter.Eventually.of_forall fun z hz => by
      simpa only [Real.norm_eq_abs, Real.abs_exp] using hqgrowth z hz.1.le hz.2.le
  have hleft (z : ℂ) (hz : z.re = a) : ‖q z‖ ≤ M := by
    have hza : a ≤ z.re := by rw [hz]
    simp only [q, norm_div, norm_pow]
    exact (div_le_iff₀ (pow_pos (hdenpos z hza) m)).mpr (ha z hz)
  have hright (z : ℂ) (hz : z.re = b) : ‖q z‖ ≤ M := by
    have hza : a ≤ z.re := by rw [hz]; exact hab.le
    simp only [q, norm_div, norm_pow]
    exact (div_le_iff₀ (pow_pos (hdenpos z hza) m)).mpr (hb z hz)
  intro z hza hzb
  have hqbound := PhragmenLindelof.vertical_strip hqdiff hBigO hleft hright hza hzb
  have hpowpos : 0 < ‖z + (d : ℂ)‖ ^ m := pow_pos (hdenpos z hza) m
  apply (div_le_iff₀ hpowpos).mp
  simpa only [q, norm_div, norm_pow] using hqbound

end ArtinPrimitiveRoots.Proofs.s7sol_zeros
