import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-CANCEL».C0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.Proofs.qs_c_p.C1Helpers

/-!
# A2-QS-CANCEL, part C1: the main-term difference is a boundary sum

With `I_W = Mellin(W∘sq)(1)
= Mellin((T W)∘sq)(1)` (`qs_half_mellin_P0`) and `φ(𝔮f)/N(𝔮f) = (φ(𝔮)/N𝔮)(φ(f)/N f)`,
`dual main − orig main = ρ_K I_W √M (φ(f)/N f) · D_κ(ψ)` with
`D_κ = A_κ · S_𝔮 − (φ(𝔮)/N𝔮) A_{κ,𝔮}`, `A_κ = Σ_{a₀ sqf, N a₀ ≤ κ} ψ(a₀)/√N a₀`,
`A_{κ,𝔮}` the same with `(a₀,𝔮) = 1`, `S_𝔮 = Σ_{e∣𝔮} μ(e)ψ(e)/√N e`.  Writing `a₀ = h t`,
`t = (a₀, 𝔮)`, and expanding `φ(𝔮)/N𝔮` by C0, the two sums agree on `N h N t ≤ κ`, leaving
`D_κ = −S_𝔮 Σ_{t∣𝔮} ψ(t)/√N t Σ_{(h,𝔮)=1, κ/N t < N h ≤ κ} ψ(h)/√N h` (`qsBoundaryKernel`).
At `𝔮 = ⊤` the boundary is empty: `T = T'` exactly.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- C1 (IMPL): exact support of `T − T'` for one residual pair. -/
theorem qs_difference_exact_support_C1 [IsTotallyComplex K] (F : QSFamily m qS)
    (hrf : ∀ g h, F.rayFactor g h = 1) (hqS : qS ≠ ⊥)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ Λ n : ℝ) (hM : 0 < M)
    (𝔮 c d : Ideal (𝓞 K)) (h𝔮 : Squarefree 𝔮) (h𝔮bad : qsBadRad m qS ∣ 𝔮)
    (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (hcl : ∃ (hc' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
      (hd' : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
      ArtinPrimitiveRoots.Hecke.rayClass m c hc' = ArtinPrimitiveRoots.Hecke.rayClass m d hd')
    (hc𝔮 : IsCoprime c 𝔮) (hd𝔮 : IsCoprime d 𝔮) :
    qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d -
        qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d =
      qsBoundaryKernel F W M κ 𝔮 c d := by
  classical
  let ψ := qsPairChar F c d
  let Iw : ℂ := mellin (fun y : ℝ => (W (y ^ 2) : ℂ)) 1
  let C : ℂ := (qsResidueOne K : ℂ) * Iw * (Real.sqrt M : ℂ) *
    (qsPhiRatio (c * d) : ℂ)
  have hq0 : 𝔮 ≠ ⊥ := h𝔮.ne_zero
  have hcd0 : c * d ≠ ⊥ := mul_ne_zero hc.1.ne_zero hd.1.ne_zero
  have hqcd : IsCoprime 𝔮 (c * d) := IsCoprime.mul_right hc𝔮.symm hd𝔮.symm
  have hhalf :
      mellin (fun y : ℝ => qsTransform K (fun x => (W x : ℂ)) (y ^ 2)) 1 = Iw := by
    simpa [Iw] using qs_half_mellin_P0 (K := K) (fun x => (W x : ℂ)) hW.1
  let E : ℂ := ∑ e ∈ qsDivisors 𝔮,
    (qsMu e : ℂ) * ψ.idealValue e / (Real.sqrt (qsN e) : ℂ)
  let Aall : ℂ := ∑ a ∈ qsSqfUpTo κ ⊤,
    ψ.idealValue a / (Real.sqrt (qsN a) : ℂ)
  have hnormPos : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → 0 < qsN I := by
    intro I hI
    have hN : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr (by
      intro h
      exact hI (Ideal.absNorm_eq_zero_iff.mp h))
    exact_mod_cast hN
  have hOrig :
      qsOrigKernel (qsInnerMain K) F W M κ Λ 𝔮 c d =
        C * (qsPhiRatio 𝔮 : ℂ) *
          (∑ a ∈ qsSqfUpTo κ 𝔮,
            ψ.idealValue a / (Real.sqrt (qsN a) : ℂ)) := by
    unfold qsOrigKernel
    simp only [qsInnerMain]
    rw [qs_phiRatio_mul_C0 𝔮 (c * d) hq0 hcd0 hqcd]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := ha
    simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq] at ha'
    rcases ha' with ⟨_, ⟨ha0, _, _, hNa⟩⟩
    have hsqrt := Real.sqrt_div (le_of_lt hM) (qsN a)
    rw [hsqrt]
    push_cast
    simp only [C, Iw]
    ring
  have hψsq : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → P ∣ 𝔮 →
      ψ.idealValue P ^ 2 = 1 := by
    intro P hP hP0 hPq
    exact qsC1_pair_value_sq_one_at_q F c d 𝔮 P hc hd hcd hcl hc𝔮 hd𝔮 hP hP0 hPq
  have harith := qsC1_cancelSum ψ 𝔮 κ h𝔮 hψsq
  have hDual :
      qsDualKernel (qsInnerMain K) F W M κ Λ n 𝔮 c d = C * E * Aall := by
    classical
    unfold qsDualKernel
    simp only [qsInnerMain]
    simp_rw [hhalf]
    have hInner : ∀ e ∈ qsDivisors 𝔮,
        (qsMu e : ℂ) * ψ.idealValue e *
            ((M / (qsN e * Real.sqrt (qsN (c * d))) : ℝ) : ℂ) *
            (∑ a ∈ qsSqfUpTo κ ⊤,
              ψ.idealValue a *
                ((qsResidueOne K : ℂ) *
                  (Real.sqrt (qsN e * qsN (c * d) / (M * qsN a)) : ℂ) *
                    Iw * (qsPhiRatio (c * d) : ℂ))) =
          C * ((qsMu e : ℂ) * ψ.idealValue e /
            (Real.sqrt (qsN e) : ℂ)) * Aall := by
      intro e he
      have he' := he
      simp only [qsDivisors, Finset.mem_filter, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq] at he'
      have hedvd : e ∣ 𝔮 := he'.2
      have hesq : Squarefree e := Squarefree.squarefree_of_dvd hedvd h𝔮
      have he0 := hesq.ne_zero
      have hY0 : c * d ≠ ⊥ := hcd0
      have hYpos := hnormPos (c * d) hY0
      have hXpos := hnormPos e he0
      rw [Finset.mul_sum]
      unfold Aall
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := ha
      simp only [qsSqfUpTo, Finset.mem_filter, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq] at ha'
      rcases ha' with ⟨_, ⟨ha0, _, _, _⟩⟩
      have hNaPos := hnormPos a ha0
      have hscale := qsC1_dual_scale M (qsN e) (qsN (c * d)) (qsN a)
        hM hXpos hYpos hNaPos
      have hscaleC :
          (((M / (qsN e * Real.sqrt (qsN (c * d)))) : ℝ) : ℂ) *
              ((Real.sqrt (qsN e * qsN (c * d) / (M * qsN a)) : ℝ) : ℂ) =
            ((Real.sqrt M / (Real.sqrt (qsN e) * Real.sqrt (qsN a)) : ℝ) : ℂ) := by
        exact_mod_cast hscale
      have hNeC : (Real.sqrt (qsN e) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 hXpos).ne'
      have hNaC : (Real.sqrt (qsN a) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 hNaPos).ne'
      calc
        _ = ((qsMu e : ℂ) * ψ.idealValue e * ψ.idealValue a *
            (qsResidueOne K : ℂ) * Iw * (qsPhiRatio (c * d) : ℂ)) *
              ((((M / (qsN e * Real.sqrt (qsN (c * d)))) : ℝ) : ℂ) *
                ((Real.sqrt (qsN e * qsN (c * d) / (M * qsN a)) : ℝ) : ℂ)) := by ring
        _ = ((qsMu e : ℂ) * ψ.idealValue e * ψ.idealValue a *
            (qsResidueOne K : ℂ) * Iw * (qsPhiRatio (c * d) : ℂ)) *
              ((Real.sqrt M / (Real.sqrt (qsN e) * Real.sqrt (qsN a)) : ℝ) : ℂ) := by
              rw [hscaleC]
        _ = C * ((qsMu e : ℂ) * ψ.idealValue e /
              (Real.sqrt (qsN e) : ℂ)) *
                (ψ.idealValue a / (Real.sqrt (qsN a) : ℂ)) := by
              simp only [C]
              push_cast
              field_simp [hNeC, hNaC]
    calc
      _ = ∑ e ∈ qsDivisors 𝔮,
          C * ((qsMu e : ℂ) * ψ.idealValue e /
            (Real.sqrt (qsN e) : ℂ)) * Aall := by
              apply Finset.sum_congr rfl
              intro e he
              exact hInner e he
      _ = C * E * Aall := by
              have hE :
                  (∑ e ∈ qsDivisors 𝔮,
                    C * ((qsMu e : ℂ) * ψ.idealValue e /
                      (Real.sqrt (qsN e) : ℂ))) = C * E := by
                unfold E
                rw [Finset.mul_sum]
              calc
                _ = (∑ e ∈ qsDivisors 𝔮,
                    C * ((qsMu e : ℂ) * ψ.idealValue e /
                      (Real.sqrt (qsN e) : ℂ))) * Aall := by
                      exact (Finset.sum_mul (qsDivisors 𝔮)
                        (fun e => C * ((qsMu e : ℂ) * ψ.idealValue e /
                          (Real.sqrt (qsN e) : ℂ))) Aall).symm
                _ = C * E * Aall := by rw [hE]
  have harith' :
      E * Aall - (qsPhiRatio 𝔮 : ℂ) *
        (∑ h ∈ qsSqfUpTo κ 𝔮,
          ψ.idealValue h / (Real.sqrt (qsN h) : ℂ)) =
      -E * ∑ t ∈ qsDivisors 𝔮,
        ψ.idealValue t / (Real.sqrt (qsN t) : ℂ) *
          ∑ h ∈ (qsSqfUpTo κ 𝔮).filter (fun h => κ / qsN t < qsN h),
            ψ.idealValue h / (Real.sqrt (qsN h) : ℂ) := by
    simpa [E, Aall] using harith
  calc
    _ = C * (E * Aall - (qsPhiRatio 𝔮 : ℂ) *
          (∑ h ∈ qsSqfUpTo κ 𝔮,
            ψ.idealValue h / (Real.sqrt (qsN h) : ℂ))) := by
              rw [hDual, hOrig]
              ring
    _ = -C * E *
          ∑ t ∈ qsDivisors 𝔮,
            ψ.idealValue t / (Real.sqrt (qsN t) : ℂ) *
              ∑ h ∈ (qsSqfUpTo κ 𝔮).filter (fun h => κ / qsN t < qsN h),
                ψ.idealValue h / (Real.sqrt (qsN h) : ℂ) := by
              rw [harith']
              ring
    _ = qsBoundaryKernel F W M κ 𝔮 c d := by
          dsimp [qsBoundaryKernel, ψ, C, Iw, E]

end ArtinPrimitiveRoots.A2
