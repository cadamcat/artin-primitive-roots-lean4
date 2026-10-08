import ArtinPrimitiveRoots.A1.ThetaInterface

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
open ArtinPrimitiveRoots.A1

theorem finite_weighted_fourier {F : Type} [Field F] [NumberField F]
    {CE : ℕ} {condη : Ideal (𝓞 F)}
    {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
    {A : AddCharData F} {C : ThetaCover D S H A} {𝓛 : Finset (SChar S)}
    (T : ThetaFamily C 𝓛) (L : SChar S) (hL : L ∈ 𝓛)
    {ι : Type} [Fintype ι] (a : ι → ℂ) (g : ι → C.G) (b : ℂ) :
    Summable (fun ν : Fˣ => b * ∑ d : ι,
      a d * T.W L (C.rat (diagGL ν) * g d)) ∧
    b * (∑ d : ι, a d * T.θ L (g d)) =
      b * (∑ d : ι, a d * T.θN L (g d)) +
        ∑' ν : Fˣ, b * ∑ d : ι,
          a d * T.W L (C.rat (diagGL ν) * g d) := by
  classical
  let W (d : ι) (ν : Fˣ) : ℂ := T.W L (C.rat (diagGL ν) * g d)
  have hW (d : ι) : Summable (W d) := (T.fourier L hL (g d)).1
  have hA (d : ι) : Summable (fun ν => a d * W d ν) := (hW d).mul_left _
  have hSum : Summable (fun ν => ∑ d : ι, a d * W d ν) :=
    summable_sum (fun d _ => hA d)
  have hθ (d : ι) : a d * T.θ L (g d) =
      a d * T.θN L (g d) + ∑' ν, a d * W d ν := by
    have h : T.θ L (g d) = T.θN L (g d) + ∑' ν, W d ν :=
      (T.fourier L hL (g d)).2
    rw [h, mul_add, (hW d).tsum_mul_left]
  have hDigits : (∑ d : ι, a d * T.θ L (g d)) =
      (∑ d : ι, a d * T.θN L (g d)) +
        ∑' ν, ∑ d : ι, a d * W d ν := by
    calc
      _ = ∑ d : ι, (a d * T.θN L (g d) + ∑' ν, a d * W d ν) :=
        Finset.sum_congr rfl (fun d _ => hθ d)
      _ = _ := by
        rw [Finset.sum_add_distrib, Summable.tsum_finsetSum (fun d _ => hA d)]
  constructor
  · exact hSum.mul_left b
  · rw [hDigits, mul_add]
    exact congrArg (fun z : ℂ => b * (∑ d : ι, a d * T.θN L (g d)) + z)
      (hSum.tsum_mul_left b).symm

end ArtinPrimitiveRoots.Proofs.a2_rffwd_sol
