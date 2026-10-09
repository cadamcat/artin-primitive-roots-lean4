import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.TupleBox
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.FiniteInjection
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.LabelMatrix

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD MeasureTheory

noncomputable section

/-- A rectangle fibre bound restricts to the physical prime-tuple signed-minor kernel. -/
theorem prime_tuple_minor_counting_bound {K : ℕ} (x : ℝ) (a : Fin K → ℝ)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (T : Finset ((ℤ × ℤ) × (Fin K → ℕ)))
    (hT : ∀ u ∈ T, IsMarkedPrimeTuple x K a u.2)
    (Φ : (ℤ × ℤ) → (ℤ × ℤ))
    (hΦ : Set.InjOn Φ ((T.image Prod.fst) : Set (ℤ × ℤ)))
    (A B : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hbox : ∀ u ∈ T, |((Φ u.1).1 : ℝ)| ≤ A ∧ |((Φ u.1).2 : ℝ)| ≤ B)
    (D : ℕ)
    (hdet : ∀ u ∈ T, ∀ v ∈ T,
      ((det2 u.1 v.1/(D : ℤ) : ℤ) : ℝ) = (det2 (Φ u.1) (Φ v.1) : ℝ))
    (ψ : ℝ → ℝ) (Y R : ℝ) (hR : 0 ≤ R) (P : Set ℝ) (hP : MeasurableSet P)
    (hfibre : ∀ θ ∈ Set.Icc (0 : ℝ) 1 ∩ P, ∀ g : ℕ × ℕ → ℂ,
      let I := (Finset.range (2*⌊A⌋+1).toNat).product (Finset.range (2*⌊B⌋+1).toNat)
      let Δ := fun i j : ℕ × ℕ =>
        (-(⌊A⌋ : ℝ)+(i.1 : ℝ))*(-(⌊B⌋ : ℝ)+(j.2 : ℝ))-
          (-(⌊B⌋ : ℝ)+(i.2 : ℝ))*(-(⌊A⌋ : ℝ)+(j.1 : ℝ))
      (∑ i ∈ I, ‖∑ j ∈ I,
        (ψ (Δ i j/Y) : ℂ)*additiveCharacter (θ*Δ i j)*g j‖^2) ≤
          R^2*(∑ j ∈ I, ‖g j‖^2))
    (f : ((ℤ × ℤ) × (Fin K → ℕ)) → ℂ) :
    let t := fun u v : ((ℤ × ℤ) × (Fin K → ℕ)) => ((det2 u.1 v.1/(D : ℤ) : ℤ) : ℝ)
    (∑ u ∈ T, ‖∑ v ∈ T,
      ((ψ (t u v/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
        additiveCharacter (θ*(t u v-(tupleProduct u.2 : ℝ)+(tupleProduct v.2 : ℝ)))
          else 0))*f v‖^2) ≤ R^2*(∑ v ∈ T, ‖f v‖^2) := by
  let M := (2*⌊A⌋+1).toNat
  let N := (2*⌊B⌋+1).toNat
  let I := (Finset.range M).product (Finset.range N)
  let Δ := fun i j : ℕ × ℕ =>
    (-(⌊A⌋ : ℝ)+(i.1 : ℝ))*(-(⌊B⌋ : ℝ)+(j.2 : ℝ))-
      (-(⌊B⌋ : ℝ)+(i.2 : ℝ))*(-(⌊A⌋ : ℝ)+(j.1 : ℝ))
  let E : ((ℤ × ℤ) × (Fin K → ℕ)) → ((ℕ × ℕ) × ℤ) := fun u =>
    ((((Φ u.1).1+⌊A⌋).toNat, ((Φ u.1).2+⌊B⌋).toNat), (tupleProduct u.2 : ℤ))
  let U : Finset ℤ := T.image (fun u => (tupleProduct u.2 : ℤ))
  let t := fun u v : ((ℤ × ℤ) × (Fin K → ℕ)) => ((det2 u.1 v.1/(D : ℤ) : ℤ) : ℝ)
  let k : ((ℕ × ℕ) × ℤ) → ((ℕ × ℕ) × ℤ) → ℂ := fun u v =>
    (ψ (Δ u.1 v.1/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
      additiveCharacter (θ*(Δ u.1 v.1-(u.2 : ℝ)+(v.2 : ℝ))) else 0)
  have hemb := position_prime_tuple_box_embedding x a hbands T hT Φ hΦ A B hA hB hbox
  change (M : ℝ) ≤ 3*A ∧ (N : ℝ) ≤ 3*B ∧ Set.InjOn E (T : Set _) ∧
    (∀ u ∈ T, E u ∈ I.product U) ∧
    ∀ u ∈ T, ((E u).1.1 : ℤ)-⌊A⌋ = (Φ u.1).1 ∧
      ((E u).1.2 : ℤ)-⌊B⌋ = (Φ u.1).2 at hemb
  rcases hemb with ⟨_, _, hinj, hmap, hcoords⟩
  have hreal (u : (ℤ × ℤ) × (Fin K → ℕ)) (hu : u ∈ T) :
      -(⌊A⌋ : ℝ)+((E u).1.1 : ℝ) = ((Φ u.1).1 : ℝ) ∧
        -(⌊B⌋ : ℝ)+((E u).1.2 : ℝ) = ((Φ u.1).2 : ℝ) := by
    have h₁ := congrArg (fun n : ℤ => (n : ℝ)) (hcoords u hu).1
    have h₂ := congrArg (fun n : ℤ => (n : ℝ)) (hcoords u hu).2
    push_cast at h₁ h₂
    constructor <;> linarith
  have hpair (u : (ℤ × ℤ) × (Fin K → ℕ)) (hu : u ∈ T)
      (v : (ℤ × ℤ) × (Fin K → ℕ)) (hv : v ∈ T) : t u v = Δ (E u).1 (E v).1 := by
    dsimp only [t]
    rw [hdet u hu v hv]
    dsimp only [Δ, det2]
    push_cast
    rw [(hreal u hu).1, (hreal u hu).2, (hreal v hv).1, (hreal v hv).2]
  have hfull (g : ((ℕ × ℕ) × ℤ) → ℂ) :
      (∑ u ∈ I.product U, ‖∑ v ∈ I.product U, k u v*g v‖^2) ≤
        R^2*(∑ v ∈ I.product U, ‖g v‖^2) :=
    minor_label_matrix_bound I U Δ ψ Y R hR P hP hfibre g
  have hrestricted := finite_injective_matrix_bound T (I.product U) E hmap hinj k R hfull f
  have hterm (u : (ℤ × ℤ) × (Fin K → ℕ)) (hu : u ∈ T)
      (v : (ℤ × ℤ) × (Fin K → ℕ)) (hv : v ∈ T) :
      k (E u) (E v) = (ψ (t u v/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
        additiveCharacter (θ*(t u v-(tupleProduct u.2 : ℝ)+(tupleProduct v.2 : ℝ)))
          else 0) := by
    dsimp only [k]
    rw [← hpair u hu v hv]
    simp only [E, Int.cast_natCast]
  have hrows (u : (ℤ × ℤ) × (Fin K → ℕ)) (hu : u ∈ T) :
      (∑ v ∈ T, k (E u) (E v)*f v) =
        ∑ v ∈ T, ((ψ (t u v/Y) : ℂ)*(∫ θ in (0 : ℝ)..1, if θ ∈ P then
          additiveCharacter (θ*(t u v-(tupleProduct u.2 : ℝ)+(tupleProduct v.2 : ℝ)))
            else 0))*f v :=
    Finset.sum_congr rfl (fun v hv => by rw [hterm u hu v hv])
  have houtput := Finset.sum_congr rfl (fun u hu => congrArg (fun z : ℂ => ‖z‖^2) (hrows u hu))
  rw [houtput] at hrestricted
  exact hrestricted

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
