import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false
open Set Filter
open scoped Classical Topology
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.thsol_sheets

private theorem local_sixth_power_open (A : Type*) [NontriviallyNormedField A]
    [CompleteSpace A] [CharZero A] :
    IsOpen ((powMonoidHom 6 : Aˣ →* Aˣ).range : Set Aˣ) := by
  have hd : HasStrictDerivAt (fun x : A => x ^ 6) (6 : A) 1 := by
    simpa using hasStrictDerivAt_pow 6 (1 : A)
  have hmap : map (fun x : A => x ^ 6) (𝓝 (1 : A)) = 𝓝 (1 : A) := by
    simpa using hd.map_nhds_eq (by norm_num : (6 : A) ≠ 0)
  have hzero : ({0} : Set A)ᶜ ∈ 𝓝 (1 : A) :=
    isClosed_singleton.isOpen_compl.mem_nhds (by simp)
  have himage : (fun x : A => x ^ 6) '' ({0} : Set A)ᶜ ∈ 𝓝 (1 : A) := by
    rw [← hmap]
    exact image_mem_map hzero
  have hu := (Units.continuous_val.tendsto (1 : Aˣ)) himage
  change Units.val ⁻¹' ((fun x : A => x ^ 6) '' ({0} : Set A)ᶜ) ∈ 𝓝 (1 : Aˣ) at hu
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : Aˣ))
  apply mem_of_superset hu
  intro u hu
  obtain ⟨x, hx, hpow⟩ := hu
  refine ⟨Units.mk0 x (by simpa using hx), ?_⟩
  apply Units.ext
  exact hpow

private theorem pi_sixth_power_open {ι : Type*} [Finite ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    (hG : ∀ i, IsOpen ((powMonoidHom 6 : G i →* G i).range : Set (G i))) :
    IsOpen ((powMonoidHom 6 : (∀ i, G i) →* (∀ i, G i)).range : Set (∀ i, G i)) := by
  have heq : ((powMonoidHom 6 : (∀ i, G i) →* (∀ i, G i)).range : Set (∀ i, G i)) =
      pi univ (fun i => ((powMonoidHom 6 : G i →* G i).range : Set (G i))) := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      intro i hi
      exact ⟨g i, rfl⟩
    · intro hf
      have hr : ∀ i, ∃ x : G i, x ^ 6 = f i := fun i => hf i (mem_univ i)
      choose g hg using hr
      refine ⟨g, ?_⟩
      funext i
      exact hg i
  rw [heq]
  exact isOpen_set_pi finite_univ (fun i _ => hG i)

private theorem prod_sixth_power_open {A B : Type*} [CommGroup A] [CommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B]
    (hA : IsOpen ((powMonoidHom 6 : A →* A).range : Set A))
    (hB : IsOpen ((powMonoidHom 6 : B →* B).range : Set B)) :
    IsOpen ((powMonoidHom 6 : A × B →* A × B).range : Set (A × B)) := by
  have heq : ((powMonoidHom 6 : A × B →* A × B).range : Set (A × B)) =
      ((powMonoidHom 6 : A →* A).range : Set A) ×ˢ
        ((powMonoidHom 6 : B →* B).range : Set B) := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨⟨q.1, rfl⟩, ⟨q.2, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  rw [heq]
  exact hA.prod hB

/-- Any function on sixth-power classes pulls back continuously to a finite product of local units. -/
theorem power_quotient_factor_continuous {ι κ : Type*} [Finite ι] [Finite κ]
    (K : ι → Type*) (T : κ → Type*)
    [∀ i, NontriviallyNormedField (K i)] [∀ i, CompleteSpace (K i)] [∀ i, CharZero (K i)]
    [∀ j, NontriviallyNormedField (T j)] [∀ j, CompleteSpace (T j)] [∀ j, CharZero (T j)]
    (b : (((∀ i, K i) × (∀ j, T j))ˣ ⧸
      (powMonoidHom 6 : ((∀ i, K i) × (∀ j, T j))ˣ →* ((∀ i, K i) × (∀ j, T j))ˣ).range) → ℂ) :
    Continuous (fun y : ((∀ i, K i) × (∀ j, T j))ˣ => b (QuotientGroup.mk y)) := by
  let M := (∀ i, K i) × (∀ j, T j)
  let A := ∀ i, (K i)ˣ
  let B := ∀ j, (T j)ˣ
  let em : Mˣ ≃* A × B := MulEquiv.prodUnits.trans
    ((ContinuousMulEquiv.piUnits (M := K)).toMulEquiv.prodCongr
      (ContinuousMulEquiv.piUnits (M := T)).toMulEquiv)
  let eh : Mˣ ≃ₜ A × B := Homeomorph.prodUnits.trans
    ((ContinuousMulEquiv.piUnits (M := K)).toHomeomorph.prodCongr
      (ContinuousMulEquiv.piUnits (M := T)).toHomeomorph)
  let e : Mˣ ≃ₜ* A × B := {
    em with
    continuous_toFun := eh.continuous_toFun
    continuous_invFun := eh.continuous_invFun }
  have hA : IsOpen ((powMonoidHom 6 : A →* A).range : Set A) :=
    pi_sixth_power_open (fun i => (K i)ˣ) (fun i => local_sixth_power_open (K i))
  have hB : IsOpen ((powMonoidHom 6 : B →* B).range : Set B) :=
    pi_sixth_power_open (fun j => (T j)ˣ) (fun j => local_sixth_power_open (T j))
  have hprod := prod_sixth_power_open hA hB
  have heq : ((powMonoidHom 6 : Mˣ →* Mˣ).range : Set Mˣ) =
      e ⁻¹' ((powMonoidHom 6 : A × B →* A × B).range : Set (A × B)) := by
    ext y
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨e x, ?_⟩
      change x ^ 6 = y at hx
      change (e x) ^ 6 = e y
      simpa only [map_pow] using congrArg e hx
    · rintro ⟨x, hx⟩
      refine ⟨e.symm x, ?_⟩
      change x ^ 6 = e y at hx
      change (e.symm x) ^ 6 = y
      apply e.injective
      simpa only [map_pow, e.apply_symm_apply] using hx
  have hopen : IsOpen ((powMonoidHom 6 : Mˣ →* Mˣ).range : Set Mˣ) := by
    rw [heq]
    exact hprod.preimage e.continuous
  have : DiscreteTopology (Mˣ ⧸ (powMonoidHom 6 : Mˣ →* Mˣ).range) :=
    QuotientGroup.discreteTopology hopen
  have hb : Continuous b := continuous_of_discreteTopology
  exact hb.comp QuotientGroup.continuous_mk

end ArtinPrimitiveRoots.Proofs.thsol_sheets
