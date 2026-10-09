import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_f.EulerProducts

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem deleted_identity (HC : EulerCorrection R η U) (HA : HeckeAnalysis F)
    (hE : EulerHypotheses R η)
    (hfactor : ∀ u ξ w z, initialRegion ξ w z →
      HasProd (fun v : {v : FinPlace F // v ∉ S.Sf} => localEuler R η U u v.1 v.2 ξ w z)
        (calF R η U u ξ w z))
    (hH : ∀ u p, eulerNeighborhood p → HasProd
      (fun v : {v : FinPlace F // v ∉ S.Sf} =>
        normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2)) (HC.H u p)) :
    ∀ u ξ w z, initialRegion ξ w z →
      calF R η U u ξ w z = HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
        HA.LS S (η * (U.kummer u)⁻¹) ξ := by
  intro u ξ w z hreg
  have hξ : 1 < ξ.re := by linarith [hreg.1]
  have hw : 1 < w.re := by linarith [hreg.2.1]
  have hz : 1 < (6 * z).re := by
    norm_num [Complex.mul_re]
    linarith [hreg.2.2]
  have hnb : eulerNeighborhood ![ξ,w,z] := by
    right
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    exact ⟨by linarith [hreg.1], by linarith [hreg.2.1], by linarith [hreg.2.2]⟩
  have hk := e_f.kummer_finiteOrder η U u hE.1
  have ht : IsOfFinOrder (η * (U.kummer u)⁻¹) := by
    rw [← U.omega_induces_twist u]
    exact U.omega_finiteOrder u
  have hmask (v : FinPlace F) (hv : v ∉ S.Sf) :
      (U.kummer u).primeValue v = chi D v (U.repr u : F) := by
    rw [U.kummer_primeValue_masked u v hv]
    by_cases hr : residue v (U.repr u : F) = 0
    · simp [hr, chi]
    · simp [hr]
  have htw (v : FinPlace F) (hv : v ∉ S.Sf) :
      (η * (U.kummer u)⁻¹).primeValue v =
        η.primeValue v * star (chi D v (U.repr u : F)) := by
    rw [e_f.twist_primeValue η (U.kummer u) v (hE.2.1 v hv) hk, hmask v hv]
  have hV := e_f.deleted_hasProd S HA (1 : HeckeChar F) IsOfFinOrder.one hz
  have hW := e_f.deleted_hasProd S HA (U.kummer u) hk hw
  have hD := e_f.deleted_hasProd S HA (η * (U.kummer u)⁻¹) ht hξ
  have hD0 := e_f.deleted_ne_zero S HA (η * (U.kummer u)⁻¹) ht hξ
  have hcomb := ((hV.mul hW).mul (hH u ![ξ,w,z] hnb)).mul (hD.inv₀ hD0)
  have hprod : HasProd
      (fun v : {v : FinPlace F // v ∉ S.Sf} => localEuler R η U u v.1 v.2 ξ w z)
      (HA.LS S 1 (6 * z) * HA.LS S (U.kummer u) w * HC.H u ![ξ,w,z] /
        HA.LS S (η * (U.kummer u)⁻¹) ξ) := by
    rw [div_eq_mul_inv]
    apply hcomb.congr_fun
    intro v
    have hq : (qI v.1.asIdeal : ℂ) = (Ideal.absNorm v.1.asIdeal : ℂ) := by
      simp [qI]
    have hV0 : 1 - localV v.1 z ≠ 0 := by
      intro he
      have hb := e_f.prime_ratio_small (1 : HeckeChar F) IsOfFinOrder.one hz v.1
      rw [e_f.one_primeValue, one_mul, ← hq] at hb
      have heq : localV v.1 z = 1 := (sub_eq_zero.mp he).symm
      have hb' : ‖localV v.1 z‖ < 1 := by
        simpa only [localV, neg_mul] using hb
      rw [heq] at hb'
      norm_num at hb'
    have hW0 : 1 - localWvar η U u v.1 w ≠ 0 := by
      intro he
      have hb := e_f.prime_ratio_small (U.kummer u) hk hw v.1
      rw [hmask v.1 v.2, ← hq] at hb
      have heq : localWvar η U u v.1 w = 1 := (sub_eq_zero.mp he).symm
      change ‖localWvar η U u v.1 w‖ < 1 at hb
      rw [heq] at hb
      norm_num at hb
    have hDlocal0 : 1 - localDvar η U u v.1 ξ ≠ 0 := by
      intro he
      have hb := e_f.prime_ratio_small (η * (U.kummer u)⁻¹) ht hξ v.1
      rw [htw v.1 v.2, ← hq] at hb
      have heq : localDvar η U u v.1 ξ = 1 := (sub_eq_zero.mp he).symm
      change ‖localDvar η U u v.1 ξ‖ < 1 at hb
      rw [heq] at hb
      norm_num at hb
    simp only [e_f.one_primeValue, one_mul, hmask v.1 v.2, htw v.1 v.2,
      ← hq, inv_inv, ← neg_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    change localEuler R η U u v.1 v.2 ξ w z =
      (1 - localV v.1 z)⁻¹ * (1 - localWvar η U u v.1 w)⁻¹ *
        normalizedLocal R η U u v.1 v.2 ξ w z * (1 - localDvar η U u v.1 ξ)
    rw [normalizedLocal]
    field_simp [hV0, hW0, hDlocal0] <;> ring
  exact (hfactor u ξ w z hreg).unique hprod

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
