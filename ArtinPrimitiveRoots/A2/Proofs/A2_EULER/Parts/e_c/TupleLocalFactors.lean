import Mathlib.Algebra.Field.Equiv
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.LocalNormalization
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.e_c.GeneratorCharacters

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory Function
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_c
open ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)











include R

theorem generator_valuation_pow (I : S.ExtIdeal) (a : S.R)
    (ha : S.IsGen (a : F) I.1) (v : ExteriorPrime S) :
    v.1.valuation F (a : F) = v.1.valuation F (primeGen R v.1 : F) ^ idealExp v.1 I.1 := by
  rw [generatorR_valuation R I a ha v, primeGen_valuation R v]
  simp [← WithZero.exp_nsmul, nsmul_eq_mul]

theorem complementR_split (a : S.R) (v : ExteriorPrime S) (n : ℕ)
    (hn : v.1.valuation F (a : F) = v.1.valuation F (primeGen R v.1 : F) ^ n) :
    a = primeR R v ^ n * complementR R a v n hn := by
  apply Subtype.ext
  change (a : F) = (primeR R v : F) ^ n * (complementR R a v n hn : F)
  rw [primeR_val, complementR_val]
  field_simp [(primeGen R v.1).ne_zero]

theorem local_unit_factor (v : ExteriorPrime S) (k t : ℕ) (sp ap hp : S.R)
    (hs : v.1.valuation F (sp : F) = 1) (ha : v.1.valuation F (ap : F) = 1)
    (hh : v.1.valuation F (hp : F) = 1) :
    chi D v.1 ((hp : F) / (ap : F)) ^ k *
      chi D v.1 (((sp * ap : S.R) : F) / (hp : F)) ^ t =
    chi D v.1 (hp : F) ^ ((k : ℤ) - t) * chi D v.1 (sp : F) ^ t *
      chi D v.1 (ap : F) ^ ((t : ℤ) - k) := by
  have hsa : v.1.valuation F ((sp * ap : S.R) : F) = 1 := by
    change v.1.valuation F ((sp : F) * (ap : F)) = 1
    rw [map_mul, hs, ha, one_mul]
  rw [chi_ratio R v (ap : F) (hp : F) ha hh,
    chi_ratio R v (hp : F) ((sp * ap : S.R) : F) hh hsa]
  change (chi D v.1 (hp : F) / chi D v.1 (ap : F)) ^ k *
    (chi D v.1 ((sp : F) * (ap : F)) / chi D v.1 (hp : F)) ^ t = _
  rw [(a2_bridge_SYMBOL D S).chi_mul v.1 v.2 _ _ hs.le ha.le]
  have hs0 := chi_unit_ne_zero R v (sp : F) hs
  have ha0 := chi_unit_ne_zero R v (ap : F) ha
  have hh0 := chi_unit_ne_zero R v (hp : F) hh
  rw [zpow_sub₀ hh0, zpow_sub₀ ha0]
  simp only [zpow_natCast, div_pow, mul_pow]
  field_simp
  <;> ring

theorem finiteFactor_localC (s I : S.ExtIdeal) (a h : S.R)
    (ha : S.IsGen (a : F) I.1) (V : Finset (ExteriorPrime S))
    (hsV : ∀ v : ExteriorPrime S, idealExp v.1 s.1 ≠ 0 → v ∈ V)
    (hIV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V)
    (J : ExteriorPrime S → ℕ)
    (hJ : ∀ v ∈ V, v.1.valuation F (h : F) = v.1.valuation F (primeGen R v.1 : F) ^ J v) :
    finiteFactor R s I (Units.mk0 (a : F) ha.2.1) (h : F) =
      ∏ v ∈ V,
        (chi D v.1 ((h : F) / (primeGen R v.1 : F) ^ J v) ^
            ((idealExp v.1 s.1 : ℤ) - idealExp v.1 I.1) *
          chi D v.1 ((R.exterior.genR s : F) / (primeGen R v.1 : F) ^ idealExp v.1 s.1) ^
            idealExp v.1 I.1 *
          chi D v.1 ((a : F) / (primeGen R v.1 : F) ^ idealExp v.1 I.1) ^
            ((idealExp v.1 I.1 : ℤ) - idealExp v.1 s.1)) *
        localC R v.1 v.2 (idealExp v.1 I.1) (idealExp v.1 s.1) (J v) := by
  classical
  rw [finiteFactor_crt R s I a h ha V hsV hIV]
  apply Finset.prod_congr rfl
  intro v hv
  have hs : S.IsGen (R.exterior.genR s : F) s.1 := by
    simpa only [R.exterior.genR_val] using (bc.gen_spec s).1
  let sp := complementR R (R.exterior.genR s) v _ (generator_valuation_pow R s _ hs v)
  let ap := complementR R a v _ (generator_valuation_pow R I a ha v)
  let hp := complementR R h v (J v) (hJ v hv)
  have hs' := complementR_split R (R.exterior.genR s) v _ (generator_valuation_pow R s _ hs v)
  have ha' := complementR_split R a v _ (generator_valuation_pow R I a ha v)
  have hh' := complementR_split R h v (J v) (hJ v hv)
  have hsp := complementR_unit R (R.exterior.genR s) v _ (generator_valuation_pow R s _ hs v)
  have hap := complementR_unit R a v _ (generator_valuation_pow R I a ha v)
  have hhp := complementR_unit R h v (J v) (hJ v hv)
  have heq := localizedSum_eq_localC R s I v (J v) sp ap hp hs' hsp hap hhp
  rw [← ha', ← hh'] at heq
  rw [heq, local_unit_factor R v _ _ sp ap hp hsp hap hhp]
  rfl

end ArtinPrimitiveRoots.Proofs.e_c
