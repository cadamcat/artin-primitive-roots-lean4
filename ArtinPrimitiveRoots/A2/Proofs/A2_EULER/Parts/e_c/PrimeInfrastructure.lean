import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Parts.BridgeDefinitions
import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.e_c
open ArtinPrimitiveRoots.Proofs.a2_euler_sol
local macro "reflection% " n:ident : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.ArtinPrimitiveRoots.A2.Reflection.Missing 0) ++
    `ArtinPrimitiveRoots.A2 ++ n.getId))
local macro "characters% " n:ident : term =>
  pure (Lean.mkIdent ((Lean.Name.num `_private.ArtinPrimitiveRoots.A1.Characters 0) ++
    `ArtinPrimitiveRoots.A1 ++ n.getId))
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

theorem ideal_factorization_on (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    I.1 = ∏ v ∈ V, v.1.asIdeal ^ idealExp v.1 I.1 := by
  classical
  let W : Finset (FinPlace F) := V.image Subtype.val
  have hsub : R.exterior.support I ⊆ W := by
    intro v hvI
    have hv := R.exterior.support_exterior I v hvI
    have hn :=
      ((reflection% rf_local_exp_ne_zero_iff_support)
        R v I).mpr hvI
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, hV ⟨v, hv⟩ hn, rfl⟩
  calc
    I.1 = ∏ v ∈ R.exterior.support I, v.asIdeal ^ idealExp v I.1 :=
      (reflection% rf_local_ideal_factorization) R I
    _ = ∏ v ∈ W, v.asIdeal ^ idealExp v I.1 := by
      apply Finset.prod_subset hsub
      intro v hvW hnot
      have hz :=
        (reflection% rf_idealExp_zero_of_not_support)
          R v I hnot
      simp only [hz, pow_zero]
    _ = ∏ v ∈ V, v.1.asIdeal ^ idealExp v.1 I.1 :=
      Finset.prod_image Subtype.val_injective.injOn

theorem tuple_exponents (B : PrimeTupleBridge S) (p : IdealTuple S)
    (v : ExteriorPrime S) :
    idealExp v.1 p.1.1 = ((B.equiv p v).1 : ℕ) ∧
    idealExp v.1 p.2.1.1 = (B.equiv p v).2.1 ∧
    idealExp v.1 p.2.2.1.1 = (B.equiv p v).2.2.1 ∧
    idealExp v.1 p.2.2.2.1 = (B.equiv p v).2.2.2 := by
  have hcount (I : S.ExtIdeal) : idealExp v.1 I.1 =
      (UniqueFactorizationMonoid.normalizedFactors I.1).count v.1.asIdeal := by
    dsimp [idealExp]
    exact Ideal.count_associates_factors_eq
      (by simpa only [Ideal.zero_eq_bot] using I.property.1) v.1.isPrime v.1.ne_bot
  rcases B.counts p v with ⟨hc, hn, hs, hr⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc' := hcount (R.exterior.ofSqf p.1)
    have hc'' : idealExp v.1 p.1.1 =
        (UniqueFactorizationMonoid.normalizedFactors p.1.1).count v.1.asIdeal := by
      simpa only [R.exterior.ofSqf_val] using hc'
    exact hc''.trans hc.symm
  · exact (hcount p.2.1).trans hn.symm
  · exact (hcount p.2.2.1).trans hs.symm
  · exact (hcount p.2.2.2).trans hr.symm

theorem tuple_ideal_factorizations (B : PrimeTupleBridge S) (p : IdealTuple S) :
    p.1.1 = ∏ v ∈ (B.equiv p).support, v.1.asIdeal ^ ((B.equiv p v).1 : ℕ) ∧
    p.2.1.1 = ∏ v ∈ (B.equiv p).support, v.1.asIdeal ^ (B.equiv p v).2.1 ∧
    p.2.2.1.1 = ∏ v ∈ (B.equiv p).support, v.1.asIdeal ^ (B.equiv p v).2.2.1 ∧
    p.2.2.2.1 = ∏ v ∈ (B.equiv p).support, v.1.asIdeal ^ (B.equiv p v).2.2.2 := by
  classical
  let V := (B.equiv p).support
  have hzero (v : ExteriorPrime S) (hv : v ∉ V) :
      idealExp v.1 p.1.1 = 0 ∧ idealExp v.1 p.2.1.1 = 0 ∧
      idealExp v.1 p.2.2.1.1 = 0 ∧ idealExp v.1 p.2.2.2.1 = 0 := by
    have hz : B.equiv p v = 0 := Finsupp.notMem_support_iff.mp hv
    rcases tuple_exponents R B p v with ⟨hc, hn, hs, hr⟩
    simpa [hz] using And.intro hc (And.intro hn (And.intro hs hr))
  have hc := ideal_factorization_on R (R.exterior.ofSqf p.1) V (by
    intro v hn
    by_contra hv
    have h := (hzero v hv).1
    exact hn (by simpa only [R.exterior.ofSqf_val] using h))
  have hn := ideal_factorization_on R p.2.1 V (by
    intro v hn
    by_contra hv
    exact hn (hzero v hv).2.1)
  have hs := ideal_factorization_on R p.2.2.1 V (by
    intro v hn
    by_contra hv
    exact hn (hzero v hv).2.2.1)
  have hr := ideal_factorization_on R p.2.2.2 V (by
    intro v hn
    by_contra hv
    exact hn (hzero v hv).2.2.2)
  have hcExp (v : ExteriorPrime S) := (tuple_exponents R B p v).1
  have hnExp (v : ExteriorPrime S) := (tuple_exponents R B p v).2.1
  have hsExp (v : ExteriorPrime S) := (tuple_exponents R B p v).2.2.1
  have hrExp (v : ExteriorPrime S) := (tuple_exponents R B p v).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [R.exterior.ofSqf_val, hcExp, V] using hc
  · simpa only [hnExp, V] using hn
  · simpa only [hsExp, V] using hs
  · simpa only [hrExp, V] using hr

theorem finiteFactor_double_sum (s I : S.ExtIdeal) (a : Fˣ) (h : F) :
    finiteFactor R s I a h =
      ∑ᶠ d : ResidueRing R.exterior s, ∑ᶠ x : ResidueRing R.exterior I,
        if ∃ y : S.R, h - (a : F) * (d.out : F) = (bc.gen s : F) * (y : F) then
          chiIdealPow D s.1 (d.out : F) 1 * chiIdealPow D I.1 (x.out : F) 1 *
            S.e A (S.diag ((h - (a : F) * (d.out : F)) * (x.out : F) /
              ((bc.gen s : F) * (a : F))))
        else 0 := by
  classical
  letI : Fintype (ResidueRing R.exterior s) := R.exterior.residueFinite s
  letI : Fintype (ResidueRing R.exterior I) := R.exterior.residueFinite I
  simp only [finiteFactor, finiteGaussAt, finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : ∃ y : S.R,
      h - (a : F) * (d.out : F) = (bc.gen s : F) * (y : F)
  · simp only [if_pos hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have harg : ((h - (a : F) * (d.out : F)) / (bc.gen s : F)) * (x.out : F) /
        (a : F) = (h - (a : F) * (d.out : F)) * (x.out : F) /
        ((bc.gen s : F) * (a : F)) := by
      field_simp [Units.ne_zero a, Units.ne_zero (bc.gen s)] <;> ring
    simp only [harg, mul_assoc]
  · simp only [if_neg hc, Finset.sum_const_zero]

theorem ideal_norm_factorization_on (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    qI I.1 = ∏ v ∈ V, qI v.1.asIdeal ^ (idealExp v.1 I.1 : ℝ) := by
  have h := congrArg (fun J : Ideal (𝓞 F) => (Ideal.absNorm J : ℝ))
    (ideal_factorization_on R I V hV)
  simpa only [qI, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow,
    ← Real.rpow_natCast] using h

theorem hecke_idealValue_on (χ : HeckeChar F) (I : S.ExtIdeal)
    (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) :
    χ.idealValue I.1 = ∏ v ∈ V, χ.primeValue v.1 ^ idealExp v.1 I.1 := by
  classical
  let W := V.image Subtype.val
  have hsupp : Function.mulSupport
      (fun v : FinPlace F => χ.primeValue v ^ idealExp v I.1) ⊆ W := by
    intro v hv
    have he : idealExp v I.1 ≠ 0 := by
      intro hz
      change χ.primeValue v ^ idealExp v I.1 ≠ 1 at hv
      exact hv (by rw [hz, pow_zero])
    have hin :=
      ((reflection% rf_local_exp_ne_zero_iff_support)
        R v I).mp he
    have hvS := R.exterior.support_exterior I v hin
    exact Finset.mem_image.mpr ⟨⟨v, hvS⟩, hV ⟨v, hvS⟩ he, rfl⟩
  calc
    _ = ∏ᶠ v : FinPlace F, χ.primeValue v ^ idealExp v I.1 :=
      (characters% conductor_idealValue_finprod)
        χ I.1 I.property.1
    _ = ∏ v ∈ W, χ.primeValue v ^ idealExp v I.1 :=
      finprod_eq_prod_of_mulSupport_subset _ hsupp
    _ = _ := Finset.prod_image Subtype.val_injective.injOn

omit R in
 theorem cpow_nat_prod {ι : Type*} (V : Finset ι) (n : ι → ℕ) (b : ℂ) :
    ((∏ v ∈ V, n v : ℕ) : ℂ) ^ b = ∏ v ∈ V, (n v : ℂ) ^ b := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert v V hv ih =>
    rw [Finset.prod_insert hv, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
      ih, Finset.prod_insert hv]

theorem norm_weight_on (I : S.ExtIdeal) (V : Finset (ExteriorPrime S))
    (hV : ∀ v : ExteriorPrime S, idealExp v.1 I.1 ≠ 0 → v ∈ V) (b : ℂ) :
    (qI I.1 : ℂ) ^ b =
      ∏ v ∈ V, (qI v.1.asIdeal : ℂ) ^ ((idealExp v.1 I.1 : ℂ) * b) := by
  have hn : Ideal.absNorm I.1 =
      ∏ v ∈ V, Ideal.absNorm v.1.asIdeal ^ idealExp v.1 I.1 := by
    have h := congrArg Ideal.absNorm (ideal_factorization_on R I V hV)
    simpa only [map_prod, map_pow] using h
  simp only [qI, Complex.ofReal_natCast]
  rw [hn, cpow_nat_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]

theorem tuple_exponents_zero (B : PrimeTupleBridge S) (p : IdealTuple S)
    (v : ExteriorPrime S) (hv : v ∉ (B.equiv p).support) :
    idealExp v.1 p.1.1 = 0 ∧ idealExp v.1 p.2.1.1 = 0 ∧
      idealExp v.1 p.2.2.1.1 = 0 ∧ idealExp v.1 p.2.2.2.1 = 0 := by
  have hz : B.equiv p v = 0 := Finsupp.notMem_support_iff.mp hv
  simpa [hz] using tuple_exponents R B p v

theorem tuple_Aideal_exponent (B : PrimeTupleBridge S) (p : IdealTuple S)
    (v : ExteriorPrime S) :
    idealExp v.1 (Aideal R p.1 p.2.1).1 =
      ((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1 := by
  have hc0 : p.1.1 ≠ ⊥ := p.1.property.1.1
  have hn0 : p.2.1.1 ≠ ⊥ := p.2.1.property.1
  have hn3 : p.2.1.1 ^ 3 ≠ ⊥ := pow_ne_zero 3 hn0
  simp only [Aideal, R.exterior.mul_val, R.exterior.ofSqf_val, R.exterior.pow_val]
  rw [(characters% conductor_idealExp_mul_early) v.1 hc0 hn3,
    (characters% conductor_idealExp_pow_early) v.1 hn0 3,
    (tuple_exponents R B p v).1, (tuple_exponents R B p v).2.1]

theorem theta_Aideal_product (B : PrimeTupleBridge S) (p : IdealTuple S) :
    ϑ.idealValue (Aideal R p.1 p.2.1).1 =
      ∏ v ∈ (B.equiv p).support,
        ϑ.primeValue v.1 ^ (((B.equiv p v).1 : ℕ) + 3 * (B.equiv p v).2.1) := by
  have he (v : ExteriorPrime S) := tuple_Aideal_exponent R B p v
  have h := hecke_idealValue_on R ϑ (Aideal R p.1 p.2.1) (B.equiv p).support (by
    intro v hn
    by_contra hv
    have h0 := tuple_exponents_zero R B p v hv
    have hzero : idealExp v.1 (Aideal R p.1 p.2.1).1 = 0 := by
      simp only [Aideal, R.exterior.mul_val, R.exterior.ofSqf_val, R.exterior.pow_val]
      rw [(characters% conductor_idealExp_mul_early) v.1 p.1.property.1.1
          (pow_ne_zero 3 p.2.1.property.1),
        (characters% conductor_idealExp_pow_early) v.1 p.2.1.property.1 3,
        h0.1, h0.2.1]
    exact hn hzero)
  simpa only [he] using h

theorem gamma_squarefree_factorization (c : S.SqfExtIdeal) :
    gamma D S A 2 c.1 (cgen R c) =
      ∏ v ∈ R.exterior.support (R.exterior.ofSqf c),
        gamma D S A 2 v.asIdeal (primeGen R v : F) *
          chi D v (cgen R c / (primeGen R v : F)) ^ (2 : ℤ) :=
  (reflection% rf_gamma_sqf_factorization) R c

end ArtinPrimitiveRoots.Proofs.e_c
