import ArtinPrimitiveRoots.A2.Proofs.A2_RF_LOCAL.Arithmetic

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_rf_local_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

lemma exp_mul (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (v : FinPlace F) :
    idealExp v (I * J) = idealExp v I + idealExp v J := by
  have h := FractionalIdeal.count_mul F v
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)
  rw [← FractionalIdeal.coeIdeal_mul, FractionalIdeal.count_coe F v (mul_ne_zero hI hJ),
    FractionalIdeal.count_coe F v hI, FractionalIdeal.count_coe F v hJ] at h
  exact_mod_cast h

lemma coprime_exp_zero (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (h : IsCoprime I J) (v : FinPlace F) (hv : v.asIdeal ∣ J) : idealExp v I = 0 := by
  by_contra hn
  have hd := (exp_ne_zero I hI v).mp hn
  exact v.prime.not_isUnit (h.isUnit_of_dvd' hd hv)

lemma squarefree_exp_one (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hsq : Squarefree I)
    (v : FinPlace F) (hv : v.asIdeal ∣ I) : idealExp v I = 1 := by
  have hn := (exp_ne_zero I hI v).mpr hv
  have hl := exp_squarefree_le I hI hsq v
  omega

variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {bc : BalancedChoices D S H Bd}

lemma frequency_order (E : ExteriorArithmetic D S H Bd bc)
    (a : S.ExtIdeal) (c : S.SqfExtIdeal) (n d f : S.ExtIdeal) (ε : S.US)
    (v : FinPlace F) (hv : v ∉ S.Sf) :
    ordv v (toLoc v ((ε : Fˣ) * bc.gen a * bc.gen (E.ofSqf c) * bc.gen n ^ 3 /
      (bc.gen d * bc.gen f) ^ 2)) =
      (idealExp v a.1 : ℤ) + idealExp v c.1 + 3 * idealExp v n.1 -
        2 * (idealExp v d.1 + idealExp v f.1) := by
  rw [ord_div, ord_mul, ord_mul, ord_mul, ord_pow, ord_pow, ord_mul,
    ord_sunit S ε v hv, ord_gen S a _ (bc.gen_spec a).1 v hv,
    ord_gen S (E.ofSqf c) _ (bc.gen_spec (E.ofSqf c)).1 v hv,
    ord_gen S n _ (bc.gen_spec n).1 v hv,
    ord_gen S d _ (bc.gen_spec d).1 v hv,
    ord_gen S f _ (bc.gen_spec f).1 v hv, E.ofSqf_val]
  ring

lemma classification_unique (E : ExteriorArithmetic D S H Bd bc)
    (d f : S.ExtIdeal) (ν : Fˣ)
    (p q : S.ExtIdeal × S.SqfExtIdeal × S.ExtIdeal)
    (hpA : ∀ v ∈ E.support p.1, v ∈ E.support f)
    (hqA : ∀ v ∈ E.support q.1, v ∈ E.support f)
    (hpC : IsCoprime (p.2.1.1 * p.2.2.1) (d.1 * f.1))
    (hqC : IsCoprime (q.2.1.1 * q.2.2.1) (d.1 * f.1))
    (hpν : ∃ ε : S.US, ν = (ε : Fˣ) * bc.gen p.1 * bc.gen (E.ofSqf p.2.1) *
      bc.gen p.2.2 ^ 3 / (bc.gen d * bc.gen f) ^ 2)
    (hqν : ∃ ε : S.US, ν = (ε : Fˣ) * bc.gen q.1 * bc.gen (E.ofSqf q.2.1) *
      bc.gen q.2.2 ^ 3 / (bc.gen d * bc.gen f) ^ 2) : p = q := by
  obtain ⟨εp, hεp⟩ := hpν
  obtain ⟨εq, hεq⟩ := hqν
  have hcounts (v : FinPlace F) :
      idealExp v p.1.1 = idealExp v q.1.1 ∧
      idealExp v p.2.1.1 = idealExp v q.2.1.1 ∧
      idealExp v p.2.2.1 = idealExp v q.2.2.1 := by
    by_cases hvS : v ∈ S.Sf
    · have hcP := exp_zero_at_S S (E.ofSqf p.2.1) v hvS
      have hcQ := exp_zero_at_S S (E.ofSqf q.2.1) v hvS
      simp only [E.ofSqf_val] at hcP hcQ
      simp [exp_zero_at_S S p.1 v hvS, exp_zero_at_S S q.1 v hvS,
        exp_zero_at_S S p.2.2 v hvS, exp_zero_at_S S q.2.2 v hvS, hcP, hcQ]
    · have hEq :
          (idealExp v p.1.1 : ℤ) + idealExp v p.2.1.1 + 3 * idealExp v p.2.2.1 =
          (idealExp v q.1.1 : ℤ) + idealExp v q.2.1.1 + 3 * idealExp v q.2.2.1 := by
        have hEq := congrArg (fun x : Fˣ => ordv v (toLoc v x)) (hεp.symm.trans hεq)
        rw [frequency_order E _ _ _ _ _ _ v hvS,
          frequency_order E _ _ _ _ _ _ v hvS] at hEq
        omega
      by_cases hvf : v ∈ E.support f
      · have hdvf : v.asIdeal ∣ d.1 * f.1 := dvd_mul_of_dvd_right
          ((E.mem_support f v).mp hvf) _
        have hP := coprime_exp_zero _ _ (mul_ne_zero p.2.1.property.1.1 p.2.2.property.1)
          hpC v hdvf
        have hQ := coprime_exp_zero _ _ (mul_ne_zero q.2.1.property.1.1 q.2.2.property.1)
          hqC v hdvf
        rw [exp_mul _ _ p.2.1.property.1.1 p.2.2.property.1] at hP
        rw [exp_mul _ _ q.2.1.property.1.1 q.2.2.property.1] at hQ
        omega
      · have haP : idealExp v p.1.1 = 0 := by
          by_contra hn
          exact hvf (hpA v ((E.mem_support p.1 v).mpr
            ((exp_ne_zero _ p.1.property.1 v).mp hn)))
        have haQ : idealExp v q.1.1 = 0 := by
          by_contra hn
          exact hvf (hqA v ((E.mem_support q.1 v).mpr
            ((exp_ne_zero _ q.1.property.1 v).mp hn)))
        have hcP := exp_squarefree_le _ p.2.1.property.1.1 p.2.1.property.2 v
        have hcQ := exp_squarefree_le _ q.2.1.property.1.1 q.2.1.property.2 v
        omega
  apply Prod.ext
  · apply Subtype.ext
    exact ideal_ext _ _ p.1.property.1 q.1.property.1 (fun v => (hcounts v).1)
  · apply Prod.ext
    · apply Subtype.ext
      exact ideal_ext _ _ p.2.1.property.1.1 q.2.1.property.1.1 (fun v => (hcounts v).2.1)
    · apply Subtype.ext
      exact ideal_ext _ _ p.2.2.property.1 q.2.2.property.1 (fun v => (hcounts v).2.2)

lemma classification_exists (E : ExteriorArithmetic D S H Bd bc)
    (d f : S.ExtIdeal) (hd : Squarefree d.1) (hf : Squarefree f.1)
    (hdis : ∀ v ∈ E.support d, v ∉ E.support f) (ν : Fˣ)
    (hνd : ∀ v ∈ E.support d, ordv v (toLoc v ν) = -2)
    (hνf : ∀ v ∈ E.support f, 0 ≤ ordv v (toLoc v ν) + 2 ∧
      ((ordv v (toLoc v ν) + 2) % 3 = 0 ∨ (ordv v (toLoc v ν) + 2) % 3 = 1))
    (hνt : ∀ v, v ∉ S.Sf → v ∉ E.support d → v ∉ E.support f →
      0 ≤ ordv v (toLoc v ν) ∧
      (ordv v (toLoc v ν) % 3 = 0 ∨ ordv v (toLoc v ν) % 3 = 1)) :
    ∃ p : S.ExtIdeal × S.SqfExtIdeal × S.ExtIdeal,
      ((∀ v ∈ E.support p.1, v ∈ E.support f) ∧
        ∀ v ∈ E.support f, idealExp v p.1.1 % 3 = 0 ∨ idealExp v p.1.1 % 3 = 1) ∧
      IsCoprime (p.2.1.1 * p.2.2.1) (d.1 * f.1) ∧
      ∃ ε : S.US, ν = (ε : Fˣ) * bc.gen p.1 * bc.gen (E.ofSqf p.2.1) *
        bc.gen p.2.2 ^ 3 / (bc.gen d * bc.gen f) ^ 2 := by
  classical
  let k : FinPlace F → ℤ := fun v => ordv v (toLoc v ν)
  let ks : Finset (FinPlace F) := (ord_finite ν).toFinset
  have hk (v : FinPlace F) (hv : v ∉ ks) : k v = 0 := by
    by_contra hn
    exact hv ((ord_finite ν).mem_toFinset.mpr hn)
  let af : FinPlace F → ℕ := fun v => if v ∈ E.support f then (k v + 2).toNat else 0
  let cf : FinPlace F → ℕ := fun v =>
    if v ∈ S.Sf ∨ v ∈ E.support d ∨ v ∈ E.support f then 0 else (k v).toNat % 3
  let nf : FinPlace F → ℕ := fun v =>
    if v ∈ S.Sf ∨ v ∈ E.support d ∨ v ∈ E.support f then 0 else (k v).toNat / 3
  have haSupp : ∀ v, af v ≠ 0 → v ∈ E.support f := by
    intro v hv
    by_contra hn
    simp [af, hn] at hv
  have hcSupp : ∀ v, cf v ≠ 0 → v ∈ ks := by
    intro v hv
    by_contra hn
    simp [cf, hk v hn] at hv
  have hnSupp : ∀ v, nf v ≠ 0 → v ∈ ks := by
    intro v hv
    by_contra hn
    simp [nf, hk v hn] at hv
  let ae := Finsupp.onFinset (E.support f) af haSupp
  let ce := Finsupp.onFinset ks cf hcSupp
  let ne := Finsupp.onFinset ks nf hnSupp
  have haS : ∀ v ∈ S.Sf, ae v = 0 := by
    intro v hv
    have hvf : v ∉ E.support f := fun h => E.support_exterior f v h hv
    simp [ae, af, hvf]
  have hcS : ∀ v ∈ S.Sf, ce v = 0 := by intro v hv; simp [ce, cf, hv]
  have hnS : ∀ v ∈ S.Sf, ne v = 0 := by intro v hv; simp [ne, nf, hv]
  obtain ⟨a, ha⟩ := ideal_of_exponents S ae haS
  obtain ⟨c, hc⟩ := ideal_of_exponents S ce hcS
  obtain ⟨n, hn⟩ := ideal_of_exponents S ne hnS
  have hae (v : FinPlace F) : idealExp v a.1 = af v := by simpa [ae] using ha v
  have hce (v : FinPlace F) : idealExp v c.1 = cf v := by simpa [ce] using hc v
  have hne (v : FinPlace F) : idealExp v n.1 = nf v := by simpa [ne] using hn v
  have hcf (v : FinPlace F) : cf v ≤ 1 := by
    by_cases hb : v ∈ S.Sf ∨ v ∈ E.support d ∨ v ∈ E.support f
    · simp [cf, hb]
    · have hvS : v ∉ S.Sf := fun h => hb (Or.inl h)
      have hvd : v ∉ E.support d := fun h => hb (Or.inr (Or.inl h))
      have hvf : v ∉ E.support f := fun h => hb (Or.inr (Or.inr h))
      have hh := hνt v hvS hvd hvf
      simp only [cf, if_neg hb]
      dsimp [k]
      omega
  have hcsq : Squarefree c.1 := squarefree_of_exp_le c.1 c.property.1
    (fun v => by rw [hce]; exact hcf v)
  let cSq : S.SqfExtIdeal := ⟨c.1, c.property, hcsq⟩
  have hactive : (∀ v ∈ E.support a, v ∈ E.support f) ∧
      ∀ v ∈ E.support f, idealExp v a.1 % 3 = 0 ∨ idealExp v a.1 % 3 = 1 := by
    constructor
    · intro v hv
      have hev := (exp_ne_zero _ a.property.1 v).mpr ((E.mem_support a v).mp hv)
      rw [hae] at hev
      exact haSupp v hev
    · intro v hv
      rw [hae]
      simp only [af, if_pos hv]
      have hh := hνf v hv
      dsimp [k]
      omega
  have hcop : IsCoprime (c.1 * n.1) (d.1 * f.1) := by
    apply coprime_of_exp_disjoint _ _ (mul_ne_zero c.property.1 n.property.1)
      (mul_ne_zero d.property.1 f.property.1)
    intro v
    by_cases hb : v ∈ S.Sf ∨ v ∈ E.support d ∨ v ∈ E.support f
    · left
      rw [exp_mul _ _ c.property.1 n.property.1, hce, hne]
      simp [cf, nf, hb]
    · right
      have hd0 : idealExp v d.1 = 0 := by
        by_contra hz
        exact hb (Or.inr (Or.inl ((E.mem_support d v).mpr
          ((exp_ne_zero _ d.property.1 v).mp hz))))
      have hf0 : idealExp v f.1 = 0 := by
        by_contra hz
        exact hb (Or.inr (Or.inr ((E.mem_support f v).mpr
          ((exp_ne_zero _ f.property.1 v).mp hz))))
      rw [exp_mul _ _ d.property.1 f.property.1, hd0, hf0, add_zero]
  let base : Fˣ := bc.gen a * bc.gen (E.ofSqf cSq) * bc.gen n ^ 3 /
    (bc.gen d * bc.gen f) ^ 2
  have hbase (v : FinPlace F) (hvS : v ∉ S.Sf) : ordv v (toLoc v base) = k v := by
    have horder := frequency_order E a cSq n d f (1 : S.US) v hvS
    have horder' : ordv v (toLoc v base) =
        (idealExp v a.1 : ℤ) + idealExp v c.1 + 3 * idealExp v n.1 -
          2 * (idealExp v d.1 + idealExp v f.1) := by
      simpa [base, cSq] using horder
    rw [horder', hae, hce, hne]
    by_cases hvd : v ∈ E.support d
    · have hvf := hdis v hvd
      have hd1 := squarefree_exp_one d.1 d.property.1 hd v ((E.mem_support d v).mp hvd)
      have hf0 : idealExp v f.1 = 0 := by
        by_contra hz
        exact hvf ((E.mem_support f v).mpr ((exp_ne_zero _ f.property.1 v).mp hz))
      have hν := hνd v hvd
      simp [af, cf, nf, hvd, hvf, hd1, hf0, k, hν]
    · by_cases hvf : v ∈ E.support f
      · have hf1 := squarefree_exp_one f.1 f.property.1 hf v ((E.mem_support f v).mp hvf)
        have hd0 : idealExp v d.1 = 0 := by
          by_contra hz
          exact hvd ((E.mem_support d v).mpr ((exp_ne_zero _ d.property.1 v).mp hz))
        have hν := hνf v hvf
        simp only [af, cf, nf, hvf, or_true, if_true, Nat.cast_zero,
          add_zero, mul_zero, zero_add, hd0, hf1, Nat.cast_one]
        dsimp [k]
        omega
      · have hd0 : idealExp v d.1 = 0 := by
          by_contra hz
          exact hvd ((E.mem_support d v).mpr ((exp_ne_zero _ d.property.1 v).mp hz))
        have hf0 : idealExp v f.1 = 0 := by
          by_contra hz
          exact hvf ((E.mem_support f v).mpr ((exp_ne_zero _ f.property.1 v).mp hz))
        have hν := hνt v hvS hvd hvf
        simp only [af, cf, nf, hvS, hvd, hvf, false_or, if_false, Nat.cast_zero,
          zero_add, hd0, hf0, add_zero, mul_zero, sub_zero]
        dsimp [k]
        omega
  let epsF : Fˣ := ν / base
  have heps : epsF ∈ S.US := by
    apply sunit_of_ord_zero S epsF
    intro v hv
    rw [ord_div, hbase v hv]
    dsimp [k]
    omega
  let ε : S.US := ⟨epsF, heps⟩
  refine ⟨(a, cSq, n), hactive, hcop, ε, ?_⟩
  change ν = (ν / base) * bc.gen a * bc.gen (E.ofSqf cSq) * bc.gen n ^ 3 /
    (bc.gen d * bc.gen f) ^ 2
  calc
    ν = (ν / base) * base := (div_mul_cancel ν base).symm
    _ = _ := by simp only [base, mul_div_assoc, mul_assoc]

end ArtinPrimitiveRoots.Proofs.a2_rf_local_sol
