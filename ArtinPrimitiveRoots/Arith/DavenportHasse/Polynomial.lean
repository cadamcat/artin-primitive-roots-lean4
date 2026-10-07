import Mathlib

namespace ArtinPrimitiveRoots.Arith

/-- The weight attached to a monic polynomial in the Davenport–Hasse Euler product. -/
def dhPolyWeight {k : Type*} [Field k] (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    (p : Polynomial k) : ℂ :=
  (-1 : ℂ) ^ p.natDegree *
    (χ ((-1 : k) ^ p.natDegree * p.coeff 0) * ψ (-p.nextCoeff))

theorem dhPolyWeight_mul {k : Type*} [Field k] (χ : MulChar k ℂ) (ψ : AddChar k ℂ)
    {p q : Polynomial k} (hp : p.Monic) (hq : q.Monic) :
    dhPolyWeight χ ψ (p * q) = dhPolyWeight χ ψ p * dhPolyWeight χ ψ q := by
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree :=
    hp.natDegree_mul' hq.ne_zero
  have hnorm : (-1 : k) ^ (p.natDegree + q.natDegree) * (p * q).coeff 0 =
      ((-1 : k) ^ p.natDegree * p.coeff 0) *
        ((-1 : k) ^ q.natDegree * q.coeff 0) := by
    simp [pow_add, Polynomial.mul_coeff_zero]
    ring
  rw [dhPolyWeight, hdeg, hp.nextCoeff_mul hq, hnorm]
  simp only [dhPolyWeight]
  simp only [map_mul, neg_add, ψ.map_add_eq_mul, pow_add]
  ring

/-- The lower coefficients parameterize monic polynomials of a fixed degree. -/
noncomputable def dhMonicCoeffEquiv {k : Type*} [Field k] (n : ℕ) :
    (Fin n → k) ≃ {p : Polynomial k // p.Monic ∧ p.natDegree = n} :=
  (Polynomial.degreeLTEquiv k n).toEquiv.symm.trans
    (Polynomial.monicEquivDegreeLT (R := k) n).symm

@[simp] theorem dhMonicCoeffEquiv_coeff {k : Type*} [Field k]
    (n : ℕ) (v : Fin n → k) (i : Fin n) :
    (dhMonicCoeffEquiv n v).val.coeff i = v i := by
  have hi : (i : ℕ) < n := i.isLt
  have heq : ∀ j : Fin n, (j : ℕ) = (i : ℕ) ↔ j = i := by
    intro j
    constructor
    · exact Fin.ext
    · rintro rfl
      rfl
  change (Polynomial.X ^ n +
      ∑ j : Fin n, Polynomial.monomial j (v j)).coeff i = v i
  rw [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, ne_of_lt hi, Polynomial.coeff_monomial,
    heq]

theorem dhMonicCoeffEquiv_nextCoeff {k : Type*} [Field k]
    {n : ℕ} (hn : 0 < n) (v : Fin n → k) :
    (dhMonicCoeffEquiv n v).val.nextCoeff = v ⟨n - 1, by omega⟩ := by
  have hdeg : (dhMonicCoeffEquiv n v).val.natDegree = n :=
    (dhMonicCoeffEquiv n v).property.2
  have hn' : 0 < (dhMonicCoeffEquiv n v).val.natDegree := by rw [hdeg]; exact hn
  rw [Polynomial.nextCoeff_of_natDegree_pos hn', hdeg]
  exact dhMonicCoeffEquiv_coeff n v ⟨n - 1, by omega⟩

noncomputable instance dhFintypeMonicDegree {k : Type*} [Field k] [Fintype k] (n : ℕ) :
    Fintype {p : Polynomial k // p.Monic ∧ p.natDegree = n} :=
  Fintype.ofEquiv (Fin n → k) (dhMonicCoeffEquiv n)

theorem dhPolyWeight_sum_monic {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (n : ℕ) :
    ∑ p : {p : Polynomial k // p.Monic ∧ p.natDegree = n}, dhPolyWeight χ ψ p =
      if n = 0 then 1 else if n = 1 then -gaussSum χ ψ else 0 := by
  classical
  cases n with
  | zero =>
      rw [(Equiv.sum_comp (dhMonicCoeffEquiv 0) _).symm]
      simp [dhPolyWeight, dhMonicCoeffEquiv, Polynomial.monicEquivDegreeLT,
        Polynomial.degreeLTEquiv, Polynomial.nextCoeff]
  | succ n =>
      cases n with
      | zero =>
        rw [(Equiv.sum_comp (dhMonicCoeffEquiv 1) _).symm]
        let e : (Fin 1 → k) ≃ k := Equiv.ofBijective
          (fun v : Fin 1 → k => v (0 : Fin 1)) (by
          constructor
          · intro f g h
            funext i
            have : i = (0 : Fin 1) := Fin.ext (by omega)
            subst i
            exact h
          · intro a
            exact ⟨fun _ => a, rfl⟩)
        rw [(Equiv.sum_comp e.symm (fun v : Fin 1 → k =>
          dhPolyWeight χ ψ (dhMonicCoeffEquiv 1 v).val)).symm]
        have hweight (a : k) :
            dhPolyWeight χ ψ (dhMonicCoeffEquiv 1 (e.symm a)).val =
              -(χ (-a) * ψ (-a)) := by
          have h0 : e.symm a (0 : Fin 1) = a := by
            change e (e.symm a) = a
            exact e.apply_symm_apply a
          simp [dhPolyWeight, dhMonicCoeffEquiv, e, h0,
            Polynomial.monicEquivDegreeLT, Polynomial.degreeLTEquiv,
            Polynomial.nextCoeff]
        simp_rw [hweight]
        rw [Finset.sum_neg_distrib]
        calc
          -(∑ a : k, χ (-a) * ψ (-a)) =
              -(∑ a : k, χ a * ψ a) := by
                congr 1
                exact Equiv.sum_comp (Equiv.neg k) (fun a : k => χ a * ψ a)
          _ = -gaussSum χ ψ := by rw [gaussSum]
      | succ m =>
        let e : k × (Fin (m + 1) → k) ≃ (Fin (m + 2) → k) :=
          Fin.snocEquiv (fun _ : Fin (m + 1 + 1) => k)
        rw [(Equiv.sum_comp (dhMonicCoeffEquiv (m + 2)) _).symm]
        rw [(Equiv.sum_comp e _).symm]
        have hweight (a : k) (v : Fin (m + 1) → k) :
            dhPolyWeight χ ψ (dhMonicCoeffEquiv (m + 2) (e (a, v))).val =
              (-1 : ℂ) ^ (m + 2) *
                (χ ((-1 : k) ^ (m + 2) * v 0) * ψ (-a)) := by
          have hdeg := (dhMonicCoeffEquiv (m + 2) (e (a, v))).property.2
          have hc0 : (dhMonicCoeffEquiv (m + 2) (e (a, v))).val.coeff 0 = v 0 := by
            simpa [e] using
              (dhMonicCoeffEquiv_coeff (m + 2) (e (a, v)) (0 : Fin (m + 2)))
          have hlast : e (a, v) ⟨m + 1, by omega⟩ = a := by
            have hidx : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
              apply Fin.ext
              rfl
            rw [hidx]
            simpa [e] using (Fin.snoc_last v a)
          have hnext :
              (dhMonicCoeffEquiv (m + 2) (e (a, v))).val.nextCoeff = a := by
            rw [dhMonicCoeffEquiv_nextCoeff (n := m + 2) (by omega) (e (a, v))]
            exact hlast
          dsimp [dhPolyWeight]
          rw [hdeg, hc0, hnext]
        simp_rw [hweight]
        have hneg : (∑ a : k, ψ (-a)) = 0 := by
          have hsum : (∑ a : k, ψ (-a)) = ∑ a : k, ψ a := by
            simpa [Equiv.neg_apply] using
              (Equiv.sum_comp (Equiv.neg k) (fun a : k => ψ a))
          rw [hsum]
          exact AddChar.sum_eq_zero_of_ne_one hψ
        rw [Fintype.sum_prod_type]
        calc
          ∑ a : k, ∑ v : Fin (m + 1) → k,
              (-1 : ℂ) ^ (m + 2) * (χ ((-1 : k) ^ (m + 2) * v 0) * ψ (-a))
              = ∑ a : k,
                  (∑ v : Fin (m + 1) → k,
                    (-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0)) * ψ (-a) := by
                apply Finset.sum_congr rfl
                intro a ha
                calc
                  _ = ∑ v : Fin (m + 1) → k,
                        ((-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0)) * ψ (-a) := by
                          apply Finset.sum_congr rfl
                          intro v hv
                          ring
                  _ = _ :=
                    (Finset.sum_mul (Finset.univ : Finset (Fin (m + 1) → k))
                      (fun v => (-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0))
                      (ψ (-a))).symm
          _ = (∑ a : k, ψ (-a)) *
                (∑ v : Fin (m + 1) → k,
                  (-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0)) := by
                calc
                  _ = ∑ a : k, ψ (-a) *
                        (∑ v : Fin (m + 1) → k,
                          (-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0)) := by
                        apply Finset.sum_congr rfl
                        intro a ha
                        rw [mul_comm]
                  _ = _ :=
                    (Finset.sum_mul (Finset.univ : Finset k)
                      (fun a : k => ψ (-a))
                      (∑ v : Fin (m + 1) → k,
                        (-1 : ℂ) ^ (m + 2) * χ ((-1 : k) ^ (m + 2) * v 0))).symm
          _ = 0 := by rw [hneg, zero_mul]

noncomputable def dhLSeries {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ p : {p : Polynomial k // p.Monic ∧ p.natDegree = n}, dhPolyWeight χ ψ p

theorem dhLSeries_eq_one_sub {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) :
    dhLSeries χ ψ = 1 - PowerSeries.C (gaussSum χ ψ) * PowerSeries.X := by
  ext n
  rw [dhLSeries, PowerSeries.coeff_mk, dhPolyWeight_sum_monic χ ψ hχ hψ]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp [gaussSum]
      | succ n => simp

noncomputable def dhGeom (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.rescale a (PowerSeries.mk 1)

theorem dhGeom_mul_one_sub (a : ℂ) :
    dhGeom a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale a)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa [dhGeom, PowerSeries.rescale_X] using h

@[simp] theorem coeff_dhGeom (a : ℂ) (n : ℕ) :
    PowerSeries.coeff n (dhGeom a) = a ^ n := by
  simp [dhGeom, PowerSeries.coeff_rescale]

noncomputable def dhEulerLogDerivative {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.derivative (dhLSeries χ ψ) * dhGeom (gaussSum χ ψ)

theorem dhEulerLogDerivative_coeff {k : Type*} [Field k] [Fintype k]
    (χ : MulChar k ℂ) (ψ : AddChar k ℂ) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (n : ℕ) :
    PowerSeries.coeff n (dhEulerLogDerivative χ ψ) =
      if n = 0 then 0 else -(gaussSum χ ψ) ^ n := by
  rw [dhEulerLogDerivative, dhLSeries_eq_one_sub χ ψ hχ hψ]
  have hd : PowerSeries.derivative
      (1 - PowerSeries.C (gaussSum χ ψ) * PowerSeries.X) =
        -PowerSeries.C (gaussSum χ ψ) := by
    simp only [map_sub, PowerSeries.derivative_one, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X, zero_smul, smul_eq_mul,
      zero_mul, mul_zero, mul_one, zero_sub, add_zero]
  rw [hd]
  rw [mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      simp [PowerSeries.coeff_C_mul, coeff_dhGeom, pow_succ, mul_comm]

end ArtinPrimitiveRoots.Arith
