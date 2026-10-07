import OAI.NumberTheory.PrimeGaps.Main
example (M x A : ℝ) : M*x*(Real.log x)^(-A) = M*x*Real.rpow (Real.log x) (-A) := by rfl
example (P M x A : ℝ) (h : P ≤ M*x*(Real.log x)^(-A)) :
    P ≤ M*x*Real.rpow (Real.log x) (-A) := h
