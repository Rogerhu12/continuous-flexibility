import ContinuousFlexibility.Radial.CentralRadiusMetric
import ContinuousFlexibility.Radial.PositiveBufferGeometry
import Mathlib.Data.Matrix.Mul

/-!
# The exact central radial flux dictionary

The density root is the actual exp(-a_c X). Its derivative contributes
the diagonal drift with the same outward sign as the model derivative.
The final estimates use the R09 comparison of alpha_in with the mass;
the drift is retained in the positive reference diagonal.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The actual local radial flux, including the derivative of the
central density root. No model flux equality is assumed. -/
theorem innerCentral_flux_at {lam x : ℝ} {ψ w u : ℝ → ℝ}
    (hψ : DifferentiableAt ℝ ψ x)
    (hu : DifferentiableAt ℝ u (centralRadius x))
    (hw : w (centralRadius x) =
      lam * centralDensityRoot x ^ 2 * deriv centralRadius x)
    (hheight : (fun t => u (centralRadius t)) =ᶠ[𝓝 x]
      (fun t => ψ t / centralDensityRoot t)) :
    w (centralRadius x) * deriv u (centralRadius x) =
      lam * centralDensityRoot x * (deriv ψ x + centralRadiusA * ψ x) := by
  have h := liouville_flux_at
    (contDiff_centralRadius.differentiable (by simp) x)
    (contDiff_centralDensityRoot.differentiable (by simp) x)
    hψ hu (centralDensityRoot_pos x).ne' hw hheight
  rw [deriv_centralDensityRoot] at h
  calc
    _ = lam * (centralDensityRoot x * deriv ψ x -
        (-centralRadiusA * centralDensityRoot x) * ψ x) := h
    _ = _ := by ring

/-- The formula is stated for genuine radial columns related to the
model columns near the cuts. Only the local regularity supplied by
R09 is used. The input model columns have unit Dirichlet traces. -/
theorem innerCentral_radialFlux_matrix
    (lam : ℝ) (cuts : Fin 2 → ℝ) (w : ℝ → ℝ)
    (p u : Fin 2 → ℝ → ℝ)
    (hp : ∀ i k, DifferentiableAt ℝ (p k) (cuts i))
    (hu : ∀ i k, DifferentiableAt ℝ (u k) (centralRadius (cuts i)))
    (hw : ∀ i, w (centralRadius (cuts i)) =
      lam * centralDensityRoot (cuts i) ^ 2 * deriv centralRadius (cuts i))
    (hheight : ∀ i k, (fun t => u k (centralRadius t)) =ᶠ[𝓝 (cuts i)]
      (fun t => (centralDensityRoot (cuts k) * p k t) / centralDensityRoot t))
    (htrace : ∀ k i, p k (cuts i) = if k = i then 1 else 0) :
    Matrix.of (fun i k => bufferSign i * w (centralRadius (cuts i)) *
        deriv (u k) (centralRadius (cuts i))) =
      lam • (Matrix.diagonal (fun i => centralDensityRoot (cuts i)) *
        Matrix.of (fun i k => bufferSign i * deriv (p k) (cuts i)) *
        Matrix.diagonal (fun i => centralDensityRoot (cuts i))) +
      (lam * centralRadiusA) • Matrix.diagonal
        (fun i => bufferSign i * centralDensityRoot (cuts i) ^ 2) := by
  ext i k
  have hd : deriv (fun t => centralDensityRoot (cuts k) * p k t) (cuts i) =
      centralDensityRoot (cuts k) * deriv (p k) (cuts i) :=
    ((hp i k).hasDerivAt.const_mul (centralDensityRoot (cuts k))).deriv
  have hF := innerCentral_flux_at
    ((hp i k).const_mul (centralDensityRoot (cuts k))) (hu i k) (hw i) (hheight i k)
  rw [hd] at hF
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  calc
    _ = bufferSign i * (lam * centralDensityRoot (cuts i) *
        (centralDensityRoot (cuts k) * deriv (p k) (cuts i) +
          centralRadiusA * (centralDensityRoot (cuts k) * p k (cuts i)))) := by
      calc
        _ = bufferSign i *
            (w (centralRadius (cuts i)) * deriv (u k) (centralRadius (cuts i))) := by ring
        _ = _ := congrArg (fun z : ℝ => bufferSign i * z) hF
    _ = _ := by
      rw [htrace k i]
      by_cases hik : i = k
      · subst k
        simp only [eq_self_iff_true, ite_true]
        ring
      · simp only [if_neg hik, if_neg (Ne.symm hik)]
        ring

/-- The central reference diagonal, with the exact density drift. -/
def innerCentralKappa (lam : ℝ) (cuts αin : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  lam * centralDensityRoot (cuts i) ^ 2 *
    (αin i + bufferSign i * centralRadiusA)

/-- Splitting the model flux into its leading diagonal and its error
leaves precisely kappa on the radial diagonal. -/
theorem innerCentral_radialFlux_split (lam : ℝ) (cuts αin : Fin 2 → ℝ)
    (E : Matrix (Fin 2) (Fin 2) ℝ) :
    lam • (Matrix.diagonal (fun i => centralDensityRoot (cuts i)) *
        (Matrix.diagonal αin + E) *
        Matrix.diagonal (fun i => centralDensityRoot (cuts i))) +
      (lam * centralRadiusA) • Matrix.diagonal
        (fun i => bufferSign i * centralDensityRoot (cuts i) ^ 2) =
      Matrix.diagonal (innerCentralKappa lam cuts αin) +
        lam • (Matrix.diagonal (fun i => centralDensityRoot (cuts i)) * E *
          Matrix.diagonal (fun i => centralDensityRoot (cuts i))) := by
  ext i k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hik : i = k
  · subst k
    simp only [eq_self_iff_true, ite_true, innerCentralKappa]
    ring
  · simp only [if_neg hik]
    ring

/-- One scalar estimate treats both outward signs. -/
theorem innerCentral_drift_bounds (i : Fin 2) {α : ℝ}
    (hα : 2 * centralRadiusA ≤ α) :
    0 < α + bufferSign i * centralRadiusA ∧
      α / 2 ≤ α + bufferSign i * centralRadiusA ∧
      α + bufferSign i * centralRadiusA ≤ 3 * α / 2 := by
  have habs : |bufferSign i * centralRadiusA| = centralRadiusA := by
    rw [abs_mul, abs_bufferSign, one_mul, abs_of_pos centralRadiusA_pos]
  have hb := abs_le.mp habs.le
  refine ⟨?_, ?_, ?_⟩
  · linarith [centralRadiusA_pos]
  · linarith
  · linarith

/-- Positivity and comparison follow from the R09 mass bounds after
the far cut absorbs the fixed density drift. -/
theorem innerCentralKappa_compare {lam C m : ℝ} (cuts αin : Fin 2 → ℝ) (i : Fin 2)
    (hlam : 0 < lam) (hC : 0 < C) (hm : 0 < m)
    (hlo : m / C ≤ αin i) (hhi : αin i ≤ C * m)
    (hfar : 2 * C * centralRadiusA ≤ m) :
    0 < innerCentralKappa lam cuts αin i ∧
      (lam * centralDensityRoot (cuts i) ^ 2) * (m / (2 * C)) ≤
        innerCentralKappa lam cuts αin i ∧
      innerCentralKappa lam cuts αin i ≤
        (lam * centralDensityRoot (cuts i) ^ 2) * (2 * C * m) ∧
      (lam * centralDensityRoot (cuts i) ^ 2) * αin i ≤
        2 * innerCentralKappa lam cuts αin i := by
  have hlo' : m ≤ αin i * C := (div_le_iff₀ hC).mp hlo
  have hα : 2 * centralRadiusA ≤ αin i := by
    by_contra hn
    have hlt : αin i < 2 * centralRadiusA := lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_right hlt hC
    nlinarith only [hfar, hlo', hmul]
  have hd := innerCentral_drift_bounds i hα
  have hscale : 0 < lam * centralDensityRoot (cuts i) ^ 2 :=
    mul_pos hlam (sq_pos_of_pos (centralDensityRoot_pos _))
  have hlow : m / (2 * C) ≤ αin i / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
    nlinarith only [hlo']
  have hupp : αin i + bufferSign i * centralRadiusA ≤ 2 * C * m := by
    have hCm : 0 ≤ C * m := (mul_pos hC hm).le
    nlinarith only [hd.2.2, hhi, hCm]
  have hlead := mul_le_mul_of_nonneg_left hd.2.1 hscale.le
  refine ⟨mul_pos hscale hd.1,
    mul_le_mul_of_nonneg_left (hlow.trans hd.2.1) hscale.le,
    mul_le_mul_of_nonneg_left hupp hscale.le, ?_⟩
  unfold innerCentralKappa
  nlinarith only [hlead]

end ContinuousFlexibility.Radial
