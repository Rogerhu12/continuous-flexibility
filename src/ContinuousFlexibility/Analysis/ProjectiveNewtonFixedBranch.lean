import ContinuousFlexibility.Analysis.ProjectiveNewtonLimit
import ContinuousFlexibility.Analysis.ProjectiveNewtonRapidDecay

/-!
# The fixed-parameter Newton limit for the original hypotheses

The common iteration converges in the actual projective topology for
every parameter in a single interval. This gives the zero of the actual
residual and its initial value. Parameter derivatives require additional
estimates on that same iteration.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

theorem exists_projectiveNewton_fixed_branch
    {E F : ℕ → Type*}
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, CompleteSpace (E n)]
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace ℝ (F n)]
    {e : ∀ n, E (n + 1) →L[ℝ] E n} {f : ∀ n, F (n + 1) →L[ℝ] F n}
    (x₀ : ProjectiveLimit E e) (b₀ : ℕ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    {U : Set (ProjectiveLimit E e × ℝ)}
    (hU : U = {z | gradedSeminorm E e b₀ (z.1 - x₀) < ε₀ ∧ |z.2| < ε₀})
    (R : ProjectiveLimit E e × ℝ → ProjectiveLimit F f)
    (V : ProjectiveLimit E e × ℝ → ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit E e)
    (Q : ProjectiveLimit E e × ℝ →
      ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit F f →ₗ[ℝ] ProjectiveLimit F f)
    (hzero : R (x₀, 0) = 0)
    (hRight : ∀ z ∈ U, ∀ y, HasProjectiveLineDerivAt (fun x => R (x, z.2))
      (y + Q z (R z) y) z.1 (V z y)) :
    let p := gradedSeminorm E e
    let q := gradedSeminorm F f
    let a := Statements.pairGrading p Statements.realGrading
    Statements.HasSmoothing p → Statements.HasSmoothing q →
    Statements.SmoothTameOn a q U R →
    Statements.SmoothTameOn (Statements.pairGrading a q) p (U ×ˢ univ)
      (fun z : (ProjectiveLimit E e × ℝ) × ProjectiveLimit F f => V z.1 z.2) →
    Statements.SmoothTameOn (Statements.pairGrading (Statements.pairGrading a q) q)
      q ((U ×ˢ univ) ×ˢ univ)
      (fun z : ((ProjectiveLimit E e × ℝ) × ProjectiveLimit F f) × ProjectiveLimit F f =>
        Q z.1.1 z.1.2 z.2) →
    ∃ SX : ℕ → ProjectiveLimit E e →L[ℝ] ProjectiveLimit E e,
      ∃ N₀ : ℕ, ∃ q₀ : ℝ, 0 < q₀ ∧ ∃ x : ℝ → ProjectiveLimit E e, x 0 = x₀ ∧
        ∀ τ, |τ| < q₀ →
          Tendsto (projectiveSmoothedNewtonIterates R V SX (newtonSmoothingIndex N₀) (x₀, τ))
            atTop (𝓝 (x τ, τ)) ∧ (x τ, τ) ∈ U ∧ R (x τ, τ) = 0 := by
  dsimp only
  intro hSX hSY hR hV hQ
  let X := ProjectiveLimit E e
  let p := gradedSeminorm E e
  let q := gradedSeminorm F f
  have hp := gradedSeminorm_monotone E e
  have hq := gradedSeminorm_monotone F f
  obtain ⟨bMin, hsep⟩ := exists_separating_grade_of_hasSmoothing
    (withSeminorms_graded F f) hq hSY
  obtain ⟨SX, b, l, σ, N₀, q₀, μ, hbMin, hb₀, hN₀, hq₀, hqμ, hμ, hμε₀,
    hiter, D, hD, _, hinc⟩ :=
    exists_projectiveNewton_summable_iterates p hp x₀ b₀ bMin ε₀ hε₀ hU
      R V Q hzero hRight hSX hSY hR hV hQ
  obtain ⟨J, _⟩ := hR
  have hRcont : ContinuousOn R U := by
    have hc : Continuous (fun z : X × ℝ => (z, (Fin.elim0 : Fin 0 → X × ℝ))) :=
      continuous_id.prodMk continuous_const
    exact ((J.continuous 0).comp hc.continuousOn
      (fun z hz => ⟨hz, mem_univ _⟩)).congr (fun z hz => (J.zero z hz).symm)
  let N := newtonSmoothingIndex N₀
  have hpoint (τ : ℝ) (hτ : |τ| < q₀) : ∃ x : X,
      Tendsto (projectiveSmoothedNewtonIterates R V SX N (x₀, τ)) atTop (𝓝 (x, τ)) ∧
        (x, τ) ∈ U ∧ R (x, τ) = 0 := by
    let z := projectiveSmoothedNewtonIterates R V SX N (x₀, τ)
    let α₀ : ℝ := 4 * (l : ℝ) + 4 * (σ : ℝ) + 2
    have hα : 0 < α₀ := by positivity
    have hμlt : μ < ε₀ := by linarith only [hμ, hμε₀]
    have hb : b₀ ≤ b + l + l := by omega
    have hsep' : ∀ y, q (b + l) y = 0 → y = 0 := hsep _ (by omega)
    have hsum (s : ℕ) : Summable (fun n => p s (SX (N n) (V (z n) (R (z n))))) := by
      refine Summable.of_nonneg_of_le (f := D s) (fun _ => apply_nonneg _ _) ?_ (hD s)
      intro n
      have h := hinc s n τ hτ
      let c := SX (N n) (V (z n) (R (z n)))
      change p s ((z n).1 - c - (z n).1) ≤ D s n at h
      rw [show (z n).1 - c - (z n).1 = -c by abel, map_neg_eq_map] at h
      exact h
    have hclosed (n : ℕ) : p b₀ ((z n).1 - x₀) ≤ μ ∧ |(z n).2| ≤ μ := by
      obtain ⟨_, hparam, hdisp, _⟩ := hiter τ hτ n
      refine ⟨(hp hb _).trans hdisp.le, ?_⟩
      rw [hparam]
      exact hτ.le.trans hqμ
    have hdecay : Tendsto (fun n => q (b + l) (R (z n))) atTop (𝓝 0) :=
      squeeze_zero (fun _ => apply_nonneg _ _) (fun n => (hiter τ hτ n).2.2.2)
        (newton_summable_exponential hN₀ hα).tendsto_atTop_zero
    rw [hU] at hRcont ⊢
    exact exists_projectiveSmoothedNewton_limit_zero R V SX N (x₀, τ) (p b₀)
      (continuous_gradedSeminorm E e b₀) x₀ hμlt (q (b + l))
      (continuous_gradedSeminorm F f (b + l)) hsep' hRcont hsum hclosed hdecay
  let x : ℝ → X := fun τ => if hτ : |τ| < q₀ then (hpoint τ hτ).choose else x₀
  have hx (τ : ℝ) (hτ : |τ| < q₀) :
      Tendsto (projectiveSmoothedNewtonIterates R V SX N (x₀, τ)) atTop (𝓝 (x τ, τ)) ∧
        (x τ, τ) ∈ U ∧ R (x τ, τ) = 0 := by
    simpa only [x, dite_eq_left hτ] using (hpoint τ hτ).choose_spec
  have hstat (n : ℕ) : projectiveSmoothedNewtonIterates R V SX N (x₀, 0) n = (x₀, 0) := by
    induction n with
    | zero => rfl
    | succ n ih => simp [projectiveSmoothedNewtonIterates, projectiveSmoothedNewtonStep, ih, hzero]
  have hlim := (hx 0 (by simpa only [abs_zero] using hq₀)).1
  rw [show projectiveSmoothedNewtonIterates R V SX N (x₀, 0) = fun _ => (x₀, 0) from
    funext hstat] at hlim
  have heq : (x 0, (0 : ℝ)) = (x₀, 0) := tendsto_nhds_unique hlim tendsto_const_nhds
  exact ⟨SX, N₀, q₀, hq₀, x, congrArg Prod.fst heq, hx⟩

end ContinuousFlexibility.Analysis
