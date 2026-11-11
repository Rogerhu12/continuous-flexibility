import ContinuousFlexibility.Analysis.N01cFlowHighestVariation
import ContinuousFlexibility.Analysis.N01cFlowParameterJetEquations

/-!
# The recursively constructed variations are the actual parameter jets

On finite-dimensional parameter restrictions, the classical ODE has
already supplied genuine joint smoothness. Its actual iterated Fréchet
derivatives obey the differentiated time equation. The exact highest-term
splitting and scalar ODE uniqueness then identify every one of them with
the recursively constructed continuous multilinear Volterra map.

No differentiability or derivative bound for the flow is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

section JetAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual parameter derivatives form jointly continuous
multilinear evaluation families, by already proved joint smoothness. -/
def canonicalFlowVariation {Θ : E × ℝ → ℝ} (hΘ : ContDiff ℝ ∞ Θ)
    (n : ℕ) : ContinuousStateVariation (univ : Set E) n where
  value p := iteratedFDeriv ℝ n (fun x => Θ (x, p.2)) p.1
  continuous := by
    have hc : Continuous (fun p : (E × ℝ) × (Fin n → E) =>
        iteratedFDeriv ℝ n Θ p.1 (fun i => (p.2 i, 0))) :=
      ((hΘ.continuous_iteratedFDeriv (by simp)).comp continuous_fst).eval
        (continuous_pi (fun i =>
          ((continuous_apply i).comp continuous_snd).prodMk continuous_const))
    simpa only [iteratedFDeriv_parameter_slice hΘ] using hc.continuousOn

/-- At positive order the graph jet has the identity parameter term
only in degree one, and the actual scalar variation in its angle slot. -/
theorem iteratedFDeriv_parameter_graph {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) {n : ℕ} (hn : 0 < n) (q : E) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun x => (x, f x)) q v =
      flowGraphVariationSlot n (iteratedFDeriv ℝ n f q) v := by
  have hid : iteratedFDeriv ℝ n (id : E → E) q =
      continuousLinearJets (ContinuousLinearMap.id ℝ E) n q :=
    ((hasProjectiveJetsOn_continuousLinear (ContinuousLinearMap.id ℝ E) univ).eq_iteratedFDeriv_finiteDimensional isOpen_univ n (mem_univ q)).symm
  change iteratedFDeriv ℝ n (fun x => ((id : E → E) x, f x)) q v = _
  rw [iteratedFDeriv_prodMk (contDiffAt_id : ContDiffAt ℝ ∞ (id : E → E) q)
    hf.contDiffAt (by simp)]
  change (iteratedFDeriv ℝ n (id : E → E) q v, iteratedFDeriv ℝ n f q v) = _
  rw [hid]
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      change (v 0, iteratedFDeriv ℝ 1 f q v) =
        (v 0, 0) + (0, iteratedFDeriv ℝ 1 f q v)
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    | succ n =>
      change (0, iteratedFDeriv ℝ (n + 2) f q v) =
        (0 : E × ℝ) + (0, iteratedFDeriv ℝ (n + 2) f q v)
      rw [zero_add]

/-- The genuine parameter derivative of the composed speed is the
ordered-partition sum of the actual speed and actual trajectory jets. -/
theorem iteratedFDeriv_speed_along_flow_eq_partitionSum
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ}
    (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hΘ : ContDiff ℝ ∞ Θ) (n : ℕ) (q : E) (t : ℝ) (v : Fin n → E) :
    iteratedFDeriv ℝ n (fun x => G (x, (t, Θ (x, t)))) q v =
      ∑ c : _root_.OrderedFinpartition n,
        J.D c.length (flowTrajectoryGraph Θ (q, t))
          (fun i => flowGraphVariationSlot (c.partSize i)
            ((canonicalFlowVariation hΘ (c.partSize i)).value (q, t)) (v ∘ c.emb i)) := by
  let f : E → E × ℝ := fun x => (x, Θ (x, t))
  let g : E × ℝ → ℝ := fun y => G (y.1, (t, y.2))
  have hslice : ContDiff ℝ ∞ (fun x => Θ (x, t)) :=
    hΘ.comp (contDiff_id.prodMk contDiff_const)
  have hf : ContDiff ℝ ∞ f := contDiff_id.prodMk hslice
  have hg : ContDiffOn ℝ ∞ g ((univ : Set E) ×ˢ (univ : Set ℝ)) :=
    smoothDirections_contDiffOn_finiteDimensional (J.jet t)
  have hj := hasProjectiveJetsOn_contDiff_comp isOpen_univ
    (isOpen_univ.prod isOpen_univ)
    (hasProjectiveJetsOn_of_contDiffOn isOpen_univ hf.contDiffOn) hg
    (fun x _ => ⟨mem_univ x, mem_univ _⟩)
  have he := congrArg (fun B : E [×n]→L[ℝ] ℝ => B v)
    (hj.eq_iteratedFDeriv_finiteDimensional isOpen_univ n (mem_univ q))
  have hs : iteratedFDeriv ℝ n (g ∘ f) q v =
      ∑ c : _root_.OrderedFinpartition n,
        iteratedFDeriv ℝ c.length g (f q)
          (fun i => iteratedFDeriv ℝ (c.partSize i) f q (v ∘ c.emb i)) := by
    simpa only [projectiveCompositionJets_apply, projectiveCompositionTerm_apply] using he.symm
  change iteratedFDeriv ℝ n (g ∘ f) q v = _
  rw [hs]
  apply Finset.sum_congr rfl
  intro c _
  have ho := (J.jet t).hasProjectiveJetsOn.eq_iteratedFDeriv_finiteDimensional
    (J.jet t).open_domain c.length (x := f q) ⟨mem_univ _, mem_univ _⟩
  change (J.jet t).D c.length (f q) = iteratedFDeriv ℝ c.length g (f q) at ho
  rw [← ho]
  change (J.jet t).D c.length (f q) _ = (J.jet t).D c.length (f q) _
  congr 1
  funext i
  exact iteratedFDeriv_parameter_graph hslice (c.partSize_pos i) q (v ∘ c.emb i)

end JetAlgebra

section GlobalTrajectory

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- True finite-parameter jets obey the same linear equation as the
Volterra recursion, with the explicit strictly lower-order forcing. -/
theorem globalCircleVectorTrajectory_parameterJet_linearODE
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    {n : ℕ} (hn : 0 < n) (q : E) (t : ℝ) (v : Fin n → E) :
    HasDerivAt (fun r => iteratedFDeriv ℝ n (fun x => Θ (x, r)) q v)
      (speedAlongFlowAngularJet J Θ (q, t) *
          iteratedFDeriv ℝ n (fun x => Θ (x, t)) q v +
        truncatedFlowForcing J Θ
          (fun k (_ : k < n) => canonicalFlowVariation
            (contDiff_globalCircleVectorTrajectory hG hΘ hinit hflow) k) (q, t) v) t := by
  have hs := contDiff_globalCircleVectorTrajectory hG hΘ hinit hflow
  have hR := (iteratedFDeriv_speed_along_flow_eq_partitionSum J hs n q t v).trans
    (flowJetComposition_eq_linear_add_truncated J Θ (canonicalFlowVariation hs)
      hn (q, t) v)
  exact (globalCircleVectorTrajectory_hasDerivAt_parameterJet_time
    hG hΘ hinit hflow n q t v).congr_deriv hR

/-- On finite-dimensional parameter spaces, every recursively constructed
variation is the actual iterated Fréchet derivative of the trajectory. -/
theorem volterraStateVariation_eq_iteratedFDeriv
    {G : E × PolarPoint → ℝ} {Θ : E × ℝ → ℝ} {θ₀ : ℝ}
    (J : ContinuousTimeSpeedTower (univ : Set E) G)
    (hG : ContDiff ℝ ∞ G) (hΘ : Continuous Θ)
    (hinit : ∀ q : E, Θ (q, 0) = θ₀)
    (hflow : ∀ q : E, ∀ t : ℝ,
      HasDerivAt (fun r => Θ (q, r)) (G (q, (t, Θ (q, t)))) t)
    (n : ℕ) (p : E × ℝ) :
    (volterraStateVariation J hΘ.continuousOn n).value p =
      iteratedFDeriv ℝ n (fun x => Θ (x, p.2)) p.1 := by
  have hs := contDiff_globalCircleVectorTrajectory hG hΘ hinit hflow
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    cases n with
    | zero =>
      apply ContinuousMultilinearMap.ext
      intro v
      rw [show v = Fin.elim0 from Subsingleton.elim _ _,
        volterraStateVariation_zero_apply]
      exact (iteratedFDeriv_zero_apply (𝕜 := ℝ)
        (f := fun x : E => Θ (x, p.2)) (x := p.1) Fin.elim0).symm
    | succ n =>
      apply ContinuousMultilinearMap.ext
      intro v
      have hforcing (r : ℝ) :
          truncatedFlowForcing J Θ
            (fun k (_ : k < n + 1) => canonicalFlowVariation hs k) (p.1, r) v =
          truncatedFlowForcing J Θ
            (fun k (_ : k < n + 1) =>
              volterraStateVariation J hΘ.continuousOn k) (p.1, r) v := by
        simp only [truncatedFlowForcing_apply]
        apply Finset.sum_congr rfl
        intro c _
        congr 1
        funext i
        by_cases hi : c.partSize i < n + 1
        · rw [lowerStateVariation_of_lt _ hi, lowerStateVariation_of_lt _ hi]
          rw [ih (c.partSize i) hi (p.1, r)]
          rfl
        · simp only [lowerStateVariation, dif_neg hi]
      have hy (r : ℝ) := globalCircleVectorTrajectory_parameterJet_linearODE
        J hG hΘ hinit hflow (Nat.succ_pos n) p.1 r v
      have hy' (r : ℝ) :
          HasDerivAt (fun s => iteratedFDeriv ℝ (n + 1) (fun x => Θ (x, s)) p.1 v)
            (speedAlongFlowAngularJet J Θ (p.1, r) *
                iteratedFDeriv ℝ (n + 1) (fun x => Θ (x, r)) p.1 v +
              truncatedFlowForcing J Θ
                (fun k (_ : k < n + 1) =>
                  volterraStateVariation J hΘ.continuousOn k) (p.1, r) v) r := by
        simpa only [hforcing r] using hy r
      exact (volterraStateVariation_succ_unique J hΘ.continuousOn n (mem_univ p.1) v
        (globalCircleVectorTrajectory_parameterJet_initial hinit n p.1 v) hy' p.2).symm

end GlobalTrajectory

end ContinuousFlexibility.Analysis

