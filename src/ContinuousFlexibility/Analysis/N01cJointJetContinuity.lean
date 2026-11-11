import ContinuousFlexibility.Analysis.N01cReferenceDifferenceBounds
import ContinuousFlexibility.Analysis.ProjectiveMultilinearCalculus

/-!
# Joint jet evaluation continuity from the next actual derivative

The parameter source is a topological real module. A true next jet gives
the seminorm variation estimate by the ordinary scalar segment theorem.
An exact multilinear telescope treats simultaneous changes in all
direction slots. Thus finite-plane continuity in the external variables
and locally uniform seminorm bounds imply the joint continuity required
by the Volterra construction.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section Majorant

variable {Z : Type*} [TopologicalSpace Z]

/-- A continuous error bound which vanishes at the base point proves
continuity of the actual scalar function. -/
theorem continuousAt_of_eventually_abs_sub_le
    {f g : Z → ℝ} {z : Z} (hg : ContinuousAt g z) (hg0 : g z = 0)
    (hbound : ∀ᶠ y in 𝓝 z, |f y - f z| ≤ g y) : ContinuousAt f z := by
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝 z, g y < ε :=
    hg.eventually (Iio_mem_nhds (by simpa only [hg0] using hε))
  filter_upwards [hbound, hsmall] with y hy hys
  simpa only [Real.dist_eq] using hy.trans_lt hys

end Majorant

section UniformMultilinear

variable {E T : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace T]

/-- An exact continuous majorant for the multilinear telescope. No norm
is imposed on the direction space. -/
def multilinearSeminormDifferenceMajorant {n : ℕ}
    (p : Seminorm ℝ E) (C : ℝ) (v₀ v : Fin n → E) : ℝ :=
  ∑ i : Fin n, C * ∏ j : Fin n,
    p ((Function.update (multilinearReplaceBefore v₀ v i.val) i (v i - v₀ i)) j)

theorem continuous_multilinearSeminormDifferenceMajorant {n : ℕ}
    (p : Seminorm ℝ E) (hp : Continuous p) (C : ℝ) (v₀ : Fin n → E) :
    Continuous (multilinearSeminormDifferenceMajorant p C v₀) := by
  classical
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j _
  apply hp.comp
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_same] using (continuous_apply i).sub continuous_const
  · simp only [Function.update_of_ne hji, multilinearReplaceBefore]
    by_cases hlt : j.val < i.val
    · simpa only [if_pos hlt] using continuous_apply j
    · simpa only [if_neg hlt] using (continuous_const : Continuous (fun _ : Fin n → E => v₀ j))

theorem multilinearSeminormDifferenceMajorant_self {n : ℕ}
    (p : Seminorm ℝ E) (C : ℝ) (v₀ : Fin n → E) :
    multilinearSeminormDifferenceMajorant p C v₀ v₀ = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  have hp : (∏ j : Fin n,
      p ((Function.update (multilinearReplaceBefore v₀ v₀ i.val) i (v₀ i - v₀ i)) j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [Function.update_same, sub_self, map_zero])
  rw [hp, mul_zero]

theorem abs_multilinear_sub_le_seminormDifferenceMajorant {n : ℕ}
    (A : E [×n]→L[ℝ] ℝ) (p : Seminorm ℝ E) (C : ℝ)
    (hA : ∀ v, |A v| ≤ C * ∏ i, p (v i)) (v₀ v : Fin n → E) :
    |A v - A v₀| ≤ multilinearSeminormDifferenceMajorant p C v₀ v := by
  rw [multilinear_sub_eq_sum_updates]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => hA _))

/-- Pointwise continuity in the external index and a locally uniform
seminorm bound imply joint continuity of the genuine multilinear maps
and all their direction slots. -/
theorem continuousAt_multilinearEvaluation_of_uniform_seminormBound
    {n : ℕ} (A : T → E [×n]→L[ℝ] ℝ)
    (p : Seminorm ℝ E) (hp : Continuous p) (C : ℝ)
    {t₀ : T} (v₀ : Fin n → E)
    (hfixed : ContinuousAt (fun t => A t v₀) t₀)
    (hbound : ∀ᶠ t in 𝓝 t₀, ∀ v, |A t v| ≤ C * ∏ i, p (v i)) :
    ContinuousAt (fun z : T × (Fin n → E) => A z.1 z.2) (t₀, v₀) := by
  let M : (Fin n → E) → ℝ := multilinearSeminormDifferenceMajorant p C v₀
  let g : T × (Fin n → E) → ℝ := fun z => M z.2 + |A z.1 v₀ - A t₀ v₀|
  have hg : ContinuousAt g (t₀, v₀) :=
    ((continuous_multilinearSeminormDifferenceMajorant p hp C v₀).comp
      continuous_snd).continuousAt.add
        ((hfixed.comp continuousAt_fst).sub_const (A t₀ v₀)).abs
  have hg0 : g (t₀, v₀) = 0 := by
    simp only [g, M, multilinearSeminormDifferenceMajorant_self, sub_self, abs_zero, add_zero]
  apply continuousAt_of_eventually_abs_sub_le hg hg0
  have hnear := continuousAt_fst.eventually hbound
  filter_upwards [hnear] with z hz
  calc
    |A z.1 z.2 - A t₀ v₀| =
        |(A z.1 z.2 - A z.1 v₀) + (A z.1 v₀ - A t₀ v₀)| := by congr 1; ring
    _ ≤ |A z.1 z.2 - A z.1 v₀| + |A z.1 v₀ - A t₀ v₀| := abs_add _ _
    _ ≤ g z := add_le_add_right
      (abs_multilinear_sub_le_seminormDifferenceMajorant (A z.1) p C hz v₀ z.2) _

end UniformMultilinear

section ParameterVariation

variable {E T : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace T]

/-- Only the state changes in the first error term. The external
variables may include time, angle and all multilinear direction slots. -/
theorem continuousAt_of_uniform_seminorm_variation
    (f : E × T → ℝ) (p : Seminorm ℝ E) (hp : Continuous p)
    (B : T → ℝ) {x₀ : E} {t₀ : T} (hB : ContinuousAt B t₀)
    (hfixed : ContinuousAt (fun t => f (x₀, t)) t₀)
    (hbound : ∀ᶠ z in 𝓝 (x₀, t₀),
      |f z - f (x₀, z.2)| ≤ p (z.1 - x₀) * B z.2) :
    ContinuousAt f (x₀, t₀) := by
  let g : E × T → ℝ := fun z =>
    p (z.1 - x₀) * B z.2 + |f (x₀, z.2) - f (x₀, t₀)|
  have hg : ContinuousAt g (x₀, t₀) :=
    ((hp.continuousAt.comp (continuousAt_fst.sub_const x₀)).mul
      (hB.comp continuousAt_snd)).add
        ((hfixed.comp continuousAt_snd).sub_const (f (x₀, t₀))).abs
  have hg0 : g (x₀, t₀) = 0 := by
    simp only [g, sub_self, map_zero, zero_mul, abs_zero, add_zero]
  apply continuousAt_of_eventually_abs_sub_le hg hg0
  filter_upwards [hbound] with z hz
  calc
    |f z - f (x₀, t₀)| =
        |(f z - f (x₀, z.2)) + (f (x₀, z.2) - f (x₀, t₀))| := by congr 1; ring
    _ ≤ |f z - f (x₀, z.2)| + |f (x₀, z.2) - f (x₀, t₀)| := abs_add _ _
    _ ≤ g z := add_le_add_right hz _

/-- The next genuine parameter derivative controls an arbitrary fixed
jet along the actual segment. This is the scalar mean-value inequality
applied to the true directional recurrence, at every order. -/
theorem smoothDirections_jet_abs_sub_le_of_nextJet_bound
    {U : Set E} {f : E → ℝ} (J : SmoothDirections U f)
    (n : ℕ) (v : Fin n → E) {x d : E}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • d ∈ U) {M : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      |J.D (n + 1) (x + t • d) (Fin.cons d v)| ≤ M) :
    |J.D n (x + d) v - J.D n x v| ≤ M := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => J.D n (x + s • d) v)
        (J.D (n + 1) (x + t • d) (Fin.cons d v)) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have h := J.derivative n (x + t • d) (hseg t ht) v d
    simpa only [HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      zero_add, zero_smul, add_zero, add_smul, add_assoc] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hM t (Ico_subset_Icc_self ht))
  simpa only [one_smul, zero_smul, add_zero, Real.norm_eq_abs] using h

/-- A locally uniform bound on two consecutive actual jets upgrades
finite-plane continuity in the external variables to joint evaluation
continuity in the state, the external variables and all directions. -/
theorem continuousAt_stateJetEvaluation_of_nextJet_bound
    {U V : Set E} {W : Set T} {f : T → E → ℝ}
    (J : ∀ t, SmoothDirections U (f t))
    (p : Seminorm ℝ E) (hp : Continuous p) (C : ℝ)
    (n : ℕ) {x₀ : E} {t₀ : T} (v₀ : Fin n → E)
    (hV : IsOpen V) (hconv : Convex ℝ V) (hx₀ : x₀ ∈ V) (hVU : V ⊆ U)
    (hW : W ∈ 𝓝 t₀)
    (hfixed : ∀ v : Fin n → E, ContinuousAt (fun t => (J t).D n x₀ v) t₀)
    (hcurrent : ∀ t ∈ W, ∀ v : Fin n → E,
      |(J t).D n x₀ v| ≤ C * ∏ i, p (v i))
    (hnext : ∀ t ∈ W, ∀ x ∈ V, ∀ v : Fin (n + 1) → E,
      |(J t).D (n + 1) x v| ≤ C * ∏ i, p (v i)) :
    ContinuousAt (fun z : (E × T) × (Fin n → E) => (J z.1.2).D n z.1.1 z.2)
      ((x₀, t₀), v₀) := by
  have hfixedJoint : ContinuousAt
      (fun z : T × (Fin n → E) => (J z.1).D n x₀ z.2) (t₀, v₀) := by
    apply continuousAt_multilinearEvaluation_of_uniform_seminormBound
      (fun t => (J t).D n x₀) p hp C v₀ (hfixed v₀)
    filter_upwards [hW] with t ht
    exact hcurrent t ht
  let B : T × (Fin n → E) → ℝ := fun z => C * ∏ i, p (z.2 i)
  have hB : Continuous B := continuous_const.mul
    (continuous_finsetProd _ (fun i _ => hp.comp ((continuous_apply i).comp continuous_snd)))
  have hjoint : ContinuousAt
      (fun z : E × (T × (Fin n → E)) => (J z.2.1).D n z.1 z.2.2) (x₀, (t₀, v₀)) := by
    apply continuousAt_of_uniform_seminorm_variation
      (fun z : E × (T × (Fin n → E)) => (J z.2.1).D n z.1 z.2.2)
      p hp B hB.continuousAt hfixedJoint
    have hxnear := (continuousAt_fst : ContinuousAt
      (fun z : E × (T × (Fin n → E)) => z.1) (x₀, (t₀, v₀))).eventually (hV.mem_nhds hx₀)
    have htnear := ((continuousAt_fst.comp continuousAt_snd) : ContinuousAt
      (fun z : E × (T × (Fin n → E)) => z.2.1) (x₀, (t₀, v₀))).eventually hW
    filter_upwards [hxnear, htnear] with z hz ht
    have hseg (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
        x₀ + τ • (z.1 - x₀) ∈ V := hconv.add_smul_sub_mem hx₀ hz hτ
    have hb := smoothDirections_jet_abs_sub_le_of_nextJet_bound (J z.2.1) n z.2.2
      (fun τ hτ => hVU (hseg τ hτ))
      (M := p (z.1 - x₀) * B z.2)
      (fun τ hτ => by
        simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, B,
          mul_assoc, mul_left_comm, mul_comm] using
            hnext z.2.1 ht (x₀ + τ • (z.1 - x₀)) (hseg τ hτ)
              (Fin.cons (z.1 - x₀) z.2.2))
    have he : x₀ + (z.1 - x₀) = z.1 := by abel
    simpa only [he] using hb
  exact hjoint.comp ((continuous_fst.fst).prodMk
    ((continuous_fst.snd).prodMk continuous_snd)).continuousAt

end ParameterVariation

end ContinuousFlexibility.Analysis
