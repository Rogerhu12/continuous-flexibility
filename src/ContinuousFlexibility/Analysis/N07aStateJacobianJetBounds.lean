import ContinuousFlexibility.Analysis.N07aStateSampleJetComposition
import ContinuousFlexibility.Geometry.EuclideanRigidity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# State-dependent Jacobian jets from positive coordinate jets

Each differential component uses one extra coordinate derivative. The
two determinant products are estimated on one common low-order ball.
The absolute value preserves every local jet bound at a nonzero Jacobian.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}

theorem N07aStateSampleJetBounds.congr
    {p : ℕ → Seminorm ℝ E} {U : Set E} {W : E → ℕ → Set PolarPoint}
    {d : ℕ} {f g : E → ℕ → PolarPoint → ℝ}
    (hf : N07aStateSampleJetBounds T K p U W d f)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (he : ∀ z ∈ U, ∀ m, EqOn (f z m) (g z m) (W z m)) :
    N07aStateSampleJetBounds T K p U W d g := by
  intro i j
  obtain ⟨e, hes, he0, heb⟩ := hf i j
  refine ⟨e, hes, he0, fun z hz m x hx => ?_⟩
  rw [← n07a_mixedDerivative_eqOn (hW z hz m) (he z hz m) i j hx]
  exact heb z hz m x hx

theorem N07aStateSampleJetBounds.abs
    {p : ℕ → Seminorm ℝ E} {U : Set E} {W : E → ℕ → Set PolarPoint}
    {d : ℕ} {f : E → ℕ → PolarPoint → ℝ}
    (hf : N07aStateSampleJetBounds T K p U W d f)
    (hfc : ∀ z ∈ U, ∀ m x, x ∈ W z m → ContinuousAt (f z m) x)
    (hne : ∀ z ∈ U, ∀ m x, x ∈ W z m → f z m x ≠ 0) :
    N07aStateSampleJetBounds T K p U W d (fun z m x => |f z m x|) := by
  intro i j
  obtain ⟨e, he, he0, heb⟩ := hf i j
  refine ⟨e, he, he0, fun z hz m x hx => ?_⟩
  rcases lt_or_gt_of_ne (hne z hz m x hx) with hneg | hpos
  · have hnear : ∀ᶠ y in 𝓝 x, f z m y < 0 :=
      (hfc z hz m x hx).eventually (Iio_mem_nhds hneg)
    have heq : (fun y => |f z m y|) =ᶠ[𝓝 x] (fun y => (-1 : ℝ) * f z m y) := by
      filter_upwards [hnear] with y hy
      simpa only [neg_one_mul] using abs_of_neg hy
    rw [n07a_mixedDerivative_eventuallyEq heq i j, spaces_mixedDerivative_const_mul, abs_mul]
    simpa only [abs_neg, abs_one, one_mul] using heb z hz m x hx
  · have hnear : ∀ᶠ y in 𝓝 x, 0 < f z m y :=
      (hfc z hz m x hx).eventually (Ioi_mem_nhds hpos)
    have heq : (fun y => |f z m y|) =ᶠ[𝓝 x] f z m := by
      filter_upwards [hnear] with y hy
      exact abs_of_pos hy
    rw [n07a_mixedDerivative_eventuallyEq heq i j]
    exact heb z hz m x hx

theorem n07a_stateDirectionalComponent_sampleJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (U : Set E) (W : E → ℕ → Set PolarPoint)
    (F : E → ℕ → PolarPoint → PolarPoint) (d : ℕ)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hFs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (F z m) (W z m))
    (hF : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (F z m) x‖ ≤ e m * (1 + p ((n - 1) + d) z))
    (v : PolarPoint) (A : PolarPoint →L[ℝ] ℝ) :
    N07aStateSampleJetBounds T K p U W d (fun z m x => A (fderiv ℝ (F z m) x v)) := by
  intro a b
  let n := a + b
  obtain ⟨e, he, he0, heb⟩ := hF (n + 1) (Nat.succ_pos n)
  refine ⟨fun m => (‖A‖ * ‖v‖) * e m,
    N07aSampleSubpower.mul hD hT (N07aSampleSubpower.const hD hT (‖A‖ * ‖v‖)) he,
    fun m => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (he0 m), ?_⟩
  intro z hz m x hx
  have hds : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (F z m) y v) (W z m) := by
    intro y hy
    exact ((((hFs z hz m).contDiffAt ((hW z hz m).mem_nhds hy)).fderiv_right
      (by simp)).clm_apply (contDiffAt_const (c := v))).contDiffWithinAt
  have hAs : ContDiffOn ℝ ∞ (fun y => A (fderiv ℝ (F z m) y v)) (W z m) :=
    A.contDiff.contDiffOn.comp hds (mapsTo_univ _ _)
  have hd := (hds.contDiffAt ((hW z hz m).mem_nhds hx))
  have hA := A.norm_iteratedFDeriv_comp_left hd (n := n) (by simp)
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ (F z m)) x :=
    ((hFs z hz m).contDiffAt ((hW z hz m).mem_nhds hx)).fderiv_right (by simp)
  have hdir := norm_iteratedFDeriv_clm_apply_const (c := v) (n := n) hfd (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hdir
  have hbnd := heb z hz m x hx
  simp only [Nat.add_sub_cancel] at hbnd
  apply (n07a_mixedDerivative_norm_le_iteratedFDeriv (hW z hz m) hAs a b hx).trans
  exact hA.trans ((mul_le_mul_of_nonneg_left hdir (norm_nonneg A)).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbnd (norm_nonneg v))
      (norm_nonneg A)).trans_eq (by dsimp only [n]; ring)))

theorem n07a_statePlaneJacobian_sampleJets
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (hIp : HasSmoothing p)
    (U : Set E) (W : E → ℕ → Set PolarPoint)
    (F : E → ℕ → PolarPoint → PolarPoint) (d : ℕ)
    (hW : ∀ z ∈ U, ∀ m, IsOpen (W z m))
    (hFs : ∀ z ∈ U, ∀ m, ContDiffOn ℝ ∞ (F z m) (W z m))
    (hF : ∀ n : ℕ, 0 < n → ∃ e : ℕ → ℝ,
      N07aSampleSubpower T K e ∧ (∀ m, 0 ≤ e m) ∧
        ∀ z ∈ U, ∀ m x, x ∈ W z m →
          ‖iteratedFDeriv ℝ n (F z m) x‖ ≤ e m * (1 + p ((n - 1) + d) z)) :
    ∃ low loss : ℕ,
      N07aStateSampleJetBounds T K p {z | z ∈ U ∧ p low z ≤ 1} W loss
        (fun z m => planeJacobian (F z m)) := by
  let R := fun z m x => fderiv ℝ (F z m) x ((1, 0) : PolarPoint)
  let A := fun z m x => fderiv ℝ (F z m) x ((0, 1) : PolarPoint)
  have hs (v : PolarPoint) (z : E) (hz : z ∈ U) (m : ℕ) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (F z m) x v) (W z m) := by
    intro x hx
    exact ((((hFs z hz m).contDiffAt ((hW z hz m).mem_nhds hx)).fderiv_right
      (by simp)).clm_apply (contDiffAt_const (c := v))).contDiffWithinAt
  have hR₁ := n07a_stateDirectionalComponent_sampleJets hD hT p U W F d hW hFs hF
    (1, 0) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hR₂ := n07a_stateDirectionalComponent_sampleJets hD hT p U W F d hW hFs hF
    (1, 0) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hA₁ := n07a_stateDirectionalComponent_sampleJets hD hT p U W F d hW hFs hF
    (0, 1) (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hA₂ := n07a_stateDirectionalComponent_sampleJets hD hT p U W F d hW hFs hF
    (0, 1) (ContinuousLinearMap.snd ℝ ℝ ℝ)
  obtain ⟨low, loss, hprod⟩ := n07a_stateSampleJetBounds_mul_uniform hD hT p hp hIp U W hW d
  have hP := hprod (fun z m x => (R z m x).1) (fun z m x => (A z m x).2)
    hR₁ hA₂ (fun z hz m => (hs (1, 0) z hz m).fst) (fun z hz m => (hs (0, 1) z hz m).snd)
  have hQ := hprod (fun z m x => (R z m x).2) (fun z m x => (A z m x).1)
    hR₂ hA₁ (fun z hz m => (hs (1, 0) z hz m).snd) (fun z hz m => (hs (0, 1) z hz m).fst)
  have hnQ := hQ.const_mul hD hT (-1)
  have hsum := hP.add hnQ (fun z hz => hW z hz.1)
    (fun z hz m => ((hs (1, 0) z hz.1 m).fst).mul ((hs (0, 1) z hz.1 m).snd))
    (fun z hz m => contDiffOn_const.mul
      (((hs (1, 0) z hz.1 m).snd).mul ((hs (0, 1) z hz.1 m).fst)))
  refine ⟨low, loss, hsum.congr (fun z hz => hW z hz.1) ?_⟩
  intro z hz m x hx
  simp only [R, A, planeJacobian, sub_eq_add_neg, neg_one_mul]

end ContinuousFlexibility.Analysis
