module

public import ContinuousFlexibility.Analysis.N01cFlowStateSmooth

/-!
# Vector-valued tower assembly from genuine finite affine germs

Continuous multilinear candidates that agree with the actual derivatives
on every finite affine slice satisfy the directional recurrence on the
original topological source. This is the vector-output version of the
existing scalar finite-affine assembly argument.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter Function ContinuousFlexibility.Statements
open scoped Topology ContDiff

variable {E Y : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem affineJet_at_point
    {U : Set E} {f : E → Y} (A : ProjectiveJetFamily E Y)
    (hjet : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ∀ n : ℕ, ∀ v : Fin n → (Fin m → ℝ),
        iteratedFDeriv ℝ n (fun q => f (x + L q)) 0 v =
          A n x (fun i => L (v i)))
    (m : ℕ) (x : E) (L : (Fin m → ℝ) →L[ℝ] E)
    (q : Fin m → ℝ) (hq : x + L q ∈ U) (n : ℕ) (v : Fin n → (Fin m → ℝ)) :
    iteratedFDeriv ℝ n (fun y => f (x + L y)) q v =
      A n (x + L q) (fun i => L (v i)) := by
  have he : (fun y => f ((x + L q) + L y)) =
      fun y => (fun z => f (x + L z)) (q + y) := by
    funext y
    change f ((x + L q) + L y) = f (x + L (q + y))
    rw [map_add, add_assoc]
  have h := hjet m (x + L q) hq L n v
  rw [he] at h
  rw [iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun z : Fin m → ℝ => f (x + L z)) n q (0 : Fin m → ℝ), add_zero] at h
  exact h

/-- One genuine all-order tower on the original parameter topology is
determined by its continuous multilinear finite-affine restrictions. -/
def n04NegativeGeometry_smoothDirections_of_finiteAffine_germs
    {U : Set E} {f : E → Y} (hU : IsOpen U) (A : ProjectiveJetFamily E Y)
    (hzero : ∀ x ∈ U, A 0 x Fin.elim0 = f x)
    (hcontinuous : ∀ n : ℕ, ContinuousOn
      (fun p : E × (Fin n → E) => A n p.1 p.2) (U ×ˢ univ))
    (hsmooth : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ContDiffAt ℝ ∞ (fun q => f (x + L q)) 0)
    (hjet : ∀ m : ℕ, ∀ x ∈ U, ∀ L : (Fin m → ℝ) →L[ℝ] E,
      ∀ n : ℕ, ∀ v : Fin n → (Fin m → ℝ),
        iteratedFDeriv ℝ n (fun q => f (x + L q)) 0 v =
          A n x (fun i => L (v i))) : SmoothDirections U f where
  open_domain := hU
  D := A
  zero := hzero
  continuous := hcontinuous
  derivative := by
    intro n x hx v w
    let P := Fin (n + 1) → ℝ
    let L : P →L[ℝ] E := finiteDirectionsLinear (Fin.cons w v)
    let e : P := Pi.single 0 1
    let a : Fin n → P := fun i => Pi.single i.succ 1
    let F : P → Y := fun q => f (x + L q)
    have he : L e = w := by
      change finiteDirectionsLinear (Fin.cons w v) (Pi.single (0 : Fin (n + 1)) 1) = w
      exact finiteDirectionsLinear_single (Fin.cons w v) (0 : Fin (n + 1))
    have ha : (fun i => L (a i)) = v := by
      funext i
      change finiteDirectionsLinear (Fin.cons w v) (Pi.single i.succ 1) = v i
      exact finiteDirectionsLinear_single (Fin.cons w v) i.succ
    have hcons : (fun i => L ((Fin.cons e a : Fin (n + 1) → P) i)) =
        Fin.cons w v := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using he
      · simpa only [Fin.cons_succ] using congrFun ha j
    have hline (s : ℝ) : x + L (s • e) = x + s • w := by rw [map_smul, he]
    have hF : ContDiffAt ℝ ∞ F 0 := hsmooth (n + 1) x hx L
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ n F) ((0 : ℝ) • e) := by
      simpa only [zero_smul] using
        hF.differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
    have hc : HasDerivAt (fun s : ℝ => s • e) e 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hd := (hD.continuousMultilinear_apply_const a).hasFDerivAt.comp_hasDerivAt 0 hc
    simp only [zero_smul] at hd
    rw [fderiv_continuousMultilinear_apply_const_apply
      (by simpa only [zero_smul] using hD)] at hd
    change HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n F (s • e) a)
      (iteratedFDeriv ℝ (n + 1) F 0 (Fin.cons e a)) 0 at hd
    have hnext := hjet (n + 1) x hx L (n + 1) (Fin.cons e a)
    rw [hcons] at hnext
    rw [hnext] at hd
    have hpath : Continuous (fun s : ℝ => x + s • w) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • w ∈ U := by
      have hUx : U ∈ 𝓝 ((fun s : ℝ => x + s • w) 0) := by
        simpa only [zero_smul, add_zero] using hU.mem_nhds hx
      exact hpath.continuousAt.preimage_mem_nhds hUx
    have heq : (fun s : ℝ => iteratedFDeriv ℝ n F (s • e) a) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => A n (x + s • w) v) := by
      filter_upwards [hnear] with s hs
      have hj := affineJet_at_point A hjet (n + 1) x L (s • e)
        (by simpa only [hline] using hs) n a
      simpa only [ha, hline] using hj
    exact (hd.congr_of_eventuallyEq heq.symm).tendsto_slope_zero

end ContinuousFlexibility.Analysis
