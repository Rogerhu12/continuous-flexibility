module

public import ContinuousFlexibility.Radial.TailPoissonInterpolationBounds
public import ContinuousFlexibility.Radial.TailEdgeGluing
public import ContinuousFlexibility.Radial.TailClassicalRegularity

/-!
# The actual differential equation of a matched node interpolant

The flux is represented by the derivative in resistance coordinates.
Consequently it has a classical derivative at both endpoints of every
closed edge. The actual node recurrence is exactly the matching condition
for these fluxes, and the existing outward gluing operation yields a
classical solution on the open tail.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

/-- The conormal flux of the same canonical physical interpolant. -/
def tailActualEdgeInterpolationFlux (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) (a b : ℝ) (x : ℝ) : ℝ :=
  a * deriv (tailActualEdgePoisson T hT n false) (tailActualEdgeChart T hT n x) +
    b * deriv (tailActualEdgePoisson T hT n true) (tailActualEdgeChart T hT n x)

theorem tailActualEdgePoissonPhysical_hasDerivAt {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    HasDerivAt (tailActualEdgePoissonPhysical T hT n right)
      (deriv (tailActualEdgePoisson T hT n right) (tailActualEdgeChart T hT n x) /
        T.p x) x := by
  have hchart : HasDerivAt (tailActualEdgeChart T hT n) (T.p x)⁻¹ x :=
    hasDerivAt_tailClampedResistanceChart (tailActualEdge_order hT n).le
      (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n) hx
  simpa only [tailActualEdgePoissonPhysical, div_eq_mul_inv] using
    (((tailActualEdgePoisson_spec hT n).differentiable right
      (tailActualEdgeChart T hT n x)).hasDerivAt.comp x hchart)

theorem tailActualEdgeInterpolation_hasDerivAt {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    HasDerivAt (tailActualEdgeInterpolation T hT n a b)
      (tailActualEdgeInterpolationFlux T hT n a b x / T.p x) x := by
  have h := ((tailActualEdgePoissonPhysical_hasDerivAt hT n false hx).const_mul a).fun_add
    ((tailActualEdgePoissonPhysical_hasDerivAt hT n true hx).const_mul b)
  exact h.congr_deriv (by dsimp only [tailActualEdgeInterpolationFlux]; ring)

theorem tailActualEdgeInterpolation_flux {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    T.p x * deriv (tailActualEdgeInterpolation T hT n a b) x =
      tailActualEdgeInterpolationFlux T hT n a b x := by
  rw [(tailActualEdgeInterpolation_hasDerivAt hT n a b hx).deriv]
  field_simp [(tailActualEdge_pos hT n x hx).ne']

theorem tailActualEdgeInterpolationFlux_hasDerivAt {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    HasDerivAt (tailActualEdgeInterpolationFlux T hT n a b)
      (-T.Λ * T.p x * tailActualEdgeInterpolation T hT n a b x) x := by
  have hchart : HasDerivAt (tailActualEdgeChart T hT n) (T.p x)⁻¹ x :=
    hasDerivAt_tailClampedResistanceChart (tailActualEdge_order hT n).le
      (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n) hx
  have hs := tailActualEdgeChart_mem hT n hx
  have h₀ := ((tailActualEdgePoisson_spec hT n).equation false _ hs).comp x hchart
  have h₁ := ((tailActualEdgePoisson_spec hT n).equation true _ hs).comp x hchart
  apply ((h₀.const_mul a).fun_add (h₁.const_mul b)).congr_deriv
  rw [tailActualEdgePotential_apply, tailActualEdgeWeight_chart hT n hx]
  dsimp only [tailActualEdgeInterpolation, tailActualEdgePoissonPhysical, Function.comp_apply]
  field_simp [(tailActualEdge_pos hT n x hx).ne'] <;> ring

theorem tailActualEdgeInterpolation_endpoints {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) :
    tailActualEdgeInterpolation T hT n a b (T.node n) = a ∧
      tailActualEdgeInterpolation T hT n a b (T.node (n + 1)) = b := by
  have h₀ := tailActualEdgePoissonPhysical_endpoint hT n false
  have h₁ := tailActualEdgePoissonPhysical_endpoint hT n true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₀ h₁
  simp only [tailActualEdgeInterpolation, h₀.1, h₀.2, h₁.1, h₁.2,
    mul_zero, mul_one, add_zero, zero_add, and_self]

theorem tailActualEdgeInterpolationFlux_endpoints {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (a b : ℝ) :
    tailActualEdgeInterpolationFlux T hT n a b (T.node n) =
        -tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) false * a +
          tailActualNodeCoupling T hT n * b ∧
      tailActualEdgeInterpolationFlux T hT n a b (T.node (n + 1)) =
        -tailActualNodeCoupling T hT n * a +
          tailActualEdgeDiagonal T hT n (tailActualEdgePoisson T hT n) true * b := by
  have h := tailActualEdgePoissonPhysical_flux hT n a b
  change -(T.p (T.node n) * deriv (tailActualEdgeInterpolation T hT n a b) (T.node n)) = _ ∧
    T.p (T.node (n + 1)) * deriv (tailActualEdgeInterpolation T hT n a b) (T.node (n + 1)) = _ at h
  rw [tailActualEdgeInterpolation_flux hT n a b
      ⟨le_rfl, (tailActualEdge_order hT n).le⟩,
    tailActualEdgeInterpolation_flux hT n a b
      ⟨(tailActualEdge_order hT n).le, le_rfl⟩] at h
  constructor
  · dsimp only [tailActualNodeCoupling]
    linarith only [h.1]
  · exact h.2

/-- The physical node recurrence is equivalent to matching adjacent fluxes. -/
theorem tailActualInterpolationFlux_match {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) (n : ℕ) :
    tailActualEdgeInterpolationFlux T hT n (a n) (a (n + 1)) (T.node (n + 1)) =
      tailActualEdgeInterpolationFlux T hT (n + 1) (a (n + 1)) (a (n + 2))
        (T.node (n + 1)) := by
  rw [(tailActualEdgeInterpolationFlux_endpoints hT n (a n) (a (n + 1))).2,
    (tailActualEdgeInterpolationFlux_endpoints hT (n + 1) (a (n + 1)) (a (n + 2))).1]
  have h := hrec n
  dsimp only [tailActualInteriorDiagonal] at h
  linarith only [h]

def tailPoissonInterpolation (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ → ℝ) : ℝ → ℝ :=
  morseOutwardGlue T.node (fun n => tailActualEdgeInterpolation T hT n (a n) (a (n + 1)))

def tailPoissonInterpolationFlux (T : DeepTailData) (hT : DeepTailHypotheses T)
    (a : ℕ → ℝ) : ℝ → ℝ :=
  morseOutwardGlue T.node (fun n => tailActualEdgeInterpolationFlux T hT n (a n) (a (n + 1)))

theorem tailPoissonInterpolationFlux_first_node {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) :
    tailPoissonInterpolationFlux T hT a (T.node 0) =
      -tailActualEdgeDiagonal T hT 0 (tailActualEdgePoisson T hT 0) false * a 0 +
        tailActualNodeCoupling T hT 0 * a 1 := by
  unfold tailPoissonInterpolationFlux
  rw [morseOutwardGlue_apply_block (deepTail_node_strictMono hT)
    (show T.node 0 ∈ Ico (T.node 0) (T.node (0 + 1)) from
      ⟨le_rfl, tailActualEdge_order hT 0⟩)]
  exact (tailActualEdgeInterpolationFlux_endpoints hT 0 (a 0) (a 1)).1

theorem tailPoissonInterpolation_apply_closed {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) {n : ℕ} {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    tailPoissonInterpolation T hT a x = tailActualEdgeInterpolation T hT n (a n) (a (n + 1)) x :=
  tailOutwardGlue_apply_closed (deepTail_node_strictMono hT)
    (fun k => (tailActualEdgeInterpolation_endpoints hT k (a k) (a (k + 1))).2.trans
      (tailActualEdgeInterpolation_endpoints hT (k + 1) (a (k + 1)) (a (k + 2))).1.symm) hx

theorem tailPoissonInterpolation_node {T : DeepTailData}
    (hT : DeepTailHypotheses T) (a : ℕ → ℝ) (n : ℕ) :
    tailPoissonInterpolation T hT a (T.node n) = a n := by
  rw [tailPoissonInterpolation_apply_closed hT a
    ⟨le_rfl, (tailActualEdge_order hT n).le⟩]
  exact (tailActualEdgeInterpolation_endpoints hT n (a n) (a (n + 1))).1

theorem tailPoissonInterpolation_system_Ico {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) :
    TailFirstOrderSystem T.p T.Λ (tailPoissonInterpolation T hT a)
      (tailPoissonInterpolationFlux T hT a) (Ico (T.node 0) T.endpoint) := by
  let F : ℕ → ℝ → ℝ := fun n => tailActualEdgeInterpolation T hT n (a n) (a (n + 1))
  let Q : ℕ → ℝ → ℝ := fun n => tailActualEdgeInterpolationFlux T hT n (a n) (a (n + 1))
  have hF (n : ℕ) : F n (T.node (n + 1)) = F (n + 1) (T.node (n + 1)) :=
    (tailActualEdgeInterpolation_endpoints hT n (a n) (a (n + 1))).2.trans
      (tailActualEdgeInterpolation_endpoints hT (n + 1) (a (n + 1)) (a (n + 2))).1.symm
  have hQ (n : ℕ) : Q n (T.node (n + 1)) = Q (n + 1) (T.node (n + 1)) :=
    tailActualInterpolationFlux_match hT hrec n
  have hlim : Tendsto T.node atTop (𝓝 T.endpoint) := hT.2.2.2.2.2.2.2.2.2.1
  intro x hx
  obtain ⟨n, hn⟩ := morse_outward_block_exists hlim hx.1 hx.2
  have hu := tailOutwardGlue_hasDerivAt_Ico (piece := F) (slope := fun n x => Q n x / T.p x)
    (deepTail_node_strictMono hT) hlim hF
    (fun k => congrArg (fun z => z / T.p (T.node (k + 1))) (hQ k))
    (fun k y hy => tailActualEdgeInterpolation_hasDerivAt hT k (a k) (a (k + 1)) hy) hx
  have hv := tailOutwardGlue_hasDerivAt_Ico (piece := Q) (slope := fun n x => -T.Λ * T.p x * F n x)
    (deepTail_node_strictMono hT) hlim hQ
    (fun k => congrArg (fun z => -T.Λ * T.p (T.node (k + 1)) * z) (hF k))
    (fun k y hy => tailActualEdgeInterpolationFlux_hasDerivAt hT k (a k) (a (k + 1)) hy) hx
  rw [morseOutwardGlue_apply_block (deepTail_node_strictMono hT) hn] at hu hv
  constructor
  · simpa only [tailPoissonInterpolation, tailPoissonInterpolationFlux,
      morseOutwardGlue_apply_block (deepTail_node_strictMono hT) hn] using hu
  · simpa only [tailPoissonInterpolation, tailPoissonInterpolationFlux,
      morseOutwardGlue_apply_block (deepTail_node_strictMono hT) hn] using hv

theorem tailPoissonInterpolation_system {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) :
    TailFirstOrderSystem T.p T.Λ (tailPoissonInterpolation T hT a)
      (tailPoissonInterpolationFlux T hT a) (Ioo (T.node 0) T.endpoint) :=
  (tailPoissonInterpolation_system_Ico hT hrec).mono Ioo_subset_Ico_self

/-- Smoothness from the right at the first node, and on the whole open tail. -/
theorem tailPoissonInterpolation_contDiffOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) {a : ℕ → ℝ}
    (hrec : ∀ n, -tailActualInteriorDiagonal T hT n * a (n + 1) =
      tailActualNodeCoupling T hT n * a n +
        tailActualNodeCoupling T hT (n + 1) * a (n + 2)) :
    ContDiffOn ℝ ∞ (tailPoissonInterpolation T hT a) (Ico (T.node 0) T.endpoint) ∧
      ContDiffOn ℝ ∞ (tailPoissonInterpolationFlux T hT a) (Ico (T.node 0) T.endpoint) := by
  have hsub : Ico (T.node 0) T.endpoint ⊆ Ico T.entrance T.endpoint :=
    fun x hx => ⟨hT.2.1.trans hx.1, hx.2⟩
  exact tailFirstOrderSystemWithin_contDiffOn
    (uniqueDiffOn_Ico (T.node 0) T.endpoint)
    (hT.2.2.2.2.2.2.2.1.mono hsub)
    (fun x hx => (hT.2.2.2.2.2.2.2.2.1 x (hsub hx)).ne')
    (tailPoissonInterpolation_system_Ico hT hrec).within

end ContinuousFlexibility.Radial
