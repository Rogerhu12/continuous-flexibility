import ContinuousFlexibility.Radial.TailClampedResistance
import ContinuousFlexibility.Radial.TailMassResistanceData
import ContinuousFlexibility.Radial.TailEdgeFluxMatrix

/-!
# The Poisson problem on an actual deep-tail edge

The resistance chart of the clamped physical density identifies the edge
`[node n, node (n + 1)]` with `[0, RI + R]`. Its potential is exactly
`Λ` times the transformed density, and its two masses and two resistances
are the quantities in `DeepTailHypotheses`.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open ContinuousFlexibility.Statements

theorem tailActualEdge_order {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    T.node n < T.node (n + 1) :=
  deepTail_node_strictMono hT (Nat.lt_succ_self n)

theorem tailActualEdge_interval_subset {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    Icc (T.node n) (T.node (n + 1)) ⊆ Ico T.entrance T.endpoint :=
  deepTail_Icc_subset hT (deepTail_entrance_le_node hT n)
    (deepTail_node_lt_endpoint hT (n + 1))

theorem tailActualEdge_continuousOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    ContinuousOn T.p (Icc (T.node n) (T.node (n + 1))) :=
  (deepTail_contDiffOn hT).continuousOn.mono (tailActualEdge_interval_subset hT n)

theorem tailActualEdge_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    ∀ x ∈ Icc (T.node n) (T.node (n + 1)), 0 < T.p x :=
  fun x hx => deepTail_pos hT x (tailActualEdge_interval_subset hT n hx)

/-- The same clamped density is used in every construction on the actual edge. -/
def tailActualEdgeDensity (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ → ℝ :=
  tailClampedDensity T.p (T.node n) (T.node (n + 1)) (tailActualEdge_order hT n).le

theorem tailActualEdgeDensity_continuous {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : Continuous (tailActualEdgeDensity T hT n) :=
  tailClampedDensity_continuous (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n)

theorem tailActualEdgeDensity_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    ∀ x, 0 < tailActualEdgeDensity T hT n x :=
  tailClampedDensity_pos (tailActualEdge_order hT n).le (tailActualEdge_pos hT n)

/-- Resistance measured from the left node, with its globally defined chart. -/
def tailActualEdgeChart (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ → ℝ :=
  tailResistanceChart (tailActualEdgeDensity T hT n) (T.node n)

/-- Total resistance of the mass interval and its following gap. -/
def tailActualEdgeLength (T : DeepTailData) (n : ℕ) : ℝ :=
  tailInnerResistance T n + tailResistance T n

theorem tailActualEdgeLength_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    0 < tailActualEdgeLength T n :=
  add_pos (tailInnerResistance_pos hT n) (tailResistance_pos hT n)

theorem tailActualEdgeChart_left {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeChart T hT n (T.node n) = 0 := by
  simp only [tailActualEdgeChart, tailResistanceChart, intervalIntegral.integral_same]

theorem tailActualEdgeChart_massEnd {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeChart T hT n (T.massEnd n) = tailInnerResistance T n :=
  tailClampedResistanceChart_eq (tailActualEdge_order hT n).le
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩

theorem tailActualEdgeChart_right_sub_massEnd {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeChart T hT n (T.node (n + 1)) -
        tailActualEdgeChart T hT n (T.massEnd n) = tailResistance T n :=
  tailClampedResistanceChart_sub (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n)
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
    ⟨(tailActualEdge_order hT n).le, le_rfl⟩

theorem tailActualEdgeChart_right {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeChart T hT n (T.node (n + 1)) = tailActualEdgeLength T n := by
  unfold tailActualEdgeLength
  linarith only [tailActualEdgeChart_massEnd hT n,
    tailActualEdgeChart_right_sub_massEnd hT n]

theorem tailActualEdgeChart_strictMono {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : StrictMono (tailActualEdgeChart T hT n) :=
  tailResistanceChart_strictMono (tailActualEdgeDensity_continuous hT n)
    (tailActualEdgeDensity_pos hT n) (T.node n)

theorem tailActualEdgeChart_mem {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    tailActualEdgeChart T hT n x ∈ Icc 0 (tailActualEdgeLength T n) := by
  constructor
  · calc
      0 = tailActualEdgeChart T hT n (T.node n) := (tailActualEdgeChart_left hT n).symm
      _ ≤ tailActualEdgeChart T hT n x := (tailActualEdgeChart_strictMono hT n).monotone hx.1
  · calc
      tailActualEdgeChart T hT n x ≤ tailActualEdgeChart T hT n (T.node (n + 1)) :=
        (tailActualEdgeChart_strictMono hT n).monotone hx.2
      _ = tailActualEdgeLength T n := tailActualEdgeChart_right hT n

/-- The transformed density `p(x(s))²`, rather than a comparison weight. -/
def tailActualEdgeWeight (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ → ℝ :=
  tailResistanceDensity (tailActualEdgeDensity T hT n) (T.node n)

theorem tailActualEdgeWeight_pos {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ)
    (s : ℝ) : 0 < tailActualEdgeWeight T hT n s :=
  tailClampedResistanceDensity_pos (tailActualEdge_order hT n).le (tailActualEdge_pos hT n) s

theorem tailActualEdgeWeight_continuousOn {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) :
    ContinuousOn (tailActualEdgeWeight T hT n) (Icc 0 (tailActualEdgeLength T n)) := by
  have h := tailClampedResistanceDensity_continuousOn (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n)
  change ContinuousOn (tailActualEdgeWeight T hT n)
    (Icc (tailActualEdgeChart T hT n (T.node n))
      (tailActualEdgeChart T hT n (T.node (n + 1)))) at h
  simpa only [tailActualEdgeChart_left, tailActualEdgeChart_right] using h

theorem tailActualEdgeWeight_chart {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {x : ℝ} (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    tailActualEdgeWeight T hT n (tailActualEdgeChart T hT n x) = T.p x ^ 2 :=
  tailClampedResistanceDensity_chart (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n) hx

/-- The exact change of variables, available for every continuous test factor. -/
theorem tailActualEdge_mass_change {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {V : ℝ → ℝ} (hV : Continuous V) {l r : ℝ}
    (hl : l ∈ Icc (T.node n) (T.node (n + 1)))
    (hr : r ∈ Icc (T.node n) (T.node (n + 1))) :
    (∫ s in tailActualEdgeChart T hT n l..tailActualEdgeChart T hT n r,
      tailActualEdgeWeight T hT n s * V s) =
      ∫ x in l..r, T.p x * V (tailActualEdgeChart T hT n x) :=
  tailClampedResistance_mass_change (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n) hV hl hr

theorem tailActualEdgeWeight_mass {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    (∫ s in 0..tailInnerResistance T n, tailActualEdgeWeight T hT n s) = tailMass T n := by
  have h := tailActualEdge_mass_change hT n (V := fun _ => 1) continuous_const
    ⟨le_rfl, (tailActualEdge_order hT n).le⟩
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
  simpa only [tailActualEdgeChart_left, tailActualEdgeChart_massEnd, mul_one, tailMass] using h

theorem tailActualEdgeWeight_gapMass {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    (∫ s in tailInnerResistance T n..tailActualEdgeLength T n,
      tailActualEdgeWeight T hT n s) = tailGapMass T n := by
  have h := tailActualEdge_mass_change hT n (V := fun _ => 1) continuous_const
    ⟨(deepTail_node_lt_massEnd hT n).le, (deepTail_massEnd_lt_succ_node hT n).le⟩
    ⟨(tailActualEdge_order hT n).le, le_rfl⟩
  simpa only [tailActualEdgeChart_massEnd, tailActualEdgeChart_right, mul_one, tailGapMass] using h

/-- The potential of the actual equation, on the single resistance interval `[0,L]`. -/
def tailActualEdgePotential (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) :
    TailEdgeContinuous 0 (tailActualEdgeLength T n) where
  toFun s := T.Λ * tailActualEdgeWeight T hT n s
  continuous_toFun := continuous_const.mul (tailActualEdgeWeight_continuousOn hT n).domRestrict

theorem tailActualEdgePotential_apply {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ)
    (s : Icc 0 (tailActualEdgeLength T n)) :
    tailActualEdgePotential T hT n s = T.Λ * tailActualEdgeWeight T hT n s := rfl

theorem tailActualEdgePotential_nonneg {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) : ∀ s, 0 ≤ tailActualEdgePotential T hT n s := by
  intro s
  rw [tailActualEdgePotential_apply]
  exact mul_nonneg hT.2.2.1.le (tailActualEdgeWeight_pos hT n s).le

theorem tailActualEdgePotential_extend {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc 0 (tailActualEdgeLength T n)) :
    IccExtend (tailActualEdgeLength_pos hT n).le (tailActualEdgePotential T hT n) s =
      T.Λ * tailActualEdgeWeight T hT n s := by
  rw [IccExtend_of_mem (tailActualEdgeLength_pos hT n).le
    (tailActualEdgePotential T hT n) hs, tailActualEdgePotential_apply]

def tailActualEdgeDiagonalSize (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : ℝ :=
  tailEdgeDiagonalSize (tailActualEdgeLength_pos hT n) (tailActualEdgePotential T hT n)

theorem tailActualEdgeDiagonalSize_eq {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeDiagonalSize T hT n = T.Λ *
      ∫ s in 0..tailActualEdgeLength T n,
        tailActualEdgeWeight T hT n s * tailEdgeGreen 0 (tailActualEdgeLength T n) s s := by
  unfold tailActualEdgeDiagonalSize tailEdgeDiagonalSize
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (tailActualEdgeLength_pos hT n).le]
  intro s hs
  dsimp only
  rw [tailActualEdgePotential_extend hT n hs]
  ring

/-- The exact data make the Green insertion at most `η`. -/
theorem tailActualEdgeDiagonalSize_le {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    tailActualEdgeDiagonalSize T hT n ≤ T.η := by
  have hc : tailInnerResistance T n ≤ tailActualEdgeLength T n := by
    unfold tailActualEdgeLength
    exact le_add_of_nonneg_right (tailResistance_pos hT n).le
  have h := tailEdge_green_diagonal_le_mass_resistance
    (tailActualEdgeLength_pos hT n) (tailInnerResistance_pos hT n).le hc hT.2.2.1.le
    (tailActualEdgeWeight_continuousOn hT n) (fun s _ => (tailActualEdgeWeight_pos hT n s).le)
  calc
    tailActualEdgeDiagonalSize T hT n = T.Λ *
        ∫ s in 0..tailActualEdgeLength T n,
          tailActualEdgeWeight T hT n s * tailEdgeGreen 0 (tailActualEdgeLength T n) s s :=
      tailActualEdgeDiagonalSize_eq hT n
    _ ≤ T.Λ * ((tailInnerResistance T n - 0) *
          (∫ s in 0..tailInnerResistance T n, tailActualEdgeWeight T hT n s) +
        (tailActualEdgeLength T n - tailInnerResistance T n) *
          ∫ s in tailInnerResistance T n..tailActualEdgeLength T n,
            tailActualEdgeWeight T hT n s) := h
    _ = T.Λ * tailMass T n * tailInnerResistance T n +
        T.Λ * tailGapMass T n * tailResistance T n := by
      rw [tailActualEdgeWeight_mass, tailActualEdgeWeight_gapMass]
      unfold tailActualEdgeLength
      ring
    _ ≤ T.η := (hT.2.2.2.2.2.2.2.2.2.2 n).2.2.1

theorem tailActualEdgeDiagonalSize_lt_one {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : tailActualEdgeDiagonalSize T hT n < 1 :=
  (tailActualEdgeDiagonalSize_le hT n).trans_lt hT.2.2.2.2.2.1

theorem tailActualEdgeChart_differentiable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) : Differentiable ℝ (tailActualEdgeChart T hT n) :=
  fun x => (hasDerivAt_tailResistanceChart (tailActualEdgeDensity_continuous hT n)
    (tailActualEdgeDensity_pos hT n) (T.node n) x).differentiableAt

/-- The actual physical flux, including both endpoints of the edge. -/
theorem tailActualEdge_flux {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {V : ℝ → ℝ} (hV : Differentiable ℝ V) {x : ℝ}
    (hx : x ∈ Icc (T.node n) (T.node (n + 1))) :
    T.p x * deriv (V ∘ tailActualEdgeChart T hT n) x =
      deriv V (tailActualEdgeChart T hT n x) :=
  tailClampedResistance_flux (tailActualEdge_order hT n).le
    (tailActualEdge_continuousOn hT n) (tailActualEdge_pos hT n) hV hx

/-- A classical solution for the actual potential solves the original homogeneous ODE. -/
theorem tailActualEdge_equation {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) {V : ℝ → ℝ} (hV : Differentiable ℝ V)
    (hODE : ∀ s (hs : s ∈ Icc 0 (tailActualEdgeLength T n)),
      HasDerivAt (deriv V) (-(tailActualEdgePotential T hT n ⟨s, hs⟩ * V s)) s)
    {x : ℝ} (hx : x ∈ Ioo (T.node n) (T.node (n + 1))) :
    deriv (fun y => T.p y * deriv (V ∘ tailActualEdgeChart T hT n) y) x +
      T.Λ * T.p x * (V ∘ tailActualEdgeChart T hT n) x = 0 := by
  have hxc : x ∈ Icc (T.node n) (T.node (n + 1)) := ⟨hx.1.le, hx.2.le⟩
  have hs := tailActualEdgeChart_mem hT n hxc
  have hD := hODE (tailActualEdgeChart T hT n x) hs
  have hres : -deriv (deriv V) (tailActualEdgeChart T hT n x) -
      T.Λ * tailActualEdgeWeight T hT n (tailActualEdgeChart T hT n x) *
        V (tailActualEdgeChart T hT n x) =
      tailActualEdgeWeight T hT n (tailActualEdgeChart T hT n x) * 0 := by
    rw [hD.deriv, tailActualEdgePotential_apply]
    ring
  have hphys := (tailClampedResistance_equation (p := T.p) (V := V) (f := fun _ => 0)
    (tailActualEdge_order hT n).le (tailActualEdge_continuousOn hT n)
    (tailActualEdge_pos hT n) hV T.Λ hx hD.differentiableAt).mpr hres
  change -deriv (fun y => T.p y * deriv (V ∘ tailActualEdgeChart T hT n) y) x / T.p x -
    T.Λ * (V ∘ tailActualEdgeChart T hT n) x = 0 at hphys
  field_simp [(tailActualEdge_pos hT n x hxc).ne'] at hphys
  nlinarith only [hphys]

/-- The affine height for either endpoint of the actual resistance interval. -/
def tailActualEdgeAffineHeight (T : DeepTailData) (n : ℕ) (right : Bool) : ℝ → ℝ :=
  if right then tailEdgeRightHeight 0 (tailActualEdgeLength T n)
    else tailEdgeLeftHeight 0 (tailActualEdgeLength T n)

/-- Off-diagonal coefficient of a pair of actual Poisson heights. -/
def tailActualEdgeCoupling (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (V : Bool → ℝ → ℝ) : ℝ :=
  1 / tailActualEdgeLength T n + ∫ s in 0..tailActualEdgeLength T n,
    tailEdgeLeftHeight 0 (tailActualEdgeLength T n) s *
      IccExtend (tailActualEdgeLength_pos hT n).le (tailActualEdgePotential T hT n) s * V true s

/-- One formula covers the two diagonal coefficients of the actual edge. -/
def tailActualEdgeDiagonal (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ)
    (V : Bool → ℝ → ℝ) (right : Bool) : ℝ :=
  1 / tailActualEdgeLength T n - ∫ s in 0..tailActualEdgeLength T n,
    tailActualEdgeAffineHeight T n right s *
      IccExtend (tailActualEdgeLength_pos hT n).le (tailActualEdgePotential T hT n) s * V right s

/-- Properties of one pair, before making the single canonical choice on each edge. -/
structure TailActualEdgePoissonSpec (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) (V : Bool → ℝ → ℝ) : Prop where
  differentiable : ∀ right, Differentiable ℝ (V right)
  left_value : ∀ right, V right 0 = if right then 0 else 1
  right_value : ∀ right, V right (tailActualEdgeLength T n) = if right then 1 else 0
  equation : ∀ right s (hs : s ∈ Icc 0 (tailActualEdgeLength T n)),
    HasDerivAt (deriv (V right)) (-(tailActualEdgePotential T hT n ⟨s, hs⟩ * V right s)) s
  bounds : ∀ right, ∀ s ∈ Icc 0 (tailActualEdgeLength T n),
    tailActualEdgeAffineHeight T n right s ≤ V right s ∧
      V right s ≤ tailActualEdgeAffineHeight T n right s / (1 - tailActualEdgeDiagonalSize T hT n)
  flux : ∀ x y : ℝ,
    let v : ℝ → ℝ := fun s => x * V false s + y * V true s;
    -deriv v 0 = tailActualEdgeDiagonal T hT n V false * x - tailActualEdgeCoupling T hT n V * y ∧
      deriv v (tailActualEdgeLength T n) =
        -tailActualEdgeCoupling T hT n V * x + tailActualEdgeDiagonal T hT n V true * y

theorem exists_tailActualEdgePoisson {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    ∃ V : Bool → ℝ → ℝ, TailActualEdgePoissonSpec T hT n V := by
  obtain ⟨V₀, V₁, h₀, h₁, h₀a, h₀b, h₁a, h₁b, hODE, hbounds, hflux⟩ :=
    exists_tailEdgeFluxMatrix (tailActualEdgeLength_pos hT n)
      (tailActualEdgePotential_nonneg hT n) (tailActualEdgeDiagonalSize_lt_one hT n)
  refine ⟨fun right => if right then V₁ else V₀, ?_⟩
  constructor
  · intro right
    cases right
    · exact h₀
    · exact h₁
  · intro right
    cases right
    · exact h₀a
    · exact h₁a
  · intro right
    cases right
    · exact h₀b
    · exact h₁b
  · intro right s hs
    cases right
    · exact (hODE s hs).1
    · exact (hODE s hs).2
  · intro right s hs
    cases right
    · exact (hbounds s hs).1
    · exact (hbounds s hs).2
  · simpa only [tailActualEdgeDiagonal, tailActualEdgeCoupling, tailActualEdgeAffineHeight,
      Bool.false_eq_true, ite_false, ite_true, sub_zero] using hflux

/-- The sole chosen pair of resistance-coordinate Poisson heights on this edge. -/
def tailActualEdgePoisson (T : DeepTailData) (hT : DeepTailHypotheses T) (n : ℕ) : Bool → ℝ → ℝ :=
  Classical.choose (exists_tailActualEdgePoisson hT n)

theorem tailActualEdgePoisson_spec {T : DeepTailData} (hT : DeepTailHypotheses T) (n : ℕ) :
    TailActualEdgePoissonSpec T hT n (tailActualEdgePoisson T hT n) :=
  Classical.choose_spec (exists_tailActualEdgePoisson hT n)

/-- The physical heights are pullbacks of that same chosen pair. -/
def tailActualEdgePoissonPhysical (T : DeepTailData) (hT : DeepTailHypotheses T)
    (n : ℕ) (right : Bool) : ℝ → ℝ :=
  tailActualEdgePoisson T hT n right ∘ tailActualEdgeChart T hT n

theorem tailActualEdgePoissonPhysical_apply {T : DeepTailData} (hT : DeepTailHypotheses T)
    (n : ℕ) (right : Bool) (x : ℝ) :
    tailActualEdgePoissonPhysical T hT n right x =
      tailActualEdgePoisson T hT n right (tailActualEdgeChart T hT n x) := rfl

theorem tailActualEdgePoissonPhysical_differentiable {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    Differentiable ℝ (tailActualEdgePoissonPhysical T hT n right) :=
  ((tailActualEdgePoisson_spec hT n).differentiable right).comp
    (tailActualEdgeChart_differentiable hT n)

theorem tailActualEdgePoissonPhysical_endpoint {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) :
    tailActualEdgePoissonPhysical T hT n right (T.node n) = (if right then 0 else 1) ∧
      tailActualEdgePoissonPhysical T hT n right (T.node (n + 1)) = (if right then 1 else 0) := by
  rw [tailActualEdgePoissonPhysical_apply, tailActualEdgePoissonPhysical_apply,
    tailActualEdgeChart_left, tailActualEdgeChart_right]
  exact ⟨(tailActualEdgePoisson_spec hT n).left_value right,
    (tailActualEdgePoisson_spec hT n).right_value right⟩

theorem tailActualEdgePoissonPhysical_equation {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (right : Bool) {x : ℝ}
    (hx : x ∈ Ioo (T.node n) (T.node (n + 1))) :
    deriv (fun y => T.p y * deriv (tailActualEdgePoissonPhysical T hT n right) y) x +
      T.Λ * T.p x * tailActualEdgePoissonPhysical T hT n right x = 0 :=
  tailActualEdge_equation hT n ((tailActualEdgePoisson_spec hT n).differentiable right)
    ((tailActualEdgePoisson_spec hT n).equation right) hx

/-- Both physical endpoint fluxes use the coefficients of the same chosen pair. -/
theorem tailActualEdgePoissonPhysical_flux {T : DeepTailData}
    (hT : DeepTailHypotheses T) (n : ℕ) (x y : ℝ) :
    let V := tailActualEdgePoisson T hT n;
    let u : ℝ → ℝ := fun t => x * tailActualEdgePoissonPhysical T hT n false t +
      y * tailActualEdgePoissonPhysical T hT n true t;
    -(T.p (T.node n) * deriv u (T.node n)) =
        tailActualEdgeDiagonal T hT n V false * x - tailActualEdgeCoupling T hT n V * y ∧
      T.p (T.node (n + 1)) * deriv u (T.node (n + 1)) =
        -tailActualEdgeCoupling T hT n V * x + tailActualEdgeDiagonal T hT n V true * y := by
  let V := tailActualEdgePoisson T hT n
  let v : ℝ → ℝ := fun s => x * V false s + y * V true s
  have hv : Differentiable ℝ v :=
    (((tailActualEdgePoisson_spec hT n).differentiable false).const_mul x).add
      (((tailActualEdgePoisson_spec hT n).differentiable true).const_mul y)
  have hleft := tailActualEdge_flux hT n hv ⟨le_rfl, (tailActualEdge_order hT n).le⟩
  have hright := tailActualEdge_flux hT n hv ⟨(tailActualEdge_order hT n).le, le_rfl⟩
  rw [tailActualEdgeChart_left] at hleft
  rw [tailActualEdgeChart_right] at hright
  change -(T.p (T.node n) * deriv (v ∘ tailActualEdgeChart T hT n) (T.node n)) = _ ∧
    T.p (T.node (n + 1)) * deriv (v ∘ tailActualEdgeChart T hT n) (T.node (n + 1)) = _
  rw [hleft, hright]
  exact (tailActualEdgePoisson_spec hT n).flux x y

end ContinuousFlexibility.Radial
