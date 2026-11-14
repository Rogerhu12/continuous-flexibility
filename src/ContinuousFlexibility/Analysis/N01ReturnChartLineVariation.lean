module

public import ContinuousFlexibility.Analysis.N01FlowChartIndependence
public import ContinuousFlexibility.Analysis.ReturnChartVariation

/-!
# The actual chart-line derivative of the return residual

Only the chart coordinate changes along this line.  The state neighborhood
contains a genuine interval of the line, and odd chart increments preserve
the sector.  ODE uniqueness makes the actual minus return and its specified
inverse constant on that interval.  Consequently the earlier scalar
inverse calculation applies to the actual N01 right-chart inverse family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

-- Use the canonical product action directly, avoiding a costly search
-- through the abstract models that make up the state space.
local instance n01ReturnChartLineVariationStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) := Prod.instSMul

open Set Filter
open scoped Topology ContDiff

/-- The affine line which changes only the left-chart coordinate. -/
def stateChartLine (S : PhysicalSpacesData) (z : AnnularState S × ℝ)
    (w : CircleSpace S) (s : ℝ) : AnnularState S × ℝ :=
  ((z.1.1, (z.1.2.1, (z.1.2.2.1, z.1.2.2.2 + s • w))), z.2)

@[simp] theorem stateChartLine_zero (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (w : CircleSpace S) :
    stateChartLine S z w 0 = z := by
  simp only [stateChartLine, zero_smul, add_zero, Prod.eta]

theorem stateChartLine_eq_add_smul (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (w : CircleSpace S) (s : ℝ) :
    stateChartLine S z w s = (z.1 + @SMul.smul ℝ (AnnularState S) inferInstance s (0, (0, (0, w))), z.2) := by
  change ((z.1.1, (z.1.2.1, (z.1.2.2.1, z.1.2.2.2 + s • w))), z.2) =
    ((z.1.1 + s • (0 : HeightPair S), (z.1.2.1 + s • (0 : ℝ),
      (z.1.2.2.1 + s • (0 : CircleSpace S), z.1.2.2.2 + s • w))), z.2)
  simp only [smul_zero, add_zero]

theorem stateChartLine_leftChart (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (w : CircleSpace S) (s : ℝ) (m : ℕ) (θ : ℝ) :
    stateLeftChart S (stateChartLine S z w s).1 m θ =
      stateLeftChart S z.1 m θ + s * (S.circle (3 / 4 : ℝ)).decode w m θ := by
  simp only [stateLeftChart, stateChartLine, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem stateChartLine_sector (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (w : CircleSpace S)
    (hz : stateSector S z.1) (hw : IsOddCircle S w) (s : ℝ) :
    stateSector S (stateChartLine S z w s).1 := by
  refine ⟨hz.1, ?_⟩
  intro m θ
  change (S.circle (3 / 4 : ℝ)).decode (z.1.2.2.2 + s • w) m (-θ) =
    -(S.circle (3 / 4 : ℝ)).decode (z.1.2.2.2 + s • w) m θ
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hz.2 m θ, hw m θ]
  ring

/-- The defining seminorm inequality supplies a genuine parameter
neighborhood; no global openness or smoothness of the inverse is assumed. -/
theorem stateChartLine_eventually_mem (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (w : CircleSpace S) :
    ∀ᶠ s in 𝓝 (0 : ℝ), stateChartLine S z w s ∈ stateNeighborhood S C base ε := by
  let d : AnnularState S := (0, (0, (0, w)))
  let p := stateGrading S base
  have hc : ContinuousAt (fun s : ℝ => p (z.1 - C.referenceState) + ‖s‖ * p d) 0 :=
    continuousAt_const.add (continuousAt_id.norm.mul continuousAt_const)
  have hn : ∀ᶠ s in 𝓝 (0 : ℝ),
      p (z.1 - C.referenceState) + ‖s‖ * p d < ε :=
    hc.eventually_lt continuousAt_const (by simpa only [norm_zero, zero_mul, add_zero] using hz.1)
  filter_upwards [hn] with s hs
  rw [stateChartLine_eq_add_smul]
  refine ⟨?_, hz.2⟩
  change p (z.1 + @SMul.smul ℝ (AnnularState S) inferInstance s d - C.referenceState) < ε
  calc
    p (z.1 + @SMul.smul ℝ (AnnularState S) inferInstance s d - C.referenceState) =
        p ((z.1 - C.referenceState) + @SMul.smul ℝ (AnnularState S) inferInstance s d) := congrArg p (by abel)
    _ ≤ p (z.1 - C.referenceState) + p (@SMul.smul ℝ (AnnularState S) inferInstance s d) := p.add_le' _ _
    _ = p (z.1 - C.referenceState) + ‖s‖ * p d :=
      congrArg (fun t : ℝ => p (z.1 - C.referenceState) + t) (p.smul' s d)
    _ < ε := hs

/-- Composition with the actual odd left chart preserves oddness. -/
theorem chartIncrement_isOdd (S : PhysicalSpacesData)
    (z : AnnularState S × ℝ) (w v : CircleSpace S)
    (hz : stateSector S z.1) (hv : IsOddCircle S v)
    (hw : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode w m θ =
      (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ)) :
    IsOddCircle S w := by
  intro m θ
  have hleft : stateLeftChart S z.1 m (-θ) = -stateLeftChart S z.1 m θ := by
    simp only [stateLeftChart, hz.2 m θ]
    ring
  change (S.circle (3 / 4 : ℝ)).decode w m (-θ) =
    -(S.circle (3 / 4 : ℝ)).decode w m θ
  calc
    (S.circle (3 / 4 : ℝ)).decode w m (-θ) =
        (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m (-θ)) := hw m (-θ)
    _ = (S.circle (3 / 4 : ℝ)).decode v m (-stateLeftChart S z.1 m θ) :=
      congrArg ((S.circle (3 / 4 : ℝ)).decode v m) hleft
    _ = -(S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ) :=
      hv m (stateLeftChart S z.1 m θ)
    _ = -(S.circle (3 / 4 : ℝ)).decode w m θ := congrArg Neg.neg (hw m θ).symm

section ActualVariation

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
  (hN01 : N01Properties D T S C base loss ε)
  (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hsector : stateSector S z.1)

include hN01 hS hT hz hsector

theorem N01Properties.minusReturnInverse_chartLine (w : CircleSpace S)
    (hw : IsOddCircle S w) (s : ℝ)
    (hs : stateChartLine S z w s ∈ stateNeighborhood S C base ε) (m : ℕ) :
    C.minusReturnInverse (stateChartLine S z w s) m = C.minusReturnInverse z m := by
  exact (N01Properties.minusReturnInverse_eq_of_physical_coordinates hN01 hS hT hz hs
    hsector (stateChartLine_sector S z w hsector hw s) rfl rfl rfl rfl m).symm

/-- The actual scalar residual has exactly the N02 chart-direction
derivative.  The two decoding hypotheses only identify the supplied
circle elements with their specified fields. -/
theorem N01Properties.hasDerivAt_returnResidual_chartLine
    (w v r : CircleSpace S) (hv : IsOddCircle S v)
    (hw : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode w m θ =
      (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ))
    (hr : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode r m θ = returnResidualField S C z m θ)
    (m : ℕ) (θ : ℝ) :
    HasDerivAt (fun s => returnResidualField S C (stateChartLine S z w s) m θ)
      (circleRotationDifference S C v m θ + circleChartError S C z r v m θ) 0 := by
  let F : ℝ → ℝ := fun y =>
    stateLeftChart S z.1 m (C.minusReturnInverse z m y) - C.travel m
  let V : ℝ → ℝ := fun y =>
    (S.circle (3 / 4 : ℝ)).decode v m
      (stateLeftChart S z.1 m (C.minusReturnInverse z m y))
  let P : ℝ → ℝ → ℝ := fun s y => F y + s * V y
  let g : ℝ → ℝ → ℝ := fun s => C.rightChartInverse (stateChartLine S z w s) m
  have hwodd := chartIncrement_isOdd S z w v hsector hv hw
  have hsectorLine := stateChartLine_sector S z w hsector hwodd
  have hmem := stateChartLine_eventually_mem S C hz w
  have htransport : ∀ᶠ s in 𝓝 (0 : ℝ),
      (fun y => stateLeftChart S (stateChartLine S z w s).1 m
        (C.minusReturnInverse (stateChartLine S z w s) m y) - C.travel m) = P s := by
    filter_upwards [hmem] with s hs
    have hi := N01Properties.minusReturnInverse_chartLine hN01 hS hT hz hsector
      w hwodd s hs m
    funext y
    rw [hi, stateChartLine_leftChart, hw]
    dsimp only [P, F, V]
    ring
  have hchart : ∀ᶠ s in 𝓝 (0 : ℝ),
      rightChartCandidate S C (stateChartLine S z w s) m = oddPart (P s) :=
    htransport.mono fun s hs => congrArg oddPart hs
  have hpositive : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x, 0 < deriv (oddPart (P s)) x := by
    filter_upwards [hmem, hchart] with s hs hc
    intro x
    rw [← hc]
    exact N01Properties.rightChart_deriv_pos S C (stateChartLine S z w s) m
      hN01 hs (hsectorLine s) x
  have hright : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x, oddPart (P s) (g s x) = x := by
    filter_upwards [hmem, hchart] with s hs hc
    intro x
    rw [← hc]
    exact (N01Properties.return_inverse_and_positive S C (stateChartLine S z w s) m
      hN01 hs (hsectorLine s) x).2.2.1
  have hg0 (x : ℝ) : g 0 x = C.rightChartInverse z m x := by
    simp only [g, stateChartLine_zero]
  have hg : ContinuousAt (fun s => g s θ) 0 :=
    returnChart_inverse_affine_continuous F V g θ hpositive hright
  have hF := N01Properties.transportedLeftChart_differentiable S C z m hN01 hz hsector
  have hψ := ((hS.2.1 (3 / 4 : ℝ)).2.2.2.1 v).1 m
  have h := hasDerivAt_circleChartError_scalar S C z m r v g θ hF hψ.1
    (N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector) hg0
    (fun x => (N01Properties.return_inverse_and_positive S C z m hN01 hz hsector x).2.2.2.1)
    hright hg (hr m)
  apply h.congr_of_eventuallyEq
  filter_upwards [htransport] with s hs
  change evenPart (fun y => stateLeftChart S (stateChartLine S z w s).1 m
      (C.minusReturnInverse (stateChartLine S z w s) m y) - C.travel m) (g s θ) =
    evenPart (P s) (g s θ)
  exact congrArg (fun f : ℝ → ℝ => evenPart f (g s θ)) hs

/-- The same formula written as the affine state line used in the
projective directional-derivative clause of N02. -/
theorem N01Properties.hasDerivAt_returnResidual_chartDirection
    (w v r : CircleSpace S) (hv : IsOddCircle S v)
    (hw : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode w m θ =
      (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ))
    (hr : ∀ m θ, (S.circle (3 / 4 : ℝ)).decode r m θ = returnResidualField S C z m θ)
    (m : ℕ) (θ : ℝ) :
    HasDerivAt (fun s : ℝ => returnResidualField S C
      (z.1 + @SMul.smul ℝ (AnnularState S) inferInstance s (0, (0, (0, w))), z.2) m θ)
      (circleRotationDifference S C v m θ + circleChartError S C z r v m θ) 0 := by
  simpa only [stateChartLine_eq_add_smul] using
    N01Properties.hasDerivAt_returnResidual_chartLine hN01 hS hT hz hsector w v r hv hw hr m θ

end ActualVariation

end ContinuousFlexibility.Statements
