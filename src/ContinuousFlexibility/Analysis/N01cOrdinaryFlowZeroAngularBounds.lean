module

public import ContinuousFlexibility.Analysis.N01cSpeedAngularGrowth
public import ContinuousFlexibility.Analysis.N01cFlowZeroAngularGrowth
public import ContinuousFlexibility.Analysis.N01cCommonCosineGeometry
public import ContinuousFlexibility.Analysis.N01cPhysicalFlowRegularity

/-!
# Actual zero-parameter angular flow estimates

The same classical ordinary trajectories are evaluated in cosine time.
Their derivative defect obeys the proved circle Sobolev estimate, with
the low constant chosen once from the actual common geometry. A closed
surjective time change then gives every physical-radius angular bound.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Blueprint
open scoped ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

def componentCosineFlowDefectJet
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (m : ℕ)
    (hGz : ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)))
    (t : ℝ) (n : ℕ) : C(AddCircle Real.pi, ℝ) :=
  circleFlowDefectJet
    (Θ := fun p : PolarPoint =>
      C.minusFlow z m (rootCosinePath (C.left m) (C.right m) p.1) p.2)
    hGz (componentCosineSpeed_periodic hS z m)
    (continuousOn_componentCosineFlow hA hB hz m)
    (componentCosineFlow_initial hB hz m)
    (fun r hr θ => hasDerivAt_componentCosineFlow hS hT hA hB hz m θ hr) t n

/-- Both quantities are actual derivatives of the supplied ordinary flow.
The fixed index shift is `loss + d + 2`; no absolute angle value occurs. -/
def OrdinaryFlowZeroAngularGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hB : N01PartB D S C base ε)
    (hGs : ∀ z ∈ stateNeighborhood S C base ε, ∀ m,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)))
    (loss d : ℕ) : Prop :=
  (∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ z (hz : z ∈ stateNeighborhood S C base ε) m t, t ∈ Icc (0 : ℝ) Real.pi →
      circleRealSobolevNorm (s : ℝ)
        (componentCosineFlowDefectJet hS hT hA hB hz m (hGs z hz m) t 0) ≤
        K * (1 + pairGrading (stateGrading S) realGrading
          (s + 1 + loss + d) (z - (C.referenceState, 0)))) ∧
  (∀ β : ℕ, 1 ≤ β → ∃ K : ℝ, 0 < K ∧
    ∀ z ∈ stateNeighborhood S C base ε, ∀ m r,
      r ∈ Icc (C.left m) (C.right m) → ∀ θ,
        |iteratedDeriv β (C.minusFlow z m r) θ| ≤
          K * (1 + pairGrading (stateGrading S) realGrading
            (β - 1 + (loss + d + 2)) (z - (C.referenceState, 0))))

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Blueprint

open Set MeasureTheory ContinuousFlexibility.Analysis ContinuousFlexibility.Statements
open scoped ContDiff

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

set_option backward.isDefEq.respectTransparency true in
/-- The only quantitative input here is the proved speed growth and one
fixed low integrated norm of the actual compact speed. -/
theorem n01_ordinaryFlow_zeroAngular_growth_of_lowGeometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss d : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hGs : ∀ z ∈ stateNeighborhood S C base ε, ∀ m,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)))
    (M : ℝ)
    (hlow : ∀ z (hz : z ∈ stateNeighborhood S C base ε) m,
      circleFlowLambda (fun p => componentCosineSpeed D S C m (z, p))
        (hGs z hz m) (componentCosineSpeed_periodic hS z m) 4 0 Real.pi ≤ M)
    (hraw : ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ z ∈ stateNeighborhood S C base ε, ∀ m b q,
        b ≤ s → q.1 ∈ Ioo (C.left m) (C.right m) →
          |characteristicSpeedFamily D S C 0 b q z| ≤
            K * (1 + pairGrading (stateGrading S) realGrading
              (s + loss + d) (z - (C.referenceState, 0)))) :
    OrdinaryFlowZeroAngularGrowth hS hT hA hB hGs loss d := by
  let U := stateNeighborhood S C base ε
  let size : ℕ → (AnnularState S × ℝ) → ℝ :=
    fun n z => pairGrading (stateGrading S) realGrading n (z - (C.referenceState, 0))
  have hsize : ∀ n z, z ∈ U → 0 ≤ size n z := fun n z _ => apply_nonneg _ _
  let G := fun z m (p : PolarPoint) => componentCosineSpeed D S C m (z, p)
  let Θ := fun z m (p : PolarPoint) =>
    C.minusFlow z m (rootCosinePath (C.left m) (C.right m) p.1) p.2
  let c := fun m t => componentCosineSpeed D S C m ((C.referenceState, 0), (t, 0))
  have hc : ∀ m, IntervalIntegrable (c m) volume 0 Real.pi := by
    intro m
    exact ((hGs _ (reference_mem_stateNeighborhood S C base hε) m).continuous.comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 Real.pi
  have hwidth : 0 < D.b - D.a := sub_pos.mpr
    ((hA.2.2.1.1 0).1.trans ((hA.2.2.1.1 0).2.1.trans (hA.2.2.1.1 0).2.2))
  have href : ∀ s : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ z (hz : z ∈ U) m,
      circleFlowReferenceSize (G z m) (hGs z hz m)
        (componentCosineSpeed_periodic hS z m) (c m) s 0 Real.pi ≤
          K * (1 + size (s + (loss + d)) z) := by
    apply angularGrowth_of_pointwiseComparison U size hsize C.left C.right
      (fun b q z => characteristicSpeedFamily D S C 0 b q z)
      (fun s z hz m => circleFlowReferenceSize (G z m) (hGs z hz m)
        (componentCosineSpeed_periodic hS z m) (c m) s 0 Real.pi)
      (fun s => Real.pi * (2 : ℝ) ^ s * (D.b - D.a))
      (fun s => by positivity) (loss + d)
    · intro s z hz K hK hb m
      have hGc : Continuous (c m) :=
        (hGs _ (reference_mem_stateNeighborhood S C base hε) m).continuous.comp
          (continuous_id.prodMk continuous_const)
      simpa only [mul_assoc] using
        componentCosineSpeed_referenceSize_le hS hT hA hε hB hz hK hb m (hGs z hz m) hGc
    · simpa only [Nat.add_assoc] using hraw
  have hh := circleFlow_family_zeroAngular_growth U size hsize G Θ c
    Real.pi_pos.le (loss + d) hGs
    (fun z _ m => componentCosineSpeed_periodic hS z m)
    (fun z hz m => continuousOn_componentCosineFlow hA hB hz m)
    (fun z hz m => componentCosineFlow_initial hB hz m)
    (fun z hz m t ht θ => hasDerivAt_componentCosineFlow hS hT hA hB hz m θ ht)
    hc M hlow href
  refine ⟨?_, ?_⟩
  · simpa only [componentCosineFlowDefectJet, Nat.add_assoc] using hh.1
  · exact angularGrowth_surjectiveTimeChange U size (loss + d + 2) Θ
      (fun z m r θ => C.minusFlow z m r θ)
      (fun m => rootCosinePath (C.left m) (C.right m)) (Icc (0 : ℝ) Real.pi)
      (fun m => Icc (C.left m) (C.right m))
      (fun m => rootCosinePath_surjOn (hA.2.2.1.1 m).2.1)
      (fun _ _ _ _ _ _ => rfl) hh.2

set_option backward.isDefEq.respectTransparency true in
/-- A single actual common neighbourhood supplies every zero-parameter
flow order. The low geometry is chosen at fixed speed order five. -/
theorem n01_exists_ordinaryFlowZeroAngularGrowth
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hA : N01PartA D T S C) (hε : 0 < ε) (hB : N01PartB D S C base ε)
    (hG : N01PrimitiveGeometry D T S C)
    (hSpeed : CharacteristicSpeedTameBounds D T S C base loss ε) :
    ∃ base₀ : ℕ, ∃ ε₀ : ℝ, base ≤ base₀ ∧ 0 < ε₀ ∧ ε₀ ≤ min ε (1 / 2) ∧
      ∃ hB₀ : N01PartB D S C base₀ ε₀,
      ∃ hGs : ∀ z ∈ stateNeighborhood S C base₀ ε₀, ∀ m,
        ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)),
      ∃ d : ℕ, OrdinaryFlowZeroAngularGrowth hS hT hA hB₀ hGs loss d := by
  obtain ⟨base₀, εc, hbase, hεc, hεcε, hpos, hGc, M, hM, hlow⟩ :=
    n01_exists_common_cosineLowGeometry hS hT hA hε hB hG hSpeed
  let ε₀ : ℝ := min εc (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hεc (by norm_num)
  have he : ε₀ ≤ ε := (min_le_left _ _).trans hεcε
  have hB₀ : N01PartB D S C base₀ ε₀ := n01PartB_mono hB hbase he
  have hGc₀ : ∀ z ∈ stateNeighborhood S C base₀ ε₀, ∀ m,
      ContDiff ℝ ∞ (fun p : PolarPoint => componentCosineSpeed D S C m (z, p)) :=
    fun z hz m => hGc z (stateNeighborhood_subset le_rfl (min_le_left _ _) hz) m
  refine ⟨base₀, ε₀, hbase, hε₀, le_min he (min_le_right _ _), hB₀, hGc₀, ?_⟩
  have hSpeed₀ : CharacteristicSpeedTameBounds D T S C base₀ loss ε₀ :=
    characteristicSpeedTameBounds_mono hT hA.1.1 hSpeed hbase le_rfl he
  obtain ⟨d, hd⟩ := n01_speedDifference_angular_growth hT hA.1.1 hSpeed₀
  refine ⟨d, n01_ordinaryFlow_zeroAngular_growth_of_lowGeometry
    hS hT hA hε₀ hB₀ hGc₀ M ?_ hd⟩
  intro z hz m
  exact (hlow z (stateNeighborhood_subset le_rfl (min_le_left _ _) hz) m (hGc₀ z hz m)).1

end ContinuousFlexibility.Blueprint
