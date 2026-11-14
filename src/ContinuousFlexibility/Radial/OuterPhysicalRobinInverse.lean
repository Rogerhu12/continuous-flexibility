module

public import ContinuousFlexibility.Radial.OuterPhysicalGreenAssembly
public import ContinuousFlexibility.Radial.OuterPhysicalRobinUniqueness
public import ContinuousFlexibility.Radial.OuterPhysicalNaturalNorm
public import ContinuousFlexibility.Radial.OuterPhysicalTailBasisNorm

/-!
# Constructing the actual bounded Robin inverse

This is a conclusion of the construction: the actual recurrence basis,
finite-core ODE solutions, deep Friedrichs inverse, and compact core
kernel produce its operator and every field below.  In particular, the
weak graph is inverted on all L² sources in both directions.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory Real
open scoped ContDiff
open ContinuousFlexibility.Statements

structure OuterPhysicalRobinInverse
    {M : MorseChainData} {D : ReferenceData}
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right entry) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right))) where
  operator : OuterWholeL2 D right entry →L[ℝ] OuterWholeL2 D right entry
  poisson_memLp : MemLp F.P 2 (outerOutwardTailMeasure D
    (morsePhysicalDeepTail M D right j start deep η K) right)
  natural_memLp : MemLp H.V 2 (outerWholeMeasure D right entry)
  kernel : ∀ f : OuterWholeL2 D right entry,
    (operator f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] fun x =>
      ∫ y, outerGreenKernel lam H.U H.V x y * f y ∂outerWholeMeasure D right entry
  graph_iff : ∀ u f : OuterWholeL2 D right entry,
    OuterRobinWeakGraph (outerWholeMeasure D right entry)
      (outerOutwardRadius right entry)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)) ((j : ℝ) ^ 2) lam
      (outerTailOutwardWeight D right) (outerWholeDensity D right) H.entrance u f ↔
        operator f = u
  regular_trace : ∀ f : OuterWholeL2 D right entry,
    let a := outerOutwardRadius right entry
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    let u := outerPhysicalGreenValue D right entry lam H.U H.V f
    ContDiffOn ℝ 1 u (Ico a b) ∧
      outerStatePair (outerStatePerp H.entrance)
        (u a, outerTailOutwardWeight D right a * derivWithin u (Ico a b) a / lam) =
          (∫ y, H.V y * f y ∂outerWholeMeasure D right entry) / lam
  operator_bound : ∀ A Kcore : ℝ, 0 ≤ A → 0 ≤ Kcore →
    (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
      |H.U x| ≤ Kcore) →
    (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
      |H.V x| ≤ Kcore) →
    (outerWholeMeasure D right entry).real
      (Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep)) ≤ lam * A ^ 2 →
    ‖poisson_memLp.toLp F.P‖ ≤ sqrt lam * A →
    ‖operator‖ ≤ 2 * (64 / (j : ℝ) ^ 4 + 2 * A ^ 2 * Kcore ^ 2)
  natural_bound : ∀ A Kcore : ℝ, 0 ≤ A → 0 ≤ Kcore →
    (∀ x ∈ Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep),
      |H.V x| ≤ Kcore) →
    (outerWholeMeasure D right entry).real
      (Icc (outerOutwardRadius right entry) (outerOutwardRadius right deep)) ≤ lam * A ^ 2 →
    ‖poisson_memLp.toLp F.P‖ ≤ sqrt lam * A →
    ‖natural_memLp.toLp H.V‖ ≤ 2 * (sqrt lam * A * Kcore)

theorem MorsePhysicalTailBasis.exists_wholeRobinInverse
    {M : MorseChainData} {D : ReferenceData}
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (F : MorsePhysicalTailBasis M D right j start deep η K)
    (H : OuterFundamentalStatePair
      (fun x => lam / outerTailOutwardWeight D right x)
      (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
      F.P (F.ZP lam) F.Q (F.ZQ lam)
      (outerOutwardRadius right entry) (outerOutwardRadius right deep)
      (outerOutwardRadius right (tailPhysicalEndpoint D right)))
    (hD : IsAccumulatingProfile D)
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry < outerOutwardRadius right deep)
    (hlam : 0 < lam)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start deep η K) right j start)
    (hj : 2 ≤ j) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    Nonempty (OuterPhysicalRobinInverse F H) := by
  have hP := F.P_memLp_outward (matchingProfileGeometry hD)
    ((matchingProfileGeometry hD).1.trans hdeep.1) hT
  obtain ⟨hV, hVbound⟩ := F.wholeNatural_memLp_norm H hD hentry hdeep horder.le hlam hP
  obtain ⟨R, hkernel, hbound⟩ := F.exists_wholeGreenOperator H hD hentry hdeep horder.le
    hlam hT hphysical hj hη hK hKinv hP
  have hsolution := outerPhysicalGreenValue_graph_and_trace hD hentry hlam.ne' H hV
    R hkernel
  refine ⟨{
    operator := R, poisson_memLp := hP, natural_memLp := hV, kernel := hkernel,
    graph_iff := ?_, regular_trace := fun f => (hsolution f).2,
    operator_bound := hbound, natural_bound := hVbound
  }⟩
  intro u f
  constructor
  · intro hgraph
    exact F.whole_robin_graph_unique H hD hentry hdeep horder hlam.ne' hT hη hK
      (hsolution f).1 hgraph
  · intro heq
    rw [← heq]
    exact (hsolution f).1

/-- Neither the natural basis nor the full homogeneous pair is an input:
the actual recurrence and finite ODE constructions produce them together
with the bounded inverse of the physical weak Robin realization. -/
theorem exists_outerPhysicalRobinInverse
    {M : MorseChainData} {D : ReferenceData} (hD : IsAccumulatingProfile D)
    {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
    (hentry : entry ∈ radialCore D) (hdeep : deep ∈ radialCore D)
    (horder : outerOutwardRadius right entry < outerOutwardRadius right deep)
    (hlam : 0 < lam)
    (hT : DeepTailHypotheses (morsePhysicalDeepTail M D right j start deep η K))
    (hphysical : TailPhysicalRelation D
      (morsePhysicalDeepTail M D right j start deep η K) right j start)
    (hj : 2 ≤ j) (hη : η ≤ 1 / 16) (hK : 32 ≤ K)
    (hKinv : 10 * tailSmoothStepConstant + 2 ≤ K) :
    ∃ F : MorsePhysicalTailBasis M D right j start deep η K,
      ∃ H : OuterFundamentalStatePair
        (fun x => lam / outerTailOutwardWeight D right x)
        (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
        F.P (F.ZP lam) F.Q (F.ZQ lam)
        (outerOutwardRadius right entry) (outerOutwardRadius right deep)
        (outerOutwardRadius right (tailPhysicalEndpoint D right)),
        Nonempty (OuterPhysicalRobinInverse F H) := by
  have hgeom := matchingProfileGeometry hD
  obtain ⟨F⟩ := exists_morsePhysicalTailBasis hgeom right j start
    (hgeom.1.trans hdeep.1) hT hη hK
  obtain ⟨H⟩ := exists_outerPhysicalFundamentalStatePair hgeom F hentry hdeep
    horder.le hlam hT
  exact ⟨F, H, F.exists_wholeRobinInverse H hD hentry hdeep horder hlam hT hphysical
    hj hη hK hKinv⟩

end ContinuousFlexibility.Radial
