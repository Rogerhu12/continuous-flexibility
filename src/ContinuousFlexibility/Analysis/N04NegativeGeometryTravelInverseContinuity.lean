import ContinuousFlexibility.Analysis.N04NegativeGeometryInverseContinuity
import ContinuousFlexibility.Analysis.TravelStripGlobalInverse

/-!
# Actual travel inverses in a topological parameter family

First invert the strictly increasing angular lifts. At a fixed target
angle the travel coordinate is strictly increasing in the physical
radius. The two scalar inverse continuity theorems therefore establish
joint continuity of the actual planar inverse on the open travel strip.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology

variable {P : Type*} [TopologicalSpace P]
  {U : Set P} {a b : ℝ} {F : P × PolarPoint → PolarPoint}

/-- The angular inverse is continuous jointly in state, radius and
target angle in the original topology of the state. -/
theorem n04NegativeGeometry_travelAngleInverse_continuousOn
    (hF : ContinuousOn F (U ×ˢ (Ioo a b ×ˢ univ)))
    (hMono : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      StrictMono (fun θ => (F (p, (r, θ))).2))
    (hSurj : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      Function.Surjective (fun θ => (F (p, (r, θ))).2)) :
    ContinuousOn
      (fun q : P × PolarPoint =>
        parameterizedCircleInverse (fun y => (F (q.1, y)).2) q.2)
      (U ×ˢ (Ioo a b ×ˢ univ)) := by
  let φ : (P × ℝ) × ℝ → ℝ := fun q => (F (q.1.1, (q.1.2, q.2))).2
  have hφ : ContinuousOn φ ((U ×ˢ Ioo a b) ×ˢ univ) :=
    hF.snd.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)).continuousOn
      (fun q hq => ⟨hq.1.1, hq.1.2, mem_univ _⟩)
  have hA := continuousOn_parameterizedCircleInverse_of_strictMono hφ
    (fun q hq => hMono q.1 hq.1 q.2 hq.2)
    (fun q hq => hSurj q.1 hq.1 q.2 hq.2)
  have hReindex : Continuous
      (fun q : P × PolarPoint => ((q.1, q.2.1), q.2.2)) :=
    (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  have hMaps : MapsTo (fun q : P × PolarPoint => ((q.1, q.2.1), q.2.2))
      (U ×ˢ (Ioo a b ×ˢ univ)) ((U ×ˢ Ioo a b) ×ˢ univ) :=
    fun q hq => ⟨⟨hq.1, hq.2.1⟩, mem_univ _⟩
  exact hA.comp hReindex.continuousOn hMaps

/-- The literal travel coordinate at a fixed target angle has the same
joint continuity, before any radial inverse has been selected. -/
theorem n04NegativeGeometry_normalizedTravel_continuousOn
    (hF : ContinuousOn F (U ×ˢ (Ioo a b ×ˢ univ)))
    (hMono : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      StrictMono (fun θ => (F (p, (r, θ))).2))
    (hSurj : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      Function.Surjective (fun θ => (F (p, (r, θ))).2)) :
    ContinuousOn (fun q : P × PolarPoint =>
      angleNormalizedTravel (fun y => F (q.1, y)) q.2)
      (U ×ˢ (Ioo a b ×ˢ univ)) := by
  have hA := n04NegativeGeometry_travelAngleInverse_continuousOn hF hMono hSurj
  exact (hF.comp
    (continuous_fst.continuousOn.prodMk (continuous_snd.fst.continuousOn.prodMk hA))
    (fun q hq => ⟨hq.1, hq.2.1, mem_univ _⟩)).fst

/-- Angular monotonicity and fixed-angle radial monotonicity force joint
continuity of the given right inverse. No inverse continuity is assumed. -/
theorem n04NegativeGeometry_travelInverse_continuousOn
    {V : Set ℝ} {G : P × PolarPoint → PolarPoint}
    (hF : ContinuousOn F (U ×ˢ (Ioo a b ×ˢ univ)))
    (hMono : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      StrictMono (fun θ => (F (p, (r, θ))).2))
    (hSurj : ∀ p ∈ U, ∀ r ∈ Ioo a b,
      Function.Surjective (fun θ => (F (p, (r, θ))).2))
    (hRadial : ∀ p ∈ U, ∀ θ : ℝ,
      StrictMonoOn (fun r => angleNormalizedTravel (fun y => F (p, y)) (r, θ))
        (Ioo a b))
    (hMaps : MapsTo G (U ×ˢ (V ×ˢ univ)) (Ioo a b ×ˢ univ))
    (hRight : ∀ q ∈ U ×ˢ (V ×ˢ univ), F (q.1, G q) = q.2) :
    ContinuousOn G (U ×ˢ (V ×ˢ univ)) := by
  have hA := n04NegativeGeometry_travelAngleInverse_continuousOn hF hMono hSurj
  have hT := n04NegativeGeometry_normalizedTravel_continuousOn hF hMono hSurj
  have hrecover (q : P × PolarPoint) (hq : q ∈ U ×ˢ (V ×ˢ univ)) :
      parameterizedCircleInverse (fun y => (F (q.1, y)).2)
        ((G q).1, q.2.2) = (G q).2 := by
    have hs := congrArg Prod.snd (hRight q hq)
    rw [← hs]
    exact Function.leftInverse_invFun
      (hMono q.1 hq.1 (G q).1 (hMaps hq).1).injective (G q).2
  let T : (P × ℝ) × ℝ → ℝ := fun q =>
    angleNormalizedTravel (fun y => F (q.1.1, y)) (q.2, q.1.2)
  let R : (P × ℝ) × ℝ → ℝ := fun q => (G (q.1.1, (q.2, q.1.2))).1
  have hTc : ContinuousOn T ((U ×ˢ univ) ×ˢ Ioo a b) :=
    hT.comp (continuous_fst.fst.prodMk
      (continuous_snd.prodMk continuous_fst.snd)).continuousOn
      (fun q hq => ⟨hq.1.1, hq.2, mem_univ _⟩)
  have hRc : ContinuousOn R ((U ×ˢ univ) ×ˢ V) := by
    apply n04NegativeGeometry_intervalInverse_continuousOn hTc
      (fun q hq => hRadial q.1 hq.1 q.2)
    · intro q hq
      exact (hMaps ⟨hq.1.1, hq.2, mem_univ _⟩).1
    · intro q hq
      have hq' : (q.1.1, (q.2, q.1.2)) ∈ U ×ˢ (V ×ˢ univ) :=
        ⟨hq.1.1, hq.2, mem_univ _⟩
      have he := hrecover (q.1.1, (q.2, q.1.2)) hq'
      change (F (q.1.1, ((G (q.1.1, (q.2, q.1.2))).1,
        parameterizedCircleInverse (fun y => (F (q.1.1, y)).2)
          ((G (q.1.1, (q.2, q.1.2))).1, q.1.2)))).1 = q.2
      rw [he]
      exact congrArg Prod.fst (hRight (q.1.1, (q.2, q.1.2)) hq')
  have hGr : ContinuousOn (fun q : P × PolarPoint => (G q).1)
      (U ×ˢ (V ×ˢ univ)) :=
    hRc.comp
      ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst).continuousOn
      (fun q hq => ⟨⟨hq.1, mem_univ _⟩, hq.2.1⟩)
  have hGθ : ContinuousOn (fun q : P × PolarPoint => (G q).2)
      (U ×ˢ (V ×ˢ univ)) := by
    have hc := hA.comp
      (continuous_fst.continuousOn.prodMk
        (hGr.prodMk continuous_snd.snd.continuousOn))
      (fun q hq => ⟨hq.1, (hMaps hq).1, mem_univ _⟩)
    exact hc.congr (fun q hq => (hrecover q hq).symm)
  exact hGr.prodMk hGθ

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.n04NegativeGeometry_travelInverse_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.n04NegativeGeometry_travelInverse_continuousOn
