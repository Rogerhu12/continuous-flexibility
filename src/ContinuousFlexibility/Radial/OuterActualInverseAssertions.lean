import ContinuousFlexibility.Radial.OuterPhysicalRobinInverse
import ContinuousFlexibility.Radial.OuterEndpointBracket
import ContinuousFlexibility.Radial.OuterRobinJacobiPairing

/-!
# Exact assertions for the same actual outer inverse

The bounded operator, weak graph, canonical kernel representative,
entrance traces, endpoint bracket, and original Jacobi pairing below
all belong to one `OuterPhysicalRobinInverse` certificate.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set Filter MeasureTheory
open scoped Topology ContDiff
open ContinuousFlexibility.Statements

namespace OuterPhysicalRobinInverse

variable {M : MorseChainData} {D : ReferenceData}
  {right : Bool} {j start : ℕ} {entry deep η K lam : ℝ}
  {F : MorsePhysicalTailBasis M D right j start deep η K}
  {H : OuterFundamentalStatePair
    (fun x => lam / outerTailOutwardWeight D right x)
    (fun x => (j : ℝ) ^ 2 * deriv (outerTailOutwardWeight D right) x / (lam * x))
    F.P (F.ZP lam) F.Q (F.ZQ lam)
    (outerOutwardRadius right entry) (outerOutwardRadius right deep)
    (outerOutwardRadius right (tailPhysicalEndpoint D right))}

/-- The canonical kernel representative has the Robin trace in the graph.
Continuity transfers its almost-everywhere equality with any graph
representative to the entrance; equality on the interval also transfers
the one-sided derivative there. -/
theorem canonical_robin (I : OuterPhysicalRobinInverse F H)
    (hD : IsAccumulatingProfile D) (hentry : entry ∈ radialCore D)
    (f : OuterWholeL2 D right entry) :
    let a := outerOutwardRadius right entry
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    let g := outerPhysicalGreenValue D right entry lam H.U H.V f
    outerStatePair H.entrance
      (g a, outerTailOutwardWeight D right a * derivWithin g (Ico a b) a / lam) = 0 := by
  let a := outerOutwardRadius right entry
  let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
  let g := outerPhysicalGreenValue D right entry lam H.U H.V f
  have hab : a < b := outerWhole_interval hentry
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  have hgraph := (I.graph_iff (I.operator f) f).mpr rfl
  obtain ⟨u, q, hae, hu, _, hflux, _, hRobin⟩ := hgraph
  have hcan : (I.operator f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] g :=
    outerPhysicalGreenValue_ae hD hentry H.U_system.continuousOn.1
      I.natural_memLp I.operator I.kernel f
  have hg : ContDiffOn ℝ 1 g (Ico a b) := (I.regular_trace f).1
  have heq : EqOn u g (Ioo a b) := Measure.eqOn_Ioo_of_ae_eq volume
    ((outerWholeMeasure_ae_iff hD hentry).mp (hae.symm.trans hcan))
    (hu.continuousOn.mono Ioo_subset_Ico_self)
    (hg.continuousOn.mono Ioo_subset_Ico_self)
  have heq' : EqOn u g (Ico a b) := heq.of_subset_closure
    hu.continuousOn hg.continuousOn Ioo_subset_Ico_self (by
      rw [closure_Ioo hab.ne]
      exact Ico_subset_Icc_self)
  have hd : derivWithin g (Ico a b) a = derivWithin u (Ico a b) a :=
    derivWithin_congr heq'.symm (heq' ha).symm
  change outerStatePair H.entrance
    (g a, outerTailOutwardWeight D right a * derivWithin g (Ico a b) a / lam) = 0
  rw [hd, ← heq' ha, ← hflux a ha]
  exact hRobin

/-- All source and domain assertions use exactly the same actual inverse.
The graph equivalence supplies both inverse directions.  The remaining
claims use the representative obtained from its min/max kernel. -/
theorem assertions (I : OuterPhysicalRobinInverse F H)
    (hD : IsAccumulatingProfile D) (hentry : entry ∈ radialCore D)
    (hlam : lam ≠ 0) :
    let a := outerOutwardRadius right entry
    let b := outerOutwardRadius right (tailPhysicalEndpoint D right)
    let w := outerTailOutwardWeight D right
    let ρ := outerWholeDensity D right
    (∀ u f : OuterWholeL2 D right entry,
      OuterRobinWeakGraph (outerWholeMeasure D right entry) a b ((j : ℝ) ^ 2)
        lam w ρ H.entrance u f ↔ I.operator f = u) ∧
    ∀ f : OuterWholeL2 D right entry,
      let g := outerPhysicalGreenValue D right entry lam H.U H.V f
      (I.operator f : ℝ → ℝ) =ᵐ[outerWholeMeasure D right entry] g ∧
      MemLp g 2 (outerWholeMeasure D right entry) ∧
      ContDiffOn ℝ 1 g (Ico a b) ∧
      outerStatePair H.entrance (g a, w a * derivWithin g (Ico a b) a / lam) = 0 ∧
      outerStatePair (outerStatePerp H.entrance)
        (g a, w a * derivWithin g (Ico a b) a / lam) =
          (∫ y, H.V y * f y ∂outerWholeMeasure D right entry) / lam ∧
      Tendsto (fun x => g x * (w x * deriv H.V x) - w x * deriv g x * H.V x)
        (𝓝[<] b) (𝓝 0) ∧
      ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo a b →
        (∫ x in a..b, (I.operator f) x * radialJacobi ((j : ℝ) ^ 2) w ψ x) =
          -(∫ x in a..b, ρ x * f x * ψ x) := by
  refine ⟨I.graph_iff, ?_⟩
  intro f
  have hae := outerPhysicalGreenValue_ae hD hentry H.U_system.continuousOn.1
    I.natural_memLp I.operator I.kernel f
  have hmem := (memLp_congr_ae hae).mp (Lp.memLp (I.operator f))
  refine ⟨hae, hmem, (I.regular_trace f).1, I.canonical_robin hD hentry f,
    (I.regular_trace f).2,
    outerPhysicalGreen_endpoint_bracket hD hentry hlam H I.natural_memLp f, ?_⟩
  intro ψ hψ hc hs
  exact OuterRobinWeakGraph.physical_jacobi_pairing hD hentry
    ((I.graph_iff (I.operator f) f).mpr rfl) hψ hc hs

end OuterPhysicalRobinInverse

end ContinuousFlexibility.Radial
