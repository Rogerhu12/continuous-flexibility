import ContinuousFlexibility.Scalar.WeightedUniformTameGermOperations
import ContinuousFlexibility.Scalar.WeightedNeighborhood

/-!
# One common ball for the three scalar realizations

The finite scalar outputs and residual may initially have different
uniform germs. One final choice of base, loss and radius retains all three
towers, meets any prescribed additional neighborhood, and dominates the
fixed orders needed by the linear and bilinear families.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped Topology

set_option backward.isDefEq.respectTransparency false

theorem exists_scalarStateBall_realizations
    (S : PhysicalSpacesData) (v0 : ScalarHeightSpace S)
    {jets : ScalarWeightedState S → ScalarFieldOutputs S 7}
    {residual : ScalarWeightedState S → ScalarHeightSpace S}
    {coefficients : ScalarWeightedState S → ScalarFieldOutputs S 3}
    (hjets : UniformTameGerm (scalarStateGrading S) (scalarOutputsGrading S 7)
      (scalarStateCenter S v0) jets)
    (hresidual : UniformTameGerm (scalarStateGrading S) (scalarHeightGrading S)
      (scalarStateCenter S v0) residual)
    (hcoefficients : UniformTameGerm (scalarStateGrading S) (scalarOutputsGrading S 3)
      (scalarStateCenter S v0) coefficients)
    {W : Set (ScalarWeightedState S)} (hW : W ∈ 𝓝 (scalarStateCenter S v0))
    (requiredBase requiredLoss : ℕ) :
    ∃ base loss : ℕ, ∃ ε : ℝ,
      requiredBase ≤ base ∧ requiredLoss ≤ loss ∧ 0 < ε ∧ ε < 1 ∧
      scalarStateBall S v0 base ε ⊆ W ∧
      FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarOutputsGrading S 7)
        (scalarStateBall S v0 base ε) base loss jets ∧
      FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarHeightGrading S)
        (scalarStateBall S v0 base ε) base loss residual ∧
      FixedNeighborhoodSmoothTame (scalarStateGrading S) (scalarOutputsGrading S 3)
        (scalarStateBall S v0 base ε) base loss coefficients := by
  obtain ⟨bj, lj, ej, hej, hj⟩ := hjets
  obtain ⟨br, lr, er, her, hr⟩ := hresidual
  obtain ⟨bc, lc, ec, hec, hc⟩ := hcoefficients
  let Uj := scalarStateBall S v0 bj ej
  let Ur := scalarStateBall S v0 br er
  let Uc := scalarStateBall S v0 bc ec
  have hnj : Uj ∈ 𝓝 (scalarStateCenter S v0) :=
    (isOpen_scalarStateBall S v0 bj ej).mem_nhds (scalarStateCenter_mem_ball S v0 bj hej)
  have hnr : Ur ∈ 𝓝 (scalarStateCenter S v0) :=
    (isOpen_scalarStateBall S v0 br er).mem_nhds (scalarStateCenter_mem_ball S v0 br her)
  have hnc : Uc ∈ 𝓝 (scalarStateCenter S v0) :=
    (isOpen_scalarStateBall S v0 bc ec).mem_nhds (scalarStateCenter_mem_ball S v0 bc hec)
  obtain ⟨base, η, hbase, hη, hη1, hsub⟩ :=
    exists_small_uniformTameBall (scalarStateGrading_monotone S)
      (weighted_scalarStateGrading_withSeminorms S)
      (inter_mem hW (inter_mem hnj (inter_mem hnr hnc)))
      (max requiredBase (max bj (max br bc)))
  let loss := max requiredLoss (max lj (max lr lc))
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by dsimp [ε]; linarith
  have hεη : ε ≤ η := by dsimp [ε]; linarith
  have hsubset : scalarStateBall S v0 base ε ⊆ W ∩ (Uj ∩ (Ur ∩ Uc)) :=
    fun x hx => hsub (hx.trans_le hεη)
  have hU := isOpen_scalarStateBall S v0 base ε
  refine ⟨base, loss, ε, by omega, by dsimp [loss]; omega, hε, hε1,
    (fun x hx => (hsubset hx).1), ?_, ?_, ?_⟩
  · exact (hj.restrict hU (fun x hx => (hsubset hx).2.1)).weaken
      (scalarStateGrading_monotone S) (by omega) (by dsimp [loss]; omega)
  · exact (hr.restrict hU (fun x hx => (hsubset hx).2.2.1)).weaken
      (scalarStateGrading_monotone S) (by omega) (by dsimp [loss]; omega)
  · exact (hc.restrict hU (fun x hx => (hsubset hx).2.2.2)).weaken
      (scalarStateGrading_monotone S) (by omega) (by dsimp [loss]; omega)

end ContinuousFlexibility.Statements
