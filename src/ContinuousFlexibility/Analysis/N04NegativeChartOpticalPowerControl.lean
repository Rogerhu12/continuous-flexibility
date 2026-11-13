import ContinuousFlexibility.Analysis.N04NegativeChartFullHalfFields
import ContinuousFlexibility.Analysis.N01cWholeSpeedPowerBounds

/-!
# The actual divided optical speed in the mixed power algebra

The previously proved low-seminorm radial bounds supply a genuine
endpoint control with endpoint weight one. It restricts to any smaller
open state domain and uses any requested base and loss, so it can be
combined with the actual normalized multiplier without changing that
multiplier's once-chosen interpolation indices.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

/-- The numerical optical bounds and all actual parameter towers survive
restriction; the radial endpoints remain available in the source bound. -/
theorem opticalSpeed_restricted_radial_bounds
    {U : Set (AnnularState W.S × ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ stateNeighborhood W.S W.C W.base (W.ε / 2)) (n k : ℕ) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ m side t,
      t ∈ Icc (0 : ℝ) (W.negativeOpticalWidth m side) →
      ∀ J : SmoothDirections U (fun z => iteratedDeriv n (F.opticalSpeed z m side) t),
      ∀ z ∈ U, ∀ v : Fin k → AnnularState W.S × ℝ,
        |J.D k z v| ≤
          B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A *
            parameterHeightWeight
              (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ)) k *
              ∏ i, pairGrading (stateGrading W.S) realGrading 0 (v i) := by
  obtain ⟨B, A, hB, hA, hb⟩ := F.opticalSpeed_mixed_material_bounds n k
  refine ⟨B, A, hB, hA, fun m side t ht J z hz v => ?_⟩
  let J0 := F.opticalSpeed_radialJetTower m side n t ht
  have he : J.D k z v = J0.D k z v :=
    congrArg (fun A : (AnnularState W.S × ℝ) [×k]→L[ℝ] ℝ => A v)
      (J.unique (J0.restrict hU hsub) k z hz)
  exact (congrArg abs he).trans_le (hb m side t ht J0 z (hsub hz) v)

/-- No radial endpoint power is charged to the divided square root. -/
def opticalSpeed_half_powerControl
    {U : Set (AnnularState W.S × ℝ)} (hU : IsOpen U)
    (hsub : U ⊆ stateNeighborhood W.S W.C W.base (W.ε / 2)) (base loss : ℕ) :
    EndpointPowerControl (pairGrading (stateGrading W.S) realGrading)
      (W.C.referenceState, 0) base loss U
      (fun i : ℕ × Bool => Ioo (0 : ℝ) (W.negativeOpticalWidth i.1 i.2) ×ˢ univ)
      (fun _ _ => 1)
      (fun i _ => W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ (3 / 4 : ℝ))
      (fun i _ => W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl i)))))
      (fun i z p => F.opticalSpeed z i.1 i.2 p.1) := by
  let I : ℕ × Bool → Set ℝ := fun i => Ioo 0 (W.negativeOpticalWidth i.1 i.2)
  let E : ℕ × Bool → ℝ := fun i =>
    W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl i))))
  let H : ℕ × Bool → ℝ := fun i =>
    W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl i)))) ^ (3 / 4 : ℝ)
  have hH (i : ℕ × Bool) : 0 ≤ H i := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _
  refine ⟨fun i => radialMixedRegularityOn hU (fun z => F.opticalSpeed z i.1 i.2)
    (fun z hz t ht =>
      ((F.stateSquare_contDiff z i.1 i.2).contDiffAt.sqrt
        (F.stateSquare_pos (hsub hz) i.1 i.2 ⟨ht.1.le, ht.2.le⟩).ne').contDiffWithinAt)
    (fun n t ht => (F.opticalSpeed_radialJetTower i.1 i.2 n t
      ⟨ht.1.le, ht.2.le⟩).restrict hU hsub), ?_⟩
  apply endpointRadialLowJets_powerBounds
    (pairGrading (stateGrading W.S) realGrading)
    (pairGrading (stateGrading W.S) realGrading 0)
    (W.C.referenceState, 0) base loss
    (fun v => jointStateGrading_monotone W.S (Nat.zero_le base) v)
    I (fun _ _ => 1) H E hH (fun i => W.floor _)
    (fun i z => F.opticalSpeed z i.1 i.2)
  intro n k
  obtain ⟨B, A, hB, hA, hb⟩ := F.opticalSpeed_restricted_radial_bounds hU hsub n k
  refine ⟨B, A, hB, hA.le, fun i t ht J z hz v => ?_⟩
  simpa only [one_pow, one_mul, Real.norm_eq_abs] using
    hb i.1 i.2 t ⟨ht.1.le, ht.2.le⟩ J z hz v

end ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_half_powerControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_half_powerControl
