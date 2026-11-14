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

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

set_option backward.isDefEq.respectTransparency true

private abbrev opticalPowerStateTopology (S : PhysicalSpacesData) :
    TopologicalSpace (AnnularState S) := inferInstance
attribute [local instance] opticalPowerStateTopology
private abbrev opticalPowerStateGroup (S : PhysicalSpacesData) :
    AddCommGroup (AnnularState S) := inferInstance
attribute [local instance] opticalPowerStateGroup
private abbrev opticalPowerStateModule (S : PhysicalSpacesData) :
    Module ℝ (AnnularState S) := inferInstance
attribute [local instance] opticalPowerStateModule
private abbrev opticalPowerStateSMul (S : PhysicalSpacesData) : SMul ℝ (AnnularState S) :=
  (opticalPowerStateModule S).toDistribMulAction.toDistribSMul.toSMul
attribute [local instance] opticalPowerStateSMul

private theorem scalarFamilyBounds_restrict
    {X I K : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {U V : Set X} (hV : IsOpen V) (hVU : V ⊆ U)
    (f : I → K → ℝ → X → ℝ) (Ω : I → K → Set ℝ) (n : ℕ)
    (J₀ : ∀ i j t, t ∈ Ω i j → SmoothDirections U (f i j t))
    (bound : ℝ → ℝ → I → K → ℝ → (Fin n → X) → ℝ)
    (hb : ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ i j t, t ∈ Ω i j →
      ∀ J : SmoothDirections U (f i j t), ∀ x ∈ U, ∀ v : Fin n → X,
        |J.D n x v| ≤ bound B A i j t v) :
    ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ i j t, t ∈ Ω i j →
      ∀ J : SmoothDirections V (f i j t), ∀ x ∈ V, ∀ v : Fin n → X,
        |J.D n x v| ≤ bound B A i j t v := by
  obtain ⟨B, A, hB, hA, hb⟩ := hb
  refine ⟨B, A, hB, hA, fun i j t ht J x hx v => ?_⟩
  have he : J.D n x v = (J₀ i j t ht).D n x v :=
    congrArg (fun A : X [×n]→L[ℝ] ℝ => A v)
      (J.unique ((J₀ i j t ht).restrict hV hVU) n x hx)
  exact (congrArg abs he).trans_le (hb i j t ht (J₀ i j t ht) x (hVU hx) v)

private def radialLowJet_powerControl
    {X I K : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (p : ℕ → Seminorm ℝ X) (q : Seminorm ℝ X) (center : X)
    (base loss : ℕ) (hqp : ∀ v, q v ≤ p base v) {U : Set X} (hU : IsOpen U)
    (width H E : I → K → ℝ) (hH : ∀ i j, 0 ≤ H i j) (hE : ∀ i j, 1 ≤ E i j)
    (f : I → K → X → ℝ → ℝ)
    (hf : ∀ i j x, x ∈ U → ContDiffOn ℝ ∞ (f i j x) (Ioo 0 (width i j)))
    (Jr : ∀ i j n t, t ∈ Icc (0 : ℝ) (width i j) →
      SmoothDirections U (fun x => iteratedDeriv n (f i j x) t))
    (hraw : ∀ n k : ℕ, ∃ B A : ℝ, 0 < B ∧ 0 < A ∧ ∀ i j t,
      t ∈ Icc (0 : ℝ) (width i j) →
      ∀ J : SmoothDirections U (fun x => iteratedDeriv n (f i j x) t),
      ∀ x ∈ U, ∀ v : Fin k → X,
        |J.D k x v| ≤ B * E i j ^ A * parameterHeightWeight (H i j) k * ∏ a, q (v a)) :
    EndpointPowerControl p center base loss U
      (fun i : I × K => Ioo (0 : ℝ) (width i.1 i.2) ×ˢ univ) (fun _ _ => 1)
      (fun i _ => H i.1 i.2) (fun i _ => E i.1 i.2)
      (fun i x t => f i.1 i.2 x t.1) := by
  refine ⟨fun i => radialMixedRegularityOn hU (f i.1 i.2) (hf i.1 i.2)
    (fun n t ht => Jr i.1 i.2 n t ⟨ht.1.le, ht.2.le⟩), ?_⟩
  apply endpointRadialLowJets_powerBounds p q center base loss hqp
    (fun i : I × K => Ioo 0 (width i.1 i.2)) (fun _ _ => 1)
    (fun i => H i.1 i.2) (fun i => E i.1 i.2)
    (fun i => hH i.1 i.2) (fun i => hE i.1 i.2) (fun i => f i.1 i.2)
  intro n k
  obtain ⟨B, A, hB, hA, hb⟩ := hraw n k
  refine ⟨B, A, hB, hA.le, fun i t ht J x hx v => ?_⟩
  simpa only [one_pow, one_mul, Real.norm_eq_abs] using
    hb i.1 i.2 t ⟨ht.1.le, ht.2.le⟩ J x hx v

namespace N04RealizationStart.NegativeOpticalFactors

variable {W : N04RealizationStart} {e : ℕ ≃ N04PieceIndex W.D}
  (F : NegativeOpticalFactors W e)

set_option diagnostics true in
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
  exact scalarFamilyBounds_restrict hU hsub
    (fun m side t z => iteratedDeriv n (F.opticalSpeed z m side) t)
    (fun m side => Icc (0 : ℝ) (W.negativeOpticalWidth m side)) k
    (fun m side t ht => F.opticalSpeed_radialJetTower m side n t ht)
    (fun B A m side _ v =>
      B * W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ A *
        parameterHeightWeight
          (W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ)) k *
          ∏ i, pairGrading (stateGrading W.S) realGrading 0 (v i))
    (F.opticalSpeed_mixed_material_bounds n k)

private theorem opticalSpeed_contDiffOn {U : Set (AnnularState W.S × ℝ)}
    (hsub : U ⊆ stateNeighborhood W.S W.C W.base (W.ε / 2))
    (m : ℕ) (side : Bool) (z : AnnularState W.S × ℝ) (hz : z ∈ U) :
    ContDiffOn ℝ ∞ (F.opticalSpeed z m side) (Ioo 0 (W.negativeOpticalWidth m side)) :=
  fun _ ht => ((F.stateSquare_contDiff z m side).contDiffAt.sqrt
    (F.stateSquare_pos (hsub hz) m side ⟨ht.1.le, ht.2.le⟩).ne').contDiffWithinAt

set_option diagnostics true in
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
  exact radialLowJet_powerControl
    (pairGrading (stateGrading W.S) realGrading)
    (pairGrading (stateGrading W.S) realGrading 0)
    (W.C.referenceState, 0) base loss
    (fun v => jointStateGrading_monotone W.S (Nat.zero_le base) v)
    hU (W.negativeOpticalWidth)
    (fun m side => W.T.H (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))) ^ (3 / 4 : ℝ))
    (fun m side => W.T.E0 (W.T.sample ((W.A e).cell (e.symm (.inl (m, side))))))
    (fun _ _ => Real.rpow_nonneg
      (W.hT.2.1 _ (materialSample_mem_radialCore W.hT W.radial.1.choose_spec.2.1 _)).2.1.le _)
    (fun _ _ => W.floor _) (fun m side z => F.opticalSpeed z m side)
    (F.opticalSpeed_contDiffOn hsub)
    (fun m side n t ht => (F.opticalSpeed_radialJetTower m side n t ht).restrict hU hsub)
    (F.opticalSpeed_restricted_radial_bounds hU hsub)

end N04RealizationStart.NegativeOpticalFactors
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_half_powerControl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationStart.NegativeOpticalFactors.opticalSpeed_half_powerControl
