import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledDiscKernelPower
import ContinuousFlexibility.Analysis.N04PositiveGeometryEndpointBoundsOrientationDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledSamplePrefix
import ContinuousFlexibility.Analysis.N01FlowChartIndependence

/-!
# The actual discriminant power prefix at the retained positive sample

The same fixed packet radius controls every real exponent. The physical
finite sum is then transported by its fixed inward orientation and the
endpoint-to-sample material comparison. Radial orders through three
and five intrinsic angular orders use the single spatial budget eight.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04ControlledDiscSampleStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- The full finite spatial prefix of the physical discriminant power
has one low base before its exponent. Only the additional angular
order is charged in the normalized spatial power. -/
theorem n04PositiveGeometry_physicalRootDiscPowerTrace_finiteShift_power
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ γ : ℝ, ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ r ∈ radialCore D, deriv D.w r = 0 →
      ∀ a d : ℕ, a + d ≤ N →
      ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => iteratedDeriv (b + d) (radialBoundaryJet
          (fun p => polarDiscriminant (stateProfile D S C (liftSectorParameter S C z).1)
            (stateHeight D S C (liftSectorParameter S C z)) p ^ γ) r a) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood S base ε ε,
      pairGrading (sectorGrading S) realGrading B z ≤ 1 →
      ∀ v : Fin k → (StateDirections S × ℝ),
      (∀ j, pairGrading (sectorGrading S) realGrading B (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading S) realGrading (s + inputLoss) z ≤ R →
      (∀ j, pairGrading (sectorGrading S) realGrading (s + inputLoss) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
          R ^ ((b : ℝ) / ((s : ℝ) + 1)) := by
  classical
  let data := n04PositiveGeometry_rootDiscKernelTerm_finite_power
    hT hS hN hε hE N requestedBase
  let B := data.choose
  let inputLoss := data.choose_spec.choose
  have hB := data.choose_spec.choose_spec.1
  have hterms := data.choose_spec.choose_spec.2
  let count : ℝ := 1 + ∑ j : Fin (N + 1), (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hcount : 1 ≤ count := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hcard (n : ℕ) (hn : n ≤ N) :
      (Fintype.card (OrderedFinpartition n) : ℝ) ≤ count := by
    let j : Fin (N + 1) := ⟨n, by omega⟩
    exact (Finset.single_le_sum
      (f := fun i : Fin (N + 1) => (Fintype.card (OrderedFinpartition i.val) : ℝ))
      (fun i _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition i.val)))
      (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1))
  refine ⟨B, inputLoss, hB, fun γ K s => ?_⟩
  let orderData := hterms γ K s
  let C0 := orderData.choose
  let A := orderData.choose_spec.choose
  have hC0 := orderData.choose_spec.choose_spec.1
  have hA := orderData.choose_spec.choose_spec.2.1
  have hb := orderData.choose_spec.choose_spec.2.2
  refine ⟨count * C0, A, one_le_mul_of_one_le_of_one_le hcount hC0, hA, ?_⟩
  intro r hr hroot a d had b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let Ji := fun c : OrderedFinpartition (a + d) =>
    n04PositiveGeometry_rootDiscKernelTerm_joint hT hS hN hε hr hroot γ
      c (cylinderMixedWord a d)
  let g : ((StateDirections S × ℝ) × ℝ) → ℝ := fun y => iteratedDeriv d
    (radialBoundaryJet (fun p => polarDiscriminant
      (stateProfile D S C (liftSectorParameter S C y.1).1)
      (stateHeight D S C (liftSectorParameter S C y.1)) p ^ γ) r a) y.2
  have heq : EqOn (fun y => ∑ c : OrderedFinpartition (a + d),
      n04PositiveGeometry_rootDiscKernel γ c.length
        (n04PositiveGeometry_rootSpatialInput (D := D) (C := C)
          c (cylinderMixedWord a d) r y)) g
        (sectorNeighborhood S base ε ε ×ˢ univ) := by
    intro y hy
    exact (n04PositiveGeometry_physicalRootDiscPowerTrace_kernel_formula
      hT hS hN hr hroot y.1 hy.1 γ a d y.2).symm
  let Jg : SmoothDirections (sectorNeighborhood S base ε ε)
      (fun y => iteratedDeriv b (fun η => g (y, η)) θ) :=
    J.congr (fun y _ => (congrFun (circle_iteratedDeriv_iteratedDeriv
      (radialBoundaryJet (fun p => polarDiscriminant
        (stateProfile D S C (liftSectorParameter S C y).1)
        (stateHeight D S C (liftSectorParameter S C y)) p ^ γ) r a) b d) θ).symm)
  let M := C0 * T.E0 r ^ A * parameterHeightWeight (T.H r ^ scalarBeta) k *
    R ^ ((b : ℝ) / ((s : ℝ) + 1))
  have hsum := n04PositiveGeometry_angularFiniteSum_parameter_bound Ji
    (sectorNeighborhood_isOpen S base ε ε) heq k b z hz θ v Jg (fun _ => M)
      (fun c => hb r hr hroot (a + d) had c (cylinderMixedWord a d) b hbs θ
        (smoothDirections_angularStateSlice (Ji c) b θ) k hk z hz hzlow v hv R hR hzR hvR)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg (mul_nonneg (zero_le_one.trans hC0)
      (Real.rpow_nonneg (zero_le_one.trans (hE r hr)) _))
      (parameterHeightWeight_nonneg (Real.rpow_nonneg (hT.2.1 r hr).2.1.le _) k))
    (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hc := mul_le_mul_of_nonneg_right (hcard (a + d) had) hM
  have hsum' : ‖J.D k z v‖ ≤ (Fintype.card (OrderedFinpartition (a + d)) : ℝ) * M := by
    simpa only [Jg, SmoothDirections.congr, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hsum
  exact hsum'.trans (hc.trans_eq (by dsimp only [M]; ring))

def n04PositiveGeometry_rootDiscPowerTrace (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (γ r σ : ℝ) (a : ℕ)
    (z : (StateDirections S × ℝ) × ℝ) : ℝ :=
  radialBoundaryJet (fun p => polarDiscriminant
    (stateProfile D S C (liftSectorParameter S C z.1).1)
    (stateHeight D S C (liftSectorParameter S C z.1)) (rootProfileShift r σ p) ^ γ) 0 a z.2

theorem n04PositiveGeometry_rootDiscPowerTrace_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) {r : ℝ} (hr : r ∈ radialCore D)
    (z : StateDirections S × ℝ) (hz : z ∈ sectorNeighborhood S base ε ε)
    (γ σ : ℝ) (a : ℕ) (θ : ℝ) :
    n04PositiveGeometry_rootDiscPowerTrace D S C γ r σ a (z, θ) =
      σ ^ a * radialBoundaryJet
        (fun p => polarDiscriminant (stateProfile D S C (liftSectorParameter S C z).1)
          (stateHeight D S C (liftSectorParameter S C z)) p ^ γ) r a θ := by
  have hregular := N01Properties.characteristic_coefficient_regular hN hS hT
    (liftSectorParameter_mem_stateNeighborhood hz le_rfl)
    (hN.2.2.1.liftSectorParameter_sector z) (p := (r, θ)) ⟨hr, mem_univ θ⟩
  exact n04PositiveGeometry_radialBoundaryJet_rootShift a
    (hregular.2.2.2.2.2.rpow_const_of_ne hregular.2.1.ne')

def n04PositiveGeometry_rootDiscPowerTrace_joint
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    {r : ℝ} (hr : r ∈ radialCore D) (hroot : deriv D.w r = 0)
    (γ σ : ℝ) (a : ℕ) :
    SmoothDirections (sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ))
      (n04PositiveGeometry_rootDiscPowerTrace D S C γ r σ a) := by
  let JP := n04PositiveGeometry_physicalRootDiscPowerTrace_joint hT hS hN hε hr hroot γ a 0
  apply (smoothDirections_postcompCLM JP
    ((σ ^ a) • ContinuousLinearMap.id ℝ ℝ)).congr
  intro y hy
  simpa only [Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, iteratedDeriv_zero] using
    (n04PositiveGeometry_rootDiscPowerTrace_eq hT hS hN hr y.1 hy.1 γ σ a y.2).symm

/-- The actual inward radial orders zero through three and angular
reserve five retain the saved power for any supplied parameter shift.
The low base is chosen before that shift and before the real exponent. -/
theorem n04PositiveGeometry_rootDiscPower_sample_prefix
    (W : N04RealizationStart) (X : N04RealizationChoice W)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) :
    ∃ low : ℕ, base ≤ low ∧ ∀ γ : ℝ, ∀ K shift s : ℕ,
      ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, (X.src i side).val = some m →
      ∀ a : ℕ, a ≤ 3 → ∀ d : ℕ, d ≤ 5 → ∀ u : ℕ, u ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε)
        (fun z => iteratedDeriv (u + d) (fun η => n04PositiveGeometry_rootDiscPowerTrace
          W.D W.S W.C γ (n01ComponentRoot W.C m (!side))
          (n01ComponentRootOrientation (!side)) a (z, η)) θ),
      ∀ k : ℕ, k ≤ K → ∀ z ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low z ≤ 1 →
      ∀ v : Fin k → (StateDirections W.S × ℝ),
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j) ≤ 1) →
      ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) z ≤ R →
      (∀ j, pairGrading (sectorGrading W.S) realGrading
        (low + s + shift * K + 1) (v j) ≤ R) →
        ‖J.D k z v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
          parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k *
          R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hN := n01Properties_restrict W.hT W.through03.1.1 hb le_rfl hε hεW
  let data := n04PositiveGeometry_physicalRootDiscPowerTrace_finiteShift_power
    W.hT W.hS hN hεone (fun r _ => W.floor r) 8 base
  let B := data.choose
  let inputLoss := data.choose_spec.choose
  have hB := data.choose_spec.choose_spec.1
  have hphysical := data.choose_spec.choose_spec.2
  let low := max B inputLoss
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  refine ⟨low, hB.trans (le_max_left _ _), fun γ K shift s => ?_⟩
  let orderData := hphysical γ K (s + shift * K)
  let C0 := orderData.choose
  let A0 := orderData.choose_spec.choose
  have hC0 := orderData.choose_spec.choose_spec.1
  have hA0 := orderData.choose_spec.choose_spec.2.1
  have hbound := orderData.choose_spec.choose_spec.2.2
  let sampleData := n04PositiveGeometry_positiveEndpoint_parameter_weight W X
    (γ := (3 / 4 : ℝ)) (by norm_num) hA0 (zero_le_one.trans hC0)
  let A := sampleData.choose
  have hA := sampleData.choose_spec.1
  have hsample := sampleData.choose_spec.2
  refine ⟨A, hA, ?_⟩
  intro i side m hm a ha d hd u hu θ J k hk z hz hzlow v hv R hR hzR hvR
  let r := n01ComponentRoot W.C m (!side)
  let σ := n01ComponentRootOrientation (!side)
  have hrad : r = n04PositiveEndpoint i side := by
    have he : n04PositiveEndpoint i side = (if side then W.C.left m else W.C.right m) := by
      simpa only [hm] using (X.src i side).property
    cases side <;> exact he.symm
  have hr : r ∈ radialCore W.D := by rw [hrad]; exact (W.roots i side).1
  have hroot : deriv W.D.w r = 0 := by rw [hrad]; exact (W.roots i side).2.1
  have hhigh : s + shift * K + inputLoss ≤ low + s + shift * K + 1 := by
    have : inputLoss ≤ low := le_max_right _ _
    omega
  let JP := n04PositiveGeometry_physicalRootDiscPowerTrace_joint
    W.hT W.hS hN hεone hr hroot γ a 0
  let JA := smoothDirections_angularStateSlice JP (u + d) θ
  have hraw := hbound r hr hroot a d (by omega) u (by omega) θ JA k hk z hz
    ((hp (le_max_left B inputLoss) z).trans hzlow) v
    (fun j => (hp (le_max_left B inputLoss) (v j)).trans (hv j)) R hR
    ((hp hhigh z).trans hzR) (fun j => (hp hhigh (v j)).trans (hvR j))
  have he : EqOn
      (fun y => iteratedDeriv (u + d)
        (fun η => n04PositiveGeometry_rootDiscPowerTrace W.D W.S W.C γ r σ a (y, η)) θ)
      (fun y => σ ^ a * iteratedDeriv (u + d) (radialBoundaryJet
        (fun q => polarDiscriminant (stateProfile W.D W.S W.C (liftSectorParameter W.S W.C y).1)
          (stateHeight W.D W.S W.C (liftSectorParameter W.S W.C y)) q ^ γ) r a) θ)
      (sectorNeighborhood W.S base ε ε) := by
    intro y hy
    have htrace := funext (fun η =>
      n04PositiveGeometry_rootDiscPowerTrace_eq W.hT W.hS hN hr y hy γ σ a η)
    exact (congrArg (fun f : ℝ → ℝ => iteratedDeriv (u + d) f θ) htrace).trans
      (iteratedDeriv_const_mul_field (σ ^ a) _)
  have hσa : |σ ^ a| ≤ 1 := by
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg σ)
    cases side <;> norm_num [σ, n01ComponentRootOrientation]
  have horiented := (n04PositiveGeometry_parameter_constMul_bound
    JA J (σ ^ a) he k z hz v hraw).trans
      (mul_le_of_le_one_left ((norm_nonneg _).trans hraw) hσa)
  have hcost : C0 * W.T.E0 r ^ A0 * parameterHeightWeight (W.T.H r ^ scalarBeta) k ≤
      A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
        parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) k := by
    rw [hrad]
    exact hsample i side k
  have hpower : R ^ ((u : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) ≤
      R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le hR
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show u ≤ u + shift * k by omega)
  have hH := Real.rpow_nonneg
    (W.hT.2.1 _ (materialSample_mem_interval W.radial.1 W.hT (X.cell i))).2.1.le
    (3 / 4 : ℝ)
  exact horiented.trans (mul_le_mul hcost hpower (Real.rpow_nonneg (zero_le_one.trans hR) _)
    (mul_nonneg (mul_nonneg (zero_le_one.trans hA)
      (Real.rpow_nonneg (zero_le_one.trans
        ((W.floor _).trans (le_enlargedMaterialData_E0 W.T _))) _))
        (parameterHeightWeight_nonneg hH k)))

end ContinuousFlexibility.Analysis
