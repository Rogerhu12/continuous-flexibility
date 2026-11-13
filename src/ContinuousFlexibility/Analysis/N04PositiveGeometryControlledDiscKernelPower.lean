import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledDiscTrace

/-!
# Material bounds for the discriminant power kernel

The spatial packet bound fixes one compact radius and one low base
before the exponent or any future parameter and angular budget.
Ordinary outer derivatives on that fixed compact set are combined with
the actual six-coordinate input estimates. The resulting material cost
is polynomial and retains the full positive-parameter height factor.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Function ContinuousFlexibility.Statements
open scoped ContDiff BigOperators

local instance n04ControlledDiscKernelPowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- Every actual discriminant partition term retains the original
parameter height factor. The low base and spatial loss are selected
before the real exponent and all future derivative orders. -/
theorem n04PositiveGeometry_rootDiscKernelTerm_finite_power
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (hε : ε ≤ 1)
    (hE : ∀ r ∈ radialCore D, 1 ≤ T.E0 r) (N requestedBase : ℕ) :
    ∃ B inputLoss : ℕ, requestedBase ≤ B ∧ ∀ γ : ℝ, ∀ K s : ℕ,
      ∃ C0 A : ℝ, 1 ≤ C0 ∧ 0 ≤ A ∧
      ∀ r ∈ radialCore D, deriv D.w r = 0 →
      ∀ n : ℕ, n ≤ N → ∀ c : OrderedFinpartition n, ∀ w : Fin n → Fin 2,
      ∀ b : ℕ, b ≤ s → ∀ θ : ℝ,
      ∀ J : SmoothDirections (sectorNeighborhood S base ε ε)
        (fun z => iteratedDeriv b (fun η => n04PositiveGeometry_rootDiscKernel γ c.length
          (n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r (z, η))) θ),
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
  let hpacketData :=
    n04PositiveGeometry_rootPacketSector_finiteShift_power
      (C := C) (base := base) hN.1.1 hT hS hε hE N (max requestedBase (N + 7))
  let B : ℕ := hpacketData.choose
  let inputLoss : ℕ := hpacketData.choose_spec.choose
  have hB : max requestedBase (N + 7) ≤ B := hpacketData.choose_spec.choose_spec.1
  have hpacket := hpacketData.choose_spec.choose_spec.2
  have hrequested : requestedBase ≤ B := (le_max_left _ _).trans hB
  have hBN : N + 7 ≤ B := (le_max_right _ _).trans hB
  let hcompactData :=
    n04PositiveGeometry_rootSpatialInput_uniform_bound hN.1.1 hT hS C N
  let M0 : ℝ := hcompactData.choose
  have hcompact := hcompactData.choose_spec.2
  let hheightData := materialHeight_E0_weight_bounded
    hT (γ := scalarBeta) (by norm_num [scalarBeta]) 0
  let L0 : ℝ := hheightData.choose
  have hL0 : 0 < L0 := hheightData.choose_spec.1
  have hheight := hheightData.choose_spec.2
  let L : ℝ := max 1 L0
  have hL : 1 ≤ L := le_max_left _ _
  let p := pairGrading (sectorGrading S) realGrading
  refine ⟨B, inputLoss, hrequested, fun γ K s => ?_⟩
  let hpdata := hpacket K s
  let Cp : ℝ := hpdata.choose
  let Ap : ℝ := hpdata.choose_spec.choose
  have hCp : 1 ≤ Cp := hpdata.choose_spec.choose_spec.1
  have hAp : 0 ≤ Ap := hpdata.choose_spec.choose_spec.2.1
  have hpbound := hpdata.choose_spec.choose_spec.2.2
  let houterData := fun j : Fin (N + 1) =>
    n04PositiveGeometry_rootDiscKernel_finite_bound γ j.val (s + K) M0
  let Co : Fin (N + 1) → ℝ := fun j => (houterData j).choose
  have hCo (j : Fin (N + 1)) : 0 < Co j := (houterData j).choose_spec.1
  have houter (j : Fin (N + 1)) := (houterData j).choose_spec.2
  let CK : ℝ := 1 + ∑ j : Fin (N + 1), Co j
  have hCK : 1 ≤ CK := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => (hCo j).le))
  have hCoCK (j : Fin (N + 1)) : Co j ≤ CK :=
    (Finset.single_le_sum (fun i _ => (hCo i).le) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)
  let Pcount : ℝ := 1 + ∑ j : Fin (s + K + 1),
    (Fintype.card (OrderedFinpartition j.val) : ℝ)
  have hPcount : 1 ≤ Pcount := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _))
  have hcount (j : ℕ) (hj : j ≤ s + K) :
      (Fintype.card (OrderedFinpartition j) : ℝ) ≤ Pcount := by
    let t : Fin (s + K + 1) := ⟨j, by omega⟩
    exact (Finset.single_le_sum
      (f := fun i : Fin (s + K + 1) => (Fintype.card (OrderedFinpartition i.val) : ℝ))
      (fun i _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition i.val)))
      (Finset.mem_univ t)).trans
        (le_add_of_nonneg_left (zero_le_one : (0 : ℝ) ≤ 1))
  let Cfinal : ℝ := Pcount * CK * Cp ^ (s + K) * L ^ (s + K)
  have hCfinal : 1 ≤ Cfinal := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hPcount hCK)
      (one_le_pow₀ hCp)) (one_le_pow₀ hL)
  refine ⟨Cfinal, Ap * (s + K : ℕ), hCfinal, mul_nonneg hAp (Nat.cast_nonneg _), ?_⟩
  intro r hr hroot n hn c w b hbs θ J k hk z hz hzlow v hv R hR hzR hvR
  let f : (Fin (c.length + 1) × Fin 6) → ((StateDirections S × ℝ) × ℝ) → ℝ :=
    fun ij y => n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r y ij
  let Jf := n04PositiveGeometry_rootSpatialInput_coordinateJoint
    (C := C) (base := base) hN.1.1 hT hS hε hr c w
  let Ja := fun ij a η => smoothDirections_angularStateSlice (Jf ij) a η
  let g := n04PositiveGeometry_rootDiscKernel γ c.length
  have hV := n04PositiveGeometry_rootDiscKernelDomain_open c.length
  have hg := n04PositiveGeometry_rootDiscKernel_contDiff γ c.length
  have hmap := n04PositiveGeometry_rootSpatialInput_mapsTo_discKernel hT hS hN hr hroot c w
  let JT := n04PositiveGeometry_rootSpatialInput_joint
    (C := C) (base := base) hN.1.1 hT hS hε hr c w
  let Q := JT.comp_contDiff hV hg hmap
  let H := T.H r ^ scalarBeta
  let E := T.E0 r
  let M := Cp * E ^ Ap
  let t := R ^ (1 / ((s : ℝ) + 1))
  have hE1 : 1 ≤ E := hE r hr
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le hCp (Real.one_le_rpow hE1 hAp)
  have hH : 0 ≤ H := Real.rpow_nonneg (hT.2.1 r hr).2.1.le _
  have hHL : H ≤ L := by
    have hb : H ≤ L0 := calc
      H = H * T.E0 r ^ (0 : ℝ) := by rw [Real.rpow_zero, mul_one]
      _ ≤ L0 := hheight r hr
    exact hb.trans (le_max_right _ _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hpow (j : ℕ) : R ^ ((j : ℝ) / ((s : ℝ) + 1)) = t ^ j := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hR)]
    congr 1
    ring
  let v0 : N04RootRadialPacket c.length :=
    n04PositiveGeometry_rootSpatialInput (D := D) (C := C) c w r (z, θ)
  have hzθ : (z, θ) ∈ sectorNeighborhood S base ε ε ×ˢ (univ : Set ℝ) :=
    ⟨hz, mem_univ θ⟩
  have hpoint : ‖v0‖ ≤ M0 := hcompact B hBN z hzlow r hr θ n hn c w
  have hden : (1 / 2 : ℝ) ≤ n06RootNormalizedDiscriminant (fun ij => v0 (0, ij)) :=
    (n04PositiveGeometry_rootSpatialInput_denominators hT hS hN hr hroot c w
      (z := (z, θ)) hzθ).2
  let j : Fin (N + 1) := ⟨c.length, by have := c.length_le; omega⟩
  have houter' (a : ℕ) (ha : a ≤ b + k) :
      ‖iteratedFDeriv ℝ a g (fun ij => f ij (z, θ))‖ ≤ CK := by
    have ha' : a ≤ s + K := ha.trans (Nat.add_le_add hbs hk)
    have hraw : ‖iteratedFDeriv ℝ a (n04PositiveGeometry_rootDiscKernel γ c.length) v0‖ ≤
        Co j := houter j a ha' v0 hpoint hden
    exact hraw.trans (hCoCK j)
  let P : (StateDirections S × ℝ) → Prop := fun y => p B y ≤ 1 ∧ p (s + inputLoss) y ≤ R
  have hzero : P 0 :=
    ⟨(p B).map_zero'.trans_le zero_le_one,
      (p (s + inputLoss)).map_zero'.trans_le (zero_le_one.trans hR)⟩
  have hinputs (ij : Fin (c.length + 1) × Fin 6) (e u : ℕ)
      (he : e ≤ k) (hu : u ≤ b) (dirs : Fin e → StateDirections S × ℝ)
      (hdirs : ∀ a, P (dirs a)) :
      ‖(Ja ij u θ).D e z dirs‖ ≤ M * parameterHeightWeight H e * t ^ (u + 0 * e) := by
    let ar := n04PositiveGeometry_rootPartitionRadialOrder c w ij.1
    let ad := n04PositiveGeometry_rootPartitionAngularOrder c w ij.1
    let Jm := (Ja ij u θ).congr (fun y _ =>
      n04PositiveGeometry_iteratedDeriv_mixedTrace isOpen_univ
        (((contDiff_apply ℝ ℝ ij.2).comp
          (n06_actualRootAbsorbedCoordinates_contDiff hN.1.1 hT hS
            (liftSectorParameter S C y))).contDiffOn)
        r (fun _ => mem_univ _) ar ad u θ)
    have hb := hpbound ij.2 ar ad
      ((n04PositiveGeometry_rootPartition_orders_le c w ij.1).trans hn)
      u (hu.trans hbs) r hr θ Jm e (he.trans hk) z hz hzlow dirs
      (fun a => (hdirs a).1) R hR hzR (fun a => (hdirs a).2)
    simpa only [Jm, SmoothDirections.congr, Real.norm_eq_abs, M, H, E,
      Nat.zero_mul, Nat.add_zero, hpow] using hb
  have hb := n04PositiveGeometry_angularKernel_parameter_bound
    (sectorNeighborhood_isOpen S base ε ε) Jf Ja hV hg hmap Q k b 0 z hz θ P hzero
    (zero_le_one.trans hCK) hM hH hHL hL ht houter' hinputs J v (fun a => ⟨hv a, hvR a⟩)
  have hcoef : (Fintype.card (OrderedFinpartition (b + k)) : ℝ) * CK *
      M ^ (b + k) * L ^ (b + k) ≤ Cfinal * E ^ (Ap * (s + K : ℕ)) := by
    calc
      _ ≤ Pcount * CK * M ^ (s + K) * L ^ (s + K) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (hcount (b + k) (by omega))
          (zero_le_one.trans hCK)) (pow_le_pow_right₀ hM (by omega))
          (pow_nonneg (zero_le_one.trans hM) _) (mul_nonneg (zero_le_one.trans hPcount)
            (zero_le_one.trans hCK))) (pow_le_pow_right₀ hL (by omega))
          (pow_nonneg (zero_le_one.trans hL) _)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hPcount) (zero_le_one.trans hCK))
            (pow_nonneg (zero_le_one.trans hM) _))
      _ = _ := by
        dsimp only [M, Cfinal]
        rw [mul_pow, ← Real.rpow_mul_natCast (zero_le_one.trans hE1)]
        ring
  have hf := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (parameterHeightWeight_nonneg hH k))
    (pow_nonneg (zero_le_one.trans ht) b)
  exact hb.trans (by simpa only [Nat.zero_mul, Nat.add_zero, hpow, H, E] using hf)

end ContinuousFlexibility.Analysis
