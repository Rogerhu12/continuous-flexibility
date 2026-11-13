import ContinuousFlexibility.Analysis.N04NegativeInverseRawEnvelope
import ContinuousFlexibility.Analysis.N04NegativeInverseActualSystem
import ContinuousFlexibility.Analysis.N04NegativeInverseCoefficientBounds
import ContinuousFlexibility.Analysis.N04NegativeInverseJointCollector

/-!
# Closing the inverse and pulled-height joint prefixes

The forward interface is expressed on the actual inverse image in the
original physical component. The common state neighborhood and its low
grading are fixed before the parameter and spatial orders are chosen.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

/-- Reindex before instantiating a concrete physical grading. -/
private theorem negativeInverse_grading_index_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℕ → Seminorm ℝ E) {a b : ℕ} (hab : a = b)
    {x : E} {R : ℝ} (h : p b x ≤ R) : p a x ≤ R := by
  simpa only [hab] using h

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Quantitative forward data at every actual normalized inverse
point. The shift is chosen before the requested spatial prefix. -/
def NegativeInverseForwardPrefixes
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) : Prop :=
  ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ N : ℕ, ∃ B : ℝ, 1 ≤ B ∧
    ∀ k m : ℕ, ∀ side : Bool, ∀ hi : G.e k = .inl (m, side),
    ∀ z ∈ sectorNeighborhood G.W.S base ε ε, ∀ q ∈ unitStrip,
    ∀ R : ℝ, 1 ≤ R → parameterGrading G.W.S (base + N + shift * K + 1) z ≤ R →
    let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell k))
    let H := G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ)
    let t := R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))
    N04NegativeInverseJet.UnitPrefix (G.negativeInverseForwardOn 0 hadm k m side hi)
      (z, G.pulledPoint 0 (G.lift 0 z) k q)
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * K + 1))
      N K shift (B * E ^ B) H R t ∧
    N04NegativeInverseJet.UnitPrefix (G.negativeInverseHeightOn 0 hadm k m side hi)
      (z, G.pulledPoint 0 (G.lift 0 z) k q)
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * K + 1))
      N K shift (B * E ^ B) H R t ∧
    |planeJacobian ((G.V 0).chart (G.lift 0 z) k)
      (G.pulledPoint 0 (G.lift 0 z) k q)|⁻¹ ≤ B * E ^ B ∧
    ‖G.negativeInverseCanonicalLinear 0 k‖ ≤ B * E ^ B

private theorem negativeInverse_jointPrefix_pair
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε)
    (hprefix : G.NegativeInverseForwardPrefixes hadm)
    (k : ℕ) (hk : 0 < k) :
    ∃ shift : ℕ, ∀ s : ℕ, ∃ D : ℝ, 0 < D ∧
    ∀ i, G.Neg 0 i →
    ∀ J : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint => G.pulledPoint 0 (G.lift 0 x.1) i x.2),
    ∀ Q : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint => G.pulledHeight 0 x.1 i x.2),
    ∀ z ∈ sectorNeighborhood G.W.S base ε ε, ∀ q ∈ unitStrip,
    ∀ n : ℕ, ∀ w : StateAngleWord n, w.stateArity = k → w.angleArity ≤ s →
    ∀ v : Fin n → Parameter G.W.S × PolarPoint,
    (∀ a, parameterGrading G.W.S base (v a).1 ≤ 1) →
    ∀ R : ℝ, 1 ≤ R → parameterGrading G.W.S (base + s + shift * k + 1) z ≤ R →
    (∀ a, parameterGrading G.W.S (base + s + shift * k + 1) (v a).1 ≤ R) →
    (∀ a, ‖(v a).2‖ ≤ 1) →
    (∀ a, w.isState a = false → (v a).1 = 0) →
    (∀ a, w.isState a = true → (v a).2 = 0) →
    let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell i))
    let H := G.W.U.H (G.W.U.sample ((G.V 0).cell i)) ^ (3 / 4 : ℝ)
    let scale := R ^ (((w.angleArity + shift * k - 1 : ℕ) : ℝ) /
      (((s + shift * k : ℕ) : ℝ) + 1))
    ‖J.D n (z, q) v‖ ≤ D * E ^ D * H * scale ∧
      ‖Q.D n (z, q) v‖ ≤ D * E ^ D * H * scale := by
  letI : LocallyConvexSpace ℝ (Parameter G.W.S) :=
    (sectorPairGrading_withSeminorms G.W.S).toLocallyConvexSpace
  obtain ⟨L, hL, hheight⟩ := G.negativeInverse_height_uniform
  let orderData := hprefix k
  let shift : ℕ := orderData.choose
  have hshift : 1 ≤ shift := orderData.choose_spec.1
  have hf := orderData.choose_spec.2
  refine ⟨shift + 1, fun s => ?_⟩
  let N : ℕ := k + s
  let boundData := hf N
  let B : ℝ := boundData.choose
  have hB : 1 ≤ B := boundData.choose_spec.1
  have hforward := boundData.choose_spec.2
  obtain ⟨D, hD, hcoeff⟩ := n04NegativeInverse_normalizedMajorants_envelope N hB hL
  refine ⟨D, zero_lt_one.trans_le hD, ?_⟩
  intro i hi J Q z hz q hq n w hw hs v hl R hR hzR hvR hp hvstate hvspace
  let indexData : ∃ j : ℕ × Bool, G.e i = .inl j := (G.neg_iff_inl 0 i).mp hi
  let j : ℕ × Bool := indexData.choose
  have hi' : G.e i = .inl j := indexData.choose_spec
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V 0).cell i))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V 0).cell i)) ^ (3 / 4 : ℝ)
  let t : ℝ := R ^ (1 / (((N + shift * k : ℕ) : ℝ) + 1))
  let C : ℝ := B * E ^ B
  let A := G.negativeInverseCanonicalLinear 0 i
  let c : PolarPoint := ((G.V 0).left i, 0)
  let M := n04NegativeInverse_prefixMajorant (2 * C * C) C L N
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 i
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 i) _
  have hHL : H ≤ L := hheight i
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hC : 1 ≤ C := n04NegativeInverse_envelope_one_le hB hE
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hM : 1 ≤ M := n04NegativeInverse_prefixMajorant_one_le
    (mul_nonneg (mul_nonneg (by norm_num) hC0) hC0) hC0 (zero_le_one.trans hL) N
  have hn : 0 < n := by have hsum := w.arity_sum; omega
  have hnN : n ≤ N := by have hsum := w.arity_sum; dsimp only [N]; omega
  have hβN : w.angleArity ≤ N := by have hsum := w.arity_sum; omega
  have hden : N + shift * k = s + (shift + 1) * k := by
    dsimp only [N]
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hindex : base + N + shift * k + 1 = base + s + (shift + 1) * k + 1 := by
    omega
  have hzR' : parameterGrading G.W.S (base + N + shift * k + 1) z ≤ R :=
    negativeInverse_grading_index_le (parameterGrading G.W.S) hindex hzR
  have hvR' (a : Fin n) :
      parameterGrading G.W.S (base + N + shift * k + 1) (v a).1 ≤ R :=
    negativeInverse_grading_index_le (parameterGrading G.W.S) hindex (hvR a)
  have forwardData :=
    hforward i j.1 j.2 hi' z hz q hq R hR hzR'
  have hfwd := forwardData.1
  have hscalar := forwardData.2.1
  have hdet := forwardData.2.2.1
  have hlinear := forwardData.2.2.2
  let JF := G.negativeInverseForwardOn 0 hadm i j.1 j.2 hi'
  let KG := G.negativeInverseCanonicalOn 0 hadm i j.1 j.2 hi'
  let JH := G.negativeInverseHeightOn 0 hadm i j.1 j.2 hi'
  let QH := G.negativeInversePulledHeightOn 0 hadm i j.1 j.2 hi'
  have hpull : G.pulledPoint 0 (G.lift 0 z) i q =
      (G.V 0).inverseChart (G.lift 0 z) i (c + A q) := by
    unfold pulledPoint
    rw [G.negativeInverseUnit_eq_affine]
  have hmap : MapsTo (fun a => c + A a) unitStrip (G.negativeInverseTarget j.1) := by
    intro a ha
    change ((G.V 0).left i, 0) + G.negativeInverseCanonicalLinear 0 i a ∈ _
    rw [← G.negativeInverseUnit_eq_affine]
    exact G.negativeInverseUnit_maps 0 i j.1 j.2 hi' ha
  let J' : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint =>
        (G.V 0).inverseChart (G.lift 0 x.1) i (c + A x.2)) :=
    J.congrOn (fun x _ => by
      unfold pulledPoint
      rw [G.negativeInverseUnit_eq_affine])
  let Q' : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint =>
        (G.V 0).height (G.lift 0 x.1) i
          ((G.V 0).inverseChart (G.lift 0 x.1) i (c + A x.2))) :=
    Q.congrOn (fun x _ => by
      unfold pulledHeight heightField pulledPoint
      rw [G.negativeInverseUnit_eq_affine])
  have hfwd' : N04NegativeInverseJet.UnitPrefix JF
      (z, (G.V 0).inverseChart (G.lift 0 z) i (c + A q))
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t := by
    rw [← hpull]
    exact hfwd
  have hscalar' : N04NegativeInverseJet.UnitPrefix JH
      (z, (G.V 0).inverseChart (G.lift 0 z) i (c + A q))
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t := by
    rw [← hpull]
    exact hscalar
  have hdet' : |planeJacobian ((G.V 0).chart (G.lift 0 z) i)
      ((G.V 0).inverseChart (G.lift 0 z) i (c + A q))|⁻¹ ≤ C := by
    rw [← hpull]
    exact hdet
  have hpoint := N04NegativeInverseJet.normalized_inverse_prefix_norm_le JF KG
    (sectorNeighborhood_isOpen G.W.S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (isOpen_Ioo.prod isOpen_univ)
    (G.negativeInverseCanonical_maps 0 hadm i j.1 j.2 hi')
    (fun x hx => G.negativeInverseCanonical_jacobian_ne_zero 0 hadm i j.1 j.2 hi' hx)
    (fun x hx => G.negativeInverseCanonical_right 0 hadm i j.1 j.2 hi' hx)
    A c hmap J' (parameterGrading G.W.S base)
    (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift hshift hz hq
    hC0 hC0 hC0 hH hHL hL (zero_le_one.trans hR) (zero_le_one.trans ht)
    hdet' hlinear hfwd' n hn hnN w hw.le v hl hvR' hp hvstate hvspace
  have hheightRaw := N04NegativeInverseJet.normalized_scalar_prefix_norm_le JF KG JH
    (sectorNeighborhood_isOpen G.W.S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (isOpen_Ioo.prod isOpen_univ)
    (G.negativeInverseCanonical_maps 0 hadm i j.1 j.2 hi')
    (fun x hx => G.negativeInverseCanonical_jacobian_ne_zero 0 hadm i j.1 j.2 hi' hx)
    (fun x hx => G.negativeInverseCanonical_right 0 hadm i j.1 j.2 hi' hx)
    A c hmap QH Q' (parameterGrading G.W.S base)
    (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift hshift hz hq
    hC0 hC0 hC0 hH hHL hL (zero_le_one.trans hR) (zero_le_one.trans ht)
    hdet' hlinear hfwd' hscalar' n hn hnN w hw.le v hl hvR' hp hvstate hvspace
  change ‖J.D n (z, q) v‖ ≤ (M * C ^ w.angleArity) *
    parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity - 1)
    at hpoint
  change ‖Q.D n (z, q) v‖ ≤
    (n04NegativeInverse_partitionMajorant C M L n * C ^ w.angleArity) *
    parameterHeightWeight H w.stateArity * t ^ (w.angleArity + shift * w.stateArity - 1)
    at hheightRaw
  have hcoef := hcoeff E hE
  have hpointC : M * C ^ w.angleArity ≤ D * E ^ D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hβN) (zero_le_one.trans hM)).trans hcoef.1
  have hheightC : n04NegativeInverse_partitionMajorant C M L n * C ^ w.angleArity ≤
      D * E ^ D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hβN)
      (n04NegativeInverse_partitionMajorant_nonneg hC0 (zero_le_one.trans hM)
        (zero_le_one.trans hL) n)).trans (hcoef.2 n hnN)
  have hfinish (a : ℝ) (ha : a ≤ D * E ^ D * parameterHeightWeight H w.stateArity *
      t ^ (w.angleArity + shift * w.stateArity - 1)) :
      a ≤ D * E ^ D * H * R ^ (((w.angleArity + (shift + 1) * k - 1 : ℕ) : ℝ) /
        (((s + (shift + 1) * k : ℕ) : ℝ) + 1)) := by
    rw [hw, parameterHeightWeight, if_neg (Nat.ne_of_gt hk)] at ha
    have hd : w.angleArity + shift * k - 1 ≤ w.angleArity + (shift + 1) * k - 1 := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hp (d : ℕ) : t ^ d =
        R ^ ((d : ℝ) / (((s + (shift + 1) * k : ℕ) : ℝ) + 1)) := by
      dsimp only [t]
      rw [n04NegativeInverse_commonScale_pow (zero_le_one.trans hR), hden]
    calc
      a ≤ D * E ^ D * H * t ^ (w.angleArity + shift * k - 1) := ha
      _ ≤ D * E ^ D * H * t ^ (w.angleArity + (shift + 1) * k - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hd)
          (mul_nonneg (mul_nonneg (zero_le_one.trans hD)
            (Real.rpow_nonneg (zero_le_one.trans hE) _)) hH)
      _ = _ := by rw [hp]
  constructor
  · apply hfinish
    exact hpoint.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpointC (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))
  · apply hfinish
    exact hheightRaw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hheightC (parameterHeightWeight_nonneg hH _))
      (pow_nonneg (zero_le_one.trans ht) _))

/-- The actual forward prefixes close both retained inverse outputs
on the same fixed neighborhood. The extra parameter shift accounts
for using total order `k + s` in the finite implicit recurrence. -/
theorem negativeInverse_jointPrefixes_of_forward
    {base : ℕ} {ε : ℝ} (hadm : G.Admissible base ε) (_hsmall : ε ≤ 1 / 2)
    (hprefix : G.NegativeInverseForwardPrefixes hadm) :
    N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) base ε
      (fun z i q => G.pulledPoint 0 (G.lift 0 z) i q) ∧
    N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) base ε
      (G.pulledHeight 0) := by
  have hsub : sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ unitStrip :=
    fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩
  have hopen : IsOpen (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip) :=
    (sectorNeighborhood_isOpen G.W.S base ε ε).prod (isOpen_Ioo.prod isOpen_univ)
  constructor
  · intro k hk
    let orderData := G.negativeInverse_jointPrefix_pair hadm hprefix k hk
    let shift : ℕ := orderData.choose
    have hshift := orderData.choose_spec
    refine ⟨shift, fun s => ?_⟩
    let boundData := hshift s
    let D : ℝ := boundData.choose
    have hD : 0 < D := boundData.choose_spec.1
    have hb := boundData.choose_spec.2
    refine ⟨D, hD, ?_⟩
    intro i hi J z hz q hq n w hw hs v hl R hR hzR hvR hp hstate hspatial
    let Q := (G.negativePulledHeightJointTower 0 i hi).restrict hopen hsub
    exact (hb i hi J Q z hz q hq n w hw hs v hl R hR hzR hvR hp hstate hspatial).1
  · intro k hk
    let orderData := G.negativeInverse_jointPrefix_pair hadm hprefix k hk
    let shift : ℕ := orderData.choose
    have hshift := orderData.choose_spec
    refine ⟨shift, fun s => ?_⟩
    let boundData := hshift s
    let D : ℝ := boundData.choose
    have hD : 0 < D := boundData.choose_spec.1
    have hb := boundData.choose_spec.2
    refine ⟨D, hD, ?_⟩
    intro i hi Q z hz q hq n w hw hs v hl R hR hzR hvR hp hstate hspatial
    let J := (G.negativeInversePointJointTower 0 i hi).restrict hopen hsub
    exact (hb i hi J Q z hz q hq n w hw hs v hl R hR hzR hvR hp hstate hspatial).2

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_jointPrefixes_of_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_jointPrefixes_of_forward
