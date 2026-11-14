module

public import ContinuousFlexibility.Analysis.N04NegativeInverseNormalizedPair
public import ContinuousFlexibility.Analysis.N04NegativeInverseActualSystem
public import ContinuousFlexibility.Analysis.N04NegativeInverseCoefficientBounds
public import ContinuousFlexibility.Analysis.N04NegativeInverseJointPrefixes
public import ContinuousFlexibility.Analysis.N04NegativeInverseOutputAtoms

/-!
# Closing the inverse and pulled-height joint prefixes

The forward interface is expressed on the actual inverse image in the
original physical component. The common state neighborhood and its low
grading are fixed before the parameter and spatial orders are chosen.
-/

@[expose] public section

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
  let heightData := G.negativeInverse_height_uniform
  let L : ℝ := heightData.choose
  have hL : 1 ≤ L := heightData.choose_spec.1
  have hheight := heightData.choose_spec.2
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
  let coeffData := n04NegativeInverse_normalizedMajorants_envelope N hB hL
  let D : ℝ := coeffData.choose
  have hD : 1 ≤ D := coeffData.choose_spec.1
  have hcoeff := coeffData.choose_spec.2
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
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 i
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 i) _
  have hHL : H ≤ L := hheight i
  have hC : 1 ≤ C := n04NegativeInverse_envelope_one_le hB hE
  have hindex : base + N + shift * k + 1 = base + s + (shift + 1) * k + 1 := by
    dsimp only [N]
    simp only [Nat.add_mul, Nat.one_mul]
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
      (G.V 0).inverseChart (G.lift 0 z) i (c + A q) :=
    congrArg ((G.V 0).inverseChart (G.lift 0 z) i)
      (G.negativeInverseUnit_eq_affine 0 i q)
  have hmap : MapsTo (fun a => c + A a) unitStrip (G.negativeInverseTarget j.1) := by
    intro a ha
    exact (congrArg (fun p : PolarPoint => p ∈ G.negativeInverseTarget j.1)
      (G.negativeInverseUnit_eq_affine 0 i a)).mp
        (G.negativeInverseUnit_maps 0 i j.1 j.2 hi' ha)
  let J' : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint =>
        (G.V 0).inverseChart (G.lift 0 x.1) i (c + A x.2)) :=
    J.congrOn (fun x _ => congrArg ((G.V 0).inverseChart (G.lift 0 x.1) i)
      (G.negativeInverseUnit_eq_affine 0 i x.2))
  let Q' : SmoothDirections (sectorNeighborhood G.W.S base ε ε ×ˢ unitStrip)
      (fun x : Parameter G.W.S × PolarPoint =>
        (G.V 0).height (G.lift 0 x.1) i
          ((G.V 0).inverseChart (G.lift 0 x.1) i (c + A x.2))) :=
    Q.congrOn (fun x _ => congrArg (fun p : PolarPoint =>
      (G.V 0).height (G.lift 0 x.1) i ((G.V 0).inverseChart (G.lift 0 x.1) i p))
      (G.negativeInverseUnit_eq_affine 0 i x.2))
  have hfwd' : N04NegativeInverseJet.UnitPrefix JF
      (z, (G.V 0).inverseChart (G.lift 0 z) i (c + A q))
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t := by
    exact (congrArg (fun r : PolarPoint => N04NegativeInverseJet.UnitPrefix JF (z, r)
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t)
      hpull).mp hfwd
  have hscalar' : N04NegativeInverseJet.UnitPrefix JH
      (z, (G.V 0).inverseChart (G.lift 0 z) i (c + A q))
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t := by
    exact (congrArg (fun r : PolarPoint => N04NegativeInverseJet.UnitPrefix JH (z, r)
      (parameterGrading G.W.S base)
      (parameterGrading G.W.S (base + N + shift * k + 1)) N k shift C H R t)
      hpull).mp hscalar
  have hdet' : |planeJacobian ((G.V 0).chart (G.lift 0 z) i)
      ((G.V 0).inverseChart (G.lift 0 z) i (c + A q))|⁻¹ ≤ C := by
    exact (congrArg (fun r : PolarPoint =>
      |planeJacobian ((G.V 0).chart (G.lift 0 z) i) r|⁻¹ ≤ C) hpull).mp hdet
  have hmajorants := hcoeff E hE
  exact n04NegativeInverse_normalized_pair_bound (C := C) (Z := D * E ^ D) JF KG JH
    (sectorNeighborhood_isOpen G.W.S base ε ε)
    (isOpen_Ioo.prod isOpen_univ) (isOpen_Ioo.prod isOpen_univ)
    (isOpen_Ioo.prod isOpen_univ)
    (G.negativeInverseCanonical_maps 0 hadm i j.1 j.2 hi')
    (fun x hx => G.negativeInverseCanonical_jacobian_ne_zero 0 hadm i j.1 j.2 hi' hx)
    (fun x hx => G.negativeInverseCanonical_right 0 hadm i j.1 j.2 hi' hx)
    A c hmap QH J' Q' (parameterGrading G.W.S base)
    (parameterGrading G.W.S (base + N + shift * k + 1)) k s shift hk hshift hz hq
    hC (mul_nonneg (zero_le_one.trans hD) (Real.rpow_nonneg (zero_le_one.trans hE) _))
    hH hHL hL hR hmajorants.1 hmajorants.2 hdet' hlinear hfwd' hscalar'
    n w hw hs v hl hvR' hp hvstate hvspace

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
