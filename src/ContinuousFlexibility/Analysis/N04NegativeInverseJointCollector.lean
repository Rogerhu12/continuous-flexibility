module

public import ContinuousFlexibility.Analysis.N04NegativeInverseJointPrefixes
public import ContinuousFlexibility.Analysis.N04NegativeInverseOutputAtoms
public import ContinuousFlexibility.Analysis.N04NegativeInverseReferenceBounds

/-!
# Collect genuine point and height joint estimates

The quantitative geometry argument has two outputs: the actual inverse
point and the actual pulled height. This file turns their positive
joint prefixes into all three current-data fields on the same fixed
neighborhood. Fixed physical normalization costs are absorbed only in
the polynomial E0 coefficient.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

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

/-- Fixed affine normalization changes only the coefficient envelope. -/
private theorem n04NegativeInverse_atom_coefficient_pack
    {E C B D I : ℝ} (hE : 1 ≤ E) (hC : 0 < C) (hB : 0 < B)
    (hinv : I ≤ C * E ^ C)
    (hpack : ((1 + C) * B) * E ^ (C + B) ≤ D * E ^ D) :
    (1 + I) * (B * E ^ B) ≤ D * E ^ D := by
  have hCp : 1 ≤ E ^ C := Real.one_le_rpow hE hC.le
  calc
    _ ≤ ((1 + C) * E ^ C) * (B * E ^ B) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hinv])
        (mul_nonneg hB.le (Real.rpow_nonneg (zero_le_one.trans hE) _))
    _ = ((1 + C) * B) * E ^ (C + B) := by
      rw [Real.rpow_add (zero_lt_one.trans_le hE)]
      ring
    _ ≤ _ := hpack

/-- Transfer a scalar normalization bound without unfolding its jet. -/
private theorem n04NegativeInverse_scaled_product_bound
    {X Y a M N H W : ℝ} (ha : 0 ≤ a) (hH : 0 ≤ H) (hW : 0 ≤ W)
    (hA : X ≤ a * Y) (hP : Y ≤ M * H * W) (hcoef : a * M ≤ N) :
    X ≤ N * H * W := by
  calc
    _ ≤ a * Y := hA
    _ ≤ a * (M * H * W) := mul_le_mul_of_nonneg_left hP ha
    _ = (a * M) * H * W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef hH) hW

/-- Transfer a positive joint prefix before instantiating an atlas or a
constructed inverse tower.  The coefficient witness stays independent
of the piece, point, and direction tuple. -/
private theorem n04NegativeInverse_jointPrefixes_of_scalar_bound
    {S : PhysicalSpacesData} {T : MaterialData} {cell : ℕ → ℕ}
    {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
    {f : Parameter S → ℕ → PolarPoint → PolarPoint}
    {g : Parameter S → ℕ → PolarPoint → ℝ}
    {I : ℕ → ℝ} {C : ℝ}
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hH : ∀ m, 0 ≤ T.H (T.sample (cell m)))
    (hC : 0 < C) (hI : ∀ m, 0 ≤ I m)
    (hinv : ∀ m, I m ≤ C * T.E0 (T.sample (cell m)) ^ C)
    (J : ∀ m, P m → SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
      (fun x : Parameter S × PolarPoint => f x.1 m x.2))
    (hbound : ∀ m (hm : P m),
      ∀ JP : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
        (fun x : Parameter S × PolarPoint => f x.1 m x.2),
      ∀ Q : SmoothDirections (sectorNeighborhood S base ε ε ×ˢ unitStrip)
        (fun x : Parameter S × PolarPoint => g x.1 m x.2),
      ∀ z ∈ sectorNeighborhood S base ε ε, ∀ q ∈ unitStrip,
      ∀ n : ℕ, ∀ w : StateAngleWord n, 0 < w.stateArity →
      ∀ v : Fin n → Parameter S × PolarPoint,
      (∀ i, w.isState i = true → (v i).2 = 0) →
        |Q.D n (z, q) v| ≤ (1 + I m) * ‖JP.D n (z, q) v‖)
    (hpoint : N04NegativeInverseJointPrefixes S T cell P base ε f) :
    N04NegativeInverseJointPrefixes S T cell P base ε g := by
  intro k hk
  have orderData := hpoint k hk
  let shift : ℕ := orderData.choose
  have hshift := orderData.choose_spec
  refine ⟨shift, fun s => ?_⟩
  have boundData := hshift s
  let B : ℝ := boundData.choose
  have hB : 0 < B := boundData.choose_spec.1
  have hb := boundData.choose_spec.2
  have packed := coefficientEnvelope_pack ((1 + C) * B) (C + B)
  let D : ℝ := packed.choose
  have hD : 0 < D := packed.choose_spec.1
  have hpack := packed.choose_spec.2
  refine ⟨D, hD, ?_⟩
  intro m hm Q z hz q hq n w hw hs v hv R hR hzR hvR hp hstate hspatial
  have hP := hb m hm (J m hm) z hz q hq n w hw hs v hv R hR hzR hvR hp hstate hspatial
  have hA := hbound m hm (J m hm) Q z hz q hq n w (hw.symm ▸ hk) v hspatial
  let E : ℝ := T.E0 (T.sample (cell m))
  let H : ℝ := T.H (T.sample (cell m)) ^ (3 / 4 : ℝ)
  let W : ℝ := R ^ (((w.angleArity + shift * k - 1 : ℕ) : ℝ) /
    (((s + shift * k : ℕ) : ℝ) + 1))
  have hheight : 0 ≤ H := Real.rpow_nonneg (hH m) _
  have hW : 0 ≤ W := Real.rpow_nonneg (zero_le_one.trans hR) _
  have hcoef : (1 + I m) * (B * E ^ B) ≤ D * E ^ D :=
    n04NegativeInverse_atom_coefficient_pack (hE m) hC hB (hinv m) (hpack E (hE m))
  have hraw : |Q.D n (z, q) v| ≤ D * E ^ D * H * W :=
    n04NegativeInverse_scaled_product_bound
      (add_nonneg zero_le_one (hI m)) hheight hW hA hP hcoef
  exact (Real.norm_eq_abs _).trans_le hraw

namespace N04RealizationGauge

variable (G : N04RealizationGauge)

/-- Restrict the actual point tower before using it in a quantitative
interface. Its construction does not enter the coefficient transfer. -/
private def negativeInverse_pointTower_on
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε) (m : ℕ) (hm : G.Neg 0 m) :
    SmoothDirections (sectorNeighborhood (G.S 0) b ε ε ×ˢ unitStrip)
      (fun x : Parameter (G.S 0) × PolarPoint =>
        G.pulledPoint 0 (G.lift 0 x.1) m x.2) := by
  have hU : IsOpen (sectorNeighborhood G.W.S b ε ε) :=
    sectorNeighborhood_isOpen G.W.S b ε ε
  have hΩ : IsOpen unitStrip := isOpen_Ioo.prod isOpen_univ
  have hsub : sectorNeighborhood G.W.S b ε ε ⊆
      sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε :=
    sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1
  exact (G.negativeInversePointJointTower 0 m hm).restrict (hU.prod hΩ)
    (fun x hx => ⟨hsub hx.1, hx.2⟩)

/-- Extract only the inverse length cost needed by affine output
normalization. The remaining length witnesses are kept out of its jet proof. -/
private theorem negativeInverse_inverseLength_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹| ≤
        C * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ C := by
  let data := G.negativeInverse_length_values
  let C : ℝ := data.choose
  have hC : 0 < C := data.choose_spec.1
  refine ⟨C, hC, ?_⟩
  intro m
  have hlength : 0 < (G.V 0).physicalRight m - (G.V 0).physicalLeft m :=
    (data.choose_spec.2 0 m).1
  have hbound : ((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹ ≤
      C * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ C :=
    (data.choose_spec.2 0 m).2.2.2.1
  exact (abs_of_pos (inv_pos.mpr hlength)).trans_le hbound

/-- Instantiate the coordinate bound with abstract source and target
towers, before either is selected from the actual geometry. -/
private theorem negativeInverse_atom_bound_on
    {b : ℕ} {ε : ℝ} (a : Atom) (ha : atomIsNegativeInverse a) (m : ℕ)
    (JP : SmoothDirections (sectorNeighborhood (G.S 0) b ε ε ×ˢ unitStrip)
      (fun x : Parameter (G.S 0) × PolarPoint =>
        G.pulledPoint 0 (G.lift 0 x.1) m x.2))
    (Q : SmoothDirections (sectorNeighborhood (G.S 0) b ε ε ×ˢ unitStrip)
      (fun x : Parameter (G.S 0) × PolarPoint => G.atomFamily 0 a x.1 m x.2))
    {n : ℕ} (w : StateAngleWord n) (hk : 0 < w.stateArity)
    (z : Parameter (G.S 0)) (hz : z ∈ sectorNeighborhood (G.S 0) b ε ε)
    (q : PolarPoint) (hq : q ∈ unitStrip)
    (v : Fin n → Parameter (G.S 0) × PolarPoint)
    (hv : ∀ i, w.isState i = true → (v i).2 = 0) :
    |Q.D n (z, q) v| ≤
      (1 + |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|) *
        ‖JP.D n (z, q) v‖ := by
  exact G.negativeInverseAtom_positiveJoint_bound 0
    (U := sectorNeighborhood (G.S 0) b ε ε ×ˢ unitStrip)
    m JP a ha Q w hk (x := (z, q)) ⟨hz, hq⟩ v hv

/-- The concrete atlas enters the generic transfer only through a
given coefficient and a given tower family. -/
private theorem negativeInverse_atom_jointPrefixes_with_coefficients
    {b : ℕ} {ε : ℝ} (C : ℝ) (hC : 0 < C)
    (hinv : ∀ m : ℕ,
      |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹| ≤
        C * G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) ^ C)
    (J : ∀ m, G.Neg 0 m →
      SmoothDirections (sectorNeighborhood (G.S 0) b ε ε ×ˢ unitStrip)
        (fun x : Parameter (G.S 0) × PolarPoint =>
          G.pulledPoint 0 (G.lift 0 x.1) m x.2))
    (hpoint : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (fun z m q => G.pulledPoint 0 (G.lift 0 z) m q))
    (a : Atom) (ha : atomIsNegativeInverse a) :
    N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (G.atomFamily 0 a) := by
  have hE : ∀ m, 1 ≤ G.W.U.E0 (G.W.U.sample ((G.V 0).cell m)) :=
    (G.cost_nonneg 0).2.2
  have hH : ∀ m, 0 ≤ G.W.U.H (G.W.U.sample ((G.V 0).cell m)) :=
    (G.cost_nonneg 0).2.1
  exact n04NegativeInverse_jointPrefixes_of_scalar_bound
    (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell) (P := G.Neg 0)
    (base := b) (ε := ε) (C := C)
    (f := fun z m q => G.pulledPoint 0 (G.lift 0 z) m q)
    (g := G.atomFamily 0 a)
    (I := fun m => |((G.V 0).physicalRight m - (G.V 0).physicalLeft m)⁻¹|)
    hE hH hC (fun _ => abs_nonneg _) hinv J
    (fun m _ JP Q z hz q hq n w hk v hv =>
      G.negativeInverse_atom_bound_on (b := b) (ε := ε) a ha m JP Q
        (n := n) w hk z hz q hq v hv)
    hpoint

theorem negativeInverse_atom_jointPrefixes
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (hpoint : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (fun z m q => G.pulledPoint 0 (G.lift 0 z) m q))
    (a : Atom) (ha : atomIsNegativeInverse a) :
    N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (G.atomFamily 0 a) := by
  let data := G.negativeInverse_inverseLength_envelope
  exact G.negativeInverse_atom_jointPrefixes_with_coefficients
    (b := b) (ε := ε) data.choose data.choose_spec.1 data.choose_spec.2
    (fun m hm => G.negativeInverse_pointTower_on hadm m hm) hpoint a ha

/-- The point and pulled-height joint estimates close exactly the
inverse subnode's conclusion on the supplied common neighborhood. -/
theorem negativeInverse_collect_joint
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε) (hsmall : ε ≤ 1 / 2)
    (hpoint : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (fun z m q => G.pulledPoint 0 (G.lift 0 z) m q))
    (hheight : N04NegativeInverseJointPrefixes (G.S 0) G.W.U (G.V 0).cell (G.Neg 0) b ε
      (G.pulledHeight 0)) :
    ∀ η, G.NegativeAtomData η atomIsNegativeInverse b ε ∧
      G.Data η (G.Neg η) b ε (G.pulledHeight η) (G.pulledHeightRef η) := by
  apply G.negativeInverse_collect hadm hsmall
  · intro a ha
    apply n04NegativeInverse_rawPrefixes_of_joint
      (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell) (P := G.Neg 0)
      (base := b) (ε := ε) (f := G.atomFamily 0 a)
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativeInverseAtomJointTower 0 m hm a ha).restrict
        ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
        (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩))
    exact G.negativeInverse_atom_jointPrefixes hadm hpoint a ha
  · apply n04NegativeInverse_rawPrefixes_of_joint
      (S := G.S 0) (T := G.W.U) (cell := (G.V 0).cell) (P := G.Neg 0)
      (base := b) (ε := ε) (f := G.pulledHeight 0)
      (G.cost_nonneg 0).2.2 (G.cost_nonneg 0).2.1
      (fun m hm => (G.negativePulledHeightJointTower 0 m hm).restrict
        ((sectorNeighborhood_isOpen G.W.S b ε ε).prod (isOpen_Ioo.prod isOpen_univ))
        (fun x hx => ⟨sectorNeighborhood_mono G.W.S hadm.1 hadm.2.2.1 hadm.2.2.1 hx.1, hx.2⟩))
    exact hheight

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_collect_joint
