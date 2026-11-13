import ContinuousFlexibility.Analysis.N04NegativeInverseCrossing
import ContinuousFlexibility.Analysis.N04NegativeInverseGaugePrefix
import ContinuousFlexibility.Analysis.N04NegativeInverseVectorBounds

/-!
# Actual forward prefixes at the actual inverse point

The inverse point lies in the whole physical component and its current
normalized radial coordinate is exactly the original unit coordinate.
The moving-half scalar estimate therefore applies there. The remaining
costs are fixed affine normalizations and the actual Jacobian reciprocal.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

namespace N04NegativeInverseJet.UnitPrefix

variable {X Y : Type*}
  [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set (X × PolarPoint)} {f : X × PolarPoint → Y}
  {J : SmoothDirections U f} {p : X × PolarPoint}
  {low high : Seminorm ℝ X} {N K shift : ℕ} {C D H R t : ℝ}

theorem coefficient_mono
    (h : N04NegativeInverseJet.UnitPrefix J p low high N K shift C H R t)
    (hCD : C ≤ D) (hH : 0 ≤ H) (ht : 0 ≤ t) :
    N04NegativeInverseJet.UnitPrefix J p low high N K shift D H R t := by
  intro n hn hnN w hw b y hl hh hy
  exact (h n hn hnN w hw b y hl hh hy).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (parameterHeightWeight_nonneg hH _))
      (pow_nonneg ht _))

theorem of_pure (hR : 0 ≤ R)
    (hb : ∀ n : ℕ, 0 < n → n ≤ N → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → X × PolarPoint,
      (∀ i, low (v i).1 ≤ 1) → (∀ i, high (v i).1 ≤ R) →
      (∀ i, ‖(v i).2‖ ≤ 1) →
      (∀ i, w.isState i = false → (v i).1 = 0) →
      (∀ i, w.isState i = true → (v i).2 = 0) →
      ‖J.D n p v‖ ≤ C * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1)) :
    N04NegativeInverseJet.UnitPrefix J p low high N K shift C H R t := by
  intro n hn hnN w hw b y hl hh hy
  apply hb n hn hnN w hw
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · simpa only [map_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
    · exact hl i
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · simpa only [map_zero] using hR
    · exact hh i
  · intro i
    cases hi : w.isState i <;> simp only [hi, Bool.false_eq_true, if_false, if_true]
    · exact hy i
    · simp only [norm_zero, zero_le_one]
  · intro i hi
    simp only [hi, Bool.false_eq_true, if_false]
  · intro i hi
    simp only [hi, if_true]

end N04NegativeInverseJet.UnitPrefix

/-- Normalize a fixed affine interval before instantiating its endpoints. -/
private theorem n04NegativeInverse_normalized_affine_first
    (left span q : ℝ) (hspan : span ≠ 0) :
    (left + span * q - left) / span = q := by
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hspan]

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

theorem negativeInverse_pulledPoint_in_currentHalf
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    {z : Parameter G.W.S} (hz : z ∈ sectorNeighborhood G.W.S b ε ε)
    {q : PolarPoint} (hq : q ∈ unitStrip) :
    G.pulledPoint 0 (G.lift 0 z) k q ∈ G.negativeInverseComponent m ∧
      G.negativeInversePhysicalAtomFamily 0 .chartRadial z k
        (G.pulledPoint 0 (G.lift 0 z) k q) ∈ Ioo (0 : ℝ) 1 := by
  have hx : (z, canonicalUnitPoint (G.V 0) k q) ∈
      sectorNeighborhood G.W.S b ε ε ×ˢ G.negativeInverseTarget m :=
    ⟨hz, G.negativeInverseUnit_maps 0 k m side hi hq⟩
  have hp := G.negativeInverseCanonical_maps 0 hadm k m side hi hx
  have he := G.negativeInverseCanonical_right 0 hadm k m side hi hx
  change (G.V 0).chart (G.lift 0 z) k (G.pulledPoint 0 (G.lift 0 z) k q) =
    canonicalUnitPoint (G.V 0) k q at he
  have hr : G.negativeInversePhysicalAtomFamily 0 .chartRadial z k
      (G.pulledPoint 0 (G.lift 0 z) k q) = q.1 := by
    have lengths := G.negativeInverse_length_values
    have hl := lengths.choose_spec.2
    exact (G.negativeInverse_physical_chartRadial 0 z k _).trans
      ((congrArg (fun p : PolarPoint => (p.1 - (G.V 0).left k) /
        ((G.V 0).right k - (G.V 0).left k)) he).trans
          (n04NegativeInverse_normalized_affine_first _ _ _ (hl 0 k).2.1.ne'))
  exact ⟨hp, (congrArg (fun r : ℝ => r ∈ Ioo (0 : ℝ) 1) hr).mpr hq.1⟩

/-- The three current scalar fields supply all actual forward inputs
on a common neighborhood chosen before every derivative order. -/
theorem negativeInverse_forwardPrefixes
    {b : ℕ} {ε : ℝ} (hadm : G.Admissible b ε)
    (hc : G.NegativeAtomData 0 atomIsNegativeChart b ε)
    (hh : G.NegativeAtomData 0 atomIsNegativeHeight b ε) :
    ∃ low : ℕ, ∃ ε' : ℝ, b ≤ low ∧ ∃ hadm' : G.Admissible low ε',
      ε' ≤ ε ∧ ε' ≤ 1 / 2 ∧ G.NegativeInverseForwardPrefixes hadm' := by
  let jacData := G.negativeInverse_inverseJacobian_bound hadm (hc .jacobianInverse trivial)
  let base : ℕ := jacData.choose
  let radius : ℝ := jacData.choose_spec.choose
  let I : ℝ := jacData.choose_spec.choose_spec.choose
  let jacSpec := jacData.choose_spec.choose_spec.choose_spec
  have hb : b ≤ base := jacSpec.1
  have hradius : 0 < radius := jacSpec.2.1
  have hradiusε : radius ≤ ε := jacSpec.2.2.1
  have hI : 0 < I := jacSpec.2.2.2.1
  have hJac := jacSpec.2.2.2.2
  have hadm₀ : G.Admissible base radius := G.admissible_mono hadm hb hradius hradiusε
  have hc₀ := G.negativeAtomData_mono 0 hc hb hradiusε
  have hh₀ := G.negativeAtomData_mono 0 hh hb hradiusε
  let scalarData := G.negativeInverse_componentScalars_purePrefix hadm₀ hc₀ hh₀
  let low : ℕ := scalarData.choose
  let ε' : ℝ := scalarData.choose_spec.choose
  let scalarSpec := scalarData.choose_spec.choose_spec
  have hbase : base ≤ low := scalarSpec.1
  have hadm' : G.Admissible low ε' := scalarSpec.2.1
  have hε' : ε' ≤ radius := scalarSpec.2.2.1
  have hhalf : ε' ≤ 1 / 2 := scalarSpec.2.2.2.1
  have hprefix := scalarSpec.2.2.2.2
  have lengths := G.negativeInverse_length_values
  let L : ℝ := lengths.choose
  have hL : 0 < L := lengths.choose_spec.1
  have hlength := lengths.choose_spec.2
  refine ⟨low, ε', hb.trans hbase, hadm', hε'.trans hradiusε, hhalf, ?_⟩
  intro K
  let prefixData := hprefix K
  let shift : ℕ := prefixData.choose
  have hshift : 1 ≤ shift := prefixData.choose_spec.1
  have horder := prefixData.choose_spec.2
  refine ⟨shift, hshift, fun N => ?_⟩
  let order := horder N
  let C : ℝ := order.choose
  have hC : 0 < C := order.choose_spec.1
  have hscalar := order.choose_spec.2
  let commonData := n04NegativeInverse_common_coefficient hC hI hL
  let B : ℝ := commonData.choose
  have hB : 1 ≤ B := commonData.choose_spec.1
  have hcommon := commonData.choose_spec.2
  refine ⟨B, hB, ?_⟩
  intro k m side hi z hz q hq R hR hzR
  let E : ℝ := G.W.U.E0 (G.W.U.sample ((G.V 0).cell k))
  let H : ℝ := G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ)
  let t : ℝ := R ^ (1 / (((N + shift * K : ℕ) : ℝ) + 1))
  let p : PolarPoint := G.pulledPoint 0 (G.lift 0 z) k q
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 k
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 k) _
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hC0 : 0 ≤ C * E ^ C := mul_nonneg hC.le
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hpower (d : ℕ) : t ^ d =
      R ^ ((d : ℝ) / (((N + shift * K : ℕ) : ℝ) + 1)) :=
    n04NegativeInverse_commonScale_pow (zero_le_one.trans hR) d (N + shift * K)
  have currentHalf := G.negativeInverse_pulledPoint_in_currentHalf hadm' k m side hi hz hq
  have hp := currentHalf.1
  have htarget := currentHalf.2
  have hraw (a : Fin 3)
      (Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
        (fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 (n04NegativeInverseScalarAtom a) x.1 k x.2)) :
      N04NegativeInverseJet.UnitPrefix Q (z, p)
        (parameterGrading G.W.S low) (parameterGrading G.W.S (low + N + shift * K + 1))
        N K shift (C * E ^ C) H R t := by
    apply N04NegativeInverseJet.UnitPrefix.of_pure
      (X := Parameter G.W.S) (Y := ℝ)
      (U := sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (f := fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily 0 (n04NegativeInverseScalarAtom a) x.1 k x.2)
      (J := Q) (p := (z, p)) (low := parameterGrading G.W.S low)
      (high := parameterGrading G.W.S (low + N + shift * K + 1))
      (N := N) (K := K) (shift := shift) (C := C * E ^ C)
      (H := H) (R := R) (t := t) (zero_le_one.trans hR)
    intro n hn hnN w hw v vl vh vp vs va
    have hwN : w.angleArity ≤ N := by have hs := w.arity_sum; omega
    have hbound : ‖Q.D n (z, p) v‖ ≤ C * E ^ C *
        parameterHeightWeight H w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
            (((N + shift * K : ℕ) : ℝ) + 1)) :=
      hscalar a k m side hi Q z hz p hp htarget n hn w hw hwN v vl R hR hzR
        vh vp vs va
    exact hbound.trans_eq
      (congrArg (fun r : ℝ => C * E ^ C * parameterHeightWeight H w.stateArity * r)
        (hpower (w.angleArity + shift * w.stateArity - 1))).symm
  let J : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint => (G.V 0).chart (G.lift 0 x.1) k x.2) :=
    G.negativeInverseForwardOn 0 hadm' k m side hi
  let JH : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint => (G.V 0).height (G.lift 0 x.1) k x.2) :=
    G.negativeInverseHeightOn 0 hadm' k m side hi
  let JR : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily 0 .chartRadial x.1 k x.2) :=
    G.negativeInverse_componentAtomJointTowerOn hadm' k m side hi .chartRadial trivial
  let JA : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily 0 .chartAngleDefect x.1 k x.2) :=
    G.negativeInverse_componentAtomJointTowerOn hadm' k m side hi .chartAngleDefect trivial
  let C₀ : ℝ := 1 + C * E ^ C
  have hC₀ : 1 ≤ C₀ := le_add_of_nonneg_right hC0
  have hRraw : N04NegativeInverseJet.UnitPrefix JR (z, p)
      (parameterGrading G.W.S low) (parameterGrading G.W.S (low + N + shift * K + 1))
      N K shift C₀ H R t :=
    (hraw 0 JR).coefficient_mono
      (le_add_of_nonneg_left zero_le_one) hH (zero_le_one.trans ht)
  have hAraw : N04NegativeInverseJet.UnitPrefix JA (z, p)
      (parameterGrading G.W.S low) (parameterGrading G.W.S (low + N + shift * K + 1))
      N K shift C₀ H R t :=
    (hraw 1 JA).coefficient_mono
      (le_add_of_nonneg_left zero_le_one) hH (zero_le_one.trans ht)
  have hspan : |(G.V 0).right k - (G.V 0).left k| ≤ L * E ^ L :=
    (abs_of_pos (hlength 0 k).2.1).trans_le (hlength 0 k).2.2.2.2.1
  have hcoef : (2 + |(G.V 0).right k - (G.V 0).left k|) * C₀ ≤ B * E ^ B :=
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hspan)
      (zero_le_one.trans hC₀)).trans (hcommon E hE).1
  have hforward : N04NegativeInverseJet.UnitPrefix J (z, p)
      (parameterGrading G.W.S low) (parameterGrading G.W.S (low + N + shift * K + 1))
      N K shift (B * E ^ B) H R t := by
    apply N04NegativeInverseJet.UnitPrefix.of_pure
      (X := Parameter G.W.S) (Y := PolarPoint)
      (U := sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
      (f := fun x : Parameter G.W.S × PolarPoint => (G.V 0).chart (G.lift 0 x.1) k x.2)
      (J := J) (p := (z, p)) (low := parameterGrading G.W.S low)
      (high := parameterGrading G.W.S (low + N + shift * K + 1))
      (N := N) (K := K) (shift := shift) (C := B * E ^ B)
      (H := H) (R := R) (t := t) (zero_le_one.trans hR)
    intro n hn hnN w hw v vl vh vp vs va
    have hr : ‖JR.D n (z, p) v‖ ≤ C₀ * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) :=
      hRraw.norm_le n hn hnN w hw v vl vh vp vs va
    have ha : ‖JA.D n (z, p) v‖ ≤ C₀ * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity - 1) :=
      hAraw.norm_le n hn hnN w hw v vl vh vp vs va
    have hv : ‖J.D n (z, p) v‖ ≤
        (2 + |(G.V 0).right k - (G.V 0).left k|) * C₀ *
          parameterHeightWeight H w.stateArity *
            t ^ (w.angleArity + shift * w.stateArity - 1) :=
      G.negativeInverse_vector_forward_bound 0 k
        (U := sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
        J JR JA (n := n) hn w shift (x := (z, p)) ⟨hz, hp⟩ v vp va
        (C := C₀) (H := H) (t := t) hC₀ hH ht
        ((Real.norm_eq_abs _).symm.trans_le hr) ((Real.norm_eq_abs _).symm.trans_le ha)
    exact n04NegativeInverse_prefix_mono hcoef
      (parameterHeightWeight_nonneg hH _)
      (pow_nonneg (zero_le_one.trans ht) _) hv
  have hheight : N04NegativeInverseJet.UnitPrefix JH (z, p)
      (parameterGrading G.W.S low) (parameterGrading G.W.S (low + N + shift * K + 1))
      N K shift (B * E ^ B) H R t := by
    let Q : SmoothDirections (sectorNeighborhood G.W.S low ε' ε' ×ˢ G.negativeInverseComponent m)
        (fun x : Parameter G.W.S × PolarPoint =>
          G.negativeInversePhysicalAtomFamily 0 .height x.1 k x.2) :=
      JH.congrOn (fun x _ => (G.negativeInverse_physical_height 0 x.1 k x.2).symm)
    exact (hraw 2 Q).coefficient_mono (hcommon E hE).2.2.2 hH (zero_le_one.trans ht)
  have hzbase : z ∈ sectorNeighborhood G.W.S base radius radius :=
    sectorNeighborhood_mono G.W.S hbase hε' hε' hz
  have hk : G.Neg 0 k := (G.neg_iff_inl 0 k).mpr ⟨(m, side), hi⟩
  have hjac : |planeJacobian ((G.V 0).chart (G.lift 0 z) k) p|⁻¹ ≤ B * E ^ B :=
    (hJac 0 z hzbase k hk q hq).trans (hcommon E hE).2.1
  have hlinear : ‖G.negativeInverseCanonicalLinear 0 k‖ ≤ B * E ^ B :=
    (G.negativeInverseCanonicalLinear_norm 0 k).trans
      ((add_le_add le_rfl hspan).trans (hcommon E hE).2.2.1)
  exact ⟨hforward, hheight, hjac, hlinear⟩

end N04RealizationGauge
end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_forwardPrefixes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_forwardPrefixes
