import ContinuousFlexibility.Analysis.N04NegativeInverseForwardBounds
import ContinuousFlexibility.Analysis.N04NegativeInverseFamilyPurePrefix

/-!
# Undoing the fixed physical unit normalization

The affine substitution changes only physical directions.  Parameter
slots and their height factors are unchanged.  The inverse interval
length is charged once for each physical slot, before any transition
between the two old reference halves is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff BigOperators

section Affine

variable {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : PhysicalSpacesData} (K : CanonicalData S) (k : ℕ)
  {U : Set E} {Ω : Set PolarPoint} {f g : E × PolarPoint → F}

/-- Equality of the actual physical jet and the unit jet in inverse
affine directions, with no change to a parameter direction. -/
theorem n04NegativeInverse_physicalUnit_jet
    (hU : IsOpen U) (hlen : K.physicalLeft k < K.physicalRight k)
    (J : SmoothDirections (U ×ˢ Ω) f)
    (Q : SmoothDirections (U ×ˢ unitStrip) g)
    (hmap : MapsTo (physicalUnitPoint K k) unitStrip Ω)
    (heq : ∀ x ∈ U ×ˢ unitStrip, f (x.1, physicalUnitPoint K k x.2) = g x)
    {z : E} (hz : z ∈ U) {p : PolarPoint}
    (hp : p ∈ Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ (univ : Set ℝ))
    (n : ℕ) (v : Fin n → E × PolarPoint) :
    J.D n (z, p) v =
      Q.D n (z, n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k p)
        (fun i => ((v i).1,
          ((K.physicalRight k - K.physicalLeft k)⁻¹ * (v i).2.1, (v i).2.2))) := by
  let A : PolarPoint →L[ℝ] PolarPoint :=
    ((K.physicalRight k - K.physicalLeft k) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let L : (E × PolarPoint) →L[ℝ] E × PolarPoint :=
    (ContinuousLinearMap.fst ℝ E PolarPoint).prod
      (A.comp (ContinuousLinearMap.snd ℝ E PolarPoint))
  let c : E × PolarPoint := (0, (K.physicalLeft k, 0))
  have hpoint (x : E × PolarPoint) : c + L x = (x.1, physicalUnitPoint K k x.2) := by
    simp only [c, L, A, physicalUnitPoint, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul, Prod.mk_add_mk, zero_add]
  have hm : MapsTo (fun x : E × PolarPoint => c + L x) (U ×ˢ unitStrip) (U ×ˢ Ω) := by
    intro x hx
    rw [hpoint]
    exact ⟨hx.1, hmap hx.2⟩
  let Q' := (J.compAffine L c (hU.prod (isOpen_Ioo.prod isOpen_univ)) hm).congrOn
    (fun x hx => by rw [hpoint]; exact heq x hx)
  let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k p
  have hq : q ∈ unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData K) hlen hp
  have hpq : physicalUnitPoint K k q = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K) hlen p
  let v' : Fin n → E × PolarPoint := fun i => ((v i).1,
    ((K.physicalRight k - K.physicalLeft k)⁻¹ * (v i).2.1, (v i).2.2))
  have hdir : (fun i => L (v' i)) = v := by
    funext i
    apply Prod.ext
    · simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', v']
    · apply Prod.ext
      · simp only [L, A, v', ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hlen).ne', one_mul]
      · simp only [L, A, v', ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  have h := congrArg (fun B : (E × PolarPoint) [×n]→L[ℝ] F => B v')
    (Q.unique Q' n (z, q) ⟨hz, hq⟩)
  change Q.D n (z, q) v' =
    (J.compAffine L c (hU.prod (isOpen_Ioo.prod isOpen_univ)) hm).D n (z, q) v' at h
  rw [SmoothDirections.compAffine_apply, hpoint, hpq, hdir] at h
  exact h.symm

/-- Unit physical directions on the original interval acquire only the
fixed inverse-length cost. -/
theorem n04NegativeInverse_physicalUnit_norm_bound
    (hU : IsOpen U) (hlen : K.physicalLeft k < K.physicalRight k)
    (J : SmoothDirections (U ×ˢ Ω) f)
    (Q : SmoothDirections (U ×ˢ unitStrip) g)
    (hmap : MapsTo (physicalUnitPoint K k) unitStrip Ω)
    (heq : ∀ x ∈ U ×ˢ unitStrip, f (x.1, physicalUnitPoint K k x.2) = g x)
    {z : E} (hz : z ∈ U) {p : PolarPoint}
    (hp : p ∈ Ioo (K.physicalLeft k) (K.physicalRight k) ×ˢ (univ : Set ℝ))
    {n : ℕ} (w : StateAngleWord n) (v : Fin n → E × PolarPoint)
    (hphysical : ∀ i, ‖(v i).2‖ ≤ 1)
    (hstate : ∀ i, w.isState i = false → (v i).1 = 0)
    (hspatial : ∀ i, w.isState i = true → (v i).2 = 0)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hlength : (K.physicalRight k - K.physicalLeft k)⁻¹ ≤ M)
    (hunit : ∀ y : Fin n → PolarPoint, (∀ i, ‖y i‖ ≤ 1) →
      ‖Q.D n (z, n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k p)
        (fun i => if w.isState i then ((v i).1, 0) else (0, y i))‖ ≤ C) :
    ‖J.D n (z, p) v‖ ≤ C * M ^ w.angleArity := by
  let y : Fin n → PolarPoint := fun i =>
    ((K.physicalRight k - K.physicalLeft k)⁻¹ * (v i).2.1, (v i).2.2)
  have hy (i : Fin n) : ‖y i‖ ≤ M := by
    dsimp only [y]
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (inv_pos.mpr (sub_pos.mpr hlen))]
      have hv : |(v i).2.1| ≤ 1 :=
        (show |(v i).2.1| ≤ ‖(v i).2‖ by
          simpa only [Real.norm_eq_abs] using norm_fst_le (v i).2).trans (hphysical i)
      exact (mul_le_mul hlength hv (abs_nonneg _) (zero_le_one.trans hM)).trans_eq (mul_one M)
    · exact ((norm_snd_le (v i).2).trans (hphysical i)).trans hM
  have he : (fun i => ((v i).1, y i)) =
      fun i => if w.isState i then ((v i).1, (0 : PolarPoint)) else (0, y i) := by
    funext i
    cases hi : w.isState i with
    | true =>
        simp only [hi, if_true]
        have hv := hspatial i hi
        simp only [y, hv, Prod.fst_zero, Prod.snd_zero, mul_zero, Prod.mk_zero_zero]
    | false => simp only [hi, Bool.false_eq_true, if_false, hstate i hi]
  rw [n04NegativeInverse_physicalUnit_jet K k hU hlen J Q hmap heq hz hp n v]
  change ‖Q.D n _ (fun i => ((v i).1, y i))‖ ≤ _
  rw [he]
  have hh := n04NegativeInverse_pureSpatial_homogeneous w
    (Q.D n (z, n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k p))
    (fun i => (v i).1) hunit y
  have hprod : w.selectedProduct (fun i => ‖y i‖) ≤ M ^ w.angleArity := by
    simpa only [w.selectedProduct_const] using
      w.selectedProduct_mono (fun i => norm_nonneg (y i)) hy
  exact hh.trans (mul_le_mul_of_nonneg_left hprod hC)

end Affine

/-- Genuine jets are continuous through the fixed reference cut, so a
uniform bound on the open half also holds on its closed half. -/
theorem n04NegativeInverse_jet_bound_on_closedHalf
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {Ω : Set PolarPoint} {f : E × PolarPoint → F}
    (J : SmoothDirections (U ×ˢ Ω) f)
    {z : E} (hz : z ∈ U) {p : PolarPoint} (hp : p ∈ Ω)
    {a b M : ℝ} (hab : a < b) (hhalf : p ∈ Icc a b ×ˢ (univ : Set ℝ))
    (n : ℕ) (v : Fin n → E × PolarPoint)
    (hb : ∀ q ∈ Ioo a b ×ˢ (univ : Set ℝ), ‖J.D n (z, q) v‖ ≤ M) :
    ‖J.D n (z, p) v‖ ≤ M := by
  apply n04NegativeInverse_le_on_closedHalf hab hhalf
  · have hc := (J.continuous n).continuousAt
      ((J.open_domain.prod isOpen_univ).mem_nhds
        (show ((z, p), v) ∈ (U ×ˢ Ω) ×ˢ univ from ⟨⟨hz, hp⟩, mem_univ _⟩))
    exact (hc.comp ((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const)).norm
  · exact hb

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

/-- The actual atom as a function of the unscaled physical point. -/
def negativeInversePhysicalAtomFamily
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom)
    (z : Parameter G.W.S) (k : ℕ) (p : PolarPoint) : ℝ :=
  G.atomFamily η a z k
    (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V η)) k p)

theorem negativeInverse_physicalAtom_on_unit
    (η : (G.W.S.height (3 / 4 : ℝ)).Space) (a : Atom)
    (z : Parameter G.W.S) (k : ℕ) (q : PolarPoint) :
    G.negativeInversePhysicalAtomFamily η a z k (physicalUnitPoint (G.V η) k q) =
      G.atomFamily η a z k q := by
  obtain ⟨B, hB, hl⟩ := G.negativeInverse_length_values
  apply congrArg (G.atomFamily η a z k)
  apply Prod.ext
  · change ((G.V η).physicalLeft k +
      ((G.V η).physicalRight k - (G.V η).physicalLeft k) * q.1 -
      (G.V η).physicalLeft k) /
        ((G.V η).physicalRight k - (G.V η).physicalLeft k) = q.1
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (hl η k).1.ne']
  · rfl

theorem negativeInverse_physicalUnit_maps
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side)) :
    MapsTo (physicalUnitPoint (G.V η) k) unitStrip
      (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)) := by
  obtain ⟨B, hB, hl⟩ := G.negativeInverse_length_values
  have hf := G.negativeInverse_actual_fields η 0 k m side hi
  intro q hq
  have hp := (n04NegativeGeometry_affine_unitPoint
    ((G.V η).physicalLeft k) ((G.V η).physicalRight k)
    (sub_pos.mp (hl η k).1)).2.1 hq
  change physicalUnitPoint (G.V η) k q ∈
    Ioo ((G.V η).physicalLeft k) ((G.V η).physicalRight k) ×ˢ (univ : Set ℝ) at hp
  rw [hf.2.2.1, hf.2.2.2.1] at hp
  exact ⟨n04b_negativeHalf_subset (n04bActualReferenceCut_mem G.W.through03)
    (m, side) hp.1, mem_univ _⟩

/-- Every physical atom is represented by its genuine actual tower on
the whole original component, including the old optical cut. -/
def negativeInverse_componentAtomJointTower
    (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    (k m : ℕ) (side : Bool) (hi : G.e k = .inl (m, side))
    (a : Atom) (ha : negativePhysicalGeometryAtom a) :
    SmoothDirections
      (sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε ×ˢ
        (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
      (fun x : Parameter G.W.S × PolarPoint =>
        G.negativeInversePhysicalAtomFamily η a x.1 k x.2) := by
  let K := G.V η
  let U := sectorNeighborhood G.W.S G.W.base G.W.ε G.W.ε
  let Ω := Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ)
  have hU : IsOpen (U ×ˢ Ω) :=
    (sectorNeighborhood_isOpen G.W.S G.W.base G.W.ε G.W.ε).prod
      (isOpen_Ioo.prod isOpen_univ)
  obtain ⟨B, hB, hlength⟩ := G.negativeInverse_length_values
  have hp (p : PolarPoint) : physicalUnitPoint K k
      (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k p) = p :=
    n07aCanonicalUnitPoint_inverse (K := n07aPhysicalIntervalData K)
      (sub_pos.mp (hlength η k).1) p
  have hf (z : Parameter G.W.S) := G.negativeInverse_actual_fields η z k m side hi
  let JC := G.W.negativeChartJointTower m side
  let JH := G.W.negativeHeightJointTower m side
  let JHI := G.W.negativeHeightInverseJointTower m side
  let JJ := G.W.negativeAbsJacobianJointTower m side
  let JJI := G.W.negativeJacobianInverseJointTower m side
  cases a <;> simp only [negativePhysicalGeometryAtom] at ha
  · have hradial : ContDiff ℝ ∞
        (fun p : PolarPoint => (p.1 - K.left k) / (K.right k - K.left k)) :=
      (contDiff_fst.sub contDiff_const).div_const (K.right k - K.left k)
    apply (JC.comp_contDiff isOpen_univ hradial.contDiffOn (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change (_ - K.left k) / (K.right k - K.left k) =
      ((K.chart (G.lift η x.1) k
        (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2))).1 -
        K.left k) / (K.right k - K.left k)
    rw [hp, (hf x.1).2.2.2.2.1]
  · let L : (Parameter G.W.S × PolarPoint) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ (Parameter G.W.S) PolarPoint)
    let Jθ := smoothDirectionsLinearOn L hU
    apply ((smoothDirectionsProd JC Jθ).comp_contDiff isOpen_univ
      ((contDiff_fst.snd.sub contDiff_snd) :
        ContDiff ℝ ∞ (fun p : PolarPoint × ℝ => p.1.2 - p.2)).contDiffOn
      (fun _ _ => mem_univ _)).congrOn
    intro x hx
    change _ - x.2.2 =
      (K.chart (G.lift η x.1) k
        (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2))).2 - x.2.2
    rw [hp, (hf x.1).2.2.2.2.1]
  · apply JH.congrOn
    intro x hx
    change _ = K.height (G.lift η x.1) k
      (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2))
    rw [hp, (hf x.1).2.2.2.2.2.2]
  · apply JHI.congrOn
    intro x hx
    change _ = (K.height (G.lift η x.1) k
      (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2)))⁻¹
    rw [hp, (hf x.1).2.2.2.2.2.2]
  · apply JJ.congrOn
    intro x hx
    change _ = |planeJacobian (K.chart (G.lift η x.1) k)
      (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2))|
    rw [hp, (hf x.1).2.2.2.2.1]
  · apply JJI.congrOn
    intro x hx
    change _ = |planeJacobian (K.chart (G.lift η x.1) k)
      (physicalUnitPoint K k (n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData K) k x.2))|⁻¹
    rw [hp, (hf x.1).2.2.2.2.1]

/-- A finite family of actual physical atoms has one sharp prefix bound
on the closed old halves.  Every parameter factor and its sampled height
is retained; only the fixed affine length costs enter the coefficient. -/
theorem negativeInverse_physicalFamily_purePrefix
    {A : Type*} [Fintype A] {b : ℕ} {ε : ℝ}
    (hadm : G.Admissible b ε) (select : A → Atom)
    (hselect : ∀ a, negativePhysicalGeometryAtom (select a))
    (h : ∀ a, G.Data 0 (G.Neg 0) b ε
      (G.atomFamily 0 (select a)) (G.atomRef 0 (select a))) :
    ∃ low : ℕ, b ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ, 1 ≤ shift ∧ ∀ s : ℕ,
      ∃ B : ℝ, 0 < B ∧ ∀ a k m side (hi : G.e k = .inl (m, side)),
        ∀ J : SmoothDirections (sectorNeighborhood G.W.S b ε ε ×ˢ
          (Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ univ))
          (fun x : Parameter G.W.S × PolarPoint =>
            G.negativeInversePhysicalAtomFamily 0 (select a) x.1 k x.2),
        ∀ z ∈ sectorNeighborhood G.W.S b ε ε, parameterGrading G.W.S low z ≤ 1 →
        ∀ p ∈ Ioo (G.W.C.left m) (G.W.C.right m) ×ˢ (univ : Set ℝ),
          p ∈ Icc ((G.V 0).physicalLeft k) ((G.V 0).physicalRight k) ×ˢ (univ : Set ℝ) →
        ∀ n : ℕ, ∀ w : StateAngleWord n, w.stateArity ≤ K → w.angleArity ≤ s →
        ∀ v : Fin n → Parameter G.W.S × PolarPoint,
          (∀ i, parameterGrading G.W.S low (v i).1 ≤ 1) →
        ∀ R : ℝ, 1 ≤ R → parameterGrading G.W.S (low + s + shift * K + 1) z ≤ R →
          (∀ i, parameterGrading G.W.S (low + s + shift * K + 1) (v i).1 ≤ R) →
          (∀ i, ‖(v i).2‖ ≤ 1) →
          (∀ i, w.isState i = false → (v i).1 = 0) →
          (∀ i, w.isState i = true → (v i).2 = 0) →
        ‖J.D n (z, p) v‖ ≤
          B * G.W.U.E0 (G.W.U.sample ((G.V 0).cell k)) ^ B *
            parameterHeightWeight
              (G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ)) w.stateArity *
            R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
              (((s + shift * K : ℕ) : ℝ) + 1)) := by
  have hgeometry (a : A) : atomIsGeometry (select a) := by
    have ha := hselect a
    cases he : select a <;> simp_all only [negativePhysicalGeometryAtom, atomIsGeometry,
      false_or, or_false, true_or, or_true]
  have hfamily := G.negativeInverse_atomFamily_purePrefix select hgeometry h
  let low : ℕ := hfamily.choose
  have hlow : b ≤ low := hfamily.choose_spec.1
  have hprefix := hfamily.choose_spec.2
  obtain ⟨D, hD, hlength⟩ := G.negativeInverse_length_values
  refine ⟨low, hlow, fun K => ?_⟩
  let shift : ℕ := (hprefix K).choose
  have hshift : 1 ≤ shift := (hprefix K).choose_spec.1
  have hpref := (hprefix K).choose_spec.2
  refine ⟨shift, hshift, fun s => ?_⟩
  let C : ℝ := (hpref s).choose
  have hC : 0 < C := (hpref s).choose_spec.1
  have hb := (hpref s).choose_spec.2
  obtain ⟨B, hB, hpack⟩ := coefficientEnvelope_pack (C * (1 + D) ^ s) (C + D * s)
  refine ⟨B, hB, ?_⟩
  intro a k m side hi J z hz hzlow p hp hhalf n w hwK hws v hvlow R hR hzR hvR hvphys hvstate hvspatial
  have hk : G.Neg 0 k := (G.neg_iff_inl 0 k).mpr ⟨(m, side), hi⟩
  let E := G.W.U.E0 (G.W.U.sample ((G.V 0).cell k))
  let H := G.W.U.H (G.W.U.sample ((G.V 0).cell k)) ^ (3 / 4 : ℝ)
  let tail := parameterHeightWeight H w.stateArity *
    R ^ (((w.angleArity + shift * w.stateArity - 1 : ℕ) : ℝ) /
      (((s + shift * K : ℕ) : ℝ) + 1))
  let M := 1 + D * E ^ D
  have hE : 1 ≤ E := (G.cost_nonneg 0).2.2 k
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hH : 0 ≤ H := Real.rpow_nonneg ((G.cost_nonneg 0).2.1 k) _
  have htail : 0 ≤ tail := mul_nonneg (parameterHeightWeight_nonneg hH _)
    (Real.rpow_nonneg (zero_le_one.trans hR) _)
  have hM : 1 ≤ M := le_add_of_nonneg_right
    (mul_nonneg hD.le (Real.rpow_nonneg hEpos.le _))
  have hMupper : M ≤ (1 + D) * E ^ D := by
    dsimp only [M]
    nlinarith only [Real.one_le_rpow hE hD.le]
  have hcoefficient : C * E ^ C * M ^ w.angleArity ≤ B * E ^ B := by
    calc
      _ ≤ C * E ^ C * M ^ s := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hM hws) (mul_nonneg hC.le (Real.rpow_nonneg hEpos.le _))
      _ ≤ C * E ^ C * ((1 + D) * E ^ D) ^ s := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans hM) hMupper s)
        (mul_nonneg hC.le (Real.rpow_nonneg hEpos.le _))
      _ = (C * (1 + D) ^ s) * E ^ (C + D * s) := by
        rw [mul_pow, ← Real.rpow_mul_natCast hEpos.le, Real.rpow_add hEpos]
        ring
      _ ≤ B * E ^ B := hpack E hE
  have hlen : (G.V 0).physicalLeft k < (G.V 0).physicalRight k :=
    sub_pos.mp (hlength 0 k).1
  apply n04NegativeInverse_jet_bound_on_closedHalf J hz hp hlen hhalf n v
  intro r hr
  let q := n07aCanonicalUnitInversePoint (n07aPhysicalIntervalData (G.V 0)) k r
  have hq : q ∈ unitStrip :=
    n07aCanonicalUnitInversePoint_maps (K := n07aPhysicalIntervalData (G.V 0)) hlen hr
  let Q := G.negativeInverse_physicalAtomJointTower hadm k hk (select a) (hselect a)
  have hunit : ∀ y : Fin n → PolarPoint, (∀ i, ‖y i‖ ≤ 1) →
      ‖Q.D n (z, q) (fun i => if w.isState i then ((v i).1, 0) else (0, y i))‖ ≤
        (C * E ^ C) * tail := by
    intro y hy
    let u : Fin n → Parameter G.W.S × PolarPoint :=
      fun i => if w.isState i then ((v i).1, 0) else (0, y i)
    have hu (i : Fin n) : (u i).1 = (v i).1 := by
      cases he : w.isState i with
      | true => simp only [u, he, if_true]
      | false => simp only [u, he, Bool.false_eq_true, if_false, hvstate i he]
    have hbnd := hb a k hk Q z hz hzlow q hq n w hwK hws u
      (fun i => by rw [hu]; exact hvlow i) R hR hzR
      (fun i => by rw [hu]; exact hvR i)
      (fun i => by cases he : w.isState i <;> simp only [u, he, if_true,
        Bool.false_eq_true, if_false, norm_zero, zero_le_one, hy i])
      (fun i he => by simp only [u, he, Bool.false_eq_true, if_false])
      (fun i he => by simp only [u, he, if_true])
    simpa only [Real.norm_eq_abs, E, H, tail, mul_assoc] using hbnd
  have hraw := n04NegativeInverse_physicalUnit_norm_bound (G.V 0) k
    (sectorNeighborhood_isOpen G.W.S b ε ε) hlen J Q
    (G.negativeInverse_physicalUnit_maps 0 k m side hi)
    (fun x hx => G.negativeInverse_physicalAtom_on_unit 0 (select a) x.1 k x.2)
    hz hr w v hvphys hvstate hvspatial
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hEpos.le _)) htail) hM
    ((hlength 0 k).2.2.2.1.trans (le_add_of_nonneg_left zero_le_one)) hunit
  calc
    ‖J.D n (z, r) v‖ ≤ ((C * E ^ C) * tail) * M ^ w.angleArity := hraw
    _ = (C * E ^ C * M ^ w.angleArity) * tail := by ring
    _ ≤ (B * E ^ B) * tail := mul_le_mul_of_nonneg_right hcoefficient htail
    _ = _ := by dsimp only [E, H, tail]; ring

end N04RealizationGauge

end ContinuousFlexibility.Analysis

/-- info: 'ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_physicalFamily_purePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ContinuousFlexibility.Analysis.N04RealizationGauge.negativeInverse_physicalFamily_purePrefix
